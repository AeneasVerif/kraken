module

public import LeanQbe.T.LeanLCNF.Sem.PerceusCall
public import LeanQbe.T.LeanLCNF.Sem.Perceus4
public import LeanQbe.T.LeanLCNF.Sem.PerceusPrims
public import LeanQbe.T.LeanLCNF.Sem.PerceusJp4
public import LeanQbe.T.LeanLCNF.Sem.PerceusMut
public import LeanQbe.T.LeanLCNF.Sem.PerceusDec
import LeanQbe.T.Logic.ProofKit

/-!
# LCNF Perceus-Sound Simulation: `let_` Helper Lemmas (`PerceusLet1`)

Bitvector/value-representation helpers, context/shadow invariants across `applyArgs` and
bindings, and full invariant-preservation wrappers for non-pointer, `isShared`, borrowed,
`box`, and `ctor` bindings.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

section BitAndValRepHelpers

public theorem readNatLE_congr :
    ∀ {k : Nat} {bs1 bs2 : List UInt8} {off : Nat},
      (∀ d < k, bs1[off + d]? = bs2[off + d]?) →
      readNatLE bs1 off k = readNatLE bs2 off k := by
  intro k
  induction k with
  | zero =>
    intro _ _ _ _
    simp [readNatLE]
  | succ k ih =>
    intro bs1 bs2 off h
    simp only [readNatLE]
    have h0 : bs1[off]? = bs2[off]? := by
      have := h 0 (Nat.zero_lt_succ k)
      simpa using this
    have hget : bs1.getD off 0 = bs2.getD off 0 := by
      simp only [List.getD]
      rw [h0]
    have htail : readNatLE bs1 (off + 1) k = readNatLE bs2 (off + 1) k := by
      apply ih
      intro d hd
      have h1 := h (d + 1) (Nat.succ_lt_succ hd)
      rwa [show off + 1 + d = off + (d + 1) by omega]
    rw [hget, htail]

public theorem readBitsLE_congr {w : Nat} {bs1 bs2 : List UInt8} {off : Nat}
    (h : ∀ d < (w + 7) / 8, bs1[off + d]? = bs2[off + d]?) :
    readBitsLE w bs1 off = readBitsLE w bs2 off := by
  simp only [readBitsLE]
  rw [readNatLE_congr h]

public theorem word_toWidth_of_valRep {ty : LcTy} {pv : PVal} {rw : Word}
    {objs : List LcnfObj} (hrep : ValRep ty pv rw objs) :
    Word.toWidth ty.width rw = some rw := by
  by_cases hsc : ty.isScalar = true
  · simp only [ValRep, hsc, ↓reduceIte, ScalarRep] at hrep
    rcases hrep with ⟨bv, _, rfl⟩ | ⟨c, _, _, rfl⟩ | ⟨_, rfl⟩ <;>
      simp [Word.toWidth, BitVec.setWidth_eq]
  · simp only [ValRep, hsc, Bool.false_eq_true, ↓reduceIte] at hrep
    obtain ⟨bv, rfl, _⟩ := hrep
    have hw : ty.width = 64 := by cases ty <;> simp_all [LcTy.isScalar, LcTy.width]
    rw [hw]
    simp [Word.toWidth, Word.i64]

public theorem bv64_setWidth_shl1_or1 {w : Nat} (v : BitVec w) (hw : w < 64)
    (tw : Nat) :
    BitVec.setWidth tw ((BitVec.setWidth 64 v <<< 1 ||| 1#64) >>> 1) =
      BitVec.setWidth tw v := by
  have hinner : ((BitVec.setWidth 64 v <<< 1 ||| 1#64) >>> 1) = BitVec.setWidth 64 v := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth]
    by_cases hi0 : i = 63
    · subst hi0
      have hge : w ≤ 63 := by omega
      simp only [show ¬(63 + 1 < 64) by omega, decide_false, Bool.false_and, Bool.false_or,
        show 63 < 64 by omega, decide_true, Bool.true_and]
      rw [BitVec.getLsbD_of_ge (x := v) 63 hge, BitVec.getLsbD_of_ge (x := 1#64) 64 (by omega)]
    · have hlt64 : 1 + i < 64 := by omega
      have hge1 : ¬(1 + i < 1) := by omega
      have hsub : 1 + i - 1 = i := by omega
      have hb1 : (1#64).getLsbD (1 + i) = false := by simp [BitVec.getLsbD_one]
      rw [hb1, decide_eq_true hlt64, decide_eq_false hge1, hsub, decide_eq_true hi]
      simp
  rw [hinner]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
  by_cases hlt : j < 64
  · simp [hlt]
  · simp [hlt, BitVec.getLsbD_of_ge (x := v) j (by omega : w ≤ j)]

public theorem bv64_ofNat_2n1_ushr1 {n : Nat} (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 (2 * n + 1) >>> 1) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hlt64 : 2 * n + 1 < 2 ^ 64 := by omega
  simp [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

public theorem odd_of_2n_add_1 (n : Nat) :
    BitVec.ofNat 64 (2 * n + 1) &&& 1#64 ≠ 0#64 := by
  intro h
  have h0 := congrArg (fun x => x.getLsbD 0) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
    Nat.zero_lt_succ, decide_true, Bool.true_and, Nat.testBit_zero, Bool.and_true] at h0
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  simp [hmod] at h0

public theorem odd_of_shl1_or1 (x : BitVec 64) :
    (x <<< 1 ||| 1#64) &&& 1#64 ≠ 0#64 := by
  rw [bv64_tagged_ofNat64]
  exact odd_of_2n_add_1 x.toNat

public theorem isTaggedPVal_shadow_eq {sm : List (Nat × Nat × List Bool)} {ctx : RcCtx}
    {ρP envP : PValEnv} (hshd : ShadowOk sm ctx ρP envP)
    {v : RcVar} (hv : v ∈ ctx.vars) (hlive : v.isLive = true)
    {pv1 pv2 : PVal} (h1 : ρP v.id = some pv1) (h2 : envP v.id = some pv2) :
    isTaggedPVal pv1 = isTaggedPVal pv2 := by
  have hspec := hshd v hv hlive
  by_cases hi : isVarScalarInit sm v.id = true
  · simp only [hi, ↓reduceIte] at hspec
    rw [hspec, h2] at h1
    injection h1 with h1'
    rw [h1']
  · simp only [hi, Bool.false_eq_true, ↓reduceIte] at hspec
    obtain ⟨sz, m, _, cidx, fs, pscal, hscal, hρ, hE, hpl, hhl, _⟩ := hspec
    rw [hρ] at h1; injection h1 with h1'; subst h1'
    rw [hE] at h2; injection h2 with h2'; subst h2'
    have hlen_eq : pscal.length = hscal.length := hpl.trans hhl.symm
    cases fs with
    | nil =>
      cases pscal <;> cases hscal <;> simp at hlen_eq <;> simp [isTaggedPVal]
    | cons _ _ => simp [isTaggedPVal]

public theorem even_mem_of_not_isTaggedPVal_objRep {pv : PVal} {bv : BitVec 64}
    {objs : List LcnfObj} (htag : isTaggedPVal pv = false) (hrep : ObjRep pv bv objs)
    (hwf_all : ∀ o ∈ objs, o.Wf) :
    (∃ o, o ∈ objs ∧ o.addr = bv) ∧ bv &&& 1#64 = 0#64 := by
  have hmem : ∃ o, o ∈ objs ∧ o.addr = bv := by
    cases pv with
    | erased => simp [isTaggedPVal] at htag
    | bits w v =>
      simp only [isTaggedPVal, decide_eq_false_iff_not, Nat.not_lt] at htag
      rw [ObjRep.eq_2] at hrep
      rcases hrep with ⟨hlt, _⟩ | ⟨_, o, ho, hoa, _⟩
      · omega
      · exact ⟨o, ho, hoa⟩
    | nat n =>
      simp only [isTaggedPVal, decide_eq_false_iff_not, Nat.not_lt] at htag
      rw [ObjRep.eq_3, natRepR0] at hrep
      split at hrep
      · omega
      · obtain ⟨_, o, ho, hoa, _⟩ := hrep
        exact ⟨o, ho, hoa⟩
    | ctor c fs sc =>
      rw [ObjRep.eq_4] at hrep
      rcases hrep with ⟨rfl, rfl, hlt, _⟩ | ⟨_, o, ho, hoa, _⟩
      · simp [isTaggedPVal, hlt] at htag
      · exact ⟨o, ho, hoa⟩
    | str s =>
      rw [ObjRep.eq_5] at hrep
      obtain ⟨o, ho, hoa, _⟩ := hrep
      exact ⟨o, ho, hoa⟩
    | arr xs =>
      rw [ObjRep.eq_6] at hrep
      obtain ⟨o, ho, hoa, _⟩ := hrep
      exact ⟨o, ho, hoa⟩
    | barr bs =>
      rw [ObjRep.eq_7] at hrep
      obtain ⟨o, ho, hoa, _⟩ := hrep
      exact ⟨o, ho, hoa⟩
    | int z => rw [ObjRep.eq_8] at hrep; exact False.elim hrep
    | clo f a args => simp [ObjRep] at hrep
  obtain ⟨o, ho, hoa⟩ := hmem
  have howf := hwf_all o ho
  have hmod : bv.toNat % 8 = 0 := hoa ▸ howf.2.1
  have hev : bv &&& 1#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    have hmod1 : (1#64).toNat = 1 := rfl
    have hmod0 : (0#64).toNat = 0 := rfl
    simp only [BitVec.toNat_and, hmod1, hmod0]
    have hband := Nat.and_one_is_mod bv.toNat
    omega
  exact ⟨⟨o, ho, hoa⟩, hev⟩

end BitAndValRepHelpers

section CtxAndShadowHelpers

private theorem isLive_mono {v' v : RcVar}
    (hno : v'.noRc = v.noRc) (hps : v'.persistent = v.persistent)
    (how : v'.owned ≤ v.owned) (hbr : v'.borrowed = true → v.borrowed = true)
    (hrt : v'.resetTok = true → v.resetTok = true)
    (hl : v'.isLive = true) : v.isLive = true := by
  simp only [RcVar.isLive, Bool.or_eq_true, decide_eq_true_eq] at hl ⊢
  rcases hl with (((h1 | h2) | h3) | h4) | h5
  · simp [hno.symm.trans h1]
  · simp [hps.symm.trans h2]
  · simp [show 0 < v.owned by omega]
  · simp [hbr h4]
  · simp [hrt h5]

private theorem isLive_clearBorrow_ite (x : Nat) (v : RcVar)
    (hl : (if (v.parent? == some x) = true then
      { v with borrowed := false, parent? := none } else v).isLive = true) :
    v.isLive = true := by
  by_cases hp : (v.parent? == some x) = true
  · simp only [hp, ↓reduceIte] at hl
    exact isLive_mono (v' := { v with borrowed := false, parent? := none }) rfl rfl
      (Nat.le_refl _) (fun h => by cases h) id hl
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hl
    exact hl

public theorem consumeVar_ctx_props {ctx ctx1 : RcCtx} {x n : Nat}
    (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hc : ctx.consumeVar x n = Except.ok ctx1) :
    (∀ z, Option.map RcVar.ty (ctx1.get? z) = Option.map RcVar.ty (ctx.get? z) ∧
      (Option.map RcVar.isLive (ctx1.get? z) = some true →
        Option.map RcVar.isLive (ctx.get? z) = some true)) ∧
      (∀ p, p ∈ ctx1.sharedPreds → p ∈ ctx.sharedPreds) ∧
      (∀ z, (ctx.get? z).isSome = true → (ctx1.get? z).isSome = true) ∧
      (∀ u ∈ ctx1.vars, ∃ u0 ∈ ctx.vars, u.id = u0.id ∧ u.ty = u0.ty ∧
        (u.isLive = true → u0.isLive = true) ∧ u.noRc = u0.noRc ∧
        u.persistent = u0.persistent ∧ (u.excl = true → u0.excl = true) ∧
        (u.parent? = u0.parent? ∨ u.parent? = none)) := by
  simp only [RcCtx.consumeVar] at hc
  cases hgx : ctx.get? x with
  | none => simp [hgx] at hc
  | some vx =>
    simp only [hgx] at hc
    by_cases hnp : (vx.noRc || vx.persistent) = true
    · simp only [hnp, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hc
      subst hc
      exact ⟨fun _ => ⟨rfl, id⟩, fun _ h => h, fun _ h => h,
        fun u hu => ⟨u, hu, rfl, rfl, id, rfl, rfl, id, Or.inl rfl⟩⟩
    · simp only [hnp, Bool.false_eq_true, ↓reduceIte] at hc
      by_cases hn0 : (n == 0) = true
      · simp only [hn0, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hc
        subst hc
        exact ⟨fun _ => ⟨rfl, id⟩, fun _ h => h, fun _ h => h,
          fun u hu => ⟨u, hu, rfl, rfl, id, rfl, rfl, id, Or.inl rfl⟩⟩
      · simp only [hn0, Bool.false_eq_true, ↓reduceIte] at hc
        by_cases hlt : vx.owned < n
        · simp [hlt] at hc
        · simp only [hlt, ↓reduceIte] at hc
          let rem := vx.owned - n
          let vx' : RcVar := {
            id := vx.id, ty := vx.ty, noRc := vx.noRc, persistent := vx.persistent,
            owned := rem, borrowed := vx.borrowed, parent? := vx.parent?,
            excl := if (rem == 0) = true then false else vx.excl,
            resetTok := if (rem == 0) = true then false else vx.resetTok }
          let ctxMid := ctx.put vx'
          have hvx_id : vx.id = x := (RcCtx.get?_mem hgx).2
          have hvx'_id : vx'.id = x := hvx_id
          have hmid_get : ∀ z, ctxMid.get? z = if z = x then some vx' else ctx.get? z := by
            intro z
            rw [RcCtx.put_get? hnd vx' z, hvx'_id]
            by_cases hzx : z = x
            · simp [hzx]
            · simp [hzx]
          have hvx'_live : vx'.isLive = true → vx.isLive = true :=
            isLive_mono rfl rfl (Nat.sub_le _ _) id (fun h => by
              by_cases hrem : rem = 0 <;> simp [vx', hrem] at h; exact h)
          change (if (rem == 0 && !vx'.borrowed) = true then
              pure (ctxMid.invalidateChildren x) else pure ctxMid) = Except.ok ctx1 at hc
          by_cases hinv : (rem == 0 && !vx'.borrowed) = true
          · simp only [hinv, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hc
            subst hc
            have hinv_sp : ∀ p, p ∈ (ctxMid.invalidateChildren x).sharedPreds →
                p ∈ ctx.sharedPreds := by
              intro p hp
              simp only [RcCtx.invalidateChildren, ctxMid, RcCtx.put, List.mem_filter] at hp
              exact hp.1
            have hinv_get : ∀ z, (ctxMid.invalidateChildren x).get? z =
                Option.map (fun v => if (v.parent? == some x) = true then
                  { v with borrowed := false, parent? := none } else v) (ctxMid.get? z) := by
              intro z
              simp only [RcCtx.invalidateChildren, RcCtx.get?]
              induction ctxMid.vars with
              | nil => rfl
              | cons u us ihu =>
                simp only [List.map_cons, List.find?_cons]
                by_cases hp : (u.parent? == some x) = true <;>
                  by_cases hid : (u.id == z) = true
                · simp only [hp, ↓reduceIte, hid, Option.map_some]
                · simp only [hp, ↓reduceIte, hid, ihu]
                · simp only [hp, Bool.false_eq_true, ↓reduceIte, hid, Option.map_some]
                · simp only [hp, Bool.false_eq_true, ↓reduceIte, hid, ihu]
            refine ⟨fun z => ?_, hinv_sp, fun z hz => ?_, fun u hu => ?_⟩
            · rw [hinv_get z, hmid_get z]
              by_cases hzx : z = x
              · rw [hzx]; simp only [↓reduceIte, hgx]; constructor
                · by_cases hp : vx.parent? = some x <;> simp +zetaDelta [hp]
                · intro hlive
                  simp only [Option.map_some, Option.some.injEq] at hlive ⊢
                  exact hvx'_live (isLive_clearBorrow_ite x vx' hlive)
              · simp only [hzx, ↓reduceIte]
                cases hgz : ctx.get? z with
                | none => simp
                | some vz =>
                  constructor
                  · by_cases hp : vz.parent? = some x <;> simp [hp]
                  · intro hlive
                    simp only [Option.map_some, Option.some.injEq] at hlive ⊢
                    exact isLive_clearBorrow_ite x vz hlive
            · rw [hinv_get z, hmid_get z]
              by_cases hzx : z = x
              · rw [hzx]; simp
              · simp only [hzx, ↓reduceIte]
                cases hgz : ctx.get? z with
                | none => simp [hgz] at hz
                | some _ => simp
            · simp only [RcCtx.invalidateChildren, List.mem_map] at hu
              obtain ⟨u1, hu1, rfl⟩ := hu
              rcases (RcCtx.put_mem_iff hnd).mp hu1 with hux | ⟨hu1_mem, _⟩
              · subst u1
                refine ⟨vx, (RcCtx.get?_mem hgx).1, ?_, ?_, fun hl => ?_, ?_, ?_, fun he => ?_, ?_⟩
                · by_cases hp : vx.parent? = some x <;> simp +zetaDelta [hp]
                · by_cases hp : vx.parent? = some x <;> simp +zetaDelta [hp]
                · exact hvx'_live (isLive_clearBorrow_ite x vx' hl)
                · by_cases hp : vx.parent? = some x <;> simp +zetaDelta [hp]
                · by_cases hp : vx.parent? = some x <;> simp +zetaDelta [hp]
                · by_cases hp : vx.parent? = some x <;> by_cases hrem : rem = 0 <;>
                    simp +zetaDelta [hp, hrem] at he ⊢ <;> exact he
                · by_cases hp : vx.parent? = some x <;> simp +zetaDelta [hp]
              · refine ⟨u1, hu1_mem, ?_, ?_, fun hl => ?_, ?_, ?_, fun he => ?_, ?_⟩
                · by_cases hp : u1.parent? = some x <;> simp [hp]
                · by_cases hp : u1.parent? = some x <;> simp [hp]
                · exact isLive_clearBorrow_ite x u1 hl
                · by_cases hp : u1.parent? = some x <;> simp [hp]
                · by_cases hp : u1.parent? = some x <;> simp [hp]
                · by_cases hp : u1.parent? = some x <;> simp [hp] at he ⊢ <;> exact he
                · by_cases hp : u1.parent? = some x <;> simp [hp]
          · simp only [hinv, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
              Except.ok.injEq] at hc
            subst hc
            refine ⟨fun z => ?_, fun _ h => h, fun z hz => ?_, fun u hu => ?_⟩
            · rw [hmid_get z]
              by_cases hzx : z = x
              · rw [hzx]; simp only [↓reduceIte, hgx]; constructor
                · simp +zetaDelta
                · intro hlive
                  simp only [Option.map_some, Option.some.injEq] at hlive ⊢
                  exact hvx'_live hlive
              · simp only [hzx, ↓reduceIte]; simp
            · rw [hmid_get z]
              by_cases hzx : z = x
              · rw [hzx]; simp
              · simp only [hzx, ↓reduceIte]; exact hz
            · rcases (RcCtx.put_mem_iff hnd).mp hu with hu_eq | ⟨hu_mem, _⟩
              · subst u
                refine ⟨vx, (RcCtx.get?_mem hgx).1, rfl, rfl, fun hl => hvx'_live hl, rfl, rfl,
                  fun he => ?_, Or.inl rfl⟩
                by_cases hrem : rem = 0 <;> simp +zetaDelta [hrem] at he ⊢ <;> exact he
              · exact ⟨u, hu_mem, rfl, rfl, id, rfl, rfl, id, Or.inl rfl⟩

public theorem applyArgs_ctx_props {ctx ctx1 : RcCtx} {as : List LcArg} {bs : List Bool}
    (hnd : (ctx.vars.map RcVar.id).Nodup)
    (ha : ctx.applyArgs as bs = Except.ok ctx1) :
    (∀ z, Option.map RcVar.ty (ctx1.get? z) = Option.map RcVar.ty (ctx.get? z) ∧
      (Option.map RcVar.isLive (ctx1.get? z) = some true →
        Option.map RcVar.isLive (ctx.get? z) = some true)) ∧
      (∀ p, p ∈ ctx1.sharedPreds → p ∈ ctx.sharedPreds) ∧
      (∀ z, (ctx.get? z).isSome = true → (ctx1.get? z).isSome = true) ∧
      (∀ u ∈ ctx1.vars, ∃ u0 ∈ ctx.vars, u.id = u0.id ∧ u.ty = u0.ty ∧
        (u.isLive = true → u0.isLive = true) ∧ u.noRc = u0.noRc ∧
        u.persistent = u0.persistent ∧ (u.excl = true → u0.excl = true) ∧
        (u.parent? = u0.parent? ∨ u.parent? = none)) := by
  induction as generalizing ctx bs with
  | nil =>
    cases bs with
    | nil =>
      simp only [RcCtx.applyArgs.eq_1, pure, Except.pure, Except.ok.injEq] at ha
      subst ha
      exact ⟨fun _ => ⟨rfl, id⟩, fun _ h => h, fun _ h => h,
        fun u hu => ⟨u, hu, rfl, rfl, id, rfl, rfl, id, Or.inl rfl⟩⟩
    | cons _ _ => simp [RcCtx.applyArgs] at ha
  | cons a as ih =>
    cases bs with
    | nil => simp [RcCtx.applyArgs] at ha
    | cons b bs =>
      rw [RcCtx.applyArgs.eq_2] at ha
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte] at ha
        cases hchk : ctx.checkArgLive a with
        | error e => simp [bind, Except.bind, hchk] at ha
        | ok _ =>
          simp only [bind, Except.bind, hchk] at ha
          exact ih hnd ha
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
        cases hca : ctx.consumeArg a with
        | error e => simp [bind, Except.bind, hca] at ha
        | ok ctxMid =>
          simp only [bind, Except.bind, hca] at ha
          have hndMid : (ctxMid.vars.map RcVar.id).Nodup := by
            cases a with
            | erased =>
              simp only [RcCtx.consumeArg, pure, Except.pure, Except.ok.injEq] at hca
              subst hca; exact hnd
            | var y => exact consumeVar_nodup hnd hca
          have h1 : (∀ z, Option.map RcVar.ty (ctxMid.get? z) = Option.map RcVar.ty (ctx.get? z) ∧
              (Option.map RcVar.isLive (ctxMid.get? z) = some true →
                Option.map RcVar.isLive (ctx.get? z) = some true)) ∧
              (∀ p, p ∈ ctxMid.sharedPreds → p ∈ ctx.sharedPreds) ∧
              (∀ z, (ctx.get? z).isSome = true → (ctxMid.get? z).isSome = true) ∧
              (∀ u ∈ ctxMid.vars, ∃ u0 ∈ ctx.vars, u.id = u0.id ∧ u.ty = u0.ty ∧
                (u.isLive = true → u0.isLive = true) ∧ u.noRc = u0.noRc ∧
                u.persistent = u0.persistent ∧ (u.excl = true → u0.excl = true) ∧
                (u.parent? = u0.parent? ∨ u.parent? = none)) := by
            cases a with
            | erased =>
              simp only [RcCtx.consumeArg, pure, Except.pure, Except.ok.injEq] at hca
              subst hca
              exact ⟨fun _ => ⟨rfl, id⟩, fun _ h => h, fun _ h => h,
                fun u hu => ⟨u, hu, rfl, rfl, id, rfl, rfl, id, Or.inl rfl⟩⟩
            | var y => exact consumeVar_ctx_props hnd hca
          have h2 := ih hndMid ha
          refine ⟨fun z => ⟨(h2.1 z).1.trans (h1.1 z).1, fun h => (h1.1 z).2 ((h2.1 z).2 h)⟩,
            fun p hp => h1.2.1 p (h2.2.1 p hp),
            fun z hz => h2.2.2.1 z (h1.2.2.1 z hz), fun u hu => ?_⟩
          obtain ⟨um, hum, hidm, htym, hlm, hnom, hpm, hexm, hprm⟩ := h2.2.2.2 u hu
          obtain ⟨u0, hu0, hid0, hty0, hl0, hno0, hp0, hex0, hpr0⟩ := h1.2.2.2 um hum
          refine ⟨u0, hu0, hidm.trans hid0, htym.trans hty0, fun hl => hl0 (hlm hl),
            hnom.trans hno0, hpm.trans hp0, fun he => hex0 (hexm he), ?_⟩
          rcases hprm with hm | hm
          · rw [hm]; exact hpr0
          · exact Or.inr hm

public theorem applyArgs_unconsumed_var_same {ctx ctx1 : RcCtx}
    {as : List LcArg} {bs : List Bool} {s : Nat}
    (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hno_sh : (as.zip bs).all (fun p => if p.2 = true then true else
      match p.1 with | .erased => true | .var z => (z != s)) = true)
    (ha : ctx.applyArgs as bs = Except.ok ctx1)
    {v0 v1 : RcVar} (hg0 : ctx.get? s = some v0) (hg1 : ctx1.get? s = some v1) :
    v1.owned = v0.owned ∧ v1.noRc = v0.noRc ∧ v1.persistent = v0.persistent ∧
      v1.resetTok = v0.resetTok ∧ v1.ty = v0.ty := by
  induction as generalizing ctx bs v0 with
  | nil =>
    cases bs with
    | nil =>
      simp only [RcCtx.applyArgs.eq_1, pure, Except.pure, Except.ok.injEq] at ha
      subst ha; rw [hg0] at hg1; cases hg1; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | cons _ _ => simp [RcCtx.applyArgs] at ha
  | cons a as ih =>
    cases bs with
    | nil => simp [RcCtx.applyArgs] at ha
    | cons b bs =>
      rw [RcCtx.applyArgs.eq_2] at ha
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hno_sh
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte] at ha
        cases hchk : ctx.checkArgLive a with
        | error e => simp [bind, Except.bind, hchk] at ha
        | ok _ =>
          simp only [bind, Except.bind, hchk] at ha
          exact ih hnd hno_sh.2 ha hg0
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
        cases hca : ctx.consumeArg a with
        | error e => simp [bind, Except.bind, hca] at ha
        | ok ctxMid =>
          simp only [bind, Except.bind, hca] at ha
          have hndMid : (ctxMid.vars.map RcVar.id).Nodup := by
            cases a with
            | erased =>
              simp only [RcCtx.consumeArg, pure, Except.pure, Except.ok.injEq] at hca
              subst hca; exact hnd
            | var y => exact consumeVar_nodup hnd hca
          have hmid_mem : ∃ vm, ctxMid.get? s = some vm ∧ vm.owned = v0.owned ∧
              vm.noRc = v0.noRc ∧ vm.persistent = v0.persistent ∧
              vm.resetTok = v0.resetTok ∧ vm.ty = v0.ty := by
            cases a with
            | erased =>
              simp only [RcCtx.consumeArg, pure, Except.pure, Except.ok.injEq] at hca
              subst hca; exact ⟨v0, hg0, rfl, rfl, rfl, rfl, rfl⟩
            | var z =>
              have hne : z ≠ s := by
                have h1 := hno_sh.1
                simp only [hb, Bool.false_eq_true, ↓reduceIte, bne_iff_ne] at h1
                exact h1
              simp only [RcCtx.consumeArg] at hca
              have hvm_get : ∃ vm, ctxMid.get? s = some vm := by
                have hprops := consumeVar_ctx_props hnd hca
                have his := hprops.2.2.1 s (by simp [hg0])
                cases hg_m : ctxMid.get? s with
                | none => simp [hg_m] at his
                | some vm => exact ⟨vm, rfl⟩
              obtain ⟨vm, hg_m⟩ := hvm_get
              refine ⟨vm, hg_m, ?_, ?_, ?_, ?_, ?_⟩ <;> {
                simp only [RcCtx.consumeVar] at hca
                cases hgz : ctx.get? z with
                | none => simp [hgz] at hca
                | some vz =>
                  simp only [hgz] at hca
                  split at hca
                  · injection hca with h'; subst h'; rw [hg0] at hg_m; cases hg_m; rfl
                  · split at hca
                    · injection hca with h'; subst h'; rw [hg0] at hg_m; cases hg_m; rfl
                    · split at hca
                      · cases hca
                      · let rem := vz.owned - 1
                        let vz' : RcVar := {
                          id := vz.id, ty := vz.ty, noRc := vz.noRc, persistent := vz.persistent,
                          owned := rem, borrowed := vz.borrowed, parent? := vz.parent?,
                          excl := if (rem == 0) = true then false else vz.excl,
                          resetTok := if (rem == 0) = true then false else vz.resetTok }
                        have hmid_ne : (ctx.put vz').get? s = some v0 := by
                          rw [RcCtx.put_get? hnd vz' s]
                          have hvid : vz'.id = z := (RcCtx.get?_mem hgz).2
                          simp [hvid, beq_false_of_ne (Ne.symm hne), hg0]
                        split at hca <;> injection hca with h' <;> subst h'
                        · have hget_inv : (RcCtx.invalidateChildren (ctx.put vz') z).get? s =
                              Option.map (fun v => if (v.parent? == some z) = true then
                                { v with borrowed := false, parent? := none } else v)
                                ((ctx.put vz').get? s) := by
                            simp only [RcCtx.invalidateChildren, RcCtx.get?]
                            induction (ctx.put vz').vars with
                            | nil => rfl
                            | cons u us ihu =>
                              simp only [List.map_cons, List.find?_cons]
                              by_cases hp : (u.parent? == some z) = true <;>
                                by_cases hid : (u.id == s) = true
                              · simp only [hp, ↓reduceIte, hid, Option.map_some]
                              · simp only [hp, ↓reduceIte, hid, ihu]
                              · simp only [hp, Bool.false_eq_true, ↓reduceIte, hid,
                                  Option.map_some]
                              · simp only [hp, Bool.false_eq_true, ↓reduceIte, hid, ihu]
                          rw [hget_inv, hmid_ne] at hg_m
                          simp only [Option.map_some, Option.some.injEq] at hg_m
                          by_cases hp : (v0.parent? == some z) = true <;>
                            simp [hp] at hg_m <;> rw [← hg_m] <;> rfl
                        · rw [hmid_ne] at hg_m; cases hg_m; rfl }
          obtain ⟨vm, hg_m, ho, hno, hps, hrt, hty⟩ := hmid_mem
          obtain ⟨ho', hno', hps', hrt', hty'⟩ := ih hndMid hno_sh.2 ha hg_m
          exact ⟨ho'.trans ho, hno'.trans hno, hps'.trans hps, hrt'.trans hrt, hty'.trans hty⟩

public theorem binderFreshOwned_applyArgs_nodup {ctx ctx1 : RcCtx} {x : Nat}
    {as : List LcArg} {bs : List Bool}
    (hfr : binderFreshOwned ctx x = true)
    (hnd : (ctx.vars.map RcVar.id).Nodup)
    (ha : ctx.applyArgs as bs = Except.ok ctx1) :
    binderFreshOwned ctx1 x = true := by
  have hprops := applyArgs_ctx_props hnd ha
  simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true] at hfr ⊢
  obtain ⟨⟨hpar, hsp⟩, hgx⟩ := hfr
  refine ⟨⟨fun u hu => ?_, fun p hp => ?_⟩, ?_⟩
  · obtain ⟨u0, hu0, _, _, _, _, _, _, hpr⟩ := hprops.2.2.2 u hu
    rcases hpr with hpr | hpr
    · rw [hpr]; exact hpar u0 hu0
    · simp [hpr]
  · exact hsp p (hprops.2.1 p hp)
  · cases hg1 : ctx1.get? x with
    | none => simp
    | some v1 =>
      by_cases hl : v1.isLive = true
      · have h0 := (hprops.1 x).2 (by rw [hg1]; simp [hl])
        cases hg0 : ctx.get? x with
        | none => simp [hg0] at h0
        | some v0 =>
          simp only [hg0, Bool.not_eq_true'] at hgx
          simp [hg0, hgx] at h0
      · simp [hl]

public theorem shadowOk_applyArgs {sm : List (Nat × Nat × List Bool)}
    {ctx ctx1 : RcCtx} {ρP envP : PValEnv} {as : List LcArg} {bs : List Bool}
    (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hshd : ShadowOk sm ctx ρP envP)
    (ha : ctx.applyArgs as bs = Except.ok ctx1) :
    ShadowOk sm ctx1 ρP envP := by
  have hprops := applyArgs_ctx_props hnd ha
  intro v hv hlive
  obtain ⟨u0, hu0, hid, _, hl0, _, _, _, _⟩ := hprops.2.2.2 v hv
  simpa [hid] using hshd u0 hu0 (hl0 hlive)

public theorem sharedTargetsHeap_applyArgs {rf : RcFrame} {ctx1 : RcCtx}
    {as : List LcArg} {bs : List Bool}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup)
    (hsth : SharedTargetsHeap rf)
    (ha : rf.ctx.applyArgs as bs = Except.ok ctx1) :
    SharedTargetsHeap {
      ctx := ctx1, envP := rf.envP, envH := rf.envH,
      extH := rf.extH, ghostH := rf.ghostH } := by
  have hprops := applyArgs_ctx_props hnd ha
  intro p hp vx hgx1 hno
  have hp0 := hprops.2.1 p hp
  have hvx_mem := (RcCtx.get?_mem hgx1).1
  have hvx_id := (RcCtx.get?_mem hgx1).2
  obtain ⟨u0, hu0, hid0, hty0, _, hno0, _, _, _⟩ := hprops.2.2.2 vx hvx_mem
  have hgu0 : rf.ctx.get? p.2 = some u0 := by
    have h := (RcCtx.mem_get?_iff hnd).mpr hu0
    rwa [← hid0, hvx_id] at h
  simpa [hty0] using hsth p hp0 u0 hgu0 (hno0.symm.trans hno)

public theorem exclCtorHeap_applyArgs {rf : RcFrame} {ctx1 : RcCtx}
    {as : List LcArg} {bs : List Bool}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup)
    (hexcl : ExclCtorHeap rf)
    (ha : rf.ctx.applyArgs as bs = Except.ok ctx1) :
    ExclCtorHeap {
      ctx := ctx1, envP := rf.envP, envH := rf.envH,
      extH := rf.extH, ghostH := rf.ghostH } := by
  have hprops := applyArgs_ctx_props hnd ha
  intro v hv hlive hex hno hps cidx fs sc hρ
  obtain ⟨u0, hu0, hid0, hty0, hl0, hno0, hp0, hex0, _⟩ := hprops.2.2.2 v hv
  have hret := hexcl u0 hu0 (hl0 hlive) (hex0 hex) (hno0.symm.trans hno) (hp0.symm.trans hps)
    cidx fs sc (by simpa [hid0] using hρ)
  simpa [hid0, hty0] using hret

private theorem find?_filter_ne {α : Type} (p : Nat → Bool) (f : (Nat × α) → Bool)
    (l : List (Nat × α)) (h : ∀ e, f e = true → p e.1 = true) :
    (l.filter (fun e => p e.1)).find? f = l.find? f := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [List.filter_cons, List.find?_cons]
    by_cases hf : f e = true
    · have hp : p e.1 = true := h e hf
      simp [hp, hf]
    · by_cases hp : p e.1 = true
      · simp [hp, hf, ih]
      · simp [hp, hf, ih]

public theorem shadowOk_put_same {sm : List (Nat × Nat × List Bool)}
    {ctx : RcCtx} {ρP envP : PValEnv} {x : Nat} {vx : RcVar} {pv : PVal}
    (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hshd : ShadowOk sm ctx ρP envP) (hxid : vx.id = x) :
    ShadowOk (sm.filter (fun e => e.1 != x)) (ctx.put vx) (ρP.set x pv) (envP.set x pv) := by
  intro v hv hlive
  rcases (RcCtx.put_mem_iff hnd).mp hv with rfl | ⟨hv_mem, hv_ne⟩
  · have his : isVarScalarInit (sm.filter (fun e => e.1 != x)) v.id = true := by
      simp only [isVarScalarInit, List.all_eq_true, List.mem_filter, bne_iff_ne]
      intro e ⟨_, hne⟩
      rw [hxid]; exact hne
    rw [hxid] at his
    simp [his, hxid, PValEnv.set]
  · have hvne' : v.id ≠ x := by simpa [hxid] using hv_ne
    have his_eq : isVarScalarInit (sm.filter (fun e => e.1 != x)) v.id =
        isVarScalarInit sm v.id := by
      simp only [isVarScalarInit]
      cases h : List.all sm (fun e => e.1 != v.id)
      · rw [Bool.eq_false_iff]; intro hall
        simp only [List.all_eq_true, List.mem_filter, bne_iff_ne] at hall
        have hf : ∃ e ∈ sm, e.1 = v.id := by
          by_cases hex : ∃ e ∈ sm, e.1 = v.id
          · exact hex
          · have htrue : List.all sm (fun e => e.1 != v.id) = true := by
              rw [List.all_eq_true]
              intro e he
              rw [bne_iff_ne]
              intro heq
              exact hex ⟨e, he, heq⟩
            rw [htrue] at h
            cases h
        obtain ⟨e, he, hid⟩ := hf
        have h1 := hall e ⟨he, by rw [hid]; exact hvne'⟩
        simp [hid] at h1
      · simp only [List.all_eq_true, List.mem_filter, bne_iff_ne] at h ⊢
        intro e ⟨he, _⟩
        exact h e he
    have hfind : (sm.filter (fun e => e.1 != x)).find? (fun e => e.1 == v.id) =
        sm.find? (fun e => e.1 == v.id) := by
      apply find?_filter_ne (fun k => k != x)
      intro e he
      simp only [beq_iff_eq] at he
      exact bne_iff_ne.mpr (by rw [he]; exact hvne')
    have hspec := hshd v hv_mem hlive
    rw [his_eq]
    by_cases hi : isVarScalarInit sm v.id = true
    · simp only [hi, ↓reduceIte] at hspec ⊢
      simp [PValEnv.set, hvne', hspec]
    · simp only [hi, Bool.false_eq_true, ↓reduceIte] at hspec ⊢
      rw [hfind]
      obtain ⟨sz, m, hfn, cidx, fs, pscal, hscal, hρ, hE, hpl, hhl, hfsz, hidx⟩ := hspec
      refine ⟨sz, m, hfn, cidx, fs, pscal, hscal, ?_, ?_, hpl, hhl, hfsz, hidx⟩ <;>
        simp [PValEnv.set, hvne', hρ, hE]

public theorem shadowOk_bind_ctor {sm : List (Nat × Nat × List Bool)}
    {ctx : RcCtx} {ρP envP : PValEnv} {x : Nat} {vx : RcVar}
    {ci : LcCtor} {fs : List PVal} {scal : List UInt8}
    (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hshd : ShadowOk sm ctx ρP envP) (hxid : vx.id = x)
    (hns : ¬ci.isScalar = true) (hfs_len : fs.length = ci.size)
    (hscal_len : scal.length = 8 * ci.usize + ci.ssize) :
    let pvP := PVal.ctor ci.cidx fs (List.replicate (8 * ci.usize + ci.ssize) 0)
    let pvH := PVal.ctor ci.cidx fs scal
    ShadowOk (ctorBindMask x ci sm) (ctx.put vx) (ρP.set x pvP) (envP.set x pvH) := by
  intro pvP pvH v hv hlive
  let len := 8 * ci.usize + ci.ssize
  let smBase := sm.filter (fun e => e.1 != x)
  have hbase : ShadowOk smBase (ctx.put vx) (ρP.set x pvP) (envP.set x pvP) :=
    shadowOk_put_same hnd hshd hxid
  have hns_b : (!ci.isScalar) = true := by simp [hns]
  by_cases hlen : 0 < len
  · have hmask : ctorBindMask x ci sm = (x, ci.size, List.replicate len false) :: smBase := by
      simp [ctorBindMask, hns_b, hlen, len, smBase]
    rw [hmask]
    rcases (RcCtx.put_mem_iff hnd).mp hv with rfl | ⟨hv_mem, hv_ne⟩
    · have his : isVarScalarInit ((x, ci.size, List.replicate len false) :: smBase) v.id =
          false := by
        simp [isVarScalarInit, hxid]
      rw [hxid] at his
      simp only [his, Bool.false_eq_true, ↓reduceIte, List.find?_cons, hxid, beq_self_eq_true]
      refine ⟨ci.size, List.replicate len false, rfl, ci.cidx, fs,
        List.replicate len 0, scal, ?_, ?_, ?_, ?_, hfs_len, ?_⟩
      · simp [PValEnv.set, pvP]; rfl
      · simp [PValEnv.set, pvH]
      · simp
      · simp [hscal_len]; rfl
      · intro i hi hm
        simp only [List.length_replicate] at hi
        simp [hi] at hm
    · have hvne' : v.id ≠ x := by simpa [hxid] using hv_ne
      have hxb : (x != v.id) = true := bne_iff_ne.mpr (Ne.symm hvne')
      have hxbeq : (x == v.id) = false := beq_false_of_ne (Ne.symm hvne')
      have hspec := hbase v hv hlive
      have his_eq : isVarScalarInit ((x, ci.size, List.replicate len false) :: smBase) v.id =
          isVarScalarInit smBase v.id := by
        simp [isVarScalarInit, hxb]
      rw [his_eq]
      by_cases hi : isVarScalarInit smBase v.id = true
      · simp only [hi, ↓reduceIte] at hspec ⊢
        simpa [PValEnv.set, hvne'] using hspec
      · simp only [hi, Bool.false_eq_true, ↓reduceIte, List.find?_cons, hxbeq] at hspec ⊢
        simpa [PValEnv.set, hvne'] using hspec
  · have hlen0 : len = 0 := by omega
    have hscal0 : scal = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h0a : 8 * ci.usize = 0 := by omega
    have h0b : ci.ssize = 0 := by omega
    have hpveq : pvH = pvP := by simp [pvH, pvP, hscal0, h0a, h0b]
    have hmask : ctorBindMask x ci sm = smBase := by
      simp [ctorBindMask, hns_b, hlen, len, smBase]
    rw [hmask, hpveq]
    exact hbase v hv hlive

public theorem exclCtorHeap_put_nonExcl {rf : RcFrame} {x : Nat} {vx : RcVar}
    {pv : PVal} {w : Word}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup)
    (hexcl : ExclCtorHeap rf) (hxid : vx.id = x) (hne : vx.excl = false) :
    ExclCtorHeap {
      ctx := rf.ctx.put vx, envP := rf.envP.set x pv,
      envH := rf.envH.set x vx.ty w, extH := rf.extH, ghostH := rf.ghostH } := by
  intro v hv hlive hex hno hps cidx fs sc hρ
  rcases (RcCtx.put_mem_iff hnd).mp hv with rfl | ⟨hv_mem, hv_ne⟩
  · rw [hne] at hex; cases hex
  · have hvne' : v.id ≠ x := by simpa [hxid] using hv_ne
    simp only [PValEnv.set, hvne', ↓reduceIte] at hρ
    obtain ⟨bv, hbv, hev⟩ := hexcl v hv_mem hlive hex hno hps cidx fs sc hρ
    exact ⟨bv, by simp [HValEnv.set, hvne', hbv], hev⟩

public theorem exclCtorHeap_put_notCtor {rf : RcFrame} {x : Nat} {vx : RcVar}
    {pv : PVal} {w : Word}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup)
    (hexcl : ExclCtorHeap rf) (hxid : vx.id = x)
    (hnctor : ∀ cidx fs sc, pv ≠ PVal.ctor cidx fs sc) :
    ExclCtorHeap {
      ctx := rf.ctx.put vx, envP := rf.envP.set x pv,
      envH := rf.envH.set x vx.ty w, extH := rf.extH, ghostH := rf.ghostH } := by
  intro v hv hlive hex hno hps cidx fs sc hρ
  rcases (RcCtx.put_mem_iff hnd).mp hv with rfl | ⟨hv_mem, hv_ne⟩
  · simp only [hxid, PValEnv.set, ↓reduceIte, Option.some.injEq] at hρ
    exact False.elim (hnctor cidx fs sc hρ)
  · have hvne' : v.id ≠ x := by simpa [hxid] using hv_ne
    simp only [PValEnv.set, hvne', ↓reduceIte] at hρ
    obtain ⟨bv, hbv, hev⟩ := hexcl v hv_mem hlive hex hno hps cidx fs sc hρ
    exact ⟨bv, by simp [HValEnv.set, hvne', hbv], hev⟩

public theorem exclCtorHeap_put_ctor {rf : RcFrame} {x : Nat} {vx : RcVar}
    {pv : PVal} {bv_x : BitVec 64}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup)
    (hexcl : ExclCtorHeap rf) (hxid : vx.id = x) (hev_x : bv_x &&& 1#64 = 0#64) :
    ExclCtorHeap {
      ctx := rf.ctx.put vx, envP := rf.envP.set x pv,
      envH := rf.envH.set x vx.ty (Word.i64 bv_x), extH := rf.extH, ghostH := rf.ghostH } := by
  intro v hv hlive hex hno hps cidx fs sc hρ
  rcases (RcCtx.put_mem_iff hnd).mp hv with rfl | ⟨hv_mem, hv_ne⟩
  · refine ⟨bv_x, ?_, hev_x⟩
    simp [hxid, HValEnv.set]
  · have hvne' : v.id ≠ x := by simpa [hxid] using hv_ne
    simp only [PValEnv.set, hvne', ↓reduceIte] at hρ
    obtain ⟨bv, hbv, hev⟩ := hexcl v hv_mem hlive hex hno hps cidx fs sc hρ
    exact ⟨bv, by simp [HValEnv.set, hvne', hbv], hev⟩

public theorem binderFreshOwned_mem_false {ctx : RcCtx} {x : Nat}
    (hfr : binderFreshOwned ctx x = true) :
    ∀ p ∈ ctx.sharedPreds, p.1 ≠ x ∧ p.2 ≠ x := by
  simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hfr
  intro p hp
  exact hfr.1.2 p hp

public theorem noRcCorrect_bindOwned {ctx : RcCtx}
    (hnd : (ctx.vars.map RcVar.id).Nodup) (hno : NoRcCorrect ctx)
    (x : Nat) (ty : LcTy) (excl pers rtok : Bool) :
    NoRcCorrect (ctx.bindOwned x ty excl pers rtok) := by
  apply noRcCorrect_put hnd hno
  simp

public theorem noRcCorrect_bindBorrowed {ctx : RcCtx}
    (hnd : (ctx.vars.map RcVar.id).Nodup) (hno : NoRcCorrect ctx)
    (x : Nat) (ty : LcTy) (p? : Option Nat) (pers : Bool) :
    NoRcCorrect (ctx.bindBorrowed x ty p? pers) := by
  apply noRcCorrect_put hnd hno
  simp

public theorem sharedBoolPreds_bind_isShared {ctx : RcCtx} {x y : Nat}
    (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hfr : binderFreshOwned ctx x = true)
    (hsp : SharedBoolPreds ctx) :
    let ctx1 := ctx.bindOwned x LcTy.uint8
    SharedBoolPreds { vars := ctx1.vars, sharedPreds := (x, y) :: ctx1.sharedPreds } := by
  intro ctx1 p hp
  simp only [List.mem_cons] at hp
  let vx : RcVar := {
    id := x, ty := LcTy.uint8, noRc := !LcTy.uint8.needsRc,
    persistent := if (!LcTy.uint8.needsRc) = true then false else false,
    owned := if (!LcTy.uint8.needsRc || false) = true then 0 else 1,
    excl := if (!LcTy.uint8.needsRc || false) = true then false else false,
    resetTok := if (!LcTy.uint8.needsRc || false) = true then false else false }
  rcases hp with rfl | hp
  · refine ⟨vx, ?_, rfl⟩
    change (ctx.put vx).get? x = some vx
    rw [RcCtx.put_get? hnd vx x]; simp [vx]
  · have hsp1 := sharedBoolPreds_put_fresh hnd hsp (v := vx)
      (fun q hq => (binderFreshOwned_mem_false hfr q hq).1)
    exact hsp1 p hp

end CtxAndShadowHelpers

end LeanQbe.T.LeanLCNF.Sem
