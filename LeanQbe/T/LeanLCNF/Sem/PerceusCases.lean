module

public import LeanQbe.T.LeanLCNF.Sem.PerceusDec
import LeanQbe.T.Logic.ProofKit

/-!
# LCNF Perceus-Sound Simulation: `cases`, `markScalarBranch`, and `markExcl`

Tag extraction (`casesTag_step`), branch specialization (`markScalarBranch`, `markExcl`),
and stepwise simulation (`cases_step`).
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

section HandleAndReachHelpers

private theorem invalidateChildren_varHandles_eq (envH : HValEnv) (v : RcVar) (x : Nat) :
    varHandles envH
      (if (v.parent? == some x) = true then { v with borrowed := false, parent? := none } else v) =
      varHandles envH v := by
  by_cases hpx : (v.parent? == some x) = true <;> simp [hpx, varHandles]

private theorem invalidateChildren_localHandles_eq (ctx : RcCtx) (envH : HValEnv) (x : Nat) :
    localHandles (ctx.invalidateChildren x) envH = localHandles ctx envH := by
  simp only [localHandles, RcCtx.invalidateChildren, List.map_map]
  congr 1
  apply List.map_congr_left
  intro v _
  exact invalidateChildren_varHandles_eq envH v x

private theorem invalidateChildren_localHandlesExcept_eq (ctx : RcCtx) (envH : HValEnv)
    (x s : Nat) :
    localHandlesExcept (ctx.invalidateChildren x) envH s = localHandlesExcept ctx envH s := by
  let fn : RcVar → RcVar := fun v =>
    if (v.parent? == some x) = true then { v with borrowed := false, parent? := none } else v
  have hflt : List.filter (fun v => v.id != s) (ctx.vars.map fn) =
      (List.filter (fun v => v.id != s) ctx.vars).map fn := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro v _
    dsimp only [fn, Function.comp_apply]
    by_cases hpx : (v.parent? == some x) = true <;> simp [hpx]
  simp only [localHandlesExcept, RcCtx.invalidateChildren]
  change (List.map (varHandles envH) (List.filter (fun v => v.id != s) (ctx.vars.map fn))).flatten =
    (List.map (varHandles envH) (List.filter (fun v => v.id != s) ctx.vars)).flatten
  rw [hflt, List.map_map]
  congr 1
  apply List.map_congr_left
  intro v _
  exact invalidateChildren_varHandles_eq envH v x

private theorem noRcCorrect_invalidateChildren {ctx : RcCtx} (hn : NoRcCorrect ctx) (x : Nat) :
    NoRcCorrect (ctx.invalidateChildren x) := by
  intro u hu hno
  obtain ⟨w, hw, _, hty, hnow, _⟩ := invalidateChildren_live_back x hu
  rw [hty]
  rw [hnow] at hno
  exact hn w hw hno

private theorem backed_of_perm {objs : List LcnfObj} {h1 h2 : List (BitVec 64)}
    (hp : h1.Perm h2) {a : BitVec 64} (hb : Backed objs h1 a) : Backed objs h2 a := by
  rcases hb with hpers | ⟨r, hr, hreach⟩
  · exact Or.inl hpers
  · exact Or.inr ⟨r, hp.mem_iff.mp hr, hreach⟩

private theorem obj_eq_of_mem_nodup {objs : List LcnfObj} (hnd : (objs.map LcnfObj.addr).Nodup)
    {o1 o2 : LcnfObj} (h1 : o1 ∈ objs) (h2 : o2 ∈ objs) (ha : o1.addr = o2.addr) : o1 = o2 := by
  induction objs with
  | nil => nomatch h1
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h1 with rfl | h1s
    · rcases List.mem_cons.mp h2 with rfl | h2s
      · rfl
      · exact absurd (ha ▸ List.mem_map.mpr ⟨_, h2s, rfl⟩) hnd.1
    · rcases List.mem_cons.mp h2 with rfl | h2s
      · exact absurd (ha.symm ▸ List.mem_map.mpr ⟨_, h1s, rfl⟩) hnd.1
      · exact ih hnd.2 h1s h2s

private theorem nonPersistReach_end_nonPersist {objs : List LcnfObj} {r v : BitVec 64}
    (hr : NonPersistReach objs r v) : ∃ o, o ∈ objs ∧ o.addr = v ∧ o.rc ≠ 0#32 := by
  cases hr with
  | refl h => exact h
  | step _ _ _ h => exact h

private theorem nonPersistRefs_pos_of_mem {objs : List LcnfObj} {o : LcnfObj} (ho : o ∈ objs)
    (hne : o.rc ≠ 0#32) {v : BitVec 64} (hv : v ∈ o.childFields) : 0 < nonPersistRefs objs v := by
  have hfold : ∀ (acc : Nat) (l : List LcnfObj),
      acc ≤ List.foldl
        (fun a (p : LcnfObj) => if p.rc = 0#32 then a else a + List.count v p.childFields)
        acc l := by
    intro acc l
    induction l generalizing acc with
    | nil => exact Nat.le_refl acc
    | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases h0 : LcnfObj.rc x = 0#32
      · simp only [h0, ↓reduceIte]; exact ih acc
      · simp only [h0, ↓reduceIte]
        exact Nat.le_trans (Nat.le_add_right acc _) (ih _)
  have hstep : ∀ (acc : Nat) (l : List LcnfObj), o ∈ l →
      0 < List.foldl
        (fun a (p : LcnfObj) => if p.rc = 0#32 then a else a + List.count v p.childFields)
        acc l := by
    intro acc l hl
    induction l generalizing acc with
    | nil => nomatch hl
    | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hl with rfl | hxs
      · have hc : 0 < List.count v o.childFields := List.count_pos_iff.mpr hv
        simp only [hne, ↓reduceIte]
        exact Nat.lt_of_lt_of_le (by omega) (hfold _ xs)
      · exact ih _ hxs
  exact hstep 0 objs ho

private theorem nonPersistReach_eq_or_refs_pos {rt : BitVec 64} {σ : HState}
    (hc : HeapClean rt σ) {r bv : BitVec 64} (hr : NonPersistReach σ.objs r bv) :
    r = bv ∨ 0 < nonPersistRefs σ.objs bv := by
  cases hr with
  | refl => exact Or.inl rfl
  | step hru hstep _ _ =>
    obtain ⟨o, ho, hoa, hv⟩ := hstep
    obtain ⟨ou, hou, houa, hou_rc⟩ := nonPersistReach_end_nonPersist hru
    have hoeq : o = ou := obj_eq_of_mem_nodup hc.2 ho hou (hoa.trans houa.symm)
    exact Or.inr (nonPersistRefs_pos_of_mem ho (hoeq ▸ hou_rc) hv)

private theorem mem_localHandlesExcept_of_mem {ctx : RcCtx} {envH : HValEnv} {w : RcVar}
    (hw : w ∈ ctx.vars) {s : Nat} (hne : w.id ≠ s) {a : BitVec 64}
    (ha : a ∈ varHandles envH w) : a ∈ localHandlesExcept ctx envH s := by
  unfold localHandlesExcept
  rw [List.mem_flatten]
  refine ⟨varHandles envH w, List.mem_map.mpr ⟨w, List.mem_filter.mpr ⟨hw, ?_⟩, rfl⟩, ha⟩
  simp [hne]

private theorem varHandles_mem_of_live {envH : HValEnv} {w : RcVar} (hno : w.noRc = false)
    (hp : w.persistent = false) (hrt : w.resetTok = false) (hown : 0 < w.owned)
    {bv : BitVec 64} (hh : envH w.id = some (w.ty, Word.i64 bv)) (hev : bv &&& 1#64 = 0#64) :
    bv ∈ varHandles envH w := by
  unfold varHandles
  have hskip : (w.noRc || w.persistent || w.resetTok || w.owned == 0) = false := by
    cases h : (w.owned == 0) with
    | false => simp [hno, hp, hrt]
    | true => simp at h; omega
  rw [hskip]
  simp only [Bool.false_eq_true, ↓reduceIte, hh]
  dsimp only [Word.toBV64?, Word.i64]
  simp only [hev, beq_self_eq_true, ↓reduceIte, List.mem_replicate]
  exact ⟨by omega, trivial⟩

private theorem not_borrowed_of_sharedZero {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) {b tgt : Nat} (hp : (b, tgt) ∈ rf.ctx.sharedPreds)
    {vb vt : RcVar} (hgb : rf.ctx.get? b = some vb) (hgt : rf.ctx.get? tgt = some vt)
    (hlb : vb.isLive = true) (hno : vt.noRc = false) (hpers : vt.persistent = false)
    (hown : 0 < vt.owned) (henv0 : (rf.envP b).bind PVal.tag? = some 0) :
    vt.borrowed = false := by
  by_cases hbr : vt.borrowed = true
  · exfalso
    obtain ⟨bv, hht, hev, hzero_fn⟩ :=
      (hinv.2.2.2.2 (b, tgt) hp vb vt hgb hgt hlb hno hpers).1 henv0
    obtain ⟨hzero, o0, ho0, hoa0, horc0⟩ := hzero_fn hown
    have horc_ne0 : o0.rc ≠ 0#32 := by
      intro h0; rw [h0] at horc0; simp at horc0; omega
    have hns : ¬vt.ty.isScalar = true := fun hs => by
      have := hnorc vt (RcCtx.get?_mem hgt).1 hno
      cases hty : vt.ty <;> simp [LcTy.isScalar, LcTy.needsRc, hty] at hs this
    have hlt : vt.isLive = true := by unfold RcVar.isLive; simp [hbr]
    obtain ⟨_, _, _, hht', _, hnon⟩ := hinv.2.2.2.1 vt (RcCtx.get?_mem hgt).1 hlt
    rw [(RcCtx.get?_mem hgt).2] at hht'
    obtain ⟨bv', hwbv, _, _, _, hbor⟩ := hnon hns
    rw [hwbv] at hht'
    have hbveq : bv' = bv := by rw [hht] at hht'; cases hht'; rfl
    subst hbveq
    obtain ⟨_, hback_sub⟩ := hbor hno hpers hbr hev
    have no_pers : ¬∃ op, op ∈ σ.objs ∧ op.addr = bv' ∧ op.rc = 0#32 := by
      rintro ⟨op, hop, hopa, hop0⟩
      have hoeq := obj_eq_of_mem_nodup hinv.1.2 hop ho0 (hopa.trans hoa0.symm)
      exact horc_ne0 (hoeq ▸ hop0)
    cases hpar : vt.parent? with
    | none =>
      rw [hpar] at hback_sub
      rcases hback_sub with hpers' | ⟨r, hr, hreach⟩
      · exact no_pers hpers'
      · rcases nonPersistReach_eq_or_refs_pos hinv.1 hreach with rfl | hpos
        · have hc : 0 < List.count r
              (localHandlesExcept rf.ctx rf.envH tgt ++ rf.extH ++ rf.ghostH) :=
            List.count_pos_iff.mpr (by simp [hr])
          simp only [List.count_append] at hzero hc
          omega
        · omega
    | some p =>
      rw [hpar] at hback_sub
      obtain ⟨pw, _, hpid, _, _, _, pback⟩ := hback_sub
      obtain ⟨pw', hpw'm, hpw'id, pno', ppers', pown', hpw'br⟩ :=
        hpo vt (RcCtx.get?_mem hgt).1 p hpar
      have hpne : p ≠ tgt := fun heq => by
        have := rcVar_eq_of_mem_nodup hinv.2.1 hpw'm (RcCtx.get?_mem hgt).1
          (hpw'id.trans (heq.trans (RcCtx.get?_mem hgt).2.symm))
        rw [this, hbr] at hpw'br; cases hpw'br
      have hpown_pos : 0 < pw'.owned := pown'
      have hpw'_live : pw'.isLive = true := by
        unfold RcVar.isLive; simp [hpown_pos]
      have hp_ns : ¬pw'.ty.isScalar = true := fun hs => by
        have := hnorc pw' hpw'm pno'
        cases hty : pw'.ty <;> simp [LcTy.isScalar, LcTy.needsRc, hty] at hs this
      obtain ⟨_, wp, _, hhpw, _, hnon_pw⟩ := hinv.2.2.2.1 pw' hpw'm hpw'_live
      rw [hpw'id] at hhpw
      obtain ⟨bp, hwbp, _⟩ := hnon_pw hp_ns
      rw [hwbp] at hhpw
      rcases pback with hpers' | ⟨r, hr, hreach⟩
      · exact no_pers hpers'
      · rcases nonPersistReach_eq_or_refs_pos hinv.1 hreach with rfl | hpos
        · have hhpw' : rf.envH p = some (pw'.ty, Word.i64 r) := by
            rw [hhpw] at hr ⊢
            simp only [Word.toBV64?, Word.i64, List.mem_append, List.mem_cons,
              List.mem_nil_iff, or_false] at hr
            rcases hr with rfl | hmem
            · rfl
            · exfalso
              have hc : 0 < List.count r
                  (localHandlesExcept rf.ctx rf.envH tgt ++ rf.extH ++ rf.ghostH) :=
                List.count_pos_iff.mpr (by simp [hmem])
              simp only [List.count_append] at hzero hc
              omega
          have hvh := varHandles_mem_of_live pno' ppers' (hclean pw' hpw'm).2.2.2.2 pown'
            (hpw'id ▸ hhpw') hev
          have hmem_ex := mem_localHandlesExcept_of_mem hpw'm
            (fun heq => hpne (hpw'id.symm.trans heq)) hvh
          have hc : 0 < List.count r
              (localHandlesExcept rf.ctx rf.envH tgt ++ rf.extH ++ rf.ghostH) :=
            List.count_pos_iff.mpr (by simp [hmem_ex])
          simp only [List.count_append] at hzero hc
          omega
        · omega
  · exact Bool.eq_false_iff.mpr hbr

end HandleAndReachHelpers

section CasesStep

private theorem boxNat_shr1_toNat {n : Nat} (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 (2 * n + 1) >>> 1).toNat = n := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [Nat.shiftRight_eq_div_pow]
  omega

private theorem bv_setWidth_shl1_or1_shr1 {w : Nat} (hw : w < 64) (v : BitVec w) :
    ((BitVec.setWidth 64 v <<< 1 ||| 1#64) >>> 1).toNat = v.toNat := by
  rw [bv64_tagged_bits_eq_ofNat hw v]
  exact boxNat_shr1_toNat
    (Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by decide) (by omega)))

private theorem bv64_setWidth_self (bv : BitVec 64) : BitVec.setWidth 64 bv = bv := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- From `VarInv`, `ShadowOk`, and `casesResSafe`, extract `HState.casesTag rf.envH x tag`. -/
public theorem casesTag_step {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv}
    (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    {x tag : Nat} {vx : RcVar} (hgx : rf.ctx.get? x = some vx) (hlx : vx.isLive = true)
    {pv : PVal} (hρx : ρP x = some pv) (htag : pv.tag? = some tag)
    (hsafe : casesResSafe vx.ty pv) :
    σ.casesTag rf.envH x tag := by
  have ⟨hvm, hxid⟩ := RcCtx.get?_mem hgx
  obtain ⟨pv', w, hp, hh, hrep, hnon⟩ := hinv.2.2.2.1 vx hvm hlx
  rw [hxid] at hp hh
  have hsh := hshd vx hvm hlx
  rw [hxid] at hsh
  have ⟨htag', hsafe'⟩ : pv'.tag? = some tag ∧ casesResSafe vx.ty pv' := by
    cases hi : isVarScalarInit sm x
    · simp only [hi, Bool.false_eq_true, ite_false] at hsh
      obtain ⟨_, _, _, cidx, fs, _, hscal, hρ0, hE0, _⟩ := hsh
      rw [hρx] at hρ0; cases hρ0
      rw [hp] at hE0; cases hE0
      simp only [PVal.tag?, Option.some.injEq] at htag
      exact ⟨by simp [PVal.tag?, htag], trivial⟩
    · simp only [hi, ite_true] at hsh
      rw [hρx, hp] at hsh; cases hsh
      exact ⟨htag, hsafe⟩
  by_cases hsc : vx.ty.isScalar = true
  · simp only [ValRep, hsc, ↓reduceIte] at hrep
    rcases hrep with ⟨bv, rfl, rfl⟩ | ⟨cidx, rfl, hlt, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [PVal.tag?, Option.some.injEq] at htag'
      simp [HState.casesTag, hh, hsc, htag']
    · simp only [PVal.tag?, Option.some.injEq] at htag'
      simp only [HState.casesTag, hh, hsc, ↓reduceIte, true_and]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, htag']
    · simp only [PVal.tag?, Option.some.injEq] at htag'
      subst htag'
      simp [HState.casesTag, hh, hsc]
  · have hnsf : vx.ty.isScalar = false := Bool.eq_false_iff.mpr hsc
    obtain ⟨bv, hwbv, _⟩ := hnon hsc
    rw [hwbv] at hh hrep
    simp only [ValRep, hnsf, Bool.false_eq_true, ↓reduceIte] at hrep
    obtain ⟨bv0, hweq0, hobj, ho1, ht1⟩ := hrep
    have hbveq : bv = bv0 := by cases hweq0; rfl
    subst hbveq
    unfold HState.casesTag
    rw [hh]
    have hwidth : 64 = vx.ty.width := by
      cases h : vx.ty <;> first | rfl | (rw [h] at hsc; exact absurd rfl hsc)
    refine ⟨hwidth, ?_⟩
    rw [hnsf]; dsimp only
    have h64 : BitVec.setWidth 64 bv = bv := bv64_setWidth_self bv
    rw [h64]
    cases pv' with
    | erased =>
      simp only [PVal.tag?, Option.some.injEq] at htag'
      dsimp only [ObjRep] at hobj
      have hodd : bv &&& 1#64 ≠ 0#64 := by rw [hobj]; decide
      have hnot_obj : ¬ (vx.ty = .object) := fun h => absurd (ho1 h) hodd
      subst htag'
      have hshr : (bv >>> 1).toNat = 0 := by rw [hobj]; decide
      by_cases hobj_ty : vx.ty = .object
      · exact absurd hobj_ty hnot_obj
      · by_cases htag_ty : vx.ty = .tagged <;> simp [hobj_ty, htag_ty, hodd, hshr]
    | bits bw v =>
      have hbw : bw < 64 := by
        cases hsafe' with
        | inl h => exact absurd h hsc
        | inr h => exact h
      simp only [PVal.tag?, Option.some.injEq] at htag'
      dsimp only [ObjRep] at hobj
      rcases hobj with ⟨_, hbv⟩ | ⟨hw64, _⟩
      · have hodd : bv &&& 1#64 ≠ 0#64 := by
          rw [hbv]; exact bv64_tagged_bits_and1 hbw v
        have hnot_obj : ¬ (vx.ty = .object) := fun h => absurd (ho1 h) hodd
        have hshr : (bv >>> 1).toNat = v.toNat := by
          rw [hbv]; exact bv_setWidth_shl1_or1_shr1 hbw v
        by_cases hobj_ty : vx.ty = .object
        · exact absurd hobj_ty hnot_obj
        · by_cases htag_ty : vx.ty = .tagged <;> simp [hobj_ty, htag_ty, hodd, hshr, htag']
      · omega
    | nat n =>
      obtain ⟨hnlt, hne_obj⟩ := hsafe'
      simp only [PVal.tag?, Option.some.injEq] at htag'
      dsimp only [ObjRep] at hobj
      have hbv := (natRep_small hnlt).mp hobj
      have hodd : bv &&& 1#64 ≠ 0#64 := hbv ▸ boxNat_and1_ne_zero n
      have hnot_obj : ¬ (vx.ty = .object) := fun h => absurd (ho1 h) hodd
      have hshr : (bv >>> 1).toNat = n := hbv ▸ boxNat_shr1_toNat hnlt
      by_cases hobj_ty : vx.ty = .object
      · exact absurd hobj_ty hnot_obj
      · by_cases htag_ty : vx.ty = .tagged <;> simp [hobj_ty, htag_ty, hodd, hshr, htag']
    | ctor cidx fs sc =>
      simp only [PVal.tag?, Option.some.injEq] at htag'
      dsimp only [ObjRep] at hobj
      rcases hobj with ⟨rfl, rfl, hclt, hbv⟩ | ⟨_, o, ho, hoa, _, ht, _, _, _⟩
      · have hodd : bv &&& 1#64 ≠ 0#64 := hbv ▸ boxNat_and1_ne_zero cidx
        have hnot_obj : ¬ (vx.ty = .object) := fun h => absurd (ho1 h) hodd
        have hshr : (bv >>> 1).toNat = cidx := hbv ▸ boxNat_shr1_toNat hclt
        by_cases hobj_ty : vx.ty = .object
        · exact absurd hobj_ty hnot_obj
        · by_cases htag_ty : vx.ty = .tagged <;> simp [hobj_ty, htag_ty, hodd, hshr, htag']
      · have hev : bv &&& 1#64 = 0#64 := hoa ▸ obj_addr_and1_zero (hinv.1.1.2.1 o ho)
        have hnot_tag : ¬ (vx.ty = .tagged) := fun h => absurd hev (ht1 h)
        have hodd_f : ¬ (bv &&& 1#64 ≠ 0#64) := fun h => h hev
        by_cases hobj_ty : vx.ty = .object
        · simp [hobj_ty]; exact ⟨o, ho, hoa, hinv.1.1.2.1 o ho, (ht.trans htag').symm⟩
        · simp [hobj_ty, hnot_tag, hodd_f]
          exact ⟨o, ho, hoa, hinv.1.1.2.1 o ho, (ht.trans htag').symm⟩
    | str _ | arr _ | barr _ | int _ | clo _ _ _ => cases htag'

private theorem cleanVar_markScalarBranch (v : RcVar) :
    CleanVar
      { id := v.id, ty := v.ty, noRc := true, persistent := false, owned := 0,
        borrowed := false, parent? := none, excl := false, resetTok := false } := by
  simp [CleanVar]

private theorem markScalarBranch_nodup {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (x : Nat) : ((ctx.markScalarBranch x).vars.map RcVar.id).Nodup := by
  unfold RcCtx.markScalarBranch
  cases hgx : ctx.get? x with
  | none => exact hnd
  | some vx =>
    by_cases hty : (vx.ty == .tobject || vx.ty == .tagged) = true
    · simp only [hty, ↓reduceIte]
      let vx' : RcVar := { id := vx.id, ty := vx.ty, noRc := true }
      have hnd1 := ctx.put_nodup hnd vx'
      unfold RcCtx.invalidateChildren; dsimp only; rw [List.map_map]
      have heq : (List.map (RcVar.id ∘ fun v =>
          if v.parent? == some x then { v with borrowed := false, parent? := none } else v)
          (ctx.put vx').vars) = (ctx.put vx').vars.map RcVar.id := by
        apply List.map_congr_left
        intro u _
        dsimp only [Function.comp_apply]
        by_cases hpx : u.parent? = some x <;> simp [hpx]
      rw [heq]; exact hnd1
    · simp only [hty, Bool.false_eq_true, ↓reduceIte]; exact hnd

private theorem tagged_obj_bv_odd {ty : LcTy} {pv : PVal} {bv : BitVec 64} {objs : List LcnfObj}
    (htag : isTaggedPVal pv = true) (hrep : ValRep ty pv (Word.i64 bv) objs)
    (hns : ¬ty.isScalar = true) : bv &&& 1#64 ≠ 0#64 := by
  have hnsf : ty.isScalar = false := Bool.eq_false_iff.mpr hns
  simp only [ValRep, hnsf, Bool.false_eq_true, ↓reduceIte] at hrep
  obtain ⟨bv0, hweq, hobj, _, _⟩ := hrep
  have hbveq : bv = bv0 := by cases hweq; rfl
  subst hbveq
  cases pv with
  | erased =>
    dsimp only [ObjRep] at hobj
    rw [hobj]; decide
  | bits w v =>
    simp only [isTaggedPVal, decide_eq_true_eq] at htag
    dsimp only [ObjRep] at hobj
    rcases hobj with ⟨_, hbv⟩ | ⟨hw64, _⟩
    · rw [hbv]; exact bv64_tagged_bits_and1 htag v
    · omega
  | nat n =>
    simp only [isTaggedPVal, decide_eq_true_eq] at htag
    dsimp only [ObjRep] at hobj
    rw [(natRep_small htag).mp hobj]
    exact boxNat_and1_ne_zero n
  | ctor cidx fs sc =>
    cases fs with
    | cons _ _ => simp [isTaggedPVal] at htag
    | nil =>
      cases sc with
      | cons _ _ => simp [isTaggedPVal] at htag
      | nil =>
        simp only [isTaggedPVal, decide_eq_true_eq] at htag
        dsimp only [ObjRep] at hobj
        rcases hobj with ⟨_, _, _, hbv⟩ | ⟨hne, _⟩
        · rw [hbv]; exact boxNat_and1_ne_zero cidx
        · exact absurd ⟨rfl, rfl⟩ hne
  | str _ | arr _ | barr _ | int _ | clo _ _ _ => simp [isTaggedPVal] at htag

private theorem varHandles_eq_empty_of_bv_odd {envH : HValEnv} {v : RcVar} {bv : BitVec 64}
    (hh : envH v.id = some (v.ty, Word.i64 bv)) (hodd : bv &&& 1#64 ≠ 0#64) :
    varHandles envH v = [] := by
  unfold varHandles
  by_cases hskip : (v.noRc || v.persistent || v.resetTok || v.owned == 0) = true
  · simp [hskip]
  · have hmod : (bv &&& 1#64 == 0#64) = false := by
      cases h : (bv &&& 1#64 == 0#64) with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp h) hodd
    have hf : (v.noRc || v.persistent || v.resetTok || v.owned == 0) = false :=
      Bool.eq_false_iff.mpr hskip
    simp only [hf, Bool.false_eq_true, ↓reduceIte, hh, Word.toBV64?, Word.i64, hmod]

private theorem markScalarBranch_handles {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv}
    (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    {x : Nat} {vx : RcVar} (hgx : rf.ctx.get? x = some vx) (hlx : vx.isLive = true)
    {pv : PVal} (hρx : ρP x = some pv) (htag : isTaggedPVal pv = true)
    (hty : (vx.ty == .tobject || vx.ty == .tagged) = true) :
    let vx' : RcVar := { id := vx.id, ty := vx.ty, noRc := true }
    let ctx1 := (rf.ctx.put vx').invalidateChildren x
    (localHandles ctx1 rf.envH).Perm (localHandles rf.ctx rf.envH) ∧
      ∀ s, s ≠ x → ∀ u ∈ ctx1.vars, u.id = s →
        ∀ w ∈ rf.ctx.vars, w.id = s →
          u.noRc = w.noRc → u.persistent = w.persistent → u.owned = w.owned →
            u.resetTok = w.resetTok →
              ∀ a, List.count a (localHandlesExcept ctx1 rf.envH s) =
                List.count a (localHandlesExcept rf.ctx rf.envH s) := by
  intro vx' ctx1
  have hxm := (RcCtx.get?_mem hgx).1
  have hxid := (RcCtx.get?_mem hgx).2
  have hns : ¬vx.ty.isScalar = true := by
    intro hsc
    cases h : vx.ty <;> rw [h] at hsc hty <;>
      first | (revert hsc; decide) | (revert hty; decide)
  obtain ⟨pv', hρ', htag'⟩ := shadow_isTaggedPVal hshd hxm hlx (hxid.symm ▸ hρx) htag
  obtain ⟨pv0, w0, hp0, hh0, hrep0, hnon0⟩ := hinv.2.2.2.1 vx hxm hlx
  rw [hxid] at hp0 hh0 hρ'
  rw [hρ'] at hp0; cases hp0
  obtain ⟨bv, rfl, _⟩ := hnon0 hns
  have hodd := tagged_obj_bv_odd htag' hrep0 hns
  have hvx_empty := varHandles_eq_empty_of_bv_odd (hxid ▸ hh0) hodd
  have hvx'_empty : varHandles rf.envH vx' = [] := by simp [varHandles, vx']
  have hnd1 : (ctx1.vars.map RcVar.id).Nodup := by
    have h := markScalarBranch_nodup hinv.2.1 x
    simp only [RcCtx.markScalarBranch, hgx, hty, ↓reduceIte] at h
    exact h
  have hperm : (localHandles ctx1 rf.envH).Perm (localHandles rf.ctx rf.envH) := by
    have h1 := localHandles_put_perm hinv.2.1 rf.envH vx'
    rw [hvx'_empty, List.nil_append] at h1
    have h2 := localHandles_perm_filter hinv.2.1 rf.envH vx hxm
    rw [hvx_empty, List.nil_append] at h2
    have h3 : vx'.id = vx.id := rfl
    rw [h3] at h1
    rw [invalidateChildren_localHandles_eq]
    exact h1.trans h2.symm
  refine ⟨hperm, fun s _ u hu hus w hw hws hno hp ho hr a => ?_⟩
  have hvh_eq : varHandles rf.envH u = varHandles rf.envH w := by
    simp only [varHandles, hno, hp, hr, ho, hus, hws]
  have hpu := (localHandles_perm_filter hnd1 rf.envH u hu).count_eq a
  have hpw := (localHandles_perm_filter hinv.2.1 rf.envH w hw).count_eq a
  have hpc := hperm.count_eq a
  simp only [List.count_append, hvh_eq, hus, hws] at hpu hpw
  omega

private theorem markScalarBranch_var_invs {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hsth : SharedTargetsHeap rf) (hexcl : ExclCtorHeap rf)
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv}
    (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    {x : Nat} {vx : RcVar} (hgx : rf.ctx.get? x = some vx) (hlx : vx.isLive = true)
    {pv : PVal} (hρx : ρP x = some pv) (htag : isTaggedPVal pv = true)
    (hty : (vx.ty == .tobject || vx.ty == .tagged) = true) :
    let vx' : RcVar := { id := vx.id, ty := vx.ty, noRc := true }
    let ctx1 := (rf.ctx.put vx').invalidateChildren x
    let rf1 : RcFrame := { rf with ctx := ctx1 }
    (localHandles ctx1 rf.envH).Perm (localHandles rf.ctx rf.envH) →
      (∀ u ∈ ctx1.vars, VarInv u rf1 σ.objs) ∧
        SharedTargetsHeap rf1 ∧ ExclCtorHeap rf1 ∧ ShadowOk sm ctx1 ρP rf1.envP ∧
        (∀ a, IsolatedAddr a rf σ.objs → IsolatedAddr a rf1 σ.objs) := by
  intro vx' ctx1 rf1 hperm
  have hxm := (RcCtx.get?_mem hgx).1
  have hxid := (RcCtx.get?_mem hgx).2
  have hpo1 : ParentsOwned ctx1 := by
    have h := parentsOwned_markScalarBranch hinv.2.1 hclean hpo x
    simp only [RcCtx.markScalarBranch, hgx, hty, ↓reduceIte] at h
    exact h
  have hfh_perm : (frameHandles rf1).Perm (frameHandles rf) :=
    (hperm.append_right rf.extH).append_right rf.ghostH
  have hns : ¬vx.ty.isScalar = true := by
    intro hsc
    cases h : vx.ty <;> rw [h] at hsc hty <;>
      first | (revert hsc; decide) | (revert hty; decide)
  obtain ⟨pv', hρ', htag'⟩ := shadow_isTaggedPVal hshd hxm hlx (hxid.symm ▸ hρx) htag
  obtain ⟨pv0, w0, hp0, hh0, hrep0, hnon0⟩ := hinv.2.2.2.1 vx hxm hlx
  rw [hxid] at hp0 hh0 hρ'
  rw [hρ'] at hp0; cases hp0
  obtain ⟨bv, rfl, _⟩ := hnon0 hns
  have hodd := tagged_obj_bv_odd htag' hrep0 hns
  have hback : ∀ {u : RcVar}, u ∈ ctx1.vars → u.id ≠ x →
      ∃ w, w ∈ rf.ctx.vars ∧ u.id = w.id ∧ u.ty = w.ty ∧ u.noRc = w.noRc ∧
        u.persistent = w.persistent ∧ u.owned = w.owned ∧ u.excl = w.excl ∧
        u.resetTok = w.resetTok ∧ (u.borrowed = true → w.borrowed = true ∧ w.parent? = u.parent?) ∧
        (u.isLive = true → w.isLive = true) := by
    intro u hu hne
    obtain ⟨w, hw, hid, htyw, hnow, hpw, how, hew, hrw, hbrw⟩ := invalidateChildren_live_back x hu
    rcases (RcCtx.put_mem_iff hinv.2.1).mp hw with rfl | ⟨hwm, _⟩
    · exact absurd (hid.trans hxid) hne
    · refine ⟨w, hwm, hid, htyw, hnow, hpw, how, hew, hrw, hbrw, fun hl => ?_⟩
      unfold RcVar.isLive at hl ⊢
      rw [hnow, hpw, how, hrw] at hl
      simp only [Bool.or_eq_true] at hl ⊢
      rcases hl with (((ha | hb) | hc) | hd) | he
      · exact Or.inl (Or.inl (Or.inl (Or.inl ha)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr hb)))
      · exact Or.inl (Or.inl (Or.inr hc))
      · exact Or.inl (Or.inr (hbrw hd).1)
      · exact Or.inr he
  refine ⟨fun u hu hul => ?_, fun p hp vx1 hgv hno => ?_, ?_, ?_, fun a hiso => ?_⟩
  · by_cases hux : u.id = x
    · obtain ⟨w, hw, hid, htyw, hnow, hpw, how, hew, hrw, hbrw⟩ := invalidateChildren_live_back x hu
      rcases (RcCtx.put_mem_iff hinv.2.1).mp hw with rfl | ⟨_, hne⟩
      · have hu_id : u.id = x := hid.trans hxid
        have hu_no : u.noRc = true := hnow
        have hu_pers : u.persistent = false := hpw
        have hu_ex : u.excl = false := hew
        rw [hu_id, htyw]
        refine ⟨pv', Word.i64 bv, hρ', hh0, hrep0, fun _ => ?_⟩
        refine ⟨bv, rfl, (fun _ => hodd), (fun h => by rw [hu_pers] at h; cases h),
          (fun h => by rw [hu_ex] at h; cases h), (fun h => by rw [hu_no] at h; cases h)⟩
      · exact absurd (hid.symm.trans hux) (fun heq => hne (heq.trans hxid.symm))
    · obtain ⟨w, hwm, hid, htyw, hnow, hpw, how, hew, hrw, hbrw, hlw⟩ := hback hu hux
      obtain ⟨pu, wu, hpu, hhu, hrepu, hnonu⟩ := hinv.2.2.2.1 w hwm (hlw hul)
      rw [← hid] at hpu hhu
      refine ⟨pu, wu, hpu, htyw ▸ hhu, htyw ▸ hrepu, fun hnsu => ?_⟩
      obtain ⟨bvu, hwbv, hnou, hpersu, hexu, hboru⟩ := hnonu (htyw ▸ hnsu)
      refine ⟨bvu, hwbv, (fun hu_no => hnou (hnow ▸ hu_no)),
        (fun hu_ps hev => hpersu (hpw ▸ hu_ps) hev),
        (fun hu_ex => by
          obtain ⟨hn, hp, ho, hbr⟩ := hexu (hew ▸ hu_ex)
          exact ⟨hnow ▸ hn, hpw ▸ hp, how ▸ ho, hbr⟩),
        (fun hu_no hu_ps hu_br hev => by
          obtain ⟨hb1, hb2⟩ := hboru (hnow ▸ hu_no) (hpw ▸ hu_ps) (hbrw hu_br).1 hev
          refine ⟨backed_of_perm hfh_perm.symm hb1, ?_⟩
          cases hup : u.parent? with
          | none =>
            have hwp : w.parent? = none := (hbrw hu_br).2.trans hup
            rw [hwp] at hb2; exact hb2
          | some p =>
            have hwp : w.parent? = some p := (hbrw hu_br).2.trans hup
            rw [hwp] at hb2
            obtain ⟨_, _, _, _, _, _, hpback⟩ := hb2
            obtain ⟨pw1, hpw1m, hpw1id, hpw1no, hpw1p, hpw1o, _⟩ := hpo1 u hu p hup
            exact ⟨pw1, hpw1m, hpw1id, hpw1no, hpw1p, Or.inl hpw1o, hpback⟩)⟩
  · have hm1 := (RcCtx.get?_mem hgv).1
    have hid1 := (RcCtx.get?_mem hgv).2
    have hpx : p.2 ≠ x := by
      intro heq
      obtain ⟨w, hw, hid, _, hnow, _⟩ := invalidateChildren_live_back x hm1
      rcases (RcCtx.put_mem_iff hinv.2.1).mp hw with rfl | ⟨_, hne⟩
      · rw [hnow] at hno; cases hno
      · exact hne (hid.symm.trans (hid1.trans (heq.trans hxid.symm)))
    obtain ⟨w, hwm, hid, htyw, hnow, _⟩ := hback hm1 (hid1.symm ▸ hpx)
    have hw_p : p.2 = w.id := hid1.symm.trans hid
    have hgw : rf.ctx.get? p.2 = some w := by
      rw [hw_p]; exact (RcCtx.mem_get?_iff hinv.2.1).mpr hwm
    have hsp : p ∈ rf.ctx.sharedPreds := by
      change p ∈ ctx1.sharedPreds at hp
      simp only [ctx1, RcCtx.invalidateChildren, List.mem_filter] at hp
      exact hp.1
    obtain ⟨bvu, hh, hev⟩ := hsth p hsp w hgw (hnow ▸ hno)
    exact ⟨bvu, htyw ▸ hh, hev⟩
  · intro u hu hul huex huno hupers cidx fs sc henp
    by_cases hux : u.id = x
    · obtain ⟨w, hw, hid, _, _, _, _, hew, _⟩ := invalidateChildren_live_back x hu
      rcases (RcCtx.put_mem_iff hinv.2.1).mp hw with rfl | ⟨_, hne⟩
      · rw [hew] at huex; cases huex
      · exact absurd (hid.symm.trans hux) (fun heq => hne (heq.trans hxid.symm))
    · obtain ⟨w, hwm, hid, htyw, hnow, hpw, _, hew, _, _, hlw⟩ := hback hu hux
      have henp' : rf.envP w.id = some (PVal.ctor cidx fs sc) := by rw [← hid]; exact henp
      obtain ⟨bvu, hh, hev⟩ :=
        hexcl w hwm (hlw hul) (hew ▸ huex) (hnow ▸ huno) (hpw ▸ hupers) cidx fs sc henp'
      have hh' : rf1.envH u.id = some (u.ty, Word.i64 bvu) := by
        dsimp only [rf1]; rw [hid, htyw]; exact hh
      exact ⟨bvu, hh', hev⟩
  · intro u hu hul
    by_cases hux : u.id = x
    · rw [hux, ← hxid]; exact hshd vx hxm hlx
    · obtain ⟨w, hwm, hid, _, _, _, _, _, _, _, hlw⟩ := hback hu hux
      rw [hid]; exact hshd w hwm (hlw hul)
  · refine ⟨fun v hv hvl hvns w hhv => ?_, hiso.2.1, hiso.2.2⟩
    by_cases hvx : v.id = x
    · obtain ⟨w0, hw0, hid, htyw, _⟩ := invalidateChildren_live_back x hv
      rcases (RcCtx.put_mem_iff hinv.2.1).mp hw0 with rfl | ⟨_, hne⟩
      · exact hiso.1 vx hxm hlx (htyw ▸ hvns) w
          (by change rf.envH vx.id = some (vx.ty, w); rw [hxid, ← hvx, ← htyw]; exact hhv)
      · exact absurd (hid.symm.trans hvx) (fun heq => hne (heq.trans hxid.symm))
    · obtain ⟨w0, hwm, hid, htyw, _, _, _, _, _, _, hlw⟩ := hback hv hvx
      exact hiso.1 w0 hwm (hlw hvl) (htyw ▸ hvns) w
        (by change rf.envH w0.id = some (w0.ty, w); rw [← hid, ← htyw]; exact hhv)

private theorem markScalarBranch_var_invs' {rt : BitVec 64} {rf rf0 : RcFrame} {σ σ0 : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hepres : EntryPres rf0 σ0 rf σ)
    (hsbv : SharedBoolVars rf.ctx) (hsbp : SharedBoolPreds rf.ctx) (hexcl : ExclCtorHeap rf)
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv}
    (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    {x : Nat} {vx : RcVar} (hgx : rf.ctx.get? x = some vx) (hlx : vx.isLive = true)
    {pv : PVal} (hρx : ρP x = some pv) (htag : isTaggedPVal pv = true)
    (hty : (vx.ty == .tobject || vx.ty == .tagged) = true) :
    let vx' : RcVar := { id := vx.id, ty := vx.ty, noRc := true }
    let ctx1 := (rf.ctx.put vx').invalidateChildren x
    let rf1 : RcFrame := { rf with ctx := ctx1 }
    RcInv rt rf1 σ ∧ CleanVars ctx1 ∧ ParentsOwned ctx1 ∧ NoRcCorrect ctx1 ∧
      ParentChildBacked rf1 σ.objs ∧ SharedTargetsHeap rf1 ∧ EntryPres rf0 σ0 rf1 σ ∧
      SharedBoolVars ctx1 ∧ SharedBoolPreds ctx1 ∧ ExclCtorHeap rf1 ∧
      ShadowOk sm ctx1 ρP rf1.envP ∧
      (∀ p ∈ rf.ctx.sharedPreds, p ∈ ctx1.sharedPreds ∨
        (p.2 = x ∧ ∃ v1, ctx1.get? p.2 = some v1 ∧ v1.noRc = true)) := by
  intro vx' ctx1 rf1
  have hxm := (RcCtx.get?_mem hgx).1
  have hxid := (RcCtx.get?_mem hgx).2
  have hnd1 : (ctx1.vars.map RcVar.id).Nodup := by
    have h := markScalarBranch_nodup hinv.2.1 x
    simp only [RcCtx.markScalarBranch, hgx, hty, ↓reduceIte] at h
    exact h
  have hclean1 : CleanVars ctx1 :=
    cleanVars_invalidateChildren (cleanVars_put hinv.2.1 hclean (cleanVar_markScalarBranch vx)) x
  have hpo1 : ParentsOwned ctx1 := by
    have h := parentsOwned_markScalarBranch hinv.2.1 hclean hpo x
    simp only [RcCtx.markScalarBranch, hgx, hty, ↓reduceIte] at h
    exact h
  have hnorc1 : NoRcCorrect ctx1 :=
    noRcCorrect_invalidateChildren (noRcCorrect_put hinv.2.1 hnorc fun h => by simp at h) x
  have hpcb1 : ParentChildBacked rf1 σ.objs := by
    have h := parentChildBacked_markScalarBranch (rf := rf) (σ := σ) hinv.2.1 hclean x hpcb
    simp only [RcCtx.markScalarBranch, hgx, hty, ↓reduceIte] at h
    exact h
  obtain ⟨hperm, hcount_ex⟩ := markScalarBranch_handles hinv hshd hgx hlx hρx htag hty
  obtain ⟨hvar1, hsth1, hexcl1, hshd1, hiso1⟩ :=
    markScalarBranch_var_invs hinv hclean hpo hsth hexcl hshd hgx hlx hρx htag hty hperm
  have hfh_perm : (frameHandles rf1).Perm (frameHandles rf) :=
    (hperm.append_right rf.extH).append_right rf.ghostH
  have hsp_sub : ∀ {p : Nat × Nat}, p ∈ ctx1.sharedPreds → p ∈ rf.ctx.sharedPreds := by
    intro p hp
    simp only [ctx1, RcCtx.invalidateChildren, RcCtx.put, List.mem_filter] at hp
    exact hp.1
  have hsp_keep : ∀ p ∈ rf.ctx.sharedPreds, p ∈ ctx1.sharedPreds ∨
      (p.2 = x ∧ ∃ v1, ctx1.get? p.2 = some v1 ∧ v1.noRc = true) := by
    intro p hp
    by_cases hpx : p.2 = x
    · have hm : vx' ∈ (rf.ctx.put vx').vars := (RcCtx.put_mem_iff hinv.2.1).mpr (Or.inl rfl)
      let v1 := if (vx'.parent? == some x) = true then
        { vx' with borrowed := false, parent? := none } else vx'
      have hv1m : v1 ∈ ctx1.vars := List.mem_map.mpr ⟨vx', hm, rfl⟩
      have hv1id : v1.id = p.2 := by
        dsimp only [v1]; split <;> simp [vx', hxid, hpx]
      have hv1no : v1.noRc = true := by
        dsimp only [v1]; split <;> rfl
      exact Or.inr ⟨hpx, v1, hv1id ▸ (RcCtx.mem_get?_iff hnd1).mpr hv1m, hv1no⟩
    · refine Or.inl ?_
      simp only [ctx1, RcCtx.invalidateChildren, RcCtx.put, List.mem_filter, bne_iff_ne, ne_eq]
      exact ⟨hp, hpx⟩
  have hpred1 : SharedPredInv rf1 σ.objs := by
    intro p hp vb1 vx1 hgb1 hgv1 hlb1 hno1 hpers1
    have hp0 : p ∈ rf.ctx.sharedPreds := hsp_sub hp
    have hv1m := (RcCtx.get?_mem hgv1).1
    have hv1id := (RcCtx.get?_mem hgv1).2
    obtain ⟨wv, hwv, hidv, htyv, hnowv, hpswv, hownwv, _, hrwv, _⟩ :=
      invalidateChildren_live_back x hv1m
    rcases (RcCtx.put_mem_iff hinv.2.1).mp hwv with rfl | ⟨hwvm, hne⟩
    · rw [hnowv] at hno1; cases hno1
    · have hp2ne : p.2 ≠ x := fun heq => hne (hidv.symm.trans (hv1id.trans (heq.trans hxid.symm)))
      have hwv_id : p.2 = wv.id := hv1id.symm.trans hidv
      have hgv0 : rf.ctx.get? p.2 = some wv := by
        rw [hwv_id]; exact (RcCtx.mem_get?_iff hinv.2.1).mpr hwvm
      have hc_eq : ∀ a, List.count a (localHandlesExcept ctx1 rf.envH p.2) =
          List.count a (localHandlesExcept rf.ctx rf.envH p.2) :=
        hcount_ex p.2 hp2ne vx1 hv1m hv1id wv hwvm (hidv.symm.trans hv1id)
          hnowv hpswv hownwv hrwv
      have hb1m := (RcCtx.get?_mem hgb1).1
      have hb1id := (RcCtx.get?_mem hgb1).2
      obtain ⟨wb, hwb, hidb, _, hnob, hpsb, hownb, _, hrb, hbrb⟩ :=
        invalidateChildren_live_back x hb1m
      rcases (RcCtx.put_mem_iff hinv.2.1).mp hwb with rfl | ⟨hwbm, _⟩
      · have hp1x : p.1 = x := hb1id.symm.trans (hidb.trans hxid)
        have hgb0 : rf.ctx.get? p.1 = some vx := by rw [hp1x]; exact hgx
        have hlb0 : vx.isLive = true := hlx
        obtain ⟨h0, h1⟩ :=
          hinv.2.2.2.2 p hp0 vx wv hgb0 hgv0 hlb0 (hnowv ▸ hno1) (hpswv ▸ hpers1)
        refine ⟨fun he0 => ?_, fun he1 ho1 => ?_⟩
        · obtain ⟨bv, hh, hev, hfn⟩ := h0 he0
          refine ⟨bv, htyv ▸ hh, hev, fun ho1 => ?_⟩
          obtain ⟨hz, ho⟩ := hfn (hownwv ▸ ho1)
          simp only [List.count_append] at hz ⊢
          rw [hc_eq bv]
          exact ⟨hz, by obtain ⟨o, hom, hoa, horc⟩ := ho; exact ⟨o, hom, hoa, hownwv ▸ horc⟩⟩
        · obtain ⟨bv, hh, hev, o, hom, hoa, horc⟩ := h1 he1 (hownwv ▸ ho1)
          exact ⟨bv, htyv ▸ hh, hev, o, hom, hoa, hownwv ▸ horc⟩
      · have hwb_id : p.1 = wb.id := hb1id.symm.trans hidb
        have hgb0 : rf.ctx.get? p.1 = some wb := by
          rw [hwb_id]; exact (RcCtx.mem_get?_iff hinv.2.1).mpr hwbm
        have hlb0 : wb.isLive = true := by
          unfold RcVar.isLive at hlb1 ⊢
          rw [hnob, hpsb, hownb, hrb] at hlb1
          simp only [Bool.or_eq_true] at hlb1 ⊢
          rcases hlb1 with (((ha | hb) | hc) | hd) | he
          · simp [ha]
          · simp [hb]
          · simp [hc]
          · simp [(hbrb hd).1]
          · simp [he]
        obtain ⟨h0, h1⟩ :=
          hinv.2.2.2.2 p hp0 wb wv hgb0 hgv0 hlb0 (hnowv ▸ hno1) (hpswv ▸ hpers1)
        refine ⟨fun he0 => ?_, fun he1 ho1 => ?_⟩
        · obtain ⟨bv, hh, hev, hfn⟩ := h0 he0
          refine ⟨bv, htyv ▸ hh, hev, fun ho1 => ?_⟩
          obtain ⟨hz, ho⟩ := hfn (hownwv ▸ ho1)
          simp only [List.count_append] at hz ⊢
          rw [hc_eq bv]
          exact ⟨hz, by obtain ⟨o, hom, hoa, horc⟩ := ho; exact ⟨o, hom, hoa, hownwv ▸ horc⟩⟩
        · obtain ⟨bv, hh, hev, o, hom, hoa, horc⟩ := h1 he1 (hownwv ▸ ho1)
          exact ⟨bv, htyv ▸ hh, hev, o, hom, hoa, hownwv ▸ horc⟩
  have hsbv1 : SharedBoolVars ctx1 := by
    intro p hp vb hgb
    have hp0 : p ∈ rf.ctx.sharedPreds := hsp_sub hp
    obtain ⟨w, hw, hid, _, hno, _⟩ := invalidateChildren_live_back x (RcCtx.get?_mem hgb).1
    rcases (RcCtx.put_mem_iff hinv.2.1).mp hw with rfl | ⟨hwm, _⟩
    · exact hno
    · have hbw_id : p.1 = w.id := (RcCtx.get?_mem hgb).2.symm.trans hid
      have hgw : rf.ctx.get? p.1 = some w := by
        rw [hbw_id]; exact (RcCtx.mem_get?_iff hinv.2.1).mpr hwm
      exact hno ▸ hsbv p hp0 w hgw
  have hsbp1 : SharedBoolPreds ctx1 := by
    intro p hp
    have hp0 : p ∈ rf.ctx.sharedPreds := hsp_sub hp
    obtain ⟨vb0, hgb0, hno0⟩ := hsbp p hp0
    by_cases hp1x : p.1 = x
    · have hm : vx' ∈ (rf.ctx.put vx').vars := (RcCtx.put_mem_iff hinv.2.1).mpr (Or.inl rfl)
      let vb1 := if (vx'.parent? == some x) = true then
        { vx' with borrowed := false, parent? := none } else vx'
      have hbm : vb1 ∈ ctx1.vars := List.mem_map.mpr ⟨vx', hm, rfl⟩
      have hbid : vb1.id = p.1 := by simp [vb1, vx', hxid, hp1x]
      have hbno : vb1.noRc = true := by simp [vb1, vx']
      exact ⟨vb1, hbid ▸ (RcCtx.mem_get?_iff hnd1).mpr hbm, hbno⟩
    · have hvbm := (RcCtx.get?_mem hgb0).1
      have hvbid := (RcCtx.get?_mem hgb0).2
      have hm : vb0 ∈ (rf.ctx.put vx').vars := (RcCtx.put_mem_iff hinv.2.1).mpr (Or.inr
        ⟨hvbm, fun heq => hp1x (hvbid.symm.trans (heq.trans hxid))⟩)
      let vb1 := if (vb0.parent? == some x) = true then
        { vb0 with borrowed := false, parent? := none } else vb0
      have hbm : vb1 ∈ ctx1.vars := List.mem_map.mpr ⟨vb0, hm, rfl⟩
      have hbid : vb1.id = p.1 := by
        by_cases hpx : (vb0.parent? == some x) = true <;> simp [vb1, hpx, hvbid]
      have hbno : vb1.noRc = true := by
        by_cases hpx : (vb0.parent? == some x) = true <;> simp [vb1, hpx, hno0]
      exact ⟨vb1, hbid ▸ (RcCtx.mem_get?_iff hnd1).mpr hbm, hbno⟩
  have hrc1 : RcInv rt rf1 σ :=
    ⟨hinv.1, hnd1, handlesRcSound_of_perm hfh_perm.symm hinv.2.2.1, hvar1, hpred1⟩
  have hepres1 : EntryPres rf0 σ0 rf1 σ :=
    ⟨hepres.1, fun a ha hiso => ⟨hiso1 a (hepres.2.1 a ha hiso).1, (hepres.2.1 a ha hiso).2⟩,
      hepres.2.2⟩
  exact ⟨hrc1, hclean1, hpo1, hnorc1, hpcb1, hsth1, hepres1, hsbv1, hsbp1, hexcl1, hshd1, hsp_keep⟩

private theorem markScalarBranch_invs {rt : BitVec 64} {rf rf0 : RcFrame} {σ σ0 : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hepres : EntryPres rf0 σ0 rf σ)
    (hsbv : SharedBoolVars rf.ctx) (hsbp : SharedBoolPreds rf.ctx) (hexcl : ExclCtorHeap rf)
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv}
    (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    {x : Nat} {vx : RcVar} (hgx : rf.ctx.get? x = some vx) (hlx : vx.isLive = true)
    {pv : PVal} (hρx : ρP x = some pv) (htag : isTaggedPVal pv = true) :
    let ctx1 := rf.ctx.markScalarBranch x
    let rf1 : RcFrame := { rf with ctx := ctx1 }
    RcInv rt rf1 σ ∧ CleanVars ctx1 ∧ ParentsOwned ctx1 ∧ NoRcCorrect ctx1 ∧
      ParentChildBacked rf1 σ.objs ∧ SharedTargetsHeap rf1 ∧ EntryPres rf0 σ0 rf1 σ ∧
      SharedBoolVars ctx1 ∧ SharedBoolPreds ctx1 ∧ ExclCtorHeap rf1 ∧
      ShadowOk sm ctx1 ρP rf1.envP ∧
      (∀ p ∈ rf.ctx.sharedPreds, p ∈ ctx1.sharedPreds ∨
        (p.2 = x ∧ ∃ v1, ctx1.get? p.2 = some v1 ∧ v1.noRc = true)) := by
  intro ctx1 rf1
  by_cases hty : (vx.ty == .tobject || vx.ty == .tagged) = true
  · have hsub : ctx1 =
        (rf.ctx.put { id := vx.id, ty := vx.ty, noRc := true }).invalidateChildren x := by
      simp [ctx1, RcCtx.markScalarBranch, hgx, hty]
    simpa only [rf1, hsub] using
      markScalarBranch_var_invs' hinv hclean hpo hnorc hpcb hsth hepres hsbv hsbp hexcl hshd
        hgx hlx hρx htag hty
  · have hsub : ctx1 = rf.ctx := by simp [ctx1, RcCtx.markScalarBranch, hgx, hty]
    have hrf_eq : rf1 = rf := by cases rf; simp [rf1, hsub]
    rw [hrf_eq, hsub]
    exact ⟨hinv, hclean, hpo, hnorc, hpcb, hsth, hepres, hsbv, hsbp, hexcl, hshd,
      fun p hp => Or.inl hp⟩

private theorem markExcl_varHandles_perm {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (envH : HValEnv) {vt : RcVar} (hgt : ctx.get? vt.id = some vt) :
    let vt' := { vt with excl := true }
    (localHandles (ctx.put vt') envH).Perm (localHandles ctx envH) ∧
      ∀ (s : Nat) (a : BitVec 64),
        List.count a (localHandlesExcept (ctx.put vt') envH s) =
          List.count a (localHandlesExcept ctx envH s) := by
  intro vt'
  have hvh : varHandles envH vt' = varHandles envH vt := rfl
  have hperm : (localHandles (ctx.put vt') envH).Perm (localHandles ctx envH) := by
    have h1 := localHandles_put_perm hnd envH vt'
    have h2 := localHandles_perm_filter hnd envH vt (RcCtx.get?_mem hgt).1
    rw [hvh] at h1
    exact h1.trans h2.symm
  have hnd1 := ctx.put_nodup hnd vt'
  refine ⟨hperm, fun s a => ?_⟩
  by_cases hst : s = vt.id
  · subst hst
    have h1 := (localHandles_perm_filter hnd1 envH vt'
      ((RcCtx.put_mem_iff hnd).mpr (Or.inl rfl))).count_eq a
    have h2 := (localHandles_perm_filter hnd envH vt (RcCtx.get?_mem hgt).1).count_eq a
    have hpc := hperm.count_eq a
    have hvtid : vt'.id = vt.id := rfl
    rw [hvh, hvtid] at h1
    simp only [List.count_append] at h1 h2
    exact Nat.add_left_cancel (h1.symm.trans (hpc.trans h2))
  · cases hg' : (ctx.put vt').get? s with
    | none =>
      have hpc := hperm.count_eq a
      have hm1 : ∀ u ∈ (ctx.put vt').vars, u.id ≠ s := fun u hu heq => by
        have hmem := (RcCtx.mem_get?_iff hnd1).mpr hu
        rw [heq, hg'] at hmem; cases hmem
      have hm0 : ∀ w ∈ ctx.vars, w.id ≠ s := fun w hw heq => by
        have hw' : w ∈ (ctx.put vt').vars := (RcCtx.put_mem_iff hnd).mpr (Or.inr
          ⟨hw, fun heq2 => hst (heq.symm.trans heq2)⟩)
        exact hm1 w hw' heq
      have hf1 : (ctx.put vt').vars.filter (fun v => v.id != s) = (ctx.put vt').vars :=
        List.filter_eq_self.mpr fun v hv => by simp [hm1 v hv]
      have hf0 : ctx.vars.filter (fun v => v.id != s) = ctx.vars :=
        List.filter_eq_self.mpr fun v hv => by simp [hm0 v hv]
      change List.count a ((List.map (varHandles envH) _).flatten) =
        List.count a ((List.map (varHandles envH) _).flatten)
      rw [hf1, hf0]
      exact hpc
    | some u' =>
      have hum := (RcCtx.get?_mem hg').1
      have huid := (RcCtx.get?_mem hg').2
      rcases (RcCtx.put_mem_iff hnd).mp hum with rfl | ⟨hwm, _⟩
      · exact absurd huid (fun heq => hst heq.symm)
      · have h1 := (localHandles_perm_filter hnd1 envH u' hum).count_eq a
        have h2 := (localHandles_perm_filter hnd envH u' hwm).count_eq a
        have hpc := hperm.count_eq a
        simp only [List.count_append, huid] at h1 h2
        omega

private theorem markExcl_invs {rt : BitVec 64} {rf rf0 : RcFrame} {σ σ0 : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hepres : EntryPres rf0 σ0 rf σ)
    (hsbv : SharedBoolVars rf.ctx) (hsbp : SharedBoolPreds rf.ctx) (hexcl : ExclCtorHeap rf)
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv}
    (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    {scru tgt : Nat} (hp_mem : (scru, tgt) ∈ rf.ctx.sharedPreds)
    (hρ0 : (ρP scru).bind PVal.tag? = some 0) :
    let ctx' := rf.ctx.markExcl tgt
    let rf' : RcFrame := { rf with ctx := ctx' }
    RcInv rt rf' σ ∧ CleanVars ctx' ∧ ParentsOwned ctx' ∧ NoRcCorrect ctx' ∧
      ParentChildBacked rf' σ.objs ∧ SharedTargetsHeap rf' ∧ EntryPres rf0 σ0 rf' σ ∧
      SharedBoolVars ctx' ∧ SharedBoolPreds ctx' ∧ ExclCtorHeap rf' ∧
      ShadowOk sm ctx' ρP rf'.envP := by
  intro ctx' rf'
  cases hgt : rf.ctx.get? tgt with
  | none =>
    have hsub : ctx' = rf.ctx := by simp [ctx', RcCtx.markExcl, hgt]
    have hrf_eq : rf' = rf := by cases rf; simp [rf', hsub]
    rw [hrf_eq, hsub]
    exact ⟨hinv, hclean, hpo, hnorc, hpcb, hsth, hepres, hsbv, hsbp, hexcl, hshd⟩
  | some vt =>
    by_cases hcond : (!vt.noRc && !vt.persistent && vt.owned == 1) = true
    · have hsub : ctx' = rf.ctx.put { vt with excl := true } := by
        simp [ctx', RcCtx.markExcl, hgt, hcond]
      let vt' : RcVar := { vt with excl := true }
      have htm := (RcCtx.get?_mem hgt).1
      have htid := (RcCtx.get?_mem hgt).2
      have hvt_no : vt.noRc = false := by cases h : vt.noRc <;> simp_all
      have hvt_pers : vt.persistent = false := by cases h : vt.persistent <;> simp_all
      have hvt_own : vt.owned = 1 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond; exact hcond.2
      obtain ⟨vb, hgb, hvb_no⟩ := hsbp (scru, tgt) hp_mem
      have hgb' : rf.ctx.get? scru = some vb := hgb
      have hlb : vb.isLive = true := by unfold RcVar.isLive; simp [hvb_no]
      have henv0 : (rf.envP scru).bind PVal.tag? = some 0 := by
        rw [← hρ0, ← (RcCtx.get?_mem hgb').2]
        exact (shadow_tag?_eq hshd (RcCtx.get?_mem hgb').1 hlb).symm
      have hbr_f := not_borrowed_of_sharedZero hinv hclean hpo hnorc hp_mem hgb' hgt hlb
        hvt_no hvt_pers (by omega) henv0
      have hsp_res := (hinv.2.2.2.2 (scru, tgt) hp_mem vb vt hgb' hgt hlb hvt_no hvt_pers).1 henv0
      obtain ⟨bv_t, hht_t, hev_t, hzero_fn⟩ := hsp_res
      have hht_t' : rf.envH tgt = some (vt.ty, Word.i64 bv_t) := hht_t
      obtain ⟨_, o_t, ho_t, hoa_t, horc_t⟩ := hzero_fn (by omega)
      have horc1 : o_t.rc = 1#32 := by
        apply BitVec.eq_of_toNat_eq
        simp [horc_t, hvt_own]
      have hnd' := rf.ctx.put_nodup hinv.2.1 vt'
      obtain ⟨hperm_lh, hcount_ex⟩ :=
        markExcl_varHandles_perm hinv.2.1 rf.envH (htid ▸ hgt : rf.ctx.get? vt.id = some vt)
      have hperm_ctx' : (localHandles ctx' rf.envH).Perm (localHandles rf.ctx rf.envH) := by
        rw [hsub]; exact hperm_lh
      have hfh_perm : (frameHandles rf').Perm (frameHandles rf) :=
        (hperm_ctx'.append_right rf.extH).append_right rf.ghostH
      have hcv_vt' : CleanVar vt' := by
        have hcv := hclean vt htm
        exact ⟨⟨(fun h => by rw [hvt_no] at h; cases h), hcv.1.2⟩,
          (fun h => by rw [hvt_pers] at h; cases h),
          (fun h => by rw [hbr_f] at h; cases h), hcv.2.2.2.1, hcv.2.2.2.2⟩
      have hclean' : CleanVars ctx' := hsub ▸ cleanVars_put hinv.2.1 hclean hcv_vt'
      have hpo' : ParentsOwned ctx' := by
        have h := parentsOwned_markExcl hinv.2.1 hclean hpo tgt
        change ParentsOwned (rf.ctx.markExcl tgt) at h
        exact h
      have hnorc' : NoRcCorrect ctx' := hsub ▸ noRcCorrect_put hinv.2.1 hnorc
        (fun h => hnorc vt htm h)
      have hpcb' : ParentChildBacked rf' σ.objs := by
        have h := parentChildBacked_markExcl (rf := rf) (σ := σ) hinv.2.1 tgt hpcb
        exact h
      have hvar' : ∀ u ∈ ctx'.vars, VarInv u rf' σ.objs := by
        intro u hu hul
        rw [hsub] at hu
        rcases (RcCtx.put_mem_iff hinv.2.1).mp hu with rfl | ⟨hum, hne⟩
        · obtain ⟨pu, wu, hp, hh, hrep, hnon⟩ := hinv.2.2.2.1 vt htm hul
          refine ⟨pu, wu, hp, hh, hrep, fun hns => ?_⟩
          obtain ⟨bvu, hwbv, _, hpers, _, _⟩ := hnon hns
          refine ⟨bvu, hwbv, (fun h => by rw [hvt_no] at h; cases h), hpers,
            (fun _ => ⟨hvt_no, hvt_pers, hvt_own, fun _ => by
              have hbv_eq : bvu = bv_t := by
                rw [htid, hht_t', hwbv] at hh; cases hh; rfl
              subst hbv_eq; exact ⟨o_t, ho_t, hoa_t, horc1⟩⟩),
            (fun _ _ hb => by rw [hbr_f] at hb; cases hb)⟩
        · obtain ⟨pu, wu, hp, hh, hrep, hnon⟩ := hinv.2.2.2.1 u hum hul
          refine ⟨pu, wu, hp, hh, hrep, fun hns => ?_⟩
          obtain ⟨bvu, hwbv, hno, hpers, hex, hbor⟩ := hnon hns
          refine ⟨bvu, hwbv, hno, hpers, hex, fun huno hups hubr hev => ?_⟩
          obtain ⟨hb1, hb2⟩ := hbor huno hups hubr hev
          refine ⟨backed_of_perm hfh_perm.symm hb1, ?_⟩
          cases hup : u.parent? with
          | none => rw [hup] at hb2; exact hb2
          | some p =>
            rw [hup] at hb2
            obtain ⟨_, _, _, _, _, _, hpback⟩ := hb2
            have hu' : u ∈ ctx'.vars := by rw [hsub]; exact hu
            obtain ⟨pw', hpw'm, hpw'id, hpw'no, hpw'p, hpw'o, _⟩ := hpo' u hu' p hup
            exact ⟨pw', hpw'm, hpw'id, hpw'no, hpw'p, Or.inl hpw'o, hpback⟩
      have hpred' : SharedPredInv rf' σ.objs := by
        intro p hp vb1 vx1 hgb1 hgv1 hlb1 hno1 hpers1
        change p ∈ ctx'.sharedPreds at hp
        have hp0 : p ∈ rf.ctx.sharedPreds := by rw [hsub] at hp; exact hp
        have hget_back : ∀ {z : Nat} {v' : RcVar}, ctx'.get? z = some v' →
            ∃ v0, rf.ctx.get? z = some v0 ∧ v'.id = v0.id ∧ v'.ty = v0.ty ∧
              v'.noRc = v0.noRc ∧ v'.persistent = v0.persistent ∧ v'.owned = v0.owned ∧
              v'.isLive = v0.isLive := by
          intro z v' hgz
          have hv'm := (RcCtx.get?_mem hgz).1
          have hv'id := (RcCtx.get?_mem hgz).2
          rw [hsub] at hv'm
          rcases (RcCtx.put_mem_iff hinv.2.1).mp hv'm with rfl | ⟨hwm, _⟩
          · refine ⟨vt, hv'id ▸ htid ▸ hgt, rfl, rfl, rfl, rfl, rfl, ?_⟩
            unfold RcVar.isLive; simp
          · refine ⟨v', hv'id ▸ (RcCtx.mem_get?_iff hinv.2.1).mpr hwm,
              rfl, rfl, rfl, rfl, rfl, rfl⟩
        obtain ⟨vb0, hgb0, _, _, _, _, _, hlb0⟩ := hget_back hgb1
        obtain ⟨vx0, hgv0, _, htyv, hnov, hpsv, hownv, _⟩ := hget_back hgv1
        obtain ⟨h0, h1⟩ :=
          hinv.2.2.2.2 p hp0 vb0 vx0 hgb0 hgv0 (hlb0 ▸ hlb1) (hnov ▸ hno1) (hpsv ▸ hpers1)
        refine ⟨fun he0 => ?_, fun he1 ho1 => ?_⟩
        · obtain ⟨bv, hh, hev, hfn⟩ := h0 he0
          refine ⟨bv, htyv ▸ hh, hev, fun ho1 => ?_⟩
          obtain ⟨hz, ho⟩ := hfn (hownv ▸ ho1)
          simp only [List.count_append] at hz ⊢
          change nonPersistRefs σ.objs bv + (List.count bv (localHandlesExcept ctx' rf.envH p.2) +
            List.count bv rf.extH + List.count bv rf.ghostH) = 0 ∧ _
          rw [hsub, hcount_ex p.2 bv]
          exact ⟨hz, by obtain ⟨o, hom, hoa, horc⟩ := ho; exact ⟨o, hom, hoa, hownv ▸ horc⟩⟩
        · obtain ⟨bv, hh, hev, o, hom, hoa, horc⟩ := h1 he1 (hownv ▸ ho1)
          exact ⟨bv, htyv ▸ hh, hev, o, hom, hoa, hownv ▸ horc⟩
      have hnd_ctx' : (ctx'.vars.map RcVar.id).Nodup := by rw [hsub]; exact hnd'
      have hrc' : RcInv rt rf' σ :=
        ⟨hinv.1, hnd_ctx', handlesRcSound_of_perm hfh_perm.symm hinv.2.2.1, hvar', hpred'⟩
      have hsth' : SharedTargetsHeap rf' := by
        intro p hp vx1 hgv hno
        change p ∈ ctx'.sharedPreds at hp
        have hp0 : p ∈ rf.ctx.sharedPreds := by rw [hsub] at hp; exact hp
        have hv1m := (RcCtx.get?_mem hgv).1
        have hv1id := (RcCtx.get?_mem hgv).2
        change vx1 ∈ ctx'.vars at hv1m
        rw [hsub] at hv1m
        rcases (RcCtx.put_mem_iff hinv.2.1).mp hv1m with rfl | ⟨hwm, _⟩
        · exact hsth p hp0 vt (hv1id ▸ htid ▸ hgt) hno
        · exact hsth p hp0 vx1 (hv1id ▸ (RcCtx.mem_get?_iff hinv.2.1).mpr hwm) hno
      have hepres' : EntryPres rf0 σ0 rf' σ := by
        refine ⟨hepres.1, fun a ha hiso => ?_, hepres.2.2⟩
        obtain ⟨hiso_v, hiso_r, hiso_o⟩ := (hepres.2.1 a ha hiso).1
        refine ⟨⟨fun v hv hvl hvns w hhw => ?_, hiso_r, hiso_o⟩, (hepres.2.1 a ha hiso).2⟩
        change v ∈ ctx'.vars at hv
        rw [hsub] at hv
        rcases (RcCtx.put_mem_iff hinv.2.1).mp hv with rfl | ⟨hwm, _⟩
        · exact hiso_v vt htm (by change vt.isLive = true; exact hvl) hvns w hhw
        · exact hiso_v v hwm hvl hvns w hhw
      have hsbv' : SharedBoolVars ctx' := by
        intro p hp vb1 hgb
        have hp0 : p ∈ rf.ctx.sharedPreds := by rw [hsub] at hp; exact hp
        have hbm := (RcCtx.get?_mem hgb).1
        have hbid := (RcCtx.get?_mem hgb).2
        rw [hsub] at hbm
        rcases (RcCtx.put_mem_iff hinv.2.1).mp hbm with rfl | ⟨hwm, _⟩
        · exact hsbv p hp0 vt (hbid ▸ htid ▸ hgt)
        · exact hsbv p hp0 vb1 (hbid ▸ (RcCtx.mem_get?_iff hinv.2.1).mpr hwm)
      have hsbp' : SharedBoolPreds ctx' := by
        intro p hp
        have hp0 : p ∈ rf.ctx.sharedPreds := by rw [hsub] at hp; exact hp
        obtain ⟨vb0, hgb0, hno0⟩ := hsbp p hp0
        by_cases hp1t : p.1 = vt.id
        · have hvt_eq : vb0 = vt := by
            rw [hp1t, htid] at hgb0; rw [hgt] at hgb0; cases hgb0; rfl
          have hm : vt' ∈ ctx'.vars := by
            rw [hsub]; exact (RcCtx.put_mem_iff hinv.2.1).mpr (Or.inl rfl)
          have hno_vt' : vt'.noRc = true := by
            change vt.noRc = true; rw [← hvt_eq]; exact hno0
          exact ⟨vt', hp1t ▸ (RcCtx.mem_get?_iff hnd_ctx').mpr hm, hno_vt'⟩
        · have hm : vb0 ∈ ctx'.vars := by
            rw [hsub]; exact (RcCtx.put_mem_iff hinv.2.1).mpr (Or.inr
              ⟨(RcCtx.get?_mem hgb0).1,
                fun heq => hp1t ((RcCtx.get?_mem hgb0).2.symm.trans heq)⟩)
          exact ⟨vb0, (RcCtx.get?_mem hgb0).2 ▸ (RcCtx.mem_get?_iff hnd_ctx').mpr hm, hno0⟩
      have hexcl' : ExclCtorHeap rf' := by
        intro u hu hul huex huno hupers cidx fs sc henp
        change u ∈ ctx'.vars at hu
        rw [hsub] at hu
        rcases (RcCtx.put_mem_iff hinv.2.1).mp hu with rfl | ⟨hwm, _⟩
        · exact ⟨bv_t, htid ▸ hht_t', hev_t⟩
        · exact hexcl u hwm hul huex huno hupers cidx fs sc henp
      have hshd' : ShadowOk sm ctx' ρP rf'.envP := by
        intro u hu hul
        rw [hsub] at hu
        rcases (RcCtx.put_mem_iff hinv.2.1).mp hu with rfl | ⟨hwm, _⟩
        · exact hshd vt htm (by change vt.isLive = true; exact hul)
        · exact hshd u hwm hul
      exact ⟨hrc', hclean', hpo', hnorc', hpcb', hsth', hepres', hsbv', hsbp', hexcl', hshd'⟩
    · have hsub : ctx' = rf.ctx := by simp [ctx', RcCtx.markExcl, hgt, hcond]
      have hrf_eq : rf' = rf := by cases rf; simp [rf', hsub]
      rw [hrf_eq, hsub]
      exact ⟨hinv, hclean, hpo, hnorc, hpcb, hsth, hepres, hsbv, hsbp, hexcl, hshd⟩

private theorem find_sharedPreds_some {x tgt : Nat} {ps : List (Nat × Nat)}
    (h : Option.map Prod.snd (List.find? (fun p => p.fst == x) ps) = some tgt) :
    (x, tgt) ∈ ps := by
  cases hf : List.find? (fun p => p.fst == x) ps with
  | none => simp [hf] at h
  | some p =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    have hm := List.mem_of_find?_eq_some hf
    have hb : (p.fst == x) = true :=
      @List.find?_some (Nat × Nat) (fun q => q.fst == x) p ps hf
    rcases p with ⟨a, b⟩
    simp only [beq_iff_eq] at hb
    simp only at h
    subst hb h
    exact hm

/-- Exact checker/Perceus branch context for alternative pattern `pat` in `cases x alts`. -/
@[expose] public def casesBranchCtx (env : RcModEnv) (target? : Option Nat) (pat : LcPat) (x : Nat)
    (ctx : RcCtx) : RcCtx :=
  let ctx1 := match pat with
    | .ctor _ cname =>
      if env.scalarCtors.contains cname then ctx.markScalarBranch x else ctx
    | .dflt => ctx
  match pat with
  | .ctor 0 _ =>
    match target? with
    | some tgt => ctx1.markExcl tgt
    | none => ctx1
  | _ => ctx1

private theorem dflt_alts_sim {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {J : HJEnv} {Jp : PResJEnv} {Qh : HPost} {Xh : HXPost}
    {Qp : PResPost} {Xp : PResXPost} {jps : List RcJpInfo} {rf : RcFrame} {σ : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr x : Nat}
    {scruTy : LcTy} {target? : Option Nat} {alts alts' : List (LcPat × LcCode)}
    (hmem : ∀ p b, (p, b) ∈ alts' → (p, b) ∈ alts)
    (hwf : perceusAltsWf env retTy jps rf.ctx sm x scruTy target? alts' = true)
    (hpr : PRWpDfltAlts m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Qp Xp alts')
    (hbody : ∀ {b : LcCode}, (LcPat.dflt, b) ∈ alts →
      perceusCodeWf env retTy jps rf.ctx sm b = true →
      PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Qp Xp b →
      HWp Δh rt retTy J rf.envH Qh Xh b σ) :
    HWpDfltAlts Δh rt retTy J rf.envH Qh Xh alts' σ := by
  induction alts' with
  | nil =>
    rw [PRWpDfltAlts.eq_1] at hpr
    exact False.elim hpr
  | cons a rest ih =>
    rcases a with ⟨pat, b⟩
    cases pat with
    | dflt =>
      rw [HWpDfltAlts.eq_2]
      rw [PRWpDfltAlts.eq_2] at hpr
      have hne : ∀ (tgt : Nat) (name : String),
          target? = some tgt → LcPat.dflt = LcPat.ctor 0 name → False := by
        intro _ _ _ h; cases h
      rw [perceusAltsWf.eq_4 env retTy jps rf.ctx sm x scruTy b rest target? hne] at hwf
      simp only [Bool.true_and, Bool.and_eq_true] at hwf
      exact hbody (hmem _ _ List.mem_cons_self) hwf.1 hpr
    | ctor ci cname =>
      rw [HWpDfltAlts.eq_3]
      rw [PRWpDfltAlts.eq_3] at hpr
      have hrest_wf : perceusAltsWf env retTy jps rf.ctx sm x scruTy target? rest = true := by
        cases htg : target? with
        | none =>
          rw [htg] at hwf
          have hne : ∀ (tgt : Nat) (name : String),
              none = some tgt → LcPat.ctor ci cname = LcPat.ctor 0 name → False := by
            intro _ _ h; cases h
          rw [perceusAltsWf.eq_3 env retTy jps rf.ctx sm x scruTy b rest
            ci cname none hne] at hwf
          simp only [Bool.and_eq_true] at hwf; exact hwf.2
        | some tgt =>
          by_cases h0 : ci = 0
          · subst h0; rw [htg] at hwf
            rw [perceusAltsWf.eq_2 env retTy jps rf.ctx sm x scruTy b rest
              0 cname tgt cname rfl] at hwf
            simp only [Bool.and_eq_true] at hwf; exact hwf.2
          · rw [htg] at hwf
            have hne : ∀ (tgt' : Nat) (name : String),
                some tgt = some tgt' → LcPat.ctor ci cname = LcPat.ctor 0 name → False := by
              intro _ _ _ hc; cases hc; exact h0 rfl
            rw [perceusAltsWf.eq_3 env retTy jps rf.ctx sm x scruTy b rest
              ci cname (some tgt) hne] at hwf
            simp only [Bool.and_eq_true] at hwf; exact hwf.2
      exact ih (fun p b' hm => hmem p b' (List.mem_cons_of_mem _ hm)) hrest_wf hpr

private theorem ctor_alts_sim {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {J : HJEnv} {Jp : PResJEnv} {Qh : HPost} {Xh : HXPost}
    {Qp : PResPost} {Xp : PResXPost} {jps : List RcJpInfo} {rf rf0 : RcFrame} {σ σ0 : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr x tag : Nat}
    {vx : RcVar} {pv : PVal} {target? : Option Nat} {alts alts' : List (LcPat × LcCode)}
    (hgx : rf.ctx.get? x = some vx) (hlx : vx.isLive = true)
    (hρx : ρP x = some pv) (hptag : (ρP x).bind PVal.tag? = some tag)
    (htgt : ∀ tgt, target? = some tgt → (x, tgt) ∈ rf.ctx.sharedPreds)
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx)
    (hsbp : SharedBoolPreds rf.ctx) (hexcl : ExclCtorHeap rf) (hsw : ShadowSmWf sm)
    (hshd : ShadowOk sm rf.ctx ρP rf.envP) (hrs : ResStateInv σ rem wr rcr)
    (hmem : ∀ p b, (p, b) ∈ alts' → (p, b) ∈ alts)
    (hwf : perceusAltsWf env retTy jps rf.ctx sm x vx.ty target? alts' = true)
    (hpr_dflt : PRWpDfltAlts m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Qp Xp alts →
      HWpDfltAlts Δh rt retTy J rf.envH Qh Xh alts σ)
    (hpr : PRWpCtorAlts m env retTy Δr jps rf.ctx x target? pv Jp ρP tag rem wr rcr Qp Xp alts'
      (PRWpDfltAlts m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Qp Xp alts))
    (hbody : ∀ {b : LcCode}, (∃ pat, (pat, b) ∈ alts) →
      ∀ (ctx' : RcCtx), let rf' : RcFrame := { rf with ctx := ctx' }
      (∃ pat, (pat, b) ∈ alts ∧ ctx' = casesBranchCtx env target? pat x rf.ctx) →
      perceusCodeWf env retTy jps ctx' sm b = true →
      PRWp m env retTy Δr jps ctx' Jp ρP rem wr rcr Qp Xp b →
      RcInv rt rf' σ → CleanVars ctx' → ParentsOwned ctx' → NoRcCorrect ctx' →
      ParentChildBacked rf' σ.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ.objs → EntryPres rf0 σ0 rf' σ →
      SharedBoolVars ctx' → SharedBoolPreds ctx' → ExclCtorHeap rf' →
      ShadowSmWf sm → ShadowOk sm ctx' ρP rf'.envP → ResStateInv σ rem wr rcr →
      HWp Δh rt retTy J rf.envH Qh Xh b σ) :
    HWpCtorAlts Δh rt retTy J rf.envH Qh Xh tag alts'
      (HWpDfltAlts Δh rt retTy J rf.envH Qh Xh alts) σ := by
  cases target? with
  | some tgt =>
    have hsp_tgt : (x, tgt) ∈ rf.ctx.sharedPreds := htgt tgt rfl
    induction alts' with
    | nil =>
      rw [HWpCtorAlts.eq_1]
      rw [PRWpCtorAlts.eq_1] at hpr
      exact hpr_dflt hpr
    | cons a rest ih =>
      rcases a with ⟨pat, b⟩
      cases pat with
      | dflt =>
        rw [HWpCtorAlts.eq_3]
        rw [PRWpCtorAlts.eq_4] at hpr
        have hne : ∀ (tgt' : Nat) (name : String),
            some tgt = some tgt' → LcPat.dflt = LcPat.ctor 0 name → False := by
          intro _ _ _ h; cases h
        rw [perceusAltsWf.eq_4 env retTy jps rf.ctx sm x vx.ty b rest (some tgt) hne] at hwf
        simp only [Bool.true_and, Bool.and_eq_true] at hwf
        exact ih (fun p b' hm => hmem p b' (List.mem_cons_of_mem _ hm)) hwf.2 hpr
      | ctor ci cname =>
        rw [HWpCtorAlts.eq_2]
        have hstep_ctx1 : ∀
            (htag_if : env.scalarCtors.contains cname = true → isTaggedPVal pv = true),
            let ctx1 :=
              if env.scalarCtors.contains cname = true then rf.ctx.markScalarBranch x else rf.ctx
            let rf1 : RcFrame := { rf with ctx := ctx1 }
            RcInv rt rf1 σ ∧ CleanVars ctx1 ∧ ParentsOwned ctx1 ∧ NoRcCorrect ctx1 ∧
              ParentChildBacked rf1 σ.objs ∧ SharedTargetsHeap rf1 ∧ EntryPres rf0 σ0 rf1 σ ∧
              SharedBoolVars ctx1 ∧ SharedBoolPreds ctx1 ∧ ExclCtorHeap rf1 ∧
              ShadowOk sm ctx1 ρP rf1.envP ∧
              (∀ p ∈ rf.ctx.sharedPreds, p ∈ ctx1.sharedPreds ∨
                (p.2 = x ∧ ∃ v1, ctx1.get? p.2 = some v1 ∧ v1.noRc = true)) := by
          intro htag_if ctx1 rf1
          by_cases hsc : env.scalarCtors.contains cname = true
          · simpa only [ctx1, rf1, hsc, ↓reduceIte] using
              markScalarBranch_invs hinv hclean hpo hnorc hpcb hsth hepres hsbv hsbp hexcl
                hshd hgx hlx hρx (htag_if hsc)
          · have hsub : ctx1 = rf.ctx := ite_eq_right (fun hc => absurd hc hsc)
            have hrfe : rf1 = rf := by cases rf; simp [rf1, hsub]
            rw [hrfe, hsub]
            exact ⟨hinv, hclean, hpo, hnorc, hpcb, hsth, hepres, hsbv, hsbp, hexcl, hshd,
              fun p hp => Or.inl hp⟩
        by_cases hci0 : ci = 0
        · subst hci0
          rw [PRWpCtorAlts.eq_2] at hpr
          rw [perceusAltsWf.eq_2 env retTy jps rf.ctx sm x vx.ty b rest
            0 cname tgt cname rfl] at hwf
          simp only [Bool.and_eq_true] at hwf
          by_cases hhit : 0 = tag
          · simp only [hhit, ↓reduceIte] at hpr ⊢
            obtain ⟨htag_if, hpr_b⟩ := hpr
            obtain ⟨hrc1, hc1, hpo1, hnr1, hpcb1, hsth1, hep1, hsbv1, hsbp1, hex1, hsh1, hsp1⟩ :=
              hstep_ctx1 htag_if
            have hρ0 : (ρP x).bind PVal.tag? = some 0 := by rwa [hhit]
            rcases hsp1 (x, tgt) hsp_tgt with hp1_mem | ⟨_, v1, hgv1, hno1⟩
            · obtain ⟨hrc2, hc2, hpo2, hnr2, hpcb2, hsth2, hep2, hsbv2, hsbp2, hex2, hsh2⟩ :=
                markExcl_invs hrc1 hc1 hpo1 hnr1 hpcb1 hsth1 hep1 hsbv1 hsbp1 hex1 hsh1 hp1_mem hρ0
              exact hbody ⟨LcPat.ctor 0 cname, hmem _ _ List.mem_cons_self⟩ _
                ⟨LcPat.ctor 0 cname, hmem _ _ List.mem_cons_self, rfl⟩
                hwf.1.2 hpr_b hrc2 hc2 hpo2 hnr2 hpcb2 hsth2 hih hep2 hsbv2 hsbp2 hex2 hsw hsh2 hrs
            · have hctx_eq : (if env.scalarCtors.contains cname = true
                  then rf.ctx.markScalarBranch x else rf.ctx).markExcl tgt =
                  (if env.scalarCtors.contains cname = true
                    then rf.ctx.markScalarBranch x else rf.ctx) := by
                dsimp only at hgv1
                unfold RcCtx.markExcl; rw [hgv1]; dsimp only; rw [hno1]; simp
              rw [hctx_eq] at hwf hpr_b
              exact hbody ⟨LcPat.ctor 0 cname, hmem _ _ List.mem_cons_self⟩ _
                ⟨LcPat.ctor 0 cname, hmem _ _ List.mem_cons_self, hctx_eq.symm⟩
                hwf.1.2 hpr_b hrc1 hc1 hpo1 hnr1 hpcb1 hsth1 hih hep1 hsbv1 hsbp1 hex1 hsw hsh1 hrs
          · simp only [hhit, ↓reduceIte] at hpr ⊢
            exact ih (fun p b' hm => hmem p b' (List.mem_cons_of_mem _ hm)) hwf.2 hpr
        · have hne : ∀ (tgt' : Nat), some tgt = some tgt' → ci = 0 → False := fun _ _ h => hci0 h
          have hne2 : ∀ (tgt' : Nat) (name : String),
              some tgt = some tgt' → LcPat.ctor ci cname = LcPat.ctor 0 name → False :=
            fun _ _ _ hc => by cases hc; exact hci0 rfl
          rw [PRWpCtorAlts.eq_3 m env retTy Δr jps rf.ctx x (some tgt) pv Jp ρP tag rem wr rcr Qp Xp
            _ ci cname b rest hne] at hpr
          rw [perceusAltsWf.eq_3 env retTy jps rf.ctx sm x vx.ty b rest
            ci cname (some tgt) hne2] at hwf
          simp only [Bool.and_eq_true] at hwf
          by_cases hhit : ci = tag
          · simp only [hhit, ↓reduceIte] at hpr ⊢
            obtain ⟨htag_if, hpr_b⟩ := hpr
            obtain ⟨hrc1, hc1, hpo1, hnr1, hpcb1, hsth1, hep1, hsbv1, hsbp1, hex1, hsh1, _⟩ :=
              hstep_ctx1 htag_if
            exact hbody ⟨LcPat.ctor ci cname, hmem _ _ List.mem_cons_self⟩ _
              ⟨LcPat.ctor ci cname, hmem _ _ List.mem_cons_self, by
                dsimp only [casesBranchCtx]
                cases ci with
                | zero => exact absurd rfl hci0
                | succ _ => rfl⟩
              hwf.1.2 hpr_b hrc1 hc1 hpo1 hnr1 hpcb1 hsth1 hih hep1 hsbv1 hsbp1 hex1 hsw hsh1 hrs
          · simp only [hhit, ↓reduceIte] at hpr ⊢
            exact ih (fun p b' hm => hmem p b' (List.mem_cons_of_mem _ hm)) hwf.2 hpr
  | none =>
    induction alts' with
    | nil =>
      rw [HWpCtorAlts.eq_1]
      rw [PRWpCtorAlts.eq_1] at hpr
      exact hpr_dflt hpr
    | cons a rest ih =>
      rcases a with ⟨pat, b⟩
      cases pat with
      | dflt =>
        rw [HWpCtorAlts.eq_3]
        rw [PRWpCtorAlts.eq_4] at hpr
        have hne : ∀ (tgt' : Nat) (name : String),
            none = some tgt' → LcPat.dflt = LcPat.ctor 0 name → False := by
          intro _ _ h; cases h
        rw [perceusAltsWf.eq_4 env retTy jps rf.ctx sm x vx.ty b rest none hne] at hwf
        simp only [Bool.true_and, Bool.and_eq_true] at hwf
        exact ih (fun p b' hm => hmem p b' (List.mem_cons_of_mem _ hm)) hwf.2 hpr
      | ctor ci cname =>
        rw [HWpCtorAlts.eq_2]
        have hne : ∀ (tgt' : Nat), none = some tgt' → ci = 0 → False := fun _ h => by cases h
        have hne2 : ∀ (tgt' : Nat) (name : String),
            none = some tgt' → LcPat.ctor ci cname = LcPat.ctor 0 name → False :=
          fun _ _ h => by cases h
        rw [PRWpCtorAlts.eq_3 m env retTy Δr jps rf.ctx x none pv Jp ρP tag rem wr rcr Qp Xp
          _ ci cname b rest hne] at hpr
        rw [perceusAltsWf.eq_3 env retTy jps rf.ctx sm x vx.ty b rest
          ci cname none hne2] at hwf
        simp only [Bool.and_eq_true] at hwf
        by_cases hhit : ci = tag
        · simp only [hhit, ↓reduceIte] at hpr ⊢
          obtain ⟨htag_if, hpr_b⟩ := hpr
          by_cases hsc : env.scalarCtors.contains cname = true
          · obtain ⟨hrc1, hc1, hpo1, hnr1, hpcb1, hsth1, hep1, hsbv1, hsbp1, hex1, hsh1, _⟩ :=
              markScalarBranch_invs hinv hclean hpo hnorc hpcb hsth hepres hsbv hsbp hexcl
                hshd hgx hlx hρx (htag_if hsc)
            have hctx_eq :
                (if env.scalarCtors.contains cname = true
                  then rf.ctx.markScalarBranch x else rf.ctx) =
                  rf.ctx.markScalarBranch x := ite_eq_left hsc
            exact hbody ⟨LcPat.ctor ci cname, hmem _ _ List.mem_cons_self⟩
              (rf.ctx.markScalarBranch x)
              ⟨LcPat.ctor ci cname, hmem _ _ List.mem_cons_self,
                by cases ci <;> exact hctx_eq.symm⟩
              (hctx_eq ▸ hwf.1.2) (hctx_eq ▸ hpr_b)
              hrc1 hc1 hpo1 hnr1 hpcb1 hsth1 hih hep1 hsbv1 hsbp1 hex1 hsw hsh1 hrs
          · have hctx_eq :
                (if env.scalarCtors.contains cname = true
                  then rf.ctx.markScalarBranch x else rf.ctx) =
                  rf.ctx := ite_eq_right (fun hc => absurd hc hsc)
            have hrfe : ({ rf with ctx := rf.ctx } : RcFrame) = rf := by cases rf; rfl
            exact hbody ⟨LcPat.ctor ci cname, hmem _ _ List.mem_cons_self⟩ rf.ctx
              ⟨LcPat.ctor ci cname, hmem _ _ List.mem_cons_self,
                by cases ci <;> exact hctx_eq.symm⟩
              (hctx_eq ▸ hwf.1.2) (hctx_eq ▸ hpr_b)
              (hrfe ▸ hinv) hclean hpo hnorc (hrfe ▸ hpcb) (hrfe ▸ hsth) hih
              (hrfe ▸ hepres) hsbv hsbp (hrfe ▸ hexcl) hsw (hrfe ▸ hshd) hrs
        · simp only [hhit, ↓reduceIte] at hpr ⊢
          exact ih (fun p b' hm => hmem p b' (List.mem_cons_of_mem _ hm)) hwf.2 hpr

/-- Stepwise simulation for `LcCode.cases` exposing the exact branch pattern and
    `casesBranchCtx`. -/
public theorem cases_branch_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {J : HJEnv} {Jp : PResJEnv} {Q : PResPost} {Xp : PResXPost}
    {Qh : HPost} {Xh : HXPost} {jps : List RcJpInfo} {rf rf0 : RcFrame} {σ σ0 : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr x : Nat}
    {alts : List (LcPat × LcCode)}
    (hwf : perceusCodeWf env retTy jps rf.ctx sm (LcCode.cases x alts) = true)
    (hchk : rf.ctx.checkLive x = .ok ())
    (hpr : PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Q Xp (LcCode.cases x alts))
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx)
    (hsbp : SharedBoolPreds rf.ctx) (hexcl : ExclCtorHeap rf) (hsw : ShadowSmWf sm)
    (hshd : ShadowOk sm rf.ctx ρP rf.envP) (hrs : ResStateInv σ rem wr rcr)
    (hbody : ∀ {b : LcCode}, (∃ pat, (pat, b) ∈ alts) →
      ∀ (ctx' : RcCtx), let rf' : RcFrame := { rf with ctx := ctx' }
      (∃ pat, (pat, b) ∈ alts ∧
        ctx' = casesBranchCtx env ((rf.ctx.sharedPreds.find? (·.1 == x)).map Prod.snd)
          pat x rf.ctx) →
      perceusCodeWf env retTy jps ctx' sm b = true →
      PRWp m env retTy Δr jps ctx' Jp ρP rem wr rcr Q Xp b →
      RcInv rt rf' σ → CleanVars ctx' → ParentsOwned ctx' → NoRcCorrect ctx' →
      ParentChildBacked rf' σ.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ.objs → EntryPres rf0 σ0 rf' σ →
      SharedBoolVars ctx' → SharedBoolPreds ctx' → ExclCtorHeap rf' →
      ShadowSmWf sm → ShadowOk sm ctx' ρP rf'.envP → ResStateInv σ rem wr rcr →
      HWp Δh rt retTy J rf.envH Qh Xh b σ) :
    HWp Δh rt retTy J rf.envH Qh Xh (LcCode.cases x alts) σ := by
  obtain ⟨vx, hgx, hlx⟩ := checkLive_facts hchk
  rw [perceusCodeWf.eq_5] at hwf
  rw [hgx] at hwf
  rw [PRWp.eq_4] at hpr
  rw [hgx] at hpr
  cases hptag : (ρP x).bind PVal.tag? with
  | none => rw [hptag] at hpr; exact False.elim hpr
  | some tag =>
    cases hρx : ρP x with
    | none => rw [hρx] at hptag; cases hptag
    | some pv =>
      rw [hptag, hρx] at hpr
      dsimp only at hpr
      obtain ⟨hsafe, hpr_alts⟩ := hpr
      have htag : pv.tag? = some tag := by rw [hρx] at hptag; exact hptag
      have hc_tag := casesTag_step hinv hshd hgx hlx hρx htag hsafe
      rw [HWp.eq_4]
      refine ⟨tag, hc_tag, ctor_alts_sim hgx hlx hρx hptag
        (fun tgt h => find_sharedPreds_some h)
        hinv hclean hpo hnorc hpcb hsth hih hepres hsbv hsbp hexcl hsw hshd hrs
        (fun p b hm => hm) hwf ?_ hpr_alts hbody⟩
      intro hpr_d
      have hrfe : ({ rf with ctx := rf.ctx } : RcFrame) = rf := by cases rf; rfl
      exact dflt_alts_sim (fun p b hm => hm) hwf hpr_d fun hm hbwf hbp =>
        hbody ⟨LcPat.dflt, hm⟩ rf.ctx ⟨LcPat.dflt, hm, rfl⟩ hbwf hbp
          (hrfe ▸ hinv) hclean hpo hnorc (hrfe ▸ hpcb) (hrfe ▸ hsth)
          hih (hrfe ▸ hepres) hsbv hsbp (hrfe ▸ hexcl) hsw (hrfe ▸ hshd) hrs

/-- Stepwise simulation for `LcCode.cases`. -/
public theorem cases_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {J : HJEnv} {Jp : PResJEnv} {Q : PResPost} {Xp : PResXPost}
    {Qh : HPost} {Xh : HXPost} {jps : List RcJpInfo} {rf rf0 : RcFrame} {σ σ0 : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr x : Nat}
    {alts : List (LcPat × LcCode)}
    (hwf : perceusCodeWf env retTy jps rf.ctx sm (LcCode.cases x alts) = true)
    (hchk : rf.ctx.checkLive x = .ok ())
    (hpr : PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Q Xp (LcCode.cases x alts))
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx)
    (hsbp : SharedBoolPreds rf.ctx) (hexcl : ExclCtorHeap rf) (hsw : ShadowSmWf sm)
    (hshd : ShadowOk sm rf.ctx ρP rf.envP) (hrs : ResStateInv σ rem wr rcr)
    (hbody : ∀ {b : LcCode}, (∃ pat, (pat, b) ∈ alts) →
      ∀ (ctx' : RcCtx), let rf' : RcFrame := { rf with ctx := ctx' }
      perceusCodeWf env retTy jps ctx' sm b = true →
      PRWp m env retTy Δr jps ctx' Jp ρP rem wr rcr Q Xp b →
      RcInv rt rf' σ → CleanVars ctx' → ParentsOwned ctx' → NoRcCorrect ctx' →
      ParentChildBacked rf' σ.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ.objs → EntryPres rf0 σ0 rf' σ →
      SharedBoolVars ctx' → SharedBoolPreds ctx' → ExclCtorHeap rf' →
      ShadowSmWf sm → ShadowOk sm ctx' ρP rf'.envP → ResStateInv σ rem wr rcr →
      HWp Δh rt retTy J rf.envH Qh Xh b σ) :
    HWp Δh rt retTy J rf.envH Qh Xh (LcCode.cases x alts) σ :=
  cases_branch_step hwf hchk hpr hinv hclean hpo hnorc hpcb hsth hih hepres hsbv hsbp hexcl
    hsw hshd hrs fun hm ctx' _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 =>
      hbody hm ctx' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16

end CasesStep

end LeanQbe.T.LeanLCNF.Sem
