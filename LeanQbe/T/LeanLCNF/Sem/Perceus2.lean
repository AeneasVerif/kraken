module

public import LeanQbe.T.LeanLCNF.Sem.Perceus1

/-!
# Perceus Tier-P → Tier-H Soundness, Part 2: Frame/Heap Transitions & Primitives

Proves:
- `RcInv` preservation across fresh binders (`rcInv_bind_nonPtr`, `rcInv_bind_isShared`,
  `rcInv_bind_borrowed`, `rcInv_fresh_alloc_bind`).
- Argument-consumption & call-boundary transitions (`rcInv_consumeVar_to_ghost`,
  `rcInv_applyArgs_shift`, `rcInv_call_setup`, `rcInv_after_call`).
- Argument, `primNatP` fast-path, `primUintP`, and read-only primitive simulation lemmas.
- Reference-counting (`inc`, non-cold `dec`, standalone `decCold_clean`, exclusive `del`),
  in-place FBIP update (`oset`, `uset`, `sset`, `setTag`), and `cases` / join-point context lemmas.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

public section

/-! ## 1. Fresh Non-Allocating, `isShared`, and Borrowed Binders -/

theorem rcInv_bind_nonPtr {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx)
    {x : Nat} (hfr : binderFreshOwned rf.ctx x = true)
    (ty : LcTy) (excl : Bool) {pv : PVal} {w : Word}
    (hrep : ValRep ty pv w σ.objs)
    (htag : ¬ty.isScalar → ∃ bv : BitVec 64, w = Word.i64 bv ∧ (bv &&& 1#64) ≠ 0#64) :
    let ctx' := rf.ctx.bindOwned x ty excl false false
    let rf' : RcFrame :=
      { ctx := ctx', envP := rf.envP.set x pv, envH := rf.envH.set x ty w
        extH := rf.extH, ghostH := rf.ghostH }
    RcInv rt rf' σ ∧ CleanVars rf'.ctx := by
  let vx : RcVar :=
    { id := x, ty, noRc := !ty.needsRc
      persistent := false, owned := if !ty.needsRc then 0 else 1
      borrowed := false, parent? := none
      excl := if !ty.needsRc then false else excl, resetTok := false }
  have hvx_eq : rf.ctx.bindOwned x ty excl false false = rf.ctx.put vx := by
    cases hnr : ty.needsRc <;> simp [RcCtx.bindOwned, vx, hnr]
  have hcv : CleanVar vx := by
    simpa [RcCtx.bindOwned, vx] using cleanVar_bindOwned x ty excl false
  have hv0 : varHandles (rf.envH.set x ty w) vx = [] := by
    unfold varHandles
    by_cases hnr : ty.needsRc = true
    · have hns : ¬ty.isScalar := by cases ty <;> simp_all [LcTy.needsRc, LcTy.isScalar]
      obtain ⟨bv, hw, hne⟩ := htag hns
      simp only [vx, hnr, Bool.not_true, Bool.false_or, HValEnv.set, ↓reduceIte, hw,
        Word.toBV64?, Word.i64, beq_iff_eq]
      simp [hne]
    · have hnr' : (!ty.needsRc) = true := by simp [hnr]
      simp [vx, hnr']
  have hvarX : VarInv vx { ctx := rf.ctx.put vx, envP := rf.envP.set x pv
                           envH := rf.envH.set x vx.ty w, extH := rf.extH, ghostH := rf.ghostH }
      σ.objs := by
    intro _
    refine ⟨pv, w, by simp [vx, PValEnv.set], by simp [vx, HValEnv.set], hrep, ?_⟩
    intro hns
    obtain ⟨bv, hw, hne⟩ := htag hns
    refine ⟨bv, hw, fun _ => hne, fun hp => by simp [vx] at hp, fun he => ?_,
      fun _ _ hb => by simp [vx] at hb⟩
    by_cases hnr : ty.needsRc = true
    · exact ⟨by simp [vx, hnr], rfl, by simp [vx, hnr], fun h0 => absurd h0 hne⟩
    · simp [vx, hnr] at he
  have hsh : SharedPredInv { ctx := rf.ctx.put vx, envP := rf.envP.set x pv
                             envH := rf.envH.set x vx.ty w, extH := rf.extH, ghostH := rf.ghostH }
      σ.objs := by
    intro p hp
    have hsp : p ∈ rf.ctx.sharedPreds := by simpa [RcCtx.put] using hp
    exact sharedPredInv_put_zero hinv rfl hfr hv0 p hsp
  have hmain := rcInv_put_fresh hinv hclean hfr rfl hcv
    hinv.1 (fun o ho hwo => ⟨o, ho, objDataEq_refl o hwo, rfl⟩)
    hvarX (by rw [hv0, List.nil_append]; exact hinv.2.2.1)
    (fun bv hb => backed_mono_roots (fun r hr => by
      rcases List.mem_append.mp hr with h1 | h2
      · rcases List.mem_append.mp h1 with hloc | hext
        · have heq : (localHandles (rf.ctx.put vx) (rf.envH.set x vx.ty w)).Perm
              (localHandles rf.ctx rf.envH) := by
            have hp := localHandles_put_perm hinv.2.1 (rf.envH.set x ty w) vx
            change (localHandles (rf.ctx.put vx) (rf.envH.set x vx.ty w)).Perm
              (varHandles (rf.envH.set x ty w) vx ++
                localHandlesExcept rf.ctx (rf.envH.set x ty w) x) at hp
            rw [hv0, List.nil_append] at hp
            rw [localHandlesExcept_congr_env (ctx := rf.ctx) (envH := rf.envH)
              (envH' := rf.envH.set x ty w) x (fun y hy => by simp [HValEnv.set, hy])] at hp
            exact hp.trans (localHandlesExcept_fresh_perm hinv.2.1 hfr)
          have hr' := heq.symm.mem_iff.mp hloc
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hr')))
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hext)))
      · exact List.mem_append.mpr (Or.inr h2)) hb)
    (fun _ hb => hb) hsh
  rw [hvx_eq]
  exact hmain

theorem rcInv_bind_isShared {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx)
    {x y : Nat} (hfr : binderFreshOwned rf.ctx x = true)
    {vy : RcVar} (hgy : rf.ctx.get? y = some vy) (hylive : vy.isLive = true)
    (hyown : vy.owned ≤ 1)
    {bv : BitVec 64} (hyh : rf.envH y = some (vy.ty, Word.i64 bv))
    {o : LcnfObj} (ho : o ∈ σ.objs) (hoa : o.addr = bv) :
    let b := decide (o.rc ≠ 1#32)
    let ctx1 := rf.ctx.bindOwned x .uint8 false false false
    let ctx' := { ctx1 with sharedPreds := (x, y) :: ctx1.sharedPreds }
    let rf' : RcFrame :=
      { ctx := ctx', envP := rf.envP.set x (PVal.bool b)
        envH := rf.envH.set x .uint8 (Word.i8 (if o.rc ≠ 1#32 then 1#8 else 0#8))
        extH := rf.extH, ghostH := rf.ghostH }
    RcInv rt rf' σ ∧ CleanVars rf'.ctx := by
  let b := decide (o.rc ≠ 1#32)
  let w := Word.i8 (if o.rc ≠ 1#32 then 1#8 else 0#8)
  have hrep : ValRep .uint8 (PVal.bool b) w σ.objs := by
    unfold ValRep ScalarRep
    dsimp only [LcTy.isScalar, LcTy.width, ite_true]
    by_cases hrc : o.rc ≠ 1#32
    · have hb1 : b = true := decide_eq_true hrc
      have hw1 : w = Word.i8 1#8 := by dsimp only [w]; rw [ite_eq_left hrc]
      rw [hb1, hw1]
      dsimp only [PVal.bool]
      exact Or.inl ⟨1#8, rfl, rfl⟩
    · have hb0 : b = false := decide_eq_false hrc
      have hw0 : w = Word.i8 0#8 := by dsimp only [w]; rw [ite_eq_right hrc]
      rw [hb0, hw0]
      dsimp only [PVal.bool]
      exact Or.inl ⟨0#8, rfl, rfl⟩
  have hbase := rcInv_bind_nonPtr hinv hclean hfr .uint8 false hrep (fun h => nomatch h)
  rcases hbase with ⟨hbInv, hbClean⟩
  let ctx1 := rf.ctx.bindOwned x .uint8 false false false
  let ctx' : RcCtx := { ctx1 with sharedPreds := (x, y) :: ctx1.sharedPreds }
  let rf' : RcFrame :=
    { ctx := ctx', envP := rf.envP.set x (PVal.bool b), envH := rf.envH.set x .uint8 w
      extH := rf.extH, ghostH := rf.ghostH }
  have hne_yx : y ≠ x := by
    intro rfl
    have ha := hfr
    simp only [binderFreshOwned, Bool.and_eq_true] at ha
    rw [hgy] at ha
    simp [hylive] at ha
  have hotherH : ∀ z, z ≠ x → rf'.envH z = rf.envH z := fun z hz => by
    simp [rf', HValEnv.set, hz]
  let vx0 : RcVar :=
    { id := x, ty := .uint8, noRc := true, persistent := false, owned := 0,
      borrowed := false, parent? := none, excl := false, resetTok := false }
  have hvx_put : ctx1 = rf.ctx.put vx0 := rfl
  have hsh : SharedPredInv rf' σ.objs := by
    intro p hp vb' vx' hg1 hg2 hbl hno hps
    rcases List.mem_cons.mp hp with rfl | hp'
    · have hg1x : ctx'.get? x = some vx0 := by
        change ctx1.get? x = some vx0
        rw [hvx_put]
        have hpg := RcCtx.put_get? hinv.2.1 vx0 x
        simpa [vx0] using hpg
      have hg2y : ctx'.get? y = some vy := by
        change ctx1.get? y = some vy
        rw [hvx_put]
        have hpg := RcCtx.put_get? hinv.2.1 vx0 y
        dsimp only [vx0] at hpg
        rw [beq_false_of_ne hne_yx, hgy] at hpg
        exact hpg
      rw [hg1x] at hg1; cases hg1
      rw [hg2y] at hg2; cases hg2
      have hbv0 : (bv &&& 1#64) = 0#64 := hoa ▸ obj_addr_and1_zero (hinv.1.1.2.1 o ho)
      have hey : rf'.envH y = some (vy.ty, Word.i64 bv) := by
        rw [hotherH y hne_yx]; exact hyh
      constructor
      · intro hp0
        have hrc1 : o.rc = 1#32 := by
          by_cases hrc : o.rc = 1#32
          · exact hrc
          · exfalso
            have hb1 : b = true := decide_eq_true hrc
            simp [rf', PValEnv.set, hb1, PVal.bool, PVal.tag?] at hp0
        refine ⟨bv, hey, hbv0, fun hown => ?_⟩
        have hown1 : vy.owned = 1 := by omega
        have hy_mem := (RcCtx.get?_mem hgy).1
        have hy_rtok := (hclean vy hy_mem).2.2.2.2
        have ⟨h0np, h0cnt, _⟩ := handlesRcSound_excl_unique hinv.2.1 hinv.2.2.1 hy_mem hno hps
          hy_rtok hown1 ((RcCtx.get?_mem hgy).2 ▸ hyh) ho (hinv.1.1.2.1 o ho) hoa hrc1
        have hv0x : varHandles rf'.envH vx0 = [] := by unfold varHandles; simp [vx0]
        have hcnt := localHandlesExcept_put_zero_count hinv.2.1 (v := vx0) hfr hotherH
          hv0x hne_yx hy_mem (RcCtx.get?_mem hgy).2 bv
        have hnp0 : nonPersistRefs σ.objs bv +
            (localHandlesExcept rf'.ctx rf'.envH y ++ rf'.extH ++ rf'.ghostH).count bv = 0 := by
          have hcnt' : (localHandlesExcept rf'.ctx rf'.envH y).count bv =
              (localHandlesExcept rf.ctx rf.envH y).count bv := by
            have h1 : localHandlesExcept rf'.ctx rf'.envH y =
                localHandlesExcept (rf.ctx.put vx0) rf'.envH y := by
              change localHandlesExcept ctx1 rf'.envH y = _; rw [hvx_put]
            rw [h1]; exact hcnt
          rw [(RcCtx.get?_mem hgy).2] at h0cnt
          rw [List.count_append, List.count_append, hcnt']
          simp only [rf', List.count_append] at h0cnt ⊢
          omega
        exact ⟨hnp0, o, ho, hoa, by rw [hrc1, hown1]; decide⟩
      · intro hp1 hown
        have hrcNe : o.rc ≠ 1#32 := by
          intro heq1
          have hb0 : b = false := decide_eq_false (fun h => h heq1)
          simp [rf', PValEnv.set, hb0, PVal.bool, PVal.tag?] at hp1
        refine ⟨bv, hey, hbv0, o, ho, hoa, ?_⟩
        have h0rc := (hinv.1.1.2.1 o ho).2.2.1
        by_cases hrc0 : o.rc = 0#32
        · exact Or.inl hrc0
        · right
          have hpos := rc_toInt_pos_of_ne_zero h0rc hrc0
          have hneNat : o.rc.toNat ≠ 1 := fun h => hrcNe (BitVec.eq_of_toNat_eq h)
          have hposNat : 0 < o.rc.toNat := by
            rw [BitVec.toInt_eq_toNat_cond] at hpos; split at hpos <;> omega
          omega
    · have hsh1 : p ∈ (rf.ctx.bindOwned x .uint8 false false false).sharedPreds := hp'
      exact hbInv.2.2.2.2 p hsh1 vb' vx' hg1 hg2 hbl hno hps
  exact ⟨⟨hbInv.1, hbInv.2.1, hbInv.2.2.1, hbInv.2.2.2.1, hsh⟩, hbClean⟩

theorem rcInv_bind_borrowed {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx)
    {x src : Nat} (hfr : binderFreshOwned rf.ctx x = true)
    (ty : LcTy) (hty : ty.needsRc = true) {p? : Option Nat} {pers : Bool}
    (hpb : rf.ctx.projBacking src = .ok (p?, pers))
    {v_src : RcVar} (hgsrc : rf.ctx.get? src = some v_src)
    (hns_src : ¬v_src.ty.isScalar)
    {bv_src : BitVec 64} (hsrch : rf.envH src = some (v_src.ty, Word.i64 bv_src))
    {o_src : LcnfObj} (hosrc : o_src ∈ σ.objs) (hoasrc : o_src.addr = bv_src)
    {pv : PVal} {bv : BitVec 64} (hrep : ValRep ty pv (Word.i64 bv) σ.objs)
    (hch : (bv &&& 1#64) = 0#64 → bv ∈ o_src.childFields) :
    let ctx' := rf.ctx.bindBorrowed x ty p? pers
    let rf' : RcFrame :=
      { ctx := ctx', envP := rf.envP.set x pv, envH := rf.envH.set x ty (Word.i64 bv)
        extH := rf.extH, ghostH := rf.ghostH }
    RcInv rt rf' σ ∧ CleanVars rf'.ctx := by
  let vx : RcVar :=
    { id := x, ty, noRc := false, persistent := pers, owned := 0, borrowed := !pers
      parent? := if pers then none else p?, excl := false, resetTok := false }
  have hvx_eq : rf.ctx.bindBorrowed x ty p? pers = rf.ctx.put vx := by
    simp [RcCtx.bindBorrowed, hty, vx]
  have hcv : CleanVar vx := by
    simpa [RcCtx.bindBorrowed, hty, vx] using cleanVar_bindBorrowed x ty p? pers
  have hv0 : varHandles (rf.envH.set x ty (Word.i64 bv)) vx = [] := by simp [varHandles, vx]
  have ⟨hsrc_mem, hsrc_id⟩ := RcCtx.get?_mem hgsrc
  have hlive_src : v_src.isLive = true := by
    unfold RcCtx.projBacking at hpb; rw [hgsrc] at hpb
    cases hl : v_src.isLive <;> simp_all
  obtain ⟨_, w_src, _, hsrc_eh, _, hnon_src⟩ := hinv.2.2.2.1 v_src hsrc_mem hlive_src
  obtain ⟨bv_s, hw_s, hno_s, hpers_s, _, hbr_s⟩ := hnon_src hns_src
  have hbv_eq : bv_s = bv_src := by
    rw [hsrc_id] at hsrc_eh
    rw [hsrc_eh] at hsrch
    have heqw : w_src = Word.i64 bv_src := by cases hsrch; rfl
    have heq2 : Word.i64 bv_s = Word.i64 bv_src := hw_s.symm.trans heqw
    simpa [Word.i64] using heq2
  subst hbv_eq
  have hsrc_no0 : v_src.noRc = false := by
    by_cases hnt : v_src.noRc = false
    · exact hnt
    · exfalso
      have hnt' : v_src.noRc = true := by cases h : v_src.noRc <;> simp_all
      exact hno_s hnt' (hoasrc ▸ obj_addr_and1_zero (hinv.1.1.2.1 o_src hosrc))
  have hsrc_cs := hclean v_src hsrc_mem
  have hvarX : VarInv vx { ctx := rf.ctx.put vx, envP := rf.envP.set x pv
                           envH := rf.envH.set x vx.ty (Word.i64 bv),
                           extH := rf.extH, ghostH := rf.ghostH }
      σ.objs := by
    intro _
    refine ⟨pv, Word.i64 bv, by simp [vx, PValEnv.set], by simp [vx, HValEnv.set], hrep, ?_⟩
    intro _
    refine ⟨bv, rfl, fun h => by simp [vx] at h, ?_, fun h => by simp [vx] at h, ?_⟩
    · intro hpers0 hbv0
      unfold RcCtx.projBacking at hpb
      rw [hgsrc] at hpb; dsimp only at hpb; rw [hlive_src] at hpb
      have hpers_src : v_src.persistent = true := by
        by_cases hnp : v_src.persistent = true
        · exact hnp
        · exfalso
          have hnp' : v_src.persistent = false := by cases h : v_src.persistent <;> simp_all
          have hp2 : pers = false := by
            by_cases hbr0 : v_src.borrowed = true
            · simp [hnp', hbr0] at hpb; cases hpb; rfl
            · by_cases hown0 : 0 < v_src.owned
              · simp [hnp', hbr0, hown0] at hpb; cases hpb; rfl
              · simp [hnp', hbr0, hown0] at hpb; cases hpb; rfl
          simp [vx, hp2] at hpers0
      obtain ⟨o0, ho0, hoa0, hrc0⟩ :=
        hpers_s hpers_src (hoasrc ▸ obj_addr_and1_zero (hinv.1.1.2.1 o_src hosrc))
      have heq0 := obj_eq_of_addr_nodup hinv.1.2 ho0 hosrc (hoa0.trans hoasrc.symm)
      subst heq0
      exact hinv.2.2.1.1 o0 ho0 hrc0 bv (hch hbv0) hbv0
    · intro _ hnpers hbr bv0
      have hpers_f : pers = false := by cases pers <;> simp_all [vx]
      subst hpers_f
      let rfNew : RcFrame :=
        { ctx := rf.ctx.put vx, envP := rf.envP.set x pv,
          envH := rf.envH.set x vx.ty (Word.i64 bv), extH := rf.extH, ghostH := rf.ghostH }
      have hfhPerm : (frameHandles rfNew).Perm (frameHandles rf) := by
        unfold frameHandles rfNew
        have hp := localHandles_put_perm hinv.2.1 (rf.envH.set x ty (Word.i64 bv)) vx
        change (localHandles (rf.ctx.put vx) (rf.envH.set x vx.ty (Word.i64 bv))).Perm
          (varHandles (rf.envH.set x ty (Word.i64 bv)) vx ++
            localHandlesExcept rf.ctx (rf.envH.set x ty (Word.i64 bv)) x) at hp
        rw [hv0, List.nil_append] at hp
        rw [localHandlesExcept_congr_env (ctx := rf.ctx) (envH := rf.envH)
          (envH' := rf.envH.set x ty (Word.i64 bv)) x
          (fun y hy => by simp [HValEnv.set, hy])] at hp
        exact ((hp.trans (localHandlesExcept_fresh_perm hinv.2.1 hfr)).append_right
          rf.extH).append_right rf.ghostH
      have hps_f : v_src.persistent = false := by
        unfold RcCtx.projBacking at hpb; rw [hgsrc] at hpb; dsimp only at hpb
        rw [hlive_src] at hpb
        cases hps : v_src.persistent with
        | false => rfl
        | true =>
          simp only [hps, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpb
          cases hpb
      have hb_src : Backed σ.objs (frameHandles rf) bv_s := by
        by_cases hbr_src : v_src.borrowed = true
        · exact (hbr_s hsrc_no0 hps_f hbr_src
            (hoasrc ▸ obj_addr_and1_zero (hinv.1.1.2.1 o_src hosrc))).1
        · have hown_src : 0 < v_src.owned := by
            have := hlive_src
            simp only [RcVar.isLive, hsrc_no0, hps_f, hbr_src, hsrc_cs.2.2.2.2, Bool.or_false,
              Bool.false_or] at this
            simpa using this
          have hmem_h : bv_s ∈ varHandles rf.envH v_src := by
            have hbv_src0 := hoasrc ▸ obj_addr_and1_zero (hinv.1.1.2.1 o_src hosrc)
            have hb_beq : (bv_s &&& 1#64 == 0#64) = true := beq_iff_eq.mpr hbv_src0
            unfold varHandles
            rw [hsrc_no0, hps_f, hsrc_cs.2.2.2.2]
            have hne0 : (v_src.owned == 0) = false := by
              cases h : v_src.owned <;> simp_all
            rw [hne0, hsrc_id, hsrch]
            change bv_s ∈
              (if (bv_s &&& 1#64 == 0#64) = true then List.replicate v_src.owned bv_s else [])
            rw [hb_beq, ite_eq_left rfl]
            exact List.mem_replicate.mpr ⟨Nat.ne_of_gt hown_src, rfl⟩
          have hmem_fh : bv_s ∈ frameHandles rf := by
            unfold frameHandles localHandles
            refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ?_)))
            exact List.mem_flatten.mpr
              ⟨varHandles rf.envH v_src, List.mem_map.mpr ⟨v_src, hsrc_mem, rfl⟩, hmem_h⟩
          by_cases hrc0 : o_src.rc = 0#32
          · exact Or.inl ⟨o_src, hosrc, hoasrc, hrc0⟩
          · exact Or.inr ⟨bv_s, hmem_fh, NonPersistReach.refl ⟨o_src, hosrc, hoasrc, hrc0⟩⟩
      have hb_bv := backed_trans_child_simple hinv.1.2 hinv.1.1.2.2.1 hinv.2.2.1 hb_src hosrc hoasrc
        (hch bv0) bv0
      refine ⟨backed_mono_roots (fun r hr => hfhPerm.symm.mem_iff.mp hr) hb_bv, ?_⟩
      unfold RcCtx.projBacking at hpb
      rw [hgsrc] at hpb; dsimp only at hpb; rw [hlive_src, hps_f] at hpb
      by_cases hbr_src : v_src.borrowed = true
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hbr_src] at hpb
        have hp_eq : v_src.parent? = p? := by cases hpb; rfl
        have hbr2 := (hbr_s hsrc_no0 hps_f hbr_src
          (hoasrc ▸ obj_addr_and1_zero (hinv.1.1.2.1 o_src hosrc))).2
        dsimp only [vx, Bool.false_eq_true, ite_false]
        cases hp_u : v_src.parent? with
        | none =>
          rw [hp_u] at hbr2
          rw [← hp_eq, hp_u]
          exact backed_trans_child_simple hinv.1.2 hinv.1.1.2.2.1 hinv.2.2.1 hbr2 hosrc hoasrc
            (hch bv0) bv0
        | some p =>
          rw [hp_u] at hbr2
          obtain ⟨pv0, hpvm, hpvid, hpv1, hpv2, hpv3, hpback⟩ := hbr2
          have hne_px : pv0.id ≠ x := by
            have ha := hfr
            simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at ha
            rw [hpvid]; intro rfl; exact ha.1.1 v_src hsrc_mem hp_u
          have hpx : p ≠ x := hpvid ▸ hne_px
          have hother_p : (rf.envH.set x vx.ty (Word.i64 bv)) p = rf.envH p := by
            simp [HValEnv.set, hpx]
          rw [← hp_eq, hp_u]
          refine ⟨pv0, (RcCtx.put_mem_iff hinv.2.1).mpr (Or.inr ⟨hpvm, hne_px⟩), hpvid,
            hpv1, hpv2, hpv3, ?_⟩
          rw [hother_p]
          exact backed_trans_child_simple hinv.1.2 hinv.1.1.2.2.1 hinv.2.2.1 hpback hosrc hoasrc
            (hch bv0) bv0
      · have hown_src : 0 < v_src.owned := by
          have := hlive_src
          simp only [RcVar.isLive, hsrc_no0, hps_f, hbr_src, hsrc_cs.2.2.2.2, Bool.or_false,
            Bool.false_or] at this
          simpa using this
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hbr_src, hown_src] at hpb
        have hp_eq : some src = p? := by cases hpb; rfl
        dsimp only [vx, Bool.false_eq_true, ite_false]
        rw [← hp_eq]
        have hne_sx : v_src.id ≠ x := by
          intro heq; rw [hsrc_id] at heq
          have ha := hfr; simp only [binderFreshOwned, Bool.and_eq_true] at ha
          rw [← heq, hgsrc] at ha; simp [hlive_src] at ha
        have hne_srcx : src ≠ x := hsrc_id ▸ hne_sx
        have hsrc_env :
            (rf.envH.set x vx.ty (Word.i64 bv)) src = some (v_src.ty, Word.i64 bv_s) := by
          simp [HValEnv.set, hne_srcx, hsrch]
        refine ⟨v_src, (RcCtx.put_mem_iff hinv.2.1).mpr (Or.inr ⟨hsrc_mem, hne_sx⟩), hsrc_id,
          hsrc_no0, hps_f, Or.inl hown_src, ?_⟩
        rw [hsrc_env]
        have hb_par : Backed σ.objs ([bv_s] ++ (rf.extH ++ rf.ghostH)) bv_s := by
          by_cases hrc0 : o_src.rc = 0#32
          · exact Or.inl ⟨o_src, hosrc, hoasrc, hrc0⟩
          · exact Or.inr
              ⟨bv_s, List.mem_cons_self, NonPersistReach.refl ⟨o_src, hosrc, hoasrc, hrc0⟩⟩
        exact backed_trans_child_simple hinv.1.2 hinv.1.1.2.2.1 hinv.2.2.1
          hb_par hosrc hoasrc (hch bv0) bv0
  have hsh : SharedPredInv { ctx := rf.ctx.put vx, envP := rf.envP.set x pv
                             envH := rf.envH.set x vx.ty (Word.i64 bv),
                             extH := rf.extH, ghostH := rf.ghostH }
      σ.objs := by
    intro p hp
    have hsp : p ∈ rf.ctx.sharedPreds := by simpa [RcCtx.put] using hp
    exact sharedPredInv_put_zero hinv rfl hfr hv0 p hsp
  have hmain := rcInv_put_fresh hinv hclean hfr rfl hcv
    hinv.1 (fun o ho hwo => ⟨o, ho, objDataEq_refl o hwo, rfl⟩)
    hvarX (by rw [hv0, List.nil_append]; exact hinv.2.2.1)
    (fun bv0 hb => backed_mono_roots (fun r hr => by
      rcases List.mem_append.mp hr with h1 | h2
      · rcases List.mem_append.mp h1 with hloc | hext
        · have heq : (localHandles (rf.ctx.put vx) (rf.envH.set x vx.ty (Word.i64 bv))).Perm
              (localHandles rf.ctx rf.envH) := by
            have hp := localHandles_put_perm hinv.2.1 (rf.envH.set x ty (Word.i64 bv)) vx
            change (localHandles (rf.ctx.put vx) (rf.envH.set x vx.ty (Word.i64 bv))).Perm
              (varHandles (rf.envH.set x ty (Word.i64 bv)) vx ++
                localHandlesExcept rf.ctx (rf.envH.set x ty (Word.i64 bv)) x) at hp
            rw [hv0, List.nil_append] at hp
            rw [localHandlesExcept_congr_env (ctx := rf.ctx) (envH := rf.envH)
              (envH' := rf.envH.set x ty (Word.i64 bv)) x
              (fun y hy => by simp [HValEnv.set, hy])] at hp
            exact hp.trans (localHandlesExcept_fresh_perm hinv.2.1 hfr)
          have hr' := heq.symm.mem_iff.mp hloc
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hr')))
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hext)))
      · exact List.mem_append.mpr (Or.inr h2)) hb)
    (fun _ hb => hb) hsh
  rw [hvx_eq]
  exact hmain

theorem evalArg_nonScalar_sim {rf : RcFrame} {objs : List LcnfObj}
    (hvars : ∀ v ∈ rf.ctx.vars, VarInv v rf objs)
    {a : LcArg} (hlive : match a with
      | .erased => True
      | .var id => ∃ v, rf.ctx.get? id = some v ∧ v.isLive = true ∧ ¬v.ty.isScalar)
    {pv : PVal} (heval : rf.envP.evalArg a = some pv) :
    ∃ bv : BitVec 64, rf.envH.evalArgOwn a = some (Word.i64 bv) ∧
      rf.envH.evalArgAt a .tobject = some (Word.i64 bv) ∧ ObjRep pv bv objs := by
  cases a with
  | erased =>
    simp only [PValEnv.evalArg] at heval; cases heval
    exact ⟨1#64, rfl, rfl, rfl⟩
  | var id =>
    obtain ⟨v, hgv, hlv, hns⟩ := hlive
    obtain ⟨pu, wu, hpu, hwu, hrep, hnon⟩ := hvars v (RcCtx.get?_mem hgv).1 hlv
    have hid := (RcCtx.get?_mem hgv).2
    rw [hid] at hpu hwu
    obtain ⟨bv, hwbv, _⟩ := hnon hns
    simp only [PValEnv.evalArg] at heval
    rw [hpu] at heval; cases heval
    have heown : rf.envH.evalArgOwn (.var id) = some (Word.i64 bv) := by
      simp [HValEnv.evalArgOwn, hwu, hwbv]
    have heat : rf.envH.evalArgAt (.var id) .tobject = some (Word.i64 bv) := by
      simp [HValEnv.evalArgAt, hwu, hwbv, Word.i64, LcTy.toTTy, LcTy.width]
    have hobj : ObjRep pv bv objs := by
      unfold ValRep at hrep
      rw [Bool.eq_false_iff.mpr hns] at hrep
      rcases hrep with ⟨bv', hw', hrep', _⟩
      rw [hwbv] at hw'; cases hw'; exact hrep'
    exact ⟨bv, heown, heat, hobj⟩

theorem evalObjArgs_sim {rf : RcFrame} {objs : List LcnfObj}
    (hvars : ∀ v ∈ rf.ctx.vars, VarInv v rf objs)
    {as : List LcArg} (hns : argsNonScalar rf.ctx as = true)
    (hlive : ∀ a ∈ as, match a with
      | .erased => True | .var id => ∃ v, rf.ctx.get? id = some v ∧ v.isLive = true)
    {pvs : List PVal} (heval : rf.envP.evalArgs as = some pvs) :
    ∃ bvs : List (BitVec 64), rf.envH.evalObjArgs as = some bvs ∧ objFieldsRep pvs bvs objs := by
  induction as generalizing pvs with
  | nil =>
    simp only [PValEnv.evalArgs] at heval; cases heval
    exact ⟨[], rfl, trivial⟩
  | cons a as ih =>
    simp only [argsNonScalar, List.all_cons, Bool.and_eq_true] at hns
    simp only [PValEnv.evalArgs] at heval
    cases ha : rf.envP.evalArg a with
    | none => simp [ha] at heval
    | some pv =>
      cases has : rf.envP.evalArgs as with
      | none => simp [ha, has] at heval
      | some pvs' =>
        simp only [ha, has] at heval; cases heval
        have h1 : ∃ bv : BitVec 64, rf.envH.evalArgAt a .tobject = some (Word.i64 bv) ∧
            ObjRep pv bv objs := by
          cases a with
          | erased =>
            obtain ⟨bv, _, heat, hobj⟩ := evalArg_nonScalar_sim hvars (a := .erased) trivial ha
            exact ⟨bv, heat, hobj⟩
          | var id =>
            obtain ⟨v, hgv, hlv⟩ := hlive (.var id) List.mem_cons_self
            have ha2 := hns.1
            dsimp only at ha2; rw [hgv] at ha2
            have hvns : ¬v.ty.isScalar := by cases h : v.ty.isScalar <;> simp_all
            obtain ⟨bv, _, heat, hobj⟩ :=
              evalArg_nonScalar_sim hvars (a := .var id) ⟨v, hgv, hlv, hvns⟩ ha
            exact ⟨bv, heat, hobj⟩
        obtain ⟨bv, heat, hobj⟩ := h1
        obtain ⟨bvs, hbvs, hrest⟩ := ih hns.2 (fun u hu => hlive u (List.mem_cons_of_mem _ hu)) has
        refine ⟨bv :: bvs, ?_, hobj, hrest⟩
        simp [HValEnv.evalObjArgs, heat, hbvs, Word.toBV64?, Word.i64]

inductive ArgsValRep : List PVal → List Word → List LcnfObj → Prop
  | nil (objs : List LcnfObj) : ArgsValRep [] [] objs
  | cons {pv : PVal} {w : Word} {pvs : List PVal} {ws : List Word} {objs : List LcnfObj} :
      (∃ ty : LcTy, ValRep ty pv w objs) → ArgsValRep pvs ws objs →
      ArgsValRep (pv :: pvs) (w :: ws) objs

theorem evalArgsOwn_sim {rf : RcFrame} {objs : List LcnfObj}
    (hvars : ∀ v ∈ rf.ctx.vars, VarInv v rf objs) :
    ∀ {as : List LcArg} {pvs : List PVal},
      (∀ a ∈ as, match a with
        | .erased => True | .var id => ∃ v, rf.ctx.get? id = some v ∧ v.isLive = true) →
      rf.envP.evalArgs as = some pvs →
      ∃ ws : List Word, rf.envH.evalArgsOwn as = some ws ∧ ArgsValRep pvs ws objs := by
  intro as
  induction as with
  | nil =>
    intro pvs _ heval
    simp only [PValEnv.evalArgs] at heval; cases heval
    exact ⟨[], rfl, ArgsValRep.nil objs⟩
  | cons a as ih =>
    intro pvs hlive heval
    simp only [PValEnv.evalArgs] at heval
    cases ha : rf.envP.evalArg a with
    | none => simp [ha] at heval
    | some pv =>
      cases has : rf.envP.evalArgs as with
      | none => simp [ha, has] at heval
      | some pvs' =>
        simp only [ha, has] at heval; cases heval
        have h1 : ∃ w, rf.envH.evalArgOwn a = some w ∧ ∃ ty : LcTy, ValRep ty pv w objs := by
          cases a with
          | erased =>
            simp only [PValEnv.evalArg] at ha; cases ha
            exact ⟨Word.i64 1#64, rfl, .tobject,
              ⟨1#64, rfl, rfl, fun h => LcTy.noConfusion h, fun h => LcTy.noConfusion h⟩⟩
          | var id =>
            obtain ⟨v, hgv, hlv⟩ := hlive (.var id) List.mem_cons_self
            obtain ⟨pu, wu, hpu, hwu, hrep, _⟩ := hvars v (RcCtx.get?_mem hgv).1 hlv
            have hid := (RcCtx.get?_mem hgv).2
            rw [hid] at hpu hwu
            simp only [PValEnv.evalArg] at ha; rw [hpu] at ha; cases ha
            exact ⟨wu, by simp [HValEnv.evalArgOwn, hwu], v.ty, hrep⟩
        obtain ⟨w, hw, ty, hrep⟩ := h1
        obtain ⟨ws, hws, hf2⟩ := ih (fun u hu => hlive u (List.mem_cons_of_mem _ hu)) has
        exact ⟨w :: ws, by simp [HValEnv.evalArgsOwn, hw, hws], ArgsValRep.cons ⟨ty, hrep⟩ hf2⟩

/-! ## 2. Parent-Ownership Invariant & Heap Allocation (`rcInv_fresh_alloc_bind`) -/

/-- Every borrowed variable pointing to a local parent `p` points to a non-persistent owned root. -/
@[expose] def ParentsOwned (ctx : RcCtx) : Prop :=
  ∀ v ∈ ctx.vars, ∀ p, v.parent? = some p →
    ∃ pv ∈ ctx.vars, pv.id = p ∧ pv.noRc = false ∧ pv.persistent = false ∧
      0 < pv.owned ∧ pv.borrowed = false

theorem parentsOwned_put_none {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hpo : ParentsOwned ctx) {vx : RcVar} (hpar : ∀ u ∈ ctx.vars, u.parent? ≠ some vx.id)
    (hvp : vx.parent? = none) : ParentsOwned (ctx.put vx) := by
  intro v hv p hp
  rcases (RcCtx.put_mem_iff hnd).mp hv with rfl | ⟨hvm, _⟩
  · simp [hvp] at hp
  · obtain ⟨pv, hpvm, hpvid, hp1, hp2, hp3, hp4⟩ := hpo v hvm p hp
    have hne : pv.id ≠ vx.id := by rw [hpvid]; intro rfl; exact hpar v hvm hp
    exact ⟨pv, (RcCtx.put_mem_iff hnd).mpr (Or.inr ⟨hpvm, hne⟩), hpvid, hp1, hp2, hp3, hp4⟩

theorem parentsOwned_bindOwned {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hpo : ParentsOwned ctx) {x : Nat} (hfr : binderFreshOwned ctx x = true)
    (ty : LcTy) (excl pers rtok : Bool) :
    ParentsOwned (ctx.bindOwned x ty excl pers rtok) := by
  have hpar : ∀ u ∈ ctx.vars, u.parent? ≠ some x := by
    have ha := hfr
    simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at ha
    exact ha.1.1
  let vx : RcVar :=
    { id := x, ty, noRc := !ty.needsRc
      persistent := if !ty.needsRc then false else pers
      owned := if !ty.needsRc || pers then 0 else 1
      borrowed := false, parent? := none
      excl := if !ty.needsRc || pers then false else excl
      resetTok := if !ty.needsRc || pers then false else rtok }
  have hvx : ctx.bindOwned x ty excl pers rtok = ctx.put vx := rfl
  rw [hvx]
  exact parentsOwned_put_none hnd hpo hpar rfl

theorem parentsOwned_bindBorrowed {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hpo : ParentsOwned ctx) (hc : CleanVars ctx) {x src : Nat}
    (hfr : binderFreshOwned ctx x = true) (ty : LcTy) {p? : Option Nat} {pers : Bool}
    (hpb : ctx.projBacking src = .ok (p?, pers)) :
    ParentsOwned (ctx.bindBorrowed x ty p? pers) := by
  have hpar : ∀ u ∈ ctx.vars, u.parent? ≠ some x := by
    have ha := hfr
    simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at ha
    exact ha.1.1
  let vx : RcVar :=
    { id := x, ty, noRc := !ty.needsRc
      persistent := if !ty.needsRc then false else pers
      owned := 0, borrowed := !(!ty.needsRc) && !pers
      parent? := if !ty.needsRc || pers then none else p?
      excl := false, resetTok := false }
  have hvx : ctx.bindBorrowed x ty p? pers = ctx.put vx := rfl
  rw [hvx]
  intro v hv p hp
  rcases (RcCtx.put_mem_iff hnd).mp hv with rfl | ⟨hvm, _⟩
  · have hno : ty.needsRc = true := by
      cases hnr : ty.needsRc
      · simp [vx, hnr] at hp
      · rfl
    have hps : pers = false := by
      cases hpr : pers
      · rfl
      · simp [vx, hno, hpr] at hp
    have hpx : vx.parent? = p? := by simp [vx, hno, hps]
    rw [hpx] at hp
    unfold RcCtx.projBacking at hpb
    cases hg : ctx.get? src with
    | none => simp [hg] at hpb
    | some v_src =>
      rw [hg] at hpb; dsimp only at hpb
      have ⟨hsmem, hsid⟩ := RcCtx.get?_mem hg
      have hsc := hc v_src hsmem
      by_cases hlive : v_src.isLive = true
      · simp only [hlive, Bool.not_true, Bool.false_eq_true, ite_false] at hpb
        by_cases hps_s : v_src.persistent = true
        · simp [hps_s] at hpb; cases hpb; exact absurd hps (by simp)
        · have hps_f : v_src.persistent = false := by cases h : v_src.persistent <;> simp_all
          simp only [hps_f, Bool.false_eq_true, ite_false] at hpb
          by_cases hbr_s : v_src.borrowed = true
          · simp [hbr_s] at hpb; cases hpb
            obtain ⟨pv, hpvm, hpvid, hp1, hp2, hp3, hp4⟩ := hpo v_src hsmem p hp
            have hne : pv.id ≠ vx.id := by
              rw [hpvid]; dsimp only [vx]; intro rfl; exact hpar v_src hsmem hp
            exact ⟨pv, (RcCtx.put_mem_iff hnd).mpr (Or.inr ⟨hpvm, hne⟩), hpvid, hp1, hp2, hp3, hp4⟩
          · have hbr_f : v_src.borrowed = false := by cases h : v_src.borrowed <;> simp_all
            have hno_s : v_src.noRc = false := by
              cases h : v_src.noRc
              · rfl
              · exfalso
                simp [(hsc.1.1 h).2.2.1, (hsc.1.1 h).2.1] at hpb
                cases hpb; exact absurd hp (by simp)
            have hown_s : 0 < v_src.owned := by
              have hl := hlive
              simp [RcVar.isLive, hno_s, hps_f, hbr_f, hsc.2.2.2.2] at hl
              simpa using hl
            simp [hbr_f, hown_s] at hpb; cases hpb
            cases hp
            have hne : v_src.id ≠ vx.id := by
              rw [hsid]; dsimp only [vx]; intro rfl
              have ha := hfr; simp only [binderFreshOwned, Bool.and_eq_true] at ha
              rw [hg] at ha; simp [hlive] at ha
            exact ⟨v_src, (RcCtx.put_mem_iff hnd).mpr (Or.inr ⟨hsmem, hne⟩), hsid,
              hno_s, hps_f, hown_s, hbr_f⟩
      · simp [hlive] at hpb
  · obtain ⟨pv, hpvm, hpvid, hp1, hp2, hp3, hp4⟩ := hpo v hvm p hp
    have hne : pv.id ≠ vx.id := by
      rw [hpvid]; dsimp only [vx]; intro rfl; exact hpar v hvm hp
    exact ⟨pv, (RcCtx.put_mem_iff hnd).mpr (Or.inr ⟨hpvm, hne⟩), hpvid, hp1, hp2, hp3, hp4⟩

theorem parentsOwned_invalidateChildren {ctx : RcCtx} (hc : CleanVars ctx)
    (hpo : ParentsOwned ctx) (x : Nat) :
    ParentsOwned (ctx.invalidateChildren x) := by
  intro v hv p hp
  unfold RcCtx.invalidateChildren at hv
  simp only [List.mem_map] at hv
  rcases hv with ⟨u, hu, rfl⟩
  by_cases hpx : (u.parent? == some x) = true
  · simp [hpx] at hp
  · simp only [hpx, Bool.false_eq_true, ↓reduceIte] at hp
    obtain ⟨pv, hpvm, hpvid, hp1, hp2, hp3, hp4⟩ := hpo u hu p hp
    have hpar_none : pv.parent? = none := (hc pv hpvm).2.2.2.1 hp4
    have hne : (pv.parent? == some x) = false := by simp [hpar_none]
    exact ⟨pv, List.mem_map.mpr ⟨pv, hpvm, by simp [hne]⟩, hpvid, hp1, hp2, hp3, hp4⟩

theorem parentsOwned_consumeVar {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hc : CleanVars ctx) (hpo : ParentsOwned ctx) {x n : Nat} {ctx' : RcCtx}
    (hcons : ctx.consumeVar x n = .ok ctx') : ParentsOwned ctx' := by
  unfold RcCtx.consumeVar at hcons
  cases hgx : ctx.get? x with
  | none => simp [hgx] at hcons
  | some v =>
    rw [hgx] at hcons
    by_cases hnop : (v.noRc || v.persistent) = true
    · simp only [hnop, ↓reduceIte, pure] at hcons; cases hcons; exact hpo
    · simp only [hnop, Bool.false_eq_true, ↓reduceIte] at hcons
      by_cases hn0 : n == 0
      · simp only [hn0, ↓reduceIte, pure] at hcons; cases hcons; exact hpo
      · simp only [hn0, Bool.false_eq_true, ↓reduceIte] at hcons
        by_cases hlt : v.owned < n
        · simp [hlt] at hcons
        · simp only [hlt, ↓reduceIte] at hcons
          have hcv := hc v (RcCtx.get?_mem hgx).1
          have hno : v.noRc = false := by cases h : v.noRc <;> simp_all
          have hps : v.persistent = false := by cases h : v.persistent <;> simp_all
          let v' : RcVar :=
            { v with
              owned := v.owned - n
              excl := if v.owned - n == 0 then false else v.excl
              resetTok := if v.owned - n == 0 then false else v.resetTok }
          have hv'id : v'.id = v.id := rfl
          have hvid : v.id = x := (RcCtx.get?_mem hgx).2
          have hcv' : CleanVar v' := by
            refine ⟨⟨fun h => absurd h (by simp [v', hno]), hcv.1.2⟩,
              fun h => absurd h (by simp [v', hps]),
              fun hb => ⟨by simp [v', hno], by simp [v', hps], ?_⟩,
              fun hnb => hcv.2.2.2.1 hnb, ?_⟩
            · dsimp only [v']; split; rfl; exact (hcv.2.2.1 hb).2.2
            · dsimp only [v']; split; rfl; exact hcv.2.2.2.2
          change (if (v.owned - n == 0 && !v.borrowed) = true then
            Except.ok ((ctx.put v').invalidateChildren x) else Except.ok (ctx.put v')) =
              Except.ok ctx' at hcons
          have hnodup_eq : ∀ {l : List RcVar}, (l.map RcVar.id).Nodup →
              ∀ {a b : RcVar}, a ∈ l → b ∈ l → a.id = b.id → a = b := by
            intro l hl a b ha hb hid
            induction l with
            | nil => cases ha
            | cons c cs ih =>
              rw [List.map_cons, List.nodup_cons] at hl
              cases ha with
              | head =>
                cases hb with
                | head => rfl
                | tail _ hb => exact absurd (hid ▸ List.mem_map.mpr ⟨b, hb, rfl⟩) hl.1
              | tail _ ha =>
                cases hb with
                | head => exact absurd (hid.symm ▸ List.mem_map.mpr ⟨a, ha, rfl⟩) hl.1
                | tail _ hb => exact ih hl.2 ha hb
          by_cases hinv : (v.owned - n == 0 && !v.borrowed) = true
          · rw [ite_eq_left hinv] at hcons; cases hcons
            have hbr : v.borrowed = false := by
              cases hb : v.borrowed
              · rfl
              · simp [hb] at hinv
            have hpar : v.parent? = none := hcv.2.2.2.1 hbr
            intro u hu p hp
            unfold RcCtx.invalidateChildren at hu
            simp only [List.mem_map] at hu
            rcases hu with ⟨w, hw, rfl⟩
            by_cases hpx : (w.parent? == some x) = true
            · simp [hpx] at hp
            · simp only [hpx, Bool.false_eq_true, ↓reduceIte] at hp
              rcases (RcCtx.put_mem_iff hnd).mp hw with rfl | ⟨hwm, _⟩
              · simp [v', hpar] at hp
              · obtain ⟨pv, hpvm, hpvid, hp1, hp2, hp3, hp4⟩ := hpo w hwm p hp
                have hp_ne_x : p ≠ x := fun h => by
                  rw [h] at hp; exact hpx (beq_iff_eq.mpr hp)
                have hne_pv : pv.id ≠ v'.id := by
                  rw [hpvid, hv'id, hvid]; exact hp_ne_x
                have hpvm' : pv ∈ (ctx.put v').vars :=
                  (RcCtx.put_mem_iff hnd).mpr (Or.inr ⟨hpvm, hne_pv⟩)
                have hpar_none : pv.parent? = none := (hc pv hpvm).2.2.2.1 hp4
                have hne_par : (pv.parent? == some x) = false := by simp [hpar_none]
                exact ⟨pv, List.mem_map.mpr ⟨pv, hpvm', by simp [hne_par]⟩,
                  hpvid, hp1, hp2, hp3, hp4⟩
          · rw [ite_eq_right hinv] at hcons; cases hcons
            intro u hu p hp
            rcases (RcCtx.put_mem_iff hnd).mp hu with rfl | ⟨hum, _⟩
            · obtain ⟨pv, hpvm, hpvid, hp1, hp2, hp3, hp4⟩ :=
                hpo v (RcCtx.get?_mem hgx).1 p hp
              have hpv_ne : pv.id ≠ v'.id := by
                intro heq
                have hpv_eq := hnodup_eq hnd hpvm (RcCtx.get?_mem hgx).1 (heq.trans hv'id)
                rw [hpv_eq] at hp4
                have hpar_n := hcv.2.2.2.1 hp4
                change v.parent? = some p at hp; rw [hpar_n] at hp; cases hp
              exact ⟨pv, (RcCtx.put_mem_iff hnd).mpr (Or.inr ⟨hpvm, hpv_ne⟩),
                hpvid, hp1, hp2, hp3, hp4⟩
            · obtain ⟨pv, hpvm, hpvid, hp1, hp2, hp3, hp4⟩ := hpo u hum p hp
              by_cases hpvid_eq : pv.id = v'.id
              · have hpv_eq := hnodup_eq hnd hpvm (RcCtx.get?_mem hgx).1 (hpvid_eq.trans hv'id)
                rw [hpv_eq] at hp4
                have hnz : 0 < v.owned - n := by
                  have hne0 : v.owned - n ≠ 0 := fun hz => by simp [hz, hp4] at hinv
                  omega
                exact ⟨v', (RcCtx.put_mem_iff hnd).mpr (Or.inl rfl),
                  hv'id.symm.trans (hpvid_eq.symm.trans hpvid), by simp [v', hno],
                  by simp [v', hps], hnz, by simp [v', hp4]⟩
              · exact ⟨pv, (RcCtx.put_mem_iff hnd).mpr (Or.inr ⟨hpvm, hpvid_eq⟩),
                  hpvid, hp1, hp2, hp3, hp4⟩

theorem parentsOwned_applyArgs {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hc : CleanVars ctx) (hpo : ParentsOwned ctx) (as : List LcArg) (bs : List Bool)
    {ctx' : RcCtx} (ha : ctx.applyArgs as bs = .ok ctx') : ParentsOwned ctx' := by
  induction as generalizing ctx bs with
  | nil =>
    cases bs with
    | nil => simp [RcCtx.applyArgs, pure] at ha; cases ha; exact hpo
    | cons _ _ => simp [RcCtx.applyArgs] at ha
  | cons a as ih =>
    cases bs with
    | nil => simp [RcCtx.applyArgs] at ha
    | cons b bs =>
      simp only [RcCtx.applyArgs, bind, Except.bind] at ha
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte] at ha
        cases hchk : ctx.checkArgLive a with
        | error _ => simp [hchk] at ha
        | ok _ => simp only [hchk] at ha; exact ih hnd hc hpo bs ha
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
        cases hcarg : ctx.consumeArg a with
        | error _ => simp [hcarg] at ha
        | ok ctx1 =>
          simp only [hcarg] at ha
          cases a with
          | erased =>
            simp [RcCtx.consumeArg, pure] at hcarg; cases hcarg
            exact ih hnd hc hpo bs ha
          | var id =>
            exact ih (consumeVar_nodup hnd hcarg) (cleanVars_consumeVar hnd hc hcarg)
              (parentsOwned_consumeVar hnd hc hpo hcarg) bs ha

theorem binderFreshOwned_put_none {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    {vx : RcVar} (hvp : vx.parent? = none) {y : Nat} (hy : y ≠ vx.id)
    (hfr : binderFreshOwned ctx y = true) : binderFreshOwned (ctx.put vx) y = true := by
  simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hfr ⊢
  refine ⟨⟨?_, fun p hp => hfr.1.2 p (by simpa [RcCtx.put] using hp)⟩, ?_⟩
  · intro u hu
    rcases (RcCtx.put_mem_iff hnd).mp hu with rfl | ⟨hum, _⟩
    · simp [hvp]
    · exact hfr.1.1 u hum
  · rw [RcCtx.put_get? hnd vx y, beq_false_of_ne hy]
    exact hfr.2

theorem parentsOwned_bindParams {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hpo : ParentsOwned ctx) {ps : List LcParam}
    (hpsNd : (ps.map (·.id)).Nodup)
    (hfr : ps.all (fun p => binderFreshOwned ctx p.id) = true) :
    ParentsOwned (ctx.bindParams ps) := by
  induction ps generalizing ctx with
  | nil => exact hpo
  | cons p ps ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hpsNd
    simp only [List.all_cons, Bool.and_eq_true] at hfr
    have hpar : ∀ u ∈ ctx.vars, u.parent? ≠ some p.id := by
      have ha := hfr.1
      simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at ha
      exact ha.1.1
    simp only [RcCtx.bindParams, List.foldl_cons]
    by_cases hb : p.borrow = true
    · simp only [hb, ↓reduceIte]
      let vp : RcVar :=
        { id := p.id, ty := p.ty, noRc := !p.ty.needsRc, persistent := false, owned := 0,
          borrowed := !(!p.ty.needsRc), parent? := none, excl := false, resetTok := false }
      have hvp : ctx.bindBorrowed p.id p.ty = ctx.put vp := by
        cases h : p.ty.needsRc <;> simp [RcCtx.bindBorrowed, vp, h]
      rw [hvp]
      refine ih (ctx.put_nodup hnd vp) (parentsOwned_put_none hnd hpo hpar rfl) hpsNd.2 ?_
      rw [List.all_eq_true]
      intro q hq
      have hne : q.id ≠ vp.id := fun h => hpsNd.1 ⟨q, hq, h⟩
      exact binderFreshOwned_put_none hnd rfl hne (List.all_eq_true.mp hfr.2 q hq)
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      let vp : RcVar :=
        { id := p.id, ty := p.ty, noRc := !p.ty.needsRc, persistent := false,
          owned := if !p.ty.needsRc then 0 else 1, borrowed := false, parent? := none,
          excl := false, resetTok := false }
      have hvp : ctx.bindOwned p.id p.ty false false false = ctx.put vp := by
        cases h : p.ty.needsRc <;> simp [RcCtx.bindOwned, vp, h]
      rw [hvp]
      refine ih (ctx.put_nodup hnd vp) (parentsOwned_put_none hnd hpo hpar rfl) hpsNd.2 ?_
      rw [List.all_eq_true]
      intro q hq
      have hne : q.id ≠ vp.id := fun h => hpsNd.1 ⟨q, hq, h⟩
      exact binderFreshOwned_put_none hnd rfl hne (List.all_eq_true.mp hfr.2 q hq)

theorem parentsOwned_entry (ps : List LcParam) (hnd : (ps.map (·.id)).Nodup) :
    ParentsOwned ((RcCtx.mk [] []).bindParams ps) :=
  parentsOwned_bindParams (by simp) (fun _ h => by cases h) hnd
    (List.all_eq_true.mpr fun p _ => by simp [binderFreshOwned, RcCtx.get?])

theorem rcVar_eq_of_mem_nodup {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    {u v : RcVar} (hu : u ∈ ctx.vars) (hv : v ∈ ctx.vars) (hid : u.id = v.id) : u = v := by
  have hgu := (RcCtx.mem_get?_iff hnd).mpr hu
  rw [hid, (RcCtx.mem_get?_iff hnd).mpr hv] at hgu
  cases hgu; rfl

theorem parentsOwned_markExcl {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hc : CleanVars ctx) (hpo : ParentsOwned ctx) (x : Nat) : ParentsOwned (ctx.markExcl x) := by
  unfold RcCtx.markExcl
  cases hgx : ctx.get? x with
  | none => exact hpo
  | some v =>
    by_cases hcond : (!v.noRc && !v.persistent && v.owned == 1) = true
    · simp only [hcond, ↓reduceIte]
      intro u hu p hp
      rcases (RcCtx.put_mem_iff hnd).mp hu with rfl | ⟨hum, _⟩
      · obtain ⟨pv, hpvm, hpvid, hp1, hp2, hp3, hp4⟩ := hpo v (RcCtx.get?_mem hgx).1 p hp
        have hne : pv.id ≠ v.id := by
          intro heq
          have hv_eq := rcVar_eq_of_mem_nodup hnd hpvm (RcCtx.get?_mem hgx).1 heq
          have hpar_n := (hc pv hpvm).2.2.2.1 hp4
          rw [hv_eq] at hpar_n
          change ({ v with excl := true }).parent? = some p at hp
          dsimp only at hp
          rw [hpar_n] at hp; cases hp
        exact ⟨pv, (RcCtx.put_mem_iff hnd).mpr (Or.inr ⟨hpvm, hne⟩), hpvid, hp1, hp2, hp3, hp4⟩
      · obtain ⟨pv, hpvm, hpvid, hp1, hp2, hp3, hp4⟩ := hpo u hum p hp
        by_cases heq : pv.id = v.id
        · have hv_eq := rcVar_eq_of_mem_nodup hnd hpvm (RcCtx.get?_mem hgx).1 heq
          subst hv_eq
          exact ⟨{ pv with excl := true }, (RcCtx.put_mem_iff hnd).mpr (Or.inl rfl),
            hpvid, hp1, hp2, hp3, hp4⟩
        · exact ⟨pv, (RcCtx.put_mem_iff hnd).mpr (Or.inr ⟨hpvm, heq⟩), hpvid, hp1, hp2, hp3, hp4⟩
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]; exact hpo

theorem parentsOwned_markScalarBranch {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hc : CleanVars ctx) (hpo : ParentsOwned ctx) (x : Nat) :
    ParentsOwned (ctx.markScalarBranch x) := by
  unfold RcCtx.markScalarBranch
  cases hgx : ctx.get? x with
  | none => exact hpo
  | some v =>
    by_cases hty : (v.ty == .tobject || v.ty == .tagged) = true
    · simp only [hty, ↓reduceIte]
      let v' : RcVar :=
        { v with noRc := true, persistent := false, owned := 0, borrowed := false,
                 parent? := none, excl := false, resetTok := false }
      intro u hu p hp
      unfold RcCtx.invalidateChildren at hu
      simp only [List.mem_map] at hu
      rcases hu with ⟨w, hw, rfl⟩
      by_cases hpx : (w.parent? == some x) = true
      · simp [hpx] at hp
      · simp only [hpx, Bool.false_eq_true, ↓reduceIte] at hp
        rcases (RcCtx.put_mem_iff hnd).mp hw with rfl | ⟨hwm, _⟩
        · simp at hp
        · obtain ⟨pv, hpvm, hpvid, hp1, hp2, hp3, hp4⟩ := hpo w hwm p hp
          have hne_px : p ≠ x := fun h => by
            rw [h] at hp; exact hpx (beq_iff_eq.mpr hp)
          have hvid := (RcCtx.get?_mem hgx).2
          have hne_pv : pv.id ≠ v'.id := by
            rw [hpvid, show v'.id = v.id from rfl, hvid]; exact hne_px
          have hpvm' : pv ∈ (ctx.put v').vars := (RcCtx.put_mem_iff hnd).mpr (Or.inr ⟨hpvm, hne_pv⟩)
          have hpar_none : pv.parent? = none := (hc pv hpvm).2.2.2.1 hp4
          have hne_par : (pv.parent? == some x) = false := by simp [hpar_none]
          exact ⟨pv, List.mem_map.mpr ⟨pv, hpvm', by simp [hne_par]⟩, hpvid, hp1, hp2, hp3, hp4⟩
    · simp only [hty, Bool.false_eq_true, ↓reduceIte]; exact hpo

/-! ## 3. Pointer Representation & Fresh Object Allocation -/

theorem objRep_even_mem {pv : PVal} {bv : BitVec 64} {objs : List LcnfObj}
    (hrep : ObjRep pv bv objs) (heven : (bv &&& 1#64) = 0#64) :
    ∃ o ∈ objs, o.addr = bv := by
  cases pv with
  | erased =>
    rw [ObjRep] at hrep; rw [hrep] at heven; cases (by decide : (1#64 &&& 1#64) ≠ 0#64) heven
  | bits w v =>
    rcases hrep with ⟨hw, rfl⟩ | ⟨_, o, ho, hoa, _⟩
    · exact absurd heven (bv64_tagged_bits_and1 hw v)
    · exact ⟨o, ho, hoa⟩
  | nat n =>
    unfold ObjRep natRepR0 at hrep
    by_cases hn : n < 2 ^ 63
    · rw [ite_eq_left hn] at hrep; rw [hrep] at heven
      exact absurd heven (boxNat_and1_ne_zero n)
    · rw [ite_eq_right hn] at hrep; obtain ⟨_, o, ho, hoa, _⟩ := hrep; exact ⟨o, ho, hoa⟩
  | ctor cidx fields scal =>
    rcases hrep with ⟨_, _, _, rfl⟩ | ⟨_, o, ho, hoa, _⟩
    · exact absurd heven (boxNat_and1_ne_zero cidx)
    · exact ⟨o, ho, hoa⟩
  | str s => obtain ⟨o, ho, hoa, _⟩ := hrep; exact ⟨o, ho, hoa⟩
  | arr xs => obtain ⟨o, ho, hoa, _⟩ := hrep; exact ⟨o, ho, hoa⟩
  | barr bs => obtain ⟨o, ho, hoa, _⟩ := hrep; exact ⟨o, ho, hoa⟩
  | int _ => exact False.elim hrep
  | clo _ _ _ => exact False.elim hrep

theorem valRep_even_mem {ty : LcTy} {pv : PVal} {bv : BitVec 64} {objs : List LcnfObj}
    (hrep : ValRep ty pv (Word.i64 bv) objs) (hns : ¬ty.isScalar)
    (heven : (bv &&& 1#64) = 0#64) : ∃ o ∈ objs, o.addr = bv := by
  unfold ValRep at hrep
  rw [Bool.eq_false_iff.mpr hns] at hrep
  rcases hrep with ⟨bv', hw, hobj, _⟩
  cases hw
  exact objRep_even_mem hobj heven

theorem rcInv_fresh_alloc_bind {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx)
    (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    {rem wr rcr bytes : Nat} (hres : ResStateInv σ rem wr rcr)
    (hbytes : bytes ≤ rem) (hwr : 1 ≤ wr)
    {newObj : LcnfObj} (hwfNew : newObj.Wf) (hrcNew : newObj.rc = 1#32)
    (hfresh : ∀ o ∈ σ.objs, o.addr ≠ newObj.addr)
    (hcfClosed : ∀ f ∈ newObj.childFields, (f &&& 1#64) = 0#64 → ∃ q ∈ σ.objs, q.addr = f)
    (hnotSelf : newObj.addr ∉ newObj.childFields)
    {st' : RtC0State} {scrLimbs' : List (BitVec 64)}
    (hrem' : σ.st.rem - bytes ≤ st'.rem)
    (hwc' : st'.workCap = σ.st.workCap) (hbn' : BigNumRtWfR0 rt st' σ.scr scrLimbs')
    {ghostH' : List (BitVec 64)} (hghostSub : ∀ a ∈ ghostH', a ∈ rf.ghostH)
    (hconsOld : ∀ o ∈ σ.objs, 0 < o.rc.toInt →
      ghostH'.count o.addr + newObj.childFields.count o.addr ≤ rf.ghostH.count o.addr)
    (hbackExt : ∀ bv, Backed σ.objs (rf.extH ++ rf.ghostH) bv →
      Backed (newObj :: σ.objs) (rf.extH ++ ghostH') bv)
    {x : Nat} (hfr : binderFreshOwned rf.ctx x = true)
    (ty : LcTy) (hty : ty.needsRc = true) (excl : Bool) {pv : PVal}
    (hrep : ValRep ty pv (Word.i64 newObj.addr) (newObj :: σ.objs)) :
    let ctx' := rf.ctx.bindOwned x ty excl false false
    let rf' : RcFrame :=
      { ctx := ctx', envP := rf.envP.set x pv, envH := rf.envH.set x ty (Word.i64 newObj.addr),
        extH := rf.extH, ghostH := ghostH' }
    let σ' : HState := { st := st', objs := newObj :: σ.objs, scr := σ.scr, scrLimbs := scrLimbs' }
    RcInv rt rf' σ' ∧ CleanVars rf'.ctx ∧ HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs ∧
      ResStateInv σ' (rem - bytes) (wr - 1) rcr ∧
      (∀ o ∈ σ.objs, o.Wf → ∃ o' ∈ σ'.objs, ObjDataEq o o' ∧ o'.rc = o.rc) ∧
      (∀ a, Backed σ.objs (rf.extH ++ rf.ghostH) a →
        Backed σ'.objs (rf'.extH ++ rf'.ghostH) a) := by
  let vx : RcVar :=
    { id := x, ty, noRc := false, persistent := false, owned := 1,
      borrowed := false, parent? := none, excl := excl, resetTok := false }
  have hvx_eq : rf.ctx.bindOwned x ty excl false false = rf.ctx.put vx := by
    simp [RcCtx.bindOwned, hty, vx]
  have hcv : CleanVar vx := by
    cases ty <;> simp_all [CleanVar, vx, LcTy.needsRc, LcTy.isScalar]
  have hna0 : (newObj.addr &&& 1#64) = 0#64 := obj_addr_and1_zero hwfNew
  have hv1 : varHandles (rf.envH.set x ty (Word.i64 newObj.addr)) vx = [newObj.addr] := by
    unfold varHandles
    simp [vx, HValEnv.set, Word.toBV64?, Word.i64, hna0]
  have hnot_loc : (localHandles rf.ctx rf.envH).count newObj.addr = 0 := by
    rw [List.count_eq_zero]
    intro hmem
    unfold localHandles at hmem
    obtain ⟨hs, hhm, hinhs⟩ := List.mem_flatten.mp hmem
    obtain ⟨u, hum, rfl⟩ := List.mem_map.mp hhm
    unfold varHandles at hinhs
    split at hinhs
    · cases hinhs
    · rcases he : rf.envH u.id with _ | ⟨tu, wu⟩
      · simp [he] at hinhs
      · rw [he] at hinhs
        rcases hw : wu.toBV64? with _ | bv
        · dsimp only at hinhs; rw [hw] at hinhs; simp at hinhs
        · change newObj.addr ∈ (match wu.toBV64? with
            | some bv => if (bv &&& 1#64 == 0#64) = true then List.replicate u.owned bv else []
            | none => []) at hinhs
          rw [hw] at hinhs
          dsimp only at hinhs
          by_cases hev : (bv &&& 1#64 == 0#64) = true
          · rw [ite_eq_left hev] at hinhs
            have hu_eq := List.eq_of_mem_replicate hinhs
            subst hu_eq
            have hlive : u.isLive = true := by
              unfold RcVar.isLive
              rename_i hcond
              simp only [Bool.or_eq_true, beq_iff_eq] at hcond
              have : u.noRc = false ∧ u.persistent = false ∧ 0 < u.owned := by
                cases h1 : u.noRc <;> cases h2 : u.persistent <;> cases h3 : u.owned <;> simp_all
              simp only [this.1, this.2.1, (hclean u hum).2.2.2.2, Bool.or_false, Bool.false_or]
              simp [this.2.2]
            obtain ⟨_, w0, _, hw0, hrep0, hnon0⟩ := hinv.2.2.2.1 u hum hlive
            rw [hw0] at he; cases he
            have hno_u : u.noRc = false := by
              unfold RcVar.isLive at hlive
              rename_i hcond
              cases h1 : u.noRc <;> simp_all
            have hns : ¬u.ty.isScalar := fun hsc => by
              have := (hclean u hum).1.2 hsc; rw [this] at hno_u; cases hno_u
            obtain ⟨bv0, rfl, _⟩ := hnon0 hns
            have hbv_eq : bv0 = newObj.addr := by simpa [Word.toBV64?, Word.i64] using hw
            subst hbv_eq
            have hne0 := beq_iff_eq.mp hev
            obtain ⟨o, ho, hoa⟩ := valRep_even_mem hrep0 hns hne0
            exact hfresh o ho hoa
          · rw [ite_eq_right hev] at hinhs; cases hinhs
  have hnot_ext : (rf.extH ++ ghostH').count newObj.addr = 0 := by
    rw [List.count_eq_zero]
    intro hmem
    rcases List.mem_append.mp hmem with h1 | h2
    · obtain ⟨o, ho, hoa⟩ := hhih newObj.addr (List.mem_append.mpr (Or.inl h1))
      exact hfresh o ho hoa
    · obtain ⟨o, ho, hoa⟩ :=
        hhih newObj.addr (List.mem_append.mpr (Or.inr (hghostSub newObj.addr h2)))
      exact hfresh o ho hoa
  have hrcNewLt : newObj.rc.toNat < 2 ^ 31 - 1 := by rw [hrcNew]; decide
  have hwcAlloc : σ.objs.length + 1 ≤ st'.workCap := by
    have := hres.2.1; omega
  have hhc' : HeapClean rt
      { st := st', objs := newObj :: σ.objs, scr := σ.scr, scrLimbs := scrLimbs' } :=
    heapClean_fresh_alloc hinv.1 hbn' hwfNew hrcNewLt hfresh hwcAlloc hcfClosed
  have hpres : ∀ o ∈ σ.objs, o.Wf →
      ∃ o' ∈ ({
          st := st', objs := newObj :: σ.objs,
          scr := σ.scr, scrLimbs := scrLimbs' } : HState).objs,
        ObjDataEq o o' ∧ o'.rc = o.rc := fun o ho hwo =>
    ⟨o, List.mem_cons_of_mem _ ho, objDataEq_refl o hwo, rfl⟩
  let σ' : HState := { st := st', objs := newObj :: σ.objs, scr := σ.scr, scrLimbs := scrLimbs' }
  have hnpZero : nonPersistRefs σ.objs newObj.addr = 0 := by
    have haux : ∀ (l : List LcnfObj) (acc : Nat),
        (∀ o ∈ l, ∀ f ∈ o.childFields, (f &&& 1#64) = 0#64 → ∃ q ∈ σ.objs, q.addr = f) →
        List.foldl (fun acc p =>
            if p.rc = 0#32 then acc else acc + List.count newObj.addr p.childFields)
          acc l = acc := by
      intro l
      induction l with
      | nil => intro acc _; rfl
      | cons p ps ih =>
        intro acc hcl'
        simp only [List.foldl_cons]
        have hcnt : List.count newObj.addr p.childFields = 0 := by
          rw [List.count_eq_zero]
          intro hm
          obtain ⟨q, hq, hqa⟩ := hcl' p List.mem_cons_self newObj.addr hm hna0
          exact hfresh q hq hqa
        simp only [hcnt, Nat.add_zero, ite_self]
        exact ih acc (fun o ho => hcl' o (List.mem_cons_of_mem _ ho))
    exact haux σ.objs 0 hinv.1.1.2.2.1
  have hhs' : HandlesRcSound
      (varHandles (rf.envH.set x vx.ty (Word.i64 newObj.addr)) vx ++
        localHandles rf.ctx rf.envH ++ rf.extH ++ ghostH') σ'.objs := by
    constructor
    · intro p hp hrc0 f hf hf0
      rcases List.mem_cons.mp hp with rfl | hp'
      · rw [hrcNew] at hrc0; cases hrc0
      · obtain ⟨q, hq, hqa, hqrc⟩ := hinv.2.2.1.1 p hp' hrc0 f hf hf0
        exact ⟨q, List.mem_cons_of_mem _ hq, hqa, hqrc⟩
    · intro y hy hpos
      rw [nonPersistRefs_cons]
      rcases List.mem_cons.mp hy with hyeq | hy'
      · rw [hyeq]
        have hc0 : newObj.childFields.count newObj.addr = 0 := List.count_eq_zero.mpr hnotSelf
        have hvh1 :
            (varHandles (rf.envH.set x vx.ty (Word.i64 newObj.addr)) vx).count newObj.addr = 1 := by
          change (varHandles (rf.envH.set x ty (Word.i64 newObj.addr)) vx).count newObj.addr = 1
          rw [hv1]; simp
        simp only [List.count_append, hvh1, hnot_loc]
        have he0 : (rf.extH).count newObj.addr = 0 ∧ ghostH'.count newObj.addr = 0 := by
          have := hnot_ext; rw [List.count_append] at this; omega
        rw [hnpZero, hc0, hrcNew, he0.1, he0.2]; decide
      · have hprev := hinv.2.2.1.2 y hy' hpos
        have hco := hconsOld y hy' hpos
        have hne_ny : newObj.addr ≠ y.addr := hfresh y hy' |>.symm
        have hvh0 :
            (varHandles (rf.envH.set x vx.ty (Word.i64 newObj.addr)) vx).count y.addr = 0 := by
          change (varHandles (rf.envH.set x ty (Word.i64 newObj.addr)) vx).count y.addr = 0
          rw [hv1]; simp [hne_ny]
        have hrcn : newObj.rc ≠ 0#32 := by rw [hrcNew]; decide
        simp only [hrcn, ↓reduceIte, List.count_append, hvh0] at hprev ⊢
        unfold frameHandles at hprev; simp only [List.count_append] at hprev
        omega
  have hvarX : VarInv vx { ctx := rf.ctx.put vx, envP := rf.envP.set x pv
                           envH := rf.envH.set x vx.ty (Word.i64 newObj.addr),
                           extH := rf.extH, ghostH := ghostH' } σ'.objs := by
    intro _
    refine ⟨pv, Word.i64 newObj.addr, by simp [vx, PValEnv.set],
      by simp [vx, HValEnv.set], hrep, ?_⟩
    intro _
    refine ⟨newObj.addr, rfl, fun h => by simp [vx] at h, fun h => by simp [vx] at h, ?_,
      fun _ _ h => by simp [vx] at h⟩
    intro _
    exact ⟨rfl, rfl, rfl, fun _ => ⟨newObj, List.mem_cons_self, rfl, hrcNew⟩⟩
  have hpermLoc : (localHandles (rf.ctx.put vx) (rf.envH.set x vx.ty (Word.i64 newObj.addr))).Perm
      ([newObj.addr] ++ localHandles rf.ctx rf.envH) := by
    have hp := localHandles_put_perm hinv.2.1 (rf.envH.set x ty (Word.i64 newObj.addr)) vx
    change (localHandles (rf.ctx.put vx) (rf.envH.set x vx.ty (Word.i64 newObj.addr))).Perm
      (varHandles (rf.envH.set x ty (Word.i64 newObj.addr)) vx ++
        localHandlesExcept rf.ctx (rf.envH.set x ty (Word.i64 newObj.addr)) x) at hp
    rw [hv1] at hp
    rw [localHandlesExcept_congr_env (ctx := rf.ctx) (envH := rf.envH)
      (envH' := rf.envH.set x ty (Word.i64 newObj.addr)) x
      (fun y hy => by simp [HValEnv.set, hy])] at hp
    exact hp.trans ((localHandlesExcept_fresh_perm hinv.2.1 hfr).append_left _)
  have hback : ∀ bv, Backed σ.objs (frameHandles rf) bv →
      Backed σ'.objs (frameHandles { ctx := rf.ctx.put vx, envP := rf.envP.set x pv
                                     envH := rf.envH.set x vx.ty (Word.i64 newObj.addr),
                                     extH := rf.extH, ghostH := ghostH' }) bv := by
    intro bv hb
    rcases hb with ⟨o, ho, hoa, hrc0⟩ | ⟨r, hr, hreach⟩
    · exact Or.inl ⟨o, List.mem_cons_of_mem _ ho, hoa, hrc0⟩
    · rcases List.mem_append.mp hr with h1 | h2
      · rcases List.mem_append.mp h1 with hloc | hext
        · have hpres' : ∀ o ∈ σ.objs, o.Wf → True →
              ∃ o' ∈ σ'.objs, o'.addr = o.addr ∧ o'.rc = o.rc ∧ o'.childFields = o.childFields :=
            fun o ho _ _ => ⟨o, List.mem_cons_of_mem _ ho, rfl, rfl, rfl⟩
          have hr' := (nonPersistReach_mono_pred hpres' (fun _ _ _ _ _ _ _ => trivial)
            hinv.1.1.2.1 trivial hreach).1
          have hr_loc' : r ∈ localHandles (rf.ctx.put vx)
              (rf.envH.set x vx.ty (Word.i64 newObj.addr)) := by
            rw [hpermLoc.mem_iff]; exact List.mem_cons_of_mem newObj.addr hloc
          exact Or.inr ⟨r, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hr_loc'))), hr'⟩
        · exact backed_mono_roots
            (fun z hz => by
              rcases List.mem_append.mp hz with hze | hzg
              · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hze)))
              · exact List.mem_append.mpr (Or.inr hzg))
            (hbackExt bv (Or.inr ⟨r, List.mem_append.mpr (Or.inl hext), hreach⟩))
      · exact backed_mono_roots
          (fun z hz => by
            rcases List.mem_append.mp hz with hze | hzg
            · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hze)))
            · exact List.mem_append.mpr (Or.inr hzg))
          (hbackExt bv (Or.inr ⟨r, List.mem_append.mpr (Or.inr h2), hreach⟩))
  have hsh : SharedPredInv { ctx := rf.ctx.put vx, envP := rf.envP.set x pv
                             envH := rf.envH.set x vx.ty (Word.i64 newObj.addr),
                             extH := rf.extH, ghostH := ghostH' } σ'.objs := by
    let rfNew : RcFrame :=
      { ctx := rf.ctx.put vx, envP := rf.envP.set x pv,
        envH := rf.envH.set x vx.ty (Word.i64 newObj.addr),
        extH := rf.extH, ghostH := ghostH' }
    intro p hp vb' vx' hg1 hg2 hbl hno hps
    have hsp : p ∈ rf.ctx.sharedPreds := by simpa [RcCtx.put] using hp
    have ha := hfr
    simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at ha
    have hpx := ha.1.2 p hsp
    have hg1' : rf.ctx.get? p.1 = some vb' := by
      have he := RcCtx.put_get? hinv.2.1 vx p.1
      rw [show vx.id = x from rfl, beq_false_of_ne hpx.1] at he; exact he.symm.trans hg1
    have hg2' : rf.ctx.get? p.2 = some vx' := by
      have he := RcCtx.put_get? hinv.2.1 vx p.2
      rw [show vx.id = x from rfl, beq_false_of_ne hpx.2] at he; exact he.symm.trans hg2
    have hep : rfNew.envP p.1 = rf.envP p.1 := by simp [rfNew, PValEnv.set, hpx.1]
    have heh : rfNew.envH p.2 = rf.envH p.2 := by simp [rfNew, HValEnv.set, hpx.2]
    have hotherH : ∀ y, y ≠ x → rfNew.envH y = rf.envH y := fun y hy => by
      simp [rfNew, HValEnv.set, hy]
    obtain ⟨h0, h1⟩ := hinv.2.2.2.2 p hsp vb' vx' hg1' hg2' hbl hno hps
    constructor
    · intro hp0
      obtain ⟨bv, hev, hb0, hpos⟩ := h0 (hep ▸ hp0)
      refine ⟨bv, heh.trans hev, hb0, fun hown => ?_⟩
      obtain ⟨hz, o, ho, hoa, hrc⟩ := hpos hown
      have hposO : 0 < o.rc.toInt := rc_toInt_pos_of_ne_zero (hinv.1.1.2.1 o ho).2.2.1
        (fun h0z => by rw [h0z] at hrc; simp at hrc; omega)
      have hco := hconsOld o ho hposO
      rw [hoa] at hco
      have hcf0 : newObj.childFields.count bv = 0 := by
        simp only [List.count_append] at hz; omega
      have hgh0 : ghostH'.count bv = 0 := by
        simp only [List.count_append] at hz; omega
      have hne_nb : newObj.addr ≠ bv := by
        have := hfresh o ho; rw [hoa] at this; exact this.symm
      obtain ⟨hm2, hid2⟩ := RcCtx.get?_mem hg2'
      have hndNew := rf.ctx.put_nodup hinv.2.1 vx
      have hm2' : vx' ∈ (rf.ctx.put vx).vars :=
        (RcCtx.put_mem_iff hinv.2.1).mpr (Or.inr ⟨hm2, by rw [hid2]; exact hpx.2⟩)
      have hcntPerm := localHandles_perm_filter hndNew rfNew.envH vx' hm2'
      have hv_eq : varHandles rfNew.envH vx' = varHandles rf.envH vx' :=
        varHandles_subset_eq (hotherH vx'.id (hid2 ▸ hpx.2)).symm
      have hvh_new_0 : ([newObj.addr]).count bv = 0 := by simp [hne_nb]
      have hcntEq : (localHandlesExcept rfNew.ctx rfNew.envH p.2).count bv =
          (localHandlesExcept rf.ctx rf.envH p.2).count bv := by
        have hA := hcntPerm.count_eq bv
        have hB := (localHandles_perm_filter hinv.2.1 rf.envH vx' hm2).count_eq bv
        have hC := hpermLoc.count_eq bv
        rw [List.count_append, hid2] at hA hB
        change (localHandles (rf.ctx.put vx) rfNew.envH).count bv =
          (varHandles rfNew.envH vx').count bv +
            (localHandlesExcept (rf.ctx.put vx) rfNew.envH p.2).count bv at hA
        rw [hv_eq] at hA
        change (localHandles (rf.ctx.put vx) rfNew.envH).count bv = _ at hC
        rw [List.count_append, hvh_new_0, Nat.zero_add] at hC
        change (localHandles (rf.ctx.put vx) rfNew.envH).count bv =
          (varHandles rf.envH vx').count bv +
            (localHandlesExcept rfNew.ctx rfNew.envH p.2).count bv at hA
        omega
      have hnpNew : nonPersistRefs (newObj :: σ.objs) bv = 0 := by
        rw [nonPersistRefs_cons]
        have hrcn : newObj.rc ≠ 0#32 := by rw [hrcNew]; decide
        simp only [hrcn, ↓reduceIte]
        simp only [List.count_append] at hz
        omega
      refine ⟨?_, o, List.mem_cons_of_mem _ ho, hoa, hrc⟩
      simp only [List.count_append] at hz ⊢
      rw [hnpNew, hcntEq]; omega
    · intro hp1 hown
      obtain ⟨bv, hev, hb0, o, ho, hoa, hrc⟩ := h1 (hep ▸ hp1) hown
      exact ⟨bv, heh.trans hev, hb0, o, List.mem_cons_of_mem _ ho, hoa, hrc⟩
  have hmain := rcInv_put_fresh hinv hclean hfr rfl hcv hhc' hpres hvarX hhs' hback hbackExt hsh
  rw [hvx_eq]
  refine ⟨hmain.1, hmain.2, ?_,
    resStateInv_fresh_alloc hres hbytes hwr hrcNew hrem' hwc', hpres, hbackExt⟩
  intro a ha
  rcases List.mem_append.mp ha with h1 | h2
  · obtain ⟨o, ho, hoa⟩ := hhih a (List.mem_append.mpr (Or.inl h1))
    exact ⟨o, List.mem_cons_of_mem _ ho, hoa⟩
  · obtain ⟨o, ho, hoa⟩ := hhih a (List.mem_append.mpr (Or.inr (hghostSub a h2)))
    exact ⟨o, List.mem_cons_of_mem _ ho, hoa⟩

end
