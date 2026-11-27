module

public import LeanQbe.T.LeanLCNF.Sem.PerceusMut1
import LeanQbe.T.Logic.ProofKit

/-!
# LCNF Perceus-Sound Simulation: `oset` Step

Invariant preservation and stepwise simulation lemma for `LcCode.oset`, bridging pure
`PVal.setObj` and Tier-H object-field updates (`o.fields.set i newF`) while maintaining
RC soundness and `ghostH` backing for evicted even child pointers.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

section OsetStep

private def consumeArgHandles (rf : RcFrame) : LcArg → List (BitVec 64)
  | .erased => []
  | .var yid => consumeVarHandles rf yid 1

private theorem oset_obj_eval {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv}
    (hinv : RcInv rt rf σ) (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    {y : LcArg} (hy_init : argScalarInit sm y = true)
    (hy_ok : ∀ yid, y = .var yid →
      ∃ vy, rf.ctx.get? yid = some vy ∧ vy.isLive = true ∧ vy.ty.isScalar = false)
    {py : PVal} (hpy : ρP.evalArg y = some py) :
    ∃ newF, (rf.envH.evalArgAt y .tobject).bind Word.toBV64? = some newF ∧
      ObjRep py newF σ.objs ∧
      (y = .erased → newF = 1#64 ∧ py = .erased) ∧
      (∀ yid vy, y = .var yid → rf.ctx.get? yid = some vy →
        rf.envH yid = some (vy.ty, .i64 newF) ∧ rf.envP yid = some py) := by
  cases y with
  | erased =>
    simp only [PValEnv.evalArg] at hpy; cases hpy
    exact ⟨1#64, rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun _ _ h => (by cases h)⟩
  | var yid =>
    obtain ⟨vy, hgy, hly, hvy_ns⟩ := hy_ok yid rfl
    have ⟨hvy_m, hyid⟩ := RcCtx.get?_mem hgy
    have hy_shd := hshd vy hvy_m hly
    simp only [argScalarInit] at hy_init
    simp only [hyid, hy_init, ite_true] at hy_shd
    simp only [PValEnv.evalArg] at hpy
    have hE_y : rf.envP yid = some py := hy_shd ▸ hpy
    obtain ⟨_, wy, hpy0, hwy0, hrep_y, _⟩ := hinv.2.2.2.1 vy hvy_m hly
    rw [hyid, hE_y] at hpy0; cases hpy0
    have hnonsc : ¬vy.ty.isScalar = true := by simp [hvy_ns]
    simp only [ValRep, hnonsc] at hrep_y
    obtain ⟨newF, hwy_eq, hobj_y, _⟩ := hrep_y
    have hwy' : rf.envH yid = some (vy.ty, .i64 newF) := hyid ▸ hwy_eq ▸ hwy0
    have hev : (rf.envH.evalArgAt (.var yid) .tobject).bind Word.toBV64? = some newF := by
      simp [HValEnv.evalArgAt, hwy', Word.i64, LcTy.toTTy]
      rfl
    have hvar : ∀ yid' vy', LcArg.var yid = .var yid' → rf.ctx.get? yid' = some vy' →
        rf.envH yid' = some (vy'.ty, .i64 newF) ∧ rf.envP yid' = some py := by
      intro yid' vy' h1 h2
      cases h1; simp only [hgy, Option.some.injEq] at h2; cases h2
      exact ⟨hwy', hE_y⟩
    exact ⟨newF, hev, hobj_y, (fun h => by cases h), hvar⟩

private theorem oset_consume_step {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    {y : LcArg} {ctx1 : RcCtx} (hcons : rf.ctx.consumeArg y = .ok ctx1)
    {newF : BitVec 64}
    (hy_ok : (y = .erased → newF = 1#64) ∧
      (∀ yid, y = .var yid → ∃ vy, rf.ctx.get? yid = some vy ∧ vy.isLive = true ∧
        vy.ty.isScalar = false ∧ rf.envH yid = some (vy.ty, .i64 newF) ∧
        (rf.ctx.sharedPreds.all (·.2 != yid)) = true)) :
    let consH := consumeArgHandles rf y
    (localHandles rf.ctx rf.envH).Perm (localHandles ctx1 rf.envH ++ consH) ∧
    (∀ s, (y = .erased ∨ y ≠ .var s) →
      (localHandlesExcept rf.ctx rf.envH s).Perm (localHandlesExcept ctx1 rf.envH s ++ consH)) ∧
    RcInv rt { rf with ctx := ctx1 } σ ∧ CleanVars ctx1 ∧ ParentsOwned ctx1 ∧
    (∀ u ∈ ctx1.vars, ∃ w0, rf.ctx.get? u.id = some w0 ∧ w0.ty = u.ty ∧
      (u.isLive = true → w0.isLive = true ∧ (u.borrowed = true → w0.borrowed = true))) ∧
    (∀ v0 yid, y = .var yid → rf.ctx.get? yid = some v0 → ∀ vx', ctx1.get? yid = some vx' →
      vx'.owned = if v0.noRc || v0.persistent || 1 == 0 then v0.owned else v0.owned - 1) := by
  intro consH
  have hnodup := hinv.2.1
  cases y with
  | erased =>
    simp only [RcCtx.consumeArg, pure, Except.pure, Except.ok.injEq] at hcons
    subst hcons
    refine ⟨by simp [consH, consumeArgHandles], fun _ _ => by simp [consH, consumeArgHandles],
      hinv, hclean, hpo, fun u hu => ?_, fun _ _ h => by cases h⟩
    have hgu := rcCtx_get?_of_mem hnodup hu
    exact ⟨u, hgu, rfl, fun hl => ⟨hl, id⟩⟩
  | var yid =>
    obtain ⟨vy, hgy, _, _, _, hsp_y⟩ := hy_ok.2 yid rfl
    have hsh_sub : ∀ p ∈ rf.ctx.sharedPreds, p.2 = yid →
        ∀ v0, rf.ctx.get? yid = some v0 →
          v0.noRc = true ∨ v0.persistent = true ∨ 1 = 0 ∨ v0.owned ≤ 1 := by
      intro p hp heq
      have hf := List.all_eq_true.mp hsp_y p hp
      simp [heq] at hf
    have hstep := rcInv_consumeVar_step hinv hclean hpo hcons hsh_sub
    obtain ⟨hperm_lh, hperm_ex, hinv1, hclean1, hpo1, hown⟩ := hstep
    have hnd1 := consumeVar_nodup hnodup hcons
    refine ⟨hperm_lh, fun s hs => hperm_ex s (by
      rcases hs with h | h
      · cases h
      · intro heq; apply h; rw [heq]), hinv1, hclean1, hpo1, fun u hu => ?_, ?_⟩
    · have hgu := rcCtx_get?_of_mem hnd1 hu
      by_cases hul : u.isLive = true
      · obtain ⟨w0, hw0, hw0_l, _, _, hw0_ty, _, hw0_bor, _⟩ :=
          consumeVar_get?_live_back hnodup hclean hcons u.id hgu hul
        exact ⟨w0, hw0, hw0_ty, fun _ => ⟨hw0_l, fun hb => (hw0_bor hb).1⟩⟩
      · have hflg := consumeVar_preserves_flags hnodup hcons u.id
        rw [hgu] at hflg
        cases hg0 : rf.ctx.get? u.id with
        | none => rw [hg0] at hflg; cases hflg
        | some w0 =>
          rw [hg0] at hflg
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hflg
          exact ⟨w0, rfl, hflg.2.2.symm, fun hl => absurd hl hul⟩
    · intro v0 yid' heq hv0 vx' hvx'
      cases heq; exact hown v0 hv0 vx' hvx'

private theorem oset_handlesRcSound {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (_hclean : CleanVars rf.ctx)
    {idx i : Nat} (hidx : idx < σ.objs.length)
    (horc1 : σ.objs[idx].rc = 1#32) (hotle : σ.objs[idx].tag ≤ 244)
    (hi : i < σ.objs[idx].fields.length)
    {y : LcArg} {ctx1 : RcCtx} (hcons : rf.ctx.consumeArg y = .ok ctx1)
    {newF : BitVec 64}
    (hperm_lh : (localHandles rf.ctx rf.envH).Perm
      (localHandles ctx1 rf.envH ++ consumeArgHandles rf y))
    (hy_ok : (y = .erased → newF = 1#64) ∧
      (∀ yid, y = .var yid → ∃ vy, rf.ctx.get? yid = some vy ∧ vy.isLive = true ∧
        vy.ty.isScalar = false ∧ rf.envH yid = some (vy.ty, .i64 newF))) :
    let o := σ.objs[idx]
    let oldF := o.fields[i]
    let o' := { o with fields := o.fields.set i newF }
    let σ' : HState := { σ with objs := σ.objs.set idx o' }
    let ghostH' := if oldF &&& 1#64 == 0#64 then oldF :: rf.ghostH else rf.ghostH
    let rf' : RcFrame :=
      { ctx := ctx1, envP := rf.envP, envH := rf.envH, extH := rf.extH, ghostH := ghostH' }
    (∀ a, nonPersistRefs σ'.objs a + (if a = oldF then 1 else 0) =
      nonPersistRefs σ.objs a + (if a = newF then 1 else 0)) ∧
    HandlesRcSound (frameHandles rf') σ'.objs := by
  intro o oldF o' σ' ghostH' rf'
  obtain ⟨hheap, _, hsound, hvars, _⟩ := hinv
  have hwf_all := hheap.1.2.1
  have hnodup_objs := hheap.2
  have hnpre : ∀ a, nonPersistRefs σ'.objs a + (if a = oldF then 1 else 0) =
      nonPersistRefs σ.objs a + (if a = newF then 1 else 0) := by
    intro a
    have hch : o'.childFields = o.childFields.set i newF := by
      simp [o', o, LcnfObj.childFields, hotle]
    have hi_ch : i < o.childFields.length := by simp [o, LcnfObj.childFields, hotle, hi]
    have hold_ch : o.childFields[i]'hi_ch = oldF := by simp [oldF, o, LcnfObj.childFields, hotle]
    have hrc_nz : o.rc ≠ 0#32 := by rw [horc1]; decide
    have hrc'_nz : o'.rc ≠ 0#32 := by simp [o', hrc_nz]
    exact nonPersistRefs_set_obj_fields hidx o' hrc_nz hrc'_nz oldF newF hch hi_ch hold_ch a
  refine ⟨hnpre, ?_⟩
  refine ⟨?_, ?_⟩
  · intro p hp hp0 f hf hevf
    dsimp only [σ'] at hp; rw [list_mem_set_iff hidx] at hp
    rcases hp with rfl | ⟨j, hj, _, rfl⟩
    · simp only [o', o, horc1] at hp0; cases hp0
    · obtain ⟨q, hq, hqa, hq0⟩ := hsound.1 _ (List.getElem_mem hj) hp0 f hf hevf
      have hqne : q.addr ≠ σ.objs[idx].addr := by
        intro h
        have heq := obj_eq_of_addr_nodup hnodup_objs hq (List.getElem_mem hidx) h
        rw [heq, horc1] at hq0; cases hq0
      obtain ⟨k, hk, hgetk⟩ := obj_mem_idx hq
      have hkne : k ≠ idx := fun h => by subst h; exact hqne (congrArg LcnfObj.addr hgetk).symm
      exact ⟨q, (list_mem_set_iff hidx).mpr (Or.inr ⟨k, hk, hkne, hgetk⟩), hqa, hq0⟩
  · intro q hq hqpos
    have hq_ev : q.addr &&& 1#64 = 0#64 := by
      dsimp only [σ'] at hq; rw [list_mem_set_iff hidx] at hq
      rcases hq with rfl | ⟨j, hj, _, rfl⟩
      · exact obj_addr_and1_zero
          (lcnfObj_wf_set_fields (hwf_all _ (List.getElem_mem hidx)) hotle hi newF)
      · exact obj_addr_and1_zero (hwf_all _ (List.getElem_mem hj))
    have hbase :
        nonPersistRefs σ.objs q.addr + List.count q.addr (frameHandles rf) ≤ q.rc.toNat := by
      dsimp only [σ'] at hq; rw [list_mem_set_iff hidx] at hq
      rcases hq with rfl | ⟨j, hj, _, rfl⟩
      · have hb := hsound.2 _ (List.getElem_mem hidx) (by
          simp only [o', o] at hqpos; exact hqpos)
        simpa [o', o] using hb
      · exact hsound.2 _ (List.getElem_mem hj) hqpos
    have hc_gh : List.count q.addr ghostH' =
        List.count q.addr rf.ghostH + (if q.addr = oldF then 1 else 0) := by
      dsimp only [ghostH']
      by_cases hev_old : (oldF &&& 1#64 == 0#64) = true
      · simp only [hev_old, ite_true, List.count_cons]
        by_cases hqo : q.addr = oldF
        · simp [hqo]
        · simp [hqo, beq_false_of_ne (fun h => hqo h.symm)]
      · simp only [hev_old]
        by_cases hqo : q.addr = oldF
        · have hbe : (oldF &&& 1#64 == 0#64) = true := beq_iff_eq.mpr (hqo ▸ hq_ev)
          rw [hbe] at hev_old; exact absurd rfl hev_old
        · simp [hqo]
    have hc_cons : (if q.addr = newF then 1 else 0) ≤
        List.count q.addr (consumeArgHandles rf y) ∨ q.rc = 0#32 := by
      by_cases hqn : q.addr = newF
      · cases y with
        | erased =>
          rw [hqn, hy_ok.1 rfl] at hq_ev; cases hq_ev
        | var yid =>
          obtain ⟨vy, hgy, hly, hvy_ns, hwy⟩ := hy_ok.2 yid rfl
          have ⟨hvy_m, hyid⟩ := RcCtx.get?_mem hgy
          have ⟨_, _, _, hwu, _, hnon⟩ := hvars vy hvy_m hly
          obtain ⟨bv0, hwb0, hno_r, hpers_r, _⟩ := hnon (by simp [hvy_ns])
          have heq0 : newF = bv0 := by
            have h := (hyid ▸ hwy).symm.trans (hwb0 ▸ hwu); cases h; rfl
          by_cases hno_y : vy.noRc = true
          · exfalso; rw [hqn, heq0] at hq_ev; exact absurd hq_ev (hno_r hno_y)
          have hnoy_f : vy.noRc = false := by cases h : vy.noRc <;> simp_all
          by_cases hpers_y : vy.persistent = true
          · right
            obtain ⟨q0, hq0, hqa0, hqrc0⟩ := hpers_r hpers_y (heq0 ▸ hqn ▸ hq_ev)
            dsimp only [σ'] at hq; rw [list_mem_set_iff hidx] at hq
            rcases hq with rfl | ⟨j, hj, _, rfl⟩
            · have heq := obj_eq_of_addr_nodup hnodup_objs hq0 (List.getElem_mem hidx)
                (hqa0.trans (heq0.symm.trans hqn.symm))
              simp only [o', o] at hqpos
              rw [heq, horc1] at hqrc0; cases hqrc0
            · have heq := obj_eq_of_addr_nodup hnodup_objs hq0 (List.getElem_mem hj)
                (hqa0.trans (heq0.symm.trans hqn.symm))
              rw [← heq]; exact hqrc0
          · left
            have hpersy_f : vy.persistent = false := by cases h : vy.persistent <;> simp_all
            have hown_pos : vy.owned ≠ 0 := by
              intro h0
              unfold RcCtx.consumeArg RcCtx.consumeVar at hcons
              simp [hgy, hnoy_f, hpersy_f, h0] at hcons
            have hev_n : newF &&& 1#64 = 0#64 := hqn ▸ hq_ev
            have hc1 : consumeVarHandles rf yid 1 = [newF] := by
              unfold consumeVarHandles
              simp only [hgy, hnoy_f, hpersy_f, Bool.or_false]
              rw [hwy]
              simp [Word.i64, Word.toBV64?, hev_n]
            simp [consumeArgHandles, hc1, hqn]
      · left; simp [hqn]
    have hcnt_lh := hperm_lh.count_eq q.addr
    have hn := hnpre q.addr
    dsimp only [rf'] at hcnt_lh ⊢
    simp only [frameHandles, List.count_append] at hbase hcnt_lh hc_cons ⊢
    rw [hc_gh]
    rcases hc_cons with hle_c | hq0
    · omega
    · rw [hq0] at hqpos; cases hqpos

/-- Lift `Backed` across `oset` when evicted even child `oldF` is tracked in `r2`. -/
private theorem oset_backed_mono {objs objs' : List LcnfObj} {idx i : Nat}
    (hidx : idx < objs.length) {o' : LcnfObj} {newF oldF : BitVec 64}
    (ho'a : o'.addr = objs[idx].addr) (ho'rc : o'.rc = objs[idx].rc)
    (hotle : objs[idx].tag ≤ 244) (hi : i < objs[idx].fields.length)
    (hold : objs[idx].fields[i] = oldF)
    (ho'ch : o'.childFields = objs[idx].childFields.set i newF)
    (ho'_mem : o' ∈ objs')
    (hpres : ∀ q ∈ objs, q.addr ≠ objs[idx].addr → q ∈ objs')
    (hnodup : (objs.map LcnfObj.addr).Nodup) (hnodup' : (objs'.map LcnfObj.addr).Nodup)
    {r1 r2 : List (BitVec 64)} (hrsub : ∀ r ∈ r1, r ∈ r2)
    (hold_sub : oldF &&& 1#64 = 0#64 → oldF ∈ r2)
    {a : BitVec 64} (hb : Backed objs r1 a) : Backed objs' r2 a := by
  have hlift : ∀ {b}, (∃ t ∈ objs, t.addr = b ∧ t.rc ≠ 0#32) →
      ∃ t' ∈ objs', t'.addr = b ∧ t'.rc ≠ 0#32 := by
    intro b ⟨t, ht, hta, htnz⟩
    by_cases htd : t.addr = objs[idx].addr
    · have heq := obj_eq_of_addr_nodup hnodup ht (List.getElem_mem hidx) htd
      exact ⟨o', ho'_mem, ho'a.trans (heq ▸ hta), by rw [ho'rc, ← heq]; exact htnz⟩
    · exact ⟨t, hpres t ht htd, hta, htnz⟩
  rcases hb with ⟨q, hq, hqa, hqrc0⟩ | ⟨r, hr, hreach⟩
  · by_cases hqd : q.addr = objs[idx].addr
    · have heq := obj_eq_of_addr_nodup hnodup hq (List.getElem_mem hidx) hqd
      exact Or.inl ⟨o', ho'_mem, ho'a.trans (heq ▸ hqa), ho'rc.trans (heq ▸ hqrc0)⟩
    · exact Or.inl ⟨q, hpres q hq hqd, hqa, hqrc0⟩
  · induction hreach with
    | refl hq0 => exact Or.inr ⟨r, hrsub r hr, NonPersistReach.refl (hlift hq0)⟩
    | @step _ v hprev hmem hcev hcnz ih =>
      rcases hmem with ⟨q, hq, hqb, hcf⟩
      rcases ih with ⟨o_b, ho_b, hob_a, hob_rc0⟩ | ⟨r', hr', hreach_b⟩
      · exfalso
        obtain ⟨ob', hob', hob'a, hob'nz⟩ := hlift (nonPersistReach_target_nz hprev)
        have hoe := obj_eq_of_addr_nodup hnodup' ho_b hob' (hob_a.trans hob'a.symm)
        rw [hoe] at hob_rc0; exact hob'nz hob_rc0
      · have hcnz' := hlift hcnz
        by_cases hqd : q.addr = objs[idx].addr
        · have heq := obj_eq_of_addr_nodup hnodup hq (List.getElem_mem hidx) hqd
          have hqcf : objs[idx].childFields = objs[idx].fields := by
            simp [LcnfObj.childFields, hotle]
          have hmem_f : v ∈ objs[idx].fields := by rw [← hqcf, ← heq]; exact hcf
          obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp hmem_f
          by_cases hki : k = i
          · subst hki
            have hce_old : v = oldF := hgetk.symm.trans hold
            exact Or.inr ⟨oldF, hold_sub (hce_old ▸ hcev),
              by rw [← hce_old]; exact NonPersistReach.refl hcnz'⟩
          · have hsetk : (objs[idx].fields.set i newF)[k]'(by simp [hk]) =
                objs[idx].fields[k] := by
              rw [List.getElem_set_ne (Ne.symm hki)]
            have hcf' : v ∈ o'.childFields := by
              rw [ho'ch, hqcf, ← hgetk, ← hsetk]
              exact List.getElem_mem (by simp [hk])
            exact Or.inr ⟨r', hr', NonPersistReach.step hreach_b
              ⟨o', ho'_mem, ho'a.trans (heq ▸ hqb), hcf'⟩ hcev hcnz'⟩
        · exact Or.inr ⟨r', hr', NonPersistReach.step hreach_b
            ⟨q, hpres q hq hqd, hqb, hcf⟩ hcev hcnz'⟩

private theorem oset_not_live_of_consume_self {rf : RcFrame} {x : Nat} {vx : RcVar}
    (hnodup : (rf.ctx.vars.map RcVar.id).Nodup)
    (hgx : rf.ctx.get? x = some vx) (hno : vx.noRc = false) (hpers : vx.persistent = false)
    (hown1 : vx.owned = 1) (hvbor : vx.borrowed = false)
    {ctx1 : RcCtx} (hcons : rf.ctx.consumeArg (.var x) = .ok ctx1)
    (hclean1 : CleanVars ctx1)
    (hback : ∀ u ∈ ctx1.vars, ∃ w0, rf.ctx.get? u.id = some w0 ∧ w0.ty = u.ty ∧
      (u.isLive = true → w0.isLive = true ∧ (u.borrowed = true → w0.borrowed = true)))
    (hown_y : ∀ v0, rf.ctx.get? x = some v0 → ∀ vx', ctx1.get? x = some vx' →
      vx'.owned = if v0.noRc || v0.persistent || 1 == 0 then v0.owned else v0.owned - 1)
    {u : RcVar} (hu : u ∈ ctx1.vars) (hux : u.id = x) (hul : u.isLive = true) : False := by
  have hnd1 := consumeVar_nodup hnodup hcons
  have hgu := rcCtx_get?_of_mem hnd1 hu
  have hown0 := hown_y vx hgx u (hux ▸ hgu)
  simp [hno, hpers, hown1] at hown0
  obtain ⟨w0, hw0, _, hw0_lb⟩ := hback u hu
  have hw0_eq : w0 = vx := by have h := hw0; rw [hux, hgx] at h; cases h; rfl
  have hubor : u.borrowed = false := by
    cases hbu : u.borrowed
    · rfl
    · have hb := (hw0_lb hul).2 hbu; rw [hw0_eq, hvbor] at hb; cases hb
  have hflg := consumeVar_preserves_flags hnodup hcons u.id
  rw [hgu, hux, hgx] at hflg
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hflg
  have hno_u : u.noRc = false := hflg.1.trans hno
  have hpers_u : u.persistent = false := hflg.2.1.trans hpers
  simp [RcVar.isLive, hno_u, hpers_u, hown0, hubor, (hclean1 u hu).2.2.2.2] at hul

private theorem oset_hvars_step {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx)
    {x i cidx : Nat} {vx : RcVar} (hgx : rf.ctx.get? x = some vx)
    (hno : vx.noRc = false) (hpers : vx.persistent = false)
    (hown1 : vx.owned = 1) (hvbor : vx.borrowed = false)
    (hvx_ns : vx.ty.isScalar = false) (hvx_nt : vx.ty ≠ .tagged)
    {addr : BitVec 64} (henvh_v : rf.envH vx.id = some (vx.ty, .i64 addr))
    (hev : addr &&& 1#64 = 0#64) {idx : Nat} (hidx : idx < σ.objs.length)
    (haddr : σ.objs[idx].addr = addr) (horc1 : σ.objs[idx].rc = 1#32)
    (hotle : σ.objs[idx].tag ≤ 244) (hotag : σ.objs[idx].tag = cidx)
    (hi : i < σ.objs[idx].fields.length) (hnot_self : ¬addr ∈ σ.objs[idx].childFields)
    (hchild_ne : ∀ q ∈ σ.objs, q.Wf → q.addr ≠ addr →
      ∀ f ∈ q.childFields, f &&& 1#64 = 0#64 → f ≠ addr)
    (hlive_ne : ∀ u ∈ rf.ctx.vars, u.id ≠ vx.id → u.isLive = true →
      (!decide (u.ty.isScalar = true)) = true →
      ∀ bvu, rf.envH u.id = some (u.ty, .i64 bvu) → bvu ≠ addr)
    {fs : List PVal} {hscal : List UInt8}
    (hosc : σ.objs[idx].scalarData = hscal)
    (hof : objFieldsRep fs σ.objs[idx].fields σ.objs)
    {y : LcArg} {ctx1 : RcCtx} (hcons : rf.ctx.consumeArg y = .ok ctx1)
    {py : PVal} {newF : BitVec 64} (hobj_y : ObjRep py newF σ.objs)
    (hy_ok : (y = .erased → newF = 1#64 ∧ py = .erased) ∧
      (∀ yid, y = .var yid → ∃ vy, rf.ctx.get? yid = some vy ∧ vy.isLive = true ∧
        vy.ty.isScalar = false ∧ rf.envH yid = some (vy.ty, .i64 newF) ∧
        (rf.ctx.sharedPreds.all (·.2 != yid)) = true))
    (hinv1 : RcInv rt { rf with ctx := ctx1 } σ) (hclean1 : CleanVars ctx1)
    (hback1 : ∀ u ∈ ctx1.vars, ∃ w0, rf.ctx.get? u.id = some w0 ∧ w0.ty = u.ty ∧
      (u.isLive = true → w0.isLive = true ∧ (u.borrowed = true → w0.borrowed = true)))
    (hown_y : ∀ v0 yid, y = .var yid → rf.ctx.get? yid = some v0 → ∀ vx', ctx1.get? yid = some vx' →
      vx'.owned = if v0.noRc || v0.persistent || 1 == 0 then v0.owned else v0.owned - 1) :
    let o := σ.objs[idx]
    let oldF := o.fields[i]
    let o' := { o with fields := o.fields.set i newF }
    let σ' : HState := { σ with objs := σ.objs.set idx o' }
    let ghostH' := if oldF &&& 1#64 == 0#64 then oldF :: rf.ghostH else rf.ghostH
    let rf' : RcFrame :=
      { ctx := ctx1, envP := rf.envP.set x (.ctor cidx (fs.set i py) hscal),
        envH := rf.envH, extH := rf.extH, ghostH := ghostH' }
    (σ'.objs.map LcnfObj.addr).Nodup →
    (∀ q ∈ σ.objs, q.addr ≠ addr → q ∈ σ'.objs) →
    ∀ u ∈ ctx1.vars, VarInv u rf' σ'.objs := by
  intro o oldF o' σ' ghostH' rf' hnodup_objs' hq_mem' u hu hulive
  have hnodup := hinv.2.1
  have hnodup_objs := hinv.1.2
  have hnd1 := hinv1.2.1
  have hxid : vx.id = x := (RcCtx.get?_mem hgx).2
  have hcf_o : o.childFields = o.fields := by simp [o, LcnfObj.childFields, hotle]
  have ho'w : o'.Wf := lcnfObj_wf_set_fields (hinv.1.1.2.1 _ (List.getElem_mem hidx)) hotle hi newF
  have ho'ch : o'.childFields = σ.objs[idx].childFields.set i newF := by
    simp [o', o, LcnfObj.childFields, hotle]
  have hpres_p : ∀ q ∈ σ.objs, q.Wf → q.addr ≠ addr → ∃ q' ∈ σ'.objs, ObjDataEq q q' :=
    fun q hq hqwf hqne => ⟨q, hq_mem' q hq hqne, objDataEq_refl q hqwf⟩
  have hgh_sub : ∀ a, a ∈ rf.ghostH → a ∈ ghostH' := by
    intro a ha; dsimp only [ghostH']; split <;> simp [ha]
  have hold_sub_gh : oldF &&& 1#64 = 0#64 → oldF ∈ rf'.extH ++ rf'.ghostH := fun hev_o =>
    List.mem_append.mpr (Or.inr (by simp [rf', ghostH', beq_iff_eq.mpr hev_o]))
  have hold_sub_fh : oldF &&& 1#64 = 0#64 → oldF ∈ frameHandles rf' := fun hev_o =>
    List.mem_append.mpr (Or.inr (by simp [rf', ghostH', beq_iff_eq.mpr hev_o]))
  by_cases hux : u.id = x
  · have hy_nex : y = .erased ∨ ∃ yid, y = .var yid ∧ yid ≠ x := by
      cases y with
      | erased => exact Or.inl rfl
      | var yid =>
        by_cases hyx : yid = x
        · subst hyx
          exact absurd (oset_not_live_of_consume_self hnodup hgx hno hpers hown1 hvbor
            hcons hclean1 hback1 (fun v0 hv0 vx' hvx' => hown_y v0 yid rfl hv0 vx' hvx')
            hu hux hulive) False.elim
        · exact Or.inr ⟨yid, rfl, hyx⟩
    have hgu := rcCtx_get?_of_mem hnd1 hu
    have hback_x : u.noRc = false ∧ u.persistent = false ∧ u.ty = vx.ty ∧
        u.owned = 1 ∧ u.borrowed = false := by
      rcases hy_nex with rfl | ⟨yid, rfl, hyx⟩
      · simp [RcCtx.consumeArg, pure, Except.pure] at hcons; subst hcons
        have heq : u = vx := by have h := hgu.symm.trans (hux.symm ▸ hgx); cases h; rfl
        exact ⟨heq ▸ hno, heq ▸ hpers, heq ▸ rfl, heq ▸ hown1, heq ▸ hvbor⟩
      · obtain ⟨w0, hw0, _, hw0_no, hw0_ps, hw0_ty, hw0_le, hw0_bor, _⟩ :=
          consumeVar_get?_live_back hnodup hclean hcons u.id hgu hulive
        have hw0_eq : w0 = vx := by have h := (hux ▸ hw0).symm.trans hgx; cases h; rfl
        have hubor : u.borrowed = false := by
          cases hbu : u.borrowed
          · rfl
          · have hb := (hw0_bor hbu).1; rw [hw0_eq, hvbor] at hb; cases hb
        have hu_no : u.noRc = false := hw0_no.symm.trans (hw0_eq ▸ hno)
        have hu_ps : u.persistent = false := hw0_ps.symm.trans (hw0_eq ▸ hpers)
        have hu_rt : u.resetTok = false := (hclean1 u hu).2.2.2.2
        have hu_pos : 0 < u.owned := by
          simp only [RcVar.isLive, hu_no, hu_ps, hubor, hu_rt, Bool.or_false,
            Bool.false_or] at hulive
          exact decide_eq_true_eq.mp hulive
        have hu_le : u.owned ≤ 1 := Nat.le_trans hw0_le (hw0_eq ▸ hown1 ▸ Nat.le_refl 1)
        exact ⟨hu_no, hu_ps, hw0_ty.symm.trans (hw0_eq ▸ rfl), by omega, hubor⟩
    obtain ⟨hu_no, hu_ps, hu_ty, hu_own, hu_bor⟩ := hback_x
    have hnewF_ne : newF &&& 1#64 = 0#64 → newF ≠ addr := by
      intro hev_y
      rcases hy_nex with rfl | ⟨yid, rfl, hyx⟩
      · rw [(hy_ok.1 rfl).1] at hev_y; cases hev_y
      · obtain ⟨vy, hgy, hly, hvy_ns, hwy, _⟩ := hy_ok.2 yid rfl
        have ⟨hvy_m, hyid⟩ := RcCtx.get?_mem hgy
        have hnsb : !vy.ty.isScalar = true := by simp [hvy_ns]
        exact hlive_ne vy hvy_m (fun h => hyx (hyid.symm.trans (h.trans hxid))) hly hnsb
          newF (hyid ▸ hwy)
    have hrep_x : ValRep u.ty (.ctor cidx (fs.set i py) hscal) (.i64 addr) σ'.objs := by
      have hnonsc : ¬vx.ty.isScalar = true := by simp [hvx_ns]
      have hne_fs : ¬(fs.set i py = [] ∧ hscal = []) := by
        intro ⟨h0, _⟩
        have hl := congrArg List.length h0
        simp only [List.length_set, List.length_nil] at hl
        have := objFieldsRep_length hof; omega
      have hof' : objFieldsRep (fs.set i py) (o.fields.set i newF) σ'.objs := by
        apply objFieldsRep_set
        · refine objFieldsRep_mono_pred (P := fun a => a ≠ addr) hpres_p hchild_ne hof ?_
          intro f hf _ heq; apply hnot_self; rw [hcf_o]; exact heq ▸ hf
        · exact objRep_mono_pred (P := fun a => a ≠ addr) hpres_p hchild_ne py newF hobj_y hnewF_ne
      rw [hu_ty]; simp only [ValRep, hnonsc]
      exact ⟨addr, rfl, Or.inr ⟨hne_fs, o', (list_mem_set_iff hidx).mpr (Or.inl rfl),
        haddr, ho'w, hotag, hotle, hosc, hof'⟩, fun _ => hev, fun ht => absurd ht hvx_nt⟩
    refine ⟨.ctor cidx (fs.set i py) hscal, .i64 addr,
      by simp [rf', PValEnv.set, hux],
      by rw [hu_ty, hux, ← hxid]; exact henvh_v, hrep_x, fun _ => ?_⟩
    exact ⟨addr, rfl, (fun h => by rw [hu_no] at h; cases h),
      (fun h => by rw [hu_ps] at h; cases h),
      (fun _ => ⟨hu_no, hu_ps, hu_own, fun _ =>
        ⟨o', (list_mem_set_iff hidx).mpr (Or.inl rfl), haddr, horc1⟩⟩),
      (fun _ _ hb => by rw [hu_bor] at hb; cases hb)⟩
  · obtain ⟨pu, wu, hp, hh, hrep, hnon⟩ := hinv1.2.2.2.1 u hu hulive
    obtain ⟨w0, hw0, hw0_ty, hw0_lb⟩ := hback1 u hu
    have hw0_id : w0.id = u.id := (RcCtx.get?_mem hw0).2
    have hne_fn : ∀ {bvu : BitVec 64}, ¬u.ty.isScalar = true → wu = Word.i64 bvu → bvu ≠ addr :=
      fun hns hwu => hlive_ne w0 (RcCtx.get?_mem hw0).1 (fun h => hux (hw0_id ▸ h.trans hxid))
        (hw0_lb hulive).1 (by rw [hw0_ty]; cases h : u.ty.isScalar <;> simp_all)
        _ (hw0_id ▸ hw0_ty ▸ hwu ▸ hh)
    have hrep_u : ValRep u.ty pu wu σ'.objs := by
      refine valRep_mono_pred (P := fun a => a ≠ addr) hpres_p hchild_ne hrep ?_
      intro hns bvu hwu _; exact hne_fn hns hwu
    refine ⟨pu, wu, by simp [rf', PValEnv.set, hux]; exact hp, hh, hrep_u, fun hns => ?_⟩
    obtain ⟨bvu, hwu, hno_u, hpers_u, hex_u, hbor_u⟩ := hnon hns
    have hne_bv : bvu ≠ addr := hne_fn hns hwu
    refine ⟨bvu, hwu, hno_u, fun hp hev_u => ?_, ?_, ?_⟩
    · obtain ⟨o_u, ho_u, ho_ua, ho_urc⟩ := hpers_u hp hev_u
      exact ⟨o_u, hq_mem' o_u ho_u (ho_ua.symm ▸ hne_bv), ho_ua, ho_urc⟩
    · intro hexu
      obtain ⟨hx1, hx2, hx3, hxo⟩ := hex_u hexu
      refine ⟨hx1, hx2, hx3, fun hevu => ?_⟩
      obtain ⟨o_u, ho_u, ho_ua, ho_urc⟩ := hxo hevu
      exact ⟨o_u, hq_mem' o_u ho_u (ho_ua.symm ▸ hne_bv), ho_ua, ho_urc⟩
    · intro hno' hpers' hbor' hevu
      obtain ⟨hbk1, hbk2⟩ := hbor_u hno' hpers' hbor' hevu
      refine ⟨oset_backed_mono (o' := o') (newF := newF) hidx rfl rfl hotle hi rfl ho'ch
        ((list_mem_set_iff hidx).mpr (Or.inl rfl))
        (fun q hq hne => hq_mem' q hq (haddr ▸ hne)) hnodup_objs hnodup_objs'
        (fun r hr => by
          simp only [frameHandles, List.mem_append] at hr ⊢
          rcases hr with (hr1 | hr2) | hr3
          · exact Or.inl (Or.inl hr1)
          · exact Or.inl (Or.inr hr2)
          · exact Or.inr (hgh_sub r hr3))
        hold_sub_fh hbk1, ?_⟩
      cases hpar : u.parent? with
      | none =>
        rw [hpar] at hbk2; dsimp only at hbk2
        exact oset_backed_mono (o' := o') (newF := newF) hidx rfl rfl hotle hi rfl ho'ch
          ((list_mem_set_iff hidx).mpr (Or.inl rfl))
          (fun q hq hne => hq_mem' q hq (haddr ▸ hne)) hnodup_objs hnodup_objs'
          (fun r hr => by
            simp only [List.mem_append] at hr ⊢
            rcases hr with h1 | h2
            · exact Or.inl h1
            · exact Or.inr (hgh_sub r h2))
          hold_sub_gh hbk2
      | some p =>
        rw [hpar] at hbk2; dsimp only at hbk2
        obtain ⟨pv, hpv_m, hpv_id, hpv_no, hpv_ps, hpv_pos, hpv_bk⟩ := hbk2
        refine ⟨pv, hpv_m, hpv_id, hpv_no, hpv_ps, hpv_pos, ?_⟩
        exact oset_backed_mono (o' := o') (newF := newF) hidx rfl rfl hotle hi rfl ho'ch
          ((list_mem_set_iff hidx).mpr (Or.inl rfl))
          (fun q hq hne => hq_mem' q hq (haddr ▸ hne)) hnodup_objs hnodup_objs'
          (fun r hr => by
            simp only [List.mem_append] at hr ⊢
            rcases hr with h1 | h2 | h3
            · exact Or.inl h1
            · exact Or.inr (Or.inl h2)
            · exact Or.inr (Or.inr (hgh_sub r h3)))
          (fun hev_o => List.mem_append.mpr (Or.inr (hold_sub_gh hev_o))) hpv_bk

private theorem oset_hsp_step {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx)
    {x i cidx : Nat} {vx : RcVar} (hgx : rf.ctx.get? x = some vx) (hno : vx.noRc = false)
    {addr : BitVec 64} {idx : Nat} (hidx : idx < σ.objs.length)
    (haddr : σ.objs[idx].addr = addr) (horc1 : σ.objs[idx].rc = 1#32)
    (hotle : σ.objs[idx].tag ≤ 244) (hi : i < σ.objs[idx].fields.length)
    {fs : List PVal} {hscal : List UInt8}
    {y : LcArg} {ctx1 : RcCtx} (hcons : rf.ctx.consumeArg y = .ok ctx1)
    {py : PVal} {newF : BitVec 64}
    (hy_ok : (y = .erased → newF = 1#64 ∧ py = .erased) ∧
      (∀ yid, y = .var yid → ∃ vy, rf.ctx.get? yid = some vy ∧ vy.isLive = true ∧
        vy.ty.isScalar = false ∧ rf.envH yid = some (vy.ty, .i64 newF) ∧
        (rf.ctx.sharedPreds.all (·.2 != yid)) = true))
    (hinv1 : RcInv rt { rf with ctx := ctx1 } σ) (hsbv1 : SharedBoolVars ctx1)
    (hperm_ex : ∀ s, (y = .erased ∨ y ≠ .var s) →
      (localHandlesExcept rf.ctx rf.envH s).Perm
        (localHandlesExcept ctx1 rf.envH s ++ consumeArgHandles rf y))
    (hnpre : ∀ a,
      nonPersistRefs (σ.objs.set idx { σ.objs[idx] with
          fields := σ.objs[idx].fields.set i newF }) a +
        (if a = σ.objs[idx].fields[i] then 1 else 0) =
      nonPersistRefs σ.objs a + (if a = newF then 1 else 0)) :
    let o := σ.objs[idx]
    let oldF := o.fields[i]
    let o' := { o with fields := o.fields.set i newF }
    let σ' : HState := { σ with objs := σ.objs.set idx o' }
    let ghostH' := if oldF &&& 1#64 == 0#64 then oldF :: rf.ghostH else rf.ghostH
    let rf' : RcFrame :=
      { ctx := ctx1, envP := rf.envP.set x (.ctor cidx (fs.set i py) hscal),
        envH := rf.envH, extH := rf.extH, ghostH := ghostH' }
    (∀ q ∈ σ.objs, q.addr ≠ addr → q ∈ σ'.objs) → SharedPredInv rf' σ'.objs := by
  intro o oldF o' σ' ghostH' rf' hq_mem' p hp vb vs hgb hgs hblive hsno hspers
  have hnodup := hinv.2.1
  have hnodup_objs := hinv.1.2
  have hcf_o : o.childFields = o.fields := by simp [o, LcnfObj.childFields, hotle]
  have hpx1 : p.1 ≠ x := by
    intro heq
    have hvb_no : vb.noRc = true := hsbv1 p hp vb hgb
    cases y with
    | erased =>
      simp [RcCtx.consumeArg, pure, Except.pure] at hcons; subst hcons
      have h := hgb; rw [heq, hgx] at h; cases h; rw [hno] at hvb_no; cases hvb_no
    | var _ =>
      have h1 := consumeVar_preserves_flags hnodup hcons p.1
      rw [hgb, heq, hgx] at h1
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
      rw [hno] at h1; rw [h1.1] at hvb_no; cases hvb_no
  have hny_p2 : y = .erased ∨ y ≠ .var p.2 := by
    cases y with
    | erased => exact Or.inl rfl
    | var yid =>
      right; intro heq; cases heq
      have hp0 := consumeVar_sharedPreds_sub hcons p hp
      obtain ⟨vy, _, _, _, _, hsp_y⟩ := hy_ok.2 p.2 rfl
      have hf := List.all_eq_true.mp hsp_y p hp0
      simp at hf
  have hsp_old := hinv1.2.2.2.2 p hp vb vs hgb hgs hblive hsno hspers
  have htag_eq : (rf'.envP p.1).bind PVal.tag? = (rf.envP p.1).bind PVal.tag? := by
    simp [rf', PValEnv.set, hpx1]
  rw [htag_eq]
  have h_diff_refs : ∀ bvs, rf.envH p.2 = some (vs.ty, .i64 bvs) → bvs &&& 1#64 = 0#64 →
      nonPersistRefs σ.objs bvs +
        (localHandlesExcept ctx1 rf.envH p.2 ++ rf.extH ++ rf.ghostH).count bvs = 0 →
      (∃ o_s ∈ σ.objs, o_s.addr = bvs ∧ o_s.rc.toNat = vs.owned) → 0 < vs.owned →
      nonPersistRefs σ'.objs bvs +
        (localHandlesExcept ctx1 rf.envH p.2 ++ rf.extH ++ ghostH').count bvs = 0 := by
    intro bvs henvs hevs hc0 ⟨o_s, ho_s, ho_sa, ho_src⟩ hspos
    have hc0_np : nonPersistRefs σ.objs bvs = 0 := by omega
    have hne_old : bvs ≠ oldF := fun heq => by
      have hpos := nonPersistRefs_pos_of_mem_cf (a := oldF) (List.getElem_mem hidx)
        (by rw [horc1]; decide) (by rw [hcf_o]; exact List.getElem_mem hi)
      rw [← heq] at hpos; omega
    have hne_new : bvs ≠ newF := by
      intro heq
      cases y with
      | erased => rw [(hy_ok.1 rfl).1] at heq; rw [heq] at hevs; cases hevs
      | var yid =>
        obtain ⟨vy, hgy, hly, hvy_ns, hwy, _⟩ := hy_ok.2 yid rfl
        by_cases hnoy : vy.noRc = true
        · obtain ⟨_, _, _, hwu0, _, hnon_y⟩ := hinv.2.2.2.1 vy (RcCtx.get?_mem hgy).1 hly
          obtain ⟨bvy, hwy0, hno_r, _⟩ := hnon_y (by simp [hvy_ns])
          have hbvy : bvy = newF := by
            have h := ((RcCtx.get?_mem hgy).2 ▸ hwy).symm.trans (hwy0 ▸ hwu0); cases h; rfl
          exact absurd (hbvy ▸ heq ▸ hevs) (hno_r hnoy)
        · by_cases hpersy : vy.persistent = true
          · obtain ⟨_, _, _, hwu0, _, hnon_y⟩ := hinv.2.2.2.1 vy (RcCtx.get?_mem hgy).1 hly
            obtain ⟨bvy, hwy0, _, hpers_r, _⟩ := hnon_y (by simp [hvy_ns])
            have hbvy : bvy = newF := by
              have h := ((RcCtx.get?_mem hgy).2 ▸ hwy).symm.trans (hwy0 ▸ hwu0); cases h; rfl
            obtain ⟨qy, hqy, hqya, hqy0⟩ := hpers_r hpersy (hbvy ▸ heq ▸ hevs)
            have hoeq := obj_eq_of_addr_nodup hnodup_objs ho_s hqy
              (ho_sa.trans (heq.trans (hbvy ▸ hqya.symm)))
            rw [hoeq, hqy0] at ho_src; simp at ho_src; omega
          · have hny_p : yid ≠ p.2 := fun h => by
              rcases hny_p2 with h' | h'
              · cases h'
              · exact h' (congrArg LcArg.var h)
            have hnoy_f : vy.noRc = false := by cases h : vy.noRc <;> simp_all
            have hpersy_f : vy.persistent = false := by cases h : vy.persistent <;> simp_all
            have hown_pos : vy.owned ≠ 0 := by
              intro h0
              unfold RcCtx.consumeArg RcCtx.consumeVar at hcons
              simp [hgy, hnoy_f, hpersy_f, h0] at hcons
            have hny_p_id : vy.id ≠ p.2 := by rw [(RcCtx.get?_mem hgy).2]; exact hny_p
            have hvy_rt := (hclean vy (RcCtx.get?_mem hgy).1).2.2.2.2
            have hv_in : vy ∈ rf.ctx.vars.filter (·.id != p.2) :=
              List.mem_filter.mpr ⟨(RcCtx.get?_mem hgy).1, bne_iff_ne.mpr hny_p_id⟩
            have hsub : (varHandles rf.envH vy).Sublist
                (localHandlesExcept rf.ctx rf.envH p.2) := by
              simp only [localHandlesExcept]
              exact List.sublist_flatten_of_mem (List.mem_map.mpr ⟨vy, hv_in, rfl⟩)
            have hev_n : newF &&& 1#64 = 0#64 := heq ▸ hevs
            have hown_b : (vy.owned == 0) = false := beq_false_of_ne hown_pos
            have hvh : newF ∈ varHandles rf.envH vy := by
              simp only [varHandles, hnoy_f, hpersy_f, hvy_rt, hown_b, Bool.or_self,
                (RcCtx.get?_mem hgy).2 ▸ hwy, Word.i64, Word.toBV64?, hev_n]
              simp only [beq_self_eq_true, ↓reduceIte]
              exact List.mem_replicate.mpr ⟨hown_pos, rfl⟩
            have hcnt_pos : 1 ≤ (localHandlesExcept rf.ctx rf.envH p.2).count bvs :=
              Nat.le_trans (List.count_pos_iff.mpr (heq ▸ hvh)) (hsub.count_le bvs)
            have hlive_s : vs.isLive = true := by simp [RcVar.isLive, hspos]
            obtain ⟨w0, hw0, _, hw0_no, hw0_ps, _, hw0_le, _⟩ :=
              consumeVar_get?_live_back hnodup hclean hcons p.2 hgs hlive_s
            have hw0_no' : w0.noRc = false := hw0_no.trans hsno
            have hw0_ps' : w0.persistent = false := hw0_ps.trans hspers
            have hw0_rt := (hclean w0 (RcCtx.get?_mem hw0).1).2.2.2.2
            have hw0_own_b : (w0.owned == 0) = false := beq_false_of_ne (by omega)
            have hw0_id : w0.id = p.2 := (RcCtx.get?_mem hw0).2
            have hvw0 : (varHandles rf.envH w0).count bvs = w0.owned := by
              simp only [varHandles, hw0_no', hw0_ps', hw0_rt, hw0_own_b, Bool.or_self,
                hw0_id ▸ henvs, Word.i64, Word.toBV64?, hevs]
              simp
            have hlh := localHandles_count_eq_add hnodup rf.envH (RcCtx.get?_mem hw0).1 bvs
            rw [hw0_id, hvw0] at hlh
            have hrc_pos : 0 < o_s.rc.toInt :=
              rc_toInt_pos_of_ne_zero (hinv.1.1.2.1 o_s ho_s).2.2.1
                (fun h => by rw [h] at ho_src; simp at ho_src; omega)
            have hbd := hinv.2.2.1.2 o_s ho_s hrc_pos
            simp only [frameHandles, List.count_append, ho_sa] at hbd
            omega
    have hnp' := hnpre bvs
    change nonPersistRefs σ'.objs bvs + (if bvs = oldF then 1 else 0) =
      nonPersistRefs σ.objs bvs + (if bvs = newF then 1 else 0) at hnp'
    simp only [hne_old, hne_new, ite_false] at hnp'
    have hgh' : ghostH'.count bvs = rf.ghostH.count bvs := by
      dsimp only [ghostH']; split
      · simp [List.count_cons, beq_false_of_ne (Ne.symm hne_old)]
      · rfl
    simp only [List.count_append] at hc0 ⊢; rw [hgh']; omega
  refine ⟨fun htag => ?_, fun htag hspos => ?_⟩
  · obtain ⟨bvs, henvs, hevs, hrest⟩ := hsp_old.1 htag
    refine ⟨bvs, henvs, hevs, fun hspos => ?_⟩
    obtain ⟨hc0, o_s, ho_s, ho_sa, ho_src⟩ := hrest hspos
    refine ⟨h_diff_refs bvs henvs hevs hc0 ⟨o_s, ho_s, ho_sa, ho_src⟩ hspos, ?_⟩
    by_cases hsbv_addr : bvs = addr
    · refine ⟨o', (list_mem_set_iff hidx).mpr (Or.inl rfl), haddr.trans hsbv_addr.symm, ?_⟩
      have heqo := obj_eq_of_addr_nodup hnodup_objs ho_s (List.getElem_mem hidx)
        (ho_sa.trans (hsbv_addr.trans haddr.symm))
      rw [heqo] at ho_src; exact ho_src
    · exact ⟨o_s, hq_mem' o_s ho_s (ho_sa.symm ▸ hsbv_addr), ho_sa, ho_src⟩
  · obtain ⟨bvs, henvs, hevs, o_s, ho_s, ho_sa, horc⟩ := hsp_old.2 htag hspos
    refine ⟨bvs, henvs, hevs, ?_⟩
    by_cases hsbv_addr : bvs = addr
    · refine ⟨o', (list_mem_set_iff hidx).mpr (Or.inl rfl), haddr.trans hsbv_addr.symm, ?_⟩
      have heqo := obj_eq_of_addr_nodup hnodup_objs ho_s (List.getElem_mem hidx)
        (ho_sa.trans (hsbv_addr.trans haddr.symm))
      rw [heqo] at horc; exact horc
    · exact ⟨o_s, hq_mem' o_s ho_s (ho_sa.symm ▸ hsbv_addr), ho_sa, horc⟩

private theorem oset_lift_nz {objs objs' : List LcnfObj} {idx : Nat}
    (hidx : idx < objs.length) {o' : LcnfObj} (ho'a : o'.addr = objs[idx].addr)
    (ho'rc : o'.rc = objs[idx].rc) (ho'_mem : o' ∈ objs')
    (hq_mem' : ∀ q ∈ objs, q.addr ≠ objs[idx].addr → q ∈ objs')
    (hnodup : (objs.map LcnfObj.addr).Nodup) {v : BitVec 64}
    (h : ∃ t ∈ objs, t.addr = v ∧ t.rc ≠ 0#32) :
    ∃ t' ∈ objs', t'.addr = v ∧ t'.rc ≠ 0#32 := by
  obtain ⟨t, ht, hta, htnz⟩ := h
  by_cases htd : t.addr = objs[idx].addr
  · have heq := obj_eq_of_addr_nodup hnodup ht (List.getElem_mem hidx) htd
    exact ⟨o', ho'_mem, ho'a.trans (heq ▸ hta), by rw [ho'rc, ← heq]; exact htnz⟩
  · exact ⟨t, hq_mem' t ht htd, hta, htnz⟩

private theorem oset_reach_extend {objs objs' : List LcnfObj} {idx i : Nat}
    {newF : BitVec 64}
    (hidx : idx < objs.length) {o' : LcnfObj} (ho'a : o'.addr = objs[idx].addr)
    (ho'rc : o'.rc = objs[idx].rc) (hotle : objs[idx].tag ≤ 244)
    (hi : i < objs[idx].fields.length)
    (ho'ch : o'.childFields = objs[idx].childFields.set i newF)
    (ho'_mem : o' ∈ objs') (hq_mem' : ∀ q ∈ objs, q.addr ≠ objs[idx].addr → q ∈ objs')
    (hnodup : (objs.map LcnfObj.addr).Nodup)
    (hclosed : lcnfHeapClosed objs)
    {r_gh : List (BitVec 64)}
    (hold_sub : objs[idx].fields[i] &&& 1#64 = 0#64 → objs[idx].fields[i] ∈ r_gh)
    {r b : BitVec 64} (hr : r ∈ r_gh) {o_cur : LcnfObj} (hcur : o_cur ∈ objs)
    (hrr : NonPersistReach objs' r o_cur.addr)
    (hbcf : b ∈ o_cur.childFields) (hbev : b &&& 1#64 = 0#64) :
    Backed objs' r_gh b := by
  have hcf_o : objs[idx].childFields = objs[idx].fields := by simp [LcnfObj.childFields, hotle]
  obtain ⟨t, ht, hta⟩ := hclosed o_cur hcur b hbcf hbev
  by_cases htrc0 : t.rc = 0#32
  · by_cases htd : t.addr = objs[idx].addr
    · have heq := obj_eq_of_addr_nodup hnodup ht (List.getElem_mem hidx) htd
      exact Or.inl ⟨o', ho'_mem, ho'a.trans (heq ▸ hta), by rw [ho'rc, ← heq]; exact htrc0⟩
    · exact Or.inl ⟨t, hq_mem' t ht htd, hta, htrc0⟩
  · have htnz' := oset_lift_nz hidx ho'a ho'rc ho'_mem hq_mem' hnodup ⟨t, ht, hta, htrc0⟩
    by_cases hcd : o_cur.addr = objs[idx].addr
    · have heq := obj_eq_of_addr_nodup hnodup hcur (List.getElem_mem hidx) hcd
      have hbf : b ∈ objs[idx].fields := by rw [← hcf_o, ← heq]; exact hbcf
      obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp hbf
      by_cases hki : k = i
      · subst hki
        exact Or.inr ⟨objs[idx].fields[k], hold_sub (hgetk ▸ hbev),
          by rw [hgetk]; exact NonPersistReach.refl htnz'⟩
      · have hsetk : (objs[idx].fields.set i newF)[k]'(by simp [hk]) = objs[idx].fields[k] := by
          rw [List.getElem_set_ne (Ne.symm hki)]
        have hbcf' : b ∈ o'.childFields := by
          rw [ho'ch, hcf_o, ← hgetk, ← hsetk]; exact List.getElem_mem (by simp [hk])
        exact Or.inr ⟨r, hr, NonPersistReach.step hrr
          ⟨o', ho'_mem, ho'a.trans hcd.symm, hbcf'⟩ hbev htnz'⟩
    · exact Or.inr ⟨r, hr, NonPersistReach.step hrr
        ⟨o_cur, hq_mem' o_cur hcur hcd, rfl, hbcf⟩ hbev htnz'⟩

private theorem oset_reach_child_step {objs objs' : List LcnfObj} {idx i : Nat}
    {newF : BitVec 64}
    (hidx : idx < objs.length) {o' : LcnfObj} (ho'a : o'.addr = objs[idx].addr)
    (ho'rc : o'.rc = objs[idx].rc) (hotle : objs[idx].tag ≤ 244)
    (hi : i < objs[idx].fields.length)
    (ho'ch : o'.childFields = objs[idx].childFields.set i newF)
    (ho'_mem : o' ∈ objs') (hq_mem' : ∀ q ∈ objs, q.addr ≠ objs[idx].addr → q ∈ objs')
    (hnodup : (objs.map LcnfObj.addr).Nodup) (hnodup' : (objs'.map LcnfObj.addr).Nodup)
    (hclosed : lcnfHeapClosed objs)
    {r_gh : List (BitVec 64)}
    (hold_sub : objs[idx].fields[i] &&& 1#64 = 0#64 → objs[idx].fields[i] ∈ r_gh)
    {s u : BitVec 64} (hreach : NonPersistReach objs s u) :
    ∀ {o_mid : LcnfObj}, o_mid ∈ objs → o_mid.addr = u → ∀ {bvu : BitVec 64},
      bvu ∈ o_mid.childFields → bvu &&& 1#64 = 0#64 →
      Backed objs' r_gh bvu ∨
        ∃ o_mid' ∈ objs', o_mid'.addr = u ∧ NonPersistReach objs' s u ∧
          bvu ∈ o_mid'.childFields := by
  have hcf_o : objs[idx].childFields = objs[idx].fields := by simp [LcnfObj.childFields, hotle]
  induction hreach with
  | refl h1 =>
    intro o_mid hom_m hom_a bvu hbcf hbev
    obtain ⟨t, ht, hta, htnz⟩ := h1
    have htnz' := oset_lift_nz hidx ho'a ho'rc ho'_mem hq_mem' hnodup ⟨t, ht, hta, htnz⟩
    by_cases hmd : o_mid.addr = objs[idx].addr
    · have heq := obj_eq_of_addr_nodup hnodup hom_m (List.getElem_mem hidx) hmd
      have hbf : bvu ∈ objs[idx].fields := by rw [← hcf_o, ← heq]; exact hbcf
      obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp hbf
      by_cases hki : k = i
      · subst hki
        obtain ⟨tb, htb, htba⟩ := hclosed o_mid hom_m bvu hbcf hbev
        by_cases htb0 : tb.rc = 0#32
        · by_cases hbd : tb.addr = objs[idx].addr
          · have heqb := obj_eq_of_addr_nodup hnodup htb (List.getElem_mem hidx) hbd
            exact Or.inl (Or.inl ⟨o', ho'_mem, ho'a.trans (heqb ▸ htba),
              by rw [ho'rc, ← heqb]; exact htb0⟩)
          · exact Or.inl (Or.inl ⟨tb, hq_mem' tb htb hbd, htba, htb0⟩)
        · have htbnz' := oset_lift_nz hidx ho'a ho'rc ho'_mem hq_mem' hnodup ⟨tb, htb, htba, htb0⟩
          exact Or.inl (Or.inr ⟨objs[idx].fields[k], hold_sub (hgetk ▸ hbev),
            by rw [hgetk]; exact NonPersistReach.refl htbnz'⟩)
      · have hsetk : (objs[idx].fields.set i newF)[k]'(by simp [hk]) = objs[idx].fields[k] := by
          rw [List.getElem_set_ne (Ne.symm hki)]
        have hbcf' : bvu ∈ o'.childFields := by
          rw [ho'ch, hcf_o, ← hgetk, ← hsetk]; exact List.getElem_mem (by simp [hk])
        exact Or.inr ⟨o', ho'_mem, ho'a.trans (hmd.symm.trans hom_a),
          NonPersistReach.refl htnz', hbcf'⟩
    · exact Or.inr ⟨o_mid, hq_mem' o_mid hom_m hmd, hom_a, NonPersistReach.refl htnz', hbcf⟩
  | @step u_r v_r hprev hch hev hnz ih =>
    intro o_mid hom_m hom_a bvu hbcf hbev
    obtain ⟨oq, hoq, hoqa, hqcf⟩ := hch
    rcases ih hoq hoqa hqcf hev with hbk | ⟨oq', hoq', hoq'a, hreach', hqcf'⟩
    · rcases hbk with ⟨q0, hq0, hq0a, hq0rc⟩ | ⟨r, hr, hrr⟩
      · exfalso
        obtain ⟨t', ht', ht'a, ht'nz⟩ := oset_lift_nz hidx ho'a ho'rc ho'_mem hq_mem' hnodup hnz
        have heq := obj_eq_of_addr_nodup hnodup' hq0 ht' (hq0a.trans ht'a.symm)
        rw [heq] at hq0rc; exact ht'nz hq0rc
      · exact Or.inl (oset_reach_extend hidx ho'a ho'rc hotle hi ho'ch ho'_mem hq_mem' hnodup
          hclosed hold_sub hr hom_m (hom_a ▸ hrr) hbcf hbev)
    · have hvnz' := oset_lift_nz hidx ho'a ho'rc ho'_mem hq_mem' hnodup hnz
      have hreach_v : NonPersistReach objs' s v_r :=
        NonPersistReach.step hreach' ⟨oq', hoq', hoq'a, hqcf'⟩ hev hvnz'
      by_cases hmd : o_mid.addr = objs[idx].addr
      · have heq := obj_eq_of_addr_nodup hnodup hom_m (List.getElem_mem hidx) hmd
        have hbf : bvu ∈ objs[idx].fields := by rw [← hcf_o, ← heq]; exact hbcf
        obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp hbf
        by_cases hki : k = i
        · subst hki
          obtain ⟨tb, htb, htba⟩ := hclosed o_mid hom_m bvu hbcf hbev
          by_cases htb0 : tb.rc = 0#32
          · by_cases hbd : tb.addr = objs[idx].addr
            · have heqb := obj_eq_of_addr_nodup hnodup htb (List.getElem_mem hidx) hbd
              exact Or.inl (Or.inl ⟨o', ho'_mem, ho'a.trans (heqb ▸ htba),
                by rw [ho'rc, ← heqb]; exact htb0⟩)
            · exact Or.inl (Or.inl ⟨tb, hq_mem' tb htb hbd, htba, htb0⟩)
          · have htbnz' := oset_lift_nz hidx ho'a ho'rc ho'_mem hq_mem' hnodup
              ⟨tb, htb, htba, htb0⟩
            exact Or.inl (Or.inr ⟨objs[idx].fields[k], hold_sub (hgetk ▸ hbev),
              by rw [hgetk]; exact NonPersistReach.refl htbnz'⟩)
        · have hsetk : (objs[idx].fields.set i newF)[k]'(by simp [hk]) = objs[idx].fields[k] := by
            rw [List.getElem_set_ne (Ne.symm hki)]
          have hbcf' : bvu ∈ o'.childFields := by
            rw [ho'ch, hcf_o, ← hgetk, ← hsetk]; exact List.getElem_mem (by simp [hk])
          exact Or.inr ⟨o', ho'_mem, ho'a.trans (hmd.symm.trans hom_a), hreach_v, hbcf'⟩
      · exact Or.inr ⟨o_mid, hq_mem' o_mid hom_m hmd, hom_a, hreach_v, hbcf⟩

private theorem oset_hpcb_step {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ)
    {x i cidx : Nat} {vx : RcVar} (hgx : rf.ctx.get? x = some vx)
    (hvbor : vx.borrowed = false)
    {addr : BitVec 64} (henvh_v : rf.envH vx.id = some (vx.ty, .i64 addr))
    {idx : Nat} (hidx : idx < σ.objs.length)
    (haddr : σ.objs[idx].addr = addr) (hotle : σ.objs[idx].tag ≤ 244)
    (hi : i < σ.objs[idx].fields.length) (_hnot_self : ¬addr ∈ σ.objs[idx].childFields)
    (hlive_ne : ∀ u ∈ rf.ctx.vars, u.id ≠ vx.id → u.isLive = true →
      (!decide (u.ty.isScalar = true)) = true →
      ∀ bvu, rf.envH u.id = some (u.ty, .i64 bvu) → bvu ≠ addr)
    {fs : List PVal} {hscal : List UInt8} {ctx1 : RcCtx}
    {py : PVal} {newF : BitVec 64}
    (hinv1 : RcInv rt { rf with ctx := ctx1 } σ) (hclean1 : CleanVars ctx1)
    (hpo1 : ParentsOwned ctx1) (hpcb1 : ParentChildBacked { rf with ctx := ctx1 } σ.objs)
    (hback1 : ∀ u ∈ ctx1.vars, ∃ w0, rf.ctx.get? u.id = some w0 ∧ w0.ty = u.ty ∧
      (u.isLive = true → w0.isLive = true ∧ (u.borrowed = true → w0.borrowed = true))) :
    let o := σ.objs[idx]
    let oldF := o.fields[i]
    let o' := { o with fields := o.fields.set i newF }
    let σ' : HState := { σ with objs := σ.objs.set idx o' }
    let ghostH' := if oldF &&& 1#64 == 0#64 then oldF :: rf.ghostH else rf.ghostH
    let rf' : RcFrame :=
      { ctx := ctx1, envP := rf.envP.set x (.ctor cidx (fs.set i py) hscal),
        envH := rf.envH, extH := rf.extH, ghostH := ghostH' }
    (σ'.objs.map LcnfObj.addr).Nodup →
    (∀ q ∈ σ.objs, q.addr ≠ addr → q ∈ σ'.objs) →
    ParentChildBacked rf' σ'.objs := by
  intro o oldF o' σ' ghostH' rf' hnodup_objs' hq_mem'
  have hclosed := hinv.1.1.2.2.1
  have hnodup_objs := hinv.1.2
  have hxid := (RcCtx.get?_mem hgx).2
  have hcf_o : o.childFields = o.fields := by simp [o, LcnfObj.childFields, hotle]
  have ho'ch : o'.childFields = σ.objs[idx].childFields.set i newF := by
    simp [o', o, LcnfObj.childFields, hotle]
  have hgh_sub : ∀ a, a ∈ rf.ghostH → a ∈ ghostH' := by
    intro a ha; dsimp only [ghostH']; split <;> simp [ha]
  have hold_sub_gh : oldF &&& 1#64 = 0#64 → oldF ∈ rf'.extH ++ rf'.ghostH := fun hev_o =>
    List.mem_append.mpr (Or.inr (by simp [rf', ghostH', beq_iff_eq.mpr hev_o]))
  intro u hu hulive huno hupers hubor q hpar bvu henvu hevu
  have hux : u.id ≠ vx.id := by
    intro heq
    obtain ⟨w0, hw0, _, hw0_lb⟩ := hback1 u hu
    have hw0_eq : w0 = vx := by have h := hw0; rw [heq, hxid, hgx] at h; cases h; rfl
    have hb := (hw0_lb hulive).2 hubor; rw [hw0_eq, hvbor] at hb; cases hb
  obtain ⟨w0, hw0, hw0_ty, hw0_lb⟩ := hback1 u hu
  have hw0_id : w0.id = u.id := (RcCtx.get?_mem hw0).2
  have hns_u := not_isScalar_of_check (hclean1 u hu) huno
  have hnsb : !w0.ty.isScalar = true := by
    rw [hw0_ty]; cases h : u.ty.isScalar <;> simp_all
  have hne_u : bvu ≠ addr := hlive_ne w0 (RcCtx.get?_mem hw0).1
    (fun h => hux (hw0_id ▸ h)) (hw0_lb hulive).1 hnsb bvu (hw0_id ▸ hw0_ty ▸ henvu)
  rcases hpcb1 u hu hulive huno hupers hubor q hpar bvu henvu hevu with hext | hch
  · exact Or.inl (oset_backed_mono (o' := o') (newF := newF) hidx rfl rfl hotle hi rfl ho'ch
      ((list_mem_set_iff hidx).mpr (Or.inl rfl))
      (fun q hq hne => hq_mem' q hq (haddr ▸ hne)) hnodup_objs hnodup_objs'
      (fun r hr => by
        simp only [List.mem_append] at hr ⊢
        rcases hr with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (hgh_sub r h2))
      hold_sub_gh hext)
  · obtain ⟨wp, o_q, hwp, hqaddr, ho_q, o_mid, hom_m, hreach_mid, hcf⟩ := hch
    obtain ⟨pv, hpv_m, hpv_id, hpv_no, hpv_ps, hpv_pos, _⟩ := hpo1 u hu q hpar
    have hlive_pv : pv.isLive = true := by simp [RcVar.isLive, hpv_pos]
    have hns_pv := not_isScalar_of_check (hclean1 pv hpv_m) hpv_no
    obtain ⟨_, wu0, _, hwu0, _, hnon0⟩ := hinv1.2.2.2.1 pv hpv_m hlive_pv
    obtain ⟨bvp, hwp0, _⟩ := hnon0 hns_pv
    have hwu0' : rf.envH pv.id = some (pv.ty, Word.i64 bvp) := hwp0 ▸ hwu0
    have hwp_eq : wp = (pv.ty, Word.i64 bvp) := by
      have h := hwu0'; rw [hpv_id, hwp] at h; cases h; rfl
    have hq_bv : o_q.addr = bvp := by
      have h := hqaddr; rw [hwp_eq] at h
      change some bvp = some o_q.addr at h
      exact (Option.some.inj h).symm
    rcases oset_reach_child_step (o' := o') (newF := newF) hidx rfl rfl hotle hi ho'ch
        ((list_mem_set_iff hidx).mpr (Or.inl rfl))
        (fun q hq hne => hq_mem' q hq (haddr ▸ hne)) hnodup_objs hnodup_objs' hclosed
        hold_sub_gh hreach_mid hom_m rfl hcf hevu with hbk | ⟨o_mid', hom'm, hom'a, hreach', hcf'⟩
    · exact Or.inl hbk
    · right
      obtain ⟨pw0, hpw0, hpw_ty, hpw_lb⟩ := hback1 pv hpv_m
      have hpw_id : pw0.id = pv.id := (RcCtx.get?_mem hpw0).2
      by_cases hpvx : pv.id = vx.id
      · have hpw_eq : pw0 = vx := by have h := hpw0; rw [hpvx, hxid, hgx] at h; cases h; rfl
        have hty_pv : pv.ty = vx.ty := hpw_ty.symm.trans (hpw_eq ▸ rfl)
        have hbvp_eq : bvp = addr := by
          have h := (hpvx ▸ henvh_v).symm.trans (hty_pv ▸ hwu0'); cases h; rfl
        have hq_o' : o_q.addr = o'.addr := hq_bv.trans (hbvp_eq.trans haddr.symm)
        exact ⟨wp, o', hwp, hq_o' ▸ hqaddr, (list_mem_set_iff hidx).mpr (Or.inl rfl),
          o_mid', hom'm, hq_o' ▸ hom'a.symm ▸ hreach', hcf'⟩
      · have hnsb_pv : !pw0.ty.isScalar = true := by
          rw [hpw_ty]; cases h : pv.ty.isScalar <;> simp_all
        have hne_q : o_q.addr ≠ addr := by
          rw [hq_bv]
          exact hlive_ne pw0 (RcCtx.get?_mem hpw0).1 (fun h => hpvx (hpw_id ▸ h))
            (hpw_lb hlive_pv).1 hnsb_pv bvp (hpw_id ▸ hpw_ty ▸ hwu0')
        exact ⟨wp, o_q, hwp, hqaddr, hq_mem' o_q ho_q hne_q, o_mid', hom'm,
          hom'a.symm ▸ hreach', hcf'⟩

private theorem oset_hhih_ep_excl_step {rt : BitVec 64} {rf rf0 : RcFrame} {σ σ0 : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx)
    (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs) (hepres : EntryPres rf0 σ0 rf σ)
    (hexcl : ExclCtorHeap rf)
    {x i cidx : Nat} {vx : RcVar} (hgx : rf.ctx.get? x = some vx)
    (hno : vx.noRc = false) (hpers : vx.persistent = false)
    (hown1 : vx.owned = 1) (hvbor : vx.borrowed = false) (hvx_ns : vx.ty.isScalar = false)
    {addr : BitVec 64} (henvh_v : rf.envH vx.id = some (vx.ty, .i64 addr))
    (hev : addr &&& 1#64 = 0#64) {idx : Nat} (hidx : idx < σ.objs.length)
    (_haddr : σ.objs[idx].addr = addr) (horc1 : σ.objs[idx].rc = 1#32)
    (hotle : σ.objs[idx].tag ≤ 244) (hi : i < σ.objs[idx].fields.length)
    (hcnt0 : List.count addr (localHandlesExcept rf.ctx rf.envH vx.id ++ rf.extH ++ rf.ghostH) = 0)
    (hchild_ne : ∀ q ∈ σ.objs, q.Wf → q.addr ≠ addr →
      ∀ f ∈ q.childFields, f &&& 1#64 = 0#64 → f ≠ addr)
    (hbk_ne : ∀ a,
      Backed σ.objs (localHandlesExcept rf.ctx rf.envH vx.id ++ rf.extH ++ rf.ghostH) a →
      a ≠ addr)
    {fs : List PVal} {hscal : List UInt8}
    {y : LcArg} {ctx1 : RcCtx} (hcons : rf.ctx.consumeArg y = .ok ctx1)
    {py : PVal} {newF : BitVec 64}
    (hy_ok : (y = .erased → newF = 1#64 ∧ py = .erased) ∧
      (∀ yid, y = .var yid → ∃ vy, rf.ctx.get? yid = some vy ∧ vy.isLive = true ∧
        vy.ty.isScalar = false ∧ rf.envH yid = some (vy.ty, .i64 newF) ∧
        (rf.ctx.sharedPreds.all (·.2 != yid)) = true))
    (hclean1 : CleanVars ctx1) (hnd1 : (ctx1.vars.map RcVar.id).Nodup)
    (hback1 : ∀ u ∈ ctx1.vars, ∃ w0, rf.ctx.get? u.id = some w0 ∧ w0.ty = u.ty ∧
      (u.isLive = true → w0.isLive = true ∧ (u.borrowed = true → w0.borrowed = true)))
    (hown_y : ∀ v0 yid, y = .var yid → rf.ctx.get? yid = some v0 → ∀ vx', ctx1.get? yid = some vx' →
      vx'.owned = if v0.noRc || v0.persistent || 1 == 0 then v0.owned else v0.owned - 1)
    (hnpre : ∀ a,
      nonPersistRefs (σ.objs.set idx { σ.objs[idx] with
          fields := σ.objs[idx].fields.set i newF }) a +
        (if a = σ.objs[idx].fields[i] then 1 else 0) =
      nonPersistRefs σ.objs a + (if a = newF then 1 else 0)) :
    let o := σ.objs[idx]
    let oldF := o.fields[i]
    let o' := { o with fields := o.fields.set i newF }
    let σ' : HState := { σ with objs := σ.objs.set idx o' }
    let ghostH' := if oldF &&& 1#64 == 0#64 then oldF :: rf.ghostH else rf.ghostH
    let rf' : RcFrame :=
      { ctx := ctx1, envP := rf.envP.set x (.ctor cidx (fs.set i py) hscal),
        envH := rf.envH, extH := rf.extH, ghostH := ghostH' }
    (∀ q ∈ σ.objs, q.addr ≠ addr → q ∈ σ'.objs) → oldF ≠ addr →
    HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs ∧
    EntryPres rf0 σ0 rf' σ' ∧ ExclCtorHeap rf' := by
  intro o oldF o' σ' ghostH' rf' hq_mem' holdF_ne
  have hwf_all := hinv.1.1.2.1
  have hclosed := hinv.1.1.2.2.1
  have hnodup := hinv.2.1
  have hvm := (RcCtx.get?_mem hgx).1
  have hxid := (RcCtx.get?_mem hgx).2
  have hlive : vx.isLive = true := by simp [RcVar.isLive, hown1]
  have hcf_o : o.childFields = o.fields := by simp [o, LcnfObj.childFields, hotle]
  have hgh_sub : ∀ a, a ∈ rf.ghostH → a ∈ ghostH' := by
    intro a ha; dsimp only [ghostH']; split <;> simp [ha]
  have hhih' : HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs := by
    intro a ha
    dsimp only [rf'] at ha
    rw [List.mem_append] at ha
    have ha_cases : a ∈ rf.extH ++ rf.ghostH ∨ (a = oldF ∧ oldF &&& 1#64 = 0#64) := by
      rcases ha with hext | hgh
      · exact Or.inl (List.mem_append.mpr (Or.inl hext))
      · dsimp only [ghostH'] at hgh
        by_cases hevo : (oldF &&& 1#64 == 0#64) = true
        · simp only [hevo, ite_true, List.mem_cons] at hgh
          rcases hgh with rfl | hgh0
          · exact Or.inr ⟨rfl, beq_iff_eq.mp hevo⟩
          · exact Or.inl (List.mem_append.mpr (Or.inr hgh0))
        · simp only [hevo] at hgh
          exact Or.inl (List.mem_append.mpr (Or.inr hgh))
    rcases ha_cases with ha_old | ⟨rfl, hevo⟩
    · obtain ⟨q, hq, hqa⟩ := hhih a ha_old
      have hne : a ≠ addr := fun h => by
        have hcnt_pos : 0 < List.count addr (rf.extH ++ rf.ghostH) :=
          List.count_pos_iff.mpr (h ▸ ha_old)
        simp only [List.count_append] at hcnt0 hcnt_pos; omega
      exact ⟨q, hq_mem' q hq (hqa.symm ▸ hne), hqa⟩
    · obtain ⟨t, ht, hta⟩ := hclosed o (List.getElem_mem hidx) oldF
        (by rw [hcf_o]; exact List.getElem_mem hi) hevo
      exact ⟨t, hq_mem' t ht (hta.symm ▸ holdF_ne), hta⟩
  have hepres' : EntryPres rf0 σ0 rf' σ' := by
    obtain ⟨hhs0, hiso0, hext0, hgh0, hgh_cnt0⟩ := hepres
    have hhs_step : HeapStepRel (rf0.extH ++ rf0.ghostH) σ σ' := by
      refine ⟨by dsimp only [σ']; simp [RtC0State.PreservesMeta], rfl, rfl,
        fun q hq hqwf hbk => ?_, fun a hb => ?_⟩
      · have hbk_all : Backed σ.objs
            (localHandlesExcept rf.ctx rf.envH vx.id ++ rf.extH ++ rf.ghostH) q.addr := by
          refine backed_mono_roots (fun r hr => ?_) hbk
          rw [List.mem_append] at hr
          rcases hr with hre | hrg
          · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (hext0 ▸ hre))))
          · exact List.mem_append.mpr (Or.inr (hgh0 r hrg))
        have hne := hbk_ne q.addr hbk_all
        exact ⟨q, hq_mem' q hq hne, objDataEq_refl q hqwf, id, id⟩
      · have hbk_all :
            Backed σ.objs (localHandlesExcept rf.ctx rf.envH vx.id ++ rf.extH ++ rf.ghostH) a := by
          refine backed_mono_roots (fun r hr => ?_) hb
          rw [List.mem_append] at hr
          rcases hr with hre | hrg
          · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (hext0 ▸ hre))))
          · exact List.mem_append.mpr (Or.inr (hgh0 r hrg))
        have hne := hbk_ne a hbk_all
        refine backed_mono_heap (P := fun z => z ≠ addr)
          (fun q hq _ hne_q => ⟨q, hq_mem' q hq hne_q, rfl, rfl, rfl⟩)
          hchild_ne hwf_all (fun r hr => ⟨hr, fun h => by
            have hmem : addr ∈ rf.extH ++ rf.ghostH := by
              rw [List.mem_append] at hr ⊢
              rcases hr with hre | hrg
              · exact Or.inl (hext0 ▸ h ▸ hre)
              · exact Or.inr (hgh0 addr (h ▸ hrg))
            have hcnt_pos : 0 < List.count addr (rf.extH ++ rf.ghostH) :=
              List.count_pos_iff.mpr hmem
            simp only [List.count_append] at hcnt0 hcnt_pos; omega⟩)
          hne hb
    refine ⟨heapStepRel_trans hhs0 hhs_step, ?_, hext0, fun a ha => hgh_sub a (hgh0 a ha),
      fun a => by
        dsimp only [rf', ghostH']
        split
        · rw [List.count_cons]
          exact Nat.le_trans (hgh_cnt0 a) (Nat.le_add_right _ _)
        · exact hgh_cnt0 a⟩
    intro a ha hiso_a0
    obtain ⟨hiso_a, ha_rc1⟩ := hiso0 a ha hiso_a0
    obtain ⟨hiso_live, hiso_np, o_a, ho_a, ho_awf, ho_aa, ho_arc1⟩ := hiso_a
    have hnsb : !vx.ty.isScalar = true := by simp [hvx_ns]
    have hne_addr : addr ≠ a := fun heq =>
      hiso_live vx hvm hlive hnsb (Word.i64 addr) henvh_v (by subst heq; rfl)
    have hnp_a' : nonPersistRefs σ'.objs a = 0 := by
      have ha_ne_new : a ≠ newF := fun heq => by
        cases y with
        | erased =>
          rw [(hy_ok.1 rfl).1] at heq
          have : o_a.addr &&& 1#64 = 0#64 := obj_addr_and1_zero ho_awf
          rw [ho_aa, heq] at this; cases this
        | var yid =>
          obtain ⟨vy, hgy, hly, hvy_ns, hwy, _⟩ := hy_ok.2 yid rfl
          exact hiso_live vy (RcCtx.get?_mem hgy).1 hly (by simp [hvy_ns])
            (.i64 newF) ((RcCtx.get?_mem hgy).2 ▸ hwy) (by subst heq; rfl)
      have ha_ne_old : a ≠ oldF := fun heq => by
        have hpos := nonPersistRefs_pos_of_mem_cf (a := oldF) (List.getElem_mem hidx)
          (by rw [horc1]; decide) (by rw [hcf_o]; exact List.getElem_mem hi)
        rw [← heq] at hpos; omega
      have hnp := hnpre a
      change nonPersistRefs σ'.objs a + (if a = oldF then 1 else 0) =
        nonPersistRefs σ.objs a + (if a = newF then 1 else 0) at hnp
      simp only [ha_ne_old, ha_ne_new, ite_false] at hnp
      omega
    refine ⟨⟨fun u hu hul hns_u w hw heqw => ?_, hnp_a',
      ⟨o_a, hq_mem' o_a ho_a (ho_aa.symm ▸ hne_addr.symm), ho_awf, ho_aa, ho_arc1⟩⟩, ?_⟩
    · obtain ⟨w0, hw0, hw0_ty, hw0_lb⟩ := hback1 u hu
      exact hiso_live w0 (RcCtx.get?_mem hw0).1 (hw0_lb hul).1
        (hw0_ty ▸ hns_u) w ((RcCtx.get?_mem hw0).2 ▸ hw0_ty ▸ hw) heqw
    · intro q0 hq0 hqa0
      obtain ⟨q, hq, hdeq, hq1⟩ := ha_rc1 q0 hq0 hqa0
      exact ⟨q, hq_mem' q hq ((hdeq.1.trans hqa0).symm ▸ hne_addr.symm), hdeq, hq1⟩
  have hexcl1 : ExclCtorHeap { rf with ctx := ctx1 } :=
    exclCtorHeap_consumeArg hnodup hclean hcons hexcl
  have hexcl' : ExclCtorHeap rf' := by
    intro u hu hul hexu hnou hpersu c fs' sc hpu
    by_cases hux : u.id = x
    · have hgu := rcCtx_get?_of_mem hnd1 hu
      rcases y with _ | yid
      · simp [RcCtx.consumeArg, pure, Except.pure] at hcons; subst hcons
        have hueq : u = vx := by have h := hgu.symm.trans (hux.symm ▸ hgx); cases h; rfl
        exact ⟨addr, hueq ▸ henvh_v, hev⟩
      · by_cases hyx : yid = x
        · subst hyx
          exact absurd (oset_not_live_of_consume_self hnodup hgx hno hpers hown1 hvbor
            hcons hclean1 hback1 (fun v0 hv0 vx' hvx' => hown_y v0 yid rfl hv0 vx' hvx')
            hu hux hul) False.elim
        · obtain ⟨w0, hw0, _, _, _, hw0_ty, _⟩ :=
            consumeVar_get?_live_back hnodup hclean hcons u.id hgu hul
          have hw0_eq : w0 = vx := by have h := (hux ▸ hw0).symm.trans hgx; cases h; rfl
          have hu_ty : u.ty = vx.ty := hw0_ty.symm.trans (hw0_eq ▸ rfl)
          exact ⟨addr, by rw [hu_ty, hux, ← hxid]; exact henvh_v, hev⟩
    · simp only [rf', PValEnv.set, hux, ite_false] at hpu
      exact hexcl1 u hu hul hexu hnou hpersu c fs' sc hpu
  exact ⟨hhih', hepres', hexcl'⟩

/-- Full invariant preservation for `LcCode.oset`. -/
public theorem oset_heap_rcInv {rt : BitVec 64} {rf rf0 : RcFrame} {σ σ0 : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx) (hexcl : ExclCtorHeap rf)
    {x i cidx : Nat} {vx : RcVar} (hgx : rf.ctx.get? x = some vx)
    (hno : vx.noRc = false) (hpers : vx.persistent = false) (hrt : vx.resetTok = false)
    (hown1 : vx.owned = 1) (hex : vx.excl = true) (hvx_ns : vx.ty.isScalar = false)
    (hvx_nt : vx.ty ≠ .tagged)
    {addr : BitVec 64} (henvh : rf.envH x = some (vx.ty, .i64 addr)) (hev : addr &&& 1#64 = 0#64)
    {idx : Nat} (hidx : idx < σ.objs.length) (haddr : σ.objs[idx].addr = addr)
    (horc1 : σ.objs[idx].rc = 1#32) (hotle : σ.objs[idx].tag ≤ 244)
    (hotag : σ.objs[idx].tag = cidx) (hi : i < σ.objs[idx].fields.length)
    {fs : List PVal} {hscal : List UInt8}
    (hosc : σ.objs[idx].scalarData = hscal)
    (hof : objFieldsRep fs σ.objs[idx].fields σ.objs)
    {y : LcArg} {ctx1 : RcCtx} (hcons : rf.ctx.consumeArg y = .ok ctx1)
    {py : PVal} {newF : BitVec 64} (hobj_y : ObjRep py newF σ.objs)
    (hy_ok : (y = .erased → newF = 1#64 ∧ py = .erased) ∧
      (∀ yid, y = .var yid → ∃ vy, rf.ctx.get? yid = some vy ∧ vy.isLive = true ∧
        vy.ty.isScalar = false ∧ rf.envH yid = some (vy.ty, .i64 newF) ∧
        (rf.ctx.sharedPreds.all (·.2 != yid)) = true)) :
    let o := σ.objs[idx]
    let oldF := o.fields[i]
    let o' := { o with fields := o.fields.set i newF }
    let σ' : HState := { σ with objs := σ.objs.set idx o' }
    let ghostH' := if oldF &&& 1#64 == 0#64 then oldF :: rf.ghostH else rf.ghostH
    let rf' : RcFrame :=
      { ctx := ctx1, envP := rf.envP.set x (.ctor cidx (fs.set i py) hscal),
        envH := rf.envH, extH := rf.extH, ghostH := ghostH' }
    RcInv rt rf' σ' ∧ CleanVars rf'.ctx ∧ ParentsOwned rf'.ctx ∧ NoRcCorrect rf'.ctx ∧
      ParentChildBacked rf' σ'.objs ∧ SharedTargetsHeap rf' ∧
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs ∧ EntryPres rf0 σ0 rf' σ' ∧
      SharedBoolVars rf'.ctx ∧ ExclCtorHeap rf' := by
  intro o oldF o' σ' ghostH' rf'
  have ⟨hheap, hnodup, _, _, _⟩ := hinv
  obtain ⟨hbn, hwf_all, hclosed, hcap, hrc_all⟩ := hheap.1
  have hnodup_objs := hheap.2
  have howf : o.Wf := hwf_all _ (List.getElem_mem hidx)
  obtain ⟨hvm, hxid⟩ := RcCtx.get?_mem hgx
  have hvbor : vx.borrowed = false := by
    cases hb : vx.borrowed
    · rfl
    · exfalso; have := (hclean vx hvm).2.2.1 hb; rw [hex] at this; cases this.2.2
  have henvh_v : rf.envH vx.id = some (vx.ty, .i64 addr) := hxid ▸ henvh
  have hdisj := excl_disjoint_facts hinv hclean hpo hpcb hvm hno hpers hrt hown1 henvh_v
    (List.getElem_mem hidx) howf haddr horc1
  obtain ⟨_, hcnt0, hnot_self, hlive_ne, hchild_ne, hbk_ne⟩ := hdisj
  have hcf_o : o.childFields = o.fields := by simp [o, LcnfObj.childFields, hotle]
  have holdF_ne : oldF ≠ addr := fun h => hnot_self (by
    rw [hcf_o]; exact h ▸ List.getElem_mem hi)
  have ho'w : o'.Wf := lcnfObj_wf_set_fields howf hotle hi newF
  have ho'ch : o'.childFields = o.childFields.set i newF := by
    simp [o', o, LcnfObj.childFields, hotle]
  have hnodup_objs' : (σ'.objs.map LcnfObj.addr).Nodup := by
    dsimp only [σ']
    rw [list_map_addr_set_eq hidx (show o'.addr = σ.objs[idx].addr from rfl)]
    exact hnodup_objs
  have hwf_all' : ∀ q ∈ σ'.objs, q.Wf := by
    intro q hq; dsimp only [σ'] at hq; rw [list_mem_set_iff hidx] at hq
    rcases hq with rfl | ⟨j, hj, _, rfl⟩
    · exact ho'w
    · exact hwf_all _ (List.getElem_mem hj)
  have hclosed' : lcnfHeapClosed σ'.objs := by
    intro q hq f hf hevf
    dsimp only [σ'] at hq; rw [list_mem_set_iff hidx] at hq
    rcases hq with rfl | ⟨j, hj, hjne, rfl⟩
    · have hi_ch : i < o.childFields.length := by rw [hcf_o]; exact hi
      rw [ho'ch, list_mem_set_iff hi_ch] at hf
      rcases hf with rfl | ⟨m', hm', _, rfl⟩
      · obtain ⟨t, ht, hta⟩ := objRep_even_mem hobj_y hevf
        by_cases ht_eq : t.addr = addr
        · exact ⟨o', (list_mem_set_iff hidx).mpr (Or.inl rfl),
            show o'.addr = f from haddr.trans (ht_eq.symm.trans hta)⟩
        · obtain ⟨k, hk, hgetk⟩ := obj_mem_idx ht
          have hkne : k ≠ idx := fun h => by subst h; exact ht_eq (hgetk.symm ▸ haddr)
          exact ⟨t, (list_mem_set_iff hidx).mpr (Or.inr ⟨k, hk, hkne, hgetk⟩), hta⟩
      · have hf_old := List.getElem_mem hm'
        obtain ⟨t, ht, hta⟩ := hclosed o (List.getElem_mem hidx) _ hf_old hevf
        have hne : t.addr ≠ addr := fun h => by
          rw [← hta, h] at hf_old; exact hnot_self hf_old
        obtain ⟨k, hk, hgetk⟩ := obj_mem_idx ht
        have hkne : k ≠ idx := fun h => by
          subst h; exact hne ((congrArg LcnfObj.addr hgetk).symm.trans haddr)
        exact ⟨t, (list_mem_set_iff hidx).mpr (Or.inr ⟨k, hk, hkne, hgetk⟩), hta⟩
    · have hqj : σ.objs[j].addr ≠ addr := fun h =>
        hjne (nodup_map_getElem_inj hnodup_objs hj hidx (h.trans haddr.symm))
      have hne : f ≠ addr := hchild_ne _ (List.getElem_mem hj)
        (hwf_all _ (List.getElem_mem hj)) hqj f hf hevf
      obtain ⟨t, ht, hta⟩ := hclosed _ (List.getElem_mem hj) f hf hevf
      obtain ⟨k, hk, hgetk⟩ := obj_mem_idx ht
      have hkne : k ≠ idx := fun h => by
        subst h; exact hne (hta.symm.trans ((congrArg LcnfObj.addr hgetk).symm.trans haddr))
      exact ⟨t, (list_mem_set_iff hidx).mpr (Or.inr ⟨k, hk, hkne, hgetk⟩), hta⟩
  have hcap' : σ'.objs.length ≤ σ'.st.workCap := by simpa [σ'] using hcap
  have hrc_all' : ∀ q ∈ σ'.objs, q.rc.toNat < 2 ^ 31 - 1 := by
    intro q hq; dsimp only [σ'] at hq; rw [list_mem_set_iff hidx] at hq
    rcases hq with rfl | ⟨j, hj, _, rfl⟩
    · simp [o']; exact hrc_all _ (List.getElem_mem hidx)
    · exact hrc_all _ (List.getElem_mem hj)
  have hy_sub : (y = .erased → newF = 1#64) ∧
      (∀ yid, y = .var yid → ∃ vy, rf.ctx.get? yid = some vy ∧ vy.isLive = true ∧
        vy.ty.isScalar = false ∧ rf.envH yid = some (vy.ty, .i64 newF) ∧
        (rf.ctx.sharedPreds.all (·.2 != yid)) = true) :=
    ⟨fun h => (hy_ok.1 h).1, hy_ok.2⟩
  have hcons_info := oset_consume_step hinv hclean hpo hcons hy_sub
  obtain ⟨hperm_lh, hperm_ex, hinv1, hclean1, hpo1, hback1, hown_y⟩ := hcons_info
  have hy_sub2 : (y = .erased → newF = 1#64) ∧
      (∀ yid, y = .var yid → ∃ vy, rf.ctx.get? yid = some vy ∧ vy.isLive = true ∧
        vy.ty.isScalar = false ∧ rf.envH yid = some (vy.ty, .i64 newF)) :=
    ⟨fun h => (hy_ok.1 h).1, fun yid hy =>
      let ⟨a, b, c, d, e, _⟩ := hy_ok.2 yid hy; ⟨a, b, c, d, e⟩⟩
  obtain ⟨hnpre, hsound'⟩ :=
    oset_handlesRcSound hinv hclean hidx horc1 hotle hi hcons hperm_lh hy_sub2
  have hnd1 := hinv1.2.1
  have hnorc1 : NoRcCorrect ctx1 := by
    cases y with
    | erased => simp [RcCtx.consumeArg, pure, Except.pure] at hcons; subst hcons; exact hnorc
    | var yid => exact noRcCorrect_consumeVar hnodup hnorc hcons
  have hpcb1 : ParentChildBacked { rf with ctx := ctx1 } σ.objs := by
    cases y with
    | erased => simp [RcCtx.consumeArg, pure, Except.pure] at hcons; subst hcons; exact hpcb
    | var yid => exact parentChildBacked_consumeVar hnodup hclean hcons hpcb
  have hsth1 : SharedTargetsHeap { rf with ctx := ctx1 } := by
    cases y with
    | erased => simp [RcCtx.consumeArg, pure, Except.pure] at hcons; subst hcons; exact hsth
    | var yid => exact sharedTargetsHeap_consumeVar hnodup hsth hcons
  have hsbv1 : SharedBoolVars ctx1 := sharedBoolVars_consumeArg hnodup hsbv hcons
  have hq_mem' : ∀ q ∈ σ.objs, q.addr ≠ addr → q ∈ σ'.objs := by
    intro q hq hqne
    obtain ⟨j, hj, hgetj⟩ := obj_mem_idx hq
    exact (list_mem_set_iff hidx).mpr
      (Or.inr ⟨j, hj, fun h => by subst h; exact hqne (hgetj.symm ▸ haddr), hgetj⟩)
  have hvars' := oset_hvars_step hinv hclean hgx hno hpers hown1 hvbor hvx_ns hvx_nt henvh_v hev
    hidx haddr horc1 hotle hotag hi hnot_self hchild_ne hlive_ne hosc hof hcons hobj_y hy_ok
    hinv1 hclean1 hback1 hown_y hnodup_objs' hq_mem'
  have hsp' := oset_hsp_step (cidx := cidx) (fs := fs) (hscal := hscal) hinv hclean hgx hno hidx
    haddr horc1 hotle hi hcons hy_ok hinv1 hsbv1 hperm_ex hnpre hq_mem'
  have hpcb' := oset_hpcb_step (cidx := cidx) (fs := fs) (hscal := hscal) (py := py) hinv hgx
    hvbor henvh_v hidx haddr hotle hi hnot_self hlive_ne hinv1 hclean1 hpo1 hpcb1 hback1
    hnodup_objs' hq_mem'
  obtain ⟨hhih', hepres', hexcl'⟩ := oset_hhih_ep_excl_step (cidx := cidx) (fs := fs)
    (hscal := hscal) hinv hclean hhih hepres hexcl hgx hno hpers hown1 hvbor hvx_ns henvh_v hev
    hidx haddr horc1 hotle hi hcnt0 hchild_ne hbk_ne hcons hy_ok hclean1 hnd1 hback1 hown_y hnpre
    hq_mem' holdF_ne
  exact ⟨⟨⟨⟨hbn, hwf_all', hclosed', hcap', hrc_all'⟩, hnodup_objs'⟩, hnd1,
    hsound', hvars', hsp'⟩,
    hclean1, hpo1, hnorc1, hpcb', hsth1, hhih', hepres', hsbv1, hexcl'⟩

/-- Stepwise simulation for `LcCode.oset` exposing `extH` and `consumeArg` post-context. -/
public theorem oset_step_ctx {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {J : HJEnv} {Jp : PResJEnv}
    {Q : PResPost} {Xp : PResXPost} {Qh : HPost} {Xh : HXPost}
    {jps : List RcJpInfo} {rf rf0 : RcFrame} {σ σ0 : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr : Nat}
    {x i : Nat} {y : LcArg} {k : LcCode}
    (hwf : perceusCodeWf env retTy jps rf.ctx sm (LcCode.oset x i y k) = true)
    (hchk : rf.ctx.checkExcl x "oset" = .ok ())
    (hpr : PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Q Xp (LcCode.oset x i y k))
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx)
    (hexcl : ExclCtorHeap rf) (hsm : ShadowSmWf sm) (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    (hres : ResStateInv σ rem wr rcr)
    (hk : ∀ {rf' : RcFrame} {σ' : HState} {ρP' : PValEnv},
      perceusCodeWf env retTy jps rf'.ctx sm k = true →
      PRWp m env retTy Δr jps rf'.ctx Jp ρP' rem wr rcr Q Xp k →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → ExclCtorHeap rf' → ShadowSmWf sm →
      ShadowOk sm rf'.ctx ρP' rf'.envP → ResStateInv σ' rem wr rcr →
      rf'.envH = rf.envH ∧ (∀ z ≠ x, ρP' z = ρP z ∧ rf'.envP z = rf.envP z) ∧
        rf'.extH = rf.extH ∧ rf.ctx.consumeArg y = .ok rf'.ctx →
      HWp Δh rt retTy J rf'.envH Qh Xh k σ') :
    HWp Δh rt retTy J rf.envH Qh Xh (LcCode.oset x i y k) σ := by
  rw [PRWp.eq_7] at hpr
  rw [HWp.eq_7]
  obtain ⟨vx, hgx, hno, hpers, hrt, hown1, hex, hlx⟩ := checkExcl_facts hchk
  cases hρx : ρP x with
  | none => simp [hρx] at hpr
  | some xv =>
    cases hρy : ρP.evalArg y with
    | none => simp [hρx, hρy] at hpr
    | some py =>
      cases hcons : rf.ctx.consumeArg y with
      | error _ => simp [hρx, hρy, hcons] at hpr
      | ok ctx1 =>
        simp only [hρx, hρy, hcons] at hpr
        cases hset : xv.setObj i py with
        | none => simp [hset] at hpr
        | some xv' =>
          simp only [hset] at hpr
          cases xv with
          | ctor cidx fs pscal =>
            simp only [PVal.setObj] at hset
            by_cases hi_p : i < fs.length
            · simp only [hi_p, ite_true] at hset; cases hset
              unfold perceusCodeWf at hwf; dsimp only at hwf
              simp only [hgx, hcons, Bool.and_eq_true] at hwf
              have hy_init : argScalarInit sm y = true := by
                cases y with
                | erased => rfl
                | var _ => exact hwf.1.1
              have hwf_k : perceusCodeWf env retTy jps ctx1 sm k = true := hwf.2
              have hvx_ns : vx.ty.isScalar = false := by
                cases y with
                | erased =>
                  have hw1 := hwf.1.2
                  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hw1; exact hw1.1
                | var yid =>
                  cases hgy : rf.ctx.get? yid with
                  | none => simp [hgy] at hwf
                  | some vy =>
                    have hw1 := hwf.1.2
                    simp only [hgy, Bool.and_eq_true, Bool.not_eq_true'] at hw1
                    exact hw1.1.1
              have hvx_nt : vx.ty ≠ .tagged := by
                cases y with
                | erased =>
                  have hw1 := hwf.1.2
                  simp only [Bool.and_eq_true] at hw1
                  exact fun heq => by rw [heq] at hw1; exact absurd hw1.2 (by decide)
                | var yid =>
                  cases hgy : rf.ctx.get? yid with
                  | none => simp [hgy] at hwf
                  | some vy =>
                    have hw1 := hwf.1.2
                    simp only [hgy, Bool.and_eq_true] at hw1
                    exact fun heq => by rw [heq] at hw1; exact absurd hw1.1.2 (by decide)
              have hy_ev_in : ∀ yid, y = .var yid → ∃ vy, rf.ctx.get? yid = some vy ∧
                  vy.isLive = true ∧ vy.ty.isScalar = false := by
                intro yid heq; subst heq
                cases hgy : rf.ctx.get? yid with
                | none => simp [hgy] at hwf
                | some vy =>
                  have hw1 := hwf.1.2
                  simp only [hgy, Bool.and_eq_true, Bool.not_eq_true'] at hw1
                  have hly : vy.isLive = true := by
                    by_cases h1 : vy.noRc = true
                    · simp [RcVar.isLive, h1]
                    · by_cases h2 : vy.persistent = true
                      · simp [RcVar.isLive, h2]
                      · have h1f : vy.noRc = false := by cases h : vy.noRc <;> simp_all
                        have h2f : vy.persistent = false := by
                          cases h : vy.persistent <;> simp_all
                        have hpos : ¬ vy.owned < 1 := by
                          intro hlt
                          unfold RcCtx.consumeArg RcCtx.consumeVar at hcons
                          simp [hgy, h1f, h2f, hlt] at hcons
                        simp [RcVar.isLive]; omega
                  exact ⟨vy, rfl, hly, hw1.2.1⟩
              obtain ⟨newF, hnewF_ev, hobj_y, hy_er, hy_var⟩ :=
                oset_obj_eval hinv hshd hy_init hy_ev_in hρy
              have hne_p : ¬(fs = [] ∧ pscal = []) := fun ⟨h0, _⟩ => by simp [h0] at hi_p
              obtain ⟨hscal, addr, idx, hidx, hE_x, _, henvh_x, hgbv_x, hev, haddr, _,
                hotag, hotle, hflen, hosc, horc1, hof⟩ := ctor_excl_obj_facts hinv hclean hshd hexcl
                hgx hno hpers hrt hown1 hex hlx hvx_ns hρx (Or.inl hne_p)
              have hi_o : i < σ.objs[idx].fields.length := hflen ▸ hi_p
              have hy_full : (y = .erased → newF = 1#64 ∧ py = .erased) ∧
                  (∀ yid, y = .var yid → ∃ vy, rf.ctx.get? yid = some vy ∧ vy.isLive = true ∧
                    vy.ty.isScalar = false ∧ rf.envH yid = some (vy.ty, .i64 newF) ∧
                    (rf.ctx.sharedPreds.all (·.2 != yid)) = true) := by
                refine ⟨hy_er, fun yid heq => ?_⟩
                subst heq
                cases hgy : rf.ctx.get? yid with
                | none => simp [hgy] at hwf
                | some vy =>
                  have hw1 := hwf.1.2
                  simp only [hgy, Bool.and_eq_true] at hw1
                  obtain ⟨vy', h1, h2, h3⟩ := hy_ev_in yid rfl
                  simp only [hgy, Option.some.injEq] at h1; cases h1
                  exact ⟨vy, rfl, h2, h3, (hy_var yid vy rfl hgy).1, hw1.2.2⟩
              have hrc_st := oset_heap_rcInv hinv hclean hpo hnorc hpcb hsth hhih hepres hsbv
                hexcl hgx hno hpers hrt hown1 hex hvx_ns hvx_nt henvh_x hev hidx haddr horc1 hotle
                hotag hi_o hosc hof hcons hobj_y hy_full
              obtain ⟨hinv', hclean', hpo', hnorc', hpcb', hsth', hhih', hepres', hsbv', hexcl'⟩ :=
                hrc_st
              let o := σ.objs[idx]
              let o' : LcnfObj := { o with fields := o.fields.set i newF }
              let σ' : HState := { σ with objs := σ.objs.set idx o' }
              have hres' : ResStateInv σ' rem wr rcr := by
                refine ⟨hres.1, by simpa [σ'] using hres.2.1, ?_⟩
                have hle : maxObjRc (σ.objs.set idx o') ≤ maxObjRc σ.objs := by
                  apply maxObjRc_set_le; intro _; simp [o', o, horc1]
                have hmax_le : Nat.max 1 (maxObjRc (σ.objs.set idx o')) ≤
                    Nat.max 1 (maxObjRc σ.objs) :=
                  Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hle (Nat.le_max_right _ _)⟩
                have := hres.2.2; simp only [σ']; omega
              have hshd0 := shadowOk_consumeArg hinv.2.1 hclean hcons hshd
              have hshd' : ShadowOk sm ctx1 (ρP.set x (.ctor cidx (fs.set i py) pscal))
                  (rf.envP.set x (.ctor cidx (fs.set i py) hscal)) := by
                refine shadowOk_update_same_shape hshd0 ?_ ?_
                · intro hinit
                  have hxs := hshd vx (RcCtx.get?_mem hgx).1 hlx
                  simp only [(RcCtx.get?_mem hgx).2, hinit, ite_true] at hxs
                  rw [hρx, hE_x] at hxs; cases hxs; rfl
                · intro sz m hf
                  have hxs := hshd vx (RcCtx.get?_mem hgx).1 hlx
                  have hni : isVarScalarInit sm x = false := by
                    cases hi0 : isVarScalarInit sm x
                    · rfl
                    · rw [isVarScalarInit_iff_find_none] at hi0; rw [hf] at hi0; cases hi0
                  simp only [(RcCtx.get?_mem hgx).2, hni] at hxs
                  obtain ⟨sz0, m0, hf0, c0, fs0, ps0, hs0, hρ0, hE0, hl1, hl2, hsz, hagr⟩ := hxs
                  rw [hf] at hf0; cases hf0
                  rw [hρx] at hρ0; cases hρ0; rw [hE_x] at hE0; cases hE0
                  exact ⟨cidx, fs.set i py, pscal, hscal, rfl, rfl, hl1, hl2, by simpa using hsz,
                    hagr⟩
              have hstep_k := hk hwf_k hpr hinv' hclean' hpo' hnorc' hpcb' hsth' hhih' hepres'
                hsbv' hexcl' hsm hshd' hres'
                ⟨rfl, fun z hzx => ⟨by simp [PValEnv.set, hzx], by simp [PValEnv.set, hzx]⟩,
                  rfl, hcons⟩
              rw [hgbv_x, hnewF_ev]
              exact ⟨idx, hidx, haddr, hotle, hi_o, hstep_k⟩
            · simp [hi_p] at hset
          | _ => simp [PVal.setObj] at hset

/-- Stepwise simulation for `LcCode.oset`: advances `HWp`, `RcInv`, `ShadowOk`, and `ghostH`. -/
public theorem oset_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {J : HJEnv} {Jp : PResJEnv}
    {Q : PResPost} {Xp : PResXPost} {Qh : HPost} {Xh : HXPost}
    {jps : List RcJpInfo} {rf rf0 : RcFrame} {σ σ0 : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr : Nat}
    {x i : Nat} {y : LcArg} {k : LcCode}
    (hwf : perceusCodeWf env retTy jps rf.ctx sm (LcCode.oset x i y k) = true)
    (hchk : rf.ctx.checkExcl x "oset" = .ok ())
    (hpr : PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Q Xp (LcCode.oset x i y k))
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx)
    (hexcl : ExclCtorHeap rf) (hsm : ShadowSmWf sm) (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    (hres : ResStateInv σ rem wr rcr)
    (hk : ∀ {rf' : RcFrame} {σ' : HState} {ρP' : PValEnv},
      perceusCodeWf env retTy jps rf'.ctx sm k = true →
      PRWp m env retTy Δr jps rf'.ctx Jp ρP' rem wr rcr Q Xp k →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → ExclCtorHeap rf' → ShadowSmWf sm →
      ShadowOk sm rf'.ctx ρP' rf'.envP → ResStateInv σ' rem wr rcr →
      rf'.envH = rf.envH ∧ (∀ z ≠ x, ρP' z = ρP z ∧ rf'.envP z = rf.envP z) →
      HWp Δh rt retTy J rf'.envH Qh Xh k σ') :
    HWp Δh rt retTy J rf.envH Qh Xh (LcCode.oset x i y k) σ :=
  oset_step_ctx hwf hchk hpr hinv hclean hpo hnorc hpcb hsth hhih hepres hsbv hexcl hsm hshd hres
    fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 he =>
      hk h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 ⟨he.1, he.2.1⟩

end OsetStep

end LeanQbe.T.LeanLCNF.Sem
