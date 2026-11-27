module

public import LeanQbe.T.LeanLCNF.Sem.PerceusInc
import LeanQbe.T.Logic.ProofKit

/-!
# LCNF Perceus-Sound Simulation: `del` Step

Invariant preservation and stepwise simulation lemma for `LcCode.del` in the
LCNF P-tier → H-tier Perceus soundness proof (`L4b`).
-/

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T.LeanLCNF

section DelStep

private theorem not_isScalar_of_clean_noRc {v : RcVar} (hcv : CleanVar v) (hno : v.noRc = false) :
    (!v.ty.isScalar) = true := by
  cases hs : v.ty.isScalar
  · rfl
  · exact absurd (hcv.1.2 hs) (by simp [hno])

private theorem map_eraseIdx {α β : Type} (f : α → β) (xs : List α) (idx : Nat) :
    (xs.eraseIdx idx).map f = (xs.map f).eraseIdx idx := by
  induction xs generalizing idx with
  | nil => rfl
  | cons x xs ih =>
    cases idx with
    | zero => rfl
    | succ i => simp [List.eraseIdx_cons_succ, ih i]

/-- `NonPersistReach` starting from `r ≠ bv` cannot pass through an exclusive root `bv`
    with `nonPersistRefs objs bv = 0`, so it lifts directly to `objs.eraseIdx idx`. -/
public theorem nonPersistReach_eraseIdx_of_ne {objs : List LcnfObj}
    {idx : Nat} (hidx : idx < objs.length)
    (hchild_ne : ∀ q ∈ objs, q.Wf → q.addr ≠ objs[idx].addr →
      ∀ f ∈ q.childFields, f &&& 1#64 = 0#64 → f ≠ objs[idx].addr)
    (hwf : ∀ q ∈ objs, q.Wf)
    {r a : BitVec 64} (hrne : r ≠ objs[idx].addr)
    (hreach : NonPersistReach objs r a) :
    NonPersistReach (objs.eraseIdx idx) r a ∧ a ≠ objs[idx].addr := by
  induction hreach with
  | refl h =>
    obtain ⟨o, ho, hoa, horc⟩ := h
    have hmem := mem_eraseIdx_of_addr_ne hidx ho (hoa ▸ hrne)
    exact ⟨NonPersistReach.refl ⟨o, hmem, hoa, horc⟩, hoa ▸ hrne⟩
  | step _ hchild hev hnz ih =>
    obtain ⟨ih_r, ih_ne⟩ := ih
    obtain ⟨o, ho, hoa, hcf⟩ := hchild
    obtain ⟨ov, hov, hova, hovrc⟩ := hnz
    have hmem_o := mem_eraseIdx_of_addr_ne hidx ho (hoa ▸ ih_ne)
    have hne_v : ov.addr ≠ objs[idx].addr := by
      rw [hova]
      exact hchild_ne o ho (hwf o ho) (hoa ▸ ih_ne) _ hcf hev
    have hmem_ov := mem_eraseIdx_of_addr_ne hidx hov hne_v
    exact ⟨NonPersistReach.step ih_r ⟨o, hmem_o, hoa, hcf⟩ hev ⟨ov, hmem_ov, hova, hovrc⟩,
      hova ▸ hne_v⟩

/-- Dropping an exclusive object at `idx` (`o.rc = 1#32`) and moving its heap children into
    `ghostH'` preserves all Perceus frame invariants. -/
public theorem del_heap_rcInv {rt : BitVec 64} {rf rf0 : RcFrame} {σ σ0 : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ)
    {x : Nat} {v : RcVar} {ctx1 : RcCtx}
    (hget : rf.ctx.get? x = some v) (hcons : rf.ctx.consumeVar x = Except.ok ctx1)
    (hno : v.noRc = false) (hpers : v.persistent = false) (hrt : v.resetTok = false)
    (hown1 : v.owned = 1) (hex : v.excl = true)
    {bv : BitVec 64} (henvh : rf.envH x = some (v.ty, Word.i64 bv))
    (hev : bv &&& 1#64 = 0#64)
    {idx : Nat} (hidx : idx < σ.objs.length) (haddr : σ.objs[idx].addr = bv)
    (horc1 : σ.objs[idx].rc = 1#32)
    {st' : RtC0State} (hmeta : st'.PreservesMeta σ.st) :
    let o := σ.objs[idx]
    let objs' := σ.objs.eraseIdx idx
    let σ' : HState := { st := st', objs := objs', scr := σ.scr, scrLimbs := σ.scrLimbs }
    let ghostH' := (o.childFields.filter (fun f => f &&& 1#64 == 0#64)) ++ rf.ghostH
    let rf' : RcFrame :=
      { ctx := ctx1, envP := rf.envP, envH := rf.envH, extH := rf.extH, ghostH := ghostH' }
    RcInv rt rf' σ' ∧ CleanVars rf'.ctx ∧ ParentsOwned rf'.ctx ∧ NoRcCorrect rf'.ctx ∧
      ParentChildBacked rf' σ'.objs ∧ SharedTargetsHeap rf' ∧
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs ∧ EntryPres rf0 σ0 rf' σ' := by
  intro o objs' σ' ghostH' rf'
  obtain ⟨hheap, hnodup, hsound, hvars, hsp⟩ := hinv
  obtain ⟨hbn, hwf_all, hclosed, hcap, hrc_all⟩ := hheap.1
  have hnodup_objs := hheap.2
  have howf : o.Wf := hwf_all o (List.getElem_mem hidx)
  obtain ⟨hvm, hxid⟩ := RcCtx.get?_mem hget
  have hlive : v.isLive = true := by simp [RcVar.isLive, hown1]
  have hvbor : v.borrowed = false := by
    cases hb : v.borrowed
    · rfl
    · exfalso; have := (hclean v hvm).2.2.1 hb; rw [hex] at this; simp at this
  have henvh_v : rf.envH v.id = some (v.ty, Word.i64 bv) := hxid ▸ henvh
  have hdisj := excl_disjoint_facts
    ⟨⟨⟨hbn, hwf_all, hclosed, hcap, hrc_all⟩, hnodup_objs⟩, hnodup, hsound, hvars, hsp⟩
    hclean hpo hpcb hvm hno hpers hrt hown1 henvh_v (List.getElem_mem hidx) howf haddr horc1
  obtain ⟨hnpre0, hcnt0, hnot_self, hlive_ne, hchild_ne, hbk_ne⟩ := hdisj
  have hsh_sub : ∀ p ∈ rf.ctx.sharedPreds, p.2 = x →
      ∀ v0, rf.ctx.get? x = some v0 →
        v0.noRc = true ∨ v0.persistent = true ∨ 1 = 0 ∨ v0.owned ≤ 1 := by
    intro _ _ _ v0 hg0
    rw [hg0] at hget; cases hget
    exact Or.inr (Or.inr (Or.inr (by omega)))
  have hcons_step := rcInv_consumeVar_step
    ⟨⟨⟨hbn, hwf_all, hclosed, hcap, hrc_all⟩, hnodup_objs⟩, hnodup, hsound, hvars, hsp⟩
    hclean hpo hcons hsh_sub
  obtain ⟨hperm_lh, hperm_ex, hinv1, hclean1, hpo1, hown_after⟩ := hcons_step
  have hnodup' : (ctx1.vars.map RcVar.id).Nodup := consumeVar_nodup hnodup hcons
  have hnorc' : NoRcCorrect ctx1 := noRcCorrect_consumeVar hnodup hnorc hcons
  have hsth' : SharedTargetsHeap rf' := sharedTargetsHeap_consumeVar hnodup hsth hcons
  have hpcb1 : ParentChildBacked
      { ctx := ctx1, envP := rf.envP, envH := rf.envH, extH := rf.extH, ghostH := rf.ghostH }
      σ.objs :=
    parentChildBacked_consumeVar hnodup hclean hcons hpcb
  have hbev : (bv &&& 1#64 == 0#64) = true := decide_eq_true hev
  have hch_bv : consumeVarHandles rf x 1 = [bv] := by
    have htbv : (Word.i64 bv).toBV64? = some bv := rfl
    simp [consumeVarHandles, hget, hno, hpers, henvh, hbev, htbv]
  rw [hch_bv] at hperm_lh hperm_ex
  have hbn' : BigNumRtWfR0 rt st' σ.scr σ.scrLimbs :=
    bigNumRtWfR0_of_preservesMeta hbn hmeta
  have hnodup_objs' : (objs'.map LcnfObj.addr).Nodup := by
    rw [show objs' = σ.objs.eraseIdx idx from rfl, map_eraseIdx]
    exact list_nodup_eraseIdx hnodup_objs idx
  have hwf_all' : ∀ q ∈ objs', q.Wf := fun q hq =>
    hwf_all q (mem_of_mem_eraseIdx_nodup hnodup_objs hidx hq).1
  have hclosed' : lcnfHeapClosed objs' := by
    intro q hq f hf hevf
    obtain ⟨hq_old, hq_ne⟩ := mem_of_mem_eraseIdx_nodup hnodup_objs hidx hq
    have hne : f ≠ bv := hchild_ne q hq_old (hwf_all q hq_old) (haddr ▸ hq_ne) f hf hevf
    obtain ⟨t, ht, hta⟩ := hclosed q hq_old f hf hevf
    exact ⟨t, mem_eraseIdx_of_addr_ne hidx ht (by rw [hta, haddr]; exact hne), hta⟩
  have hcap' : objs'.length ≤ st'.workCap := by
    have hlen : objs'.length ≤ σ.objs.length := by
      simp [objs', List.length_eraseIdx, hidx]
    have hwc : st'.workCap = σ.st.workCap := by
      simp [RtC0State.workCap, hmeta.2.2.2.2.2.1]
    omega
  have hrc_all' : ∀ q ∈ objs', q.rc.toNat < 2 ^ 31 - 1 := fun q hq =>
    hrc_all q (mem_of_mem_eraseIdx_nodup hnodup_objs hidx hq).1
  have hheap' : HeapClean rt σ' := ⟨⟨hbn', hwf_all', hclosed', hcap', hrc_all'⟩, hnodup_objs'⟩
  have hcf_count : ∀ a, a &&& 1#64 = 0#64 →
      List.count a (o.childFields.filter (fun f => f &&& 1#64 == 0#64)) =
        List.count a o.childFields := by
    intro a ha_ev
    simp [List.count_filter, ha_ev]
  have hcnt_fh : ∀ a, a &&& 1#64 = 0#64 → a ≠ bv →
      List.count a (frameHandles rf') =
        List.count a (frameHandles rf) + List.count a o.childFields := by
    intro a ha_ev hne
    have hlh : List.count a (localHandles ctx1 rf.envH) =
        List.count a (localHandles rf.ctx rf.envH) := by
      have hc := hperm_lh.count_eq a
      have hbva : (bv == a) = false := beq_false_of_ne hne.symm
      simp [List.count_append, List.count_cons, hbva] at hc
      omega
    simp only [frameHandles, rf', ghostH', List.count_append, hcf_count a ha_ev]
    omega
  have hnpre_diff : ∀ a, nonPersistRefs objs' a + List.count a o.childFields =
      nonPersistRefs σ.objs a := by
    intro a
    have hfoc := nonPersistRefs_focus σ.objs hidx a
    have honz : σ.objs[idx].rc ≠ 0#32 := by rw [horc1]; decide
    simp only [honz, ite_false] at hfoc
    dsimp only [o, objs']
    omega
  have hsound' : HandlesRcSound (frameHandles rf') objs' := by
    refine ⟨?_, ?_⟩
    · intro p hp hp0 f hf hevf
      obtain ⟨hp_old, hp_ne⟩ := mem_of_mem_eraseIdx_nodup hnodup_objs hidx hp
      have hne : f ≠ bv := hchild_ne p hp_old (hwf_all p hp_old) (haddr ▸ hp_ne) f hf hevf
      obtain ⟨q, hq, hqa, hq0⟩ := hsound.1 p hp_old hp0 f hf hevf
      exact ⟨q, mem_eraseIdx_of_addr_ne hidx hq (by rw [hqa, haddr]; exact hne), hqa, hq0⟩
    · intro y hy hypos
      obtain ⟨hy_old, hy_ne⟩ := mem_of_mem_eraseIdx_nodup hnodup_objs hidx hy
      have hy_ev : y.addr &&& 1#64 = 0#64 := obj_addr_and1_zero (hwf_all y hy_old)
      have hbase := hsound.2 y hy_old hypos
      rw [hcnt_fh y.addr hy_ev (haddr ▸ hy_ne)]
      have hd := hnpre_diff y.addr
      omega
  have hctx1_vars_ne : ∀ u ∈ ctx1.vars, u.isLive = true → (!u.ty.isScalar) = true →
      ∀ bvu, rf.envH u.id = some (u.ty, Word.i64 bvu) → bvu ≠ bv := by
    intro u hu hulive huns bvu henvu
    have hget_u : ctx1.get? u.id = some u := rcCtx_get?_of_mem hnodup' hu
    obtain ⟨w0, hw0, hw0_live, hw0_no, hw0_pers, hw0_ty, _, hw0_bor, _⟩ :=
      consumeVar_get?_live_back hnodup hclean hcons u.id hget_u hulive
    by_cases huid : u.id = v.id
    · exfalso
      have hw0_eq : w0 = v := by
        have := hw0; rw [huid, hxid, hget] at this; cases this; rfl
      have huown0 : u.owned = 0 := by
        have := hown_after v hget u (by rw [← hxid, ← huid]; exact hget_u)
        simp [hno, hpers, hown1] at this
        exact this
      have hubor : u.borrowed = false := by
        cases hbu : u.borrowed
        · rfl
        · have := hw0_bor hbu
          rw [hw0_eq] at this
          rw [this.1] at hvbor
          cases hvbor
      have hurk : u.resetTok = false := (hclean1 u hu).2.2.2.2
      rw [hw0_eq] at hw0_no hw0_pers
      simp [RcVar.isLive, hw0_no ▸ hno, hw0_pers ▸ hpers, huown0, hubor, hurk] at hulive
    · have hw0_id : w0.id = u.id := (RcCtx.get?_mem hw0).2
      have huns_w : (!decide (w0.ty.isScalar = true)) = true := by
        rw [hw0_ty]; cases hs : u.ty.isScalar <;> simp_all
      exact hlive_ne w0 (RcCtx.get?_mem hw0).1 (hw0_id ▸ huid) hw0_live huns_w bvu
        (hw0_id ▸ hw0_ty ▸ henvu)
  have hreach_erase : ∀ r a, r ≠ bv → NonPersistReach σ.objs r a →
      NonPersistReach objs' r a ∧ a ≠ bv := by
    intro r a hrne hreach
    simpa [haddr] using nonPersistReach_eraseIdx_of_ne hidx
      (by simpa [haddr] using hchild_ne) hwf_all (by simpa [haddr] using hrne) hreach
  have hne_ext : ∀ r, r ∈ rf.extH ++ rf.ghostH → r ≠ bv := by
    intro r hr heq
    have hpos : 0 < List.count r (rf.extH ++ rf.ghostH) := List.count_pos_iff.mpr hr
    rw [heq, List.count_append] at hpos
    rw [List.count_append, List.count_append] at hcnt0
    omega
  have hbk_lift : ∀ r1 r2 a, a ≠ bv →
      (∀ r, r ∈ r1 → r ∈ r2 ∧ r ≠ bv) → Backed σ.objs r1 a → Backed objs' r2 a := by
    intro r1 r2 a hne_a hsub hb
    rcases hb with ⟨o0, ho0, hoa0, ho0rc⟩ | ⟨r, hr, hreach⟩
    · exact Or.inl ⟨o0, mem_eraseIdx_of_addr_ne hidx ho0
        (by rw [hoa0, haddr]; exact hne_a), hoa0, ho0rc⟩
    · obtain ⟨hr2, hrne⟩ := hsub r hr
      exact Or.inr ⟨r, hr2, (hreach_erase r a hrne hreach).1⟩
  have hvars' : ∀ u ∈ ctx1.vars, VarInv u rf' σ'.objs := by
    intro u hu hulive
    obtain ⟨pu, wu, hp, hh, hrep, hnon⟩ := hinv1.2.2.2.1 u hu hulive
    have hrep_p : ∀ q ∈ σ.objs, q.Wf → q.addr ≠ bv → ∃ q' ∈ objs', ObjDataEq q q' :=
      fun q hq hqwf hqne =>
        ⟨q, mem_eraseIdx_of_addr_ne hidx hq (by rw [haddr]; exact hqne), objDataEq_refl q hqwf⟩
    have hrep_closed : ∀ q ∈ σ.objs, q.Wf → q.addr ≠ bv →
        ∀ f ∈ q.childFields, f &&& 1#64 = 0#64 → f ≠ bv :=
      fun q hq hqwf hqne f hf hevf => hchild_ne q hq hqwf hqne f hf hevf
    have hrep' : ValRep u.ty pu wu objs' := by
      refine valRep_mono_pred (P := fun a => a ≠ bv) hrep_p hrep_closed hrep ?_
      intro hns bvu hwu hevu
      exact hctx1_vars_ne u hu hulive (by simp [hns]) bvu (by simpa [hwu] using hh)
    refine ⟨pu, wu, hp, hh, hrep', ?_⟩
    intro hns
    obtain ⟨bvu, hwu, hno_u, hpers_u, hex_u, hbor_u⟩ := hnon hns
    have hne_bv : bvu ≠ bv :=
      hctx1_vars_ne u hu hulive (by simp [hns]) bvu (by simpa [hwu] using hh)
    refine ⟨bvu, hwu, hno_u, fun hp' hev' => ?_, ?_, ?_⟩
    · obtain ⟨q, hq, hqa, hq0⟩ := hpers_u hp' hev'
      exact ⟨q, mem_eraseIdx_of_addr_ne hidx hq (by rw [hqa, haddr]; exact hne_bv), hqa, hq0⟩
    · intro hexu
      obtain ⟨hxno, hxpers, hxown, hxo⟩ := hex_u hexu
      refine ⟨hxno, hxpers, hxown, fun hevu => ?_⟩
      obtain ⟨o_u, ho_u, ho_ua, ho_urc⟩ := hxo hevu
      exact ⟨o_u, mem_eraseIdx_of_addr_ne hidx ho_u (by rw [ho_ua, haddr]; exact hne_bv),
        ho_ua, ho_urc⟩
    · intro hno' hpers' hbor' hevu
      obtain ⟨hbk1, hbk2⟩ := hbor_u hno' hpers' hbor' hevu
      refine ⟨?_, ?_⟩
      · rcases hbk1 with ⟨o0, ho0, hoa0, ho0rc⟩ | ⟨r, hr, hreach⟩
        · exact Or.inl ⟨o0, mem_eraseIdx_of_addr_ne hidx ho0
            (by rw [hoa0, haddr]; exact hne_bv), hoa0, ho0rc⟩
        · by_cases hr_bv : r = bv
          · rw [hr_bv] at hr
            exfalso
            have hcnt_r : 0 < List.count bv (frameHandles { rf with ctx := ctx1 }) :=
              List.count_pos_iff.mpr hr
            have hcnt_lh0 : List.count bv (localHandles ctx1 rf.envH) = 0 := by
              have hc := hperm_lh.count_eq bv
              have htbv : (Word.i64 bv).toBV64? = some bv := rfl
              have hv_cnt : List.count bv (varHandles rf.envH v) = 1 := by
                simp [varHandles, hno, hpers, hrt, hown1, henvh_v, hbev, htbv]
              have hlh_old := localHandles_count_eq_add hnodup rf.envH hvm bv
              rw [List.count_append, List.count_append] at hcnt0
              have hc_one : List.count bv (localHandles ctx1 rf.envH ++ [bv]) =
                  List.count bv (localHandles ctx1 rf.envH) + 1 := by simp
              omega
            simp only [frameHandles, List.count_append] at hcnt_r
            rw [List.count_append, List.count_append] at hcnt0
            omega
          · refine Or.inr ⟨r, ?_, (hreach_erase r bvu hr_bv hreach).1⟩
            simp only [frameHandles, rf', ghostH', List.mem_append] at hr ⊢
            rcases hr with (hr_l | hr_e) | hr_g
            · exact Or.inl (Or.inl hr_l)
            · exact Or.inl (Or.inr hr_e)
            · exact Or.inr (Or.inr hr_g)
      · cases hpar : u.parent? with
        | none =>
          rw [hpar] at hbk2
          dsimp only at hbk2
          refine hbk_lift (rf.extH ++ rf.ghostH) (rf'.extH ++ rf'.ghostH) bvu hne_bv
            (fun r hr => ⟨?_, hne_ext r hr⟩) hbk2
          rcases List.mem_append.mp hr with hr_e | hr_g
          · exact List.mem_append.mpr (Or.inl hr_e)
          · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hr_g)))
        | some q =>
          rw [hpar] at hbk2
          dsimp only at hbk2
          obtain ⟨pv, hpv_mem, hpv_id, hpv_no, hpv_pers, hpv_pos, hpv_bk⟩ := hbk2
          refine ⟨pv, hpv_mem, hpv_id, hpv_no, hpv_pers, hpv_pos, ?_⟩
          refine hbk_lift _ _ bvu hne_bv (fun r hr => ?_) hpv_bk
          rw [List.mem_append] at hr
          rcases hr with hr_p | hr_eg
          · have hlive_pv : pv.isLive = true := by
              rcases hpv_pos with hp | hb
              · simp [RcVar.isLive, hpv_no, hpv_pers, hp]
              · simp [RcVar.isLive, hpv_no, hpv_pers, hb]
            have hns_pv : (!pv.ty.isScalar) = true :=
              not_isScalar_of_clean_noRc (hclean1 pv hpv_mem) hpv_no
            have hne_p : r ≠ bv := by
              cases hwp : rf.envH q with
              | none => simp [hwp] at hr_p
              | some wp =>
                simp only [hwp] at hr_p
                cases htb : wp.2.toBV64? with
                | none => simp [htb] at hr_p
                | some bp =>
                  simp only [htb, List.mem_singleton] at hr_p
                  have ⟨_, wu0, _, hwu0, _, hnon0⟩ := hinv1.2.2.2.1 pv hpv_mem hlive_pv
                  obtain ⟨bvp, hwp0, _⟩ := hnon0 (fun hs => by simp [hs] at hns_pv)
                  have hwu0' : rf.envH pv.id = some (pv.ty, Word.i64 bvp) := by
                    dsimp only at hwu0; rw [hwp0] at hwu0; exact hwu0
                  have hwp_eq : wp = (pv.ty, Word.i64 bvp) := by
                    have h := hwu0'; rw [hpv_id, hwp] at h; cases h; rfl
                  have hbp_eq : bp = bvp := by
                    have h := htb; rw [hwp_eq] at h
                    change some bvp = some bp at h
                    exact (Option.some.inj h).symm
                  rw [hr_p, hbp_eq]
                  exact hctx1_vars_ne pv hpv_mem hlive_pv hns_pv bvp hwu0'
            exact ⟨List.mem_append.mpr (Or.inl hr_p), hne_p⟩
          · refine ⟨List.mem_append.mpr (Or.inr (List.mem_append.mpr ?_)), hne_ext r hr_eg⟩
            rcases List.mem_append.mp hr_eg with hr_e | hr_g
            · exact Or.inl hr_e
            · exact Or.inr (List.mem_append.mpr (Or.inr hr_g))
  have hsp' : SharedPredInv rf' objs' := by
    intro p hp vb vs hgb hgs hblive hsno hspers
    have hsp1 := hinv1.2.2.2.2 p hp vb vs hgb hgs hblive hsno hspers
    refine ⟨fun htag => ?_, fun htag hspos => ?_⟩
    · obtain ⟨bvs, henvs, hevs, hrest⟩ := hsp1.1 htag
      refine ⟨bvs, henvs, hevs, fun hspos => ?_⟩
      obtain ⟨hc0, o_s, ho_s, ho_sa, ho_src⟩ := hrest hspos
      have hslive : vs.isLive = true := by simp [RcVar.isLive, hspos]
      have hns_s : (!vs.ty.isScalar) = true :=
        not_isScalar_of_clean_noRc (hclean1 vs (RcCtx.get?_mem hgs).1) hsno
      have hne_s : bvs ≠ bv := hctx1_vars_ne vs (RcCtx.get?_mem hgs).1 hslive hns_s bvs
        (by simpa [rf', (RcCtx.get?_mem hgs).2] using henvs)
      have ho_s' : o_s ∈ objs' :=
        mem_eraseIdx_of_addr_ne hidx ho_s (by rw [ho_sa, haddr]; exact hne_s)
      have hd := hnpre_diff bvs
      dsimp only at hc0
      rw [List.count_append, List.count_append] at hc0
      have hcf0 : List.count bvs o.childFields = 0 := by omega
      have hcf0' : List.count bvs (o.childFields.filter (fun f => f &&& 1#64 == 0#64)) = 0 := by
        rw [hcf_count bvs hevs]; exact hcf0
      refine ⟨?_, o_s, ho_s', ho_sa, ho_src⟩
      simp only [rf', ghostH', List.count_append]
      omega
    · obtain ⟨bvs, henvs, hevs, o_s, ho_s, ho_sa, horc⟩ := hsp1.2 htag hspos
      have hslive : vs.isLive = true := by simp [RcVar.isLive, hspos]
      have hns_s : (!vs.ty.isScalar) = true :=
        not_isScalar_of_clean_noRc (hclean1 vs (RcCtx.get?_mem hgs).1) hsno
      have hne_s : bvs ≠ bv := hctx1_vars_ne vs (RcCtx.get?_mem hgs).1 hslive hns_s bvs
        (by simpa [rf', (RcCtx.get?_mem hgs).2] using henvs)
      exact ⟨bvs, henvs, hevs, o_s,
        mem_eraseIdx_of_addr_ne hidx ho_s (by rw [ho_sa, haddr]; exact hne_s), ho_sa, horc⟩
  have hpcb' : ParentChildBacked rf' objs' := by
    intro u hu hulive huno hupers hubor q hpar bvu henvu hevu
    have hns_u : (!u.ty.isScalar) = true :=
      not_isScalar_of_clean_noRc (hclean1 u hu) huno
    have hne_u : bvu ≠ bv := hctx1_vars_ne u hu hulive hns_u bvu henvu
    rcases hpcb1 u hu hulive huno hupers hubor q hpar bvu henvu hevu with hext | hch
    · exact Or.inl (hbk_lift _ _ bvu hne_u (fun r hr => ⟨List.mem_append.mpr
        (by
          rw [List.mem_append] at hr
          rcases hr with hr_e | hr_g
          · exact Or.inl hr_e
          · exact Or.inr (List.mem_append.mpr (Or.inr hr_g))),
        hne_ext r hr⟩) hext)
    · right
      obtain ⟨wp, o_q, hwp, hqaddr, ho_q, o_mid, hom_m, hreach_mid, hcf⟩ := hch
      obtain ⟨pv, hpv_mem, hpv_id, hpv_no, hpv_pers, hpv_pos, _⟩ := hpo1 u hu q hpar
      have hlive_pv : pv.isLive = true := by simp [RcVar.isLive, hpv_pos]
      have hns_pv : (!pv.ty.isScalar) = true :=
        not_isScalar_of_clean_noRc (hclean1 pv hpv_mem) hpv_no
      obtain ⟨_, wu0, _, hwu0, _, hnon0⟩ := hinv1.2.2.2.1 pv hpv_mem hlive_pv
      obtain ⟨bvp, hwp0, _⟩ := hnon0 (fun hs => by simp [hs] at hns_pv)
      have hwu0' : rf.envH pv.id = some (pv.ty, Word.i64 bvp) := by
        dsimp only at hwu0; rw [hwp0] at hwu0; exact hwu0
      have hwp_eq : wp = (pv.ty, Word.i64 bvp) := by
        have h := hwu0'; rw [hpv_id, hwp] at h; cases h; rfl
      have hq_bv : o_q.addr = bvp := by
        have h := hqaddr; rw [hwp_eq] at h
        change some bvp = some o_q.addr at h
        exact (Option.some.inj h).symm
      have hne_q : o_q.addr ≠ bv := by
        rw [hq_bv]; exact hctx1_vars_ne pv hpv_mem hlive_pv hns_pv bvp hwu0'
      have ⟨hreach', hne_mid⟩ := hreach_erase o_q.addr o_mid.addr hne_q hreach_mid
      exact ⟨wp, o_q, hwp, hqaddr, mem_eraseIdx_of_addr_ne hidx ho_q (haddr ▸ hne_q),
        o_mid, mem_eraseIdx_of_addr_ne hidx hom_m (haddr ▸ hne_mid), hreach', hcf⟩
  have hhih' : HandlesInHeap (rf'.extH ++ rf'.ghostH) objs' := by
    intro a ha
    simp only [rf', ghostH', List.mem_append] at ha
    rcases ha with ha_e | (ha_cf | ha_g)
    · obtain ⟨q, hq, hqa⟩ := hhih a (List.mem_append.mpr (Or.inl ha_e))
      have hne := hne_ext a (List.mem_append.mpr (Or.inl ha_e))
      exact ⟨q, mem_eraseIdx_of_addr_ne hidx hq (by rw [hqa, haddr]; exact hne), hqa⟩
    · rw [List.mem_filter] at ha_cf
      obtain ⟨ha_mem, ha_bev⟩ := ha_cf
      have ha_ev : a &&& 1#64 = 0#64 := of_decide_eq_true ha_bev
      obtain ⟨q, hq, hqa⟩ := hclosed o (List.getElem_mem hidx) a ha_mem ha_ev
      have hne : a ≠ bv := fun heq => hnot_self (by simpa [haddr, heq] using ha_mem)
      exact ⟨q, mem_eraseIdx_of_addr_ne hidx hq (by rw [hqa, haddr]; exact hne), hqa⟩
    · obtain ⟨q, hq, hqa⟩ := hhih a (List.mem_append.mpr (Or.inr ha_g))
      have hne := hne_ext a (List.mem_append.mpr (Or.inr ha_g))
      exact ⟨q, mem_eraseIdx_of_addr_ne hidx hq (by rw [hqa, haddr]; exact hne), hqa⟩
  have hepres' : EntryPres rf0 σ0 rf' σ' := by
    obtain ⟨hhs0, hiso0, hext0, hgh0, hcnt0⟩ := hepres
    have hhs_step : HeapStepRel (rf0.extH ++ rf0.ghostH) σ σ' := by
      refine ⟨hmeta, rfl, rfl, fun q hq hqwf hbk => ?_, fun a hb => ?_⟩
      · have hbk_all : Backed σ.objs (localHandlesExcept rf.ctx rf.envH x ++ rf.extH ++ rf.ghostH)
            q.addr := by
          refine backed_mono_roots (fun r hr => ?_) hbk
          rw [List.mem_append] at hr
          rcases hr with hre | hrg
          · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (hext0 ▸ hre))))
          · exact List.mem_append.mpr (Or.inr (hgh0 r hrg))
        have hne := hbk_ne q.addr (hxid ▸ hbk_all)
        exact ⟨q, mem_eraseIdx_of_addr_ne hidx hq (haddr ▸ hne), objDataEq_refl q hqwf, id, id⟩
      · have hbk_all :
            Backed σ.objs (localHandlesExcept rf.ctx rf.envH x ++ rf.extH ++ rf.ghostH) a := by
          refine backed_mono_roots (fun r hr => ?_) hb
          rw [List.mem_append] at hr
          rcases hr with hre | hrg
          · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (hext0 ▸ hre))))
          · exact List.mem_append.mpr (Or.inr (hgh0 r hrg))
        have hne := hbk_ne a (hxid ▸ hbk_all)
        refine hbk_lift _ _ a hne (fun r hr => ⟨hr, hne_ext r ?_⟩) hb
        rw [List.mem_append] at hr ⊢
        rcases hr with hre | hrg
        · exact Or.inl (hext0 ▸ hre)
        · exact Or.inr (hgh0 r hrg)
    refine ⟨heapStepRel_trans hhs0 hhs_step, ?_, hext0,
      fun a ha => List.mem_append.mpr (Or.inr (hgh0 a ha)),
      fun a => by rw [List.count_append]; exact Nat.le_trans (hcnt0 a) (Nat.le_add_left _ _)⟩
    intro a ha hiso_a0
    obtain ⟨hiso_a, ha_rc1⟩ := hiso0 a ha hiso_a0
    obtain ⟨hiso_live, hiso_np, o_a, ho_a, ho_awf, ho_aa, ho_arc1⟩ := hiso_a
    have hnsv : !v.ty.isScalar = true := not_isScalar_of_clean_noRc (hclean v hvm) hno
    have hne_bv : bv ≠ a := fun heq =>
      hiso_live v hvm hlive hnsv (Word.i64 bv) henvh_v (by subst heq; rfl)
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro u hu hulive huns w hw
      have hget_u : ctx1.get? u.id = some u := rcCtx_get?_of_mem hnodup' hu
      obtain ⟨w0, hw0, hw0_live, _, _, hw0_ty, _⟩ :=
        consumeVar_get?_live_back hnodup hclean hcons u.id hget_u hulive
      have hw0_id : w0.id = u.id := (RcCtx.get?_mem hw0).2
      have hw' : rf.envH w0.id = some (w0.ty, w) := by
        dsimp only [rf'] at hw; rw [hw0_id, hw0_ty]; exact hw
      exact hiso_live w0 (RcCtx.get?_mem hw0).1 hw0_live (hw0_ty ▸ huns) w hw'
    · dsimp only [σ']
      have hd := hnpre_diff a; omega
    · exact ⟨o_a, mem_eraseIdx_of_addr_ne hidx ho_a (by rw [ho_aa, haddr]; exact hne_bv.symm),
        ho_awf, ho_aa, ho_arc1⟩
    · intro q0 hq0 hqa0
      obtain ⟨q, hq, hdeq, hq1⟩ := ha_rc1 q0 hq0 hqa0
      exact ⟨q, mem_eraseIdx_of_addr_ne hidx hq
        (by rw [hdeq.1, hqa0, haddr]; exact hne_bv.symm), hdeq, hq1⟩
  exact ⟨⟨hheap', hnodup', hsound', hvars', hsp'⟩, hclean1, hpo1, hnorc',
    hpcb', hsth', hhih', hepres'⟩

/-- Stepwise simulation for `LcCode.del` exposing the exact post-step `RcFrame`. -/
public theorem del_step_ctx {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {J : HJEnv} {Jp : PResJEnv}
    {Q : PResPost} {Xp : PResXPost} {Qh : HPost} {Xh : HXPost}
    {jps : List RcJpInfo} {rf rf0 : RcFrame} {σ σ0 : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr : Nat}
    {x : Nat} {k : LcCode}
    (hwf : perceusCodeWf env retTy jps rf.ctx sm (LcCode.del x k) = true)
    (hchk : rf.ctx.checkExcl x "del" = Except.ok ())
    (hpr : PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Q Xp (LcCode.del x k))
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ) (hres : ResStateInv σ rem wr rcr)
    (hk : ∀ {rf' : RcFrame} {σ' : HState},
      perceusCodeWf env retTy jps rf'.ctx (sm.filter (fun p => p.1 != x)) k = true →
      PRWp m env retTy Δr jps rf'.ctx Jp ρP rem wr rcr Q Xp k →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs →
      EntryPres rf0 σ0 rf' σ' → ResStateInv σ' rem wr rcr →
      (∀ q' ∈ σ'.objs, ∀ q ∈ σ.objs, q'.addr = q.addr → ObjDataEq q q') →
      rf'.envP = rf.envP ∧ rf'.envH = rf.envH ∧ rf'.extH = rf.extH ∧
        rf.ctx.consumeVar x = .ok rf'.ctx →
      HWp Δh rt retTy J rf'.envH Qh Xh k σ') :
    HWp Δh rt retTy J rf.envH Qh Xh (LcCode.del x k) σ := by
  rw [perceusCodeWf.eq_17] at hwf
  rw [PRWp.eq_13] at hpr
  rw [HWp.eq_13]
  cases hcons : rf.ctx.consumeVar x with
  | error e => simp [hcons] at hwf
  | ok ctx1 =>
    simp only [hcons] at hwf hpr
    have hnodup := hinv.2.1
    have hnodup_objs := hinv.1.2
    have hwf_all := hinv.1.1.2.1
    simp only [RcCtx.checkExcl] at hchk
    cases hget : rf.ctx.get? x with
    | none => simp [hget] at hchk
    | some v =>
      simp only [hget] at hchk
      by_cases hno : v.noRc = true
      · simp [hno] at hchk
      have hnof : v.noRc = false := by cases h : v.noRc <;> simp_all
      by_cases hpers : v.persistent = true
      · simp [hnof, hpers] at hchk
      have hpersf : v.persistent = false := by cases h : v.persistent <;> simp_all
      by_cases hrtok : v.resetTok = true
      · simp [hnof, hpersf, hrtok] at hchk
      have hrtf : v.resetTok = false := by cases h : v.resetTok <;> simp_all
      by_cases hown1 : v.owned = 1
      · by_cases hex : v.excl = true
        · obtain ⟨hvm, hxid⟩ := RcCtx.get?_mem hget
          have hlive : v.isLive = true := by simp [RcVar.isLive, hown1]
          have hnonsc : ¬v.ty.isScalar = true :=
            fun hs => by have := (hclean v hvm).1.2 hs; simp [hnof] at this
          obtain ⟨_, wu, _, hwu, _, hnon⟩ := hinv.2.2.2.1 v hvm hlive
          obtain ⟨bv, hwbv, _, _, hex_v, _⟩ := hnon hnonsc
          have henvh : rf.envH x = some (v.ty, Word.i64 bv) := by
            rw [← hxid, hwu, hwbv]
          have hgbv : rf.envH.getBV64? x = some bv := by
            have htbv : (Word.i64 bv).toBV64? = some bv := rfl
            simp [HValEnv.getBV64?, HValEnv.evalArgOwn, henvh, htbv]
          rw [hgbv]
          by_cases hev : bv &&& 1#64 = 0#64
          · simp only [hev, ne_eq, not_true_eq_false, ite_false]
            obtain ⟨_, _, _, ho_ex⟩ := hex_v hex
            obtain ⟨o, ho, hoa, horc1⟩ := ho_ex hev
            obtain ⟨idx, hidx, hget_idx⟩ := obj_mem_idx ho
            refine ⟨idx, hidx, hget_idx ▸ hoa, fun st' hmeta hrem hwb => ?_⟩
            have hcore := del_heap_rcInv hinv hclean hpo hnorc hpcb hsth hhih hepres
              hget hcons hnof hpersf hrtf hown1 hex henvh hev hidx (hget_idx ▸ hoa)
              (hget_idx ▸ horc1) hmeta
            obtain ⟨hinv', hclean', hpo', hnorc', hpcb', hsth', hhih', hepres'⟩ := hcore
            let objs' := σ.objs.eraseIdx idx
            let σ' : HState :=
              { st := st', objs := objs', scr := σ.scr, scrLimbs := σ.scrLimbs }
            have hres' : ResStateInv σ' rem wr rcr := by
              refine ⟨?_, ?_, ?_⟩
              · rw [hrem]; exact hres.1
              · have hlen : objs'.length ≤ σ.objs.length := by
                  simp [objs', List.length_eraseIdx, hidx]
                have hwc : st'.workCap = σ.st.workCap := by
                  simp [RtC0State.workCap, hmeta.2.2.2.2.2.1]
                have := hres.2.1; simp only [σ']; omega
              · have hm := maxObjRc_eraseIdx_le σ.objs idx
                have hmax_le : Nat.max 1 (maxObjRc (σ.objs.eraseIdx idx)) ≤
                    Nat.max 1 (maxObjRc σ.objs) :=
                  Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hm (Nat.le_max_right _ _)⟩
                have := hres.2.2; simp only [σ', objs']; omega
            have hdeq : ∀ q' ∈ σ'.objs, ∀ q ∈ σ.objs, q'.addr = q.addr → ObjDataEq q q' := by
              intro q' hq' q hq hqa
              have hq'_old := (mem_of_mem_eraseIdx_nodup hnodup_objs hidx hq').1
              have hqeq := obj_eq_of_addr_nodup hnodup_objs hq hq'_old hqa.symm
              subst hqeq; exact objDataEq_refl q (hwf_all q hq)
            let ghostH' := (σ.objs[idx].childFields.filter (· &&& 1#64 == 0#64)) ++ rf.ghostH
            let rf' : RcFrame := { rf with ctx := ctx1, ghostH := ghostH' }
            exact hk (rf' := rf') (σ' := σ')
              hwf hpr hinv' hclean' hpo' hnorc' hpcb' hsth' hhih' hepres' hres' hdeq
              ⟨rfl, rfl, rfl, hcons⟩
          · simp only [hev, ne_eq, not_false_eq_true, ite_true]
            have hsh_sub : ∀ p ∈ rf.ctx.sharedPreds, p.2 = x →
                ∀ v0, rf.ctx.get? x = some v0 →
                  v0.noRc = true ∨ v0.persistent = true ∨ 1 = 0 ∨ v0.owned ≤ 1 := by
              intro _ _ _ v0 hg0
              rw [hg0] at hget; cases hget
              exact Or.inr (Or.inr (Or.inr (by omega)))
            obtain ⟨_, _, hinv1, hclean1, hpo1, _⟩ :=
              rcInv_consumeVar_step hinv hclean hpo hcons hsh_sub
            have hnorc' := noRcCorrect_consumeVar hnodup hnorc hcons
            have hpcb' := parentChildBacked_consumeVar hnodup hclean hcons hpcb
            have hsth' := sharedTargetsHeap_consumeVar hnodup hsth hcons
            have hepres' := entryPres_consumeVar hnodup hclean hcons hepres
            exact hk (rf' := { rf with ctx := ctx1 }) (σ' := σ)
              hwf hpr hinv1 hclean1 hpo1 hnorc' hpcb' hsth' hhih hepres' hres
              (fun _ hq' q hq hqa => by
                have hqeq := obj_eq_of_addr_nodup hnodup_objs hq' hq hqa
                rw [hqeq]; exact objDataEq_refl q (hwf_all q hq))
              ⟨rfl, rfl, rfl, hcons⟩
        · have hexf : v.excl = false := by cases h : v.excl <;> simp_all
          simp [hnof, hpersf, hrtf, hown1, hexf] at hchk
      · have hne1 : (v.owned != 1) = true := by simp [hown1]
        simp [hnof, hpersf, hrtf, hne1] at hchk

/-- Stepwise simulation for `LcCode.del`: advances `HWp` given `perceusCodeWf`, `checkExcl`,
    `PRWp`, and the Perceus frame/resource invariants. -/
public theorem del_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {J : HJEnv} {Jp : PResJEnv}
    {Q : PResPost} {Xp : PResXPost} {Qh : HPost} {Xh : HXPost}
    {jps : List RcJpInfo} {rf rf0 : RcFrame} {σ σ0 : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr : Nat}
    {x : Nat} {k : LcCode}
    (hwf : perceusCodeWf env retTy jps rf.ctx sm (LcCode.del x k) = true)
    (hchk : rf.ctx.checkExcl x "del" = Except.ok ())
    (hpr : PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Q Xp (LcCode.del x k))
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ) (hres : ResStateInv σ rem wr rcr)
    (hk : ∀ {rf' : RcFrame} {σ' : HState},
      perceusCodeWf env retTy jps rf'.ctx (sm.filter (fun p => p.1 != x)) k = true →
      PRWp m env retTy Δr jps rf'.ctx Jp ρP rem wr rcr Q Xp k →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs →
      EntryPres rf0 σ0 rf' σ' → ResStateInv σ' rem wr rcr →
      (∀ q' ∈ σ'.objs, ∀ q ∈ σ.objs, q'.addr = q.addr → ObjDataEq q q') →
      HWp Δh rt retTy J rf'.envH Qh Xh k σ') :
    HWp Δh rt retTy J rf.envH Qh Xh (LcCode.del x k) σ :=
  del_step_ctx hwf hchk hpr hinv hclean hpo hnorc hpcb hsth hhih hepres hres
    fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 _ => hk h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

end DelStep

end LeanQbe.T.LeanLCNF.Sem
