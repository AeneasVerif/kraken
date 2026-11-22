module

public import LeanQbe.T.Bootstrap0.Sound0Part7

/-!
# Bootstrap Stage B (`Sound0Part8`): `.jnz` / `.group` Lockstep & `compileFn0_maxSlots_lt`

Completes the full lockstep `PrePass0` ↔ `Rega0` proof started in `Sound0Part7`:
* `regaStep0_jnz`: `.jnz` branch target labels, condition release, and `seenJnz := true`.
* `regaStep0_group`: empty and single-block `.group [(pts, b)] k` with Bug C `ctrl.lblSlots.size`
  alignment, `slotsOfVids0` target tracking, and `waiting` protection across `work`.
* `regaStep0_lockstep`, `regaRunAux0_lockstep`, and `compileFn0_maxSlots_lt`
  (x64-only `Compiler0` verification targeting `LeanQbe.T.Amd64.ScalarTarg` via `Sound0Part1`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T

theorem regaStep0_jnz {ctx : LegalCtx0} {fnIdx : UInt32} {fnMaxJump : Nat}
    {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0} {curPre : PreItem0}
    {restPre : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {rest : List RegaTask0} {mCur : TaskMeta0} {restMeta : List TaskMeta0}
    {c : Arg0} {t e : TFlat0}
    (h : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: restPre) seenJnz st ctrl
      (cur :: rest) (mCur :: restMeta))
    (hnd : cur.node = .jnz c t e) :
    let st0 := regaPrependLbl0 cur st ctrl
    let ls := regaStep0 preRes.escaped cur st0 ctrl rest
    let preSt1 := preNoteNode0 curPre.scope curPre.venv curPre.node preSt
    let out := preStepPush0 curPre preSt1 nextSc restPre
    let mB := TaskMeta0.mk mCur.vT mCur.lT mCur.gl none
    RegaStepInv0 ctx fnIdx fnMaxJump preRes out.nextScope out.st out.work true
      ls.st ls.ctrl ls.work (mB :: mB :: restMeta) := by
  intro st0 ls preSt1 out mB
  have hcur_ok := h.items_ok 0 (by simp) (by simp) (by simp)
  dsimp only [List.getElem_cons_zero] at hcur_ok
  obtain ⟨hpn, hpv, hvlen, hvlt, hllen, hgl, hgi, hwf, hfit, hsbg, hnb, hpool, hnxt_nv,
    hinfo_ok, hwait, hentry, hlive⟩ := hcur_ok
  have hpn_j : curPre.node = .jnz c t e := hpn.trans hnd
  rw [hnd] at hwf hfit hsbg hnb
  have ⟨_, hwft, hwfe⟩ :
      checkArg0 mCur.vT .bool c = true ∧ WfNode0 ctx mCur.vT mCur.lT t ∧
        WfNode0 ctx mCur.vT mCur.lT e := by
    cases hwf; exact ⟨‹_›, ‹_›, ‹_›⟩
  dsimp only [TFlat0.sigLensFitU32] at hfit; rw [Bool.and_eq_true] at hfit
  dsimp only [TFlat0.singleBlockGroups] at hsbg; rw [Bool.and_eq_true] at hsbg
  dsimp only [TFlat0.noNegBool] at hnb; rw [Bool.and_eq_true] at hnb
  have hsub := preRunAux0_sub_active h.pre_inv h.pre_run
  obtain ⟨_, hpr_noesc⟩ := hsub
  have hp_inv := h.pre_inv.items_ok curPre List.mem_cons_self
  obtain ⟨vT', lT', hvlen', hvlt', hwf', _, _, _⟩ := hp_inv
  have hst1 := preNoteNode0_spec curPre.scope curPre.venv curPre.node preSt
    h.pre_inv.defScope_sz h.pre_inv.uses_sz h.pre_inv.escaped_sz hvlt'
    (hvlen' ▸ wfNode0_nodeArgsInVenv0 hwf')
    (fun v hv => by
      have hb := h.pre_inv.uses_bound v hv
      rw [List.map_cons] at hb; dsimp only [workArgCount0] at hb
      omega)
    (fun v hv => Nat.lt_trans (h.pre_inv.defScope_lt v hv) (UInt32.toNat_lt nextSc))
    h.pre_inv.escaped_bit
  dsimp only at hst1
  have hout : out = PreOut0.mk preSt1 (nextSc + 2)
      (PreItem0.mk e curPre.venv (nextSc + 1) ::
        PreItem0.mk t curPre.venv nextSc :: restPre) := by
    dsimp only [out, preStepPush0]; simp [isTerm0, preStepJnz0, hpn_j]
  have hsc_ub : nextSc.toNat + 2 * (1 + nodeCount0 t + nodeCount0 e +
      workNodeCount0 (restPre.map PreItem0.node)) < 2 ^ 31 := by
    have := h.pre_inv.nextSc_bound
    rw [List.map_cons, hpn_j] at this
    dsimp only [workNodeCount0, nodeCount0] at this; exact this
  have hsc1 : (nextSc + 1).toNat = nextSc.toNat + 1 := u32_add1_toNat7 (by omega)
  have hsc2 : (nextSc + 2).toNat = nextSc.toNat + 2 := u32_add_ofNat_lt7 (m := 2) (by omega)
  have hrest_scopes : ∀ p ∈ restPre, p.scope ≠ curPre.scope := by
    have hnd_sc := h.pre_inv.scopes_nodup
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd_sc
    exact hnd_sc.1
  have hrest_nodup : (restPre.map PreItem0.scope).Nodup := by
    have hnd_sc := h.pre_inv.scopes_nodup
    simp only [List.map_cons, List.nodup_cons] at hnd_sc
    exact hnd_sc.2
  have hrest_lt : ∀ p ∈ restPre, p.scope.toNat < nextSc.toNat := fun p hp =>
    h.pre_inv.scopes_lt p (List.mem_cons_of_mem _ hp)
  have hnd_scopes : ([nextSc + 1, nextSc] ++ restPre.map PreItem0.scope).Nodup := by
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, hrest_nodup⟩⟩
    · intro hm; rcases List.mem_cons.mp hm with h1 | h1
      · have := congrArg UInt32.toNat h1; omega
      · obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h1
        have := hrest_lt p hp; have := congrArg UInt32.toNat hpe; omega
    · intro hm; obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
      have := hrest_lt p hp; have := congrArg UInt32.toNat hpe; omega
  have hpre_inv' : PreWorkInv0 ctx out.nextScope out.st out.work := by
    rw [hout]; dsimp only
    refine ⟨hst1.1 ▸ hst1.2.1.symm ▸ h.pre_inv.defScope_sz,
      hst1.1 ▸ hst1.2.2.1, hst1.1 ▸ hst1.2.2.2.1,
      fun v hv => by have := h.pre_inv.defScope_lt v (hst1.1 ▸ hv); rw [hst1.2.1]; omega,
      fun v hv => hst1.2.2.2.2.1 v (hst1.1 ▸ hv),
      by simpa only [List.map_cons, List.cons_append, List.nil_append] using hnd_scopes,
      fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp1
        · dsimp only; omega
        · rcases List.mem_cons.mp hp1 with rfl | hp2
          · dsimp only; omega
          · have := hrest_lt p hp2; omega,
      fun p hp => by
        rw [hst1.1]; rcases List.mem_cons.mp hp with rfl | hp1
        · exact ⟨mCur.vT, mCur.lT, by rw [hpv, hvlen],
            fun v hm => by rw [hpv] at hm; exact h.st_nv ▸ hvlt v hm,
            hwfe, hfit.2, hsbg.2, hnb.2⟩
        · rcases List.mem_cons.mp hp1 with rfl | hp2
          · exact ⟨mCur.vT, mCur.lT, by rw [hpv, hvlen],
              fun v hm => by rw [hpv] at hm; exact h.st_nv ▸ hvlt v hm,
              hwft, hfit.1, hsbg.1, hnb.1⟩
          · exact h.pre_inv.items_ok p (List.mem_cons_of_mem _ hp2),
      by rw [hst1.1]; have := h.pre_inv.nextVid_bound
         rw [List.map_cons, hpn_j] at this; simp only [List.map_cons]
         dsimp only [workBinderCount0, binderCount0] at this ⊢; omega,
      by have := hsc_ub; simp only [List.map_cons]; dsimp only [workNodeCount0]; omega,
      by have := h.pre_inv.argCount_bound
         rw [List.map_cons, hpn_j] at this; simp only [List.map_cons]
         dsimp only [workArgCount0, argCount0] at this ⊢; omega,
      fun v hv => by
        rw [hst1.1] at hv
        have hv1 := hst1.2.2.2.2.2 v hv
        have hau : argUses0 (UInt32.ofNat v) curPre.venv c ≤ 1 := by
          cases c <;> simp [argUses0] <;> try split <;> omega
        have hb := h.pre_inv.uses_bound v hv
        rw [List.map_cons, hpn_j] at hb; dsimp only [workArgCount0, argCount0] at hb
        split at hv1
        · rw [hv1.1]; dsimp only [nodeArgsUses0]; rw [hpn_j]; dsimp only [nodeArgsUses0]
          simp only [List.map_cons]; dsimp only [workArgCount0]; omega
        · rw [hv1.1]; simp only [List.map_cons]; dsimp only [workArgCount0]; omega⟩
  have hpre_run' : (preRunAux0 (UInt32.ofNat (workNodeCount0 (out.work.map PreItem0.node)))
      out.nextScope out.st out.work).2 = preRes :=
    preRun_step_eq7 h.pre_inv.nextSc_bound h.pre_run
  have hst0_eqs : st0.nextVid = st.nextVid ∧ st0.maxSlots = st.maxSlots ∧
      st0.vslot = st.vslot ∧ st0.remUses = st.remUses := by
    dsimp only [st0, regaPrependLbl0]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  let rd := jnzPrep0 preRes.escaped c cur st0 ctrl
  let st2 : RegaSt0 := { st0 with remUses := rd.1.remUses, revDirs := rd.2 }
  let ctrl2 : CtrlSt0 :=
    { ctrl with nextLbl := ctrl.nextLbl + 1, lblSlots := ctrl.lblSlots.push [] }
  let tTask := RegaTask0.mk ctrl.nextLbl t cur.venv cur.lenv rd.1.free cur.nextSlot
  let eTask := RegaTask0.mk 0 e cur.venv cur.lenv rd.1.free cur.nextSlot
  have hst2_eqs : st2.nextVid = st.nextVid ∧ st2.maxSlots = st.maxSlots ∧
      st2.vslot = st.vslot := ⟨hst0_eqs.1, hst0_eqs.2.1, hst0_eqs.2.2.1⟩
  have hlen_rest : restPre.length = rest.length := by simpa using h.len_pw
  have hlen_mrest : restMeta.length = rest.length := by simpa using h.len_mw
  have hls_eq : ls.st = st2 ∧ ls.ctrl = ctrl2 ∧ ls.work = eTask :: tTask :: rest := by
    dsimp only [ls, regaStep0]; rw [hnd]
    dsimp only [stepJnzPush0, jnzBuildSt0, jnzWrapRes0, st2, ctrl2, tTask, eTask, rd]
    exact ⟨rfl, rfl, rfl⟩
  have hrel := releaseArg0_spec preRes.escaped st0.vslot cur.venv ⟨st0.remUses, cur.freeSlots⟩ c
    preRes.nextVid.toNat cur.nextSlot (by have := h.preRes_nv; omega)
    (ActiveDefScope0 preSt (curPre :: restPre))
    (by rw [hst0_eqs.2.2.2]; exact h.st_rem_sz)
    (fun v hv => Nat.lt_of_lt_of_le (hvlt v hv) (by have := h.preRes_uses_lt_bd; omega))
    (by have hva := wfNode0_nodeArgsInVenv0 hwf; rw [← hvlen] at hva; exact hva)
    (fun idx heq hesc => by
      subst heq
      have hva := wfNode0_nodeArgsInVenv0 hwf; rw [← hvlen] at hva
      have hidx := hva idx rfl
      have hvid_mem : listGetU32 cur.venv idx ∈ cur.venv := by
        rw [listGetU32_eq_listGetD, listGetD_eq_getElem7 _ _ _ hidx]; exact List.getElem_mem _
      have hv_st : (listGetU32 cur.venv idx).toNat < preSt.nextVid.toNat :=
        h.st_nv ▸ hvlt _ hvid_mem
      refine ⟨hv_st, curPre, List.mem_cons_self, ?_⟩
      by_cases he : curPre.scope.toNat = preSt.defScope.getD (listGetU32 cur.venv idx).toNat 0
      · exact he
      · exfalso
        have h0 := hpr_noesc _ hv_st hesc curPre List.mem_cons_self
        simp only [he, ↓reduceIte, hpn_j, hpv, ← h.st_nv] at h0
        have hnz := nodeArgsUses0_zero_of_astZero h0
        dsimp only [nodeArgsUses0] at hnz
        have hev : argUses0 (UInt32.ofNat (listGetU32 cur.venv idx).toNat) cur.venv (.var idx) =
            1 := by simp [argUses0, UInt32.ofNat_toNat]
        omega)
    h.preRes_es_bit
    (fun v hv => by
      rw [hst0_eqs.2.2.2]
      exact Nat.lt_of_le_of_lt (h.st_rem_le v hv) (h.preRes_us_bd v hv))
    (fun v hv hesc => by
      rw [hst0_eqs.2.2.2]
      by_cases hpos : 0 < argUses0 (UInt32.ofNat v) cur.venv c
      · have hact : ActiveDefScope0 preSt (curPre :: restPre) v := by
          have hv_st : v < preSt.nextVid.toNat := Nat.lt_of_not_le fun hge => False.elim <| by
            have h0 : argUses0 (UInt32.ofNat v) cur.venv c = 0 := by
              cases c with
              | immBool _ | immBits _ _ => rfl
              | var idx =>
                dsimp only [argUses0]
                have hva := wfNode0_nodeArgsInVenv0 hwf; rw [← hvlen] at hva
                have hlt := hvlt (listGetU32 cur.venv idx) (by
                  rw [listGetU32_eq_listGetD, listGetD_eq_getElem7 _ _ _ (hva idx rfl)]
                  exact List.getElem_mem _)
                have hne : listGetU32 cur.venv idx ≠ UInt32.ofNat v := fun he => by
                  have hn := congrArg UInt32.toNat he
                  have hnv_lt : v < 2 ^ 32 :=
                    Nat.lt_trans hv (Nat.lt_trans h.preRes_nv (by decide : 2 ^ 31 < 2 ^ 32))
                  rw [u32_toNat_ofNat7, Nat.mod_eq_of_lt hnv_lt] at hn
                  rw [h.st_nv] at hlt; omega
                simp [hne]
            omega
          refine ⟨hv_st, curPre, List.mem_cons_self, ?_⟩
          by_cases he : curPre.scope.toNat = preSt.defScope.getD v 0
          · exact he
          · exfalso
            have h0 := hpr_noesc v hv_st hesc curPre List.mem_cons_self
            simp only [he, ↓reduceIte, hpn_j, hpv, ← h.st_nv] at h0
            have hnz := nodeArgsUses0_zero_of_astZero h0
            dsimp only [nodeArgsUses0] at hnz; omega
        have hsc : curPre.scope.toNat = preSt.defScope.getD v 0 := by
          by_cases he : curPre.scope.toNat = preSt.defScope.getD v 0
          · exact he
          · exfalso
            have h0 := hpr_noesc v hact.1 hesc curPre List.mem_cons_self
            simp only [he, ↓reduceIte, hpn_j, hpv, ← h.st_nv] at h0
            have hnz := nodeArgsUses0_zero_of_astZero h0
            dsimp only [nodeArgsUses0] at hnz; omega
        rw [h.st_rem_active v (h.st_nv ▸ hact.1) hesc hact]
        dsimp only [sameScopeSpineSum0]
        rw [hsc.symm]; simp only [↓reduceIte]
        rw [hpv, hpn_j, ← h.st_nv]; dsimp only [spineUses0, nodeArgsUses0]
        omega
      · omega)
    (fun v hv hDv hev hrv => by
      dsimp only at hrv ⊢
      rw [hst0_eqs.2.2.2] at hrv
      simp only [hst0_eqs.2.2.1, hst0_eqs.2.2.2]
      exact activeDefScope0_live_slots_ok h v hv hDv hev hrv)
    hpool.1 hpool.2.1
  have hrd1 :
      rd.1 = releaseArg0 preRes.escaped st0.vslot cur.venv ⟨st0.remUses, cur.freeSlots⟩ c := rfl
  rw [← hrd1] at hrel
  change rd.1.remUses.size = preRes.nextVid.toNat ∧ _ at hrel
  have hfree_no_esc1 : ∀ v < st.nextVid.toNat,
      preRes.escaped.getD v 0 = 1 → UInt32.ofNat v ∈ cur.venv →
      arrGetU0 st.vslot (UInt32.ofNat v) ∉ rd.1.free := by
    intro v hv hesc1 hvmem hm
    have hlv : LiveInTask0 preRes.escaped preSt st curPre cur v := Or.inl ⟨hesc1, hvmem⟩
    rcases (hrel.2.2.2.2.1 _).mp hm with hc | ⟨u, hu, hDu, hescu, hposu, hzu, heq⟩
    · exact (hlive v hv hlv).2.1 hc
    · rw [hst0_eqs.2.2.1] at heq
      dsimp only at hposu; rw [hst0_eqs.2.2.2] at hposu
      have hu_lt : u < st.nextVid.toNat := h.st_nv ▸ hDu.1
      have hne : u ≠ v := fun he => by subst he; rw [hesc1] at hescu; cases hescu
      have hrs := hrel.2.2.2.1 u hu
      dsimp only at hrs
      rw [hst0_eqs.2.2.2, hzu] at hrs
      simp only [hescu, ↓reduceIte] at hrs
      have hpos_nu : 0 < argUses0 (UInt32.ofNat u) cur.venv c := by omega
      have hsc_u : curPre.scope.toNat = preSt.defScope.getD u 0 := by
        by_cases he : curPre.scope.toNat = preSt.defScope.getD u 0
        · exact he
        · exfalso
          have hp0 := hpr_noesc u (h.st_nv ▸ hu_lt) hescu curPre List.mem_cons_self
          simp only [he, ↓reduceIte, hpn_j, hpv, ← h.st_nv] at hp0
          have hnz := nodeArgsUses0_zero_of_astZero hp0
          dsimp only [nodeArgsUses0] at hnz; omega
      exact (hlive v hv hlv).2.2 u hu_lt hne (Or.inr ⟨hescu, hsc_u, hposu⟩) heq.symm
  have hfree_no_wait : ∀ info ∈ mCur.gl, info.waiting = true →
      ∀ s ∈ info.tgts, s ∉ rd.1.free := by
    intro info hi hw s hs hm
    rcases (hrel.2.2.2.2.1 _).mp hm with hc | ⟨u, hu, hDu, hescu, hposu, hzu, rfl⟩
    · exact (hwait info hi hw).1 s hs |>.2 hc
    · rw [hst0_eqs.2.2.1] at hs
      dsimp only at hposu; rw [hst0_eqs.2.2.2] at hposu
      have hu_lt : u < st.nextVid.toNat := h.st_nv ▸ hDu.1
      have hsc_u : curPre.scope.toNat = preSt.defScope.getD u 0 := by
        have hrs := hrel.2.2.2.1 u hu
        dsimp only at hrs
        rw [hst0_eqs.2.2.2, hzu] at hrs
        simp only [hescu, ↓reduceIte] at hrs
        by_cases he : curPre.scope.toNat = preSt.defScope.getD u 0
        · exact he
        · exfalso
          have hp0 := hpr_noesc u (h.st_nv ▸ hu_lt) hescu curPre List.mem_cons_self
          simp only [he, ↓reduceIte, hpn_j, hpv, ← h.st_nv] at hp0
          have hnz := nodeArgsUses0_zero_of_astZero hp0
          dsimp only [nodeArgsUses0] at hnz; omega
      exact (hwait info hi hw).2 u hu_lt (Or.inr ⟨hescu, hsc_u, hposu⟩) hs
  have hlive_branch' : ∀ (lbl : UInt32) (sc : UInt32), nextSc.toNat ≤ sc.toNat →
      ∀ (nd : TFlat0) (fr : List UInt32) (v : Nat), v < st.nextVid.toNat →
      LiveInTask0 preRes.escaped preSt1 st2 ⟨nd, curPre.venv, sc⟩
        ⟨lbl, nd, cur.venv, cur.lenv, fr, cur.nextSlot⟩ v →
      preRes.escaped.getD v 0 = 1 ∧ UInt32.ofNat v ∈ cur.venv := by
    intro _ sc hsc _ _ v hv hlv
    rcases hlv with ⟨hes, hvmem⟩ | ⟨_, hsc_v, _⟩
    · exact ⟨hes, hvmem⟩
    · have := h.pre_inv.defScope_lt v (h.st_nv ▸ hv)
      rw [hst1.2.1] at hsc_v; dsimp only at hsc_v; omega
  have hnl1 : (ctrl.nextLbl + 1).toNat = ctrl.nextLbl.toNat + 1 :=
    u32_add1_toNat7 (by
      have := h.ctrl_nl
      rw [List.map_cons, hnd] at this; dsimp only [workNodeCount0, nodeCount0] at this; omega)
  have hctrl2_lt : ctrl.nextLbl.toNat ≤ ctrl2.nextLbl.toNat := by dsimp only [ctrl2]; omega
  have hctrl2_get_old : ∀ l, 1 ≤ l → l < ctrl.nextLbl.toNat →
      ctrl2.lblSlots.getD l [] = ctrl.lblSlots.getD l [] := by
    intro l _ hl
    dsimp only [ctrl2]
    rw [arrPush_getD7, h.seenJnz_ctrl]
    simp [hl]
  have htm_branch : ∀ (lbl : UInt32) (sc : UInt32) (nd : TFlat0),
      nextSc.toNat ≤ sc.toNat → WfNode0 ctx mCur.vT mCur.lT nd → nd.sigLensFitU32 = true →
      nd.singleBlockGroups = true → nd.noNegBool = true →
      TaskMetaOk0 ctx (preRes.nextVid.toNat + fnMaxJump) preRes.escaped preSt1 st2 ctrl2
        ⟨nd, curPre.venv, sc⟩ ⟨lbl, nd, cur.venv, cur.lenv, rd.1.free, cur.nextSlot⟩ mB := by
    intro lbl sc nd hsc hwfb hfitb hsbgb hnbb
    refine ⟨rfl, hpv, hvlen, fun v hv => by rw [hst2_eqs.1]; exact hvlt v hv,
      hllen, hgl, fun k h1 h2 h3 => hgi k h1 h2 h3, hwfb, hfitb, hsbgb, hnbb,
      ⟨hrel.2.1, hrel.2.2.1, by rw [hst2_eqs.2.1]; exact hpool.2.2.1,
       by rw [hst2_eqs.2.1]; exact h.st_maxSl_le, hpool.2.2.2.2⟩,
      by rw [hst2_eqs.1]; exact hnxt_nv,
      fun info hi => lblInfoOk0_mono (hinfo_ok info hi) hctrl2_lt hctrl2_get_old
        (by rw [hst2_eqs.1]; exact Nat.le_refl _)
        (by rw [hst2_eqs.2.1]; exact Nat.le_refl _)
        (fun v _ => by rw [hst2_eqs.2.2]),
      fun info hi hw =>
        ⟨fun s hs => ⟨(hwait info hi hw).1 s hs |>.1, hfree_no_wait info hi hw s hs⟩,
        fun v hv hlv => by
          have hv' : v < st.nextVid.toNat := hst2_eqs.1 ▸ hv
          obtain ⟨hes, hvmem⟩ := hlive_branch' lbl sc hsc nd rd.1.free v hv' hlv
          rw [hst2_eqs.2.2]
          exact (hwait info hi hw).2 v hv' (Or.inl ⟨hes, hvmem⟩)⟩,
      trivial,
      fun v hv hlv => by
        have hv' : v < st.nextVid.toNat := hst2_eqs.1 ▸ hv
        obtain ⟨hes, hvmem⟩ := hlive_branch' lbl sc hsc nd rd.1.free v hv' hlv
        rw [hst2_eqs.2.2]
        have hlv_cur := hlive v hv' (Or.inl ⟨hes, hvmem⟩)
        refine ⟨hlv_cur.1, hfree_no_esc1 v hv' hes hvmem, fun w hw hne hlw => ?_⟩
        have hw' : w < st.nextVid.toNat := hst2_eqs.1 ▸ hw
        obtain ⟨hesw, hwmemw⟩ := hlive_branch' lbl sc hsc nd rd.1.free w hw' hlw
        exact hlv_cur.2.2 w hw' hne (Or.inl ⟨hesw, hwmemw⟩)⟩
  refine
    { preRes_nv := h.preRes_nv
      preRes_ds_sz := h.preRes_ds_sz
      preRes_us_sz := h.preRes_us_sz
      preRes_es_sz := h.preRes_es_sz
      preRes_es_bit := h.preRes_es_bit
      preRes_us_bd := h.preRes_us_bd
      maxBd_lt := h.maxBd_lt
      pre_inv := hpre_inv'
      pre_run := hpre_run'
      len_pw := by rw [hout, hls_eq.2.2]; simp only [List.length_cons, hlen_rest]
      len_mw := by rw [hls_eq.2.2]; simp only [List.length_cons, hlen_mrest]
      seenJnz_safe := by
        rw [hls_eq.2.2]; have hs := h.seenJnz_safe
        simp only [List.map_cons, hnd, eTask, tTask] at hs ⊢
        rwa [← jnzGroupSafeWork0_jnz seenJnz c t e (rest.map RegaTask0.node)]
      seenJnz_ctrl := by
        rw [hls_eq.2.1]; dsimp only [ctrl2]; rw [Array.size_push, h.seenJnz_ctrl, hnl1]
      maxJump_bd := by
        rw [hls_eq.2.2]; have hm := h.maxJump_bd
        rw [List.map_cons, hnd] at hm
        rw [List.map_cons, List.map_cons]
        dsimp only [workMaxJumpArity0, maxJumpArity0, eTask, tTask] at hm ⊢
        omega
      ctrl_fn := hls_eq.2.1 ▸ h.ctrl_fn
      ctrl_nl := by
        rw [hls_eq.2.1, hls_eq.2.2]; have hnl := h.ctrl_nl
        rw [List.map_cons, hnd] at hnl
        dsimp only [workNodeCount0, nodeCount0] at hnl
        dsimp only [ctrl2, eTask, tTask]
        rw [List.map_cons, List.map_cons]
        dsimp only [workNodeCount0]; rw [hnl1]
        exact ⟨by omega, by omega⟩
      st_nv := by rw [hls_eq.1, hout, hst2_eqs.1, hst1.1, h.st_nv]
      st_vslot_sz := by rw [hls_eq.1, hst2_eqs.1, hst2_eqs.2.2]; exact h.st_vslot_sz
      st_rem_sz := by rw [hls_eq.1]; exact hrel.1
      st_maxSl_le := by rw [hls_eq.1, hst2_eqs.2.1]; exact h.st_maxSl_le
      st_rem_le := fun v hv => by
        rw [hls_eq.1]
        have hrs := hrel.2.2.2.1 v hv
        have hle := h.st_rem_le v hv
        dsimp only at hrs
        rw [hst0_eqs.2.2.2] at hrs
        change rd.1.remUses.getD v 0 ≤ preRes.uses.getD v 0
        rw [hrs]
        split <;> omega
      st_rem_future := fun v h1 h2 => by
        rw [hls_eq.1] at h1 ⊢; rw [hst2_eqs.1] at h1
        have hrs := hrel.2.2.2.1 v h2
        dsimp only at hrs
        rw [hst0_eqs.2.2.2, h.st_rem_future v h1 h2] at hrs
        have hnu : argUses0 (UInt32.ofNat v) cur.venv c = 0 := by
          cases c with
          | immBool _ | immBits _ _ => rfl
          | var idx =>
            dsimp only [argUses0]
            have hva := wfNode0_nodeArgsInVenv0 hwf; rw [← hvlen] at hva
            have hlt := hvlt (listGetU32 cur.venv idx) (by
              rw [listGetU32_eq_listGetD, listGetD_eq_getElem7 _ _ _ (hva idx rfl)]
              exact List.getElem_mem _)
            have hne : listGetU32 cur.venv idx ≠ UInt32.ofNat v := fun he => by
              have hn := congrArg UInt32.toNat he
              rw [u32_toNat_ofNat7,
                Nat.mod_eq_of_lt (Nat.lt_trans h2 (by have := h.preRes_nv; omega))] at hn
              omega
            simp [hne]
        change rd.1.remUses.getD v 0 = preRes.uses.getD v 0
        rw [hrs, hnu, Nat.sub_zero]; split <;> rfl
      st_rem_active := fun v hv hesc hact => by
        rw [hls_eq.1] at hv ⊢; rw [hout] at hact ⊢; dsimp only at hv hact ⊢
        rw [hst2_eqs.1] at hv
        rw [hst1.2.1, hst1.1]
        have hdl := h.pre_inv.defScope_lt v (h.st_nv ▸ hv)
        have hact_rest : ∃ q ∈ restPre, q.scope.toNat = preSt.defScope.getD v 0 := by
          obtain ⟨q, hq, hq_sc⟩ := hact.2
          rw [hst1.2.1] at hq_sc
          rcases List.mem_cons.mp hq with rfl | hq1
          · dsimp only at hq_sc; omega
          · rcases List.mem_cons.mp hq1 with rfl | hq2
            · dsimp only at hq_sc; omega
            · exact ⟨q, hq2, hq_sc⟩
        obtain ⟨q, hq, hq_sc⟩ := hact_rest
        have hact0 : ActiveDefScope0 preSt (curPre :: restPre) v :=
          ⟨h.st_nv ▸ hv, q, List.mem_cons_of_mem _ hq, hq_sc⟩
        have hsc_ne : curPre.scope.toNat ≠ preSt.defScope.getD v 0 := fun he =>
          hrest_scopes q hq (u32_ext7 (by omega))
        have h0 := hpr_noesc v (h.st_nv ▸ hv) hesc curPre List.mem_cons_self
        have hne' : ¬ (curPre.scope.toNat = preSt.defScope.getD v 0) := hsc_ne
        simp only [hne', ↓reduceIte, hpn_j, hpv, ← h.st_nv] at h0
        have hnz := nodeArgsUses0_zero_of_astZero h0
        dsimp only [nodeArgsUses0] at hnz
        have hrs := hrel.2.2.2.1 v (Nat.lt_of_lt_of_le hv (by have := h.preRes_uses_lt_bd; omega))
        change rd.1.remUses.getD v 0 = _ at hrs
        rw [hst0_eqs.2.2.2] at hrs
        simp only [hesc, ↓reduceIte] at hrs
        change rd.1.remUses.getD v 0 = _
        rw [hrs, hnz, Nat.sub_zero, h.st_rem_active v hv hesc hact0]
        have hne0 : preSt.defScope.getD v 0 ≠ curPre.scope.toNat := hsc_ne.symm
        have hne1 : preSt.defScope.getD v 0 ≠ (nextSc + 1).toNat := by omega
        have hne2 : preSt.defScope.getD v 0 ≠ nextSc.toNat := by omega
        dsimp only [sameScopeSpineSum0]
        simp only [hne0, hne1, hne2, ↓reduceIte, Nat.zero_add]
      items_ok := fun i hi1 hi2 hi3 => by
        let pE : PreItem0 := PreItem0.mk e curPre.venv (nextSc + 1)
        let pT : PreItem0 := PreItem0.mk t curPre.venv nextSc
        have hi1' : i < (pE :: pT :: restPre).length := by rw [hout] at hi1; exact hi1
        have hi2' : i < (eTask :: tTask :: rest).length := by rw [hls_eq.2.2] at hi2; exact hi2
        have hout_st : out.st = preSt1 := by rw [hout]
        rw [show out.work[i] = (pE :: pT :: restPre)[i]'hi1' from by simp [hout, pE, pT],
          show ls.work[i] = (eTask :: tTask :: rest)[i]'hi2' from by simp [hls_eq.2.2],
          hout_st, hls_eq.1, hls_eq.2.1]
        cases i with
        | zero =>
          dsimp only [List.getElem_cons_zero, pE]
          exact htm_branch 0 (nextSc + 1) e (by omega) hwfe hfit.2 hsbg.2 hnb.2
        | succ i' =>
          cases i' with
          | zero =>
            dsimp only [List.getElem_cons_succ, List.getElem_cons_zero, pT]
            exact htm_branch ctrl.nextLbl nextSc t (Nat.le_refl _) hwft hfit.1 hsbg.1 hnb.1
          | succ j' =>
            dsimp only [List.getElem_cons_succ]
            have hj'_lt : j' < restPre.length := by simp only [List.length_cons] at hi1'; omega
            have htm := h.items_ok (j' + 1) (by simp only [List.length_cons] at hi1' ⊢; omega)
              (by simp only [List.length_cons] at hi2' ⊢; omega)
              (by simp only [List.length_cons] at hi3 ⊢; omega)
            dsimp only [List.getElem_cons_succ] at htm
            refine taskMetaOk0_mono_rest htm
              (fun w h1 h2 => by rw [hst1.1] at h2; rw [h.st_nv] at h1; omega)
              (fun _ _ => by rw [hst1.2.1]) (by rw [hst1.1]; exact Nat.le_refl _)
              h.st_nv (u32_ext7 (by rw [hst2_eqs.1, h.st_nv, hst1.1]))
              (by rw [hst2_eqs.2.1]; exact Nat.le_refl _)
              (by rw [hst2_eqs.2.1]; exact h.st_maxSl_le)
              (fun _ _ => by rw [hst2_eqs.2.2])
              hctrl2_lt hctrl2_get_old
              (fun v hv hesc hsc => by
                have hsc_ne : curPre.scope.toNat ≠ preSt.defScope.getD v 0 := fun he =>
                  hrest_scopes (restPre[j']'hj'_lt) (List.getElem_mem hj'_lt)
                    (u32_ext7 (hsc ▸ he.symm))
                have h0 := hpr_noesc v (h.st_nv ▸ hv) hesc curPre List.mem_cons_self
                simp only [hsc_ne, ↓reduceIte, hpn_j, hpv, ← h.st_nv] at h0
                have hnz := nodeArgsUses0_zero_of_astZero h0
                dsimp only [nodeArgsUses0] at hnz
                have hrs := hrel.2.2.2.1 v (Nat.lt_of_lt_of_le hv
                  (by have := h.preRes_uses_lt_bd; omega))
                change rd.1.remUses.getD v 0 = _ at hrs
                rw [hst0_eqs.2.2.2] at hrs
                simp only [hesc, ↓reduceIte] at hrs
                change 0 < rd.1.remUses.getD v 0 ↔ _
                rw [hrs, hnz, Nat.sub_zero])
      later_live := fun i j hi1 hi2 hi3 hj1 hj2 hij w hw hlive_j => by
        rw [hls_eq.1, hst2_eqs.1] at hw
        let pE : PreItem0 := PreItem0.mk e curPre.venv (nextSc + 1)
        let pT : PreItem0 := PreItem0.mk t curPre.venv nextSc
        have hi1' : i < (pE :: pT :: restPre).length := by rw [hout] at hi1; exact hi1
        have hj1' : j < (pE :: pT :: restPre).length := by rw [hout] at hj1; exact hj1
        have hi2' : i < (eTask :: tTask :: rest).length := by rw [hls_eq.2.2] at hi2; exact hi2
        have hj2' : j < (eTask :: tTask :: rest).length := by rw [hls_eq.2.2] at hj2; exact hj2
        have hout_st : out.st = preSt1 := by rw [hout]
        rw [show out.work[j] = (pE :: pT :: restPre)[j]'hj1' from by simp [hout, pE, pT],
          show ls.work[j] = (eTask :: tTask :: rest)[j]'hj2' from by simp [hls_eq.2.2],
          hout_st, hls_eq.1] at hlive_j
        rw [show out.work[i] = (pE :: pT :: restPre)[i]'hi1' from by simp [hout, pE, pT],
          show ls.work[i] = (eTask :: tTask :: rest)[i]'hi2' from by simp [hls_eq.2.2],
          hout_st, hls_eq.1]
        have hlive_rest_iff : ∀ (k : Nat) (hk1 : k < restPre.length) (hk2 : k < rest.length),
            LiveInTask0 preRes.escaped preSt1 st2 restPre[k] rest[k] w ↔
            LiveInTask0 preRes.escaped preSt st restPre[k] rest[k] w := by
          intro k hk1 hk2
          simp only [LiveInTask0]; rw [hst1.2.1]
          have hrs := hrel.2.2.2.1 w (Nat.lt_of_lt_of_le hw
            (by have := h.preRes_uses_lt_bd; omega))
          dsimp only at hrs
          rw [hst0_eqs.2.2.2] at hrs
          rcases h.preRes_es_bit w (Nat.lt_of_lt_of_le hw
              (by have := h.preRes_uses_lt_bd; omega)) with he0 | he1
          · simp only [he0, ↓reduceIte] at hrs
            by_cases hsc : restPre[k].scope.toNat = preSt.defScope.getD w 0
            · have hne_s : ¬ (curPre.scope.toNat = preSt.defScope.getD w 0) := fun he =>
                hrest_scopes (restPre[k]'hk1) (List.getElem_mem hk1) (u32_ext7 (hsc.trans he.symm))
              have h0 := hpr_noesc w (h.st_nv ▸ hw) he0 curPre List.mem_cons_self
              simp only [hne_s, ↓reduceIte, hpn_j, hpv, ← h.st_nv] at h0
              have hnz := nodeArgsUses0_zero_of_astZero h0
              dsimp only [nodeArgsUses0] at hnz
              dsimp only [st2]
              rw [hrs, hnz, Nat.sub_zero]
            · simp only [he0, hsc, Nat.zero_ne_one, false_and, false_or]
          · simp only [he1, Nat.one_ne_zero, false_and, or_false]
        cases j with
        | zero => omega
        | succ j' =>
          cases j' with
          | zero =>
            cases i with
            | zero =>
              dsimp only [List.getElem_cons_zero, List.getElem_cons_succ, pT] at hlive_j ⊢
              obtain ⟨hes, hvmem⟩ := hlive_branch' ctrl.nextLbl nextSc (Nat.le_refl _) t
                rd.1.free w hw hlive_j
              exact Or.inl (Or.inl ⟨hes, hvmem⟩)
            | succ _ => omega
          | succ k =>
            dsimp only [List.getElem_cons_succ] at hlive_j
            have hk1_lt : k < restPre.length := by simp only [List.length_cons] at hj1'; omega
            have hk2_lt : k < rest.length := by simp only [List.length_cons] at hj2'; omega
            have hk1_s : k + 1 < (curPre :: restPre).length := by
              simp only [List.length_cons]; omega
            have hk2_s : k + 1 < (cur :: rest).length := by simp only [List.length_cons]; omega
            have hj_old := (hlive_rest_iff k hk1_lt hk2_lt).mp hlive_j
            cases i with
            | zero =>
              dsimp only [List.getElem_cons_zero]
              have hcov := h.later_live 0 (k + 1) (by simp) (by simp) (by simp)
                hk1_s hk2_s (Nat.zero_lt_succ k) w hw hj_old
              rcases hcov with hl0 | ⟨info, hm, hwt, hsl⟩
              · left
                rcases hl0 with ⟨hes, hvmem⟩ | ⟨hes, hsc, _⟩
                · exact Or.inl ⟨hes, hvmem⟩
                · exfalso
                  dsimp only [List.getElem_cons_zero] at hsc
                  rcases hj_old with ⟨hes1, _⟩ | ⟨_, hsc_j, _⟩
                  · rw [hes] at hes1; cases hes1
                  · exact hrest_scopes (restPre[k]'hk1_lt) (List.getElem_mem hk1_lt)
                      (u32_ext7 (hsc_j.trans hsc.symm))
              · right; refine ⟨info, hm, hwt, ?_⟩
                rw [hst2_eqs.2.2]; exact hsl
            | succ i' =>
              cases i' with
              | zero =>
                dsimp only [List.getElem_cons_succ, List.getElem_cons_zero]
                have hcov := h.later_live 0 (k + 1) (by simp) (by simp) (by simp)
                  hk1_s hk2_s (Nat.zero_lt_succ k) w hw hj_old
                rcases hcov with hl0 | ⟨info, hm, hwt, hsl⟩
                · left
                  rcases hl0 with ⟨hes, hvmem⟩ | ⟨hes, hsc, _⟩
                  · exact Or.inl ⟨hes, hvmem⟩
                  · exfalso
                    dsimp only [List.getElem_cons_zero] at hsc
                    rcases hj_old with ⟨hes1, _⟩ | ⟨_, hsc_j, _⟩
                    · rw [hes] at hes1; cases hes1
                    · exact hrest_scopes (restPre[k]'hk1_lt) (List.getElem_mem hk1_lt)
                        (u32_ext7 (hsc_j.trans hsc.symm))
                · right; refine ⟨info, hm, hwt, ?_⟩
                  rw [hst2_eqs.2.2]; exact hsl
              | succ m =>
                dsimp only [List.getElem_cons_succ]
                have hm1_lt : m < restPre.length := by simp only [List.length_cons] at hi1'; omega
                have hm2_lt : m < rest.length := by simp only [List.length_cons] at hi2'; omega
                have hm1_s : m + 1 < (curPre :: restPre).length := by
                  simp only [List.length_cons]; omega
                have hm2_s : m + 1 < (cur :: rest).length := by
                  simp only [List.length_cons]; omega
                have hm3_s : m + 1 < (mCur :: restMeta).length := by
                  have := hlen_mrest; simp only [List.length_cons]; omega
                have hcov := h.later_live (m + 1) (k + 1) hm1_s hm2_s hm3_s
                  hk1_s hk2_s (by omega) w hw hj_old
                rcases hcov with hli | ⟨info, hm, hwt, hsl⟩
                · left; exact (hlive_rest_iff m hm1_lt hm2_lt).mpr hli
                · right; refine ⟨info, hm, hwt, ?_⟩
                  rw [hst2_eqs.2.2]; exact hsl }

theorem regaStep0_group {ctx : LegalCtx0} {fnIdx : UInt32} {fnMaxJump : Nat}
    {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0} {curPre : PreItem0}
    {restPre : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {rest : List RegaTask0} {mCur : TaskMeta0} {restMeta : List TaskMeta0}
    {bodies : List (List Ty0 × TFlat0)} {k : TFlat0}
    (h : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: restPre) seenJnz st ctrl
      (cur :: rest) (mCur :: restMeta))
    (hnd : cur.node = .group bodies k) :
    let st0 := regaPrependLbl0 cur st ctrl
    let ls := regaStep0 preRes.escaped cur st0 ctrl rest
    let preSt1 := preNoteNode0 curPre.scope curPre.venv curPre.node preSt
    let out := preStepPush0 curPre preSt1 nextSc restPre
    ∃ (headMeta : List TaskMeta0),
      RegaStepInv0 ctx fnIdx fnMaxJump preRes out.nextScope out.st out.work false
        ls.st ls.ctrl ls.work (headMeta ++ restMeta) := by
  intro st0 ls preSt1 out
  have hsj_false : seenJnz = false := by
    have hs := h.seenJnz_safe
    simp only [List.map_cons, hnd, jnzGroupSafeWork0_group, Bool.and_eq_true,
      Bool.not_eq_true'] at hs
    exact hs.1
  subst hsj_false
  have hctrl_sz : ctrl.lblSlots.size = ctrl.nextLbl.toNat := h.seenJnz_ctrl
  have hcur_ok := h.items_ok 0 (by simp) (by simp) (by simp)
  dsimp only [List.getElem_cons_zero] at hcur_ok
  obtain ⟨hpn, hpv, hvlen, hvlt, hllen, hgl, hgi, hwf, hfit, hsbg, hnb, hpool, hnxt_nv,
    hinfo_ok, hwait, hentry, hlive⟩ := hcur_ok
  have hpn_g : curPre.node = .group bodies k := hpn.trans hnd
  have hpreSt1 : preSt1 = preSt := by dsimp only [preSt1]; rw [hpn_g]; rfl
  rw [hnd] at hwf hfit hsbg hnb
  obtain ⟨hwfk, hfitk, hsbgk, hnbk, hcases⟩ := wfNode0_group_single_inv hwf hfit hsbg hnb
  have hsub := preRunAux0_sub_active h.pre_inv h.pre_run
  obtain ⟨_, hpr_noesc⟩ := hsub
  have hrest_scopes : ∀ p ∈ restPre, p.scope ≠ curPre.scope := by
    have hnd_sc := h.pre_inv.scopes_nodup
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd_sc
    exact hnd_sc.1
  have hrest_nodup : (restPre.map PreItem0.scope).Nodup := by
    have hnd_sc := h.pre_inv.scopes_nodup
    simp only [List.map_cons, List.nodup_cons] at hnd_sc
    exact hnd_sc.2
  have hrest_lt : ∀ p ∈ restPre, p.scope.toNat < nextSc.toNat := fun p hp =>
    h.pre_inv.scopes_lt p (List.mem_cons_of_mem _ hp)
  have hst0_eqs : st0.nextVid = st.nextVid ∧ st0.maxSlots = st.maxSlots ∧
      st0.vslot = st.vslot ∧ st0.remUses = st.remUses := by
    dsimp only [st0, regaPrependLbl0]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have hlen_rest : restPre.length = rest.length := by simpa using h.len_pw
  have hlen_mrest : restMeta.length = rest.length := by simpa using h.len_mw
  rcases hcases with rfl | ⟨pts, b, rfl, hpts_lt, hwfb, hfitb, hsbgb, hnbb⟩
  · have hout : out = PreOut0.mk preSt (nextSc + 1)
        (PreItem0.mk k curPre.venv nextSc :: restPre) := by
      dsimp only [out, preStepPush0, isTerm0, preStepGroup0, prePushGroup0, preEnqueueGroup0]
      rw [hpn_g, hpreSt1]; rfl
    have hls_eq : ls.st = st0 ∧ ls.ctrl = ctrl ∧
        ls.work = RegaTask0.mk 0 k cur.venv cur.lenv cur.freeSlots cur.nextSlot :: rest := by
      dsimp only [ls, regaStep0]; rw [hnd]
      dsimp only [stepGroupFinish0, stepGroupPrep0, regaPrepGroup0, groupEnqCont0,
        regaEnqueueGroup0]
      exact ⟨rfl, rfl, rfl⟩
    have hsc_ub : nextSc.toNat + 2 * (1 + 0 + nodeCount0 k +
        workNodeCount0 (restPre.map PreItem0.node)) < 2 ^ 31 := by
      have := h.pre_inv.nextSc_bound
      rw [List.map_cons, hpn_g] at this
      dsimp only [workNodeCount0, nodeCount0, blocksNodeCount0] at this; exact this
    have hsc1 : (nextSc + 1).toNat = nextSc.toNat + 1 := u32_add1_toNat7 (by omega)
    have hnd_sc : (nextSc :: restPre.map PreItem0.scope).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hm => ?_, hrest_nodup⟩
      obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
      have := hrest_lt p hp; have := congrArg UInt32.toNat hpe; omega
    have hpre_inv' : PreWorkInv0 ctx out.nextScope out.st out.work := by
      rw [hout]; dsimp only
      refine ⟨h.pre_inv.defScope_sz, h.pre_inv.uses_sz, h.pre_inv.escaped_sz,
        fun v hv => by have := h.pre_inv.defScope_lt v hv; omega,
        h.pre_inv.escaped_bit, hnd_sc,
        fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp1
          · dsimp only; omega
          · have := hrest_lt p hp1; omega,
        fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp1
          · exact ⟨mCur.vT, mCur.lT, by rw [hpv, hvlen],
              fun v hm => by rw [hpv] at hm; exact h.st_nv ▸ hvlt v hm, hwfk, hfitk, hsbgk, hnbk⟩
          · exact h.pre_inv.items_ok p (List.mem_cons_of_mem _ hp1),
        by have := h.pre_inv.nextVid_bound
           rw [List.map_cons, hpn_g] at this; simp only [List.map_cons]
           dsimp only [workBinderCount0, binderCount0, blocksBinderCount0] at this ⊢; omega,
        by have := hsc_ub; rw [List.map_cons]; dsimp only [workNodeCount0]; omega,
        by have := h.pre_inv.argCount_bound
           rw [List.map_cons, hpn_g] at this; simp only [List.map_cons]
           dsimp only [workArgCount0, argCount0, blocksArgCount0] at this ⊢; omega,
        fun v hv => by
          have hb := h.pre_inv.uses_bound v hv
          rw [List.map_cons, hpn_g] at hb; simp only [List.map_cons]
          dsimp only [workArgCount0, argCount0, blocksArgCount0] at hb ⊢; omega⟩
    have hpre_run' : (preRunAux0 (UInt32.ofNat (workNodeCount0 (out.work.map PreItem0.node)))
        out.nextScope out.st out.work).2 = preRes :=
      preRun_step_eq7 h.pre_inv.nextSc_bound h.pre_run
    let m0 := TaskMeta0.mk mCur.vT mCur.lT mCur.gl none
    have hlive_k : ∀ v < st.nextVid.toNat,
        LiveInTask0 preRes.escaped preSt st0 ⟨k, curPre.venv, nextSc⟩
          ⟨0, k, cur.venv, cur.lenv, cur.freeSlots, cur.nextSlot⟩ v →
        preRes.escaped.getD v 0 = 1 ∧ UInt32.ofNat v ∈ cur.venv := by
      intro v hv hlv
      rcases hlv with ⟨hes, hvmem⟩ | ⟨_, hsc_v, _⟩
      · exact ⟨hes, hvmem⟩
      · have := h.pre_inv.defScope_lt v (h.st_nv ▸ hv); dsimp only at hsc_v; omega
    have hres : RegaStepInv0 ctx fnIdx fnMaxJump preRes out.nextScope out.st out.work false
        ls.st ls.ctrl ls.work (m0 :: restMeta) :=
      { preRes_nv := h.preRes_nv
        preRes_ds_sz := h.preRes_ds_sz
        preRes_us_sz := h.preRes_us_sz
        preRes_es_sz := h.preRes_es_sz
        preRes_es_bit := h.preRes_es_bit
        preRes_us_bd := h.preRes_us_bd
        maxBd_lt := h.maxBd_lt
        pre_inv := hpre_inv'
        pre_run := hpre_run'
        len_pw := by rw [hout, hls_eq.2.2]; simp only [List.length_cons, hlen_rest]
        len_mw := by rw [hls_eq.2.2]; simp only [List.length_cons, hlen_mrest]
        seenJnz_safe := by
          rw [hls_eq.2.2]; have hs := h.seenJnz_safe
          simp only [List.map_cons, hnd, jnzGroupSafeWork0_group, Bool.not_false, Bool.true_and,
            List.map_nil, List.nil_append] at hs
          exact hs
        seenJnz_ctrl := by rw [hls_eq.2.1]; exact hctrl_sz
        maxJump_bd := by
          rw [hls_eq.2.2]; have hm := h.maxJump_bd
          rw [List.map_cons, hnd] at hm; simp only [List.map_cons]
          dsimp only [workMaxJumpArity0, maxJumpArity0, blocksMaxJumpArity0] at hm ⊢; omega
        ctrl_fn := hls_eq.2.1 ▸ h.ctrl_fn
        ctrl_nl := by
          rw [hls_eq.2.1, hls_eq.2.2]; have hnl := h.ctrl_nl
          rw [List.map_cons, hnd] at hnl; simp only [List.map_cons]
          dsimp only [workNodeCount0, nodeCount0, blocksNodeCount0] at hnl ⊢
          exact ⟨hnl.1, by omega⟩
        st_nv := by rw [hls_eq.1, hout]; dsimp only; rw [hst0_eqs.1]; exact h.st_nv
        st_vslot_sz := by rw [hls_eq.1, hst0_eqs.1, hst0_eqs.2.2.1]; exact h.st_vslot_sz
        st_rem_sz := by rw [hls_eq.1, hst0_eqs.2.2.2]; exact h.st_rem_sz
        st_maxSl_le := by rw [hls_eq.1, hst0_eqs.2.1]; exact h.st_maxSl_le
        st_rem_le := fun v hv => by rw [hls_eq.1, hst0_eqs.2.2.2]; exact h.st_rem_le v hv
        st_rem_future := fun v h1 h2 => by
          rw [hls_eq.1] at h1 ⊢; rw [hst0_eqs.1] at h1; rw [hst0_eqs.2.2.2]
          exact h.st_rem_future v h1 h2
        st_rem_active := fun v hv hesc hact => by
          rw [hls_eq.1] at hv ⊢; rw [hout] at hact ⊢; dsimp only at hv hact ⊢
          rw [hst0_eqs.1] at hv; rw [hst0_eqs.2.2.2]
          have hdl := h.pre_inv.defScope_lt v (h.st_nv ▸ hv)
          have hact_rest : ∃ q ∈ restPre, q.scope.toNat = preSt.defScope.getD v 0 := by
            obtain ⟨q, hq, hq_sc⟩ := hact.2
            rcases List.mem_cons.mp hq with rfl | hq1
            · dsimp only at hq_sc; omega
            · exact ⟨q, hq1, hq_sc⟩
          obtain ⟨q, hq, hq_sc⟩ := hact_rest
          have hact0 : ActiveDefScope0 preSt (curPre :: restPre) v :=
            ⟨h.st_nv ▸ hv, q, List.mem_cons_of_mem _ hq, hq_sc⟩
          have hsc_ne : preSt.defScope.getD v 0 ≠ curPre.scope.toNat := fun he =>
            hrest_scopes q hq (u32_ext7 (by omega))
          have hne_k : preSt.defScope.getD v 0 ≠ nextSc.toNat := by omega
          rw [h.st_rem_active v hv hesc hact0]
          dsimp only [sameScopeSpineSum0]
          simp only [hsc_ne, hne_k, ↓reduceIte, Nat.zero_add]
        items_ok := fun i hi1 hi2 hi3 => by
          let pK : PreItem0 := PreItem0.mk k curPre.venv nextSc
          let tK0 : RegaTask0 := RegaTask0.mk 0 k cur.venv cur.lenv cur.freeSlots cur.nextSlot
          have hi1' : i < (pK :: restPre).length := by rw [hout] at hi1; exact hi1
          have hi2' : i < (tK0 :: rest).length := by rw [hls_eq.2.2] at hi2; exact hi2
          have hout_st : out.st = preSt := by rw [hout]
          rw [show out.work[i] = (pK :: restPre)[i]'hi1' from by simp [hout, pK],
            show ls.work[i] = (tK0 :: rest)[i]'hi2' from by simp [hls_eq.2.2, tK0],
            hout_st, hls_eq.1, hls_eq.2.1]
          cases i with
          | zero =>
            dsimp only [List.getElem_cons_zero, pK, tK0]
            refine ⟨rfl, hpv, hvlen, fun v hv => by rw [hst0_eqs.1]; exact hvlt v hv,
              hllen, hgl, fun j h1 h2 h3 => hgi j h1 h2 h3,
              by dsimp only [legalAddSigs0] at hwfk; exact hwfk, hfitk, hsbgk, hnbk,
              by rw [hst0_eqs.2.1]; exact hpool, by rw [hst0_eqs.1]; exact hnxt_nv,
              fun info hi => lblInfoOk0_mono (hinfo_ok info hi) (Nat.le_refl _)
                (fun _ _ _ => rfl) (by rw [hst0_eqs.1]; exact Nat.le_refl _)
                (by rw [hst0_eqs.2.1]; exact Nat.le_refl _)
                (fun _ _ => by rw [hst0_eqs.2.2.1]),
              fun info hi hw => ⟨(hwait info hi hw).1, fun v hv hlv => by
                have hv' : v < st.nextVid.toNat := by rwa [hst0_eqs.1] at hv
                obtain ⟨hes, hvmem⟩ := hlive_k v hv' hlv
                rw [hst0_eqs.2.2.1]
                exact (hwait info hi hw).2 v hv' (Or.inl ⟨hes, hvmem⟩)⟩,
              trivial,
              fun v hv hlv => by
                have hv' : v < st.nextVid.toNat := by rwa [hst0_eqs.1] at hv
                obtain ⟨hes, hvmem⟩ := hlive_k v hv' hlv
                rw [hst0_eqs.2.2.1]
                have hlv_c := hlive v hv' (Or.inl ⟨hes, hvmem⟩)
                refine ⟨hlv_c.1, hlv_c.2.1, fun w hw hne hlw => ?_⟩
                have hw' : w < st.nextVid.toNat := by rwa [hst0_eqs.1] at hw
                obtain ⟨hesw, hwmemw⟩ := hlive_k w hw' hlw
                exact hlv_c.2.2 w hw' hne (Or.inl ⟨hesw, hwmemw⟩)⟩
          | succ j' =>
            dsimp only [List.getElem_cons_succ]
            have htm := h.items_ok (j' + 1) (by simp only [List.length_cons] at hi1' ⊢; omega)
              (by simp only [List.length_cons] at hi2' ⊢; omega)
              (by simp only [List.length_cons] at hi3 ⊢; omega)
            dsimp only [List.getElem_cons_succ] at htm
            refine taskMetaOk0_mono_rest htm
              (fun w h1 h2 => by rw [h.st_nv] at h1; omega)
              (fun _ _ => rfl) (Nat.le_refl _) h.st_nv
              (by rw [hst0_eqs.1]; exact h.st_nv)
              (by rw [hst0_eqs.2.1]; exact Nat.le_refl _)
              (by rw [hst0_eqs.2.1]; exact h.st_maxSl_le)
              (fun _ _ => by rw [hst0_eqs.2.2.1])
              (Nat.le_refl _) (fun _ _ _ => rfl)
              (fun _ _ _ _ => by rw [hst0_eqs.2.2.2])
        later_live := fun i j hi1 hi2 hi3 hj1 hj2 hij w hw hlive_j => by
          rw [hls_eq.1, hst0_eqs.1] at hw
          let pK : PreItem0 := PreItem0.mk k curPre.venv nextSc
          let tK0 : RegaTask0 := RegaTask0.mk 0 k cur.venv cur.lenv cur.freeSlots cur.nextSlot
          have hi1' : i < (pK :: restPre).length := by rw [hout] at hi1; exact hi1
          have hj1' : j < (pK :: restPre).length := by rw [hout] at hj1; exact hj1
          have hi2' : i < (tK0 :: rest).length := by rw [hls_eq.2.2] at hi2; exact hi2
          have hj2' : j < (tK0 :: rest).length := by rw [hls_eq.2.2] at hj2; exact hj2
          have hout_st : out.st = preSt := by rw [hout]
          rw [show out.work[j] = (pK :: restPre)[j]'hj1' from by simp [hout, pK],
            show ls.work[j] = (tK0 :: rest)[j]'hj2' from by simp [hls_eq.2.2, tK0],
            hout_st, hls_eq.1] at hlive_j
          rw [show out.work[i] = (pK :: restPre)[i]'hi1' from by simp [hout, pK],
            show ls.work[i] = (tK0 :: rest)[i]'hi2' from by simp [hls_eq.2.2, tK0],
            hout_st, hls_eq.1]
          obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          have hj'_lt : j' < restPre.length := by simp only [List.length_cons] at hj1'; omega
          have hj2'_lt : j' < rest.length := by simp only [List.length_cons] at hj2'; omega
          have hj1_s : j' + 1 < (curPre :: restPre).length := by simp only [List.length_cons]; omega
          have hj2_s : j' + 1 < (cur :: rest).length := by simp only [List.length_cons]; omega
          dsimp only [List.getElem_cons_succ] at hlive_j
          have hj_old : LiveInTask0 preRes.escaped preSt st (restPre[j']'hj'_lt)
              (rest[j']'hj2'_lt) w := by
            simpa only [LiveInTask0, hst0_eqs.2.2.2] using hlive_j
          cases i with
          | zero =>
            dsimp only [List.getElem_cons_zero]
            have hcov := h.later_live 0 (j' + 1) (by simp) (by simp) (by simp)
              hj1_s hj2_s (Nat.zero_lt_succ j') w hw hj_old
            rcases hcov with hl0 | ⟨info, hm, hwt, hsl⟩
            · rcases hl0 with ⟨hes, hvmem⟩ | ⟨hes, hsc, _⟩
              · exact Or.inl (Or.inl ⟨hes, hvmem⟩)
              · exfalso
                dsimp only [List.getElem_cons_zero] at hsc
                rcases hj_old with ⟨hes1, _⟩ | ⟨_, hsc_j, _⟩
                · rw [hes] at hes1; cases hes1
                · exact hrest_scopes (restPre[j']'hj'_lt) (List.getElem_mem hj'_lt)
                    (u32_ext7 (hsc_j.trans hsc.symm))
            · right; refine ⟨info, hm, hwt, ?_⟩
              rw [hst0_eqs.2.2.1]; exact hsl
          | succ i' =>
            dsimp only [List.getElem_cons_succ]
            have hi'_lt : i' < restPre.length := by simp only [List.length_cons] at hi1'; omega
            have hi2'_lt : i' < rest.length := by simp only [List.length_cons] at hi2'; omega
            have hi1_s : i' + 1 < (curPre :: restPre).length := by
              simp only [List.length_cons]; omega
            have hi2_s : i' + 1 < (cur :: rest).length := by simp only [List.length_cons]; omega
            have hi3_s : i' + 1 < (mCur :: restMeta).length := by
              have := hlen_mrest; simp only [List.length_cons]; omega
            have hcov := h.later_live (i' + 1) (j' + 1) hi1_s hi2_s hi3_s
              hj1_s hj2_s hij w hw hj_old
            rcases hcov with hli | ⟨info, hm, hwt, hsl⟩
            · left; dsimp only [List.getElem_cons_succ] at hli
              simpa only [LiveInTask0, hst0_eqs.2.2.2] using hli
            · right; refine ⟨info, hm, hwt, ?_⟩
              rw [hst0_eqs.2.2.1]; exact hsl }
    exact ⟨[m0], hres⟩
  · have hsc_ub : nextSc.toNat + 2 * (1 + (nodeCount0 b + 0) + nodeCount0 k +
        workNodeCount0 (restPre.map PreItem0.node)) < 2 ^ 31 := by
      have := h.pre_inv.nextSc_bound
      rw [List.map_cons, hpn_g] at this
      dsimp only [workNodeCount0, nodeCount0, blocksNodeCount0] at this; exact this
    have hsc1 : (nextSc + 1).toNat = nextSc.toNat + 1 := u32_add1_toNat7 (by omega)
    have hsc2 : (nextSc + 2).toNat = nextSc.toNat + 2 := u32_add_ofNat_lt7 (m := 2) (by omega)
    have hlen_pts : (tyLenU0 pts 0).toNat = pts.length := tyLenU0_eq_of_lt hpts_lt
    have hnv_b : preSt.nextVid.toNat + pts.length < 2 ^ 32 := by
      have := h.pre_inv.nextVid_bound
      rw [List.map_cons, hpn_g] at this
      dsimp only [workBinderCount0, binderCount0, blocksBinderCount0] at this; omega
    have hst_bd_step : st.nextVid.toNat + pts.length ≤ preRes.nextVid.toNat := by
      have htot := h.preRes_uses_lt_bd
      rw [List.map_cons, hnd] at htot
      dsimp only [workBinderCount0, binderCount0, blocksBinderCount0] at htot; omega
    have hnv_b32 : st.nextVid.toNat + pts.length < 2 ^ 32 := by
      rw [h.st_nv]; exact hnv_b
    have hbind_pre := preBindLoop0_spec pts.length (tyLenU0 pts 0) nextSc curPre.venv
      preSt hlen_pts hnv_b h.pre_inv.defScope_sz h.pre_inv.uses_sz h.pre_inv.escaped_sz
    dsimp only at hbind_pre
    have hout : out = PreOut0.mk (preBindLoop0 (tyLenU0 pts 0) nextSc curPre.venv preSt).2
        (nextSc + 2)
        (PreItem0.mk k curPre.venv (nextSc + 1) ::
          PreItem0.mk b (preBindLoop0 (tyLenU0 pts 0) nextSc curPre.venv preSt).1
            nextSc :: restPre) := by
      dsimp only [out, preStepPush0]; rw [hpn_g, hpreSt1]
      simp only [isTerm0, Bool.false_eq_true, ↓reduceIte]
      dsimp only [preStepGroup0, preEnqueueGroup0, prePushGroup0, prePushOne0]
      rw [UInt32.add_assoc, show (1 : UInt32) + 1 = 2 by decide]
    have hnd_sc : ([nextSc + 1, nextSc] ++ restPre.map PreItem0.scope).Nodup := by
      refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, hrest_nodup⟩⟩
      · intro hm; rcases List.mem_cons.mp hm with h1 | h1
        · have := congrArg UInt32.toNat h1; omega
        · obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h1
          have := hrest_lt p hp; have := congrArg UInt32.toNat hpe; omega
      · intro hm; obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
        have := hrest_lt p hp; have := congrArg UInt32.toNat hpe; omega
    have hvlen_b : (pushFreshVids0 pts.length preSt.nextVid curPre.venv).length =
        (pushTys0 pts mCur.vT).length := by
      rw [pushFreshVids0_length, hpv, hvlen, pushTys0_eq_pushTypes, pushTypes_length]
    have hvlt_b : ∀ v ∈ pushFreshVids0 pts.length preSt.nextVid curPre.venv,
        v.toNat < preSt.nextVid.toNat + pts.length := by
      intro v hm
      rcases (mem_pushFreshVids0 pts.length preSt.nextVid curPre.venv v).mp hm
        with h0 | ⟨j, hj, rfl⟩
      · exact Nat.lt_of_lt_of_le (h.st_nv ▸ hvlt v (hpv ▸ h0)) (Nat.le_add_right _ _)
      · rw [u32_add_ofNat_lt7 (by omega)]; omega
    have hpre_inv' : PreWorkInv0 ctx out.nextScope out.st out.work := by
      rw [hout]; dsimp only
      refine ⟨hbind_pre.2.2.1.trans hbind_pre.2.1.symm,
        hbind_pre.2.2.2.1.trans hbind_pre.2.1.symm, hbind_pre.2.2.2.2.1.trans hbind_pre.2.1.symm,
        fun v hv => by
          rw [hbind_pre.2.1] at hv; rw [hbind_pre.2.2.2.2.2.1 v]; split
          · rename_i hv0; have := h.pre_inv.defScope_lt v hv0; omega
          · omega,
        fun v hv => by
          rw [hbind_pre.2.1] at hv; rw [hbind_pre.2.2.2.2.2.2.2 v]; split
          · rename_i hv0; exact h.pre_inv.escaped_bit v hv0
          · exact Or.inl rfl,
        by simpa only [List.map_cons, List.cons_append, List.nil_append] using hnd_sc,
        fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp1
          · dsimp only; omega
          · rcases List.mem_cons.mp hp1 with rfl | hp2
            · dsimp only; omega
            · have := hrest_lt p hp2; omega,
        fun p hp => by
          rw [hbind_pre.2.1]; rcases List.mem_cons.mp hp with rfl | hp1
          · exact ⟨mCur.vT, legalAddSigs0 [(pts, b)] mCur.lT, by rw [hpv, hvlen],
              fun v hm => Nat.lt_of_lt_of_le (h.st_nv ▸ hvlt v (hpv ▸ hm))
                (Nat.le_add_right _ _),
              hwfk, hfitk, hsbgk, hnbk⟩
          · rcases List.mem_cons.mp hp1 with rfl | hp2
            · rw [hbind_pre.1]
              exact ⟨pushTys0 pts mCur.vT, legalAddSigs0 [(pts, b)] mCur.lT, hvlen_b, hvlt_b,
                hwfb, hfitb, hsbgb, hnbb⟩
            · obtain ⟨vT2, lT2, hvl2, hvlt2, hwf2, hfit2, hsbg2, hnb2⟩ :=
                h.pre_inv.items_ok p (List.mem_cons_of_mem _ hp2)
              exact ⟨vT2, lT2, hvl2,
                fun v hm => Nat.lt_of_lt_of_le (hvlt2 v hm) (Nat.le_add_right _ _),
                hwf2, hfit2, hsbg2, hnb2⟩,
        by rw [hbind_pre.2.1]; have := h.pre_inv.nextVid_bound
           rw [List.map_cons, hpn_g] at this; simp only [List.map_cons]
           dsimp only [workBinderCount0, binderCount0, blocksBinderCount0] at this ⊢; omega,
        by have := hsc_ub; simp only [List.map_cons]; dsimp only [workNodeCount0]; omega,
        by have := h.pre_inv.argCount_bound
           rw [List.map_cons, hpn_g] at this; simp only [List.map_cons]
           dsimp only [workArgCount0, argCount0, blocksArgCount0] at this ⊢; omega,
        fun v hv => by
          rw [hbind_pre.2.1] at hv; rw [hbind_pre.2.2.2.2.2.2.1 v]
          by_cases hv0 : v < preSt.nextVid.toNat
          · simp only [hv0, ↓reduceIte]
            have hb := h.pre_inv.uses_bound v hv0
            rw [List.map_cons, hpn_g] at hb; simp only [List.map_cons]
            dsimp only [workArgCount0, argCount0, blocksArgCount0] at hb ⊢; omega
          · simp only [hv0, ↓reduceIte, Nat.zero_add]
            have hb := h.pre_inv.argCount_bound
            rw [List.map_cons, hpn_g] at hb; simp only [List.map_cons]
            dsimp only [workArgCount0, argCount0, blocksArgCount0] at hb ⊢; omega⟩
    have hpre_run' : (preRunAux0 (UInt32.ofNat (workNodeCount0 (out.work.map PreItem0.node)))
        out.nextScope out.st out.work).2 = preRes :=
      preRun_step_eq7 h.pre_inv.nextSc_bound h.pre_run
    have hsub' := preRunAux0_sub_active hpre_inv' hpre_run'
    let bb := bindBlockParams0 pts cur.venv st0 cur.freeSlots cur.nextSlot
    let slots := slotsOfVids0 (tyLenU0 pts 0) bb.venv bb.st.vslot []
    let ctrl1 : CtrlSt0 :=
      { ctrl with nextLbl := ctrl.nextLbl + 1, lblSlots := ctrl.lblSlots.push slots }
    let tK := RegaTask0.mk 0 k cur.venv (ctrl.nextLbl :: cur.lenv) bb.free bb.nxt
    let tB := RegaTask0.mk ctrl.nextLbl b bb.venv (ctrl.nextLbl :: cur.lenv) bb.free bb.nxt
    have hls_eq : ls.st = bb.st ∧ ls.ctrl = ctrl1 ∧ ls.work = tK :: tB :: rest := by
      dsimp only [ls, regaStep0]; rw [hnd]
      dsimp only [stepGroupFinish0, stepGroupPrep0, regaPrepGroup0, prepOneBlock0, prepOneBind0,
        prepFinishBlock0, prepUpdCtrl0, groupEnqCont0, regaEnqueueGroup0]
      exact ⟨rfl, rfl, rfl⟩
    have hbb := bindBlockParams0_spec_clean pts cur.venv st0 cur.freeSlots cur.nextSlot
      (preRes.nextVid.toNat + fnMaxJump)
      (by rw [hst0_eqs.1, hst0_eqs.2.2.1]; exact h.st_vslot_sz)
      (by rw [hst0_eqs.1]; have := h.preRes_nv; omega)
      ⟨hpool.1, hpool.2.1, by rw [hst0_eqs.2.1]; exact hpool.2.2.1,
        by rw [hst0_eqs.2.1]; exact h.st_maxSl_le, hpool.2.2.2.2⟩
      (by omega)
    dsimp only at hbb
    rw [show bindBlockParams0 pts cur.venv st0 cur.freeSlots cur.nextSlot = bb from rfl] at hbb
    obtain ⟨hbb_venv, hbb_nv, hbb_vsz, hbb_rem, _, hbb_pool, hbb_nlo, hbb_nhi, hbb_fr,
      hbb_pres, hbb_sl⟩ := hbb
    have hnl1 : (ctrl.nextLbl + 1).toNat = ctrl.nextLbl.toNat + 1 := u32_add1_toNat7 (by
      have := h.ctrl_nl
      rw [List.map_cons, hnd] at this
      dsimp only [workNodeCount0, nodeCount0, blocksNodeCount0] at this; omega)
    have hslots_eq : slots =
        (List.range pts.length).map
          (fun j => arrGetU0 bb.st.vslot (st.nextVid + UInt32.ofNat j)) := by
      dsimp only [slots]
      rw [hbb_venv, hst0_eqs.1]
      rw [slotsOfVids0_pushFreshVids0 pts.length (tyLenU0 pts 0) st.nextVid cur.venv
        bb.st.vslot [] hlen_pts (by have := h.preRes_nv; omega)]
      simp only [List.append_nil]
    have hslots_len : slots.length = pts.length := by
      rw [hslots_eq, List.length_map, List.length_range]
    have hslots_getD : ∀ j < pts.length,
        slots.getD j 0 = arrGetU0 bb.st.vslot (st.nextVid + UInt32.ofNat j) := by
      intro j hj
      rw [listGetD_eq_getElem7 slots 0 j (by rw [hslots_len]; exact hj)]
      simp only [hslots_eq, List.getElem_map, List.getElem_range]
    have hslots_nd : slots.Nodup := by
      refine nodup_of_getD7 slots 0 fun i j hi hj hij => ?_
      rw [hslots_len] at hi hj
      rw [hslots_getD i hi, hslots_getD j hj, ← hst0_eqs.1]
      exact (hbb_sl j hj).2.2.2 i hij
    have hslots_mem : ∀ s ∈ slots,
        s.toNat < bb.nxt.toNat ∧ s ∉ bb.free ∧
        (s ∈ cur.freeSlots ∨ cur.nextSlot.toNat ≤ s.toNat) := by
      intro s hs
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hs
      have hj' : j < pts.length := by rwa [← hslots_len]
      have hgs := hslots_getD j hj'
      rw [listGetD_eq_getElem7 slots 0 j hj] at hgs
      rw [hgs, ← hst0_eqs.1]
      have hbj := hbb_sl j hj'
      exact ⟨hbj.1, hbj.2.1, hbj.2.2.1⟩
    have hctrl1_get_new : ctrl1.lblSlots.getD ctrl.nextLbl.toNat [] = slots := by
      dsimp only [ctrl1]
      rw [arrPush_getD7, hctrl_sz]
      simp
    have hctrl1_get_old : ∀ l, 1 ≤ l → l < ctrl.nextLbl.toNat →
        ctrl1.lblSlots.getD l [] = ctrl.lblSlots.getD l [] := by
      intro l _ hl
      dsimp only [ctrl1]
      rw [arrPush_getD7, hctrl_sz]
      simp [hl]
    have hbb_nv_eq : bb.st.nextVid = out.st.nextVid := by
      apply u32_ext7
      rw [hbb_nv, hst0_eqs.1, h.st_nv, hout]; dsimp only
      rw [hbind_pre.2.1]
    have hbb_venv_eq : bb.venv =
        (preBindLoop0 (tyLenU0 pts 0) nextSc curPre.venv preSt).1 := by
      rw [hbb_venv, hst0_eqs.1, h.st_nv, hbind_pre.1, hpv]
    have hbb_rem_eq : bb.st.remUses = st.remUses := by rw [hbb_rem, hst0_eqs.2.2.2]
    let infoK : LblInfo0 :=
      ⟨ctrl.nextLbl, pts, slots, bb.nxt, cur.venv, mCur.vT, st.nextVid, true⟩
    let infoB : LblInfo0 := { infoK with waiting := false }
    have hinfo_new_ok : ∀ w : Bool,
        LblInfoOk0 preRes.escaped bb.st ctrl1 { infoK with waiting := w } := by
      intro w
      have hnl := h.ctrl_nl
      rw [List.map_cons, hnd] at hnl
      dsimp only [workNodeCount0, nodeCount0, blocksNodeCount0] at hnl
      refine ⟨hnl.1, by dsimp only [ctrl1, infoK]; rw [hnl1]; omega, hctrl1_get_new,
        hslots_len, hslots_nd, by dsimp only [infoK]; rw [hbb_nv, hst0_eqs.1]; omega,
        fun j hj => by
          dsimp only [infoK]
          rw [← hslots_getD j hj],
        hbb_pool.2.2.1,
        fun s hs => (hslots_mem s hs).1, hvlen, hvlt, fun s hs u hu hescu humem => ?_⟩
      dsimp only [infoK] at hs hu humem ⊢
      have hu_lt : u < st.nextVid.toNat := hu
      rw [hbb_pres u (hst0_eqs.1 ▸ hu_lt), hst0_eqs.2.2.1]
      have hlu := hlive u hu_lt (Or.inl ⟨hescu, humem⟩)
      have hsm := hslots_mem s hs
      intro heq
      rcases hsm.2.2 with hfr | hge
      · exact hlu.2.1 (heq ▸ hfr)
      · have := hlu.1; rw [heq] at this; omega
    have hrem_act' : ∀ v < bb.st.nextVid.toNat, preRes.escaped.getD v 0 = 0 →
        ActiveDefScope0 out.st out.work v →
        bb.st.remUses.getD v 0 =
          sameScopeSpineSum0 (UInt32.ofNat v) (out.st.defScope.getD v 0)
            out.st.nextVid out.work := by
      intro v hv hesc hact
      rw [hout] at hact ⊢; dsimp only at hact ⊢
      rw [hbb_rem_eq]
      by_cases hv_old : v < st.nextVid.toNat
      · have hds_v :
            (preBindLoop0 (tyLenU0 pts 0) nextSc curPre.venv preSt).2.defScope.getD v 0 =
              preSt.defScope.getD v 0 := by
          rw [hbind_pre.2.2.2.2.2.1 v]
          simp only [show v < preSt.nextVid.toNat from h.st_nv ▸ hv_old, ↓reduceIte]
        rw [hds_v]
        have hdl := h.pre_inv.defScope_lt v (h.st_nv ▸ hv_old)
        have hact_rest : ∃ q ∈ restPre, q.scope.toNat = preSt.defScope.getD v 0 := by
          obtain ⟨q, hq, hq_sc⟩ := hact.2
          rw [hds_v] at hq_sc
          rcases List.mem_cons.mp hq with rfl | hq1
          · dsimp only at hq_sc; omega
          · rcases List.mem_cons.mp hq1 with rfl | hq2
            · dsimp only at hq_sc; omega
            · exact ⟨q, hq2, hq_sc⟩
        obtain ⟨q, hq, hq_sc⟩ := hact_rest
        have hact0 : ActiveDefScope0 preSt (curPre :: restPre) v :=
          ⟨h.st_nv ▸ hv_old, q, List.mem_cons_of_mem _ hq, hq_sc⟩
        have hsc_ne : preSt.defScope.getD v 0 ≠ curPre.scope.toNat := fun he =>
          hrest_scopes q hq (u32_ext7 (by omega))
        have hne_k : preSt.defScope.getD v 0 ≠ (nextSc + 1).toNat := by omega
        have hne_b : preSt.defScope.getD v 0 ≠ nextSc.toNat := by omega
        rw [h.st_rem_active v hv_old hesc hact0]
        have hrest_congr := sameScopeSpineSum0_congr_nv (vid := UInt32.ofNat v)
          (ds := preSt.defScope.getD v 0) (nv₁ := preSt.nextVid)
          (nv₂ := (preBindLoop0 (tyLenU0 pts 0) nextSc curPre.venv preSt).2.nextVid)
          (work := restPre)
          (by rw [u32_toNat_ofNat7, Nat.mod_eq_of_lt (Nat.lt_trans hv_old (UInt32.toNat_lt _))]
              exact h.st_nv ▸ hv_old)
          (by rw [hbind_pre.2.1]; exact Nat.le_add_right _ _)
          (by rw [hbind_pre.2.1]
              have := h.pre_inv.nextVid_bound
              rw [List.map_cons, hpn_g] at this
              dsimp only [workBinderCount0, binderCount0, blocksBinderCount0] at this; omega)
        dsimp only [sameScopeSpineSum0]
        simp only [hsc_ne, hne_k, hne_b, ↓reduceIte, Nat.zero_add, hrest_congr]
      · have hv_ge : st.nextVid.toNat ≤ v := Nat.le_of_not_lt hv_old
        have hv_pre : v < preRes.nextVid.toNat := by
          rw [hbb_nv, hst0_eqs.1] at hv; exact Nat.lt_of_lt_of_le hv hst_bd_step
        rw [h.st_rem_future v hv_ge hv_pre]
        have hu_eq := hsub'.1.2.2.2.2.2 v (by rw [← hbb_nv_eq]; exact hv)
        rw [hout] at hu_eq; dsimp only at hu_eq
        rw [hbind_pre.2.2.2.2.2.2.1 v] at hu_eq
        simp only [show ¬ v < preSt.nextVid.toNat from h.st_nv ▸ hv_old, ↓reduceIte,
          Nat.zero_add] at hu_eq
        exact hu_eq
    have hlive_k : ∀ v < bb.st.nextVid.toNat,
        LiveInTask0 preRes.escaped out.st bb.st
          ⟨k, curPre.venv, nextSc + 1⟩ tK v →
        v < st.nextVid.toNat ∧ preRes.escaped.getD v 0 = 1 ∧ UInt32.ofNat v ∈ cur.venv := by
      intro v hv hlv
      rcases hlv with ⟨hes, hvmem⟩ | ⟨_, hsc_v, _⟩
      · have hv' : v < st.nextVid.toNat := by
          have := hvlt (UInt32.ofNat v) hvmem
          rwa [u32_toNat_ofNat7, Nat.mod_eq_of_lt (Nat.lt_trans hv (UInt32.toNat_lt _))] at this
        exact ⟨hv', hes, hvmem⟩
      · rw [hout] at hsc_v; dsimp only at hsc_v
        rw [hbind_pre.2.2.2.2.2.1 v] at hsc_v
        split at hsc_v
        · rename_i hv0; have := h.pre_inv.defScope_lt v hv0; omega
        · have hv_tot : v < preSt.nextVid.toNat + pts.length := by
            rw [hbb_nv, hst0_eqs.1, h.st_nv] at hv; exact hv
          simp only [hv_tot, ↓reduceIte] at hsc_v; omega
    let lT' := pts :: mCur.lT
    let mK := TaskMeta0.mk mCur.vT lT' (infoK :: mCur.gl) none
    let mB := TaskMeta0.mk (pushTys0 pts mCur.vT) lT' (infoB :: mCur.gl) (some infoB)
    have hlT_eq : legalAddSigs0 [(pts, b)] mCur.lT = lT' := rfl
    have hgi_ext : ∀ (info0 : LblInfo0) (gl0 : List LblInfo0) (lT0 : List (List Ty0)),
        info0.lbl = ctrl.nextLbl → info0.pts = pts →
        (∀ (j : Nat) (h1 : j < gl0.length) (h2 : j < cur.lenv.length) (h3 : j < lT0.length),
          gl0[j].lbl = cur.lenv[j] ∧ gl0[j].pts = lT0[j]) →
        ∀ (j : Nat) (h1 : j < (info0 :: gl0).length) (h2 : j < (ctrl.nextLbl :: cur.lenv).length)
          (h3 : j < (pts :: lT0).length),
          (info0 :: gl0)[j].lbl = (ctrl.nextLbl :: cur.lenv)[j] ∧
            (info0 :: gl0)[j].pts = (pts :: lT0)[j] := by
      intro info0 gl0 lT0 hl hp hprev j h1 h2 h3
      cases j with
      | zero => exact ⟨hl, hp⟩
      | succ j' =>
        exact hprev j' (by simp at h1; omega) (by simp at h2; omega) (by simp at h3; omega)
    have hres : RegaStepInv0 ctx fnIdx fnMaxJump preRes out.nextScope out.st out.work false
        ls.st ls.ctrl ls.work (mK :: mB :: restMeta) :=
      { preRes_nv := h.preRes_nv
        preRes_ds_sz := h.preRes_ds_sz
        preRes_us_sz := h.preRes_us_sz
        preRes_es_sz := h.preRes_es_sz
        preRes_es_bit := h.preRes_es_bit
        preRes_us_bd := h.preRes_us_bd
        maxBd_lt := h.maxBd_lt
        pre_inv := hpre_inv'
        pre_run := hpre_run'
        len_pw := by rw [hout, hls_eq.2.2]; simp only [List.length_cons, hlen_rest]
        len_mw := by rw [hls_eq.2.2]; simp only [List.length_cons, hlen_mrest]
        seenJnz_safe := by
          rw [hls_eq.2.2]; have hs := h.seenJnz_safe
          simp only [List.map_cons, hnd, jnzGroupSafeWork0_group, Bool.not_false, Bool.true_and,
            List.map_cons, List.map_nil, List.cons_append, List.nil_append] at hs
          exact hs
        seenJnz_ctrl := by
          rw [hls_eq.2.1]; dsimp only [ctrl1]; rw [Array.size_push, hctrl_sz, hnl1]
        maxJump_bd := by
          rw [hls_eq.2.2]; have hm := h.maxJump_bd
          rw [List.map_cons, hnd] at hm
          rw [List.map_cons, List.map_cons]
          dsimp only [workMaxJumpArity0, maxJumpArity0, blocksMaxJumpArity0, tK, tB] at hm ⊢
          omega
        ctrl_fn := hls_eq.2.1 ▸ h.ctrl_fn
        ctrl_nl := by
          rw [hls_eq.2.1, hls_eq.2.2]; have hnl := h.ctrl_nl
          rw [List.map_cons, hnd] at hnl
          dsimp only [workNodeCount0, nodeCount0, blocksNodeCount0] at hnl
          dsimp only [ctrl1, tK, tB]
          rw [List.map_cons, List.map_cons]; dsimp only [workNodeCount0]; rw [hnl1]
          exact ⟨by omega, by omega⟩
        st_nv := by rw [hls_eq.1, hbb_nv_eq]
        st_vslot_sz := by rw [hls_eq.1, hbb_vsz, hbb_nv]
        st_rem_sz := by rw [hls_eq.1, hbb_rem_eq]; exact h.st_rem_sz
        st_maxSl_le := by rw [hls_eq.1]; exact hbb_pool.2.2.2.1
        st_rem_le := fun v hv => by rw [hls_eq.1, hbb_rem_eq]; exact h.st_rem_le v hv
        st_rem_future := fun v h1 h2 => by
          rw [hls_eq.1, hbb_nv, hst0_eqs.1] at h1
          rw [hls_eq.1, hbb_rem_eq]
          exact h.st_rem_future v (by omega) h2
        st_rem_active := fun v hv hesc hact => by
          rw [hls_eq.1] at hv ⊢
          exact hrem_act' v hv hesc hact
        items_ok := fun i hi1 hi2 hi3 => by
          let pK : PreItem0 := PreItem0.mk k curPre.venv (nextSc + 1)
          let pB : PreItem0 := PreItem0.mk b
            (preBindLoop0 (tyLenU0 pts 0) nextSc curPre.venv preSt).1 nextSc
          let outStPre := (preBindLoop0 (tyLenU0 pts 0) nextSc curPre.venv preSt).2
          have hi1' : i < (pK :: pB :: restPre).length := by rw [hout] at hi1; exact hi1
          have hi2' : i < (tK :: tB :: rest).length := by rw [hls_eq.2.2] at hi2; exact hi2
          have hout_st : out.st = outStPre := by rw [hout]
          rw [show out.work[i] = (pK :: pB :: restPre)[i]'hi1' from by simp [hout, pK, pB],
            show ls.work[i] = (tK :: tB :: rest)[i]'hi2' from by simp [hls_eq.2.2],
            hout_st, hls_eq.1, hls_eq.2.1]
          cases i with
          | zero =>
            dsimp only [List.getElem_cons_zero, pK, tK, mK, outStPre]
            have hwf' : WfNode0 ctx mCur.vT lT' k := by rwa [← hlT_eq]
            refine ⟨rfl, hpv, hvlen,
              fun v hm => by
                rw [hbb_nv, hst0_eqs.1]
                exact Nat.lt_of_lt_of_le (hvlt v hm) (Nat.le_add_right _ _),
              by simp only [lT', List.length_cons, hllen],
              by simp only [List.length_cons, hgl],
              hgi_ext infoK mCur.gl mCur.lT rfl rfl hgi,
              hwf', hfitk, hsbgk, hnbk, hbb_pool,
              by dsimp only; have := hbb_nhi; have := hnxt_nv; rw [hbb_nv, hst0_eqs.1]; omega,
              fun info hi => by
                rcases List.mem_cons.mp hi with rfl | hi'
                · exact hinfo_new_ok true
                · exact lblInfoOk0_mono (hinfo_ok info hi') (by dsimp only [ctrl1]; omega)
                    hctrl1_get_old (by rw [hbb_nv, hst0_eqs.1]; exact Nat.le_add_right _ _)
                    (by rw [← hst0_eqs.2.1]
                        exact bindBlockParams0_maxSlots_le pts cur.venv st0 cur.freeSlots
                          cur.nextSlot)
                    (fun v hv => by rw [hbb_pres v (hst0_eqs.1 ▸ hv), hst0_eqs.2.2.1]),
              fun info hi hw => by
                rcases List.mem_cons.mp hi with rfl | hi'
                · refine ⟨fun s hs => ⟨(hslots_mem s hs).1, (hslots_mem s hs).2.1⟩,
                    fun v hv hlv => ?_⟩
                  have hlv' : LiveInTask0 preRes.escaped out.st bb.st
                      ⟨k, curPre.venv, nextSc + 1⟩ tK v := by simpa [hout_st] using hlv
                  obtain ⟨hv_lt, hes, hvmem⟩ := hlive_k v hv hlv'
                  rw [hbb_pres v (hst0_eqs.1 ▸ hv_lt), hst0_eqs.2.2.1]
                  intro hm
                  have hlu := hlive v hv_lt (Or.inl ⟨hes, hvmem⟩)
                  rcases (hslots_mem _ hm).2.2 with hfr | hge
                  · exact hlu.2.1 hfr
                  · have := hlu.1; omega
                · refine ⟨fun s hs => ⟨Nat.lt_of_lt_of_le ((hwait info hi' hw).1 s hs).1 hbb_nlo,
                      fun hm => ((hwait info hi' hw).1 s hs).2 (hbb_fr s hm)⟩,
                    fun v hv hlv => ?_⟩
                  have hlv' : LiveInTask0 preRes.escaped out.st bb.st
                      ⟨k, curPre.venv, nextSc + 1⟩ tK v := by simpa [hout_st] using hlv
                  obtain ⟨hv_lt, hes, hvmem⟩ := hlive_k v hv hlv'
                  rw [hbb_pres v (hst0_eqs.1 ▸ hv_lt), hst0_eqs.2.2.1]
                  exact (hwait info hi' hw).2 v hv_lt (Or.inl ⟨hes, hvmem⟩),
              trivial,
              fun v hv hlv => by
                have hlv' : LiveInTask0 preRes.escaped out.st bb.st
                    ⟨k, curPre.venv, nextSc + 1⟩ tK v := by simpa [hout_st] using hlv
                obtain ⟨hv_lt, hes, hvmem⟩ := hlive_k v hv hlv'
                rw [hbb_pres v (hst0_eqs.1 ▸ hv_lt), hst0_eqs.2.2.1]
                have hlv_c := hlive v hv_lt (Or.inl ⟨hes, hvmem⟩)
                refine ⟨Nat.lt_of_lt_of_le hlv_c.1 hbb_nlo, fun hm => hlv_c.2.1 (hbb_fr _ hm),
                  fun w hw hne hlw => ?_⟩
                have hlw' : LiveInTask0 preRes.escaped out.st bb.st
                    ⟨k, curPre.venv, nextSc + 1⟩ tK w := by simpa [hout_st] using hlw
                obtain ⟨hw_lt, hesw, hwmemw⟩ := hlive_k w hw hlw'
                rw [hbb_pres w (hst0_eqs.1 ▸ hw_lt), hst0_eqs.2.2.1]
                exact hlv_c.2.2 w hw_lt hne (Or.inl ⟨hesw, hwmemw⟩)⟩
          | succ i' =>
            cases i' with
            | zero =>
              dsimp only [List.getElem_cons_succ, List.getElem_cons_zero, pB, tB, mB, outStPre]
              have hwf' : WfNode0 ctx (pushTys0 pts mCur.vT) lT' b := by rwa [← hlT_eq]
              have hvlt_b' : ∀ v ∈ bb.venv, v.toNat < bb.st.nextVid.toNat := by
                intro v hm; rw [hbb_nv, hst0_eqs.1]; rw [hbb_venv, hst0_eqs.1] at hm
                rcases (mem_pushFreshVids0 pts.length st.nextVid cur.venv v).mp hm
                  with h0 | ⟨j, hj, rfl⟩
                · exact Nat.lt_of_lt_of_le (hvlt v h0) (Nat.le_add_right _ _)
                · rw [u32_add_ofNat_lt7 (by omega)]; omega
              have hlive_b_old : ∀ v < st.nextVid.toNat,
                  LiveInTask0 preRes.escaped
                    (preBindLoop0 (tyLenU0 pts 0) nextSc curPre.venv preSt).2 bb.st
                    ⟨b, (preBindLoop0 (tyLenU0 pts 0) nextSc curPre.venv preSt).1,
                      nextSc⟩
                    tB v →
                  preRes.escaped.getD v 0 = 1 ∧ UInt32.ofNat v ∈ cur.venv := by
                intro v hv hlv
                rcases hlv with ⟨hes, hvmem⟩ | ⟨_, hsc_v, _⟩
                · dsimp only [tB] at hvmem; rw [hbb_venv, hst0_eqs.1] at hvmem
                  rcases (mem_pushFreshVids0 pts.length st.nextVid cur.venv _).mp hvmem
                    with h0 | ⟨j, hj, he⟩
                  · exact ⟨hes, h0⟩
                  · have hn := congrArg UInt32.toNat he
                    rw [u32_toNat_ofNat7, u32_add_ofNat_lt7 (m := j) (by omega),
                      Nat.mod_eq_of_lt (Nat.lt_trans hv (UInt32.toNat_lt _))] at hn
                    omega
                · rw [hbind_pre.2.2.2.2.2.1 v] at hsc_v
                  simp only [show v < preSt.nextVid.toNat from h.st_nv ▸ hv, ↓reduceIte] at hsc_v
                  have := h.pre_inv.defScope_lt v (h.st_nv ▸ hv)
                  omega
              have hlive_b_single : ∀ u < bb.st.nextVid.toNat,
                  LiveInTask0 preRes.escaped
                    (preBindLoop0 (tyLenU0 pts 0) nextSc curPre.venv preSt).2 bb.st
                    ⟨b, (preBindLoop0 (tyLenU0 pts 0) nextSc curPre.venv preSt).1,
                      nextSc⟩
                    tB u →
                  (arrGetU0 bb.st.vslot (UInt32.ofNat u)).toNat < bb.nxt.toNat ∧
                  arrGetU0 bb.st.vslot (UInt32.ofNat u) ∉ bb.free ∧
                  (u < st.nextVid.toNat →
                    (arrGetU0 st.vslot (UInt32.ofNat u)).toNat < cur.nextSlot.toNat ∧
                    arrGetU0 st.vslot (UInt32.ofNat u) ∉ cur.freeSlots) := by
                intro u hu hlu
                rw [hbb_nv, hst0_eqs.1] at hu
                by_cases huo : u < st.nextVid.toNat
                · obtain ⟨hes, humem⟩ := hlive_b_old u huo hlu
                  rw [hbb_pres u (hst0_eqs.1 ▸ huo), hst0_eqs.2.2.1]
                  have hlu_c := hlive u huo (Or.inl ⟨hes, humem⟩)
                  exact ⟨Nat.lt_of_lt_of_le hlu_c.1 hbb_nlo, fun hm => hlu_c.2.1 (hbb_fr _ hm),
                    fun _ => ⟨hlu_c.1, hlu_c.2.1⟩⟩
                · obtain ⟨j, hj, rfl⟩ : ∃ j < pts.length, u = st.nextVid.toNat + j :=
                    ⟨u - st.nextVid.toNat, by omega, by omega⟩
                  have hidx_eq : UInt32.ofNat (st.nextVid.toNat + j) =
                      st0.nextVid + UInt32.ofNat j := by
                    rw [hst0_eqs.1]; exact u32_ofNat_add_eq7 st.nextVid j (by omega)
                  rw [hidx_eq]
                  have hbj := hbb_sl j hj
                  exact ⟨hbj.1, hbj.2.1, fun hlt => absurd hlt (by omega)⟩
              refine ⟨rfl, hbb_venv_eq.symm,
                by rw [hbb_venv, pushFreshVids0_length, hvlen, pushTys0_eq_pushTypes,
                    pushTypes_length],
                hvlt_b', by simp only [lT', List.length_cons, hllen],
                by simp only [List.length_cons, hgl],
                hgi_ext infoB mCur.gl mCur.lT rfl rfl hgi, hwf', hfitb, hsbgb, hnbb, hbb_pool,
                by dsimp only; have := hbb_nhi; have := hnxt_nv; rw [hbb_nv, hst0_eqs.1]; omega,
                fun info hi => by
                  rcases List.mem_cons.mp hi with rfl | hi'
                  · exact hinfo_new_ok false
                  · exact lblInfoOk0_mono (hinfo_ok info hi') (by dsimp only [ctrl1]; omega)
                      hctrl1_get_old (by rw [hbb_nv, hst0_eqs.1]; exact Nat.le_add_right _ _)
                      (by rw [← hst0_eqs.2.1]
                          exact bindBlockParams0_maxSlots_le pts cur.venv st0 cur.freeSlots
                            cur.nextSlot)
                      (fun v hv => by rw [hbb_pres v (hst0_eqs.1 ▸ hv), hst0_eqs.2.2.1]),
                fun info hi hw => by
                  rcases List.mem_cons.mp hi with rfl | hi'
                  · cases hw
                  · refine ⟨fun s hs => ⟨Nat.lt_of_lt_of_le ((hwait info hi' hw).1 s hs).1 hbb_nlo,
                        fun hm => ((hwait info hi' hw).1 s hs).2 (hbb_fr s hm)⟩,
                      fun v hv hlv => ?_⟩
                    rw [hbb_nv, hst0_eqs.1] at hv
                    by_cases hvo : v < st.nextVid.toNat
                    · obtain ⟨hes, hvmem⟩ := hlive_b_old v hvo hlv
                      rw [hbb_pres v (hst0_eqs.1 ▸ hvo), hst0_eqs.2.2.1]
                      exact (hwait info hi' hw).2 v hvo (Or.inl ⟨hes, hvmem⟩)
                    · obtain ⟨j, hj, rfl⟩ : ∃ j < pts.length, v = st.nextVid.toNat + j :=
                        ⟨v - st.nextVid.toNat, by omega, by omega⟩
                      have hidx_eq : UInt32.ofNat (st.nextVid.toNat + j) =
                          st0.nextVid + UInt32.ofNat j := by
                        rw [hst0_eqs.1]; exact u32_ofNat_add_eq7 st.nextVid j (by omega)
                      rw [hidx_eq]
                      have hbj := hbb_sl j hj
                      intro hm
                      rcases hbj.2.2.1 with hfr | hge
                      · exact ((hwait info hi' hw).1 _ hm).2 hfr
                      · have := ((hwait info hi' hw).1 _ hm).1; omega,
                by dsimp only [infoB, infoK]
                   exact ⟨rfl, List.mem_cons_self, rfl,
                     by rw [hbb_venv, hst0_eqs.1], rfl, rfl⟩,
                fun v hv hlv => by
                  obtain ⟨hs_lt, hs_nf, _⟩ := hlive_b_single v hv hlv
                  refine ⟨hs_lt, hs_nf, fun w hw hne hlw => ?_⟩
                  rw [hbb_nv, hst0_eqs.1] at hv hw
                  by_cases hvo : v < st.nextVid.toNat <;> by_cases hwo : w < st.nextVid.toNat
                  · obtain ⟨hesv, hvmem⟩ := hlive_b_old v hvo hlv
                    obtain ⟨hesw, hwmem⟩ := hlive_b_old w hwo hlw
                    rw [hbb_pres v (hst0_eqs.1 ▸ hvo),
                      hbb_pres w (hst0_eqs.1 ▸ hwo), hst0_eqs.2.2.1]
                    exact (hlive v hvo (Or.inl ⟨hesv, hvmem⟩)).2.2 w hwo hne
                      (Or.inl ⟨hesw, hwmem⟩)
                  · obtain ⟨jw, hjw, rfl⟩ : ∃ j < pts.length, w = st.nextVid.toNat + j :=
                      ⟨w - st.nextVid.toNat, by omega, by omega⟩
                    obtain ⟨hesv, hvmem⟩ := hlive_b_old v hvo hlv
                    rw [hbb_pres v (hst0_eqs.1 ▸ hvo), hst0_eqs.2.2.1]
                    have hlv_c := hlive v hvo (Or.inl ⟨hesv, hvmem⟩)
                    have hidx_w : UInt32.ofNat (st.nextVid.toNat + jw) =
                        st0.nextVid + UInt32.ofNat jw := by
                      rw [hst0_eqs.1]; exact u32_ofNat_add_eq7 st.nextVid jw (by omega)
                    rw [hidx_w]
                    have hbw := hbb_sl jw hjw
                    intro hcol
                    rcases hbw.2.2.1 with hfr | hge
                    · exact hlv_c.2.1 (hcol ▸ hfr)
                    · have := hlv_c.1; rw [← hcol] at this; omega
                  · obtain ⟨jv, hjv, rfl⟩ : ∃ j < pts.length, v = st.nextVid.toNat + j :=
                      ⟨v - st.nextVid.toNat, by omega, by omega⟩
                    obtain ⟨hesw, hwmem⟩ := hlive_b_old w hwo hlw
                    rw [hbb_pres w (hst0_eqs.1 ▸ hwo), hst0_eqs.2.2.1]
                    have hlw_c := hlive w hwo (Or.inl ⟨hesw, hwmem⟩)
                    have hidx_v : UInt32.ofNat (st.nextVid.toNat + jv) =
                        st0.nextVid + UInt32.ofNat jv := by
                      rw [hst0_eqs.1]; exact u32_ofNat_add_eq7 st.nextVid jv (by omega)
                    rw [hidx_v]
                    have hbv := hbb_sl jv hjv
                    intro hcol
                    rcases hbv.2.2.1 with hfr | hge
                    · exact hlw_c.2.1 (hcol.symm ▸ hfr)
                    · have := hlw_c.1; rw [hcol] at this; omega
                  · obtain ⟨jv, hjv, rfl⟩ : ∃ j < pts.length, v = st.nextVid.toNat + j :=
                      ⟨v - st.nextVid.toNat, by omega, by omega⟩
                    obtain ⟨jw, hjw, rfl⟩ : ∃ j < pts.length, w = st.nextVid.toNat + j :=
                      ⟨w - st.nextVid.toNat, by omega, by omega⟩
                    have hidx_v : UInt32.ofNat (st.nextVid.toNat + jv) =
                        st0.nextVid + UInt32.ofNat jv := by
                      rw [hst0_eqs.1]; exact u32_ofNat_add_eq7 st.nextVid jv (by omega)
                    have hidx_w : UInt32.ofNat (st.nextVid.toNat + jw) =
                        st0.nextVid + UInt32.ofNat jw := by
                      rw [hst0_eqs.1]; exact u32_ofNat_add_eq7 st.nextVid jw (by omega)
                    rw [hidx_v, hidx_w]
                    have hne_j : jw ≠ jv := fun he => hne (by omega)
                    rcases Nat.lt_or_gt_of_ne hne_j with hlt | hgt
                    · exact (hbb_sl jv hjv).2.2.2 jw hlt
                    · exact Ne.symm ((hbb_sl jw hjw).2.2.2 jv hgt)⟩
            | succ j' =>
              dsimp only [List.getElem_cons_succ, outStPre]
              have hj'_lt : j' < restPre.length := by
                simp only [List.length_cons] at hi1'; omega
              have htm := h.items_ok (j' + 1) (by simp only [List.length_cons] at hi1' ⊢; omega)
                (by simp only [List.length_cons] at hi2' ⊢; omega)
                (by simp only [List.length_cons] at hi3 ⊢; omega)
              dsimp only [List.getElem_cons_succ] at htm
              refine taskMetaOk0_mono_rest htm
                (fun w h1 h2 => by
                  rw [hbind_pre.2.2.2.2.2.1 w]
                  have hwtot : w < preSt.nextVid.toNat + pts.length := by
                    rw [← h.st_nv, ← hst0_eqs.1, ← hbb_nv, hbb_nv_eq, hout]; exact h2
                  simp only [show ¬ w < preSt.nextVid.toNat from h.st_nv ▸ Nat.not_lt_of_ge h1,
                    hwtot, ↓reduceIte]
                  have := hrest_lt (restPre[j']'hj'_lt) (List.getElem_mem hj'_lt)
                  omega)
                (fun v hv => by
                  rw [hbind_pre.2.2.2.2.2.1 v]
                  simp only [hv, ↓reduceIte])
                (by rw [hbind_pre.2.1]; exact Nat.le_add_right _ _)
                h.st_nv (hbb_nv_eq.trans (by rw [hout]))
                (by rw [← hst0_eqs.2.1]
                    exact bindBlockParams0_maxSlots_le pts cur.venv st0 cur.freeSlots cur.nextSlot)
                hbb_pool.2.2.2.1
                (fun v hv => by rw [hbb_pres v (hst0_eqs.1 ▸ hv), hst0_eqs.2.2.1])
                (by dsimp only [ctrl1]; omega) hctrl1_get_old
                (fun _ _ _ _ => by rw [hbb_rem_eq])
        later_live := fun i j hi1 hi2 hi3 hj1 hj2 hij w hw hlive_j => by
          rw [hls_eq.1] at hw
          rw [hbb_nv, hst0_eqs.1] at hw
          let pK : PreItem0 := PreItem0.mk k curPre.venv (nextSc + 1)
          let pB : PreItem0 := PreItem0.mk b
            (preBindLoop0 (tyLenU0 pts 0) nextSc curPre.venv preSt).1 nextSc
          let outStPre := (preBindLoop0 (tyLenU0 pts 0) nextSc curPre.venv preSt).2
          have hi1' : i < (pK :: pB :: restPre).length := by rw [hout] at hi1; exact hi1
          have hj1' : j < (pK :: pB :: restPre).length := by rw [hout] at hj1; exact hj1
          have hi2' : i < (tK :: tB :: rest).length := by rw [hls_eq.2.2] at hi2; exact hi2
          have hj2' : j < (tK :: tB :: rest).length := by rw [hls_eq.2.2] at hj2; exact hj2
          have hout_st : out.st = outStPre := by rw [hout]
          rw [show out.work[j] = (pK :: pB :: restPre)[j]'hj1' from by simp [hout, pK, pB],
            show ls.work[j] = (tK :: tB :: rest)[j]'hj2' from by simp [hls_eq.2.2],
            hout_st, hls_eq.1] at hlive_j
          rw [show out.work[i] = (pK :: pB :: restPre)[i]'hi1' from by simp [hout, pK, pB],
            show ls.work[i] = (tK :: tB :: rest)[i]'hi2' from by simp [hls_eq.2.2],
            hout_st, hls_eq.1]
          have hwf_rest_item : ∀ (k : Nat) (hk1 : k < restPre.length) (hk2 : k < rest.length),
              LiveInTask0 preRes.escaped outStPre bb.st restPre[k] rest[k] w →
              w < st.nextVid.toNat ∧
              LiveInTask0 preRes.escaped preSt st restPre[k] rest[k] w := by
            intro k hk1 hk2 hlv
            rcases hlv with ⟨hes, hvmem⟩ | ⟨hes, hsc_v, hpos⟩
            · have htm := h.items_ok (k + 1) (by simp only [List.length_cons] at hk1 ⊢; omega)
                (by simp only [List.length_cons] at hk2 ⊢; omega)
                (by simp only [List.length_cons] at hk2 ⊢; have := h.len_mw; omega)
              have hw_lt : w < st.nextVid.toNat := by
                have := htm.2.2.2.1 (UInt32.ofNat w) hvmem
                rwa [u32_toNat_ofNat7, Nat.mod_eq_of_lt (Nat.lt_trans hw (by
                  have := h.preRes_uses_lt_bd; have := h.preRes_nv; omega))] at this
              exact ⟨hw_lt, Or.inl ⟨hes, hvmem⟩⟩
            · have hw_lt : w < st.nextVid.toNat := Nat.lt_of_not_le fun hge => False.elim <| by
                dsimp only [outStPre] at hsc_v
                rw [hbind_pre.2.2.2.2.2.1 w] at hsc_v
                simp only [show ¬ w < preSt.nextVid.toNat from
                  h.st_nv ▸ Nat.not_lt_of_ge hge,
                  show w < preSt.nextVid.toNat + pts.length from h.st_nv ▸ hw,
                  ↓reduceIte] at hsc_v
                have := hrest_lt (restPre[k]'hk1) (List.getElem_mem hk1)
                omega
              dsimp only [outStPre] at hsc_v
              rw [hbind_pre.2.2.2.2.2.1 w] at hsc_v
              simp only [show w < preSt.nextVid.toNat from h.st_nv ▸ hw_lt, ↓reduceIte] at hsc_v
              rw [hbb_rem_eq] at hpos
              exact ⟨hw_lt, Or.inr ⟨hes, hsc_v, hpos⟩⟩
          cases j with
          | zero => omega
          | succ j' =>
            cases j' with
            | zero =>
              cases i with
              | zero =>
                dsimp only [List.getElem_cons_zero, List.getElem_cons_succ,
                  pK, tK, pB, tB, outStPre] at hlive_j ⊢
                by_cases hwo : w < st.nextVid.toNat
                · have hlv_w : preRes.escaped.getD w 0 = 1 ∧ UInt32.ofNat w ∈ cur.venv := by
                    rcases hlive_j with ⟨hes, hvmem⟩ | ⟨_, hsc_v, _⟩
                    · rw [hbb_venv, hst0_eqs.1] at hvmem
                      rcases (mem_pushFreshVids0 pts.length st.nextVid cur.venv _).mp hvmem
                        with h0 | ⟨jj, hjj, he⟩
                      · exact ⟨hes, h0⟩
                      · have hn := congrArg UInt32.toNat he
                        rw [u32_toNat_ofNat7, u32_add_ofNat_lt7 (m := jj) (by omega),
                          Nat.mod_eq_of_lt (Nat.lt_trans hwo (UInt32.toNat_lt _))] at hn
                        omega
                    · rw [hbind_pre.2.2.2.2.2.1 w] at hsc_v
                      simp only [show w < preSt.nextVid.toNat from h.st_nv ▸ hwo,
                        ↓reduceIte] at hsc_v
                      have := h.pre_inv.defScope_lt w (h.st_nv ▸ hwo)
                      omega
                  exact Or.inl (Or.inl hlv_w)
                · obtain ⟨jj, hjj, rfl⟩ : ∃ jj < pts.length, w = st.nextVid.toNat + jj :=
                    ⟨w - st.nextVid.toNat, by omega, by omega⟩
                  right
                  refine ⟨infoK, List.mem_cons_self, rfl, ?_⟩
                  dsimp only [infoK]
                  have hlem := hslots_getD jj hjj
                  rw [listGetD_eq_getElem7 slots 0 jj (by rw [hslots_len]; exact hjj)] at hlem
                  rw [u32_ofNat_add_eq7 st.nextVid jj (by omega), ← hlem]
                  exact List.getElem_mem _
              | succ _ => omega
            | succ k' =>
              dsimp only [List.getElem_cons_succ] at hlive_j
              have hk'_pre : k' < restPre.length := by simp only [List.length_cons] at hj1'; omega
              have hk'_st : k' < rest.length := by simp only [List.length_cons] at hj2'; omega
              obtain ⟨hw_old, hj_old⟩ := hwf_rest_item k' hk'_pre hk'_st hlive_j
              have hk1_s : k' + 1 < (curPre :: restPre).length := by
                simp only [List.length_cons]; omega
              have hk2_s : k' + 1 < (cur :: rest).length := by
                simp only [List.length_cons]; omega
              cases i with
              | zero =>
                dsimp only [List.getElem_cons_zero, pK, tK]
                have hcov := h.later_live 0 (k' + 1) (by simp) (by simp) (by simp)
                  hk1_s hk2_s (Nat.zero_lt_succ k') w hw_old hj_old
                rcases hcov with hl0 | ⟨info, hm, hwt, hsl⟩
                · rcases hl0 with ⟨hes, hvmem⟩ | ⟨hes, hsc, _⟩
                  · exact Or.inl (Or.inl ⟨hes, hvmem⟩)
                  · exfalso
                    dsimp only [List.getElem_cons_zero, List.getElem_cons_succ] at hsc hj_old
                    rcases hj_old with ⟨hes1, _⟩ | ⟨_, hsc_j, _⟩
                    · rw [hes] at hes1; cases hes1
                    · exact hrest_scopes (restPre[k']'hk'_pre) (List.getElem_mem hk'_pre)
                        (u32_ext7 (hsc_j.trans hsc.symm))
                · right; refine ⟨info, List.mem_cons_of_mem _ hm, hwt, ?_⟩
                  rw [hbb_pres w (hst0_eqs.1 ▸ hw_old), hst0_eqs.2.2.1]; exact hsl
              | succ i' =>
                cases i' with
                | zero =>
                  dsimp only [List.getElem_cons_succ, List.getElem_cons_zero, pB, tB]
                  have hcov := h.later_live 0 (k' + 1) (by simp) (by simp) (by simp)
                    hk1_s hk2_s (Nat.zero_lt_succ k') w hw_old hj_old
                  rcases hcov with hl0 | ⟨info, hm, hwt, hsl⟩
                  · rcases hl0 with ⟨hes, hvmem⟩ | ⟨hes, hsc, _⟩
                    · left; refine Or.inl ⟨hes, ?_⟩
                      rw [hbb_venv, hst0_eqs.1]
                      exact (mem_pushFreshVids0 pts.length st.nextVid cur.venv _).mpr
                        (Or.inl hvmem)
                    · exfalso
                      dsimp only [List.getElem_cons_zero, List.getElem_cons_succ] at hsc hj_old
                      rcases hj_old with ⟨hes1, _⟩ | ⟨_, hsc_j, _⟩
                      · rw [hes] at hes1; cases hes1
                      · exact hrest_scopes (restPre[k']'hk'_pre) (List.getElem_mem hk'_pre)
                          (u32_ext7 (hsc_j.trans hsc.symm))
                  · right; refine ⟨info, List.mem_cons_of_mem _ hm, hwt, ?_⟩
                    rw [hbb_pres w (hst0_eqs.1 ▸ hw_old), hst0_eqs.2.2.1]; exact hsl
                | succ m =>
                  dsimp only [List.getElem_cons_succ]
                  have hcov := h.later_live (m + 1) (k' + 1)
                    (by simp only [List.length_cons] at hi1' ⊢; omega)
                    (by simp only [List.length_cons] at hi2' ⊢; omega)
                    (by simp only [List.length_cons] at hi2' ⊢; have := h.len_mw; omega)
                    hk1_s hk2_s (by omega) w hw_old hj_old
                  rcases hcov with hli | ⟨info, hm, hwt, hsl⟩
                  · left
                    rcases hli with ⟨hes, hvmem⟩ | ⟨hes, hsc, hpos⟩
                    · exact Or.inl ⟨hes, hvmem⟩
                    · refine Or.inr ⟨hes, ?_, by rwa [hbb_rem_eq]⟩
                      dsimp only [outStPre]
                      rw [hbind_pre.2.2.2.2.2.1 w]
                      simp only [show w < preSt.nextVid.toNat from h.st_nv ▸ hw_old, ↓reduceIte]
                      exact hsc
                  · right; refine ⟨info, hm, hwt, ?_⟩
                    rw [hbb_pres w (hst0_eqs.1 ▸ hw_old), hst0_eqs.2.2.1]; exact hsl }
    exact ⟨[mK, mB], hres⟩

theorem regaStep0_lockstep_head {ctx : LegalCtx0} {fnIdx : UInt32} {fnMaxJump : Nat}
    {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0} {curPre : PreItem0}
    {restPre : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {rest : List RegaTask0} {mCur : TaskMeta0} {restMeta : List TaskMeta0}
    (h : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: restPre) seenJnz st ctrl
      (cur :: rest) (mCur :: restMeta)) :
    let st0 := regaPrependLbl0 cur st ctrl
    let ls := regaStep0 preRes.escaped cur st0 ctrl rest
    let preSt1 := preNoteNode0 curPre.scope curPre.venv curPre.node preSt
    let out := preStepPush0 curPre preSt1 nextSc restPre
    ∃ (seenJnz' : Bool) (headMeta : List TaskMeta0),
      RegaStepInv0 ctx fnIdx fnMaxJump preRes out.nextScope out.st out.work seenJnz'
        ls.st ls.ctrl ls.work (headMeta ++ restMeta) := by
  cases hnd : cur.node with
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt =>
    exact ⟨seenJnz, [], regaStep0_term h (by simp [isTerm0, hnd])⟩
  | jnz c t e =>
    let mB := TaskMeta0.mk mCur.vT mCur.lT mCur.gl none
    exact ⟨true, [mB, mB], regaStep0_jnz h hnd⟩
  | group bodies k =>
    obtain ⟨headMeta, h'⟩ := regaStep0_group h hnd
    exact ⟨false, headMeta, h'⟩
  | let1 _ _ _ | let2Umulw64 _ _ _ | load _ _ _ | store _ _ _ _ | call _ _ _ _ _ =>
    let m0 := TaskMeta0.mk (legalNextVenv0 cur.node mCur.vT) mCur.lT mCur.gl none
    exact ⟨seenJnz, [m0], regaStep0_lin h (by simp [isTerm0, hnd])
      (fun _ _ _ he => by rw [hnd] at he; cases he)
      (fun _ _ he => by rw [hnd] at he; cases he)⟩

theorem regaStep0_lockstep {ctx : LegalCtx0} {fnIdx : UInt32} {fnMaxJump : Nat}
    {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0} {curPre : PreItem0}
    {restPre : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {rest : List RegaTask0} {mCur : TaskMeta0} {restMeta : List TaskMeta0}
    (h : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: restPre) seenJnz st ctrl
      (cur :: rest) (mCur :: restMeta)) :
    let st0 := regaPrependLbl0 cur st ctrl
    let ls := regaStep0 preRes.escaped cur st0 ctrl rest
    let preSt1 := preNoteNode0 curPre.scope curPre.venv curPre.node preSt
    let out := preStepPush0 curPre preSt1 nextSc restPre
    ∃ (seenJnz' : Bool) (metas' : List TaskMeta0),
      RegaStepInv0 ctx fnIdx fnMaxJump preRes out.nextScope out.st out.work seenJnz'
        ls.st ls.ctrl ls.work metas' := by
  obtain ⟨seenJnz', headMeta, h'⟩ := regaStep0_lockstep_head h
  exact ⟨seenJnz', headMeta ++ restMeta, h'⟩

theorem regaRunAux0_lockstep :
    ∀ (N : Nat) (fuel : UInt32) (ctx : LegalCtx0) (fnIdx : UInt32) (fnMaxJump : Nat)
      (preRes : PreSt0) (nextSc : UInt32) (preSt : PreSt0) (preWork : List PreItem0)
      (seenJnz : Bool) (st : RegaSt0) (ctrl : CtrlSt0) (work : List RegaTask0)
      (metas : List TaskMeta0),
      workNodeCount0 (work.map RegaTask0.node) = N → N ≤ fuel.toNat →
      RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt preWork seenJnz st ctrl work metas →
      let r := regaRunAux0 fuel preRes.escaped st ctrl work
      r.1.nextVid = preRes.nextVid ∧
      r.1.vslot.size = preRes.nextVid.toNat ∧
      r.1.maxSlots.toNat ≤ preRes.nextVid.toNat + fnMaxJump ∧
      r.2.fnIdx = fnIdx ∧
      1 ≤ r.2.nextLbl.toNat ∧ r.2.nextLbl.toNat < 2 ^ 31 := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro fuel ctx fnIdx fnMaxJump preRes nextSc preSt preWork seenJnz st ctrl work metas
      hN hle h
    cases work with
    | nil =>
      subst hN
      have hpw_nil : preWork = [] := List.eq_nil_of_length_eq_zero h.len_pw
      subst hpw_nil
      have hr : regaRunAux0 fuel preRes.escaped st ctrl [] = (st, ctrl) :=
        regaRunAux0_nil fuel preRes.escaped st ctrl
      rw [hr]
      have hbd := h.preRes_uses_lt_bd
      rw [List.map_nil] at hbd; dsimp only [workBinderCount0] at hbd; rw [Nat.add_zero] at hbd
      have hnv_eq : st.nextVid = preRes.nextVid := u32_ext7 hbd
      have hnl := h.ctrl_nl
      rw [List.map_nil] at hnl; dsimp only [workNodeCount0] at hnl; rw [Nat.add_zero] at hnl
      exact ⟨hnv_eq, h.st_vslot_sz.trans hbd, h.st_maxSl_le, h.ctrl_fn, hnl.1, hnl.2⟩
    | cons cur rest =>
      cases preWork with
      | nil => have := h.len_pw; simp at this
      | cons curPre restPre =>
        cases metas with
        | nil => have := h.len_mw; simp at this
        | cons mCur restMeta =>
          have hpos : 0 < N := by
            rw [← hN, List.map_cons]; dsimp only [workNodeCount0]
            have := nodeCount0_pos cur.node; omega
          have hfne : fuel ≠ 0 := fun hz => by
            have := congrArg UInt32.toNat hz; simp at this; omega
          have hsub : (fuel - 1).toNat = fuel.toNat - 1 := u32_sub1_toNat7 (by omega)
          let st0 := regaPrependLbl0 cur st ctrl
          let ls := regaStep0 preRes.escaped cur st0 ctrl rest
          have hdef_eq : regaRunAux0 fuel preRes.escaped st ctrl (cur :: rest) =
              regaRunAux0 (fuel - 1) preRes.escaped ls.st ls.ctrl ls.work :=
            regaRunAux0_succ hfne preRes.escaped st ctrl cur rest
          have hcnt : workNodeCount0 (ls.work.map RegaTask0.node) + 1 = N := by
            rw [← hN]
            simpa only [ls, List.map_cons] using
              regaWorkNodeCount0_children preRes.escaped cur st0 ctrl rest
          have hlt_N : workNodeCount0 (ls.work.map RegaTask0.node) < N := by omega
          obtain ⟨seenJnz', metas', h'⟩ := regaStep0_lockstep h
          dsimp only
          rw [hdef_eq]
          exact ih (workNodeCount0 (ls.work.map RegaTask0.node)) hlt_N (fuel - 1) ctx fnIdx
            fnMaxJump preRes _ _ _ seenJnz' ls.st ls.ctrl ls.work metas' rfl (by omega) h'

theorem compileFn0_maxSlots_lt {ctx : LegalCtx0} (fnIdx : UInt32) (fn : TFlatFn0)
    (hwf : WfNode0 ctx (pushTys0 fn.as []) [] fn.body) (hg : fn.okGuardsFull = true) :
    (compileFn0 fnIdx fn).2.toNat ≤ fn.as.length + binderCount0 fn.body + maxJumpArity0 fn.body ∧
    (compileFn0 fnIdx fn).2.toNat + 1 < 2 ^ 31 := by
  have hpre := compileFnPre0_inv hwf hg
  dsimp only at hpre
  have hinv0 := regaStepInv0_init fnIdx fn hwf hg
  dsimp only at hinv0
  have hbd := TFlatFn0.okGuardsFull_boundsFitU32 hg
  simp only [TFlatFn0.boundsFitU32, Bool.and_eq_true, decide_eq_true_eq] at hbd
  have hrun := regaRunAux0_lockstep (nodeCount0 fn.body) 0x7fffffff ctx fnIdx
    (maxJumpArity0 fn.body) (compileFnPre0 fn) 1 (preInit0 fn.as).2 _ false _ _ _ _
    (by rw [List.map_singleton]; dsimp only [workNodeCount0]; exact Nat.add_zero _)
    (by change nodeCount0 fn.body ≤ 2147483647; omega) hinv0
  dsimp only at hrun
  dsimp only [compileFn0, compileFnFinish0]
  rw [← regaRunAux0_fst_eq_regaWorkLoop0]
  have hms := hrun.2.2.1
  rw [hpre.2.1] at hms
  exact ⟨hms, by omega⟩

end LeanQbe.T.Bootstrap0
