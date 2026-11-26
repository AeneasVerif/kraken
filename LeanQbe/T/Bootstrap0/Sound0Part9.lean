module

public import LeanQbe.T.Bootstrap0.Sound0Part9a
import LeanQbe.T.TargetLemmas
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Amd64.FrameLemmas
import LeanQbe.T.Amd64.IselLemmas1
import LeanQbe.T.Amd64.IselLemmas2
import LeanQbe.T.Amd64.IselLemmas3
import LeanQbe.T.Amd64.IselLemmas4

/-!
# Bootstrap Stage B (`Sound0Part9`): `Rega0` Worklist Slicing & Entry-Arg Runners

Proves worklist slicing (`regaStep0_prefix_split`), `GlEntriesSem0` preservation, and
`bindEntryArgs0_run_spec`, building on `Sound0Part9a`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T
open LeanQbe.T.Amd64
open Std Std.ExtHashMap

theorem regaStep0_prefix_split {ctx : LegalCtx0} {fnIdx : UInt32} {fnMaxJump : Nat}
    {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0} {curPre : PreItem0}
    {restPre₁ restPre₂ : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {rest₁ w₂ : List RegaTask0} {mCur : TaskMeta0} {restM₁ m₂ : List TaskMeta0}
    (h : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: (restPre₁ ++ restPre₂))
      seenJnz st ctrl (cur :: (rest₁ ++ w₂)) (mCur :: (restM₁ ++ m₂)))
    (hlpw : restPre₁.length = rest₁.length) (hlmw : restM₁.length = rest₁.length) :
    let st0 := regaPrependLbl0 cur st ctrl
    let ls := regaStep0 preRes.escaped cur st0 ctrl (rest₁ ++ w₂)
    let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
    let lsClean := regaStep0 preRes.escaped cur st0Clean ctrl rest₁
    let preSt1 := preNoteNode0 curPre.scope curPre.venv curPre.node preSt
    let out := preStepPush0 curPre preSt1 nextSc (restPre₁ ++ restPre₂)
    ∃ (seenJnz' : Bool) (pw₁' : List PreItem0) (m₁' : List TaskMeta0),
      pw₁'.length = lsClean.work.length ∧ m₁'.length = lsClean.work.length ∧
      out.work = pw₁' ++ restPre₂ ∧
      RegaStepInv0 ctx fnIdx fnMaxJump preRes out.nextScope out.st out.work seenJnz'
        ls.st ls.ctrl ls.work (m₁' ++ m₂) := by
  intro st0 ls st0Clean lsClean preSt1 out
  obtain ⟨seenJnz', headMeta, hinv'⟩ := regaStep0_lockstep_head
    (by simpa only [List.cons_append] using h)
  have hcur_ok := h.items_ok 0 (by simp) (by simp) (by simp)
  dsimp only [List.getElem_cons_zero] at hcur_ok
  obtain ⟨hpn, _, _, _, _, _, _, _, _, hsbg, _⟩ := hcur_ok
  have hcl := regaStep0_clean_append preRes.escaped cur st ctrl rest₁ w₂
  dsimp only at hcl
  have hl_m2 : m₂.length = w₂.length := by
    have hmw := h.len_mw
    simp only [List.length_cons, List.length_append] at hmw
    omega
  have hl_hm : (headMeta ++ restM₁).length = lsClean.work.length := by
    have h1 := hinv'.len_mw
    have h2 := congrArg List.length hcl.1
    dsimp only [lsClean, st0Clean] at h2 ⊢
    simp only [List.length_append] at h1 h2 ⊢
    omega
  have hpw_split : ∃ pw₁', pw₁'.length = lsClean.work.length ∧ out.work = pw₁' ++ restPre₂ := by
    have hpre_split : ∀ bodies k, curPre.node = .group bodies k →
        bodies = [] ∨ ∃ pts b, bodies = [(pts, b)] := fun bodies k he => by
      rw [← hpn, he] at hsbg
      dsimp only [TFlat0.singleBlockGroups] at hsbg
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hsbg
      cases bodies with
      | nil => exact Or.inl rfl
      | cons p bs => cases bs with
        | nil => exact Or.inr ⟨p.1, p.2, rfl⟩
        | cons _ _ => simp at hsbg
    rcases hnd : cur.node with
      op | a | t | t | fnSym | fnSym | c | j | vs | fnSym | _ | bodies
    · exact ⟨PreItem0.mk (linK0 curPre.node)
          (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1 curPre.scope ::
          restPre₁,
        by simp [lsClean, regaStep0, stepLinear0, stepLinBindPush0, linBindPush0, hnd, hlpw],
        by dsimp only [out, preStepPush0]
           simp [isTerm0, preStepLin0, preLinFinish0, hpn, hnd, List.cons_append]⟩
    · exact ⟨PreItem0.mk (linK0 curPre.node)
          (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1 curPre.scope ::
          restPre₁,
        by simp [lsClean, regaStep0, stepLinear0, stepLinBindPush0, linBindPush0, hnd, hlpw],
        by dsimp only [out, preStepPush0]
           simp [isTerm0, preStepLin0, preLinFinish0, hpn, hnd, List.cons_append]⟩
    · exact ⟨PreItem0.mk (linK0 curPre.node)
          (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1 curPre.scope ::
          restPre₁,
        by simp [lsClean, regaStep0, stepLinear0, stepLinBindPush0, linBindPush0, hnd, hlpw],
        by dsimp only [out, preStepPush0]
           simp [isTerm0, preStepLin0, preLinFinish0, hpn, hnd, List.cons_append]⟩
    · exact ⟨PreItem0.mk (linK0 curPre.node)
          (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1 curPre.scope ::
          restPre₁,
        by simp [lsClean, regaStep0, stepLinear0, stepLinBindPush0, linBindPush0, hnd, hlpw],
        by dsimp only [out, preStepPush0]
           simp [isTerm0, preStepLin0, preLinFinish0, hpn, hnd, List.cons_append]⟩
    · exact ⟨PreItem0.mk (linK0 curPre.node)
          (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1 curPre.scope ::
          restPre₁,
        by simp [lsClean, regaStep0, stepLinear0, stepLinBindPush0, linBindPush0, hnd, hlpw],
        by dsimp only [out, preStepPush0]
           simp [isTerm0, preStepLin0, preLinFinish0, hpn, hnd, List.cons_append]⟩
    · exact ⟨restPre₁, by simp [lsClean, regaStep0, regaStepCtrl0, hnd, hlpw],
        by dsimp only [out, preStepPush0]; simp [isTerm0, hpn, hnd]⟩
    · rename_i t e
      exact ⟨PreItem0.mk e curPre.venv (nextSc + 1) :: PreItem0.mk t curPre.venv nextSc ::
          restPre₁,
        by simp [lsClean, regaStep0, stepJnzPush0, hnd, hlpw],
        by dsimp only [out, preStepPush0]
           simp [isTerm0, preStepJnz0, hpn, hnd, List.cons_append]⟩
    · exact ⟨restPre₁, by simp [lsClean, regaStep0, regaStepCtrl0, hnd, hlpw],
        by dsimp only [out, preStepPush0]; simp [isTerm0, hpn, hnd]⟩
    · exact ⟨restPre₁, by simp [lsClean, regaStep0, regaStepCtrl0, hnd, hlpw],
        by dsimp only [out, preStepPush0]; simp [isTerm0, hpn, hnd]⟩
    · exact ⟨restPre₁, by simp [lsClean, regaStep0, regaStepCtrl0, hnd, hlpw],
        by dsimp only [out, preStepPush0]; simp [isTerm0, hpn, hnd]⟩
    · exact ⟨restPre₁, by simp [lsClean, regaStep0, regaStepCtrl0, hnd, hlpw],
        by dsimp only [out, preStepPush0]; simp [isTerm0, hpn, hnd]⟩
    · rename_i k
      rcases hpre_split bodies k (hpn.trans hnd) with rfl | ⟨pts, b, rfl⟩
      · exact ⟨PreItem0.mk k curPre.venv nextSc :: restPre₁, by
            dsimp only [lsClean, regaStep0]; rw [hnd]
            dsimp only [stepGroupFinish0, stepGroupPrep0, regaPrepGroup0,
              groupEnqCont0, regaEnqueueGroup0]
            simp only [List.length_cons, hlpw],
          by dsimp only [out, preStepPush0]; rw [hpn, hnd]
             simp only [isTerm0, Bool.false_eq_true, ↓reduceIte]
             dsimp only [preStepGroup0, prePushGroup0, preEnqueueGroup0]
             rw [List.cons_append]⟩
      · exact ⟨PreItem0.mk k curPre.venv (nextSc + 1) ::
            PreItem0.mk b (preBindLoop0 (tyLenU0 pts 0) nextSc curPre.venv preSt1).1
              nextSc :: restPre₁,
          by dsimp only [lsClean, regaStep0]; rw [hnd]
             dsimp only [stepGroupFinish0, stepGroupPrep0, regaPrepGroup0,
               prepOneBlock0, prepOneBind0, prepFinishBlock0, prepUpdCtrl0,
               groupEnqCont0, regaEnqueueGroup0]
             simp only [List.length_cons, hlpw],
          by dsimp only [out, preStepPush0]; rw [hpn, hnd]
             simp only [isTerm0, Bool.false_eq_true, ↓reduceIte]
             dsimp only [preStepGroup0, prePushGroup0, prePushOne0, preEnqueueGroup0]
             rw [List.cons_append, List.cons_append]⟩
  obtain ⟨pw₁', hlpw', hout_eq⟩ := hpw_split
  exact ⟨seenJnz', pw₁', headMeta ++ restM₁, hlpw', hl_hm, hout_eq, by
    simpa only [List.append_assoc] using hinv'⟩

/-- Worklist monotonicity & prefix splitting for `regaRunAux0` along `RegaStepInv0`. -/
theorem regaRunAux0_step_prefix :
    ∀ (N : Nat) (fuel : UInt32) (ctx : LegalCtx0) (fnIdx : UInt32) (fnMaxJump : Nat)
      (preRes : PreSt0) (nextSc : UInt32) (preSt : PreSt0) (preWork₁ preWork₂ : List PreItem0)
      (seenJnz : Bool) (st : RegaSt0) (ctrl : CtrlSt0) (w₁ w₂ : List RegaTask0)
      (m₁ m₂ : List TaskMeta0),
      workNodeCount0 (w₁.map RegaTask0.node) = N → N ≤ fuel.toNat →
      preWork₁.length = w₁.length → m₁.length = w₁.length →
      RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (preWork₁ ++ preWork₂) seenJnz st ctrl
        (w₁ ++ w₂) (m₁ ++ m₂) →
      let r1 := regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] } ctrl w₁
      let rFull := regaRunAux0 fuel preRes.escaped st ctrl (w₁ ++ w₂)
      rFull = regaRunAux0 (UInt32.ofNat (fuel.toNat - N)) preRes.escaped
        { r1.1 with revDirs := r1.1.revDirs ++ st.revDirs } r1.2 w₂ ∧
      st.nextVid.toNat ≤ r1.1.nextVid.toNat ∧
      r1.1.maxSlots.toNat ≤ (regaRunAux0 fuel preRes.escaped st ctrl (w₁ ++ w₂)).1.maxSlots.toNat ∧
      st.maxSlots.toNat ≤ r1.1.maxSlots.toNat ∧
      (∀ v < st.nextVid.toNat,
        arrGetU0 r1.1.vslot (UInt32.ofNat v) = arrGetU0 st.vslot (UInt32.ofNat v)) ∧
      ∃ seenJnz' nextSc' preSt',
        RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc' preSt' preWork₂ seenJnz'
          { r1.1 with revDirs := r1.1.revDirs ++ st.revDirs } r1.2 w₂ m₂ := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro fuel ctx fnIdx fnMaxJump preRes nextSc preSt pw₁ pw₂ seenJnz st ctrl w₁ w₂ m₁ m₂
      hN hle hlen_pw hlen_mw hinv
    cases w₁ with
    | nil =>
      subst hN
      have hpw_nil : pw₁ = [] := List.eq_nil_of_length_eq_zero hlen_pw
      have hm_nil : m₁ = [] := List.eq_nil_of_length_eq_zero hlen_mw
      subst hpw_nil; subst hm_nil
      rw [List.nil_append] at hinv
      rw [show workNodeCount0 (List.map RegaTask0.node []) = 0 from rfl,
        Nat.sub_zero, List.nil_append, UInt32.ofNat_toNat]
      rw [show regaRunAux0 (UInt32.ofNat 0) preRes.escaped { st with revDirs := [] } ctrl [] =
          ({ st with revDirs := [] }, ctrl) from regaRunAux0_nil _ _ _ _]
      simp only [List.nil_append]
      have hst_id : ({ st with revDirs := st.revDirs } : RegaSt0) = st := by cases st; rfl
      rw [hst_id]
      refine ⟨trivial, Nat.le_refl _, ?_, Nat.le_refl _, fun _ _ => trivial,
        seenJnz, nextSc, preSt, hinv⟩
      have aux_ms : ∀ (M : Nat) (fl : UInt32) (esc : Array Nat) (s0 : RegaSt0) (c0 : CtrlSt0)
          (wk : List RegaTask0),
          fl.toNat = M → s0.maxSlots.toNat ≤ (regaRunAux0 fl esc s0 c0 wk).1.maxSlots.toNat := by
        intro M
        induction M using Nat.strongRecOn with
        | ind M ihM =>
          intro fl esc s0 c0 wk hfl
          by_cases hfl0 : fl = 0
          · rw [hfl0, regaRunAux0_zero]; exact Nat.le_refl _
          · cases wk with
            | nil => rw [regaRunAux0_nil]; exact Nat.le_refl _
            | cons hd tl =>
              rw [regaRunAux0_succ hfl0]
              have hltM : (fl - 1).toNat < M := hfl ▸ u32Sub1Lt0 fl hfl0
              have ih1 := ihM (fl - 1).toNat hltM (fl - 1) esc
                (regaStep0 esc hd (regaPrependLbl0 hd s0 c0) c0 tl).st
                (regaStep0 esc hd (regaPrependLbl0 hd s0 c0) c0 tl).ctrl
                (regaStep0 esc hd (regaPrependLbl0 hd s0 c0) c0 tl).work rfl
              have hstep_ms : s0.maxSlots.toNat ≤
                  (regaStep0 esc hd (regaPrependLbl0 hd s0 c0) c0 tl).st.maxSlots.toNat := by
                have hs0_bd : (regaPrependLbl0 hd s0 c0).maxSlots = s0.maxSlots := by
                  dsimp only [regaPrependLbl0]; split <;> rfl
                rcases hd with ⟨lbl, nd, venv, lenv, fr, nxt⟩
                cases nd with
                | tailCall _ _ _ | exit _ _ _ | ret _ | hlt =>
                  dsimp only [regaStep0, regaStepCtrl0, stepTail0, stepRet0]; rw [hs0_bd]
                  exact Nat.le_refl _
                | jump j args =>
                  dsimp only [regaStep0, regaStepCtrl0, emitJump0]
                  cases args with
                  | nil => rw [hs0_bd]; exact Nat.le_refl _
                  | cons _ r => cases r with
                    | nil => dsimp only [emitJumpOne0]; rw [hs0_bd]; exact Nat.le_refl _
                    | cons _ _ =>
                      dsimp only [emitJumpMulti0]; rw [u32Max0_toNat, hs0_bd]
                      exact Nat.le_max_left _ _
                | jnz _ _ _ =>
                  dsimp only [regaStep0, stepJnzPush0, jnzBuildSt0, jnzWrapRes0]
                  rw [hs0_bd]; exact Nat.le_refl _
                | group bs k' =>
                  dsimp only [regaStep0, stepGroupFinish0, groupEnqCont0, stepGroupPrep0]
                  have hgp_ms : ∀ bs' venv' gp',
                      gp'.st.maxSlots.toNat ≤ (regaPrepGroup0 bs' venv' gp').st.maxSlots.toNat := by
                    intro bs'; induction bs' with
                    | nil => intro _ _; exact Nat.le_refl _
                    | cons p restB ihg =>
                      intro venv' gp'; rcases p with ⟨pts, b⟩
                      dsimp only [regaPrepGroup0, prepOneBlock0, prepOneBind0, prepFinishBlock0,
                        prepUpdCtrl0]
                      let bb := bindBlockParams0 pts venv' gp'.st gp'.free gp'.nxt
                      let gp1 : GroupPrepOut0 :=
                        ⟨gp'.ctrl.nextLbl :: gp'.lenv, bb.st,
                         ⟨gp'.ctrl.fnIdx, gp'.ctrl.nextLbl + 1,
                          gp'.ctrl.lblSlots.push
                            (slotsOfVids0 (tyLenU0 pts 0) bb.venv bb.st.vslot [])⟩,
                         bb.free, bb.nxt, ⟨gp'.ctrl.nextLbl, b, bb.venv⟩ :: gp'.metas⟩
                      exact Nat.le_trans
                        (bindBlockParams0_maxSlots_le pts venv' gp'.st gp'.free gp'.nxt)
                        (ihg venv' gp1)
                  have hms := hgp_ms bs venv ⟨lenv, regaPrependLbl0
                    { lblId := lbl, node := .group bs k', venv := venv, lenv := lenv,
                      freeSlots := fr, nextSlot := nxt } s0 c0, c0, fr, nxt, []⟩
                  dsimp only at hms
                  rwa [hs0_bd] at hms
                | let1 _ _ _ | let2Umulw64 _ _ _ | load _ _ _ | store _ _ _ _ | call _ _ _ _ _ =>
                  have lin_ms : ∀ (t0 : RegaTask0) (s1 : RegaSt0),
                      s1.maxSlots.toNat ≤ (stepLinear0 esc t0 s1 c0 tl).st.maxSlots.toNat :=
                    fun t0 s1 => bindRetsN0_maxSlots_le esc (linCnt0 t0.node).toNat
                      (linCnt0 t0.node) 0 (relAndUpdateSt0 esc t0 s1 (emitLinNode0 t0 s1)) rfl
                  dsimp only [regaStep0]
                  exact hs0_bd ▸ lin_ms _ _
              exact Nat.le_trans hstep_ms ih1
      exact aux_ms fuel.toNat fuel preRes.escaped { st with revDirs := st.revDirs } ctrl w₂ rfl
    | cons cur rest₁ =>
      cases pw₁ with
      | nil => simp at hlen_pw
      | cons curPre restPre₁ =>
        cases m₁ with
        | nil => simp at hlen_mw
        | cons mCur restM₁ =>
          have hpos : 0 < N := by
            rw [← hN, List.map_cons]; dsimp only [workNodeCount0]
            have := nodeCount0_pos cur.node; omega
          have hN_lt32 : N < 2 ^ 32 := by
            have htot := hinv.ctrl_nl.2
            rw [List.cons_append] at htot
            have hN_le : N ≤ workNodeCount0 ((cur :: (rest₁ ++ w₂)).map RegaTask0.node) := by
              rw [← hN, List.map_cons, List.map_cons, List.map_append]
              dsimp only [workNodeCount0]
              rw [workNodeCount0_append]
              omega
            omega
          have hf_ne : fuel ≠ 0 := fun h => by
            have := congrArg UInt32.toNat h; rw [UInt32.toNat_zero] at this; omega
          have hN_ne : UInt32.ofNat N ≠ 0 := fun h => by
            have := congrArg UInt32.toNat h
            rw [u32_ofNat_toNat_lt9 hN_lt32, UInt32.toNat_zero] at this
            omega
          have hN1 : (UInt32.ofNat N - 1).toNat = N - 1 := by
            rw [u32_sub1_toNat7 (by rw [u32_ofNat_toNat_lt9 hN_lt32]; exact hpos),
              u32_ofNat_toNat_lt9 hN_lt32]
          have hfl1 : (fuel - 1).toNat = fuel.toNat - 1 := u32_sub1_toNat7 (by omega)
          let st0 := regaPrependLbl0 cur st ctrl
          let ls := regaStep0 preRes.escaped cur st0 ctrl (rest₁ ++ w₂)
          let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
          let lsClean := regaStep0 preRes.escaped cur st0Clean ctrl rest₁
          have hcl := regaStep0_clean_append preRes.escaped cur st ctrl rest₁ w₂
          dsimp only at hcl
          have hsplit_clean :
              regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] } ctrl
                (cur :: rest₁) =
              regaRunAux0 (UInt32.ofNat N - 1) preRes.escaped lsClean.st lsClean.ctrl
                lsClean.work :=
            regaRunAux0_succ hN_ne preRes.escaped { st with revDirs := [] } ctrl cur rest₁
          have hsplit_full1 :
              regaRunAux0 fuel preRes.escaped st ctrl (cur :: (rest₁ ++ w₂)) =
              regaRunAux0 (fuel - 1) preRes.escaped ls.st ls.ctrl ls.work :=
            regaRunAux0_succ hf_ne preRes.escaped st ctrl cur (rest₁ ++ w₂)
          have hcnt_clean : workNodeCount0 (lsClean.work.map RegaTask0.node) + 1 = N := by
            rw [← hN]
            simpa only [lsClean, List.map_cons] using
              regaWorkNodeCount0_children preRes.escaped cur st0Clean ctrl rest₁
          have hlt_clean : workNodeCount0 (lsClean.work.map RegaTask0.node) < N := by omega
          have hcnt_sub : UInt32.ofNat N - 1 =
              UInt32.ofNat (workNodeCount0 (lsClean.work.map RegaTask0.node)) := by
            apply u32_ext7; rw [hN1, u32_ofNat_toNat_lt9 (by omega)]; omega
          have hcur_ok := hinv.items_ok 0 (by simp) (by simp) (by simp)
          simp only [List.cons_append, List.getElem_cons_zero] at hcur_ok
          have hnv_bd : st.nextVid.toNat + binderCount0 cur.node < 2 ^ 31 := by
            have hb := hinv.pre_inv.nextVid_bound
            rw [List.cons_append, List.map_cons] at hb
            dsimp only [workBinderCount0] at hb
            rw [hcur_ok.1] at hb
            rw [← hinv.st_nv] at hb; omega
          have hmono1 := regaStep0_st_mono preRes.escaped cur { st with revDirs := [] } ctrl rest₁
            hinv.st_vslot_sz hnv_bd
          dsimp only at hmono1
          obtain ⟨seenJnz1, pw₁', m₁', hlen_pw', hlen_mw', hout_eq, hinv1⟩ :=
            regaStep0_prefix_split hinv (by simp at hlen_pw; exact hlen_pw)
              (by simp at hlen_mw; exact hlen_mw)
          rw [hcl.1, hcl.2.1, hout_eq] at hinv1
          have hih := ih (workNodeCount0 (lsClean.work.map RegaTask0.node)) hlt_clean (fuel - 1)
            ctx fnIdx fnMaxJump preRes _ _ pw₁' pw₂ seenJnz1 ls.st lsClean.ctrl lsClean.work w₂
            m₁' m₂ rfl (by rw [hfl1]; omega) hlen_pw' hlen_mw' hinv1
          dsimp only at hih
          have hz_clean : { ls.st with revDirs := [] } = { lsClean.st with revDirs := [] } := by
            rw [hcl.2.2]
          let r1' := regaRunAux0 (UInt32.ofNat (workNodeCount0 (lsClean.work.map RegaTask0.node)))
            preRes.escaped { lsClean.st with revDirs := [] } lsClean.ctrl lsClean.work
          have hrev_ls :
              regaRunAux0 (UInt32.ofNat (workNodeCount0 (lsClean.work.map RegaTask0.node)))
                preRes.escaped lsClean.st lsClean.ctrl lsClean.work =
              ({ r1'.1 with revDirs := r1'.1.revDirs ++ lsClean.st.revDirs }, r1'.2) :=
            regaRunAux0_revDirs_append
              (UInt32.ofNat (workNodeCount0 (lsClean.work.map RegaTask0.node)))
              preRes.escaped lsClean.st lsClean.ctrl lsClean.work
          have hr1_eq : regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] }
              ctrl (cur :: rest₁) =
              ({ r1'.1 with revDirs := r1'.1.revDirs ++ lsClean.st.revDirs }, r1'.2) := by
            rw [hsplit_clean, hcnt_sub, hrev_ls]
          have hfull_eq : regaRunAux0 fuel preRes.escaped st ctrl ((cur :: rest₁) ++ w₂) =
              regaRunAux0 (fuel - 1) preRes.escaped ls.st lsClean.ctrl (lsClean.work ++ w₂) := by
            rw [List.cons_append, hsplit_full1, hcl.1, hcl.2.1]
          have hcomb_rev :
              ({ r1'.1 with revDirs := r1'.1.revDirs ++ ls.st.revDirs }, r1'.2) =
              ({ (regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] } ctrl
                  (cur :: rest₁)).1 with
                revDirs :=
                  (regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] } ctrl
                    (cur :: rest₁)).1.revDirs ++ st.revDirs },
               (regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] } ctrl
                  (cur :: rest₁)).2) := by
            rw [hr1_eq, hcl.2.2]
            dsimp only [lsClean, st0Clean]
            simp only [List.append_assoc]
          have hcomb_st := congrArg Prod.fst hcomb_rev
          have hcomb_ctrl := congrArg Prod.snd hcomb_rev
          dsimp only at hcomb_st hcomb_ctrl
          have hih' :
              regaRunAux0 (fuel - 1) preRes.escaped ls.st lsClean.ctrl (lsClean.work ++ w₂) =
                regaRunAux0 (UInt32.ofNat ((fuel - 1).toNat -
                  workNodeCount0 (lsClean.work.map RegaTask0.node))) preRes.escaped
                  { r1'.1 with revDirs := r1'.1.revDirs ++ ls.st.revDirs } r1'.2 w₂ ∧
              ls.st.nextVid.toNat ≤ r1'.1.nextVid.toNat ∧
              r1'.1.maxSlots.toNat ≤
                (regaRunAux0 (fuel - 1) preRes.escaped ls.st lsClean.ctrl
                  (lsClean.work ++ w₂)).1.maxSlots.toNat ∧
              ls.st.maxSlots.toNat ≤ r1'.1.maxSlots.toNat ∧
              (∀ v < ls.st.nextVid.toNat,
                arrGetU0 r1'.1.vslot (UInt32.ofNat v) = arrGetU0 ls.st.vslot (UInt32.ofNat v)) ∧
              ∃ seenJnz' nextSc' preSt',
                RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc' preSt' pw₂ seenJnz'
                  { r1'.1 with revDirs := r1'.1.revDirs ++ ls.st.revDirs } r1'.2 w₂ m₂ := by
            rwa [hz_clean] at hih
          have hsub_fuel : (fuel - 1).toNat - workNodeCount0 (lsClean.work.map RegaTask0.node) =
              fuel.toNat - N := by
            rw [hfl1]; omega
          have hls_eq : ls.st.nextVid = lsClean.st.nextVid ∧
              ls.st.maxSlots = lsClean.st.maxSlots ∧ ls.st.vslot = lsClean.st.vslot := by
            rw [hcl.2.2]; exact ⟨rfl, rfl, rfl⟩
          refine ⟨?_, ?_, ?_, ?_, fun v hv => ?_, ?_⟩
          · rw [List.cons_append, hsplit_full1, hcl.1, hcl.2.1, hih'.1, ← hsub_fuel,
              hcomb_st, hcomb_ctrl]
          · rw [hr1_eq]; exact Nat.le_trans hmono1.1 (hls_eq.1 ▸ hih'.2.1)
          · rw [hr1_eq, hfull_eq]; exact hih'.2.2.1
          · rw [hr1_eq]; exact Nat.le_trans hmono1.2.1 (hls_eq.2.1 ▸ hih'.2.2.2.1)
          · rw [hr1_eq]
            have hv2 : v < ls.st.nextVid.toNat := hls_eq.1 ▸ Nat.lt_of_lt_of_le hv hmono1.1
            exact (hih'.2.2.2.2.1 v hv2).trans (hls_eq.2.2 ▸ hmono1.2.2 v hv)
          · rw [← hcomb_st, ← hcomb_ctrl]; exact hih'.2.2.2.2.2

/-! ### Program-Slice Helpers, `FnFrameInv0` Lemmas, & Binder Execution Specs -/

theorem compileFnFinish0_rev_eq (fn : TFlatFn0) (r : RegaSt0) :
    let fSz := x64FrameSizeU0 r.maxSlots
    revDirAux0 (emitSpAdj0 true fSz [.label (.sym fn.name)])
      (patchEpilogues0 fSz (revDirAux0 r.revDirs []) []) =
    .label (.sym fn.name) ::
      ((emitSpAdj0 true fSz []).reverse ++
        patchEpilogues0 fSz (revDirAux0 r.revDirs []) []) := by
  intro fSz
  rw [(emitSpAdj0_acc true fSz (Or.inl rfl) [.label (.sym fn.name)]).1,
    revDirAux0_eq, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.cons_append]

theorem infix_getElem?_zero {α : Type} {xs ys : List α} {k : Nat} {x : α}
    (hinf : xs.IsInfixAt ys k) (hx : xs[0]? = some x) : ys[k]? = some x := by
  cases xs with
  | nil => simp at hx
  | cons a _ =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
    subst hx
    exact (List.IsInfixAt.cons hinf).1

theorem list_drop_getElem9 {α : Type} (xs ys : List α) (k j : Nat)
    (hj : j < ys.length) (hkj : k + j < xs.length) (he : xs.drop k = ys) :
    ys[j]'hj = xs[k + j]'hkj := by
  subst he; exact List.getElem_drop

theorem list_getElem_eq9 {α : Type} (xs : List α) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (he : i = j) :
    xs[i]'hi = xs[j]'hj := by
  subst he; rfl

theorem infix_labelAddr_eq {h : Host} {prog : List Directive} {k : Nat} {l : Sym}
    (hu : x64ScalarTarget.LabelsUnique h)
    (hinf : prog.IsInfixAt (x64ScalarMach.prog h) k)
    (hl : prog[0]? = some (x64Frame.label l)) :
    x64ScalarMach.labelAddr h l = x64ScalarMach.addrOf h k := by
  have hk := infix_getElem?_zero hinf hl
  exact x64ScalarTarget.frameSpec.labelAddr_eq hk fun j hj heq =>
    absurd (hu j k l heq hk) (Nat.ne_of_lt hj)

theorem defined_labelAddr_eq {h : Host} {l : Sym}
    (hu : x64ScalarTarget.LabelsUnique h) (hd : x64ScalarTarget.Defined h l) :
    ∃ j, (x64ScalarMach.prog h)[j]? = some (x64Frame.label l) ∧
      x64ScalarMach.labelAddr h l = x64ScalarMach.addrOf h j := by
  obtain ⟨j, hj⟩ := hd
  exact ⟨j, hj, x64ScalarTarget.frameSpec.labelAddr_eq hj fun i hi heq =>
    absurd (hu i j l heq hj) (Nat.ne_of_lt hi)⟩

theorem listNoSpZero0_prependLbl (cur : RegaTask0) (st : RegaSt0) (ctrl : CtrlSt0) :
    ListNoSpZero0 (regaPrependLbl0 cur { st with revDirs := [] } ctrl).revDirs := by
  dsimp only [regaPrependLbl0]; split
  · exact listNoSpZero0_nil
  · exact listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil

theorem regaPrependLbl0_dirs_eq (cur : RegaTask0) (st : RegaSt0) (ctrl : CtrlSt0) :
    let st0 := regaPrependLbl0 cur { st with revDirs := [] } ctrl
    st0.revDirs = if cur.lblId = 0 then [] else [.label (.loc ctrl.fnIdx cur.lblId)] := by
  dsimp only [regaPrependLbl0]; split <;> rfl

theorem sub_add_ofNat_le (a : BitVec 64) {n k : Nat} (hle : k ≤ n) :
    a - BitVec.ofNat 64 n + BitVec.ofNat 64 k = a - BitVec.ofNat 64 (n - k) := by
  have h1 : BitVec.ofNat 64 n = BitVec.ofNat 64 (n - k) + BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.add_mod_mod, Nat.mod_add_mod, Nat.sub_add_cancel hle]
  rw [h1]
  grind

theorem fnFrameInv0_mem_slots {ns : UInt32} {s0 : MachineData} {ra0 : Int64} {n : Nat}
    {Rf : Mem 64 → Prop} {mCur : Mem 64} {s : MachineData} {σ : List (BitVec 64)}
    (h : FnFrameInv0 ns s0 ra0 n Rf mCur s σ) :
    s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆
      (Eq mCur ⋆ x64ScalarFramePreds.Saved (s0.regs.get64 .rsp) ra0 ns.toNat ⋆
        region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆ Rf) :=
  sep_cast h.2.2.2 (by ac_rfl)

theorem fnFrameInv0_of_eq {ns : UInt32} {s0 : MachineData} {ra0 : Int64} {n : Nat}
    {Rf : Mem 64 → Prop} {mCur : Mem 64} {s s' : MachineData} {σ : List (BitVec 64)}
    {clob : List Reg64} {fClob : FlagMask}
    (h : FnFrameInv0 ns s0 ra0 n Rf mCur s σ)
    (hfr : x64ScalarMach.Frame x64CondReads s s' clob [] fClob)
    (hrsp : .rsp ∉ clob) (hcs : ∀ r ∈ x64Frame.calleeSaved, r ∉ clob)
    (hmem : s'.dmem = s.dmem) :
    FnFrameInv0 ns s0 ra0 n Rf mCur s' σ := by
  obtain ⟨hlen, hr, hcal, hm⟩ := h
  have hrsp' : s'.regs.get64 .rsp = s.regs.get64 .rsp := hfr.1 .rsp hrsp
  refine ⟨hlen, hrsp'.trans hr,
    fun r hrm => (hfr.1 r (hcs r hrm)).trans (hcal r hrm), ?_⟩
  rw [hmem, hrsp']
  exact hm

theorem escOuterAgree0_of_slotsAgree0 {esc : Array Nat} {preSt : PreSt0} {st : RegaSt0}
    {p : PreItem0} {cur : RegaTask0} {vT : List Ty0} {vs : List ((ty : Ty) × Val ty)}
    {σ : List (BitVec 64)} {info : LblInfo0} {outerVs : List ((ty : Ty) × Val ty)}
    {pLen : Nat}
    (hag : SlotsAgree0 esc preSt st p cur vT vs σ)
    (hplen : pLen + info.outerVenv.length = cur.venv.length)
    (hv : cur.venv.drop pLen = info.outerVenv)
    (hvt : vT.drop pLen = info.outerVT)
    (hvs : vs.drop pLen = outerVs) :
    EscOuterAgree0 esc st.vslot info outerVs σ := by
  obtain ⟨hv_len, henv, hslot⟩ := hag
  have hov_len : info.outerVenv.length = outerVs.length := by
    rw [← hv, ← hvs, List.length_drop, List.length_drop, hv_len]
  have henv_drop : EnvTypesOk0 info.outerVT outerVs := by
    rw [← hvt, ← hvs]
    have hplen_le : pLen ≤ vT.length := by have := envTypesOk0_length henv; omega
    clear hvt hvs hv hplen hslot hv_len hov_len
    induction pLen generalizing vT vs with
    | zero => exact henv
    | succ k ih =>
      cases vT with
      | nil => simp at hplen_le
      | cons _ ts => cases vs with
        | nil => exact False.elim henv
        | cons _ ws => exact ih henv.2 (by simp at hplen_le; omega)
  refine ⟨hov_len, henv_drop, fun idx hi hesc => ?_⟩
  have hpi : pLen + idx < cur.venv.length := by omega
  have hvid_eq : info.outerVenv[idx]'hi = cur.venv[pLen + idx]'hpi :=
    list_drop_getElem9 cur.venv info.outerVenv pLen idx hi hpi hv
  have hlv : LiveInTask0 esc preSt st p cur (cur.venv[pLen + idx]'hpi).toNat :=
    Or.inl ⟨hvid_eq ▸ hesc, by rw [UInt32.ofNat_toNat]; exact List.getElem_mem _⟩
  obtain ⟨hsl, hvs', ht', hcanon⟩ := hslot (pLen + idx) hpi hlv
  have hvs_lt : idx < outerVs.length := hov_len ▸ hi
  have ht_lt : idx < info.outerVT.length := by have := envTypesOk0_length henv_drop; omega
  have hvs_eq : outerVs[idx]'hvs_lt = vs[pLen + idx]'hvs' :=
    list_drop_getElem9 vs outerVs pLen idx hvs_lt hvs' hvs
  have hvt_eq : info.outerVT[idx]'ht_lt = vT[pLen + idx]'ht' :=
    list_drop_getElem9 vT info.outerVT pLen idx ht_lt ht' hvt
  have hsl' : (arrGetU0 st.vslot (info.outerVenv[idx]'hi)).toNat < σ.length := hvid_eq ▸ hsl
  refine ⟨hsl', hvs_lt, ht_lt, ?_⟩
  rw [list_getElem_eq9 σ hsl' hsl (congrArg UInt32.toNat (congrArg (arrGetU0 st.vslot) hvid_eq)),
    hvs_eq, hvt_eq]
  exact hcanon

theorem escOuterAgree0_vslot_congr {esc : Array Nat} {vsl1 vsl2 : Array Nat}
    {info : LblInfo0} {outerVs : List ((ty : Ty) × Val ty)} {σ : List (BitVec 64)} {bound : Nat}
    (hbd : ∀ w ∈ info.outerVenv, w.toNat < bound)
    (heq : ∀ v < bound, arrGetU0 vsl1 (UInt32.ofNat v) = arrGetU0 vsl2 (UInt32.ofNat v))
    (h : EscOuterAgree0 esc vsl1 info outerVs σ) :
    EscOuterAgree0 esc vsl2 info outerVs σ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun idx hi hesc => ?_⟩
  have hw := heq _ (hbd _ (List.getElem_mem hi))
  rw [UInt32.ofNat_toNat] at hw
  obtain ⟨hsl, hvs, ht, hcanon⟩ := h3 idx hi hesc
  have hsl' : (arrGetU0 vsl2 (info.outerVenv[idx]'hi)).toNat < σ.length := hw ▸ hsl
  refine ⟨hsl', hvs, ht, ?_⟩
  rw [list_getElem_eq9 σ hsl' hsl (congrArg UInt32.toNat hw.symm)]
  exact hcanon

theorem escOuterAgree0_mem_congr {esc : Array Nat} {vslot : Array Nat}
    {info : LblInfo0} {outerVs : List ((ty : Ty) × Val ty)} {σ σ' : List (BitVec 64)}
    (hlen : σ'.length = σ.length)
    (hmem : ∀ idx (hi : idx < info.outerVenv.length), esc.getD info.outerVenv[idx].toNat 0 = 1 →
      ∀ hsl : (arrGetU0 vslot (info.outerVenv[idx]'hi)).toNat < σ.length,
        σ'[(arrGetU0 vslot (info.outerVenv[idx]'hi)).toNat]'(hlen ▸ hsl) =
          σ[(arrGetU0 vslot (info.outerVenv[idx]'hi)).toNat]'hsl)
    (h : EscOuterAgree0 esc vslot info outerVs σ) :
    EscOuterAgree0 esc vslot info outerVs σ' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun idx hi hesc => ?_⟩
  obtain ⟨hsl, hvs, ht, hcanon⟩ := h3 idx hi hesc
  refine ⟨hlen ▸ hsl, hvs, ht, ?_⟩
  rw [hmem idx hi hesc hsl]; exact hcanon

theorem glEntrySem0_eq_vslot_nextSlot {h : Host} {symName : Sym0 → Sym}
    {post : MachineState → Prop} {ns : UInt32} {s0 : MachineData} {ra0 : Int64} {n : Nat}
    {Rf : Mem 64 → Prop} {esc : Array Nat} {st st' : RegaSt0} {cur cur' : RegaTask0}
    {mCur mCur' : TaskMeta0} {vs : List ((ty : Ty) × Val ty)} {fnIdx : UInt32} :
    ∀ {gl : List LblInfo0} {ls : List ((ts : List Ty) × Cont ts)},
      GlEntriesSem0 h symName post ns s0 ra0 n Rf esc st cur mCur vs fnIdx gl ls →
      cur.nextSlot.toNat ≤ cur'.nextSlot.toNat →
      cur'.venv = cur.venv → mCur'.vT = mCur.vT →
      (∀ info ∈ gl, ∃ N,
        (∀ w ∈ info.outerVenv, w.toNat < N) ∧
        ∀ v < N, arrGetU0 st'.vslot (UInt32.ofNat v) = arrGetU0 st.vslot (UInt32.ofNat v)) →
      GlEntriesSem0 h symName post ns s0 ra0 n Rf esc st' cur' mCur' vs fnIdx gl ls
  | [], [], _, _, _, _, _ => trivial
  | [], _ :: _, hgl, _, _, _, _ => False.elim hgl
  | _ :: _, [], hgl, _, _, _, _ => False.elim hgl
  | info :: glRest, lentry :: lsRest, hgl, hnxt, hvenv, hvT, houter => by
    refine ⟨?_, glEntrySem0_eq_vslot_nextSlot hgl.2 hnxt hvenv hvT
      fun inf hinf => houter inf (List.mem_cons_of_mem _ hinf)⟩
    obtain ⟨hn_le, hdef, outerVs, pLen, hplen, hv, hvt, hvs, J, rfl, hj⟩ := hgl.1
    obtain ⟨N, hN_bd, hN_eq⟩ := houter info List.mem_cons_self
    refine ⟨Nat.le_trans hn_le hnxt, hdef, outerVs, pLen, hvenv ▸ hplen, hvenv ▸ hv,
      hvT ▸ hvt, hvs, J, rfl, fun xs m' hJ s' σ' hfr hesc htup => ?_⟩
    exact hj xs m' hJ s' σ' hfr (escOuterAgree0_vslot_congr hN_bd hN_eq hesc) htup

theorem glEntrySem0_pushTys0 {h : Host} {symName : Sym0 → Sym}
    {post : MachineState → Prop} {ns : UInt32} {s0 : MachineData} {ra0 : Int64} {n : Nat}
    {Rf : Mem 64 → Prop} {esc : Array Nat} {st st' : RegaSt0} {cur cur' : RegaTask0}
    {mCur mCur' : TaskMeta0} {vs : List ((ty : Ty) × Val ty)} {fnIdx : UInt32}
    {bs : List Ty0} {rvs : Tup Val (ty0ListToTy bs)} {nv : UInt32} :
    ∀ {gl : List LblInfo0} {ls : List ((ts : List Ty) × Cont ts)},
      GlEntriesSem0 h symName post ns s0 ra0 n Rf esc st cur mCur vs fnIdx gl ls →
      cur.nextSlot.toNat ≤ cur'.nextSlot.toNat →
      cur'.venv = pushFreshVids0 bs.length nv cur.venv →
      mCur'.vT = pushTys0 bs mCur.vT →
      (∀ info ∈ gl, ∃ N,
        (∀ w ∈ info.outerVenv, w.toNat < N) ∧
        ∀ v < N, arrGetU0 st'.vslot (UInt32.ofNat v) = arrGetU0 st.vslot (UInt32.ofNat v)) →
      GlEntriesSem0 h symName post ns s0 ra0 n Rf esc st' cur' mCur'
        (pushTup rvs vs) fnIdx gl ls
  | [], [], _, _, _, _, _ => trivial
  | [], _ :: _, hgl, _, _, _, _ => False.elim hgl
  | _ :: _, [], hgl, _, _, _, _ => False.elim hgl
  | info :: glRest, lentry :: lsRest, hgl, hnxt, hvenv, hvT, houter => by
    refine ⟨?_, glEntrySem0_pushTys0 hgl.2 hnxt hvenv hvT
      fun inf hinf => houter inf (List.mem_cons_of_mem _ hinf)⟩
    obtain ⟨hn_le, hdef, outerVs, pLen, hplen, hv, hvt, hvs, J, rfl, hj⟩ := hgl.1
    obtain ⟨N, hN_bd, hN_eq⟩ := houter info List.mem_cons_self
    refine ⟨Nat.le_trans hn_le hnxt, hdef, outerVs, bs.length + pLen, ?_, ?_, ?_, ?_, J, rfl,
      fun xs m' hJ s' σ' hfr hesc htup => ?_⟩
    · rw [hvenv, pushFreshVids0_length]; omega
    · rw [hvenv, ← list_drop_drop9, pushFreshVids0_drop, hv]
    · rw [hvT, ← list_drop_drop9, pushTys0_drop, hvt]
    · rw [← list_drop_drop9, pushTup_drop, hvs]
    · exact hj xs m' hJ s' σ' hfr (escOuterAgree0_vslot_congr hN_bd hN_eq hesc) htup

/-- Slot agreement for freshly bound variables (`nv .. nv + ts.length - 1`). -/
@[expose] def PushAgree0 (esc : Array Nat) (remUses vslot : Array Nat) (nv : UInt32) :
    (ts : List Ty0) → Tup Val (ty0ListToTy ts) → List (BitVec 64) → Prop
  | [], (), _ => True
  | t :: rest, (x, xs), σ =>
    ((0 < remUses.getD nv.toNat 0 ∨ 0 < esc.getD nv.toNat 0) →
      ∃ hsl : (arrGetU0 vslot nv).toNat < σ.length,
        σ[(arrGetU0 vslot nv).toNat]'hsl = toCanon64 t x) ∧
    PushAgree0 esc remUses vslot (nv + 1) rest xs σ

theorem pushAgree0_mono_esc_rem {esc remUses : Array Nat} {vslot1 vslot2 : Array Nat}
    {σ : List (BitVec 64)} :
    ∀ (ts : List Ty0) (xs : Tup Val (ty0ListToTy ts)) (nv : UInt32),
      nv.toNat + ts.length < 2 ^ 31 →
      (∀ k < ts.length, arrGetU0 vslot1 (nv + UInt32.ofNat k) =
        arrGetU0 vslot2 (nv + UInt32.ofNat k)) →
      PushAgree0 esc remUses vslot1 nv ts xs σ → PushAgree0 esc remUses vslot2 nv ts xs σ
  | [], (), _, _, _, _ => trivial
  | _ :: rest, (_, xs), nv, hnv, heq, ⟨h1, h2⟩ => by
    simp only [List.length_cons] at hnv
    have heq0 := heq 0 (Nat.zero_lt_succ _)
    rw [show nv + UInt32.ofNat 0 = nv from u32_ofNat_add_eq7 nv 0 (by omega) ▸
      congrArg UInt32.ofNat (Nat.add_zero nv.toNat) ▸ UInt32.ofNat_toNat] at heq0
    refine ⟨fun hneed => by rw [← heq0]; exact h1 hneed,
      pushAgree0_mono_esc_rem rest xs (nv + 1)
        (by rw [u32_add1_toNat7 (by omega)]; omega) (fun k hk => by
          have := heq (k + 1) (Nat.succ_lt_succ hk)
          rwa [u32_add_ofNat_succ9] at this) h2⟩

theorem pushFresh_slotsAgree0_aux (esc : Array Nat) (preSt' : PreSt0) (st' : RegaSt0)
    (p' : PreItem0) (t' : RegaTask0) (σ : List (BitVec 64)) :
    ∀ (ts : List Ty0) (xs : Tup Val (ty0ListToTy ts)) (nv : UInt32)
      (venv : List UInt32) (vT : List Ty0) (vs : List ((ty : Ty) × Val ty)),
      nv.toNat + ts.length < 2 ^ 31 →
      venv.length = vs.length → EnvTypesOk0 vT vs →
      (∀ v ∈ venv, v.toNat < nv.toNat) →
      (∀ (idx : Nat) (_hi : idx < venv.length),
        let vid := venv[idx]
        LiveInTask0 esc preSt' st' p' t' vid.toNat →
        ∃ (hsl : (arrGetU0 st'.vslot vid).toNat < σ.length) (hvs : idx < vs.length)
          (ht : idx < vT.length),
          HoldsCanon640 vT[idx] vs[idx] σ[(arrGetU0 st'.vslot vid).toNat]) →
      PushAgree0 esc st'.remUses st'.vslot nv ts xs σ →
      (pushFreshVids0 ts.length nv venv).length = (pushTup xs vs).length ∧
      EnvTypesOk0 (pushTys0 ts vT) (pushTup xs vs) ∧
      ∀ (idx : Nat) (hi : idx < (pushFreshVids0 ts.length nv venv).length),
        let vid := (pushFreshVids0 ts.length nv venv)[idx]
        LiveInTask0 esc preSt' st' p' t' vid.toNat →
        ∃ (hsl : (arrGetU0 st'.vslot vid).toNat < σ.length)
          (hvs : idx < (pushTup xs vs).length)
          (ht : idx < (pushTys0 ts vT).length),
          HoldsCanon640 (pushTys0 ts vT)[idx] (pushTup xs vs)[idx]
            σ[(arrGetU0 st'.vslot vid).toNat] := by
  intro ts
  induction ts with
  | nil =>
    intro xs nv venv vT vs _ hlen henv _ hold _
    cases xs
    exact ⟨hlen, henv, hold⟩
  | cons t rest ih =>
    intro xs nv venv vT vs hnv hlen henv hbd hold hpa
    simp only [List.length_cons] at hnv
    rcases xs with ⟨x, restX⟩
    have hnv1 : (nv + 1).toNat = nv.toNat + 1 := u32_add1_toNat7 (by omega)
    dsimp only [PushAgree0] at hpa
    have hbd1 : ∀ v ∈ nv :: venv, v.toNat < (nv + 1).toNat := by
      intro v hv; rcases List.mem_cons.mp hv with rfl | hv'
      · rw [hnv1]; omega
      · have := hbd v hv'; rw [hnv1]; omega
    have hold1 : ∀ (idx : Nat) (_hi : idx < (nv :: venv).length),
        let vid := (nv :: venv)[idx]
        LiveInTask0 esc preSt' st' p' t' vid.toNat →
        ∃ (hsl : (arrGetU0 st'.vslot vid).toNat < σ.length)
          (hvs : idx < (⟨ty0ToTy t, x⟩ :: vs).length)
          (ht : idx < (t :: vT).length),
          HoldsCanon640 (t :: vT)[idx] (⟨ty0ToTy t, x⟩ :: vs)[idx]
            σ[(arrGetU0 st'.vslot vid).toNat] := by
      intro idx hi
      cases idx with
      | zero =>
        dsimp only [List.getElem_cons_zero]
        intro hlv
        have hneed : 0 < st'.remUses.getD nv.toNat 0 ∨ 0 < esc.getD nv.toNat 0 := by
          rcases hlv with ⟨hes, _⟩ | ⟨_, _, hpos⟩
          · right; omega
          · left; exact hpos
        obtain ⟨hsl, heq⟩ := hpa.1 hneed
        refine ⟨hsl, Nat.zero_lt_succ _, Nat.zero_lt_succ _, ?_⟩
        rw [heq]; exact holdsCanon640_mk x
      | succ idx' =>
        dsimp only [List.getElem_cons_succ]
        intro hlv
        obtain ⟨hsl, hvs, ht, hcanon⟩ := hold idx' (Nat.lt_of_succ_lt_succ hi) hlv
        exact ⟨hsl, Nat.succ_lt_succ hvs, Nat.succ_lt_succ ht, hcanon⟩
    exact ih restX (nv + 1) (nv :: venv) (t :: vT) (⟨ty0ToTy t, x⟩ :: vs)
      (by rw [hnv1]; omega) (by simp [hlen]) (envTypesOk0_cons henv) hbd1 hold1 hpa.2

private theorem arrGetU0_eq9 (arr : Array Nat) (i : UInt32) :
    (arrGetU0 arr i).toNat = arr.getD i.toNat 0 % 2 ^ 32 := by
  dsimp only [arrGetU0]; exact u32_toNat_ofNat7 _

theorem allocSlot0_spec9 (free : List UInt32) (nxt maxSl : UInt32) (maxBd : Nat)
    (hinv : SlotPoolInv0 free nxt maxSl maxBd) (hlt : nxt.toNat + 1 ≤ maxBd) :
    let sp := allocSlot0 free nxt maxSl
    SlotPoolInv0 sp.free sp.nxt sp.maxSlots maxBd ∧
    sp.slot.toNat < sp.nxt.toNat ∧
    nxt.toNat ≤ sp.nxt.toNat ∧ sp.nxt.toNat ≤ nxt.toNat + 1 ∧
    (sp.slot ∈ free ∨ sp.slot = nxt) ∧
    (∀ x, x ∈ sp.free ↔ x ∈ free ∧ x ≠ sp.slot) := by
  cases free with
  | nil =>
    dsimp only [allocSlot0]
    obtain ⟨_, _, h1, h2, hmax_bd⟩ := hinv
    have hadd1 : (nxt + 1).toNat = nxt.toNat + 1 := u32_add1_toNat7 (by omega)
    have hlt_s : nxt.toNat < (nxt + 1).toNat := by omega
    refine ⟨⟨List.nodup_nil, fun _ hm => by simp at hm, ?_, ?_, hmax_bd⟩,
      hlt_s, by omega, by omega, Or.inr rfl, fun x => by simp⟩
    · rw [u32Max0_toNat, hadd1]; exact Nat.le_max_right _ _
    · rw [u32Max0_toNat, hadd1]; exact Nat.max_le.mpr ⟨h2, hlt⟩
  | cons s rest =>
    dsimp only [allocSlot0]
    obtain ⟨hnd0, hflt0, h1, h2, hmax_bd⟩ := hinv
    obtain ⟨hnin, hnd⟩ := List.nodup_cons.mp hnd0
    have hs_lt : s.toNat < nxt.toNat := hflt0 s List.mem_cons_self
    have hadd1 : (s + 1).toNat = s.toNat + 1 := u32_add1_toNat7 (by omega)
    refine ⟨⟨hnd, fun x hx => hflt0 x (List.mem_cons_of_mem _ hx), ?_, ?_, hmax_bd⟩,
      hs_lt, Nat.le_refl _, Nat.le_add_right _ _, Or.inl List.mem_cons_self, fun x => ?_⟩
    · rw [u32Max0_toNat]; exact Nat.le_trans h1 (Nat.le_max_left _ _)
    · rw [u32Max0_toNat, hadd1]; exact Nat.max_le.mpr ⟨h2, by omega⟩
    · constructor
      · intro hx; exact ⟨List.mem_cons_of_mem _ hx, fun h => hnin (h ▸ hx)⟩
      · rintro ⟨hx, hne⟩; rcases List.mem_cons.mp hx with rfl | hx'
        · exact absurd rfl hne
        · exact hx'

theorem bindRetsN0_run_spec {symName : Sym0 → Sym} {h : Host} {esc : Array Nat}
    {G : Mem 64 → Prop} {post : MachineState → Prop} :
    ∀ (ts : List Ty0) (k : Nat) (rem idx : UInt32) (bl : BindListOut0)
      (xs : Tup Val (ty0ListToTy ts)) (σ : List (BitVec 64)) (s : MachineData) (maxBd : Nat),
      let bl0 : BindListOut0 := { bl with st := { bl.st with revDirs := [] } }
      let bl' := bindRetsN0 esc rem idx bl0
      rem.toNat = ts.length → idx.toNat + ts.length ≤ 7 →
      tupAbiHolds0 s true idx.toNat ts xs →
      bl.st.vslot.size = bl.st.nextVid.toNat →
      bl.st.nextVid.toNat + ts.length < 2 ^ 31 →
      SlotPoolInv0 bl.free bl.nxt bl.st.maxSlots maxBd →
      bl.nxt.toNat + ts.length ≤ maxBd →
      bl'.st.maxSlots.toNat ≤ σ.length →
      (∀ j < ts.length, esc.getD (bl.st.nextVid.toNat + j) 0 < 2 ^ 32 ∧
        bl.st.remUses.getD (bl.st.nextVid.toNat + j) 0 < 2 ^ 32) →
      (s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆ G) →
      x64ScalarMach.FallsTo x64CondReads h k
        (toAmd64Program symName (emitFwd0 bl'.st.revDirs)) [.r10] [] maskNone s
        (fun s' => ∃ (σ' : List (BitVec 64)) (hσ' : σ'.length = σ.length),
          (∀ q : UInt32, q.toNat < bl.nxt.toNat → q ∉ bl.free →
            ∀ hq : q.toNat < σ.length, σ'[q.toNat]'(hσ' ▸ hq) = σ[q.toNat]'hq) ∧
          PushAgree0 esc bl'.st.remUses bl'.st.vslot bl.st.nextVid ts xs σ' ∧
          (s'.dmem =⋆ array64 (s'.regs.get64 .rsp) σ' ⋆ G)) post := by
  intro ts
  induction ts with
  | nil =>
    intro k rem idx bl xs σ s maxBd bl0 bl' hrem _ _ _ _ _ _ _ _ hmem
    cases xs
    have hr0 : rem = 0 := u32_ext7 hrem
    have hrev : bl'.st.revDirs = [] := by
      dsimp only [bl', bl0]; subst hr0; rw [bindRetsN0.eq_def]; simp
    rw [hrev]
    dsimp only [emitFwd0, List.reverse_nil, toAmd64Program, List.flatMap_nil]
    refine Machine.FallsTo.nil ⟨σ, rfl, fun _ _ _ _ => rfl, trivial, hmem⟩
  | cons t rest ih =>
    intro k rem idx bl xs σ s maxBd bl0 bl' hrem hidx htup hvsz hnv hpool hnxt hms hbd hmem
    change Val (ty0ToTy t) × Tup Val (ty0ListToTy rest) at xs
    simp only [List.length_cons] at hnv hnxt
    rcases xs with ⟨x, restX⟩
    dsimp only [tupAbiHolds0] at htup
    have hrem_pos : 0 < rem.toNat := by rw [hrem]; simp
    have hrne : rem ≠ 0 := fun h => by simp [h] at hrem_pos
    have hsub : (rem - 1).toNat = rest.length := by
      rw [u32_sub1_toNat7 hrem_pos, hrem]; simp
    have hidx1 : (idx + 1).toNat = idx.toNat + 1 :=
      u32_add1_toNat7 (by simp only [List.length_cons] at hidx; omega)
    let bo := bindOneSlot0 esc (abiRegAt0 true idx) bl0.st bl0.free bl0.nxt
    let bl1 : BindListOut0 := ⟨bo.vid :: bl0.venv, bo.st, bo.free, bo.nxt⟩
    let bl1Clean : BindListOut0 := { bl1 with st := { bl1.st with revDirs := [] } }
    let bl'1 := bindRetsN0 esc (rem - 1) (idx + 1) bl1Clean
    have hbo_spec := bindRetsN0_spec esc (t :: rest).length rem idx bl0 maxBd
      hrem hvsz (by simp only [List.length_cons]; exact hnv)
      hpool (by simp only [List.length_cons]; exact hnxt) hbd
    have hbr_tail := bindRetsN0_revDirs esc rest.length (rem - 1) (idx + 1) bl1 hsub
    dsimp only at hbr_tail
    have hbl'_eq : bl' = bindRetsN0 esc (rem - 1) (idx + 1) bl1 := by
      dsimp only [bl']; rw [bindRetsN0.eq_def]; simp only [hrne, ↓reduceDIte]
      rfl
    have hrev_split : bl'.st.revDirs = bl'1.st.revDirs ++ bo.st.revDirs := by
      rw [hbl'_eq, hbr_tail.2.2.2.1]
    have hbl'_st_eq : bl'.st = { bl'1.st with revDirs := bl'1.st.revDirs ++ bo.st.revDirs } := by
      rw [hbl'_eq, hbr_tail.2.2.2.1]
    have hbo_ms_le : bo.st.maxSlots.toNat ≤ bl'.st.maxSlots.toNat := by
      rw [hbl'_eq]
      exact bindRetsN0_maxSlots_le esc rest.length (rem - 1) (idx + 1) bl1 hsub
    have h1_nv : bo.st.nextVid.toNat = bl.st.nextVid.toNat + 1 := by
      dsimp only [bl0, bo, bindOneSlot0]; split <;> exact u32_add1_toNat7 (by omega)
    have h1_nv_eq : bo.st.nextVid = bl.st.nextVid + 1 := by
      dsimp only [bl0, bo, bindOneSlot0]; split <;> rfl
    have h1_sz : bo.st.vslot.size = bo.st.nextVid.toNat := by
      rw [h1_nv]; dsimp only [bl0, bo, bindOneSlot0]
      split <;> simp only [Array.size_push, hvsz]
    have h1_rem : bo.st.remUses = bl.st.remUses := by
      dsimp only [bl0, bo, bindOneSlot0]; split <;> rfl
    have h1_pool : SlotPoolInv0 bo.free bo.nxt bo.st.maxSlots maxBd := by
      dsimp only [bo, bindOneSlot0]; split
      · exact (allocSlot0_spec9 bl0.free bl0.nxt bl0.st.maxSlots maxBd hpool
          (by dsimp only [bl0]; omega)).1
      · exact hpool
    have h1_nxt_le : bl.nxt.toNat ≤ bo.nxt.toNat ∧ bo.nxt.toNat ≤ bl.nxt.toNat + 1 := by
      dsimp only [bo, bindOneSlot0]; split
      · have hs := allocSlot0_spec9 bl0.free bl0.nxt bl0.st.maxSlots maxBd hpool
          (by dsimp only [bl0]; omega)
        exact ⟨hs.2.2.1, hs.2.2.2.1⟩
      · exact ⟨Nat.le_refl _, Nat.le_succ _⟩
    have h1_fr : ∀ x, x ∈ bo.free → x ∈ bl.free := by
      intro q hq; dsimp only [bo, bindOneSlot0] at hq; split at hq
      · exact ((allocSlot0_spec9 bl0.free bl0.nxt bl0.st.maxSlots maxBd hpool
          (by dsimp only [bl0]; omega)).2.2.2.2.2 q).mp hq |>.1
      · exact hq
    have hneed_iff :
        ((decide (0 < arrGetU0 bl0.st.remUses bl0.st.nextVid) ||
          decide (0 < arrGetU0 esc bl0.st.nextVid)) = true) ↔
        (0 < bl.st.remUses.getD bl.st.nextVid.toNat 0 ∨
          0 < esc.getD bl.st.nextVid.toNat 0) := by
      have hre := arrGetU0_eq9 bl0.st.remUses bl0.st.nextVid
      have hee := arrGetU0_eq9 esc bl0.st.nextVid
      dsimp only [bl0] at hre hee ⊢
      rw [Nat.mod_eq_of_lt (by simpa only [Nat.add_zero] using (hbd 0 (by simp)).2)] at hre
      rw [Nat.mod_eq_of_lt (by simpa only [Nat.add_zero] using (hbd 0 (by simp)).1)] at hee
      simp only [Bool.or_eq_true, decide_eq_true_eq, UInt32.lt_iff_toNat_lt, UInt32.toNat_zero,
        hre, hee]
    have h1_slot_spec := bindRetsN0_spec esc rest.length (rem - 1) (idx + 1) bl1Clean maxBd
      hsub h1_sz (by dsimp only [bl1Clean, bl1]; rw [h1_nv]; omega) h1_pool
      (by dsimp only [bl1Clean, bl1]; omega)
      (fun j hj => by
        dsimp only [bl1Clean, bl1]; rw [h1_nv, h1_rem, Nat.add_assoc, Nat.add_comm 1 j]
        exact hbd (j + 1) (by simp only [List.length_cons]; omega))
    dsimp only [bl1Clean, bl1] at h1_slot_spec
    have hbo_exec :
        x64ScalarMach.FallsTo x64CondReads h k
          (toAmd64Program symName (emitFwd0 bo.st.revDirs)) [.r10] [] maskNone s
          (fun s1 => ∃ (σ1 : List (BitVec 64)) (hσ1 : σ1.length = σ.length),
            (∀ q : UInt32, q.toNat < bl.nxt.toNat → q ∉ bl.free →
              ∀ hq : q.toNat < σ.length, σ1[q.toNat]'(hσ1 ▸ hq) = σ[q.toNat]'hq) ∧
            ((0 < bl.st.remUses.getD bl.st.nextVid.toNat 0 ∨
              0 < esc.getD bl.st.nextVid.toNat 0) →
              ∃ hsl : (arrGetU0 bl'.st.vslot bl.st.nextVid).toNat < σ1.length,
                σ1[(arrGetU0 bl'.st.vslot bl.st.nextVid).toNat]'hsl = toCanon64 t x ∧
                (arrGetU0 bl'.st.vslot bl.st.nextVid).toNat < bo.nxt.toNat ∧
                arrGetU0 bl'.st.vslot bl.st.nextVid ∉ bo.free) ∧
            tupAbiHolds0 s1 true (idx + 1).toNat rest restX ∧
            (s1.dmem =⋆ array64 (s1.regs.get64 .rsp) σ1 ⋆ G)) post := by
      dsimp only [bo, bindOneSlot0]
      by_cases hn : (decide (0 < arrGetU0 bl0.st.remUses bl0.st.nextVid) ||
          decide (0 < arrGetU0 esc bl0.st.nextVid)) = true
      · simp only [hn, ↓reduceIte]
        let sp := allocSlot0 bl0.free bl0.nxt bl0.st.maxSlots
        have hsp := allocSlot0_spec9 bl0.free bl0.nxt bl0.st.maxSlots maxBd hpool
          (by dsimp only [bl0]; omega)
        have hsp_lt_σ : sp.slot.toNat < σ.length := by
          have h2 : bo.st.maxSlots.toNat ≤ σ.length := Nat.le_trans hbo_ms_le hms
          have hbo_nxt_le : bo.nxt.toNat ≤ bo.st.maxSlots.toNat := h1_pool.2.2.1
          have hbo_n : bo.nxt = sp.nxt := by dsimp only [bo, bindOneSlot0]; simp [hn, sp]
          have hsp_lt : sp.slot.toNat < bo.nxt.toNat := by rw [hbo_n]; exact hsp.2.1
          omega
        have hst_spec := emitSlotMem0_st_spec (symName := symName) (h := h) (k := k)
          (post := post) (abiRegAt0 true idx) (abiRegAt0_ne_r10 true idx) sp.slot hsp_lt_σ hmem
        refine Machine.FallsTo.conseq hst_spec fun s1 hd1 hfr1 => ?_
        have hfr1_rsp : s1.regs.get64 .rsp = s.regs.get64 .rsp := hfr1.1 .rsp (by simp)
        have hreg_val : s.regs.get64 (abiRegAt0 true idx) = toCanon64 t x := by
          simpa [UInt32.ofNat_toNat] using htup.1
        let σ1 := σ.set sp.slot.toNat (toCanon64 t x)
        have hσ1_len : σ1.length = σ.length := List.length_set
        have hbo_vslot : arrGetU0 bo.st.vslot bl.st.nextVid = sp.slot := by
          apply u32_ext7
          dsimp only [bo, bindOneSlot0]
          simp only [hn, ↓reduceIte]
          dsimp only [arrGetU0, bl0]
          rw [u32_toNat_ofNat7, arrPush_getD7, hvsz]
          simp only [Nat.lt_irrefl, ↓reduceIte]
          exact Nat.mod_eq_of_lt (UInt32.toNat_lt sp.slot)
        have hslot_eq : arrGetU0 bl'.st.vslot bl.st.nextVid = sp.slot := by
          have hv_pres := h1_slot_spec.2.2.2.2.2.2.2.2.1 bl.st.nextVid.toNat (by omega)
          simp only [UInt32.ofNat_toNat] at hv_pres
          have hve : bl'.st.vslot = bl'1.st.vslot := by rw [hbl'_st_eq]
          rw [hve, hv_pres, hbo_vslot]
        have hup_tup : tupAbiHolds0 s1 true (idx + 1).toNat rest restX := by
          rw [hidx1]
          refine tupAbiHolds0_frame (fun r hr => hfr1.1 r hr) (fun j hj => ?_) htup.2
          simp only [List.mem_singleton]
          exact abiRegAt0_ne_r10 true _
        refine ⟨σ1, hσ1_len, fun q hq1 hq2 hqσ => ?_, fun _ => ?_, hup_tup, ?_⟩
        · have hne : q.toNat ≠ sp.slot.toNat := fun heq => by
            have hqe : q = sp.slot := u32_ext7 heq
            rcases hsp.2.2.2.2.1 with hm | hnxt_eq
            · exact hq2 (hqe ▸ hm)
            · dsimp only [bl0] at hnxt_eq; rw [hqe, hnxt_eq] at hq1; omega
          dsimp only [σ1]; rw [List.getElem_set_ne (Ne.symm hne)]
        · refine ⟨by rw [hslot_eq, hσ1_len]; exact hsp_lt_σ, ?_, ?_, ?_⟩
          · simp only [σ1, hslot_eq, List.getElem_set_self]
          · rw [hslot_eq]; exact hsp.2.1
          · rw [hslot_eq]; exact fun hm => ((hsp.2.2.2.2.2 sp.slot).mp hm).2 rfl
        · rw [hfr1_rsp]; dsimp only [σ1]; rw [← hreg_val]; exact hd1
      · simp only [hn, Bool.false_eq_true, ↓reduceIte]
        have hnot : ¬ (0 < bl.st.remUses.getD bl.st.nextVid.toNat 0 ∨
            0 < esc.getD bl.st.nextVid.toNat 0) := fun h => hn (hneed_iff.mpr h)
        dsimp only [emitFwd0, List.reverse_nil, toAmd64Program, List.flatMap_nil]
        refine Machine.FallsTo.nil ⟨σ, rfl, fun _ _ _ _ => rfl,
          fun h => absurd h hnot, hidx1 ▸ htup.2, hmem⟩
    have hcomp_rev :
        emitFwd0 bl'.st.revDirs = emitFwd0 bo.st.revDirs ++ emitFwd0 bl'1.st.revDirs := by
      rw [hrev_split, emitFwd0_append]
    rw [hcomp_rev, toAmd64Program_append]
    refine Machine.FallsTo.weaken (Machine.FallsTo.comp hbo_exec fun s1 hq _ => by
      rcases hq with ⟨σ1, hσ1_len, hq1, hhead1, htup1, hmem1⟩
      have hih1 := ih (k + (toAmd64Program symName (emitFwd0 bo.st.revDirs)).length)
        (rem - 1) (idx + 1) bl1 restX σ1 s1 maxBd hsub
        (by rw [hidx1]; simp only [List.length_cons] at hidx; omega) htup1 h1_sz
        (by dsimp only [bl1]; rw [h1_nv]; omega) h1_pool (by dsimp only [bl1]; omega)
        (by change bl'1.st.maxSlots.toNat ≤ σ1.length
            have hms1 : bl'1.st.maxSlots.toNat = bl'.st.maxSlots.toNat := by rw [hbl'_st_eq]
            omega)
        (fun j hj => by
          dsimp only [bl1]; rw [h1_nv, h1_rem, Nat.add_assoc, Nat.add_comm 1 j]
          exact hbd (j + 1) (by simp only [List.length_cons]; omega))
        hmem1
      dsimp only [bl1] at hih1
      refine Machine.FallsTo.conseq hih1 fun s2 ⟨σ2, hσ2_len, hq2, htail2, hmem2⟩ _ => ?_
      refine ⟨σ2, hσ2_len.trans hσ1_len, fun q hql hqf hqσ => ?_, ?_, hmem2⟩
      · have hqσ1 : q.toNat < σ1.length := hσ1_len ▸ hqσ
        have hq_nxt1 : q.toNat < bo.nxt.toNat := Nat.lt_of_lt_of_le hql h1_nxt_le.1
        have hq_nf1 : q ∉ bo.free := fun hm => hqf (h1_fr q hm)
        exact (hq2 q hq_nxt1 hq_nf1 hqσ1).trans (hq1 q hql hqf hqσ)
      · dsimp only [PushAgree0]
        refine ⟨fun hneed => ?_, ?_⟩
        · have hneed0 : 0 < bl.st.remUses.getD bl.st.nextVid.toNat 0 ∨
              0 < esc.getD bl.st.nextVid.toNat 0 := by
            rw [hbo_spec.2.2.2.1] at hneed; exact hneed
          obtain ⟨hsl1, heq1, hsl_lt_bonxt, hnf_bo⟩ := hhead1 hneed0
          have hq_step := hq2 (arrGetU0 bl'.st.vslot bl.st.nextVid) hsl_lt_bonxt hnf_bo hsl1
          refine ⟨hσ2_len ▸ hsl1, ?_⟩
          exact hq_step.trans heq1
        · have hrem_eq' : bl'.st.remUses = bl'1.st.remUses := by rw [hbl'_st_eq]
          have hvsl_eq' : bl'.st.vslot = bl'1.st.vslot := by rw [hbl'_st_eq]
          rw [hrem_eq', hvsl_eq', ← h1_nv_eq]
          exact htail2)
      (fun r hr => by
        simp only [List.mem_append, List.mem_singleton] at hr ⊢
        rcases hr with rfl | rfl <;> rfl)
      (fun _ hv => nomatch hv) (by decide)

private theorem bindEntryArgs0_run_spec_aux {symName : Sym0 → Sym} {h : Host} {G : Mem 64 → Prop}
    {post : MachineState → Prop} :
    ∀ (ts : List Ty0) (k : Nat) (i : UInt32) (venv : List UInt32) (st : RegaSt0)
      (xs : Tup Val (ty0ListToTy ts)) (σ : List (BitVec 64)) (s : MachineData),
      let bl0 := bindEntryArgs0 ts i venv { st with revDirs := [] }
      i.toNat + ts.length ≤ 6 → (hi_σ : i.toNat + ts.length ≤ σ.length) →
      tupAbiHolds0 s false i.toNat ts xs →
      (s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆ G) →
      x64ScalarMach.FallsTo x64CondReads h k
        (toAmd64Program symName (emitFwd0 bl0.st.revDirs)) x64ScratchAndAbi [] maskNone s
        (fun s' => ∃ (σ' : List (BitVec 64)) (hσ' : σ'.length = σ.length),
          (∀ q : Nat, ∀ hq : q < i.toNat,
            σ'[q]'(hσ' ▸ by omega) = σ[q]'(by omega)) ∧
          (∀ (j : Nat) (hj : j < ts.length),
            σ'[i.toNat + j]'(hσ' ▸ by omega) =
              (tupToCanon64s ts xs)[j]'(by rw [tupToCanon64s_length]; exact hj)) ∧
          (s'.dmem =⋆ array64 (s'.regs.get64 .rsp) σ' ⋆ G)) post := by
  intro ts
  induction ts with
  | nil =>
    intro k i venv st xs σ s bl0 _ hi_σ _ hmem
    cases xs
    dsimp only [bl0, bindEntryArgs0, emitFwd0, List.reverse_nil, toAmd64Program, List.flatMap_nil]
    refine Machine.FallsTo.nil ⟨σ, rfl, fun _ _ => rfl, fun _ hj => absurd hj (Nat.not_lt_zero _),
      hmem⟩
  | cons t rest ih =>
    intro k i venv st xs σ s bl0 hi_cap hi_σ htup hmem
    change Val (ty0ToTy t) × Tup Val (ty0ListToTy rest) at xs
    rcases xs with ⟨x, restX⟩
    dsimp only [tupAbiHolds0] at htup
    have hi_lt6 : i.toNat < 6 := by simp only [List.length_cons] at hi_cap; omega
    have hi_ltσ : i.toNat < σ.length := by simp only [List.length_cons] at hi_σ; omega
    have hi1 : (i + 1).toNat = i.toNat + 1 := u32_add1_toNat7 (by omega)
    let st10 := bindOneEntryArg0 i t { st with revDirs := [] }
    have hacc := bindEntryArgs0_acc rest (i + 1) (st.nextVid :: venv) st10
    dsimp only at hacc
    have hst10_rev :
        st10.revDirs =
          emitSlotMem0 false (abiRegAt0 false i) i [] ++
            emitCanon0 (tyWidth0 t) (abiRegAt0 false i) [] := by
      dsimp only [st10, bindOneEntryArg0]
      exact (emitSlotMem0_acc false (abiRegAt0 false i) i _).1
    have hbl_eq :
        bl0.st.revDirs =
          (bindEntryArgs0 rest (i + 1) (st.nextVid :: venv)
            { st10 with revDirs := [] }).st.revDirs ++ st10.revDirs := by
      dsimp only [bl0, bindEntryArgs0]; rw [hacc.2.2.2.2.1]
    have hprog_eq :
        toAmd64Program symName (emitFwd0 bl0.st.revDirs) =
          (toAmd64Program symName (emitFwd0 (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) [])) ++
            toAmd64Program symName (emitFwd0 (emitSlotMem0 false (abiRegAt0 false i) i []))) ++
          toAmd64Program symName (emitFwd0
            (bindEntryArgs0 rest (i + 1) (st.nextVid :: venv)
              { st10 with revDirs := [] }).st.revDirs) := by
      rw [hbl_eq, hst10_rev, emitFwd0_append, emitFwd0_append, toAmd64Program_append,
        toAmd64Program_append, List.append_assoc]
    have hreg0 : s.regs.get64 (abiRegAt0 false i) = toCanon64 t x := by
      simpa [UInt32.ofNat_toNat] using htup.1
    have hcan_spec :
        x64ScalarMach.FallsTo x64CondReads h k
          (toAmd64Program symName (emitFwd0 (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) [])))
          [abiRegAt0 false i] [] maskNone s
          (fun s1 => s1.regs.get64 (abiRegAt0 false i) = toCanon64 t x ∧ s1.dmem = s.dmem) post :=
      emitCanon0_ty_spec (symName := symName) (h := h) (k := k) t (abiRegAt0 false i)
        (by rw [hreg0]; exact toCanon64_toGprHolds t x)
    have hone :
        x64ScalarMach.FallsTo x64CondReads h k
          (toAmd64Program symName (emitFwd0 (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) [])) ++
            toAmd64Program symName (emitFwd0 (emitSlotMem0 false (abiRegAt0 false i) i [])))
          [abiRegAt0 false i, .r10] [] maskNone s
          (fun s2 =>
            tupAbiHolds0 s2 false (i + 1).toNat rest restX ∧
            (s2.dmem =⋆ array64 (s2.regs.get64 .rsp) (σ.set i.toNat (toCanon64 t x)) ⋆ G))
          post := by
      have hc12 :
          x64ScalarMach.FallsTo x64CondReads h k
            (toAmd64Program symName (emitFwd0 (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) [])) ++
              toAmd64Program symName (emitFwd0 (emitSlotMem0 false (abiRegAt0 false i) i [])))
            ([abiRegAt0 false i] ++ [.r10]) ([] ++ []) (maskNone ||| maskNone) s
            (fun s2 =>
              tupAbiHolds0 s2 false (i + 1).toNat rest restX ∧
              (s2.dmem =⋆ array64 (s2.regs.get64 .rsp) (σ.set i.toNat (toCanon64 t x)) ⋆ G))
            post :=
        Machine.FallsTo.comp hcan_spec fun s1 ⟨hr1, hm1⟩ hfr1 => by
          have hrsp1 : s1.regs.get64 .rsp = s.regs.get64 .rsp :=
            hfr1.1 .rsp fun hm => abiRegAt0_ne_rsp false i (List.mem_singleton.mp hm).symm
          have hmem1 : s1.dmem =⋆ array64 (s1.regs.get64 .rsp) σ ⋆ G := by
            rw [hm1, hrsp1]; exact hmem
          have htup1 : tupAbiHolds0 s1 false (i + 1).toNat rest restX := by
            rw [hi1]
            refine tupAbiHolds0_frame (fun r hr => hfr1.1 r hr) (fun j hj hm => ?_) htup.2
            have hj_eq := List.mem_singleton.mp hm
            have hj_lt : i.toNat + 1 + j < 6 := by simp only [List.length_cons] at hi_cap; omega
            have hne := abiRegAt0_inj_lt false hi_lt6 hj_lt
              (by simpa [UInt32.ofNat_toNat] using hj_eq.symm)
            omega
          have hst1 := emitSlotMem0_st_spec (symName := symName) (h := h)
            (k := k + (toAmd64Program symName (emitFwd0
              (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) []))).length)
            (post := post) (abiRegAt0 false i) (abiRegAt0_ne_r10 false i) i hi_ltσ hmem1
          refine Machine.FallsTo.conseq hst1 fun s2 hm2 hfr2 => ?_
          have hrsp2 : s2.regs.get64 .rsp = s1.regs.get64 .rsp := hfr2.1 .rsp (by simp)
          refine ⟨tupAbiHolds0_frame (fun r hr => hfr2.1 r hr)
              (fun j _ hm => abiRegAt0_ne_r10 false _ (List.mem_singleton.mp hm)) htup1, ?_⟩
          rw [← hrsp2, hr1] at hm2
          exact hm2
      exact Machine.FallsTo.weaken hc12
        (fun r hr => by simp at hr ⊢; exact hr) (fun _ hv => nomatch hv) (by decide)
    rw [hprog_eq]
    have hcomp := Machine.FallsTo.comp hone fun s2 ⟨htup2, hmem2⟩ _ =>
      ih (k + (toAmd64Program symName (emitFwd0 (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) [])) ++
        toAmd64Program symName (emitFwd0 (emitSlotMem0 false (abiRegAt0 false i) i []))).length)
        (i + 1) (st.nextVid :: venv) st10 restX (σ.set i.toNat (toCanon64 t x)) s2
        (by simp only [List.length_cons] at hi_cap; rw [hi1]; omega)
        (by simp only [List.length_cons, List.length_set] at hi_σ ⊢; rw [hi1]; omega)
        htup2 hmem2
    have hwk :
        x64ScalarMach.FallsTo x64CondReads h k
          ((toAmd64Program symName (emitFwd0 (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) [])) ++
              toAmd64Program symName (emitFwd0 (emitSlotMem0 false (abiRegAt0 false i) i []))) ++
            toAmd64Program symName (emitFwd0
              (bindEntryArgs0 rest (i + 1) (st.nextVid :: venv)
                { st10 with revDirs := [] }).st.revDirs))
          x64ScratchAndAbi [] maskNone s
          (fun s' =>
            ∃ (σ' : List (BitVec 64)) (hσ' : σ'.length = (σ.set i.toNat (toCanon64 t x)).length),
            (∀ q : Nat, ∀ hq : q < (i + 1).toNat,
              σ'[q]'(hσ' ▸ by simp only [List.length_set]; rw [hi1] at hq; omega) =
                (σ.set i.toNat (toCanon64 t x))[q]'(by
                  simp only [List.length_set]; rw [hi1] at hq; omega)) ∧
            (∀ (j : Nat) (hj : j < rest.length),
              σ'[(i + 1).toNat + j]'(hσ' ▸ by
                simp only [List.length_set]; simp only [List.length_cons] at hi_σ
                rw [hi1]; omega) =
                (tupToCanon64s rest restX)[j]'(by rw [tupToCanon64s_length]; exact hj)) ∧
            (s'.dmem =⋆ array64 (s'.regs.get64 .rsp) σ' ⋆ G)) post :=
      Machine.FallsTo.weaken hcomp (fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with (rfl | rfl) | hr2
        · exact abiRegAt0_mem_scratchAndAbi false i
        · simp [x64ScratchAndAbi]
        · exact hr2) (fun _ hv => nomatch hv) (by decide)
    refine Machine.FallsTo.conseq hwk fun s' ⟨σ', hσ'_len, hq_lt, hj_rest, hmem'⟩ _ => ?_
    refine ⟨σ', hσ'_len.trans List.length_set, fun q hq => ?_, fun j hj => ?_, hmem'⟩
    · have hne : q ≠ i.toNat := by omega
      exact (hq_lt q (by rw [hi1]; omega)).trans (by rw [List.getElem_set_ne (Ne.symm hne)])
    · cases j with
      | zero =>
        dsimp only [tupToCanon64s, List.getElem_cons_zero]
        simp only [Nat.add_zero]
        exact (hq_lt i.toNat (by rw [hi1]; omega)).trans (List.getElem_set_self ..)
      | succ k' =>
        have h' := hj_rest k' (Nat.lt_of_succ_lt_succ hj)
        have h2 : k' < (tupToCanon64s rest restX).length := by
          rw [tupToCanon64s_length]; exact Nat.lt_of_succ_lt_succ hj
        refine Eq.trans ?_ (tupToCanon64s_cons_getElem x restX k' _ h2).symm
        simpa only [hi1, Nat.add_assoc, Nat.add_comm 1 k'] using h'

theorem bindEntryArgs0_run_spec {symName : Sym0 → Sym} {h : Host} {G : Mem 64 → Prop}
    {post : MachineState → Prop} (ts : List Ty0) (k : Nat) (st : RegaSt0)
    (xs : Tup Val (ty0ListToTy ts)) (σ : List (BitVec 64)) (s : MachineData) (maxBd : Nat)
    (hcap : ts.length ≤ 6) (hvsz : st.vslot.size = st.nextVid.toNat) (hnv0 : st.nextVid = 0)
    (hmaxBd : ts.length ≤ maxBd) (hlt31 : maxBd < 2 ^ 31) (hms0 : st.maxSlots = 0)
    (hσ_len : ts.length ≤ σ.length)
    (hargs : x64ScalarTarget.ArgsIn xs s)
    (hmem : s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆ G) :
    let bl0 := bindEntryArgs0 ts 0 [] { st with revDirs := [] }
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 bl0.st.revDirs)) x64ScratchAndAbi [] maskNone s
      (fun s' => ∃ (σ' : List (BitVec 64)) (hσ' : σ'.length = σ.length),
        (∀ (j : Nat) (hj : j < ts.length),
          σ'[(arrGetU0 bl0.st.vslot (UInt32.ofNat j)).toNat]'(hσ' ▸ by
            have hsp := bindEntryArgs0_spec ts 0 [] { st with revDirs := [] } maxBd
              hvsz hnv0 (by simpa using hmaxBd) hlt31 (by rw [hms0])
            have hj0 := hsp.2.2.2.2.2.2.2.2 j hj
            simp only [UInt32.toNat_zero, Nat.zero_add] at hj0
            rw [hj0, u32_toNat_ofNat7, Nat.mod_eq_of_lt (by omega)]
            omega) =
          (tupToCanon64s ts xs)[j]'(by rw [tupToCanon64s_length]; exact hj)) ∧
        (s'.dmem =⋆ array64 (s'.regs.get64 .rsp) σ' ⋆ G)) post := by
  have htup := (argsIn_ty0_iff hcap xs s).mp hargs
  have hrun := bindEntryArgs0_run_spec_aux (symName := symName) (h := h) (G := G) (post := post)
    ts k 0 [] st xs σ s (by simpa using hcap) (by simpa using hσ_len) htup hmem
  have hsp := bindEntryArgs0_spec ts 0 [] { st with revDirs := [] } maxBd
    hvsz hnv0 (by simpa using hmaxBd) hlt31 (by rw [hms0])
  refine Machine.FallsTo.conseq hrun fun s' ⟨σ', hσ'_len, _, hj_val, hmem'⟩ _ => ?_
  refine ⟨σ', hσ'_len, fun j hj => ?_, hmem'⟩
  have hslot_j := hsp.2.2.2.2.2.2.2.2 j hj
  simp only [UInt32.toNat_zero, Nat.zero_add] at hslot_j
  have heq_toNat : (arrGetU0 (bindEntryArgs0 ts 0 [] { st with revDirs := [] }).st.vslot
      (UInt32.ofNat j)).toNat = j := by
    rw [hslot_j, u32_toNat_ofNat7, Nat.mod_eq_of_lt (by omega)]
  have hj' := hj_val j hj
  simp only [UInt32.toNat_zero, Nat.zero_add] at hj'
  simpa only [heq_toNat] using hj'

end LeanQbe.T.Bootstrap0
