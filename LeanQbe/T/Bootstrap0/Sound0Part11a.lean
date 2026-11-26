module

public import LeanQbe.T.Bootstrap0.Sound0Part10
import LeanQbe.T.FlatLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.TargetLemmas
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Amd64.FrameLemmas
import LeanQbe.T.Amd64.IselLemmas1
import LeanQbe.T.Amd64.IselLemmas2
import LeanQbe.T.Amd64.IselLemmas3
import LeanQbe.T.Amd64.IselLemmas4

/-!
# Bootstrap Stage B (`Sound0Part11a`): Straight-Line `Rega0` Runners

Proves machine-level `x64ScalarMach.Run` preservation for straight-line instructions in `Rega0`:
1. Leading-label, `defScope` prefix-preservation, and call stack-region reconstruction helpers.
2. Straight-line runners (`let1_run_ok`, `umulw_run_ok`, `load_run_ok`, `store_run_ok`,
   `call_run_ok`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T
open LeanQbe.T.Amd64
open Std Std.ExtHashMap

/-! ## 1. Leading-Label, `defScope` Prefix-Preservation, & Frame-Reconstruction Helpers -/

theorem nodeCount0_head_lt_2p31 {ctx : LegalCtx0} {fnIdx : UInt32} {fnMaxJump : Nat}
    {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0} {preWork : List PreItem0}
    {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0} {cur : RegaTask0} {rest : List RegaTask0}
    {metas : List TaskMeta0}
    (h : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt preWork seenJnz st ctrl
      (cur :: rest) metas) :
    nodeCount0 cur.node < 2 ^ 31 := by
  have hnl := h.ctrl_nl.2
  rw [List.map_cons] at hnl; dsimp only [workNodeCount0] at hnl
  omega

private theorem regaStep0_revDirs_suffix (esc : Array Nat) (cur : RegaTask0) (st : RegaSt0)
    (ctrl : CtrlSt0) (rest : List RegaTask0) :
    ∃ pfx, (regaStep0 esc cur st ctrl rest).st.revDirs = pfx ++ st.revDirs := by
  have hbb : ∀ (pts : List Ty0) (venv : List UInt32) (s0 : RegaSt0) (f : List UInt32)
      (n : UInt32), (bindBlockParams0 pts venv s0 f n).st.revDirs = s0.revDirs := by
    intro pts
    induction pts with
    | nil => intro _ _ _ _; rfl
    | cons _ _ ih =>
      intro _ _ _ _; dsimp only [bindBlockParams0, bindOneBlockSlot0]; exact ih _ _ _ _
  have hgp : ∀ (bs : List (List Ty0 × TFlat0)) (venv : List UInt32) (gp : GroupPrepOut0),
      (regaPrepGroup0 bs venv gp).st.revDirs = gp.st.revDirs := by
    intro bs
    induction bs with
    | nil => intro _ _; rfl
    | cons p restB ih =>
      intro venv gp; rcases p with ⟨pts, b⟩
      dsimp only [regaPrepGroup0, prepOneBlock0, prepOneBind0, prepFinishBlock0]
      rw [ih]; exact hbb pts venv gp.st gp.free gp.nxt
  have hlin_sfx : ∀ (hlin : isTerm0 cur.node = false)
      (hnj : ∀ c t e, cur.node ≠ .jnz c t e) (hng : ∀ bs k, cur.node ≠ .group bs k),
      ∃ pfx, (stepLinear0 esc cur st ctrl rest).st.revDirs = pfx ++ st.revDirs := by
    intro hlin hnj hng
    dsimp only [stepLinear0, stepLinBindPush0, linBindPush0, relAndUpdateSt0]
    let rr := relNodeArgs0 esc st.vslot cur.venv cur.node (RelRes0.mk st.remUses cur.freeSlots)
    let bl0 := BindListOut0.mk cur.venv
      (RegaSt0.mk st.nextVid st.maxSlots st.vslot rr.remUses (emitLinNode0 cur st))
      rr.free cur.nextSlot
    have hbr := bindRetsN0_revDirs esc (linCnt0 cur.node).toNat (linCnt0 cur.node) 0 bl0 rfl
    have hd := (emitLinNode0_acc cur st).1
    have hgoal : (bindRetsN0 esc (linCnt0 cur.node) 0 bl0).st.revDirs =
        ((bindRetsN0 esc (linCnt0 cur.node) 0
          { bl0 with st := { bl0.st with revDirs := [] } }).st.revDirs ++
         emitLinNode0 cur { st with revDirs := [] }) ++ st.revDirs := by
      dsimp only [bl0] at hbr ⊢
      rw [hbr.2.2.2.1, hd, ← List.append_assoc]
    exact ⟨_, hgoal⟩
  cases hnd : cur.node with
  | jnz c t e =>
    dsimp only [regaStep0]; rw [hnd]
    dsimp only [stepJnzPush0, jnzBuildSt0, jnzWrapRes0]
    exact ⟨_, (jnzPrep0_revDirs esc c cur st ctrl).1⟩
  | group bodies k =>
    dsimp only [regaStep0]; rw [hnd]
    dsimp only [stepGroupFinish0, stepGroupPrep0]
    exact ⟨[], hgp bodies cur.venv _⟩
  | let1 _ _ _ | let2Umulw64 _ _ _ | load _ _ _ | store _ _ _ _ | call _ _ _ _ _ =>
    dsimp only [regaStep0]; rw [hnd]
    exact hlin_sfx (by simp [isTerm0, hnd]) (fun _ _ _ he => by rw [hnd] at he; cases he)
      (fun _ _ he => by rw [hnd] at he; cases he)
  | tailCall fnSym as args =>
    dsimp only [regaStep0, regaStepCtrl0]; rw [hnd]; dsimp only [stepTail0]
    rw [show ∀ xs : List Dir0, pushDImm0 1 .rsp 0 xs = .spAdd false 0 :: xs from fun _ => rfl]
    rw [(loadRegArgs0_acc _ as args 0 st.revDirs).1]
    simp only [← List.cons_append]; exact ⟨_, rfl⟩
  | exit fnSym as args =>
    dsimp only [regaStep0, regaStepCtrl0]; rw [hnd]; dsimp only [stepTail0]
    rw [show ∀ xs : List Dir0, pushDImm0 1 .rsp 0 xs = .spAdd false 0 :: xs from fun _ => rfl]
    rw [(loadRegArgs0_acc _ as args 0 st.revDirs).1]
    simp only [← List.cons_append]; exact ⟨_, rfl⟩
  | ret vs =>
    dsimp only [regaStep0, regaStepCtrl0]; rw [hnd]; dsimp only [stepRet0]
    rw [show ∀ xs : List Dir0, pushDImm0 1 .rsp 0 xs = .spAdd false 0 :: xs from fun _ => rfl]
    rw [(loadRegArgs0_acc _ [] vs 0 st.revDirs).1]
    simp only [← List.cons_append]; exact ⟨_, rfl⟩
  | jump j args =>
    dsimp only [regaStep0, regaStepCtrl0]; rw [hnd]; dsimp only
    exact ⟨_, congrArg RegaSt0.revDirs (emitJump0_revDirs j args cur st ctrl).1⟩
  | hlt =>
    dsimp only [regaStep0, regaStepCtrl0]; rw [hnd]; exact ⟨[], rfl⟩

theorem regaRunAux0_leading_label {symName : Sym0 → Sym} (fSz : UInt64) (esc : Array Nat)
    (st : RegaSt0) (ctrl : CtrlSt0) (cur : RegaTask0) (rest : List RegaTask0) (fuel : UInt32)
    (hf : 0 < fuel.toNat) (hlbl : cur.lblId ≠ 0) :
    (toAmd64Program symName (patchEpilogues0 fSz
      (emitFwd0 (regaRunAux0 fuel esc { st with revDirs := [] } ctrl
        (cur :: rest)).1.revDirs) []))[0]? =
      some (x64Frame.label (label0ToSym symName (.loc ctrl.fnIdx cur.lblId))) := by
  have hd := regaRunAux0_step_once (fuel := fuel) (esc := esc)
    (st := { st with revDirs := [] }) (ctrl := ctrl) (cur := cur) (rest := rest) hf
  dsimp only at hd
  let st0 := regaPrependLbl0 cur { st with revDirs := [] } ctrl
  let ls := regaStep0 esc cur st0 ctrl rest
  have hr := regaRunAux0_revDirs_append (fuel - 1) esc ls.st ls.ctrl ls.work
  obtain ⟨pfx, hpfx⟩ := regaStep0_revDirs_suffix esc cur st0 ctrl rest
  have hst0_dirs : st0.revDirs = [.label (.loc ctrl.fnIdx cur.lblId)] := by
    dsimp only [st0]; rw [regaPrependLbl0_dirs_eq]; simp [hlbl]
  rw [hd, hr]
  change (toAmd64Program symName (patchEpilogues0 fSz
    (emitFwd0 (_ ++ ls.st.revDirs)) []))[0]? = _
  rw [hpfx, hst0_dirs, ← List.append_assoc, emitFwd0_append, emitFwd0_append,
    patchEpilogues0_append, patchEpilogues0_append, toAmd64Program_append,
    toAmd64Program_append]
  have hlead : toAmd64Program symName
      (patchEpilogues0 fSz (emitFwd0 [.label (.loc ctrl.fnIdx cur.lblId)]) []) =
      [x64Frame.label (label0ToSym symName (.loc ctrl.fnIdx cur.lblId))] := by
    rw [emitFwd0, List.reverse_singleton, patchEpilogues0_eq]; rfl
  rw [hlead]; rfl

theorem preNoteNode0_defScope (scope : UInt32) (venv : List UInt32) (node : TFlat0)
    (st : PreSt0) :
    (preNoteNode0 scope venv node st).defScope = st.defScope ∧
    (preNoteNode0 scope venv node st).nextVid = st.nextVid := by
  have harg : ∀ (s0 : PreSt0) (a : Arg0),
      (preNoteArg0 scope venv s0 a).defScope = s0.defScope ∧
      (preNoteArg0 scope venv s0 a).nextVid = s0.nextVid := fun s0 a => by
    cases a <;> simp only [preNoteArg0] <;> (try split) <;> simp
  have hargs : ∀ (args : List Arg0) (s0 : PreSt0),
      (preNoteArgs0 scope venv s0 args).defScope = s0.defScope ∧
      (preNoteArgs0 scope venv s0 args).nextVid = s0.nextVid := by
    intro args; induction args with
    | nil => intro _; exact ⟨rfl, rfl⟩
    | cons a rs ih =>
      intro s0; dsimp only [preNoteArgs0]
      exact ⟨(ih _).1.trans (harg s0 a).1, (ih _).2.trans (harg s0 a).2⟩
  cases node with
  | let1 _ args _ | call _ _ _ args _ | tailCall _ _ args | jump _ args | ret args
  | exit _ _ args => exact hargs args st
  | let2Umulw64 a b _ | store _ a b _ =>
    dsimp only [preNoteNode0]
    exact ⟨(harg _ b).1.trans (harg st a).1, (harg _ b).2.trans (harg st a).2⟩
  | load _ a _ | jnz a _ _ => exact harg st a
  | hlt | group _ _ => exact ⟨rfl, rfl⟩

private theorem preBindLoop0_nextVid_eq :
    ∀ (m : Nat) (n scope : UInt32) (venv : List UInt32) (st : PreSt0),
      n.toNat = m → st.nextVid.toNat + m < 2 ^ 32 →
      (preBindLoop0 n scope venv st).2.nextVid.toNat = st.nextVid.toNat + m
  | 0, n, _, _, st, hm, _ => by
    have hn0 : n = 0 := u32_ext7 hm
    subst hn0; rw [preBindLoop0.eq_def]; simp
  | k + 1, n, scope, venv, st, hm, hbd => by
    have hn_ne : n ≠ 0 := fun hz => by subst hz; simp at hm
    have hk : (n - 1).toNat = k := by rw [u32_sub1_toNat7 (by omega), hm]; omega
    have hnv : (st.nextVid + 1).toNat = st.nextVid.toNat + 1 := u32_add1_toNat7 (by omega)
    have hdef := preBindLoop0.eq_def n scope venv st
    simp only [hn_ne, ↓reduceDIte] at hdef
    rw [hdef]
    let st' : PreSt0 :=
      { nextVid := st.nextVid + 1
        defScope := st.defScope.push scope.toNat
        uses := st.uses.push 0
        escaped := st.escaped.push 0 }
    have hih := preBindLoop0_nextVid_eq k (n - 1) scope (st.nextVid :: venv) st' hk
      (by dsimp only [st']; rw [hnv]; omega)
    dsimp only [st'] at hih
    omega

private theorem preBindLoop0_defScope_pres :
    ∀ (m : Nat) (n scope : UInt32) (venv : List UInt32) (st : PreSt0),
      n.toNat = m → st.nextVid.toNat + m < 2 ^ 32 → st.defScope.size = st.nextVid.toNat →
      ∀ v < st.nextVid.toNat,
        (preBindLoop0 n scope venv st).2.defScope.getD v 0 = st.defScope.getD v 0
  | 0, n, _, _, st, hm, _, _, v, _ => by
    have hn0 : n = 0 := u32_ext7 hm
    subst hn0; rw [preBindLoop0.eq_def]; simp
  | k + 1, n, scope, venv, st, hm, hbd, hsz, v, hv => by
    have hn_ne : n ≠ 0 := fun hz => by subst hz; simp at hm
    have hk : (n - 1).toNat = k := by rw [u32_sub1_toNat7 (by omega), hm]; omega
    have hnv : (st.nextVid + 1).toNat = st.nextVid.toNat + 1 := u32_add1_toNat7 (by omega)
    have hdef := preBindLoop0.eq_def n scope venv st
    simp only [hn_ne, ↓reduceDIte] at hdef
    rw [hdef]
    let st' : PreSt0 :=
      { nextVid := st.nextVid + 1
        defScope := st.defScope.push scope.toNat
        uses := st.uses.push 0
        escaped := st.escaped.push 0 }
    have hih := preBindLoop0_defScope_pres k (n - 1) scope (st.nextVid :: venv) st' hk
      (by dsimp only [st']; rw [hnv]; omega)
      (by dsimp only [st']; rw [Array.size_push, hsz, hnv])
      v (by dsimp only [st']; rw [hnv]; omega)
    dsimp only [st'] at hih
    rw [hih, arrPush_getD7, hsz]
    simp [hv]

theorem regaRunAux0_step_prefix_defScope :
    ∀ (N : Nat) (fuel : UInt32) (ctx : LegalCtx0) (fnIdx : UInt32) (fnMaxJump : Nat)
      (preRes : PreSt0) (nextSc : UInt32) (preSt : PreSt0) (pw₁ pw₂ : List PreItem0)
      (seenJnz : Bool) (st : RegaSt0) (ctrl : CtrlSt0) (w₁ w₂ : List RegaTask0)
      (m₁ m₂ : List TaskMeta0),
      workNodeCount0 (w₁.map RegaTask0.node) = N → N ≤ fuel.toNat →
      pw₁.length = w₁.length → m₁.length = w₁.length →
      RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (pw₁ ++ pw₂) seenJnz st ctrl
        (w₁ ++ w₂) (m₁ ++ m₂) →
      let r1 := regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] } ctrl w₁
      ∃ seenJnz' nextSc' preSt',
        RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc' preSt' pw₂ seenJnz'
          { r1.1 with revDirs := r1.1.revDirs ++ st.revDirs } r1.2 w₂ m₂ ∧
        preSt.nextVid.toNat ≤ preSt'.nextVid.toNat ∧
        (∀ v < preSt.nextVid.toNat, preSt'.defScope.getD v 0 = preSt.defScope.getD v 0) := by
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
      rw [List.nil_append, List.nil_append, List.nil_append] at hinv
      have h0 : workNodeCount0 (([] : List RegaTask0).map RegaTask0.node) = 0 := rfl
      rw [h0]
      rw [show regaRunAux0 (UInt32.ofNat 0) preRes.escaped { st with revDirs := [] } ctrl [] =
          ({ st with revDirs := [] }, ctrl) from regaRunAux0_nil_eq ..]
      dsimp only
      have hst_id : ({ st with revDirs := [] ++ st.revDirs } : RegaSt0) = st := by cases st; rfl
      rw [hst_id]
      exact ⟨seenJnz, nextSc, preSt, hinv, Nat.le_refl _, fun _ _ => rfl⟩
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
          have hN_ne : UInt32.ofNat N ≠ 0 := fun h => by
            have := congrArg UInt32.toNat h
            rw [u32_ofNat_toNat_lt10 hN_lt32, UInt32.toNat_zero] at this
            omega
          have hN1 : (UInt32.ofNat N - 1).toNat = N - 1 := by
            rw [u32_sub1_toNat7 (by rw [u32_ofNat_toNat_lt10 hN_lt32]; exact hpos),
              u32_ofNat_toNat_lt10 hN_lt32]
          have hfl1 : (fuel - 1).toNat = fuel.toNat - 1 := u32_sub1_toNat7 (by omega)
          let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
          let lsClean := regaStep0 preRes.escaped cur st0Clean ctrl rest₁
          let preSt1 := preNoteNode0 curPre.scope curPre.venv curPre.node preSt
          let out := preStepPush0 curPre preSt1 nextSc (restPre₁ ++ pw₂)
          have hcl := regaStep0_clean_append preRes.escaped cur st ctrl rest₁ w₂
          dsimp only at hcl
          have hcnt_clean : workNodeCount0 (lsClean.work.map RegaTask0.node) + 1 = N := by
            rw [← hN]
            simpa only [lsClean, List.map_cons] using
              regaWorkNodeCount0_children preRes.escaped cur st0Clean ctrl rest₁
          have hlt_clean : workNodeCount0 (lsClean.work.map RegaTask0.node) < N := by omega
          have hcnt_sub : UInt32.ofNat N - 1 =
              UInt32.ofNat (workNodeCount0 (lsClean.work.map RegaTask0.node)) := by
            apply u32_ext7; rw [hN1, u32_ofNat_toNat_lt10 (by omega)]; omega
          obtain ⟨seenJnz1, pw₁', m₁', hlen_pw', hlen_mw', hout_eq, hinv1⟩ :=
            regaStep0_prefix_split hinv (by simp at hlen_pw; exact hlen_pw)
              (by simp at hlen_mw; exact hlen_mw)
          rw [hcl.1, hcl.2.1, hout_eq] at hinv1
          have hcur_ok := hinv.items_ok 0 (by simp) (by simp) (by simp)
          simp only [List.cons_append, List.getElem_cons_zero] at hcur_ok
          obtain ⟨hpn, _, _, _, _, _, _, hwf, hfit, hsbg, hnb, _⟩ := hcur_ok
          have hpre_nv_bd : preSt.nextVid.toNat + binderCount0 cur.node < 2 ^ 31 := by
            have hb := hinv.pre_inv.nextVid_bound
            rw [List.cons_append, List.map_cons] at hb
            dsimp only [workBinderCount0] at hb
            rw [hpn] at hb
            omega
          have hst1_ds : preSt1.defScope = preSt.defScope := (preNoteNode0_defScope ..).1
          have hst1_nv : preSt1.nextVid = preSt.nextVid := (preNoteNode0_defScope ..).2
          have hst1_sz : preSt1.defScope.size = preSt1.nextVid.toNat := by
            rw [hst1_ds, hst1_nv]; exact hinv.pre_inv.defScope_sz
          have hstep_pres : preSt.nextVid.toNat ≤ out.st.nextVid.toNat ∧
              ∀ v < preSt.nextVid.toNat, out.st.defScope.getD v 0 = preSt.defScope.getD v 0 := by
            dsimp only [out, preStepPush0]
            cases hnd : curPre.node with
            | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt =>
              simp only [isTerm0, ↓reduceIte]; rw [hst1_nv, hst1_ds]
              exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
            | jnz _ _ _ =>
              simp only [isTerm0, Bool.false_eq_true, ↓reduceIte, preStepJnz0]
              rw [hst1_nv, hst1_ds]; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
            | group bodies k =>
              simp only [isTerm0, Bool.false_eq_true, ↓reduceIte]
              dsimp only [preStepGroup0, preEnqueueGroup0]
              have hsbg_p : (TFlat0.group bodies k).singleBlockGroups = true := hnd ▸ hpn ▸ hsbg
              have hfit_p : (TFlat0.group bodies k).sigLensFitU32 = true := hnd ▸ hpn ▸ hfit
              have hnb_p : (TFlat0.group bodies k).noNegBool = true := hnd ▸ hpn ▸ hnb
              have hwf_p : WfNode0 ctx mCur.vT mCur.lT (.group bodies k) := hnd ▸ hpn ▸ hwf
              obtain ⟨_, _, _, _, hcases⟩ :=
                wfNode0_group_single_inv hwf_p hfit_p hsbg_p hnb_p
              rcases hcases with rfl | ⟨pts, b, rfl, hpts_lt, _⟩
              · dsimp only [prePushGroup0]; rw [hst1_nv, hst1_ds]
                exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
              · dsimp only [prePushGroup0, prePushOne0]
                have hlen_pts : (tyLenU0 pts 0).toNat = pts.length := tyLenU0_eq_of_lt hpts_lt
                have hpts_bd : pts.length ≤ binderCount0 cur.node := by
                  rw [← hpn, hnd]; dsimp only [binderCount0, blocksBinderCount0]; omega
                refine ⟨?_, fun v hv => ?_⟩
                · rw [preBindLoop0_nextVid_eq pts.length (tyLenU0 pts 0) nextSc curPre.venv
                      preSt1 hlen_pts (by rw [hst1_nv]; omega), hst1_nv]
                  omega
                · rw [preBindLoop0_defScope_pres pts.length (tyLenU0 pts 0) nextSc curPre.venv
                    preSt1 hlen_pts (by rw [hst1_nv]; omega) hst1_sz v (hst1_nv ▸ hv), hst1_ds]
            | let1 _ _ _ | let2Umulw64 _ _ _ | load _ _ _ | store _ _ _ _ | call _ _ _ _ _ =>
              have hlin_p : isTerm0 curPre.node = false := by simp [isTerm0, hnd]
              have hnj_p : ∀ c t e, curPre.node ≠ .jnz c t e := fun _ _ _ he => by
                rw [hnd] at he; cases he
              have hng_p : ∀ bs k, curPre.node ≠ .group bs k := fun _ _ he => by
                rw [hnd] at he; cases he
              simp only [isTerm0, Bool.false_eq_true, ↓reduceIte, preStepLin0, preLinFinish0, hnd]
              have hcnt_bd := hinv.items_ok 0 (by simp) (by simp) (by simp)
              have hcnt_le : (linCnt0 cur.node).toNat ≤ binderCount0 cur.node := by
                cases hcnd : cur.node with
                | let1 _ _ _ | load _ _ _ =>
                  dsimp only [linCnt0, binderCount0]; simp only [UInt32.toNat_one]; omega
                | let2Umulw64 _ _ _ =>
                  dsimp only [linCnt0, binderCount0]
                  rw [show (2 : UInt32).toNat = 2 from rfl]; omega
                | store _ _ _ _ =>
                  dsimp only [linCnt0, binderCount0]; rw [UInt32.toNat_zero]; exact Nat.zero_le _
                | call _ _ bs _ _ =>
                  have hbs7 : bs.length ≤ 7 := by rw [hcnd] at hwf; cases hwf; assumption
                  dsimp only [linCnt0, binderCount0]
                  rw [tyLenU0_eq_of_lt (by omega : bs.length < 2 ^ 32)]
                  omega
                | jnz _ _ _ | group _ _ => rw [← hpn, hnd] at hcnd; cases hcnd
                | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt =>
                  rw [← hpn, hnd] at hcnd; cases hcnd
              have hbd1 : preSt1.nextVid.toNat + (linCnt0 curPre.node).toNat < 2 ^ 32 := by
                rw [hst1_nv, hpn]; omega
              have h1 := preBindLoop0_nextVid_eq (linCnt0 curPre.node).toNat (linCnt0 curPre.node)
                curPre.scope curPre.venv preSt1 rfl (by rw [hst1_nv, hpn]; omega)
              have h2 := preBindLoop0_defScope_pres (linCnt0 curPre.node).toNat
                (linCnt0 curPre.node) curPre.scope curPre.venv preSt1 rfl
                (by rw [hst1_nv, hpn]; omega) hst1_sz
              rw [hnd] at h1 h2
              refine ⟨by rw [h1, hst1_nv]; omega, fun v hv => ?_⟩
              rw [h2 v (hst1_nv ▸ hv), hst1_ds]
          have hih := ih (workNodeCount0 (lsClean.work.map RegaTask0.node)) hlt_clean (fuel - 1)
            ctx fnIdx fnMaxJump preRes out.nextScope out.st pw₁' pw₂ seenJnz1
            (regaStep0 preRes.escaped cur (regaPrependLbl0 cur st ctrl) ctrl (rest₁ ++ w₂)).st
            lsClean.ctrl lsClean.work w₂ m₁' m₂ rfl (by omega) hlen_pw' hlen_mw' hinv1
          obtain ⟨seenJnz', nextSc', preSt', hinv', hnv_ih, hds_ih⟩ := hih
          have hsplit_clean :
              regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] } ctrl
                (cur :: rest₁) =
              regaRunAux0 (UInt32.ofNat (workNodeCount0 (lsClean.work.map RegaTask0.node)))
                preRes.escaped lsClean.st lsClean.ctrl lsClean.work := by
            rw [regaRunAux0_succ hN_ne, hcnt_sub]
          let r1' := regaRunAux0 (UInt32.ofNat (workNodeCount0 (lsClean.work.map RegaTask0.node)))
            preRes.escaped { lsClean.st with revDirs := [] } lsClean.ctrl lsClean.work
          have hrev_ls :
              regaRunAux0 (UInt32.ofNat (workNodeCount0 (lsClean.work.map RegaTask0.node)))
                preRes.escaped lsClean.st lsClean.ctrl lsClean.work =
              ({ r1'.1 with revDirs := r1'.1.revDirs ++ lsClean.st.revDirs }, r1'.2) :=
            regaRunAux0_revDirs_append _ _ _ _ _
          let rStep := regaRunAux0 (UInt32.ofNat (workNodeCount0 (lsClean.work.map RegaTask0.node)))
            preRes.escaped { (regaStep0 preRes.escaped cur (regaPrependLbl0 cur st ctrl) ctrl
              (rest₁ ++ w₂)).st with revDirs := [] } lsClean.ctrl lsClean.work
          have hr1_eq : { rStep.1 with revDirs := rStep.1.revDirs ++
              (regaStep0 preRes.escaped cur (regaPrependLbl0 cur st ctrl) ctrl
                (rest₁ ++ w₂)).st.revDirs } =
              { (regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] } ctrl
                (cur :: rest₁)).1 with
                revDirs := (regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] }
                  ctrl (cur :: rest₁)).1.revDirs ++ st.revDirs } ∧
              rStep.2 = (regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] } ctrl
                (cur :: rest₁)).2 := by
            have hclean_st : { (regaStep0 preRes.escaped cur (regaPrependLbl0 cur st ctrl) ctrl
                (rest₁ ++ w₂)).st with revDirs := [] } = { lsClean.st with revDirs := [] } := by
              rw [hcl.2.2]
            have hstep_rev :
                { (regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] }
                    ctrl (cur :: rest₁)).1 with
                  revDirs := (regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] }
                    ctrl (cur :: rest₁)).1.revDirs ++ st.revDirs } =
                { r1'.1 with revDirs := r1'.1.revDirs ++ lsClean.st.revDirs ++ st.revDirs } := by
              rw [hsplit_clean, hrev_ls]
            rw [hstep_rev]
            have hrStep_eq : rStep = r1' := by dsimp only [rStep, r1']; rw [hclean_st]
            rw [hrStep_eq, hcl.2.2]
            refine ⟨by dsimp only [lsClean, st0Clean]; simp [List.append_assoc],
              by rw [hsplit_clean, hrev_ls]⟩
          rw [hr1_eq.1, hr1_eq.2] at hinv'
          exact ⟨seenJnz', nextSc', preSt', hinv', Nat.le_trans hstep_pres.1 hnv_ih,
            fun v hv => (hds_ih v (Nat.lt_of_lt_of_le hv hstep_pres.1)).trans
              (hstep_pres.2 v hv)⟩

theorem regaRunAux0_step_prefix_ds {N : Nat} {fuel : UInt32} {ctx : LegalCtx0} {fnIdx : UInt32}
    {fnMaxJump : Nat} {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0}
    {pw₁ pw₂ : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {w₁ w₂ : List RegaTask0} {m₁ m₂ : List TaskMeta0}
    (hN : workNodeCount0 (w₁.map RegaTask0.node) = N) (hle : N ≤ fuel.toNat)
    (hlen_pw : pw₁.length = w₁.length) (hlen_mw : m₁.length = w₁.length)
    (hinv : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (pw₁ ++ pw₂) seenJnz st ctrl
      (w₁ ++ w₂) (m₁ ++ m₂)) :
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
      RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc' preSt' pw₂ seenJnz'
        { r1.1 with revDirs := r1.1.revDirs ++ st.revDirs } r1.2 w₂ m₂ ∧
      preSt.nextVid.toNat ≤ preSt'.nextVid.toNat ∧
      (∀ v < preSt.nextVid.toNat, preSt'.defScope.getD v 0 = preSt.defScope.getD v 0) := by
  have hp := regaRunAux0_step_prefix N fuel ctx fnIdx fnMaxJump preRes nextSc preSt pw₁ pw₂
    seenJnz st ctrl w₁ w₂ m₁ m₂ hN hle hlen_pw hlen_mw hinv
  have hds := regaRunAux0_step_prefix_defScope N fuel ctx fnIdx fnMaxJump preRes nextSc preSt pw₁
    pw₂ seenJnz st ctrl w₁ w₂ m₁ m₂ hN hle hlen_pw hlen_mw hinv
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hds⟩

theorem call_reconstruct_frame_region {sp0 : BitVec 64} {n bound xSz : Nat}
    (hle : xSz + 8 + bound ≤ n) (hn : n + 8 ≤ 2 ^ 64) :
    (region ((sp0 - BitVec.ofNat 64 xSz - 8#64) - BitVec.ofNat 64 bound) (bound + 8) ⋆
      region (sp0 - BitVec.ofNat 64 n) (n - xSz - 8 - bound)) =
      region (sp0 - BitVec.ofNat 64 n) (n - xSz) := by
  have hsp := region_split
    (a := (sp0 - BitVec.ofNat 64 xSz - 8#64) - BitVec.ofNat 64 bound)
    (n1 := bound) (n2 := 8) (by omega)
  rw [BitVec.sub_add_cancel] at hsp
  rw [hsp, call_split_frame_region hle hn]
  ac_rfl

private theorem regaPrependLbl0_vslot_eq (cur : RegaTask0) (st : RegaSt0) (ctrl : CtrlSt0) :
    (regaPrependLbl0 cur st ctrl).vslot = st.vslot := by
  dsimp only [regaPrependLbl0]; split <;> rfl

theorem bindBlockParams0_revDirs11 :
    ∀ (pts : List Ty0) (venv : List UInt32) (st : RegaSt0) (free : List UInt32) (nxt : UInt32),
      (bindBlockParams0 pts venv st free nxt).st.revDirs = st.revDirs
  | [], _, _, _, _ => rfl
  | _ :: rest, venv, st, free, nxt => by
    dsimp only [bindBlockParams0, bindOneBlockSlot0]
    exact bindBlockParams0_revDirs11 rest (st.nextVid :: venv) _ _ _

private theorem stepLinear_bind_ok_ret {h : Host} {symName : Sym0 → Sym} {Γ : Env}
    {ctx : LegalCtx0} {fnIdx : UInt32} {fnMaxJump : Nat} {preRes : PreSt0} {nextSc : UInt32}
    {preSt : PreSt0} {curPre : PreItem0} {pw₂ : List PreItem0} {seenJnz : Bool}
    {st : RegaSt0} {ctrl : CtrlSt0} {cur : RegaTask0} {w₂ : List RegaTask0}
    {mCur : TaskMeta0} {m₂ : List TaskMeta0} {vs : List ((t : Ty) × Val t)}
    {ls : List ((ts : List Ty) × Cont ts)} {rs : List Ty0} {Q : Post (ty0ListToTy rs)}
    {X : XPost} {s0 : MachineData} {ra0 : Int64} {n nX : Nat} {Rf : Mem 64 → Prop}
    {ns : UInt32} {k : Nat} {fuel : UInt32} {mNew : Mem 64} {s1 : MachineData}
    {σ : List (BitVec 64)} {retTys : List Ty0} {kNode : TFlat0}
    (hret : retTys = linRetTys0 cur.node) (hk : kNode = linK0 cur.node)
    (rvs : Tup Val (ty0ListToTy retTys))
    (hlin : isTerm0 cur.node = false) (hnj : ∀ c t e, cur.node ≠ .jnz c t e)
    (hng : ∀ bs k, cur.node ≠ .group bs k)
    (hfuel : workNodeCount0 ((cur :: w₂).map RegaTask0.node) ≤ fuel.toNat)
    (hns_eq : (regaRunAux0 fuel preRes.escaped st ctrl (cur :: w₂)).1.maxSlots = ns)
    (hinv : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: pw₂) seenJnz st ctrl
      (cur :: w₂) (mCur :: m₂))
    (hlen_pw : pw₂.length = w₂.length) (hlen_mw : m₂.length = w₂.length)
    (hk_inf :
      let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
      let lsC := stepLinear0 preRes.escaped cur st0Clean ctrl []
      let tK := lsC.work[0]'(by simp [lsC, stepLinear0, stepLinBindPush0, linBindPush0])
      let blZero := bindRetsN0 preRes.escaped (linCnt0 cur.node) 0
        (relAndUpdateSt0 preRes.escaped cur { st0Clean with revDirs := [] } [])
      (toAmd64Program symName (emitFwd0 blZero.st.revDirs) ++
        toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
          (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 (linK0 cur.node))) preRes.escaped
            { lsC.st with revDirs := [] } ctrl [tK]).1.revDirs) [])).IsInfixAt
        (x64ScalarMach.prog h) k)
    (hwp' : wp0 Γ symName rs (pushTup rvs vs) ls Q X kNode mNew)
    (hfr1 : FnFrameInv0 ns s0 ra0 n Rf mNew s1 σ)
    (htup1 : tupAbiHolds0 s1 true 0 retTys rvs)
    (hag1 : SlotsAgree0 preRes.escaped preSt st curPre cur mCur.vT vs σ)
    (hgl : GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
      preRes.escaped st cur mCur vs fnIdx mCur.gl ls)
    (hih : ∀ k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' m' fuel' s' σ',
      RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc' preSt' (curPre' :: pw') seenJnz' st' ctrl'
        (cur' :: w') (mCur' :: m') →
      pw'.length = w'.length → m'.length = w'.length →
      cur'.node = linK0 cur.node →
      nodeCount0 cur'.node = nodeCount0 (linK0 cur.node) →
      workNodeCount0 ((cur' :: w').map RegaTask0.node) ≤ fuel'.toNat →
      (regaRunAux0 fuel' preRes.escaped st' ctrl' (cur' :: w')).1.maxSlots = ns →
      (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
        (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 cur'.node)) preRes.escaped
          { st' with revDirs := [] } ctrl' [cur']).1.revDirs) [])).IsInfixAt
        (x64ScalarMach.prog h) k_nxt →
      wp0 Γ symName rs (pushTup (rvs |> fun x => hret ▸ x) vs) ls Q X cur'.node mNew →
      FnFrameInv0 ns s0 ra0 n Rf mNew s' σ' →
      SlotsAgree0 preRes.escaped preSt' st' curPre' cur' mCur'.vT
        (pushTup (rvs |> fun x => hret ▸ x) vs) σ' →
      GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
        preRes.escaped st' cur' mCur' (pushTup (rvs |> fun x => hret ▸ x) vs) fnIdx mCur'.gl ls →
      x64ScalarMach.Run h k_nxt s' (fnPost0 h rs Q X s0 ra0 n nX Rf)) :
    x64ScalarMach.Run h k s1 (fnPost0 h rs Q X s0 ra0 n nX Rf) := by
  subst hret; subst hk
  exact stepLinear_bind_ok hlin hnj hng hfuel hns_eq hinv hlen_pw hlen_mw hk_inf hwp' hfr1
    htup1 hag1 hgl hih

/-! ## 2. Straight-Line Node Runners (`let1`, `let2Umulw64`, `load`, `store`, `call`) -/

theorem let1_run_ok {h : Host} {symName : Sym0 → Sym} {Γ : Env} {ctx : LegalCtx0}
    {fnIdx : UInt32} {fnMaxJump : Nat} {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0}
    {curPre : PreItem0} {pw₂ : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {w₂ : List RegaTask0} {mCur : TaskMeta0} {m₂ : List TaskMeta0}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {rs : List Ty0} {Q : Post (ty0ListToTy rs)} {X : XPost}
    {s0 : MachineData} {ra0 : Int64} {n nX : Nat} {Rf : Mem 64 → Prop} {ns : UInt32}
    {op : OpCode0} {args : List Arg0} {cont : TFlat0} {k : Nat} {fuel : UInt32}
    {mCurMem : Mem 64} {s : MachineData} {σ : List (BitVec 64)}
    (hnd : cur.node = .let1 op args cont)
    (hfuel : workNodeCount0 ((cur :: w₂).map RegaTask0.node) ≤ fuel.toNat)
    (hns_eq : (regaRunAux0 fuel preRes.escaped st ctrl (cur :: w₂)).1.maxSlots = ns)
    (hinv : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: pw₂) seenJnz st ctrl
      (cur :: w₂) (mCur :: m₂))
    (hlen_pw : pw₂.length = w₂.length) (hlen_mw : m₂.length = w₂.length)
    (hcode : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
      (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 cur.node)) preRes.escaped
        { st with revDirs := [] } ctrl [cur]).1.revDirs) [])).IsInfixAt
      (x64ScalarMach.prog h) k)
    (hu : x64ScalarTarget.LabelsUnique h)
    (hwp : wp0 Γ symName rs vs ls Q X cur.node mCurMem)
    (hfr : FnFrameInv0 ns s0 ra0 n Rf mCurMem s σ)
    (hag : SlotsAgree0 preRes.escaped preSt st curPre cur mCur.vT vs σ)
    (hgl : GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
      preRes.escaped st cur mCur vs fnIdx mCur.gl ls)
    (hc_node : NodeContracts0 h symName Γ ctx ns n nX cur.node)
    (hih : ∀ k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' m' fuel' s' σ'
        vs' ls' mMem',
      RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc' preSt' (curPre' :: pw') seenJnz' st' ctrl'
        (cur' :: w') (mCur' :: m') →
      pw'.length = w'.length → m'.length = w'.length →
      nodeCount0 cur'.node < nodeCount0 cur.node →
      workNodeCount0 ((cur' :: w').map RegaTask0.node) ≤ fuel'.toNat →
      (regaRunAux0 fuel' preRes.escaped st' ctrl' (cur' :: w')).1.maxSlots = ns →
      (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
        (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 cur'.node)) preRes.escaped
          { st' with revDirs := [] } ctrl' [cur']).1.revDirs) [])).IsInfixAt
        (x64ScalarMach.prog h) k_nxt →
      wp0 Γ symName rs vs' ls' Q X cur'.node mMem' →
      FnFrameInv0 ns s0 ra0 n Rf mMem' s' σ' →
      SlotsAgree0 preRes.escaped preSt' st' curPre' cur' mCur'.vT vs' σ' →
      GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
        preRes.escaped st' cur' mCur' vs' fnIdx mCur'.gl ls' →
      NodeContracts0 h symName Γ ctx ns n nX cur'.node →
      x64ScalarMach.Run h k_nxt s' (fnPost0 h rs Q X s0 ra0 n nX Rf)) :
    x64ScalarMach.Run h k s (fnPost0 h rs Q X s0 ra0 n nX Rf) := by
  have hlin : isTerm0 cur.node = false := by rw [hnd]; rfl
  have hnj : ∀ c t e, cur.node ≠ .jnz c t e := fun _ _ _ he => by rw [hnd] at he; cases he
  have hng : ∀ bs k', cur.node ≠ .group bs k' := fun _ _ he => by rw [hnd] at he; cases he
  have hcur_ok := hinv.items_ok 0 (by simp) (by simp) (by simp)
  dsimp only [List.getElem_cons_zero] at hcur_ok
  obtain ⟨_, _, hvlen, _, _, _, _, hwf, _, _, hnb, _, _, _, _, _, _⟩ := hcur_ok
  have hop_chk : checkOp0 mCur.vT op args = true := by
    rw [hnd] at hwf; cases hwf; assumption
  have hne_neg : op ≠ .un .neg .bool := by
    rintro rfl; rw [hnd] at hnb; dsimp only [TFlat0.noNegBool] at hnb; cases hnb
  have hvalid := validOp0_of_checkOp0 hop_chk hne_neg
  have hcargs := checkOp0_checkArgs0 hop_chk
  have hc_specs := checkArgs0_spec hcargs
  have hargs_len : args.length = (op0ArgTys op).length := hc_specs.1.symm
  have hargs_ok : ∀ a ∈ args, ∀ idx, a = .var idx → idx.toNat < cur.venv.length := by
    have hva := wfNode0_nodeArgsInVenv0 hwf; rw [← hvlen, hnd] at hva; exact hva
  have hlive_args : ∀ a ∈ args, ∀ idx, a = .var idx →
      LiveInTask0 preRes.escaped preSt st curPre cur (listGetU32 cur.venv idx).toNat :=
    taskMetaOk0_args_live hinv (fun a ha idx heq => by
      rw [hnd]; exact nodeArgsUses0_pos_lin_term (heq ▸ ha)) hargs_ok
  rw [hnd, wp0_let1] at hwp
  cases hev : evalArgs0Ty vs (ty0ListToTy (op0ArgTys op)) args with
  | none => rw [hev] at hwp; exact False.elim hwp
  | some argv =>
    rw [hev] at hwp
    have hvals := argsSlotVal64_of_evalArgs0Ty hcargs hag hev hlive_args
    have hsplit := stepLinear_program_split preRes.escaped cur st ctrl ns hlin hnj hng
      (nodeCount0_head_lt_2p31 hinv) hcode
    dsimp only at hsplit
    refine regaPrependLbl0_run cur st ctrl (x64FrameSizeU0 ns) _ s
      (fnPost0 h rs Q X s0 ra0 n nX Rf) hu hsplit fun _ hprog => ?_
    let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
    have hvsl0 : ({ st0Clean with revDirs := [] } : RegaSt0).vslot = st.vslot :=
      regaPrependLbl0_vslot_eq cur { st with revDirs := [] } ctrl
    let pLoad := emitFwd0 (loadRegArgs0 (LoadCfg0.mk false false cur.venv st.vslot) [] args 0 [])
    let pOp := emitFwd0 (emitOp0 op [])
    have hemit_eq :
        toAmd64Program symName (emitFwd0 (emitLinNode0 cur { st0Clean with revDirs := [] })) =
          toAmd64Program symName pLoad ++ toAmd64Program symName pOp := by
      dsimp only [emitLinNode0]; rw [hnd]; dsimp only
      rw [hvsl0, (emitOp0_acc op _).1, emitFwd0_append, toAmd64Program_append]
    have hprog_1 := hprog.append.1
    rw [hemit_eq] at hprog_1
    have hlen3 : (op0ArgTys op).length ≤ 6 := Nat.le_trans (op0ArgTys_length_le op) (by decide)
    have hld := loadRegArgs0_spec (symName := symName) (h := h)
      (k := k + (if cur.lblId = 0 then 0 else 1))
      (post := fnPost0 h rs Q X s0 ra0 n nX Rf)
      (LoadCfg0.mk false false cur.venv st.vslot) [] args 0 (fun _ => rfl)
      (by simp [hargs_len, hlen3]) (fun h => by cases h) hvals (fnFrameInv0_mem_slots hfr)
    refine hld hprog_1.append.1 fun s1 ⟨hm1, hregs1⟩ hfr1 => ?_
    have hfr1' : FnFrameInv0 ns s0 ra0 n Rf mCurMem s1 σ :=
      fnFrameInv0_weaken_scratchAndAbi hfr hfr1 hm1
    have hin : OpArgsIn0 s1 op argv := by
      refine opArgsIn0_of_regs op argv s1 fun j hj => ?_
      have h' := hregs1 j (hargs_len ▸ hj) (by rw [tupToCanon64s_length]; exact hj)
      simpa only [UInt32.toNat_zero, Nat.zero_add] using h'
    have hop_spec := emitOp0_spec (symName := symName) (h := h)
      (k := k + (if cur.lblId = 0 then 0 else 1) + (toAmd64Program symName pLoad).length)
      (post := fnPost0 h rs Q X s0 ra0 n nX Rf) op hvalid hin hwp
    refine hop_spec hprog_1.append.2 fun s2 ⟨rv, hsingle, hrax, hm2⟩ hfr2 => ?_
    have hfr2' : FnFrameInv0 ns s0 ra0 n Rf mCurMem s2 σ :=
      fnFrameInv0_weaken_scratchAndAbi hfr1' hfr2 hm2
    have hwp' : wp0 Γ symName rs (pushTup (as := [ty0ToTy (opRetTy0 op)]) (rv, ()) vs)
        ls Q X cont mCurMem :=
      singleRetPost0_pushTup
        (K := fun vs' => wp0 Γ symName rs vs' ls Q X cont mCurMem) hvalid hsingle
    have htup2 : tupAbiHolds0 s2 true 0 [opRetTy0 op] (rv, ()) := ⟨hrax, trivial⟩
    have hlen_add :
        k + (if cur.lblId = 0 then 0 else 1) +
          (toAmd64Program symName (emitFwd0 (emitLinNode0 cur
            { st0Clean with revDirs := [] }))).length =
        k + (if cur.lblId = 0 then 0 else 1) + (toAmd64Program symName pLoad).length +
          (toAmd64Program symName pOp).length := by
      rw [hemit_eq, List.length_append, ← Nat.add_assoc]
    have hk_inf := hprog.append.2
    rw [hlen_add] at hk_inf
    exact stepLinear_bind_ok_ret (by rw [hnd]) (by rw [hnd]) (rv, ()) hlin hnj hng
      hfuel hns_eq hinv hlen_pw hlen_mw hk_inf hwp' hfr2' htup2 hag hgl
      fun k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' mMeta' fuel' s' σ'
        hinv' hpw' hmw' heq_nd hnc' hfuel' hns' hk_inf' hwp_n hfr_n hag_n hgl_n =>
      hih k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' mMeta' fuel' s' σ'
        _ ls mCurMem hinv' hpw' hmw' (by rw [hnc', hnd]; dsimp only [linK0, nodeCount0]; omega)
        hfuel' hns' hk_inf' hwp_n hfr_n hag_n hgl_n
        (by rw [heq_nd]; exact nodeContracts0_lin hc_node hlin hnj hng)

theorem umulw_run_ok {h : Host} {symName : Sym0 → Sym} {Γ : Env} {ctx : LegalCtx0}
    {fnIdx : UInt32} {fnMaxJump : Nat} {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0}
    {curPre : PreItem0} {pw₂ : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {w₂ : List RegaTask0} {mCur : TaskMeta0} {m₂ : List TaskMeta0}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {rs : List Ty0} {Q : Post (ty0ListToTy rs)} {X : XPost}
    {s0 : MachineData} {ra0 : Int64} {n nX : Nat} {Rf : Mem 64 → Prop} {ns : UInt32}
    {a b : Arg0} {cont : TFlat0} {k : Nat} {fuel : UInt32}
    {mCurMem : Mem 64} {s : MachineData} {σ : List (BitVec 64)}
    (hnd : cur.node = .let2Umulw64 a b cont)
    (hfuel : workNodeCount0 ((cur :: w₂).map RegaTask0.node) ≤ fuel.toNat)
    (hns_eq : (regaRunAux0 fuel preRes.escaped st ctrl (cur :: w₂)).1.maxSlots = ns)
    (hinv : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: pw₂) seenJnz st ctrl
      (cur :: w₂) (mCur :: m₂))
    (hlen_pw : pw₂.length = w₂.length) (hlen_mw : m₂.length = w₂.length)
    (hcode : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
      (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 cur.node)) preRes.escaped
        { st with revDirs := [] } ctrl [cur]).1.revDirs) [])).IsInfixAt
      (x64ScalarMach.prog h) k)
    (hu : x64ScalarTarget.LabelsUnique h)
    (hwp : wp0 Γ symName rs vs ls Q X cur.node mCurMem)
    (hfr : FnFrameInv0 ns s0 ra0 n Rf mCurMem s σ)
    (hag : SlotsAgree0 preRes.escaped preSt st curPre cur mCur.vT vs σ)
    (hgl : GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
      preRes.escaped st cur mCur vs fnIdx mCur.gl ls)
    (hc_node : NodeContracts0 h symName Γ ctx ns n nX cur.node)
    (hih : ∀ k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' m' fuel' s' σ'
        vs' ls' mMem',
      RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc' preSt' (curPre' :: pw') seenJnz' st' ctrl'
        (cur' :: w') (mCur' :: m') →
      pw'.length = w'.length → m'.length = w'.length →
      nodeCount0 cur'.node < nodeCount0 cur.node →
      workNodeCount0 ((cur' :: w').map RegaTask0.node) ≤ fuel'.toNat →
      (regaRunAux0 fuel' preRes.escaped st' ctrl' (cur' :: w')).1.maxSlots = ns →
      (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
        (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 cur'.node)) preRes.escaped
          { st' with revDirs := [] } ctrl' [cur']).1.revDirs) [])).IsInfixAt
        (x64ScalarMach.prog h) k_nxt →
      wp0 Γ symName rs vs' ls' Q X cur'.node mMem' →
      FnFrameInv0 ns s0 ra0 n Rf mMem' s' σ' →
      SlotsAgree0 preRes.escaped preSt' st' curPre' cur' mCur'.vT vs' σ' →
      GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
        preRes.escaped st' cur' mCur' vs' fnIdx mCur'.gl ls' →
      NodeContracts0 h symName Γ ctx ns n nX cur'.node →
      x64ScalarMach.Run h k_nxt s' (fnPost0 h rs Q X s0 ra0 n nX Rf)) :
    x64ScalarMach.Run h k s (fnPost0 h rs Q X s0 ra0 n nX Rf) := by
  have hlin : isTerm0 cur.node = false := by rw [hnd]; rfl
  have hnj : ∀ c t e, cur.node ≠ .jnz c t e := fun _ _ _ he => by rw [hnd] at he; cases he
  have hng : ∀ bs k', cur.node ≠ .group bs k' := fun _ _ he => by rw [hnd] at he; cases he
  have hcur_ok := hinv.items_ok 0 (by simp) (by simp) (by simp)
  dsimp only [List.getElem_cons_zero] at hcur_ok
  obtain ⟨_, _, hvlen, _, _, _, _, hwf, _, _, _, _, _, _, _, _, _⟩ := hcur_ok
  have ⟨hca, hcb⟩ : checkArg0 mCur.vT .b64 a = true ∧ checkArg0 mCur.vT .b64 b = true := by
    rw [hnd] at hwf; cases hwf; exact ⟨‹_›, ‹_›⟩
  have hva_ok : ∀ idx, a = .var idx → idx.toNat < cur.venv.length := fun idx he => by
    have hva := wfNode0_nodeArgsInVenv0 hwf; rw [← hvlen, hnd] at hva; exact hva.1 idx he
  have hvb_ok : ∀ idx, b = .var idx → idx.toNat < cur.venv.length := fun idx he => by
    have hva := wfNode0_nodeArgsInVenv0 hwf; rw [← hvlen, hnd] at hva; exact hva.2 idx he
  have hlive_a : ∀ idx, a = .var idx →
      LiveInTask0 preRes.escaped preSt st curPre cur (listGetU32 cur.venv idx).toNat :=
    fun idx he => taskMetaOk0_args_live hinv (args := [a])
      (fun x hx idx' heq => by
        rw [List.mem_singleton.mp hx] at heq
        rw [hnd]; exact nodeArgsUses0_pos_lin_term (Or.inl heq))
      (fun x hx => by rw [List.mem_singleton.mp hx]; exact hva_ok) a List.mem_cons_self idx he
  have hlive_b : ∀ idx, b = .var idx →
      LiveInTask0 preRes.escaped preSt st curPre cur (listGetU32 cur.venv idx).toNat :=
    fun idx he => taskMetaOk0_args_live hinv (args := [b])
      (fun x hx idx' heq => by
        rw [List.mem_singleton.mp hx] at heq
        rw [hnd]; exact nodeArgsUses0_pos_lin_term (Or.inr heq))
      (fun x hx => by rw [List.mem_singleton.mp hx]; exact hvb_ok) b List.mem_cons_self idx he
  rw [hnd, wp0_let2Umulw64] at hwp
  cases hea : evalArg0Ty vs (.bits 64) a with
  | none => rw [hea] at hwp; exact False.elim hwp
  | some va =>
    cases heb : evalArg0Ty vs (.bits 64) b with
    | none => rw [hea, heb] at hwp; exact False.elim hwp
    | some vb =>
      rw [hea, heb] at hwp
      have ha := argSlotVal64_of_evalArg0Ty hca hag hea hlive_a
      have hb := argSlotVal64_of_evalArg0Ty hcb hag heb hlive_b
      have hsplit := stepLinear_program_split preRes.escaped cur st ctrl ns hlin hnj hng
        (nodeCount0_head_lt_2p31 hinv) hcode
      dsimp only at hsplit
      refine regaPrependLbl0_run cur st ctrl (x64FrameSizeU0 ns) _ s
        (fnPost0 h rs Q X s0 ra0 n nX Rf) hu hsplit fun _ hprog => ?_
      let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
      have hvsl0 : ({ st0Clean with revDirs := [] } : RegaSt0).vslot = st.vslot :=
        regaPrependLbl0_vslot_eq cur { st with revDirs := [] } ctrl
      have hemit_eq :
          emitLinNode0 cur { st0Clean with revDirs := [] } =
            emitLinUmulw0 a b cur { st with revDirs := [] } := by
        dsimp only [emitLinNode0, emitLinMem0]; rw [hnd]; dsimp only [emitLinUmulw0]; rw [hvsl0]
      have hprog1 := hprog.append.1
      rw [hemit_eq] at hprog1
      have hspec := emitLinUmulw0_spec (symName := symName) (h := h)
        (k := k + (if cur.lblId = 0 then 0 else 1))
        (post := fnPost0 h rs Q X s0 ra0 n nX Rf) a b cur st ha hb hwp
        (fnFrameInv0_mem_slots hfr)
      refine hspec hprog1 fun s2 ⟨lo, hi, hP, hrax, hrdx, hm2⟩ hfr2 => ?_
      have hfr2' : FnFrameInv0 ns s0 ra0 n Rf mCurMem s2 σ :=
        fnFrameInv0_weaken_scratchAndAbi hfr hfr2 hm2
      have hwp' : wp0 Γ symName rs (pushTup (as := ty0ListToTy [.b64, .b64]) (lo, hi, ()) vs)
          ls Q X cont mCurMem := hP
      have htup2 : tupAbiHolds0 s2 true 0 [.b64, .b64] (lo, hi, ()) := ⟨hrax, hrdx, trivial⟩
      have hk_inf := hprog.append.2
      rw [hemit_eq] at hk_inf
      exact stepLinear_bind_ok_ret (by rw [hnd]) (by rw [hnd]) (lo, hi, ()) hlin hnj hng
        hfuel hns_eq hinv hlen_pw hlen_mw hk_inf hwp' hfr2' htup2 hag hgl
        fun k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' mMeta' fuel' s' σ'
          hinv' hpw' hmw' heq_nd hnc' hfuel' hns' hk_inf' hwp_n hfr_n hag_n hgl_n =>
        hih k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' mMeta' fuel' s' σ'
          _ ls mCurMem hinv' hpw' hmw' (by rw [hnc', hnd]; dsimp only [linK0, nodeCount0]; omega)
          hfuel' hns' hk_inf' hwp_n hfr_n hag_n hgl_n
          (by rw [heq_nd]; exact nodeContracts0_lin hc_node hlin hnj hng)

theorem load_run_ok {h : Host} {symName : Sym0 → Sym} {Γ : Env} {ctx : LegalCtx0}
    {fnIdx : UInt32} {fnMaxJump : Nat} {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0}
    {curPre : PreItem0} {pw₂ : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {w₂ : List RegaTask0} {mCur : TaskMeta0} {m₂ : List TaskMeta0}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {rs : List Ty0} {Q : Post (ty0ListToTy rs)} {X : XPost}
    {s0 : MachineData} {ra0 : Int64} {n nX : Nat} {Rf : Mem 64 → Prop} {ns : UInt32}
    {t : Ty0} {addr : Arg0} {cont : TFlat0} {k : Nat} {fuel : UInt32}
    {mCurMem : Mem 64} {s : MachineData} {σ : List (BitVec 64)}
    (hnd : cur.node = .load t addr cont)
    (hfuel : workNodeCount0 ((cur :: w₂).map RegaTask0.node) ≤ fuel.toNat)
    (hns_eq : (regaRunAux0 fuel preRes.escaped st ctrl (cur :: w₂)).1.maxSlots = ns)
    (hinv : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: pw₂) seenJnz st ctrl
      (cur :: w₂) (mCur :: m₂))
    (hlen_pw : pw₂.length = w₂.length) (hlen_mw : m₂.length = w₂.length)
    (hcode : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
      (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 cur.node)) preRes.escaped
        { st with revDirs := [] } ctrl [cur]).1.revDirs) [])).IsInfixAt
      (x64ScalarMach.prog h) k)
    (hu : x64ScalarTarget.LabelsUnique h)
    (hwp : wp0 Γ symName rs vs ls Q X cur.node mCurMem)
    (hfr : FnFrameInv0 ns s0 ra0 n Rf mCurMem s σ)
    (hag : SlotsAgree0 preRes.escaped preSt st curPre cur mCur.vT vs σ)
    (hgl : GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
      preRes.escaped st cur mCur vs fnIdx mCur.gl ls)
    (hc_node : NodeContracts0 h symName Γ ctx ns n nX cur.node)
    (hih : ∀ k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' m' fuel' s' σ'
        vs' ls' mMem',
      RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc' preSt' (curPre' :: pw') seenJnz' st' ctrl'
        (cur' :: w') (mCur' :: m') →
      pw'.length = w'.length → m'.length = w'.length →
      nodeCount0 cur'.node < nodeCount0 cur.node →
      workNodeCount0 ((cur' :: w').map RegaTask0.node) ≤ fuel'.toNat →
      (regaRunAux0 fuel' preRes.escaped st' ctrl' (cur' :: w')).1.maxSlots = ns →
      (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
        (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 cur'.node)) preRes.escaped
          { st' with revDirs := [] } ctrl' [cur']).1.revDirs) [])).IsInfixAt
        (x64ScalarMach.prog h) k_nxt →
      wp0 Γ symName rs vs' ls' Q X cur'.node mMem' →
      FnFrameInv0 ns s0 ra0 n Rf mMem' s' σ' →
      SlotsAgree0 preRes.escaped preSt' st' curPre' cur' mCur'.vT vs' σ' →
      GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
        preRes.escaped st' cur' mCur' vs' fnIdx mCur'.gl ls' →
      NodeContracts0 h symName Γ ctx ns n nX cur'.node →
      x64ScalarMach.Run h k_nxt s' (fnPost0 h rs Q X s0 ra0 n nX Rf)) :
    x64ScalarMach.Run h k s (fnPost0 h rs Q X s0 ra0 n nX Rf) := by
  have hlin : isTerm0 cur.node = false := by rw [hnd]; rfl
  have hnj : ∀ c t e, cur.node ≠ .jnz c t e := fun _ _ _ he => by rw [hnd] at he; cases he
  have hng : ∀ bs k', cur.node ≠ .group bs k' := fun _ _ he => by rw [hnd] at he; cases he
  have hcur_ok := hinv.items_ok 0 (by simp) (by simp) (by simp)
  dsimp only [List.getElem_cons_zero] at hcur_ok
  obtain ⟨_, _, hvlen, _, _, _, _, hwf, _, _, _, _, _, _, _, _, _⟩ := hcur_ok
  have hcaddr : checkArg0 mCur.vT .b64 addr = true := by rw [hnd] at hwf; cases hwf; assumption
  have haddr_ok : ∀ idx, addr = .var idx → idx.toNat < cur.venv.length := fun idx he => by
    have hva := wfNode0_nodeArgsInVenv0 hwf; rw [← hvlen, hnd] at hva; exact hva idx he
  have hlive_addr : ∀ idx, addr = .var idx →
      LiveInTask0 preRes.escaped preSt st curPre cur (listGetU32 cur.venv idx).toNat :=
    fun idx he => taskMetaOk0_args_live hinv (args := [addr])
      (fun x hx idx' heq => by
        rw [List.mem_singleton.mp hx] at heq; rw [hnd]; exact nodeArgsUses0_pos_lin_term heq)
      (fun x hx => by rw [List.mem_singleton.mp hx]; exact haddr_ok) addr List.mem_cons_self idx he
  rw [hnd, wp0_load] at hwp
  cases hea : evalArg0Ty vs (.bits 64) addr with
  | none => rw [hea] at hwp; exact False.elim hwp
  | some addrVal =>
    rw [hea] at hwp
    obtain ⟨v, hlv, hwp'⟩ := hwp
    have ha := argSlotVal64_of_evalArg0Ty hcaddr hag hea hlive_addr
    have hs_mem : (Eq mCurMem ⋆ (array64 (s.regs.get64 .rsp) σ ⋆
        x64ScalarFramePreds.Saved (s0.regs.get64 .rsp) ra0 ns.toNat ⋆
        region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆ Rf))
        s.dmem := sep_cast hfr.2.2.2 (by ac_rfl)
    have hlv_s := loadVal_frame hs_mem hlv
    have hsplit := stepLinear_program_split preRes.escaped cur st ctrl ns hlin hnj hng
      (nodeCount0_head_lt_2p31 hinv) hcode
    dsimp only at hsplit
    refine regaPrependLbl0_run cur st ctrl (x64FrameSizeU0 ns) _ s
      (fnPost0 h rs Q X s0 ra0 n nX Rf) hu hsplit fun _ hprog => ?_
    let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
    have hvsl0 : ({ st0Clean with revDirs := [] } : RegaSt0).vslot = st.vslot :=
      regaPrependLbl0_vslot_eq cur { st with revDirs := [] } ctrl
    have hemit_eq :
        emitLinNode0 cur { st0Clean with revDirs := [] } =
          pushDRR0 2 (tyWidth0 t) .rax .rdi (emitLoadArg0 .rdi addr cur.venv st.vslot []) := by
      dsimp only [emitLinNode0, emitLinMem0]; rw [hnd]; rw [hvsl0]
    have hprog1 := hprog.append.1
    rw [hemit_eq] at hprog1
    have hspec := emitLinLoad0_spec (symName := symName) (h := h)
      (k := k + (if cur.lblId = 0 then 0 else 1))
      (post := fnPost0 h rs Q X s0 ra0 n nX Rf) t addr cur st ha hlv_s
      (fnFrameInv0_mem_slots hfr)
    refine hspec hprog1 fun s2 ⟨hrax, hm2⟩ hfr2 => ?_
    have hfr2' : FnFrameInv0 ns s0 ra0 n Rf mCurMem s2 σ :=
      fnFrameInv0_weaken_scratchAndAbi hfr hfr2 hm2
    have hwp_k : wp0 Γ symName rs (pushTup (as := ty0ListToTy [t]) (v, ()) vs)
        ls Q X cont mCurMem := hwp'
    have htup2 : tupAbiHolds0 s2 true 0 [t] (v, ()) := ⟨hrax, trivial⟩
    have hk_inf := hprog.append.2
    rw [hemit_eq] at hk_inf
    exact stepLinear_bind_ok_ret (by rw [hnd]) (by rw [hnd]) (v, ()) hlin hnj hng
      hfuel hns_eq hinv hlen_pw hlen_mw hk_inf hwp_k hfr2' htup2 hag hgl
      fun k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' mMeta' fuel' s' σ'
        hinv' hpw' hmw' heq_nd hnc' hfuel' hns' hk_inf' hwp_n hfr_n hag_n hgl_n =>
      hih k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' mMeta' fuel' s' σ'
        _ ls mCurMem hinv' hpw' hmw' (by rw [hnc', hnd]; dsimp only [linK0, nodeCount0]; omega)
        hfuel' hns' hk_inf' hwp_n hfr_n hag_n hgl_n
        (by rw [heq_nd]; exact nodeContracts0_lin hc_node hlin hnj hng)

theorem store_run_ok {h : Host} {symName : Sym0 → Sym} {Γ : Env} {ctx : LegalCtx0}
    {fnIdx : UInt32} {fnMaxJump : Nat} {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0}
    {curPre : PreItem0} {pw₂ : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {w₂ : List RegaTask0} {mCur : TaskMeta0} {m₂ : List TaskMeta0}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {rs : List Ty0} {Q : Post (ty0ListToTy rs)} {X : XPost}
    {s0 : MachineData} {ra0 : Int64} {n nX : Nat} {Rf : Mem 64 → Prop} {ns : UInt32}
    {t : Ty0} {val addr : Arg0} {cont : TFlat0} {k : Nat} {fuel : UInt32}
    {mCurMem : Mem 64} {s : MachineData} {σ : List (BitVec 64)}
    (hnd : cur.node = .store t val addr cont)
    (hfuel : workNodeCount0 ((cur :: w₂).map RegaTask0.node) ≤ fuel.toNat)
    (hns_eq : (regaRunAux0 fuel preRes.escaped st ctrl (cur :: w₂)).1.maxSlots = ns)
    (hinv : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: pw₂) seenJnz st ctrl
      (cur :: w₂) (mCur :: m₂))
    (hlen_pw : pw₂.length = w₂.length) (hlen_mw : m₂.length = w₂.length)
    (hcode : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
      (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 cur.node)) preRes.escaped
        { st with revDirs := [] } ctrl [cur]).1.revDirs) [])).IsInfixAt
      (x64ScalarMach.prog h) k)
    (hu : x64ScalarTarget.LabelsUnique h)
    (hwp : wp0 Γ symName rs vs ls Q X cur.node mCurMem)
    (hfr : FnFrameInv0 ns s0 ra0 n Rf mCurMem s σ)
    (hag : SlotsAgree0 preRes.escaped preSt st curPre cur mCur.vT vs σ)
    (hgl : GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
      preRes.escaped st cur mCur vs fnIdx mCur.gl ls)
    (hc_node : NodeContracts0 h symName Γ ctx ns n nX cur.node)
    (hih : ∀ k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' m' fuel' s' σ'
        vs' ls' mMem',
      RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc' preSt' (curPre' :: pw') seenJnz' st' ctrl'
        (cur' :: w') (mCur' :: m') →
      pw'.length = w'.length → m'.length = w'.length →
      nodeCount0 cur'.node < nodeCount0 cur.node →
      workNodeCount0 ((cur' :: w').map RegaTask0.node) ≤ fuel'.toNat →
      (regaRunAux0 fuel' preRes.escaped st' ctrl' (cur' :: w')).1.maxSlots = ns →
      (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
        (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 cur'.node)) preRes.escaped
          { st' with revDirs := [] } ctrl' [cur']).1.revDirs) [])).IsInfixAt
        (x64ScalarMach.prog h) k_nxt →
      wp0 Γ symName rs vs' ls' Q X cur'.node mMem' →
      FnFrameInv0 ns s0 ra0 n Rf mMem' s' σ' →
      SlotsAgree0 preRes.escaped preSt' st' curPre' cur' mCur'.vT vs' σ' →
      GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
        preRes.escaped st' cur' mCur' vs' fnIdx mCur'.gl ls' →
      NodeContracts0 h symName Γ ctx ns n nX cur'.node →
      x64ScalarMach.Run h k_nxt s' (fnPost0 h rs Q X s0 ra0 n nX Rf)) :
    x64ScalarMach.Run h k s (fnPost0 h rs Q X s0 ra0 n nX Rf) := by
  have hlin : isTerm0 cur.node = false := by rw [hnd]; rfl
  have hnj : ∀ c t e, cur.node ≠ .jnz c t e := fun _ _ _ he => by rw [hnd] at he; cases he
  have hng : ∀ bs k', cur.node ≠ .group bs k' := fun _ _ he => by rw [hnd] at he; cases he
  have hcur_ok := hinv.items_ok 0 (by simp) (by simp) (by simp)
  dsimp only [List.getElem_cons_zero] at hcur_ok
  obtain ⟨_, _, hvlen, _, _, _, _, hwf, _, _, _, _, _, _, _, _, _⟩ := hcur_ok
  have ⟨hcval, hcaddr⟩ : checkArg0 mCur.vT t val = true ∧ checkArg0 mCur.vT .b64 addr = true := by
    rw [hnd] at hwf; cases hwf; exact ⟨‹_›, ‹_›⟩
  have hval_ok : ∀ idx, val = .var idx → idx.toNat < cur.venv.length := fun idx he => by
    have hva := wfNode0_nodeArgsInVenv0 hwf; rw [← hvlen, hnd] at hva; exact hva.1 idx he
  have haddr_ok : ∀ idx, addr = .var idx → idx.toNat < cur.venv.length := fun idx he => by
    have hva := wfNode0_nodeArgsInVenv0 hwf; rw [← hvlen, hnd] at hva; exact hva.2 idx he
  have hlive_val : ∀ idx, val = .var idx →
      LiveInTask0 preRes.escaped preSt st curPre cur (listGetU32 cur.venv idx).toNat :=
    fun idx he => taskMetaOk0_args_live hinv (args := [val])
      (fun x hx idx' heq => by
        rw [List.mem_singleton.mp hx] at heq
        rw [hnd]; exact nodeArgsUses0_pos_lin_term (Or.inl heq))
      (fun x hx => by rw [List.mem_singleton.mp hx]; exact hval_ok) val List.mem_cons_self idx he
  have hlive_addr : ∀ idx, addr = .var idx →
      LiveInTask0 preRes.escaped preSt st curPre cur (listGetU32 cur.venv idx).toNat :=
    fun idx he => taskMetaOk0_args_live hinv (args := [addr])
      (fun x hx idx' heq => by
        rw [List.mem_singleton.mp hx] at heq
        rw [hnd]; exact nodeArgsUses0_pos_lin_term (Or.inr heq))
      (fun x hx => by rw [List.mem_singleton.mp hx]; exact haddr_ok) addr List.mem_cons_self idx he
  rw [hnd, wp0_store] at hwp
  cases hev_v : evalArg0Ty vs (ty0ToTy t) val with
  | none => rw [hev_v] at hwp; exact False.elim hwp
  | some v =>
    cases hev_a : evalArg0Ty vs (.bits 64) addr with
    | none => rw [hev_v, hev_a] at hwp; exact False.elim hwp
    | some addrVal =>
      rw [hev_v, hev_a] at hwp
      obtain ⟨hok, hwp'⟩ := hwp
      have hv := argSlotVal64_of_evalArg0Ty hcval hag hev_v hlive_val
      have ha := argSlotVal64_of_evalArg0Ty hcaddr hag hev_a hlive_addr
      have hs_mem : (Eq mCurMem ⋆ (array64 (s.regs.get64 .rsp) σ ⋆
          x64ScalarFramePreds.Saved (s0.regs.get64 .rsp) ra0 ns.toNat ⋆
          region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆ Rf))
          s.dmem := sep_cast hfr.2.2.2 (by ac_rfl)
      have hok_s := storeOk_frame hs_mem hok
      have hsplit := stepLinear_program_split preRes.escaped cur st ctrl ns hlin hnj hng
        (nodeCount0_head_lt_2p31 hinv) hcode
      dsimp only at hsplit
      refine regaPrependLbl0_run cur st ctrl (x64FrameSizeU0 ns) _ s
        (fnPost0 h rs Q X s0 ra0 n nX Rf) hu hsplit fun _ hprog => ?_
      let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
      have hvsl0 : ({ st0Clean with revDirs := [] } : RegaSt0).vslot = st.vslot :=
        regaPrependLbl0_vslot_eq cur { st with revDirs := [] } ctrl
      have hemit_eq :
          emitLinNode0 cur { st0Clean with revDirs := [] } =
            emitLinStore0 t val addr cur { st with revDirs := [] } := by
        dsimp only [emitLinNode0, emitLinMem0]; rw [hnd]; dsimp only [emitLinStore0]; rw [hvsl0]
      have hprog1 := hprog.append.1
      rw [hemit_eq] at hprog1
      have hspec := emitLinStore0_spec (symName := symName) (h := h)
        (k := k + (if cur.lblId = 0 then 0 else 1))
        (post := fnPost0 h rs Q X s0 ra0 n nX Rf) t val addr cur st hv ha hok_s
        (fnFrameInv0_mem_slots hfr)
      refine hspec hprog1 fun s2 hm2 hfr2 => ?_
      have hrsp2 : s2.regs.get64 .rsp = s.regs.get64 .rsp :=
        hfr2.1 .rsp rsp_not_mem_scratchAndAbi
      have hfr2' : FnFrameInv0 ns s0 ra0 n Rf (storeMem mCurMem (ty0ToTy t) addrVal v) s2 σ := by
        refine ⟨hfr.1, hrsp2.trans hfr.2.1,
          fun r hr => (hfr2.1 r (calleeSaved_not_mem_scratchAndAbi r hr)).trans (hfr.2.2.1 r hr),
          ?_⟩
        rw [hm2, hrsp2]
        exact sep_cast (storeMem_frame hs_mem hok v) (by ac_rfl)
      have hwp_k : wp0 Γ symName rs (pushTup (as := ty0ListToTy []) () vs) ls Q X cont
          (storeMem mCurMem (ty0ToTy t) addrVal v) := hwp'
      have htup2 : tupAbiHolds0 s2 true 0 [] () := trivial
      have hk_inf := hprog.append.2
      rw [hemit_eq] at hk_inf
      exact stepLinear_bind_ok_ret (by rw [hnd]) (by rw [hnd]) () hlin hnj hng
        hfuel hns_eq hinv hlen_pw hlen_mw hk_inf hwp_k hfr2' htup2 hag hgl
        fun k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' mMeta' fuel' s' σ'
          hinv' hpw' hmw' heq_nd hnc' hfuel' hns' hk_inf' hwp_n hfr_n hag_n hgl_n =>
        hih k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' mMeta' fuel' s' σ'
          _ ls (storeMem mCurMem (ty0ToTy t) addrVal v) hinv' hpw' hmw'
          (by rw [hnc', hnd]; dsimp only [linK0, nodeCount0]; omega)
          hfuel' hns' hk_inf' hwp_n hfr_n hag_n hgl_n
          (by rw [heq_nd]; exact nodeContracts0_lin hc_node hlin hnj hng)

theorem call_run_ok {h : Host} {symName : Sym0 → Sym} {Γ : Env} {ctx : LegalCtx0}
    {fnIdx : UInt32} {fnMaxJump : Nat} {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0}
    {curPre : PreItem0} {pw₂ : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {w₂ : List RegaTask0} {mCur : TaskMeta0} {m₂ : List TaskMeta0}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {rs : List Ty0} {Q : Post (ty0ListToTy rs)} {X : XPost}
    {s0 : MachineData} {ra0 : Int64} {n nX : Nat} {Rf : Mem 64 → Prop} {ns : UInt32}
    {fnSym : Sym0} {as bs : List Ty0} {args : List Arg0} {cont : TFlat0} {k : Nat} {fuel : UInt32}
    {mCurMem : Mem 64} {s : MachineData} {σ : List (BitVec 64)}
    (hnd : cur.node = .call fnSym as bs args cont)
    (hn_bd : n + 8 ≤ 2 ^ 64) (hsp0 : x64ScalarTarget.frameSpec.spEntry (s0.regs.get64 .rsp))
    (hc_node : NodeContracts0 h symName Γ ctx ns n nX cur.node)
    (hfuel : workNodeCount0 ((cur :: w₂).map RegaTask0.node) ≤ fuel.toNat)
    (hns_eq : (regaRunAux0 fuel preRes.escaped st ctrl (cur :: w₂)).1.maxSlots = ns)
    (hinv : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: pw₂) seenJnz st ctrl
      (cur :: w₂) (mCur :: m₂))
    (hlen_pw : pw₂.length = w₂.length) (hlen_mw : m₂.length = w₂.length)
    (hcode : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
      (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 cur.node)) preRes.escaped
        { st with revDirs := [] } ctrl [cur]).1.revDirs) [])).IsInfixAt
      (x64ScalarMach.prog h) k)
    (hu : x64ScalarTarget.LabelsUnique h)
    (hwp : wp0 Γ symName rs vs ls Q X cur.node mCurMem)
    (hfr : FnFrameInv0 ns s0 ra0 n Rf mCurMem s σ)
    (hag : SlotsAgree0 preRes.escaped preSt st curPre cur mCur.vT vs σ)
    (hgl : GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
      preRes.escaped st cur mCur vs fnIdx mCur.gl ls)
    (hih : ∀ k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' m' fuel' s' σ'
        vs' ls' mMem',
      RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc' preSt' (curPre' :: pw') seenJnz' st' ctrl'
        (cur' :: w') (mCur' :: m') →
      pw'.length = w'.length → m'.length = w'.length →
      nodeCount0 cur'.node < nodeCount0 cur.node →
      workNodeCount0 ((cur' :: w').map RegaTask0.node) ≤ fuel'.toNat →
      (regaRunAux0 fuel' preRes.escaped st' ctrl' (cur' :: w')).1.maxSlots = ns →
      (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
        (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 cur'.node)) preRes.escaped
          { st' with revDirs := [] } ctrl' [cur']).1.revDirs) [])).IsInfixAt
        (x64ScalarMach.prog h) k_nxt →
      wp0 Γ symName rs vs' ls' Q X cur'.node mMem' →
      FnFrameInv0 ns s0 ra0 n Rf mMem' s' σ' →
      SlotsAgree0 preRes.escaped preSt' st' curPre' cur' mCur'.vT vs' σ' →
      GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
        preRes.escaped st' cur' mCur' vs' fnIdx mCur'.gl ls' →
      NodeContracts0 h symName Γ ctx ns n nX cur'.node →
      x64ScalarMach.Run h k_nxt s' (fnPost0 h rs Q X s0 ra0 n nX Rf)) :
    x64ScalarMach.Run h k s (fnPost0 h rs Q X s0 ra0 n nX Rf) := by
  have hlin : isTerm0 cur.node = false := by rw [hnd]; rfl
  have hnj : ∀ c t e, cur.node ≠ .jnz c t e := fun _ _ _ he => by rw [hnd] at he; cases he
  have hng : ∀ bs' k', cur.node ≠ .group bs' k' := fun _ _ he => by rw [hnd] at he; cases he
  have hcur_ok := hinv.items_ok 0 (by simp) (by simp) (by simp)
  dsimp only [List.getElem_cons_zero] at hcur_ok
  obtain ⟨_, _, hvlen, _, _, _, _, hwf, _, _, _, _, _, _, _, _, _⟩ := hcur_ok
  have ⟨has6, hbs7, hcargs⟩ :
      as.length ≤ 6 ∧ bs.length ≤ 7 ∧ checkArgs0 mCur.vT as args = true := by
    rw [hnd] at hwf; cases hwf; exact ⟨‹_›, ‹_›, ‹_›⟩
  have hc_cont : NodeContracts0 h symName Γ ctx ns n nX cont := by
    rw [hnd] at hc_node; dsimp only [NodeContracts0] at hc_node; exact hc_node.2
  rw [hnd] at hc_node; dsimp only [NodeContracts0] at hc_node
  obtain ⟨⟨bound, hbd_le, _, hfspec⟩, _⟩ := hc_node
  have hc_specs := checkArgs0_spec hcargs
  have hargs_len : args.length = as.length := hc_specs.1.symm
  have hargs_ok : ∀ a ∈ args, ∀ idx, a = .var idx → idx.toNat < cur.venv.length := by
    have hva := wfNode0_nodeArgsInVenv0 hwf; rw [← hvlen, hnd] at hva; exact hva
  have hlive_args : ∀ a ∈ args, ∀ idx, a = .var idx →
      LiveInTask0 preRes.escaped preSt st curPre cur (listGetU32 cur.venv idx).toNat :=
    taskMetaOk0_args_live hinv (fun a ha idx heq => by
      rw [hnd]; exact nodeArgsUses0_pos_lin_term (heq ▸ ha)) hargs_ok
  rw [hnd, wp0_call] at hwp
  cases hev : evalArgs0Ty vs (ty0ListToTy as) args with
  | none => rw [hev] at hwp; exact False.elim hwp
  | some argv =>
    rw [hev] at hwp
    obtain ⟨P, E, hΓ, hP_cont, hE_exit⟩ := hwp
    have hvals := argsSlotVal64_of_evalArgs0Ty hcargs hag hev hlive_args
    have hsplit := stepLinear_program_split preRes.escaped cur st ctrl ns hlin hnj hng
      (nodeCount0_head_lt_2p31 hinv) hcode
    dsimp only at hsplit
    refine regaPrependLbl0_run cur st ctrl (x64FrameSizeU0 ns) _ s
      (fnPost0 h rs Q X s0 ra0 n nX Rf) hu hsplit fun _ hprog => ?_
    let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
    have hvsl0 : ({ st0Clean with revDirs := [] } : RegaSt0).vslot = st.vslot :=
      regaPrependLbl0_vslot_eq cur { st with revDirs := [] } ctrl
    let dLoad := loadRegArgs0 (LoadCfg0.mk false true cur.venv st.vslot) as args 0 []
    have hemit_eq :
        toAmd64Program symName (emitFwd0 (emitLinNode0 cur { st0Clean with revDirs := [] })) =
          toAmd64Program symName (emitFwd0 dLoad) ++ x64Frame.call (symName fnSym) := by
      dsimp only [emitLinNode0]; rw [hnd]; dsimp only
      rw [hvsl0, emitFwd0_cons, toAmd64Program_append]
      rfl
    have hprog1 := hprog.append.1
    rw [hemit_eq] at hprog1
    have hld := loadRegArgs0_spec (symName := symName) (h := h)
      (k := k + (if cur.lblId = 0 then 0 else 1))
      (post := fnPost0 h rs Q X s0 ra0 n nX Rf)
      (LoadCfg0.mk false true cur.venv st.vslot) as args 0 (vals := tupToCanon64s as argv)
      (fun h => by cases h) (by simp [hargs_len, has6])
      (fun _ => ⟨hargs_len.symm, fun j hj1 hj2 => tupToCanon64s_canon_ok as argv j hj1 hj2⟩)
      hvals (fnFrameInv0_mem_slots hfr)
    refine hld hprog1.append.1 fun s1 ⟨hm1, hregs1⟩ hfr1 => ?_
    have hfr1' : FnFrameInv0 ns s0 ra0 n Rf mCurMem s1 σ :=
      fnFrameInv0_weaken_scratchAndAbi hfr hfr1 hm1
    have hargs1 : x64ScalarTarget.ArgsIn argv s1 := by
      refine (argsIn_ty0_iff has6 argv s1).mpr (tupAbiHolds0_of_regs false 0 as argv s1 ?_)
      intro j hj
      have h' := hregs1 j (hargs_len ▸ hj) (by rw [tupToCanon64s_length]; exact hj)
      simpa only [UInt32.toNat_zero, Nat.zero_add] using h'
    let k_call := k + (if cur.lblId = 0 then 0 else 1) +
      (toAmd64Program symName (emitFwd0 dLoad)).length
    let k_ret := k_call + (x64Frame.call (symName fnSym)).length
    let G_call :=
      array64 (s1.regs.get64 .rsp) σ ⋆ Eq mCurMem ⋆
      x64ScalarFramePreds.Saved (s0.regs.get64 .rsp) ra0 ns.toNat ⋆
      region (((s0.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat)) - 8#64) -
        BitVec.ofNat 64 bound) bound ⋆
      region (s0.regs.get64 .rsp - BitVec.ofNat 64 n)
        (n - x64FrameSize ns.toNat - 8 - bound) ⋆ Rf
    have hmem_call :
        s1.dmem =⋆ region (s1.regs.get64 .rsp - BitVec.ofNat 64 x64Frame.raBytes)
          x64Frame.raBytes ⋆ G_call := by
      have hm_ent := fnFrameInv0_mem_entry hfr1'
      rw [call_split_frame_region hbd_le hn_bd] at hm_ent
      have hrsp_eq : s1.regs.get64 .rsp - BitVec.ofNat 64 x64Frame.raBytes =
          (s0.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat)) - 8#64 := by
        rw [hfr1'.2.1]
      rw [hrsp_eq]; dsimp only [G_call, x64ScalarFramePreds, x64FramePreds] at hm_ent ⊢
      exact sep_cast hm_ent (by ac_rfl)
    refine x64ScalarTarget.frameSpec.call_spec hprog1.append.2 hmem_call
      fun s2 hrsp2 hfr2 hra2 hm2 => ?_
    have hargs2 : x64ScalarTarget.ArgsIn argv s2 := by
      refine (argsIn_ty0_iff has6 argv s2).mpr ?_
      refine tupAbiHolds0_frame (fun r hr => hfr2.1 r hr) (fun j _ hm => ?_)
        ((argsIn_ty0_iff has6 argv s1).mp hargs1)
      dsimp only [Isa.frame, x64ScalarTarget, x64Frame] at hm
      exact abiRegAt0_not_in_rsp_scratch false _ hm
    have hrsp2' : s2.regs.get64 .rsp = s1.regs.get64 .rsp - 8#64 := hrsp2
    have hsp2 : x64ScalarTarget.frameSpec.spEntry (s2.regs.get64 .rsp) := by
      have hsp_c := x64ScalarTarget.frameSpec.spEntry_call (s0.regs.get64 .rsp) ns.toNat hsp0
      have hrsp2_eq : s2.regs.get64 .rsp =
          s0.regs.get64 .rsp - BitVec.ofNat 64 (x64Frame.frameSize ns.toNat) -
            BitVec.ofNat 64 x64Frame.raBytes := by
        have hra_e : BitVec.ofNat 64 x64Frame.raBytes = 8#64 := rfl
        have hfs_e : x64Frame.frameSize ns.toNat = x64FrameSize ns.toNat := rfl
        rw [hrsp2', hfr1'.2.1, hra_e, hfs_e]
      rwa [hrsp2_eq]
    let F_call :=
      x64ScalarFramePreds.Saved (s0.regs.get64 .rsp) ra0 ns.toNat ⋆
      array64 (s1.regs.get64 .rsp) σ ⋆
      region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat - 8 - bound)
    have hmem2_cal :
        s2.dmem =⋆ Eq mCurMem ⋆
          x64ScalarTarget.Entry (s2.regs.get64 .rsp) (x64ScalarMach.addrOf h k_ret) bound ⋆
          (F_call ⋆ Rf) := by
      have hra_e : BitVec.ofNat 64 x64Frame.raBytes = 8#64 := rfl
      have hrsp2_eq : s2.regs.get64 .rsp =
          (s0.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat)) - 8#64 := by
        rw [hrsp2', hfr1'.2.1, hra_e]
      change s2.dmem =⋆ Eq mCurMem ⋆
        (region (s2.regs.get64 .rsp - BitVec.ofNat 64 bound) bound ⋆
          x64ScalarFramePreds.RetAddr (s2.regs.get64 .rsp) (x64ScalarMach.addrOf h k_ret)) ⋆
        (F_call ⋆ Rf)
      have hm2' : (s2.dmem =⋆ x64ScalarFramePreds.RetAddr (s2.regs.get64 .rsp)
          (x64ScalarMach.addrOf h k_ret) ⋆ G_call) := hm2
      rw [hrsp2_eq] at hm2' ⊢; dsimp only [G_call, F_call] at hm2' ⊢
      exact sep_cast hm2' (by ac_rfl)
    have hev_cal := hfspec argv mCurMem P E hΓ s2 (x64ScalarMach.addrOf h k_ret) (F_call ⋆ Rf)
      hargs2 hra2 hsp2 hmem2_cal
    refine eventually_trans _ _ _ _ hev_cal fun st_ret hst => ?_
    rcases hst with ⟨hpc, rets, mRet, hP, hrets, hrest, hm_ret⟩ |
      ⟨sym', cs, xs, mRet, hX, hdef', hpc', hargs', hsp', ra', n', F, hnx, hnbd, hra', hm'⟩
    · have hrsp_ret : st_ret.data.regs.get64 .rsp =
          s0.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat) := by
        have hrest2 : st_ret.data.regs.get64 .rsp = s2.regs.get64 .rsp + 8#64 := hrest.2
        rw [hrest2, hrsp2', hfr1'.2.1, BitVec.sub_add_cancel]
      have hcs_ret : ∀ r ∈ x64Frame.calleeSaved,
          st_ret.data.regs.get64 r = s0.regs.get64 r := fun r hr => by
        have h1 : st_ret.data.regs.get64 r = s2.regs.get64 r := hrest.1 r hr
        have hn : r ∉ x64ScalarTarget.frame.sp :: x64ScalarTarget.frame.raRegs ++
            x64ScalarTarget.frame.scratch := by
          dsimp only [Isa.frame, x64ScalarTarget, x64Frame]
          exact calleeSaved_not_in_rsp_scratch r hr
        exact h1.trans ((hfr2.1 r hn).trans (hfr1'.2.2.1 r hr))
      have hm_ret' : FnFrameInv0 ns s0 ra0 n Rf mRet st_ret.data σ := by
        refine ⟨hfr1'.1, hrsp_ret, hcs_ret, ?_⟩
        have h1 : (st_ret.data.dmem =⋆ Eq mRet ⋆
            x64ScalarTarget.Exit (s2.regs.get64 .rsp) bound ⋆ (F_call ⋆ Rf)) := hm_ret
        have hex_eq : x64ScalarTarget.Exit (s2.regs.get64 .rsp) bound =
            region ((s0.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat)) - 8#64 -
              BitVec.ofNat 64 bound) (bound + 8) := by
          change region (s2.regs.get64 .rsp - BitVec.ofNat 64 bound) (bound + 8) = _
          rw [hrsp2', hfr1'.2.1]
        rw [hex_eq] at h1
        dsimp only [F_call, x64ScalarFramePreds, x64FramePreds] at h1
        have h1' : st_ret.data.dmem =⋆ Eq mRet ⋆ array64 (s1.regs.get64 .rsp) σ ⋆
            x64ScalarFramePreds.Saved (s0.regs.get64 .rsp) ra0 ns.toNat ⋆
            (region ((s0.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat)) - 8#64 -
              BitVec.ofNat 64 bound) (bound + 8) ⋆
              region (s0.regs.get64 .rsp - BitVec.ofNat 64 n)
                (n - x64FrameSize ns.toNat - 8 - bound)) ⋆ Rf := by
          dsimp only [x64ScalarFramePreds, x64FramePreds]
          exact sep_cast h1 (by ac_rfl)
        rw [call_reconstruct_frame_region hbd_le hn_bd, hfr1'.2.1, ← hrsp_ret] at h1'
        exact sep_cast h1' (by ac_rfl)
      have hwp_k : wp0 Γ symName rs (pushTup (as := ty0ListToTy bs) rets vs) ls Q X cont
          mRet :=
        hP_cont rets mRet hP
      have htup_k : tupAbiHolds0 st_ret.data true 0 bs rets :=
        (retsIn_ty0_iff hbs7 rets st_ret.data).mp hrets
      have hk_inf := hprog.append.2
      have hlen_eq :
          k + (if cur.lblId = 0 then 0 else 1) +
            (toAmd64Program symName (emitFwd0 (emitLinNode0 cur
              { st0Clean with revDirs := [] }))).length = k_ret := by
        dsimp only [k_ret, k_call]
        rw [hemit_eq, List.length_append, ← Nat.add_assoc]
      rw [hlen_eq] at hk_inf
      have hrun_k := stepLinear_bind_ok_ret (by rw [hnd]; rfl) (by rw [hnd]; rfl) rets
        hlin hnj hng hfuel hns_eq hinv hlen_pw hlen_mw hk_inf hwp_k hm_ret' htup_k hag hgl
        fun k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' mMeta' fuel' s' σ'
          hinv' hpw' hmw' heq_nd hnc' hfuel' hns' hk_inf' hwp_n hfr_n hag_n hgl_n =>
        hih k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' mMeta' fuel' s' σ'
          _ ls mRet hinv' hpw' hmw' (by rw [hnc', hnd]; dsimp only [linK0, nodeCount0]; omega)
          hfuel' hns' hk_inf' hwp_n hfr_n hag_n hgl_n (by rw [heq_nd, hnd, linK0]; exact hc_cont)
      have hst_eta : st_ret = ⟨st_ret.data, st_ret.pc⟩ := by cases st_ret; rfl
      rw [hst_eta, show st_ret.pc = x64ScalarMach.addrOf h k_ret from hpc]
      exact hrun_k
    · refine Eventually.done st_ret ?_
      right
      refine ⟨sym', cs, xs, mRet, hE_exit sym' cs xs mRet hX,
        hdef', hpc', hargs', hsp', ra', n', F ⋆ F_call, hnx, hnbd, hra', ?_⟩
      exact sep_cast hm' (by ac_rfl)

end LeanQbe.T.Bootstrap0
