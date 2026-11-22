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
# Bootstrap Stage B (`Sound0Part11`): Straight-Line & Structured Control-Flow Runners

Proves machine-level `x64ScalarMach.Run` preservation for every remaining straight-line and
structured control-flow instruction in `Rega0`:
1. Leading-label, `defScope` prefix-preservation, and call stack-region reconstruction helpers.
2. Straight-line runners (`let1_run_ok`, `umulw_run_ok`, `load_run_ok`, `store_run_ok`,
   `call_run_ok`).
3. Structured control-flow runners (`jnz_run_ok`, `group_run_ok`).
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

private theorem bindBlockParams0_revDirs :
    ∀ (pts : List Ty0) (venv : List UInt32) (st : RegaSt0) (free : List UInt32) (nxt : UInt32),
      (bindBlockParams0 pts venv st free nxt).st.revDirs = st.revDirs
  | [], _, _, _, _ => rfl
  | _ :: rest, venv, st, free, nxt => by
    dsimp only [bindBlockParams0, bindOneBlockSlot0]
    exact bindBlockParams0_revDirs rest (st.nextVid :: venv) _ _ _

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

/-! ## 3. Structured Control-Flow Runners (`jnz_run_ok`, `group_run_ok`) -/

theorem jnz_run_ok {h : Host} {symName : Sym0 → Sym} {Γ : Env} {ctx : LegalCtx0}
    {fnIdx : UInt32} {fnMaxJump : Nat} {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0}
    {curPre : PreItem0} {pw₂ : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {w₂ : List RegaTask0} {mCur : TaskMeta0} {m₂ : List TaskMeta0}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {rs : List Ty0} {Q : Post (ty0ListToTy rs)} {X : XPost}
    {s0 : MachineData} {ra0 : Int64} {n nX : Nat} {Rf : Mem 64 → Prop} {ns : UInt32}
    {c : Arg0} {t e : TFlat0} {k : Nat} {fuel : UInt32}
    {mCurMem : Mem 64} {s : MachineData} {σ : List (BitVec 64)}
    (hnd : cur.node = .jnz c t e)
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
  have hcur_ok := hinv.items_ok 0 (by simp) (by simp) (by simp)
  dsimp only [List.getElem_cons_zero] at hcur_ok
  obtain ⟨hpn, hpv, hvlen, hvlt, _, _, _, hwf, _, _, _, _, _, hinfo_ok, _, _, _⟩ := hcur_ok
  have hcb : checkArg0 mCur.vT .bool c = true := by rw [hnd] at hwf; cases hwf; assumption
  have hc_ok : ∀ idx, c = .var idx → idx.toNat < cur.venv.length := fun idx he => by
    have hva := wfNode0_nodeArgsInVenv0 hwf; rw [← hvlen, hnd] at hva; exact hva idx he
  have hlive_c : ∀ idx, c = .var idx →
      LiveInTask0 preRes.escaped preSt st curPre cur (listGetU32 cur.venv idx).toNat :=
    fun idx he => taskMetaOk0_args_live hinv (args := [c])
      (fun x hx idx' heq => by
        rw [List.mem_singleton.mp hx] at heq; rw [hnd]; exact nodeArgsUses0_pos_lin_term heq)
      (fun x hx => by rw [List.mem_singleton.mp hx]; exact hc_ok) c List.mem_cons_self idx he
  rw [hnd, wp0_jnz] at hwp
  cases hev : evalArg0Ty vs .bool c with
  | none => rw [hev] at hwp; exact False.elim hwp
  | some cv =>
    rw [hev] at hwp
    have hc_val := argSlotVal64_of_evalArg0Ty hcb hag hev hlive_c
    have hinv1 := regaStep0_jnz hinv hnd
    dsimp only at hinv1
    have hnc_bd := nodeCount0_head_lt_2p31 hinv
    have hnc_eq : nodeCount0 cur.node = 1 + nodeCount0 t + nodeCount0 e := by
      rw [hnd]; dsimp only [nodeCount0]
    have hfuel_pos : 0 < fuel.toNat := by
      rw [List.map_cons] at hfuel; dsimp only [workNodeCount0] at hfuel
      have := nodeCount0_pos cur.node; omega
    have hfuel_sub : (fuel - 1).toNat = fuel.toNat - 1 := u32_sub1_toNat7 hfuel_pos
    have hcnt_ch := regaWorkNodeCount0_children preRes.escaped cur
      (regaPrependLbl0 cur st ctrl) ctrl w₂
    let st0 := regaPrependLbl0 cur st ctrl
    let lsS := regaStep0 preRes.escaped cur st0 ctrl w₂
    let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
    let lsC := regaStep0 preRes.escaped cur st0Clean ctrl []
    have hns_next : (regaRunAux0 (fuel - 1) preRes.escaped lsS.st lsS.ctrl lsS.work).1.maxSlots =
        ns := by
      have hd := regaRunAux0_step_once (fuel := fuel) (esc := preRes.escaped) (st := st)
        (ctrl := ctrl) (cur := cur) (rest := w₂) hfuel_pos
      dsimp only at hd; rwa [← hd]
    have hfuel1 : workNodeCount0 (lsS.work.map RegaTask0.node) ≤ (fuel - 1).toNat := by
      dsimp only [lsS, st0] at hcnt_ch ⊢; omega
    let rd := jnzPrep0 preRes.escaped c cur st0 ctrl
    let rdC := jnzPrep0 preRes.escaped c cur st0Clean ctrl
    let rdZ := jnzPrep0 preRes.escaped c cur { st0Clean with revDirs := [] } ctrl
    let st2 : RegaSt0 := { st0 with remUses := rd.1.remUses, revDirs := rd.2 }
    let ctrl2 : CtrlSt0 :=
      { ctrl with nextLbl := ctrl.nextLbl + 1, lblSlots := ctrl.lblSlots.push [] }
    let tTask := RegaTask0.mk ctrl.nextLbl t cur.venv cur.lenv rd.1.free cur.nextSlot
    let eTask := RegaTask0.mk 0 e cur.venv cur.lenv rd.1.free cur.nextSlot
    let st2C : RegaSt0 := { st0Clean with remUses := rdC.1.remUses, revDirs := rdC.2 }
    let tTaskC := RegaTask0.mk ctrl.nextLbl t cur.venv cur.lenv rdC.1.free cur.nextSlot
    let eTaskC := RegaTask0.mk 0 e cur.venv cur.lenv rdC.1.free cur.nextSlot
    have hlsS_eq : lsS.st = st2 ∧ lsS.ctrl = ctrl2 ∧ lsS.work = eTask :: tTask :: w₂ := by
      dsimp only [lsS, regaStep0]; rw [hnd]; exact ⟨rfl, rfl, rfl⟩
    have hlsC_eq : lsC.st = st2C ∧ lsC.ctrl = ctrl2 ∧ lsC.work = [eTaskC, tTaskC] := by
      dsimp only [lsC, regaStep0]; rw [hnd]; exact ⟨rfl, rfl, rfl⟩
    have hst0_eqs : st0.nextVid = st.nextVid ∧ st0.maxSlots = st.maxSlots ∧
        st0.vslot = st.vslot ∧ st0.remUses = st.remUses := by
      dsimp only [st0, regaPrependLbl0]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
    have hst0C_eqs : st0Clean.nextVid = st.nextVid ∧ st0Clean.maxSlots = st.maxSlots ∧
        st0Clean.vslot = st.vslot ∧ st0Clean.remUses = st.remUses := by
      dsimp only [st0Clean, regaPrependLbl0]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
    have hrd_eq : rd.1 = rdC.1 := by
      dsimp only [rd, rdC, jnzPrep0]
      rw [hst0_eqs.2.2.1, hst0_eqs.2.2.2, hst0C_eqs.2.2.1, hst0C_eqs.2.2.2]
    have htask_eq : eTask = eTaskC ∧ tTask = tTaskC := by
      dsimp only [eTask, eTaskC, tTask, tTaskC]; rw [hrd_eq]; exact ⟨rfl, rfl⟩
    have hst2C_clean : { st2C with revDirs := [] } = { st2 with revDirs := [] } := by
      dsimp only [st2C, st2]; rw [hrd_eq, hst0C_eqs.1, hst0C_eqs.2.1, hst0C_eqs.2.2.1,
        hst0_eqs.1, hst0_eqs.2.1, hst0_eqs.2.2.1]
    have hjnz_acc := jnzPrep0_revDirs preRes.escaped c cur st0Clean ctrl
    have hst2C_rev : st2C.revDirs = rdZ.2 ++ st0Clean.revDirs := by
      dsimp only [st2C]; rw [hjnz_acc.1]
    have hpat_jnz : patchEpilogues0 (x64FrameSizeU0 ns) (emitFwd0 rdZ.2) [] = emitFwd0 rdZ.2 :=
      patchEpilogues0_of_listNoSpZero0 _ (listNoSpZero0_emitFwd0 hjnz_acc.2)
    have hr_pos_f : 0 < (UInt32.ofNat (nodeCount0 cur.node)).toNat := by
      rw [u32_ofNat_toNat_lt10 (by omega), hnc_eq]; omega
    have hr_sub : UInt32.ofNat (nodeCount0 cur.node) - 1 =
        UInt32.ofNat (nodeCount0 t + nodeCount0 e) := by
      apply u32_ext7; rw [u32_sub1_toNat7 hr_pos_f, u32_ofNat_toNat_lt10 (by omega),
        u32_ofNat_toNat_lt10 (by omega), hnc_eq]; omega
    have hstep1 := regaRunAux0_step_once (fuel := UInt32.ofNat (nodeCount0 cur.node))
      (esc := preRes.escaped) (st := { st with revDirs := [] }) (ctrl := ctrl)
      (cur := cur) (rest := []) hr_pos_f
    dsimp only at hstep1
    rw [hlsC_eq.1, hlsC_eq.2.1, hlsC_eq.2.2, hr_sub] at hstep1
    let rE := regaRunAux0 (UInt32.ofNat (nodeCount0 e)) preRes.escaped
      { st2C with revDirs := [] } ctrl2 [eTaskC]
    let rT := regaRunAux0 (UInt32.ofNat (nodeCount0 t)) preRes.escaped
      { rE.1 with revDirs := [] } rE.2 [tTaskC]
    have hsplit_et := regaRunAux0_split_and_fuel (nodeCount0 e)
      (UInt32.ofNat (nodeCount0 t + nodeCount0 e)) (UInt32.ofNat (nodeCount0 e))
      preRes.escaped st2C ctrl2 [eTaskC] [tTaskC]
      (by rw [List.map_singleton]; dsimp only [eTaskC, workNodeCount0]; exact Nat.add_zero _)
      (by rw [u32_ofNat_toNat_lt10 (by omega)]; omega)
      (by rw [u32_ofNat_toNat_lt10 (by omega)]; exact Nat.le_refl _)
    dsimp only at hsplit_et
    have hrev_et := regaRunAux0_revDirs_append (UInt32.ofNat (nodeCount0 e))
      preRes.escaped st2C ctrl2 [eTaskC]
    have hclean_rE_arg : regaRunAux0 (UInt32.ofNat (nodeCount0 e)) preRes.escaped
        { st2C with revDirs := [] } ctrl2 [eTaskC] = rE := rfl
    rw [hclean_rE_arg] at hrev_et
    have hte_nat : (UInt32.ofNat (nodeCount0 t + nodeCount0 e)).toNat =
        nodeCount0 t + nodeCount0 e := u32_ofNat_toNat_lt10 (by rw [hnc_eq] at hnc_bd; omega)
    have hsub_t : UInt32.ofNat ((UInt32.ofNat (nodeCount0 t + nodeCount0 e)).toNat - nodeCount0 e) =
        UInt32.ofNat (nodeCount0 t) := by
      rw [hte_nat]; congr 1; omega
    rw [hrev_et, hsub_t] at hsplit_et
    dsimp only at hsplit_et
    have hrev_t := regaRunAux0_revDirs_append (UInt32.ofNat (nodeCount0 t))
      preRes.escaped { rE.1 with revDirs := rE.1.revDirs ++ st2C.revDirs } rE.2 [tTaskC]
    rw [hrev_t] at hsplit_et
    dsimp only [List.cons_append, List.nil_append] at hsplit_et
    have hclean_rE : { { rE.1 with revDirs := rE.1.revDirs ++ st2C.revDirs } with revDirs := [] } =
        { rE.1 with revDirs := [] } := rfl
    rw [hclean_rE] at hsplit_et
    have hfull_rev :
        (regaRunAux0 (UInt32.ofNat (nodeCount0 cur.node)) preRes.escaped
          { st with revDirs := [] } ctrl [cur]).1.revDirs =
        rT.1.revDirs ++ (rE.1.revDirs ++ (rdZ.2 ++ st0Clean.revDirs)) := by
      rw [hstep1, hsplit_et]; dsimp only [rT]; rw [hst2C_rev]
    rw [hfull_rev, emitFwd0_append, emitFwd0_append, emitFwd0_append,
      patchEpilogues0_append, patchEpilogues0_append, patchEpilogues0_append,
      hpat_jnz, toAmd64Program_append, toAmd64Program_append, toAmd64Program_append] at hcode
    simp only [List.append_assoc] at hcode
    refine regaPrependLbl0_run cur st ctrl (x64FrameSizeU0 ns) _ s
      (fnPost0 h rs Q X s0 ra0 n nX Rf) hu hcode fun _ hprog => ?_
    let k1 := k + (if cur.lblId = 0 then 0 else 1)
    let pJ := toAmd64Program symName (emitFwd0 rdZ.2)
    let pE := toAmd64Program symName
      (patchEpilogues0 (x64FrameSizeU0 ns) (emitFwd0 rE.1.revDirs) [])
    let pT := toAmd64Program symName
      (patchEpilogues0 (x64FrameSizeU0 ns) (emitFwd0 rT.1.revDirs) [])
    have hpJ_inf : pJ.IsInfixAt (x64ScalarMach.prog h) k1 := hprog.append.1
    have hpE_inf : pE.IsInfixAt (x64ScalarMach.prog h) (k1 + pJ.length) :=
      hprog.append.2.append.1
    have hpT_inf : pT.IsInfixAt (x64ScalarMach.prog h) (k1 + pJ.length + pE.length) := by
      dsimp only [k1]
      simpa only [Nat.add_assoc] using hprog.append.2.append.2
    have hvsl_t0 : ({ st0Clean with revDirs := [] } : RegaSt0).vslot = st.vslot :=
      hst0C_eqs.2.2.1
    have hpJ_eq : pJ = toAmd64Program symName
        (emitFwd0 (jnzPrep0 preRes.escaped c cur { st with revDirs := [] } ctrl).2) := by
      dsimp only [pJ, rdZ, jnzPrep0]; rw [hvsl_t0]
    rw [hpJ_eq] at hpJ_inf
    have hnl_ne : ctrl.nextLbl ≠ 0 := fun hz => by
      have := hinv.ctrl_nl.1; simp [hz] at this
    have ht_pos : 0 < (UInt32.ofNat (nodeCount0 t)).toNat := by
      rw [u32_ofNat_toNat_lt10 (by omega)]; exact nodeCount0_pos t
    have hlead_T := regaRunAux0_leading_label (symName := symName) (x64FrameSizeU0 ns)
      preRes.escaped rE.1 rE.2 tTaskC [] (UInt32.ofNat (nodeCount0 t)) ht_pos hnl_ne
    have hinv_e : RegaStepInv0 ctx fnIdx fnMaxJump preRes (nextSc + 2)
        (preNoteNode0 curPre.scope curPre.venv curPre.node preSt)
        (PreItem0.mk e curPre.venv (nextSc + 1) :: PreItem0.mk t curPre.venv nextSc :: pw₂)
        true st2 ctrl2 (eTask :: tTask :: w₂)
        (TaskMeta0.mk mCur.vT mCur.lT mCur.gl none ::
          TaskMeta0.mk mCur.vT mCur.lT mCur.gl none :: m₂) := by
      rw [hlsS_eq.1, hlsS_eq.2.1, hlsS_eq.2.2] at hinv1
      have hpn_j : curPre.node = .jnz c t e := hpn.trans hnd
      simpa [preStepPush0, isTerm0, preStepJnz0, hpn_j] using hinv1
    have hfuel_e : workNodeCount0 ((eTask :: tTask :: w₂).map RegaTask0.node) ≤
        (fuel - 1).toNat := by
      rw [hlsS_eq.2.2] at hfuel1; exact hfuel1
    have hrE_fn : rE.2.fnIdx = ctrl.fnIdx := by
      have hpre := regaRunAux0_step_prefix (nodeCount0 e) (fuel - 1) ctx fnIdx fnMaxJump preRes
        (nextSc + 2) (preNoteNode0 curPre.scope curPre.venv curPre.node preSt)
        [PreItem0.mk e curPre.venv (nextSc + 1)]
        (PreItem0.mk t curPre.venv nextSc :: pw₂) true st2 ctrl2 [eTask] (tTask :: w₂)
        [TaskMeta0.mk mCur.vT mCur.lT mCur.gl none]
        (TaskMeta0.mk mCur.vT mCur.lT mCur.gl none :: m₂)
        (by rw [List.map_singleton]; dsimp only [eTask, workNodeCount0]; exact Nat.add_zero _)
        (by rw [List.map_cons, List.map_cons] at hfuel_e
            dsimp only [workNodeCount0, eTask, tTask] at hfuel_e; omega)
        rfl rfl hinv_e
      dsimp only at hpre
      obtain ⟨_, _, _, hinv_t⟩ := hpre.2.2.2.2.2
      have heq_rE : (regaRunAux0 (UInt32.ofNat (nodeCount0 e)) preRes.escaped
          { st2 with revDirs := [] } ctrl2 [eTask]).2 = rE.2 := by
        dsimp only [rE]; rw [hst2C_clean, htask_eq.1]
      rw [← heq_rE]; exact hinv_t.ctrl_fn.trans hinv.ctrl_fn.symm
    rw [hrE_fn] at hlead_T
    have hlbl_adr := infix_labelAddr_eq hu hpT_inf hlead_T
    refine jnzPrep0_spec (symName := symName) (h := h) (k := k1)
      (j := k1 + pJ.length + pE.length) (post := fnPost0 h rs Q X s0 ra0 n nX Rf)
      preRes.escaped c cur st ctrl hc_val (fnFrameInv0_mem_slots hfr) hlbl_adr hpJ_inf
      fun s' hfr' hm' => ?_
    have hfr_s' : FnFrameInv0 ns s0 ra0 n Rf mCurMem s' σ :=
      fnFrameInv0_weaken_scratchAndAbi hfr hfr' hm'
    have hlen_j_eq : k1 + (toAmd64Program symName (emitFwd0
        (jnzPrep0 preRes.escaped c cur { st with revDirs := [] } ctrl).2)).length =
        k1 + pJ.length := by rw [← hpJ_eq]
    have hst2_eq_nv : st2.nextVid = st.nextVid := hst0_eqs.1
    have hst2_eq_vsl : st2.vslot = st.vslot := hst0_eqs.2.2.1
    have hpres_t : preSt.nextVid =
        (preNoteNode0 curPre.scope curPre.venv curPre.node preSt).nextVid :=
      (preNoteNode0_defScope ..).2.symm
    have hds_t : preSt.defScope =
        (preNoteNode0 curPre.scope curPre.venv curPre.node preSt).defScope :=
      (preNoteNode0_defScope ..).1.symm
    have hsc1 : (nextSc + 1).toNat = nextSc.toNat + 1 := by
      have h := hinv.pre_inv.nextSc_bound
      rw [List.map_cons, hpn, hnd] at h; dsimp only [workNodeCount0, nodeCount0] at h
      exact u32_add1_toNat7 (by omega)
    refine ⟨fun ht => ?_, fun hf => ?_⟩
    · have hp_e_pre := regaRunAux0_step_prefix_ds (N := nodeCount0 e) (fuel := fuel - 1)
        (ctx := ctx) (fnIdx := fnIdx) (fnMaxJump := fnMaxJump) (preRes := preRes)
        (nextSc := nextSc + 2) (preSt := preNoteNode0 curPre.scope curPre.venv curPre.node preSt)
        (pw₁ := [PreItem0.mk e curPre.venv (nextSc + 1)])
        (pw₂ := PreItem0.mk t curPre.venv nextSc :: pw₂)
        (seenJnz := true) (st := st2) (ctrl := ctrl2) (w₁ := [eTask]) (w₂ := tTask :: w₂)
        (m₁ := [TaskMeta0.mk mCur.vT mCur.lT mCur.gl none])
        (m₂ := TaskMeta0.mk mCur.vT mCur.lT mCur.gl none :: m₂)
        (by rw [List.map_singleton]; dsimp only [eTask, workNodeCount0]; exact Nat.add_zero _)
        (by rw [List.map_cons, List.map_cons] at hfuel_e
            dsimp only [workNodeCount0, eTask, tTask] at hfuel_e; omega)
        rfl rfl hinv_e
      dsimp only at hp_e_pre
      obtain ⟨rE_eq, _, hrE_ms, _, hrE_vsl, seenJnz'', nextSc'', preSt'', hinv_t, _, hds_t_e⟩ :=
        hp_e_pre
      have hrE_st_eq : (regaRunAux0 (UInt32.ofNat (nodeCount0 e)) preRes.escaped
          { st2 with revDirs := [] } ctrl2 [eTask]) = rE := by
        dsimp only [rE]; rw [hst2C_clean, htask_eq.1]
      let st_t := { rE.1 with revDirs := rE.1.revDirs ++ st2.revDirs }
      have hinv_t' : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc'' preSt''
          (PreItem0.mk t curPre.venv nextSc :: pw₂) seenJnz'' st_t rE.2 (tTask :: w₂)
          (TaskMeta0.mk mCur.vT mCur.lT mCur.gl none :: m₂) := by
        simpa only [hrE_st_eq] using hinv_t
      have hns_t :
          (regaRunAux0 (UInt32.ofNat ((fuel - 1).toNat - nodeCount0 e)) preRes.escaped
            st_t rE.2 (tTask :: w₂)).1.maxSlots = ns := by
        have hm := congrArg (fun p => p.1.maxSlots) rE_eq
        rw [hrE_st_eq] at hm
        rw [← hm]; dsimp only [List.cons_append, List.nil_append]
        rw [← hlsS_eq.1, ← hlsS_eq.2.1, ← hlsS_eq.2.2]
        exact hns_next
      have hfuel_t : workNodeCount0 ((tTask :: w₂).map RegaTask0.node) ≤
          (UInt32.ofNat ((fuel - 1).toNat - nodeCount0 e)).toNat := by
        have hm : workNodeCount0 (lsS.work.map RegaTask0.node) + 1 =
            workNodeCount0 ((cur :: w₂).map RegaTask0.node) := hcnt_ch
        have hf0 := hfuel
        rw [hlsS_eq.2.2] at hm
        rw [List.map_cons] at hm hf0 ⊢
        rw [List.map_cons] at hm
        dsimp only [workNodeCount0, eTask, tTask] at hm hf0 ⊢
        have hflt := UInt32.toNat_lt (fuel - 1)
        rw [u32_ofNat_toNat_lt10 (by omega)]; omega
      have hinf_t' : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
          (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 tTask.node)) preRes.escaped
            { st_t with revDirs := [] } rE.2 [tTask]).1.revDirs) [])).IsInfixAt
          (x64ScalarMach.prog h) (k1 + pJ.length + pE.length) := by
        dsimp only [pT, rT] at hpT_inf
        rw [← htask_eq.2] at hpT_inf
        dsimp only [tTask] at hpT_inf ⊢
        exact hpT_inf
      have hag_t : SlotsAgree0 preRes.escaped preSt'' st_t ⟨t, curPre.venv, nextSc⟩ tTask
          mCur.vT vs σ := by
        refine ⟨hpv ▸ hag.1, hag.2.1, fun idx hi hlv => ?_⟩
        have hvid_lt : (tTask.venv[idx]'hi).toNat < st.nextVid.toNat :=
          hvlt _ (List.getElem_mem hi)
        have hlv_old : LiveInTask0 preRes.escaped preSt st curPre cur
            (tTask.venv[idx]'hi).toNat := by
          rcases hlv with ⟨hes, hm⟩ | ⟨_, hsc, _⟩
          · exact Or.inl ⟨hes, hm⟩
          · exfalso
            have hdl := hinv.pre_inv.defScope_lt (tTask.venv[idx]'hi).toNat
              (hinv.st_nv ▸ hvid_lt)
            have hds_pre : preSt''.defScope.getD (tTask.venv[idx]'hi).toNat 0 =
                preSt.defScope.getD (tTask.venv[idx]'hi).toNat 0 := by
              rw [hds_t_e _ (by rw [← hpres_t, ← hinv.st_nv]; exact hvid_lt), ← hds_t]
            rw [hds_pre] at hsc; dsimp only at hsc; omega
        have hvsl_t : arrGetU0 st_t.vslot (tTask.venv[idx]'hi) =
            arrGetU0 st.vslot (cur.venv[idx]'hi) := by
          have h1 := hrE_vsl (cur.venv[idx]'hi).toNat (hst2_eq_nv ▸ hvid_lt)
          rw [hrE_st_eq] at h1
          rw [UInt32.ofNat_toNat] at h1
          exact h1.trans (congrArg (fun a => arrGetU0 a _) hst2_eq_vsl)
        obtain ⟨hsl, hvs, ht', hc⟩ := hag.2.2 idx hi hlv_old
        rw [hvsl_t]
        exact ⟨hsl, hvs, ht', hc⟩
      have hgl_t : GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
          preRes.escaped st_t tTask (TaskMeta0.mk mCur.vT mCur.lT mCur.gl none) vs fnIdx
          mCur.gl ls := by
        refine glEntrySem0_eq_vslot_nextSlot hgl (Nat.le_refl _) rfl rfl fun info hi => ?_
        obtain ⟨_, _, _, _, _, hnv_o, _, _, _, _, hov_lt, _⟩ := hinfo_ok info hi
        refine ⟨st.nextVid.toNat, fun w hw => Nat.lt_of_lt_of_le (hov_lt w hw)
          (Nat.le_trans (Nat.le_add_right _ _) hnv_o), fun v hv => ?_⟩
        have h1 := hrE_vsl v (hst2_eq_nv ▸ hv)
        rw [hrE_st_eq] at h1
        exact h1.trans (congrArg (fun a => arrGetU0 a (UInt32.ofNat v)) hst2_eq_vsl)
      exact hih (k1 + pJ.length + pE.length) nextSc'' preSt'' ⟨t, curPre.venv, nextSc⟩ pw₂
        seenJnz'' st_t rE.2 tTask w₂
        (TaskMeta0.mk mCur.vT mCur.lT mCur.gl none) m₂
        (UInt32.ofNat ((fuel - 1).toNat - nodeCount0 e)) s' σ vs ls mCurMem
        hinv_t' (by simp [hlen_pw]) (by simp [hlen_mw])
        (by dsimp only [tTask]; rw [hnc_eq]; have := nodeCount0_pos e; omega)
        hfuel_t hns_t hinf_t' (hwp.1 ht) hfr_s' hag_t hgl_t
        (by rw [hnd] at hc_node; dsimp only [NodeContracts0] at hc_node; exact hc_node.1)
    · rw [hlen_j_eq]
      have hns_e : (regaRunAux0 (fuel - 1) preRes.escaped st2 ctrl2
          (eTask :: tTask :: w₂)).1.maxSlots = ns := by
        rw [← hlsS_eq.1, ← hlsS_eq.2.1, ← hlsS_eq.2.2]; exact hns_next
      have hinf_e' : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
          (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 eTask.node)) preRes.escaped
            { st2 with revDirs := [] } ctrl2 [eTask]).1.revDirs) [])).IsInfixAt
          (x64ScalarMach.prog h) (k1 + pJ.length) := by
        dsimp only [pE, rE] at hpE_inf
        rw [hst2C_clean, ← htask_eq.1] at hpE_inf
        dsimp only [eTask] at hpE_inf ⊢
        exact hpE_inf
      have hag_e : SlotsAgree0 preRes.escaped
          (preNoteNode0 curPre.scope curPre.venv curPre.node preSt) st2
          ⟨e, curPre.venv, nextSc + 1⟩ eTask mCur.vT vs σ := by
        refine ⟨hpv ▸ hag.1, hag.2.1, fun idx hi hlv => ?_⟩
        have hvid_lt : (eTask.venv[idx]'hi).toNat < st.nextVid.toNat :=
          hvlt _ (List.getElem_mem hi)
        have hlv_old : LiveInTask0 preRes.escaped preSt st curPre cur
            (eTask.venv[idx]'hi).toNat := by
          rcases hlv with ⟨hes, hm⟩ | ⟨_, hsc, _⟩
          · exact Or.inl ⟨hes, hm⟩
          · exfalso
            have hdl := hinv.pre_inv.defScope_lt (eTask.venv[idx]'hi).toNat
              (hinv.st_nv ▸ hvid_lt)
            rw [← hds_t] at hsc; dsimp only at hsc; rw [hsc1] at hsc; omega
        obtain ⟨hsl, hvs, ht', hc⟩ := hag.2.2 idx hi hlv_old
        rw [hst2_eq_vsl]
        exact ⟨hsl, hvs, ht', hc⟩
      have hgl_e : GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
          preRes.escaped st2 eTask (TaskMeta0.mk mCur.vT mCur.lT mCur.gl none) vs fnIdx
          mCur.gl ls :=
        glEntrySem0_eq_vslot_nextSlot hgl (Nat.le_refl _) rfl rfl fun info hi =>
          ⟨st.nextVid.toNat, fun w hw => by
            obtain ⟨_, _, _, _, _, hnv_o, _, _, _, _, hov_lt, _⟩ := hinfo_ok info hi
            exact Nat.lt_of_lt_of_le (hov_lt w hw) (Nat.le_trans (Nat.le_add_right _ _) hnv_o),
            fun v _ => by rw [hst2_eq_vsl]⟩
      exact hih (k1 + pJ.length) (nextSc + 2)
        (preNoteNode0 curPre.scope curPre.venv curPre.node preSt)
        ⟨e, curPre.venv, nextSc + 1⟩ (PreItem0.mk t curPre.venv nextSc :: pw₂)
        true st2 ctrl2 eTask (tTask :: w₂)
        (TaskMeta0.mk mCur.vT mCur.lT mCur.gl none)
        (TaskMeta0.mk mCur.vT mCur.lT mCur.gl none :: m₂) (fuel - 1) s' σ vs ls mCurMem
        hinv_e (by simp [hlen_pw]) (by simp [hlen_mw])
        (by dsimp only [eTask]; rw [hnc_eq]; have := nodeCount0_pos t; omega)
        hfuel_e hns_e hinf_e' (hwp.2 hf) hfr_s' hag_e hgl_e
        (by rw [hnd] at hc_node; dsimp only [NodeContracts0] at hc_node; exact hc_node.2)

private theorem bindBlockParams0_clean_eq :
    ∀ (pts : List Ty0) (venv : List UInt32) (stA stB : RegaSt0) (free : List UInt32)
      (nxt : UInt32),
      stA.nextVid = stB.nextVid → stA.maxSlots = stB.maxSlots →
      stA.vslot = stB.vslot → stA.remUses = stB.remUses →
      let bbA := bindBlockParams0 pts venv stA free nxt
      let bbB := bindBlockParams0 pts venv stB free nxt
      bbA.venv = bbB.venv ∧ bbA.free = bbB.free ∧ bbA.nxt = bbB.nxt ∧
      bbA.st.nextVid = bbB.st.nextVid ∧ bbA.st.maxSlots = bbB.st.maxSlots ∧
      bbA.st.vslot = bbB.st.vslot ∧ bbA.st.remUses = bbB.st.remUses ∧
      ({ bbA.st with revDirs := [] } : RegaSt0) = { bbB.st with revDirs := [] }
  | [], _, stA, stB, _, _, hnv, hms, hvsl, hrem => by
    have hcl : ({ stA with revDirs := [] } : RegaSt0) = { stB with revDirs := [] } := by
      cases stA; cases stB; simp_all
    exact ⟨rfl, rfl, rfl, hnv, hms, hvsl, hrem, hcl⟩
  | _ :: rest, venv, stA, stB, free, nxt, hnv, hms, hvsl, hrem => by
    dsimp only [bindBlockParams0, bindOneBlockSlot0]
    have hsp : allocSlot0 free nxt stA.maxSlots = allocSlot0 free nxt stB.maxSlots := by
      rw [hms]
    have hvid : stA.nextVid = stB.nextVid := hnv
    rw [hsp, hvid, hvsl, hrem]
    exact bindBlockParams0_clean_eq rest (stB.nextVid :: venv) _ _ _ _ rfl rfl rfl rfl

private theorem pushTup_drop_aux11 :
    ∀ {tys : List Ty} (xs : Tup Val tys) (vs : List ((t : Ty) × Val t)),
      (pushTup xs vs).drop tys.length = vs
  | [], xs, vs => by cases xs; rfl
  | t :: _, xs, vs => by
    rcases xs with ⟨x, rest⟩
    dsimp only [pushTup, List.length_cons]
    have h := pushTup_drop_aux11 rest (⟨t, x⟩ :: vs)
    rw [← List.drop_drop, h, List.drop_one, List.tail_cons]

private theorem pushTup_drop11 {ts : List Ty0} (xs : Tup Val (ty0ListToTy ts))
    (vs : List ((t : Ty) × Val t)) :
    (pushTup xs vs).drop ts.length = vs := by
  have h : (ty0ListToTy ts).length = ts.length := List.length_map ..
  exact h ▸ pushTup_drop_aux11 xs vs

private theorem pushAgree0_of_list (esc remUses vslot : Array Nat) (σ : List (BitVec 64)) :
    ∀ (ts : List Ty0) (ss : List UInt32) (nv : UInt32) (xs : Tup Val (ty0ListToTy ts)),
      nv.toNat + ts.length < 2 ^ 31 → ss.length = ts.length →
      (∀ k (hk : k < ss.length), ss[k]'hk = arrGetU0 vslot (nv + UInt32.ofNat k)) →
      TupInSlots0 σ ss ts xs → PushAgree0 esc remUses vslot nv ts xs σ
  | [], [], _, (), _, _, _, _ => trivial
  | [], _ :: _, _, (), _, hlen, _, _ => by simp at hlen
  | _ :: _, [], _, _, _, hlen, _, _ => by simp at hlen
  | t :: rest, s :: sr, nv, (x, rx), hnv, hlen, hss, ⟨⟨hsl, heq⟩, htr⟩ => by
    simp only [List.length_cons] at hnv
    have hs0 := hss 0 (Nat.zero_lt_succ _)
    simp only [List.getElem_cons_zero] at hs0
    have hnv0 : nv + UInt32.ofNat 0 = nv := by
      apply u32_ext7; rw [u32_add_ofNat_lt7 (by omega), Nat.add_zero]
    rw [hnv0] at hs0
    have hpa_tail : PushAgree0 esc remUses vslot (nv + 1) rest rx σ := by
      refine pushAgree0_of_list esc remUses vslot σ rest sr (nv + 1) rx
        (by rw [u32_add1_toNat7 (by omega)]; omega) (Nat.succ.inj hlen) (fun k hk => ?_) htr
      have hk1 := hss (k + 1) (Nat.succ_lt_succ hk)
      simp only [List.getElem_cons_succ] at hk1
      have hnv_eq : nv + UInt32.ofNat (k + 1) = (nv + 1) + UInt32.ofNat k := by
        apply u32_ext7
        rw [UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_one,
          u32_toNat_ofNat7, u32_toNat_ofNat7, Nat.mod_add_mod, Nat.add_mod_mod,
          Nat.add_mod_mod, Nat.add_assoc, Nat.add_comm k 1]
      rwa [hnv_eq] at hk1
    exact ⟨fun _ => ⟨hs0 ▸ hsl, by
      have h1 : σ[(arrGetU0 vslot nv).toNat]'(hs0 ▸ hsl) = σ[s.toNat]'hsl :=
        list_getElem_eq9 σ (hs0 ▸ hsl) hsl (congrArg UInt32.toNat hs0.symm)
      exact h1.trans heq⟩, hpa_tail⟩

theorem group_run_ok {h : Host} {symName : Sym0 → Sym} {Γ : Env} {ctx : LegalCtx0}
    {fnIdx : UInt32} {fnMaxJump : Nat} {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0}
    {curPre : PreItem0} {pw₂ : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {w₂ : List RegaTask0} {mCur : TaskMeta0} {m₂ : List TaskMeta0}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {rs : List Ty0} {Q : Post (ty0ListToTy rs)} {X : XPost}
    {s0 : MachineData} {ra0 : Int64} {n nX : Nat} {Rf : Mem 64 → Prop} {ns : UInt32}
    {bodies : List (List Ty0 × TFlat0)} {cont : TFlat0} {k : Nat} {fuel : UInt32}
    {mCurMem : Mem 64} {s : MachineData} {σ : List (BitVec 64)}
    (hnd : cur.node = .group bodies cont)
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
  have hcur_ok := hinv.items_ok 0 (by simp) (by simp) (by simp)
  dsimp only [List.getElem_cons_zero] at hcur_ok
  obtain ⟨hpn, hpv, hvlen, hvlt, hllen, hgl_len, hgi, hwf, hfit, hsbg, hnb, hpool, hnxt_nv,
    hinfo_ok, hwait, _, hlive⟩ := hcur_ok
  rw [hnd] at hwf hfit hsbg hnb
  obtain ⟨hwfk, hfitk, hsbgk, hnbk, hcases⟩ := wfNode0_group_single_inv hwf hfit hsbg hnb
  rw [hnd] at hc_node; dsimp only [NodeContracts0] at hc_node
  obtain ⟨hc_bs, hc_k⟩ := hc_node
  obtain ⟨headMeta, hinv1⟩ := regaStep0_group hinv hnd
  have hnc_bd := nodeCount0_head_lt_2p31 hinv
  have hfuel_pos : 0 < fuel.toNat := by
    rw [List.map_cons] at hfuel; dsimp only [workNodeCount0] at hfuel
    have := nodeCount0_pos cur.node; omega
  have hfuel_sub : (fuel - 1).toNat = fuel.toNat - 1 := u32_sub1_toNat7 hfuel_pos
  have hcnt_ch := regaWorkNodeCount0_children preRes.escaped cur
    (regaPrependLbl0 cur st ctrl) ctrl w₂
  let st0 := regaPrependLbl0 cur st ctrl
  let lsS := regaStep0 preRes.escaped cur st0 ctrl w₂
  let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
  let lsC := regaStep0 preRes.escaped cur st0Clean ctrl []
  have hns_next : (regaRunAux0 (fuel - 1) preRes.escaped lsS.st lsS.ctrl lsS.work).1.maxSlots =
      ns := by
    have hd := regaRunAux0_step_once (fuel := fuel) (esc := preRes.escaped) (st := st)
      (ctrl := ctrl) (cur := cur) (rest := w₂) hfuel_pos
    dsimp only at hd; rwa [← hd]
  have hfuel1 : workNodeCount0 (lsS.work.map RegaTask0.node) ≤ (fuel - 1).toNat := by
    dsimp only [lsS, st0] at hcnt_ch ⊢; omega
  have hst0_eqs : st0.nextVid = st.nextVid ∧ st0.maxSlots = st.maxSlots ∧
      st0.vslot = st.vslot ∧ st0.remUses = st.remUses := by
    dsimp only [st0, regaPrependLbl0]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have hst0C_eqs : st0Clean.nextVid = st.nextVid ∧ st0Clean.maxSlots = st.maxSlots ∧
      st0Clean.vslot = st.vslot ∧ st0Clean.remUses = st.remUses := by
    dsimp only [st0Clean, regaPrependLbl0]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have hpn_g : curPre.node = .group bodies cont := hpn.trans hnd
  have hrest_scopes : ∀ p ∈ pw₂, p.scope ≠ curPre.scope := by
    have hnd_sc := hinv.pre_inv.scopes_nodup
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd_sc
    exact hnd_sc.1
  have hctrl_sz : ctrl.lblSlots.size = ctrl.nextLbl.toNat := hinv.seenJnz_ctrl
  rw [hnd, wp0_group] at hwp
  rcases hcases with rfl | ⟨pts, b, rfl, hpts_lt, hwfb, hfitb, hsbgb, hnbb⟩
  · have hnc_eq : nodeCount0 cur.node = 1 + nodeCount0 cont := by
      rw [hnd]; dsimp only [nodeCount0, blocksNodeCount0]
    change ∀ Js : Tup Cont [],
      closed0 Γ symName rs vs (pushConts0 [] Js ls) Q X [] Js →
      wp0 Γ symName rs vs (pushConts0 [] Js ls) Q X cont mCurMem at hwp
    have hwp_k : wp0 Γ symName rs vs ls Q X cont mCurMem :=
      hwp () (by rw [closed0_nil]; trivial)
    let pK_item := PreItem0.mk cont curPre.venv nextSc
    let tK := RegaTask0.mk 0 cont cur.venv cur.lenv cur.freeSlots cur.nextSlot
    let mK := TaskMeta0.mk mCur.vT mCur.lT mCur.gl none
    have hlsS_eq : lsS.st = st0 ∧ lsS.ctrl = ctrl ∧ lsS.work = tK :: w₂ := by
      dsimp only [lsS, regaStep0]; rw [hnd]; exact ⟨rfl, rfl, rfl⟩
    have hlsC_eq : lsC.st = st0Clean ∧ lsC.ctrl = ctrl ∧ lsC.work = [tK] := by
      dsimp only [lsC, regaStep0]; rw [hnd]; exact ⟨rfl, rfl, rfl⟩
    have hr_pos_f : 0 < (UInt32.ofNat (nodeCount0 cur.node)).toNat := by
      rw [u32_ofNat_toNat_lt10 (by omega), hnc_eq]; omega
    have hr_sub : UInt32.ofNat (nodeCount0 cur.node) - 1 = UInt32.ofNat (nodeCount0 cont) := by
      apply u32_ext7; rw [u32_sub1_toNat7 hr_pos_f, u32_ofNat_toNat_lt10 (by omega),
        u32_ofNat_toNat_lt10 (by omega), hnc_eq]; omega
    have hstep1 := regaRunAux0_step_once (fuel := UInt32.ofNat (nodeCount0 cur.node))
      (esc := preRes.escaped) (st := { st with revDirs := [] }) (ctrl := ctrl)
      (cur := cur) (rest := []) hr_pos_f
    dsimp only at hstep1
    rw [hlsC_eq.1, hlsC_eq.2.1, hlsC_eq.2.2, hr_sub] at hstep1
    have hrev_k := regaRunAux0_revDirs_append (UInt32.ofNat (nodeCount0 cont))
      preRes.escaped st0Clean ctrl [tK]
    let rK := regaRunAux0 (UInt32.ofNat (nodeCount0 cont)) preRes.escaped
      { st0Clean with revDirs := [] } ctrl [tK]
    rw [hrev_k] at hstep1
    have hstep_rev :
        (regaRunAux0 (UInt32.ofNat (nodeCount0 cur.node)) preRes.escaped
          { st with revDirs := [] } ctrl [cur]).1.revDirs =
        rK.1.revDirs ++ st0Clean.revDirs := by rw [hstep1]
    rw [hstep_rev, emitFwd0_append, patchEpilogues0_append, toAmd64Program_append] at hcode
    refine regaPrependLbl0_run cur st ctrl (x64FrameSizeU0 ns) _ s
      (fnPost0 h rs Q X s0 ra0 n nX Rf) hu hcode fun _ hprog => ?_
    have hout_eq : preStepPush0 curPre (preNoteNode0 curPre.scope curPre.venv curPre.node preSt)
        nextSc pw₂ = PreOut0.mk preSt (nextSc + 1) (pK_item :: pw₂) := by
      dsimp only [preStepPush0, preNoteNode0]; rw [hpn_g]
      simp only [isTerm0, Bool.false_eq_true, ↓reduceIte]
      dsimp only [preStepGroup0, preEnqueueGroup0, prePushGroup0, pK_item]
    rw [hout_eq, hlsS_eq.1, hlsS_eq.2.1, hlsS_eq.2.2] at hinv1
    obtain ⟨hm0, rfl⟩ : ∃ hm0, headMeta = [hm0] := by
      have hmw1 := hinv1.len_mw
      rw [List.length_append, hlen_mw] at hmw1
      cases headMeta with
      | nil => simp only [List.length_nil, List.length_cons] at hmw1; omega
      | cons a tl => cases tl with
        | nil => exact ⟨a, rfl⟩
        | cons _ _ => simp only [List.length_cons] at hmw1; omega
    have hlive_k : ∀ v < st.nextVid.toNat,
        LiveInTask0 preRes.escaped preSt st0 pK_item tK v →
        preRes.escaped.getD v 0 = 1 ∧ UInt32.ofNat v ∈ cur.venv := by
      intro v hv hlv
      rcases hlv with ⟨hes, hvmem⟩ | ⟨_, hsc_v, _⟩
      · exact ⟨hes, hvmem⟩
      · have := hinv.pre_inv.defScope_lt v (hinv.st_nv ▸ hv); dsimp only [pK_item] at hsc_v; omega
    have hinv_k : RegaStepInv0 ctx fnIdx fnMaxJump preRes (nextSc + 1) preSt
        (pK_item :: pw₂) false st0 ctrl (tK :: w₂) (mK :: m₂) :=
      { preRes_nv := hinv1.preRes_nv
        preRes_ds_sz := hinv1.preRes_ds_sz
        preRes_us_sz := hinv1.preRes_us_sz
        preRes_es_sz := hinv1.preRes_es_sz
        preRes_es_bit := hinv1.preRes_es_bit
        preRes_us_bd := hinv1.preRes_us_bd
        maxBd_lt := hinv1.maxBd_lt
        pre_inv := hinv1.pre_inv
        pre_run := hinv1.pre_run
        len_pw := hinv1.len_pw
        len_mw := by simp only [List.length_cons, hlen_mw]
        seenJnz_safe := hinv1.seenJnz_safe
        seenJnz_ctrl := hinv1.seenJnz_ctrl
        maxJump_bd := hinv1.maxJump_bd
        ctrl_fn := hinv1.ctrl_fn
        ctrl_nl := hinv1.ctrl_nl
        st_nv := hinv1.st_nv
        st_vslot_sz := hinv1.st_vslot_sz
        st_rem_sz := hinv1.st_rem_sz
        st_maxSl_le := hinv1.st_maxSl_le
        st_rem_le := hinv1.st_rem_le
        st_rem_future := hinv1.st_rem_future
        st_rem_active := hinv1.st_rem_active
        items_ok := fun i hi1 hi2 hi3 => by
          cases i with
          | zero =>
            dsimp only [List.getElem_cons_zero, pK_item, tK, mK]
            refine ⟨rfl, hpv, hvlen, fun v hv => by rw [hst0_eqs.1]; exact hvlt v hv,
              hllen, hgl_len, hgi, by dsimp only [legalAddSigs0] at hwfk; exact hwfk,
              hfitk, hsbgk, hnbk,
              by rw [hst0_eqs.2.1]; exact hpool, by rw [hst0_eqs.1]; exact hnxt_nv,
              fun info hi => lblInfoOk0_mono (hinfo_ok info hi) (Nat.le_refl _)
                (fun _ _ _ => rfl) (by rw [hst0_eqs.1]; exact Nat.le_refl _)
                (by rw [hst0_eqs.2.1]; exact Nat.le_refl _) (fun _ _ => by rw [hst0_eqs.2.2.1]),
              fun info hi hw => ⟨(hwait info hi hw).1, fun v hv hlv => by
                have hv' : v < st.nextVid.toNat := by rwa [hst0_eqs.1] at hv
                obtain ⟨hes, hvmem⟩ := hlive_k v hv' hlv
                rw [hst0_eqs.2.2.1]; exact (hwait info hi hw).2 v hv' (Or.inl ⟨hes, hvmem⟩)⟩,
              trivial, fun v hv hlv => by
                have hv' : v < st.nextVid.toNat := by rwa [hst0_eqs.1] at hv
                obtain ⟨hes, hvmem⟩ := hlive_k v hv' hlv
                rw [hst0_eqs.2.2.1]
                have hlv_c := hlive v hv' (Or.inl ⟨hes, hvmem⟩)
                refine ⟨hlv_c.1, hlv_c.2.1, fun w hw hne hlw => ?_⟩
                have hw' : w < st.nextVid.toNat := by rwa [hst0_eqs.1] at hw
                obtain ⟨hesw, hwmemw⟩ := hlive_k w hw' hlw
                exact hlv_c.2.2 w hw' hne (Or.inl ⟨hesw, hwmemw⟩)⟩
          | succ j' =>
            exact hinv1.items_ok (j' + 1) hi1 hi2 (by simp at hi3 ⊢; omega)
        later_live := fun i j hi1 hi2 hi3 hj1 hj2 hij w hw hlive_j => by
          cases i with
          | zero =>
            obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
            have hj'_lt : j' < pw₂.length := by simp only [List.length_cons] at hj1; omega
            have hj2'_lt : j' < w₂.length := by simp only [List.length_cons] at hj2; omega
            have hj1_s : j' + 1 < (curPre :: pw₂).length := by simp only [List.length_cons]; omega
            have hj2_s : j' + 1 < (cur :: w₂).length := by simp only [List.length_cons]; omega
            rw [hst0_eqs.1] at hw
            dsimp only [List.getElem_cons_succ, List.getElem_cons_zero] at hlive_j ⊢
            have hj_old : LiveInTask0 preRes.escaped preSt st (pw₂[j']'hj'_lt)
                (w₂[j']'hj2'_lt) w := by simpa only [LiveInTask0, hst0_eqs.2.2.2] using hlive_j
            have hcov := hinv.later_live 0 (j' + 1) (by simp) (by simp) (by simp)
              hj1_s hj2_s (Nat.zero_lt_succ j') w hw hj_old
            rcases hcov with hl0 | ⟨info, hm, hwt, hsl⟩
            · rcases hl0 with ⟨hes, hvmem⟩ | ⟨hes, hsc, _⟩
              · exact Or.inl (Or.inl ⟨hes, hvmem⟩)
              · exfalso
                dsimp only [List.getElem_cons_zero] at hsc
                rcases hj_old with ⟨hes1, _⟩ | ⟨_, hsc_j, _⟩
                · rw [hes] at hes1; cases hes1
                · exact hrest_scopes (pw₂[j']'hj'_lt) (List.getElem_mem hj'_lt)
                    (u32_ext7 (hsc_j.trans hsc.symm))
            · right; refine ⟨info, hm, hwt, ?_⟩; rw [hst0_eqs.2.2.1]; exact hsl
          | succ i' =>
            exact hinv1.later_live (i' + 1) j hi1 hi2 (by simp at hi3 ⊢; omega) hj1 hj2 hij w hw
              hlive_j }
    have hinf_k : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
        (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 tK.node)) preRes.escaped
          { st0 with revDirs := [] } ctrl [tK]).1.revDirs) [])).IsInfixAt
        (x64ScalarMach.prog h) (k + (if cur.lblId = 0 then 0 else 1)) := by
      have hst0_eq : { st0 with revDirs := [] } = { st0Clean with revDirs := [] } := by
        dsimp only [st0, st0Clean, regaPrependLbl0]; split <;> rfl
      dsimp only [tK]; rw [hst0_eq]; exact hprog
    have hag_k : SlotsAgree0 preRes.escaped preSt st0 pK_item tK mK.vT vs σ := by
      refine ⟨hag.1, hag.2.1, fun idx hi hlv => ?_⟩
      have hvid_lt : (tK.venv[idx]'hi).toNat < st.nextVid.toNat := hvlt _ (List.getElem_mem hi)
      obtain ⟨hes, hvmem⟩ := hlive_k _ hvid_lt (by simpa [UInt32.ofNat_toNat] using hlv)
      obtain ⟨hsl, hvs, ht', hc⟩ := hag.2.2 idx hi (Or.inl ⟨hes, hvmem⟩)
      rw [hst0_eqs.2.2.1]; exact ⟨hsl, hvs, ht', hc⟩
    have hgl_k : GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
        preRes.escaped st0 tK mK vs fnIdx mK.gl ls :=
      glEntrySem0_eq_vslot_nextSlot hgl (Nat.le_refl _) rfl rfl fun info hi =>
        ⟨st.nextVid.toNat, fun w hw => by
          obtain ⟨_, _, _, _, _, hnv_o, _, _, _, _, hov_lt, _⟩ := hinfo_ok info hi
          exact Nat.lt_of_lt_of_le (hov_lt w hw) (Nat.le_trans (Nat.le_add_right _ _) hnv_o),
          fun v _ => by rw [hst0_eqs.2.2.1]⟩
    exact hih (k + (if cur.lblId = 0 then 0 else 1)) (nextSc + 1) preSt pK_item pw₂ false st0 ctrl
      tK w₂ mK m₂ (fuel - 1) s σ vs ls mCurMem hinv_k hlen_pw hlen_mw
      (by dsimp only [tK]; rw [hnc_eq]; omega)
      (by rw [← hlsS_eq.2.2]; exact hfuel1)
      (by rw [← hlsS_eq.1, ← hlsS_eq.2.1, ← hlsS_eq.2.2]; exact hns_next)
      hinf_k hwp_k hfr hag_k hgl_k hc_k
  · have hnc_eq : nodeCount0 cur.node = 1 + nodeCount0 b + nodeCount0 cont := by
      rw [hnd]; dsimp only [nodeCount0, blocksNodeCount0]; omega
    have hsc1 : (nextSc + 1).toNat = nextSc.toNat + 1 := by
      have h := hinv.pre_inv.nextSc_bound
      rw [List.map_cons, hpn_g] at h; dsimp only [workNodeCount0, nodeCount0, blocksNodeCount0] at h
      exact u32_add1_toNat7 (by omega)
    have hlen_pts : (tyLenU0 pts 0).toNat = pts.length := tyLenU0_eq_of_lt hpts_lt
    have hnv_b : preSt.nextVid.toNat + pts.length < 2 ^ 32 := by
      have := hinv.pre_inv.nextVid_bound
      rw [List.map_cons, hpn_g] at this
      dsimp only [workBinderCount0, binderCount0, blocksBinderCount0] at this; omega
    have hst_bd_step : st.nextVid.toNat + pts.length ≤ preRes.nextVid.toNat := by
      have htot := hinv.preRes_uses_lt_bd
      rw [List.map_cons, hnd] at htot
      dsimp only [workBinderCount0, binderCount0, blocksBinderCount0] at htot
      omega
    have hnv_b32 : st.nextVid.toNat + pts.length < 2 ^ 31 := by
      have := hinv.preRes_nv; omega
    have hbind_pre := preBindLoop0_spec pts.length (tyLenU0 pts 0) nextSc curPre.venv
      preSt hlen_pts hnv_b hinv.pre_inv.defScope_sz hinv.pre_inv.uses_sz hinv.pre_inv.escaped_sz
    dsimp only at hbind_pre
    let preOut := preBindLoop0 (tyLenU0 pts 0) nextSc curPre.venv preSt
    let pK_item := PreItem0.mk cont curPre.venv (nextSc + 1)
    let pB_item := PreItem0.mk b preOut.1 nextSc
    have hout_eq : preStepPush0 curPre (preNoteNode0 curPre.scope curPre.venv curPre.node preSt)
        nextSc pw₂ = PreOut0.mk preOut.2 (nextSc + 2) (pK_item :: pB_item :: pw₂) := by
      dsimp only [preStepPush0, preNoteNode0]; rw [hpn_g]
      simp only [isTerm0, Bool.false_eq_true, ↓reduceIte]
      dsimp only [preStepGroup0, preEnqueueGroup0, prePushGroup0, prePushOne0]
      rw [UInt32.add_assoc, show (1 : UInt32) + 1 = 2 by decide]
    let bb := bindBlockParams0 pts cur.venv st0 cur.freeSlots cur.nextSlot
    let bbC := bindBlockParams0 pts cur.venv st0Clean cur.freeSlots cur.nextSlot
    let slots := slotsOfVids0 (tyLenU0 pts 0) bb.venv bb.st.vslot []
    let ctrl1 : CtrlSt0 :=
      { ctrl with nextLbl := ctrl.nextLbl + 1, lblSlots := ctrl.lblSlots.push slots }
    let tK := RegaTask0.mk 0 cont cur.venv (ctrl.nextLbl :: cur.lenv) bb.free bb.nxt
    let tB := RegaTask0.mk ctrl.nextLbl b bb.venv (ctrl.nextLbl :: cur.lenv) bb.free bb.nxt
    have hbbC_eq := bindBlockParams0_clean_eq pts cur.venv st0Clean st0 cur.freeSlots cur.nextSlot
      (hst0C_eqs.1.trans hst0_eqs.1.symm) (hst0C_eqs.2.1.trans hst0_eqs.2.1.symm)
      (hst0C_eqs.2.2.1.trans hst0_eqs.2.2.1.symm) (hst0C_eqs.2.2.2.trans hst0_eqs.2.2.2.symm)
    dsimp only at hbbC_eq
    have hslots_C_eq : slotsOfVids0 (tyLenU0 pts 0) bbC.venv bbC.st.vslot [] = slots := by
      have hvsl_sz0 : st0.vslot.size = st0.nextVid.toNat := by
        rw [hst0_eqs.1, hst0_eqs.2.2.1]; exact hinv.st_vslot_sz
      have h := bindBlockParams0_spec_clean pts cur.venv st0 cur.freeSlots cur.nextSlot
        (preRes.nextVid.toNat + fnMaxJump) hvsl_sz0
        (by rw [hst0_eqs.1]; omega)
        ⟨hpool.1, hpool.2.1, by rw [hst0_eqs.2.1]; exact hpool.2.2.1,
          by rw [hst0_eqs.2.1]; exact hinv.st_maxSl_le, hpool.2.2.2.2⟩
        (by omega)
      dsimp only at h
      have hC := bindBlockParams0_spec_clean pts cur.venv st0Clean cur.freeSlots cur.nextSlot
        (preRes.nextVid.toNat + fnMaxJump)
        (by rw [hst0C_eqs.1, hst0C_eqs.2.2.1]; exact hinv.st_vslot_sz)
        (by rw [hst0C_eqs.1]; omega)
        ⟨hpool.1, hpool.2.1, by rw [hst0C_eqs.2.1]; exact hpool.2.2.1,
          by rw [hst0C_eqs.2.1]; exact hinv.st_maxSl_le, hpool.2.2.2.2⟩
        (by omega)
      dsimp only at hC
      rw [hC.1, hst0C_eqs.1, slotsOfVids0_pushFreshVids0 pts.length (tyLenU0 pts 0) st.nextVid
        cur.venv bbC.st.vslot [] hlen_pts (by omega)]
      dsimp only [slots]
      rw [h.1, hst0_eqs.1, slotsOfVids0_pushFreshVids0 pts.length (tyLenU0 pts 0) st.nextVid
        cur.venv bb.st.vslot [] hlen_pts (by omega)]
      congr 1; apply List.map_congr_left; intro j hj
      have hj_lt : j < pts.length := List.mem_range.mp hj
      have hj32 : (st.nextVid + UInt32.ofNat j).toNat < st0.nextVid.toNat + pts.length := by
        rw [hst0_eqs.1, u32_add_ofNat_lt7 (by omega)]; omega
      have hd1 := congrArg (fun a : Array Nat => a.getD (st.nextVid + UInt32.ofNat j).toNat 0)
        hbbC_eq.2.2.2.2.2.1
      dsimp only [arrGetU0]; exact congrArg UInt32.ofNat hd1
    have hlsS_eq : lsS.st = bb.st ∧ lsS.ctrl = ctrl1 ∧ lsS.work = tK :: tB :: w₂ := by
      dsimp only [lsS, regaStep0]; rw [hnd]
      dsimp only [stepGroupFinish0, stepGroupPrep0, regaPrepGroup0, prepOneBlock0, prepOneBind0,
        prepFinishBlock0, prepUpdCtrl0, groupEnqCont0, regaEnqueueGroup0]
      exact ⟨rfl, rfl, rfl⟩
    have hlsC_eq : lsC.st = bbC.st ∧ lsC.ctrl = ctrl1 ∧ lsC.work = [tK, tB] := by
      dsimp only [lsC, regaStep0]; rw [hnd]
      dsimp only [stepGroupFinish0, stepGroupPrep0, regaPrepGroup0, prepOneBlock0, prepOneBind0,
        prepFinishBlock0, prepUpdCtrl0, groupEnqCont0, regaEnqueueGroup0]
      rw [hslots_C_eq, hbbC_eq.1, hbbC_eq.2.1, hbbC_eq.2.2.1]; exact ⟨rfl, rfl, rfl⟩
    have hvsl_sz0' : st0.vslot.size = st0.nextVid.toNat := by
      rw [hst0_eqs.1, hst0_eqs.2.2.1]; exact hinv.st_vslot_sz
    have hbb := bindBlockParams0_spec_clean pts cur.venv st0 cur.freeSlots cur.nextSlot
      (preRes.nextVid.toNat + fnMaxJump) hvsl_sz0'
      (by rw [hst0_eqs.1]; omega)
      ⟨hpool.1, hpool.2.1, by rw [hst0_eqs.2.1]; exact hpool.2.2.1,
        by rw [hst0_eqs.2.1]; exact hinv.st_maxSl_le, hpool.2.2.2.2⟩
      (by omega)
    dsimp only at hbb
    rw [show bindBlockParams0 pts cur.venv st0 cur.freeSlots cur.nextSlot = bb from rfl] at hbb
    obtain ⟨hbb_venv, hbb_nv, hbb_vsz, hbb_rem, hbb_rev, hbb_pool, hbb_nlo, hbb_nhi, hbb_fr,
      hbb_pres, hbb_sl⟩ := hbb
    have hnl1 : (ctrl.nextLbl + 1).toNat = ctrl.nextLbl.toNat + 1 := u32_add1_toNat7 (by
      have := hinv.ctrl_nl
      rw [List.map_cons, hnd] at this
      dsimp only [workNodeCount0, nodeCount0, blocksNodeCount0] at this; omega)
    have hslots_eq : slots =
        (List.range pts.length).map
          (fun j => arrGetU0 bb.st.vslot (st.nextVid + UInt32.ofNat j)) := by
      dsimp only [slots]; rw [hbb_venv, hst0_eqs.1]
      rw [slotsOfVids0_pushFreshVids0 pts.length (tyLenU0 pts 0) st.nextVid cur.venv
        bb.st.vslot [] hlen_pts (by omega)]
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
      dsimp only [ctrl1]; rw [arrPush_getD7, hctrl_sz]; simp
    have hctrl1_get_old : ∀ l, 1 ≤ l → l < ctrl.nextLbl.toNat →
        ctrl1.lblSlots.getD l [] = ctrl.lblSlots.getD l [] := by
      intro l _ hl; dsimp only [ctrl1]; rw [arrPush_getD7, hctrl_sz]; simp [hl]
    let infoK : LblInfo0 :=
      ⟨ctrl.nextLbl, pts, slots, bb.nxt, cur.venv, mCur.vT, st.nextVid, true⟩
    let infoB : LblInfo0 := { infoK with waiting := false }
    let lT' := pts :: mCur.lT
    let mK := TaskMeta0.mk mCur.vT lT' (infoK :: mCur.gl) none
    let mB := TaskMeta0.mk (pushTys0 pts mCur.vT) lT' (infoB :: mCur.gl) (some infoB)
    rw [hout_eq, hlsS_eq.1, hlsS_eq.2.1, hlsS_eq.2.2] at hinv1
    obtain ⟨hmK, hmB, rfl⟩ : ∃ hmK hmB, headMeta = [hmK, hmB] := by
      have hmw1 := hinv1.len_mw
      rw [List.length_append, hlen_mw] at hmw1
      cases headMeta with
      | nil => simp only [List.length_nil, List.length_cons] at hmw1; omega
      | cons a tl => cases tl with
        | nil => simp only [List.length_cons, List.length_nil] at hmw1; omega
        | cons b' tl' => cases tl' with
          | nil => exact ⟨a, b', rfl⟩
          | cons _ _ => simp only [List.length_cons] at hmw1; omega
    have hr_pos_f : 0 < (UInt32.ofNat (nodeCount0 cur.node)).toNat := by
      rw [u32_ofNat_toNat_lt10 (by omega), hnc_eq]; omega
    have hr_sub : UInt32.ofNat (nodeCount0 cur.node) - 1 =
        UInt32.ofNat (nodeCount0 cont + nodeCount0 b) := by
      apply u32_ext7; rw [u32_sub1_toNat7 hr_pos_f, u32_ofNat_toNat_lt10 (by omega),
        u32_ofNat_toNat_lt10 (by omega), hnc_eq]; omega
    have hstep1 := regaRunAux0_step_once (fuel := UInt32.ofNat (nodeCount0 cur.node))
      (esc := preRes.escaped) (st := { st with revDirs := [] }) (ctrl := ctrl)
      (cur := cur) (rest := []) hr_pos_f
    dsimp only at hstep1
    rw [hlsC_eq.1, hlsC_eq.2.1, hlsC_eq.2.2, hr_sub] at hstep1
    let rK := regaRunAux0 (UInt32.ofNat (nodeCount0 cont)) preRes.escaped
      { bb.st with revDirs := [] } ctrl1 [tK]
    let rB := regaRunAux0 (UInt32.ofNat (nodeCount0 b)) preRes.escaped
      { rK.1 with revDirs := [] } rK.2 [tB]
    have hsplit_kb := regaRunAux0_split_and_fuel (nodeCount0 cont)
      (UInt32.ofNat (nodeCount0 cont + nodeCount0 b)) (UInt32.ofNat (nodeCount0 cont))
      preRes.escaped bbC.st ctrl1 [tK] [tB]
      (by rw [List.map_singleton]; dsimp only [tK, workNodeCount0]; exact Nat.add_zero _)
      (by rw [u32_ofNat_toNat_lt10 (by omega)]; omega)
      (by rw [u32_ofNat_toNat_lt10 (by omega)]; exact Nat.le_refl _)
    dsimp only at hsplit_kb
    have hrev_k := regaRunAux0_revDirs_append (UInt32.ofNat (nodeCount0 cont))
      preRes.escaped bbC.st ctrl1 [tK]
    have hclean_bbC : regaRunAux0 (UInt32.ofNat (nodeCount0 cont)) preRes.escaped
        { bbC.st with revDirs := [] } ctrl1 [tK] = rK := by
      dsimp only [rK]; rw [hbbC_eq.2.2.2.2.2.2.2]
    rw [hclean_bbC] at hrev_k
    have hkb_nat : (UInt32.ofNat (nodeCount0 cont + nodeCount0 b)).toNat =
        nodeCount0 cont + nodeCount0 b := u32_ofNat_toNat_lt10 (by rw [hnc_eq] at hnc_bd; omega)
    have hsub_b : UInt32.ofNat ((UInt32.ofNat (nodeCount0 cont + nodeCount0 b)).toNat -
        nodeCount0 cont) = UInt32.ofNat (nodeCount0 b) := by
      rw [hkb_nat]; congr 1; omega
    rw [hrev_k, hsub_b] at hsplit_kb
    dsimp only at hsplit_kb
    have hrev_b := regaRunAux0_revDirs_append (UInt32.ofNat (nodeCount0 b))
      preRes.escaped { rK.1 with revDirs := rK.1.revDirs ++ bbC.st.revDirs } rK.2 [tB]
    rw [hrev_b] at hsplit_kb
    dsimp only [List.cons_append, List.nil_append] at hsplit_kb
    have hbbC_rev : bbC.st.revDirs = st0Clean.revDirs := bindBlockParams0_revDirs ..
    have hstep_rev :
        (regaRunAux0 (UInt32.ofNat (nodeCount0 cur.node)) preRes.escaped
          { st with revDirs := [] } ctrl [cur]).1.revDirs =
        rB.1.revDirs ++ (rK.1.revDirs ++ st0Clean.revDirs) := by
      rw [hstep1, hsplit_kb]; dsimp only [rB]; rw [hbbC_rev]
    rw [hstep_rev, emitFwd0_append, emitFwd0_append, patchEpilogues0_append,
      patchEpilogues0_append, toAmd64Program_append, toAmd64Program_append] at hcode
    simp only [List.append_assoc] at hcode
    refine regaPrependLbl0_run cur st ctrl (x64FrameSizeU0 ns) _ s
      (fnPost0 h rs Q X s0 ra0 n nX Rf) hu hcode fun _ hprog => ?_
    let k1 := k + (if cur.lblId = 0 then 0 else 1)
    let pK := toAmd64Program symName
      (patchEpilogues0 (x64FrameSizeU0 ns) (emitFwd0 rK.1.revDirs) [])
    let pB := toAmd64Program symName
      (patchEpilogues0 (x64FrameSizeU0 ns) (emitFwd0 rB.1.revDirs) [])
    have hpK_inf : pK.IsInfixAt (x64ScalarMach.prog h) k1 := hprog.append.1
    have hpB_inf : pB.IsInfixAt (x64ScalarMach.prog h) (k1 + pK.length) := hprog.append.2
    have hinfo_new_ok : ∀ w : Bool,
        LblInfoOk0 preRes.escaped bb.st ctrl1 { infoK with waiting := w } := fun w => by
      have hnl := hinv.ctrl_nl
      rw [List.map_cons, hnd] at hnl
      dsimp only [workNodeCount0, nodeCount0, blocksNodeCount0] at hnl
      refine ⟨hnl.1, by dsimp only [ctrl1, infoK]; rw [hnl1]; omega, hctrl1_get_new,
        hslots_len, hslots_nd, by dsimp only [infoK]; rw [hbb_nv, hst0_eqs.1]; omega,
        fun j hj => by dsimp only [infoK]; rw [← hslots_getD j hj], hbb_pool.2.2.1,
        fun s hs => (hslots_mem s hs).1, hvlen, hvlt, fun s hs u hu hescu humem => ?_⟩
      dsimp only [infoK] at hs hu humem ⊢
      have hu_lt : u < st.nextVid.toNat := hu
      rw [hbb_pres u (hst0_eqs.1 ▸ hu_lt), hst0_eqs.2.2.1]
      have hlu := hlive u hu_lt (Or.inl ⟨hescu, humem⟩)
      have hsm := hslots_mem s hs
      intro heq
      rcases hsm.2.2 with hfr' | hge
      · exact hlu.2.1 (heq ▸ hfr')
      · have := hlu.1; rw [heq] at this; omega
    have hgi_ext : ∀ (info0 : LblInfo0) (gl0 : List LblInfo0) (lT0 : List (List Ty0)),
        info0.lbl = ctrl.nextLbl → info0.pts = pts →
        (∀ (j : Nat) (h1 : j < gl0.length) (h2 : j < cur.lenv.length) (h3 : j < lT0.length),
          gl0[j].lbl = cur.lenv[j] ∧ gl0[j].pts = lT0[j]) →
        ∀ (j : Nat) (h1 : j < (info0 :: gl0).length) (h2 : j < (ctrl.nextLbl :: cur.lenv).length)
          (h3 : j < (pts :: lT0).length),
          (info0 :: gl0)[j].lbl = (ctrl.nextLbl :: cur.lenv)[j] ∧
            (info0 :: gl0)[j].pts = (pts :: lT0)[j] :=
        fun info0 gl0 lT0 hl hp hprev j h1 h2 h3 => by
      cases j with
      | zero => exact ⟨hl, hp⟩
      | succ j' =>
        exact hprev j' (by simp at h1; omega) (by simp at h2; omega) (by simp at h3; omega)
    have hlive_k : ∀ v < bb.st.nextVid.toNat,
        LiveInTask0 preRes.escaped preOut.2 bb.st pK_item tK v →
        v < st.nextVid.toNat ∧ preRes.escaped.getD v 0 = 1 ∧ UInt32.ofNat v ∈ cur.venv := by
      intro v hv hlv
      rcases hlv with ⟨hes, hvmem⟩ | ⟨_, hsc_v, _⟩
      · have hv' : v < st.nextVid.toNat := by
          have := hvlt (UInt32.ofNat v) hvmem
          rwa [u32_toNat_ofNat7, Nat.mod_eq_of_lt (Nat.lt_trans hv (UInt32.toNat_lt _))] at this
        exact ⟨hv', hes, hvmem⟩
      · dsimp only [pK_item, preOut] at hsc_v
        rw [hbind_pre.2.2.2.2.2.1 v] at hsc_v
        split at hsc_v
        · rename_i hv0; have := hinv.pre_inv.defScope_lt v hv0; omega
        · have hv_tot : v < preSt.nextVid.toNat + pts.length := by
            rw [hbb_nv, hst0_eqs.1, hinv.st_nv] at hv; exact hv
          simp only [hv_tot, ↓reduceIte] at hsc_v; omega
    have hvlt_b : ∀ v ∈ bb.venv, v.toNat < bb.st.nextVid.toNat := fun v hm => by
      rw [hbb_nv, hst0_eqs.1]; rw [hbb_venv, hst0_eqs.1] at hm
      rcases (mem_pushFreshVids0 pts.length st.nextVid cur.venv v).mp hm with h0 | ⟨j, hj, rfl⟩
      · exact Nat.lt_of_lt_of_le (hvlt v h0) (Nat.le_add_right _ _)
      · rw [u32_add_ofNat_lt7 (by omega)]; omega
    have hlive_b_old : ∀ v < st.nextVid.toNat,
        LiveInTask0 preRes.escaped preOut.2 bb.st pB_item tB v →
        preRes.escaped.getD v 0 = 1 ∧ UInt32.ofNat v ∈ cur.venv := fun v hv hlv => by
      rcases hlv with ⟨hes, hvmem⟩ | ⟨_, hsc_v, _⟩
      · dsimp only [tB] at hvmem; rw [hbb_venv, hst0_eqs.1] at hvmem
        rcases (mem_pushFreshVids0 pts.length st.nextVid cur.venv _).mp hvmem
          with h0 | ⟨j, hj, he⟩
        · exact ⟨hes, h0⟩
        · have hn := congrArg UInt32.toNat he
          rw [u32_toNat_ofNat7, u32_add_ofNat_lt7 (m := j) (by omega),
            Nat.mod_eq_of_lt (Nat.lt_trans hv (UInt32.toNat_lt _))] at hn
          omega
      · dsimp only [pB_item, preOut] at hsc_v
        rw [hbind_pre.2.2.2.2.2.1 v] at hsc_v
        simp only [show v < preSt.nextVid.toNat from hinv.st_nv ▸ hv, ↓reduceIte] at hsc_v
        have := hinv.pre_inv.defScope_lt v (hinv.st_nv ▸ hv); omega
    have hbb_live : ∀ u < bb.st.nextVid.toNat,
        LiveInTask0 preRes.escaped preOut.2 bb.st pB_item tB u →
        (arrGetU0 bb.st.vslot (UInt32.ofNat u)).toNat < bb.nxt.toNat ∧
        arrGetU0 bb.st.vslot (UInt32.ofNat u) ∉ bb.free ∧
        (u < st.nextVid.toNat →
          (arrGetU0 st.vslot (UInt32.ofNat u)).toNat < cur.nextSlot.toNat ∧
          arrGetU0 st.vslot (UInt32.ofNat u) ∉ cur.freeSlots) := fun u hu hlu => by
      rw [hbb_nv, hst0_eqs.1] at hu
      by_cases huo : u < st.nextVid.toNat
      · obtain ⟨hes, humem⟩ := hlive_b_old u huo hlu
        rw [hbb_pres u (hst0_eqs.1 ▸ huo), hst0_eqs.2.2.1]
        have hlu_c := hlive u huo (Or.inl ⟨hes, humem⟩)
        exact ⟨Nat.lt_of_lt_of_le hlu_c.1 hbb_nlo, fun hm => hlu_c.2.1 (hbb_fr _ hm),
          fun _ => ⟨hlu_c.1, hlu_c.2.1⟩⟩
      · obtain ⟨j, hj, rfl⟩ : ∃ j < pts.length, u = st.nextVid.toNat + j :=
          ⟨u - st.nextVid.toNat, by omega, by omega⟩
        rw [show UInt32.ofNat (st.nextVid.toNat + j) = st0.nextVid + UInt32.ofNat j from by
          rw [hst0_eqs.1]; exact u32_ofNat_add_eq7 st.nextVid j (by omega)]
        have hbj := hbb_sl j hj; exact ⟨hbj.1, hbj.2.1, fun hlt => absurd hlt (by omega)⟩
    have hbb_venv_pre : bb.venv = preOut.1 := by
      rw [hbb_venv, hst0_eqs.1, hinv.st_nv, hbind_pre.1, hpv]
    have hwf_rest : ∀ (m : Nat) (hm1 : m < pw₂.length) (hm2 : m < w₂.length) w,
        w < bb.st.nextVid.toNat →
        LiveInTask0 preRes.escaped preOut.2 bb.st (pw₂[m]'hm1) (w₂[m]'hm2) w →
        w < st.nextVid.toNat ∧
        LiveInTask0 preRes.escaped preSt st (pw₂[m]'hm1) (w₂[m]'hm2) w :=
        fun m hm1 hm2 w hw hlv => by
      rcases hlv with ⟨hes, hvmem⟩ | ⟨hes, hsc_v, hpos⟩
      · have htm := hinv.items_ok (m + 1) (by simp only [List.length_cons] at hm1 ⊢; omega)
          (by simp only [List.length_cons] at hm2 ⊢; omega)
          (by simp only [List.length_cons] at hm2 ⊢; omega)
        have hw_lt : w < st.nextVid.toNat := by
          have := htm.2.2.2.1 (UInt32.ofNat w) hvmem
          rwa [u32_toNat_ofNat7, Nat.mod_eq_of_lt (Nat.lt_trans hw (UInt32.toNat_lt _))] at this
        exact ⟨hw_lt, Or.inl ⟨hes, hvmem⟩⟩
      · have hw_lt : w < st.nextVid.toNat := Nat.lt_of_not_le fun hge => False.elim <| by
          dsimp only [preOut] at hsc_v
          rw [hbind_pre.2.2.2.2.2.1 w] at hsc_v
          simp only [show ¬ w < preSt.nextVid.toNat from hinv.st_nv ▸ Nat.not_lt_of_ge hge,
            show w < preSt.nextVid.toNat + pts.length from by
              rw [← hinv.st_nv, ← hst0_eqs.1, ← hbb_nv]; exact hw,
            ↓reduceIte] at hsc_v
          have hsc_m := hinv.pre_inv.scopes_lt (pw₂[m]'hm1)
            (List.mem_cons_of_mem _ (List.getElem_mem hm1))
          omega
        dsimp only [preOut] at hsc_v
        rw [hbind_pre.2.2.2.2.2.1 w] at hsc_v
        simp only [show w < preSt.nextVid.toNat from hinv.st_nv ▸ hw_lt, ↓reduceIte] at hsc_v
        rw [hbb_rem, hst0_eqs.2.2.2] at hpos
        exact ⟨hw_lt, Or.inr ⟨hes, hsc_v, hpos⟩⟩
    have hinv_k : RegaStepInv0 ctx fnIdx fnMaxJump preRes (nextSc + 2) preOut.2
        (pK_item :: pB_item :: pw₂) false bb.st ctrl1 (tK :: tB :: w₂) (mK :: mB :: m₂) :=
      { preRes_nv := hinv1.preRes_nv
        preRes_ds_sz := hinv1.preRes_ds_sz
        preRes_us_sz := hinv1.preRes_us_sz
        preRes_es_sz := hinv1.preRes_es_sz
        preRes_es_bit := hinv1.preRes_es_bit
        preRes_us_bd := hinv1.preRes_us_bd
        maxBd_lt := hinv1.maxBd_lt
        pre_inv := hinv1.pre_inv
        pre_run := hinv1.pre_run
        len_pw := hinv1.len_pw
        len_mw := by simp only [List.length_cons, hlen_mw]
        seenJnz_safe := hinv1.seenJnz_safe
        seenJnz_ctrl := hinv1.seenJnz_ctrl
        maxJump_bd := hinv1.maxJump_bd
        ctrl_fn := hinv1.ctrl_fn
        ctrl_nl := hinv1.ctrl_nl
        st_nv := hinv1.st_nv
        st_vslot_sz := hinv1.st_vslot_sz
        st_rem_sz := hinv1.st_rem_sz
        st_maxSl_le := hinv1.st_maxSl_le
        st_rem_le := hinv1.st_rem_le
        st_rem_future := hinv1.st_rem_future
        st_rem_active := hinv1.st_rem_active
        items_ok := fun i hi1 hi2 hi3 => by
          cases i with
          | zero =>
            dsimp only [List.getElem_cons_zero, pK_item, tK, mK]
            refine ⟨rfl, hpv, hvlen, fun v hm => by
                rw [hbb_nv, hst0_eqs.1]
                exact Nat.lt_of_lt_of_le (hvlt v hm) (Nat.le_add_right _ _),
              by simp only [lT', List.length_cons, hllen],
              by simp only [List.length_cons, hgl_len],
              hgi_ext infoK mCur.gl mCur.lT rfl rfl hgi,
              hwfk, hfitk, hsbgk, hnbk, hbb_pool,
              by dsimp only; have := hbb_nhi; have := hnxt_nv; rw [hbb_nv, hst0_eqs.1]; omega,
              fun info hi => by
                rcases List.mem_cons.mp hi with rfl | hi'
                · exact hinfo_new_ok true
                · exact lblInfoOk0_mono (hinfo_ok info hi') (by dsimp only [ctrl1]; omega)
                    hctrl1_get_old (by rw [hbb_nv, hst0_eqs.1]; exact Nat.le_add_right _ _)
                    (hst0_eqs.2.1 ▸ bindBlockParams0_maxSlots_le pts cur.venv st0 cur.freeSlots
                      cur.nextSlot)
                    (fun v hv => by rw [hbb_pres v (hst0_eqs.1 ▸ hv), hst0_eqs.2.2.1]),
              fun info hi hw => by
                rcases List.mem_cons.mp hi with rfl | hi'
                · refine ⟨fun s hs => ⟨(hslots_mem s hs).1, (hslots_mem s hs).2.1⟩,
                    fun v hv hlv => ?_⟩
                  obtain ⟨hv_lt, hes, hvmem⟩ := hlive_k v hv hlv
                  rw [hbb_pres v (hst0_eqs.1 ▸ hv_lt), hst0_eqs.2.2.1]
                  have hlu := hlive v hv_lt (Or.inl ⟨hes, hvmem⟩)
                  intro hm; rcases (hslots_mem _ hm).2.2 with hfr' | hge
                  · exact hlu.2.1 hfr'
                  · have := hlu.1; omega
                · refine ⟨fun s hs => ⟨Nat.lt_of_lt_of_le ((hwait info hi' hw).1 s hs).1 hbb_nlo,
                      fun hm => ((hwait info hi' hw).1 s hs).2 (hbb_fr s hm)⟩, fun v hv hlv => ?_⟩
                  obtain ⟨hv_lt, hes, hvmem⟩ := hlive_k v hv hlv
                  rw [hbb_pres v (hst0_eqs.1 ▸ hv_lt), hst0_eqs.2.2.1]
                  exact (hwait info hi' hw).2 v hv_lt (Or.inl ⟨hes, hvmem⟩),
              trivial, fun v hv hlv => by
                obtain ⟨hv_lt, hes, hvmem⟩ := hlive_k v hv hlv
                rw [hbb_pres v (hst0_eqs.1 ▸ hv_lt), hst0_eqs.2.2.1]
                have hlv_c := hlive v hv_lt (Or.inl ⟨hes, hvmem⟩)
                refine ⟨Nat.lt_of_lt_of_le hlv_c.1 hbb_nlo, fun hm => hlv_c.2.1 (hbb_fr _ hm),
                  fun w hw hne hlw => ?_⟩
                obtain ⟨hw_lt, hesw, hwmemw⟩ := hlive_k w hw hlw
                rw [hbb_pres w (hst0_eqs.1 ▸ hw_lt), hst0_eqs.2.2.1]
                exact hlv_c.2.2 w hw_lt hne (Or.inl ⟨hesw, hwmemw⟩)⟩
          | succ i' => cases i' with
            | zero =>
              dsimp only [List.getElem_cons_succ, List.getElem_cons_zero, pB_item, tB, mB]
              refine ⟨rfl, hbb_venv_pre.symm,
                by rw [hbb_venv, pushFreshVids0_length, hvlen, pushTys0_eq_pushTypes,
                    pushTypes_length],
                hvlt_b, by simp only [lT', List.length_cons, hllen],
                by simp only [List.length_cons, hgl_len],
                hgi_ext infoB mCur.gl mCur.lT rfl rfl hgi, hwfb, hfitb, hsbgb, hnbb, hbb_pool,
                by dsimp only; have := hbb_nhi; have := hnxt_nv; rw [hbb_nv, hst0_eqs.1]; omega,
                fun info hi => by
                  rcases List.mem_cons.mp hi with rfl | hi'
                  · exact hinfo_new_ok false
                  · exact lblInfoOk0_mono (hinfo_ok info hi') (by dsimp only [ctrl1]; omega)
                      hctrl1_get_old (by rw [hbb_nv, hst0_eqs.1]; exact Nat.le_add_right _ _)
                      (hst0_eqs.2.1 ▸ bindBlockParams0_maxSlots_le pts cur.venv st0 cur.freeSlots
                        cur.nextSlot)
                      (fun v hv => by rw [hbb_pres v (hst0_eqs.1 ▸ hv), hst0_eqs.2.2.1]),
                fun info hi hw => by
                  rcases List.mem_cons.mp hi with rfl | hi'
                  · cases hw
                  · refine ⟨fun s hs => ⟨Nat.lt_of_lt_of_le ((hwait info hi' hw).1 s hs).1 hbb_nlo,
                        fun hm => ((hwait info hi' hw).1 s hs).2 (hbb_fr s hm)⟩, fun v hv hlv => ?_⟩
                    rw [hbb_nv, hst0_eqs.1] at hv
                    by_cases hvo : v < st.nextVid.toNat
                    · obtain ⟨hes, hvmem⟩ := hlive_b_old v hvo hlv
                      rw [hbb_pres v (hst0_eqs.1 ▸ hvo), hst0_eqs.2.2.1]
                      exact (hwait info hi' hw).2 v hvo (Or.inl ⟨hes, hvmem⟩)
                    · obtain ⟨j, hj, rfl⟩ : ∃ j < pts.length, v = st.nextVid.toNat + j :=
                        ⟨v - st.nextVid.toNat, by omega, by omega⟩
                      rw [show UInt32.ofNat (st.nextVid.toNat + j) = st0.nextVid + UInt32.ofNat j
                        from by rw [hst0_eqs.1]; exact u32_ofNat_add_eq7 st.nextVid j (by omega)]
                      intro hm; rcases (hbb_sl j hj).2.2.1 with hfr' | hge
                      · exact ((hwait info hi' hw).1 _ hm).2 hfr'
                      · have := ((hwait info hi' hw).1 _ hm).1; omega,
                by dsimp only [infoB, infoK]
                   exact ⟨rfl, List.mem_cons_self, rfl, by rw [hbb_venv, hst0_eqs.1], rfl, rfl⟩,
                fun v hv hlv => by
                  obtain ⟨hs_lt, hs_nf, _⟩ := hbb_live v hv hlv
                  refine ⟨hs_lt, hs_nf, fun w hw hne hlw => ?_⟩
                  rw [hbb_nv, hst0_eqs.1] at hv hw
                  by_cases hvo : v < st.nextVid.toNat <;> by_cases hwo : w < st.nextVid.toNat
                  · obtain ⟨hesv, hvmem⟩ := hlive_b_old v hvo hlv
                    obtain ⟨hesw, hwmem⟩ := hlive_b_old w hwo hlw
                    rw [hbb_pres v (hst0_eqs.1 ▸ hvo), hbb_pres w (hst0_eqs.1 ▸ hwo),
                      hst0_eqs.2.2.1]
                    exact (hlive v hvo (Or.inl ⟨hesv, hvmem⟩)).2.2 w hwo hne (Or.inl ⟨hesw, hwmem⟩)
                  · obtain ⟨jw, hjw, rfl⟩ : ∃ j < pts.length, w = st.nextVid.toNat + j :=
                      ⟨w - st.nextVid.toNat, by omega, by omega⟩
                    obtain ⟨hesv, hvmem⟩ := hlive_b_old v hvo hlv
                    rw [hbb_pres v (hst0_eqs.1 ▸ hvo), hst0_eqs.2.2.1]
                    have hlv_c := hlive v hvo (Or.inl ⟨hesv, hvmem⟩)
                    rw [show UInt32.ofNat (st.nextVid.toNat + jw) = st0.nextVid + UInt32.ofNat jw
                      from by rw [hst0_eqs.1]; exact u32_ofNat_add_eq7 st.nextVid jw (by omega)]
                    intro hcol; rcases (hbb_sl jw hjw).2.2.1 with hfr' | hge
                    · exact hlv_c.2.1 (hcol ▸ hfr')
                    · have := hlv_c.1; rw [← hcol] at this; omega
                  · obtain ⟨jv, hjv, rfl⟩ : ∃ j < pts.length, v = st.nextVid.toNat + j :=
                      ⟨v - st.nextVid.toNat, by omega, by omega⟩
                    obtain ⟨hesw, hwmem⟩ := hlive_b_old w hwo hlw
                    rw [hbb_pres w (hst0_eqs.1 ▸ hwo), hst0_eqs.2.2.1]
                    have hlw_c := hlive w hwo (Or.inl ⟨hesw, hwmem⟩)
                    rw [show UInt32.ofNat (st.nextVid.toNat + jv) = st0.nextVid + UInt32.ofNat jv
                      from by rw [hst0_eqs.1]; exact u32_ofNat_add_eq7 st.nextVid jv (by omega)]
                    intro hcol; rcases (hbb_sl jv hjv).2.2.1 with hfr' | hge
                    · exact hlw_c.2.1 (hcol.symm ▸ hfr')
                    · have := hlw_c.1; rw [hcol] at this; omega
                  · obtain ⟨jv, hjv, rfl⟩ : ∃ j < pts.length, v = st.nextVid.toNat + j :=
                      ⟨v - st.nextVid.toNat, by omega, by omega⟩
                    obtain ⟨jw, hjw, rfl⟩ : ∃ j < pts.length, w = st.nextVid.toNat + j :=
                      ⟨w - st.nextVid.toNat, by omega, by omega⟩
                    rw [show UInt32.ofNat (st.nextVid.toNat + jv) = st0.nextVid + UInt32.ofNat jv
                        from by rw [hst0_eqs.1]; exact u32_ofNat_add_eq7 st.nextVid jv (by omega),
                      show UInt32.ofNat (st.nextVid.toNat + jw) = st0.nextVid + UInt32.ofNat jw
                        from by rw [hst0_eqs.1]; exact u32_ofNat_add_eq7 st.nextVid jw (by omega)]
                    have hne_j : jw ≠ jv := fun he => hne (by omega)
                    rcases Nat.lt_or_gt_of_ne hne_j with hlt | hgt
                    · exact (hbb_sl jv hjv).2.2.2 jw hlt
                    · exact Ne.symm ((hbb_sl jw hjw).2.2.2 jv hgt)⟩
            | succ j' =>
              exact hinv1.items_ok (j' + 2) hi1 hi2 (by simp at hi3 ⊢; omega)
        later_live := fun i j hi1 hi2 hi3 hj1 hj2 hij w hw hlive_j => by
          cases j with
          | zero => omega
          | succ j' => cases j' with
            | zero =>
              cases i with
              | zero =>
                dsimp only [List.getElem_cons_zero, List.getElem_cons_succ, pK_item, tK,
                  pB_item, tB]
                  at hlive_j ⊢
                by_cases hwo : w < st.nextVid.toNat
                · exact Or.inl (Or.inl (hlive_b_old w hwo hlive_j))
                · rw [hbb_nv, hst0_eqs.1] at hw
                  obtain ⟨jj, hjj, rfl⟩ : ∃ jj < pts.length, w = st.nextVid.toNat + jj :=
                    ⟨w - st.nextVid.toNat, by omega, by omega⟩
                  right; refine ⟨infoK, List.mem_cons_self, rfl, ?_⟩
                  dsimp only [infoK]
                  have hlem := hslots_getD jj hjj
                  rw [listGetD_eq_getElem7 slots 0 jj (by rw [hslots_len]; exact hjj)] at hlem
                  rw [u32_ofNat_add_eq7 st.nextVid jj (by omega), ← hlem]
                  exact List.getElem_mem _
              | succ _ => omega
            | succ k' =>
              have hk'_pre : k' < pw₂.length := by simp only [List.length_cons] at hj1; omega
              have hk'_st : k' < w₂.length := by simp only [List.length_cons] at hj2; omega
              have hk1_s : k' + 1 < (curPre :: pw₂).length := by simp only [List.length_cons]; omega
              have hk2_s : k' + 1 < (cur :: w₂).length := by simp only [List.length_cons]; omega
              cases i with
              | zero =>
                dsimp only [List.getElem_cons_zero, List.getElem_cons_succ, pK_item, tK]
                  at hlive_j ⊢
                obtain ⟨hw_old, hj_old⟩ := hwf_rest k' hk'_pre hk'_st w hw hlive_j
                have hcov := hinv.later_live 0 (k' + 1) (by simp) (by simp) (by simp)
                  hk1_s hk2_s (Nat.zero_lt_succ k') w hw_old hj_old
                rcases hcov with hl0 | ⟨info, hm, hwt, hsl⟩
                · rcases hl0 with ⟨hes, hvmem⟩ | ⟨hes, hsc, _⟩
                  · exact Or.inl (Or.inl ⟨hes, hvmem⟩)
                  · exfalso
                    dsimp only [List.getElem_cons_zero] at hsc
                    rcases hj_old with ⟨hes1, _⟩ | ⟨_, hsc_j, _⟩
                    · rw [hes] at hes1; cases hes1
                    · exact hrest_scopes (pw₂[k']'hk'_pre) (List.getElem_mem hk'_pre)
                        (u32_ext7 (hsc_j.trans hsc.symm))
                · right; refine ⟨info, List.mem_cons_of_mem _ hm, hwt, ?_⟩
                  rw [hbb_pres w (hst0_eqs.1 ▸ hw_old), hst0_eqs.2.2.1]; exact hsl
              | succ i' => cases i' with
                | zero =>
                  dsimp only [List.getElem_cons_succ, List.getElem_cons_zero, pB_item, tB]
                    at hlive_j ⊢
                  obtain ⟨hw_old, hj_old⟩ := hwf_rest k' hk'_pre hk'_st w hw hlive_j
                  have hcov := hinv.later_live 0 (k' + 1) (by simp) (by simp) (by simp)
                    hk1_s hk2_s (Nat.zero_lt_succ k') w hw_old hj_old
                  rcases hcov with hl0 | ⟨info, hm, hwt, hsl⟩
                  · rcases hl0 with ⟨hes, hvmem⟩ | ⟨hes, hsc, _⟩
                    · left; refine Or.inl ⟨hes, ?_⟩
                      rw [hbb_venv, hst0_eqs.1]
                      exact (mem_pushFreshVids0 pts.length st.nextVid cur.venv _).mpr (Or.inl hvmem)
                    · exfalso
                      dsimp only [List.getElem_cons_zero] at hsc
                      rcases hj_old with ⟨hes1, _⟩ | ⟨_, hsc_j, _⟩
                      · rw [hes] at hes1; cases hes1
                      · exact hrest_scopes (pw₂[k']'hk'_pre) (List.getElem_mem hk'_pre)
                          (u32_ext7 (hsc_j.trans hsc.symm))
                  · right; refine ⟨info, List.mem_cons_of_mem _ hm, hwt, ?_⟩
                    rw [hbb_pres w (hst0_eqs.1 ▸ hw_old), hst0_eqs.2.2.1]; exact hsl
                | succ m =>
                  exact hinv1.later_live (m + 2) (k' + 2) hi1 hi2 (by simp at hi3 ⊢; omega)
                    hj1 hj2 hij w hw hlive_j }
    have hp_k_pre := regaRunAux0_step_prefix_ds (N := nodeCount0 cont) (fuel := fuel - 1)
      (ctx := ctx) (fnIdx := fnIdx) (fnMaxJump := fnMaxJump) (preRes := preRes)
      (nextSc := nextSc + 2) (preSt := preOut.2)
      (pw₁ := [pK_item]) (pw₂ := pB_item :: pw₂) (seenJnz := false) (st := bb.st) (ctrl := ctrl1)
      (w₁ := [tK]) (w₂ := tB :: w₂) (m₁ := [mK]) (m₂ := mB :: m₂)
      (by rw [List.map_singleton]; dsimp only [tK, workNodeCount0]; exact Nat.add_zero _)
      (by
        rw [hlsS_eq.2.2] at hfuel1
        rw [List.map_cons, List.map_cons] at hfuel1
        have htk_nd : tK.node = cont := rfl
        have htb_nd : tB.node = b := rfl
        rw [htk_nd, htb_nd] at hfuel1
        dsimp only [workNodeCount0] at hfuel1; omega)
      rfl rfl hinv_k
    dsimp only at hp_k_pre
    obtain ⟨rK_eq, _, hrK_ms, _, hrK_vsl, seenJnz'', nextSc'', preSt'',
      hinv_b, hnv_b_pre, hds_b_pre⟩ := hp_k_pre
    let st_b := { rK.1 with revDirs := rK.1.revDirs ++ bb.st.revDirs }
    have hrK_fn : rK.2.fnIdx = ctrl.fnIdx := hinv_b.ctrl_fn.trans hinv.ctrl_fn.symm
    have hnl_ne : ctrl.nextLbl ≠ 0 := fun hz => by have := hinv.ctrl_nl.1; simp [hz] at this
    have hb_pos : 0 < (UInt32.ofNat (nodeCount0 b)).toNat := by
      rw [u32_ofNat_toNat_lt10 (by omega)]; exact nodeCount0_pos b
    have hlead_B := regaRunAux0_leading_label (symName := symName) (x64FrameSizeU0 ns)
      preRes.escaped rK.1 rK.2 tB [] (UInt32.ofNat (nodeCount0 b)) hb_pos hnl_ne
    rw [hrK_fn] at hlead_B
    have hdef_B : x64ScalarTarget.Defined h (label0ToSym symName (.loc ctrl.fnIdx ctrl.nextLbl)) :=
      ⟨k1 + pK.length, infix_getElem?_zero hpB_inf hlead_B⟩
    have hadr_B := infix_labelAddr_eq hu hpB_inf hlead_B
    let J : Cont (ty0ListToTy pts) := fun xs m' =>
      ∀ s' σ', FnFrameInv0 ns s0 ra0 n Rf m' s' σ' →
        EscOuterAgree0 preRes.escaped bb.st.vslot infoK vs σ' →
        TupInSlots0 σ' infoK.tgts pts xs →
        Eventually (x64ScalarMach.step h) (fnPost0 h rs Q X s0 ra0 n nX Rf)
          ⟨s', x64ScalarMach.labelAddr h (label0ToSym symName (.loc ctrl.fnIdx ctrl.nextLbl))⟩
    have hclosed : closed0 Γ symName rs vs (pushConts0 [(pts, b)] (J, ()) ls) Q X
        [(pts, b)] (J, ()) := by
      rw [closed0_cons]
      refine ⟨fun xs m' hwp_b s' σ' hfr' hesc' htup' => ?_,
        by rw [closed0_nil]; trivial⟩
      have hadr_B' : x64ScalarMach.labelAddr h
          (label0ToSym symName (.loc ctrl.fnIdx ctrl.nextLbl)) =
          x64ScalarMach.addrOf h (k1 + pK.length) := hadr_B
      rw [hadr_B']
      have hns_b :
          (regaRunAux0 (UInt32.ofNat ((fuel - 1).toNat - nodeCount0 cont)) preRes.escaped
            st_b rK.2 (tB :: w₂)).1.maxSlots = ns := by
        have hm := congrArg (fun p => p.1.maxSlots) rK_eq
        rw [← hm]; dsimp only [List.cons_append, List.nil_append]
        rw [← hlsS_eq.1, ← hlsS_eq.2.1, ← hlsS_eq.2.2]; exact hns_next
      have hfuel_b : workNodeCount0 ((tB :: w₂).map RegaTask0.node) ≤
          (UInt32.ofNat ((fuel - 1).toNat - nodeCount0 cont)).toNat := by
        have hm : workNodeCount0 (lsS.work.map RegaTask0.node) + 1 =
            workNodeCount0 ((cur :: w₂).map RegaTask0.node) := hcnt_ch
        have hf0 := hfuel
        rw [hlsS_eq.2.2] at hm
        rw [List.map_cons] at hm hf0 ⊢
        rw [List.map_cons] at hm
        have htk_nd : tK.node = cont := rfl
        have htb_nd : tB.node = b := rfl
        rw [htk_nd, htb_nd] at hm; rw [htb_nd]
        dsimp only [workNodeCount0] at hm hf0 ⊢
        have hflt := UInt32.toNat_lt (fuel - 1)
        rw [u32_ofNat_toNat_lt10 (by omega)]; omega
      have hinf_b : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
          (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 tB.node)) preRes.escaped
            { st_b with revDirs := [] } rK.2 [tB]).1.revDirs) [])).IsInfixAt
          (x64ScalarMach.prog h) (k1 + pK.length) := hpB_inf
      have hag_b : SlotsAgree0 preRes.escaped preSt'' st_b pB_item tB mB.vT
          (pushTup xs vs) σ' := by
        have hpa : PushAgree0 preRes.escaped st_b.remUses st_b.vslot st.nextVid pts xs σ' := by
          refine pushAgree0_of_list preRes.escaped st_b.remUses st_b.vslot σ' pts slots
            st.nextVid xs hnv_b32 hslots_len (fun j hj => ?_) htup'
          rw [← listGetD_eq_getElem7 slots 0 j hj, hslots_getD j (hslots_len ▸ hj)]
          have hvj : (st.nextVid + UInt32.ofNat j).toNat < bb.st.nextVid.toNat := by
            rw [hbb_nv, hst0_eqs.1, u32_add_ofNat_lt7 (by omega)]; omega
          have heq_v := hrK_vsl (st.nextVid + UInt32.ofNat j).toNat hvj
          rw [UInt32.ofNat_toNat] at heq_v
          exact heq_v.symm
        have haux := pushFresh_slotsAgree0_aux preRes.escaped preSt'' st_b pB_item tB σ' pts xs
          st.nextVid cur.venv mCur.vT vs hnv_b32 hag.1 hag.2.1
          (fun v hm => hvlt v hm) (fun idx hi hlv => by
            have hesc_v := (hesc'.2.2 idx hi ?_)
            · have hv_lt : (cur.venv[idx]'hi).toNat < bb.st.nextVid.toNat := by
                rw [hbb_nv, hst0_eqs.1]
                exact Nat.lt_of_lt_of_le (hvlt _ (List.getElem_mem hi)) (Nat.le_add_right _ _)
              have hv_eq := hrK_vsl _ hv_lt
              rw [UInt32.ofNat_toNat] at hv_eq
              obtain ⟨hsl, hvs', ht', hcanon⟩ := hesc_v
              have hsl' : (arrGetU0 st_b.vslot (cur.venv[idx]'hi)).toNat < σ'.length :=
                hv_eq ▸ hsl
              refine ⟨hsl', hvs', ht', ?_⟩
              rw [list_getElem_eq9 σ' hsl' hsl (congrArg UInt32.toNat hv_eq)]
              exact hcanon
            · have hvid_lt : (cur.venv[idx]'hi).toNat < st.nextVid.toNat :=
                hvlt _ (List.getElem_mem hi)
              rcases hlv with ⟨hes, _⟩ | ⟨_, hsc_v, _⟩
              · exact hes
              · exfalso
                have hds1 := hds_b_pre (cur.venv[idx]'hi).toNat (by
                  rw [hbind_pre.2.1]; exact Nat.lt_of_lt_of_le (hinv.st_nv ▸ hvid_lt)
                    (Nat.le_add_right _ _))
                rw [hbind_pre.2.2.2.2.2.1 _] at hds1
                simp only [show (cur.venv[idx]'hi).toNat < preSt.nextVid.toNat from
                  hinv.st_nv ▸ hvid_lt, ↓reduceIte] at hds1
                have := hinv.pre_inv.defScope_lt _ (hinv.st_nv ▸ hvid_lt)
                dsimp only [pB_item] at hsc_v; omega) hpa
        refine ⟨by dsimp only [tB]; rw [hbb_venv, hst0_eqs.1]; exact haux.1, haux.2.1,
          fun idx hi hlv => ?_⟩
        have heq_v : tB.venv = pushFreshVids0 pts.length st.nextVid cur.venv := by
          dsimp only [tB]; rw [hbb_venv, hst0_eqs.1]
        have hget : ∀ (l1 l2 : List UInt32) (he : l1 = l2) (i : Nat)
            (h1 : i < l1.length) (h2 : i < l2.length), l1[i]'h1 = l2[i]'h2 := by
          intro _ _ he _ _ _; cases he; rfl
        have hi' : idx < (pushFreshVids0 pts.length st.nextVid cur.venv).length := heq_v ▸ hi
        obtain ⟨hsl, hvs', ht', hcanon⟩ := haux.2.2 idx hi'
          (by rw [← hget _ _ heq_v idx hi hi']; exact hlv)
        have hsl' : (arrGetU0 st_b.vslot (tB.venv[idx]'hi)).toNat < σ'.length := by
          rw [hget _ _ heq_v idx hi hi']; exact hsl
        refine ⟨hsl', hvs', ht', ?_⟩
        rw [list_getElem_eq9 σ' hsl' hsl
          (congrArg (fun v => (arrGetU0 st_b.vslot v).toNat) (hget _ _ heq_v idx hi hi'))]
        exact hcanon
      have hgl_b : GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
          preRes.escaped st_b tB mB (pushTup xs vs) fnIdx mB.gl (⟨ty0ListToTy pts, J⟩ :: ls) := by
        refine ⟨?_, glEntrySem0_pushTys0 hgl hbb_nlo
            (by dsimp only [tB]; rw [hbb_venv, hst0_eqs.1]) rfl
            fun info hi => ⟨st.nextVid.toNat, fun w hw => by
              obtain ⟨_, _, _, _, _, hnv_o, _, _, _, _, hov_lt, _⟩ := hinfo_ok info hi
              exact Nat.lt_of_lt_of_le (hov_lt w hw) (Nat.le_trans (Nat.le_add_right _ _) hnv_o),
              fun v hv => by
                have hv' : v < bb.st.nextVid.toNat := by rw [hbb_nv, hst0_eqs.1]; omega
                exact (hrK_vsl v hv').trans (by rw [hbb_pres v (hst0_eqs.1 ▸ hv), hst0_eqs.2.2.1])⟩⟩
        refine ⟨Nat.le_refl _, hinv.ctrl_fn ▸ hdef_B, vs, pts.length,
          by dsimp only [tB, infoB, infoK]; rw [hbb_venv, hst0_eqs.1, pushFreshVids0_length]; omega,
          by dsimp only [tB, infoB, infoK]; rw [hbb_venv, hst0_eqs.1, pushFreshVids0_drop],
          by dsimp only [mB, infoB, infoK]; exact pushTys0_drop pts mCur.vT,
          pushTup_drop11 xs vs, J, rfl, fun xs' m'' hJ' s'' σ'' hfr'' hesc'' htup'' => ?_⟩
        have hesc''' : EscOuterAgree0 preRes.escaped bb.st.vslot infoK vs σ'' :=
          escOuterAgree0_vslot_congr (bound := bb.st.nextVid.toNat)
            (fun w hw => by
              rw [hbb_nv, hst0_eqs.1]; exact Nat.lt_of_lt_of_le (hvlt w hw) (Nat.le_add_right _ _))
            hrK_vsl hesc''
        have := hJ' s'' σ'' hfr'' hesc''' htup''
        dsimp only [infoB] at *; rw [hinv.ctrl_fn] at this; exact this
      exact hih (k1 + pK.length) nextSc'' preSt'' pB_item pw₂ seenJnz'' st_b rK.2 tB w₂ mB m₂
        (UInt32.ofNat ((fuel - 1).toNat - nodeCount0 cont)) s' σ' (pushTup xs vs)
        (⟨ty0ListToTy pts, J⟩ :: ls) m' hinv_b hlen_pw hlen_mw (by dsimp only [tB]; omega)
        hfuel_b hns_b hinf_b hwp_b hfr' hag_b hgl_b (blocksContracts0_mem hc_bs (pts, b) (.head _))
    have hwp_k := hwp (J, ()) hclosed
    dsimp only [pushConts0] at hwp_k
    have hinf_k : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
        (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 tK.node)) preRes.escaped
          { bb.st with revDirs := [] } ctrl1 [tK]).1.revDirs) [])).IsInfixAt
        (x64ScalarMach.prog h) k1 := hpK_inf
    have hag_k : SlotsAgree0 preRes.escaped preOut.2 bb.st pK_item tK mK.vT vs σ := by
      refine ⟨hag.1, hag.2.1, fun idx hi hlv => ?_⟩
      have hvid_lt : (tK.venv[idx]'hi).toNat < bb.st.nextVid.toNat := by
        rw [hbb_nv, hst0_eqs.1]
        exact Nat.lt_of_lt_of_le (hvlt _ (List.getElem_mem hi)) (Nat.le_add_right _ _)
      obtain ⟨h_old, hes, hvmem⟩ := hlive_k _ hvid_lt (by simpa [UInt32.ofNat_toNat] using hlv)
      obtain ⟨hsl, hvs, ht', hc⟩ := hag.2.2 idx hi (Or.inl ⟨hes, hvmem⟩)
      have hv_eq := hbb_pres (tK.venv[idx]'hi).toNat (hst0_eqs.1 ▸ h_old)
      rw [UInt32.ofNat_toNat, hst0_eqs.2.2.1] at hv_eq
      dsimp only [tK] at hv_eq ⊢; rw [hv_eq]
      exact ⟨hsl, hvs, ht', hc⟩
    have hgl_k : GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
        preRes.escaped bb.st tK mK vs fnIdx mK.gl (⟨ty0ListToTy pts, J⟩ :: ls) := by
      refine ⟨⟨Nat.le_refl _, hinv.ctrl_fn ▸ hdef_B, vs, 0, by simp [tK, infoK], rfl, rfl, rfl,
          J, rfl, fun xs' m'' hJ' s'' σ'' hfr'' hesc'' htup'' => ?_⟩,
        glEntrySem0_eq_vslot_nextSlot hgl hbb_nlo rfl rfl fun info hi =>
          ⟨st.nextVid.toNat, fun w hw => by
            obtain ⟨_, _, _, _, _, hnv_o, _, _, _, _, hov_lt, _⟩ := hinfo_ok info hi
            exact Nat.lt_of_lt_of_le (hov_lt w hw) (Nat.le_trans (Nat.le_add_right _ _) hnv_o),
            fun v hv => by rw [hbb_pres v (hst0_eqs.1 ▸ hv), hst0_eqs.2.2.1]⟩⟩
      have := hJ' s'' σ'' hfr'' hesc'' htup''
      rw [hinv.ctrl_fn] at this; exact this
    exact hih k1 (nextSc + 2) preOut.2 pK_item (pB_item :: pw₂) false bb.st ctrl1 tK (tB :: w₂) mK
      (mB :: m₂) (fuel - 1) s σ vs (⟨ty0ListToTy pts, J⟩ :: ls) mCurMem hinv_k
      (by simp [hlen_pw]) (by simp [hlen_mw]) (by dsimp only [tK]; omega)
      (by rw [hlsS_eq.2.2] at hfuel1; exact hfuel1)
      (by rw [← hlsS_eq.1, ← hlsS_eq.2.1, ← hlsS_eq.2.2]; exact hns_next)
      hinf_k hwp_k hfr hag_k hgl_k hc_k

end LeanQbe.T.Bootstrap0