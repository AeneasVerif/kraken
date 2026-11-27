module

public import LeanQbe.T.LeanLCNF.Sem.LowerSound1b
import LeanQbe.T.OpsLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.LeanLCNF.LcnfC0RtProofCommon

/-!
# Reference-Counting Simulation Combinators (`LowerSound1c`)

Companion to `LowerSound1b.lean` proving `LMMono` and `LExpr.wp` simulation combinators for:
1. `LMMono` monotonicity lemmas (`incRef_mono`, `decRefJ_mono`, `emitInc_mono`, `emitDec1_mono`,
   `emitDec_mono`)
2. `incRef_wp`, `emitInc_wp`, `decRefJ_wp`, `emitDec1_wp`, and `emitDec_wp`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.LeanLCNF.RtProof
open LeanQbe.T.Frontend.C0
open Std.ExtHashMap

/-! ## 1. `LMMono` Monotonicity Lemmas for RC Builders -/

private theorem pure_mono {α : Type} (a : α) : LMMono (pure a : LM α) := by
  intro n a' n' h
  rw [lm_pure_run] at h
  injection h with hp
  have hn : n = n' := congrArg Prod.snd hp
  subst hn
  exact Nat.le_refl _

theorem incRef_mono {x : LArg} {cnt : Nat} {k : LM LExpr} (hk : LMMono k) :
    LMMono (incRef x cnt k) := by
  unfold incRef
  refine loadAt_mono fun _ => cmpOp_mono fun _ => op1_mono fun _ => ?_
  split
  · exact op1_mono fun _ => storeAt_mono hk
  · exact op1_mono fun _ => op1_mono fun _ => storeAt_mono hk

theorem emitInc_mono {x : LArg} {ty : LcTy} {cnt : Nat} {chk : Bool} {k : LM LExpr}
    (hk : LMMono k) : LMMono (emitInc x ty cnt chk k) := by
  unfold emitInc
  split
  · exact hk
  · split
    · exact incRef_mono hk
    · refine isScalarObj_mono fun _ => withJoin_mono (fun _ => hk) fun _ => ?_
      intro n e n' hrun
      rw [lm_bind_run] at hrun
      rcases hrun with ⟨eInc, n1, heInc, hpure⟩
      rw [lm_pure_run] at hpure
      injection hpure with hpr
      have hn1 : n1 = n' := congrArg Prod.snd hpr
      subst hn1
      exact incRef_mono (pure_mono _) n eInc n1 heInc

theorem decRefJ_mono {rt x : LArg} {j : LExpr} : LMMono (decRefJ rt x j) := by
  unfold decRefJ
  refine loadAt_mono fun _ => cmpOp_mono fun _ => fun n e n' hrun => ?_
  rw [lm_bind_run] at hrun
  rcases hrun with ⟨cold, n1, hcold, hrest⟩
  rw [lm_bind_run] at hrest
  rcases hrest with ⟨hot, n2, hhot, hpure⟩
  rw [lm_pure_run] at hpure
  injection hpure with hpr
  have hn2 : n2 = n' := congrArg Prod.snd hpr
  subst hn2
  have h1 : n ≤ n1 := call0_mono (pure_mono j) n cold n1 hcold
  have h2 : n1 ≤ n2 :=
    cmpOp_mono (fun _ => op1_mono fun _ => op1_mono fun _ => storeAt_mono (pure_mono j))
      n1 hot n2 hhot
  exact Nat.le_trans h1 h2

theorem emitDec1_mono {rt x : LArg} {ty : LcTy} {chk : Bool} {k : LM LExpr} (hk : LMMono k) :
    LMMono (emitDec1 rt x ty chk k) := by
  unfold emitDec1
  split
  · exact hk
  · split
    · exact withJoin_mono (fun _ => hk) fun _ => decRefJ_mono
    · refine isScalarObj_mono fun _ => withJoin_mono (fun _ => hk) fun _ => ?_
      intro n e n' hrun
      rw [lm_bind_run] at hrun
      rcases hrun with ⟨eDec, n1, heDec, hpure⟩
      rw [lm_pure_run] at hpure
      injection hpure with hpr
      have hn1 : n1 = n' := congrArg Prod.snd hpr
      subst hn1
      exact decRefJ_mono n eDec n1 heDec

theorem emitDec_mono {rt x : LArg} {ty : LcTy} {chk : Bool} {k : LM LExpr} (hk : LMMono k) :
    ∀ cnt, LMMono (emitDec rt x ty cnt chk k)
  | 0 => hk
  | cnt' + 1 => emitDec1_mono (emitDec_mono hk cnt')

/-! ## 2. `incRef` and `emitInc` Combinators -/

theorem incRef_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {xArg : LArg} {cnt : Nat} {k : LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt vx : BitVec 64}
    {σ : HState} {R : Mem 64 → Prop} {idx : Nat} (hidx : idx < σ.objs.length)
    (hrun : (incRef xArg cnt k).run n = .ok (e, n'))
    (hx : LArg.eval ρ i64 xArg = some vx) (hnx : argIdsBelow xArg n)
    (haddr : σ.objs[idx].addr = vx) (hwf : σ.objs[idx].Wf)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hk : ∀ (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nr : Nat) (m' : Mem 64),
      n ≤ nr → k.run nr = .ok (ek, n') → VEnvAgreeBelow n ρ' ρ →
      let o := σ.objs[idx]
      let rc' := if 0 < o.rc.toInt then o.rc + BitVec.ofNat 32 cnt else o.rc
      let σ' : HState :=
        { st := σ.st, objs := σ.objs.set idx (o.withRc rc'), scr := σ.scr, scrLimbs := σ.scrLimbs }
      HInv rt σ' → (σ'.mem rt ⋆ R) m' → LExpr.wp Γ QT XT ek ρ' J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  let o := σ.objs[idx]
  have haddrO : o.addr = vx := haddr
  let heapRest : Mem 64 → Prop :=
    fullRtInv rt σ.st σ.scr σ.scrLimbs ⋆
      (lcnfHeap (σ.objs.take idx) ⋆ lcnfHeap (σ.objs.drop (idx + 1))) ⋆ R
  have hmObj : (lcnfObjMem o ⋆ heapRest) mem := by
    rw [HState.mem.eq_1, lcnfHeap_focus σ.objs hidx] at hm
    exact sep_cast hm (by dsimp only [heapRest]; ac_rfl)
  have hload : loadVal mem i32 (vx + BitVec.ofNat 64 0) = some o.rc := by
    have h0 := lcnfObjMem_load_i32_rc hmObj
    rw [haddrO] at h0
    simpa using h0
  unfold incRef at hrun
  refine lm_loadAt_wp hrun hx hnx hload ?_
  intro rcArg ek1 ρ1 n1 hn1 hek1 hrcId hagr1 hrcEv
  have hpos : CmpOp.evalBits .sgt o.rc (BitVec.ofNat 32 0) = decide (0 < o.rc.toInt) := by
    dsimp [CmpOp.evalBits]
    simp [BitVec.slt]
  refine cmpOp_wp hek1 hrcEv (LArg.eval_imm_self ρ1 i32 0#32) ?_
  intro posArg ek2 ρ2 hek2 _ hagr2 hposEv
  rw [hpos] at hposEv
  refine op1_wp hek2 (evalArgs_cons hposEv (evalArgs_nil ρ2)) ?_
  intro ek3 hek3 hbId
  rw [OpCode.wp_ofBool]
  let bVal : BitVec 32 := BitVec.ofNat 32 (decide (0 < o.rc.toInt)).toNat
  have hbEv : LArg.eval (ρ2.set (n1 + 1) i32 bVal) i32
      (vArg { id := n1 + 1, name := "", ty := i32 }) =
      some (if 0 < o.rc.toInt then 1#32 else 0#32) := by
    have hv := LArg.eval_vArg_set_self ρ2 { id := n1 + 1, name := "", ty := i32 } bVal
    by_cases hgt : 0 < o.rc.toInt <;> simpa [bVal, hgt] using hv
  have hagr3 : VEnvAgreeBelow n (ρ2.set (n1 + 1) i32 bVal) ρ :=
    ((VEnvAgreeBelow.set (Nat.le_refl _) _ _).mono (by omega : n ≤ n1 + 1)).trans
      ((hagr2.mono (by omega : n ≤ n1)).trans hagr1)
  have hbId' : argIdsBelow (vArg { id := n1 + 1, name := "", ty := i32 }) (n1 + 2) := hbId
  let ρ3 := ρ2.set (n1 + 1) i32 bVal
  have hfinish : ∀ (dArg : LArg) (ekD : LExpr) (ρD : Frontend.C0.VEnv) (nD : Nat),
      n1 + 2 ≤ nD →
      (op1 i32 (.add i32) [rcArg, dArg] fun rc' => storeAt i32 rc' xArg 0 k).run nD =
        .ok (ekD, n') →
      argIdsBelow dArg nD → VEnvAgreeBelow (n1 + 1) ρD ρ2 →
      LArg.eval ρD i32 dArg = some (if 0 < o.rc.toInt then BitVec.ofNat 32 cnt else 0#32) →
      LExpr.wp Γ QT XT ekD ρD J mem := by
    intro dArg ekD ρD nD hnD hekD hdId hagrD hdEv
    have hrcD : LArg.eval ρD i32 rcArg = some o.rc := by
      have hagree : VEnvAgreeBelow n1 ρD ρ1 :=
        (hagrD.mono (by omega : n1 ≤ n1 + 1)).trans hagr2
      exact (hagree.eval hrcId).trans hrcEv
    have hagrD0 : VEnvAgreeBelow n ρD ρ :=
      (hagrD.mono (by omega : n ≤ n1 + 1)).trans ((hagr2.mono (by omega : n ≤ n1)).trans hagr1)
    refine op1_wp hekD (evalArgs_cons hrcD (evalArgs_cons hdEv (evalArgs_nil ρD))) ?_
    intro ek4 hek4 hrcpId
    rw [OpCode.wp_add]
    simp only [lift2]
    let rc' := if 0 < o.rc.toInt then o.rc + BitVec.ofNat 32 cnt else o.rc
    have hrcEq : o.rc + (if 0 < o.rc.toInt then BitVec.ofNat 32 cnt else 0#32) = rc' := by
      by_cases hgt : 0 < o.rc.toInt <;> simp [rc', hgt]
    let ρ4 := ρD.set nD i32 (o.rc + (if 0 < o.rc.toInt then BitVec.ofNat 32 cnt else 0#32))
    have hagr4 : VEnvAgreeBelow n ρ4 ρ :=
      ((VEnvAgreeBelow.set (Nat.le_refl _) _ _).mono (by omega : n ≤ nD)).trans hagrD0
    have hrcpEv : LArg.eval ρ4 i32 (vArg { id := nD, name := "", ty := i32 }) = some rc' := by
      rw [← hrcEq]
      exact LArg.eval_vArg_set_self ρD { id := nD, name := "", ty := i32 } _
    have hst := lcnfObjMem_store_i32_rc rc' hwf hmObj
    have haddr0 : o.addr = vx + BitVec.ofNat 64 0 := by simp [haddrO]
    rw [haddr0] at hst
    refine storeAt_wp hek4 hrcpEv hrcpId ((hagr4.eval hnx).trans hx)
      (argIdsBelow_mono (by omega) hnx) hst.1 ?_
    intro ek5 ρ5 nk hnk hek5 hagr5
    have hagrOut : VEnvAgreeBelow n ρ5 ρ := (hagr5.mono (by omega)).trans hagr4
    let σ' : HState :=
      { st := σ.st, objs := σ.objs.set idx (o.withRc rc'), scr := σ.scr, scrLimbs := σ.scrLimbs }
    have hmPost : (σ'.mem rt ⋆ R) (storeMem mem i32 (vx + BitVec.ofNat 64 0) rc') := by
      rw [HState.mem.eq_1, lcnfHeap_set σ.objs hidx (o.withRc rc')]
      exact sep_cast hst.2 (by dsimp only [heapRest, σ']; ac_rfl)
    exact hk ek5 ρ5 nk _ (by omega) hek5 hagrOut hinv hmPost
  by_cases h1 : (cnt == 1) = true
  · have hcnt1 : cnt = 1 := beq_iff_eq.mp h1
    rw [ite_eq_left h1] at hek3
    refine hfinish _ ek3 ρ3 (n1 + 2) (Nat.le_refl _) hek3 hbId'
      (VEnvAgreeBelow.set (Nat.le_refl _) _ _) ?_
    subst hcnt1; exact hbEv
  · rw [ite_eq_right h1] at hek3
    refine op1_wp hek3 (evalArgs_cons hbEv (evalArgs_cons (LArg.eval_imm_self ρ3 i32 _)
      (evalArgs_nil ρ3))) ?_
    intro ek4 hek4 hdId
    rw [OpCode.wp_mul]
    simp only [lift2]
    let dVal := (if 0 < o.rc.toInt then 1#32 else 0#32) * BitVec.ofNat 32 cnt
    have hdEq : dVal = if 0 < o.rc.toInt then BitVec.ofNat 32 cnt else 0#32 := by
      by_cases hgt : 0 < o.rc.toInt <;> simp [dVal, hgt]
    let ρ4 := ρ3.set (n1 + 2) i32 dVal
    have hagr4 : VEnvAgreeBelow (n1 + 1) ρ4 ρ2 :=
      ((VEnvAgreeBelow.set (Nat.le_refl _) _ _).mono (by omega : n1 + 1 ≤ n1 + 2)).trans
        (VEnvAgreeBelow.set (Nat.le_refl _) _ _)
    refine hfinish _ ek4 ρ4 (n1 + 3) (Nat.le_succ _) hek4 hdId hagr4 ?_
    rw [← hdEq]
    exact LArg.eval_vArg_set_self ρ3 { id := n1 + 2, name := "", ty := i32 } dVal

theorem emitInc_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {xArg : LArg} {ty : LcTy} {cnt : Nat} {chk : Bool} {k : LM LExpr}
    {n n' : Nat} {e : LExpr} {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64}
    {rt vx : BitVec 64} {σ : HState} {R : Mem 64 → Prop}
    (hrun : (emitInc xArg ty cnt chk k).run n = .ok (e, n'))
    (hkMono : LMMono k)
    (hx : LArg.eval ρ i64 xArg = some vx) (hnx : argIdsBelow xArg n)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hpre :
      if (!ty.needsRc || cnt == 0) = true then
        ∀ ek, k.run n = .ok (ek, n') → LExpr.wp Γ QT XT ek ρ J mem
      else if (vx &&& 1#64) ≠ 0#64 then
        chk = true ∧ ty = LcTy.tobject ∧
          ∀ (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk : Nat),
            n ≤ nr → k.run nr = .ok (ek, nk) →
            VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
            LExpr.wp Γ QT XT ek ρ' J' mem
      else
        ∃ (idx : Nat) (hidx : idx < σ.objs.length),
          let o := σ.objs[idx]
          o.addr = vx ∧ o.Wf ∧
            let rc' := if 0 < o.rc.toInt then o.rc + BitVec.ofNat 32 cnt else o.rc
            let σ' : HState :=
              { st := σ.st, objs := σ.objs.set idx (o.withRc rc'),
                scr := σ.scr, scrLimbs := σ.scrLimbs }
            ∀ (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk : Nat) (m' : Mem 64),
              n ≤ nr → k.run nr = .ok (ek, nk) →
              VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
              HInv rt σ' → (σ'.mem rt ⋆ R) m' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold emitInc at hrun
  by_cases hskip : (!ty.needsRc || cnt == 0) = true
  · rw [ite_eq_left hskip] at hrun hpre
    exact hpre e hrun
  · rw [ite_eq_right hskip] at hrun hpre
    by_cases hdir : (!chk || ty == LcTy.object) = true
    · rw [ite_eq_left hdir] at hrun
      have hscFalse : ¬ ((vx &&& 1#64) ≠ 0#64) := by
        intro hne
        rw [ite_eq_left hne] at hpre
        rcases hpre with ⟨rfl, rfl, _⟩
        cases hdir
      rw [ite_eq_right hscFalse] at hpre
      rcases hpre with ⟨idx, hidx, haddr, hwf, hk⟩
      exact incRef_wp hidx hrun hx hnx haddr hwf hinv hm
        (fun ek ρ' nr m' hnr hek hagr =>
          hk ek ρ' J nr n' m' hnr hek hagr (JEnvAgreeBelow.refl n J))
    · rw [ite_eq_right hdir] at hrun
      refine isScalarObj_wp hrun hx ?_
      intro sArg ek1 ρ1 hek1 _ hagr1 hsEv
      let Inv : Unit → Mem 64 → Prop := fun _ m1 =>
        ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m1 ∧
          (if (vx &&& 1#64) ≠ 0#64 then σ' = σ ∧ m1 = mem
           else
             ∃ (idx : Nat) (hidx : idx < σ.objs.length),
               let o := σ.objs[idx]
               o.addr = vx ∧
                 let rc' := if 0 < o.rc.toInt then o.rc + BitVec.ofNat 32 cnt else o.rc
                 σ' = { st := σ.st, objs := σ.objs.set idx (o.withRc rc'),
                        scr := σ.scr, scrLimbs := σ.scrLimbs })
      refine withJoin_wp (Inv := Inv) hek1 hkMono ?_ ?_
      · intro ps blk n2 J' hps hblk hJagr () m1 ⟨σ', hinv', hm', hrel⟩ hagr _ _
        have hk' : k.run (n + 2 + 1) = .ok (blk, n2) := by
          subst hps; exact hblk
        have hagrAll : VEnvAgreeBelow n (ρ1.bind ps [] ()) ρ :=
          (hagr.mono (by omega : n ≤ n + 2)).trans hagr1
        have hJagrAll : JEnvAgreeBelow n J' J := hJagr.mono (by omega : n ≤ n + 2)
        by_cases hsc : (vx &&& 1#64) ≠ 0#64
        · rw [ite_eq_left hsc] at hpre hrel
          rcases hrel with ⟨rfl, rfl⟩
          exact hpre.2.2 blk (ρ1.bind ps [] ()) J' (n + 2 + 1) n2 (by omega) hk' hagrAll
            hJagrAll
        · rw [ite_eq_right hsc] at hpre hrel
          rcases hpre with ⟨idx, hidx, haddr, hwf, hkPre⟩
          rcases hrel with ⟨idx', hidx', haddr', rfl⟩
          have heqIdx : idx' = idx := by
            have hltNe : ∀ i j : Nat, i < j → (hi : i < σ.objs.length) →
                (hj : j < σ.objs.length) → σ.objs[i].addr ≠ σ.objs[j].addr := by
              intro i j hij _ hj
              have hmTmp :
                  (lcnfHeap σ.objs ⋆ (fullRtInv rt σ.st σ.scr σ.scrLimbs ⋆ R)) mem := by
                rw [HState.mem.eq_1] at hm; exact sep_cast hm (by ac_rfl)
              rw [lcnfHeap_focus σ.objs hj, lcnfObjMem_eq_header_body, sep_assoc] at hmTmp
              have hmCell :
                  (cell64 σ.objs[j].addr σ.objs[j].header ⋆ lcnfHeap (σ.objs.take j) ⋆
                    (lcnfObjBody σ.objs[j] ⋆ lcnfHeap (σ.objs.drop (j + 1)) ⋆
                      (fullRtInv rt σ.st σ.scr σ.scrLimbs ⋆ R))) mem :=
                sep_cast hmTmp (by ac_rfl)
              have hiTake : i < (σ.objs.take j).length := by simp [List.length_take]; omega
              have hmem : σ.objs[i] ∈ σ.objs.take j := by
                have hg : (σ.objs.take j)[i]'hiTake = σ.objs[i] := List.getElem_take
                rw [← hg]
                exact List.getElem_mem hiTake
              exact lcnfHeap_disj_of_cell64 hmCell _ hmem
            rcases Nat.lt_trichotomy idx' idx with hlt | heq | hgt
            · exact False.elim (hltNe idx' idx hlt hidx' hidx (haddr'.trans haddr.symm))
            · exact heq
            · exact False.elim (hltNe idx idx' hgt hidx hidx' (haddr.trans haddr'.symm))
          subst heqIdx
          exact hkPre blk (ρ1.bind ps [] ()) J' (n + 2 + 1) n2 m1 (by omega) hk' hagrAll
            hJagrAll hinv' hm'
      · intro j body n2 J' hn2 hbody _ hjok
        rw [lm_bind_run] at hbody
        rcases hbody with ⟨eInc, n3, heInc, hpure⟩
        rw [lm_pure_run] at hpure
        injection hpure with hpure'
        have hbod : LExpr.jnz sArg (j []) eInc = body := congrArg Prod.fst hpure'
        have hn3 : n3 = n' := congrArg Prod.snd hpure'
        subst hbod; subst hn3
        refine wp_jnz hsEv ?_ ?_
        · intro htrue
          have hsc : (vx &&& 1#64) ≠ 0#64 := of_decide_eq_true htrue
          refine hjok J' [] ρ1 mem () (JEnvAgreeBelow.refl _ J') rfl ?_
          exact ⟨σ, hinv, hm, by rw [ite_eq_left hsc]; exact ⟨rfl, rfl⟩⟩
        · intro hfalse
          have hsc : ¬ ((vx &&& 1#64) ≠ 0#64) := of_decide_eq_false hfalse
          rw [ite_eq_right hsc] at hpre
          rcases hpre with ⟨idx, hidx, haddr, hwf, _⟩
          have hnx2 : argIdsBelow xArg n2 := argIdsBelow_mono (by omega) hnx
          have hx2 : LArg.eval ρ1 i64 xArg = some vx := (hagr1.eval hnx).trans hx
          exact incRef_wp hidx heInc hx2 hnx2 haddr hwf hinv hm
            (fun ek3 ρ3 nr3 m' _ hek3 _ hinv' hm' => by
              rw [lm_pure_run] at hek3
              injection hek3 with hek3p
              have hekEq : j [] = ek3 := congrArg Prod.fst hek3p
              subst hekEq
              refine hjok J' [] ρ3 m' () (JEnvAgreeBelow.refl _ J') rfl ?_
              refine ⟨_, hinv', hm', ?_⟩
              rw [ite_eq_right hsc]
              exact ⟨idx, hidx, haddr, rfl⟩)

/-! ## 3. `decRefJ`, `emitDec1`, and `emitDec` Combinators -/

theorem decRefJ_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg xArg : LArg} {j : LExpr}
    {n n' : Nat} {e : LExpr} {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64}
    {rt vx : BitVec 64} {ty : LcTy} {chk : Bool} {σ : HState} {R : Mem 64 → Prop}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (decRefJ rtArg xArg j).run n = .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (hx : LArg.eval ρ i64 xArg = some vx) (hnx : argIdsBelow xArg n)
    (hnotSc : (vx &&& 1#64) = 0#64) (htyRc : ty.needsRc = true)
    (hpre : HDec1Pre vx ty chk σ)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hj : ∀ (ρ' : Frontend.C0.VEnv) (m' : Mem 64) (σ' : HState),
      VEnvAgreeBelow n ρ' ρ → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      HDec1Rel vx ty σ σ' → LExpr.wp Γ QT XT j ρ' J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  have hpre' : ∃ o ∈ σ.objs, o.addr = vx ∧ o.Wf ∧
      (o.rc = 1#32 → σ.objs.length ≤ σ.st.workCap ∧ (∀ obj ∈ σ.objs, obj.Wf) ∧
        lcnfHeapClosed σ.objs ∧ RcSound vx σ.objs) := by
    simpa [HDec1Pre, htyRc, hnotSc] using hpre
  rcases hpre' with ⟨o, ho, haddr, hwf, h1pre⟩
  obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp ho
  let o := σ.objs[idx]
  have haddrO : o.addr = vx := haddr
  let heapRest : Mem 64 → Prop :=
    fullRtInv rt σ.st σ.scr σ.scrLimbs ⋆
      (lcnfHeap (σ.objs.take idx) ⋆ lcnfHeap (σ.objs.drop (idx + 1))) ⋆ R
  have hmObj : (lcnfObjMem o ⋆ heapRest) mem := by
    rw [HState.mem.eq_1, lcnfHeap_focus σ.objs hidx] at hm
    exact sep_cast hm (by dsimp only [heapRest]; ac_rfl)
  have hload : loadVal mem i32 (vx + BitVec.ofNat 64 0) = some o.rc := by
    have h0 := lcnfObjMem_load_i32_rc hmObj
    rw [haddrO] at h0
    simpa using h0
  unfold decRefJ at hrun
  refine lm_loadAt_wp hrun hx hnx hload ?_
  intro rcArg ek1 ρ1 n1 hn1 hek1 hrcId hagr1 hrcEv
  refine cmpOp_wp hek1 hrcEv (LArg.eval_imm_self ρ1 i32 1#32) ?_
  intro is1Arg ek2 ρ2 hek2 _ hagr2 his1Ev
  rw [lm_bind_run] at hek2
  rcases hek2 with ⟨cold, n2, hcold, hrest2⟩
  rw [lm_bind_run] at hrest2
  rcases hrest2 with ⟨hot, n3, hhot, hpure⟩
  rw [lm_pure_run] at hpure
  injection hpure with hpr
  have heq : LExpr.jnz is1Arg cold hot = ek2 := congrArg Prod.fst hpr
  subst heq
  have his1Eq : CmpOp.evalBits .eq o.rc 1#32 = decide (o.rc = 1#32) := rfl
  rw [his1Eq] at his1Ev
  refine wp_jnz his1Ev ?_ ?_
  · intro htrue
    have hrc1 : o.rc = 1#32 := of_decide_eq_true htrue
    obtain ⟨hcap, hallWf, hcl, hrcSound⟩ := h1pre hrc1
    have hsig : ("lcnf_dec_ref_cold", [i64, i64], []) ∈ rtCoreCallSigs := by decide
    let scrFrame : Mem 64 → Prop :=
      cell64 (rt + 33672#64) σ.scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 σ.scrLimbs.length) ⋆
      array64 σ.scr σ.scrLimbs ⋆ R
    have hmRt : (rtC0Inv rt σ.st ⋆ lcnfHeap σ.objs ⋆ scrFrame) mem := by
      rw [hstate_mem_unfold] at hm
      exact sep_cast hm (by dsimp only [scrFrame]; ac_rfl)
    let P : Post [] := fun () m' =>
      ∃ st' objs', st'.PreservesMeta σ.st ∧ st'.rem = σ.st.rem ∧ DecColdRel vx σ.objs objs' ∧
        (rtC0Inv rt st' ⋆ lcnfHeap objs' ⋆ scrFrame) m'
    let E : XPost := fun _ _ _ _ => False
    have hspec : lcnfDecRefColdSpec (rt, vx, ()) mem P E :=
      ⟨hnotSc, σ.st, σ.objs, scrFrame, hcap, hmRt,
        ⟨o, List.getElem_mem hidx, haddr, hrc1⟩, hallWf, hcl, hrcSound,
        fun st' objs' m' hpm hrem hrel hm' => ⟨st', objs', hpm, hrem, hrel, hm'⟩⟩
    have hagr21 : VEnvAgreeBelow n ρ2 ρ := (hagr2.mono (by omega : n ≤ n1)).trans hagr1
    have hrt2 : LArg.eval ρ2 i64 rtArg = some rt := (hagr21.eval hnrt).trans hrt
    have hx2 : LArg.eval ρ2 i64 xArg = some vx := (hagr21.eval hnx).trans hx
    refine call0_wp hcold (evalArgs_cons hrt2 (evalArgs_cons hx2 (evalArgs_nil ρ2)))
      (hΓ.rt hsig (rtC0CoreEnv_lcnf_dec_ref_cold hspec)) (fun _ _ _ _ hf => False.elim hf) ?_
    intro ekC hekC m' ⟨st', objs', hpm, hrem, hrel, hm'⟩
    rw [lm_pure_run] at hekC
    injection hekC with hcp
    have hec : j = ekC := congrArg Prod.fst hcp
    subst hec
    let σ' : HState := { st := st', objs := objs', scr := σ.scr, scrLimbs := σ.scrLimbs }
    have hmOut : (σ'.mem rt ⋆ R) m' := by
      rw [hstate_mem_unfold]
      exact sep_cast hm' (by dsimp only [scrFrame]; ac_rfl)
    have hDecRel : HDec1Rel vx ty σ σ' := by
      simp only [HDec1Rel, htyRc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hnotSc,
        ne_eq, not_true_eq_false]
      exact Or.inr (Or.inr ⟨hpm, hrem, rfl, rfl, hrel⟩)
    exact hj ρ2 m' σ' hagr21 (hinv_of_preservesMeta hinv hpm) hmOut hDecRel
  · intro hfalse
    have hrcNe1 : o.rc ≠ 1#32 := of_decide_eq_false hfalse
    have hcoldMono : n1 + 1 ≤ n2 := call0_mono (pure_mono j) (n1 + 1) cold n2 hcold
    have hagr20 : VEnvAgreeBelow n ρ2 ρ := (hagr2.mono (by omega : n ≤ n1)).trans hagr1
    have hrc2 : LArg.eval ρ2 i32 rcArg = some o.rc := (hagr2.eval hrcId).trans hrcEv
    have hgt : CmpOp.evalBits .sgt o.rc (BitVec.ofNat 32 1) = decide (1 < o.rc.toInt) := by
      dsimp [CmpOp.evalBits]; simp [BitVec.slt]
    refine cmpOp_wp hhot hrc2 (LArg.eval_imm_self ρ2 i32 1#32) ?_
    intro gtArg ek3 ρ3 hek3 hgtId hagr3 hgtEv
    rw [hgt] at hgtEv
    refine op1_wp hek3 (evalArgs_cons hgtEv (evalArgs_nil ρ3)) ?_
    intro ek4 hek4 hbId
    rw [OpCode.wp_ofBool]
    let bVal : BitVec 32 := BitVec.ofNat 32 (decide (1 < o.rc.toInt)).toNat
    let ρ4 := ρ3.set (n2 + 1) i32 bVal
    have hagr43 : VEnvAgreeBelow (n2 + 1) ρ4 ρ3 := VEnvAgreeBelow.set (Nat.le_refl _) _ _
    have hagr40 : VEnvAgreeBelow n ρ4 ρ :=
      ((hagr43.mono (by omega : n ≤ n2 + 1)).trans (hagr3.mono (by omega : n ≤ n2))).trans hagr20
    have hrc4 : LArg.eval ρ4 i32 rcArg = some o.rc := by
      have h1 : VEnvAgreeBelow n1 ρ4 ρ1 :=
        ((hagr43.mono (by omega : n1 ≤ n2 + 1)).trans
          (hagr3.mono (by omega : n1 ≤ n2))).trans hagr2
      exact (h1.eval hrcId).trans hrcEv
    have hb4 : LArg.eval ρ4 i32 (vArg { id := n2 + 1, name := "", ty := i32 }) = some bVal :=
      LArg.eval_vArg_set_self ρ3 { id := n2 + 1, name := "", ty := i32 } bVal
    refine op1_wp hek4 (evalArgs_cons hrc4 (evalArgs_cons hb4 (evalArgs_nil ρ4))) ?_
    intro ek5 hek5 hrcpId
    rw [OpCode.wp_sub]
    simp only [lift2]
    let rc' := o.rc - bVal
    let ρ5 := ρ4.set (n2 + 2) i32 rc'
    have hagr54 : VEnvAgreeBelow (n2 + 2) ρ5 ρ4 := VEnvAgreeBelow.set (Nat.le_refl _) _ _
    have hagr50 : VEnvAgreeBelow n ρ5 ρ :=
      (hagr54.mono (by omega : n ≤ n2 + 2)).trans hagr40
    have hrcpEv : LArg.eval ρ5 i32 (vArg { id := n2 + 2, name := "", ty := i32 }) = some rc' :=
      LArg.eval_vArg_set_self ρ4 { id := n2 + 2, name := "", ty := i32 } rc'
    have hst := lcnfObjMem_store_i32_rc rc' hwf hmObj
    have haddr0 : o.addr = vx + BitVec.ofNat 64 0 := by simp [haddrO]
    rw [haddr0] at hst
    refine storeAt_wp hek5 hrcpEv hrcpId ((hagr50.eval hnx).trans hx)
      (argIdsBelow_mono (by omega) hnx) hst.1 ?_
    intro ek6 ρ6 nk hnk hek6 hagr6
    rw [lm_pure_run] at hek6
    injection hek6 with hekp
    have he6 : j = ek6 := congrArg Prod.fst hekp
    subst he6
    have hagrOut : VEnvAgreeBelow n ρ6 ρ := (hagr6.mono (by omega : n ≤ n2 + 3)).trans hagr50
    by_cases hgt1 : 1 < o.rc.toInt
    · have hb1 : bVal = 1#32 := by simp [bVal, hgt1]
      have hrcSub : rc' = o.rc - 1#32 := by simp [rc', hb1]
      let σ' : HState :=
        { st := σ.st, objs := σ.objs.set idx (o.withRc (o.rc - 1#32)),
          scr := σ.scr, scrLimbs := σ.scrLimbs }
      have hmOut : (σ'.mem rt ⋆ R) (storeMem mem i32 (vx + BitVec.ofNat 64 0) rc') := by
        rw [hrcSub] at hst ⊢
        rw [HState.mem.eq_1, lcnfHeap_set σ.objs hidx (o.withRc (o.rc - 1#32))]
        exact sep_cast hst.2 (by dsimp only [heapRest, σ']; ac_rfl)
      have hDecRel : HDec1Rel vx ty σ σ' := by
        simp only [HDec1Rel, htyRc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hnotSc,
          ne_eq, not_true_eq_false]
        exact Or.inr (Or.inl ⟨idx, hidx, haddr, hgt1, rfl⟩)
      exact hj ρ6 _ σ' hagrOut hinv hmOut hDecRel
    · have hrc0Int : o.rc.toInt = 0 := by
        have h0 : 0 ≤ o.rc.toInt := hwf.2.2.1
        have hne1 : o.rc.toInt ≠ 1 := fun h => hrcNe1 (BitVec.eq_of_toInt_eq (by simpa using h))
        omega
      have hrc0 : o.rc = 0#32 := BitVec.eq_of_toInt_eq (by simpa using hrc0Int)
      have hb0 : bVal = 0#32 := by simp [bVal, hgt1]
      have hrcSame : rc' = 0#32 := by simp [rc', hrc0, hb0]
      have hmOut : (σ.mem rt ⋆ R) (storeMem mem i32 (vx + BitVec.ofNat 64 0) rc') := by
        rw [hrcSame] at hst ⊢
        have hwith0 : o.withRc 0#32 = o := by rw [← hrc0]; exact lcnfObj_withRc_self o
        rw [hwith0] at hst
        rw [HState.mem.eq_1, lcnfHeap_focus σ.objs hidx]
        exact sep_cast hst.2 (by dsimp only [heapRest, o]; ac_rfl)
      have hDecRel : HDec1Rel vx ty σ σ := by
        simp only [HDec1Rel, htyRc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hnotSc,
          ne_eq, not_true_eq_false]
        exact Or.inl ⟨o, List.getElem_mem hidx, haddr, hrc0, trivial⟩
      exact hj ρ6 _ σ hagrOut hinv hmOut hDecRel

theorem emitDec1_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg xArg : LArg} {ty : LcTy} {chk : Bool}
    {k : LM LExpr} {n n' : Nat} {e : LExpr} {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64}
    {rt vx : BitVec 64} {σ : HState} {R : Mem 64 → Prop}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (emitDec1 rtArg xArg ty chk k).run n = .ok (e, n'))
    (hkMono : LMMono k)
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (hx : LArg.eval ρ i64 xArg = some vx) (hnx : argIdsBelow xArg n)
    (hpre : HDec1Pre vx ty chk σ)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hk : ∀ (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk : Nat)
        (σ' : HState) (m' : Mem 64),
      n ≤ nr → k.run nr = .ok (ek, nk) →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      HInv rt σ' → (σ'.mem rt ⋆ R) m' → HDec1Rel vx ty σ σ' →
      LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold emitDec1 at hrun
  by_cases hskip : (!ty.needsRc) = true
  · rw [ite_eq_left hskip] at hrun
    have hrel : HDec1Rel vx ty σ σ := by simp [HDec1Rel, hskip]
    exact hk e ρ J n n' σ mem (Nat.le_refl n) hrun (VEnvAgreeBelow.refl n ρ)
      (JEnvAgreeBelow.refl n J) hinv hm hrel
  · rw [ite_eq_right hskip] at hrun
    have htyRc : ty.needsRc = true := by cases hc : ty.needsRc <;> simp_all
    let Inv : Unit → Mem 64 → Prop := fun _ m1 =>
      ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m1 ∧ HDec1Rel vx ty σ σ'
    by_cases hdir : (!chk || ty == LcTy.object) = true
    · rw [ite_eq_left hdir] at hrun
      have hnotSc : (vx &&& 1#64) = 0#64 := by
        by_cases hsc : (vx &&& 1#64) = 0#64
        · exact hsc
        · have hp' : chk = true ∧ ty = LcTy.tobject := by
            simpa [HDec1Pre, hskip, hsc] using hpre
          rcases hp' with ⟨rfl, rfl⟩
          cases hdir
      refine withJoin_wp (Inv := Inv) hrun hkMono ?_ ?_
      · intro ps blk n2 J' hps hblk hJagr () m1 ⟨σ', hinv', hm', hrel⟩ hagr _ _
        have hk' : k.run (n + 1) = .ok (blk, n2) := by subst hps; exact hblk
        exact hk blk (ρ.bind ps [] ()) J' (n + 1) n2 σ' m1 (by omega) hk' hagr
          hJagr hinv' hm' hrel
      · intro j body n2 J' _ hbody _ hjok
        refine decRefJ_wp hΓ hbody hrt (argIdsBelow_mono (by omega) hnrt) hx
          (argIdsBelow_mono (by omega) hnx) hnotSc htyRc hpre hinv hm ?_
        intro ρ' m' σ' _ hinv' hm' hrel
        exact hjok J' [] ρ' m' () (JEnvAgreeBelow.refl _ J') rfl ⟨σ', hinv', hm', hrel⟩
    · rw [ite_eq_right hdir] at hrun
      refine isScalarObj_wp hrun hx ?_
      intro sArg ek1 ρ1 hek1 _ hagr1 hsEv
      refine withJoin_wp (Inv := Inv) hek1 hkMono ?_ ?_
      · intro ps blk n2 J' hps hblk hJagr () m1 ⟨σ', hinv', hm', hrel⟩ hagr _ _
        have hk' : k.run (n + 2 + 1) = .ok (blk, n2) := by subst hps; exact hblk
        exact hk blk (ρ1.bind ps [] ()) J' (n + 2 + 1) n2 σ' m1 (by omega) hk'
          ((hagr.mono (by omega)).trans hagr1) (hJagr.mono (by omega)) hinv' hm' hrel
      · intro j body n2 J' _ hbody _ hjok
        rw [lm_bind_run] at hbody
        rcases hbody with ⟨eDec, n3, heDec, hpure⟩
        rw [lm_pure_run] at hpure
        injection hpure with hpr
        have hbod : LExpr.jnz sArg (j []) eDec = body := congrArg Prod.fst hpr
        have hn3 : n3 = n' := congrArg Prod.snd hpr
        subst hbod; subst hn3
        refine wp_jnz hsEv ?_ ?_
        · intro htrue
          have hsc : (vx &&& 1#64) ≠ 0#64 := of_decide_eq_true htrue
          have hrel : HDec1Rel vx ty σ σ := by simp [HDec1Rel, hskip, hsc]
          exact hjok J' [] ρ1 mem () (JEnvAgreeBelow.refl _ J') rfl ⟨σ, hinv, hm, hrel⟩
        · intro hfalse
          have hsc : (vx &&& 1#64) = 0#64 := by
            have := of_decide_eq_false hfalse
            simpa using this
          refine decRefJ_wp hΓ heDec ((hagr1.eval hnrt).trans hrt)
            (argIdsBelow_mono (by omega) hnrt) ((hagr1.eval hnx).trans hx)
            (argIdsBelow_mono (by omega) hnx) hsc htyRc hpre hinv hm ?_
          intro ρ' m' σ' _ hinv' hm' hrel
          exact hjok J' [] ρ' m' () (JEnvAgreeBelow.refl _ J') rfl ⟨σ', hinv', hm', hrel⟩

theorem emitDec_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg xArg : LArg} {ty : LcTy} {chk : Bool}
    {k : LM LExpr} {QT_K : HState → Prop}
    {rt vx : BitVec 64} {R : Mem 64 → Prop}
    (hΓ : HCallEnvOk m Δ Γ) (hkMono : LMMono k) :
    ∀ (cnt n n' : Nat) (e : LExpr) (ρ : Frontend.C0.VEnv) (J : JEnv) (σ : HState) (mem : Mem 64),
      (emitDec rtArg xArg ty cnt chk k).run n = .ok (e, n') →
      LArg.eval ρ i64 rtArg = some rt → argIdsBelow rtArg n →
      LArg.eval ρ i64 xArg = some vx → argIdsBelow xArg n →
      HInv rt σ → (σ.mem rt ⋆ R) mem →
      HDecN vx ty chk cnt QT_K σ →
      (∀ (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk : Nat)
          (σ' : HState) (m' : Mem 64),
        n ≤ nr → k.run nr = .ok (ek, nk) →
        VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
        HInv rt σ' → (σ'.mem rt ⋆ R) m' → QT_K σ' →
        LExpr.wp Γ QT XT ek ρ' J' m') →
      LExpr.wp Γ QT XT e ρ J mem := by
  intro cnt
  induction cnt with
  | zero =>
    intro n n' e ρ J σ mem hrun _ _ _ _ hinv hm hdec hk
    rw [HDecN.eq_1] at hdec
    unfold emitDec at hrun
    exact hk e ρ J n n' σ mem (Nat.le_refl n) hrun (VEnvAgreeBelow.refl n ρ)
      (JEnvAgreeBelow.refl n J) hinv hm hdec
  | succ cnt' ih =>
    intro n n' e ρ J σ mem hrun hrt hnrt hx hnx hinv hm hdec hk
    rw [HDecN.eq_2] at hdec
    rcases hdec with ⟨hpre, hcont⟩
    unfold emitDec at hrun
    refine emitDec1_wp hΓ hrun (emitDec_mono hkMono cnt') hrt hnrt hx hnx hpre hinv hm ?_
    intro ek1 ρ1 J1 nr1 nk1 σ1 m1 hn1 hek1 hagr1 hJagr1 hinv1 hm1 hrel1
    refine ih nr1 nk1 ek1 ρ1 J1 σ1 m1 hek1 ((hagr1.eval hnrt).trans hrt)
      (argIdsBelow_mono hn1 hnrt) ((hagr1.eval hnx).trans hx) (argIdsBelow_mono hn1 hnx)
      hinv1 hm1 (hcont σ1 hrel1) ?_
    intro ek2 ρ2 J2 nr2 nk2 σ2 m2 hn2 hek2 hagr2 hJagr2 hinv2 hm2 hqt2
    exact hk ek2 ρ2 J2 nr2 nk2 σ2 m2 (Nat.le_trans hn1 hn2) hek2
      ((hagr2.mono hn1).trans hagr1) ((hJagr2.mono hn1).trans hJagr1) hinv2 hm2 hqt2

end LeanQbe.T.LeanLCNF.Sem
