module

public import LeanQbe.T.LeanLCNF.Sem.Perceus3

/-!
# Perceus Tier-P → Tier-H Soundness:
Function Call Entry Framing & Post-Call Restoration (`PerceusCall`)

Connects `applyArgsHandles` (`Perceus3`) to callee `entryRcFrame` (`Perceus1`) and post-call
caller restoration via `CallPreserve`:
- `entryParamHandles`, `localHandles_bindParams_perm`
- `applyArgs_var_live`
- `entryRcFrame_fap_ok`
- `rcInv_after_call`
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

public section

/-! ## 1. Parameter Binding & `applyArgs` Liveness -/

@[expose] def paramRcVar (p : LcParam) : RcVar :=
  if p.borrow then
    { id := p.id, ty := p.ty, noRc := !p.ty.needsRc, persistent := false, owned := 0,
      borrowed := !(!p.ty.needsRc), parent? := none, excl := false, resetTok := false }
  else
    { id := p.id, ty := p.ty, noRc := !p.ty.needsRc, persistent := false,
      owned := if !p.ty.needsRc then 0 else 1, borrowed := false, parent? := none,
      excl := false, resetTok := false }

@[expose] def entryParamHandles (p : LcParam) (w : Word) : List (BitVec 64) :=
  if p.borrow || !p.ty.needsRc then []
  else match w.toBV64? with
    | some bv => if (bv &&& 1#64 == 0#64) = true then [bv] else []
    | none => []

theorem localHandles_bindParams_perm (ps : List LcParam) (ws : List Word)
    (hlen : ws.length = ps.length) (hndP : (ps.map (·.id)).Nodup) :
    ∀ (ctx : RcCtx) (envH : HValEnv),
      (ctx.vars.map RcVar.id).Nodup →
      (∀ u ∈ ctx.vars, ∀ p ∈ ps, u.id ≠ p.id) →
      (localHandles (ctx.bindParams ps) (envH.bindAll ps ws)).Perm
        (localHandles ctx envH ++
          ((ps.zip ws).map (fun (p, w) => entryParamHandles p w)).flatten) := by
  induction ps generalizing ws with
  | nil =>
    cases ws with
    | nil => intro ctx envH _ _; simp [RcCtx.bindParams, HValEnv.bindAll]
    | cons _ _ => simp at hlen
  | cons p ps ih =>
    cases ws with
    | nil => simp at hlen
    | cons w ws =>
      intro ctx envH hndC hdisj
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hndP
      simp only [RcCtx.bindParams, List.foldl_cons, HValEnv.bindAll, List.zip_cons_cons,
        List.map_cons, List.flatten_cons]
      let vp := paramRcVar p
      have hctx_step : (if p.borrow then ctx.bindBorrowed p.id p.ty none false
          else ctx.bindOwned p.id p.ty false false false) = ctx.put vp := by
        by_cases hb : p.borrow = true <;> cases hn : p.ty.needsRc <;>
          simp [hb, hn, RcCtx.bindBorrowed, RcCtx.bindOwned, vp, paramRcVar]
      rw [hctx_step]
      have hnd1 := ctx.put_nodup hndC vp
      have hvp_id : vp.id = p.id := by by_cases hb : p.borrow <;> simp [hb, vp, paramRcVar]
      have hdisj1 : ∀ u ∈ (ctx.put vp).vars, ∀ q ∈ ps, u.id ≠ q.id := by
        intro u hu q hq
        rcases (RcCtx.put_mem_iff hndC).mp hu with rfl | ⟨hum, _⟩
        · exact fun heq => hndP.1 ⟨q, hq, heq.symm.trans hvp_id⟩
        · exact hdisj u hum q (List.mem_cons_of_mem _ hq)
      have hih := ih ws (by simp at hlen; exact hlen) hndP.2
        (ctx.put vp) (envH.set p.id p.ty w) hnd1 hdisj1
      have hput_perm := localHandles_put_perm hndC (envH.set p.id p.ty w) vp
      have hcongr_ex : localHandlesExcept ctx (envH.set p.id p.ty w) vp.id =
          localHandles ctx envH := by
        unfold localHandlesExcept localHandles
        have hflt : ctx.vars.filter (fun u => u.id != vp.id) = ctx.vars :=
          List.filter_eq_self.mpr fun u hu => bne_iff_ne.mpr (by
            rw [hvp_id]; exact hdisj u hu p List.mem_cons_self)
        rw [hflt]
        refine congrArg List.flatten (List.map_congr_left fun u hu => ?_)
        have hne : u.id ≠ p.id := hdisj u hu p List.mem_cons_self
        unfold varHandles; simp [HValEnv.set, hne]
      have hvp_handles : varHandles (envH.set p.id p.ty w) vp = entryParamHandles p w := by
        unfold varHandles entryParamHandles
        by_cases hb : p.borrow = true
        · simp [hb, vp, paramRcVar]
        · have hbf : p.borrow = false := by cases h : p.borrow <;> simp_all
          by_cases hnr : p.ty.needsRc = true
          · simp only [hbf, hnr, Bool.false_eq_true, ↓reduceIte, Bool.or_self,
              Bool.not_true, vp, paramRcVar, HValEnv.set, List.replicate_succ, List.replicate_zero]
            cases w.toBV64? with
            | none => rfl
            | some bv => by_cases h : bv &&& 1#64 = 0#64 <;> simp [h]
          · have hnrf : p.ty.needsRc = false := by cases h : p.ty.needsRc <;> simp_all
            simp [hbf, hnrf, vp, paramRcVar]
      rw [hvp_handles, hcongr_ex] at hput_perm
      refine hih.trans ((hput_perm.append_right _).trans ?_)
      exact List.perm_iff_count.mpr fun a => by simp only [List.count_append]; omega

private theorem bindParams_bindAll_mem_iff (ps : List LcParam) (pvs : List PVal) (ws : List Word)
    (hpv : pvs.length = ps.length) (hws : ws.length = ps.length) (hndP : (ps.map (·.id)).Nodup) :
    ∀ (ctx : RcCtx) (envP : PValEnv) (envH : HValEnv),
      (ctx.vars.map RcVar.id).Nodup →
      (∀ u ∈ ctx.vars, ∀ p ∈ ps, u.id ≠ p.id) →
      ∀ v ∈ (ctx.bindParams ps).vars,
        (v ∈ ctx.vars ∧ ∀ p ∈ ps, v.id ≠ p.id) ∨
        ∃ i, ∃ hi : i < ps.length,
          let p := ps[i]
          v = paramRcVar p ∧
          (envP.bindAll ps pvs) v.id = some (pvs[i]'(by omega)) ∧
          (envH.bindAll ps ws) v.id = some (p.ty, ws[i]'(by omega)) := by
  induction ps generalizing pvs ws with
  | nil =>
    cases pvs <;> cases ws <;> try (simp at hpv hws; done)
    intro ctx envP envH _ _ v hv
    exact Or.inl ⟨hv, fun _ h => by cases h⟩
  | cons p ps ih =>
    cases pvs with
    | nil => simp at hpv
    | cons pv pvs =>
      cases ws with
      | nil => simp at hws
      | cons w ws =>
        intro ctx envP envH hndC hdisj v hv
        simp only [List.map_cons, List.nodup_cons, List.mem_map] at hndP
        simp only [RcCtx.bindParams, List.foldl_cons, PValEnv.bindAll, HValEnv.bindAll] at hv ⊢
        let vp := paramRcVar p
        have hctx_step : (if p.borrow then ctx.bindBorrowed p.id p.ty none false
            else ctx.bindOwned p.id p.ty false false false) = ctx.put vp := by
          by_cases hb : p.borrow = true <;> cases hn : p.ty.needsRc <;>
            simp [hb, hn, RcCtx.bindBorrowed, RcCtx.bindOwned, vp, paramRcVar]
        rw [hctx_step] at hv
        have hnd1 := ctx.put_nodup hndC vp
        have hvp_id : vp.id = p.id := by by_cases hb : p.borrow <;> simp [hb, vp, paramRcVar]
        have hdisj1 : ∀ u ∈ (ctx.put vp).vars, ∀ q ∈ ps, u.id ≠ q.id := by
          intro u hu q hq
          rcases (RcCtx.put_mem_iff hndC).mp hu with rfl | ⟨hum, _⟩
          · exact fun heq => hndP.1 ⟨q, hq, heq.symm.trans hvp_id⟩
          · exact hdisj u hum q (List.mem_cons_of_mem _ hq)
        rcases ih pvs ws (by simp at hpv; exact hpv) (by simp at hws; exact hws) hndP.2
            (ctx.put vp) (envP.set p.id pv) (envH.set p.id p.ty w) hnd1 hdisj1 v hv with
            ⟨hvc, hvne⟩ | ⟨i, hi, hveq, hep, heh⟩
        · rcases (RcCtx.put_mem_iff hndC).mp hvc with rfl | ⟨hvm, _⟩
          · refine Or.inr ⟨0, Nat.zero_lt_succ _, rfl, ?_, ?_⟩
            · have hnotin : ∀ q ∈ ps, p.id ≠ q.id := fun q hq heq => hndP.1 ⟨q, hq, heq.symm⟩
              have hnot_bind : ∀ (l : List LcParam) (ys : List PVal) (ep : PValEnv) (k : Nat),
                  (∀ q ∈ l, k ≠ q.id) → (ep.bindAll l ys) k = ep k := by
                intro l; induction l with
                | nil => intro ys ep _ _; cases ys <;> rfl
                | cons q qs ihq =>
                  intro ys ep k hk
                  cases ys with
                  | nil => rfl
                  | cons y ys =>
                    simp only [PValEnv.bindAll]
                    rw [ihq ys (ep.set q.id y) k (fun r hr => hk r (List.mem_cons_of_mem _ hr))]
                    simp [PValEnv.set, hk q List.mem_cons_self]
              rw [hvp_id, hnot_bind ps pvs (envP.set p.id pv) p.id hnotin]; simp [PValEnv.set]
            · have hnotin : ∀ q ∈ ps, p.id ≠ q.id := fun q hq heq => hndP.1 ⟨q, hq, heq.symm⟩
              have hnot_bind : ∀ (l : List LcParam) (ys : List Word) (eh : HValEnv) (k : Nat),
                  (∀ q ∈ l, k ≠ q.id) → (eh.bindAll l ys) k = eh k := by
                intro l; induction l with
                | nil => intro ys eh _ _; cases ys <;> rfl
                | cons q qs ihq =>
                  intro ys eh k hk
                  cases ys with
                  | nil => rfl
                  | cons y ys =>
                    simp only [HValEnv.bindAll]
                    rw [ihq ys (eh.set q.id q.ty y) k
                      (fun r hr => hk r (List.mem_cons_of_mem _ hr))]
                    simp [HValEnv.set, hk q List.mem_cons_self]
              rw [hvp_id, hnot_bind ps ws (envH.set p.id p.ty w) p.id hnotin]; simp [HValEnv.set]
          · refine Or.inl ⟨hvm, fun q hq => ?_⟩
            rcases List.mem_cons.mp hq with rfl | hqs
            · exact hdisj v hvm q List.mem_cons_self
            · exact hvne q hqs
        · exact Or.inr ⟨i + 1, Nat.succ_lt_succ hi, hveq, hep, heh⟩

theorem applyArgs_var_live {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hc : CleanVars ctx) {as : List LcArg} {bs : List Bool} {ctx' : RcCtx}
    (ha : ctx.applyArgs as bs = .ok ctx') :
    ∀ a ∈ as, a = .erased ∨ ∃ z v, a = .var z ∧ ctx.get? z = some v ∧ v.isLive = true := by
  induction as generalizing ctx bs with
  | nil => intro a h; cases h
  | cons a as ih =>
    intro u hu
    cases bs with
    | nil => simp [RcCtx.applyArgs] at ha
    | cons b bs =>
      simp only [RcCtx.applyArgs, bind, Except.bind] at ha
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte] at ha
        cases hchk : ctx.checkArgLive a with
        | error _ => simp [hchk] at ha
        | ok _ =>
          simp only [hchk] at ha
          rcases List.mem_cons.mp hu with rfl | hus
          · cases u with
            | erased => exact Or.inl rfl
            | var z =>
              unfold RcCtx.checkArgLive RcCtx.checkLive at hchk
              dsimp only at hchk
              cases hgz : ctx.get? z with
              | none => simp [hgz] at hchk
              | some v =>
                rw [hgz] at hchk
                by_cases hl : v.isLive = true
                · exact Or.inr ⟨z, v, rfl, hgz, hl⟩
                · simp [hl] at hchk
          · exact ih hnd hc ha u hus
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
        cases hcarg : ctx.consumeArg a with
        | error _ => simp [hcarg] at ha
        | ok ctx1 =>
          simp only [hcarg] at ha
          cases a with
          | erased =>
            simp only [RcCtx.consumeArg, pure, Except.pure] at hcarg; cases hcarg
            rcases List.mem_cons.mp hu with rfl | hus
            · exact Or.inl rfl
            · exact ih hnd hc ha u hus
          | var z =>
            have hnd1 := consumeVar_nodup hnd hcarg
            have hc1 := cleanVars_consumeVar hnd hc hcarg
            rcases List.mem_cons.mp hu with rfl | hus
            · unfold RcCtx.consumeArg RcCtx.consumeVar at hcarg
              dsimp only at hcarg
              cases hgz : ctx.get? z with
              | none => simp [hgz] at hcarg
              | some v =>
                have hcv := hc v (RcCtx.get?_mem hgz).1
                have hrt := hcv.2.2.2.2
                rw [hgz] at hcarg; dsimp only at hcarg
                by_cases hnp : (v.noRc || v.persistent) = true
                · refine Or.inr ⟨z, v, rfl, hgz, ?_⟩
                  cases h1 : v.noRc <;> cases h2 : v.persistent <;> simp_all [RcVar.isLive]
                · have hnpf : (v.noRc || v.persistent) = false := by
                    cases h : (v.noRc || v.persistent) <;> simp_all
                  simp only [hnpf, Bool.false_eq_true, ↓reduceIte] at hcarg
                  by_cases hlt : v.owned < 1
                  · simp [hlt] at hcarg
                  · have hown : 0 < v.owned := by omega
                    refine Or.inr ⟨z, v, rfl, hgz, ?_⟩
                    cases h1 : v.noRc <;> cases h2 : v.persistent <;>
                      simp_all [RcVar.isLive]
            · obtain hres := ih hnd1 hc1 ha u hus
              rcases hres with rfl | ⟨w, vw1, rfl, hgw1, hlw1⟩
              · exact Or.inl rfl
              · obtain ⟨vw0, hgw0, hlw0, _⟩ :=
                  consumeVar_get?_live_back hnd hc hcarg w hgw1 hlw1
                exact Or.inr ⟨w, vw0, rfl, hgw0, hlw0⟩

/-! ## 2. Callee Entry Framing (`entryRcFrame_fap_ok`) -/

private theorem find?_eq_some_of_mem_nodup : ∀ {l : List RcVar} {w : RcVar},
    (l.map RcVar.id).Nodup → w ∈ l → l.find? (·.id == w.id) = some w
  | [], _, _, h => by cases h
  | a :: l, w, hnd, hw => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd; simp only [List.find?]
    rcases List.mem_cons.mp hw with rfl | hmem
    · simp
    · have hne : (a.id == w.id) = false := beq_false_of_ne fun h => hnd.1 ⟨w, hmem, h.symm⟩
      simp [hne, find?_eq_some_of_mem_nodup hnd.2 hmem]
private theorem handlesRcSound_of_nonPersist_count_le {h1 h2 : List (BitVec 64)}
    {objs : List LcnfObj}
    (hle : ∀ y ∈ objs, 0 < y.rc.toInt → h2.count y.addr ≤ h1.count y.addr)
    (hs : HandlesRcSound h1 objs) : HandlesRcSound h2 objs :=
  ⟨hs.1, fun y hy hrc => Nat.le_trans (Nat.add_le_add_left (hle y hy hrc) _) (hs.2 y hy hrc)⟩
private theorem bindParams_nodup (ps : List LcParam) (ctx : RcCtx)
    (hnd : (ctx.vars.map RcVar.id).Nodup) :
    ((ctx.bindParams ps).vars.map RcVar.id).Nodup := by
  induction ps generalizing ctx with
  | nil => exact hnd
  | cons p ps ih =>
    simp only [RcCtx.bindParams, List.foldl_cons]; apply ih
    by_cases hb : p.borrow <;>
      simp only [hb, Bool.false_eq_true, ↓reduceIte, RcCtx.bindBorrowed, RcCtx.bindOwned] <;>
      exact ctx.put_nodup hnd _
private theorem bindParams_sharedPreds (ps : List LcParam) (ctx : RcCtx) :
    (ctx.bindParams ps).sharedPreds = ctx.sharedPreds := by
  induction ps generalizing ctx with
  | nil => rfl
  | cons p ps ih =>
    simp only [RcCtx.bindParams, List.foldl_cons]; refine (ih _).trans ?_
    by_cases hb : p.borrow <;> simp [hb, RcCtx.bindBorrowed, RcCtx.bindOwned, RcCtx.put]
private theorem varHandles_eq_nil_of_not_live (envH : HValEnv) {v : RcVar}
    (hl : v.isLive = false) : varHandles envH v = [] := by
  unfold RcVar.isLive at hl
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero] at hl
  rcases hl with ⟨⟨⟨⟨hnr, hps⟩, hown⟩, _⟩, hrt⟩; unfold varHandles; simp [hnr, hps, hown, hrt]

private theorem obj_addr_inj_nodup {objs : List LcnfObj} (hnd : (objs.map LcnfObj.addr).Nodup)
    {o1 o2 : LcnfObj} (h1 : o1 ∈ objs) (h2 : o2 ∈ objs) (heq : o1.addr = o2.addr) : o1 = o2 := by
  induction objs with
  | nil => cases h1
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp h1 with rfl | h1m <;> rcases List.mem_cons.mp h2 with rfl | h2m
    · rfl
    · exact absurd ⟨o2, h2m, heq.symm⟩ hnd.1
    · exact absurd ⟨o1, h1m, heq⟩ hnd.1
    · exact ih hnd.2 h1m h2m

private theorem entry_count_le_applyArgsHandles {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (_hclean : CleanVars rf.ctx)
    (ps : List LcParam) (as : List LcArg) (ws : List Word)
    (hla : as.length = ps.length) (hlw : ws.length = ps.length)
    (hws : rf.envH.evalArgsOwn as = some ws)
    (hmatch : argsMatchTys rf.ctx as (ps.map (·.ty)) = true)
    (hlive : ∀ a ∈ as, a = .erased ∨ ∃ z v, a = .var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true) :
    ∀ y ∈ σ.objs, 0 < y.rc.toInt →
      ((ps.zip ws).map (fun (p, w) => entryParamHandles p w)).flatten.count y.addr ≤
        (applyArgsHandles rf as (ps.map (·.borrow))).count y.addr := by
  induction ps generalizing as ws with
  | nil =>
    cases as <;> cases ws <;> simp_all [applyArgsHandles]
  | cons p ps ih =>
    cases as with
    | nil => simp at hla
    | cons a as =>
      cases ws with
      | nil => simp at hlw
      | cons w ws =>
        simp only [HValEnv.evalArgsOwn] at hws
        cases h1 : rf.envH.evalArgOwn a with
        | none => simp [h1] at hws
        | some w' =>
          cases h2 : rf.envH.evalArgsOwn as with
          | none => simp [h1, h2] at hws
          | some ws' =>
            simp only [h1, h2, Option.some.injEq, List.cons.injEq] at hws
            obtain ⟨hw', hws'⟩ := hws
            subst w'; subst ws'
            have hstep : ∀ (bs : List Bool),
                applyArgsHandles rf (a :: as) (p.borrow :: bs) =
                  (if p.borrow then [] else match a with
                    | .erased => []
                    | .var z => consumeVarHandles rf z 1) ++ applyArgsHandles rf as bs :=
                fun bs => by
              by_cases hbr : p.borrow <;> cases a <;>
                simp only [applyArgsHandles, hbr, Bool.false_eq_true, ↓reduceIte,
                  List.nil_append] <;>
                rfl
            simp only [List.map_cons]
            rw [hstep (ps.map (·.borrow))]
            simp only [List.count_append]
            have hla' : as.length = ps.length := by simp at hla; exact hla
            have hlw' : ws.length = ps.length := by simp at hlw; exact hlw
            have hm := hmatch
            simp only [argsMatchTys, List.map_cons, List.zip_cons_cons, List.all_cons,
              Bool.and_eq_true] at hm
            have hih := ih as ws hla' hlw' h2
              (by simp only [argsMatchTys, List.length_map, hla', beq_self_eq_true, Bool.true_and,
                hm.2.2])
              (fun u hu => hlive u (List.mem_cons_of_mem _ hu))
            intro y hy hrc
            have hih_y := hih y hy hrc
            simp only [List.zip_cons_cons, List.map_cons, List.flatten_cons, List.count_append]
            have hhead : (entryParamHandles p w).count y.addr ≤
                ((if p.borrow then [] else match a with
                  | .erased => []
                  | .var z => consumeVarHandles rf z 1)).count y.addr := by
              unfold entryParamHandles
              by_cases hbr : p.borrow = true
              · simp [hbr]
              · have hbrf : p.borrow = false := Bool.eq_false_iff.mpr hbr
                simp only [hbrf, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
                by_cases hnr : p.ty.needsRc = true
                · simp only [hnr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                  rcases hlive a List.mem_cons_self with rfl | ⟨z, vz, rfl, hgz, hzl⟩
                  · simp only [HValEnv.evalArgOwn] at h1; cases h1
                    simp [Word.toBV64?, Word.i64]
                  · have hzm := (RcCtx.get?_mem hgz).1
                    have hzid := (RcCtx.get?_mem hgz).2
                    obtain ⟨_, wz, _, hwz, _, hnonz⟩ := hinv.2.2.2.1 vz hzm hzl
                    rw [hzid] at hwz
                    have hw_eq : w = wz := by
                      simp only [HValEnv.evalArgOwn, hwz] at h1; exact (Option.some.inj h1).symm
                    subst hw_eq
                    have hns_p : p.ty.isScalar = false := by revert hnr; cases p.ty <;> decide
                    have hmt := hm.2.1
                    dsimp only at hmt; rw [hgz] at hmt; dsimp only at hmt
                    have hns_z : ¬vz.ty.isScalar := by
                      simp only [Bool.and_eq_true, beq_iff_eq] at hmt
                      intro hs; rw [hs, hns_p] at hmt; simp at hmt
                    obtain ⟨bv, rfl, hno_z, hps_z, _, _⟩ := hnonz hns_z
                    dsimp only
                    unfold consumeVarHandles
                    simp only [hgz, hwz, Word.toBV64?, Word.i64]
                    by_cases hev : (bv &&& 1#64 == 0#64) = true
                    · have heven : bv &&& 1#64 = 0#64 := beq_iff_eq.mp hev
                      simp only [hev, ↓reduceIte]
                      by_cases hzn : vz.noRc = true
                      · exact absurd heven (hno_z hzn)
                      · have hzn0 : vz.noRc = false := Bool.eq_false_iff.mpr hzn
                        by_cases hzp : vz.persistent = true
                        · obtain ⟨o, ho, hoa, hrc0⟩ := hps_z hzp heven
                          have hne : y.addr ≠ bv := by
                            intro heq
                            have hyeo := obj_addr_inj_nodup hinv.1.2 hy ho (heq.trans hoa.symm)
                            subst hyeo; simp [hrc0] at hrc
                          simp [hzn0, hzp, hne.symm]
                        · have hzp0 : vz.persistent = false := Bool.eq_false_iff.mpr hzp
                          simp [hzn0, hzp0]
                    · simp [hev]
                · have hnrf : p.ty.needsRc = false := Bool.eq_false_iff.mpr hnr; simp [hnrf]
            exact Nat.add_le_add hhead hih_y
private theorem invalidateChildren_nodup (ctx : RcCtx) (p : Nat)
    (hnd : (ctx.vars.map RcVar.id).Nodup) :
    ((ctx.invalidateChildren p).vars.map RcVar.id).Nodup := by
  unfold RcCtx.invalidateChildren; dsimp only
  have hmap : List.map RcVar.id (List.map (fun v =>
      if (v.parent? == some p) = true then
        { id := v.id, ty := v.ty, noRc := v.noRc, persistent := v.persistent,
          owned := v.owned, excl := v.excl, resetTok := v.resetTok }
      else v) ctx.vars) = ctx.vars.map RcVar.id := by
    induction ctx.vars with
    | nil => rfl
    | cons v vs ih =>
      simp only [List.map_cons, ih]; by_cases h : (v.parent? == some p) = true <;> simp [h]
  rw [hmap]; exact hnd

private theorem applyArgs_get?_eq_of_not_mem {ctx : RcCtx}
    (hnd : (ctx.vars.map RcVar.id).Nodup) (hc : CleanVars ctx)
    {as : List LcArg} {bs : List Bool} {ctx' : RcCtx}
    (ha : ctx.applyArgs as bs = .ok ctx')
    {z : Nat} {v0 : RcVar} (hgz : ctx.get? z = some v0)
    (hpar : v0.parent? = none) (hnot : as.all (· != .var z) = true) :
    ctx'.get? z = some v0 := by
  induction as generalizing ctx bs with
  | nil =>
    cases bs with
    | nil => simp [RcCtx.applyArgs, pure, Except.pure] at ha; subst ha; exact hgz
    | cons _ _ => simp [RcCtx.applyArgs] at ha
  | cons a as ih =>
    cases bs with
    | nil => simp [RcCtx.applyArgs] at ha
    | cons b bs =>
      simp only [List.all_cons, Bool.and_eq_true] at hnot
      simp only [RcCtx.applyArgs, bind, Except.bind] at ha
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte] at ha
        cases hchk : ctx.checkArgLive a <;> simp [hchk] at ha
        exact ih hnd hc ha hgz hnot.2
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
        cases hcarg : ctx.consumeArg a <;> simp [hcarg] at ha
        rename_i ctx1
        cases a with
        | erased =>
          simp only [RcCtx.consumeArg, pure, Except.pure] at hcarg; cases hcarg
          exact ih hnd hc ha hgz hnot.2
        | var w =>
          have hne : w ≠ z := fun h => by
            subst h; have h1 := hnot.1
            simp [bne, BEq.beq, instBEqLcArg.beq] at h1
          have hnd1 := consumeVar_nodup hnd hcarg
          have hc1 := cleanVars_consumeVar hnd hc hcarg
          have hgz1 : ctx1.get? z = some v0 := by
            unfold RcCtx.consumeArg RcCtx.consumeVar at hcarg
            dsimp only at hcarg
            cases hgw : ctx.get? w with
            | none => simp [hgw] at hcarg
            | some vw =>
              rw [hgw] at hcarg; dsimp only at hcarg
              by_cases hnp : (vw.noRc || vw.persistent) = true
              · simp [hnp, pure, Except.pure] at hcarg; subst hcarg; exact hgz
              · have hnpf : (vw.noRc || vw.persistent) = false := by
                  cases h : (vw.noRc || vw.persistent) <;> simp_all
                simp only [hnpf, Bool.false_eq_true, ↓reduceIte] at hcarg
                by_cases hlt : vw.owned < 1
                · simp [hlt] at hcarg
                · have h10 : (1 == 0) = false := rfl
                  simp only [hlt, ↓reduceIte, h10, Bool.false_eq_true, pure, Except.pure] at hcarg
                  have hv0m := (RcCtx.get?_mem hgz).1
                  have hv0id := (RcCtx.get?_mem hgz).2
                  have hwid := (RcCtx.get?_mem hgw).2
                  let vw' : RcVar := {
                    id := vw.id, ty := vw.ty, noRc := vw.noRc, persistent := vw.persistent,
                    owned := vw.owned - 1, borrowed := vw.borrowed, parent? := vw.parent?,
                    excl := if (vw.owned - 1 == 0) = true then false else vw.excl,
                    resetTok := if (vw.owned - 1 == 0) = true then false else vw.resetTok }
                  have hv0_put : v0 ∈ (ctx.put vw').vars :=
                    (RcCtx.put_mem_iff hnd).mpr
                      (Or.inr ⟨hv0m, by rw [hv0id]; exact (hwid ▸ hne).symm⟩)
                  by_cases hrem : (vw.owned - 1 == 0 && !vw.borrowed) = true
                  · simp only [hrem, ↓reduceIte, Except.ok.injEq] at hcarg
                    subst hcarg
                    have hv0_mem : v0 ∈ ((ctx.put vw').invalidateChildren w).vars := by
                      unfold RcCtx.invalidateChildren
                      refine List.mem_map.mpr ⟨v0, hv0_put, ?_⟩
                      simp [hpar]
                    have hres := find?_eq_some_of_mem_nodup hnd1 hv0_mem
                    rwa [hv0id] at hres
                  · have hremf : (vw.owned - 1 == 0 && !vw.borrowed) = false := by
                      cases h : (vw.owned - 1 == 0 && !vw.borrowed) <;> simp_all
                    simp only [hremf, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hcarg
                    subst hcarg
                    have hres := find?_eq_some_of_mem_nodup hnd1 hv0_put
                    rwa [hv0id] at hres
          exact ih hnd1 hc1 ha hgz1 hnot.2

private theorem applyArgs_get?_meta_back {ctx : RcCtx}
    (hnd : (ctx.vars.map RcVar.id).Nodup) (hc : CleanVars ctx)
    {as : List LcArg} {bs : List Bool} {ctx' : RcCtx}
    (ha : ctx.applyArgs as bs = .ok ctx')
    (z : Nat) {w' : RcVar} (hgz' : ctx'.get? z = some w') :
    ∃ w, ctx.get? z = some w ∧ w.noRc = w'.noRc ∧ w.persistent = w'.persistent ∧
      w.ty = w'.ty ∧ w'.owned ≤ w.owned := by
  induction as generalizing ctx bs with
  | nil =>
    cases bs with
    | nil =>
      simp [RcCtx.applyArgs, pure, Except.pure] at ha; subst ha
      exact ⟨w', hgz', rfl, rfl, rfl, Nat.le_refl _⟩
    | cons _ _ => simp [RcCtx.applyArgs] at ha
  | cons a as ih =>
    cases bs with
    | nil => simp [RcCtx.applyArgs] at ha
    | cons b bs =>
      simp only [RcCtx.applyArgs, bind, Except.bind] at ha
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte] at ha
        cases hchk : ctx.checkArgLive a <;> simp [hchk] at ha
        exact ih hnd hc ha
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
        cases hcarg : ctx.consumeArg a <;> simp [hcarg] at ha
        rename_i ctx1
        cases a with
        | erased =>
          simp only [RcCtx.consumeArg, pure, Except.pure] at hcarg; cases hcarg
          exact ih hnd hc ha
        | var x =>
          have hnd1 := consumeVar_nodup hnd hcarg
          have hc1 := cleanVars_consumeVar hnd hc hcarg
          obtain ⟨w1, hgw1, hno1, hps1, hty1, hown1⟩ := ih hnd1 hc1 ha
          unfold RcCtx.consumeArg RcCtx.consumeVar at hcarg
          dsimp only at hcarg
          cases hgx : ctx.get? x with
          | none => simp [hgx] at hcarg
          | some vx =>
            rw [hgx] at hcarg; dsimp only at hcarg
            by_cases hnp : (vx.noRc || vx.persistent) = true
            · simp [hnp, pure, Except.pure] at hcarg; subst hcarg
              exact ⟨w1, hgw1, hno1, hps1, hty1, hown1⟩
            · have hnpf : (vx.noRc || vx.persistent) = false := by
                cases h : (vx.noRc || vx.persistent) <;> simp_all
              simp only [hnpf, Bool.false_eq_true, ↓reduceIte] at hcarg
              by_cases hlt : vx.owned < 1
              · simp [hlt] at hcarg
              · have h10 : (1 == 0) = false := rfl
                simp only [hlt, ↓reduceIte, h10, Bool.false_eq_true, pure, Except.pure] at hcarg
                have hw1m := (RcCtx.get?_mem hgw1).1
                have hw1id := (RcCtx.get?_mem hgw1).2
                have hxid := (RcCtx.get?_mem hgx).2
                let vx' : RcVar := {
                  id := vx.id, ty := vx.ty, noRc := vx.noRc, persistent := vx.persistent,
                  owned := vx.owned - 1, borrowed := vx.borrowed, parent? := vx.parent?,
                  excl := if (vx.owned - 1 == 0) = true then false else vx.excl,
                  resetTok := if (vx.owned - 1 == 0) = true then false else vx.resetTok }
                have hput_back : ∀ u ∈ (ctx.put vx').vars,
                    ∃ w0, ctx.get? u.id = some w0 ∧ w0.noRc = u.noRc ∧
                      w0.persistent = u.persistent ∧ w0.ty = u.ty ∧ u.owned ≤ w0.owned := by
                  intro u hu
                  rcases (RcCtx.put_mem_iff hnd).mp hu with rfl | ⟨hum, _⟩
                  · refine ⟨vx, ?_, rfl, rfl, rfl, Nat.sub_le _ _⟩
                    simpa [vx', hxid] using hgx
                  · exact ⟨u, find?_eq_some_of_mem_nodup hnd hum, rfl, rfl, rfl, Nat.le_refl _⟩
                by_cases hrem : (vx.owned - 1 == 0 && !vx.borrowed) = true
                · simp only [hrem, ↓reduceIte, Except.ok.injEq] at hcarg
                  subst hcarg
                  unfold RcCtx.invalidateChildren at hw1m
                  rcases List.mem_map.mp hw1m with ⟨u, hu_put, rfl⟩
                  have hpar_eq : (if (u.parent? == some x) = true then
                      { id := u.id, ty := u.ty, noRc := u.noRc, persistent := u.persistent,
                        owned := u.owned, excl := u.excl,
                        resetTok := u.resetTok } else u).id = u.id := by
                    by_cases hp : (u.parent? == some x) = true <;> simp [hp]
                  obtain ⟨w0, hgw0, hn0, hp0, ht0, ho0⟩ := hput_back u hu_put
                  rw [← hw1id, hpar_eq]
                  refine ⟨w0, hgw0, ?_, ?_, ?_, ?_⟩
                  · by_cases hp : (u.parent? == some x) = true <;> simp [hp] at hno1 ⊢ <;>
                      exact hn0.trans hno1
                  · by_cases hp : (u.parent? == some x) = true <;> simp [hp] at hps1 ⊢ <;>
                      exact hp0.trans hps1
                  · by_cases hp : (u.parent? == some x) = true <;> simp [hp] at hty1 ⊢ <;>
                      exact ht0.trans hty1
                  · by_cases hp : (u.parent? == some x) = true <;> simp [hp] at hown1 ⊢ <;>
                      exact Nat.le_trans hown1 ho0
                · have hremf : (vx.owned - 1 == 0 && !vx.borrowed) = false := by
                    cases h : (vx.owned - 1 == 0 && !vx.borrowed) <;> simp_all
                  simp only [hremf, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hcarg
                  subst hcarg
                  obtain ⟨w0, hgw0, hn0, hp0, ht0, ho0⟩ := hput_back w1 hw1m
                  rw [← hw1id]
                  exact ⟨w0, hgw0, hn0.trans hno1, hp0.trans hps1, ht0.trans hty1,
                    Nat.le_trans hown1 ho0⟩

private theorem list_flatten_split_perm {f : RcVar → List (BitVec 64)} :
    ∀ {l : List RcVar} {v : RcVar}, (l.map RcVar.id).Nodup → v ∈ l →
      (l.map f).flatten.Perm (f v ++ ((l.filter (·.id != v.id)).map f).flatten)
  | [], _, _, h => by cases h
  | a :: l, v, hnd, hv => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hv with rfl | hmem
    · have hflt : l.filter (fun u => u.id != v.id) = l :=
        List.filter_eq_self.mpr fun u hu => bne_iff_ne.mpr fun h => hnd.1 ⟨u, hu, h⟩
      simp [bne_self_eq_false, hflt]
    · have hne : (a.id != v.id) = true := bne_iff_ne.mpr fun h => hnd.1 ⟨v, hmem, h.symm⟩
      simp only [List.filter_cons, hne, ↓reduceIte, List.map_cons, List.flatten_cons]
      refine (List.Perm.append_left (f a) (list_flatten_split_perm hnd.2 hmem)).trans ?_
      exact List.perm_iff_count.mpr fun x => by simp only [List.count_append]; omega

private theorem localHandles_split_var_perm {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (envH : HValEnv) {v : RcVar} (hv : v ∈ ctx.vars) :
    (localHandles ctx envH).Perm (varHandles envH v ++ localHandlesExcept ctx envH v.id) :=
  list_flatten_split_perm hnd hv

private theorem backed_trans_roots {objs : List LcnfObj} (hnd : (objs.map LcnfObj.addr).Nodup)
    {handles : List (BitVec 64)} (hhs : HandlesRcSound handles objs)
    {r1 r2 : List (BitVec 64)}
    (hsub : ∀ r ∈ r1, (∃ o ∈ objs, o.addr = r ∧ o.rc ≠ 0#32) → Backed objs r2 r) :
    ∀ {a : BitVec 64}, Backed objs r1 a → Backed objs r2 a := by
  intro a hb
  rcases hb with hp | ⟨r, hr, hreach⟩
  · exact Or.inl hp
  · induction hreach with
    | refl h0 =>
      rcases h0 with ⟨o, ho, hoa, hrcne⟩
      rcases hsub _ hr ⟨o, ho, hoa, hrcne⟩ with ⟨o', ho', hoa', hrc0⟩ | ⟨r2, hr2, hrch⟩
      · have heq := obj_addr_inj_nodup hnd ho ho' (hoa.trans hoa'.symm)
        subst heq; exact absurd hrc0 hrcne
      · exact Or.inr ⟨r2, hr2, hrch⟩
    | step _ hstep hev hne ih =>
      rcases ih with ⟨op, hop, hoap, hrcp⟩ | ⟨r2, hr2, hrch2⟩
      · rcases hstep with ⟨ou, hou, hoau, hmem⟩
        have heq := obj_addr_inj_nodup hnd hop hou (hoap.trans hoau.symm)
        subst heq
        exact Or.inl (hhs.1 op hop hrcp _ hmem hev)
      · exact Or.inr ⟨r2, hr2, NonPersistReach.step hrch2 hstep hev hne⟩

private theorem evalArgsOwn_mem_arg {envH : HValEnv} {as : List LcArg} :
    ∀ {ws : List Word}, envH.evalArgsOwn as = some ws → ∀ {w : Word}, w ∈ ws →
      ∃ a, a ∈ as ∧ envH.evalArgOwn a = some w := by
  induction as with
  | nil => intro ws hws w hw; simp [HValEnv.evalArgsOwn] at hws; subst hws; cases hw
  | cons a as ih =>
    intro ws hws w hw
    simp only [HValEnv.evalArgsOwn] at hws
    cases h1 : envH.evalArgOwn a
    · simp [h1] at hws
    · cases h2 : envH.evalArgsOwn as
      · simp [h1, h2] at hws
      · simp only [h1, h2, Option.some.injEq] at hws; subst hws
        rcases List.mem_cons.mp hw with rfl | hwt
        · exact ⟨a, List.mem_cons_self, h1⟩
        · obtain ⟨u, hu, hev⟩ := ih h2 hwt
          exact ⟨u, List.mem_cons_of_mem _ hu, hev⟩

private theorem evalArgs_getElem {envP : PValEnv} {l : List LcArg} :
    ∀ {pvs : List PVal}, envP.evalArgs l = some pvs →
      ∀ (i : Nat) (hl : i < l.length) (hp : i < pvs.length),
        envP.evalArg (l[i]'hl) = some (pvs[i]'hp) := by
  induction l with
  | nil => intro _ _ i hl _; cases hl
  | cons u us ih =>
    intro pvs hev i hl hp
    simp only [PValEnv.evalArgs] at hev
    cases h1 : envP.evalArg u
    · simp [h1] at hev
    · cases h2 : envP.evalArgs us
      · simp [h1, h2] at hev
      · simp only [h1, h2, Option.some.injEq] at hev; subst hev
        cases i with
        | zero => exact h1
        | succ k => exact ih h2 k (Nat.lt_of_succ_lt_succ hl) (Nat.lt_of_succ_lt_succ hp)

private theorem evalArgsOwn_getElem {envH : HValEnv} {l : List LcArg} :
    ∀ {ws : List Word}, envH.evalArgsOwn l = some ws →
      ∀ (i : Nat) (hl : i < l.length) (hw : i < ws.length),
        envH.evalArgOwn (l[i]'hl) = some (ws[i]'hw) := by
  induction l with
  | nil => intro _ _ i hl _; cases hl
  | cons u us ih =>
    intro ws hev i hl hw
    simp only [HValEnv.evalArgsOwn] at hev
    cases h1 : envH.evalArgOwn u
    · simp [h1] at hev
    · cases h2 : envH.evalArgsOwn us
      · simp [h1, h2] at hev
      · simp only [h1, h2, Option.some.injEq] at hev; subst hev
        cases i with
        | zero => exact h1
        | succ k => exact ih h2 k (Nat.lt_of_succ_lt_succ hl) (Nat.lt_of_succ_lt_succ hw)

theorem entryRcFrame_fap_ok {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (d : LcDecl) (hndP : (d.params.map (·.id)).Nodup)
    {as : List LcArg} {ctx' : RcCtx}
    (ha : rf.ctx.applyArgs as (d.params.map (·.borrow)) = .ok ctx')
    (hmatch : argsMatchTys rf.ctx as (d.params.map (·.ty)) = true)
    (hsh : argsNoSharedTarget rf.ctx as (d.params.map (·.borrow)) = true)
    (hsurv : argsBorrowSurvive ctx' as (d.params.map (·.borrow)) = true)
    {pvs : List PVal} {ws : List Word}
    (hpvs : rf.envP.evalArgs as = some pvs) (hws : rf.envH.evalArgsOwn as = some ws) :
    let calleeExtH := localHandles ctx' rf.envH ++ rf.extH
    let calleeRf := entryRcFrame d pvs ws calleeExtH rf.ghostH
    pvs.length = d.params.length ∧ ws.length = d.params.length ∧
    RcInv rt calleeRf σ ∧ CleanVars calleeRf.ctx ∧ ParentsOwned calleeRf.ctx ∧
    HandlesInHeap (calleeExtH ++ rf.ghostH) σ.objs ∧
    RcInv rt { rf with ctx := ctx' } σ ∧ CleanVars ctx' ∧ ParentsOwned ctx' := by
  have ⟨hperm_loc, hinv_after, hclean_after, hpo_after⟩ :=
    rcInv_applyArgs_step hinv hclean hpo ha hsh
  have hlen_a : as.length = d.params.length := by
    have := hmatch; simp only [argsMatchTys, Bool.and_eq_true, beq_iff_eq] at this
    simpa using this.1
  have hlen_pvs : pvs.length = d.params.length := by
    have hlen : ∀ (xs : List LcArg) (ys : List PVal),
        rf.envP.evalArgs xs = some ys → ys.length = xs.length := by
      intro xs; induction xs with
      | nil => intro ys h; simp [PValEnv.evalArgs] at h; subst h; rfl
      | cons u us ih =>
        intro ys h; simp only [PValEnv.evalArgs] at h
        cases h1 : rf.envP.evalArg u
        · simp [h1] at h
        · cases h2 : rf.envP.evalArgs us
          · simp [h1, h2] at h
          · simp only [h1, h2, Option.some.injEq] at h; subst h; simp [ih _ h2]
    exact (hlen as pvs hpvs).trans hlen_a
  have hlen_ws : ws.length = d.params.length := by
    have hlen : ∀ (xs : List LcArg) (ys : List Word),
        rf.envH.evalArgsOwn xs = some ys → ys.length = xs.length := by
      intro xs; induction xs with
      | nil => intro ys h; simp [HValEnv.evalArgsOwn] at h; subst h; rfl
      | cons u us ih =>
        intro ys h; simp only [HValEnv.evalArgsOwn] at h
        cases h1 : rf.envH.evalArgOwn u
        · simp [h1] at h
        · cases h2 : rf.envH.evalArgsOwn us
          · simp [h1, h2] at h
          · simp only [h1, h2, Option.some.injEq] at h; subst h; simp [ih _ h2]
    exact (hlen as ws hws).trans hlen_a
  let calleeExtH := localHandles ctx' rf.envH ++ rf.extH
  let calleeRf := entryRcFrame d pvs ws calleeExtH rf.ghostH
  have hhih_loc := handlesInHeap_localHandles hinv_after hclean_after
  have hhih_callee : HandlesInHeap (calleeExtH ++ rf.ghostH) σ.objs := by
    intro a ha'
    rcases List.mem_append.mp ha' with h1 | h2
    · rcases List.mem_append.mp h1 with h1a | h1b
      · exact hhih_loc a h1a
      · exact hhih a (List.mem_append.mpr (Or.inl h1b))
    · exact hhih a (List.mem_append.mpr (Or.inr h2))
  have hlive_all := applyArgs_var_live hinv.2.1 hclean ha
  have harg_inv : ∀ i (hi : i < d.params.length),
      let p := d.params[i]
      let pv := pvs[i]'(by omega)
      let w := ws[i]'(by omega)
      ValRep p.ty pv w σ.objs ∧
      (¬p.ty.isScalar → ∃ bv, w = Word.i64 bv ∧
        (p.ty.needsRc = false → (bv &&& 1#64) ≠ 0#64) ∧
        (p.borrow = true → (bv &&& 1#64) = 0#64 →
          Backed σ.objs (calleeExtH ++ rf.ghostH) bv)) := by
    intro i hi
    have hia : i < as.length := by omega
    have hap : (as[i]'hia, d.params[i].ty) ∈ as.zip (d.params.map (·.ty)) := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by rw [List.length_zip, List.length_map]; exact Nat.lt_min.mpr ⟨hia, hi⟩, by simp⟩
    have hm1 := hmatch; simp only [argsMatchTys, Bool.and_eq_true, List.all_eq_true] at hm1
    have hmt := hm1.2 _ hap
    have h_evp := evalArgs_getElem hpvs i hia (by omega)
    have h_evh := evalArgsOwn_getElem hws i hia (by omega)
    have ham : as[i]'hia ∈ as := List.getElem_mem hia
    rcases hlive_all (as[i]'hia) ham with ha_er | ⟨z, vz, ha_z, hgz, hlz⟩
    · rw [ha_er] at h_evp h_evh hmt; dsimp only at h_evp h_evh hmt
      have hpv_eq : pvs[i]'(by omega) = .erased := by simpa [PValEnv.evalArg] using h_evp.symm
      have hw_eq : ws[i]'(by omega) = Word.i64 1#64 := by
        simpa [HValEnv.evalArgOwn] using h_evh.symm
      rw [hpv_eq, hw_eq]
      have hns_p : (d.params[i].ty).isScalar = false := by
        cases h : (d.params[i].ty).isScalar <;> simp_all
      have hno_o : d.params[i].ty ≠ .object := fun h => by rw [h] at hmt; revert hmt; decide
      have hno_t : d.params[i].ty ≠ .tagged := fun h => by rw [h] at hmt; revert hmt; decide
      refine ⟨?_, fun _ => ⟨1#64, rfl, fun _ => by decide, fun _ h => by cases h⟩⟩
      unfold ValRep; simp only [hns_p, Bool.false_eq_true, ↓reduceIte]
      exact ⟨1#64, rfl, rfl, fun h => absurd h hno_o, fun h => absurd h hno_t⟩
    · rw [ha_z] at hmt; dsimp only at hmt; rw [hgz] at hmt; dsimp only at hmt
      rw [ha_z] at h_evp h_evh
      have hzm := (RcCtx.get?_mem hgz).1
      have hzid := (RcCtx.get?_mem hgz).2
      obtain ⟨pvz, wz, hpvz, hwz, hrepz, hnonz⟩ := hinv.2.2.2.1 vz hzm hlz
      rw [hzid] at hpvz hwz
      have hpv_eq : pvs[i]'(by omega) = pvz := by
        simpa [PValEnv.evalArg, hpvz] using h_evp.symm
      have hw_eq : ws[i]'(by omega) = wz := by
        simpa [HValEnv.evalArgOwn, hwz] using h_evh.symm
      rw [hpv_eq, hw_eq]
      have ⟨hmt1, hmt2⟩ := Bool.and_eq_true _ _ |>.mp hmt
      simp only [Bool.and_eq_true, beq_iff_eq] at hmt1
      have hcast : ValRep d.params[i].ty pvz wz σ.objs :=
        valRep_cast hrepz hmt1.1.1.1 hmt1.1.1.2
          (fun h => by
            have h1 : (d.params[i].ty == .object) = true := by rw [h]; rfl
            have h2 : (vz.ty == .object) = true := (of_decide_eq_true hmt1.1.2) h1
            cases htyz : vz.ty <;> rw [htyz] at h2 <;>
              first | rfl | exact absurd h2 (by decide))
          (fun h => by
            have h1 : (d.params[i].ty == .tagged) = true := by rw [h]; rfl
            have h2 : (vz.ty == .tagged) = true := (of_decide_eq_true hmt1.2) h1
            cases htyz : vz.ty <;> rw [htyz] at h2 <;>
              first | rfl | exact absurd h2 (by decide))
      refine ⟨hcast, fun hns_p => ?_⟩
      have hns_z : ¬vz.ty.isScalar := fun h => by
        rw [h] at hmt1; exact absurd hmt1.1.1.1.symm (by simp [hns_p])
      obtain ⟨bv, hweq, hno_z, _, _, _⟩ := hnonz hns_z
      refine ⟨bv, hweq, fun hnr => ?_, fun hbr heven => ?_⟩
      · cases hpt : d.params[i].ty with
        | tagged =>
          rw [hpt] at hcast; unfold ValRep at hcast
          simp only [LcTy.isScalar] at hcast
          rcases hcast with ⟨bv', hw', _, _, ht'⟩
          rw [hweq] at hw'; cases hw'; exact ht' trivial
        | erased | void =>
          rw [hpt] at hmt2
          simp only [LcTy.isScalar, LcTy.needsRc, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
            Bool.or_eq_true] at hmt2
          rcases hmt2 with hvzt | hvzn
          · have hvzt' : vz.ty = .tagged := by
              cases h : vz.ty <;> rw [h] at hvzt <;>
                first | rfl | exact absurd hvzt (by decide)
            rw [hvzt'] at hrepz; unfold ValRep at hrepz
            simp only [LcTy.isScalar] at hrepz
            rcases hrepz with ⟨bv', hw', _, _, ht'⟩
            rw [hweq] at hw'; cases hw'; exact ht' trivial
          · exact hno_z hvzn
        | _ => simp [hpt, LcTy.isScalar, LcTy.needsRc] at hnr hns_p
      · have hbr_zip : (as[i]'hia, d.params[i].borrow) ∈ as.zip (d.params.map (·.borrow)) := by
          rw [List.mem_iff_getElem]
          exact ⟨i, by rw [List.length_zip, List.length_map]; exact Nat.lt_min.mpr ⟨hia, hi⟩,
            by simp [hbr]⟩
        have hs1 := hsurv; simp only [argsBorrowSurvive, List.all_eq_true] at hs1
        have hsz := hs1 _ hbr_zip
        rw [ha_z, hbr] at hsz; dsimp only at hsz
        cases hgz' : ctx'.get? z with
        | none => simp [hgz'] at hsz
        | some vz' =>
          rw [hgz'] at hsz; dsimp only at hsz
          have hzm' := (RcCtx.get?_mem hgz').1
          have hzid' := (RcCtx.get?_mem hgz').2
          have hns_z' : ¬vz'.ty.isScalar := fun h => by
            obtain ⟨vz0, hgz0, _, _, _, hty0, _, _, _⟩ :=
              applyArgs_get?_live_back hinv.2.1 hclean ha z hgz' hsz
            rw [hgz] at hgz0; cases hgz0
            exact hns_z (hty0 ▸ h)
          obtain ⟨_, wz', _, hwz', _, hnonz'⟩ := hinv_after.2.2.2.1 vz' hzm' hsz
          have hw_eq' : wz' = wz := by
            have := Option.some.inj (hwz'.symm.trans (hzid' ▸ hwz))
            exact (Prod.mk.inj this).2
          rw [hw_eq'] at hnonz'
          obtain ⟨bv', hweq', hno_z', hps_z', _, hbr_z'⟩ := hnonz' hns_z'
          rw [hweq] at hweq'; cases hweq'
          have hcv_z' := hclean_after vz' hzm'
          by_cases hzn : vz'.noRc = true
          · exact absurd heven (hno_z' hzn)
          · have hzn0 : vz'.noRc = false := by cases h : vz'.noRc <;> simp_all
            by_cases hzp : vz'.persistent = true
            · obtain ⟨o, ho, hoa, hrc0⟩ := hps_z' hzp heven
              exact Or.inl ⟨o, ho, hoa, hrc0⟩
            · have hzp0 : vz'.persistent = false := by cases h : vz'.persistent <;> simp_all
              by_cases hzb : vz'.borrowed = true
              · obtain ⟨hb_rf, _⟩ := hbr_z' hzn0 hzp0 hzb heven
                exact hb_rf
              · have hzb0 : vz'.borrowed = false := by cases h : vz'.borrowed <;> simp_all
                have hown_z' : 0 < vz'.owned := by
                  have := hsz; simp [RcVar.isLive, hzn0, hzp0, hzb0, hcv_z'.2.2.2.2] at this
                  exact this
                obtain ⟨o, ho, hoa⟩ := hhih_loc bv (by
                  unfold localHandles
                  refine List.mem_flatten.mpr ⟨varHandles rf.envH vz',
                    List.mem_map.mpr ⟨vz', hzm', rfl⟩, ?_⟩
                  unfold varHandles
                  rw [hzn0, hzp0, hcv_z'.2.2.2.2, beq_false_of_ne (Nat.ne_of_gt hown_z'),
                    hzid', hwz, hweq]
                  simp only [Word.toBV64?, Word.i64, beq_iff_eq.mpr heven, ↓reduceIte]
                  exact List.mem_replicate.mpr ⟨Nat.ne_of_gt hown_z', rfl⟩)
                by_cases hrc0 : o.rc = 0#32
                · exact Or.inl ⟨o, ho, hoa, hrc0⟩
                · refine Or.inr ⟨bv, ?_, NonPersistReach.refl ⟨o, ho, hoa, hrc0⟩⟩
                  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ?_)))
                  unfold localHandles
                  refine List.mem_flatten.mpr ⟨varHandles rf.envH vz',
                    List.mem_map.mpr ⟨vz', hzm', rfl⟩, ?_⟩
                  unfold varHandles
                  rw [hzn0, hzp0, hcv_z'.2.2.2.2, beq_false_of_ne (Nat.ne_of_gt hown_z'),
                    hzid', hwz, hweq]
                  simp only [Word.toBV64?, Word.i64, beq_iff_eq.mpr heven, ↓reduceIte]
                  exact List.mem_replicate.mpr ⟨Nat.ne_of_gt hown_z', rfl⟩
  have hbm := bindParams_bindAll_mem_iff d.params pvs ws hlen_pvs hlen_ws hndP ({} : RcCtx)
    PValEnv.empty HValEnv.empty (by simp) (fun u hu => by cases hu)
  have hclean_callee : CleanVars calleeRf.ctx := by
    intro v hv
    rcases hbm v hv with ⟨hc, _⟩ | ⟨i, hi, rfl, _, _⟩
    · cases hc
    · by_cases hb : d.params[i].borrow <;>
        cases hty : d.params[i].ty <;>
        simp_all [paramRcVar, CleanVar, LcTy.isScalar, LcTy.needsRc]
  have hpo_callee : ParentsOwned calleeRf.ctx := by
    intro v hv p hp
    rcases hbm v hv with ⟨hc, _⟩ | ⟨i, hi, rfl, _, _⟩
    · cases hc
    · by_cases hb : d.params[i].borrow <;> simp [hb, paramRcVar] at hp
  have hnd_callee : (calleeRf.ctx.vars.map RcVar.id).Nodup :=
    bindParams_nodup d.params ({} : RcCtx) (by simp)
  have hloc_perm := localHandles_bindParams_perm d.params ws hlen_ws hndP ({} : RcCtx)
    HValEnv.empty (by simp) (fun u hu => by cases hu)
  have hloc_empty : localHandles ({} : RcCtx) HValEnv.empty = [] := rfl
  rw [hloc_empty, List.nil_append] at hloc_perm
  have hcnt_le := entry_count_le_applyArgsHandles hinv hclean d.params as ws
    hlen_a hlen_ws hws hmatch hlive_all
  have hhs_callee : HandlesRcSound (frameHandles calleeRf) σ.objs := by
    have hperm_rf : (frameHandles rf).Perm (applyArgsHandles rf as (d.params.map (·.borrow)) ++
        (localHandles ctx' rf.envH ++ rf.extH ++ rf.ghostH)) :=
      List.perm_iff_count.mpr fun a => by
        have hpc := hperm_loc.count_eq a
        simp only [frameHandles, List.count_append] at hpc ⊢; omega
    have hperm_c : (frameHandles calleeRf).Perm
        (((d.params.zip ws).map (fun (p, w) => entryParamHandles p w)).flatten ++
          (localHandles ctx' rf.envH ++ rf.extH ++ rf.ghostH)) :=
      List.perm_iff_count.mpr fun a => by
        have hpc := hloc_perm.count_eq a
        simp only [frameHandles, calleeRf, entryRcFrame, calleeExtH, List.count_append] at hpc ⊢
        omega
    have hhs_mid := handlesRcSound_of_perm hperm_rf hinv.2.2.1
    have hhs_mid2 : HandlesRcSound
        (((d.params.zip ws).map (fun (p, w) => entryParamHandles p w)).flatten ++
          (localHandles ctx' rf.envH ++ rf.extH ++ rf.ghostH)) σ.objs :=
      handlesRcSound_of_nonPersist_count_le (fun y hy hrc => by
        have hc := hcnt_le y hy hrc
        simp only [List.count_append]
        exact Nat.add_le_add_right hc _) hhs_mid
    exact handlesRcSound_of_perm hperm_c.symm hhs_mid2
  have hvar_callee : ∀ v ∈ calleeRf.ctx.vars, VarInv v calleeRf σ.objs := by
    intro v hv hl
    rcases hbm v hv with ⟨hc, _⟩ | ⟨i, hi, rfl, hep, heh⟩
    · cases hc
    · obtain ⟨hvr, hnon⟩ := harg_inv i hi
      have hv_ty : (paramRcVar d.params[i]).ty = d.params[i].ty := by
        by_cases hb : d.params[i].borrow <;> simp [hb, paramRcVar]
      have hv_par : (paramRcVar d.params[i]).parent? = none := by
        by_cases hb : d.params[i].borrow <;> simp [hb, paramRcVar]
      refine ⟨pvs[i]'(by omega), ws[i]'(by omega), hep, ?_, ?_, fun hns => ?_⟩
      · simpa [hv_ty, calleeRf, entryRcFrame] using heh
      · simpa [hv_ty] using hvr
      · obtain ⟨bv, hweq, hnr, hbr_back⟩ := hnon (by simpa [hv_ty] using hns)
        refine ⟨bv, hweq, fun hno => ?_, fun hps => ?_, fun hex => ?_, fun _ _ hbr hev => ?_⟩
        · by_cases hb : d.params[i].borrow <;> simp [hb, paramRcVar] at hno <;>
            exact hnr (by simp [hno])
        · by_cases hb : d.params[i].borrow <;> simp [hb, paramRcVar] at hps
        · by_cases hb : d.params[i].borrow <;> simp [hb, paramRcVar] at hex
        · have hpb : d.params[i].borrow = true := by
            by_cases hb : d.params[i].borrow
            · exact hb
            · simp [hb, paramRcVar] at hbr
          have hb_ext := hbr_back hpb hev
          refine ⟨backed_mono_roots (fun r hr => ?_) hb_ext, ?_⟩
          · dsimp only [frameHandles, calleeRf, entryRcFrame, calleeExtH]
            rcases List.mem_append.mp hr with h1 | h2
            · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h1)))
            · exact List.mem_append.mpr (Or.inr h2)
          · simpa [hv_par, calleeRf, entryRcFrame, frameHandles] using hb_ext
  have hsh_callee : SharedPredInv calleeRf σ.objs := by
    intro p hp
    simp only [calleeRf, entryRcFrame, bindParams_sharedPreds] at hp
    cases hp
  exact ⟨hlen_pvs, hlen_ws, ⟨hinv.1, hnd_callee, hhs_callee, hvar_callee, hsh_callee⟩,
    hclean_callee, hpo_callee, hhih_callee, hinv_after, hclean_after, hpo_after⟩

private theorem rcInv_after_call_sharedPredInv {rt : BitVec 64} {rf : RcFrame} {σ σ' : HState}
    {x : Nat} {ty : LcTy} {as : List LcArg} {borrows : List Bool} {ctx' : RcCtx}
    {pv : PVal} {rw : Word} {ws nsWs : List Word}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (ha : rf.ctx.applyArgs as borrows = .ok ctx')
    (hsh : argsNoSharedTarget rf.ctx as borrows = true)
    (hnoexcl : argsNoExclBorrow rf.ctx as borrows = true)
    (hsh_call : ∀ p ∈ rf.ctx.sharedPreds,
      match rf.ctx.get? p.1, rf.ctx.get? p.2 with
      | some vb, some vt =>
        !vb.isLive || vt.noRc || vt.persistent || vt.owned == 0 ||
          (vt.excl && as.all (· != .var p.2))
      | _, _ => true)
    (hguard : ∀ u ∈ ctx'.vars, u.excl = true → ∀ a ∈ as, match a with
      | .erased => True
      | .var z => match rf.ctx.get? z with
        | some vz => vz.parent? ≠ some u.id ∧ ¬(vz.ty.isScalar = true ∧ vz.ty.width = 64)
        | none => True)
    (hws : rf.envH.evalArgsOwn as = some ws) (hns_sub : ∀ w, w ∈ nsWs → w ∈ ws)
    (hcall : CallPreserve nsWs ((localHandles ctx' rf.envH ++ rf.extH) ++ rf.ghostH) σ σ')
    (hinv' : RcInv rt (RcFrame.mk ctx' rf.envP rf.envH rf.extH rf.ghostH) σ)
    (_hclean'_ctx : CleanVars ctx') (hfr' : binderFreshOwned ctx' x = true)
    (hlive_all : ∀ a ∈ as,
      a = .erased ∨ ∃ z v, a = .var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true)
    {vx : RcVar} (hxid : vx.id = x) (hctx_bind : ctx'.bindOwned x ty = ctx'.put vx)
    (hnd_post : ((ctx'.bindOwned x ty).vars.map RcVar.id).Nodup)
    (hhs_post : HandlesRcSound (frameHandles
      (RcFrame.mk (ctx'.bindOwned x ty) (rf.envP.set x pv) (rf.envH.set x ty rw)
        rf.extH rf.ghostH)) σ'.objs)
    (_hext_perm_rf' : ((localHandles ctx' rf.envH ++ rf.extH) ++ rf.ghostH).Perm
      (frameHandles (RcFrame.mk ctx' rf.envP rf.envH rf.extH rf.ghostH))) :
    SharedPredInv
      (RcFrame.mk (ctx'.bindOwned x ty) (rf.envP.set x pv) (rf.envH.set x ty rw)
        rf.extH rf.ghostH) σ'.objs := by
  let ext := (localHandles ctx' rf.envH ++ rf.extH) ++ rf.ghostH
  let rf_post : RcFrame :=
    RcFrame.mk (ctx'.bindOwned x ty) (rf.envP.set x pv) (rf.envH.set x ty rw) rf.extH rf.ghostH
  intro p hp vb vt hgb hgt hbl htn htp
  dsimp only [rf_post] at hp hgb hgt; rw [hctx_bind] at hp hgb hgt
  have hp_ctx' : p ∈ ctx'.sharedPreds := by simpa [RcCtx.put] using hp
  have hfr_p : p.1 ≠ x ∧ p.2 ≠ x := by
    have hf := hfr'
    simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hf
    exact hf.1.2 p hp_ctx'
  have hgb' : ctx'.get? p.1 = some vb := by
    have hm := (RcCtx.get?_mem hgb).1; have hid := (RcCtx.get?_mem hgb).2
    rcases (RcCtx.put_mem_iff hinv'.2.1).mp hm with rfl | ⟨hbm, _⟩
    · exact absurd (hxid.symm.trans hid).symm hfr_p.1
    · have h := find?_eq_some_of_mem_nodup hinv'.2.1 hbm; rwa [hid] at h
  have hgt' : ctx'.get? p.2 = some vt := by
    have hm := (RcCtx.get?_mem hgt).1; have hid := (RcCtx.get?_mem hgt).2
    rcases (RcCtx.put_mem_iff hinv'.2.1).mp hm with rfl | ⟨htm, _⟩
    · exact absurd (hxid.symm.trans hid).symm hfr_p.2
    · have h := find?_eq_some_of_mem_nodup hinv'.2.1 htm; rwa [hid] at h
  have hps_0 := applyArgs_sharedPreds_sub ha p hp_ctx'
  obtain ⟨vb0, hgb0, hb0l, _, _, _, _, _, _⟩ :=
    applyArgs_get?_live_back hinv.2.1 hclean ha p.1 hgb' hbl
  obtain ⟨vt0, hgt0, htn0, htp0, hty0, hown_le⟩ :=
    applyArgs_get?_meta_back hinv.2.1 hclean ha p.2 hgt'
  have hsp0 := hinv.2.2.2.2 p hps_0 vb0 vt0 hgb0 hgt0 hb0l (htn0 ▸ htn) (htp0 ▸ htp)
  have henvP1 : rf_post.envP p.1 = rf.envP p.1 := by simp [rf_post, PValEnv.set, hfr_p.1]
  have henvH2 : rf_post.envH p.2 = rf.envH p.2 := by simp [rf_post, HValEnv.set, hfr_p.2]
  rw [henvP1, henvH2, ← hty0]
  by_cases hown0 : vt.owned = 0
  · refine ⟨fun htag => ?_, fun _ hlt => by omega⟩
    obtain ⟨bv, hbvH, hevbv, _⟩ := hsp0.1 htag
    exact ⟨bv, hbvH, hevbv, fun hlt => by omega⟩
  · have hown_pos : 0 < vt.owned := Nat.pos_of_ne_zero hown0
    have hown0_pos : 0 < vt0.owned := Nat.lt_of_lt_of_le hown_pos hown_le
    have hcall_p := hsh_call p hps_0
    rw [hgb0, hgt0] at hcall_p; dsimp only at hcall_p
    have hvte : vt0.excl = true ∧ as.all (· != .var p.2) = true := by
      have hown0_ne : (vt0.owned == 0) = false := beq_false_of_ne (Nat.ne_of_gt hown0_pos)
      simp only [hb0l, Bool.not_true, htn0 ▸ htn, htp0 ▸ htp, hown0_ne, Bool.false_or,
        Bool.and_eq_true] at hcall_p
      exact hcall_p
    have hcv_t0 := hclean vt0 (RcCtx.get?_mem hgt0).1
    have ht0_nb : vt0.borrowed = false := by cases hb : vt0.borrowed <;> simp_all [CleanVar]
    have hgt'_0 := applyArgs_get?_eq_of_not_mem hinv.2.1 hclean ha hgt0
      (hcv_t0.2.2.2.1 ht0_nb) hvte.2
    rw [hgt'] at hgt'_0; cases hgt'_0
    have htl : vt.isLive = true := by simp [RcVar.isLive, hown_pos]
    have hvt_ns : ¬vt.ty.isScalar := fun hs => by
      have := hcv_t0.1.2 hs; rw [this] at htn; cases htn
    obtain ⟨_, wt0, _, hwt0, _, hnon_t0⟩ := hinv.2.2.2.1 vt (RcCtx.get?_mem hgt0).1 htl
    obtain ⟨bvt, hweq_t, _, _, hex_t0, _⟩ := hnon_t0 hvt_ns
    obtain ⟨_, _, hvt_own1, hvt_obj⟩ := hex_t0 hvte.1
    refine ⟨fun htag => ?_, fun htag hlt => ?_⟩
    · obtain ⟨bv, hbvH, hevbv, hpre_0⟩ := hsp0.1 htag
      have hpid0 := (RcCtx.get?_mem hgt0).2
      have hweq_b : bv = bvt := by
        have := hwt0.symm.trans (hpid0 ▸ hbvH); rw [hweq_t] at this; cases this; rfl
      subst hweq_b
      obtain ⟨hnp0_cnt0, o_t, hot, hoat, hrct⟩ := hpre_0 hown_pos
      have hrct1 : o_t.rc = 1#32 := BitVec.eq_of_toNat_eq (by rw [hrct, hvt_own1]; rfl)
      have hwft := hinv.1.1.2.1 o_t hot
      have hnp0_t : nonPersistRefs σ.objs o_t.addr = 0 := by rw [hoat]; omega
      have hdisj := applyArgs_eval_excl_disjoint hinv hclean hpo ha hsh hnoexcl hlive_all
        (RcCtx.get?_mem hgt').1 htl hvte.1 (hguard vt (RcCtx.get?_mem hgt').1 hvte.1)
        hws (hpid0 ▸ hbvH) hot hwft hoat hrct1
      have hmem_loc : bv ∈ localHandles ctx' rf.envH := by
        unfold localHandles
        refine List.mem_flatten.mpr ⟨varHandles rf.envH vt,
          List.mem_map.mpr ⟨vt, (RcCtx.get?_mem hgt').1, rfl⟩, ?_⟩
        unfold varHandles
        rw [htn, htp, hcv_t0.2.2.2.2, hvt_own1, hpid0, hbvH]
        simp only [↓reduceIte, Bool.or_self, Word.toBV64?, Word.i64, beq_iff_eq.mpr hevbv]
        exact List.mem_replicate.mpr ⟨by omega, rfl⟩
      have hext_mem : o_t.addr ∈ ext :=
        List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (hoat ▸ hmem_loc))))
      obtain ⟨o', ho', hdeq, hrc'⟩ :=
        hcall.2 o_t hot hwft hext_mem hrct1 hnp0_t
          (fun w hw heq => hdisj w (hns_sub w hw) (hoat ▸ heq))
      refine ⟨bv, hbvH, hevbv, fun _ =>
        ⟨?_, o', ho', hdeq.1.trans hoat, by rw [hrc', hvt_own1]; rfl⟩⟩
      have hvt_post : vt ∈ rf_post.ctx.vars := by
        dsimp only [rf_post]; rw [hctx_bind]
        exact (RcCtx.put_mem_iff hinv'.2.1).mpr (Or.inr ⟨(RcCtx.get?_mem hgt').1,
          by rw [(RcCtx.get?_mem hgt').2, hxid]; exact hfr_p.2⟩)
      have hsplit := localHandles_split_var_perm hnd_post rf_post.envH hvt_post
      have hperm_s : (frameHandles rf_post).Perm (varHandles rf_post.envH vt ++
          (localHandlesExcept rf_post.ctx rf_post.envH p.2 ++ rf.extH ++ rf.ghostH)) := by
        unfold frameHandles
        rw [← (RcCtx.get?_mem hgt).2]
        exact List.perm_iff_count.mpr fun a => by
          have hpc := hsplit.count_eq a
          simp only [rf_post, List.count_append] at hpc ⊢; omega
      have hs := (handlesRcSound_of_perm hperm_s hhs_post).2 o' ho' (by rw [hrc']; decide)
      have hvh_mem : bv ∈ varHandles rf_post.envH vt := by
        unfold varHandles
        rw [htn, htp, hcv_t0.2.2.2.2, hvt_own1, (RcCtx.get?_mem hgt).2, henvH2, hbvH]
        simp only [↓reduceIte, Bool.or_self, Word.toBV64?, Word.i64, beq_iff_eq.mpr hevbv]
        exact List.mem_replicate.mpr ⟨by omega, rfl⟩
      have hcnt_pos : 1 ≤ (varHandles rf_post.envH vt).count bv := List.count_pos_iff.mpr hvh_mem
      rw [List.count_append, hdeq.1.trans hoat, hrc'] at hs
      simp only [BitVec.toNat_ofNat] at hs
      dsimp only [rf_post] at hs hcnt_pos ⊢; omega
    · obtain ⟨bv, hbvH, hevbv, o, ho, hoa, hrc_or⟩ := hsp0.2 htag hown0_pos
      have hpid0 := (RcCtx.get?_mem hgt0).2
      have hweq_b : bv = bvt := by
        have := hwt0.symm.trans (hpid0 ▸ hbvH); rw [hweq_t] at this; cases this; rfl
      subst hweq_b
      obtain ⟨o_u, hou, hoau, hrcu1⟩ := hvt_obj hevbv
      have heq := obj_addr_inj_nodup hinv.1.2 ho hou (hoa.trans hoau.symm)
      subst heq; rw [hrcu1, hvt_own1] at hrc_or
      rcases hrc_or with h0 | hlt1
      · exact absurd h0 (by decide)
      · exact absurd hlt1 (by decide)

theorem rcInv_after_call {rt : BitVec 64} {rf : RcFrame} {σ σ' : HState}
    {x : Nat} {ty rty : LcTy} {as : List LcArg} {borrows : List Bool} {ctx' : RcCtx}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (ha : rf.ctx.applyArgs as borrows = .ok ctx')
    (hfr : binderFreshOwned rf.ctx x = true)
    (hsh : argsNoSharedTarget rf.ctx as borrows = true)
    (hnoexcl : argsNoExclBorrow rf.ctx as borrows = true)
    (hsh_call : ∀ p ∈ rf.ctx.sharedPreds,
      match rf.ctx.get? p.1, rf.ctx.get? p.2 with
      | some vb, some vt =>
        !vb.isLive || vt.noRc || vt.persistent || vt.owned == 0 ||
          (vt.excl && as.all (· != .var p.2))
      | _, _ => true)
    (hguard : ∀ u ∈ ctx'.vars, u.excl = true → ∀ a ∈ as, match a with
      | .erased => True
      | .var z => match rf.ctx.get? z with
        | some vz => vz.parent? ≠ some u.id ∧ ¬(vz.ty.isScalar = true ∧ vz.ty.width = 64)
        | none => True)
    (hty : ty.isScalar = rty.isScalar ∧ ty.width = rty.width ∧
      (ty.needsRc = rty.needsRc ∨ (ty = .tobject ∧ rty = .tagged)) ∧
      (ty = .object → rty = .object) ∧ (ty = .tagged → rty = .tagged))
    {pv : PVal} {rw : Word} {ws nsWs : List Word}
    (hws : rf.envH.evalArgsOwn as = some ws)
    (hns_sub : ∀ w, w ∈ nsWs → w ∈ ws)
    (hns_isol : ∀ a : BitVec 64, (a &&& 1#64) = 0#64 →
      (∀ v ∈ rf.ctx.vars, v.isLive = true → !v.ty.isScalar = true →
        ∀ w, rf.envH v.id = some (v.ty, w) → w.toBV64? ≠ some a) →
      ∀ w ∈ nsWs, w.toBV64? ≠ some a)
    (hclean' : HeapClean rt σ')
    (hrep_r : ValRep rty pv rw σ'.objs)
    (hret_odd : ¬rty.isScalar → ¬rty.needsRc → ∃ bv, rw = Word.i64 bv ∧ (bv &&& 1#64) ≠ 0#64)
    (hhs_ret : HandlesRcSound (retHandles rty rw ++ (localHandles ctx' rf.envH ++ rf.extH) ++
      rf.ghostH) σ'.objs)
    (hcall : CallPreserve nsWs ((localHandles ctx' rf.envH ++ rf.extH) ++ rf.ghostH) σ σ') :
    let rf_post : RcFrame :=
      { ctx := ctx'.bindOwned x ty, envP := rf.envP.set x pv,
        envH := rf.envH.set x ty rw, extH := rf.extH, ghostH := rf.ghostH }
    RcInv rt rf_post σ' ∧ CleanVars rf_post.ctx ∧ ParentsOwned rf_post.ctx ∧
    HandlesInHeap (rf.extH ++ rf.ghostH) σ'.objs ∧ IsolPreserve rf σ σ' ∧
    ValRep ty pv rw σ'.objs := by
  let rf_post : RcFrame :=
    { ctx := ctx'.bindOwned x ty, envP := rf.envP.set x pv,
      envH := rf.envH.set x ty rw, extH := rf.extH, ghostH := rf.ghostH }
  change RcInv rt rf_post σ' ∧ CleanVars rf_post.ctx ∧ ParentsOwned rf_post.ctx ∧
    HandlesInHeap (rf.extH ++ rf.ghostH) σ'.objs ∧ IsolPreserve rf σ σ' ∧
    ValRep ty pv rw σ'.objs
  have ⟨_, hinv', hclean'_ctx, hpo'⟩ := rcInv_applyArgs_step hinv hclean hpo ha hsh
  have hfr' := binderFreshOwned_applyArgs hinv.2.1 hclean ha hfr
  have hlive_all := applyArgs_var_live hinv.2.1 hclean ha
  let vx : RcVar := {
    id := x, ty := ty, noRc := !ty.needsRc, persistent := false,
    owned := if !ty.needsRc then 0 else 1, borrowed := false, parent? := none,
    excl := false, resetTok := false }
  have hctx_bind : ctx'.bindOwned x ty = ctx'.put vx := by
    cases hn : ty.needsRc <;> simp [RcCtx.bindOwned, vx, hn]
  have hcv_x : CleanVar vx := by
    cases hty_c : ty <;> simp [CleanVar, vx, LcTy.isScalar, LcTy.needsRc, hty_c]
  have hrep_ty : ValRep ty pv rw σ'.objs :=
    valRep_cast hrep_r hty.1.symm hty.2.1.symm hty.2.2.2.1 hty.2.2.2.2
  have hnd_post : (rf_post.ctx.vars.map RcVar.id).Nodup := by
    dsimp only [rf_post]; rw [hctx_bind]; exact ctx'.put_nodup hinv'.2.1 vx
  have hclean_post : CleanVars rf_post.ctx := fun v hv => by
    dsimp only [rf_post] at hv; rw [hctx_bind] at hv
    rcases (RcCtx.put_mem_iff hinv'.2.1).mp hv with rfl | ⟨hum, _⟩
    · exact hcv_x
    · exact hclean'_ctx v hum
  have hne_fresh : ∀ u ∈ ctx'.vars, ∀ p, u.parent? = some p → p ≠ x := fun u hum p hp heq => by
    subst heq; have hf := hfr'
    simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hf
    exact hf.1.1 u hum (by simp [hp])
  have hpo_post : ParentsOwned rf_post.ctx := fun v hv p hp => by
    dsimp only [rf_post] at hv; rw [hctx_bind] at hv
    rcases (RcCtx.put_mem_iff hinv'.2.1).mp hv with rfl | ⟨hum, _⟩
    · simp [vx] at hp
    · obtain ⟨pv0, hpvm, hpvid, hp1, hp2, hp3⟩ := hpo' v hum p hp
      refine ⟨pv0, (RcCtx.put_mem_iff hinv'.2.1).mpr
        (Or.inr ⟨hpvm, by rw [hpvid]; exact hne_fresh v hum p hp⟩), hpvid, hp1, hp2, hp3⟩
  let ext := (localHandles ctx' rf.envH ++ rf.extH) ++ rf.ghostH
  have hcongr_ex : localHandles ctx' (rf.envH.set x ty rw) = localHandles ctx' rf.envH := by
    refine localHandles_congr_var_env x (fun y hy => by simp [HValEnv.set, hy]) ?_
    intro v hv hvid
    have hgf : ctx'.get? x = some v := by
      have h := find?_eq_some_of_mem_nodup hinv'.2.1 hv; rwa [hvid] at h
    have hnl : v.isLive = false := by
      have hf := hfr'; simp only [binderFreshOwned, Bool.and_eq_true, hgf] at hf
      cases hl : v.isLive <;> simp_all
    rw [varHandles_eq_nil_of_not_live _ hnl, varHandles_eq_nil_of_not_live _ hnl]
  have hloc_ex_perm : (localHandlesExcept ctx' (rf.envH.set x ty rw) x).Perm
      (localHandles ctx' rf.envH) := by
    rw [← hcongr_ex]; exact localHandlesExcept_fresh_perm hinv'.2.1 hfr'
  have hput_perm : (localHandles rf_post.ctx rf_post.envH).Perm
      (varHandles (rf.envH.set x ty rw) vx ++ localHandles ctx' rf.envH) := by
    dsimp only [rf_post]; rw [hctx_bind]
    exact (localHandles_put_perm hinv'.2.1 (rf.envH.set x ty rw) vx).trans
      (List.Perm.append_left _ hloc_ex_perm)
  have hvx_le_ret : ∀ a : BitVec 64,
      (varHandles (rf.envH.set x ty rw) vx).count a ≤ (retHandles rty rw).count a := by
    intro a
    by_cases hnr : ty.needsRc = true
    · have hvh : varHandles (rf.envH.set x ty rw) vx = match rw.toBV64? with
          | some bv => if (bv &&& 1#64 == 0#64) = true then [bv] else [] | none => [] := by
        unfold varHandles
        simp only [vx, hnr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.or_self,
          HValEnv.set, List.replicate_succ, List.replicate_zero]
        cases rw.toBV64? with
        | none => rfl
        | some bv => by_cases h : bv &&& 1#64 = 0#64 <;> simp [h]
      rw [hvh]
      have hty_ns : ty.isScalar = false := by
        cases ty <;> first | rfl | exact absurd hnr (by decide)
      have hrty_ns : rty.isScalar = false := by rw [← hty.1, hty_ns]
      rcases hty.2.2.1 with heq | ⟨rfl, rfl⟩
      · have hrnr : rty.needsRc = true := by rw [← heq, hnr]
        have hret : retHandles rty rw = match rw.toBV64? with
            | some bv => if (bv &&& 1#64 == 0#64) = true then [bv] else [] | none => [] := by
          unfold retHandles; simp only [hrnr, hrty_ns]
          cases rw.toBV64? with
          | none => rfl
          | some bv => by_cases h : bv &&& 1#64 = 0#64 <;> simp [h]
        rw [hret]
        cases rw.toBV64? with
        | none => exact Nat.le_refl _
        | some bv => by_cases h : bv &&& 1#64 = 0#64 <;> simp [h]
      · obtain ⟨bv, hweq, hodd⟩ := hret_odd (by decide) (by decide)
        unfold retHandles; rw [hweq]; simp [Word.toBV64?, Word.i64, beq_false_of_ne hodd]
    · have hnrf : ty.needsRc = false := by cases h : ty.needsRc <;> simp_all
      unfold varHandles; simp [vx, hnrf]
  have hperm_post : (frameHandles rf_post).Perm (varHandles (rf.envH.set x ty rw) vx ++ ext) :=
    List.perm_iff_count.mpr fun a => by
      have hpc := hput_perm.count_eq a
      simp only [frameHandles, rf_post, ext, List.count_append] at hpc ⊢; omega
  have hhs_ret' : HandlesRcSound (retHandles rty rw ++ ext) σ'.objs :=
    handlesRcSound_of_perm (List.perm_iff_count.mpr fun a => by
      simp only [ext, List.count_append]; omega) hhs_ret
  have hhs_post : HandlesRcSound (frameHandles rf_post) σ'.objs :=
    handlesRcSound_of_perm hperm_post.symm (handlesRcSound_of_count_le (fun a => by
      simp only [List.count_append]; exact Nat.add_le_add_right (hvx_le_ret a) _) hhs_ret')
  have hhih_loc' := handlesInHeap_localHandles hinv' hclean'_ctx
  have hext_in_heap : ∀ a ∈ rf.extH ++ rf.ghostH, Backed σ.objs ext a := fun a ha' => by
    obtain ⟨o, ho, hoa⟩ := hhih a ha'
    by_cases hrc0 : o.rc = 0#32
    · exact Or.inl ⟨o, ho, hoa, hrc0⟩
    · rcases List.mem_append.mp ha' with h1 | h2
      · exact Or.inr ⟨a, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h1))),
          NonPersistReach.refl ⟨o, ho, hoa, hrc0⟩⟩
      · exact Or.inr ⟨a, List.mem_append.mpr (Or.inr h2), NonPersistReach.refl ⟨o, ho, hoa, hrc0⟩⟩
  have hext_back : ∀ a, Backed σ.objs (rf.extH ++ rf.ghostH) a →
      Backed σ'.objs (rf.extH ++ rf.ghostH) a :=
    backed_of_objPres hinv.1.1.2.1 fun o ho hwf hb =>
      hcall.1.2.2.2.1 o ho hwf (backed_mono_roots (fun r hr => List.mem_append.mpr
        (by rcases List.mem_append.mp hr with h1 | h2
            · exact Or.inl (List.mem_append.mpr (Or.inr h1))
            · exact Or.inr h2)) hb)
  have hhih_post : HandlesInHeap (rf.extH ++ rf.ghostH) σ'.objs := fun a ha' => by
    obtain ⟨o, ho, hoa⟩ := hhih a ha'
    obtain ⟨o', ho', hdeq, _⟩ := hcall.1.2.2.2.1 o ho (hinv.1.1.2.1 o ho) (hoa ▸ hext_in_heap a ha')
    exact ⟨o', ho', hdeq.1.trans hoa⟩
  have hext_perm_rf' : ext.Perm (frameHandles { rf with ctx := ctx' }) :=
    List.perm_iff_count.mpr fun a => by simp only [ext, frameHandles, List.count_append]
  have hvar_ctx'_backed : ∀ (u : RcVar), u ∈ ctx'.vars → u.isLive = true →
      ∀ (bv : BitVec 64),
        ¬u.ty.isScalar → rf.envH u.id = some (u.ty, Word.i64 bv) → bv &&& 1#64 = 0#64 →
        Backed σ.objs ext bv := by
    intro u hum hul bv hns_u hw_u hev_u
    obtain ⟨_, wu, _, hwu, _, hnon_u⟩ := hinv'.2.2.2.1 u hum hul
    rw [hw_u] at hwu; cases hwu
    obtain ⟨bv', hweq, hno_u, hps_u, _, hbr_u⟩ := hnon_u hns_u; cases hweq
    have hcv_u := hclean'_ctx u hum
    by_cases hun : u.noRc = true
    · exact absurd hev_u (hno_u hun)
    · have hun0 : u.noRc = false := by cases h : u.noRc <;> simp_all
      by_cases hup : u.persistent = true
      · exact Or.inl (hps_u hup hev_u)
      · have hup0 : u.persistent = false := by cases h : u.persistent <;> simp_all
        by_cases hub : u.borrowed = true
        · exact backed_mono_roots (fun r hr => hext_perm_rf'.symm.subset hr)
            (hbr_u hun0 hup0 hub hev_u).1
        · have hub0 : u.borrowed = false := by cases h : u.borrowed <;> simp_all
          have hu_own : 0 < u.owned := by
            have := hul; simp [RcVar.isLive, hun0, hup0, hub0, hcv_u.2.2.2.2] at this; exact this
          have hmem : bv ∈ localHandles ctx' rf.envH := by
            unfold localHandles
            refine List.mem_flatten.mpr ⟨varHandles rf.envH u, List.mem_map.mpr ⟨u, hum, rfl⟩, ?_⟩
            unfold varHandles
            rw [hun0, hup0, hcv_u.2.2.2.2, beq_false_of_ne (Nat.ne_of_gt hu_own), hw_u]
            simp only [Word.toBV64?, Word.i64, beq_iff_eq.mpr hev_u, ↓reduceIte]
            exact List.mem_replicate.mpr ⟨Nat.ne_of_gt hu_own, rfl⟩
          obtain ⟨o, ho, hoa⟩ := hhih_loc' bv hmem
          by_cases hrc0 : o.rc = 0#32
          · exact Or.inl ⟨o, ho, hoa, hrc0⟩
          · exact Or.inr ⟨bv, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hmem))),
              NonPersistReach.refl ⟨o, ho, hoa, hrc0⟩⟩
  have hvar_post : ∀ u ∈ rf_post.ctx.vars, VarInv u rf_post σ'.objs := by
    intro u hu hl
    dsimp only [rf_post] at hu; rw [hctx_bind] at hu
    rcases (RcCtx.put_mem_iff hinv'.2.1).mp hu with rfl | ⟨hum, hne_u⟩
    · refine ⟨pv, rw, by simp [rf_post, vx, PValEnv.set],
        by simp [rf_post, vx, HValEnv.set], hrep_ty, fun hns => ?_⟩
      have hr_ns : ¬rty.isScalar := by rw [← hty.1]; exact hns
      by_cases hnr : vx.noRc = true
      · have htn : ty.needsRc = false := by simp [vx] at hnr; exact hnr
        have hrtn : ¬rty.needsRc := by
          rcases hty.2.2.1 with heq | ⟨rfl, rfl⟩
          · rw [← heq, htn]; decide
          · simp [LcTy.needsRc] at htn
        obtain ⟨bv, hweq, hodd⟩ := hret_odd hr_ns hrtn
        exact ⟨bv, hweq, fun _ => hodd, fun h => by simp [vx] at h,
          fun h => by simp [vx] at h, fun _ _ h => by simp [vx] at h⟩
      · have hnrf : vx.noRc = false := by cases h : vx.noRc <;> simp_all
        have hval_nv := hrep_ty; unfold ValRep at hval_nv
        simp only [show ty.isScalar = false from by cases h : ty.isScalar <;> simp_all,
          Bool.false_eq_true, ↓reduceIte] at hval_nv
        rcases hval_nv with ⟨bv, hweq, _⟩
        exact ⟨bv, hweq, fun h => absurd h (by simp [hnrf]), fun h => by simp [vx] at h,
          fun h => by simp [vx] at h, fun _ _ h => by simp [vx] at h⟩
    · obtain ⟨pu, wu, hepu, hehu, hrepu, hnonu⟩ := hinv'.2.2.2.1 u hum hl
      have hrepu' : ValRep u.ty pu wu σ'.objs :=
        valRep_mono_pred (P := fun a => Backed σ.objs ext a)
          (fun o ho hwf hp =>
            let ⟨o', ho', hdeq, _⟩ := hcall.1.2.2.2.1 o ho hwf hp; ⟨o', ho', hdeq⟩)
          (fun o ho hwf hp f hf hev => backed_trans_child_simple hinv.1.2 hinv.1.1.2.2.1
            (handlesRcSound_of_perm hext_perm_rf'.symm hinv'.2.2.1) hp ho rfl hf hev)
          hrepu fun hns bv hweq hev => hvar_ctx'_backed u hum hl bv hns (hweq ▸ hehu) hev
      have hne_ux : u.id ≠ x := by simpa [vx] using hne_u
      refine ⟨pu, wu, by simpa [rf_post, PValEnv.set, hne_ux] using hepu,
        by simpa [rf_post, HValEnv.set, hne_ux] using hehu, hrepu', fun hns => ?_⟩
      obtain ⟨bv, hweq, hno_u, hps_u, hex_u, hbr_u⟩ := hnonu hns
      refine ⟨bv, hweq, hno_u, fun hup hev => ?_, fun hue => ?_, fun hun0 hup0 hub hev => ?_⟩
      · obtain ⟨o, ho, hoa, hrc0⟩ := hps_u hup hev
        obtain ⟨o', ho', hdeq, hpres0, _⟩ :=
          hcall.1.2.2.2.1 o ho (hinv.1.1.2.1 o ho) (Or.inl ⟨o, ho, rfl, hrc0⟩)
        exact ⟨o', ho', hdeq.1.trans hoa, hpres0 hrc0⟩
      · obtain ⟨uno, ups, uown, hobj⟩ := hex_u hue
        refine ⟨uno, ups, uown, fun hev => ?_⟩
        obtain ⟨o_u, hou, hoau, hrcu⟩ := hobj hev
        have hwfu := hinv.1.1.2.1 o_u hou
        have hmem_loc : bv ∈ localHandles ctx' rf.envH := by
          unfold localHandles
          refine List.mem_flatten.mpr ⟨varHandles rf.envH u, List.mem_map.mpr ⟨u, hum, rfl⟩, ?_⟩
          unfold varHandles
          rw [uno, ups, (hclean'_ctx u hum).2.2.2.2, uown]
          simp only [↓reduceIte, Bool.or_self,
            show rf.envH u.id = some (u.ty, Word.i64 bv) from hweq ▸ hehu,
            Word.toBV64?, Word.i64, beq_iff_eq.mpr hev]
          exact List.mem_replicate.mpr ⟨by omega, rfl⟩
        have hnp0 : nonPersistRefs σ.objs o_u.addr = 0 := by
          have hs := (handlesRcSound_of_perm hext_perm_rf'.symm hinv'.2.2.1).2 o_u hou
            (by rw [hrcu]; decide)
          have hcnt : 1 ≤ ext.count o_u.addr := List.count_pos_iff.mpr
            (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (hoau ▸ hmem_loc)))))
          rw [hrcu] at hs; simp only [BitVec.toNat_ofNat] at hs; omega
        have hdisj := applyArgs_eval_excl_disjoint hinv hclean hpo ha hsh hnoexcl hlive_all
          hum hl hue (hguard u hum hue) hws (hweq ▸ hehu) hou hwfu hoau hrcu
        have hext_mem : o_u.addr ∈ ext := List.mem_append.mpr
          (Or.inl (List.mem_append.mpr (Or.inl (hoau ▸ hmem_loc))))
        obtain ⟨o', ho', hdeq, hrc'⟩ := hcall.2 o_u hou hwfu hext_mem hrcu hnp0
          (fun w hw heq => hdisj w (hns_sub w hw) (hoau ▸ heq))
        exact ⟨o', ho', hdeq.1.trans hoau, hrc'⟩
      · obtain ⟨hb_rf', hpar⟩ := hbr_u hun0 hup0 hub hev
        have hb_ext' : Backed σ'.objs ext bv := hcall.1.2.2.2.2 bv
          (backed_mono_roots (fun r hr => hext_perm_rf'.symm.subset hr) hb_rf')
        refine ⟨backed_mono_roots
          (fun r hr => hperm_post.symm.subset (List.mem_append.mpr (Or.inr hr))) hb_ext', ?_⟩
        cases hup : u.parent? with
        | none => rw [hup] at hpar; exact hext_back bv hpar
        | some p =>
          rw [hup] at hpar
          rcases hpar with ⟨pv0, hpvm, hpvid, hp1, hp2, hp3, hbp_ev⟩
          have hne_px : p ≠ x := hne_fresh u hum p hup
          refine ⟨pv0, (RcCtx.put_mem_iff hinv'.2.1).mpr
            (Or.inr ⟨hpvm, by rw [hpvid]; exact hne_px⟩), hpvid, hp1, hp2, hp3, ?_⟩
          simp only [rf_post, HValEnv.set, hne_px, ↓reduceIte]
          refine backed_of_objPres hinv.1.1.2.1 (fun o ho hwf hb => hcall.1.2.2.2.1 o ho hwf
            (backed_trans_roots hinv.1.2 hinv'.2.2.1 (fun r hr h0 => ?_) hb)) bv hbp_ev
          rcases List.mem_append.mp hr with h1 | h2
          · cases hrp : rf.envH p with
            | none => simp [hrp] at h1
            | some q =>
              rcases q with ⟨tp, wp⟩; simp only [hrp] at h1
              cases hwp : wp.toBV64? with
              | none => simp [hwp] at h1
              | some bp =>
                simp only [hwp, List.mem_singleton] at h1; subst h1
                have hpvl : pv0.isLive = true := by
                  rcases hp3 with hpo0 | hpb0
                  · simp [RcVar.isLive, hpo0]
                  · simp [RcVar.isLive, hpb0]
                have hns_pv : ¬pv0.ty.isScalar := fun hs => by
                  have := (hclean'_ctx pv0 hpvm).1.2 hs; rw [this] at hp1; cases hp1
                obtain ⟨_, wpu, _, hwpu, _, hnon_pu⟩ := hinv'.2.2.2.1 pv0 hpvm hpvl
                rw [hpvid, hrp] at hwpu; cases hwpu
                obtain ⟨bp', hweq', _⟩ := hnon_pu hns_pv
                rw [hweq'] at hwp; simp [Word.toBV64?, Word.i64] at hwp; subst hwp
                obtain ⟨o0, ho0, hoa0, _⟩ := h0
                have hev0 := obj_addr_and1_zero (hinv.1.1.2.1 o0 ho0)
                rw [hoa0] at hev0
                exact hvar_ctx'_backed pv0 hpvm hpvl bp' hns_pv (by rw [hpvid, hrp, hweq']) hev0
          · exact hext_in_heap r (by
              rcases List.mem_append.mp h2 with h2a | h2b
              · exact List.mem_append.mpr (Or.inl h2a)
              · exact List.mem_append.mpr (Or.inr h2b))
  have hsh_post : SharedPredInv rf_post σ'.objs :=
    rcInv_after_call_sharedPredInv hinv hclean hpo ha hsh hnoexcl hsh_call hguard hws hns_sub hcall
      hinv' hclean'_ctx hfr' hlive_all rfl hctx_bind hnd_post hhs_post hext_perm_rf'
  have hisol_post : IsolPreserve rf σ σ' := fun a ha' hiso => by
    rcases hiso with ⟨hlive_nl, hnp0, o, ho, hwf, hoa, hrc1⟩
    have ha_ext : a ∈ ext := List.mem_append.mpr (by
      rcases List.mem_append.mp ha' with h1 | h2
      · exact Or.inl (List.mem_append.mpr (Or.inr h1))
      · exact Or.inr h2)
    have hdisj : ∀ w ∈ nsWs, w.toBV64? ≠ some o.addr := hns_isol o.addr
      (obj_addr_and1_zero hwf) (fun v hm hl hns w hwe => hoa ▸ hlive_nl v hm hl hns w hwe)
    obtain ⟨o', ho', hdeq, hrc'⟩ := hcall.2 o ho hwf (hoa ▸ ha_ext) hrc1 (hoa ▸ hnp0) hdisj
    have hnp' : nonPersistRefs σ'.objs a = 0 := by
      have hs := hhs_ret'.2 o' ho' (by rw [hrc']; decide)
      have hcnt : 1 ≤ (retHandles rty rw ++ ext).count o'.addr :=
        List.count_pos_iff.mpr (List.mem_append.mpr (Or.inr (hdeq.1.trans hoa ▸ ha_ext)))
      rw [hrc', hdeq.1, hoa] at hs; rw [hdeq.1, hoa] at hcnt
      simp only [BitVec.toNat_ofNat] at hs; omega
    exact ⟨o', ho', hdeq.2.1, hdeq.1.trans hoa, hrc', hnp', fun o0 ho0 hoa0 => by
      have := obj_addr_inj_nodup hinv.1.2 ho0 ho (hoa0.trans hoa.symm); subst this; exact hdeq⟩
  exact ⟨⟨hclean', hnd_post, hhs_post, hvar_post, hsh_post⟩, hclean_post, hpo_post,
    hhih_post, hisol_post, hrep_ty⟩

end

end LeanQbe.T.LeanLCNF.Sem
