module

public import LeanQbe.T.LeanLCNF.Sem.Perceus2

/-!
# Perceus Tier-P → Tier-H Soundness, Part 3: Argument Consumption & Call Boundaries

Proves:
- `consumeVarHandles` and `rcInv_consumeVar_step` (`RcInv` preservation under `consumeVar`).
- `applyArgsHandles` and `rcInv_applyArgs_step` (`RcInv` & handle splitting under `applyArgs`).
- `entryRcFrame_init` and `rcInv_after_call`
  (Tier-P → Tier-H call setup & return framing for `.fap`).
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

public section

/-! ## 1. Consuming Variables (`consumeVarHandles`, `rcInv_consumeVar_step`) -/

/-- Exact multiset of heap handles released/transferred by `ctx.consumeVar x n`. -/
@[expose] def consumeVarHandles (rf : RcFrame) (x n : Nat) : List (BitVec 64) :=
  match rf.ctx.get? x with
  | none => []
  | some v =>
    if v.noRc || v.persistent || n == 0 then []
    else match rf.envH x with
      | some (_, w) => match w.toBV64? with
        | some bv => if (bv &&& 1#64) == 0#64 then List.replicate n bv else []
        | none => []
      | none => []

private theorem replicate_add {α : Type} (a b : Nat) (x : α) :
    List.replicate (a + b) x = List.replicate a x ++ List.replicate b x := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show a.succ + b = (a + b).succ from by omega, List.replicate_succ, ih,
      List.replicate_succ, List.cons_append]

private theorem varHandles_consume_eq {rf : RcFrame} {v : RcVar} (hc : CleanVar v)
    (hno : v.noRc = false) (hps : v.persistent = false) {n x : Nat} (hle : n ≤ v.owned)
    (hvid : v.id = x) :
    let v' : RcVar :=
      { v with
        owned := v.owned - n
        excl := if v.owned - n == 0 then false else v.excl
        resetTok := if v.owned - n == 0 then false else v.resetTok }
    varHandles rf.envH v = varHandles rf.envH v' ++
      (if n == 0 then []
       else match rf.envH x with
         | some (_, w) => match w.toBV64? with
           | some bv => if (bv &&& 1#64) == 0#64 then List.replicate n bv else []
           | none => []
         | none => []) := by
  intro v'
  by_cases hn0 : n = 0
  · subst hn0
    unfold varHandles
    simp only [v', hno, hps, hc.2.2.2.2]
    split <;> simp_all
  · have hne0 : (n == 0) = false := beq_false_of_ne hn0
    have hrt : v.resetTok = false := hc.2.2.2.2
    have hrt' : v'.resetTok = false := by dsimp only [v']; split <;> simp [hrt]
    have hsum : v'.owned + n = v.owned := Nat.sub_add_cancel hle
    have hvne0 : (v.owned == 0) = false := by
      have : 0 < v.owned := by omega
      cases h : v.owned <;> simp_all
    unfold varHandles
    rw [hno, hps, hrt, hvne0, hvid]
    simp only [Bool.false_or, Bool.false_eq_true, ite_false, hne0]
    cases he : rf.envH x with
    | none => simp [v']
    | some p =>
      rcases p with ⟨ty, w⟩
      cases hw : w.toBV64? with
      | none => simp [v', hw]
      | some bv =>
        by_cases hev : (bv &&& 1#64 == 0#64) = true
        · by_cases hvo : v'.owned = 0
          · simp [v', hw, hev, show v.owned = n from by omega]
          · have hvo' : (v'.owned == 0) = false := beq_false_of_ne hvo
            simp [v', hw, hvo', hev, hc.2.2.2.2]
            omega
        · simp [v', hw, hev]

private theorem localHandlesExcept_none {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (envH : HValEnv) {s : Nat} (hg : ctx.get? s = none) :
    localHandlesExcept ctx envH s = localHandles ctx envH := by
  unfold localHandlesExcept localHandles
  congr 1
  congr 1
  rw [List.filter_eq_self]
  intro v hv
  refine bne_iff_ne.mpr fun h => ?_
  have h1 := (RcCtx.mem_get?_iff hnd).mpr hv
  rw [h, hg] at h1; cases h1

private theorem varInv_backed_parent {rf : RcFrame} {objs : List LcnfObj}
    (hwf : ∀ o ∈ objs, o.Wf)
    (howned : ∀ pv ∈ rf.ctx.vars, pv.noRc = false → pv.persistent = false →
      pv.resetTok = false → 0 < pv.owned → ∃ ty w, rf.envH pv.id = some (ty, w))
    (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    {u : RcVar} (hu : u ∈ rf.ctx.vars) {bv : BitVec 64}
    (hpback : Backed objs ((match u.parent? with
      | none => []
      | some p => match rf.envH p with
        | some (_, w) => match w.toBV64? with | some bp => [bp] | none => []
        | none => []) ++ (rf.extH ++ rf.ghostH)) bv) :
    Backed objs (frameHandles rf) bv := by
  rcases hpback with ⟨o, ho, hoa, hrc0⟩ | ⟨r, hr, hreach⟩
  · exact Or.inl ⟨o, ho, hoa, hrc0⟩
  · rcases List.mem_append.mp hr with hpar | hext
    · cases hpu : u.parent? with
      | none => simp [hpu] at hpar
      | some p =>
        rw [hpu] at hpar
        obtain ⟨pv, hpvm, hpvid, hp1, hp2, hp3, _⟩ := hpo u hu p hpu
        have hprtok : pv.resetTok = false := (hclean pv hpvm).2.2.2.2
        obtain ⟨_, wp, hwp⟩ := howned pv hpvm hp1 hp2 hprtok hp3
        rw [hpvid] at hwp
        simp only [hwp] at hpar
        cases hwb : wp.toBV64? with
        | none => simp [hwb] at hpar
        | some bp =>
          simp only [hwb] at hpar
          have hreq : r = bp := by simpa using hpar
          rcases hreq.symm with rfl
          have heven : (bp &&& 1#64) = 0#64 := by
            induction hreach with
            | refl h =>
              obtain ⟨o, ho, hoa, _⟩ := h
              exact hoa ▸ obj_addr_and1_zero (hwf o ho)
            | step _ _ _ _ ih => exact ih
          have hmem_vh : bp ∈ varHandles rf.envH pv := by
            simp only [varHandles, hp1, hp2, hprtok, beq_false_of_ne (Nat.ne_of_gt hp3),
              hpvid, hwp, hwb, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
              beq_iff_eq.mpr heven]
            exact List.mem_replicate.mpr ⟨Nat.ne_of_gt hp3, rfl⟩
          have hmem_fh : bp ∈ frameHandles rf := by
            refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ?_)))
            exact List.mem_flatten.mpr
              ⟨varHandles rf.envH pv, List.mem_map.mpr ⟨pv, hpvm, rfl⟩, hmem_vh⟩
          exact Or.inr ⟨bp, hmem_fh, hreach⟩
    · rcases List.mem_append.mp hext with he1 | he2
      · exact Or.inr ⟨r, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr he1))), hreach⟩
      · exact Or.inr ⟨r, List.mem_append.mpr (Or.inr he2), hreach⟩

private theorem isLive_of_eq {u w : RcVar} (hno : w.noRc = u.noRc)
    (hps : w.persistent = u.persistent) (hown : w.owned = u.owned) (hrs : w.resetTok = u.resetTok)
    (hbr : u.borrowed = true → w.borrowed = true) (hl : u.isLive = true) : w.isLive = true := by
  simp only [RcVar.isLive, Bool.or_eq_true, decide_eq_true_eq] at hl ⊢
  rcases hl with (((h | h) | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (hno.symm ▸ h))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr (hps.symm ▸ h))))
  · exact Or.inl (Or.inl (Or.inr (hown.symm ▸ h)))
  · exact Or.inl (Or.inr (hbr h))
  · exact Or.inr (hrs.symm ▸ h)

theorem rcInv_consumeVar_step {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    {x n : Nat} {ctx' : RcCtx} (hcons : rf.ctx.consumeVar x n = .ok ctx')
    (hsh_tgt : ∀ p ∈ rf.ctx.sharedPreds, p.2 = x →
      ∀ v, rf.ctx.get? x = some v →
        v.noRc = true ∨ v.persistent = true ∨ n = 0 ∨ v.owned ≤ n) :
    let rf' : RcFrame := { rf with ctx := ctx' }
    let consH := consumeVarHandles rf x n
    (localHandles rf.ctx rf.envH).Perm (localHandles ctx' rf.envH ++ consH) ∧
    (∀ s ≠ x, (localHandlesExcept rf.ctx rf.envH s).Perm
      (localHandlesExcept ctx' rf.envH s ++ consH)) ∧
    RcInv rt rf' σ ∧ CleanVars ctx' ∧ ParentsOwned ctx' ∧
    (∀ v, rf.ctx.get? x = some v → ∀ vx', ctx'.get? x = some vx' →
      vx'.owned = (if v.noRc || v.persistent || n == 0 then v.owned else v.owned - n)) := by
  let rf' : RcFrame := { rf with ctx := ctx' }
  let consH := consumeVarHandles rf x n
  have hclean' := cleanVars_consumeVar hinv.2.1 hclean hcons
  have hnd' := consumeVar_nodup hinv.2.1 hcons
  have hpo' := parentsOwned_consumeVar hinv.2.1 hclean hpo hcons
  unfold RcCtx.consumeVar at hcons
  cases hgx : rf.ctx.get? x with
  | none => simp [hgx] at hcons
  | some v =>
    have hvid := (RcCtx.get?_mem hgx).2
    have hvm := (RcCtx.get?_mem hgx).1
    have hcv := hclean v hvm
    by_cases hskip : (v.noRc || v.persistent || n == 0) = true
    · have hctx_eq : ctx' = rf.ctx := by
        rw [hgx] at hcons; dsimp only at hcons
        cases hnop : (v.noRc || v.persistent) <;> cases hn0 : (n == 0) <;>
          simp_all [pure, Except.pure]
      have hc0 : consumeVarHandles rf x n = [] := by
        dsimp only [consumeVarHandles]; rw [hgx]
        cases hnop : (v.noRc || v.persistent) <;> cases hn0 : (n == 0) <;> simp_all
      subst hctx_eq
      refine ⟨by rw [hc0, List.append_nil], fun s _ => by rw [hc0, List.append_nil],
        hinv, hclean, hpo, fun v0 hv0 vx' hvx' => ?_⟩
      cases hv0; rw [hgx] at hvx'; cases hvx'; simp [hskip]
    · have hnop : (v.noRc || v.persistent) = false := by
        cases h : (v.noRc || v.persistent) <;> simp_all
      have hn0 : (n == 0) = false := by cases h : (n == 0) <;> simp_all
      have hno : v.noRc = false := by cases h : v.noRc <;> simp_all
      have hps : v.persistent = false := by cases h : v.persistent <;> simp_all
      have hn_pos : 0 < n := by
        have : n ≠ 0 := fun h => by subst h; simp at hn0
        omega
      simp only [hgx, hnop, hn0, Bool.false_eq_true, ↓reduceIte] at hcons
      by_cases hlt : v.owned < n
      · simp [hlt] at hcons
      · have hle : n ≤ v.owned := by omega
        simp only [ite_eq_right (fun h => absurd h (by omega : ¬v.owned < n))] at hcons
        let v' : RcVar :=
          { v with
            owned := v.owned - n
            excl := if v.owned - n == 0 then false else v.excl
            resetTok := if v.owned - n == 0 then false else v.resetTok }
        have hv'id : v'.id = x := hvid
        have hv_ne_par : (v'.parent? == some x) = false := by
          change (v.parent? == some x) = false
          cases hp : v.parent? with
          | none => rfl
          | some p =>
            obtain ⟨pv, hpvm, hpvid, _, _, _, hp4⟩ := hpo v hvm p hp
            cases hpx : (p == x)
            · simp [hpx]
            · exfalso
              have hpv_eq := rcVar_eq_of_mem_nodup hinv.2.1 hpvm hvm
                (hpvid.trans ((beq_iff_eq.mp hpx).trans hvid.symm))
              rw [hpv_eq] at hp4
              have := hcv.2.2.2.1 hp4; rw [this] at hp; cases hp
        have hcons_eq : consH = (if n == 0 then [] else match rf.envH x with
            | some (_, w) => match w.toBV64? with
              | some bv => if (bv &&& 1#64) == 0#64 then List.replicate n bv else []
              | none => []
            | none => []) := by
          simp [consH, consumeVarHandles, hgx, hno, hps, hn0]
        have hvh_split := varHandles_consume_eq hcv hno hps hle hvid (rf := rf)
        rw [← hcons_eq] at hvh_split
        have hctx_cases : ctx' = (rf.ctx.put v').invalidateChildren x ∨ ctx' = rf.ctx.put v' := by
          by_cases hz : (v.owned - n == 0 && !v.borrowed) = true
          · rw [ite_eq_left hz] at hcons; cases hcons; exact Or.inl rfl
          · rw [ite_eq_right hz] at hcons; cases hcons; exact Or.inr rfl
        have hloc_ctx' : localHandles ctx' rf.envH = localHandles (rf.ctx.put v') rf.envH := by
          rcases hctx_cases with rfl | rfl
          · exact localHandles_invalidateChildren rf.envH x
          · rfl
        have hperm_loc :
            (localHandles rf.ctx rf.envH).Perm (localHandles ctx' rf.envH ++ consH) := by
          have hp1 := localHandles_perm_filter hinv.2.1 rf.envH v hvm
          have hp2 := localHandles_put_perm hinv.2.1 rf.envH v'
          rw [hvid] at hp1; rw [hv'id] at hp2
          rw [hvh_split] at hp1
          rw [hloc_ctx']
          exact hp1.trans (by
            have hp_mid :
                (varHandles rf.envH v' ++ consH ++ localHandlesExcept rf.ctx rf.envH x).Perm
                ((varHandles rf.envH v' ++ localHandlesExcept rf.ctx rf.envH x) ++ consH) := by
              simp only [List.append_assoc]
              exact List.Perm.append_left _ List.perm_append_comm
            exact hp_mid.trans (hp2.symm.append_right consH))
        have hperm_ex : ∀ s ≠ x, (localHandlesExcept rf.ctx rf.envH s).Perm
            (localHandlesExcept ctx' rf.envH s ++ consH) := by
          intro s hsne
          have hex_ctx' : localHandlesExcept ctx' rf.envH s =
              localHandlesExcept (rf.ctx.put v') rf.envH s := by
            rcases hctx_cases with rfl | rfl
            · exact localHandlesExcept_invalidateChildren rf.envH x s
            · rfl
          rw [hex_ctx']
          rcases hgs : rf.ctx.get? s with _ | u
          · have hgs' : (rf.ctx.put v').get? s = none := by
              rw [RcCtx.put_get? hinv.2.1 v' s, hv'id, beq_false_of_ne hsne]; exact hgs
            rw [localHandlesExcept_none hinv.2.1 rf.envH hgs,
                localHandlesExcept_none (rf.ctx.put_nodup hinv.2.1 v') rf.envH hgs', ← hloc_ctx']
            exact hperm_loc
          · obtain ⟨hum, huid⟩ := RcCtx.get?_mem hgs
            have hum' : u ∈ (rf.ctx.put v').vars :=
              (RcCtx.put_mem_iff hinv.2.1).mpr (Or.inr ⟨hum, by rw [huid, hv'id]; exact hsne⟩)
            have hpU1 := localHandles_perm_filter hinv.2.1 rf.envH u hum
            have hpU2 := localHandles_perm_filter (rf.ctx.put_nodup hinv.2.1 v') rf.envH u hum'
            rw [huid] at hpU1 hpU2
            rw [hloc_ctx'] at hperm_loc
            have hpcomb := hpU1.symm.trans (hperm_loc.trans (hpU2.append_right consH))
            have hpcomb' : (varHandles rf.envH u ++ localHandlesExcept rf.ctx rf.envH s).Perm
                (varHandles rf.envH u ++
                  (localHandlesExcept (rf.ctx.put v') rf.envH s ++ consH)) := by
              simpa [List.append_assoc] using hpcomb
            exact (List.perm_append_left_iff _).mp hpcomb'
        have hhs' : HandlesRcSound (frameHandles rf') σ.objs := by
          apply handlesRcSound_of_count_le _ hinv.2.2.1
          intro a
          have hc := hperm_loc.count_eq a
          unfold frameHandles rf'
          simp only [List.count_append] at hc ⊢
          omega
        have hu_back : ∀ u ∈ ctx'.vars, u.isLive = true →
            ∃ w ∈ (rf.ctx.put v').vars,
              w.id = u.id ∧ w.ty = u.ty ∧ w.noRc = u.noRc ∧
              w.persistent = u.persistent ∧ w.owned = u.owned ∧
              w.excl = u.excl ∧ w.resetTok = u.resetTok ∧
              (u.borrowed = true → w.borrowed = true ∧ w.parent? = u.parent?) := by
          intro u hu _
          rcases hctx_cases with rfl | rfl
          · unfold RcCtx.invalidateChildren at hu
            simp only [List.mem_map] at hu
            rcases hu with ⟨w, hw, rfl⟩
            by_cases hpx : (w.parent? == some x) = true
            · refine ⟨w, hw, by simp [hpx], by simp [hpx], by simp [hpx], by simp [hpx],
                by simp [hpx], by simp [hpx], by simp [hpx], fun h => by simp [hpx] at h⟩
            · simp only [hpx, Bool.false_eq_true, ↓reduceIte]
              exact ⟨w, hw, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun h => ⟨h, rfl⟩⟩
          · exact ⟨u, hu, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun h => ⟨h, rfl⟩⟩
        have howned_env : ∀ pv ∈ ctx'.vars, pv.noRc = false → pv.persistent = false →
            pv.resetTok = false → 0 < pv.owned → ∃ ty w, rf'.envH pv.id = some (ty, w) := by
          intro pv hpvm h1 h2 h3 h4
          have hpl : pv.isLive = true := by
            simp [RcVar.isLive, h1, h2, h3, h4]
          obtain ⟨w, hw, hidw, htyw, hnow, hpsw, hownw, _, hrsw, hbrw⟩ := hu_back pv hpvm hpl
          rcases (RcCtx.put_mem_iff hinv.2.1).mp hw with rfl | ⟨hpv_old, _⟩
          · have hvl : v.isLive = true := by
              simp [RcVar.isLive, hno, hps, hcv.2.2.2.2, show 0 < v.owned by omega]
            obtain ⟨_, wv, _, hwv, _⟩ := hinv.2.2.2.1 v hvm hvl
            exact ⟨pv.ty, wv, by rw [← hidw, hv'id, ← hvid, hwv, htyw]⟩
          · have hwl := isLive_of_eq hnow hpsw hownw hrsw (fun h => (hbrw h).1) hpl
            obtain ⟨_, wp, _, hwp, _⟩ := hinv.2.2.2.1 w hpv_old hwl
            exact ⟨pv.ty, wp, by rw [← hidw, hwp, htyw]⟩
        have hvars' : ∀ u ∈ ctx'.vars, VarInv u rf' σ.objs := by
          intro u hu hlive
          obtain ⟨w, hw, hidw, htyw, hnow, hpsw, hownw, hexw, hrsw, hbrw⟩ := hu_back u hu hlive
          have hw_live := isLive_of_eq hnow hpsw hownw hrsw (fun h => (hbrw h).1) hlive
          rcases (RcCtx.put_mem_iff hinv.2.1).mp hw with rfl | ⟨hum, _⟩
          · have hv_live : v.isLive = true := by
              simp [RcVar.isLive, hno, hps, hcv.2.2.2.2, show 0 < v.owned by omega]
            obtain ⟨pu, wu, hpu, hwu, hrep, hnon⟩ := hinv.2.2.2.1 v hvm hv_live
            refine ⟨pu, wu, by rw [← hidw, hv'id, ← hvid]; exact hpu,
              by rw [← hidw, hv'id, ← hvid, ← htyw]; exact hwu, by rw [← htyw]; exact hrep, ?_⟩
            intro hns
            obtain ⟨bv, hw_bv, _, _, hexcl, h3⟩ := hnon (by rw [htyw]; exact hns)
            refine ⟨bv, hw_bv, fun h => by rw [← hnow] at h; simp [v', hno] at h,
              fun h => by rw [← hpsw] at h; simp [v', hps] at h, fun hex => ?_, ?_⟩
            · exfalso
              have hv'_ex : v'.excl = true := by rw [hexw]; exact hex
              have hv_ex : v.excl = true := by
                dsimp only [v'] at hv'_ex; split at hv'_ex <;> simp_all
              have hv_own1 := (hexcl hv_ex).2.2.1
              have hz0 : (v.owned - n == 0) = true := by
                have : v.owned - n = 0 := by omega
                simp [this]
              dsimp only [v'] at hv'_ex; simp [hz0] at hv'_ex
            · intro hn0' hp0' hb0' bv0
              obtain ⟨_, hpback⟩ := h3 hno hps (hbrw hb0').1 bv0
              have hpar_eq : u.parent? = v.parent? := (hbrw hb0').2.symm
              cases hpu : u.parent? with
              | none =>
                rw [hpu] at hpar_eq; rw [← hpar_eq] at hpback
                exact ⟨backed_mono_roots
                  (fun z hz => by
                    rcases List.mem_append.mp hz with hz1 | hz2
                    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hz1)))
                    · exact List.mem_append.mpr (Or.inr hz2))
                  hpback, by dsimp only; exact hpback⟩
              | some p =>
                rw [hpu] at hpar_eq; rw [← hpar_eq] at hpback
                obtain ⟨pv, _, hpvid, _, _, _, hpb_parent⟩ := hpback
                obtain ⟨pv', hpv'm, hpv'id, hpv'1, hpv'2, hpv'3, _⟩ := hpo' u hu p hpu
                have hback_rf' : Backed σ.objs (frameHandles rf') bv :=
                  varInv_backed_parent hinv.1.1.2.1 howned_env hclean' hpo' hu
                    (by dsimp only [rf']; rw [hpu]; exact hpb_parent)
                exact ⟨hback_rf', pv', hpv'm, hpv'id, hpv'1, hpv'2, Or.inl hpv'3, hpb_parent⟩
          · obtain ⟨pu, wu, hpu, hwu, hrep, hnon⟩ := hinv.2.2.2.1 w hum hw_live
            refine ⟨pu, wu, by rw [← hidw]; exact hpu, by rw [← hidw, ← htyw]; exact hwu,
              by rw [← htyw]; exact hrep, ?_⟩
            intro hns
            obtain ⟨bv, hw_bv, h1, h2, hexcl, h3⟩ := hnon (by rw [htyw]; exact hns)
            refine ⟨bv, hw_bv, fun h => h1 (by rw [hnow]; exact h),
              fun h => h2 (by rw [hpsw]; exact h),
              fun h => have he := hexcl (by rw [hexw]; exact h);
                ⟨hnow ▸ he.1, hpsw ▸ he.2.1, hownw ▸ he.2.2.1, he.2.2.2⟩, ?_⟩
            intro hn0' hp0' hb0' bv0
            obtain ⟨_, hpback⟩ := h3 (by rw [hnow]; exact hn0') (by rw [hpsw]; exact hp0')
              (hbrw hb0').1 bv0
            have hpar_eq : u.parent? = w.parent? := (hbrw hb0').2.symm
            cases hpu : u.parent? with
            | none =>
              rw [hpu] at hpar_eq; rw [← hpar_eq] at hpback
              exact ⟨backed_mono_roots
                (fun z hz => by
                  rcases List.mem_append.mp hz with hz1 | hz2
                  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hz1)))
                  · exact List.mem_append.mpr (Or.inr hz2))
                hpback, by dsimp only; exact hpback⟩
            | some p =>
              rw [hpu] at hpar_eq; rw [← hpar_eq] at hpback
              obtain ⟨pv, _, hpvid, _, _, _, hpb_parent⟩ := hpback
              obtain ⟨pv', hpv'm, hpv'id, hpv'1, hpv'2, hpv'3, _⟩ := hpo' u hu p hpu
              have hback_rf' : Backed σ.objs (frameHandles rf') bv :=
                varInv_backed_parent hinv.1.1.2.1 howned_env hclean' hpo' hu
                  (by dsimp only [rf']; rw [hpu]; exact hpb_parent)
              exact ⟨hback_rf', pv', hpv'm, hpv'id, hpv'1, hpv'2, Or.inl hpv'3, hpb_parent⟩
        have hsh' : SharedPredInv rf' σ.objs := by
          intro p hp vb' vx' hg1 hg2 hbl hno' hps'
          have hsp : p ∈ rf.ctx.sharedPreds := by
            dsimp only [rf'] at hp
            rcases hctx_cases with rfl | rfl
            · have hp1 : p ∈ (rf.ctx.put v').sharedPreds := by
                simpa [RcCtx.invalidateChildren] using (List.mem_filter.mp hp).1
              simpa [RcCtx.put] using hp1
            · simpa [RcCtx.put] using hp
          have hmem_b := (RcCtx.get?_mem hg1).1
          have hmem_x := (RcCtx.get?_mem hg2).1
          have hid_b := (RcCtx.get?_mem hg1).2
          have hid_x := (RcCtx.get?_mem hg2).2
          have hv_orig : ∀ w ∈ ctx'.vars, w.isLive = true →
              ∃ w0, rf.ctx.get? w.id = some w0 ∧ w0.isLive = true ∧
                w0.noRc = w.noRc ∧ w0.persistent = w.persistent ∧ w0.ty = w.ty := by
            intro w hw hwl
            obtain ⟨w1, hw1, hid1, hty1, hno1, hps1, hown1, _, hrs1, hbr1⟩ := hu_back w hw hwl
            rcases (RcCtx.put_mem_iff hinv.2.1).mp hw1 with rfl | ⟨hwm, _⟩
            · exact ⟨v, hid1 ▸ hv'id ▸ hvid ▸ (RcCtx.mem_get?_iff hinv.2.1).mpr hvm,
                by simp [RcVar.isLive, hno, hps, hcv.2.2.2.2, show 0 < v.owned by omega],
                hno1, hps1, hty1⟩
            · have hw1_live := isLive_of_eq hno1 hps1 hown1 hrs1 (fun h => (hbr1 h).1) hwl
              exact ⟨w1, hid1 ▸ (RcCtx.mem_get?_iff hinv.2.1).mpr hwm, hw1_live,
                hno1, hps1, hty1⟩
          obtain ⟨vb0, hgb0, hbl0, _⟩ := hv_orig vb' hmem_b hbl
          rw [hid_b] at hgb0
          by_cases hpx : p.2 = x
          · have hvx'_own0 : vx'.owned = 0 := by
              have hle_tgt := hsh_tgt p hsp hpx v hgx
              have hvn : v.owned ≤ n := by cases hle_tgt <;> simp_all
              have hv'_in : v' ∈ ctx'.vars := by
                rcases hctx_cases with hctx_inv | hctx_eq
                · rw [hctx_inv]
                  have hm_p : v' ∈ (rf.ctx.put v').vars :=
                    (RcCtx.put_mem_iff hinv.2.1).mpr (Or.inl rfl)
                  exact List.mem_map.mpr ⟨v', hm_p, by simp [hv_ne_par]⟩
                · rw [hctx_eq]
                  exact (RcCtx.put_mem_iff hinv.2.1).mpr (Or.inl rfl)
              have hvx'_eq := rcVar_eq_of_mem_nodup hnd' hmem_x hv'_in
                (hid_x.trans (hpx.trans hv'id.symm))
              rw [hvx'_eq]; dsimp only [v']; omega
            have hsh_old := hinv.2.2.2.2 p hsp vb0 v hgb0 (hpx ▸ hgx) hbl0 hno hps
            have hty_eq : vx'.ty = v.ty := by
              dsimp only [rf'] at hmem_x
              rcases hctx_cases with rfl | rfl
              · unfold RcCtx.invalidateChildren at hmem_x
                simp only [List.mem_map] at hmem_x
                rcases hmem_x with ⟨w, hw, rfl⟩
                by_cases hxp : (w.parent? == some x) = true
                · simp only [hxp, ↓reduceIte] at hid_x ⊢
                  rcases (RcCtx.put_mem_iff hinv.2.1).mp hw with rfl | ⟨_, hne⟩
                  · rfl
                  · rw [hv'id] at hne; exact absurd (hid_x.trans hpx) hne
                · simp only [hxp, Bool.false_eq_true, ↓reduceIte] at hid_x ⊢
                  rcases (RcCtx.put_mem_iff hinv.2.1).mp hw with rfl | ⟨_, hne⟩
                  · rfl
                  · rw [hv'id] at hne; exact absurd (hid_x.trans hpx) hne
              · rcases (RcCtx.put_mem_iff hinv.2.1).mp hmem_x with rfl | ⟨_, hne⟩
                · rfl
                · rw [hv'id] at hne; exact absurd (hid_x.trans hpx) hne
            refine ⟨fun hp0 => ?_, fun _ hown => absurd hown (by omega)⟩
            obtain ⟨bv, hev, hb0, _⟩ := hsh_old.1 hp0
            dsimp only [rf']
            exact ⟨bv, hty_eq ▸ hev, hb0, fun hown => absurd hown (by omega)⟩
          · have hux_orig : ∃ vx0 ∈ rf.ctx.vars, vx0.id = p.2 ∧ vx0.ty = vx'.ty ∧
                vx0.noRc = vx'.noRc ∧ vx0.persistent = vx'.persistent ∧
                vx0.owned = vx'.owned := by
              dsimp only [rf'] at hmem_x
              rcases hctx_cases with rfl | rfl
              · unfold RcCtx.invalidateChildren at hmem_x
                simp only [List.mem_map] at hmem_x
                rcases hmem_x with ⟨w, hw, rfl⟩
                by_cases hxp : (w.parent? == some x) = true
                · simp only [hxp, ↓reduceIte] at hid_x ⊢
                  rcases (RcCtx.put_mem_iff hinv.2.1).mp hw with rfl | ⟨hwm, _⟩
                  · exact absurd (hid_x.symm.trans hv'id) hpx
                  · exact ⟨w, hwm, hid_x, rfl, rfl, rfl, rfl⟩
                · simp only [hxp, Bool.false_eq_true, ↓reduceIte] at hid_x ⊢
                  rcases (RcCtx.put_mem_iff hinv.2.1).mp hw with rfl | ⟨hwm, _⟩
                  · exact absurd (hid_x.symm.trans hv'id) hpx
                  · exact ⟨w, hwm, hid_x, rfl, rfl, rfl, rfl⟩
              · rcases (RcCtx.put_mem_iff hinv.2.1).mp hmem_x with rfl | ⟨hwm, _⟩
                · exact absurd (hid_x.symm.trans hv'id) hpx
                · exact ⟨vx', hwm, hid_x, rfl, rfl, rfl, rfl⟩
            obtain ⟨vx0, hvx0m, hvx0id, hty0, hno0, hps0, hown0⟩ := hux_orig
            have hgx0 : rf.ctx.get? p.2 = some vx0 := by
              rw [← hvx0id]; exact (RcCtx.mem_get?_iff hinv.2.1).mpr hvx0m
            obtain ⟨h0, h1⟩ := hinv.2.2.2.2 p hsp vb0 vx0 hgb0 hgx0 hbl0
              (hno0.trans hno') (hps0.trans hps')
            constructor
            · intro hp0
              obtain ⟨bv, hev, hb0, hpos⟩ := h0 hp0
              refine ⟨bv, hty0 ▸ hev, hb0, fun hown => ?_⟩
              obtain ⟨hz, hobj⟩ := hpos (hown0 ▸ hown)
              have hcperm := (hperm_ex p.2 hpx).count_eq bv
              refine ⟨?_, ?_⟩
              · simp only [List.count_append, rf'] at hz hcperm ⊢; omega
              · rcases hobj with ⟨o, ho, hoa, hrc⟩; exact ⟨o, ho, hoa, hown0 ▸ hrc⟩
            · intro hp1 hown
              obtain ⟨bv, hev, hb0, o, ho, hoa, hrc⟩ := h1 hp1 (hown0 ▸ hown)
              exact ⟨bv, hty0 ▸ hev, hb0, o, ho, hoa, hown0 ▸ hrc⟩
        have hown_res : ∀ vx', ctx'.get? x = some vx' → vx'.owned = v.owned - n := by
          intro vx' hvx'
          have hmem_x' := (RcCtx.get?_mem hvx').1
          have hid_x' := (RcCtx.get?_mem hvx').2
          rcases hctx_cases with rfl | rfl
          · unfold RcCtx.invalidateChildren at hmem_x'
            simp only [List.mem_map] at hmem_x'
            rcases hmem_x' with ⟨w, hw, hweq⟩
            rcases (RcCtx.put_mem_iff hinv.2.1).mp hw with rfl | ⟨_, hne⟩
            · have hnp' : ¬((v'.parent? == some x) = true) := by simp [hv_ne_par]
              rw [ite_eq_right hnp'] at hweq
              rw [← hweq]
            · exfalso
              have wid_eq : w.id = x := by
                rw [← hweq] at hid_x'
                split at hid_x' <;> exact hid_x'
              exact hne (wid_eq.trans hv'id.symm)
          · rcases (RcCtx.put_mem_iff hinv.2.1).mp hmem_x' with rfl | ⟨_, hne⟩
            · rfl
            · exact absurd (hid_x'.trans hv'id.symm) hne
        exact ⟨hperm_loc, hperm_ex, ⟨hinv.1, hnd', hhs', hvars', hsh'⟩, hclean', hpo',
          fun v0 hv0 vx' hvx' => by
            cases hv0; simp only [hskip, Bool.false_eq_true, ↓reduceIte]; exact hown_res vx' hvx'⟩

/-! ## 2. Call-Argument Consumption (`applyArgsHandles`), Entry Framing, and Call Return -/

@[expose] def applyArgsHandles (rf : RcFrame) : List LcArg → List Bool → List (BitVec 64)
  | [], [] => []
  | a :: as, b :: bs =>
    if b then applyArgsHandles rf as bs
    else
      let h1 := match a with
        | .erased => []
        | .var id => consumeVarHandles rf id 1
      h1 ++ applyArgsHandles rf as bs
  | _, _ => []

private theorem find?_map_of_id_eq {f : RcVar → RcVar} (hf : ∀ v, (f v).id = v.id)
    (l : List RcVar) (z : Nat) :
    (l.map f).find? (fun v => v.id == z) = (l.find? (fun v => v.id == z)).map f := by
  induction l with
  | nil => rfl
  | cons u us ih =>
    simp only [List.map_cons, List.find?_cons, hf]
    cases h : (u.id == z) <;> simp [ih]

theorem consumeVar_sharedPreds_sub {ctx : RcCtx} {x n : Nat} {ctx' : RcCtx}
    (hc : ctx.consumeVar x n = .ok ctx') : ∀ p ∈ ctx'.sharedPreds, p ∈ ctx.sharedPreds := by
  unfold RcCtx.consumeVar at hc
  cases hgx : ctx.get? x with
  | none => simp [hgx] at hc
  | some v =>
    rw [hgx] at hc; dsimp only at hc
    by_cases h1 : (v.noRc || v.persistent) = true
    · simp only [h1, ↓reduceIte, pure] at hc; cases hc; exact fun _ h => h
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hc
      by_cases h2 : (n == 0) = true
      · simp only [h2, ↓reduceIte, pure] at hc; cases hc; exact fun _ h => h
      · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hc
        by_cases h3 : v.owned < n
        · simp [h3] at hc
        · simp only [h3, ↓reduceIte] at hc
          by_cases h4 : (v.owned - n == 0 && !v.borrowed) = true
          · rw [ite_eq_left h4] at hc; cases hc
            intro p hp
            exact (by simpa [RcCtx.put] using (List.mem_filter.mp hp).1 : p ∈ ctx.sharedPreds)
          · rw [ite_eq_right h4] at hc; cases hc
            intro p hp; simpa [RcCtx.put] using hp

theorem applyArgs_sharedPreds_sub {ctx : RcCtx} {as : List LcArg} {bs : List Bool}
    {ctx' : RcCtx} (ha : ctx.applyArgs as bs = .ok ctx') :
    ∀ p ∈ ctx'.sharedPreds, p ∈ ctx.sharedPreds := by
  induction as generalizing ctx bs with
  | nil =>
    cases bs with
    | nil =>
      simp only [RcCtx.applyArgs, pure, Except.pure, Except.ok.injEq] at ha
      subst ha; exact fun _ h => h
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
        | ok _ => simp only [hchk] at ha; exact ih ha
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
        cases hcarg : ctx.consumeArg a with
        | error _ => simp [hcarg] at ha
        | ok ctx1 =>
          simp only [hcarg] at ha
          have hsub1 : ∀ p ∈ ctx1.sharedPreds, p ∈ ctx.sharedPreds := by
            cases a with
            | erased => simp [RcCtx.consumeArg, pure] at hcarg; cases hcarg; exact fun _ h => h
            | var id => exact consumeVar_sharedPreds_sub hcarg
          exact fun p hp => hsub1 p (ih ha p hp)

theorem applyArgs_nodup {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    {as : List LcArg} {bs : List Bool} {ctx' : RcCtx} (ha : ctx.applyArgs as bs = .ok ctx') :
    (ctx'.vars.map RcVar.id).Nodup := by
  induction as generalizing ctx bs with
  | nil =>
    cases bs with
    | nil =>
      simp only [RcCtx.applyArgs, pure, Except.pure, Except.ok.injEq] at ha; subst ha; exact hnd
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
        | ok _ => simp only [hchk] at ha; exact ih hnd ha
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
        cases hcarg : ctx.consumeArg a with
        | error _ => simp [hcarg] at ha
        | ok ctx1 =>
          simp only [hcarg] at ha
          cases a with
          | erased =>
            simp [RcCtx.consumeArg, pure, Except.pure] at hcarg; cases hcarg; exact ih hnd ha
          | var id => exact ih (consumeVar_nodup hnd hcarg) ha

theorem consumeVar_preserves_flags {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    {x n : Nat} {ctx' : RcCtx} (hc : ctx.consumeVar x n = .ok ctx') (z : Nat) :
    (ctx'.get? z).map (fun v => (v.noRc, v.persistent, v.ty)) =
      (ctx.get? z).map (fun v => (v.noRc, v.persistent, v.ty)) := by
  unfold RcCtx.consumeVar at hc
  cases hgx : ctx.get? x with
  | none => simp [hgx] at hc
  | some v =>
    rw [hgx] at hc; dsimp only at hc
    by_cases h1 : (v.noRc || v.persistent || n == 0) = true
    · have hctx_eq : ctx' = ctx := by
        cases hn : (v.noRc || v.persistent) <;> cases hnn : (n == 0) <;>
          simp_all [pure, Except.pure]
      subst hctx_eq; rfl
    · have hnop : (v.noRc || v.persistent) = false := by
        cases h : (v.noRc || v.persistent) <;> simp_all
      have hn0 : (n == 0) = false := by cases h : (n == 0) <;> simp_all
      simp only [hnop, hn0, Bool.false_eq_true, ↓reduceIte] at hc
      by_cases hlt : v.owned < n
      · simp [hlt] at hc
      · simp only [hlt, ↓reduceIte] at hc
        let v' : RcVar :=
          { v with owned := v.owned - n
                   excl := if v.owned - n == 0 then false else v.excl
                   resetTok := if v.owned - n == 0 then false else v.resetTok }
        have hv'id : v'.id = x := (RcCtx.get?_mem hgx).2
        have hput : (ctx.put v').get? z =
            if z == x then some v' else ctx.get? z := by
          rw [RcCtx.put_get? hnd v' z, hv'id]
        by_cases hinv : (v.owned - n == 0 && !v.borrowed) = true
        · rw [ite_eq_left hinv] at hc; cases hc
          have hginv : ((ctx.put v').invalidateChildren x).get? z =
              ((ctx.put v').get? z).map
                (fun w => if w.parent? == some x then
                  { w with borrowed := false, parent? := none } else w) := by
            unfold RcCtx.get? RcCtx.invalidateChildren
            exact find?_map_of_id_eq (fun w => by split <;> rfl) (ctx.put v').vars z
          rw [hginv, hput]
          by_cases hzx : z = x
          · subst hzx; simp only [beq_self_eq_true, ↓reduceIte, hgx]
            dsimp only [Option.map]; split <;> rfl
          · simp only [beq_false_of_ne hzx, Bool.false_eq_true, ↓reduceIte]
            cases ctx.get? z <;> dsimp only [Option.map] <;> try split <;> rfl
        · rw [ite_eq_right hinv] at hc; cases hc
          rw [hput]
          by_cases hzx : z = x
          · subst hzx; simp [hgx, v']
          · simp [beq_false_of_ne hzx]

theorem consumeVarHandles_congr_ctx {rf : RcFrame} {ctx' : RcCtx} (x n : Nat)
    (hfl : (ctx'.get? x).map (fun v => (v.noRc, v.persistent, v.ty)) =
      (rf.ctx.get? x).map (fun v => (v.noRc, v.persistent, v.ty))) :
    consumeVarHandles { rf with ctx := ctx' } x n = consumeVarHandles rf x n := by
  unfold consumeVarHandles
  cases hg1 : ctx'.get? x <;> cases hg2 : rf.ctx.get? x
  · rfl
  · simp [hg1, hg2] at hfl
  · simp [hg1, hg2] at hfl
  · simp only [hg1, hg2, Option.map, Option.some.injEq, Prod.mk.injEq] at hfl
    dsimp only; simp only [hfl.1, hfl.2.1]

theorem invalidateChildren_live_back {ctx : RcCtx} (x : Nat)
    {w' : RcVar} (hm : w' ∈ (ctx.invalidateChildren x).vars) :
    ∃ w ∈ ctx.vars, w'.id = w.id ∧ w'.ty = w.ty ∧ w'.noRc = w.noRc ∧
      w'.persistent = w.persistent ∧ w'.owned = w.owned ∧ w'.excl = w.excl ∧
      w'.resetTok = w.resetTok ∧
      (w'.borrowed = true → w.borrowed = true ∧ w.parent? = w'.parent?) := by
  unfold RcCtx.invalidateChildren at hm
  simp only [List.mem_map] at hm
  rcases hm with ⟨w, hw, rfl⟩
  by_cases hxp : (w.parent? == some x) = true
  · exact ⟨w, hw, by simp [hxp], by simp [hxp], by simp [hxp], by simp [hxp],
      by simp [hxp], by simp [hxp], by simp [hxp], fun hb => by simp [hxp] at hb⟩
  · simp only [hxp, Bool.false_eq_true, ↓reduceIte]
    exact ⟨w, hw, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun hb => ⟨hb, rfl⟩⟩

theorem consumeVar_get?_live_back {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hc : CleanVars ctx) {x n : Nat} {ctx' : RcCtx} (hcons : ctx.consumeVar x n = .ok ctx')
    (z : Nat) {w' : RcVar} (hg' : ctx'.get? z = some w') (hlive : w'.isLive = true) :
    ∃ w, ctx.get? z = some w ∧ w.isLive = true ∧ w.noRc = w'.noRc ∧
      w.persistent = w'.persistent ∧ w.ty = w'.ty ∧ w'.owned ≤ w.owned ∧
      (w'.borrowed = true → w.borrowed = true ∧ w.parent? = w'.parent?) ∧
      (w'.excl = true → w.excl = true ∧ (z = x → n = 0 ∨ w'.owned + n = w.owned)) := by
  have hmem' := (RcCtx.get?_mem hg').1
  have hid' := (RcCtx.get?_mem hg').2
  unfold RcCtx.consumeVar at hcons
  cases hgx : ctx.get? x with
  | none => simp [hgx] at hcons
  | some v =>
    rw [hgx] at hcons; dsimp only at hcons
    by_cases hskip : (v.noRc || v.persistent || n == 0) = true
    · have hctx_eq : ctx' = ctx := by
        cases h1 : (v.noRc || v.persistent) <;> cases h2 : (n == 0) <;>
          simp_all [pure, Except.pure]
      subst hctx_eq
      refine ⟨w', hg', hlive, rfl, rfl, rfl, Nat.le_refl _, fun h => ⟨h, rfl⟩, fun hexc => ?_⟩
      refine ⟨hexc, fun hzx => ?_⟩
      subst hzx
      rw [hgx] at hg'; cases hg'
      have hcv := hc w' (RcCtx.get?_mem hgx).1
      by_cases hnp : (w'.noRc || w'.persistent) = true
      · exfalso
        cases hnr : w'.noRc <;> cases hps : w'.persistent <;> simp_all
        · exact absurd hexc (by simp [hcv.2.1 hps])
        · exact absurd hexc (by simp [(hcv.1.1 hnr).2.2.2.2])
        · exact absurd hexc (by simp [(hcv.1.1 hnr).2.2.2.2])
      · have : (n == 0) = true := by cases h : (n == 0) <;> simp_all
        exact Or.inl (beq_iff_eq.mp this)
    · have hnop : (v.noRc || v.persistent) = false := by
        cases h : (v.noRc || v.persistent) <;> simp_all
      have hn0 : (n == 0) = false := by cases h : (n == 0) <;> simp_all
      simp only [hnop, hn0, Bool.false_eq_true, ↓reduceIte] at hcons
      by_cases hlt : v.owned < n
      · simp [hlt] at hcons
      · simp only [hlt, ↓reduceIte] at hcons
        let v' : RcVar :=
          { v with owned := v.owned - n
                   excl := if v.owned - n == 0 then false else v.excl
                   resetTok := if v.owned - n == 0 then false else v.resetTok }
        have hv'id : v'.id = x := (RcCtx.get?_mem hgx).2
        have hcv := hc v (RcCtx.get?_mem hgx).1
        have hno : v.noRc = false := by cases h : v.noRc <;> simp_all
        have hps : v.persistent = false := by cases h : v.persistent <;> simp_all
        have hw1_back : ∃ w1 ∈ (ctx.put v').vars, w'.id = w1.id ∧ w'.ty = w1.ty ∧
            w'.noRc = w1.noRc ∧ w'.persistent = w1.persistent ∧ w'.owned = w1.owned ∧
            w'.excl = w1.excl ∧ w'.resetTok = w1.resetTok ∧
            (w'.borrowed = true → w1.borrowed = true ∧ w1.parent? = w'.parent?) := by
          by_cases hinv : (v.owned - n == 0 && !v.borrowed) = true
          · rw [ite_eq_left hinv] at hcons; cases hcons
            exact invalidateChildren_live_back x hmem'
          · rw [ite_eq_right hinv] at hcons; cases hcons
            exact ⟨w', hmem', rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun hb => ⟨hb, rfl⟩⟩
        obtain ⟨w1, hw1m, hid1, hty1, hno1, hps1, hown1, hex1, hrs1, hbr1⟩ := hw1_back
        rcases (RcCtx.put_mem_iff hnd).mp hw1m with rfl | ⟨hwm, hne⟩
        · have hxz : x = z := hv'id.symm.trans (hid1.symm.trans hid')
          refine ⟨v, hxz ▸ hgx, ?_, hno1.symm, hps1.symm, hty1.symm,
            by rw [hown1]; exact Nat.sub_le _ _, fun h => hbr1 h, ?_⟩
          · unfold RcVar.isLive
            simp [hno, hps, hcv.2.2.2.2]
            have : 0 < v.owned := by
              have : n ≠ 0 := fun h => by subst h; simp at hn0
              omega
            simp [this]
          · intro hexc
            have hexc' : v'.excl = true := by rw [← hex1]; exact hexc
            have hnz : v.owned - n ≠ 0 := by intro hz; simp [hz, v'] at hexc'
            refine ⟨?_, fun _ => Or.inr (by rw [hown1]; dsimp only [v']; omega)⟩
            dsimp only [v'] at hexc'; simp [hnz] at hexc'; exact hexc'
        · have hne' : w1.id ≠ x := hv'id ▸ hne
          have hgw : ctx.get? z = some w1 := by
            rw [← hid', hid1]; exact (RcCtx.mem_get?_iff hnd).mpr hwm
          have hw1_live := isLive_of_eq hno1.symm hps1.symm hown1.symm hrs1.symm
            (fun h => (hbr1 h).1) hlive
          exact ⟨w1, hgw, hw1_live, hno1.symm, hps1.symm, hty1.symm,
            by rw [hown1]; exact Nat.le_refl _, fun h => hbr1 h,
            fun he => ⟨hex1 ▸ he, fun h => absurd (h ▸ (hid1.symm.trans hid')) hne'⟩⟩

theorem binderFreshOwned_consumeVar {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hc : CleanVars ctx) {x n y : Nat} {ctx' : RcCtx}
    (hcons : ctx.consumeVar x n = .ok ctx') (hfr : binderFreshOwned ctx y = true) :
    binderFreshOwned ctx' y = true := by
  simp only [binderFreshOwned, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hfr ⊢
  refine ⟨⟨?_, fun p hp => hfr.1.2 p (consumeVar_sharedPreds_sub hcons p hp)⟩, ?_⟩
  · intro u hu
    unfold RcCtx.consumeVar at hcons
    cases hgx : ctx.get? x with
    | none => simp [hgx] at hcons
    | some v =>
      rw [hgx] at hcons; dsimp only at hcons
      by_cases hskip : (v.noRc || v.persistent || n == 0) = true
      · have : ctx' = ctx := by
          cases h1 : (v.noRc || v.persistent) <;> cases h2 : (n == 0) <;>
            simp_all [pure, Except.pure]
        subst this; exact hfr.1.1 u hu
      · have hnop : (v.noRc || v.persistent) = false := by
          cases h : (v.noRc || v.persistent) <;> simp_all
        have hn0 : (n == 0) = false := by cases h : (n == 0) <;> simp_all
        simp only [hnop, hn0, Bool.false_eq_true, ↓reduceIte] at hcons
        by_cases hlt : v.owned < n
        · simp [hlt] at hcons
        · simp only [hlt, ↓reduceIte] at hcons
          let v' : RcVar :=
            { v with owned := v.owned - n
                     excl := if v.owned - n == 0 then false else v.excl
                     resetTok := if v.owned - n == 0 then false else v.resetTok }
          have hmem : ∀ w ∈ (ctx.put v').vars, w.parent? ≠ some y := by
            intro w hw
            rcases (RcCtx.put_mem_iff hnd).mp hw with rfl | ⟨hwm, _⟩
            · exact hfr.1.1 v (RcCtx.get?_mem hgx).1
            · exact hfr.1.1 w hwm
          by_cases hinv : (v.owned - n == 0 && !v.borrowed) = true
          · rw [ite_eq_left hinv] at hcons; cases hcons
            unfold RcCtx.invalidateChildren at hu
            simp only [List.mem_map] at hu
            rcases hu with ⟨w, hw, rfl⟩
            by_cases hpx : (w.parent? == some x) = true
            · simp [hpx]
            · simp only [hpx, Bool.false_eq_true, ↓reduceIte]; exact hmem w hw
          · rw [ite_eq_right hinv] at hcons; cases hcons; exact hmem u hu
  · cases hgy : ctx'.get? y with
    | none => rfl
    | some u' =>
      by_cases hl : u'.isLive = true
      · exfalso
        obtain ⟨u, hgu, hul, _⟩ := consumeVar_get?_live_back hnd hc hcons y hgy hl
        have := hfr.2; rw [hgu] at this; simp [hul] at this
      · simp [hl]

theorem binderFreshOwned_applyArgs {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hc : CleanVars ctx) {as : List LcArg} {bs : List Bool} {ctx' : RcCtx}
    (ha : ctx.applyArgs as bs = .ok ctx') {y : Nat} (hfr : binderFreshOwned ctx y = true) :
    binderFreshOwned ctx' y = true := by
  induction as generalizing ctx bs with
  | nil =>
    cases bs with
    | nil =>
      simp only [RcCtx.applyArgs, pure, Except.pure, Except.ok.injEq] at ha; subst ha; exact hfr
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
        | ok _ => simp only [hchk] at ha; exact ih hnd hc ha hfr
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
        cases hcarg : ctx.consumeArg a with
        | error _ => simp [hcarg] at ha
        | ok ctx1 =>
          simp only [hcarg] at ha
          cases a with
          | erased =>
            simp [RcCtx.consumeArg, pure, Except.pure] at hcarg; cases hcarg
            exact ih hnd hc ha hfr
          | var id =>
            exact ih (consumeVar_nodup hnd hcarg) (cleanVars_consumeVar hnd hc hcarg) ha
              (binderFreshOwned_consumeVar hnd hc hcarg hfr)

theorem rcInv_applyArgs_step {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    {as : List LcArg} {bs : List Bool} {ctx' : RcCtx}
    (ha : rf.ctx.applyArgs as bs = .ok ctx')
    (hsh : argsNoSharedTarget rf.ctx as bs = true) :
    (localHandles rf.ctx rf.envH).Perm (localHandles ctx' rf.envH ++ applyArgsHandles rf as bs) ∧
    RcInv rt { rf with ctx := ctx' } σ ∧ CleanVars ctx' ∧ ParentsOwned ctx' := by
  induction as generalizing rf bs with
  | nil =>
    cases bs with
    | nil =>
      simp only [RcCtx.applyArgs, pure, Except.pure, Except.ok.injEq] at ha; subst ha
      exact ⟨by simp [applyArgsHandles], hinv, hclean, hpo⟩
    | cons _ _ => simp [RcCtx.applyArgs] at ha
  | cons a as ih =>
    cases bs with
    | nil => simp [RcCtx.applyArgs] at ha
    | cons b bs =>
      simp only [RcCtx.applyArgs, bind, Except.bind] at ha
      have hsh1 := hsh
      simp only [argsNoSharedTarget, List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hsh1
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte] at ha
        cases hchk : rf.ctx.checkArgLive a with
        | error _ => simp [hchk] at ha
        | ok _ =>
          simp only [hchk] at ha
          obtain ⟨hp, hi, hc, hp2⟩ := ih hinv hclean hpo ha hsh1.2
          refine ⟨?_, hi, hc, hp2⟩
          simpa [applyArgsHandles, hb] using hp
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
        cases hcarg : rf.ctx.consumeArg a with
        | error _ => simp [hcarg] at ha
        | ok ctx1 =>
          simp only [hcarg] at ha
          cases a with
          | erased =>
            simp only [RcCtx.consumeArg, pure, Except.pure] at hcarg; cases hcarg
            obtain ⟨hp, hi, hc, hp2⟩ := ih hinv hclean hpo ha hsh1.2
            refine ⟨?_, hi, hc, hp2⟩
            simpa [applyArgsHandles, hb] using hp
          | var id =>
            have hsh_tgt : ∀ p ∈ rf.ctx.sharedPreds, p.2 = id →
                ∀ v, rf.ctx.get? id = some v →
                  v.noRc = true ∨ v.persistent = true ∨ (1 : Nat) = 0 ∨ v.owned ≤ 1 := by
              intro p hp hpeq
              have hall := hsh1.1
              simp only [hb, Bool.false_eq_true, ↓reduceIte, List.all_eq_true, bne_iff_ne] at hall
              exact absurd hpeq (hall p hp)
            obtain ⟨hp1, _, hi1, hc1, hp_1, _⟩ :=
              rcInv_consumeVar_step hinv hclean hpo hcarg hsh_tgt
            let rf1 : RcFrame := { rf with ctx := ctx1 }
            have hsh_next : argsNoSharedTarget ctx1 as bs = true := by
              have h2 := hsh1.2
              simp only [argsNoSharedTarget, List.all_eq_true] at h2 ⊢
              intro p hp
              rcases p with ⟨pa, pb⟩
              have this := h2 (pa, pb) hp
              dsimp only at this ⊢
              cases pa with
              | erased => exact this
              | var y =>
                by_cases hbr : pb = true
                · simp [hbr]
                · simp only [hbr, Bool.false_eq_true, ↓reduceIte, List.all_eq_true] at this ⊢
                  exact fun q hq => this q (consumeVar_sharedPreds_sub hcarg q hq)
            obtain ⟨hp2, hi2, hc2, hp_2⟩ := ih hi1 hc1 hp_1 ha hsh_next
            have hcongr : applyArgsHandles rf1 as bs = applyArgsHandles rf as bs := by
              have hflags := consumeVar_preserves_flags hinv.2.1 hcarg
              clear ih hp1 hp2 hi1 hc1 hp_1 hi2 hc2 hp_2 ha hsh_next hsh1 hsh
              induction as generalizing bs with
              | nil => cases bs <;> rfl
              | cons u us ihu =>
                cases bs with
                | nil => rfl
                | cons c cs =>
                  by_cases hc_b : c = true
                  · simp [applyArgsHandles, hc_b, ihu cs]
                  · simp only [applyArgsHandles, hc_b, Bool.false_eq_true, ↓reduceIte]
                    rw [ihu cs]
                    cases u with
                    | erased => rfl
                    | var z =>
                      have hc_eq := consumeVarHandles_congr_ctx (rf := rf) z 1 (hflags z)
                      simpa [rf1] using hc_eq
            rw [hcongr] at hp2
            refine ⟨hp1.trans ?_, hi2, hc2, hp_2⟩
            have hperm_app := hp2.append_right (consumeVarHandles rf id 1)
            refine hperm_app.trans ?_
            simp only [applyArgsHandles, hb, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
            exact List.Perm.append_left _ List.perm_append_comm

theorem handlesInHeap_localHandles {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) :
    HandlesInHeap (localHandles rf.ctx rf.envH) σ.objs := by
  intro a ha
  unfold localHandles at ha
  obtain ⟨hs, hhm, hinhs⟩ := List.mem_flatten.mp ha
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hhm
  unfold varHandles at hinhs
  split at hinhs
  · cases hinhs
  · rename_i hcond
    have hno : v.noRc = false := by cases h : v.noRc <;> simp_all
    have hps : v.persistent = false := by cases h : v.persistent <;> simp_all
    have hrt : v.resetTok = false := (hclean v hv).2.2.2.2
    have hown : v.owned ≠ 0 := by
      intro hz; simp [hz, hno, hps, hrt] at hcond
    have hlive : v.isLive = true := by
      simp [RcVar.isLive, hno, hps, hrt, Nat.pos_of_ne_zero hown]
    have hns : ¬v.ty.isScalar := fun hs => by
      have := (hclean v hv).1.2 hs; rw [this] at hno; cases hno
    cases he : rf.envH v.id with
    | none => simp [he] at hinhs
    | some p =>
      rcases p with ⟨ty, w⟩
      rw [he] at hinhs; dsimp only at hinhs
      cases hw : w.toBV64? with
      | none => simp [hw] at hinhs
      | some bv =>
        rw [hw] at hinhs; dsimp only at hinhs
        by_cases hev : (bv &&& 1#64 == 0#64) = true
        · rw [ite_eq_left hev] at hinhs
          have heqa := List.eq_of_mem_replicate hinhs
          subst heqa
          obtain ⟨pv, w0, _, hw0, hrep0, hnon0⟩ := hinv.2.2.2.1 v hv hlive
          obtain ⟨bv0, hweq, _⟩ := hnon0 hns
          subst hweq
          have : bv0 = a := by
            rw [hw0] at he; cases he; simp [Word.toBV64?, Word.i64] at hw; exact hw
          subst this
          exact valRep_even_mem hrep0 hns (beq_iff_eq.mp hev)
        · rw [ite_eq_right hev] at hinhs; cases hinhs

theorem valRep_cast {ty1 ty2 : LcTy} {pv : PVal} {w : Word} {objs : List LcnfObj}
    (hrep : ValRep ty1 pv w objs) (hsc : ty1.isScalar = ty2.isScalar)
    (hw : ty1.width = ty2.width) (hobj : ty2 = .object → ty1 = .object)
    (htag : ty2 = .tagged → ty1 = .tagged) : ValRep ty2 pv w objs := by
  unfold ValRep at hrep ⊢
  by_cases hs : ty2.isScalar = true
  · have hs1 : ty1.isScalar = true := hsc.trans hs
    simp only [hs1, ↓reduceIte] at hrep
    simp only [hs, ↓reduceIte, ← hw]; exact hrep
  · have hs1 : ty1.isScalar = false := by cases h : ty1.isScalar <;> simp_all
    have hs2 : ty2.isScalar = false := by cases h : ty2.isScalar <;> simp_all
    simp only [hs1, Bool.false_eq_true, ↓reduceIte] at hrep
    simp only [hs2, Bool.false_eq_true, ↓reduceIte]
    rcases hrep with ⟨bv, hw64, hobjr, ho1, ht1⟩
    exact ⟨bv, hw64, hobjr, fun h => ho1 (hobj h), fun h => ht1 (htag h)⟩

private theorem nonPersistReach_target_nonzero {objs : List LcnfObj} {r u : BitVec 64}
    (h : NonPersistReach objs r u) : ∃ o ∈ objs, o.addr = u ∧ o.rc ≠ 0#32 := by
  induction h with
  | refl h0 => exact h0
  | step _ _ _ hnz _ => exact hnz

private theorem nonPersistRefs_pos_of_mem (objs : List LcnfObj) {o : LcnfObj} (ho : o ∈ objs)
    (hne : o.rc ≠ 0#32) {a : BitVec 64} (ha : a ∈ o.childFields) : 0 < nonPersistRefs objs a := by
  have hm : ∀ (l : List LcnfObj) (acc : Nat),
      acc ≤ l.foldl (fun k p => if p.rc = 0#32 then k else k + p.childFields.count a) acc := by
    intro l
    induction l with
    | nil => intro acc; exact Nat.le_refl acc
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons]
      split
      · exact ih acc
      · exact Nat.le_trans (Nat.le_add_right _ _) (ih _)
  have haux : ∀ (l : List LcnfObj) (acc : Nat), o ∈ l →
      0 < l.foldl (fun k p => if p.rc = 0#32 then k else k + p.childFields.count a) acc := by
    intro l
    induction l with
    | nil => intro _ h; cases h
    | cons x xs ih =>
      intro acc h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with rfl | hxs
      · simp only [hne, ↓reduceIte]
        have hc : 0 < o.childFields.count a := List.count_pos_iff.mpr ha
        exact Nat.lt_of_lt_of_le (by omega) (hm xs (acc + o.childFields.count a))
      · exact ih _ hxs
  exact haux objs 0 ho

theorem applyArgs_get?_live_back {ctx : RcCtx} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hc : CleanVars ctx) {as : List LcArg} {bs : List Bool} {ctx' : RcCtx}
    (ha : ctx.applyArgs as bs = .ok ctx') (z : Nat) {w' : RcVar}
    (hg' : ctx'.get? z = some w') (hlive : w'.isLive = true) :
    ∃ w, ctx.get? z = some w ∧ w.isLive = true ∧ w.noRc = w'.noRc ∧
      w.persistent = w'.persistent ∧ w.ty = w'.ty ∧ w'.owned ≤ w.owned ∧
      (w'.borrowed = true → w.borrowed = true ∧ w.parent? = w'.parent?) ∧
      (w'.excl = true → w.excl = true) := by
  induction as generalizing ctx bs with
  | nil =>
    cases bs with
    | nil =>
      simp only [RcCtx.applyArgs, pure, Except.pure, Except.ok.injEq] at ha; subst ha
      exact ⟨w', hg', hlive, rfl, rfl, rfl, Nat.le_refl _, fun h => ⟨h, rfl⟩, fun h => h⟩
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
        | ok _ => simp only [hchk] at ha; exact ih hnd hc ha
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
        cases hcarg : ctx.consumeArg a with
        | error _ => simp [hcarg] at ha
        | ok ctx1 =>
          simp only [hcarg] at ha
          cases a with
          | erased =>
            simp [RcCtx.consumeArg, pure, Except.pure] at hcarg; subst hcarg; exact ih hnd hc ha
          | var id =>
            have hnd1 := consumeVar_nodup hnd hcarg
            have hc1 := cleanVars_consumeVar hnd hc hcarg
            obtain ⟨w1, hg1, hl1, hno1, hps1, hty1, hown1, hbr1, hex1⟩ := ih hnd1 hc1 ha
            obtain ⟨w0, hg0, hl0, hno0, hps0, hty0, hown0, hbr0, hex0⟩ :=
              consumeVar_get?_live_back hnd hc hcarg z hg1 hl1
            refine ⟨w0, hg0, hl0, hno0.trans hno1, hps0.trans hps1, hty0.trans hty1,
              Nat.le_trans hown1 hown0, fun h => ?_, fun h => (hex0 (hex1 h)).1⟩
            have ⟨h1a, h1b⟩ := hbr1 h
            have ⟨h0a, h0b⟩ := hbr0 h1a
            exact ⟨h0a, h0b.trans h1b⟩

private theorem applyArgs_excl_not_passed_var_aux {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx)
    {as : List LcArg} {bs : List Bool} {ctx' : RcCtx}
    (ha : rf.ctx.applyArgs as bs = .ok ctx')
    (hsh : argsNoSharedTarget rf.ctx as bs = true) (hpo : ParentsOwned rf.ctx)
    {u' : RcVar} (hu' : u' ∈ ctx'.vars) (hu'_live : u'.isLive = true)
    (hu'_excl : u'.excl = true)
    (hno_u : ∀ a br, (a, br) ∈ as.zip bs → br = true → a ≠ .var u'.id) :
    ∀ a ∈ as, a ≠ .var u'.id := by
  induction as generalizing rf bs with
  | nil => cases bs <;> simp [RcCtx.applyArgs] at ha ⊢
  | cons a as ih =>
    cases bs with
    | nil => simp [RcCtx.applyArgs] at ha
    | cons b bs =>
      have hnd' := applyArgs_nodup hinv.2.1 ha
      have hgu' := (RcCtx.mem_get?_iff hnd').mpr hu'
      simp only [RcCtx.applyArgs, bind, Except.bind] at ha
      have hsh1 := hsh
      simp only [argsNoSharedTarget, List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hsh1
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte] at ha
        cases hchk : rf.ctx.checkArgLive a with
        | error _ => simp [hchk] at ha
        | ok _ =>
          simp only [hchk] at ha
          have htail := ih hinv hclean ha hsh1.2 hpo
            (fun x br hx hbr => hno_u x br (List.mem_cons_of_mem _ hx) hbr)
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hxs
          · exact hno_u x b List.mem_cons_self hb
          · exact htail x hxs
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
        cases hcarg : rf.ctx.consumeArg a with
        | error _ => simp [hcarg] at ha
        | ok ctx1 =>
          simp only [hcarg] at ha
          cases a with
          | erased =>
            simp only [RcCtx.consumeArg, pure, Except.pure] at hcarg; cases hcarg
            have htail := ih hinv hclean ha hsh1.2 hpo
              (fun x br hx hbr => hno_u x br (List.mem_cons_of_mem _ hx) hbr)
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hxs
            · exact fun h => by cases h
            · exact htail x hxs
          | var id =>
            have hsh_tgt : ∀ p ∈ rf.ctx.sharedPreds, p.2 = id →
                ∀ v, rf.ctx.get? id = some v →
                  v.noRc = true ∨ v.persistent = true ∨ (1 : Nat) = 0 ∨ v.owned ≤ 1 := by
              intro p hp hpeq
              have hall := hsh1.1
              simp only [hb, Bool.false_eq_true, ↓reduceIte, List.all_eq_true, bne_iff_ne] at hall
              exact absurd hpeq (hall p hp)
            obtain ⟨_, _, hi1, hc1, hp1, _⟩ := rcInv_consumeVar_step hinv hclean hpo hcarg hsh_tgt
            have hsh_next : argsNoSharedTarget ctx1 as bs = true := by
              have h2 := hsh1.2
              simp only [argsNoSharedTarget, List.all_eq_true] at h2 ⊢
              intro p hp
              rcases p with ⟨pa, pb⟩
              have this := h2 (pa, pb) hp
              dsimp only at this ⊢
              cases pa with
              | erased => exact this
              | var y =>
                by_cases hbr : pb = true
                · simp [hbr]
                · simp only [hbr, Bool.false_eq_true, ↓reduceIte, List.all_eq_true] at this ⊢
                  exact fun q hq => this q (consumeVar_sharedPreds_sub hcarg q hq)
            have htail := ih hi1 hc1 ha hsh_next hp1
              (fun x br hx hbr => hno_u x br (List.mem_cons_of_mem _ hx) hbr)
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hxs
            · intro hveq
              cases hveq
              obtain ⟨w1, hg1, hl1, _, _, _, _, _, hex1⟩ :=
                applyArgs_get?_live_back hi1.2.1 hc1 ha u'.id hgu' hu'_live
              have hw1e := hex1 hu'_excl
              obtain ⟨w0, hg0, hl0, _, _, _, _, _, hex0⟩ :=
                consumeVar_get?_live_back hinv.2.1 hclean hcarg u'.id hg1 hl1
              obtain ⟨hw0e, hw0r⟩ := hex0 hw1e
              have hw0_n1 : w1.owned + 1 = w0.owned := by
                rcases hw0r rfl with h0 | h1
                · cases h0
                · exact h1
              have hns1 : ¬w1.ty.isScalar := fun hs => by
                have hc_w1 := (hc1 w1 (RcCtx.get?_mem hg1).1).1.2 hs
                have : w1.noRc = false := by
                  cases hn : w1.noRc
                  · rfl
                  · have := ((hc1 w1 (RcCtx.get?_mem hg1).1).1.1 hn).2.2.2.2
                    rw [hw1e] at this; cases this
                rw [hc_w1] at this; cases this
              obtain ⟨_, _, _, _, _, hnon1⟩ := hi1.2.2.2.1 w1 (RcCtx.get?_mem hg1).1 hl1
              obtain ⟨_, _, _, _, hex_w1, _⟩ := hnon1 hns1
              have hown1 : w1.owned = 1 := (hex_w1 hw1e).2.2.1
              have hns0 : ¬w0.ty.isScalar := fun hs => by
                have hc_w0 := (hclean w0 (RcCtx.get?_mem hg0).1).1.2 hs
                have : w0.noRc = false := by
                  cases hn : w0.noRc
                  · rfl
                  · have := ((hclean w0 (RcCtx.get?_mem hg0).1).1.1 hn).2.2.2.2
                    rw [hw0e] at this; cases this
                rw [hc_w0] at this; cases this
              obtain ⟨_, _, _, _, _, hnon0⟩ := hinv.2.2.2.1 w0 (RcCtx.get?_mem hg0).1 hl0
              obtain ⟨_, _, _, _, hex_w0, _⟩ := hnon0 hns0
              have hown0 : w0.owned = 1 := (hex_w0 hw0e).2.2.1
              omega
            · exact htail x hxs

theorem applyArgs_excl_not_passed_var {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx)
    {as : List LcArg} {bs : List Bool} {ctx' : RcCtx}
    (ha : rf.ctx.applyArgs as bs = .ok ctx')
    (hsh : argsNoSharedTarget rf.ctx as bs = true) (hpo : ParentsOwned rf.ctx)
    (hnoexcl : argsNoExclBorrow rf.ctx as bs = true)
    {u' : RcVar} (hu' : u' ∈ ctx'.vars) (hu'_live : u'.isLive = true)
    (hu'_excl : u'.excl = true) :
    ∀ a ∈ as, a ≠ .var u'.id := by
  have hnd' := applyArgs_nodup hinv.2.1 ha
  have hgu' := (RcCtx.mem_get?_iff hnd').mpr hu'
  obtain ⟨u0, hgu0, _, _, _, _, _, _, hex0⟩ :=
    applyArgs_get?_live_back hinv.2.1 hclean ha u'.id hgu' hu'_live
  have hu0e := hex0 hu'_excl
  apply applyArgs_excl_not_passed_var_aux hinv hclean ha hsh hpo hu' hu'_live hu'_excl
  intro a br hab hbr heq
  subst heq
  simp only [argsNoExclBorrow, List.all_eq_true] at hnoexcl
  have hcheck := hnoexcl (.var u'.id, br) hab
  simp [hbr, hgu0, hu0e] at hcheck

theorem applyArgs_eval_excl_disjoint {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    {as : List LcArg} {bs : List Bool} {ctx' : RcCtx}
    (ha : rf.ctx.applyArgs as bs = .ok ctx')
    (hsh : argsNoSharedTarget rf.ctx as bs = true)
    (hnoexcl : argsNoExclBorrow rf.ctx as bs = true)
    (hlive : ∀ a ∈ as, a = .erased ∨ ∃ z v, a = .var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true)
    {u' : RcVar} (hu' : u' ∈ ctx'.vars) (hu'_live : u'.isLive = true) (hu'_excl : u'.excl = true)
    (hguard : ∀ a ∈ as, match a with
      | .erased => True
      | .var z => match rf.ctx.get? z with
        | some vz => vz.parent? ≠ some u'.id ∧ ¬(vz.ty.isScalar = true ∧ vz.ty.width = 64)
        | none => True)
    {ws : List Word} (hws : rf.envH.evalArgsOwn as = some ws)
    {bv_u : BitVec 64} (heu : rf.envH u'.id = some (u'.ty, Word.i64 bv_u))
    {o_u : LcnfObj} (hou : o_u ∈ σ.objs) (hwfu : o_u.Wf) (hoau : o_u.addr = bv_u)
    (hrcu : o_u.rc = 1#32) :
    ∀ w ∈ ws, w.toBV64? ≠ some bv_u := by
  have hnd' := applyArgs_nodup hinv.2.1 ha
  have hgu' := (RcCtx.mem_get?_iff hnd').mpr hu'
  obtain ⟨u0, hgu0, hu0l, _, _, hty0, _, _, hex0⟩ :=
    applyArgs_get?_live_back hinv.2.1 hclean ha u'.id hgu' hu'_live
  have hu0e := hex0 hu'_excl
  have hu0id : u0.id = u'.id := (RcCtx.get?_mem hgu0).2
  have hcv_u0 := hclean u0 (RcCtx.get?_mem hgu0).1
  have hu0_ns : ¬u0.ty.isScalar := fun hs => by
    have := hcv_u0.1.2 hs
    have hno0 : u0.noRc = false := by
      cases hn : u0.noRc
      · rfl
      · have := (hcv_u0.1.1 hn).2.2.2.2; rw [hu0e] at this; cases this
    rw [this] at hno0; cases hno0
  obtain ⟨_, _, _, _, _, hnon0⟩ := hinv.2.2.2.1 u0 (RcCtx.get?_mem hgu0).1 hu0l
  obtain ⟨_, _, _, _, hex_u0, _⟩ := hnon0 hu0_ns
  have hu0_no : u0.noRc = false := (hex_u0 hu0e).1
  have hu0_ps : u0.persistent = false := (hex_u0 hu0e).2.1
  have hu0_own : u0.owned = 1 := (hex_u0 hu0e).2.2.1
  have hu0_ev : rf.envH u0.id = some (u0.ty, Word.i64 bv_u) := by
    rw [hu0id, hty0]; exact heu
  obtain ⟨hnp0, hcnt0, _⟩ := handlesRcSound_excl_unique hinv.2.1 hinv.2.2.1
    (RcCtx.get?_mem hgu0).1 hu0_no hu0_ps hcv_u0.2.2.2.2 hu0_own hu0_ev hou hwfu hoau hrcu
  have hnot_var :=
    applyArgs_excl_not_passed_var hinv hclean ha hsh hpo hnoexcl hu' hu'_live hu'_excl
  have hnot_backed : ∀ (roots : List (BitVec 64)),
      roots.count bv_u = 0 → ¬Backed σ.objs roots bv_u := by
    intro roots hrcnt hb
    rcases hb with ⟨o2, ho2, ha2, hrc2⟩ | ⟨r, hr, hreach⟩
    · have := obj_eq_of_addr_nodup hinv.1.2 ho2 hou (ha2.trans hoau.symm)
      subst this; rw [hrcu] at hrc2; cases hrc2
    · cases hreach with
      | refl _ => exact absurd (List.count_pos_iff.mpr hr) (by omega)
      | @step u _ hprev hmem _ _ =>
        rcases hmem with ⟨op, hop, hopa, hcf⟩
        obtain ⟨o0, ho0, hoa0, hnz0⟩ := nonPersistReach_target_nonzero hprev
        have heqo := obj_eq_of_addr_nodup hinv.1.2 ho0 hop (hoa0.trans hopa.symm)
        subst heqo
        have hpos_ref : 0 < nonPersistRefs σ.objs bv_u :=
          nonPersistRefs_pos_of_mem σ.objs ho0 hnz0 hcf
        omega
  have haux : ∀ (as1 : List LcArg) (ws1 : List Word),
      (∀ a ∈ as1, a ∈ as) →
      rf.envH.evalArgsOwn as1 = some ws1 →
      ∀ w ∈ ws1, w.toBV64? ≠ some bv_u := by
    intro as1
    induction as1 with
    | nil =>
      intro ws1 _ h1 w hw; simp [HValEnv.evalArgsOwn] at h1; subst h1; cases hw
    | cons a as1 ih =>
      intro ws1 hsub h1 w hw
      simp only [HValEnv.evalArgsOwn] at h1
      cases ha1 : rf.envH.evalArgOwn a with
      | none => simp [ha1] at h1
      | some wa =>
        cases has1 : rf.envH.evalArgsOwn as1 with
        | none => simp [ha1, has1] at h1
        | some ws1' =>
          simp only [ha1, has1] at h1; cases h1
          rcases List.mem_cons.mp hw with rfl | hwt
          · have ham := hsub a List.mem_cons_self
            rcases hlive a ham with rfl | ⟨z, vz, rfl, hgz, hzl⟩
            · simp [HValEnv.evalArgOwn] at ha1; subst ha1
              intro heq; simp [Word.toBV64?, Word.i64] at heq
              have := obj_addr_and1_zero hwfu; rw [hoau, ← heq] at this; cases this
            · have hz_ne : z ≠ u'.id := fun h => hnot_var (.var z) ham (by rw [h])
              have hgd := hguard (.var z) ham; dsimp only at hgd; rw [hgz] at hgd; dsimp only at hgd
              have hzm := (RcCtx.get?_mem hgz).1
              have hzid := (RcCtx.get?_mem hgz).2
              obtain ⟨_, wz, _, hwz, hrepz, hnonz⟩ := hinv.2.2.2.1 vz hzm hzl
              rw [hzid] at hwz
              have hwa_eq : w = wz := by
                simp only [HValEnv.evalArgOwn, hwz] at ha1; cases ha1; rfl
              rw [hwa_eq]
              by_cases hzsc : vz.ty.isScalar = true
              · have hne64 : vz.ty.width ≠ 64 := fun h => hgd.2 ⟨hzsc, h⟩
                unfold ValRep at hrepz; simp only [hzsc, ↓reduceIte] at hrepz
                rcases hrepz with ⟨bv, _, rfl⟩ | ⟨c, _, _, rfl⟩ | ⟨_, rfl⟩ <;>
                  intro hbv <;> simp [Word.toBV64?, hne64] at hbv
              · have hz_ns : ¬vz.ty.isScalar := fun h => hzsc h
                obtain ⟨bv_z, rfl, hno_z, hps_z, _, hbr_z⟩ := hnonz hz_ns
                intro hbv
                have hbeq : bv_z = bv_u := by simpa [Word.toBV64?, Word.i64] using hbv
                subst hbeq
                have hcv_z := hclean vz hzm
                by_cases hzn : vz.noRc = true
                · exact hno_z hzn (hoau ▸ obj_addr_and1_zero hwfu)
                · have hzn0 : vz.noRc = false := by cases h : vz.noRc <;> simp_all
                  by_cases hzp : vz.persistent = true
                  · obtain ⟨o2, ho2, ha2, hrc2⟩ := hps_z hzp (hoau ▸ obj_addr_and1_zero hwfu)
                    have := obj_eq_of_addr_nodup hinv.1.2 ho2 hou (ha2.trans hoau.symm)
                    subst this; rw [hrcu] at hrc2; cases hrc2
                  · have hzp0 : vz.persistent = false := by cases h : vz.persistent <;> simp_all
                    by_cases hzb : vz.borrowed = true
                    · obtain ⟨_, hpback⟩ := hbr_z hzn0 hzp0 hzb (hoau ▸ obj_addr_and1_zero hwfu)
                      cases hpv : vz.parent? with
                      | none =>
                        rw [hpv] at hpback
                        have hcnt_eg : (rf.extH ++ rf.ghostH).count bv_z = 0 := by
                          simp only [List.count_append] at hcnt0 ⊢; omega
                        exact hnot_backed _ hcnt_eg hpback
                      | some p =>
                        rw [hpv] at hpback
                        obtain ⟨pv, hpvm, hpvid, hp1, hp2, hp3, _⟩ := hpo vz hzm p hpv
                        obtain ⟨_, _, _, _, _, _, hbp_ev⟩ := hpback
                        have hp_ne : p ≠ u0.id := fun h =>
                          hgd.1 (hpv.trans (congrArg some (h.trans hu0id)))
                        have hbp_cnt : (match rf.envH p with
                            | some (_, w) => match w.toBV64? with | some bp => [bp] | none => []
                            | none => []).count bv_z = 0 := by
                          cases hrep : rf.envH p with
                          | none => simp
                          | some q =>
                            rcases q with ⟨tq, wq⟩
                            cases hwb : wq.toBV64? with
                            | none => simp [hwb]
                            | some bp =>
                              by_cases hbe : bp = bv_z
                              · subst hbe
                                have hcv_pv := hclean pv hpvm
                                have hown_pv : 0 < pv.owned := hp3
                                have hmem_pv : bp ∈ localHandlesExcept rf.ctx rf.envH u0.id := by
                                  unfold localHandlesExcept
                                  refine List.mem_flatten.mpr ⟨varHandles rf.envH pv,
                                    List.mem_map.mpr ⟨pv, List.mem_filter.mpr ⟨hpvm, ?_⟩, rfl⟩, ?_⟩
                                  · exact bne_iff_ne.mpr (by rw [hpvid]; exact hp_ne)
                                  · unfold varHandles
                                    rw [hp1, hp2, hcv_pv.2.2.2.2,
                                      beq_false_of_ne (Nat.ne_of_gt hown_pv), hpvid, hrep]
                                    dsimp only; rw [hwb]; dsimp only
                                    simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                                      beq_iff_eq.mpr (hoau ▸ obj_addr_and1_zero hwfu),
                                      List.mem_replicate, ne_eq]
                                    exact ⟨Nat.ne_of_gt hown_pv, trivial⟩
                                have hpos_c : 0 < (localHandlesExcept rf.ctx rf.envH u0.id ++
                                    rf.extH ++ rf.ghostH).count bp :=
                                  List.count_pos_iff.mpr (List.mem_append.mpr
                                    (Or.inl (List.mem_append.mpr (Or.inl hmem_pv))))
                                omega
                              · dsimp only; rw [hwb]; simp [hbe]
                        have hcnt_all : ((match rf.envH p with
                            | some (_, w) => match w.toBV64? with | some bp => [bp] | none => []
                            | none => []) ++ (rf.extH ++ rf.ghostH)).count bv_z = 0 := by
                          simp only [List.count_append] at hcnt0 hbp_cnt ⊢; omega
                        exact hnot_backed _ hcnt_all hbp_ev
                    · have hzb0 : vz.borrowed = false := by cases h : vz.borrowed <;> simp_all
                      have hzown : 0 < vz.owned := by
                        have := hzl; simp [RcVar.isLive, hzn0, hzp0, hzb0, hcv_z.2.2.2.2] at this
                        exact this
                      have hmem_ex : bv_z ∈ localHandlesExcept rf.ctx rf.envH u0.id := by
                        unfold localHandlesExcept
                        refine List.mem_flatten.mpr ⟨varHandles rf.envH vz,
                          List.mem_map.mpr ⟨vz, List.mem_filter.mpr ⟨hzm, ?_⟩, rfl⟩, ?_⟩
                        · exact bne_iff_ne.mpr (by rw [hzid, hu0id]; exact hz_ne)
                        · unfold varHandles
                          rw [hzn0, hzp0, hcv_z.2.2.2.2, beq_false_of_ne (Nat.ne_of_gt hzown),
                            hzid, hwz]
                          simp only [Word.toBV64?, Word.i64,
                            beq_iff_eq.mpr (hoau ▸ obj_addr_and1_zero hwfu), ↓reduceIte]
                          exact List.mem_replicate.mpr ⟨Nat.ne_of_gt hzown, rfl⟩
                      have hcnt_pos : 0 < (localHandlesExcept rf.ctx rf.envH u0.id ++
                          rf.extH ++ rf.ghostH).count bv_z :=
                        List.count_pos_iff.mpr
                          (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hmem_ex))))
                      omega
          · exact ih ws1' (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) has1 w hwt
  exact haux as ws (fun _ h => h) hws

end
