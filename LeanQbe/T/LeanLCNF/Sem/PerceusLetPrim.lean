module

public import LeanQbe.T.LeanLCNF.Sem.PerceusLet3

/-!
# Perceus Primitive `fap` Step Simulation (`PerceusLetPrim`)

Simulates primitive `.fap` bindings (`outOfBounds._redArg`, `Array.get!InternalBorrowed`,
`propagateMark`, and all read-only / allocating primitives in `perceusPrimWf`) between
`PRValWp` and `HVal.wp`.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

public section

private theorem mem_applyArgsHandles_of_getLast {rf : RcFrame} {as : List LcArg}
    {borrows : List Bool} {y : Nat} {bv : BitVec 64}
    (hlen : as.length = borrows.length)
    (hlast_a : as.getLast? = some (.var y)) (hlast_b : borrows.getLast? = some false)
    (hcv : bv ∈ consumeVarHandles rf y 1) :
    bv ∈ applyArgsHandles rf as borrows := by
  induction as generalizing borrows with
  | nil => simp at hlast_a
  | cons a rest ih =>
    cases borrows with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : rest.length = bs.length := by simpa using hlen
      cases rest with
      | nil =>
        cases bs with
        | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast_a hlast_b
          subst hlast_a; subst hlast_b
          have hstep : applyArgsHandles rf [.var y] [false] =
              consumeVarHandles rf y 1 ++ applyArgsHandles rf [] [] := rfl
          rw [hstep]
          exact List.mem_append_left _ hcv
        | cons _ _ => simp at hlen'
      | cons a2 rest2 =>
        cases bs with
        | nil => simp at hlen'
        | cons b2 bs2 =>
          have ha2 : (a2 :: rest2).getLast? = some (.var y) := by
            simpa [List.getLast?_cons_cons] using hlast_a
          have hb2 : (b2 :: bs2).getLast? = some false := by
            simpa [List.getLast?_cons_cons] using hlast_b
          have hih := ih hlen' ha2 hb2
          have hstep : applyArgsHandles rf (a :: a2 :: rest2) (b :: b2 :: bs2) =
              if b = true then applyArgsHandles rf (a2 :: rest2) (b2 :: bs2)
              else (match a with
                | .erased => [] | .var id => consumeVarHandles rf id 1) ++
                  applyArgsHandles rf (a2 :: rest2) (b2 :: bs2) := by
            cases a <;> rfl
          rw [hstep]
          split
          · exact hih
          · exact List.mem_append_right _ hih

private theorem evalArgsOwn_getLast? {envH : HValEnv} {as : List LcArg} {ws : List Word}
    {a : LcArg} {rw : Word}
    (hev : envH.evalArgsOwn as = some ws)
    (hlast_a : as.getLast? = some a) (hlast_w : ws.getLast? = some rw) :
    envH.evalArgOwn a = some rw := by
  induction as generalizing ws with
  | nil => simp at hlast_a
  | cons hd tl ih =>
    have hstep : envH.evalArgsOwn (hd :: tl) =
        match envH.evalArgOwn hd, envH.evalArgsOwn tl with
        | some v, some vs => some (v :: vs) | _, _ => none := rfl
    rw [hstep] at hev
    cases hhd : envH.evalArgOwn hd with
    | none => simp [hhd] at hev
    | some w0 =>
      cases htl : envH.evalArgsOwn tl with
      | none => simp [hhd, htl] at hev
      | some wt0 =>
        simp only [hhd, htl, Option.some.injEq] at hev
        subst hev
        cases tl with
        | nil =>
          have hnil : envH.evalArgsOwn [] = some [] := rfl
          rw [hnil] at htl; cases htl
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast_a hlast_w
          subst hlast_a; subst hlast_w; exact hhd
        | cons hd2 tl2 =>
          cases wt0 with
          | nil =>
            have hstep2 : envH.evalArgsOwn (hd2 :: tl2) =
                match envH.evalArgOwn hd2, envH.evalArgsOwn tl2 with
                | some v, some vs => some (v :: vs) | _, _ => none := rfl
            rw [hstep2] at htl
            cases h1 : envH.evalArgOwn hd2 <;> cases h2 : envH.evalArgsOwn tl2 <;>
              simp [h1, h2] at htl
          | cons wh2 wt2 =>
            exact ih htl
              (by simpa [List.getLast?_cons_cons] using hlast_a)
              (by simpa [List.getLast?_cons_cons] using hlast_w)

private theorem mem_zip_of_getLast? {α β : Type} {xs : List α} {ys : List β}
    {a : α} {b : β} (hlen : xs.length = ys.length)
    (ha : xs.getLast? = some a) (hb : ys.getLast? = some b) :
    (a, b) ∈ xs.zip ys := by
  induction xs generalizing ys with
  | nil => simp at ha
  | cons x rest ih =>
    cases ys with
    | nil => simp at hlen
    | cons y bs =>
      have hlen' : rest.length = bs.length := by simpa using hlen
      cases rest with
      | nil =>
        cases bs with
        | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at ha hb
          subst ha; subst hb; exact .head _
        | cons _ _ => simp at hlen'
      | cons x2 rest2 =>
        cases bs with
        | nil => simp at hlen'
        | cons y2 bs2 =>
          have ha2 : (x2 :: rest2).getLast? = some a := by
            simpa [List.getLast?_cons_cons] using ha
          have hb2 : (y2 :: bs2).getLast? = some b := by
            simpa [List.getLast?_cons_cons] using hb
          exact .tail _ (ih hlen' ha2 hb2)

private theorem count_cons_le_add {α : Type} [DecidableEq α] (x : α) (l m : List α)
    (hx : x ∈ m) :
    ∀ a, List.count a (x :: l) ≤ List.count a (l ++ m) := by
  intro a
  rw [List.count_cons, List.count_append]
  by_cases heq : a = x
  · subst heq
    have hc : 1 ≤ List.count a m := Nat.succ_le_of_lt (List.count_pos_iff.mpr hx)
    simp; omega
  · simp [Ne.symm heq]

private theorem invalidateChildren_get?_none {ctx : RcCtx} {z y : Nat}
    (hnone : ctx.get? y = none) :
    (ctx.invalidateChildren z).get? y = none := by
  have hdef : (ctx.invalidateChildren z).get? y =
      (ctx.vars.map fun v =>
        if (v.parent? == some z) = true then
          { v with borrowed := false, parent? := none }
        else v).find? (·.id == y) := rfl
  rw [hdef]
  unfold RcCtx.get? at hnone
  generalize hvs : ctx.vars = vs at hnone ⊢
  clear hvs
  induction vs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.find?_cons] at hnone
    by_cases hdy : hd.id = y
    · simp [hdy] at hnone
    · have hbf : (hd.id == y) = false := beq_false_of_ne hdy
      rw [hbf] at hnone
      simp only [List.map_cons, List.find?_cons]
      by_cases hp : (hd.parent? == some z) = true
      · simp only [hp, ↓reduceIte, hbf]
        exact ih hnone
      · have hpf : (hd.parent? == some z) = false := Bool.eq_false_iff.mpr hp
        simp only [hpf, ↓reduceIte, Bool.false_eq_true, hbf]
        exact ih hnone

private theorem consumeVar_none_of_none {ctx ctx1 : RcCtx} {z n y : Nat}
    (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hcv : ctx.consumeVar z n = .ok ctx1) (hnone : ctx.get? y = none) :
    ctx1.get? y = none := by
  unfold RcCtx.consumeVar at hcv
  cases hgz : ctx.get? z with
  | none => simp [hgz] at hcv
  | some vz =>
    simp only [hgz] at hcv
    have hyz : y ≠ z := fun heq => by subst heq; simp [hnone] at hgz
    have hnez : vz.id = z := (RcCtx.get?_mem hgz).2
    split at hcv
    · cases hcv; exact hnone
    · split at hcv
      · cases hcv; exact hnone
      · split at hcv
        · simp at hcv
        · let vz' : RcVar :=
            ⟨vz.id, vz.ty, vz.noRc, vz.persistent, vz.owned - n, vz.borrowed, vz.parent?,
              if (vz.owned - n == 0) = true then false else vz.excl,
              if (vz.owned - n == 0) = true then false else vz.resetTok⟩
          have hyzv : y ≠ vz'.id := by dsimp [vz']; rw [hnez]; exact hyz
          split at hcv
          · have hput : (ctx.put vz').get? y = none := by
              rw [get?_put_ne ctx hnd hyzv]; exact hnone
            have hc : ctx1 = (ctx.put vz').invalidateChildren z := by cases hcv; rfl
            rw [hc]; exact invalidateChildren_get?_none hput
          · have hc : ctx1 = ctx.put vz' := by cases hcv; rfl
            rw [hc, get?_put_ne ctx hnd hyzv]; exact hnone

private theorem consumeVar_preserves_flags_self {ctx ctx1 : RcCtx} {z n y : Nat} {vy : RcVar}
    (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hcv : ctx.consumeVar z n = .ok ctx1) (hget : ctx.get? y = some vy) :
    ∃ vy1, ctx1.get? y = some vy1 ∧ vy1.noRc = vy.noRc ∧ vy1.persistent = vy.persistent ∧
      vy1.owned ≤ vy.owned := by
  unfold RcCtx.consumeVar at hcv
  cases hgz : ctx.get? z with
  | none => simp [hgz] at hcv
  | some vz =>
    simp only [hgz] at hcv
    split at hcv
    · cases hcv; exact ⟨vy, hget, rfl, rfl, Nat.le_refl _⟩
    · split at hcv
      · cases hcv; exact ⟨vy, hget, rfl, rfl, Nat.le_refl _⟩
      · split at hcv
        · simp at hcv
        · have hne_z : vz.id = z := (RcCtx.get?_mem hgz).2
          have hget_put : ∀ {u : RcVar}, u.id = z →
              (ctx.put u).get? y = if y = z then some u else some vy := by
            intro u hu
            by_cases hyz : y = z
            · simp [hyz, ← hu, get?_put_self ctx hnd u]
            · rw [get?_put_ne ctx hnd (by simpa [hu] using hyz)]; simp [hyz, hget]
          have hinv : ∀ {c : RcCtx} {vy0 : RcVar}, c.get? y = some vy0 →
              ∃ vy', (c.invalidateChildren z).get? y = some vy' ∧ vy'.noRc = vy0.noRc ∧
                vy'.persistent = vy0.persistent ∧ vy'.owned = vy0.owned := by
            intro c vy0 hgc
            have hdef : (c.invalidateChildren z).get? y =
                (c.vars.map fun v =>
                  if (v.parent? == some z) = true then
                    { v with borrowed := false, parent? := none }
                  else v).find? (·.id == y) := rfl
            rw [hdef]
            unfold RcCtx.get? at hgc
            generalize hvs : c.vars = vs at hgc ⊢
            clear hvs
            induction vs with
            | nil => cases hgc
            | cons hd tl ih =>
              simp only [List.find?_cons] at hgc
              by_cases hdy : hd.id = y
              · have hb : (hd.id == y) = true := by simp [hdy]
                rw [hb] at hgc; cases hgc
                simp only [List.map_cons, List.find?_cons]
                by_cases hp : (vy0.parent? == some z) = true
                · simp only [hp, ↓reduceIte, hb]
                  exact ⟨_, rfl, rfl, rfl, rfl⟩
                · have hpf : (vy0.parent? == some z) = false := Bool.eq_false_iff.mpr hp
                  simp only [hpf, Bool.false_eq_true, ↓reduceIte, hb]
                  exact ⟨_, rfl, rfl, rfl, rfl⟩
              · have hbf : (hd.id == y) = false := beq_false_of_ne hdy
                rw [hbf] at hgc
                rcases ih hgc with ⟨vy', htl, hfl⟩
                simp only [List.map_cons, List.find?_cons] at htl ⊢
                by_cases hp : (hd.parent? == some z) = true
                · simp only [hp, ↓reduceIte, hbf]
                  exact ⟨vy', htl, hfl⟩
                · have hpf : (hd.parent? == some z) = false := Bool.eq_false_iff.mpr hp
                  simp only [hpf, ↓reduceIte, Bool.false_eq_true, hbf]
                  exact ⟨vy', htl, hfl⟩
          let vz' : RcVar :=
            ⟨vz.id, vz.ty, vz.noRc, vz.persistent, vz.owned - n, vz.borrowed, vz.parent?,
              if (vz.owned - n == 0) = true then false else vz.excl,
              if (vz.owned - n == 0) = true then false else vz.resetTok⟩
          split at hcv
          · have hgp := hget_put (u := vz') hne_z
            have hcv' : (ctx.put vz').invalidateChildren z = ctx1 := by cases hcv; rfl
            rw [← hcv']
            by_cases hyz : y = z
            · subst hyz
              rw [hgz] at hget; cases hget
              simp only [↓reduceIte] at hgp
              rcases hinv hgp with ⟨vy', h1, h2, h3, h4⟩
              exact ⟨vy', h1, h2, h3, by rw [h4]; exact Nat.sub_le _ _⟩
            · have hgp' : (ctx.put vz').get? y = some vy := by simpa [hyz] using hgp
              rcases hinv hgp' with ⟨vy', h1, h2, h3, h4⟩
              exact ⟨vy', h1, h2, h3, by rw [h4]; exact Nat.le_refl _⟩
          · have hctx1 : ctx1 = ctx.put vz' := by cases hcv; rfl
            rw [hctx1]
            by_cases hyz : y = z
            · subst hyz
              rw [hgz] at hget; cases hget
              have hgp := get?_put_self ctx hnd vz'
              rw [hne_z] at hgp
              rw [hgp]
              exact ⟨vz', rfl, rfl, rfl, Nat.sub_le _ _⟩
            · have hyzv : y ≠ vz'.id := by dsimp [vz']; rw [hne_z]; exact hyz
              rw [get?_put_ne ctx hnd hyzv]
              exact ⟨vy, hget, rfl, rfl, Nat.le_refl _⟩

private theorem applyArgs_preserves_flags {ctx ctx1 : RcCtx} {as : List LcArg} {bs : List Bool}
    (hnd : (ctx.vars.map RcVar.id).Nodup)
    (happ : ctx.applyArgs as bs = .ok ctx1) {z : Nat} {vz1 : RcVar}
    (hget1 : ctx1.get? z = some vz1) :
    ∃ vz0, ctx.get? z = some vz0 ∧ vz1.noRc = vz0.noRc ∧
      vz1.persistent = vz0.persistent ∧ vz1.owned ≤ vz0.owned := by
  induction as generalizing ctx bs with
  | nil =>
    cases bs with
    | nil =>
      have hce : ctx = ctx1 := by cases happ; rfl
      subst hce; exact ⟨vz1, hget1, rfl, rfl, Nat.le_refl _⟩
    | cons _ _ => simp [RcCtx.applyArgs] at happ
  | cons a rest ih =>
    cases bs with
    | nil => simp [RcCtx.applyArgs] at happ
    | cons b bs' =>
      by_cases hb : b = true
      · subst hb
        change (do let _ ← ctx.checkArgLive a; ctx.applyArgs rest bs') = .ok ctx1 at happ
        cases hchk : ctx.checkArgLive a with
        | error e =>
          rw [hchk] at happ
          change Except.error e = .ok ctx1 at happ
          cases happ
        | ok _ =>
          rw [hchk] at happ
          change ctx.applyArgs rest bs' = .ok ctx1 at happ
          exact ih hnd happ
      · have hbf : b = false := Bool.eq_false_iff.mpr hb
        subst hbf
        change (do let cm ← ctx.consumeArg a; cm.applyArgs rest bs') = .ok ctx1 at happ
        cases a with
        | erased =>
          change ctx.applyArgs rest bs' = .ok ctx1 at happ
          exact ih hnd happ
        | var w =>
          cases hca : ctx.consumeVar w 1 with
          | error e =>
            have hce : ctx.consumeArg (.var w) = .error e := by
              simp [RcCtx.consumeArg, hca]
            rw [hce] at happ
            change Except.error e = .ok ctx1 at happ
            cases happ
          | ok cm =>
            have hca' : ctx.consumeArg (.var w) = .ok cm := by
              simp [RcCtx.consumeArg, hca]
            rw [hca'] at happ
            change cm.applyArgs rest bs' = .ok ctx1 at happ
            have hndm := consumeVar_nodup hnd hca
            obtain ⟨vzm, hgetm, hnrm, hprm, hlem⟩ := ih hndm happ
            cases hgz0 : ctx.get? z with
            | none =>
              exfalso
              rw [consumeVar_none_of_none hnd hca hgz0] at hgetm
              cases hgetm
            | some vz0 =>
              obtain ⟨vzm', hgetm', hnr', hpr', hle'⟩ :=
                consumeVar_preserves_flags_self hnd hca hgz0
              rw [hgetm] at hgetm'; cases hgetm'
              exact ⟨vz0, rfl, hnrm.trans hnr', hprm.trans hpr', Nat.le_trans hlem hle'⟩

private theorem applyArgs_consumeVar_owned_pos {ctx ctx1 : RcCtx} {as : List LcArg}
    {borrows : List Bool} {y : Nat} {vy : RcVar}
    (hnd : (ctx.vars.map RcVar.id).Nodup)
    (happ : ctx.applyArgs as borrows = .ok ctx1)
    (hlen : as.length = borrows.length)
    (hlast_a : as.getLast? = some (.var y)) (hlast_b : borrows.getLast? = some false)
    (hgety : ctx.get? y = some vy) (hnr : vy.noRc = false) (hpr : vy.persistent = false) :
    0 < vy.owned := by
  induction as generalizing ctx borrows vy with
  | nil => simp at hlast_a
  | cons a rest ih =>
    cases borrows with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : rest.length = bs.length := by simpa using hlen
      cases rest with
      | nil =>
        cases bs with
        | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast_a hlast_b
          subst hlast_a; subst hlast_b
          change (do let c1 ← ctx.consumeArg (.var y); c1.applyArgs [] []) = .ok ctx1 at happ
          by_cases hlt : vy.owned < 1
          · have herr : ∃ e, ctx.consumeArg (.var y) = .error e := by
              unfold RcCtx.consumeArg RcCtx.consumeVar
              simp only [hgety, hnr, Bool.false_or, hpr, Bool.false_eq_true, ↓reduceIte, hlt]
              exact ⟨_, rfl⟩
            rcases herr with ⟨e, he⟩
            rw [he] at happ
            change Except.error e = .ok ctx1 at happ
            cases happ
          · omega
        | cons _ _ => simp at hlen'
      | cons a2 rest2 =>
        cases bs with
        | nil => simp at hlen'
        | cons b2 bs2 =>
          have ha2 : (a2 :: rest2).getLast? = some (.var y) := by
            simpa [List.getLast?_cons_cons] using hlast_a
          have hb2 : (b2 :: bs2).getLast? = some false := by
            simpa [List.getLast?_cons_cons] using hlast_b
          by_cases hb : b = true
          · subst hb
            change (do let _ ← ctx.checkArgLive a; ctx.applyArgs (a2 :: rest2) (b2 :: bs2)) =
              .ok ctx1 at happ
            cases hchk : ctx.checkArgLive a with
            | error e =>
              rw [hchk] at happ
              change Except.error e = .ok ctx1 at happ
              cases happ
            | ok _ =>
              rw [hchk] at happ
              change ctx.applyArgs (a2 :: rest2) (b2 :: bs2) = .ok ctx1 at happ
              exact ih hnd happ hlen' ha2 hb2 hgety hnr hpr
          · have hbf : b = false := Bool.eq_false_iff.mpr hb
            subst hbf
            change (do let cm ← ctx.consumeArg a; cm.applyArgs (a2 :: rest2) (b2 :: bs2)) =
              .ok ctx1 at happ
            cases a with
            | erased =>
              change ctx.applyArgs (a2 :: rest2) (b2 :: bs2) = .ok ctx1 at happ
              exact ih hnd happ hlen' ha2 hb2 hgety hnr hpr
            | var z =>
              cases hca : ctx.consumeVar z 1 with
              | error e =>
                have hce : ctx.consumeArg (.var z) = .error e := by simp [RcCtx.consumeArg, hca]
                rw [hce] at happ
                change Except.error e = .ok ctx1 at happ
                cases happ
              | ok cm =>
                have hca' : ctx.consumeArg (.var z) = .ok cm := by simp [RcCtx.consumeArg, hca]
                rw [hca'] at happ
                change cm.applyArgs (a2 :: rest2) (b2 :: bs2) = .ok ctx1 at happ
                have hndm := consumeVar_nodup hnd hca
                obtain ⟨vy_m, hget_m, hnr_m, hpr_m, hle_m⟩ :=
                  consumeVar_preserves_flags_self hnd hca hgety
                have hpos_m := ih hndm happ hlen' ha2 hb2 hget_m
                  (by rw [hnr_m]; exact hnr) (by rw [hpr_m]; exact hpr)
                omega

private theorem localHandlesExcept_put_fresh_count_le {vs : List RcVar}
    (hnd : (vs.map RcVar.id).Nodup) {vx : RcVar}
    (hfr : ∀ v ∈ vs, v.id = vx.id → ∀ envH, varHandles envH v = [])
    {envH envH' : HValEnv} (henv : ∀ y, y ≠ vx.id → envH' y = envH y) {tgt : Nat} :
    ∀ a, List.count a
        (((RcCtx.put.go vx vs).filter (·.id != tgt)).map (varHandles envH')).flatten ≤
      List.count a (varHandles envH' vx) +
        List.count a ((vs.filter (·.id != tgt)).map (varHandles envH)).flatten := by
  induction vs with
  | nil =>
    intro a
    have hdef : RcCtx.put.go vx [] = [vx] := rfl
    rw [hdef]
    simp only [List.filter_cons, List.filter_nil, List.map_nil, List.flatten_nil,
      List.count_nil, Nat.add_zero]
    split <;> simp
  | cons hd tl ih =>
    intro a
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hdef : RcCtx.put.go vx (hd :: tl) =
        if (hd.id == vx.id) = true then vx :: tl else hd :: RcCtx.put.go vx tl := rfl
    rw [hdef]
    by_cases heq : hd.id = vx.id
    · have hb : (hd.id == vx.id) = true := by simp [heq]
      simp only [hb, ↓reduceIte]
      have htl_map : (tl.filter (·.id != tgt)).map (varHandles envH') =
          (tl.filter (·.id != tgt)).map (varHandles envH) := by
        apply List.map_congr_left
        intro u hu
        have hu_tl := (List.mem_filter.mp hu).1
        have hne : u.id ≠ vx.id := fun he => hnd.1 (heq ▸ he ▸ List.mem_map.mpr ⟨u, hu_tl, rfl⟩)
        simp only [varHandles, henv u.id hne]
      have hhd0 : varHandles envH hd = [] := hfr hd (.head _) heq envH
      by_cases ht1 : (vx.id != tgt) = true
      · have ht2 : (hd.id != tgt) = true := by rw [heq]; exact ht1
        simp [ht1, ht2, htl_map, hhd0]
      · have h1f : (vx.id != tgt) = false := Bool.eq_false_iff.mpr ht1
        have h2f : (hd.id != tgt) = false := by rw [heq]; exact h1f
        simp [h1f, h2f, htl_map]
    · have hbf : (hd.id == vx.id) = false := by simp [heq]
      simp only [hbf, Bool.false_eq_true, ↓reduceIte]
      have hih := ih hnd.2 (fun v hv => hfr v (.tail _ hv)) a
      have hhd_eq : varHandles envH' hd = varHandles envH hd := by
        simp only [varHandles, henv hd.id heq]
      by_cases ht : (hd.id != tgt) = true
      · simp [ht, hhd_eq] at hih ⊢; omega
      · have htf : (hd.id != tgt) = false := Bool.eq_false_iff.mpr ht
        simp [htf] at hih ⊢; exact hih

private theorem cleanVar_bindOwned_default (x : Nat) (ty : LcTy) :
    CleanVar (let noRc := !ty.needsRc;
      { id := x, ty := ty, noRc := noRc,
        persistent := if noRc then false else false,
        owned := if (noRc || false) then 0 else 1,
        excl := if (noRc || false) then false else false,
        resetTok := if (noRc || false) then false else false }) := by
  simpa using cleanVar_bindOwned x ty false false

theorem propagateMark_step_invs {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {x y : Nat} {ty : LcTy}
    {as : List LcArg} {borrows : List Bool} {ctx1 : RcCtx} {vy : RcVar} {bv : BitVec 64}
    {pv : PVal}
    (hrc : RcInv rt rf σ) (hcl : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx) (hsbp : SharedBoolPreds rf.ctx)
    (hex : ExclCtorHeap rf) (hsh : ShadowOk sm rf.ctx ρP rf.envP)
    (hfr : binderFreshOwned rf.ctx x = true)
    (happ : rf.ctx.applyArgs as borrows = .ok ctx1)
    (hnost : argsNoSharedTarget rf.ctx as borrows = true)
    (htynrc : ty.needsRc = true)
    (hgety : rf.ctx.get? y = some vy) (hlive_y : vy.isLive = true)
    (hns_y : ¬vy.ty.isScalar = true)
    (hlen : as.length = borrows.length)
    (hlast_a : as.getLast? = some (.var y)) (hlast_b : borrows.getLast? = some false)
    (hhy : rf.envH y = some (vy.ty, Word.i64 bv))
    (heven : bv &&& 1#64 = 0#64)
    (hvr : ValRep ty pv (Word.i64 bv) σ.objs) :
    let ctx' := ctx1.bindOwned x ty
    let rf' : RcFrame :=
      ⟨ctx', rf.envP.set x pv, rf.envH.set x ty (Word.i64 bv), rf.extH, rf.ghostH⟩
    RcInv rt rf' σ ∧ CleanVars ctx' ∧ ParentsOwned ctx' ∧ NoRcCorrect ctx' ∧
      ParentChildBacked rf' σ.objs ∧ SharedTargetsHeap rf' ∧
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ.objs ∧ EntryPres rf0 σ0 rf' σ ∧
      SharedBoolVars ctx' ∧ SharedBoolPreds ctx' ∧ ExclCtorHeap rf' ∧
      ShadowOk (sm.filter (·.1 != x)) ctx' (ρP.set x pv) rf'.envP := by
  have rc1 := rcInv_applyArgs_step hrc hcl hpo happ hnost
  rcases rc1 with ⟨hperm, hrc1, hcl1, hpo1⟩
  have hnd1 := applyArgs_nodup hrc.2.1 happ
  have hfr1 := binderFreshOwned_applyArgs hrc.2.1 hcl happ hfr
  let rf1 : RcFrame := { rf with ctx := ctx1 }
  let vx : RcVar :=
    let noRc := !ty.needsRc
    ⟨x, ty, noRc, if noRc then false else false, if (noRc || false) then 0 else 1,
      false, none, if (noRc || false) then false else false,
      if (noRc || false) then false else false⟩
  let ctx' := ctx1.bindOwned x ty
  let rf' : RcFrame :=
    ⟨ctx', rf.envP.set x pv, rf.envH.set x ty (Word.i64 bv), rf.extH, rf.ghostH⟩
  have hvy_nr : vy.noRc = false := by
    obtain ⟨_, _, _, hvy_h, _, hvy_ns⟩ := hrc.2.2.2.1 vy (RcCtx.get?_mem hgety).1 hlive_y
    obtain ⟨bv0, hbw0, hnr0, _⟩ := hvy_ns hns_y
    rw [(RcCtx.get?_mem hgety).2, hhy] at hvy_h
    cases hvy_h
    have hbv_eq : bv = bv0 := by simpa [Word.i64] using hbw0
    subst hbv_eq
    cases h : vy.noRc
    · rfl
    · exact absurd heven (hnr0 h)
  have hvx_vh : varHandles rf'.envH vx = [bv] := by
    simp [varHandles, vx, htynrc, rf', HValEnv.set, Word.i64, Word.toBV64?, heven]
  have hvi_x : VarInv vx rf' σ.objs := by
    intro _
    refine ⟨pv, Word.i64 bv, by simp [vx, rf', PValEnv.set], by simp [vx, rf', HValEnv.set],
      hvr, fun _ => ?_⟩
    refine ⟨bv, rfl, fun h => by simp [vx, htynrc] at h, fun h => by simp [vx] at h,
      fun h => by simp [vx] at h, fun _ _ h => by simp [vx] at h⟩
  have hhrs : HandlesRcSound
      (varHandles rf'.envH vx ++ localHandles ctx1 rf.envH ++ rf.extH ++ rf.ghostH) σ.objs := by
    rw [hvx_vh]
    by_cases hpr : vy.persistent = true
    · obtain ⟨_, _, _, hvy_h, _, hvy_ns⟩ := hrc.2.2.2.1 vy (RcCtx.get?_mem hgety).1 hlive_y
      obtain ⟨bv0, hbw0, _, hpr0, _⟩ := hvy_ns hns_y
      rw [(RcCtx.get?_mem hgety).2, hhy] at hvy_h
      cases hvy_h
      have hbv_eq : bv = bv0 := by simpa [Word.i64] using hbw0
      subst hbv_eq
      obtain ⟨o0, ho0, ha0, hrc0⟩ := hpr0 hpr heven
      refine ⟨hrc1.2.2.1.1, fun q hq hpos => ?_⟩
      have hne : q.addr ≠ bv := by
        intro heq
        have hqe := obj_addr_inj_nodup hrc.1.2 hq ho0 (heq.trans ha0.symm)
        subst hqe; simp [hrc0] at hpos
      have hc0 := hrc1.2.2.1.2 q hq hpos
      simpa [frameHandles, rf1, List.count_cons, List.count_append, hne.symm] using hc0
    · have hpr_f : vy.persistent = false := Bool.eq_false_iff.mpr hpr
      have howned_y :=
        applyArgs_consumeVar_owned_pos hrc.2.1 happ hlen hlast_a hlast_b hgety hvy_nr hpr_f
      have hcv : bv ∈ consumeVarHandles rf y 1 := by
        simp [consumeVarHandles, hgety, hvy_nr, hpr_f, hhy, Word.i64, Word.toBV64?, heven]
      have hm_app := mem_applyArgsHandles_of_getLast hlen hlast_a hlast_b hcv
      have hle_cnt : ∀ a, List.count a ([bv] ++ localHandles ctx1 rf.envH) ≤
          List.count a (localHandles rf.ctx rf.envH) := by
        intro a
        rw [hperm.count_eq]
        simpa using count_cons_le_add bv (localHandles ctx1 rf.envH)
          (applyArgsHandles rf as borrows) hm_app a
      refine ⟨hrc.2.2.1.1, fun q hq hpos => ?_⟩
      have hc := hrc.2.2.1.2 q hq hpos
      have hle_q := hle_cnt q.addr
      rw [List.count_append] at hle_q
      simp only [frameHandles, List.count_append] at hc ⊢
      omega
  have hbk_f : ∀ a, Backed σ.objs (frameHandles rf1) a → Backed σ.objs (frameHandles rf') a := by
    intro a ha
    rcases ha with h0 | ⟨r, hr, hreach⟩
    · exact Or.inl h0
    · refine Or.inr ⟨r, ?_, hreach⟩
      simp only [frameHandles, rf1, rf', List.mem_append] at hr ⊢
      rcases hr with (hrl | hre) | hrg
      · left; left
        unfold localHandles at hrl ⊢
        rw [List.mem_flatten] at hrl ⊢
        rcases hrl with ⟨vh, hvh_m, hr_vh⟩
        rcases List.mem_map.mp hvh_m with ⟨u, hu, rfl⟩
        have hne_u : u.id ≠ x := by
          intro heq
          have hempty := binderFresh_varHandles_empty hnd1 (envH := rf.envH) hfr1 u hu heq
          rw [hempty] at hr_vh; cases hr_vh
        have hgetu' : ctx'.get? u.id = some u := by
          change (ctx1.bindOwned x ty).get? u.id = some u
          rw [get?_bindOwned_ne ctx1 hnd1 hne_u]
          exact get?_of_mem_nodup hnd1 hu
        refine ⟨varHandles rf'.envH u, List.mem_map.mpr ⟨u, (RcCtx.get?_mem hgetu').1, rfl⟩, ?_⟩
        simpa [varHandles, rf', HValEnv.set, hne_u] using hr_vh
      · left; right; exact hre
      · right; exact hrg
  have hspi : SharedPredInv rf' σ.objs := by
    intro p hp vb vt hgb hgt hlv htnr htpr
    have hp1 : p ∈ ctx1.sharedPreds := hp
    have hfr_p : p.1 ≠ x ∧ p.2 ≠ x := by
      unfold binderFreshOwned at hfr1
      simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hfr1
      exact hfr1.1.2 p hp1
    have hgb1 : ctx1.get? p.1 = some vb := by
      change (ctx1.bindOwned x ty).get? p.1 = some vb at hgb
      rwa [get?_bindOwned_ne ctx1 hnd1 hfr_p.1] at hgb
    have hgt1 : ctx1.get? p.2 = some vt := by
      change (ctx1.bindOwned x ty).get? p.2 = some vt at hgt
      rwa [get?_bindOwned_ne ctx1 hnd1 hfr_p.2] at hgt
    have hspi1 := hrc1.2.2.2.2 p hp1 vb vt hgb1 hgt1 hlv htnr htpr
    dsimp only [rf']
    simp only [PValEnv.set, HValEnv.set, hfr_p.1, hfr_p.2, ↓reduceIte]
    refine ⟨fun htag0 => ?_, hspi1.2⟩
    obtain ⟨bvt, hh_t, hev_t, hrest_t⟩ := hspi1.1 htag0
    refine ⟨bvt, hh_t, hev_t, fun ho => ?_⟩
    obtain ⟨hcnt0, o_t, ho_t, ha_t, hrc_t⟩ := hrest_t ho
    refine ⟨?_, o_t, ho_t, ha_t, hrc_t⟩
    have hne_bv : bv ≠ bvt := by
      intro heq; subst heq
      by_cases hpr : vy.persistent = true
      · obtain ⟨_, _, _, hvy_h, _, hvy_ns⟩ := hrc.2.2.2.1 vy (RcCtx.get?_mem hgety).1 hlive_y
        obtain ⟨bv0, hbw0, _, hpr0, _⟩ := hvy_ns hns_y
        rw [(RcCtx.get?_mem hgety).2, hhy] at hvy_h
        cases hvy_h
        have hbv_eq : bv = bv0 := by simpa [Word.i64] using hbw0
        subst hbv_eq
        obtain ⟨o0, ho0, ha0, hrc0⟩ := hpr0 hpr heven
        have heqo := obj_addr_inj_nodup hrc.1.2 ho0 ho_t (ha0.trans ha_t.symm)
        subst heqo; simp [hrc0] at hrc_t; omega
      · have hpr_f : vy.persistent = false := Bool.eq_false_iff.mpr hpr
        have howned_y :=
          applyArgs_consumeVar_owned_pos hrc.2.1 happ hlen hlast_a hlast_b hgety hvy_nr hpr_f
        have hp0 : p ∈ rf.ctx.sharedPreds := (applyArgs_ctx_props hrc.2.1 happ).2.1 p hp1
        have hne_yt : y ≠ p.2 := by
          unfold argsNoSharedTarget at hnost
          simp only [List.all_eq_true] at hnost
          have hmem_zip : ((.var y : LcArg), false) ∈ as.zip borrows :=
            mem_zip_of_getLast? hlen hlast_a hlast_b
          have hnost_y := hnost ((.var y : LcArg), false) hmem_zip
          simp only [Bool.false_eq_true, ↓reduceIte, List.all_eq_true, bne_iff_ne] at hnost_y
          exact Ne.symm (hnost_y p hp0)
        obtain ⟨vb0, hgb0, hlb0, _⟩ := applyArgs_get?_live_back hrc.2.1 hcl happ p.1 hgb1 hlv
        obtain ⟨vt0, hgt0, nr_t0, pr_t0, o_le0⟩ := applyArgs_preserves_flags hrc.2.1 happ hgt1
        have hspi0 := hrc.2.2.2.2 p hp0 vb0 vt0 hgb0 hgt0 hlb0
          (by rw [← nr_t0]; exact htnr) (by rw [← pr_t0]; exact htpr)
        obtain ⟨bvt', hh0', _, hrest0⟩ := hspi0.1 htag0
        obtain ⟨hcnt_rf0, _⟩ := hrest0 (by omega)
        dsimp only [rf1] at hh_t
        rw [hh_t] at hh0'
        have hbv_eq : Word.i64 bv = Word.i64 bvt' := congrArg Prod.snd (Option.some.inj hh0')
        have hbv_t : bvt' = bv := by simpa [Word.i64] using hbv_eq.symm
        rw [hbv_t] at hcnt_rf0
        have hvy_vh : bv ∈ varHandles rf.envH vy :=
          varHandles_mem_of_owned hvy_nr hpr_f (hcl vy (RcCtx.get?_mem hgety).1).2.2.2.2
            howned_y ⟨(vy.ty, Word.i64 bv), by rw [(RcCtx.get?_mem hgety).2]; exact hhy, rfl⟩
            heven
        have hmem_loc : bv ∈ localHandlesExcept rf.ctx rf.envH p.2 := by
          unfold localHandlesExcept
          rw [List.mem_flatten]
          refine ⟨varHandles rf.envH vy, List.mem_map.mpr ⟨vy, ?_, rfl⟩, hvy_vh⟩
          rw [List.mem_filter]
          exact ⟨(RcCtx.get?_mem hgety).1, by simp [(RcCtx.get?_mem hgety).2, hne_yt]⟩
        have hpos_cnt :
            0 < List.count bv (localHandlesExcept rf.ctx rf.envH p.2 ++ rf.extH ++ rf.ghostH) :=
          List.count_pos_iff.mpr
            (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hmem_loc))))
        omega
    have hcnt_le : List.count bvt (localHandlesExcept ctx' rf'.envH p.2) ≤
        List.count bvt (varHandles rf'.envH vx) +
          List.count bvt (localHandlesExcept ctx1 rf.envH p.2) :=
      localHandlesExcept_put_fresh_count_le hnd1 (vx := vx)
        (fun v hv hid e =>
          binderFresh_varHandles_empty hnd1 (envH := e) hfr1 v hv (by simpa [vx] using hid))
        (envH := rf.envH) (envH' := rf'.envH)
        (fun z hz => by
          dsimp only [rf']; simp [HValEnv.set, show z ≠ x from by simpa [vx] using hz])
        (tgt := p.2) bvt
    have hcnt_vx : List.count bvt (varHandles rf'.envH vx) = 0 := by
      rw [hvx_vh]
      simp [List.count_eq_zero, Ne.symm hne_bv]
    rw [hcnt_vx, Nat.zero_add] at hcnt_le
    dsimp only [rf'] at hcnt_le
    simp only [List.count_append] at hcnt0 hcnt_le ⊢
    omega
  have hrci := rcInv_put_fresh hrc1 hcl1 hfr1 rfl (cleanVar_bindOwned_default x ty) hrc.1
    (fun o ho hwf => ⟨o, ho, objDataEq_refl o hwf, rfl⟩) hvi_x hhrs hbk_f (fun _ h => h) hspi
  refine ⟨hrci.1, hrci.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu p hp
    have hgetu := get?_of_mem_nodup hrci.1.2.1 hu
    have hne : u.id ≠ x := by
      intro heq
      have hgetx : (ctx1.bindOwned x ty).get? x = some u := by
        change (ctx1.bindOwned x ty).get? u.id = some u at hgetu
        rwa [heq] at hgetu
      dsimp only [RcCtx.bindOwned] at hgetx
      rw [get?_put_self ctx1 hnd1 _] at hgetx
      cases hgetx; simp at hp
    change (ctx1.bindOwned x ty).get? u.id = some u at hgetu
    rw [get?_bindOwned_ne ctx1 hnd1 hne] at hgetu
    obtain ⟨vp, hvpm, hidvp, hnrp, hprp, hovp, hbrp⟩ := hpo1 u (RcCtx.get?_mem hgetu).1 p hp
    have hnep : p ≠ x := by
      intro heq; subst heq
      unfold binderFreshOwned at hfr1
      simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hfr1
      exact absurd hp (hfr1.1.1 u (RcCtx.get?_mem hgetu).1)
    have hgetvp' := get?_of_mem_nodup hnd1 hvpm
    rw [hidvp] at hgetvp'
    have hgetvp'' : (ctx1.bindOwned x ty).get? p = some vp := by
      rw [get?_bindOwned_ne ctx1 hnd1 hnep]; exact hgetvp'
    exact ⟨vp, (RcCtx.get?_mem hgetvp'').1, hidvp, hnrp, hprp, hovp, hbrp⟩
  · exact noRcCorrect_bindOwned hnd1 (noRcCorrect_applyArgs hrc.2.1 hno as borrows happ)
      x ty false false false
  · have hpcb1 := parentChildBacked_applyArgs hrc.2.1 hcl happ hpcb
    intro u hu hlive hunr hupr hubr p hp bv0 hb0 hev0
    have hgetu := get?_of_mem_nodup hrci.1.2.1 hu
    have hne : u.id ≠ x := by
      intro heq
      have hgetx : (ctx1.bindOwned x ty).get? x = some u := by
        change (ctx1.bindOwned x ty).get? u.id = some u at hgetu
        rwa [heq] at hgetu
      dsimp only [RcCtx.bindOwned] at hgetx
      rw [get?_put_self ctx1 hnd1 _] at hgetx
      cases hgetx; simp at hubr
    change (ctx1.bindOwned x ty).get? u.id = some u at hgetu
    rw [get?_bindOwned_ne ctx1 hnd1 hne] at hgetu
    have hnep : p ≠ x := by
      intro heq; subst heq
      unfold binderFreshOwned at hfr1
      simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hfr1
      exact absurd hp (hfr1.1.1 u (RcCtx.get?_mem hgetu).1)
    simp only [HValEnv.set, hne, ↓reduceIte] at hb0
    have hres0 := hpcb1 u (RcCtx.get?_mem hgetu).1 hlive hunr hupr hubr p hp bv0 hb0 hev0
    simpa [HValEnv.set, hnep] using hres0
  · exact sharedTargetsHeap_applyArgs_bindOwned hrc.2.1 hcl hsth happ hfr
  · simpa [rf'] using hhih
  · have hep1 := entryPres_applyArgs hrc.2.1 hcl happ hep
    refine ⟨hep1.1, fun a ha hiso => ?_, hep1.2.2.1, hep1.2.2.2⟩
    obtain ⟨hiso_rf, _⟩ := hep.2.1 a ha hiso
    obtain ⟨hiso1, hobj1⟩ := hep1.2.1 a ha hiso
    refine ⟨⟨fun u hu hlive hns w hw => ?_, hiso1.2.1, hiso1.2.2⟩, hobj1⟩
    by_cases heq : u.id = x
    · simp only [HValEnv.set, heq, ↓reduceIte] at hw
      cases hw
      exact hiso_rf.1 vy (RcCtx.get?_mem hgety).1 hlive_y (by simp [hns_y])
        (Word.i64 bv) (by rw [(RcCtx.get?_mem hgety).2]; exact hhy)
    · have hgetu := get?_of_mem_nodup hrci.1.2.1 hu
      change (ctx1.bindOwned x ty).get? u.id = some u at hgetu
      rw [get?_bindOwned_ne ctx1 hnd1 heq] at hgetu
      simp only [HValEnv.set, heq, ↓reduceIte] at hw
      exact hiso1.1 u (RcCtx.get?_mem hgetu).1 hlive hns w hw
  · exact (sharedBool_applyArgs_bindOwned hrc.2.1 hsbv hsbp happ hfr ty).1
  · exact (sharedBool_applyArgs_bindOwned hrc.2.1 hsbv hsbp happ hfr ty).2
  · exact exclCtorHeap_applyArgs_bindOwned (x := x) (ty := ty) (pv := pv) (w := Word.i64 bv)
      hrc.2.1 hex happ
  · exact shadowOk_applyArgs_bindOwned (x := x) (ty := ty) (pv := pv) hrc.2.1 hsh happ

private theorem propagateMark_sig_args {ctx : RcCtx} {f : String} {as : List LcArg}
    {borrows : List Bool}
    (hpw : perceusPrimWf f as.length = true)
    (hsig : primRcSig f as.length = some (borrows, .owned))
    (hpaw : perceusPrimArgsWf ctx f as = true)
    (hpm : (f == "Array.propagateMark" || f == "ByteArray.propagateMark" ||
        f == "String.propagateMark") = true) :
    borrows.getLast? = some false ∧
      (as.all fun a => match a with
        | .erased => true
        | .var x => match ctx.get? x with
          | some v => !v.ty.isScalar | none => false) = true := by
  simp only [Bool.or_eq_true, beq_iff_eq] at hpm
  rcases hpm with (rfl | rfl) | rfl
  · have hsp : splitDot "Array.propagateMark" = ["Array", "propagateMark"] := rfl
    have has4 : as.length = 4 := by
      unfold perceusPrimWf at hpw; rw [hsp] at hpw
      rcases hlen : as.length with _ | _ | _ | _ | _ | n <;> simp [hlen] at hpw
      rfl
    have hbr : borrows = [true, true, true, false] := by
      unfold primRcSig at hsig; rw [hsp, has4] at hsig
      simp at hsig; exact hsig.symm
    subst hbr
    rcases as with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | tl⟩⟩⟩⟩ <;> simp at has4
    unfold perceusPrimArgsWf at hpaw; rw [hsp] at hpaw; dsimp only [uintWidth?] at hpaw
    exact ⟨rfl, hpaw⟩
  · have hsp : splitDot "ByteArray.propagateMark" = ["ByteArray", "propagateMark"] := rfl
    have has2 : as.length = 2 := by
      unfold perceusPrimWf at hpw; rw [hsp] at hpw
      rcases hlen : as.length with _ | _ | _ | n <;> simp [hlen] at hpw
      rfl
    have hbr : borrows = [true, false] := by
      unfold primRcSig at hsig; rw [hsp, has2] at hsig
      simp at hsig; exact hsig.symm
    subst hbr
    rcases as with _ | ⟨a0, _ | ⟨a1, _ | tl⟩⟩ <;> simp at has2
    unfold perceusPrimArgsWf at hpaw; rw [hsp] at hpaw; dsimp only [uintWidth?] at hpaw
    exact ⟨rfl, hpaw⟩
  · have hsp : splitDot "String.propagateMark" = ["String", "propagateMark"] := rfl
    have has2 : as.length = 2 := by
      unfold perceusPrimWf at hpw; rw [hsp] at hpw
      rcases hlen : as.length with _ | _ | _ | n <;> simp [hlen] at hpw
      rfl
    have hbr : borrows = [true, false] := by
      unfold primRcSig at hsig; rw [hsp, has2] at hsig
      simp at hsig; exact hsig.symm
    subst hbr
    rcases as with _ | ⟨a0, _ | ⟨a1, _ | tl⟩⟩ <;> simp at has2
    unfold perceusPrimArgsWf at hpaw; rw [hsp] at hpaw; dsimp only [uintWidth?] at hpaw
    exact ⟨rfl, hpaw⟩

private theorem splitDot_go_singleton (cs acc : List Char) (s : String)
    (h : splitDot.go cs acc = [s]) :
    String.ofList (acc.reverse ++ cs) = s := by
  induction cs generalizing acc with
  | nil => simpa [splitDot.go] using h
  | cons c cs ih =>
    have hstep : splitDot.go (c :: cs) acc =
        if (c == '.') = true then String.ofList acc.reverse :: splitDot.go cs []
        else splitDot.go cs (c :: acc) := rfl
    rw [hstep] at h
    by_cases hc : (c == '.') = true
    · simp only [hc, ↓reduceIte, List.cons.injEq] at h
      have hne : splitDot.go cs [] ≠ [] := by
        have hgo : ∀ l a, splitDot.go l a ≠ [] := by
          intro l
          induction l with
          | nil => intro a; simp [splitDot.go]
          | cons d ds ihd =>
            intro a
            have hs : splitDot.go (d :: ds) a =
                if (d == '.') = true then String.ofList a.reverse :: splitDot.go ds []
                else splitDot.go ds (d :: a) := rfl
            rw [hs]; split
            · simp
            · exact ihd (d :: a)
        exact hgo cs []
      exact False.elim (hne h.2)
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
      simpa [List.reverse_cons, List.append_assoc] using ih (c :: acc) h

private theorem splitDot_go_pair (cs acc : List Char) (a b : String)
    (h : splitDot.go cs acc = [a, b]) :
    String.ofList (acc.reverse ++ cs) = a ++ "." ++ b := by
  induction cs generalizing acc with
  | nil => simp [splitDot.go] at h
  | cons c cs ih =>
    have hstep : splitDot.go (c :: cs) acc =
        if (c == '.') = true then String.ofList acc.reverse :: splitDot.go cs []
        else splitDot.go cs (c :: acc) := rfl
    rw [hstep] at h
    by_cases hc : (c == '.') = true
    · simp only [hc, ↓reduceIte, List.cons.injEq] at h
      rcases h with ⟨rfl, hb⟩
      have hcb : c = '.' := beq_iff_eq.mp hc
      subst hcb
      have hbs := splitDot_go_singleton cs [] b hb
      simp only [List.reverse_nil, List.nil_append] at hbs
      rw [← hbs, ← String.ofList_toList (s := String.ofList acc.reverse ++ "." ++ String.ofList cs)]
      simp [String.toList_append]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
      simpa [List.reverse_cons, List.append_assoc] using ih (c :: acc) h

private theorem splitDot_eq_pair {f a b : String} (h : splitDot f = [a, b]) :
    f = a ++ "." ++ b :=
  by simpa using splitDot_go_pair f.toList [] a b h

private theorem primRcSig_not_persistent {f : String} {n : Nat} {borrows : List Bool}
    (hpw : perceusPrimWf f n = true) (hsig : primRcSig f n = some (borrows, .persistent)) :
    False := by
  unfold perceusPrimWf at hpw
  unfold primRcSig at hsig
  split at hsig
  · split at hsig <;> cases hsig
  · split at hsig <;> cases hsig
  · split at hsig <;> cases hsig
  · split at hsig <;> cases hsig
  · split at hsig <;> cases hsig
  · split at hsig <;> cases hsig
  · split at hsig <;> cases hsig
  · rename_i hsp
    split at hsig
    · simp only [hsp] at hpw; cases hpw
    · cases hsig
    · cases hsig
    · cases hsig
    · cases hsig
    · cases hsig
    · cases hsig
    · cases hsig
    · cases hsig
    · cases hsig
    · cases hsig
    · cases hsig
    · cases hsig
    · cases hsig
    · cases hsig
    · cases hsig
    · cases hsig
    · cases hsig
    · cases hsig
  · cases hsig
  · cases hsig
  · split at hsig <;> cases hsig
  · split at hsig
    · split at hsig <;> cases hsig
    · cases hsig
  · cases hsig

private theorem primRcSig_borrowed_is_arr {f : String} {n idx : Nat} {borrows : List Bool}
    (hpw : perceusPrimWf f n = true) (hsig : primRcSig f n = some (borrows, .borrowed idx)) :
    f = "Array.get!InternalBorrowed" ∧ n = 4 ∧ idx = 2 ∧ borrows = [true, true, true, true] := by
  unfold primRcSig at hsig
  split at hsig
  · split at hsig <;> cases hsig
  · split at hsig <;> cases hsig
  · split at hsig <;> cases hsig
  · split at hsig <;> cases hsig
  · split at hsig <;> cases hsig
  · split at hsig <;> cases hsig
  · rename_i hsp
    split at hsig <;> cases hsig <;>
      first
      | exact ⟨by simpa using splitDot_eq_pair hsp, rfl, rfl, rfl⟩
      | (simp only [perceusPrimWf, hsp] at hpw; cases hpw)
  · split at hsig <;> cases hsig
  · cases hsig
  · cases hsig
  · split at hsig <;> cases hsig
  · split at hsig
    · split at hsig <;> cases hsig
    · cases hsig
  · cases hsig

private theorem primRcSig_len {f : String} {n : Nat} {borrows : List Bool} {rk : PrimRetKind}
    (hsig : primRcSig f n = some (borrows, rk)) :
    borrows.length = n := by
  unfold primRcSig at hsig
  split at hsig
  · split at hsig <;> cases hsig <;> rfl
  · split at hsig <;> cases hsig <;> rfl
  · split at hsig <;> cases hsig <;> rfl
  · split at hsig <;> cases hsig <;> rfl
  · split at hsig <;> cases hsig <;> rfl
  · split at hsig <;> cases hsig <;> rfl
  · split at hsig <;> cases hsig <;> rfl
  · split at hsig <;> cases hsig <;> rfl
  · cases hsig; simp
  · cases hsig; simp
  · split at hsig <;> cases hsig <;> simp_all
  · split at hsig
    · split at hsig <;> cases hsig <;> simp
    · cases hsig
  · cases hsig

theorem prim_step {m : LcModule} {Δr : PResEnv} {Δh : HEnv}
    {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState} {sm : List (Nat × Nat × List Bool)}
    {ρP : PValEnv} {rem wr rcr x : Nat} {ty : LcTy} {f : String} {as : List LcArg}
    {jpsOk : List JpEntry} {Jp : PResJEnv} {Jh : HJEnv} {jumps : List (Nat × RcCtx)}
    {ctx' : RcCtx} {K : PResPost} {Xp : PResXPost} {Kh : HPost} {Xh : HXPost}
    (hnone : (mkRcModEnv m).decls.find? (·.1 == f) = none)
    (hpvwf : perceusValWf (mkRcModEnv m) rf.ctx x ty (.fap f as) = true)
    (hinit : ∀ a ∈ as, argScalarInit sm a = true)
    (hcv : checkVal (mkRcModEnv m) rf.ctx x ty (.fap f as) = .ok ctx')
    (hpr : PRValWp (mkRcModEnv m) Δr ρP ty (.fap f as) rem wr rcr K Xp)
    (hjok : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps)
    (hrc : RcInv rt rf σ) (hcl : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx) (hsbp : SharedBoolPreds rf.ctx)
    (hex : ExclCtorHeap rf) (hsh : ShadowOk sm rf.ctx ρP rf.envP) (hsmwf : ShadowSmWf sm)
    (hres : ResStateInv σ rem wr rcr) (hjsc : JpsScopeIn (jpsOk.map JpEntry.info) rf.ctx)
    (hcont : ∀ {rf' : RcFrame} {σ' : HState} {sm' : List (Nat × Nat × List Bool)}
      {ρP' : PValEnv} {rem' wr' rcr' : Nat} {jpsOk' : List JpEntry} {pv : PVal} {rw : Word},
      K pv rem' wr' rcr' →
      rf'.ctx = ctx' → rf'.envH = rf.envH.set x ty rw → ρP' = ρP.set x pv →
      sm' = sm.filter (·.1 != x) →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → SharedBoolPreds rf'.ctx → ExclCtorHeap rf' →
      ShadowSmWf sm' → ShadowOk sm' rf'.ctx ρP' rf'.envP →
      ResStateInv σ' rem' wr' rcr' →
      JpsScopeIn (jpsOk'.map JpEntry.info) rf'.ctx →
      JpsOk rt rf0 σ0 Jp Jh jpsOk' rf' ρP' jumps →
      jpsOk' = jpsOk.map (fun e => { e with mutVars := x :: e.mutVars }) →
      Kh rw σ')
    (hx : ∀ {c rem' wr' rcr' : Nat} {σ' : HState},
      Xp c rem' wr' rcr' → Xh (BitVec.ofNat 64 c) σ') :
    HVal.wp Δh rt rf.envH ty (.fap f as) Kh Xh σ := by
  have hpvwf' := hpvwf
  unfold perceusValWf at hpvwf'
  simp only [Bool.and_eq_true, hnone] at hpvwf'
  rcases hpvwf' with ⟨hfr, ⟨⟨⟨⟨hpw, hprw⟩, hpaw⟩, hpm_ty⟩, hsig_m⟩⟩
  cases hsig : primRcSig f as.length with
  | none => simp [hsig] at hsig_m
  | some sr =>
    rcases sr with ⟨borrows, retKind⟩
    simp only [hsig] at hsig_m
    have hnost : argsNoSharedTarget rf.ctx as borrows = true := hsig_m
    have hfind_f : (List.find? (fun x => x.fst == f) (mkRcModEnv m).decls).isSome = false := by
      simp [hnone]
    unfold PRValWp at hpr
    cases hevp : ρP.evalArgs as with
    | none => simp [hevp] at hpr
    | some pvs =>
      simp only [hevp] at hpr
      by_cases hoob : f = "outOfBounds._redArg"
      · subst hoob
        simp only [beq_self_eq_true, ↓reduceIte, beq_iff_eq] at hpr
        rcases hpr with ⟨_, hxp⟩
        cases happ : rf.ctx.applyArgs as borrows with
        | error e =>
          unfold checkVal at hcv
          simp only [hnone, hsig, happ] at hcv
          change Except.error e = Except.ok ctx' at hcv
          cases hcv
        | ok ctx1 =>
          have hlive := applyArgs_var_live hrc.2.1 hcl happ
          have hl_eval : ∀ a ∈ as, match a with
              | .erased => True
              | .var z => ∃ v, rf.ctx.get? z = some v ∧ v.isLive = true := by
            intro a ha
            rcases hlive a ha with rfl | ⟨z, v, rfl, hgz, hlv⟩
            · trivial
            · exact ⟨v, hgz, hlv⟩
          have hevp_rf : rf.envP.evalArgs as = some pvs := by
            rw [← shadowOk_evalArgs_init hsh hinit hl_eval]; exact hevp
          obtain ⟨ws, hevh, _⟩ := evalArgsOwn_sim hrc.2.2.2.1 hl_eval hevp_rf
          have has1 : as.length = 1 := by
            have hsp : splitDot "outOfBounds._redArg" = ["outOfBounds", "_redArg"] := rfl
            unfold perceusPrimWf at hpw
            simp [hsp] at hpw
            exact hpw
          cases as with
          | nil => simp at has1
          | cons a0 as_t =>
            cases as_t with
            | cons _ _ => simp at has1
            | nil =>
              cases ws with
              | nil =>
                have hstep : rf.envH.evalArgsOwn [a0] =
                    match rf.envH.evalArgOwn a0, rf.envH.evalArgsOwn [] with
                    | some v, some vs => some (v :: vs) | _, _ => none := rfl
                rw [hstep] at hevh
                cases h0 : rf.envH.evalArgOwn a0 <;> simp [h0] at hevh
                have he0 : rf.envH.evalArgsOwn [] = some [] := rfl
                rw [he0] at hevh; cases hevh
              | cons w0 ws_t =>
                cases ws_t with
                | cons wh2 wt2 =>
                  have hstep : rf.envH.evalArgsOwn [a0] =
                      match rf.envH.evalArgOwn a0, rf.envH.evalArgsOwn [] with
                      | some v, some vs => some (v :: vs) | _, _ => none := rfl
                  have he0 : rf.envH.evalArgsOwn [] = some [] := rfl
                  rw [hstep, he0] at hevh
                  cases h0 : rf.envH.evalArgOwn a0 <;> simp [h0] at hevh
                | nil =>
                  have hbv_some : w0.toBV64?.isSome = true := by
                    rcases hlive a0 (.head _) with rfl | ⟨z, vz, rfl, hgz, hlv⟩
                    · have hstep : rf.envH.evalArgsOwn [LcArg.erased] =
                          match rf.envH.evalArgOwn .erased, rf.envH.evalArgsOwn [] with
                          | some v, some vs => some (v :: vs) | _, _ => none := rfl
                      have he0 : rf.envH.evalArgsOwn [] = some [] := rfl
                      have her : rf.envH.evalArgOwn .erased = some (Word.i64 1#64) := rfl
                      rw [hstep, he0, her] at hevh; cases hevh; rfl
                    · have hns_z : ¬vz.ty.isScalar = true := by
                        have hsp : splitDot "outOfBounds._redArg" =
                            ["outOfBounds", "_redArg"] := rfl
                        unfold perceusPrimArgsWf at hpaw
                        simp [hsp, hgz, uintWidth?] at hpaw
                        simp [hpaw]
                      obtain ⟨_, w0', _, hhz, hvr_z, _⟩ :=
                        hrc.2.2.2.1 vz (RcCtx.get?_mem hgz).1 hlv
                      rw [(RcCtx.get?_mem hgz).2] at hhz
                      have hw0' : w0' = w0 := by
                        have hstep : rf.envH.evalArgsOwn [.var z] =
                            match rf.envH.evalArgOwn (.var z), rf.envH.evalArgsOwn [] with
                            | some v, some vs => some (v :: vs) | _, _ => none := rfl
                        have he0 : rf.envH.evalArgsOwn [] = some [] := rfl
                        have hvz : rf.envH.evalArgOwn (.var z) = some w0' := by
                          simp [HValEnv.evalArgOwn, hhz]
                        rw [hstep, he0, hvz] at hevh; cases hevh; rfl
                      subst hw0'
                      unfold ValRep at hvr_z
                      simp only [Bool.eq_false_iff.mpr hns_z, Bool.false_eq_true, ↓reduceIte]
                        at hvr_z
                      rcases hvr_z with ⟨bv, rfl, _⟩
                      simp [Word.toBV64?, Word.i64]
                  simp only [HVal.wp, hevh, isPrimName, splitDot, ↓reduceIte,
                    HPrim.wp, hbv_some, panicOobCode]
                  exact hx hxp
      · have hne_oob : (f == "outOfBounds._redArg") = false := by simp [hoob]
        simp only [hne_oob, hfind_f, Bool.false_eq_true, ↓reduceIte] at hpr
        rcases hpr with ⟨hpprim, hprim_m⟩
        cases hpval : primP f pvs with
        | none => simp [hpval] at hprim_m
        | some pv_res =>
          simp only [hpval] at hprim_m
          rcases hprim_m with ⟨hsafe, hK⟩
          cases happ : rf.ctx.applyArgs as borrows with
          | error e =>
            unfold checkVal at hcv
            simp only [hnone, hsig, happ] at hcv
            change Except.error e = Except.ok ctx' at hcv
            cases hcv
          | ok ctx1 =>
            have hlive := applyArgs_var_live hrc.2.1 hcl happ
            have hl_eval : ∀ a ∈ as, match a with
                | .erased => True
                | .var z => ∃ v, rf.ctx.get? z = some v ∧ v.isLive = true := by
              intro a ha
              rcases hlive a ha with rfl | ⟨z, v, rfl, hgz, hlv⟩
              · trivial
              · exact ⟨v, hgz, hlv⟩
            have hevp_rf : rf.envP.evalArgs as = some pvs := by
              rw [← shadowOk_evalArgs_init hsh hinit hl_eval]; exact hevp
            obtain ⟨ws, hevh, _⟩ := evalArgsOwn_sim hrc.2.2.2.1 hl_eval hevp_rf
            have his_prim : isPrimName f = true := hpprim
            have hpm_cond : (f == "Array.propagateMark" || f == "ByteArray.propagateMark" ||
                f == "String.propagateMark") = true →
                ty = .tobject ∨ ∃ y vy, as.getLast? = some (.var y) ∧
                  rf.ctx.get? y = some vy ∧ vy.ty = .object := by
              intro hpm
              simp only [hpm, ↓reduceIte, Bool.or_eq_true, lcTy_beq_iff] at hpm_ty
              rcases hpm_ty with rfl | hm_last
              · left; rfl
              · right
                cases hlst : as.getLast? with
                | none => simp [hlst] at hm_last
                | some al =>
                  cases al with
                  | erased => simp [hlst] at hm_last
                  | var y =>
                    cases hgy : rf.ctx.get? y with
                    | none => simp [hlst, hgy] at hm_last
                    | some vy =>
                      simp only [hlst, hgy, lcTy_beq_iff] at hm_last
                      exact ⟨y, vy, rfl, hgy, hm_last⟩
            simp only [HVal.wp, hevh, his_prim, ↓reduceIte]
            refine primP_sim hrc.2.2.2.1 hpw hprw hpaw hlive hevp_rf hevh hsafe hpval hpm_cond
              (fun {rw} hvr hpost => ?_)
            cases retKind with
            | persistent => exact False.elim (primRcSig_not_persistent hpw hsig)
            | borrowed idx =>
              obtain ⟨hf_arr, _, rfl, rfl⟩ := primRcSig_borrowed_is_arr hpw hsig
              subst hf_arr
              simp only [beq_self_eq_true, ↓reduceIte] at hpost
              rcases hpost with ⟨o_src, bv, ha2, rfl, arrObj, pv_arr, w_arr, hho, rfl, ho_mem, hch⟩
              unfold checkVal at hcv
              simp only [hnone, hsig, happ, ha2, Bind.bind, Except.bind, Pure.pure,
                Except.pure] at hcv
              cases hpb : ctx1.projBacking o_src with
              | error e => rw [hpb] at hcv; cases hcv
              | ok bp =>
                rcases bp with ⟨p?, pers⟩
                rw [hpb] at hcv
                have hctx'_eq : ctx' = ctx1.bindBorrowed x ty p? pers := by
                  cases hcv; rfl
                subst hctx'_eq
                have rc1 := rcInv_applyArgs_step hrc hcl hpo happ hnost
                rcases rc1 with ⟨_, hrc1, hcl1, hpo1⟩
                have hnd1 := applyArgs_nodup hrc.2.1 happ
                have hfr1 := binderFreshOwned_applyArgs hrc.2.1 hcl happ hfr
                have hty_nrc : ty.needsRc = true := by
                  have hsp : splitDot "Array.get!InternalBorrowed" =
                      ["Array", "get!InternalBorrowed"] := rfl
                  unfold perceusPrimRetWf at hprw
                  rw [hsp] at hprw
                  have hty_o : ty = .tobject := (lcTy_beq_iff _ _).mp hprw
                  subst hty_o; rfl
                have hlive_src : ∃ v_src, ctx1.get? o_src = some v_src ∧ v_src.isLive = true := by
                  unfold RcCtx.projBacking at hpb
                  cases hg : ctx1.get? o_src with
                  | none => simp [hg] at hpb
                  | some v_src =>
                    simp only [hg] at hpb
                    split at hpb
                    · simp at hpb
                    · cases hlv : v_src.isLive <;> simp_all
                rcases hlive_src with ⟨v_src, hg_src, hl_src⟩
                obtain ⟨v_src0, hg_src0, _, _, _, hty_src0, _⟩ :=
                  applyArgs_get?_live_back hrc.2.1 hcl happ o_src hg_src hl_src
                have hns_src : ¬v_src.ty.isScalar = true := by
                  have ha2_mem : (.var o_src : LcArg) ∈ as :=
                    (List.getElem?_eq_some_iff.mp ha2).2 ▸
                      List.getElem_mem (List.getElem?_eq_some_iff.mp ha2).1
                  have has4 : as.length = 4 := (primRcSig_len hsig).symm
                  have hall : (as.all fun a => match a with
                      | .erased => true
                      | .var x => match rf.ctx.get? x with
                        | some v => !v.ty.isScalar | none => false) = true := by
                    rcases as with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | _⟩⟩⟩⟩ <;>
                      simp at has4
                    dsimp only [perceusPrimArgsWf, splitDot, uintWidth?] at hpaw
                    exact hpaw
                  have hmem_c := List.all_eq_true.mp hall (.var o_src) ha2_mem
                  simp only [hg_src0] at hmem_c
                  rw [← hty_src0]; simpa using hmem_c
                obtain ⟨_, w_src0, _, hh_src0, _⟩ :=
                  hrc1.2.2.2.1 v_src (RcCtx.get?_mem hg_src).1 hl_src
                rw [(RcCtx.get?_mem hg_src).2, hho] at hh_src0
                cases hh_src0
                have hpcb1 := parentChildBacked_applyArgs hrc.2.1 hcl happ hpcb
                have hno1 := noRcCorrect_applyArgs hrc.2.1 hno as [true, true, true, true] happ
                have hsth1 := sharedTargetsHeap_applyArgs hrc.2.1 hsth happ
                have hsb1 := sharedBool_applyArgs hrc.2.1 hsbv hsbp happ
                have hex1 := exclCtorHeap_applyArgs hrc.2.1 hex happ
                have hsh1 := shadowOk_applyArgs hrc.2.1 hsh happ
                have hsteps := bind_borrowed_step_invs hrc1 hcl1 hpo1 hno1 hpcb1 hsth1 hhih
                  (entryPres_applyArgs hrc.2.1 hcl happ hep) hsb1.2 hex1 hsh1 hfr1 hty_nrc hpb
                  hg_src hns_src hho ho_mem rfl hvr hch
                rcases hsteps with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
                let ctx' := ctx1.bindBorrowed x ty p? pers
                let rf' : RcFrame :=
                  ⟨ctx', rf.envP.set x pv_res, rf.envH.set x ty (Word.i64 bv), rf.extH, rf.ghostH⟩
                have hjsc' : JpsScopeIn
                    ((jpsOk.map fun e => { e with mutVars := x :: e.mutVars }).map
                      JpEntry.info) ctx' := by
                  simp; exact jpsScopeIn_put hnd1 (jpsScopeIn_applyArgs hrc.2.1 happ hjsc)
                have hjok' := jpsOk_let_step (rf' := rf') (ρP' := ρP.set x pv_res) hjok
                  ⟨fun z hz => by
                    change Option.map RcVar.ty ((ctx1.bindBorrowed x ty p? pers).get? z) =
                        Option.map RcVar.ty (rf.ctx.get? z) ∧
                      (Option.map RcVar.isLive ((ctx1.bindBorrowed x ty p? pers).get? z) =
                          some true →
                        Option.map RcVar.isLive (rf.ctx.get? z) = some true)
                    rw [get?_bindBorrowed_ne ctx1 hnd1 hz ty p? pers]
                    exact (applyArgs_ctx_props hrc.2.1 happ).1 z,
                  fun p hp _ => by
                    have hp0 := (applyArgs_ctx_props hrc.2.1 happ).2.1 p hp
                    refine ⟨hp0, ?_⟩
                    unfold binderFreshOwned at hfr
                    simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hfr
                    exact (hfr.1.2 p hp0).2⟩
                  (fun z hz => by simp [rf', PValEnv.set, HValEnv.set, hz]) rfl
                exact hcont (rf' := rf') (ρP' := ρP.set x pv_res) (pv := pv_res) (rw := Word.i64 bv)
                  hK rfl rfl rfl rfl h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
                  (shadowSmWf_filter_ne hsmwf) h12 hres hjsc' hjok' rfl
            | owned =>
              have hctx'_eq : ctx' = ctx1.bindOwned x ty := by
                unfold checkVal at hcv
                simp only [hnone, hsig, happ] at hcv
                change Except.ok (ctx1.bindOwned x ty) = Except.ok ctx' at hcv
                cases hcv; rfl
              subst hctx'_eq
              have hnot_arr : (f == "Array.get!InternalBorrowed") = false := by
                by_cases heq : f = "Array.get!InternalBorrowed"
                · have hsp : splitDot "Array.get!InternalBorrowed" =
                      ["Array", "get!InternalBorrowed"] := rfl
                  unfold primRcSig at hsig
                  rw [heq, hsp] at hsig
                  by_cases h4 : as.length = 4 <;> simp [h4] at hsig
                · simp [heq]
              simp only [hnot_arr, Bool.false_eq_true, ↓reduceIte] at hpost
              have hjsc' : JpsScopeIn ((jpsOk.map fun e => { e with mutVars := x :: e.mutVars }).map
                  JpEntry.info) (ctx1.bindOwned x ty) := by
                simp; exact jpsScopeIn_put (applyArgs_nodup hrc.2.1 happ)
                  (jpsScopeIn_applyArgs hrc.2.1 happ hjsc)
              let rf' : RcFrame :=
                ⟨ctx1.bindOwned x ty, rf.envP.set x pv_res, rf.envH.set x ty rw,
                  rf.extH, rf.ghostH⟩
              have hjok' := jpsOk_let_step (rf' := rf') (ρP' := ρP.set x pv_res) hjok
                (ctx_step_props_applyArgs_bindOwned hrc.2.1 happ hfr ty)
                (fun z hz => by simp [rf', PValEnv.set, HValEnv.set, hz]) rfl
              by_cases hpm : (f == "Array.propagateMark" || f == "ByteArray.propagateMark" ||
                  f == "String.propagateMark") = true
              · simp only [hpm, ↓reduceIte] at hpost
                have hty_nrc : ty.needsRc = true := by
                  unfold perceusPrimRetWf at hprw
                  simp only [Bool.or_eq_true, beq_iff_eq] at hpm
                  rcases hpm with (rfl | rfl) | rfl <;> exact hprw
                cases hlast_a : as.getLast? with
                | none =>
                  cases as with
                  | nil =>
                    have he0 : rf.envH.evalArgsOwn [] = some [] := rfl
                    rw [he0] at hevh; cases hevh
                    simp at hpost
                  | cons hd tl => simp [List.getLast?] at hlast_a
                | some a_last =>
                  have hev_last := evalArgsOwn_getLast? hevh hlast_a hpost
                  cases a_last with
                  | erased =>
                    have hrw : rw = Word.i64 1#64 := by
                      change some (Word.i64 1#64) = some rw at hev_last
                      cases hev_last; rfl
                    subst hrw
                    have rc1 := rcInv_applyArgs_step hrc hcl hpo happ hnost
                    have hsteps := bind_nonPtr_step_invs rc1.2.1 rc1.2.2.1 rc1.2.2.2
                      (noRcCorrect_applyArgs hrc.2.1 hno as borrows happ)
                      (parentChildBacked_applyArgs hrc.2.1 hcl happ hpcb)
                      (sharedTargetsHeap_applyArgs hrc.2.1 hsth happ) hhih
                      (entryPres_applyArgs hrc.2.1 hcl happ hep)
                      (sharedBool_applyArgs hrc.2.1 hsbv hsbp happ).2
                      (exclCtorHeap_applyArgs hrc.2.1 hex happ)
                      (shadowOk_applyArgs hrc.2.1 hsh happ)
                      (binderFreshOwned_applyArgs hrc.2.1 hcl happ hfr)
                      hvr (fun _ => ⟨1#64, rfl, by decide⟩)
                    rcases hsteps with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
                    exact hcont (rf' := rf') (ρP' := ρP.set x pv_res) (pv := pv_res)
                      (rw := Word.i64 1#64) hK rfl rfl rfl rfl h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
                      (shadowSmWf_filter_ne hsmwf) h12 hres hjsc' hjok' rfl
                  | var y =>
                    have hmem_last : (.var y : LcArg) ∈ as := List.mem_of_getLast? hlast_a
                    rcases hlive (.var y) hmem_last with h_abs | ⟨z, vy, heq_y, hgety, hlive_y⟩
                    · cases h_abs
                    · cases heq_y
                      have hsig_pm := propagateMark_sig_args hpw hsig hpaw hpm
                      have hns_y : ¬vy.ty.isScalar = true := by
                        have := List.all_eq_true.mp hsig_pm.2 (.var y) hmem_last
                        simpa [hgety] using this
                      obtain ⟨_, w_y, _, hhy, hvr_y, _⟩ :=
                        hrc.2.2.2.1 vy (RcCtx.get?_mem hgety).1 hlive_y
                      rw [(RcCtx.get?_mem hgety).2] at hhy
                      have hw_eq : w_y = rw := by
                        simpa [HValEnv.evalArgOwn, hhy] using hev_last
                      subst hw_eq
                      unfold ValRep at hvr_y
                      simp only [Bool.eq_false_iff.mpr hns_y, Bool.false_eq_true, ↓reduceIte]
                        at hvr_y
                      rcases hvr_y with ⟨bv, rfl, _⟩
                      by_cases hev_bv : bv &&& 1#64 = 0#64
                      · have hlast_b : borrows.getLast? = some false := hsig_pm.1
                        have hsteps := propagateMark_step_invs hrc hcl hpo hno hpcb hsth hhih hep
                          hsbv hsbp hex hsh hfr happ hnost hty_nrc hgety hlive_y hns_y
                          (primRcSig_len hsig).symm hlast_a hlast_b hhy hev_bv hvr
                        rcases hsteps with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
                        exact hcont (rf' := rf') (ρP' := ρP.set x pv_res) (pv := pv_res)
                          (rw := Word.i64 bv) hK rfl rfl rfl rfl h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
                          (shadowSmWf_filter_ne hsmwf) h12 hres hjsc' hjok' rfl
                      · have rc1 := rcInv_applyArgs_step hrc hcl hpo happ hnost
                        have hsteps := bind_nonPtr_step_invs rc1.2.1 rc1.2.2.1 rc1.2.2.2
                          (noRcCorrect_applyArgs hrc.2.1 hno as borrows happ)
                          (parentChildBacked_applyArgs hrc.2.1 hcl happ hpcb)
                          (sharedTargetsHeap_applyArgs hrc.2.1 hsth happ) hhih
                          (entryPres_applyArgs hrc.2.1 hcl happ hep)
                          (sharedBool_applyArgs hrc.2.1 hsbv hsbp happ).2
                          (exclCtorHeap_applyArgs hrc.2.1 hex happ)
                          (shadowOk_applyArgs hrc.2.1 hsh happ)
                          (binderFreshOwned_applyArgs hrc.2.1 hcl happ hfr)
                          hvr (fun _ => ⟨bv, rfl, hev_bv⟩)
                        rcases hsteps with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
                        exact hcont (rf' := rf') (ρP' := ρP.set x pv_res) (pv := pv_res)
                          (rw := Word.i64 bv) hK rfl rfl rfl rfl h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
                          (shadowSmWf_filter_ne hsmwf) h12 hres hjsc' hjok' rfl
              · simp only [hpm, Bool.false_eq_true, ↓reduceIte] at hpost
                have rc1 := rcInv_applyArgs_step hrc hcl hpo happ hnost
                have hsteps := bind_nonPtr_step_invs rc1.2.1 rc1.2.2.1 rc1.2.2.2
                  (noRcCorrect_applyArgs hrc.2.1 hno as borrows happ)
                  (parentChildBacked_applyArgs hrc.2.1 hcl happ hpcb)
                  (sharedTargetsHeap_applyArgs hrc.2.1 hsth happ) hhih
                  (entryPres_applyArgs hrc.2.1 hcl happ hep)
                  (sharedBool_applyArgs hrc.2.1 hsbv hsbp happ).2
                  (exclCtorHeap_applyArgs hrc.2.1 hex happ)
                  (shadowOk_applyArgs hrc.2.1 hsh happ)
                  (binderFreshOwned_applyArgs hrc.2.1 hcl happ hfr)
                  hvr hpost
                rcases hsteps with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
                exact hcont (rf' := rf') (ρP' := ρP.set x pv_res) (pv := pv_res) (rw := rw)
                  hK rfl rfl rfl rfl h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
                  (shadowSmWf_filter_ne hsmwf) h12 hres hjsc' hjok' rfl
