module

public import LeanQbe.T.LeanLCNF.Sem.PerceusDel
import LeanQbe.T.Logic.ProofKit

/-!
# LCNF Perceus-Sound Simulation: Mutable Field & Tag Steps

Invariant preservation and stepwise simulation lemmas for `LcCode.oset`, `LcCode.uset`,
`LcCode.sset`, and `LcCode.setTag`, plus the scalar initialization mask invariant `ShadowOk`,
`SharedBoolVars`, and `ExclCtorHeap`.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

section MutHelpers

/-- Every `isShared` boolean predicate variable (`p.1` in `ctx.sharedPreds`) has `noRc = true`. -/
@[expose] public def SharedBoolVars (ctx : RcCtx) : Prop :=
  ∀ p ∈ ctx.sharedPreds, ∀ vb, ctx.get? p.1 = some vb → vb.noRc = true

/-- Every live exclusive non-scalar non-persistent `.ctor` in `rf.envP` is an even heap pointer
    in `rf.envH`. -/
@[expose] public def ExclCtorHeap (rf : RcFrame) : Prop :=
  ∀ v ∈ rf.ctx.vars, v.isLive = true → v.excl = true → v.noRc = false →
    v.persistent = false → ∀ cidx fs sc, rf.envP v.id = some (.ctor cidx fs sc) →
      ∃ bv, rf.envH v.id = some (v.ty, .i64 bv) ∧ bv &&& 1#64 = 0#64

/-- Well-formedness of the partial scalar-initialization shadow mask `sm`: unique variable keys. -/
@[expose] public def ShadowSmWf (sm : List (Nat × Nat × List Bool)) : Prop :=
  (sm.map Prod.fst).Nodup

/-- Agreement between pure `ρP` and shadow `envP`: variables whose scalar slots are fully
    initialized agree identically, while variables still in `sm` agree on constructor tag, object
    fields, total byte length, and all scalar bytes marked initialized in `sm`. -/
@[expose] public def ShadowOk (sm : List (Nat × Nat × List Bool)) (ctx : RcCtx)
    (ρP envP : PValEnv) : Prop :=
  ∀ v ∈ ctx.vars, v.isLive = true →
    if isVarScalarInit sm v.id then ρP v.id = envP v.id
    else
      ∃ sz m, sm.find? (·.1 == v.id) = some (v.id, sz, m) ∧
        ∃ cidx fs pscal hscal,
          ρP v.id = some (.ctor cidx fs pscal) ∧
          envP v.id = some (.ctor cidx fs hscal) ∧
          pscal.length = m.length ∧ hscal.length = m.length ∧ fs.length = sz ∧
          ∀ i, i < m.length → m[i]! = true → pscal[i]? = hscal[i]?

public theorem sharedBoolVars_consumeVar {ctx ctx1 : RcCtx} {x n : Nat}
    (hnd : (ctx.vars.map RcVar.id).Nodup) (hsbv : SharedBoolVars ctx)
    (hcons : ctx.consumeVar x n = .ok ctx1) : SharedBoolVars ctx1 := by
  intro p hp vb hgb
  have hps : p ∈ ctx.sharedPreds := by
    have hsp := consumeVar_sharedPreds_sub hcons
    exact hsp p hp
  have hflg := consumeVar_preserves_flags hnd hcons p.1
  rw [hgb] at hflg
  cases hg0 : ctx.get? p.1 with
  | none => rw [hg0] at hflg; cases hflg
  | some vb0 =>
    rw [hg0] at hflg
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hflg
    exact hflg.1 ▸ hsbv p hps vb0 hg0

public theorem sharedBoolVars_consumeArg {ctx ctx1 : RcCtx} {y : LcArg}
    (hnd : (ctx.vars.map RcVar.id).Nodup) (hsbv : SharedBoolVars ctx)
    (hcons : ctx.consumeArg y = .ok ctx1) : SharedBoolVars ctx1 := by
  cases y with
  | erased => simp [RcCtx.consumeArg, pure, Except.pure] at hcons; subst hcons; exact hsbv
  | var _ => exact sharedBoolVars_consumeVar hnd hsbv hcons

public theorem shadowSmWf_filter {sm : List (Nat × Nat × List Bool)}
    (hsm : ShadowSmWf sm) (x : Nat) : ShadowSmWf (sm.filter (·.1 != x)) := by
  have hsub : ((sm.filter (·.1 != x)).map Prod.fst).Sublist (sm.map Prod.fst) :=
    (List.filter_sublist).map Prod.fst
  exact hsm.sublist hsub

public theorem shadowSmWf_ctorBindMask {sm : List (Nat × Nat × List Bool)}
    (hsm : ShadowSmWf sm) (x : Nat) (ci : LcCtor) : ShadowSmWf (ctorBindMask x ci sm) := by
  unfold ctorBindMask
  by_cases hc : !ci.isScalar && 0 < 8 * ci.usize + ci.ssize
  · simp only [hc, ite_true, ShadowSmWf, List.map_cons, List.nodup_cons]
    refine ⟨?_, shadowSmWf_filter hsm x⟩
    intro hm
    rcases List.mem_map.mp hm with ⟨e, he, rfl⟩
    rw [List.mem_filter] at he
    simp at he
  · simp only [hc]
    exact shadowSmWf_filter hsm x

private theorem filterMap_fst_sublist {α : Type}
    (sm : List (Nat × α)) (f : Nat × α → Option (Nat × α))
    (hf : ∀ e e', f e = some e' → e'.1 = e.1) :
    ((sm.filterMap f).map Prod.fst).Sublist (sm.map Prod.fst) := by
  induction sm with
  | nil => simp
  | cons a rest ih =>
    simp only [List.filterMap_cons, List.map_cons]
    cases ha : f a with
    | none => exact List.Sublist.cons _ ih
    | some a' =>
      simp only [List.map_cons]
      rw [hf a a' ha]
      exact List.Sublist.cons_cons _ ih

public theorem shadowSmWf_initScalarBytes {sm : List (Nat × Nat × List Bool)}
    (hsm : ShadowSmWf sm) (x n off nb : Nat) :
    ShadowSmWf (initScalarBytes sm x n off nb) := by
  unfold ShadowSmWf initScalarBytes
  let f : Nat × Nat × List Bool → Option (Nat × Nat × List Bool) := fun e =>
    let (k, sz, m) := e
    if k == x then
      let m' := setBytesTrue m (8 * (n - sz) + off) nb
      if m'.all id then none else some (k, sz, m')
    else some (k, sz, m)
  have hsub := filterMap_fst_sublist sm f (fun ⟨k, sz, m⟩ e' h => by
    dsimp only [f] at h
    by_cases hkx : (k == x) = true
    · simp only [hkx, ite_true] at h
      by_cases hall : (setBytesTrue m (8 * (n - sz) + off) nb).all id = true
      · simp [hall] at h
      · simp [hall] at h; cases h; rfl
    · simp [hkx] at h; cases h; rfl)
  exact hsm.sublist hsub

public theorem isVarScalarInit_iff_find_none {sm : List (Nat × Nat × List Bool)} (x : Nat) :
    isVarScalarInit sm x = true ↔ sm.find? (·.1 == x) = none := by
  simp only [isVarScalarInit, List.all_eq_true, List.find?_eq_none, bne_iff_ne, ne_eq,
    beq_iff_eq]

public theorem find_some_mem {α : Type} {xs : List α} {p : α → Bool} {a : α}
    (h : xs.find? p = some a) : a ∈ xs ∧ p a = true := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.find?_cons] at h
    cases hp : p x with
    | true =>
      simp only [hp] at h; cases h
      exact ⟨List.mem_cons_self, hp⟩
    | false =>
      simp only [hp] at h
      obtain ⟨hm, hpa⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hm, hpa⟩

public theorem find_eq_some_of_mem_nodup {sm : List (Nat × Nat × List Bool)}
    (hsm : ShadowSmWf sm) {x sz : Nat} {m : List Bool} (hm : (x, sz, m) ∈ sm) :
    sm.find? (·.1 == x) = some (x, sz, m) := by
  induction sm with
  | nil => cases hm
  | cons e rest ih =>
    simp only [ShadowSmWf, List.map_cons, List.nodup_cons] at hsm
    simp only [List.find?_cons]
    rcases List.mem_cons.mp hm with rfl | hmem
    · simp
    · have hne : (e.1 == x) = false := by
        apply beq_false_of_ne
        intro heq
        apply hsm.1
        rw [heq]
        exact List.mem_map.mpr ⟨(x, sz, m), hmem, rfl⟩
      simp only [hne]
      exact ih hsm.2 hmem

public theorem isVarScalarInit_filter_eq {sm : List (Nat × Nat × List Bool)}
    (x y : Nat) (hne : y ≠ x) :
    isVarScalarInit (sm.filter (·.1 != x)) y = isVarScalarInit sm y := by
  apply Bool.eq_iff_iff.mpr
  simp only [isVarScalarInit, List.all_eq_true, List.mem_filter, bne_iff_ne, ne_eq, and_imp]
  constructor
  · intro h e hm
    by_cases hx : e.1 = x
    · rw [hx]; exact hne.symm
    · exact h e hm hx
  · intro h e hm _; exact h e hm

public theorem find_filter_eq_of_ne {sm : List (Nat × Nat × List Bool)}
    (x y : Nat) (hne : y ≠ x) :
    (sm.filter (·.1 != x)).find? (·.1 == y) = sm.find? (·.1 == y) := by
  induction sm with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.filter_cons]
    by_cases hex : (e.1 != x) = true
    · simp only [hex, ite_true, List.find?_cons]
      cases h : (e.1 == y) <;> simp [ih]
    · have hex_eq : e.1 = x := by cases h : (e.1 == x) <;> simp_all
      have hne_y : (e.1 == y) = false := beq_false_of_ne (hex_eq ▸ hne.symm)
      simp only [hex, List.find?_cons, hne_y]
      exact ih

public theorem setBytesTrue_length (m : List Bool) (bOff nb : Nat) :
    (setBytesTrue m bOff nb).length = m.length := by
  simp [setBytesTrue]

public theorem setBytesTrue_getElem {m : List Bool} {bOff nb k : Nat} (hk : k < m.length) :
    (setBytesTrue m bOff nb)[k]'(by simp [setBytesTrue_length, hk]) =
      if bOff ≤ k ∧ k < bOff + nb then true else m[k] := by
  unfold setBytesTrue
  simp only [List.getElem_ofFn, Bool.and_eq_true, decide_eq_true_eq]
  split <;> rfl

public theorem writeBytesAt_getElem {bs patch : List UInt8} {bOff k : Nat}
    (hbd : bOff + patch.length ≤ bs.length) (hk : k < bs.length) :
    (writeBytesAt bs bOff patch)[k]'(by rw [writeBytesAt_length hbd]; exact hk) =
      if h : bOff ≤ k ∧ k < bOff + patch.length then patch[k - bOff]'(by omega)
      else bs[k] := by
  have hlt1 : (bs.take bOff).length = bOff := by simp; omega
  have hlt2 : (bs.take bOff ++ patch).length = bOff + patch.length := by simp [hlt1]
  have hlt3 : (bs.take bOff ++ patch ++ bs.drop (bOff + patch.length)).length = bs.length := by
    rw [← writeBytesAt]; exact writeBytesAt_length hbd
  have heq : (writeBytesAt bs bOff patch)[k]'(by rw [writeBytesAt_length hbd]; exact hk) =
      (bs.take bOff ++ patch ++ bs.drop (bOff + patch.length))[k]'(hlt3.symm ▸ hk) := rfl
  rw [heq]
  by_cases h1 : k < bOff
  · have hnot : ¬(bOff ≤ k ∧ k < bOff + patch.length) := by omega
    split
    · contradiction
    · rw [List.getElem_append_left (by simp [hlt2]; omega),
        List.getElem_append_left (by simp [hlt1]; omega), List.getElem_take]
  · by_cases h2 : k < bOff + patch.length
    · have hok : bOff ≤ k ∧ k < bOff + patch.length := by omega
      split
      · rw [List.getElem_append_left (by simp [hlt2]; omega),
          List.getElem_append_right (by simp [hlt1]; omega)]
        simp [hlt1]
      · contradiction
    · have hnot : ¬(bOff ≤ k ∧ k < bOff + patch.length) := by omega
      split
      · contradiction
      · rw [List.getElem_append_right (by simp [hlt2]; omega), List.getElem_drop]
        congr 1; rw [hlt2]; omega

public theorem initScalarBytes_lookup_ne {sm : List (Nat × Nat × List Bool)}
    {x y n off nb : Nat} (hne : y ≠ x) :
    (initScalarBytes sm x n off nb).find? (·.1 == y) = sm.find? (·.1 == y) := by
  unfold initScalarBytes
  induction sm with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨k, sz, m⟩
    simp only [List.filterMap_cons]
    by_cases hkx : k = x
    · subst hkx
      have hky : (k == y) = false := beq_false_of_ne hne.symm
      simp only [beq_self_eq_true, ite_true]
      by_cases hall : (setBytesTrue m (8 * (n - sz) + off) nb).all id = true
      · simp only [hall, ite_true, List.find?_cons, hky, ih]
      · have hf : (setBytesTrue m (8 * (n - sz) + off) nb).all id = false := by
          cases hc : (setBytesTrue m (8 * (n - sz) + off) nb).all id <;> simp_all
        simp only [hf, Bool.false_eq_true, ite_false, List.find?_cons, hky, ih]
    · have hkx_b : (k == x) = false := beq_false_of_ne hkx
      simp only [hkx_b, Bool.false_eq_true, ite_false, List.find?_cons]
      cases h : (k == y) <;> simp only [ih]

public theorem isVarScalarInit_initScalarBytes_ne {sm : List (Nat × Nat × List Bool)}
    {x y n off nb : Nat} (hne : y ≠ x) :
    isVarScalarInit (initScalarBytes sm x n off nb) y = isVarScalarInit sm y := by
  by_cases h : isVarScalarInit sm y = true
  · rw [h, isVarScalarInit_iff_find_none, initScalarBytes_lookup_ne hne,
      ← isVarScalarInit_iff_find_none]; exact h
  · have hf : isVarScalarInit sm y = false := by cases hc : isVarScalarInit sm y <;> simp_all
    rw [hf]
    cases h' : isVarScalarInit (initScalarBytes sm x n off nb) y
    · rfl
    · exfalso
      rw [isVarScalarInit_iff_find_none, initScalarBytes_lookup_ne hne,
        ← isVarScalarInit_iff_find_none] at h'
      rw [h'] at hf; cases hf

private theorem initScalarBytes_none_of_none {sm : List (Nat × Nat × List Bool)}
    {x n off nb : Nat} (hnone : sm.find? (·.1 == x) = none) :
    (initScalarBytes sm x n off nb).find? (·.1 == x) = none := by
  induction sm with
  | nil => simp [initScalarBytes]
  | cons e rest ih =>
    rcases e with ⟨k, sz, m⟩
    simp only [List.find?_cons] at hnone
    cases hkx : k == x
    · simp only [hkx] at hnone
      simp only [initScalarBytes, List.filterMap_cons, hkx, Bool.false_eq_true, ite_false,
        List.find?_cons]
      exact ih hnone
    · simp only [hkx] at hnone; cases hnone

private theorem initScalarBytes_some_eq {sm : List (Nat × Nat × List Bool)}
    (hsm : ShadowSmWf sm) {x sz : Nat} {m : List Bool} {n off nb : Nat}
    (hsome : sm.find? (·.1 == x) = some (x, sz, m)) :
    let m' := setBytesTrue m (8 * (n - sz) + off) nb
    (initScalarBytes sm x n off nb).find? (·.1 == x) =
      if m'.all id then none else some (x, sz, m') := by
  intro m'
  induction sm with
  | nil => simp at hsome
  | cons e rest ih =>
    rcases e with ⟨k, szo, mo⟩
    simp only [ShadowSmWf, List.map_cons, List.nodup_cons] at hsm
    simp only [List.find?_cons] at hsome
    cases hkx : k == x
    · simp only [hkx] at hsome
      simp only [initScalarBytes, List.filterMap_cons, hkx, Bool.false_eq_true, ite_false,
        List.find?_cons]
      exact ih hsm.2 hsome
    · simp only [hkx] at hsome; cases hsome
      simp only [initScalarBytes, List.filterMap_cons, beq_self_eq_true, ite_true]
      by_cases hall : m'.all id = true
      · have hall' : (setBytesTrue m (8 * (n - sz) + off) nb).all id = true := hall
        simp only [m', hall', ite_true]
        apply initScalarBytes_none_of_none
        rw [List.find?_eq_none]
        intro q hqm heq
        apply hsm.1
        rw [← beq_iff_eq.mp heq]
        exact List.mem_map.mpr ⟨q, hqm, rfl⟩
      · have hall_f : (setBytesTrue m (8 * (n - sz) + off) nb).all id = false := by
          cases h : (setBytesTrue m (8 * (n - sz) + off) nb).all id <;> simp_all [m']
        simp only [m', hall_f, Bool.false_eq_true, ite_false, List.find?_cons, beq_self_eq_true]

public theorem shadowOk_evalArg {sm : List (Nat × Nat × List Bool)} {ctx : RcCtx}
    {ρP envP : PValEnv} (hshd : ShadowOk sm ctx ρP envP)
    {a : LcArg} (hinit : argScalarInit sm a = true)
    (hlive : match a with
      | .erased => True
      | .var y => ∃ v ∈ ctx.vars, v.id = y ∧ v.isLive = true) :
    ρP.evalArg a = envP.evalArg a := by
  cases a with
  | erased => rfl
  | var y =>
    obtain ⟨v, hv, rfl, hvl⟩ := hlive
    have hs := hshd v hv hvl
    simp only [argScalarInit] at hinit
    simp only [hinit, ite_true] at hs
    simp [PValEnv.evalArg, hs]

public theorem shadowOk_consumeVar {sm : List (Nat × Nat × List Bool)} {ctx ctx1 : RcCtx}
    {ρP envP : PValEnv} {x n : Nat} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hclean : CleanVars ctx) (hcons : ctx.consumeVar x n = .ok ctx1)
    (hshd : ShadowOk sm ctx ρP envP) :
    ShadowOk sm ctx1 ρP envP := by
  intro u hu hulive
  have hnd1 := consumeVar_nodup hnd hcons
  have hgu : ctx1.get? u.id = some u := rcCtx_get?_of_mem hnd1 hu
  obtain ⟨w0, hw0, hw0_live, _⟩ := consumeVar_get?_live_back hnd hclean hcons u.id hgu hulive
  obtain ⟨hw0_m, hw0_id⟩ := RcCtx.get?_mem hw0
  have h := hshd w0 hw0_m hw0_live
  rwa [hw0_id] at h

public theorem shadowOk_consumeArg {sm : List (Nat × Nat × List Bool)} {ctx ctx1 : RcCtx}
    {ρP envP : PValEnv} {y : LcArg} (hnd : (ctx.vars.map RcVar.id).Nodup)
    (hclean : CleanVars ctx) (hcons : ctx.consumeArg y = .ok ctx1)
    (hshd : ShadowOk sm ctx ρP envP) :
    ShadowOk sm ctx1 ρP envP := by
  cases y with
  | erased => simp [RcCtx.consumeArg, pure, Except.pure] at hcons; subst hcons; exact hshd
  | var _ => exact shadowOk_consumeVar hnd hclean hcons hshd

public theorem shadowOk_update_same_shape {sm : List (Nat × Nat × List Bool)} {ctx : RcCtx}
    {ρP envP : PValEnv} (hshd : ShadowOk sm ctx ρP envP)
    {x : Nat} {pvρ pvE : PVal}
    (hinit : isVarScalarInit sm x = true → pvρ = pvE)
    (hmask : ∀ sz m, sm.find? (·.1 == x) = some (x, sz, m) →
      ∃ cidx fs pscal hscal,
        pvρ = .ctor cidx fs pscal ∧ pvE = .ctor cidx fs hscal ∧
        pscal.length = m.length ∧ hscal.length = m.length ∧ fs.length = sz ∧
        ∀ i, i < m.length → m[i]! = true → pscal[i]? = hscal[i]?) :
    ShadowOk sm ctx (ρP.set x pvρ) (envP.set x pvE) := by
  intro u hu hulive
  by_cases hux : u.id = x
  · rw [hux]
    cases hi : isVarScalarInit sm x
    · simp only [Bool.false_eq_true, ite_false]
      have hfind : sm.find? (·.1 == x) ≠ none := fun hnone => by
        rw [← isVarScalarInit_iff_find_none] at hnone; rw [hi] at hnone; cases hnone
      obtain ⟨⟨k, sz, m⟩, hf⟩ := Option.ne_none_iff_exists'.mp hfind
      have ⟨_, hkeq⟩ := find_some_mem hf
      have hk : k = x := beq_iff_eq.mp hkeq
      subst hk
      obtain ⟨cidx, fs, pscal, hscal, hp1, hp2, hl1, hl2, hsz, hbs⟩ := hmask sz m hf
      exact ⟨sz, m, hf, cidx, fs, pscal, hscal,
        by simp [PValEnv.set, hp1], by simp [PValEnv.set, hp2], hl1, hl2, hsz, hbs⟩
    · simp only [ite_true, PValEnv.set]
      exact congrArg some (hinit hi)
  · have h := hshd u hu hulive
    simpa [PValEnv.set, hux] using h

public theorem shadowOk_update_scalarBytes {sm : List (Nat × Nat × List Bool)} {ctx : RcCtx}
    {ρP envP : PValEnv} (hsm : ShadowSmWf sm) (hshd : ShadowOk sm ctx ρP envP)
    {x n off : Nat} {patch : List UInt8}
    {vx : RcVar} (hget : ctx.get? x = some vx) (hlive : vx.isLive = true)
    {cidx : Nat} {fs : List PVal} {pscal hscal : List UInt8}
    (hρ : ρP x = some (.ctor cidx fs pscal)) (hE : envP x = some (.ctor cidx fs hscal))
    (hbdP : 8 * (n - fs.length) + off + patch.length ≤ pscal.length)
    (hbdH : 8 * (n - fs.length) + off + patch.length ≤ hscal.length) :
    let bOff := 8 * (n - fs.length) + off
    let sm' := initScalarBytes sm x n off patch.length
    ShadowOk sm' ctx
      (ρP.set x (.ctor cidx fs (writeBytesAt pscal bOff patch)))
      (envP.set x (.ctor cidx fs (writeBytesAt hscal bOff patch))) := by
  intro bOff sm' u hu hulive
  by_cases hux : u.id = x
  · rw [hux]
    obtain ⟨hvm, hxid⟩ := RcCtx.get?_mem hget
    have hx := hshd vx hvm hlive
    rw [hxid] at hx
    cases hi : isVarScalarInit sm x
    · simp only [hi, Bool.false_eq_true, ite_false] at hx
      obtain ⟨sz, m, hfind, c0, fs0, ps0, hs0, hρ0, hE0, hlP, hlH, hfs, hagree⟩ := hx
      rw [hρ] at hρ0; cases hρ0
      rw [hE] at hE0; cases hE0
      have hfind' := initScalarBytes_some_eq hsm (n := n) (off := off) (nb := patch.length) hfind
      dsimp only at hfind'
      let m' := setBytesTrue m bOff patch.length
      have hfind'' : sm'.find? (·.1 == x) = if m'.all id then none else some (x, sz, m') := by
        simpa [sm', m', bOff, hfs] using hfind'
      have hlP' : (writeBytesAt pscal bOff patch).length = m'.length := by
        rw [writeBytesAt_length hbdP, setBytesTrue_length, hlP]
      have hlH' : (writeBytesAt hscal bOff patch).length = m'.length := by
        rw [writeBytesAt_length hbdH, setBytesTrue_length, hlH]
      have hagree' : ∀ i, i < m'.length → m'[i]! = true →
          (writeBytesAt pscal bOff patch)[i]? = (writeBytesAt hscal bOff patch)[i]? := by
        intro i him hmi
        have him_m : i < m.length := by rwa [setBytesTrue_length] at him
        have hmget := setBytesTrue_getElem (bOff := bOff) (nb := patch.length) him_m
        have hmi' : m'[i] = true := by simpa [getElem!_pos, him] using hmi
        have hikP : i < pscal.length := hlP ▸ him_m
        have hikH : i < hscal.length := hlH ▸ him_m
        have hkP : i < (writeBytesAt pscal bOff patch).length := by
          rw [writeBytesAt_length hbdP]; exact hikP
        have hkH : i < (writeBytesAt hscal bOff patch).length := by
          rw [writeBytesAt_length hbdH]; exact hikH
        rw [List.getElem?_eq_getElem hkP, List.getElem?_eq_getElem hkH]
        rw [writeBytesAt_getElem hbdP hikP, writeBytesAt_getElem hbdH hikH]
        by_cases hin : bOff ≤ i ∧ i < bOff + patch.length
        · split
          · rfl
          · contradiction
        · split
          · contradiction
          · simp only [m', hmget, hin, ite_false] at hmi'
            have hagr := hagree i him_m (by simpa [getElem!_pos, him_m] using hmi')
            rw [List.getElem?_eq_getElem hikP, List.getElem?_eq_getElem hikH] at hagr
            exact hagr
      by_cases hall : m'.all id = true
      · simp only [hall, ite_true] at hfind''
        have hinit' : isVarScalarInit sm' x = true :=
          (isVarScalarInit_iff_find_none x).mpr hfind''
        simp only [hinit', ite_true, PValEnv.set]
        have heq_sc : writeBytesAt pscal bOff patch = writeBytesAt hscal bOff patch := by
          apply List.ext_getElem (hlP'.trans hlH'.symm)
          intro i hi1 hi2
          have him : i < m'.length := hlP' ▸ hi1
          have hall_i : m'[i]! = true := by
            have := List.all_eq_true.mp hall (m'[i]) (List.getElem_mem him)
            simpa [getElem!_pos, him] using this
          have hq := hagree' i him hall_i
          rw [List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2] at hq
          exact Option.some.inj hq
        rw [heq_sc]
      · have hinit' : isVarScalarInit sm' x = false := by
          by_cases ht : isVarScalarInit sm' x = true
          · rw [isVarScalarInit_iff_find_none, hfind''] at ht
            simp only [hall] at ht; cases ht
          · cases h : isVarScalarInit sm' x <;> simp_all
        simp only [hinit', Bool.false_eq_true, ite_false]
        have hfind''' : sm'.find? (·.1 == x) = some (x, sz, m') := by
          simpa [hall] using hfind''
        exact ⟨sz, m', hfind''', cidx, fs, writeBytesAt pscal bOff patch,
          writeBytesAt hscal bOff patch, by simp [PValEnv.set], by simp [PValEnv.set],
          hlP', hlH', hfs, hagree'⟩
    · simp only [hi, ite_true] at hx
      rw [hρ] at hx; rw [hE] at hx; cases hx
      have hnone : sm.find? (·.1 == x) = none := (isVarScalarInit_iff_find_none x).mp hi
      have hnone' := initScalarBytes_none_of_none (n := n) (off := off) (nb := patch.length) hnone
      have hi' : isVarScalarInit sm' x = true := (isVarScalarInit_iff_find_none x).mpr hnone'
      simp [hi', PValEnv.set]
  · have h := hshd u hu hulive
    rw [isVarScalarInit_initScalarBytes_ne hux, initScalarBytes_lookup_ne hux]
    simpa [PValEnv.set, hux] using h

public theorem exclCtorHeap_consumeVar {rf : RcFrame} {ctx1 : RcCtx} {x n : Nat}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup) (hclean : CleanVars rf.ctx)
    (hcons : rf.ctx.consumeVar x n = .ok ctx1) (hexcl : ExclCtorHeap rf) :
    ExclCtorHeap { rf with ctx := ctx1 } := by
  intro u hu hul hexu hnou hpersu cidx fs sc hpu
  have hnd1 := consumeVar_nodup hnd hcons
  have hgu := rcCtx_get?_of_mem hnd1 hu
  obtain ⟨w0, hw0, hw0_live, hw0_no, hw0_pers, hw0_ty, _, _, hw0_ex⟩ :=
    consumeVar_get?_live_back hnd hclean hcons u.id hgu hul
  have hw0_id : w0.id = u.id := (RcCtx.get?_mem hw0).2
  obtain ⟨bv, hbv, hev⟩ := hexcl w0 (RcCtx.get?_mem hw0).1 hw0_live (hw0_ex hexu).1
    (hw0_no ▸ hnou) (hw0_pers ▸ hpersu) cidx fs sc (hw0_id ▸ hpu)
  exact ⟨bv, hw0_id ▸ hw0_ty ▸ hbv, hev⟩

public theorem exclCtorHeap_consumeArg {rf : RcFrame} {ctx1 : RcCtx} {y : LcArg}
    (hnd : (rf.ctx.vars.map RcVar.id).Nodup) (hclean : CleanVars rf.ctx)
    (hcons : rf.ctx.consumeArg y = .ok ctx1) (hexcl : ExclCtorHeap rf) :
    ExclCtorHeap { rf with ctx := ctx1 } := by
  cases y with
  | erased => simp [RcCtx.consumeArg, pure, Except.pure] at hcons; subst hcons; exact hexcl
  | var _ => exact exclCtorHeap_consumeVar hnd hclean hcons hexcl

end MutHelpers

section MutObjWf

private theorem tag_le_244_ne_special {t : Nat} (ht : t ≤ 244) :
    t ≠ closureTag ∧ t ≠ arrayTag ∧ t ≠ sarrayTag ∧ t ≠ stringTag ∧ t ≠ mpzTag := by
  simp only [closureTag, arrayTag, sarrayTag, stringTag, mpzTag]
  omega

public theorem lcnfObj_wf_set_fields {o : LcnfObj} (hwf : o.Wf) (ht : o.tag ≤ 244)
    {i : Nat} (_hi : i < o.fields.length) (yv : BitVec 64) :
    ({ o with fields := o.fields.set i yv } : LcnfObj).Wf := by
  rcases hwf with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hrest⟩
  have ⟨hc, ha, hsa, hst, hmp⟩ := tag_le_244_ne_special ht
  have htot : ({ o with fields := o.fields.set i yv } : LcnfObj).totalBytes = o.totalBytes := by
    simp [LcnfObj.totalBytes, ha, hsa, hst, hmp]
  simp only [hc, ha, hsa, hst, hmp, ite_false] at hrest
  refine ⟨h1, h2, h3, h4, h5, h6, htot ▸ h7, htot ▸ h8, htot ▸ h9, ?_⟩
  simp [hc, ha, hsa, hst, hmp, ht, hrest]
  omega

public theorem lcnfObj_wf_set_scalar {o : LcnfObj} (hwf : o.Wf) (ht : o.tag ≤ 244)
    {scal' : List UInt8} (hlen : scal'.length = o.scalarData.length) :
    ({ o with scalarData := scal' } : LcnfObj).Wf := by
  rcases hwf with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hrest⟩
  have ⟨hc, ha, hsa, hst, hmp⟩ := tag_le_244_ne_special ht
  have htot : ({ o with scalarData := scal' } : LcnfObj).totalBytes = o.totalBytes := by
    simp [LcnfObj.totalBytes, ha, hsa, hst, hmp]
  simp only [hc, ha, hsa, hst, hmp, ite_false] at hrest
  refine ⟨h1, h2, h3, h4, h5, h6, htot ▸ h7, htot ▸ h8, htot ▸ h9, ?_⟩
  simp [hc, ha, hsa, hst, hmp, hlen, ht, hrest]
  omega

public theorem lcnfObj_wf_set_tag {o : LcnfObj} (hwf : o.Wf) (ht : o.tag ≤ 244)
    {cidx : Nat} (hcidx : cidx ≤ 244) :
    ({ o with tag := cidx } : LcnfObj).Wf := by
  rcases hwf with ⟨h1, h2, h3, h4, h5, _, h7, h8, h9, hrest⟩
  have ⟨hc, ha, hsa, hst, hmp⟩ := tag_le_244_ne_special ht
  have ⟨hc', ha', hsa', hst', hmp'⟩ := tag_le_244_ne_special hcidx
  have htot1 : o.totalBytes = o.csSz := by simp [LcnfObj.totalBytes, ha, hsa, hst, hmp]
  have htot2 : ({ o with tag := cidx } : LcnfObj).totalBytes = o.csSz := by
    simp [LcnfObj.totalBytes, ha', hsa', hst', hmp']
  simp only [hc, ha, hsa, hst, hmp, ite_false] at hrest
  refine ⟨h1, h2, h3, h4, h5, show cidx < 256 by omega, htot2.symm ▸ htot1.symm ▸ h7,
    htot2.symm ▸ htot1.symm ▸ h8, htot2.symm ▸ htot1.symm ▸ h9, ?_⟩
  simp [hc', ha', hsa', hst', hmp', hcidx, hrest]
  omega

public theorem checkExcl_facts {ctx : RcCtx} {x : Nat} {op : String}
    (hchk : ctx.checkExcl x op = .ok ()) :
    ∃ vx, ctx.get? x = some vx ∧ vx.noRc = false ∧ vx.persistent = false ∧
      vx.resetTok = false ∧ vx.owned = 1 ∧ vx.excl = true ∧ vx.isLive = true := by
  simp only [RcCtx.checkExcl] at hchk
  cases hget : ctx.get? x with
  | none => simp [hget] at hchk
  | some vx =>
    simp only [hget] at hchk
    by_cases hno : vx.noRc = true
    · simp [hno] at hchk
    have hnof : vx.noRc = false := by cases h : vx.noRc <;> simp_all
    by_cases hpers : vx.persistent = true
    · simp [hnof, hpers] at hchk
    have hpersf : vx.persistent = false := by cases h : vx.persistent <;> simp_all
    by_cases hrt : vx.resetTok = true
    · simp [hnof, hpersf, hrt] at hchk
    have hrtf : vx.resetTok = false := by cases h : vx.resetTok <;> simp_all
    by_cases hown : vx.owned = 1
    · by_cases hex : vx.excl = true
      · exact ⟨vx, rfl, hnof, hpersf, hrtf, hown, hex, by simp [RcVar.isLive, hown]⟩
      · have hexf : vx.excl = false := by cases h : vx.excl <;> simp_all
        simp [hnof, hpersf, hrt, hown, hexf] at hchk
    · have hne : (vx.owned != 1) = true := by simp [hown]
      simp [hnof, hpersf, hrtf, hne] at hchk

public theorem checkLive_facts {ctx : RcCtx} {x : Nat} (hl : ctx.checkLive x = .ok ()) :
    ∃ vx, ctx.get? x = some vx ∧ vx.isLive = true := by
  simp only [RcCtx.checkLive] at hl
  cases hget : ctx.get? x with
  | none => simp [hget] at hl
  | some vx =>
    simp only [hget] at hl
    by_cases hlive : vx.isLive = true
    · exact ⟨vx, rfl, hlive⟩
    · have hf : vx.isLive = false := by cases h : vx.isLive <;> simp_all
      simp [hf] at hl

public theorem not_isScalar_of_check {v : RcVar} (hcv : CleanVar v) (hno : v.noRc = false) :
    ¬v.ty.isScalar = true :=
  fun hs => absurd (hcv.1.2 hs) (by simp [hno])

public theorem exclDataTagMut_rcInv {rt : BitVec 64} {rf rf0 : RcFrame} {σ σ0 : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx) (hexcl : ExclCtorHeap rf)
    {x : Nat} {vx : RcVar} (hget : rf.ctx.get? x = some vx)
    (hno : vx.noRc = false) (hpers : vx.persistent = false) (hrt : vx.resetTok = false)
    (hown1 : vx.owned = 1) (hex : vx.excl = true)
    {bv : BitVec 64} (henvh : rf.envH x = some (vx.ty, Word.i64 bv)) (hev : bv &&& 1#64 = 0#64)
    {idx : Nat} (hidx : idx < σ.objs.length) (haddr : σ.objs[idx].addr = bv)
    (horc1 : σ.objs[idx].rc = 1#32)
    (o' : LcnfObj) (ho'w : o'.Wf) (ho'a : o'.addr = bv) (ho'rc : o'.rc = 1#32)
    (ho'ch : o'.childFields = σ.objs[idx].childFields)
    (pv' : PVal)
    (hrep' : ValRep vx.ty pv' (Word.i64 bv) (σ.objs.set idx o')) :
    let σ' : HState := { σ with objs := σ.objs.set idx o' }
    let rf' : RcFrame := { rf with envP := rf.envP.set x pv' }
    RcInv rt rf' σ' ∧ CleanVars rf'.ctx ∧ ParentsOwned rf'.ctx ∧ NoRcCorrect rf'.ctx ∧
      ParentChildBacked rf' σ'.objs ∧ SharedTargetsHeap rf' ∧
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs ∧ EntryPres rf0 σ0 rf' σ' ∧
      SharedBoolVars rf'.ctx ∧ ExclCtorHeap rf' := by
  intro σ' rf'
  have ⟨hheap, hnodup, hsound, hvars, hsp⟩ := hinv
  obtain ⟨hbn, hwf_all, hclosed, hcap, hrc_all⟩ := hheap.1
  have hnodup_objs := hheap.2
  have howf : σ.objs[idx].Wf := hwf_all _ (List.getElem_mem hidx)
  obtain ⟨hvm, hxid⟩ := RcCtx.get?_mem hget
  have hlive : vx.isLive = true := by simp [RcVar.isLive, hown1]
  have henvh_v : rf.envH vx.id = some (vx.ty, Word.i64 bv) := hxid ▸ henvh
  have hdisj := excl_disjoint_facts hinv hclean hpo hpcb hvm hno hpers hrt hown1 henvh_v
    (List.getElem_mem hidx) howf haddr horc1
  obtain ⟨hnpre0, hcnt0, hnot_self, hlive_ne, hchild_ne, hbk_ne⟩ := hdisj
  have hnodup_objs' : (σ'.objs.map LcnfObj.addr).Nodup := by
    dsimp only [σ']
    rw [list_map_addr_set_eq hidx (ho'a.trans haddr.symm)]
    exact hnodup_objs
  have hwf_all' : ∀ q ∈ σ'.objs, q.Wf := by
    intro q hq
    rw [list_mem_set_iff hidx] at hq
    rcases hq with rfl | ⟨j, hj, _, rfl⟩
    · exact ho'w
    · exact hwf_all _ (List.getElem_mem hj)
  have hclosed' : lcnfHeapClosed σ'.objs := by
    intro q hq f hf hevf
    dsimp only [σ'] at hq
    rw [list_mem_set_iff hidx] at hq
    rcases hq with rfl | ⟨j, hj, hjne, rfl⟩
    · rw [ho'ch] at hf
      obtain ⟨t, ht, hta⟩ := hclosed _ (List.getElem_mem hidx) f hf hevf
      have hne : f ≠ bv := fun h => hnot_self (h ▸ hf)
      obtain ⟨k, hk, hgetk⟩ := obj_mem_idx ht
      have hkne : k ≠ idx := fun h => by subst h; rw [← hgetk, haddr] at hta; exact hne hta.symm
      exact ⟨t, (list_mem_set_iff hidx).mpr (Or.inr ⟨k, hk, hkne, hgetk⟩), hta⟩
    · have hqj : σ.objs[j].addr ≠ bv := fun h =>
        hjne (nodup_map_getElem_inj hnodup_objs hj hidx (h.trans haddr.symm))
      have hne : f ≠ bv := hchild_ne _ (List.getElem_mem hj)
        (hwf_all _ (List.getElem_mem hj)) hqj f hf hevf
      obtain ⟨t, ht, hta⟩ := hclosed _ (List.getElem_mem hj) f hf hevf
      obtain ⟨k, hk, hgetk⟩ := obj_mem_idx ht
      have hkne : k ≠ idx := fun h => by subst h; rw [← hgetk, haddr] at hta; exact hne hta.symm
      exact ⟨t, (list_mem_set_iff hidx).mpr (Or.inr ⟨k, hk, hkne, hgetk⟩), hta⟩
  have hcap' : σ'.objs.length ≤ σ'.st.workCap := by simpa [σ'] using hcap
  have hrc_all' : ∀ q ∈ σ'.objs, q.rc.toNat < 2 ^ 31 - 1 := by
    intro q hq
    dsimp only [σ'] at hq
    rw [list_mem_set_iff hidx] at hq
    rcases hq with rfl | ⟨j, hj, _, rfl⟩
    · simp [ho'rc]
    · exact hrc_all _ (List.getElem_mem hj)
  have hnpre_eq : ∀ a, nonPersistRefs σ'.objs a = nonPersistRefs σ.objs a := by
    intro a
    have hidx' : idx < σ'.objs.length := by simp [σ', hidx]
    have h1 := nonPersistRefs_focus σ'.objs hidx' a
    have h2 := nonPersistRefs_focus σ.objs hidx a
    have hrc_nz : σ.objs[idx].rc ≠ 0#32 := by rw [horc1]; decide
    have hget_o' : σ'.objs[idx] = o' := by simp [σ']
    have her : σ'.objs.eraseIdx idx = σ.objs.eraseIdx idx := by
      simp [σ', List.eraseIdx_set_eq]
    rw [hget_o', ho'ch, her] at h1
    simp only [ho'rc] at h1
    simp only [horc1] at h2
    change nonPersistRefs σ'.objs a = List.count a σ.objs[idx].childFields +
        nonPersistRefs (σ.objs.eraseIdx idx) a at h1
    change nonPersistRefs σ.objs a = List.count a σ.objs[idx].childFields +
        nonPersistRefs (σ.objs.eraseIdx idx) a at h2
    omega
  have hsound' : HandlesRcSound (frameHandles rf') σ'.objs := by
    have hfeq : frameHandles rf' = frameHandles rf := rfl
    rw [hfeq]
    refine ⟨?_, ?_⟩
    · intro p hp hp0 f hf hevf
      dsimp only [σ'] at hp
      rw [list_mem_set_iff hidx] at hp
      rcases hp with rfl | ⟨j, hj, _, rfl⟩
      · rw [ho'rc] at hp0; cases hp0
      · have hj_mem := List.getElem_mem hj
        obtain ⟨q, hq, hqa, hq0⟩ := hsound.1 _ hj_mem hp0 f hf hevf
        have hqne : q.addr ≠ bv := by
          intro h
          have heq := obj_eq_of_addr_nodup hnodup_objs hq (List.getElem_mem hidx)
            (h.trans haddr.symm)
          rw [heq, horc1] at hq0; cases hq0
        obtain ⟨k, hk, hgetk⟩ := obj_mem_idx hq
        have hkne : k ≠ idx := fun h => by subst h; exact hqne (hgetk.symm ▸ haddr)
        exact ⟨q, (list_mem_set_iff hidx).mpr (Or.inr ⟨k, hk, hkne, hgetk⟩), hqa, hq0⟩
    · intro y hy hypos
      rw [hnpre_eq y.addr]
      dsimp only [σ'] at hy
      rw [list_mem_set_iff hidx] at hy
      rcases hy with rfl | ⟨j, hj, _, rfl⟩
      · have hbase := hsound.2 _ (List.getElem_mem hidx) (by rw [horc1]; decide)
        rw [horc1] at hbase
        rw [ho'a, ho'rc, ← haddr]; exact hbase
      · exact hsound.2 _ (List.getElem_mem hj) hypos
  have hq_mem' : ∀ q ∈ σ.objs, q.addr ≠ bv → q ∈ σ'.objs := by
    intro q hq hqne
    obtain ⟨j, hj, hgetj⟩ := obj_mem_idx hq
    exact (list_mem_set_iff hidx).mpr
      (Or.inr ⟨j, hj, fun h => by subst h; exact hqne (hgetj.symm ▸ haddr), hgetj⟩)
  have hpres_p : ∀ q ∈ σ.objs, q.Wf → q.addr ≠ bv → ∃ q' ∈ σ'.objs, ObjDataEq q q' :=
    fun q hq hqwf hqne => ⟨q, hq_mem' q hq hqne, objDataEq_refl q hqwf⟩
  have hpres_all : ∀ q ∈ σ.objs, q.Wf → (fun _ : BitVec 64 => True) q.addr →
      ∃ q' ∈ σ'.objs, q'.addr = q.addr ∧ q'.rc = q.rc ∧ q'.childFields = q.childFields := by
    intro q hq _ _
    obtain ⟨j, hj, hgetj⟩ := obj_mem_idx hq
    by_cases hjx : j = idx
    · subst hjx
      exact ⟨o', (list_mem_set_iff hidx).mpr (Or.inl rfl), ho'a.trans (hgetj ▸ haddr).symm,
        ho'rc.trans (hgetj ▸ horc1).symm, ho'ch.trans (congrArg LcnfObj.childFields hgetj)⟩
    · exact ⟨q, (list_mem_set_iff hidx).mpr (Or.inr ⟨j, hj, hjx, hgetj⟩), rfl, rfl, rfl⟩
  have hclosed_p : ∀ q ∈ σ.objs, q.Wf → q.addr ≠ bv →
      ∀ f ∈ q.childFields, f &&& 1#64 = 0#64 → f ≠ bv :=
    fun q hq hqwf hqne f hf hevf => hchild_ne q hq hqwf hqne f hf hevf
  have hvars' : ∀ u ∈ rf'.ctx.vars, VarInv u rf' σ'.objs := by
    intro u hu hulive
    by_cases hux : u.id = x
    · have hueq : u = vx := rcVar_eq_of_mem_nodup hnodup hu hvm (hux.trans hxid.symm)
      have hvlive : vx.isLive = true := hueq ▸ hulive
      obtain ⟨_, wu, _, hwu, _, hnon⟩ := hvars vx hvm hvlive
      have hns := not_isScalar_of_check (hclean vx hvm) hno
      obtain ⟨bvv, hwbv, _, _, _, _⟩ := hnon hns
      have heq_bv : bv = bvv := by
        have h := henvh_v.symm.trans (hwbv ▸ hwu); cases h; rfl
      refine ⟨pv', .i64 bv, by simp [rf', PValEnv.set, hux],
        by rw [hueq]; exact henvh_v, hueq ▸ hrep', fun _ => ?_⟩
      refine ⟨bv, rfl, (fun h => by rw [hueq, hno] at h; cases h),
        (fun h => by rw [hueq, hpers] at h; cases h),
        (fun _ => ⟨hueq ▸ hno, hueq ▸ hpers, hueq ▸ hown1, fun _ =>
          ⟨o', (list_mem_set_iff hidx).mpr (Or.inl rfl), ho'a, ho'rc⟩⟩),
        (fun _ _ hb => by
          exfalso
          have hcl := (hclean vx hvm).2.2.1 (hueq ▸ hb)
          rw [hex] at hcl; cases hcl.2.2)⟩
    · obtain ⟨pu, wu, hp, hh, hrep, hnon⟩ := hvars u hu hulive
      have hrep_u : ValRep u.ty pu wu σ'.objs := by
        refine valRep_mono_pred (P := fun a => a ≠ bv) hpres_p hclosed_p hrep ?_
        intro hns bvu hwu _
        have hnsb : !u.ty.isScalar = true := by cases h : u.ty.isScalar <;> simp_all
        exact hlive_ne u hu (fun h => hux (h.trans hxid)) hulive hnsb bvu (hwu ▸ hh)
      refine ⟨pu, wu, by simp [rf', PValEnv.set, hux, hp], hh, hrep_u, fun hns => ?_⟩
      obtain ⟨bvu, hwu, hno_u, hpers_u, hex_u, hbor_u⟩ := hnon hns
      have hnsb : !u.ty.isScalar = true := by cases h : u.ty.isScalar <;> simp_all
      have hne_bv : bvu ≠ bv :=
        hlive_ne u hu (fun h => hux (h.trans hxid)) hulive hnsb bvu (hwu ▸ hh)
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
        refine ⟨backed_mono_heap hpres_all (fun _ _ _ _ _ _ _ => trivial) hwf_all
          (fun _ hr => ⟨hr, trivial⟩) trivial hbk1, ?_⟩
        cases hpar : u.parent? with
        | none =>
          rw [hpar] at hbk2; dsimp only at hbk2
          exact backed_mono_heap hpres_all (fun _ _ _ _ _ _ _ => trivial) hwf_all
            (fun _ hr => ⟨hr, trivial⟩) trivial hbk2
        | some p =>
          rw [hpar] at hbk2; dsimp only at hbk2
          obtain ⟨pv, hpv_m, hpv_id, hpv_no, hpv_ps, hpv_pos, hpv_bk⟩ := hbk2
          refine ⟨pv, hpv_m, hpv_id, hpv_no, hpv_ps, hpv_pos, ?_⟩
          exact backed_mono_heap hpres_all (fun _ _ _ _ _ _ _ => trivial) hwf_all
            (fun _ hr => ⟨hr, trivial⟩) trivial hpv_bk
  have hsp' : SharedPredInv rf' σ'.objs := by
    intro p hp vb vs hgb hgs hblive hsno hspers
    have hpx1 : p.1 ≠ x := by
      intro heq
      have hvb_no : vb.noRc = true := hsbv p hp vb hgb
      have h := hgb; rw [heq, hget] at h; cases h
      rw [hno] at hvb_no; cases hvb_no
    have hsp_old := hsp p hp vb vs hgb hgs hblive hsno hspers
    have htag_eq : (rf'.envP p.1).bind PVal.tag? = (rf.envP p.1).bind PVal.tag? := by
      simp [rf', PValEnv.set, hpx1]
    rw [htag_eq]
    by_cases hpx2 : p.2 = x
    · have hvs_eq : vs = vx := by have h := hgs; rw [hpx2, hget] at h; cases h; rfl
      refine ⟨fun htag => ?_, fun htag hspos => ?_⟩
      · obtain ⟨bvs, henvs, hevs, hrest⟩ := hsp_old.1 htag
        have henvh_s : rf.envH p.2 = some (vs.ty, Word.i64 bv) := hvs_eq ▸ hpx2 ▸ henvh
        have heq_bvs : bvs = bv := by
          have h := henvh_s.symm.trans henvs; cases h; rfl
        refine ⟨bv, hvs_eq ▸ hpx2 ▸ henvh, hev, fun hspos => ?_⟩
        obtain ⟨hc0, o_s, ho_s, ho_sa, ho_src⟩ := hrest hspos
        refine ⟨?_, o', (list_mem_set_iff hidx).mpr (Or.inl rfl), ho'a, ?_⟩
        · rw [hnpre_eq bv]
          have hc0' : nonPersistRefs σ.objs bv +
              List.count bv
                (localHandlesExcept rf'.ctx rf'.envH p.2 ++ rf'.extH ++ rf'.ghostH) = 0 := by
            simpa [rf', heq_bvs] using hc0
          exact hc0'
        · rw [ho'rc, hvs_eq, hown1]; decide
      · exfalso
        obtain ⟨bvs, henvs, _, o_s, ho_s, ho_sa, horc⟩ := hsp_old.2 htag hspos
        have henvh_s : rf.envH p.2 = some (vs.ty, Word.i64 bv) := hvs_eq ▸ hpx2 ▸ henvh
        have heq_bvs : bvs = bv := by
          have h := henvh_s.symm.trans henvs; cases h; rfl
        have ho_eq : o_s = σ.objs[idx] := obj_eq_of_addr_nodup hnodup_objs ho_s
          (List.getElem_mem hidx) (ho_sa.trans (heq_bvs ▸ haddr.symm))
        rw [ho_eq, horc1, hvs_eq, hown1] at horc
        rcases horc with h0 | hlt
        · simp at h0
        · simp at hlt
    · refine ⟨fun htag => ?_, fun htag hspos => ?_⟩
      · obtain ⟨bvs, henvs, hevs, hrest⟩ := hsp_old.1 htag
        refine ⟨bvs, henvs, hevs, fun hspos => ?_⟩
        obtain ⟨hc0, o_s, ho_s, ho_sa, ho_src⟩ := hrest hspos
        have hslive : vs.isLive = true := by simp [RcVar.isLive, hspos]
        have hns_s := not_isScalar_of_check (hclean vs (RcCtx.get?_mem hgs).1) hsno
        have hnsb_s : !vs.ty.isScalar = true := by cases h : vs.ty.isScalar <;> simp_all
        have hne_s : bvs ≠ bv := hlive_ne vs (RcCtx.get?_mem hgs).1
          (fun h => hpx2 (((RcCtx.get?_mem hgs).2 ▸ h).trans hxid)) hslive hnsb_s bvs
          (by simpa [(RcCtx.get?_mem hgs).2] using henvs)
        refine ⟨?_, o_s, hq_mem' o_s ho_s (ho_sa.symm ▸ hne_s), ho_sa, ho_src⟩
        rw [hnpre_eq bvs]; exact hc0
      · obtain ⟨bvs, henvs, hevs, o_s, ho_s, ho_sa, horc⟩ := hsp_old.2 htag hspos
        have hslive : vs.isLive = true := by simp [RcVar.isLive, hspos]
        have hns_s := not_isScalar_of_check (hclean vs (RcCtx.get?_mem hgs).1) hsno
        have hnsb_s : !vs.ty.isScalar = true := by cases h : vs.ty.isScalar <;> simp_all
        have hne_s : bvs ≠ bv := hlive_ne vs (RcCtx.get?_mem hgs).1
          (fun h => hpx2 (((RcCtx.get?_mem hgs).2 ▸ h).trans hxid)) hslive hnsb_s bvs
          (by simpa [(RcCtx.get?_mem hgs).2] using henvs)
        exact ⟨bvs, henvs, hevs, o_s, hq_mem' o_s ho_s (ho_sa.symm ▸ hne_s), ho_sa, horc⟩
  have hpcb' : ParentChildBacked rf' σ'.objs := by
    intro u hu hulive huno hupers hubor q hpar bvu henvu hevu
    have hns_u := not_isScalar_of_check (hclean u hu) huno
    have hnsb : !u.ty.isScalar = true := by cases h : u.ty.isScalar <;> simp_all
    have hux : u.id ≠ vx.id := by
      intro heq
      have hueq := rcVar_eq_of_mem_nodup hnodup hu hvm heq
      subst hueq
      have := (hclean u hvm).2.2.1 hubor
      rw [hex] at this; simp at this
    have hne_u : bvu ≠ bv := hlive_ne u hu hux hulive hnsb bvu henvu
    rcases hpcb u hu hulive huno hupers hubor q hpar bvu henvu hevu with hext | hch
    · exact Or.inl (backed_mono_heap hpres_all (fun _ _ _ _ _ _ _ => trivial) hwf_all
        (fun _ hr => ⟨hr, trivial⟩) trivial hext)
    · right
      obtain ⟨wp, o_q, hwp, hqaddr, ho_q, o_mid, hom_m, hreach_mid, hcf⟩ := hch
      have hreach' := (nonPersistReach_mono_pred (P := fun _ => True) hpres_all
        (fun _ _ _ _ _ _ _ => trivial) hwf_all trivial hreach_mid).1
      obtain ⟨o_mid', hom'm, hma, _, hmcf⟩ := hpres_all o_mid hom_m (hwf_all o_mid hom_m) trivial
      obtain ⟨pv, hpv_m, hpv_id, hpv_no, hpv_ps, hpv_pos, _⟩ := hpo u hu q hpar
      have hlive_pv : pv.isLive = true := by simp [RcVar.isLive, hpv_pos]
      have hns_pv := not_isScalar_of_check (hclean pv hpv_m) hpv_no
      have hnsb_pv : !pv.ty.isScalar = true := by cases h : pv.ty.isScalar <;> simp_all
      obtain ⟨_, wu0, _, hwu0, _, hnon0⟩ := hvars pv hpv_m hlive_pv
      obtain ⟨bvp, hwp0, _⟩ := hnon0 hns_pv
      have hwu0' : rf.envH pv.id = some (pv.ty, Word.i64 bvp) := hwp0 ▸ hwu0
      have hwp_eq : wp = (pv.ty, Word.i64 bvp) := by
        have h := hwu0'; rw [hpv_id, hwp] at h; cases h; rfl
      have hq_bv : o_q.addr = bvp := by
        have h := hqaddr; rw [hwp_eq] at h
        change some bvp = some o_q.addr at h
        exact (Option.some.inj h).symm
      by_cases hpvx : pv.id = vx.id
      · have hpveq : pv = vx := rcVar_eq_of_mem_nodup hnodup hpv_m hvm hpvx
        subst hpveq
        have hbvp_eq : bvp = bv := by
          have h := hwu0'.symm.trans henvh_v; cases h; rfl
        have ho_q_eq : o_q = σ.objs[idx] := obj_eq_of_addr_nodup hnodup_objs ho_q
          (List.getElem_mem hidx) (hq_bv.trans (hbvp_eq.trans haddr.symm))
        have hq_o' : o_q.addr = o'.addr := hq_bv.trans (hbvp_eq.trans ho'a.symm)
        exact ⟨wp, o', hwp, hq_o' ▸ hqaddr, (list_mem_set_iff hidx).mpr (Or.inl rfl),
          o_mid', hom'm, hq_o' ▸ hma ▸ hreach', hmcf ▸ hcf⟩
      · have hne_q : o_q.addr ≠ bv := by
          rw [hq_bv]; exact hlive_ne pv hpv_m hpvx hlive_pv hnsb_pv bvp hwu0'
        exact ⟨wp, o_q, hwp, hqaddr, hq_mem' o_q ho_q hne_q,
          o_mid', hom'm, hma ▸ hreach', hmcf ▸ hcf⟩
  have hhih' : HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs := by
    intro a ha
    obtain ⟨q, hq, hqa⟩ := hhih a ha
    have hne : a ≠ bv := fun h => by
      have hcnt_pos : 0 < List.count bv (rf.extH ++ rf.ghostH) :=
        List.count_pos_iff.mpr (h ▸ ha)
      simp only [List.count_append] at hcnt0 hcnt_pos
      omega
    exact ⟨q, hq_mem' q hq (hqa.symm ▸ hne), hqa⟩
  have hepres' : EntryPres rf0 σ0 rf' σ' := by
    obtain ⟨hhs0, hiso0, hext0, hgh0⟩ := hepres
    have hhs_step : HeapStepRel (rf0.extH ++ rf0.ghostH) σ σ' := by
      refine ⟨by dsimp only [σ']; simp [RtC0State.PreservesMeta], rfl, rfl,
        fun q hq hqwf hbk => ?_, fun a hb => ?_⟩
      · have hbk_all : Backed σ.objs
            (localHandlesExcept rf.ctx rf.envH vx.id ++ rf.extH ++ rf.ghostH) q.addr := by
          refine backed_mono_roots (fun r hr => ?_) hbk
          rw [List.mem_append] at hr
          rcases hr with hre | hrg
          · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (hext0 ▸ hre))))
          · exact List.mem_append.mpr (Or.inr (hgh0.1 r hrg))
        have hne := hbk_ne q.addr hbk_all
        exact ⟨q, hq_mem' q hq hne, objDataEq_refl q hqwf, id, id⟩
      · exact backed_mono_heap hpres_all (fun _ _ _ _ _ _ _ => trivial) hwf_all
          (fun _ hr => ⟨hr, trivial⟩) trivial hb
    refine ⟨heapStepRel_trans hhs0 hhs_step, ?_, hext0, hgh0⟩
    intro a ha hiso_a0
    obtain ⟨hiso_a, ha_rc1⟩ := hiso0 a ha hiso_a0
    obtain ⟨hiso_live, hiso_np, o_a, ho_a, ho_awf, ho_aa, ho_arc1⟩ := hiso_a
    have hnsb : !vx.ty.isScalar = true := by
      have h := not_isScalar_of_check (hclean vx hvm) hno
      cases hs : vx.ty.isScalar <;> simp_all
    have hne_bv : bv ≠ a := fun heq =>
      hiso_live vx hvm hlive hnsb (Word.i64 bv) henvh_v (by subst heq; rfl)
    refine ⟨⟨hiso_live, by rw [hnpre_eq a]; exact hiso_np, ?_⟩, ?_⟩
    · exact ⟨o_a, hq_mem' o_a ho_a (ho_aa.symm ▸ hne_bv.symm), ho_awf, ho_aa, ho_arc1⟩
    · intro q0 hq0 hqa0
      obtain ⟨q, hq, hdeq, hq1⟩ := ha_rc1 q0 hq0 hqa0
      exact ⟨q, hq_mem' q hq ((hdeq.1.trans hqa0).symm ▸ hne_bv.symm), hdeq, hq1⟩
  have hexcl' : ExclCtorHeap rf' := by
    intro u hu hul hexu hnou hpersu cidx fs sc hpu
    by_cases hux : u.id = x
    · have hueq : u = vx := rcVar_eq_of_mem_nodup hnodup hu hvm (hux.trans hxid.symm)
      subst hueq
      exact ⟨bv, henvh_v, hev⟩
    · simp only [rf', PValEnv.set, hux, ite_false] at hpu
      exact hexcl u hu hul hexu hnou hpersu cidx fs sc hpu
  exact ⟨⟨⟨⟨hbn, hwf_all', hclosed', hcap', hrc_all'⟩, hnodup_objs'⟩, hnodup,
    hsound', hvars', hsp'⟩,
    hclean, hpo, hnorc, hpcb', hsth, hhih', hepres', hsbv, hexcl'⟩

end MutObjWf

section ScalarAndTagSteps

private theorem scalar_toTTy_bytes_pos {ty : LcTy} (h : ty.isScalar = true) :
    0 < ty.toTTy.bytes := by
  cases ty <;> simp [LcTy.isScalar, LcTy.toTTy, Ty.bytes, Ty.size, LcTy.width] at h ⊢

private theorem scalarRep_toNat_eq {w : Nat} {pv : PVal} {wd : Word}
    (hsr : ScalarRep w pv wd) : wd.1 = Ty.bits w ∧ wd.toNat? = pv.toNat? := by
  rcases hsr with ⟨bv, rfl, rfl⟩ | ⟨cidx, rfl, hlt, rfl⟩ | ⟨rfl, rfl⟩
  · simp [Word.toNat?, PVal.toNat?]
  · simp [Word.toNat?, PVal.toNat?]
  · simp [Word.toNat?, PVal.toNat?]

private theorem scalarTy_toTTy_eq_bits {ty : LcTy} (h : ty.isScalar = true) :
    ty.toTTy = Ty.bits ty.width := by
  cases ty <;> simp [LcTy.isScalar, LcTy.toTTy, LcTy.width] at h ⊢

/-- Shared extraction of heap object + exclusivity facts for a live exclusive `.ctor` variable. -/
public theorem ctor_excl_obj_facts {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (_hclean : CleanVars rf.ctx)
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    (hexcl : ExclCtorHeap rf) {x : Nat} {vx : RcVar} (hgx : rf.ctx.get? x = some vx)
    (hno : vx.noRc = false) (hpers : vx.persistent = false) (_hrt : vx.resetTok = false)
    (_hown1 : vx.owned = 1) (hex : vx.excl = true) (hlx : vx.isLive = true)
    (hvx_ns : vx.ty.isScalar = false)
    {cidx : Nat} {fs : List PVal} {pscal : List UInt8}
    (hρx : ρP x = some (.ctor cidx fs pscal))
    (hheap_or : ¬(fs = [] ∧ pscal = []) ∨ True) :
    ∃ hscal addr idx, ∃ hidx : idx < σ.objs.length,
      rf.envP x = some (.ctor cidx fs hscal) ∧
      hscal.length = pscal.length ∧
      rf.envH x = some (vx.ty, .i64 addr) ∧
      rf.envH.getBV64? x = some addr ∧
      addr &&& 1#64 = 0#64 ∧
      let o := σ.objs[idx]
      o.addr = addr ∧ o.Wf ∧ o.tag = cidx ∧ o.tag ≤ 244 ∧
      o.fields.length = fs.length ∧ o.scalarData = hscal ∧ o.rc = 1#32 ∧
      objFieldsRep fs o.fields σ.objs := by
  have ⟨hvx_m, hxid⟩ := RcCtx.get?_mem hgx
  have hnodup_objs := hinv.1.2
  have hx_shd := hshd vx hvx_m hlx
  rw [hxid] at hx_shd
  obtain ⟨hscal, hE_x, hlen_eq⟩ :
      ∃ hscal, rf.envP x = some (.ctor cidx fs hscal) ∧ hscal.length = pscal.length := by
    cases hxi : isVarScalarInit sm x
    · simp only [hxi, Bool.false_eq_true, ite_false] at hx_shd
      obtain ⟨_, _, _, _, _, _, hs0, hρ0, hE0, hl1, hl2, _⟩ := hx_shd
      rw [hρx] at hρ0; cases hρ0
      exact ⟨hs0, hE0, hl2.trans hl1.symm⟩
    · simp only [hxi, ite_true] at hx_shd
      exact ⟨pscal, hx_shd ▸ hρx, rfl⟩
  have ⟨_, wx, hpx, hwx, hrx, hnon⟩ := hinv.2.2.2.1 vx hvx_m hlx
  rw [hxid, hE_x] at hpx; cases hpx
  have hnonsc : ¬vx.ty.isScalar = true := by simp [hvx_ns]
  simp only [ValRep, hnonsc] at hrx
  obtain ⟨addr, hw_x, hobj_x, _⟩ := hrx
  have hne_or_ev : ¬(fs = [] ∧ hscal = []) ∨ addr &&& 1#64 = 0#64 := by
    rcases hheap_or with hne | _
    · left
      intro ⟨h1, h2⟩
      apply hne
      exact ⟨h1, List.eq_nil_of_length_eq_zero (by rw [← hlen_eq, h2]; rfl)⟩
    · right
      obtain ⟨bv0, hbv0, hev0⟩ := hexcl vx hvx_m hlx hex hno hpers cidx fs hscal (hxid ▸ hE_x)
      have h := (hw_x ▸ hwx).symm.trans hbv0; cases h; exact hev0
  rcases hobj_x with ⟨_, _, _, htag_bv⟩ | ⟨_, o, ho, hoa, howf, hotag, hotle, hosc, hof⟩
  · exfalso
    rcases hne_or_ev with hne | hev
    · exact absurd ⟨‹_›, ‹_›⟩ hne
    · rw [htag_bv] at hev
      exact boxNat_and1_ne_zero cidx hev
  · obtain ⟨idx, hidx, hget_idx⟩ := obj_mem_idx ho
    have haddr : σ.objs[idx].addr = addr := hget_idx ▸ hoa
    have hev : addr &&& 1#64 = 0#64 := hoa ▸ obj_addr_and1_zero howf
    have henvh_x : rf.envH x = some (vx.ty, .i64 addr) := hxid ▸ hw_x ▸ hwx
    have horc1 : σ.objs[idx].rc = 1#32 := by
      obtain ⟨bv0, hwb0, _, _, hex0, _⟩ := hnon hnonsc
      have heqbv : addr = bv0 := by
        have h := henvh_x.symm.trans (hxid ▸ hwb0 ▸ hwx); cases h; rfl
      obtain ⟨q, hq, hqa, hqrc1⟩ := (hex0 hex).2.2.2 (heqbv ▸ hev)
      have hqeq := obj_eq_of_addr_nodup hnodup_objs hq (List.getElem_mem hidx)
        (hqa.trans (heqbv ▸ haddr).symm)
      exact hqeq ▸ hqrc1
    have hgbv_x : rf.envH.getBV64? x = some addr := by
      have htbv : (Word.i64 addr).toBV64? = some addr := rfl
      simp [HValEnv.getBV64?, HValEnv.evalArgOwn, henvh_x, htbv]
    refine ⟨hscal, addr, idx, hidx, hE_x, hlen_eq, henvh_x, hgbv_x, hev, haddr,
      hget_idx ▸ howf, hget_idx ▸ hotag, hget_idx ▸ hotle,
      hget_idx ▸ (objFieldsRep_length hof).symm, hget_idx ▸ hosc, horc1, hget_idx ▸ hof⟩

/-- Shared step simulation for scalar constructor field writes (`uset` and `sset`). -/
private theorem scalarMut_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {J : HJEnv} {Jp : PResJEnv}
    {Q : PResPost} {Xp : PResXPost} {Qh : HPost} {Xh : HXPost}
    {jps : List RcJpInfo} {rf rf0 : RcFrame} {σ σ0 : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr : Nat}
    {x n off cidx : Nat} {fs : List PVal} {pscal : List UInt8}
    {patch : List UInt8} {op : String} {k : LcCode}
    (hwf_k : perceusCodeWf env retTy jps rf.ctx (initScalarBytes sm x n off patch.length) k = true)
    (hchk : rf.ctx.checkExcl x op = .ok ())
    (hpr_k : PRWp m env retTy Δr jps rf.ctx Jp
      (ρP.set x (.ctor cidx fs (writeBytesAt pscal (8 * (n - fs.length) + off) patch)))
      rem wr rcr Q Xp k)
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx)
    (hexcl : ExclCtorHeap rf) (hsm : ShadowSmWf sm) (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    (hres : ResStateInv σ rem wr rcr)
    {vx : RcVar} (hgx : rf.ctx.get? x = some vx) (hvx_ns : vx.ty.isScalar = false)
    (hvx_nt : (vx.ty != .tagged) = true)
    (hρx : ρP x = some (.ctor cidx fs pscal)) (hfs_le : fs.length ≤ n)
    (hpat_pos : 0 < patch.length)
    (hbd_p : 8 * (n - fs.length) + off + patch.length ≤ pscal.length)
    (hk : ∀ {rf' : RcFrame} {σ' : HState} {ρP' : PValEnv},
      perceusCodeWf env retTy jps rf'.ctx (initScalarBytes sm x n off patch.length) k = true →
      PRWp m env retTy Δr jps rf'.ctx Jp ρP' rem wr rcr Q Xp k →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → ExclCtorHeap rf' →
      ShadowSmWf (initScalarBytes sm x n off patch.length) →
      ShadowOk (initScalarBytes sm x n off patch.length) rf'.ctx ρP' rf'.envP →
      ResStateInv σ' rem wr rcr →
      rf'.ctx = rf.ctx ∧ rf'.extH = rf.extH ∧
        rf'.envH = rf.envH ∧ (∀ z ≠ x, ρP' z = ρP z ∧ rf'.envP z = rf.envP z) →
      HWp Δh rt retTy J rf'.envH Qh Xh k σ') :
    ∃ addr, ∃ (idx : Nat) (hidx : idx < σ.objs.length),
      let o := σ.objs[idx]
      rf.envH.getBV64? x = some addr ∧
      o.addr = addr ∧ o.tag ≤ 244 ∧ o.fields.length ≤ n ∧
      let bOff := 8 * (n - o.fields.length) + off
      bOff + patch.length ≤ o.scalarData.length ∧
      let scal' := writeBytesAt o.scalarData bOff patch
      HWp Δh rt retTy J rf.envH Qh Xh k
        { σ with objs := σ.objs.set idx { o with scalarData := scal' } } := by
  obtain ⟨vx', hgx', hno, hpers, hrt, hown1, hex, hlx⟩ := checkExcl_facts hchk
  rw [hgx'] at hgx; cases hgx
  have hne_p : ¬(fs = [] ∧ pscal = []) := fun ⟨_, hs0⟩ => by
    have h := hbd_p
    rw [hs0] at h; simp only [List.length_nil] at h; omega
  obtain ⟨hscal, addr, idx, hidx, hE_x, hlen_eq, henvh_x, hgbv_x, hev, haddr, howf, hotag,
    hotle, hflen, hosc, horc1, hof⟩ := ctor_excl_obj_facts hinv hclean hshd hexcl hgx'
    hno hpers hrt hown1 hex hlx hvx_ns hρx (Or.inl hne_p)
  have hbd_h : 8 * (n - fs.length) + off + patch.length ≤ hscal.length := hlen_eq ▸ hbd_p
  let bOff := 8 * (n - fs.length) + off
  let scal' := writeBytesAt hscal bOff patch
  let o' : LcnfObj := { σ.objs[idx] with scalarData := scal' }
  have hsc_len : scal'.length = σ.objs[idx].scalarData.length := by
    rw [hosc]; exact writeBytesAt_length hbd_h
  have ho'w : o'.Wf := lcnfObj_wf_set_scalar howf hotle hsc_len
  have ho'ch : o'.childFields = σ.objs[idx].childFields := by
    simp [o', LcnfObj.childFields, hotle]
  let σ' : HState := { σ with objs := σ.objs.set idx o' }
  have hnodup_objs := hinv.1.2
  have hvx_m := (RcCtx.get?_mem hgx').1
  have hpres_p : ∀ q ∈ σ.objs, q.Wf → q.addr ≠ addr → ∃ q' ∈ σ'.objs, ObjDataEq q q' := by
    intro q hq hqwf hqne
    obtain ⟨j, hj, hgetj⟩ := obj_mem_idx hq
    have hjne : j ≠ idx := fun h => by subst h; exact hqne (hgetj.symm ▸ haddr)
    exact ⟨q, (list_mem_set_iff hidx).mpr (Or.inr ⟨j, hj, hjne, hgetj⟩), objDataEq_refl q hqwf⟩
  have hdisj := excl_disjoint_facts hinv hclean hpo hpcb hvx_m hno hpers hrt hown1
    ((RcCtx.get?_mem hgx').2 ▸ henvh_x) (List.getElem_mem hidx) howf haddr horc1
  obtain ⟨_, _, hnot_self, _, hchild_ne, _⟩ := hdisj
  have hrep' : ValRep vx.ty (.ctor cidx fs scal') (.i64 addr) σ'.objs := by
    have hnonsc : ¬vx.ty.isScalar = true := by simp [hvx_ns]
    simp only [ValRep, hnonsc]
    refine ⟨addr, rfl, Or.inr ⟨fun ⟨_, hs0⟩ => by
      have := hsc_len; rw [hs0, hosc] at this; simp at this; omega,
      o', (list_mem_set_iff hidx).mpr (Or.inl rfl), haddr, ho'w, hotag, hotle, rfl, ?_⟩,
      fun _ => hev, fun ht => by rw [ht] at hvx_nt; exact absurd hvx_nt (by decide)⟩
    refine objFieldsRep_mono_pred (P := fun a => a ≠ addr) hpres_p hchild_ne hof
      (fun f hf _ heq => ?_)
    apply hnot_self
    have hcf : σ.objs[idx].childFields = σ.objs[idx].fields := by
      simp [LcnfObj.childFields, hotle]
    rw [hcf]; exact heq ▸ hf
  have hcore := exclDataTagMut_rcInv hinv hclean hpo hnorc hpcb hsth hhih hepres hsbv hexcl
    hgx' hno hpers hrt hown1 hex henvh_x hev hidx haddr horc1 o' ho'w haddr horc1 ho'ch
    (.ctor cidx fs scal') hrep'
  obtain ⟨hinv', hclean', hpo', hnorc', hpcb', hsth', hhih', hepres', hsbv', hexcl'⟩ := hcore
  have hres' : ResStateInv σ' rem wr rcr := by
    refine ⟨hres.1, by simpa [σ'] using hres.2.1, ?_⟩
    have hle : maxObjRc (σ.objs.set idx o') ≤ maxObjRc σ.objs := by
      apply maxObjRc_set_le; intro _; simp [o', horc1]
    have hmax_le : Nat.max 1 (maxObjRc (σ.objs.set idx o')) ≤ Nat.max 1 (maxObjRc σ.objs) :=
      Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hle (Nat.le_max_right _ _)⟩
    have := hres.2.2; simp only [σ']; omega
  have hsm' := shadowSmWf_initScalarBytes hsm x n off patch.length
  have hshd' := shadowOk_update_scalarBytes hsm hshd hgx' hlx hρx hE_x hbd_p hbd_h
  have hstep_k := hk
    (rf' := { rf with envP := rf.envP.set x (.ctor cidx fs scal') }) (σ' := σ')
    (ρP' := ρP.set x (.ctor cidx fs (writeBytesAt pscal bOff patch)))
    hwf_k hpr_k hinv' hclean' hpo' hnorc' hpcb' hsth' hhih' hepres' hsbv' hexcl' hsm' hshd' hres'
    ⟨rfl, rfl, rfl, fun z hzx => ⟨by simp [PValEnv.set, hzx], by simp [PValEnv.set, hzx]⟩⟩
  refine ⟨addr, idx, hidx, hgbv_x, haddr, hotle, hflen ▸ hfs_le,
    by simpa [bOff, hflen, hosc] using hbd_h, ?_⟩
  simpa [σ', o', bOff, scal', hflen, hosc] using hstep_k

/-- Stepwise simulation for `LcCode.uset`: advances `HWp`, `RcInv`, and `ShadowOk`. -/
public theorem uset_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {J : HJEnv} {Jp : PResJEnv}
    {Q : PResPost} {Xp : PResXPost} {Qh : HPost} {Xh : HXPost}
    {jps : List RcJpInfo} {rf rf0 : RcFrame} {σ σ0 : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr : Nat}
    {x i y : Nat} {k : LcCode}
    (hwf : perceusCodeWf env retTy jps rf.ctx sm (LcCode.uset x i y k) = true)
    (hchk : rf.ctx.checkExcl x "uset" = .ok ()) (hly : rf.ctx.checkLive y = .ok ())
    (hpr : PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Q Xp (LcCode.uset x i y k))
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx)
    (hexcl : ExclCtorHeap rf) (hsm : ShadowSmWf sm) (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    (hres : ResStateInv σ rem wr rcr)
    (hk : ∀ {rf' : RcFrame} {σ' : HState} {ρP' : PValEnv},
      perceusCodeWf env retTy jps rf'.ctx (initScalarBytes sm x i 0 8) k = true →
      PRWp m env retTy Δr jps rf'.ctx Jp ρP' rem wr rcr Q Xp k →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → ExclCtorHeap rf' →
      ShadowSmWf (initScalarBytes sm x i 0 8) →
      ShadowOk (initScalarBytes sm x i 0 8) rf'.ctx ρP' rf'.envP →
      ResStateInv σ' rem wr rcr →
      rf'.ctx = rf.ctx ∧ rf'.extH = rf.extH ∧
        rf'.envH = rf.envH ∧ (∀ z ≠ x, ρP' z = ρP z ∧ rf'.envP z = rf.envP z) →
      HWp Δh rt retTy J rf'.envH Qh Xh k σ') :
    HWp Δh rt retTy J rf.envH Qh Xh (LcCode.uset x i y k) σ := by
  rw [perceusCodeWf.eq_12] at hwf
  rw [PRWp.eq_8] at hpr
  rw [HWp.eq_8]
  obtain ⟨vx, hgx, _, _, _, _, _, _⟩ := checkExcl_facts hchk
  obtain ⟨vy, hgy, hly_live⟩ := checkLive_facts hly
  simp only [Bool.and_eq_true, hgx, hgy] at hwf
  rcases hwf with ⟨⟨⟨_, hy_init⟩, hxy_ty⟩, hwf_k⟩
  simp only [Bool.not_eq_true', beq_iff_eq] at hxy_ty
  obtain ⟨⟨⟨hvx_ns, hvx_nt⟩, hvy_sc⟩, hvy_w⟩ := hxy_ty
  cases hρx : ρP x with
  | none => simp [hρx] at hpr
  | some xv =>
    cases hρy : ρP y with
    | none => simp [hρx, hρy] at hpr
    | some yv =>
      simp only [hρx, hρy] at hpr
      cases hset : xv.setUsize i yv with
      | none => simp [hset] at hpr
      | some xv' =>
        simp only [hset] at hpr
        cases yv with
        | bits w bv_y =>
          cases hvty_w : w == 64 with
          | false =>
            have hwn : w ≠ 64 := fun h => by subst h; cases hvty_w
            simp [PVal.setUsize, PVal.toBits?, hwn] at hset
          | true =>
            have hw64 : w = 64 := eq_of_beq hvty_w
            subst hw64
            cases xv with
            | ctor cidx fs pscal =>
              have hbits64 : PVal.toBits? 64 (PVal.bits 64 bv_y) = some bv_y := rfl
              simp only [PVal.setUsize, hbits64] at hset
              by_cases hfs_le : fs.length ≤ i
              · simp only [hfs_le, ite_true] at hset
                by_cases hbd_p : 8 * (i - fs.length) + 8 ≤ pscal.length
                · simp only [hbd_p, ite_true] at hset; cases hset
                  have ⟨hvy_m, hyid⟩ := RcCtx.get?_mem hgy
                  have hy_shd := hshd vy hvy_m hly_live
                  simp only [hyid, hy_init, ite_true] at hy_shd
                  have hE_y : rf.envP y = some (.bits 64 bv_y) := hy_shd ▸ hρy
                  obtain ⟨py0, wy0, hpy0, hwy0, hrep_y, _⟩ := hinv.2.2.2.1 vy hvy_m hly_live
                  rw [hyid, hE_y] at hpy0; cases hpy0
                  simp only [ValRep, hvy_sc, ite_true, hvy_w] at hrep_y
                  rcases hrep_y with ⟨bv0, hbv0, rfl⟩ | ⟨_, hc0, _⟩ | ⟨hc0, _⟩
                  · cases hbv0
                    have hgbv_y : rf.envH.getBV64? y = some bv_y := by
                      simp [HValEnv.getBV64?, HValEnv.evalArgOwn, hyid ▸ hwy0]; rfl
                    let patch := writeNatLE bv_y.toNat 8
                    have hpat_len : patch.length = 8 := writeNatLE_length _ 8
                    have hstep := scalarMut_step (Δh := Δh) (J := J) (Qh := Qh) (Xh := Xh)
                      (x := x) (n := i) (off := 0) (patch := patch)
                      (by simpa [hpat_len] using hwf_k) hchk
                      (by simpa [writeNatLE_eq_pval, writeBytesAt_eq_pval, patch] using hpr)
                      hinv hclean hpo hnorc hpcb hsth hhih hepres hsbv hexcl hsm hshd hres
                      hgx hvx_ns hvx_nt hρx hfs_le (by omega) (by simpa [hpat_len] using hbd_p)
                      (fun hw' hp' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 => by
                        rw [hpat_len] at hw' h11 h12
                        exact hk hw' hp' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14)
                    obtain ⟨addr, idx, hidx, hgx_bv, haddr, hotle, hflen_le, hbd_o, hwp_k⟩ := hstep
                    rw [hgx_bv, hgbv_y]
                    refine ⟨idx, hidx, haddr, hotle, hflen_le, ?_, ?_⟩
                    · simpa [patch, hpat_len] using hbd_o
                    · simpa [patch] using hwp_k
                  · cases hc0
                  · cases hc0
                · simp [hbd_p] at hset
              · simp [hfs_le] at hset
            | _ => simp [PVal.setUsize] at hset
        | _ => simp [PVal.setUsize, PVal.toBits?] at hset

/-- Stepwise simulation for `LcCode.sset`: advances `HWp`, `RcInv`, and `ShadowOk`. -/
public theorem sset_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {J : HJEnv} {Jp : PResJEnv}
    {Q : PResPost} {Xp : PResXPost} {Qh : HPost} {Xh : HXPost}
    {jps : List RcJpInfo} {rf rf0 : RcFrame} {σ σ0 : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr : Nat}
    {x n off y : Nat} {ty : LcTy} {k : LcCode}
    (hwf : perceusCodeWf env retTy jps rf.ctx sm (LcCode.sset x n off y ty k) = true)
    (hchk : rf.ctx.checkExcl x "sset" = .ok ()) (hly : rf.ctx.checkLive y = .ok ())
    (hpr : PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Q Xp (LcCode.sset x n off y ty k))
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx)
    (hexcl : ExclCtorHeap rf) (hsm : ShadowSmWf sm) (hshd : ShadowOk sm rf.ctx ρP rf.envP)
    (hres : ResStateInv σ rem wr rcr)
    (hk : ∀ {rf' : RcFrame} {σ' : HState} {ρP' : PValEnv},
      perceusCodeWf env retTy jps rf'.ctx
        (initScalarBytes sm x n off ty.toTTy.bytes) k = true →
      PRWp m env retTy Δr jps rf'.ctx Jp ρP' rem wr rcr Q Xp k →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → ExclCtorHeap rf' →
      ShadowSmWf (initScalarBytes sm x n off ty.toTTy.bytes) →
      ShadowOk (initScalarBytes sm x n off ty.toTTy.bytes) rf'.ctx ρP' rf'.envP →
      ResStateInv σ' rem wr rcr →
      rf'.ctx = rf.ctx ∧ rf'.extH = rf.extH ∧
        rf'.envH = rf.envH ∧ (∀ z ≠ x, ρP' z = ρP z ∧ rf'.envP z = rf.envP z) →
      HWp Δh rt retTy J rf'.envH Qh Xh k σ') :
    HWp Δh rt retTy J rf.envH Qh Xh (LcCode.sset x n off y ty k) σ := by
  rw [perceusCodeWf.eq_13] at hwf
  rw [PRWp.eq_9] at hpr
  rw [HWp.eq_9]
  obtain ⟨vx, hgx, _, _, _, _, _, _⟩ := checkExcl_facts hchk
  obtain ⟨vy, hgy, hly_live⟩ := checkLive_facts hly
  simp only [Bool.and_eq_true, hgx, hgy] at hwf
  rcases hwf with ⟨⟨⟨⟨hty_sc, _⟩, hy_init⟩, hxy_ty⟩, hwf_k⟩
  simp only [Bool.not_eq_true', beq_iff_eq] at hxy_ty
  obtain ⟨⟨⟨hvx_ns, hvx_nt⟩, hvy_sc⟩, hvy_w⟩ := hxy_ty
  cases hρx : ρP x with
  | none => simp [hρx] at hpr
  | some xv =>
    cases hρy : ρP y with
    | none => simp [hρx, hρy] at hpr
    | some yv =>
      simp only [hρx, hρy] at hpr
      cases hset : xv.setScalar n off ty yv with
      | none => simp [hset] at hpr
      | some xv' =>
        simp only [hset] at hpr
        cases hynat : yv.toNat? with
        | none => simp [PVal.setScalar, hynat] at hset
        | some yNat =>
          cases xv with
          | ctor cidx fs pscal =>
            simp only [PVal.setScalar, hynat] at hset
            by_cases hfs_le : fs.length ≤ n
            · simp only [hfs_le, ite_true] at hset
              by_cases hbd_p : 8 * (n - fs.length) + off + ty.toTTy.bytes ≤ pscal.length
              · simp only [hbd_p, ite_true] at hset; cases hset
                have ⟨hvy_m, hyid⟩ := RcCtx.get?_mem hgy
                have hy_shd := hshd vy hvy_m hly_live
                simp only [hyid, hy_init, ite_true] at hy_shd
                have hE_y : rf.envP y = some yv := hy_shd ▸ hρy
                obtain ⟨py0, wy0, hpy0, hwy0, hrep_y, _⟩ := hinv.2.2.2.1 vy hvy_m hly_live
                rw [hyid, hE_y] at hpy0; cases hpy0
                simp only [ValRep, hvy_sc, ite_true, hvy_w] at hrep_y
                obtain ⟨hwy1, hnat_eq⟩ := scalarRep_toNat_eq hrep_y
                have heval_y : (rf.envH.evalArgAt (.var y) ty).bind Word.toNat? = some yNat := by
                  have hty1 : wy0.1 = ty.toTTy := by
                    rw [hwy1, scalarTy_toTTy_eq_bits hty_sc]
                  simp [HValEnv.evalArgAt, hyid ▸ hwy0, hty1, hnat_eq, hynat]
                let nbytes := ty.toTTy.bytes
                let patch := writeNatLE yNat nbytes
                have hpat_len : patch.length = nbytes := writeNatLE_length _ nbytes
                have hnb_pos : 0 < nbytes := scalar_toTTy_bytes_pos hty_sc
                have hstep := scalarMut_step (Δh := Δh) (J := J) (Qh := Qh) (Xh := Xh)
                  (x := x) (n := n) (off := off) (patch := patch)
                  (by simpa only [hpat_len, nbytes] using hwf_k) hchk
                  (by simpa only [writeNatLE_eq_pval, writeBytesAt_eq_pval, patch, nbytes]
                      using hpr)
                  hinv hclean hpo hnorc hpcb hsth hhih hepres hsbv hexcl hsm hshd hres
                  hgx hvx_ns hvx_nt hρx hfs_le (hpat_len ▸ hnb_pos)
                  (by simpa [hpat_len, nbytes] using hbd_p)
                  (fun hw' hp' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 => by
                    have hpat_eq : patch.length = ty.toTTy.bytes := hpat_len
                    rw [hpat_eq] at hw' h11 h12
                    exact hk hw' hp' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14)
                obtain ⟨addr, idx, hidx, hgx_bv, haddr, hotle, hflen_le, hbd_o, hwp_k⟩ := hstep
                rw [hgx_bv, heval_y]
                refine ⟨idx, hidx, haddr, hotle, hflen_le, ?_, ?_⟩
                · simpa [patch, hpat_len, nbytes] using hbd_o
                · simpa [patch, nbytes] using hwp_k
              · simp [hbd_p] at hset
            · simp [hfs_le] at hset
          | _ => simp [PVal.setScalar] at hset

/-- Stepwise simulation for `LcCode.setTag`: advances `HWp`, `RcInv`, and `ShadowOk`. -/
public theorem setTag_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {J : HJEnv} {Jp : PResJEnv}
    {Q : PResPost} {Xp : PResXPost} {Qh : HPost} {Xh : HXPost}
    {jps : List RcJpInfo} {rf rf0 : RcFrame} {σ σ0 : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr : Nat}
    {x cidx : Nat} {k : LcCode}
    (hwf : perceusCodeWf env retTy jps rf.ctx sm (LcCode.setTag x cidx k) = true)
    (hchk : rf.ctx.checkExcl x "setTag" = .ok ())
    (hpr : PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Q Xp (LcCode.setTag x cidx k))
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
      rf'.ctx = rf.ctx ∧ rf'.extH = rf.extH ∧
        rf'.envH = rf.envH ∧ (∀ z ≠ x, ρP' z = ρP z ∧ rf'.envP z = rf.envP z) →
      HWp Δh rt retTy J rf'.envH Qh Xh k σ') :
    HWp Δh rt retTy J rf.envH Qh Xh (LcCode.setTag x cidx k) σ := by
  rw [perceusCodeWf.eq_14] at hwf
  rw [PRWp.eq_10] at hpr
  rw [HWp.eq_10]
  obtain ⟨vx, hgx, hno, hpers, hrt, hown1, hex, hlx⟩ := checkExcl_facts hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, hgx, Bool.not_eq_true'] at hwf
  rcases hwf with ⟨⟨hcidx_le, hvx_ns, hvx_nt⟩, hwf_k⟩
  cases hρx : ρP x with
  | none => simp [hρx] at hpr
  | some xv =>
    cases xv with
    | ctor oldTag fs pscal =>
      simp only [hρx, Option.bind_some, PVal.setTag] at hpr
      obtain ⟨hscal, addr, idx, hidx, hE_x, hlen_eq, henvh_x, hgbv_x, hev, haddr, howf, _,
        hotle, _, hosc, horc1, hof⟩ := ctor_excl_obj_facts hinv hclean hshd hexcl hgx
        hno hpers hrt hown1 hex hlx hvx_ns hρx (Or.inr trivial)
      let o' : LcnfObj := { σ.objs[idx] with tag := cidx }
      have ho'w : o'.Wf := lcnfObj_wf_set_tag howf hotle hcidx_le
      have ho'ch : o'.childFields = σ.objs[idx].childFields := by
        simp [o', LcnfObj.childFields, hotle, hcidx_le]
      let σ' : HState := { σ with objs := σ.objs.set idx o' }
      have hnodup_objs := hinv.1.2
      have hvx_m := (RcCtx.get?_mem hgx).1
      have hdisj := excl_disjoint_facts hinv hclean hpo hpcb hvx_m hno hpers hrt hown1
        ((RcCtx.get?_mem hgx).2 ▸ henvh_x) (List.getElem_mem hidx) howf haddr horc1
      obtain ⟨_, _, hnot_self, _, hchild_ne, _⟩ := hdisj
      have hpres_p : ∀ q ∈ σ.objs, q.Wf → q.addr ≠ addr → ∃ q' ∈ σ'.objs, ObjDataEq q q' := by
        intro q hq hqwf hqne
        obtain ⟨j, hj, hgetj⟩ := obj_mem_idx hq
        have hjne : j ≠ idx := fun h => by subst h; exact hqne (hgetj.symm ▸ haddr)
        exact ⟨q, (list_mem_set_iff hidx).mpr (Or.inr ⟨j, hj, hjne, hgetj⟩), objDataEq_refl q hqwf⟩
      have hrep' : ValRep vx.ty (.ctor cidx fs hscal) (.i64 addr) σ'.objs := by
        have hnonsc : ¬vx.ty.isScalar = true := by simp [hvx_ns]
        simp only [ValRep, hnonsc]
        have hne_fs : ¬(fs = [] ∧ hscal = []) := by
          obtain ⟨_, _, hpx, hwx, hrx, _⟩ := hinv.2.2.2.1 vx hvx_m hlx
          have h1 := ((RcCtx.get?_mem hgx).2 ▸ henvh_x).symm.trans hwx; cases h1
          have h2 := ((RcCtx.get?_mem hgx).2 ▸ hE_x).symm.trans hpx; cases h2
          simp only [ValRep, hnonsc] at hrx
          obtain ⟨bvp, hwbp, hox, _⟩ := hrx; cases hwbp
          rcases hox with ⟨_, _, _, htb⟩ | ⟨hne, _⟩
          · rw [htb] at hev; exact absurd hev (boxNat_and1_ne_zero _)
          · exact hne
        refine ⟨addr, rfl, Or.inr ⟨hne_fs, o', (list_mem_set_iff hidx).mpr (Or.inl rfl),
          haddr, ho'w, rfl, hcidx_le, hosc, ?_⟩, fun _ => hev,
          fun ht => by rw [ht] at hvx_nt; exact absurd hvx_nt (by decide)⟩
        refine objFieldsRep_mono_pred (P := fun a => a ≠ addr) hpres_p hchild_ne hof
          (fun f hf _ heq => ?_)
        apply hnot_self
        have hcf : σ.objs[idx].childFields = σ.objs[idx].fields := by
          simp [LcnfObj.childFields, hotle]
        rw [hcf]; exact heq ▸ hf
      have hcore := exclDataTagMut_rcInv hinv hclean hpo hnorc hpcb hsth hhih hepres hsbv hexcl
        hgx hno hpers hrt hown1 hex henvh_x hev hidx haddr horc1 o' ho'w haddr horc1 ho'ch
        (.ctor cidx fs hscal) hrep'
      obtain ⟨hinv', hclean', hpo', hnorc', hpcb', hsth', hhih', hepres', hsbv', hexcl'⟩ := hcore
      have hres' : ResStateInv σ' rem wr rcr := by
        refine ⟨hres.1, by simpa [σ'] using hres.2.1, ?_⟩
        have hle : maxObjRc (σ.objs.set idx o') ≤ maxObjRc σ.objs := by
          apply maxObjRc_set_le; intro _; simp [o', horc1]
        have hmax_le : Nat.max 1 (maxObjRc (σ.objs.set idx o')) ≤ Nat.max 1 (maxObjRc σ.objs) :=
          Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hle (Nat.le_max_right _ _)⟩
        have := hres.2.2; simp only [σ']; omega
      have hshd' : ShadowOk sm rf.ctx (ρP.set x (.ctor cidx fs pscal))
          (rf.envP.set x (.ctor cidx fs hscal)) := by
        refine shadowOk_update_same_shape hshd ?_ ?_
        · intro hi
          have hx := hshd vx hvx_m hlx
          simp only [(RcCtx.get?_mem hgx).2, hi, ite_true] at hx
          rw [hρx, hE_x] at hx; cases hx; rfl
        · intro sz m hf
          have hx := hshd vx hvx_m hlx
          have hni : isVarScalarInit sm x = false := by
            cases h : isVarScalarInit sm x
            · rfl
            · rw [isVarScalarInit_iff_find_none] at h; rw [h] at hf; cases hf
          simp only [(RcCtx.get?_mem hgx).2, hni, Bool.false_eq_true, ite_false] at hx
          obtain ⟨sz0, m0, hf0, c0, fs0, ps0, hs0, hρ0, hE0, hl1, hl2, hsz, hag⟩ := hx
          rw [hf] at hf0; cases hf0
          rw [hρx] at hρ0; cases hρ0
          rw [hE_x] at hE0; cases hE0
          exact ⟨cidx, fs, pscal, hscal, rfl, rfl, hl1, hl2, hsz, hag⟩
      rw [hgbv_x]
      refine ⟨idx, hidx, haddr, hotle, hcidx_le, ?_⟩
      exact hk
        (rf' := { rf with envP := rf.envP.set x (.ctor cidx fs hscal) }) (σ' := σ')
        (ρP' := ρP.set x (.ctor cidx fs pscal))
        hwf_k hpr hinv' hclean' hpo' hnorc' hpcb' hsth' hhih' hepres' hsbv' hexcl' hsm hshd' hres'
        ⟨rfl, rfl, rfl, fun z hzx => ⟨by simp [PValEnv.set, hzx], by simp [PValEnv.set, hzx]⟩⟩
    | _ => simp [hρx, PVal.setTag] at hpr

end ScalarAndTagSteps


end LeanQbe.T.LeanLCNF.Sem
