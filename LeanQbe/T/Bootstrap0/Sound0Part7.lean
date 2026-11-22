module

public import LeanQbe.T.Bootstrap0.Sound0Part6

/-!
# Bootstrap Stage B (`Sound0Part7`): Lockstep `PrePass0` ↔ `Rega0` Base, `init`, `term`, & `lin`

Establishes the complete lockstep invariant (`RegaStepInv0`) connecting `PrePass0` (`preRunAux0`,
`compileFnPre0`) and `Rega0` (`regaRunAux0`, `compileFn0`) under `fn.okGuardsFull = true`:
* Every worklist item `(p, t, m)` carries exact typing (`WfNode0`), label metadata (`LblInfo0`),
  `SlotPoolInv0`, live/free slot disjointness, and `LaterLiveCovered0` across `work`.
* Bug C (`seenJnz` / `jnzGroupSafeWork0`) guarantees `ctrl.lblSlots.size = ctrl.nextLbl.toNat` at
  every `.group`.
* Base step cases (`regaStepInv0_init`, `regaStep0_term`, `regaStep0_lin`); `.jnz`, `.group`, and
  `compileFn0_maxSlots_lt` follow in `Sound0Part8`
  (x64-only `Compiler0` verification targeting `LeanQbe.T.Amd64.ScalarTarg` via `Sound0Part1`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T

/-! ## 1. Small Arithmetic, Array, & Bug C Worklist Unfolding Helpers -/

theorem u32_ext7 {a b : UInt32} (h : a.toNat = b.toNat) : a = b :=
  UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

theorem u32_toNat_ofNat7 (n : Nat) : (UInt32.ofNat n).toNat = n % 2 ^ 32 := by
  rw [← UInt32.toNat_toBitVec]; exact BitVec.toNat_ofNat n 32

theorem u32_sub1_toNat7 {x : UInt32} (hx : 0 < x.toNat) :
    (x - 1).toNat = x.toNat - 1 := by
  refine UInt32.toNat_sub_of_le x 1 ?_
  exact UInt32.le_iff_toNat_le.mpr (by rw [UInt32.toNat_one]; exact hx)

theorem u32_add1_toNat7 {x : UInt32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt hx]

theorem u32_add_ofNat_lt7 {a : UInt32} {m : Nat} (hlt : a.toNat + m < 2 ^ 32) :
    (a + UInt32.ofNat m).toNat = a.toNat + m := by
  rw [UInt32.toNat_add, u32_toNat_ofNat7,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hlt), Nat.mod_eq_of_lt hlt]

theorem u32_ofNat_add_eq7 (a : UInt32) (j : Nat) (hlt : a.toNat + j < 2 ^ 32) :
    UInt32.ofNat (a.toNat + j) = a + UInt32.ofNat j := by
  apply u32_ext7
  rw [u32_toNat_ofNat7, u32_add_ofNat_lt7 hlt, Nat.mod_eq_of_lt hlt]

theorem arrPush_getD7 {α : Type} (arr : Array α) (x d : α) (j : Nat) :
    (arr.push x).getD j d =
      if j < arr.size then arr.getD j d else if j = arr.size then x else d := by
  dsimp only [Array.getD]
  by_cases hj : j < arr.size
  · have hlt : j < (arr.push x).size := by rw [Array.size_push]; omega
    simp only [hj, hlt, ↓reduceDIte]; exact Array.getElem_push_lt hj
  · by_cases heq : j = arr.size
    · subst heq
      have hlt : arr.size < (arr.push x).size := by rw [Array.size_push]; omega
      simp only [Nat.lt_irrefl, hlt, ↓reduceDIte]; exact Array.getElem_push_eq
    · have hge : ¬ j < (arr.push x).size := by rw [Array.size_push]; omega
      simp only [hj, heq, hge, ↓reduceDIte, ite_false]

theorem listGetD_eq_getElem7 {α : Type} :
    ∀ (xs : List α) (d : α) (i : Nat) (hi : i < xs.length), xs.getD i d = xs[i]'hi
  | [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, d, k + 1, hi => listGetD_eq_getElem7 xs d k (Nat.lt_of_succ_lt_succ hi)

theorem nodup_of_getD7 {α : Type} :
    ∀ (xs : List α) (d : α),
      (∀ i j, i < xs.length → j < xs.length → i < j → xs.getD i d ≠ xs.getD j d) →
      xs.Nodup
  | [], _, _ => List.nodup_nil
  | x :: rest, d, h => by
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_of_getD7 rest d fun i j hi hj hij => ?_⟩
    · obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hm
      have hne := h 0 (k + 1) (by simp) (by simp [hk]) (Nat.zero_lt_succ k)
      rw [listGetD_eq_getElem7 (x :: rest) d 0 (Nat.zero_lt_succ _),
        listGetD_eq_getElem7 (x :: rest) d (k + 1) (Nat.succ_lt_succ hk)] at hne
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, he] at hne
      exact hne rfl
    · have hne := h (i + 1) (j + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj)
        (Nat.succ_lt_succ hij)
      rw [listGetD_eq_getElem7 (x :: rest) d (i + 1) (Nat.succ_lt_succ hi),
        listGetD_eq_getElem7 (x :: rest) d (j + 1) (Nat.succ_lt_succ hj)] at hne
      simp only [List.getElem_cons_succ, listGetD_eq_getElem7 rest d i hi,
        listGetD_eq_getElem7 rest d j hj] at hne ⊢
      exact hne

private theorem jnzNat_pos (seen : Bool) (n : TFlat0) (rest : List TFlat0) :
    jnzGroupSafeWork0 seen (n :: rest) =
      jnzGroupSafeWorkNat0 seen ((workNodeCount0 (n :: rest) - 1) + 1) (n :: rest) := by
  have hpos : 0 < workNodeCount0 (n :: rest) := by
    dsimp only [workNodeCount0]; have := nodeCount0_pos n; omega
  dsimp only [jnzGroupSafeWork0]
  exact jnzGroupSafeWorkNat0_fuel_indep _ _ seen (n :: rest) (by omega) (by omega)

theorem jnzGroupSafeWork0_term (seen : Bool) {n : TFlat0} (ht : isTerm0 n = true)
    (rest : List TFlat0) :
    jnzGroupSafeWork0 seen (n :: rest) = jnzGroupSafeWork0 seen rest := by
  rw [jnzNat_pos]
  cases n <;> simp [isTerm0] at ht
  all_goals
    dsimp only [jnzGroupSafeWorkNat0, jnzGroupSafeWork0]
    exact jnzGroupSafeWorkNat0_fuel_indep _ _ seen rest
      (by dsimp only [workNodeCount0, nodeCount0]; omega) (Nat.le_refl _)

theorem jnzGroupSafeWork0_lin (seen : Bool) {n : TFlat0} (hlin : isTerm0 n = false)
    (hnj : ∀ c t e, n ≠ .jnz c t e) (hng : ∀ bs k, n ≠ .group bs k) (rest : List TFlat0) :
    jnzGroupSafeWork0 seen (n :: rest) = jnzGroupSafeWork0 seen (linK0 n :: rest) := by
  rw [jnzNat_pos]
  cases n with
  | let1 _ _ _ | let2Umulw64 _ _ _ | load _ _ _ | store _ _ _ _ | call _ _ _ _ _ =>
    dsimp only [jnzGroupSafeWorkNat0, jnzGroupSafeWork0, linK0]
    exact jnzGroupSafeWorkNat0_fuel_indep _ _ seen _
      (by dsimp only [workNodeCount0, nodeCount0]; omega) (Nat.le_refl _)
  | jnz c t e => exact absurd rfl (hnj c t e)
  | group bs k => exact absurd rfl (hng bs k)
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt => simp [isTerm0] at hlin

theorem jnzGroupSafeWork0_jnz (seen : Bool) (c : Arg0) (t e : TFlat0)
    (rest : List TFlat0) :
    jnzGroupSafeWork0 seen (.jnz c t e :: rest) = jnzGroupSafeWork0 true (e :: t :: rest) := by
  rw [jnzNat_pos]
  dsimp only [jnzGroupSafeWorkNat0, jnzGroupSafeWork0]
  exact jnzGroupSafeWorkNat0_fuel_indep _ _ true _
    (by dsimp only [workNodeCount0, nodeCount0]; omega) (Nat.le_refl _)

theorem jnzGroupSafeWork0_group (seen : Bool) (bs : List (List Ty0 × TFlat0))
    (k : TFlat0) (rest : List TFlat0) :
    jnzGroupSafeWork0 seen (.group bs k :: rest) =
      (!seen && jnzGroupSafeWork0 seen (k :: (bs.map Prod.snd ++ rest))) := by
  rw [jnzNat_pos]
  dsimp only [jnzGroupSafeWorkNat0, jnzGroupSafeWork0]
  congr 1
  exact jnzGroupSafeWorkNat0_fuel_indep _ _ seen _
    (by dsimp only [workNodeCount0, nodeCount0]
        rw [workNodeCount0_append, workNodeCount0_map_snd]; omega)
    (Nat.le_refl _)

/-! ## 2. Metadata, Liveness, Waiting Labels, & Lockstep Invariant -/

/-- Compiled block-label slot metadata tracked across `Rega0` (`Sound0Part7` & `Part8`). -/
structure LblInfo0 where
  lbl : UInt32
  pts : List Ty0
  tgts : List UInt32
  nxt : UInt32
  outerVenv : List UInt32
  outerVT : List Ty0
  outerNextVid : UInt32
  waiting : Bool

/-- Semantic metadata paired 1-to-1 with each `RegaTask0` / `PreItem0` in the worklist. -/
structure TaskMeta0 where
  vT : List Ty0
  lT : List (List Ty0)
  gl : List LblInfo0
  entryInfo : Option LblInfo0

/-- Variables live in task `(p, t)` under `esc` and remaining-use state `(preSt, st)`. -/
@[expose] def LiveInTask0 (esc : Array Nat) (preSt : PreSt0) (st : RegaSt0)
    (p : PreItem0) (t : RegaTask0) (v : Nat) : Prop :=
  (esc.getD v 0 = 1 ∧ UInt32.ofNat v ∈ t.venv) ∨
  (esc.getD v 0 = 0 ∧ p.scope.toNat = preSt.defScope.getD v 0 ∧ 0 < st.remUses.getD v 0)

/-- Variables whose `defScope` matches an active item in `preWork`. -/
@[expose] def ActiveDefScope0 (preSt : PreSt0) (preWork : List PreItem0) (v : Nat) : Prop :=
  v < preSt.nextVid.toNat ∧ ∃ q ∈ preWork, q.scope.toNat = preSt.defScope.getD v 0

/-- Structural and slot-disjointness well-formedness for a compiled `.group` block `LblInfo0`. -/
@[expose] def LblInfoOk0 (esc : Array Nat) (st : RegaSt0) (ctrl : CtrlSt0)
    (info : LblInfo0) : Prop :=
  1 ≤ info.lbl.toNat ∧ info.lbl.toNat < ctrl.nextLbl.toNat ∧
  ctrl.lblSlots.getD info.lbl.toNat [] = info.tgts ∧
  info.tgts.length = info.pts.length ∧ info.tgts.Nodup ∧
  info.outerNextVid.toNat + info.pts.length ≤ st.nextVid.toNat ∧
  (∀ k < info.pts.length,
    arrGetU0 st.vslot (info.outerNextVid + UInt32.ofNat k) = info.tgts.getD k 0) ∧
  info.nxt.toNat ≤ st.maxSlots.toNat ∧
  (∀ s ∈ info.tgts, s.toNat < info.nxt.toNat) ∧
  info.outerVenv.length = info.outerVT.length ∧
  (∀ w ∈ info.outerVenv, w.toNat < info.outerNextVid.toNat) ∧
  (∀ s ∈ info.tgts, ∀ w < info.outerNextVid.toNat, esc.getD w 0 = 1 →
    UInt32.ofNat w ∈ info.outerVenv → arrGetU0 st.vslot (UInt32.ofNat w) ≠ s)

/-- Per-task lockstep & slot invariant for `(p, t, m)` at `(preSt, st, ctrl)`. -/
@[expose] def TaskMetaOk0 (ctx : LegalCtx0) (maxBd : Nat) (esc : Array Nat) (preSt : PreSt0)
    (st : RegaSt0) (ctrl : CtrlSt0) (p : PreItem0) (t : RegaTask0) (m : TaskMeta0) : Prop :=
  p.node = t.node ∧ p.venv = t.venv ∧
  t.venv.length = m.vT.length ∧ (∀ v ∈ t.venv, v.toNat < st.nextVid.toNat) ∧
  t.lenv.length = m.lT.length ∧ m.gl.length = t.lenv.length ∧
  (∀ (i : Nat) (h1 : i < m.gl.length) (h2 : i < t.lenv.length) (h3 : i < m.lT.length),
    m.gl[i].lbl = t.lenv[i] ∧ m.gl[i].pts = m.lT[i]) ∧
  WfNode0 ctx m.vT m.lT t.node ∧ t.node.sigLensFitU32 = true ∧
  t.node.singleBlockGroups = true ∧ t.node.noNegBool = true ∧
  SlotPoolInv0 t.freeSlots t.nextSlot st.maxSlots maxBd ∧
  t.nextSlot.toNat ≤ st.nextVid.toNat ∧
  (∀ info ∈ m.gl, LblInfoOk0 esc st ctrl info) ∧
  (∀ info ∈ m.gl, info.waiting = true →
    (∀ s ∈ info.tgts, s.toNat < t.nextSlot.toNat ∧ s ∉ t.freeSlots) ∧
    (∀ v < st.nextVid.toNat, LiveInTask0 esc preSt st p t v →
      arrGetU0 st.vslot (UInt32.ofNat v) ∉ info.tgts)) ∧
  (match m.entryInfo with
   | none => True
   | some info =>
     t.lblId = info.lbl ∧ info ∈ m.gl ∧ info.waiting = false ∧
     t.venv = pushFreshVids0 info.pts.length info.outerNextVid info.outerVenv ∧
     m.vT = pushTys0 info.pts info.outerVT ∧ info.nxt = t.nextSlot) ∧
  (∀ v < st.nextVid.toNat, LiveInTask0 esc preSt st p t v →
    (arrGetU0 st.vslot (UInt32.ofNat v)).toNat < t.nextSlot.toNat ∧
    arrGetU0 st.vslot (UInt32.ofNat v) ∉ t.freeSlots ∧
    ∀ w < st.nextVid.toNat, w ≠ v → LiveInTask0 esc preSt st p t w →
      arrGetU0 st.vslot (UInt32.ofNat w) ≠ arrGetU0 st.vslot (UInt32.ofNat v))

/-- Full worklist lockstep invariant relating `preWork`, `work`, `metas`, `preRes`, and `st`. -/
structure RegaStepInv0 (ctx : LegalCtx0) (fnIdx : UInt32) (fnMaxJump : Nat) (preRes : PreSt0)
    (nextSc : UInt32) (preSt : PreSt0) (preWork : List PreItem0) (seenJnz : Bool)
    (st : RegaSt0) (ctrl : CtrlSt0) (work : List RegaTask0) (metas : List TaskMeta0) :
    Prop where
  preRes_nv : preRes.nextVid.toNat < 2 ^ 31
  preRes_ds_sz : preRes.defScope.size = preRes.nextVid.toNat
  preRes_us_sz : preRes.uses.size = preRes.nextVid.toNat
  preRes_es_sz : preRes.escaped.size = preRes.nextVid.toNat
  preRes_es_bit : ∀ v < preRes.nextVid.toNat,
    preRes.escaped.getD v 0 = 0 ∨ preRes.escaped.getD v 0 = 1
  preRes_us_bd : ∀ v < preRes.nextVid.toNat, preRes.uses.getD v 0 < 2 ^ 31
  maxBd_lt : preRes.nextVid.toNat + fnMaxJump + 1 < 2 ^ 31
  pre_inv : PreWorkInv0 ctx nextSc preSt preWork
  pre_run : (preRunAux0 (UInt32.ofNat (workNodeCount0 (preWork.map PreItem0.node)))
    nextSc preSt preWork).2 = preRes
  len_pw : preWork.length = work.length
  len_mw : metas.length = work.length
  seenJnz_safe : jnzGroupSafeWork0 seenJnz (work.map RegaTask0.node) = true
  seenJnz_ctrl : ctrl.lblSlots.size = ctrl.nextLbl.toNat
  maxJump_bd : workMaxJumpArity0 (work.map RegaTask0.node) ≤ fnMaxJump
  ctrl_fn : ctrl.fnIdx = fnIdx
  ctrl_nl : 1 ≤ ctrl.nextLbl.toNat ∧
    ctrl.nextLbl.toNat + workNodeCount0 (work.map RegaTask0.node) < 2 ^ 31
  st_nv : st.nextVid = preSt.nextVid
  st_vslot_sz : st.vslot.size = st.nextVid.toNat
  st_rem_sz : st.remUses.size = preRes.nextVid.toNat
  st_maxSl_le : st.maxSlots.toNat ≤ preRes.nextVid.toNat + fnMaxJump
  st_rem_le : ∀ v < preRes.nextVid.toNat, st.remUses.getD v 0 ≤ preRes.uses.getD v 0
  st_rem_future : ∀ v, st.nextVid.toNat ≤ v → v < preRes.nextVid.toNat →
    st.remUses.getD v 0 = preRes.uses.getD v 0
  st_rem_active : ∀ v < st.nextVid.toNat, preRes.escaped.getD v 0 = 0 →
    ActiveDefScope0 preSt preWork v →
    st.remUses.getD v 0 =
      sameScopeSpineSum0 (UInt32.ofNat v) (preSt.defScope.getD v 0) preSt.nextVid preWork
  items_ok : ∀ (i : Nat) (h1 : i < preWork.length) (h2 : i < work.length)
    (h3 : i < metas.length),
    TaskMetaOk0 ctx (preRes.nextVid.toNat + fnMaxJump) preRes.escaped preSt st ctrl
      preWork[i] work[i] metas[i]
  later_live : ∀ (i j : Nat) (hi1 : i < preWork.length) (hi2 : i < work.length)
    (hi3 : i < metas.length) (hj1 : j < preWork.length) (hj2 : j < work.length),
    i < j → ∀ w < st.nextVid.toNat,
    LiveInTask0 preRes.escaped preSt st preWork[j] work[j] w →
    LiveInTask0 preRes.escaped preSt st preWork[i] work[i] w ∨
    ∃ info ∈ metas[i].gl, info.waiting = true ∧
      arrGetU0 st.vslot (UInt32.ofNat w) ∈ info.tgts

/-! ## 3. Shared Lookup, Disjointness, & Monotonicity Helpers -/

theorem RegaStepInv0.preRes_uses_lt_bd {ctx : LegalCtx0} {fnIdx : UInt32} {fnMaxJump : Nat}
    {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0} {preWork : List PreItem0}
    {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0} {work : List RegaTask0}
    {metas : List TaskMeta0}
    (h : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt preWork seenJnz st ctrl
      work metas) :
    st.nextVid.toNat + workBinderCount0 (work.map RegaTask0.node) = preRes.nextVid.toNat := by
  have hnodes : work.map RegaTask0.node = preWork.map PreItem0.node := by
    apply List.ext_getElem (by simp [h.len_pw])
    intro i hi1 hi2
    simp only [List.getElem_map] at hi1 hi2 ⊢
    have htm := h.items_ok i (by simp at hi2; exact hi2) (by simp at hi1; exact hi1)
      (by have := h.len_mw; simp only [List.length_map] at hi1; omega)
    exact htm.1.symm
  have hpre := preRunAux0_inv ctx (workNodeCount0 (preWork.map PreItem0.node))
    (UInt32.ofNat (workNodeCount0 (preWork.map PreItem0.node))) nextSc preSt preWork rfl
    (by
      have := h.pre_inv.nextSc_bound
      rw [u32_toNat_ofNat7, Nat.mod_eq_of_lt (by omega)]
      exact Nat.le_refl _)
    h.pre_inv
  dsimp only at hpre
  rw [h.pre_run] at hpre
  rw [h.st_nv, hnodes, ← hpre.1]

theorem taskMetaOk0_jump_lblInfo {ctx : LegalCtx0} {maxBd : Nat} {esc : Array Nat}
    {preSt : PreSt0} {st : RegaSt0} {ctrl : CtrlSt0} {p : PreItem0} {t : RegaTask0}
    {m : TaskMeta0} {j : UInt32} {pts : List Ty0}
    (hm : TaskMetaOk0 ctx maxBd esc preSt st ctrl p t m)
    (hlg : listGetSig0 m.lT j = some pts) :
    ∃ info ∈ m.gl,
      info.lbl = listGetU32 t.lenv j ∧ info.pts = pts ∧ LblInfoOk0 esc st ctrl info := by
  obtain ⟨_, _, _, _, hllen, hgl_len, hgi, _, _, _, _, _, _, hinfo_ok, _, _, _⟩ := hm
  rw [listGetSig0_eq_listGet?] at hlg
  have hjn : j.toNat < m.lT.length := Nat.lt_of_not_le fun hge' => False.elim <| by
    have hnone_of : ∀ (xs : List (List Ty0)) (k : Nat), xs.length ≤ k → listGet? xs k = none := by
      intro xs
      induction xs with
      | nil => intro k _; cases k <;> rfl
      | cons _ _ ih =>
        intro k hk
        cases k with
        | zero => simp only [List.length_cons] at hk; omega
        | succ k' =>
          simp only [List.length_cons] at hk
          exact ih k' (by omega)
    rw [hnone_of m.lT j.toNat hge'] at hlg
    cases hlg
  have hm_eq : m.lT[j.toNat]'hjn = pts := by
    have hget : ∀ (xs : List (List Ty0)) (k : Nat) (hk : k < xs.length),
        listGet? xs k = some (xs[k]'hk) := by
      intro xs
      induction xs with
      | nil => intro k hk; exact absurd hk (Nat.not_lt_zero _)
      | cons x rest ih =>
        intro k hk
        cases k with
        | zero => rfl
        | succ k' => exact ih k' (Nat.lt_of_succ_lt_succ hk)
    rw [hget m.lT j.toNat hjn] at hlg
    exact Option.some.inj hlg
  have h1 : j.toNat < m.gl.length := by rw [hgl_len, hllen]; exact hjn
  have h2 : j.toNat < t.lenv.length := by rw [hllen]; exact hjn
  have hgl := hgi j.toNat h1 h2 hjn
  refine ⟨m.gl[j.toNat]'h1, List.getElem_mem h1, ?_, by rw [hgl.2, hm_eq],
    hinfo_ok _ (List.getElem_mem h1)⟩
  rw [listGetU32_eq_listGetD, listGetD_eq_getElem7 t.lenv 0 j.toNat h2, hgl.1]

theorem lblInfoOk0_mono {esc : Array Nat} {st st' : RegaSt0} {ctrl ctrl' : CtrlSt0}
    {info : LblInfo0} (h : LblInfoOk0 esc st ctrl info)
    (hnl : ctrl.nextLbl.toNat ≤ ctrl'.nextLbl.toNat)
    (hls : ∀ l, 1 ≤ l → l < ctrl.nextLbl.toNat →
      ctrl'.lblSlots.getD l [] = ctrl.lblSlots.getD l [])
    (hnv : st.nextVid.toNat ≤ st'.nextVid.toNat)
    (hms : st.maxSlots.toNat ≤ st'.maxSlots.toNat)
    (hvsl : ∀ v < st.nextVid.toNat, arrGetU0 st'.vslot (UInt32.ofNat v) =
      arrGetU0 st.vslot (UInt32.ofNat v)) :
    LblInfoOk0 esc st' ctrl' info := by
  obtain ⟨hl1, hl2, hget, hlen, hnd, hnv_o, hvsl_o, hmxs, hslts, hov_len, hov_lt, hdisj⟩ := h
  refine ⟨hl1, Nat.lt_of_lt_of_le hl2 hnl, ?_, hlen, hnd, Nat.le_trans hnv_o hnv, ?_,
    Nat.le_trans hmxs hms, hslts, hov_len, hov_lt, ?_⟩
  · rw [hls info.lbl.toNat hl1 hl2, hget]
  · intro k hk
    have hk_lt : info.outerNextVid.toNat + k < st.nextVid.toNat := Nat.lt_of_lt_of_le
      (Nat.add_lt_add_left hk _) hnv_o
    have heq_idx : info.outerNextVid + UInt32.ofNat k =
        UInt32.ofNat (info.outerNextVid.toNat + k) := by
      apply u32_ext7
      rw [u32_add_ofNat_lt7 (Nat.lt_trans hk_lt (UInt32.toNat_lt st.nextVid)),
        u32_toNat_ofNat7, Nat.mod_eq_of_lt (Nat.lt_trans hk_lt (UInt32.toNat_lt st.nextVid))]
    rw [heq_idx, hvsl _ hk_lt, ← heq_idx]
    exact hvsl_o k hk
  · intro s hs w hw hesc hwmem
    have hw_lt : w < st.nextVid.toNat := Nat.lt_of_lt_of_le hw
      (Nat.le_trans (Nat.le_add_right _ _) hnv_o)
    rw [hvsl w hw_lt]
    exact hdisj s hs w hw hesc hwmem

theorem preRunAux0_sub_active {ctx : LegalCtx0} {preRes : PreSt0} {nextSc : UInt32}
    {preSt : PreSt0} {preWork : List PreItem0}
    (hpre_inv : PreWorkInv0 ctx nextSc preSt preWork)
    (hpre_run : (preRunAux0 (UInt32.ofNat (workNodeCount0 (preWork.map PreItem0.node)))
      nextSc preSt preWork).2 = preRes) :
    (preRes.nextVid.toNat = preSt.nextVid.toNat + workBinderCount0 (preWork.map PreItem0.node) ∧
    preRes.defScope.size = preRes.nextVid.toNat ∧
    preRes.uses.size = preRes.nextVid.toNat ∧
    preRes.escaped.size = preRes.nextVid.toNat ∧
    (∀ v < preSt.nextVid.toNat, preRes.defScope.getD v 0 = preSt.defScope.getD v 0) ∧
    (∀ v < preSt.nextVid.toNat, preRes.uses.getD v 0 = preSt.uses.getD v 0 +
      sameScopeSpineSum0 (UInt32.ofNat v) (preSt.defScope.getD v 0) preSt.nextVid preWork)) ∧
    (∀ v < preSt.nextVid.toNat, preRes.escaped.getD v 0 = 0 →
      ∀ p ∈ preWork,
        if p.scope.toNat = preSt.defScope.getD v 0 then
          astUses0 (UInt32.ofNat v) p.venv preSt.nextVid p.node =
            spineUses0 (UInt32.ofNat v) p.venv preSt.nextVid p.node
        else
          astUses0 (UInt32.ofNat v) p.venv preSt.nextVid p.node = 0) := by
  have hle : workNodeCount0 (preWork.map PreItem0.node) ≤
      (UInt32.ofNat (workNodeCount0 (preWork.map PreItem0.node))).toNat := by
    have := hpre_inv.nextSc_bound
    rw [u32_toNat_ofNat7, Nat.mod_eq_of_lt (by omega)]
    exact Nat.le_refl _
  have h1 := preRunAux0_inv ctx (workNodeCount0 (preWork.map PreItem0.node))
    (UInt32.ofNat (workNodeCount0 (preWork.map PreItem0.node))) nextSc preSt preWork rfl hle
    hpre_inv
  have h2 := preRunAux0_no_esc_uses ctx (workNodeCount0 (preWork.map PreItem0.node))
    (UInt32.ofNat (workNodeCount0 (preWork.map PreItem0.node))) nextSc preSt preWork rfl hle
    hpre_inv
  dsimp only at h1 h2
  rw [hpre_run] at h1 h2
  obtain ⟨h1_nv, h1_ds_sz, h1_us_sz, h1_es_sz, _, _, h1_ds_eq, _, _, _, _, h1_us_eq⟩ := h1
  exact ⟨⟨h1_nv, h1_ds_sz, h1_us_sz, h1_es_sz, h1_ds_eq, h1_us_eq⟩, h2⟩

theorem preRun_step_eq7 {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0}
    {curPre : PreItem0} {restPre : List PreItem0}
    (hbd : nextSc.toNat + 2 * workNodeCount0 ((curPre :: restPre).map PreItem0.node) < 2 ^ 31)
    (hrun : (preRunAux0
      (UInt32.ofNat (workNodeCount0 ((curPre :: restPre).map PreItem0.node)))
      nextSc preSt (curPre :: restPre)).2 = preRes) :
    let preSt1 := preNoteNode0 curPre.scope curPre.venv curPre.node preSt
    let out := preStepPush0 curPre preSt1 nextSc restPre
    (preRunAux0 (UInt32.ofNat (workNodeCount0 (out.work.map PreItem0.node)))
      out.nextScope out.st out.work).2 = preRes := by
  intro preSt1 out
  have hN_pos : 0 < workNodeCount0 ((curPre :: restPre).map PreItem0.node) := by
    rw [List.map_cons]; dsimp only [workNodeCount0]; have := nodeCount0_pos curPre.node; omega
  have hfne : UInt32.ofNat (workNodeCount0 ((curPre :: restPre).map PreItem0.node)) ≠ 0 := by
    intro hz; have hn := congrArg UInt32.toNat hz
    rw [u32_toNat_ofNat7, Nat.mod_eq_of_lt (by omega), UInt32.toNat_zero] at hn; omega
  have hdef := preRunAux0_succ hfne nextSc preSt curPre restPre
  have hcnt := preWorkNodeCount0_children curPre preSt1 nextSc restPre
  change workNodeCount0 (out.work.map PreItem0.node) + 1 = _ at hcnt
  have h0 : 0 < (UInt32.ofNat
      (workNodeCount0 ((curPre :: restPre).map PreItem0.node))).toNat := by
    rw [u32_toNat_ofNat7, Nat.mod_eq_of_lt (by omega)]; exact hN_pos
  have hf1 : UInt32.ofNat (workNodeCount0 ((curPre :: restPre).map PreItem0.node)) - 1 =
      UInt32.ofNat (workNodeCount0 (out.work.map PreItem0.node)) := by
    apply u32_ext7
    rw [u32_sub1_toNat7 h0, u32_toNat_ofNat7, u32_toNat_ofNat7,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hf1] at hdef
  rw [hdef] at hrun
  exact hrun

private theorem activeDefScope0_live_of_witness {ctx : LegalCtx0} {fnIdx : UInt32}
    {fnMaxJump : Nat} {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0}
    {preWork : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {work : List RegaTask0} {metas : List TaskMeta0}
    (h : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt preWork seenJnz st ctrl
      work metas)
    {v : Nat} (_hv : v < st.nextVid.toNat) (hesc : preRes.escaped.getD v 0 = 0)
    (hact : ActiveDefScope0 preSt preWork v) (hrem : 0 < st.remUses.getD v 0) :
    ∃ (i : Nat) (_h1 : i < preWork.length) (_h2 : i < work.length),
      i < metas.length ∧ LiveInTask0 preRes.escaped preSt st preWork[i] work[i] v := by
  obtain ⟨q, hq, hq_sc⟩ := hact.2
  obtain ⟨i, hi1, rfl⟩ := List.mem_iff_getElem.mp hq
  have hi2 : i < work.length := h.len_pw ▸ hi1
  have hi3 : i < metas.length := h.len_mw.symm ▸ hi2
  exact ⟨i, hi1, hi2, hi3, Or.inr ⟨hesc, hq_sc, hrem⟩⟩

private theorem head_protects_later_live {ctx : LegalCtx0} {fnIdx : UInt32} {fnMaxJump : Nat}
    {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0} {preWork : List PreItem0}
    {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0} {cur : RegaTask0}
    {rest : List RegaTask0} {metas : List TaskMeta0}
    (h : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt preWork seenJnz st ctrl
      (cur :: rest) metas)
    {i : Nat} (hi1 : i < preWork.length) (hi2 : i < (cur :: rest).length)
    {w : Nat} (hw : w < st.nextVid.toNat)
    (hlive : LiveInTask0 preRes.escaped preSt st preWork[i] (cur :: rest)[i] w) :
    (arrGetU0 st.vslot (UInt32.ofNat w)).toNat < cur.nextSlot.toNat ∧
    arrGetU0 st.vslot (UInt32.ofNat w) ∉ cur.freeSlots := by
  have h01 : 0 < preWork.length := by rw [h.len_pw]; exact Nat.zero_lt_succ _
  have h02 : 0 < (cur :: rest).length := Nat.zero_lt_succ _
  have h03 : 0 < metas.length := by rw [h.len_mw]; exact Nat.zero_lt_succ _
  have htm0 := h.items_ok 0 h01 h02 h03
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hwait0, _, hlive0⟩ := htm0
  cases i with
  | zero => exact ⟨(hlive0 w hw hlive).1, (hlive0 w hw hlive).2.1⟩
  | succ i' =>
    have hcov := h.later_live 0 (i' + 1) h01 h02 h03 hi1 hi2 (Nat.zero_lt_succ i') w hw hlive
    rcases hcov with hl0 | ⟨info, hinfo, hwait, hsl_mem⟩
    · exact ⟨(hlive0 w hw hl0).1, (hlive0 w hw hl0).2.1⟩
    · exact (hwait0 info hinfo hwait).1 _ hsl_mem

theorem activeDefScope0_live_slots_ok {ctx : LegalCtx0} {fnIdx : UInt32}
    {fnMaxJump : Nat} {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0}
    {preWork : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {rest : List RegaTask0} {metas : List TaskMeta0}
    (h : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt preWork seenJnz st ctrl
      (cur :: rest) metas) :
    ∀ v < preRes.nextVid.toNat, ActiveDefScope0 preSt preWork v →
      preRes.escaped.getD v 0 = 0 → 0 < st.remUses.getD v 0 →
      (arrGetU0 st.vslot (UInt32.ofNat v)).toNat < cur.nextSlot.toNat ∧
      arrGetU0 st.vslot (UInt32.ofNat v) ∉ cur.freeSlots ∧
      ∀ w < preRes.nextVid.toNat, w ≠ v → ActiveDefScope0 preSt preWork w →
        preRes.escaped.getD w 0 = 0 → 0 < st.remUses.getD w 0 →
        arrGetU0 st.vslot (UInt32.ofNat w) ≠ arrGetU0 st.vslot (UInt32.ofNat v) := by
  intro v _ hDv hev hrv
  have hv_lt : v < st.nextVid.toNat := h.st_nv ▸ hDv.1
  obtain ⟨iv, hiv1, hiv2, hiv3, hlv⟩ := activeDefScope0_live_of_witness h hv_lt hev hDv hrv
  obtain ⟨hflt, hfnf⟩ := head_protects_later_live h hiv1 hiv2 hv_lt hlv
  refine ⟨hflt, hfnf, fun w _ hne hDw hew hrw => ?_⟩
  have hw_lt : w < st.nextVid.toNat := h.st_nv ▸ hDw.1
  obtain ⟨iw, hiw1, hiw2, hiw3, hlw⟩ := activeDefScope0_live_of_witness h hw_lt hew hDw hrw
  by_cases heq : iw = iv
  · subst heq
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlive_iw⟩ :=
      h.items_ok iw hiw1 hiw2 hiw3
    exact ((hlive_iw w hw_lt hlw).2.2 v hv_lt hne.symm hlv).symm
  · rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hwait_iw, _, hlive_iw⟩ :=
        h.items_ok iw hiw1 hiw2 hiw3
      have hcov := h.later_live iw iv hiw1 hiw2 hiw3 hiv1 hiv2 hlt v hv_lt hlv
      rcases hcov with hlv_iw | ⟨info, hinfo, hwait, hmem⟩
      · exact ((hlive_iw w hw_lt hlw).2.2 v hv_lt hne.symm hlv_iw).symm
      · intro hcol
        have hnin := (hwait_iw info hinfo hwait).2 w hw_lt hlw
        rw [← hcol] at hmem
        exact hnin hmem
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hwait_iv, _, hlive_iv⟩ :=
        h.items_ok iv hiv1 hiv2 hiv3
      have hcov := h.later_live iv iw hiv1 hiv2 hiv3 hiw1 hiw2 hgt w hw_lt hlw
      rcases hcov with hlw_iv | ⟨info, hinfo, hwait, hmem⟩
      · exact ((hlive_iv w hw_lt hlw_iv).2.2 v hv_lt hne.symm hlv).symm
      · intro hcol
        have hnin := (hwait_iv info hinfo hwait).2 v hv_lt hlv
        rw [hcol] at hmem
        exact hnin hmem

theorem taskMetaOk0_mono_rest {ctx : LegalCtx0} {maxBd : Nat} {esc : Array Nat}
    {preSt preSt' : PreSt0} {st st' : RegaSt0} {ctrl ctrl' : CtrlSt0}
    {p : PreItem0} {t : RegaTask0} {m : TaskMeta0}
    (hm : TaskMetaOk0 ctx maxBd esc preSt st ctrl p t m)
    (hp_sc_ne : ∀ w, st.nextVid.toNat ≤ w → w < preSt'.nextVid.toNat →
      p.scope.toNat ≠ preSt'.defScope.getD w 0)
    (hpre_ds : ∀ v < preSt.nextVid.toNat, preSt'.defScope.getD v 0 = preSt.defScope.getD v 0)
    (hpre_nv : preSt.nextVid.toNat ≤ preSt'.nextVid.toNat)
    (hst_eq : st.nextVid = preSt.nextVid) (hst'_eq : st'.nextVid = preSt'.nextVid)
    (hms : st.maxSlots.toNat ≤ st'.maxSlots.toNat)
    (hmxs : st'.maxSlots.toNat ≤ maxBd)
    (hvsl : ∀ v < st.nextVid.toNat, arrGetU0 st'.vslot (UInt32.ofNat v) =
      arrGetU0 st.vslot (UInt32.ofNat v))
    (hnl : ctrl.nextLbl.toNat ≤ ctrl'.nextLbl.toNat)
    (hls : ∀ l, 1 ≤ l → l < ctrl.nextLbl.toNat →
      ctrl'.lblSlots.getD l [] = ctrl.lblSlots.getD l [])
    (hrem : ∀ v < st.nextVid.toNat, esc.getD v 0 = 0 →
      p.scope.toNat = preSt.defScope.getD v 0 →
      (0 < st'.remUses.getD v 0 ↔ 0 < st.remUses.getD v 0)) :
    TaskMetaOk0 ctx maxBd esc preSt' st' ctrl' p t m := by
  obtain ⟨hpn, hpv, hvl, hvlt, hll, hgl, hgi, hwf, hfit, hsbg, hnb, hpool, hnxt_nv,
    hinfo_ok, hwait, hentry, hlive⟩ := hm
  have hnv_le : st.nextVid.toNat ≤ st'.nextVid.toNat := by
    rw [hst_eq, hst'_eq]; exact hpre_nv
  have hlive_iff : ∀ w < st'.nextVid.toNat,
      LiveInTask0 esc preSt' st' p t w ↔
        (w < st.nextVid.toNat ∧ LiveInTask0 esc preSt st p t w) := by
    intro w hw
    constructor
    · intro hlw
      rcases hlw with ⟨hes, hwmem⟩ | ⟨hes, hsc, hpos⟩
      · have hw_lt : w < st.nextVid.toNat := by
          have := hvlt (UInt32.ofNat w) hwmem
          rwa [u32_toNat_ofNat7, Nat.mod_eq_of_lt (Nat.lt_trans hw (UInt32.toNat_lt _))] at this
        exact ⟨hw_lt, Or.inl ⟨hes, hwmem⟩⟩
      · have hw_lt : w < st.nextVid.toNat := Nat.lt_of_not_le fun hge' =>
          False.elim <| hp_sc_ne w hge' (hst'_eq ▸ hw) hsc
        rw [hpre_ds w (hst_eq ▸ hw_lt)] at hsc
        exact ⟨hw_lt, Or.inr ⟨hes, hsc, (hrem w hw_lt hes hsc).mp hpos⟩⟩
    · rintro ⟨hw_lt, hlw⟩
      rcases hlw with ⟨hes, hwmem⟩ | ⟨hes, hsc, hpos⟩
      · exact Or.inl ⟨hes, hwmem⟩
      · refine Or.inr ⟨hes, ?_, (hrem w hw_lt hes hsc).mpr hpos⟩
        rw [hpre_ds w (hst_eq ▸ hw_lt)]; exact hsc
  refine ⟨hpn, hpv, hvl, fun v hv => Nat.lt_of_lt_of_le (hvlt v hv) hnv_le, hll, hgl, hgi, hwf,
    hfit, hsbg, hnb, ⟨hpool.1, hpool.2.1, Nat.le_trans hpool.2.2.1 hms, hmxs, hpool.2.2.2.2⟩,
    Nat.le_trans hnxt_nv hnv_le,
    fun info hi => lblInfoOk0_mono (hinfo_ok info hi) hnl hls hnv_le hms hvsl,
    fun info hi hw => by
      obtain ⟨hw1, hw2⟩ := hwait info hi hw
      refine ⟨hw1, fun v hv hlv => ?_⟩
      obtain ⟨hv_lt, hlv'⟩ := (hlive_iff v hv).mp hlv
      rw [hvsl v hv_lt]
      exact hw2 v hv_lt hlv',
    ?_, fun v hv hlv => ?_⟩
  · cases he : m.entryInfo with
    | none => exact trivial
    | some info => rw [he] at hentry; exact hentry
  · obtain ⟨hv_lt, hlv'⟩ := (hlive_iff v hv).mp hlv
    have hv_ok := hlive v hv_lt hlv'
    rw [hvsl v hv_lt]
    refine ⟨hv_ok.1, hv_ok.2.1, fun w hw hne hlw => ?_⟩
    obtain ⟨hw_lt, hlw'⟩ := (hlive_iff w hw).mp hlw
    rw [hvsl w hw_lt]
    exact hv_ok.2.2 w hw_lt hne hlw'

/-! ## 4. Initial State `regaStepInv0_init` -/

theorem regaStepInv0_init {ctx : LegalCtx0} (fnIdx : UInt32) (fn : TFlatFn0)
    (hwf : WfNode0 ctx (pushTys0 fn.as []) [] fn.body) (hg : fn.okGuardsFull = true) :
    let preRes := compileFnPre0 fn
    let cap := Nat.add 32 (tyLenU0 fn.as 0).toNat
    let lblArr0 : Array (List UInt32) := (Array.emptyWithCapacity cap).push []
    let rega0 := RegaSt0.mk 0 0 (Array.emptyWithCapacity cap) preRes.uses []
    let ctrl0 := CtrlSt0.mk fnIdx 1 lblArr0
    let bl := bindEntryArgs0 fn.as 0 [] rega0
    let initTask := RegaTask0.mk 0 fn.body bl.venv [] bl.free bl.nxt
    let initMeta := TaskMeta0.mk (pushTys0 fn.as []) [] [] none
    let initPre := PreItem0.mk fn.body (preInit0 fn.as).1 0
    RegaStepInv0 ctx fnIdx (maxJumpArity0 fn.body) preRes 1 (preInit0 fn.as).2 [initPre]
      false bl.st ctrl0 [initTask] [initMeta] := by
  intro preRes cap lblArr0 rega0 ctrl0 bl initTask initMeta initPre
  have hsbg := TFlatFn0.okGuardsFull_singleBlock hg
  have hnb := TFlatFn0.okGuardsFull_noNegBool hg
  have hfit := TFlatFn0.okGuardsFull_sigLensFitU32 hg
  have hngj := TFlatFn0.okGuardsFull_noGroupAfterJnz hg
  have hbd := TFlatFn0.okGuardsFull_boundsFitU32 hg
  simp only [TFlatFn0.sigLensFitU32, listLenFitsU32, Bool.and_eq_true, decide_eq_true_eq] at hfit
  simp only [TFlatFn0.boundsFitU32, Bool.and_eq_true, decide_eq_true_eq] at hbd
  have hlen_as : (tyLenU0 fn.as 0).toNat = fn.as.length := tyLenU0_eq_of_lt hfit.1.1
  have hpre := compileFnPre0_inv hwf hg
  rw [show compileFnPre0 fn = preRes from rfl] at hpre
  obtain ⟨hp_venv, hp_nv, hp_nv_lt, hp_ds_sz, hp_us_sz, hp_es_sz, hp_es_bit,
    hp_us_bd, hp_ac_bd, hp_entry⟩ := hpre
  let preCap := Nat.add 32 (tyLenU0 fn.as 0).toNat
  have hinit := preBindLoop0_spec fn.as.length (tyLenU0 fn.as 0) 0 []
    (PreSt0.mk 0 (Array.emptyWithCapacity preCap) (Array.emptyWithCapacity preCap)
      (Array.emptyWithCapacity preCap))
    hlen_as (by simp; omega) (by simp) (by simp) (by simp)
  have hinit_eq : preInit0 fn.as =
      preBindLoop0 (tyLenU0 fn.as 0) 0 []
        (PreSt0.mk 0 (Array.emptyWithCapacity preCap) (Array.emptyWithCapacity preCap)
          (Array.emptyWithCapacity preCap)) := rfl
  rw [← hinit_eq] at hinit
  simp only [UInt32.toNat_zero, Nat.zero_add, Nat.not_lt_zero, ↓reduceIte] at hinit
  have hbl := bindEntryArgs0_spec fn.as 0 [] rega0 (preRes.nextVid.toNat + maxJumpArity0 fn.body)
    (by simp [rega0]) rfl (by simp only [UInt32.toNat_zero, Nat.zero_add]; omega)
    (by omega) (by simp [rega0])
  dsimp only [rega0] at hbl
  rw [← show bl = bindEntryArgs0 fn.as 0 [] rega0 from rfl] at hbl
  obtain ⟨hb_venv, hb_free, hb_nxt, hb_nv, hb_vsz, hb_rem, hb_pool, hb_pres, hb_slots⟩ := hbl
  simp only [UInt32.toNat_zero, Nat.zero_add] at hb_venv hb_nxt hb_nv hb_vsz hb_slots
  have hnv_eq : bl.st.nextVid = (preInit0 fn.as).2.nextVid :=
    u32_ext7 (by rw [hb_nv, hinit.2.1])
  have hvlen_0 : bl.venv.length = (pushTys0 fn.as []).length := by
    rw [hb_venv, pushFreshVids0_length, List.length_nil, pushTys0_eq_pushTypes, pushTypes_length,
      List.length_nil]
  have hvlt_0 : ∀ v ∈ bl.venv, v.toNat < bl.st.nextVid.toNat := by
    intro v hm
    rw [hb_venv] at hm
    rw [hb_nv]
    rcases (mem_pushFreshVids0 fn.as.length 0 [] v).mp hm with hf | ⟨k, hk, rfl⟩
    · nomatch hf
    · rw [UInt32.zero_add, u32_toNat_ofNat7, Nat.mod_eq_of_lt (Nat.lt_trans hk (by omega))]
      exact hk
  have hpre_inv0 : PreWorkInv0 ctx 1 (preInit0 fn.as).2 [initPre] := by
    refine ⟨hinit.2.2.1.trans hinit.2.1.symm, hinit.2.2.2.1.trans hinit.2.1.symm,
      hinit.2.2.2.2.1.trans hinit.2.1.symm,
      fun v hv => by
        rw [hinit.2.1] at hv; rw [hinit.2.2.2.2.2.1 v]; simp only [hv, ↓reduceIte]
        simp only [UInt32.toNat_one]; exact Nat.zero_lt_one,
      fun v _ => by rw [hinit.2.2.2.2.2.2.2 v]; exact Or.inl rfl,
      by simp [initPre],
      fun p hp => by
        simp only [List.mem_singleton] at hp; subst hp
        simp only [initPre, UInt32.toNat_zero, UInt32.toNat_one]; exact Nat.zero_lt_one,
      fun p hp => by
        simp only [List.mem_singleton] at hp; subst hp
        refine ⟨pushTys0 fn.as [], [], ?_, ?_, hwf, hfit.2, hsbg, hnb⟩
        · simpa only [initPre, ← hinit.1, hb_venv] using hvlen_0
        · intro v hm; rw [← hnv_eq]; apply hvlt_0
          simpa only [initPre, ← hinit.1, hb_venv] using hm,
      by rw [hinit.2.1]; dsimp only [initPre]; rw [List.map_singleton]
         dsimp only [workBinderCount0]; omega,
      by dsimp only [initPre]; rw [List.map_singleton]; dsimp only [workNodeCount0]
         rw [UInt32.toNat_one]; omega,
      by dsimp only [initPre]; rw [List.map_singleton]; dsimp only [workArgCount0]; exact hbd.2,
      fun v _ => by
        rw [hinit.2.2.2.2.2.2.1 v]
        dsimp only [initPre]; rw [List.map_singleton]; dsimp only [workArgCount0]
        simp only [Nat.add_zero, Nat.zero_add]
        exact hbd.2⟩
  have hpre_run0 :
      (preRunAux0 (UInt32.ofNat (workNodeCount0 ([initPre].map PreItem0.node)))
        1 (preInit0 fn.as).2 [initPre]).2 = preRes := by
    have hfl : preRunAux0 (UInt32.ofNat (workNodeCount0 ([initPre].map PreItem0.node)))
        1 (preInit0 fn.as).2 [initPre] =
        preRunAux0 0x7fffffff 1 (preInit0 fn.as).2 [initPre] := by
      refine preRunAux0_fuel_indep ?_ ?_
      · rw [u32_toNat_ofNat7, Nat.mod_eq_of_lt (by
            dsimp only [initPre]; rw [List.map_singleton]; dsimp only [workNodeCount0]; omega)]
        exact Nat.le_refl _
      · dsimp only [initPre]; rw [List.map_singleton]; dsimp only [workNodeCount0]
        change nodeCount0 fn.body ≤ 2147483647; omega
    rw [hfl, preRunAux0_snd_eq_preWorkLoop0]
    rfl
  refine
    { preRes_nv := hp_nv_lt
      preRes_ds_sz := hp_ds_sz
      preRes_us_sz := hp_us_sz
      preRes_es_sz := hp_es_sz
      preRes_es_bit := hp_es_bit
      preRes_us_bd := fun v hv => Nat.lt_of_le_of_lt (hp_us_bd v hv) hp_ac_bd
      maxBd_lt := by rw [hp_nv]; exact hbd.1.1
      pre_inv := hpre_inv0
      pre_run := hpre_run0
      len_pw := rfl
      len_mw := rfl
      seenJnz_safe := hngj
      seenJnz_ctrl := by simp [ctrl0, lblArr0]
      maxJump_bd := by
        dsimp only [initTask]; rw [List.map_singleton]; dsimp only [workMaxJumpArity0]; omega
      ctrl_fn := rfl
      ctrl_nl := by
        dsimp only [ctrl0, initTask]; rw [List.map_singleton]
        dsimp only [workNodeCount0]; rw [UInt32.toNat_one]; omega
      st_nv := hnv_eq
      st_vslot_sz := hb_vsz.trans hb_nv.symm
      st_rem_sz := by rw [hb_rem]; exact hp_us_sz
      st_maxSl_le := Nat.le_trans hb_pool.2.2.2.1 (Nat.le_refl _)
      st_rem_le := fun v _ => by rw [hb_rem]; exact Nat.le_refl _
      st_rem_future := fun v _ _ => by rw [hb_rem]
      st_rem_active := fun v hv hesc _ => by
        rw [hb_nv] at hv
        rw [hb_rem, (hp_entry v hv).2]
        have hnv_a : (preInit0 fn.as).2.nextVid = UInt32.ofNat fn.as.length :=
          u32_ext7 (by rw [hinit.2.1, u32_toNat_ofNat7, Nat.mod_eq_of_lt (by omega)])
        have hds0 : (preInit0 fn.as).2.defScope.getD v 0 = 0 := by
          rw [hinit.2.2.2.2.2.1 v]; simp [hv]
        rw [hds0, hp_venv]
        dsimp only [initPre, sameScopeSpineSum0]
        simp only [UInt32.toNat_zero, ↓reduceIte, Nat.add_zero, hnv_a, hinit.1]
      items_ok := fun i hi1 hi2 hi3 => by
        simp only [List.length_singleton] at hi2
        obtain rfl : i = 0 := by omega
        simp only [List.getElem_cons_zero]
        dsimp only [initPre, initTask, initMeta, TaskMetaOk0]
        refine ⟨rfl, ?_, hvlen_0, hvlt_0, rfl, rfl, fun k hk _ _ => absurd hk (Nat.not_lt_zero _),
          hwf, hfit.2, hsbg, hnb, hb_pool, by rw [hb_nxt, hb_nv]; exact Nat.le_refl _,
          fun _ hm => absurd hm List.not_mem_nil,
          fun _ hm => absurd hm List.not_mem_nil, trivial, fun v hv hlv => ?_⟩
        · rw [hb_venv]; exact hinit.1
        · rw [hb_nv] at hv
          have hslt : (arrGetU0 bl.st.vslot (UInt32.ofNat v)).toNat < bl.nxt.toNat := by
            have he := hb_slots v hv
            rw [he, u32_toNat_ofNat7, Nat.mod_eq_of_lt (by omega), hb_nxt]
            exact hv
          refine ⟨hslt, by rw [hb_free]; exact List.not_mem_nil, fun w hw hne hlw => ?_⟩
          rw [hb_nv] at hw
          have hev := hb_slots v hv; have hew := hb_slots w hw
          rw [hev, hew]
          intro hcol
          have hn := congrArg UInt32.toNat hcol
          rw [u32_toNat_ofNat7, u32_toNat_ofNat7, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)] at hn
          exact hne hn
      later_live := fun i j hi1 hi2 hi3 hj1 hj2 hlt => by
        simp only [List.length_singleton] at hi2 hj2; omega }

/-! ## 5. Single-Step Lockstep Theorems (`term`, `lin`, `jnz`, `group`) -/

theorem regaStep0_term {ctx : LegalCtx0} {fnIdx : UInt32} {fnMaxJump : Nat}
    {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0} {curPre : PreItem0}
    {restPre : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {rest : List RegaTask0} {mCur : TaskMeta0} {restMeta : List TaskMeta0}
    (h : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: restPre) seenJnz st ctrl
      (cur :: rest) (mCur :: restMeta))
    (hterm : isTerm0 cur.node = true) :
    let st0 := regaPrependLbl0 cur st ctrl
    let ls := regaStep0 preRes.escaped cur st0 ctrl rest
    let preSt1 := preNoteNode0 curPre.scope curPre.venv curPre.node preSt
    let out := preStepPush0 curPre preSt1 nextSc restPre
    RegaStepInv0 ctx fnIdx fnMaxJump preRes out.nextScope out.st out.work seenJnz
      ls.st ls.ctrl ls.work restMeta := by
  intro st0 ls preSt1 out
  have hcur_ok := h.items_ok 0 (by simp) (by simp) (by simp)
  dsimp only [List.getElem_cons_zero] at hcur_ok
  obtain ⟨hpn, _, _, _, _, _, _, _, _, _, _, _, hnxt_nv, _, _, _, _⟩ := hcur_ok
  have hterm_p : isTerm0 curPre.node = true := by rw [hpn]; exact hterm
  have hout : out = PreOut0.mk preSt1 nextSc restPre := by
    dsimp only [out, preStepPush0]; simp [hterm_p]
  have hp_inv := h.pre_inv.items_ok curPre List.mem_cons_self
  obtain ⟨vT, lT, hvlen, hvlt, hwf, _, _, _⟩ := hp_inv
  have hst1 := preNoteNode0_spec curPre.scope curPre.venv curPre.node preSt
    h.pre_inv.defScope_sz h.pre_inv.uses_sz h.pre_inv.escaped_sz hvlt
    (hvlen ▸ wfNode0_nodeArgsInVenv0 hwf)
    (fun v hv => by
      have hb := h.pre_inv.uses_bound v hv
      rw [List.map_cons] at hb; dsimp only [workArgCount0] at hb; omega)
    (fun v hv => Nat.lt_trans (h.pre_inv.defScope_lt v hv) (UInt32.toNat_lt nextSc))
    h.pre_inv.escaped_bit
  dsimp only at hst1
  change preSt1.nextVid = preSt.nextVid ∧ preSt1.defScope = preSt.defScope ∧
    preSt1.uses.size = preSt.nextVid.toNat ∧ preSt1.escaped.size = preSt.nextVid.toNat ∧ _ at hst1
  have hbc0 : binderCount0 curPre.node = 0 := by
    cases hnd : curPre.node <;> rw [hnd] at hterm_p <;> simp only [isTerm0] at hterm_p
    all_goals first
      | exact absurd hterm_p Bool.false_ne_true
      | (dsimp only [binderCount0]; first | done | rfl)
  have hnc1 : nodeCount0 curPre.node = 1 := by
    cases hnd : curPre.node <;> rw [hnd] at hterm_p <;> simp only [isTerm0] at hterm_p
    all_goals first
      | exact absurd hterm_p Bool.false_ne_true
      | (dsimp only [nodeCount0]; first | done | rfl)
  have hrest_nodup : (restPre.map PreItem0.scope).Nodup := by
    have hnd := h.pre_inv.scopes_nodup
    simp only [List.map_cons, List.nodup_cons] at hnd
    exact hnd.2
  have hpre_inv' : PreWorkInv0 ctx out.nextScope out.st out.work := by
    rw [hout]; dsimp only
    refine ⟨hst1.1 ▸ hst1.2.1.symm ▸ h.pre_inv.defScope_sz,
      hst1.1 ▸ hst1.2.2.1, hst1.1 ▸ hst1.2.2.2.1,
      fun v hv => hst1.2.1 ▸ h.pre_inv.defScope_lt v (hst1.1 ▸ hv),
      fun v hv => hst1.2.2.2.2.1 v (hst1.1 ▸ hv),
      hrest_nodup, fun p hp => h.pre_inv.scopes_lt p (List.mem_cons_of_mem _ hp),
      fun p hp => hst1.1 ▸ h.pre_inv.items_ok p (List.mem_cons_of_mem _ hp),
      by rw [hst1.1]; have := h.pre_inv.nextVid_bound
         rw [List.map_cons] at this; dsimp only [workBinderCount0] at this
         rw [hbc0] at this; omega,
      by have hns := h.pre_inv.nextSc_bound; have hnp := nodeCount0_pos curPre.node
         rw [List.map_cons] at hns; dsimp only [workNodeCount0] at hns; omega,
      by have := h.pre_inv.argCount_bound
         rw [List.map_cons] at this; dsimp only [workArgCount0] at this; omega,
      fun v hv => by
        rw [hst1.1] at hv
        have hv1 := hst1.2.2.2.2.2 v hv
        have hau := nodeArgsUses0_le_argCount0 (UInt32.ofNat v) curPre.venv curPre.node
        have hb := h.pre_inv.uses_bound v hv
        rw [List.map_cons] at hb; dsimp only [workArgCount0] at hb
        split at hv1 <;> { rw [hv1.1]; omega }⟩
  have hpre_run' : (preRunAux0 (UInt32.ofNat (workNodeCount0 (out.work.map PreItem0.node)))
      out.nextScope out.st out.work).2 = preRes :=
    preRun_step_eq7 h.pre_inv.nextSc_bound h.pre_run
  have hst0_nv : st0.nextVid = st.nextVid := by
    dsimp only [st0, regaPrependLbl0]; split <;> rfl
  have hst0_vslot : st0.vslot = st.vslot := by
    dsimp only [st0, regaPrependLbl0]; split <;> rfl
  have hst0_rem : st0.remUses = st.remUses := by
    dsimp only [st0, regaPrependLbl0]; split <;> rfl
  have hst0_msl : st0.maxSlots = st.maxSlots := by
    dsimp only [st0, regaPrependLbl0]; split <;> rfl
  have hls_step : ls.ctrl = ctrl ∧ ls.work = rest ∧
      ls.st.nextVid = st.nextVid ∧ ls.st.vslot = st.vslot ∧
      ls.st.remUses = st.remUses ∧ ls.st.maxSlots.toNat ≤ preRes.nextVid.toNat + fnMaxJump ∧
      st.maxSlots.toNat ≤ ls.st.maxSlots.toNat := by
    have hstep : ls = regaStepCtrl0 cur st0 ctrl rest := by
      rcases cur with ⟨lbl, nd, venv, lenv, fr, nxt⟩
      cases nd with
      | jnz _ _ _ | group _ _ | let1 _ _ _ | let2Umulw64 _ _ _ | load _ _ _
      | store _ _ _ _ | call _ _ _ _ _ => simp [isTerm0] at hterm
      | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt => rfl
    rw [hstep]
    dsimp only [regaStepCtrl0]
    cases hnd : cur.node with
    | jnz _ _ _ | group _ _ | let1 _ _ _ | let2Umulw64 _ _ _ | load _ _ _
    | store _ _ _ _ | call _ _ _ _ _ => rw [hnd] at hterm; simp [isTerm0] at hterm
    | tailCall _ _ _ | exit _ _ _ =>
      exact ⟨rfl, rfl, hst0_nv, hst0_vslot, hst0_rem, hst0_msl ▸ h.st_maxSl_le,
        hst0_msl ▸ Nat.le_refl _⟩
    | ret _ =>
      exact ⟨rfl, rfl, hst0_nv, hst0_vslot, hst0_rem, hst0_msl ▸ h.st_maxSl_le,
        hst0_msl ▸ Nat.le_refl _⟩
    | hlt =>
      exact ⟨rfl, rfl, hst0_nv, hst0_vslot, hst0_rem, hst0_msl ▸ h.st_maxSl_le,
        hst0_msl ▸ Nat.le_refl _⟩
    | jump j args =>
      dsimp only [emitJump0]
      cases args with
      | nil =>
        exact ⟨rfl, rfl, hst0_nv, hst0_vslot, hst0_rem, hst0_msl ▸ h.st_maxSl_le,
          hst0_msl ▸ Nat.le_refl _⟩
      | cons a rest_a =>
        cases rest_a with
        | nil =>
          exact ⟨rfl, rfl, hst0_nv, hst0_vslot, hst0_rem, hst0_msl ▸ h.st_maxSl_le,
            hst0_msl ▸ Nat.le_refl _⟩
        | cons b tail_a =>
          dsimp only [emitJumpMulti0]
          refine ⟨rfl, rfl, hst0_nv, hst0_vslot, hst0_rem, ?_, ?_⟩
          · have hjm := h.maxJump_bd
            rw [List.map_cons, hnd] at hjm
            dsimp only [workMaxJumpArity0, maxJumpArity0] at hjm
            have harg_lt : (a :: b :: tail_a).length < 2 ^ 32 := by have := h.maxBd_lt; omega
            have hst_bd :
                st.nextVid.toNat + workBinderCount0 ((cur :: rest).map RegaTask0.node) =
                  preRes.nextVid.toNat := h.preRes_uses_lt_bd
            have hsum_lt : cur.nextSlot.toNat + (a :: b :: tail_a).length < 2 ^ 32 := by
              have := h.maxBd_lt; omega
            have hadd_eq : (cur.nextSlot + argLenU0 (a :: b :: tail_a) 0).toNat =
                cur.nextSlot.toNat + (a :: b :: tail_a).length := by
              rw [UInt32.toNat_add, argLenU0_eq_of_lt harg_lt, Nat.mod_eq_of_lt hsum_lt]
            rw [u32Max0_toNat, hst0_msl, hadd_eq]
            exact Nat.max_le.mpr ⟨h.st_maxSl_le, by omega⟩
          · rw [u32Max0_toNat, hst0_msl]; exact Nat.le_max_left _ _
  obtain ⟨hlc, hlw, hlnv, hlvsl, hlrem, hlms_le, hlms_ge⟩ := hls_step
  have hout_st : out.st = preSt1 := by rw [hout]
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
      len_pw := by rw [hout, hlw]; simpa using h.len_pw
      len_mw := by rw [hlw]; simpa using h.len_mw
      seenJnz_safe := by
        rw [hlw]; have hs := h.seenJnz_safe
        simp only [List.map_cons] at hs; rwa [← jnzGroupSafeWork0_term seenJnz hterm]
      seenJnz_ctrl := by rw [hlc]; exact h.seenJnz_ctrl
      maxJump_bd := by
        rw [hlw]; have hm := h.maxJump_bd
        rw [List.map_cons] at hm; dsimp only [workMaxJumpArity0] at hm; omega
      ctrl_fn := hlc ▸ h.ctrl_fn
      ctrl_nl := by
        rw [hlc, hlw]; have hnl := h.ctrl_nl
        rw [List.map_cons] at hnl; dsimp only [workNodeCount0] at hnl
        exact ⟨hnl.1, by have := nodeCount0_pos cur.node; omega⟩
      st_nv := by rw [hout, hlnv, hst1.1, h.st_nv]
      st_vslot_sz := by rw [hlnv, hlvsl]; exact h.st_vslot_sz
      st_rem_sz := by rw [hlrem]; exact h.st_rem_sz
      st_maxSl_le := hlms_le
      st_rem_le := fun v hv => by rw [hlrem]; exact h.st_rem_le v hv
      st_rem_future := fun v h1 h2 => by rw [hlnv] at h1; rw [hlrem]; exact h.st_rem_future v h1 h2
      st_rem_active := fun v hv hesc hact => by
        rw [hlnv] at hv
        rw [hout] at hact; dsimp only [ActiveDefScope0] at hact
        rw [hst1.1, hst1.2.1] at hact
        rw [hlrem, hout]; dsimp only; rw [hst1.2.1, hst1.1]
        have hact0 : ActiveDefScope0 preSt (curPre :: restPre) v :=
          ⟨h.st_nv ▸ hv, hact.2.elim fun q hq => ⟨q, List.mem_cons_of_mem _ hq.1, hq.2⟩⟩
        rw [h.st_rem_active v (h.st_nv ▸ hv) hesc hact0]
        have hsc_ne : preSt.defScope.getD v 0 ≠ curPre.scope.toNat := by
          intro he
          obtain ⟨q, hq, hq_sc⟩ := hact.2
          have hnd := h.pre_inv.scopes_nodup
          simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
          exact hnd.1 q hq (u32_ext7 (by omega))
        dsimp only [sameScopeSpineSum0]
        simp only [hsc_ne, ↓reduceIte, Nat.zero_add]
      items_ok := fun i hi1 hi2 hi3 => by
        have hi1' : i < restPre.length := by rw [hout] at hi1; exact hi1
        have hi2' : i < rest.length := by rw [hlw] at hi2; exact hi2
        have htm := h.items_ok (i + 1) (by simp only [List.length_cons]; omega)
          (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
        dsimp only [List.getElem_cons_succ] at htm
        rw [show out.work[i] = restPre[i]'hi1' from by simp [hout],
          show ls.work[i] = rest[i]'hi2' from by simp [hlw], hout_st, hlc]
        refine taskMetaOk0_mono_rest htm
          (fun w h1 h2 => by
            rw [h.st_nv] at h1; rw [hst1.1] at h2; omega)
          (fun v _ => congrArg (fun a => a.getD v 0) hst1.2.1)
          (by rw [hst1.1]; exact Nat.le_refl _)
          h.st_nv (by rw [hlnv, hst1.1, h.st_nv]) hlms_ge hlms_le
          (fun v _ => by rw [hlvsl]) (Nat.le_refl _) (fun _ _ _ => rfl)
          (fun v _ _ _ => by rw [hlrem])
      later_live := fun i j hi1 hi2 hi3 hj1 hj2 hij w hw hlive => by
        rw [hlnv] at hw
        have hi1' : i < restPre.length := by rw [hout] at hi1; exact hi1
        have hj1' : j < restPre.length := by rw [hout] at hj1; exact hj1
        have hi2' : i < rest.length := by rw [hlw] at hi2; exact hi2
        have hj2' : j < rest.length := by rw [hlw] at hj2; exact hj2
        have hcov := h.later_live (i + 1) (j + 1) (by simp only [List.length_cons]; omega)
          (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
          (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
          (Nat.succ_lt_succ hij) w hw
        have hiff : ∀ (k : Nat) (hk1 : k < restPre.length) (hk2 : k < rest.length),
            LiveInTask0 preRes.escaped preSt1 ls.st restPre[k] rest[k] w ↔
            LiveInTask0 preRes.escaped preSt st
              ((curPre :: restPre)[k + 1]'(Nat.succ_lt_succ hk1))
              ((cur :: rest)[k + 1]'(Nat.succ_lt_succ hk2)) w := by
          intro k hk1 hk2
          dsimp only [List.getElem_cons_succ]
          simp only [LiveInTask0, hst1.2.1, hlrem]
        rw [show out.work[j] = restPre[j]'hj1' from by simp [hout],
          show ls.work[j] = rest[j]'hj2' from by simp [hlw], hout_st] at hlive
        have hres := hcov ((hiff j hj1' hj2').mp hlive)
        rw [show out.work[i] = restPre[i]'hi1' from by simp [hout],
          show ls.work[i] = rest[i]'hi2' from by simp [hlw], hout_st]
        rcases hres with hl | ⟨info, hm, hwt, hsl⟩
        · exact Or.inl ((hiff i hi1' hi2').mpr hl)
        · refine Or.inr ⟨info, hm, hwt, ?_⟩
          rw [hlvsl]; exact hsl }

private theorem preStepPush0_lin_eq (cur : PreItem0) (st1 : PreSt0) (nextSc : UInt32)
    (rest : List PreItem0) (hlin : isTerm0 cur.node = false)
    (hnj : ∀ c t e, cur.node ≠ .jnz c t e) (hng : ∀ bs k, cur.node ≠ .group bs k) :
    preStepPush0 cur st1 nextSc rest = preStepLin0 cur st1 nextSc rest := by
  rcases cur with ⟨nd, venv, sc⟩
  cases nd with
  | jnz _ _ _ => exact absurd rfl (hnj _ _ _)
  | group _ _ => exact absurd rfl (hng _ _)
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt => simp [isTerm0] at hlin
  | let1 _ _ _ | let2Umulw64 _ _ _ | load _ _ _ | store _ _ _ _ | call _ _ _ _ _ =>
    dsimp only [preStepPush0, isTerm0]; rfl

private theorem regaStep0_lin_eq (esc : Array Nat) (cur : RegaTask0) (st0 : RegaSt0)
    (ctrl : CtrlSt0) (rest : List RegaTask0) (hlin : isTerm0 cur.node = false)
    (hnj : ∀ c t e, cur.node ≠ .jnz c t e) (hng : ∀ bs k, cur.node ≠ .group bs k) :
    regaStep0 esc cur st0 ctrl rest = stepLinear0 esc cur st0 ctrl rest := by
  rcases cur with ⟨lbl, nd, venv, lenv, fr, nxt⟩
  cases nd with
  | jnz _ _ _ => exact absurd rfl (hnj _ _ _)
  | group _ _ => exact absurd rfl (hng _ _)
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt => simp [isTerm0] at hlin
  | _ => rfl

theorem regaStep0_lin {ctx : LegalCtx0} {fnIdx : UInt32} {fnMaxJump : Nat}
    {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0} {curPre : PreItem0}
    {restPre : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {rest : List RegaTask0} {mCur : TaskMeta0} {restMeta : List TaskMeta0}
    (h : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: restPre) seenJnz st ctrl
      (cur :: rest) (mCur :: restMeta))
    (hlin : isTerm0 cur.node = false) (hnj : ∀ c t e, cur.node ≠ .jnz c t e)
    (hng : ∀ bs k, cur.node ≠ .group bs k) :
    let st0 := regaPrependLbl0 cur st ctrl
    let ls := regaStep0 preRes.escaped cur st0 ctrl rest
    let preSt1 := preNoteNode0 curPre.scope curPre.venv curPre.node preSt
    let out := preStepPush0 curPre preSt1 nextSc restPre
    let m0 := TaskMeta0.mk (legalNextVenv0 cur.node mCur.vT) mCur.lT mCur.gl none
    RegaStepInv0 ctx fnIdx fnMaxJump preRes out.nextScope out.st out.work seenJnz
      ls.st ls.ctrl ls.work (m0 :: restMeta) := by
  intro st0 ls preSt1 out m0
  have hcur_ok := h.items_ok 0 (by simp) (by simp) (by simp)
  dsimp only [List.getElem_cons_zero] at hcur_ok
  obtain ⟨hpn, hpv, hvlen, hvlt, hllen, hgl, hgi, hwf, hfit, hsbg, hnb, hpool, hnxt_nv,
    hinfo_ok, hwait, hentry, hlive⟩ := hcur_ok
  have hlin_p : isTerm0 curPre.node = false := by rw [hpn]; exact hlin
  have hnj_p : ∀ c t e, curPre.node ≠ .jnz c t e := fun c t e he => hnj c t e (hpn ▸ he)
  have hng_p : ∀ bs k, curPre.node ≠ .group bs k := fun bs k he => hng bs k (hpn ▸ he)
  obtain ⟨hcnt_lt, hvlen_l, hwfl, hfitl, hsbgl, hnbl, hbc_l, hac_l, hnc_l, hmja_l⟩ :=
    wfNode0_lin_inv hwf hfit hsbg hnb hlin hnj hng
  have hsub := preRunAux0_sub_active h.pre_inv h.pre_run
  obtain ⟨⟨hpr_nv, hpr_ds_sz, hpr_us_sz, hpr_es_sz, hpr_ds_eq, hpr_us_eq⟩, hpr_noesc⟩ := hsub
  have hp_inv := h.pre_inv.items_ok curPre List.mem_cons_self
  obtain ⟨vT', lT', hvlen', hvlt', hwf', hfit', hsbg', hnb'⟩ := hp_inv
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
  have hout : out =
      PreOut0.mk (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).2 nextSc
        (PreItem0.mk (linK0 curPre.node)
          (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1 curPre.scope ::
          restPre) :=
    preStepPush0_lin_eq curPre preSt1 nextSc restPre hlin_p hnj_p hng_p
  let cnt := linCnt0 cur.node
  have hcnt_eq : linCnt0 curPre.node = cnt := by rw [hpn]
  obtain ⟨_, hvlen_l', hwfl', hfitl', hsbgl', hnbl', hbc_l', hac_l', hnc_l', _⟩ :=
    wfNode0_lin_inv hwf' hfit' hsbg' hnb' hlin_p hnj_p hng_p
  have hnv_b : preSt1.nextVid.toNat + cnt.toNat < 2 ^ 32 := by
    rw [hst1.1]
    have hb := h.pre_inv.nextVid_bound
    have := hbc_l'
    rw [List.map_cons] at hb; dsimp only [workBinderCount0] at hb
    rw [hcnt_eq] at this
    omega
  have hbind_pre := preBindLoop0_spec cnt.toNat (linCnt0 curPre.node) curPre.scope curPre.venv
    preSt1 (by rw [hcnt_eq]) hnv_b (hst1.1 ▸ hst1.2.1.symm ▸ h.pre_inv.defScope_sz)
    (hst1.1 ▸ hst1.2.2.1) (hst1.1 ▸ hst1.2.2.2.1)
  dsimp only at hbind_pre
  have hst0_eqs : st0.nextVid = st.nextVid ∧ st0.maxSlots = st.maxSlots ∧
      st0.vslot = st.vslot ∧ st0.remUses = st.remUses := by
    dsimp only [st0, regaPrependLbl0]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  let dOut := emitLinNode0 cur st0
  let rr := relNodeArgs0 preRes.escaped st0.vslot cur.venv cur.node
    (RelRes0.mk st0.remUses cur.freeSlots)
  let st1 : RegaSt0 := { st0 with remUses := rr.remUses, revDirs := dOut }
  let bl0 : BindListOut0 := BindListOut0.mk cur.venv st1 rr.free cur.nextSlot
  let bl := bindRetsN0 preRes.escaped cnt 0 bl0
  have hls_eq : ls.st = bl.st ∧ ls.ctrl = ctrl ∧
      ls.work = RegaTask0.mk 0 (linK0 cur.node) bl.venv cur.lenv bl.free bl.nxt :: rest := by
    have hstep : ls = stepLinear0 preRes.escaped cur st0 ctrl rest :=
      regaStep0_lin_eq preRes.escaped cur st0 ctrl rest hlin hnj hng
    rw [hstep]
    exact ⟨rfl, rfl, rfl⟩
  have hsc_cur_lt : curPre.scope.toNat < nextSc.toNat :=
    h.pre_inv.scopes_lt curPre List.mem_cons_self
  have hrest_scopes : ∀ p ∈ restPre, p.scope ≠ curPre.scope := by
    have hnd := h.pre_inv.scopes_nodup
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    exact hnd.1
  have hrest_nodup : (restPre.map PreItem0.scope).Nodup := by
    have hnd := h.pre_inv.scopes_nodup
    simp only [List.map_cons, List.nodup_cons] at hnd
    exact hnd.2
  have hnd_sc : (curPre.scope :: restPre.map PreItem0.scope).Nodup :=
    List.nodup_cons.mpr ⟨fun hm => by
      obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm; exact hrest_scopes p hp hpe, hrest_nodup⟩
  have hvlt_pre' : ∀ v ∈ (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1,
      v.toNat < preSt.nextVid.toNat + cnt.toNat := by
    rw [hbind_pre.1, hst1.1]
    intro v hm
    rcases (mem_pushFreshVids0 cnt.toNat preSt.nextVid curPre.venv v).mp hm with h0 | ⟨k, hk, rfl⟩
    · exact Nat.lt_of_lt_of_le (hvlt' v h0) (Nat.le_add_right _ _)
    · rw [u32_add_ofNat_lt7 (by rw [hst1.1] at hnv_b; omega)]; omega
  have hpre_inv' : PreWorkInv0 ctx out.nextScope out.st out.work := by
    rw [hout]; dsimp only
    refine ⟨hbind_pre.2.2.1.trans hbind_pre.2.1.symm, hbind_pre.2.2.2.1.trans hbind_pre.2.1.symm,
      hbind_pre.2.2.2.2.1.trans hbind_pre.2.1.symm,
      fun v hv => by
        rw [hbind_pre.2.1] at hv; rw [hbind_pre.2.2.2.2.2.1 v]; split
        · rename_i hv0; rw [hst1.2.1]; exact h.pre_inv.defScope_lt v (hst1.1 ▸ hv0)
        · exact hsc_cur_lt,
      fun v hv => by
        rw [hbind_pre.2.1] at hv; rw [hbind_pre.2.2.2.2.2.2.2 v]; split
        · rename_i hv0; exact hst1.2.2.2.2.1 v (hst1.1 ▸ hv0)
        · exact Or.inl rfl,
      hnd_sc,
      fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact hsc_cur_lt
        · exact h.pre_inv.scopes_lt p (List.mem_cons_of_mem _ hp'),
      fun p hp => by
        rw [hbind_pre.2.1, hst1.1]
        rcases List.mem_cons.mp hp with rfl | hp'
        · rw [hbind_pre.1]
          have hvl_eq : (pushFreshVids0 cnt.toNat preSt1.nextVid curPre.venv).length =
              (legalNextVenv0 curPre.node vT').length := by
            rw [pushFreshVids0_length, hvlen', ← hcnt_eq]
            exact hvlen_l'.symm
          refine ⟨legalNextVenv0 curPre.node vT', lT', hvl_eq, ?_, hwfl', hfitl', hsbgl', hnbl'⟩
          dsimp only
          intro v hm
          rw [hst1.1] at hm
          exact hvlt_pre' v (by rw [hbind_pre.1, hst1.1]; exact hm)
        · obtain ⟨vT2, lT2, hvl2, hvlt2, hwf2, hfit2, hsbg2, hnb2⟩ :=
            h.pre_inv.items_ok p (List.mem_cons_of_mem _ hp')
          exact ⟨vT2, lT2, hvl2, fun v hm => Nat.lt_of_lt_of_le (hvlt2 v hm) (Nat.le_add_right _ _),
            hwf2, hfit2, hsbg2, hnb2⟩,
      by rw [hbind_pre.2.1, hst1.1]; have := h.pre_inv.nextVid_bound
         rw [List.map_cons] at this ⊢; dsimp only [workBinderCount0] at this ⊢
         rw [← hcnt_eq]; omega,
      by have hns := h.pre_inv.nextSc_bound
         rw [List.map_cons] at hns ⊢; dsimp only [workNodeCount0] at hns ⊢; omega,
      by have hac := h.pre_inv.argCount_bound
         rw [List.map_cons] at hac ⊢; dsimp only [workArgCount0] at hac ⊢; omega,
      fun v hv => by
        rw [hbind_pre.2.1, hst1.1] at hv; rw [hbind_pre.2.2.2.2.2.2.1 v]
        by_cases hv0 : v < preSt.nextVid.toNat
        · rw [hst1.1]; simp only [hv0, ↓reduceIte]
          have hv1 := hst1.2.2.2.2.2 v hv0
          have hb := h.pre_inv.uses_bound v hv0
          rw [List.map_cons] at hb; dsimp only [workArgCount0] at hb
          have hnu := nodeArgsUses0_add_linK0_le (UInt32.ofNat v) curPre.venv hlin_p hnj_p hng_p
          split at hv1 <;> { rw [hv1.1, List.map_cons]; dsimp only [workArgCount0]; omega }
        · rw [hst1.1]; simp only [hv0, ↓reduceIte, Nat.zero_add]
          have hb := h.pre_inv.argCount_bound
          rw [List.map_cons] at hb ⊢; dsimp only [workArgCount0] at hb ⊢; omega⟩
  have hpre_run' : (preRunAux0 (UInt32.ofNat (workNodeCount0 (out.work.map PreItem0.node)))
      out.nextScope out.st out.work).2 = preRes :=
    preRun_step_eq7 h.pre_inv.nextSc_bound h.pre_run
  have hsub' := preRunAux0_sub_active hpre_inv' hpre_run'
  have hrel := relNodeArgs0_spec preRes.escaped st0.vslot cur.venv cur.node
    ⟨st0.remUses, cur.freeSlots⟩ preRes.nextVid.toNat cur.nextSlot (by have := h.preRes_nv; omega)
    (ActiveDefScope0 preSt (curPre :: restPre)) hlin hnj hng
    (by rw [hst0_eqs.2.2.2]; exact h.st_rem_sz)
    (fun v hv => Nat.lt_of_lt_of_le (hvlt v hv) (by
      have := h.preRes_uses_lt_bd; omega))
    (by rw [hvlen]; exact wfNode0_nodeArgsInVenv0 hwf)
    (fun v hv hesc hpos => by
      have hnv_cur : ∃ w ∈ cur.venv, UInt32.ofNat v = w :=
        Classical.byContradiction fun hnin => False.elim <| by
          have hzer : nodeArgsUses0 (UInt32.ofNat v) cur.venv cur.node = 0 := by
            have ha0 : ∀ a, (∀ idx, a = .var idx → idx.toNat < cur.venv.length) →
                argUses0 (UInt32.ofNat v) cur.venv a = 0 := fun a ha => by
              cases a with
              | immBool _ | immBits _ _ => rfl
              | var idx =>
                dsimp only [argUses0]
                have hne : listGetU32 cur.venv idx ≠ UInt32.ofNat v := fun he => by
                  apply hnin
                  refine ⟨listGetU32 cur.venv idx, ?_, he.symm⟩
                  rw [listGetU32_eq_listGetD, listGetD_eq_getElem7 _ _ _ (ha idx rfl)]
                  exact List.getElem_mem _
                simp [hne]
            have has0 : ∀ xs, (∀ a ∈ xs, ∀ idx, a = .var idx → idx.toNat < cur.venv.length) →
                argsUses0 (UInt32.ofNat v) cur.venv xs = 0 := fun xs hxs => by
              induction xs with
              | nil => rfl
              | cons a rs ih =>
                dsimp only [argsUses0]
                rw [ha0 a (hxs a List.mem_cons_self),
                  ih (fun b hb => hxs b (List.mem_cons_of_mem _ hb))]
            have hva := wfNode0_nodeArgsInVenv0 hwf; rw [← hvlen] at hva
            cases hnd : cur.node <;> rw [hnd] at hlin hnj hng hva
            all_goals first
              | (dsimp only [nodeArgsUses0]; exact has0 _ hva)
              | (dsimp only [nodeArgsUses0]; rw [ha0 _ hva.1, ha0 _ hva.2])
              | (dsimp only [nodeArgsUses0]; exact ha0 _ hva)
              | exact absurd rfl (hnj _ _ _)
              | exact absurd rfl (hng _ _)
              | simp [isTerm0] at hlin
          omega
      obtain ⟨w, hw, hwe⟩ := hnv_cur
      have hv_st : v < preSt.nextVid.toNat := by
        have hwlt := hvlt w hw
        have hwl : w.toNat = v := by
          rw [← hwe, u32_toNat_ofNat7,
            Nat.mod_eq_of_lt (Nat.lt_trans hv (by have := h.preRes_nv; omega))]
        rw [← hwl, ← h.st_nv]; exact hwlt
      refine ⟨hv_st, curPre, List.mem_cons_self, ?_⟩
      by_cases he : preSt.defScope.getD v 0 = curPre.scope.toNat
      · exact he.symm
      · exfalso
        have h0 := hpr_noesc v hv_st hesc curPre List.mem_cons_self
        have hne' : ¬ (curPre.scope.toNat = preSt.defScope.getD v 0) := fun ha => he ha.symm
        simp only [hne', ↓reduceIte, hpn, hpv, ← h.st_nv] at h0
        have hnz := nodeArgsUses0_zero_of_astZero h0
        omega)
    h.preRes_es_bit
    (fun v hv => by
      rw [hst0_eqs.2.2.2]
      exact Nat.lt_of_le_of_lt (h.st_rem_le v hv) (h.preRes_us_bd v hv))
    (fun v hv hesc => by
      rw [hst0_eqs.2.2.2]
      by_cases hpos : 0 < nodeArgsUses0 (UInt32.ofNat v) cur.venv cur.node
      · have hact : ActiveDefScope0 preSt (curPre :: restPre) v := by
          have hv_st : v < preSt.nextVid.toNat := Nat.lt_of_not_le fun hge => False.elim <| by
            have h0 : nodeArgsUses0 (UInt32.ofNat v) cur.venv cur.node = 0 := by
              have hva := wfNode0_nodeArgsInVenv0 hwf; rw [← hvlen] at hva
              have ha0 : ∀ a, (∀ idx, a = .var idx → idx.toNat < cur.venv.length) →
                  argUses0 (UInt32.ofNat v) cur.venv a = 0 := fun a ha => by
                cases a with
                | immBool _ | immBits _ _ => rfl
                | var idx =>
                  dsimp only [argUses0]
                  have hlt := hvlt (listGetU32 cur.venv idx) (by
                    rw [listGetU32_eq_listGetD, listGetD_eq_getElem7 _ _ _ (ha idx rfl)]
                    exact List.getElem_mem _)
                  have hne : listGetU32 cur.venv idx ≠ UInt32.ofNat v := fun he => by
                    have hn := congrArg UInt32.toNat he
                    rw [u32_toNat_ofNat7,
                      Nat.mod_eq_of_lt (Nat.lt_trans hv (by have := h.preRes_nv; omega))] at hn
                    rw [h.st_nv] at hlt; omega
                  simp [hne]
              have has0 : ∀ xs, (∀ a ∈ xs, ∀ idx, a = .var idx → idx.toNat < cur.venv.length) →
                  argsUses0 (UInt32.ofNat v) cur.venv xs = 0 := fun xs hxs => by
                induction xs with
                | nil => rfl
                | cons a rs ih =>
                  dsimp only [argsUses0]
                  rw [ha0 a (hxs a List.mem_cons_self),
                    ih (fun b hb => hxs b (List.mem_cons_of_mem _ hb))]
              cases hnd : cur.node <;> rw [hnd] at hlin hnj hng hva
              all_goals first
                | (dsimp only [nodeArgsUses0]; exact has0 _ hva)
                | (dsimp only [nodeArgsUses0]; rw [ha0 _ hva.1, ha0 _ hva.2])
                | (dsimp only [nodeArgsUses0]; exact ha0 _ hva)
                | exact absurd rfl (hnj _ _ _)
                | exact absurd rfl (hng _ _)
                | simp [isTerm0] at hlin
            omega
          refine ⟨hv_st, curPre, List.mem_cons_self, ?_⟩
          by_cases he : preSt.defScope.getD v 0 = curPre.scope.toNat
          · exact he.symm
          · exfalso
            have h0 := hpr_noesc v hv_st hesc curPre List.mem_cons_self
            have hne' : ¬ (curPre.scope.toNat = preSt.defScope.getD v 0) := fun ha => he ha.symm
            simp only [hne', ↓reduceIte, hpn, hpv, ← h.st_nv] at h0
            have hnz := nodeArgsUses0_zero_of_astZero h0
            omega
        have hsc : curPre.scope.toNat = preSt.defScope.getD v 0 := by
          by_cases he : curPre.scope.toNat = preSt.defScope.getD v 0
          · exact he
          · exfalso
            have h0 := hpr_noesc v hact.1 hesc curPre List.mem_cons_self
            simp only [he, ↓reduceIte, hpn, hpv, ← h.st_nv] at h0
            have hnz := nodeArgsUses0_zero_of_astZero h0
            omega
        rw [h.st_rem_active v (h.st_nv ▸ hact.1) hesc hact]
        dsimp only [sameScopeSpineSum0]
        rw [hsc.symm]; simp only [↓reduceIte, hpv, hpn, ← h.st_nv]
        have hsp_le : nodeArgsUses0 (UInt32.ofNat v) cur.venv cur.node ≤
            spineUses0 (UInt32.ofNat v) cur.venv st.nextVid cur.node := by
          rw [spineUses0_lin (UInt32.ofNat v) cur.venv st.nextVid hlin hnj hng hfit]
          exact Nat.le_add_right _ _
        omega
      · omega)
    (by rw [hst0_eqs.2.2.1, hst0_eqs.2.2.2]; exact activeDefScope0_live_slots_ok h)
    hpool.1 hpool.2.1
  dsimp only at hrel
  change rr.remUses.size = preRes.nextVid.toNat ∧ _ at hrel
  have hrel_rem : ∀ v < preRes.nextVid.toNat, rr.remUses.getD v 0 =
      if preRes.escaped.getD v 0 = 0 then
        st.remUses.getD v 0 - nodeArgsUses0 (UInt32.ofNat v) cur.venv cur.node
      else st.remUses.getD v 0 := fun v hv => by
    have hrs := hrel.2.2.2.1 v hv
    change rr.remUses.getD v 0 = _ at hrs
    rw [hst0_eqs.2.2.2] at hrs
    exact hrs
  have hst_bd_step : st.nextVid.toNat + cnt.toNat ≤ preRes.nextVid.toNat := by
    have htot := h.preRes_uses_lt_bd
    have hle : cnt.toNat ≤ workBinderCount0 ((cur :: rest).map RegaTask0.node) := by
      rw [List.map_cons]; dsimp only [workBinderCount0]
      cases hnd : cur.node with
      | let1 _ _ _ | load _ _ _ =>
        dsimp only [cnt]; rw [hnd]; dsimp only [linCnt0, binderCount0]
        simp only [UInt32.toNat_one]; omega
      | let2Umulw64 _ _ _ =>
        dsimp only [cnt]; rw [hnd]; dsimp only [linCnt0, binderCount0]
        rw [show (2 : UInt32).toNat = 2 from rfl]; omega
      | store _ _ _ _ =>
        dsimp only [cnt]; rw [hnd]; dsimp only [linCnt0, binderCount0]
        rw [UInt32.toNat_zero]; omega
      | call _ _ bs _ _ =>
        rw [hnd] at hfit
        dsimp only [TFlat0.sigLensFitU32, listLenFitsU32] at hfit
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hfit
        dsimp only [cnt]; rw [hnd]; dsimp only [linCnt0, binderCount0]
        rw [tyLenU0_eq_of_lt hfit.1.2]; omega
      | jnz _ _ _ => exact absurd hnd (hnj _ _ _)
      | group _ _ => exact absurd hnd (hng _ _)
      | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt =>
        rw [hnd] at hlin; simp [isTerm0] at hlin
    omega
  have hbr := bindRetsN0_spec preRes.escaped cnt.toNat cnt 0 bl0
    (preRes.nextVid.toNat + fnMaxJump) rfl
    (by dsimp only [bl0, st1]; rw [hst0_eqs.1, hst0_eqs.2.2.1]; exact h.st_vslot_sz)
    (by dsimp only [bl0, st1]; rw [hst0_eqs.1]; have := h.preRes_nv; omega)
    ⟨hrel.2.1, hrel.2.2.1, by dsimp only [bl0, st1]; rw [hst0_eqs.2.1]; exact hpool.2.2.1,
      by dsimp only [bl0, st1]; rw [hst0_eqs.2.1]; exact h.st_maxSl_le, hpool.2.2.2.2⟩
    (by dsimp only [bl0]; omega)
    (fun k hk => by
      dsimp only [bl0, st1]; rw [hst0_eqs.1]
      have hult : st.nextVid.toNat + k < preRes.nextVid.toNat := by omega
      have hes_lt : preRes.escaped.getD (st.nextVid.toNat + k) 0 < 2 ^ 32 := by
        rcases h.preRes_es_bit (st.nextVid.toNat + k) hult with h0 | h1 <;> omega
      have hru_lt : rr.remUses.getD (st.nextVid.toNat + k) 0 < 2 ^ 32 := by
        have hrs := hrel_rem (st.nextVid.toNat + k) hult
        have hbd := Nat.lt_of_le_of_lt (h.st_rem_le (st.nextVid.toNat + k) hult)
          (h.preRes_us_bd (st.nextVid.toNat + k) hult)
        rw [hrs]; split <;> omega
      exact ⟨hes_lt, hru_lt⟩)
  dsimp only at hbr
  obtain ⟨hbr_venv, hbr_nv, hbr_vsz, hbr_rem, hbr_pool, hbr_nlo, hbr_nhi, hbr_fr, hbr_pres,
    hbr_sl⟩ := hbr
  have hst1_nv32 : st1.nextVid = st.nextVid := hst0_eqs.1
  have hst1_nv : st1.nextVid.toNat = st.nextVid.toNat := by
    dsimp only [st1]; rw [hst0_eqs.1]
  have hst1_vsl : st1.vslot = st.vslot := by
    dsimp only [st1]; rw [hst0_eqs.2.2.1]
  have hbl_nv_eq : bl.st.nextVid = out.st.nextVid := by
    apply u32_ext7
    rw [hbr_nv, hst1_nv, h.st_nv, hout]; dsimp only
    rw [hbind_pre.2.1, hst1.1]
  have hbl_venv_eq : bl.venv =
      (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1 := by
    rw [hbr_venv, hbind_pre.1, hst1_nv32, hst1.1, h.st_nv, hpv]
  have hrr_nonew : ∀ v, st.nextVid.toNat ≤ v → v < preRes.nextVid.toNat →
      rr.remUses.getD v 0 = preRes.uses.getD v 0 := by
    intro v hge hv
    have hrs := hrel_rem v hv
    rw [h.st_rem_future v hge hv] at hrs
    have hnu : nodeArgsUses0 (UInt32.ofNat v) cur.venv cur.node = 0 := by
      have hva := wfNode0_nodeArgsInVenv0 hwf; rw [← hvlen] at hva
      have ha0 : ∀ a, (∀ idx, a = .var idx → idx.toNat < cur.venv.length) →
          argUses0 (UInt32.ofNat v) cur.venv a = 0 := fun a ha => by
        cases a with
        | immBool _ | immBits _ _ => rfl
        | var idx =>
          dsimp only [argUses0]
          have hlt := hvlt (listGetU32 cur.venv idx) (by
            rw [listGetU32_eq_listGetD, listGetD_eq_getElem7 _ _ _ (ha idx rfl)]
            exact List.getElem_mem _)
          have hne : listGetU32 cur.venv idx ≠ UInt32.ofNat v := fun he => by
            have hn := congrArg UInt32.toNat he
            rw [u32_toNat_ofNat7,
              Nat.mod_eq_of_lt (Nat.lt_trans hv (by have := h.preRes_nv; omega))] at hn
            omega
          simp [hne]
      have has0 : ∀ xs, (∀ a ∈ xs, ∀ idx, a = .var idx → idx.toNat < cur.venv.length) →
          argsUses0 (UInt32.ofNat v) cur.venv xs = 0 := fun xs hxs => by
        induction xs with
        | nil => rfl
        | cons a rs ih =>
          dsimp only [argsUses0]
          rw [ha0 a (hxs a List.mem_cons_self),
            ih (fun b hb => hxs b (List.mem_cons_of_mem _ hb))]
      cases hnd : cur.node with
      | let1 _ _ _ | call _ _ _ _ _ =>
        rw [hnd] at hva; dsimp only [nodeArgsUses0]; exact has0 _ hva
      | let2Umulw64 _ _ _ | store _ _ _ _ =>
        rw [hnd] at hva; dsimp only [nodeArgsUses0]; rw [ha0 _ hva.1, ha0 _ hva.2]
      | load _ _ _ =>
        rw [hnd] at hva; dsimp only [nodeArgsUses0]; exact ha0 _ hva
      | jnz _ _ _ => exact absurd hnd (hnj _ _ _)
      | group _ _ => exact absurd hnd (hng _ _)
      | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt =>
        rw [hnd] at hlin; simp [isTerm0] at hlin
    rw [hrs, hnu]; split <;> simp
  have hrem_eq_rr : bl.st.remUses = rr.remUses := by rw [hbr_rem]
  have hlive_old_cur : ∀ v < st.nextVid.toNat,
      LiveInTask0 preRes.escaped out.st bl.st
        ⟨linK0 curPre.node,
          (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1,
          curPre.scope⟩
        ⟨0, linK0 cur.node, bl.venv, cur.lenv, bl.free, bl.nxt⟩ v →
      LiveInTask0 preRes.escaped preSt st curPre cur v := by
    intro v hv hlv
    rcases hlv with ⟨hes, hwmem⟩ | ⟨hes, hsc, hpos⟩
    · refine Or.inl ⟨hes, ?_⟩
      rw [hbr_venv, hst1_nv32] at hwmem
      rcases (mem_pushFreshVids0 cnt.toNat st.nextVid cur.venv (UInt32.ofNat v)).mp hwmem
        with h0 | ⟨j, hj, he⟩
      · exact h0
      · have hn := congrArg UInt32.toNat he
        rw [u32_toNat_ofNat7,
          u32_add_ofNat_lt7 (by have := hst_bd_step; have := h.preRes_nv; omega),
          Nat.mod_eq_of_lt (Nat.lt_trans hv (UInt32.toNat_lt _))] at hn
        omega
    · rw [hout] at hsc; dsimp only at hsc
      rw [hbind_pre.2.2.2.2.2.1 v] at hsc
      simp only [show v < preSt1.nextVid.toNat from hst1.1 ▸ h.st_nv ▸ hv, ↓reduceIte] at hsc
      rw [hst1.2.1] at hsc
      have hv_res : v < preRes.nextVid.toNat := Nat.lt_of_lt_of_le hv
        (by have := h.preRes_uses_lt_bd; omega)
      have hru := hrel_rem v hv_res
      rw [hrem_eq_rr] at hpos
      simp only [hes, ↓reduceIte] at hru
      rw [hru] at hpos
      exact Or.inr ⟨hes, hsc, by omega⟩
  have hfree_no_old : ∀ v < st.nextVid.toNat,
      LiveInTask0 preRes.escaped out.st bl.st
        ⟨linK0 curPre.node,
          (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1,
          curPre.scope⟩
        ⟨0, linK0 cur.node, bl.venv, cur.lenv, bl.free, bl.nxt⟩ v →
      arrGetU0 st.vslot (UInt32.ofNat v) ∉ rr.free := by
    intro v hv hlv_lin hm
    have hlv := hlive_old_cur v hv hlv_lin
    rcases (hrel.2.2.2.2.1 _).mp hm with hc | ⟨u, hu, hDu, hescu, hposu, hzu, heq⟩
    · exact (hlive v hv hlv).2.1 hc
    · rw [hst1_vsl] at heq
      have hu_lt : u < st.nextVid.toNat := h.st_nv ▸ hDu.1
      change rr.remUses.getD u 0 = 0 at hzu
      have hposu' : 0 < st.remUses.getD u 0 := hst0_eqs.2.2.2 ▸ hposu
      have hne : u ≠ v := by
        rintro rfl
        rcases hlv_lin with ⟨hes1, _⟩ | ⟨_, _, hpos'⟩
        · rw [hescu] at hes1; cases hes1
        · rw [hrem_eq_rr, hzu] at hpos'; exact Nat.lt_irrefl 0 hpos'
      have hlu_cur : LiveInTask0 preRes.escaped preSt st curPre cur u := by
        have hr_u := hrel_rem u hu
        simp only [hescu, ↓reduceIte] at hr_u
        have hpos_nu : 0 < nodeArgsUses0 (UInt32.ofNat u) cur.venv cur.node := by omega
        have hsc_u : curPre.scope.toNat = preSt.defScope.getD u 0 := by
          by_cases he : curPre.scope.toNat = preSt.defScope.getD u 0
          · exact he
          · exfalso
            have h0 := hpr_noesc u (h.st_nv ▸ hu_lt) hescu curPre List.mem_cons_self
            simp only [he, ↓reduceIte, hpn, hpv, ← h.st_nv] at h0
            have hnz := nodeArgsUses0_zero_of_astZero h0
            omega
        exact Or.inr ⟨hescu, hsc_u, hposu'⟩
      exact (hlive v hv hlv).2.2 u hu_lt hne hlu_cur heq.symm
  have hfree_no_wait : ∀ info ∈ mCur.gl, info.waiting = true →
      ∀ s ∈ info.tgts, s ∉ rr.free := by
    intro info hi hw s hs hm
    rcases (hrel.2.2.2.2.1 _).mp hm with hc | ⟨u, hu, hDu, hescu, hposu, hzu, rfl⟩
    · exact ((hwait info hi hw).1 s hs).2 hc
    · rw [hst1_vsl] at hs
      have hu_lt : u < st.nextVid.toNat := h.st_nv ▸ hDu.1
      change rr.remUses.getD u 0 = 0 at hzu
      have hposu' : 0 < st.remUses.getD u 0 := hst0_eqs.2.2.2 ▸ hposu
      have hsc_u : curPre.scope.toNat = preSt.defScope.getD u 0 := by
        have hru := hrel_rem u hu
        simp only [hescu, ↓reduceIte] at hru
        by_cases he : curPre.scope.toNat = preSt.defScope.getD u 0
        · exact he
        · exfalso
          have h0 := hpr_noesc u (h.st_nv ▸ hu_lt) hescu curPre List.mem_cons_self
          simp only [he, ↓reduceIte, hpn, hpv, ← h.st_nv] at h0
          have hnz := nodeArgsUses0_zero_of_astZero h0
          omega
      exact (hwait info hi hw).2 u hu_lt (Or.inr ⟨hescu, hsc_u, hposu'⟩) hs
  have hrem_act' : ∀ v < bl.st.nextVid.toNat, preRes.escaped.getD v 0 = 0 →
      ActiveDefScope0 out.st out.work v →
      bl.st.remUses.getD v 0 =
        sameScopeSpineSum0 (UInt32.ofNat v) (out.st.defScope.getD v 0)
          out.st.nextVid out.work := by
    intro v hv hesc hact
    rw [hout] at hact ⊢; dsimp only at hact ⊢
    rw [hrem_eq_rr]
    have hv_pre : v < preRes.nextVid.toNat := by
      rw [hbr_nv, hst1_nv] at hv; exact Nat.lt_of_lt_of_le hv hst_bd_step
    by_cases hv_old : v < st.nextVid.toNat
    · have hds_v :
          (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).2.defScope.getD v 0 =
            preSt.defScope.getD v 0 := by
        rw [hbind_pre.2.2.2.2.2.1 v]
        simp only [show v < preSt1.nextVid.toNat from hst1.1 ▸ h.st_nv ▸ hv_old, ↓reduceIte]
        rw [hst1.2.1]
      rw [hds_v]
      have hact_old : ActiveDefScope0 preSt (curPre :: restPre) v := by
        refine ⟨h.st_nv ▸ hv_old, ?_⟩
        obtain ⟨q, hq, hq_sc⟩ := hact.2
        rw [hds_v] at hq_sc
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact ⟨curPre, List.mem_cons_self, hq_sc⟩
        · exact ⟨q, List.mem_cons_of_mem _ hq', hq_sc⟩
      have hru := hrel_rem v hv_pre
      simp only [hesc, ↓reduceIte] at hru
      rw [hru, h.st_rem_active v hv_old hesc hact_old]
      have hrest_congr := sameScopeSpineSum0_congr_nv (vid := UInt32.ofNat v)
        (ds := preSt.defScope.getD v 0) (nv₁ := preSt.nextVid)
        (nv₂ := (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).2.nextVid)
        (work := restPre)
        (by rw [u32_toNat_ofNat7, Nat.mod_eq_of_lt (Nat.lt_trans hv_old (UInt32.toNat_lt _))]
            exact h.st_nv ▸ hv_old)
        (by rw [hbind_pre.2.1, hst1.1]; exact Nat.le_add_right _ _)
        (by rw [hbind_pre.2.1, hst1.1]
            have hbc := h.pre_inv.nextVid_bound
            rw [List.map_cons] at hbc; dsimp only [workBinderCount0] at hbc
            have := hbc_l'; rw [hcnt_eq] at this; omega)
      have hnv_pre' :
          (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).2.nextVid =
            preSt.nextVid + UInt32.ofNat cnt.toNat := by
        apply u32_ext7
        rw [hbind_pre.2.1, hst1.1,
          u32_add_ofNat_lt7 (by
            rw [← h.st_nv]
            exact Nat.lt_of_le_of_lt hst_bd_step (Nat.lt_trans h.preRes_nv (by decide)))]
      by_cases heq_sc : preSt.defScope.getD v 0 = curPre.scope.toNat
      · have hrest_zero : ∀ q ∈ restPre, q.scope.toNat ≠ preSt.defScope.getD v 0 := fun q hq he =>
          hrest_scopes q hq (u32_ext7 (by omega))
        have hsum_z1 := sameScopeSpineSum0_eq_zero (vid := UInt32.ofNat v)
          (ds := preSt.defScope.getD v 0) (nxt := preSt.nextVid) hrest_zero
        have hsum_z2 := sameScopeSpineSum0_eq_zero (vid := UInt32.ofNat v)
          (ds := preSt.defScope.getD v 0)
          (nxt := (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).2.nextVid)
          hrest_zero
        dsimp only [sameScopeSpineSum0]
        simp only [ite_eq_left heq_sc, hsum_z1, hsum_z2, Nat.add_zero]
        rw [hnv_pre', hbind_pre.1, hst1.1, hpv, hpn, ← h.st_nv]
        dsimp only [cnt]
        rw [spineUses0_lin (UInt32.ofNat v) cur.venv st.nextVid hlin hnj hng hfit]
        omega
      · have hne_sc : ¬ (curPre.scope.toNat = preSt.defScope.getD v 0) := Ne.symm heq_sc
        dsimp only [sameScopeSpineSum0]
        simp only [ite_eq_right heq_sc, Nat.zero_add, hrest_congr]
        have h0 := hpr_noesc v (h.st_nv ▸ hv_old) hesc curPre List.mem_cons_self
        simp only [hne_sc, ↓reduceIte, hpn, hpv, ← h.st_nv] at h0
        have hnz := nodeArgsUses0_zero_of_astZero h0
        omega
    · have hv_ge : st.nextVid.toNat ≤ v := Nat.le_of_not_lt hv_old
      rw [hrr_nonew v hv_ge hv_pre]
      have hu_eq := hsub'.1.2.2.2.2.2 v (by rw [← hbl_nv_eq]; exact hv)
      rw [hout] at hu_eq; dsimp only at hu_eq
      rw [hbind_pre.2.2.2.2.2.2.1 v] at hu_eq
      have hnv_not : ¬ v < preSt1.nextVid.toNat := by rw [hst1.1, ← h.st_nv]; exact hv_old
      simp only [hnv_not, ↓reduceIte, Nat.zero_add] at hu_eq
      exact hu_eq
  let outPre : PreItem0 := PreItem0.mk (linK0 curPre.node)
    (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1 curPre.scope
  let outStPre := (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).2
  let outTask : RegaTask0 := RegaTask0.mk 0 (linK0 cur.node) bl.venv cur.lenv bl.free bl.nxt
  have hout_st : out.st = outStPre := by rw [hout]
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
      len_pw := by rw [hout, hls_eq.2.2]; simpa using h.len_pw
      len_mw := by rw [hls_eq.2.2]; simpa using h.len_mw
      seenJnz_safe := by
        rw [hls_eq.2.2]; have hs := h.seenJnz_safe
        simp only [List.map_cons] at hs
        rwa [jnzGroupSafeWork0_lin seenJnz hlin hnj hng] at hs
      seenJnz_ctrl := by rw [hls_eq.2.1]; exact h.seenJnz_ctrl
      maxJump_bd := by
        rw [hls_eq.2.2]; have hm := h.maxJump_bd
        rw [List.map_cons] at hm ⊢; dsimp only [workMaxJumpArity0] at hm ⊢
        rw [hmja_l]; exact hm
      ctrl_fn := hls_eq.2.1 ▸ h.ctrl_fn
      ctrl_nl := by
        rw [hls_eq.2.1, hls_eq.2.2]; have hnl := h.ctrl_nl
        rw [List.map_cons] at hnl ⊢; dsimp only [workNodeCount0] at hnl ⊢
        exact ⟨hnl.1, by omega⟩
      st_nv := by rw [hls_eq.1, hbl_nv_eq]
      st_vslot_sz := by rw [hls_eq.1, hbr_vsz, hbr_nv]
      st_rem_sz := by rw [hls_eq.1, hrem_eq_rr]; exact hrel.1
      st_maxSl_le := by rw [hls_eq.1]; exact hbr_pool.2.2.2.1
      st_rem_le := fun v hv => by
        rw [hls_eq.1, hrem_eq_rr]
        have hrs := hrel_rem v hv
        have hle := h.st_rem_le v hv
        rw [hrs]; split <;> omega
      st_rem_future := fun v h1 h2 => by
        rw [hls_eq.1, hbr_nv, hst1_nv] at h1
        rw [hls_eq.1, hrem_eq_rr]
        exact hrr_nonew v (by omega) h2
      st_rem_active := fun v hv hesc hact => by
        rw [hls_eq.1] at hv ⊢
        exact hrem_act' v hv hesc hact
      items_ok := fun i hi1 hi2 hi3 => by
        have hi1' : i < (outPre :: restPre).length := by rw [hout] at hi1; exact hi1
        have hi2' : i < (outTask :: rest).length := by rw [hls_eq.2.2] at hi2; exact hi2
        rw [show out.work[i] = (outPre :: restPre)[i]'hi1' from by simp [hout, outPre],
          show ls.work[i] = (outTask :: rest)[i]'hi2' from by simp [hls_eq.2.2, outTask],
          hout_st, hls_eq.1, hls_eq.2.1]
        cases i with
        | zero =>
          dsimp only [List.getElem_cons_zero, outPre, outStPre, outTask]
          have hvlt_bl : ∀ v ∈ bl.venv, v.toNat < bl.st.nextVid.toNat := by
            intro v hm; rw [hbr_nv, hst1_nv]
            rw [hbr_venv, hst1_nv32] at hm
            rcases (mem_pushFreshVids0 cnt.toNat st.nextVid cur.venv v).mp hm
              with h0 | ⟨j, hj, rfl⟩
            · exact Nat.lt_of_lt_of_le (hvlt v h0) (Nat.le_add_right _ _)
            · rw [u32_add_ofNat_lt7 (by have := hst_bd_step; have := h.preRes_nv; omega)]; omega
          have hgi' : ∀ (idx : Nat) (h1 : idx < m0.gl.length) (h2 : idx < cur.lenv.length)
              (h3 : idx < m0.lT.length),
              m0.gl[idx].lbl = cur.lenv[idx] ∧ m0.gl[idx].pts = m0.lT[idx] := by
            intro idx h1 h2 h3; exact hgi idx h1 h2 h3
          refine ⟨hpn ▸ rfl, hbl_venv_eq.symm,
            by rw [hbr_venv, pushFreshVids0_length, hvlen, hvlen_l], hvlt_bl, hllen, hgl,
            hgi', hwfl, hfitl, hsbgl, hnbl, hbr_pool,
            by dsimp only [bl, bl0] at hbr_nv hbr_nhi ⊢; rw [hbr_nv, hst1_nv]; omega,
            fun info hi => lblInfoOk0_mono (hinfo_ok info hi) (Nat.le_refl _) (fun _ _ _ => rfl)
              (by rw [hbr_nv, hst1_nv]; exact Nat.le_add_right _ _)
              (by rw [← hst0_eqs.2.1]
                  exact bindRetsN0_maxSlots_le preRes.escaped cnt.toNat cnt 0 bl0 rfl)
              (fun v hv => by rw [hbr_pres v (hst1_nv ▸ hv), hst1_vsl]),
            fun info hi hw => ?_, trivial, fun v hv hlv => ?_⟩
          · refine ⟨fun s hs => ⟨Nat.lt_of_lt_of_le ((hwait info hi hw).1 s hs).1 hbr_nlo,
              fun hm => hfree_no_wait info hi hw s hs (hbr_fr s hm)⟩, fun v' hv' hlv'' => ?_⟩
            have hlv_o : LiveInTask0 preRes.escaped out.st bl.st
                ⟨linK0 curPre.node,
                  (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1,
                  curPre.scope⟩
                ⟨0, linK0 cur.node, bl.venv, cur.lenv, bl.free, bl.nxt⟩ v' := by
              simpa [hout_st] using hlv''
            rw [hbr_nv, hst1_nv] at hv'
            by_cases hvo : v' < st.nextVid.toNat
            · rw [hbr_pres v' (hst1_nv ▸ hvo), hst1_vsl]
              exact (hwait info hi hw).2 v' hvo (hlive_old_cur v' hvo hlv_o)
            · have hvk : ∃ k < cnt.toNat, v' = st.nextVid.toNat + k := ⟨v' - st.nextVid.toNat,
                by omega, by omega⟩
              obtain ⟨k, hk, rfl⟩ := hvk
              have hneed : 0 < rr.remUses.getD (st.nextVid.toNat + k) 0 ∨
                  0 < preRes.escaped.getD (st.nextVid.toNat + k) 0 := by
                rcases hlv_o with ⟨hes1, _⟩ | ⟨_, _, hpos⟩
                · right; omega
                · left; rwa [← hrem_eq_rr]
              have hslk := hbr_sl k hk (by dsimp only [bl0, st1]; rw [hst0_eqs.1]; exact hneed)
              rw [hst1_nv] at hslk
              intro hm
              dsimp only [bl, bl0] at hm hslk
              rcases hslk.2.2.1 with hfr | hge
              · exact hfree_no_wait info hi hw _ hm hfr
              · have := ((hwait info hi hw).1 _ hm).1; omega
          · rw [hbr_nv, hst1_nv] at hv
            have hsingle : ∀ u < st.nextVid.toNat + cnt.toNat,
                LiveInTask0 preRes.escaped out.st bl.st
                  ⟨linK0 curPre.node,
                    (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1,
                    curPre.scope⟩
                  ⟨0, linK0 cur.node, bl.venv, cur.lenv, bl.free, bl.nxt⟩ u →
                (arrGetU0 bl.st.vslot (UInt32.ofNat u)).toNat < bl.nxt.toNat ∧
                arrGetU0 bl.st.vslot (UInt32.ofNat u) ∉ bl.free := by
              intro u hu hlu
              by_cases huo : u < st.nextVid.toNat
              · rw [hbr_pres u (hst1_nv ▸ huo), hst1_vsl]
                have hlu_cur := hlive_old_cur u huo hlu
                refine ⟨Nat.lt_of_lt_of_le (hlive u huo hlu_cur).1 hbr_nlo, fun hm => ?_⟩
                exact hfree_no_old u huo hlu (hbr_fr _ hm)
              · obtain ⟨k, hk, rfl⟩ : ∃ k < cnt.toNat, u = st.nextVid.toNat + k :=
                  ⟨u - st.nextVid.toNat, by omega, by omega⟩
                have hneed : 0 < rr.remUses.getD (st.nextVid.toNat + k) 0 ∨
                    0 < preRes.escaped.getD (st.nextVid.toNat + k) 0 := by
                  rcases hlu with ⟨hes1, _⟩ | ⟨_, _, hpos⟩
                  · right; omega
                  · left; rwa [← hrem_eq_rr]
                have hslk := hbr_sl k hk (by dsimp only [bl0, st1]; rw [hst0_eqs.1]; exact hneed)
                rw [hst1_nv] at hslk
                exact ⟨hslk.1, hslk.2.1⟩
            have hlv' : LiveInTask0 preRes.escaped out.st bl.st
                ⟨linK0 curPre.node,
                  (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1,
                  curPre.scope⟩
                ⟨0, linK0 cur.node, bl.venv, cur.lenv, bl.free, bl.nxt⟩ v := by
              simpa [hout_st] using hlv
            obtain ⟨hs_lt, hs_nf⟩ := hsingle v hv hlv'
            refine ⟨hs_lt, hs_nf, fun w hw hne hlw => ?_⟩
            have hlw' : LiveInTask0 preRes.escaped out.st bl.st
                ⟨linK0 curPre.node,
                  (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1,
                  curPre.scope⟩
                ⟨0, linK0 cur.node, bl.venv, cur.lenv, bl.free, bl.nxt⟩ w := by
              simpa [hout_st] using hlw
            rw [hbr_nv, hst1_nv] at hw
            by_cases hvo : v < st.nextVid.toNat <;> by_cases hwo : w < st.nextVid.toNat
            · rw [hbr_pres v (hst1_nv ▸ hvo), hbr_pres w (hst1_nv ▸ hwo), hst1_vsl]
              exact (hlive v hvo (hlive_old_cur v hvo hlv')).2.2 w hwo hne
                (hlive_old_cur w hwo hlw')
            · obtain ⟨kw, hkw, rfl⟩ : ∃ kw < cnt.toNat, w = st.nextVid.toNat + kw :=
                ⟨w - st.nextVid.toNat, by omega, by omega⟩
              have hneed_w : 0 < rr.remUses.getD (st.nextVid.toNat + kw) 0 ∨
                  0 < preRes.escaped.getD (st.nextVid.toNat + kw) 0 := by
                rcases hlw' with ⟨hes1, _⟩ | ⟨_, _, hpos⟩
                · right; omega
                · left; rwa [← hrem_eq_rr]
              have hslw := hbr_sl kw hkw (by dsimp only [bl0, st1]; rw [hst0_eqs.1]; exact hneed_w)
              rw [hst1_nv] at hslw
              dsimp only [bl0] at hslw
              rw [hbr_pres v (hst1_nv ▸ hvo), hst1_vsl]
              have hv_cur := hlive_old_cur v hvo hlv'
              intro hcol
              rcases hslw.2.2.1 with hfr | hge
              · rw [hcol] at hfr; exact hfree_no_old v hvo hlv' hfr
              · dsimp only [bl] at hcol
                have := (hlive v hvo hv_cur).1; rw [hcol] at hge; omega
            · obtain ⟨kv, hkv, rfl⟩ : ∃ kv < cnt.toNat, v = st.nextVid.toNat + kv :=
                ⟨v - st.nextVid.toNat, by omega, by omega⟩
              have hneed_v : 0 < rr.remUses.getD (st.nextVid.toNat + kv) 0 ∨
                  0 < preRes.escaped.getD (st.nextVid.toNat + kv) 0 := by
                rcases hlv' with ⟨hes1, _⟩ | ⟨_, _, hpos⟩
                · right; omega
                · left; rwa [← hrem_eq_rr]
              have hslv := hbr_sl kv hkv (by dsimp only [bl0, st1]; rw [hst0_eqs.1]; exact hneed_v)
              rw [hst1_nv] at hslv
              dsimp only [bl0] at hslv
              rw [hbr_pres w (hst1_nv ▸ hwo), hst1_vsl]
              have hw_cur := hlive_old_cur w hwo hlw'
              intro hcol
              rcases hslv.2.2.1 with hfr | hge
              · rw [← hcol] at hfr; exact hfree_no_old w hwo hlw' hfr
              · dsimp only [bl] at hcol
                have := (hlive w hwo hw_cur).1; rw [← hcol] at hge; omega
            · obtain ⟨kv, hkv, rfl⟩ : ∃ kv < cnt.toNat, v = st.nextVid.toNat + kv :=
                ⟨v - st.nextVid.toNat, by omega, by omega⟩
              obtain ⟨kw, hkw, rfl⟩ : ∃ kw < cnt.toNat, w = st.nextVid.toNat + kw :=
                ⟨w - st.nextVid.toNat, by omega, by omega⟩
              have hne_k : kw ≠ kv := fun he => hne (by omega)
              have hneed_v : 0 < rr.remUses.getD (st.nextVid.toNat + kv) 0 ∨
                  0 < preRes.escaped.getD (st.nextVid.toNat + kv) 0 := by
                rcases hlv' with ⟨hes1, _⟩ | ⟨_, _, hpos⟩
                · right; omega
                · left; rwa [← hrem_eq_rr]
              have hneed_w : 0 < rr.remUses.getD (st.nextVid.toNat + kw) 0 ∨
                  0 < preRes.escaped.getD (st.nextVid.toNat + kw) 0 := by
                rcases hlw' with ⟨hes1, _⟩ | ⟨_, _, hpos⟩
                · right; omega
                · left; rwa [← hrem_eq_rr]
              rcases Nat.lt_or_gt_of_ne hne_k with hlt_k | hgt_k
              · have hslv := hbr_sl kv hkv
                  (by dsimp only [bl0, st1]; rw [hst0_eqs.1]; exact hneed_v)
                rw [hst1_nv] at hslv
                exact hslv.2.2.2 kw hlt_k hneed_w
              · have hslw := hbr_sl kw hkw
                  (by dsimp only [bl0, st1]; rw [hst0_eqs.1]; exact hneed_w)
                rw [hst1_nv] at hslw
                exact Ne.symm (hslw.2.2.2 kv hgt_k hneed_v)
        | succ j' =>
          dsimp only [List.getElem_cons_succ, outStPre]
          have hj'_lt : j' < restPre.length := by simp only [List.length_cons] at hi1'; omega
          have htm := h.items_ok (j' + 1) (by simp only [List.length_cons] at hi1' ⊢; omega)
            (by simp only [List.length_cons] at hi2' ⊢; omega)
            (by simp only [List.length_cons] at hi3 ⊢; omega)
          dsimp only [List.getElem_cons_succ] at htm
          refine taskMetaOk0_mono_rest htm
            (fun w hw1 hw2 => by
              rw [hbind_pre.2.2.2.2.2.1 w]
              have hnw : ¬ w < preSt1.nextVid.toNat := by
                rw [hst1.1, ← h.st_nv]; exact Nat.not_lt_of_ge hw1
              have hltw : w < preSt1.nextVid.toNat + cnt.toNat := by
                have := hbind_pre.2.1; omega
              simp only [hnw, hltw, ↓reduceIte]
              intro he
              exact hrest_scopes (restPre[j']'hj'_lt) (List.getElem_mem hj'_lt) (u32_ext7 he))
            (fun v hv => by
              rw [hbind_pre.2.2.2.2.2.1 v]
              simp only [show v < preSt1.nextVid.toNat from hst1.1 ▸ hv, ↓reduceIte]
              rw [hst1.2.1])
            (by rw [hbind_pre.2.1, hst1.1]; exact Nat.le_add_right _ _)
            h.st_nv (by rw [hbl_nv_eq, hout])
            (by rw [← hst0_eqs.2.1]
                exact bindRetsN0_maxSlots_le preRes.escaped cnt.toNat cnt 0 bl0 rfl)
            hbr_pool.2.2.2.1
            (fun v hv => by rw [hbr_pres v (hst1_nv ▸ hv), hst1_vsl])
            (Nat.le_refl _) (fun _ _ _ => rfl)
            (fun v hv hesc hsc => by
              have hsc_ne : curPre.scope.toNat ≠ preSt.defScope.getD v 0 := by
                rw [← hsc]
                intro he
                exact hrest_scopes (restPre[j']'hj'_lt) (List.getElem_mem hj'_lt)
                  (u32_ext7 he.symm)
              have h0 := hpr_noesc v (h.st_nv ▸ hv) hesc curPre List.mem_cons_self
              have hne' : ¬ (curPre.scope.toNat = preSt.defScope.getD v 0) := hsc_ne
              simp only [hne', ↓reduceIte, hpn, hpv, ← h.st_nv] at h0
              have hnz := nodeArgsUses0_zero_of_astZero h0
              have hrs := hrel_rem v (Nat.lt_of_lt_of_le hv
                (by have := h.preRes_uses_lt_bd; omega))
              simp only [hesc, ↓reduceIte] at hrs
              rw [hrem_eq_rr, hrs, hnz, Nat.sub_zero])
      later_live := fun i j hi1 hi2 hi3 hj1 hj2 hij w hw hlive_j => by
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [hls_eq.1] at hw
        rw [hbr_nv, hst1_nv] at hw
        have hi1' : i < (outPre :: restPre).length := by rw [hout] at hi1; exact hi1
        have hj1' : j' + 1 < (outPre :: restPre).length := by rw [hout] at hj1; exact hj1
        have hi2' : i < (outTask :: rest).length := by rw [hls_eq.2.2] at hi2; exact hi2
        have hj2' : j' + 1 < (outTask :: rest).length := by rw [hls_eq.2.2] at hj2; exact hj2
        have hj'_lt : j' < restPre.length := by simp only [List.length_cons] at hj1'; omega
        have hj2'_lt : j' < rest.length := by simp only [List.length_cons] at hj2'; omega
        rw [show out.work[j' + 1] = restPre[j']'hj'_lt from by simp [hout],
          show ls.work[j' + 1] = rest[j']'hj2'_lt from by simp [hls_eq.2.2],
          hout_st, hls_eq.1] at hlive_j
        rw [show out.work[i] = (outPre :: restPre)[i]'hi1' from by simp [hout, outPre],
          show ls.work[i] = (outTask :: rest)[i]'hi2' from by simp [hls_eq.2.2, outTask],
          hout_st, hls_eq.1]
        have hwf_j : w < st.nextVid.toNat := by
          rcases hlive_j with ⟨_, hwmem⟩ | ⟨_, hsc, _⟩
          · have htmj := h.items_ok (j' + 1)
              (by simp only [List.length_cons] at hj1' ⊢; omega)
              (by simp only [List.length_cons] at hj2' ⊢; omega)
              (by have hlm := h.len_mw; simp only [List.length_cons] at hlm hj2' ⊢; omega)
            have := htmj.2.2.2.1 (UInt32.ofNat w) hwmem
            rwa [u32_toNat_ofNat7, Nat.mod_eq_of_lt (Nat.lt_trans hw (by
              have := h.preRes_uses_lt_bd; have := h.preRes_nv; omega))] at this
          · exact Nat.lt_of_not_le fun hge' => False.elim <| by
              dsimp only [outStPre] at hsc
              rw [hbind_pre.2.2.2.2.2.1 w] at hsc
              have hnw : ¬ w < preSt1.nextVid.toNat := by
                rw [hst1.1, ← h.st_nv]; exact Nat.not_lt_of_ge hge'
              have hlt_w : w < preSt1.nextVid.toNat + cnt.toNat := by
                rw [hst1.1, ← h.st_nv]; exact hw
              simp only [hnw, hlt_w, ↓reduceIte] at hsc
              exact hrest_scopes (restPre[j']'hj'_lt) (List.getElem_mem hj'_lt) (u32_ext7 hsc)
        have hiff_rest : ∀ (k : Nat) (hk1 : k < restPre.length) (hk2 : k < rest.length)
            (hk1s : k + 1 < (curPre :: restPre).length) (hk2s : k + 1 < (cur :: rest).length),
            LiveInTask0 preRes.escaped outStPre bl.st restPre[k] rest[k] w ↔
            LiveInTask0 preRes.escaped preSt st ((curPre :: restPre)[k + 1]'hk1s)
              ((cur :: rest)[k + 1]'hk2s) w := by
          intro k hk1 hk2 hk1s hk2s
          simp only [LiveInTask0, outStPre]
          rw [hbind_pre.2.2.2.2.2.1 w]
          simp only [show w < preSt1.nextVid.toNat from hst1.1 ▸ h.st_nv ▸ hwf_j,
            ↓reduceIte, hrem_eq_rr]
          rw [hst1.2.1]
          have hrs := hrel_rem w (Nat.lt_of_lt_of_le hwf_j
            (by have := h.preRes_uses_lt_bd; omega))
          rcases h.preRes_es_bit w (Nat.lt_of_lt_of_le hwf_j
              (by have := h.preRes_uses_lt_bd; omega)) with he0 | he1
          · simp only [he0, ↓reduceIte] at hrs
            by_cases hsc : restPre[k].scope.toNat = preSt.defScope.getD w 0
            · have hne_s : ¬ (curPre.scope.toNat = preSt.defScope.getD w 0) := fun he =>
                hrest_scopes restPre[k] (List.getElem_mem hk1) (u32_ext7 (hsc.trans he.symm))
              have h0 := hpr_noesc w (h.st_nv ▸ hwf_j) he0 curPre List.mem_cons_self
              simp only [hne_s, ↓reduceIte, hpn, hpv, ← h.st_nv] at h0
              have hnz := nodeArgsUses0_zero_of_astZero h0
              simp only [he0, hsc, hrs, hnz, Nat.sub_zero, Nat.zero_ne_one, false_and, false_or,
                true_and, List.getElem_cons_succ]
            · simp only [he0, hsc, Nat.zero_ne_one, false_and, false_or, List.getElem_cons_succ]
          · simp only [he1, Nat.one_ne_zero, false_and, or_false, true_and,
              List.getElem_cons_succ]
        have hj_old := (hiff_rest j' hj'_lt hj2'_lt (Nat.succ_lt_succ hj'_lt)
          (Nat.succ_lt_succ hj2'_lt)).mp hlive_j
        cases i with
        | zero =>
          have hcov := h.later_live 0 (j' + 1) (by simp) (by simp) (by simp)
            (by simp only [List.length_cons] at hj1'; omega)
            (by simp only [List.length_cons] at hj2'; omega) (Nat.zero_lt_succ j') w hwf_j hj_old
          rcases hcov with hl0 | ⟨info, hm, hwt, hsl⟩
          · left
            dsimp only [List.getElem_cons_zero] at hl0 ⊢
            rcases hl0 with ⟨hes, hwmem⟩ | ⟨hes, hsc, _⟩
            · refine Or.inl ⟨hes, ?_⟩
              dsimp only [outTask]; rw [hbr_venv, hst1_nv32]
              exact (mem_pushFreshVids0 cnt.toNat st.nextVid cur.venv _).mpr (Or.inl hwmem)
            · exfalso
              rcases hj_old with ⟨hes1, _⟩ | ⟨_, hsc_j, _⟩
              · rw [hes] at hes1; cases hes1
              · dsimp only [List.getElem_cons_succ] at hsc_j
                exact hrest_scopes (restPre[j']'hj'_lt) (List.getElem_mem hj'_lt)
                  (u32_ext7 (hsc_j.trans hsc.symm))
          · right
            dsimp only [List.getElem_cons_zero] at hm ⊢
            refine ⟨info, hm, hwt, ?_⟩
            rw [hbr_pres w (hst1_nv ▸ hwf_j), hst1_vsl]; exact hsl
        | succ i' =>
          dsimp only [List.getElem_cons_succ]
          have hi'_lt : i' < restPre.length := by simp only [List.length_cons] at hi1'; omega
          have hcov := h.later_live (i' + 1) (j' + 1)
            (by simp only [List.length_cons] at hi1'; omega)
            (by simp only [List.length_cons] at hi2'; omega)
            (by have hlm := h.len_mw; simp only [List.length_cons] at hlm hi2' ⊢; omega)
            (by simp only [List.length_cons] at hj1'; omega)
            (by simp only [List.length_cons] at hj2'; omega) hij w hwf_j hj_old
          rcases hcov with hli | ⟨info, hm, hwt, hsl⟩
          · left
            exact (hiff_rest i' hi'_lt
              (by simp only [List.length_cons] at hi2'; omega)
              (Nat.succ_lt_succ hi'_lt)
              (by simp only [List.length_cons] at hi2' ⊢; omega)).mpr hli
          · right
            refine ⟨info, hm, hwt, ?_⟩
            rw [hbr_pres w (hst1_nv ▸ hwf_j), hst1_vsl]; exact hsl }

end LeanQbe.T.Bootstrap0
