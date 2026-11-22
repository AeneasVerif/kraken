module

public import LeanQbe.T.Bootstrap0.Sound0Part4

/-!
# Bootstrap Stage B (`Sound0Part5`): `PrePass0` Execution, Lockstep `Rega0`, & Labels

Establishes:
1. Full `PrePass0` worklist invariant (`preRunAux0_inv`, `compileFnPre0_inv`).
2. Lockstep `PrePass0` ↔ `Rega0` invariant (`SlotPoolInv0`, `CtrlInv0`, `releaseArgs0_inv`,
   `ctrl.lblSlots.size = ctrl.nextLbl.toNat`, `compileFn0_maxSlots_lt`).
3. Structural label uniqueness (`LabOk0`, `lrange0`, `Nat.repr` digit injectivity,
   `compileFn0_labelsUnique`, `compileFn0_label_mem`).
   (x64-only `Compiler0` verification targeting `LeanQbe.T.Amd64.ScalarTarg` via `Sound0Part1`.)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T
open LeanQbe.T.Amd64

private theorem u32_ext_toNat5 {a b : UInt32} (h : a.toNat = b.toNat) : a = b :=
  UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

private theorem u32_toNat_ofNat5 (n : Nat) : (UInt32.ofNat n).toNat = n % 2 ^ 32 := by
  rw [← UInt32.toNat_toBitVec]
  exact BitVec.toNat_ofNat n 32

private theorem u32_sub1_toNat5 {x : UInt32} (hx : 0 < x.toNat) :
    (x - 1).toNat = x.toNat - 1 := by
  refine UInt32.toNat_sub_of_le x 1 ?_
  exact UInt32.le_iff_toNat_le.mpr (by rw [UInt32.toNat_one]; exact hx)

private theorem u32_add1_toNat5 {x : UInt32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt hx]

private theorem u32_eq_add_of_toNat5 {a b : UInt32} {m : Nat} (h : b.toNat = a.toNat + m)
    (hlt : a.toNat + m < 2 ^ 32) : b = a + UInt32.ofNat m := by
  apply u32_ext_toNat5
  rw [h, UInt32.toNat_add, u32_toNat_ofNat5,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hlt), Nat.mod_eq_of_lt hlt]

theorem preRunAux0_inv (ctx : LegalCtx0) :
    ∀ (N : Nat) (fuel nextSc : UInt32) (st : PreSt0) (work : List PreItem0),
      workNodeCount0 (work.map PreItem0.node) = N →
      N ≤ fuel.toNat →
      PreWorkInv0 ctx nextSc st work →
      let r := preRunAux0 fuel nextSc st work
      r.2.nextVid.toNat = st.nextVid.toNat + workBinderCount0 (work.map PreItem0.node) ∧
      r.2.defScope.size = r.2.nextVid.toNat ∧
      r.2.uses.size = r.2.nextVid.toNat ∧
      r.2.escaped.size = r.2.nextVid.toNat ∧
      nextSc.toNat ≤ r.1.toNat ∧ r.1.toNat ≤ nextSc.toNat + 2 * N ∧
      (∀ v < st.nextVid.toNat, r.2.defScope.getD v 0 = st.defScope.getD v 0) ∧
      (∀ v < r.2.nextVid.toNat, r.2.defScope.getD v 0 < r.1.toNat) ∧
      (∀ v < st.nextVid.toNat, st.escaped.getD v 0 = 1 → r.2.escaped.getD v 0 = 1) ∧
      (∀ v < r.2.nextVid.toNat, r.2.escaped.getD v 0 = 0 ∨ r.2.escaped.getD v 0 = 1) ∧
      (∀ v < r.2.nextVid.toNat,
        r.2.uses.getD v 0 ≤ (if v < st.nextVid.toNat then st.uses.getD v 0 else 0) +
          workArgCount0 (work.map PreItem0.node)) ∧
      (∀ v < st.nextVid.toNat,
        r.2.uses.getD v 0 = st.uses.getD v 0 +
          sameScopeSpineSum0 (UInt32.ofNat v) (st.defScope.getD v 0) st.nextVid work) := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro fuel nextSc st work hN hle hinv
    cases work with
    | nil =>
      subst hN
      rw [List.map_nil] at hle ⊢
      dsimp only [workNodeCount0] at hle ⊢
      dsimp only [workBinderCount0, workArgCount0]
      simp only [Nat.add_zero, Nat.mul_zero] at *
      have hr : preRunAux0 fuel nextSc st [] = (nextSc, st) :=
        preRunAux0_nil fuel nextSc st
      rw [hr]
      refine ⟨rfl, hinv.defScope_sz, hinv.uses_sz, hinv.escaped_sz, Nat.le_refl _,
        Nat.le_refl _, (fun _ _ => rfl), hinv.defScope_lt, (fun _ _ h => h),
        hinv.escaped_bit, (fun v hv => by simp [hv]),
        (fun v _ => by dsimp only [sameScopeSpineSum0]; exact Nat.add_zero _)⟩
    | cons cur rest =>
      have hpos : 0 < N := by
        rw [← hN, List.map_cons]; dsimp only [workNodeCount0]
        have := nodeCount0_pos cur.node; omega
      have hfne : fuel ≠ 0 := fun h => by
        have := congrArg UInt32.toNat h; simp at this; omega
      have hN1 : (fuel - 1).toNat = fuel.toNat - 1 := u32_sub1_toNat5 (by omega)
      have hcur_ok := hinv.items_ok cur List.mem_cons_self
      obtain ⟨vT, lT, hvlen, hvlt, hwf, hfit, hsbg, hnb⟩ := hcur_ok
      have hnd_vars : nodeArgsInVenv0 cur.venv.length cur.node := by
        rw [hvlen]; exact wfNode0_nodeArgsInVenv0 hwf
      have hmax_u : ∀ v < st.nextVid.toNat, st.uses.getD v 0 + argCount0 cur.node < 2 ^ 32 := by
        intro v hv
        have hb := hinv.uses_bound v hv
        rw [List.map_cons] at hb; dsimp only [workArgCount0] at hb
        omega
      have hds_lt : ∀ v < st.nextVid.toNat, st.defScope.getD v 0 < 2 ^ 32 := fun v hv =>
        Nat.lt_trans (hinv.defScope_lt v hv) (UInt32.toNat_lt nextSc)
      have hst1 := preNoteNode0_spec cur.scope cur.venv cur.node st hinv.defScope_sz
        hinv.uses_sz hinv.escaped_sz hvlt hnd_vars hmax_u hds_lt hinv.escaped_bit
      dsimp only at hst1
      let st1 := preNoteNode0 cur.scope cur.venv cur.node st
      let out := preStepPush0 cur st1 nextSc rest
      have hcnt : workNodeCount0 (out.work.map PreItem0.node) + 1 = N := by
        rw [← hN]
        simpa only [out, List.map_cons] using preWorkNodeCount0_children cur st1 nextSc rest
      have hlt_N : workNodeCount0 (out.work.map PreItem0.node) < N := by omega
      have hrest_scopes : ∀ p ∈ rest, p.scope ≠ cur.scope := by
        have hnd := hinv.scopes_nodup
        simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
        intro p hp he; exact hnd.1 p hp he
      have hrest_nodup : (rest.map PreItem0.scope).Nodup := by
        have hnd := hinv.scopes_nodup
        simp only [List.map_cons, List.nodup_cons] at hnd
        exact hnd.2
      have hrest_lt : ∀ p ∈ rest, p.scope.toNat < nextSc.toNat := fun p hp =>
        hinv.scopes_lt p (List.mem_cons_of_mem _ hp)
      have hsc_cur_lt : cur.scope.toNat < nextSc.toNat := hinv.scopes_lt cur List.mem_cons_self
      have hsame_sc : ∀ v < st.nextVid.toNat,
          st.defScope.getD v 0 = cur.scope.toNat →
          ∀ p ∈ rest, p.scope.toNat ≠ st.defScope.getD v 0 := fun v _ he p hp => by
        rw [he]; exact fun h => hrest_scopes p hp
          (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))
      have finish_step :
          PreWorkInv0 ctx out.nextScope out.st out.work →
          (∀ v < st.nextVid.toNat, out.st.defScope.getD v 0 = st.defScope.getD v 0) →
          (∀ v < st.nextVid.toNat, st1.escaped.getD v 0 = 1 →
            out.st.escaped.getD v 0 = 1) →
          (∀ v < out.st.nextVid.toNat,
            out.st.uses.getD v 0 = if v < st.nextVid.toNat then st1.uses.getD v 0 else 0) →
          workBinderCount0 (out.work.map PreItem0.node) +
            (out.st.nextVid.toNat - st.nextVid.toNat) =
            workBinderCount0 ((cur :: rest).map PreItem0.node) →
          st.nextVid.toNat ≤ out.st.nextVid.toNat →
          nextSc.toNat ≤ out.nextScope.toNat → out.nextScope.toNat ≤ nextSc.toNat + 2 →
          (∀ v < st.nextVid.toNat,
            nodeArgsUses0 (UInt32.ofNat v) cur.venv cur.node +
              workArgCount0 (out.work.map PreItem0.node) ≤
              workArgCount0 ((cur :: rest).map PreItem0.node)) →
          (∀ v < st.nextVid.toNat,
            st1.uses.getD v 0 +
              sameScopeSpineSum0 (UInt32.ofNat v) (st.defScope.getD v 0)
                out.st.nextVid out.work =
            st.uses.getD v 0 +
              sameScopeSpineSum0 (UInt32.ofNat v) (st.defScope.getD v 0)
                st.nextVid (cur :: rest)) →
          workArgCount0 (out.work.map PreItem0.node) ≤
            workArgCount0 ((cur :: rest).map PreItem0.node) →
          let r := preRunAux0 fuel nextSc st (cur :: rest)
          r.2.nextVid.toNat =
            st.nextVid.toNat + workBinderCount0 ((cur :: rest).map PreItem0.node) ∧
          r.2.defScope.size = r.2.nextVid.toNat ∧
          r.2.uses.size = r.2.nextVid.toNat ∧
          r.2.escaped.size = r.2.nextVid.toNat ∧
          nextSc.toNat ≤ r.1.toNat ∧ r.1.toNat ≤ nextSc.toNat + 2 * N ∧
          (∀ v < st.nextVid.toNat, r.2.defScope.getD v 0 = st.defScope.getD v 0) ∧
          (∀ v < r.2.nextVid.toNat, r.2.defScope.getD v 0 < r.1.toNat) ∧
          (∀ v < st.nextVid.toNat, st.escaped.getD v 0 = 1 → r.2.escaped.getD v 0 = 1) ∧
          (∀ v < r.2.nextVid.toNat, r.2.escaped.getD v 0 = 0 ∨ r.2.escaped.getD v 0 = 1) ∧
          (∀ v < r.2.nextVid.toNat,
            r.2.uses.getD v 0 ≤ (if v < st.nextVid.toNat then st.uses.getD v 0 else 0) +
              workArgCount0 ((cur :: rest).map PreItem0.node)) ∧
          (∀ v < st.nextVid.toNat,
            r.2.uses.getD v 0 = st.uses.getD v 0 +
              sameScopeSpineSum0 (UInt32.ofNat v) (st.defScope.getD v 0) st.nextVid
                (cur :: rest)) := by
        intro hinv' hds_eq hesc_mono hus_eq hbc hnv_le hsc_le hsc_ub hsum_u hsame_sum hac_le
        have hdef_out : preRunAux0 fuel nextSc st (cur :: rest) =
            preRunAux0 (fuel - 1) out.nextScope out.st out.work :=
          preRunAux0_succ hfne nextSc st cur rest
        dsimp only
        rw [hdef_out]
        have ih_r := ih (workNodeCount0 (out.work.map PreItem0.node)) hlt_N (fuel - 1)
          out.nextScope out.st out.work rfl (by omega) hinv'
        dsimp only at ih_r
        have hsc_ub_ih := ih_r.2.2.2.2.2.1
        refine ⟨by rw [ih_r.1]; omega, ih_r.2.1, ih_r.2.2.1, ih_r.2.2.2.1,
          Nat.le_trans hsc_le ih_r.2.2.2.2.1, by omega,
          fun v hv => (ih_r.2.2.2.2.2.2.1 v (Nat.lt_of_lt_of_le hv hnv_le)).trans (hds_eq v hv),
          ih_r.2.2.2.2.2.2.2.1,
          fun v hv he => by
            apply ih_r.2.2.2.2.2.2.2.2.1 v (Nat.lt_of_lt_of_le hv hnv_le)
            apply hesc_mono v hv
            have hv1 := hst1.2.2.2.2.2 v hv
            split at hv1
            · exact hv1.2.trans he
            · rw [hv1.2, he]; split <;> rfl,
          ih_r.2.2.2.2.2.2.2.2.2.1,
          fun v hv => ?_,
          fun v hv => ?_⟩
        · have hru := ih_r.2.2.2.2.2.2.2.2.2.2.1 v hv
          by_cases hv_out : v < out.st.nextVid.toNat
          · simp only [hv_out, ↓reduceIte] at hru
            rw [hus_eq v hv_out] at hru
            by_cases hv0 : v < st.nextVid.toNat
            · simp only [hv0, ↓reduceIte] at hru ⊢
              have hv1 := hst1.2.2.2.2.2 v hv0
              split at hv1
              · have hu := hsum_u v hv0
                rw [hv1.1] at hru
                omega
              · rw [hv1.1] at hru
                omega
            · simp only [hv0, ↓reduceIte, Nat.zero_add] at hru ⊢
              omega
          · simp only [hv_out, ↓reduceIte, Nat.zero_add] at hru
            have hv0 : ¬ v < st.nextVid.toNat := fun h => hv_out (Nat.lt_of_lt_of_le h hnv_le)
            simp only [hv0, ↓reduceIte, Nat.zero_add]
            omega
        · rw [ih_r.2.2.2.2.2.2.2.2.2.2.2 v (Nat.lt_of_lt_of_le hv hnv_le), hus_eq v
            (Nat.lt_of_lt_of_le hv hnv_le), hds_eq v hv]
          simpa only [hv, ↓reduceIte] using hsame_sum v hv
      have hterm : isTerm0 cur.node = true →
          let r := preRunAux0 fuel nextSc st (cur :: rest)
          r.2.nextVid.toNat =
            st.nextVid.toNat + workBinderCount0 ((cur :: rest).map PreItem0.node) ∧
          r.2.defScope.size = r.2.nextVid.toNat ∧
          r.2.uses.size = r.2.nextVid.toNat ∧
          r.2.escaped.size = r.2.nextVid.toNat ∧
          nextSc.toNat ≤ r.1.toNat ∧ r.1.toNat ≤ nextSc.toNat + 2 * N ∧
          (∀ v < st.nextVid.toNat, r.2.defScope.getD v 0 = st.defScope.getD v 0) ∧
          (∀ v < r.2.nextVid.toNat, r.2.defScope.getD v 0 < r.1.toNat) ∧
          (∀ v < st.nextVid.toNat, st.escaped.getD v 0 = 1 → r.2.escaped.getD v 0 = 1) ∧
          (∀ v < r.2.nextVid.toNat, r.2.escaped.getD v 0 = 0 ∨ r.2.escaped.getD v 0 = 1) ∧
          (∀ v < r.2.nextVid.toNat,
            r.2.uses.getD v 0 ≤ (if v < st.nextVid.toNat then st.uses.getD v 0 else 0) +
              workArgCount0 ((cur :: rest).map PreItem0.node)) ∧
          (∀ v < st.nextVid.toNat,
            r.2.uses.getD v 0 = st.uses.getD v 0 +
              sameScopeSpineSum0 (UInt32.ofNat v) (st.defScope.getD v 0) st.nextVid
                (cur :: rest)) := by
        intro ht
        have hout : out = PreOut0.mk st1 nextSc rest := by
          dsimp only [out, preStepPush0]; simp [ht]
        have hbc0 : binderCount0 cur.node = 0 := by
          cases hnd : cur.node <;> rw [hnd] at ht <;> simp only [isTerm0] at ht <;>
            first | (dsimp only [binderCount0]; done) | exact absurd ht Bool.false_ne_true
        have hsp_eq : ∀ vid, spineUses0 vid cur.venv st.nextVid cur.node =
            nodeArgsUses0 vid cur.venv cur.node := fun vid => by
          cases hnd : cur.node <;> rw [hnd] at ht <;> simp only [isTerm0] at ht <;>
            first | (dsimp only [spineUses0]; done) | exact absurd ht Bool.false_ne_true
        have hac0 : workArgCount0 (rest.map PreItem0.node) ≤
            workArgCount0 ((cur :: rest).map PreItem0.node) := by
          rw [List.map_cons]; dsimp only [workArgCount0]; omega
        have huses_b : ∀ v < st1.nextVid.toNat,
            st1.uses.getD v 0 + workArgCount0 (rest.map PreItem0.node) < 2 ^ 31 := by
          intro v hv; rw [hst1.1] at hv
          have hv1 := hst1.2.2.2.2.2 v hv
          have hau := nodeArgsUses0_le_argCount0 (UInt32.ofNat v) cur.venv cur.node
          have hb := hinv.uses_bound v hv
          rw [List.map_cons] at hb; dsimp only [workArgCount0] at hb
          split at hv1 <;> { rw [hv1.1]; omega }
        have hinv' : PreWorkInv0 ctx out.nextScope out.st out.work := by
          rw [hout]; dsimp only
          refine ⟨(by rw [hst1.1, hst1.2.1]; exact hinv.defScope_sz),
            (by rw [hst1.1]; exact hst1.2.2.1), (by rw [hst1.1]; exact hst1.2.2.2.1),
            fun v hv => by rw [hst1.1] at hv; rw [hst1.2.1]; exact hinv.defScope_lt v hv,
            fun v hv => hst1.2.2.2.2.1 v (by rw [← hst1.1]; exact hv),
            hrest_nodup, hrest_lt,
            fun p hp => by rw [hst1.1]; exact hinv.items_ok p (List.mem_cons_of_mem _ hp),
            by
              rw [hst1.1]
              have := hinv.nextVid_bound
              rw [List.map_cons] at this; dsimp only [workBinderCount0] at this
              rw [hbc0] at this; omega,
            by
              have := hinv.nextSc_bound
              have hp := nodeCount0_pos cur.node
              rw [List.map_cons] at this; dsimp only [workNodeCount0] at this; omega,
            by
              have := hinv.argCount_bound
              rw [List.map_cons] at this; dsimp only [workArgCount0] at this; omega,
            huses_b⟩
        refine finish_step hinv'
          (fun v _ => by rw [hout, hst1.2.1])
          (fun v _ h => by rw [hout]; exact h)
          (fun v hv => by rw [hout]; rw [hout, hst1.1] at hv; simp [hv])
          (by rw [hout, hst1.1, List.map_cons]
              dsimp only [workBinderCount0]; rw [hbc0]; omega)
          (by rw [hout, hst1.1]; exact Nat.le_refl _)
          (by rw [hout]; dsimp only; exact Nat.le_refl _)
          (by rw [hout]; dsimp only; omega)
          (fun v _ => by
            rw [hout, List.map_cons]; dsimp only [workArgCount0]
            have := nodeArgsUses0_le_argCount0 (UInt32.ofNat v) cur.venv cur.node; omega)
          (fun v hv => by
            rw [hout, hst1.1]
            dsimp only [sameScopeSpineSum0]
            have hv1 := hst1.2.2.2.2.2 v hv
            split at hv1
            · rename_i heq
              simp only [heq, ↓reduceIte, hsp_eq]
              rw [hv1.1, Nat.add_assoc]
            · rename_i hne
              simp only [hne, ↓reduceIte, Nat.zero_add]
              rw [hv1.1])
          (by rw [hout]; exact hac0)
      cases hnd_eq : cur.node with
      | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt =>
        exact hterm (by simp [isTerm0, hnd_eq])
      | jnz c t e =>
        have hout : out = PreOut0.mk st1 (nextSc + 2)
            (PreItem0.mk e cur.venv (nextSc + 1) ::
              PreItem0.mk t cur.venv nextSc :: rest) := by
          dsimp only [out, preStepPush0]; simp [isTerm0, preStepJnz0, hnd_eq]
        have hsc_ub_big : nextSc.toNat + 2 * (1 + nodeCount0 t + nodeCount0 e +
            workNodeCount0 (rest.map PreItem0.node)) < 2 ^ 31 := by
          have := hinv.nextSc_bound
          rw [List.map_cons, hnd_eq] at this
          dsimp only [workNodeCount0, nodeCount0] at this; exact this
        have hsc1 : (nextSc + 1).toNat = nextSc.toNat + 1 :=
          u32_add1_toNat5 (by have := hsc_ub_big; omega)
        have hsc2 : (nextSc + 2).toNat = nextSc.toNat + 2 := by
          rw [UInt32.toNat_add, show (2 : UInt32).toNat = 2 by decide,
            Nat.mod_eq_of_lt (by omega)]
        rw [hnd_eq] at hwf hfit hsbg hnb
        cases hwf with | jnz _ hwft hwfe =>
        dsimp only [TFlat0.sigLensFitU32] at hfit; rw [Bool.and_eq_true] at hfit
        dsimp only [TFlat0.singleBlockGroups] at hsbg; rw [Bool.and_eq_true] at hsbg
        dsimp only [TFlat0.noNegBool] at hnb; rw [Bool.and_eq_true] at hnb
        have hnd_scopes : ([nextSc + 1, nextSc] ++ rest.map PreItem0.scope).Nodup := by
          refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, hrest_nodup⟩⟩
          · intro hm
            rcases List.mem_cons.mp hm with h | h
            · have := congrArg UInt32.toNat h; omega
            · obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h
              have := hrest_lt p hp; have := congrArg UInt32.toNat hpe; omega
          · intro hm
            obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
            have := hrest_lt p hp; have := congrArg UInt32.toNat hpe; omega
        have huses_b : ∀ v < st1.nextVid.toNat,
            st1.uses.getD v 0 +
              (argCount0 e + (argCount0 t + workArgCount0 (rest.map PreItem0.node))) < 2 ^ 31 := by
          intro v hv; rw [hst1.1] at hv
          have hv1 := hst1.2.2.2.2.2 v hv
          have hau : argUses0 (UInt32.ofNat v) cur.venv c ≤ 1 := by
            cases c with
            | var _ => dsimp only [argUses0]; split <;> omega
            | immBool _ | immBits _ _ => simp [argUses0]
          have hb := hinv.uses_bound v hv
          rw [List.map_cons, hnd_eq] at hb; dsimp only [workArgCount0, argCount0] at hb
          split at hv1
          · rw [hv1.1]; dsimp only [nodeArgsUses0]; rw [hnd_eq]; dsimp only [nodeArgsUses0]; omega
          · rw [hv1.1]; omega
        have hinv' : PreWorkInv0 ctx out.nextScope out.st out.work := by
          rw [hout]; dsimp only
          refine ⟨(by rw [hst1.1, hst1.2.1]; exact hinv.defScope_sz),
            (by rw [hst1.1]; exact hst1.2.2.1), (by rw [hst1.1]; exact hst1.2.2.2.1),
            fun v hv => by
              have hdl := hinv.defScope_lt v (by rw [← hst1.1]; exact hv)
              rw [hst1.2.1]; omega,
            fun v hv => hst1.2.2.2.2.1 v (by rw [← hst1.1]; exact hv),
            by simpa only [List.map_cons, List.cons_append, List.nil_append] using hnd_scopes,
            fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp1
              · dsimp only; omega
              · rcases List.mem_cons.mp hp1 with rfl | hp2
                · dsimp only; omega
                · have := hrest_lt p hp2; omega,
            fun p hp => by
              rw [hst1.1]
              rcases List.mem_cons.mp hp with rfl | hp1
              · exact ⟨vT, lT, hvlen, hvlt, hwfe, hfit.2, hsbg.2, hnb.2⟩
              · rcases List.mem_cons.mp hp1 with rfl | hp2
                · exact ⟨vT, lT, hvlen, hvlt, hwft, hfit.1, hsbg.1, hnb.1⟩
                · exact hinv.items_ok p (List.mem_cons_of_mem _ hp2),
            by
              rw [hst1.1]
              have := hinv.nextVid_bound
              rw [List.map_cons, hnd_eq] at this; simp only [List.map_cons]
              dsimp only [workBinderCount0, binderCount0] at this ⊢; omega,
            by
              have := hsc_ub_big
              simp only [List.map_cons]; dsimp only [workNodeCount0]; omega,
            by
              have := hinv.argCount_bound
              rw [List.map_cons, hnd_eq] at this; simp only [List.map_cons]
              dsimp only [workArgCount0, argCount0] at this ⊢; omega,
            by rw [List.map_cons]; dsimp only [workArgCount0]; exact huses_b⟩
        refine finish_step hinv'
          (fun v _ => by rw [hout, hst1.2.1])
          (fun v _ h => by rw [hout]; exact h)
          (fun v hv => by rw [hout]; rw [hout, hst1.1] at hv; simp [hv])
          (by rw [hout, hst1.1]; simp only [List.map_cons]; rw [hnd_eq]
              dsimp only [workBinderCount0, binderCount0]; omega)
          (by rw [hout, hst1.1]; exact Nat.le_refl _)
          (by rw [hout]; dsimp only; omega)
          (by rw [hout]; dsimp only; omega)
          (fun v _ => by
            rw [hout]
            have hau : argUses0 (UInt32.ofNat v) cur.venv c ≤ 1 := by
              cases c with
              | var _ => dsimp only [argUses0]; split <;> omega
              | immBool _ | immBits _ _ => simp [argUses0]
            simp only [List.map_cons]; rw [hnd_eq]
            dsimp only [workArgCount0, nodeArgsUses0, argCount0]; omega)
          (fun v hv => by
            rw [hout, hst1.1]
            have hdl := hinv.defScope_lt v hv
            have hne1 : st.defScope.getD v 0 ≠ (nextSc + 1).toNat := by omega
            have hne0 : st.defScope.getD v 0 ≠ nextSc.toNat := by omega
            dsimp only [sameScopeSpineSum0]
            simp only [hne1, hne0, ↓reduceIte, Nat.zero_add]
            have hv1 := hst1.2.2.2.2.2 v hv
            split at hv1
            · rename_i heq
              rw [hv1.1]
              simp only [heq, ↓reduceIte]; rw [hnd_eq]
              dsimp only [spineUses0, nodeArgsUses0]; rw [Nat.add_assoc]
            · rename_i hne
              simp only [hne, ↓reduceIte, Nat.zero_add]
              rw [hv1.1])
          (by
            rw [hout]; simp only [List.map_cons]; rw [hnd_eq]
            dsimp only [workArgCount0, argCount0]; omega)
      | group bodies k =>
        rw [hnd_eq] at hwf hfit hsbg hnb
        obtain ⟨hwfk, hfitk, hsbgk, hnbk, hcases⟩ := wfNode0_group_single_inv hwf hfit hsbg hnb
        have hau_z : ∀ vid, nodeArgsUses0 vid cur.venv cur.node = 0 := fun vid => by
          rw [hnd_eq]; rfl
        have hsp_z : ∀ vid nv, spineUses0 vid cur.venv nv cur.node = 0 := fun vid nv => by
          rw [hnd_eq]; rfl
        have hst1_eq : st1 = st := by
          dsimp only [st1]; rw [hnd_eq]; rfl
        rcases hcases with rfl | ⟨pts, b, rfl, hpts_lt, hwfb, hfitb, hsbgb, hnbb⟩
        · have hout : out = PreOut0.mk st1 (nextSc + 1)
              (PreItem0.mk k cur.venv nextSc :: rest) := by
            dsimp only [out, preStepPush0, isTerm0, preStepGroup0, prePushGroup0,
              preEnqueueGroup0]
            rw [hnd_eq]
            rfl
          have hsc_ub_big : nextSc.toNat + 2 * (1 + 0 + nodeCount0 k +
              workNodeCount0 (rest.map PreItem0.node)) < 2 ^ 31 := by
            have := hinv.nextSc_bound
            rw [List.map_cons, hnd_eq] at this
            dsimp only [workNodeCount0, nodeCount0, blocksNodeCount0] at this; exact this
          have hsc1 : (nextSc + 1).toNat = nextSc.toNat + 1 := u32_add1_toNat5 (by omega)
          have hnd_sc : (nextSc :: rest.map PreItem0.scope).Nodup := by
            refine List.nodup_cons.mpr ⟨fun hm => ?_, hrest_nodup⟩
            obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
            have := hrest_lt p hp; have := congrArg UInt32.toNat hpe; omega
          have huses_b : ∀ v < st1.nextVid.toNat,
              st1.uses.getD v 0 +
                (argCount0 k + workArgCount0 (rest.map PreItem0.node)) < 2 ^ 31 := by
            intro v hv; rw [hst1_eq] at hv ⊢
            have hb := hinv.uses_bound v hv
            rw [List.map_cons, hnd_eq] at hb
            dsimp only [workArgCount0, argCount0, blocksArgCount0] at hb
            omega
          have hinv' : PreWorkInv0 ctx out.nextScope out.st out.work := by
            rw [hout]; dsimp only
            refine ⟨(by rw [hst1_eq]; exact hinv.defScope_sz),
              (by rw [hst1_eq]; exact hinv.uses_sz), (by rw [hst1_eq]; exact hinv.escaped_sz),
              fun v hv => by rw [hst1_eq] at hv ⊢; have := hinv.defScope_lt v hv; omega,
              fun v hv => by rw [hst1_eq] at hv ⊢; exact hinv.escaped_bit v hv,
              by simpa only [List.map_cons] using hnd_sc,
              fun p hp => by
                rcases List.mem_cons.mp hp with rfl | hp1
                · dsimp only; omega
                · have := hrest_lt p hp1; omega,
              fun p hp => by
                rw [hst1_eq]
                rcases List.mem_cons.mp hp with rfl | hp1
                · exact ⟨vT, legalAddSigs0 [] lT, hvlen, hvlt, hwfk, hfitk, hsbgk, hnbk⟩
                · exact hinv.items_ok p (List.mem_cons_of_mem _ hp1),
              by
                rw [hst1_eq]
                have := hinv.nextVid_bound
                rw [List.map_cons, hnd_eq] at this; simp only [List.map_cons]
                dsimp only [workBinderCount0, binderCount0, blocksBinderCount0] at this ⊢
                omega,
              by have := hsc_ub_big; simp only [List.map_cons]
                 dsimp only [workNodeCount0]; omega,
              by
                have := hinv.argCount_bound
                rw [List.map_cons, hnd_eq] at this; simp only [List.map_cons]
                dsimp only [workArgCount0, argCount0, blocksArgCount0] at this ⊢
                omega,
              by rw [List.map_cons]; dsimp only [workArgCount0]; exact huses_b⟩
          refine finish_step hinv'
            (fun v _ => by rw [hout, hst1_eq])
            (fun v _ h => by rw [hout]; exact h)
            (fun v hv => by rw [hout]; rw [hout, hst1_eq] at hv; simp [hv])
            (by
              rw [hout, hst1_eq]; simp only [List.map_cons]; rw [hnd_eq]
              dsimp only [workBinderCount0, binderCount0, blocksBinderCount0]; omega)
            (by rw [hout, hst1_eq]; exact Nat.le_refl _)
            (by rw [hout]; dsimp only; omega)
            (by rw [hout]; dsimp only; omega)
            (fun v _ => by
              rw [hout, hau_z]; simp only [List.map_cons]; rw [hnd_eq]
              dsimp only [workArgCount0, argCount0, blocksArgCount0]; omega)
            (fun v hv => by
              rw [hout, hst1_eq]
              have hdl := hinv.defScope_lt v hv
              have hne : st.defScope.getD v 0 ≠ nextSc.toNat := by omega
              dsimp only [sameScopeSpineSum0]
              simp only [hne, ↓reduceIte, Nat.zero_add, hsp_z]
              split <;> simp)
            (by
              rw [hout]; simp only [List.map_cons]; rw [hnd_eq]
              dsimp only [workArgCount0, argCount0, blocksArgCount0]; omega)
        · have hout : out =
              PreOut0.mk (preBindLoop0 (tyLenU0 pts 0) nextSc cur.venv st1).2 (nextSc + 2)
                (PreItem0.mk k cur.venv (nextSc + 1) ::
                  PreItem0.mk b (preBindLoop0 (tyLenU0 pts 0) nextSc cur.venv st1).1
                    nextSc :: rest) := by
            dsimp only [out, preStepPush0]; rw [hnd_eq]
            simp only [isTerm0, Bool.false_eq_true, ↓reduceIte]
            dsimp only [preStepGroup0, preEnqueueGroup0, prePushGroup0, prePushOne0]
            rw [UInt32.add_assoc, show (1 : UInt32) + 1 = 2 by decide]
          have hsc_ub_big : nextSc.toNat + 2 * (1 + (nodeCount0 b + 0) + nodeCount0 k +
              workNodeCount0 (rest.map PreItem0.node)) < 2 ^ 31 := by
            have := hinv.nextSc_bound
            rw [List.map_cons, hnd_eq] at this
            dsimp only [workNodeCount0, nodeCount0, blocksNodeCount0] at this; exact this
          have hsc1 : (nextSc + 1).toNat = nextSc.toNat + 1 := u32_add1_toNat5 (by omega)
          have hsc2 : (nextSc + 2).toNat = nextSc.toNat + 2 := by
            rw [UInt32.toNat_add, show (2 : UInt32).toNat = 2 by decide,
              Nat.mod_eq_of_lt (by omega)]
          have hlen_pts : (tyLenU0 pts 0).toNat = pts.length := tyLenU0_eq_of_lt hpts_lt
          have hnv_b : st1.nextVid.toNat + pts.length < 2 ^ 32 := by
            rw [hst1_eq]
            have := hinv.nextVid_bound
            rw [List.map_cons, hnd_eq] at this
            dsimp only [workBinderCount0, binderCount0, blocksBinderCount0] at this
            omega
          have hbind := preBindLoop0_spec pts.length (tyLenU0 pts 0) nextSc cur.venv st1
            hlen_pts hnv_b (hst1_eq ▸ hinv.defScope_sz) (hst1_eq ▸ hinv.uses_sz)
            (hst1_eq ▸ hinv.escaped_sz)
          dsimp only at hbind
          rw [hst1_eq] at hbind
          have hnd_sc : ([nextSc + 1, nextSc] ++ rest.map PreItem0.scope).Nodup := by
            refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, hrest_nodup⟩⟩
            · intro hm
              rcases List.mem_cons.mp hm with h | h
              · have := congrArg UInt32.toNat h; omega
              · obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h
                have := hrest_lt p hp; have := congrArg UInt32.toNat hpe; omega
            · intro hm
              obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
              have := hrest_lt p hp; have := congrArg UInt32.toNat hpe; omega
          have hvlen_b : (pushFreshVids0 pts.length st.nextVid cur.venv).length =
              (pushTys0 pts vT).length := by
            rw [pushFreshVids0_length, hvlen, pushTys0_eq_pushTypes, pushTypes_length]
          have hvlt_b : ∀ v ∈ pushFreshVids0 pts.length st.nextVid cur.venv,
              v.toNat < st.nextVid.toNat + pts.length := by
            intro v hm
            rw [hst1_eq] at hnv_b
            rcases (mem_pushFreshVids0 pts.length st.nextVid cur.venv v).mp hm
              with h0 | ⟨j, hj, rfl⟩
            · exact Nat.lt_of_lt_of_le (hvlt v h0) (Nat.le_add_right _ _)
            · rw [UInt32.toNat_add, u32_toNat_ofNat5,
                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
              omega
          have huses_b : ∀ v <
              (preBindLoop0 (tyLenU0 pts 0) nextSc cur.venv st).2.nextVid.toNat,
              (preBindLoop0 (tyLenU0 pts 0) nextSc cur.venv st).2.uses.getD v 0 +
                (argCount0 k +
                  (argCount0 b + workArgCount0 (rest.map PreItem0.node))) < 2 ^ 31 := by
            intro v hv
            rw [hbind.2.1] at hv
            rw [hbind.2.2.2.2.2.2.1 v]
            by_cases hv0 : v < st.nextVid.toNat
            · simp only [hv0, ↓reduceIte]
              have hb := hinv.uses_bound v hv0
              rw [List.map_cons, hnd_eq] at hb
              dsimp only [workArgCount0, argCount0, blocksArgCount0] at hb
              omega
            · simp only [hv0, ↓reduceIte, Nat.zero_add]
              have hb := hinv.argCount_bound
              rw [List.map_cons, hnd_eq] at hb
              dsimp only [workArgCount0, argCount0, blocksArgCount0] at hb
              omega
          have hinv' : PreWorkInv0 ctx out.nextScope out.st out.work := by
            rw [hout, hst1_eq]; dsimp only
            refine ⟨hbind.2.2.1.trans hbind.2.1.symm, hbind.2.2.2.1.trans hbind.2.1.symm,
              hbind.2.2.2.2.1.trans hbind.2.1.symm,
              fun v hv => by
                rw [hbind.2.1] at hv
                rw [hbind.2.2.2.2.2.1 v]
                split
                · rename_i hv0; have := hinv.defScope_lt v hv0; omega
                · omega,
              fun v hv => by
                rw [hbind.2.1] at hv
                rw [hbind.2.2.2.2.2.2.2 v]
                split
                · rename_i hv0; exact hinv.escaped_bit v hv0
                · exact Or.inl rfl,
              by simpa only [List.map_cons, List.cons_append, List.nil_append] using hnd_sc,
              fun p hp => by
                rcases List.mem_cons.mp hp with rfl | hp1
                · dsimp only; omega
                · rcases List.mem_cons.mp hp1 with rfl | hp2
                  · dsimp only; omega
                  · have := hrest_lt p hp2; omega,
              fun p hp => by
                rw [hbind.2.1]
                rcases List.mem_cons.mp hp with rfl | hp1
                · exact ⟨vT, legalAddSigs0 [(pts, b)] lT, hvlen,
                    fun v hm => Nat.lt_of_lt_of_le (hvlt v hm) (Nat.le_add_right _ _),
                    hwfk, hfitk, hsbgk, hnbk⟩
                · rcases List.mem_cons.mp hp1 with rfl | hp2
                  · rw [hbind.1]
                    exact ⟨pushTys0 pts vT, legalAddSigs0 [(pts, b)] lT, hvlen_b, hvlt_b,
                      hwfb, hfitb, hsbgb, hnbb⟩
                  · obtain ⟨vT', lT', hvl', hvlt', hwf', hfit', hsbg', hnb'⟩ :=
                      hinv.items_ok p (List.mem_cons_of_mem _ hp2)
                    exact ⟨vT', lT', hvl',
                      fun v hm => Nat.lt_of_lt_of_le (hvlt' v hm) (Nat.le_add_right _ _),
                      hwf', hfit', hsbg', hnb'⟩,
              by
                rw [hbind.2.1]
                have := hinv.nextVid_bound
                rw [List.map_cons, hnd_eq] at this; simp only [List.map_cons]
                dsimp only [workBinderCount0, binderCount0, blocksBinderCount0] at this ⊢
                omega,
              by have := hsc_ub_big; simp only [List.map_cons]
                 dsimp only [workNodeCount0]; omega,
              by
                have := hinv.argCount_bound
                rw [List.map_cons, hnd_eq] at this; simp only [List.map_cons]
                dsimp only [workArgCount0, argCount0, blocksArgCount0] at this ⊢
                omega,
              by rw [List.map_cons]; dsimp only [workArgCount0]; exact huses_b⟩
          refine finish_step hinv'
            (fun v hv => by rw [hout, hst1_eq, hbind.2.2.2.2.2.1 v]; simp [hv])
            (fun v hv h => by
              rw [hout, hst1_eq, hbind.2.2.2.2.2.2.2 v]
              simp only [hv, ↓reduceIte]
              rw [hst1_eq] at h
              exact h)
            (fun v hv => by
              rw [hout, hst1_eq]
              rw [hbind.2.2.2.2.2.2.1 v])
            (by
              rw [hout, hst1_eq, hbind.2.1]; simp only [List.map_cons]; rw [hnd_eq]
              dsimp only [workBinderCount0, binderCount0, blocksBinderCount0]
              omega)
            (by rw [hout, hst1_eq, hbind.2.1]; exact Nat.le_add_right _ _)
            (by rw [hout]; dsimp only; omega)
            (by rw [hout]; dsimp only; omega)
            (fun v _ => by
              rw [hout, hau_z]; simp only [List.map_cons]; rw [hnd_eq]
              dsimp only [workArgCount0, argCount0, blocksArgCount0]; omega)
            (fun v hv => by
              rw [hout, hst1_eq]
              have hdl := hinv.defScope_lt v hv
              have hne0 : st.defScope.getD v 0 ≠ nextSc.toNat := by omega
              have hne1 : st.defScope.getD v 0 ≠ (nextSc + 1).toNat := by omega
              dsimp only [sameScopeSpineSum0]
              simp only [hne0, hne1, ↓reduceIte, Nat.zero_add, hsp_z]
              have hnv_le' : st.nextVid.toNat ≤
                  (preBindLoop0 (tyLenU0 pts 0) nextSc cur.venv st).2.nextVid.toNat := by
                rw [hbind.2.1]; exact Nat.le_add_right _ _
              have hlt32 : (UInt32.ofNat v).toNat < st.nextVid.toNat := by
                rw [u32_toNat_ofNat5, Nat.mod_eq_of_lt (Nat.lt_trans hv (UInt32.toNat_lt _))]
                exact hv
              have hrest_eq := sameScopeSpineSum0_congr_nv (vid := UInt32.ofNat v)
                (ds := st.defScope.getD v 0) (work := rest) hlt32 hnv_le'
                (by
                  rw [hbind.2.1]
                  have := hinv.nextVid_bound
                  rw [List.map_cons, hnd_eq] at this
                  dsimp only [workBinderCount0, binderCount0, blocksBinderCount0] at this
                  omega)
              rw [hrest_eq]
              split <;> simp)
            (by
              rw [hout]; simp only [List.map_cons]; rw [hnd_eq]
              dsimp only [workArgCount0, argCount0, blocksArgCount0]; omega)
      | let1 op args k | let2Umulw64 a b k | load t addr k | store t val addr k
      | call fnSym as bs args k =>
        have hlin : isTerm0 cur.node = false := by simp [isTerm0, hnd_eq]
        have hnj : ∀ c t e, cur.node ≠ .jnz c t e := fun c t e h => by rw [hnd_eq] at h; cases h
        have hng : ∀ bs' k', cur.node ≠ .group bs' k' := fun bs' k' h => by
          rw [hnd_eq] at h; cases h
        obtain ⟨hcnt_lt, hvlen_l, hwfl, hfitl, hsbgl, hnbl, hbc_l, hac_l, hnc_l, _⟩ :=
          wfNode0_lin_inv hwf hfit hsbg hnb hlin hnj hng
        have hout : out =
            PreOut0.mk (preBindLoop0 (linCnt0 cur.node) cur.scope cur.venv st1).2 nextSc
              (PreItem0.mk (linK0 cur.node)
                (preBindLoop0 (linCnt0 cur.node) cur.scope cur.venv st1).1 cur.scope ::
                rest) := by
          dsimp only [out, preStepPush0]
          simp only [hlin, Bool.false_eq_true, ↓reduceIte]
          rfl
        have hnv_b : st1.nextVid.toNat + (linCnt0 cur.node).toNat < 2 ^ 32 := by
          rw [hst1.1]
          have := hinv.nextVid_bound
          rw [List.map_cons] at this; dsimp only [workBinderCount0] at this
          omega
        have hbind := preBindLoop0_spec (linCnt0 cur.node).toNat (linCnt0 cur.node) cur.scope
          cur.venv st1 rfl hnv_b (hst1.1 ▸ hst1.2.1.symm ▸ hinv.defScope_sz)
          (hst1.1 ▸ hst1.2.2.1) (hst1.1 ▸ hst1.2.2.2.1)
        dsimp only at hbind
        have hnd_sc : (cur.scope :: rest.map PreItem0.scope).Nodup :=
          List.nodup_cons.mpr ⟨fun hm => by
            obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
            exact hrest_scopes p hp hpe, hrest_nodup⟩
        have hvlt_l : ∀ v ∈ pushFreshVids0 (linCnt0 cur.node).toNat st1.nextVid cur.venv,
            v.toNat < st1.nextVid.toNat + (linCnt0 cur.node).toNat := by
          intro v hm
          rcases (mem_pushFreshVids0 (linCnt0 cur.node).toNat st1.nextVid cur.venv v).mp hm
            with h0 | ⟨j, hj, rfl⟩
          · rw [hst1.1]
            exact Nat.lt_of_lt_of_le (hvlt v h0) (Nat.le_add_right _ _)
          · rw [UInt32.toNat_add, u32_toNat_ofNat5,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            omega
        have huses_b : ∀ v <
            (preBindLoop0 (linCnt0 cur.node) cur.scope cur.venv st1).2.nextVid.toNat,
            (preBindLoop0 (linCnt0 cur.node) cur.scope cur.venv st1).2.uses.getD v 0 +
              (argCount0 (linK0 cur.node) + workArgCount0 (rest.map PreItem0.node)) < 2 ^ 31 := by
          intro v hv
          rw [hbind.2.1, hst1.1] at hv
          rw [hbind.2.2.2.2.2.2.1 v]
          by_cases hv0 : v < st.nextVid.toNat
          · rw [hst1.1]
            simp only [hv0, ↓reduceIte]
            have hv1 := hst1.2.2.2.2.2 v hv0
            have hb := hinv.uses_bound v hv0
            rw [List.map_cons] at hb; dsimp only [workArgCount0] at hb
            have hnu := nodeArgsUses0_add_linK0_le (UInt32.ofNat v) cur.venv hlin hnj hng
            split at hv1
            · rw [hv1.1]; omega
            · rw [hv1.1]; omega
          · rw [hst1.1]
            simp only [hv0, ↓reduceIte, Nat.zero_add]
            have hb := hinv.argCount_bound
            rw [List.map_cons] at hb; dsimp only [workArgCount0] at hb
            omega
        have hinv' : PreWorkInv0 ctx out.nextScope out.st out.work := by
          rw [hout]
          refine ⟨hbind.2.2.1.trans hbind.2.1.symm, hbind.2.2.2.1.trans hbind.2.1.symm,
            hbind.2.2.2.2.1.trans hbind.2.1.symm,
            fun v hv => by
              rw [hbind.2.1] at hv
              rw [hbind.2.2.2.2.2.1 v]
              split
              · rename_i hv0; rw [hst1.2.1]; exact hinv.defScope_lt v (hst1.1 ▸ hv0)
              · exact hsc_cur_lt,
            fun v hv => by
              rw [hbind.2.1] at hv
              rw [hbind.2.2.2.2.2.2.2 v]
              split
              · rename_i hv0; exact hst1.2.2.2.2.1 v (hst1.1 ▸ hv0)
              · exact Or.inl rfl,
            by simpa only [List.map_cons] using hnd_sc,
            fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp1
              · exact hsc_cur_lt
              · exact hrest_lt p hp1,
            fun p hp => by
              rw [hbind.2.1]
              rcases List.mem_cons.mp hp with rfl | hp1
              · rw [hbind.1]
                exact ⟨legalNextVenv0 cur.node vT, lT,
                  (pushFreshVids0_length _ _ _).trans (hvlen ▸ hvlen_l.symm), hvlt_l,
                  hwfl, hfitl, hsbgl, hnbl⟩
              · obtain ⟨vT', lT', hvl', hvlt', hwf', hfit', hsbg', hnb'⟩ :=
                  hinv.items_ok p (List.mem_cons_of_mem _ hp1)
                exact ⟨vT', lT', hvl',
                  fun v hm => by
                    rw [hst1.1]
                    exact Nat.lt_of_lt_of_le (hvlt' v hm) (Nat.le_add_right _ _),
                  hwf', hfit', hsbg', hnb'⟩,
            by
              rw [hbind.2.1, hst1.1]
              have := hinv.nextVid_bound
              rw [List.map_cons] at this ⊢; dsimp only [workBinderCount0] at this ⊢
              omega,
            by
              have := hinv.nextSc_bound
              rw [List.map_cons] at this ⊢; dsimp only [workNodeCount0] at this ⊢
              omega,
            by
              have := hinv.argCount_bound
              rw [List.map_cons] at this ⊢; dsimp only [workArgCount0] at this ⊢
              omega,
            by rw [List.map_cons]; dsimp only [workArgCount0]; exact huses_b⟩
        refine finish_step hinv'
          (fun v hv => by
            have hv1 : v < st1.nextVid.toNat := by rw [hst1.1]; exact hv
            rw [hout, hbind.2.2.2.2.2.1 v]
            simp only [hv1, ↓reduceIte]
            rw [hst1.2.1])
          (fun v hv h => by
            have hv1 : v < st1.nextVid.toNat := by rw [hst1.1]; exact hv
            rw [hout, hbind.2.2.2.2.2.2.2 v]
            simp only [hv1, ↓reduceIte]
            exact h)
          (fun v hv => by
            rw [hout]
            rw [hbind.2.2.2.2.2.2.1 v, hst1.1])
          (by
            have hbc_l' := hbc_l
            rw [hout, hbind.2.1, hst1.1]; simp only [List.map_cons]
            dsimp only [workBinderCount0]; omega)
          (by rw [hout, hbind.2.1, hst1.1]; exact Nat.le_add_right _ _)
          (by rw [hout]; dsimp only; exact Nat.le_refl _)
          (by rw [hout]; dsimp only; omega)
          (fun v _ => by
            rw [hout]
            have hnu := nodeArgsUses0_add_linK0_le (UInt32.ofNat v) cur.venv hlin hnj hng
            simp only [List.map_cons]; dsimp only [workArgCount0]
            omega)
          (fun v hv => by
            rw [hout]; dsimp only
            have hnv_b2 :
                (preBindLoop0 (linCnt0 cur.node) cur.scope cur.venv st1).2.nextVid.toNat =
                st.nextVid.toNat + (linCnt0 cur.node).toNat := by rw [hbind.2.1, hst1.1]
            have hnv_lt32 : (UInt32.ofNat v).toNat < st.nextVid.toNat := by
              rw [u32_toNat_ofNat5, Nat.mod_eq_of_lt (Nat.lt_trans hv (UInt32.toNat_lt _))]
              exact hv
            have hnv_out_eq :
                (preBindLoop0 (linCnt0 cur.node) cur.scope cur.venv st1).2.nextVid =
                st.nextVid + UInt32.ofNat (linCnt0 cur.node).toNat :=
              u32_eq_add_of_toNat5 hnv_b2 (by rw [← hst1.1]; exact hnv_b)
            have hrest_eq : sameScopeSpineSum0 (UInt32.ofNat v) (st.defScope.getD v 0)
                (preBindLoop0 (linCnt0 cur.node) cur.scope cur.venv st1).2.nextVid rest =
                sameScopeSpineSum0 (UInt32.ofNat v) (st.defScope.getD v 0) st.nextVid rest :=
              sameScopeSpineSum0_congr_nv hnv_lt32 (by omega) (by
                rw [hnv_b2]
                have := hinv.nextVid_bound
                rw [List.map_cons] at this; dsimp only [workBinderCount0] at this
                omega)
            dsimp only [sameScopeSpineSum0]
            rw [hrest_eq, hbind.1, hst1.1]
            have hsp_expand : spineUses0 (UInt32.ofNat v) cur.venv st.nextVid cur.node =
                nodeArgsUses0 (UInt32.ofNat v) cur.venv cur.node +
                  spineUses0 (UInt32.ofNat v)
                    (pushFreshVids0 (linCnt0 cur.node).toNat st.nextVid cur.venv)
                    (preBindLoop0 (linCnt0 cur.node) cur.scope cur.venv st1).2.nextVid
                    (linK0 cur.node) := by
              rw [hnv_out_eq]
              exact spineUses0_lin (UInt32.ofNat v) cur.venv st.nextVid hlin hnj hng hfit
            have hv1 := hst1.2.2.2.2.2 v hv
            split at hv1
            · rename_i heq
              rw [hv1.1, hsp_expand]
              simp only [heq, ↓reduceIte, Nat.add_assoc]
            · rename_i hne
              simp only [hne, ↓reduceIte, Nat.zero_add]
              rw [hv1.1])
          (by
            rw [hout]; simp only [List.map_cons]; dsimp only [workArgCount0]
            omega)

theorem compileFnPre0_inv {ctx : LegalCtx0} {fn : TFlatFn0}
    (hwf : WfNode0 ctx (pushTys0 fn.as []) [] fn.body)
    (hg : fn.okGuardsFull = true) :
    let preRes := compileFnPre0 fn
    let preVenv := (preInit0 fn.as).1
    preVenv = pushFreshVids0 fn.as.length 0 [] ∧
    preRes.nextVid.toNat = fn.as.length + binderCount0 fn.body ∧
    preRes.nextVid.toNat < 2 ^ 31 ∧
    preRes.defScope.size = preRes.nextVid.toNat ∧
    preRes.uses.size = preRes.nextVid.toNat ∧
    preRes.escaped.size = preRes.nextVid.toNat ∧
    (∀ v < preRes.nextVid.toNat, preRes.escaped.getD v 0 = 0 ∨ preRes.escaped.getD v 0 = 1) ∧
    (∀ v < preRes.nextVid.toNat, preRes.uses.getD v 0 ≤ argCount0 fn.body) ∧
    argCount0 fn.body < 2 ^ 31 ∧
    (∀ v < fn.as.length, preRes.defScope.getD v 0 = 0 ∧
      preRes.uses.getD v 0 =
        spineUses0 (UInt32.ofNat v) preVenv (UInt32.ofNat fn.as.length) fn.body) := by
  have hsbg := TFlatFn0.okGuardsFull_singleBlock hg
  have hnb := TFlatFn0.okGuardsFull_noNegBool hg
  have hfit := TFlatFn0.okGuardsFull_sigLensFitU32 hg
  have hbd := TFlatFn0.okGuardsFull_boundsFitU32 hg
  simp only [TFlatFn0.sigLensFitU32, listLenFitsU32, Bool.and_eq_true, decide_eq_true_eq] at hfit
  simp only [TFlatFn0.boundsFitU32, Bool.and_eq_true, decide_eq_true_eq] at hbd
  have hlen_as : (tyLenU0 fn.as 0).toNat = fn.as.length := tyLenU0_eq_of_lt hfit.1.1
  let cap := Nat.add 32 (tyLenU0 fn.as 0).toNat
  have hinit := preBindLoop0_spec fn.as.length (tyLenU0 fn.as 0) 0 []
    (PreSt0.mk 0 (Array.emptyWithCapacity cap) (Array.emptyWithCapacity cap)
      (Array.emptyWithCapacity cap))
    hlen_as (by simp; omega) (by simp) (by simp) (by simp)
  have hinit_eq : preInit0 fn.as =
      preBindLoop0 (tyLenU0 fn.as 0) 0 []
        (PreSt0.mk 0 (Array.emptyWithCapacity cap) (Array.emptyWithCapacity cap)
          (Array.emptyWithCapacity cap)) := rfl
  rw [← hinit_eq] at hinit
  simp only [UInt32.toNat_zero, Nat.zero_add, Nat.not_lt_zero, ↓reduceIte] at hinit
  have hvlen_0 : (pushFreshVids0 fn.as.length 0 []).length = (pushTys0 fn.as []).length := by
    rw [pushFreshVids0_length, List.length_nil, pushTys0_eq_pushTypes, pushTypes_length,
      List.length_nil]
  have hvlt_0 : ∀ v ∈ (preInit0 fn.as).1, v.toNat < fn.as.length := by
    intro v hm
    rw [hinit.1] at hm
    rcases (mem_pushFreshVids0 fn.as.length 0 [] v).mp hm with hf | ⟨k, hk, rfl⟩
    · nomatch hf
    · rw [UInt32.zero_add, u32_toNat_ofNat5,
        Nat.mod_eq_of_lt (Nat.lt_trans hk (by omega))]
      exact hk
  have hinv0 : PreWorkInv0 ctx 1 (preInit0 fn.as).2 [PreItem0.mk fn.body (preInit0 fn.as).1 0] := by
    refine ⟨hinit.2.2.1.trans hinit.2.1.symm, hinit.2.2.2.1.trans hinit.2.1.symm,
      hinit.2.2.2.2.1.trans hinit.2.1.symm,
      fun v hv => by
        rw [hinit.2.1] at hv
        rw [hinit.2.2.2.2.2.1 v]
        simp only [hv, ↓reduceIte, UInt32.toNat_one, Nat.zero_lt_one],
      fun v hv => by
        rw [hinit.2.2.2.2.2.2.2 v]
        exact Or.inl rfl,
      by simp,
      fun p hp => by
        simp only [List.mem_singleton] at hp; subst hp
        simp only [UInt32.toNat_zero, UInt32.toNat_one]; exact Nat.zero_lt_one,
      fun p hp => by
        simp only [List.mem_singleton] at hp; subst hp
        rw [hinit.2.1]
        exact ⟨pushTys0 fn.as [], [], hinit.1 ▸ hvlen_0, hvlt_0, hwf, hfit.2, hsbg, hnb⟩,
      by rw [hinit.2.1, List.map_singleton]; dsimp only [workBinderCount0]; omega,
      by rw [List.map_singleton]; dsimp only [workNodeCount0]; rw [UInt32.toNat_one]; omega,
      by rw [List.map_singleton]; dsimp only [workArgCount0]; exact hbd.2,
      fun v hv => by
        rw [hinit.2.2.2.2.2.2.1 v]
        rw [List.map_singleton]; dsimp only [workArgCount0]
        simp only [Nat.add_zero, Nat.zero_add]
        exact hbd.2⟩
  have hrun := preRunAux0_inv ctx (nodeCount0 fn.body) 0x7fffffff 1 (preInit0 fn.as).2
    [PreItem0.mk fn.body (preInit0 fn.as).1 0]
    (by rw [List.map_singleton]; dsimp only [workNodeCount0]; exact Nat.add_zero _)
    (by change nodeCount0 fn.body ≤ 2147483647; omega) hinv0
  dsimp only [compileFnPre0]
  rw [← preRunAux0_snd_eq_preWorkLoop0]
  have hnv_init : (preInit0 fn.as).2.nextVid = UInt32.ofNat fn.as.length :=
    u32_ext_toNat5 (by
      rw [hinit.2.1, u32_toNat_ofNat5, Nat.mod_eq_of_lt (by omega)])
  refine ⟨hinit.1,
    by rw [hrun.1, hinit.2.1, List.map_singleton]
       dsimp only [workBinderCount0]; rw [Nat.add_zero],
    by rw [hrun.1, hinit.2.1, List.map_singleton]; dsimp only [workBinderCount0]; omega,
    hrun.2.1, hrun.2.2.1, hrun.2.2.2.1, hrun.2.2.2.2.2.2.2.2.2.1,
    fun v hv => by
      have hu := hrun.2.2.2.2.2.2.2.2.2.2.1 v hv
      by_cases hv0 : v < (preInit0 fn.as).2.nextVid.toNat
      · simp only [hv0, ↓reduceIte] at hu
        rw [hinit.2.2.2.2.2.2.1 v] at hu
        rw [List.map_singleton] at hu; dsimp only [workArgCount0] at hu
        simp only [Nat.add_zero, Nat.zero_add] at hu
        exact hu
      · rw [List.map_singleton] at hu; dsimp only [workArgCount0] at hu
        simp only [hv0, ↓reduceIte, Nat.add_zero, Nat.zero_add] at hu
        exact hu,
    hbd.2,
    fun v hv => ?_⟩
  have hv_init : v < (preInit0 fn.as).2.nextVid.toNat := by rw [hinit.2.1]; exact hv
  have hds0 : (preInit0 fn.as).2.defScope.getD v 0 = 0 := by
    rw [hinit.2.2.2.2.2.1 v]; simp [hv]
  have hu0 : (preInit0 fn.as).2.uses.getD v 0 = 0 := by
    rw [hinit.2.2.2.2.2.2.1 v]
  refine ⟨by rw [hrun.2.2.2.2.2.2.1 v hv_init, hds0], ?_⟩
  rw [hrun.2.2.2.2.2.2.2.2.2.2.2 v hv_init, hu0, hds0]
  dsimp only [sameScopeSpineSum0]
  simp only [UInt32.toNat_zero, ↓reduceIte, Nat.zero_add, Nat.add_zero, hnv_init]

/-! ## 2. Structural Label Uniqueness (`NoLab0`, `LabOk0`, `compileFn0_labOk0`) -/

/-- True iff `xs : List Dir0` emits no `.label` directives. -/
@[expose] def NoLab0 (xs : List Dir0) : Prop :=
  ∀ l, .label l ∉ xs

theorem noLab0_nil : NoLab0 [] := fun _ h => nomatch h

theorem noLab0_cons {d : Dir0} {xs : List Dir0} (hd : ∀ l, d ≠ .label l) (hxs : NoLab0 xs) :
    NoLab0 (d :: xs) := fun l hm =>
  (List.mem_cons.mp hm).elim (fun e => hd l e.symm) (hxs l)

theorem noLab0_append {xs ys : List Dir0} (hx : NoLab0 xs) (hy : NoLab0 ys) :
    NoLab0 (xs ++ ys) := fun l hm =>
  (List.mem_append.mp hm).elim (hx l) (hy l)

theorem noLab0_reverse {xs : List Dir0} (h : NoLab0 xs) : NoLab0 xs.reverse := fun l hm =>
  h l (List.mem_reverse.mp hm)

/-- Equal labels of `xs` sit at equal indices, and every label in `xs` satisfies `S`. -/
@[expose] def LabOk0 (S : Label0 → Prop) (xs : List Dir0) : Prop :=
  (∀ (i j : Nat) l, xs[i]? = some (.label l) → xs[j]? = some (.label l) → i = j) ∧
  ∀ l, .label l ∈ xs → S l

theorem labOk0_clean {S : Label0 → Prop} {xs : List Dir0} (h : NoLab0 xs) : LabOk0 S xs :=
  ⟨fun _ _ l hi _ => absurd (List.mem_of_getElem? hi) (h l), fun l hl => absurd hl (h l)⟩

theorem labOk0_mono {S S' : Label0 → Prop} {xs : List Dir0} (h : LabOk0 S xs)
    (hs : ∀ l, S l → S' l) : LabOk0 S' xs := ⟨h.1, fun l hl => hs l (h.2 l hl)⟩

theorem labOk0_single {S : Label0 → Prop} (l : Label0) (hl : S l) : LabOk0 S [.label l] := by
  refine ⟨fun i j l' hi hj => ?_, fun l' hm => ?_⟩
  · cases i <;> cases j <;> simp_all
  · simp only [List.mem_singleton, Dir0.label.injEq] at hm; exact hm ▸ hl

theorem labOk0_append {S₁ S₂ S : Label0 → Prop} {xs ys : List Dir0}
    (hx : LabOk0 S₁ xs) (hy : LabOk0 S₂ ys)
    (hdisj : ∀ l, .label l ∈ xs → .label l ∈ ys → False)
    (hs : ∀ l, S₁ l ∨ S₂ l → S l) : LabOk0 S (xs ++ ys) := by
  refine ⟨fun i j l hi hj => ?_, fun l hm => hs l ((List.mem_append.mp hm).imp (hx.2 l) (hy.2 l))⟩
  rw [List.getElem?_append] at hi hj
  split at hi <;> split at hj
  · exact hx.1 i j l hi hj
  · exact absurd (List.mem_of_getElem? hj) (fun hm => hdisj l (List.mem_of_getElem? hi) hm)
  · exact absurd (List.mem_of_getElem? hi) (fun hm => hdisj l (List.mem_of_getElem? hj) hm)
  · have := hy.1 _ _ l hi hj; omega

theorem labOk0_prepend_noLab {S : Label0 → Prop} {a xs : List Dir0} (ha : NoLab0 a)
    (hx : LabOk0 S xs) : LabOk0 S (a ++ xs) :=
  labOk0_append (labOk0_clean ha) hx (fun l hm _ => ha l hm) (fun _ h => h.elim False.elim id)

theorem labOk0_cons_nonLab {S : Label0 → Prop} {d : Dir0} {xs : List Dir0}
    (hd : ∀ l, d ≠ .label l) (hx : LabOk0 S xs) : LabOk0 S (d :: xs) :=
  labOk0_prepend_noLab (noLab0_cons hd noLab0_nil) hx

theorem labOk0_cons_label {S : Label0 → Prop} {l : Label0} {xs : List Dir0}
    (hl : .label l ∉ xs) (hx : LabOk0 S xs) (hs : S l) : LabOk0 S (.label l :: xs) :=
  labOk0_append (labOk0_single l hs) hx
    (fun _ hm1 hm2 =>
      hl (by simp only [List.mem_singleton, Dir0.label.injEq] at hm1; exact hm1 ▸ hm2))
    (fun _ h => h.elim id id)

theorem labOk0_reverse {S : Label0 → Prop} {xs : List Dir0} (hx : LabOk0 S xs) :
    LabOk0 S xs.reverse := by
  induction xs with
  | nil => exact labOk0_clean noLab0_nil
  | cons d rest ih =>
    rw [List.reverse_cons]
    have hrest : LabOk0 S rest :=
      ⟨fun i j l hi hj => by
          have := hx.1 (i + 1) (j + 1) l (by simpa using hi) (by simpa using hj)
          omega,
        fun l hl => hx.2 l (List.mem_cons_of_mem _ hl)⟩
    have ih' := ih hrest
    by_cases hdl : ∃ l, d = .label l
    · obtain ⟨l, rfl⟩ := hdl
      have hnin : .label l ∉ rest := fun hm => by
        obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hm
        have hget : (.label l :: rest)[k + 1]? = some (.label l) := by
          simp only [List.getElem?_cons_succ]; rw [List.getElem?_eq_getElem hk, he]
        have := hx.1 0 (k + 1) l rfl hget
        omega
      refine labOk0_append ih' (labOk0_single l (hx.2 l List.mem_cons_self))
        (fun l' hm1 hm2 => ?_) (fun _ h => h.elim id id)
      simp only [List.mem_singleton, Dir0.label.injEq] at hm2
      exact hnin (hm2 ▸ List.mem_reverse.mp hm1)
    · have hdnl : NoLab0 [d] := fun l hm =>
        hdl ⟨l, (List.mem_singleton.mp hm).symm⟩
      exact labOk0_append ih' (labOk0_clean hdnl)
        (fun l _ hm2 => hdnl l hm2) (fun _ h => h.elim id False.elim)

private theorem noLab0_emitSpAdj0 (isSub : Bool) (bytes : UInt64) {acc : List Dir0}
    (h : NoLab0 acc) : NoLab0 (emitSpAdj0 isSub bytes acc) := by
  dsimp only [emitSpAdj0]; split
  · dsimp only [pushDImm0]; repeat' split
    all_goals exact noLab0_cons (fun _ hc => by cases hc) h
  · dsimp only [pushDUnary0, pushDImm0]; repeat' split
    all_goals
      exact noLab0_cons (fun _ hc => by cases hc) (noLab0_cons (fun _ hc => by cases hc) h)

private theorem patchDir0_mem_label {bytes : UInt64} {d : Dir0} {l : Label0}
    (hm : .label l ∈ patchDir0 bytes d) : d = .label l := by
  cases d
  case label l' =>
    dsimp only [patchDir0] at hm
    simp only [List.mem_singleton, Dir0.label.injEq] at hm; exact hm ▸ rfl
  case spAdd isSub imm =>
    cases isSub
    · by_cases h0 : imm = 0
      · subst h0
        dsimp only [patchDir0] at hm
        have hnl : NoLab0 (revDirAux0 (emitSpAdj0 false bytes []) []) := by
          rw [revDirAux0_eq, List.append_nil]
          exact noLab0_reverse (noLab0_emitSpAdj0 false bytes noLab0_nil)
        exact absurd hm (hnl l)
      · have hp : patchDir0 bytes (.spAdd false imm) = [.spAdd false imm] := by
          simp [patchDir0, h0]
        rw [hp] at hm; simp only [List.mem_singleton] at hm; cases hm
    · dsimp only [patchDir0] at hm; simp only [List.mem_singleton] at hm; cases hm
  all_goals (dsimp only [patchDir0] at hm; simp only [List.mem_singleton] at hm; cases hm)

theorem labOk0_patchEpilogues0 (bytes : UInt64) {S : Label0 → Prop} {xs : List Dir0}
    (hx : LabOk0 S xs) : LabOk0 S (patchEpilogues0 bytes xs []) := by
  rw [patchEpilogues0_eq]
  induction xs with
  | nil => exact labOk0_clean noLab0_nil
  | cons d rest ih =>
    rw [List.flatMap_cons]
    have hrest : LabOk0 S rest :=
      ⟨fun i j l hi hj => by
          have := hx.1 (i + 1) (j + 1) l (by simpa using hi) (by simpa using hj)
          omega,
        fun l hl => hx.2 l (List.mem_cons_of_mem _ hl)⟩
    have ih' := ih hrest
    by_cases hdl : ∃ l, d = .label l
    · obtain ⟨l, rfl⟩ := hdl
      dsimp only [patchDir0, List.singleton_append]
      have hnin : .label l ∉ rest := fun hm => by
        obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hm
        have hget : (.label l :: rest)[k + 1]? = some (.label l) := by
          simp only [List.getElem?_cons_succ]; rw [List.getElem?_eq_getElem hk, he]
        have := hx.1 0 (k + 1) l rfl hget
        omega
      refine labOk0_cons_label (fun hm => ?_) ih' (hx.2 l List.mem_cons_self)
      rw [List.mem_flatMap] at hm
      obtain ⟨d', hd', hdl⟩ := hm
      exact hnin (patchDir0_mem_label hdl ▸ hd')
    · have hnl : NoLab0 (patchDir0 bytes d) := fun l hm =>
        hdl ⟨l, patchDir0_mem_label hm⟩
      exact labOk0_prepend_noLab hnl ih'

private theorem labOk0_pushDRR0 {S : Label0 → Prop} (t : UInt32) (w : Width) (rd rs : Reg64)
    {acc : List Dir0} (h : LabOk0 S acc) : LabOk0 S (pushDRR0 t w rd rs acc) := by
  dsimp only [pushDRR0]; repeat' split
  all_goals exact labOk0_cons_nonLab (fun _ hc => by cases hc) h

private theorem labOk0_pushDUnary0 {S : Label0 → Prop} (t : UInt32) (w : Width) (rd rs : Reg64)
    {acc : List Dir0} (h : LabOk0 S acc) : LabOk0 S (pushDUnary0 t w rd rs acc) := by
  dsimp only [pushDUnary0]; repeat' split
  all_goals exact labOk0_cons_nonLab (fun _ hc => by cases hc) h

private theorem labOk0_pushDImm0 {S : Label0 → Prop} (t : UInt32) (rd : Reg64) (imm : UInt64)
    {acc : List Dir0} (h : LabOk0 S acc) : LabOk0 S (pushDImm0 t rd imm acc) := by
  dsimp only [pushDImm0]; repeat' split
  all_goals exact labOk0_cons_nonLab (fun _ hc => by cases hc) h

private theorem labOk0_pushDShift0 {S : Label0 → Prop} (w : Width) (sk : ShiftKind0)
    (rd : Reg64) {acc : List Dir0} (h : LabOk0 S acc) :
    LabOk0 S (pushDShift0 w sk rd acc) :=
  labOk0_cons_nonLab (fun _ hc => by cases hc) h

private theorem labOk0_pushDAlu0 {S : Label0 → Prop} (w : Width) (ak : AluKind0) (rd rs : Reg64)
    {acc : List Dir0} (h : LabOk0 S acc) : LabOk0 S (pushDAlu0 w ak rd rs acc) :=
  labOk0_cons_nonLab (fun _ hc => by cases hc) h

private theorem labOk0_pushDMovsx0 {S : Label0 → Prop} (wd : Width) (rd : Reg64) (ws : Width)
    (rs : Reg64) {acc : List Dir0} (h : LabOk0 S acc) :
    LabOk0 S (pushDMovsx0 wd rd ws rs acc) :=
  labOk0_cons_nonLab (fun _ hc => by cases hc) h

private theorem labOk0_emitCanon0 {S : Label0 → Prop} (w : Width) (r : Reg64) {acc : List Dir0}
    (h : LabOk0 S acc) : LabOk0 S (emitCanon0 w r acc) := by
  cases w <;> dsimp only [emitCanon0]
  · exact labOk0_pushDRR0 _ _ _ _ h
  · exact labOk0_pushDRR0 _ _ _ _ h
  · exact labOk0_pushDRR0 _ _ _ _ h
  · exact h

private theorem labOk0_emitSlotMem0 {S : Label0 → Prop} (isLd : Bool) (r : Reg64) (sl : UInt32)
    {acc : List Dir0} (h : LabOk0 S acc) : LabOk0 S (emitSlotMem0 isLd r sl acc) := by
  cases isLd
  · simp only [emitSlotMem0, Bool.false_eq_true, ↓reduceIte]; split
    · exact labOk0_cons_nonLab (fun _ hc => by cases hc) h
    · exact labOk0_cons_nonLab (fun _ hc => by cases hc) (labOk0_pushDImm0 _ _ _ h)
  · simp only [emitSlotMem0, ↓reduceIte]; split
    · exact labOk0_cons_nonLab (fun _ hc => by cases hc) h
    · exact labOk0_cons_nonLab (fun _ hc => by cases hc) (labOk0_pushDImm0 _ _ _ h)

private theorem labOk0_emitLoadArg0 {S : Label0 → Prop} (rd : Reg64) (a : Arg0)
    (venv : List UInt32) (vslot : Array Nat) {acc : List Dir0} (h : LabOk0 S acc) :
    LabOk0 S (emitLoadArg0 rd a venv vslot acc) := by
  cases a with
  | var _ => exact labOk0_emitSlotMem0 _ _ _ h
  | immBool _ | immBits _ _ => exact labOk0_pushDImm0 _ _ _ h

private theorem labOk0_loadRegArgs0 {S : Label0 → Prop} (cfg : LoadCfg0) :
    ∀ (ts : List Ty0) (args : List Arg0) (i : UInt32) {acc : List Dir0},
      LabOk0 S acc → LabOk0 S (loadRegArgs0 cfg ts args i acc)
  | _, [], _, _, h => h
  | ts, a :: rest, i, acc, h => by
    dsimp only [loadRegArgs0]
    have h1 := labOk0_emitLoadArg0 (abiRegAt0 cfg.useRet i) a cfg.venv cfg.vslot h
    cases ts with
    | nil => exact labOk0_loadRegArgs0 cfg [] rest (i + 1) h1
    | cons t tRest =>
      apply labOk0_loadRegArgs0 cfg tRest rest (i + 1)
      cases cfg.canon
      · exact h1
      · exact labOk0_emitCanon0 (tyWidth0 t) _ h1

private theorem labOk0_emitOp0 {S : Label0 → Prop} (op : OpCode0) {acc : List Dir0}
    (h : LabOk0 S acc) : LabOk0 S (emitOp0 op acc) := by
  cases op with
  | un u t =>
    dsimp only [emitOp0, emitUn0]
    have h1 := labOk0_pushDRR0 0 .W64 .rax .rdi h
    cases u with
    | copy => exact labOk0_emitCanon0 _ _ h1
    | neg => exact labOk0_emitCanon0 _ _ (labOk0_pushDUnary0 _ _ _ _ h1)
    | not =>
      cases t
      · exact labOk0_pushDRR0 _ _ _ _
          (labOk0_pushDUnary0 _ _ _ _ (labOk0_pushDImm0 _ _ _ h1))
      all_goals exact labOk0_emitCanon0 _ _ (labOk0_pushDUnary0 _ _ _ _ h1)
  | bin b t =>
    dsimp only [emitOp0]
    cases b <;> dsimp only [emitBinShift0, emitBinAlu0]
    case shl | lshr | ashr | rotl | rotr =>
      have h2 := labOk0_pushDRR0 0 .W64 .rcx .rsi (labOk0_pushDRR0 0 .W64 .rax .rdi h)
      refine labOk0_emitCanon0 _ _ (labOk0_pushDShift0 _ _ _ ?_)
      cases tyWidth0 t <;> first | exact labOk0_pushDImm0 _ _ _ h2 | exact h2
    all_goals
      have h1 := labOk0_pushDRR0 0 .W64 .rax .rdi h
      cases t <;> first
        | exact labOk0_pushDRR0 _ _ _ _ (labOk0_pushDAlu0 _ _ _ _ h1)
        | exact labOk0_emitCanon0 _ _ (labOk0_pushDAlu0 _ _ _ _ h1)
  | cmp co t =>
    dsimp only [emitOp0, emitCmpSelect0]
    exact labOk0_pushDRR0 1 .W8 .rax .rax
      (labOk0_cons_nonLab (fun _ hc => by cases hc)
        (labOk0_cons_nonLab (fun _ hc => by cases hc) h))
  | select t =>
    dsimp only [emitOp0, emitCmpSelect0]
    exact labOk0_cons_nonLab (fun _ hc => by cases hc)
      (labOk0_pushDRR0 _ _ _ _ (labOk0_pushDRR0 _ _ _ _ h))
  | conv c m n =>
    dsimp only [emitOp0]
    cases c <;> dsimp only [emitConvZextTrunc0, emitConvSext0]
    · exact labOk0_pushDRR0 _ _ _ _ h
    · split
      · exact labOk0_emitCanon0 _ _ (labOk0_pushDRR0 _ _ _ _ h)
      · cases m <;> exact labOk0_pushDRR0 _ _ _ _ h
    · split
      · exact labOk0_emitCanon0 _ _ (labOk0_pushDRR0 _ _ _ _ h)
      · split
        · exact labOk0_pushDMovsx0 _ _ _ _ h
        · exact labOk0_emitCanon0 _ _ (labOk0_pushDMovsx0 _ _ _ _ h)
    · exact labOk0_emitCanon0 _ _ (labOk0_pushDRR0 _ _ _ _ h)
  | div d w =>
    dsimp only [emitOp0, emitDiv0]
    cases w
    · cases d <;> simp only [↓reduceIte, Bool.false_eq_true]
      · exact labOk0_emitCanon0 _ _ (labOk0_pushDUnary0 _ _ _ _
          (labOk0_pushDRR0 _ _ _ _ (labOk0_pushDRR0 _ _ _ _ h)))
      · exact labOk0_emitCanon0 _ _ (labOk0_pushDRR0 _ _ _ _ (labOk0_pushDUnary0 _ _ _ _
          (labOk0_pushDRR0 _ _ _ _ (labOk0_pushDRR0 _ _ _ _ h))))
      · exact labOk0_emitCanon0 _ _ (labOk0_pushDUnary0 _ _ _ _
          (labOk0_pushDMovsx0 _ _ _ _ (labOk0_pushDMovsx0 _ _ _ _ h)))
      · exact labOk0_emitCanon0 _ _ (labOk0_pushDRR0 _ _ _ _ (labOk0_pushDUnary0 _ _ _ _
          (labOk0_pushDMovsx0 _ _ _ _ (labOk0_pushDMovsx0 _ _ _ _ h))))
    · cases d <;> simp only [↓reduceIte, Bool.false_eq_true]
      · exact labOk0_emitCanon0 _ _ (labOk0_pushDUnary0 _ _ _ _
          (labOk0_pushDRR0 _ _ _ _ (labOk0_pushDRR0 _ _ _ _ h)))
      · exact labOk0_emitCanon0 _ _ (labOk0_pushDRR0 _ _ _ _ (labOk0_pushDUnary0 _ _ _ _
          (labOk0_pushDRR0 _ _ _ _ (labOk0_pushDRR0 _ _ _ _ h))))
      · exact labOk0_emitCanon0 _ _ (labOk0_pushDUnary0 _ _ _ _
          (labOk0_pushDMovsx0 _ _ _ _ (labOk0_pushDMovsx0 _ _ _ _ h)))
      · exact labOk0_emitCanon0 _ _ (labOk0_pushDRR0 _ _ _ _ (labOk0_pushDUnary0 _ _ _ _
          (labOk0_pushDMovsx0 _ _ _ _ (labOk0_pushDMovsx0 _ _ _ _ h))))
    · cases d <;> simp only [↓reduceIte, Bool.false_eq_true]
      · exact labOk0_pushDUnary0 _ _ _ _ (labOk0_pushDRR0 _ _ _ _ (labOk0_pushDRR0 _ _ _ _ h))
      · exact labOk0_pushDRR0 _ _ _ _ (labOk0_pushDUnary0 _ _ _ _
          (labOk0_pushDRR0 _ _ _ _ (labOk0_pushDRR0 _ _ _ _ h)))
      · exact labOk0_pushDUnary0 _ _ _ _ (labOk0_pushDRR0 _ _ _ _ (labOk0_pushDRR0 _ _ _ _ h))
      · exact labOk0_pushDRR0 _ _ _ _ (labOk0_pushDUnary0 _ _ _ _
          (labOk0_pushDRR0 _ _ _ _ (labOk0_pushDRR0 _ _ _ _ h)))
    · cases d <;> simp only [↓reduceIte, Bool.false_eq_true]
      · exact labOk0_pushDUnary0 _ _ _ _ (labOk0_pushDRR0 _ _ _ _ h)
      · exact labOk0_pushDRR0 _ _ _ _ (labOk0_pushDUnary0 _ _ _ _ (labOk0_pushDRR0 _ _ _ _ h))
      · exact labOk0_pushDUnary0 _ _ _ _ (labOk0_pushDRR0 _ _ _ _ h)
      · exact labOk0_pushDRR0 _ _ _ _ (labOk0_pushDUnary0 _ _ _ _ (labOk0_pushDRR0 _ _ _ _ h))
  | umulw64 => exact h

private theorem labOk0_emitLinNode0 {S : Label0 → Prop} (cur : RegaTask0) (st : RegaSt0)
    (h : LabOk0 S st.revDirs) : LabOk0 S (emitLinNode0 cur st) := by
  dsimp only [emitLinNode0, emitLinMem0, emitLinUmulw0, emitLinStore0]
  cases cur.node with
  | let1 op args _ => exact labOk0_emitOp0 op (labOk0_loadRegArgs0 _ [] args 0 h)
  | call fnSym as _ args _ =>
    exact labOk0_cons_nonLab (fun _ hc => by cases hc) (labOk0_loadRegArgs0 _ as args 0 h)
  | let2Umulw64 a b _ =>
    exact labOk0_pushDRR0 _ _ _ _ (labOk0_pushDRR0 _ _ _ _
      (labOk0_emitLoadArg0 _ b _ _ (labOk0_emitLoadArg0 _ a _ _ h)))
  | load _ addr _ => exact labOk0_pushDRR0 _ _ _ _ (labOk0_emitLoadArg0 _ addr _ _ h)
  | store _ val addr _ =>
    exact labOk0_pushDRR0 _ _ _ _ (labOk0_emitLoadArg0 _ addr _ _ (labOk0_emitLoadArg0 _ val _ _ h))
  | _ => exact h

private theorem labOk0_bindRetsN0 {S : Label0 → Prop} (esc : Array Nat) :
    ∀ (n : Nat) (rem idx : UInt32) (bl : BindListOut0),
      rem.toNat = n → LabOk0 S bl.st.revDirs →
      LabOk0 S (bindRetsN0 esc rem idx bl).st.revDirs
  | 0, rem, idx, bl, hr, h => by
    have h0 : rem = 0 := u32_ext_toNat5 hr
    subst h0; rw [bindRetsN0.eq_def]; simp only [↓reduceDIte]; exact h
  | k + 1, rem, idx, bl, hr, h => by
    have hne : rem ≠ 0 := fun hz => by subst hz; simp at hr
    have hdef := bindRetsN0.eq_def esc rem idx bl
    simp only [hne, ↓reduceDIte] at hdef
    rw [hdef]
    have hsub : (rem - 1).toNat = k := by rw [u32_sub1_toNat5 (by omega), hr]; omega
    apply labOk0_bindRetsN0 esc k (rem - 1) (idx + 1) _ hsub
    dsimp only [bindOneSlot0]
    split <;> dsimp only
    · exact labOk0_emitSlotMem0 _ _ _ h
    · exact h

private theorem noLab0_bindEntryArgs0 :
    ∀ (ts : List Ty0) (i : UInt32) (venv : List UInt32) (st : RegaSt0),
      NoLab0 st.revDirs → NoLab0 (bindEntryArgs0 ts i venv st).st.revDirs
  | [], _, _, _, h => h
  | t :: rest, i, venv, st, h => by
    dsimp only [bindEntryArgs0, bindOneEntryArg0]
    apply noLab0_bindEntryArgs0 rest (i + 1) _ _
    have hc : LabOk0 (fun _ => False) (emitSlotMem0 false (abiRegAt0 false i) i
        (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) st.revDirs)) :=
      labOk0_emitSlotMem0 _ _ _ (labOk0_emitCanon0 _ _ (labOk0_clean h))
    exact fun l hm => hc.2 l hm

private theorem bindBlockParams0_revDirs :
    ∀ (pts : List Ty0) (venv : List UInt32) (st : RegaSt0) (free : List UInt32) (nxt : UInt32),
      (bindBlockParams0 pts venv st free nxt).st.revDirs = st.revDirs
  | [], _, _, _, _ => rfl
  | _ :: rest, venv, st, free, nxt => by
    dsimp only [bindBlockParams0, bindOneBlockSlot0]
    exact bindBlockParams0_revDirs rest _ _ _ _

private theorem labOk0_jumpStageLoop0 {S : Label0 → Prop} :
    ∀ (args : List Arg0) (tmpIdx : UInt32) (venv : List UInt32) (vslot : Array Nat)
      {acc : List Dir0}, LabOk0 S acc → LabOk0 S (jumpStageLoop0 args tmpIdx venv vslot acc)
  | [], _, _, _, _, h => h
  | a :: rest, tmpIdx, venv, vslot, _, h =>
    labOk0_jumpStageLoop0 rest (tmpIdx + 1) venv vslot
      (labOk0_emitSlotMem0 _ _ _ (labOk0_emitLoadArg0 _ a venv vslot h))

private theorem labOk0_jumpCopyLoop0 {S : Label0 → Prop} :
    ∀ (tgts : List UInt32) (tmpIdx : UInt32) {acc : List Dir0},
      LabOk0 S acc → LabOk0 S (jumpCopyLoop0 tgts tmpIdx acc)
  | [], _, _, h => h
  | _ :: rest, tmpIdx, _, h =>
    labOk0_jumpCopyLoop0 rest (tmpIdx + 1)
      (labOk0_emitSlotMem0 _ _ _ (labOk0_emitSlotMem0 _ _ _ h))

private theorem labOk0_emitJump0 {S : Label0 → Prop} (j : UInt32) (args : List Arg0)
    (task : RegaTask0) (st : RegaSt0) (ctrl : CtrlSt0) (h : LabOk0 S st.revDirs) :
    LabOk0 S (emitJump0 j args task st ctrl).revDirs := by
  dsimp only [emitJump0]
  cases args with
  | nil => exact labOk0_cons_nonLab (fun _ hc => by cases hc) h
  | cons a rest =>
    cases rest with
    | nil =>
      dsimp only [emitJumpOne0, emitJumpOneDir0]
      apply labOk0_cons_nonLab (fun _ hc => by cases hc)
      split
      · exact labOk0_emitSlotMem0 _ _ _ (labOk0_emitLoadArg0 _ a task.venv st.vslot h)
      · exact h
    | cons _ _ =>
      dsimp only [emitJumpMulti0]
      exact labOk0_cons_nonLab (fun _ hc => by cases hc)
        (labOk0_jumpCopyLoop0 _ _ (labOk0_jumpStageLoop0 _ _ _ _ h))

private theorem singleBlockGroups_linK0 {n : TFlat0} (h : n.singleBlockGroups = true) :
    (linK0 n).singleBlockGroups = true := by
  cases n <;> (dsimp only [linK0, TFlat0.singleBlockGroups] at h ⊢; first | done | exact h)

private theorem workLbls_nodup_cons_zero {t : RegaTask0} {rest : List RegaTask0} (hz : t.lblId = 0)
    (h : ((t :: rest).filterMap fun x => if x.lblId = 0 then none else some x.lblId).Nodup) :
    (rest.filterMap fun x => if x.lblId = 0 then none else some x.lblId).Nodup := by
  simpa [hz] using h

private theorem workLbls_nodup_cons_nz {t : RegaTask0} {rest : List RegaTask0} (hnz : t.lblId ≠ 0)
    (h : ((t :: rest).filterMap fun x => if x.lblId = 0 then none else some x.lblId).Nodup) :
    (t.lblId ∉ rest.filterMap fun x => if x.lblId = 0 then none else some x.lblId) ∧
    (rest.filterMap fun x => if x.lblId = 0 then none else some x.lblId).Nodup := by
  simpa [hnz, List.nodup_cons] using h

@[expose] def WorkLabInv0 (nextLbl : UInt32) (work : List RegaTask0) : Prop :=
  1 ≤ nextLbl.toNat ∧
  (work.filterMap fun t => if t.lblId = 0 then none else some t.lblId).Nodup ∧
  (∀ t ∈ work, t.lblId ≠ 0 → 1 ≤ t.lblId.toNat ∧ t.lblId.toNat < nextLbl.toNat) ∧
  (∀ t ∈ work, t.node.singleBlockGroups = true) ∧
  nextLbl.toNat + workNodeCount0 (work.map RegaTask0.node) < 2 ^ 31

private theorem blocksNodeCount0_ge_len :
    ∀ (bs : List (List Ty0 × TFlat0)), bs.length ≤ blocksNodeCount0 bs
  | [] => Nat.le_refl 0
  | (_, b) :: rest => by
    have := nodeCount0_pos b
    have := blocksNodeCount0_ge_len rest
    rw [List.length_cons]; dsimp only [blocksNodeCount0]
    omega

private theorem regaPrepGroup0_labs :
    ∀ (bodies : List (List Ty0 × TFlat0)) (venv : List UInt32) (gp : GroupPrepOut0),
      gp.ctrl.nextLbl.toNat + bodies.length < 2 ^ 31 →
      1 ≤ gp.ctrl.nextLbl.toNat →
      (∀ gm ∈ gp.metas, 1 ≤ gm.lbl.toNat ∧ gm.lbl.toNat < gp.ctrl.nextLbl.toNat) →
      (gp.metas.map GroupMeta0.lbl).Nodup →
      let gp' := regaPrepGroup0 bodies venv gp
      gp'.ctrl.fnIdx = gp.ctrl.fnIdx ∧
      gp'.ctrl.nextLbl.toNat = gp.ctrl.nextLbl.toNat + bodies.length ∧
      gp'.st.revDirs = gp.st.revDirs ∧
      (∀ gm ∈ gp'.metas, 1 ≤ gm.lbl.toNat ∧ gm.lbl.toNat < gp'.ctrl.nextLbl.toNat) ∧
      (gp'.metas.map GroupMeta0.lbl).Nodup ∧
      (∀ gm ∈ gp'.metas, gm ∈ gp.metas ∨ gp.ctrl.nextLbl.toNat ≤ gm.lbl.toNat) := by
  intro bodies
  induction bodies with
  | nil =>
    intro venv gp _ _ hgm hnd
    exact ⟨rfl, rfl, rfl, hgm, hnd, fun _ hm => Or.inl hm⟩
  | cons p rest ih =>
    intro venv gp hlt h1 hgm hnd
    rcases p with ⟨pts, b⟩
    dsimp only [regaPrepGroup0, prepOneBlock0, prepOneBind0, prepFinishBlock0, prepUpdCtrl0]
    have hlbl1 : (gp.ctrl.nextLbl + 1).toNat = gp.ctrl.nextLbl.toNat + 1 :=
      u32_add1_toNat5 (by simp only [List.length_cons] at hlt; omega)
    have hbb_rd := bindBlockParams0_revDirs pts venv gp.st gp.free gp.nxt
    have hnin : gp.ctrl.nextLbl ∉ gp.metas.map GroupMeta0.lbl := fun hm => by
      obtain ⟨gm, hmem, he⟩ := List.mem_map.mp hm
      have := (hgm gm hmem).2; rw [he] at this; omega
    let bb := bindBlockParams0 pts venv gp.st gp.free gp.nxt
    let ctrl1 : CtrlSt0 :=
      { gp.ctrl with
        nextLbl := gp.ctrl.nextLbl + 1
        lblSlots := gp.ctrl.lblSlots.push
          (slotsOfVids0 (tyLenU0 pts 0) bb.venv bb.st.vslot []) }
    let gp1 : GroupPrepOut0 :=
      GroupPrepOut0.mk (gp.ctrl.nextLbl :: gp.lenv) bb.st ctrl1 bb.free bb.nxt
        (GroupMeta0.mk gp.ctrl.nextLbl b bb.venv :: gp.metas)
    have ih' := ih venv gp1
      (by simp only [gp1, ctrl1, hlbl1, List.length_cons] at hlt ⊢; omega)
      (by simp only [gp1, ctrl1, hlbl1]; omega)
      (fun gm hm => by
        simp only [gp1, ctrl1, hlbl1] at hm ⊢
        rcases List.mem_cons.mp hm with rfl | hm'
        · dsimp only; omega
        · have := hgm gm hm'; omega)
      (List.nodup_cons.mpr ⟨hnin, hnd⟩)
    dsimp only at ih'
    refine ⟨ih'.1, by rw [ih'.2.1]; simp only [gp1, ctrl1, hlbl1, List.length_cons]; omega,
      ih'.2.2.1.trans hbb_rd, ih'.2.2.2.1, ih'.2.2.2.2.1, fun gm hm => ?_⟩
    rcases ih'.2.2.2.2.2 gm hm with hmem | hge
    · rcases List.mem_cons.mp hmem with rfl | hm'
      · exact Or.inr (Nat.le_refl _)
      · exact Or.inl hm'
    · exact Or.inr (by simp only [gp1, ctrl1, hlbl1] at hge; omega)

theorem regaRunAux0_labInv (fnIdx : UInt32) :
    ∀ (N : Nat) (fuel : UInt32) (esc : Array Nat) (st : RegaSt0) (ctrl : CtrlSt0)
      (work : List RegaTask0),
      workNodeCount0 (work.map RegaTask0.node) = N →
      N ≤ fuel.toNat →
      ctrl.fnIdx = fnIdx →
      WorkLabInv0 ctrl.nextLbl work →
      LabOk0 (fun l => ∃ j : UInt32, 1 ≤ j.toNat ∧ j.toNat < ctrl.nextLbl.toNat ∧
        l = .loc fnIdx j ∧ ∀ t ∈ work, t.lblId ≠ 0 → j ≠ t.lblId) st.revDirs →
      let r := regaRunAux0 fuel esc st ctrl work
      r.2.fnIdx = fnIdx ∧ r.2.nextLbl.toNat ≤ ctrl.nextLbl.toNat + N ∧
      1 ≤ r.2.nextLbl.toNat ∧
      LabOk0 (fun l => ∃ j : UInt32, 1 ≤ j.toNat ∧ j.toNat < r.2.nextLbl.toNat ∧
        l = .loc fnIdx j) r.1.revDirs := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro fuel esc st ctrl work hN hle hfn hwk hlab
    cases work with
    | nil =>
      subst hN
      rw [List.map_nil] at hle ⊢; dsimp only [workNodeCount0] at hle ⊢
      simp only [Nat.add_zero] at hle ⊢
      have hr : regaRunAux0 fuel esc st ctrl [] = (st, ctrl) :=
        regaRunAux0_nil fuel esc st ctrl
      rw [hr]
      refine ⟨hfn, Nat.le_refl _, hwk.1, labOk0_mono hlab ?_⟩
      rintro l ⟨j, h1, h2, rfl, _⟩; exact ⟨j, h1, h2, rfl⟩
    | cons cur rest =>
      have hpos : 0 < N := by
        rw [← hN, List.map_cons]; dsimp only [workNodeCount0]
        have := nodeCount0_pos cur.node; omega
      have hfne : fuel ≠ 0 := fun h => by
        have := congrArg UInt32.toNat h; simp at this; omega
      have hN1 : (fuel - 1).toNat = fuel.toNat - 1 := u32_sub1_toNat5 (by omega)
      have hrest_bnd : ∀ t ∈ rest, t.lblId ≠ 0 →
          1 ≤ t.lblId.toNat ∧ t.lblId.toNat < ctrl.nextLbl.toNat := fun t ht =>
        hwk.2.2.1 t (List.mem_cons_of_mem _ ht)
      have hrest_nodup :
          (rest.filterMap fun t => if t.lblId = 0 then none else some t.lblId).Nodup := by
        by_cases hcz : cur.lblId = 0
        · exact workLbls_nodup_cons_zero hcz hwk.2.1
        · exact (workLbls_nodup_cons_nz hcz hwk.2.1).2
      have hcur_sbg : cur.node.singleBlockGroups = true := hwk.2.2.2.1 cur List.mem_cons_self
      have hrest_sbg : ∀ t ∈ rest, t.node.singleBlockGroups = true := fun t ht =>
        hwk.2.2.2.1 t (List.mem_cons_of_mem _ ht)
      let st0 := regaPrependLbl0 cur st ctrl
      have hst0_lab : LabOk0 (fun l => ∃ j : UInt32, 1 ≤ j.toNat ∧ j.toNat < ctrl.nextLbl.toNat ∧
          l = .loc fnIdx j ∧ ∀ t ∈ rest, t.lblId ≠ 0 → j ≠ t.lblId) st0.revDirs := by
        dsimp only [st0, regaPrependLbl0]
        by_cases hcz : cur.lblId = 0
        · simp only [hcz, ↓reduceIte]
          refine labOk0_mono hlab ?_
          rintro l ⟨j, h1, h2, rfl, hnex⟩
          exact ⟨j, h1, h2, rfl, fun t ht => hnex t (List.mem_cons_of_mem _ ht)⟩
        · simp only [hcz, ↓reduceIte, hfn]
          have hcb := hwk.2.2.1 cur List.mem_cons_self hcz
          have hnin_st : .label (.loc fnIdx cur.lblId) ∉ st.revDirs := fun hm => by
            obtain ⟨j, _, _, hj, hnex⟩ := hlab.2 (.loc fnIdx cur.lblId) hm
            have he : j = cur.lblId := (Label0.loc.inj hj).2.symm
            exact hnex cur List.mem_cons_self hcz he
          have hnin_rest : ∀ t ∈ rest, t.lblId ≠ 0 → cur.lblId ≠ t.lblId := by
            intro t ht htnz he
            have hmem : cur.lblId ∈ rest.filterMap fun x =>
                if x.lblId = 0 then none else some x.lblId :=
              List.mem_filterMap.mpr ⟨t, ht, by simp [htnz, he]⟩
            exact (workLbls_nodup_cons_nz hcz hwk.2.1).1 hmem
          refine labOk0_cons_label hnin_st (labOk0_mono hlab ?_)
            ⟨cur.lblId, hcb.1, hcb.2, rfl, hnin_rest⟩
          rintro l ⟨j, h1, h2, rfl, hnex⟩
          exact ⟨j, h1, h2, rfl, fun t ht => hnex t (List.mem_cons_of_mem _ ht)⟩
      let ls := regaStep0 esc cur st0 ctrl rest
      have hdef_eq : regaRunAux0 fuel esc st ctrl (cur :: rest) =
          regaRunAux0 (fuel - 1) esc ls.st ls.ctrl ls.work :=
        regaRunAux0_succ hfne esc st ctrl cur rest
      have hcnt : workNodeCount0 (ls.work.map RegaTask0.node) + 1 = N := by
        rw [← hN]
        simpa only [ls, List.map_cons] using regaWorkNodeCount0_children esc cur st0 ctrl rest
      have hlt_N : workNodeCount0 (ls.work.map RegaTask0.node) < N := by omega
      have finish_ls : ls.ctrl.fnIdx = fnIdx →
          WorkLabInv0 ls.ctrl.nextLbl ls.work →
          ls.ctrl.nextLbl.toNat ≤ ctrl.nextLbl.toNat +
            (N - workNodeCount0 (ls.work.map RegaTask0.node)) →
          LabOk0 (fun l => ∃ j : UInt32, 1 ≤ j.toNat ∧ j.toNat < ls.ctrl.nextLbl.toNat ∧
            l = .loc fnIdx j ∧ ∀ t ∈ ls.work, t.lblId ≠ 0 → j ≠ t.lblId) ls.st.revDirs →
          let r := regaRunAux0 fuel esc st ctrl (cur :: rest)
          r.2.fnIdx = fnIdx ∧ r.2.nextLbl.toNat ≤ ctrl.nextLbl.toNat + N ∧
          1 ≤ r.2.nextLbl.toNat ∧
          LabOk0 (fun l => ∃ j : UInt32, 1 ≤ j.toNat ∧ j.toNat < r.2.nextLbl.toNat ∧
            l = .loc fnIdx j) r.1.revDirs := by
        intro hfn' hwk' hnl' hlab'
        dsimp only
        rw [hdef_eq]
        have ih' := ih (workNodeCount0 (ls.work.map RegaTask0.node)) hlt_N (fuel - 1) esc
          ls.st ls.ctrl ls.work rfl (by omega) hfn' hwk' hlab'
        dsimp only at ih'
        exact ⟨ih'.1, by omega, ih'.2.2.1, ih'.2.2.2⟩
      cases hnd : cur.node with
      | tailCall fnSym as args | exit fnSym as args =>
        have hc : ls.ctrl = ctrl := by
          dsimp only [ls, regaStep0]; rw [hnd]; dsimp only [regaStepCtrl0]; rw [hnd]
        have hw : ls.work = rest := by
          dsimp only [ls, regaStep0]; rw [hnd]; dsimp only [regaStepCtrl0]; rw [hnd]
        have hr : LabOk0 (fun l => ∃ j : UInt32, 1 ≤ j.toNat ∧ j.toNat < ctrl.nextLbl.toNat ∧
            l = .loc fnIdx j ∧ ∀ t ∈ rest, t.lblId ≠ 0 → j ≠ t.lblId) ls.st.revDirs := by
          dsimp only [ls, regaStep0]; rw [hnd]; dsimp only [regaStepCtrl0]; rw [hnd]
          dsimp only [stepTail0]
          exact labOk0_cons_nonLab (fun _ hc => by cases hc)
            (labOk0_cons_nonLab (fun _ hc => by cases hc)
              (labOk0_loadRegArgs0 _ as args 0 hst0_lab))
        refine finish_ls (hc ▸ hfn) ⟨hc ▸ hwk.1, hw ▸ hrest_nodup,
          fun t ht htz => hc ▸ hrest_bnd t (hw ▸ ht) htz,
          fun t ht => hrest_sbg t (hw ▸ ht), by rw [hc]; have := hwk.2.2.2.2; omega⟩
          (by rw [hc]; omega) (hc ▸ hw ▸ hr)
      | jump j args =>
        have hc : ls.ctrl = ctrl := by
          dsimp only [ls, regaStep0]; rw [hnd]; dsimp only [regaStepCtrl0]; rw [hnd]
        have hw : ls.work = rest := by
          dsimp only [ls, regaStep0]; rw [hnd]; dsimp only [regaStepCtrl0]; rw [hnd]
        have hr : LabOk0 (fun l => ∃ j : UInt32, 1 ≤ j.toNat ∧ j.toNat < ctrl.nextLbl.toNat ∧
            l = .loc fnIdx j ∧ ∀ t ∈ rest, t.lblId ≠ 0 → j ≠ t.lblId) ls.st.revDirs := by
          dsimp only [ls, regaStep0]; rw [hnd]; dsimp only [regaStepCtrl0]; rw [hnd]
          exact labOk0_emitJump0 j args cur st0 ctrl hst0_lab
        refine finish_ls (hc ▸ hfn) ⟨hc ▸ hwk.1, hw ▸ hrest_nodup,
          fun t ht htz => hc ▸ hrest_bnd t (hw ▸ ht) htz,
          fun t ht => hrest_sbg t (hw ▸ ht), by rw [hc]; have := hwk.2.2.2.2; omega⟩
          (by rw [hc]; omega) (hc ▸ hw ▸ hr)
      | ret vs =>
        have hc : ls.ctrl = ctrl := by
          dsimp only [ls, regaStep0]; rw [hnd]; dsimp only [regaStepCtrl0]; rw [hnd]
        have hw : ls.work = rest := by
          dsimp only [ls, regaStep0]; rw [hnd]; dsimp only [regaStepCtrl0]; rw [hnd]
        have hr : LabOk0 (fun l => ∃ j : UInt32, 1 ≤ j.toNat ∧ j.toNat < ctrl.nextLbl.toNat ∧
            l = .loc fnIdx j ∧ ∀ t ∈ rest, t.lblId ≠ 0 → j ≠ t.lblId) ls.st.revDirs := by
          dsimp only [ls, regaStep0]; rw [hnd]; dsimp only [regaStepCtrl0]; rw [hnd]
          dsimp only [stepRet0]
          exact labOk0_cons_nonLab (fun _ hc => by cases hc)
            (labOk0_cons_nonLab (fun _ hc => by cases hc)
              (labOk0_loadRegArgs0 _ [] vs 0 hst0_lab))
        refine finish_ls (hc ▸ hfn) ⟨hc ▸ hwk.1, hw ▸ hrest_nodup,
          fun t ht htz => hc ▸ hrest_bnd t (hw ▸ ht) htz,
          fun t ht => hrest_sbg t (hw ▸ ht), by rw [hc]; have := hwk.2.2.2.2; omega⟩
          (by rw [hc]; omega) (hc ▸ hw ▸ hr)
      | hlt =>
        have hc : ls.ctrl = ctrl := by
          dsimp only [ls, regaStep0]; rw [hnd]; dsimp only [regaStepCtrl0]; rw [hnd]
        have hw : ls.work = rest := by
          dsimp only [ls, regaStep0]; rw [hnd]; dsimp only [regaStepCtrl0]; rw [hnd]
        have hr : ls.st.revDirs = st0.revDirs := by
          dsimp only [ls, regaStep0]; rw [hnd]; dsimp only [regaStepCtrl0]; rw [hnd]
        refine finish_ls (hc ▸ hfn) ⟨hc ▸ hwk.1, hw ▸ hrest_nodup,
          fun t ht htz => hc ▸ hrest_bnd t (hw ▸ ht) htz,
          fun t ht => hrest_sbg t (hw ▸ ht), by rw [hc]; have := hwk.2.2.2.2; omega⟩
          (by rw [hc]; omega) (hc ▸ hw ▸ hr ▸ hst0_lab)
      | let1 _ _ k | let2Umulw64 _ _ k | load _ _ k | store _ _ _ k | call _ _ _ _ k =>
        have hk_sbg : (linK0 cur.node).singleBlockGroups = true := singleBlockGroups_linK0 hcur_sbg
        have hc : ls.ctrl = ctrl := by dsimp only [ls, regaStep0]; rw [hnd]; rfl
        have hweq : ∃ t0, ls.work = t0 :: rest ∧ t0.lblId = 0 ∧ t0.node = linK0 cur.node := by
          dsimp only [ls, regaStep0, stepLinear0, stepLinBindPush0, linBindPush0]; rw [hnd]
          exact ⟨_, rfl, rfl, rfl⟩
        obtain ⟨t0, hw, ht0_z, ht0_n⟩ := hweq
        have hr : LabOk0 (fun l => ∃ j : UInt32, 1 ≤ j.toNat ∧ j.toNat < ctrl.nextLbl.toNat ∧
            l = .loc fnIdx j ∧ ∀ t ∈ rest, t.lblId ≠ 0 → j ≠ t.lblId) ls.st.revDirs := by
          dsimp only [ls, regaStep0]; rw [hnd]
          dsimp only [stepLinear0, stepLinBindPush0, linBindPush0]
          exact labOk0_bindRetsN0 esc (linCnt0 cur.node).toNat (linCnt0 cur.node) 0 _ rfl
            (labOk0_emitLinNode0 cur st0 hst0_lab)
        refine finish_ls (hc ▸ hfn) ⟨hc ▸ hwk.1,
          by rw [hw]; simp only [List.filterMap_cons, ht0_z, ↓reduceIte]; exact hrest_nodup,
          fun t ht htz => by
            rw [hw] at ht
            rcases List.mem_cons.mp ht with rfl | ht'
            · exact absurd ht0_z htz
            · exact hc ▸ hrest_bnd t ht' htz,
          fun t ht => by
            rw [hw] at ht
            rcases List.mem_cons.mp ht with rfl | ht'
            · rw [ht0_n]; exact hk_sbg
            · exact hrest_sbg t ht',
          by rw [hc]; have := hwk.2.2.2.2; omega⟩
          (by rw [hc]; omega) ?_
        rw [hc, hw]
        refine labOk0_mono hr ?_
        rintro l ⟨j, h1, h2, rfl, hnex⟩
        exact ⟨j, h1, h2, rfl, fun t ht htz => by
          rcases List.mem_cons.mp ht with rfl | ht'
          · exact absurd ht0_z htz
          · exact hnex t ht' htz⟩
      | jnz c t e =>
        rw [hnd] at hcur_sbg
        dsimp only [TFlat0.singleBlockGroups] at hcur_sbg; rw [Bool.and_eq_true] at hcur_sbg
        have hpos_nl : 1 ≤ ctrl.nextLbl.toNat := hwk.1
        have hlt_31 : ctrl.nextLbl.toNat + 1 < 2 ^ 31 := by
          have := hwk.2.2.2.2
          rw [List.map_cons, hnd] at this; dsimp only [workNodeCount0, nodeCount0] at this
          omega
        have hadd1 : (ctrl.nextLbl + 1).toNat = ctrl.nextLbl.toNat + 1 :=
          u32_add1_toNat5 (by omega)
        have hnz_lbl : ctrl.nextLbl ≠ 0 := fun hz => by
          have := hpos_nl; simp [hz] at this
        have hc : ls.ctrl =
            CtrlSt0.mk ctrl.fnIdx (ctrl.nextLbl + 1) (ctrl.lblSlots.push []) := by
          dsimp only [ls, regaStep0]; rw [hnd]; rfl
        have hw : ls.work =
            RegaTask0.mk 0 e cur.venv cur.lenv
              (releaseArg0 esc st0.vslot cur.venv ⟨st0.remUses, cur.freeSlots⟩ c).free
              cur.nextSlot ::
            RegaTask0.mk ctrl.nextLbl t cur.venv cur.lenv
              (releaseArg0 esc st0.vslot cur.venv ⟨st0.remUses, cur.freeSlots⟩ c).free
              cur.nextSlot :: rest := by
          dsimp only [ls, regaStep0]; rw [hnd]; rfl
        have hnin_rest : ctrl.nextLbl ∉ rest.filterMap fun x =>
            if x.lblId = 0 then none else some x.lblId := fun hm => by
          obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.mp hm
          split at hqe
          · contradiction
          · rename_i hqnz
            simp only [Option.some.injEq] at hqe
            have := (hrest_bnd q hq hqnz).2; rw [hqe] at this; omega
        have hr : LabOk0 (fun l => ∃ j : UInt32, 1 ≤ j.toNat ∧ j.toNat < ctrl.nextLbl.toNat ∧
            l = .loc fnIdx j ∧ ∀ q ∈ rest, q.lblId ≠ 0 → j ≠ q.lblId) ls.st.revDirs := by
          dsimp only [ls, regaStep0]; rw [hnd]
          dsimp only [stepJnzPush0, jnzBuildSt0, jnzWrapRes0, jnzPrep0]
          exact labOk0_cons_nonLab (fun _ hc => by cases hc)
            (labOk0_pushDRR0 _ _ _ _ (labOk0_emitLoadArg0 _ c _ _ hst0_lab))
        refine finish_ls (by rw [hc]; exact hfn)
          ⟨by rw [hc, hadd1]; omega,
           by rw [hw]; simp only [List.filterMap_cons, ↓reduceIte, hnz_lbl,
                List.nodup_cons]; exact ⟨hnin_rest, hrest_nodup⟩,
           fun q hq hqz => by
             rw [hw] at hq
             rcases List.mem_cons.mp hq with rfl | hq1
             · simp at hqz
             · rcases List.mem_cons.mp hq1 with rfl | hq2
               · rw [hc, hadd1]; dsimp only; exact ⟨hpos_nl, by omega⟩
               · have := hrest_bnd q hq2 hqz; rw [hc, hadd1]; exact ⟨this.1, by omega⟩,
           fun q hq => by
             rw [hw] at hq
             rcases List.mem_cons.mp hq with rfl | hq1
             · exact hcur_sbg.2
             · rcases List.mem_cons.mp hq1 with rfl | hq2
               · exact hcur_sbg.1
               · exact hrest_sbg q hq2,
           by
             have := hwk.2.2.2.2
             rw [List.map_cons, hnd] at this; dsimp only [workNodeCount0, nodeCount0] at this
             rw [hc, hadd1, hw, List.map_cons, List.map_cons]
             dsimp only [workNodeCount0]
             omega⟩
          (by rw [hc, hw]
              rw [hw] at hcnt
              dsimp only
              rw [hadd1]
              simp only [List.map_cons] at hcnt ⊢
              dsimp only [workNodeCount0] at hcnt ⊢
              omega) ?_
        rw [hc, hadd1, hw]
        refine labOk0_mono hr ?_
        rintro l ⟨j, h1, h2, rfl, hnex⟩
        refine ⟨j, h1, by omega, rfl, fun q hq hqz => ?_⟩
        rcases List.mem_cons.mp hq with rfl | hq1
        · simp at hqz
        · rcases List.mem_cons.mp hq1 with rfl | hq2
          · dsimp only; exact fun he => by rw [he] at h2; omega
          · exact hnex q hq2 hqz
      | group bodies k =>
        rw [hnd] at hcur_sbg
        dsimp only [TFlat0.singleBlockGroups] at hcur_sbg
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcur_sbg
        rcases hcur_sbg with ⟨⟨hlen_b, hb_sbg⟩, hk_sbg⟩
        have hlt_gp : ctrl.nextLbl.toNat + bodies.length < 2 ^ 31 := by
          have := hwk.2.2.2.2
          have := blocksNodeCount0_ge_len bodies
          rw [List.map_cons, hnd] at *; dsimp only [workNodeCount0, nodeCount0] at *
          omega
        have hgp := regaPrepGroup0_labs bodies cur.venv ⟨cur.lenv, st0, ctrl, cur.freeSlots,
          cur.nextSlot, []⟩ hlt_gp hwk.1 (fun _ hm => nomatch hm) List.nodup_nil
        dsimp only at hgp
        let gp := regaPrepGroup0 bodies cur.venv
          ⟨cur.lenv, st0, ctrl, cur.freeSlots, cur.nextSlot, []⟩
        have hc : ls.ctrl = gp.ctrl := by
          dsimp only [ls, regaStep0]; rw [hnd]; rfl
        have hs_rev : ls.st.revDirs = st0.revDirs := by
          dsimp only [ls, regaStep0]; rw [hnd]
          dsimp only [stepGroupFinish0, stepGroupPrep0]
          exact hgp.2.2.1
        have hw_cases : bodies = [] ∨ ∃ pts b, bodies = [(pts, b)] := by
          cases bodies with
          | nil => exact Or.inl rfl
          | cons p restB =>
            cases restB with
            | nil => exact Or.inr ⟨p.1, p.2, rfl⟩
            | cons _ _ => simp at hlen_b
        rcases hw_cases with rfl | ⟨pts, b, rfl⟩
        · have hgp0 : gp = ⟨cur.lenv, st0, ctrl, cur.freeSlots, cur.nextSlot, []⟩ := rfl
          have hw : ls.work = RegaTask0.mk 0 k cur.venv cur.lenv cur.freeSlots cur.nextSlot ::
              rest := by
            dsimp only [ls, regaStep0]; rw [hnd]; rfl
          have hce : ls.ctrl = ctrl := hc.trans (by rw [hgp0])
          refine finish_ls (hce ▸ hfn) ⟨hce ▸ hwk.1,
            by rw [hw]; simp only [List.filterMap_cons, ↓reduceIte]; exact hrest_nodup,
            fun t ht htz => by
              rw [hw] at ht
              rcases List.mem_cons.mp ht with rfl | ht'
              · simp at htz
              · exact hce ▸ hrest_bnd t ht' htz,
            fun t ht => by
              rw [hw] at ht
              rcases List.mem_cons.mp ht with rfl | ht'
              · exact hk_sbg
              · exact hrest_sbg t ht',
            by
              have := hwk.2.2.2.2
              rw [List.map_cons, hnd] at this
              dsimp only [workNodeCount0, nodeCount0, blocksNodeCount0] at this
              rw [hce, hw, List.map_cons]; dsimp only [workNodeCount0]; omega⟩
            (by rw [hce]; omega) ?_
          rw [hce, hw, hs_rev]
          refine labOk0_mono hst0_lab ?_
          rintro l ⟨j, h1, h2, rfl, hnex⟩
          refine ⟨j, h1, h2, rfl, fun t ht htz => ?_⟩
          rcases List.mem_cons.mp ht with rfl | ht'
          · simp at htz
          · exact hnex t ht' htz
        · dsimp only [blocksSingleBlockGroups] at hb_sbg; rw [Bool.and_true] at hb_sbg
          have hadd1 : (ctrl.nextLbl + 1).toNat = ctrl.nextLbl.toNat + 1 :=
            u32_add1_toNat5 (by simp only [List.length_singleton] at hlt_gp; omega)
          have hnz_lbl : ctrl.nextLbl ≠ 0 := fun hz => by
            have := hwk.1; simp [hz] at this
          have hnin_rest : ctrl.nextLbl ∉ rest.filterMap fun x =>
              if x.lblId = 0 then none else some x.lblId := fun hm => by
            obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.mp hm
            split at hqe
            · contradiction
            · rename_i hqnz
              simp only [Option.some.injEq] at hqe
              have := (hrest_bnd q hq hqnz).2; rw [hqe] at this; omega
          have hgp1 : ls.ctrl = CtrlSt0.mk ctrl.fnIdx (ctrl.nextLbl + 1)
              (ctrl.lblSlots.push
                (slotsOfVids0 (tyLenU0 pts 0)
                  (bindBlockParams0 pts cur.venv st0 cur.freeSlots cur.nextSlot).venv
                  (bindBlockParams0 pts cur.venv st0 cur.freeSlots cur.nextSlot).st.vslot [])) := by
            dsimp only [ls, regaStep0]; rw [hnd]
            dsimp only [stepGroupFinish0, stepGroupPrep0, regaPrepGroup0, prepOneBlock0,
              prepOneBind0, prepFinishBlock0, prepUpdCtrl0]
            try rfl
          have hw1 : ∃ tK tB, ls.work = tK :: tB :: rest ∧
              tK.lblId = 0 ∧ tK.node = k ∧
              tB.lblId = ctrl.nextLbl ∧ tB.node = b := by
            dsimp only [ls, regaStep0]; rw [hnd]
            exact ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩
          obtain ⟨tK, tB, hw, htKz, htKn, htBl, htBn⟩ := hw1
          refine finish_ls (by rw [hgp1]; exact hfn)
            ⟨by rw [hgp1, hadd1]; omega,
             by rw [hw]; simp only [List.filterMap_cons, ↓reduceIte, htKz, htBl, hnz_lbl,
                  List.nodup_cons]; exact ⟨hnin_rest, hrest_nodup⟩,
             fun q hq hqz => by
               rw [hw] at hq
               rcases List.mem_cons.mp hq with rfl | hq1
               · exact absurd htKz hqz
               · rcases List.mem_cons.mp hq1 with rfl | hq2
                 · rw [hgp1, hadd1, htBl]; exact ⟨hwk.1, by omega⟩
                 · have := hrest_bnd q hq2 hqz; rw [hgp1, hadd1]; exact ⟨this.1, by omega⟩,
             fun q hq => by
               rw [hw] at hq
               rcases List.mem_cons.mp hq with rfl | hq1
               · rw [htKn]; exact hk_sbg
               · rcases List.mem_cons.mp hq1 with rfl | hq2
                 · rw [htBn]; exact hb_sbg
                 · exact hrest_sbg q hq2,
             by
               have := hwk.2.2.2.2
               rw [List.map_cons, hnd] at this
               dsimp only [workNodeCount0, nodeCount0, blocksNodeCount0] at this
               rw [hgp1, hadd1, hw, List.map_cons, List.map_cons]
               dsimp only [workNodeCount0]
               rw [htKn, htBn]
               omega⟩
            (by rw [hgp1, hadd1, hw]
                rw [hw] at hcnt
                simp only [List.map_cons] at hcnt ⊢
                dsimp only [workNodeCount0] at hcnt ⊢
                rw [htKn, htBn] at hcnt ⊢
                omega) ?_
          rw [hgp1, hadd1, hw, hs_rev]
          refine labOk0_mono hst0_lab ?_
          rintro l ⟨j, h1, h2, rfl, hnex⟩
          refine ⟨j, h1, by omega, rfl, fun q hq hqz => ?_⟩
          rcases List.mem_cons.mp hq with rfl | hq1
          · exact absurd htKz hqz
          · rcases List.mem_cons.mp hq1 with rfl | hq2
            · rw [htBl]; exact fun he => by rw [he] at h2; omega
            · exact hnex q hq2 hqz

private theorem compileFnFinish0_rev_eq (fn : TFlatFn0) (r : RegaSt0) :
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

private theorem compileFn0_tail_labOk0 (fnIdx : UInt32) (fn : TFlatFn0) (r : RegaSt0)
    (nextLbl : UInt32) (hnl : nextLbl.toNat < 2 ^ 31)
    (hlab : LabOk0 (fun l => ∃ j : UInt32, 1 ≤ j.toNat ∧ j.toNat < nextLbl.toNat ∧
      l = .loc fnIdx j) r.revDirs) :
    let fSz := x64FrameSizeU0 r.maxSlots
    let body := (emitSpAdj0 true fSz []).reverse ++
      patchEpilogues0 fSz (revDirAux0 r.revDirs []) []
    LabOk0 (fun l => l = .sym fn.name ∨
      ∃ j : UInt32, 1 ≤ j.toNat ∧ j.toNat < 2 ^ 31 ∧ l = .loc fnIdx j)
      (.label (.sym fn.name) :: body) := by
  intro fSz body
  have hnl_sp : NoLab0 (emitSpAdj0 true fSz []) := noLab0_emitSpAdj0 true fSz noLab0_nil
  have hbody_lab : LabOk0 (fun l => ∃ j : UInt32, 1 ≤ j.toNat ∧ j.toNat < 2 ^ 31 ∧
      l = .loc fnIdx j) body := by
    refine labOk0_prepend_noLab (noLab0_reverse hnl_sp) ?_
    refine labOk0_patchEpilogues0 fSz ?_
    rw [revDirAux0_eq, List.append_nil]
    refine labOk0_reverse (labOk0_mono hlab ?_)
    rintro l ⟨j, h1, h2, rfl⟩
    exact ⟨j, h1, by omega, rfl⟩
  have hnin_sym : .label (.sym fn.name) ∉ body := fun hm => by
    obtain ⟨j, _, _, he⟩ := hbody_lab.2 (.sym fn.name) hm
    cases he
  exact labOk0_cons_label hnin_sym (labOk0_mono hbody_lab (fun _ h => Or.inr h)) (Or.inl rfl)

private theorem compileFn0_labOk0_aux (fnIdx : UInt32) (fn : TFlatFn0) (esc uses0 : Array Nat)
    (hsbg : fn.body.singleBlockGroups = true) (hbd : nodeCount0 fn.body < 2 ^ 30) :
    let cap := Nat.add 32 (tyLenU0 fn.as 0).toNat
    let lblArr0 : Array (List UInt32) := (Array.emptyWithCapacity cap).push []
    let rega0 := RegaSt0.mk 0 0 (Array.emptyWithCapacity cap) uses0 []
    let ctrl0 := CtrlSt0.mk fnIdx 1 lblArr0
    let bl := bindEntryArgs0 fn.as 0 [] rega0
    let initTask := RegaTask0.mk 0 fn.body bl.venv [] bl.free bl.nxt
    let regaOut := (regaRunAux0 0x7fffffff esc bl.st ctrl0 [initTask]).1
    let fSz := x64FrameSizeU0 regaOut.maxSlots
    let bodyFwd := patchEpilogues0 fSz (revDirAux0 regaOut.revDirs []) []
    let dirs := revDirAux0 (emitSpAdj0 true fSz [.label (.sym fn.name)]) bodyFwd
    dirs[0]? = some (.label (.sym fn.name)) ∧
    LabOk0 (fun l => l = .sym fn.name ∨
      ∃ j : UInt32, 1 ≤ j.toNat ∧ j.toNat < 2 ^ 31 ∧ l = .loc fnIdx j) dirs := by
  intro cap lblArr0 rega0 ctrl0 bl initTask regaOut fSz bodyFwd dirs
  dsimp only [dirs, bodyFwd, fSz]
  rw [compileFnFinish0_rev_eq fn regaOut]
  refine ⟨List.getElem?_cons_zero, ?_⟩
  have hbl_nl : NoLab0 bl.st.revDirs := noLab0_bindEntryArgs0 fn.as 0 [] rega0 noLab0_nil
  have hwk0 : WorkLabInv0 ctrl0.nextLbl [initTask] := by
    refine ⟨by simp [ctrl0], by simp [initTask],
      fun t ht htz => by
        simp only [List.mem_singleton] at ht; subst ht; exact absurd rfl htz,
      fun t ht => by
        simp only [List.mem_singleton] at ht; subst ht; exact hsbg,
      by dsimp only [ctrl0, initTask]; rw [List.map_singleton]; dsimp only [workNodeCount0]
         rw [UInt32.toNat_one]; omega⟩
  have hrun := regaRunAux0_labInv fnIdx (nodeCount0 fn.body) 0x7fffffff esc bl.st
    ctrl0 [initTask]
    (by dsimp only [initTask]; rw [List.map_singleton]
        dsimp only [workNodeCount0]; exact Nat.add_zero _)
    (by change nodeCount0 fn.body ≤ 2147483647; omega) rfl hwk0 (labOk0_clean hbl_nl)
  dsimp only at hrun
  exact compileFn0_tail_labOk0 fnIdx fn regaOut _ (by
    have h1 : ctrl0.nextLbl.toNat = 1 := rfl
    have := hrun.2.1
    omega) hrun.2.2.2

theorem compileFn0_labOk0 (fnIdx : UInt32) (fn : TFlatFn0) (hg : fn.okGuardsFull = true) :
    let dirs := (compileFn0 fnIdx fn).1
    dirs[0]? = some (.label (.sym fn.name)) ∧
    LabOk0 (fun l => l = .sym fn.name ∨
      ∃ j : UInt32, 1 ≤ j.toNat ∧ j.toNat < 2 ^ 31 ∧ l = .loc fnIdx j) dirs := by
  have hsbg := TFlatFn0.okGuardsFull_singleBlock hg
  have hbd := TFlatFn0.okGuardsFull_boundsFitU32 hg
  simp only [TFlatFn0.boundsFitU32, Bool.and_eq_true, decide_eq_true_eq] at hbd
  dsimp only [compileFn0, compileFnFinish0]
  rw [← regaRunAux0_fst_eq_regaWorkLoop0]
  exact compileFn0_labOk0_aux fnIdx fn (compileFnPre0 fn).escaped (compileFnPre0 fn).uses
    hsbg hbd.1.2

end LeanQbe.T.Bootstrap0
