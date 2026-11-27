module

public import LeanQbe.T.LeanLCNF.LcnfC0Strings
public import LeanQbe.T.LeanLCNF.LcnfC0StringsSpec
public import LeanQbe.T.LeanLCNF.LcnfC0StringsProof1
public import LeanQbe.T.LeanLCNF.LcnfC0StringsProof2
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof1
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof2
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof3
import all Kraken.Separation

/-!
# Soundness Proofs for `LcnfC0Strings`, Part 2b: `lcnf_string_pos_op`

Proves `Func.wp rtR2bEnv` for the exported position/slice helper `lcnf_string_pos_op`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil

local macro "r2b_steps" : tactic => `(tactic| (try change LeanQbe.T.wp _ _ _ _ _; c0_steps))
local elab "r2b_to_group" : tactic => do
  let _ ← Lean.Elab.Tactic.tryTactic
    (Lean.Elab.Tactic.evalTactic (← `(tactic| change LeanQbe.T.wp _ _ _ _ _)))
  for _ in [:200] do
    let st0 ← Lean.Elab.Tactic.saveState
    let isGrp ← Lean.Elab.Tactic.tryTactic <| Lean.Elab.Tactic.evalTactic
      (← `(tactic| refine LeanQbe.T.wp_unroll_group fun _ _ => ?_))
    if isGrp then
      st0.restore
      break
    let gs0 ← Lean.Elab.Tactic.getGoals
    let ok ← Lean.Elab.Tactic.tryTactic (Lean.Elab.Tactic.evalTactic (← `(tactic| c0_step)))
    if !ok then
      st0.restore
      break
    let gs1 ← Lean.Elab.Tactic.getGoals
    if gs1.length > gs0.length then
      st0.restore
      break
local macro "r2b_call" h:term : tactic =>
  `(tactic| (refine LeanQbe.T.wp_call_of_spec _ _ ($h ?_); try c0_let_simp))

theorem lcnf_string_pos_op_wp :
    ∀ xs m Q X,
      lcnfStringPosOpSpec xs m Q X → Func.wp rtR2bEnv lcnf_string_pos_op_body xs m Q X := by
  intro ⟨rt, op, s, idxV, endV, ⟨⟩⟩ m Q X
    ⟨st, sObj, objs, R, hsAddr, hcanon, hobj1, hwfObjs, hm, hPost⟩
  subst hsAddr
  dsimp only [Func.wp, lcnf_string_pos_op_body]
  change LeanQbe.T.wp _ _ _ _ _
  let bs := strPayload sObj
  have hszLt := str_payload_lt_max sObj hcanon
  have hsz64 : bs.length < 2 ^ 64 := by
    dsimp only [bs]; unfold strMaxCap at hszLt; exact Nat.lt_trans hszLt (by decide)
  have hszTo : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz64]
  have hsh1 : (idxV >>> BitVec.signExtend 64 1#32) = idxV >>> 1 := by
    rw [BitVec.ushiftRight_eq', show (BitVec.signExtend 64 1#32).toNat = 1 by decide]
  have hshEnd1 : (endV >>> BitVec.signExtend 64 1#32) = endV >>> 1 := by
    rw [BitVec.ushiftRight_eq', show (BitVec.signExtend 64 1#32).toNat = 1 by decide]
  have hmS : (lcnfObjMem sObj ⋆ (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R)) m := sep_cast hm (by ac_rfl)
  apply wp_load_of (str_load_sz hcanon hmS)
  r2b_to_group
  try rw [str_sz_sub1_eq sObj hcanon] at *
  by_cases hop0 : op = 0#64
  · subst hop0
    rw [ite_eq_left (Or.inl rfl)] at hPost
    simp only [show (0#64 : BitVec 64) ≠ 1#64 by decide, ite_false] at hPost
    obtain ⟨Rest, hmExp, _⟩ := strObj_expose_bytes hcanon hmS
    c0_step
    · r2b_to_group
      c0_step
      · have ha0 : (idxV &&& 1#64) = 0#64 := by
          rw [show (0 : BitVec 64) = 0#64 from rfl, show (1 : BitVec 64) = 1#64 from rfl] at hc
          exact hc
        r2b_steps
        have hsp := hPost m (sep_cast hm (by ac_rfl))
        simp only [strPosOpVal, ite_true, ite_eq_left ha0] at hsp
        exact hsp
      · have ha1 : (idxV &&& 1#64) ≠ 0#64 := by
          rw [show (0 : BitVec 64) = 0#64 from rfl, show (1 : BitVec 64) = 1#64 from rfl] at hc
          exact hc
        r2b_to_group
        c0_step
        · try rw [hsh1] at hc
          rw [Nat.mod_eq_of_lt hsz64] at hc
          dsimp only [bs] at hc
          r2b_steps
          have hsp := hPost m (sep_cast hm (by ac_rfl))
          simp only [strPosOpVal, ite_true, ite_eq_right ha1,
            ite_eq_right (Nat.not_lt_of_le hc)] at hsp
          exact hsp
        · try rw [hsh1] at hc
          rw [Nat.mod_eq_of_lt hsz64] at hc
          have hlt : (idxV >>> 1).toNat < bs.length := Nat.lt_of_not_le hc
          r2b_call rtR2bEnv_r2b_utf8_decode_cp
          dsimp only [r2bUtf8DecodeCpSpec, vals, Tup.map, Arg.val]
          refine ⟨bs, Rest, hszTo.symm, hmExp, ?_⟩
          dsimp only [bs] at hlt ⊢
          have hsp := hPost m (sep_cast hm (by ac_rfl))
          simp only [strPosOpVal, ite_true, ite_eq_right ha1, ite_eq_left hlt] at hsp
          exact hsp
    all_goals try
      (exfalso; rw [show (0 : BitVec 64) = 0#64 from rfl] at hc; exact hc rfl)
  · c0_step
    all_goals try
      (exfalso; rw [show (0 : BitVec 64) = 0#64 from rfl] at hc; exact hop0 hc)
    focus
      r2b_to_group
      by_cases hop1 : op = 1#64
      · subst hop1
        rw [ite_eq_left (Or.inr (Or.inl rfl))] at hPost
        simp only [ite_true] at hPost
        c0_step
        · r2b_to_group
          c0_step
          · have ha0 : (idxV &&& 1#64) = 0#64 := by
              rw [show (0 : BitVec 64) = 0#64 from rfl,
                show (1 : BitVec 64) = 1#64 from rfl] at hc
              exact hc
            by_cases h0 : idxV = 0#64
            · r2b_call rtR2bEnv_r2_inc_obj
              dsimp only [r2IncObjSpec, vals, Tup.map, Arg.val]
              rw [ite_eq_left (Or.inl h0)]
              r2b_steps
              have hinc0 : incObjList idxV objs = objs := by
                unfold incObjList; rw [ite_eq_left (Or.inl h0)]
              rw [hinc0] at hPost
              have hsp := hPost m (sep_cast hm (by ac_rfl))
              simp only [strPosOpVal, show (1#64 : BitVec 64) ≠ 0#64 by decide,
                ite_false, ite_true, ite_eq_left ha0] at hsp
              exact hsp
            · obtain ⟨iObj, hiMem, hiAddr, hiWf⟩ := hobj1 ⟨rfl, ha0, h0⟩
              obtain ⟨k, hkLen, hobjk⟩ := List.getElem_of_mem hiMem
              have hnd : (objs.map LcnfObj.addr).Nodup :=
                lcnfHeap_nodup_addrs (sep_cast hm (by ac_rfl) :
                  (lcnfHeap objs ⋆ (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ R)) m)
              have hfocus : lcnfHeap objs = lcnfObjMem iObj ⋆ lcnfHeap (objs.eraseIdx k) := by
                rw [lcnfHeap_focus objs hkLen, hobjk, ← lcnfHeap_eraseIdx objs]
              have hmI : (lcnfObjMem iObj ⋆ (lcnfHeap (objs.eraseIdx k) ⋆
                  rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆ R)) m := by
                rw [hfocus] at hm; exact sep_cast hm (by ac_rfl)
              r2b_call rtR2bEnv_r2_inc_obj
              dsimp only [r2IncObjSpec, vals, Tup.map, Arg.val]
              rw [ite_eq_right (by simp [h0, ha0])]
              refine ⟨iObj, _, hiAddr, hiWf, hmI, fun m1 hm1 => ?_⟩
              r2b_steps
              have hmInc : (rtC0Inv rt st ⋆ lcnfObjMem sObj ⋆
                  lcnfHeap (incObjList idxV objs) ⋆ R) m1 := by
                have hset : objs.set k (iObj.withRc (incRcVal iObj.rc)) =
                    objs.map (fun o =>
                      if o.addr = idxV then o.withRc (incRcVal o.rc) else o) := by
                  rw [list_set_eq_map_of_nodup hkLen (iObj.withRc (incRcVal iObj.rc)) hnd]
                  refine List.map_congr_left fun o ho => ?_
                  rw [hobjk, hiAddr]
                  split
                  · next heq =>
                    obtain ⟨ko, hko, hkoEq⟩ := List.getElem_of_mem ho
                    have hkEq : ko = k :=
                      nodup_map_getElem_eq LcnfObj.addr hnd hko hkLen
                        (by rw [hkoEq, hobjk, heq, hiAddr])
                    subst hkEq; rw [← hobjk, hkoEq]
                  · rfl
                have hinc : incObjList idxV objs =
                    objs.set k (iObj.withRc (incRcVal iObj.rc)) := by
                  unfold incObjList; rw [ite_eq_right (by simp [h0, ha0]), ← hset]
                have hfc : lcnfHeap (objs.set k (iObj.withRc (incRcVal iObj.rc))) =
                    lcnfObjMem (iObj.withRc (incRcVal iObj.rc)) ⋆
                      lcnfHeap (objs.eraseIdx k) := by
                  rw [lcnfHeap_focus (objs.set k _) (by rw [List.length_set]; exact hkLen),
                    List.getElem_set_self, ← lcnfHeap_eraseIdx (objs.set k _),
                    eraseIdx_set_eq_self]
                rw [hinc, hfc]
                exact sep_cast hm1 (by ac_rfl)
              have hsp := hPost m1 hmInc
              simp only [strPosOpVal, show (1#64 : BitVec 64) ≠ 0#64 by decide,
                ite_false, ite_true, ite_eq_left ha0] at hsp
              exact hsp
          · have ha1 : (idxV &&& 1#64) ≠ 0#64 := by
              rw [show (0 : BitVec 64) = 0#64 from rfl,
                show (1 : BitVec 64) = 1#64 from rfl] at hc
              exact hc
            have hincId : incObjList idxV objs = objs := by
              unfold incObjList; rw [ite_eq_left (Or.inr ha1)]
            rw [hincId] at hPost
            r2b_to_group
            c0_step
            · try rw [hsh1] at hc
              rw [Nat.mod_eq_of_lt hsz64] at hc
              r2b_steps
              dsimp only [bs] at hc
              have hsp := hPost m (sep_cast hm (by ac_rfl))
              simp only [strPosOpVal, show (1#64 : BitVec 64) ≠ 0#64 by decide,
                ite_false, ite_true, ite_eq_right ha1,
                ite_eq_right (Nat.not_lt_of_le hc)] at hsp
              exact hsp
            · try rw [hsh1] at hc
              rw [Nat.mod_eq_of_lt hsz64] at hc
              have hlt : (idxV >>> 1).toNat < bs.length := Nat.lt_of_not_le hc
              obtain ⟨Rest, hmExp, _⟩ := strObj_expose_bytes hcanon hmS
              r2b_call rtR2bEnv_r2b_utf8_decode_step
              dsimp only [r2bUtf8DecodeStepSpec, vals, Tup.map, Arg.val]
              refine ⟨bs, Rest, hszTo.symm, hmExp, ?_⟩
              r2b_steps
              have hst := (utf8DecodeStepAt_pos hlt).2
              have hidxLt : (idxV >>> 1).toNat < 2 ^ 64 := (idxV >>> 1).isLt
              have hstLt : utf8DecodeStepAt bs (idxV >>> 1).toNat < 2 ^ 64 :=
                Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) hst) hsz64
              have hsumLt :
                  (idxV >>> 1).toNat + utf8DecodeStepAt bs (idxV >>> 1).toNat < 2 ^ 64 :=
                Nat.lt_of_le_of_lt hst hsz64
              have hbox :
                  ((((idxV >>> 1) + BitVec.ofNat 64 (utf8DecodeStepAt bs (idxV >>> 1).toNat)) <<<
                      BitVec.signExtend 64 1#32) ||| 1#64) =
                    ((BitVec.ofNat 64 ((idxV >>> 1).toNat +
                      utf8DecodeStepAt bs (idxV >>> 1).toNat)) <<< 1) ||| 1#64 := by
                rw [BitVec.shiftLeft_eq', show (BitVec.signExtend 64 1#32).toNat = 1 by decide]
                apply BitVec.eq_of_toNat_eq
                simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_add,
                  BitVec.toNat_ofNat, Nat.mod_eq_of_lt hstLt, Nat.mod_eq_of_lt hsumLt]
              dsimp only [bs] at hlt hbox ⊢
              have hsp := hPost m (sep_cast hm (by ac_rfl))
              simp only [strPosOpVal, show (1#64 : BitVec 64) ≠ 0#64 by decide,
                ite_false, ite_true, ite_eq_right ha1, ite_eq_left hlt] at hsp
              rw [show (BitVec.signExtend 64 1#32) = 1#64 from rfl,
                show (1 : BitVec 64) = 1#64 from rfl] at *
              rw [← hbox] at hsp
              exact hsp
        all_goals try
          (exfalso; rw [show (1 : BitVec 64) = 1#64 from rfl] at hc; exact hc rfl)
      · c0_step
        all_goals try
          (exfalso; rw [show (1 : BitVec 64) = 1#64 from rfl] at hc; exact hop1 hc)
        focus
          r2b_to_group
          by_cases hop2 : op = 2#64
          · subst hop2
            rw [ite_eq_left (Or.inr (Or.inr (Or.inl rfl)))] at hPost
            simp only [show (2#64 : BitVec 64) ≠ 1#64 by decide, ite_false] at hPost
            c0_step
            · r2b_to_group
              c0_step
              · have ha0 : (idxV &&& 1#64) = 0#64 := by
                  rw [show (0 : BitVec 64) = 0#64 from rfl,
                    show (1 : BitVec 64) = 1#64 from rfl] at hc
                  exact hc
                r2b_steps
                have hsp := hPost m (sep_cast hm (by ac_rfl))
                simp only [strPosOpVal, show (2#64 : BitVec 64) ≠ 0#64 by decide,
                  show (2#64 : BitVec 64) ≠ 1#64 by decide, ite_false, ite_true,
                  ite_eq_left ha0] at hsp
                exact hsp
              · have ha1 : (idxV &&& 1#64) ≠ 0#64 := by
                  rw [show (0 : BitVec 64) = 0#64 from rfl,
                    show (1 : BitVec 64) = 1#64 from rfl] at hc
                  exact hc
                r2b_to_group
                c0_step
                · try rw [hsh1] at hc
                  rw [Nat.mod_eq_of_lt hsz64] at hc
                  dsimp only [bs] at hc
                  r2b_steps
                  have hsp := hPost m (sep_cast hm (by ac_rfl))
                  simp only [strPosOpVal, show (2#64 : BitVec 64) ≠ 0#64 by decide,
                    show (2#64 : BitVec 64) ≠ 1#64 by decide, ite_false, ite_true,
                    ite_eq_right ha1, ite_eq_right (Nat.not_lt_of_le hc)] at hsp
                  exact hsp
                · try rw [hsh1] at hc
                  rw [Nat.mod_eq_of_lt hsz64] at hc
                  have hlt : (idxV >>> 1).toNat < bs.length := Nat.lt_of_not_le hc
                  r2b_steps
                  dsimp only [bs] at hlt
                  have hsp := hPost m (sep_cast hm (by ac_rfl))
                  simp only [strPosOpVal, show (2#64 : BitVec 64) ≠ 0#64 by decide,
                    show (2#64 : BitVec 64) ≠ 1#64 by decide, ite_false, ite_true,
                    ite_eq_right ha1, ite_eq_left hlt] at hsp
                  exact hsp
            all_goals try
              (exfalso; rw [show (2 : BitVec 64) = 2#64 from rfl] at hc; exact hc rfl)
          · c0_step
            all_goals try
              (exfalso; rw [show (2 : BitVec 64) = 2#64 from rfl] at hc; exact hop2 hc)
            focus
              r2b_to_group
              by_cases hop3 : op = 3#64
              · subst hop3
                rw [ite_eq_right (by simp [hop0, hop1, hop2]), ite_eq_left rfl] at hPost
                rcases hPost with ⟨hav, hpostK⟩
                let b := strPosClamp idxV bs.length
                let e := strPosClamp endV bs.length
                have hbLe : b ≤ bs.length := by
                  dsimp only [b, strPosClamp]
                  split <;> first | exact Nat.min_le_right _ _ | exact Nat.le_refl _
                have heLe : e ≤ bs.length := by
                  dsimp only [e, strPosClamp]
                  split <;> first | exact Nat.min_le_right _ _ | exact Nat.le_refl _
                have hb64 : b < 2 ^ 64 := Nat.lt_of_le_of_lt hbLe hsz64
                have he64 : e < 2 ^ 64 := Nat.lt_of_le_of_lt heLe hsz64
                have hbTo : (BitVec.ofNat 64 b).toNat = b := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64]
                have heTo : (BitVec.ofNat 64 e).toNat = e := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64]
                rw [show (3#64 == (3 : BitVec 64)) = true from rfl]
                apply r2b_wp_jnz_true
                focus
                  r2b_to_group
                  refine wp_join_group
                    (P := fun (xs : Tup Val [i64]) m1 => match xs with
                      | (bv, PUnit.unit) => m1 = m ∧ bv = BitVec.ofNat 64 b) ?_ ?_
                  · intro _ ⟨bv, ⟨⟩⟩ m1 ⟨hm1Eq, hbv⟩
                    subst hbv; cases hm1Eq
                    change LeanQbe.T.wp _ _ _ _ _
                    r2b_to_group
                    refine wp_join_group
                      (P := fun (xs : Tup Val [i64]) m2 => match xs with
                        | (ev, PUnit.unit) => m2 = m ∧ ev = BitVec.ofNat 64 e) ?_ ?_
                    · intro _ ⟨ev, ⟨⟩⟩ m2 ⟨hm2Eq, hev⟩
                      subst hev; cases hm2Eq
                      change LeanQbe.T.wp _ _ _ _ _
                      by_cases hbe : b < e
                      · have hnotGe : ¬ e ≤ b := Nat.not_le_of_lt hbe
                        let newSz := e - b
                        have hnewLt : newSz < strMaxCap :=
                          Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_le_of_lt heLe hszLt)
                        have hnew64 : newSz < 2 ^ 64 := by
                          unfold strMaxCap at hnewLt; exact Nat.lt_trans hnewLt (by decide)
                        have hnew1LeMax : newSz + 1 ≤ strMaxCap := Nat.succ_le_of_lt hnewLt
                        have hnew164 : newSz + 1 < 2 ^ 64 :=
                          Nat.lt_of_le_of_lt hnew1LeMax (by unfold strMaxCap; decide)
                        have hnewSub : BitVec.ofNat 64 e - BitVec.ofNat 64 b =
                            BitVec.ofNat 64 newSz := by
                          apply BitVec.eq_of_toNat_eq
                          rw [str_sub_mod_lt e b he64 (Nat.le_of_lt hbe), BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt hnew64]
                        have hnewTo : (BitVec.ofNat 64 newSz).toNat = newSz := by
                          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnew64]
                        have hnew1To : (BitVec.ofNat 64 newSz + 1#64).toNat = newSz + 1 := by
                          rw [bv_ofNat_add1_mod64 newSz hnew64, BitVec.toNat_ofNat, Nat.mod_mod,
                            Nat.mod_eq_of_lt hnew164]
                        have hsubEq : (bs.take e).drop b =
                            if b < e then (bs.take e).drop b else [] := (ite_eq_left hbe).symm
                        have hsubLen : ((bs.take e).drop b).length = newSz := by
                          simp [List.length_drop, List.length_take, Nat.min_eq_left heLe, newSz]
                        have hlenEq : utf8CountFrom (bs.take e) b =
                            if b < e then utf8CountFrom (bs.take e) b else 0 :=
                          (ite_eq_left hbe).symm
                        have htakeLen : (bs.take e).length = e := by
                          rw [List.length_take, Nat.min_eq_left heLe]
                        obtain ⟨Rest, hmExp, _⟩ := strObj_expose_bytes hcanon hmS
                        have hspE : bs = bs.take e ++ bs.drop e := (List.take_append_drop e bs).symm
                        have hlenSum : (bs.take e).length + (bs.drop e).length ≤ 2 ^ 64 := by
                          rw [← List.length_append, ← hspE]; exact Nat.le_of_lt hsz64
                        have happE := bytes_append (sObj.addr + 32#64) (bs.take e) (bs.drop e)
                          hlenSum
                        have hmSubE : (bytes (sObj.addr + 32#64) (bs.take e) ⋆
                            (bytes (sObj.addr + 32#64 + BitVec.ofNat 64 e) (bs.drop e) ⋆
                              Rest)) m := by
                          have hmE0 : (bytes (sObj.addr + 32#64) (bs.take e ++ bs.drop e) ⋆
                              Rest) m := by
                            dsimp only [bs] at hspE hmExp ⊢; rw [← hspE]; exact hmExp
                          rw [happE, htakeLen] at hmE0
                          exact sep_cast hmE0 (by ac_rfl)
                        r2b_to_group
                        focus
                          refine wp_loop_inv
                            (fun (xs : Tup Val [i64, i64]) mL =>
                              mL = m ∧ ∃ posN : Nat, b ≤ posN ∧ posN ≤ e ∧
                                xs.2.1 = BitVec.ofNat 64 posN ∧
                                xs.1.toNat + utf8CountFrom (bs.take e) posN =
                                  utf8CountFrom (bs.take e) b ∧
                                xs.1.toNat + (e - posN) ≤ e)
                            (fun (xs : Tup Val [i64, i64]) _ => e - xs.2.1.toNat) ?_ ?_
                          · intro Jlp hJlp
                            change LeanQbe.T.wp _ _ _ _ _
                            c0_steps
                            exact hJlp (0#64, BitVec.ofNat 64 b, ()) m
                              ⟨rfl, b, Nat.le_refl _, Nat.le_of_lt hbe, rfl,
                                by simp only [show (0#64 : BitVec 64).toNat = 0 from rfl,
                                  Nat.zero_add],
                                by simp only [show (0#64 : BitVec 64).toNat = 0 from rfl,
                                     Nat.zero_add]; exact Nat.sub_le _ _⟩
                          · intro Jlp ⟨nlen, pos, ⟨⟩⟩ mL
                              ⟨hmL, posN, hbp, hpe, hposEq, hcntEq, hbnd⟩ hRec
                            cases hmL
                            dsimp only at hposEq hcntEq hbnd
                            subst hposEq
                            have hpos64 : posN < 2 ^ 64 := Nat.lt_of_le_of_lt hpe he64
                            have hposTo : (BitVec.ofNat 64 posN).toNat = posN := by
                              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpos64]
                            r2b_to_group
                            c0_step
                            · rw [Nat.mod_eq_of_lt hpos64, Nat.mod_eq_of_lt he64] at hc
                              have hltTake : posN < (bs.take e).length := by
                                rw [htakeLen]; exact hc
                              have hstepPos := utf8DecodeStepAt_pos hltTake
                              rw [htakeLen] at hstepPos
                              have hnlenLt : nlen.toNat + 1 < 2 ^ 64 := by
                                have : nlen.toNat + 1 ≤ e + 1 := by omega
                                exact Nat.lt_of_le_of_lt this
                                  (Nat.lt_of_le_of_lt
                                    (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt heLe hszLt))
                                    (by unfold strMaxCap; decide))
                              have hnlen1 : (nlen + 1#64).toNat = nlen.toNat + 1 := by
                                rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
                                  Nat.mod_eq_of_lt hnlenLt]
                              r2b_call rtR2bEnv_r2b_utf8_decode_step
                              dsimp only [r2bUtf8DecodeStepSpec, vals, Tup.map, Arg.val]
                              refine ⟨bs.take e,
                                bytes (sObj.addr + 32#64 + BitVec.ofNat 64 e) (bs.drop e) ⋆ Rest,
                                by rw [htakeLen, heTo], hmSubE, ?_⟩
                              r2b_steps
                              have hposNext : posN + utf8DecodeStepAt (bs.take e) posN ≤ e :=
                                hstepPos.2
                              have hposAdd : BitVec.ofNat 64 posN +
                                  BitVec.ofNat 64 (utf8DecodeStepAt (bs.take e) posN) =
                                  BitVec.ofNat 64 (posN + utf8DecodeStepAt (bs.take e) posN) :=
                                (BitVec.ofNat_add _ _).symm
                              have hposNextTo :
                                  (BitVec.ofNat 64
                                    (posN + utf8DecodeStepAt (bs.take e) posN)).toNat =
                                    posN + utf8DecodeStepAt (bs.take e) posN := by
                                rw [BitVec.toNat_ofNat,
                                  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hposNext he64)]
                              have hstepCnt := utf8CountFrom_step hltTake
                              apply hRec
                              · dsimp only; rw [hposTo, hposAdd, hposNextTo]
                                have := hstepPos.1; omega
                              · refine ⟨rfl, posN + utf8DecodeStepAt (bs.take e) posN,
                                  Nat.le_trans hbp (Nat.le_add_right _ _), hposNext,
                                  by rw [hposTo]; exact hposAdd, ?_, ?_⟩
                                · dsimp only
                                  rw [hstepCnt] at hcntEq
                                  rw [show (1 : BitVec 64) = 1#64 from rfl, hnlen1]
                                  omega
                                · dsimp only
                                  rw [show (1 : BitVec 64) = 1#64 from rfl, hnlen1]
                                  have := hstepPos.1; omega
                            · rw [Nat.mod_eq_of_lt hpos64, Nat.mod_eq_of_lt he64] at hc
                              have hposE : posN = e := Nat.le_antisymm hpe (Nat.not_lt.mp hc)
                              subst hposE
                              have hcnt0 : utf8CountFrom (bs.take e) e = 0 := by
                                apply utf8CountFrom_end; rw [htakeLen]; exact Nat.lt_irrefl _
                              rw [hcnt0, Nat.add_zero] at hcntEq
                              have hnlenBv :
                                  nlen = BitVec.ofNat 64 (utf8CountFrom (bs.take e) b) := by
                                apply BitVec.eq_of_toNat_eq
                                rw [← hcntEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt nlen.isLt]
                              r2b_call rtR2bEnv_r2b_str_alloc_cap
                              dsimp only [r2bStrAllocCapSpec, vals, Tup.map, Arg.val]
                              have hvalid : newSz < strMaxCap ∧ newSz < newSz + 1 ∧
                                  newSz + 1 ≤ strMaxCap :=
                                ⟨hnewLt, Nat.lt_succ_self _, hnew1LeMax⟩
                              rw [show (1 : BitVec 64) = 1#64 from rfl,
                                hnewSub, hnewTo, hnew1To, ite_eq_left hvalid]
                              have hav' : st.hasFree (strAllocBytes (newSz + 1)) ∨
                                  strAllocBytes (newSz + 1) ≤ st.rem := by
                                have hbDef : strPosClamp idxV bs.length = b := rfl
                                have heDef : strPosClamp endV bs.length = e := rfl
                                rw [show strPayload sObj = bs from rfl] at hav
                                simp only [hbDef, heDef, hbe, ↓reduceIte, hsubLen] at hav
                                exact hav
                              refine ⟨st, lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R, hav',
                                sep_cast hm (by ac_rfl),
                                fun dst st1 m1 hdst0 hdst8 hpr1 hrem1 _ hm1 => ?_⟩
                              rw [bv_ofNat_add1_mod64 newSz hnew64,
                                Nat.mod_eq_of_lt hnew164] at hm1
                              r2b_steps
                              have hmS1 : (lcnfObjMem sObj ⋆
                                  (region (dst + 32#64) newSz ⋆
                                    rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
                                    cell64 (dst + 8#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
                                    cell64 (dst + 16#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
                                    cell64 (dst + 24#64) nlen ⋆
                                    bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
                                    region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                                      (strAllocBytes (newSz + 1) - (32 + newSz + 1)) ⋆
                                    lcnfHeap objs ⋆ R)) m1 := sep_cast hm1 (by ac_rfl)
                              rw [strObj_eq_bytes_rest hcanon] at hmS1
                              let sub := (bs.take e).drop b
                              have hspSub : bs = bs.take b ++ sub ++ bs.drop e := by
                                dsimp only [sub]
                                have h1 : (bs.take e).take b = bs.take b := by
                                  rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hbe)]
                                conv => lhs; rw [← List.take_append_drop e bs,
                                  ← List.take_append_drop b (bs.take e), h1]
                              have htakeB : (bs.take b).length = b := by
                                rw [List.length_take, Nat.min_eq_left hbLe]
                              have hspSum :
                                  (bs.take b).length + (sub ++ bs.drop e).length ≤ 2 ^ 64 := by
                                rw [← List.length_append, ← List.append_assoc, ← hspSub]
                                exact Nat.le_of_lt hsz64
                              have hsubDropSum : sub.length + (bs.drop e).length ≤ 2 ^ 64 := by
                                have hle := Nat.le_add_left (sub ++ bs.drop e).length
                                  (bs.take b).length
                                rw [← List.length_append, ← List.append_assoc, ← hspSub] at hle
                                rw [List.length_append] at hle
                                exact Nat.le_trans hle (Nat.le_of_lt hsz64)
                              have happ1 := bytes_append (sObj.addr + 32#64) (bs.take b)
                                (sub ++ bs.drop e) hspSum
                              have happ2 := bytes_append (sObj.addr + 32#64 + BitVec.ofNat 64 b) sub
                                (bs.drop e) hsubDropSum
                              let restOuter :=
                                bytes (sObj.addr + 32#64) (bs.take b) ⋆
                                  bytes (sObj.addr + 32#64 + BitVec.ofNat 64 b +
                                    BitVec.ofNat 64 newSz) (bs.drop e) ⋆
                                  strRest sObj ⋆ rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
                                  cell64 (dst + 8#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
                                  cell64 (dst + 16#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
                                  cell64 (dst + 24#64) nlen ⋆
                                  bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
                                  region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                                    (strAllocBytes (newSz + 1) - (32 + newSz + 1)) ⋆
                                  lcnfHeap objs ⋆ R
                              have hmSplit : (bytes (sObj.addr + 32#64 + BitVec.ofNat 64 b) sub ⋆
                                  region (dst + 32#64) newSz ⋆ restOuter) m1 := by
                                dsimp only [bs] at hmS1 hspSub ⊢
                                have hmA : (bytes (sObj.addr + 32#64)
                                    (bs.take b ++ (sub ++ bs.drop e)) ⋆
                                    (strRest sObj ⋆ region (dst + 32#64) newSz ⋆
                                      rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
                                      cell64 (dst + 8#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
                                      cell64 (dst + 16#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
                                      cell64 (dst + 24#64) nlen ⋆
                                      bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
                                      region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                                        (strAllocBytes (newSz + 1) - (32 + newSz + 1)) ⋆
                                      lcnfHeap objs ⋆ R)) m1 := by
                                  rw [← List.append_assoc, ← hspSub]
                                  exact sep_cast hmS1 (by ac_rfl)
                                rw [happ1, htakeB, happ2, hsubLen] at hmA
                                dsimp only [restOuter]
                                exact sep_cast hmA (by ac_rfl)
                              r2b_call rtR2bEnv_r2_mem_copy_bytes
                              dsimp only [r2MemCopyBytesSpec, vals, Tup.map, Arg.val]
                              try rw [hnewSub]
                              try simp only [show (32 : BitVec 64) = 32#64 from rfl]
                              refine ⟨sub, newSz, restOuter,
                                by rw [hnewTo]; exact hsubLen,
                                by rw [hnewTo]; exact Nat.le_refl _,
                                Nat.le_of_lt hnew64, hmSplit, fun m2 hm2 => ?_⟩
                              rw [hnewTo, Nat.sub_self, region_zero] at hm2
                              try simp only [emp_sep] at hm2
                              try simp only [sep_emp] at hm2
                              dsimp only [restOuter] at hm2
                              have hmClosed : (lcnfObjMem sObj ⋆ bytes (dst + 32#64) sub ⋆
                                  rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
                                  cell64 (dst + 8#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
                                  cell64 (dst + 16#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
                                  cell64 (dst + 24#64) nlen ⋆
                                  bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
                                  region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                                    (strAllocBytes (newSz + 1) - (32 + newSz + 1)) ⋆
                                  lcnfHeap objs ⋆ R) m2 := by
                                rw [strObj_eq_bytes_rest hcanon]
                                dsimp only [bs] at hspSub ⊢
                                have hmJ0 : (bytes (sObj.addr + 32#64)
                                    (bs.take b ++ (sub ++ bs.drop e)) ⋆
                                    (strRest sObj ⋆ bytes (dst + 32#64) sub ⋆
                                      rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
                                      cell64 (dst + 8#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
                                      cell64 (dst + 16#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
                                      cell64 (dst + 24#64) nlen ⋆
                                      bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
                                      region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                                        (strAllocBytes (newSz + 1) - (32 + newSz + 1)) ⋆
                                      lcnfHeap objs ⋆ R)) m2 := by
                                  rw [happ1, htakeB, happ2, hsubLen]
                                  exact sep_cast hm2 (by ac_rfl)
                                rw [← List.append_assoc, ← hspSub] at hmJ0
                                exact sep_cast hmJ0 (by ac_rfl)
                              r2b_steps
                              let rObj := mkStrObj dst 1#32 (sub.length + 1) sub
                                (utf8CountFrom (bs.take e) b)
                              have hsubMax : sub.length + 1 ≤ strMaxCap := by
                                rw [hsubLen]; exact hnew1LeMax
                              have hcanR : StrCanon rObj :=
                                mkStrObj_canon hdst0 hdst8 (by decide) (Nat.le_refl _)
                                  hsubMax (hcntEq ▸ nlen.isLt)
                              have hmR : (rtC0Inv rt st1 ⋆ lcnfObjMem rObj ⋆ lcnfObjMem sObj ⋆
                                  lcnfHeap objs ⋆ R) m2 := by
                                have hparts : (cell64 dst strHeaderWord ⋆
                                    cell64 (dst + 8#64) (BitVec.ofNat 64 (sub.length + 1)) ⋆
                                    cell64 (dst + 16#64) (BitVec.ofNat 64 (sub.length + 1)) ⋆
                                    cell64 (dst + 24#64)
                                      (BitVec.ofNat 64 (utf8CountFrom (bs.take e) b)) ⋆
                                    bytes (dst + 32#64) sub ⋆
                                    bytes (dst + 32#64 + BitVec.ofNat 64 sub.length) [(0 : UInt8)] ⋆
                                    region (dst + 32#64 + BitVec.ofNat 64 sub.length + 1#64)
                                      (strAllocBytes (sub.length + 1) - (32 + sub.length + 1)) ⋆
                                    (rtC0Inv rt st1 ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R)) m2 := by
                                  rw [hsubLen, ← hnlenBv]
                                  exact sep_cast hmClosed (by ac_rfl)
                                exact sep_cast (mkStrObj_mem_of_parts hsubMax
                                  (Nat.le_refl _) hparts) (by ac_rfl)
                              have hbDef : strPosClamp idxV bs.length = b := rfl
                              have heDef : strPosClamp endV bs.length = e := rfl
                              rw [show strPayload sObj = bs from rfl] at hpostK
                              simp only [hbDef, heDef, hbe, ↓reduceIte] at hpostK
                              exact hpostK dst st1 m2 hdst0 hdst8 hpr1 hrem1 hcanR hmR
                      · have hge : e ≤ b := Nat.not_lt.mp hbe
                        have hsubNil : (if b < e then (bs.take e).drop b else []) = [] :=
                          ite_eq_right hbe
                        have hlen0 : (if b < e then utf8CountFrom (bs.take e) b else 0) = 0 :=
                          ite_eq_right hbe
                        r2b_to_group
                        focus
                          r2b_call rtR2bEnv_r2b_str_alloc_cap
                          dsimp only [r2bStrAllocCapSpec, vals, Tup.map, Arg.val]
                          have hv : 0 < strMaxCap ∧ 0 < 1 ∧ 1 ≤ strMaxCap := by
                            unfold strMaxCap; decide
                          rw [show (0 : BitVec 64).toNat = 0 from rfl,
                            show (1 : BitVec 64).toNat = 1 from rfl, ite_eq_left hv]
                          refine ⟨st, lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R,
                            by
                              have hbDef : strPosClamp idxV bs.length = b := rfl
                              have heDef : strPosClamp endV bs.length = e := rfl
                              rw [show strPayload sObj = bs from rfl] at hav
                              simp only [hbDef, heDef, hbe, ↓reduceIte,
                                List.length_nil, Nat.zero_add] at hav
                              exact hav,
                            sep_cast hm (by ac_rfl), fun r st1 m1 hr0 hr8 hpr1 hrem1 _ hm1 => ?_⟩
                          r2b_steps
                          let rObj := mkStrObj r 1#32 1 [] 0
                          have hcanR : StrCanon rObj :=
                            mkStrObj_canon hr0 hr8 (by decide) (by decide)
                              (by unfold strMaxCap; decide) (by decide)
                          have hmR : (rtC0Inv rt st1 ⋆ lcnfObjMem rObj ⋆ lcnfObjMem sObj ⋆
                              lcnfHeap objs ⋆ R) m1 := by
                            have hparts : (cell64 r strHeaderWord ⋆
                                cell64 (r + 8#64) (BitVec.ofNat 64 (([] : List UInt8).length + 1)) ⋆
                                cell64 (r + 16#64) (BitVec.ofNat 64 1) ⋆
                                cell64 (r + 24#64) (BitVec.ofNat 64 0) ⋆
                                bytes (r + 32#64) [] ⋆
                                bytes (r + 32#64 + BitVec.ofNat 64 ([] : List UInt8).length)
                                  [(0 : UInt8)] ⋆
                                region (r + 32#64 + BitVec.ofNat 64 ([] : List UInt8).length + 1#64)
                                  (strAllocBytes 1 - (32 + ([] : List UInt8).length + 1)) ⋆
                                (rtC0Inv rt st1 ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R)) m1 := by
                              simp only [List.length_nil, Nat.zero_add,
                                show (0 : BitVec 64) = 0#64 from rfl,
                                show (1 : BitVec 64) = 1#64 from rfl,
                                show r + 32#64 + 0#64 = r + 32#64 from by simp,
                                bytes_nil_eq, region_zero] at hm1 ⊢
                              exact sep_cast hm1 (by ac_rfl)
                            exact sep_cast (mkStrObj_mem_of_parts (by unfold strMaxCap; decide)
                              (by decide) hparts) (by ac_rfl)
                          have hbDef : strPosClamp idxV bs.length = b := rfl
                          have heDef : strPosClamp endV bs.length = e := rfl
                          rw [show strPayload sObj = bs from rfl] at hpostK
                          simp only [hbDef, heDef, hbe, ↓reduceIte,
                            List.length_nil, Nat.zero_add] at hpostK
                          exact hpostK r st1 m1 hr0 hr8 hpr1 hrem1 hcanR hmR
                    · intro J2 hJ2
                      r2b_to_group
                      c0_step
                      · have ha1 : (endV &&& 1#64) ≠ 0#64 := by
                          rw [show (1 : BitVec 64) = 1#64 from rfl,
                            show (0 : BitVec 64) = 0#64 from rfl] at hc; exact hc
                        r2b_to_group
                        c0_step
                        r2b_to_group
                        c0_step
                        · r2b_steps
                          try rw [hshEnd1] at hc
                          rw [Nat.mod_eq_of_lt hsz64] at hc
                          have heEq : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 e := by
                            dsimp only [e, strPosClamp]
                            rw [ite_eq_left ha1, Nat.min_eq_right (Nat.le_of_lt hc)]
                          apply hJ; simp only [Blocks.get]; c0_steps
                          dsimp only [bs] at heEq; rw [heEq]
                          exact hJ2 (BitVec.ofNat 64 e, ()) m ⟨rfl, rfl⟩
                        · r2b_steps
                          try rw [hshEnd1] at hc
                          rw [Nat.mod_eq_of_lt hsz64] at hc
                          have hle : (endV >>> 1).toNat ≤ bs.length := Nat.not_lt.mp hc
                          have heEq : (endV >>> 1) = BitVec.ofNat 64 e := by
                            dsimp only [e, strPosClamp]
                            rw [ite_eq_left ha1, Nat.min_eq_left hle]
                            apply BitVec.eq_of_toNat_eq
                            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hsz64)]
                          apply hJ; simp only [Blocks.get]; c0_steps
                          try rw [hshEnd1]
                          rw [heEq]
                          exact hJ2 (BitVec.ofNat 64 e, ()) m ⟨rfl, rfl⟩
                      · r2b_steps
                        have hnot : (endV &&& 1#64) = 0#64 := by
                          rw [show (1 : BitVec 64) = 1#64 from rfl,
                            show (0 : BitVec 64) = 0#64 from rfl] at hc
                          first | exact hc | exact Classical.not_not.mp hc
                        have heEq : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 e := by
                          dsimp only [e, strPosClamp]; rw [ite_eq_right (by simp [hnot])]
                        dsimp only [bs] at heEq; rw [heEq]
                        exact hJ2 (BitVec.ofNat 64 e, ()) m ⟨rfl, rfl⟩
                  · intro J1 hJ1
                    r2b_to_group
                    c0_step
                    · have ha1 : (idxV &&& 1#64) ≠ 0#64 := by
                        rw [show (1 : BitVec 64) = 1#64 from rfl,
                          show (0 : BitVec 64) = 0#64 from rfl] at hc; exact hc
                      r2b_to_group
                      c0_step
                      r2b_to_group
                      c0_step
                      · r2b_steps
                        try rw [hsh1] at hc
                        rw [Nat.mod_eq_of_lt hsz64] at hc
                        have hbEq : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 b := by
                          dsimp only [b, strPosClamp]
                          rw [ite_eq_left ha1, Nat.min_eq_right (Nat.le_of_lt hc)]
                        apply hJ; simp only [Blocks.get]; c0_steps
                        dsimp only [bs] at hbEq; rw [hbEq]
                        exact hJ1 (BitVec.ofNat 64 b, ()) m ⟨rfl, rfl⟩
                      · r2b_steps
                        try rw [hsh1] at hc
                        rw [Nat.mod_eq_of_lt hsz64] at hc
                        have hle : (idxV >>> 1).toNat ≤ bs.length := Nat.not_lt.mp hc
                        have hbEq : (idxV >>> 1) = BitVec.ofNat 64 b := by
                          dsimp only [b, strPosClamp]
                          rw [ite_eq_left ha1, Nat.min_eq_left hle]
                          apply BitVec.eq_of_toNat_eq
                          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hsz64)]
                        apply hJ; simp only [Blocks.get]; c0_steps
                        try rw [hsh1]
                        rw [hbEq]
                        exact hJ1 (BitVec.ofNat 64 b, ()) m ⟨rfl, rfl⟩
                    · r2b_steps
                      have hnot : (idxV &&& 1#64) = 0#64 := by
                        rw [show (1 : BitVec 64) = 1#64 from rfl,
                          show (0 : BitVec 64) = 0#64 from rfl] at hc
                        first | exact hc | exact Classical.not_not.mp hc
                      have hbEq : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 b := by
                        dsimp only [b, strPosClamp]; rw [ite_eq_right (by simp [hnot])]
                      dsimp only [bs] at hbEq; rw [hbEq]
                      exact hJ1 (BitVec.ofNat 64 b, ()) m ⟨rfl, rfl⟩
              · c0_step
                all_goals try
                  (exfalso; rw [show (3 : BitVec 64) = 3#64 from rfl] at hc; exact hop3 hc)
                focus
                  r2b_to_group
                  by_cases hop4 : op = 4#64
                  · subst hop4
                    rw [ite_eq_left (Or.inr (Or.inr (Or.inr (Or.inl rfl))))] at hPost
                    simp only [show (4#64 : BitVec 64) ≠ 1#64 by decide, ite_false] at hPost
                    obtain ⟨Rest, hmExp, _⟩ := strObj_expose_bytes hcanon hmS
                    c0_step
                    · r2b_to_group
                      c0_step
                      · have ha0 : (idxV &&& 1#64) = 0#64 := by
                          rw [show (0 : BitVec 64) = 0#64 from rfl,
                            show (1 : BitVec 64) = 1#64 from rfl] at hc
                          exact hc
                        r2b_steps
                        have hsp := hPost m (sep_cast hm (by ac_rfl))
                        simp only [strPosOpVal, show (4#64 : BitVec 64) ≠ 0#64 by decide,
                          show (4#64 : BitVec 64) ≠ 1#64 by decide,
                          show (4#64 : BitVec 64) ≠ 2#64 by decide, ite_false, ite_true,
                          ite_eq_left ha0] at hsp
                        exact hsp
                      · have ha1 : (idxV &&& 1#64) ≠ 0#64 := by
                          rw [show (0 : BitVec 64) = 0#64 from rfl,
                            show (1 : BitVec 64) = 1#64 from rfl] at hc
                          exact hc
                        r2b_to_group
                        c0_step
                        · try rw [hsh1] at hc
                          rw [Nat.mod_eq_of_lt hsz64] at hc
                          r2b_steps
                          dsimp only [bs] at hc
                          have hsp := hPost m (sep_cast hm (by ac_rfl))
                          simp only [strPosOpVal, show (4#64 : BitVec 64) ≠ 0#64 by decide,
                            show (4#64 : BitVec 64) ≠ 1#64 by decide,
                            show (4#64 : BitVec 64) ≠ 2#64 by decide, ite_false, ite_true,
                            ite_eq_right ha1, dite_eq_right (Nat.not_lt_of_le hc)] at hsp
                          exact hsp
                        · try rw [hsh1] at hc
                          rw [Nat.mod_eq_of_lt hsz64] at hc
                          have hlt : (idxV >>> 1).toNat < bs.length := Nat.lt_of_not_le hc
                          apply wp_load_of (by
                            first
                            | exact r2b_c0_load_bytes_add32 hmExp
                                (by dsimp only [bs] at hlt; exact hlt)
                                (by dsimp only [bs] at hsz64; exact Nat.le_of_lt hsz64)
                            | exact r2b_c0_load_bytes_add32 hmExp
                                (by dsimp only [bs] at hlt; rw [← hsh1] at hlt; exact hlt)
                                (by dsimp only [bs] at hsz64; exact Nat.le_of_lt hsz64))
                          r2b_steps
                          have hspec := hPost m (sep_cast hm (by ac_rfl))
                          dsimp only [bs] at hlt
                          simp only [strPosOpVal, ite_eq_right ha1, dite_eq_left hlt,
                            show (4#64 : BitVec 64) ≠ 0#64 by decide,
                            show (4#64 : BitVec 64) ≠ 1#64 by decide,
                            show (4#64 : BitVec 64) ≠ 2#64 by decide, ite_true, ite_false] at hspec
                          try rw [hsh1]
                          have hbvEq : BitVec.ofNat 8 bs[(idxV >>> 1).toNat].toNat =
                              bs[(idxV >>> 1).toNat].toBitVec := by
                            apply BitVec.eq_of_toNat_eq
                            rw [BitVec.toNat_ofNat, UInt8.toNat_toBitVec]
                            exact Nat.mod_eq_of_lt bs[(idxV >>> 1).toNat].toBitVec.isLt
                          dsimp only [bs] at hbvEq ⊢
                          rw [hbvEq]; exact hspec
                    all_goals try
                      (exfalso; rw [show (4 : BitVec 64) = 4#64 from rfl] at hc; exact hc rfl)
                  · c0_step
                    all_goals try
                      (exfalso; rw [show (4 : BitVec 64) = 4#64 from rfl] at hc; exact hop4 hc)
                    focus
                      r2b_to_group
                      by_cases hop5 : op = 5#64
                      · subst hop5
                        rw [ite_eq_left (Or.inr (Or.inr (Or.inr (Or.inr rfl))))] at hPost
                        simp only [show (5#64 : BitVec 64) ≠ 1#64 by decide, ite_false] at hPost
                        obtain ⟨Rest, hmExp, _⟩ := strObj_expose_bytes hcanon hmS
                        c0_step
                        · r2b_to_group
                          c0_step
                          · have ha0 : (idxV &&& 1#64) = 0#64 := by
                              rw [show (0 : BitVec 64) = 0#64 from rfl,
                                show (1 : BitVec 64) = 1#64 from rfl] at hc
                              exact hc
                            r2b_steps
                            have hsp := hPost m (sep_cast hm (by ac_rfl))
                            simp only [strPosOpVal, show (5#64 : BitVec 64) ≠ 0#64 by decide,
                              show (5#64 : BitVec 64) ≠ 1#64 by decide,
                              show (5#64 : BitVec 64) ≠ 2#64 by decide,
                              show (5#64 : BitVec 64) ≠ 4#64 by decide, ite_false,
                              ite_eq_left ha0] at hsp
                            exact hsp
                          · have ha1 : (idxV &&& 1#64) ≠ 0#64 := by
                              rw [show (0 : BitVec 64) = 0#64 from rfl,
                                show (1 : BitVec 64) = 1#64 from rfl] at hc
                              exact hc
                            r2b_to_group
                            c0_step
                            · try rw [hsh1] at hc
                              rw [Nat.mod_eq_of_lt hsz64] at hc
                              r2b_steps
                              dsimp only [bs] at hc
                              have hsp := hPost m (sep_cast hm (by ac_rfl))
                              simp only [strPosOpVal, show (5#64 : BitVec 64) ≠ 0#64 by decide,
                                show (5#64 : BitVec 64) ≠ 1#64 by decide,
                                show (5#64 : BitVec 64) ≠ 2#64 by decide,
                                show (5#64 : BitVec 64) ≠ 4#64 by decide, ite_false,
                                ite_eq_right ha1, ite_eq_left hc] at hsp
                              exact hsp
                            · try rw [hsh1] at hc
                              rw [Nat.mod_eq_of_lt hsz64] at hc
                              have hng : ¬ bs.length < (idxV >>> 1).toNat := hc
                              r2b_to_group
                              c0_step
                              · try rw [hsh1] at hc
                                have heq : (idxV >>> 1).toNat = bs.length := by
                                  have := congrArg BitVec.toNat hc
                                  rwa [hszTo] at this
                                r2b_steps
                                dsimp only [bs] at heq hng
                                have hnl : ¬ (idxV >>> 1).toNat < (strPayload sObj).length := by
                                  rw [heq]; exact Nat.lt_irrefl _
                                have hsp := hPost m (sep_cast hm (by ac_rfl))
                                simp only [strPosOpVal, show (5#64 : BitVec 64) ≠ 0#64 by decide,
                                  show (5#64 : BitVec 64) ≠ 1#64 by decide,
                                  show (5#64 : BitVec 64) ≠ 2#64 by decide,
                                  show (5#64 : BitVec 64) ≠ 4#64 by decide, ite_false,
                                  ite_eq_right ha1, ite_eq_right hng, dite_eq_right hnl] at hsp
                                exact hsp
                              · try rw [hsh1] at hc
                                have hne : (idxV >>> 1).toNat ≠ bs.length := by
                                  intro he; apply hc; apply BitVec.eq_of_toNat_eq; rw [he, hszTo]
                                have hlt : (idxV >>> 1).toNat < bs.length :=
                                  Nat.lt_of_le_of_ne (Nat.not_lt.mp hng) hne
                                apply wp_load_of (by
                                  first
                                  | exact r2b_c0_load_bytes_add32 hmExp
                                      (by dsimp only [bs] at hlt; exact hlt)
                                      (by dsimp only [bs] at hsz64; exact Nat.le_of_lt hsz64)
                                  | exact r2b_c0_load_bytes_add32 hmExp
                                      (by dsimp only [bs] at hlt; rw [← hsh1] at hlt; exact hlt)
                                      (by dsimp only [bs] at hsz64; exact Nat.le_of_lt hsz64))
                                r2b_to_group
                                c0_step
                                · have hmNe :
                                      ((strPayload sObj)[(idxV >>> 1).toNat].toNat &&& 0xc0) ≠
                                        0x80 := by
                                    rw [show (192 : BitVec 64) = 192#64 from rfl,
                                      show (128 : BitVec 64) = 128#64 from rfl] at hc
                                    intro h0; apply hc; apply BitVec.eq_of_toNat_eq
                                    rw [bv8_zext_mask_eq]; exact h0
                                  dsimp only [bs] at hlt hng
                                  r2b_steps
                                  have hsp := hPost m (sep_cast hm (by ac_rfl))
                                  simp only [strPosOpVal, show (5#64 : BitVec 64) ≠ 0#64 by decide,
                                    show (5#64 : BitVec 64) ≠ 1#64 by decide,
                                    show (5#64 : BitVec 64) ≠ 2#64 by decide,
                                    show (5#64 : BitVec 64) ≠ 4#64 by decide, ite_false,
                                    ite_eq_right ha1, ite_eq_right hng, dite_eq_left hlt,
                                    ite_eq_left hmNe] at hsp
                                  exact hsp
                                · have hmEq :
                                      ((strPayload sObj)[(idxV >>> 1).toNat].toNat &&& 0xc0) =
                                        0x80 := by
                                    rw [show (192 : BitVec 64) = 192#64 from rfl,
                                      show (128 : BitVec 64) = 128#64 from rfl] at hc
                                    have htn := congrArg BitVec.toNat hc
                                    rw [bv8_zext_mask_eq] at htn; exact htn
                                  dsimp only [bs] at hlt hng
                                  r2b_steps
                                  have hsp := hPost m (sep_cast hm (by ac_rfl))
                                  simp only [strPosOpVal, show (5#64 : BitVec 64) ≠ 0#64 by decide,
                                    show (5#64 : BitVec 64) ≠ 1#64 by decide,
                                    show (5#64 : BitVec 64) ≠ 2#64 by decide,
                                    show (5#64 : BitVec 64) ≠ 4#64 by decide, ite_false,
                                    ite_eq_right ha1, ite_eq_right hng, dite_eq_left hlt,
                                    ite_eq_right (Classical.not_not.mpr hmEq)] at hsp
                                  rw [show (0#64 : BitVec 64) = 0 from rfl] at hsp
                                  exact hsp
                        all_goals try
                          (exfalso; rw [show (5 : BitVec 64) = 5#64 from rfl] at hc
                           exact hc rfl)
                      · c0_step
                        all_goals try
                          (exfalso; rw [show (5 : BitVec 64) = 5#64 from rfl] at hc
                           exact hop5 hc)
                        rw [ite_eq_right (by simp [hop0, hop1, hop2, hop4, hop5]),
                          ite_eq_right hop3] at hPost
                        r2b_steps
                        exact hPost

end LeanQbe.T.LeanLCNF
