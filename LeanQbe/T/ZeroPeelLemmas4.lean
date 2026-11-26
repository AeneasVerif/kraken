module

public import LeanQbe.T.ZeroPeel
public import LeanQbe.T.ZeroPeelLemmas1
public import LeanQbe.T.ZeroPeelLemmas2
public import LeanQbe.T.ZeroPeelLemmas3
public import LeanQbe.T.Wf
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.GroupLfpLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.PassFlatKit
import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.OpsLemmas
import all Kraken.Mem

/-!
# Helper Lemmas for `LeanQbe.T.ZeroPeel` (Part 4: `widenFillExt` Wrap + `unrollCountedSingle`)

Exports `widenFillExt_wp`, `widenFillExt_callsOk`, `unrollCountedSingle_wf`,
`unrollCountedSingle_wp`, and `unrollCountedSingle_callsOk`.
-/

set_option autoImplicit false
namespace LeanQbe.T
open Std Std.ExtHashMap
namespace ZeroPeel

/-! ## Section 1: `widenFillExt_wp` & `widenFillExt_callsOk` -/

private def mkFB : (is32 : Bool) → Bool → Arg K (.bits (if is32 then 32 else 64)) → FillBound
  | true => .b32
  | false => .b64

private theorem lookupL_0 {L : List Ty → Type} {ts : List Ty} (l : L ts)
    (ls : List ((ts : List Ty) × L ts)) : lookupL (⟨ts, l⟩ :: ls) ts 0 = some l := by
  dsimp only [lookupL]; rw [listGet?_cons_zero_eq]; exact castListTy_self _ _
private theorem lookupL_1 {L : List Ty → Type} {ts0 ts1 : List Ty} (l0 : L ts0) (l1 : L ts1)
    (ls : List ((ts : List Ty) × L ts)) :
    lookupL (⟨ts0, l0⟩ :: ⟨ts1, l1⟩ :: ls) ts1 1 = some l1 := by
  dsimp only [lookupL]; rw [listGet?_cons_succ_eq, listGet?_cons_zero_eq]
  exact castListTy_self _ _

private theorem widenFillExt_wp_case {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {GOuter : List Ty} {DOuter : List (List Ty)}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    (hCtxV : CtxTypes GOuter vs) {unrollN : Nat} (hu1 : 1 ≤ unrollN) (hu64 : unrollN ≤ 64)
    (is32 : Bool) {initArg : Arg K (.bits (if is32 then 32 else 64))} {isLt : Bool}
    {bnd : Arg K (.bits (if is32 then 32 else 64))} {stores : List StoreSpec}
    {body : TFlat rs} {m : Mem 64}
    (hwf1 : TFlat.wfCheck (pushTypes [.bits (if is32 then 32 else 64)] GOuter)
      (pushTypes [[.bits (if is32 then 32 else 64)]] DOuter) body = true)
    (hwf2 : TFlat.wfCheck (rs := rs) GOuter (pushTypes [[.bits (if is32 then 32 else 64)]] DOuter)
      (.jump (rs := rs) (ts := [.bits (if is32 then 32 else 64)]) 0 (initArg, ())) = true)
    (hm : matchMultiFillBody is32 #[] body = some (mkFB is32 isLt bnd, stores))
    (hLen1 : 1 ≤ stores.length) (_hLen8 : stores.length ≤ 8)
    (hwp : wp Γ Q X (denote Val Cont
      (.group (sig := [[.bits (if is32 then 32 else 64)]]) (.cons body .nil)
        (.jump (ts := [.bits (if is32 then 32 else 64)]) 0 (initArg, ()))) vs ls) m) :
    wp Γ Q X (denote Val Cont
      (.group (sig := [[.bits (if is32 then 32 else 64)]]) (.cons body .nil)
        (mkMultiWideWrapper (if is32 then 32 else 64) isLt initArg bnd stores
          (computeMultiStepK unrollN stores))) vs ls) m := by
  let w := if is32 then 32 else 64
  have hwEq : w = 32 ∨ w = 64 := by cases is32 <;> simp [w]
  have hG := ctx_diagV_of_vs (vs := vs); have hD := ctx_monoD_of_ls (ls := ls)
  have hRelV := ctxRel_refl_vs (vs := vs); have hRelL := ctxRel_refl_ls (ls := ls)
  have hEmpty : SymExtEnvWf GOuter [] #[] := ⟨rfl, fun _ h => by cases h⟩
  rw [wfCheck_jump_eq, Bool.and_eq_true] at hwf2
  have hInitWf : checkArg GOuter (.bits w) initArg = true := by
    simpa [pushTypes, checkArgs, w] using hwf2.2
  have hmWf := matchMultiFillBody_wf (GOuter := GOuter)
    (D := [if is32 then i32 else i64] :: DOuter) (is32 := is32) body hEmpty
    (show body.wfCheck ([] ++ (if is32 then i32 else i64) :: GOuter)
        ([if is32 then i32 else i64] :: DOuter) = true by
      cases is32 <;> simpa [pushTypes] using hwf1) hm
  have hBndWf : checkArg GOuter (.bits w) bnd = true := by cases is32 <;> exact hmWf.1.2
  have hStep := computeMultiStepK_spec unrollN stores hu1 hu64 hLen1
    (fun s hs => (hmWf.2 s hs).2.2)
  obtain ⟨initA, hdInit⟩ := Option.isSome_iff_exists.mp (denoteArg_isSome_of_checkArg hCtxV hInitWf)
  obtain ⟨bndA, hdBnd⟩ := Option.isSome_iff_exists.mp (denoteArg_isSome_of_checkArg hCtxV hBndWf)
  let bodies : Tup Cont [[.bits w]] → Blocks Val Cont rs [[.bits w]] := fun Js =>
    denoteB Val Cont (.cons (ts := [.bits w]) body .nil) vs (pushTup Js ls)
  have hWfB (Js₁ Js₂ : Tup Cont [[.bits w]]) :
      WfB (List.map (fun ⟨t, v⟩ => ⟨t, (v, v)⟩) vs)
        (Js₁.zip Js₂ ++ List.map (fun ⟨ts, l⟩ => ⟨ts, (l, l)⟩) ls) (bodies Js₁) (bodies Js₂) :=
    denoteB_wf (.cons (ts := [.bits w]) body .nil) hRelV (ctxRel_pushTup Js₁ Js₂ hRelL)
  rw [denote_group_eq] at hwp ⊢
  rw [wp_group_iff hG hD hWfB (fun Js₁ Js₂ =>
    denote_wf (.jump (ts := [.bits w]) 0 (initArg, ())) hRelV (ctxRel_pushTup Js₁ Js₂ hRelL))]
    at hwp
  rw [wp_group_iff hG hD hWfB (fun Js₁ Js₂ =>
    denote_wf (mkMultiWideWrapper w isLt initArg bnd stores (computeMultiStepK unrollN stores))
      hRelV (ctxRel_pushTup Js₁ Js₂ hRelL))]
  let JLoop : Cont [.bits w] := (lfp Γ Q X bodies).fst
  have hPushJs : pushTup (lfp Γ Q X bodies) ls = ⟨[.bits w], JLoop⟩ :: ls := by
    cases hEq : lfp Γ Q X bodies with | mk jl u => cases u; dsimp only [JLoop]; rw [hEq]; rfl
  have hJInit : JLoop (initA.val, ()) m := by
    rw [hPushJs, denote_jump_eq, denoteArgs_singleton_eq, lookupL_0, hdInit] at hwp
    simpa [wp_jump, vals, Arg.val] using hwp
  cases is32 with
  | true =>
    obtain ⟨isLt', bnd', ss, hFb, hF2, hBodyMatched⟩ :=
      matchMultiFillBody_spec (Γ := Γ) (Q := Q) (X := X) (vsOuter := vs) (ls := ls)
        (is32 := true) (JLoop := JLoop) hCtxV body hEmpty
        (by simpa [pushTypes] using hwf1) hm
    dsimp only [mkFB] at hFb; cases hFb
    have hStepScal : ∀ (i' : BitVec 32) (m' : Mem 64),
        i'.toNat < bndA.val.toNat → JLoop (i', ()) m' →
        ScalarChainOk m' (bv64OfW i') ss ∧
        JLoop (i' + BitVec.ofNat 32 1, ()) (applyScalarChain m' (bv64OfW i') ss) := by
      intro i' m' hiLt hJi
      have hUnr := lfp_unroll_single hG hD hWfB (i', ()) m' hJi
      change wp Γ Q X ((denoteB Val Cont (.cons (ts := [.bits 32]) body .nil) vs
        (pushTup (lfp Γ Q X bodies) ls)).get Member.here (i', ())) m' at hUnr
      rw [hPushJs, denoteB_cons_eq] at hUnr
      have hCmpT : cmpBoundOk true isLt i' bndA.val := by
        have hLe := Nat.le_of_lt hiLt
        dsimp only [cmpBoundOk]; cases isLt
        · exact decide_eq_true (BitVec.le_def.mpr hLe)
        · exact decide_eq_true (BitVec.lt_def.mpr hiLt)
      simpa [bv64OfW_32, incLoopVal] using
        hBodyMatched [] i' m' bndA symExtEnvMatch_empty hdBnd hCmpT hUnr
    rw [hPushJs]; dsimp only [mkMultiWideWrapper]; rw [denote_group_eq]
    exact widenFillExt_loop_wp hwEq hu1 hu64 hdInit hdBnd hLen1 hStep hF2 hJInit hStepScal rfl
  | false =>
    obtain ⟨isLt', bnd', ss, hFb, hF2, hBodyMatched⟩ :=
      matchMultiFillBody_spec (Γ := Γ) (Q := Q) (X := X) (vsOuter := vs) (ls := ls)
        (is32 := false) (JLoop := JLoop) hCtxV body hEmpty
        (by simpa [pushTypes] using hwf1) hm
    dsimp only [mkFB] at hFb; cases hFb
    have hStepScal : ∀ (i' : BitVec 64) (m' : Mem 64),
        i'.toNat < bndA.val.toNat → JLoop (i', ()) m' →
        ScalarChainOk m' (bv64OfW i') ss ∧
        JLoop (i' + BitVec.ofNat 64 1, ()) (applyScalarChain m' (bv64OfW i') ss) := by
      intro i' m' hiLt hJi
      have hUnr := lfp_unroll_single hG hD hWfB (i', ()) m' hJi
      change wp Γ Q X ((denoteB Val Cont (.cons (ts := [.bits 64]) body .nil) vs
        (pushTup (lfp Γ Q X bodies) ls)).get Member.here (i', ())) m' at hUnr
      rw [hPushJs, denoteB_cons_eq] at hUnr
      have hCmpT : cmpBoundOk false isLt i' bndA.val := by
        have hLe := Nat.le_of_lt hiLt
        dsimp only [cmpBoundOk]; cases isLt
        · exact decide_eq_true (BitVec.le_def.mpr hLe)
        · exact decide_eq_true (BitVec.lt_def.mpr hiLt)
      simpa [bv64OfW_64, incLoopVal] using
        hBodyMatched [] i' m' bndA symExtEnvMatch_empty hdBnd hCmpT hUnr
    rw [hPushJs]; dsimp only [mkMultiWideWrapper]; rw [denote_group_eq]
    exact widenFillExt_loop_wp hwEq hu1 hu64 hdInit hdBnd hLen1 hStep hF2 hJInit hStepScal rfl

public theorem widenFillExt_wp {Γ : Env} {rs ts0 : List Ty} {Q : Post rs} {X : XPost}
    {GOuter : List Ty} {DOuter : List (List Ty)}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    (hCtxV : CtxTypes GOuter vs) (_hCtxL : CtxTypes DOuter ls)
    {unrollN : Nat} {body k res : TFlat rs} {m : Mem 64}
    (hwf : TFlat.wfCheck GOuter DOuter (.group (@TBlocks.cons rs ts0 [] body .nil) k) = true)
    (hw : widenFillExt unrollN ts0 body k = some res)
    (hwp : wp Γ Q X (denote Val Cont (.group (@TBlocks.cons rs ts0 [] body .nil) k) vs ls) m) :
    wp Γ Q X (denote Val Cont res vs ls) m := by
  obtain ⟨hu1, hu64, hCase⟩ := widenFillExt_eq_some hw
  rw [wfCheck_group_eq, wfCheckB_cons_eq, wfCheckB_nil_eq, Bool.and_true, Bool.and_eq_true] at hwf
  rcases hCase with ⟨rfl, initArg, isLt, bnd, stores, rfl, hm, h1, h8, rfl⟩ |
      ⟨rfl, initArg, isLt, bnd, stores, rfl, hm, h1, h8, rfl⟩
  · exact widenFillExt_wp_case hCtxV hu1 hu64 true hwf.1 hwf.2 hm h1 h8 hwp
  · exact widenFillExt_wp_case hCtxV hu1 hu64 false hwf.1 hwf.2 hm
      (Nat.le_trans (by decide) h1) h8 hwp

private theorem mkSeqStoresGo_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (fill64 : BitVec 64) (cont : Nat → TFlat rs)
    (hCont : ∀ d, PassFlatKit.callsOkTF allowed exits (cont d)) :
    ∀ (m r : Nat), PassFlatKit.callsOkTF allowed exits (mkSeqStoresGo fill64 m r cont)
  | m, 0 => hCont (m - 1)
  | m, r + 1 => by
    dsimp only [mkSeqStoresGo]
    simp only [PassFlatKit.callsOkTF_let, PassFlatKit.callsOkTF_store]
    exact mkSeqStoresGo_callsOk fill64 cont hCont (m + 1) r

private theorem mkSeqStores_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (fill64 : BitVec 64) (cont : Nat → TFlat rs)
    (hCont : ∀ d, PassFlatKit.callsOkTF allowed exits (cont d)) :
    ∀ n64, PassFlatKit.callsOkTF allowed exits (mkSeqStores fill64 n64 cont)
  | 0 => by simp [mkSeqStores]
  | r + 1 => by
    dsimp only [mkSeqStores]; simp only [PassFlatKit.callsOkTF_store]
    exact mkSeqStoresGo_callsOk fill64 cont hCont 1 r

private theorem emitWideStreams_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (w stepK : Nat) :
    (stores : List StoreSpec) → ∀ (d iD i64D : Nat),
      PassFlatKit.callsOkTF allowed exits (emitWideStreams (rs := rs) w stepK stores d iD i64D)
  | [], _, _, _ => by simp [emitWideStreams]
  | st :: rest, d, iD, i64D => by
    dsimp only [emitWideStreams]
    have hAfterOff : ∀ d1 iD1 i64D1 idx,
        PassFlatKit.callsOkTF allowed exits
          (if (st.shift == 0) = true then
            TFlat.let_ (op2 (.add i64) (tArgShift d1 st.base) idx)
              (mkSeqStores (rs := rs) st.fill64 (stepK / (8 >>> st.shift)) (fun pushed =>
                emitWideStreams w stepK rest (d1 + 1 + pushed)
                  (iD1 + 1 + pushed) (i64D1 + 1 + pushed)))
          else
            TFlat.let_ (op2 (.shl i64) idx (.imm (BitVec.ofNat 64 st.shift)))
              (TFlat.let_ (op2 (.add i64) (tArgShift (d1 + 1) st.base) (.var 0))
                (mkSeqStores (rs := rs) st.fill64 (stepK / (8 >>> st.shift)) (fun pushed =>
                  emitWideStreams w stepK rest (d1 + 1 + 1 + pushed)
                    (iD1 + 1 + 1 + pushed) (i64D1 + 1 + 1 + pushed))))) := by
      intro d1 iD1 i64D1 _; split
      · simp only [PassFlatKit.callsOkTF_let]
        exact mkSeqStores_callsOk st.fill64 _ (fun p => emitWideStreams_callsOk w stepK rest _ _ _)
          _
      · simp only [PassFlatKit.callsOkTF_let]
        exact mkSeqStores_callsOk st.fill64 _ (fun p => emitWideStreams_callsOk w stepK rest _ _ _)
          _
    cases st.off?
    · exact hAfterOff d iD i64D _
    · simp only [PassFlatKit.callsOkTF_let]; exact hAfterOff _ _ _ _

private theorem mkPairChecks_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (w : Nat) (initArg : Arg K (.bits w)) :
    (pairs : List ((Nat × Nat) × (Nat × Nat))) → (d : Nat) →
      PassFlatKit.callsOkTF allowed exits (mkPairChecks (rs := rs) w initArg pairs d)
  | [], _ => by simp [mkPairChecks]
  | _ :: rest, d => by
    dsimp only [mkPairChecks]
    simp only [PassFlatKit.callsOkTF_let, PassFlatKit.callsOkTF_jnz, PassFlatKit.callsOkTF_jump,
      and_true]
    exact mkPairChecks_callsOk w initArg rest (d + 3)

private theorem mkStreamBounds_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (w : Nat) (initArg : Arg K (.bits w)) (rL iL : Nat) :
    (stores : List StoreSpec) → (d : Nat) → (ivs : List (Nat × Nat)) →
      PassFlatKit.callsOkTF allowed exits (mkStreamBounds (rs := rs) w initArg rL iL stores d ivs)
  | [], d, ivs => mkPairChecks_callsOk w initArg (allIdxPairs ivs) d
  | st :: rest, d, ivs => by
    dsimp only [mkStreamBounds]
    cases st.off? <;> cases hS : st.shift == 0 <;>
      simp only [Bool.false_eq_true, ite_true, ite_false,
        PassFlatKit.callsOkTF_let, PassFlatKit.callsOkTF_jnz,
        PassFlatKit.callsOkTF_jump, and_true] <;>
      exact mkStreamBounds_callsOk w initArg rL iL rest _ _

private theorem mkMultiWideWrapper_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (w : Nat) (isLt : Bool) (initArg bound : Arg K (.bits w))
    (stores : List StoreSpec) (stepK : Nat) :
    PassFlatKit.callsOkTF allowed exits
      (mkMultiWideWrapper (rs := rs) w isLt initArg bound stores stepK) := by
  dsimp only [mkMultiWideWrapper, mkMultiWideBody, mkDisjointCheck]
  simp only [PassFlatKit.callsOkTF_group, PassFlatKit.callsOkBs_cons, PassFlatKit.callsOkBs_nil,
    PassFlatKit.callsOkTF_let, PassFlatKit.callsOkTF_jnz, PassFlatKit.callsOkTF_jump, and_true]
  refine ⟨by split <;> simp [emitWideStreams_callsOk], ?_⟩
  split
  · cases isLt <;> simp
  · cases isLt <;>
      · simp only [PassFlatKit.callsOkTF_let, PassFlatKit.callsOkTF_jnz,
          PassFlatKit.callsOkTF_jump, and_true]
        split <;> try split
        · simp [mkStreamBounds_callsOk (rs := rs)]
        · simp [mkStreamBounds_callsOk (rs := rs)]
        · simp

public theorem widenFillExt_callsOk {allowed : List SigEntry} {exits : List Sym} {rs ts0 : List Ty}
    {unrollN : Nat} {body k res : TFlat rs}
    (hb : PassFlatKit.callsOkTF allowed exits body)
    (hw : widenFillExt unrollN ts0 body k = some res) :
    PassFlatKit.callsOkTF allowed exits res := by
  obtain ⟨_, _, hCase⟩ := widenFillExt_eq_some hw
  rcases hCase with ⟨rfl, initArg, isLt, bnd, stores, rfl, _, _, _, rfl⟩ |
      ⟨rfl, initArg, isLt, bnd, stores, rfl, _, _, _, rfl⟩ <;>
    simp [hb, mkMultiWideWrapper_callsOk]

/-! ## Section 2: `shiftLabelsTFlat`, `stripJnzTrue`, & `inlineJumpTarget` Helpers -/

private theorem lookupL_append_mid_lt {L : List Ty → Type}
    (lsPre lsMid lsPost : List ((ts : List Ty) × L ts)) (ts : List Ty) {i : Nat}
    (hlt : i < lsPre.length) :
    lookupL (lsPre ++ (lsMid ++ lsPost)) ts i = lookupL (lsPre ++ lsPost) ts i := by
  simp only [lookupL, listGet?_eq_getElem?, List.getElem?_append_left hlt]
private theorem pushTup_singleton {t : Ty} (x : Val t) (vs : List ((u : Ty) × Val u)) :
    pushTup (f := Val) (as := [t]) (x, ()) vs = ⟨t, x⟩ :: vs := rfl
private theorem lookupL_append_mid_ge {L : List Ty → Type}
    (lsPre lsMid lsPost : List ((ts : List Ty) × L ts)) (ts : List Ty) {i : Nat}
    (hge : i ≥ lsPre.length) :
    lookupL (lsPre ++ (lsMid ++ lsPost)) ts (i + lsMid.length) =
      lookupL (lsPre ++ lsPost) ts i := by
  have hi : i + lsMid.length ≥ lsPre.length := Nat.le_trans hge (Nat.le_add_right i lsMid.length)
  simp only [lookupL, listGet?_eq_getElem?]
  rw [List.getElem?_append_right hi, List.getElem?_append_right hge]
  have hge2 : i + lsMid.length - lsPre.length ≥ lsMid.length := by omega
  rw [List.getElem?_append_right hge2,
    show i + lsMid.length - lsPre.length - lsMid.length = i - lsPre.length by omega]
private theorem lookupL_append_drop {L : List Ty → Type}
    (ls1 ls2 : List ((ts : List Ty) × L ts)) (ts : List Ty) :
    lookupL (ls1 ++ ls2) ts ls1.length = lookupL ls2 ts 0 := by
  have h := lookupL_append_mid_ge (L := L) ([] : List ((ts : List Ty) × L ts)) ls1 ls2 ts
    (i := 0) (by simp)
  simpa using h
private theorem wfCheckB_cons_nil {rs : List Ty} (G : List Ty) (D : List (List Ty))
    (ts : List Ty) (b : TFlat rs) :
    (TBlocks.cons (ts := ts) b .nil).wfCheck G D = b.wfCheck (pushTypes ts G) D := by
  rw [wfCheckB_cons_eq, wfCheckB_nil_eq, Bool.and_true]

mutual
private theorem wfCheck_shiftLabelsTFlat {rs : List Ty} (G : List Ty)
    (DPre DMid DPost : List (List Ty)) : (tf : TFlat rs) →
    (shiftLabelsTFlat DPre.length DMid.length tf).wfCheck G (DPre ++ (DMid ++ DPost)) =
      tf.wfCheck G (DPre ++ DPost)
  | .let_ _ k => by
    unfold shiftLabelsTFlat; rw [wfCheck_let_eq, wfCheck_let_eq]
    exact congrArg _ (wfCheck_shiftLabelsTFlat _ DPre DMid DPost k)
  | .load _ _ k => by
    unfold shiftLabelsTFlat; rw [wfCheck_load_eq, wfCheck_load_eq]
    exact congrArg _ (wfCheck_shiftLabelsTFlat _ DPre DMid DPost k)
  | .store _ _ k => by
    unfold shiftLabelsTFlat; rw [wfCheck_store_eq, wfCheck_store_eq]
    exact congrArg _ (wfCheck_shiftLabelsTFlat _ DPre DMid DPost k)
  | .call _ _ _ k => by
    unfold shiftLabelsTFlat; rw [wfCheck_call_eq, wfCheck_call_eq]
    exact congrArg _ (wfCheck_shiftLabelsTFlat _ DPre DMid DPost k)
  | .jnz _ t e => by
    unfold shiftLabelsTFlat; rw [wfCheck_jnz_eq, wfCheck_jnz_eq,
      wfCheck_shiftLabelsTFlat G DPre DMid DPost t,
      wfCheck_shiftLabelsTFlat G DPre DMid DPost e]
  | .jump (ts := ts) j args => by
    unfold shiftLabelsTFlat
    by_cases hj : j ≥ DPre.length
    · rw [ite_eq_left (by simp [hj]), wfCheck_jump_eq, wfCheck_jump_eq]
      have hL := listGet?_append_mid_ge DPre DMid DPost j hj
      rw [listGet?_eq_getElem?] at hL ⊢; rw [hL]
    · rw [ite_eq_right (by simp [hj]), wfCheck_jump_eq, wfCheck_jump_eq]
      have hlt : j < DPre.length := by omega
      have hL := listGet?_append_mid_lt DPre DMid DPost j hlt
      rw [listGet?_eq_getElem?] at hL ⊢; rw [hL]
  | .ret _ | .exit _ _ | .hlt => by unfold shiftLabelsTFlat; rfl
  | .group (sig := sig) bs k => by
    unfold shiftLabelsTFlat
    rw [wfCheck_group_eq, wfCheck_group_eq]
    have hb := wfCheckB_shiftLabelsTBlocks G (pushTypes sig DPre) DMid DPost bs
    have hk := wfCheck_shiftLabelsTFlat G (pushTypes sig DPre) DMid DPost k
    rw [pushTypes_length] at hb hk
    rw [pushTypes_append, pushTypes_append, hb, hk]

private theorem wfCheckB_shiftLabelsTBlocks {rs : List Ty} (G : List Ty)
    (DPre DMid DPost : List (List Ty)) :
    {sig : List (List Ty)} → (bs : TBlocks rs sig) →
    (shiftLabelsTBlocks DPre.length DMid.length bs).wfCheck G (DPre ++ (DMid ++ DPost)) =
      bs.wfCheck G (DPre ++ DPost)
  | _, .nil => by unfold shiftLabelsTBlocks; rfl
  | _, .cons b bs => by
    unfold shiftLabelsTBlocks
    rw [wfCheckB_cons_eq, wfCheckB_cons_eq, wfCheck_shiftLabelsTFlat _ DPre DMid DPost b,
      wfCheckB_shiftLabelsTBlocks G DPre DMid DPost bs]
end

mutual
private theorem denote_shiftLabelsTFlat (V : Ty → Type) (L : List Ty → Type) {rs : List Ty} :
    (tf : TFlat rs) → (vs : List ((t : Ty) × V t)) →
    (lsPre lsMid lsPost : List ((ts : List Ty) × L ts)) →
    denote V L (shiftLabelsTFlat lsPre.length lsMid.length tf) vs
      (lsPre ++ (lsMid ++ lsPost)) =
      denote V L tf vs (lsPre ++ lsPost)
  | .let_ op k, vs, lsPre, lsMid, lsPost => by
    unfold shiftLabelsTFlat; rw [denote_let_eq, denote_let_eq]
    cases denoteArgs vs op.args with
    | none => rfl
    | some _ =>
      dsimp only; congr 1; funext res
      exact denote_shiftLabelsTFlat V L k (pushTup res vs) lsPre lsMid lsPost
  | .load t a k, vs, lsPre, lsMid, lsPost => by
    unfold shiftLabelsTFlat; rw [denote_load_eq, denote_load_eq]
    cases denoteArg vs a with
    | none => rfl
    | some _ =>
      dsimp only; congr 1; funext v
      exact denote_shiftLabelsTFlat V L k (⟨t, v⟩ :: vs) lsPre lsMid lsPost
  | .store v a k, vs, lsPre, lsMid, lsPost => by
    unfold shiftLabelsTFlat; rw [denote_store_eq, denote_store_eq,
      denote_shiftLabelsTFlat V L k vs lsPre lsMid lsPost]
  | .call f bs args k, vs, lsPre, lsMid, lsPost => by
    unfold shiftLabelsTFlat; rw [denote_call_eq, denote_call_eq]
    cases denoteArgs vs args with
    | none => rfl
    | some _ =>
      dsimp only; congr 1; funext res
      exact denote_shiftLabelsTFlat V L k (pushTup res vs) lsPre lsMid lsPost
  | .jnz c t e, vs, lsPre, lsMid, lsPost => by
    unfold shiftLabelsTFlat; rw [denote_jnz_eq, denote_jnz_eq,
      denote_shiftLabelsTFlat V L t vs lsPre lsMid lsPost,
      denote_shiftLabelsTFlat V L e vs lsPre lsMid lsPost]
  | .jump (ts := ts) j args, vs, lsPre, lsMid, lsPost => by
    unfold shiftLabelsTFlat
    by_cases hj : j ≥ lsPre.length
    · rw [ite_eq_left (by simp [hj]), denote_jump_eq, denote_jump_eq,
        lookupL_append_mid_ge lsPre lsMid lsPost ts hj]
    · rw [ite_eq_right (by simp [hj]), denote_jump_eq, denote_jump_eq,
        lookupL_append_mid_lt lsPre lsMid lsPost ts (by omega)]
  | .ret _, _, _, _, _ | .exit _ _, _, _, _, _ | .hlt, _, _, _, _ => by
    unfold shiftLabelsTFlat; rfl
  | .group (sig := sig) bs k, vs, lsPre, lsMid, lsPost => by
    unfold shiftLabelsTFlat; rw [denote_group_eq, denote_group_eq]
    congr 1
    · funext Js
      have hb := denoteB_shiftLabelsTBlocks V L bs vs (pushTup Js lsPre) lsMid lsPost
      rw [pushTup_length] at hb
      rw [pushTup_append, pushTup_append]; exact hb
    · funext Js
      have hk := denote_shiftLabelsTFlat V L k vs (pushTup Js lsPre) lsMid lsPost
      rw [pushTup_length] at hk
      rw [pushTup_append, pushTup_append]; exact hk

private theorem denoteB_shiftLabelsTBlocks (V : Ty → Type) (L : List Ty → Type) {rs : List Ty} :
    {sig : List (List Ty)} → (bs : TBlocks rs sig) → (vs : List ((t : Ty) × V t)) →
    (lsPre lsMid lsPost : List ((ts : List Ty) × L ts)) →
    denoteB V L (shiftLabelsTBlocks lsPre.length lsMid.length bs) vs
      (lsPre ++ (lsMid ++ lsPost)) =
      denoteB V L bs vs (lsPre ++ lsPost)
  | _, .nil, _, _, _, _ => by unfold shiftLabelsTBlocks; rfl
  | _, .cons b bs, vs, lsPre, lsMid, lsPost => by
    unfold shiftLabelsTBlocks; rw [denoteB_cons_eq, denoteB_cons_eq]
    congr 1
    · funext xs; exact denote_shiftLabelsTFlat V L b (pushTup xs vs) lsPre lsMid lsPost
    · exact denoteB_shiftLabelsTBlocks V L bs vs lsPre lsMid lsPost
end

mutual
private theorem callsOk_shiftLabelsTFlat {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (dl nl : Nat) : (tf : TFlat rs) →
    PassFlatKit.callsOkTF allowed exits tf →
    PassFlatKit.callsOkTF allowed exits (shiftLabelsTFlat dl nl tf)
  | .let_ _ k, h => by
    unfold shiftLabelsTFlat; simp only [PassFlatKit.callsOkTF_let] at h ⊢
    exact callsOk_shiftLabelsTFlat dl nl k h
  | .load _ _ k, h => by
    unfold shiftLabelsTFlat; simp only [PassFlatKit.callsOkTF_load] at h ⊢
    exact callsOk_shiftLabelsTFlat dl nl k h
  | .store _ _ k, h => by
    unfold shiftLabelsTFlat; simp only [PassFlatKit.callsOkTF_store] at h ⊢
    exact callsOk_shiftLabelsTFlat dl nl k h
  | .call _ _ _ k, h => by
    unfold shiftLabelsTFlat; simp only [PassFlatKit.callsOkTF_call] at h ⊢
    exact ⟨h.1, callsOk_shiftLabelsTFlat dl nl k h.2⟩
  | .jnz _ t e, h => by
    unfold shiftLabelsTFlat; simp only [PassFlatKit.callsOkTF_jnz] at h ⊢
    exact ⟨callsOk_shiftLabelsTFlat dl nl t h.1, callsOk_shiftLabelsTFlat dl nl e h.2⟩
  | .jump _ _, _ => by unfold shiftLabelsTFlat; split <;> simp
  | .ret _, _ | .hlt, _ => by unfold shiftLabelsTFlat; simp
  | .exit _ _, h => by unfold shiftLabelsTFlat; exact h
  | .group (sig := sig) bs k, h => by
    unfold shiftLabelsTFlat; simp only [PassFlatKit.callsOkTF_group] at h ⊢
    exact ⟨callsOkB_shiftLabelsTBlocks (dl + sig.length) nl bs h.1,
      callsOk_shiftLabelsTFlat (dl + sig.length) nl k h.2⟩

private theorem callsOkB_shiftLabelsTBlocks {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (dl nl : Nat) : {sig : List (List Ty)} → (bs : TBlocks rs sig) →
    PassFlatKit.callsOkBs allowed exits bs →
    PassFlatKit.callsOkBs allowed exits (shiftLabelsTBlocks dl nl bs)
  | _, .nil, _ => by unfold shiftLabelsTBlocks; trivial
  | _, .cons b bs, h => by
    unfold shiftLabelsTBlocks; simp only [PassFlatKit.callsOkBs_cons] at h ⊢
    exact ⟨callsOk_shiftLabelsTFlat dl nl b h.1, callsOkB_shiftLabelsTBlocks dl nl bs h.2⟩
end

private theorem wfCheck_stripJnzTrue {rs : List Ty} :
    (tf : TFlat rs) → (G : List Ty) → (D : List (List Ty)) →
    tf.wfCheck G D = true → (stripJnzTrue tf).wfCheck G D = true
  | .let_ _ k, G, D, h => by
    dsimp only [stripJnzTrue]; rw [wfCheck_let_eq, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, wfCheck_stripJnzTrue k _ D h.2⟩
  | .jnz _ _ _, G, D, h => by
    dsimp only [stripJnzTrue]; rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true] at h
    exact h.1.2
  | .load _ _ _, _, _, h | .store _ _ _, _, _, h | .call _ _ _ _, _, _, h
  | .jump _ _, _, _, h | .ret _, _, _, h | .exit _ _, _, _, h
  | .hlt, _, _, h | .group _ _, _, _, h => h

private theorem callsOk_stripJnzTrue {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} : (tf : TFlat rs) →
    PassFlatKit.callsOkTF allowed exits tf →
    PassFlatKit.callsOkTF allowed exits (stripJnzTrue tf)
  | .let_ _ k, h => by
    dsimp only [stripJnzTrue]; simp only [PassFlatKit.callsOkTF_let] at h ⊢
    exact callsOk_stripJnzTrue k h
  | .jnz _ _ _, h => by
    dsimp only [stripJnzTrue]; simp only [PassFlatKit.callsOkTF_jnz] at h
    exact h.1
  | .load _ _ _, h | .store _ _ _, h | .call _ _ _ _, h
  | .jump _ _, h | .ret _, h | .exit _ _, h | .hlt, h | .group _ _, h => h

private theorem wfCheck_checkJoinEntry0 {rs : List Ty} {GOuter : List Ty} {is32 : Bool} :
    (tf : TFlat rs) → {GLocal : List Ty} → {env : Array SymExt} →
    {DPre DMid DPost : List (List Ty)} → 1 ≤ DPre.length →
    checkJoinEntry0 is32 env DPre.length tf = true →
    tf.wfCheck (GLocal ++ (if is32 then i32 else i64) :: GOuter)
      (DPre ++ [if is32 then i32 else i64] :: DPost) = true →
    tf.wfCheck (GLocal ++ (if is32 then i32 else i64) :: GOuter)
      (DPre ++ [if is32 then i32 else i64] :: (DMid ++ DPost)) = true
  | .let_ (ts := ts) _ k, GLocal, _, DPre, DMid, DPost, h1, hc, hwf => by
    dsimp only [checkJoinEntry0] at hc; rw [Bool.and_eq_true] at hc
    rw [wfCheck_let_eq, Bool.and_eq_true] at hwf ⊢
    have hRec := wfCheck_checkJoinEntry0 k (GLocal := pushTypes ts GLocal) (DMid := DMid)
      (DPost := DPost) h1 hc.2 (by rw [← pushTypes_append]; exact hwf.2)
    rw [← pushTypes_append] at hRec
    exact ⟨hwf.1, hRec⟩
  | .load t _ k, GLocal, _, DPre, DMid, DPost, h1, hc, hwf => by
    dsimp only [checkJoinEntry0] at hc
    rw [wfCheck_load_eq, Bool.and_eq_true] at hwf ⊢
    have hRec := wfCheck_checkJoinEntry0 k (GLocal := t :: GLocal) (DMid := DMid)
      (DPost := DPost) h1 hc (by rw [List.cons_append]; exact hwf.2)
    rw [List.cons_append] at hRec
    exact ⟨hwf.1, hRec⟩
  | .store _ _ k, _, _, _, _, _, h1, hc, hwf => by
    dsimp only [checkJoinEntry0] at hc
    rw [wfCheck_store_eq, Bool.and_eq_true] at hwf ⊢
    exact ⟨hwf.1, wfCheck_checkJoinEntry0 k h1 hc hwf.2⟩
  | .jnz _ t e, _, _, _, _, _, h1, hc, hwf => by
    dsimp only [checkJoinEntry0] at hc; rw [Bool.and_eq_true] at hc
    rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true] at hwf ⊢
    exact ⟨⟨hwf.1.1, wfCheck_checkJoinEntry0 t h1 hc.1 hwf.1.2⟩,
      wfCheck_checkJoinEntry0 e h1 hc.2 hwf.2⟩
  | .jump j args, _, _, DPre, DMid, DPost, h1, hc, hwf => by
    dsimp only [checkJoinEntry0] at hc
    by_cases hj0 : j == 0
    · rw [wfCheck_jump_eq, Bool.and_eq_true] at hwf ⊢
      have hEq0 : j = 0 := beq_iff_eq.mp hj0; subst hEq0
      rcases DPre with _ | ⟨d0, dr⟩; · simp at h1
      simp only [List.cons_append, listGet?_cons_zero_eq] at hwf ⊢; exact hwf
    · rw [ite_eq_right (by simp [hj0])] at hc
      by_cases hjT : j == DPre.length
      · have hEqT : j = DPre.length := beq_iff_eq.mp hjT; subst hEqT
        rw [wfCheck_jump_eq, Bool.and_eq_true] at hwf ⊢
        have hL1 : listGet? (DPre ++ [if is32 then i32 else i64] :: DPost) DPre.length =
            some [if is32 then i32 else i64] := by
          rw [listGet?_append_drop DPre _ DPre.length (Nat.le_refl _), Nat.sub_self,
            listGet?_cons_zero_eq]
        have hL2 : listGet? (DPre ++ [if is32 then i32 else i64] :: (DMid ++ DPost)) DPre.length =
            some [if is32 then i32 else i64] := by
          rw [listGet?_append_drop DPre _ DPre.length (Nat.le_refl _), Nat.sub_self,
            listGet?_cons_zero_eq]
        rw [hL1] at hwf; rw [hL2]; exact hwf
      · rw [ite_eq_right (by simp [hjT])] at hc; cases hc
  | .call _ _ _ _, _, _, _, _, _, _, hc, _ | .ret _, _, _, _, _, _, _, hc, _
  | .exit _ _, _, _, _, _, _, _, hc, _ | .hlt, _, _, _, _, _, _, hc, _
  | .group _ _, _, _, _, _, _, _, hc, _ => by
    dsimp only [checkJoinEntry0] at hc; cases hc

private theorem checkTrueArmCounted_group_one {rs : List Ty} (is32 : Bool)
    (env : Array SymExt) (l : Nat) (ts1 : List Ty) (b1 k1 : TFlat rs) :
    checkTrueArmCounted is32 env l (.group (sig := [ts1]) (.cons b1 .nil) k1) =
      (zpJumps 0 b1 == 0 &&
        checkTrueArmCounted is32 (env ++ (ts1.map fun _ => .other).toArray) (l + 1) b1 &&
        checkJoinEntry0 is32 env (l + 1) k1) := rfl

private theorem wfCheck_checkTrueArmCounted {rs : List Ty} {GOuter : List Ty} {is32 : Bool} :
    (tf : TFlat rs) → {GLocal : List Ty} → {env : Array SymExt} →
    {DPre DMid DPost : List (List Ty)} →
    checkTrueArmCounted is32 env DPre.length tf = true →
    tf.wfCheck (GLocal ++ (if is32 then i32 else i64) :: GOuter)
      (DPre ++ [if is32 then i32 else i64] :: DPost) = true →
    tf.wfCheck (GLocal ++ (if is32 then i32 else i64) :: GOuter)
      (DPre ++ [if is32 then i32 else i64] :: (DMid ++ DPost)) = true
  | .let_ (ts := ts) _ k, GLocal, _, DPre, DMid, DPost, hc, hwf => by
    dsimp only [checkTrueArmCounted] at hc; rw [Bool.and_eq_true] at hc
    rw [wfCheck_let_eq, Bool.and_eq_true] at hwf ⊢
    have hRec := wfCheck_checkTrueArmCounted k (GLocal := pushTypes ts GLocal) (DMid := DMid)
      (DPost := DPost) hc.2 (by rw [← pushTypes_append]; exact hwf.2)
    rw [← pushTypes_append] at hRec
    exact ⟨hwf.1, hRec⟩
  | .load t _ k, GLocal, _, DPre, DMid, DPost, hc, hwf => by
    dsimp only [checkTrueArmCounted] at hc
    rw [wfCheck_load_eq, Bool.and_eq_true] at hwf ⊢
    have hRec := wfCheck_checkTrueArmCounted k (GLocal := t :: GLocal) (DMid := DMid)
      (DPost := DPost) hc (by rw [List.cons_append]; exact hwf.2)
    rw [List.cons_append] at hRec
    exact ⟨hwf.1, hRec⟩
  | .store _ _ k, _, _, _, _, _, hc, hwf => by
    dsimp only [checkTrueArmCounted] at hc
    rw [wfCheck_store_eq, Bool.and_eq_true] at hwf ⊢
    exact ⟨hwf.1, wfCheck_checkTrueArmCounted k hc hwf.2⟩
  | .jnz _ t e, _, _, _, _, _, hc, hwf => by
    dsimp only [checkTrueArmCounted] at hc; rw [Bool.and_eq_true] at hc
    rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true] at hwf ⊢
    exact ⟨⟨hwf.1.1, wfCheck_checkTrueArmCounted t hc.1 hwf.1.2⟩,
      wfCheck_checkTrueArmCounted e hc.2 hwf.2⟩
  | .jump j _, _, _, DPre, DMid, DPost, hc, hwf => by
    dsimp only [checkTrueArmCounted] at hc; rw [Bool.and_eq_true] at hc
    have hEqT : j = DPre.length := beq_iff_eq.mp hc.1; subst hEqT
    rw [wfCheck_jump_eq, Bool.and_eq_true] at hwf ⊢
    have hL1 : listGet? (DPre ++ [if is32 then i32 else i64] :: DPost) DPre.length =
        some [if is32 then i32 else i64] := by
      rw [listGet?_append_drop DPre _ DPre.length (Nat.le_refl _), Nat.sub_self,
        listGet?_cons_zero_eq]
    have hL2 : listGet? (DPre ++ [if is32 then i32 else i64] :: (DMid ++ DPost)) DPre.length =
        some [if is32 then i32 else i64] := by
      rw [listGet?_append_drop DPre _ DPre.length (Nat.le_refl _), Nat.sub_self,
        listGet?_cons_zero_eq]
    rw [hL1] at hwf; rw [hL2]; exact hwf
  | .group (sig := [ts1]) (.cons b1 .nil) k, GLocal, env, DPre, DMid, DPost, hc, hwf => by
    rw [checkTrueArmCounted_group_one] at hc; rw [Bool.and_eq_true, Bool.and_eq_true] at hc
    rw [wfCheck_group_eq, wfCheckB_cons_nil, Bool.and_eq_true] at hwf ⊢
    have hb := wfCheck_checkTrueArmCounted b1 (GLocal := pushTypes ts1 GLocal)
      (DPre := ts1 :: DPre) (DMid := DMid) (DPost := DPost) hc.1.2
      (by rw [← pushTypes_append]; exact hwf.1)
    have hk := wfCheck_checkJoinEntry0 k (GLocal := GLocal) (DPre := ts1 :: DPre) (DMid := DMid)
      (DPost := DPost) (by simp) hc.2 (by simpa [pushTypes] using hwf.2)
    rw [← pushTypes_append] at hb
    exact ⟨hb, by simpa [pushTypes] using hk⟩
  | .group .nil _, _, _, _, _, _, hc, _
  | .group (.cons _ (.cons _ _)) _, _, _, _, _, _, hc, _
  | .call _ _ _ _, _, _, _, _, _, hc, _ | .ret _, _, _, _, _, _, hc, _
  | .exit _ _, _, _, _, _, _, hc, _ | .hlt, _, _, _, _, _, hc, _ => by
    change false = true at hc; cases hc

mutual
private theorem wfCheck_inlineJumpTarget {rs : List Ty} (nextBody : TFlat rs) (ivTy : Ty)
    {GOuter : List Ty} {DOuter : List (List Ty)}
    (hNext : nextBody.wfCheck (ivTy :: GOuter) ([ivTy] :: DOuter) = true) :
    (tf : TFlat rs) → (GLocal : List Ty) → (DPre : List (List Ty)) →
    tf.wfCheck (GLocal ++ ivTy :: GOuter) (DPre ++ [ivTy] :: DOuter) = true →
    (inlineJumpTarget nextBody ivTy DPre.length GLocal.length tf).wfCheck
      (GLocal ++ ivTy :: GOuter) (DPre ++ [ivTy] :: DOuter) = true
  | .let_ (ts := ts) op k, GLocal, DPre, h => by
    dsimp only [inlineJumpTarget]; rw [wfCheck_let_eq, Bool.and_eq_true] at h ⊢
    refine ⟨h.1, ?_⟩
    have hk := wfCheck_inlineJumpTarget nextBody ivTy hNext k (pushTypes ts GLocal) DPre
      (by rw [← pushTypes_append]; exact h.2)
    rwa [← pushTypes_append, pushTypes_length] at hk
  | .load t a k, GLocal, DPre, h => by
    dsimp only [inlineJumpTarget]; rw [wfCheck_load_eq, Bool.and_eq_true] at h ⊢
    refine ⟨h.1, ?_⟩
    have hk := wfCheck_inlineJumpTarget nextBody ivTy hNext k (t :: GLocal) DPre h.2
    rwa [List.length_cons] at hk
  | .store v a k, GLocal, DPre, h => by
    dsimp only [inlineJumpTarget]; rw [wfCheck_store_eq, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, wfCheck_inlineJumpTarget nextBody ivTy hNext k GLocal DPre h.2⟩
  | .call f bs args k, GLocal, DPre, h => by
    dsimp only [inlineJumpTarget]; rw [wfCheck_call_eq, Bool.and_eq_true] at h ⊢
    refine ⟨h.1, ?_⟩
    have hk := wfCheck_inlineJumpTarget nextBody ivTy hNext k (pushTypes bs GLocal) DPre
      (by rw [← pushTypes_append]; exact h.2)
    rwa [← pushTypes_append, pushTypes_length] at hk
  | .jnz c t e, GLocal, DPre, h => by
    dsimp only [inlineJumpTarget]
    rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true] at h ⊢
    exact ⟨⟨h.1.1, wfCheck_inlineJumpTarget nextBody ivTy hNext t GLocal DPre h.1.2⟩,
      wfCheck_inlineJumpTarget nextBody ivTy hNext e GLocal DPre h.2⟩
  | .jump (ts := ts) j args, GLocal, DPre, h => by
    dsimp only [inlineJumpTarget]
    by_cases hj : (j == DPre.length) = true
    · have hjEq : j = DPre.length := beq_iff_eq.mp hj; subst hjEq
      rw [ite_eq_left hj]
      rw [wfCheck_jump_eq, Bool.and_eq_true, listGet?_append_drop DPre _ DPre.length
        (Nat.le_refl _), Nat.sub_self, listGet?_cons_zero_eq] at h
      dsimp only at h
      have hTs : ts = [ivTy] := by
        cases hdec : listTyDecEq [ivTy] ts with
        | isTrue heq => exact heq.symm
        | isFalse _ => rw [hdec] at h; cases h.1
      rw [dite_eq_left hTs]; subst hTs
      refine wfCheck_letBindTup args [] (GLocal ++ ivTy :: GOuter) _ h.2 ?_
      have hSh := wfCheck_shiftTFlat [ivTy] (GLocal ++ [ivTy]) GOuter
        (DPre ++ [ivTy] :: DOuter) (shiftLabelsTFlat 0 DPre.length nextBody)
      rw [List.length_singleton, List.length_append, List.length_singleton] at hSh
      rw [List.append_assoc] at hSh; simp only [List.singleton_append] at hSh
      rw [List.nil_append, pushTypes_cons_eq, pushTypes_nil_eq, hSh]
      have hShL := wfCheck_shiftLabelsTFlat (ivTy :: GOuter) [] DPre ([ivTy] :: DOuter) nextBody
      rw [List.length_nil, List.nil_append, List.nil_append] at hShL
      rw [hShL]; exact hNext
    · rw [ite_eq_right hj]; exact h
  | .ret _, _, _, h | .exit _ _, _, _, h | .hlt, _, _, h => h
  | .group (sig := sig) bs k, GLocal, DPre, h => by
    dsimp only [inlineJumpTarget]; rw [wfCheck_group_eq, Bool.and_eq_true] at h ⊢
    have hb := wfCheckB_inlineJumpTargetB nextBody ivTy hNext bs GLocal (pushTypes sig DPre)
      (by rw [← pushTypes_append]; exact h.1)
    have hk := wfCheck_inlineJumpTarget nextBody ivTy hNext k GLocal (pushTypes sig DPre)
      (by rw [← pushTypes_append]; exact h.2)
    rw [pushTypes_length] at hb hk
    rw [← pushTypes_append] at hb hk
    exact ⟨hb, hk⟩

private theorem wfCheckB_inlineJumpTargetB {rs : List Ty} (nextBody : TFlat rs) (ivTy : Ty)
    {GOuter : List Ty} {DOuter : List (List Ty)}
    (hNext : nextBody.wfCheck (ivTy :: GOuter) ([ivTy] :: DOuter) = true) :
    {sig : List (List Ty)} → (bs : TBlocks rs sig) → (GLocal : List Ty) → (DPre : List (List Ty)) →
    bs.wfCheck (GLocal ++ ivTy :: GOuter) (DPre ++ [ivTy] :: DOuter) = true →
    (inlineJumpTargetB nextBody ivTy DPre.length GLocal.length bs).wfCheck
      (GLocal ++ ivTy :: GOuter) (DPre ++ [ivTy] :: DOuter) = true
  | _, .nil, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, GLocal, DPre, h => by
    dsimp only [inlineJumpTargetB]; rw [wfCheckB_cons_eq, Bool.and_eq_true] at h ⊢
    have hb := wfCheck_inlineJumpTarget nextBody ivTy hNext b (pushTypes ts GLocal) DPre
      (by rw [← pushTypes_append]; exact h.1)
    rw [pushTypes_length, ← pushTypes_append] at hb
    exact ⟨hb, wfCheckB_inlineJumpTargetB nextBody ivTy hNext bs GLocal DPre h.2⟩
end

private theorem wfCheck_mkUnrollChain {rs : List Ty} (stepBody : TFlat rs) (ivTy : Ty)
    {GOuter : List Ty} {DOuter : List (List Ty)}
    (hStep : stepBody.wfCheck (ivTy :: GOuter) ([ivTy] :: DOuter) = true) :
    ∀ u : Nat, (mkUnrollChain stepBody ivTy u).wfCheck (ivTy :: GOuter) ([ivTy] :: DOuter) = true
  | 0 => by
    dsimp only [mkUnrollChain]
    rw [wfCheck_jump_eq, listGet?_cons_zero_eq]; dsimp only [checkArgs, checkArg, listGet?]
    cases listTyDecEq [ivTy] [ivTy] with
    | isFalse h => exact absurd rfl h
    | isTrue _ =>
      cases tyDecEq ivTy ivTy with
      | isFalse h => exact absurd rfl h
      | isTrue _ => rfl
  | u + 1 => by
    dsimp only [mkUnrollChain]
    exact wfCheck_inlineJumpTarget (mkUnrollChain stepBody ivTy u) ivTy
      (wfCheck_mkUnrollChain stepBody ivTy hStep u) stepBody [] [] hStep

/-! ## Section 3: `unrollCountedSingle_wf`, `matchCountedBody_spec`, & `inlineJumpTarget_wp` -/

private theorem matchCountedBody_wf {rs : List Ty} {GOuter : List Ty} {D : List (List Ty)}
    {is32 : Bool} {fb : FillBound} :
    (tf : TFlat rs) → {GLocal : List Ty} → {env : Array SymExt} →
    SymExtEnvWf GOuter GLocal env →
    tf.wfCheck (GLocal ++ (if is32 then i32 else i64) :: GOuter) D = true →
    matchCountedBody is32 env tf = some fb →
    FillBoundWf GOuter is32 fb
  | .let_ op k, GLocal, env, hwf, htf, hm => by
    rw [wfCheck_let_eq, Bool.and_eq_true] at htf
    dsimp only [matchCountedBody] at hm
    by_cases hp : isTotalPureOp op.code = true
    · rw [ite_eq_left hp] at hm
      have hk := htf.2; rw [pushTypes_append] at hk
      exact matchCountedBody_wf k (evalSymOpExt_wf hwf op htf.1) hk hm
    · rw [ite_eq_right hp] at hm; cases hm
  | .jnz c t _, GLocal, env, hwf, htf, hm => by
    rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true] at htf
    dsimp only [matchCountedBody] at hm
    split at hm
    · have hcb : SymExtOuterOk GOuter (argToSym is32 env c) := argToSym_wf hwf htf.1.1
      cases hc : argToSym is32 env c <;> rw [hc] at hm hcb <;>
        first
        | cases hm
        | (cases is32 <;> simp at hm; subst hm; exact ⟨rfl, hcb⟩)
    · cases hm
  | .load _ _ _, _, _, _, _, hm | .store _ _ _, _, _, _, _, hm
  | .call _ _ _ _, _, _, _, _, hm | .jump _ _, _, _, _, _, hm
  | .ret _, _, _, _, _, hm | .exit _ _, _, _, _, _, hm
  | .hlt, _, _, _, _, hm | .group _ _, _, _, _, _, hm => by
    dsimp only [matchCountedBody] at hm; cases hm

private theorem matchCountedBody_checkTrueArm {rs : List Ty} {is32 : Bool} {fb : FillBound} :
    (tf : TFlat rs) → {env : Array SymExt} →
    matchCountedBody is32 env tf = some fb →
    checkTrueArmCounted is32 env 0 (stripJnzTrue tf) = true
  | .let_ op k, env, hm => by
    dsimp only [matchCountedBody] at hm
    by_cases hp : isTotalPureOp op.code = true
    · rw [ite_eq_left hp] at hm
      dsimp only [stripJnzTrue, checkTrueArmCounted]
      rw [Bool.and_eq_true]
      exact ⟨hp, matchCountedBody_checkTrueArm k hm⟩
    · rw [ite_eq_right hp] at hm; cases hm
  | .jnz _ t _, env, hm => by
    dsimp only [matchCountedBody] at hm
    split at hm
    · next hc => rw [Bool.and_eq_true] at hc; exact hc.2
    · cases hm
  | .load _ _ _, _, hm | .store _ _ _, _, hm | .call _ _ _ _, _, hm | .jump _ _, _, hm
  | .ret _, _, hm | .exit _ _, _, hm | .hlt, _, hm | .group _ _, _, hm => by
    dsimp only [matchCountedBody] at hm; cases hm

private abbrev IvTy (is32 : Bool) : Ty := if is32 then i32 else i64

private def mkFBTy : (is32 : Bool) → Bool → Arg K (IvTy is32) → FillBound
  | true => .b32
  | false => .b64

private def bvToNatW : {is32 : Bool} → Val (IvTy is32) → Nat
  | true, v => v.toNat
  | false, v => v.toNat

private theorem bvToNatW_lt : ∀ {is32 : Bool} (v : Val (IvTy is32)),
    bvToNatW v < 2 ^ (if is32 then 32 else 64)
  | true, v => v.isLt
  | false, v => v.isLt

private theorem checkArg_bits_var0 (G : List Ty) (w : Nat) :
    checkArg (.bits w :: G) (.bits w) (.var 0) = true := by
  dsimp only [checkArg, listGet?]
  cases tyDecEq (.bits w) (.bits w) with
  | isTrue _ => rfl
  | isFalse h => exact absurd rfl h

private theorem checkArg_bits_var2 (G : List Ty) (t0 t1 : Ty) (w : Nat) :
    checkArg (t0 :: t1 :: .bits w :: G) (.bits w) (.var 2) = true := by
  dsimp only [checkArg, listGet?]
  cases tyDecEq (.bits w) (.bits w) with
  | isTrue _ => rfl
  | isFalse h => exact absurd rfl h

private theorem unrollCountedSingle_eq_some {unrollN : Nat} {rs ts0 : List Ty}
    {body k res : TFlat rs}
    (hu : unrollCountedSingle unrollN ts0 body k = some res) :
    2 ≤ unrollN ∧ unrollN ≤ 64 ∧
    zpLoops (stripJnzTrue body) = 0 ∧ zpSize (stripJnzTrue body) ≤ 64 ∧
    hasStore (stripJnzTrue body) = true ∧
    let u := if zpSize (stripJnzTrue body) ≤ 36 then min unrollN 4 else min unrollN 2
    2 ≤ u ∧ u ≤ 4 ∧
    ((∃ (initArg bnd : Arg K i32) (isLt : Bool),
        ts0 = [i32] ∧ k = .jump (ts := [i32]) 0 (initArg, ()) ∧
        matchCountedBody true #[] body = some (.b32 isLt bnd) ∧
        res = .group (sig := [[i32]]) (.cons body .nil)
          (mkUnrollWrapper 32 isLt initArg bnd body u)) ∨
     (∃ (initArg bnd : Arg K i64) (isLt : Bool),
        ts0 = [i64] ∧ k = .jump (ts := [i64]) 0 (initArg, ()) ∧
        matchCountedBody false #[] body = some (.b64 isLt bnd) ∧
        res = .group (sig := [[i64]]) (.cons body .nil)
          (mkUnrollWrapper 64 isLt initArg bnd body u))) := by
  dsimp only [unrollCountedSingle] at hu
  by_cases h1 : (unrollN < 2 || unrollN > 64) = true
  · rw [ite_eq_left h1] at hu; cases hu
  · rw [ite_eq_right h1] at hu
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at h1
    by_cases h2 : (zpLoops (stripJnzTrue body) > 0 || zpSize (stripJnzTrue body) > 64 ||
        !hasStore (stripJnzTrue body)) = true
    · rw [ite_eq_left h2] at hu; cases hu
    · rw [ite_eq_right h2] at hu
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or, not_lt] at h2
      let u := if zpSize (stripJnzTrue body) ≤ 36 then min unrollN 4 else min unrollN 2
      have hu2 : 2 ≤ u := by dsimp only [u]; split <;> omega
      have hu4 : u ≤ 4 := by dsimp only [u]; split <;> omega
      have hNot : ¬ (u < 2) := by omega
      change (if u < 2 then none else _) = some res at hu
      simp only [hNot, ↓reduceIte] at hu
      have hStore : hasStore (stripJnzTrue body) = true := by
        cases hS : hasStore (stripJnzTrue body) <;> simp_all
      refine ⟨h1.1, h1.2, by omega, h2.1.2, hStore, hu2, hu4, ?_⟩
      rcases ts0 with _ | ⟨t0, _ | _⟩
      · cases hu
      · cases t0 with
        | bits w =>
          by_cases hw32 : w = 32
          · subst hw32
            cases k with
            | jump j args =>
              rename_i tsJ
              rcases tsJ with _ | ⟨tj, _ | _⟩
              · cases hu
              · cases tj with
                | bits wj =>
                  by_cases hwj : wj = 32
                  · subst hwj
                    by_cases hj0 : j = 0
                    · subst hj0; rcases args with ⟨initArg, ⟨⟩⟩
                      cases hm : matchCountedBody true #[] body with
                      | none => simp [hm] at hu
                      | some fb =>
                        cases fb with
                        | b64 _ _ => simp [hm] at hu
                        | b32 isLt bnd =>
                          simp [hm] at hu; subst hu
                          exact Or.inl ⟨initArg, bnd, isLt, rfl, rfl, rfl, rfl⟩
                    · cases j <;> simp_all
                  · simp [hwj] at hu
                | bool | float _ | pair _ _ => cases hu
              · simp at hu
            | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ _ | jnz _ _ _ | ret _
            | exit _ _ | hlt | group _ _ => cases hu
          · by_cases hw64 : w = 64
            · subst hw64
              cases k with
              | jump j args =>
                rename_i tsJ
                rcases tsJ with _ | ⟨tj, _ | _⟩
                · cases hu
                · cases tj with
                  | bits wj =>
                    by_cases hwj : wj = 64
                    · subst hwj
                      by_cases hj0 : j = 0
                      · subst hj0; rcases args with ⟨initArg, ⟨⟩⟩
                        cases hm : matchCountedBody false #[] body with
                        | none => simp [hm] at hu
                        | some fb =>
                          cases fb with
                          | b32 _ _ => simp [hm] at hu
                          | b64 isLt bnd =>
                            simp [hm] at hu; subst hu
                            exact Or.inr ⟨initArg, bnd, isLt, rfl, rfl, rfl, rfl⟩
                      · cases j <;> simp_all
                    · simp [hwj] at hu
                  | bool | float _ | pair _ _ => cases hu
                · simp at hu
              | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ _ | jnz _ _ _ | ret _
              | exit _ _ | hlt | group _ _ => cases hu
            · simp [hw32, hw64] at hu
        | bool | float _ | pair _ _ => cases hu
      · cases k <;> simp at hu

private theorem wfCheck_mkUnrollWrapper {rs : List Ty} {GOuter : List Ty}
    {DOuter : List (List Ty)} {w : Nat} {isLt : Bool} {initArg bnd : Arg K (.bits w)}
    {body : TFlat rs} {u : Nat}
    (hInitWf : checkArg GOuter (.bits w) initArg = true)
    (hBndWf : checkArg GOuter (.bits w) bnd = true)
    (hChainWf : (mkUnrollChain (stripJnzTrue body) (.bits w) u).wfCheck
      (.bits w :: GOuter) ([.bits w] :: [.bits w] :: DOuter) = true) :
    (mkUnrollWrapper w isLt initArg bnd body u).wfCheck GOuter ([.bits w] :: DOuter) = true := by
  dsimp only [mkUnrollWrapper]; rw [wfCheck_group_eq, wfCheckB_cons_nil, Bool.and_eq_true]
  have hVar0 := checkArg_bits_var0 GOuter w
  have hVar0b := checkArg_bits_var0 (.bits w :: GOuter) w
  have hVar2 := checkArg_bits_var2 GOuter Ty.bool (.bits w) w
  constructor
  · rw [wfCheck_let_eq]; dsimp only [op2]
    rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
    have hB1 : checkArg (pushTypes [.bits w] GOuter) (.bits w) (tArgShift 1 bnd) = true := by
      change checkArg ([.bits w] ++ GOuter) (.bits w)
        (tArgShift ([.bits w] : List Ty).length bnd) = true
      rw [wfCheck_tArgShift]; exact hBndWf
    refine ⟨⟨hB1, hVar0⟩, ?_⟩
    rw [wfCheck_let_eq]; dsimp only [op2]
    rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨hVar0b, rfl⟩, ?_⟩
    rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨rfl, ?_⟩, ?_⟩
    · rw [wfCheck_let_eq, Bool.and_eq_true]; dsimp only [op1, checkArgs]; rw [Bool.and_true]
      refine ⟨hVar2, ?_⟩
      have hSh := wfCheck_shiftTFlat [.bits w] [Ty.bool, .bits w, .bits w] GOuter
        ([.bits w] :: [.bits w] :: DOuter) (mkUnrollChain (stripJnzTrue body) (.bits w) u)
      rw [List.length_singleton] at hSh; exact hSh.trans hChainWf
    · rw [wfCheck_jump_eq, Bool.and_eq_true]; dsimp only [pushTypes]
      rw [listGet?_cons_succ_eq, listGet?_cons_zero_eq]; dsimp only
      cases listTyDecEq [.bits w] [.bits w] with
      | isFalse h => exact absurd rfl h
      | isTrue _ => exact ⟨rfl, by simp [checkArgs, hVar2]⟩
  · rw [wfCheck_let_eq]; dsimp only [op2]
    rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨hInitWf, hBndWf⟩, ?_⟩
    rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true]
    have hISh : checkArg (pushTypes [.bool] GOuter) (.bits w) (tArgShift 1 initArg) = true := by
      change checkArg ([.bool] ++ GOuter) (.bits w)
        (tArgShift ([.bool] : List Ty).length initArg) = true
      rw [wfCheck_tArgShift]; exact hInitWf
    dsimp only [pushTypes] at hISh
    refine ⟨⟨rfl, ?_⟩, ?_⟩
    · rw [wfCheck_jump_eq, Bool.and_eq_true]; dsimp only [pushTypes]
      rw [listGet?_cons_zero_eq]; dsimp only
      cases listTyDecEq [.bits w] [.bits w] with
      | isFalse h => exact absurd rfl h
      | isTrue _ => exact ⟨rfl, by simp [checkArgs, hISh]⟩
    · rw [wfCheck_jump_eq, Bool.and_eq_true]; dsimp only [pushTypes]
      rw [listGet?_cons_succ_eq, listGet?_cons_zero_eq]; dsimp only
      cases listTyDecEq [.bits w] [.bits w] with
      | isFalse h => exact absurd rfl h
      | isTrue _ => exact ⟨rfl, by simp [checkArgs, hISh]⟩

public theorem unrollCountedSingle_wf {unrollN : Nat} {rs ts0 : List Ty}
    {GOuter : List Ty} {DOuter : List (List Ty)} {body k res : TFlat rs}
    (hwf : TFlat.wfCheck GOuter DOuter (.group (@TBlocks.cons rs ts0 [] body .nil) k) = true)
    (hu : unrollCountedSingle unrollN ts0 body k = some res) :
    res.wfCheck GOuter DOuter = true := by
  obtain ⟨_, _, _, _, _, _, _, hCase⟩ := unrollCountedSingle_eq_some hu
  have hEmpty : SymExtEnvWf GOuter [] #[] := ⟨rfl, fun _ h => by cases h⟩
  rw [wfCheck_group_eq, wfCheckB_cons_eq, wfCheckB_nil_eq, Bool.and_true, Bool.and_eq_true] at hwf
  have checkCase : ∀ (is32 : Bool) (w : Nat) (hw : IvTy is32 = .bits w)
      (initArg bnd : Arg K (.bits w)) (isLt : Bool) (u : Nat),
      body.wfCheck (pushTypes [.bits w] GOuter) (pushTypes [[.bits w]] DOuter) = true →
      k = .jump (ts := [.bits w]) 0 (initArg, ()) →
      matchCountedBody is32 #[] body = some (mkFBTy is32 isLt (hw ▸ bnd)) →
      (TFlat.group (sig := [[.bits w]]) (.cons body .nil)
        (mkUnrollWrapper w isLt initArg bnd body u)).wfCheck GOuter DOuter = true := by
    intro is32 w hw initArg bnd isLt u hwf1 hkEq hm
    subst hkEq
    have hwf2 := hwf.2; rw [wfCheck_jump_eq, Bool.and_eq_true] at hwf2
    have hInitWf : checkArg GOuter (.bits w) initArg = true := by
      simpa [pushTypes, checkArgs] using hwf2.2
    have hBndWf : checkArg GOuter (.bits w) bnd = true := by
      have hmWf := matchCountedBody_wf (GOuter := GOuter) (D := [[IvTy is32]] ++ DOuter)
        (is32 := is32) body hEmpty (by cases is32 <;> cases hw <;> exact hwf1) hm
      cases is32 <;> cases hw <;> exact hmWf.2
    let step := stripJnzTrue body
    have hStep0 : step.wfCheck (.bits w :: GOuter) ([.bits w] :: DOuter) = true :=
      wfCheck_stripJnzTrue body _ _ (by cases is32 <;> cases hw <;> exact hwf1)
    have hStep1 : step.wfCheck (.bits w :: GOuter) ([.bits w] :: [.bits w] :: DOuter) = true := by
      have hArm := matchCountedBody_checkTrueArm body hm
      have h := wfCheck_checkTrueArmCounted (GOuter := GOuter) (is32 := is32) step
        (GLocal := []) (DPre := []) (DMid := [[IvTy is32]]) (DPost := DOuter) hArm
        (by cases is32 <;> cases hw <;> exact hStep0)
      cases is32 <;> cases hw <;> exact h
    rw [wfCheck_group_eq, wfCheckB_cons_nil, Bool.and_eq_true]
    exact ⟨hwf1, wfCheck_mkUnrollWrapper hInitWf hBndWf
      (wfCheck_mkUnrollChain step (.bits w) hStep1 u)⟩
  rcases hCase with ⟨initArg, bnd, isLt, rfl, rfl, hm, rfl⟩ |
      ⟨initArg, bnd, isLt, rfl, rfl, hm, rfl⟩
  · exact checkCase true 32 rfl initArg bnd isLt _ hwf.1 rfl hm
  · exact checkCase false 64 rfl initArg bnd isLt _ hwf.1 rfl hm

private theorem opCode_wp_totalPure_det : {as rs : List Ty} → (c : OpCode as rs) →
    isTotalPureOp c = true → ∀ (args : Tup Val as) (p : Tup Val rs → Prop),
    c.wp args p →
    ∃ v : Tup Val rs, ∀ q : Tup Val rs → Prop, (q v → c.wp args q) ∧ (c.wp args q → q v)
  | _, _, .copy _, _, (_, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .add t, htot, (_, _, ()), p, hp | _, _, .sub t, htot, (_, _, ()), p, hp
  | _, _, .mul t, htot, (_, _, ()), p, hp | _, _, .shl t, htot, (_, _, ()), p, hp
  | _, _, .lshr t, htot, (_, _, ()), p, hp | _, _, .ashr t, htot, (_, _, ()), p, hp
  | _, _, .rotl t, htot, (_, _, ()), p, hp | _, _, .rotr t, htot, (_, _, ()), p, hp => by
    dsimp only [isTotalPureOp] at htot
    have hf : t.hasFloat = false := by cases ht : t.hasFloat <;> simp_all
    dsimp only [OpCode.wp] at hp ⊢; rw [hf] at hp ⊢; exact ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .neg t, htot, (_, ()), p, hp => by
    dsimp only [isTotalPureOp] at htot
    have hf : t.hasFloat = false := by cases ht : t.hasFloat <;> simp_all
    dsimp only [OpCode.wp] at hp ⊢; rw [hf] at hp ⊢; exact ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .and _, _, (_, _, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .or _, _, (_, _, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .xor _, _, (_, _, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .not _, _, (_, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .ternlog _ _, _, (_, _, _, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .fshl _, _, (_, _, _, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .fshr _, _, (_, _, _, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .clz _, _, (_, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .cls _, _, (_, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .rbit _, _, (_, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .ctz _, _, (_, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .popcnt _, _, (_, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .cmp _ t _ rfl, htot, (_, _, ()), p, hp => by
    dsimp only [isTotalPureOp] at htot
    have hf : t.hasFloat = false := by cases ht : t.hasFloat <;> simp_all
    dsimp only [OpCode.wp] at hp ⊢; rw [hf] at hp ⊢; exact ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .select _, _, (_, _, _, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .blend _ _ rfl, _, (_, _, _, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .zext _ _, _, (_, ()), p, hp => ⟨_, fun _ => ⟨fun h => ⟨hp.1, h⟩, fun h => h.2⟩⟩
  | _, _, .sext _ _, _, (_, ()), p, hp => ⟨_, fun _ => ⟨fun h => ⟨hp.1, h⟩, fun h => h.2⟩⟩
  | _, _, .trunc _ _, _, (_, ()), p, hp => ⟨_, fun _ => ⟨fun h => ⟨hp.1, h⟩, fun h => h.2⟩⟩
  | _, _, .ofBool _, _, (_, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .addc _, _, (_, _, _, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .subb _, _, (_, _, _, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .umulw _, _, (_, _, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .smulw _, _, (_, _, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .udiv0 _, _, (_, _, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .sdiv0 _, _, (_, _, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .mkpair _ _, _, (_, _, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .unpair _ _, _, (_, ()), p, hp => ⟨_, fun _ => ⟨id, id⟩⟩
  | _, _, .bswap _, htot, _, _, _ | _, _, .udiv _, htot, _, _, _
  | _, _, .sdiv _, htot, _, _, _ | _, _, .urem _, htot, _, _, _
  | _, _, .srem _, htot, _, _, _ | _, _, .bitcast _ _ _, htot, _, _, _
  | _, _, .shufd _ _, htot, _, _, _ | _, _, .shufb _, htot, _, _, _
  | _, _, .alignr _ _, htot, _, _, _ | _, _, .blendw _ _, htot, _, _, _
  | _, _, .sha256rnds2, htot, _, _, _ | _, _, .sha256msg1, htot, _, _, _
  | _, _, .sha256msg2, htot, _, _, _ | _, _, .fadd _, htot, _, _, _
  | _, _, .fsub _, htot, _, _, _ | _, _, .fmul _, htot, _, _, _
  | _, _, .fdiv _, htot, _, _, _ | _, _, .ffma _, htot, _, _, _
  | _, _, .fsqrt _, htot, _, _, _ | _, _, .fneg _, htot, _, _, _
  | _, _, .fabs _, htot, _, _, _ | _, _, .fcmp _ _ _ _, htot, _, _, _
  | _, _, .fptoui _ _, htot, _, _, _ | _, _, .fptosi _ _, htot, _, _, _
  | _, _, .uitofp _ _, htot, _, _, _ | _, _, .sitofp _ _, htot, _, _, _
  | _, _, .fcvt _ _, htot, _, _, _ => by cases htot

private theorem totalPure_let_wp_step
    {vsOuter : List ((t : Ty) × Val t)} {is32 : Bool}
    {iVal : Val (if is32 then i32 else i64)} {vsLocal : List ((t : Ty) × Val t)}
    {env : Array SymExt} (hm : SymExtEnvMatch vsOuter is32 iVal vsLocal env)
    {ts : List Ty} (op : Op K ts) (htot : isTotalPureOp op.code = true)
    {valArgs : Tup (Arg Val) op.sig}
    (hda : denoteArgs (vsLocal ++ ⟨if is32 then i32 else i64, iVal⟩ :: vsOuter) op.args =
      some valArgs)
    {P : Tup Val ts → Prop} (hwp : op.code.wp (vals valArgs) P) :
    ∃ res : Tup Val ts, P res ∧
      SymExtEnvMatch vsOuter is32 iVal (pushTup res vsLocal)
        (env ++ (evalSymOpExt is32 env op).toArray) ∧
      (∀ Q' : Tup Val ts → Prop, Q' res → op.code.wp (vals valArgs) Q') := by
  obtain ⟨v, hDet⟩ := opCode_wp_totalPure_det op.code htot (vals valArgs) P hwp
  have hvEq : op.code.wp (vals valArgs) (fun r => r = v) := (hDet (fun r => r = v)).1 rfl
  obtain ⟨res, hEq, hm'⟩ := evalSymOpExt_wp hm op hda hvEq
  subst hEq
  exact ⟨res, (hDet P).2 hwp, hm', fun Q' hQ => (hDet Q').1 hQ⟩

private theorem stripJnzTrue_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vsOuter : List ((t : Ty) × Val t)}
    {ls : List ((ts : List Ty) × Cont ts)} {is32 : Bool}
    {iVal : Val (IvTy is32)} {fb : FillBound} {isLt : Bool}
    {bnd : Arg K (IvTy is32)} {bndA : Arg Val (IvTy is32)}
    (hFb : fb = mkFBTy is32 isLt bnd) (hBnd : denoteArg vsOuter bnd = some bndA)
    (hCmp : cmpBoundOk is32 isLt iVal bndA.val) :
    (body : TFlat rs) → {env : Array SymExt} → {vsLocal : List ((t : Ty) × Val t)} →
    {m : Mem 64} →
    SymExtEnvMatch vsOuter is32 iVal vsLocal env →
    matchCountedBody is32 env body = some fb →
    wp Γ Q X (denote Val Cont body (vsLocal ++ ⟨IvTy is32, iVal⟩ :: vsOuter) ls) m →
    wp Γ Q X (denote Val Cont (stripJnzTrue body) (vsLocal ++ ⟨IvTy is32, iVal⟩ :: vsOuter) ls) m
  | .let_ op k, _, vsLocal, _, hEnv, hm, hwp => by
    dsimp only [matchCountedBody] at hm
    by_cases hp : isTotalPureOp op.code = true
    · rw [ite_eq_left hp] at hm
      dsimp only [stripJnzTrue]; rw [denote_let_eq] at hwp ⊢
      cases hda : denoteArgs (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) op.args with
      | none => rw [hda] at hwp; exact False.elim (wp_hlt_false hwp)
      | some valArgs =>
        rw [hda] at hwp; dsimp only [Op.wp] at hwp ⊢; rw [wp_let] at hwp ⊢
        obtain ⟨res, hP, hm', hBack⟩ := totalPure_let_wp_step hEnv op hp hda hwp
        refine hBack _ ?_
        rw [pushTup_append_assoc] at hP ⊢
        exact stripJnzTrue_wp hFb hBnd hCmp k hm' hm hP
    · rw [ite_eq_right hp] at hm; cases hm
  | .jnz c t _, env, vsLocal, m, hEnv, hm, hwp => by
    dsimp only [matchCountedBody] at hm
    split at hm
    · rw [denote_jnz_eq] at hwp
      cases hdc : denoteArg (vsLocal ++ ⟨IvTy is32, iVal⟩ :: vsOuter) c with
      | none => rw [hdc] at hwp; exact False.elim (wp_hlt_false hwp)
      | some cA =>
        rw [hdc] at hwp; dsimp only at hwp; rw [wp_jnz] at hwp
        have hRel := argToSym_correct hEnv c hdc
        cases hc : argToSym is32 env c <;> rw [hc] at hm hRel <;>
          first
          | cases hm
          | (cases is32 <;> simp at hm <;> subst hm <;>
              (dsimp only [mkFBTy] at hFb; cases hFb
               rcases hRel with ⟨_, bndA', hBnd', hCEq⟩; rw [hBnd] at hBnd'; cases hBnd'
               dsimp only [stripJnzTrue]
               exact hwp.1 (by
                 dsimp only [cmpBoundOk] at hCmp; rw [sigma_val_eq hCEq]; exact hCmp)))
    · cases hm
  | .load _ _ _, _, _, _, _, hm, _
  | .store _ _ _, _, _, _, _, hm, _
  | .call _ _ _ _, _, _, _, _, hm, _
  | .jump _ _, _, _, _, _, hm, _
  | .ret _, _, _, _, _, hm, _
  | .exit _ _, _, _, _, _, hm, _
  | .hlt, _, _, _, _, hm, _
  | .group _ _, _, _, _, _, hm, _ => by
    dsimp only [matchCountedBody] at hm; cases hm

private theorem checkJoinEntry0_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vsOuter : List ((t : Ty) × Val t)} {lsOuter : List ((ts : List Ty) × Cont ts)}
    {is32 : Bool} {iVal : Val (IvTy is32)}
    {nextBody : TFlat rs} {JLoop JUnr : Cont [IvTy is32]}
    {lsExtra : List ((ts : List Ty) × Cont ts)}
    (hNext : ∀ m', JLoop (incLoopVal is32 iVal, ()) m' →
      wp Γ Q X (denote Val Cont nextBody
        (⟨IvTy is32, incLoopVal is32 iVal⟩ :: vsOuter)
        (⟨[IvTy is32], JUnr⟩ :: (lsExtra ++ lsOuter))) m') :
    (tf : TFlat rs) → {ts1 : List Ty} → {J1 J2 : Cont ts1} →
    (∀ xs1 m1, J1 xs1 m1 → J2 xs1 m1) →
    (lsMid0 : List ((ts : List Ty) × Cont ts)) →
    {env : Array SymExt} → {vsLocal : List ((t : Ty) × Val t)} → {m : Mem 64} →
    checkJoinEntry0 is32 env (lsMid0.length + 1) tf = true →
    SymExtEnvMatch vsOuter is32 iVal vsLocal env →
    wp Γ Q X (denote Val Cont tf
      (vsLocal ++ ⟨IvTy is32, iVal⟩ :: vsOuter)
      ((⟨ts1, J1⟩ :: lsMid0) ++ ⟨[IvTy is32], JLoop⟩ :: lsOuter)) m →
    wp Γ Q X (denote Val Cont
      (inlineJumpTarget nextBody (IvTy is32) (lsMid0.length + 1) vsLocal.length tf)
      (vsLocal ++ ⟨IvTy is32, iVal⟩ :: vsOuter)
      ((⟨ts1, J2⟩ :: lsMid0) ++ ⟨[IvTy is32], JUnr⟩ :: (lsExtra ++ lsOuter))) m
  | .let_ (ts := ts) op k, ts1, J1, J2, hJ12, lsMid0, env, vsLocal, m, hc, hEnv, hwp => by
    dsimp only [checkJoinEntry0] at hc; rw [Bool.and_eq_true] at hc
    dsimp only [inlineJumpTarget]
    rw [denote_let_eq] at hwp ⊢
    cases hda : denoteArgs (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) op.args with
    | none => rw [hda] at hwp; exact False.elim (wp_hlt_false hwp)
    | some valArgs =>
      rw [hda] at hwp; dsimp only [Op.wp] at hwp ⊢; rw [wp_let] at hwp ⊢
      obtain ⟨res, hP, hm', hBack⟩ := totalPure_let_wp_step hEnv op hc.1 hda hwp
      refine hBack _ ?_
      rw [pushTup_append_assoc] at hP ⊢
      have hRec := checkJoinEntry0_wp hNext k hJ12 lsMid0 hc.2 hm' hP
      rw [pushTup_length] at hRec; exact hRec
  | .load t a k, ts1, J1, J2, hJ12, lsMid0, env, vsLocal, m, hc, hEnv, hwp => by
    dsimp only [checkJoinEntry0] at hc; dsimp only [inlineJumpTarget]
    rw [denote_load_eq] at hwp ⊢
    cases hda : denoteArg (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) a with
    | none => rw [hda] at hwp; exact False.elim (wp_hlt_false hwp)
    | some a' =>
      rw [hda] at hwp; dsimp only at hwp ⊢; rw [wp_load] at hwp ⊢
      obtain ⟨v, hv, hk⟩ := hwp; refine ⟨v, hv, ?_⟩
      have hm' := symExtEnvMatch_push_other hEnv (ts := [t]) (v, ()) [SymExt.other]
        rfl (fun _ hs => by simp at hs; exact hs)
      rw [← List.cons_append] at hk ⊢
      exact checkJoinEntry0_wp hNext k hJ12 lsMid0 hc hm' hk
  | .store v a k, ts1, J1, J2, hJ12, lsMid0, env, vsLocal, m, hc, hEnv, hwp => by
    dsimp only [checkJoinEntry0] at hc; dsimp only [inlineJumpTarget]
    rw [denote_store_eq] at hwp ⊢
    cases hdv : denoteArg (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) v with
    | none => rw [hdv] at hwp; exact False.elim (wp_hlt_false hwp)
    | some v' =>
      cases hda : denoteArg (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) a with
      | none => rw [hdv, hda] at hwp; exact False.elim (wp_hlt_false hwp)
      | some a' =>
        rw [hdv, hda] at hwp; dsimp only at hwp ⊢; rw [wp_store] at hwp ⊢
        exact ⟨hwp.1, checkJoinEntry0_wp hNext k hJ12 lsMid0 hc hEnv hwp.2⟩
  | .jnz c t e, ts1, J1, J2, hJ12, lsMid0, env, vsLocal, m, hc, hEnv, hwp => by
    dsimp only [checkJoinEntry0] at hc; rw [Bool.and_eq_true] at hc
    dsimp only [inlineJumpTarget]; rw [denote_jnz_eq] at hwp ⊢
    cases hdc : denoteArg (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) c with
    | none => rw [hdc] at hwp; exact False.elim (wp_hlt_false hwp)
    | some c' =>
      rw [hdc] at hwp; dsimp only at hwp ⊢; rw [wp_jnz] at hwp ⊢
      exact ⟨fun ht => checkJoinEntry0_wp hNext t hJ12 lsMid0 hc.1 hEnv (hwp.1 ht),
        fun he => checkJoinEntry0_wp hNext e hJ12 lsMid0 hc.2 hEnv (hwp.2 he)⟩
  | .jump (ts := ts) j args, ts1, J1, J2, hJ12, lsMid0, env, vsLocal, m, hc, hEnv, hwp => by
    dsimp only [checkJoinEntry0] at hc
    by_cases hj0 : (j == 0) = true
    · have hjEq0 : j = 0 := beq_iff_eq.mp hj0; subst hjEq0; dsimp only [inlineJumpTarget]
      have hNe : (0 == lsMid0.length + 1) = false := beq_false_of_ne (by omega)
      rw [ite_eq_right (by simp [hNe])]; rw [denote_jump_eq] at hwp ⊢
      cases hda : denoteArgs (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) args with
      | none =>
        cases hLk : lookupL (⟨ts1, J1⟩ :: lsMid0 ++ ⟨[IvTy is32], JLoop⟩ :: lsOuter) ts 0 with
        | none => rw [hLk] at hwp; exact False.elim (wp_hlt_false hwp)
        | some _ => rw [hLk, hda] at hwp; exact False.elim (wp_hlt_false hwp)
      | some args' =>
        rw [hda] at hwp; dsimp only [List.cons_append, lookupL, listGet?] at hwp ⊢
        cases hDec : listTyDecEq ts1 ts with
        | isFalse hne =>
          have : castListTy ts1 ts J1 = none := by simp [castListTy, hDec]
          rw [this] at hwp; exact False.elim (wp_hlt_false hwp)
        | isTrue heq =>
          subst heq; rw [castListTy_self] at hwp ⊢; dsimp only at hwp ⊢; rw [wp_jump] at hwp ⊢
          exact hJ12 _ _ hwp
    · rw [ite_eq_right hj0] at hc
      by_cases hjT : (j == lsMid0.length + 1) = true
      · have hjEqT : j = lsMid0.length + 1 := beq_iff_eq.mp hjT; subst hjEqT
        rw [ite_eq_left hjT] at hc
        rcases ts with _ | ⟨t0, _ | ⟨t1, tr⟩⟩
        · cases hc
        · cases t0 with
          | bits w =>
            rcases args with ⟨nextArg, ⟨⟩⟩
            dsimp only at hc; rw [Bool.and_eq_true] at hc
            have hw : w = if is32 then 32 else 64 := by simp_all
            subst hw
            cases is32 with
            | true =>
              dsimp only [inlineJumpTarget]
              rw [ite_eq_left hjT, dite_eq_left (by simp [IvTy])]
              rw [denote_jump_eq, denoteArgs_singleton_eq] at hwp
              have hLk : lookupL ((⟨ts1, J1⟩ :: lsMid0) ++ ⟨[IvTy true], JLoop⟩ :: lsOuter)
                  [Ty.bits (if true = true then 32 else 64)] (lsMid0.length + 1) = some JLoop := by
                have hLen : (⟨ts1, J1⟩ :: lsMid0).length = lsMid0.length + 1 := by simp
                rw [← hLen, lookupL_append_drop]
                dsimp only [lookupL, listGet?]; exact castListTy_self _ _
              cases hda : denoteArg (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) nextArg with
              | none => rw [hLk, hda] at hwp; exact False.elim (wp_hlt_false hwp)
              | some nextA =>
                rw [hLk, hda] at hwp; dsimp only at hwp; rw [wp_jump] at hwp
                dsimp only [vals] at hwp
                have hInc := matchInc1Ext_correct (argToSym_correct hEnv nextArg hda) hc.2
                have hJVal : JLoop (incLoopVal true iVal, ()) m := by
                  rw [sigma_val_eq hInc] at hwp; exact hwp
                have hda' : denoteArgs (vsLocal ++ ⟨_, iVal⟩ :: vsOuter)
                    (ts := [IvTy true]) (nextArg, ()) = some (nextA, ()) := by
                  rw [denoteArgs_singleton_eq, hda]
                refine denote_letBindTup_wp (ts := [IvTy true]) (nextArg, ()) []
                  (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) _ _ m hda' ?_
                have hSh := denote_shiftTFlat Val Cont
                  (shiftLabelsTFlat 0 (lsMid0.length + 1) nextBody)
                  [⟨IvTy true, nextA.val⟩] (vsLocal ++ [⟨IvTy true, iVal⟩]) vsOuter
                  ((⟨ts1, J2⟩ :: lsMid0) ++ ⟨[IvTy true], JUnr⟩ :: (lsExtra ++ lsOuter))
                rw [List.length_singleton, List.length_append, List.length_singleton] at hSh
                rw [List.append_assoc, List.singleton_append, List.singleton_append] at hSh
                dsimp only [vals, pushTup]; rw [List.nil_append, hSh]
                rw [show (⟨IvTy true, nextA.val⟩ : (t : Ty) × Val t) =
                  ⟨IvTy true, incLoopVal true iVal⟩ from hInc]
                have hShL := denote_shiftLabelsTFlat Val Cont nextBody
                  (⟨IvTy true, incLoopVal true iVal⟩ :: vsOuter) [] (⟨ts1, J2⟩ :: lsMid0)
                  (⟨[IvTy true], JUnr⟩ :: (lsExtra ++ lsOuter))
                rw [List.length_nil, List.length_cons, List.nil_append, List.nil_append] at hShL
                rw [List.singleton_append, hShL]; exact hNext m hJVal
            | false =>
              dsimp only [inlineJumpTarget]
              rw [ite_eq_left hjT, dite_eq_left (by simp [IvTy])]
              rw [denote_jump_eq, denoteArgs_singleton_eq] at hwp
              have hLk : lookupL ((⟨ts1, J1⟩ :: lsMid0) ++ ⟨[IvTy false], JLoop⟩ :: lsOuter)
                  [Ty.bits (if false = true then 32 else 64)] (lsMid0.length + 1) = some JLoop := by
                have hLen : (⟨ts1, J1⟩ :: lsMid0).length = lsMid0.length + 1 := by simp
                rw [← hLen, lookupL_append_drop]
                dsimp only [lookupL, listGet?]; exact castListTy_self _ _
              cases hda : denoteArg (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) nextArg with
              | none => rw [hLk, hda] at hwp; exact False.elim (wp_hlt_false hwp)
              | some nextA =>
                rw [hLk, hda] at hwp; dsimp only at hwp; rw [wp_jump] at hwp
                dsimp only [vals] at hwp
                have hInc := matchInc1Ext_correct (argToSym_correct hEnv nextArg hda) hc.2
                have hJVal : JLoop (incLoopVal false iVal, ()) m := by
                  rw [sigma_val_eq hInc] at hwp; exact hwp
                have hda' : denoteArgs (vsLocal ++ ⟨_, iVal⟩ :: vsOuter)
                    (ts := [IvTy false]) (nextArg, ()) = some (nextA, ()) := by
                  rw [denoteArgs_singleton_eq, hda]
                refine denote_letBindTup_wp (ts := [IvTy false]) (nextArg, ()) []
                  (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) _ _ m hda' ?_
                have hSh := denote_shiftTFlat Val Cont
                  (shiftLabelsTFlat 0 (lsMid0.length + 1) nextBody)
                  [⟨IvTy false, nextA.val⟩] (vsLocal ++ [⟨IvTy false, iVal⟩]) vsOuter
                  ((⟨ts1, J2⟩ :: lsMid0) ++ ⟨[IvTy false], JUnr⟩ :: (lsExtra ++ lsOuter))
                rw [List.length_singleton, List.length_append, List.length_singleton] at hSh
                rw [List.append_assoc, List.singleton_append, List.singleton_append] at hSh
                dsimp only [vals, pushTup]; rw [List.nil_append, hSh]
                rw [show (⟨IvTy false, nextA.val⟩ : (t : Ty) × Val t) =
                  ⟨IvTy false, incLoopVal false iVal⟩ from hInc]
                have hShL := denote_shiftLabelsTFlat Val Cont nextBody
                  (⟨IvTy false, incLoopVal false iVal⟩ :: vsOuter) [] (⟨ts1, J2⟩ :: lsMid0)
                  (⟨[IvTy false], JUnr⟩ :: (lsExtra ++ lsOuter))
                rw [List.length_nil, List.length_cons, List.nil_append, List.nil_append] at hShL
                rw [List.singleton_append, hShL]; exact hNext m hJVal
          | bool | float _ | pair _ _ => cases hc
        · simp at hc
      · rw [ite_eq_right hjT] at hc; cases hc
  | .call _ _ _ _, _, _, _, _, _, _, _, _, hc, _, _ | .ret _, _, _, _, _, _, _, _, _, hc, _, _
  | .exit _ _, _, _, _, _, _, _, _, _, hc, _, _ | .hlt, _, _, _, _, _, _, _, _, hc, _, _
  | .group _ _, _, _, _, _, _, _, _, _, hc, _, _ => by
    dsimp only [checkJoinEntry0] at hc; cases hc

private theorem checkTrueArmCounted_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vsOuter : List ((t : Ty) × Val t)} {lsOuter : List ((ts : List Ty) × Cont ts)}
    {is32 : Bool} {iVal : Val (IvTy is32)}
    {nextBody : TFlat rs} {JLoop JUnr : Cont [IvTy is32]}
    {lsExtra : List ((ts : List Ty) × Cont ts)}
    (hNext : ∀ m', JLoop (incLoopVal is32 iVal, ()) m' →
      wp Γ Q X (denote Val Cont nextBody
        (⟨IvTy is32, incLoopVal is32 iVal⟩ :: vsOuter)
        (⟨[IvTy is32], JUnr⟩ :: (lsExtra ++ lsOuter))) m') :
    (tf : TFlat rs) → (lsMid : List ((ts : List Ty) × Cont ts)) →
    {env : Array SymExt} → {vsLocal : List ((t : Ty) × Val t)} → {m : Mem 64} →
    checkTrueArmCounted is32 env lsMid.length tf = true →
    SymExtEnvMatch vsOuter is32 iVal vsLocal env →
    wp Γ Q X (denote Val Cont tf
      (vsLocal ++ ⟨IvTy is32, iVal⟩ :: vsOuter)
      (lsMid ++ ⟨[IvTy is32], JLoop⟩ :: lsOuter)) m →
    wp Γ Q X (denote Val Cont
      (inlineJumpTarget nextBody (IvTy is32) lsMid.length vsLocal.length tf)
      (vsLocal ++ ⟨IvTy is32, iVal⟩ :: vsOuter)
      (lsMid ++ ⟨[IvTy is32], JUnr⟩ :: (lsExtra ++ lsOuter))) m
  | .let_ (ts := ts) op k, lsMid, env, vsLocal, m, hc, hEnv, hwp => by
    dsimp only [checkTrueArmCounted] at hc; rw [Bool.and_eq_true] at hc
    dsimp only [inlineJumpTarget]
    rw [denote_let_eq] at hwp ⊢
    cases hda : denoteArgs (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) op.args with
    | none => rw [hda] at hwp; exact False.elim (wp_hlt_false hwp)
    | some valArgs =>
      rw [hda] at hwp; dsimp only [Op.wp] at hwp ⊢; rw [wp_let] at hwp ⊢
      obtain ⟨res, hP, hm', hBack⟩ := totalPure_let_wp_step hEnv op hc.1 hda hwp
      refine hBack _ ?_
      rw [pushTup_append_assoc] at hP ⊢
      have hRec := checkTrueArmCounted_wp hNext k lsMid hc.2 hm' hP
      rw [pushTup_length] at hRec; exact hRec
  | .load t a k, lsMid, env, vsLocal, m, hc, hEnv, hwp => by
    dsimp only [checkTrueArmCounted] at hc
    dsimp only [inlineJumpTarget]
    rw [denote_load_eq] at hwp ⊢
    cases hda : denoteArg (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) a with
    | none => rw [hda] at hwp; exact False.elim (wp_hlt_false hwp)
    | some a' =>
      rw [hda] at hwp; dsimp only at hwp ⊢; rw [wp_load] at hwp ⊢
      obtain ⟨v, hv, hk⟩ := hwp
      refine ⟨v, hv, ?_⟩
      have hm' := symExtEnvMatch_push_other hEnv (ts := [t]) (v, ()) [SymExt.other]
        rfl (fun _ hs => by simp at hs; exact hs)
      rw [← List.cons_append] at hk ⊢
      exact checkTrueArmCounted_wp hNext k lsMid hc hm' hk
  | .store v a k, lsMid, env, vsLocal, m, hc, hEnv, hwp => by
    dsimp only [checkTrueArmCounted] at hc; dsimp only [inlineJumpTarget]
    rw [denote_store_eq] at hwp ⊢
    cases hdv : denoteArg (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) v with
    | none => rw [hdv] at hwp; exact False.elim (wp_hlt_false hwp)
    | some v' =>
      cases hda : denoteArg (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) a with
      | none => rw [hdv, hda] at hwp; exact False.elim (wp_hlt_false hwp)
      | some a' =>
        rw [hdv, hda] at hwp; dsimp only at hwp ⊢; rw [wp_store] at hwp ⊢
        exact ⟨hwp.1, checkTrueArmCounted_wp hNext k lsMid hc hEnv hwp.2⟩
  | .jnz c t e, lsMid, env, vsLocal, m, hc, hEnv, hwp => by
    dsimp only [checkTrueArmCounted] at hc; rw [Bool.and_eq_true] at hc
    dsimp only [inlineJumpTarget]; rw [denote_jnz_eq] at hwp ⊢
    cases hdc : denoteArg (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) c with
    | none => rw [hdc] at hwp; exact False.elim (wp_hlt_false hwp)
    | some c' =>
      rw [hdc] at hwp; dsimp only at hwp ⊢; rw [wp_jnz] at hwp ⊢
      exact ⟨fun ht => checkTrueArmCounted_wp hNext t lsMid hc.1 hEnv (hwp.1 ht),
        fun he => checkTrueArmCounted_wp hNext e lsMid hc.2 hEnv (hwp.2 he)⟩
  | .jump (ts := ts) j args, lsMid, env, vsLocal, m, hc, hEnv, hwp => by
    dsimp only [checkTrueArmCounted] at hc; rw [Bool.and_eq_true] at hc
    have hjT : (j == lsMid.length) = true := hc.1
    have hjEq : j = lsMid.length := beq_iff_eq.mp hjT; subst hjEq
    rcases ts with _ | ⟨t0, _ | ⟨t1, tr⟩⟩
    · cases hc.2
    · cases t0 with
      | bits w =>
        rcases args with ⟨nextArg, ⟨⟩⟩
        have hc2 := hc.2; dsimp only at hc2; rw [Bool.and_eq_true] at hc2
        have hw : w = if is32 then 32 else 64 := by simp_all
        subst hw
        cases is32 with
        | true =>
          dsimp only [inlineJumpTarget]; rw [ite_eq_left hjT, dite_eq_left (by simp [IvTy])]
          rw [denote_jump_eq, denoteArgs_singleton_eq] at hwp
          have hLk : lookupL (lsMid ++ ⟨[IvTy true], JLoop⟩ :: lsOuter)
              [Ty.bits (if true = true then 32 else 64)] lsMid.length = some JLoop := by
            rw [lookupL_append_drop]; dsimp only [lookupL, listGet?]; exact castListTy_self _ _
          cases hda : denoteArg (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) nextArg with
          | none => rw [hLk, hda] at hwp; exact False.elim (wp_hlt_false hwp)
          | some nextA =>
            rw [hLk, hda] at hwp; dsimp only at hwp; rw [wp_jump] at hwp; dsimp only [vals] at hwp
            have hInc := matchInc1Ext_correct (argToSym_correct hEnv nextArg hda) hc2.2
            have hJVal : JLoop (incLoopVal true iVal, ()) m := by
              rw [sigma_val_eq hInc] at hwp; exact hwp
            have hda' : denoteArgs (vsLocal ++ ⟨_, iVal⟩ :: vsOuter)
                (ts := [IvTy true]) (nextArg, ()) = some (nextA, ()) := by
              rw [denoteArgs_singleton_eq, hda]
            refine denote_letBindTup_wp (ts := [IvTy true]) (nextArg, ()) []
              (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) _ _ m hda' ?_
            have hSh := denote_shiftTFlat Val Cont (shiftLabelsTFlat 0 lsMid.length nextBody)
              [⟨IvTy true, nextA.val⟩] (vsLocal ++ [⟨IvTy true, iVal⟩]) vsOuter
              (lsMid ++ ⟨[IvTy true], JUnr⟩ :: (lsExtra ++ lsOuter))
            rw [List.length_singleton, List.length_append, List.length_singleton] at hSh
            rw [List.append_assoc, List.singleton_append, List.singleton_append] at hSh
            dsimp only [vals, pushTup]; rw [List.nil_append, hSh]
            rw [show (⟨IvTy true, nextA.val⟩ : (t : Ty) × Val t) =
              ⟨IvTy true, incLoopVal true iVal⟩ from hInc]
            have hShL := denote_shiftLabelsTFlat Val Cont nextBody
              (⟨IvTy true, incLoopVal true iVal⟩ :: vsOuter) [] lsMid
              (⟨[IvTy true], JUnr⟩ :: (lsExtra ++ lsOuter))
            rw [List.length_nil, List.nil_append, List.nil_append] at hShL
            rw [List.singleton_append, hShL]; exact hNext m hJVal
        | false =>
          dsimp only [inlineJumpTarget]; rw [ite_eq_left hjT, dite_eq_left (by simp [IvTy])]
          rw [denote_jump_eq, denoteArgs_singleton_eq] at hwp
          have hLk : lookupL (lsMid ++ ⟨[IvTy false], JLoop⟩ :: lsOuter)
              [Ty.bits (if false = true then 32 else 64)] lsMid.length = some JLoop := by
            rw [lookupL_append_drop]; dsimp only [lookupL, listGet?]; exact castListTy_self _ _
          cases hda : denoteArg (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) nextArg with
          | none => rw [hLk, hda] at hwp; exact False.elim (wp_hlt_false hwp)
          | some nextA =>
            rw [hLk, hda] at hwp; dsimp only at hwp; rw [wp_jump] at hwp; dsimp only [vals] at hwp
            have hInc := matchInc1Ext_correct (argToSym_correct hEnv nextArg hda) hc2.2
            have hJVal : JLoop (incLoopVal false iVal, ()) m := by
              rw [sigma_val_eq hInc] at hwp; exact hwp
            have hda' : denoteArgs (vsLocal ++ ⟨_, iVal⟩ :: vsOuter)
                (ts := [IvTy false]) (nextArg, ()) = some (nextA, ()) := by
              rw [denoteArgs_singleton_eq, hda]
            refine denote_letBindTup_wp (ts := [IvTy false]) (nextArg, ()) []
              (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) _ _ m hda' ?_
            have hSh := denote_shiftTFlat Val Cont (shiftLabelsTFlat 0 lsMid.length nextBody)
              [⟨IvTy false, nextA.val⟩] (vsLocal ++ [⟨IvTy false, iVal⟩]) vsOuter
              (lsMid ++ ⟨[IvTy false], JUnr⟩ :: (lsExtra ++ lsOuter))
            rw [List.length_singleton, List.length_append, List.length_singleton] at hSh
            rw [List.append_assoc, List.singleton_append, List.singleton_append] at hSh
            dsimp only [vals, pushTup]; rw [List.nil_append, hSh]
            rw [show (⟨IvTy false, nextA.val⟩ : (t : Ty) × Val t) =
              ⟨IvTy false, incLoopVal false iVal⟩ from hInc]
            have hShL := denote_shiftLabelsTFlat Val Cont nextBody
              (⟨IvTy false, incLoopVal false iVal⟩ :: vsOuter) [] lsMid
              (⟨[IvTy false], JUnr⟩ :: (lsExtra ++ lsOuter))
            rw [List.length_nil, List.nil_append, List.nil_append] at hShL
            rw [List.singleton_append, hShL]; exact hNext m hJVal
      | bool | float _ | pair _ _ => cases hc.2
    · have h2 := hc.2; simp at h2
  | .group (sig := [ts1]) (.cons b1 .nil) k, lsMid, env, vsLocal, m, hc, hEnv, hwp => by
    rw [checkTrueArmCounted_group_one] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc
    let vsAll := vsLocal ++ ⟨IvTy is32, iVal⟩ :: vsOuter
    let lsSrc := lsMid ++ ⟨[IvTy is32], JLoop⟩ :: lsOuter
    let lsTgt := lsMid ++ ⟨[IvTy is32], JUnr⟩ :: (lsExtra ++ lsOuter)
    let b1' := inlineJumpTarget nextBody (IvTy is32) (lsMid.length + 1)
      (vsLocal.length + ts1.length) b1
    let k' := inlineJumpTarget nextBody (IvTy is32) (lsMid.length + 1) vsLocal.length k
    change wp Γ Q X (denote Val Cont
      (.group (sig := [ts1]) (.cons b1' .nil) k') vsAll lsTgt) m
    let bodies1 : Tup Cont [ts1] → Blocks Val Cont rs [ts1] := fun Js =>
      denoteB Val Cont (.cons b1 .nil) vsAll (pushTup Js lsSrc)
    let bodies2 : Tup Cont [ts1] → Blocks Val Cont rs [ts1] := fun Js =>
      denoteB Val Cont (.cons b1' .nil) vsAll (pushTup Js lsTgt)
    have hG := ctx_diagV_of_vs (vs := vsAll)
    have hD1 := ctx_monoD_of_ls (ls := lsSrc)
    have hD2 := ctx_monoD_of_ls (ls := lsTgt)
    have hRV := ctxRel_refl_vs (vs := vsAll)
    have hRL1 := ctxRel_refl_ls (ls := lsSrc)
    have hRL2 := ctxRel_refl_ls (ls := lsTgt)
    have hWfB1 (Js₁ Js₂ : Tup Cont [ts1]) :
        WfB (List.map (fun ⟨t, v⟩ => ⟨t, (v, v)⟩) vsAll)
          (Js₁.zip Js₂ ++ List.map (fun ⟨ts, l⟩ => ⟨ts, (l, l)⟩) lsSrc)
          (bodies1 Js₁) (bodies1 Js₂) :=
      denoteB_wf (.cons b1 .nil) hRV (ctxRel_pushTup Js₁ Js₂ hRL1)
    have hWfB2 (Js₁ Js₂ : Tup Cont [ts1]) :
        WfB (List.map (fun ⟨t, v⟩ => ⟨t, (v, v)⟩) vsAll)
          (Js₁.zip Js₂ ++ List.map (fun ⟨ts, l⟩ => ⟨ts, (l, l)⟩) lsTgt)
          (bodies2 Js₁) (bodies2 Js₂) :=
      denoteB_wf (.cons b1' .nil) hRV (ctxRel_pushTup Js₁ Js₂ hRL2)
    rw [denote_group_eq] at hwp ⊢
    rw [wp_group_iff hG hD1 hWfB1 (fun Js₁ Js₂ =>
      denote_wf k hRV (ctxRel_pushTup Js₁ Js₂ hRL1))] at hwp
    rw [wp_group_iff hG hD2 hWfB2 (fun Js₁ Js₂ =>
      denote_wf k' hRV (ctxRel_pushTup Js₁ Js₂ hRL2))]
    let J1 : Cont ts1 := (lfp Γ Q X bodies1).fst
    let J2 : Cont ts1 := (lfp Γ Q X bodies2).fst
    have hPush1 : pushTup (lfp Γ Q X bodies1) lsSrc = ⟨ts1, J1⟩ :: lsSrc := by
      cases hEq : lfp Γ Q X bodies1 with
      | mk jl u => cases u; dsimp only [J1]; rw [hEq]; rfl
    have hPush2 : pushTup (lfp Γ Q X bodies2) lsTgt = ⟨ts1, J2⟩ :: lsTgt := by
      cases hEq : lfp Γ Q X bodies2 with
      | mk jl u => cases u; dsimp only [J2]; rw [hEq]; rfl
    have hCl2 := lfp_closed (Γ := Γ) (Q := Q) (X := X) hG hD2 hWfB2
    rw [closed_iff] at hCl2
    have hCl12 : Closed Γ Q X (bodies1 (J2, ())) (J2, ()) := by
      rw [closed_iff]
      intro _ i xs1 m1 hb1
      cases i with
      | here =>
        change wp Γ Q X (denote Val Cont b1 (pushTup xs1 vsAll)
          (pushTup (as := [ts1]) (J2, ()) lsSrc)) m1 at hb1
        have hEnv1 := symExtEnvMatch_push_other hEnv (ts := ts1) xs1 (ts1.map fun _ => .other)
          (by rw [List.length_map]) (fun _ hs => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp hs; rfl)
        have hb1' := checkTrueArmCounted_wp hNext b1 (⟨ts1, J2⟩ :: lsMid) hc.1.2 hEnv1
          (by rw [← pushTup_append_assoc]; exact hb1)
        rw [List.length_cons, pushTup_length] at hb1'
        exact hCl2 .here xs1 m1 (by
          change wp Γ Q X (denote Val Cont b1' (pushTup xs1 vsAll)
            (pushTup (lfp Γ Q X bodies2) lsTgt)) m1
          rw [hPush2]; dsimp only [vsAll, lsTgt]; rw [pushTup_append_assoc]; exact hb1')
      | there j => exact nomatch j
    have hJ12 : ∀ xs1 m1, J1 xs1 m1 → J2 xs1 m1 := fun xs1 m1 hj =>
      lfp_le hCl12 .here xs1 m1 hj
    rw [hPush1] at hwp; rw [hPush2]
    exact checkJoinEntry0_wp hNext k hJ12 lsMid hc.2 hEnv hwp
  | .group .nil _, _, _, _, _, hc, _, _
  | .group (.cons _ (.cons _ _)) _, _, _, _, _, hc, _, _
  | .call _ _ _ _, _, _, _, _, hc, _, _ | .ret _, _, _, _, _, hc, _, _
  | .exit _ _, _, _, _, _, hc, _, _ | .hlt, _, _, _, _, hc, _, _ => by
    change false = true at hc; cases hc

/-! ## Section 4: `mkUnrollChain_wp`, `unrollCountedSingle_wp`, & `unrollCountedSingle_callsOk` -/

private theorem denoteArg_var0 {t : Ty} (v : Val t) (vs : List ((u : Ty) × Val u)) :
    denoteArg (⟨t, v⟩ :: vs) (.var 0 : Arg K t) = some (.var v) := by
  dsimp only [denoteArg, lookupV]; rw [listGet?_cons_zero_eq]; dsimp only
  rw [PassFlatKit.castTy_self]

private theorem liftOp_sub_args_wp {w : Nat} (hw : w = 32 ∨ w = 64) {a b : Arg Val (.bits w)}
    {P : Tup Val [.bits w] → Prop} (h : P (a.val - b.val, ())) :
    OpCode.wp (.sub (.bits w)) (vals (ts := [.bits w, .bits w]) (a, b, ())) P := by
  rcases hw with rfl | rfl <;> exact h

private theorem liftOp_cmp_args_wp {w : Nat} (hw : w = 32 ∨ w = 64) {o : CmpOp}
    {a b : Arg Val (.bits w)} {P : Tup Val [Ty.bool] → Prop}
    (h : P (o.evalBits a.val b.val, ())) :
    OpCode.wp (.cmp o (.bits w) Ty.bool rfl)
      (vals (ts := [.bits w, .bits w]) (a, b, ())) P := by
  rcases hw with rfl | rfl <;> exact h

private theorem mkUnrollChain_succ_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vsOuter : List ((t : Ty) × Val t)} {lsOuter : List ((ts : List Ty) × Cont ts)}
    {is32 : Bool} {body : TFlat rs} {isLt : Bool}
    {bnd : Arg K (IvTy is32)} {bndA : Arg Val (IvTy is32)}
    {JLoop JUnr : Cont [IvTy is32]}
    (hm : matchCountedBody is32 #[] body = some (mkFBTy is32 isLt bnd))
    (hdBnd : denoteArg vsOuter bnd = some bndA)
    (hStepLoop : ∀ (i' : Val (IvTy is32)) (m' : Mem 64),
      JLoop (i', ()) m' →
      wp Γ Q X (denote Val Cont body
        (⟨IvTy is32, i'⟩ :: vsOuter)
        (⟨[IvTy is32], JLoop⟩ :: lsOuter)) m')
    {i0 : Val (IvTy is32)}
    (hDone : ∀ (iEnd : Val (IvTy is32)) (mEnd : Mem 64),
      bvToNatW i0 < bvToNatW iEnd → bvToNatW iEnd ≤ bvToNatW bndA.val →
      JLoop (iEnd, ()) mEnd → JUnr (iEnd, ()) mEnd) :
    ∀ (k : Nat) (iCur : Val (IvTy is32)) (mCur : Mem 64),
      bvToNatW i0 ≤ bvToNatW iCur →
      bvToNatW iCur + (k + 1) ≤ bvToNatW bndA.val →
      JLoop (iCur, ()) mCur →
      wp Γ Q X (denote Val Cont
        (mkUnrollChain (stripJnzTrue body) (IvTy is32) (k + 1))
        (⟨IvTy is32, iCur⟩ :: vsOuter)
        (⟨[IvTy is32], JUnr⟩ ::
          ⟨[IvTy is32], JLoop⟩ :: lsOuter)) mCur
  | k, iCur, mCur, h0Le, hSumLe, hJC => by
    have hiLt : bvToNatW iCur < bvToNatW bndA.val := by omega
    have hCmp : cmpBoundOk is32 isLt iCur bndA.val := by
      have hLe : bvToNatW iCur ≤ bvToNatW bndA.val := Nat.le_of_lt hiLt
      cases is32 with
      | true =>
        dsimp only [bvToNatW] at hiLt hLe
        dsimp only [cmpBoundOk]; cases isLt
        · exact decide_eq_true (BitVec.le_def.mpr hLe)
        · exact decide_eq_true (BitVec.lt_def.mpr hiLt)
      | false =>
        dsimp only [bvToNatW] at hiLt hLe
        dsimp only [cmpBoundOk]; cases isLt
        · exact decide_eq_true (BitVec.le_def.mpr hLe)
        · exact decide_eq_true (BitVec.lt_def.mpr hiLt)
    have hSrc := stripJnzTrue_wp (ls := ⟨[IvTy is32], JLoop⟩ :: lsOuter)
      rfl hdBnd hCmp body symExtEnvMatch_empty hm (hStepLoop iCur mCur hJC)
    have hArm := matchCountedBody_checkTrueArm body hm
    have hNextInc : bvToNatW (incLoopVal is32 iCur) = bvToNatW iCur + 1 := by
      have hSLt : bvToNatW iCur + 1 < 2 ^ (if is32 then 32 else 64) :=
        Nat.lt_of_le_of_lt (by omega) (bvToNatW_lt bndA.val)
      cases is32 with
      | true =>
        have h1Lt : 1 < 2 ^ 32 := by decide
        dsimp only [incLoopVal, bvToNatW]
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1Lt,
          Nat.mod_eq_of_lt (by simpa [bvToNatW] using hSLt)]
      | false =>
        have h1Lt : 1 < 2 ^ 64 := by decide
        dsimp only [incLoopVal, bvToNatW]
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1Lt,
          Nat.mod_eq_of_lt (by simpa [bvToNatW] using hSLt)]
    have hNextSpec : ∀ m', JLoop (incLoopVal is32 iCur, ()) m' →
        wp Γ Q X (denote Val Cont
          (mkUnrollChain (stripJnzTrue body) (IvTy is32) k)
          (⟨IvTy is32, incLoopVal is32 iCur⟩ :: vsOuter)
          (⟨[IvTy is32], JUnr⟩ ::
            (⟨[IvTy is32], JLoop⟩ :: lsOuter))) m' := by
      intro m' hJN
      cases k with
      | zero =>
        dsimp only [mkUnrollChain]
        have hV0 : denoteArg (⟨IvTy is32, incLoopVal is32 iCur⟩ :: vsOuter)
            (.var 0 : Arg K (IvTy is32)) =
            some (.var (incLoopVal is32 iCur)) := by
          dsimp only [denoteArg, lookupV]; rw [listGet?_cons_zero_eq]; dsimp only
          rw [PassFlatKit.castTy_self]
        rw [denote_jump_eq, denoteArgs_singleton_eq, hV0]
        have hLk : lookupL (⟨[IvTy is32], JUnr⟩ :: ⟨[IvTy is32], JLoop⟩ :: lsOuter)
            [IvTy is32] 0 = some JUnr := by
          dsimp only [lookupL]; rw [listGet?_cons_zero_eq]; dsimp only; exact castListTy_self _ _
        rw [hLk]; dsimp only; rw [wp_jump]
        exact hDone (incLoopVal is32 iCur) m' (by omega) (by omega) hJN
      | succ k' =>
        exact mkUnrollChain_succ_wp hm hdBnd hStepLoop hDone k' (incLoopVal is32 iCur) m'
          (by omega) (by omega) hJN
    have hRes := checkTrueArmCounted_wp (lsExtra := [⟨[IvTy is32], JLoop⟩])
      hNextSpec (stripJnzTrue body) [] hArm symExtEnvMatch_empty hSrc
    simpa [mkUnrollChain] using hRes

private theorem unrollCountedSingle_wp_core {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {w : Nat} (hwEq : w = 32 ∨ w = 64) {isLt : Bool}
    {initArg bnd : Arg K (.bits w)} {initA bndA : Arg Val (.bits w)} {u : Nat}
    (_hu2 : 2 ≤ u) (hu4 : u ≤ 4) {body : TFlat rs} {m : Mem 64}
    (hdInit : denoteArg vs initArg = some initA) (hdBnd : denoteArg vs bnd = some bndA)
    {JLoop : Cont [.bits w]} (hJInit : JLoop (initA.val, ()) m)
    (hChainWp : ∀ (JUnr : Cont [.bits w]) (i' : BitVec w) (m' : Mem 64),
      i'.toNat + u ≤ bndA.val.toNat → JLoop (i', ()) m' →
      (∀ (iEnd : BitVec w) (mEnd : Mem 64),
        i'.toNat < iEnd.toNat → iEnd.toNat ≤ bndA.val.toNat →
        JLoop (iEnd, ()) mEnd → JUnr (iEnd, ()) mEnd) →
      wp Γ Q X (denote Val Cont (mkUnrollChain (stripJnzTrue body) (.bits w) u)
        (⟨.bits w, i'⟩ :: vs) (⟨[.bits w], JUnr⟩ :: ⟨[.bits w], JLoop⟩ :: ls)) m') :
    let wb : TFlat rs :=
      .let_ (op2 (.sub (.bits w)) (tArgShift 1 bnd) (.var 0))
        (.let_ (op2 (.cmp .uge (.bits w) .bool rfl) (.var 0) (.imm (BitVec.ofNat w u)))
          (.jnz (.var 0)
            (.let_ (op1 (.copy (.bits w)) (.var 2))
              (shiftTFlat 1 3 (mkUnrollChain (stripJnzTrue body) (.bits w) u)))
            (.jump (ts := [.bits w]) 1 (.var 2, ()))))
    let kCheck : TFlat rs :=
      .let_ (op2 (.cmp (if isLt then .ult else .ule) (.bits w) .bool rfl) initArg bnd)
        (.jnz (.var 0) (.jump (ts := [.bits w]) 0 (tArgShift 1 initArg, ()))
          (.jump (ts := [.bits w]) 1 (tArgShift 1 initArg, ())))
    wp Γ Q X (Expr.group (sig := [[.bits w]])
      (fun Js => denoteB Val Cont (.cons (ts := [.bits w]) wb .nil) vs
        (pushTup Js (⟨[.bits w], JLoop⟩ :: ls)))
      (fun Js => denote Val Cont kCheck vs (pushTup Js (⟨[.bits w], JLoop⟩ :: ls)))) m := by
  let wb : TFlat rs :=
    .let_ (op2 (.sub (.bits w)) (tArgShift 1 bnd) (.var 0))
      (.let_ (op2 (.cmp .uge (.bits w) .bool rfl) (.var 0) (.imm (BitVec.ofNat w u)))
        (.jnz (.var 0)
          (.let_ (op1 (.copy (.bits w)) (.var 2))
            (shiftTFlat 1 3 (mkUnrollChain (stripJnzTrue body) (.bits w) u)))
          (.jump (ts := [.bits w]) 1 (.var 2, ()))))
  let kCheck : TFlat rs :=
    .let_ (op2 (.cmp (if isLt then .ult else .ule) (.bits w) .bool rfl) initArg bnd)
      (.jnz (.var 0) (.jump (ts := [.bits w]) 0 (tArgShift 1 initArg, ()))
        (.jump (ts := [.bits w]) 1 (tArgShift 1 initArg, ())))
  have hEqGroup :
      Expr.group (sig := [[.bits w]])
        (fun Js => denoteB Val Cont (.cons (ts := [.bits w]) wb .nil) vs
          (pushTup Js (⟨[.bits w], JLoop⟩ :: ls)))
        (fun Js => denote Val Cont kCheck vs (pushTup Js (⟨[.bits w], JLoop⟩ :: ls))) =
      Expr.group (sig := [[.bits w]])
        (fun Js : Tup Cont [[.bits w]] => Blocks.cons
          (fun xs => denote Val Cont wb (pushTup xs vs)
            (⟨[.bits w], Js.fst⟩ :: ⟨[.bits w], JLoop⟩ :: ls))
          Blocks.nil)
        (fun Js => denote Val Cont kCheck vs
          (⟨[.bits w], Js.fst⟩ :: ⟨[.bits w], JLoop⟩ :: ls)) := by
    congr 1 <;> funext Js <;> rcases Js with ⟨jw, ⟨⟩⟩ <;>
      · dsimp only [pushTup]; try rw [denoteB_cons_eq, denoteB_nil_eq]; rfl
  dsimp only [wb, kCheck] at hEqGroup ⊢; rw [hEqGroup]
  let Inv : Nat → Tup Val [.bits w] → Mem 64 → Prop := fun n xs m' =>
    xs.fst.toNat ≤ bndA.val.toNat ∧ n = bndA.val.toNat - xs.fst.toNat ∧ JLoop xs m'
  refine wp_loop
    (fun JUnr xs => denote Val Cont wb (pushTup xs vs)
      (⟨[.bits w], JUnr⟩ :: ⟨[.bits w], JLoop⟩ :: ls))
    (fun JUnr => denote Val Cont kCheck vs (⟨[.bits w], JUnr⟩ :: ⟨[.bits w], JLoop⟩ :: ls))
    Inv ?_ ?_
  · intro JUnr n xs m' ih ⟨hLe, hn, hJL⟩
    rcases xs with ⟨i', ⟨⟩⟩
    dsimp only at hLe hn hJL; subst hn
    dsimp only [wb, op2]
    rw [denote_let_eq, denoteArgs_pair_eq, pushTup_singleton]
    have hBnd1 : denoteArg (⟨.bits w, i'⟩ :: vs) (tArgShift 1 bnd) = some bndA := by
      simpa [tArgShift] using (denoteArg_shiftArgAbove (vsPre := []) [⟨.bits w, i'⟩] vs bnd).trans
        hdBnd
    rw [hBnd1, denoteArg_var0, wp_let]; dsimp only [Op.wp]
    refine liftOp_sub_args_wp hwEq (a := bndA) (b := (.var i' : Arg Val (.bits w))) ?_
    rw [show (Arg.var i' : Arg Val (.bits w)).val = i' from rfl]
    let rem := bndA.val - i'
    rw [denote_let_eq, denoteArgs_pair_eq]
    have hImmU : denoteArg (⟨.bits w, rem⟩ :: ⟨.bits w, i'⟩ :: vs)
        (.imm (BitVec.ofNat w u) : Arg K (.bits w)) = some (.imm (BitVec.ofNat w u)) := rfl
    rw [pushTup_singleton (t := .bits w), denoteArg_var0, hImmU, wp_let]; dsimp only [Op.wp]
    refine liftOp_cmp_args_wp hwEq (o := .uge) (a := (.var rem : Arg Val (.bits w)))
      (b := (.imm (BitVec.ofNat w u) : Arg Val (.bits w))) ?_
    rw [show (Arg.var rem : Arg Val (.bits w)).val = rem from rfl,
      show (Arg.imm (BitVec.ofNat w u) : Arg Val (.bits w)).val = BitVec.ofNat w u from rfl]
    let cU := CmpOp.uge.evalBits rem (BitVec.ofNat w u)
    let vs3 : List ((t : Ty) × Val t) := [⟨Ty.bool, cU⟩, ⟨.bits w, rem⟩, ⟨.bits w, i'⟩]
    rw [pushTup_singleton (t := Ty.bool), denote_jnz_eq]
    have hVs3 : (⟨Ty.bool, CmpOp.uge.evalBits rem (BitVec.ofNat w u)⟩ ::
        ⟨.bits w, bndA.val - i'⟩ :: ⟨.bits w, i'⟩ :: vs) = vs3 ++ vs := rfl
    rw [hVs3]; dsimp only [vs3, List.cons_append]; rw [denoteArg_var0]; dsimp only; rw [wp_jnz]
    rw [show (Arg.var cU : Arg Val Ty.bool).val = cU from rfl]
    constructor
    · intro hcTrue
      have huW : u < 2 ^ w := by rcases hwEq with rfl | rfl <;> omega
      have hRemGe : u ≤ bndA.val.toNat - i'.toNat := by
        have hc' : (BitVec.ofNat w u).toNat ≤ rem.toNat := by
          dsimp only [cU, CmpOp.evalBits] at hcTrue
          exact of_decide_eq_true (by unfold BitVec.ule at hcTrue; exact hcTrue)
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt huW,
          BitVec.toNat_sub_of_le (BitVec.le_def.mpr hLe)] at hc'
      dsimp only [op1]; rw [denote_let_eq, denoteArgs_singleton_eq]
      have hV2 : denoteArg (vs3 ++ vs) (.var 2 : Arg K (.bits w)) = some (.var i') := by
        dsimp only [vs3, List.cons_append, List.nil_append, denoteArg, lookupV, listGet?]
        rw [PassFlatKit.castTy_self]
      dsimp only [vs3, List.cons_append, List.nil_append] at hV2
      rw [List.nil_append, hV2, wp_let]; dsimp only [Op.wp]; rw [OpCode.wp_copy]
      dsimp only [vals, Arg.val, pushTup]
      have hSh := denote_shiftTFlat Val Cont (mkUnrollChain (stripJnzTrue body) (.bits w) u)
        [⟨.bits w, i'⟩] vs3 vs (⟨[.bits w], JUnr⟩ :: ⟨[.bits w], JLoop⟩ :: ls)
      rw [List.length_singleton] at hSh
      have hLen3 : vs3.length = 3 := rfl
      dsimp only [vs3, List.cons_append, List.nil_append] at hSh
      rw [← hLen3, hSh]
      exact hChainWp JUnr i' m' (by omega) hJL (fun iEnd mEnd hLt hEndLe hJEnd =>
        ih (bndA.val.toNat - iEnd.toNat) (iEnd, ()) mEnd (by omega) ⟨hEndLe, rfl, hJEnd⟩)
    · intro _
      have hV2 : denoteArg (vs3 ++ vs) (.var 2 : Arg K (.bits w)) = some (.var i') := by
        dsimp only [vs3, List.cons_append, List.nil_append, denoteArg, lookupV, listGet?]
        rw [PassFlatKit.castTy_self]
      dsimp only [vs3, List.cons_append, List.nil_append] at hV2
      rw [denote_jump_eq, denoteArgs_singleton_eq, lookupL_1, List.nil_append, hV2]
      dsimp only; rw [wp_jump]; exact hJL
  · intro JUnr hInv
    dsimp only [kCheck, op2]
    rw [denote_let_eq, denoteArgs_pair_eq, hdInit, hdBnd, wp_let]; dsimp only [Op.wp]
    refine liftOp_cmp_args_wp hwEq (o := if isLt then .ult else .ule) (a := initA) (b := bndA) ?_
    let cInit := (if isLt then CmpOp.ult else CmpOp.ule).evalBits initA.val bndA.val
    rw [pushTup_singleton (t := Ty.bool), denote_jnz_eq, denoteArg_var0]
    dsimp only; rw [wp_jnz, show (Arg.var cInit : Arg Val Ty.bool).val = cInit from rfl]
    have hInitSh1 : denoteArg (⟨Ty.bool, cInit⟩ :: vs) (tArgShift 1 initArg) = some initA := by
      simpa [tArgShift] using (denoteArg_shiftArgAbove (vsPre := []) [⟨Ty.bool, cInit⟩] vs
        initArg).trans hdInit
    constructor
    · intro hcTrue
      rw [denote_jump_eq, denoteArgs_singleton_eq, lookupL_0, hInitSh1]
      dsimp only; rw [wp_jump]
      have hLe : initA.val.toNat ≤ bndA.val.toNat := by
        dsimp only [cInit] at hcTrue
        cases isLt <;> dsimp only [CmpOp.evalBits] at hcTrue
        · exact of_decide_eq_true (by unfold BitVec.ule at hcTrue; exact hcTrue)
        · exact Nat.le_of_lt (of_decide_eq_true (by unfold BitVec.ult at hcTrue; exact hcTrue))
      exact hInv (bndA.val.toNat - initA.val.toNat) (initA.val, ()) m ⟨hLe, rfl, hJInit⟩
    · intro _
      rw [denote_jump_eq, denoteArgs_singleton_eq, lookupL_1, hInitSh1]
      dsimp only; rw [wp_jump]; exact hJInit

private theorem unrollCountedSingle_wp_case {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {GOuter : List Ty} {DOuter : List (List Ty)}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    (hCtxV : CtxTypes GOuter vs) {w : Nat} (hwEq : w = 32 ∨ w = 64)
    {initArg bnd : Arg K (.bits w)} {isLt : Bool} {u : Nat}
    (hu2 : 2 ≤ u) (hu4 : u ≤ 4) {body : TFlat rs} {m : Mem 64}
    (hwf2 : TFlat.wfCheck (rs := rs) GOuter (pushTypes [[.bits w]] DOuter)
      (.jump (rs := rs) (ts := [.bits w]) 0 (initArg, ())) = true)
    (hBndWf : checkArg GOuter (.bits w) bnd = true)
    (hChainWp : ∀ {JLoop JUnr : Cont [.bits w]} {bndA : Arg Val (.bits w)},
      denoteArg vs bnd = some bndA →
      (∀ i' m', JLoop (i', ()) m' →
        wp Γ Q X (denote Val Cont body (⟨.bits w, i'⟩ :: vs)
          (⟨[.bits w], JLoop⟩ :: ls)) m') →
      ∀ (i' : BitVec w) (m' : Mem 64),
        i'.toNat + u ≤ bndA.val.toNat → JLoop (i', ()) m' →
        (∀ (iEnd : BitVec w) (mEnd : Mem 64),
          i'.toNat < iEnd.toNat → iEnd.toNat ≤ bndA.val.toNat →
          JLoop (iEnd, ()) mEnd → JUnr (iEnd, ()) mEnd) →
        wp Γ Q X (denote Val Cont (mkUnrollChain (stripJnzTrue body) (.bits w) u)
          (⟨.bits w, i'⟩ :: vs) (⟨[.bits w], JUnr⟩ :: ⟨[.bits w], JLoop⟩ :: ls)) m')
    (hwp : wp Γ Q X (denote Val Cont
      (.group (sig := [[.bits w]]) (.cons body .nil)
        (.jump (ts := [.bits w]) 0 (initArg, ()))) vs ls) m) :
    wp Γ Q X (denote Val Cont
      (.group (sig := [[.bits w]]) (.cons body .nil)
        (mkUnrollWrapper w isLt initArg bnd body u)) vs ls) m := by
  have hG := ctx_diagV_of_vs (vs := vs); have hD := ctx_monoD_of_ls (ls := ls)
  have hRelV := ctxRel_refl_vs (vs := vs); have hRelL := ctxRel_refl_ls (ls := ls)
  rw [wfCheck_jump_eq, Bool.and_eq_true] at hwf2
  have hInitWf : checkArg GOuter (.bits w) initArg = true := by
    simpa [pushTypes, checkArgs] using hwf2.2
  obtain ⟨initA, hdInit⟩ := Option.isSome_iff_exists.mp (denoteArg_isSome_of_checkArg hCtxV hInitWf)
  obtain ⟨bndA, hdBnd⟩ := Option.isSome_iff_exists.mp (denoteArg_isSome_of_checkArg hCtxV hBndWf)
  let bodies : Tup Cont [[.bits w]] → Blocks Val Cont rs [[.bits w]] := fun Js =>
    denoteB Val Cont (.cons (ts := [.bits w]) body .nil) vs (pushTup Js ls)
  have hWfB (Js₁ Js₂ : Tup Cont [[.bits w]]) :
      WfB (List.map (fun ⟨t, v⟩ => ⟨t, (v, v)⟩) vs)
        (Js₁.zip Js₂ ++ List.map (fun ⟨ts, l⟩ => ⟨ts, (l, l)⟩) ls) (bodies Js₁) (bodies Js₂) :=
    denoteB_wf (.cons (ts := [.bits w]) body .nil) hRelV (ctxRel_pushTup Js₁ Js₂ hRelL)
  rw [denote_group_eq] at hwp ⊢
  rw [wp_group_iff hG hD hWfB (fun Js₁ Js₂ =>
    denote_wf (.jump (ts := [.bits w]) 0 (initArg, ())) hRelV (ctxRel_pushTup Js₁ Js₂ hRelL))]
    at hwp
  rw [wp_group_iff hG hD hWfB (fun Js₁ Js₂ =>
    denote_wf (mkUnrollWrapper w isLt initArg bnd body u)
      hRelV (ctxRel_pushTup Js₁ Js₂ hRelL))]
  let JLoop : Cont [.bits w] := (lfp Γ Q X bodies).fst
  have hPushJs : pushTup (lfp Γ Q X bodies) ls = ⟨[.bits w], JLoop⟩ :: ls := by
    cases hEq : lfp Γ Q X bodies with | mk jl u => cases u; dsimp only [JLoop]; rw [hEq]; rfl
  have hJInit : JLoop (initA.val, ()) m := by
    rw [hPushJs, denote_jump_eq, denoteArgs_singleton_eq, lookupL_0, hdInit] at hwp
    simpa [wp_jump, vals, Arg.val] using hwp
  have hStepLoop : ∀ (i' : Val (.bits w)) (m' : Mem 64), JLoop (i', ()) m' →
      wp Γ Q X (denote Val Cont body (⟨.bits w, i'⟩ :: vs) (⟨[.bits w], JLoop⟩ :: ls)) m' := by
    intro i' m' hJi
    have hUnr := lfp_unroll_single hG hD hWfB (i', ()) m' hJi
    change wp Γ Q X ((denoteB Val Cont (.cons (ts := [.bits w]) body .nil) vs
      (pushTup (lfp Γ Q X bodies) ls)).get Member.here (i', ())) m' at hUnr
    rw [hPushJs, denoteB_cons_eq] at hUnr; exact hUnr
  rw [hPushJs]; dsimp only [mkUnrollWrapper]; rw [denote_group_eq]
  refine unrollCountedSingle_wp_core hwEq hu2 hu4 hdInit hdBnd hJInit ?_
  intro JUnr i' m' hSum hJL hDone
  exact hChainWp hdBnd hStepLoop i' m' hSum hJL hDone

public theorem unrollCountedSingle_wp {Γ : Env} {rs ts0 : List Ty} {Q : Post rs} {X : XPost}
    {GOuter : List Ty} {DOuter : List (List Ty)}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    (hCtxV : CtxTypes GOuter vs) (_hCtxL : CtxTypes DOuter ls)
    {unrollN : Nat} {body k res : TFlat rs} {m : Mem 64}
    (hwf : TFlat.wfCheck GOuter DOuter (.group (@TBlocks.cons rs ts0 [] body .nil) k) = true)
    (hu : unrollCountedSingle unrollN ts0 body k = some res)
    (hwp : wp Γ Q X (denote Val Cont (.group (@TBlocks.cons rs ts0 [] body .nil) k) vs ls) m) :
    wp Γ Q X (denote Val Cont res vs ls) m := by
  obtain ⟨_, _, _, _, _, hu2, hu4, hCase⟩ := unrollCountedSingle_eq_some hu
  have hEmpty : SymExtEnvWf GOuter [] #[] := ⟨rfl, fun _ h => by cases h⟩
  rw [wfCheck_group_eq, wfCheckB_cons_eq, wfCheckB_nil_eq, Bool.and_true, Bool.and_eq_true] at hwf
  let u := if zpSize (stripJnzTrue body) ≤ 36 then min unrollN 4 else min unrollN 2
  let k' := u - 1
  have hkEq : k' + 1 = u := by dsimp only [k', u]; omega
  rcases hCase with ⟨initArg, bnd, isLt, rfl, rfl, hm, rfl⟩ |
      ⟨initArg, bnd, isLt, rfl, rfl, hm, rfl⟩
  · refine unrollCountedSingle_wp_case hCtxV (Or.inl rfl) hu2 hu4 hwf.2 ?_ ?_ hwp
    · exact (matchCountedBody_wf (GOuter := GOuter) (D := [[i32]] ++ DOuter)
        (is32 := true) body hEmpty hwf.1 hm).2
    · intro JLoop JUnr bndA hdBnd hStepLoop i' m' hSum hJL hDone
      change wp Γ Q X (denote Val Cont (mkUnrollChain (stripJnzTrue body) i32 u) _ _) m'
      rw [← hkEq]
      exact mkUnrollChain_succ_wp hm hdBnd hStepLoop hDone k' i' m' (Nat.le_refl _)
        (by dsimp only [bvToNatW]; rw [hkEq]; exact hSum) hJL
  · refine unrollCountedSingle_wp_case hCtxV (Or.inr rfl) hu2 hu4 hwf.2 ?_ ?_ hwp
    · exact (matchCountedBody_wf (GOuter := GOuter) (D := [[i64]] ++ DOuter)
        (is32 := false) body hEmpty hwf.1 hm).2
    · intro JLoop JUnr bndA hdBnd hStepLoop i' m' hSum hJL hDone
      change wp Γ Q X (denote Val Cont (mkUnrollChain (stripJnzTrue body) i64 u) _ _) m'
      rw [← hkEq]
      exact mkUnrollChain_succ_wp hm hdBnd hStepLoop hDone k' i' m' (Nat.le_refl _)
        (by dsimp only [bvToNatW]; rw [hkEq]; exact hSum) hJL

private theorem callsOk_letBindTup {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {cont : TFlat rs} (hCont : PassFlatKit.callsOkTF allowed exits cont) :
    {ts : List Ty} → (args : Tup (Arg K) ts) → (d : Nat) →
    PassFlatKit.callsOkTF allowed exits (letBindTup args d cont)
  | [], (), _ => hCont
  | _ :: _, (_, rest), d => by
    dsimp only [letBindTup]; simp only [PassFlatKit.callsOkTF_let]
    exact callsOk_letBindTup hCont rest (d + 1)

mutual
private theorem callsOk_shiftTFlat {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (d n : Nat) : (tf : TFlat rs) →
    PassFlatKit.callsOkTF allowed exits tf → PassFlatKit.callsOkTF allowed exits (shiftTFlat d n tf)
  | .let_ (ts := ts) _ k, h => by
    unfold shiftTFlat; simp only [PassFlatKit.callsOkTF_let] at h ⊢
    exact callsOk_shiftTFlat (d + ts.length) n k h
  | .load _ _ k, h => by
    unfold shiftTFlat; simp only [PassFlatKit.callsOkTF_load] at h ⊢
    exact callsOk_shiftTFlat (d + 1) n k h
  | .store _ _ k, h => by
    unfold shiftTFlat; simp only [PassFlatKit.callsOkTF_store] at h ⊢
    exact callsOk_shiftTFlat d n k h
  | .call _ bs _ k, h => by
    unfold shiftTFlat; simp only [PassFlatKit.callsOkTF_call] at h ⊢
    exact ⟨h.1, callsOk_shiftTFlat (d + bs.length) n k h.2⟩
  | .jnz _ t e, h => by
    unfold shiftTFlat; simp only [PassFlatKit.callsOkTF_jnz] at h ⊢
    exact ⟨callsOk_shiftTFlat d n t h.1, callsOk_shiftTFlat d n e h.2⟩
  | .jump _ _, _ | .ret _, _ | .hlt, _ => by unfold shiftTFlat; trivial
  | .exit _ _, h => by unfold shiftTFlat; exact h
  | .group bs k, h => by
    unfold shiftTFlat; simp only [PassFlatKit.callsOkTF_group] at h ⊢
    exact ⟨callsOkB_shiftTBlocks d n bs h.1, callsOk_shiftTFlat d n k h.2⟩

private theorem callsOkB_shiftTBlocks {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (d n : Nat) : {sig : List (List Ty)} → (bs : TBlocks rs sig) →
    PassFlatKit.callsOkBs allowed exits bs →
    PassFlatKit.callsOkBs allowed exits (shiftTBlocks d n bs)
  | _, .nil, _ => by unfold shiftTBlocks; simp [PassFlatKit.callsOkBs_nil]
  | _, .cons (ts := ts) b bs, h => by
    unfold shiftTBlocks; simp only [PassFlatKit.callsOkBs_cons] at h ⊢
    exact ⟨callsOk_shiftTFlat (d + ts.length) n b h.1, callsOkB_shiftTBlocks d n bs h.2⟩
end

mutual
private theorem callsOk_inlineJumpTarget {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (nextBody : TFlat rs) (ivTy : Ty)
    (hNext : PassFlatKit.callsOkTF allowed exits nextBody) : (targetL d : Nat) → (tf : TFlat rs) →
    PassFlatKit.callsOkTF allowed exits tf →
    PassFlatKit.callsOkTF allowed exits (inlineJumpTarget nextBody ivTy targetL d tf)
  | targetL, d, .let_ (ts := ts) _ k, h => by
    dsimp only [inlineJumpTarget]; simp only [PassFlatKit.callsOkTF_let] at h ⊢
    exact callsOk_inlineJumpTarget nextBody ivTy hNext targetL (d + ts.length) k h
  | targetL, d, .load _ _ k, h => by
    dsimp only [inlineJumpTarget]; simp only [PassFlatKit.callsOkTF_load] at h ⊢
    exact callsOk_inlineJumpTarget nextBody ivTy hNext targetL (d + 1) k h
  | targetL, d, .store _ _ k, h => by
    dsimp only [inlineJumpTarget]; simp only [PassFlatKit.callsOkTF_store] at h ⊢
    exact callsOk_inlineJumpTarget nextBody ivTy hNext targetL d k h
  | targetL, d, .call _ bs _ k, h => by
    dsimp only [inlineJumpTarget]; simp only [PassFlatKit.callsOkTF_call] at h ⊢
    exact ⟨h.1, callsOk_inlineJumpTarget nextBody ivTy hNext targetL (d + bs.length) k h.2⟩
  | targetL, d, .jnz _ t e, h => by
    dsimp only [inlineJumpTarget]; simp only [PassFlatKit.callsOkTF_jnz] at h ⊢
    exact ⟨callsOk_inlineJumpTarget nextBody ivTy hNext targetL d t h.1,
      callsOk_inlineJumpTarget nextBody ivTy hNext targetL d e h.2⟩
  | targetL, d, .jump _ _, h => by
    dsimp only [inlineJumpTarget]; split
    · split
      · exact callsOk_letBindTup
          (callsOk_shiftTFlat 1 (d + 1) _ (callsOk_shiftLabelsTFlat 0 targetL nextBody hNext))
          _ 0
      · exact h
    · exact h
  | _, _, .ret _, h | _, _, .exit _ _, h | _, _, .hlt, h => h
  | targetL, d, .group (sig := sig) bs k, h => by
    dsimp only [inlineJumpTarget]; simp only [PassFlatKit.callsOkTF_group] at h ⊢
    exact callsOkB_inlineJumpTargetB nextBody ivTy hNext (targetL + sig.length) d bs h.1 |>
      fun h1 => ⟨h1, callsOk_inlineJumpTarget nextBody ivTy hNext (targetL + sig.length) d k h.2⟩

private theorem callsOkB_inlineJumpTargetB {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (nextBody : TFlat rs) (ivTy : Ty)
    (hNext : PassFlatKit.callsOkTF allowed exits nextBody) :
    (targetL d : Nat) → {sig : List (List Ty)} → (bs : TBlocks rs sig) →
    PassFlatKit.callsOkBs allowed exits bs →
    PassFlatKit.callsOkBs allowed exits (inlineJumpTargetB nextBody ivTy targetL d bs)
  | _, _, _, .nil, _ => trivial
  | targetL, d, _, .cons (ts := ts) b bs, h => by
    dsimp only [inlineJumpTargetB]; simp only [PassFlatKit.callsOkBs_cons] at h ⊢
    exact ⟨callsOk_inlineJumpTarget nextBody ivTy hNext targetL (d + ts.length) b h.1,
      callsOkB_inlineJumpTargetB nextBody ivTy hNext targetL d bs h.2⟩
end

private theorem callsOk_mkUnrollChain {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (stepBody : TFlat rs) (ivTy : Ty)
    (hStep : PassFlatKit.callsOkTF allowed exits stepBody) :
    ∀ u : Nat, PassFlatKit.callsOkTF allowed exits (mkUnrollChain stepBody ivTy u)
  | 0 => by simp [mkUnrollChain]
  | u + 1 =>
    callsOk_inlineJumpTarget (mkUnrollChain stepBody ivTy u) ivTy
      (callsOk_mkUnrollChain stepBody ivTy hStep u) 0 0 stepBody hStep

public theorem unrollCountedSingle_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs ts0 : List Ty} {unrollN : Nat} {body k res : TFlat rs}
    (hb : PassFlatKit.callsOkTF allowed exits body)
    (hu : unrollCountedSingle unrollN ts0 body k = some res) :
    PassFlatKit.callsOkTF allowed exits res := by
  obtain ⟨_, _, _, _, _, _, _, hCase⟩ := unrollCountedSingle_eq_some hu
  have hStep := callsOk_stripJnzTrue body hb
  have hWrap : ∀ (w : Nat) (isLt : Bool) (initArg bnd : Arg K (.bits w)) (u : Nat),
      PassFlatKit.callsOkTF allowed exits
        (mkUnrollWrapper (rs := rs) w isLt initArg bnd body u) := by
    intro w isLt _ _ u; dsimp only [mkUnrollWrapper]
    simp only [PassFlatKit.callsOkTF_group, PassFlatKit.callsOkBs_cons, PassFlatKit.callsOkBs_nil,
      PassFlatKit.callsOkTF_let, PassFlatKit.callsOkTF_jnz, PassFlatKit.callsOkTF_jump, and_true]
    exact callsOk_shiftTFlat 1 3 _ (callsOk_mkUnrollChain _ (.bits w) hStep u)
  rcases hCase with ⟨initArg, bnd, isLt, rfl, rfl, _, rfl⟩ |
      ⟨initArg, bnd, isLt, rfl, rfl, _, rfl⟩ <;> simp [hb, hWrap]

end ZeroPeel

end LeanQbe.T
