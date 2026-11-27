module

public import LeanQbe.T.LeanLCNF.Sem.LowerSound2a
public import LeanQbe.T.LeanLCNF.Sem.LowerSound2b
import LeanQbe.T.OpsLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.LeanLCNF.Sem.SpecNormProof

/-!
# Tier-H `String.*` and `ByteArray.*` Lowering Soundness (`LowerSound2c`)

Part 1 of the container / external-primitive Stage 2 proofs:
1. Shared heap-splitting and container-header load helpers (`hmem_focus_obj`,
   `lcnfHeap_eraseIdx`, `lcnfHeap_focus_two`, `lcnfObjMem_load_*`).
2. `String.*` monotonicity and simulation (`stringPrim_mono`, `stringPrim_sound`).
3. `ByteArray.*` monotonicity and simulation (`byteArrayPrim_mono`, `byteArrayPrim_sound`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Frontend.C0
open Std.ExtHashMap

/-! ## 1. Heap-Split & Container-Header Load Helpers -/

theorem hmem_focus_obj {rt : BitVec 64} {σ : HState} {R : Mem 64 → Prop} {mem : Mem 64}
    {idx : Nat} (hidx : idx < σ.objs.length) (hm : (σ.mem rt ⋆ R) mem) :
    ∃ F : Mem 64 → Prop, (lcnfObjMem σ.objs[idx] ⋆ F) mem := by
  rw [hstate_mem_unfold, lcnfHeap_focus σ.objs hidx] at hm
  exact ⟨lcnfHeap (σ.objs.take idx) ⋆ lcnfHeap (σ.objs.drop (idx + 1)) ⋆
    rtC0Inv rt σ.st ⋆ array64 σ.scr σ.scrLimbs ⋆
    cell64 (rt + 33672#64) σ.scr ⋆ cell64 (rt + 33680#64) (BitVec.ofNat 64 σ.scrLimbs.length) ⋆ R,
    sep_cast hm (by ac_rfl)⟩

theorem lcnfHeap_eraseIdx :
    ∀ (objs : List LcnfObj) {k : Nat} (_hk : k < objs.length),
      lcnfHeap objs = (lcnfObjMem objs[k] ⋆ lcnfHeap (objs.eraseIdx k))
  | [], _, hk => by simp at hk
  | _ :: _, 0, _ => by simp [lcnfHeap, List.eraseIdx]
  | x :: xs, k + 1, hk => by
    have hk' : k < xs.length := by simp at hk; omega
    have ih := lcnfHeap_eraseIdx xs hk'
    simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ, lcnfHeap]
    rw [ih, ← sep_assoc (lcnfObjMem x), sep_comm (lcnfObjMem x) (lcnfObjMem xs[k]),
      sep_assoc (lcnfObjMem xs[k])]

theorem lcnfHeap_focus_two {objs : List LcnfObj} {o1 o2 : LcnfObj} {F : Mem 64 → Prop}
    {m : Mem 64} (h1 : o1 ∈ objs) (h2 : o2 ∈ objs) (hneAddr : o1.addr ≠ o2.addr)
    (hm : (lcnfHeap objs ⋆ F) m) :
    ∃ R' : Mem 64 → Prop, (lcnfObjMem o1 ⋆ lcnfObjMem o2 ⋆ R') m := by
  obtain ⟨k1, hk1, rfl⟩ := List.mem_iff_getElem.mp h1
  obtain ⟨k2, hk2, heq2⟩ := List.mem_iff_getElem.mp h2
  have hneIdx : k2 ≠ k1 := fun e => by subst e; exact hneAddr (congrArg LcnfObj.addr heq2)
  rw [lcnfHeap_focus objs hk1] at hm
  rcases Nat.lt_or_gt_of_ne hneIdx with hlt | hgt
  · have hk2' : k2 < (objs.take k1).length := by simp [List.length_take]; omega
    have hget : (objs.take k1)[k2]'hk2' = o2 := by rw [List.getElem_take]; exact heq2
    rw [lcnfHeap_focus (objs.take k1) hk2', hget] at hm
    exact ⟨lcnfHeap ((objs.take k1).take k2) ⋆ lcnfHeap ((objs.take k1).drop (k2 + 1)) ⋆
      lcnfHeap (objs.drop (k1 + 1)) ⋆ F, sep_cast hm (by ac_rfl)⟩
  · have hk2' : k2 - k1 - 1 < (objs.drop (k1 + 1)).length := by simp [List.length_drop]; omega
    have hget : (objs.drop (k1 + 1))[k2 - k1 - 1]'hk2' = o2 := by
      rw [List.getElem_drop]
      simp only [show k1 + 1 + (k2 - k1 - 1) = k2 by omega]
      exact heq2
    rw [lcnfHeap_focus (objs.drop (k1 + 1)) hk2', hget] at hm
    exact ⟨lcnfHeap (objs.take k1) ⋆ lcnfHeap ((objs.drop (k1 + 1)).take (k2 - k1 - 1)) ⋆
      lcnfHeap ((objs.drop (k1 + 1)).drop (k2 - k1 - 1 + 1)) ⋆ F, sep_cast hm (by ac_rfl)⟩

theorem lcnfObjMem_load_arrSize_string {o : LcnfObj} {F : Mem 64 → Prop} {m : Mem 64}
    (hc : StrCanon o) (hm : (lcnfObjMem o ⋆ F) m) :
    loadVal m i64 (o.addr + 8#64) = some (BitVec.ofNat 64 o.arrSize) := by
  have htag := hc.2.2.2.2.2.1
  unfold lcnfObjMem at hm
  simp only [htag, stringTag, closureTag, arrayTag, sarrayTag,
    show (249 : Nat) ≠ 245 by decide, show (249 : Nat) ≠ 246 by decide,
    show (249 : Nat) ≠ 248 by decide, ↓reduceIte] at hm
  have hm' : (cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.arrSize) ⋆
      (cell64 o.addr o.header ⋆ cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
        cell64 (o.addr + 24#64) (BitVec.ofNat 64 o.strLen) ⋆
        bytes (o.addr + 32#64) o.scalarData ⋆
        region (o.addr + BitVec.ofNat 64 (32 + o.scalarData.length))
          (o.totalBytes - (32 + o.scalarData.length)) ⋆ F)) m :=
    sep_cast hm (by ac_rfl)
  exact loadVal_cell64 hm'

theorem lcnfObjMem_load_strLen_string {o : LcnfObj} {F : Mem 64 → Prop} {m : Mem 64}
    (hc : StrCanon o) (hm : (lcnfObjMem o ⋆ F) m) :
    loadVal m i64 (o.addr + 24#64) = some (BitVec.ofNat 64 o.strLen) := by
  have htag := hc.2.2.2.2.2.1
  unfold lcnfObjMem at hm
  simp only [htag, stringTag, closureTag, arrayTag, sarrayTag,
    show (249 : Nat) ≠ 245 by decide, show (249 : Nat) ≠ 246 by decide,
    show (249 : Nat) ≠ 248 by decide, ↓reduceIte] at hm
  have hm' : (cell64 (o.addr + 24#64) (BitVec.ofNat 64 o.strLen) ⋆
      (cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.arrSize) ⋆
        cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
        bytes (o.addr + 32#64) o.scalarData ⋆
        region (o.addr + BitVec.ofNat 64 (32 + o.scalarData.length))
          (o.totalBytes - (32 + o.scalarData.length)) ⋆ F)) m :=
    sep_cast hm (by ac_rfl)
  exact loadVal_cell64 hm'

theorem lcnfObjMem_load_fieldsLen_array {o : LcnfObj} {F : Mem 64 → Prop} {m : Mem 64}
    (hc : ArrCanon o) (hm : (lcnfObjMem o ⋆ F) m) :
    loadVal m i64 (o.addr + 8#64) = some (BitVec.ofNat 64 o.fields.length) := by
  have htag := hc.2.2.2.2.2.1
  unfold lcnfObjMem at hm
  simp only [htag, arrayTag, closureTag, show (246 : Nat) ≠ 245 by decide, ↓reduceIte] at hm
  have hm' : (cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
      (cell64 o.addr o.header ⋆ cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
        array64 (o.addr + 24#64) o.fields ⋆
        region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
          (8 * (o.cap - o.fields.length)) ⋆ F)) m :=
    sep_cast hm (by ac_rfl)
  exact loadVal_cell64 hm'

theorem lcnfObjMem_load_arrSize_ba {o : LcnfObj} {F : Mem 64 → Prop} {m : Mem 64}
    (hc : BaCanon o) (hm : (lcnfObjMem o ⋆ F) m) :
    loadVal m i64 (o.addr + 8#64) = some (BitVec.ofNat 64 o.arrSize) := by
  have htag := hc.2.2.2.2.2.1
  unfold lcnfObjMem at hm
  simp only [htag, sarrayTag, closureTag, arrayTag,
    show (248 : Nat) ≠ 245 by decide, show (248 : Nat) ≠ 246 by decide, ↓reduceIte] at hm
  have hm' : (cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.arrSize) ⋆
      (cell64 o.addr o.header ⋆ cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
        bytes (o.addr + 24#64) o.scalarData ⋆
        region (o.addr + BitVec.ofNat 64 (24 + o.scalarData.length))
          (o.totalBytes - (24 + o.scalarData.length)) ⋆ F)) m :=
    sep_cast hm (by ac_rfl)
  exact loadVal_cell64 hm'

theorem word_zext64_of_toBits {w : Nat} {word : Word} {bv : BitVec w}
    (h : word.toBits? w = some bv) : word.zext64 = bv.setWidth 64 := by
  cases word with
  | mk t v =>
    cases t with
    | bits bw =>
      dsimp [Word.toBits?] at h
      split at h
      · rename_i heq; subst heq; injection h with hbv; subst hbv; rfl
      · cases h
    | _ => cases h

theorem bv64_sub1_ofNat_eq {n : Nat} (h1 : 1 ≤ n) (hlt : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 1#64 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega : n - 1 < 2 ^ 64),
    Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64)]
  omega

theorem uintWidth?_cases {ty : String} {w : Nat} (h : uintWidth? ty = some w) :
    w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
  unfold uintWidth? at h
  split at h <;> cases h <;> omega

/-! ## 2. `String.*` Monotonicity & Simulation (`stringPrim_sound`) -/

theorem stringPrim_mono {rt : LArg} {parts : List String} {args : List LArg}
    {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) :
    LMMono (stringPrim rt parts args k) := by
  unfold stringPrim
  split
  all_goals first
    | exact lfail_mono
    | (dsimp only
       split
       all_goals first
         | exact lfail_mono
         | exact hk _
         | exact loadAt_mono fun _ => boxSmall_mono hk
         | exact loadAt_mono fun _ => sub64_mono fun _ => boxSmall_mono hk
         | exact rtCall1_mono hk)

private theorem isPhase1StringPrim_mem {parts : List String} {arity : Nat} {retTy : LcTy}
    (h : isPhase1StringPrim parts arity retTy = true) :
    (parts = ["length"] ∧ arity = 1) ∨
    (parts = ["Internal", "length"] ∧ arity = 1) ∨
    (parts = ["utf8ByteSize"] ∧ arity = 1) ∨
    (parts = ["propagateMark"] ∧ arity = 2) ∨
    (parts = ["append"] ∧ arity = 2) ∨
    (parts = ["Internal", "append"] ∧ arity = 2) ∨
    (parts = ["decEq"] ∧ arity = 2) ∨
    (parts = ["decidableLT"] ∧ arity = 2) := by
  unfold isPhase1StringPrim at h
  split at h <;> simp_all

private theorem stringAppend_rtCall1_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg s1Arg s2Arg : LArg}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt s1 s2 : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost} {X : HXPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (rtCall1 rtArg "lcnf_string_append" [s1Arg, s2Arg] 64 k).run n = .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (hs1Id : argIdsBelow s1Arg n) (hs1Ev : EvalRtArg ρ s1Arg s1)
    (hs2Id : argIdsBelow s2Arg n) (hs2Ev : EvalRtArg ρ s2Arg s2)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem) (hX : HXPostRel rt R X XT)
    (hpre : HStringAppendWp s1 s2 K X σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nr : Nat)
        (res : BitVec 64) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, n') → argIdsBelow r nr → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i64 r = some res → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K (Word.i64 res) σ' → LExpr.wp Γ QT XT ek ρ' J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  rcases hpre with ⟨s1Obj, hm1, ha1, hc1, s2Obj, hm2, ha2, hc2, hwf, hbody⟩
  dsimp only at hbody
  let scrFrame : Mem 64 → Prop :=
    cell64 (rt + 33672#64) σ.scr ⋆
    cell64 (rt + 33680#64) (BitVec.ofNat 64 σ.scrLimbs.length) ⋆
    array64 σ.scr σ.scrLimbs ⋆ R
  have hm' : (rtC0Inv rt σ.st ⋆ lcnfHeap σ.objs ⋆ scrFrame) mem := by
    rw [hstate_mem_unfold] at hm
    exact sep_cast hm (by dsimp only [scrFrame]; ac_rfl)
  let P : Post [i64] := fun (r, ()) m' =>
    ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m' ∧ K (Word.i64 r) σ'
  have hspec : lcnfStringAppendSpec (rt, s1, s2, ()) mem P XT := by
    refine ⟨σ.st, s1Obj, s2Obj, σ.objs, scrFrame, hm1, ha1, hc1, hm2, ha2, hc2, hwf, hm', ?_⟩
    dsimp only
    by_cases hp2 : (strPayload s2Obj).length = 0
    · rw [ite_eq_left hp2] at hbody ⊢
      exact ⟨σ, hinv, hm, hbody⟩
    · rw [ite_eq_right hp2] at hbody ⊢
      by_cases hcap : strMaxCap ≤ (strPayload s1Obj).length + (strPayload s2Obj).length
      · rw [ite_eq_left hcap] at hbody ⊢
        exact hX panicCapCode σ hbody mem hm
      · rw [ite_eq_right hcap] at hbody ⊢
        rcases hbody with ⟨hpreCond, hpost⟩
        refine ⟨hpreCond, fun r st' objs' m' hr0 hr8 hpm hrem hIn hNot hmObj => ?_⟩
        let σ' : HState := { σ with st := st', objs := objs' }
        have hmPost : (σ'.mem rt ⋆ R) m' := by
          rw [hstate_mem_unfold]
          exact sep_cast hmObj (by dsimp only [scrFrame, σ']; ac_rfl)
        exact ⟨σ', hinv_of_preservesMeta hinv hpm, hmPost,
          hpost r st' objs' hr0 hr8 hpm hrem hIn hNot⟩
  have hsig : ("lcnf_string_append", [i64, i64, i64], [i64]) ∈ rtCoreCallSigs := by decide
  refine rtCall1_wp hrun hrt hnrt (by simp [hs1Id, hs2Id])
    (evalRtArgs_cons hs1Ev (evalRtArgs_cons hs2Ev (evalRtArgs_nil ρ)))
    (hΓ.rt hsig (rtR2bEnv_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR2bEnv_lcnf_string_append hspec)))
    (fun _ _ _ _ h => h) ?_
  intro ret m' ⟨σ', hinv', hm'', hK⟩ r ek ρ' nr hnr hek hr hagr hrEv
  have hrEv' : LArg.eval ρ' i64 r = some ret := by simpa [BitVec.setWidth_eq] using hrEv
  exact hk r ek ρ' nr ret σ' m' hnr hek hr hagr hrEv' hinv' hm'' hK

private theorem stringCmpOp_rtCall1_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg s1Arg s2Arg : LArg} {code : Nat}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt s1 s2 : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hcode : code = 0 ∨ code = 1)
    (hrun : (rtCall1 rtArg "lcnf_string_cmp_op" [imm64 code, s1Arg, s2Arg] 8 k).run n =
      .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (hs1Id : argIdsBelow s1Arg n) (hs1Ev : EvalRtArg ρ s1Arg s1)
    (hs2Id : argIdsBelow s2Arg n) (hs2Ev : EvalRtArg ρ s2Arg s2)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hpre : if s1 = s2 then K (Word.i8 (if code = 0 then 1#8 else 0#8)) σ
      else ∃ s1Obj ∈ σ.objs, s1Obj.addr = s1 ∧ StrCanon s1Obj ∧
        ∃ s2Obj ∈ σ.objs, s2Obj.addr = s2 ∧ StrCanon s2Obj ∧
          K (Word.i8 ((strCmpOpVal (BitVec.ofNat 64 code)
            (strPayload s1Obj) (strPayload s2Obj)).setWidth 8)) σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nr : Nat)
        (res : BitVec 8) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, n') → argIdsBelow r nr → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i8 r = some res → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K (Word.i8 res) σ' → LExpr.wp Γ QT XT ek ρ' J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  let P : Post [i64] := fun (r, ()) m' => m' = mem ∧ K (Word.i8 (r.setWidth 8)) σ
  have hspec : lcnfStringCmpOpSpec (rt, BitVec.ofNat 64 code, s1, s2, ()) mem P
      (fun _ _ _ _ => False) := by
    dsimp only [lcnfStringCmpOpSpec]
    have hop : BitVec.ofNat 64 code = 0#64 ∨ BitVec.ofNat 64 code = 1#64 ∨
        BitVec.ofNat 64 code = 2#64 := by
      rcases hcode with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    rw [ite_eq_left hop]
    by_cases hs : s1 = s2
    · rw [ite_eq_left hs] at hpre ⊢
      refine ⟨rfl, ?_⟩
      rcases hcode with rfl | rfl <;> simpa [strCmpOpVal, cmpByteSlices] using hpre
    · rw [ite_eq_right hs] at hpre ⊢
      rcases hpre with ⟨s1Obj, hm1, ha1, hc1, s2Obj, hm2, ha2, hc2, hK⟩
      have hneAddr : s1Obj.addr ≠ s2Obj.addr := by rw [ha1, ha2]; exact hs
      have hmHeap : (lcnfHeap σ.objs ⋆
          (fullRtInv rt σ.st σ.scr σ.scrLimbs ⋆ R)) mem := by
        rw [hstate_mem_unfold] at hm
        dsimp only [fullRtInv]
        exact sep_cast hm (by ac_rfl)
      obtain ⟨R', hmTwo⟩ := lcnfHeap_focus_two hm1 hm2 hneAddr hmHeap
      exact ⟨s1Obj, s2Obj, R', ha1, hc1, ha2, hc2, hmTwo, rfl, hK⟩
  have hsig : ("lcnf_string_cmp_op", [i64, i64, i64, i64], [i64]) ∈ rtCoreCallSigs := by decide
  have hids : ∀ a ∈ [imm64 code, s1Arg, s2Arg], argIdsBelow a n := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact argIdsBelow_imm _ _ _
    · exact hs1Id
    · exact hs2Id
  refine rtCall1_wp hrun hrt hnrt hids
    (evalRtArgs_cons (evalRtArg_imm64 ρ code)
      (evalRtArgs_cons hs1Ev (evalRtArgs_cons hs2Ev (evalRtArgs_nil ρ))))
    (hΓ.rt hsig (rtR2bEnv_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR2bEnv_lcnf_string_cmp_op hspec)))
    (fun _ _ _ _ hf => False.elim hf) ?_
  intro ret m' hP r ek ρ' nr hnr hek hr hagr hrEv
  dsimp only [P] at hP
  rw [hP.1]
  exact hk r ek ρ' nr (ret.setWidth 8) σ mem hnr hek hr hagr hrEv hinv hm hP.2

theorem stringPrim_sound {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg : LArg} {parts : List String} {args : List LArg}
    {retTy : LcTy} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {ws : List Word} {K : HPost} {X : HXPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hprim : isPhase1StringPrim parts args.length retTy = true)
    (hrun : (stringPrim rtArg parts args k).run n = .ok (e, n'))
    (_hkMono : ∀ r, LMMono (k r))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (hargsIds : ∀ a ∈ args, argIdsBelow a n) (hargsEv : EvalWordArgs ρ args ws)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem) (hX : HXPostRel rt R X XT)
    (hwp : HStringPrimWp parts ws K X σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  rcases isPhase1StringPrim_mem hprim with
    ⟨rfl, har⟩ | ⟨rfl, har⟩ | ⟨rfl, har⟩ | ⟨rfl, har⟩ |
    ⟨rfl, har⟩ | ⟨rfl, har⟩ | ⟨rfl, har⟩ | ⟨rfl, har⟩
  · -- ["length"]
    rcases args with _ | ⟨sArg, _ | _⟩ <;> simp at har
    rcases ws with _ | ⟨ws0, _ | _⟩
    · simp [EvalWordArgs] at hargsEv
    · have hsId := hargsIds sArg List.mem_cons_self
      have hsW := hargsEv.2 (sArg, ws0) List.mem_cons_self
      simp only [HStringPrimWp] at hwp
      cases hws : ws0.toBV64? with
      | none => simp [hws] at hwp
      | some s =>
        simp only [hws] at hwp
        rcases hwp with ⟨sObj, hmS, haS, hcS, hK⟩
        obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hmS
        obtain ⟨_, hmObj⟩ := hmem_focus_obj hidx hm
        have hload : loadVal mem i64 (s + BitVec.ofNat 64 24) =
            some (BitVec.ofNat 64 σ.objs[idx].strLen) := by
          rw [← haS]; exact lcnfObjMem_load_strLen_string hcS hmObj
        unfold stringPrim at hrun
        refine lm_loadAt_wp hrun (hsW.toBV64? hws) hsId hload ?_
        intro nArg ek1 ρ1 n1 hn1 hek1 _ hagr1 hnEv
        refine boxSmall_wp hek1 hnEv ?_
        intro rArg ek2 ρ2 hek2 hrId hagr2 hrEv
        exact hk rArg ek2 ρ2 J (n1 + 2) n' 64 _ σ mem (by omega) hek2 hrId
          ((hagr2.mono (by omega : n ≤ n1)).trans hagr1) (JEnvAgreeBelow.refl n J) hrEv hinv hm hK
    · simp [EvalWordArgs] at hargsEv
  · -- ["Internal", "length"]
    rcases args with _ | ⟨sArg, _ | _⟩ <;> simp at har
    rcases ws with _ | ⟨ws0, _ | _⟩
    · simp [EvalWordArgs] at hargsEv
    · have hsId := hargsIds sArg List.mem_cons_self
      have hsW := hargsEv.2 (sArg, ws0) List.mem_cons_self
      simp only [HStringPrimWp] at hwp
      cases hws : ws0.toBV64? with
      | none => simp [hws] at hwp
      | some s =>
        simp only [hws] at hwp
        rcases hwp with ⟨sObj, hmS, haS, hcS, hK⟩
        obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hmS
        obtain ⟨_, hmObj⟩ := hmem_focus_obj hidx hm
        have hload : loadVal mem i64 (s + BitVec.ofNat 64 24) =
            some (BitVec.ofNat 64 σ.objs[idx].strLen) := by
          rw [← haS]; exact lcnfObjMem_load_strLen_string hcS hmObj
        unfold stringPrim at hrun
        refine lm_loadAt_wp hrun (hsW.toBV64? hws) hsId hload ?_
        intro nArg ek1 ρ1 n1 hn1 hek1 _ hagr1 hnEv
        refine boxSmall_wp hek1 hnEv ?_
        intro rArg ek2 ρ2 hek2 hrId hagr2 hrEv
        exact hk rArg ek2 ρ2 J (n1 + 2) n' 64 _ σ mem (by omega) hek2 hrId
          ((hagr2.mono (by omega : n ≤ n1)).trans hagr1) (JEnvAgreeBelow.refl n J) hrEv hinv hm hK
    · simp [EvalWordArgs] at hargsEv
  · -- ["utf8ByteSize"]
    rcases args with _ | ⟨sArg, _ | _⟩ <;> simp at har
    rcases ws with _ | ⟨ws0, _ | _⟩
    · simp [EvalWordArgs] at hargsEv
    · have hsId := hargsIds sArg List.mem_cons_self
      have hsW := hargsEv.2 (sArg, ws0) List.mem_cons_self
      simp only [HStringPrimWp] at hwp
      cases hws : ws0.toBV64? with
      | none => simp [hws] at hwp
      | some s =>
        simp only [hws] at hwp
        rcases hwp with ⟨sObj, hmS, haS, hcS, hK⟩
        obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hmS
        obtain ⟨_, hmObj⟩ := hmem_focus_obj hidx hm
        have hload : loadVal mem i64 (s + BitVec.ofNat 64 8) =
            some (BitVec.ofNat 64 σ.objs[idx].arrSize) := by
          rw [← haS]; exact lcnfObjMem_load_arrSize_string hcS hmObj
        unfold stringPrim at hrun
        refine lm_loadAt_wp hrun (hsW.toBV64? hws) hsId hload ?_
        intro nArg ek1 ρ1 n1 hn1 hek1 _ hagr1 hnEv
        refine sub64_wp hek1 hnEv (LArg.eval_imm_self ρ1 i64 1#64) ?_
        intro bArg ek2 ρ2 hek2 _ hagr2 hbEv
        have h1 : 1 ≤ σ.objs[idx].arrSize := hcS.2.2.2.2.2.2.1
        have hlt : σ.objs[idx].arrSize < 2 ^ 64 := by
          have := hcS.2.2.2.2.2.2.2.1
          have := hcS.2.2.2.2.2.2.2.2.1
          unfold strMaxCap at *; omega
        rw [bv64_sub1_ofNat_eq h1 hlt] at hbEv
        refine boxSmall_wp hek2 hbEv ?_
        intro rArg ek3 ρ3 hek3 hrId hagr3 hrEv
        exact hk rArg ek3 ρ3 J (n1 + 1 + 2) n' 64 _ σ mem (by omega) hek3 hrId
          (((hagr3.mono (by omega : n ≤ n1 + 1)).trans (hagr2.mono (by omega : n ≤ n1))).trans
            hagr1)
          (JEnvAgreeBelow.refl n J) hrEv hinv hm hK
    · simp [EvalWordArgs] at hargsEv
  · -- ["propagateMark"]
    rcases args with _ | ⟨a0, _ | ⟨iArg, _ | _⟩⟩ <;> simp at har
    rcases ws with _ | ⟨w0, _ | ⟨wi, _ | _⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have hiId := hargsIds iArg (List.mem_cons_of_mem _ List.mem_cons_self)
      have hiW := hargsEv.2 (iArg, wi) (List.mem_cons_of_mem _ List.mem_cons_self)
      rcases hiW with ⟨bw, bv, _, rfl, hiEv⟩
      simp only [HStringPrimWp] at hwp
      unfold stringPrim at hrun
      exact hk iArg e ρ J n n' bw bv σ mem (Nat.le_refl n) hrun hiId
        (VEnvAgreeBelow.refl n ρ) (JEnvAgreeBelow.refl n J) hiEv hinv hm hwp.2
    · simp [EvalWordArgs] at hargsEv
  · -- ["append"]
    rcases args with _ | ⟨s1Arg, _ | ⟨s2Arg, _ | _⟩⟩ <;> simp at har
    rcases ws with _ | ⟨w1, _ | ⟨w2, _ | _⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have hs1Id := hargsIds s1Arg List.mem_cons_self
      have hs2Id := hargsIds s2Arg (List.mem_cons_of_mem _ List.mem_cons_self)
      have hs1W := hargsEv.2 (s1Arg, w1) List.mem_cons_self
      have hs2W := hargsEv.2 (s2Arg, w2) (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [HStringPrimWp] at hwp
      cases hw1 : w1.toBV64? with
      | none => simp [hw1] at hwp
      | some s1 => cases hw2 : w2.toBV64? with
        | none => simp [hw1, hw2] at hwp
        | some s2 =>
          simp only [hw1, hw2] at hwp
          unfold stringPrim at hrun
          exact stringAppend_rtCall1_wp hΓ hrun hrt hnrt hs1Id (hs1W.toRtArgBV64 hw1)
            hs2Id (hs2W.toRtArgBV64 hw2) hinv hm hX hwp fun r ek ρ' nr res σ' m' hnr hek hr
            hagr hrEv hinv' hm' hK =>
            hk r ek ρ' J nr n' 64 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J) hrEv
              hinv' hm' hK
    · simp [EvalWordArgs] at hargsEv
  · -- ["Internal", "append"]
    rcases args with _ | ⟨s1Arg, _ | ⟨s2Arg, _ | _⟩⟩ <;> simp at har
    rcases ws with _ | ⟨w1, _ | ⟨w2, _ | _⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have hs1Id := hargsIds s1Arg List.mem_cons_self
      have hs2Id := hargsIds s2Arg (List.mem_cons_of_mem _ List.mem_cons_self)
      have hs1W := hargsEv.2 (s1Arg, w1) List.mem_cons_self
      have hs2W := hargsEv.2 (s2Arg, w2) (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [HStringPrimWp] at hwp
      cases hw1 : w1.toBV64? with
      | none => simp [hw1] at hwp
      | some s1 => cases hw2 : w2.toBV64? with
        | none => simp [hw1, hw2] at hwp
        | some s2 =>
          simp only [hw1, hw2] at hwp
          unfold stringPrim at hrun
          exact stringAppend_rtCall1_wp hΓ hrun hrt hnrt hs1Id (hs1W.toRtArgBV64 hw1)
            hs2Id (hs2W.toRtArgBV64 hw2) hinv hm hX hwp fun r ek ρ' nr res σ' m' hnr hek hr
            hagr hrEv hinv' hm' hK =>
            hk r ek ρ' J nr n' 64 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J) hrEv
              hinv' hm' hK
    · simp [EvalWordArgs] at hargsEv
  · -- ["decEq"]
    rcases args with _ | ⟨s1Arg, _ | ⟨s2Arg, _ | _⟩⟩ <;> simp at har
    rcases ws with _ | ⟨w1, _ | ⟨w2, _ | _⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have hs1Id := hargsIds s1Arg List.mem_cons_self
      have hs2Id := hargsIds s2Arg (List.mem_cons_of_mem _ List.mem_cons_self)
      have hs1W := hargsEv.2 (s1Arg, w1) List.mem_cons_self
      have hs2W := hargsEv.2 (s2Arg, w2) (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [HStringPrimWp] at hwp
      cases hw1 : w1.toBV64? with
      | none => simp [hw1] at hwp
      | some s1 => cases hw2 : w2.toBV64? with
        | none => simp [hw1, hw2] at hwp
        | some s2 =>
          simp only [hw1, hw2] at hwp
          unfold stringPrim at hrun
          exact stringCmpOp_rtCall1_wp hΓ (Or.inl rfl) hrun hrt hnrt hs1Id
            (hs1W.toRtArgBV64 hw1) hs2Id (hs2W.toRtArgBV64 hw2) hinv hm hwp fun r ek ρ' nr res
            σ' m' hnr hek hr hagr hrEv hinv' hm' hK =>
            hk r ek ρ' J nr n' 8 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J) hrEv
              hinv' hm' hK
    · simp [EvalWordArgs] at hargsEv
  · -- ["decidableLT"]
    rcases args with _ | ⟨s1Arg, _ | ⟨s2Arg, _ | _⟩⟩ <;> simp at har
    rcases ws with _ | ⟨w1, _ | ⟨w2, _ | _⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have hs1Id := hargsIds s1Arg List.mem_cons_self
      have hs2Id := hargsIds s2Arg (List.mem_cons_of_mem _ List.mem_cons_self)
      have hs1W := hargsEv.2 (s1Arg, w1) List.mem_cons_self
      have hs2W := hargsEv.2 (s2Arg, w2) (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [HStringPrimWp] at hwp
      cases hw1 : w1.toBV64? with
      | none => simp [hw1] at hwp
      | some s1 => cases hw2 : w2.toBV64? with
        | none => simp [hw1, hw2] at hwp
        | some s2 =>
          simp only [hw1, hw2] at hwp
          unfold stringPrim at hrun
          exact stringCmpOp_rtCall1_wp hΓ (Or.inr rfl) hrun hrt hnrt hs1Id
            (hs1W.toRtArgBV64 hw1) hs2Id (hs2W.toRtArgBV64 hw2) hinv hm hwp fun r ek ρ' nr res
            σ' m' hnr hek hr hagr hrEv hinv' hm' hK =>
            hk r ek ρ' J nr n' 8 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J) hrEv
              hinv' hm' hK
    · simp [EvalWordArgs] at hargsEv

/-! ## 3. `ByteArray.*` Monotonicity & Simulation (`byteArrayPrim_sound`) -/

theorem byteArrayPrim_mono {rt : LArg} {op : String} {args : List LArg} {k : LArg → LM LExpr}
    (hk : ∀ r, LMMono (k r)) : LMMono (byteArrayPrim rt op args k) := by
  unfold byteArrayPrim
  split
  all_goals first
    | exact lfail_mono
    | exact hk _
    | exact loadAt_mono fun _ => boxSmall_mono hk
    | exact loadAt_mono hk
    | exact rtCall1_mono hk

private theorem isPhase1ByteArrayPrim_mem {op : String} {arity : Nat} {retTy : LcTy}
    (h : isPhase1ByteArrayPrim op arity retTy = true) :
    (op = "size" ∧ arity = 1) ∨
    (op = "usize" ∧ arity = 1) ∨
    (op = "propagateMark" ∧ arity = 2) ∨
    (op = "push" ∧ arity = 2) ∨
    (op = "get!" ∧ arity = 2) ∨
    (op = "get" ∧ arity = 3) := by
  unfold isPhase1ByteArrayPrim at h
  split at h <;> simp_all

private theorem baGet_rtCall1_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg baArg idxArg : LArg}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt ba idx : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (rtCall1 rtArg "lcnf_ba_get" [baArg, idxArg, imm64 0] 8 k).run n = .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (hbaId : argIdsBelow baArg n) (hbaEv : EvalRtArg ρ baArg ba)
    (hidxId : argIdsBelow idxArg n) (hidxEv : EvalRtArg ρ idxArg idx)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hpre : ∃ baObj ∈ σ.objs, baObj.addr = ba ∧ BaCanon baObj ∧
      K (Word.i8 ((baGetVal baObj.scalarData idx 0#64).setWidth 8)) σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nr : Nat)
        (res : BitVec 8) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, n') → argIdsBelow r nr → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i8 r = some res → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K (Word.i8 res) σ' → LExpr.wp Γ QT XT ek ρ' J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  rcases hpre with ⟨baObj, hmBa, haBa, hcBa, hK⟩
  obtain ⟨idxO, hidxO, rfl⟩ := List.mem_iff_getElem.mp hmBa
  obtain ⟨F, hmObj⟩ := hmem_focus_obj hidxO hm
  let P : Post [i64] := fun (r, ()) m' => m' = mem ∧ K (Word.i8 (r.setWidth 8)) σ
  have hspec : lcnfBaGetSpec (rt, ba, idx, 0#64, ()) mem P (fun _ _ _ _ => False) :=
    ⟨σ.objs[idxO], F, haBa, hcBa, hmObj, rfl, hK⟩
  have hsig : ("lcnf_ba_get", [i64, i64, i64, i64], [i64]) ∈ rtCoreCallSigs := by decide
  have hids : ∀ a ∈ [baArg, idxArg, imm64 0], argIdsBelow a n := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact hbaId
    · exact hidxId
    · exact argIdsBelow_imm _ _ _
  refine rtCall1_wp hrun hrt hnrt hids
    (evalRtArgs_cons hbaEv (evalRtArgs_cons hidxEv
      (evalRtArgs_cons (evalRtArg_imm64 ρ 0) (evalRtArgs_nil ρ))))
    (hΓ.rt hsig (rtR2Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR2Env_lcnf_ba_get hspec)))
    (fun _ _ _ _ hf => False.elim hf) ?_
  intro ret m' hP r ek ρ' nr hnr hek hr hagr hrEv
  dsimp only [P] at hP
  rw [hP.1]
  exact hk r ek ρ' nr (ret.setWidth 8) σ mem hnr hek hr hagr hrEv hinv hm hP.2

private theorem baPush_rtCall1_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg baArg bArg : LArg}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt ba : BitVec 64} {b : BitVec 8}
    {σ : HState} {R : Mem 64 → Prop} {K : HPost} {X : HXPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (rtCall1 rtArg "lcnf_ba_push" [baArg, bArg] 64 k).run n = .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (hbaId : argIdsBelow baArg n) (hbaEv : EvalRtArg ρ baArg ba)
    (hbId : argIdsBelow bArg n) (hbEv : EvalRtArg ρ bArg (b.setWidth 64))
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem) (hX : HXPostRel rt R X XT)
    (hpre : ∃ (idx : Nat) (hidx : idx < σ.objs.length),
      let baObj := σ.objs[idx]'hidx
      baObj.addr = ba ∧ BaCanon baObj ∧
      if baObj.cap ≤ baObj.arrSize ∧ baMaxCap ≤ baObj.cap then X panicCapCode σ
      else
        let newCap := baEnsureCap baObj.arrSize baObj.cap 1#64
        let needAlloc := baObj.rc ≠ 1#32 ∨ baObj.arrSize ≥ baObj.cap
        (needAlloc → canAllocBytesR0 σ.st (baAllocBytes newCap)) ∧
        ∀ r st',
          r ≠ 0#64 → r.toNat % 8 = 0 → st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem →
          (baObj.rc = 1#32 → baObj.arrSize < baObj.cap → r = ba ∧ st' = σ.st) →
          let rObj := mkBaObj r 1#32 newCap (baObj.scalarData ++ [UInt8.ofNat b.toNat])
          BaCanon rObj →
          let objs' :=
            if baObj.rc = 1#32 then σ.objs.set idx rObj
            else rObj :: σ.objs.set idx (baObj.withRc (decNonExclRc baObj.rc))
          K (Word.i64 r) { σ with st := st', objs := objs' })
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nr : Nat)
        (res : BitVec 64) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, n') → argIdsBelow r nr → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i64 r = some res → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K (Word.i64 res) σ' → LExpr.wp Γ QT XT ek ρ' J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  rcases hpre with ⟨idx, hidx, ha, hc, hbody⟩
  let baObj := σ.objs[idx]'hidx
  let scrFrame : Mem 64 → Prop :=
    lcnfHeap (σ.objs.take idx) ⋆ lcnfHeap (σ.objs.drop (idx + 1)) ⋆
    cell64 (rt + 33672#64) σ.scr ⋆
    cell64 (rt + 33680#64) (BitVec.ofNat 64 σ.scrLimbs.length) ⋆
    array64 σ.scr σ.scrLimbs ⋆ R
  have hm' : (rtC0Inv rt σ.st ⋆ lcnfObjMem baObj ⋆ scrFrame) mem := by
    rw [hstate_mem_unfold, lcnfHeap_focus σ.objs hidx] at hm
    exact sep_cast hm (by dsimp only [scrFrame, baObj]; ac_rfl)
  have hbToNat : UInt8.ofNat (b.setWidth 64).toNat = UInt8.ofNat b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
  let P : Post [i64] := fun (r, ()) m' =>
    ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m' ∧ K (Word.i64 r) σ'
  have hspec : lcnfBaPushSpec (rt, ba, b.setWidth 64, ()) mem P XT := by
    refine ⟨σ.st, baObj, scrFrame, ha, hc, hm', ?_⟩
    dsimp only at hbody ⊢
    by_cases hp : baObj.cap ≤ baObj.arrSize ∧ baMaxCap ≤ baObj.cap
    · rw [ite_eq_left hp] at hbody ⊢; exact hX panicCapCode σ hbody mem hm
    · rw [ite_eq_right hp] at hbody ⊢
      rcases hbody with ⟨hneed, hpost⟩
      refine ⟨hneed, fun r st' m' hr0 hr8 hpm hrem hIn hcan hmObj => ?_⟩
      rw [hbToNat] at hcan hmObj
      let newCap := baEnsureCap baObj.arrSize baObj.cap 1#64
      let rObj := mkBaObj r 1#32 newCap (baObj.scalarData ++ [UInt8.ofNat b.toNat])
      let objs' :=
        if baObj.rc = 1#32 then σ.objs.set idx rObj
        else rObj :: σ.objs.set idx (baObj.withRc (decNonExclRc baObj.rc))
      let σ' : HState := { σ with st := st', objs := objs' }
      have hmPost : (σ'.mem rt ⋆ R) m' := by
        rw [hstate_mem_unfold]
        dsimp only [σ', objs']
        by_cases hrc1 : baObj.rc = 1#32
        · simp only [hrc1, ↓reduceIte] at hmObj ⊢
          rw [lcnfHeap_set σ.objs hidx rObj]
          exact sep_cast hmObj (by dsimp only [scrFrame, newCap, rObj]; ac_rfl)
        · simp only [hrc1, ↓reduceIte] at hmObj ⊢
          rw [lcnfHeap.eq_2, lcnfHeap_set σ.objs hidx (baObj.withRc (decNonExclRc baObj.rc))]
          exact sep_cast hmObj (by dsimp only [scrFrame, newCap, rObj, baObj]; ac_rfl)
      exact ⟨σ', hinv_of_preservesMeta hinv hpm, hmPost,
        hpost r st' hr0 hr8 hpm hrem hIn hcan⟩
  have hsig : ("lcnf_ba_push", [i64, i64, i64], [i64]) ∈ rtCoreCallSigs := by decide
  refine rtCall1_wp hrun hrt hnrt (by simp [hbaId, hbId])
    (evalRtArgs_cons hbaEv (evalRtArgs_cons hbEv (evalRtArgs_nil ρ)))
    (hΓ.rt hsig (rtR2Env_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR2Env_lcnf_ba_push hspec)))
    (fun _ _ _ _ h => h) ?_
  intro ret m' ⟨σ', hinv', hm'', hK⟩ r ek ρ' nr hnr hek hr hagr hrEv
  have hrEv' : LArg.eval ρ' i64 r = some ret := by simpa [BitVec.setWidth_eq] using hrEv
  exact hk r ek ρ' nr ret σ' m' hnr hek hr hagr hrEv' hinv' hm'' hK

theorem byteArrayPrim_sound {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg : LArg} {op : String} {args : List LArg}
    {retTy : LcTy} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {ws : List Word} {K : HPost} {X : HXPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hprim : isPhase1ByteArrayPrim op args.length retTy = true)
    (hrun : (byteArrayPrim rtArg op args k).run n = .ok (e, n'))
    (_hkMono : ∀ r, LMMono (k r))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (hargsIds : ∀ a ∈ args, argIdsBelow a n) (hargsEv : EvalWordArgs ρ args ws)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem) (hX : HXPostRel rt R X XT)
    (hwp : HByteArrayPrimWp op ws K X σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  rcases isPhase1ByteArrayPrim_mem hprim with
    ⟨rfl, har⟩ | ⟨rfl, har⟩ | ⟨rfl, har⟩ | ⟨rfl, har⟩ | ⟨rfl, har⟩ | ⟨rfl, har⟩
  · -- "size"
    rcases args with _ | ⟨baArg, _ | _⟩ <;> simp at har
    rcases ws with _ | ⟨wba, _ | _⟩
    · simp [EvalWordArgs] at hargsEv
    · have hbaId := hargsIds baArg List.mem_cons_self
      have hbaW := hargsEv.2 (baArg, wba) List.mem_cons_self
      simp only [HByteArrayPrimWp] at hwp
      cases hwba : wba.toBV64? with
      | none => simp [hwba] at hwp
      | some ba =>
        simp only [hwba] at hwp
        rcases hwp with ⟨baObj, hmBa, haBa, hcBa, hK⟩
        obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hmBa
        obtain ⟨_, hmObj⟩ := hmem_focus_obj hidx hm
        have hload : loadVal mem i64 (ba + BitVec.ofNat 64 8) =
            some (BitVec.ofNat 64 σ.objs[idx].arrSize) := by
          rw [← haBa]; exact lcnfObjMem_load_arrSize_ba hcBa hmObj
        unfold byteArrayPrim at hrun
        refine lm_loadAt_wp hrun (hbaW.toBV64? hwba) hbaId hload ?_
        intro szArg ek1 ρ1 n1 hn1 hek1 _ hagr1 hszEv
        refine boxSmall_wp hek1 hszEv ?_
        intro rArg ek2 ρ2 hek2 hrId hagr2 hrEv
        exact hk rArg ek2 ρ2 J (n1 + 2) n' 64 _ σ mem (by omega) hek2 hrId
          ((hagr2.mono (by omega : n ≤ n1)).trans hagr1) (JEnvAgreeBelow.refl n J) hrEv hinv hm hK
    · simp [EvalWordArgs] at hargsEv
  · -- "usize"
    rcases args with _ | ⟨baArg, _ | _⟩ <;> simp at har
    rcases ws with _ | ⟨wba, _ | _⟩
    · simp [EvalWordArgs] at hargsEv
    · have hbaId := hargsIds baArg List.mem_cons_self
      have hbaW := hargsEv.2 (baArg, wba) List.mem_cons_self
      simp only [HByteArrayPrimWp] at hwp
      cases hwba : wba.toBV64? with
      | none => simp [hwba] at hwp
      | some ba =>
        simp only [hwba] at hwp
        rcases hwp with ⟨baObj, hmBa, haBa, hcBa, hK⟩
        obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hmBa
        obtain ⟨_, hmObj⟩ := hmem_focus_obj hidx hm
        have hload : loadVal mem i64 (ba + BitVec.ofNat 64 8) =
            some (BitVec.ofNat 64 σ.objs[idx].arrSize) := by
          rw [← haBa]; exact lcnfObjMem_load_arrSize_ba hcBa hmObj
        unfold byteArrayPrim at hrun
        refine lm_loadAt_wp hrun (hbaW.toBV64? hwba) hbaId hload ?_
        intro szArg ek1 ρ1 n1 hn1 hek1 hszId hagr1 hszEv
        exact hk szArg ek1 ρ1 J n1 n' 64 _ σ mem (by omega) hek1 hszId hagr1
          (JEnvAgreeBelow.refl n J) hszEv hinv hm hK
    · simp [EvalWordArgs] at hargsEv
  · -- "propagateMark"
    rcases args with _ | ⟨a0, _ | ⟨bArg, _ | _⟩⟩ <;> simp at har
    rcases ws with _ | ⟨w0, _ | ⟨wb, _ | _⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have hbId := hargsIds bArg (List.mem_cons_of_mem _ List.mem_cons_self)
      have hbW := hargsEv.2 (bArg, wb) (List.mem_cons_of_mem _ List.mem_cons_self)
      rcases hbW with ⟨bw, bv, _, rfl, hbEv⟩
      simp only [HByteArrayPrimWp] at hwp
      unfold byteArrayPrim at hrun
      exact hk bArg e ρ J n n' bw bv σ mem (Nat.le_refl n) hrun hbId
        (VEnvAgreeBelow.refl n ρ) (JEnvAgreeBelow.refl n J) hbEv hinv hm hwp.2
    · simp [EvalWordArgs] at hargsEv
  · -- "push"
    rcases args with _ | ⟨baArg, _ | ⟨bArg, _ | _⟩⟩ <;> simp at har
    rcases ws with _ | ⟨wba, _ | ⟨wb, _ | _⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have hbaId := hargsIds baArg List.mem_cons_self
      have hbId := hargsIds bArg (List.mem_cons_of_mem _ List.mem_cons_self)
      have hbaW := hargsEv.2 (baArg, wba) List.mem_cons_self
      have hbW := hargsEv.2 (bArg, wb) (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [HByteArrayPrimWp] at hwp
      cases hwba : wba.toBV64? with
      | none => simp [hwba] at hwp
      | some ba => cases hwb : wb.toBits? 8 with
        | none => simp [hwba, hwb] at hwp
        | some b8 =>
          simp only [hwba, hwb] at hwp
          have hbRt : EvalRtArg ρ bArg (b8.setWidth 64) := by
            rw [← word_zext64_of_toBits hwb]; exact hbW.toRtArg
          unfold byteArrayPrim at hrun
          exact baPush_rtCall1_wp hΓ hrun hrt hnrt hbaId (hbaW.toRtArgBV64 hwba)
            hbId hbRt hinv hm hX hwp fun r ek ρ' nr res σ' m' hnr hek hr hagr hrEv
            hinv' hm' hK =>
            hk r ek ρ' J nr n' 64 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J) hrEv
              hinv' hm' hK
    · simp [EvalWordArgs] at hargsEv
  · -- "get!"
    rcases args with _ | ⟨baArg, _ | ⟨idxArg, _ | _⟩⟩ <;> simp at har
    rcases ws with _ | ⟨wba, _ | ⟨wi, _ | _⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have hbaId := hargsIds baArg List.mem_cons_self
      have hiId := hargsIds idxArg (List.mem_cons_of_mem _ List.mem_cons_self)
      have hbaW := hargsEv.2 (baArg, wba) List.mem_cons_self
      have hiW := hargsEv.2 (idxArg, wi) (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [HByteArrayPrimWp] at hwp
      cases hwba : wba.toBV64? with
      | none => simp [hwba] at hwp
      | some ba => cases hwi : wi.toBV64? with
        | none => simp [hwba, hwi] at hwp
        | some idx =>
          simp only [hwba, hwi] at hwp
          unfold byteArrayPrim at hrun
          exact baGet_rtCall1_wp hΓ hrun hrt hnrt hbaId (hbaW.toRtArgBV64 hwba)
            hiId (hiW.toRtArgBV64 hwi) hinv hm hwp fun r ek ρ' nr res σ' m' hnr hek hr hagr
            hrEv hinv' hm' hK =>
            hk r ek ρ' J nr n' 8 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J) hrEv
              hinv' hm' hK
    · simp [EvalWordArgs] at hargsEv
  · -- "get"
    rcases args with _ | ⟨baArg, _ | ⟨idxArg, _ | ⟨a2, _ | _⟩⟩⟩ <;> simp at har
    rcases ws with _ | ⟨wba, _ | ⟨wi, _ | ⟨w2, _ | _⟩⟩⟩
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · simp [EvalWordArgs] at hargsEv
    · have hbaId := hargsIds baArg List.mem_cons_self
      have hiId := hargsIds idxArg (List.mem_cons_of_mem _ List.mem_cons_self)
      have hbaW := hargsEv.2 (baArg, wba) List.mem_cons_self
      have hiW := hargsEv.2 (idxArg, wi) (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [HByteArrayPrimWp] at hwp
      cases hwba : wba.toBV64? with
      | none => simp [hwba] at hwp
      | some ba => cases hwi : wi.toBV64? with
        | none => simp [hwba, hwi] at hwp
        | some idx =>
          simp only [hwba, hwi] at hwp
          unfold byteArrayPrim at hrun
          exact baGet_rtCall1_wp hΓ hrun hrt hnrt hbaId (hbaW.toRtArgBV64 hwba)
            hiId (hiW.toRtArgBV64 hwi) hinv hm hwp fun r ek ρ' nr res σ' m' hnr hek hr hagr
            hrEv hinv' hm' hK =>
            hk r ek ρ' J nr n' 8 res σ' m' hnr hek hr hagr (JEnvAgreeBelow.refl n J) hrEv
              hinv' hm' hK
    · simp [EvalWordArgs] at hargsEv

end LeanQbe.T.LeanLCNF.Sem
