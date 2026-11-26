module

public import LeanQbe.T.ZeroPeel
public import LeanQbe.T.ZeroPeelLemmas1
public import LeanQbe.T.ZeroPeelLemmas2
public import LeanQbe.T.Wf
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.GroupLfpLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.PassFlatKit
import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.OpsLemmas
import all Kraken.Mem

/-!
# Helper Lemmas for `LeanQbe.T.ZeroPeel` (Part 3: Wide Multi-Store WP & `CallsOk`)

Proves `matchMultiFillBody_spec`, disjoint-memory store commutation, `runMultiScalarMem_step`,
`emitWideStreams_wp`, `mkDisjointCheck_wp`, `widenFillExt_wp`, and `widenFillExt_callsOk`.
-/

set_option autoImplicit false

namespace LeanQbe.T

open Std Std.ExtHashMap

namespace ZeroPeel

/-! ## Section 1: Concrete Scalar Stream Specs & `matchMultiFillBody_spec` -/

public structure ScalarStream where
  tAtom : Ty
  fillAtom : Val tAtom
  baseA : Arg Val i64
  oVal : BitVec 64
  sh : Nat
  fill64 : BitVec 64
  hShLe : sh ≤ 3
  hBytesEq : tAtom.bytes = 2 ^ sh
  hK64Mul : (8 >>> sh) * tAtom.bytes = 8
  hWideBytes : (List.replicate (8 >>> sh) (Int.toBytes tAtom.bytes
    ((toBits tAtom fillAtom).setWidth (8 * tAtom.bytes)).toInt)).flatten =
      Int.toBytes 8 fill64.toInt

@[expose] public def ScalarStream.ptr (s : ScalarStream) (i64Val : BitVec 64) : BitVec 64 :=
  s.baseA.val + ((i64Val + s.oVal) <<< s.sh)

private def ScalarStream.atomBytes (s : ScalarStream) : List UInt8 :=
  Int.toBytes s.tAtom.bytes ((toBits s.tAtom s.fillAtom).setWidth (8 * s.tAtom.bytes)).toInt

private theorem ScalarStream.atomBytes_length (s : ScalarStream) :
    s.atomBytes.length = s.tAtom.bytes := toBytes_length ..
private theorem ScalarStream.bytes_pos (s : ScalarStream) : 0 < s.tAtom.bytes := by
  rw [s.hBytesEq]; exact Nat.pow_pos (by omega)
@[expose] public def StreamMatchesSpec (vsOuter : List ((t : Ty) × Val t))
    (s : ScalarStream) (sp : StoreSpec) : Prop :=
  denoteArg vsOuter sp.base = some s.baseA ∧
  offVal vsOuter sp.off? = some s.oVal ∧
  s.sh = sp.shift ∧ s.fill64 = sp.fill64
public inductive PairForall {α β : Type} (R : α → β → Prop) :
    List α → List β → Prop
  | nil : PairForall R [] []
  | cons {a b xs ys} : R a b → PairForall R xs ys → PairForall R (a :: xs) (b :: ys)
@[expose] public def applyScalarChain (m : Mem 64) (i64Val : BitVec 64) :
    List ScalarStream → Mem 64
  | [] => m
  | s :: rest => applyScalarChain (storeMem m s.tAtom (s.ptr i64Val) s.fillAtom) i64Val rest
@[expose] public def ScalarChainOk (m : Mem 64) (i64Val : BitVec 64) : List ScalarStream → Prop
  | [] => True
  | s :: rest =>
    storeOk m s.tAtom (s.ptr i64Val) ∧
    ScalarChainOk (storeMem m s.tAtom (s.ptr i64Val) s.fillAtom) i64Val rest

private theorem storeBytes_preserves_dom (m : Mem 64) (a : BitVec 64) (bs : List UInt8)
    (hmem : ∀ j < bs.length, (m.get? (a + BitVec.ofNat 64 j)).isSome = true) (q : BitVec 64) :
    ((m.storeBytes a bs).get? q).isSome = (m.get? q).isSome := by
  simp only [Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.union_eq,
    Std.ExtHashMap.getElem?_union]
  by_cases hkb : q ∈ bs.At a
  · obtain ⟨j, hj, rfl⟩ := (mem_At_iff bs a q).1 hkb
    have hm := hmem j hj
    rw [Std.ExtHashMap.get?_eq_getElem?] at hm
    cases hk1 : m[a + BitVec.ofNat 64 j]? with
    | none => simp [hk1] at hm
    | some _ => simp
  · rw [Std.ExtHashMap.getElem?_eq_none hkb, Option.none_or]

private theorem storeMem_preserves_dom (m : Mem 64) (t : Ty) (a : BitVec 64) (v : Val t)
    (hOk : storeOk m t a) (q : BitVec 64) :
    ((storeMem m t a v).get? q).isSome = (m.get? q).isSome := by
  rw [storeOk_iff_forall_mem] at hOk
  rw [storeMem_eq_storeBytes]
  exact storeBytes_preserves_dom m a _ (by simpa [Int.toBytes_length] using hOk) q

private theorem scalarChainOk_preserves_dom (i64Val : BitVec 64) :
    (ss : List ScalarStream) → (m : Mem 64) → ScalarChainOk m i64Val ss →
    (∀ q, ((applyScalarChain m i64Val ss).get? q).isSome = (m.get? q).isSome) ∧
    (∀ s ∈ ss, storeOk m s.tAtom (s.ptr i64Val))
  | [], _, _ => ⟨fun _ => rfl, fun _ h => nomatch h⟩
  | s :: rest, m, ⟨hOk, hRest⟩ => by
    let m1 := storeMem m s.tAtom (s.ptr i64Val) s.fillAtom
    have hDom1 : ∀ q, (m1.get? q).isSome = (m.get? q).isSome :=
      storeMem_preserves_dom m s.tAtom (s.ptr i64Val) s.fillAtom hOk
    obtain ⟨hDomR, hOkR⟩ := scalarChainOk_preserves_dom i64Val rest m1 hRest
    refine ⟨fun q => (hDomR q).trans (hDom1 q), fun x hx => ?_⟩
    cases hx with
    | head => exact hOk
    | tail _ ht =>
      exact (storeOk_storeMem_iff m s.tAtom (s.ptr i64Val) s.fillAtom hOk x.tAtom
        (x.ptr i64Val)).1 (hOkR x ht)

private theorem denoteArgs_singleton_some {V : Ty → Type} {vs : List ((t : Ty) × V t)}
    {t : Ty} {a : Arg K t} {va : Arg V t}
    (h : denoteArgs vs (ts := [t]) (a, ()) = some (va, ())) : denoteArg vs a = some va := by
  rw [denoteArgs_singleton_eq] at h; cases hd : denoteArg vs a <;> simp_all

private theorem denoteArgs_pair_some {V : Ty → Type} {vs : List ((t : Ty) × V t)}
    {t1 t2 : Ty} {a : Arg K t1} {b : Arg K t2} {va : Arg V t1} {vb : Arg V t2}
    (h : denoteArgs vs (ts := [t1, t2]) (a, b, ()) = some (va, vb, ())) :
    denoteArg vs a = some va ∧ denoteArg vs b = some vb := by
  rw [denoteArgs_pair_eq] at h
  cases hda : denoteArg vs a <;> cases hdb : denoteArg vs b <;> simp_all

private theorem offVal_exists_of_wf {GOuter : List Ty} {vsOuter : List ((t : Ty) × Val t)}
    (hCtx : CtxTypes GOuter vsOuter) {off? : Option (Arg K i64)}
    (hwf : off?.all (checkArg GOuter i64) = true) :
    ∃ oVal : BitVec 64, offVal vsOuter off? = some oVal := by
  cases off? with
  | none => exact ⟨0#64, rfl⟩
  | some off =>
    rw [Option.all_some] at hwf
    obtain ⟨offA, hdo⟩ := Option.isSome_iff_exists.mp (denoteArg_isSome_of_checkArg hCtx hwf)
    exact ⟨offA.val, by dsimp only [offVal]; rw [hdo]; rfl⟩

private theorem matchMultiBodyTail_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {GOuter : List Ty} {D : List (List Ty)} {vsOuter : List ((t : Ty) × Val t)}
    {ls : List ((ts : List Ty) × Cont ts)} (hCtxV : CtxTypes GOuter vsOuter)
    {is32 : Bool} {JLoop : Cont [if is32 then i32 else i64]} :
    (cont : TFlat rs) → {GLocal : List Ty} → {env : Array SymExt} → {acc stores : List StoreSpec} →
    SymExtEnvWf GOuter GLocal env →
    cont.wfCheck (GLocal ++ (if is32 then i32 else i64) :: GOuter) D = true →
    matchMultiBodyTail is32 env acc cont = some stores →
    ∃ (tail : List StoreSpec) (streams : List ScalarStream),
      stores = acc.reverse ++ tail ∧
      PairForall (StreamMatchesSpec vsOuter) streams tail ∧
      ∀ (vsLocal : List ((t : Ty) × Val t))
        (iVal : Val (if is32 then i32 else i64)) (m : Mem 64),
        SymExtEnvMatch vsOuter is32 iVal vsLocal env →
        wp Γ Q X (denote Val Cont cont
          (vsLocal ++ ⟨if is32 then i32 else i64, iVal⟩ :: vsOuter)
          (⟨[if is32 then i32 else i64], JLoop⟩ :: ls)) m →
        ScalarChainOk m (loopVal64 is32 iVal) streams ∧
        JLoop (incLoopVal is32 iVal, ())
          (applyScalarChain m (loopVal64 is32 iVal) streams)
  | .let_ op k, GLocal, env, acc, stores, hwf, htf, hm => by
    rw [wfCheck_let_eq, Bool.and_eq_true] at htf
    dsimp only [matchMultiBodyTail] at hm
    by_cases hPure : isTotalPureOp op.code = true
    · rw [ite_eq_left hPure] at hm
      have hk := htf.2; rw [pushTypes_append] at hk
      obtain ⟨tail, streams, hEq, hF2, hBody⟩ :=
        matchMultiBodyTail_spec hCtxV k (evalSymOpExt_wf hwf op htf.1) hk hm
      refine ⟨tail, streams, hEq, hF2, fun vsLocal iVal m hEnv hwp => ?_⟩
      rw [denote_let_eq] at hwp
      cases hda : denoteArgs (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) op.args with
      | none => rw [hda] at hwp; exact False.elim (wp_hlt_false hwp)
      | some valArgs =>
        rw [hda] at hwp; dsimp only [Op.wp] at hwp; rw [wp_let] at hwp
        obtain ⟨res, hP, hm'⟩ := evalSymOpExt_wp hEnv op hda hwp
        rw [pushTup_append_assoc] at hP
        exact hBody (pushTup res vsLocal) iVal m hm' hP
    · rw [ite_eq_right hPure] at hm; cases hm
  | .store (t := t_atom) valArg addrArg cont, GLocal, env, acc, stores, hwf, htf, hm => by
    rw [wfCheck_store_eq, Bool.and_eq_true, Bool.and_eq_true] at htf
    dsimp only [matchMultiBodyTail] at hm
    by_cases hlen : acc.length ≥ 8
    · rw [ite_eq_left (by simp [hlen])] at hm; cases hm
    · rw [ite_eq_right (by simp [hlen])] at hm
      cases valArg with
      | var _ => cases hm
      | imm fillAtom =>
        dsimp only at hm
        cases hSp : splatVal64 fillAtom with
        | none => rw [hSp] at hm; cases hm
        | some sf =>
          rcases sf with ⟨sh, f64⟩; rw [hSp] at hm; dsimp only at hm
          cases hAddr : matchAddrExt is32 sh (argToSym is32 env addrArg) with
          | none => rw [hAddr] at hm; cases hm
          | some bo =>
            rcases bo with ⟨base, off?⟩; rw [hAddr] at hm; dsimp only at hm
            let st : StoreSpec := { base, off?, shift := sh, fill64 := f64 }
            have hSplatSpec := splatVal64_spec fillAtom hSp
            have hAddrWf := matchAddrExt_wf (argToSym_wf hwf htf.1.2) hAddr
            obtain ⟨baseA, hdBase⟩ :=
              Option.isSome_iff_exists.mp (denoteArg_isSome_of_checkArg hCtxV hAddrWf.1)
            obtain ⟨oVal, hdOff⟩ := offVal_exists_of_wf hCtxV hAddrWf.2
            let sc : ScalarStream := {
              tAtom := t_atom, fillAtom := fillAtom, baseA := baseA, oVal := oVal,
              sh := sh, fill64 := f64, hShLe := hSplatSpec.1, hBytesEq := hSplatSpec.2.1,
              hK64Mul := hSplatSpec.2.2.1, hWideBytes := hSplatSpec.2.2.2.symm
            }
            have hMatch : StreamMatchesSpec vsOuter sc st := ⟨hdBase, hdOff, rfl, rfl⟩
            have stepOne : ∀ (vsLocal : List ((t : Ty) × Val t))
                (iVal : Val (if is32 then i32 else i64)) (m : Mem 64),
                SymExtEnvMatch vsOuter is32 iVal vsLocal env →
                wp Γ Q X (denote Val Cont (.store (.imm fillAtom) addrArg cont)
                  (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) (⟨_, JLoop⟩ :: ls)) m →
                storeOk m t_atom (sc.ptr (loopVal64 is32 iVal)) ∧
                wp Γ Q X (denote Val Cont cont
                  (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) (⟨_, JLoop⟩ :: ls))
                  (storeMem m t_atom (sc.ptr (loopVal64 is32 iVal)) fillAtom) := by
              intro vsLocal iVal m hEnv hwp
              rw [denote_store_eq] at hwp
              have hdv : denoteArg (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) (.imm fillAtom) =
                  some (.imm fillAtom) := rfl
              cases hda : denoteArg (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) addrArg with
              | none => exact absurd (by rw [hdv, hda] at hwp; exact hwp) wp_hlt_false
              | some addrA =>
                rw [hdv, hda] at hwp; dsimp only at hwp; rw [wp_store] at hwp
                obtain ⟨baseA', oVal', hdB', hdO', hEqAddr⟩ :=
                  matchAddrExt_correct (argToSym_correct hEnv addrArg hda) hAddr
                rw [hdBase] at hdB'; rw [hdOff] at hdO'; cases hdB'; cases hdO'
                have hAddrEq : addrA.val = sc.ptr (loopVal64 is32 iVal) := hEqAddr
                exact ⟨hAddrEq ▸ hwp.1, hAddrEq ▸ hwp.2⟩
            by_cases hChk : checkJump0Inc1Ext is32 env cont = true
            · rw [ite_eq_left hChk] at hm; cases hm
              refine ⟨[st], [sc], by simp [st], .cons hMatch .nil, ?_⟩
              intro vsLocal iVal m hEnv hwp
              obtain ⟨hOk1, hNext⟩ := stepOne vsLocal iVal m hEnv hwp
              exact ⟨⟨hOk1, trivial⟩, checkJump0Inc1Ext_wp cont hChk hEnv hNext⟩
            · rw [ite_eq_right hChk] at hm
              obtain ⟨tail, streams, hEq, hF2, hCont⟩ :=
                matchMultiBodyTail_spec hCtxV cont hwf htf.2 hm
              refine ⟨st :: tail, sc :: streams, by simpa [st] using hEq, .cons hMatch hF2, ?_⟩
              intro vsLocal iVal m hEnv hwp
              obtain ⟨hOk1, hNext⟩ := stepOne vsLocal iVal m hEnv hwp
              obtain ⟨hOkRest, hJ⟩ := hCont vsLocal iVal _ hEnv hNext
              exact ⟨⟨hOk1, hOkRest⟩, hJ⟩
  | .load _ _ _, _, _, _, _, _, _, hm | .call _ _ _ _, _, _, _, _, _, _, hm
  | .jnz _ _ _, _, _, _, _, _, _, hm | .jump _ _, _, _, _, _, _, _, hm
  | .ret _, _, _, _, _, _, _, hm | .exit _ _, _, _, _, _, _, _, hm
  | .hlt, _, _, _, _, _, _, hm | .group _ _, _, _, _, _, _, _, hm => by
    dsimp only [matchMultiBodyTail] at hm; cases hm

@[expose] public def cmpBoundOk : (is32 : Bool) → Bool →
    Val (if is32 then i32 else i64) → Val (if is32 then i32 else i64) → Prop
  | true => fun isLt (iVal bndVal : BitVec 32) =>
    (if isLt then decide (iVal < bndVal) else decide (iVal ≤ bndVal)) = true
  | false => fun isLt (iVal bndVal : BitVec 64) =>
    (if isLt then decide (iVal < bndVal) else decide (iVal ≤ bndVal)) = true

public theorem matchMultiFillBody_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {GOuter : List Ty} {D : List (List Ty)} {vsOuter : List ((t : Ty) × Val t)}
    {ls : List ((ts : List Ty) × Cont ts)} (hCtxV : CtxTypes GOuter vsOuter)
    {is32 : Bool} {JLoop : Cont [if is32 then i32 else i64]} :
    (body : TFlat rs) → {GLocal : List Ty} → {env : Array SymExt} →
    {fb : FillBound} → {stores : List StoreSpec} →
    SymExtEnvWf GOuter GLocal env →
    body.wfCheck (GLocal ++ (if is32 then i32 else i64) :: GOuter) D = true →
    matchMultiFillBody is32 env body = some (fb, stores) →
    ∃ (isLt : Bool) (bnd : Arg K (if is32 then i32 else i64)) (streams : List ScalarStream),
      fb = (match is32 with | true => .b32 isLt bnd | false => .b64 isLt bnd) ∧
      PairForall (StreamMatchesSpec vsOuter) streams stores ∧
      ∀ (vsLocal : List ((t : Ty) × Val t))
        (iVal : Val (if is32 then i32 else i64)) (m : Mem 64)
        (bndA : Arg Val (if is32 then i32 else i64)),
        SymExtEnvMatch vsOuter is32 iVal vsLocal env →
        denoteArg vsOuter bnd = some bndA →
        cmpBoundOk is32 isLt iVal bndA.val →
        wp Γ Q X (denote Val Cont body
          (vsLocal ++ ⟨if is32 then i32 else i64, iVal⟩ :: vsOuter)
          (⟨[if is32 then i32 else i64], JLoop⟩ :: ls)) m →
        ScalarChainOk m (loopVal64 is32 iVal) streams ∧
        JLoop (incLoopVal is32 iVal, ())
          (applyScalarChain m (loopVal64 is32 iVal) streams)
  | .let_ op k, GLocal, env, fb, stores, hwf, htf, hm => by
    rw [wfCheck_let_eq, Bool.and_eq_true] at htf
    dsimp only [matchMultiFillBody] at hm
    by_cases hPure : isTotalPureOp op.code = true
    · rw [ite_eq_left hPure] at hm
      have hk := htf.2; rw [pushTypes_append] at hk
      obtain ⟨isLt, bnd, streams, hFb, hF2, hBody⟩ :=
        matchMultiFillBody_spec hCtxV k (evalSymOpExt_wf hwf op htf.1) hk hm
      refine ⟨isLt, bnd, streams, hFb, hF2, fun vsLocal iVal m bndA hEnv hBnd hCmp hwp => ?_⟩
      rw [denote_let_eq] at hwp
      cases hda : denoteArgs (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) op.args with
      | none => rw [hda] at hwp; exact False.elim (wp_hlt_false hwp)
      | some valArgs =>
        rw [hda] at hwp; dsimp only [Op.wp] at hwp; rw [wp_let] at hwp
        obtain ⟨res, hP, hm'⟩ := evalSymOpExt_wp hEnv op hda hwp
        rw [pushTup_append_assoc] at hP
        exact hBody (pushTup res vsLocal) iVal m bndA hm' hBnd hCmp hP
    · rw [ite_eq_right hPure] at hm; cases hm
  | .jnz c t _, GLocal, env, fb, stores, hwf, htf, hm => by
    rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true] at htf
    dsimp only [matchMultiFillBody] at hm
    cases hc : argToSym is32 env c with
    | cmpU32 isLt bnd =>
      rw [hc] at hm; dsimp only at hm
      cases is32 with
      | false => cases hm
      | true =>
        rcases Option.map_eq_some_iff.mp hm with ⟨stores', hmTail, hPair⟩
        injection hPair with hFb hStEq; subst hStEq
        obtain ⟨tail, streams, hEq, hF2, hTail⟩ :=
          matchMultiBodyTail_spec (Γ := Γ) (Q := Q) (X := X) hCtxV t hwf htf.1.2 hmTail
        rw [List.reverse_nil, List.nil_append] at hEq; subst hEq
        refine ⟨isLt, bnd, streams, hFb.symm, hF2, fun vsLocal iVal m bndA hEnv hBnd hCmp hwp => ?_⟩
        rw [denote_jnz_eq] at hwp
        cases hdc : denoteArg (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) c with
        | none => rw [hdc] at hwp; exact False.elim (wp_hlt_false hwp)
        | some cA =>
          rw [hdc] at hwp; dsimp only at hwp; rw [wp_jnz] at hwp
          have hRel := argToSym_correct hEnv c hdc; rw [hc] at hRel
          rcases hRel with ⟨_, bndA', hBnd', hCEq⟩
          rw [hBnd] at hBnd'; cases hBnd'
          exact hTail vsLocal iVal m hEnv
            (hwp.1 (by dsimp only [cmpBoundOk] at hCmp; rw [sigma_val_eq hCEq]; exact hCmp))
    | cmpU64 isLt bnd =>
      rw [hc] at hm; dsimp only at hm
      cases is32 with
      | true => cases hm
      | false =>
        rcases Option.map_eq_some_iff.mp hm with ⟨stores', hmTail, hPair⟩
        injection hPair with hFb hStEq; subst hStEq
        obtain ⟨tail, streams, hEq, hF2, hTail⟩ :=
          matchMultiBodyTail_spec (Γ := Γ) (Q := Q) (X := X) hCtxV t hwf htf.1.2 hmTail
        rw [List.reverse_nil, List.nil_append] at hEq; subst hEq
        refine ⟨isLt, bnd, streams, hFb.symm, hF2, fun vsLocal iVal m bndA hEnv hBnd hCmp hwp => ?_⟩
        rw [denote_jnz_eq] at hwp
        cases hdc : denoteArg (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) c with
        | none => rw [hdc] at hwp; exact False.elim (wp_hlt_false hwp)
        | some cA =>
          rw [hdc] at hwp; dsimp only at hwp; rw [wp_jnz] at hwp
          have hRel := argToSym_correct hEnv c hdc; rw [hc] at hRel
          rcases hRel with ⟨_, bndA', hBnd', hCEq⟩
          rw [hBnd] at hBnd'; cases hBnd'
          exact hTail vsLocal iVal m hEnv
            (hwp.1 (by dsimp only [cmpBoundOk] at hCmp; rw [sigma_val_eq hCEq]; exact hCmp))
    | loopI | loopZext64 | outer64 _ | outer32 _ | const64 _ | const32 _
    | add64 _ _ | add32 _ _ | shlConst64 _ _ | other => rw [hc] at hm; cases hm
  | .load _ _ _, _, _, _, _, _, _, hm | .store _ _ _, _, _, _, _, _, _, hm
  | .call _ _ _ _, _, _, _, _, _, _, hm | .jump _ _, _, _, _, _, _, _, hm
  | .ret _, _, _, _, _, _, _, hm | .exit _ _, _, _, _, _, _, _, hm
  | .hlt, _, _, _, _, _, _, hm | .group _ _, _, _, _, _, _, _, hm => by
    dsimp only [matchMultiFillBody] at hm; cases hm

/-! ## Section 2: Disjoint Memory Algebra & Multi-Stream Scalar-to-Wide Step -/

private def ByteDisj (a : BitVec 64) (lenA : Nat) (b : BitVec 64) (lenB : Nat) : Prop :=
  lenA ≤ 2 ^ 64 ∧ lenB ≤ 2 ^ 64 ∧
  ∀ j1 < lenA, ∀ j2 < lenB, a + BitVec.ofNat 64 j1 ≠ b + BitVec.ofNat 64 j2

private theorem byteDisj_symm {a : BitVec 64} {lenA : Nat} {b : BitVec 64} {lenB : Nat}
    (h : ByteDisj a lenA b lenB) : ByteDisj b lenB a lenA :=
  ⟨h.2.1, h.1, fun j2 hj2 j1 hj1 heq => h.2.2 j1 hj1 j2 hj2 heq.symm⟩

private theorem byteDisj_sub {a : BitVec 64} {lenA : Nat} {b : BitVec 64} {lenB : Nat}
    (h : ByteDisj a lenA b lenB) {offA subA offB subB : Nat}
    (hA : offA + subA ≤ lenA) (hB : offB + subB ≤ lenB) :
    ByteDisj (a + BitVec.ofNat 64 offA) subA (b + BitVec.ofNat 64 offB) subB := by
  have h1 := h.1; have h2 := h.2.1
  refine ⟨by omega, by omega, fun j1 hj1 j2 hj2 heq => ?_⟩
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add] at heq
  exact h.2.2 (offA + j1) (by omega) (offB + j2) (by omega) heq

private theorem byteDisj_of_intervals {loA : BitVec 64} {totA : Nat}
    {loB : BitVec 64} {totB : Nat}
    (hNoA : loA.toNat + totA < 2 ^ 64) (hNoB : loB.toNat + totB < 2 ^ 64)
    (hSep : loA.toNat + totA ≤ loB.toNat ∨ loB.toNat + totB ≤ loA.toNat) :
    ByteDisj loA totA loB totB := by
  refine ⟨by omega, by omega, fun j1 hj1 j2 hj2 heq => ?_⟩
  have h1 : (loA + BitVec.ofNat 64 j1).toNat = loA.toNat + j1 := by
    have hlt1 : j1 < 2 ^ 64 := by omega
    have hlt2 : loA.toNat + j1 < 2 ^ 64 := by omega
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2]
  have h2 : (loB + BitVec.ofNat 64 j2).toNat = loB.toNat + j2 := by
    have hlt1 : j2 < 2 ^ 64 := by omega
    have hlt2 : loB.toNat + j2 < 2 ^ 64 := by omega
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2]
  have hNat := congrArg BitVec.toNat heq
  rw [h1, h2] at hNat
  omega

private theorem storeBytes_comm_disjoint (m : Mem 64) (a : BitVec 64) (bs1 : List UInt8)
    (b : BitVec 64) (bs2 : List UInt8) (hDisj : ByteDisj a bs1.length b bs2.length) :
    (m.storeBytes a bs1).storeBytes b bs2 = (m.storeBytes b bs2).storeBytes a bs1 := by
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Mem.storeBytes, Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  by_cases hk1 : k ∈ bs1.At a
  · obtain ⟨j1, hj1, rfl⟩ := (mem_At_iff bs1 a k).1 hk1
    have hk2 : a + BitVec.ofNat 64 j1 ∉ bs2.At b := by
      intro hm
      obtain ⟨j2, hj2, heq⟩ := (mem_At_iff bs2 b _).1 hm
      exact hDisj.2.2 j1 hj1 j2 hj2 heq
    rw [Std.ExtHashMap.getElem?_eq_none hk2]
    cases (bs1.At a)[a + BitVec.ofNat 64 j1]? <;> cases m[a + BitVec.ofNat 64 j1]? <;> rfl
  · rw [Std.ExtHashMap.getElem?_eq_none hk1]
    cases (bs2.At b)[k]? <;> cases m[k]? <;> rfl

private theorem list_replicate_add {α : Type} (n m : Nat) (x : α) :
    List.replicate (n + m) x = List.replicate n x ++ List.replicate m x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, ih, List.cons_append]

private def applyWideStreamsMem (m : Mem 64) (i64Init : BitVec 64) (k : Nat) :
    List ScalarStream → Mem 64
  | [] => m
  | s :: rest =>
    let m1 := m.storeBytes (s.ptr i64Init) (List.replicate k s.atomBytes).flatten
    applyWideStreamsMem m1 i64Init k rest

private theorem applyWideStreamsMem_zero (m : Mem 64) (i64Init : BitVec 64) :
    (ss : List ScalarStream) → applyWideStreamsMem m i64Init 0 ss = m
  | [] => rfl
  | s :: rest => by
    dsimp only [applyWideStreamsMem, List.replicate, List.flatten]
    rw [storeBytes_nil]
    exact applyWideStreamsMem_zero m i64Init rest

private theorem applyWideStreamsMem_preserves_dom (i64Init : BitVec 64) (k : Nat) :
    (ss : List ScalarStream) → (m : Mem 64) →
    (∀ s ∈ ss, ∀ j < k * s.tAtom.bytes,
      (m.get? (s.ptr i64Init + BitVec.ofNat 64 j)).isSome = true) →
    ∀ q, ((applyWideStreamsMem m i64Init k ss).get? q).isSome = (m.get? q).isSome
  | [], _, _, _ => rfl
  | s :: rest, m, hMem, q => by
    dsimp only [applyWideStreamsMem]
    have hBsLen : (List.replicate k s.atomBytes).flatten.length = k * s.tAtom.bytes := by
      rw [length_flatten_replicate, s.atomBytes_length]
    have hS : ∀ j < (List.replicate k s.atomBytes).flatten.length,
        (m.get? (s.ptr i64Init + BitVec.ofNat 64 j)).isSome = true := by
      intro j hj; rw [hBsLen] at hj; exact hMem s (List.Mem.head _) j hj
    have hDom1 : ∀ p, ((m.storeBytes (s.ptr i64Init)
        (List.replicate k s.atomBytes).flatten).get? p).isSome = (m.get? p).isSome :=
      storeBytes_preserves_dom m (s.ptr i64Init) _ hS
    have hRest : ∀ r ∈ rest, ∀ j < k * r.tAtom.bytes,
        ((m.storeBytes (s.ptr i64Init) (List.replicate k s.atomBytes).flatten).get?
          (r.ptr i64Init + BitVec.ofNat 64 j)).isSome = true := by
      intro r hr j hj; rw [hDom1]; exact hMem r (List.Mem.tail _ hr) j hj
    exact (applyWideStreamsMem_preserves_dom i64Init k rest _ hRest q).trans (hDom1 q)

@[expose] public def bv64OfW {w : Nat} (x : BitVec w) : BitVec 64 := x.setWidth 64

public theorem bv64OfW_32 (x : BitVec 32) : bv64OfW x = loopVal64 true x := rfl

public theorem bv64OfW_64 (x : BitVec 64) : bv64OfW x = loopVal64 false x := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [bv64OfW, loopVal64]
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt x.isLt]

private theorem bv64OfW_64_eq (x : BitVec 64) : bv64OfW x = x := by
  apply BitVec.eq_of_toNat_eq
  dsimp only [bv64OfW]; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt x.isLt]

private theorem storeBytes_comm_wideStreams (i64Init : BitVec 64) (k : Nat)
    (a : BitVec 64) (bs : List UInt8) (m : Mem 64) :
    (rest : List ScalarStream) →
    (∀ s ∈ rest, ByteDisj a bs.length (s.ptr i64Init) (k * s.tAtom.bytes)) →
    (applyWideStreamsMem m i64Init k rest).storeBytes a bs =
      applyWideStreamsMem (m.storeBytes a bs) i64Init k rest
  | [], _ => rfl
  | s :: rest, hDisj => by
    dsimp only [applyWideStreamsMem]
    have hS := hDisj s (List.Mem.head _)
    have hBsLen : (List.replicate k s.atomBytes).flatten.length = k * s.tAtom.bytes := by
      rw [length_flatten_replicate, s.atomBytes_length]
    rw [storeBytes_comm_wideStreams i64Init k a bs _ rest
      (fun x hx => hDisj x (List.Mem.tail _ hx))]
    rw [storeBytes_comm_disjoint m _ _ a bs (byteDisj_symm (by rw [← hBsLen] at hS; exact hS))]

private theorem scalarStream_ptr_add (s : ScalarStream) (i64Init : BitVec 64) (k : Nat) :
    s.ptr (i64Init + BitVec.ofNat 64 k) = s.ptr i64Init + BitVec.ofNat 64 (k * s.tAtom.bytes) := by
  dsimp only [ScalarStream.ptr]
  have h1 : (i64Init + BitVec.ofNat 64 k) + s.oVal = (i64Init + s.oVal) + BitVec.ofNat 64 k := by
    rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 k) s.oVal, ← BitVec.add_assoc]
  rw [h1, bv64_shl_add, bv64_ofNat_shl, ← s.hBytesEq, BitVec.add_assoc]

private theorem flatten_replicate_succ_eq {α : Type} (k : Nat) (xs : List α) :
    (List.replicate (k + 1) xs).flatten = (List.replicate k xs).flatten ++ xs := by
  rw [list_replicate_add k 1 xs, List.flatten_append, List.replicate_one, List.flatten_cons,
    List.flatten_nil, List.append_nil]

private theorem applyScalarChain_after_wideStreams (i64Init : BitVec 64) (k : Nat) (m : Mem 64) :
    (ss : List ScalarStream) →
    ss.Pairwise (fun a b => ByteDisj (a.ptr i64Init) ((k + 1) * a.tAtom.bytes)
      (b.ptr i64Init) ((k + 1) * b.tAtom.bytes)) →
    (∀ s ∈ ss, (k + 1) * s.tAtom.bytes ≤ 2 ^ 64) →
    applyScalarChain (applyWideStreamsMem m i64Init k ss) (i64Init + BitVec.ofNat 64 k) ss =
      applyWideStreamsMem m i64Init (k + 1) ss
  | [], _, _ => rfl
  | s :: rest, hPair, hBnd => by
    rw [List.pairwise_cons] at hPair
    dsimp only [applyScalarChain, applyWideStreamsMem]
    have hBsK : (List.replicate k s.atomBytes).flatten.length = k * s.tAtom.bytes := by
      rw [length_flatten_replicate, s.atomBytes_length]
    have hPtr := scalarStream_ptr_add s i64Init k
    rw [storeMem_eq_storeBytes]
    have hBndS := hBnd s (List.Mem.head _)
    have hSubA : k * s.tAtom.bytes + s.tAtom.bytes ≤ (k + 1) * s.tAtom.bytes := by
      rw [Nat.add_mul, Nat.one_mul]; exact Nat.le_refl _
    have hDisjRest : ∀ r ∈ rest, ByteDisj (s.ptr (i64Init + BitVec.ofNat 64 k))
        s.atomBytes.length (r.ptr i64Init) (k * r.tAtom.bytes) := by
      intro r hr
      rw [hPtr, s.atomBytes_length]
      have hSubB : 0 + k * r.tAtom.bytes ≤ (k + 1) * r.tAtom.bytes := by
        rw [Nat.zero_add]; exact Nat.mul_le_mul_right r.tAtom.bytes (Nat.le_succ k)
      have hD := byteDisj_sub (offA := k * s.tAtom.bytes) (subA := s.tAtom.bytes)
        (offB := 0) (subB := k * r.tAtom.bytes) (hPair.1 r hr) hSubA hSubB
      simpa [BitVec.add_zero] using hD
    change applyScalarChain ((applyWideStreamsMem
        (m.storeBytes (s.ptr i64Init) (List.replicate k s.atomBytes).flatten)
        i64Init k rest).storeBytes
        (s.ptr (i64Init + BitVec.ofNat 64 k)) s.atomBytes) (i64Init + BitVec.ofNat 64 k) rest = _
    rw [storeBytes_comm_wideStreams i64Init k _ _ _ rest hDisjRest]
    rw [hPtr, show k * s.tAtom.bytes = (List.replicate k s.atomBytes).flatten.length from hBsK.symm]
    rw [storeBytes_append _ _ _ _ (by rw [hBsK, s.atomBytes_length]; omega)]
    rw [← flatten_replicate_succ_eq k s.atomBytes]
    exact applyScalarChain_after_wideStreams i64Init k _ rest hPair.2
      (fun r hr => hBnd r (List.Mem.tail _ hr))

private theorem bvW_setWidth64_add {w : Nat} (hw : w = 32 ∨ w = 64)
    (iVal bndVal : BitVec w) (k : Nat) (hk : iVal.toNat + k ≤ bndVal.toNat) :
    bv64OfW (iVal + BitVec.ofNat w k) = bv64OfW iVal + BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  have hltW : iVal.toNat + k < 2 ^ w := Nat.lt_of_le_of_lt hk bndVal.isLt
  have hlt64 : iVal.toNat + k < 2 ^ 64 := by rcases hw with rfl | rfl <;> omega
  have hkW : k < 2 ^ w := by omega
  have hk64 : k < 2 ^ 64 := by omega
  have hIV64 : iVal.toNat < 2 ^ 64 := by rcases hw with rfl | rfl <;> omega
  dsimp only [bv64OfW]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hkW, Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt hltW,
    Nat.mod_eq_of_lt hlt64, Nat.mod_eq_of_lt hIV64]

private theorem runMultiScalarMem_step {w : Nat} (hw : w = 32 ∨ w = 64)
    {JLoop : Cont [.bits w]} {ss : List ScalarStream} {bndVal : BitVec w}
    (hStep : ∀ (i' : BitVec w) (m' : Mem 64),
      i'.toNat < bndVal.toNat → JLoop (i', ()) m' →
      ScalarChainOk m' (bv64OfW i') ss ∧
      JLoop (i' + BitVec.ofNat w 1, ()) (applyScalarChain m' (bv64OfW i') ss))
    (iVal : BitVec w) (m : Mem 64) (hJ : JLoop (iVal, ()) m) :
    (k : Nat) → k ≤ bndVal.toNat - iVal.toNat →
    (∀ s ∈ ss, k * s.tAtom.bytes ≤ 2 ^ 64) →
    ss.Pairwise (fun a b => ByteDisj (a.ptr (bv64OfW iVal)) (k * a.tAtom.bytes)
      (b.ptr (bv64OfW iVal)) (k * b.tAtom.bytes)) →
    (∀ s ∈ ss, ∀ j < k, storeOk m s.tAtom
      (s.ptr (bv64OfW iVal) + BitVec.ofNat 64 (s.tAtom.bytes * j))) ∧
    JLoop (iVal + BitVec.ofNat w k, ()) (applyWideStreamsMem m (bv64OfW iVal) k ss)
  | 0, _, _, _ => ⟨fun _ _ _ hj => by omega, by
      rw [applyWideStreamsMem_zero, BitVec.add_zero]; exact hJ⟩
  | k + 1, hk, hBnd, hPair => by
    have hk' : k ≤ bndVal.toNat - iVal.toNat := by omega
    have hBnd' : ∀ s ∈ ss, k * s.tAtom.bytes ≤ 2 ^ 64 := fun s hs =>
      Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_succ k)) (hBnd s hs)
    have hPair' : ss.Pairwise (fun a b => ByteDisj (a.ptr (bv64OfW iVal))
        (k * a.tAtom.bytes) (b.ptr (bv64OfW iVal)) (k * b.tAtom.bytes)) := by
      refine hPair.imp (fun {a b} h => ?_)
      have hSub := byteDisj_sub (offA := 0) (subA := k * a.tAtom.bytes)
        (offB := 0) (subB := k * b.tAtom.bytes) h
        (by rw [Nat.zero_add]; exact Nat.mul_le_mul_right _ (Nat.le_succ k))
        (by rw [Nat.zero_add]; exact Nat.mul_le_mul_right _ (Nat.le_succ k))
      rwa [BitVec.add_zero, BitVec.add_zero] at hSub
    obtain ⟨hOkPrev, hJk⟩ := runMultiScalarMem_step hw hStep iVal m hJ k hk' hBnd' hPair'
    have hltW : iVal.toNat + k < 2 ^ w := by have := bndVal.isLt; omega
    have hkW : k < 2 ^ w := by omega
    have hiK : (iVal + BitVec.ofNat w k).toNat < bndVal.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkW, Nat.mod_eq_of_lt hltW]
      omega
    obtain ⟨hOkCur, hJNext⟩ := hStep (iVal + BitVec.ofNat w k) _ hiK hJk
    have hMapped : ∀ s ∈ ss, ∀ j < k * s.tAtom.bytes,
        (m.get? (s.ptr (bv64OfW iVal) + BitVec.ofNat 64 j)).isSome = true := by
      intro s hs j hj
      have hq : j / s.tAtom.bytes < k := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have hr : j % s.tAtom.bytes < s.tAtom.bytes := Nat.mod_lt _ s.bytes_pos
      have hMem := (storeOk_iff_forall_mem m s.tAtom (s.ptr (bv64OfW iVal) +
        BitVec.ofNat 64 (s.tAtom.bytes * (j / s.tAtom.bytes)))).1
        (hOkPrev s hs (j / s.tAtom.bytes) hq) (j % s.tAtom.bytes) hr
      have hSplit : s.tAtom.bytes * (j / s.tAtom.bytes) + j % s.tAtom.bytes = j :=
        Nat.div_add_mod j s.tAtom.bytes
      rwa [BitVec.add_assoc, ← BitVec.ofNat_add, hSplit] at hMem
    have hDomEq : ∀ q, ((applyWideStreamsMem m (bv64OfW iVal) k ss).get? q).isSome =
        (m.get? q).isSome :=
      applyWideStreamsMem_preserves_dom (bv64OfW iVal) k ss m hMapped
    have hL64 : bv64OfW (iVal + BitVec.ofNat w k) = bv64OfW iVal + BitVec.ofNat 64 k :=
      bvW_setWidth64_add hw iVal bndVal k (by omega)
    rw [hL64] at hOkCur hJNext
    obtain ⟨_, hOkEach⟩ := scalarChainOk_preserves_dom _ ss _ hOkCur
    refine ⟨fun s hs j hj => ?_, ?_⟩
    · by_cases hjLt : j < k
      · exact hOkPrev s hs j hjLt
      · have hjEq : j = k := by omega
        subst hjEq
        have hCur := hOkEach s hs
        rw [scalarStream_ptr_add, Nat.mul_comm] at hCur
        rw [storeOk_iff_forall_mem] at hCur ⊢
        intro b hb; rw [← hDomEq]; exact hCur b hb
    · rw [applyScalarChain_after_wideStreams (bv64OfW iVal) k m ss hPair hBnd] at hJNext
      have hSucc : (iVal + BitVec.ofNat w k) + BitVec.ofNat w 1 =
          iVal + BitVec.ofNat w (k + 1) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      rwa [hSucc] at hJNext

/-! ## Section 3: `mkSeqStores_wp` & `emitWideStreams_wp` -/

private theorem liftOp_add_wp {w : Nat} (hw : w = 32 ∨ w = 64) {x y : BitVec w}
    {K : Tup Val [.bits w] → Prop} (hK : K (x + y, ())) :
    OpCode.wp (OpCode.add (.bits w))
      (vals ((.var x : Arg Val (.bits w)), (.imm y : Arg Val (.bits w)), ())) K := by
  rcases hw with rfl | rfl <;>
    (rw [OpCode.wp_add]; dsimp only [lift2, vals, Arg.val, Ty.hasFloat]; exact hK)

private theorem liftOp_add_args_wp {a b : Arg Val i64} {K : Tup Val [i64] → Prop}
    (hK : K (a.val + b.val, ())) : OpCode.wp (OpCode.add i64) (vals (a, b, ())) K := by
  rw [OpCode.wp_add]; dsimp only [lift2, vals, Arg.val, i64, Ty.hasFloat]
  cases a <;> cases b <;> exact hK
private theorem liftOp_sub_args_wp {w : Nat} (hw : w = 32 ∨ w = 64)
    {a b : Arg Val (.bits w)} {K : Tup Val [.bits w] → Prop} (hK : K (a.val - b.val, ())) :
    OpCode.wp (OpCode.sub (.bits w)) (vals (a, b, ())) K := by
  rcases hw with rfl | rfl
  · rw [OpCode.wp_sub]; dsimp only [lift2, vals, Arg.val, Ty.hasFloat]
    cases a <;> cases b <;> exact hK
  · rw [OpCode.wp_sub]; dsimp only [lift2, vals, Arg.val, Ty.hasFloat]
    cases a <;> cases b <;> exact hK
private theorem liftOp_cmp_args_wp {w : Nat} (hw : w = 32 ∨ w = 64) {o : CmpOp}
    {a b : Arg Val (.bits w)} {K : Tup Val [.bool] → Prop} (hK : K (o.evalBits a.val b.val, ())) :
    OpCode.wp (OpCode.cmp o (.bits w) .bool rfl) (vals (a, b, ())) K := by
  rcases hw with rfl | rfl
  · rw [OpCode.wp_cmp _ _ rfl]; dsimp only [liftCmp, vals, Arg.val, Ty.hasFloat]
    cases a <;> cases b <;> exact hK
  · rw [OpCode.wp_cmp _ _ rfl]; dsimp only [liftCmp, vals, Arg.val, Ty.hasFloat]
    cases a <;> cases b <;> exact hK
private theorem liftOp_or_wp {a b : Arg Val .bool} {K : Tup Val [.bool] → Prop}
    (hK : K ((a.val || b.val), ())) : OpCode.wp (OpCode.or .bool) (vals (a, b, ())) K := by
  rw [OpCode.wp_or]; dsimp only [lift2, vals, Arg.val, Ty.hasFloat]
  cases a <;> cases b <;> exact hK
private theorem liftOp_shl_args_wp {a : Arg Val i64} {s : BitVec 64} {K : Tup Val [i64] → Prop}
    (hK : K (a.val <<< (s.toNat % 64), ())) :
    OpCode.wp (OpCode.shl i64) (vals (a, (.imm s : Arg Val i64), ())) K := by
  rw [OpCode.wp_shl]; dsimp only [lift2, vals, Arg.val, i64, Ty.hasFloat]; cases a <;> exact hK
private theorem pushTup_singleton {t : Ty} (x : Val t) (vs : List ((u : Ty) × Val u)) :
    pushTup (as := [t]) (x, ()) vs = ⟨t, x⟩ :: vs := rfl
private theorem liftOp_zext32_wp {a : Arg Val i32} {K : Tup Val [i64] → Prop}
    (hK : K (a.val.setWidth 64, ())) : OpCode.wp (OpCode.zext 32 64) (vals (a, ())) K := by
  rw [OpCode.wp_zext]; dsimp only [vals, Arg.val]; exact ⟨by decide, hK⟩
private theorem liftOp_copy64_wp {a : Arg Val i64} {K : Tup Val [i64] → Prop}
    (hK : K (a.val, ())) : OpCode.wp (OpCode.copy i64) (vals (a, ())) K := by
  rw [OpCode.wp_copy]; dsimp only [vals, Arg.val]; exact hK
private theorem denoteArg_var0 {V : Ty → Type} {t : Ty} (v : V t)
    (vs : List ((t' : Ty) × V t')) :
    denoteArg (⟨t, v⟩ :: vs) (.var 0 : Arg K t) = some (.var v) := by
  dsimp only [denoteArg, lookupV]; rw [listGet?_cons_zero_eq]; dsimp only
  rw [PassFlatKit.castTy_self]
private theorem denoteArg_var1 {V : Ty → Type} {t0 t1 : Ty} (v0 : V t0) (v1 : V t1)
    (vs : List ((t' : Ty) × V t')) :
    denoteArg (⟨t0, v0⟩ :: ⟨t1, v1⟩ :: vs) (.var 1 : Arg K t1) = some (.var v1) := by
  dsimp only [denoteArg, lookupV, listGet?]; rw [PassFlatKit.castTy_self]
private theorem lookupV_cons_succ {V : Ty → Type} (vs : List ((t' : Ty) × V t'))
    {t t0 : Ty} (v0 : V t0) (idx : Nat) :
    lookupV (⟨t0, v0⟩ :: vs) t (idx + 1) = lookupV vs t idx := rfl
private theorem lookupV_append_extra {V : Ty → Type} :
    (extra : List ((t' : Ty) × V t')) → (vs : List ((t' : Ty) × V t')) →
    {t : Ty} → {idx : Nat} → lookupV (extra ++ vs) t (idx + extra.length) = lookupV vs t idx
  | [], _, _, _ => rfl
  | ⟨_, _⟩ :: extra, vs, t, idx => by
    rw [List.cons_append, List.length_cons, ← Nat.add_assoc]; exact lookupV_append_extra extra vs
private theorem lookupL_0 {L : List Ty → Type} {ts : List Ty} (l : L ts)
    (ls : List ((ts' : List Ty) × L ts')) : lookupL (⟨ts, l⟩ :: ls) ts 0 = some l := by
  dsimp only [lookupL]; rw [listGet?_cons_zero_eq]; dsimp only; exact castListTy_self ts l
private theorem lookupL_1 {L : List Ty → Type} {ts ts0 : List Ty} (l0 : L ts0) (l : L ts)
    (ls : List ((ts' : List Ty) × L ts')) :
    lookupL (⟨ts0, l0⟩ :: ⟨ts, l⟩ :: ls) ts 1 = some l := by
  dsimp only [lookupL, listGet?]; exact castListTy_self ts l

private theorem mkSeqStoresGo_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {fill64 ptr0 : BitVec 64} {cont : Nat → TFlat rs} {ls : List ((ts : List Ty) × Cont ts)} :
    ∀ (r m : Nat) (vs : List ((t : Ty) × Val t)) (mem : Mem 64),
      1 ≤ m → 8 * (r + 1) ≤ 2 ^ 64 →
      lookupV vs i64 (m - 1) = some ptr0 →
      (∀ j < r, storeOk mem i64 (ptr0 + BitVec.ofNat 64 (8 * (m + j)))) →
      (∀ (extra : List ((t : Ty) × Val t)), extra.length = r →
        wp Γ Q X (denote Val Cont (cont (m + r - 1)) (extra ++ vs) ls)
          (mem.storeBytes (ptr0 + BitVec.ofNat 64 (8 * m))
            (List.replicate r (Int.toBytes 8 fill64.toInt)).flatten)) →
      wp Γ Q X (denote Val Cont (mkSeqStoresGo fill64 m r cont) vs ls) mem
  | 0, m, vs, mem, _, _, _, _, hCont => by
    dsimp only [mkSeqStoresGo]
    have h0 := hCont [] rfl
    simpa [Nat.add_zero, storeBytes_nil] using h0
  | r + 1, m, vs, mem, hmGe, hBnd, hPtr, hOk, hCont => by
    dsimp only [mkSeqStoresGo, op2]
    rw [denote_let_eq, denoteArgs_pair_eq]
    have hVarM : denoteArg vs (.var (m - 1) : Arg K i64) = some (.var ptr0) := by
      dsimp only [denoteArg]; rw [hPtr]
    have hImm : denoteArg vs (.imm (BitVec.ofNat 64 (8 * m)) : Arg K i64) =
        some (.imm (BitVec.ofNat 64 (8 * m))) := rfl
    rw [hVarM, hImm, wp_let]; dsimp only [Op.wp]
    refine liftOp_add_args_wp (a := .var ptr0) (b := .imm (BitVec.ofNat 64 (8 * m))) ?_
    dsimp only [Arg.val, pushTup]
    rw [denote_store_eq, denoteArg_var0]
    have hImmF : denoteArg (⟨i64, ptr0 + BitVec.ofNat 64 (8 * m)⟩ :: vs) (.imm fill64 : Arg K i64) =
        some (.imm fill64) := rfl
    rw [hImmF, wp_store]; dsimp only [Arg.val]
    have hOk0 : storeOk mem i64 (ptr0 + BitVec.ofNat 64 (8 * m)) := by
      simpa using hOk 0 (Nat.zero_lt_succ r)
    refine ⟨hOk0, ?_⟩
    let mem1 := storeMem mem i64 (ptr0 + BitVec.ofNat 64 (8 * m)) fill64
    have hPtr' : lookupV (⟨i64, ptr0 + BitVec.ofNat 64 (8 * m)⟩ :: vs) i64 ((m + 1) - 1) =
        some ptr0 := by
      have hmSub : m = (m - 1) + 1 := by omega
      change lookupV (⟨i64, _⟩ :: vs) i64 m = some ptr0
      rw [hmSub]; exact hPtr
    have hOk' : ∀ j < r, storeOk mem1 i64 (ptr0 + BitVec.ofNat 64 (8 * (m + 1 + j))) := by
      intro j hj
      rw [storeOk_storeMem_iff mem i64 (ptr0 + BitVec.ofNat 64 (8 * m)) fill64 hOk0]
      rw [show m + 1 + j = m + (j + 1) by omega]; exact hOk (j + 1) (Nat.succ_lt_succ hj)
    refine mkSeqStoresGo_wp r (m + 1) _ mem1 (by omega) (by omega) hPtr' hOk' ?_
    intro extra hLen
    have hStepEq : (m + 1) + r - 1 = m + (r + 1) - 1 := by omega
    have hMemEq : mem1.storeBytes (ptr0 + BitVec.ofNat 64 (8 * (m + 1)))
        (List.replicate r (Int.toBytes 8 fill64.toInt)).flatten =
        mem.storeBytes (ptr0 + BitVec.ofNat 64 (8 * m))
          (List.replicate (r + 1) (Int.toBytes 8 fill64.toInt)).flatten := by
      rw [show ptr0 + BitVec.ofNat 64 (8 * (m + 1)) =
          (ptr0 + BitVec.ofNat 64 (8 * m)) + BitVec.ofNat 64 8 by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add, Nat.mul_one]]
      exact storeMem_i64_prepend_bytes mem _ fill64 r (by omega)
    rw [hStepEq, hMemEq]
    have hApp := hCont (extra ++ [⟨i64, ptr0 + BitVec.ofNat 64 (8 * m)⟩]) (by simp [hLen])
    rwa [List.append_assoc] at hApp

private theorem mkSeqStores_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {fill64 ptr0 : BitVec 64} {cont : Nat → TFlat rs} {ls : List ((ts : List Ty) × Cont ts)}
    {n64 : Nat} {vs : List ((t : Ty) × Val t)} {mem : Mem 64}
    (hn : 1 ≤ n64) (hBnd : 8 * n64 ≤ 2 ^ 64) (hPtr : lookupV vs i64 0 = some ptr0)
    (hOk : ∀ r < n64, storeOk mem i64 (ptr0 + BitVec.ofNat 64 (8 * r)))
    (hCont : ∀ (extra : List ((t : Ty) × Val t)), extra.length = n64 - 1 →
      wp Γ Q X (denote Val Cont (cont (n64 - 1)) (extra ++ vs) ls)
        (mem.storeBytes ptr0 (List.replicate n64 (Int.toBytes 8 fill64.toInt)).flatten)) :
    wp Γ Q X (denote Val Cont (mkSeqStores fill64 n64 cont) vs ls) mem := by
  cases n64 with
  | zero => omega
  | succ r =>
    dsimp only [mkSeqStores]
    rw [denote_store_eq]
    have hVar0 : denoteArg vs (.var 0 : Arg K i64) = some (.var ptr0) := by
      dsimp only [denoteArg]; rw [hPtr]
    have hImmF : denoteArg vs (.imm fill64 : Arg K i64) = some (.imm fill64) := rfl
    rw [hImmF, hVar0, wp_store]; dsimp only [Arg.val]
    have hOk0 : storeOk mem i64 ptr0 := by simpa using hOk 0 (Nat.zero_lt_succ r)
    refine ⟨hOk0, ?_⟩
    let mem1 := storeMem mem i64 ptr0 fill64
    have hOkRest : ∀ j < r, storeOk mem1 i64 (ptr0 + BitVec.ofNat 64 (8 * (1 + j))) := by
      intro j hj
      rw [storeOk_storeMem_iff mem i64 ptr0 fill64 hOk0]
      exact hOk (1 + j) (by omega)
    refine mkSeqStoresGo_wp r 1 vs mem1 (Nat.le_refl 1) (by omega) hPtr hOkRest ?_
    intro extra hLen
    have hStepEq : 1 + r - 1 = r := by omega
    have hMemEq : mem1.storeBytes (ptr0 + BitVec.ofNat 64 (8 * 1))
        (List.replicate r (Int.toBytes 8 fill64.toInt)).flatten =
        mem.storeBytes ptr0 (List.replicate (r + 1) (Int.toBytes 8 fill64.toInt)).flatten := by
      rw [Nat.mul_one]
      exact storeMem_i64_prepend_bytes mem ptr0 fill64 r (by omega)
    rw [hStepEq, hMemEq]
    exact hCont extra (by simpa using hLen)

private theorem emitWideStreams_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {w stepK : Nat} (hw : w = 32 ∨ w = 64) (hStepPos : 1 ≤ stepK) (hStep512 : stepK ≤ 512)
    {vsOuter : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {JWide : Cont [.bits w]} {iVal : BitVec w} {i64Val : BitVec 64} {memOrig : Mem 64} :
    (stores : List StoreSpec) → (ss : List ScalarStream) →
    PairForall (StreamMatchesSpec vsOuter) ss stores →
    (∀ sp ∈ stores, 1 ≤ stepK / (8 >>> sp.shift) ∧ stepK / (8 >>> sp.shift) ≤ 64 ∧
      (stepK / (8 >>> sp.shift)) * (8 >>> sp.shift) = stepK) →
    (vsLocal : List ((t : Ty) × Val t)) → (iDepth i64Depth : Nat) →
    vsLocal.length ≥ 1 →
    lookupV (vsLocal ++ vsOuter) (.bits w) iDepth = some iVal →
    lookupV (vsLocal ++ vsOuter) i64 i64Depth = some i64Val →
    (mem : Mem 64) →
    (∀ q, (mem.get? q).isSome = (memOrig.get? q).isSome) →
    (∀ sc ∈ ss, ∀ r < stepK / (8 >>> sc.sh),
      storeOk memOrig i64 (sc.ptr i64Val + BitVec.ofNat 64 (8 * r))) →
    JWide (iVal + BitVec.ofNat w stepK, ()) (applyWideStreamsMem mem i64Val stepK ss) →
    wp Γ Q X (denote Val Cont
      (emitWideStreams w stepK stores vsLocal.length iDepth i64Depth)
      (vsLocal ++ vsOuter) (⟨[.bits w], JWide⟩ :: ls)) mem
  | [], [], .nil, _, vsLocal, iDepth, _, _, hiD, _, mem, _, _, hJ => by
    dsimp only [emitWideStreams, op2]
    rw [denote_let_eq, denoteArgs_pair_eq]
    have hVI : denoteArg (vsLocal ++ vsOuter) (.var iDepth : Arg K (.bits w)) =
        some (.var iVal) := by dsimp only [denoteArg]; rw [hiD]
    have hImm : denoteArg (vsLocal ++ vsOuter)
        (.imm (BitVec.ofNat w stepK) : Arg K (.bits w)) =
        some (.imm (BitVec.ofNat w stepK)) := rfl
    rw [hVI, hImm, wp_let]; dsimp only [Op.wp]
    refine liftOp_add_wp hw ?_
    dsimp only [pushTup]
    rw [denote_jump_eq, denoteArgs_singleton_eq, lookupL_0, denoteArg_var0]
    dsimp only; rw [wp_jump]; exact hJ
  | st :: rest, sc :: restSc, .cons hM hRestF, hStK, vsLocal, iDepth, i64Depth,
      hLen1, hiD, hi64D, mem, hDom, hOkOrig, hJ => by
    have hStSpec := hStK st (List.Mem.head _)
    have hRestK : ∀ sp ∈ rest, 1 ≤ stepK / (8 >>> sp.shift) ∧
        stepK / (8 >>> sp.shift) ≤ 64 ∧ (stepK / (8 >>> sp.shift)) * (8 >>> sp.shift) = stepK :=
      fun sp hp => hStK sp (List.Mem.tail _ hp)
    let n64 := stepK / (8 >>> sc.sh)
    have hn64 : 1 ≤ n64 ∧ n64 ≤ 64 ∧ n64 * (8 >>> sc.sh) = stepK := by
      simpa [n64, hM.2.2.1] using hStSpec
    have afterOff : ∀ (vsL1 : List ((t : Ty) × Val t)) (iD1 i64D1 : Nat) (idxVar : Arg K i64)
        (idxA : Arg Val i64),
        vsL1.length ≥ 1 →
        denoteArg (vsL1 ++ vsOuter) idxVar = some idxA → idxA.val = i64Val + sc.oVal →
        lookupV (vsL1 ++ vsOuter) (.bits w) iD1 = some iVal →
        lookupV (vsL1 ++ vsOuter) i64 i64D1 = some i64Val →
        wp Γ Q X (denote Val Cont
          (if (st.shift == 0) = true then
            TFlat.let_ (op2 (.add i64) (tArgShift vsL1.length st.base) idxVar)
              (mkSeqStores st.fill64 (stepK / (8 >>> st.shift)) (fun pushed =>
                emitWideStreams w stepK rest (vsL1.length + 1 + pushed)
                  (iD1 + 1 + pushed) (i64D1 + 1 + pushed)))
          else
            TFlat.let_ (op2 (.shl i64) idxVar (.imm (BitVec.ofNat 64 st.shift)))
              (TFlat.let_ (op2 (.add i64) (tArgShift (vsL1.length + 1) st.base) (.var 0))
                (mkSeqStores st.fill64 (stepK / (8 >>> st.shift)) (fun pushed =>
                  emitWideStreams w stepK rest ((vsL1.length + 1) + 1 + pushed)
                    ((iD1 + 1) + 1 + pushed) ((i64D1 + 1) + 1 + pushed)))))
          (vsL1 ++ vsOuter) (⟨[.bits w], JWide⟩ :: ls)) mem := by
      intro vsL1 iD1 i64D1 idxVar idxA hL1 hdIdx hIdxVal hI1 hI64_1
      have afterShift : ∀ (vsL2 : List ((t : Ty) × Val t)) (iD2 i64D2 : Nat)
          (scVar : Arg K i64) (scA : Arg Val i64),
          vsL2.length ≥ 1 →
          denoteArg (vsL2 ++ vsOuter) scVar = some scA →
          scA.val = (i64Val + sc.oVal) <<< sc.sh →
          lookupV (vsL2 ++ vsOuter) (.bits w) iD2 = some iVal →
          lookupV (vsL2 ++ vsOuter) i64 i64D2 = some i64Val →
          wp Γ Q X (denote Val Cont
            (TFlat.let_ (op2 (.add i64) (tArgShift vsL2.length st.base) scVar)
              (mkSeqStores st.fill64 (stepK / (8 >>> st.shift)) (fun pushed =>
                emitWideStreams w stepK rest (vsL2.length + 1 + pushed)
                  (iD2 + 1 + pushed) (i64D2 + 1 + pushed))))
            (vsL2 ++ vsOuter) (⟨[.bits w], JWide⟩ :: ls)) mem := by
        intro vsL2 iD2 i64D2 scVar scA _ hdSc hScVal hI2 hI64_2
        dsimp only [op2]; rw [denote_let_eq, denoteArgs_pair_eq]
        have hdBaseSh : denoteArg (vsL2 ++ vsOuter) (tArgShift vsL2.length st.base) =
            some sc.baseA := by
          simpa [tArgShift] using (denoteArg_shiftArgAbove (vsPre := []) vsL2 vsOuter st.base).trans
            hM.1
        rw [hdBaseSh, hdSc, wp_let]; dsimp only [Op.wp]
        refine liftOp_add_args_wp (a := sc.baseA) (b := scA) ?_
        dsimp only [pushTup]; rw [hScVal]
        have hPtr0 : lookupV (⟨i64, sc.ptr i64Val⟩ :: (vsL2 ++ vsOuter)) i64 0 =
            some (sc.ptr i64Val) := by dsimp only [lookupV, listGet?, castTy]; rfl
        have hOkCur : ∀ r < n64,
            storeOk mem i64 (sc.ptr i64Val + BitVec.ofNat 64 (8 * r)) := by
          intro r hr
          rw [storeOk_iff_forall_mem]
          intro b hb; rw [hDom]
          exact (storeOk_iff_forall_mem memOrig i64 _).1 (hOkOrig sc (List.Mem.head _) r hr) b hb
        have hSh : st.shift = sc.sh := hM.2.2.1.symm
        rw [hSh, ← hM.2.2.2]
        change wp Γ Q X (denote Val Cont
          (mkSeqStores sc.fill64 n64 (fun pushed =>
            emitWideStreams w stepK rest (vsL2.length + 1 + pushed)
              (iD2 + 1 + pushed) (i64D2 + 1 + pushed)))
          (⟨i64, sc.ptr i64Val⟩ :: (vsL2 ++ vsOuter)) (⟨[.bits w], JWide⟩ :: ls)) mem
        refine mkSeqStores_wp hn64.1 (by omega) hPtr0 hOkCur ?_
        intro extra hExLen
        let vsNext := extra ++ ⟨i64, sc.ptr i64Val⟩ :: vsL2
        have hNextLen : vsNext.length = vsL2.length + 1 + (n64 - 1) := by
          simp [vsNext, hExLen]; omega
        have hINext : lookupV (vsNext ++ vsOuter) (.bits w) (iD2 + 1 + (n64 - 1)) = some iVal := by
          dsimp only [vsNext]; rw [List.append_assoc, List.cons_append]
          rw [show iD2 + 1 + (n64 - 1) = (iD2 + 1) + extra.length by omega]
          rw [lookupV_append_extra extra (⟨i64, sc.ptr i64Val⟩ :: (vsL2 ++ vsOuter))]
          exact hI2
        have hI64Next : lookupV (vsNext ++ vsOuter) i64 (i64D2 + 1 + (n64 - 1)) =
            some i64Val := by
          dsimp only [vsNext]; rw [List.append_assoc, List.cons_append]
          rw [show i64D2 + 1 + (n64 - 1) = (i64D2 + 1) + extra.length by omega]
          rw [lookupV_append_extra extra (⟨i64, sc.ptr i64Val⟩ :: (vsL2 ++ vsOuter))]
          exact hI64_2
        have hRepEq : (List.replicate n64 (Int.toBytes 8 sc.fill64.toInt)).flatten =
            (List.replicate stepK sc.atomBytes).flatten := by
          rw [← sc.hWideBytes, flatten_replicate_flatten, hn64.2.2]; rfl
        have hMem1Dom : ∀ q, ((mem.storeBytes (sc.ptr i64Val)
            (List.replicate stepK sc.atomBytes).flatten).get? q).isSome =
            (memOrig.get? q).isSome := by
          intro q
          rw [← hDom q, ← hRepEq]
          have hBLen : (List.replicate n64 (Int.toBytes 8 sc.fill64.toInt)).flatten.length =
              8 * n64 := by
            rw [length_flatten_replicate, toBytes_length, Nat.mul_comm]
          refine storeBytes_preserves_dom mem (sc.ptr i64Val) _ (fun j hj => ?_) q
          rw [hBLen] at hj
          have hq := hOkCur (j / 8) (Nat.div_lt_of_lt_mul (by omega))
          have hm := (storeOk_iff_forall_mem mem i64 _).1 hq (j % 8) (Nat.mod_lt _ (by decide))
          have hSplit : 8 * (j / 8) + j % 8 = j := by omega
          rwa [BitVec.add_assoc, ← BitVec.ofNat_add, hSplit] at hm
        have hVsNext : vsNext ++ vsOuter = extra ++ ⟨i64, sc.ptr i64Val⟩ :: (vsL2 ++ vsOuter) := by
          dsimp only [vsNext]; simp [List.append_assoc]
        rw [← hVsNext, hRepEq, ← hNextLen]
        exact emitWideStreams_wp hw hStepPos hStep512 rest restSc hRestF hRestK vsNext
          (iD2 + 1 + (n64 - 1)) (i64D2 + 1 + (n64 - 1)) (by omega) hINext hI64Next _ hMem1Dom
          (fun r hr => hOkOrig r (List.Mem.tail _ hr)) hJ
      by_cases hS0 : st.shift = 0
      · rw [ite_eq_left (by simp [hS0])]
        exact afterShift vsL1 iD1 i64D1 idxVar idxA hL1 hdIdx
          (by rw [hIdxVal, hM.2.2.1, hS0, BitVec.shiftLeft_zero]) hI1 hI64_1
      · rw [ite_eq_right (beq_false_of_ne hS0 ▸ Bool.false_ne_true)]
        dsimp only [op2]; rw [denote_let_eq, denoteArgs_pair_eq, hdIdx]
        have hImmS : denoteArg (vsL1 ++ vsOuter)
            (.imm (BitVec.ofNat 64 st.shift) : Arg K i64) =
            some (.imm (BitVec.ofNat 64 st.shift)) := rfl
        rw [hImmS, wp_let]; dsimp only [Op.wp]
        refine liftOp_shl_args_wp (a := idxA) (s := BitVec.ofNat 64 st.shift) ?_
        dsimp only [pushTup]
        have hShLt : st.shift ≤ 3 := hM.2.2.1 ▸ sc.hShLe
        have hMod : (BitVec.ofNat 64 st.shift).toNat % 64 = st.shift := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [← List.cons_append]
        exact afterShift (⟨i64, _⟩ :: vsL1) (iD1 + 1) (i64D1 + 1) (.var 0) (.var _)
          (Nat.succ_pos _) (denoteArg_var0 _ _)
          (by change idxA.val <<< ((BitVec.ofNat 64 st.shift).toNat % 64) = _
              rw [hIdxVal, hMod, hM.2.2.1]) hI1 hI64_1
    dsimp only [emitWideStreams]
    cases hOff : st.off? with
    | none =>
      have hO : sc.oVal = 0#64 := by
        have hm2 := hM.2.1; dsimp only [offVal] at hm2; rw [hOff] at hm2
        exact (Option.some.inj hm2).symm
      have hD64 : denoteArg (vsLocal ++ vsOuter) (.var i64Depth : Arg K i64) =
          some (.var i64Val) := by dsimp only [denoteArg]; rw [hi64D]
      exact afterOff vsLocal iDepth i64Depth (.var i64Depth) (.var i64Val) hLen1 hD64
        (by dsimp only [Arg.val]; rw [hO, BitVec.add_zero]) hiD hi64D
    | some off =>
      have hOffArg : ∃ aOff : Arg Val i64, denoteArg vsOuter off = some aOff ∧
          aOff.val = sc.oVal := by
        have hm2 := hM.2.1; dsimp only [offVal] at hm2; rw [hOff] at hm2
        exact Option.map_eq_some_iff.mp hm2
      obtain ⟨aOff, hdOffA, haOffVal⟩ := hOffArg
      dsimp only [op2]; rw [denote_let_eq, denoteArgs_pair_eq]
      have hD64 : denoteArg (vsLocal ++ vsOuter) (.var i64Depth : Arg K i64) =
          some (.var i64Val) := by dsimp only [denoteArg]; rw [hi64D]
      have hOffSh : denoteArg (vsLocal ++ vsOuter) (tArgShift vsLocal.length off) = some aOff := by
        simpa [tArgShift] using (denoteArg_shiftArgAbove (vsPre := []) vsLocal vsOuter off).trans
          hdOffA
      rw [hD64, hOffSh, wp_let]; dsimp only [Op.wp]
      refine liftOp_add_args_wp (a := .var i64Val) (b := aOff) ?_
      dsimp only [pushTup]; rw [← List.cons_append]
      exact afterOff (⟨i64, _⟩ :: vsLocal) (iDepth + 1) (i64Depth + 1)
        (.var 0) (.var _) (Nat.succ_pos _) (denoteArg_var0 _ _)
        (by change i64Val + aOff.val = i64Val + sc.oVal; rw [haOffVal]) hiD hi64D

/-! ## Section 4: `mkMultiWideBody_wp`, `mkDisjointCheck_wp`, & `widenFillExt_wp` -/

private theorem mkMultiWideBody_iter_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {w stepK : Nat} (hw : w = 32 ∨ w = 64) (hStepPos : 1 ≤ stepK) (hStep512 : stepK ≤ 512)
    {vsOuter : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {bound : Arg K (.bits w)} {bndA : Arg Val (.bits w)}
    (hdBnd : denoteArg vsOuter bound = some bndA)
    {stores : List StoreSpec} {ss : List ScalarStream}
    (hF2 : PairForall (StreamMatchesSpec vsOuter) ss stores)
    (hStK : ∀ sp ∈ stores, 1 ≤ stepK / (8 >>> sp.shift) ∧ stepK / (8 >>> sp.shift) ≤ 64 ∧
      (stepK / (8 >>> sp.shift)) * (8 >>> sp.shift) = stepK)
    {JLoop : Cont [.bits w]} {initA : Arg Val (.bits w)}
    (hStep : ∀ (i' : BitVec w) (m' : Mem 64),
      i'.toNat < bndA.val.toNat → JLoop (i', ()) m' →
      ScalarChainOk m' (bv64OfW i') ss ∧
      JLoop (i' + BitVec.ofNat w 1, ()) (applyScalarChain m' (bv64OfW i') ss))
    (hInvDisj : ∀ (i' : BitVec w), initA.val.toNat ≤ i'.toNat →
      i'.toNat + stepK ≤ bndA.val.toNat →
      ss.Pairwise (fun a b => ByteDisj (a.ptr (bv64OfW i')) (stepK * a.tAtom.bytes)
        (b.ptr (bv64OfW i')) (stepK * b.tAtom.bytes))) :
    let Inv : Nat → Tup Val [.bits w] → Mem 64 → Prop := fun n xs m' =>
      initA.val.toNat ≤ xs.fst.toNat ∧ xs.fst.toNat ≤ bndA.val.toNat ∧
      n = bndA.val.toNat - xs.fst.toNat ∧ JLoop xs m'
    ∀ JWide (n : Nat) (xs : Tup Val [.bits w]) (m' : Mem 64),
      (∀ n' xs' m'', n' < n → Inv n' xs' m'' → JWide xs' m'') →
      Inv n xs m' →
      wp Γ Q X (denote Val Cont (mkMultiWideBody w bound stores stepK) (pushTup xs vsOuter)
        (⟨[.bits w], JWide⟩ :: ⟨[.bits w], JLoop⟩ :: ls)) m' := by
  intro Inv JWide n xs m' ih ⟨hInitLe, hLe, hn, hJL⟩
  rcases xs with ⟨i', ⟨⟩⟩
  dsimp only at hInitLe hLe hn hJL; subst hn
  dsimp only [mkMultiWideBody, op2]
  rw [denote_let_eq, denoteArgs_pair_eq, pushTup_singleton]
  have hBnd1 : denoteArg (⟨.bits w, i'⟩ :: vsOuter) (tArgShift 1 bound) = some bndA := by
    simpa [tArgShift] using
      (denoteArg_shiftArgAbove (vsPre := []) [⟨.bits w, i'⟩] vsOuter bound).trans hdBnd
  rw [hBnd1, denoteArg_var0, wp_let]; dsimp only [Op.wp]
  refine liftOp_sub_args_wp hw (a := bndA) (b := (.var i' : Arg Val (.bits w))) ?_
  rw [show (Arg.var i' : Arg Val (.bits w)).val = i' from rfl]
  let rem := bndA.val - i'
  rw [pushTup_singleton (t := .bits w), denote_let_eq, denoteArgs_pair_eq, denoteArg_var0]
  have hImmK : denoteArg (⟨.bits w, rem⟩ :: ⟨.bits w, i'⟩ :: vsOuter)
      (.imm (BitVec.ofNat w stepK) : Arg K (.bits w)) =
      some (.imm (BitVec.ofNat w stepK)) := rfl
  rw [hImmK, wp_let]; dsimp only [Op.wp]
  refine liftOp_cmp_args_wp hw (o := .uge) (a := (.var rem : Arg Val (.bits w)))
    (b := (.imm (BitVec.ofNat w stepK) : Arg Val (.bits w))) ?_
  rw [show (Arg.var rem : Arg Val (.bits w)).val = rem from rfl,
    show (Arg.imm (BitVec.ofNat w stepK) : Arg Val (.bits w)).val =
      BitVec.ofNat w stepK from rfl]
  let cStep := CmpOp.uge.evalBits rem (BitVec.ofNat w stepK)
  rw [pushTup_singleton (t := Ty.bool), denote_jnz_eq, denoteArg_var0]
  dsimp only; rw [wp_jnz, show (Arg.var cStep : Arg Val Ty.bool).val = cStep from rfl]
  constructor
  · intro hcTrue
    have hStepW : stepK < 2 ^ w := by rcases hw with rfl | rfl <;> omega
    have hRemGe : stepK ≤ bndA.val.toNat - i'.toNat := by
      have hc' : (BitVec.ofNat w stepK).toNat ≤ rem.toNat := by
        dsimp only [cStep, CmpOp.evalBits] at hcTrue
        exact of_decide_eq_true (by unfold BitVec.ule at hcTrue; exact hcTrue)
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hStepW,
        BitVec.toNat_sub_of_le (BitVec.le_def.mpr hLe)] at hc'
    have hLenBnd : ∀ sc ∈ ss, stepK * sc.tAtom.bytes ≤ 2 ^ 64 := fun sc _ => by
      have := sc.hBytesEq
      have h8 : sc.tAtom.bytes ≤ 8 := by
        rw [this]; have := sc.hShLe
        have : sc.sh = 0 ∨ sc.sh = 1 ∨ sc.sh = 2 ∨ sc.sh = 3 := by omega
        rcases this with h | h | h | h <;> simp [h]
      exact Nat.le_trans (Nat.mul_le_mul hStep512 h8) (by decide)
    obtain ⟨hOkSc, hJPostSc⟩ := runMultiScalarMem_step hw hStep i' m' hJL stepK hRemGe
      hLenBnd (hInvDisj i' hInitLe (by omega))
    have hSumLe : i'.toNat + stepK ≤ bndA.val.toNat := by omega
    have hAddNat : (i' + BitVec.ofNat w stepK).toNat = i'.toNat + stepK := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hStepW,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hSumLe bndA.val.isLt)]
    have hWidePost : JWide (i' + BitVec.ofNat w stepK, ())
        (applyWideStreamsMem m' (bv64OfW i') stepK ss) :=
      ih (bndA.val.toNat - (i'.toNat + stepK)) (i' + BitVec.ofNat w stepK, ()) _
        (by omega) ⟨by dsimp only; rw [hAddNat]; omega,
          by dsimp only; rw [hAddNat]; exact hSumLe,
          by dsimp only; rw [hAddNat], hJPostSc⟩
    have hOkWide : ∀ sc ∈ ss, ∀ r < stepK / (8 >>> sc.sh),
        storeOk m' i64 (sc.ptr (bv64OfW i') + BitVec.ofNat 64 (8 * r)) := by
      intro sc hsc r hr
      let k64 := 8 >>> sc.sh
      have hk64Le : stepK / k64 * k64 ≤ stepK := Nat.div_mul_le_self stepK k64
      exact storeOk_split_8 m' sc.tAtom (sc.ptr (bv64OfW i'))
        (stepK / k64) k64 sc.hK64Mul sc.bytes_pos
        (fun j hj => hOkSc sc hsc j (Nat.lt_of_lt_of_le hj hk64Le)) r hr
    rcases hw with rfl | rfl
    · rw [ite_eq_left (by decide)]; dsimp only [op1]
      rw [denote_let_eq, denoteArgs_singleton_eq]
      have hV2 : denoteArg (⟨Ty.bool, CmpOp.uge.evalBits rem (BitVec.ofNat 32 stepK)⟩ ::
          ⟨i32, bndA.val - i'⟩ :: ⟨i32, i'⟩ :: vsOuter) (.var 2 : Arg K i32) = some (.var i') := rfl
      rw [hV2, wp_let]; dsimp only [Op.wp]
      refine liftOp_zext32_wp (a := .var i') ?_
      rw [show (Arg.var i' : Arg Val i32).val = i' from rfl]
      dsimp only [pushTup]
      change wp Γ Q X (denote Val Cont (emitWideStreams 32 stepK stores 4 3 0)
        ([⟨i64, i'.setWidth 64⟩, ⟨Ty.bool, cStep⟩, ⟨i32, rem⟩, ⟨i32, i'⟩] ++ vsOuter)
        (⟨[i32], JWide⟩ :: ⟨[i32], JLoop⟩ :: ls)) m'
      exact emitWideStreams_wp (Or.inl rfl) hStepPos hStep512 stores ss hF2 hStK
        [⟨i64, i'.setWidth 64⟩, ⟨Ty.bool, cStep⟩, ⟨i32, rem⟩, ⟨i32, i'⟩] 3 0 (Nat.succ_pos _)
        rfl rfl m' (fun _ => rfl) hOkWide hWidePost
    · rw [ite_eq_right (by decide)]
      refine emitWideStreams_wp (Or.inr rfl) hStepPos hStep512 stores ss hF2 hStK
        [⟨Ty.bool, cStep⟩, ⟨i64, rem⟩, ⟨i64, i'⟩] 2 2 (Nat.succ_pos _) rfl rfl m'
        (fun _ => rfl) hOkWide ?_
      rwa [bv64OfW_64_eq] at hWidePost
  · intro _
    have hV2 : denoteArg (⟨Ty.bool, CmpOp.uge.evalBits rem (BitVec.ofNat w stepK)⟩ ::
        ⟨.bits w, bndA.val - i'⟩ :: ⟨.bits w, i'⟩ :: vsOuter) (.var 2 : Arg K (.bits w)) =
        some (.var i') := by
      dsimp only [denoteArg, lookupV, listGet?]; rw [PassFlatKit.castTy_self]
    rw [denote_jump_eq, denoteArgs_singleton_eq, lookupL_1, hV2]
    dsimp only; rw [wp_jump]; exact hJL

private def IntervalBound (vsLocal vsOuter : List ((t : Ty) × Val t))
    (lh : Nat × Nat) (lt : BitVec 64 × Nat) : Prop :=
  lh.1 < vsLocal.length ∧ lh.2 < vsLocal.length ∧ lt.1.toNat + lt.2 < 2 ^ 64 ∧
  lookupV (vsLocal ++ vsOuter) i64 (vsLocal.length - 1 - lh.1) = some lt.1 ∧
  lookupV (vsLocal ++ vsOuter) i64 (vsLocal.length - 1 - lh.2) = some (lt.1 + BitVec.ofNat 64 lt.2)

private def IntervalEntry (vsLocal vsOuter : List ((t : Ty) × Val t))
    (init64 rem64 : BitVec 64) (lh : Nat × Nat) (entry : ScalarStream × BitVec 64 × Nat) : Prop :=
  let (sc, lo, tot) := entry
  IntervalBound vsLocal vsOuter lh (lo, tot) ∧ lo = sc.ptr init64 ∧ tot = rem64.toNat * 2 ^ sc.sh

private theorem intervalBound_push {vsLocal vsOuter : List ((t : Ty) × Val t)}
    {lh : Nat × Nat} {lt : BitVec 64 × Nat} {t : Ty} (v : Val t)
    (h : IntervalBound vsLocal vsOuter lh lt) :
    IntervalBound (⟨t, v⟩ :: vsLocal) vsOuter lh lt := by
  rcases h with ⟨h1, h2, hno, hl1, hl2⟩
  refine ⟨by rw [List.length_cons]; omega, by rw [List.length_cons]; omega, hno, ?_, ?_⟩
  · rw [List.length_cons, List.cons_append,
      show vsLocal.length + 1 - 1 - lh.1 = (vsLocal.length - 1 - lh.1) + 1 by omega]
    exact hl1
  · rw [List.length_cons, List.cons_append,
      show vsLocal.length + 1 - 1 - lh.2 = (vsLocal.length - 1 - lh.2) + 1 by omega]
    exact hl2

private theorem intervalEntry_push {vsLocal vsOuter : List ((t : Ty) × Val t)}
    {init64 rem64 : BitVec 64} {lh : Nat × Nat} {entry : ScalarStream × BitVec 64 × Nat}
    {t : Ty} (v : Val t) (h : IntervalEntry vsLocal vsOuter init64 rem64 lh entry) :
    IntervalEntry (⟨t, v⟩ :: vsLocal) vsOuter init64 rem64 lh entry :=
  ⟨intervalBound_push v h.1, h.2⟩

private theorem pairForall_entry_push {vsLocal vsOuter : List ((t : Ty) × Val t)}
    {init64 rem64 : BitVec 64} {ivs : List (Nat × Nat)}
    {done : List (ScalarStream × BitVec 64 × Nat)} {t : Ty} (v : Val t)
    (h : PairForall (IntervalEntry vsLocal vsOuter init64 rem64) ivs done) :
    PairForall (IntervalEntry (⟨t, v⟩ :: vsLocal) vsOuter init64 rem64) ivs done := by
  induction h with
  | nil => exact .nil
  | cons ha _ ih => exact .cons (intervalEntry_push v ha) ih

private theorem intervalBound_uniq {vsLocal vsOuter : List ((t : Ty) × Val t)} {lh : Nat × Nat}
    {lt1 lt2 : BitVec 64 × Nat} (h1 : IntervalBound vsLocal vsOuter lh lt1)
    (h2 : IntervalBound vsLocal vsOuter lh lt2) : lt1 = lt2 := by
  have hlo : lt1.1 = lt2.1 := by
    have h := h1.2.2.2.1; rw [h2.2.2.2.1] at h; exact (Option.some.inj h).symm
  have hhi : lt1.1 + BitVec.ofNat 64 lt1.2 = lt2.1 + BitVec.ofNat 64 lt2.2 := by
    have h := h1.2.2.2.2; rw [h2.2.2.2.2] at h; exact (Option.some.inj h).symm
  rw [hlo] at hhi
  have hnat := congrArg BitVec.toNat hhi
  have hL1 := h1.2.2.1; have hL2 := h2.2.2.1
  have hlt1 : lt1.2 < 2 ^ 64 := by omega
  have hlt2 : lt2.2 < 2 ^ 64 := by omega
  have hS1 : lt2.1.toNat + lt1.2 < 2 ^ 64 := by rw [← hlo]; exact hL1
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2, Nat.mod_eq_of_lt hS1,
    Nat.mod_eq_of_lt hL2] at hnat
  exact Prod.ext hlo (by omega)

private theorem pairwise_of_allIdxPairs {α β : Type} {P : α → β → Prop} {R : β → β → Prop}
    {xs : List α} {ys : List β} (hF : PairForall P xs ys)
    (hAll : ∀ p ∈ allIdxPairs xs, ∀ bx by_, P p.1 bx → P p.2 by_ → R bx by_) :
    ys.Pairwise R := by
  induction hF with
  | nil => exact .nil
  | @cons x y xs' ys' hP hRest ih =>
    rw [List.pairwise_cons]
    refine ⟨fun y' hy' => ?_, ih (fun p hp => hAll p (List.mem_append_right _ hp))⟩
    have exX : ∀ {as bs} (hf : PairForall P as bs) {b}, b ∈ bs → ∃ a ∈ as, P a b := by
      intro as bs hf b hb
      induction hf with
      | nil => cases hb
      | cons ha _ ih2 =>
        cases hb with
        | head => exact ⟨_, List.Mem.head _, ha⟩
        | tail _ hb' => obtain ⟨a', ha', hpa⟩ := ih2 hb'; exact ⟨a', List.Mem.tail _ ha', hpa⟩
    obtain ⟨x', hx', hPx'⟩ := exX hRest hy'
    exact hAll (x, x') (List.mem_append_left _ (List.mem_map.mpr ⟨x', hx', rfl⟩)) y y' hP hPx'

private theorem pairwise_reverse {α : Type} {R : α → α → Prop} (hSymm : ∀ a b, R a b → R b a) :
    (xs : List α) → xs.reverse.Pairwise R → xs.Pairwise R
  | [], _ => .nil
  | x :: xs, h => by
    rw [List.reverse_cons, List.pairwise_append] at h
    rw [List.pairwise_cons]
    refine ⟨fun y hy => ?_, pairwise_reverse hSymm xs h.1⟩
    exact hSymm y x (h.2.2 y (List.mem_reverse.mpr hy) x List.mem_cons_self)

private theorem pairwise_map_spec {α β : Type} {f : α → β} {S : α → Prop}
    {R : α → α → Prop} {Q : β → β → Prop}
    (hMap : ∀ a b, S a → S b → R a b → Q (f a) (f b)) :
    (xs : List α) → (∀ x ∈ xs, S x) → xs.Pairwise R → (xs.map f).Pairwise Q
  | [], _, _ => .nil
  | x :: xs, hS, hP => by
    rw [List.pairwise_cons] at hP
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨fun y hy => ?_, pairwise_map_spec hMap xs (fun z hz => hS z (List.Mem.tail _ hz)) hP.2⟩
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    exact hMap x z (hS x (List.Mem.head _)) (hS z (List.Mem.tail _ hz)) (hP.1 z hz)

private theorem mkPairChecks_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {w : Nat} {initArg : Arg K (.bits w)} {initA : Arg Val (.bits w)}
    {vsOuter : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {JWide JLoop : Cont [.bits w]} (hdInit : denoteArg vsOuter initArg = some initA) (hm : Mem 64)
    (hJInit : JLoop (initA.val, ()) hm) :
    (pairs : List ((Nat × Nat) × (Nat × Nat))) → (vsLocal : List ((t : Ty) × Val t)) →
    (∀ p ∈ pairs, (∃ lt1, IntervalBound vsLocal vsOuter p.1 lt1) ∧
      (∃ lt2, IntervalBound vsLocal vsOuter p.2 lt2)) →
    ((∀ p ∈ pairs, ∀ lt1 lt2, IntervalBound vsLocal vsOuter p.1 lt1 →
        IntervalBound vsLocal vsOuter p.2 lt2 → ByteDisj lt1.1 lt1.2 lt2.1 lt2.2) →
      JWide (initA.val, ()) hm) →
    wp Γ Q X (denote Val Cont (mkPairChecks w initArg pairs vsLocal.length)
      (vsLocal ++ vsOuter) (⟨[.bits w], JWide⟩ :: ⟨[.bits w], JLoop⟩ :: ls)) hm
  | [], vsLocal, _, hPass => by
    dsimp only [mkPairChecks]
    have hInitSh : denoteArg (vsLocal ++ vsOuter) (tArgShift vsLocal.length initArg) =
        some initA := by
      simpa [tArgShift] using (denoteArg_shiftArgAbove (vsPre := []) vsLocal vsOuter initArg).trans
        hdInit
    rw [denote_jump_eq, denoteArgs_singleton_eq, lookupL_0, hInitSh]
    dsimp only; rw [wp_jump]; exact hPass (fun _ h => nomatch h)
  | ((loA, hiA), (loB, hiB)) :: rest, vsLocal, hEntries, hPass => by
    obtain ⟨⟨⟨lA, tA⟩, hEA⟩, ⟨⟨lB, tB⟩, hEB⟩⟩ := hEntries _ (List.Mem.head _)
    obtain ⟨h1A, h2A, hnoA, hvLoA, hvHiA⟩ := hEA
    obtain ⟨h1B, h2B, hnoB, hvLoB, hvHiB⟩ := hEB
    dsimp only [mkPairChecks, op2]
    rw [denote_let_eq, denoteArgs_pair_eq]
    have hVHiA : denoteArg (vsLocal ++ vsOuter) (.var (vsLocal.length - 1 - hiA) : Arg K i64) =
        some (.var (lA + BitVec.ofNat 64 tA)) := by dsimp only [denoteArg]; rw [hvHiA]
    have hVLoB : denoteArg (vsLocal ++ vsOuter) (.var (vsLocal.length - 1 - loB) : Arg K i64) =
        some (.var lB) := by dsimp only [denoteArg]; rw [hvLoB]
    rw [hVHiA, hVLoB, wp_let]; dsimp only [Op.wp]
    refine liftOp_cmp_args_wp (Or.inr rfl) (o := .ule) (a := .var _) (b := .var _) ?_
    rw [show (Arg.var (lA + BitVec.ofNat 64 tA) : Arg Val i64).val =
        lA + BitVec.ofNat 64 tA from rfl,
      show (Arg.var lB : Arg Val i64).val = lB from rfl]
    let c1 := CmpOp.ule.evalBits (lA + BitVec.ofNat 64 tA) lB
    rw [pushTup_singleton (t := Ty.bool), denote_let_eq, denoteArgs_pair_eq]
    have hVHiB : denoteArg (⟨Ty.bool, c1⟩ :: (vsLocal ++ vsOuter))
        (.var (vsLocal.length - hiB) : Arg K i64) =
        some (.var (lB + BitVec.ofNat 64 tB)) := by
      have : hiB < vsLocal.length := h2B
      rw [show vsLocal.length - hiB = (vsLocal.length - 1 - hiB) + 1 by omega]
      dsimp only [denoteArg]; rw [lookupV_cons_succ, hvHiB]
    have hVLoA : denoteArg (⟨Ty.bool, c1⟩ :: (vsLocal ++ vsOuter))
        (.var (vsLocal.length - loA) : Arg K i64) = some (.var lA) := by
      have : loA < vsLocal.length := h1A
      rw [show vsLocal.length - loA = (vsLocal.length - 1 - loA) + 1 by omega]
      dsimp only [denoteArg]; rw [lookupV_cons_succ, hvLoA]
    rw [hVHiB, hVLoA, wp_let]; dsimp only [Op.wp]
    refine liftOp_cmp_args_wp (Or.inr rfl) (o := .ule) (a := .var _) (b := .var _) ?_
    rw [show (Arg.var (lB + BitVec.ofNat 64 tB) : Arg Val i64).val =
        lB + BitVec.ofNat 64 tB from rfl,
      show (Arg.var lA : Arg Val i64).val = lA from rfl]
    let c2 := CmpOp.ule.evalBits (lB + BitVec.ofNat 64 tB) lA
    rw [pushTup_singleton (t := Ty.bool), denote_let_eq, denoteArgs_pair_eq,
      denoteArg_var1, denoteArg_var0, wp_let]; dsimp only [Op.wp]
    refine liftOp_or_wp (a := .var c1) (b := .var c2) ?_
    rw [show (Arg.var c1 : Arg Val Ty.bool).val = c1 from rfl,
      show (Arg.var c2 : Arg Val Ty.bool).val = c2 from rfl]
    let vsL3 : List ((t : Ty) × Val t) :=
      [⟨Ty.bool, c1 || c2⟩, ⟨Ty.bool, c2⟩, ⟨Ty.bool, c1⟩] ++ vsLocal
    rw [pushTup_singleton (t := Ty.bool), denote_jnz_eq, denoteArg_var0]
    dsimp only; rw [wp_jnz]
    rw [show (Arg.var (c1 || c2) : Arg Val Ty.bool).val = (c1 || c2) from rfl]
    constructor
    · intro hDisjTrue
      have hLen3 : vsL3.length = vsLocal.length + 3 := by simp [vsL3]
      change wp Γ Q X (denote Val Cont (mkPairChecks w initArg rest (vsLocal.length + 3))
        (vsL3 ++ vsOuter) (⟨[.bits w], JWide⟩ :: ⟨[.bits w], JLoop⟩ :: ls)) hm
      rw [← hLen3]
      have push3 : ∀ {lh lt}, IntervalBound vsLocal vsOuter lh lt →
          IntervalBound vsL3 vsOuter lh lt := fun h =>
        intervalBound_push _ (intervalBound_push _ (intervalBound_push _ h))
      refine mkPairChecks_wp hdInit hm hJInit rest vsL3 ?_ ?_
      · intro p hp
        obtain ⟨⟨lt1, h1⟩, ⟨lt2, h2⟩⟩ := hEntries p (List.Mem.tail _ hp)
        exact ⟨⟨lt1, push3 h1⟩, ⟨lt2, push3 h2⟩⟩
      · intro hRestDisj
        refine hPass (fun p hp lt1 lt2 hb1 hb2 => ?_)
        cases hp with
        | head =>
          have hEA : IntervalBound vsLocal vsOuter (loA, hiA) (lA, tA) :=
            ⟨h1A, h2A, hnoA, hvLoA, hvHiA⟩
          have hEB : IntervalBound vsLocal vsOuter (loB, hiB) (lB, tB) :=
            ⟨h1B, h2B, hnoB, hvLoB, hvHiB⟩
          change IntervalBound vsLocal vsOuter (loA, hiA) lt1 at hb1
          change IntervalBound vsLocal vsOuter (loB, hiB) lt2 at hb2
          have hE1 : lt1 = (lA, tA) := intervalBound_uniq hb1 hEA
          have hE2 : lt2 = (lB, tB) := intervalBound_uniq hb2 hEB
          rw [hE1, hE2]
          have hSepNat : (lA + BitVec.ofNat 64 tA).toNat ≤ lB.toNat ∨
              (lB + BitVec.ofNat 64 tB).toNat ≤ lA.toNat := by
            simp only [Bool.or_eq_true] at hDisjTrue
            rcases hDisjTrue with hc1 | hc2
            · left; dsimp only [c1, CmpOp.evalBits] at hc1
              exact of_decide_eq_true (by unfold BitVec.ule at hc1; exact hc1)
            · right; dsimp only [c2, CmpOp.evalBits] at hc2
              exact of_decide_eq_true (by unfold BitVec.ule at hc2; exact hc2)
          have htALt : tA < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hnoA
          have htBLt : tB < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hnoB
          have hHiA : (lA + BitVec.ofNat 64 tA).toNat = lA.toNat + tA := by
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htALt,
              Nat.mod_eq_of_lt hnoA]
          have hHiB : (lB + BitVec.ofNat 64 tB).toNat = lB.toNat + tB := by
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htBLt,
              Nat.mod_eq_of_lt hnoB]
          rw [hHiA, hHiB] at hSepNat
          exact byteDisj_of_intervals hnoA hnoB hSepNat
        | tail _ hp' => exact hRestDisj p hp' lt1 lt2 (push3 hb1) (push3 hb2)
    · intro _
      have hLen3 : vsL3.length = vsLocal.length + 3 := by simp [vsL3]
      have hInitSh : denoteArg
          (⟨Ty.bool, c1 || c2⟩ :: ⟨Ty.bool, c2⟩ :: ⟨Ty.bool, c1⟩ :: (vsLocal ++ vsOuter))
          (tArgShift (vsLocal.length + 3) initArg) = some initA := by
        change denoteArg (vsL3 ++ vsOuter) (tArgShift (vsLocal.length + 3) initArg) = some initA
        rw [← hLen3]
        simpa [tArgShift] using (denoteArg_shiftArgAbove (vsPre := []) vsL3 vsOuter initArg).trans
          hdInit
      dsimp only [c1, c2] at hInitSh
      rw [denote_jump_eq, denoteArgs_singleton_eq, lookupL_1, hInitSh]
      dsimp only; rw [wp_jump]; exact hJInit

private theorem allIdxPairs_mem {α : Type} {xs : List α} {p : α × α} (hp : p ∈ allIdxPairs xs) :
    p.1 ∈ xs ∧ p.2 ∈ xs := by
  induction xs with
  | nil => cases hp
  | cons x xs ih =>
    dsimp only [allIdxPairs] at hp; rw [List.mem_append] at hp
    rcases hp with hmap | hrest
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hmap
      exact ⟨List.Mem.head _, List.Mem.tail _ hy⟩
    · obtain ⟨h1, h2⟩ := ih hrest
      exact ⟨List.Mem.tail _ h1, List.Mem.tail _ h2⟩

private theorem intervalEntry_done_spec {vsLocal vsOuter : List ((t : Ty) × Val t)}
    {init64 rem64 : BitVec 64} {ivs : List (Nat × Nat)}
    {done : List (ScalarStream × BitVec 64 × Nat)}
    (hDone : PairForall (IntervalEntry vsLocal vsOuter init64 rem64) ivs done) :
    ∀ e ∈ done, e.2.1 = e.1.ptr init64 ∧ e.2.2 = rem64.toNat * 2 ^ e.1.sh ∧
      e.2.1.toNat + e.2.2 < 2 ^ 64 := by
  induction hDone with
  | nil => intro _ h; cases h
  | cons ha _ ih =>
    intro e he; cases he with
    | head => exact ⟨ha.2.1, ha.2.2, ha.1.2.2.1⟩
    | tail _ ht => exact ih e ht

private theorem lookupV_lvl_push {V : Ty → Type} {vs vsOuter : List ((t : Ty) × V t)}
    {t u : Ty} {x : V t} {y : V u} {lvl : Nat} (hlt : lvl < vs.length)
    (h : lookupV (vs ++ vsOuter) t (vs.length - 1 - lvl) = some x) :
    lookupV ((⟨u, y⟩ :: vs) ++ vsOuter) t ((⟨u, y⟩ :: vs).length - 1 - lvl) = some x := by
  rw [List.length_cons, List.cons_append,
    show vs.length + 1 - 1 - lvl = (vs.length - 1 - lvl) + 1 by omega]
  exact h

private theorem lookupV_lvl_push2 {V : Ty → Type} {vs vsOuter : List ((t : Ty) × V t)}
    {t u1 u2 : Ty} {x : V t} {y1 : V u1} {y2 : V u2} {lvl : Nat} (hlt : lvl < vs.length)
    (h : lookupV (vs ++ vsOuter) t (vs.length - 1 - lvl) = some x) :
    lookupV ((⟨u1, y1⟩ :: ⟨u2, y2⟩ :: vs) ++ vsOuter) t
      ((⟨u1, y1⟩ :: ⟨u2, y2⟩ :: vs).length - 1 - lvl) = some x :=
  lookupV_lvl_push (by rw [List.length_cons]; omega) (lookupV_lvl_push hlt h)

private theorem mkStreamBounds_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {w : Nat} {initArg : Arg K (.bits w)} {initA : Arg Val (.bits w)}
    {vsOuter : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {JWide JLoop : Cont [.bits w]} {rem64Lvl init64Lvl : Nat} {init64 rem64 : BitVec 64}
    (hdInit : denoteArg vsOuter initArg = some initA) (hm : Mem 64)
    (hJInit : JLoop (initA.val, ()) hm) (hRem60 : rem64.toNat < 2 ^ 60) :
    (rest : List StoreSpec) → (restSc : List ScalarStream) →
    PairForall (StreamMatchesSpec vsOuter) restSc rest →
    (ivs : List (Nat × Nat)) → (done : List (ScalarStream × BitVec 64 × Nat)) →
    (vsLocal : List ((t : Ty) × Val t)) →
    rem64Lvl < vsLocal.length → init64Lvl < vsLocal.length →
    lookupV (vsLocal ++ vsOuter) i64 (vsLocal.length - 1 - rem64Lvl) = some rem64 →
    lookupV (vsLocal ++ vsOuter) i64 (vsLocal.length - 1 - init64Lvl) = some init64 →
    PairForall (IntervalEntry vsLocal vsOuter init64 rem64) ivs done →
    ((∀ sc ∈ done.reverse.map Prod.fst ++ restSc,
        (sc.ptr init64).toNat + rem64.toNat * 2 ^ sc.sh < 2 ^ 64) →
      (done.reverse.map Prod.fst ++ restSc).Pairwise
        (fun a b => ByteDisj (a.ptr init64) (rem64.toNat * a.tAtom.bytes)
          (b.ptr init64) (rem64.toNat * b.tAtom.bytes)) →
      JWide (initA.val, ()) hm) →
    wp Γ Q X (denote Val Cont (mkStreamBounds w initArg rem64Lvl init64Lvl rest vsLocal.length ivs)
      (vsLocal ++ vsOuter) (⟨[.bits w], JWide⟩ :: ⟨[.bits w], JLoop⟩ :: ls)) hm
  | [], [], .nil, ivs, done, vsLocal, _, _, _, _, hDone, hPass => by
    dsimp only [mkStreamBounds]
    have memEx : ∀ x ∈ ivs, ∃ e, IntervalEntry vsLocal vsOuter init64 rem64 x e := by
      clear hPass
      induction hDone with
      | nil => intro _ hx; cases hx
      | cons ha _ ih =>
        intro x hx; cases hx with | head => exact ⟨_, ha⟩ | tail _ ht => exact ih x ht
    refine mkPairChecks_wp hdInit hm hJInit (allIdxPairs ivs) vsLocal ?_ ?_
    · intro p hp
      obtain ⟨h1, h2⟩ := allIdxPairs_mem hp
      obtain ⟨e1, he1⟩ := memEx p.1 h1
      obtain ⟨e2, he2⟩ := memEx p.2 h2
      exact ⟨⟨_, he1.1⟩, ⟨_, he2.1⟩⟩
    · intro hPairDisj
      have hDonePair : done.Pairwise (fun a b => ByteDisj a.2.1 a.2.2 b.2.1 b.2.2) :=
        pairwise_of_allIdxPairs hDone (fun p hp bx by_ hx hy => hPairDisj p hp _ _ hx.1 hy.1)
      have hRevPair : done.reverse.Pairwise (fun a b => ByteDisj a.2.1 a.2.2 b.2.1 b.2.2) :=
        pairwise_reverse (fun _ _ h => byteDisj_symm h) done.reverse (by simpa using hDonePair)
      have hEntrySpec : ∀ e ∈ done.reverse, e.2.1 = e.1.ptr init64 ∧
          e.2.2 = rem64.toNat * 2 ^ e.1.sh ∧ e.2.1.toNat + e.2.2 < 2 ^ 64 :=
        fun e he => intervalEntry_done_spec hDone e (List.mem_reverse.mp he)
      have hAllNo : ∀ sc ∈ done.reverse.map Prod.fst ++ [],
          (sc.ptr init64).toNat + rem64.toNat * 2 ^ sc.sh < 2 ^ 64 := by
        intro sc hsc
        rw [List.append_nil, List.mem_map] at hsc
        obtain ⟨e, he, rfl⟩ := hsc
        have hs := hEntrySpec e he
        simpa [hs.1, hs.2.1] using hs.2.2
      have hAllDisj : (done.reverse.map Prod.fst ++ []).Pairwise
          (fun (a b : ScalarStream) => ByteDisj (a.ptr init64) (rem64.toNat * a.tAtom.bytes)
            (b.ptr init64) (rem64.toNat * b.tAtom.bytes)) := by
        rw [List.append_nil]
        refine pairwise_map_spec (f := Prod.fst)
          (S := fun e => e.2.1 = e.1.ptr init64 ∧ e.2.2 = rem64.toNat * 2 ^ e.1.sh)
          (R := fun a b => ByteDisj a.2.1 a.2.2 b.2.1 b.2.2) ?_ done.reverse
          (fun e he => ⟨(hEntrySpec e he).1, (hEntrySpec e he).2.1⟩) hRevPair
        intro a b ha hb hR
        rw [ha.1, ha.2, ← a.1.hBytesEq, hb.1, hb.2, ← b.1.hBytesEq] at hR; exact hR
      exact hPass hAllNo hAllDisj
  | st :: rest, sc :: restSc, .cons hM hRest, ivs, done, vsLocal,
      hRemLt, hInitLt, hRemV, hInitV, hDone, hPass => by
    have withIdx : ∀ (vsL1 : List ((t : Ty) × Val t)) (idxVar : Arg K i64) (idxA : Arg Val i64),
        vsL1.length ≥ vsLocal.length →
        denoteArg (vsL1 ++ vsOuter) idxVar = some idxA → idxA.val = init64 + sc.oVal →
        lookupV (vsL1 ++ vsOuter) i64 (vsL1.length - 1 - rem64Lvl) = some rem64 →
        lookupV (vsL1 ++ vsOuter) i64 (vsL1.length - 1 - init64Lvl) = some init64 →
        PairForall (IntervalEntry vsL1 vsOuter init64 rem64) ivs done →
        wp Γ Q X (denote Val Cont
          (let withScaled (d2 : Nat) (scaledVar : Arg K i64) : TFlat rs :=
             .let_ (op2 (.add i64) (tArgShift d2 st.base) scaledVar)
               (let loLvl := d2; let d3 := d2 + 1
                let afterTot (d4 : Nat) (totVar : Arg K i64) : TFlat rs :=
                  .let_ (op2 (.add i64) (.var (d4 - 1 - loLvl)) totVar)
                    (let hiLvl := d4; let d5 := d4 + 1
                     .let_ (op2 (.cmp .ule i64 .bool rfl) (.var (d5 - 1 - loLvl)) (.var 0))
                       (.jnz (.var 0)
                         (mkStreamBounds w initArg rem64Lvl init64Lvl rest (d5 + 1)
                           ((loLvl, hiLvl) :: ivs))
                         (.jump (ts := [.bits w]) 1 (tArgShift (d5 + 1) initArg, ()))))
                if st.shift == 0 then afterTot d3 (.var (d3 - 1 - rem64Lvl))
                else
                  .let_ (op2 (.shl i64) (.var (d3 - 1 - rem64Lvl))
                    (.imm (BitVec.ofNat 64 st.shift)))
                    (afterTot (d3 + 1) (.var 0)))
           if st.shift == 0 then withScaled vsL1.length idxVar
           else
             .let_ (op2 (.shl i64) idxVar (.imm (BitVec.ofNat 64 st.shift)))
               (withScaled (vsL1.length + 1) (.var 0)))
          (vsL1 ++ vsOuter) (⟨[.bits w], JWide⟩ :: ⟨[.bits w], JLoop⟩ :: ls)) hm := by
      intro vsL1 idxVar idxA hLen1 hdIdx hIdxVal hRem1 hInit1 hDone1
      have withScaled : ∀ (vsL2 : List ((t : Ty) × Val t)) (scVar : Arg K i64) (scA : Arg Val i64),
          vsL2.length ≥ vsLocal.length →
          denoteArg (vsL2 ++ vsOuter) scVar = some scA →
          scA.val = (init64 + sc.oVal) <<< sc.sh →
          lookupV (vsL2 ++ vsOuter) i64 (vsL2.length - 1 - rem64Lvl) = some rem64 →
          lookupV (vsL2 ++ vsOuter) i64 (vsL2.length - 1 - init64Lvl) = some init64 →
          PairForall (IntervalEntry vsL2 vsOuter init64 rem64) ivs done →
          wp Γ Q X (denote Val Cont
            (.let_ (op2 (.add i64) (tArgShift vsL2.length st.base) scVar)
              (let loLvl := vsL2.length; let d3 := vsL2.length + 1
               let afterTot (d4 : Nat) (totVar : Arg K i64) : TFlat rs :=
                 .let_ (op2 (.add i64) (.var (d4 - 1 - loLvl)) totVar)
                   (let hiLvl := d4; let d5 := d4 + 1
                    .let_ (op2 (.cmp .ule i64 .bool rfl) (.var (d5 - 1 - loLvl)) (.var 0))
                      (.jnz (.var 0)
                        (mkStreamBounds w initArg rem64Lvl init64Lvl rest (d5 + 1)
                          ((loLvl, hiLvl) :: ivs))
                        (.jump (ts := [.bits w]) 1 (tArgShift (d5 + 1) initArg, ()))))
               if st.shift == 0 then afterTot d3 (.var (d3 - 1 - rem64Lvl))
               else
                 .let_ (op2 (.shl i64) (.var (d3 - 1 - rem64Lvl))
                   (.imm (BitVec.ofNat 64 st.shift)))
                   (afterTot (d3 + 1) (.var 0))))
            (vsL2 ++ vsOuter) (⟨[.bits w], JWide⟩ :: ⟨[.bits w], JLoop⟩ :: ls)) hm := by
        intro vsL2 scVar scA hLen2 hdSc hScVal hRem2 hInit2 hDone2
        dsimp only [op2]; rw [denote_let_eq, denoteArgs_pair_eq]
        have hdBaseSh : denoteArg (vsL2 ++ vsOuter) (tArgShift vsL2.length st.base) =
            some sc.baseA := by
          simpa [tArgShift] using
            (denoteArg_shiftArgAbove (vsPre := []) vsL2 vsOuter st.base).trans hM.1
        rw [hdBaseSh, hdSc, wp_let]; dsimp only [Op.wp]
        refine liftOp_add_args_wp (a := sc.baseA) (b := scA) ?_
        dsimp only [pushTup]; rw [hScVal]
        let lo := sc.ptr init64
        let vsL3 := ⟨i64, lo⟩ :: vsL2
        have hRem3 := lookupV_lvl_push (u := i64) (y := lo) (by omega) hRem2
        have hInit3 := lookupV_lvl_push (u := i64) (y := lo) (by omega) hInit2
        have hAfterTot : ∀ (vsL4 : List ((t : Ty) × Val t)) (totVar : Arg K i64)
            (totA : Arg Val i64),
            vsL4.length ≥ vsL2.length + 1 →
            denoteArg (vsL4 ++ vsOuter) totVar = some totA →
            totA.val = rem64 <<< sc.sh →
            lookupV (vsL4 ++ vsOuter) i64 (vsL4.length - 1 - vsL2.length) = some lo →
            lookupV (vsL4 ++ vsOuter) i64 (vsL4.length - 1 - rem64Lvl) = some rem64 →
            lookupV (vsL4 ++ vsOuter) i64 (vsL4.length - 1 - init64Lvl) = some init64 →
            PairForall (IntervalEntry vsL4 vsOuter init64 rem64) ivs done →
            wp Γ Q X (denote Val Cont
              (.let_ (op2 (.add i64) (.var (vsL4.length - 1 - vsL2.length)) totVar)
                (.let_ (op2 (.cmp .ule i64 .bool rfl) (.var (vsL4.length + 1 - 1 - vsL2.length))
                    (.var 0))
                  (.jnz (.var 0)
                    (mkStreamBounds w initArg rem64Lvl init64Lvl rest (vsL4.length + 2)
                      ((vsL2.length, vsL4.length) :: ivs))
                    (.jump (ts := [.bits w]) 1 (tArgShift (vsL4.length + 2) initArg, ())))))
              (vsL4 ++ vsOuter) (⟨[.bits w], JWide⟩ :: ⟨[.bits w], JLoop⟩ :: ls)) hm := by
          intro vsL4 totVar totA hLen4 hdTot hTotVal hLo4 hRem4 hInit4 hDone4
          dsimp only [op2]; rw [denote_let_eq, denoteArgs_pair_eq]
          have hVLo : denoteArg (vsL4 ++ vsOuter)
              (.var (vsL4.length - 1 - vsL2.length) : Arg K i64) =
              some (.var lo) := by dsimp only [denoteArg]; rw [hLo4]
          rw [hVLo, hdTot, wp_let]; dsimp only [Op.wp]
          refine liftOp_add_args_wp (a := .var lo) (b := totA) ?_
          rw [show (Arg.var lo : Arg Val i64).val = lo from rfl]
          dsimp only [pushTup]; rw [hTotVal]
          let hi := lo + (rem64 <<< sc.sh)
          let vsL5 : List ((t : Ty) × Val t) := ⟨i64, hi⟩ :: vsL4
          have hLo5 : lookupV (vsL5 ++ vsOuter) i64 (vsL4.length + 1 - 1 - vsL2.length) =
              some lo := by
            dsimp only [vsL5]; rw [List.cons_append,
              show vsL4.length + 1 - 1 - vsL2.length = (vsL4.length - 1 - vsL2.length) + 1 by omega]
            exact hLo4
          rw [show (⟨i64, hi⟩ :: (vsL4 ++ vsOuter)) = vsL5 ++ vsOuter from rfl]
          rw [denote_let_eq, denoteArgs_pair_eq]
          have hVLo5 : denoteArg (vsL5 ++ vsOuter)
              (.var (vsL4.length + 1 - 1 - vsL2.length) : Arg K i64) = some (.var lo) := by
            dsimp only [denoteArg]; rw [hLo5]
          have hV0_5 : denoteArg (vsL5 ++ vsOuter) (.var 0 : Arg K i64) = some (.var hi) := rfl
          rw [hVLo5, hV0_5, wp_let]; dsimp only [Op.wp]
          refine liftOp_cmp_args_wp (Or.inr rfl) (o := .ule) (a := .var lo) (b := .var hi) ?_
          rw [show (Arg.var lo : Arg Val i64).val = lo from rfl,
            show (Arg.var hi : Arg Val i64).val = hi from rfl]
          let cNoWrap := CmpOp.ule.evalBits lo hi
          let vsL6 : List ((t : Ty) × Val t) := ⟨Ty.bool, cNoWrap⟩ :: vsL5
          rw [pushTup_singleton (t := Ty.bool), denote_jnz_eq, denoteArg_var0]
          dsimp only; rw [wp_jnz, show (Arg.var cNoWrap : Arg Val Ty.bool).val = cNoWrap from rfl]
          constructor
          · intro hNoWrapTrue
            have hTotEq : rem64 <<< sc.sh = BitVec.ofNat 64 (rem64.toNat * 2 ^ sc.sh) := by
              apply BitVec.eq_of_toNat_eq
              have : sc.sh = 0 ∨ sc.sh = 1 ∨ sc.sh = 2 ∨ sc.sh = 3 := by have := sc.hShLe; omega
              have hMulLt : rem64.toNat * 2 ^ sc.sh < 2 ^ 64 := by
                rcases this with h | h | h | h <;> simp [h] <;> omega
              rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
                Nat.mod_eq_of_lt hMulLt]
            have hTotNat : (rem64 <<< sc.sh).toNat = rem64.toNat * 2 ^ sc.sh := by
              rw [hTotEq, BitVec.toNat_ofNat]
              have : sc.sh = 0 ∨ sc.sh = 1 ∨ sc.sh = 2 ∨ sc.sh = 3 := by have := sc.hShLe; omega
              rcases this with h | h | h | h <;> simp [h] <;> omega
            have hLeHi : lo.toNat ≤ hi.toNat := by
              dsimp only [cNoWrap, CmpOp.evalBits] at hNoWrapTrue
              exact of_decide_eq_true (by unfold BitVec.ule at hNoWrapTrue; exact hNoWrapTrue)
            have hNoWrapNat : lo.toNat + rem64.toNat * 2 ^ sc.sh < 2 ^ 64 := by
              have hSum := BitVec.toNat_add lo (rem64 <<< sc.sh)
              change hi.toNat = (lo.toNat + (rem64 <<< sc.sh).toNat) % 2 ^ 64 at hSum
              rw [hTotNat] at hSum
              have : sc.sh = 0 ∨ sc.sh = 1 ∨ sc.sh = 2 ∨ sc.sh = 3 := by have := sc.hShLe; omega
              have hTotLt : rem64.toNat * 2 ^ sc.sh < 2 ^ 63 := by
                rcases this with h | h | h | h <;> simp [h] <;> omega
              rcases Nat.lt_or_ge (lo.toNat + rem64.toNat * 2 ^ sc.sh) (2 ^ 64) with hLt | hGe
              · exact hLt
              · have hSub : (lo.toNat + rem64.toNat * 2 ^ sc.sh) % 2 ^ 64 =
                    lo.toNat + rem64.toNat * 2 ^ sc.sh - 2 ^ 64 := by omega
                rw [hSub] at hSum; omega
            have hLen6 : vsL6.length = vsL4.length + 2 := by simp [vsL6, vsL5]
            have hRem6 := lookupV_lvl_push2 (u1 := Ty.bool) (y1 := cNoWrap) (u2 := i64) (y2 := hi)
              (by omega) hRem4
            have hInit6 := lookupV_lvl_push2 (u1 := Ty.bool) (y1 := cNoWrap) (u2 := i64) (y2 := hi)
              (by omega) hInit4
            have hLo6 := lookupV_lvl_push2 (u1 := Ty.bool) (y1 := cNoWrap) (u2 := i64) (y2 := hi)
              (by omega) hLo4
            have hHi6 : lookupV (vsL6 ++ vsOuter) i64 (vsL6.length - 1 - vsL4.length) =
                some (lo + BitVec.ofNat 64 (rem64.toNat * 2 ^ sc.sh)) := by
              dsimp only [vsL6, vsL5]; rw [hLen6, List.cons_append, List.cons_append,
                show vsL4.length + 2 - 1 - vsL4.length = 1 by omega, ← hTotEq]; rfl
            have hEntryNew : IntervalEntry vsL6 vsOuter init64 rem64 (vsL2.length, vsL4.length)
                (sc, lo, rem64.toNat * 2 ^ sc.sh) :=
              ⟨⟨by rw [hLen6]; omega, by rw [hLen6]; omega, hNoWrapNat, hLo6, hHi6⟩, rfl, rfl⟩
            change wp Γ Q X (denote Val Cont
              (mkStreamBounds w initArg rem64Lvl init64Lvl rest (vsL4.length + 2)
                ((vsL2.length, vsL4.length) :: ivs))
              (vsL6 ++ vsOuter) (⟨[.bits w], JWide⟩ :: ⟨[.bits w], JLoop⟩ :: ls)) hm
            rw [← hLen6]
            refine mkStreamBounds_wp hdInit hm hJInit hRem60 rest restSc hRest
              ((vsL2.length, vsL4.length) :: ivs) ((sc, lo, rem64.toNat * 2 ^ sc.sh) :: done)
              vsL6 (by omega) (by omega) hRem6 hInit6
              (.cons hEntryNew (pairForall_entry_push _ (pairForall_entry_push _ hDone4))) ?_
            simpa [List.reverse_cons, List.append_assoc] using hPass
          · intro _
            rw [show (⟨Ty.bool, CmpOp.ule.evalBits lo hi⟩ :: (vsL5 ++ vsOuter)) =
              vsL6 ++ vsOuter from rfl]
            have hLen6 : vsL6.length = vsL4.length + 2 := by simp [vsL6, vsL5]
            have hInitSh : denoteArg (vsL6 ++ vsOuter) (tArgShift (vsL4.length + 2) initArg) =
                some initA := by
              rw [← hLen6]
              simpa [tArgShift] using
                (denoteArg_shiftArgAbove (vsPre := []) vsL6 vsOuter initArg).trans hdInit
            rw [denote_jump_eq, denoteArgs_singleton_eq, lookupL_1, hInitSh]
            dsimp only; rw [wp_jump]; exact hJInit
        by_cases hS0 : st.shift = 0
        · rw [ite_eq_left (by simp [hS0])]
          change wp Γ Q X (denote Val Cont _ (vsL3 ++ vsOuter) _) hm
          have hLen3 : vsL3.length = vsL2.length + 1 := by simp [vsL3]
          have hRem3' : lookupV (vsL3 ++ vsOuter) i64 (vsL2.length + 1 - 1 - rem64Lvl) =
              some rem64 := by rwa [← hLen3]
          rw [← hLen3]
          refine hAfterTot vsL3 (.var (vsL2.length + 1 - 1 - rem64Lvl)) (.var rem64) (by omega)
            (by dsimp only [denoteArg]; rw [hRem3'])
            (by dsimp only [Arg.val]; rw [hM.2.2.1, hS0, BitVec.shiftLeft_zero])
            (by dsimp only [vsL3]; rw [hLen3,
              show vsL2.length + 1 - 1 - vsL2.length = 0 by omega]; rfl)
            hRem3 hInit3 (pairForall_entry_push _ hDone2)
        · rw [ite_eq_right (beq_false_of_ne hS0 ▸ Bool.false_ne_true)]
          have hRem3' : lookupV (vsL3 ++ vsOuter) i64 (vsL2.length + 1 - 1 - rem64Lvl) =
              some rem64 := by
            have hLen3 : vsL3.length = vsL2.length + 1 := by simp [vsL3]
            rwa [← hLen3]
          change wp Γ Q X (denote Val Cont (TFlat.let_ (op2 (.shl i64)
            (.var (vsL2.length + 1 - 1 - rem64Lvl)) (.imm (BitVec.ofNat 64 st.shift))) _)
            (vsL3 ++ vsOuter) _) hm
          dsimp only [op2]; rw [denote_let_eq, denoteArgs_pair_eq]
          have hVRem : denoteArg (vsL3 ++ vsOuter)
              (.var (vsL2.length + 1 - 1 - rem64Lvl) : Arg K i64) = some (.var rem64) := by
            dsimp only [denoteArg]; rw [hRem3']
          have hImmS : denoteArg (vsL3 ++ vsOuter)
              (.imm (BitVec.ofNat 64 st.shift) : Arg K i64) =
              some (.imm (BitVec.ofNat 64 st.shift)) := rfl
          rw [hVRem, hImmS, wp_let]; dsimp only [Op.wp]
          refine liftOp_shl_args_wp (a := .var rem64) (s := BitVec.ofNat 64 st.shift) ?_
          rw [show (Arg.var rem64 : Arg Val i64).val = rem64 from rfl]
          dsimp only [pushTup]
          let vsL4 : List ((t : Ty) × Val t) :=
            ⟨i64, rem64 <<< ((BitVec.ofNat 64 st.shift).toNat % 64)⟩ :: vsL3
          have hLen4 : vsL4.length = vsL2.length + 1 + 1 := by simp [vsL4, vsL3]
          have hRem4 := lookupV_lvl_push (u := i64)
            (y := rem64 <<< ((BitVec.ofNat 64 st.shift).toNat % 64))
            (by rw [List.length_cons]; omega) hRem3
          have hInit4 := lookupV_lvl_push (u := i64)
            (y := rem64 <<< ((BitVec.ofNat 64 st.shift).toNat % 64))
            (by rw [List.length_cons]; omega) hInit3
          have hShLt : st.shift ≤ 3 := hM.2.2.1 ▸ sc.hShLe
          have hMod : (BitVec.ofNat 64 st.shift).toNat % 64 = st.shift := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          rw [← List.cons_append]
          change wp Γ Q X (denote Val Cont _ (vsL4 ++ vsOuter) _) hm
          rw [← hLen4]
          refine hAfterTot vsL4 (.var 0) (.var _) (by omega) (denoteArg_var0 _ _)
            (by change (rem64 <<< ((BitVec.ofNat 64 st.shift).toNat % 64)) = _
                rw [hMod, hM.2.2.1])
            (by dsimp only [vsL4, vsL3]; rw [hLen4,
              show vsL2.length + 1 + 1 - 1 - vsL2.length = 1 by omega]; rfl)
            hRem4 hInit4 (pairForall_entry_push _ (pairForall_entry_push _ hDone2))
      by_cases hS0 : st.shift = 0
      · rw [ite_eq_left (by simp [hS0])]
        exact withScaled vsL1 idxVar idxA hLen1 hdIdx
          (by rw [hIdxVal, hM.2.2.1, hS0, BitVec.shiftLeft_zero]) hRem1 hInit1 hDone1
      · rw [ite_eq_right (beq_false_of_ne hS0 ▸ Bool.false_ne_true)]
        dsimp only [op2]; rw [denote_let_eq, denoteArgs_pair_eq, hdIdx]
        have hImmS : denoteArg (vsL1 ++ vsOuter)
            (.imm (BitVec.ofNat 64 st.shift) : Arg K i64) =
            some (.imm (BitVec.ofNat 64 st.shift)) := rfl
        rw [hImmS, wp_let]; dsimp only [Op.wp]
        refine liftOp_shl_args_wp (a := idxA) (s := BitVec.ofNat 64 st.shift) ?_
        dsimp only [pushTup]
        have hShLt : st.shift ≤ 3 := hM.2.2.1 ▸ sc.hShLe
        have hMod : (BitVec.ofNat 64 st.shift).toNat % 64 = st.shift := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        let vsL1' : List ((t : Ty) × Val t) :=
          ⟨i64, idxA.val <<< ((BitVec.ofNat 64 st.shift).toNat % 64)⟩ :: vsL1
        have hLen1' : vsL1'.length = vsL1.length + 1 := by simp [vsL1']
        have hRem1' := lookupV_lvl_push (u := i64)
          (y := idxA.val <<< ((BitVec.ofNat 64 st.shift).toNat % 64)) (by omega) hRem1
        have hInit1' := lookupV_lvl_push (u := i64)
          (y := idxA.val <<< ((BitVec.ofNat 64 st.shift).toNat % 64)) (by omega) hInit1
        rw [← List.cons_append]
        change wp Γ Q X (denote Val Cont _ (vsL1' ++ vsOuter) _) hm
        rw [← hLen1']
        exact withScaled vsL1' (.var 0) (.var _) (by omega) (denoteArg_var0 _ _)
          (by change idxA.val <<< ((BitVec.ofNat 64 st.shift).toNat % 64) = _
              rw [hIdxVal, hMod, hM.2.2.1])
          hRem1' hInit1' (pairForall_entry_push _ hDone1)
    dsimp only [mkStreamBounds]
    cases hOff : st.off? with
    | none =>
      have hO : sc.oVal = 0#64 := by
        have hm2 := hM.2.1; dsimp only [offVal] at hm2; rw [hOff] at hm2
        exact (Option.some.inj hm2).symm
      have hVInit : denoteArg (vsLocal ++ vsOuter)
          (.var (vsLocal.length - 1 - init64Lvl) : Arg K i64) = some (.var init64) := by
        dsimp only [denoteArg]; rw [hInitV]
      exact withIdx vsLocal (.var (vsLocal.length - 1 - init64Lvl)) (.var init64) (Nat.le_refl _)
        hVInit (by dsimp only [Arg.val]; rw [hO, BitVec.add_zero]) hRemV hInitV hDone
    | some off =>
      have hOffArg : ∃ aOff : Arg Val i64, denoteArg vsOuter off = some aOff ∧
          aOff.val = sc.oVal := by
        have hm2 := hM.2.1; dsimp only [offVal] at hm2; rw [hOff] at hm2
        exact Option.map_eq_some_iff.mp hm2
      obtain ⟨aOff, hdOffA, haOffVal⟩ := hOffArg
      dsimp only [op2]; rw [denote_let_eq, denoteArgs_pair_eq]
      have hVInit : denoteArg (vsLocal ++ vsOuter)
          (.var (vsLocal.length - 1 - init64Lvl) : Arg K i64) = some (.var init64) := by
        dsimp only [denoteArg]; rw [hInitV]
      have hOffSh : denoteArg (vsLocal ++ vsOuter) (tArgShift vsLocal.length off) = some aOff := by
        simpa [tArgShift] using (denoteArg_shiftArgAbove (vsPre := []) vsLocal vsOuter off).trans
          hdOffA
      rw [hVInit, hOffSh, wp_let]; dsimp only [Op.wp]
      refine liftOp_add_args_wp (a := .var init64) (b := aOff) ?_
      dsimp only [pushTup]; rw [haOffVal]; dsimp only [Arg.val]
      let vsL1 := ⟨i64, init64 + sc.oVal⟩ :: vsLocal
      have hLen1 : vsL1.length = vsLocal.length + 1 := by simp [vsL1]
      have hRem1 := lookupV_lvl_push (u := i64) (y := init64 + sc.oVal) hRemLt hRemV
      have hInit1 := lookupV_lvl_push (u := i64) (y := init64 + sc.oVal) hInitLt hInitV
      rw [← List.cons_append]
      change wp Γ Q X (denote Val Cont _ (vsL1 ++ vsOuter) _) hm
      rw [← hLen1]
      exact withIdx vsL1 (.var 0) (.var _) (Nat.le_succ _) (denoteArg_var0 _ _) rfl hRem1 hInit1
        (pairForall_entry_push _ hDone)

private theorem mkDisjointCheck_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {w stepK : Nat} (hw : w = 32 ∨ w = 64) (_hStepPos : 1 ≤ stepK) (_hStep512 : stepK ≤ 512)
    (isLt : Bool) {initArg bound : Arg K (.bits w)} {initA bndA : Arg Val (.bits w)}
    {vsOuter : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {stores : List StoreSpec} {ss : List ScalarStream}
    (hF2 : PairForall (StreamMatchesSpec vsOuter) ss stores)
    (hdInit : denoteArg vsOuter initArg = some initA)
    (hdBnd : denoteArg vsOuter bound = some bndA)
    {JWide JLoop : Cont [.bits w]} (hm : Mem 64) (hJInit : JLoop (initA.val, ()) hm)
    (hPass : initA.val.toNat ≤ bndA.val.toNat →
      ss.Pairwise (fun a b => ByteDisj (a.ptr (bv64OfW initA.val))
        ((bndA.val.toNat - initA.val.toNat) * a.tAtom.bytes)
        (b.ptr (bv64OfW initA.val))
        ((bndA.val.toNat - initA.val.toNat) * b.tAtom.bytes)) →
      JWide (initA.val, ()) hm) :
    wp Γ Q X (denote Val Cont (mkDisjointCheck w isLt initArg bound stores stepK)
      vsOuter (⟨[.bits w], JWide⟩ :: ⟨[.bits w], JLoop⟩ :: ls)) hm := by
  dsimp only [mkDisjointCheck, op2]
  rw [denote_let_eq, denoteArgs_pair_eq, hdInit, hdBnd, wp_let]; dsimp only [Op.wp]
  refine liftOp_cmp_args_wp hw (o := if isLt then .ult else .ule) (a := initA) (b := bndA) ?_
  let cInit := (if isLt then CmpOp.ult else CmpOp.ule).evalBits initA.val bndA.val
  rw [pushTup_singleton (t := Ty.bool), denote_jnz_eq, denoteArg_var0]
  dsimp only; rw [wp_jnz, show (Arg.var cInit : Arg Val Ty.bool).val = cInit from rfl]
  have hInitSh1 : denoteArg (⟨Ty.bool, cInit⟩ :: vsOuter) (tArgShift 1 initArg) = some initA := by
    simpa [tArgShift] using (denoteArg_shiftArgAbove (vsPre := []) [⟨Ty.bool, cInit⟩] vsOuter
      initArg).trans hdInit
  constructor
  · intro hcInitTrue
    have hInitLe : initA.val.toNat ≤ bndA.val.toNat := by
      dsimp only [cInit] at hcInitTrue
      cases isLt <;> dsimp only [CmpOp.evalBits] at hcInitTrue
      · exact of_decide_eq_true (by unfold BitVec.ule at hcInitTrue; exact hcInitTrue)
      · exact Nat.le_of_lt
          (of_decide_eq_true (by unfold BitVec.ult at hcInitTrue; exact hcInitTrue))
    have hBndSh1 : denoteArg (⟨Ty.bool, cInit⟩ :: vsOuter) (tArgShift 1 bound) = some bndA := by
      simpa [tArgShift] using (denoteArg_shiftArgAbove (vsPre := []) [⟨Ty.bool, cInit⟩] vsOuter
        bound).trans hdBnd
    rw [denote_let_eq, denoteArgs_pair_eq, hBndSh1, hInitSh1, wp_let]; dsimp only [Op.wp]
    refine liftOp_sub_args_wp hw (a := bndA) (b := initA) ?_
    let rem := bndA.val - initA.val
    let vs2 : List ((t : Ty) × Val t) := [⟨.bits w, rem⟩, ⟨Ty.bool, cInit⟩]
    rw [pushTup_singleton (t := .bits w)]
    change wp Γ Q X (denote Val Cont
      (.let_ (op2 (.cmp .uge (.bits w) .bool rfl) (.var 0) (.imm (BitVec.ofNat w stepK))) _)
      (vs2 ++ vsOuter) _) hm
    dsimp only [op2]; rw [denote_let_eq, denoteArgs_pair_eq]
    have hV0_2 : denoteArg (vs2 ++ vsOuter) (.var 0 : Arg K (.bits w)) = some (.var rem) := by
      dsimp only [vs2, List.cons_append, List.nil_append, denoteArg, lookupV, listGet?]
      rw [PassFlatKit.castTy_self]
    have hImmK : denoteArg (vs2 ++ vsOuter) (.imm (BitVec.ofNat w stepK) : Arg K (.bits w)) =
        some (.imm (BitVec.ofNat w stepK)) := rfl
    rw [hV0_2, hImmK, wp_let]; dsimp only [Op.wp]
    refine liftOp_cmp_args_wp hw (o := .uge) (a := (.var rem : Arg Val (.bits w)))
      (b := (.imm (BitVec.ofNat w stepK) : Arg Val (.bits w))) ?_
    rw [show (Arg.var rem : Arg Val (.bits w)).val = rem from rfl,
      show (Arg.imm (BitVec.ofNat w stepK) : Arg Val (.bits w)).val =
        BitVec.ofNat w stepK from rfl]
    let cStep := CmpOp.uge.evalBits rem (BitVec.ofNat w stepK)
    let vs3 : List ((t : Ty) × Val t) := ⟨Ty.bool, cStep⟩ :: vs2
    rw [pushTup_singleton (t := Ty.bool), denote_jnz_eq, denoteArg_var0]
    dsimp only; rw [wp_jnz, show (Arg.var cStep : Arg Val Ty.bool).val = cStep from rfl]
    have hInitSh3 : denoteArg (vs3 ++ vsOuter) (tArgShift 3 initArg) = some initA := by
      simpa [vs3, vs2, tArgShift] using (denoteArg_shiftArgAbove (vsPre := []) vs3 vsOuter
        initArg).trans hdInit
    have hVs3Eq : (⟨Ty.bool, CmpOp.uge.evalBits rem (BitVec.ofNat w stepK)⟩ :: (vs2 ++ vsOuter)) =
        vs3 ++ vsOuter := rfl
    constructor
    · intro _
      rw [hVs3Eq]
      rcases hw with rfl | rfl
      · rw [dite_eq_left rfl]; dsimp only [op1]
        rw [denote_let_eq, denoteArgs_singleton_eq]
        have hV1 : denoteArg (vs3 ++ vsOuter) (.var 1 : Arg K i32) = some (.var rem) := rfl
        rw [hV1, wp_let]; dsimp only [Op.wp]
        refine liftOp_zext32_wp (a := .var rem) ?_
        rw [show (Arg.var rem : Arg Val i32).val = rem from rfl]
        let vs4 : List ((t : Ty) × Val t) := ⟨i64, rem.setWidth 64⟩ :: vs3
        have hInitSh4 : denoteArg (vs4 ++ vsOuter) (tArgShift 4 initArg) = some initA := by
          simpa [vs4, vs3, vs2, tArgShift] using
            (denoteArg_shiftArgAbove (vsPre := []) vs4 vsOuter initArg).trans hdInit
        rw [pushTup_singleton (t := i64), denote_let_eq, denoteArgs_singleton_eq]
        rw [show (⟨i64, rem.setWidth 64⟩ :: (vs3 ++ vsOuter)) = vs4 ++ vsOuter from rfl, hInitSh4,
          wp_let]; dsimp only [Op.wp]
        refine liftOp_zext32_wp (a := initA) ?_
        let vs5 : List ((t : Ty) × Val t) := ⟨i64, initA.val.setWidth 64⟩ :: vs4
        have hRem64Nat : (rem.setWidth 64).toNat = bndA.val.toNat - initA.val.toNat := by
          rw [BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (Nat.lt_trans rem.isLt (by decide : 2 ^ 32 < 2 ^ 64))]
          exact BitVec.toNat_sub_of_le (BitVec.le_def.mpr hInitLe)
        have hRem60 : (rem.setWidth 64).toNat < 2 ^ 60 := by rw [hRem64Nat]; omega
        rw [pushTup_singleton (t := i64), ← List.cons_append]
        change wp Γ Q X (denote Val Cont (mkStreamBounds 32 initArg 3 4 stores 5 [])
          (vs5 ++ vsOuter) (⟨[i32], JWide⟩ :: ⟨[i32], JLoop⟩ :: ls)) hm
        have hLen5 : vs5.length = 5 := rfl
        rw [← hLen5]
        refine mkStreamBounds_wp hdInit hm hJInit hRem60 stores ss hF2 [] [] vs5 (by omega)
          (by omega) rfl rfl .nil ?_
        intro _ hPair
        simp only [List.reverse_nil, List.map_nil, List.nil_append, hRem64Nat] at hPair
        exact hPass hInitLe hPair
      · rw [dite_eq_right (by decide), dite_eq_left rfl]
        dsimp only [op2]; rw [denote_let_eq, denoteArgs_pair_eq]
        have hV1 : denoteArg (vs3 ++ vsOuter) (.var 1 : Arg K i64) = some (.var rem) := rfl
        have hImm60 : denoteArg (vs3 ++ vsOuter)
            (.imm (BitVec.ofNat 64 (2 ^ 60 - 1)) : Arg K i64) =
            some (.imm (BitVec.ofNat 64 (2 ^ 60 - 1))) := rfl
        rw [hV1, hImm60, wp_let]; dsimp only [Op.wp]
        refine liftOp_cmp_args_wp (Or.inr rfl) (o := .ule) (a := .var rem)
          (b := .imm (BitVec.ofNat 64 (2 ^ 60 - 1))) ?_
        rw [show (Arg.var rem : Arg Val i64).val = rem from rfl,
          show (Arg.imm (BitVec.ofNat 64 (2 ^ 60 - 1)) : Arg Val i64).val =
            BitVec.ofNat 64 (2 ^ 60 - 1) from rfl]
        let c60 := CmpOp.ule.evalBits rem (BitVec.ofNat 64 (2 ^ 60 - 1))
        let vs4 := ⟨Ty.bool, c60⟩ :: vs3
        rw [pushTup_singleton (t := Ty.bool), denote_jnz_eq, denoteArg_var0]
        dsimp only; rw [wp_jnz, show (Arg.var c60 : Arg Val Ty.bool).val = c60 from rfl]
        have hInitSh4 : denoteArg (vs4 ++ vsOuter) (tArgShift 4 initArg) = some initA := by
          simpa [vs4, vs3, vs2, tArgShift] using (denoteArg_shiftArgAbove (vsPre := []) vs4 vsOuter
            initArg).trans hdInit
        have hVs4Eq : (⟨Ty.bool, CmpOp.ule.evalBits rem (BitVec.ofNat 64 (2 ^ 60 - 1))⟩ ::
            (vs3 ++ vsOuter)) = vs4 ++ vsOuter := rfl
        constructor
        · intro hc60True
          rw [hVs4Eq]
          have hRem64Nat : rem.toNat = bndA.val.toNat - initA.val.toNat :=
            BitVec.toNat_sub_of_le (BitVec.le_def.mpr hInitLe)
          have hRem60 : rem.toNat < 2 ^ 60 := by
            dsimp only [c60, CmpOp.evalBits] at hc60True
            have hle : rem.toNat ≤ (BitVec.ofNat 64 (2 ^ 60 - 1)).toNat :=
              of_decide_eq_true (by unfold BitVec.ule at hc60True; exact hc60True)
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)] at hle; omega
          dsimp only [op1]
          rw [denote_let_eq, denoteArgs_singleton_eq, hInitSh4, wp_let]; dsimp only [Op.wp]
          refine liftOp_copy64_wp (a := initA) ?_
          let vs5 := ⟨i64, initA.val⟩ :: vs4
          rw [pushTup_singleton (t := i64), ← List.cons_append]
          change wp Γ Q X (denote Val Cont (mkStreamBounds 64 initArg 1 4 stores 5 [])
            (vs5 ++ vsOuter) (⟨[i64], JWide⟩ :: ⟨[i64], JLoop⟩ :: ls)) hm
          have hLen5 : vs5.length = 5 := rfl
          rw [← hLen5]
          refine mkStreamBounds_wp hdInit hm hJInit hRem60 stores ss hF2 [] [] vs5 (by omega)
            (by omega) rfl rfl .nil ?_
          intro _ hPair
          simp only [List.reverse_nil, List.map_nil, List.nil_append, hRem64Nat] at hPair
          exact hPass hInitLe (by rw [bv64OfW_64_eq]; exact hPair)
        · intro _
          rw [hVs4Eq, denote_jump_eq, denoteArgs_singleton_eq, lookupL_1, hInitSh4]
          dsimp only; rw [wp_jump]; exact hJInit
    · intro _
      rw [hVs3Eq, denote_jump_eq, denoteArgs_singleton_eq, lookupL_1, hInitSh3]
      dsimp only; rw [wp_jump]; exact hJInit
  · intro _
    rw [denote_jump_eq, denoteArgs_singleton_eq, lookupL_1, hInitSh1]
    dsimp only; rw [wp_jump]; exact hJInit

public theorem widenFillExt_loop_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {w unrollN : Nat} (hwEq : w = 32 ∨ w = 64) (_hu1 : 1 ≤ unrollN) (_hu64 : unrollN ≤ 64)
    {isLt : Bool} {initArg bnd : Arg K (.bits w)} {stores : List StoreSpec}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {initA bndA : Arg Val (.bits w)} {ss : List ScalarStream} {m : Mem 64}
    (hdInit : denoteArg vs initArg = some initA) (hdBnd : denoteArg vs bnd = some bndA)
    (hLen1 : 1 ≤ stores.length)
    (hStep : 1 ≤ computeMultiStepK unrollN stores ∧ computeMultiStepK unrollN stores ≤ 512 ∧
      ∀ s ∈ stores, 1 ≤ computeMultiStepK unrollN stores / (8 >>> s.shift) ∧
        computeMultiStepK unrollN stores / (8 >>> s.shift) ≤ 64 ∧
        (computeMultiStepK unrollN stores / (8 >>> s.shift)) * (8 >>> s.shift) =
          computeMultiStepK unrollN stores)
    (hF2 : PairForall (StreamMatchesSpec vs) ss stores)
    {JLoop : Cont [.bits w]}
    (hJInit : JLoop (initA.val, ()) m)
    (hStepScal : ∀ (i' : BitVec w) (m' : Mem 64),
      i'.toNat < bndA.val.toNat → JLoop (i', ()) m' →
      ScalarChainOk m' (bv64OfW i') ss ∧
      JLoop (i' + BitVec.ofNat w 1, ()) (applyScalarChain m' (bv64OfW i') ss))
    {wb : TFlat rs} (hWb : wb = mkMultiWideBody (rs := rs) w bnd stores
      (computeMultiStepK unrollN stores)) :
    let stepK := computeMultiStepK unrollN stores
    let kCheck : TFlat rs := if stores.length ≤ 1 then
        .let_ (op2 (.cmp (if isLt then .ult else .ule) (.bits w) .bool rfl) initArg bnd)
          (.jnz (.var 0) (.jump (ts := [.bits w]) 0 (tArgShift 1 initArg, ()))
            (.jump (ts := [.bits w]) 1 (tArgShift 1 initArg, ())))
      else mkDisjointCheck (rs := rs) w isLt initArg bnd stores stepK
    wp Γ Q X (Expr.group (sig := [[.bits w]])
      (fun Js => denoteB Val Cont (.cons (ts := [.bits w]) wb .nil) vs
        (pushTup Js (⟨[.bits w], JLoop⟩ :: ls)))
      (fun Js => denote Val Cont kCheck vs (pushTup Js (⟨[.bits w], JLoop⟩ :: ls)))) m := by
  subst hWb
  let stepK := computeMultiStepK unrollN stores
  let wb := mkMultiWideBody (rs := rs) w bnd stores stepK
  let kCheck := if stores.length ≤ 1 then
      TFlat.let_ (op2 (.cmp (if isLt then .ult else .ule) (.bits w) .bool rfl) initArg bnd)
        (.jnz (.var 0) (.jump (ts := [.bits w]) 0 (tArgShift 1 initArg, ()))
          (.jump (ts := [.bits w]) 1 (tArgShift 1 initArg, ())))
    else mkDisjointCheck (rs := rs) w isLt initArg bnd stores stepK
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
  dsimp only [wb, kCheck, stepK] at hEqGroup ⊢; rw [hEqGroup]
  let DisjInv : Prop := stores.length ≤ 1 ∨
    ss.Pairwise (fun a b => ByteDisj (a.ptr (bv64OfW initA.val))
      ((bndA.val.toNat - initA.val.toNat) * a.tAtom.bytes)
      (b.ptr (bv64OfW initA.val))
      ((bndA.val.toNat - initA.val.toNat) * b.tAtom.bytes))
  have mkInvDisj : DisjInv → ∀ (i' : BitVec w), initA.val.toNat ≤ i'.toNat →
      i'.toNat + stepK ≤ bndA.val.toNat →
      ss.Pairwise (fun a b => ByteDisj (a.ptr (bv64OfW i')) (stepK * a.tAtom.bytes)
        (b.ptr (bv64OfW i')) (stepK * b.tAtom.bytes)) := by
    intro hDI i' hInitLe hSumLe
    rcases hDI with hLe1 | hDisj
    · have hSsLen : ss.length ≤ 1 := by
        clear hStepScal hJInit; induction hF2 with
        | nil => simp
        | cons _ h _ => simp at hLe1 ⊢; cases h with | nil => simp | cons _ _ => simp at hLe1
      cases ss with
      | nil => exact .nil
      | cons x xs =>
        cases xs with | nil => exact List.pairwise_singleton _ _ | cons _ _ => simp at hSsLen
    · let done := i'.toNat - initA.val.toNat
      have hIEq : i' = initA.val + BitVec.ofNat w done := by
        apply BitVec.eq_of_toNat_eq
        have hltW : done < 2 ^ w := Nat.lt_of_le_of_lt (by omega) bndA.val.isLt
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hltW,
          Nat.mod_eq_of_lt (by have := bndA.val.isLt; omega)]
        omega
      have hL64 : bv64OfW i' = bv64OfW initA.val + BitVec.ofNat 64 done := by
        rw [hIEq]; exact bvW_setWidth64_add hwEq initA.val bndA.val done (by omega)
      refine hDisj.imp (fun {a b} hAB => ?_)
      rw [hL64, scalarStream_ptr_add, scalarStream_ptr_add]
      exact byteDisj_sub hAB
        (by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega))
        (by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega))
  by_cases hS1 : stores.length ≤ 1
  · let Inv : Nat → Tup Val [.bits w] → Mem 64 → Prop := fun n xs m' =>
      initA.val.toNat ≤ xs.fst.toNat ∧ xs.fst.toNat ≤ bndA.val.toNat ∧
      n = bndA.val.toNat - xs.fst.toNat ∧ JLoop xs m'
    refine wp_loop
      (fun JWide xs => denote Val Cont wb (pushTup xs vs)
        (⟨[.bits w], JWide⟩ :: ⟨[.bits w], JLoop⟩ :: ls))
      (fun JWide => denote Val Cont kCheck vs
        (⟨[.bits w], JWide⟩ :: ⟨[.bits w], JLoop⟩ :: ls)) Inv ?_ ?_
    · exact mkMultiWideBody_iter_wp hwEq hStep.1 hStep.2.1 hdBnd hF2
        hStep.2.2 hStepScal (mkInvDisj (Or.inl hS1))
    · intro JWide hInv
      dsimp only [kCheck]; rw [ite_eq_left (by simp [hS1])]
      dsimp only [op2]; rw [denote_let_eq, denoteArgs_pair_eq, hdInit, hdBnd, wp_let]
      dsimp only [Op.wp]
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
        exact hInv (bndA.val.toNat - initA.val.toNat) (initA.val, ()) m
          ⟨Nat.le_refl _, hLe, rfl, hJInit⟩
      · intro _
        rw [denote_jump_eq, denoteArgs_singleton_eq, lookupL_1, hInitSh1]
        dsimp only; rw [wp_jump]; exact hJInit
  · let Inv : Nat → Tup Val [.bits w] → Mem 64 → Prop := fun n xs m' =>
      DisjInv ∧ initA.val.toNat ≤ xs.fst.toNat ∧ xs.fst.toNat ≤ bndA.val.toNat ∧
      n = bndA.val.toNat - xs.fst.toNat ∧ JLoop xs m'
    refine wp_loop
      (fun JWide xs => denote Val Cont wb (pushTup xs vs)
        (⟨[.bits w], JWide⟩ :: ⟨[.bits w], JLoop⟩ :: ls))
      (fun JWide => denote Val Cont kCheck vs
        (⟨[.bits w], JWide⟩ :: ⟨[.bits w], JLoop⟩ :: ls)) Inv ?_ ?_
    · intro JWide n xs m' ih ⟨hDI, hInitLe, hLe, hn, hJL⟩
      exact mkMultiWideBody_iter_wp hwEq hStep.1 hStep.2.1 hdBnd hF2 hStep.2.2
        hStepScal (mkInvDisj hDI) JWide n xs m'
        (fun n' xs' m'' hlt hInv' => ih n' xs' m'' hlt ⟨hDI, hInv'⟩)
        ⟨hInitLe, hLe, hn, hJL⟩
    · intro JWide hInv
      dsimp only [kCheck]; rw [ite_eq_right (by simp [hS1])]
      refine mkDisjointCheck_wp hwEq hStep.1 hStep.2.1 isLt hF2 hdInit hdBnd m hJInit ?_
      intro hLe hDisj
      exact hInv (bndA.val.toNat - initA.val.toNat) (initA.val, ()) m
        ⟨Or.inr hDisj, Nat.le_refl _, hLe, rfl, hJInit⟩

end ZeroPeel

end LeanQbe.T
