module

public import LeanQbe.T.ZeroPeel
public import LeanQbe.T.ZeroPeelLemmas1
public import LeanQbe.T.Wf
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.GroupLfpLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.PassFlatKit
import all Kraken.Mem

/-!
# Helper Lemmas for `LeanQbe.T.ZeroPeel` (Part 2: `u32` & Multi-Store Fill Widening)

Proves `SymExt` well-scopedness & relational evaluation, `matchMultiFillBody_{wf,spec}`,
`mkSeqStores_{wf,wp,callsOk}`, `emitWideStreams_{wf,wp,callsOk}`, `storeBytes_comm_disjoint`,
`runMultiScalarMem_step`, `mkDisjointCheck_{wf,wp,callsOk}`, and
`wfCheck_widenFillExt` / `widenFillExt_wp` / `widenFillExt_callsOk`.
-/

set_option autoImplicit false

namespace LeanQbe.T

open Std Std.ExtHashMap

namespace ZeroPeel

/-! ## Section 1: `SymExt` Well-Scopedness & `matchMultiFillBody_wf` -/

@[expose] public def SymExtOuterOk (GOuter : List Ty) : SymExt → Prop
  | .loopI | .loopZext64 | .const64 _ | .const32 _ | .other => True
  | .outer64 idx0 => checkArg GOuter i64 (.var idx0) = true
  | .outer32 idx0 => checkArg GOuter i32 (.var idx0) = true
  | .add64 a b | .add32 a b => SymExtOuterOk GOuter a ∧ SymExtOuterOk GOuter b
  | .shlConst64 a _ => SymExtOuterOk GOuter a
  | .cmpU64 _ bnd => checkArg GOuter i64 bnd = true
  | .cmpU32 _ bnd => checkArg GOuter i32 bnd = true

@[expose] public def SymExtEnvWf (GOuter GLocal : List Ty) (env : Array SymExt) : Prop :=
  env.size = GLocal.length ∧ ∀ s ∈ env.toList, SymExtOuterOk GOuter s

private theorem symToOuterArg64Ext_wf {GOuter : List Ty} {s : SymExt} {a : Arg K i64}
    (hs : SymExtOuterOk GOuter s) (hm : symToOuterArg64Ext s = some a) :
    checkArg GOuter i64 a = true := by
  cases s <;> dsimp only [symToOuterArg64Ext] at hm <;> cases hm <;> first | exact hs | rfl

private theorem symToOuterArg32_wf {GOuter : List Ty} {s : SymExt} {a : Arg K i32}
    (hs : SymExtOuterOk GOuter s) (hm : symToOuterArg32 s = some a) :
    checkArg GOuter i32 a = true := by
  cases s <;> dsimp only [symToOuterArg32] at hm <;> cases hm <;> first | exact hs | rfl

private theorem matchOffLoopExt_wf {GOuter : List Ty} {is32 : Bool} {s : SymExt}
    {off? : Option (Arg K i64)} (hs : SymExtOuterOk GOuter s)
    (hm : matchOffLoopExt is32 s = some off?) :
    off?.all (checkArg GOuter i64) = true := by
  cases s with
  | add64 a b =>
    dsimp only [SymExtOuterOk] at hs; dsimp only [matchOffLoopExt] at hm
    split at hm
    · rcases Option.map_eq_some_iff.mp hm with ⟨arg, harg, rfl⟩
      rw [Option.all_some]; exact symToOuterArg64Ext_wf hs.2 harg
    · split at hm
      · rcases Option.map_eq_some_iff.mp hm with ⟨arg, harg, rfl⟩
        rw [Option.all_some]; exact symToOuterArg64Ext_wf hs.1 harg
      · cases hm
  | _ =>
    dsimp only [matchOffLoopExt] at hm
    split at hm <;> cases hm; rfl

public theorem matchAddrExt_wf {GOuter : List Ty} {is32 : Bool} {s : SymExt} {sh : Nat}
    {res : Arg K i64 × Option (Arg K i64)} (hs : SymExtOuterOk GOuter s)
    (hm : matchAddrExt is32 sh s = some res) :
    checkArg GOuter i64 res.1 = true ∧ res.2.all (checkArg GOuter i64) = true := by
  cases s with
  | add64 x y =>
    dsimp only [SymExtOuterOk] at hs; dsimp only [matchAddrExt] at hm
    let chk (p idx : SymExt) : Option (Arg K i64 × Option (Arg K i64)) :=
      match symToOuterArg64Ext p with
      | some base =>
        if (sh == 0) = true then Option.map (base, ·) (matchOffLoopExt is32 idx)
        else match idx with
          | .shlConst64 inner s =>
            if (s == sh) = true then Option.map (base, ·) (matchOffLoopExt is32 inner) else none
          | _ => none
      | none => none
    have check_wf : ∀ p idx : SymExt, SymExtOuterOk GOuter p → SymExtOuterOk GOuter idx →
        chk p idx = some res →
        checkArg GOuter i64 res.1 = true ∧ res.2.all (checkArg GOuter i64) = true := by
      intro p idx hp hidx hc; dsimp only [chk] at hc
      cases hso : symToOuterArg64Ext p with
      | none => simp [hso] at hc
      | some base =>
        rw [hso] at hc; dsimp only at hc; have hb := symToOuterArg64Ext_wf hp hso
        by_cases hsh : (sh == 0) = true
        · rw [ite_eq_left hsh] at hc
          rcases Option.map_eq_some_iff.mp hc with ⟨off?, hoff, rfl⟩
          exact ⟨hb, matchOffLoopExt_wf hidx hoff⟩
        · rw [ite_eq_right hsh] at hc
          cases idx with
          | shlConst64 inner s =>
            dsimp only [SymExtOuterOk] at hidx
            dsimp only at hc; by_cases hsEq : (s == sh) = true
            · rw [ite_eq_left hsEq] at hc
              rcases Option.map_eq_some_iff.mp hc with ⟨off?, hoff, rfl⟩
              exact ⟨hb, matchOffLoopExt_wf hidx hoff⟩
            · rw [ite_eq_right hsEq] at hc; cases hc
          | _ => cases hc
    change (match chk x y with | some r => some r | none => chk y x) = some res at hm
    cases hc1 : chk x y with
    | some r => rw [hc1] at hm; cases hm; exact check_wf x y hs.1 hs.2 hc1
    | none => rw [hc1] at hm; exact check_wf y x hs.2 hs.1 hm
  | _ => dsimp only [matchAddrExt] at hm; cases hm

public theorem argToSym_var (is32 : Bool) (env : Array SymExt) {t : Ty} (idx : K t) :
    argToSym is32 env (.var idx) =
      if idx < env.size then env[env.size - 1 - idx]!
      else if idx == env.size then
        if (is32 && t == i32) || (!is32 && t == i64) then .loopI else .other
      else if t == i64 then .outer64 (idx - (env.size + 1))
      else if t == i32 then .outer32 (idx - (env.size + 1))
      else .other := by
  dsimp only [argToSym]; split <;> try (next h => cases h)
  next h => cases h; rfl

public theorem argToSym_wf {GOuter GLocal : List Ty} {is32 : Bool} {env : Array SymExt}
    (hwf : SymExtEnvWf GOuter GLocal env) {t : Ty} {a : Arg K t}
    (ha : checkArg (GLocal ++ (if is32 then i32 else i64) :: GOuter) t a = true) :
    SymExtOuterOk GOuter (argToSym is32 env a) := by
  cases a with
  | imm _ => dsimp only [argToSym]; split <;> trivial
  | var idx =>
    rw [argToSym_var]; split
    · next hlt =>
      dsimp only [K] at hlt idx
      have hidx : env.size - 1 - idx < env.size := by omega
      rw [getElem!_pos env (env.size - 1 - idx) hidx]
      exact hwf.2 _ (Array.getElem_mem_toList hidx)
    · next hge =>
      dsimp only [K] at hge idx; split
      · split <;> exact trivial
      · next hne =>
        have hlen := hwf.1; dsimp only [K] at *; simp only [beq_iff_eq] at hne
        have hge' : GLocal.length ≤ idx := by omega
        have hDrop := listGet?_append_drop GLocal ((if is32 then i32 else i64) :: GOuter)
          idx hge'
        rw [show idx - GLocal.length = (idx - (GLocal.length + 1)) + 1 by omega] at hDrop
        split
        · next ht =>
          rw [beq_iff_eq] at ht; subst ht
          simp only [checkArg, hDrop, listGet?_cons_succ_eq] at ha
          rw [show idx - (env.size + 1) = idx - (GLocal.length + 1) by omega]; exact ha
        · split
          · next ht =>
            rw [beq_iff_eq] at ht; subst ht
            simp only [checkArg, hDrop, listGet?_cons_succ_eq] at ha
            rw [show idx - (env.size + 1) = idx - (GLocal.length + 1) by omega]; exact ha
          · exact trivial

public theorem symExtEnvWf_push {GOuter GLocal : List Ty} {env : Array SymExt}
    (hwf : SymExtEnvWf GOuter GLocal env) (ts : List Ty) (sy : List SymExt)
    (hlen : sy.length = ts.length) (hok : ∀ s ∈ sy, SymExtOuterOk GOuter s) :
    SymExtEnvWf GOuter (pushTypes ts GLocal) (env ++ sy.toArray) := by
  refine ⟨by rw [Array.size_append, hwf.1, List.size_toArray, hlen, pushTypes_length,
    Nat.add_comm], fun s hs => ?_⟩
  rw [Array.toList_append, List.toList_toArray, List.mem_append] at hs
  exact hs.elim (hwf.2 s) (hok s)

public theorem evalSymOpExt_len (is32 : Bool) (env : Array SymExt) {ts : List Ty}
    (op : Op K ts) : (evalSymOpExt is32 env op).length = ts.length := by
  dsimp only [evalSymOpExt]
  cases evalSymOp1Ext is32 env op <;> cases ts with
  | nil => rfl
  | cons _ ts' => cases ts' <;> simp only [List.length_map] <;> rfl

private theorem symExtOuterOk_cmpU64 {GOuter : List Ty} (isLt : Bool) {s : SymExt}
    (hs : SymExtOuterOk GOuter s) :
    SymExtOuterOk GOuter
      ((Option.map (SymExt.cmpU64 isLt) (symToOuterArg64Ext s)).getD .other) := by
  cases hso : symToOuterArg64Ext s with
  | none => exact trivial
  | some _ => exact symToOuterArg64Ext_wf hs hso

private theorem symExtOuterOk_cmpU32 {GOuter : List Ty} (isLt : Bool) {s : SymExt}
    (hs : SymExtOuterOk GOuter s) :
    SymExtOuterOk GOuter
      ((Option.map (SymExt.cmpU32 isLt) (symToOuterArg32 s)).getD .other) := by
  cases hso : symToOuterArg32 s with
  | none => exact trivial
  | some _ => exact symToOuterArg32_wf hs hso

public theorem evalSymOpExt_wf {GOuter GLocal : List Ty} {is32 : Bool} {env : Array SymExt}
    (hwf : SymExtEnvWf GOuter GLocal env) {ts : List Ty} (op : Op K ts)
    (hargs : checkArgs (GLocal ++ (if is32 then i32 else i64) :: GOuter) op.args = true) :
    SymExtEnvWf GOuter (pushTypes ts GLocal) (env ++ (evalSymOpExt is32 env op).toArray) := by
  refine symExtEnvWf_push hwf ts (evalSymOpExt is32 env op) (evalSymOpExt_len is32 env op) ?_
  have hOth : ∀ {ts' : List Ty} {op' : Op K ts'},
      evalSymOp1Ext is32 env op' = none →
      ∀ s ∈ evalSymOpExt is32 env op', SymExtOuterOk GOuter s := by
    intro ts' op' h1 s hs
    dsimp only [evalSymOpExt] at hs; rw [h1] at hs
    have hs' : s ∈ ts'.map fun _ => SymExt.other := by
      cases ts' with | nil => exact hs | cons _ tl => cases tl <;> exact hs
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hs'; exact trivial
  cases op with
  | mk code args =>
    cases code with
    | copy t =>
      by_cases ht64 : t = i64
      · subst ht64; dsimp only [evalSymOpExt, evalSymOp1Ext]; rw [dite_eq_left rfl]
        intro s hs; cases hs with
        | head =>
          dsimp only [checkArgs] at hargs; rw [Bool.and_true] at hargs
          exact argToSym_wf hwf hargs
        | tail _ h => cases h
      · by_cases ht32 : t = i32
        · subst ht32; dsimp only [evalSymOpExt, evalSymOp1Ext]
          rw [dite_eq_right ht64, dite_eq_left rfl]
          intro s hs; cases hs with
          | head =>
            dsimp only [checkArgs] at hargs; rw [Bool.and_true] at hargs
            exact argToSym_wf hwf hargs
          | tail _ h => cases h
        · exact hOth (by dsimp only [evalSymOp1Ext]; rw [dite_eq_right ht64, dite_eq_right ht32])
    | zext m n =>
      by_cases hm : m = 32
      · subst hm
        by_cases hn : (n == 64) = true
        · dsimp only [evalSymOpExt, evalSymOp1Ext]
          rw [dite_eq_left rfl, ite_eq_left hn]
          cases argToSym is32 env args.1 <;> intro s hs
          all_goals
            try (have hs' : s ∈ [Ty.bits n].map fun _ => SymExt.other := hs
                 obtain ⟨_, _, rfl⟩ := List.mem_map.mp hs'; exact trivial)
          · cases is32 <;> cases hs with
            | head => exact trivial
            | tail _ h => cases h
        · exact hOth (by dsimp only [evalSymOp1Ext]; rw [dite_eq_left rfl, ite_eq_right hn])
      · exact hOth (by dsimp only [evalSymOp1Ext]; rw [dite_eq_right hm])
    | add t =>
      by_cases ht64 : t = i64
      · subst ht64; rcases args with ⟨a, b, ⟨⟩⟩
        dsimp only [evalSymOpExt, evalSymOp1Ext]; rw [dite_eq_left rfl]
        intro s hs; cases hs with
        | head =>
          rw [checkArgs_pair_eq, Bool.and_eq_true] at hargs
          exact ⟨argToSym_wf hwf hargs.1, argToSym_wf hwf hargs.2⟩
        | tail _ h => cases h
      · by_cases ht32 : t = i32
        · subst ht32; rcases args with ⟨a, b, ⟨⟩⟩
          dsimp only [evalSymOpExt, evalSymOp1Ext]; rw [dite_eq_right ht64, dite_eq_left rfl]
          intro s hs; cases hs with
          | head =>
            rw [checkArgs_pair_eq, Bool.and_eq_true] at hargs
            exact ⟨argToSym_wf hwf hargs.1, argToSym_wf hwf hargs.2⟩
          | tail _ h => cases h
        · exact hOth (by dsimp only [evalSymOp1Ext]; rw [dite_eq_right ht64, dite_eq_right ht32])
    | shl t =>
      by_cases ht64 : t = i64
      · subst ht64; rcases args with ⟨a, b, ⟨⟩⟩
        rw [checkArgs_pair_eq, Bool.and_eq_true] at hargs
        dsimp only [evalSymOpExt, evalSymOp1Ext]; rw [dite_eq_left rfl]
        cases argToSym is32 env b <;> intro s hs <;> cases hs with
        | head => first | exact trivial | exact argToSym_wf hwf hargs.1
        | tail _ h => cases h
      · exact hOth (by dsimp only [evalSymOp1Ext]; rw [dite_eq_right ht64])
    | cmp o t _ _ =>
      by_cases ht64 : t = i64
      · subst ht64; rcases args with ⟨a, b, ⟨⟩⟩
        rw [checkArgs_pair_eq, Bool.and_eq_true] at hargs
        have hsa := argToSym_wf hwf hargs.1; have hsb := argToSym_wf hwf hargs.2
        cases is32
        · dsimp only [evalSymOpExt, evalSymOp1Ext]; rw [dite_eq_left rfl]
          intro s hs; cases hs with
          | head =>
            cases o <;>
              first
              | exact trivial
              | (cases argToSym false env a <;>
                  first | exact trivial | exact symExtOuterOk_cmpU64 _ hsb)
              | (cases argToSym false env b <;>
                  first | exact trivial | exact symExtOuterOk_cmpU64 _ hsa)
          | tail _ h => cases h
        · exact hOth (by dsimp only [evalSymOp1Ext]; rw [dite_eq_left rfl]; rfl)
      · by_cases ht32 : t = i32
        · subst ht32; rcases args with ⟨a, b, ⟨⟩⟩
          rw [checkArgs_pair_eq, Bool.and_eq_true] at hargs
          have hsa := argToSym_wf hwf hargs.1; have hsb := argToSym_wf hwf hargs.2
          cases is32
          · exact hOth (by
              dsimp only [evalSymOp1Ext]; rw [dite_eq_right ht64, dite_eq_left rfl]; rfl)
          · dsimp only [evalSymOpExt, evalSymOp1Ext]; rw [dite_eq_right ht64, dite_eq_left rfl]
            intro s hs; cases hs with
            | head =>
              cases o <;>
                first
                | exact trivial
                | (cases argToSym true env a <;>
                    first | exact trivial | exact symExtOuterOk_cmpU32 _ hsb)
                | (cases argToSym true env b <;>
                    first | exact trivial | exact symExtOuterOk_cmpU32 _ hsa)
            | tail _ h => cases h
        · exact hOth (by dsimp only [evalSymOp1Ext]; rw [dite_eq_right ht64, dite_eq_right ht32])
    | _ => exact hOth rfl

@[expose] public def StoreSpecWf (GOuter : List Ty) (st : StoreSpec) : Prop :=
  checkArg GOuter i64 st.base = true ∧ st.off?.all (checkArg GOuter i64) = true ∧ st.shift ≤ 3

@[expose] public def FillBoundWf (GOuter : List Ty) (is32 : Bool) : FillBound → Prop
  | .b32 _ bnd => is32 = true ∧ checkArg GOuter i32 bnd = true
  | .b64 _ bnd => is32 = false ∧ checkArg GOuter i64 bnd = true

private theorem matchMultiBodyTail_wf {rs : List Ty} {GOuter : List Ty} {D : List (List Ty)}
    {is32 : Bool} {stores : List StoreSpec} :
    (tf : TFlat rs) → {GLocal : List Ty} → {env : Array SymExt} → {acc : List StoreSpec} →
    (∀ s ∈ acc, StoreSpecWf GOuter s) →
    SymExtEnvWf GOuter GLocal env →
    tf.wfCheck (GLocal ++ (if is32 then i32 else i64) :: GOuter) D = true →
    matchMultiBodyTail is32 env acc tf = some stores →
    ∀ s ∈ stores, StoreSpecWf GOuter s
  | .let_ op k, GLocal, env, acc, hacc, hwf, htf, hm => by
    rw [wfCheck_let_eq, Bool.and_eq_true] at htf
    dsimp only [matchMultiBodyTail] at hm
    by_cases hp : isTotalPureOp op.code = true
    · rw [ite_eq_left hp] at hm
      have hk := htf.2; rw [pushTypes_append] at hk
      exact matchMultiBodyTail_wf k hacc (evalSymOpExt_wf hwf op htf.1) hk hm
    · rw [ite_eq_right hp] at hm; cases hm
  | .store valArg addrArg cont, GLocal, env, acc, hacc, hwf, htf, hm => by
    rw [wfCheck_store_eq, Bool.and_eq_true, Bool.and_eq_true] at htf
    dsimp only [matchMultiBodyTail] at hm
    by_cases hlen : acc.length ≥ 8
    · rw [ite_eq_left (by simp [hlen])] at hm; cases hm
    · rw [ite_eq_right (by simp [hlen])] at hm
      cases valArg with
      | var _ => cases hm
      | imm v =>
        dsimp only at hm
        cases hsp : splatVal64 v with
        | none => rw [hsp] at hm; cases hm
        | some p =>
          rcases p with ⟨shift, fill64⟩; rw [hsp] at hm; dsimp only at hm
          cases hma : matchAddrExt is32 shift (argToSym is32 env addrArg) with
          | none => rw [hma] at hm; cases hm
          | some bp =>
            rcases bp with ⟨base, off?⟩; rw [hma] at hm; dsimp only at hm
            have hwfA := matchAddrExt_wf (argToSym_wf hwf htf.1.2) hma
            have hsp' := splatVal64_spec v hsp
            have hSt : StoreSpecWf GOuter { base, off?, shift, fill64 } := ⟨hwfA.1, hwfA.2, hsp'.1⟩
            have hAll : ∀ s ∈ ({ base, off?, shift, fill64 } : StoreSpec) :: acc,
                StoreSpecWf GOuter s := fun s hs => by
              cases hs with | head => exact hSt | tail _ h => exact hacc s h
            split at hm
            · cases hm; intro s hs; rw [List.mem_reverse] at hs; exact hAll s hs
            · exact matchMultiBodyTail_wf cont hAll hwf htf.2 hm
  | .load _ _ _, _, _, _, _, _, _, hm | .call _ _ _ _, _, _, _, _, _, _, hm
  | .jnz _ _ _, _, _, _, _, _, _, hm | .jump _ _, _, _, _, _, _, _, hm
  | .ret _, _, _, _, _, _, _, hm | .exit _ _, _, _, _, _, _, _, hm
  | .hlt, _, _, _, _, _, _, hm | .group _ _, _, _, _, _, _, _, hm => by
    dsimp only [matchMultiBodyTail] at hm; cases hm

public theorem matchMultiFillBody_wf {rs : List Ty} {GOuter : List Ty} {D : List (List Ty)}
    {is32 : Bool} {fb : FillBound} {stores : List StoreSpec} :
    (tf : TFlat rs) → {GLocal : List Ty} → {env : Array SymExt} →
    SymExtEnvWf GOuter GLocal env →
    tf.wfCheck (GLocal ++ (if is32 then i32 else i64) :: GOuter) D = true →
    matchMultiFillBody is32 env tf = some (fb, stores) →
    FillBoundWf GOuter is32 fb ∧ ∀ s ∈ stores, StoreSpecWf GOuter s
  | .let_ op k, GLocal, env, hwf, htf, hm => by
    rw [wfCheck_let_eq, Bool.and_eq_true] at htf
    dsimp only [matchMultiFillBody] at hm
    by_cases hp : isTotalPureOp op.code = true
    · rw [ite_eq_left hp] at hm
      have hk := htf.2; rw [pushTypes_append] at hk
      exact matchMultiFillBody_wf k (evalSymOpExt_wf hwf op htf.1) hk hm
    · rw [ite_eq_right hp] at hm; cases hm
  | .jnz c t e, GLocal, env, hwf, htf, hm => by
    rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true] at htf
    dsimp only [matchMultiFillBody] at hm
    have hcb : SymExtOuterOk GOuter (argToSym is32 env c) := argToSym_wf hwf htf.1.1
    cases hc : argToSym is32 env c with
    | cmpU32 isLt bnd =>
      rw [hc] at hm hcb
      cases is32
      · simp at hm
      · dsimp only at hm
        rcases Option.map_eq_some_iff.mp hm with ⟨sts, hsts, hpair⟩
        cases hpair
        exact ⟨⟨rfl, hcb⟩, matchMultiBodyTail_wf t (fun _ h => by cases h)
          (by simpa using hwf) (by simpa using htf.1.2) hsts⟩
    | cmpU64 isLt bnd =>
      rw [hc] at hm hcb
      cases is32
      · dsimp only at hm
        rcases Option.map_eq_some_iff.mp hm with ⟨sts, hsts, hpair⟩
        cases hpair
        exact ⟨⟨rfl, hcb⟩, matchMultiBodyTail_wf t (fun _ h => by cases h)
          (by simpa using hwf) (by simpa using htf.1.2) hsts⟩
      · simp at hm
    | loopI | loopZext64 | outer64 _ | outer32 _ | const64 _ | const32 _
    | add64 _ _ | add32 _ _ | shlConst64 _ _ | other =>
      rw [hc] at hm; cases hm
  | .load _ _ _, _, _, _, _, hm | .store _ _ _, _, _, _, _, hm
  | .call _ _ _ _, _, _, _, _, hm | .jump _ _, _, _, _, _, hm
  | .ret _, _, _, _, _, hm | .exit _ _, _, _, _, _, hm
  | .hlt, _, _, _, _, hm | .group _ _, _, _, _, _, hm => by
    dsimp only [matchMultiFillBody] at hm; cases hm

/-! ## Section 2: `mkSeqStores`, `emitWideStreams`, `mkMultiWideBody`, `mkDisjointCheck` WF -/

private theorem replicate_append_cons {α : Type} (r : Nat) (x : α) (xs : List α) :
    List.replicate (r + 1) x ++ xs = List.replicate r x ++ (x :: xs) := by
  induction r with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.cons_append, ih]; rfl

private theorem wfCheck_mkSeqStoresGo {rs : List Ty} (fill64 : BitVec 64)
    (D : List (List Ty)) (cont : Nat → TFlat rs) :
    ∀ (rem m : Nat) (GLocal : List Ty),
      1 ≤ m → listGet? GLocal (m - 1) = some i64 →
      (cont (m - 1 + rem)).wfCheck (List.replicate rem i64 ++ GLocal) D = true →
      (mkSeqStoresGo fill64 m rem cont).wfCheck GLocal D = true
  | 0, m, GLocal, _, _, hCont => by
    dsimp only [mkSeqStoresGo]; simpa using hCont
  | r + 1, m, GLocal, hm, hp, hCont => by
    dsimp only [mkSeqStoresGo, op2]
    rw [wfCheck_let_eq]; dsimp only [op2]
    rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
    have hcp : checkArg GLocal i64 (.var (m - 1)) = true := by
      dsimp only [checkArg]; rw [hp]; rfl
    refine ⟨⟨hcp, rfl⟩, ?_⟩
    rw [wfCheck_store_eq, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨rfl, by dsimp only [checkArg, pushTypes, listGet?]; rfl⟩, ?_⟩
    have hm1 : 1 ≤ m + 1 := by omega
    have hp1 : listGet? (pushTypes [i64] GLocal) ((m + 1) - 1) = some i64 := by
      have hm_eq : (m + 1) - 1 = (m - 1) + 1 := by omega
      rw [pushTypes_cons_eq, pushTypes_nil_eq, hm_eq]; exact hp
    have hEq1 : m - 1 + (r + 1) = (m + 1) - 1 + r := by omega
    rw [hEq1, replicate_append_cons] at hCont
    exact wfCheck_mkSeqStoresGo fill64 D cont r (m + 1) (i64 :: GLocal) hm1 hp1 hCont

private theorem wfCheck_mkSeqStores {rs : List Ty} (fill64 : BitVec 64)
    (D : List (List Ty)) (cont : Nat → TFlat rs) :
    ∀ (n64 : Nat) (GLocal : List Ty),
      0 < n64 → listGet? GLocal 0 = some i64 →
      (cont (n64 - 1)).wfCheck (List.replicate (n64 - 1) i64 ++ GLocal) D = true →
      (mkSeqStores fill64 n64 cont).wfCheck GLocal D = true
  | 0, _, hn, _, _ => by omega
  | r + 1, GLocal, _, hp0, hCont => by
    dsimp only [mkSeqStores]
    rw [wfCheck_store_eq, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨rfl, by dsimp only [checkArg]; rw [hp0]; rfl⟩, ?_⟩
    exact wfCheck_mkSeqStoresGo fill64 D cont r 1 GLocal (Nat.le_refl 1) hp0
      (by simpa [Nat.zero_add] using hCont)

private theorem listGet?_replicate_append {α : Type} (n : Nat) (x : α) (xs : List α) (k : Nat) :
    listGet? (List.replicate n x ++ xs) (k + n) = listGet? xs k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, show k + (n + 1) = (k + n) + 1 by omega,
      listGet?_cons_succ_eq]
    exact ih

private theorem checkArg_var_eq (G : List Ty) {t : Ty} (idx : Nat) (h : listGet? G idx = some t) :
    checkArg G t (.var idx) = true := by
  dsimp only [checkArg]; rw [h]; dsimp only
  cases tyDecEq t t with | isTrue _ => rfl | isFalse hne => exact absurd rfl hne

private theorem wfCheck_jump_self {rs : List Ty} (G : List Ty) (D : List (List Ty))
    (j : Nat) {t : Ty} (a : Arg K t) (hj : listGet? D j = some [t])
    (ha : checkArg G t a = true) :
    (TFlat.jump (rs := rs) (ts := [t]) j (a, ())).wfCheck G D = true := by
  rw [wfCheck_jump_eq, hj]; dsimp only [checkArgs]; rw [ha, Bool.and_true]
  cases listTyDecEq [t] [t] with | isTrue _ => rfl | isFalse h => exact absurd rfl h

private theorem wfCheck_emitWideStreams {rs : List Ty} (w stepK : Nat)
    {GOuter : List Ty} {D : List (List Ty)} (hLab0 : listGet? D 0 = some [.bits w]) :
    (stores : List StoreSpec) → (GPre : List Ty) → (iDepth i64Depth : Nat) →
    GPre.length ≥ 1 →
    (∀ s ∈ stores, StoreSpecWf GOuter s ∧ 0 < stepK / (8 >>> s.shift)) →
    listGet? (GPre ++ GOuter) iDepth = some (.bits w) →
    listGet? (GPre ++ GOuter) i64Depth = some i64 →
    (emitWideStreams (rs := rs) w stepK stores GPre.length iDepth i64Depth).wfCheck
      (GPre ++ GOuter) D = true
  | [], GPre, iDepth, _, _, _, hiD, _ => by
    dsimp only [emitWideStreams, op2]
    rw [wfCheck_let_eq]; dsimp only [op2]
    rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨checkArg_var_eq _ iDepth hiD, rfl⟩, ?_⟩
    exact wfCheck_jump_self _ D 0 (.var 0) hLab0 (checkArg_var_eq _ 0 rfl)
  | st :: rest, GPre, iDepth, i64Depth, hPre1, hSts, hiD, hi64D => by
    have hSt := hSts st (List.Mem.head _)
    have hRest : ∀ s ∈ rest, StoreSpecWf GOuter s ∧ 0 < stepK / (8 >>> s.shift) :=
      fun s hs => hSts s (List.Mem.tail _ hs)
    dsimp only [emitWideStreams]
    let n64 := stepK / (8 >>> st.shift)
    have hn64 : 0 < n64 := hSt.2
    have hBaseStep : ∀ (G2 : List Ty) (d2 iD2 i64D2 : Nat) (sv : Arg K i64),
        G2.length = d2 → 1 ≤ G2.length →
        checkArg (G2 ++ GOuter) i64 sv = true →
        listGet? (G2 ++ GOuter) iD2 = some (.bits w) →
        listGet? (G2 ++ GOuter) i64D2 = some i64 →
        (TFlat.let_ (rs := rs) (op2 (.add i64) (tArgShift d2 st.base) sv)
          (mkSeqStores st.fill64 n64 (fun pushed =>
            emitWideStreams w stepK rest (d2 + 1 + pushed)
              (iD2 + 1 + pushed) (i64D2 + 1 + pushed)))).wfCheck
          (G2 ++ GOuter) D = true := by
      intro G2 d2 iD2 i64D2 sv hd2 hG2 hsv hiD2 hi64D2
      rw [wfCheck_let_eq]; dsimp only [op2]
      rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
      have hbase' : checkArg (G2 ++ GOuter) i64 (tArgShift d2 st.base) = true := by
        rw [← hd2, wfCheck_tArgShift G2 GOuter st.base]; exact hSt.1.1
      refine ⟨⟨hbase', hsv⟩, ?_⟩
      rw [pushTypes_cons_eq, pushTypes_nil_eq, ← List.cons_append]
      refine wfCheck_mkSeqStores st.fill64 D _ n64 (i64 :: G2 ++ GOuter) hn64 rfl ?_
      have hLenEq : (List.replicate (n64 - 1) i64 ++ (i64 :: G2)).length =
          d2 + 1 + (n64 - 1) := by
        rw [List.length_append, List.length_replicate, List.length_cons, hd2]; omega
      rw [← List.append_assoc, ← hLenEq]
      have hGe1 : (List.replicate (n64 - 1) i64 ++ (i64 :: G2)).length ≥ 1 := by omega
      have hiD_n : listGet? ((List.replicate (n64 - 1) i64 ++ (i64 :: G2)) ++ GOuter)
          (iD2 + 1 + (n64 - 1)) = some (.bits w) := by
        rw [List.append_assoc, show iD2 + 1 + (n64 - 1) = (iD2 + 1) + (n64 - 1) by omega,
          listGet?_replicate_append]
        exact hiD2
      have hi64D_n : listGet? ((List.replicate (n64 - 1) i64 ++ (i64 :: G2)) ++ GOuter)
          (i64D2 + 1 + (n64 - 1)) = some i64 := by
        rw [List.append_assoc, show i64D2 + 1 + (n64 - 1) = (i64D2 + 1) + (n64 - 1) by omega,
          listGet?_replicate_append]
        exact hi64D2
      exact wfCheck_emitWideStreams w stepK hLab0 rest _ _ _ hGe1 hRest hiD_n hi64D_n
    have hAfterShift : ∀ (G1 : List Ty) (d1 iD1 i64D1 : Nat) (idxVar : Arg K i64),
        G1.length = d1 → 1 ≤ G1.length →
        checkArg (G1 ++ GOuter) i64 idxVar = true →
        listGet? (G1 ++ GOuter) iD1 = some (.bits w) →
        listGet? (G1 ++ GOuter) i64D1 = some i64 →
        (if st.shift == 0 then
           TFlat.let_ (rs := rs) (op2 (.add i64) (tArgShift d1 st.base) idxVar)
             (mkSeqStores st.fill64 n64 (fun pushed =>
               emitWideStreams w stepK rest (d1 + 1 + pushed)
                 (iD1 + 1 + pushed) (i64D1 + 1 + pushed)))
         else
           TFlat.let_ (rs := rs) (op2 (.shl i64) idxVar (.imm (BitVec.ofNat 64 st.shift)))
             (TFlat.let_ (op2 (.add i64) (tArgShift (d1 + 1) st.base) (.var 0))
               (mkSeqStores st.fill64 n64 (fun pushed =>
                 emitWideStreams w stepK rest (d1 + 1 + 1 + pushed) (iD1 + 1 + 1 + pushed)
                   (i64D1 + 1 + 1 + pushed))))).wfCheck
          (G1 ++ GOuter) D = true := by
      intro G1 d1 iD1 i64D1 idxVar hd1 hG1 hidx hiD1 hi64D1
      split
      · exact hBaseStep G1 d1 iD1 i64D1 idxVar hd1 hG1 hidx hiD1 hi64D1
      · rw [wfCheck_let_eq]; dsimp only [op2]
        rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
        refine ⟨⟨hidx, rfl⟩, ?_⟩
        rw [pushTypes_cons_eq, pushTypes_nil_eq, ← List.cons_append]
        exact hBaseStep (i64 :: G1) (d1 + 1) (iD1 + 1) (i64D1 + 1) (.var 0)
          (by simp [hd1]) (by simp) rfl hiD1 hi64D1
    cases hoff : st.off? with
    | none =>
      exact hAfterShift GPre GPre.length iDepth i64Depth (.var i64Depth) rfl hPre1
        (by dsimp only [checkArg]; rw [hi64D]; rfl) hiD hi64D
    | some off =>
      dsimp only
      rw [wfCheck_let_eq]; dsimp only [op2]
      rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
      have hoff' : checkArg (GPre ++ GOuter) i64 (tArgShift GPre.length off) = true := by
        rw [wfCheck_tArgShift GPre GOuter off]
        have ho := hSt.1.2.1; rw [hoff, Option.all_some] at ho; exact ho
      refine ⟨⟨by dsimp only [checkArg]; rw [hi64D]; rfl, hoff'⟩, ?_⟩
      rw [pushTypes_cons_eq, pushTypes_nil_eq, ← List.cons_append]
      exact hAfterShift (i64 :: GPre) (GPre.length + 1) (iDepth + 1) (i64Depth + 1) (.var 0)
        (by simp) (by simp) rfl hiD hi64D

private theorem wfCheck_mkMultiWideBody {rs : List Ty} {GOuter : List Ty} {DOuter : List (List Ty)}
    {w stepK : Nat} (hw : w = 32 ∨ w = 64) {bound : Arg K (.bits w)} {stores : List StoreSpec}
    (hBnd : checkArg GOuter (.bits w) bound = true)
    (hSts : ∀ s ∈ stores, StoreSpecWf GOuter s ∧ 0 < stepK / (8 >>> s.shift)) :
    (mkMultiWideBody (rs := rs) w bound stores stepK).wfCheck
      (pushTypes [.bits w] GOuter) ([.bits w] :: [.bits w] :: DOuter) = true := by
  dsimp only [mkMultiWideBody]
  rw [wfCheck_let_eq]; dsimp only [op2]
  rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
  have hbnd : checkArg ([.bits w] ++ GOuter) (.bits w)
      (tArgShift ([Ty.bits w] : List Ty).length bound) = true := by
    rw [wfCheck_tArgShift ([Ty.bits w] : List Ty) GOuter bound]; exact hBnd
  refine ⟨⟨hbnd, checkArg_var_eq (pushTypes [.bits w] GOuter) 0 rfl⟩, ?_⟩
  rw [wfCheck_let_eq]; dsimp only [op2]
  rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨checkArg_var_eq (pushTypes [.bits w] (pushTypes [.bits w] GOuter)) 0 rfl, rfl⟩, ?_⟩
  rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true]
  have hjFalse : (TFlat.jump (rs := rs) (ts := [.bits w]) 1 (.var 2, ())).wfCheck
      ([.bool, .bits w, .bits w] ++ GOuter) ([.bits w] :: [.bits w] :: DOuter) = true :=
    wfCheck_jump_self _ _ 1 (.var 2) rfl (checkArg_var_eq _ 2 rfl)
  refine ⟨⟨by dsimp only [checkArg, pushTypes, listGet?]; rfl, ?_⟩, hjFalse⟩
  have hLab0 : listGet? ([.bits w] :: [.bits w] :: DOuter) 0 = some [.bits w] := rfl
  rcases hw with rfl | rfl
  · simp only [beq_self_eq_true, ↓reduceIte]
    rw [wfCheck_let_eq, Bool.and_eq_true]
    dsimp only [op1, checkArgs, pushTypes]
    refine ⟨by rw [Bool.and_true]; exact checkArg_var_eq _ 2 rfl, ?_⟩
    exact wfCheck_emitWideStreams 32 stepK hLab0 stores [i64, .bool, .bits 32, .bits 32] 3 0
      (by simp) hSts rfl rfl
  · rw [ite_eq_right (by decide)]
    exact wfCheck_emitWideStreams 64 stepK hLab0 stores [.bool, .bits 64, .bits 64] 2 2
      (by simp) hSts rfl rfl

private theorem allIdxPairs_mem {α : Type} {xs : List α} {a b : α}
    (h : (a, b) ∈ allIdxPairs xs) : a ∈ xs ∧ b ∈ xs := by
  induction xs with
  | nil => simp [allIdxPairs] at h
  | cons x xs ih =>
    dsimp only [allIdxPairs] at h
    rw [List.mem_append] at h
    rcases h with h1 | h2
    · obtain ⟨y, hy, heq⟩ := List.mem_map.mp h1
      cases heq; exact ⟨List.Mem.head _, List.Mem.tail _ hy⟩
    · obtain ⟨ha, hb⟩ := ih h2
      exact ⟨List.Mem.tail _ ha, List.Mem.tail _ hb⟩

private theorem listGet?_append_left_lt (G1 G2 : List Ty) {k : Nat} (hk : k < G1.length)
    (h : listGet? G1 k = some i64) : listGet? (G1 ++ G2) k = some i64 := by
  rw [listGet?_eq_getElem?, List.getElem?_append_left hk, ← listGet?_eq_getElem?]; exact h

private theorem wfCheck_mkPairChecks {rs : List Ty} {GOuter : List Ty} {D : List (List Ty)}
    (w : Nat) (initArg : Arg K (.bits w)) (hInit : checkArg GOuter (.bits w) initArg = true)
    (hLab0 : listGet? D 0 = some [.bits w]) (hLab1 : listGet? D 1 = some [.bits w]) :
    ∀ (pairs : List ((Nat × Nat) × (Nat × Nat))) (GPre : List Ty),
      (∀ p ∈ pairs,
        p.1.1 < GPre.length ∧ p.1.2 < GPre.length ∧
        p.2.1 < GPre.length ∧ p.2.2 < GPre.length ∧
        listGet? GPre (GPre.length - 1 - p.1.1) = some i64 ∧
        listGet? GPre (GPre.length - 1 - p.1.2) = some i64 ∧
        listGet? GPre (GPre.length - 1 - p.2.1) = some i64 ∧
        listGet? GPre (GPre.length - 1 - p.2.2) = some i64) →
      (mkPairChecks (rs := rs) w initArg pairs GPre.length).wfCheck (GPre ++ GOuter) D = true
  | [], GPre, _ => by
    dsimp only [mkPairChecks]
    exact wfCheck_jump_self _ D 0 (tArgShift GPre.length initArg) hLab0
      (by rw [wfCheck_tArgShift]; exact hInit)
  | ((loA, hiA), (loB, hiB)) :: rest, GPre, hP => by
    have h0 := hP ((loA, hiA), (loB, hiB)) (List.Mem.head _)
    dsimp only at h0
    dsimp only [mkPairChecks]
    rw [wfCheck_let_eq]; dsimp only [op2]
    rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
    have hc1a : checkArg (GPre ++ GOuter) i64 (.var (GPre.length - 1 - hiA)) = true := by
      dsimp only [checkArg]
      rw [listGet?_append_left_lt GPre GOuter (k := GPre.length - 1 - hiA) (by omega)
        h0.2.2.2.2.2.1]; rfl
    have hc1b : checkArg (GPre ++ GOuter) i64 (.var (GPre.length - 1 - loB)) = true := by
      dsimp only [checkArg]
      rw [listGet?_append_left_lt GPre GOuter (k := GPre.length - 1 - loB) (by omega)
        h0.2.2.2.2.2.2.1]; rfl
    refine ⟨⟨hc1a, hc1b⟩, ?_⟩
    rw [wfCheck_let_eq]; dsimp only [op2]
    rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
    have hc2a : checkArg (pushTypes [.bool] (GPre ++ GOuter)) i64
        (.var (GPre.length - hiB)) = true := by
      rw [pushTypes_cons_eq, pushTypes_nil_eq, show GPre.length - hiB =
        (GPre.length - 1 - hiB) + 1 by omega]
      dsimp only [checkArg, listGet?]
      rw [listGet?_append_left_lt GPre GOuter (k := GPre.length - 1 - hiB) (by omega)
        h0.2.2.2.2.2.2.2]; rfl
    have hc2b : checkArg (pushTypes [.bool] (GPre ++ GOuter)) i64
        (.var (GPre.length - loA)) = true := by
      rw [pushTypes_cons_eq, pushTypes_nil_eq, show GPre.length - loA =
        (GPre.length - 1 - loA) + 1 by omega]
      dsimp only [checkArg, listGet?]
      rw [listGet?_append_left_lt GPre GOuter (k := GPre.length - 1 - loA) (by omega)
        h0.2.2.2.2.1]; rfl
    refine ⟨⟨hc2a, hc2b⟩, ?_⟩
    rw [wfCheck_let_eq]; dsimp only [op2]
    rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨by dsimp only [checkArg, pushTypes, listGet?]; rfl,
      by dsimp only [checkArg, pushTypes, listGet?]; rfl⟩, ?_⟩
    rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true]
    have hlen3 : ([Ty.bool, Ty.bool, Ty.bool] ++ GPre).length = GPre.length + 3 := by simp
    have hjFalse : (TFlat.jump (rs := rs) (ts := [.bits w]) 1
        (tArgShift (GPre.length + 3) initArg, ())).wfCheck
        (pushTypes [.bool] (pushTypes [.bool] (pushTypes [.bool] (GPre ++ GOuter)))) D = true := by
      simp only [pushTypes]
      exact wfCheck_jump_self _ D 1 (tArgShift (GPre.length + 3) initArg) hLab1
        (by
          change checkArg (([Ty.bool, Ty.bool, Ty.bool] ++ GPre) ++ GOuter) (.bits w) _ = true
          rw [← hlen3, wfCheck_tArgShift]; exact hInit)
    refine ⟨⟨by dsimp only [checkArg, pushTypes, listGet?]; rfl, ?_⟩, hjFalse⟩
    simp only [pushTypes]
    change (mkPairChecks (rs := rs) w initArg rest (GPre.length + 3)).wfCheck
      (([Ty.bool, Ty.bool, Ty.bool] ++ GPre) ++ GOuter) D = true
    rw [← hlen3]
    refine wfCheck_mkPairChecks w initArg hInit hLab0 hLab1 rest
      ([Ty.bool, Ty.bool, Ty.bool] ++ GPre) ?_
    intro p hp
    have hpf := hP p (List.Mem.tail _ hp)
    rw [hlen3]
    refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · rw [show GPre.length + 3 - 1 - p.1.1 = (GPre.length - 1 - p.1.1) + 3 by omega]
      exact hpf.2.2.2.2.1
    · rw [show GPre.length + 3 - 1 - p.1.2 = (GPre.length - 1 - p.1.2) + 3 by omega]
      exact hpf.2.2.2.2.2.1
    · rw [show GPre.length + 3 - 1 - p.2.1 = (GPre.length - 1 - p.2.1) + 3 by omega]
      exact hpf.2.2.2.2.2.2.1
    · rw [show GPre.length + 3 - 1 - p.2.2 = (GPre.length - 1 - p.2.2) + 3 by omega]
      exact hpf.2.2.2.2.2.2.2

private def IvLvlWf (GPre : List Ty) (p : Nat × Nat) : Prop :=
  p.1 < GPre.length ∧ p.2 < GPre.length ∧
  listGet? GPre (GPre.length - 1 - p.1) = some i64 ∧
  listGet? GPre (GPre.length - 1 - p.2) = some i64

private theorem ivLvlWf_push (GPre : List Ty) (t : Ty) {p : Nat × Nat} (hp : IvLvlWf GPre p) :
    IvLvlWf (t :: GPre) p := by
  dsimp only [IvLvlWf] at hp ⊢
  refine ⟨by simp; omega, by simp; omega, ?_, ?_⟩
  · rw [List.length_cons, show GPre.length + 1 - 1 - p.1 = (GPre.length - 1 - p.1) + 1 by omega,
      listGet?_cons_succ_eq]
    exact hp.2.2.1
  · rw [List.length_cons, show GPre.length + 1 - 1 - p.2 = (GPre.length - 1 - p.2) + 1 by omega,
      listGet?_cons_succ_eq]
    exact hp.2.2.2

private theorem wfCheck_mkStreamBounds {rs : List Ty} {GOuter : List Ty} {D : List (List Ty)}
    (w : Nat) (initArg : Arg K (.bits w)) (rem64Lvl init64Lvl : Nat)
    (hInit : checkArg GOuter (.bits w) initArg = true)
    (hLab0 : listGet? D 0 = some [.bits w]) (hLab1 : listGet? D 1 = some [.bits w]) :
    ∀ (stores : List StoreSpec) (GPre : List Ty) (ivs : List (Nat × Nat)),
      IvLvlWf GPre (rem64Lvl, init64Lvl) →
      (∀ s ∈ stores, StoreSpecWf GOuter s) →
      (∀ p ∈ ivs, IvLvlWf GPre p) →
      (mkStreamBounds (rs := rs) w initArg rem64Lvl init64Lvl stores GPre.length ivs).wfCheck
        (GPre ++ GOuter) D = true
  | [], GPre, ivs, _, _, hivs => by
    dsimp only [mkStreamBounds]
    refine wfCheck_mkPairChecks w initArg hInit hLab0 hLab1 (allIdxPairs ivs) GPre ?_
    intro p hp
    obtain ⟨h1, h2⟩ := allIdxPairs_mem hp
    have ha := hivs p.1 h1; have hb := hivs p.2 h2
    exact ⟨ha.1, ha.2.1, hb.1, hb.2.1, ha.2.2.1, ha.2.2.2, hb.2.2.1, hb.2.2.2⟩
  | st :: rest, GPre, ivs, hRI, hSts, hivs => by
    have hSt := hSts st (List.Mem.head _)
    have hRest : ∀ s ∈ rest, StoreSpecWf GOuter s := fun s hs => hSts s (List.Mem.tail _ hs)
    dsimp only [mkStreamBounds]
    have hAfterTot : ∀ (G4 : List Ty) (loLvl : Nat) (totVar : Arg K i64),
        IvLvlWf G4 (rem64Lvl, init64Lvl) →
        loLvl < G4.length →
        listGet? G4 (G4.length - 1 - loLvl) = some i64 →
        checkArg (G4 ++ GOuter) i64 totVar = true →
        (∀ p ∈ ivs, IvLvlWf G4 p) →
        (TFlat.let_ (rs := rs) (op2 (.add i64) (.var (G4.length - 1 - loLvl)) totVar)
           (TFlat.let_ (op2 (.cmp .ule i64 .bool (rfl : i64.mask = Ty.bool))
               (.var (G4.length + 1 - 1 - loLvl)) (.var 0))
             (TFlat.jnz (.var 0)
               (mkStreamBounds w initArg rem64Lvl init64Lvl rest (G4.length + 2)
                 ((loLvl, G4.length) :: ivs))
               (TFlat.jump (ts := [.bits w]) 1 (tArgShift (G4.length + 2) initArg, ()))))).wfCheck
          (G4 ++ GOuter) D = true := by
      intro G4 loLvl totVar hRI4 hLo4 hG_Lo hTot hiv4
      rw [wfCheck_let_eq]; dsimp only [op2]
      rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
      have hLoArg : checkArg (G4 ++ GOuter) i64 (.var (G4.length - 1 - loLvl)) = true := by
        dsimp only [checkArg]
        rw [listGet?_append_left_lt G4 GOuter (k := G4.length - 1 - loLvl) (by omega) hG_Lo]; rfl
      refine ⟨⟨hLoArg, hTot⟩, ?_⟩
      rw [wfCheck_let_eq]; dsimp only [op2]
      rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
      have hLoArg5 : checkArg (pushTypes [i64] (G4 ++ GOuter)) i64
          (.var (G4.length + 1 - 1 - loLvl)) = true := by
        rw [pushTypes_cons_eq, pushTypes_nil_eq, show G4.length + 1 - 1 - loLvl =
          (G4.length - 1 - loLvl) + 1 by omega]
        dsimp only [checkArg, listGet?]
        rw [listGet?_append_left_lt G4 GOuter (k := G4.length - 1 - loLvl) (by omega) hG_Lo]; rfl
      refine ⟨⟨hLoArg5, by dsimp only [checkArg, pushTypes, listGet?]; rfl⟩, ?_⟩
      rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true]
      have hlen2 : ([Ty.bool, i64] ++ G4).length = G4.length + 2 := by simp
      have hjF : (TFlat.jump (rs := rs) (ts := [.bits w]) 1
          (tArgShift (G4.length + 2) initArg, ())).wfCheck
          (pushTypes [Ty.bool] (pushTypes [i64] (G4 ++ GOuter))) D = true := by
        simp only [pushTypes]
        exact wfCheck_jump_self _ D 1 (tArgShift (G4.length + 2) initArg) hLab1
          (by
            change checkArg (([Ty.bool, i64] ++ G4) ++ GOuter) (.bits w) _ = true
            rw [← hlen2, wfCheck_tArgShift]; exact hInit)
      refine ⟨⟨by dsimp only [checkArg, pushTypes, listGet?]; rfl, ?_⟩, hjF⟩
      simp only [pushTypes]
      change (mkStreamBounds (rs := rs) w initArg rem64Lvl init64Lvl rest (G4.length + 2)
        ((loLvl, G4.length) :: ivs)).wfCheck (([Ty.bool, i64] ++ G4) ++ GOuter) D = true
      have hRI5 : IvLvlWf ([Ty.bool, i64] ++ G4) (rem64Lvl, init64Lvl) :=
        ivLvlWf_push _ Ty.bool (ivLvlWf_push G4 i64 hRI4)
      have hNew : IvLvlWf ([Ty.bool, i64] ++ G4) (loLvl, G4.length) := by
        refine ⟨by simp; omega, by simp; omega, ?_, ?_⟩
        · rw [show ([Ty.bool, i64] ++ G4).length - 1 - loLvl =
            (G4.length - 1 - loLvl) + 2 by simp; omega]
          exact hG_Lo
        · rw [show ([Ty.bool, i64] ++ G4).length - 1 - G4.length = 1 by simp]; rfl
      have hiv5 : ∀ p ∈ (loLvl, G4.length) :: ivs, IvLvlWf ([Ty.bool, i64] ++ G4) p := by
        intro p hp; cases hp with
        | head => exact hNew
        | tail _ hp => exact ivLvlWf_push _ Ty.bool (ivLvlWf_push G4 i64 (hiv4 p hp))
      rw [← hlen2]
      exact wfCheck_mkStreamBounds w initArg rem64Lvl init64Lvl hInit hLab0 hLab1
        rest ([Ty.bool, i64] ++ G4) ((loLvl, G4.length) :: ivs) hRI5 hRest hiv5
    have hWithScaled : ∀ (G2 : List Ty) (sv : Arg K i64),
        IvLvlWf G2 (rem64Lvl, init64Lvl) →
        checkArg (G2 ++ GOuter) i64 sv = true →
        (∀ p ∈ ivs, IvLvlWf G2 p) →
        (TFlat.let_ (rs := rs) (op2 (.add i64) (tArgShift G2.length st.base) sv)
           (let loLvl := G2.length; let d3 := G2.length + 1
            let hM : i64.mask = Ty.bool := rfl
            let afterTot (d4 : Nat) (totVar : Arg K i64) : TFlat rs :=
              TFlat.let_ (op2 (.add i64) (.var (d4 - 1 - loLvl)) totVar)
                (TFlat.let_ (op2 (.cmp .ule i64 .bool hM) (.var (d4 + 1 - 1 - loLvl)) (.var 0))
                  (TFlat.jnz (.var 0)
                    (mkStreamBounds w initArg rem64Lvl init64Lvl rest (d4 + 2) ((loLvl, d4) :: ivs))
                    (TFlat.jump (ts := [.bits w]) 1 (tArgShift (d4 + 2) initArg, ()))))
            if st.shift == 0 then afterTot d3 (.var (d3 - 1 - rem64Lvl))
            else TFlat.let_ (op2 (.shl i64) (.var (d3 - 1 - rem64Lvl))
                (.imm (BitVec.ofNat 64 st.shift)))
              (afterTot (d3 + 1) (.var 0)))).wfCheck (G2 ++ GOuter) D = true := by
      intro G2 sv hRI2 hsv hiv2
      rw [wfCheck_let_eq]; dsimp only [op2]
      rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
      have hb' : checkArg (G2 ++ GOuter) i64 (tArgShift G2.length st.base) = true := by
        rw [wfCheck_tArgShift G2 GOuter st.base]; exact hSt.1
      refine ⟨⟨hb', hsv⟩, ?_⟩
      rw [pushTypes_cons_eq, pushTypes_nil_eq, ← List.cons_append]
      have hRI3 := ivLvlWf_push G2 i64 hRI2
      dsimp only [IvLvlWf] at hRI3
      have hiv3 : ∀ p ∈ ivs, IvLvlWf (i64 :: G2) p := fun p hp => ivLvlWf_push G2 i64 (hiv2 p hp)
      have hRem3 : checkArg ((i64 :: G2) ++ GOuter) i64
          (.var ((i64 :: G2).length - 1 - rem64Lvl)) = true := by
        dsimp only [checkArg]
        rw [listGet?_append_left_lt (i64 :: G2) GOuter (k := (i64 :: G2).length - 1 - rem64Lvl)
          (by omega) hRI3.2.2.1]; rfl
      split
      · have hGLo3 : listGet? (i64 :: G2) ((i64 :: G2).length - 1 - G2.length) = some i64 := by
          rw [List.length_cons, Nat.add_sub_cancel, Nat.sub_self]; rfl
        exact hAfterTot (i64 :: G2) G2.length (.var ((i64 :: G2).length - 1 - rem64Lvl)) hRI3
          (by simp) hGLo3 hRem3 hiv3
      · rw [wfCheck_let_eq]; dsimp only [op2]
        rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
        refine ⟨⟨hRem3, rfl⟩, ?_⟩
        rw [pushTypes_cons_eq, pushTypes_nil_eq, ← List.cons_append]
        have hGLo4 : listGet? (i64 :: i64 :: G2) ((i64 :: i64 :: G2).length - 1 - G2.length) =
            some i64 := by
          rw [show (i64 :: i64 :: G2).length - 1 - G2.length = 1 by simp]; rfl
        exact hAfterTot (i64 :: i64 :: G2) G2.length (.var 0) (ivLvlWf_push _ i64 hRI3)
          (by rw [List.length_cons, List.length_cons]; omega) hGLo4
          (by dsimp only [checkArg, listGet?]; rfl)
          (fun p hp => ivLvlWf_push _ i64 (hiv3 p hp))
    have hWithIdx : ∀ (G1 : List Ty) (idxVar : Arg K i64),
        IvLvlWf G1 (rem64Lvl, init64Lvl) →
        checkArg (G1 ++ GOuter) i64 idxVar = true →
        (∀ p ∈ ivs, IvLvlWf G1 p) →
        (let withScaled (d2 : Nat) (scaledVar : Arg K i64) : TFlat rs :=
           TFlat.let_ (op2 (.add i64) (tArgShift d2 st.base) scaledVar)
             (let loLvl := d2; let d3 := d2 + 1; let hM : i64.mask = Ty.bool := rfl
              let afterTot (d4 : Nat) (totVar : Arg K i64) : TFlat rs :=
                TFlat.let_ (op2 (.add i64) (.var (d4 - 1 - loLvl)) totVar)
                  (TFlat.let_ (op2 (.cmp .ule i64 .bool hM) (.var (d4 + 1 - 1 - loLvl)) (.var 0))
                    (TFlat.jnz (.var 0)
                      (mkStreamBounds w initArg rem64Lvl init64Lvl rest (d4 + 2)
                        ((loLvl, d4) :: ivs))
                      (TFlat.jump (ts := [.bits w]) 1 (tArgShift (d4 + 2) initArg, ()))))
              if st.shift == 0 then afterTot d3 (.var (d3 - 1 - rem64Lvl))
              else TFlat.let_ (op2 (.shl i64) (.var (d3 - 1 - rem64Lvl))
                  (.imm (BitVec.ofNat 64 st.shift)))
                (afterTot (d3 + 1) (.var 0)))
         if st.shift == 0 then withScaled G1.length idxVar
         else TFlat.let_ (op2 (.shl i64) idxVar (.imm (BitVec.ofNat 64 st.shift)))
           (withScaled (G1.length + 1) (.var 0))).wfCheck (G1 ++ GOuter) D = true := by
      intro G1 idxVar hRI1 hidx1 hiv1
      dsimp only
      by_cases hsh0 : (st.shift == 0) = true
      · rw [ite_eq_left hsh0]
        simpa [hsh0] using hWithScaled G1 idxVar hRI1 hidx1 hiv1
      · rw [ite_eq_right hsh0]
        rw [wfCheck_let_eq]; dsimp only [op2]
        rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
        refine ⟨⟨hidx1, rfl⟩, ?_⟩
        rw [pushTypes_cons_eq, pushTypes_nil_eq, ← List.cons_append]
        have hws := hWithScaled (i64 :: G1) (.var 0) (ivLvlWf_push G1 i64 hRI1)
          (by dsimp only [checkArg, listGet?]; rfl) (fun p hp => ivLvlWf_push G1 i64 (hiv1 p hp))
        simpa [hsh0, op2] using hws
    dsimp only [IvLvlWf] at hRI
    cases hoff : st.off? with
    | none =>
      exact hWithIdx GPre (.var (GPre.length - 1 - init64Lvl)) hRI
        (by dsimp only [checkArg]
            rw [listGet?_append_left_lt GPre GOuter (k := GPre.length - 1 - init64Lvl)
              (by omega) hRI.2.2.2]; rfl)
        hivs
    | some off =>
      dsimp only
      rw [wfCheck_let_eq]; dsimp only [op2]
      rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
      have hi64 : checkArg (GPre ++ GOuter) i64 (.var (GPre.length - 1 - init64Lvl)) = true := by
        dsimp only [checkArg]
        rw [listGet?_append_left_lt GPre GOuter (k := GPre.length - 1 - init64Lvl)
          (by omega) hRI.2.2.2]; rfl
      have hoff' : checkArg (GPre ++ GOuter) i64 (tArgShift GPre.length off) = true := by
        rw [wfCheck_tArgShift GPre GOuter off]
        have ho := hSt.2.1; rw [hoff, Option.all_some] at ho; exact ho
      refine ⟨⟨hi64, hoff'⟩, ?_⟩
      rw [pushTypes_cons_eq, pushTypes_nil_eq, ← List.cons_append]
      exact hWithIdx (i64 :: GPre) (.var 0) (ivLvlWf_push GPre i64 hRI)
        (by dsimp only [checkArg, listGet?]; rfl)
        (fun p hp => ivLvlWf_push GPre i64 (hivs p hp))

private theorem wfCheck_mkDisjointCheck {rs : List Ty} {GOuter : List Ty} {D : List (List Ty)}
    {w stepK : Nat} {isLt : Bool} {initArg bound : Arg K (.bits w)} {stores : List StoreSpec}
    (hInit : checkArg GOuter (.bits w) initArg = true)
    (hBnd : checkArg GOuter (.bits w) bound = true)
    (hSts : ∀ s ∈ stores, StoreSpecWf GOuter s)
    (hLab0 : listGet? D 0 = some [.bits w]) (hLab1 : listGet? D 1 = some [.bits w]) :
    (mkDisjointCheck (rs := rs) w isLt initArg bound stores stepK).wfCheck GOuter D = true := by
  have hJump1 : ∀ (GPre : List Ty),
      (TFlat.jump (rs := rs) (ts := [.bits w]) 1 (tArgShift GPre.length initArg, ())).wfCheck
        (GPre ++ GOuter) D = true := fun GPre =>
    wfCheck_jump_self _ D 1 (tArgShift GPre.length initArg) hLab1
      (by rw [wfCheck_tArgShift]; exact hInit)
  dsimp only [mkDisjointCheck]
  rw [wfCheck_let_eq]; dsimp only [op2]
  rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨hInit, hBnd⟩, ?_⟩
  rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true]
  have hj1 := hJump1 [Ty.bool]
  refine ⟨⟨by dsimp only [checkArg, pushTypes, listGet?]; rfl, ?_⟩, hj1⟩
  rw [wfCheck_let_eq]; dsimp only [op2]
  rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
  have hB1 : checkArg (pushTypes [Ty.bool] GOuter) (.bits w) (tArgShift 1 bound) = true := by
    rw [pushTypes_cons_eq, pushTypes_nil_eq]
    change checkArg ([Ty.bool] ++ GOuter) (.bits w)
      (tArgShift ([Ty.bool] : List Ty).length bound) = true
    rw [wfCheck_tArgShift]; exact hBnd
  have hI1 : checkArg (pushTypes [Ty.bool] GOuter) (.bits w) (tArgShift 1 initArg) = true := by
    rw [pushTypes_cons_eq, pushTypes_nil_eq]
    change checkArg ([Ty.bool] ++ GOuter) (.bits w)
      (tArgShift ([Ty.bool] : List Ty).length initArg) = true
    rw [wfCheck_tArgShift]; exact hInit
  refine ⟨⟨hB1, hI1⟩, ?_⟩
  rw [wfCheck_let_eq]; dsimp only [op2]
  rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨checkArg_var_eq (pushTypes [.bits w] (pushTypes [Ty.bool] GOuter)) 0 rfl, rfl⟩, ?_⟩
  rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true]
  have hj3 := hJump1 [Ty.bool, .bits w, Ty.bool]
  refine ⟨⟨by dsimp only [checkArg, pushTypes, listGet?]; rfl, ?_⟩, hj3⟩
  by_cases hw32 : w = 32
  · subst hw32; rw [dite_eq_left rfl]
    rw [wfCheck_let_eq, Bool.and_eq_true]; dsimp only [op1, checkArgs, pushTypes]
    refine ⟨by rw [Bool.and_true]; exact checkArg_var_eq _ 1 rfl, ?_⟩
    rw [wfCheck_let_eq, Bool.and_eq_true]; dsimp only [op1, checkArgs]; rw [Bool.and_true]
    have hI4 : checkArg (pushTypes [i64] (pushTypes [Ty.bool]
        (pushTypes [.bits 32] (pushTypes [Ty.bool] GOuter)))) (.bits 32)
        (tArgShift 4 initArg) = true := by
      have hlen : ([i64, Ty.bool, .bits 32, Ty.bool] : List Ty).length = 4 := rfl
      change checkArg ([i64, Ty.bool, .bits 32, Ty.bool] ++ GOuter) (.bits 32) _ = true
      rw [← hlen, wfCheck_tArgShift]; exact hInit
    refine ⟨hI4, ?_⟩
    exact wfCheck_mkStreamBounds 32 initArg 3 4 hInit hLab0 hLab1 stores
      [i64, i64, Ty.bool, .bits 32, Ty.bool] [] ⟨by decide, by decide, rfl, rfl⟩ hSts
      (fun _ h => nomatch h)
  · rw [dite_eq_right hw32]
    by_cases hw64 : w = 64
    · subst hw64; rw [dite_eq_left rfl]
      rw [wfCheck_let_eq]; dsimp only [op2]
      rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨by dsimp only [checkArg, pushTypes, listGet?]; rfl, rfl⟩, ?_⟩
      rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true]
      have hj4 := hJump1 [Ty.bool, Ty.bool, i64, Ty.bool]
      refine ⟨⟨by dsimp only [checkArg, pushTypes, listGet?]; rfl, ?_⟩, hj4⟩
      rw [wfCheck_let_eq, Bool.and_eq_true]; dsimp only [op1, checkArgs]; rw [Bool.and_true]
      have hI4 : checkArg (pushTypes [Ty.bool] (pushTypes [Ty.bool]
          (pushTypes [.bits 64] (pushTypes [Ty.bool] GOuter)))) i64
          (tArgShift 4 initArg) = true := by
        have hlen : ([Ty.bool, Ty.bool, i64, Ty.bool] : List Ty).length = 4 := rfl
        change checkArg ([Ty.bool, Ty.bool, i64, Ty.bool] ++ GOuter) i64 _ = true
        rw [← hlen, wfCheck_tArgShift]; exact hInit
      refine ⟨hI4, ?_⟩
      exact wfCheck_mkStreamBounds 64 initArg 1 4 hInit hLab0 hLab1 stores
        [i64, Ty.bool, Ty.bool, i64, Ty.bool] [] ⟨by decide, by decide, rfl, rfl⟩ hSts
        (fun _ h => nomatch h)
    · rw [dite_eq_right hw64]; exact hJump1 [Ty.bool, .bits w, Ty.bool]

private theorem foldl_min_le (xs : List StoreSpec) (acc : Nat) :
    xs.foldl (fun m s => min m s.shift) acc ≤ acc ∧
    ∀ s ∈ xs, xs.foldl (fun m s => min m s.shift) acc ≤ s.shift := by
  induction xs generalizing acc with
  | nil => exact ⟨Nat.le_refl _, fun _ h => nomatch h⟩
  | cons x xs ih =>
    dsimp only [List.foldl]
    obtain ⟨hacc, hmem⟩ := ih (min acc x.shift)
    refine ⟨Nat.le_trans hacc (Nat.min_le_left _ _), fun s hs => ?_⟩
    cases hs with
    | head => exact Nat.le_trans hacc (Nat.min_le_right _ _)
    | tail _ h => exact hmem s h

private theorem foldl_max_ge (xs : List StoreSpec) (acc : Nat) :
    acc ≤ xs.foldl (fun m s => max m s.shift) acc ∧
    ∀ s ∈ xs, s.shift ≤ xs.foldl (fun m s => max m s.shift) acc := by
  induction xs generalizing acc with
  | nil => exact ⟨Nat.le_refl _, fun _ h => nomatch h⟩
  | cons x xs ih =>
    dsimp only [List.foldl]
    obtain ⟨hacc, hmem⟩ := ih (max acc x.shift)
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) hacc, fun s hs => ?_⟩
    cases hs with
    | head => exact Nat.le_trans (Nat.le_max_right _ _) hacc
    | tail _ h => exact hmem s h

private theorem shift_dvd_le (a b : Nat) (hab : a ≤ b) (hb : b ≤ 3) :
    let d := 8 >>> b; let u := 8 >>> a
    1 ≤ d ∧ d ≤ 8 ∧ 1 ≤ u / d ∧ u / d ≤ 8 ∧ (u / d) * d = u := by
  dsimp only
  have ha : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl
  all_goals first | omega | decide

private theorem computeMultiStepK_aux (unrollN minSh maxSh len : Nat)
    (hu1 : 1 ≤ unrollN) (hu64 : unrollN ≤ 64) (_hlen : 1 ≤ len)
    (hmin : minSh ≤ 3) :
    let mult := if len ≤ 1 then min unrollN 64 else if maxSh == minSh then min unrollN 4 else 1
    let stepK := mult * (8 >>> minSh)
    1 ≤ stepK ∧ stepK ≤ 512 ∧
    ∀ sh : Nat, minSh ≤ sh → sh ≤ 3 → (len ≤ 1 → sh = minSh) →
      (maxSh == minSh → sh = minSh) →
      let n64 := stepK / (8 >>> sh)
      1 ≤ n64 ∧ n64 ≤ 64 ∧ n64 * (8 >>> sh) = stepK := by
  dsimp only
  have hMinK : 1 ≤ 8 >>> minSh ∧ 8 >>> minSh ≤ 8 := by
    have : minSh = 0 ∨ minSh = 1 ∨ minSh = 2 ∨ minSh = 3 := by omega
    rcases this with h | h | h | h <;> simp [h]
  have hMultBnd : 1 ≤ (if len ≤ 1 then min unrollN 64
      else if maxSh == minSh then min unrollN 4 else 1) ∧
      (if len ≤ 1 then min unrollN 64 else if maxSh == minSh then min unrollN 4 else 1) ≤ 64 := by
    split
    · omega
    · split <;> omega
  refine ⟨Nat.le_trans hMultBnd.1 (Nat.le_mul_of_pos_right _ hMinK.1),
    Nat.mul_le_mul hMultBnd.2 hMinK.2, fun sh hmSh hsh3 hL1 hEqSh => ?_⟩
  obtain ⟨hd1, _, hdiv1, hdiv8, hmul⟩ := shift_dvd_le minSh sh hmSh hsh3
  have hMulDiv : ∀ m, (m * (8 >>> minSh)) / (8 >>> sh) = m * ((8 >>> minSh) / (8 >>> sh)) := by
    intro m
    have hEq : m * (8 >>> minSh) = (m * ((8 >>> minSh) / (8 >>> sh))) * (8 >>> sh) := by
      rw [Nat.mul_assoc, hmul]
    rw [hEq, Nat.mul_div_cancel _ hd1]
  have hMulEq : ∀ m, ((m * (8 >>> minSh)) / (8 >>> sh)) * (8 >>> sh) = m * (8 >>> minSh) := by
    intro m; rw [hMulDiv, Nat.mul_assoc, hmul]
  refine ⟨?_, ?_, hMulEq _⟩
  · rw [hMulDiv]; exact Nat.le_trans hMultBnd.1 (Nat.le_mul_of_pos_right _ hdiv1)
  · split
    · next hl1 =>
      have hshEq := hL1 hl1; subst hshEq; rw [Nat.mul_div_cancel _ hd1]; omega
    · split
      · next hbe =>
        have hshEq := hEqSh hbe; subst hshEq; rw [Nat.mul_div_cancel _ hd1]; omega
      · rw [Nat.one_mul]; exact Nat.le_trans hdiv8 (by decide)

public theorem computeMultiStepK_spec (unrollN : Nat) (stores : List StoreSpec)
    (hu1 : 1 ≤ unrollN) (hu64 : unrollN ≤ 64) (hne : 1 ≤ stores.length)
    (hsh : ∀ s ∈ stores, s.shift ≤ 3) :
    let stepK := computeMultiStepK unrollN stores
    1 ≤ stepK ∧ stepK ≤ 512 ∧
    ∀ s ∈ stores,
      let n64 := stepK / (8 >>> s.shift)
      1 ≤ n64 ∧ n64 ≤ 64 ∧ n64 * (8 >>> s.shift) = stepK := by
  have hMinBnd : stores.foldl (fun m s => min m s.shift) 3 ≤ 3 := (foldl_min_le stores 3).1
  have hMinMem : ∀ s ∈ stores, stores.foldl (fun m s => min m s.shift) 3 ≤ s.shift :=
    (foldl_min_le stores 3).2
  have hMaxMem : ∀ s ∈ stores, s.shift ≤ stores.foldl (fun m s => max m s.shift) 0 :=
    (foldl_max_ge stores 0).2
  have hAux := computeMultiStepK_aux unrollN (stores.foldl (fun m s => min m s.shift) 3)
    (stores.foldl (fun m s => max m s.shift) 0) stores.length hu1 hu64 hne hMinBnd
  refine ⟨hAux.1, hAux.2.1, fun s hs => hAux.2.2 s.shift (hMinMem s hs) (hsh s hs) ?_ ?_⟩
  · intro hlen1
    cases stores with
    | nil => simp at hne
    | cons x xs =>
      have hxs : xs = [] := by simp at hlen1; omega
      subst hxs; cases hs with | head => _ | tail _ h => nomatch h
      dsimp only [List.foldl]; have := hsh s (List.Mem.head _); omega
  · intro hEq; rw [beq_iff_eq] at hEq
    have := hMinMem s hs; have := hMaxMem s hs; omega

private theorem wfCheck_mkMultiWideWrapper {rs : List Ty} {GOuter : List Ty}
    {DOuter : List (List Ty)} {w stepK : Nat} (hw : w = 32 ∨ w = 64) {isLt : Bool}
    {initArg bound : Arg K (.bits w)} {stores : List StoreSpec}
    (hInit : checkArg GOuter (.bits w) initArg = true)
    (hBnd : checkArg GOuter (.bits w) bound = true)
    (hSts : ∀ s ∈ stores, StoreSpecWf GOuter s ∧ 0 < stepK / (8 >>> s.shift)) :
    (mkMultiWideWrapper (rs := rs) w isLt initArg bound stores stepK).wfCheck
      GOuter ([.bits w] :: DOuter) = true := by
  dsimp only [mkMultiWideWrapper]
  rw [wfCheck_group_eq, wfCheckB_cons_eq, wfCheckB_nil_eq, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨wfCheck_mkMultiWideBody hw hBnd hSts, rfl⟩, ?_⟩
  have hLab0 : listGet? (pushTypes [[.bits w]] ([.bits w] :: DOuter)) 0 = some [.bits w] := rfl
  have hLab1 : listGet? (pushTypes [[.bits w]] ([.bits w] :: DOuter)) 1 = some [.bits w] := rfl
  split
  · rw [wfCheck_let_eq]; dsimp only [op2]
    rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨hInit, hBnd⟩, ?_⟩
    rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true]
    have hInit1 : checkArg (pushTypes [Ty.bool] GOuter) (.bits w) (tArgShift 1 initArg) = true := by
      rw [pushTypes_cons_eq, pushTypes_nil_eq]
      change checkArg ([Ty.bool] ++ GOuter) (.bits w)
        (tArgShift ([Ty.bool] : List Ty).length initArg) = true
      rw [wfCheck_tArgShift]; exact hInit
    have hj0 := wfCheck_jump_self (rs := rs) (pushTypes [Ty.bool] GOuter)
      (pushTypes [[.bits w]] ([.bits w] :: DOuter)) 0 (tArgShift 1 initArg) hLab0 hInit1
    have hj1 := wfCheck_jump_self (rs := rs) (pushTypes [Ty.bool] GOuter)
      (pushTypes [[.bits w]] ([.bits w] :: DOuter)) 1 (tArgShift 1 initArg) hLab1 hInit1
    exact ⟨⟨by dsimp only [checkArg, pushTypes, listGet?]; rfl, hj0⟩, hj1⟩
  · exact wfCheck_mkDisjointCheck hInit hBnd (fun s hs => (hSts s hs).1) hLab0 hLab1

public theorem widenFillExt_eq_some {unrollN : Nat} {rs : List Ty} {ts0 : List Ty}
    {body k res : TFlat rs} (hw : widenFillExt unrollN ts0 body k = some res) :
    1 ≤ unrollN ∧ unrollN ≤ 64 ∧
    ((ts0 = [i32] ∧ ∃ (initArg : Arg K i32) (isLt : Bool) (bnd : Arg K i32)
        (stores : List StoreSpec),
        k = .jump (ts := [i32]) 0 (initArg, ()) ∧
        matchMultiFillBody true #[] body = some (.b32 isLt bnd, stores) ∧
        1 ≤ stores.length ∧ stores.length ≤ 8 ∧
        res = .group (sig := [[i32]]) (.cons body .nil)
          (mkMultiWideWrapper 32 isLt initArg bnd stores (computeMultiStepK unrollN stores))) ∨
     (ts0 = [i64] ∧ ∃ (initArg : Arg K i64) (isLt : Bool) (bnd : Arg K i64)
        (stores : List StoreSpec),
        k = .jump (ts := [i64]) 0 (initArg, ()) ∧
        matchMultiFillBody false #[] body = some (.b64 isLt bnd, stores) ∧
        2 ≤ stores.length ∧ stores.length ≤ 8 ∧
        res = .group (sig := [[i64]]) (.cons body .nil)
          (mkMultiWideWrapper 64 isLt initArg bnd stores (computeMultiStepK unrollN stores)))) := by
  dsimp only [widenFillExt] at hw
  by_cases hu : (unrollN == 0 || unrollN > 64) = true
  · rw [ite_eq_left hu] at hw; cases hw
  · rw [ite_eq_right hu] at hw
    have hu1 : 1 ≤ unrollN := by simp at hu; omega
    have hu64 : unrollN ≤ 64 := by simp at hu; omega
    refine ⟨hu1, hu64, ?_⟩
    split at hw
    · rename_i initArg
      split at hw
      · rename_i isLt bnd stores hm
        by_cases hlen : (1 ≤ stores.length && stores.length ≤ 8) = true
        · rw [ite_eq_left hlen] at hw; cases hw
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hlen
          refine Or.inl ⟨rfl, initArg, isLt, bnd, stores, rfl, hm, hlen.1, hlen.2, rfl⟩
        · rw [ite_eq_right hlen] at hw; cases hw
      · cases hw
    · rename_i initArg
      split at hw
      · rename_i isLt bnd stores hm
        by_cases hlen : (2 ≤ stores.length && stores.length ≤ 8) = true
        · rw [ite_eq_left hlen] at hw; cases hw
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hlen
          refine Or.inr ⟨rfl, initArg, isLt, bnd, stores, rfl, hm, hlen.1, hlen.2, rfl⟩
        · rw [ite_eq_right hlen] at hw; cases hw
      · cases hw
    · cases hw

public theorem wfCheck_widenFillExt {rs : List Ty} {GOuter : List Ty} {DOuter : List (List Ty)}
    {unrollN : Nat} {ts0 : List Ty} {body k res : TFlat rs}
    (hwf : TFlat.wfCheck GOuter DOuter (.group (.cons (ts := ts0) body .nil) k) = true)
    (hw : widenFillExt unrollN ts0 body k = some res) :
    res.wfCheck GOuter DOuter = true := by
  obtain ⟨hu1, hu64, hCase⟩ := widenFillExt_eq_some hw
  rw [wfCheck_group_eq, wfCheckB_cons_eq, wfCheckB_nil_eq, Bool.and_true, Bool.and_eq_true] at hwf
  rcases hCase with ⟨rfl, initArg, isLt, bnd, stores, rfl, hm, h1, _, rfl⟩ |
      ⟨rfl, initArg, isLt, bnd, stores, rfl, hm, h2, _, rfl⟩
  · obtain ⟨hfbWf, hStsWf⟩ :=
      matchMultiFillBody_wf (GOuter := GOuter) (D := pushTypes [[i32]] DOuter) body
        (GLocal := []) ⟨rfl, fun _ h => by cases h⟩
        (show body.wfCheck ([] ++ (if true then i32 else i64) :: GOuter)
          (pushTypes [[i32]] DOuter) = true from hwf.1) hm
    have hStep := computeMultiStepK_spec unrollN stores hu1 hu64 h1 (fun s hs => (hStsWf s hs).2.2)
    rw [wfCheck_jump_eq, Bool.and_eq_true] at hwf
    have hInitWf : checkArg GOuter i32 initArg = true := by
      simpa [pushTypes, checkArgs] using hwf.2.2
    rw [wfCheck_group_eq, wfCheckB_cons_eq, wfCheckB_nil_eq, Bool.and_true, Bool.and_eq_true]
    exact ⟨hwf.1, wfCheck_mkMultiWideWrapper (Or.inl rfl) hInitWf hfbWf.2
      (fun s hs => ⟨hStsWf s hs, (hStep.2.2 s hs).1⟩)⟩
  · obtain ⟨hfbWf, hStsWf⟩ :=
      matchMultiFillBody_wf (GOuter := GOuter) (D := pushTypes [[i64]] DOuter) body
        (GLocal := []) ⟨rfl, fun _ h => by cases h⟩
        (show body.wfCheck ([] ++ (if false then i32 else i64) :: GOuter)
          (pushTypes [[i64]] DOuter) = true from hwf.1) hm
    have hStep := computeMultiStepK_spec unrollN stores hu1 hu64 (by omega)
      (fun s hs => (hStsWf s hs).2.2)
    rw [wfCheck_jump_eq, Bool.and_eq_true] at hwf
    have hInitWf : checkArg GOuter i64 initArg = true := by
      simpa [pushTypes, checkArgs] using hwf.2.2
    rw [wfCheck_group_eq, wfCheckB_cons_eq, wfCheckB_nil_eq, Bool.and_true, Bool.and_eq_true]
    exact ⟨hwf.1, wfCheck_mkMultiWideWrapper (Or.inr rfl) hInitWf hfbWf.2
      (fun s hs => ⟨hStsWf s hs, (hStep.2.2 s hs).1⟩)⟩

/-! ## Section 3: `SymExt` Relational Semantics & `matchMultiFillBody_spec` -/

@[expose] public def offVal (vsOuter : List ((t : Ty) × Val t)) :
    Option (Arg K i64) → Option (BitVec 64)
  | none => some 0#64
  | some off => (denoteArg vsOuter off).map Arg.val

@[expose] public def incLoopVal :
    (is32 : Bool) → Val (if is32 then i32 else i64) → Val (if is32 then i32 else i64)
  | true, v => show Val i32 from (show BitVec 32 from v) + 1#32
  | false, v => show Val i64 from (show BitVec 64 from v) + 1#64

@[expose] public def loopVal (is32 : Bool) (iVal : Val (if is32 then i32 else i64)) :
    (t : Ty) × Val t :=
  match is32, iVal with
  | true, v => ⟨i32, v⟩
  | false, v => ⟨i64, v⟩

@[expose] public def loopVal64 : (is32 : Bool) → Val (if is32 then i32 else i64) → BitVec 64
  | true, v => v.setWidth 64
  | false, v => v

@[expose] public def loopVal32 : (is32 : Bool) → Val (if is32 then i32 else i64) → BitVec 32
  | true, v => v
  | false, v => v.setWidth 32

@[expose] public def SymExtRel (vsOuter : List ((t : Ty) × Val t)) (is32 : Bool)
    (iVal : Val (if is32 then i32 else i64)) : SymExt → (t : Ty) → Val t → Prop
  | .loopI, t, v => (⟨t, v⟩ : (u : Ty) × Val u) = loopVal is32 iVal
  | .loopZext64, t, v => is32 = true ∧ (⟨t, v⟩ : (u : Ty) × Val u) = ⟨i64, loopVal64 is32 iVal⟩
  | .outer64 idx0, t, v =>
    ∃ a : Arg Val i64, denoteArg vsOuter (.var idx0) = some a ∧
      (⟨t, v⟩ : (u : Ty) × Val u) = ⟨i64, a.val⟩
  | .outer32 idx0, t, v =>
    ∃ a : Arg Val i32, denoteArg vsOuter (.var idx0) = some a ∧
      (⟨t, v⟩ : (u : Ty) × Val u) = ⟨i32, a.val⟩
  | .const64 c, t, v => (⟨t, v⟩ : (u : Ty) × Val u) = ⟨i64, c⟩
  | .const32 c, t, v => (⟨t, v⟩ : (u : Ty) × Val u) = ⟨i32, c⟩
  | .add64 a b, t, v =>
    ∃ va vb : BitVec 64,
      SymExtRel vsOuter is32 iVal a i64 va ∧ SymExtRel vsOuter is32 iVal b i64 vb ∧
      (⟨t, v⟩ : (u : Ty) × Val u) = ⟨i64, va + vb⟩
  | .add32 a b, t, v =>
    ∃ va vb : BitVec 32,
      SymExtRel vsOuter is32 iVal a i32 va ∧ SymExtRel vsOuter is32 iVal b i32 vb ∧
      (⟨t, v⟩ : (u : Ty) × Val u) = ⟨i32, va + vb⟩
  | .shlConst64 a s, t, v =>
    ∃ va : BitVec 64, SymExtRel vsOuter is32 iVal a i64 va ∧
      (⟨t, v⟩ : (u : Ty) × Val u) = ⟨i64, va <<< s⟩
  | .cmpU64 isLt bnd, t, v =>
    is32 = false ∧ ∃ bndA : Arg Val i64, denoteArg vsOuter bnd = some bndA ∧
      (⟨t, v⟩ : (u : Ty) × Val u) =
        ⟨.bool, if isLt then CmpOp.ult.evalBits (loopVal64 is32 iVal) bndA.val
                else CmpOp.ule.evalBits (loopVal64 is32 iVal) bndA.val⟩
  | .cmpU32 isLt bnd, t, v =>
    is32 = true ∧ ∃ bndA : Arg Val i32, denoteArg vsOuter bnd = some bndA ∧
      (⟨t, v⟩ : (u : Ty) × Val u) =
        ⟨.bool, if isLt then CmpOp.ult.evalBits (loopVal32 is32 iVal) bndA.val
                else CmpOp.ule.evalBits (loopVal32 is32 iVal) bndA.val⟩
  | .other, _, _ => True

@[expose] public def SymExtEnvMatch (vsOuter : List ((t : Ty) × Val t)) (is32 : Bool)
    (iVal : Val (if is32 then i32 else i64)) (vsLocal : List ((t : Ty) × Val t))
    (env : Array SymExt) : Prop :=
  env.size = vsLocal.length ∧
    ∀ (idx : Nat) (h : idx < vsLocal.length),
      SymExtRel vsOuter is32 iVal (env[env.size - 1 - idx]!) vsLocal[idx].1 vsLocal[idx].2

public theorem symExtEnvMatch_empty {vsOuter : List ((t : Ty) × Val t)} {is32 : Bool}
    {iVal : Val (if is32 then i32 else i64)} : SymExtEnvMatch vsOuter is32 iVal [] #[] :=
  ⟨rfl, fun _ h => nomatch h⟩

public theorem symExtEnvMatch_push1 {vsOuter : List ((t : Ty) × Val t)} {is32 : Bool}
    {iVal : Val (if is32 then i32 else i64)} {vsLocal : List ((t : Ty) × Val t)}
    {env : Array SymExt} (hm : SymExtEnvMatch vsOuter is32 iVal vsLocal env)
    {t : Ty} {v : Val t} {s : SymExt} (hrel : SymExtRel vsOuter is32 iVal s t v) :
    SymExtEnvMatch vsOuter is32 iVal (⟨t, v⟩ :: vsLocal) (env ++ #[s]) := by
  refine ⟨by rw [Array.size_append, hm.1]; rfl, fun idx hidx => ?_⟩
  cases idx with
  | zero =>
    rw [Array.size_append, show #[s].size = 1 by rfl, Nat.sub_zero,
      Nat.add_sub_cancel, array_getElem!_push_last]
    exact hrel
  | succ k =>
    have hlen := hm.1
    have hk : k < vsLocal.length := by rw [List.length_cons] at hidx; omega
    rw [Array.size_append, show #[s].size = 1 by rfl,
      show env.size + 1 - 1 - (k + 1) = env.size - 1 - k by omega,
      array_getElem!_append_left env #[s] _ (by omega)]
    exact hm.2 k hk

public theorem symExtEnvMatch_push_other {vsOuter : List ((t : Ty) × Val t)} {is32 : Bool}
    {iVal : Val (if is32 then i32 else i64)} {vsLocal : List ((t : Ty) × Val t)}
    {env : Array SymExt} (hm : SymExtEnvMatch vsOuter is32 iVal vsLocal env) :
    {ts : List Ty} → (res : Tup Val ts) → (sy : List SymExt) →
    sy.length = ts.length → (∀ s ∈ sy, s = .other) →
    SymExtEnvMatch vsOuter is32 iVal (pushTup res vsLocal) (env ++ sy.toArray)
  | [], (), [], _, _ => by
    dsimp only [pushTup]
    have hEmpty : [].toArray = (#[] : Array SymExt) := rfl
    rw [hEmpty, Array.append_empty]; exact hm
  | _ :: _, (v, res), s :: sy, hlen, hs => by
    dsimp only [pushTup]
    have h1 := symExtEnvMatch_push1 hm
      (show SymExtRel vsOuter is32 iVal s _ v from (hs s List.mem_cons_self) ▸ trivial)
    rw [List.toArray_cons, ← Array.append_assoc]
    exact symExtEnvMatch_push_other h1 res sy (Nat.succ.inj hlen)
      (fun x hx => hs x (List.mem_cons_of_mem _ hx))

private theorem argToSym_imm_other (is32 : Bool) (env : Array SymExt) {w : Nat}
    (h64 : w ≠ 64) (h32 : w ≠ 32) (c : BitVec w) :
    argToSym is32 env (.imm (t := .bits w) c) = .other := by
  dsimp only [argToSym]
  split <;> simp_all [Ty.bits.injEq]

public theorem argToSym_correct {vsOuter : List ((t : Ty) × Val t)} {is32 : Bool}
    {iVal : Val (if is32 then i32 else i64)} {vsLocal : List ((t : Ty) × Val t)}
    {env : Array SymExt} (hm : SymExtEnvMatch vsOuter is32 iVal vsLocal env)
    {t : Ty} (a : Arg K t) {vA : Arg Val t}
    (hd : denoteArg (vsLocal ++ ⟨if is32 then i32 else i64, iVal⟩ :: vsOuter) a = some vA) :
    SymExtRel vsOuter is32 iVal (argToSym is32 env a) t vA.val := by
  cases a with
  | imm c =>
    dsimp only [denoteArg] at hd; cases hd
    cases t with
    | bool | float _ | pair _ _ => dsimp only [argToSym]; exact trivial
    | bits w =>
      by_cases h64 : w = 64
      · subst h64; rfl
      · by_cases h32 : w = 32
        · subst h32; rfl
        · rw [argToSym_imm_other is32 env h64 h32 c]; exact trivial
  | var idx =>
    rw [argToSym_var]; dsimp only [denoteArg, lookupV] at hd
    rw [listGet?_eq_getElem?] at hd
    have hlen := hm.1; dsimp only [K] at idx hlen
    by_cases hlt : idx < env.size
    · have hltV : idx < vsLocal.length := by omega
      rw [ite_eq_left (by simp [hlt])]
      rw [List.getElem?_append_left hltV, List.getElem?_eq_getElem hltV] at hd
      dsimp only at hd
      cases hC : castTy vsLocal[idx].1 t vsLocal[idx].2 with
      | none => rw [hC] at hd; cases hd
      | some v =>
        rw [hC] at hd; cases hd
        have hElem := castTy_some_eq hC
        have hRel := hm.2 idx hltV
        have h1 : (⟨vsLocal[idx].1, vsLocal[idx].2⟩ : (u : Ty) × Val u) = ⟨t, v⟩ := hElem
        cases h1; exact hRel
    · rw [ite_eq_right (by simp [hlt])]
      have hgeV : vsLocal.length ≤ idx := by omega
      rw [List.getElem?_append_right hgeV] at hd
      by_cases heq : idx = env.size
      · subst heq; rw [ite_eq_left (beq_self_eq_true _)]
        have hSub : env.size - vsLocal.length = 0 := by omega
        rw [hSub, List.getElem?_cons_zero] at hd; dsimp only at hd
        cases hC : castTy (if is32 then i32 else i64) t iVal with
        | none => rw [hC] at hd; cases hd
        | some v =>
          rw [hC] at hd; cases hd
          have hElem := castTy_some_eq hC
          cases is32 with
          | true =>
            by_cases ht32 : t = i32
            · subst ht32; rw [ite_eq_left (by decide)]; exact hElem.symm
            · rw [ite_eq_right (by simp [ht32])]; exact trivial
          | false =>
            by_cases ht64 : t = i64
            · subst ht64; rw [ite_eq_left (by decide)]; exact hElem.symm
            · rw [ite_eq_right (by simp [ht64])]; exact trivial
      · rw [ite_eq_right (by simp [heq])]
        have hSub : idx - vsLocal.length = (idx - (env.size + 1)) + 1 := by omega
        rw [hSub, List.getElem?_cons_succ] at hd
        by_cases ht64 : t = i64
        · subst ht64; rw [ite_eq_left (by decide)]
          cases hGet : vsOuter[idx - (env.size + 1)]? with
          | none => rw [hGet] at hd; cases hd
          | some tv =>
            rw [hGet] at hd; dsimp only at hd
            cases hC : castTy tv.1 i64 tv.2 with
            | none => rw [hC] at hd; cases hd
            | some v =>
              rw [hC] at hd; cases hd
              refine ⟨.var v, ?_, rfl⟩
              dsimp only [denoteArg, lookupV]; rw [listGet?_eq_getElem?, hGet]; dsimp only; rw [hC]
        · rw [ite_eq_right (by simp [ht64])]
          by_cases ht32 : t = i32
          · subst ht32; rw [ite_eq_left (by decide)]
            cases hGet : vsOuter[idx - (env.size + 1)]? with
            | none => rw [hGet] at hd; cases hd
            | some tv =>
              rw [hGet] at hd; dsimp only at hd
              cases hC : castTy tv.1 i32 tv.2 with
              | none => rw [hC] at hd; cases hd
              | some v =>
                rw [hC] at hd; cases hd
                refine ⟨.var v, ?_, rfl⟩
                dsimp only [denoteArg, lookupV]
                rw [listGet?_eq_getElem?, hGet]; dsimp only; rw [hC]
          · rw [ite_eq_right (by simp [ht32])]; exact trivial

private theorem evalSymCmp64_left {vsOuter : List ((t : Ty) × Val t)} {iVal : Val i64}
    (isLt : Bool) {sb : SymExt} {vb : BitVec 64}
    (hb : SymExtRel vsOuter false iVal sb i64 vb) :
    SymExtRel vsOuter false iVal
      ((Option.map (SymExt.cmpU64 isLt) (symToOuterArg64Ext sb)).getD .other)
      .bool (if isLt then CmpOp.ult.evalBits iVal vb else CmpOp.ule.evalBits iVal vb) := by
  cases hs : symToOuterArg64Ext sb with
  | none => exact trivial
  | some bnd =>
    have hOuter : ∃ bndA : Arg Val i64, denoteArg vsOuter bnd = some bndA ∧ vb = bndA.val := by
      cases sb <;> dsimp only [symToOuterArg64Ext] at hs <;> cases hs
      · obtain ⟨a, ha, hEq⟩ := hb; exact ⟨a, ha, sigma_val_eq hEq⟩
      · exact ⟨.imm _, rfl, sigma_val_eq hb⟩
    obtain ⟨bndA, hdb, rfl⟩ := hOuter
    refine ⟨rfl, bndA, hdb, ?_⟩
    cases isLt <;> rfl

private theorem evalSymCmp32_left {vsOuter : List ((t : Ty) × Val t)} {iVal : Val i32}
    (isLt : Bool) {sb : SymExt} {vb : BitVec 32}
    (hb : SymExtRel vsOuter true iVal sb i32 vb) :
    SymExtRel vsOuter true iVal
      ((Option.map (SymExt.cmpU32 isLt) (symToOuterArg32 sb)).getD .other)
      .bool (if isLt then CmpOp.ult.evalBits iVal vb else CmpOp.ule.evalBits iVal vb) := by
  cases hs : symToOuterArg32 sb with
  | none => exact trivial
  | some bnd =>
    have hOuter : ∃ bndA : Arg Val i32, denoteArg vsOuter bnd = some bndA ∧ vb = bndA.val := by
      cases sb <;> dsimp only [symToOuterArg32] at hs <;> cases hs
      · obtain ⟨a, ha, hEq⟩ := hb; exact ⟨a, ha, sigma_val_eq hEq⟩
      · exact ⟨.imm _, rfl, sigma_val_eq hb⟩
    obtain ⟨bndA, hdb, rfl⟩ := hOuter
    refine ⟨rfl, bndA, hdb, ?_⟩
    cases isLt <;> rfl

private theorem evalSymCmpExt64_correct {vsOuter : List ((t : Ty) × Val t)} {iVal : Val i64}
    (o : CmpOp) {sa sb : SymExt} {va vb : BitVec 64}
    (ha : SymExtRel vsOuter false iVal sa i64 va)
    (hb : SymExtRel vsOuter false iVal sb i64 vb) :
    SymExtRel vsOuter false iVal
      ((match o, sa, sb with
        | .ult, .loopI, _ => Option.map (SymExt.cmpU64 true) (symToOuterArg64Ext sb)
        | .ule, .loopI, _ => Option.map (SymExt.cmpU64 false) (symToOuterArg64Ext sb)
        | .ugt, _, .loopI => Option.map (SymExt.cmpU64 true) (symToOuterArg64Ext sa)
        | .uge, _, .loopI => Option.map (SymExt.cmpU64 false) (symToOuterArg64Ext sa)
        | _, _, _ => none).getD .other)
      .bool (o.evalBits va vb) := by
  cases o with
  | ult =>
    cases sa <;>
      first | exact trivial | (rw [sigma_val_eq ha]; exact evalSymCmp64_left true hb)
  | ule =>
    cases sa <;>
      first | exact trivial | (rw [sigma_val_eq ha]; exact evalSymCmp64_left false hb)
  | ugt =>
    cases sb <;>
      first | exact trivial | (rw [sigma_val_eq hb]; exact evalSymCmp64_left true ha)
  | uge =>
    cases sb <;>
      first | exact trivial | (rw [sigma_val_eq hb]; exact evalSymCmp64_left false ha)
  | eq | ne | slt | sle | sgt | sge => exact trivial

private theorem evalSymCmpExt32_correct {vsOuter : List ((t : Ty) × Val t)} {iVal : Val i32}
    (o : CmpOp) {sa sb : SymExt} {va vb : BitVec 32}
    (ha : SymExtRel vsOuter true iVal sa i32 va)
    (hb : SymExtRel vsOuter true iVal sb i32 vb) :
    SymExtRel vsOuter true iVal
      ((match o, sa, sb with
        | .ult, .loopI, _ => Option.map (SymExt.cmpU32 true) (symToOuterArg32 sb)
        | .ule, .loopI, _ => Option.map (SymExt.cmpU32 false) (symToOuterArg32 sb)
        | .ugt, _, .loopI => Option.map (SymExt.cmpU32 true) (symToOuterArg32 sa)
        | .uge, _, .loopI => Option.map (SymExt.cmpU32 false) (symToOuterArg32 sa)
        | _, _, _ => none).getD .other)
      .bool (o.evalBits va vb) := by
  cases o with
  | ult =>
    cases sa <;>
      first | exact trivial | (rw [sigma_val_eq ha]; exact evalSymCmp32_left true hb)
  | ule =>
    cases sa <;>
      first | exact trivial | (rw [sigma_val_eq ha]; exact evalSymCmp32_left false hb)
  | ugt =>
    cases sb <;>
      first | exact trivial | (rw [sigma_val_eq hb]; exact evalSymCmp32_left true ha)
  | uge =>
    cases sb <;>
      first | exact trivial | (rw [sigma_val_eq hb]; exact evalSymCmp32_left false ha)
  | eq | ne | slt | sle | sgt | sge => exact trivial

private theorem evalSymOpExt_push_other {vsOuter : List ((t : Ty) × Val t)} {is32 : Bool}
    {iVal : Val (if is32 then i32 else i64)} {vsLocal : List ((t : Ty) × Val t)}
    {env : Array SymExt} (hm : SymExtEnvMatch vsOuter is32 iVal vsLocal env)
    {ts : List Ty} (op : Op K ts) {valArgs : Tup (Arg Val) op.sig} {P : Tup Val ts → Prop}
    (hwp : op.code.wp (vals valArgs) P)
    (hOth : evalSymOpExt is32 env op = ts.map fun _ => SymExt.other) :
    ∃ res : Tup Val ts, P res ∧
      SymExtEnvMatch vsOuter is32 iVal (pushTup res vsLocal)
        (env ++ (evalSymOpExt is32 env op).toArray) := by
  obtain ⟨res, hRes⟩ := OpCode.wp_exists _ _ hwp
  refine ⟨res, hRes, hOth ▸ symExtEnvMatch_push_other hm res _ (List.length_map ..) ?_⟩
  intro s hs; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hs; rfl

private theorem pushTup_singleton {t : Ty} (x : Val t) (vs : List ((u : Ty) × Val u)) :
    pushTup (as := [t]) (x, ()) vs = ⟨t, x⟩ :: vs := rfl

private theorem denoteArgs_singleton_some {V : Ty → Type}
    {vs : List ((t : Ty) × V t)} {t : Ty} {a : Arg K t} {va : Arg V t}
    (h : denoteArgs vs (ts := [t]) (a, ()) = some (va, ())) : denoteArg vs a = some va := by
  rw [denoteArgs_singleton_eq] at h
  cases hd : denoteArg vs a <;> simp_all

private theorem denoteArgs_pair_some {V : Ty → Type}
    {vs : List ((t : Ty) × V t)} {t₁ t₂ : Ty} {a : Arg K t₁} {b : Arg K t₂}
    {va : Arg V t₁} {vb : Arg V t₂}
    (h : denoteArgs vs (ts := [t₁, t₂]) (a, b, ()) = some (va, vb, ())) :
    denoteArg vs a = some va ∧ denoteArg vs b = some vb := by
  rw [denoteArgs_pair_eq] at h
  cases hda : denoteArg vs a <;> cases hdb : denoteArg vs b <;> simp_all

public theorem evalSymOpExt_wp {vsOuter : List ((t : Ty) × Val t)} {is32 : Bool}
    {iVal : Val (if is32 then i32 else i64)} {vsLocal : List ((t : Ty) × Val t)}
    {env : Array SymExt} (hm : SymExtEnvMatch vsOuter is32 iVal vsLocal env)
    {ts : List Ty} (op : Op K ts) {valArgs : Tup (Arg Val) op.sig}
    (hargs : denoteArgs (vsLocal ++ ⟨if is32 then i32 else i64, iVal⟩ :: vsOuter) op.args =
      some valArgs)
    {P : Tup Val ts → Prop} (hwp : op.code.wp (vals valArgs) P) :
    ∃ res : Tup Val ts, P res ∧
      SymExtEnvMatch vsOuter is32 iVal (pushTup res vsLocal)
        (env ++ (evalSymOpExt is32 env op).toArray) := by
  have hNone {ts' : List Ty} {op' : Op K ts'} {va' : Tup (Arg Val) op'.sig}
      {P' : Tup Val ts' → Prop} (hw' : op'.code.wp (vals va') P')
      (h1 : evalSymOp1Ext is32 env op' = none) :
      ∃ res : Tup Val ts', P' res ∧
        SymExtEnvMatch vsOuter is32 iVal (pushTup res vsLocal)
          (env ++ (evalSymOpExt is32 env op').toArray) :=
    evalSymOpExt_push_other hm op' hw' (by
      dsimp only [evalSymOpExt]; rw [h1]
      cases ts' with | nil => rfl | cons _ tl => cases tl <;> rfl)
  rcases op with ⟨code, args⟩; dsimp only at valArgs hargs hwp
  cases code with
  | copy t =>
    rcases args with ⟨a, ⟨⟩⟩; rcases valArgs with ⟨va, ⟨⟩⟩
    have hda := denoteArgs_singleton_some hargs
    by_cases ht64 : t = i64
    · subst ht64; rw [OpCode.wp_copy] at hwp; dsimp only [vals, Arg.val] at hwp
      refine ⟨(va.val, ()), hwp, ?_⟩
      dsimp only [evalSymOpExt, evalSymOp1Ext]; rw [dite_eq_left rfl, pushTup_singleton]
      exact symExtEnvMatch_push1 hm (argToSym_correct hm a hda)
    · by_cases ht32 : t = i32
      · subst ht32; rw [OpCode.wp_copy] at hwp; dsimp only [vals, Arg.val] at hwp
        refine ⟨(va.val, ()), hwp, ?_⟩
        dsimp only [evalSymOpExt, evalSymOp1Ext]
        rw [dite_eq_right ht64, dite_eq_left rfl, pushTup_singleton]
        exact symExtEnvMatch_push1 hm (argToSym_correct hm a hda)
      · exact hNone hwp (by dsimp only [evalSymOp1Ext]; rw [dite_eq_right ht64, dite_eq_right ht32])
  | zext m n =>
    rcases args with ⟨a, ⟨⟩⟩; rcases valArgs with ⟨va, ⟨⟩⟩
    have hda := denoteArgs_singleton_some hargs
    by_cases hm32 : m = 32
    · subst hm32
      by_cases hn64 : n = 64
      · subst hn64
        cases hsa : argToSym is32 env a with
        | loopI =>
          cases is32
          · exact hNone hwp (by dsimp only [evalSymOp1Ext]; rw [dite_eq_left rfl, hsa]; rfl)
          · rw [OpCode.wp_zext] at hwp; dsimp only [vals, Arg.val] at hwp
            refine ⟨(va.val.setWidth 64, ()), hwp.2, ?_⟩
            have hEval : evalSymOpExt true env
                ⟨.zext 32 64, (a, ())⟩ = [SymExt.loopZext64] := by
              dsimp only [evalSymOpExt, evalSymOp1Ext]; rw [dite_eq_left rfl, hsa]; rfl
            rw [hEval]
            have hRel := argToSym_correct hm a hda; rw [hsa] at hRel
            have hEq := sigma_val_eq hRel
            exact symExtEnvMatch_push1 hm (t := i64) ⟨rfl, by rw [hEq]; rfl⟩
        | _ =>
          exact hNone hwp (by dsimp only [evalSymOp1Ext]; rw [dite_eq_left rfl, hsa]; rfl)
      · exact hNone hwp (by
          dsimp only [evalSymOp1Ext]; rw [dite_eq_left rfl, ite_eq_right (by simp [hn64])])
    · exact hNone hwp (by dsimp only [evalSymOp1Ext]; rw [dite_eq_right hm32])
  | add t =>
    rcases args with ⟨a, b, ⟨⟩⟩; rcases valArgs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨hda, hdb⟩ := denoteArgs_pair_some hargs
    by_cases ht64 : t = i64
    · subst ht64
      rw [OpCode.wp_add] at hwp; dsimp only [lift2, vals, Arg.val, i64, Ty.hasFloat] at hwp
      refine ⟨(va.val + vb.val, ()), hwp, ?_⟩
      dsimp only [evalSymOpExt, evalSymOp1Ext]; rw [dite_eq_left rfl, pushTup_singleton]
      exact symExtEnvMatch_push1 hm
        ⟨va.val, vb.val, argToSym_correct hm a hda, argToSym_correct hm b hdb, rfl⟩
    · by_cases ht32 : t = i32
      · subst ht32
        rw [OpCode.wp_add] at hwp; dsimp only [lift2, vals, Arg.val, i32, Ty.hasFloat] at hwp
        refine ⟨(va.val + vb.val, ()), hwp, ?_⟩
        dsimp only [evalSymOpExt, evalSymOp1Ext]
        rw [dite_eq_right ht64, dite_eq_left rfl, pushTup_singleton]
        exact symExtEnvMatch_push1 hm
          ⟨va.val, vb.val, argToSym_correct hm a hda, argToSym_correct hm b hdb, rfl⟩
      · exact hNone hwp (by dsimp only [evalSymOp1Ext]; rw [dite_eq_right ht64, dite_eq_right ht32])
  | shl t =>
    rcases args with ⟨a, b, ⟨⟩⟩; rcases valArgs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨hda, hdb⟩ := denoteArgs_pair_some hargs
    by_cases ht64 : t = i64
    · subst ht64
      cases hsb : argToSym is32 env b with
      | const64 c =>
        rw [OpCode.wp_shl] at hwp; dsimp only [lift2, vals, Arg.val, i64, Ty.hasFloat] at hwp
        have hrelB := argToSym_correct hm b hdb; rw [hsb] at hrelB
        refine ⟨(va.val <<< (vb.val.toNat % 64), ()), hwp, ?_⟩
        have hEval : evalSymOpExt is32 env ⟨.shl i64, (a, b, ())⟩ =
            [SymExt.shlConst64 (argToSym is32 env a) (c.toNat % 64)] := by
          dsimp only [evalSymOpExt, evalSymOp1Ext]; rw [dite_eq_left rfl, hsb]
        rw [hEval]
        exact symExtEnvMatch_push1 hm (t := i64)
          ⟨va.val, argToSym_correct hm a hda, by rw [sigma_val_eq hrelB]⟩
      | _ =>
        exact evalSymOpExt_push_other hm _ hwp
          (by dsimp only [evalSymOpExt, evalSymOp1Ext]; rw [dite_eq_left rfl, hsb]; rfl)
    · exact hNone hwp (by dsimp only [evalSymOp1Ext]; rw [dite_eq_right ht64])
  | cmp o t m h =>
    subst h; rcases args with ⟨a, b, ⟨⟩⟩; rcases valArgs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨hda, hdb⟩ := denoteArgs_pair_some hargs
    by_cases ht64 : t = i64
    · subst ht64
      cases is32
      · rw [OpCode.wp_cmp _ _ rfl] at hwp
        dsimp only [liftCmp, vals, Arg.val, i64, Ty.hasFloat] at hwp
        refine ⟨(o.evalBits va.val vb.val, ()), hwp, ?_⟩
        dsimp only [evalSymOpExt, evalSymOp1Ext]
        rw [dite_eq_left rfl, pushTup_singleton (t := i64.mask)]
        exact symExtEnvMatch_push1 hm
          (evalSymCmpExt64_correct o (argToSym_correct hm a hda) (argToSym_correct hm b hdb))
      · exact hNone hwp (by dsimp only [evalSymOp1Ext]; rw [dite_eq_left rfl]; rfl)
    · by_cases ht32 : t = i32
      · subst ht32
        cases is32
        · exact hNone hwp (by
            dsimp only [evalSymOp1Ext]; rw [dite_eq_right ht64, dite_eq_left rfl]; rfl)
        · rw [OpCode.wp_cmp _ _ rfl] at hwp
          dsimp only [liftCmp, vals, Arg.val, i32, Ty.hasFloat] at hwp
          refine ⟨(o.evalBits va.val vb.val, ()), hwp, ?_⟩
          dsimp only [evalSymOpExt, evalSymOp1Ext]
          rw [dite_eq_right ht64, dite_eq_left rfl, pushTup_singleton (t := i32.mask)]
          exact symExtEnvMatch_push1 hm
            (evalSymCmpExt32_correct o (argToSym_correct hm a hda) (argToSym_correct hm b hdb))
      · exact hNone hwp (by
          dsimp only [evalSymOp1Ext]; rw [dite_eq_right ht64, dite_eq_right ht32])
  | _ => exact hNone hwp rfl

private theorem symToOuterArg64Ext_correct {vsOuter : List ((t : Ty) × Val t)} {is32 : Bool}
    {iVal : Val (if is32 then i32 else i64)} {s : SymExt} {v : BitVec 64} {a : Arg K i64}
    (hrel : SymExtRel vsOuter is32 iVal s i64 v) (hsym : symToOuterArg64Ext s = some a) :
    ∃ aVal : Arg Val i64, denoteArg vsOuter a = some aVal ∧ v = aVal.val := by
  cases s <;> dsimp only [symToOuterArg64Ext] at hsym <;> cases hsym
  · obtain ⟨aVal, ha, hEq⟩ := hrel; exact ⟨aVal, ha, sigma_val_eq hEq⟩
  · exact ⟨.imm _, rfl, sigma_val_eq hrel⟩

private theorem matchOffLoopExt_correct {vsOuter : List ((t : Ty) × Val t)} {is32 : Bool}
    {iVal : Val (if is32 then i32 else i64)} {s : SymExt} {v : BitVec 64}
    {off? : Option (Arg K i64)} (hrel : SymExtRel vsOuter is32 iVal s i64 v)
    (hm : matchOffLoopExt is32 s = some off?) :
    ∃ oVal : BitVec 64, offVal vsOuter off? = some oVal ∧ v = loopVal64 is32 iVal + oVal := by
  have addArm : ∀ (sa sb : SymExt) {va vb : BitVec 64},
      isLoopIdx64 is32 sa = true →
      SymExtRel vsOuter is32 iVal sa i64 va → SymExtRel vsOuter is32 iVal sb i64 vb →
      Option.map some (symToOuterArg64Ext sb) = some off? →
      ∃ oVal : BitVec 64,
        offVal vsOuter off? = some oVal ∧ va + vb = loopVal64 is32 iVal + oVal := by
    intro sa sb va vb hloop ha hb hmap
    rcases Option.map_eq_some_iff.mp hmap with ⟨off, hoff, rfl⟩
    obtain ⟨offA, hd, rfl⟩ := symToOuterArg64Ext_correct hb hoff
    have hva : va = loopVal64 is32 iVal := by
      cases sa <;> cases is32 <;> simp [isLoopIdx64] at hloop
      · exact sigma_val_eq ha
      · exact sigma_val_eq ha.2
    subst hva; exact ⟨offA.val, by dsimp only [offVal]; rw [hd]; rfl, rfl⟩
  cases s with
  | loopI =>
    dsimp only [matchOffLoopExt] at hm
    cases is32 <;> simp [isLoopIdx64] at hm
    subst hm; exact ⟨0#64, rfl, by rw [BitVec.add_zero]; exact sigma_val_eq hrel⟩
  | loopZext64 =>
    dsimp only [matchOffLoopExt] at hm
    cases is32 <;> simp [isLoopIdx64] at hm
    subst hm; exact ⟨0#64, rfl, by rw [BitVec.add_zero]; exact sigma_val_eq hrel.2⟩
  | add64 a b =>
    rcases hrel with ⟨va, vb, ha, hb, hEq⟩
    have hv := sigma_val_eq hEq; subst hv
    dsimp only [matchOffLoopExt] at hm
    by_cases hlA : isLoopIdx64 is32 a = true
    · rw [ite_eq_left hlA] at hm; exact addArm a b hlA ha hb hm
    · rw [ite_eq_right hlA] at hm
      by_cases hlB : isLoopIdx64 is32 b = true
      · rw [ite_eq_left hlB] at hm
        obtain ⟨oVal, ho, hSum⟩ := addArm b a hlB hb ha hm
        exact ⟨oVal, ho, by rw [BitVec.add_comm, hSum]⟩
      · rw [ite_eq_right hlB] at hm; cases hm
  | _ => dsimp only [matchOffLoopExt] at hm; cases hm

public theorem matchAddrExt_correct {vsOuter : List ((t : Ty) × Val t)} {is32 : Bool}
    {iVal : Val (if is32 then i32 else i64)} {sExpected : Nat} {s : SymExt} {v : BitVec 64}
    {base : Arg K i64} {off? : Option (Arg K i64)}
    (hrel : SymExtRel vsOuter is32 iVal s i64 v)
    (hm : matchAddrExt is32 sExpected s = some (base, off?)) :
    ∃ (baseVal : Arg Val i64) (oVal : BitVec 64),
      denoteArg vsOuter base = some baseVal ∧ offVal vsOuter off? = some oVal ∧
      v = baseVal.val + ((loopVal64 is32 iVal + oVal) <<< sExpected) := by
  cases s with
  | add64 x y =>
    rcases hrel with ⟨vx, vy, hx, hy, hEq⟩
    have hv := sigma_val_eq hEq; subst hv
    let check (sp sidx : SymExt) : Option (Arg K i64 × Option (Arg K i64)) :=
      match symToOuterArg64Ext sp with
      | some base =>
        if sExpected == 0 then (matchOffLoopExt is32 sidx).map (base, ·)
        else match sidx with
          | .shlConst64 inner s =>
            if s == sExpected then (matchOffLoopExt is32 inner).map (base, ·) else none
          | _ => none
      | none => none
    have check_ok : ∀ sp sidx vp vidx,
        SymExtRel vsOuter is32 iVal sp i64 vp → SymExtRel vsOuter is32 iVal sidx i64 vidx →
        check sp sidx = some (base, off?) →
        ∃ (baseVal : Arg Val i64) (oVal : BitVec 64),
          denoteArg vsOuter base = some baseVal ∧ offVal vsOuter off? = some oVal ∧
          vp + vidx = baseVal.val + ((loopVal64 is32 iVal + oVal) <<< sExpected) := by
      intro sp sidx vp vidx hp hidx hc; dsimp only [check] at hc
      cases ho : symToOuterArg64Ext sp with
      | none => rw [ho] at hc; cases hc
      | some base' =>
        rw [ho] at hc; dsimp only at hc
        obtain ⟨baseVal, hdB, rfl⟩ := symToOuterArg64Ext_correct hp ho
        by_cases hz : sExpected = 0
        · subst hz; rw [ite_eq_left (by decide)] at hc
          rcases Option.map_eq_some_iff.mp hc with ⟨off'', hoff, hpair⟩
          cases hpair
          obtain ⟨oVal, hO, rfl⟩ := matchOffLoopExt_correct hidx hoff
          exact ⟨baseVal, oVal, hdB, hO, by rw [BitVec.shiftLeft_zero]⟩
        · rw [ite_eq_right (by simp [hz])] at hc
          cases sidx with
          | shlConst64 inner s =>
            dsimp only at hc
            by_cases hs : s = sExpected
            · subst hs; rw [ite_eq_left (beq_self_eq_true s)] at hc
              rcases Option.map_eq_some_iff.mp hc with ⟨off'', hoff, hpair⟩
              cases hpair
              rcases hidx with ⟨va, ha, hEq⟩
              have hvidx := sigma_val_eq hEq; subst hvidx
              obtain ⟨oVal, hO, rfl⟩ := matchOffLoopExt_correct ha hoff
              exact ⟨baseVal, oVal, hdB, hO, rfl⟩
            · rw [ite_eq_right (by simp [hs])] at hc; cases hc
          | _ => cases hc
    change (match check x y with | some r => some r | none => check y x) = some (base, off?) at hm
    cases hc1 : check x y with
    | some r => rw [hc1] at hm; cases hm; exact check_ok x y vx vy hx hy hc1
    | none =>
      rw [hc1] at hm
      obtain ⟨bV, oV, hd, ho, hSum⟩ := check_ok y x vy vx hy hx hm
      exact ⟨bV, oV, hd, ho, by rw [BitVec.add_comm, hSum]⟩
  | _ => dsimp only [matchAddrExt] at hm; cases hm

public theorem matchInc1Ext_correct {vsOuter : List ((t : Ty) × Val t)} {is32 : Bool}
    {iVal : Val (if is32 then i32 else i64)} {s : SymExt} {t : Ty} {v : Val t}
    (hrel : SymExtRel vsOuter is32 iVal s t v) (hm : matchInc1Ext is32 s = true) :
    (⟨t, v⟩ : (u : Ty) × Val u) = loopVal is32 (incLoopVal is32 iVal) := by
  dsimp only [matchInc1Ext] at hm
  split at hm
  · rcases hrel with ⟨va, vb, ha, hb, hEq⟩
    cases is32
    · cases hm
    · rw [sigma_val_eq ha, sigma_val_eq hb] at hEq; exact hEq
  · rcases hrel with ⟨va, vb, ha, hb, hEq⟩
    cases is32
    · cases hm
    · rw [sigma_val_eq ha, sigma_val_eq hb, BitVec.add_comm] at hEq; exact hEq
  · rcases hrel with ⟨va, vb, ha, hb, hEq⟩
    cases is32
    · rw [sigma_val_eq ha, sigma_val_eq hb] at hEq; exact hEq
    · cases hm
  · rcases hrel with ⟨va, vb, ha, hb, hEq⟩
    cases is32
    · rw [sigma_val_eq ha, sigma_val_eq hb, BitVec.add_comm] at hEq; exact hEq
    · cases hm
  · cases hm

public theorem checkJump0Inc1Ext_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vsOuter : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {is32 : Bool} {JLoop : Cont [if is32 then i32 else i64]} :
    (cont : TFlat rs) →
    ∀ {vsLocal : List ((t : Ty) × Val t)} {env : Array SymExt}
      {iVal : Val (if is32 then i32 else i64)} {m : Mem 64},
      checkJump0Inc1Ext is32 env cont = true →
      SymExtEnvMatch vsOuter is32 iVal vsLocal env →
      wp Γ Q X (denote Val Cont cont
        (vsLocal ++ ⟨if is32 then i32 else i64, iVal⟩ :: vsOuter)
        (⟨[if is32 then i32 else i64], JLoop⟩ :: ls)) m →
      JLoop (incLoopVal is32 iVal, ()) m
  | .let_ op k, vsLocal, env, iVal, m, hChk, hm, hwp => by
    dsimp only [checkJump0Inc1Ext] at hChk; rw [Bool.and_eq_true] at hChk
    rw [denote_let_eq] at hwp
    cases hda : denoteArgs (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) op.args with
    | none => rw [hda] at hwp; exact False.elim (wp_hlt_false hwp)
    | some valArgs =>
      rw [hda] at hwp; dsimp only [Op.wp] at hwp; rw [wp_let] at hwp
      obtain ⟨res, hP, hm'⟩ := evalSymOpExt_wp hm op hda hwp
      rw [pushTup_append_assoc] at hP
      exact checkJump0Inc1Ext_wp k hChk.2 hm' hP
  | .jump (ts := ts) j args, vsLocal, env, iVal, m, hChk, hm, hwp => by
    cases j with
    | succ _ => simp [checkJump0Inc1Ext] at hChk
    | zero =>
      rcases ts with _ | ⟨t0, _ | _⟩
      · simp [checkJump0Inc1Ext] at hChk
      · cases t0 with
        | bits w =>
          rcases args with ⟨nextArg, ⟨⟩⟩
          change ((w == (if is32 then 32 else 64)) &&
            matchInc1Ext is32 (argToSym is32 env nextArg)) = true at hChk
          rw [Bool.and_eq_true] at hChk
          have hw : w = if is32 then 32 else 64 := by simp_all
          subst hw
          have hTy : Ty.bits (if is32 then 32 else 64) = if is32 then i32 else i64 := by
            cases is32 <;> rfl
          rw [denote_jump_eq, denoteArgs_singleton_eq] at hwp
          have hL : lookupL (⟨[if is32 then i32 else i64], JLoop⟩ :: ls)
              [.bits (if is32 then 32 else 64)] 0 = some (hTy ▸ JLoop) := by
            dsimp only [lookupL, listGet?]; cases is32 <;> exact castListTy_self _ _
          cases hda : denoteArg (vsLocal ++ ⟨_, iVal⟩ :: vsOuter) nextArg with
          | none => rw [hL, hda] at hwp; exact False.elim (wp_hlt_false hwp)
          | some nextA =>
            rw [hL, hda] at hwp; dsimp only at hwp; rw [wp_jump] at hwp; dsimp only [vals] at hwp
            have hInc := matchInc1Ext_correct (argToSym_correct hm nextArg hda) hChk.2
            cases is32 with
            | false =>
              have hv : nextA.val = incLoopVal false iVal := sigma_val_eq hInc
              rw [hv] at hwp; exact hwp
            | true =>
              have hv : nextA.val = incLoopVal true iVal := sigma_val_eq hInc
              rw [hv] at hwp; exact hwp
        | bool | float _ | pair _ _ => simp [checkJump0Inc1Ext] at hChk
      · simp [checkJump0Inc1Ext] at hChk
  | .load _ _ _, _, _, _, _, hChk, _, _ | .store _ _ _, _, _, _, _, hChk, _, _
  | .call _ _ _ _, _, _, _, _, hChk, _, _ | .jnz _ _ _, _, _, _, _, hChk, _, _
  | .ret _, _, _, _, _, hChk, _, _ | .exit _ _, _, _, _, _, hChk, _, _
  | .hlt, _, _, _, _, hChk, _, _ | .group _ _, _, _, _, _, hChk, _, _ => by
    dsimp only [checkJump0Inc1Ext] at hChk; cases hChk

end ZeroPeel

end LeanQbe.T
