module

public import LeanQbe.T.LeanLCNF.Sem.HBase
public import LeanQbe.T.LeanLCNF.Sem.HPrim

/-!
# Tier-H (Heap / RC) Weakest-Precondition Semantics for Impure `LeanLCNF`

Re-exports `HBase` (`Word`, `HState`, `HState.mem`, `HInv`, `HPost`, `HXPost`, `HSpec`, `HEnv`,
`HJEnv`, `HValEnv`, `HDecN`) and `HPrim` (`isPrimName`, `HPrim.wp`, `HPrim.wp_mono`), and defines:

1. **Heap semantics (`HVal.wp`, `HWp`)**: env-parametric, total, structurally recursive WP over
   `LcCode` covering all Phase-1 constructs, join points via lfp, and `lcnf_panic` via `HXPost`.
2. **Lifting into `LeanQbe.T`**: `liftSpec`, `liftDeclSpec`, `liftEnv`, `HModuleOk`,
   `HModuleOkIdx` (for both acyclic `LinkedCert` and measure-indexed `BudgetEnv.semScc`).
3. **Core metatheory**: `HVal.wp_conseq`, `HWp_conseq`, `HWp_mono`, `HWp_env_mono`, `HWp_jp_mono`,
   `HWp_frame_pure`, `HWp_jp_loop`, `HWp_jp_rule`, `liftSpec_mono`, `liftDeclSpec_mono`,
   `liftSpec_of_le`, `liftDeclSpec_of_le`, `liftSpec_frame`, `liftEnv_mono`, `liftEnv_of_mem`,
   and `liftDeclSpec_iff_liftSpec_of_le`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open Std.ExtHashMap

/-! ## 1. `HVal.wp` and `HWp` (Total, Structurally Recursive Tier-H WP) -/

/-- Weakest precondition of `LcVal` bound at type `ty`. -/
@[expose] def HVal.wp (Δ : HEnv) (rt : BitVec 64) (ρ : HValEnv) (ty : LcTy)
    (v : LcVal) (K : HPost) (X : HXPost) (σ : HState) : Prop :=
  match v with
  | .lit (.nat n) =>
    if n < 2 ^ 63 then K (Word.i64 (BitVec.ofNat 64 (2 * n + 1))) σ
    else
      ∀ p st' objs',
        st'.PreservesMetaExceptBaEmpty σ.st → st'.rem ≤ σ.st.rem →
        natRep p n objs' → (∀ o ∈ σ.objs, o ∈ objs') →
        K (Word.i64 p) { σ with st := st', objs := objs' }
  | .lit (.scalar n) => K ⟨ty.toTTy, BitVec.ofNat ty.width n⟩ σ
  | .lit (.str s) =>
    ∀ p st' objs',
      st'.PreservesMetaExceptBaEmpty σ.st → st'.rem ≤ σ.st.rem →
      (∃ o ∈ objs', o.addr = p ∧ StrCanon o ∧ o.rc = 0#32 ∧
        strPayload o = s.toUTF8.toList ∧ o.strLen = s.length) →
      (∀ o ∈ σ.objs, o ∈ objs') →
      K (Word.i64 p) { σ with st := st', objs := objs' }
  | .erased => K ⟨ty.toTTy, BitVec.ofNat ty.width (if ty.isScalar then 0 else 1)⟩ σ
  | .ap f as =>
    match ρ.evalArgOwn (.var f), ρ.evalArgsOwn as with
    | some fw, some ws =>
      ∃ (P : HPost) (E : HXPost),
        Δ (applySym as.length) (fw :: ws) σ P E ∧
        (∀ r σ', P r σ' → K r σ') ∧ (∀ c σ', E c σ' → X c σ')
    | _, _ => False
  | .ctor ci as =>
    if ci.isScalar then
      K ⟨ty.toTTy, BitVec.ofNat ty.width (if ty.isScalar then ci.cidx else 2 * ci.cidx + 1)⟩ σ
    else
      match ρ.evalObjArgs as with
      | none => False
      | some vs =>
        vs.length = ci.size ∧ ci.cidx ≤ 244 ∧ ci.size < 256 ∧
        rtMinObjBytes ≤ ci.byteSize ∧ ci.byteSize < 65536 ∧
        canAllocBytes σ.st ci.byteSize ∧
        ∀ (p : BitVec 64) (st' : RtC0State) (scal : List UInt8),
          p ≠ 0#64 → p.toNat % 8 = 0 → (∀ o ∈ σ.objs, o.addr ≠ p) →
          st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem → σ.st.rem - ci.byteSize ≤ st'.rem →
          scal.length = 8 * ci.usize + ci.ssize →
          let newObj : LcnfObj :=
            { addr := p, rc := 1#32, csSz := ci.byteSize, other := ci.size, tag := ci.cidx,
              fields := vs, scalarData := scal }
          K (Word.i64 p) { σ with st := st', objs := newObj :: σ.objs }
  | .oproj i x =>
    match ρ.getBV64? x with
    | some addr =>
      ∃ o ∈ σ.objs, o.addr = addr ∧ o.tag ≤ 244 ∧
        ∃ hi : i < o.fields.length, K (Word.i64 (o.fields[i]'hi)) σ
    | none => False
  | .uproj i x =>
    match ρ.getBV64? x with
    | some addr =>
      ∃ o ∈ σ.objs, o.addr = addr ∧ o.Wf ∧ o.tag ≤ 244 ∧ o.fields.length ≤ i ∧
        let bOff := 8 * (i - o.fields.length)
        bOff + 8 ≤ o.scalarData.length ∧ K (Word.i64 (readBitsLE 64 o.scalarData bOff)) σ
    | none => False
  | .sproj n off x =>
    match ρ.getBV64? x with
    | some addr =>
      ∃ o ∈ σ.objs, o.addr = addr ∧ o.Wf ∧ o.tag ≤ 244 ∧ o.fields.length ≤ n ∧
        let bOff := 8 * (n - o.fields.length) + off
        bOff + ty.toTTy.bytes ≤ o.scalarData.length ∧
        K ⟨ty.toTTy, readBitsLE ty.width o.scalarData bOff⟩ σ
    | none => False
  | .fap f as =>
    match ρ.evalArgsOwn as with
    | none => False
    | some ws =>
      if isPrimName f then HPrim.wp rt f ws K X σ
      else
        ∃ (P : HPost) (E : HXPost),
          Δ f ws σ P E ∧
          (∀ r σ', P r σ' → ∃ r', r.toWidth ty.width = some r' ∧ K r' σ') ∧
          (∀ c σ', E c σ' → X c σ')
  | .pap _ _ => False
  | .reset n x =>
    match ρ.getBV64? x with
    | some addr =>
      ∃ (idx : Nat) (hidx : idx < σ.objs.length),
        let o := σ.objs[idx]'hidx
        o.addr = addr ∧ o.tag ≤ 244 ∧ n ≤ o.fields.length ∧
        if o.rc = 1#32 then HResetRelease addr n K n σ
        else HDecN addr .object false 1 (K (Word.i64 1#64)) σ
    | none => False
  | .reuse x ci upd as =>
    match ρ.getBV64? x, ρ.evalObjArgs as with
    | some addr, some vs =>
      if (addr &&& 1#64) ≠ 0#64 then
        vs.length = ci.size ∧ ci.cidx ≤ 244 ∧ ci.size < 256 ∧
        rtMinObjBytes ≤ ci.byteSize ∧ ci.byteSize < 65536 ∧
        canAllocBytes σ.st ci.byteSize ∧
        ∀ (p : BitVec 64) (st' : RtC0State) (scal : List UInt8),
          p ≠ 0#64 → p.toNat % 8 = 0 → (∀ o ∈ σ.objs, o.addr ≠ p) →
          st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem → σ.st.rem - ci.byteSize ≤ st'.rem →
          scal.length = 8 * ci.usize + ci.ssize →
          let newObj : LcnfObj :=
            { addr := p, rc := 1#32, csSz := ci.byteSize, other := ci.size, tag := ci.cidx,
              fields := vs, scalarData := scal }
          K (Word.i64 p) { σ with st := st', objs := newObj :: σ.objs }
      else
        ∃ (idx : Nat) (hidx : idx < σ.objs.length),
          let o := σ.objs[idx]'hidx
          o.addr = addr ∧ o.tag ≤ 244 ∧ ci.cidx ≤ 244 ∧ vs.length = o.fields.length ∧
          let o' : LcnfObj := { o with tag := if upd then ci.cidx else o.tag, fields := vs }
          K (Word.i64 addr) { σ with objs := σ.objs.set idx o' }
    | _, _ => False
  | .box t x =>
    match ρ.evalArgAt (.var x) t with
    | none => False
    | some w =>
      match t with
      | .uint64 | .usize | .float =>
        match w.toBV64? with
        | none => False
        | some v =>
          canAllocBytes σ.st 16 ∧
          ∀ (p : BitVec 64) (st' : RtC0State),
            p ≠ 0#64 → p.toNat % 8 = 0 → (∀ o ∈ σ.objs, o.addr ≠ p) →
            st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem → σ.st.rem - 16 ≤ st'.rem →
            let newObj : LcnfObj :=
              { addr := p, rc := 1#32, csSz := 16, other := 0, tag := 0,
                scalarData := writeNatLE v.toNat 8 }
            K (Word.i64 p) { σ with st := st', objs := newObj :: σ.objs }
      | .uint8 | .uint16 | .uint32 =>
        match (w.toWidth 64).bind Word.toBV64? with
        | some x64 => K (Word.i64 ((x64 <<< 1) ||| 1#64)) σ
        | none => False
      | _ => K w σ
  | .unbox x =>
    match ρ.getBV64? x with
    | some addr =>
      match ty with
      | .uint64 | .usize | .float =>
        ∃ o ∈ σ.objs, o.addr = addr ∧ o.Wf ∧ o.tag = 0 ∧ o.fields = [] ∧
          8 ≤ o.scalarData.length ∧ K (Word.i64 (readBitsLE 64 o.scalarData 0)) σ
      | _ => K ⟨ty.toTTy, (addr >>> 1).setWidth ty.width⟩ σ
    | none => False
  | .isShared x =>
    match ρ.getBV64? x with
    | some addr =>
      ∃ o ∈ σ.objs, o.addr = addr ∧ K (Word.i8 (if o.rc ≠ 1#32 then 1#8 else 0#8)) σ
    | none => False

mutual
/-- Total-correctness Tier-H weakest precondition of impure `LcCode`. -/
@[expose] def HWp (Δ : HEnv) (rt : BitVec 64) (retTy : LcTy)
    (J : HJEnv) (ρ : HValEnv) (Q : HPost) (X : HXPost) : LcCode → HState → Prop
  | .let_ x ty v k, σ =>
    HVal.wp Δ rt ρ ty v (fun r σ' => HWp Δ rt retTy J (ρ.set x ty r) Q X k σ') X σ
  | .jp j ps body k, σ =>
    ∀ (Jj : List Word → HState → Prop),
      (∀ as σ', paramsMatch ps as →
        HWp Δ rt retTy (J.set j Jj) (ρ.bindAll ps as) Q X body σ' → Jj as σ') →
      HWp Δ rt retTy (J.set j Jj) ρ Q X k σ
  | .jmp j as, σ =>
    match ρ.evalArgsOwn as with
    | some ws => J j ws σ
    | none => False
  | .cases x alts, σ =>
    ∃ tag, σ.casesTag ρ x tag ∧
      HWpCtorAlts Δ rt retTy J ρ Q X tag alts (HWpDfltAlts Δ rt retTy J ρ Q X alts) σ
  | .ret a, σ =>
    match ρ.evalArgAt a retTy with
    | some w => Q w σ
    | none => False
  | .unreach, σ => X (BitVec.ofNat 64 panicUnreachable) σ
  | .oset x i y k, σ =>
    match ρ.getBV64? x, (ρ.evalArgAt y .tobject).bind Word.toBV64? with
    | some addr, some yv =>
      ∃ (idx : Nat) (hidx : idx < σ.objs.length),
        let o := σ.objs[idx]'hidx
        o.addr = addr ∧ o.tag ≤ 244 ∧ i < o.fields.length ∧
        HWp Δ rt retTy J ρ Q X k
          { σ with objs := σ.objs.set idx { o with fields := o.fields.set i yv } }
    | _, _ => False
  | .uset x i y k, σ =>
    match ρ.getBV64? x, ρ.getBV64? y with
    | some addr, some yv =>
      ∃ (idx : Nat) (hidx : idx < σ.objs.length),
        let o := σ.objs[idx]'hidx
        o.addr = addr ∧ o.tag ≤ 244 ∧ o.fields.length ≤ i ∧
        let bOff := 8 * (i - o.fields.length)
        bOff + 8 ≤ o.scalarData.length ∧
        let scal' := writeBytesAt o.scalarData bOff (writeNatLE yv.toNat 8)
        HWp Δ rt retTy J ρ Q X k
          { σ with objs := σ.objs.set idx { o with scalarData := scal' } }
    | _, _ => False
  | .sset x n off y ty k, σ =>
    match ρ.getBV64? x, (ρ.evalArgAt (.var y) ty).bind Word.toNat? with
    | some addr, some yNat =>
      ∃ (idx : Nat) (hidx : idx < σ.objs.length),
        let o := σ.objs[idx]'hidx
        o.addr = addr ∧ o.tag ≤ 244 ∧ o.fields.length ≤ n ∧
        let bOff := 8 * (n - o.fields.length) + off
        let nbytes := ty.toTTy.bytes
        bOff + nbytes ≤ o.scalarData.length ∧
        let scal' := writeBytesAt o.scalarData bOff (writeNatLE yNat nbytes)
        HWp Δ rt retTy J ρ Q X k
          { σ with objs := σ.objs.set idx { o with scalarData := scal' } }
    | _, _ => False
  | .setTag x cidx k, σ =>
    match ρ.getBV64? x with
    | some addr =>
      ∃ (idx : Nat) (hidx : idx < σ.objs.length),
        let o := σ.objs[idx]'hidx
        o.addr = addr ∧ o.tag ≤ 244 ∧ cidx ≤ 244 ∧
        HWp Δ rt retTy J ρ Q X k { σ with objs := σ.objs.set idx { o with tag := cidx } }
    | none => False
  | .inc x n chk k, σ =>
    match ρ.getTypedBV64? x with
    | some (ty, addr) =>
      if !ty.needsRc || n == 0 then HWp Δ rt retTy J ρ Q X k σ
      else if (addr &&& 1#64) ≠ 0#64 then
        chk = true ∧ ty = .tobject ∧ HWp Δ rt retTy J ρ Q X k σ
      else
        ∃ (idx : Nat) (hidx : idx < σ.objs.length),
          let o := σ.objs[idx]'hidx
          o.addr = addr ∧ o.Wf ∧ (0 < o.rc.toInt → o.rc.toNat + n < 2 ^ 31 - 1) ∧
          let rc' := if 0 < o.rc.toInt then o.rc + BitVec.ofNat 32 n else o.rc
          HWp Δ rt retTy J ρ Q X k { σ with objs := σ.objs.set idx (o.withRc rc') }
    | none => False
  | .dec x n chk k, σ =>
    match ρ.getTypedBV64? x with
    | some (ty, addr) => HDecN addr ty chk n (HWp Δ rt retTy J ρ Q X k) σ
    | none => False
  | .del x k, σ =>
    match ρ.getBV64? x with
    | some addr =>
      if (addr &&& 1#64) ≠ 0#64 then HWp Δ rt retTy J ρ Q X k σ
      else
        ∃ (idx : Nat) (hidx : idx < σ.objs.length),
          σ.objs[idx].addr = addr ∧
          ∀ st', st'.PreservesMeta σ.st → st'.rem = σ.st.rem → st'.workBuf = σ.st.workBuf →
            HWp Δ rt retTy J ρ Q X k { σ with st := st', objs := σ.objs.eraseIdx idx }
    | none => False

/-- Pass 1 of `cases` dispatch: match the first `.ctor tag _` alternative, else invoke `kDflt`. -/
@[expose] def HWpCtorAlts (Δ : HEnv) (rt : BitVec 64) (retTy : LcTy)
    (J : HJEnv) (ρ : HValEnv) (Q : HPost) (X : HXPost) (tag : Nat) :
    List (LcPat × LcCode) → (HState → Prop) → HState → Prop
  | [], kDflt, σ => kDflt σ
  | (.ctor ci _, b) :: rest, kDflt, σ =>
    if ci = tag then HWp Δ rt retTy J ρ Q X b σ
    else HWpCtorAlts Δ rt retTy J ρ Q X tag rest kDflt σ
  | (.dflt, _) :: rest, kDflt, σ => HWpCtorAlts Δ rt retTy J ρ Q X tag rest kDflt σ

/-- Pass 2 of `cases` dispatch: enter the first `.dflt` alternative, or `False`. -/
@[expose] def HWpDfltAlts (Δ : HEnv) (rt : BitVec 64) (retTy : LcTy)
    (J : HJEnv) (ρ : HValEnv) (Q : HPost) (X : HXPost) : List (LcPat × LcCode) → HState → Prop
  | [], _ => False
  | (.dflt, b) :: _, σ => HWp Δ rt retTy J ρ Q X b σ
  | (.ctor _ _, _) :: rest, σ => HWpDfltAlts Δ rt retTy J ρ Q X rest σ
end

/-! ## 2. Lifting into `LeanQbe.T` and Module Correctness -/

/-- Lift a Tier-H contract `S : HSpec` into a `LeanQbe.T.Spec (i64 :: as) [retTy]` (register-only
arguments `as.length ≤ regArgs`), framing arbitrary memory `R` and routing panics to
`X "lcnf_panic" [i64, i64] (rt, code, ())`. -/
@[expose] def liftSpec (S : HSpec) (as : List Ty) (retTy : Ty) : Spec (i64 :: as) [retTy] :=
  fun (rt, xs) m Q X =>
    ∃ (σ : HState) (R : Mem 64 → Prop),
      HInv rt σ ∧ (σ.mem rt ⋆ R) m ∧
      S (wordsOfTup xs) σ
        (fun r σ' =>
          ∃ h : r.1 = retTy,
            ∀ m', HInv rt σ' → (σ'.mem rt ⋆ R) m' → Q (h ▸ r.2, ()) m')
        (fun c σ' =>
          ∀ m', (σ'.mem rt ⋆ R) m' → X "lcnf_panic" [i64, i64] (rt, c, ()) m')

/-- Decode spilled parameters (`params.drop regArgs`) from `rt->extra_args`. -/
@[expose] def spilledWords (extraArgs : List (BitVec 64)) : List Ty → List Word
  | [] => []
  | t :: ts =>
    match extraArgs with
    | [] => []
    | w :: ws =>
      let word : Word := match t with | .bits n => ⟨.bits n, w.setWidth n⟩ | _ => Word.i64 w
      word :: spilledWords ws ts

/-- Full declaration-signature lifting handling both register parameters (`0..4`) and spilled
parameters (`5..` in `st.extraArgs`). -/
@[expose] def liftDeclSpec (S : HSpec) (params : List LcParam) (retTy : LcTy) :
    Spec (i64 :: (params.map (·.ty.toTTy)).take regArgs) [retTy.toTTy] :=
  fun (rt, xs) m Q X =>
    let spilled := (params.map (·.ty.toTTy)).drop regArgs
    ∃ (σ : HState) (R : Mem 64 → Prop),
      spilled.length ≤ σ.st.extraArgs.length ∧
      HInv rt σ ∧ (σ.mem rt ⋆ R) m ∧
      S (wordsOfTup xs ++ spilledWords σ.st.extraArgs spilled) σ
        (fun r σ' =>
          ∃ h : r.1 = retTy.toTTy,
            ∀ m', HInv rt σ' → (σ'.mem rt ⋆ R) m' → Q (h ▸ r.2, ()) m')
        (fun c σ' =>
          ∀ m', (σ'.mem rt ⋆ R) m' → X "lcnf_panic" [i64, i64] (rt, c, ()) m')

/-- Lift a Tier-H environment `Δ` for module `m` into a `LeanQbe.T.Env`, mapping `mangleLc d.name`
to `liftDeclSpec (Δ d.name) d.params d.retTy`. -/
@[expose] def liftEnv (m : LcModule) (Δ : HEnv) : Env :=
  fun sym as rs xs mem Q X =>
    ∃ d ∈ m.decls,
      mangleLc d.name = sym ∧
      ∃ (ha : (i64 :: (d.params.map (·.ty.toTTy)).take regArgs) = as)
        (hr : [d.retTy.toTTy] = rs),
        liftDeclSpec (Δ d.name) d.params d.retTy (ha ▸ xs) mem (hr ▸ Q) X

/-- Closed / acyclic Tier-H module correctness: every declaration satisfies its contract in `Δ`. -/
@[expose] def HModuleOk (Δ : HEnv) (m : LcModule) : Prop :=
  ∀ d ∈ m.decls, ∀ rt as σ Q X,
    HInv rt σ → paramsMatch d.params as → Δ d.name as σ Q X →
    HWp Δ rt d.retTy HJEnv.empty (HValEnv.empty.bindAll d.params as) Q X d.body σ

/-- Measure-indexed Tier-H module correctness for recursive / self-tail modules (feeds
`BudgetEnv.semScc` and `LinkedCertScc`). -/
@[expose] def HModuleOkIdx (Δ : Nat → HEnv) (m : LcModule) : Prop :=
  (∀ k, HEnv.le (Δ k) (Δ (k + 1))) ∧
  ∀ k, ∀ d ∈ m.decls, ∀ rt as σ Q X,
    HInv rt σ → paramsMatch d.params as → Δ k d.name as σ Q X →
    HWp (match k with | 0 => HEnv.bot | k' + 1 => Δ k')
      rt d.retTy HJEnv.empty (HValEnv.empty.bindAll d.params as) Q X d.body σ

/-! ## 3. Core Monotonicity, Join, Frame, and Lifting Lemmas -/

theorem HVal.wp_conseq {Δ₁ Δ₂ : HEnv} {rt : BitVec 64} {ρ : HValEnv} {ty : LcTy}
    {v : LcVal} {K₁ K₂ : HPost} {X₁ X₂ : HXPost}
    (hΔ : HEnv.le Δ₁ Δ₂) (hK : ∀ r σ, K₁ r σ → K₂ r σ) (hX : ∀ c σ, X₁ c σ → X₂ c σ)
    {σ : HState} (h : HVal.wp Δ₁ rt ρ ty v K₁ X₁ σ) :
    HVal.wp Δ₂ rt ρ ty v K₂ X₂ σ := by
  cases v with
  | lit l =>
    cases l with
    | nat n =>
      dsimp only [HVal.wp] at h ⊢
      by_cases hlt : n < 2 ^ 63
      · rw [ite_eq_left hlt] at h ⊢; exact hK _ _ h
      · rw [ite_eq_right hlt] at h ⊢
        exact fun p st' objs' h1 h2 h3 h4 => hK _ _ (h p st' objs' h1 h2 h3 h4)
    | scalar _ => exact hK _ _ h
    | str _ => exact fun p st' objs' h1 h2 h3 h4 => hK _ _ (h p st' objs' h1 h2 h3 h4)
  | erased => exact hK _ _ h
  | ap f as =>
    dsimp only [HVal.wp] at h ⊢
    cases hf : ρ.evalArgOwn (.var f) with
    | none => simp [hf] at h
    | some _ => cases has : ρ.evalArgsOwn as with
      | none => simp [hf, has] at h
      | some _ =>
        simp only [hf, has] at h ⊢
        rcases h with ⟨P, E, hcall, hP, hE⟩
        exact ⟨P, E, hΔ _ _ _ _ _ hcall, fun r σ' hp => hK _ _ (hP r σ' hp),
          fun c σ' he => hX _ _ (hE c σ' he)⟩
  | ctor ci as =>
    dsimp only [HVal.wp] at h ⊢
    by_cases hsc : ci.isScalar = true
    · rw [ite_eq_left hsc] at h ⊢; exact hK _ _ h
    · rw [ite_eq_right hsc] at h ⊢
      cases has : ρ.evalObjArgs as with
      | none => simp [has] at h
      | some _ =>
        simp only [has] at h ⊢
        rcases h with ⟨h1, h2, h3, h4, h5, h6, hk⟩
        exact ⟨h1, h2, h3, h4, h5, h6, fun p st' scal a1 a2 a3 a4 a5 a6 a7 =>
          hK _ _ (hk p st' scal a1 a2 a3 a4 a5 a6 a7)⟩
  | oproj i x =>
    dsimp only [HVal.wp] at h ⊢
    cases hx : ρ.getBV64? x with
    | none => simp [hx] at h
    | some _ =>
      simp only [hx] at h ⊢
      rcases h with ⟨o, hm, ha, ht, hi, hk⟩; exact ⟨o, hm, ha, ht, hi, hK _ _ hk⟩
  | uproj i x =>
    dsimp only [HVal.wp] at h ⊢
    cases hx : ρ.getBV64? x with
    | none => simp [hx] at h
    | some _ =>
      simp only [hx] at h ⊢
      rcases h with ⟨o, hm, ha, hwf, ht, hle, hsz, hk⟩
      exact ⟨o, hm, ha, hwf, ht, hle, hsz, hK _ _ hk⟩
  | sproj n off x =>
    dsimp only [HVal.wp] at h ⊢
    cases hx : ρ.getBV64? x with
    | none => simp [hx] at h
    | some _ =>
      simp only [hx] at h ⊢
      rcases h with ⟨o, hm, ha, hwf, ht, hle, hsz, hk⟩
      exact ⟨o, hm, ha, hwf, ht, hle, hsz, hK _ _ hk⟩
  | fap f as =>
    dsimp only [HVal.wp] at h ⊢
    cases has : ρ.evalArgsOwn as with
    | none => simp [has] at h
    | some _ =>
      simp only [has] at h ⊢
      by_cases hp : isPrimName f = true
      · rw [ite_eq_left hp] at h ⊢; exact HPrim.wp_mono hK hX h
      · rw [ite_eq_right hp] at h ⊢
        rcases h with ⟨P, E, hcall, hP, hE⟩
        refine ⟨P, E, hΔ _ _ _ _ _ hcall, fun r σ' hp' => ?_,
          fun c σ' he => hX _ _ (hE c σ' he)⟩
        rcases hP r σ' hp' with ⟨r', hr', hk⟩
        exact ⟨r', hr', hK _ _ hk⟩
  | pap _ _ => exact False.elim h
  | reset n x =>
    dsimp only [HVal.wp] at h ⊢
    cases hx : ρ.getBV64? x with
    | none => simp [hx] at h
    | some _ =>
      simp only [hx] at h ⊢
      rcases h with ⟨idx, hidx, ha, ht, hle, hif⟩
      refine ⟨idx, hidx, ha, ht, hle, ?_⟩
      by_cases hrc : (σ.objs[idx]'hidx).rc = 1#32
      · rw [ite_eq_left hrc] at hif ⊢; exact HResetRelease_mono hK n σ hif
      · rw [ite_eq_right hrc] at hif ⊢; exact HDecN_mono (hK _) 1 σ hif
  | reuse x ci upd as =>
    dsimp only [HVal.wp] at h ⊢
    cases hx : ρ.getBV64? x with
    | none => simp [hx] at h
    | some addr => cases has : ρ.evalObjArgs as with
      | none => simp [hx, has] at h
      | some _ =>
        simp only [hx, has] at h ⊢
        by_cases hsc : (addr &&& 1#64) ≠ 0#64
        · rw [ite_eq_left hsc] at h ⊢
          rcases h with ⟨h1, h2, h3, h4, h5, h6, hk⟩
          exact ⟨h1, h2, h3, h4, h5, h6, fun p st' scal a1 a2 a3 a4 a5 a6 a7 =>
            hK _ _ (hk p st' scal a1 a2 a3 a4 a5 a6 a7)⟩
        · rw [ite_eq_right hsc] at h ⊢
          rcases h with ⟨idx, hidx, h1, h2, h3, h4, hk⟩
          exact ⟨idx, hidx, h1, h2, h3, h4, hK _ _ hk⟩
  | box t x =>
    dsimp only [HVal.wp] at h ⊢
    cases hx : ρ.evalArgAt (.var x) t with
    | none => simp [hx] at h
    | some w =>
      simp only [hx] at h ⊢
      cases t <;> simp only at h ⊢
      all_goals
        first
          | exact hK _ _ h
          | (cases hbv : w.toBV64? with
             | none => simp [hbv] at h
             | some _ =>
               simp only [hbv] at h ⊢
               exact ⟨h.1, fun p st' a1 a2 a3 a4 a5 a6 => hK _ _ (h.2 p st' a1 a2 a3 a4 a5 a6)⟩)
          | (cases hw : (w.toWidth 64).bind Word.toBV64? with
             | none => simp [hw] at h
             | some _ => simp only [hw] at h ⊢; exact hK _ _ h)
  | unbox x =>
    dsimp only [HVal.wp] at h ⊢
    cases hx : ρ.getBV64? x with
    | none => simp [hx] at h
    | some _ =>
      simp only [hx] at h ⊢
      cases ty <;> simp only at h ⊢
      all_goals
        first
          | exact hK _ _ h
          | (rcases h with ⟨o, hm, h1, hwf, h2, h3, h4, hk⟩;
             exact ⟨o, hm, h1, hwf, h2, h3, h4, hK _ _ hk⟩)
  | isShared x =>
    dsimp only [HVal.wp] at h ⊢
    cases hx : ρ.getBV64? x with
    | none => simp [hx] at h
    | some _ =>
      simp only [hx] at h ⊢
      rcases h with ⟨o, hm, ha, hk⟩; exact ⟨o, hm, ha, hK _ _ hk⟩

mutual
/-- Unified consequence / monotonicity theorem for `HWp` in `Δ`, `J`, `Q`, and `X`. -/
theorem HWp_conseq {Δ₁ Δ₂ : HEnv} {rt : BitVec 64} {retTy : LcTy}
    {Q₁ Q₂ : HPost} {X₁ X₂ : HXPost}
    (hΔ : HEnv.le Δ₁ Δ₂) (hQ : ∀ r σ, Q₁ r σ → Q₂ r σ) (hX : ∀ c σ, X₁ c σ → X₂ c σ) :
    ∀ (c : LcCode) {J₁ J₂ : HJEnv}, HJEnv.le J₁ J₂ → ∀ (ρ : HValEnv) (σ : HState),
      HWp Δ₁ rt retTy J₁ ρ Q₁ X₁ c σ → HWp Δ₂ rt retTy J₂ ρ Q₂ X₂ c σ
  | .let_ x ty v k, _, _, hJ, ρ, σ, h =>
    HVal.wp_conseq hΔ (fun r σ' hk => HWp_conseq hΔ hQ hX k hJ (ρ.set x ty r) σ' hk) hX h
  | .jp j ps body k, _, _, hJ, ρ, σ, h => by
    dsimp only [HWp] at h ⊢
    intro Jj hcl
    refine HWp_conseq hΔ hQ hX k (HJEnv.le_set hJ j Jj) ρ σ (h Jj fun as σ' hpm hb => ?_)
    exact hcl as σ' hpm
      (HWp_conseq hΔ hQ hX body (HJEnv.le_set hJ j Jj) (ρ.bindAll ps as) σ' hb)
  | .jmp j as, _, _, hJ, ρ, σ, h => by
    dsimp only [HWp] at h ⊢
    cases has : ρ.evalArgsOwn as with
    | none => simp [has] at h
    | some ws => simp only [has] at h ⊢; exact hJ j ws σ h
  | .cases x alts, _, _, hJ, ρ, σ, ⟨tag, htag, halts⟩ =>
    ⟨tag, htag, HWpCtorAlts_conseq hΔ hQ hX tag alts
      (fun σ' hd => HWpDfltAlts_conseq hΔ hQ hX alts hJ ρ σ' hd) hJ ρ σ halts⟩
  | .ret a, _, _, _, ρ, σ, h => by
    dsimp only [HWp] at h ⊢
    cases ha : ρ.evalArgAt a retTy with
    | none => simp [ha] at h
    | some w => simp only [ha] at h ⊢; exact hQ w σ h
  | .unreach, _, _, _, _, σ, h => hX _ σ h
  | .oset x i y k, _, _, hJ, ρ, σ, h => by
    dsimp only [HWp] at h ⊢
    cases hx : ρ.getBV64? x with
    | none => simp [hx] at h
    | some _ => cases hy : (ρ.evalArgAt y .tobject).bind Word.toBV64? with
      | none => simp [hx, hy] at h
      | some _ =>
        simp only [hx, hy] at h ⊢
        rcases h with ⟨idx, hidx, h1, h2, h3, hk⟩
        exact ⟨idx, hidx, h1, h2, h3, HWp_conseq hΔ hQ hX k hJ ρ _ hk⟩
  | .uset x i y k, _, _, hJ, ρ, σ, h => by
    dsimp only [HWp] at h ⊢
    cases hx : ρ.getBV64? x with
    | none => simp [hx] at h
    | some _ => cases hy : ρ.getBV64? y with
      | none => simp [hx, hy] at h
      | some _ =>
        simp only [hx, hy] at h ⊢
        rcases h with ⟨idx, hidx, h1, h2, h3, h4, hk⟩
        exact ⟨idx, hidx, h1, h2, h3, h4, HWp_conseq hΔ hQ hX k hJ ρ _ hk⟩
  | .sset x n off y ty k, _, _, hJ, ρ, σ, h => by
    dsimp only [HWp] at h ⊢
    cases hx : ρ.getBV64? x with
    | none => simp [hx] at h
    | some _ => cases hy : (ρ.evalArgAt (.var y) ty).bind Word.toNat? with
      | none => simp [hx, hy] at h
      | some _ =>
        simp only [hx, hy] at h ⊢
        rcases h with ⟨idx, hidx, h1, h2, h3, h4, hk⟩
        exact ⟨idx, hidx, h1, h2, h3, h4, HWp_conseq hΔ hQ hX k hJ ρ _ hk⟩
  | .setTag x cidx k, _, _, hJ, ρ, σ, h => by
    dsimp only [HWp] at h ⊢
    cases hx : ρ.getBV64? x with
    | none => simp [hx] at h
    | some _ =>
      simp only [hx] at h ⊢
      rcases h with ⟨idx, hidx, h1, h2, h3, hk⟩
      exact ⟨idx, hidx, h1, h2, h3, HWp_conseq hΔ hQ hX k hJ ρ _ hk⟩
  | .inc x n chk k, _, _, hJ, ρ, σ, h => by
    dsimp only [HWp] at h ⊢
    cases hx : ρ.getTypedBV64? x with
    | none => simp [hx] at h
    | some p =>
      rcases p with ⟨ty, addr⟩
      simp only [hx] at h ⊢
      by_cases hskip : (!ty.needsRc || n == 0) = true
      · rw [ite_eq_left hskip] at h ⊢; exact HWp_conseq hΔ hQ hX k hJ ρ σ h
      · rw [ite_eq_right hskip] at h ⊢
        by_cases hsc : (addr &&& 1#64) ≠ 0#64
        · rw [ite_eq_left hsc] at h ⊢; exact ⟨h.1, h.2.1, HWp_conseq hΔ hQ hX k hJ ρ σ h.2.2⟩
        · rw [ite_eq_right hsc] at h ⊢
          rcases h with ⟨idx, hidx, h1, hwf, h2, hk⟩
          exact ⟨idx, hidx, h1, hwf, h2, HWp_conseq hΔ hQ hX k hJ ρ _ hk⟩
  | .dec x n chk k, _, _, hJ, ρ, σ, h => by
    dsimp only [HWp] at h ⊢
    cases hx : ρ.getTypedBV64? x with
    | none => simp [hx] at h
    | some p =>
      rcases p with ⟨ty, addr⟩
      simp only [hx] at h ⊢
      exact HDecN_mono (fun σ' hk => HWp_conseq hΔ hQ hX k hJ ρ σ' hk) n σ h
  | .del x k, _, _, hJ, ρ, σ, h => by
    dsimp only [HWp] at h ⊢
    cases hx : ρ.getBV64? x with
    | none => simp [hx] at h
    | some addr =>
      simp only [hx] at h ⊢
      by_cases hsc : (addr &&& 1#64) ≠ 0#64
      · rw [ite_eq_left hsc] at h ⊢; exact HWp_conseq hΔ hQ hX k hJ ρ σ h
      · rw [ite_eq_right hsc] at h ⊢
        rcases h with ⟨idx, hidx, ha, hk⟩
        exact ⟨idx, hidx, ha, fun st' h1 h2 h3 =>
          HWp_conseq hΔ hQ hX k hJ ρ _ (hk st' h1 h2 h3)⟩

theorem HWpCtorAlts_conseq {Δ₁ Δ₂ : HEnv} {rt : BitVec 64} {retTy : LcTy}
    {Q₁ Q₂ : HPost} {X₁ X₂ : HXPost}
    (hΔ : HEnv.le Δ₁ Δ₂) (hQ : ∀ r σ, Q₁ r σ → Q₂ r σ) (hX : ∀ c σ, X₁ c σ → X₂ c σ)
    (tag : Nat) :
    ∀ (alts : List (LcPat × LcCode)) {kD₁ kD₂ : HState → Prop},
      (∀ σ, kD₁ σ → kD₂ σ) → ∀ {J₁ J₂ : HJEnv}, HJEnv.le J₁ J₂ →
      ∀ (ρ : HValEnv) (σ : HState),
      HWpCtorAlts Δ₁ rt retTy J₁ ρ Q₁ X₁ tag alts kD₁ σ →
      HWpCtorAlts Δ₂ rt retTy J₂ ρ Q₂ X₂ tag alts kD₂ σ
  | [], _, _, hkD, _, _, _, _, σ, h => hkD σ h
  | (.ctor ci _, b) :: rest, _, _, hkD, _, _, hJ, ρ, σ, h => by
    dsimp only [HWpCtorAlts] at h ⊢
    by_cases hci : ci = tag
    · rw [ite_eq_left hci] at h ⊢; exact HWp_conseq hΔ hQ hX b hJ ρ σ h
    · rw [ite_eq_right hci] at h ⊢; exact HWpCtorAlts_conseq hΔ hQ hX tag rest hkD hJ ρ σ h
  | (.dflt, _) :: rest, _, _, hkD, _, _, hJ, ρ, σ, h =>
    HWpCtorAlts_conseq hΔ hQ hX tag rest hkD hJ ρ σ h

theorem HWpDfltAlts_conseq {Δ₁ Δ₂ : HEnv} {rt : BitVec 64} {retTy : LcTy}
    {Q₁ Q₂ : HPost} {X₁ X₂ : HXPost}
    (hΔ : HEnv.le Δ₁ Δ₂) (hQ : ∀ r σ, Q₁ r σ → Q₂ r σ) (hX : ∀ c σ, X₁ c σ → X₂ c σ) :
    ∀ (alts : List (LcPat × LcCode)) {J₁ J₂ : HJEnv}, HJEnv.le J₁ J₂ →
      ∀ (ρ : HValEnv) (σ : HState),
      HWpDfltAlts Δ₁ rt retTy J₁ ρ Q₁ X₁ alts σ →
      HWpDfltAlts Δ₂ rt retTy J₂ ρ Q₂ X₂ alts σ
  | [], _, _, _, _, _, h => False.elim h
  | (.dflt, b) :: _, _, _, hJ, ρ, σ, h => HWp_conseq hΔ hQ hX b hJ ρ σ h
  | (.ctor _ _, _) :: rest, _, _, hJ, ρ, σ, h =>
    HWpDfltAlts_conseq hΔ hQ hX rest hJ ρ σ h
end

/-- Postcondition / exit-postcondition monotonicity of `HWp`. -/
theorem HWp_mono {Δ : HEnv} {rt : BitVec 64} {retTy : LcTy} {J : HJEnv} {ρ : HValEnv}
    {Q₁ Q₂ : HPost} {X₁ X₂ : HXPost} {c : LcCode} {σ : HState}
    (hQ : ∀ r σ', Q₁ r σ' → Q₂ r σ') (hX : ∀ e σ', X₁ e σ' → X₂ e σ')
    (h : HWp Δ rt retTy J ρ Q₁ X₁ c σ) : HWp Δ rt retTy J ρ Q₂ X₂ c σ :=
  HWp_conseq (HEnv.le_refl Δ) hQ hX c (HJEnv.le_refl J) ρ σ h

/-- Environment monotonicity of `HWp`. -/
theorem HWp_env_mono {Δ₁ Δ₂ : HEnv} {rt : BitVec 64} {retTy : LcTy} {J : HJEnv} {ρ : HValEnv}
    {Q : HPost} {X : HXPost} {c : LcCode} {σ : HState}
    (hΔ : HEnv.le Δ₁ Δ₂) (h : HWp Δ₁ rt retTy J ρ Q X c σ) :
    HWp Δ₂ rt retTy J ρ Q X c σ :=
  HWp_conseq hΔ (fun _ _ h => h) (fun _ _ h => h) c (HJEnv.le_refl J) ρ σ h

/-- Join-environment monotonicity of `HWp`. -/
theorem HWp_jp_mono {Δ : HEnv} {rt : BitVec 64} {retTy : LcTy} {J₁ J₂ : HJEnv} {ρ : HValEnv}
    {Q : HPost} {X : HXPost} {c : LcCode} {σ : HState}
    (hJ : HJEnv.le J₁ J₂) (h : HWp Δ rt retTy J₁ ρ Q X c σ) :
    HWp Δ rt retTy J₂ ρ Q X c σ :=
  HWp_conseq (HEnv.le_refl Δ) (fun _ _ h => h) (fun _ _ h => h) c hJ ρ σ h

/-- Pure-proposition frame rule for `HWp`. -/
theorem HWp_frame_pure {Δ : HEnv} {rt : BitVec 64} {retTy : LcTy} {J : HJEnv} {ρ : HValEnv}
    {Q : HPost} {X : HXPost} {c : LcCode} {σ : HState} {φ : Prop}
    (hφ : φ) (h : HWp Δ rt retTy J ρ Q X c σ) :
    HWp Δ rt retTy J ρ (fun r σ' => φ ∧ Q r σ') (fun e σ' => φ ∧ X e σ') c σ :=
  HWp_mono (fun _ _ hq => ⟨hφ, hq⟩) (fun _ _ hx => ⟨hφ, hx⟩) h

/-- Measure-indexed join-point induction rule (mirrors `T.wp_loop_group`). -/
theorem HWp_jp_loop {Δ : HEnv} {rt : BitVec 64} {retTy : LcTy} {J : HJEnv} {ρ : HValEnv}
    {Q : HPost} {X : HXPost} {j : Nat} {ps : List LcParam} {body k : LcCode} {σ : HState}
    (Inv : Nat → List Word → HState → Prop)
    (hpm : ∀ n as σ', Inv n as σ' → paramsMatch ps as)
    (hbody : ∀ (Jj : List Word → HState → Prop) n as σ',
      (∀ n' ys σ'', n' < n → Inv n' ys σ'' → Jj ys σ'') →
      Inv n as σ' →
      HWp Δ rt retTy (J.set j Jj) (ρ.bindAll ps as) Q X body σ')
    (hk : ∀ (Jj : List Word → HState → Prop),
      (∀ n as σ', Inv n as σ' → Jj as σ') →
      HWp Δ rt retTy (J.set j Jj) ρ Q X k σ) :
    HWp Δ rt retTy J ρ Q X (.jp j ps body k) σ := by
  dsimp only [HWp]
  intro Jj hcl
  refine hk Jj fun n => ?_
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro as σ' hinv
    exact hcl as σ' (hpm n as σ' hinv)
      (hbody Jj n as σ' (fun n' ys σ'' hlt hi => ih n' hlt ys σ'' hi) hinv)

/-- Non-recursive join-point introduction rule (mirrors `T.wp_join_group`). -/
theorem HWp_jp_rule {Δ : HEnv} {rt : BitVec 64} {retTy : LcTy} {J : HJEnv} {ρ : HValEnv}
    {Q : HPost} {X : HXPost} {j : Nat} {ps : List LcParam} {body k : LcCode} {σ : HState}
    (P : List Word → HState → Prop)
    (hpm : ∀ as σ', P as σ' → paramsMatch ps as)
    (hbody : ∀ (Jj : List Word → HState → Prop) as σ', P as σ' →
      HWp Δ rt retTy (J.set j Jj) (ρ.bindAll ps as) Q X body σ')
    (hk : ∀ (Jj : List Word → HState → Prop),
      (∀ as σ', P as σ' → Jj as σ') →
      HWp Δ rt retTy (J.set j Jj) ρ Q X k σ) :
    HWp Δ rt retTy J ρ Q X (.jp j ps body k) σ :=
  HWp_jp_loop (fun _ => P) (fun _ => hpm) (fun Jj _ as σ' _ h => hbody Jj as σ' h)
    (fun Jj hJ => hk Jj (hJ 0))

/-- `Spec.Mono` for `liftSpec`. -/
theorem liftSpec_mono (S : HSpec) (hS : S.Mono) (as : List Ty) (retTy : Ty) :
    (liftSpec S as retTy).Mono := by
  rintro ⟨rt, xs⟩ m Q₁ Q₂ X₁ X₂ hQ hX ⟨σ, R, hinv, hm, hs⟩
  refine ⟨σ, R, hinv, hm, hS _ σ _ _ _ _ ?_ ?_ hs⟩
  · rintro r σ' ⟨heq, hk⟩; exact ⟨heq, fun m' hinv' hm' => hQ _ m' (hk m' hinv' hm')⟩
  · intro c σ' hk m' hm'; exact hX _ _ _ m' (hk m' hm')

/-- `Spec.Mono` for `liftDeclSpec`. -/
theorem liftDeclSpec_mono (S : HSpec) (hS : S.Mono) (params : List LcParam) (retTy : LcTy) :
    (liftDeclSpec S params retTy).Mono := by
  rintro ⟨rt, xs⟩ m Q₁ Q₂ X₁ X₂ hQ hX ⟨σ, R, hsp, hinv, hm, hs⟩
  refine ⟨σ, R, hsp, hinv, hm, hS _ σ _ _ _ _ ?_ ?_ hs⟩
  · rintro r σ' ⟨heq, hk⟩; exact ⟨heq, fun m' hinv' hm' => hQ _ m' (hk m' hinv' hm')⟩
  · intro c σ' hk m' hm'; exact hX _ _ _ m' (hk m' hm')

/-- Refinement monotonicity of `liftSpec` in `S`. -/
theorem liftSpec_of_le {S₁ S₂ : HSpec} (hle : HSpec.le S₁ S₂) (as : List Ty) (retTy : Ty)
    {xs : Tup Val (i64 :: as)} {m : Mem 64} {Q : Post [retTy]} {X : XPost}
    (h : liftSpec S₁ as retTy xs m Q X) : liftSpec S₂ as retTy xs m Q X := by
  rcases xs with ⟨rt, args⟩; rcases h with ⟨σ, R, hinv, hm, hs⟩
  exact ⟨σ, R, hinv, hm, hle _ σ _ _ hs⟩

/-- Refinement monotonicity of `liftDeclSpec` in `S`. -/
theorem liftDeclSpec_of_le {S₁ S₂ : HSpec} (hle : HSpec.le S₁ S₂)
    (params : List LcParam) (retTy : LcTy)
    {xs : Tup Val (i64 :: (params.map (·.ty.toTTy)).take regArgs)}
    {m : Mem 64} {Q : Post [retTy.toTTy]} {X : XPost}
    (h : liftDeclSpec S₁ params retTy xs m Q X) : liftDeclSpec S₂ params retTy xs m Q X := by
  rcases xs with ⟨rt, args⟩; rcases h with ⟨σ, R, hsp, hinv, hm, hs⟩
  exact ⟨σ, R, hsp, hinv, hm, hle _ σ _ _ hs⟩

private theorem sep_elim_l {P F : Mem 64 → Prop} {m : Mem 64} (h : (P ⋆ F) m) :
    ∃ m₁, P m₁ ∧ (Eq m₁ ⋆ F) m := by
  have h1 : ((fun ma => ∃ m₁, P m₁ ∧ Eq m₁ ma) ⋆ F) m :=
    sep_mono (fun ma hma => ⟨ma, hma, rfl⟩) h
  obtain ⟨m₁, hm₁⟩ := sep_ex_l.mp h1
  exact ⟨m₁, sep_pure_l.mp hm₁⟩

/-- Separation-logic frame rule for `liftSpec`: an arbitrary disjoint frame `F` can be added
to the memory footprint without modifying the Tier-H proof. -/
theorem liftSpec_frame (S : HSpec) (hS : S.Mono) (as : List Ty) (retTy : Ty)
    {xs : Tup Val (i64 :: as)} {m : Mem 64} {F : Mem 64 → Prop}
    {Q : Post [retTy]} {X : XPost}
    (h : ((fun m₀ => liftSpec S as retTy xs m₀
      (fun r m₁ => ∀ m', (Eq m₁ ⋆ F) m' → Q r m')
      (fun f cs ys m₁ => ∀ m', (Eq m₁ ⋆ F) m' → X f cs ys m')) ⋆ F) m) :
    liftSpec S as retTy xs m Q X := by
  rcases xs with ⟨rt, args⟩
  have h1 : ((fun m₀ => ∃ (σ : HState) (R : Mem 64 → Prop),
      (HInv rt σ ∧ S (wordsOfTup args) σ
        (fun r σ' => ∃ h : r.1 = retTy,
          ∀ m₁, HInv rt σ' → (σ'.mem rt ⋆ R) m₁ →
            ∀ m', (Eq m₁ ⋆ F) m' → Q (h ▸ r.2, ()) m')
        (fun c σ' =>
          ∀ m₁, (σ'.mem rt ⋆ R) m₁ →
            ∀ m', (Eq m₁ ⋆ F) m' → X "lcnf_panic" [i64, i64] (rt, c, ()) m')) ∧
      (σ.mem rt ⋆ R) m₀) ⋆ F) m :=
    sep_mono (fun _ ⟨σ, R, hinv, hm0, hs⟩ => ⟨σ, R, ⟨hinv, hs⟩, hm0⟩) h
  obtain ⟨σ, h2⟩ := sep_ex_l.mp h1
  obtain ⟨R, h3⟩ := sep_ex_l.mp h2
  obtain ⟨⟨hinv, hs⟩, hm⟩ := sep_pure_l.mp h3
  refine ⟨σ, R ⋆ F, hinv, sep_cast hm (by ac_rfl), hS _ σ _ _ _ _ ?_ ?_ hs⟩
  · rintro r σ' ⟨heq, hk⟩
    refine ⟨heq, fun m' hinv' hm' => ?_⟩
    obtain ⟨m₁, hm₁, heqF⟩ := sep_elim_l (sep_cast hm' (by ac_rfl) : ((σ'.mem rt ⋆ R) ⋆ F) m')
    exact hk m₁ hinv' hm₁ m' heqF
  · intro c σ' hk m' hm'
    obtain ⟨m₁, hm₁, heqF⟩ := sep_elim_l (sep_cast hm' (by ac_rfl) : ((σ'.mem rt ⋆ R) ⋆ F) m')
    exact hk m₁ hm₁ m' heqF

/-- Environment monotonicity of `liftEnv`. -/
theorem liftEnv_mono (m : LcModule) {Δ₁ Δ₂ : HEnv} (hΔ : HEnv.le Δ₁ Δ₂) :
    Env.le (liftEnv m Δ₁) (liftEnv m Δ₂) := by
  rintro sym as rs xs mem Q X ⟨d, hd, hsym, ha, hr, hspec⟩
  exact ⟨d, hd, hsym, ha, hr, liftDeclSpec_of_le (hΔ d.name) d.params d.retTy hspec⟩

/-- Lookup introduction rule for `liftEnv`. -/
theorem liftEnv_of_mem {m : LcModule} {Δ : HEnv} {d : LcDecl} (hd : d ∈ m.decls)
    {xs : Tup Val (i64 :: (d.params.map (·.ty.toTTy)).take regArgs)}
    {mem : Mem 64} {Q : Post [d.retTy.toTTy]} {X : XPost}
    (h : liftDeclSpec (Δ d.name) d.params d.retTy xs mem Q X) :
    liftEnv m Δ (mangleLc d.name)
      (i64 :: (d.params.map (·.ty.toTTy)).take regArgs) [d.retTy.toTTy] xs mem Q X :=
  ⟨d, hd, rfl, rfl, rfl, h⟩

/-- When a declaration has `≤ regArgs` (`5`) parameters, `liftDeclSpec` reduces to `liftSpec`. -/
theorem liftDeclSpec_iff_liftSpec_of_le (S : HSpec) (params : List LcParam) (retTy : LcTy)
    (hlen : params.length ≤ regArgs)
    (xs : Tup Val (i64 :: (params.map (·.ty.toTTy)).take regArgs))
    (m : Mem 64) (Q : Post [retTy.toTTy]) (X : XPost) :
    liftDeclSpec S params retTy xs m Q X ↔
      liftSpec S ((params.map (·.ty.toTTy)).take regArgs) retTy.toTTy xs m Q X := by
  have hdrop : (params.map (·.ty.toTTy)).drop regArgs = [] := by
    apply List.drop_eq_nil_of_le
    simpa [List.length_map] using hlen
  rcases xs with ⟨rt, args⟩
  simp only [liftDeclSpec, liftSpec, hdrop, spilledWords, List.append_nil, List.length_nil,
    Nat.zero_le, true_and]

end LeanQbe.T.LeanLCNF.Sem
