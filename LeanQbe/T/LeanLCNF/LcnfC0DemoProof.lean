module

public import LeanQbe.T.LeanLCNF.LcnfC0Demo
public import LeanQbe.T.LeanLCNF.LcnfC0LinkKit
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof1
public import LeanQbe.T.LeanLCNF.LcnfC0RtProofNv
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.Cells
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# Soundness Proofs & `ModuleOk` for `LcnfC0Demo` (`addNat`, `addToStr`, `fmtSumTagged`)

Proves end-to-end typed-IR (`Func.wp`) correctness for all three Lean `LCNF` functions
extracted in `LeanQbe.T.LeanLCNF.LcnfC0Demo` against the linked `rtC0CoreEnv` + `demoNatStrEnv`
environment (`demoNatStrLinkedEnv := linkRtC0Env demoNatStrEnv`), and composes whole-module
`ModuleOk` via `LcnfC0LinkKit.linkLcnfWithRtC0_moduleOk`:

1. `addNatSpec`: tagged scalar fast path (`(a &&& b &&& 1#64) ≠ 0#64` and non-overflowing
   `(a - 1#64) + b`) returning in-place with `0` memory side effects; slow path delegating to
   R1 `lcnfNatSlowSpec`.
2. `addToStrSpec`: calls `addNat` on scalar `boxNat aVal`, `boxNat bVal` (`aVal + bVal < 2 ^ 63`)
   and R2b `lcnf_nat_to_str` (`lcnfNatToStrSpec` → R0 `lcnf_alloc`) allocating a fresh heap
   `String` object (`natToDecimalBytes (aVal + bVal)`).
3. `fmtSumTaggedSpec`: calls `addToStr`, appends onto an exclusive heap `String` buffer
   in-place via R2b `lcnf_string_append`, reads the temporary string header's 32-bit RC via
   `load i32`, and frees it via R0 `lcnf_dec_ref_cold` (`lcnf_free_obj`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open Kraken.Bedrock2.Test

/-! ## 1. Arithmetic, Header, and `DecColdRel` Helpers -/

/-- Guard for `DemoNatStr.addNat`'s fast tagged scalar path. -/
@[expose] def addNatFastOk (a b : BitVec 64) : Bool :=
  ((a &&& b &&& 1#64) != 0#64) && !((a - 1#64 + b).ult b)

theorem addNatFastOk_boxNat {aVal bVal : Nat} (hlt : aVal + bVal < 2 ^ 63) :
    addNatFastOk (boxNat aVal) (boxNat bVal) = true ∧
      (boxNat aVal - 1#64) + boxNat bVal = boxNat (aVal + bVal) := by
  have ha : (boxNat aVal).toNat = 2 * aVal + 1 := by
    unfold boxNat; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hb : (boxNat bVal).toNat = 2 * bVal + 1 := by
    unfold boxNat; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : (boxNat aVal - 1#64).toNat = 2 * aVal := by
    rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def, ha])]
    simp [ha]
  have hadd : ((boxNat aVal - 1#64) + boxNat bVal).toNat = 2 * (aVal + bVal) + 1 := by
    rw [BitVec.toNat_add, hsub, hb, Nat.mod_eq_of_lt (by omega)]
    omega
  have hsumEq : (boxNat aVal - 1#64) + boxNat bVal = boxNat (aVal + bVal) := by
    apply BitVec.eq_of_toNat_eq
    rw [hadd, boxNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, hsumEq⟩
  have ha1 : (boxNat aVal &&& 1#64) = 1#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide),
      Nat.and_one_is_mod, ha]
    omega
  have hb1 : (boxNat bVal &&& 1#64) = 1#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide),
      Nat.and_one_is_mod, hb]
    omega
  have hlsb : (boxNat aVal &&& boxNat bVal &&& 1#64) = 1#64 := by
    rw [BitVec.and_assoc, hb1, ha1]
  have hbit : ((boxNat aVal &&& boxNat bVal &&& 1#64) != 0#64) = true := by
    rw [hlsb]; decide
  have hult : ((boxNat aVal - 1#64 + boxNat bVal).ult (boxNat bVal)) = false := by
    rw [BitVec.ult, decide_eq_false_iff_not, hadd, hb]
    omega
  unfold addNatFastOk
  simp [hbit, hult]

private theorem rt_boxNat_and_one (n : Nat) (hn : n < 2 ^ 63) :
    (boxNat n &&& 1#64) = 1#64 := by
  have h1 : (1#64).toNat = 1 := by decide
  have hmod : (2 * n + 1) % 2 ^ 64 = 2 * n + 1 := Nat.mod_eq_of_lt (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, h1, Nat.and_one_is_mod, boxNat, BitVec.toNat_ofNat, hmod]
  omega

private theorem wp_call_pred {Γ : Env} {rs as bs : List Ty} {f : Sym}
    {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont rs}
    {m : Mem 64} {Q : Post rs} {X : XPost} (P : Post bs)
    (hcall : Γ f as bs (vals args) m P X)
    (hk : ∀ r m', P r m' → wp Γ Q X (k r) m') :
    wp Γ Q X (.call f args k) m :=
  ⟨P, X, hcall, hk, fun _ _ _ _ hx => hx⟩

private theorem rt_lcnfObj_header_setWidth32 (o : LcnfObj) (_hwf : o.Wf) :
    o.header.setWidth 32 = o.rc := by
  have hsh : ∀ (k : Nat) (hk : 32 ≤ k) (v : BitVec 64), (v <<< k).setWidth 32 = 0#32 := by
    intro k hk v
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hge : ¬ (k ≤ i) := by omega
    simp [hi, hge]
  unfold LcnfObj.header
  simp only [BitVec.setWidth_or, hsh 32 (by omega), hsh 48 (by omega), hsh 56 (by omega),
    BitVec.or_zero]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans o.rc.isLt
    (by decide))]
  rw [Nat.mod_eq_of_lt o.rc.isLt]

private theorem rt_str_load_rc {o : LcnfObj} {objs : List LcnfObj} {R : Mem 64 → Prop}
    {m : Mem 64} (hwf : o.Wf) (hmem : o ∈ objs)
    (hm : (lcnfHeap objs ⋆ R) m) :
    loadVal m i32 o.addr = some o.rc := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
  have hf := lcnfHeap_focus objs hi
  rw [heq] at hf
  obtain ⟨body, hbd, _⟩ := lcnfObjMem_header_body o
  rw [hf, hbd] at hm
  have hm' : (word8 o.addr o.header ⋆ (body ⋆ lcnfHeap (objs.take i) ⋆
      lcnfHeap (objs.drop (i + 1)) ⋆ R)) m := by
    rw [← cell64_eq_word8]
    exact sep_cast hm (by ac_rfl)
  have hld := load_int4_of_word8 hm'
  rwa [rt_lcnfObj_header_setWidth32 o hwf] at hld

private theorem rt_string_childFields_nil {o : LcnfObj} (htag : o.tag = stringTag) :
    o.childFields = [] := by
  unfold LcnfObj.childFields
  rw [htag]
  have h1 : ¬ (stringTag ≤ 244 ∨ stringTag = closureTag ∨ stringTag = arrayTag) := by
    unfold stringTag closureTag arrayTag; decide
  simp [h1]

private theorem rt_strPayload_mkStrObj {p : BitVec 64} {rc : BitVec 32} {cap strLen : Nat}
    {pay : List UInt8} :
    strPayload (mkStrObj p rc cap pay strLen) = pay := by
  unfold strPayload mkStrObj
  simp

private theorem nonPersistRefs_zero_of_not_mem {objs : List LcnfObj} {addr : BitVec 64}
    (hclosed : lcnfHeapClosed objs) (hptr : (addr &&& 1#64) = 0#64)
    (hnot : addr ∉ objs.map LcnfObj.addr) :
    nonPersistRefs objs addr = 0 := by
  have hfold : ∀ (xs : List LcnfObj) (acc : Nat),
      (∀ x ∈ xs, x ∈ objs) →
      xs.foldl (fun a p => if p.rc = 0#32 then a else a + p.childFields.count addr) acc =
        acc := by
    intro xs acc hsub
    induction xs generalizing acc with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.foldl_cons]
      have hcnt : x.childFields.count addr = 0 := by
        rw [List.count_eq_zero]
        intro hmem
        obtain ⟨q, hqMem, hqAddr⟩ :=
          hclosed x (hsub x List.mem_cons_self) addr hmem hptr
        exact hnot (hqAddr ▸ List.mem_map_of_mem hqMem)
      split <;> simp [hcnt, ih acc (fun z hz => hsub z (List.mem_cons_of_mem _ hz))]
  exact hfold objs 0 (fun _ h => h)

private theorem rt_mkStrObj_rc_eq {rObj : LcnfObj} {objs' : List LcnfObj}
    {s2 : BitVec 64} {objs2 : List LcnfObj}
    (hnd2 : (objs2.map LcnfObj.addr).Nodup)
    (hrMem : rObj ∈ objs2) (hrAddr : rObj.addr ≠ s2) (hrRc1 : rObj.rc = 1#32)
    (hs2Nil : ∀ o ∈ objs2, o.addr = s2 → o.childFields = [])
    (hDec : DecColdRel s2 objs2 objs') :
    rObj ∈ objs' := by
  have hrPos : 0 < rObj.rc.toInt := by rw [hrRc1]; decide
  have hnotReach : ¬ NonPersistReach objs2 s2 rObj.addr := by
    intro hreach
    have hEqS2 : ∀ {u}, NonPersistReach objs2 s2 u → u = s2 := by
      intro u hu
      induction hu with
      | refl _ => rfl
      | @step u v _ hchild _ _ ih =>
        subst ih
        obtain ⟨o, hoMem, hoAddr, hvMem⟩ := hchild
        rw [hs2Nil o hoMem hoAddr] at hvMem
        nomatch hvMem
    exact hrAddr (hEqS2 hreach)
  have hnotFreed : rObj ∉ freedObjs objs2 objs' := fun hf =>
    hnotReach (((hDec.2.2.2.2.2.2.2.2 rObj hrMem hrPos).2 hf).2)
  have haddrIn : rObj.addr ∈ objs'.map LcnfObj.addr := by
    by_cases hmem : rObj.addr ∈ objs'.map LcnfObj.addr
    · exact hmem
    · exfalso
      have hc : (objs'.map LcnfObj.addr).contains rObj.addr = false :=
        Bool.eq_false_iff.mpr fun ht => hmem (List.contains_iff_mem.mp ht)
      exact hnotFreed (List.mem_filter.mpr ⟨hrMem, by rw [hc]; decide⟩)
  obtain ⟨r', hr'Mem, hr'Addr⟩ := List.mem_map.mp haddrIn
  have hr'Props := hDec.2.2.2.2.1 r' hr'Mem
  obtain ⟨o, hoMem, hoAddr, hoCs, hoOth, hoTag, hoFun, hoAr, hoCap, hoAS, hoSL, hoFlds,
    hoSD, hoLmb, hoRc⟩ := hr'Props.2.2
  have hoEq : o = rObj := nodup_addr_eq_of_mem hnd2 hoMem hrMem (hoAddr.trans hr'Addr)
  subst hoEq
  have hr'Rc1 : r'.rc = 1#32 := by
    rcases hoRc with ⟨hz, _⟩ | ⟨_, hr'Pos, hr'Le⟩
    · exact absurd hz (by rw [hrRc1]; decide)
    · have h1 : o.rc.toInt = 1 := by rw [hrRc1]; decide
      have hInt : r'.rc.toInt = 1 := by omega
      apply BitVec.eq_of_toInt_eq
      simpa using hInt
  have hr'RcEq : r'.rc = o.rc := hr'Rc1.trans hrRc1.symm
  have hr'Eq : r' = o := by
    cases r'; cases o
    simp only at hr'Addr hoCs hoOth hoTag hoFun hoAr hoCap hoAS hoSL hoFlds hoSD hoLmb hr'RcEq
    subst hr'Addr hr'RcEq hoCs hoOth hoTag hoFun hoAr hoCap hoAS hoSL hoFlds hoSD hoLmb
    rfl
  rwa [← hr'Eq]

/-! ## 2. Specifications for `DemoNatStr` (`addNat`, `addToStr`, `fmtSumTagged`) -/

/-- Specification of `DemoNatStr.addNat`: unboxed-fast-path scalar addition or `lcnfNatSlowSpec`. -/
@[expose] def addNatSpec : Spec [i64, i64, i64] [i64] := fun (rt, a, b, ()) m Q X =>
  if addNatFastOk a b then
    Q ((a - 1#64) + b, ()) m
  else
    lcnfNatSlowSpec (rt, 1#64, a, b, ()) m Q X

/-- Specification of `DemoNatStr.addToStr`: scalar `boxNat aVal`, `boxNat bVal`
(`aVal + bVal < 2^63`) formatted to a newly allocated heap `String`
(`natToDecimalBytes (aVal + bVal)`). -/
@[expose] def addToStrSpec : Spec [i64, i64, i64] [i64] := fun (rt, a, b, ()) m Q _ =>
  ∃ (aVal bVal : Nat),
    a = boxNat aVal ∧ b = boxNat bVal ∧ aVal + bVal < 2 ^ 63 ∧
    ∃ (st : RtC0State) (objs : List LcnfObj) (R : Mem 64 → Prop),
      (∀ o ∈ objs, o.Wf) ∧
      (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
      let dec := natToDecimalBytes (aVal + bVal)
      let bytes := strAllocBytes (dec.length + 1)
      (st.hasFree bytes ∨ bytes ≤ st.rem) ∧
      ∀ (s : BitVec 64) (st' : RtC0State) (m' : Mem 64),
        s ≠ 0#64 → s.toNat % 8 = 0 →
        st'.PreservesMeta st → st'.rem ≤ st.rem →
        let sObj := mkStrObj s 1#32 (dec.length + 1) dec dec.length
        StrCanon sObj →
        (rtC0Inv rt st' ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs ⋆ R) m' →
        Q (s, ()) m'

/-- Well-formedness and reference-count closure invariant for `lcnf_dec_ref_cold`-safe heaps. -/
@[expose] def HeapRcInv (objs : List LcnfObj) : Prop :=
  (∀ o ∈ objs, o.Wf) ∧
  lcnfHeapClosed objs ∧
  (∀ p ∈ objs, p.rc = 0#32 → ∀ f ∈ p.childFields, (f &&& 1#64) = 0#64 →
    ∃ q ∈ objs, q.addr = f ∧ q.rc = 0#32) ∧
  (∀ y ∈ objs, 0 < y.rc.toInt → nonPersistRefs objs y.addr ≤ y.rc.toNat)

/-- Specification of `DemoNatStr.fmtSumTagged`: formats `a + b` (`< 2 ^ 63`) onto an exclusive heap
`String` buffer `tag` in place via `lcnf_string_append` and releases the temporary string via
`lcnf_dec_ref_cold`. -/
@[expose] def fmtSumTaggedSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (rt, tag, a, b, ()) m Q _ =>
    ∃ (aVal bVal : Nat) (tagObj : LcnfObj) (st : RtC0State) (objs : List LcnfObj)
      (R : Mem 64 → Prop),
      a = boxNat aVal ∧ b = boxNat bVal ∧ aVal + bVal < 2 ^ 63 ∧
      tagObj ∈ objs ∧ tagObj.addr = tag ∧ StrCanon tagObj ∧
      let dec := natToDecimalBytes (aVal + bVal)
      let bytes := strAllocBytes (dec.length + 1)
      let newPayload := strPayload tagObj ++ dec
      let newLen := (tagObj.strLen + dec.length) % 2 ^ 64
      tagObj.rc = 1#32 ∧ newPayload.length + 1 ≤ tagObj.cap ∧
      HeapRcInv objs ∧ objs.length + 1 ≤ st.workCap ∧
      (st.hasFree bytes ∨ bytes ≤ st.rem) ∧
      (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
      ∀ (st' : RtC0State) (objs' : List LcnfObj) (m' : Mem 64),
        st'.PreservesMeta st → st'.rem ≤ st.rem →
        let rObj := mkStrObj tag 1#32 tagObj.cap newPayload newLen
        StrCanon rObj → rObj ∈ objs' →
        (rtC0Inv rt st' ⋆ lcnfHeap objs' ⋆ R) m' →
        Q (tag, ()) m'

/-- Specification table for the three functions in `demoNatStrProgMod`. -/
@[expose] def demoNatStrSpecEntries : List SpecEntry :=
  [ SpecEntry.ofFn demoNatStrTfs.tf_0.toFn addNatSpec false
  , SpecEntry.ofFn demoNatStrTfs.tf_1.toFn addToStrSpec false
  , SpecEntry.ofFn demoNatStrTfs.tf_2.toFn fmtSumTaggedSpec false ]

/-- Source-level specification environment for `demoNatStrProgMod`. -/
@[expose] def demoNatStrEnv : Env :=
  Env.ofTable demoNatStrSpecEntries

/-- Combined linked environment (`rtC0CoreEnv` on runtime, `demoNatStrEnv` on `demoNatStrProgMod`).
-/
@[expose] def demoNatStrLinkedEnv : Env :=
  linkRtC0Env demoNatStrEnv

theorem demoNatStrSpecEntries_nodup :
    (demoNatStrSpecEntries.map SpecEntry.name).Nodup := by
  decide

theorem demoNatStrEnv_addNat {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : addNatSpec xs m Q X) :
    demoNatStrEnv "l_LeanQbe_T_LeanLCNF_DemoNatStr_addNat" [i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := SpecEntry.ofFn demoNatStrTfs.tf_0.toFn addNatSpec false)
    (by simp [demoNatStrSpecEntries]) demoNatStrSpecEntries_nodup h

theorem demoNatStrEnv_addToStr {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : addToStrSpec xs m Q X) :
    demoNatStrEnv "l_LeanQbe_T_LeanLCNF_DemoNatStr_addToStr" [i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := SpecEntry.ofFn demoNatStrTfs.tf_1.toFn addToStrSpec false)
    (by simp [demoNatStrSpecEntries]) demoNatStrSpecEntries_nodup h

theorem demoNatStrEnv_fmtSumTagged {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : fmtSumTaggedSpec xs m Q X) :
    demoNatStrEnv "l_LeanQbe_T_LeanLCNF_DemoNatStr_fmtSumTagged"
      [i64, i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := SpecEntry.ofFn demoNatStrTfs.tf_2.toFn fmtSumTaggedSpec false)
    (by simp [demoNatStrSpecEntries]) demoNatStrSpecEntries_nodup h

theorem demoNatStrEnv_addNat_noex {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost}
    (h : demoNatStrEnv demoNatStrTfs.tf_0.toFn.name demoNatStrTfs.tf_0.toFn.as
      demoNatStrTfs.tf_0.toFn.rs xs m Q X) :
    demoNatStrEnv demoNatStrTfs.tf_0.toFn.name demoNatStrTfs.tf_0.toFn.as
      demoNatStrTfs.tf_0.toFn.rs xs m Q X' :=
  demoNatStrEnv_addNat ((Env.ofTable_cons_self _ _ _ _ _ _).mp h)

theorem demoNatStrEnv_addToStr_noex {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost}
    (h : demoNatStrEnv demoNatStrTfs.tf_1.toFn.name demoNatStrTfs.tf_1.toFn.as
      demoNatStrTfs.tf_1.toFn.rs xs m Q X) :
    demoNatStrEnv demoNatStrTfs.tf_1.toFn.name demoNatStrTfs.tf_1.toFn.as
      demoNatStrTfs.tf_1.toFn.rs xs m Q X' :=
  let hne : demoNatStrTfs.tf_0.toFn.name ≠ demoNatStrTfs.tf_1.toFn.name := by decide
  demoNatStrEnv_addToStr
    ((Env.ofTable_cons_self _ _ _ _ _ _).mp ((Env.ofTable_cons_ne hne _ _ _ _).mp h))

theorem demoNatStrEnv_fmtSumTagged_noex {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost}
    (h : demoNatStrEnv demoNatStrTfs.tf_2.toFn.name demoNatStrTfs.tf_2.toFn.as
      demoNatStrTfs.tf_2.toFn.rs xs m Q X) :
    demoNatStrEnv demoNatStrTfs.tf_2.toFn.name demoNatStrTfs.tf_2.toFn.as
      demoNatStrTfs.tf_2.toFn.rs xs m Q X' :=
  let h1 : demoNatStrTfs.tf_0.toFn.name ≠ demoNatStrTfs.tf_2.toFn.name := by decide
  let h2 : demoNatStrTfs.tf_1.toFn.name ≠ demoNatStrTfs.tf_2.toFn.name := by decide
  demoNatStrEnv_fmtSumTagged
    ((Env.ofTable_cons_self _ _ _ _ _ _).mp
      ((Env.ofTable_cons_ne h2 _ _ _ _).mp ((Env.ofTable_cons_ne h1 _ _ _ _).mp h)))

/-! ## 3. Per-Function `Func.wp` Soundness Proofs -/

theorem demo_addNat_wp :
    ∀ xs m Q X, addNatSpec xs m Q X →
      Func.wp demoNatStrLinkedEnv demoNatStrTfs.tf_0.toFn.body xs m Q X := by
  rintro ⟨rt, a, b, ⟨⟩⟩ m Q X hspec
  dsimp only [addNatSpec] at hspec
  change wp demoNatStrLinkedEnv Q X
    (.let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var a) (.var b)) fun v0 =>
      .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var v0.1) (.imm 1#64)) fun v1 =>
        .let_ (_root_.LeanQbe.T.op2 (OpCode.ne i64) (.var v1.1) (.imm 0#64)) fun v2 =>
          .group (sig := [[i64]]) (fun _ => .cons (fun xs => .ret (.var xs.1, ())) .nil)
            fun Js =>
            .jnz (.var v2.1)
              (.let_ (_root_.LeanQbe.T.op2 (OpCode.sub i64) (.var a) (.imm 1#64)) fun v3 =>
                .let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var v3.1) (.var b)) fun v4 =>
                  .let_ (_root_.LeanQbe.T.op2 (OpCode.ult i64) (.var v4.1) (.var b)) fun v5 =>
                    .jnz (.var v5.1)
                      (.call "lcnf_nat_slow" (as := [i64, i64, i64, i64]) (bs := [i64])
                        (.var rt, .imm 1#64, .var a, .var b, ()) fun v6 =>
                        .jump Js.1 (.var v6.1, ()))
                      (.jump Js.1 (.var v4.1, ())))
              (.call "lcnf_nat_slow" (as := [i64, i64, i64, i64]) (bs := [i64])
                (.var rt, .imm 1#64, .var a, .var b, ()) fun v7 =>
                .jump Js.1 (.var v7.1, ()))) m
  c0_let_simp
  refine wp_join_group (fun xs m' => Q xs m') ?_ ?_
  · rintro J ⟨r, ⟨⟩⟩ m' hq
    rw [Blocks.get.eq_1, wp_ret]
    exact hq
  · intro J hJ
    rw [wp_jnz]; dsimp only [Arg.val_var]
    refine ⟨fun hsc => ?_, fun hslow => ?_⟩
    · have hbit : ((a &&& b &&& 1#64) != 0#64) = true := hsc
      c0_let_simp
      rw [wp_jnz]; dsimp only [Arg.val_var]
      refine ⟨fun hov => ?_, fun hfast => ?_⟩
      · have hcond : addNatFastOk a b = false := by
          unfold addNatFastOk; simp [hbit, hov]
        rw [ite_eq_right (by simp [hcond])] at hspec
        refine wp_call_pred _ (linkRtC0Env_of_r1 (by decide) (rtR1Env_lcnf_nat_slow hspec))
          ?_
        intro ⟨res, ⟨⟩⟩ m' hq
        rw [wp_jump]
        exact hJ (res, ()) m' hq
      · have hcond : addNatFastOk a b = true := by
          unfold addNatFastOk; simp [hbit, hfast]
        rw [ite_eq_left (by simp [hcond])] at hspec
        rw [wp_jump]
        exact hJ ((a - 1#64) + b, ()) m hspec
    · have hcond : addNatFastOk a b = false := by
        have hnb : ((a &&& b &&& 1#64) != 0#64) = false := hslow
        unfold addNatFastOk; simp [hnb]
      rw [ite_eq_right (by simp [hcond])] at hspec
      refine wp_call_pred _ (linkRtC0Env_of_r1 (by decide) (rtR1Env_lcnf_nat_slow hspec)) ?_
      intro ⟨res, ⟨⟩⟩ m' hq
      rw [wp_jump]
      exact hJ (res, ()) m' hq

theorem demo_addToStr_wp :
    ∀ xs m Q X, addToStrSpec xs m Q X →
      Func.wp demoNatStrLinkedEnv demoNatStrTfs.tf_1.toFn.body xs m Q X := by
  rintro ⟨rt, a, b, ⟨⟩⟩ m Q X ⟨aVal, bVal, ha, hb, hlt, st, objs, R, hwf, hm, halloc, hk⟩
  subst ha hb
  change wp demoNatStrLinkedEnv Q X
    (.call "l_LeanQbe_T_LeanLCNF_DemoNatStr_addNat" (as := [i64, i64, i64]) (bs := [i64])
      (.var rt, .var (boxNat aVal), .var (boxNat bVal), ()) fun v0 =>
      .call "lcnf_nat_to_str" (as := [i64, i64]) (bs := [i64])
        (.var rt, .var v0.1, ()) fun v1 => .ret (.var v1.1, ())) m
  obtain ⟨hfast, hsumEq⟩ := addNatFastOk_boxNat hlt
  have hCall1 : demoNatStrLinkedEnv "l_LeanQbe_T_LeanLCNF_DemoNatStr_addNat"
      [i64, i64, i64] [i64] (rt, boxNat aVal, boxNat bVal, ()) m
      (fun (sum, ()) m1 => sum = boxNat (aVal + bVal) ∧ m1 = m) X := by
    refine (linkRtC0Env_prog demoNatStrEnv (by decide)).mpr (demoNatStrEnv_addNat ?_)
    dsimp only [addNatSpec]
    rw [ite_eq_left (by simp [hfast])]
    exact ⟨hsumEq, rfl⟩
  refine wp_call_pred _ hCall1 ?_
  rintro ⟨sum, ⟨⟩⟩ m1 ⟨rfl, rfl⟩
  refine wp_call_pred Q (linkRtC0Env_of_r2b (by decide) ?_) ?_
  · change rtR2bEnv "lcnf_nat_to_str" [i64, i64] [i64] (rt, boxNat (aVal + bVal), ()) m1 Q X
    refine rtR2bEnv_lcnf_nat_to_str ?_
    have hsc : (boxNat (aVal + bVal) &&& 1#64) ≠ 0#64 := by
      rw [rt_boxNat_and_one (aVal + bVal) hlt]; decide
    refine ⟨st, aVal + bVal, objs, R, ?_, hwf, hm, ?_⟩
    · unfold NatInHeap
      rw [ite_eq_left hsc]
      unfold boxNat
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 2 * (aVal + bVal) + 1 < 2 ^ 64),
        Nat.shiftRight_eq_div_pow, show (2 ^ 1 : Nat) = 2 by decide]
      omega
    · rw [ite_eq_left hsc]
      exact ⟨halloc, hk⟩
  · intro ⟨s, ⟨⟩⟩ m' hq
    rw [wp_ret]
    exact hq

theorem demo_fmtSumTagged_wp :
    ∀ xs m Q X, fmtSumTaggedSpec xs m Q X →
      Func.wp demoNatStrLinkedEnv demoNatStrTfs.tf_2.toFn.body xs m Q X := by
  rintro ⟨rt, tag, a, b, ⟨⟩⟩ m Q X
    ⟨aVal, bVal, tagObj, st, objs, R, ha, hb, hlt, htagMem, htagAddr, htagCan, htagRc1, hcapFit,
      hrcInv, hworkCap, halloc, hm, hk⟩
  subst ha hb
  change wp demoNatStrLinkedEnv Q X
    (.call "l_LeanQbe_T_LeanLCNF_DemoNatStr_addToStr" (as := [i64, i64, i64]) (bs := [i64])
      (.var rt, .var (boxNat aVal), .var (boxNat bVal), ()) fun v0 =>
      .call "lcnf_string_append" (as := [i64, i64, i64]) (bs := [i64])
        (.var rt, .var tag, .var v0.1, ()) fun v1 =>
        .group (sig := [[]]) (fun _ => .cons (fun _ => .ret (.var v1.1, ())) .nil)
          fun Js =>
          .load i32 (.var v0.1) fun v2 =>
            .let_ (_root_.LeanQbe.T.op2 (OpCode.eq i32) (.var v2) (.imm 1#32)) fun t =>
              .jnz (.var t.1)
                (.call "lcnf_dec_ref_cold" (as := [i64, i64]) (bs := [])
                  (.var rt, .var v0.1, ()) fun _ => .jump Js.1 ())
                (.let_ (_root_.LeanQbe.T.op2 (OpCode.sgt i32) (.var v2) (.imm 1#32)) fun t1 =>
                  .let_ (_root_.LeanQbe.T.op1 (OpCode.ofBool 32) (.var t1.1)) fun t2 =>
                    .let_ (_root_.LeanQbe.T.op2 (OpCode.sub i32) (.var v2) (.var t2.1)) fun t3 =>
                      .store (.var t3.1) (.var v0.1) (.jump Js.1 ()))) m
  have hCall1 : demoNatStrLinkedEnv "l_LeanQbe_T_LeanLCNF_DemoNatStr_addToStr"
      [i64, i64, i64] [i64] (rt, boxNat aVal, boxNat bVal, ()) m
      (fun (s2, ()) m1 =>
        ∃ st1 : RtC0State,
          s2 ≠ 0#64 ∧ s2.toNat % 8 = 0 ∧ st1.PreservesMeta st ∧ st1.rem ≤ st.rem ∧
          let dec := natToDecimalBytes (aVal + bVal)
          let s2Obj := mkStrObj s2 1#32 (dec.length + 1) dec dec.length
          StrCanon s2Obj ∧ (rtC0Inv rt st1 ⋆ lcnfObjMem s2Obj ⋆ lcnfHeap objs ⋆ R) m1) X := by
    refine (linkRtC0Env_prog demoNatStrEnv (by decide)).mpr (demoNatStrEnv_addToStr ?_)
    exact ⟨aVal, bVal, rfl, rfl, hlt, st, objs, R, hrcInv.1, hm, halloc,
      fun s2 st1 m1 hs0 hs8 hpr1 hrem1 hcan1 hm1 =>
        ⟨st1, hs0, hs8, hpr1, hrem1, hcan1, hm1⟩⟩
  refine wp_call_pred _ hCall1 ?_
  rintro ⟨s2, ⟨⟩⟩ m1 ⟨st1, hs20, hs28, hpr1, hrem1, hs2Can, hm1⟩
  let dec := natToDecimalBytes (aVal + bVal)
  let s2Obj := mkStrObj s2 1#32 (dec.length + 1) dec dec.length
  let newPay := strPayload tagObj ++ dec
  let newLen := (tagObj.strLen + dec.length) % 2 ^ 64
  let rObj := mkStrObj tag 1#32 tagObj.cap newPay newLen
  have hm1Heap : (lcnfHeap (s2Obj :: objs) ⋆ (rtC0Inv rt st1 ⋆ R)) m1 := by
    simp only [lcnfHeap]
    exact sep_cast hm1 (by ac_rfl)
  have hnd1 : ((s2Obj :: objs).map LcnfObj.addr).Nodup := lcnfHeap_nodup_addrs hm1Heap
  have hs2NotIn : s2 ∉ objs.map LcnfObj.addr := by
    simpa [s2Obj, mkStrObj] using (List.nodup_cons.mp hnd1).1
  have hs2NeTag : s2 ≠ tag := fun heq =>
    hs2NotIn (heq ▸ htagAddr ▸ List.mem_map_of_mem htagMem)
  have hnd0 : (objs.map LcnfObj.addr).Nodup := (List.nodup_cons.mp hnd1).2
  have hs2Pay : strPayload s2Obj = dec := rt_strPayload_mkStrObj
  have hp2Pos : (strPayload s2Obj).length ≠ 0 := by
    rw [hs2Pay]
    exact Nat.ne_of_gt (natToDecimalBytes_pos (aVal + bVal))
  have hnotOver : ¬ strMaxCap ≤ (strPayload tagObj).length + (strPayload s2Obj).length := by
    have hcapMax : tagObj.cap ≤ strMaxCap := htagCan.2.2.2.2.2.2.2.2.1
    change (strPayload tagObj ++ dec).length + 1 ≤ tagObj.cap at hcapFit
    rw [hs2Pay, ← List.length_append]
    omega
  have hinp : tagObj.rc = 1#32 ∧ (strPayload tagObj ++ strPayload s2Obj).length + 1 ≤
      tagObj.cap := by
    rw [hs2Pay]; exact ⟨htagRc1, hcapFit⟩
  have hrCan : StrCanon rObj := by
    have hnewLenLt : newLen < 2 ^ 64 := Nat.mod_lt _ (by decide)
    exact mkStrObj_canon (htagAddr ▸ htagCan.1) (htagAddr ▸ htagCan.2.1) (by decide) hcapFit
      htagCan.2.2.2.2.2.2.2.2.1 hnewLenLt
  have hCall2 : demoNatStrLinkedEnv "lcnf_string_append" [i64, i64, i64] [i64]
      (rt, tag, s2, ()) m1
      (fun (r, ()) m2 =>
        r = tag ∧
        let objs2 := s2Obj :: objs.map (fun o => if o.addr = tag then rObj else o)
        (rtC0Inv rt st1 ⋆ lcnfHeap objs2 ⋆ R) m2) X := by
    refine linkRtC0Env_of_r2b (by decide) (rtR2bEnv_lcnf_string_append ?_)
    refine ⟨st1, tagObj, s2Obj, s2Obj :: objs, R, List.mem_cons_of_mem _ htagMem, htagAddr,
      htagCan, List.mem_cons_self, rfl, hs2Can, ?_,
      sep_cast hm1Heap (by ac_rfl), ?_⟩
    · intro o ho
      rcases List.mem_cons.mp ho with rfl | ho'
      · exact hs2Can.wf
      · exact hrcInv.1 o ho'
    · rw [ite_eq_right hp2Pos, ite_eq_right hnotOver]
      dsimp only
      rw [ite_eq_left hinp]
      refine ⟨fun h => absurd hinp h, fun r st2 objs2 m2 _ _ _ _ hIn _ hm2 => ?_⟩
      obtain ⟨hrEq, hstEq, hobjs2⟩ := hIn hinp
      rw [hstEq] at hm2
      have hmapEq :
          ((s2Obj :: objs).map fun o =>
            if o.addr = tag then
              mkStrObj tag (1#32) tagObj.cap (strPayload tagObj ++ strPayload s2Obj)
                ((tagObj.strLen + s2Obj.strLen) % 2 ^ 64)
            else o) =
          s2Obj :: objs.map (fun o => if o.addr = tag then rObj else o) := by
        simp only [List.map_cons]
        have hs2Ne : (if s2Obj.addr = tag then
            mkStrObj tag (1#32) tagObj.cap (strPayload tagObj ++ strPayload s2Obj)
              ((tagObj.strLen + s2Obj.strLen) % 2 ^ 64)
            else s2Obj) = s2Obj := ite_eq_right (by simpa [s2Obj, mkStrObj] using hs2NeTag)
        rw [hs2Ne]
        congr 1
        refine List.map_congr_left fun o _ => ?_
        have hEqPay : strPayload tagObj ++ strPayload s2Obj = newPay := by rw [hs2Pay]
        rw [hEqPay]; rfl
      rw [hobjs2, hmapEq] at hm2
      exact ⟨hrEq, hm2⟩
  refine wp_call_pred _ hCall2 ?_
  rintro ⟨r, ⟨⟩⟩ m2 ⟨hrTag, hm2⟩
  subst r
  let objs2 := s2Obj :: objs.map (fun o => if o.addr = tag then rObj else o)
  have hm2' : (lcnfHeap objs2 ⋆ (rtC0Inv rt st1 ⋆ R)) m2 := by
    dsimp only at hm2
    exact sep_cast hm2 (by ac_rfl)
  have hnd2 : (objs2.map LcnfObj.addr).Nodup := lcnfHeap_nodup_addrs hm2'
  have hloadRc : loadVal m2 i32 s2 = some 1#32 := by
    have hld := rt_str_load_rc hs2Can.wf List.mem_cons_self hm2'
    simpa [s2Obj, mkStrObj] using hld
  refine wp_join_group (fun _ m' => Q (tag, ()) m') ?_ ?_
  · rintro J ⟨⟩ m' hq
    rw [Blocks.get.eq_1, wp_ret]
    exact hq
  · intro J hJ
    refine wp_load_of (v := 1#32) (by simpa [Arg.val_var] using hloadRc) ?_
    c0_let_simp
    rw [wp_jnz]
    refine ⟨fun _ => ?_, fun h => absurd h (by simp [Arg.val_var])⟩
    have hobjs2_wf : ∀ o ∈ objs2, o.Wf := by
      intro o ho
      rcases List.mem_cons.mp ho with rfl | ho'
      · exact hs2Can.wf
      · obtain ⟨orig, horig, rfl⟩ := List.mem_map.mp ho'
        split
        · exact hrCan.wf
        · exact hrcInv.1 orig horig
    have hobjs2_map_addr :
        ((objs.map fun o => if o.addr = tag then rObj else o).map LcnfObj.addr) =
        objs.map LcnfObj.addr := by
      rw [List.map_map]
      refine List.map_congr_left fun o _ => ?_
      dsimp only [Function.comp_apply]
      split <;> simp_all [rObj, mkStrObj]
    have hobjs2_closed : lcnfHeapClosed objs2 := by
      intro o ho f hf hptr
      rcases List.mem_cons.mp ho with rfl | ho'
      · have : f ∈ ([] : List (BitVec 64)) := by
          rwa [rt_string_childFields_nil rfl] at hf
        nomatch this
      · obtain ⟨orig, horig, rfl⟩ := List.mem_map.mp ho'
        by_cases htg : orig.addr = tag
        · rw [ite_eq_left htg, rt_string_childFields_nil rfl] at hf
          nomatch hf
        · rw [ite_eq_right htg] at hf
          obtain ⟨o', ho'Mem, ho'Addr⟩ := hrcInv.2.1 orig horig f hf hptr
          refine ⟨if o'.addr = tag then rObj else o',
            List.mem_cons_of_mem _ (List.mem_map_of_mem ho'Mem), ?_⟩
          split
          · rename_i h
            exact h.symm.trans ho'Addr
          · exact ho'Addr
    have hnpEq : ∀ a, nonPersistRefs (objs.map fun o => if o.addr = tag then rObj else o) a =
        nonPersistRefs objs a := by
      intro a
      have hsub : ∀ xs : List LcnfObj,
          (∀ o ∈ xs, o.addr = tag → o.childFields = []) →
          nonPersistRefs (xs.map fun o => if o.addr = tag then rObj else o) a =
          nonPersistRefs xs a := by
        intro xs hnil
        induction xs with
        | nil => rfl
        | cons x xs ih =>
          rw [List.map_cons, nonPersistRefs_cons, nonPersistRefs_cons,
            ih (fun o ho => hnil o (List.mem_cons_of_mem _ ho))]
          by_cases hxt : x.addr = tag
          · have hxNil := hnil x List.mem_cons_self hxt
            rw [ite_eq_left hxt, rt_string_childFields_nil rfl]
            simp [hxNil]
          · rw [ite_eq_right hxt]
      exact hsub objs fun o ho hoad => by
        have hoeq : o = tagObj := nodup_addr_eq_of_mem hnd0 ho htagMem (hoad.trans htagAddr.symm)
        subst hoeq
        exact rt_string_childFields_nil htagCan.2.2.2.2.2.1
    have hrcSound : RcSound s2 objs2 := by
      refine ⟨?_, ?_⟩
      · intro p hp hp0 f hf hptr
        rcases List.mem_cons.mp hp with rfl | hp'
        · simp [s2Obj, mkStrObj] at hp0
        · obtain ⟨orig, horig, horigEq⟩ := List.mem_map.mp hp'
          by_cases hot : orig.addr = tag
          · rw [ite_eq_left hot] at horigEq; subst horigEq
            simp [rObj, mkStrObj] at hp0
          · rw [ite_eq_right hot] at horigEq; subst horigEq
            obtain ⟨q, hqMem, hqAddr, hqRc⟩ := hrcInv.2.2.1 orig horig hp0 f hf hptr
            have hqNeTag : q.addr ≠ tag := fun hqt => by
              have hqEq : q = tagObj :=
                nodup_addr_eq_of_mem hnd0 hqMem htagMem (hqt.trans htagAddr.symm)
              rw [hqEq, htagRc1] at hqRc
              exact absurd hqRc (by decide)
            refine ⟨if q.addr = tag then rObj else q,
              List.mem_cons_of_mem _ (List.mem_map_of_mem hqMem), ?_⟩
            rw [ite_eq_right hqNeTag]
            exact ⟨hqAddr, hqRc⟩
      · intro y hy hyPos
        rw [nonPersistRefs_cons, rt_string_childFields_nil rfl]
        change (if s2Obj.rc = 0#32 then 0 else List.count y.addr []) +
          nonPersistRefs (objs.map fun o => if o.addr = tag then rObj else o) y.addr +
          (if y.addr = s2 then 1 else 0) ≤ y.rc.toNat
        simp only [List.count_nil, ite_self, Nat.zero_add, hnpEq y.addr]
        rcases List.mem_cons.mp hy with rfl | hy'
        · have hs2NotChild : nonPersistRefs objs s2Obj.addr = 0 :=
            nonPersistRefs_zero_of_not_mem hrcInv.2.1 (bv64_and1_zero_of_mod8 hs28) hs2NotIn
          rw [hs2NotChild]
          simp [s2Obj, mkStrObj]
        · obtain ⟨orig, horig, horigEq⟩ := List.mem_map.mp hy'
          have hyAddrEq : y.addr = orig.addr := by
            subst horigEq
            split
            · rename_i h
              exact h.symm
            · rfl
          have hyNe : y.addr ≠ s2 := fun h =>
            hs2NotIn (h ▸ hyAddrEq ▸ List.mem_map_of_mem horig)
          rw [ite_eq_right hyNe, Nat.add_zero]
          by_cases hot : orig.addr = tag
          · rw [ite_eq_left hot] at horigEq
            subst horigEq
            have horigTag : orig = tagObj :=
              nodup_addr_eq_of_mem hnd0 horig htagMem (hot.trans htagAddr.symm)
            have hrcEq : rObj.rc = orig.rc := by rw [horigTag, htagRc1]; rfl
            rw [hrcEq, hyAddrEq]
            exact hrcInv.2.2.2 orig horig (by rw [← hrcEq]; exact hyPos)
          · rw [ite_eq_right hot] at horigEq
            subst horigEq
            exact hrcInv.2.2.2 orig horig hyPos
    refine wp_call_pred (fun () m' => Q (tag, ()) m')
      (linkRtC0Env_of_rt (by decide) (rtC0CoreEnv_lcnf_dec_ref_cold ?_)) ?_
    · refine ⟨bv64_and1_zero_of_mod8 hs28, st1, objs2, R, ?_, hm2,
        ⟨s2Obj, List.mem_cons_self, rfl, rfl⟩, hobjs2_wf, hobjs2_closed, hrcSound, ?_⟩
      · simpa [objs2, RtC0State.workCap_eq_of_preservesMeta hpr1] using hworkCap
      · intro st' objs' m' hpr2 hrem2 hdec hm'
        have hrMem2 : rObj ∈ objs2 :=
          List.mem_cons_of_mem _ (List.mem_map.mpr ⟨tagObj, htagMem, by simp [htagAddr]⟩)
        have hrIn' : rObj ∈ objs' := by
          refine rt_mkStrObj_rc_eq hnd2 hrMem2 hs2NeTag.symm rfl ?_ hdec
          intro o ho hoad
          rcases List.mem_cons.mp ho with rfl | ho'
          · exact rt_string_childFields_nil rfl
          · exfalso
            have had : o.addr ∈ objs.map LcnfObj.addr := by
              rw [← hobjs2_map_addr]
              exact List.mem_map_of_mem ho'
            exact hs2NotIn (hoad ▸ had)
        exact hk st' objs' m' (hpr1.trans hpr2) (by omega) hrCan hrIn' hm'
    · intro ⟨⟩ m' hq
      rw [wp_jump]
      exact hJ () m' hq

/-! ## 4. Whole-Module Soundness & Compositional `ModuleOk` -/

theorem demoNatStrLinkedMod_checkAcyclic :
    demoNatStrLinkedMod.checkAcyclic = true := by
  decide

theorem demoNatStrProgMod_fns_eq :
    (lcnfProgMod demoNatStrTfs).fns =
      [demoNatStrTfs.tf_0.toFn, demoNatStrTfs.tf_1.toFn, demoNatStrTfs.tf_2.toFn] :=
  rfl

theorem demoNatStrProgMod_wp :
    ∀ fn ∈ (lcnfProgMod demoNatStrTfs).fns,
      ∀ xs m Q X, demoNatStrEnv fn.name fn.as fn.rs xs m Q X →
        Func.wp demoNatStrLinkedEnv fn.body xs m Q X := by
  intro fn hfn xs m Q X hpre
  rw [demoNatStrProgMod_fns_eq] at hfn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl
  · exact demo_addNat_wp xs m Q X ((Env.ofTable_cons_self _ _ _ _ _ _).mp hpre)
  · have h1 : (demoNatStrTfs.tf_0.toFn.name ≠ demoNatStrTfs.tf_1.toFn.name) := by decide
    have hpre' := (Env.ofTable_cons_ne h1 _ _ _ _).mp hpre
    exact demo_addToStr_wp xs m Q X ((Env.ofTable_cons_self _ _ _ _ _ _).mp hpre')
  · have h1 : (demoNatStrTfs.tf_0.toFn.name ≠ demoNatStrTfs.tf_2.toFn.name) := by decide
    have h2 : (demoNatStrTfs.tf_1.toFn.name ≠ demoNatStrTfs.tf_2.toFn.name) := by decide
    have hpre' := (Env.ofTable_cons_ne h2 _ _ _ _).mp ((Env.ofTable_cons_ne h1 _ _ _ _).mp hpre)
    exact demo_fmtSumTagged_wp xs m Q X ((Env.ofTable_cons_self _ _ _ _ _ _).mp hpre')

/-- Whole-module `ModuleOk` composition combining `rtC0CoreMod` (`80` fns) and `demoNatStrProgMod`
(`3` fns) under `demoNatStrLinkedEnv` via `linkLcnfWithRtC0_moduleOk`. -/
theorem demoNatStrLinkedMod_moduleOk :
    ModuleOk demoNatStrLinkedEnv demoNatStrLinkedMod :=
  linkLcnfWithRtC0_moduleOk demoNatStrEnv demoNatStrLinkedMod_checkAcyclic demoNatStrProgMod_wp

/-! ## 5. Concrete String+DAG Heap Fixture (`"sum="`) for Closed Machine Witnesses -/

/-- Address of the exclusive `"sum="` string buffer packed immediately after `nvDagObjs`. -/
@[expose] def demoTagAddr : BitVec 64 := nvDagBase + 112#64

/-- Mutable exclusive `"sum="` string (`cap := 16`, `rc := 1`) for `fmtSumTagged`. -/
@[expose] def demoTagObj : LcnfObj :=
  mkStrObj demoTagAddr 1#32 16 [115, 117, 109, 61] 4

/-- Concrete 6-object heap list combining `demoTagObj` and `nvDagObjs`. -/
@[expose] def demoTagObjs : List LcnfObj :=
  demoTagObj :: nvDagObjs

@[expose] def demoTagHdrBytes : List UInt8 :=
  bytes64 [demoTagObj.header, 5#64, 16#64, 4#64]

@[expose] def demoTagPayBytes : List UInt8 :=
  [115, 117, 109, 61, 0]

@[expose] def demoTagPadBytes : List UInt8 :=
  List.replicate 11 0

@[expose] def demoTagBytes : List UInt8 :=
  (demoTagHdrBytes ++ demoTagPayBytes) ++ demoTagPadBytes

/-- Concrete `Mem 64` image extending `nvDagMem` with the exclusive `"sum="` string slab. -/
@[expose] def demoTagMem : Mem 64 :=
  ((nvRtBytes ++ nvDagBytes) ++ demoTagBytes).At nvRtBase

private theorem demo_sep_append {P Q : Mem 64 → Prop} {a : BitVec 64} {bs1 bs2 : List UInt8}
    {n1 n2 : Nat} (h1 : bs1.length = n1) (h2 : bs2.length = n2) (hfit : n1 + n2 ≤ 2 ^ 64)
    (hp : P (bs1.At a)) (hq : Q (bs2.At (a + BitVec.ofNat 64 n1))) :
    (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have hs := (congrFun (Mem.At_append_sep bs1 bs2 a (by omega)) ((bs1 ++ bs2).At a)).mp rfl
  exact sep_mono (fun _ h => h ▸ hp) (sep_mono_r (fun _ h => h ▸ (h1 ▸ hq)) hs)

private theorem demo_prefix_len : (nvRtBytes ++ nvDagBytes).length = 33912 := by
  have hRt : nvRtBytes.length = 33800 := by
    simp only [nvRtBytes, List.length_append, bytes64_length, List.length_replicate,
      rtExtraSlots, rtGlobalSlots, rtNumClasses, nvHdrWords, nvRtState, initRtC0State,
      nvWorkCap, nvRem, List.length_cons, List.length_nil]
  have hDag : nvDagBytes.length = 112 := by decide
  rw [List.length_append, hRt, hDag]

private theorem demoTagBytes_ok :
    demoTagBytes.length = 48 ∧ lcnfObjMem demoTagObj (demoTagBytes.At demoTagAddr) := by
  have hHdrArr : array64 demoTagAddr [demoTagObj.header, 5#64, 16#64, 4#64]
      (demoTagHdrBytes.At demoTagAddr) :=
    array64_bytes demoTagAddr _ (by decide)
  have hHdrPay := demo_sep_append
    (Q := bytes (demoTagAddr + 32#64) demoTagObj.scalarData)
    (by decide : demoTagHdrBytes.length = 32)
    (by decide : demoTagPayBytes.length = 5) (by decide) hHdrArr rfl
  have hAll := demo_sep_append
    (Q := region (demoTagAddr + 37#64) 11)
    (by decide : (demoTagHdrBytes ++ demoTagPayBytes).length = 37)
    (by decide : demoTagPadBytes.length = 11) (by decide) hHdrPay
    ⟨demoTagPadBytes, by decide, rfl⟩
  refine ⟨by decide, ?_⟩
  unfold lcnfObjMem
  have heq4 : demoTagObj.tag = stringTag := rfl
  simp only [heq4, ↓reduceIte]
  have htb : demoTagObj.totalBytes - (32 + demoTagObj.scalarData.length) = 11 := by decide
  have h37 : demoTagObj.addr + BitVec.ofNat 64 (32 + demoTagObj.scalarData.length) =
      demoTagAddr + 37#64 := by decide
  rw [htb, h37]
  simp only [array64, BitVec.add_assoc, sep_emp] at hAll
  exact sep_cast hAll (by simp only [demoTagObj, mkStrObj]; ac_rfl)

theorem demoTagMem_ok :
    (rtC0Inv nvRtBase nvRtState ⋆ lcnfHeap demoTagObjs) demoTagMem := by
  have haddr : demoTagAddr = nvRtBase + BitVec.ofNat 64 33912 := by decide
  have hpref := demo_sep_append
    (P := rtC0Inv nvRtBase nvRtState ⋆ lcnfHeap nvDagObjs)
    (Q := lcnfObjMem demoTagObj)
    demo_prefix_len demoTagBytes_ok.1 (by decide) nvDagMem_ok (haddr ▸ demoTagBytes_ok.2)
  change (rtC0Inv nvRtBase nvRtState ⋆ lcnfHeap (demoTagObj :: nvDagObjs)) demoTagMem
  simp only [lcnfHeap]
  rw [sep_comm (lcnfObjMem demoTagObj), ← sep_assoc]
  exact hpref

theorem demoTagObj_canon : StrCanon demoTagObj :=
  mkStrObj_canon (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem demoTagObjs_heapRcInv : HeapRcInv demoTagObjs := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro o ho
    simp only [demoTagObjs, nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (unfold LcnfObj.Wf LcnfObj.totalBytes; decide)
  · intro o ho f hf hf0
    simp only [demoTagObjs, nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [LcnfObj.childFields, demoTagObj, mkStrObj, nvObjA, nvObjB, nvObjC, nvObjP, nvObjU,
        stringTag, closureTag, arrayTag] at hf
    · exact hf.elim (fun h => h ▸ ⟨nvObjB, by simp [demoTagObjs, nvDagObjs], rfl⟩)
        (fun h => h ▸ ⟨nvObjC, by simp [demoTagObjs, nvDagObjs], rfl⟩)
    · exact ⟨nvObjC, by simp [demoTagObjs, nvDagObjs], hf.symm⟩
    · exact hf.elim (fun h => absurd (h ▸ hf0) (by decide))
        (fun h => h ▸ ⟨nvObjP, by simp [demoTagObjs, nvDagObjs], rfl⟩)
    · exact absurd (hf ▸ hf0) (by decide)
    · exact absurd (hf ▸ hf0) (by decide)
  · intro p hp hp0 f hf hf0
    simp only [demoTagObjs, nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd hp0 (by decide) | (
      change f ∈ [11#64] at hf; simp only [List.mem_singleton] at hf; subst hf
      exact absurd hf0 (by decide))
  · intro y hy hyPos
    simp only [demoTagObjs, nvDagObjs, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | decide | exact absurd hyPos (by decide)

end LeanQbe.T.LeanLCNF
