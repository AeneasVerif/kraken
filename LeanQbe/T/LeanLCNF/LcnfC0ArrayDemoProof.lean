module

public import LeanQbe.T.LeanLCNF.LcnfC0ArrayDemo
public import LeanQbe.T.LeanLCNF.LcnfC0LinkKit
public import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.Rules

/-!
# Soundness Proofs, `ModuleOk`, & Concrete Slab Fixtures (`LcnfC0ArrayDemoProof`)

Target-generic (`0` arch imports, `0` `import all`) soundness proofs for the three R2 container
clients in `LcnfC0ArrayDemo`, composing R2 (`LcnfC0Containers`) and R0 (`LcnfC0Rt`) contracts
through `LcnfC0LinkKit`: `arrayPushSetGetSpec`, `baPushSetGetSpec`, `baCowSetGetSpec`, whole-module
`arrayDemoLinkedMod_moduleOk`, and concrete `0x1000#64` slab fixtures (`arrayRtBytes`,
`arrayCowBytes`) with a shared `rc = 2` `ByteArray` `[10, 20]`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step

/-! ## 1. Pure Functional Identities & BitVec / Heap Helpers -/

theorem arrayPushSetGet_eq (a b c : Nat) : ArrayDemo.arrayPushSetGet a b c = c + b := by
  simp [ArrayDemo.arrayPushSetGet]

theorem baPushSetGet_eq (cap : Nat) (a b c : UInt8) :
    ArrayDemo.baPushSetGet cap a b c = c + b := by
  simp [ArrayDemo.baPushSetGet, ByteArray.get!, ByteArray.set!, ByteArray.push,
    ByteArray.emptyWithCapacity, Array.getElem_push, Array.size_push]
  intro h
  exact absurd h (by decide)

private theorem arr_boxNat_and_one {n : Nat} (hn : n < 2 ^ 63) :
    (boxNat n &&& 1#64) = 1#64 := by
  have h1 : (1#64 : BitVec 64).toNat = 1 := by decide
  have hmod : (2 * n + 1) % 2 ^ 64 = 2 * n + 1 := Nat.mod_eq_of_lt (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, h1, Nat.and_one_is_mod, boxNat, BitVec.toNat_ofNat, hmod]
  omega

private theorem arr_boxNat_shr1 {n : Nat} (hn : n < 2 ^ 63) :
    (boxNat n >>> 1).toNat = n := by
  unfold boxNat
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.shiftRight_eq_div_pow, show (2 ^ 1 : Nat) = 2 by decide]
  omega

private theorem arr_boxNat_add_fast {aVal bVal : Nat} (hlt : aVal + bVal < 2 ^ 63) :
    ((boxNat aVal &&& boxNat bVal &&& 1#64) != 0#64) = true ∧
    ((boxNat aVal - 1#64 + boxNat bVal).ult (boxNat bVal)) = false ∧
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
  have ha1 : (boxNat aVal &&& 1#64) = 1#64 := arr_boxNat_and_one (by omega)
  have hb1 : (boxNat bVal &&& 1#64) = 1#64 := arr_boxNat_and_one (by omega)
  have hlsb : (boxNat aVal &&& boxNat bVal &&& 1#64) = 1#64 := by
    rw [BitVec.and_assoc, hb1, ha1]
  have hbit : ((boxNat aVal &&& boxNat bVal &&& 1#64) != 0#64) = true := by
    rw [hlsb]; decide
  have hult : ((boxNat aVal - 1#64 + boxNat bVal).ult (boxNat bVal)) = false := by
    rw [BitVec.ult, decide_eq_false_iff_not, hadd, hb]
    omega
  exact ⟨hbit, hult, hsumEq⟩

private theorem arr_and1_zero_of_mod8 {p : BitVec 64} (hp8 : p.toNat % 8 = 0) :
    (p &&& 1#64) = 0#64 := by
  have h1 : (1#64 : BitVec 64).toNat = 1 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, h1, Nat.and_one_is_mod]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  omega

private theorem uint8_ofNat_setWidth64 (v : BitVec 8) :
    UInt8.ofNat (v.setWidth 64).toNat = ⟨v⟩ := by
  have hv : (v.setWidth 64).toNat = v.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide))]
  rw [hv]
  apply UInt8.eq_of_toBitVec_eq
  simp [UInt8.ofNat]

private theorem setWidth8_ofNat64 (u : UInt8) :
    (BitVec.ofNat 64 u.toNat).setWidth 8 = u.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  have hu : u.toNat < 2 ^ 8 := u.toBitVec.isLt
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans hu (by decide)), Nat.mod_eq_of_lt hu]
  rfl

private theorem arr_wp_call {Γ : Env} {rs as bs : List Ty} {f : Sym}
    {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont rs}
    {m : Mem 64} {Q : Post rs} {X : XPost} (P : Post bs)
    (hcall : Γ f as bs (vals args) m P X)
    (hk : ∀ r m', P r m' → wp Γ Q X (k r) m') :
    wp Γ Q X (.call f args k) m :=
  ⟨P, X, hcall, hk, fun _ _ _ _ hx => hx⟩

private theorem lcnfObjMem_arr_load_rc1 {p : BitVec 64} {cap : Nat} {elems : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem (mkArrObj p 1#32 cap elems) ⋆ R) m) :
    loadVal m i32 p = some 1#32 := by
  have hmem : (cell64 p (mkArrObj p 1#32 cap elems).header ⋆
      ((cell64 (p + 8#64) (BitVec.ofNat 64 elems.length) ⋆
        cell64 (p + 16#64) (BitVec.ofNat 64 cap) ⋆
        array64 (p + 24#64) elems ⋆
        region (p + BitVec.ofNat 64 (24 + 8 * elems.length))
          (8 * (cap - elems.length))) ⋆ R)) m := by
    unfold lcnfObjMem at hm
    have htag : (mkArrObj p 1#32 cap elems).tag = arrayTag := rfl
    simp only [htag, ↓reduceIte] at hm
    exact sep_cast hm (by ac_rfl)
  have hld := loadVal_bits_of_cell64 (n := 32) (Or.inr (Or.inr (Or.inl rfl))) hmem
  rw [mkArrObj_header] at hld
  simpa [arrHeaderWord] using hld

private theorem lcnfObjMem_ba_load_rc1 {p : BitVec 64} {cap : Nat} {data : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem (mkBaObj p 1#32 cap data) ⋆ R) m) :
    loadVal m i32 p = some 1#32 := by
  have hmem : (cell64 p (mkBaObj p 1#32 cap data).header ⋆
      ((cell64 (p + 8#64) (BitVec.ofNat 64 data.length) ⋆
        cell64 (p + 16#64) (BitVec.ofNat 64 cap) ⋆
        bytes (p + 24#64) data ⋆
        region (p + BitVec.ofNat 64 (24 + data.length))
          ((mkBaObj p 1#32 cap data).totalBytes - (24 + data.length))) ⋆ R)) m := by
    unfold lcnfObjMem at hm
    have htag : (mkBaObj p 1#32 cap data).tag = sarrayTag := rfl
    simp only [htag, ↓reduceIte] at hm
    exact sep_cast hm (by ac_rfl)
  have hld := loadVal_bits_of_cell64 (n := 32) (Or.inr (Or.inr (Or.inl rfl))) hmem
  rw [mkBaObj_header] at hld
  simpa [baHeaderWord] using hld

private theorem arr_decColdRel_singleton_nil {obj : LcnfObj} {objs' : List LcnfObj}
    (hrel : DecColdRel obj.addr [obj] objs') : objs' = [] := by
  cases objs' with
  | nil => rfl
  | cons o' rest =>
    have ho' := hrel.2.2.2.2.1 o' List.mem_cons_self
    obtain ⟨o, hoMem, hoAddr, _⟩ := ho'.2.2
    rw [List.mem_singleton] at hoMem
    subst hoMem
    exact absurd hoAddr.symm ho'.2.1

/-! ## 2. Reusable Lowered-IR Pattern WP Helpers -/

private def arrDecScalarExpr (rt obj : Val i64) (cont : Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var obj) (.imm 1#64)) fun b0 =>
    .let_ (_root_.LeanQbe.T.op2 (OpCode.ne i64) (.var b0.1) (.imm 0#64)) fun b1 =>
      .group (sig := [[]]) (fun _ => .cons (fun _ => cont) .nil) fun J =>
        .jnz (.var b1.1) (.jump J.1 ())
          (.load i32 (.var obj) fun rc =>
            .let_ (_root_.LeanQbe.T.op2 (OpCode.eq i32) (.var rc) (.imm 1#32)) fun is1 =>
              .jnz (.var is1.1)
                (.call "lcnf_dec_ref_cold" (as := [i64, i64]) (bs := [])
                  (.var rt, .var obj, ()) fun _ => .jump J.1 ())
                (.let_ (_root_.LeanQbe.T.op2 (OpCode.sgt i32) (.var rc) (.imm 1#32)) fun gt1 =>
                  .let_ (_root_.LeanQbe.T.op1 (OpCode.ofBool 32) (.var gt1.1)) fun b =>
                    .let_ (_root_.LeanQbe.T.op2 (OpCode.sub i32) (.var rc) (.var b.1)) fun rc' =>
                      .store (.var rc'.1) (.var obj) (.jump J.1 ())))

private theorem wp_arrDecScalarExpr {Γ : Env} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    {rt obj : Val i64} {cont : Expr Val Cont [i64]}
    (hsc : (obj &&& 1#64) = 1#64) (hcont : wp Γ Q X cont m) :
    wp Γ Q X (arrDecScalarExpr rt obj cont) m := by
  have hbit : ((obj &&& 1#64) != 0#64) = true := by rw [hsc]; decide
  dsimp only [arrDecScalarExpr]
  c0_let_simp
  refine wp_join_group (fun _ m' => m' = m) ?_ ?_
  · rintro J ⟨⟩ m' hm'; subst m'; rw [Blocks.get.eq_1]; exact hcont
  · intro J hJ
    rw [wp_jnz]
    refine ⟨fun _ => ?_, fun h => absurd h (by simp [Arg.val_var, hbit])⟩
    rw [wp_jump]; exact hJ () m rfl

private def arrDecObjExpr {rs : List Ty} (rt obj : Val i64) (cont : Expr Val Cont rs) :
    Expr Val Cont rs :=
  .group (sig := [[]]) (fun _ => .cons (fun _ => cont) .nil) fun J =>
    .load i32 (.var obj) fun rc =>
      .let_ (_root_.LeanQbe.T.op2 (OpCode.eq i32) (.var rc) (.imm 1#32)) fun is1 =>
        .jnz (.var is1.1)
          (.call "lcnf_dec_ref_cold" (as := [i64, i64]) (bs := [])
            (.var rt, .var obj, ()) fun _ => .jump J.1 ())
          (.let_ (_root_.LeanQbe.T.op2 (OpCode.sgt i32) (.var rc) (.imm 1#32)) fun gt1 =>
            .let_ (_root_.LeanQbe.T.op1 (OpCode.ofBool 32) (.var gt1.1)) fun b =>
              .let_ (_root_.LeanQbe.T.op2 (OpCode.sub i32) (.var rc) (.var b.1)) fun rc' =>
                .store (.var rc'.1) (.var obj) (.jump J.1 ()))

private theorem wp_arrDecObjExpr_free_singleton {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {rt : Val i64} {obj : LcnfObj} {st : RtC0State} {R : Mem 64 → Prop}
    {cont : Expr Val Cont rs}
    (hcallRt : ∀ m0 P, lcnfDecRefColdSpec (rt, obj.addr, ()) m0 P X →
      Γ "lcnf_dec_ref_cold" [i64, i64] [] (rt, obj.addr, ()) m0 P X)
    (hp8 : obj.addr.toNat % 8 = 0) (hrc1 : obj.rc = 1#32) (hwf : obj.Wf)
    (hfieldsScalar : ∀ f ∈ obj.childFields, (f &&& 1#64) = 1#64)
    (hwc : 1 ≤ st.workCap) (hld : loadVal m i32 obj.addr = some 1#32)
    (hm : (rtC0Inv rt st ⋆ lcnfObjMem obj ⋆ R) m)
    (hcont : ∀ st' m', st'.PreservesMeta st → st'.rem = st.rem →
      (rtC0Inv rt st' ⋆ R) m' → wp Γ Q X cont m') :
    wp Γ Q X (arrDecObjExpr rt obj.addr cont) m := by
  dsimp only [arrDecObjExpr]
  let PostDec : Post [] := fun () m' =>
    ∃ st' : RtC0State, st'.PreservesMeta st ∧ st'.rem = st.rem ∧ (rtC0Inv rt st' ⋆ R) m'
  refine wp_join_group PostDec ?_ ?_
  · rintro J ⟨⟩ m' ⟨st', hpr, hrem, hm'⟩
    rw [Blocks.get.eq_1]
    exact hcont st' m' hpr hrem hm'
  · intro J hJ
    refine wp_load_of (v := 1#32) (by simpa [Arg.val_var] using hld) ?_
    c0_let_simp
    rw [wp_jnz]
    refine ⟨fun _ => ?_, fun h => absurd h (by simp [Arg.val_var])⟩
    have hp0 : (obj.addr &&& 1#64) = 0#64 := arr_and1_zero_of_mod8 hp8
    have hclosed : lcnfHeapClosed [obj] := by
      intro o ho f hf hf0
      rw [List.mem_singleton] at ho; subst ho
      have h1 := hfieldsScalar f hf
      rw [hf0] at h1
      exact absurd h1 (by decide)
    have hnotMem : obj.addr ∉ obj.childFields := fun hmem => by
      have h1 := hfieldsScalar obj.addr hmem
      rw [hp0] at h1
      exact absurd h1 (by decide)
    have hrcSound : RcSound obj.addr [obj] := by
      refine ⟨?_, ?_⟩
      · intro p hp hp0'
        rw [List.mem_singleton] at hp; subst hp
        rw [hrc1] at hp0'; exact absurd hp0' (by decide)
      · intro y hy _
        rw [List.mem_singleton] at hy; subst hy
        simp only [nonPersistRefs, List.foldl_cons, List.foldl_nil, hrc1,
          List.count_eq_zero.mpr hnotMem]
        decide
    have hmHeap : (rtC0Inv rt st ⋆ lcnfHeap [obj] ⋆ R) m := by
      simp only [lcnfHeap, sep_emp]; exact hm
    have hDec : lcnfDecRefColdSpec (rt, obj.addr, ()) m PostDec X := by
      refine ⟨hp0, st, [obj], R, hwc, hmHeap, ⟨obj, List.mem_cons_self, rfl, hrc1⟩,
        fun o ho => by rw [List.mem_singleton] at ho; subst ho; exact hwf,
        hclosed, hrcSound, ?_⟩
      intro st' objs' m' hpr hrem hrel hm'
      have hnil := arr_decColdRel_singleton_nil hrel
      subst hnil
      simp only [lcnfHeap, sep_emp] at hm'
      exact ⟨st', hpr, hrem, sep_cast hm' (by ac_rfl)⟩
    refine arr_wp_call PostDec (hcallRt m PostDec hDec) ?_
    rintro ⟨⟩ m' hpost
    rw [wp_jump]
    exact hJ () m' hpost

private def arrNatAddExpr (rt a b : Val i64) (cont : Tup Val [i64] → Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var a) (.var b)) fun v0 =>
    .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var v0.1) (.imm 1#64)) fun v1 =>
      .let_ (_root_.LeanQbe.T.op2 (OpCode.ne i64) (.var v1.1) (.imm 0#64)) fun v2 =>
        .group (sig := [[i64]]) (fun _ => .cons cont .nil) fun Jsum =>
          .jnz (.var v2.1)
            (.let_ (_root_.LeanQbe.T.op2 (OpCode.sub i64) (.var a) (.imm 1#64)) fun v3 =>
              .let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var v3.1) (.var b)) fun v4 =>
                .let_ (_root_.LeanQbe.T.op2 (OpCode.ult i64) (.var v4.1) (.var b)) fun v5 =>
                  .jnz (.var v5.1)
                    (.call "lcnf_nat_slow" (as := [i64, i64, i64, i64]) (bs := [i64])
                      (.var rt, .imm 1#64, .var a, .var b, ()) fun v6 =>
                      .jump Jsum.1 (.var v6.1, ()))
                    (.jump Jsum.1 (.var v4.1, ())))
            (.call "lcnf_nat_slow" (as := [i64, i64, i64, i64]) (bs := [i64])
              (.var rt, .imm 1#64, .var a, .var b, ()) fun v7 => .jump Jsum.1 (.var v7.1, ()))

private theorem wp_arrNatAddExpr_fast {Γ : Env} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    {rt : Val i64} {aVal bVal : Nat} {cont : Tup Val [i64] → Expr Val Cont [i64]}
    (hlt : aVal + bVal < 2 ^ 63) (hcont : wp Γ Q X (cont (boxNat (aVal + bVal), ())) m) :
    wp Γ Q X (arrNatAddExpr rt (boxNat aVal) (boxNat bVal) cont) m := by
  obtain ⟨hbit, hult, heq⟩ := arr_boxNat_add_fast hlt
  dsimp only [arrNatAddExpr]
  c0_let_simp
  refine wp_join_group (fun s m' => s.1 = boxNat (aVal + bVal) ∧ m' = m) ?_ ?_
  · rintro Jsum ⟨sVal, ⟨⟩⟩ m' ⟨rfl, hm'⟩; subst m'; rw [Blocks.get.eq_1]; exact hcont
  · intro Jsum hJsum
    rw [wp_jnz]
    refine ⟨fun _ => ?_, fun h => absurd h (by simp [Arg.val_var, hbit])⟩
    c0_let_simp
    rw [wp_jnz]
    refine ⟨fun h => absurd h (by simp [Arg.val_var, hult]), fun _ => ?_⟩
    rw [wp_jump]; exact hJsum _ m ⟨heq, rfl⟩

/-! ## 3. Specifications & Combined Environment (`arrayDemoLinkedEnv`) -/

/-- Specification of `ArrayDemo.arrayPushSetGet`: allocates a 4-slot `Array Nat`, pushes `a` & `b`,
replaces slot `0` with `c` in place, reads slots `0` & `1`, frees the array, and returns
`boxNat (ArrayDemo.arrayPushSetGet aVal bVal cVal)`. -/
@[expose] def arrayPushSetGetSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (rt, a, b, c, ()) m Q _ =>
    ∃ (aVal bVal cVal : Nat) (st : RtC0State) (R : Mem 64 → Prop),
      a = boxNat aVal ∧ b = boxNat bVal ∧ c = boxNat cVal ∧
      aVal < 2 ^ 63 ∧ cVal + bVal < 2 ^ 63 ∧
      1 ≤ st.workCap ∧ (st.hasFree (arrAllocBytes 4) ∨ arrAllocBytes 4 ≤ st.rem) ∧
      (rtC0Inv rt st ⋆ R) m ∧
      ∀ (st' : RtC0State) (m' : Mem 64),
        st'.PreservesMeta st → st'.rem ≤ st.rem →
        (rtC0Inv rt st' ⋆ R) m' →
        Q (boxNat (ArrayDemo.arrayPushSetGet aVal bVal cVal), ()) m'

/-- Specification of `ArrayDemo.baPushSetGet`: allocates a `ByteArray` (`capVal ≥ 2`), pushes
`a` & `b`, replaces byte `0` with `c` in place, reads bytes `0` & `1`, frees the `ByteArray`, and
returns `(ArrayDemo.baPushSetGet capVal ⟨a⟩ ⟨b⟩ ⟨c⟩).toBitVec`. -/
@[expose] def baPushSetGetSpec : Spec [i64, i64, i8, i8, i8] [i8] :=
  fun (rt, cap, a, b, c, ()) m Q _ =>
    ∃ (capVal : Nat) (st : RtC0State) (R : Mem 64 → Prop),
      cap = boxNat capVal ∧ 2 ≤ capVal ∧ capVal ≤ baMaxCap ∧
      1 ≤ st.workCap ∧
      (st.hasFree (baAllocBytes capVal) ∨ baAllocBytes capVal ≤ st.rem) ∧
      (rtC0Inv rt st ⋆ R) m ∧
      ∀ (st' : RtC0State) (m' : Mem 64),
        st'.PreservesMeta st → st'.rem ≤ st.rem →
        (rtC0Inv rt st' ⋆ R) m' →
        Q ((ArrayDemo.baPushSetGet capVal ⟨a⟩ ⟨b⟩ ⟨c⟩).toBitVec, ()) m'

/-- Specification of `ArrayDemo.baCowSetGet`: updates byte `0` of an exclusive (`rc = 1`) or
shared (`rc ≥ 2`) `ByteArray` holding `b0 :: b1 :: rest`, reads bytes `0` & `1`, frees the updated
copy, preserves `oldKeep` (the untouched original with decremented RC when shared), and returns
`v + b1.toBitVec`. -/
@[expose] def baCowSetGetSpec : Spec [i64, i64, i8] [i8] :=
  fun (rt, ba, v, ()) m Q _ =>
    ∃ (st : RtC0State) (baObj : LcnfObj) (b0 b1 : UInt8) (rest : List UInt8)
      (R : Mem 64 → Prop),
      baObj.addr = ba ∧ BaCanon baObj ∧ baObj.scalarData = b0 :: b1 :: rest ∧
      1 ≤ st.workCap ∧
      (baObj.rc ≠ 1#32 →
        st.hasFree (baAllocBytes baObj.cap) ∨ baAllocBytes baObj.cap ≤ st.rem) ∧
      (rtC0Inv rt st ⋆ lcnfObjMem baObj ⋆ R) m ∧
      let oldKeep :=
        if baObj.rc = 1#32 then emp
        else lcnfObjMem (baObj.withRc (decNonExclRc baObj.rc))
      ∀ (st' : RtC0State) (m' : Mem 64),
        st'.PreservesMeta st → st'.rem ≤ st.rem →
        (rtC0Inv rt st' ⋆ oldKeep ⋆ R) m' →
        Q (v + b1.toBitVec, ()) m'

/-- Specification table for the three user functions in `arrayDemoProgMod`. -/
@[expose] def arrayDemoSpecEntries : List SpecEntry :=
  [ SpecEntry.ofFn arrayDemoTfs.tf_0.toFn arrayPushSetGetSpec false
  , SpecEntry.ofFn arrayDemoTfs.tf_1.toFn baPushSetGetSpec false
  , SpecEntry.ofFn arrayDemoTfs.tf_2.toFn baCowSetGetSpec false ]

/-- Source-level specification environment for `arrayDemoProgMod`. -/
@[expose] def arrayDemoEnv : Env :=
  Env.ofTable arrayDemoSpecEntries

/-- Combined linked environment (`rtC0CoreEnv` on runtime, `arrayDemoEnv` on user functions). -/
@[expose] def arrayDemoLinkedEnv : Env :=
  linkRtC0Env arrayDemoEnv

theorem arrayDemoSpecEntries_nodup : (arrayDemoSpecEntries.map SpecEntry.name).Nodup := by
  decide

theorem arrayDemoEnv_arrayPushSetGet {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : arrayPushSetGetSpec xs m Q X) :
    arrayDemoEnv arrayDemoArrName [i64, i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (e := SpecEntry.ofFn arrayDemoTfs.tf_0.toFn arrayPushSetGetSpec false)
    (by simp [arrayDemoSpecEntries]) arrayDemoSpecEntries_nodup h

theorem arrayDemoEnv_baPushSetGet {xs : Tup Val [i64, i64, i8, i8, i8]} {m : Mem 64}
    {Q : Post [i8]} {X : XPost} (h : baPushSetGetSpec xs m Q X) :
    arrayDemoEnv arrayDemoBaName [i64, i64, i8, i8, i8] [i8] xs m Q X :=
  Env.ofTable_of_mem (e := SpecEntry.ofFn arrayDemoTfs.tf_1.toFn baPushSetGetSpec false)
    (by simp [arrayDemoSpecEntries]) arrayDemoSpecEntries_nodup h

theorem arrayDemoEnv_baCowSetGet {xs : Tup Val [i64, i64, i8]} {m : Mem 64}
    {Q : Post [i8]} {X : XPost} (h : baCowSetGetSpec xs m Q X) :
    arrayDemoEnv arrayDemoBaCowName [i64, i64, i8] [i8] xs m Q X :=
  Env.ofTable_of_mem (e := SpecEntry.ofFn arrayDemoTfs.tf_2.toFn baCowSetGetSpec false)
    (by simp [arrayDemoSpecEntries]) arrayDemoSpecEntries_nodup h

theorem arrayDemoEnv_arrayPushSetGet_noex {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost}
    (h : arrayDemoEnv arrayDemoTfs.tf_0.toFn.name arrayDemoTfs.tf_0.toFn.as
      arrayDemoTfs.tf_0.toFn.rs xs m Q X) :
    arrayDemoEnv arrayDemoTfs.tf_0.toFn.name arrayDemoTfs.tf_0.toFn.as
      arrayDemoTfs.tf_0.toFn.rs xs m Q X' :=
  arrayDemoEnv_arrayPushSetGet ((Env.ofTable_cons_self _ _ _ _ _ _).mp h)

theorem arrayDemoEnv_baPushSetGet_noex {xs : Tup Val [i64, i64, i8, i8, i8]} {m : Mem 64}
    {Q : Post [i8]} {X X' : XPost}
    (h : arrayDemoEnv arrayDemoTfs.tf_1.toFn.name arrayDemoTfs.tf_1.toFn.as
      arrayDemoTfs.tf_1.toFn.rs xs m Q X) :
    arrayDemoEnv arrayDemoTfs.tf_1.toFn.name arrayDemoTfs.tf_1.toFn.as
      arrayDemoTfs.tf_1.toFn.rs xs m Q X' :=
  let hne : arrayDemoTfs.tf_0.toFn.name ≠ arrayDemoTfs.tf_1.toFn.name := by decide
  arrayDemoEnv_baPushSetGet
    ((Env.ofTable_cons_self _ _ _ _ _ _).mp ((Env.ofTable_cons_ne hne _ _ _ _).mp h))

theorem arrayDemoEnv_baCowSetGet_noex {xs : Tup Val [i64, i64, i8]} {m : Mem 64}
    {Q : Post [i8]} {X X' : XPost}
    (h : arrayDemoEnv arrayDemoTfs.tf_2.toFn.name arrayDemoTfs.tf_2.toFn.as
      arrayDemoTfs.tf_2.toFn.rs xs m Q X) :
    arrayDemoEnv arrayDemoTfs.tf_2.toFn.name arrayDemoTfs.tf_2.toFn.as
      arrayDemoTfs.tf_2.toFn.rs xs m Q X' :=
  let h1 : arrayDemoTfs.tf_0.toFn.name ≠ arrayDemoTfs.tf_2.toFn.name := by decide
  let h2 : arrayDemoTfs.tf_1.toFn.name ≠ arrayDemoTfs.tf_2.toFn.name := by decide
  arrayDemoEnv_baCowSetGet
    ((Env.ofTable_cons_self _ _ _ _ _ _).mp
      ((Env.ofTable_cons_ne h2 _ _ _ _).mp ((Env.ofTable_cons_ne h1 _ _ _ _).mp h)))

/-! ## 4. Per-Function `Func.wp` Soundness Proofs (Composing R2 + R0 Specs) -/

theorem arrayDemo_arrayPushSetGet_wp :
    ∀ xs m Q X, arrayPushSetGetSpec xs m Q X →
      Func.wp arrayDemoLinkedEnv arrayDemoTfs.tf_0.toFn.body xs m Q X := by
  rintro ⟨rt, a, b, c, ⟨⟩⟩ m Q X ⟨aVal, bVal, cVal, st, R, ha, hb, hc, haLt, hcbLt, hwc, halloc,
    hm, hk⟩
  subst ha hb hc
  change wp arrayDemoLinkedEnv Q X
    (.call "lcnf_array_mk_empty" (as := [i64, i64]) (bs := [i64]) (.var rt, .imm 9#64, ())
      fun a0 =>
      .call "lcnf_array_push" (as := [i64, i64, i64]) (bs := [i64])
        (.var rt, .var a0.1, .var (boxNat aVal), ()) fun a1 =>
        .call "lcnf_array_push" (as := [i64, i64, i64]) (bs := [i64])
          (.var rt, .var a1.1, .var (boxNat bVal), ()) fun a2 =>
          .call "lcnf_array_set" (as := [i64, i64, i64, i64, i64]) (bs := [i64])
            (.var rt, .var a2.1, .imm 1#64, .var (boxNat cVal), .imm 0#64, ()) fun a3 =>
            .call "lcnf_array_get" (as := [i64, i64, i64, i64, i64]) (bs := [i64])
              (.var rt, .imm 1#64, .var a3.1, .imm 1#64, .imm 0#64, ()) fun v0 =>
              .call "lcnf_array_get" (as := [i64, i64, i64, i64, i64]) (bs := [i64])
                (.var rt, .imm 1#64, .var a3.1, .imm 3#64, .imm 0#64, ()) fun v1 =>
                arrDecObjExpr rt a3.1
                  (arrNatAddExpr rt v0.1 v1.1 fun sum =>
                    arrDecScalarExpr rt v1.1
                      (arrDecScalarExpr rt v0.1 (.ret (.var sum.1, ()))))) m
  have ha1 : (boxNat aVal &&& 1#64) = 1#64 := arr_boxNat_and_one haLt
  have hb1 : (boxNat bVal &&& 1#64) = 1#64 := arr_boxNat_and_one (by omega)
  have hc1 : (boxNat cVal &&& 1#64) = 1#64 := arr_boxNat_and_one (by omega)
  -- Step 1: `lcnf_array_mk_empty(rt, 9#64)` (`cap = 4`)
  let P0 : Post [i64] := fun (p, ()) m1 =>
    ∃ st1 : RtC0State, p ≠ 0#64 ∧ p.toNat % 8 = 0 ∧
      st1.PreservesMeta st ∧ st1.rem ≤ st.rem ∧
      ArrCanon (mkArrObj p 1#32 4 []) ∧
      (rtC0Inv rt st1 ⋆ lcnfObjMem (mkArrObj p 1#32 4 []) ⋆ R) m1
  refine arr_wp_call P0 (linkRtC0Env_of_r2 (by decide) (rtR2Env_lcnf_array_mk_empty ?_)) ?_
  · simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
    dsimp only [lcnfArrayMkEmptySpec]
    have hc4 : (if (9#64 &&& 1#64) ≠ 0#64 then (9#64 >>> 1).toNat else 0) = 4 := by decide
    rw [hc4, ite_eq_left (by decide)]
    exact ⟨st, R, halloc, hm, fun p st1 m1 hp0 hp8 hpr hrem hcan hm1 =>
      ⟨st1, hp0, hp8, hpr, hrem, hcan, hm1⟩⟩
  rintro ⟨p, ⟨⟩⟩ m1 ⟨st1, hp0, hp8, hpr1, hrem1, hcan0, hm1⟩
  -- Step 2: `lcnf_array_push(rt, p, boxNat aVal)` (in-place, `0 < 4`)
  let P1 : Post [i64] := fun (r, ()) m2 =>
    r = p ∧ ArrCanon (mkArrObj p 1#32 4 [boxNat aVal]) ∧
    (rtC0Inv rt st1 ⋆ lcnfObjMem (mkArrObj p 1#32 4 [boxNat aVal]) ⋆ R) m2
  refine arr_wp_call P1 (linkRtC0Env_of_r2 (by decide) (rtR2Env_lcnf_array_push ?_)) ?_
  · simp only [vals_nil, vals_cons, Arg.val_var]
    refine ⟨st1, mkArrObj p 1#32 4 [], [], R, rfl, hcan0, (fun _ h => nomatch h),
      by simp only [lcnfHeap]; exact sep_cast hm1 (by ac_rfl),
      fun h => absurd rfl h, ?_⟩
    rw [ite_eq_right (by dsimp [mkArrObj]; decide)]
    have hcap0 : arrEnsureCap 0 4 1#64 = 4 := by decide
    refine ⟨fun h => by simp [mkArrObj] at h,
      fun r st2 ch2 m2 _ _ _ _ hfp hcan1 hch1 _ hm2 => ?_⟩
    obtain ⟨rfl, rfl⟩ := hfp rfl (by dsimp [mkArrObj]; decide)
    have hchNil : ch2 = [] := hch1 rfl; subst hchNil
    simp only [mkArrObj, List.length_nil, List.nil_append, ↓reduceIte, lcnfHeap,
      hcap0] at hcan1 hm2
    exact ⟨rfl, hcan1, sep_cast hm2 (by ac_rfl)⟩
  rintro ⟨r1, ⟨⟩⟩ m2 ⟨hr1, hcan1, hm2⟩; subst r1
  -- Step 3: `lcnf_array_push(rt, p, boxNat bVal)` (in-place, `1 < 4`)
  let arr2 := mkArrObj p 1#32 4 [boxNat aVal, boxNat bVal]
  let P2 : Post [i64] := fun (r, ()) m3 =>
    r = p ∧ ArrCanon arr2 ∧ (rtC0Inv rt st1 ⋆ lcnfObjMem arr2 ⋆ R) m3
  refine arr_wp_call P2 (linkRtC0Env_of_r2 (by decide) (rtR2Env_lcnf_array_push ?_)) ?_
  · simp only [vals_nil, vals_cons, Arg.val_var]
    refine ⟨st1, mkArrObj p 1#32 4 [boxNat aVal], [], R, rfl, hcan1, (fun _ h => nomatch h),
      by simp only [lcnfHeap]; exact sep_cast hm2 (by ac_rfl),
      fun h => absurd rfl h, ?_⟩
    rw [ite_eq_right (by dsimp [mkArrObj]; decide)]
    have hcap1 : arrEnsureCap 1 4 1#64 = 4 := by decide
    refine ⟨fun h => by simp [mkArrObj] at h,
      fun r st3 ch3 m3 _ _ _ _ hfp hcan2 hch2 _ hm3 => ?_⟩
    obtain ⟨rfl, rfl⟩ := hfp rfl (by dsimp [mkArrObj]; decide)
    have hchNil : ch3 = [] := hch2 rfl; subst hchNil
    simp only [mkArrObj, List.length_cons, List.length_nil, List.cons_append, List.nil_append,
      ↓reduceIte, lcnfHeap, hcap1] at hcan2 hm3
    exact ⟨rfl, hcan2, sep_cast hm3 (by ac_rfl)⟩
  rintro ⟨r2, ⟨⟩⟩ m3 ⟨hr2, hcan2, hm3⟩; subst r2
  -- Step 4: `lcnf_array_set(rt, p, 1#64, boxNat cVal, 0#64)` (in-place overwrite slot 0)
  let arr3 := mkArrObj p 1#32 4 [boxNat cVal, boxNat bVal]
  have hcan3 : ArrCanon arr3 := mkArrObj_canon hp0 hp8 (by decide) (by simp) (by decide)
  have hp0bit : (p &&& 1#64) = 0#64 := arr_and1_zero_of_mod8 hp8
  let P3 : Post [i64] := fun (r, ()) m4 =>
    r = p ∧ ∃ st4 : RtC0State, st4.PreservesMeta st1 ∧ st4.rem ≤ st1.rem ∧
      (rtC0Inv rt st4 ⋆ lcnfObjMem arr3 ⋆ R) m4
  refine arr_wp_call P3 (linkRtC0Env_of_r2 (by decide) (rtR2Env_lcnf_array_set ?_)) ?_
  · simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
    have hpNotIn : arr2.addr ∉ arr2.fields := by
      simp only [arr2, mkArrObj, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => by rw [h, ha1] at hp0bit; exact absurd hp0bit (by decide),
             fun h => by rw [h, hb1] at hp0bit; exact absurd hp0bit (by decide)⟩
    have hcl2 : lcnfHeapClosed [arr2] := by
      intro o ho f hf hf0
      rw [List.mem_singleton] at ho; subst ho
      have hcf2 : arr2.childFields = [boxNat aVal, boxNat bVal] := by
        simp [arr2, mkArrObj, LcnfObj.childFields]
      rw [hcf2, List.mem_cons, List.mem_singleton] at hf
      rcases hf with rfl | rfl
      · rw [ha1] at hf0; exact absurd hf0 (by decide)
      · rw [hb1] at hf0; exact absurd hf0 (by decide)
    refine ⟨st1, [arr2], 0, by simp, R, rfl, hcan2, hpNotIn,
      fun o ho => by rw [List.mem_singleton] at ho; subst ho; exact hcan2.wf, hcl2,
      by simp only [lcnfHeap, sep_emp]; exact hm3, ?_⟩
    dsimp only; simp only [List.getElem_cons_zero]
    have hi0 : (if (0#64 : BitVec 64) ≠ 0#64 then (1#64 : BitVec 64).toNat
        else if (1#64 &&& 1#64) ≠ 0#64 then (1#64 >>> 1).toNat
        else arr2.fields.length) = 0 := by
      rw [ite_eq_right (by decide), ite_eq_left (by decide)]; decide
    have hlt0 : 0 < arr2.fields.length := by dsimp [arr2, mkArrObj]; decide
    simp only [hi0, hlt0, ↓reduceDIte]
    have holdEq : arr2.fields[0]'(by dsimp [arr2, mkArrObj]; decide) = boxNat aVal := rfl
    refine ⟨fun h => absurd rfl h,
      fun _ _ h0 => by rw [holdEq, ha1] at h0; exact absurd h0 (by decide),
      fun _ h0 _ => by rw [holdEq, ha1] at h0; exact absurd h0 (by decide), ?_⟩
    intro r st4 objs4 m4 _ _ hpr4 hrem4 hfp4 rObj mid1 mid2 hrObj hmid1 _ hmid2 hdec hm4
    have hrEq : r = p := hfp4 rfl; subst hrEq
    have hm1Eq : mid1 = [] := hmid1 rfl
    have hrObjEq : rObj = arr3 := by rw [hrObj]; rfl
    have hm2Eq : mid2 = [arr3] := by rw [hmid2, hm1Eq, hrObjEq]
    have hdecNil : objs4 = [arr3] := by
      rw [holdEq, hm2Eq] at hdec; unfold DecObjRel at hdec
      rw [ite_eq_left (Or.inr (by rw [ha1]; decide))] at hdec; exact hdec
    rw [hdecNil] at hm4; simp only [lcnfHeap, sep_emp] at hm4
    exact ⟨rfl, st4, hpr4, hrem4, hm4⟩
  rintro ⟨r3, ⟨⟩⟩ m4 ⟨hr3, st4, hpr4, hrem4, hm4⟩; subst r3
  -- Steps 5 & 6: `lcnf_array_get` at boxed indices `0` (`1#64`) and `1` (`3#64`)
  have hGetScalar : ∀ {idx : BitVec 64} {idxNat : Nat} {val : BitVec 64} {m0 : Mem 64}
      {k : Tup Val [i64] → Expr Val Cont [i64]},
      (idx &&& 1#64) ≠ 0#64 → (idx >>> 1).toNat = idxNat →
      (hi : idxNat < arr3.fields.length) → arr3.fields[idxNat]'hi = val →
      (val &&& 1#64) = 1#64 → (rtC0Inv rt st4 ⋆ lcnfObjMem arr3 ⋆ R) m0 →
      (∀ m', (rtC0Inv rt st4 ⋆ lcnfObjMem arr3 ⋆ R) m' →
        wp arrayDemoLinkedEnv Q X (k (val, ())) m') →
      wp arrayDemoLinkedEnv Q X
        (.call "lcnf_array_get" (as := [i64, i64, i64, i64, i64]) (bs := [i64])
          (.var rt, .imm 1#64, .var p, .imm idx, .imm 0#64, ()) k) m0 := by
    intro idx idxNat val m0 k hsc hshr hi hval hv1 hm0 hcont
    let PG : Post [i64] := fun (v, ()) m' =>
      v = val ∧ (rtC0Inv rt st4 ⋆ lcnfObjMem arr3 ⋆ R) m'
    refine arr_wp_call PG (linkRtC0Env_of_r2 (by decide) (rtR2Env_lcnf_array_get ?_))
      (fun ⟨v, ⟨⟩⟩ m' ⟨hv, hm'⟩ => hv ▸ hcont m' hm')
    simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
    refine ⟨arr3, [arr3], rtC0Inv rt st4 ⋆ R, List.mem_cons_self, rfl, hcan3,
      fun o ho => by rw [List.mem_singleton] at ho; subst ho; exact hcan3.wf,
      by simp only [lcnfHeap, sep_emp]; exact sep_cast hm0 (by ac_rfl), ?_⟩
    dsimp only; rw [ite_eq_right (fun h => absurd h.1 (by decide))]
    have hret : (if (0#64 &&& 2#64) ≠ 0#64 then
        if h : idx.toNat < arr3.fields.length then arr3.fields[idx.toNat] else 1#64
      else if (idx &&& 1#64) ≠ 0#64 then
        if h : (idx >>> 1).toNat < arr3.fields.length then arr3.fields[(idx >>> 1).toNat] else 1#64
      else 1#64) = val := by
      rw [ite_eq_right (by decide), ite_eq_left hsc]
      simp only [hshr, hi, ↓reduceDIte, hval]
    refine ⟨fun h => by rw [hret, hv1] at h; exact absurd h.2.2 (by decide), fun m' _ hm' => ?_⟩
    rw [hret] at hm' ⊢
    rw [ite_eq_left (Or.inr (Or.inr (by rw [hv1]; decide)))] at hm'
    simp only [lcnfHeap, sep_emp] at hm'
    exact ⟨rfl, sep_cast hm' (by ac_rfl)⟩
  refine hGetScalar (idx := 1#64) (idxNat := 0) (by decide) (by decide)
    (by dsimp [arr3, mkArrObj]; decide) rfl hc1 hm4 ?_
  intro m5 hm5
  refine hGetScalar (idx := 3#64) (idxNat := 1) (by decide) (by decide)
    (by dsimp [arr3, mkArrObj]; decide) rfl hb1 hm5 ?_
  intro m6 hm6
  -- Step 7: `dec_ref(arr3)` → `lcnf_dec_ref_cold(rt, p)` frees `arr3`
  have hpr14 : st4.PreservesMeta st := hpr1.trans hpr4
  have hwc4 : 1 ≤ st4.workCap := by
    rwa [RtC0State.workCap_eq_of_preservesMeta hpr14]
  have hldRc : loadVal m6 i32 arr3.addr = some 1#32 :=
    lcnfObjMem_arr_load_rc1 (R := rtC0Inv rt st4 ⋆ R) (sep_cast hm6 (by ac_rfl))
  refine wp_arrDecObjExpr_free_singleton (obj := arr3)
    (fun _ _ h => linkRtC0Env_of_rt (by decide) (rtC0CoreEnv_lcnf_dec_ref_cold h))
    hp8 rfl hcan3.wf
    (fun f hf => by
      have hcf3 : arr3.childFields = [boxNat cVal, boxNat bVal] := by
        simp [arr3, mkArrObj, LcnfObj.childFields]
      rw [hcf3, List.mem_cons, List.mem_singleton] at hf
      rcases hf with rfl | rfl; exact hc1; exact hb1)
    hwc4 hldRc hm6 ?_
  intro st5 m7 hpr5 hrem5 hm7
  -- Step 8: fast tagged `Nat.add` (`cVal + bVal`), scalar decs, return
  refine wp_arrNatAddExpr_fast hcbLt ?_
  refine wp_arrDecScalarExpr hb1 ?_
  refine wp_arrDecScalarExpr hc1 ?_
  rw [wp_ret, ← arrayPushSetGet_eq aVal bVal cVal]
  exact hk st5 m7 (hpr14.trans hpr5) (by omega) hm7

theorem arrayDemo_baPushSetGet_wp :
    ∀ xs m Q X, baPushSetGetSpec xs m Q X →
      Func.wp arrayDemoLinkedEnv arrayDemoTfs.tf_1.toFn.body xs m Q X := by
  rintro ⟨rt, cap, a, b, c, ⟨⟩⟩ m Q X ⟨capVal, st, R, hcap, hcap2, hcapMax, hwc, halloc, hm, hk⟩
  subst hcap
  change wp arrayDemoLinkedEnv Q X
    (.call "lcnf_ba_mk_empty" (as := [i64, i64]) (bs := [i64]) (.var rt, .var (boxNat capVal), ())
      fun ba0 =>
      .let_ (_root_.LeanQbe.T.op1 (OpCode.zext 8 64) (.var a)) fun a64 =>
        .call "lcnf_ba_push" (as := [i64, i64, i64]) (bs := [i64])
          (.var rt, .var ba0.1, .var a64.1, ()) fun ba1 =>
          .let_ (_root_.LeanQbe.T.op1 (OpCode.zext 8 64) (.var b)) fun b64 =>
            .call "lcnf_ba_push" (as := [i64, i64, i64]) (bs := [i64])
              (.var rt, .var ba1.1, .var b64.1, ()) fun ba2 =>
              .let_ (_root_.LeanQbe.T.op1 (OpCode.zext 8 64) (.var c)) fun c64 =>
                .call "lcnf_ba_set" (as := [i64, i64, i64, i64, i64]) (bs := [i64])
                  (.var rt, .var ba2.1, .imm 1#64, .var c64.1, .imm 0#64, ()) fun ba3 =>
                  .call "lcnf_ba_get" (as := [i64, i64, i64, i64]) (bs := [i64])
                    (.var rt, .var ba3.1, .imm 1#64, .imm 0#64, ()) fun g0 =>
                    .let_ (_root_.LeanQbe.T.op1 (OpCode.trunc 64 8) (.var g0.1)) fun r0 =>
                      .call "lcnf_ba_get" (as := [i64, i64, i64, i64]) (bs := [i64])
                        (.var rt, .var ba3.1, .imm 3#64, .imm 0#64, ()) fun g1 =>
                        .let_ (_root_.LeanQbe.T.op1 (OpCode.trunc 64 8) (.var g1.1)) fun r1 =>
                          arrDecObjExpr rt ba3.1
                            (.let_ (_root_.LeanQbe.T.op2 (OpCode.add i8) (.var r0.1) (.var r1.1))
                              fun sum => .ret (.var sum.1, ()))) m
  have hcapLt63 : capVal < 2 ^ 63 := by unfold baMaxCap at hcapMax; omega
  have hcapSc : (boxNat capVal &&& 1#64) ≠ 0#64 := by
    rw [arr_boxNat_and_one hcapLt63]; decide
  have hcapUnbox : (if (boxNat capVal &&& 1#64) ≠ 0#64 then (boxNat capVal >>> 1).toNat else 0) =
      capVal := by
    rw [ite_eq_left hcapSc, arr_boxNat_shr1 hcapLt63]
  -- Step 1: `lcnf_ba_mk_empty(rt, boxNat capVal)`
  let P0 : Post [i64] := fun (p, ()) m1 =>
    ∃ st1 : RtC0State, p ≠ 0#64 ∧ p.toNat % 8 = 0 ∧
      st1.PreservesMeta st ∧ st1.rem ≤ st.rem ∧
      BaCanon (mkBaObj p 1#32 capVal []) ∧
      (rtC0Inv rt st1 ⋆ lcnfObjMem (mkBaObj p 1#32 capVal []) ⋆ R) m1
  refine arr_wp_call P0 (linkRtC0Env_of_r2 (by decide) (rtR2Env_lcnf_ba_mk_empty ?_)) ?_
  · simp only [vals_nil, vals_cons, Arg.val_var]
    dsimp only [lcnfBaMkEmptySpec]
    rw [hcapUnbox, ite_eq_left hcapMax]
    exact ⟨st, R, halloc, hm, fun p st1 m1 hp0 hp8 hpr hrem hcan hm1 =>
      ⟨st1, hp0, hp8, hpr, hrem, hcan, hm1⟩⟩
  rintro ⟨p, ⟨⟩⟩ m1 ⟨st1, hp0, hp8, hpr1, hrem1, hcan0, hm1⟩; c0_let_simp
  -- Step 2: `lcnf_ba_push(rt, p, zext a)` (in-place, `0 < capVal`)
  let P1 : Post [i64] := fun (r, ()) m2 =>
    r = p ∧ BaCanon (mkBaObj p 1#32 capVal [⟨a⟩]) ∧
    (rtC0Inv rt st1 ⋆ lcnfObjMem (mkBaObj p 1#32 capVal [⟨a⟩]) ⋆ R) m2
  refine arr_wp_call P1 (linkRtC0Env_of_r2 (by decide) (rtR2Env_lcnf_ba_push ?_)) ?_
  · simp only [vals_nil, vals_cons, Arg.val_var]
    refine ⟨st1, mkBaObj p 1#32 capVal [], R, rfl, hcan0, hm1, ?_⟩
    rw [ite_eq_right (by dsimp [mkBaObj]; omega)]
    have hcap0 : baEnsureCap 0 capVal 1#64 = capVal := by
      unfold baEnsureCap; rw [ite_eq_right (by decide), ite_eq_left (by omega)]
    refine ⟨fun h => by
        dsimp [mkBaObj] at h; rcases h with h1 | h2; exact absurd rfl h1; omega,
      fun r st2 m2 _ _ _ _ hfp hcan1 hm2 => ?_⟩
    obtain ⟨rfl, rfl⟩ := hfp rfl (by dsimp [mkBaObj]; omega)
    simp only [mkBaObj, List.length_nil, List.nil_append, ↓reduceIte, hcap0,
      uint8_ofNat_setWidth64] at hcan1 hm2
    exact ⟨rfl, hcan1, sep_cast hm2 (by ac_rfl)⟩
  rintro ⟨r1, ⟨⟩⟩ m2 ⟨hr1, hcan1, hm2⟩; subst r1; c0_let_simp
  -- Step 3: `lcnf_ba_push(rt, p, zext b)` (in-place, `1 < capVal`)
  let P2 : Post [i64] := fun (r, ()) m3 =>
    r = p ∧ BaCanon (mkBaObj p 1#32 capVal [⟨a⟩, ⟨b⟩]) ∧
    (rtC0Inv rt st1 ⋆ lcnfObjMem (mkBaObj p 1#32 capVal [⟨a⟩, ⟨b⟩]) ⋆ R) m3
  refine arr_wp_call P2 (linkRtC0Env_of_r2 (by decide) (rtR2Env_lcnf_ba_push ?_)) ?_
  · simp only [vals_nil, vals_cons, Arg.val_var]
    refine ⟨st1, mkBaObj p 1#32 capVal [⟨a⟩], R, rfl, hcan1, hm2, ?_⟩
    rw [ite_eq_right (by dsimp [mkBaObj]; omega)]
    have hcap1 : baEnsureCap 1 capVal 1#64 = capVal := by
      unfold baEnsureCap; rw [ite_eq_right (by decide), ite_eq_left (by omega)]
    refine ⟨fun h => by
        dsimp [mkBaObj] at h; rcases h with h1 | h2; exact absurd rfl h1; omega,
      fun r st3 m3 _ _ _ _ hfp hcan2 hm3 => ?_⟩
    obtain ⟨rfl, rfl⟩ := hfp rfl (by dsimp [mkBaObj]; omega)
    simp only [mkBaObj, List.length_cons, List.length_nil, List.cons_append, List.nil_append,
      ↓reduceIte, hcap1, uint8_ofNat_setWidth64] at hcan2 hm3
    exact ⟨rfl, hcan2, sep_cast hm3 (by ac_rfl)⟩
  rintro ⟨r2, ⟨⟩⟩ m3 ⟨hr2, hcan2, hm3⟩; subst r2; c0_let_simp
  -- Step 4: `lcnf_ba_set(rt, p, 1#64, zext c, 0#64)` (in-place overwrite byte 0)
  let ba3 := mkBaObj p 1#32 capVal [⟨c⟩, ⟨b⟩]
  let P3 : Post [i64] := fun (r, ()) m4 =>
    r = p ∧ BaCanon ba3 ∧ (rtC0Inv rt st1 ⋆ lcnfObjMem ba3 ⋆ R) m4
  refine arr_wp_call P3 (linkRtC0Env_of_r2 (by decide) (rtR2Env_lcnf_ba_set ?_)) ?_
  · simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
    refine ⟨st1, mkBaObj p 1#32 capVal [⟨a⟩, ⟨b⟩], R, rfl, hcan2, hm3, ?_⟩
    have hi0 : (if (0#64 : BitVec 64) ≠ 0#64 then (1#64 : BitVec 64).toNat
        else if (1#64 &&& 1#64) ≠ 0#64 then (1#64 >>> 1).toNat
        else (mkBaObj p 1#32 capVal [⟨a⟩, ⟨b⟩]).arrSize) = 0 := by
      rw [ite_eq_right (by decide), ite_eq_left (by decide)]; decide
    rw [hi0, ite_eq_right (by dsimp [mkBaObj]; omega)]
    refine ⟨fun h => absurd rfl h, fun r st4 m4 _ _ _ _ hfp hcan3 hm4 => ?_⟩
    obtain ⟨rfl, rfl⟩ := hfp rfl
    simp only [mkBaObj, List.set_cons_zero, ↓reduceIte, uint8_ofNat_setWidth64] at hcan3 hm4
    exact ⟨rfl, hcan3, sep_cast hm4 (by ac_rfl)⟩
  rintro ⟨r3, ⟨⟩⟩ m4 ⟨hr3, hcan3, hm4⟩; subst r3
  -- Step 5: `lcnf_ba_get(rt, p, 1#64, 0#64)` → `c`
  let P4 : Post [i64] := fun (v, ()) m5 => v = BitVec.ofNat 64 (⟨c⟩ : UInt8).toNat ∧ m5 = m4
  refine arr_wp_call P4 (linkRtC0Env_of_r2 (by decide) (rtR2Env_lcnf_ba_get ?_)) ?_
  · simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
    refine ⟨ba3, rtC0Inv rt st1 ⋆ R, rfl, hcan3, sep_cast hm4 (by ac_rfl), ?_⟩
    exact ⟨by unfold baGetVal; rfl, rfl⟩
  rintro ⟨g0, ⟨⟩⟩ m5 ⟨rfl, hm5⟩; subst m5; c0_let_simp
  -- Step 6: `lcnf_ba_get(rt, p, 3#64, 0#64)` → `b`
  let P5 : Post [i64] := fun (v, ()) m6 => v = BitVec.ofNat 64 (⟨b⟩ : UInt8).toNat ∧ m6 = m4
  refine arr_wp_call P5 (linkRtC0Env_of_r2 (by decide) (rtR2Env_lcnf_ba_get ?_)) ?_
  · simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
    refine ⟨ba3, rtC0Inv rt st1 ⋆ R, rfl, hcan3, sep_cast hm4 (by ac_rfl), ?_⟩
    exact ⟨by unfold baGetVal; rfl, rfl⟩
  rintro ⟨g1, ⟨⟩⟩ m6 ⟨rfl, hm6⟩; subst m6; c0_let_simp
  -- Step 7: `dec_ref(ba3)` → `lcnf_dec_ref_cold(rt, p)` frees `ba3`
  have hwc1 : 1 ≤ st1.workCap := by rwa [RtC0State.workCap_eq_of_preservesMeta hpr1]
  have hldRc : loadVal m4 i32 ba3.addr = some 1#32 :=
    lcnfObjMem_ba_load_rc1 (R := rtC0Inv rt st1 ⋆ R) (sep_cast hm4 (by ac_rfl))
  refine wp_arrDecObjExpr_free_singleton (obj := ba3)
    (fun _ _ h => linkRtC0Env_of_rt (by decide) (rtC0CoreEnv_lcnf_dec_ref_cold h))
    hp8 rfl hcan3.wf
    (fun f hf => by simp [ba3, mkBaObj, LcnfObj.childFields, sarrayTag, closureTag, arrayTag] at hf)
    hwc1 hldRc hm4 ?_
  intro st2 m7 hpr2 hrem2 hm7
  c0_let_simp
  have hsum : (ArrayDemo.baPushSetGet capVal ⟨a⟩ ⟨b⟩ ⟨c⟩).toBitVec = c + b := by
    rw [baPushSetGet_eq]; rfl
  rw [setWidth8_ofNat64 ⟨c⟩, setWidth8_ofNat64 ⟨b⟩]
  change Q (c + b, ()) m7
  rw [← hsum]
  exact hk st2 m7 (hpr1.trans hpr2) (by omega) hm7

theorem arrayDemo_baCowSetGet_wp :
    ∀ xs m Q X, baCowSetGetSpec xs m Q X →
      Func.wp arrayDemoLinkedEnv arrayDemoTfs.tf_2.toFn.body xs m Q X := by
  rintro ⟨rt, ba, v, ⟨⟩⟩ m Q X
    ⟨st, baObj, b0, b1, rest, R, hbaAddr, hbaCan, hbaData, hwc, hfree, hm, hk⟩
  change wp arrayDemoLinkedEnv Q X
    (.let_ (_root_.LeanQbe.T.op1 (OpCode.zext 8 64) (.var v)) fun v64 =>
      .call "lcnf_ba_set" (as := [i64, i64, i64, i64, i64]) (bs := [i64])
        (.var rt, .var ba, .imm 1#64, .var v64.1, .imm 0#64, ()) fun ba1 =>
        .call "lcnf_ba_get" (as := [i64, i64, i64, i64]) (bs := [i64])
          (.var rt, .var ba1.1, .imm 1#64, .imm 0#64, ()) fun g0 =>
          .let_ (_root_.LeanQbe.T.op1 (OpCode.trunc 64 8) (.var g0.1)) fun r0 =>
            .call "lcnf_ba_get" (as := [i64, i64, i64, i64]) (bs := [i64])
              (.var rt, .var ba1.1, .imm 3#64, .imm 0#64, ()) fun g1 =>
              .let_ (_root_.LeanQbe.T.op1 (OpCode.trunc 64 8) (.var g1.1)) fun r1 =>
                arrDecObjExpr rt ba1.1
                  (.let_ (_root_.LeanQbe.T.op2 (OpCode.add i8) (.var r0.1) (.var r1.1)) fun sum =>
                    .ret (.var sum.1, ()))) m
  c0_let_simp
  let oldKeep : Mem 64 → Prop :=
    if baObj.rc = 1#32 then emp
    else lcnfObjMem (baObj.withRc (decNonExclRc baObj.rc))
  -- Step 1: `lcnf_ba_set(rt, ba, 1#64, zext v, 0#64)` (exclusive in-place OR shared COW copy)
  let P1 : Post [i64] := fun (r, ()) m1 =>
    ∃ st1 : RtC0State, r ≠ 0#64 ∧ r.toNat % 8 = 0 ∧
      st1.PreservesMeta st ∧ st1.rem ≤ st.rem ∧
      let rObj := mkBaObj r 1#32 baObj.cap (⟨v⟩ :: b1 :: rest)
      BaCanon rObj ∧ (rtC0Inv rt st1 ⋆ lcnfObjMem rObj ⋆ oldKeep ⋆ R) m1
  refine arr_wp_call P1 (linkRtC0Env_of_r2 (by decide) (rtR2Env_lcnf_ba_set ?_)) ?_
  · simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
    refine ⟨st, baObj, R, hbaAddr, hbaCan, hm, ?_⟩
    have hi0 : (if (0#64 : BitVec 64) ≠ 0#64 then (1#64 : BitVec 64).toNat
        else if (1#64 &&& 1#64) ≠ 0#64 then (1#64 >>> 1).toNat
        else baObj.arrSize) = 0 := by
      rw [ite_eq_right (by decide), ite_eq_left (by decide)]; decide
    have hsz2 : baObj.arrSize ≥ 2 := by
      have hlen := hbaCan.2.2.2.2.2.2.1; rw [hbaData] at hlen; simp at hlen; omega
    rw [hi0, ite_eq_right (by omega)]
    refine ⟨hfree, fun r st1 m1 hr0 hr8 hpr1 hrem1 _ hcan1 hm1 => ?_⟩
    rw [hbaData, List.set_cons_zero, uint8_ofNat_setWidth64] at hcan1 hm1
    exact ⟨st1, hr0, hr8, hpr1, hrem1, hcan1, hm1⟩
  rintro ⟨r, ⟨⟩⟩ m1 ⟨st1, hr0, hr8, hpr1, hrem1, hrCan, hm1⟩
  let rObj := mkBaObj r 1#32 baObj.cap (⟨v⟩ :: b1 :: rest)
  -- Step 2: `lcnf_ba_get(rt, r, 1#64, 0#64)` → `v`
  let P2 : Post [i64] := fun (w, ()) m2 => w = BitVec.ofNat 64 (⟨v⟩ : UInt8).toNat ∧ m2 = m1
  refine arr_wp_call P2 (linkRtC0Env_of_r2 (by decide) (rtR2Env_lcnf_ba_get ?_)) ?_
  · simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
    refine ⟨rObj, rtC0Inv rt st1 ⋆ oldKeep ⋆ R, rfl, hrCan, sep_cast hm1 (by ac_rfl), ?_⟩
    exact ⟨by unfold baGetVal; rfl, rfl⟩
  rintro ⟨g0, ⟨⟩⟩ m2 ⟨rfl, hm2⟩; subst m2; c0_let_simp
  -- Step 3: `lcnf_ba_get(rt, r, 3#64, 0#64)` → `b1`
  let P3 : Post [i64] := fun (w, ()) m3 => w = BitVec.ofNat 64 b1.toNat ∧ m3 = m1
  refine arr_wp_call P3 (linkRtC0Env_of_r2 (by decide) (rtR2Env_lcnf_ba_get ?_)) ?_
  · simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
    refine ⟨rObj, rtC0Inv rt st1 ⋆ oldKeep ⋆ R, rfl, hrCan, sep_cast hm1 (by ac_rfl), ?_⟩
    exact ⟨by unfold baGetVal; rfl, rfl⟩
  rintro ⟨g1, ⟨⟩⟩ m3 ⟨rfl, hm3⟩; subst m3; c0_let_simp
  -- Step 4: `dec_ref(rObj)` frees `rObj` while keeping `oldKeep ⋆ R` intact
  have hwc1 : 1 ≤ st1.workCap := by rwa [RtC0State.workCap_eq_of_preservesMeta hpr1]
  have hldRc : loadVal m1 i32 rObj.addr = some 1#32 :=
    lcnfObjMem_ba_load_rc1 (R := rtC0Inv rt st1 ⋆ oldKeep ⋆ R) (sep_cast hm1 (by ac_rfl))
  refine wp_arrDecObjExpr_free_singleton (obj := rObj) (R := oldKeep ⋆ R)
    (fun _ _ h => linkRtC0Env_of_rt (by decide) (rtC0CoreEnv_lcnf_dec_ref_cold h))
    hr8 rfl hrCan.wf
    (fun f hf => by
      simp [rObj, mkBaObj, LcnfObj.childFields, sarrayTag, closureTag, arrayTag] at hf)
    hwc1 hldRc (sep_cast hm1 (by ac_rfl)) ?_
  intro st2 m4 hpr2 hrem2 hm4
  c0_let_simp
  rw [setWidth8_ofNat64 ⟨v⟩, setWidth8_ofNat64 b1]
  dsimp only [oldKeep] at hm4
  exact hk st2 m4 (hpr1.trans hpr2) (by omega) (sep_cast hm4 (by ac_rfl))

/-! ## 5. Whole-Module Soundness & Compositional `ModuleOk` -/

theorem arrayDemoLinkedMod_checkAcyclic : arrayDemoLinkedMod.checkAcyclic = true := by decide

theorem arrayDemoProgMod_fns_eq :
    (lcnfProgMod arrayDemoTfs).fns =
      [arrayDemoTfs.tf_0.toFn, arrayDemoTfs.tf_1.toFn, arrayDemoTfs.tf_2.toFn] := rfl

theorem arrayDemoProgMod_wp :
    ∀ fn ∈ (lcnfProgMod arrayDemoTfs).fns,
      ∀ xs m Q X, arrayDemoEnv fn.name fn.as fn.rs xs m Q X →
        Func.wp arrayDemoLinkedEnv fn.body xs m Q X := by
  intro fn hfn xs m Q X hpre
  rw [arrayDemoProgMod_fns_eq] at hfn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl
  · exact arrayDemo_arrayPushSetGet_wp xs m Q X ((Env.ofTable_cons_self _ _ _ _ _ _).mp hpre)
  · have h1 : arrayDemoTfs.tf_0.toFn.name ≠ arrayDemoTfs.tf_1.toFn.name := by decide
    have hpre' := (Env.ofTable_cons_ne h1 _ _ _ _).mp hpre
    exact arrayDemo_baPushSetGet_wp xs m Q X ((Env.ofTable_cons_self _ _ _ _ _ _).mp hpre')
  · have h1 : arrayDemoTfs.tf_0.toFn.name ≠ arrayDemoTfs.tf_2.toFn.name := by decide
    have h2 : arrayDemoTfs.tf_1.toFn.name ≠ arrayDemoTfs.tf_2.toFn.name := by decide
    have hpre' := (Env.ofTable_cons_ne h2 _ _ _ _).mp ((Env.ofTable_cons_ne h1 _ _ _ _).mp hpre)
    exact arrayDemo_baCowSetGet_wp xs m Q X ((Env.ofTable_cons_self _ _ _ _ _ _).mp hpre')

/-- Whole-module `ModuleOk` composition combining `rtC0CoreMod` (`80` fns) and `arrayDemoProgMod`
(`3` fns) under `arrayDemoLinkedEnv` via `linkLcnfWithRtC0_moduleOk`. -/
theorem arrayDemoLinkedMod_moduleOk :
    ModuleOk arrayDemoLinkedEnv arrayDemoLinkedMod :=
  linkLcnfWithRtC0_moduleOk arrayDemoEnv arrayDemoLinkedMod_checkAcyclic arrayDemoProgMod_wp

/-! ## 6. Concrete `0x1000#64` Slab & Shared-`ByteArray` COW Fixtures (`0` `import all`) -/

/-- Base address of the concrete R0 slab (`0x1000#64`, matching `TargetInit` payload base). -/
@[expose] def arrayRtBase : BitVec 64 := 0x1000#64

/-- Work-stack capacity (`8` words) and bump-arena headroom (`256` bytes) for the concrete slab. -/
@[expose] def arrayRtWorkCap : Nat := 8
@[expose] def arrayRtRem : Nat := 256

/-- Initialized concrete `RtC0State` rooted at `0x1000#64`. -/
@[expose] def arrayRtState : RtC0State :=
  initRtC0State arrayRtBase arrayRtWorkCap arrayRtRem (by decide) (by decide)

/-- Header words of an `LcnfC0Rt` struct in exact field order (`17 × i64 = 136` bytes). -/
@[expose] def arrayRtHdrWords (h : LcnfC0Rt) : List (BitVec 64) :=
  [ h.s_large_free, h.s_ba_empty, h.s_cur, h.s_end, h.s_work, h.s_work_cap, h.s_chunks, h.s_nchunks,
    h.s_chunks_cap, h.s_st_allocs, h.s_st_frees, h.s_st_live, h.s_st_peak_live, h.s_st_persistent,
    h.s_st_reused, h.s_st_cold_decs, h.s_st_bytes ]

/-- Concrete `33,992`-byte image of `rtC0Inv arrayRtBase arrayRtState` at `0x1000#64`. -/
@[expose] def arrayRtBytes : List UInt8 :=
  bytes64 arrayRtState.extraArgs ++ bytes64 arrayRtState.globals ++
  bytes64 arrayRtState.freeList ++ bytes64 (arrayRtHdrWords arrayRtState.hdr) ++
  bytes64 arrayRtState.workBuf ++ List.replicate arrayRtRem 0

/-- Address & canonical `LcnfObj`s for the shared (`rc = 2`) and post-COW (`rc = 1`) `ByteArray`
`[10, 20]` (`cap = 4`, `32` bytes) packed immediately after `arrayRtBytes`. -/
@[expose] def sharedBaAddr : BitVec 64 := arrayRtBase + 33992#64
@[expose] def sharedBaObj : LcnfObj := mkBaObj sharedBaAddr 2#32 4 [10, 20]
@[expose] def sharedBaObjAfter : LcnfObj := mkBaObj sharedBaAddr 1#32 4 [10, 20]

/-- Concrete `32`-byte image of `sharedBaObj` and `34,024`-byte packed slab `arrayCowBytes`. -/
@[expose] def sharedBaBytes : List UInt8 :=
  (bytes64 [sharedBaObj.header, 2#64, 4#64] ++ [10, 20]) ++ List.replicate 6 0
@[expose] def arrayCowBytes : List UInt8 := arrayRtBytes ++ sharedBaBytes

private theorem arr_sep_append {P Q : Mem 64 → Prop} {a : BitVec 64} {bs1 bs2 : List UInt8}
    {n1 n2 : Nat} (h1 : bs1.length = n1) (h2 : bs2.length = n2) (hfit : n1 + n2 ≤ 2 ^ 64)
    (hp : P (bs1.At a)) (hq : Q (bs2.At (a + BitVec.ofNat 64 n1))) :
    (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have hs : (Eq (bs1.At a) ⋆ Eq (bs2.At (a + BitVec.ofNat 64 bs1.length))) ((bs1 ++ bs2).At a) :=
    (congrFun (Mem.At_append_sep bs1 bs2 a (by omega)) ((bs1 ++ bs2).At a)).mp rfl
  exact sep_mono2 (fun _ h => h ▸ hp) (fun _ h => h ▸ (h1 ▸ hq)) _ hs

private theorem arr_sep_join {P Q : Mem 64 → Prop} {a : BitVec 64} {bs1 bs2 : List UInt8}
    {n1 n2 : Nat} (h1 : bs1.length = n1) (h2 : bs2.length = n2) (hfit : n1 + n2 ≤ 2 ^ 64)
    (hp : P (bs1.At a)) (hq : Q (bs2.At (a + BitVec.ofNat 64 n1))) :
    (bs1 ++ bs2).length = n1 + n2 ∧ (P ⋆ Q) ((bs1 ++ bs2).At a) :=
  ⟨by simp [h1, h2], arr_sep_append h1 h2 hfit hp hq⟩

private theorem array64_rtHdr_to_At (rt : BitVec 64) (h : LcnfC0Rt) {m : Mem 64}
    (hm : array64 (rt + 33536#64) (arrayRtHdrWords h) m) : LcnfC0Rt.At rt h m := by
  unfold arrayRtHdrWords at hm
  simp only [array64, cell64_eq_cell, sep_emp, BitVec.add_assoc] at hm
  unfold LcnfC0Rt.At
  exact sep_cast hm (by ac_rfl)

/-- Proof that `arrayRtBytes` has length `33,992` and satisfies `rtC0Inv` at `0x1000#64`. -/
theorem arrayRtBytes_ok :
    arrayRtBytes.length = 33992 ∧
    rtC0Inv arrayRtBase arrayRtState (arrayRtBytes.At arrayRtBase) := by
  let b0 := bytes64 arrayRtState.extraArgs
  let b1 := bytes64 arrayRtState.globals
  let b2 := bytes64 arrayRtState.freeList
  let b3 := bytes64 (arrayRtHdrWords arrayRtState.hdr)
  let b4 := bytes64 arrayRtState.workBuf
  let b5 := List.replicate arrayRtRem (0 : UInt8)
  have hl0 : b0.length = 256 := by rw [bytes64_length, arrayRtState.extraLen]; decide
  have hl1 : b1.length = 32768 := by rw [bytes64_length, arrayRtState.globalsLen]; decide
  have hl2 : b2.length = 512 := by rw [bytes64_length, arrayRtState.freeListLen]; decide
  have hl3 : b3.length = 136 := by rw [bytes64_length]; simp [arrayRtHdrWords]
  have hwl : arrayRtState.workBuf.length = 8 := by rw [arrayRtState.workLen]; decide
  have hl4 : b4.length = 64 := by rw [bytes64_length, hwl]
  have hl5 : b5.length = 256 := List.length_replicate
  have s1 := arr_sep_join (a := arrayRtBase) hl0 hl1 (by decide)
    (array64_bytes arrayRtBase _ (by rw [arrayRtState.extraLen]; decide))
    (array64_bytes _ _ (by rw [arrayRtState.globalsLen]; decide))
  have s2 := arr_sep_join (a := arrayRtBase) s1.1 hl2 (by decide) s1.2
    (array64_bytes _ _ (by rw [arrayRtState.freeListLen]; decide))
  have s3 := arr_sep_join (a := arrayRtBase) s2.1 hl3 (by decide) s2.2
    (array64_rtHdr_to_At arrayRtBase _ (array64_bytes _ _ (by decide)))
  have s4 := arr_sep_join (a := arrayRtBase) s3.1 hl4 (by decide) s3.2
    (array64_bytes _ _ (by rw [hwl]; decide))
  have s5 := arr_sep_join (a := arrayRtBase) (Q := region (arrayRtBase + 33736#64) arrayRtRem)
    s4.1 hl5 (by decide) s4.2 ⟨b5, hl5, rfl⟩
  exact ⟨s5.1,
    rtC0Inv_init_satisfiable arrayRtBase arrayRtWorkCap arrayRtRem (by decide) (by decide) s5.2⟩

theorem sharedBaObj_canon : BaCanon sharedBaObj :=
  mkBaObj_canon (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem sharedBaBytes_ok :
    sharedBaBytes.length = 32 ∧ lcnfObjMem sharedBaObj (sharedBaBytes.At sharedBaAddr) := by
  have hHdrArr : array64 sharedBaAddr [sharedBaObj.header, 2#64, 4#64]
      ((bytes64 [sharedBaObj.header, 2#64, 4#64]).At sharedBaAddr) :=
    array64_bytes sharedBaAddr _ (by decide)
  have hHdrCells : (cell64 sharedBaAddr sharedBaObj.header ⋆
      cell64 (sharedBaAddr + 8#64) 2#64 ⋆ cell64 (sharedBaAddr + 16#64) 4#64)
      ((bytes64 [sharedBaObj.header, 2#64, 4#64]).At sharedBaAddr) := by
    simp only [array64_cons, array64_nil, sep_emp] at hHdrArr
    have h8 : sharedBaAddr + 8 = sharedBaAddr + 8#64 := by bv_omega
    have h16 : sharedBaAddr + 8 + 8 = sharedBaAddr + 16#64 := by bv_omega
    rw [h16, h8] at hHdrArr
    exact sep_cast hHdrArr (by ac_rfl)
  have hLenHdr : (bytes64 [sharedBaObj.header, 2#64, 4#64]).length = 24 := by
    rw [bytes64_length]; decide
  have hHdrPay := arr_sep_join (Q := bytes (sharedBaAddr + 24#64) [10, 20])
    hLenHdr (by decide : ([10, 20] : List UInt8).length = 2) (by decide) hHdrCells rfl
  have hPadLen : (List.replicate 6 (0 : UInt8)).length = 6 := List.length_replicate
  have hAll := arr_sep_join (Q := region (sharedBaAddr + 26#64) 6)
    hHdrPay.1 hPadLen (by decide) hHdrPay.2 ⟨List.replicate 6 0, hPadLen, rfl⟩
  refine ⟨hAll.1, ?_⟩
  unfold lcnfObjMem
  have ht : sharedBaObj.tag = sarrayTag := rfl
  simp only [ht, ↓reduceIte]
  have htb : sharedBaObj.totalBytes - (24 + sharedBaObj.scalarData.length) = 6 := by decide
  have h26 : sharedBaObj.addr + BitVec.ofNat 64 (24 + sharedBaObj.scalarData.length) =
      sharedBaAddr + 26#64 := by decide
  rw [htb, h26]
  exact sep_cast hAll.2 (by ac_rfl)

/-- Proof that `arrayCowBytes` has length `34,024` and satisfies `rtC0Inv ⋆ lcnfObjMem sharedBaObj`
at `0x1000#64`. -/
theorem arrayCowBytes_ok :
    arrayCowBytes.length = 34024 ∧
    (rtC0Inv arrayRtBase arrayRtState ⋆ lcnfObjMem sharedBaObj)
      (arrayCowBytes.At arrayRtBase) := by
  have ⟨hlRt, hRt⟩ := arrayRtBytes_ok
  have ⟨hlBa, hBa⟩ := sharedBaBytes_ok
  exact arr_sep_join hlRt hlBa (by decide) hRt hBa

end LeanQbe.T.LeanLCNF
