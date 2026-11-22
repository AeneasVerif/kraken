module

public import LeanQbe.T.Examples.Kissat.FullM4InprocHot
public import LeanQbe.T.Examples.Kissat.FullM4InprocHotProof0

/-!
# Kissat `D-Full` M4 Track A6 Kitten Init Proof (`FullM4InprocHotProof1`)

Proves `full_kitten_init_m4_wp` under exact `Full.fullKittenInitSpec`
(`LeanQbe.T.Examples.Kissat.FullM4InprocHot`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4InprocHot

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.KittenMemATactics
open Kraken.Bedrock2.Test

local macro "m4_wp_lets" : tactic =>
  `(tactic| simp only [
    LeanQbe.T.op1_eq_mk, LeanQbe.T.op2_eq_mk, LeanQbe.T.op3_eq_mk,
    LeanQbe.T.wp_let_copy_eq, LeanQbe.T.wp_let_add_eq, LeanQbe.T.wp_let_sub_eq,
    LeanQbe.T.wp_let_mul_eq, LeanQbe.T.wp_let_neg_eq, LeanQbe.T.wp_let_and_eq,
    LeanQbe.T.wp_let_or_eq, LeanQbe.T.wp_let_xor_eq, LeanQbe.T.wp_let_not_eq,
    LeanQbe.T.wp_let_shl_eq, LeanQbe.T.wp_let_lshr_eq, LeanQbe.T.wp_let_ashr_eq,
    LeanQbe.T.wp_let_cmp_eq, LeanQbe.T.wp_let_select_eq, LeanQbe.T.wp_let_zext_eq,
    LeanQbe.T.wp_let_sext_eq, LeanQbe.T.wp_let_trunc_eq, LeanQbe.T.wp_let_ofBool_eq,
    LeanQbe.T.OpCode.eq, LeanQbe.T.OpCode.ne, LeanQbe.T.OpCode.ult, LeanQbe.T.OpCode.ule,
    LeanQbe.T.OpCode.ugt, LeanQbe.T.OpCode.uge, LeanQbe.T.OpCode.slt, LeanQbe.T.OpCode.sle,
    LeanQbe.T.OpCode.sgt, LeanQbe.T.OpCode.sge,
    LeanQbe.T.vals_nil, LeanQbe.T.vals_cons, LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
    LeanQbe.T.Blocks.get_here, LeanQbe.T.Blocks.get_there,
    LeanQbe.T.evalBits_eq_beq, LeanQbe.T.evalBits_ne_bne,
    LeanQbe.T.evalBits_ult_eq, LeanQbe.T.evalBits_ule_eq,
    LeanQbe.T.evalBits_ugt_eq, LeanQbe.T.evalBits_uge_eq,
    LeanQbe.T.evalBits_slt_eq, LeanQbe.T.evalBits_sle_eq,
    LeanQbe.T.evalBits_sgt_eq, LeanQbe.T.evalBits_sge_eq,
    LeanQbe.T.evalBool_eq_beq, LeanQbe.T.evalBool_ne_bne,
    LeanQbe.T.lift1, LeanQbe.T.lift2, LeanQbe.T.lift3, LeanQbe.T.liftCmp,
    cast_eq, ite_self, Bool.false_or, Bool.or_false, Bool.true_and, Bool.and_true,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false,
    true_and, and_true, Option.some.injEq,
    BitVec.reduceToNat, Nat.reduceMod, Nat.reduceLeDiff])

/-! ## 3. `full_kitten_init_m4_wp` -/

section KittenInitM4

open LeanQbe.T.C0HeadStep
open scoped KittenMemTactics KittenMemATactics KittenProjTactics

private structure InitM4ScalarState (nv0 ta0 ac0 : BitVec 32) (st : KittenState) : Prop where
  nv : st.nv = nv0
  nc : st.nc = 0#32
  orig_nc : st.orig_nc = 0#32
  lvl : st.lvl = 0#32
  prop : st.prop = 0#32
  trl_end : st.trl_end = 0#32
  unass : st.unass = nv0
  acap : st.acap = ac0
  alen : st.alen = 0#32
  incons : st.incons = 0xFFFFFFFF#32
  failing : st.failing = 0xFFFFFFFF#32
  ante : st.ante = ta0
  nassump : st.nassump = 0#32
  nunits : st.nunits = 0#32
  nres : st.nres = 0#32
  nkl : st.nkl = 0#32
  nana : st.nana = 0#32

private theorem InitM4ScalarState.putArr {nv ta ac : BitVec 32} {st : KittenState}
    (h : InitM4ScalarState nv ta ac st) (f : KArrField) (i : Nat) (v : BitVec 32) :
    InitM4ScalarState nv ta ac (st.putArr f i v) := by
  cases f <;> exact ⟨h.nv, h.nc, h.orig_nc, h.lvl, h.prop, h.trl_end, h.unass, h.acap,
    h.alen, h.incons, h.failing, h.ante, h.nassump, h.nunits, h.nres, h.nkl, h.nana⟩

private def kPutArr64 (ks : KittenState) (f : KArrField) (idx : Nat) (v : BitVec 64) :
    KittenState :=
  (ks.putArr f (2 * idx) (v.setWidth 32)).putArr f (2 * idx + 1) ((v >>> 32).setWidth 32)

private theorem kPutArr64_shapes {acap : Nat} {ks : KittenState}
    (h : ks.ShapesOk acap) (f : KArrField) (idx : Nat) (v : BitVec 64) :
    (kPutArr64 ks f idx v).ShapesOk acap :=
  (h.putArr f _ _).putArr f _ _

private theorem InitM4ScalarState.putArr64 {nv ta ac : BitVec 32} {st : KittenState}
    (h : InitM4ScalarState nv ta ac st) (f : KArrField) (idx : Nat) (v : BitVec 64) :
    InitM4ScalarState nv ta ac (kPutArr64 st f idx v) :=
  (h.putArr f _ _).putArr f _ _

private theorem kArrPut64_gen {kPtr : BitVec 64} {acap : Nat} {ks : KittenState}
    (p : List Bool) (off64 : BitVec 64) (xs : List (BitVec 32)) (f : KArrField)
    (v : BitVec 64) {idx : Nat} (hi : 2 * idx + 1 < xs.length) (hsh : ks.ShapesOk acap)
    (hget : (KittenTree kPtr ks).get p = array (t := i32) (kPtr + off64) xs)
    (heq : ((KittenTree kPtr ks).set p (array (t := i32) (kPtr + off64)
      ((xs.set (2 * idx) (v.setWidth 32)).set (2 * idx + 1)
        ((v >>> 32).setWidth 32)))).eval = KittenMem kPtr (kPutArr64 ks f idx v))
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i64 (kPtr + off64 + BitVec.ofNat 64 (8 * idx)) ∧
      (KittenMemA kPtr acap (kPutArr64 ks f idx v) ⋆ R)
        (storeMem m i64 (kPtr + off64 + BitVec.ofNat 64 (8 * idx)) v) := by
  obtain ⟨_, hm0⟩ := kittenMemA_to_mem hm
  have hm1 := SepTree.focus (t := KittenTree kPtr ks) p hm0
  rw [hget] at hm1
  obtain ⟨hok, hst⟩ := store_array32_as_i64 v hi hm1
  exact ⟨hok, kittenMem_to_amem (kPutArr64_shapes hsh f idx v)
    (SepTree.unfocus_eq (t := KittenTree kPtr ks) p heq hst)⟩

private theorem store_ka64_lvlArr {kPtr : BitVec 64} {acap : Nat} {ks : KittenState}
    (v : BitVec 64) {idx : Nat} (hi : 2 * idx + 1 < 128) (hsh : ks.ShapesOk acap)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i64 (kPtr + 128#64 + BitVec.ofNat 64 (8 * idx)) ∧
      (KittenMemA kPtr acap (kPutArr64 ks .lvlArr idx v) ⋆ R)
        (storeMem m i64 (kPtr + 128#64 + BitVec.ofNat 64 (8 * idx)) v) :=
  kArrPut64_gen (kPath 1) 128#64 ks.lvlArr .lvlArr v (by rw [hsh.lvlArr_len]; exact hi) hsh
    (by simp only [KittenTree, kPath, SepTree.get])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval, kittenHdrWords,
      kPutArr64, KittenState.putArr]) hm

private theorem store_ka64_rsn {kPtr : BitVec 64} {acap : Nat} {ks : KittenState}
    (v : BitVec 64) {idx : Nat} (hi : 2 * idx + 1 < 128) (hsh : ks.ShapesOk acap)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i64 (kPtr + 640#64 + BitVec.ofNat 64 (8 * idx)) ∧
      (KittenMemA kPtr acap (kPutArr64 ks .rsn idx v) ⋆ R)
        (storeMem m i64 (kPtr + 640#64 + BitVec.ofNat 64 (8 * idx)) v) :=
  kArrPut64_gen (kPath 2) 640#64 ks.rsn .rsn v (by rw [hsh.rsn_len]; exact hi) hsh
    (by simp only [KittenTree, kPath, SepTree.get])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval, kittenHdrWords,
      kPutArr64, KittenState.putArr]) hm

private theorem store_ka64_qprev {kPtr : BitVec 64} {acap : Nat} {ks : KittenState}
    (v : BitVec 64) {idx : Nat} (hi : 2 * idx + 1 < 128) (hsh : ks.ShapesOk acap)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i64 (kPtr + 1152#64 + BitVec.ofNat 64 (8 * idx)) ∧
      (KittenMemA kPtr acap (kPutArr64 ks .qprev idx v) ⋆ R)
        (storeMem m i64 (kPtr + 1152#64 + BitVec.ofNat 64 (8 * idx)) v) :=
  kArrPut64_gen (kPath 3) 1152#64 ks.qprev .qprev v (by rw [hsh.qprev_len]; exact hi) hsh
    (by simp only [KittenTree, kPath, SepTree.get])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval, kittenHdrWords,
      kPutArr64, KittenState.putArr]) hm

private theorem store_ka64_qnext {kPtr : BitVec 64} {acap : Nat} {ks : KittenState}
    (v : BitVec 64) {idx : Nat} (hi : 2 * idx + 1 < 128) (hsh : ks.ShapesOk acap)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i64 (kPtr + 1664#64 + BitVec.ofNat 64 (8 * idx)) ∧
      (KittenMemA kPtr acap (kPutArr64 ks .qnext idx v) ⋆ R)
        (storeMem m i64 (kPtr + 1664#64 + BitVec.ofNat 64 (8 * idx)) v) :=
  kArrPut64_gen (kPath 4) 1664#64 ks.qnext .qnext v (by rw [hsh.qnext_len]; exact hi) hsh
    (by simp only [KittenTree, kPath, SepTree.get])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval, kittenHdrWords,
      kPutArr64, KittenState.putArr]) hm

private theorem store_ka64_qstampArr {kPtr : BitVec 64} {acap : Nat} {ks : KittenState}
    (v : BitVec 64) {idx : Nat} (hi : 2 * idx + 1 < 128) (hsh : ks.ShapesOk acap)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i64 (kPtr + 2176#64 + BitVec.ofNat 64 (8 * idx)) ∧
      (KittenMemA kPtr acap (kPutArr64 ks .qstampArr idx v) ⋆ R)
        (storeMem m i64 (kPtr + 2176#64 + BitVec.ofNat 64 (8 * idx)) v) :=
  kArrPut64_gen (kPath 5) 2176#64 ks.qstampArr .qstampArr v
    (by rw [hsh.qstampArr_len]; exact hi) hsh
    (by simp only [KittenTree, kPath, SepTree.get])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval, kittenHdrWords,
      kPutArr64, KittenState.putArr]) hm

private theorem store_ka64_flags {kPtr : BitVec 64} {acap : Nat} {ks : KittenState}
    (v : BitVec 64) {idx : Nat} (hi : 2 * idx + 1 < 128) (hsh : ks.ShapesOk acap)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i64 (kPtr + 3200#64 + BitVec.ofNat 64 (8 * idx)) ∧
      (KittenMemA kPtr acap (kPutArr64 ks .flags idx v) ⋆ R)
        (storeMem m i64 (kPtr + 3200#64 + BitVec.ofNat 64 (8 * idx)) v) :=
  kArrPut64_gen (kPath 7) 3200#64 ks.flags .flags v (by rw [hsh.flags_len]; exact hi) hsh
    (by simp only [KittenTree, kPath, SepTree.get])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval, kittenHdrWords,
      kPutArr64, KittenState.putArr]) hm

private theorem store_ka64_vals {kPtr : BitVec 64} {acap : Nat} {ks : KittenState}
    (v : BitVec 64) {idx : Nat} (hi : 2 * idx + 1 < 256) (hsh : ks.ShapesOk acap)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i64 (kPtr + 3712#64 + BitVec.ofNat 64 (8 * idx)) ∧
      (KittenMemA kPtr acap (kPutArr64 ks .vals idx v) ⋆ R)
        (storeMem m i64 (kPtr + 3712#64 + BitVec.ofNat 64 (8 * idx)) v) :=
  kArrPut64_gen (kPath 8) 3712#64 ks.vals .vals v (by rw [hsh.vals_len]; exact hi) hsh
    (by simp only [KittenTree, kPath, SepTree.get])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval, kittenHdrWords,
      kPutArr64, KittenState.putArr]) hm

private theorem store_ka64_whead {kPtr : BitVec 64} {acap : Nat} {ks : KittenState}
    (v : BitVec 64) {idx : Nat} (hi : 2 * idx + 1 < 256) (hsh : ks.ShapesOk acap)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (KittenMemA kPtr acap ks ⋆ R) m) :
    storeOk m i64 (kPtr + 8320#64 + BitVec.ofNat 64 (8 * idx)) ∧
      (KittenMemA kPtr acap (kPutArr64 ks .whead idx v) ⋆ R)
        (storeMem m i64 (kPtr + 8320#64 + BitVec.ofNat 64 (8 * idx)) v) :=
  kArrPut64_gen (kPath 14) 8320#64 ks.whead .whead v (by rw [hsh.whead_len]; exact hi) hsh
    (by simp only [KittenTree, kPath, SepTree.get])
    (by simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval, kittenHdrWords,
      kPutArr64, KittenState.putArr]) hm

private theorem kPutArr64_get_other_lvl {ks : KittenState} {f : KArrField} (hf : f ≠ .lvlArr)
    (idx : Nat) (val : BitVec 64) (v : Nat) :
    (kPutArr64 ks f idx val).lvlArr[v]? = ks.lvlArr[v]? := by
  cases f <;> simp [kPutArr64, KittenState.putArr] at hf ⊢

private theorem kPutArr64_get_other_rsn {ks : KittenState} {f : KArrField} (hf : f ≠ .rsn)
    (idx : Nat) (val : BitVec 64) (v : Nat) :
    (kPutArr64 ks f idx val).rsn[v]? = ks.rsn[v]? := by
  cases f <;> simp [kPutArr64, KittenState.putArr] at hf ⊢

private theorem kPutArr64_get_other_flags {ks : KittenState} {f : KArrField} (hf : f ≠ .flags)
    (idx : Nat) (val : BitVec 64) (v : Nat) :
    (kPutArr64 ks f idx val).flags[v]? = ks.flags[v]? := by
  cases f <;> simp [kPutArr64, KittenState.putArr] at hf ⊢

private theorem kPutArr64_get_other_vals {ks : KittenState} {f : KArrField} (hf : f ≠ .vals)
    (idx : Nat) (val : BitVec 64) (v : Nat) :
    (kPutArr64 ks f idx val).vals[v]? = ks.vals[v]? := by
  cases f <;> simp [kPutArr64, KittenState.putArr] at hf ⊢

private theorem kPutArr64_get_other_whead {ks : KittenState} {f : KArrField} (hf : f ≠ .whead)
    (idx : Nat) (val : BitVec 64) (v : Nat) :
    (kPutArr64 ks f idx val).whead[v]? = ks.whead[v]? := by
  cases f <;> simp [kPutArr64, KittenState.putArr] at hf ⊢

private theorem kitten_m4_shl1_toNat (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

private def kPutArr64Step (ks : KittenState) (idx : Nat) (qn : BitVec 64) : KittenState :=
  let ks1 := kPutArr64 ks .lvlArr idx 0#64
  let ks2 := kPutArr64 ks1 .rsn idx 0xFFFFFFFFFFFFFFFF#64
  let ks3 := kPutArr64 ks2 .qprev idx (qn - 0x0000000200000002#64)
  let ks4 := kPutArr64 ks3 .qnext idx qn
  let ks5 := kPutArr64 ks4 .qstampArr idx qn
  let ks6 := kPutArr64 ks5 .flags idx 0#64
  let ks7 := kPutArr64 ks6 .vals (2 * idx) 0#64
  let ks8 := kPutArr64 ks7 .vals (2 * idx + 1) 0#64
  let ks9 := kPutArr64 ks8 .whead (2 * idx) 0xFFFFFFFFFFFFFFFF#64
  kPutArr64 ks9 .whead (2 * idx + 1) 0xFFFFFFFFFFFFFFFF#64

private theorem kPutArr64Step_eq (ks : KittenState) (idx : Nat) (qn : BitVec 64) :
    kPutArr64 (kPutArr64 (kPutArr64 (kPutArr64 (kPutArr64 (kPutArr64 (kPutArr64 (kPutArr64
      (kPutArr64 (kPutArr64 ks .lvlArr idx 0#64) .rsn idx 0xFFFFFFFFFFFFFFFF#64)
      .qprev idx (qn - 0x0000000200000002#64)) .qnext idx qn) .qstampArr idx qn)
      .flags idx 0#64) .vals (2 * idx) 0#64) .vals (2 * idx + 1) 0#64)
      .whead (2 * idx) 0xFFFFFFFFFFFFFFFF#64) .whead (2 * idx + 1) 0xFFFFFFFFFFFFFFFF#64 =
    kPutArr64Step ks idx qn := rfl

private theorem kPutArr64Step_shapes {acap : Nat} {ks : KittenState}
    (h : ks.ShapesOk acap) (idx : Nat) (qn : BitVec 64) :
    (kPutArr64Step ks idx qn).ShapesOk acap := by
  unfold kPutArr64Step
  apply kPutArr64_shapes; apply kPutArr64_shapes; apply kPutArr64_shapes
  apply kPutArr64_shapes; apply kPutArr64_shapes; apply kPutArr64_shapes
  apply kPutArr64_shapes; apply kPutArr64_shapes; apply kPutArr64_shapes
  exact kPutArr64_shapes h .lvlArr idx 0#64

private theorem kPutArr64Step_init {nv ta ac : BitVec 32} {ks : KittenState}
    (h : InitM4ScalarState nv ta ac ks) (idx : Nat) (qn : BitVec 64) :
    InitM4ScalarState nv ta ac (kPutArr64Step ks idx qn) := by
  have h1 := h.putArr64 .lvlArr idx 0#64
  have h2 := h1.putArr64 .rsn idx 0xFFFFFFFFFFFFFFFF#64
  have h3 := h2.putArr64 .qprev idx (qn - 0x0000000200000002#64)
  have h4 := h3.putArr64 .qnext idx qn
  have h5 := h4.putArr64 .qstampArr idx qn
  have h6 := h5.putArr64 .flags idx 0#64
  have h7 := h6.putArr64 .vals (2 * idx) 0#64
  have h8 := h7.putArr64 .vals (2 * idx + 1) 0#64
  have h9 := h8.putArr64 .whead (2 * idx) 0xFFFFFFFFFFFFFFFF#64
  exact h9.putArr64 .whead (2 * idx + 1) 0xFFFFFFFFFFFFFFFF#64

private theorem bv64_zero_lo : (0#64 : BitVec 64).setWidth 32 = 0#32 := by decide
private theorem bv64_zero_hi : ((0#64 : BitVec 64) >>> 32).setWidth 32 = 0#32 := by decide
private theorem bv64_ff_lo :
    (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).setWidth 32 = 0xFFFFFFFF#32 := by decide
private theorem bv64_ff_hi :
    ((0xFFFFFFFFFFFFFFFF#64 : BitVec 64) >>> 32).setWidth 32 = 0xFFFFFFFF#32 := by decide

private theorem kPutArr64Step_vars {ks : KittenState} {acap idx : Nat} (qn : BitVec 64)
    (hsh : ks.ShapesOk acap) (hidx : 2 * idx + 1 < 128)
    (hprev : ∀ v < 2 * idx, ks.lvlArr[v]? = some 0#32 ∧
      ks.rsn[v]? = some 0xFFFFFFFF#32 ∧ ks.flags[v]? = some 0#32) :
    ∀ v < 2 * idx + 2, (kPutArr64Step ks idx qn).lvlArr[v]? = some 0#32 ∧
      (kPutArr64Step ks idx qn).rsn[v]? = some 0xFFFFFFFF#32 ∧
      (kPutArr64Step ks idx qn).flags[v]? = some 0#32 := by
  intro v hv
  have hl1 : ks.lvlArr.length = 128 := hsh.lvlArr_len
  have hr1 : ks.rsn.length = 128 := hsh.rsn_len
  have hf1 : ks.flags.length = 128 := hsh.flags_len
  have hget :
      (kPutArr64Step ks idx qn).lvlArr[v]? =
        ((ks.lvlArr.set (2 * idx) 0#32).set (2 * idx + 1) 0#32)[v]? ∧
      (kPutArr64Step ks idx qn).rsn[v]? =
        ((ks.rsn.set (2 * idx) 0xFFFFFFFF#32).set (2 * idx + 1) 0xFFFFFFFF#32)[v]? ∧
      (kPutArr64Step ks idx qn).flags[v]? =
        ((ks.flags.set (2 * idx) 0#32).set (2 * idx + 1) 0#32)[v]? := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [kPutArr64Step, kPutArr64, KittenState.putArr,
        bv64_zero_lo, bv64_zero_hi, bv64_ff_lo, bv64_ff_hi]
  rw [hget.1, hget.2.1, hget.2.2]
  by_cases hv1 : v = 2 * idx + 1
  · subst hv1
    refine ⟨List.getElem?_set_self (by simp [hl1]; exact hidx),
      List.getElem?_set_self (by simp [hr1]; exact hidx),
      List.getElem?_set_self (by simp [hf1]; exact hidx)⟩
  · by_cases hv0 : v = 2 * idx
    · subst hv0
      refine ⟨?_, ?_, ?_⟩
      · rw [List.getElem?_set_ne (Ne.symm hv1), List.getElem?_set_self (by omega)]
      · rw [List.getElem?_set_ne (Ne.symm hv1), List.getElem?_set_self (by omega)]
      · rw [List.getElem?_set_ne (Ne.symm hv1), List.getElem?_set_self (by omega)]
    · have hvv := hprev v (by omega)
      refine ⟨?_, ?_, ?_⟩
      · rw [List.getElem?_set_ne (Ne.symm hv1), List.getElem?_set_ne (Ne.symm hv0)]; exact hvv.1
      · rw [List.getElem?_set_ne (Ne.symm hv1), List.getElem?_set_ne (Ne.symm hv0)]; exact hvv.2.1
      · rw [List.getElem?_set_ne (Ne.symm hv1), List.getElem?_set_ne (Ne.symm hv0)]; exact hvv.2.2

private theorem kPutArr64Step_lits {ks : KittenState} {acap idx : Nat} (qn : BitVec 64)
    (hsh : ks.ShapesOk acap) (hidx : 2 * (2 * idx + 1) + 1 < 256)
    (hprev : ∀ l < 4 * idx, ks.vals[l]? = some 0#32 ∧ ks.whead[l]? = some 0xFFFFFFFF#32) :
    ∀ l < 4 * idx + 4, (kPutArr64Step ks idx qn).vals[l]? = some 0#32 ∧
      (kPutArr64Step ks idx qn).whead[l]? = some 0xFFFFFFFF#32 := by
  intro l hl
  have hv_len : ks.vals.length = 256 := hsh.vals_len
  have hw_len : ks.whead.length = 256 := hsh.whead_len
  have hget :
      (kPutArr64Step ks idx qn).vals[l]? =
        ((((ks.vals.set (4 * idx) 0#32).set (4 * idx + 1) 0#32).set (4 * idx + 2) 0#32).set
          (4 * idx + 3) 0#32)[l]? ∧
      (kPutArr64Step ks idx qn).whead[l]? =
        ((((ks.whead.set (4 * idx) 0xFFFFFFFF#32).set (4 * idx + 1) 0xFFFFFFFF#32).set
          (4 * idx + 2) 0xFFFFFFFF#32).set (4 * idx + 3) 0xFFFFFFFF#32)[l]? := by
    refine ⟨?_, ?_⟩ <;>
      simp only [kPutArr64Step, kPutArr64, KittenState.putArr,
        bv64_zero_lo, bv64_zero_hi, bv64_ff_lo, bv64_ff_hi,
        show 2 * (2 * idx) = 4 * idx by omega,
        show 2 * (2 * idx + 1) = 4 * idx + 2 by omega]
  rw [hget.1, hget.2]
  by_cases hl3 : l = 4 * idx + 3
  · subst hl3
    exact ⟨List.getElem?_set_self (by simp [hv_len]; omega),
      List.getElem?_set_self (by simp [hw_len]; omega)⟩
  · rw [List.getElem?_set_ne (Ne.symm hl3), List.getElem?_set_ne (Ne.symm hl3)]
    by_cases hl2 : l = 4 * idx + 2
    · subst hl2
      exact ⟨List.getElem?_set_self (by simp [hv_len]; omega),
        List.getElem?_set_self (by simp [hw_len]; omega)⟩
    · rw [List.getElem?_set_ne (Ne.symm hl2), List.getElem?_set_ne (Ne.symm hl2)]
      by_cases hl1 : l = 4 * idx + 1
      · subst hl1
        exact ⟨List.getElem?_set_self (by simp [hv_len]; omega),
          List.getElem?_set_self (by simp [hw_len]; omega)⟩
      · rw [List.getElem?_set_ne (Ne.symm hl1), List.getElem?_set_ne (Ne.symm hl1)]
        by_cases hl0 : l = 4 * idx
        · subst hl0
          exact ⟨List.getElem?_set_self (by simp [hv_len]; omega),
            List.getElem?_set_self (by simp [hw_len]; omega)⟩
        · rw [List.getElem?_set_ne (Ne.symm hl0), List.getElem?_set_ne (Ne.symm hl0)]
          exact hprev l (by omega)

private def kPutArr32OddStep (ks : KittenState) (i : BitVec 32) : KittenState :=
  let ks1 := ks.putArr .lvlArr i.toNat 0#32
  let ks2 := ks1.putArr .rsn i.toNat 0xFFFFFFFF#32
  let ks3 := ks2.putArr .flags i.toNat 0#32
  let ks4 := ks3.putArr .qstampArr i.toNat (i + 1#32)
  let ks5 := ks4.putArr .qprev i.toNat (i - 1#32)
  let ks6 := ks5.putArr .qnext i.toNat 0xFFFFFFFF#32
  let l0 := i <<< (1 : Nat)
  let ks7 := ks6.putArr .vals l0.toNat 0#32
  let ks8 := ks7.putArr .vals (l0 + 1#32).toNat 0#32
  let ks9 := ks8.putArr .whead l0.toNat 0xFFFFFFFF#32
  ks9.putArr .whead (l0 + 1#32).toNat 0xFFFFFFFF#32

private theorem kPutArr32OddStep_eq (ks : KittenState) (i : BitVec 32) :
    (((((((((ks.putArr .lvlArr i.toNat 0#32).putArr .rsn i.toNat 0xFFFFFFFF#32).putArr
      .flags i.toNat 0#32).putArr .qstampArr i.toNat (i + 1#32)).putArr
      .qprev i.toNat (i - 1#32)).putArr .qnext i.toNat 0xFFFFFFFF#32).putArr
      .vals (i <<< (1 : Nat)).toNat 0#32).putArr
      .vals ((i <<< (1 : Nat)) + 1#32).toNat 0#32).putArr
      .whead (i <<< (1 : Nat)).toNat 0xFFFFFFFF#32).putArr
      .whead ((i <<< (1 : Nat)) + 1#32).toNat 0xFFFFFFFF#32 =
    kPutArr32OddStep ks i := rfl

private theorem kPutArr32OddStep_shapes {acap : Nat} {ks : KittenState}
    (h : ks.ShapesOk acap) (i : BitVec 32) : (kPutArr32OddStep ks i).ShapesOk acap := by
  unfold kPutArr32OddStep
  exact (((((((((h.putArr .lvlArr _ _).putArr .rsn _ _).putArr .flags _ _).putArr
    .qstampArr _ _).putArr .qprev _ _).putArr .qnext _ _).putArr .vals _ _).putArr
    .vals _ _).putArr .whead _ _).putArr .whead _ _

private theorem kPutArr32OddStep_init {nv ta ac : BitVec 32} {ks : KittenState}
    (h : InitM4ScalarState nv ta ac ks) (i : BitVec 32) :
    InitM4ScalarState nv ta ac (kPutArr32OddStep ks i) := by
  unfold kPutArr32OddStep
  exact (((((((((h.putArr .lvlArr _ _).putArr .rsn _ _).putArr .flags _ _).putArr
    .qstampArr _ _).putArr .qprev _ _).putArr .qnext _ _).putArr .vals _ _).putArr
    .vals _ _).putArr .whead _ _).putArr .whead _ _

private theorem kPutArr32OddStep_vars {ks : KittenState} {acap : Nat} {i : BitVec 32}
    (hsh : ks.ShapesOk acap) (hi128 : i.toNat < 128)
    (hprev : ∀ v < i.toNat, ks.lvlArr[v]? = some 0#32 ∧
      ks.rsn[v]? = some 0xFFFFFFFF#32 ∧ ks.flags[v]? = some 0#32) :
    ∀ v < i.toNat + 1, (kPutArr32OddStep ks i).lvlArr[v]? = some 0#32 ∧
      (kPutArr32OddStep ks i).rsn[v]? = some 0xFFFFFFFF#32 ∧
      (kPutArr32OddStep ks i).flags[v]? = some 0#32 := by
  intro v hv
  have hget :
      (kPutArr32OddStep ks i).lvlArr[v]? = (ks.lvlArr.set i.toNat 0#32)[v]? ∧
      (kPutArr32OddStep ks i).rsn[v]? = (ks.rsn.set i.toNat 0xFFFFFFFF#32)[v]? ∧
      (kPutArr32OddStep ks i).flags[v]? = (ks.flags.set i.toNat 0#32)[v]? :=
    ⟨rfl, rfl, rfl⟩
  rw [hget.1, hget.2.1, hget.2.2]
  by_cases hvi : v = i.toNat
  · subst hvi
    exact ⟨List.getElem?_set_self (by rw [hsh.lvlArr_len]; exact hi128),
      List.getElem?_set_self (by rw [hsh.rsn_len]; exact hi128),
      List.getElem?_set_self (by rw [hsh.flags_len]; exact hi128)⟩
  · have hvv := hprev v (by omega)
    exact ⟨by rw [List.getElem?_set_ne (Ne.symm hvi)]; exact hvv.1,
      by rw [List.getElem?_set_ne (Ne.symm hvi)]; exact hvv.2.1,
      by rw [List.getElem?_set_ne (Ne.symm hvi)]; exact hvv.2.2⟩

private theorem kPutArr32OddStep_lits {ks : KittenState} {acap : Nat} {i : BitVec 32}
    (hsh : ks.ShapesOk acap) (hi128 : i.toNat < 128)
    (hprev : ∀ l < 2 * i.toNat, ks.vals[l]? = some 0#32 ∧ ks.whead[l]? = some 0xFFFFFFFF#32) :
    ∀ l < 2 * (i.toNat + 1), (kPutArr32OddStep ks i).vals[l]? = some 0#32 ∧
      (kPutArr32OddStep ks i).whead[l]? = some 0xFFFFFFFF#32 := by
  intro l hl
  have hl0_eq : (i <<< (1 : Nat)).toNat = 2 * i.toNat := by
    rw [kitten_m4_shl1_toNat]; exact Nat.mod_eq_of_lt (by omega)
  have hl01_eq : ((i <<< (1 : Nat)) + 1#32).toNat = 2 * i.toNat + 1 := by
    rw [BitVec.toNat_add, hl0_eq, show (1#32 : BitVec 32).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega : 2 * i.toNat + 1 < 2 ^ 32)
  have hget :
      (kPutArr32OddStep ks i).vals[l]? =
        ((ks.vals.set (2 * i.toNat) 0#32).set (2 * i.toNat + 1) 0#32)[l]? ∧
      (kPutArr32OddStep ks i).whead[l]? =
        ((ks.whead.set (2 * i.toNat) 0xFFFFFFFF#32).set
          (2 * i.toNat + 1) 0xFFFFFFFF#32)[l]? := by
    refine ⟨?_, ?_⟩ <;> simp only [kPutArr32OddStep, KittenState.putArr, hl0_eq, hl01_eq]
  rw [hget.1, hget.2]
  have hv_len : ks.vals.length = 256 := hsh.vals_len
  have hw_len : ks.whead.length = 256 := hsh.whead_len
  by_cases hl1 : l = 2 * i.toNat + 1
  · subst hl1
    exact ⟨List.getElem?_set_self (by simp [hv_len]; omega),
      List.getElem?_set_self (by simp [hw_len]; omega)⟩
  · rw [List.getElem?_set_ne (Ne.symm hl1), List.getElem?_set_ne (Ne.symm hl1)]
    by_cases hl0 : l = 2 * i.toNat
    · subst hl0
      exact ⟨List.getElem?_set_self (by rw [hv_len]; omega),
        List.getElem?_set_self (by rw [hw_len]; omega)⟩
    · rw [List.getElem?_set_ne (Ne.symm hl0), List.getElem?_set_ne (Ne.symm hl0)]
      exact hprev l (by omega)

private theorem bv64_kptr0_add4_assoc (p k : BitVec 64) (hpk : p = k) (a b c : BitVec 32) :
    p + BitVec.setWidth 64 (a + b + c) * 4 = k + BitVec.setWidth 64 (a + (b + c)) * 4 := by
  rw [hpk, BitVec.add_assoc a b c]

private theorem bv64_kptr0_add4_sub (p k : BitVec 64) (hpk : p = k) (a b c : BitVec 32) :
    p + BitVec.setWidth 64 (a + b - c) * 4 = k + BitVec.setWidth 64 (a + (b - c)) * 4 := by
  rw [hpk]
  have heq : a + b - c = a + (b - c) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_sub]
    omega
  rw [heq]

private theorem bv64_add_off_eq (base a b c y : BitVec 64) (h : a + c = b) :
    base + a + y + c = base + b + y := by
  rw [BitVec.add_assoc (base + a) y c, BitVec.add_comm y c, ← BitVec.add_assoc (base + a) c y,
    BitVec.add_assoc base a c, h]

private theorem bv64_add_0mul8 (base a y : BitVec 64) :
    base + a + y + BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) * 8 = base + a + y := by
  rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) : BitVec 64) * 8 = 0#64 from by decide,
    BitVec.add_zero]

private theorem bv64_off_0 :
    (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) : BitVec 64) * 8 = 0#64 := by decide
private theorem bv64_off_1 :
    (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 1) : BitVec 64) * 8 = 8#64 := by decide
private theorem bv64_add_1mul8 (base off : BitVec 64) {n m : Nat} (h : n + 8 = m) :
    base + off + BitVec.ofNat 64 n + BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 1) * 8 =
      base + off + BitVec.ofNat 64 m := by
  rw [← h, bv64_off_1, BitVec.add_assoc (base + off)]
  congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
private theorem bv64_off_64 :
    (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 64) : BitVec 64) * 8 = 512#64 := by decide
private theorem bv64_off_128 :
    (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 128) : BitVec 64) * 8 = 1024#64 := by decide
private theorem bv64_off_192 :
    (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 192) : BitVec 64) * 8 = 1536#64 := by decide
private theorem bv64_off_256 :
    (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 256) : BitVec 64) * 8 = 2048#64 := by decide
private theorem bv64_off_384 :
    (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 384) : BitVec 64) * 8 = 3072#64 := by decide

/-- **#2 (`full_kitten_init_m4`)**: proves `Full.fullKittenInitSpec` using `u64`-widened
header clearing and pointer-stepped paired table initialization. -/
theorem full_kitten_init_m4_wp (Γ : Env) :
    ∀ args m Q X, Full.fullKittenInitSpec args m Q X →
      Func.wp Γ full_kitten_init_m4_body args m Q X := by
  rintro ⟨hPtr, nv, track_ante, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hsc_lt : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by decide)
  c0_hsteps_nogrp
  · have hcap_lt : c.scratch_cap < kMinScratchCap := by unfold kMinScratchCap; bv_omega
    have hif : c.scratch_cap < kMinScratchCap ∨ kMaxV < nv.toNat := Or.inl hcap_lt
    simp only [hif, ite_true] at hQ; exact hQ
  · have hnv_gt : kMaxV < nv.toNat := by unfold kMaxV; bv_omega
    have hif : c.scratch_cap < kMinScratchCap ∨ kMaxV < nv.toNat := Or.inr hnv_gt
    simp only [hif, ite_true] at hQ; exact hQ
  · have hcap_ge : kMinScratchCap ≤ c.scratch_cap := by unfold kMinScratchCap; bv_omega
    have hnv_le : nv.toNat ≤ kMaxV := by unfold kMaxV; bv_omega
    have hnot : ¬ (c.scratch_cap < kMinScratchCap ∨ kMaxV < nv.toNat) := by omega
    simp only [hnot, ite_false] at hQ
    let scr := s.scratch.scratch_buf
    have hscr_len : scr.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
    have hscr_ge : 8864 ≤ scr.length := by unfold kMinScratchCap at hcap_ge; omega
    let acap := scr.length - 8864
    have hacap_ge : kMinScratchCap - kBase - kSlabFixed ≤ acap := by
      unfold kMinScratchCap kBase kSlabFixed at *; omega
    have hacap_lt : acap < dimacsBound := by
      have := c.hscr; unfold dimacsBound at *; omega
    let ks0 := KittenState.ofSlab (scr.drop 256)
    have hlen_drop : 8608 ≤ (scr.drop 256).length := by simp; omega
    have hsh0 : ks0.ShapesOk acap := by
      have h1 := KittenState.shapesOk_ofSlab (xs := scr.drop 256) hlen_drop
      rwa [show (scr.drop 256).length - 8608 = acap by simp [acap]; omega] at h1
    have hmF : (FullKittenFrame c s ⋆ KittenMem (c.pScratchBuf + 1024#64) ks0 ⋆ R) m := by
      have hfull := fullMem_eq_kittenFrame (c := c) (s := s) hscr_ge
      rw [hfull] at hm; exact sep_ac hm
    clear hm
    c0_hsteps_nogrp
    let kPtr := c.pScratchBuf + 1024#64
    have hmHdr : (array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 256 * 4)
        (kittenHdrWords ks0) ⋆ ((KittenTree kPtr ks0).rest (kPath 0) ⋆
          (FullKittenFrame c s ⋆ R))) m := by
      have hm1 : (KittenMem kPtr ks0 ⋆ (FullKittenFrame c s ⋆ R)) m := sep_ac hmF
      exact KittenMemTactics.focus_kitten_hdr hm1
    clear hmF
    refine wp_while_state1 (fun p : BitVec 64 × List (BitVec 32) => p.1)
      (fun p => 16 - p.1.toNat)
      (fun p m' => p.1.toNat ≤ 16 ∧ p.2.length = 32 ∧
        (∀ j < 2 * p.1.toNat, p.2[j]? = some 0#32) ∧
        (array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 256 * 4) p.2 ⋆
          ((KittenTree kPtr ks0).rest (kPath 0) ⋆ (FullKittenFrame c s ⋆ R))) m')
      ?_ ?_
    · intro J hJ
      exact wp_jump_state (proj := fun p : BitVec 64 × List (BitVec 32) => (p.1, ()))
        (0#64, kittenHdrWords ks0) rfl
        (hJ _ m ⟨by simp, kittenHdrWords_length hsh0, fun j hj => by simp at hj, hmHdr⟩)
    · rintro J ⟨ih, hdrWs⟩ m' ⟨hi_le, hlen_w, hzeros, hm'⟩ ihLoop
      dsimp only at hi_le hlen_w hzeros hm'
      c0_hsplit
      · have hi_lt : ih.toNat < 16 := by bv_omega
        have hi_2 : 2 * ih.toNat + 1 < hdrWs.length := by rw [hlen_w]; omega
        c0_hsteps_nogrp
        have haddr : (c.pScratchBuf + 1024#64 + ih * 8) =
            (c.pScratchBuf + BitVec.ofNat 64 256 * 4) + BitVec.ofNat 64 (8 * ih.toNat) := by
          rw [show BitVec.ofNat 64 256 * 4 = (1024#64 : BitVec 64) from by decide]
          congr 1
          exact BitVec.eq_of_toNat_eq (by
            simp only [BitVec.toNat_mul, BitVec.toNat_ofNat,
              show (8 : BitVec 64).toNat = 8 from rfl]
            omega)
        have hst := store_array32_as_i64 0#64 hi_2 hm'
        rw [← haddr] at hst
        refine wp_store_sep hst fun m'' hm'' => ?_
        c0_hsteps_nogrp
        let hdrWs' := (hdrWs.set (2 * ih.toNat) 0#32).set (2 * ih.toNat + 1) 0#32
        have hhdr_eq : ((hdrWs.set (2 * ih.toNat) ((0#64 : BitVec 64).setWidth 32)).set
            (2 * ih.toNat + 1) ((0#64 >>> 32).setWidth 32)) = hdrWs' := rfl
        rw [hhdr_eq] at hm''
        have hi1 : (ih + 1#64).toNat = ih.toNat + 1 := by bv_omega
        refine ihLoop (ih + 1#64, hdrWs') m'' (by dsimp only; rw [hi1]; omega)
          ⟨by dsimp only; rw [hi1]; omega, by simp [hdrWs', hlen_w], ?_, hm''⟩
        intro j hj
        rw [hi1] at hj
        by_cases hj1 : j = 2 * ih.toNat + 1
        · subst hj1; exact List.getElem?_set_self (by simp [hlen_w]; omega)
        · rw [List.getElem?_set_ne (Ne.symm hj1)]
          by_cases hj0 : j = 2 * ih.toNat
          · subst hj0; exact List.getElem?_set_self (by rw [hlen_w]; omega)
          · rw [List.getElem?_set_ne (Ne.symm hj0)]; exact hzeros j (by omega)
      · have hi_eq : ih.toNat = 16 := by bv_omega
        have hrep : hdrWs = List.replicate 32 0#32 := by
          apply List.ext_getElem (by simp [hlen_w])
          intro j hj _
          have hj32 : j < 32 := by simp [hlen_w] at hj; exact hj
          have hz := hzeros j (by omega)
          rw [List.getElem?_eq_getElem (by omega : j < hdrWs.length)] at hz
          rw [List.getElem_replicate]; exact Option.some.inj hz
        rw [hrep] at hm'
        let hm'k : (array (t := i32) kPtr (List.replicate 32 0#32) ⋆
            ((KittenTree kPtr ks0).rest (kPath 0) ⋆ (FullKittenFrame c s ⋆ R))) m' := hm'
        let ks1 : KittenState :=
          { ks0 with
            nv := 0#32, nc := 0#32, orig_nc := 0#32, lvl := 0#32, prop := 0#32,
            trl_end := 0#32, unass := 0#32, incons := 0x0#32, failing := 0#32, ante := 0#32,
            qfirst := 0#32, qlast := 0#32, qsearch := 0#32, qstamp := 0#32, ticks := 0#32,
            tick_lim := 0#32, alen := 0#32, acap := 0#32, nassump := 0#32, nunits := 0#32,
            nres := 0#32, nkl := 0#32, nana := 0#32, status := 0#32, phase := 0#32,
            hdrTail := List.replicate 7 0#32 }
        have hsh1 : ks1.ShapesOk acap := by
          refine ⟨by simp [ks1], hsh0.lvlArr_len, hsh0.rsn_len, hsh0.qprev_len, hsh0.qnext_len,
            hsh0.qstampArr_len, hsh0.trl_len, hsh0.flags_len, hsh0.vals_len, hsh0.assump_len,
            hsh0.ana_len, hsh0.kl_len, hsh0.units_len, hsh0.res_len, hsh0.whead_len,
            hsh0.wnext_len, hsh0.wblit_len, hsh0.clOff_len, hsh0.clMeta_len, hsh0.clAux_len,
            hsh0.arena_len⟩
        have hunf : (KittenMem kPtr ks1 ⋆ (FullKittenFrame c s ⋆ R)) m' := by
          refine KittenMemTactics.unfocus_kitten_hdr (ks := ks0) (ks' := ks1)
            (hdr' := List.replicate 32 0#32) ?_ hm'k
          simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval, kittenHdrWords,
            ks1, List.replicate]
          congr 1
        let kPtr0 := c.pScratchBuf + BitVec.ofNat 64 256 * 4
        have hmA1 : (KittenMemA kPtr0 acap ks1 ⋆ (FullKittenFrame c s ⋆ R)) m' :=
          kittenMem_to_amem hsh1 hunf
        clear hm' hm'k hunf
        c0_hsteps_nogrp
        let ksH0 := ((((((ks1.putHdr .nv nv).putHdr .unass nv).putHdr .ante track_ante).putHdr
          .incons 0xFFFFFFFF#32).putHdr .failing 0xFFFFFFFF#32).putHdr .tick_lim 8192#32
          ).putHdr .acap ((BitVec.ofNat 64 c.scratch_cap - 256#64 - 8608#64).setWidth 32)
        have hshH0 : ksH0.ShapesOk acap := by
          exact ((((((hsh1.putHdr .nv nv).putHdr .unass nv).putHdr .ante
            track_ante).putHdr .incons 0xFFFFFFFF#32).putHdr .failing 0xFFFFFFFF#32).putHdr
            .tick_lim 8192#32).putHdr .acap
              ((BitVec.ofNat 64 c.scratch_cap - 256#64 - 8608#64).setWidth 32)
        have e_acap0 : ksH0.acap = BitVec.ofNat 32 acap := by
          have hh : ksH0.acap =
              (BitVec.ofNat 64 c.scratch_cap - 256#64 - 8608#64).setWidth 32 := by
            dsimp only [ksH0]; kp_field
          rw [hh]; apply BitVec.eq_of_toNat_eq
          have hsc := c.hscr; unfold dimacsBound at hsc
          simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
          have hmod : c.scratch_cap < 2 ^ 64 := by omega
          omega
        c0_hsplit
        · -- `nv == 0u`: early return
          have hnv0 : nv = 0#32 := by bv_omega
          c0_hsteps!
          let ksZ := ((ksH0.putHdr .qfirst 0xFFFFFFFF#32).putHdr .qlast 0xFFFFFFFF#32).putHdr
            .qsearch 0xFFFFFFFF#32
          have hshZ : ksZ.ShapesOk acap :=
            ((hshH0.putHdr .qfirst _).putHdr .qlast _).putHdr .qsearch _
          have hscZ : InitM4ScalarState nv track_ante ksZ.acap ksZ := by
            dsimp only [ksZ, ksH0, ks1]
            refine ⟨by kp_field, by kp_field, by kp_field, by kp_field, by kp_field,
              by kp_field, by kp_field, by kp_field, by kp_field, by kp_field,
              by kp_field, by kp_field, by kp_field, by kp_field, by kp_field,
              by kp_field, by kp_field⟩
          have e_acapZ : ksZ.acap = BitVec.ofNat 32 acap := by
            rw [show ksZ.acap = ksH0.acap by dsimp only [ksZ]; kp_field, e_acap0]
          have hfin := init_finish_inv hshZ hacap_ge hacap_lt hnv_le hscZ.nv hscZ.nc
            hscZ.orig_nc hscZ.lvl hscZ.prop hscZ.trl_end hscZ.unass
            (hscZ.acap.trans e_acapZ) hscZ.alen hscZ.incons hscZ.failing hscZ.nassump
            hscZ.nunits hscZ.nres hscZ.nkl hscZ.nana
            (fun v hv => by rw [hnv0] at hv; simp at hv)
            (fun l hl => by rw [hnv0] at hl; simp at hl)
          obtain ⟨_, hmZ'⟩ := kittenMemA_to_mem hm
          have hmZ'_exp : (FullKittenFrame c s ⋆ KittenMem kPtr ksZ ⋆ R) _ := sep_ac hmZ'
          have hmJ := fullMem_join_kitten (c := c) (s := s) (acap := acap)
            (ks' := ksZ) (R := R) (by change 256 ≤ scr.length; omega) hshZ hmZ'_exp
          let scr' := s.scratch.scratch_buf.take 256 ++ ksZ.toSlab
          have hscr_s_eq : s.scratch.scratch_buf = scr := rfl
          have hscr'_len : scr'.length = c.scratch_cap := by
            simp only [scr', hscr_s_eq, List.length_append,
              List.length_take_of_le (by omega : 256 ≤ scr.length),
              KittenState.toSlab_length hshZ]
            dsimp only [acap]; omega
          have hpre : ∀ x < kBase, scr'[x]? = s.scratch.scratch_buf[x]? := by
            intro x hx
            have htk : x < (s.scratch.scratch_buf.take 256).length := by
              rw [hscr_s_eq, List.length_take_of_le (by omega : 256 ≤ scr.length)]
              unfold kBase at hx; omega
            rw [List.getElem?_append_left htk, List.getElem?_take_of_lt
              (by unfold kBase at hx; omega)]
          have hof : kittenStateOfScratch scr' = ksZ := by
            unfold kittenStateOfScratch
            rw [slab_drop_exact _ ksZ.toSlab (by
              rw [hscr_s_eq, List.length_take_of_le (by omega : 256 ≤ scr.length)])]
            exact KittenState.ofSlab_toSlab hshZ
          have hks_inv : KittenScratchInv scr' := by
            refine ⟨by omega, by rw [hscr'_len]; exact c.hscr, ?_⟩
            rw [hof, show scr'.length - 8864 = acap by dsimp only [acap]; omega]
            exact hfin.1
          exact hQ scr' _ (fullState_lengthsOk_scratch hlen hscr'_len) hpre hks_inv
            (by rw [hof]; exact hfin.2.1) (by rw [hof]; exact hscZ.nv)
            (by rw [hof]; exact hscZ.nc) (by rw [hof]; exact hscZ.orig_nc)
            (by rw [hof]; exact hscZ.lvl) (by rw [hof]; exact hscZ.prop)
            (by rw [hof]; exact hscZ.trl_end) (by rw [hof]; exact hscZ.unass)
            (by rw [hof]; exact hscZ.incons) (by rw [hof]; exact hscZ.failing)
            (by rw [hof]; exact hscZ.ante) (by rw [hof]; exact hscZ.nassump)
            (by rw [hof]; exact hscZ.nunits)
            (by unfold kittenOrigClausesS; rw [hof]; exact hfin.2.2.1)
            (by unfold kittenAssumpLitsS; rw [hof]; exact hfin.2.2.2) hmJ
        · -- `nv ≠ 0u`: `qfirst..qstamp`, paired `u64` loop, optional odd tail, head/tail links
          have hnv_pos : 0 < nv.toNat := by bv_omega
          c0_hsteps_nogrp
          let ksH0' := ((((((ks1.putHdr .nv nv).putHdr .unass nv).putHdr .ante track_ante).putHdr
            .incons 0xFFFFFFFF#32).putHdr .failing 0xFFFFFFFF#32).putHdr .tick_lim 8192#32
            ).putHdr .acap ((BitVec.ofNat 64 c.scratch_cap - 256#64 - 8608#64).setWidth 32)
          have hshH0' : ksH0'.ShapesOk acap :=
            ((((((hsh1.putHdr .nv nv).putHdr .unass nv).putHdr .ante track_ante).putHdr
              .incons 0xFFFFFFFF#32).putHdr .failing 0xFFFFFFFF#32).putHdr .tick_lim
              8192#32).putHdr .acap
              ((BitVec.ofNat 64 c.scratch_cap - 256#64 - 8608#64).setWidth 32)
          let ksH := (((ksH0'.putHdr .qfirst 0#32).putHdr .qlast (nv - 1#32)).putHdr
            .qsearch (nv - 1#32)).putHdr .qstamp nv
          have hshH : ksH.ShapesOk acap :=
            (((hshH0'.putHdr .qfirst _).putHdr .qlast _).putHdr .qsearch _).putHdr .qstamp _
          have e_acapH : ksH.acap = BitVec.ofNat 32 acap := by
            have hh : ksH.acap =
                (BitVec.ofNat 64 c.scratch_cap - 256#64 - 8608#64).setWidth 32 := by
              dsimp only [ksH, ksH0']; kp_field
            rw [hh]; apply BitVec.eq_of_toNat_eq
            have hsc := c.hscr; unfold dimacsBound at hsc
            simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
            have hmod : c.scratch_cap < 2 ^ 64 := by omega
            omega
          have hInitH : InitM4ScalarState nv track_ante ksH.acap ksH := by
            dsimp only [ksH, ksH0', ks1]
            refine ⟨by kp_field, by kp_field, by kp_field, by kp_field, by kp_field,
              by kp_field, by kp_field, by kp_field, by kp_field, by kp_field,
              by kp_field, by kp_field, by kp_field, by kp_field, by kp_field,
              by kp_field, by kp_field⟩
          refine wp_while_state
            (fun st : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 32 × KittenState =>
              (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1, ()))
            (fun st => nv.toNat - st.2.2.2.2.1.toNat)
            (fun st m2 =>
              let (_, p, pv, pw, i, ks) := st
              i.toNat ≤ nv.toNat ∧ i.toNat % 2 = 0 ∧
              p = kPtr0 + 128#64 + BitVec.ofNat 64 (4 * i.toNat) ∧
              pv = kPtr0 + 3712#64 + BitVec.ofNat 64 (8 * i.toNat) ∧
              pw = kPtr0 + 8320#64 + BitVec.ofNat 64 (8 * i.toNat) ∧
              ks.ShapesOk acap ∧ InitM4ScalarState nv track_ante ksH.acap ks ∧
              (∀ v < i.toNat, ks.lvlArr[v]? = some 0#32 ∧
                ks.rsn[v]? = some 0xFFFFFFFF#32 ∧ ks.flags[v]? = some 0#32) ∧
              (∀ l < 2 * i.toNat, ks.vals[l]? = some 0#32 ∧
                ks.whead[l]? = some 0xFFFFFFFF#32) ∧
              (KittenMemA kPtr0 acap ks ⋆ (FullKittenFrame c s ⋆ R)) m2)
            ?_ ?_
          · intro JL hJL
            exact wp_jump_state
              (proj := fun st : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 ×
                  BitVec 32 × KittenState =>
                (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1, ()))
              (0x0000000200000001#64, c.pScratchBuf + 1152#64, c.pScratchBuf + 4736#64,
                c.pScratchBuf + 9344#64, 0#32, ksH)
              (by simp [BitVec.add_assoc]; decide)
              (hJL _ _ ⟨by simp, by simp,
                by simp [kPtr0, BitVec.add_assoc],
                by simp [kPtr0, BitVec.add_assoc],
                by simp [kPtr0, BitVec.add_assoc],
                hshH, hInitH, fun _ h => by simp at h, fun _ h => by simp at h, hm⟩)
          · rintro JL ⟨qnext_w, p, pv, pw, i, ksL⟩ m2
              ⟨hi_le, hi_even, hp_eq, hpv_eq, hpw_eq, hshL, hscL, hvarsL, hlitsL, hm2⟩ ihL
            c0_hsplit
            · have hi1_lt : i.toNat + 1 < nv.toNat := by unfold kMaxV at hnv_le; bv_omega
              let idx := i.toNat / 2
              have hidx2 : 2 * idx + 1 < 128 := by unfold kMaxV at hnv_le; omega
              have hidx4a : 2 * (2 * idx) + 1 < 256 := by unfold kMaxV at hnv_le; omega
              have hidx4b : 2 * (2 * idx + 1) + 1 < 256 := by unfold kMaxV at hnv_le; omega
              have hi_4 : 4 * i.toNat = 8 * idx := by omega
              have hi_8a : 8 * i.toNat = 8 * (2 * idx) := by omega
              have hi_8b : 8 * i.toNat + 8 = 8 * (2 * idx + 1) := by omega
              rw [hp_eq, hpv_eq, hpw_eq]
              c0_hsteps_nogrp
              refine wp_store_sep_at (ptr := kPtr0 + 128#64 + BitVec.ofNat 64 (8 * idx))
                (by rw [hi_4]; exact bv64_add_0mul8 kPtr0 128#64 (BitVec.ofNat 64 (8 * idx)))
                (store_ka64_lvlArr 0#64 hidx2 hshL hm2) fun m3 hm3 => ?_
              c0_hsteps_nogrp
              have hsh3 := kPutArr64_shapes hshL .lvlArr idx 0#64
              refine wp_store_sep_at (ptr := kPtr0 + 640#64 + BitVec.ofNat 64 (8 * idx))
                (by rw [hi_4, bv64_off_64]; exact bv64_add_off_eq _ _ _ _ _ (by decide))
                (store_ka64_rsn 0xFFFFFFFFFFFFFFFF#64 hidx2 hsh3 hm3) fun m4 hm4 => ?_
              c0_hsteps_nogrp
              have hsh4 := kPutArr64_shapes hsh3 .rsn idx 0xFFFFFFFFFFFFFFFF#64
              refine wp_store_sep_at (ptr := kPtr0 + 1152#64 + BitVec.ofNat 64 (8 * idx))
                (by rw [hi_4, bv64_off_128]; exact bv64_add_off_eq _ _ _ _ _ (by decide))
                (store_ka64_qprev (qnext_w - 0x0000000200000002#64) hidx2 hsh4 hm4)
                fun m5 hm5 => ?_
              c0_hsteps_nogrp
              have hsh5 := kPutArr64_shapes hsh4 .qprev idx (qnext_w - 0x0000000200000002#64)
              refine wp_store_sep_at (ptr := kPtr0 + 1664#64 + BitVec.ofNat 64 (8 * idx))
                (by rw [hi_4, bv64_off_192]; exact bv64_add_off_eq _ _ _ _ _ (by decide))
                (store_ka64_qnext qnext_w hidx2 hsh5 hm5) fun m6 hm6 => ?_
              c0_hsteps_nogrp
              have hsh6 := kPutArr64_shapes hsh5 .qnext idx qnext_w
              refine wp_store_sep_at (ptr := kPtr0 + 2176#64 + BitVec.ofNat 64 (8 * idx))
                (by rw [hi_4, bv64_off_256]; exact bv64_add_off_eq _ _ _ _ _ (by decide))
                (store_ka64_qstampArr qnext_w hidx2 hsh6 hm6) fun m7 hm7 => ?_
              c0_hsteps_nogrp
              have hsh7 := kPutArr64_shapes hsh6 .qstampArr idx qnext_w
              refine wp_store_sep_at (ptr := kPtr0 + 3200#64 + BitVec.ofNat 64 (8 * idx))
                (by rw [hi_4, bv64_off_384]; exact bv64_add_off_eq _ _ _ _ _ (by decide))
                (store_ka64_flags 0#64 hidx2 hsh7 hm7) fun m8 hm8 => ?_
              c0_hsteps_nogrp
              have hsh8 := kPutArr64_shapes hsh7 .flags idx 0#64
              refine wp_store_sep_at (ptr := kPtr0 + 3712#64 + BitVec.ofNat 64 (8 * (2 * idx)))
                (by rw [hi_8a]
                    exact bv64_add_0mul8 kPtr0 3712#64 (BitVec.ofNat 64 (8 * (2 * idx))))
                (store_ka64_vals 0#64 hidx4a hsh8 hm8) fun m9 hm9 => ?_
              c0_hsteps_nogrp
              have hsh9 := kPutArr64_shapes hsh8 .vals (2 * idx) 0#64
              refine wp_store_sep_at
                (ptr := kPtr0 + 3712#64 + BitVec.ofNat 64 (8 * (2 * idx + 1)))
                (bv64_add_1mul8 kPtr0 3712#64 hi_8b)
                (store_ka64_vals 0#64 hidx4b hsh9 hm9) fun m10 hm10 => ?_
              c0_hsteps_nogrp
              have hsh10 := kPutArr64_shapes hsh9 .vals (2 * idx + 1) 0#64
              refine wp_store_sep_at (ptr := kPtr0 + 8320#64 + BitVec.ofNat 64 (8 * (2 * idx)))
                (by rw [hi_8a]
                    exact bv64_add_0mul8 kPtr0 8320#64 (BitVec.ofNat 64 (8 * (2 * idx))))
                (store_ka64_whead 0xFFFFFFFFFFFFFFFF#64 hidx4a hsh10 hm10) fun m11 hm11 => ?_
              c0_hsteps_nogrp
              have hsh11 := kPutArr64_shapes hsh10 .whead (2 * idx) 0xFFFFFFFFFFFFFFFF#64
              refine wp_store_sep_at
                (ptr := kPtr0 + 8320#64 + BitVec.ofNat 64 (8 * (2 * idx + 1)))
                (bv64_add_1mul8 kPtr0 8320#64 hi_8b)
                (store_ka64_whead 0xFFFFFFFFFFFFFFFF#64 hidx4b hsh11 hm11) fun m12 hm12 => ?_
              c0_hsteps_nogrp
              have hi2_n : (i + 2#32).toNat = i.toNat + 2 := by
                rw [BitVec.toNat_add, show (2#32 : BitVec 32).toNat = 2 from rfl]
                exact Nat.mod_eq_of_lt (by unfold kMaxV at hnv_le; omega)
              rw [kPutArr64Step_eq] at hm12
              have hidx_eq : 2 * idx = i.toNat := by omega
              have hvars_next : ∀ v < (i + 2#32).toNat,
                  (kPutArr64Step ksL idx qnext_w).lvlArr[v]? = some 0#32 ∧
                  (kPutArr64Step ksL idx qnext_w).rsn[v]? = some 0xFFFFFFFF#32 ∧
                  (kPutArr64Step ksL idx qnext_w).flags[v]? = some 0#32 := by
                rw [hi2_n, show i.toNat + 2 = 2 * idx + 2 by omega]
                exact kPutArr64Step_vars qnext_w hshL hidx2 fun v hv => hvarsL v (by omega)
              have hlits_next : ∀ l < 2 * (i + 2#32).toNat,
                  (kPutArr64Step ksL idx qnext_w).vals[l]? = some 0#32 ∧
                  (kPutArr64Step ksL idx qnext_w).whead[l]? = some 0xFFFFFFFF#32 := by
                rw [hi2_n, show 2 * (i.toNat + 2) = 4 * idx + 4 by omega]
                exact kPutArr64Step_lits qnext_w hshL hidx4b fun l hl => hlitsL l (by omega)
              exact ihL
                (qnext_w + 0x0000000200000002#64,
                 kPtr0 + 128#64 + BitVec.ofNat 64 (4 * i.toNat) + 8#64,
                 kPtr0 + 3712#64 + BitVec.ofNat 64 (8 * i.toNat) + 16#64,
                 kPtr0 + 8320#64 + BitVec.ofNat 64 (8 * i.toNat) + 16#64,
                 i + 2#32, kPutArr64Step ksL idx qnext_w) m12
                (by dsimp only; rw [hi2_n]; omega)
                ⟨by rw [hi2_n]; omega,
                 by rw [hi2_n]; omega,
                 by rw [hi2_n, show 4 * (i.toNat + 2) = 4 * i.toNat + 8 by omega,
                      BitVec.add_assoc (kPtr0 + 128#64),
                      show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add],
                 by rw [hi2_n, show 8 * (i.toNat + 2) = 8 * i.toNat + 16 by omega,
                      BitVec.add_assoc (kPtr0 + 3712#64),
                      show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add],
                 by rw [hi2_n, show 8 * (i.toNat + 2) = 8 * i.toNat + 16 by omega,
                      BitVec.add_assoc (kPtr0 + 8320#64),
                      show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add],
                 kPutArr64Step_shapes hshL idx qnext_w,
                 kPutArr64Step_init hscL idx qnext_w,
                 hvars_next, hlits_next, hm12⟩
            · -- Exit `while (i + 1u < nv)`: `i.toNat + 1 ≥ nv.toNat`, so `nv - 1 ≤ i ≤ nv`
              have hi_ge : nv.toNat ≤ i.toNat + 1 := by unfold kMaxV at hnv_le; bv_omega
              refine wp_join0
                (fun m3 => ∃ ksTail : KittenState,
                  ksTail.ShapesOk acap ∧ InitM4ScalarState nv track_ante ksH.acap ksTail ∧
                  (∀ v < nv.toNat, ksTail.lvlArr[v]? = some 0#32 ∧
                    ksTail.rsn[v]? = some 0xFFFFFFFF#32 ∧ ksTail.flags[v]? = some 0#32) ∧
                  (∀ l < 2 * nv.toNat, ksTail.vals[l]? = some 0#32 ∧
                    ksTail.whead[l]? = some 0xFFFFFFFF#32) ∧
                  (KittenMemA kPtr0 acap ksTail ⋆ (FullKittenFrame c s ⋆ R)) m3) ?_ ?_
              · rintro _ m3 ⟨ksTail, hshT, hscT, hvarsT, hlitsT, hm3⟩
                have hi128 : 0 < 128 := by decide
                have hi1_128 : 1 < 128 := by decide
                have hnv1_eq : (nv - 1#32).toNat = nv.toNat - 1 := by
                  have h1 : (1#32 : BitVec 32) ≤ nv :=
                    BitVec.le_def.mpr (by simp only [BitVec.toNat_ofNat]; omega)
                  rw [BitVec.toNat_sub_of_le h1, show (1#32 : BitVec 32).toNat = 1 from rfl]
                have hnv1_wrap : (nv - 1#32).toNat < 2 ^ 28 := by
                  rw [hnv1_eq]; unfold kMaxV at hnv_le; omega
                have hnv1_128 : (nv - 1#32).toNat < 128 := by
                  rw [hnv1_eq]; unfold kMaxV at hnv_le; omega
                m4_wp_lets
                refine wp_store_sep_at (ptr := kPtr0 + (288#32 + 0#32).setWidth 64 * 4)
                  (by rfl)
                  (store_ka_qprev (ks := ksTail) (i := 0#32) 0xFFFFFFFF#32
                    (by decide) hi128 hm3)
                  fun m3a hm3a => ?_
                refine wp_join0
                  (fun m4 => ∃ ksQ : KittenState,
                    ksQ.ShapesOk acap ∧ InitM4ScalarState nv track_ante ksH.acap ksQ ∧
                    (∀ v < nv.toNat, ksQ.lvlArr[v]? = some 0#32 ∧
                      ksQ.rsn[v]? = some 0xFFFFFFFF#32 ∧ ksQ.flags[v]? = some 0#32) ∧
                    (∀ l < 2 * nv.toNat, ksQ.vals[l]? = some 0#32 ∧
                      ksQ.whead[l]? = some 0xFFFFFFFF#32) ∧
                    (KittenMemA kPtr0 acap ksQ ⋆ (FullKittenFrame c s ⋆ R)) m4) ?_ ?_
                · rintro _ m4 ⟨ksQ, hshQ, hscQ, hvarsQ, hlitsQ, hm4⟩
                  m4_wp_lets
                  refine wp_store_sep_at (ptr := kPtr0 + (416#32 + (nv - 1#32)).setWidth 64 * 4)
                    (bv64_kptr0_add4_sub _ _ rfl 416#32 nv 1#32)
                    (store_ka_qnext (ks := ksQ) 0xFFFFFFFF#32 hnv1_wrap hnv1_128 hm4)
                    fun m5 hm5 => ?_
                  simp only [LeanQbe.T.wp_ret, LeanQbe.T.vals_nil]
                  let ksFin := ksQ.putArr .qnext (nv - 1#32).toNat 0xFFFFFFFF#32
                  have hshF : ksFin.ShapesOk acap := hshQ.putArr .qnext _ _
                  have hscF : InitM4ScalarState nv track_ante ksH.acap ksFin :=
                    hscQ.putArr .qnext _ _
                  have hvarsF : ∀ v < nv.toNat, ksFin.lvlArr[v]? = some 0#32 ∧
                      ksFin.rsn[v]? = some 0xFFFFFFFF#32 ∧ ksFin.flags[v]? = some 0#32 := by
                    intro v hv; have := hvarsQ v hv; dsimp only [ksFin]
                    exact ⟨by kp_field; exact this.1, by kp_field; exact this.2.1,
                      by kp_field; exact this.2.2⟩
                  have hlitsF : ∀ l < 2 * nv.toNat, ksFin.vals[l]? = some 0#32 ∧
                      ksFin.whead[l]? = some 0xFFFFFFFF#32 := by
                    intro l hl; have := hlitsQ l hl; dsimp only [ksFin]
                    exact ⟨by kp_field; exact this.1, by kp_field; exact this.2⟩
                  have hfin := init_finish_inv hshF hacap_ge hacap_lt hnv_le hscF.nv hscF.nc
                    hscF.orig_nc hscF.lvl hscF.prop hscF.trl_end hscF.unass
                    (hscF.acap.trans e_acapH) hscF.alen hscF.incons hscF.failing hscF.nassump
                    hscF.nunits hscF.nres hscF.nkl hscF.nana hvarsF hlitsF
                  obtain ⟨_, hmFin'⟩ := kittenMemA_to_mem hm5
                  have hmFin'_exp : (FullKittenFrame c s ⋆ KittenMem kPtr ksFin ⋆ R) _ :=
                    sep_ac hmFin'
                  have hmJ := fullMem_join_kitten (c := c) (s := s) (acap := acap)
                    (ks' := ksFin) (R := R) (by change 256 ≤ scr.length; omega) hshF hmFin'_exp
                  let scr' := s.scratch.scratch_buf.take 256 ++ ksFin.toSlab
                  have hscr_s_eq : s.scratch.scratch_buf = scr := rfl
                  have hscr'_len : scr'.length = c.scratch_cap := by
                    simp only [scr', hscr_s_eq, List.length_append,
                      List.length_take_of_le (by omega : 256 ≤ scr.length),
                      KittenState.toSlab_length hshF]
                    dsimp only [acap]; omega
                  have hpre : ∀ x < kBase, scr'[x]? = s.scratch.scratch_buf[x]? := by
                    intro x hx
                    have htk : x < (s.scratch.scratch_buf.take 256).length := by
                      rw [hscr_s_eq, List.length_take_of_le (by omega : 256 ≤ scr.length)]
                      unfold kBase at hx; omega
                    rw [List.getElem?_append_left htk, List.getElem?_take_of_lt
                      (by unfold kBase at hx; omega)]
                  have hof : kittenStateOfScratch scr' = ksFin := by
                    unfold kittenStateOfScratch
                    rw [slab_drop_exact _ ksFin.toSlab (by
                      rw [hscr_s_eq, List.length_take_of_le (by omega : 256 ≤ scr.length)])]
                    exact KittenState.ofSlab_toSlab hshF
                  have hks_inv : KittenScratchInv scr' := by
                    refine ⟨by omega, by rw [hscr'_len]; exact c.hscr, ?_⟩
                    rw [hof, show scr'.length - 8864 = acap by dsimp only [acap]; omega]
                    exact hfin.1
                  exact hQ scr' _ (fullState_lengthsOk_scratch hlen hscr'_len) hpre hks_inv
                    (by rw [hof]; exact hfin.2.1) (by rw [hof]; exact hscF.nv)
                    (by rw [hof]; exact hscF.nc) (by rw [hof]; exact hscF.orig_nc)
                    (by rw [hof]; exact hscF.lvl) (by rw [hof]; exact hscF.prop)
                    (by rw [hof]; exact hscF.trl_end) (by rw [hof]; exact hscF.unass)
                    (by rw [hof]; exact hscF.incons) (by rw [hof]; exact hscF.failing)
                    (by rw [hof]; exact hscF.ante) (by rw [hof]; exact hscF.nassump)
                    (by rw [hof]; exact hscF.nunits)
                    (by unfold kittenOrigClausesS; rw [hof]; exact hfin.2.2.1)
                    (by unfold kittenAssumpLitsS; rw [hof]; exact hfin.2.2.2) hmJ
                · intro JQ hJQ
                  m4_wp_lets
                  simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
                  refine ⟨fun _ => ?_, fun _ => ?_⟩
                  · m4_wp_lets
                    refine wp_store_sep_at (ptr := kPtr0 + (288#32 + 1#32).setWidth 64 * 4)
                      (by rfl)
                      (store_ka_qprev (ks := ksTail.putArr .qprev 0 0xFFFFFFFF#32)
                        (i := 1#32) 0#32 (by decide) hi1_128 hm3a)
                      fun m3b hm3b => ?_
                    simp only [LeanQbe.T.wp_jump, LeanQbe.T.vals_nil]
                    have hvarsQ : ∀ v < nv.toNat,
                        ((ksTail.putArr .qprev 0 0xFFFFFFFF#32).putArr .qprev 1 0#32).lvlArr[v]? =
                          some 0#32 ∧
                        ((ksTail.putArr .qprev 0 0xFFFFFFFF#32).putArr .qprev 1 0#32).rsn[v]? =
                          some 0xFFFFFFFF#32 ∧
                        ((ksTail.putArr .qprev 0 0xFFFFFFFF#32).putArr .qprev 1 0#32).flags[v]? =
                          some 0#32 := by
                      intro v hv; have := hvarsT v hv
                      exact ⟨by kp_field; exact this.1, by kp_field; exact this.2.1,
                        by kp_field; exact this.2.2⟩
                    have hlitsQ : ∀ l < 2 * nv.toNat,
                        ((ksTail.putArr .qprev 0 0xFFFFFFFF#32).putArr .qprev 1 0#32).vals[l]? =
                          some 0#32 ∧
                        ((ksTail.putArr .qprev 0 0xFFFFFFFF#32).putArr .qprev 1 0#32).whead[l]? =
                          some 0xFFFFFFFF#32 := by
                      intro l hl; have := hlitsT l hl
                      exact ⟨by kp_field; exact this.1, by kp_field; exact this.2⟩
                    exact hJQ _ ⟨_, (hshT.putArr .qprev 0 _).putArr .qprev 1 _,
                      (hscT.putArr .qprev 0 _).putArr .qprev 1 _, hvarsQ, hlitsQ, hm3b⟩
                  · simp only [LeanQbe.T.wp_jump, LeanQbe.T.vals_nil]
                    have hvarsQ : ∀ v < nv.toNat,
                        (ksTail.putArr .qprev 0 0xFFFFFFFF#32).lvlArr[v]? = some 0#32 ∧
                        (ksTail.putArr .qprev 0 0xFFFFFFFF#32).rsn[v]? = some 0xFFFFFFFF#32 ∧
                        (ksTail.putArr .qprev 0 0xFFFFFFFF#32).flags[v]? = some 0#32 := by
                      intro v hv; have := hvarsT v hv
                      exact ⟨by kp_field; exact this.1, by kp_field; exact this.2.1,
                        by kp_field; exact this.2.2⟩
                    have hlitsQ : ∀ l < 2 * nv.toNat,
                        (ksTail.putArr .qprev 0 0xFFFFFFFF#32).vals[l]? = some 0#32 ∧
                        (ksTail.putArr .qprev 0 0xFFFFFFFF#32).whead[l]? = some 0xFFFFFFFF#32 := by
                      intro l hl; have := hlitsT l hl
                      exact ⟨by kp_field; exact this.1, by kp_field; exact this.2⟩
                    exact hJQ _ ⟨_, hshT.putArr .qprev 0 _, hscT.putArr .qprev 0 _,
                      hvarsQ, hlitsQ, hm3a⟩
              · intro JT hJT
                m4_wp_lets
                simp only [LeanQbe.T.wp_jnz, LeanQbe.T.Arg.val_var]
                refine ⟨fun hc => ?_, fun hc => ?_⟩
                · have hi_lt : i.toNat < nv.toNat := of_decide_eq_true hc
                  have hi_eq : i.toNat + 1 = nv.toNat := by omega
                  have hi_wrap : i.toNat < 2 ^ 28 := by unfold kMaxV at hnv_le; omega
                  have hi_128 : i.toNat < 128 := by unfold kMaxV at hnv_le; omega
                  have hl0_eq : (i <<< (1 : Nat)).toNat = 2 * i.toNat := by
                    rw [kitten_m4_shl1_toNat]; unfold kMaxV at hnv_le; omega
                  have hl0_wrap : (i <<< (1 : Nat)).toNat < 2 ^ 28 := by
                    rw [hl0_eq]; unfold kMaxV at hnv_le; omega
                  have hl0_256 : (i <<< (1 : Nat)).toNat < 256 := by
                    rw [hl0_eq]; unfold kMaxV at hnv_le; omega
                  have hl01_eq : ((i <<< (1 : Nat)) + 1#32).toNat = 2 * i.toNat + 1 := by
                    rw [BitVec.toNat_add, hl0_eq, show (1#32 : BitVec 32).toNat = 1 from rfl]
                    omega
                  have hl01_wrap : ((i <<< (1 : Nat)) + 1#32).toNat < 2 ^ 28 := by
                    rw [hl01_eq]; unfold kMaxV at hnv_le; omega
                  have hl01_256 : ((i <<< (1 : Nat)) + 1#32).toNat < 256 := by
                    rw [hl01_eq]; unfold kMaxV at hnv_le; omega
                  m4_wp_lets
                  refine wp_store_sep_at (ptr := kPtr0 + (32#32 + i).setWidth 64 * 4)
                    (by rfl) (store_ka_lvlArr 0#32 hi_wrap hi_128 hm2) fun mT1 hmT1 => ?_
                  m4_wp_lets
                  refine wp_store_sep_at (ptr := kPtr0 + (160#32 + i).setWidth 64 * 4)
                    (by rfl) (store_ka_rsn 0xFFFFFFFF#32 hi_wrap hi_128 hmT1)
                    fun mT2 hmT2 => ?_
                  m4_wp_lets
                  refine wp_store_sep_at (ptr := kPtr0 + (800#32 + i).setWidth 64 * 4)
                    (by rfl) (store_ka_flags 0#32 hi_wrap hi_128 hmT2)
                    fun mT3 hmT3 => ?_
                  m4_wp_lets
                  refine wp_store_sep_at (ptr := kPtr0 + (544#32 + i).setWidth 64 * 4)
                    (by rfl) (store_ka_qstampArr (i + 1#32) hi_wrap hi_128 hmT3)
                    fun mT4 hmT4 => ?_
                  m4_wp_lets
                  refine wp_store_sep_at (ptr := kPtr0 + (288#32 + i).setWidth 64 * 4)
                    (by rfl) (store_ka_qprev (i - 1#32) hi_wrap hi_128 hmT4)
                    fun mT5 hmT5 => ?_
                  m4_wp_lets
                  refine wp_store_sep_at (ptr := kPtr0 + (416#32 + i).setWidth 64 * 4)
                    (by rfl) (store_ka_qnext 0xFFFFFFFF#32 hi_wrap hi_128 hmT5)
                    fun mT6 hmT6 => ?_
                  m4_wp_lets
                  refine wp_store_sep_at
                    (ptr := kPtr0 + (928#32 + (i <<< (1 : Nat))).setWidth 64 * 4)
                    (by rfl) (store_ka_vals 0#32 hl0_wrap hl0_256 hmT6)
                    fun mT7 hmT7 => ?_
                  m4_wp_lets
                  refine wp_store_sep_at
                    (ptr := kPtr0 + (928#32 + ((i <<< (1 : Nat)) + 1#32)).setWidth 64 * 4)
                    (bv64_kptr0_add4_assoc _ _ rfl 928#32 (i <<< (1 : Nat)) 1#32)
                    (store_ka_vals 0#32 hl01_wrap hl01_256 hmT7)
                    fun mT8 hmT8 => ?_
                  m4_wp_lets
                  refine wp_store_sep_at
                    (ptr := kPtr0 + (2080#32 + (i <<< (1 : Nat))).setWidth 64 * 4)
                    (by rfl) (store_ka_whead 0xFFFFFFFF#32 hl0_wrap hl0_256 hmT8)
                    fun mT9 hmT9 => ?_
                  m4_wp_lets
                  refine wp_store_sep_at
                    (ptr := kPtr0 + (2080#32 + ((i <<< (1 : Nat)) + 1#32)).setWidth 64 * 4)
                    (bv64_kptr0_add4_assoc _ _ rfl 2080#32 (i <<< (1 : Nat)) 1#32)
                    (store_ka_whead 0xFFFFFFFF#32 hl01_wrap hl01_256 hmT9)
                    fun mT10 hmT10 => ?_
                  simp only [LeanQbe.T.wp_jump, LeanQbe.T.vals_nil]
                  rw [kPutArr32OddStep_eq] at hmT10
                  refine hJT _ ⟨kPutArr32OddStep ksL i, kPutArr32OddStep_shapes hshL i,
                    kPutArr32OddStep_init hscL i, ?_, ?_, hmT10⟩
                  · rw [← hi_eq]; exact kPutArr32OddStep_vars hshL hi_128 hvarsL
                  · rw [← hi_eq]; exact kPutArr32OddStep_lits hshL hi_128 hlitsL
                · have hi_ge2 : nv.toNat ≤ i.toNat := Nat.not_lt.mp (of_decide_eq_false hc)
                  have hi_eq : i.toNat = nv.toNat := by omega
                  simp only [LeanQbe.T.wp_jump, LeanQbe.T.vals_nil]
                  rw [hi_eq] at hvarsL hlitsL
                  exact hJT _ ⟨ksL, hshL, hscL, hvarsL, hlitsL, hm2⟩

end KittenInitM4

/-! ## Concrete `Mem 64` Fixture for Track A6 Non-Vacuity -/

def nvM4Cfg : FullCfg where
  hdr := 0x2000000#64; avail := 42716; mv := 1; max_vars := 1; bva_cap := 0; nc := 0
  arena_cap := 0; wcap := 1; delayed_cap := 0; red_cap := 0; extend_cap := 0
  scratch_cap := 10240; hbva := rfl
  hmv := by decide
  hmaxv := by decide
  hnc := by decide
  harena := by decide
  hwcap := by decide
  hdel := by decide
  hred := by decide
  hext := by decide
  hscr := by decide
  havail_fit := by decide
  hsize := by decide

def nvM4Scratch : FullScratch where
  heap_len := 0; scinc := 0#64; rel_period := 0#64; rel_limit := 0#64; rel_wait := 0#64
  rel_u := 0#64; rel_v := 0#64; rel_trigger := 0#64; conflicts := 0#64
  learned_lits := 0#64; min_removed := 0#64; delayed_len := 0; stable := 0#64
  switched := 0#64; mode_count := 0#64; mode_confl_lim := 0#64; mode_tick_lim := 0#64
  mode_saved_ticks := 0#64; search_ticks := 0#64; q_first := 0#64; q_last := 0#64
  q_search_idx := 0#64; q_search_stamp := 0#64; q_cur_stamp := 0#64
  target_assigned := 0#64; best_assigned := 0#64; rephase_limit := 0#64; rephased := 0#64
  reduce_limit := 0#64; reductions := 0#64; tier1 := 0#64; tier2 := 0#64
  restarts := 0#64; restart_limit := 0#64; ema_fast_biased := 0#64; ema_fast_exp := 0#64
  ema_slow_biased := 0#64; ema_slow_exp := 0#64; extend_len := 0; rng_state := 0#64
  chrono_levels := 0#64; otfs_cnt := 0#64; eager_sub_cnt := 0#64; probe_limit := 0#64
  probings := 0#64; elim_limit := 0#64; eliminations := 0#64; elim_bound := 0#64
  iterating := 0#64; hbr_cnt := 0#64; trans_cnt := 0#64; viv_cnt := 0#64
  subst_cnt := 0#64; cong_cnt := 0#64; sweep_cnt := 0#64; bve_cnt := 0#64
  bce_cnt := 0#64; bva_cnt := 0#64; walk_cnt_stat := 0#64; fwd_sub_cnt := 0#64
  fwd_str_cnt := 0#64; ant_sz := 0#64; res_sz := 0#64
  walk_vals := List.replicate 2 0#8; phases := List.replicate 1 0#8
  phases_target := List.replicate 1 0#8; phases_best := List.replicate 1 0#8
  walk_best := List.replicate 1 0#8; heap := List.replicate 1 0#32
  pos := List.replicate 1 0#32; shrink_stk := List.replicate 1 0#32
  q_prev := List.replicate 1 0#32; q_next := List.replicate 1 0#32
  q_stamp := List.replicate 1 0#32; wsort := List.replicate 2 0#32
  work_stk1 := List.replicate 2 0#32; work_stk2 := List.replicate 2 0#32
  tarjan_mark := List.replicate 2 0#32; tarjan_reach := List.replicate 2 0#32
  score := List.replicate 1 0#64; sim_sig := List.replicate 1 0#64
  glue_used := List.replicate 64 0#32; last_learned := List.replicate 16 0xFFFFFFFF#32
  delayed := []; red_refs := []; extend_stk := []
  scratch_buf := List.replicate 10240 0#32

def nvM4State : FullState where
  core :=
    { d_cur := 0#64, d_val := 0#64, cur_vars := 1, unassigned := 2#64
      arena_len := 0, wlen := 1, wusable := 0#64, arena_garbage := 0#64
      first_reducible := 0#64, num_irred := 0#64, num_redundant := 0#64, num_binary := 0#64
      unflushed := 0#64, probing := 0#64, trail_end := 0, propagated := 0
      cur_level := 0, fuel := 1#64, confl_ref := 0#64, confl_type := 0#64
      confl_lit0 := 0#64, confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0
      min_clr_len := 0, min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64
      inconsistent := 0#64, vals := [0#8, 0#8], lit_mark := [0#8, 0#8], mrk := [0#8]
      flags := [0#32], lvl := [0#32], rsns := [0xFFFFFFFF#32], trl := [0#32]
      trail_pos := [0#32], tmp := [0#32], min_clr := [0#32]
      frame_trail := [0#32, 0#32], frame_dec := [0#32, 0#32]
      wvec := [0#32, 0#32, 0#32, 0#32], repr := [0#32, 0#32]
      min_stk := [0#32, 0#32, 0#32, 0#32], arena := [], wstk := [0#32] }
  scratch := nvM4Scratch

theorem nvM4State_lengths : nvM4State.LengthsOk nvM4Cfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, List.length_replicate⟩⟩

def nvM4BlockHdr : List UInt8 :=
  bytes64 [1#64, 0#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords nvM4Cfg nvM4State)

def nvM4BlockBytes : List UInt8 :=
  (bytesOf (t := i8) nvM4State.core.vals ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvM4State.scratch.walk_vals ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvM4State.core.lit_mark ++ List.replicate 6 0) ++
  (bytesOf (t := i8) nvM4State.core.mrk ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvM4State.scratch.phases ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvM4State.scratch.phases_target ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvM4State.scratch.phases_best ++ List.replicate 7 0) ++
  (bytesOf (t := i8) nvM4State.scratch.walk_best ++ List.replicate 7 0)

def nvM4BlockU32A : List UInt8 :=
  (bytesOf (t := i32) nvM4State.core.flags ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4State.core.lvl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4State.core.rsns ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4State.core.trl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4State.core.trail_pos ++ List.replicate 4 0)

def nvM4BlockU32B : List UInt8 :=
  (bytesOf (t := i32) nvM4State.core.tmp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4State.scratch.heap ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4State.scratch.pos ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4State.core.min_clr ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4State.scratch.shrink_stk ++ List.replicate 4 0)

def nvM4BlockU32C : List UInt8 :=
  (bytesOf (t := i32) nvM4State.scratch.q_prev ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4State.scratch.q_next ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4State.scratch.q_stamp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4State.core.frame_trail ++ List.replicate 0 0) ++
  (bytesOf (t := i32) nvM4State.core.frame_dec ++ List.replicate 0 0)

def nvM4BlockWvec : List UInt8 :=
  bytesOf (t := i32) nvM4State.core.wvec ++
  bytesOf (t := i32) nvM4State.core.repr ++
  bytesOf (t := i32) nvM4State.scratch.wsort ++
  bytesOf (t := i32) nvM4State.scratch.work_stk1 ++
  bytesOf (t := i32) nvM4State.scratch.work_stk2 ++
  bytesOf (t := i32) nvM4State.scratch.tarjan_mark ++
  bytesOf (t := i32) nvM4State.scratch.tarjan_reach ++
  bytes64 nvM4State.scratch.score ++
  bytes64 nvM4State.scratch.sim_sig

def nvM4BlockTail : List UInt8 :=
  bytesOf (t := i32) nvM4State.core.min_stk ++
  bytesOf (t := i32) nvM4State.scratch.glue_used ++
  bytesOf (t := i32) nvM4State.scratch.last_learned ++
  bytesOf (t := i32) nvM4State.core.arena ++
  bytesOf (t := i32) nvM4State.core.wstk ++
  bytesOf (t := i32) nvM4State.scratch.delayed ++
  bytesOf (t := i32) nvM4State.scratch.red_refs ++
  bytesOf (t := i32) nvM4State.scratch.extend_stk ++
  bytesOf (t := i32) nvM4State.scratch.scratch_buf ++
  List.replicate 0 0

def nvM4Bytes : List UInt8 :=
  nvM4BlockHdr ++ nvM4BlockBytes ++ nvM4BlockU32A ++ nvM4BlockU32B ++
  nvM4BlockU32C ++ nvM4BlockWvec ++ nvM4BlockTail

def nvM4Mem : Mem 64 := nvM4Bytes.At nvM4Cfg.hdr

private theorem nvM4_sep_append {P Q : Mem 64 → Prop} {a b : BitVec 64}
    {bs1 bs2 : List UInt8}
    (hb : b = a + BitVec.ofNat 64 bs1.length) (hlen : bs1.length + bs2.length ≤ 2 ^ 64)
    (h1 : P (bs1.At a)) (h2 : Q (bs2.At b)) : (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have heq := congrFun (Mem.At_append_sep bs1 bs2 a hlen) ((bs1 ++ bs2).At a)
  rw [← hb] at heq
  exact sep_mono2 (fun _ h => h ▸ h1) (fun _ h => h ▸ h2) _ (heq.mp rfl)

private theorem nvM4_arr_pad_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n pad : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n + pad ≤ 2 ^ 64) :
    (bytesOf xs ++ List.replicate pad 0).length = n + pad ∧
    (array (t := t) a xs ⋆ region (a + BitVec.ofNat 64 n) pad)
      ((bytesOf xs ++ List.replicate pad 0).At a) :=
  ⟨by rw [List.length_append, bytesOf_length, List.length_replicate, hn],
   nvM4_sep_append (by rw [bytesOf_length, hn])
     (by rw [bytesOf_length, List.length_replicate]; omega)
     (array_bytes a xs (by omega)) ⟨List.replicate pad 0, List.length_replicate, rfl⟩⟩

private theorem nvM4_arr_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytesOf xs).length = n ∧ array (t := t) a xs ((bytesOf xs).At a) :=
  ⟨by rw [bytesOf_length, hn], array_bytes a xs (by omega)⟩

private theorem nvM4_arr64_p {a : BitVec 64} {xs : List (BitVec 64)} (n : Nat)
    (hn : 8 * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytes64 xs).length = n ∧ array64 a xs ((bytes64 xs).At a) :=
  ⟨by rw [bytes64_length, hn], array64_bytes a xs (by omega)⟩

private theorem nvM4_join {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    {n1 n2 : Nat} (h1 : bs1.length = n1 ∧ P (bs1.At a))
    (h2 : bs2.length = n2 ∧ Q (bs2.At b))
    (hb : b = a + BitVec.ofNat 64 n1) (hbd : n1 + n2 ≤ 2 ^ 64) :
    (bs1 ++ bs2).length = n1 + n2 ∧ (P ⋆ Q) ((bs1 ++ bs2).At a) :=
  ⟨by rw [List.length_append, h1.1, h2.1], nvM4_sep_append (h1.1 ▸ hb) (by omega) h1.2 h2.2⟩

private theorem nvM4_reorg {P Q : Mem 64 → Prop} {bs : List UInt8} {a : BitVec 64} {n : Nat}
    (h : bs.length = n ∧ P (bs.At a)) (himp : ∀ m, P m → Q m) : bs.length = n ∧ Q (bs.At a) :=
  ⟨h.1, himp _ h.2⟩

private theorem nvM4_zip4 {A1 B1 A2 B2 A3 B3 A4 B4 : Mem 64 → Prop} {m : Mem 64}
    (h : ((((A1 ⋆ B1) ⋆ (A2 ⋆ B2)) ⋆ (A3 ⋆ B3)) ⋆ (A4 ⋆ B4)) m) :
    (((A1 ⋆ A3 ⋆ A4) ⋆ A2) ⋆ (B1 ⋆ B2 ⋆ B3 ⋆ B4)) m := sep_ac h

private theorem nvM4_zip4_tail {C A2 P1 A5 B5 A6 B6 A7 B7 A8 B8 : Mem 64 → Prop} {m : Mem 64}
    (h : ((((((C ⋆ A2) ⋆ P1) ⋆ (A5 ⋆ B5)) ⋆ (A6 ⋆ B6)) ⋆ (A7 ⋆ B7)) ⋆ (A8 ⋆ B8)) m) :
    (C ⋆ (A2 ⋆ A5 ⋆ A6 ⋆ A7 ⋆ A8) ⋆ (P1 ⋆ B5 ⋆ B6 ⋆ B7 ⋆ B8)) m := sep_ac h

theorem nvM4Mem_ok : FullMem nvM4Cfg nvM4State nvM4Mem := by
  let c := nvM4Cfg; let s := nvM4State
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 6 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 7 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv1 : BitVec.ofNat 64 c.max_vars = 1#64 := rfl
  have hmv2 : BitVec.ofNat 64 (2 * c.max_vars) = 2#64 := rfl
  have hmv4 : BitVec.ofNat 64 (4 * c.max_vars) = 4#64 := rfl
  have hmv8 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 8#64 := rfl
  have hHdr : nvM4BlockHdr.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        (nvM4BlockHdr.At c.hdr) :=
    nvM4_join (nvM4_arr64_p (a := c.hdr) (xs := [1#64, 0#64, 0#64, 0#64]) 32 rfl (by decide))
      (nvM4_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      (by decide) (by decide)
  have hBytes : nvM4BlockBytes.length = 64 ∧
      (FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
        (nvM4BlockBytes.At c.pVals) := by
    have h1 := nvM4_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 2 6 rfl (by decide)
    have h2 := nvM4_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 2 6 rfl
      (by decide)
    have h3 := nvM4_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 2 6 rfl
      (by decide)
    have h4 := nvM4_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 1 7 rfl (by decide)
    have h5 := nvM4_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 1 7 rfl
      (by decide)
    have h6 := nvM4_arr_pad_p (t := i8) (a := c.pPhasesTarget) (xs := s.scratch.phases_target)
      1 7 rfl (by decide)
    have h7 := nvM4_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 1 7 rfl
      (by decide)
    have h8 := nvM4_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 1 7 rfl
      (by decide)
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 2#64) 6 ⋆ region (c.pWalkVals + 2#64) 6 ⋆
      region (c.pLitMark + 2#64) 6 ⋆ region (c.pMark + 1#64) 7
    have h12 := nvM4_join h1 h2 (by decide) (by decide)
    have h123 := nvM4_join h12 h3 (by decide) (by decide)
    have h1234 := nvM4_reorg (nvM4_join h123 h4 (by decide) (by decide))
      (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
      fun _ hm => nvM4_zip4 hm
    have h12345 := nvM4_join h1234 h5 (by decide) (by decide)
    have h123456 := nvM4_join h12345 h6 (by decide) (by decide)
    have h1234567 := nvM4_join h123456 h7 (by decide) (by decide)
    exact nvM4_reorg (nvM4_join h1234567 h8 (by decide) (by decide)) fun _ hm => by
      have hfin := nvM4_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes; rw [hvb, hmb, hmv2, hmv1]
      simpa only [pB1, sep_assoc] using hfin
  have hU32A : nvM4BlockU32A.length = 40 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nvM4BlockU32A.At c.pFlags) := by
    have h1 := nvM4_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 4 4 rfl (by decide)
    have h2 := nvM4_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 4 4 rfl (by decide)
    have h3 := nvM4_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 4 4 rfl (by decide)
    have h4 := nvM4_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 4 4 rfl (by decide)
    have h5 := nvM4_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 4 4 rfl
      (by decide)
    have h12 := nvM4_join h1 h2 (by decide) (by decide)
    have h123 := nvM4_join h12 h3 (by decide) (by decide)
    have h1234 := nvM4_join h123 h4 (by decide) (by decide)
    exact nvM4_reorg (nvM4_join h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, hmv4]; exact sep_ac hm
  have hU32B : nvM4BlockU32B.length = 40 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (nvM4BlockU32B.At c.pTmp) := by
    have h1 := nvM4_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 4 4 rfl (by decide)
    have h2 := nvM4_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 4 4 rfl (by decide)
    have h3 := nvM4_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 4 4 rfl (by decide)
    have h4 := nvM4_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 4 4 rfl
      (by decide)
    have h5 := nvM4_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 4 4 rfl
      (by decide)
    have h12 := nvM4_join h1 h2 (by decide) (by decide)
    have h123 := nvM4_join h12 h3 (by decide) (by decide)
    have h1234 := nvM4_join h123 h4 (by decide) (by decide)
    exact nvM4_reorg (nvM4_join h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, hmv4]; exact sep_ac hm
  have hU32C : nvM4BlockU32C.length = 40 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (nvM4BlockU32C.At c.pQPrev) := by
    have h1 := nvM4_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 4 4 rfl
      (by decide)
    have h2 := nvM4_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 4 4 rfl
      (by decide)
    have h3 := nvM4_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 4 4 rfl
      (by decide)
    have h4 := nvM4_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 8 0 rfl
      (by decide)
    have h5 := nvM4_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 8 0 rfl
      (by decide)
    have h12 := nvM4_join h1 h2 (by decide) (by decide)
    have h123 := nvM4_join h12 h3 (by decide) (by decide)
    have h1234 := nvM4_join h123 h4 (by decide) (by decide)
    exact nvM4_reorg (nvM4_join h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu8, hmv4, hmv8]; exact sep_ac hm
  have hWvec : nvM4BlockWvec.length = 80 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (nvM4BlockWvec.At c.pWvec) := by
    have h1 := nvM4_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 16 rfl (by decide)
    have h2 := nvM4_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 8 rfl (by decide)
    have h3 := nvM4_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 8 rfl (by decide)
    have h4 := nvM4_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 8 rfl
      (by decide)
    have h5 := nvM4_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 8 rfl
      (by decide)
    have h6 := nvM4_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 8 rfl
      (by decide)
    have h7 := nvM4_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 8 rfl
      (by decide)
    have h8 := nvM4_arr64_p (a := c.pScore) (xs := s.scratch.score) 8 rfl (by decide)
    have h9 := nvM4_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 8 rfl (by decide)
    have h12 := nvM4_join h1 h2 (by decide) (by decide)
    have h123 := nvM4_join h12 h3 (by decide) (by decide)
    have h1234 := nvM4_join h123 h4 (by decide) (by decide)
    have h12345 := nvM4_join h1234 h5 (by decide) (by decide)
    have h123456 := nvM4_join h12345 h6 (by decide) (by decide)
    have h1234567 := nvM4_join h123456 h7 (by decide) (by decide)
    have h12345678 := nvM4_join h1234567 h8 (by decide) (by decide)
    exact nvM4_reorg (nvM4_join h12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nvM4BlockTail.length = 41300 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        (nvM4BlockTail.At c.pMinStk) := by
    have h1 := nvM4_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 16 rfl (by decide)
    have h2 := nvM4_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
      (by decide)
    have h3 := nvM4_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64 rfl
      (by decide)
    have h4 := nvM4_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 0 rfl (by decide)
    have h5 := nvM4_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide)
    have h6 := nvM4_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl (by decide)
    have h7 := nvM4_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl
      (by decide)
    have h8 := nvM4_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := nvM4_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 40960
      (by show 4 * (List.replicate 10240 (0#32 : BitVec 32)).length = 40960
          rw [List.length_replicate]) (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
      ⟨rfl, ⟨List.replicate 0 0, by decide, rfl⟩⟩
    have h12 := nvM4_join h1 h2 (by decide) (by decide)
    have h123 := nvM4_join h12 h3 (by decide) (by decide)
    have h1234 := nvM4_join h123 h4 (by decide) (by decide)
    have h12345 := nvM4_join h1234 h5 (by decide) (by decide)
    have h123456 := nvM4_join h12345 h6 (by decide) (by decide)
    have h1234567 := nvM4_join h123456 h7 (by decide) (by decide)
    have h12345678 := nvM4_join h1234567 h8 (by decide) (by decide)
    have h123456789 := nvM4_join h12345678 h9 (by decide) (by decide)
    exact nvM4_reorg (nvM4_join h123456789 h10 (by decide) (by decide)) fun _ hm => by
      unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := nvM4_join hHdr hBytes (by decide) (by decide)
  have h02 := nvM4_join h01 hU32A (by decide) (by decide)
  have h03 := nvM4_join h02 hU32B (by decide) (by decide)
  have h04 := nvM4_join h03 hU32C (by decide) (by decide)
  have h05 := nvM4_join h04 hWvec (by decide) (by decide)
  exact (nvM4_reorg (Q := FullMem c s) (nvM4_join h05 hTail (by decide) (by decide))
    fun _ hm => by
      unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
        FullScrMetaArrs FullCfg.pad
      exact sep_ac hm).2

theorem nvM4_refs_nil : fullArenaClauseRefsCore nvM4State.core = [] := rfl

theorem nvM4_witness : FullWitnessInv nvM4Cfg (cnfOfClauses []) [] nvM4State.core where
  ext_sound := ⟨fun _ h => by simp at h, fun h => h⟩
  inconsistent_sound := fun h => absurd rfl h
  arena :=
    { len_ok := Or.inl rfl
      refs_wf := fun _ h => by rw [nvM4_refs_nil] at h; cases h
      shrk_term := fun _ h => by rw [nvM4_refs_nil] at h; cases h
      lits_lt := fun _ h => by rw [nvM4_refs_nil] at h; cases h
      entails := fun _ h => by rw [nvM4_refs_nil] at h; cases h }
  watches := WatchesInv.of_slices
    (fun l _ => by
      have hz : fullWatchSizeCore nvM4State.core l = 0 := by
        rcases l with _ | _ | _ <;> rfl
      have ho : fullWatchOffCore nvM4State.core l = 0 := by
        rcases l with _ | _ | _ <;> rfl
      rw [hz, ho]; exact Nat.zero_le _)
    (fun l _ h => by
      have hz : fullWatchSizeCore nvM4State.core l = 0 := by
        rcases l with _ | _ | _ <;> rfl
      omega)
    (fun l1 _ _ _ _ h => by
      have hz : fullWatchSizeCore nvM4State.core l1 = 0 := by
        rcases l1 with _ | _ | _ <;> rfl
      omega)
    (fun l _ => by
      have hz : fullWatchSizeCore nvM4State.core l = 0 := by
        rcases l with _ | _ | _ <;> rfl
      rw [hz]; exact .empty)
  cur_level_le := Nat.le_refl _
  trail_lits_lt := fun _ h => by change _ < 0 at h; omega
  trail_vars_nodup := fun _ _ h => by change _ < 0 at h; omega
  vals_domain := fun l hl => Or.inl (by
    have : l < 2 := hl
    rcases l with _ | _ | _ <;> first | rfl | omega)
  vals_true_iff := fun l hl =>
    ⟨fun h => by
       have : l < 2 := hl
       rcases l with _ | _ | _ <;> first | omega | (exfalso; revert h; decide),
     fun ⟨_, h, _⟩ => by change _ < 0 at h; omega⟩
  vals_false_iff := fun l hl =>
    ⟨fun h => by
       have : l < 2 := hl
       rcases l with _ | _ | _ <;> first | omega | (exfalso; revert h; decide),
     fun ⟨_, h, _⟩ => by change _ < 0 at h; omega⟩
  lvl_le := fun _ h => by change _ < 0 at h; omega
  dec_earliest := fun _ _ h => by change _ < 0 at h; omega
  levels_inhabited := fun _ h1 h2 => by change _ ≤ 0 at h2; omega
  level0_sound := fun _ h => by change _ < 0 at h; omega
  trail_pos_inv := fun _ h => by change _ < 0 at h; omega
  level0_rsn_none := fun _ h => by change _ < 0 at h; omega
  frame_trail_lt := fun L h => by
    have h0 : L = 0 := by change L ≤ 0 at h; omega
    subst h0; decide
  frame_trail_mono := fun L1 L2 h1 h2 => by
    have hL2 : L2 = 0 := by change L2 ≤ 0 at h2; omega
    have hL1 : L1 = 0 := by omega
    subst hL1 hL2; exact Nat.le_refl _
  frame_trail_before_lt := fun _ h1 h2 => by change _ ≤ 0 at h2; omega
  frame_dec_lt := fun _ h1 h2 => by change _ ≤ 0 at h2; omega
  reason_inv := fun _ h => by change _ < 0 at h; omega
  reason_lit_mem := fun _ h => by change _ < 0 at h; omega

theorem nvM4_layout : WatchStackLayout nvM4State.core :=
  nvM4_witness.watches.layout

end LeanQbe.T.Examples.Kissat.FullM4InprocHot
