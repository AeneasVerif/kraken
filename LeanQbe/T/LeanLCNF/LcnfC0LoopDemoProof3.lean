module

public import LeanQbe.T.LeanLCNF.LcnfC0LoopDemoProof2

/-!
# Dual-Arch WP Proof for `FactLoop` (`LcnfC0LoopDemoProof3`)

Section 3a (part 2): `twoLimb_divLimb_wp`, `twoLimb_divJoin_wp`,
`twoLimb_divStep_wp`, `twoLimb_outerDiv_wp`, and `lcnf_nat_to_str_two_limb_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T LeanQbe.T.Frontend.C0 LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Std Std.ExtHashMap
open scoped LeanQbe.T.ProofUtil

private theorem wp_let_udiv10 {Γ : Env} {Q : Post [i64]} {X : XPost} {x : BitVec 64}
    {k : Tup Val [i64] → Expr Val Cont [i64]} {m : Mem 64} :
    wp Γ Q X (Expr.let_
      { sig := [i64, i64], code := OpCode.udiv 64, args := (Arg.var x, Arg.imm 10, ()) } k) m ↔
    wp Γ Q X (k (x / 10#64, ())) m := by
  rw [wp_let]; simp [Op.wp, OpCode.wp, Arg.val, vals]
private theorem wp_let_urem10 {Γ : Env} {Q : Post [i64]} {X : XPost} {x : BitVec 64}
    {k : Tup Val [i64] → Expr Val Cont [i64]} {m : Mem 64} :
    wp Γ Q X (Expr.let_
      { sig := [i64, i64], code := OpCode.urem 64, args := (Arg.var x, Arg.imm 10, ()) } k) m ↔
    wp Γ Q X (k (x % 10#64, ())) m := by
  rw [wp_let]; simp [Op.wp, OpCode.wp, Arg.val, vals]
private def divLimbStepExpr (tmp remBv j : BitVec 64)
    (after : Tup Val [i64, i64] → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.let_ { sig := [i64, i64], code := OpCode.sub i64, args := (Arg.var j, Arg.imm 1, ()) }
    fun p_19 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var tmp, Arg.imm 16, ()) }
    fun p_20 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.imm 8, Arg.var p_19.fst, ()) }
    fun p_21 =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_20.fst, Arg.var p_21.fst, ()) }
    fun p_22 =>
  Expr.load i64 (Arg.var p_22.fst) fun ld =>
  Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 32, ()) } fun p_23 =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.shl i64, args := (Arg.var remBv, Arg.var p_23.fst, ()) }
    fun p =>
  Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 32, ()) } fun p_24 =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.lshr i64, args := (Arg.var ld, Arg.var p_24.fst, ()) }
    fun p_25 =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.or i64, args := (Arg.var p.fst, Arg.var p_25.fst, ()) }
    fun p =>
  Expr.let_ { sig := [i64, i64], code := OpCode.udiv 64, args := (Arg.var p.fst, Arg.imm 10, ()) }
    fun p_26 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.urem 64, args := (Arg.var p.fst, Arg.imm 10, ()) }
    fun p =>
  Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 32, ()) } fun p_27 =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.shl i64, args := (Arg.var p.fst, Arg.var p_27.fst, ()) }
    fun p =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.and i64, args := (Arg.var ld, Arg.imm 4294967295, ()) }
    fun p_28 =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.or i64, args := (Arg.var p.fst, Arg.var p_28.fst, ()) }
    fun p =>
  Expr.let_ { sig := [i64, i64], code := OpCode.udiv 64, args := (Arg.var p.fst, Arg.imm 10, ()) }
    fun p_29 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.urem 64, args := (Arg.var p.fst, Arg.imm 10, ()) }
    fun p =>
  Expr.let_ { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var tmp, Arg.imm 16, ()) }
    fun p_30 =>
  Expr.let_ { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.imm 8, Arg.var p_19.fst, ()) }
    fun p_31 =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_30.fst, Arg.var p_31.fst, ()) }
    fun p_32 =>
  Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 32, ()) } fun p_33 =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.shl i64, args := (Arg.var p_26.fst, Arg.var p_33.fst, ()) }
    fun p_34 =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.or i64, args := (Arg.var p_34.fst, Arg.var p_29.fst, ()) }
    fun p_35 =>
  Expr.store (Arg.var p_35.fst) (Arg.var p_32.fst) (after (p.fst, p_19.fst, ()))
private theorem twoLimb_divLimb_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {tmp remBv j w0 w1 wOld : BitVec 64} {i remNat : Nat} {m : Mem 64}
    {after : Tup Val [i64, i64] → Expr Val Cont [i64]}
    (hi : i < 2) (hj : j = BitVec.ofNat 64 (i + 1))
    (hwIdx : [w0, w1][i] = wOld)
    (hremLt : remNat < 10) (hremEq : remBv = BitVec.ofNat 64 remNat)
    (hm : (array64 (tmp + 16#64) [w0, w1] ⋆ R) m)
    (hk : ∀ m',
      (array64 (tmp + 16#64) ([w0, w1].set i (div10Limb remNat wOld).2) ⋆ R) m' →
      wp loopRtEnv Q X (after (BitVec.ofNat 64 (div10Limb remNat wOld).1, j - 1#64, ())) m') :
    wp loopRtEnv Q X (divLimbStepExpr tmp remBv j after) m := by
  have hjSub : j - 1#64 = BitVec.ofNat 64 i := by
    rw [hj]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by decide), Nat.add_sub_cancel]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hi8Eq : BitVec.ofNat 64 (8 * i) = 8#64 * BitVec.ofNat 64 i := by
    cases i with
    | zero => decide
    | succ k => cases k with | zero => decide | succ => omega
  unfold divLimbStepExpr
  t_wp_unfold
  have hld : loadVal m i64 (tmp + 16#64 + 8#64 * (j - 1#64)) = some wOld := by
    rw [hjSub, ← hi8Eq, ← hwIdx]
    exact loadVal_array64 (i := i) (by simp [hi]) hm
  refine ⟨wOld, by simpa using hld, ?_⟩
  rw [wp_let_udiv10, wp_let_urem10]
  t_wp_unfold
  rw [wp_let_udiv10, wp_let_urem10]
  t_wp_unfold
  have hc0 := div10Limb_c0 wOld hremLt
  have hst := store_array64 (a := tmp + 16#64) (i := i) (div10Limb remNat wOld).2 (by simp [hi]) hm
  rw [show (1 : BitVec 64) = 1#64 from rfl, show (8 : BitVec 64) = 8#64 from rfl,
    show (16 : BitVec 64) = 16#64 from rfl, show (4294967295 : BitVec 64) = 4294967295#64 from rfl,
    hjSub, ← hi8Eq, hremEq, hc0.1, hc0.2]
  refine ⟨hst.1, ?_⟩
  rw [← hjSub]
  exact hk _ hst.2
private theorem wp_ugt0_jnz {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {x : BitVec 64} {t e : Expr Val Cont rs} :
    wp Γ Q X (Expr.let_
      { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide),
        args := (Arg.var x, Arg.imm 0, ()) } fun p => Expr.jnz (Arg.var p.fst) t e) m ↔
    ((BitVec.ult 0#64 x = true → wp Γ Q X t m) ∧
      (BitVec.ult 0#64 x = false → wp Γ Q X e m)) := by
  rw [wp_let]
  dsimp only [Op.wp, OpCode.wp, Arg.val, vals, Ty.hasFloat, Bool.false_eq_true, ite_false,
    liftCmp, CmpOp.evalBits, decide_eq_true_eq]
  rw [wp_jnz]
  rfl
private theorem wp_add_imm_store {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a v imm : Val i64} {k : Expr Val Cont rs} :
    wp Γ Q X (Expr.let_
      { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var a, Arg.imm imm, ()) }
      fun p => Expr.store (Arg.var v) (Arg.var p.fst) k) m ↔
    (storeOk m i64 (a + imm) ∧ wp Γ Q X k (storeMem m i64 (a + imm) v)) := by
  rw [wp_let]
  dsimp only [Op.wp, OpCode.wp, Arg.val, vals, Ty.hasFloat, Bool.false_eq_true, ite_false, lift2]
  rw [wp_store]
  rfl
private theorem blocks_get_here {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    {sig : List (List Ty)} {ts : List Ty} (f : Tup V ts → Expr V L rs)
    (b : Blocks V L rs sig) (xs : Tup V ts) :
    (Blocks.cons f b).get Member.here xs = f xs := rfl
private def divJoinExpr (tmp rev dlen curCn lim remBv : BitVec 64)
    (after : Tup Val [i64, i64] → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i64, i64]])
    (fun Js_2 =>
      Blocks.cons
        (fun p_dlcn =>
          trimExpr2 tmp p_dlcn.snd.fst (fun q => after (p_dlcn.fst, q.fst, ())))
        Blocks.nil)
    fun Js_2 =>
    Expr.let_
      { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool (by decide),
        args := (Arg.var dlen, Arg.var lim, ()) } fun p_19 =>
    Expr.jnz (Arg.var p_19.fst)
      (Expr.let_
        { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var rev, Arg.imm 24, ()) }
          fun p_20 =>
      Expr.let_
        { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var p_20.fst, Arg.var dlen, ()) }
          fun p_21 =>
      Expr.let_
        { sig := [i64, i64], code := OpCode.add i64, args := (Arg.imm 48, Arg.var remBv, ()) }
          fun p_r =>
      Expr.let_
        { sig := [i64], code := OpCode.trunc 64 8, args := (Arg.var p_r.fst, ()) } fun p_b =>
      Expr.store (Arg.var p_b.fst) (Arg.var p_21.fst)
        (Expr.let_
          { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var dlen, Arg.imm 1, ()) }
            fun p_dl =>
          Expr.jump Js_2.fst (Arg.var p_dl.fst, Arg.var curCn, ())))
      (Expr.jump Js_2.fst (Arg.var dlen, Arg.imm 0, ()))
private theorem twoLimb_divJoin_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {rt tmp rev dlen curCn cw0 cw1 d0_2 d1_2 : BitVec 64} {st3 : RtC0State}
    {objs' : List LcnfObj} {d0_1 : Nat} {revBs fullRev : List UInt8} {m : Mem 64}
    {after : Tup Val [i64, i64] → Expr Val Cont [i64]}
    (hrevL : revBs.length = 40) (hdlenLt : dlen.toNat < 40)
    (hd0Lt : d0_1 < 10)
    (hbv : bvDiv10Rev cw0 cw1 = UInt8.ofNat (48 + d0_1) :: bvDiv10Rev d0_2 d1_2)
    (hdlSum : dlen.toNat + (bvDiv10Rev cw0 cw1).length = fullRev.length)
    (hdlPref : revBs.take dlen.toNat ++ bvDiv10Rev cw0 cw1 = fullRev)
    (hcn : (curCn = 2#64) ∨ (curCn = 1#64 ∧ d1_2 = 0#64))
    (hm : (array64 (tmp + 16#64) [d0_2, d1_2] ⋆
      (bytes (rev + 24#64) revBs ⋆ twoLimbTail rt rev tmp st3 objs' 0#64 R)) m)
    (hk : ∀ (cn'' : BitVec 64) (revBs' : List UInt8) (mk' : Mem 64),
      revBs'.length = 40 →
      (dlen + 1#64).toNat + (bvDiv10Rev d0_2 d1_2).length = fullRev.length →
      revBs'.take (dlen + 1#64).toNat ++ bvDiv10Rev d0_2 d1_2 = fullRev →
      ((cn'' = 2#64 ∧ d1_2 ≠ 0#64) ∨
        (cn'' = 1#64 ∧ d1_2 = 0#64 ∧ d0_2 ≠ 0#64) ∨
        (cn'' = 0#64 ∧ d0_2 = 0#64 ∧ d1_2 = 0#64)) →
      (array64 (tmp + 16#64) [d0_2, d1_2] ⋆
        (bytes (rev + 24#64) revBs' ⋆ twoLimbTail rt rev tmp st3 objs' 0#64 R)) mk' →
      wp loopRtEnv Q X (after (dlen + 1#64, cn'', ())) mk') :
    wp loopRtEnv Q X
      (divJoinExpr tmp rev dlen curCn (20 * 2#64) (BitVec.ofNat 64 d0_1) after) m := by
  unfold divJoinExpr
  refine wp_join_group (Γ := loopRtEnv)
    (fun (dl', cn', ()) ms => dl' = dlen + 1#64 ∧ cn' = curCn ∧
      (array64 (tmp + 16#64) [d0_2, d1_2] ⋆
        (bytes (rev + 24#64) (revBs.set dlen.toNat (UInt8.ofNat (48 + d0_1))) ⋆
          twoLimbTail rt rev tmp st3 objs' 0#64 R)) ms) ?_ ?_
  · rintro Jt ⟨dl', cn', ⟨⟩⟩ ms ⟨rfl, hcnEq, hms⟩
    rw [hcnEq]
    t_wp_unfold
    refine twoLimb_trim_wp (a0 := d0_2) (a1 := d1_2) (cnInit := curCn) hcn hms
      fun cn'' _ hcn'' => ?_
    have hdl1 : (dlen + 1#64).toNat = dlen.toNat + 1 := by
      rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    have htake1 :
        (revBs.set dlen.toNat (UInt8.ofNat (48 + d0_1))).take (dlen + 1#64).toNat =
          revBs.take dlen.toNat ++ [UInt8.ofNat (48 + d0_1)] := by
      rw [hdl1, list_take_succ _ _ (by simp [hrevL, hdlenLt]), list_take_set_of_le,
        List.getElem_set_self (by simp [hrevL, hdlenLt])]
    have hsum' : (dlen + 1#64).toNat + (bvDiv10Rev d0_2 d1_2).length = fullRev.length := by
      rw [hdl1]; rw [hbv, List.length_cons] at hdlSum; omega
    have hpref' :
        (revBs.set dlen.toNat (UInt8.ofNat (48 + d0_1))).take (dlen + 1#64).toNat ++
          bvDiv10Rev d0_2 d1_2 = fullRev := by
      rw [htake1, List.append_assoc]
      change revBs.take dlen.toNat ++ (UInt8.ofNat (48 + d0_1) :: bvDiv10Rev d0_2 d1_2) = fullRev
      rw [← hbv]
      exact hdlPref
    rcases hcn'' with ⟨hd1nz, rfl⟩ | ⟨hd1z, hd0nz, rfl⟩ | ⟨hd1z, hd0z, rfl⟩
    · exact hk 2#64 _ _ (by simp [hrevL]) hsum' hpref' (Or.inl ⟨rfl, hd1nz⟩) hms
    · exact hk 1#64 _ _ (by simp [hrevL]) hsum' hpref' (Or.inr (Or.inl ⟨rfl, hd1z, hd0nz⟩)) hms
    · exact hk 0#64 _ _ (by simp [hrevL]) hsum' hpref' (Or.inr (Or.inr ⟨rfl, hd0z, hd1z⟩)) hms
  · intro Jt hJt
    t_wp_unfold
    have hdlen_ult : BitVec.ult dlen (20 * 2#64) = true := by
      simp only [BitVec.ult, decide_eq_true_eq]
      rw [show (20 * 2#64 : BitVec 64).toNat = 40 from by decide]
      exact hdlenLt
    refine ⟨fun _ => ?_, fun hf => absurd hdlen_ult (by rw [hf]; decide)⟩
    have htrunc : BitVec.truncate 8 (48#64 + BitVec.ofNat 64 d0_1) =
        BitVec.ofNat 8 (48 + d0_1) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hm_r :
        (bytes (rev + 24#64) revBs ⋆
          (array64 (tmp + 16#64) [d0_2, d1_2] ⋆
            twoLimbTail rt rev tmp st3 objs' 0#64 R)) m := sep_cast hm (by ac_rfl)
    have hst := r2_c0_store_bytes_bv (a := rev + 24#64) (i := dlen)
      (BitVec.truncate 8 (48#64 + BitVec.ofNat 64 d0_1)) hm_r
      (by rw [hrevL]; exact hdlenLt) (by rw [hrevL]; decide)
    rw [show (24 : BitVec 64) = 24#64 from rfl]
    refine ⟨hst.1, ?_⟩
    have hset_eq : UInt8.ofNat (BitVec.truncate 8 (48#64 + BitVec.ofNat 64 d0_1)).toNat =
        UInt8.ofNat (48 + d0_1) := by
      rw [htrunc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hset_eq] at hst
    exact hJt (dlen + 1#64, curCn, ()) _ ⟨rfl, rfl, sep_cast hst.2 (by ac_rfl)⟩
private def divStepExpr2 (tmp rev lim dlen curCn : BitVec 64)
    (after : Tup Val [i64, i64] → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i64, i64]])
    (fun Js_1 =>
      Blocks.cons
        (fun p =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide),
              args := (Arg.var p.snd.fst, Arg.imm 0, ()) }
            fun p_18 =>
            Expr.jnz (Arg.var p_18.fst)
              (divLimbStepExpr tmp p.fst p.snd.fst
                (fun r => Expr.jump Js_1.fst (Arg.var r.fst, Arg.var r.snd.fst, ())))
              (divJoinExpr tmp rev dlen curCn lim p.fst after))
        Blocks.nil)
    fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0, Arg.var curCn, ())
private theorem divStepExpr2_loop_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {tmp rev lim dlen curCn : BitVec 64} {m : Mem 64}
    {after : Tup Val [i64, i64] → Expr Val Cont [i64]}
    (Inv : BitVec 64 → BitVec 64 → Mem 64 → Prop)
    (μ : BitVec 64 → BitVec 64 → Mem 64 → Nat)
    (hInit : Inv 0#64 curCn m)
    (hStep : ∀ (remBv j : BitVec 64) (mi : Mem 64)
        (cont : Tup Val [i64, i64] → Expr Val Cont [i64]),
      Inv remBv j mi →
      (∀ (remBv' j' : BitVec 64) (m' : Mem 64),
        μ remBv' j' m' < μ remBv j mi → Inv remBv' j' m' →
        wp Γ Q X (cont (remBv', j', ())) m') →
      (BitVec.ult 0#64 j = true →
        wp Γ Q X (divLimbStepExpr tmp remBv j cont) mi) ∧
      (BitVec.ult 0#64 j = false →
        wp Γ Q X (divJoinExpr tmp rev dlen curCn lim remBv after) mi)) :
    wp Γ Q X (divStepExpr2 tmp rev lim dlen curCn after) m := by
  unfold divStepExpr2
  refine wp_loop_inv (Γ := Γ) (fun (remBv, j, ()) mi => Inv remBv j mi)
    (fun (remBv, j, ()) mi => μ remBv j mi) ?_ ?_
  · intro Ji hJi
    dsimp only
    rw [wp_jump]
    dsimp only [vals, Arg.val]
    exact hJi (0#64, curCn, ()) m hInit
  · rintro Ji ⟨remBv, j, ⟨⟩⟩ mi hjin hRecIn
    rw [blocks_get_here]
    dsimp only
    rw [wp_ugt0_jnz]
    refine hStep remBv j mi
      (fun r => Expr.jump Ji (Arg.var r.fst, Arg.var r.snd.fst, ())) hjin ?_
    intro remBv' j' m' hlt hinv'
    dsimp only
    rw [wp_jump]
    dsimp only [vals, Arg.val]
    exact hRecIn (remBv', j', ()) m' hlt hinv'
private theorem twoLimb_divStep_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {rt tmp rev dlen curCn : BitVec 64} {st3 : RtC0State} {objs' : List LcnfObj}
    {cw0 cw1 : BitVec 64} {revBs fullRev : List UInt8} {m : Mem 64}
    {after : Tup Val [i64, i64] → Expr Val Cont [i64]}
    (hrevL : revBs.length = 40)
    (hdlSum : dlen.toNat + (bvDiv10Rev cw0 cw1).length = fullRev.length)
    (hdlPref : revBs.take dlen.toNat ++ bvDiv10Rev cw0 cw1 = fullRev)
    (hfullLen : fullRev.length < 40)
    (hcn : (curCn = 2#64 ∧ cw1 ≠ 0#64) ∨ (curCn = 1#64 ∧ cw1 = 0#64 ∧ cw0 ≠ 0#64))
    (hmk : (array64 (tmp + 16#64) [cw0, cw1] ⋆
      (bytes (rev + 24#64) revBs ⋆ twoLimbTail rt rev tmp st3 objs' 0#64 R)) m)
    (hk : ∀ (cw0' cw1' cn'' : BitVec 64) (revBs' : List UInt8) (mk' : Mem 64),
      revBs'.length = 40 →
      (dlen + 1#64).toNat + (bvDiv10Rev cw0' cw1').length = fullRev.length →
      revBs'.take (dlen + 1#64).toNat ++ bvDiv10Rev cw0' cw1' = fullRev →
      ((cn'' = 2#64 ∧ cw1' ≠ 0#64) ∨
        (cn'' = 1#64 ∧ cw1' = 0#64 ∧ cw0' ≠ 0#64) ∨
        (cn'' = 0#64 ∧ cw0' = 0#64 ∧ cw1' = 0#64)) →
      (array64 (tmp + 16#64) [cw0', cw1'] ⋆
        (bytes (rev + 24#64) revBs' ⋆ twoLimbTail rt rev tmp st3 objs' 0#64 R)) mk' →
      wp loopRtEnv Q X (after (dlen + 1#64, cn'', ())) mk') :
    wp loopRtEnv Q X (divStepExpr2 tmp rev (20 * 2#64) dlen curCn after) m := by
  let d1 := div10Limb 0 cw1
  let d0 := div10Limb d1.1 cw0
  have hd1_val := div10Limb_eq (rem := 0) cw1 (by decide)
  have hd0_val := div10Limb_eq (rem := d1.1) cw0 hd1_val.2
  have hne_cw : cw0.toNat + 2 ^ 64 * cw1.toNat ≠ 0 := by
    rcases hcn with ⟨_, h1⟩ | ⟨_, _, h0⟩
    · have hp : cw1.toNat ≠ 0 := fun hz => h1 (BitVec.eq_of_toNat_eq hz)
      omega
    · have hp : cw0.toNat ≠ 0 := fun hz => h0 (BitVec.eq_of_toNat_eq hz)
      omega
  have hbv_cw := bvDiv10Rev_ne hne_cw
  have hdlen_lt : dlen.toNat < 40 := by
    have hp := bvDiv10Rev_len_pos hne_cw
    omega
  refine divStepExpr2_loop_wp (Γ := loopRtEnv)
    (fun remBv j mi =>
      (j = 2#64 ∧ remBv = 0#64 ∧ curCn = 2#64 ∧
        (array64 (tmp + 16#64) [cw0, cw1] ⋆
          (bytes (rev + 24#64) revBs ⋆ twoLimbTail rt rev tmp st3 objs' 0#64 R)) mi) ∨
      (j = 1#64 ∧ remBv = BitVec.ofNat 64 d1.1 ∧
        (array64 (tmp + 16#64) [cw0, d1.2] ⋆
          (bytes (rev + 24#64) revBs ⋆ twoLimbTail rt rev tmp st3 objs' 0#64 R)) mi) ∨
      (j = 0#64 ∧ remBv = BitVec.ofNat 64 d0.1 ∧
        (array64 (tmp + 16#64) [d0.2, d1.2] ⋆
          (bytes (rev + 24#64) revBs ⋆ twoLimbTail rt rev tmp st3 objs' 0#64 R)) mi))
    (fun _ j _ => j.toNat) ?_ ?_
  · rcases hcn with ⟨rfl, _⟩ | ⟨rfl, rfl, _⟩
    · exact Or.inl ⟨rfl, rfl, rfl, hmk⟩
    · have hd1z : d1 = (0, 0#64) := by dsimp [d1]; exact div10Limb_zero
      refine Or.inr (Or.inl ⟨rfl, ?_, ?_⟩)
      · rw [hd1z]
      · rw [hd1z]; exact hmk
  · intro remBv j mi cont hjin hRecIn
    rcases hjin with ⟨rfl, rfl, rfl, hmi⟩ | ⟨rfl, rfl, hmi⟩ | ⟨rfl, rfl, hmi⟩
    · refine ⟨fun _ => ?_, fun hf => absurd hf (by decide)⟩
      exact twoLimb_divLimb_wp (i := 1) (remNat := 0) (by decide) rfl rfl (by decide) rfl hmi
        fun m' hm' => hRecIn (BitVec.ofNat 64 d1.1) 1#64 m' (by decide)
          (Or.inr (Or.inl ⟨rfl, rfl, hm'⟩))
    · refine ⟨fun _ => ?_, fun hf => absurd hf (by decide)⟩
      exact twoLimb_divLimb_wp (i := 0) (remNat := d1.1) (by decide) rfl rfl hd1_val.2 rfl hmi
        fun m' hm' => hRecIn (BitVec.ofNat 64 d0.1) 0#64 m' (by decide)
          (Or.inr (Or.inr ⟨rfl, rfl, hm'⟩))
    · refine ⟨fun ht => absurd ht (by decide), fun _ => ?_⟩
      have hInit : curCn = 2#64 ∨ (curCn = 1#64 ∧ d1.2 = 0#64) := by
        rcases hcn with ⟨rfl, _⟩ | ⟨rfl, rfl, _⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨rfl, by dsimp [d1]; rw [div10Limb_zero]⟩
      dsimp only [d0, d1] at hbv_cw
      exact twoLimb_divJoin_wp hrevL hdlen_lt hd0_val.2 hbv_cw hdlSum hdlPref hInit hmi
        fun cn'' revBs' mk' hrl hs' hp' hc' hm' =>
          hk d0.2 d1.2 cn'' revBs' mk' hrl hs' hp' hc' hm'
private def outerDivExpr2 (rt tmp rev cnInit lim : BitVec 64) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i64, i64]])
    (fun Js =>
      Blocks.cons
        (fun p_16 =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide),
              args := (Arg.var p_16.snd.fst, Arg.imm 0, ()) }
            fun p_17 =>
            Expr.jnz (Arg.var p_17.fst)
              (divStepExpr2 tmp rev lim p_16.fst p_16.snd.fst
                (fun q => Expr.jump Js.fst (Arg.var q.fst, Arg.var q.snd.fst, ())))
              (Expr.let_
                { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var rev, Arg.imm 8, ()) } fun p_18 =>
              Expr.store (Arg.var p_16.fst) (Arg.var p_18.fst)
                (revFreeExpr2 rt tmp rev p_16.fst)))
        Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, Arg.var cnInit, ())
private theorem outerDivExpr2_loop_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {rt tmp rev cnInit lim : BitVec 64} {m : Mem 64}
    (Inv : BitVec 64 → BitVec 64 → Mem 64 → Prop)
    (μ : BitVec 64 → BitVec 64 → Mem 64 → Nat)
    (hInit : Inv 0#64 cnInit m)
    (hStep : ∀ (dlen curCn : BitVec 64) (mk : Mem 64)
        (cont : Tup Val [i64, i64] → Expr Val Cont [i64]),
      Inv dlen curCn mk →
      (∀ (dlen' cn'' : BitVec 64) (mk' : Mem 64),
        μ dlen' cn'' mk' < μ dlen curCn mk → Inv dlen' cn'' mk' →
        wp Γ Q X (cont (dlen', cn'', ())) mk') →
      (BitVec.ult 0#64 curCn = true →
        wp Γ Q X (divStepExpr2 tmp rev lim dlen curCn cont) mk) ∧
      (BitVec.ult 0#64 curCn = false →
        storeOk mk i64 (rev + 8#64) ∧
        wp Γ Q X (revFreeExpr2 rt tmp rev dlen) (storeMem mk i64 (rev + 8#64) dlen))) :
    wp Γ Q X (outerDivExpr2 rt tmp rev cnInit lim) m := by
  unfold outerDivExpr2
  refine wp_loop_inv (Γ := Γ) (fun (dlen, curCn, ()) mk => Inv dlen curCn mk)
    (fun (dlen, curCn, ()) mk => μ dlen curCn mk) ?_ ?_
  · intro Jo hJo
    dsimp only
    rw [wp_jump]
    dsimp only [vals, Arg.val]
    exact hJo (0#64, cnInit, ()) m hInit
  · rintro Jo ⟨dlen, curCn, ⟨⟩⟩ mk hinv hRec
    rw [blocks_get_here]
    dsimp only
    rw [wp_ugt0_jnz]
    have hs := hStep dlen curCn mk
      (fun q => Expr.jump Jo (Arg.var q.fst, Arg.var q.snd.fst, ())) hinv
      (fun dlen' cn'' mk' hlt hinv' => by
        dsimp only
        rw [wp_jump]
        dsimp only [vals, Arg.val]
        exact hRec (dlen', cn'', ()) mk' hlt hinv')
    refine ⟨hs.1, fun hf => ?_⟩
    rw [wp_add_imm_store]
    exact hs.2 hf
private theorem twoLimb_outerDiv_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {rt tmp rev : BitVec 64} {st3 : RtC0State} {objs' : List LcnfObj}
    {w0 w1 : BitVec 64} {bs0 : List UInt8} {m : Mem 64}
    (htmp0 : tmp ≠ 0#64) (htmp8 : tmp.toNat % 8 = 0)
    (hrev0 : rev ≠ 0#64) (hrev8 : rev.toNat % 8 = 0)
    (hw1Ne : w1 ≠ 0#64) (hbs0Len : bs0.length = 40)
    (hst3Rem : strAllocBytes 41 ≤ st3.rem)
    (hm : (array64 (tmp + 16#64) [w0, w1] ⋆
      (bytes (rev + 24#64) bs0 ⋆ twoLimbTail rt rev tmp st3 objs' 0#64 R)) m)
    (hk : ∀ (s : BitVec 64) (st' : RtC0State) (m' : Mem 64),
      s ≠ 0#64 → s.toNat % 8 = 0 → st'.PreservesMeta st3 → st'.rem ≤ st3.rem →
      let dec := natToDecimalBytes (w0.toNat + 2 ^ 64 * w1.toNat)
      let sObj := mkStrObj s 1#32 (dec.length + 1) dec dec.length
      StrCanon sObj → (rtC0Inv rt st' ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs' ⋆ R) m' → Q (s, ()) m') :
    wp loopRtEnv Q X (outerDivExpr2 rt tmp rev 2#64 (20 * 2#64)) m := by
  have hvalNe0 : w0.toNat + 2 ^ 64 * w1.toNat ≠ 0 := by
    have hp : w1.toNat ≠ 0 := fun h0 => hw1Ne (BitVec.eq_of_toNat_eq h0)
    omega
  let fullRev := bvDiv10Rev w0 w1
  have hfullRevLen : fullRev.length < 40 := by
    dsimp only [fullRev]; rw [bvDiv10Rev_eq_natDigitsRev]; exact natDigitsRev_len_lt_40
  refine outerDivExpr2_loop_wp (Γ := loopRtEnv)
    (fun dlen curCn mk =>
      ∃ (cw0 cw1 : BitVec 64) (revBs : List UInt8),
        revBs.length = 40 ∧
        dlen.toNat + (bvDiv10Rev cw0 cw1).length = fullRev.length ∧
        revBs.take dlen.toNat ++ bvDiv10Rev cw0 cw1 = fullRev ∧
        (((curCn = 2#64 ∧ cw1 ≠ 0#64) ∨
          (curCn = 1#64 ∧ cw1 = 0#64 ∧ cw0 ≠ 0#64)) ∨
          (curCn = 0#64 ∧ cw0 = 0#64 ∧ cw1 = 0#64)) ∧
        (array64 (tmp + 16#64) [cw0, cw1] ⋆
          (bytes (rev + 24#64) revBs ⋆ twoLimbTail rt rev tmp st3 objs' 0#64 R)) mk)
    (fun dlen _ _ => fullRev.length - dlen.toNat) ?_ ?_
  · exact ⟨w0, w1, bs0, hbs0Len,
      by rw [BitVec.toNat_zero, Nat.zero_add],
      by rw [BitVec.toNat_zero, List.take_zero, List.nil_append],
      Or.inl (Or.inl ⟨rfl, hw1Ne⟩), hm⟩
  · rintro dlen curCn mk cont ⟨cw0, cw1, revBs, hrevL, hdlSum, hdlPref, hcnSt, hmk⟩ hRec
    rcases hcnSt with hstep | ⟨rfl, rfl, rfl⟩
    · have hgt : BitVec.ult 0#64 curCn = true := by
        rcases hstep with ⟨rfl, _⟩ | ⟨rfl, _, _⟩ <;> decide
      refine ⟨fun _ => ?_, fun hf => absurd hgt (by rw [hf]; decide)⟩
      have hne_cw : cw0.toNat + 2 ^ 64 * cw1.toNat ≠ 0 := by
        rcases hstep with ⟨_, h1⟩ | ⟨_, _, h0⟩
        · have hp : cw1.toNat ≠ 0 := fun hz => h1 (BitVec.eq_of_toNat_eq hz)
          omega
        · have hp : cw0.toNat ≠ 0 := fun hz => h0 (BitVec.eq_of_toNat_eq hz)
          omega
      have hdlen_lt : dlen.toNat < 40 := by
        have hp := bvDiv10Rev_len_pos hne_cw
        omega
      have hdl1 : (dlen + 1#64).toNat = dlen.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      refine twoLimb_divStep_wp hrevL hdlSum hdlPref hfullRevLen hstep hmk
        fun cw0' cw1' cn'' revBs' mk' hrl hs' hp' hc' hm' => ?_
      refine hRec (dlen + 1#64) cn'' mk' (by rw [hdl1]; omega)
        ⟨cw0', cw1', revBs', hrl, hs', hp', ?_, hm'⟩
      rcases hc' with h2 | h1 | h0
      · exact Or.inl (Or.inl h2)
      · exact Or.inl (Or.inr h1)
      · exact Or.inr h0
    · refine ⟨fun ht => absurd ht (by decide), fun _ => ?_⟩
      rw [bvDiv10Rev_zero, List.length_nil, Nat.add_zero] at hdlSum
      rw [bvDiv10Rev_zero, List.append_nil] at hdlPref
      have hfullPos : 1 ≤ fullRev.length := by
        dsimp only [fullRev]; exact bvDiv10Rev_len_pos hvalNe0
      have hdec_eq :
          natToDecimalBytes (w0.toNat + 2 ^ 64 * w1.toNat) = (revBs.take dlen.toNat).reverse := by
        rw [hdlPref]
        unfold natToDecimalBytes
        rw [ite_eq_right hvalNe0]
        dsimp only [fullRev]
        rw [bvDiv10Rev_eq_natDigitsRev]
      have hdl_pos : 1 ≤ dlen.toNat := by omega
      have hdl_lt40 : dlen.toNat < 40 := by omega
      unfold twoLimbTail at hmk
      have hst_len := store_cell64 dlen (a := rev + 8#64)
        (R := rtC0Inv rt st3 ⋆ cell64 rev baHeaderWord ⋆ cell64 (rev + 16#64) 40#64 ⋆
          bytes (rev + 24#64) revBs ⋆ array64 (tmp + 16#64) [0#64, 0#64] ⋆ lcnfHeap objs' ⋆
          cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆ R)
        (sep_cast hmk (by ac_rfl))
      refine ⟨hst_len.1, ?_⟩
      have hmk_rf :
          (array64 (tmp + 16#64) [0#64, 0#64] ⋆
            (bytes (rev + 24#64) revBs ⋆ twoLimbTail rt rev tmp st3 objs' dlen R))
            (storeMem mk i64 (rev + 8#64) dlen) := by
        unfold twoLimbTail; exact sep_cast hst_len.2 (by ac_rfl)
      exact twoLimb_revFree_wp htmp0 htmp8 hrev0 hrev8 hrevL hdl_pos hdl_lt40 hst3Rem hdec_eq
        hmk_rf hk
theorem lcnf_nat_to_str_two_limb_wp (xs : Tup Val [i64, i64]) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) :
    loopNatToStr2Spec xs m Q X → Func.wp loopRtEnv lcnf_nat_to_str.body xs m Q X := by
  rcases xs with ⟨rt, n, ⟨⟩⟩
  dsimp only [Val] at rt n
  rintro ⟨st, nObj, objs, val, R, hnBit, hnMem, hnAddr, hcanon, hlen2, hwf, hrc1, hrem, hm, hk⟩
  obtain ⟨w0, w1, hwEq⟩ := list_two_elim hlen2
  have hw1Ne : w1 ≠ 0#64 := by
    have hl := hcanon.2.2.2.2.2.2.1
    simpa [hwEq] using hl
  have hvalEq : val = w0.toNat + 2 ^ 64 * w1.toNat := by
    have hv := hcanon.2.2.2.2.2.2.2.1
    rw [hwEq] at hv
    simpa [limbsVal] using hv.symm
  have hvalNe0 : w0.toNat + 2 ^ 64 * w1.toNat ≠ 0 := by
    have hp : 2 ^ 63 ≤ val := hcanon.2.2.2.2.2.2.2.2
    omega
  have hnArr2 : nObj.arrSize = 2 := by rw [hcanon.2.2.2.1, hlen2]
  have hcapMax : nObj.cap ≤ mpzMaxLimbs := by
    have hwf_n := hcanon.1
    unfold LcnfObj.Wf at hwf_n
    simp only [hcanon.2.1, mpzTag, closureTag, arrayTag,
      sarrayTag, stringTag, show (250 = 245) = False by decide,
      show (250 = 246) = False by decide, show (250 = 248) = False by decide,
      show (250 = 249) = False by decide, ite_false, ite_true] at hwf_n
    exact hwf_n.2.2.2.2.2.2.2.2.2.2.1
  dsimp only [mpzMaxLimbs] at hcapMax
  have hmetaShift : nObj.mpzMeta >>> 32 = 2#64 := by
    unfold LcnfObj.mpzMeta
    rw [hnArr2]
    apply BitVec.eq_of_toNat_eq
    have hdisj : ((BitVec.ofNat 64 nObj.cap) &&& (BitVec.ofNat 64 2 <<< 32)) = 0#64 := by
      ext i hi
      simp only [BitVec.getElem_and, BitVec.getElem_zero, BitVec.getElem_shiftLeft,
        Bool.and_eq_false_iff]
      by_cases h32 : i < 32
      · right; simp [h32]
      · left
        rw [← BitVec.getLsbD_eq_getElem, ← BitVec.testBit_toNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
        exact Nat.testBit_lt_two_pow (by
          have hp : 2 ^ 32 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
          omega)
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      ← BitVec.add_eq_or_of_and_eq_zero _ _ hdisj, BitVec.toNat_add, BitVec.toNat_shiftLeft,
      Nat.shiftLeft_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      show (BitVec.ofNat 64 2 : BitVec 64).toNat = 2 from rfl]
    rw [Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  obtain ⟨idxObj, hidxLt, hgetObj⟩ := List.mem_iff_getElem.mp hnMem
  have hfocus := lcnfHeap_focus objs hidxLt
  rw [hgetObj] at hfocus
  have hmpzTagB : nObj.tag = mpzTag := hcanon.2.1
  dsimp only [Func.wp, Ty.hasFloat, List.any, lcnf_nat_to_str, lcnf_nat_to_str_body]
  try rw [if_neg (by decide)]
  t_wp_unfold
  refine ⟨fun h => absurd hnBit h, fun _ => ?_⟩
  have hm_unfold :
      (array64 (n + 16#64) [w0, w1] ⋆
        (cell64 n nObj.header ⋆ cell64 (n + 8#64) nObj.mpzMeta ⋆
          lcnfHeap (List.take idxObj objs) ⋆
          lcnfHeap (List.drop (idxObj + 1) objs) ⋆
          rtC0Inv rt st ⋆ R)) m := by
    rw [hfocus, loop_mpzObjMem_eq hmpzTagB, hnAddr, hwEq] at hm
    exact sep_cast hm (by ac_rfl)
  have hldMeta : loadVal m i64 (n + 8#64) = some nObj.mpzMeta := by
    have hm_meta :
        (cell64 (n + 8#64) nObj.mpzMeta ⋆
          (array64 (n + 16#64) [w0, w1] ⋆ cell64 n nObj.header ⋆
            lcnfHeap (List.take idxObj objs) ⋆
            lcnfHeap (List.drop (idxObj + 1) objs) ⋆
            rtC0Inv rt st ⋆ R)) m := sep_cast hm_unfold (by ac_rfl)
    exact loadVal_cell64 hm_meta
  refine ⟨nObj.mpzMeta, by simpa using hldMeta, ?_⟩
  rw [show (BitVec.signExtend 64 (32 : BitVec 32)).toNat % 64 = 32 from by decide, hmetaShift]
  refine twoLimb_trim_wp (Or.inl rfl) hm_unfold fun cn' _ hcn' => ?_
  rcases hcn' with ⟨_, rfl⟩ | ⟨h1z, _⟩ | ⟨h1z, _⟩
  · t_wp_unfold
    refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
    refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
    apply wp_call_step
    dsimp only [vals, Arg.val]
    apply rtC0CoreEnv_le_loopRtEnv
    apply rtR2bEnv_le_rtC0CoreEnv
    apply rtR2bEnv_r2b_alloc_mpz
    dsimp only [r2bAllocMpzSpec, vals, Arg.val]
    rw [ite_eq_left (by decide : (2#64 : BitVec 64).toNat ≤ (2#64 : BitVec 64).toNat ∧
      (2#64 : BitVec 64).toNat ≤ 33554429)]
    refine ⟨st, lcnfHeap objs ⋆ R,
      Or.inr (by rw [show (2#64 : BitVec 64).toNat = 2 from rfl]; omega),
      sep_cast hm (by ac_rfl), ?_⟩
    intro tmp st1 m2 htmp0 htmp8 hpr1 hrem1 hrem1Lo hm2
    rw [show (2#64 : BitVec 64).toNat = 2 from rfl] at hm2 hrem1Lo
    have hm2_reg :
        (region (tmp + 16#64) (8 * 2) ⋆
          (rtC0Inv rt st1 ⋆ cell64 tmp mpzHeaderWord ⋆
            cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆
            lcnfHeap objs ⋆ R)) m2 := sep_cast hm2 (by ac_rfl)
    obtain ⟨zXs, hzLen, hm2_arr⟩ := region_to_array64_sep (by decide) hm2_reg
    obtain ⟨z0, z1, hzEq⟩ := list_two_elim hzLen
    rw [hzEq] at hm2_arr
    have hm_copy0 :
        (array64 (tmp + 16#64) [z0, z1] ⋆
          (array64 (n + 16#64) [w0, w1] ⋆
            cell64 n nObj.header ⋆ cell64 (n + 8#64) nObj.mpzMeta ⋆
            lcnfHeap (List.take idxObj objs) ⋆
            lcnfHeap (List.drop (idxObj + 1) objs) ⋆
            rtC0Inv rt st1 ⋆ cell64 tmp mpzHeaderWord ⋆
            cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆ R)) m2 := by
      rw [hfocus, loop_mpzObjMem_eq hmpzTagB, hnAddr, hwEq] at hm2_arr
      exact sep_cast hm2_arr (by ac_rfl)
    refine wp_loop_inv (Γ := loopRtEnv)
      (fun (i, ()) mk =>
        ∃ zs : List (BitVec 64),
          ((i = 0#64 ∧ zs = [z0, z1]) ∨ (i = 1#64 ∧ zs = [w0, z1]) ∨
            (i = 2#64 ∧ zs = [w0, w1])) ∧
          (array64 (tmp + 16#64) zs ⋆
            (array64 (n + 16#64) [w0, w1] ⋆
              cell64 n nObj.header ⋆ cell64 (n + 8#64) nObj.mpzMeta ⋆
              lcnfHeap (List.take idxObj objs) ⋆
              lcnfHeap (List.drop (idxObj + 1) objs) ⋆
              rtC0Inv rt st1 ⋆ cell64 tmp mpzHeaderWord ⋆
              cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆ R)) mk)
      (fun (i, ()) _ => 2 - i.toNat) ?_ ?_
    · intro Jc hJc
      exact hJc (0#64, ()) m2 ⟨[z0, z1], Or.inl ⟨rfl, rfl⟩, hm_copy0⟩
    · rintro Jc ⟨i, ⟨⟩⟩ mk ⟨zs, hcase, hmk⟩ hRec
      t_wp_unfold
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨fun _ => ?_, fun hf => absurd hf (by decide)⟩
        have hmk_n :
            (array64 (n + 16#64) [w0, w1] ⋆
              (array64 (tmp + 16#64) [z0, z1] ⋆
                cell64 n nObj.header ⋆ cell64 (n + 8#64) nObj.mpzMeta ⋆
                lcnfHeap (List.take idxObj objs) ⋆
                lcnfHeap (List.drop (idxObj + 1) objs) ⋆
                rtC0Inv rt st1 ⋆ cell64 tmp mpzHeaderWord ⋆
                cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆ R)) mk := sep_cast hmk (by ac_rfl)
        have hld0 : loadVal mk i64 (n + 16#64 + 8#64 * 0#64) = some w0 := by
          rw [bv_add2_eq (c1 := 16#64) (c2 := BitVec.ofNat 64 (8 * 0)) (by decide)]
          exact loadVal_array64 (i := 0) (by simp) hmk_n
        refine ⟨w0, by simpa using hld0, ?_⟩
        have hst := store_array64 (a := tmp + 16#64) (i := 0) w0 (by simp) hmk
        rw [bv_add2_eq (c1 := 16#64) (c2 := BitVec.ofNat 64 (8 * 0)) (by decide)]
        refine ⟨hst.1, ?_⟩
        exact hRec (1#64, ()) _ (by decide)
          ⟨[w0, z1], Or.inr (Or.inl ⟨rfl, rfl⟩), by simpa using hst.2⟩
      · refine ⟨fun _ => ?_, fun hf => absurd hf (by decide)⟩
        have hmk_n :
            (array64 (n + 16#64) [w0, w1] ⋆
              (array64 (tmp + 16#64) [w0, z1] ⋆
                cell64 n nObj.header ⋆ cell64 (n + 8#64) nObj.mpzMeta ⋆
                lcnfHeap (List.take idxObj objs) ⋆
                lcnfHeap (List.drop (idxObj + 1) objs) ⋆
                rtC0Inv rt st1 ⋆ cell64 tmp mpzHeaderWord ⋆
                cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆ R)) mk := sep_cast hmk (by ac_rfl)
        have hld1 : loadVal mk i64 (n + 16#64 + 8#64 * 1#64) = some w1 := by
          rw [bv_add2_eq (c1 := 16#64) (c2 := BitVec.ofNat 64 (8 * 1)) (by decide)]
          exact loadVal_array64 (i := 1) (by simp) hmk_n
        refine ⟨w1, by simpa using hld1, ?_⟩
        have hst := store_array64 (a := tmp + 16#64) (i := 1) w1 (by simp) hmk
        rw [bv_add2_eq (c1 := 16#64) (c2 := BitVec.ofNat 64 (8 * 1)) (by decide)]
        refine ⟨hst.1, ?_⟩
        exact hRec (2#64, ()) _ (by decide)
          ⟨[w0, w1], Or.inr (Or.inr ⟨rfl, rfl⟩), by simpa using hst.2⟩
      · refine ⟨fun ht => absurd ht (by decide), fun _ => ?_⟩
        have hmk_dec :
            (rtC0Inv rt st1 ⋆ lcnfHeap objs ⋆
              (cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆
                array64 (tmp + 16#64) [w0, w1] ⋆ R)) mk := by
          rw [hfocus, loop_mpzObjMem_eq hmpzTagB, hnAddr, hwEq]
          exact sep_cast hmk (by ac_rfl)
        apply wp_call_step
        dsimp only [vals, Arg.val]
        apply rtC0CoreEnv_le_loopRtEnv
        apply rtR2bEnv_le_rtC0CoreEnv
        apply rtR2bEnv_r2_dec_obj
        dsimp only [r2DecObjSpec, vals, Arg.val]
        have hnoNull : ¬ (n = 0#64 ∨ n &&& 1#64 ≠ 0#64) := by
          intro h
          rcases h with rfl | h
          · exact (hwf nObj hnMem).1 hnAddr
          · exact h hnBit
        rw [ite_eq_right hnoNull]
        have hworkEq : st1.workCap = st.workCap := by
          simpa [RtC0State.workCap, RtC0State.workCap] using
            congrArg BitVec.toNat hpr1.2.2.2.2.2.1.symm
        refine ⟨st1, objs, _,
          ⟨nObj, hnMem, hnAddr, fun hrc => by
            obtain ⟨hwc, hcl, hrcS⟩ := hrc1 hrc
            refine ⟨by rw [hworkEq]; simp [hwc], hcl,
              hrcS⟩⟩,
          hwf,
          hmk_dec, ?_⟩
        intro st2 objs' m3 hpr2 hrem2 hdec hm3
        t_wp_unfold
        apply wp_call_step
        dsimp only [vals, Arg.val]
        apply rtC0CoreEnv_le_loopRtEnv
        apply rtR2bEnv_le_rtC0CoreEnv
        apply rtR2bEnv_r2_alloc_sarray
        dsimp only [r2AllocSarraySpec, vals, Arg.val]
        have h40le : (0 : BitVec 64).toNat ≤ (20 * 2#64 : BitVec 64).toNat ∧
            (20 * 2#64 : BitVec 64).toNat ≤ baMaxCap := by dsimp only [baMaxCap]; decide
        split
        case isFalse hc => exact absurd h40le hc
        rw [show baAllocBytes = sarrayAllocBytes from rfl]
        have hs40_eq : sarrayAllocBytes (20 * 2#64 : BitVec 64).toNat = sarrayAllocBytes 40 := by
          rw [show (20 * 2#64 : BitVec 64).toNat = 40 from by decide]
        have hst2_rem : sarrayAllocBytes 40 + strAllocBytes 41 ≤ st2.rem := by
          have : mpzAllocBytes 2 = 32 := rfl
          omega
        refine ⟨st2,
          (lcnfHeap objs' ⋆ cell64 tmp mpzHeaderWord ⋆
            cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆ array64 (tmp + 16#64) [w0, w1] ⋆ R),
          Or.inr (by rw [hs40_eq]; exact Nat.le_trans (Nat.le_add_right _ _) hst2_rem),
          sep_cast hm3 (by ac_rfl), ?_⟩
        intro rev st3 m4 hrev0 hrev8 hpr3 hrem3 hrem3Lo hm4
        rw [hs40_eq] at hrem3Lo hm4
        have hst3_rem : strAllocBytes 41 ≤ st3.rem := by omega
        have hm4_reg :
            (region (rev + 24#64) 40 ⋆
              (rtC0Inv rt st3 ⋆ cell64 rev baHeaderWord ⋆ cell64 (rev + 8#64) 0#64 ⋆
                cell64 (rev + 16#64) 40#64 ⋆ lcnfHeap objs' ⋆ cell64 tmp mpzHeaderWord ⋆
                cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆
                array64 (tmp + 16#64) [w0, w1] ⋆ R)) m4 := by
          have h40m : sarrayAllocBytes 40 - 24 = 40 := rfl
          rw [h40m, show (20 * 2#64 : BitVec 64) = 40#64 from rfl] at hm4
          exact sep_cast hm4 (by ac_rfl)
        obtain ⟨bs0, hbs0Len, hm4_bs⟩ :=
          region_pop_bytes (k := 40) (Nat.le_refl _) (by decide) hm4_reg
        rw [Nat.sub_self, region_zero, sep_emp] at hm4_bs
        have hm4_tail :
            (array64 (tmp + 16#64) [w0, w1] ⋆
              (bytes (rev + 24#64) bs0 ⋆ twoLimbTail rt rev tmp st3 objs' 0#64 R)) m4 := by
          unfold twoLimbTail; exact sep_cast hm4_bs (by ac_rfl)
        exact twoLimb_outerDiv_wp htmp0 htmp8 hrev0 hrev8 hw1Ne hbs0Len hst3_rem hm4_tail
          fun s st' m' hs0 hs8 hpr' hrem' hcan hm' => by
            rw [← hvalEq] at hcan hm'
            exact hk s st' objs' m' hs0 hs8
              (hpr1.trans (hpr2.trans (hpr3.trans hpr'))) (by omega) hcan hdec hm'
  · exact absurd h1z hw1Ne
  · exact absurd h1z hw1Ne


end LeanQbe.T.LeanLCNF
