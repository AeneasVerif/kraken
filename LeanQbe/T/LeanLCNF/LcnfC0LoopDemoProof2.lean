module

public import LeanQbe.T.LeanLCNF.LcnfC0LoopDemoProof1

/-!
# Dual-Arch WP Proof for `FactLoop` (`LcnfC0LoopDemoProof2`)

Section 3a (part 1): 2-limb base-10 arithmetic (`div10Limb`, `bvDiv10Rev`),
`twoLimb_trim_wp`, and `twoLimb_revFree_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T LeanQbe.T.Frontend.C0 LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Std Std.ExtHashMap
open scoped LeanQbe.T.ProofUtil

private theorem mem_map_name_ne {s : Sym} {fns : List Fn} (h : s ∉ fns.map Fn.name)
    {fn : Fn} (hmem : fn ∈ fns) : fn.name ≠ s :=
  fun heq => h (heq ▸ List.mem_map_of_mem hmem)
@[expose] def div10Limb (rem : Nat) (w : BitVec 64) : Nat × BitVec 64 :=
  let hi := rem * 2 ^ 32 + w.toNat / 2 ^ 32
  let rh := hi % 10
  let lo := rh * 2 ^ 32 + w.toNat % 2 ^ 32
  (lo % 10, BitVec.ofNat 64 ((hi / 10) * 2 ^ 32 + lo / 10))
theorem div10Limb_zero : div10Limb 0 0#64 = (0, 0#64) := rfl
theorem div10Limb_eq {rem : Nat} (w : BitVec 64) (hrem : rem < 10) :
    (div10Limb rem w).2.toNat * 10 + (div10Limb rem w).1 = rem * 2 ^ 64 + w.toNat ∧
      (div10Limb rem w).1 < 10 := by
  dsimp only [div10Limb]
  have hw := w.isLt
  have hdivw := Nat.div_add_mod w.toNat (2 ^ 32)
  have h1 : (rem * 2 ^ 32 + w.toNat / 2 ^ 32) / 10 < 2 ^ 32 := by
    have hhi_lt : rem * 2 ^ 32 + w.toNat / 2 ^ 32 < 10 * 2 ^ 32 := by omega
    exact Nat.div_lt_of_lt_mul hhi_lt
  have hdiv1 := Nat.div_add_mod (rem * 2 ^ 32 + w.toNat / 2 ^ 32) 10
  have h2 : ((rem * 2 ^ 32 + w.toNat / 2 ^ 32) % 10 * 2 ^ 32 + w.toNat % 2 ^ 32) / 10 < 2 ^ 32 := by
    have hlo_lt :
        (rem * 2 ^ 32 + w.toNat / 2 ^ 32) % 10 * 2 ^ 32 + w.toNat % 2 ^ 32 < 10 * 2 ^ 32 := by
      have hm1 : (rem * 2 ^ 32 + w.toNat / 2 ^ 32) % 10 < 10 := Nat.mod_lt _ (by decide)
      have hm2 : w.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
      omega
    exact Nat.div_lt_of_lt_mul hlo_lt
  have hlt64 :
      ((rem * 2 ^ 32 + w.toNat / 2 ^ 32) / 10) * 2 ^ 32 +
        ((rem * 2 ^ 32 + w.toNat / 2 ^ 32) % 10 * 2 ^ 32 + w.toNat % 2 ^ 32) / 10 < 2 ^ 64 := by
    omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
  have hdiv2 := Nat.div_add_mod
    ((rem * 2 ^ 32 + w.toNat / 2 ^ 32) % 10 * 2 ^ 32 + w.toNat % 2 ^ 32) 10
  have hm2 :
      ((rem * 2 ^ 32 + w.toNat / 2 ^ 32) % 10 * 2 ^ 32 + w.toNat % 2 ^ 32) % 10 < 10 :=
    Nat.mod_lt _ (by decide)
  omega
private theorem add_mul_2p32_lt_2p64 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    a * 2 ^ 32 + b < 2 ^ 64 := by omega
theorem div10Limb_c0 {rem : Nat} (w : BitVec 64) (hrem : rem < 10) :
    let d := div10Limb rem w
    let remBv := BitVec.ofNat 64 rem
    let hi := (remBv <<< ((BitVec.signExtend 64 (32 : BitVec 32)).toNat % 64)) |||
      (w >>> ((BitVec.signExtend 64 (32 : BitVec 32)).toNat % 64))
    let q_hi := hi / 10#64
    let r_hi := hi % 10#64
    let lo := (r_hi <<< ((BitVec.signExtend 64 (32 : BitVec 32)).toNat % 64)) |||
      (w &&& 4294967295#64)
    lo % 10#64 = BitVec.ofNat 64 d.1 ∧
      ((q_hi <<< ((BitVec.signExtend 64 (32 : BitVec 32)).toNat % 64)) ||| (lo / 10#64)) = d.2 := by
  have hs32 : (BitVec.signExtend 64 (32 : BitVec 32)).toNat % 64 = 32 := by decide
  have hw := w.isLt
  have hrem64 : (BitVec.ofNat 64 rem).toNat = rem := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hshl_disj : ∀ a b : BitVec 64, a.toNat < 2 ^ 32 → b.toNat < 2 ^ 32 →
      ((a <<< 32) ||| b).toNat = a.toNat * 2 ^ 32 + b.toNat := by
    intro a b ha hb
    have hdisj : (a <<< 32) &&& b = 0#64 := by
      ext i hi
      simp only [BitVec.getElem_and, BitVec.getElem_zero, BitVec.getElem_shiftLeft,
        Bool.and_eq_false_iff]
      by_cases h : i < 32
      · left; simp [h]
      · right
        rw [← BitVec.getLsbD_eq_getElem, ← BitVec.testBit_toNat]
        exact Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hdisj, BitVec.toNat_add, BitVec.toNat_shiftLeft,
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hw_hi : (w >>> 32).toNat = w.toNat / 2 ^ 32 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hw_lo : (w &&& 4294967295#64).toNat = w.toNat % 2 ^ 32 := by
    rw [BitVec.toNat_and, show (4294967295#64 : BitVec 64).toNat = 2 ^ 32 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  let hiBv := (BitVec.ofNat 64 rem <<< 32) ||| (w >>> 32)
  let r_hiBv := hiBv % 10#64
  let q_hiBv := hiBv / 10#64
  let loBv := (r_hiBv <<< 32) ||| (w &&& 4294967295#64)
  have hhi : hiBv.toNat = rem * 2 ^ 32 + w.toNat / 2 ^ 32 := by
    dsimp only [hiBv]
    rw [hshl_disj _ _ (by rw [hrem64]; omega) (by rw [hw_hi]; omega), hrem64, hw_hi]
  have h10 : (10#64 : BitVec 64).toNat = 10 := rfl
  have hqhi : q_hiBv.toNat = (rem * 2 ^ 32 + w.toNat / 2 ^ 32) / 10 := by
    dsimp only [q_hiBv]; rw [BitVec.toNat_udiv, hhi, h10]
  have hrhi : r_hiBv.toNat = (rem * 2 ^ 32 + w.toNat / 2 ^ 32) % 10 := by
    dsimp only [r_hiBv]; rw [BitVec.toNat_umod, hhi, h10]
  have hlo : loBv.toNat = (rem * 2 ^ 32 + w.toNat / 2 ^ 32) % 10 * 2 ^ 32 + w.toNat % 2 ^ 32 := by
    dsimp only [loBv]
    rw [hshl_disj _ _ (by rw [hrhi]; omega) (by rw [hw_lo]; omega), hrhi, hw_lo]
  have hqhi_lt : q_hiBv.toNat < 2 ^ 32 := by
    rw [hqhi]
    exact Nat.div_lt_of_lt_mul (by omega)
  have hlo_lt32 :
      ((rem * 2 ^ 32 + w.toNat / 2 ^ 32) % 10 * 2 ^ 32 + w.toNat % 2 ^ 32) < 10 * 2 ^ 32 := by
    have hm1 : (rem * 2 ^ 32 + w.toNat / 2 ^ 32) % 10 < 10 := Nat.mod_lt _ (by decide)
    have hm2 : w.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    omega
  have hqlo : (loBv / 10#64).toNat =
      ((rem * 2 ^ 32 + w.toNat / 2 ^ 32) % 10 * 2 ^ 32 + w.toNat % 2 ^ 32) / 10 := by
    rw [BitVec.toNat_udiv, hlo, h10]
  have hqlo_lt : (loBv / 10#64).toNat < 2 ^ 32 := by
    rw [hqlo]
    exact Nat.div_lt_of_lt_mul hlo_lt32
  have hsum_lt64 : q_hiBv.toNat * 2 ^ 32 + (loBv / 10#64).toNat < 2 ^ 64 :=
    add_mul_2p32_lt_2p64 hqhi_lt hqlo_lt
  rw [hqhi, hqlo] at hsum_lt64
  dsimp only
  rw [hs32]
  change loBv % 10#64 = BitVec.ofNat 64 (div10Limb rem w).1 ∧
    ((q_hiBv <<< 32) ||| (loBv / 10#64)) = (div10Limb rem w).2
  constructor
  · apply BitVec.eq_of_toNat_eq
    have hr_lt : (div10Limb rem w).1 < 10 := (div10Limb_eq w hrem).2
    dsimp only [div10Limb] at hr_lt ⊢
    rw [BitVec.toNat_umod, hlo, h10, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans hr_lt (by decide))]
  · apply BitVec.eq_of_toNat_eq
    rw [hshl_disj _ _ hqhi_lt hqlo_lt, hqhi, hqlo]
    dsimp only [div10Limb]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsum_lt64]
@[expose] def bvDiv10Rev (w0 w1 : BitVec 64) : List UInt8 :=
  if h : w0.toNat + 2 ^ 64 * w1.toNat = 0 then []
  else
    let d1 := div10Limb 0 w1
    let d0 := div10Limb d1.1 w0
    UInt8.ofNat (48 + d0.1) :: bvDiv10Rev d0.2 d1.2
termination_by w0.toNat + 2 ^ 64 * w1.toNat
decreasing_by
  have h1 := div10Limb_eq (rem := 0) w1 (by decide)
  have h0 := div10Limb_eq (rem := (div10Limb 0 w1).1) w0 h1.2
  omega
theorem bvDiv10Rev_zero : bvDiv10Rev 0#64 0#64 = [] := by
  unfold bvDiv10Rev; simp
theorem bvDiv10Rev_ne {w0 w1 : BitVec 64} (hne : w0.toNat + 2 ^ 64 * w1.toNat ≠ 0) :
    let d1 := div10Limb 0 w1
    let d0 := div10Limb d1.1 w0
    bvDiv10Rev w0 w1 = UInt8.ofNat (48 + d0.1) :: bvDiv10Rev d0.2 d1.2 := by
  dsimp only
  conv => lhs; unfold bvDiv10Rev
  rw [dite_eq_right hne]
theorem bvDiv10Rev_len_pos {w0 w1 : BitVec 64}
    (hne : w0.toNat + 2 ^ 64 * w1.toNat ≠ 0) :
    1 ≤ (bvDiv10Rev w0 w1).length := by
  rw [bvDiv10Rev_ne hne, List.length_cons]
  exact Nat.le_add_left 1 _
theorem bvDiv10Rev_eq_natDigitsRev (w0 w1 : BitVec 64) :
    bvDiv10Rev w0 w1 = natDigitsRev (w0.toNat + 2 ^ 64 * w1.toNat) := by
  let V := w0.toNat + 2 ^ 64 * w1.toNat
  have hind : ∀ N (a b : BitVec 64), a.toNat + 2 ^ 64 * b.toNat = N →
      bvDiv10Rev a b = natDigitsRev N := by
    intro N
    induction N using Nat.strongRecOn with
    | ind N ih =>
      intro a b hN
      by_cases h0 : N = 0
      · subst h0
        have ha : a.toNat + 2 ^ 64 * b.toNat = 0 := hN
        have hnz : a = 0#64 ∧ b = 0#64 := ⟨BitVec.eq_of_toNat_eq (by simp; omega),
          BitVec.eq_of_toNat_eq (by simp; omega)⟩
        rw [hnz.1, hnz.2, bvDiv10Rev_zero]
        rw [natDigitsRev.eq_def]; simp
      · have hd1 := div10Limb_eq (rem := 0) b (by decide)
        have hd0 := div10Limb_eq (rem := (div10Limb 0 b).1) a hd1.2
        have hval :
            ((div10Limb (div10Limb 0 b).1 a).2.toNat + 2 ^ 64 * (div10Limb 0 b).2.toNat) * 10 +
            (div10Limb (div10Limb 0 b).1 a).1 = N := by omega
        have hdiv :
            (div10Limb (div10Limb 0 b).1 a).2.toNat +
              2 ^ 64 * (div10Limb 0 b).2.toNat = N / 10 := by
          omega
        have hmod : (div10Limb (div10Limb 0 b).1 a).1 = N % 10 := by omega
        rw [bvDiv10Rev_ne (by omega)]
        conv => rhs; rw [natDigitsRev.eq_def]
        rw [dite_eq_right h0, hmod, ih (N / 10) (by omega) _ _ hdiv]
  exact hind V w0 w1 rfl
theorem natDigitsRev_len_lt_40 {w0 w1 : BitVec 64} :
    (natDigitsRev (w0.toNat + 2 ^ 64 * w1.toNat)).length < 40 := by
  have hpow : w0.toNat + 2 ^ 64 * w1.toNat < 10 ^ 39 := by
    have h1 := w0.isLt; have h2 := w1.isLt
    have hp : 2 ^ 128 < 10 ^ 39 := by decide
    omega
  have hl : ∀ k m : Nat, m < 10 ^ k → (natDigitsRev m).length ≤ k := by
    intro k
    induction k with
    | zero =>
      intro m hm; have : m = 0 := by omega
      subst this; rw [natDigitsRev.eq_def]; simp
    | succ k ih =>
      intro m hm
      by_cases hm0 : m = 0
      · subst hm0; rw [natDigitsRev.eq_def]; simp
      · rw [natDigitsRev.eq_def, dite_eq_right hm0]
        simp only [List.length_cons]
        have hdiv : m / 10 < 10 ^ k := Nat.div_lt_of_lt_mul (by rw [Nat.pow_succ'] at hm; omega)
        exact Nat.succ_le_succ (ih (m / 10) hdiv)
  have hle := hl 39 (w0.toNat + 2 ^ 64 * w1.toNat) hpow
  omega
theorem list_two_elim {α : Type} {xs : List α} (h : xs.length = 2) :
    ∃ a b, xs = [a, b] := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp at h
  exact ⟨a, b, rfl⟩
private theorem loop_cell64_to_region {a v : BitVec 64} {m : Mem 64} (h : cell64 a v m) :
    region a 8 m :=
  ⟨Int.toBytes 8 v.toInt, Int.toBytes_length 8 _, h.symm⟩
private theorem sarrayFreeLayout_of_parts {rev : BitVec 64} {bs : List UInt8}
    {dlen : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} (hbs : bs.length = 40)
    (hm : (cell64 rev baHeaderWord ⋆ cell64 (rev + 8#64) dlen ⋆
      cell64 (rev + 16#64) 40#64 ⋆ bytes (rev + 24#64) bs ⋆ R) m) :
    (freeObjLayout rev (sarrayAllocBytes 40) baHeaderWord ⋆ R) m := by
  have htag : (baHeaderWord >>> 56).toNat = sarrayTag := by decide
  have hnot1 : sarrayTag ≠ arrayTag := by decide
  unfold freeObjLayout
  rw [htag, ite_eq_right hnot1, ite_eq_left rfl]
  have hm' :
      ((((cell64 rev baHeaderWord ⋆ cell64 (rev + 8#64) dlen) ⋆
        cell64 (rev + 16#64) 40#64) ⋆ bytes (rev + 24#64) bs) ⋆ R) m := sep_ac hm
  have hlen : bs.length = sarrayAllocBytes 40 - 24 := by rw [hbs]; decide
  refine sep_mono (fun _ mx => ⟨40#64, by decide, by decide, ?_⟩) hm'
  exact sep_mono (fun _ m3 => sep_mono (fun _ m2 =>
    sep_mono_r (fun _ m21 => loop_cell64_to_region m21) m2) m3)
    (sep_mono_r (fun _ mbs => hlen ▸ LeanLCNF.bytes_to_region mbs) mx)
private theorem mpzFreeLayout_of_parts {tmp : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (hxs : xs.length = 2)
    (hm : (cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆
      array64 (tmp + 16#64) xs ⋆ R) m) :
    (freeObjLayout tmp (mpzAllocBytes 2) mpzHeaderWord ⋆ R) m := by
  have htag : (mpzHeaderWord >>> 56).toNat = mpzTag := by decide
  unfold freeObjLayout
  rw [htag, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left rfl]
  have hm' :
      (((cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32))) ⋆
        array64 (tmp + 16#64) xs) ⋆ R) m := sep_ac hm
  have hlow : ((2#64 ||| (2#64 <<< 32)) &&& 4294967295#64).toNat = 2 := by decide
  have hlen : 8 * xs.length = mpzAllocBytes 2 - 16 := by rw [hxs]; decide
  exact sep_mono (fun _ mx => ⟨2#64 ||| (2#64 <<< 32), by rw [hlow]; decide,
    by rw [hlow]; decide,
    sep_mono_r (fun _ m22 => hlen ▸ array64_to_region (by rw [hxs]; decide) m22) mx⟩) hm'
theorem loop_mpzObjMem_eq {o : LcnfObj} (h : o.tag = mpzTag) :
    lcnfObjMem o = cell64 o.addr o.header ⋆ cell64 (o.addr + 8#64) o.mpzMeta ⋆
      array64 (o.addr + 16#64) o.limbs :=
  r2b_lcnfObjMem_mpz_eq h
theorem bv_add2_eq {a b1 b2 c1 c2 : BitVec 64}
    (h : b1 + b2 = c1 + c2) : a + b1 + b2 = a + c1 + c2 := by
  rw [BitVec.add_assoc, h, ← BitVec.add_assoc]
private theorem wp_pass_group2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {entry : Tup Cont [[i64, i64]] → Expr Val Cont rs} (K : Cont [i64, i64])
    (h : ∀ J : Cont [i64, i64], (∀ xs mk, K xs mk → J xs mk) → wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [[i64, i64]])
      (fun _ => .cons (fun p => .jump K (Arg.var p.fst, Arg.var p.snd.fst, ())) .nil)
      entry) m :=
  wp_join_group (fun xs mk => K xs mk) (fun _ ⟨_, _, ⟨⟩⟩ _ hk => hk) h
@[expose] def twoLimbTail (rt rev tmp : BitVec 64) (st : RtC0State) (objs : List LcnfObj)
    (dlenRev : BitVec 64) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  rtC0Inv rt st ⋆ cell64 rev baHeaderWord ⋆ cell64 (rev + 8#64) dlenRev ⋆
    cell64 (rev + 16#64) 40#64 ⋆ lcnfHeap objs ⋆ cell64 tmp mpzHeaderWord ⋆
    cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆ R
@[expose] def trimExpr2 (arrPtr cnInit : Val i64)
    (after : Tup Val [i64, i64] → Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  Expr.group (sig := [[i64, i64]])
    (fun Js =>
      Blocks.cons
        (fun p6 =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool (by decide),
              args := (Arg.var p6.snd.fst, Arg.imm 0, ()) }
            fun p7 =>
            Expr.jnz (Arg.var p7.fst)
              (Expr.group (sig := [[i64, i64]])
                (fun _ =>
                  Blocks.cons
                    (fun p => Expr.jump Js.fst (Arg.var p.fst, Arg.var p.snd.fst, ()))
                    Blocks.nil)
                fun Js =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide),
                    args := (Arg.var p6.fst, Arg.imm 0, ()) }
                  fun p8 =>
                  Expr.jnz (Arg.var p8.fst)
                    (Expr.let_
                      { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var arrPtr, Arg.imm 16, ()) }
                      fun p =>
                      Expr.let_
                        { sig := [i64, i64], code := OpCode.sub i64,
                          args := (Arg.var p6.fst, Arg.imm 1, ()) }
                        fun p9 =>
                        Expr.let_
                          { sig := [i64, i64], code := OpCode.mul i64,
                            args := (Arg.imm 8, Arg.var p9.fst, ()) }
                          fun p10 =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.add i64,
                              args := (Arg.var p.fst, Arg.var p10.fst, ()) }
                            fun p =>
                            Expr.load i64 (Arg.var p.fst) fun ld =>
                              Expr.group (sig := [[i64, i64]])
                                (fun _ =>
                                  Blocks.cons
                                    (fun p => Expr.jump Js.fst
                                      (Arg.var p.fst, Arg.var p.snd.fst, ()))
                                    Blocks.nil)
                                fun Js =>
                                Expr.let_
                                  { sig := [i64, i64],
                                    code := OpCode.cmp CmpOp.eq i64 Ty.bool (by decide),
                                    args := (Arg.var ld, Arg.imm 0, ()) }
                                  fun p =>
                                  Expr.jnz (Arg.var p.fst)
                                    (Expr.let_
                                      { sig := [i64, i64], code := OpCode.sub i64,
                                        args := (Arg.var p6.fst, Arg.imm 1, ()) }
                                      fun p =>
                                      Expr.jump Js.fst (Arg.var p.fst, Arg.var p6.snd.fst, ()))
                                    (Expr.jump Js.fst (Arg.var p6.fst, Arg.imm 0, ())))
                    (Expr.jump Js.fst (Arg.var p6.fst, Arg.imm 0, ())))
              (after p6))
        Blocks.nil)
    (fun Js => Expr.jump Js.fst (Arg.var cnInit, Arg.imm 1, ()))
theorem twoLimb_trim_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {arrPtr a0 a1 cnInit : BitVec 64} {after : Tup Val [i64, i64] → Expr Val Cont [i64]}
    {m : Mem 64}
    (hcn : cnInit = 2#64 ∨ (cnInit = 1#64 ∧ a1 = 0#64))
    (hm : (array64 (arrPtr + 16#64) [a0, a1] ⋆ R) m)
    (hafter : ∀ cn' go' : BitVec 64,
      ((a1 ≠ 0#64 ∧ cn' = 2#64) ∨ (a1 = 0#64 ∧ a0 ≠ 0#64 ∧ cn' = 1#64) ∨
        (a1 = 0#64 ∧ a0 = 0#64 ∧ cn' = 0#64)) →
      wp loopRtEnv Q X (after (cn', go', ())) m) :
    wp loopRtEnv Q X (trimExpr2 arrPtr cnInit after) m := by
  unfold trimExpr2
  refine wp_loop_inv (Γ := loopRtEnv)
    (fun (cnZ, zgo, ()) mt => mt = m ∧
      ((cnZ = 2#64 ∧ zgo = 1#64) ∨
       (cnZ = 1#64 ∧ zgo = 1#64 ∧ a1 = 0#64) ∨
       (cnZ = 0#64 ∧ zgo = 1#64 ∧ a1 = 0#64 ∧ a0 = 0#64) ∨
       (cnZ = 2#64 ∧ zgo = 0#64 ∧ a1 ≠ 0#64) ∨
       (cnZ = 1#64 ∧ zgo = 0#64 ∧ a1 = 0#64 ∧ a0 ≠ 0#64) ∨
       (cnZ = 0#64 ∧ zgo = 0#64 ∧ a1 = 0#64 ∧ a0 = 0#64)))
    (fun (cnZ, zgo, ()) _ => if zgo = 0#64 then 0 else cnZ.toNat + 1) ?_ ?_
  · intro Jz hJz
    rcases hcn with rfl | ⟨rfl, rfl⟩
    · exact hJz (2#64, 1#64, ()) m ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    · exact hJz (1#64, 1#64, ()) m ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
  · rintro Jz ⟨cnZ, zgo, ⟨⟩⟩ mt ⟨rfl, hzc⟩ hRecZ
    t_wp_unfold
    rcases hzc with ⟨rfl, rfl⟩ | ⟨rfl, rfl, ha1z⟩ | ⟨rfl, rfl, ha1z, ha0z⟩ |
      ⟨rfl, rfl, ha1nz⟩ | ⟨rfl, rfl, ha1z, ha0nz⟩ | ⟨rfl, rfl, ha1z, ha0z⟩
    · refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      refine wp_pass_group2 Jz fun Js hJs => ?_
      t_wp_unfold
      refine ⟨fun _ => ?_, fun hf => absurd hf (by decide)⟩
      have hld1 : loadVal mt i64 (arrPtr + 16#64 + 8#64 * (2#64 - 1#64)) = some a1 := by
        rw [bv_add2_eq (c1 := 16#64) (c2 := BitVec.ofNat 64 (8 * 1)) (by decide)]
        exact loadVal_array64 (i := 1) (by simp) hm
      refine ⟨a1, by simpa using hld1, ?_⟩
      refine wp_pass_group2 Js fun Js1 hJs1 => ?_
      t_wp_unfold
      refine ⟨fun h1z => ?_, fun h1nz => ?_⟩
      · exact hJs1 _ _ (hJs _ _ (hRecZ (1#64, 1#64, ()) mt (by decide)
          ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl, h1z⟩)⟩))
      · exact hJs1 _ _ (hJs _ _ (hRecZ (2#64, 0#64, ()) mt (by decide)
          ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h1nz⟩)))⟩))
    · refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      refine wp_pass_group2 Jz fun Js hJs => ?_
      t_wp_unfold
      refine ⟨fun _ => ?_, fun hf => absurd hf (by decide)⟩
      have hld0 : loadVal mt i64 (arrPtr + 16#64 + 8#64 * (1#64 - 1#64)) = some a0 := by
        rw [bv_add2_eq (c1 := 16#64) (c2 := BitVec.ofNat 64 (8 * 0)) (by decide)]
        exact loadVal_array64 (i := 0) (by simp) hm
      refine ⟨a0, by simpa using hld0, ?_⟩
      refine wp_pass_group2 Js fun Js1 hJs1 => ?_
      t_wp_unfold
      refine ⟨fun h0z => ?_, fun h0nz => ?_⟩
      · exact hJs1 _ _ (hJs _ _ (hRecZ (0#64, 1#64, ()) mt (by decide)
          ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, ha1z, h0z⟩))⟩))
      · exact hJs1 _ _ (hJs _ _ (hRecZ (1#64, 0#64, ()) mt (by decide)
          ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, ha1z, h0nz⟩))))⟩))
    · refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      refine wp_pass_group2 Jz fun Js hJs => ?_
      t_wp_unfold
      refine ⟨fun ht => absurd ht (by decide), fun _ => ?_⟩
      exact hJs _ _ (hRecZ (0#64, 0#64, ()) mt (by decide)
        ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, ha1z, ha0z⟩))))⟩)
    · exact ⟨fun h => absurd h (by decide), fun _ => hafter 2#64 0#64 (Or.inl ⟨ha1nz, rfl⟩)⟩
    · exact ⟨fun h => absurd h (by decide),
        fun _ => hafter 1#64 0#64 (Or.inr (Or.inl ⟨ha1z, ha0nz, rfl⟩))⟩
    · exact ⟨fun h => absurd h (by decide),
        fun _ => hafter 0#64 0#64 (Or.inr (Or.inr ⟨ha1z, ha0z, rfl⟩))⟩
@[expose] def revFreeExpr2 (rt tmp rev dlen : BitVec 64) : Expr Val Cont [i64] :=
  Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "r2b_str_alloc_cap"
    (Arg.var rt, Arg.var (dlen + 1#64), Arg.var dlen, Arg.var dlen, ()) fun p =>
    Expr.group (sig := [[i64]])
      (fun Js =>
        Blocks.cons
          (fun p1 =>
            Expr.let_
              { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool (by decide),
                args := (Arg.var p1.fst, Arg.var dlen, ()) }
              fun p2 =>
              Expr.jnz (Arg.var p2.fst)
                (Expr.let_
                  { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var rev, Arg.imm 24, ()) }
                  fun p3 =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.sub i64,
                      args := (Arg.var dlen, Arg.imm 1, ()) }
                    fun p4 =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.sub i64,
                        args := (Arg.var p4.fst, Arg.var p1.fst, ()) }
                      fun p5 =>
                      Expr.let_
                        { sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var p3.fst, Arg.var p5.fst, ()) }
                        fun p6 =>
                        Expr.load i8 (Arg.var p6.fst) fun ld =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.add i64,
                              args := (Arg.var p.fst, Arg.imm 32, ()) }
                            fun p =>
                            Expr.let_
                              { sig := [i64, i64], code := OpCode.add i64,
                                args := (Arg.var p.fst, Arg.var p1.fst, ()) }
                              fun p =>
                              Expr.store (Arg.var ld) (Arg.var p.fst)
                                (Expr.let_
                                  { sig := [i64, i64], code := OpCode.add i64,
                                    args := (Arg.var p1.fst, Arg.imm 1, ()) }
                                  fun p => Expr.jump Js.fst (Arg.var p.fst, ())))
                (Expr.call (as := [i64, i64]) (bs := []) "lcnf_free_obj"
                  (Arg.var rt, Arg.var rev, ()) fun _ =>
                  Expr.call (as := [i64, i64]) (bs := []) "lcnf_free_obj"
                    (Arg.var rt, Arg.var tmp, ()) fun _ =>
                    Expr.ret (Arg.var p.fst, ())))
          Blocks.nil)
      fun Js => Expr.jump Js.fst (Arg.imm 0, ())
theorem list_take_succ {α : Type _} (l : List α) (n : Nat) (h : n < l.length) :
    l.take (n + 1) = l.take n ++ [l[n]] := by
  induction l generalizing n with
  | nil => contradiction
  | cons a t ih =>
    cases n with
    | zero => rfl
    | succ k => exact congrArg (a :: ·) (ih k (Nat.lt_of_succ_lt_succ h))
theorem list_take_set_of_le {α : Type _} (l : List α) (n : Nat) (v : α) :
    (l.set n v).take n = l.take n := by
  induction l generalizing n with
  | nil => rfl
  | cons a t ih =>
    cases n with
    | zero => rfl
    | succ k => exact congrArg (a :: ·) (ih k)
theorem twoLimb_revFree_wp {Q : Post [i64]} {X : XPost} {R : Mem 64 → Prop}
    {rt tmp rev dlen : BitVec 64} {st3 : RtC0State} {objs' : List LcnfObj}
    {revBs : List UInt8} {val : Nat} {m : Mem 64}
    (htmp0 : tmp ≠ 0#64) (htmp8 : tmp.toNat % 8 = 0)
    (hrev0 : rev ≠ 0#64) (hrev8 : rev.toNat % 8 = 0)
    (hrevL : revBs.length = 40)
    (hdlPos : 1 ≤ dlen.toNat) (hdlLt40 : dlen.toNat < 40)
    (hst3Rem : strAllocBytes 41 ≤ st3.rem)
    (hdecEq : natToDecimalBytes val = (revBs.take dlen.toNat).reverse)
    (hmk : (array64 (tmp + 16#64) [0#64, 0#64] ⋆
      (bytes (rev + 24#64) revBs ⋆ twoLimbTail rt rev tmp st3 objs' dlen R)) m)
    (hk : ∀ (s : BitVec 64) (st' : RtC0State) (m' : Mem 64),
      s ≠ 0#64 → s.toNat % 8 = 0 → st'.PreservesMeta st3 → st'.rem ≤ st3.rem →
      let dec := natToDecimalBytes val
      let sObj := mkStrObj s 1#32 (dec.length + 1) dec dec.length
      StrCanon sObj →
      (rtC0Inv rt st' ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs' ⋆ R) m' → Q (s, ()) m') :
    wp loopRtEnv Q X (revFreeExpr2 rt tmp rev dlen) m := by
  have hdlen_eq_dec : dlen.toNat = (natToDecimalBytes val).length := by
    rw [hdecEq, List.length_reverse, List.length_take_of_le (by omega)]
  have hdl1_nat : (dlen + 1#64).toNat = dlen.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hstr_bounds :
      dlen.toNat < strMaxCap ∧ dlen.toNat < (dlen + 1#64).toNat ∧
        (dlen + 1#64).toNat ≤ strMaxCap := by
    dsimp only [strMaxCap]; omega
  have hreq_le : strAllocBytes (dlen + 1#64).toNat ≤ st3.rem := by
    rw [hdl1_nat]
    have hm_mono : strAllocBytes (dlen.toNat + 1) ≤ strAllocBytes 41 := by
      unfold strAllocBytes align8; omega
    omega
  unfold revFreeExpr2
  apply wp_call_step
  dsimp only [vals, Arg.val]
  apply rtC0CoreEnv_le_loopRtEnv
  apply rtR2bEnv_le_rtC0CoreEnv
  apply rtR2bEnv_r2b_str_alloc_cap
  dsimp only [r2bStrAllocCapSpec, vals, Arg.val]
  rw [ite_eq_left hstr_bounds]
  have hmk_rt : (rtC0Inv rt st3 ⋆ (array64 (tmp + 16#64) [0#64, 0#64] ⋆
      bytes (rev + 24#64) revBs ⋆ cell64 rev baHeaderWord ⋆ cell64 (rev + 8#64) dlen ⋆
      cell64 (rev + 16#64) 40#64 ⋆ lcnfHeap objs' ⋆ cell64 tmp mpzHeaderWord ⋆
      cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆ R)) m := by
    unfold twoLimbTail at hmk; exact sep_cast hmk (by ac_rfl)
  refine ⟨st3, _, Or.inr hreq_le, hmk_rt, ?_⟩
  intro s st4 m5 hs0 hs8 hpr4 hrem4 _ hm5
  have hm5_reg :
      (region (s + 32#64) dlen.toNat ⋆
        (rtC0Inv rt st4 ⋆ cell64 s strHeaderWord ⋆ cell64 (s + 8#64) (dlen + 1#64) ⋆
          cell64 (s + 16#64) (dlen + 1#64) ⋆ cell64 (s + 24#64) dlen ⋆
          bytes (s + 32#64 + dlen) [0] ⋆
          region (s + 32#64 + dlen + 1#64)
            (strAllocBytes (dlen + 1#64).toNat - (32 + dlen.toNat + 1)) ⋆
          array64 (tmp + 16#64) [0#64, 0#64] ⋆ bytes (rev + 24#64) revBs ⋆
          cell64 rev baHeaderWord ⋆ cell64 (rev + 8#64) dlen ⋆ cell64 (rev + 16#64) 40#64 ⋆
          lcnfHeap objs' ⋆ cell64 tmp mpzHeaderWord ⋆
          cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆ R)) m5 := sep_cast hm5 (by ac_rfl)
  obtain ⟨sBs0, hsBs0Len, hm5_bs⟩ :=
    region_pop_bytes (k := dlen.toNat) (Nat.le_refl _) (by omega) hm5_reg
  rw [Nat.sub_self, region_zero, sep_emp] at hm5_bs
  let dec := natToDecimalBytes val
  have hdecL : dec.length = dlen.toNat := hdlen_eq_dec.symm
  refine wp_loop_inv (Γ := loopRtEnv)
    (fun (idx, ()) mr =>
      ∃ sBs : List UInt8,
        idx.toNat ≤ dlen.toNat ∧ sBs.length = dlen.toNat ∧
        sBs.take idx.toNat = dec.take idx.toNat ∧
        (bytes (s + 32#64) sBs ⋆
          (bytes (rev + 24#64) revBs ⋆ rtC0Inv rt st4 ⋆ cell64 s strHeaderWord ⋆
            cell64 (s + 8#64) (dlen + 1#64) ⋆ cell64 (s + 16#64) (dlen + 1#64) ⋆
            cell64 (s + 24#64) dlen ⋆ bytes (s + 32#64 + dlen) [0] ⋆
            region (s + 32#64 + dlen + 1#64)
              (strAllocBytes (dlen + 1#64).toNat - (32 + dlen.toNat + 1)) ⋆
            cell64 (rev + 8#64) dlen ⋆ cell64 rev baHeaderWord ⋆ cell64 (rev + 16#64) 40#64 ⋆
            array64 (tmp + 16#64) [0#64, 0#64] ⋆ lcnfHeap objs' ⋆
            cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆ R)) mr)
    (fun (idx, ()) _ => dlen.toNat - idx.toNat) ?_ ?_
  · intro Jr hJr
    exact hJr (0#64, ()) m5 ⟨sBs0, Nat.zero_le _, hsBs0Len, by simp, sep_cast hm5_bs (by ac_rfl)⟩
  · rintro Jr ⟨idx, ⟨⟩⟩ mr ⟨sBs, hidxLe, hsBsL, hsBsTake, hmr⟩ hRecR
    t_wp_unfold
    refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · rw [BitVec.ult, decide_eq_true_eq] at hlt
      have hiLt : idx.toNat < dlen.toNat := hlt
      have hsub : (dlen - 1#64 - idx).toNat = dlen.toNat - 1 - idx.toNat := by
        have h1 : (dlen - 1#64).toNat = dlen.toNat - 1 := by
          rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr
            (by rw [show (1#64 : BitVec 64).toNat = 1 from rfl]; omega))]
          rfl
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h1]; omega)), h1]
      have hmr_r :
          (bytes (rev + 24#64) revBs ⋆
            (bytes (s + 32#64) sBs ⋆ rtC0Inv rt st4 ⋆ cell64 s strHeaderWord ⋆
              cell64 (s + 8#64) (dlen + 1#64) ⋆ cell64 (s + 16#64) (dlen + 1#64) ⋆
              cell64 (s + 24#64) dlen ⋆ bytes (s + 32#64 + dlen) [0] ⋆
              region (s + 32#64 + dlen + 1#64)
                (strAllocBytes (dlen + 1#64).toNat - (32 + dlen.toNat + 1)) ⋆
              cell64 (rev + 8#64) dlen ⋆ cell64 rev baHeaderWord ⋆ cell64 (rev + 16#64) 40#64 ⋆
              array64 (tmp + 16#64) [0#64, 0#64] ⋆ lcnfHeap objs' ⋆
              cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆ R)) mr :=
        sep_cast hmr (by ac_rfl)
      have hld := r2_c0_load_bytes_bv (a := rev + 24#64) (i := dlen - 1#64 - idx)
        hmr_r (by rw [hsub, hrevL]; omega) (by rw [hrevL]; decide)
      refine ⟨BitVec.ofNat 8 (revBs[(dlen - 1#64 - idx).toNat]).toNat, by simpa using hld, ?_⟩
      let bV := BitVec.ofNat 8 (revBs[(dlen - 1#64 - idx).toNat]).toNat
      have hst := r2b_c0_store_bytes_add32 (a := s) (i := idx) bV hmr
        (by rw [hsBsL]; exact hiLt) (by omega)
      refine ⟨hst.1, ?_⟩
      have hadd1 : (idx + 1#64).toNat = idx.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      have hbEq : UInt8.ofNat bV.toNat = revBs[(dlen - 1#64 - idx).toNat] := by
        have h1 : bV.toNat = (revBs[(dlen - 1#64 - idx).toNat]).toNat := by
          dsimp [bV]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt _)]
        rw [h1]; exact UInt8.ofNat_toNat
      have hdecGet : dec[idx.toNat]'(by rw [hdecL]; exact hiLt) =
          revBs[(dlen - 1#64 - idx).toNat] := by
        have hlenT : (revBs.take dlen.toNat).length = dlen.toNat :=
          List.length_take_of_le (by rw [hrevL]; exact Nat.le_of_lt hdlLt40)
        have hrevGet :
            (revBs.take dlen.toNat).reverse[idx.toNat]'(by
              rw [List.length_reverse, hlenT]; exact hiLt) =
              revBs[(dlen - 1#64 - idx).toNat] := by
          rw [List.getElem_reverse, List.getElem_take]
          congr 1
          rw [hlenT]
          omega
        have hlistEq : ∀ (l : List UInt8) (hl : l = (revBs.take dlen.toNat).reverse)
            (hi : idx.toNat < l.length),
            l[idx.toNat]'hi = revBs[(dlen - 1#64 - idx).toNat] := by
          intro l hl hi; subst hl; exact hrevGet
        exact hlistEq dec hdecEq (by rw [hdecL]; exact hiLt)
      have hnextTake :
          (sBs.set idx.toNat (UInt8.ofNat bV.toNat)).take (idx + 1#64).toNat =
            dec.take (idx + 1#64).toNat := by
        rw [hadd1, list_take_succ _ _ (by simp [hsBsL, hiLt]),
          list_take_succ _ _ (by rw [hdecL]; exact hiLt), list_take_set_of_le, hsBsTake,
          List.getElem_set_self (by simp [hsBsL, hiLt]), hbEq, hdecGet]
      exact hRecR (idx + 1#64, ()) _ (by dsimp only; rw [hadd1]; omega)
        ⟨sBs.set idx.toNat (UInt8.ofNat bV.toNat), by rw [hadd1]; omega,
          by simp [hsBsL], hnextTake, hst.2⟩
    · rw [BitVec.ult, decide_eq_false_iff_not] at hge
      have hiEq : idx.toNat = dlen.toNat := by omega
      have hsBs_eq : sBs = dec := by
        have ht := hsBsTake
        rw [hiEq, List.take_of_length_le (Nat.le_of_eq hsBsL),
          List.take_of_length_le (Nat.le_of_eq hdecL)] at ht
        exact ht
      rw [hsBs_eq] at hmr
      let sObj := mkStrObj s 1#32 (dec.length + 1) dec dec.length
      have hsObj_canon : StrCanon sObj :=
        mkStrObj_canon hs0 hs8 (by decide) (by rw [hdecL]; omega)
          (by dsimp only [strMaxCap]; rw [hdecL]; omega) (by rw [hdecL]; omega)
      have hdl_bv : dlen = BitVec.ofNat 64 dec.length := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, hdecL, Nat.mod_eq_of_lt (by omega)]
      have hdl1_bv : dlen + 1#64 = BitVec.ofNat 64 (dec.length + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, hdecL, Nat.mod_eq_of_lt (by omega), hdl1_nat]
      have hmr_str :
          (cell64 s strHeaderWord ⋆
            cell64 (s + 8#64) (BitVec.ofNat 64 (dec.length + 1)) ⋆
            cell64 (s + 16#64) (BitVec.ofNat 64 (dec.length + 1)) ⋆
            cell64 (s + 24#64) (BitVec.ofNat 64 dec.length) ⋆
            bytes (s + 32#64) dec ⋆ bytes (s + 32#64 + BitVec.ofNat 64 dec.length) [0] ⋆
            region (s + 32#64 + BitVec.ofNat 64 dec.length + 1#64)
              (strAllocBytes (dec.length + 1) - (32 + dec.length + 1)) ⋆
            (rtC0Inv rt st4 ⋆ cell64 (rev + 8#64) dlen ⋆ cell64 rev baHeaderWord ⋆
              cell64 (rev + 16#64) 40#64 ⋆ bytes (rev + 24#64) revBs ⋆
              array64 (tmp + 16#64) [0#64, 0#64] ⋆ lcnfHeap objs' ⋆
              cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆ R)) mr := by
        rw [← hdl1_bv, ← hdl_bv, hdecL, ← hdl1_nat]
        exact sep_cast hmr (by ac_rfl)
      have hhm_str :
          (cell64 rev baHeaderWord ⋆ cell64 (rev + 8#64) dlen ⋆ cell64 (rev + 16#64) 40#64 ⋆
            bytes (rev + 24#64) revBs ⋆
            (lcnfObjMem sObj ⋆ rtC0Inv rt st4 ⋆ array64 (tmp + 16#64) [0#64, 0#64] ⋆
              lcnfHeap objs' ⋆ cell64 tmp mpzHeaderWord ⋆
              cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆ R)) mr := by
        have hmem := mkStrObj_mem_of_parts (cap := dec.length + 1) (len := dec.length)
          (by dsimp only [strMaxCap]; rw [hdecL]; omega) (by rw [hdecL]; omega) hmr_str
        exact sep_cast hmem (by ac_rfl)
      have hm_freeRev :
          (rtC0Inv rt st4 ⋆ freeObjLayout rev (sarrayAllocBytes 40) baHeaderWord ⋆
            (lcnfObjMem sObj ⋆ array64 (tmp + 16#64) [0#64, 0#64] ⋆ lcnfHeap objs' ⋆
              cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆ R)) mr :=
        sep_cast (sarrayFreeLayout_of_parts hrevL hhm_str) (by ac_rfl)
      apply wp_call_step
      dsimp only [vals, Arg.val]
      apply rtC0CoreEnv_le_loopRtEnv
      apply rtR2bEnv_le_rtC0CoreEnv
      apply rtR2bEnv_lcnf_free_obj
      dsimp only [lcnfFreeObjSpec, vals, Arg.val]
      have hrevBit : ¬ (rev &&& 1#64 ≠ 0#64) := by
        intro h; apply h
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_and, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64), Nat.and_one_is_mod]
        omega
      rw [ite_eq_right hrevBit]
      refine ⟨st4, baHeaderWord, sarrayAllocBytes 40, _, hrev0, hrev8, by decide, by decide,
        by decide, hm_freeRev, ?_⟩
      intro st5 m6 hpr5 hrem5 _ hm6
      have hm6' :
          (cell64 tmp mpzHeaderWord ⋆ cell64 (tmp + 8#64) (2#64 ||| (2#64 <<< 32)) ⋆
            array64 (tmp + 16#64) [0#64, 0#64] ⋆
            (rtC0Inv rt st5 ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs' ⋆ R)) m6 :=
        sep_cast hm6 (by ac_rfl)
      have hm_freeTmp :
          (rtC0Inv rt st5 ⋆ freeObjLayout tmp (mpzAllocBytes 2) mpzHeaderWord ⋆
            (lcnfObjMem sObj ⋆ lcnfHeap objs' ⋆ R)) m6 :=
        sep_cast (mpzFreeLayout_of_parts rfl hm6') (by ac_rfl)
      apply wp_call_step
      dsimp only [vals, Arg.val]
      apply rtC0CoreEnv_le_loopRtEnv
      apply rtR2bEnv_le_rtC0CoreEnv
      apply rtR2bEnv_lcnf_free_obj
      dsimp only [lcnfFreeObjSpec, vals, Arg.val]
      have htmpBit : ¬ (tmp &&& 1#64 ≠ 0#64) := by
        intro h; apply h
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_and, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64), Nat.and_one_is_mod]
        omega
      rw [ite_eq_right htmpBit]
      refine ⟨st5, mpzHeaderWord, mpzAllocBytes 2, lcnfObjMem sObj ⋆ lcnfHeap objs' ⋆ R,
        htmp0, htmp8, by decide, by decide, by decide, hm_freeTmp, ?_⟩
      intro st6 m7 hpr6 hrem6 _ hm7
      t_wp_unfold
      exact hk s st6 m7 hs0 hs8 (hpr4.trans (hpr5.trans hpr6)) (by omega) hsObj_canon
        (sep_cast hm7 (by ac_rfl))

end LeanQbe.T.LeanLCNF
