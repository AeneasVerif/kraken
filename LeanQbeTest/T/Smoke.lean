module

public import LeanQbe.T.WPLemmas

/-!
# Smoke tests, mutual groups, memory/calls/exits, and relational opcode edge cases

* `evenOdd`: mutually recursive 2-block `group` (from `Typed2.lean` / `Smoke.lean`), proved for all `n`.
* `sumLanes`: 2-label group carrying `(i32, v4i32)` exiting through `done` (from `Typed2.lean`).
* `tracer`: `load` and `store` over Kraken's partial `Mem 64` (including unmapped failure).
* `caller`: signature-indexed `call` and abnormal `exit` (D5).
* `spin`: non-vacuity (`¬ Func.wp Γ spin () m Q X`).
* Relational & edge-case checks: `udiv`/`sdiv` UB, `udiv0`/`sdiv0`, `fadd` deterministic +
  nondeterministic NaN (`∀`), `fadd` split, vector shuffles, `sha256rnds2`, `ternlog`, `fshl`/`fshr`,
  `smulw`, `bswap`, and `DecidableEq` on `OpCode` / GVN key `(sig : List Ty) × (rs : List Ty) × OpCode sig rs`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Smoke

/-! ## 1. `evenOdd`: mutually recursive 2-block `group` -/

def evenOdd : Func [i64] [i32] := fun _ _ (n, ()) =>
  .group (sig := [[i64], [i64]])
    (fun (even, odd, ()) =>
      .cons (fun (x, ()) =>
        .let_ (op2 (.ult i64) (.imm 0) (.var x)) fun (c, ()) =>
        .jnz (.var c)
          (.let_ (op2 (.sub i64) (.var x) (.imm 1)) fun (y, ()) => .jump odd (.var y, ()))
          (.ret (.imm 1, ())))
      (.cons (fun (x, ()) =>
        .let_ (op2 (.ult i64) (.imm 0) (.var x)) fun (c, ()) =>
        .jnz (.var c)
          (.let_ (op2 (.sub i64) (.var x) (.imm 1)) fun (y, ()) => .jump even (.var y, ()))
          (.ret (.imm 0, ())))
      .nil))
    (fun (even, _, ()) => .jump even (.var n, ()))

def parity (k : Nat) : BitVec 32 := if k % 2 = 0 then 1 else 0

theorem evenOdd_correct (Γ : Env) (X : XPost) (n : BitVec 64) (m : Mem 64) :
    Func.wp Γ evenOdd (n, ()) m (fun (r, ()) m' => r = parity n.toNat ∧ m' = m) X := by
  simp only [Func.wp, evenOdd, wp, vals, Arg.val_var]
  intro Js hc
  simp only [Closed, and_true] at hc
  obtain ⟨hEven, hOdd⟩ := hc
  suffices h : ∀ k : Nat, k < 2 ^ 64 →
      (n.toNat % 2 = k % 2 → Js.1 (BitVec.ofNat 64 k, ()) m) ∧
      (n.toNat % 2 ≠ k % 2 → Js.2.1 (BitVec.ofNat 64 k, ()) m) by
    have hof : BitVec.ofNat 64 n.toNat = n := BitVec.eq_of_toNat_eq (by simp)
    simpa [hof] using (h n.toNat n.isLt).1 rfl
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun hk => hEven _ _ ?_, fun hk => hOdd _ _ ?_⟩
    · simp only [wp_let_op2, wp_jnz, wp_ret, OpCode.ult, OpCode.wp_cmp, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits, cast_eq, vals, Arg.val_var,
        Arg.val_imm]
      have h0 : (0 : BitVec 64).ult (BitVec.ofNat 64 0) = false := by decide
      rw [h0]
      simp only [Bool.false_eq_true, false_implies, true_and]
      have hp : parity n.toNat = 1 := by simp [parity, show n.toNat % 2 = 0 by omega]
      exact fun _ => ⟨hp.symm, trivial⟩
    · simp only [wp_let_op2, wp_jnz, wp_ret, OpCode.ult, OpCode.wp_cmp, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits, cast_eq, vals, Arg.val_var,
        Arg.val_imm]
      have h0 : (0 : BitVec 64).ult (BitVec.ofNat 64 0) = false := by decide
      rw [h0]
      simp only [Bool.false_eq_true, false_implies, true_and]
      have hp : parity n.toNat = 0 := by simp [parity, show n.toNat % 2 ≠ 0 by omega]
      exact fun _ => ⟨hp.symm, trivial⟩
  | succ k ih =>
    intro hk
    have ih := ih (by omega)
    have hsub : BitVec.ofNat 64 (k + 1) - (1 : BitVec 64) = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hpos : (0 : BitVec 64).ult (BitVec.ofNat 64 (k + 1)) = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat]; omega
    refine ⟨fun h => hEven _ _ ?_, fun h => hOdd _ _ ?_⟩
    · simp only [wp_let_op2, wp_jnz, wp_jump, OpCode.ult, OpCode.wp_cmp, OpCode.wp_sub,
        Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp, lift2, CmpOp.evalBits, cast_eq, vals,
        Arg.val_var, Arg.val_imm]
      rw [hpos, hsub]
      exact ⟨fun _ => ih.2 (by omega), fun h0 => absurd h0 (by decide)⟩
    · simp only [wp_let_op2, wp_jnz, wp_jump, OpCode.ult, OpCode.wp_cmp, OpCode.wp_sub,
        Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp, lift2, CmpOp.evalBits, cast_eq, vals,
        Arg.val_var, Arg.val_imm]
      rw [hpos, hsub]
      exact ⟨fun _ => ih.1 (by omega), fun h0 => absurd h0 (by decide)⟩

/-! ## 2. `sumLanes`: 2-label group carrying `i32` and `v4i32` (from `Typed2.lean`) -/

def sumLanes : Func [] [i64] := fun _ _ () =>
  .group (sig := [[v4i32], [i32, v4i32]])
    (fun (done, loop, ()) =>
      .cons (fun (acc, ()) =>
        .let_ (op1 (.unpair (Ty.vec 1 i32) (Ty.vec 1 i32)) (.var acc)) fun (lo, _, ()) =>
        .let_ (op1 (.unpair i32 i32) (.var lo)) fun (x, _, ()) =>
        .let_ (op1 (.zext 32 64) (.var x)) fun (y, ()) =>
        .ret (.var y, ()))
      (.cons (fun (i, acc, ()) =>
        .let_ (op2 (.ult i32) (.var i) (.imm 10)) fun (c, ()) =>
        .jnz (.var c)
          (.let_ (op2 (.add v4i32) (.var acc) (.var acc)) fun (acc', ()) =>
           .let_ (op2 (.add i32) (.var i) (.imm 1)) fun (i', ()) =>
           .jump loop (.var i', .var acc', ()))
          (.jump done (.var acc, ())))
      .nil))
    (fun (_, loop, ()) => .jump loop (.imm 0, .imm ((1, 1), (1, 1)), ()))

theorem sumLanes_correct (Γ : Env) (X : XPost) (m : Mem 64) :
    Func.wp Γ sumLanes () m (fun (r, ()) m' => r = 1024#64 ∧ m' = m) X := by
  simp only [Func.wp, sumLanes, wp]
  intro Js hc
  simp only [Closed, and_true] at hc
  obtain ⟨hDone, hLoop⟩ := hc
  have hd : ∀ (acc : Val v4i32), acc.1.1 = 1024#32 → Js.1 (acc, ()) m := by
    intro acc hacc
    refine hDone _ _ ?_
    simp only [wp_let_op1, wp_ret, OpCode.wp_unpair, OpCode.wp_zext, vals, Arg.val_var, hacc]
    exact ⟨by decide, rfl, trivial⟩
  have hl : ∀ k : Nat, k ≤ 10 →
      ∀ acc : Val v4i32, acc.1.1 = BitVec.ofNat 32 (2 ^ (10 - k)) →
      Js.2.1 (BitVec.ofNat 32 (10 - k), acc, ()) m := by
    intro k
    induction k with
    | zero =>
      intro _ acc hacc
      refine hLoop _ _ ?_
      simp only [wp_let_op2, wp_jnz, wp_jump, OpCode.ult, OpCode.wp_cmp, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits, cast_eq, vals, Arg.val_var,
        Arg.val_imm]
      have h10 : (10#32).ult 10#32 = false := by decide
      simp only [Nat.sub_zero, BitVec.ofNat_eq_ofNat]
      rw [h10]
      refine ⟨fun h => absurd h (by decide), fun _ => hd acc (by simpa using hacc)⟩
    | succ k ih =>
      intro hk acc hacc
      refine hLoop _ _ ?_
      simp only [wp_let_op2, wp_jnz, wp_jump, OpCode.ult, OpCode.wp_cmp, OpCode.wp_add,
        Ty.hasFloat, Bool.false_or, Bool.false_eq_true, ↓reduceIte, liftCmp, lift2,
        CmpOp.evalBits, cast_eq, vals, Arg.val_var, Arg.val_imm]
      have hlt : (BitVec.ofNat 32 (10 - (k + 1))).ult 10 = true := by
        simp [BitVec.ult, BitVec.toNat_ofNat]; omega
      rw [hlt]
      refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      have hstep : BitVec.ofNat 32 (10 - (k + 1)) + (1 : BitVec 32) = BitVec.ofNat 32 (10 - k) := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have hpow : acc.1.1 + acc.1.1 = BitVec.ofNat 32 (2 ^ (10 - k)) := by
        rw [hacc]
        apply BitVec.eq_of_toNat_eq
        have h1 : 10 - k = (10 - (k + 1)) + 1 := by omega
        simp [BitVec.toNat_add, BitVec.toNat_ofNat, h1, Nat.pow_succ, Nat.mul_two]
      rw [hstep]
      exact ih (by omega) _ hpow
  exact hl 10 (Nat.le_refl 10) ((1, 1), (1, 1)) rfl

/-! ## 3. `tracer`: `store` + `load` round-trip over partial `Kraken.Mem 64` -/

def tracer : Func [i64, i64, i64] [i64] := fun _ _ (a, b, p, ()) =>
  .let_ (op2 (.add i64) (.var a) (.var b)) fun (x, ()) =>
  .store (.var x) (.var p) <|
  .load i64 (.var p) fun y =>
  .ret (.var y, ())

theorem tracer_correct (Γ : Env) (X : XPost) (a b p : BitVec 64) (m : Mem 64)
    (hok : storeOk m i64 p) :
    Func.wp Γ tracer (a, b, p, ()) m
      (fun (r, ()) m' => r = a + b ∧ m' = storeMem m i64 p (a + b)) X := by
  simp only [Func.wp, tracer, wp_let_op2, wp_store, wp_load, wp_ret, OpCode.wp_add, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte, lift2, vals, Arg.val_var]
  refine ⟨hok, a + b, loadVal_storeMem m i64 p (a + b) (by decide), rfl, trivial⟩

theorem tracer_unmapped_false (Γ : Env) (X : XPost) (a b p : BitVec 64) :
    ¬ Func.wp Γ tracer (a, b, p, ()) (∅ : Mem 64) (fun _ _ => True) X := by
  simp only [Func.wp, tracer, wp_let_op2, wp_store, OpCode.wp_add, Ty.hasFloat, Bool.false_eq_true,
    ↓reduceIte, lift2, Arg.val_var]
  rintro ⟨hok, _⟩
  exact storeOk_empty i64 p (by decide) hok

theorem partial_unmapped_store_false (Γ : Env) (X : XPost) (a b p : BitVec 64) (m : Mem 64)
    (hmiss : m.get? (p + 3#64) = none) :
    ¬ Func.wp Γ tracer (a, b, p, ()) m (fun _ _ => True) X := by
  simp only [Func.wp, tracer, wp_let_op2, wp_store, OpCode.wp_add, Ty.hasFloat, Bool.false_eq_true,
    ↓reduceIte, lift2, Arg.val_var]
  rintro ⟨hok, _⟩
  exact not_storeOk_of_unmapped m i64 p ⟨3, by decide, hmiss⟩ hok

theorem partial_unmapped_load_false (Γ : Env) (X : XPost) (p : BitVec 64) (m : Mem 64)
    (hmiss : m.get? (p + 1#64) = none) :
    ¬ wp Γ (rs := [i32]) (fun _ _ => True) X
        (.load i32 (.var p) fun y => .ret (.var y, ())) m := by
  simp only [wp_load, Arg.val_var]
  rintro ⟨v, hv, _⟩
  rw [loadVal_of_unmapped m i32 p ⟨1, by decide, hmiss⟩] at hv
  cases hv

def storeThenLoadOther : Func [i64, i64, i64] [i64] := fun _ _ (v, p, q, ()) =>
  .store (t := i64) (.var v) (.var p) <|
  .load i64 (.var q) fun y =>
  .ret (.var y, ())

theorem store_disjoint_load_preserves (Γ : Env) (X : XPost) (m : Mem 64)
    (v p q old : BitVec 64)
    (hp : storeOk m i64 p) (hq : loadVal m i64 q = some old)
    (hdisj : ∀ i j, i < 8 → j < 8 → q + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 i) :
    Func.wp Γ storeThenLoadOther (v, p, q, ()) m (fun (r, ()) _ => r = old) X := by
  simp only [Func.wp, storeThenLoadOther, wp_store, wp_load, wp_ret, vals, Arg.val_var]
  refine ⟨hp, old, ?_, rfl⟩
  rw [loadVal_storeMem_disjoint m i64 i64 p q v hdisj, hq]

/-! ## 4. `caller`: signature-indexed `call` and abnormal `exit` (D5) -/

def caller : Func [i64] [i64] := fun _ _ (a, ()) =>
  .call "g" (as := [i64]) (bs := [.bool, i64]) (.var a, ()) fun (ok, r, ()) =>
  .jnz (.var ok) (.ret (.var r, ())) (.exit "abort" (as := [i64]) (.var a, ()))

def gSpec : Spec [i64] [.bool, i64] := fun (a, ()) m Q _ =>
  Q (decide (a ≠ 0), a + 1, ()) m

theorem caller_correct (Γ : Env) (hg : Γ "g" [i64] [.bool, i64] = gSpec)
    (a : BitVec 64) (m : Mem 64) :
    Func.wp Γ caller (a, ()) m
      (fun (r, ()) m' => a ≠ 0 ∧ r = a + 1 ∧ m' = m)
      (fun f as xs m' =>
        f = "abort" ∧ (⟨as, xs⟩ : (ts : List Ty) × Tup Val ts) = ⟨[i64], (a, ())⟩ ∧
          m' = m ∧ a = 0) := by
  simp only [Func.wp, caller]
  refine wp_call_of_spec _ _ ?_
  rw [hg]
  simp only [gSpec, vals, Arg.val_var, wp_jnz, wp_ret, wp_exit]
  exact ⟨fun ha => ⟨of_decide_eq_true ha, trivial, trivial⟩,
    fun ha => ⟨trivial, trivial, trivial, by simpa using of_decide_eq_false ha⟩⟩

/-! ## 5. `spin`: non-vacuity of `wp` -/

def spin : Func [] [] := fun _ _ () =>
  .group (sig := [[]]) (fun (l, ()) => .cons (fun () => .jump l ()) .nil) (fun (l, ()) => .jump l ())

theorem spin_false (Γ : Env) (Q : Post []) (X : XPost) (m : Mem 64) :
    ¬ Func.wp Γ spin () m Q X := by
  intro h
  simp only [Func.wp, spin, wp] at h
  exact h ((fun _ _ => False), ()) ⟨fun _ _ hf => hf, trivial⟩

/-! ## 6. Relational `OpCode.wp`, floating-point, vector shuffles, SHA, and `DecidableEq` -/

theorem udiv_zero_ub (a : BitVec 64) (post : Tup Val [i64] → Prop) :
    ¬ (OpCode.udiv 64).wp (a, 0#64, ()) post := by
  simp [OpCode.wp_udiv]

theorem sdiv_overflow_ub (post : Tup Val [i64] → Prop) :
    ¬ (OpCode.sdiv 64).wp (BitVec.intMin 64, BitVec.allOnes 64, ()) post := by
  simp only [OpCode.wp_sdiv, sdivDefined]
  intro ⟨h, _⟩
  exact absurd h (by decide)

theorem udiv0_zero_eq (a : BitVec 64) :
    (OpCode.udiv0 64).wp (a, 0#64, ()) (fun (r, ()) => r = 0#64) := by
  simp [OpCode.wp_udiv0]

theorem fadd_concrete :
    (OpCode.fadd f32).wp (0x3f800000#32, 0x40000000#32, ()) (fun (r, ()) => r = 0x40400000#32) := by
  simp [OpCode.wp_fadd, liftFloatRel2, floatResultWp]
  decide

theorem fadd_nan_forall (post : Tup Val [f32] → Prop)
    (h : ∀ r : BitVec 32, isFloatNaN .s r = true → post (r, ())) :
    (OpCode.fadd f32).wp (0x7fc00000#32, 0x3f800000#32, ()) post := by
  simp only [OpCode.wp_fadd, Ty.isFloatTree, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    liftFloatRel2, floatResultWp]
  have hnan : (Float.Model.UnpackedFloat.add Fmt.s.format
      (unpackFloat .s 0x7fc00000#32) (unpackFloat .s 0x3f800000#32)).isNaN = true := by
    decide
  simpa [hnan] using h

theorem fadd_v8_split (a b : Val (Ty.vec 3 f32)) (post : Tup Val [Ty.vec 3 f32] → Prop) :
    (OpCode.fadd (Ty.vec 3 f32)).wp (a, b, ()) post =
      (OpCode.fadd v4f32).wp (a.1, b.1, ()) fun (r1, ()) =>
        (OpCode.fadd v4f32).wp (a.2, b.2, ()) fun (r2, ()) => post ((r1, r2), ()) := rfl

theorem fadd_nonfloat_ub (a b : BitVec 32) (post : Tup Val [i32] → Prop) :
    ¬ (OpCode.fadd i32).wp (a, b, ()) post := by
  simp [OpCode.wp_fadd]

theorem fcmp_concrete :
    (OpCode.fcmp .lt f32).wp (0x3f800000#32, 0x40000000#32, ()) (fun (r, ()) => r = true) := by
  simp only [OpCode.wp_fcmp, cast_eq]
  decide

theorem fcmp_uno_nan :
    (OpCode.fcmp .uno f32).wp (0x7fc00000#32, 0x3f800000#32, ()) (fun (r, ()) => r = true) := by
  simp only [OpCode.wp_fcmp, cast_eq]
  decide

theorem uitofp_concrete :
    (OpCode.uitofp 32 .s).wp (42#32, ()) (fun (r, ()) => r = 0x42280000#32) := by
  simp only [OpCode.wp_uitofp]
  decide

theorem fptoui_concrete :
    (OpCode.fptoui .s 32).wp (0x42280000#32, ()) (fun (r, ()) => r = 42#32) := by
  simp only [OpCode.wp_fptoui]
  have htr : truncToInt (unpackFloat .s 0x42280000#32) = some 42 := rfl
  rw [htr]
  decide

theorem fptoui_nan_ub (post : Tup Val [i32] → Prop) :
    ¬ (OpCode.fptoui .s 32).wp (0x7fc00000#32, ()) post := by
  simp only [OpCode.wp_fptoui]
  have htr : truncToInt (unpackFloat .s 0x7fc00000#32) = none := by decide
  rw [htr]
  exact id

theorem fcvt_concrete :
    (OpCode.fcvt .s .d).wp (0x3f800000#32, ()) (fun (r, ()) => r = 0x3ff0000000000000#64) := by
  simp only [OpCode.wp_fcvt]
  rfl

theorem fcvt_nan_forall (post : Tup Val [f64] → Prop)
    (h : ∀ r : BitVec 64, isFloatNaN .d r = true → post (r, ())) :
    (OpCode.fcvt .s .d).wp (0x7fc00000#32, ()) post := by
  have heq : convertFloat .s .d 0x7fc00000#32 (fun r => post (r, ())) =
      (∀ r : BitVec 64, isFloatNaN .d r = true → post (r, ())) := rfl
  simpa [OpCode.wp_fcvt, heq] using h

theorem ternlog_concrete (a b c : BitVec 8) :
    (OpCode.ternlog i8 0xca#8).wp (a, b, c, ())
      (fun (r, ()) => r = ternaryLogic a b c 0xca#8) := by
  simp [OpCode.wp_ternlog, lift3]

theorem ternlog_ite_eval :
    (OpCode.ternlog i8 0xca#8).wp (0xf0#8, 0xaa#8, 0x55#8, ())
      (fun (r, ()) => r = ((0xf0#8 &&& 0xaa#8) ||| (~~~0xf0#8 &&& 0x55#8))) := by
  simp only [OpCode.wp_ternlog]
  decide

theorem shufd_concrete :
    (OpCode.shufd v4i32 0b00_01_10_11#8).wp (((1, 2), (3, 4)), ())
      (fun (r, ()) => r = ((4, 3), (2, 1))) := by
  simp only [OpCode.wp_shufd]
  decide

theorem shufb_concrete :
    (OpCode.shufb v4i32).wp
      (((0x04030201#32, 0), (0, 0)),
       ((0x80_00_01_02#32, 0x80808080#32), (0x80808080#32, 0x80808080#32)), ())
      (fun (r, ()) => r = ((0x00010203#32, 0), (0, 0))) := by
  simp only [OpCode.wp_shufb]
  decide

theorem alignr_concrete :
    (OpCode.alignr v4i32 4#8).wp
      (((0x44332211#32, 0), (0, 0)), ((0, 0), (0, 0xddccbbaa#32)), ())
      (fun (r, ()) => r = ((0, 0), (0xddccbbaa#32, 0x44332211#32))) := by
  simp only [OpCode.wp_alignr]
  decide

theorem blendw_concrete :
    (OpCode.blendw v4i32 0x0f#8).wp (((1, 2), (3, 4)), ((5, 6), (7, 8)), ())
      (fun (r, ()) => r = ((5, 6), (3, 4))) := by
  simp only [OpCode.wp_blendw]
  decide

theorem sha256rnds2_concrete :
    (OpCode.sha256rnds2).wp (((0, 0), (0, 0)), ((0, 0), (0, 0)), ((0, 0), (0, 0)), ())
      (fun (r, ()) => r = ((0x00000000#32, 0#32), (0#32, 0#32))) := by
  simp only [OpCode.wp_sha256rnds2]
  decide

theorem sha256msg1_concrete :
    (OpCode.sha256msg1).wp (((0, 1), (0, 0)), ((0, 0), (0, 0)), ())
      (fun (r, ()) => r = ((0x02004000#32, 1), (0, 0))) := by
  simp only [OpCode.wp_sha256msg1]
  decide

theorem fshl_concrete :
    (OpCode.fshl 32).wp (0x12345678#32, 0x9abcdef0#32, 8#32, ())
      (fun (r, ()) => r = 0x3456789a#32) := by
  simp only [OpCode.wp_fshl]
  decide

theorem fshr_concrete :
    (OpCode.fshr 32).wp (0x12345678#32, 0x9abcdef0#32, 8#32, ())
      (fun (r, ()) => r = 0x789abcde#32) := by
  simp only [OpCode.wp_fshr]
  decide

theorem bswap_concrete :
    (OpCode.bswap i32).wp (0x12345678#32, ()) (fun (r, ()) => r = 0x78563412#32) := by
  simp only [OpCode.wp_bswap]
  decide

theorem smulw_concrete :
    (OpCode.smulw 8).wp (0xff#8, 0xfe#8, ()) (fun (lo, hi, ()) => lo = 2#8 ∧ hi = 0#8) := by
  simp only [OpCode.wp_smulw]
  decide

theorem opcode_decEq_test :
    (⟨_, _, OpCode.blend v4i32⟩ : (sig : List Ty) × (rs : List Ty) × OpCode sig rs) ≠
      ⟨_, _, OpCode.blend v8i32⟩ := by
  decide

theorem opcode_decEq_same :
    OpCode.blend v4i32 = OpCode.blend v4i32 := by
  decide

theorem opcode_decEq_cmp_fcmp_bitcast :
    (⟨_, _, OpCode.cmp .ult v4i32⟩ : (sig : List Ty) × (rs : List Ty) × OpCode sig rs) ≠
      ⟨_, _, OpCode.cmp .eq v4i32⟩ ∧
    (OpCode.fcmp .lt v4f32 = OpCode.fcmp .lt v4f32) ∧
    (OpCode.bitcast v4i32 (.pair i64 i64) rfl = OpCode.bitcast v4i32 (Ty.vec 1 i64) rfl) ∧
    (⟨_, _, OpCode.bitcast v4i32 (.pair i64 i64) rfl⟩ :
        (sig : List Ty) × (rs : List Ty) × OpCode sig rs) ≠
      ⟨_, _, OpCode.bitcast v4i32 (.bits 128) rfl⟩ := by
  decide

/-! ## 7. Coverage of remaining integer, bitwise, SHA-256, and IEEE float opcodes -/

theorem sha256rnds2_fips :
    (OpCode.sha256rnds2).wp
      (((0x5be0cd19#32, 0x1f83d9ab#32), (0xa54ff53a#32, 0x3c6ef372#32)),
       ((0x9b05688c#32, 0x510e527f#32), (0xbb67ae85#32, 0x6a09e667#32)),
       ((0xa3eca318#32, 0x71374491#32), (0#32, 0#32)), ())
      (fun (r, ()) =>
        r = ((0xfa2a5622#32, 0x78d689cb#32), (0x5d6afbcd#32, 0xdab2e5ef#32))) := by
  simp only [OpCode.wp_sha256rnds2]
  decide

theorem sha256msg2_concrete :
    (OpCode.sha256msg2).wp
      (((0x11111111#32, 0x22222222#32), (0x33333333#32, 0x44444444#32)),
       ((0#32, 0#32), (0x00000001#32, 0x00000002#32)), ())
      (fun (r, ()) =>
        r = ((0x1111b111#32, 0x22236222#32), (0x21e221f9#32, 0x21a221d1#32))) := by
  simp only [OpCode.wp_sha256msg2]
  decide

theorem scalar_int_ops_concrete :
    (OpCode.copy i32).wp (42#32, ()) (fun (r, ()) => r = 42#32) ∧
    (OpCode.mul i32).wp (6#32, 7#32, ()) (fun (r, ()) => r = 42#32) ∧
    (OpCode.neg i32).wp (5#32, ()) (fun (r, ()) => r = 0xfffffffb#32) ∧
    (OpCode.and i32).wp (0xf0#32, 0x3c#32, ()) (fun (r, ()) => r = 0x30#32) ∧
    (OpCode.or i32).wp (0xf0#32, 0x3c#32, ()) (fun (r, ()) => r = 0xfc#32) ∧
    (OpCode.xor i32).wp (0xf0#32, 0x3c#32, ()) (fun (r, ()) => r = 0xcc#32) ∧
    (OpCode.not i8).wp (0x0f#8, ()) (fun (r, ()) => r = 0xf0#8) ∧
    (OpCode.shl i32).wp (3#32, 4#32, ()) (fun (r, ()) => r = 48#32) ∧
    (OpCode.lshr i32).wp (0x80000000#32, 4#32, ()) (fun (r, ()) => r = 0x08000000#32) ∧
    (OpCode.ashr i32).wp (0x80000000#32, 4#32, ()) (fun (r, ()) => r = 0xf8000000#32) ∧
    (OpCode.rotr i32).wp (1#32, 1#32, ()) (fun (r, ()) => r = 0x80000000#32) ∧
    (OpCode.select i32).wp (false, 10#32, 20#32, ()) (fun (r, ()) => r = 20#32) := by
  simp only [OpCode.wp_copy, OpCode.wp_mul, OpCode.wp_neg, OpCode.wp_and, OpCode.wp_or,
    OpCode.wp_xor, OpCode.wp_not, OpCode.wp_shl, OpCode.wp_lshr, OpCode.wp_ashr, OpCode.wp_rotr,
    OpCode.wp_select]
  decide

theorem bit_manip_ops_concrete :
    (OpCode.clz 32).wp (0x00100000#32, ()) (fun (r, ()) => r = 11#32) ∧
    (OpCode.cls 32).wp (0xfffffff0#32, ()) (fun (r, ()) => r = 27#32) ∧
    (OpCode.rbit 8).wp (0b10110000#8, ()) (fun (r, ()) => r = 0b00001101#8) ∧
    (OpCode.ctz 32).wp (0x00000100#32, ()) (fun (r, ()) => r = 8#32) ∧
    (OpCode.popcnt 8).wp (0x55#8, ()) (fun (r, ()) => r = 4#8) ∧
    (OpCode.sext 8 32).wp (0xfe#8, ()) (fun (r, ()) => r = 0xfffffffe#32) ∧
    (OpCode.trunc 32 8).wp (0x1234#32, ()) (fun (r, ()) => r = 0x34#8) ∧
    (OpCode.ofBool 32).wp (true, ()) (fun (r, ()) => r = 1#32) := by
  simp only [OpCode.wp_clz, OpCode.wp_cls, OpCode.wp_rbit, OpCode.wp_ctz, OpCode.wp_popcnt,
    OpCode.wp_sext, OpCode.wp_trunc, OpCode.wp_ofBool]
  have hrev : (0x00000100#32).reverse = 0x00800000#32 := by
    ext i hi
    simp only [BitVec.getElem_reverse]
    revert i hi
    decide
  rw [hrev]
  decide

theorem div_rem_ops_edge_cases :
    (OpCode.urem 32).wp (17#32, 5#32, ()) (fun (r, ()) => r = 2#32) ∧
    (OpCode.srem 32).wp (BitVec.ofInt 32 (-7), 2#32, ())
      (fun (r, ()) => r = BitVec.ofInt 32 (-1)) ∧
    (OpCode.sdiv0 32).wp (42#32, 0#32, ()) (fun (r, ()) => r = 0#32) := by
  simp only [OpCode.wp_urem, OpCode.wp_srem, OpCode.wp_sdiv0]
  decide

theorem urem_zero_ub (a : BitVec 64) (post : Tup Val [i64] → Prop) :
    ¬ (OpCode.urem 64).wp (a, 0#64, ()) post := by
  simp [OpCode.wp_urem]

theorem srem_overflow_ub (post : Tup Val [i64] → Prop) :
    ¬ (OpCode.srem 64).wp (BitVec.intMin 64, BitVec.allOnes 64, ()) post := by
  simp only [OpCode.wp_srem, sdivDefined]
  intro ⟨h, _⟩
  exact absurd h (by decide)

theorem sdiv0_overflow :
    (OpCode.sdiv0 64).wp (BitVec.intMin 64, BitVec.allOnes 64, ())
      (fun (r, ()) => r = BitVec.intMin 64) := by
  simp only [OpCode.wp_sdiv0]
  decide

private theorem nat_sqrt_eq_of_bounds {m k : Nat} (h1 : k * k ≤ m)
    (h2 : m < (k + 1) * (k + 1)) : Nat.sqrt m = k := by
  have hle := Nat.sqrt_le m
  have hlt := Nat.lt_succ_sqrt m
  rcases Nat.lt_trichotomy m.sqrt k with hlt' | heq | hgt'
  · have h3 : (m.sqrt + 1) * (m.sqrt + 1) ≤ k * k := Nat.mul_le_mul hlt' hlt'
    exact absurd (Nat.lt_of_lt_of_le hlt (Nat.le_trans h3 h1)) (Nat.lt_irrefl _)
  · exact heq
  · have h3 : (k + 1) * (k + 1) ≤ m.sqrt * m.sqrt := Nat.mul_le_mul hgt' hgt'
    exact absurd (Nat.lt_of_lt_of_le h2 (Nat.le_trans h3 hle)) (Nat.lt_irrefl _)

theorem fsub_fmul_fdiv_ffma_fsqrt_concrete :
    (OpCode.fsub f32).wp (0x3f800000#32, 0x40000000#32, ()) (fun (r, ()) => r = 0xbf800000#32) ∧
    (OpCode.fmul f32).wp (0x3fc00000#32, 0x40000000#32, ()) (fun (r, ()) => r = 0x40400000#32) ∧
    (OpCode.fdiv f32).wp (0x3f800000#32, 0x00000000#32, ()) (fun (r, ()) => r = 0x7f800000#32) ∧
    (OpCode.ffma f32).wp (0x3fc00000#32, 0x40000000#32, 0x3e800000#32, ())
      (fun (r, ()) => r = 0x40500000#32) ∧
    (OpCode.fsqrt f32).wp (0x80000000#32, ()) (fun (r, ()) => r = 0x80000000#32) := by
  simp only [OpCode.wp_fsub, OpCode.wp_fmul, OpCode.wp_fdiv, OpCode.wp_ffma, OpCode.wp_fsqrt,
    Ty.isFloatTree, Bool.not_true, Bool.false_eq_true, ↓reduceIte, liftFloatRel1, liftFloatRel2,
    liftFloatRel3, floatResultWp]
  decide

theorem fsqrt_four_eq_two :
    (OpCode.fsqrt f32).wp (0x40800000#32, ()) (fun (r, ()) => r = 0x40000000#32) := by
  simp only [OpCode.wp_fsqrt, Ty.isFloatTree, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    liftFloatRel1, floatResultWp]
  have h : Float.Model.UnpackedFloat.sqrt Fmt.s.format (unpackFloat .s 0x40800000#32) =
      Float.Model.UnpackedFloat.roundWithAccuracy Fmt.s.format .positive (2 ^ 23) (-22) .exact := by
    have hunp : unpackFloat .s 0x40800000#32 = .finite .positive (2 ^ 23) (-21) (by decide) := rfl
    rw [hunp]
    simp only [Float.Model.UnpackedFloat.sqrt, Float.Model.UnpackedFloat.sqrtCore]
    have hte : min ((-21 : Int).ediv 2)
        (Fmt.s.format.targetExponent ((Float.Model.totalExponent (2 ^ 23) (-21) + 1).ediv 2)) =
        -22 := by
      decide
    rw [hte]
    have hs : (-21 - 2 * (-22 : Int)).toNat = 23 := by decide
    rw [hs]
    have hsq : Nat.sqrt (2 ^ 23 <<< 23) = 2 ^ 23 := by
      apply nat_sqrt_eq_of_bounds <;> decide
    rw [hsq]
    have hrem : 2 ^ 23 <<< 23 - 2 ^ 23 * 2 ^ 23 = 0 := by decide
    rw [hrem]
    rfl
  rw [h]
  decide

theorem fdiv_nan_forall (post : Tup Val [f32] → Prop)
    (h : ∀ r : BitVec 32, isFloatNaN .s r = true → post (r, ())) :
    (OpCode.fdiv f32).wp (0x00000000#32, 0x00000000#32, ()) post := by
  simp only [OpCode.wp_fdiv, Ty.isFloatTree, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    liftFloatRel2, floatResultWp]
  have hnan : (Float.Model.UnpackedFloat.div Fmt.s.format
      (unpackFloat .s 0x00000000#32) (unpackFloat .s 0x00000000#32)).isNaN = true := by decide
  simpa [hnan] using h

theorem fsqrt_nan_forall (post : Tup Val [f32] → Prop)
    (h : ∀ r : BitVec 32, isFloatNaN .s r = true → post (r, ())) :
    (OpCode.fsqrt f32).wp (0xbf800000#32, ()) post := by
  simp only [OpCode.wp_fsqrt, Ty.isFloatTree, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    liftFloatRel1, floatResultWp]
  have hnan : (Float.Model.UnpackedFloat.sqrt Fmt.s.format
      (unpackFloat .s 0xbf800000#32)).isNaN = true := by decide
  simpa [hnan] using h

theorem fneg_fabs_fcmp_edge_cases :
    (OpCode.fneg f32).wp (0x7f800001#32, ()) (fun (r, ()) => r = 0xff800001#32) ∧
    (OpCode.fabs f32).wp (0xff800001#32, ()) (fun (r, ()) => r = 0x7f800001#32) ∧
    (OpCode.fcmp .eq f32).wp (0x80000000#32, 0x00000000#32, ()) (fun (r, ()) => r = true) := by
  simp only [OpCode.wp_fneg, OpCode.wp_fabs, OpCode.wp_fcmp, cast_eq]
  decide

theorem fptoui_neg_half :
    (OpCode.fptoui .s 32).wp (0xbf000000#32, ()) (fun (r, ()) => r = 0#32) := by
  simp only [OpCode.wp_fptoui]
  have h : truncToInt (unpackFloat .s 0xbf000000#32) = some 0 := by decide
  rw [h]; decide

theorem fptoui_neg_one_ub (post : Tup Val [i32] → Prop) :
    ¬ (OpCode.fptoui .s 32).wp (0xbf800000#32, ()) post := by
  simp only [OpCode.wp_fptoui]
  have h : truncToInt (unpackFloat .s 0xbf800000#32) = some (-1) := by decide
  rw [h]; omega

theorem sitofp_concrete :
    (OpCode.sitofp 32 .s).wp (BitVec.ofInt 32 (-42), ())
      (fun (r, ()) => r = 0xc2280000#32) := by
  simp only [OpCode.wp_sitofp]
  decide

theorem fptosi_concrete :
    (OpCode.fptosi .s 32).wp (0xc22b0000#32, ())
      (fun (r, ()) => r = BitVec.ofInt 32 (-42)) := by
  simp only [OpCode.wp_fptosi]
  have h : truncToInt (unpackFloat .s 0xc22b0000#32) = some (-42) := by decide
  rw [h]; decide

theorem fptosi_overflow_ub (post : Tup Val [i32] → Prop) :
    ¬ (OpCode.fptosi .d 32).wp (0xc1e0000000200000#64, ()) post := by
  simp only [OpCode.wp_fptosi]
  have h : truncToInt (unpackFloat .d 0xc1e0000000200000#64) = some (-2147483649) := by decide
  rw [h]; omega

theorem fcvt_edge_cases :
    (OpCode.fcvt .d .h).wp (0x3f00000000000000#64, ()) (fun (r, ()) => r = 0x0200#16) ∧
    (OpCode.fcvt .d .h).wp (0x40f0000000000000#64, ()) (fun (r, ()) => r = 0x7c00#16) ∧
    (OpCode.fcvt .d .h).wp (0xbe10000000000000#64, ()) (fun (r, ()) => r = 0x8000#16) := by
  simp only [OpCode.wp_fcvt]
  exact ⟨rfl, rfl, rfl⟩

/-! ## 8. T1 review cleanups: `zext`/`sext`/`trunc` direction UB, `bool` load ∈ `{0,1}`, `fcmp .ne` -/

theorem ext_trunc_wrong_direction_ub (a64 : BitVec 64) (a32 : BitVec 32)
    (p32 : Tup Val [i32] → Prop) (p64 : Tup Val [i64] → Prop) :
    ¬ (OpCode.zext 64 32).wp (a64, ()) p32 ∧
    ¬ (OpCode.sext 64 32).wp (a64, ()) p32 ∧
    ¬ (OpCode.trunc 32 64).wp (a32, ()) p64 := by
  simp only [OpCode.wp_zext, OpCode.wp_sext, OpCode.wp_trunc]
  refine ⟨fun h => by omega, fun h => by omega, fun h => by omega⟩

theorem load_bool_invalid_byte_ub (Γ : Env) (X : XPost) (p : BitVec 64) (m : Mem 64)
    (b : UInt8) (hget : m.get? p = some b) (hgt : 1 < b.toNat) :
    ¬ wp Γ (rs := [.bool]) (fun _ _ => True) X
        (.load .bool (.var p) fun y => .ret (.var y, ())) m := by
  simp only [wp_load, Arg.val_var]
  rintro ⟨v, hv, _⟩
  rw [loadVal_bool_invalid m p b hget hgt] at hv
  cases hv

theorem store_load_bool_roundtrip (Γ : Env) (X : XPost) (b : Bool) (p : BitVec 64) (m : Mem 64)
    (hok : storeOk m .bool p) :
    wp Γ (rs := [.bool]) (fun (r, _) _ => r = b) X
      (.store (t := .bool) (.imm b) (.imm p) (.load .bool (.imm p) fun y => .ret (.var y, ()))) m := by
  simp only [wp_store, wp_load, wp_ret, vals, Arg.val_imm, Arg.val_var]
  exact ⟨hok, b, loadVal_storeMem m .bool p b (by decide), rfl⟩

theorem fcmp_ne_nan_unordered_true :
    (OpCode.fcmp .ne f32).wp (0x7fc00000#32, 0x3f800000#32, ()) (fun (r, ()) => r = true) ∧
    (OpCode.fcmp .eq f32).wp (0x7fc00000#32, 0x3f800000#32, ()) (fun (r, ()) => r = false) := by
  simp only [OpCode.wp_fcmp, cast_eq]
  decide

end LeanQbe.T.Smoke
