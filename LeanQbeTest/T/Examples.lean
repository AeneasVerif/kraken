module

public import LeanQbe.T.WPLemmas

/-!
# Eight Example Programs and Specifications in `LeanQbe.T`

1. `add128` (`unpair`, `addc`, `mkpair`)
2. `add256` via generic `addLimbs`
3. `mac` (`umulw` + `addc` chain)
4. `ult128` (`subb` chain returning `Bool`)
5. `umin` (`ult` + `select`)
6. `mulByAdd` (`loop1` + `wp_loop1`)
7. `qrStep` (`add`, `xor`, `rotl` on `v4i32`, plus `add_v8_split` and `bitcast` layout)
8. `vumin` (`ult` + variant-C `blend` on `Ty.vec k i32`, proved for all `k`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples

/-- A 128-bit integer as a pair of 64-bit limbs (low limb first). -/
abbrev u128 : Ty := .pair i64 i64

def U128.toNat (p : Val u128) : Nat := p.2.toNat * 2 ^ 64 + p.1.toNat

/-! ## 1. 128-bit addition on pairs -/

def add128 : Func [u128, u128] [u128, .bool] := fun _ _ (a, b, ()) =>
  .let_ (op1 (.unpair i64 i64) (.var a)) fun (a0, a1, ()) =>
  .let_ (op1 (.unpair i64 i64) (.var b)) fun (b0, b1, ()) =>
  .let_ (op3 (.addc 64) (.var a0) (.var b0) (.imm false)) fun (s0, c0, ()) =>
  .let_ (op3 (.addc 64) (.var a1) (.var b1) (.var c0)) fun (s1, c1, ()) =>
  .let_ (op2 (.mkpair i64 i64) (.var s0) (.var s1)) fun (s, ()) =>
  .ret (.var s, .var c1, ())

theorem add128_spec (Γ : Env) (X : XPost) (m : Mem 64) (a b : Val u128) :
    Func.wp Γ add128 (a, b, ()) m
      (fun (s, c, ()) _ => c.toNat * 2 ^ 128 + U128.toNat s = U128.toNat a + U128.toNat b) X := by
  dsimp only [Func.wp, add128]
  rw [wp_let_op1, OpCode.wp_unpair, wp_let_op1, OpCode.wp_unpair]
  simp only [Arg.val_var]
  refine wp_addc _ _ _ _ fun s0 c0 h0 => ?_
  refine wp_addc _ _ _ _ fun s1 c1 h1 => ?_
  simp only [wp_let_op2, wp_ret, OpCode.wp_mkpair, vals, Arg.val_var, Arg.val_imm, U128.toNat,
    Bool.toNat_false, Nat.add_zero] at h0 h1 ⊢
  rw [show (2 ^ 128 : Nat) = 2 ^ 64 * 2 ^ 64 by rw [← Nat.pow_add]]
  calc c1.toNat * (2 ^ 64 * 2 ^ 64) + (s1.toNat * 2 ^ 64 + s0.toNat)
      = (c1.toNat * 2 ^ 64 + s1.toNat) * 2 ^ 64 + s0.toNat := by
          rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
    _ = (a.2.toNat + b.2.toNat + c0.toNat) * 2 ^ 64 + s0.toNat := by rw [h1]
    _ = (a.2.toNat * 2 ^ 64 + b.2.toNat * 2 ^ 64) + (c0.toNat * 2 ^ 64 + s0.toNat) := by
          simp only [Nat.add_mul, Nat.add_assoc]
    _ = (a.2.toNat * 2 ^ 64 + b.2.toNat * 2 ^ 64) + (a.1.toNat + b.1.toNat) := by rw [h0]
    _ = (a.2.toNat * 2 ^ 64 + a.1.toNat) + (b.2.toNat * 2 ^ 64 + b.1.toNat) := by ac_rfl

/-! ## 2. `n`-limb addition (`addLimbs` / `add256`) -/

def addLimbs {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    List (Arg V i64) → List (Arg V i64) → Arg V .bool →
    (List (Arg V i64) → Arg V .bool → Expr V L rs) → Expr V L rs
  | a :: as, b :: bs, c, k =>
    .let_ (op3 (.addc 64) a b c) fun (s, c', ()) =>
      addLimbs as bs (.var c') fun ss co => k (.var s :: ss) co
  | _, _, c, k => k [] c

def limbs : List (Arg Val i64) → Nat
  | [] => 0
  | a :: as => a.val.toNat + 2 ^ 64 * limbs as

theorem wp_addLimbs (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) (m : Mem 64) :
    ∀ (as bs : List (Arg Val i64)) (c : Arg Val .bool)
      (k : List (Arg Val i64) → Arg Val .bool → Expr Val Cont rs),
    as.length = bs.length →
    (∀ ss co, ss.length = as.length →
      limbs ss + co.val.toNat * 2 ^ (64 * as.length) = limbs as + limbs bs + c.val.toNat →
      wp Γ Q X (k ss co) m) →
    wp Γ Q X (addLimbs as bs c k) m
  | [], bs, c, k, hlen, hk => by
    cases bs with
    | nil => exact hk [] c rfl (by simp [limbs])
    | cons => simp at hlen
  | a :: as, b :: bs, c, k, hlen, hk => by
    simp only [addLimbs]
    refine wp_addc _ _ _ _ fun s c' hc' => ?_
    refine wp_addLimbs Γ Q X m as bs _ _ (by simpa using hlen) ?_
    intro ss co hss heq
    refine hk _ co (by simp [hss]) ?_
    simp only [Arg.val_var] at heq hc' ⊢
    simp only [limbs, List.length_cons, Arg.val_var]
    rw [show 64 * (as.length + 1) = 64 * as.length + 64 by omega, Nat.pow_add]
    generalize 2 ^ (64 * as.length) = P at heq ⊢
    rw [show co.val.toNat * (P * 2 ^ 64) = 2 ^ 64 * (co.val.toNat * P) by
      rw [Nat.mul_comm P, ← Nat.mul_assoc, Nat.mul_comm _ (2 ^ 64), Nat.mul_assoc]]
    generalize co.val.toNat * P = Z at heq ⊢
    omega
  | _ :: _, [], _, _, hlen, _ => by simp at hlen

def add256 : Func [i64, i64, i64, i64, i64, i64, i64, i64] [i64, i64, i64, i64, .bool] :=
  fun _ _ (a0, a1, a2, a3, b0, b1, b2, b3, ()) =>
    addLimbs [.var a0, .var a1, .var a2, .var a3] [.var b0, .var b1, .var b2, .var b3] (.imm false)
      fun ss co => match ss with
        | [s0, s1, s2, s3] => .ret (s0, s1, s2, s3, co, ())
        | _ => .hlt

theorem add256_spec (Γ : Env) (X : XPost) (m : Mem 64) (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    Func.wp Γ add256 (a0, a1, a2, a3, b0, b1, b2, b3, ()) m
      (fun (s0, s1, s2, s3, c, ()) _ =>
        limbs [.imm s0, .imm s1, .imm s2, .imm s3] + c.toNat * 2 ^ 256 =
          limbs [.imm a0, .imm a1, .imm a2, .imm a3] + limbs [.imm b0, .imm b1, .imm b2, .imm b3])
      X := by
  refine wp_addLimbs Γ _ X m _ _ _ _ rfl ?_
  intro ss co hlen heq
  rcases ss with _ | ⟨s0, _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hlen
  simp only [wp_ret, vals]
  simpa [limbs] using heq

/-! ## 3. Multiply-accumulate `a * b + c + d` in two limbs -/

def mac : Func [i64, i64, i64, i64] [i64, i64] := fun _ _ (a, b, c, d, ()) =>
  .let_ (op2 (.umulw 64) (.var a) (.var b)) fun (lo, hi, ()) =>
  .let_ (op3 (.addc 64) (.var lo) (.var c) (.imm false)) fun (lo1, c1, ()) =>
  .let_ (op3 (.addc 64) (.var hi) (.imm 0) (.var c1)) fun (hi1, _, ()) =>
  .let_ (op3 (.addc 64) (.var lo1) (.var d) (.imm false)) fun (lo2, c2, ()) =>
  .let_ (op3 (.addc 64) (.var hi1) (.imm 0) (.var c2)) fun (hi2, _, ()) =>
  .ret (.var lo2, .var hi2, ())

theorem mac_spec (Γ : Env) (X : XPost) (m : Mem 64) (a b c d : BitVec 64) :
    Func.wp Γ mac (a, b, c, d, ()) m
      (fun (lo, hi, ()) _ => hi.toNat * 2 ^ 64 + lo.toNat = a.toNat * b.toNat + c.toNat + d.toNat)
      X := by
  simp only [Func.wp, mac]
  refine wp_umulw _ _ _ fun lo hi hm => ?_
  refine wp_addc _ _ _ _ fun lo1 c1 e1 => ?_
  refine wp_addc _ _ _ _ fun hi1 x1 e2 => ?_
  refine wp_addc _ _ _ _ fun lo2 c2 e3 => ?_
  refine wp_addc _ _ _ _ fun hi2 x2 e4 => ?_
  simp only [wp_ret, vals, Arg.val_var, Arg.val_imm, Bool.toNat_false,
    Nat.add_zero] at *
  have ha : a.toNat ≤ 2 ^ 64 - 1 := Nat.le_pred_of_lt a.isLt
  have hb : b.toNat ≤ 2 ^ 64 - 1 := Nat.le_pred_of_lt b.isLt
  have hc : c.toNat ≤ 2 ^ 64 - 1 := Nat.le_pred_of_lt c.isLt
  have hd : d.toNat ≤ 2 ^ 64 - 1 := Nat.le_pred_of_lt d.isLt
  have hsum : (x1.toNat + x2.toNat) * (2 ^ 64 * 2 ^ 64) + (hi2.toNat * 2 ^ 64 + lo2.toNat) =
      a.toNat * b.toNat + c.toNat + d.toNat := by
    calc (x1.toNat + x2.toNat) * (2 ^ 64 * 2 ^ 64) + (hi2.toNat * 2 ^ 64 + lo2.toNat)
        = x1.toNat * 2 ^ 64 * 2 ^ 64 + ((x2.toNat * 2 ^ 64 + hi2.toNat) * 2 ^ 64 + lo2.toNat) := by
            simp only [Nat.add_mul, Nat.mul_assoc]; ac_rfl
      _ = x1.toNat * 2 ^ 64 * 2 ^ 64 + (hi1.toNat * 2 ^ 64 + (c2.toNat * 2 ^ 64 + lo2.toNat)) := by
            rw [e4]; simp only [Nat.add_mul]; ac_rfl
      _ = (x1.toNat * 2 ^ 64 + hi1.toNat) * 2 ^ 64 + lo1.toNat + d.toNat := by
            rw [e3, Nat.add_mul]; ac_rfl
      _ = hi.toNat * 2 ^ 64 + (c1.toNat * 2 ^ 64 + lo1.toNat) + d.toNat := by
            rw [e2, Nat.add_mul]; ac_rfl
      _ = hi.toNat * 2 ^ 64 + lo.toNat + c.toNat + d.toNat := by
            rw [e1]; ac_rfl
      _ = a.toNat * b.toNat + c.toNat + d.toNat := by rw [hm]
  have hlt : a.toNat * b.toNat + c.toNat + d.toNat < 2 ^ 64 * 2 ^ 64 := by
    have h1 : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul ha hb
    have h2 : (2 ^ 64 - 1) * (2 ^ 64 - 1) + (2 ^ 64 - 1) + (2 ^ 64 - 1) + 1 = 2 ^ 64 * 2 ^ 64 := by
      have hp : 1 ≤ (2 ^ 64 : Nat) := Nat.one_le_pow _ _ (by decide)
      generalize (2 ^ 64 : Nat) = B at hp
      cases B with
      | zero => omega
      | succ k => simp only [Nat.add_sub_cancel, Nat.succ_mul, Nat.mul_succ]; omega
    omega
  have hx : x1.toNat + x2.toNat = 0 := by
    rcases Nat.eq_zero_or_pos (x1.toNat + x2.toNat) with h0 | hpos
    · exact h0
    · have hge : 2 ^ 64 * 2 ^ 64 ≤ (x1.toNat + x2.toNat) * (2 ^ 64 * 2 ^ 64) :=
        Nat.le_mul_of_pos_left _ hpos
      omega
  rw [hx, Nat.zero_mul, Nat.zero_add] at hsum
  exact hsum

/-! ## 4. 128-bit unsigned comparison via `subb` chain -/

def ult128 : Func [u128, u128] [.bool] := fun _ _ (a, b, ()) =>
  .let_ (op1 (.unpair i64 i64) (.var a)) fun (a0, a1, ()) =>
  .let_ (op1 (.unpair i64 i64) (.var b)) fun (b0, b1, ()) =>
  .let_ (op3 (.subb 64) (.var a0) (.var b0) (.imm false)) fun (_, w0, ()) =>
  .let_ (op3 (.subb 64) (.var a1) (.var b1) (.var w0)) fun (_, w1, ()) =>
  .ret (.var w1, ())

theorem ult128_spec (Γ : Env) (X : XPost) (m : Mem 64) (a b : Val u128) :
    Func.wp Γ ult128 (a, b, ()) m
      (fun (r, ()) _ => r = decide (U128.toNat a < U128.toNat b)) X := by
  dsimp only [Func.wp, ult128]
  rw [wp_let_op1, OpCode.wp_unpair, wp_let_op1, OpCode.wp_unpair]
  simp only [wp_let_op3, wp_ret, OpCode.wp_subb, vals, Arg.val_var, Arg.val_imm, U128.toNat,
    Bool.toNat_false, Nat.add_zero]
  have := a.1.isLt; have := b.1.isLt
  by_cases h : a.1.toNat < b.1.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
    (apply decide_eq_decide.2; omega)

/-! ## 5. Branchless unsigned minimum (`ult` + `select`) -/

def umin : Func [i64, i64] [i64] := fun _ _ (a, b, ()) =>
  .let_ (op2 (.ult i64) (.var a) (.var b)) fun (c, ()) =>
  .let_ (op3 (.select i64) (.var c) (.var a) (.var b)) fun (r, ()) =>
  .ret (.var r, ())

theorem umin_spec (Γ : Env) (X : XPost) (m : Mem 64) (a b : BitVec 64) :
    Func.wp Γ umin (a, b, ()) m (fun (r, ()) _ => r.toNat = min a.toNat b.toNat) X := by
  simp only [Func.wp, umin, wp_let_op2, wp_let_op3, wp_ret, OpCode.ult, OpCode.wp_cmp,
    OpCode.wp_select, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits,
    cast_eq, vals, Arg.val_var]
  by_cases h : a.toNat < b.toNat
  · have : a.ult b = true := by simpa [BitVec.ult] using h
    simp [this]; omega
  · have : a.ult b = false := by simpa [BitVec.ult] using h
    simp [this]; omega

/-! ## 6. Loop with a typed tuple state (`mulByAdd`) -/

def mulByAdd : Func [i64, i64] [i64, i64] := fun _ _ (n, b, ()) =>
  loop1 (ts := [i64, i64, i64])
    (fun loop (i, lo, hi, ()) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (z, ()) =>
      .jnz (.var z) (.ret (.var lo, .var hi, ()))
        (.let_ (op3 (.addc 64) (.var lo) (.var b) (.imm false)) fun (lo', c, ()) =>
         .let_ (op3 (.addc 64) (.var hi) (.imm 0) (.var c)) fun (hi', _, ()) =>
         .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
         .jump loop (.var i', .var lo', .var hi', ())))
    (fun loop => .jump loop (.var n, .imm 0, .imm 0, ()))

theorem mulByAdd_spec (Γ : Env) (X : XPost) (m : Mem 64) (n b : BitVec 64) :
    Func.wp Γ mulByAdd (n, b, ()) m
      (fun (lo, hi, ()) _ => hi.toNat * 2 ^ 64 + lo.toNat = n.toNat * b.toNat) X := by
  unfold Func.wp mulByAdd
  dsimp only
  refine wp_loop1 _ _
    (fun k (x : Tup Val [i64, i64, i64]) _ =>
      x.1.toNat = k ∧ x.2.2.1.toNat * 2 ^ 64 + x.2.1.toNat + k * b.toNat = n.toNat * b.toNat)
    ?_ ?_
  · rintro J k ⟨i, lo, hi, ⟨⟩⟩ m hJ ⟨hk, hinv⟩
    dsimp only at hk hinv
    simp only [wp_let_op2, wp_jnz, wp_ret, vals, Arg.val_var, Arg.val_imm, OpCode.eq,
      OpCode.wp_cmp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits,
      cast_eq]
    have hnb : n.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul_of_lt_of_lt n.isLt b.isLt
    by_cases hz : i = 0
    · subst hz
      simp at hk; subst hk
      simp only [Nat.zero_mul, Nat.add_zero] at hinv
      simp [hinv]
    · have hi0 : i.toNat ≠ 0 := by
        intro h; exact hz (BitVec.eq_of_toNat_eq (by simpa using h))
      simp only [hz, decide_false]
      refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
      refine wp_addc _ _ _ _ fun lo' c e1 => ?_
      refine wp_addc _ _ _ _ fun hi' x e2 => ?_
      simp only [wp_let_op2, wp_jump, OpCode.wp_sub, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
        lift2, vals, Arg.val_var, Arg.val_imm, Bool.toNat_false, Nat.add_zero] at e1 e2 ⊢
      refine hJ (k - 1) _ m (by omega) ?_
      have hsub : (i - 1).toNat = i.toNat - 1 :=
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)
      refine ⟨by simp only; rw [hsub]; omega, ?_⟩
      have hstep : x.toNat * (2 ^ 64 * 2 ^ 64) + (hi'.toNat * 2 ^ 64 + lo'.toNat) +
          (k - 1) * b.toNat = n.toNat * b.toNat := by
        have hkb : (k - 1) * b.toNat + b.toNat = k * b.toNat := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
        calc x.toNat * (2 ^ 64 * 2 ^ 64) + (hi'.toNat * 2 ^ 64 + lo'.toNat) + (k - 1) * b.toNat
            = (x.toNat * 2 ^ 64 + hi'.toNat) * 2 ^ 64 + lo'.toNat + (k - 1) * b.toNat := by
                simp only [Nat.add_mul, Nat.mul_assoc]; ac_rfl
          _ = (hi.toNat + c.toNat) * 2 ^ 64 + lo'.toNat + (k - 1) * b.toNat := by
                rw [e2, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero]
          _ = hi.toNat * 2 ^ 64 + (c.toNat * 2 ^ 64 + lo'.toNat) + (k - 1) * b.toNat := by
                rw [Nat.add_mul]; ac_rfl
          _ = hi.toNat * 2 ^ 64 + lo.toNat + ((k - 1) * b.toNat + b.toNat) := by
                rw [e1]; ac_rfl
          _ = hi.toNat * 2 ^ 64 + lo.toNat + k * b.toNat := by rw [hkb]
          _ = n.toNat * b.toNat := hinv
      have hx : x.toNat = 0 := by
        rcases Nat.eq_zero_or_pos x.toNat with h0 | hpos
        · exact h0
        · have hge : 2 ^ 64 * 2 ^ 64 ≤ x.toNat * (2 ^ 64 * 2 ^ 64) :=
            Nat.le_mul_of_pos_left _ hpos
          omega
      rw [hx, Nat.zero_mul, Nat.zero_add] at hstep
      exact hstep
  · intro J hJ
    simp only [wp_jump, vals, Arg.val_var, Arg.val_imm]
    exact hJ n.toNat _ m ⟨rfl, by simp⟩

/-! ## 7. Vectors as balanced `pair` trees (`qrStep`, `add_v8_split`, `vumin`, `bitcast`) -/

/-- A ChaCha-style step on four 32-bit lanes: `a += b; d ^= a; d <<<= 16`. -/
def qrStep : Func [v4i32, v4i32, v4i32] [v4i32, v4i32] := fun _ _ (a, b, d, ()) =>
  .let_ (op2 (.add v4i32) (.var a) (.var b)) fun (a', ()) =>
  .let_ (op2 (.xor v4i32) (.var d) (.var a')) fun (x, ()) =>
  .let_ (op2 (.rotl v4i32) (.var x) (.imm ((16, 16), (16, 16)))) fun (d', ()) =>
  .ret (.var a', .var d', ())

theorem qrStep_spec (Γ : Env) (X : XPost) (m : Mem 64)
    (a0 a1 a2 a3 b0 b1 b2 b3 d0 d1 d2 d3 : BitVec 32) :
    Func.wp Γ qrStep
      (((a0, a1), (a2, a3)), ((b0, b1), (b2, b3)), ((d0, d1), (d2, d3)), ()) m
      (fun (a', d', ()) _ =>
        a' = ((a0 + b0, a1 + b1), (a2 + b2, a3 + b3)) ∧
        d' = (((d0 ^^^ (a0 + b0)).rotateLeft 16, (d1 ^^^ (a1 + b1)).rotateLeft 16),
              ((d2 ^^^ (a2 + b2)).rotateLeft 16, (d3 ^^^ (a3 + b3)).rotateLeft 16))) X := by
  simp only [Func.wp, qrStep, wp_let_op2, wp_ret, OpCode.wp_add, OpCode.wp_xor, OpCode.wp_rotl,
    Ty.hasFloat, Bool.false_or, Bool.false_eq_true, ↓reduceIte, lift2, vals, Arg.val_var,
    Arg.val_imm]
  exact ⟨trivial, rfl⟩

/-- Split legalisation is definitional: an 8-lane add is two 4-lane adds. -/
theorem add_v8_split (a b : Val v8i32) (post : Tup Val [v8i32] → Prop) :
    (OpCode.add v8i32).wp (a, b, ()) post =
      (OpCode.add v4i32).wp (a.1, b.1, ()) fun (r1, ()) =>
        (OpCode.add v4i32).wp (a.2, b.2, ()) fun (r2, ()) => post ((r1, r2), ()) := rfl

/-! ## 8. Width-generic vector minimum (`vumin`) using variant-C `blend` -/

def vumin (k : Nat) : Func [Ty.vec k i32, Ty.vec k i32] [Ty.vec k i32] := fun _ _ (a, b, ()) =>
  .let_ (op2 (.ult (Ty.vec k i32)) (.var a) (.var b)) fun (c, ()) =>
  .let_ (op3 (.blend (Ty.vec k i32)) (.var c) (.var a) (.var b)) fun (r, ()) =>
  .ret (.var r, ())

/-- "Every lane of `r` is the minimum of the lanes of `a` and `b`." -/
def LanewiseMin : (k : Nat) → Val (Ty.vec k i32) → Val (Ty.vec k i32) →
    Val (Ty.vec k i32) → Prop
  | 0, r, a, b => r.toNat = min a.toNat b.toNat
  | k + 1, r, a, b => LanewiseMin k r.1 a.1 b.1 ∧ LanewiseMin k r.2 a.2 b.2

theorem blend_ult_min : ∀ (k : Nat) (a b : Val (Ty.vec k i32)),
    LanewiseMin k
      (blendV (Ty.vec k i32)
        (liftCmp (CmpOp.evalBits .ult) (CmpOp.evalBool .ult) (Ty.vec k i32) a b) a b) a b
  | 0, a, b => by
    simp only [LanewiseMin, blendV, liftCmp, CmpOp.evalBits]
    by_cases h : a.toNat < b.toNat
    · have hu : a.ult b = true := by simpa [BitVec.ult] using h
      simp [hu]; omega
    · have hu : a.ult b = false := by simpa [BitVec.ult] using h
      simp [hu]; omega
  | k + 1, a, b => ⟨blend_ult_min k a.1 b.1, blend_ult_min k a.2 b.2⟩

/-- One proof for every vector width (`4`, `8`, `16`, … lanes), by induction on the tree. -/
theorem vumin_spec (k : Nat) (Γ : Env) (X : XPost) (m : Mem 64) (a b : Val (Ty.vec k i32)) :
    Func.wp Γ (vumin k) (a, b, ()) m (fun (r, ()) _ => LanewiseMin k r a b) X := by
  simp only [Func.wp, vumin, wp_let_op2, wp_let_op3, wp_ret, OpCode.ult, OpCode.wp_cmp,
    OpCode.wp_blend, Ty.hasFloat_vec, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, cast_eq,
    vals, Arg.val_var]
  exact blend_ult_min k a b

/-- Memory/bitcast layout: the first component is in the low bits. -/
theorem bitcast_v4i32_u128 :
    (OpCode.bitcast v4i32 u128 rfl).wp (((1, 2), (3, 4)), ())
      (fun (r, ()) => r = (0x0000000200000001, 0x0000000400000003)) := by
  simp only [OpCode.wp_bitcast]
  decide

end LeanQbe.T.Examples
