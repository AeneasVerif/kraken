module

public import LeanQbe.T.AddrRangeOpt
public import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.OpsLemmas

/-!
# Helper Identities & `ARGood` Invariant for `Func.addrRangeOpt` (`AddrRangeOptLemmas0`)

Proves pure `BitVec` address reassociation and range-check identities, the `ARGood`
semantic invariant, and single-step `record*Prov_good` / `try*` soundness lemmas for
`AddrRangeOptLemmas`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## Pure `BitVec` address reassociation identities -/

theorem bv_shl_add {n : Nat} (a b : BitVec n) (k : Nat) :
    (a + b) <<< k = (a <<< k) + (b <<< k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq]
  rw [Nat.mod_mul_mod, Nat.add_mul, Nat.add_mod]

theorem bv_shl_sub {n : Nat} (a b : BitVec n) (k : Nat) :
    (a - b) <<< k = (a <<< k) - (b <<< k) := by
  have h := bv_shl_add (a - b) b k
  rw [BitVec.sub_add_cancel] at h
  have h2 := congrArg (· - (b <<< k)) h
  simpa [BitVec.add_sub_cancel] using h2.symm

theorem bv_shl_shl_add {n : Nat} (a : BitVec n) (k₁ k₂ : Nat) :
    (a <<< k₁) <<< k₂ = a <<< (k₁ + k₂) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_add]

theorem bv_add_shl_add_disp {n : Nat} (base inv iv disp : BitVec n) (sh : Nat) :
    ((base + (inv <<< sh)) + (iv <<< sh)) + disp = base + (((inv + iv) <<< sh) + disp) := by
  rw [bv_shl_add, BitVec.add_assoc base (inv <<< sh) (iv <<< sh), BitVec.add_assoc]

theorem bv_add_shl_sub_disp {n : Nat} (base inv iv disp : BitVec n) (sh : Nat) :
    ((base - (inv <<< sh)) + (iv <<< sh)) + disp = base + (((iv - inv) <<< sh) + disp) := by
  rw [bv_shl_sub, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg,
    BitVec.add_assoc base (-(inv <<< sh)) (iv <<< sh),
    BitVec.add_comm (-(inv <<< sh)) (iv <<< sh),
    BitVec.add_assoc]

theorem bv_add_add_disp {n : Nat} (base inv iv disp : BitVec n) :
    ((base + inv) + iv) + disp = base + ((inv + iv) + disp) := by
  rw [BitVec.add_assoc base inv iv, BitVec.add_assoc]

theorem bv_add_sub_disp {n : Nat} (base inv iv disp : BitVec n) :
    ((base - inv) + iv) + disp = base + ((iv - inv) + disp) := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg,
    BitVec.add_assoc base (-inv) iv, BitVec.add_comm (-inv) iv, BitVec.add_assoc]

/-! ## Pure `BitVec` range-check identities -/

/-- Semantic evaluation of a normalized `RangeBound w` on `x`. -/
@[expose] def RangeBound.eval {w : Nat} (x : BitVec w) : RangeBound w → Bool
  | .ge false lo => lo.ule x
  | .lt false hi => x.ult hi
  | .ge true lo => lo.sle x
  | .lt true hi => x.slt hi

private theorem toNat_add_one_of_ne_allOnes {w : Nat} {c : BitVec w} (h : c ≠ BitVec.allOnes w) :
    (c + 1#w).toNat = c.toNat + 1 := by
  have hlt : c.toNat < 2 ^ w := c.isLt
  have hne : c.toNat ≠ 2 ^ w - 1 := by
    intro heq
    apply h
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.toNat_allOnes] using heq
  have hw : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  have h1 : (1#w).toNat = 1 := by
    rw [BitVec.toNat_ofNat]
    have hgt : 1 < 2 ^ w := by omega
    exact Nat.mod_eq_of_lt hgt
  rw [BitVec.toNat_add, h1]
  exact Nat.mod_eq_of_lt (by omega)

private theorem toNat_arIntMax {w : Nat} (hw : 0 < w) :
    (arIntMax w).toNat = 2 ^ (w - 1) - 1 := by
  have hpow : 0 < 2 ^ (w - 1) := Nat.two_pow_pos (w - 1)
  have h2 : 2 ^ w = 2 * 2 ^ (w - 1) := by
    cases w with
    | zero => omega
    | succ k => simp [Nat.pow_succ]; omega
  simp only [arIntMax, BitVec.toNat_not, BitVec.toNat_intMin, Nat.two_pow_pred_mod_two_pow hw]
  omega

private theorem toInt_add_one_of_ne_arIntMax {w : Nat} {c : BitVec w} (h : c ≠ arIntMax w) :
    (c + 1#w).toInt = c.toInt + 1 := by
  cases w with
  | zero => exact absurd (Subsingleton.elim c (arIntMax 0)) h
  | succ m =>
    cases m with
    | zero =>
      have h2 : c.toNat < 2 := c.isLt
      have hc0 : c.toNat ≠ 0 := by
        intro h0; apply h; apply BitVec.eq_of_toNat_eq; simpa [arIntMax] using h0
      have hc : c = 1#1 := by apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
      subst hc; decide
    | succ k =>
      have hw : 0 < k + 2 := Nat.succ_pos _
      have hmax := toNat_arIntMax hw
      have hne : c.toNat ≠ 2 ^ (k + 1) - 1 := by
        intro heq
        apply h
        apply BitVec.eq_of_toNat_eq
        simpa [hmax] using heq
      have hc := c.isLt
      have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have hpow1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
      have hpow2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
      have h1 : (1#(k + 2)).toNat = 1 := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond, BitVec.toNat_add, h1]
      by_cases htop : c.toNat = 2 ^ (k + 2) - 1
      · have hzero : (c.toNat + 1) % 2 ^ (k + 2) = 0 := by
          rw [show c.toNat + 1 = 2 ^ (k + 2) by omega, Nat.mod_self]
        rw [hzero]
        split <;> split <;> omega
      · have hmod : (c.toNat + 1) % 2 ^ (k + 2) = c.toNat + 1 :=
          Nat.mod_eq_of_lt (by omega)
        rw [hmod]
        split <;> split <;> omega

theorem toRangeBound_eval {w : Nat} (o : CmpOp) (c x : BitVec w) {b : RangeBound w}
    (h : toRangeBound o c = some b) : b.eval x = o.evalBits x c := by
  cases o <;> simp only [toRangeBound] at h
  all_goals try cases h
  · rfl
  · split at h
    · injection h with h; subst h; rename_i hne
      have hadd := toNat_add_one_of_ne_allOnes (by simpa using hne)
      simp only [RangeBound.eval, CmpOp.evalBits, BitVec.ult, BitVec.ule, hadd]
      apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
    · cases h
  · split at h
    · injection h with h; subst h; rename_i hne
      have hadd := toNat_add_one_of_ne_allOnes (by simpa using hne)
      simp only [RangeBound.eval, CmpOp.evalBits, BitVec.ult, BitVec.ule, hadd]
      apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
    · cases h
  · rfl
  · rfl
  · split at h
    · injection h with h; subst h; rename_i hne
      have hadd := toInt_add_one_of_ne_arIntMax (by simpa using hne)
      simp only [RangeBound.eval, CmpOp.evalBits, BitVec.slt, BitVec.sle, hadd]
      apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
    · cases h
  · split at h
    · injection h with h; subst h; rename_i hne
      have hadd := toInt_add_one_of_ne_arIntMax (by simpa using hne)
      simp only [RangeBound.eval, CmpOp.evalBits, BitVec.slt, BitVec.sle, hadd]
      apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
    · cases h
  · rfl

theorem bv_range_and_u {w : Nat} (x lo hi : BitVec w) :
    (lo.ule x && x.ult hi) = if lo.ult hi then (x - lo).ult (hi - lo) else false := by
  apply Bool.eq_iff_iff.mpr
  have hx := x.isLt; have hlo := lo.isLt; have hhi := hi.isLt
  by_cases hlt : lo.toNat < hi.toNat
  · simp only [BitVec.ule, BitVec.ult, BitVec.toNat_sub, hlt, decide_true, ↓reduceIte,
      Bool.and_eq_true, decide_eq_true_eq]
    have hhi_sub : (2 ^ w - lo.toNat + hi.toNat) % 2 ^ w = hi.toNat - lo.toNat := by
      have : 2 ^ w - lo.toNat + hi.toNat = (hi.toNat - lo.toNat) + 2 ^ w := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hhi_sub]
    by_cases h1 : lo.toNat ≤ x.toNat
    · have hx_sub : (2 ^ w - lo.toNat + x.toNat) % 2 ^ w = x.toNat - lo.toNat := by
        have : 2 ^ w - lo.toNat + x.toNat = (x.toNat - lo.toNat) + 2 ^ w := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hx_sub]; omega
    · have hx_sub : (2 ^ w - lo.toNat + x.toNat) % 2 ^ w = 2 ^ w - lo.toNat + x.toNat :=
        Nat.mod_eq_of_lt (by omega)
      rw [hx_sub]; omega
  · simp only [BitVec.ule, BitVec.ult, hlt, decide_false, Bool.false_eq_true, ↓reduceIte,
      Bool.and_eq_true, decide_eq_true_eq, iff_false, not_and]
    omega

private theorem bv_slt_iff_add_intMin_ult {w : Nat} (a b : BitVec w) :
    a.slt b = (a + BitVec.intMin w).ult (b + BitVec.intMin w) := by
  cases w with
  | zero =>
    have ha : a = 0#0 := Subsingleton.elim a 0#0
    have hb : b = 0#0 := Subsingleton.elim b 0#0
    subst ha; subst hb; rfl
  | succ m =>
    have hpow : 0 < 2 ^ m := Nat.two_pow_pos m
    have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
    have hM : (BitVec.intMin (m + 1)).toNat = 2 ^ m := by
      rw [BitVec.toNat_intMin]
      simp only [Nat.add_sub_cancel]
      exact Nat.mod_eq_of_lt (by omega)
    have hadd : ∀ z : BitVec (m + 1),
        (z + BitVec.intMin (m + 1)).toNat =
          if z.toNat < 2 ^ m then z.toNat + 2 ^ m else z.toNat - 2 ^ m := by
      intro z
      have hz := z.isLt
      rw [BitVec.toNat_add, hM]
      split
      · exact Nat.mod_eq_of_lt (by omega)
      · have : z.toNat + 2 ^ m = (z.toNat - 2 ^ m) + 2 ^ (m + 1) := by omega
        rw [this, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
    have hshift : ∀ z : BitVec (m + 1),
        ((z + BitVec.intMin (m + 1)).toNat : Int) = z.toInt + ((2 ^ m : Nat) : Int) := by
      intro z
      have hz := z.isLt
      rw [hadd z, BitVec.toInt_eq_toNat_cond]
      split <;> split <;> omega
    apply Bool.eq_iff_iff.mpr
    simp only [BitVec.slt, BitVec.ult, decide_eq_true_eq]
    have ha := hshift a
    have hb := hshift b
    omega

private theorem bv_sle_iff_add_intMin_ule {w : Nat} (a b : BitVec w) :
    a.sle b = (a + BitVec.intMin w).ule (b + BitVec.intMin w) := by
  have h1 := bv_slt_iff_add_intMin_ult b a
  have h2 : a.sle b = !(b.slt a) := by
    apply Bool.eq_iff_iff.mpr
    simp only [BitVec.sle, BitVec.slt, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not]
    omega
  have h3 : (a + BitVec.intMin w).ule (b + BitVec.intMin w) =
      !((b + BitVec.intMin w).ult (a + BitVec.intMin w)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [BitVec.ule, BitVec.ult, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not]
    omega
  rw [h2, h3, h1]

theorem bv_range_and_s {w : Nat} (x lo hi : BitVec w) :
    (lo.sle x && x.slt hi) = if lo.slt hi then (x - lo).ult (hi - lo) else false := by
  rw [bv_sle_iff_add_intMin_ule lo x, bv_slt_iff_add_intMin_ult x hi,
      bv_slt_iff_add_intMin_ult lo hi, bv_range_and_u]
  have h1 : (x + BitVec.intMin w) - (lo + BitVec.intMin w) = x - lo := by
    rw [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc x,
        BitVec.add_comm (BitVec.intMin w), BitVec.sub_add_cancel, ← BitVec.sub_eq_add_neg]
  have h2 : (hi + BitVec.intMin w) - (lo + BitVec.intMin w) = hi - lo := by
    rw [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc hi,
        BitVec.add_comm (BitVec.intMin w), BitVec.sub_add_cancel, ← BitVec.sub_eq_add_neg]
  rw [h1, h2]

theorem bv_range_or_u {w : Nat} (x lo hi : BitVec w) :
    (x.ult lo || hi.ule x) = if lo.ult hi then (hi - lo).ule (x - lo) else true := by
  have h := congrArg (! ·) (bv_range_and_u x lo hi)
  have hnot1 : (!(lo.ule x && x.ult hi)) = (x.ult lo || hi.ule x) := by
    rw [Bool.not_and]
    have ha : (!(lo.ule x)) = x.ult lo := by
      apply Bool.eq_iff_iff.mpr
      simp only [BitVec.ule, BitVec.ult, Bool.not_eq_true', decide_eq_true_eq,
        decide_eq_false_iff_not]
      omega
    have hb : (!(x.ult hi)) = hi.ule x := by
      apply Bool.eq_iff_iff.mpr
      simp only [BitVec.ule, BitVec.ult, Bool.not_eq_true', decide_eq_true_eq,
        decide_eq_false_iff_not]
      omega
    rw [ha, hb]
  have hnot2 : (!((x - lo).ult (hi - lo))) = (hi - lo).ule (x - lo) := by
    apply Bool.eq_iff_iff.mpr
    simp only [BitVec.ule, BitVec.ult, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not]
    omega
  rw [hnot1] at h
  rw [h]
  cases lo.ult hi <;> simp [hnot2]

theorem bv_range_or_s {w : Nat} (x lo hi : BitVec w) :
    (x.slt lo || hi.sle x) = if lo.slt hi then (hi - lo).ule (x - lo) else true := by
  have h := congrArg (! ·) (bv_range_and_s x lo hi)
  have hnot1 : (!(lo.sle x && x.slt hi)) = (x.slt lo || hi.sle x) := by
    rw [Bool.not_and]
    have ha : (!(lo.sle x)) = x.slt lo := by
      apply Bool.eq_iff_iff.mpr
      simp only [BitVec.sle, BitVec.slt, Bool.not_eq_true', decide_eq_true_eq,
        decide_eq_false_iff_not]
      omega
    have hb : (!(x.slt hi)) = hi.sle x := by
      apply Bool.eq_iff_iff.mpr
      simp only [BitVec.sle, BitVec.slt, Bool.not_eq_true', decide_eq_true_eq,
        decide_eq_false_iff_not]
      omega
    rw [ha, hb]
  have hnot2 : (!((x - lo).ult (hi - lo))) = (hi - lo).ule (x - lo) := by
    apply Bool.eq_iff_iff.mpr
    simp only [BitVec.ule, BitVec.ult, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not]
    omega
  rw [hnot1] at h
  rw [h]
  cases lo.slt hi <;> simp [hnot2]

/-! ## Semantic invariant `ARGood` and WP soundness (`addrRangeSweep_wp`) -/

/-- Semantic validity of `CmpImmDef Val` for boolean value `v`. -/
@[expose] def CmpImmGood (ρ : FEnv) (b : Nat) (cm : CmpImmDef Val) (v : Bool) : Prop :=
  FKey.fev ρ cm.lhsKey = cm.lhs.val ∧ FKey.FLt b cm.lhsKey ∧ v = cm.op.evalBits cm.lhs.val cm.imm

theorem CmpImmGood.upd {ρ : FEnv} {b : Nat} {cm : CmpImmDef Val} {v : Bool}
    (h : CmpImmGood ρ b cm v) {u : Ty} (x : Val u) :
    CmpImmGood (fupd ρ b x) (b + 1) cm v :=
  ⟨(FKey.fev_fupd x h.2.1).trans h.1, h.2.1.mono, h.2.2⟩

theorem CmpImmGood.updTup {ρ : FEnv} {b : Nat} {cm : CmpImmDef Val} {v : Bool}
    (h : CmpImmGood ρ b cm v) {ts : List Ty} (xs : Tup Val ts) :
    CmpImmGood (fupdTup ρ b xs) (b + ts.length) cm v :=
  ⟨(FKey.fev_fupdTup xs h.2.1).trans h.1, h.2.1.add, h.2.2⟩

/-- Semantic validity of `ZextDef Val n` for `v : BitVec n`. -/
@[expose] def ZextDefGood (ρ : FEnv) (b : Nat) {n : Nat}
    (zd : ZextDef Val n) (v : BitVec n) : Prop :=
  FKey.fev ρ zd.srcKey = zd.src.val ∧ FKey.FLt b zd.srcKey ∧ v = zd.src.val.setWidth n

theorem ZextDefGood.upd {ρ : FEnv} {b n : Nat} {zd : ZextDef Val n} {v : BitVec n}
    (h : ZextDefGood ρ b zd v) {u : Ty} (x : Val u) :
    ZextDefGood (fupd ρ b x) (b + 1) zd v :=
  ⟨(FKey.fev_fupd x h.2.1).trans h.1, h.2.1.mono, h.2.2⟩

theorem ZextDefGood.updTup {ρ : FEnv} {b n : Nat} {zd : ZextDef Val n} {v : BitVec n}
    (h : ZextDefGood ρ b zd v) {ts : List Ty} (xs : Tup Val ts) :
    ZextDefGood (fupdTup ρ b xs) (b + ts.length) zd v :=
  ⟨(FKey.fev_fupdTup xs h.2.1).trans h.1, h.2.1.add, h.2.2⟩

/-- Semantic validity of `AddrDef Val n` for `v : BitVec n`. -/
@[expose] def AddrDefGood {n : Nat} : AddrDef Val n → BitVec n → Prop
  | .addVC x _ d, v => v = x.val + d
  | .shlVC x _ sh _ d, v => v = (x.val <<< sh) + d
  | .addVV x _ y _ d, v => v = (x.val + y.val) + d
  | .subVV x _ y _ d, v => v = (x.val - y.val) + d
  | .shlAddVV x _ y _ sh _ d, v => v = ((x.val + y.val) <<< sh) + d
  | .shlSubVV x _ y _ sh _ d, v => v = ((x.val - y.val) <<< sh) + d

theorem AddrDefGood.shiftDisp {n : Nat} {ad : AddrDef Val n} {v : BitVec n}
    (h : AddrDefGood ad v) (c : BitVec n) : AddrDefGood (ad.shiftDisp c) (v + c) := by
  cases ad <;> simp only [AddrDef.shiftDisp, AddrDefGood] at h ⊢ <;>
    rw [h, BitVec.add_assoc]

/-- Semantic validity of `BitsProv Val n` for `v : BitVec n`. -/
@[expose] def BitsProvGood (ρ : FEnv) (b : Nat) {n : Nat}
    (bp : BitsProv Val n) (v : BitVec n) : Prop :=
  (∀ ad, bp.addr? = some ad → AddrDefGood ad v) ∧
    (∀ zd, bp.zext? = some zd → ZextDefGood ρ b zd v)

/-- Type-indexed provenance validity for `ARProv Val t`. -/
@[expose] def ARProvGood (ρ : FEnv) (b : Nat) : {t : Ty} → ARProv Val t → Val t → Prop
  | .bool, none, _ => True
  | .bool, some cm, v => CmpImmGood ρ b cm v
  | .bits _, bp, v => BitsProvGood ρ b bp v
  | .float _, (), _ => True
  | .pair _ _, (), _ => True

theorem ARProvGood.none {ρ : FEnv} {b : Nat} {t : Ty} {v : Val t} :
    ARProvGood ρ b (ARProv.none (V := Val) (t := t)) v := by
  cases t with
  | bits _ => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | bool | float _ | pair _ _ => trivial

theorem ARProvGood.upd {ρ : FEnv} {b : Nat} {t : Ty} {p : ARProv Val t} {v : Val t}
    (h : ARProvGood ρ b p v) {u : Ty} (x : Val u) :
    ARProvGood (fupd ρ b x) (b + 1) p v := by
  cases t with
  | bool => cases p with | none => trivial | some _ => exact CmpImmGood.upd h x
  | bits _ => exact ⟨h.1, fun zd hzd => (h.2 zd hzd).upd x⟩
  | float _ | pair _ _ => trivial

theorem ARProvGood.updTup {ρ : FEnv} {b : Nat} {t : Ty} {p : ARProv Val t} {v : Val t}
    (h : ARProvGood ρ b p v) {ts : List Ty} (xs : Tup Val ts) :
    ARProvGood (fupdTup ρ b xs) (b + ts.length) p v := by
  cases t with
  | bool => cases p with | none => trivial | some _ => exact CmpImmGood.updTup h xs
  | bits _ => exact ⟨h.1, fun zd hzd => (h.2 zd hzd).updTup xs⟩
  | float _ | pair _ _ => trivial

/-- Value invariant for one `ARVal Val t` entry in `ARGood`. -/
@[expose] def ARValGood (ρ : FEnv) (b : Nat) {t : Ty} (r : ARVal Val t) (v : Val t) : Prop :=
  r.out.val = v ∧ FKey.fev ρ r.key = v ∧ FKey.FLt b r.key ∧ ARProvGood ρ b r.prov v

/-- Every entry in `G : Ctx (ARVal Val) Val` satisfies `ARValGood`. -/
@[expose] def ARGood (ρ : FEnv) (b : Nat) (G : Ctx (ARVal Val) Val) : Prop :=
  ∀ p ∈ G, ARValGood ρ b p.2.1 p.2.2

theorem ARValGood.upd {ρ : FEnv} {b : Nat} {t : Ty} {r : ARVal Val t} {v : Val t}
    (h : ARValGood ρ b r v) {u : Ty} (x : Val u) :
    ARValGood (fupd ρ b x) (b + 1) r v :=
  ⟨h.1, (FKey.fev_fupd x h.2.2.1).trans h.2.1, h.2.2.1.mono, h.2.2.2.upd x⟩

theorem ARValGood.updTup {ρ : FEnv} {b : Nat} {t : Ty} {r : ARVal Val t} {v : Val t}
    (h : ARValGood ρ b r v) {ts : List Ty} (xs : Tup Val ts) :
    ARValGood (fupdTup ρ b xs) (b + ts.length) r v :=
  ⟨h.1, (FKey.fev_fupdTup xs h.2.2.1).trans h.2.1, h.2.2.1.add, h.2.2.2.updTup xs⟩

theorem ARGood.cons {ρ : FEnv} {b : Nat} {G : Ctx (ARVal Val) Val} (hG : ARGood ρ b G)
    {t : Ty} {r : ARVal Val t} {v : Val t} (hr : ARValGood ρ b r v) :
    ARGood ρ b (⟨t, r, v⟩ :: G)
  | _, .head _ => hr
  | _, .tail _ hp => hG _ hp

theorem ARGood.append {ρ : FEnv} {b : Nat} {G₁ G₂ : Ctx (ARVal Val) Val}
    (h1 : ARGood ρ b G₁) (h2 : ARGood ρ b G₂) : ARGood ρ b (G₁ ++ G₂) := by
  intro p hp; rcases List.mem_append.1 hp with hp | hp
  · exact h1 p hp
  · exact h2 p hp

theorem ARGood.upd {ρ : FEnv} {b : Nat} {G : Ctx (ARVal Val) Val} (hG : ARGood ρ b G)
    {u : Ty} (x : Val u) : ARGood (fupd ρ b x) (b + 1) G :=
  fun p hp => (hG p hp).upd x

theorem ARGood.updTup {ρ : FEnv} {b : Nat} {G : Ctx (ARVal Val) Val} (hG : ARGood ρ b G)
    {ts : List Ty} (xs : Tup Val ts) : ARGood (fupdTup ρ b xs) (b + ts.length) G :=
  fun p hp => (hG p hp).updTup xs

theorem ARGood.freshARVals_only (ρ : FEnv) (d : Nat) :
    {ts : List Ty} → (xs : Tup Val ts) → (b : Nat) →
    ARGood (fupdTup ρ b xs) (b + ts.length) (Tup.zip (freshARVals d ts xs b) xs)
  | [], (), _ => fun _ hp => nomatch hp
  | _ :: ts, (x, xs), b => by
    intro p hp
    simp only [freshARVals, tupFreshWith, Tup.zip, fupdTup, List.length_cons] at hp ⊢
    cases hp with
    | head =>
      refine ⟨rfl, ?_, by simp [ARVal.fresh, FKey.FLt], ARProvGood.none⟩
      simp only [ARVal.fresh, FKey.fev]
      rw [fupdTup_lt (fupd ρ b x) xs (Nat.lt_succ_self b), fupd_eq]
    | tail _ hp =>
      have ih := ARGood.freshARVals_only (fupd ρ b x) d xs (b + 1) p hp
      simpa [show b + 1 + ts.length = b + (ts.length + 1) by omega] using ih

theorem ARGood.freshARVals {ρ : FEnv} {b : Nat} {G : Ctx (ARVal Val) Val} (hG : ARGood ρ b G)
    (d : Nat) {ts : List Ty} (xs : Tup Val ts) :
    ARGood (fupdTup ρ b xs) (b + ts.length) (Tup.zip (freshARVals d ts xs b) xs ++ G) :=
  (ARGood.freshARVals_only ρ d xs b).append (hG.updTup xs)

theorem ARGood.freshOne {ρ : FEnv} {b : Nat} {G : Ctx (ARVal Val) Val} (hG : ARGood ρ b G)
    (d : Nat) {t : Ty} (v : Val t) :
    ARGood (fupd ρ b v) (b + 1) (⟨t, ARVal.fresh v b d, v⟩ :: G) :=
  (hG.upd v).cons ⟨rfl, fupd_eq ρ b v, Nat.lt_succ_self b, ARProvGood.none⟩

theorem ARValGood.ofImm {ρ : FEnv} {b : Nat} {t : Ty} (c : Val t) :
    ARValGood ρ b (ARVal.ofImm c) c :=
  ⟨rfl, rfl, trivial, ARProvGood.none⟩

theorem ArgRel.arOut_val {G : Ctx (ARVal Val) Val} {ρ : FEnv} {b : Nat} (hG : ARGood ρ b G)
    {t : Ty} {a₁ : Arg (ARVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → a₁.arOut.val = a₂.val
  | .var h => (hG _ h).1
  | .imm _ => rfl

theorem ArgRel.arKey_ev {G : Ctx (ARVal Val) Val} {ρ : FEnv} {b : Nat} (hG : ARGood ρ b G)
    {t : Ty} {a₁ : Arg (ARVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → FKey.fev ρ a₁.arKey = a₂.val
  | .var h => (hG _ h).2.1
  | .imm _ => rfl

theorem ArgRel.arKey_FLt {G : Ctx (ARVal Val) Val} {ρ : FEnv} {b : Nat} (hG : ARGood ρ b G)
    {t : Ty} {a₁ : Arg (ARVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → FKey.FLt b a₁.arKey
  | .var h => (hG _ h).2.2.1
  | .imm _ => trivial

theorem ArgRel.arProv_good {G : Ctx (ARVal Val) Val} {ρ : FEnv} {b : Nat} (hG : ARGood ρ b G)
    {t : Ty} {a₁ : Arg (ARVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → ARProvGood ρ b a₁.arProv a₂.val
  | .var h => (hG _ h).2.2.2
  | .imm _ => ARProvGood.none

theorem ArgRel.toARVal_good {G : Ctx (ARVal Val) Val} {ρ : FEnv} {b : Nat} (hG : ARGood ρ b G)
    {t : Ty} {a₁ : Arg (ARVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → ARValGood ρ b a₁.toARVal a₂.val
  | .var h => hG _ h
  | .imm c => ARValGood.ofImm c

theorem TRel.arOut_vals {G : Ctx (ARVal Val) Val} {ρ : FEnv} {b : Nat} (hG : ARGood ρ b G)
    {ts : List Ty} {as₁ : Tup (Arg (ARVal Val)) ts} {as₂ : Tup (Arg Val) ts}
    (h : TRel (ArgRel G) as₁ as₂) : vals (tupArOut as₁) = vals as₂ :=
  TRel.tupMapArg_vals (fun _ => Arg.arOut) (fun ha => ha.arOut_val hG) h

private theorem imm?_eq_some_val {V : Ty → Type} : ∀ {t : Ty} {a : Arg V t} {c : Val t},
    a.imm? = some c → a = .imm c
  | _, .var _, _, h => by cases h
  | _, .imm _, _, h => by injection h with h; subst h; rfl

theorem arOut_imm?_eq_val {G : Ctx (ARVal Val) Val} {ρ : FEnv} {b : Nat} (hG : ARGood ρ b G)
    {t : Ty} {a₁ : Arg (ARVal Val) t} {a₂ : Arg Val t} {c : Val t}
    (ha : ArgRel G t a₁ a₂) (himm : a₁.arOut.imm? = some c) : a₂.val = c := by
  have h1 := ha.arOut_val hG
  rw [imm?_eq_some_val himm] at h1
  exact h1.symm

theorem addrOptGood_of {ρ : FEnv} {b n : Nat}
    {opt : Option (AddrDef Val n)} {v : BitVec n}
    (h : ∀ ad, opt = some ad → AddrDefGood ad v) :
    ARProvGood ρ b (t := .bits n) { addr? := opt } v :=
  ⟨h, (fun _ hz => nomatch hz)⟩

private theorem recordAddProv_good {G : Ctx (ARVal Val) Val} {ρ : FEnv} {b : Nat}
    (hG : ARGood ρ b G) {n : Nat} {a₁ b₁ : Arg (ARVal Val) (.bits n)}
    {a₂ b₂ : Arg Val (.bits n)} (ha : ArgRel G (.bits n) a₁ a₂) (hb : ArgRel G (.bits n) b₁ b₂) :
    ∀ ad, recordAddProv a₁ b₁ = some ad → AddrDefGood ad (a₂.val + b₂.val) := by
  dsimp only [recordAddProv]
  split
  · intro _ h; cases h
  · cases himma : a₁.arOut.imm? <;> cases himmb : b₁.arOut.imm?
    · have hap := (ha.arProv_good hG).1
      have hbp := (hb.arProv_good hG).1
      have hav := ha.arOut_val hG; have hbv := hb.arOut_val hG
      intro ad h
      rcases hpa : a₁.arProv.addr? with _ | ad1 <;>
        rcases hpb : b₁.arProv.addr? with _ | ad2 <;> rw [hpa, hpb] at h
      · dsimp only at h; injection h with h; subst h; simp [AddrDefGood, hav, hbv]
      · cases ad2 with
        | addVC y dy d2 =>
          have hy := hbp _ hpb; simp only [AddrDefGood] at hy
          dsimp only at h; injection h with h; subst h; simp only [AddrDefGood]
          rw [← hav, hy, BitVec.add_assoc]
        | _ => dsimp only at h; injection h with h; subst h; simp [AddrDefGood, hav, hbv]
      · cases ad1 with
        | addVC x dx d1 =>
          have hx := hap _ hpa; simp only [AddrDefGood] at hx
          dsimp only at h; injection h with h; subst h; simp only [AddrDefGood]
          rw [hx, ← hbv, BitVec.add_assoc, BitVec.add_comm _ b₁.arOut.val, BitVec.add_assoc]
        | _ => dsimp only at h; injection h with h; subst h; simp [AddrDefGood, hav, hbv]
      · cases ad1 with
        | addVC x dx d1 =>
          have hx := hap _ hpa; simp only [AddrDefGood] at hx
          cases ad2 with
          | addVC y dy d2 =>
            have hy := hbp _ hpb; simp only [AddrDefGood] at hy
            dsimp only at h; injection h with h; subst h; simp only [AddrDefGood]
            rw [hx, hy, BitVec.add_assoc, BitVec.add_comm d1, BitVec.add_assoc,
              BitVec.add_assoc, BitVec.add_comm d2 d1]
          | _ =>
            dsimp only at h; injection h with h; subst h; simp only [AddrDefGood]
            rw [hx, ← hbv, BitVec.add_assoc, BitVec.add_comm _ b₁.arOut.val, BitVec.add_assoc]
        | shlVC x dx sh1 hsh1 d1 =>
          cases ad2 with
          | addVC y dy d2 =>
            have hy := hbp _ hpb; simp only [AddrDefGood] at hy
            dsimp only at h; injection h with h; subst h; simp only [AddrDefGood]
            rw [← hav, hy, BitVec.add_assoc]
          | shlVC y dy sh2 hsh2 d2 =>
            dsimp only at h; split at h
            · rename_i hsheq; have hsh : _ = _ := eq_of_beq hsheq; subst hsh
              have hx := hap _ hpa; have hy := hbp _ hpb; simp only [AddrDefGood] at hx hy
              injection h with h; subst h; simp only [AddrDefGood]
              rw [hx, hy, bv_shl_add, BitVec.add_assoc _ d1, BitVec.add_comm d1,
                BitVec.add_assoc (y.val <<< _), BitVec.add_comm d1 d2, ← BitVec.add_assoc,
                ← BitVec.add_assoc]
            · injection h with h; subst h; simp [AddrDefGood, hav, hbv]
          | _ => dsimp only at h; injection h with h; subst h; simp [AddrDefGood, hav, hbv]
        | _ =>
          cases ad2 with
          | addVC y dy d2 =>
            have hy := hbp _ hpb; simp only [AddrDefGood] at hy
            dsimp only at h; injection h with h; subst h; simp only [AddrDefGood]
            rw [← hav, hy, BitVec.add_assoc]
          | _ => dsimp only at h; injection h with h; subst h; simp [AddrDefGood, hav, hbv]
    · rename_i c
      have hbc := arOut_imm?_eq_val hG hb himmb
      have hap := (ha.arProv_good hG).1
      cases hp : a₁.arProv.addr? with
      | none =>
        intro _ h; injection h with h; subst h; simp [AddrDefGood, ha.arOut_val hG, hbc]
      | some ad0 =>
        intro _ h; injection h with h; subst h
        rw [hbc]; exact (hap _ hp).shiftDisp c
    · rename_i c
      have hac := arOut_imm?_eq_val hG ha himma
      have hbp := (hb.arProv_good hG).1
      cases hp : b₁.arProv.addr? with
      | none =>
        intro _ h; injection h with h; subst h
        simp [AddrDefGood, hb.arOut_val hG, hac, BitVec.add_comm]
      | some ad0 =>
        intro _ h; injection h with h; subst h
        rw [hac, BitVec.add_comm c]; exact (hbp _ hp).shiftDisp c
    · intro _ h; cases h

private theorem bv_sub_r {n : Nat} (a b d : BitVec n) : a - (b + d) = (a - b) + (-d) := by
  rw [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.sub_eq_add_neg (-b) d,
    ← BitVec.add_assoc, ← BitVec.sub_eq_add_neg a b]

private theorem bv_sub_pair {n : Nat} (a d1 b d2 : BitVec n) :
    (a + d1) - (b + d2) = (a - b) + (d1 - d2) := by
  rw [BitVec.sub_eq_add_neg (a + d1) (b + d2), BitVec.neg_add, BitVec.sub_eq_add_neg (-b) d2,
    BitVec.add_assoc a d1 (-b + -d2), BitVec.add_comm d1 (-b + -d2),
    BitVec.add_assoc (-b) (-d2) d1, BitVec.add_comm (-d2) d1,
    ← BitVec.add_assoc a (-b) (d1 + -d2), ← BitVec.sub_eq_add_neg a b,
    ← BitVec.sub_eq_add_neg d1 d2]

private theorem recordSubProv_good {G : Ctx (ARVal Val) Val} {ρ : FEnv} {b : Nat}
    (hG : ARGood ρ b G) {n : Nat} {a₁ b₁ : Arg (ARVal Val) (.bits n)}
    {a₂ b₂ : Arg Val (.bits n)} (ha : ArgRel G (.bits n) a₁ a₂) (hb : ArgRel G (.bits n) b₁ b₂) :
    ∀ ad, recordSubProv a₁ b₁ = some ad → AddrDefGood ad (a₂.val - b₂.val) := by
  dsimp only [recordSubProv]
  split
  · intro _ h; cases h
  · cases himma : a₁.arOut.imm? <;> cases himmb : b₁.arOut.imm?
    · have hap := (ha.arProv_good hG).1
      have hbp := (hb.arProv_good hG).1
      have hav := ha.arOut_val hG; have hbv := hb.arOut_val hG
      intro ad h
      rcases hpa : a₁.arProv.addr? with _ | ad1 <;>
        rcases hpb : b₁.arProv.addr? with _ | ad2 <;> rw [hpa, hpb] at h
      · dsimp only at h; injection h with h; subst h; simp [AddrDefGood, hav, hbv]
      · cases ad2 with
        | addVC y dy d2 =>
          have hy := hbp _ hpb; simp only [AddrDefGood] at hy
          dsimp only at h; injection h with h; subst h; simp only [AddrDefGood]
          rw [← hav, hy, bv_sub_r]
        | _ => dsimp only at h; injection h with h; subst h; simp [AddrDefGood, hav, hbv]
      · cases ad1 with
        | addVC x dx d1 =>
          have hx := hap _ hpa; simp only [AddrDefGood] at hx
          dsimp only at h; injection h with h; subst h; simp only [AddrDefGood]
          rw [hx, ← hbv, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg x.val,
            BitVec.add_assoc, BitVec.add_comm _ (-b₁.arOut.val), ← BitVec.add_assoc]
        | _ => dsimp only at h; injection h with h; subst h; simp [AddrDefGood, hav, hbv]
      · cases ad1 with
        | addVC x dx d1 =>
          have hx := hap _ hpa; simp only [AddrDefGood] at hx
          cases ad2 with
          | addVC y dy d2 =>
            have hy := hbp _ hpb; simp only [AddrDefGood] at hy
            dsimp only at h; injection h with h; subst h; simp only [AddrDefGood]
            rw [hx, hy, bv_sub_pair]
          | _ =>
            dsimp only at h; injection h with h; subst h; simp only [AddrDefGood]
            rw [hx, ← hbv, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg x.val,
              BitVec.add_assoc, BitVec.add_comm _ (-b₁.arOut.val), ← BitVec.add_assoc]
        | shlVC x dx sh1 hsh1 d1 =>
          cases ad2 with
          | addVC y dy d2 =>
            have hy := hbp _ hpb; simp only [AddrDefGood] at hy
            dsimp only at h; injection h with h; subst h; simp only [AddrDefGood]
            rw [← hav, hy, bv_sub_r]
          | shlVC y dy sh2 hsh2 d2 =>
            dsimp only at h; split at h
            · rename_i hsheq; have hsh : _ = _ := eq_of_beq hsheq; subst hsh
              have hx := hap _ hpa; have hy := hbp _ hpb; simp only [AddrDefGood] at hx hy
              injection h with h; subst h; simp only [AddrDefGood]
              rw [hx, hy, bv_sub_pair, ← bv_shl_sub]
            · injection h with h; subst h; simp [AddrDefGood, hav, hbv]
          | _ => dsimp only at h; injection h with h; subst h; simp [AddrDefGood, hav, hbv]
        | _ =>
          cases ad2 with
          | addVC y dy d2 =>
            have hy := hbp _ hpb; simp only [AddrDefGood] at hy
            dsimp only at h; injection h with h; subst h; simp only [AddrDefGood]
            rw [← hav, hy, bv_sub_r]
          | _ => dsimp only at h; injection h with h; subst h; simp [AddrDefGood, hav, hbv]
    · rename_i c
      have hbc := arOut_imm?_eq_val hG hb himmb
      have hap := (ha.arProv_good hG).1
      cases hp : a₁.arProv.addr? with
      | none =>
        intro _ h; injection h with h; subst h
        simp [AddrDefGood, ha.arOut_val hG, hbc, BitVec.sub_eq_add_neg]
      | some ad0 =>
        intro _ h; injection h with h; subst h
        rw [hbc, BitVec.sub_eq_add_neg]; exact (hap _ hp).shiftDisp (-c)
    · intro _ h; cases h
    · intro _ h; cases h

private theorem recordShlProv_good {G : Ctx (ARVal Val) Val} {ρ : FEnv} {b : Nat}
    (hG : ARGood ρ b G) {n : Nat} {a₁ b₁ : Arg (ARVal Val) (.bits n)}
    {a₂ b₂ : Arg Val (.bits n)} (ha : ArgRel G (.bits n) a₁ a₂) (hb : ArgRel G (.bits n) b₁ b₂) :
    ∀ ad, recordShlProv a₁ b₁ = some ad → AddrDefGood ad (a₂.val <<< (b₂.val.toNat % n)) := by
  dsimp only [recordShlProv]
  split
  · intro _ h; cases h
  · cases himmb : b₁.arOut.imm? with
    | none => intro _ h; cases h
    | some k =>
      have hbk := arOut_imm?_eq_val hG hb himmb
      dsimp only; split
      · rename_i hkn
        have hmod : b₂.val.toNat % n = k.toNat := by rw [hbk, Nat.mod_eq_of_lt hkn.2]
        have hap := (ha.arProv_good hG).1
        cases hp : a₁.arProv.addr? with
        | none =>
          intro _ h; injection h with h; subst h; simp [AddrDefGood, ha.arOut_val hG, hmod]
        | some ad0 =>
          have had0 := hap _ hp
          cases ad0 <;> dsimp only
          · intro _ h; injection h with h; subst h
            simp only [AddrDefGood] at had0 ⊢; rw [had0, hmod, bv_shl_add]
          · split
            · intro _ h; injection h with h; subst h
              simp only [AddrDefGood] at had0 ⊢; rw [had0, hmod, bv_shl_add, bv_shl_shl_add]
            · intro _ h; cases h
          · intro _ h; injection h with h; subst h
            simp only [AddrDefGood] at had0 ⊢; rw [had0, hmod, bv_shl_add]
          · intro _ h; injection h with h; subst h
            simp only [AddrDefGood] at had0 ⊢; rw [had0, hmod, bv_shl_add]
          · split
            · intro _ h; injection h with h; subst h
              simp only [AddrDefGood] at had0 ⊢; rw [had0, hmod, bv_shl_add, bv_shl_shl_add]
            · intro _ h; cases h
          · split
            · intro _ h; injection h with h; subst h
              simp only [AddrDefGood] at had0 ⊢; rw [had0, hmod, bv_shl_add, bv_shl_shl_add]
            · intro _ h; cases h
      · intro _ h; cases h

private theorem setWidth_setWidth_of_le {m n k : Nat} (hmn : m ≤ n) (x : BitVec m) :
    (x.setWidth n).setWidth k = x.setWidth k := by
  apply BitVec.eq_of_toNat_eq
  have hpow : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hmn
  have hx := x.isLt
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ n)]

private theorem cmpOp_evalBits_setWidth_ar {m n : Nat} (hlt : m < n) (o : CmpOp)
    (x y : BitVec m) :
    o.evalBits (x.setWidth n) (y.setWidth n) =
      (if arCmpIsSigned o then arCmpToUnsigned o else o).evalBits x y := by
  have hpow : 2 * 2 ^ m ≤ 2 ^ n := by
    rw [← Nat.pow_succ']; exact Nat.pow_le_pow_right (by decide) hlt
  have hx := x.isLt; have hy := y.isLt
  have hxn : (x.setWidth n).toNat = x.toNat := by
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ n)]
  have hyn : (y.setWidth n).toNat = y.toNat := by
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ n)]
  have hxi : (x.setWidth n).toInt = x.toNat := by
    unfold BitVec.toInt; rw [hxn]; simp [show 2 * x.toNat < 2 ^ n by omega]
  have hyi : (y.setWidth n).toInt = y.toNat := by
    unfold BitVec.toInt; rw [hyn]; simp [show 2 * y.toNat < 2 ^ n by omega]
  have hinj : (x.setWidth n = y.setWidth n) ↔ (x = y) :=
    ⟨fun h => BitVec.eq_of_toNat_eq (by rw [← hxn, ← hyn, h]), congrArg _⟩
  cases o <;>
    simp [arCmpIsSigned, arCmpToUnsigned, CmpOp.evalBits, BitVec.ult, BitVec.ule,
      BitVec.slt, BitVec.sle, hxn, hyn, hxi, hyi, hinj]

private theorem recordZextProv_good {G : Ctx (ARVal Val) Val} {ρ : FEnv} {b : Nat}
    (hG : ARGood ρ b G) (m n : Nat) {a₁ : Arg (ARVal Val) (.bits m)} {a₂ : Arg Val (.bits m)}
    (ha : ArgRel G (.bits m) a₁ a₂) :
    ARProvGood ρ b (t := .bits n) (recordZextProv m n a₁) (a₂.val.setWidth n) := by
  dsimp only [recordZextProv]
  split
  · rename_i hmn
    have hzp := (ha.arProv_good hG).2
    cases hz : a₁.arProv.zext? with
    | none =>
      refine ⟨(fun _ h => nomatch h), fun zd h => ?_⟩
      injection h with h; subst h
      exact ⟨(ha.arKey_ev hG).trans (ha.arOut_val hG).symm, ha.arKey_FLt hG,
        by rw [ha.arOut_val hG]⟩
    | some zd0 =>
      have hzd0 := hzp zd0 hz
      refine ⟨(fun _ h => nomatch h), fun zd h => ?_⟩
      injection h with h; subst h
      exact ⟨hzd0.1, hzd0.2.1,
        by rw [hzd0.2.2, setWidth_setWidth_of_le (Nat.le_of_lt zd0.hmn)]⟩
  · exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩

private theorem mkCmpImmFromArg_good {G : Ctx (ARVal Val) Val} {ρ : FEnv} {b : Nat}
    (hG : ARGood ρ b G) {n : Nat} (o : CmpOp) {a₁ : Arg (ARVal Val) (.bits n)}
    {a₂ : Arg Val (.bits n)} (ha : ArgRel G (.bits n) a₁ a₂) (c : BitVec n) :
    CmpImmGood ρ b (mkCmpImmFromArg o a₁ c) (o.evalBits a₂.val c) := by
  dsimp only [mkCmpImmFromArg]
  have hzp := (ha.arProv_good hG).2
  cases hz : a₁.arProv.zext? with
  | none =>
    exact ⟨(ha.arKey_ev hG).trans (ha.arOut_val hG).symm, ha.arKey_FLt hG,
      by rw [ha.arOut_val hG]⟩
  | some zd =>
    have hzd := hzp zd hz
    dsimp only
    split
    · rename_i hfit
      have hfit' : (c.setWidth zd.m).setWidth n = c := eq_of_beq hfit
      have hev : o.evalBits a₂.val c =
          (if arCmpIsSigned o then arCmpToUnsigned o else o).evalBits zd.src.val
            (c.setWidth zd.m) := by
        have h1 := cmpOp_evalBits_setWidth_ar zd.hmn o zd.src.val (c.setWidth zd.m)
        rwa [← hzd.2.2, hfit'] at h1
      exact ⟨hzd.1, hzd.2.1, hev⟩
    · exact ⟨(ha.arKey_ev hG).trans (ha.arOut_val hG).symm, ha.arKey_FLt hG,
        by rw [ha.arOut_val hG]⟩

private theorem recordCmpImmProv_good {G : Ctx (ARVal Val) Val} {ρ : FEnv} {b : Nat}
    (hG : ARGood ρ b G) {w : Nat} (o : CmpOp) {a₁ b₁ : Arg (ARVal Val) (.bits w)}
    {a₂ b₂ : Arg Val (.bits w)} (ha : ArgRel G (.bits w) a₁ a₂) (hb : ArgRel G (.bits w) b₁ b₂) :
    ARProvGood ρ b (t := .bool) (recordCmpImmProv o a₁ b₁) (o.evalBits a₂.val b₂.val) := by
  dsimp only [recordCmpImmProv]
  cases himma : a₁.arOut.imm? <;> cases himmb : b₁.arOut.imm?
  · trivial
  · rename_i c; rw [arOut_imm?_eq_val hG hb himmb]; exact mkCmpImmFromArg_good hG o ha c
  · rename_i c; rw [arOut_imm?_eq_val hG ha himma, ← CmpOp.swap_evalBits]
    exact mkCmpImmFromArg_good hG o.swap hb c
  · rename_i c₁ c₂; rw [arOut_imm?_eq_val hG hb himmb]; exact mkCmpImmFromArg_good hG o ha c₂

theorem wrapKept_good {G : Ctx (ARVal Val) Val} {ρ : FEnv} {b outD : Nat}
    (hG : ARGood ρ b G) {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg (ARVal Val)) sig} {args₂ : Tup (Arg Val) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) {P : Tup Val ts → Prop}
    (hw : code.wp (vals args₂) P) :
    code.wp (vals args₂) fun xs =>
      P xs ∧ ARGood (fupdTup ρ b xs) (b + ts.length)
        (Tup.zip (wrapKept outD b code args₁ xs) xs ++ G) := by
  cases code with
  | add t =>
    cases t with
    | bits n =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, lift2] at hw ⊢
      refine ⟨hw, (hG.upd _).cons ⟨rfl, fupd_eq ρ b _, Nat.lt_succ_self b,
        (addrOptGood_of (recordAddProv_good hG ha hb)).upd _⟩⟩
    | bool | float _ | pair _ _ =>
      exact OpCode.wp_mono _ _ (fun xs hxs => ⟨hxs, hG.freshARVals outD xs⟩) hw
  | sub t =>
    cases t with
    | bits n =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, lift2] at hw ⊢
      refine ⟨hw, (hG.upd _).cons ⟨rfl, fupd_eq ρ b _, Nat.lt_succ_self b,
        (addrOptGood_of (recordSubProv_good hG ha hb)).upd _⟩⟩
    | bool | float _ | pair _ _ =>
      exact OpCode.wp_mono _ _ (fun xs hxs => ⟨hxs, hG.freshARVals outD xs⟩) hw
  | shl t =>
    cases t with
    | bits n =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, lift2] at hw ⊢
      refine ⟨hw, (hG.upd _).cons ⟨rfl, fupd_eq ρ b _, Nat.lt_succ_self b,
        (addrOptGood_of (recordShlProv_good hG ha hb)).upd _⟩⟩
    | bool | float _ | pair _ _ =>
      exact OpCode.wp_mono _ _ (fun xs hxs => ⟨hxs, hG.freshARVals outD xs⟩) hw
  | zext m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    simp only [OpCode.wp, vals] at hw ⊢
    refine ⟨hw.1, hw.2, (hG.upd _).cons ⟨rfl, fupd_eq ρ b _, Nat.lt_succ_self b,
      (recordZextProv_good hG m n ha).upd _⟩⟩
  | copy t =>
    cases t with
    | bits _ =>
      rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _⟩
      simp only [OpCode.wp, vals] at hw ⊢
      refine ⟨hw, (hG.upd _).cons ⟨rfl, fupd_eq ρ b _, Nat.lt_succ_self b,
        (ha.arProv_good hG).upd _⟩⟩
    | bool =>
      rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _⟩
      simp only [OpCode.wp, vals] at hw ⊢
      refine ⟨hw, (hG.upd _).cons ⟨rfl, fupd_eq ρ b _, Nat.lt_succ_self b,
        (ha.arProv_good hG).upd _⟩⟩
    | float _ | pair _ _ =>
      exact OpCode.wp_mono _ _ (fun xs hxs => ⟨hxs, hG.freshARVals outD xs⟩) hw
  | cmp o t m hm =>
    cases t with
    | bits w =>
      subst hm
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      simp only [OpCode.wp_cmp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, cast_eq,
        liftCmp] at hw ⊢
      refine ⟨hw, (hG.upd _).cons ⟨rfl, fupd_eq ρ b _, Nat.lt_succ_self b,
        (recordCmpImmProv_good hG o ha hb).upd _⟩⟩
    | bool | float _ | pair _ _ =>
      exact OpCode.wp_mono _ _ (fun xs hxs => ⟨hxs, hG.freshARVals outD xs⟩) hw
  | not t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _⟩
      simp only [OpCode.wp, vals, lift1] at hw ⊢
      refine ⟨hw, ?_⟩
      dsimp only [wrapKept, fupdTup, Tup.zip, List.length_singleton, List.cons_append,
        List.nil_append]
      have hap := ha.arProv_good hG
      have hneg : ARProvGood ρ b (t := .bool)
          (a₁.arProv.map fun cm => ⟨cm.w, cm.op.neg, cm.lhs, cm.lhsKey, cm.imm⟩) (!a₂.val) := by
        cases hp : a₁.arProv with
        | none => trivial
        | some cm =>
          rw [hp] at hap
          exact ⟨hap.1, hap.2.1, by rw [hap.2.2, CmpOp.neg_evalBits]⟩
      exact (hG.upd _).cons ⟨rfl, fupd_eq ρ b _, Nat.lt_succ_self b, hneg.upd _⟩
    | bits _ | float _ | pair _ _ =>
      exact OpCode.wp_mono _ _ (fun xs hxs => ⟨hxs, hG.freshARVals outD xs⟩) hw
  | _ =>
    all_goals exact OpCode.wp_mono _ _ (fun xs hxs => ⟨hxs, hG.freshARVals outD xs⟩) hw

theorem tryAddrReassocOne_sound {G : Ctx (ARVal Val) Val} {ρ : FEnv} {b : Nat}
    (hG : ARGood ρ b G) {n : Nat} {base₁ off₁ : Arg (ARVal Val) (.bits n)}
    {base₂ off₂ : Arg Val (.bits n)} (hb : ArgRel G (.bits n) base₁ base₂)
    (ho : ArgRel G (.bits n) off₁ off₂) {st : ARStep Val [.bits n]}
    (hst : tryAddrReassocOne base₁ off₁ = some st) :
    match st with
    | .addrShl _ isSub base inv iv _ sh _ disp =>
      base.val = base₂.val ∧
        (if isSub then ((base.val - (inv.val <<< sh)) + (iv.val <<< sh)) + disp
         else ((base.val + (inv.val <<< sh)) + (iv.val <<< sh)) + disp) =
        base₂.val + off₂.val
    | .addrPlain _ isSub base inv iv _ _ disp =>
      base.val = base₂.val ∧
        (if isSub then ((base.val - inv.val) + iv.val) + disp
         else ((base.val + inv.val) + iv.val) + disp) =
        base₂.val + off₂.val
    | _ => False := by
  dsimp only [tryAddrReassocOne] at hst
  split at hst
  · cases hst
  · have hop := (ho.arProv_good hG).1
    have hbv := hb.arOut_val hG
    cases hp : off₁.arProv.addr? with
    | none => rw [hp] at hst; cases hst
    | some ad =>
      have had := hop ad hp
      rw [hp] at hst
      cases ad with
      | addVC _ _ _ | shlVC _ _ _ _ _ => cases hst
      | shlAddVV x dx y dy sh hsh disp =>
        dsimp only at hst
        simp only [AddrDefGood] at had
        split at hst
        · cases hst; refine ⟨hbv, ?_⟩
          simp only [Bool.false_eq_true, ↓reduceIte, hbv, had, bv_add_shl_add_disp]
        · split at hst
          · cases hst; refine ⟨hbv, ?_⟩
            simp only [Bool.false_eq_true, ↓reduceIte, hbv, had, BitVec.add_comm x.val y.val,
              bv_add_shl_add_disp]
          · cases hst
      | shlSubVV x dx y dy sh hsh disp =>
        dsimp only at hst
        simp only [AddrDefGood] at had
        split at hst
        · cases hst; refine ⟨hbv, ?_⟩
          simp only [↓reduceIte, hbv, had, bv_add_shl_sub_disp]
        · cases hst
      | addVV x dx y dy disp =>
        dsimp only at hst
        simp only [AddrDefGood] at had
        split at hst
        · cases hst; refine ⟨hbv, ?_⟩
          simp only [Bool.false_eq_true, ↓reduceIte, hbv, had, bv_add_add_disp]
        · split at hst
          · cases hst; refine ⟨hbv, ?_⟩
            simp only [Bool.false_eq_true, ↓reduceIte, hbv, had, BitVec.add_comm x.val y.val,
              bv_add_add_disp]
          · cases hst
      | subVV x dx y dy disp =>
        dsimp only at hst
        simp only [AddrDefGood] at had
        split at hst
        · cases hst; refine ⟨hbv, ?_⟩
          simp only [↓reduceIte, hbv, had, bv_add_sub_disp]
        · cases hst

theorem tryRangeStep_sound {G : Ctx (ARVal Val) Val} {ρ : FEnv} {b outD : Nat}
    (hG : ARGood ρ b G) (isOr : Bool) {a₁ b₁ : Arg (ARVal Val) .bool} {a₂ b₂ : Arg Val .bool}
    (ha : ArgRel G .bool a₁ a₂) (hb : ArgRel G .bool b₁ b₂)
    {st : ARStep Val [.bool]} (hst : tryRangeStep isOr outD b a₁ b₁ = some st)
    {P : Tup Val [.bool] → Prop}
    (hw : P ((if isOr then a₂.val || b₂.val else a₂.val && b₂.val), ())) :
    match st with
    | .elim res =>
      ∃ xs, P xs ∧ ARGood ρ b (Tup.zip res xs ++ G)
    | .emit1 op' wrap =>
      op'.wp fun xs => P xs ∧ ARGood (fupdTup ρ b xs) (b + 1) (Tup.zip (wrap xs) xs ++ G)
    | .rangeSubCmp _ o x lo width _ =>
      P (o.evalBits (x.val - lo) width, ())
    | _ => False := by
  dsimp only [tryRangeStep] at hst
  have hap := ha.arProv_good hG
  have hbp := hb.arProv_good hG
  cases hp1 : a₁.arProv with
  | none => rw [hp1] at hst; cases hst
  | some c1 =>
    cases hp2 : b₁.arProv with
    | none => rw [hp1, hp2] at hst; cases hst
    | some c2 =>
      rw [hp1, hp2] at hst
      rw [hp1] at hap; rw [hp2] at hbp
      rcases c1 with ⟨w1, o1, lhs1, key1, imm1⟩
      rcases c2 with ⟨w2, o2, lhs2, key2, imm2⟩
      dsimp only at hst
      split at hst
      · rename_i hweq
        subst hweq
        dsimp only at hst
        split at hst
        · rename_i hkey
          have hkeq : key1 = key2 := fKeyBeq_iff_eq.mp hkey
          have hlhs : lhs1.val = lhs2.val := by
            have h1 := hap.1; have h2 := hbp.1; rw [hkeq] at h1; exact h1.symm.trans h2
          cases hb1 : toRangeBound o1 imm1 with
          | none => rw [hb1] at hst; cases hst
          | some rb1 =>
            cases hb2 : toRangeBound o2 imm2 with
            | none => rw [hb1, hb2] at hst; cases hst
            | some rb2 =>
              rw [hb1, hb2] at hst
              dsimp only at hst
              have hev1 : rb1.eval lhs1.val = a₂.val :=
                (toRangeBound_eval o1 imm1 lhs1.val hb1).trans hap.2.2.symm
              have hev2 : rb2.eval lhs1.val = b₂.val :=
                (toRangeBound_eval o2 imm2 lhs1.val hb2).trans (hlhs ▸ hbp.2.2.symm)
              cases isOr with
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte] at hst hw
                cases hm : matchAndBounds rb1 rb2 with
                | none => rw [hm] at hst; cases hst
                | some triple =>
                  rcases triple with ⟨signed, lo, hi⟩
                  rw [hm] at hst; dsimp only at hst
                  have hcomb : (a₂.val && b₂.val) =
                      if (if signed then lo.slt hi else lo.ult hi) then
                        (lhs1.val - lo).ult (hi - lo)
                      else false := by
                    rw [← hev1, ← hev2]
                    cases rb1 <;> cases rb2 <;> simp only [matchAndBounds] at hm <;> try cases hm
                    · split at hm
                      · injection hm with hm; rcases hm with ⟨rfl, rfl, rfl⟩
                        rename_i hse; have hse' : _ = _ := eq_of_beq hse; subst hse'
                        cases signed
                        · exact bv_range_and_u lhs1.val lo hi
                        · exact bv_range_and_s lhs1.val lo hi
                      · cases hm
                    · split at hm
                      · injection hm with hm; rcases hm with ⟨rfl, rfl, rfl⟩
                        rename_i hse; have hse' : _ = _ := eq_of_beq hse; subst hse'
                        rw [Bool.and_comm]
                        cases signed
                        · exact bv_range_and_u lhs1.val lo hi
                        · exact bv_range_and_s lhs1.val lo hi
                      · cases hm
                  cases hlt : (if signed then lo.slt hi else lo.ult hi) with
                  | false =>
                    rw [hlt] at hst hcomb
                    simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true] at hst hcomb
                    cases hst
                    exact ⟨(false, ()), hcomb ▸ hw,
                      by dsimp only [Tup.zip, List.cons_append, List.nil_append]
                         exact hG.cons (ARValGood.ofImm (t := .bool) false)⟩
                  | true =>
                    rw [hlt] at hst hcomb
                    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hst hcomb
                    cases hlo0 : (lo == 0#w1) with
                    | true =>
                      rw [hlo0] at hst; simp only [↓reduceIte] at hst
                      have hlo0' : lo = 0#w1 := eq_of_beq hlo0
                      subst hlo0'
                      simp only [BitVec.sub_zero] at hcomb
                      cases hst
                      simp only [Op.wp, op2, vals, OpCode.wp_cmp, Ty.hasFloat, Bool.false_eq_true,
                        ↓reduceIte, cast_eq, liftCmp, CmpOp.evalBits, Arg.val_imm]
                      exact ⟨hcomb ▸ hw, hG.freshOne outD _⟩
                    | false =>
                      rw [hlo0] at hst; simp only [Bool.false_eq_true, ↓reduceIte] at hst
                      cases hst
                      simpa [CmpOp.evalBits] using hcomb ▸ hw
              | true =>
                simp only [↓reduceIte] at hst hw
                cases hm : matchOrBounds rb1 rb2 with
                | none => rw [hm] at hst; cases hst
                | some triple =>
                  rcases triple with ⟨signed, lo, hi⟩
                  rw [hm] at hst; dsimp only at hst
                  have hcomb : (a₂.val || b₂.val) =
                      if (if signed then lo.slt hi else lo.ult hi) then
                        (hi - lo).ule (lhs1.val - lo)
                      else true := by
                    rw [← hev1, ← hev2]
                    cases rb1 <;> cases rb2 <;> simp only [matchOrBounds] at hm <;> try cases hm
                    · split at hm
                      · injection hm with hm; rcases hm with ⟨rfl, rfl, rfl⟩
                        rename_i hse; have hse' : _ = _ := eq_of_beq hse; subst hse'
                        rw [Bool.or_comm]
                        cases signed
                        · exact bv_range_or_u lhs1.val lo hi
                        · exact bv_range_or_s lhs1.val lo hi
                      · cases hm
                    · split at hm
                      · injection hm with hm; rcases hm with ⟨rfl, rfl, rfl⟩
                        rename_i hse; have hse' : _ = _ := eq_of_beq hse; subst hse'
                        cases signed
                        · exact bv_range_or_u lhs1.val lo hi
                        · exact bv_range_or_s lhs1.val lo hi
                      · cases hm
                  cases hlt : (if signed then lo.slt hi else lo.ult hi) with
                  | false =>
                    rw [hlt] at hst hcomb
                    simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true] at hst hcomb
                    cases hst
                    exact ⟨(true, ()), hcomb ▸ hw,
                      by dsimp only [Tup.zip, List.cons_append, List.nil_append]
                         exact hG.cons (ARValGood.ofImm (t := .bool) true)⟩
                  | true =>
                    rw [hlt] at hst hcomb
                    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hst hcomb
                    cases hlo0 : (lo == 0#w1) with
                    | true =>
                      rw [hlo0] at hst; simp only [↓reduceIte] at hst
                      have hlo0' : lo = 0#w1 := eq_of_beq hlo0
                      subst hlo0'
                      simp only [BitVec.sub_zero] at hcomb
                      cases hst
                      simp only [Op.wp, op2, vals, OpCode.wp_cmp, Ty.hasFloat, Bool.false_eq_true,
                        ↓reduceIte, cast_eq, liftCmp, CmpOp.evalBits, Arg.val_imm]
                      exact ⟨hcomb ▸ hw, hG.freshOne outD _⟩
                    | false =>
                      rw [hlo0] at hst; simp only [Bool.false_eq_true, ↓reduceIte] at hst
                      cases hst
                      simpa [CmpOp.evalBits] using hcomb ▸ hw
        · cases hst
      · cases hst

end LeanQbe.T
