module

public import LeanQbe.T.RegaLemmas1

/-!
# Soundness Proofs for Narrow/Wide Comparison & Zero-Jnz Flag Reuse (`C-P1.3`)

Proves:
* `symValAt_eq_symBits` / `symValAt_of_toSymArg`
* `reuseCmpPair_ok`: covers exact width (`w = n`), narrow flag / wide consumer (`0 < w < n`), and
  symmetric wide flag / narrow consumer (`0 < n < w`) via `Agree.ctx_uniq` and `FlagFactOk`.
* `cmpZeroFlagCond_ok`: deferred `jnz` (`findJnzCond`) flag reuse routed through `reuseCmpPair?`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace Rega

private theorem symBits_imm64' {G : VCtx} {w : Nat} (hw : w ≤ 64) (v : BitVec w) :
    SymBits G w v (.immBits w (v.setWidth 64)) :=
  ⟨rfl, by rw [BitVec.setWidth_setWidth_of_le v hw, BitVec.setWidth_eq]⟩

private theorem cmpEval_signExtend {m n : Nat} (_hm0 : 0 < m) (hmn : m < n)
    {co : CmpOp} (hco : cmpIsSignedOrEq co = true) (a : BitVec m) (c : BitVec n)
    (hci : (c.truncate m).signExtend n = c) :
    co.evalBits (a.signExtend n) c = co.evalBits a (c.truncate m) := by
  have hmle : m ≤ n := Nat.le_of_lt hmn
  have h1 : (a.signExtend n).toInt = a.toInt := by
    simpa [BitVec.signExtend] using BitVec.toInt_signExtend_of_le (x := a) hmle
  have h2 : ((c.truncate m).signExtend n).toInt = (c.truncate m).toInt := by
    simpa [BitVec.signExtend] using
      BitVec.toInt_signExtend_of_le (x := c.truncate m) hmle
  have goalEq : co.evalBits (a.signExtend n) ((c.truncate m).signExtend n) =
      co.evalBits a (c.truncate m) := by
    cases co with
    | eq =>
      simp only [CmpOp.evalBits, decide_eq_decide]
      exact ⟨fun h => BitVec.eq_of_toInt_eq (by rw [← h1, ← h2, h]),
             fun h => congrArg (fun x => BitVec.signExtend n x) h⟩
    | ne =>
      simp only [CmpOp.evalBits, decide_eq_decide]
      exact not_congr ⟨fun h => BitVec.eq_of_toInt_eq (by rw [← h1, ← h2, h]),
                       fun h => congrArg (fun x => BitVec.signExtend n x) h⟩
    | slt => simp only [CmpOp.evalBits, BitVec.slt_eq_decide, h1, h2]
    | sle => simp only [CmpOp.evalBits, BitVec.sle_eq_decide, h1, h2]
    | sgt => simp only [CmpOp.evalBits, BitVec.slt_eq_decide, h1, h2]
    | sge => simp only [CmpOp.evalBits, BitVec.sle_eq_decide, h1, h2]
    | ult | ule | ugt | uge => simp [cmpIsSignedOrEq] at hco
  simpa [hci] using goalEq

private theorem cmpEval_zeroExtend {m n : Nat} (hmn : m < n)
    {co : CmpOp} (hco : cmpIsUnsignedOrEq co = true) (a : BitVec m) (c : BitVec n)
    (hci : (c.truncate m).zeroExtend n = c) :
    co.evalBits (a.zeroExtend n) c = co.evalBits a (c.truncate m) := by
  have hmle : m ≤ n := Nat.le_of_lt hmn
  have h1 : (a.zeroExtend n).toNat = a.toNat := by
    simpa [BitVec.zeroExtend] using BitVec.toNat_setWidth_of_le (b := a) hmle
  have h2 : ((c.truncate m).zeroExtend n).toNat = (c.truncate m).toNat := by
    simpa [BitVec.zeroExtend] using BitVec.toNat_setWidth_of_le (b := c.truncate m) hmle
  have goalEq : co.evalBits (a.zeroExtend n) ((c.truncate m).zeroExtend n) =
      co.evalBits a (c.truncate m) := by
    cases co with
    | eq =>
      simp only [CmpOp.evalBits, decide_eq_decide]
      exact ⟨fun h => BitVec.eq_of_toNat_eq (by rw [← h1, ← h2, h]),
             fun h => congrArg (fun x => BitVec.zeroExtend n x) h⟩
    | ne =>
      simp only [CmpOp.evalBits, decide_eq_decide]
      exact not_congr ⟨fun h => BitVec.eq_of_toNat_eq (by rw [← h1, ← h2, h]),
                       fun h => congrArg (fun x => BitVec.zeroExtend n x) h⟩
    | ult => simp only [CmpOp.evalBits, BitVec.ult_eq_decide, h1, h2]
    | ule => simp only [CmpOp.evalBits, BitVec.ule_eq_decide, h1, h2]
    | ugt => simp only [CmpOp.evalBits, BitVec.ult_eq_decide, h1, h2]
    | uge => simp only [CmpOp.evalBits, BitVec.ule_eq_decide, h1, h2]
    | slt | sle | sgt | sge => simp [cmpIsUnsignedOrEq] at hco
  simpa [hci] using goalEq

theorem symValAt_eq_symBits {G : VCtx} {w : Nat} {v1 v2 : BitVec w} {sa : SymArg}
    (h1 : SymValAt G w v1 sa) (h2 : SymBits G w v2 sa) : v1 = v2 := by
  cases sa with
  | var x => exact h2 v1 h1
  | immBits w' c => rcases h1 with ⟨rfl, rfl⟩; exact h2.2
  | _ => cases h1

theorem symValAt_of_toSymArg {T : Target} {G : VCtx} {w : Nat} (hw : w ≤ 64)
    {x₁ : Arg Val (.bits w)} {x : Arg VNat (.bits w)} {sx : SymArg}
    (hrel : ArgRel G (.bits w) x₁ x) (hsx : toSymArg T.toIsa (.bits w) x = some sx) :
    SymValAt G w x₁.val sx := by
  cases hrel with
  | imm =>
    simp only [toSymArg] at hsx; split at hsx
    · simp only [Option.some.injEq] at hsx; subst hsx; exact symBits_imm64' (G := G) hw _
    · simp at hsx
  | var hm => simp only [toSymArg, Option.some.injEq] at hsx; subst hsx; exact hm

theorem normZeroCmp_evalBits {n : Nat} (o : CmpOp) (a : BitVec n) :
    (normZeroCmp o).evalBits a 0#n = o.evalBits a 0#n := by
  cases o
  all_goals first
    | rfl
    | (simp only [normZeroCmp, CmpOp.evalBits, BitVec.ult, BitVec.ule, BitVec.toNat_zero]
       by_cases h : a = 0#n
       · subst h; simp
       · have hpos : 0 < a.toNat :=
           Nat.pos_of_ne_zero fun hz => h (BitVec.eq_of_toNat_eq (by simpa using hz))
         have hne : a.toNat ≠ 0 := Nat.ne_of_gt hpos
         simp [h, hpos, hne])

theorem normCmpZero1_evalBits {n : Nat} (o : CmpOp) (a c : BitVec n) :
    (normCmpZero1 o c).1.evalBits a (normCmpZero1 o c).2 = o.evalBits a c := by
  unfold normCmpZero1
  by_cases hc0 : c = 0#n
  · subst hc0; simp [normZeroCmp_evalBits]
  · have hc0b : (c == 0#n) = false := beq_eq_false_iff_ne.mpr hc0
    simp only [hc0b, Bool.false_eq_true, ite_false]
    by_cases hcond : c = 1#n ∧ 1 ≤ n
    · obtain ⟨rfl, hn1⟩ := hcond
      have htb : (1#n == 1#n && Nat.ble 1 n) = true := by simp [Nat.ble_eq, hn1]
      simp only [htb, ite_true]
      have hpow1 : (2 : Nat) ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
      have h1toNat : (1#n).toNat = 1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < 2 ^ n)]
      cases o with
      | ult =>
        simp only [CmpOp.evalBits, BitVec.ult, h1toNat]
        by_cases ha0 : a = 0#n <;> simp [ha0]
        have : a.toNat ≠ 0 := fun h => ha0 (BitVec.eq_of_toNat_eq (by simpa using h))
        omega
      | uge =>
        simp only [CmpOp.evalBits, BitVec.ule, h1toNat]
        by_cases ha0 : a = 0#n <;> simp [ha0]
        have : a.toNat ≠ 0 := fun h => ha0 (BitVec.eq_of_toNat_eq (by simpa using h))
        omega
      | sge =>
        dsimp only; split
        · rename_i hn2
          have hn2' : 2 ≤ n := by simpa [Nat.ble_eq] using hn2
          have hpow2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn2'
          have hpow2' : (4 : Nat) ≤ 2 ^ n := hpow2
          have h1s : (1#n).toInt = 1 := by
            rw [BitVec.toInt_eq_toNat_cond, h1toNat]
            simp [show 2 * 1 < 2 ^ n by omega]
          simp only [CmpOp.evalBits, BitVec.slt, BitVec.sle, h1s, BitVec.toInt_zero]
          by_cases ha0 : (0 : Int) < a.toInt
          · simp [ha0, show (1 : Int) ≤ a.toInt by omega]
          · have hnot1 : ¬ ((1 : Int) ≤ a.toInt) := by omega
            simp [ha0, hnot1]
        · rfl
      | slt =>
        dsimp only; split
        · rename_i hn2
          have hn2' : 2 ≤ n := by simpa [Nat.ble_eq] using hn2
          have hpow2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn2'
          have hpow2' : (4 : Nat) ≤ 2 ^ n := hpow2
          have h1s : (1#n).toInt = 1 := by
            rw [BitVec.toInt_eq_toNat_cond, h1toNat]
            simp [show 2 * 1 < 2 ^ n by omega]
          simp only [CmpOp.evalBits, BitVec.slt, BitVec.sle, h1s, BitVec.toInt_zero]
          by_cases ha0 : a.toInt ≤ 0
          · have hlt1 : a.toInt < 1 := by omega
            simp [ha0, hlt1]
          · have hnlt1 : ¬ (a.toInt < 1) := by omega
            simp [ha0, hnlt1]
        · rfl
      | _ => rfl
    · have hfb : (c == 1#n && Nat.ble 1 n) = false := by
        cases h1 : (c == 1#n) <;> cases h2 : Nat.ble 1 n <;> simp_all [Nat.ble_eq]
      simp only [hfb, Bool.false_eq_true, ite_false]

theorem normCmpExpr_ok {G : VCtx} {n : Nat} {co co' : CmpOp}
    {a₁ b₁ : Arg Val (.bits n)} {a b a' b' : Arg VNat (.bits n)}
    (ha : ArgRel G (.bits n) a₁ a) (hb : ArgRel G (.bits n) b₁ b)
    (hn : normCmpExpr co n a b = (co', a', b')) :
    ∃ a₁' b₁' : Arg Val (.bits n),
      ArgRel G (.bits n) a₁' a' ∧ ArgRel G (.bits n) b₁' b' ∧
      co.evalBits a₁.val b₁.val = co'.evalBits a₁'.val b₁'.val := by
  cases a with
  | var t =>
    cases b with
    | imm c =>
      simp only [normCmpExpr, Prod.mk.injEq] at hn
      rcases hn with ⟨rfl, rfl, rfl⟩
      cases hb with | imm =>
      exact ⟨a₁, .imm (normCmpZero1 co c).2, ha, ArgRel.imm _,
        (normCmpZero1_evalBits co a₁.val c).symm⟩
    | var u =>
      simp only [normCmpExpr, Prod.mk.injEq] at hn
      rcases hn with ⟨rfl, rfl, rfl⟩
      exact ⟨a₁, b₁, ha, hb, rfl⟩
  | imm c =>
    cases b with
    | var t =>
      dsimp only [normCmpExpr] at hn
      split at hn
      · next hc0 =>
        simp only [Prod.mk.injEq] at hn
        rcases hn with ⟨rfl, rfl, rfl⟩
        cases ha with | imm =>
        refine ⟨b₁, .imm 0#n, hb, ArgRel.imm _, ?_⟩
        change co.evalBits c b₁.val = (normCmpZero1 co.swap c).fst.evalBits b₁.val 0#n
        rw [← CmpOp.swap_evalBits, ← normCmpZero1_evalBits co.swap b₁.val c, beq_iff_eq.mp hc0]
      · simp only [Prod.mk.injEq] at hn
        rcases hn with ⟨rfl, rfl, rfl⟩
        exact ⟨a₁, b₁, ha, hb, rfl⟩
    | imm d =>
      simp only [normCmpExpr, Prod.mk.injEq] at hn
      rcases hn with ⟨rfl, rfl, rfl⟩
      exact ⟨a₁, b₁, ha, hb, rfl⟩

private theorem reuseWideSide_ok {G : VCtx} {w n : Nat} (hn0 : 0 < n) (hnw : n < w)
    {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d)
    (huniq : ∀ {t : Ty} {x : Nat} {v₁ v₂ : Val t}, ⟨t, v₁, x⟩ ∈ G → ⟨t, v₂, x⟩ ∈ G → v₁ = v₂)
    {co' coBase : CmpOp} {x0 : Nat} {cn vx : BitVec n}
    {side other sa sb : SymArg} {vS : BitVec w}
    (hmx : ⟨.bits n, vx, x0⟩ ∈ G) (hsAt : SymValAt G w vS side)
    (hwd : reuseWideSide? defs w n co' x0 cn side other = some (coBase, sa, sb)) :
    coBase = co' ∧ ∃ va vb : BitVec w, SymValAt G w va sa ∧ SymValAt G w vb sb ∧
      co'.evalBits vx cn = coBase.evalBits va vb := by
  cases side with
  | immBool _ | immBits _ _ | immVec _ _ => simp [reuseWideSide?] at hwd
  | var t =>
    cases other with
    | var _ | immBool _ | immVec _ _ => simp [reuseWideSide?] at hwd
    | immBits w' cw64 =>
      simp only [reuseWideSide?] at hwd
      split at hwd; · simp at hwd
      rename_i hw'
      have hwEq : w' = w := by simpa [Nat.beq_eq] using hw'
      subst hwEq
      cases hdef : defs.find? t with
      | none => simp [hdef] at hwd
      | some df =>
        cases df with
        | sextVar m w'' x =>
          simp only [hdef] at hwd
          split at hwd
          · rename_i hgd
            simp only [Option.some.injEq, Prod.mk.injEq] at hwd
            rcases hwd with ⟨rfl, rfl, rfl⟩
            simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hgd
            obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hco⟩, hcn⟩, hcw⟩ := hgd
            obtain ⟨va0, hmx0, hvS⟩ := (hdefs t _ hdef).2.2.2 vS hsAt
            obtain rfl : va0 = vx := huniq hmx0 hmx
            refine ⟨rfl, vS, cw64.setWidth _, hsAt, ⟨rfl, rfl⟩, ?_⟩
            rw [hvS, ← hcn, (cmpEval_signExtend hn0 hnw hco va0 (cw64.setWidth _) hcw).symm]
          · simp at hwd
        | zextVar m w'' x =>
          simp only [hdef] at hwd
          split at hwd
          · rename_i hgd
            simp only [Option.some.injEq, Prod.mk.injEq] at hwd
            rcases hwd with ⟨rfl, rfl, rfl⟩
            simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hgd
            obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hco⟩, hcn⟩, hcw⟩ := hgd
            obtain ⟨va0, hmx0, hvS⟩ := (hdefs t _ hdef).2.2.2 vS hsAt
            obtain rfl : va0 = vx := huniq hmx0 hmx
            refine ⟨rfl, vS, cw64.setWidth _, hsAt, ⟨rfl, rfl⟩, ?_⟩
            rw [hvS, ← hcn, (cmpEval_zeroExtend hnw hco va0 (cw64.setWidth _) hcw).symm]
          · simp at hwd
        | _ => simp [hdef] at hwd

theorem reuseCmpPair_ok {T : Target} {G : VCtx} {w n : Nat} (hw : w ≤ 64) {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d)
    (huniq : ∀ {t : Ty} {x : Nat} {v₁ v₂ : Val t}, ⟨t, v₁, x⟩ ∈ G → ⟨t, v₂, x⟩ ∈ G → v₁ = v₂)
    {lhs rhs : SymArg} {vL vR : BitVec w}
    (hlhs : SymValAt G w vL lhs) (hrhs : SymValAt G w vR rhs)
    {co : CmpOp} {a₁ b₁ : Arg Val (.bits n)} {a b : Arg VNat (.bits n)}
    (ha : ArgRel G (.bits n) a₁ a) (hb : ArgRel G (.bits n) b₁ b)
    {coBase : CmpOp} {sa sb : SymArg}
    (h : reuseCmpPair? T.toIsa defs w lhs rhs n co a b = some (coBase, sa, sb)) :
    ∃ va vb : BitVec w, SymValAt G w va sa ∧ SymValAt G w vb sb ∧
      co.evalBits a₁.val b₁.val = coBase.evalBits va vb := by
  unfold reuseCmpPair? at h
  rcases hnorm : normCmpExpr co n a b with ⟨co0, a0, b0⟩
  rw [hnorm] at h
  dsimp only at h
  obtain ⟨a₁', b₁', ha', hb', hev⟩ := normCmpExpr_ok ha hb hnorm
  rw [hev]
  split at h
  · rename_i hwn
    obtain rfl : w = n := Nat.beq_eq.mp hwn
    obtain ⟨sa', hsa, hbb⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨sb', hsb, hp⟩ := Option.map_eq_some_iff.mp hbb
    simp only [Prod.mk.injEq] at hp; rcases hp with ⟨rfl, rfl, rfl⟩
    exact ⟨a₁'.val, b₁'.val, symValAt_of_toSymArg (T := T) hw ha' hsa,
      symValAt_of_toSymArg (T := T) hw hb' hsb, rfl⟩
  · split at h
    · rename_i hlt
      simp only [Bool.and_eq_true, Nat.blt_eq] at hlt
      obtain ⟨hw0, hwn⟩ := hlt
      have ext_ok : ∀ {co' : CmpOp} {t : Nat} {ci : BitVec n} {vt : BitVec n}
          (hmt : ⟨.bits n, vt, t⟩ ∈ G),
          (match defs.find? t with
           | some (.sextVar m n' x) =>
             if Nat.beq m w && Nat.beq n' n && cmpIsSignedOrEq co' &&
                (ci.truncate w).signExtend n == ci then some x else none
           | some (.zextVar m n' x) =>
             if Nat.beq m w && Nat.beq n' n && cmpIsUnsignedOrEq co' &&
                (ci.truncate w).zeroExtend n == ci then some x else none
           | _ => none).map (fun x => (co', .var x, .immBits w ((ci.truncate w).setWidth 64))) =
            some (coBase, sa, sb) →
          coBase = co' ∧ ∃ va vb : BitVec w, SymValAt G w va sa ∧ SymValAt G w vb sb ∧
            co'.evalBits vt ci = coBase.evalBits va vb := by
        intro co' t ci vt hmt hx
        obtain ⟨x, hok, hp⟩ := Option.map_eq_some_iff.mp hx
        simp only [Prod.mk.injEq] at hp; rcases hp with ⟨rfl, rfl, rfl⟩
        cases hdef : defs.find? t with
        | none => simp [hdef] at hok
        | some df =>
          cases df with
          | sextVar mw nw x' =>
            simp only [hdef] at hok; split at hok
            · rename_i hgd; simp only [Option.some.injEq] at hok; subst hok
              simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hgd
              obtain ⟨⟨⟨rfl, rfl⟩, hco⟩, hci⟩ := hgd
              obtain ⟨va, hmx, rfl⟩ := (hdefs t _ hdef).2.2.2 vt hmt
              exact ⟨rfl, va, ci.truncate mw, hmx, symBits_imm64' (G := G) hw _,
                cmpEval_signExtend hw0 hwn hco va ci hci⟩
            · simp at hok
          | zextVar mw nw x' =>
            simp only [hdef] at hok; split at hok
            · rename_i hgd; simp only [Option.some.injEq] at hok; subst hok
              simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hgd
              obtain ⟨⟨⟨rfl, rfl⟩, hco⟩, hci⟩ := hgd
              obtain ⟨va, hmx, rfl⟩ := (hdefs t _ hdef).2.2.2 vt hmt
              exact ⟨rfl, va, ci.truncate mw, hmx, symBits_imm64' (G := G) hw _,
                cmpEval_zeroExtend hwn hco va ci hci⟩
            · simp at hok
          | _ => simp [hdef] at hok
      cases a0 with
      | var t =>
        cases b0 with
        | imm ci =>
          cases ha' with | var hmt => cases hb' with | imm =>
          exact (ext_ok hmt h).2
        | var _ => simp at h
      | imm ci =>
        cases b0 with
        | var t =>
          cases ha' with | imm => cases hb' with | var hmt =>
          obtain ⟨_, va, vb, hsa, hsb, hevc⟩ := ext_ok hmt h
          exact ⟨va, vb, hsa, hsb, (CmpOp.swap_evalBits co0 _ _).symm.trans hevc⟩
        | imm _ => simp at h
    · split at h
      · rename_i hlt'
        simp only [Bool.and_eq_true, Nat.blt_eq] at hlt'
        obtain ⟨hn0, hnw⟩ := hlt'
        cases a0 with
        | var x =>
          cases b0 with
          | imm cn =>
            cases ha' with | var hmx => cases hb' with | imm =>
            rcases orElse_eq_some h with h1 | h2
            · exact (reuseWideSide_ok hn0 hnw hdefs huniq hmx hlhs h1).2
            · exact (reuseWideSide_ok hn0 hnw hdefs huniq hmx hrhs h2).2
          | var _ => simp at h
        | imm cn =>
          cases b0 with
          | var x =>
            cases ha' with | imm => cases hb' with | var hmx =>
            rcases orElse_eq_some h with h1 | h2
            · obtain ⟨_, va, vb, hsa, hsb, hevc⟩ :=
                reuseWideSide_ok hn0 hnw hdefs huniq hmx hlhs h1
              exact ⟨va, vb, hsa, hsb, (CmpOp.swap_evalBits co0 _ _).symm.trans hevc⟩
            · obtain ⟨_, va, vb, hsa, hsb, hevc⟩ :=
                reuseWideSide_ok hn0 hnw hdefs huniq hmx hrhs h2
              exact ⟨va, vb, hsa, hsb, (CmpOp.swap_evalBits co0 _ _).symm.trans hevc⟩
          | imm _ => simp at h
      · simp at h

theorem cmpZeroFlagCond_ok {T : Target} {G : VCtx} {nv : Nat}
    {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)}
    (hA : Agree T G nv st s σ)
    {co : CmpOp} {w y : Nat} {vy : BitVec w} (hmy : ⟨.bits w, vy, y⟩ ∈ G)
    {c : T.Cond} (hcf : cmpZeroFlagCond? T.toIsa st.defs st.flags co w y = some c) :
    T.mach.evalCond s c = co.evalBits vy 0#w := by
  cases hfl : st.flags with
  | none => simp [cmpZeroFlagCond?, hfl] at hcf
  | some fl =>
    cases fl with
    | cmp w' lhs rhs eqNe =>
      have hflOk := hA.flags_ok
      rw [hfl] at hflOk
      obtain ⟨hw', va, vb, hlhsAt, hlhs, hrhsAt, hrhs, hcmp⟩ := hflOk
      simp only [cmpZeroFlagCond?, hfl] at hcf
      obtain ⟨⟨coBase, sa, sb⟩, hpair, h⟩ := Option.bind_eq_some_iff.mp hcf
      obtain ⟨coU, hcoU, hbind⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨va', vb', hsa, hsb, hbase⟩ := reuseCmpPair_ok (T := T) hw' hA.defs hA.ctx_uniq
        hlhsAt hrhsAt (ArgRel.var hmy) (@ArgRel.imm Val VNat G (.bits w) (0#w)) hpair
      have hgd : (!eqNe || coU == .eq || coU == .ne) = true ∧ T.gpr.condOfCmp? coU = some c := by
        split at hbind
        · rename_i hok; exact ⟨hok, hbind⟩
        · simp at hbind
      change co.evalBits (@Arg.imm Val (.bits w) vy).val (@Arg.imm Val (.bits w) (0#w)).val =
        coBase.evalBits va' vb' at hbase
      simp only [Arg.val] at hbase
      rw [hbase]
      split at hcoU
      · next hmt =>
        simp only [Bool.and_eq_true, symArgEq_iff] at hmt
        obtain ⟨rfl, rfl⟩ := hmt
        simp only [Option.some.injEq] at hcoU; subst hcoU
        rw [hcmp coBase c hgd.1 hgd.2, symValAt_eq_symBits hsa hlhs,
          symValAt_eq_symBits hsb hrhs]
      · split at hcoU
        · next hmt =>
          simp only [Bool.and_eq_true, symArgEq_iff] at hmt
          obtain ⟨rfl, rfl⟩ := hmt
          simp only [Option.some.injEq] at hcoU; subst hcoU
          rw [hcmp coBase.swap c hgd.1 hgd.2, CmpOp.swap_evalBits,
            symValAt_eq_symBits hsa hrhs, symValAt_eq_symBits hsb hlhs]
        · simp at hcoU

end Rega
end LeanQbe.T
