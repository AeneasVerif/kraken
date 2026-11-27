module

public import LeanQbe.T.LeanLCNF.Sem.Perceus3

/-!
# Perceus Tier-P → Tier-H Soundness: Nat & UInt Primitive Simulations (`PerceusPrims1`)

Part 1 of safe primitive simulations (`primNatP_sim_fast`, `primUintP_sim`), plus shared
BitVec, String, `splitDot`, `HDecN`, `evalArgs`, and `ValRep` helpers used by `PerceusPrims`.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

public section

/-! ## 1. BitVec, String, `splitDot` & `HDecN` Helpers -/

theorem natRepR0_small {w : BitVec 64} {n : Nat} {objs : List LcnfObj}
    (hn : n < 2 ^ 63) : natRepR0 w n objs ↔ w = BitVec.ofNat 64 (2 * n + 1) := by
  simp [natRepR0, hn]

theorem natRepR0_of_small {n : Nat} (hn : n < 2 ^ 63) (objs : List LcnfObj) :
    natRepR0 (BitVec.ofNat 64 (2 * n + 1)) n objs :=
  (natRepR0_small hn).mpr rfl

theorem boxNat_and1_eq_one (n : Nat) : BitVec.ofNat 64 (2 * n + 1) &&& 1#64 = 1#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.and_one_is_mod]
  simp

theorem boxNat_pair_and1_ne_zero (a b : Nat) :
    (BitVec.ofNat 64 (2 * a + 1) &&& BitVec.ofNat 64 (2 * b + 1) &&& 1#64 == 0#64) = false := by
  rw [beq_false_of_ne]
  intro h
  have h0 : (BitVec.ofNat 64 (2 * a + 1) &&& BitVec.ofNat 64 (2 * b + 1) &&& 1#64).toNat =
      (0#64).toNat := by rw [h]
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat] at h0
  rw [show (1 : Nat) % 2 ^ 64 = 1 from by decide, Nat.and_one_is_mod] at h0
  have ha : (2 * a + 1) % 2 ^ 64 % 2 = 1 := by omega
  have hb : (2 * b + 1) % 2 ^ 64 % 2 = 1 := by omega
  have hbit : (((2 * a + 1) % 2 ^ 64 &&& (2 * b + 1) % 2 ^ 64).testBit 0) = true := by
    rw [Nat.testBit_and]; simp [Nat.testBit_zero, ha, hb]
  simp only [Nat.testBit_zero] at hbit
  revert hbit; simp [h0]

theorem boxNat_testBit_zero (n : Nat) : (2 * n + 1).testBit 0 = true := by simp [Nat.testBit]

theorem boxNat_testBit_succ (n m : Nat) : (2 * n + 1).testBit (m + 1) = n.testBit m := by
  rw [Nat.testBit_succ, show (2 * n + 1) / 2 = n from by omega]

theorem bv64_tagged_ofNat64 (x : BitVec 64) :
    x <<< 1 ||| 1#64 = BitVec.ofNat 64 (2 * x.toNat + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.shiftLeft_eq, Nat.pow_one]
  have h1 : (1 : Nat) % 2 ^ 64 = 1 := by decide
  rw [h1]
  have hor : ∀ k : Nat, k * 2 ||| 1 = k * 2 + 1 := fun k => by
    apply Nat.eq_of_testBit_eq; intro j
    cases j with
    | zero => simp [Nat.testBit, Nat.or_comm]
    | succ m =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
        show (k * 2) / 2 = k from by omega, show (k * 2 + 1) / 2 = k from by omega,
        show (1 : Nat) / 2 = 0 from by decide, Nat.zero_testBit]
      simp
  have hmod : (x.toNat * 2 % 2 ^ 64) = (x.toNat % 2 ^ 63) * 2 := by omega
  have hmod2 : ((2 * x.toNat + 1) % 2 ^ 64) = (x.toNat % 2 ^ 63) * 2 + 1 := by omega
  rw [hmod, hmod2, hor]

theorem boxNat_add_eq {a b : Nat} (hs : a + b < 2 ^ 63) :
    let av := BitVec.ofNat 64 (2 * a + 1)
    let bv := BitVec.ofNat 64 (2 * b + 1)
    av - 1#64 + bv = BitVec.ofNat 64 (2 * (a + b) + 1) ∧ ¬(av - 1#64 + bv < bv) := by
  intro av bv
  have hav : av.toNat = 2 * a + 1 := by simp [av, BitVec.toNat_ofNat]
  have hbv : bv.toNat = 2 * b + 1 := by simp [bv, BitVec.toNat_ofNat]
  have hsub : (av - 1#64).toNat = 2 * a := by rw [BitVec.toNat_sub, hav]; simp; omega
  have hadd : (av - 1#64 + bv).toNat = 2 * (a + b) + 1 := by
    rw [BitVec.toNat_add, hsub, hbv, Nat.mod_eq_of_lt (by omega)]; omega
  refine ⟨BitVec.eq_of_toNat_eq (by
    rw [hadd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]), ?_⟩
  simp only [BitVec.lt_def, hadd, hbv]; omega

theorem boxNat_sub_eq {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    let av := BitVec.ofNat 64 (2 * a + 1)
    let bv := BitVec.ofNat 64 (2 * b + 1)
    (if av < bv then 1#64 else av - bv + 1#64) = BitVec.ofNat 64 (2 * (a - b) + 1) := by
  intro av bv
  have hav : av.toNat = 2 * a + 1 := by simp [av, BitVec.toNat_ofNat]
  have hbv : bv.toNat = 2 * b + 1 := by simp [bv, BitVec.toNat_ofNat]
  by_cases hlt : av < bv
  · have hab : a < b := by simp only [BitVec.lt_def, hav, hbv] at hlt; omega
    simp only [hlt, ↓reduceIte, show a - b = 0 from by omega]
  · have hba : b ≤ a := by simp only [BitVec.lt_def, hav, hbv] at hlt; omega
    simp only [hlt, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    have hsub : (av - bv).toNat = 2 * (a - b) := by rw [BitVec.toNat_sub, hav, hbv]; omega
    rw [BitVec.toNat_add, hsub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]

theorem boxNat_pred_sub_eq {av : Nat} (hav1 : 1 ≤ av) (hav63 : av < 2 ^ 63) :
    BitVec.ofNat 64 (2 * av + 1) - 2#64 = BitVec.ofNat 64 (2 * (av - 1) + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by
    simp only [BitVec.le_def, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem boxNat_shiftRight_eq (a b : Nat) (ha : a < 2 ^ 63) :
    (if b < 63 then BitVec.ofNat 64 (2 * a + 1) >>> (b + 1) <<< 1 ||| 1#64 else 1#64) =
      BitVec.ofNat 64 (2 * (a >>> b) + 1) := by
  by_cases hb : b < 63
  · simp only [hb, ↓reduceIte]
    have h1 : (BitVec.ofNat 64 (2 * a + 1) >>> (b + 1)).toNat = a >>> b := by
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      rw [Nat.mod_eq_of_lt (by omega), show (2 * a + 1) / 2 ^ (b + 1) = a / 2 ^ b from by
        rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul]; congr 1; omega]
    rw [bv64_tagged_ofNat64, h1]
  · have hge : 63 ≤ b := by omega
    have hzero : a >>> b = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hge))
    simp only [hb, ↓reduceIte, hzero]

theorem boxNat_land_eq (a b : Nat) :
    BitVec.ofNat 64 (2 * a + 1) &&& BitVec.ofNat 64 (2 * b + 1) =
      BitVec.ofNat 64 (2 * (a &&& b) + 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  cases i with
  | zero =>
    rw [BitVec.getLsbD_and]
    simp only [BitVec.getLsbD_ofNat, show (0 : Nat) < 64 by decide, decide_true,
      boxNat_testBit_zero, Bool.and_self]
  | succ m =>
    rw [BitVec.getLsbD_and]
    simp only [BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and, boxNat_testBit_succ,
      Nat.testBit_and]

theorem boxNat_lor_eq (a b : Nat) :
    BitVec.ofNat 64 (2 * a + 1) ||| BitVec.ofNat 64 (2 * b + 1) =
      BitVec.ofNat 64 (2 * (a ||| b) + 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  cases i with
  | zero =>
    rw [BitVec.getLsbD_or]
    simp only [BitVec.getLsbD_ofNat, show (0 : Nat) < 64 by decide, decide_true, Bool.true_and,
      boxNat_testBit_zero, Bool.or_self]
  | succ m =>
    rw [BitVec.getLsbD_or]
    simp only [BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and, boxNat_testBit_succ,
      Nat.testBit_or]

theorem boxNat_xor_eq (a b : Nat) :
    BitVec.ofNat 64 (2 * a + 1) ^^^ BitVec.ofNat 64 (2 * b + 1) ||| 1#64 =
      BitVec.ofNat 64 (2 * (a ^^^ b) + 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  cases i with
  | zero =>
    rw [BitVec.getLsbD_or, BitVec.getLsbD_xor]
    simp only [BitVec.getLsbD_ofNat, show (0 : Nat) < 64 by decide, decide_true, Bool.true_and,
      boxNat_testBit_zero]
    rfl
  | succ m =>
    rw [BitVec.getLsbD_or, BitVec.getLsbD_xor]
    simp only [BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and, boxNat_testBit_succ,
      Nat.testBit_xor]
    have h1 : Nat.testBit 1 (m + 1) = false := by simp [Nat.testBit_succ]
    rw [h1, Bool.or_false]

theorem byteArray_toList_length (bs : ByteArray) : bs.toList.length = bs.size := by
  have hloop : ∀ (n : Nat) (i : Nat) (acc : List UInt8),
      bs.size - i = n → i ≤ bs.size →
      (ByteArray.toList.loop bs i acc).length = acc.length + n := by
    intro n
    induction n with
    | zero =>
      intro i acc hsub hle
      have heq : i = bs.size := by omega
      rw [ByteArray.toList.loop.eq_1]; simp [heq]
    | succ k ih =>
      intro i acc hsub hle
      have hlt : i < bs.size := by omega
      rw [ByteArray.toList.loop.eq_1]; simp only [hlt, ↓reduceIte]
      have hrec := ih (i + 1) (bs.get! i :: acc) (by omega) (by omega)
      simp only [List.length_cons] at hrec; omega
  simpa [ByteArray.toList] using hloop bs.size 0 [] (by omega) (Nat.zero_le _)

theorem string_toUTF8_toList_length (s : String) :
    s.toUTF8.toList.length = s.utf8ByteSize := by
  rw [String.toUTF8_eq_toByteArray, byteArray_toList_length, String.size_toByteArray]

private def joinDotChars : List String → List Char
  | [] => []
  | [s] => s.toList
  | s :: t :: rs => s.toList ++ ['.'] ++ joinDotChars (t :: rs)

private theorem splitDot_go_nonempty (cs acc : List Char) : splitDot.go cs acc ≠ [] := by
  induction cs generalizing acc with
  | nil => simp [splitDot.go]
  | cons c cs ih =>
    by_cases hc : c = '.'
    · subst hc; simp [splitDot.go]
    · simp only [splitDot.go, beq_false_of_ne hc, Bool.false_eq_true, ↓reduceIte]
      exact ih (c :: acc)

private theorem splitDot_go_join (cs acc : List Char) :
    joinDotChars (splitDot.go cs acc) = acc.reverse ++ cs := by
  induction cs generalizing acc with
  | nil => simp [splitDot.go, joinDotChars]
  | cons c cs ih =>
    by_cases hc : c = '.'
    · subst hc
      simp only [splitDot.go, beq_self_eq_true, ↓reduceIte]
      have hne := splitDot_go_nonempty cs []
      cases h : splitDot.go cs [] with
      | nil => exact absurd h hne
      | cons t rs =>
        have ih' := ih []; rw [h] at ih'
        simp only [joinDotChars, String.toList_ofList, List.append_assoc, List.cons_append,
          List.nil_append] at ih' ⊢
        simp [ih']
    · simp only [splitDot.go, beq_false_of_ne hc, Bool.false_eq_true, ↓reduceIte]
      rw [ih (c :: acc)]; simp

theorem splitDot_inj {s1 s2 : String} (h : splitDot s1 = splitDot s2) : s1 = s2 := by
  have h1 := splitDot_go_join s1.toList []
  have h2 := splitDot_go_join s2.toList []
  simp only [splitDot] at h
  rw [h] at h1
  rw [List.reverse_nil, List.nil_append] at h1 h2
  exact String.ext (h1.symm.trans h2)

theorem HDecN_one_odd {x : BitVec 64} {K : HState → Prop} {σ : HState}
    (hodd : x &&& 1#64 ≠ 0#64) (hk : K σ) :
    HDecN x LcTy.tobject true 1 K σ := by
  change HDec1Pre x LcTy.tobject true σ ∧ ∀ σ', HDec1Rel x LcTy.tobject σ σ' → K σ'
  refine ⟨?_, fun σ' hrel => ?_⟩
  · simp [HDec1Pre, LcTy.needsRc, hodd]
  · simp only [HDec1Rel, LcTy.needsRc, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      eq_true hodd] at hrel
    subst hrel; exact hk

/-! ## 2. Evaluation & `ValRep` Helpers -/

theorem evalArgs_len_one {envP : PValEnv} {envH : HValEnv} {a : LcArg}
    {pvs : List PVal} {ws : List Word}
    (hp : envP.evalArgs [a] = some pvs) (hw : envH.evalArgsOwn [a] = some ws) :
    ∃ pa wa, pvs = [pa] ∧ ws = [wa] ∧ envP.evalArg a = some pa ∧ envH.evalArgOwn a = some wa := by
  cases h1p : envP.evalArg a with
  | none => simp [PValEnv.evalArgs, h1p] at hp
  | some pa =>
    cases h1h : envH.evalArgOwn a with
    | none => simp [HValEnv.evalArgsOwn, h1h] at hw
    | some wa =>
      simp only [PValEnv.evalArgs, h1p, Option.some.injEq] at hp
      simp only [HValEnv.evalArgsOwn, h1h, Option.some.injEq] at hw
      exact ⟨pa, wa, hp.symm, hw.symm, rfl, rfl⟩

theorem evalArgs_len_two {envP : PValEnv} {envH : HValEnv} {a b : LcArg}
    {pvs : List PVal} {ws : List Word}
    (hp : envP.evalArgs [a, b] = some pvs) (hw : envH.evalArgsOwn [a, b] = some ws) :
    ∃ pa pb wa wb, pvs = [pa, pb] ∧ ws = [wa, wb] ∧
      envP.evalArg a = some pa ∧ envP.evalArg b = some pb ∧
      envH.evalArgOwn a = some wa ∧ envH.evalArgOwn b = some wb := by
  cases h1p : envP.evalArg a with | none => simp [PValEnv.evalArgs, h1p] at hp | some pa =>
  cases h2p : envP.evalArg b with | none => simp [PValEnv.evalArgs, h1p, h2p] at hp | some pb =>
  cases h1h : envH.evalArgOwn a with
  | none => simp [HValEnv.evalArgsOwn, h1h] at hw
  | some wa =>
  cases h2h : envH.evalArgOwn b with
  | none => simp [HValEnv.evalArgsOwn, h1h, h2h] at hw
  | some wb =>
  simp only [PValEnv.evalArgs, h1p, h2p, Option.some.injEq] at hp
  simp only [HValEnv.evalArgsOwn, h1h, h2h, Option.some.injEq] at hw
  exact ⟨pa, pb, wa, wb, hp.symm, hw.symm, rfl, rfl, rfl, rfl⟩

theorem evalArgs_len_three {envP : PValEnv} {envH : HValEnv} {a b c : LcArg}
    {pvs : List PVal} {ws : List Word}
    (hp : envP.evalArgs [a, b, c] = some pvs) (hw : envH.evalArgsOwn [a, b, c] = some ws) :
    ∃ pa pb pc wa wb wc, pvs = [pa, pb, pc] ∧ ws = [wa, wb, wc] ∧
      envP.evalArg a = some pa ∧ envP.evalArg b = some pb ∧ envP.evalArg c = some pc ∧
      envH.evalArgOwn a = some wa ∧ envH.evalArgOwn b = some wb ∧ envH.evalArgOwn c = some wc := by
  cases h1p : envP.evalArg a with | none => simp [PValEnv.evalArgs, h1p] at hp | some pa =>
  cases h2p : envP.evalArg b with | none => simp [PValEnv.evalArgs, h1p, h2p] at hp | some pb =>
  cases h3p : envP.evalArg c with
  | none => simp [PValEnv.evalArgs, h1p, h2p, h3p] at hp
  | some pc =>
    cases h1h : envH.evalArgOwn a with | none => simp [HValEnv.evalArgsOwn, h1h] at hw | some wa =>
    cases h2h : envH.evalArgOwn b with
    | none => simp [HValEnv.evalArgsOwn, h1h, h2h] at hw
    | some wb =>
      cases h3h : envH.evalArgOwn c with
      | none => simp [HValEnv.evalArgsOwn, h1h, h2h, h3h] at hw
      | some wc =>
        simp only [PValEnv.evalArgs, h1p, h2p, h3p, Option.some.injEq] at hp
        simp only [HValEnv.evalArgsOwn, h1h, h2h, h3h, Option.some.injEq] at hw
        exact ⟨pa, pb, pc, wa, wb, wc, hp.symm, hw.symm, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem evalArgs_len_four {envP : PValEnv} {envH : HValEnv} {a b c d : LcArg}
    {pvs : List PVal} {ws : List Word}
    (hp : envP.evalArgs [a, b, c, d] = some pvs)
    (hw : envH.evalArgsOwn [a, b, c, d] = some ws) :
    ∃ pa pb pc pd wa wb wc wd, pvs = [pa, pb, pc, pd] ∧ ws = [wa, wb, wc, wd] ∧
      envP.evalArg a = some pa ∧ envP.evalArg b = some pb ∧
      envP.evalArg c = some pc ∧ envP.evalArg d = some pd ∧
      envH.evalArgOwn a = some wa ∧ envH.evalArgOwn b = some wb ∧
      envH.evalArgOwn c = some wc ∧ envH.evalArgOwn d = some wd := by
  cases h1p : envP.evalArg a with | none => simp [PValEnv.evalArgs, h1p] at hp | some pa =>
  cases h2p : envP.evalArg b with | none => simp [PValEnv.evalArgs, h1p, h2p] at hp | some pb =>
  cases h3p : envP.evalArg c with
  | none => simp [PValEnv.evalArgs, h1p, h2p, h3p] at hp
  | some pc =>
    cases h4p : envP.evalArg d with
    | none => simp [PValEnv.evalArgs, h1p, h2p, h3p, h4p] at hp
    | some pd =>
      cases h1h : envH.evalArgOwn a with
      | none => simp [HValEnv.evalArgsOwn, h1h] at hw
      | some wa =>
        cases h2h : envH.evalArgOwn b with
        | none => simp [HValEnv.evalArgsOwn, h1h, h2h] at hw
        | some wb =>
          cases h3h : envH.evalArgOwn c with
          | none => simp [HValEnv.evalArgsOwn, h1h, h2h, h3h] at hw
          | some wc =>
            cases h4h : envH.evalArgOwn d with
            | none => simp [HValEnv.evalArgsOwn, h1h, h2h, h3h, h4h] at hw
            | some wd =>
              simp only [PValEnv.evalArgs, h1p, h2p, h3p, h4p, Option.some.injEq] at hp
              simp only [HValEnv.evalArgsOwn, h1h, h2h, h3h, h4h, Option.some.injEq] at hw
              exact ⟨pa, pb, pc, pd, wa, wb, wc, wd, hp.symm, hw.symm,
                rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem argNonSc_info_of {rf : RcFrame} {σ : HState}
    (hvar : ∀ v ∈ rf.ctx.vars, VarInv v rf σ.objs)
    {a : LcArg} {pv : PVal} {w : Word}
    (ha_ns : (match a with
      | .erased => true
      | .var x => match rf.ctx.get? x with | some v => !v.ty.isScalar | none => false) = true)
    (hlive : a = .erased ∨ ∃ z v, a = .var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true)
    (hep : rf.envP.evalArg a = some pv) (heh : rf.envH.evalArgOwn a = some w) :
    (a = .erased ∧ pv = .erased ∧ w = Word.i64 1#64 ∧ ValRep .tobject pv w σ.objs) ∨
    (∃ z vz, a = .var z ∧ rf.ctx.get? z = some vz ∧ ¬vz.ty.isScalar ∧
      rf.envH z = some (vz.ty, w) ∧ ValRep vz.ty pv w σ.objs) := by
  cases a with
  | erased =>
    simp only [PValEnv.evalArg] at hep; cases hep
    simp only [HValEnv.evalArgOwn] at heh; cases heh
    exact Or.inl ⟨rfl, rfl, rfl, by simp [ValRep, LcTy.isScalar, ObjRep.eq_1]⟩
  | var z =>
    dsimp only at ha_ns
    cases hgz : rf.ctx.get? z with
    | none => simp [hgz] at ha_ns
    | some vz =>
      rw [hgz] at ha_ns
      have hzl : vz.isLive = true := by
        rcases hlive with h | ⟨z', v', hq, hg', hl'⟩
        · cases h
        · cases hq; rw [hgz] at hg'; cases hg'; exact hl'
      obtain ⟨pv', w', hep', heh', hrep', _⟩ := hvar vz (RcCtx.get?_mem hgz).1 hzl
      rw [(RcCtx.get?_mem hgz).2] at hep' heh'
      simp only [PValEnv.evalArg, hep'] at hep; cases hep
      simp only [HValEnv.evalArgOwn, heh'] at heh; cases heh
      have hns : ¬vz.ty.isScalar = true := by simp only [Bool.not_eq_true'] at ha_ns; simp [ha_ns]
      exact Or.inr ⟨z, vz, rfl, hgz, hns, heh', hrep'⟩

theorem argNonSc_rep_of {rf : RcFrame} {σ : HState}
    (hvar : ∀ v ∈ rf.ctx.vars, VarInv v rf σ.objs)
    {a : LcArg} {pv : PVal} {w : Word}
    (ha_ns : (match a with
      | .erased => true
      | .var x => match rf.ctx.get? x with | some v => !v.ty.isScalar | none => false) = true)
    (hlive : a = .erased ∨ ∃ z v, a = .var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true)
    (hep : rf.envP.evalArg a = some pv) (heh : rf.envH.evalArgOwn a = some w) :
    ∃ ty, ¬ty.isScalar ∧ ValRep ty pv w σ.objs := by
  rcases argNonSc_info_of hvar ha_ns hlive hep heh with
    ⟨_, _, _, hrep⟩ | ⟨_, vz, _, _, hns, _, hrep⟩
  · exact ⟨.tobject, by decide, hrep⟩
  · exact ⟨vz.ty, hns, hrep⟩

theorem valRep_nat_small_word {ty : LcTy} {n : Nat} {w : Word} {objs : List LcnfObj}
    (hns : ¬ty.isScalar) (hn : n < 2 ^ 63) (hrep : ValRep ty (PVal.nat n) w objs) :
    w = Word.i64 (BitVec.ofNat 64 (2 * n + 1)) := by
  unfold ValRep at hrep
  simp only [Bool.eq_false_iff.mpr hns, Bool.false_eq_true, ↓reduceIte] at hrep
  rcases hrep with ⟨bv, hw, hobj, _, _⟩
  rw [ObjRep.eq_3, natRepR0_small hn] at hobj
  rw [hw, hobj]

theorem retValRep_small_nat {retTy : LcTy} {n : Nat} {objs : List LcnfObj}
    (ht : (retTy == LcTy.tobject || retTy == LcTy.tagged) = true) (hn : n < 2 ^ 63) :
    let rw := Word.i64 (BitVec.ofNat 64 (2 * n + 1))
    ValRep retTy (PVal.nat n) rw objs ∧
      (¬retTy.isScalar → ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) := by
  intro rw
  have hns : retTy.isScalar = false := by revert ht; cases retTy <;> decide
  have hno : retTy ≠ LcTy.object := by intro h; rw [h] at ht; revert ht; decide
  refine ⟨?_, fun _ => ⟨BitVec.ofNat 64 (2 * n + 1), rfl, boxNat_and1_ne_zero n⟩⟩
  unfold ValRep
  simp only [hns, Bool.false_eq_true, ↓reduceIte]
  refine ⟨BitVec.ofNat 64 (2 * n + 1), rfl, ?_, fun h => absurd h hno,
    fun _ => boxNat_and1_ne_zero n⟩
  rw [ObjRep.eq_3]
  exact natRepR0_of_small hn objs

theorem retValRep_bool {retTy : LcTy} (ht : retTy = LcTy.uint8) (b : Bool)
    (objs : List LcnfObj) :
    let rw := Word.i8 (if b = true then 1#8 else 0#8)
    ValRep retTy (PVal.bool b) rw objs ∧
      (¬retTy.isScalar → ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) := by
  subst ht
  refine ⟨?_, fun h => absurd (by decide : LcTy.uint8.isScalar = true) h⟩
  unfold ValRep
  simp only [LcTy.isScalar, ↓reduceIte, ScalarRep, LcTy.width]
  exact Or.inl ⟨if b = true then 1#8 else 0#8, rfl, rfl⟩

theorem retValRep_bits {retTy : LcTy} {w : Nat} (hw : retTy.isScalar = true ∧ retTy.width = w)
    (bv : BitVec w) (objs : List LcnfObj) :
    let rw : Word := ⟨Ty.bits w, bv⟩
    ValRep retTy (PVal.bits w bv) rw objs ∧
      (¬retTy.isScalar → ∃ bv', rw = Word.i64 bv' ∧ bv' &&& 1#64 ≠ 0#64) := by
  refine ⟨?_, fun h => absurd hw.1 h⟩
  unfold ValRep
  simp only [hw.1, ↓reduceIte, ScalarRep]
  cases retTy with
  | uint8 | uint16 | uint32 | uint64 | usize | float =>
    simp only [LcTy.width] at hw; cases hw.2; exact Or.inl ⟨bv, rfl, rfl⟩
  | object | tobject | tagged | erased | void => exact absurd hw.1 (by decide)

/-! ## 3. `primNatP_sim_fast` -/

private theorem primNatP_bin_nat {op : String} {pa pb pv_res : PVal}
    (hinfo : natBinSlowInfo? op ≠ none) (hp : primNatP op [pa, pb] = some pv_res) :
    ∃ av bv, pa = PVal.nat av ∧ pb = PVal.nat bv := by
  unfold natBinSlowInfo? at hinfo; split at hinfo
  all_goals first
  | exact absurd rfl hinfo
  | (cases pa <;> cases pb <;> first
    | exact ⟨_, _, rfl, rfl⟩
    | (rw [show primNatP _ _ = none from rfl] at hp; cases hp))

theorem primNatP_sim_fast {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hvar : ∀ v ∈ rf.ctx.vars, VarInv v rf σ.objs)
    {name op : String} (hsplit : splitDot name = ["Nat", op])
    {as : List LcArg} {pvs : List PVal} {ws : List Word} {retTy : LcTy}
    (hwf : perceusPrimWf name as.length = true)
    (hretwf : perceusPrimRetWf name retTy = true)
    (hargswf : perceusPrimArgsWf rf.ctx name as = true)
    (hlive : ∀ a ∈ as, a = .erased ∨ ∃ z v, a = .var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true)
    (hpvs : rf.envP.evalArgs as = some pvs) (hws : rf.envH.evalArgsOwn as = some ws)
    (hsafe : primResSafe name pvs) {pv_res : PVal} (hprim : primNatP op pvs = some pv_res)
    {K : HPost} {X : HXPost}
    (hk : ∀ {rw : Word}, ValRep retTy pv_res rw σ.objs →
      (¬retTy.isScalar → ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) → K rw σ) :
    HNatPrimWp rt op ws K X σ := by
  have has_all : as.all (fun a => match a with
      | .erased => true
      | .var x => match rf.ctx.get? x with | some v => !v.ty.isScalar | none => false) = true := by
    have := hargswf; unfold perceusPrimArgsWf at this; rw [hsplit] at this
    rcases as with _ | ⟨a1, _ | ⟨a2, _ | _⟩⟩
    · rfl
    · simp only [uintWidth?] at this; exact this
    · simp only [uintWidth?] at this; exact this
    · exact this
  cases hinfo : natBinSlowInfo? op with
  | none =>
    have hpred : op = "pred" ∧ as.length = 1 := by
      have := hwf; simp only [perceusPrimWf, hsplit, hinfo, Bool.and_eq_true, beq_iff_eq] at this
      exact this
    rcases hpred with ⟨rfl, hlen⟩
    rcases as with _ | ⟨a, _ | _⟩ <;> simp at hlen
    obtain ⟨pa, wa, rfl, rfl, h1p, h1h⟩ := evalArgs_len_one hpvs hws
    cases pa with
    | nat av =>
      simp only [primNatP, Option.some.injEq] at hprim; subst hprim
      simp only [primResSafe, hsplit] at hsafe
      obtain ⟨tya, hnsa, hrepa⟩ := argNonSc_rep_of hvar
        ((List.all_eq_true.mp has_all) a List.mem_cons_self) (hlive a List.mem_cons_self) h1p h1h
      rw [valRep_nat_small_word hnsa hsafe hrepa]
      have hodd : (BitVec.ofNat 64 (2 * av + 1) &&& 1#64 != 0#64) = true := by
        rw [boxNat_and1_eq_one]; decide
      simp only [HNatPrimWp, hinfo, Word.toBV64?, Word.i64, hodd, ↓reduceIte]
      have hres_eq : (if BitVec.ofNat 64 (2 * av + 1) = 1#64 then 1#64
          else BitVec.ofNat 64 (2 * av + 1) - 2#64) = BitVec.ofNat 64 (2 * (av - 1) + 1) := by
        by_cases h0 : av = 0
        · subst h0; simp
        · have hne : BitVec.ofNat 64 (2 * av + 1) ≠ 1#64 := fun heq => by
            have ht := congrArg BitVec.toNat heq
            simp only [BitVec.toNat_ofNat] at ht; omega
          simp only [hne, ↓reduceIte]
          exact boxNat_pred_sub_eq (by omega) hsafe
      rw [hres_eq]
      have hrt : (retTy == LcTy.tobject || retTy == LcTy.tagged) = true := by
        simpa [perceusPrimRetWf, hsplit] using hretwf
      have hrv := retValRep_small_nat hrt (by omega : av - 1 < 2 ^ 63) (objs := σ.objs)
      exact hk hrv.1 hrv.2
    | erased | bits _ _ | str _ | ctor _ _ _ | arr _ | barr _ | int _ | clo _ _ _ =>
      simp [primNatP] at hprim
  | some info =>
    rcases info with ⟨code, resW, isBits⟩
    have hlen : as.length = 2 := by
      have := hwf; simp only [perceusPrimWf, hsplit, hinfo] at this
      rcases as with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> simp at this ⊢
    rcases as with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp at hlen
    obtain ⟨pa, pb, wa, wb, rfl, rfl, h1p, h2p, h1h, h2h⟩ := evalArgs_len_two hpvs hws
    obtain ⟨av, bv, rfl, rfl⟩ := primNatP_bin_nat (by simp [hinfo]) hprim
    obtain ⟨tya, hnsa, hrepa⟩ := argNonSc_rep_of hvar
      ((List.all_eq_true.mp has_all) a List.mem_cons_self)
      (hlive a List.mem_cons_self) h1p h1h
    obtain ⟨tyb, hnsb, hrepb⟩ := argNonSc_rep_of hvar
      ((List.all_eq_true.mp has_all) b (by simp)) (hlive b (by simp)) h2p h2h
    have hop : op = "add" ∨ op = "sub" ∨ op = "mul" ∨ op = "div" ∨ op = "mod" ∨
        op = "decEq" ∨ op = "beq" ∨ op = "decLt" ∨ op = "blt" ∨ op = "decLe" ∨
        op = "ble" ∨ op = "shiftRight" ∨ op = "land" ∨ op = "lor" ∨ op = "xor" ∨
        op = "shiftLeft" := by
      unfold natBinSlowInfo? at hinfo
      split at hinfo <;> simp_all
    have ⟨ha63, hb63⟩ : av < 2 ^ 63 ∧ bv < 2 ^ 63 := by
      rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> (have := hsafe; simp [primResSafe, hsplit] at this; omega)
    rw [valRep_nat_small_word hnsa ha63 hrepa, valRep_nat_small_word hnsb hb63 hrepb]
    simp only [HNatPrimWp, hinfo, Word.toBV64?, Word.i64]
    have hpair := boxNat_pair_and1_ne_zero av bv
    have hxa := boxNat_rshift1_toNat ha63
    have hyb := boxNat_rshift1_toNat hb63
    have hav2 : (BitVec.ofNat 64 (2 * av + 1)).toNat = 2 * av + 1 := by
      simp [BitVec.toNat_ofNat]
    have hbv2 : (BitVec.ofNat 64 (2 * bv + 1)).toNat = 2 * bv + 1 := by
      simp [BitVec.toNat_ofNat]
    have hc_eq : (BitVec.ofNat 64 (2 * av + 1) = BitVec.ofNat 64 (2 * bv + 1)) ↔
        (av = bv) := ⟨fun h => by have := congrArg BitVec.toNat h; rw [hav2, hbv2] at this; omega,
      fun h => by subst h; rfl⟩
    have hc_lt : (BitVec.ofNat 64 (2 * av + 1) < BitVec.ofNat 64 (2 * bv + 1)) ↔
        (av < bv) := by simp only [BitVec.lt_def, hav2, hbv2]; omega
    have hc_le : (BitVec.ofNat 64 (2 * av + 1) ≤ BitVec.ofNat 64 (2 * bv + 1)) ↔
        (av ≤ bv) := by simp only [BitVec.le_def, hav2, hbv2]; omega
    have hrt_nat : ¬(op == "decEq" || op == "beq" || op == "decLt" || op == "blt" ||
        op == "decLe" || op == "ble") = true →
        (retTy == LcTy.tobject || retTy == LcTy.tagged) = true := fun hnot => by
      simpa [perceusPrimRetWf, hsplit, hnot] using hretwf
    have hrt_cmp : (op == "decEq" || op == "beq" || op == "decLt" || op == "blt" ||
        op == "decLe" || op == "ble") = true → retTy = LcTy.uint8 := fun hcmp => by
      have := hretwf
      simp only [perceusPrimRetWf, hsplit, hcmp, ↓reduceIte] at this
      cases retTy <;> first | rfl | exact absurd this (by decide)
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · simp only [primNatP, Option.some.injEq] at hprim; subst hprim
      simp only [primResSafe, hsplit] at hsafe
      obtain ⟨hadd, hnlt⟩ := boxNat_add_eq hsafe
      rw [hadd] at hnlt
      simp only [natBinFast?, hpair, Bool.false_eq_true, ↓reduceIte, hadd,
        Bool.not_eq_true', decide_eq_false_iff_not.mpr hnlt]
      have hrv := retValRep_small_nat (hrt_nat (by decide)) hsafe (objs := σ.objs)
      exact hk hrv.1 hrv.2
    · simp only [primNatP, Option.some.injEq] at hprim; subst hprim
      simp only [natBinFast?, hpair, Bool.false_eq_true, ↓reduceIte, boxNat_sub_eq ha63 hb63]
      have hrv := retValRep_small_nat (hrt_nat (by decide)) (n := av - bv) (by omega)
        (objs := σ.objs)
      exact hk hrv.1 hrv.2
    · simp only [primNatP, Option.some.injEq] at hprim; subst hprim
      simp only [primResSafe, hsplit] at hsafe
      simp only [natBinFast?, hpair, Bool.false_eq_true, ↓reduceIte, hxa, hyb,
        hsafe.2.2, ↓reduceIte]
      have hrv := retValRep_small_nat (hrt_nat (by decide)) hsafe.2.2 (objs := σ.objs)
      exact hk hrv.1 hrv.2
    · simp only [primNatP, Option.some.injEq] at hprim; subst hprim
      simp only [natBinFast?, hpair, Bool.false_eq_true, ↓reduceIte, hxa, hyb]
      have hdiv_eq : (if bv = 0 then 1#64 else BitVec.ofNat 64 (2 * (av / bv) + 1)) =
          BitVec.ofNat 64 (2 * (av / bv) + 1) := by by_cases h0 : bv = 0 <;> simp [h0]
      rw [hdiv_eq]
      have hrv := retValRep_small_nat (hrt_nat (by decide)) (n := av / bv)
        (Nat.lt_of_le_of_lt (Nat.div_le_self av bv) ha63) (objs := σ.objs)
      exact hk hrv.1 hrv.2
    · simp only [primNatP, Option.some.injEq] at hprim; subst hprim
      simp only [natBinFast?, hpair, Bool.false_eq_true, ↓reduceIte, hxa, hyb]
      have hmod_eq : (if bv = 0 then BitVec.ofNat 64 (2 * av + 1)
          else BitVec.ofNat 64 (2 * (av % bv) + 1)) =
          BitVec.ofNat 64 (2 * (av % bv) + 1) := by by_cases h0 : bv = 0 <;> simp [h0]
      rw [hmod_eq]
      have hrv := retValRep_small_nat (hrt_nat (by decide)) (n := av % bv)
        (Nat.lt_of_le_of_lt (Nat.mod_le av bv) ha63) (objs := σ.objs)
      exact hk hrv.1 hrv.2
    · simp only [primNatP, Option.some.injEq] at hprim; subst hprim
      simp only [natBinFast?, hpair, Bool.false_eq_true, ↓reduceIte, hc_eq]
      have hrv := retValRep_bool (hrt_cmp (by decide)) (av == bv) σ.objs
      simpa using hk hrv.1 hrv.2
    · simp only [primNatP, Option.some.injEq] at hprim; subst hprim
      simp only [natBinFast?, hpair, Bool.false_eq_true, ↓reduceIte, hc_eq]
      have hrv := retValRep_bool (hrt_cmp (by decide)) (av == bv) σ.objs
      simpa using hk hrv.1 hrv.2
    · simp only [primNatP, Option.some.injEq] at hprim; subst hprim
      simp only [natBinFast?, hpair, Bool.false_eq_true, ↓reduceIte, hc_lt]
      have hrv := retValRep_bool (hrt_cmp (by decide)) (decide (av < bv)) σ.objs
      simpa using hk hrv.1 hrv.2
    · simp only [primNatP, Option.some.injEq] at hprim; subst hprim
      simp only [natBinFast?, hpair, Bool.false_eq_true, ↓reduceIte, hc_lt]
      have hrv := retValRep_bool (hrt_cmp (by decide)) (decide (av < bv)) σ.objs
      simpa using hk hrv.1 hrv.2
    · simp only [primNatP, Option.some.injEq] at hprim; subst hprim
      simp only [natBinFast?, hpair, Bool.false_eq_true, ↓reduceIte, hc_le]
      have hrv := retValRep_bool (hrt_cmp (by decide)) (decide (av ≤ bv)) σ.objs
      simpa using hk hrv.1 hrv.2
    · simp only [primNatP, Option.some.injEq] at hprim; subst hprim
      simp only [natBinFast?, hpair, Bool.false_eq_true, ↓reduceIte, hc_le]
      have hrv := retValRep_bool (hrt_cmp (by decide)) (decide (av ≤ bv)) σ.objs
      simpa using hk hrv.1 hrv.2
    · simp only [primNatP, Option.some.injEq] at hprim; subst hprim
      simp only [natBinFast?, hpair, Bool.false_eq_true, ↓reduceIte, hyb,
        boxNat_shiftRight_eq av bv ha63]
      have hsr : av >>> bv < 2 ^ 63 := by
        rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha63
      have hrv := retValRep_small_nat (hrt_nat (by decide)) hsr (objs := σ.objs)
      exact hk hrv.1 hrv.2
    · simp only [primNatP, Option.some.injEq] at hprim; subst hprim
      simp only [natBinFast?, hpair, Bool.false_eq_true, ↓reduceIte]
      rw [boxNat_land_eq]
      have hrv := retValRep_small_nat (hrt_nat (by decide)) (n := av &&& bv)
        (Nat.lt_of_le_of_lt (Nat.and_le_left (n := av) (m := bv)) ha63) (objs := σ.objs)
      exact hk hrv.1 hrv.2
    · simp only [primNatP, Option.some.injEq] at hprim; subst hprim
      simp only [natBinFast?, hpair, Bool.false_eq_true, ↓reduceIte, boxNat_lor_eq]
      have hrv := retValRep_small_nat (hrt_nat (by decide))
        (Nat.or_lt_two_pow ha63 hb63) (objs := σ.objs)
      exact hk hrv.1 hrv.2
    · simp only [primNatP, Option.some.injEq] at hprim; subst hprim
      simp only [natBinFast?, hpair, Bool.false_eq_true, ↓reduceIte, boxNat_xor_eq]
      have hrv := retValRep_small_nat (hrt_nat (by decide))
        (Nat.xor_lt_two_pow ha63 hb63) (objs := σ.objs)
      exact hk hrv.1 hrv.2
    · simp only [primNatP, Option.some.injEq] at hprim; subst hprim
      simp only [primResSafe, hsplit] at hsafe
      simp only [natBinFast?, hpair, Bool.false_eq_true, ↓reduceIte, hxa, hyb,
        hsafe.2.1, hsafe.2.2, decide_true, Bool.and_self]
      have hrv := retValRep_small_nat (hrt_nat (by decide)) hsafe.2.2 (objs := σ.objs)
      exact hk hrv.1 hrv.2

/-! ## 4. `primUintP_sim` -/

private theorem scalar_toBits_eq {ty : LcTy} {w : Nat} {pv : PVal} {wa : Word}
    {objs : List LcnfObj} (hs : ty.isScalar = true ∧ ty.width = w)
    (hrep : ValRep ty pv wa objs) {bv : BitVec w} (hp : PVal.toBits? w pv = some bv) :
    wa = ⟨Ty.bits w, bv⟩ := by
  unfold ValRep at hrep
  simp only [hs.1, ↓reduceIte, ScalarRep, hs.2] at hrep
  cases pv with
  | bits m v =>
    simp only [PVal.toBits?] at hp
    split at hp
    · rename_i hmw; subst hmw; simp only [Option.some.injEq] at hp; subst hp
      rcases hrep with ⟨bv', heq, hw⟩ | ⟨_, hc, _⟩ | ⟨he, _⟩
      · cases heq; exact hw
      · cases hc
      · cases he
    · cases hp
  | erased | nat _ | str _ | ctor _ _ _ | arr _ | barr _ | int _ | clo _ _ _ =>
    simp [PVal.toBits?] at hp

theorem uintWidth?_le64 {ty : String} {w : Nat} (hw : uintWidth? ty = some w) : w ≤ 64 := by
  unfold uintWidth? at hw; split at hw <;> cases hw <;> omega

private def argIsScalarW (ctx : RcCtx) (w : Nat) : LcArg → Bool
  | .erased => false
  | .var x => match ctx.get? x with | some v => v.ty.isScalar && v.ty.width == w | none => false

private theorem argSc_toBits_word {rf : RcFrame} {σ : HState} {w : Nat}
    (hvar : ∀ v ∈ rf.ctx.vars, VarInv v rf σ.objs)
    {a : LcArg} {pv : PVal} {wa : Word} {bv : BitVec w}
    (ha : argIsScalarW rf.ctx w a = true)
    (hlive : a = .erased ∨ ∃ z v, a = .var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true)
    (hep : rf.envP.evalArg a = some pv) (heh : rf.envH.evalArgOwn a = some wa)
    (hp : PVal.toBits? w pv = some bv) :
    wa = ⟨Ty.bits w, bv⟩ := by
  cases a with
  | erased => simp [argIsScalarW] at ha
  | var z =>
    dsimp only [argIsScalarW] at ha
    cases hgz : rf.ctx.get? z with
    | none => simp [hgz] at ha
    | some vz =>
      rw [hgz] at ha; simp only [Bool.and_eq_true, beq_iff_eq] at ha
      have hzl : vz.isLive = true := by
        rcases hlive with h | ⟨z', v', hq, hg', hl'⟩
        · cases h
        · cases hq; rw [hgz] at hg'; cases hg'; exact hl'
      obtain ⟨pv', w', hep', heh', hrep', _⟩ := hvar vz (RcCtx.get?_mem hgz).1 hzl
      rw [(RcCtx.get?_mem hgz).2] at hep' heh'
      simp only [PValEnv.evalArg, hep'] at hep; cases hep
      simp only [HValEnv.evalArgOwn, heh'] at heh; cases heh
      exact scalar_toBits_eq ha hrep' hp

private def argIsNonSc (ctx : RcCtx) : LcArg → Bool
  | .erased => true
  | .var x => match ctx.get? x with | some v => !v.ty.isScalar | none => false

private theorem uintOfNat_core {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hvar : ∀ v ∈ rf.ctx.vars, VarInv v rf σ.objs)
    {w n : Nat} {a : LcArg} {wa : Word} {retTy : LcTy} (decAfter : Bool)
    (ha_ns : argIsNonSc rf.ctx a = true)
    (hlive : a = .erased ∨ ∃ z v, a = .var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true)
    (h1p : rf.envP.evalArg a = some (.nat n)) (h1h : rf.envH.evalArgOwn a = some wa)
    (hn : n < 2 ^ 63) (hrt_sc : retTy.isScalar = true ∧ retTy.width = w)
    {K : HPost}
    (hk : ∀ {rw : Word}, ValRep retTy (.bits w (BitVec.ofNat w n)) rw σ.objs →
      (¬retTy.isScalar → ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) → K rw σ) :
    HUintOfNatWp rt w wa decAfter K σ := by
  have ⟨tya, hnsa, hrepa⟩ : ∃ ty, ¬ty.isScalar ∧ ValRep ty (.nat n) wa σ.objs := by
    cases a with
    | erased => exact argNonSc_rep_of hvar (a := .erased) rfl hlive h1p h1h
    | var z => exact argNonSc_rep_of hvar (a := .var z) ha_ns hlive h1p h1h
  rw [valRep_nat_small_word hnsa hn hrepa]
  have hset : BitVec.setWidth w (BitVec.ofNat 64 (2 * n + 1) >>> 1) = BitVec.ofNat w n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, boxNat_rshift1_toNat hn, BitVec.toNat_ofNat]
  have hodd : (BitVec.ofNat 64 (2 * n + 1) &&& 1#64 != 0#64) = true := by
    rw [boxNat_and1_eq_one]; decide
  have hrv := retValRep_bits hrt_sc (BitVec.ofNat w n) σ.objs
  have hcall : K ⟨Ty.bits w, BitVec.ofNat w n⟩ σ := hk hrv.1 hrv.2
  simp only [HUintOfNatWp, Word.toBV64?, Word.i64, hodd, ↓reduceIte, hset]
  cases decAfter with
  | false => exact hcall
  | true => exact HDecN_one_odd (boxNat_and1_ne_zero n) hcall

theorem lcTy_beq_iff (a b : LcTy) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

private theorem uintWidth?_cases {ty : String} {w : Nat} (hw : uintWidth? ty = some w) :
    (ty = "UInt8" ∧ w = 8) ∨ (ty = "UInt16" ∧ w = 16) ∨
    (ty = "UInt32" ∧ w = 32) ∨ (ty = "UInt64" ∧ w = 64) ∨
    (ty = "USize" ∧ w = 64) := by
  unfold uintWidth? at hw; split at hw <;> first | (cases hw; simp) | cases hw

private theorem uintWidth?_ne {ty : String} {w : Nat} (hw : uintWidth? ty = some w) :
    ty ≠ "Nat" ∧ ty ≠ "Array" ∧ ty ≠ "ByteArray" ∧ ty ≠ "String" ∧
    ty ≠ "System" ∧ ty ≠ "getObjTagNat" ∧ ty ≠ "outOfBounds" := by
  unfold uintWidth? at hw; split at hw <;> simp_all

private def uintWfMatch (op : String) (n : Nat) : Bool :=
  match op, n with
  | "add", 2 | "sub", 2 | "mul", 2 | "land", 2 | "lor", 2 | "xor", 2
  | "shiftLeft", 2 | "shiftRight", 2 | "div", 2 | "mod", 2 | "complement", 1
  | "neg", 1 | "decEq", 2 | "beq", 2 | "decLt", 2 | "blt", 2 | "decLe", 2
  | "ble", 2 | "toUInt8", 1 | "toUInt16", 1 | "toUInt32", 1 | "toUInt64", 1
  | "toUSize", 1 | "ofNat", 1 | "ofNatLT", 1 | "ofNatLT", 2 | "ofBitVec", 1
  | "toNat", 1 | "toBitVec", 1 => true | _, _ => false

private theorem primWf_uint_cases {name ty op : String} {w n : Nat}
    (hsplit : splitDot name = [ty, op]) (hw : uintWidth? ty = some w)
    (hwf : perceusPrimWf name n = true) :
    ((op = "ofNat" ∧ n = 1) ∨ (op = "ofNatLT" ∧ (n = 1 ∨ n = 2)) ∨ (op = "ofBitVec" ∧ n = 1)) ∨
    ((op = "toNat" ∨ op = "toBitVec") ∧ n = 1) ∨
    ((op = "complement" ∨ op = "neg" ∨ op = "toUInt8" ∨ op = "toUInt16" ∨
      op = "toUInt32" ∨ op = "toUInt64" ∨ op = "toUSize") ∧ n = 1) ∨
    ((op = "add" ∨ op = "sub" ∨ op = "mul" ∨ op = "land" ∨ op = "lor" ∨
      op = "xor" ∨ op = "shiftLeft" ∨ op = "shiftRight" ∨ op = "div" ∨ op = "mod" ∨
      op = "decEq" ∨ op = "beq" ∨ op = "decLt" ∨ op = "blt" ∨
      op = "decLe" ∨ op = "ble") ∧ n = 2) := by
  have h := hwf; unfold perceusPrimWf at h; rw [hsplit] at h
  rcases uintWidth?_cases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    change uintWfMatch op n = true at h
    unfold uintWfMatch at h; split at h <;> simp at h ⊢

private theorem primArgsWf_uint1 {ctx : RcCtx} {name ty op : String} {w : Nat} {a : LcArg}
    (hsplit : splitDot name = [ty, op]) (hw : uintWidth? ty = some w)
    (hargswf : perceusPrimArgsWf ctx name [a] = true) :
    if (op == "ofNat" || op == "ofNatLT" || op == "ofBitVec") = true then argIsNonSc ctx a = true
    else argIsScalarW ctx w a = true := by
  have := hargswf; unfold perceusPrimArgsWf at this; rw [hsplit] at this
  dsimp only at this; rw [hw] at this; dsimp only at this
  by_cases hop : (op == "ofNat" || op == "ofNatLT" || op == "ofBitVec") = true
  · simp only [hop, ↓reduceIte] at this ⊢; exact this
  · simp only [hop, Bool.false_eq_true, ↓reduceIte] at this ⊢; exact this

private theorem primArgsWf_uint2 {ctx : RcCtx} {name ty op : String} {w : Nat} {a b : LcArg}
    (hsplit : splitDot name = [ty, op]) (hw : uintWidth? ty = some w)
    (hargswf : perceusPrimArgsWf ctx name [a, b] = true) :
    if (op == "ofNatLT") = true then argIsNonSc ctx a = true
    else argIsScalarW ctx w a = true ∧ argIsScalarW ctx w b = true := by
  have := hargswf; unfold perceusPrimArgsWf at this; rw [hsplit] at this
  dsimp only at this; rw [hw] at this
  by_cases hop : (op == "ofNatLT") = true
  · simp only [hop, ↓reduceIte] at this ⊢; exact this
  · simp only [hop, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at this ⊢; exact this

private theorem primResSafe_uint_nat {name ty op : String} {w : Nat} {pvs : List PVal} {n : Nat}
    (hsplit : splitDot name = [ty, op]) (hw : uintWidth? ty = some w)
    (hp : pvs = [PVal.nat n] ∨ ∃ pb, op = "ofNatLT" ∧ pvs = [PVal.nat n, pb])
    (hsafe : primResSafe name pvs) : n < 2 ^ 63 := by
  have hne := uintWidth?_ne hw
  rcases hp with rfl | ⟨pb, rfl, rfl⟩
  · have := hsafe; unfold primResSafe at this; rw [hsplit] at this
    simp [hne.1, hw] at this
    exact this.2
  · have := hsafe; unfold primResSafe at this; rw [hsplit] at this
    simp [hne.1, hw] at this
    exact this

private theorem primResSafe_uint_to {name ty op : String} {w m : Nat} {bv : BitVec m}
    (hsplit : splitDot name = [ty, op]) (hw : uintWidth? ty = some w)
    (hop : op = "toNat" ∨ op = "toBitVec")
    (hsafe : primResSafe name [PVal.bits m bv]) : m < 64 ∨ bv.toNat < 2 ^ 63 := by
  have := hsafe; unfold primResSafe at this
  rcases hop with rfl | rfl <;>
    (rw [hsplit] at this; simp [hw] at this; exact this)

private theorem primRetWf_uint_eq {name ty op : String} {w : Nat} {retTy : LcTy}
    (hsplit : splitDot name = [ty, op]) (hw : uintWidth? ty = some w)
    (hretwf : perceusPrimRetWf name retTy = true) :
    (if (op == "decEq" || op == "beq" || op == "decLt" || op == "blt" ||
        op == "decLe" || op == "ble") = true then retTy = LcTy.uint8
     else if (op == "toNat" || op == "toBitVec") = true then
       (retTy == LcTy.tobject || retTy == LcTy.tagged) = true
     else if (op == "toUInt8") = true then retTy = LcTy.uint8
     else if (op == "toUInt16") = true then retTy = LcTy.uint16
     else if (op == "toUInt32") = true then retTy = LcTy.uint32
     else if (op == "toUInt64") = true then retTy = LcTy.uint64
     else if (op == "toUSize") = true then retTy = LcTy.usize
     else retTy.isScalar = true ∧ retTy.width = w) := by
  have h := hretwf; unfold perceusPrimRetWf at h; rw [hsplit] at h
  rcases uintWidth?_cases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    change (if (op == "decEq" || op == "beq" || op == "decLt" || op == "blt" ||
        op == "decLe" || op == "ble") = true then retTy == LcTy.uint8
      else if (op == "toNat" || op == "toBitVec") = true then
        retTy == LcTy.tobject || retTy == LcTy.tagged
      else if (op == "toUInt8") = true then retTy == LcTy.uint8
      else if (op == "toUInt16") = true then retTy == LcTy.uint16
      else if (op == "toUInt32") = true then retTy == LcTy.uint32
      else if (op == "toUInt64") = true then retTy == LcTy.uint64
      else if (op == "toUSize") = true then retTy == LcTy.usize
      else retTy.isScalar && retTy.width == _) = true at h
    split at h
    · simp only [*, ↓reduceIte, lcTy_beq_iff] at h ⊢; exact h
    · split at h
      · simp only [*, Bool.false_eq_true, ↓reduceIte] at h ⊢
      · split at h
        · simp only [*, Bool.false_eq_true, ↓reduceIte, lcTy_beq_iff] at h ⊢; exact h
        · split at h
          · simp only [*, Bool.false_eq_true, ↓reduceIte, lcTy_beq_iff] at h ⊢; exact h
          · split at h
            · simp only [*, Bool.false_eq_true, ↓reduceIte, lcTy_beq_iff] at h ⊢; exact h
            · split at h
              · simp only [*, Bool.false_eq_true, ↓reduceIte, lcTy_beq_iff] at h ⊢; exact h
              · split at h
                · simp only [*, Bool.false_eq_true, ↓reduceIte, lcTy_beq_iff] at h ⊢; exact h
                · simp only [*, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h ⊢
                  exact h

private theorem primUintP_bin_extract {w : Nat} {op : String} {pa pb pv_res : PVal}
    (hop : op = "add" ∨ op = "sub" ∨ op = "mul" ∨ op = "land" ∨ op = "lor" ∨
      op = "xor" ∨ op = "shiftLeft" ∨ op = "shiftRight" ∨ op = "div" ∨ op = "mod" ∨
      op = "decEq" ∨ op = "beq" ∨ op = "decLt" ∨ op = "blt" ∨ op = "decLe" ∨ op = "ble")
    (hp : primUintP w op [pa, pb] = some pv_res) :
    ∃ (bva bvb : BitVec w), pa = PVal.bits w bva ∧ pb = PVal.bits w bvb := by
  cases pa with
  | bits ma bva =>
    cases pb with
    | bits mb bvb =>
      by_cases h1 : ma = w <;> by_cases h2 : mb = w
      · subst h1; subst h2; exact ⟨bva, bvb, rfl, rfl⟩
      · rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl <;> simp [primUintP, PVal.toBits?, h1, h2] at hp
      · rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl <;> simp [primUintP, PVal.toBits?, h1, h2] at hp
      · rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl <;> simp [primUintP, PVal.toBits?, h1, h2] at hp
    | erased | nat _ | str _ | ctor _ _ _ | arr _ | barr _ | int _ | clo _ _ _ =>
      rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> simp [primUintP, PVal.toBits?] at hp
  | erased | nat _ | str _ | ctor _ _ _ | arr _ | barr _ | int _ | clo _ _ _ =>
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> simp [primUintP, PVal.toBits?] at hp

private theorem primUintP_bin_step {rt : BitVec 64} {w : Nat} {op : String} {retTy : LcTy}
    {bva bvb : BitVec w} {pv_res : PVal}
    (hop : op = "add" ∨ op = "sub" ∨ op = "mul" ∨ op = "land" ∨ op = "lor" ∨
      op = "xor" ∨ op = "shiftLeft" ∨ op = "shiftRight" ∨ op = "div" ∨ op = "mod" ∨
      op = "decEq" ∨ op = "beq" ∨ op = "decLt" ∨ op = "blt" ∨ op = "decLe" ∨ op = "ble")
    (hret : if (op == "decEq" || op == "beq" || op == "decLt" || op == "blt" ||
        op == "decLe" || op == "ble") = true then retTy = LcTy.uint8
      else retTy.isScalar = true ∧ retTy.width = w)
    (hp : primUintP w op [PVal.bits w bva, PVal.bits w bvb] = some pv_res)
    {K : HPost} {σ : HState}
    (hk : ∀ {rw : Word}, ValRep retTy pv_res rw σ.objs →
      (¬retTy.isScalar → ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) → K rw σ) :
    HUintPrimWp rt w op [⟨Ty.bits w, bva⟩, ⟨Ty.bits w, bvb⟩] K σ := by
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (
    simp only [primUintP, PVal.toBits?, ↓reduceDIte, Option.some.injEq] at hp
    subst hp
    simp only [HUintPrimWp, uintPure?, Word.toBits?, ↓reduceDIte])
  · exact hk (retValRep_bits hret (bva + bvb) σ.objs).1 (retValRep_bits hret (bva + bvb) σ.objs).2
  · exact hk (retValRep_bits hret (bva - bvb) σ.objs).1 (retValRep_bits hret (bva - bvb) σ.objs).2
  · exact hk (retValRep_bits hret (bva * bvb) σ.objs).1 (retValRep_bits hret (bva * bvb) σ.objs).2
  · have h := retValRep_bits hret (bva &&& bvb) σ.objs; exact hk h.1 h.2
  · have h := retValRep_bits hret (bva ||| bvb) σ.objs; exact hk h.1 h.2
  · have h := retValRep_bits hret (bva ^^^ bvb) σ.objs; exact hk h.1 h.2
  · exact hk (retValRep_bits hret _ σ.objs).1 (retValRep_bits hret _ σ.objs).2
  · exact hk (retValRep_bits hret _ σ.objs).1 (retValRep_bits hret _ σ.objs).2
  · exact hk (retValRep_bits hret _ σ.objs).1 (retValRep_bits hret _ σ.objs).2
  · exact hk (retValRep_bits hret _ σ.objs).1 (retValRep_bits hret _ σ.objs).2
  · exact hk (retValRep_bool hret _ σ.objs).1 (retValRep_bool hret _ σ.objs).2
  · exact hk (retValRep_bool hret _ σ.objs).1 (retValRep_bool hret _ σ.objs).2
  · exact hk (retValRep_bool hret _ σ.objs).1 (retValRep_bool hret _ σ.objs).2
  · exact hk (retValRep_bool hret _ σ.objs).1 (retValRep_bool hret _ σ.objs).2
  · exact hk (retValRep_bool hret _ σ.objs).1 (retValRep_bool hret _ σ.objs).2
  · exact hk (retValRep_bool hret _ σ.objs).1 (retValRep_bool hret _ σ.objs).2

theorem primUintP_sim {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hvar : ∀ v ∈ rf.ctx.vars, VarInv v rf σ.objs)
    {name ty op : String} {w : Nat} (hsplit : splitDot name = [ty, op])
    (hw : uintWidth? ty = some w)
    {as : List LcArg} {pvs : List PVal} {ws : List Word} {retTy : LcTy}
    (hwf : perceusPrimWf name as.length = true)
    (hretwf : perceusPrimRetWf name retTy = true)
    (hargswf : perceusPrimArgsWf rf.ctx name as = true)
    (hlive : ∀ a ∈ as, a = .erased ∨ ∃ z v, a = .var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true)
    (hpvs : rf.envP.evalArgs as = some pvs) (hws : rf.envH.evalArgsOwn as = some ws)
    (hsafe : primResSafe name pvs) {pv_res : PVal} (hprim : primUintP w op pvs = some pv_res)
    {K : HPost}
    (hk : ∀ {rw : Word}, ValRep retTy pv_res rw σ.objs →
      (¬retTy.isScalar → ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) → K rw σ) :
    HUintPrimWp rt w op ws K σ := by
  have hwf_u := primWf_uint_cases hsplit hw hwf
  have hret_u := primRetWf_uint_eq hsplit hw hretwf
  rcases hwf_u with h_ofn | h_to | h_un | h_bin
  · rcases h_ofn with ⟨rfl, hlen⟩ | ⟨rfl, hlen12⟩ | ⟨rfl, hlen⟩
    · have hrt_sc : retTy.isScalar = true ∧ retTy.width = w := hret_u
      rcases as with _ | ⟨a, _ | _⟩ <;> simp at hlen
      obtain ⟨pa, wa, rfl, rfl, h1p, h1h⟩ := evalArgs_len_one hpvs hws
      cases pa with
      | nat n =>
        simp only [primUintP, Option.some.injEq] at hprim; subst hprim
        have hn63 : n < 2 ^ 63 := primResSafe_uint_nat hsplit hw (Or.inl rfl) hsafe
        have ha_ns := primArgsWf_uint1 hsplit hw hargswf
        simp only [beq_self_eq_true, Bool.true_or, ↓reduceIte] at ha_ns
        exact uintOfNat_core hvar false ha_ns (hlive a List.mem_cons_self) h1p h1h hn63 hrt_sc hk
      | erased | bits _ _ | str _ | ctor _ _ _ | arr _ | barr _ | int _ | clo _ _ _ =>
        simp [primUintP] at hprim
    · have hrt_sc : retTy.isScalar = true ∧ retTy.width = w := hret_u
      rcases hlen12 with hlen | hlen
      · rcases as with _ | ⟨a, _ | _⟩ <;> simp at hlen
        obtain ⟨pa, wa, rfl, rfl, h1p, h1h⟩ := evalArgs_len_one hpvs hws
        cases pa with
        | nat n =>
          simp only [primUintP, Option.some.injEq] at hprim; subst hprim
          have hn63 : n < 2 ^ 63 := primResSafe_uint_nat hsplit hw (Or.inl rfl) hsafe
          have ha_ns := primArgsWf_uint1 hsplit hw hargswf
          simp only [beq_self_eq_true, Bool.true_or, Bool.or_true, ↓reduceIte] at ha_ns
          exact uintOfNat_core hvar false ha_ns (hlive a List.mem_cons_self) h1p h1h hn63 hrt_sc hk
        | erased | bits _ _ | str _ | ctor _ _ _ | arr _ | barr _ | int _ | clo _ _ _ =>
          simp [primUintP] at hprim
      · rcases as with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp at hlen
        obtain ⟨pa, pb, wa, wb, rfl, rfl, h1p, _, h1h, _⟩ := evalArgs_len_two hpvs hws
        cases pa with
        | nat n =>
          simp only [primUintP, Option.some.injEq] at hprim; subst hprim
          have hn63 : n < 2 ^ 63 := primResSafe_uint_nat hsplit hw (Or.inr ⟨pb, rfl, rfl⟩) hsafe
          have ha_ns := primArgsWf_uint2 hsplit hw hargswf
          simp only [beq_self_eq_true, ↓reduceIte] at ha_ns
          exact uintOfNat_core hvar false ha_ns (hlive a List.mem_cons_self) h1p h1h hn63 hrt_sc hk
        | erased | bits _ _ | str _ | ctor _ _ _ | arr _ | barr _ | int _ | clo _ _ _ =>
          simp [primUintP] at hprim
    · have hrt_sc : retTy.isScalar = true ∧ retTy.width = w := hret_u
      rcases as with _ | ⟨a, _ | _⟩ <;> simp at hlen
      obtain ⟨pa, wa, rfl, rfl, h1p, h1h⟩ := evalArgs_len_one hpvs hws
      cases pa with
      | nat n =>
        simp only [primUintP, Option.some.injEq] at hprim; subst hprim
        have hn63 : n < 2 ^ 63 := primResSafe_uint_nat hsplit hw (Or.inl rfl) hsafe
        have ha_ns := primArgsWf_uint1 hsplit hw hargswf
        simp only [beq_self_eq_true, Bool.or_true, ↓reduceIte] at ha_ns
        exact uintOfNat_core hvar true ha_ns (hlive a List.mem_cons_self) h1p h1h hn63 hrt_sc hk
      | erased | bits _ _ | str _ | ctor _ _ _ | arr _ | barr _ | int _ | clo _ _ _ =>
        simp [primUintP] at hprim
  · rcases h_to with ⟨h_to, hlen⟩
    rcases as with _ | ⟨a, _ | _⟩ <;> simp at hlen
    obtain ⟨pa, wa, rfl, rfl, h1p, h1h⟩ := evalArgs_len_one hpvs hws
    cases pa with
    | bits m bv =>
      have hmw : m = w := by
        by_cases hm : m = w
        · exact hm
        · exfalso; revert hprim
          rcases h_to with rfl | rfl <;> simp [primUintP, PVal.toBits?, hm]
      subst hmw
      have ha_sc : argIsScalarW rf.ctx m a = true := by
        have := primArgsWf_uint1 hsplit hw hargswf
        rcases h_to with rfl | rfl <;> exact this
      rw [argSc_toBits_word hvar ha_sc (hlive a List.mem_cons_self) h1p h1h
        (bv := bv) (by simp [PVal.toBits?])]
      have hsafe_nat : m < 64 ∨ bv.toNat < 2 ^ 63 := primResSafe_uint_to hsplit hw h_to hsafe
      have hlt63 : bv.toNat < 2 ^ 63 := by
        rcases hsafe_nat with hm64 | hlt
        · have hm32 : m ≤ 32 := by unfold uintWidth? at hw; split at hw <;> cases hw <;> omega
          exact Nat.lt_of_lt_of_le bv.isLt
            (Nat.le_trans (Nat.pow_le_pow_right (by omega) hm32) (by decide))
        · exact hlt
      have hfast : (decide (m < 64) || (BitVec.setWidth 64 bv) >>> 63 == 0#64) = true := by
        have hsw : (BitVec.setWidth 64 bv).toNat = bv.toNat := by
          have := uintWidth?_le64 hw
          simp [BitVec.toNat_setWidth]
        have hrs : (BitVec.setWidth 64 bv) >>> 63 = 0#64 := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_ushiftRight, hsw, Nat.shiftRight_eq_div_pow]
          exact Nat.div_eq_of_lt hlt63
        simp [hrs]
      have htagged : BitVec.setWidth 64 bv <<< 1 ||| 1#64 = BitVec.ofNat 64 (2 * bv.toNat + 1) := by
        rw [bv64_tagged_ofNat64]
        have := uintWidth?_le64 hw
        simp [BitVec.toNat_setWidth]
      have hrt : (retTy == LcTy.tobject || retTy == LcTy.tagged) = true := by
        rcases h_to with rfl | rfl <;> exact hret_u
      have hpv_eq : pv_res = PVal.nat bv.toNat := by
        revert hprim; rcases h_to with rfl | rfl <;>
          simp [primUintP, PVal.toBits?] <;> intro h <;> exact h.symm
      rw [hpv_eq] at hk
      have hrv := retValRep_small_nat hrt hlt63 (objs := σ.objs)
      rcases h_to with rfl | rfl <;>
        simp only [HUintPrimWp, uintPure?, Word.toBits?, ↓reduceDIte,
          hfast, ↓reduceIte, htagged] <;>
        exact hk hrv.1 hrv.2
    | erased | nat _ | str _ | ctor _ _ _ | arr _ | barr _ | int _ | clo _ _ _ =>
      revert hprim; rcases h_to with rfl | rfl <;> simp [primUintP, PVal.toBits?]
  · rcases h_un with ⟨h_un, hlen⟩
    rcases as with _ | ⟨a, _ | _⟩ <;> simp at hlen
    obtain ⟨pa, wa, rfl, rfl, h1p, h1h⟩ := evalArgs_len_one hpvs hws
    cases pa with
    | bits m bv =>
      have hmw : m = w := by
        by_cases hm : m = w
        · exact hm
        · exfalso; revert hprim
          rcases h_un with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [primUintP, PVal.toBits?, hm]
      subst hmw
      have ha_sc : argIsScalarW rf.ctx m a = true := by
        have := primArgsWf_uint1 hsplit hw hargswf
        rcases h_un with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact this
      rw [argSc_toBits_word hvar ha_sc (hlive a List.mem_cons_self) h1p h1h
        (bv := bv) (by simp [PVal.toBits?])]
      rcases h_un with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [primUintP, PVal.toBits?, ↓reduceDIte, Option.map_some,
          Option.some.injEq] at hprim; subst hprim
        have hrt_sc : retTy.isScalar = true ∧ retTy.width = m := by simpa using hret_u
        simp only [HUintPrimWp, uintPure?, Word.toBits?, ↓reduceDIte, Option.map_some]
        have hrv := retValRep_bits hrt_sc (~~~bv) σ.objs; exact hk hrv.1 hrv.2
      · simp only [primUintP, PVal.toBits?, ↓reduceDIte, Option.map_some,
          Option.some.injEq] at hprim; subst hprim
        have hrt_sc : retTy.isScalar = true ∧ retTy.width = m := by simpa using hret_u
        simp only [HUintPrimWp, uintPure?, Word.toBits?, ↓reduceDIte, Option.map_some]
        have hrv := retValRep_bits hrt_sc (-bv) σ.objs; exact hk hrv.1 hrv.2
      · simp only [primUintP, PVal.toBits?, ↓reduceDIte, Option.map_some,
          Option.some.injEq] at hprim; subst hprim
        have hrt : retTy = LcTy.uint8 := by simpa using hret_u
        subst hrt
        simp only [HUintPrimWp, uintPure?, Word.toBits?, ↓reduceDIte, Option.map_some]
        have hrv := retValRep_bits (retTy := .uint8) (w := 8) ⟨rfl, rfl⟩
          (BitVec.setWidth 8 bv) σ.objs
        exact hk hrv.1 hrv.2
      · simp only [primUintP, PVal.toBits?, ↓reduceDIte, Option.map_some,
          Option.some.injEq] at hprim; subst hprim
        have hrt : retTy = LcTy.uint16 := by simpa using hret_u
        subst hrt
        simp only [HUintPrimWp, uintPure?, Word.toBits?, ↓reduceDIte, Option.map_some]
        have hrv := retValRep_bits (retTy := .uint16) (w := 16) ⟨rfl, rfl⟩
          (BitVec.setWidth 16 bv) σ.objs
        exact hk hrv.1 hrv.2
      · simp only [primUintP, PVal.toBits?, ↓reduceDIte, Option.map_some,
          Option.some.injEq] at hprim; subst hprim
        have hrt : retTy = LcTy.uint32 := by simpa using hret_u
        subst hrt
        simp only [HUintPrimWp, uintPure?, Word.toBits?, ↓reduceDIte, Option.map_some]
        have hrv := retValRep_bits (retTy := .uint32) (w := 32) ⟨rfl, rfl⟩
          (BitVec.setWidth 32 bv) σ.objs
        exact hk hrv.1 hrv.2
      · simp only [primUintP, PVal.toBits?, ↓reduceDIte, Option.map_some,
          Option.some.injEq] at hprim; subst hprim
        have hrt : retTy = LcTy.uint64 := by simpa using hret_u
        subst hrt
        simp only [HUintPrimWp, uintPure?, Word.toBits?, ↓reduceDIte, Option.map_some]
        have hrv := retValRep_bits (retTy := .uint64) (w := 64) ⟨rfl, rfl⟩
          (BitVec.setWidth 64 bv) σ.objs
        exact hk hrv.1 hrv.2
      · simp only [primUintP, PVal.toBits?, ↓reduceDIte, Option.map_some,
          Option.some.injEq] at hprim; subst hprim
        have hrt : retTy = LcTy.usize := by simpa using hret_u
        subst hrt
        simp only [HUintPrimWp, uintPure?, Word.toBits?, ↓reduceDIte, Option.map_some]
        have hrv := retValRep_bits (retTy := .usize) (w := 64) ⟨rfl, rfl⟩
          (BitVec.setWidth 64 bv) σ.objs
        exact hk hrv.1 hrv.2
    | erased | nat _ | str _ | ctor _ _ _ | arr _ | barr _ | int _ | clo _ _ _ =>
      revert hprim; rcases h_un with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [primUintP, PVal.toBits?]
  · rcases h_bin with ⟨h_bin, hlen⟩
    rcases as with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp at hlen
    obtain ⟨pa, pb, wa, wb, rfl, rfl, h1p, h2p, h1h, h2h⟩ := evalArgs_len_two hpvs hws
    obtain ⟨bva, bvb, rfl, rfl⟩ := primUintP_bin_extract h_bin hprim
    have ⟨ha_sc, hb_sc⟩ : argIsScalarW rf.ctx w a = true ∧ argIsScalarW rf.ctx w b = true := by
      have := primArgsWf_uint2 hsplit hw hargswf
      rcases h_bin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> exact this
    rw [argSc_toBits_word hvar ha_sc (hlive a List.mem_cons_self) h1p h1h (bv := bva)
          (by simp [PVal.toBits?]),
        argSc_toBits_word hvar hb_sc (hlive b (by simp)) h2p h2h (bv := bvb)
          (by simp [PVal.toBits?])]
    have hret_bin : if (op == "decEq" || op == "beq" || op == "decLt" || op == "blt" ||
        op == "decLe" || op == "ble") = true then retTy = LcTy.uint8
      else retTy.isScalar = true ∧ retTy.width = w := by
      rcases h_bin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> exact hret_u
    exact primUintP_bin_step h_bin hret_bin hprim hk

end

end LeanQbe.T.LeanLCNF.Sem
