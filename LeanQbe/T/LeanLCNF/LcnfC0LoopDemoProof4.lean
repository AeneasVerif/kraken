module

public import LeanQbe.T.LeanLCNF.LcnfC0LoopDemoProof3
public import LeanQbe.T.LeanLCNF.LcnfC0LinkKit

/-!
# Dual-Arch WP Proof for `FactLoop` (`LcnfC0LoopDemoProof4`)

Section 3b (part 1): `TFlat` WP step lemmas, factorial arithmetic, `rtC0CoreMod_loopModuleOk`,
`factAccInv`/`factAccSpec`/`factStrSpec`, `factLoopEnv`, and `factAcc_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T LeanQbe.T.Frontend.C0 LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Std Std.ExtHashMap
open scoped LeanQbe.T.ProofUtil

/-! ## 3b. `FactLoop` WP (`factAcc`, `factStr`), Runtime Lift, `ModuleOk`, and `loopRtMem` -/

/-- Concrete recursive factorial used to state and unfold `FactLoop.factAcc`. -/
@[expose] def natFact : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * natFact k

private theorem natFact_pos (n : Nat) : 0 < natFact n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ k ih => exact Nat.mul_pos (Nat.succ_pos k) ih

theorem factAcc_eq_mul (n acc : Nat) : FactLoop.factAcc n acc = acc * natFact n := by
  induction n generalizing acc with
  | zero =>
    rw [FactLoop.factAcc.eq_1]
    simp only [↓reduceDIte]
    exact (Nat.mul_one acc).symm
  | succ k ih =>
    rw [FactLoop.factAcc.eq_1]
    simp only [Nat.succ_ne_zero, ↓reduceDIte, Nat.succ_sub_one, ih, natFact]
    ac_rfl

private theorem factAcc_succ_step (k acc : Nat) :
    FactLoop.factAcc (k + 1) acc = FactLoop.factAcc k ((k + 1) * acc) := by
  rw [FactLoop.factAcc.eq_1]
  simp only [Nat.succ_ne_zero, ↓reduceDIte, Nat.succ_sub_one, Nat.mul_comm]

private theorem factAcc_step_le (k acc : Nat) :
    (k + 1) * acc ≤ FactLoop.factAcc (k + 1) acc := by
  rw [factAcc_succ_step, factAcc_eq_mul]
  exact Nat.le_mul_of_pos_right _ (natFact_pos k)

private theorem factAcc_acc_le (n acc : Nat) : acc ≤ FactLoop.factAcc n acc := by
  rw [factAcc_eq_mul]
  exact Nat.le_mul_of_pos_right _ (natFact_pos n)

theorem fact25_acc_eq : FactLoop.factAcc 25 1 = 15511210043330985984000000 := by
  rw [factAcc_eq_mul, Nat.one_mul]
  decide

private def evalDigitsFuel : Nat → Nat → List UInt8
  | _, 0 => []
  | n, k + 1 => if n = 0 then [] else UInt8.ofNat (48 + n % 10) :: evalDigitsFuel (n / 10) k

@[expose] def fact25Bytes : List UInt8 :=
  [49, 53, 53, 49, 49, 50, 49, 48, 48, 52, 51, 51, 51, 48, 57, 56, 53, 57, 56, 52,
    48, 48, 48, 48, 48, 48]

theorem fact25Bytes_len : fact25Bytes.length = 26 := by decide

theorem fact25Bytes_eq_ascii :
    fact25Bytes =
      "15511210043330985984000000".toList.map (fun c => UInt8.ofNat c.toNat) := by
  decide

theorem fact25_dec :
    natToDecimalBytes (FactLoop.factAcc 25 1) = fact25Bytes := by
  rw [fact25_acc_eq]
  have heq : ∀ k n, n < 10 ^ k → natDigitsRev n = evalDigitsFuel n k := by
    intro k
    induction k with
    | zero =>
      intro n hn
      have : n = 0 := by omega
      subst this
      rw [natDigitsRev.eq_def]
      simp [evalDigitsFuel]
    | succ k ih =>
      intro n hn
      by_cases hn0 : n = 0
      · subst hn0
        rw [natDigitsRev.eq_def]
        simp [evalDigitsFuel]
      · rw [natDigitsRev.eq_def, dite_eq_right hn0]
        simp only [evalDigitsFuel, hn0, ↓reduceIte]
        have hdiv : n / 10 < 10 ^ k :=
          Nat.div_lt_of_lt_mul (by rw [Nat.pow_succ'] at hn; omega)
        rw [ih (n / 10) hdiv]
  unfold natToDecimalBytes
  rw [ite_eq_right (by decide : (15511210043330985984000000 : Nat) ≠ 0),
    heq 26 _ (by decide)]
  decide

theorem boxNat_and_one {k : Nat} (hk : k < 2 ^ 63) :
    boxNat k &&& 1#64 = 1#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, boxNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by decide), Nat.and_one_is_mod]
  omega

theorem boxNat_ushr1 {k : Nat} (hk : k < 2 ^ 63) :
    boxNat k >>> 1#64 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp [boxNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

private theorem boxNat_ushr1_nat {k : Nat} (hk : k < 2 ^ 63) :
    boxNat k >>> (1 : Nat) = BitVec.ofNat 64 k :=
  boxNat_ushr1 hk

private theorem boxNat_sub_step {k : Nat} (hk : k + 1 < 2 ^ 63) :
    (boxNat (k + 1) &&& 3#64) &&& 1#64 = 1#64 ∧
      BitVec.ult (boxNat (k + 1)) 3#64 = false ∧
      (boxNat (k + 1) - 3#64) + 1#64 = boxNat k := by
  have hbox1 : (boxNat (k + 1)).toNat = 2 * (k + 1) + 1 := by
    unfold boxNat; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbox0 : (boxNat k).toNat = 2 * k + 1 := by
    unfold boxNat; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h3v : (3#64 : BitVec 64).toNat = 3 := by decide
  have h1v : (1#64 : BitVec 64).toNat = 1 := by decide
  have h1 : boxNat (k + 1) &&& 3#64 &&& 1#64 = 1#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_and, hbox1, h3v, h1v,
      Nat.and_assoc, show 3 &&& 1 = 1 from rfl, Nat.and_one_is_mod]
    omega
  have h2 : BitVec.ult (boxNat (k + 1)) 3#64 = false := by
    rw [BitVec.ult, hbox1, h3v]
    exact decide_eq_false (by omega)
  have h3 : (boxNat (k + 1) - 3#64) + 1#64 = boxNat k := by
    apply BitVec.eq_of_toNat_eq
    have hle : (3#64 : BitVec 64) ≤ boxNat (k + 1) := by
      rw [BitVec.le_def, hbox1, h3v]; omega
    rw [BitVec.toNat_add, BitVec.toNat_sub_of_le hle, hbox1, h3v, h1v, hbox0]
    omega
  exact ⟨h1, h2, h3⟩

private theorem umulw_ov_iff {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    ((BitVec.ofNat 64 ((x * y) / 2 ^ 64) ||| (BitVec.ofNat 64 (x * y) >>> 63#64)) ≠ 0#64) ↔
      2 ^ 63 ≤ x * y := by
  have hxy : x * y < 2 ^ 126 := by
    calc x * y < 2 ^ 63 * 2 ^ 63 := Nat.mul_lt_mul_of_lt_of_lt hx hy
      _ = 2 ^ 126 := by decide
  have h1 : (BitVec.ofNat 64 (x * y) >>> 63#64).toNat = ((x * y) % 2 ^ 64) / 2 ^ 63 := by
    simp [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have h2 : (BitVec.ofNat 64 ((x * y) / 2 ^ 64)).toNat = (x * y) / 2 ^ 64 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  constructor
  · intro hne
    by_cases hlt : x * y < 2 ^ 63
    · have hq : BitVec.ofNat 64 ((x * y) / 2 ^ 64) = 0#64 :=
        BitVec.eq_of_toNat_eq (by rw [h2, Nat.div_eq_of_lt (by omega)]; rfl)
      have hr : BitVec.ofNat 64 (x * y) >>> 63#64 = 0#64 :=
        BitVec.eq_of_toNat_eq (by rw [h1, Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt hlt]; rfl)
      exact absurd (by rw [hq, hr]; decide) hne
    · exact Nat.le_of_not_lt hlt
  · intro hge heq
    rw [BitVec.or_eq_zero_iff] at heq
    have hq : (x * y) / 2 ^ 64 = 0 := by
      have := congrArg BitVec.toNat heq.1; rw [h2] at this; exact this
    have hr : ((x * y) % 2 ^ 64) / 2 ^ 63 = 0 := by
      have := congrArg BitVec.toNat heq.2; rw [h1] at this; exact this
    have hd1 := Nat.div_add_mod (x * y) (2 ^ 64)
    have hd2 := Nat.div_add_mod ((x * y) % 2 ^ 64) (2 ^ 63)
    omega

private theorem two_mul_or_one (v : Nat) : (2 * v) ||| 1 = 2 * v + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp
  | succ j =>
    have h2 : (2 * v) / 2 = v := Nat.mul_div_right v (by decide)
    have h2p : (2 * v + 1) / 2 = v := by omega
    rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ, h2, h2p,
      show (1 : Nat) / 2 = 0 from rfl, Nat.zero_testBit, Bool.or_false]

private theorem umulw_ov_nat_iff {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    ((BitVec.ofNat 64 ((x * y) / 2 ^ 64) ||| (BitVec.ofNat 64 (x * y) >>> (63 : Nat))) ≠ 0) ↔
      2 ^ 63 ≤ x * y :=
  umulw_ov_iff hx hy

private theorem boxNat_umul_eq {x y : Nat} (hlt : x * y < 2 ^ 63) :
    (BitVec.ofNat 64 (x * y) <<< 1#64) ||| 1#64 = boxNat (x * y) := by
  apply BitVec.eq_of_toNat_eq
  have hlt1 : 2 * (x * y) + 1 < 2 ^ 64 := by omega
  have hlt2 : x * y * 2 < 2 ^ 64 := by omega
  have hshl : (BitVec.ofNat 64 (x * y) <<< 1#64).toNat = 2 * (x * y) := by
    simp [BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hlt2]
    omega
  rw [BitVec.toNat_or, hshl, boxNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by decide), Nat.mod_eq_of_lt hlt1, two_mul_or_one]

private theorem boxNat_umul_nat_eq {x y : Nat} (hlt : x * y < 2 ^ 63) :
    (BitVec.ofNat 64 (x * y) <<< (1 : Nat)) ||| 1#64 = boxNat (x * y) :=
  boxNat_umul_eq hlt

private theorem fn_eq_of_name_mem {xs : List Fn} (hnd : (xs.map Fn.name).Nodup)
    {a b : Fn} (ha : a ∈ xs) (hb : b ∈ xs) (heq : a.name = b.name) : a = b := by
  induction xs with
  | nil => cases ha
  | cons x t ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd ⟨b, hb, heq.symm⟩ hnd.1
    · exact absurd ⟨a, ha, heq⟩ hnd.1
    · exact ih hnd.2 ha hb

private theorem func_wp_monoEnv {Γ Γ' : Env} (hsub : ∀ f as bs xs m Q X, Γ f as bs xs m Q X →
    Γ' f as bs xs m Q X) {as rs : List Ty} (f : Func as rs)
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost} :
    Func.wp Γ f xs m Q X → Func.wp Γ' f xs m Q X :=
  fun h => wp_env_mono (fun f as bs xs m Q X h => hsub f as bs xs m Q X h) _ _ h

theorem rtC0CoreMod_loop_wp {fn : Fn} (hfn : fn ∈ rtC0CoreMod.fns)
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (hpre : loopRtEnv fn.name fn.as fn.rs xs m Q X) :
    Func.wp loopRtEnv fn.body xs m Q X := by
  rcases hpre with hcore | hextra
  · exact func_wp_monoEnv rtC0CoreEnv_le_loopRtEnv _ (rtC0CoreMod_fn_sound hfn hcore)
  · have hnd : (rtC0CoreMod.fns.map Fn.name).Nodup := by
      have hnm := Module.namesNodup_of_checkNamesNodup
        ((Bool.and_eq_true _ _).mp rtC0CoreMod_checkAcyclic).1
      have hEx : rtC0CoreMod.externs = [] := rfl
      rw [Module.namesNodup, Module.names, hEx, List.map_nil, List.append_nil] at hnm
      exact hnm
    have hAllocMem : lcnf_nat_alloc ∈ rtC0CoreMod.fns :=
      List.mem_of_getElem? (by rfl : rtC0CoreMod.fns[7]? = some lcnf_nat_alloc)
    have hLimbsMem : bn_nat_from_limbs ∈ rtC0CoreMod.fns :=
      List.mem_of_getElem? (by rfl : rtC0CoreMod.fns[13]? = some bn_nat_from_limbs)
    have hArithMem : lcnf_nat_arith ∈ rtC0CoreMod.fns :=
      List.mem_of_getElem? (by rfl : rtC0CoreMod.fns[32]? = some lcnf_nat_arith)
    have hSlowMem : lcnf_nat_slow ∈ rtC0CoreMod.fns :=
      List.mem_of_getElem? (by rfl : rtC0CoreMod.fns[34]? = some lcnf_nat_slow)
    have hStrMem : lcnf_nat_to_str ∈ rtC0CoreMod.fns :=
      List.mem_of_getElem? (by rfl : rtC0CoreMod.fns[85]? = some lcnf_nat_to_str)
    rcases hextra with ⟨⟨has, hrs⟩, hnm, hsp⟩ | ⟨⟨has, hrs⟩, hnm, hsp⟩ |
      ⟨⟨has, hrs⟩, hnm, hsp⟩ | ⟨⟨has, hrs⟩, hnm, hsp⟩ | ⟨⟨has, hrs⟩, hnm, hsp⟩
    · have heq := fn_eq_of_name_mem hnd hfn hAllocMem hnm; subst heq; cases has; cases hrs
      exact lcnf_nat_alloc_rem_wp xs m Q X hsp
    · have heq := fn_eq_of_name_mem hnd hfn hLimbsMem hnm; subst heq; cases has; cases hrs
      exact bn_nat_from_limbs_rem_wp xs m Q X hsp
    · have heq := fn_eq_of_name_mem hnd hfn hArithMem hnm; subst heq; cases has; cases hrs
      exact lcnf_nat_mul_arith_wp xs m Q X hsp
    · have heq := fn_eq_of_name_mem hnd hfn hSlowMem hnm; subst heq; cases has; cases hrs
      exact lcnf_nat_mul_slow_wp xs m Q X hsp
    · have heq := fn_eq_of_name_mem hnd hfn hStrMem hnm; subst heq; cases has; cases hrs
      exact lcnf_nat_to_str_two_limb_wp xs m Q X hsp

theorem rtC0CoreMod_loopModuleOk : ModuleOk loopRtEnv rtC0CoreMod :=
  Module.moduleOk_of_checkAcyclic rtC0CoreMod_checkAcyclic rtC0CoreMod_fns_wf
    (fun _ hfn _ _ _ _ hp => rtC0CoreMod_loop_wp hfn hp)

/-- Loop invariant for `FactLoop.factAcc`: owns `bigNumRtInv ⋆ lcnfHeap objs ⋆ R`. -/
@[expose] def factAccInv (rt : BitVec 64) (st : BigNumRt.RtC0State)
    (scr : BitVec 64) (scrLimbs : List (BitVec 64)) (objs : List BigNumRt.LcnfObj)
    (k accVal : Nat) (n acc : BitVec 64) (resVal extraRem : Nat)
    (R : Mem 64 → Prop) (m : Mem 64) : Prop :=
  k < 2 ^ 63 ∧ n = boxNat k ∧ FactLoop.factAcc k accVal = resVal ∧
  BigNumRtWf rt st scr scrLimbs ∧
  natRep acc accVal objs ∧
  (accVal < 2 ^ 63 → objs = []) ∧
  (2 ^ 63 ≤ accVal →
    ∃ accObj, accObj ∈ objs ∧ accObj.addr = acc ∧ accObj.rc = 1#32 ∧
      mpzNatCanon accObj accVal ∧ BigNumRt.lcnfHeapClosed objs ∧ BigNumRt.RcSound acc objs) ∧
  (∀ o ∈ objs, o.Wf) ∧
  objs.length + 1 ≤ st.workCap ∧ 2 ≤ st.workCap ∧
  2 * (1 + limbLenNat resVal) + 2 ≤ scrLimbs.length ∧
  limbLenNat resVal ≤ mpzMaxLimbs ∧
  extraRem + k * mpzAllocBytes (limbLenNat resVal) ≤ st.rem ∧
  (bigNumRtInv rt st scr scrLimbs ⋆ BigNumRt.lcnfHeap objs ⋆ R) m

/-- Spec for lowered `FactLoop.factAcc (k, accVal)` parameterized by remaining budget `extraRem`. -/
@[expose] def factAccSpec : Spec [i64, i64, i64] [i64] :=
  fun (rt, n, acc, ()) m Q _X =>
    ∃ (st : BigNumRt.RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
      (objs : List BigNumRt.LcnfObj) (k accVal resVal extraRem : Nat) (R : Mem 64 → Prop),
      factAccInv rt st scr scrLimbs objs k accVal n acc resVal extraRem R m ∧
      ∀ (res : BitVec 64) (st' : BigNumRt.RtC0State) (scrLimbs' : List (BitVec 64))
        (objs' : List BigNumRt.LcnfObj) (m' : Mem 64),
        st'.PreservesMeta st → st'.rem ≤ st.rem → extraRem ≤ st'.rem →
        BigNumRtWf rt st' scr scrLimbs' →
        natRep res resVal objs' →
        (resVal < 2 ^ 63 → objs' = [] ∧ st'.rem = st.rem) →
        (2 ^ 63 ≤ resVal →
          ∃ resObj, resObj ∈ objs' ∧ resObj.addr = res ∧ resObj.rc = 1#32 ∧
            mpzNatCanon resObj resVal ∧ objs'.length ≤ st.workCap ∧
            BigNumRt.lcnfHeapClosed objs' ∧ BigNumRt.RcSound res objs') →
        (∀ o ∈ objs', o.Wf) →
        (bigNumRtInv rt st' scr scrLimbs' ⋆ BigNumRt.lcnfHeap objs' ⋆ R) m' →
        Q (res, ()) m'

/-- Spec for lowered `FactLoop.factStr`: handles small boxed and 2-limb factorials. -/
@[expose] def factStrSpec : Spec [i64, i64] [i64] :=
  fun (rt, n, ()) m Q _X =>
    ∃ (st : BigNumRt.RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
      (k : Nat) (R : Mem 64 → Prop),
      let resVal := FactLoop.factAcc k 1
      k < 2 ^ 63 ∧ n = boxNat k ∧
      BigNumRtWf rt st scr scrLimbs ∧
      2 ≤ st.workCap ∧
      2 * (1 + limbLenNat resVal) + 2 ≤ scrLimbs.length ∧
      limbLenNat resVal ≤ mpzMaxLimbs ∧
      (resVal < 2 ^ 63 ∨ limbLenNat resVal = 2) ∧
      k * mpzAllocBytes (limbLenNat resVal) +
        (mpzAllocBytes 2 + sarrayAllocBytes 40 + strAllocBytes 41) ≤ st.rem ∧
      (bigNumRtInv rt st scr scrLimbs ⋆ R) m ∧
      ∀ (s : BitVec 64) (st' : RtC0State) (objs' : List LcnfObj)
        (scrLimbs' : List (BitVec 64)) (m' : Mem 64),
        s ≠ 0#64 → s.toNat % 8 = 0 →
        st'.PreservesMeta (b2rState st) → st'.rem ≤ st.rem →
        have dec := natToDecimalBytes resVal
        have sObj := mkStrObj s 1#32 (dec.length + 1) dec dec.length
        StrCanon sObj →
        (rtC0Inv rt st' ⋆ lcnfObjMem sObj ⋆ lcnfHeap objs' ⋆
          cell64 (rt + 33672#64) scr ⋆
          cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs'.length) ⋆
          array64 scr scrLimbs' ⋆ R) m' →
        Q (s, ()) m'

/-- Program-level specs for `FactLoop.factAcc` and `FactLoop.factStr`. -/
@[expose] def factLoopProgEnv : Env := fun f as bs xs m Q X =>
  (∃ (h : as = [i64, i64, i64] ∧ bs = [i64]),
    f = "l_LeanQbe_T_LeanLCNF_FactLoop_factAcc" ∧ factAccSpec (h.1 ▸ xs) m (h.2 ▸ Q) X) ∨
  (∃ (h : as = [i64, i64] ∧ bs = [i64]),
    f = "l_LeanQbe_T_LeanLCNF_FactLoop_factStr" ∧ factStrSpec (h.1 ▸ xs) m (h.2 ▸ Q) X)

/-- Unified environment for `factLoopLinkedMod`: runtime specs on core fns, prog specs else. -/
@[expose] def factLoopEnv : Env := fun f as bs xs m Q X =>
  if f ∈ rtCoreFnNames then loopRtEnv f as bs xs m Q X
  else factLoopProgEnv f as bs xs m Q X

theorem loopRtEnv_le_factLoopEnv_of_mem {f : Sym} (hf : f ∈ rtCoreFnNames)
    (as bs : List Ty) (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    loopRtEnv f as bs xs m Q X → factLoopEnv f as bs xs m Q X := by
  intro h; dsimp only [factLoopEnv]; rw [ite_eq_left hf]; exact h

private theorem limbLenNat_pos_lt63 {k : Nat} (hp : 0 < k) (hk : k < 2 ^ 63) :
    limbLenNat k = 1 := by
  unfold limbLenNat
  rw [ite_eq_right (Nat.ne_of_gt hp)]
  have hlog : k.log2 < 63 := (Nat.log2_lt (Nat.ne_of_gt hp)).mpr hk
  omega

private theorem and_zero_of_and_one_zero {x y : BitVec 64} (hx : x &&& 1#64 = 0#64) :
    (x &&& y) &&& 1#64 = 0#64 := by
  calc (x &&& y) &&& 1#64 = (x &&& 1#64) &&& y := by ac_rfl
    _ = 0#64 &&& y := by rw [hx]
    _ = 0#64 := BitVec.zero_and

private theorem boxNat_and_boxNat_and_one {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (boxNat a &&& boxNat b) &&& 1#64 = 1#64 := by
  rw [show (boxNat a &&& boxNat b) &&& 1#64 = (boxNat a &&& 1#64) &&& (boxNat b &&& 1#64) by
    ac_rfl, boxNat_and_one ha, boxNat_and_one hb]
  decide

theorem wp_call_pred {Γ : Env} {rs as bs : List Ty} {f : Sym}
    {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont rs}
    {m : Mem 64} {Q : Post rs} {X : XPost} (P : Post bs)
    (hcall : Γ f as bs (vals args) m P X)
    (hk : ∀ r m', P r m' → wp Γ Q X (k r) m') :
    wp Γ Q X (.call f args k) m :=
  ⟨P, X, hcall, hk, fun _ _ _ _ hx => hx⟩

@[expose] def decRefExpr (rt ptr : Val i64) (cont : Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var ptr) (.imm 1#64)) fun b =>
  .let_ (_root_.LeanQbe.T.op2 (OpCode.ne i64) (.var b.1) (.imm 0#64)) fun c =>
  .group (sig := [[]]) (fun _ => .cons (fun _ => cont) .nil) fun J =>
  .jnz (.var c.1) (.jump J.1 ())
    (.load i32 (.var ptr) fun rc =>
    .let_ (_root_.LeanQbe.T.op2 (OpCode.eq i32) (.var rc) (.imm 1#32)) fun is1 =>
    .jnz (.var is1.1)
      (.call "lcnf_dec_ref_cold" (as := [i64, i64]) (bs := []) (.var rt, .var ptr, ())
        fun _ => .jump J.1 ())
      (.let_ (_root_.LeanQbe.T.op2 (OpCode.sgt i32) (.var rc) (.imm 1#32)) fun sgt =>
      .let_ (_root_.LeanQbe.T.op1 (OpCode.ofBool 32) (.var sgt.1)) fun sub1 =>
      .let_ (_root_.LeanQbe.T.op2 (OpCode.sub i32) (.var rc) (.var sub1.1)) fun nrc =>
      .store (.var nrc.1) (.var ptr) (.jump J.1 ())))

@[expose] def factAccSubExpr (rt cn : Val i64)
    (cont : Val i64 → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var cn) (.imm 3#64)) fun v4 =>
  .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var v4.1) (.imm 1#64)) fun v5 =>
  .let_ (_root_.LeanQbe.T.op2 (OpCode.ne i64) (.var v5.1) (.imm 0#64)) fun v6 =>
  .group (sig := [[i64]]) (fun _ => .cons (fun xs => cont xs.1) .nil) fun J =>
  .jnz (.var v6.1)
    (.let_ (_root_.LeanQbe.T.op2 (OpCode.ult i64) (.var cn) (.imm 3#64)) fun v35 =>
    .jnz (.var v35.1) (.jump J.1 (.imm 1#64, ()))
      (.let_ (_root_.LeanQbe.T.op2 (OpCode.sub i64) (.var cn) (.imm 3#64)) fun v36 =>
      .let_ (_root_.LeanQbe.T.op2 (OpCode.add i64) (.var v36.1) (.imm 1#64)) fun v37 =>
      .jump J.1 (.var v37.1, ())))
    (.call "lcnf_nat_slow" (as := [i64, i64, i64, i64]) (bs := [i64])
      (.var rt, .imm 2#64, .var cn, .imm 3#64, ()) fun v38 => .jump J.1 (.var v38.1, ()))

@[expose] def factAccMulExpr (rt cn ca : Val i64)
    (cont : Val i64 → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var ca) (.var cn)) fun v7 =>
  .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var v7.1) (.imm 1#64)) fun v8 =>
  .let_ (_root_.LeanQbe.T.op2 (OpCode.ne i64) (.var v8.1) (.imm 0#64)) fun v9 =>
  .group (sig := [[i64]]) (fun _ => .cons (fun xs => cont xs.1) .nil) fun J =>
  .jnz (.var v9.1)
    (.let_ (_root_.LeanQbe.T.op2 (OpCode.lshr i64) (.var ca) (.imm 1#64)) fun v24 =>
    .let_ (_root_.LeanQbe.T.op2 (OpCode.lshr i64) (.var cn) (.imm 1#64)) fun v25 =>
    .let_ (_root_.LeanQbe.T.op2 (OpCode.umulw 64) (.var v24.1) (.var v25.1)) fun um =>
    .let_ (_root_.LeanQbe.T.op2 (OpCode.lshr i64) (.var um.1) (.imm 63#64)) fun v28 =>
    .let_ (_root_.LeanQbe.T.op2 (OpCode.or i64) (.var um.2.1) (.var v28.1)) fun v29 =>
    .let_ (_root_.LeanQbe.T.op2 (OpCode.ne i64) (.var v29.1) (.imm 0#64)) fun v30 =>
    .jnz (.var v30.1)
      (.call "lcnf_nat_slow" (as := [i64, i64, i64, i64]) (bs := [i64])
        (.var rt, .imm 3#64, .var ca, .var cn, ()) fun v31 =>
        .jump J.1 (.var v31.1, ()))
      (.let_ (_root_.LeanQbe.T.op2 (OpCode.shl i64) (.var um.1) (.imm 1#64)) fun v32 =>
      .let_ (_root_.LeanQbe.T.op2 (OpCode.or i64) (.var v32.1) (.imm 1#64)) fun v33 =>
      .jump J.1 (.var v33.1, ())))
    (.call "lcnf_nat_slow" (as := [i64, i64, i64, i64]) (bs := [i64])
      (.var rt, .imm 3#64, .var ca, .var cn, ()) fun v34 => .jump J.1 (.var v34.1, ()))

@[expose] def factAccHoas (rt n0 acc0 : Val i64) : Expr Val Cont [i64] :=
  .group (sig := [[i64, i64]])
    (fun J0 => .cons (fun xs0 =>
      let cn := xs0.1; let ca := xs0.2.1
      .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var cn) (.imm 1#64)) fun v0 =>
      .let_ (_root_.LeanQbe.T.op2 (OpCode.and i64) (.var v0.1) (.imm 1#64)) fun v1 =>
      .let_ (_root_.LeanQbe.T.op2 (OpCode.ne i64) (.var v1.1) (.imm 0#64)) fun v2 =>
      .group (sig := [[i8]]) (fun _ => .cons (fun xs1 =>
        let isOne := xs1.1
        .let_ (_root_.LeanQbe.T.op2 (OpCode.eq i8) (.var isOne) (.imm 0#8)) fun v3 =>
        .jnz (.var v3.1)
          (factAccSubExpr rt cn fun sub =>
            factAccMulExpr rt cn ca fun prod =>
              decRefExpr rt cn (decRefExpr rt ca (.jump J0.1 (.var sub, .var prod, ()))))
          (decRefExpr rt cn (.ret (.var ca, ())))
      ) .nil) fun J1 =>
      .jnz (.var v2.1)
        (.let_ (_root_.LeanQbe.T.op2 (OpCode.eq i64) (.var cn) (.imm 1#64)) fun v46 =>
        .let_ (_root_.LeanQbe.T.op1 (OpCode.ofBool 8) (.var v46.1)) fun v47 =>
        .jump J1.1 (.var v47.1, ()))
        (.call "lcnf_nat_slow" (as := [i64, i64, i64, i64]) (bs := [i64])
          (.var rt, .imm 6#64, .var cn, .imm 1#64, ()) fun v48 =>
        .let_ (_root_.LeanQbe.T.op1 (OpCode.trunc 64 8) (.var v48.1)) fun v49 =>
        .jump J1.1 (.var v49.1, ()))
    ) .nil)
    (fun J0 => .jump J0.1 (.var n0, .var acc0, ()))

private theorem decRefExpr_scalar_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {rt ptr : Val i64} {cont : Expr Val Cont [i64]} {m : Mem 64}
    (hsc : ptr &&& 1#64 = 1#64) (hcont : wp Γ Q X cont m) :
    wp Γ Q X (decRefExpr rt ptr cont) m := by
  unfold decRefExpr
  c0_let_simp
  refine wp_join_group (fun _ m' => m' = m) ?_ ?_
  · rintro J ⟨⟩ m' rfl
    rw [Blocks.get.eq_1]
    exact hcont
  · intro J hJ
    rw [wp_jnz]; dsimp only [Arg.val_var]
    refine ⟨fun _ => by rw [wp_jump]; exact hJ () m rfl,
      fun hf => absurd (by rw [hsc] at hf; exact hf : (1#64 != 0#64) = false) (by decide)⟩

private theorem factAcc_sub_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {rt : Val i64} {k' : Nat} (hkLt : k' + 1 < 2 ^ 63)
    {cont : Val i64 → Expr Val Cont [i64]} {m : Mem 64}
    (hcont : wp Γ Q X (cont (boxNat k')) m) :
    wp Γ Q X (factAccSubExpr rt (boxNat (k' + 1)) cont) m := by
  have hstep := boxNat_sub_step hkLt
  unfold factAccSubExpr
  c0_let_simp
  refine wp_join_group (fun (sub, ()) m' => sub = boxNat k' ∧ m' = m) ?_ ?_
  · rintro J ⟨sub, ⟨⟩⟩ m' ⟨rfl, rfl⟩
    rw [Blocks.get.eq_1]
    exact hcont
  · intro J hJ
    rw [wp_jnz]; dsimp only [Arg.val_var]
    refine ⟨fun _ => ?_, fun hf => absurd (by rw [hstep.1] at hf; exact hf
        : (1#64 != 0#64) = false) (by decide)⟩
    c0_let_simp
    rw [wp_jnz]; dsimp only [Arg.val_var]
    refine ⟨fun ht => absurd (hstep.2.1 ▸ ht) (by decide), fun _ => ?_⟩
    c0_let_simp
    rw [hstep.2.2]
    exact hJ (boxNat k', ()) m ⟨rfl, rfl⟩

private theorem factAcc_mul_wp {Q : Post [i64]} {X : XPost}
    {rt ca : Val i64} {k' accVal resVal extraRem : Nat}
    {st0 st : BigNumRt.RtC0State} {scr : BitVec 64} {scrLimbs : List (BitVec 64)}
    {objs : List BigNumRt.LcnfObj} {R : Mem 64 → Prop} {mk : Mem 64}
    (hkLt : k' + 1 < 2 ^ 63) (hpr0 : st.PreservesMeta st0) (hrem0 : st.rem ≤ st0.rem)
    (hremSmall0 : resVal < 2 ^ 63 → st.rem = st0.rem) (hwf : BigNumRtWf rt st scr scrLimbs)
    (hrep : natRep ca accVal objs) (haccEmpty : accVal < 2 ^ 63 → objs = [])
    (hobjsWf : ∀ o ∈ objs, o.Wf)
    (hscrCap : 2 * (1 + limbLenNat resVal) + 2 ≤ scrLimbs.length)
    (hmaxLimb : limbLenNat resVal ≤ mpzMaxLimbs)
    (hremB : extraRem + (k' + 1) * mpzAllocBytes (limbLenNat resVal) ≤ st.rem)
    (hmulLt : (k' + 1) * accVal ≤ resVal)
    (hmk : (bigNumRtInv rt st scr scrLimbs ⋆ BigNumRt.lcnfHeap objs ⋆ R) mk)
    {cont : Val i64 → Expr Val Cont [i64]}
    (hk : ∀ prod st1 scrLimbs1 objs1 m3,
      st1.PreservesMeta st0 → st1.rem ≤ st0.rem →
      (resVal < 2 ^ 63 → st1.rem = st0.rem) →
      BigNumRtWf rt st1 scr scrLimbs1 → natRep prod ((k' + 1) * accVal) objs1 →
      ((k' + 1) * accVal < 2 ^ 63 → objs1 = []) →
      (2 ^ 63 ≤ (k' + 1) * accVal →
        ∃ newObj, newObj ∈ objs1 ∧ newObj.addr = prod ∧ newObj.rc = 1#32 ∧
          mpzNatCanon newObj ((k' + 1) * accVal) ∧
          ((accVal < 2 ^ 63 ∧ objs1 = [newObj]) ∨
            (2 ^ 63 ≤ accVal ∧ objs1 = newObj :: objs))) →
      (∀ o ∈ objs1, o.Wf) → st1.workCap = st.workCap →
      2 * (1 + limbLenNat resVal) + 2 ≤ scrLimbs1.length →
      extraRem + k' * mpzAllocBytes (limbLenNat resVal) ≤ st1.rem →
      (bigNumRtInv rt st1 scr scrLimbs1 ⋆ BigNumRt.lcnfHeap objs1 ⋆ R) m3 →
      wp factLoopEnv Q X (cont prod) m3) :
    wp factLoopEnv Q X (factAccMulExpr rt (boxNat (k' + 1)) ca cont) mk := by
  have hmulMax : limbLenNat ((k' + 1) * accVal) ≤ limbLenNat resVal :=
    limbLenNat_mono_le hmulLt
  have hmulArith : natArithOk 3 accVal (k' + 1) scrLimbs.length st := by
    have hnb : limbLenNat accVal ≤ limbLenNat resVal :=
      Nat.le_trans (limbLenNat_mono_le (Nat.le_mul_of_pos_left accVal (Nat.succ_pos k'))) hmulMax
    have hna : limbLenNat (k' + 1) = 1 := limbLenNat_pos_lt63 (Nat.succ_pos k') hkLt
    have hlenB : mpzAllocBytes (limbLenNat (accVal * (k' + 1))) ≤ st.rem := by
      rw [Nat.mul_comm]
      have hmb : mpzAllocBytes (limbLenNat ((k' + 1) * accVal)) ≤
          mpzAllocBytes (limbLenNat resVal) := by unfold mpzAllocBytes; omega
      have hmul1 : mpzAllocBytes (limbLenNat resVal) ≤
          (k' + 1) * mpzAllocBytes (limbLenNat resVal) :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos k')
      omega
    refine ⟨by rw [hna]; omega,
      by unfold natArithRes; rw [Nat.mul_comm]; exact Nat.le_trans hmulMax hmaxLimb,
      fun _ => Or.inr hlenB⟩
  unfold factAccMulExpr
  c0_let_simp
  refine wp_join_group (fun (prod, ()) m3 =>
    ∃ (st1 : BigNumRt.RtC0State) (scrLimbs1 : List (BitVec 64))
      (objs1 : List BigNumRt.LcnfObj),
      st1.PreservesMeta st0 ∧ st1.rem ≤ st0.rem ∧ (resVal < 2 ^ 63 → st1.rem = st0.rem) ∧
      BigNumRtWf rt st1 scr scrLimbs1 ∧ natRep prod ((k' + 1) * accVal) objs1 ∧
      ((k' + 1) * accVal < 2 ^ 63 → objs1 = []) ∧
      (2 ^ 63 ≤ (k' + 1) * accVal →
        ∃ newObj, newObj ∈ objs1 ∧ newObj.addr = prod ∧ newObj.rc = 1#32 ∧
          mpzNatCanon newObj ((k' + 1) * accVal) ∧
          ((accVal < 2 ^ 63 ∧ objs1 = [newObj]) ∨
            (2 ^ 63 ≤ accVal ∧ objs1 = newObj :: objs))) ∧
      (∀ o ∈ objs1, o.Wf) ∧ st1.workCap = st.workCap ∧
      2 * (1 + limbLenNat resVal) + 2 ≤ scrLimbs1.length ∧
      extraRem + k' * mpzAllocBytes (limbLenNat resVal) ≤ st1.rem ∧
      (bigNumRtInv rt st1 scr scrLimbs1 ⋆ BigNumRt.lcnfHeap objs1 ⋆ R) m3) ?_ ?_
  · rintro J ⟨prod, ⟨⟩⟩ m3 ⟨st1, scrLimbs1, objs1, hpr1, hrem1, hremSmall1, hwf1, hrep1,
      hmulEmpty, hmulMpz, hobjsWf1, hwk1, hscr1, hremB1, hm3⟩
    rw [Blocks.get.eq_1]
    exact hk prod st1 scrLimbs1 objs1 m3 hpr1 hrem1 hremSmall1 hwf1 hrep1 hmulEmpty hmulMpz
      hobjsWf1 hwk1 hscr1 hremB1 hm3
  · intro J hJ
    rw [wp_jnz]; dsimp only [Arg.val_var]
    by_cases hcaLt : accVal < 2 ^ 63
    · have hcaEq : ca = boxNat accVal := by
        rw [natRep, ite_eq_left hcaLt] at hrep; exact hrep
      have hobjsNil : objs = [] := haccEmpty hcaLt
      subst hobjsNil
      refine ⟨fun _ => ?_, fun hf => absurd (by
          rw [hcaEq, boxNat_and_boxNat_and_one hcaLt hkLt]; decide :
          ((ca &&& boxNat (k' + 1)) &&& 1#64 != 0#64) = true) (by simp [hf])⟩
      c0_let_simp
      rw [hcaEq, boxNat_ushr1_nat hcaLt, boxNat_ushr1_nat hkLt]
      have hbv1 : BitVec.ofNat 64 accVal * BitVec.ofNat 64 (k' + 1) =
          BitVec.ofNat 64 ((k' + 1) * accVal) := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_comm, Nat.mul_mod]
      have hbv2 : BitVec.ofNat 64
          ((BitVec.ofNat 64 accVal).toNat * (BitVec.ofNat 64 (k' + 1)).toNat / 2 ^ 64) =
          BitVec.ofNat 64 (((k' + 1) * accVal) / 2 ^ 64) := by
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega), Nat.mul_comm accVal (k' + 1)]
      rw [hbv1, hbv2]
      rw [wp_jnz]; dsimp only [Arg.val_var]
      by_cases hmlt : (k' + 1) * accVal < 2 ^ 63
      · have hovFalse :
            ((BitVec.ofNat 64 ((k' + 1) * accVal / 2 ^ 64) |||
              BitVec.ofNat 64 ((k' + 1) * accVal) >>> (63 : Nat)) != 0) = false := by
          rw [bne_eq_false_iff_eq]
          exact Classical.byContradiction fun hne =>
            absurd ((umulw_ov_nat_iff hkLt hcaLt).mp hne) (Nat.not_le_of_gt hmlt)
        refine ⟨fun ht => absurd (hovFalse ▸ ht) (by decide), fun _ => ?_⟩
        c0_let_simp
        rw [boxNat_umul_nat_eq hmlt]
        refine hJ (boxNat ((k' + 1) * accVal), ()) mk ⟨st, scrLimbs, [], hpr0, hrem0,
          hremSmall0, hwf, (by simp [natRep, hmlt, boxNat]), (fun _ => rfl),
          (fun hbad => absurd hbad (Nat.not_le_of_gt hmlt)), (fun _ ho => by cases ho),
          rfl, hscrCap, ?_, hmk⟩
        rw [Nat.succ_mul] at hremB
        omega
      · have hmGe := Nat.le_of_not_lt hmlt
        have hovTrue :
            ((BitVec.ofNat 64 ((k' + 1) * accVal / 2 ^ 64) |||
              BitVec.ofNat 64 ((k' + 1) * accVal) >>> (63 : Nat)) != 0) = true := by
          rw [bne_iff_ne]
          exact (umulw_ov_nat_iff hkLt hcaLt).mpr hmGe
        refine ⟨fun _ => ?_, fun hf => absurd (hovTrue ▸ hf) (by decide)⟩
        refine wp_call_pred (fun (prod, ()) m3 =>
          ∃ (st1 : BigNumRt.RtC0State) (scrLimbs1 : List (BitVec 64))
            (newObj : BigNumRt.LcnfObj),
            st1.PreservesMeta st ∧ st1.rem ≤ st.rem ∧ BigNumRtWf rt st1 scr scrLimbs1 ∧
            natRep prod ((k' + 1) * accVal) [newObj] ∧ newObj.addr = prod ∧
            newObj.rc = 1#32 ∧ mpzNatCanon newObj ((k' + 1) * accVal) ∧
            scrLimbs1.length = scrLimbs.length ∧
            st.rem - mpzAllocBytes (limbLenNat ((k' + 1) * accVal)) ≤ st1.rem ∧
            (bigNumRtInv rt st1 scr scrLimbs1 ⋆ BigNumRt.lcnfHeap [newObj] ⋆ R) m3) ?_ ?_
        · refine loopRtEnv_le_factLoopEnv_of_mem (by decide) _ _ _ _ _ _
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨rfl, rfl⟩, rfl, rfl, st, scr, scrLimbs, [],
              accVal, k' + 1, R, hwf, (by simpa [hcaEq] using hrep),
              (by simp [natRep, hkLt, boxNat]), hmulArith, hmk,
              fun prod st1 scrLimbs1 _ m3 hpr1 hrem1 hscrLen1 hwf1 hrep1 _ hSlow hmk3 =>
                ?_⟩)))))
          rw [Nat.mul_comm] at hrep1 hSlow
          rcases hSlow hmGe with ⟨hremSub, newObj, haddr, hrc, hcan, rfl⟩
          exact ⟨st1, scrLimbs1, newObj, hpr1, hrem1, hwf1, hrep1, haddr, hrc, hcan, hscrLen1,
            hremSub, hmk3⟩
        · rintro ⟨prod, ⟨⟩⟩ m3 ⟨st1, scrLimbs1, newObj, hpr1, hrem1, hwf1, hrep1, haddr, hrc,
            hcan, hscrLen1, hremSub, hm3⟩
          rw [wp_jump]; dsimp only [vals, Arg.val]
          have hmB : mpzAllocBytes (limbLenNat ((k' + 1) * accVal)) ≤
              mpzAllocBytes (limbLenNat resVal) := by unfold mpzAllocBytes; omega
          refine hJ (prod, ()) m3 ⟨st1, scrLimbs1, [newObj], preservesMeta_bn_trans hpr0 hpr1,
            Nat.le_trans hrem1 hrem0,
            (fun hlt => absurd (Nat.le_trans hmGe hmulLt) (Nat.not_le_of_gt hlt)),
            hwf1, hrep1, (fun hlt => absurd hmGe (Nat.not_le_of_gt hlt)),
            (fun _ => ⟨newObj, List.mem_cons_self, haddr, hrc, hcan, Or.inl ⟨hcaLt, rfl⟩⟩),
            (fun o ho => by rcases List.mem_singleton.mp ho with rfl; exact hcan.1),
            preservesMeta_bn_workCap hpr1, (by rw [hscrLen1]; exact hscrCap), ?_, hm3⟩
          rw [Nat.succ_mul] at hremB
          omega
    · have hcaGe : 2 ^ 63 ≤ accVal := Nat.le_of_not_lt hcaLt
      have hmGe : 2 ^ 63 ≤ (k' + 1) * accVal :=
        Nat.le_trans hcaGe (Nat.le_mul_of_pos_left accVal (Nat.succ_pos k'))
      have hcaTag : ca &&& 1#64 = 0#64 := by
        rw [natRep, ite_eq_right hcaLt] at hrep; exact hrep.1
      have hzero : ((ca &&& boxNat (k' + 1)) &&& 1#64 != 0#64) = false := by
        rw [and_zero_of_and_one_zero hcaTag]; decide
      refine ⟨fun ht => absurd (hzero ▸ ht) (by decide), fun _ => ?_⟩
      refine wp_call_pred (fun (prod, ()) m3 =>
        ∃ (st1 : BigNumRt.RtC0State) (scrLimbs1 : List (BitVec 64))
          (newObj : BigNumRt.LcnfObj),
          st1.PreservesMeta st ∧ st1.rem ≤ st.rem ∧ BigNumRtWf rt st1 scr scrLimbs1 ∧
          natRep prod ((k' + 1) * accVal) (newObj :: objs) ∧ newObj.addr = prod ∧
          newObj.rc = 1#32 ∧ mpzNatCanon newObj ((k' + 1) * accVal) ∧
          scrLimbs1.length = scrLimbs.length ∧
          st.rem - mpzAllocBytes (limbLenNat ((k' + 1) * accVal)) ≤ st1.rem ∧
          (bigNumRtInv rt st1 scr scrLimbs1 ⋆
            BigNumRt.lcnfHeap (newObj :: objs) ⋆ R) m3) ?_ ?_
      · refine loopRtEnv_le_factLoopEnv_of_mem (by decide) _ _ _ _ _ _
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨rfl, rfl⟩, rfl, rfl, st, scr, scrLimbs, objs,
            accVal, k' + 1, R, hwf, hrep, (by simp [natRep, hkLt, boxNat]), hmulArith, hmk,
            fun prod st1 scrLimbs1 _ m3 hpr1 hrem1 hscrLen1 hwf1 hrep1 _ hSlow
              hmk3 => ?_⟩)))))
        rw [Nat.mul_comm] at hrep1 hSlow
        rcases hSlow hmGe with ⟨hremSub, newObj, haddr, hrc, hcan, rfl⟩
        exact ⟨st1, scrLimbs1, newObj, hpr1, hrem1, hwf1, hrep1, haddr, hrc, hcan, hscrLen1,
          hremSub, hmk3⟩
      · rintro ⟨prod, ⟨⟩⟩ m3 ⟨st1, scrLimbs1, newObj, hpr1, hrem1, hwf1, hrep1, haddr, hrc,
          hcan, hscrLen1, hremSub, hm3⟩
        rw [wp_jump]; dsimp only [vals, Arg.val]
        have hmB : mpzAllocBytes (limbLenNat ((k' + 1) * accVal)) ≤
            mpzAllocBytes (limbLenNat resVal) := by unfold mpzAllocBytes; omega
        refine hJ (prod, ()) m3 ⟨st1, scrLimbs1, newObj :: objs,
          preservesMeta_bn_trans hpr0 hpr1, Nat.le_trans hrem1 hrem0,
          (fun hlt => absurd (Nat.le_trans hmGe hmulLt) (Nat.not_le_of_gt hlt)),
          hwf1, hrep1, (fun hlt => absurd hmGe (Nat.not_le_of_gt hlt)),
          (fun _ => ⟨newObj, List.mem_cons_self, haddr, hrc, hcan, Or.inr ⟨hcaGe, rfl⟩⟩),
          (fun o ho => by
            rcases List.mem_cons.mp ho with rfl | ho'
            · exact hcan.1
            · exact hobjsWf o ho'),
          preservesMeta_bn_workCap hpr1, (by rw [hscrLen1]; exact hscrCap), ?_, hm3⟩
        rw [Nat.succ_mul] at hremB
        omega

private theorem factAcc_decAcc_wp {Q : Post [i64]} {X : XPost}
    {rt ca prod : Val i64} {k' accVal resVal : Nat}
    {st0 st st1 : BigNumRt.RtC0State} {scr : BitVec 64} {scrLimbs1 : List (BitVec 64)}
    {objs objs1 : List BigNumRt.LcnfObj} {R : Mem 64 → Prop} {m3 : Mem 64}
    (hpr1 : st1.PreservesMeta st0) (hrem1 : st1.rem ≤ st0.rem)
    (hremSmall1 : resVal < 2 ^ 63 → st1.rem = st0.rem)
    (hmulLt : (k' + 1) * accVal ≤ resVal) (hwf1 : BigNumRtWf rt st1 scr scrLimbs1)
    (hrep : natRep ca accVal objs) (hrep1 : natRep prod ((k' + 1) * accVal) objs1)
    (haccMpz : 2 ^ 63 ≤ accVal →
      ∃ accObj, accObj ∈ objs ∧ accObj.addr = ca ∧ accObj.rc = 1#32 ∧
        mpzNatCanon accObj accVal ∧ BigNumRt.lcnfHeapClosed objs ∧ BigNumRt.RcSound ca objs)
    (hmulEmpty : (k' + 1) * accVal < 2 ^ 63 → objs1 = [])
    (hmulMpz : 2 ^ 63 ≤ (k' + 1) * accVal →
      ∃ newObj, newObj ∈ objs1 ∧ newObj.addr = prod ∧ newObj.rc = 1#32 ∧
        mpzNatCanon newObj ((k' + 1) * accVal) ∧
        ((accVal < 2 ^ 63 ∧ objs1 = [newObj]) ∨ (2 ^ 63 ≤ accVal ∧ objs1 = newObj :: objs)))
    (hobjsWf1 : ∀ o ∈ objs1, o.Wf) (hwkCap : objs.length + 1 ≤ st.workCap)
    (hwkMin : 2 ≤ st.workCap) (hwk1 : st1.workCap = st.workCap)
    (hm3 : (bigNumRtInv rt st1 scr scrLimbs1 ⋆ BigNumRt.lcnfHeap objs1 ⋆ R) m3)
    {cont : Expr Val Cont [i64]}
    (hk : ∀ st2 objs2 m5,
      st2.PreservesMeta st0 → st2.rem ≤ st0.rem →
      (resVal < 2 ^ 63 → st2.rem = st0.rem) → BigNumRtWf rt st2 scr scrLimbs1 →
      natRep prod ((k' + 1) * accVal) objs2 →
      ((k' + 1) * accVal < 2 ^ 63 → objs2 = []) →
      (2 ^ 63 ≤ (k' + 1) * accVal →
        ∃ newObj, newObj ∈ objs2 ∧ newObj.addr = prod ∧ newObj.rc = 1#32 ∧
          mpzNatCanon newObj ((k' + 1) * accVal) ∧
          BigNumRt.lcnfHeapClosed objs2 ∧ BigNumRt.RcSound prod objs2) →
      (∀ o ∈ objs2, o.Wf) → objs2.length + 1 ≤ st2.workCap → st1.rem ≤ st2.rem →
      (bigNumRtInv rt st2 scr scrLimbs1 ⋆ BigNumRt.lcnfHeap objs2 ⋆ R) m5 →
      wp factLoopEnv Q X cont m5) :
    wp factLoopEnv Q X (decRefExpr rt ca cont) m3 := by
  by_cases hcaLt : accVal < 2 ^ 63
  · have hcaEq : ca = boxNat accVal := by
      rw [natRep, ite_eq_left hcaLt] at hrep; exact hrep
    refine decRefExpr_scalar_wp (by rw [hcaEq]; exact boxNat_and_one hcaLt) ?_
    refine hk st1 objs1 m3 hpr1 hrem1 hremSmall1 hwf1 hrep1 hmulEmpty ?_ hobjsWf1 ?_
      (Nat.le_refl _) hm3
    · intro hge
      rcases hmulMpz hge with ⟨newObj, hmem, haddr, hrc, hcan, hsh⟩
      rcases hsh with ⟨_, rfl⟩ | ⟨hbad, _⟩
      · refine ⟨newObj, hmem, haddr, hrc, hcan,
          lcnfHeapClosed_cons_mpz hcan.2.1 (fun _ ho => by cases ho), ?_⟩
        rw [← haddr]
        exact rcSound_singleton_mpz hcan.2.1 hrc
      · omega
    · by_cases hmLt : (k' + 1) * accVal < 2 ^ 63
      · rw [hmulEmpty hmLt, hwk1]; exact Nat.le_trans (by decide) hwkMin
      · rcases hmulMpz (Nat.le_of_not_lt hmLt) with ⟨newObj, _, _, _, _, hsh⟩
        rcases hsh with ⟨_, rfl⟩ | ⟨hbad, _⟩
        · rw [hwk1]; exact hwkMin
        · omega
  · have hcaGe : 2 ^ 63 ≤ accVal := Nat.le_of_not_lt hcaLt
    have hmulGe : 2 ^ 63 ≤ (k' + 1) * accVal :=
      Nat.le_trans hcaGe (Nat.le_mul_of_pos_left accVal (Nat.succ_pos k'))
    have hcaTag : ca &&& 1#64 = 0#64 := by
      rw [natRep, ite_eq_right hcaLt] at hrep; exact hrep.1
    rcases haccMpz hcaGe with ⟨accObj, haccMem, haccAddr, haccRc, haccCan, hobjsCl, hobjsRc⟩
    rcases hmulMpz hmulGe with ⟨newObj, _, hnewAddr, hnewRc, hnewCan, hsh⟩
    rcases hsh with ⟨hbad, _⟩ | ⟨_, rfl⟩
    · omega
    unfold decRefExpr
    c0_let_simp
    refine wp_join_group (fun _ m5 =>
      ∃ (st2 : BigNumRt.RtC0State) (objs2 : List BigNumRt.LcnfObj),
        st2.PreservesMeta st0 ∧ st2.rem ≤ st0.rem ∧ (resVal < 2 ^ 63 → st2.rem = st0.rem) ∧
        BigNumRtWf rt st2 scr scrLimbs1 ∧ natRep prod ((k' + 1) * accVal) objs2 ∧
        ((k' + 1) * accVal < 2 ^ 63 → objs2 = []) ∧
        (2 ^ 63 ≤ (k' + 1) * accVal →
          ∃ resObj, resObj ∈ objs2 ∧ resObj.addr = prod ∧ resObj.rc = 1#32 ∧
            mpzNatCanon resObj ((k' + 1) * accVal) ∧
            BigNumRt.lcnfHeapClosed objs2 ∧ BigNumRt.RcSound prod objs2) ∧
        (∀ o ∈ objs2, o.Wf) ∧ objs2.length + 1 ≤ st2.workCap ∧ st1.rem ≤ st2.rem ∧
        (bigNumRtInv rt st2 scr scrLimbs1 ⋆ BigNumRt.lcnfHeap objs2 ⋆ R) m5) ?_ ?_
    · rintro J ⟨⟩ m5 ⟨st2, objs2, hpr2, hrem2, hremS2, hwf2, hrep2, hmE2, hmM2, hobWf2, hwk2,
        hsr2, hm5⟩
      rw [Blocks.get.eq_1]
      exact hk st2 objs2 m5 hpr2 hrem2 hremS2 hwf2 hrep2 hmE2 hmM2 hobWf2 hwk2 hsr2 hm5
    · intro J hJ
      rw [wp_jnz]; dsimp only [Arg.val_var]
      refine ⟨fun ht => absurd (by rw [hcaTag] at ht; exact ht : (0#64 != 0#64) = true)
        (by decide), fun _ => ?_⟩
      obtain ⟨idxAcc, hidxLt, haccAt⟩ :=
        List.mem_iff_getElem.mp (List.mem_cons_of_mem newObj haccMem)
      have hfocus := BigNumRt.lcnfHeap_focus (newObj :: objs) hidxLt
      have hm3_acc :
          (cell64 accObj.addr accObj.header ⋆ (cell64 (accObj.addr + 8#64) accObj.mpzMeta ⋆
            array64 (accObj.addr + 16#64) accObj.limbs ⋆
            BigNumRt.lcnfHeap (List.take idxAcc (newObj :: objs)) ⋆
            BigNumRt.lcnfHeap (List.drop (idxAcc + 1) (newObj :: objs)) ⋆
            bigNumRtInv rt st1 scr scrLimbs1 ⋆ R)) m3 := by
        have hobjMem : BigNumRt.lcnfObjMem accObj =
            cell64 accObj.addr accObj.header ⋆ cell64 (accObj.addr + 8#64) accObj.mpzMeta ⋆
              array64 (accObj.addr + 16#64) accObj.limbs := by
          dsimp only [BigNumRt.lcnfObjMem]
          rw [haccCan.2.1]
          simp [BigNumRt.mpzTag, closureTag, BigNumRt.arrayTag,
            BigNumRt.sarrayTag, BigNumRt.stringTag]
        rw [hfocus, haccAt, hobjMem] at hm3
        exact sep_cast hm3 (by ac_rfl)
      have hldAcc : loadVal m3 i32 ca = some 1#32 := by
        rw [← haccAddr, ← haccRc]; exact loadVal_i32_cell64_header hm3_acc
      refine wp_load_of (v := 1#32) (by simpa [Arg.val_var] using hldAcc) ?_
      c0_let_simp
      rw [wp_jnz]; dsimp only [Arg.val_var]
      refine ⟨fun _ => ?_, fun hf => absurd hf (by decide)⟩
      have hm3_dec :
          (BigNumRt.rtC0Inv rt st1 ⋆ BigNumRt.lcnfHeap (newObj :: objs) ⋆
            (cell64 (rt + 33672#64) scr ⋆
              cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs1.length) ⋆
              array64 scr scrLimbs1 ⋆ R)) m3 := by
        unfold bigNumRtInv at hm3; exact sep_cast hm3 (by ac_rfl)
      have hm3_heap : (BigNumRt.lcnfHeap (newObj :: objs) ⋆
          (bigNumRtInv rt st1 scr scrLimbs1 ⋆ R)) m3 := sep_cast hm3 (by ac_rfl)
      have hndAddrs := bn_lcnfHeap_nodup_addrs hm3_heap
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hndAddrs
      have hneAddr : newObj.addr ≠ ca := fun heq =>
        hndAddrs.1 ⟨accObj, haccMem, haccAddr.trans heq.symm⟩
      have hprodTag : prod &&& 1#64 = 0#64 := by
        rw [natRep, ite_eq_right (Nat.not_lt_of_ge hmulGe)] at hrep1; exact hrep1.1
      have hnewAlign : newObj.addr &&& 1#64 = 0#64 := hnewAddr ▸ hprodTag
      have hnewFresh : newObj.addr ∉ objs.map BigNumRt.LcnfObj.addr := fun hm => by
        rcases List.mem_map.mp hm with ⟨a, ha, hea⟩; exact hndAddrs.1 ⟨a, ha, hea⟩
      have hcl1 : BigNumRt.lcnfHeapClosed (newObj :: objs) :=
        lcnfHeapClosed_cons_mpz hnewCan.2.1 hobjsCl
      have hrc1 : BigNumRt.RcSound ca (newObj :: objs) :=
        rcSound_cons_mpz hnewCan.2.1 hnewRc hnewAlign hnewFresh hneAddr hobjsCl hobjsRc
      refine wp_call_pred (fun _ m5 =>
        ∃ (st2 : BigNumRt.RtC0State) (objs2 : List BigNumRt.LcnfObj),
          st2.PreservesMeta st1 ∧ st2.rem = st1.rem ∧
          BigNumRt.DecColdRel ca (newObj :: objs) objs2 ∧
          (BigNumRt.rtC0Inv rt st2 ⋆ BigNumRt.lcnfHeap objs2 ⋆
            (cell64 (rt + 33672#64) scr ⋆
              cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs1.length) ⋆
              array64 scr scrLimbs1 ⋆ R)) m5) ?_ ?_
      · refine loopRtEnv_le_factLoopEnv_of_mem (by decide) _ _ _ _ _ _
          (rtC0CoreEnv_le_loopRtEnv _ _ _ _ _ _ _
          (rtC0CoreEnv_lcnf_dec_ref_cold (bnDecRefColdSpec_to_rt
          ⟨hcaTag, st1, newObj :: objs, _, hwk1 ▸ hwkCap, hm3_dec,
            ⟨accObj, List.mem_cons_of_mem newObj haccMem, haccAddr, haccRc⟩, hobjsWf1, hcl1,
            hrc1, fun st2 objs2 m5 hpr2 hrem2 hdecRel hm5 =>
              ⟨st2, objs2, hpr2, hrem2, hdecRel, hm5⟩⟩)))
      · rintro ⟨⟩ m5 ⟨st2, objs2, hpr2, hrem2, hdecRel, hm5⟩
        have hm5_inv :
            (bigNumRtInv rt st2 scr scrLimbs1 ⋆ BigNumRt.lcnfHeap objs2 ⋆ R) m5 := by
          unfold bigNumRtInv; exact sep_cast hm5 (by ac_rfl)
        have hm5_heap : (BigNumRt.lcnfHeap objs2 ⋆
            (bigNumRtInv rt st2 scr scrLimbs1 ⋆ R)) m5 := by
          unfold bigNumRtInv; exact sep_cast hm5 (by ac_rfl)
        have hstepDec := decColdRel_mpz_step
          (sep_mono2 (fun _ h => h) (fun _ _ => trivial) m3 hm3_heap)
          hnewCan.2.1 hnewRc haccMem haccCan.2.1 hobjsCl (haccAddr.symm ▸ hdecRel)
          (sep_mono2 (fun _ h => h) (fun _ _ => trivial) m5 hm5_heap)
        rw [wp_jump]
        refine hJ () m5 ⟨st2, objs2, preservesMeta_bn_trans hpr1 hpr2, hrem2 ▸ hrem1,
          (fun hlt => absurd (Nat.le_trans hmulGe hmulLt) (Nat.not_le_of_gt hlt)),
          ⟨preservesMeta_bn_bounded48 hwf1.1 hpr2, hwf1.2⟩,
          (by simp [natRep, Nat.not_lt_of_ge hmulGe, hprodTag]
              exact ⟨newObj, hstepDec.1, hnewAddr, hnewCan⟩),
          (fun hlt => absurd hmulGe (Nat.not_le_of_gt hlt)),
          (fun _ => ⟨newObj, hstepDec.1, hnewAddr, hnewRc, hnewCan, hstepDec.2.2.2.1,
            hnewAddr ▸ hstepDec.2.2.2.2⟩),
          hstepDec.2.2.1, (by rw [preservesMeta_bn_workCap hpr2, hwk1]; omega),
          Nat.le_of_eq hrem2.symm, hm5_inv⟩

theorem factAcc_wp (xs : Tup Val [i64, i64, i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    factAccSpec xs m Q X → Func.wp factLoopEnv (factLoopTfs.tf_0.toFn).body xs m Q X := by
  rcases xs with ⟨rt, n0, acc0, ⟨⟩⟩
  rintro ⟨st0, scr, scrLimbs0, objs0, k0, accVal0, resVal, extraRem, R, hinv0, hk⟩
  change wp factLoopEnv Q X (factAccHoas rt n0 acc0) m
  unfold factAccHoas
  refine wp_loop_inv (Γ := factLoopEnv)
    (fun (cn, ca, ()) mk =>
      ∃ (k accVal : Nat) (st : BigNumRt.RtC0State) (scrLimbs : List (BitVec 64))
        (objs : List BigNumRt.LcnfObj),
        st.PreservesMeta st0 ∧ st.rem ≤ st0.rem ∧
        (resVal < 2 ^ 63 → st.rem = st0.rem) ∧
        factAccInv rt st scr scrLimbs objs k accVal cn ca resVal extraRem R mk)
    (fun (cn, _, ()) _ => (cn >>> 1#64).toNat) ?_ ?_
  · intro J hJ
    rw [wp_jump]; dsimp only [vals, Arg.val]
    exact hJ (n0, acc0, ()) m ⟨k0, accVal0, st0, scrLimbs0, objs0,
      preservesMeta_bn_refl st0, Nat.le_refl _, fun _ => rfl, hinv0⟩
  · rintro J ⟨cn, ca, ⟨⟩⟩ mk
      ⟨k, accVal, st, scrLimbs, objs, hpr0, hrem0, hremSmall0,
        hkLt, rfl, hres, hwf, hrep, haccEmpty, haccMpz, hobjsWf, hwkCap, hwkMin, hscrCap,
        hmaxLimb, hremB, hmk⟩ hRec
    dsimp only [Blocks.get, Member.here]
    c0_let_simp
    have hand1 : ((boxNat k &&& 1#64) &&& 1#64 != 0#64) = true := by
      rw [boxNat_and_one hkLt]; decide
    refine wp_join_group (fun (isOne, ()) m1 =>
      (k = 0 ∧ isOne = 1#8 ∧ m1 = mk) ∨
      (∃ k', k = k' + 1 ∧ isOne = 0#8 ∧ m1 = mk)) ?_ ?_
    · rintro J1 ⟨isOne, ⟨⟩⟩ m1 h1
      rw [Blocks.get.eq_1]
      rcases h1 with ⟨rfl, rfl, rfl⟩ | ⟨k', rfl, rfl, rfl⟩
      · c0_let_simp
        rw [wp_jnz]; dsimp only [Arg.val_var]
        refine ⟨fun ht => absurd ht (by decide), fun _ => ?_⟩
        refine decRefExpr_scalar_wp (boxNat_and_one hkLt) ?_
        rw [wp_ret]; dsimp only [vals, Arg.val]
        have hvalEq : accVal = resVal := by
          rw [← hres, FactLoop.factAcc.eq_1]; simp only [↓reduceDIte]
        subst hvalEq
        exact hk ca st scrLimbs objs m1 hpr0 hrem0 (by omega) hwf hrep
          (fun hlt => ⟨haccEmpty hlt, hremSmall0 hlt⟩)
          (fun hge => by
            rcases haccMpz hge with ⟨accObj, hmem, haddr, hrc, hcan, hcl, hrcS⟩
            exact ⟨accObj, hmem, haddr, hrc, hcan,
              (by have hwc := preservesMeta_bn_workCap hpr0; rw [hwc] at hwkCap
                  exact Nat.le_trans (Nat.le_succ _) hwkCap), hcl, hrcS⟩)
          hobjsWf hmk
      · c0_let_simp
        rw [wp_jnz]; dsimp only [Arg.val_var]
        refine ⟨fun _ => ?_, fun hf => absurd hf (by decide)⟩
        refine factAcc_sub_wp hkLt ?_
        have hres' : FactLoop.factAcc k' ((k' + 1) * accVal) = resVal := by
          rw [← factAcc_succ_step, hres]
        have hmulLt : (k' + 1) * accVal ≤ resVal := hres ▸ factAcc_step_le k' accVal
        refine factAcc_mul_wp hkLt hpr0 hrem0 hremSmall0 hwf hrep haccEmpty hobjsWf
          hscrCap hmaxLimb hremB hmulLt hmk fun prod st1 scrLimbs1 objs1 m3 hpr1 hrem1
          hremSmall1 hwf1 hrep1 hmulEmpty hmulMpz hobjsWf1 hwk1 hscr1 hremB1 hm3 => ?_
        refine decRefExpr_scalar_wp (boxNat_and_one hkLt) ?_
        refine factAcc_decAcc_wp hpr1 hrem1 hremSmall1 hmulLt hwf1 hrep hrep1 haccMpz hmulEmpty
          hmulMpz hobjsWf1 hwkCap hwkMin hwk1 hm3 fun st2 objs2 m5 hpr2 hrem2 hremSmall2
          hwf2 hrep2 hmE2 hmM2 hobWf2 hwk2 hsr2 hm5 => ?_
        rw [wp_jump]; dsimp only [vals, Arg.val]
        have hdec : (boxNat k' >>> 1#64).toNat < (boxNat (k' + 1) >>> 1#64).toNat := by
          rw [boxNat_ushr1 (by omega), boxNat_ushr1 hkLt,
            BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        have hwkMin2 : 2 ≤ st2.workCap := by
          have h20 : st2.workCap = st0.workCap := preservesMeta_bn_workCap hpr2
          have hs0 : st.workCap = st0.workCap := preservesMeta_bn_workCap hpr0
          omega
        exact hRec (boxNat k', prod, ()) m5 hdec
          ⟨k', (k' + 1) * accVal, st2, scrLimbs1, objs2, hpr2, hrem2, hremSmall2,
            by omega, rfl, hres', hwf2, hrep2, hmE2, hmM2, hobWf2, hwk2, hwkMin2, hscr1,
            hmaxLimb, by omega, hm5⟩
    · intro J1 hJ1
      rw [wp_jnz]; dsimp only [Arg.val_var]
      refine ⟨fun _ => ?_, fun hf => absurd (hand1 ▸ hf) (by decide)⟩
      c0_let_simp
      cases k with
      | zero =>
        have h1 : (boxNat 0 == 1#64) = true := rfl
        rw [h1]; exact hJ1 (1#8, ()) mk (Or.inl ⟨rfl, rfl, rfl⟩)
      | succ k' =>
        have hne : boxNat (k' + 1) ≠ 1#64 := by
          intro heq
          have htn := congrArg BitVec.toNat heq
          rw [boxNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by decide)] at htn
          omega
        rw [beq_false_of_ne hne]
        exact hJ1 (0#8, ()) mk (Or.inr ⟨k', rfl, rfl, rfl⟩)

end LeanQbe.T.LeanLCNF
