/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1Core
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1Spec
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofKitten1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S1-C Proofs — Part 2 (`full_k6_init`, `full_k6_add_clause`)

Certifies `step13K6InitSpec` (`R1` `glue_used[33]` HWM + `L6a` split initialization loops) and
`step13K6AddClauseSpec` (`R1` `glue_used[33]` HWM update + `full_k6_add_ticks`), with every
theorem `<= 420` lines (`public section`, `0` `@[expose]`, `0` `import all`, `<= 100` cols).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open Kraken.Bedrock2.Test

open K6MemATactics K6PtrTactics
open scoped FullArenaTactics K6MemATactics K6PtrTactics

section S13CoreInitAddProof

attribute [local bv_c0] List.length_set

private structure S13InitScalar (L : K6Layout) (nv0 ac0 : BitVec 32) (st : K6State) : Prop where
  nv : st.nv = nv0
  nc : st.nc = 0#32
  lvl : st.lvl = 0#32
  prop : st.prop = 0#32
  trl_end : st.trl_end = 0#32
  unass : st.unass = nv0
  incons : st.incons = 0#32
  alen : st.alen = 0#32
  acap : st.acap = ac0
  nassump : st.nassump = 0#32
  nkl : st.nkl = 0#32
  nana : st.nana = 0#32
  status : st.status = 0#32
  openCnt : st.openCnt = 0#32
  max_v : st.max_v = L.mv32
  max_orig : st.max_orig = BitVec.ofNat 32 L.maxOrig
  max_cl : st.max_cl = BitVec.ofNat 32 L.maxCl
  neq : st.neq = 0#32

private theorem S13InitScalar.putArr {L : K6Layout} {nv ac : BitVec 32} {st : K6State}
    (h : S13InitScalar L nv ac st) (f : K6ArrField) (i : Nat) (v : BitVec 32) :
    S13InitScalar L nv ac (st.putArr f i v) := by
  cases f <;> exact ⟨h.nv, h.nc, h.lvl, h.prop, h.trl_end, h.unass, h.incons, h.alen, h.acap,
    h.nassump, h.nkl, h.nana, h.status, h.openCnt, h.max_v, h.max_orig, h.max_cl, h.neq⟩

private def S13VarPrefix (ks0 st : K6State) (L : K6Layout) (nLvl nRsn nFl lim : Nat) : Prop :=
  (∀ v < nLvl, st.lvlArr[v]? = some 0#32) ∧
  (∀ v, lim ≤ v → v < L.maxV → st.lvlArr[v]? = ks0.lvlArr[v]?) ∧
  (∀ v < nRsn, st.rsn[v]? = some 0xFFFFFFFF#32) ∧
  (∀ v, lim ≤ v → v < L.maxV → st.rsn[v]? = ks0.rsn[v]?) ∧
  (∀ v < nFl, st.flags[v]? = some 0#32) ∧
  (∀ v, lim ≤ v → v < L.maxV → st.flags[v]? = ks0.flags[v]?)

private def S13LitPrefix (ks0 st : K6State) (L : K6Layout) (nVal nWh lim : Nat) : Prop :=
  (∀ l < nVal, st.vals[l]? = some 0#32) ∧
  (∀ l, 2 * lim ≤ l → l < 2 * L.maxV → st.vals[l]? = ks0.vals[l]?) ∧
  (∀ l < nWh, st.whead[l]? = some 0xFFFFFFFF#32) ∧
  (∀ l, 2 * lim ≤ l → l < 2 * L.maxV → st.whead[l]? = ks0.whead[l]?)

private def S13InitSt (L : K6Layout) (nv ac : BitVec 32) (ks0 st : K6State)
    (nLvl nRsn nFl nVal nWh lim : Nat) (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (m : Mem 64) : Prop :=
  st.ShapesOk L ∧ S13InitScalar L nv ac st ∧ S13VarPrefix ks0 st L nLvl nRsn nFl lim ∧
  S13LitPrefix ks0 st L nVal nWh lim ∧
  (K6MemA L (L.kPtr c.pScratchBuf) st ⋆ (FullK6Frame c L s ⋆ R)) m

private theorem s13_varPrefix_putOther {ks0 st : K6State} {L : K6Layout} {nL nR nF lim : Nat}
    (h : S13VarPrefix ks0 st L nL nR nF lim)
    {f : K6ArrField} (hf : f ≠ .lvlArr ∧ f ≠ .rsn ∧ f ≠ .flags) (i : Nat) (v : BitVec 32) :
    S13VarPrefix ks0 (st.putArr f i v) L nL nR nF lim := by
  cases f <;> simp only [ne_eq, not_true_eq_false, false_and, and_false, K6State.putArr] at hf ⊢ <;>
    exact h

private theorem s13_litPrefix_putVar {ks0 st : K6State} {L : K6Layout} {nV nW lim : Nat}
    (h : S13LitPrefix ks0 st L nV nW lim)
    {f : K6ArrField} (hf : f ≠ .vals ∧ f ≠ .whead) (i : Nat) (v : BitVec 32) :
    S13LitPrefix ks0 (st.putArr f i v) L nV nW lim := by
  cases f <;> simp only [ne_eq, not_true_eq_false, false_and, and_false, K6State.putArr] at hf ⊢ <;>
    exact h

private theorem s13_prefix_step {xs : List (BitVec 32)} {k len lim : Nat} {val : BitVec 32}
    {ks_arr : List (BitVec 32)} (hk_lt : k < lim) (hk_len : k < xs.length) (_hlim : lim ≤ len)
    (h_lt : ∀ j < k, xs[j]? = some val) (h_ge : ∀ j, lim ≤ j → j < len → xs[j]? = ks_arr[j]?) :
    (∀ j < k + 1, (xs.set k val)[j]? = some val) ∧
    (∀ j, lim ≤ j → j < len → (xs.set k val)[j]? = ks_arr[j]?) := by
  refine ⟨fun j hj => ?_, fun j hj0 hj1 => ?_⟩
  · by_cases hjk : j = k
    · subst hjk; exact List.getElem?_set_self hk_len
    · rw [List.getElem?_set_ne (Ne.symm hjk)]; exact h_lt j (by omega)
  · rw [List.getElem?_set_ne (by omega)]; exact h_ge j hj0 hj1

private theorem s13_k6_maxV_call {Γ : Env} {rs : List Ty}
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    {n : Nat} (hn : n < 2 ^ 64) {Q : Post rs} {X : XPost}
    {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    (hk : wp Γ Q X (k (BitVec.ofNat 64 (k6MaxV n), ())) m) :
    wp Γ Q X (@Expr.call Val Cont rs "full_m6_max_v" [i64] [i64]
      (@Arg.var Val i64 (BitVec.ofNat 64 n), ()) k) m :=
  k6_maxV_call_step hMaxV hn hk

private theorem s13_k6_acap_val_eq (L : K6Layout) {cap : Nat}
    (hscr_bd : cap < dimacsBound) (hL_len : L.scrLen = cap) :
    ((BitVec.ofNat 64 cap -
      ((1280#32 + (L.mv32 <<< (1 : Nat))) + 32#32 + 38#32 * L.mv32).setWidth 64)).setWidth 32 =
    BitVec.ofNat 32 L.acap := by
  have hm_bd := L.hmaxV; have hac := L.hacap; unfold dimacsBound at hac hscr_bd
  have hmv : L.mv32.toNat = L.maxV := k6_mv32_toNat L
  have hshl : (L.mv32 <<< (1 : Nat)).toNat = 2 * L.maxV := by
    rw [k6_shl1_toNat, hmv, Nat.mod_eq_of_lt (by omega)]
  have hb_expr : ((1280#32 + (L.mv32 <<< (1 : Nat))) + 32#32 + 38#32 * L.mv32).toNat =
      1312 + 40 * L.maxV := by
    have h1280 : (1280#32 : BitVec 32).toNat = 1280 := by decide
    have h32 : (32#32 : BitVec 32).toNat = 32 := by decide
    have h38 : (38#32 : BitVec 32).toNat = 38 := by decide
    have h1 : (1280#32 + (L.mv32 <<< (1 : Nat))).toNat = 1280 + 2 * L.maxV := by
      rw [BitVec.toNat_add, h1280, hshl, Nat.mod_eq_of_lt (by omega)]
    have h2 : (1280#32 + (L.mv32 <<< (1 : Nat)) + 32#32).toNat = 1312 + 2 * L.maxV := by
      rw [BitVec.toNat_add, h1, h32, Nat.mod_eq_of_lt (by omega)]; omega
    have h3 : (38#32 * L.mv32).toNat = 38 * L.maxV := by
      rw [BitVec.toNat_mul, h38, hmv, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add, h2, h3, Nat.mod_eq_of_lt (by omega)]; omega
  have hscr_val : cap = L.k6Base + L.k6Fixed + L.acap := hL_len.symm
  have hbase_fix : L.k6Base + L.k6Fixed = 1312 + 40 * L.maxV := by
    unfold K6Layout.k6Base K6Layout.k6Fixed; omega
  have hsub64 :
      BitVec.ofNat 64 cap -
        ((1280#32 + (L.mv32 <<< (1 : Nat))) + 32#32 + 38#32 * L.mv32).setWidth 64 =
      BitVec.ofNat 64 L.acap := by
    apply BitVec.eq_of_toNat_eq
    have hm_b2 : (1312 + 40 * L.maxV) % 2 ^ 64 = 1312 + 40 * L.maxV := Nat.mod_eq_of_lt (by omega)
    have hm_sc : cap % 2 ^ 64 = cap := Nat.mod_eq_of_lt (by omega)
    have hm_ac : L.acap % 2 ^ 64 = L.acap := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub, BitVec.toNat_setWidth, hb_expr, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, hm_b2, hm_sc, hm_ac]
    have hsplit : 2 ^ 64 - (1312 + 40 * L.maxV) + cap = 2 ^ 64 + L.acap := by omega
    rw [hsplit]; omega
  rw [hsub64]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem s13_k6_hwm_weaken {L : K6Layout} {hw hw' : BitVec 32} {ks : K6State}
    (hhwm : K6HwmClean L hw ks) (hle : hw.toNat ≤ hw'.toNat) (hmax : hw'.toNat ≤ L.maxV) :
    K6HwmClean L hw' ks := by
  rcases hhwm with rfl | h
  · have := L.hmaxV; exfalso; simp at hle; omega
  · exact Or.inr ⟨hmax, fun v hv0 hv1 => h.2 v (Nat.le_trans hle hv0) hv1⟩

private theorem s13_k6_hwm_putHdr_ticks {L : K6Layout} {hw tk' : BitVec 32} {ks : K6State}
    (hhwm : K6HwmClean L hw ks) : K6HwmClean L hw (ks.putHdr .ticks tk') := hhwm

private theorem s13_k6_hwm_putHdr_incons {L : K6Layout} {hw x : BitVec 32} {ks : K6State}
    (hhwm : K6HwmClean L hw ks) : K6HwmClean L hw (ks.putHdr .incons x) := hhwm

private theorem s13_k6_hwm_add_ge2_any {L : K6Layout} {hw : BitVec 32} {ks stM : K6State}
    {cid l0 l1 tk' : BitVec 32}
    (hhwm : K6HwmClean L hw ks)
    (hlvl : stM.lvlArr = ks.lvlArr) (hrsn : stM.rsn = ks.rsn) (hfl : stM.flags = ks.flags)
    (hvals : stM.vals = ks.vals) (hwh : stM.whead = ks.whead)
    (hl0 : hw = 0xFFFFFFFF#32 ∨ l0.toNat < 2 * hw.toNat)
    (hl1 : hw = 0xFFFFFFFF#32 ∨ l1.toNat < 2 * hw.toNat) :
    K6HwmClean L hw ((k6WatchStep stM cid l0 l1).putHdr .ticks tk') := by
  rcases hhwm with rfl | hhwm
  · exact Or.inl rfl
  · rcases hl0 with hbad | hl0; · exact Or.inl hbad
    rcases hl1 with hbad | hl1; · exact Or.inl hbad
    refine Or.inr ⟨hhwm.1, fun v hv0 hv1 => ?_⟩
    have h := hhwm.2 v hv0 hv1
    dsimp only [k6WatchStep, k6WatchStep0, K6State.putHdr]
    refine ⟨by rw [hlvl]; exact h.1, by rw [hrsn]; exact h.2.1,
      by rw [hfl]; exact h.2.2.1, by rw [hvals]; exact h.2.2.2.1,
      by rw [hvals]; exact h.2.2.2.2.1, ?_, ?_⟩
    · change (((stM.whead.set l0.toNat (cid <<< 1)).set l1.toNat
        ((cid <<< 1) ||| 1#32))[2 * v]?.getD 0#32) = 0xFFFFFFFF#32
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hwh]
      exact h.2.2.2.2.2.1
    · change (((stM.whead.set l0.toNat (cid <<< 1)).set l1.toNat
        ((cid <<< 1) ||| 1#32))[2 * v + 1]?.getD 0#32) = 0xFFFFFFFF#32
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hwh]
      exact h.2.2.2.2.2.2

private theorem s13_k6_hwm_assign {L : K6Layout} {hw ul : BitVec 32} {ks : K6State}
    (hhwm : K6HwmClean L hw ks) (hul : hw = 0xFFFFFFFF#32 ∨ ul.toNat < 2 * hw.toNat) :
    K6HwmClean L hw (k6AssignStep ks ul 0xFFFFFFFF#32) := by
  rcases hhwm with rfl | hhwm
  · exact Or.inl rfl
  · rcases hul with hbad | hul; · exact Or.inl hbad
    refine Or.inr ⟨hhwm.1, fun v hv0 hv1 => ?_⟩
    have h := hhwm.2 v hv0 hv1
    have huv : (ul >>> (1 : Nat)).toNat < hw.toNat := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
    have hneg : (ul ^^^ 1#32).toNat < 2 * hw.toNat := by
      rw [BitVec.toNat_xor, show (1#32 : BitVec 32).toNat = 1 from rfl]
      rcases k6_nat_xor1_cases ul.toNat with ⟨_, hlt⟩ | ⟨_, hlt⟩ <;> omega
    refine ⟨?_, ?_, ?_, ?_, ?_, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
    · dsimp only [k6AssignStep]; rw [List.getElem?_set_ne (by omega)]; exact h.1
    · dsimp only [k6AssignStep]; rw [List.getElem?_set_ne (by omega)]; exact h.2.1
    · dsimp only [k6AssignStep]; rw [List.getElem?_set_ne (by omega)]; exact h.2.2.1
    · dsimp only [k6AssignStep]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact h.2.2.2.1
    · dsimp only [k6AssignStep]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact h.2.2.2.2.1

private theorem s13_k6_init_finish {L : K6Layout} {nv hw lim : BitVec 32} {ks0 st : K6State}
    (hsh : st.ShapesOk L) (hsh0 : ks0.ShapesOk L) (hnv_le : nv.toNat ≤ L.maxV)
    (hhwm : K6HwmClean L hw ks0)
    (hlim : lim = (if nv == L.mv32 && hw.toNat < L.maxV then hw else nv))
    (hvar : S13VarPrefix ks0 st L lim.toNat lim.toNat lim.toNat lim.toNat)
    (hlit : S13LitPrefix ks0 st L (2 * lim.toNat) (2 * lim.toNat) lim.toNat)
    (hsc : S13InitScalar L nv (BitVec.ofNat 32 L.acap) st) :
    (∀ P, K6Inv L P st) ∧ K6TrailSynced st ∧
    K6HwmClean L (if nv == L.mv32 then 0#32 else if hw < nv then nv else hw) st := by
  have hmv_val : L.mv32.toNat = L.maxV := k6_mv32_toNat L
  have hmax_b := L.hmaxV
  have hvars_lt : ∀ v < lim.toNat, st.lvlArr[v]? = some 0#32 ∧ st.rsn[v]? = some 0xFFFFFFFF#32 ∧
      st.flags[v]? = some 0#32 := fun v hv => ⟨hvar.1 v hv, hvar.2.2.1 v hv, hvar.2.2.2.2.1 v hv⟩
  have hvars_ge : ∀ v, lim.toNat ≤ v → v < L.maxV → st.lvlArr[v]? = ks0.lvlArr[v]? ∧
      st.rsn[v]? = ks0.rsn[v]? ∧ st.flags[v]? = ks0.flags[v]? := fun v h0 h1 =>
    ⟨hvar.2.1 v h0 h1, hvar.2.2.2.1 v h0 h1, hvar.2.2.2.2.2 v h0 h1⟩
  have hlits_lt : ∀ l < 2 * lim.toNat,
      st.vals[l]? = some 0#32 ∧ st.whead[l]? = some 0xFFFFFFFF#32 := fun l hl =>
    ⟨hlit.1 l hl, hlit.2.2.1 l hl⟩
  have hlits_ge : ∀ l, 2 * lim.toNat ≤ l → l < 2 * L.maxV →
      st.vals[l]? = ks0.vals[l]? ∧ st.whead[l]? = ks0.whead[l]? := fun l h0 h1 =>
    ⟨hlit.2.1 l h0 h1, hlit.2.2.2 l h0 h1⟩
  have hmv_nat : BitVec.ofNat 32 L.maxV = L.mv32 := rfl
  rcases hhwm with rfl | hhwm
  · have hlim_nv : lim = nv := by
      rw [hlim]; split
      · next h =>
        have hlt := ((Bool.and_eq_true _ _).mp h).2
        exfalso; have : (0xFFFFFFFF#32 : BitVec 32).toNat < L.maxV := by simpa using hlt
        simp at this; omega
      · rfl
    rw [hlim_nv] at hvars_lt hlits_lt
    have hinv_fin := k6Init_finish_inv hsh hnv_le hsc.nv hsc.nc hsc.lvl hsc.prop hsc.trl_end
      hsc.unass hsc.acap (hsc.max_v.trans hmv_nat) hsc.max_orig hsc.max_cl hsc.alen hsc.incons
      hsc.nassump hsc.nkl hsc.nana hvars_lt hlits_lt
    refine ⟨hinv_fin.1, hinv_fin.2, ?_⟩
    by_cases hnv_mv : nv = L.mv32
    · simp only [hnv_mv, beq_self_eq_true, ite_true]
      have hnv_val : nv.toNat = L.maxV := by rw [hnv_mv, hmv_val]
      refine Or.inr ⟨by change 0 ≤ L.maxV; omega, fun v _ hv => ?_⟩
      have h1 := hvars_lt v (by omega); have h2 := hlits_lt (2 * v) (by omega)
      have h3 := hlits_lt (2 * v + 1) (by omega)
      simp [h1.1, h1.2.1, h1.2.2, h2.1, h3.1, h2.2, h3.2]
    · have hneq : (nv == L.mv32) = false :=
        Bool.eq_false_iff.mpr (fun h => hnv_mv (beq_iff_eq.mp h))
      have hnotlt : ¬ (0xFFFFFFFF#32 : BitVec 32) < nv := by
        change ¬ (0xFFFFFFFF#32 : BitVec 32).toNat < nv.toNat; simp; omega
      simp only [hneq, Bool.false_eq_true, ite_false, hnotlt]
      exact Or.inl rfl
  · have hhw_le : hw.toNat ≤ L.maxV := hhwm.1
    have hcase : lim.toNat ≤ nv.toNat ∧
        (∀ v, lim.toNat ≤ v → v < nv.toNat → hw.toNat ≤ v) ∧
        (nv = L.mv32 → ∀ v, lim.toNat ≤ v → v < L.maxV → hw.toNat ≤ v) ∧
        (nv ≠ L.mv32 → lim = nv) := by
      rw [hlim]; split
      · next h =>
        have h1 := (Bool.and_eq_true _ _).mp h
        have hnv_mv := beq_iff_eq.mp h1.1
        have hnv_val : nv.toNat = L.maxV := by rw [hnv_mv, hmv_val]
        refine ⟨by omega, fun _ hv _ => hv, fun _ _ hv _ => hv, fun hne => absurd hnv_mv hne⟩
      · next h =>
        refine ⟨Nat.le_refl _, fun _ hv0 hv1 => absurd hv0 (by omega), ?_, fun _ => rfl⟩
        intro hnv_mv v hv0 hv1
        rw [hnv_mv, hmv_val] at hv0
        omega
    have hvars : ∀ v < nv.toNat, st.lvlArr[v]? = some 0#32 ∧ st.rsn[v]? = some 0xFFFFFFFF#32 ∧
        st.flags[v]? = some 0#32 := by
      intro v hv
      by_cases hvl : v < lim.toNat
      · exact hvars_lt v hvl
      · have hhwv := hcase.2.1 v (Nat.le_of_not_lt hvl) hv
        have hvmax : v < L.maxV := Nat.lt_of_lt_of_le hv hnv_le
        have hg := hvars_ge v (Nat.le_of_not_lt hvl) hvmax
        have hc := hhwm.2 v hhwv hvmax
        have hv_sz : v < szV L := by unfold szV; omega
        have hl0 : v < ks0.lvlArr.length := hsh0.lvlArr_len.symm ▸ hv_sz
        have hr0 : v < ks0.rsn.length := hsh0.rsn_len.symm ▸ hv_sz
        have hf0 : v < ks0.flags.length := hsh0.flags_len.symm ▸ hv_sz
        rw [List.getElem?_eq_getElem hl0, Option.getD_some,
          List.getElem?_eq_getElem hr0, Option.getD_some,
          List.getElem?_eq_getElem hf0, Option.getD_some] at hc
        exact ⟨hg.1.trans (by rw [List.getElem?_eq_getElem hl0, hc.1]),
          hg.2.1.trans (by rw [List.getElem?_eq_getElem hr0, hc.2.1]),
          hg.2.2.trans (by rw [List.getElem?_eq_getElem hf0, hc.2.2.1])⟩
    have hlits : ∀ l < 2 * nv.toNat,
        st.vals[l]? = some 0#32 ∧ st.whead[l]? = some 0xFFFFFFFF#32 := by
      intro l hl
      by_cases hll : l < 2 * lim.toNat
      · exact hlits_lt l hll
      · have hv_nv : l / 2 < nv.toNat := by omega
        have hhwv := hcase.2.1 (l / 2) (by omega) hv_nv
        have hvmax : l / 2 < L.maxV := Nat.lt_of_lt_of_le hv_nv hnv_le
        have hg := hlits_ge l (Nat.le_of_not_lt hll) (by omega)
        have hc := hhwm.2 (l / 2) hhwv hvmax
        have hl_sz : l < sz2V L := by unfold sz2V; omega
        have hva0 : l < ks0.vals.length := hsh0.vals_len.symm ▸ hl_sz
        have hwh0 : l < ks0.whead.length := hsh0.whead_len.symm ▸ hl_sz
        rcases Nat.mod_two_eq_zero_or_one l with hm2 | hm2
        · have hev : 2 * (l / 2) = l := by omega
          rw [hev, List.getElem?_eq_getElem hva0, Option.getD_some,
            List.getElem?_eq_getElem hwh0, Option.getD_some] at hc
          exact ⟨hg.1.trans (by rw [List.getElem?_eq_getElem hva0, hc.2.2.2.1]),
            hg.2.trans (by rw [List.getElem?_eq_getElem hwh0, hc.2.2.2.2.2.1])⟩
        · have hod : 2 * (l / 2) + 1 = l := by omega
          rw [hod, List.getElem?_eq_getElem hva0, Option.getD_some,
            List.getElem?_eq_getElem hwh0, Option.getD_some] at hc
          exact ⟨hg.1.trans (by rw [List.getElem?_eq_getElem hva0, hc.2.2.2.2.1]),
            hg.2.trans (by rw [List.getElem?_eq_getElem hwh0, hc.2.2.2.2.2.2])⟩
    have hinv_fin := k6Init_finish_inv hsh hnv_le hsc.nv hsc.nc hsc.lvl hsc.prop hsc.trl_end
      hsc.unass hsc.acap (hsc.max_v.trans hmv_nat) hsc.max_orig hsc.max_cl hsc.alen hsc.incons
      hsc.nassump hsc.nkl hsc.nana hvars hlits
    refine ⟨hinv_fin.1, hinv_fin.2, ?_⟩
    have clean_of_ge : ∀ v, lim.toNat ≤ v → hw.toNat ≤ v → v < L.maxV →
        st.lvlArr[v]?.getD 0#32 = 0#32 ∧ st.rsn[v]?.getD 0#32 = 0xFFFFFFFF#32 ∧
        st.flags[v]?.getD 0#32 = 0#32 ∧ st.vals[2 * v]?.getD 0#32 = 0#32 ∧
        st.vals[2 * v + 1]?.getD 0#32 = 0#32 ∧ st.whead[2 * v]?.getD 0#32 = 0xFFFFFFFF#32 ∧
        st.whead[2 * v + 1]?.getD 0#32 = 0xFFFFFFFF#32 := by
      intro v hvl hvw hvm
      have hg := hvars_ge v hvl hvm
      have hl0 := hlits_ge (2 * v) (by omega) (by omega)
      have hl1 := hlits_ge (2 * v + 1) (by omega) (by omega)
      have hc := hhwm.2 v hvw hvm
      exact ⟨by rw [hg.1]; exact hc.1, by rw [hg.2.1]; exact hc.2.1,
        by rw [hg.2.2]; exact hc.2.2.1, by rw [hl0.1]; exact hc.2.2.2.1,
        by rw [hl1.1]; exact hc.2.2.2.2.1, by rw [hl0.2]; exact hc.2.2.2.2.2.1,
        by rw [hl1.2]; exact hc.2.2.2.2.2.2⟩
    by_cases hnv_mv : nv = L.mv32
    · simp only [hnv_mv, beq_self_eq_true, ite_true]
      refine Or.inr ⟨by change 0 ≤ L.maxV; omega, fun v _ hv => ?_⟩
      by_cases hvl : v < lim.toNat
      · have h1 := hvars_lt v hvl; have h2 := hlits_lt (2 * v) (by omega)
        have h3 := hlits_lt (2 * v + 1) (by omega)
        simp [h1.1, h1.2.1, h1.2.2, h2.1, h3.1, h2.2, h3.2]
      · exact clean_of_ge v (Nat.le_of_not_lt hvl)
          (hcase.2.2.1 hnv_mv v (Nat.le_of_not_lt hvl) hv) hv
    · have hlim_nv : lim = nv := hcase.2.2.2 hnv_mv
      have hneq : (nv == L.mv32) = false :=
        Bool.eq_false_iff.mpr (fun h => hnv_mv (beq_iff_eq.mp h))
      simp only [hneq, Bool.false_eq_true, ite_false]
      split
      · next hhw_lt =>
        have hhwv : hw.toNat < nv.toNat := hhw_lt
        exact Or.inr ⟨hnv_le, fun v hv0 hv1 =>
          clean_of_ge v (by rw [hlim_nv]; exact hv0) (by omega) hv1⟩
      · next hhw_ge =>
        have hnv_hw : nv.toNat ≤ hw.toNat := Nat.le_of_not_lt hhw_ge
        exact Or.inr ⟨hhw_le, fun v hv0 hv1 =>
          clean_of_ge v (by rw [hlim_nv]; omega) hv0 hv1⟩

private theorem s13_k6_init_finish_cont {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {L : K6Layout} {nv hw : BitVec 32} {st : K6State} {Q : Post []}
    (hlen : s.LengthsOk c) (hL_len : L.scrLen = c.scratch_cap)
    (hsh : st.ShapesOk L) (hkb : L.k6Base ≤ s.scratch.scratch_buf.length)
    (hfin : (∀ P, K6Inv L P st) ∧ K6TrailSynced st ∧
      K6HwmClean L (if nv == L.mv32 then 0#32 else if hw < nv then nv else hw) st)
    (hsc : S13InitScalar L nv (BitVec.ofNat 32 L.acap) st)
    (hQ : ∀ (scr' gu' : List (BitVec 32)) (m' : Mem 64),
      let ks' := k6StateOfScratch L scr'
      let s' : FullState :=
        { s with scratch := { s.scratch with scratch_buf := scr', glue_used := gu' } }
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      (∀ i < 64, i ≠ 33 → gu'[i]? = s.scratch.glue_used[i]?) →
      (nv.toNat = L.maxV → gu'[33]? = some 0#32) →
      (nv.toNat < L.maxV →
        gu'[33]? = some 0xFFFFFFFF#32 ∨ nv.toNat ≤ (gu'[33]?.getD 0#32).toNat) →
      K6HwmClean L (gu'[33]?.getD 0#32) ks' →
      (∀ P, K6Inv L P ks') → K6TrailSynced ks' →
      ks'.nv = nv → ks'.nc = 0#32 → ks'.lvl = 0#32 → ks'.prop = 0#32 →
      ks'.trl_end = 0#32 → ks'.unass = nv → ks'.incons = 0#32 → ks'.nassump = 0#32 →
      ks'.status = 0#32 → ks'.openCnt = 0#32 → ks'.neq = 0#32 →
      (FullMem c s' ⋆ R) m' → Q () m')
    {gu' : List (BitVec 32)} {mF : Mem 64}
    (hgu_len' : gu'.length = 64)
    (hgu_oth : ∀ i < 64, i ≠ 33 → gu'[i]? = s.scratch.glue_used[i]?)
    (hgu33 : gu'[33]? = some (if nv == L.mv32 then 0#32 else if hw < nv then nv else hw))
    (hmF : (FullMem c { s with scratch := { s.scratch with
      scratch_buf := s.scratch.scratch_buf.take L.k6Base ++ st.toSlab, glue_used := gu' } } ⋆ R)
      mF) :
    Q () mF := by
  let scr' := s.scratch.scratch_buf.take L.k6Base ++ st.toSlab
  have htk_len : (s.scratch.scratch_buf.take L.k6Base).length = L.k6Base :=
    List.length_take_of_le hkb
  have hscr'_len : scr'.length = c.scratch_cap := by
    simp only [scr', List.length_append, htk_len, K6State.toSlab_length hsh, ← hL_len]
    unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed; omega
  have hlen1 := k6_fullState_lengthsOk_scratch hlen hscr'_len
  have hlen' : ({ s with scratch := { s.scratch with
      scratch_buf := scr', glue_used := gu' } } : FullState).LengthsOk c :=
    ⟨hlen1.core_ok, { hlen1.scratch_ok with glue_used_len := hgu_len' }⟩
  have hpre : ∀ x < L.k6Base, scr'[x]? = s.scratch.scratch_buf[x]? := fun x hx => by
    rw [List.getElem?_append_left (by rw [htk_len]; exact hx), List.getElem?_take_of_lt hx]
  have hof : k6StateOfScratch L scr' = st := by
    unfold k6StateOfScratch
    rw [k6_slab_drop_exact _ st.toSlab htk_len]
    exact K6State.ofSlab_toSlab hsh
  have hmv_val : L.mv32.toNat = L.maxV := by
    unfold K6Layout.mv32; have := L.hmaxV; bv_omega
  have hgu_d : gu'[33]?.getD 0#32 =
      if nv == L.mv32 then 0#32 else if hw < nv then nv else hw := by
    rw [hgu33, Option.getD_some]
  refine hQ scr' gu' mF hlen' hpre hgu_oth ?_ ?_ (by rw [hof, hgu_d]; exact hfin.2.2)
    (fun P => by rw [hof]; exact hfin.1 P) (by rw [hof]; exact hfin.2.1)
    (by rw [hof]; exact hsc.nv) (by rw [hof]; exact hsc.nc) (by rw [hof]; exact hsc.lvl)
    (by rw [hof]; exact hsc.prop) (by rw [hof]; exact hsc.trl_end) (by rw [hof]; exact hsc.unass)
    (by rw [hof]; exact hsc.incons) (by rw [hof]; exact hsc.nassump) (by rw [hof]; exact hsc.status)
    (by rw [hof]; exact hsc.openCnt) (by rw [hof]; exact hsc.neq) hmF
  · intro hnv_mv
    have hnv_eq : nv = L.mv32 := BitVec.eq_of_toNat_eq (by rw [hnv_mv, hmv_val])
    rw [hgu33]; simp [hnv_eq]
  · intro hlt
    have hneq : nv ≠ L.mv32 := fun h => by rw [h, hmv_val] at hlt; omega
    have hb : (nv == L.mv32) = false := Bool.eq_false_iff.mpr (fun h => hneq (beq_iff_eq.mp h))
    rw [hgu_d, hb]; simp only [Bool.false_eq_true, ite_false]
    right; split
    · exact Nat.le_refl _
    · next hge => exact Nat.le_of_not_lt hge

private noncomputable def s13_init_ks1 (ks0 : K6State) : K6State :=
  { ks0 with nv := 0#32, nc := 0#32, lvl := 0#32, prop := 0#32, trl_end := 0#32,
             unass := 0#32, incons := 0#32, qfirst := 0#32, qlast := 0#32,
             qsearch := 0#32, qstamp := 0#32, ticks := 0#32, tick_lim := 0#32,
             alen := 0#32, acap := 0#32, nassump := 0#32, nkl := 0#32, nana := 0#32,
             status := 0#32, phase := 0#32, openCnt := 0#32, max_v := 0#32,
             max_orig := 0#32, max_cl := 0#32, neq := 0#32,
             hdrTail := List.replicate 7 0#32 }

private noncomputable def s13_init_ksH (L : K6Layout) (nv acVal : BitVec 32)
    (ks0 : K6State) : K6State :=
  let ksH0 := (((((((s13_init_ks1 ks0).putHdr .nv nv).putHdr .unass nv).putHdr .tick_lim
    16384#32).putHdr .max_v L.mv32).putHdr .max_orig (BitVec.ofNat 32 L.maxOrig)).putHdr .max_cl
    (BitVec.ofNat 32 L.maxCl)).putHdr .acap acVal
  if nv == 0#32 then
    ((ksH0.putHdr .qfirst 0xFFFFFFFF#32).putHdr .qlast 0xFFFFFFFF#32).putHdr .qsearch
      0xFFFFFFFF#32
  else (((ksH0.putHdr .qfirst 0#32).putHdr .qlast (nv - 1#32)).putHdr
    .qsearch (nv - 1#32)).putHdr .qstamp nv

private theorem s13_init_ksH_props {L : K6Layout} {nv acVal : BitVec 32} {ks0 : K6State}
    (hsh1 : (s13_init_ks1 ks0).ShapesOk L) (hac : acVal = BitVec.ofNat 32 L.acap) :
    (s13_init_ksH L nv acVal ks0).ShapesOk L ∧
    S13InitScalar L nv (BitVec.ofNat 32 L.acap) (s13_init_ksH L nv acVal ks0) ∧
    (s13_init_ksH L nv acVal ks0).lvlArr = ks0.lvlArr ∧
    (s13_init_ksH L nv acVal ks0).rsn = ks0.rsn ∧
    (s13_init_ksH L nv acVal ks0).flags = ks0.flags ∧
    (s13_init_ksH L nv acVal ks0).vals = ks0.vals ∧
    (s13_init_ksH L nv acVal ks0).whead = ks0.whead := by
  have hh0 := ((((((hsh1.putHdr .nv nv).putHdr .unass nv).putHdr .tick_lim 16384#32).putHdr
    .max_v L.mv32).putHdr .max_orig (BitVec.ofNat 32 L.maxOrig)).putHdr .max_cl
    (BitVec.ofNat 32 L.maxCl)).putHdr .acap acVal
  unfold s13_init_ksH; split
  · refine ⟨((hh0.putHdr .qfirst _).putHdr .qlast _).putHdr .qsearch _, ?_, rfl, rfl, rfl, rfl, rfl⟩
    dsimp only [s13_init_ks1]
    refine ⟨by k6_field, by k6_field, by k6_field, by k6_field, by k6_field, by k6_field,
      by k6_field, by k6_field, ((by k6_field : _ = acVal).trans hac), by k6_field, by k6_field,
      by k6_field, by k6_field, by k6_field, by k6_field, by k6_field, by k6_field, by k6_field⟩
  · refine ⟨(((hh0.putHdr .qfirst _).putHdr .qlast _).putHdr .qsearch _).putHdr .qstamp _,
      ?_, rfl, rfl, rfl, rfl, rfl⟩
    dsimp only [s13_init_ks1]
    refine ⟨by k6_field, by k6_field, by k6_field, by k6_field, by k6_field, by k6_field,
      by k6_field, by k6_field, ((by k6_field : _ = acVal).trans hac), by k6_field, by k6_field,
      by k6_field, by k6_field, by k6_field, by k6_field, by k6_field, by k6_field, by k6_field⟩

private theorem s13_k6_hdr_zero_mem {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {L : K6Layout} {kPtr : BitVec 64} {ks0 : K6State} {hdrWs : List (BitVec 32)} {m' : Mem 64}
    (hsh0 : ks0.ShapesOk L) (hlen_w : hdrWs.length = 32)
    (hzeros : ∀ j < 32, hdrWs[j]? = some 0#32)
    (hm' : (array (t := i32) kPtr hdrWs ⋆
      ((K6Tree L kPtr ks0).rest (k6Path 0) ⋆ (FullK6Frame c L s ⋆ R))) m') :
    (s13_init_ks1 ks0).ShapesOk L ∧
    (K6MemA L kPtr (s13_init_ks1 ks0) ⋆ (FullK6Frame c L s ⋆ R)) m' := by
  have hrep : hdrWs = List.replicate 32 0#32 := by
    apply List.ext_getElem (by simp [hlen_w]); intro j hj _
    have hj32 : j < 32 := by simp [hlen_w] at hj; exact hj
    have hz := hzeros j hj32
    rw [List.getElem?_eq_getElem (by omega : j < hdrWs.length)] at hz
    rw [List.getElem_replicate]; exact Option.some.inj hz
  rw [hrep] at hm'
  have hsh1 : (s13_init_ks1 ks0).ShapesOk L := { hsh0 with hdrTail_len := by simp [s13_init_ks1] }
  refine ⟨hsh1, k6Mem_to_amem hsh1 (k6Unfocus_hdr (ks := ks0) (ks' := s13_init_ks1 ks0)
    (hdr' := List.replicate 32 0#32) ?_ hm')⟩
  rw [show k6Path 0 = [false, false, false, false] from rfl]
  simp only [K6Mem, K6Tree, SepTree.set, SepTree.eval, k6HdrWords, s13_init_ks1, List.replicate]
  congr 1

private theorem s13_k6_hdr_step_zeros {hdrWs : List (BitVec 32)} {i : BitVec 32}
    (hlen_w : hdrWs.length = 32) (hi_lt : i.toNat < 32)
    (hzeros : ∀ j < i.toNat, hdrWs[j]? = some 0#32) :
    ∀ j < (i + 1#32).toNat, (hdrWs.set i.toNat 0#32)[j]? = some 0#32 := by
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
  rw [hi1]; intro j hj
  by_cases hji : j = i.toNat
  · subst hji; exact List.getElem?_set_self (by rw [hlen_w]; exact hi_lt)
  · rw [List.getElem?_set_ne (Ne.symm hji)]; exact hzeros j (by omega)

/-- Certifies `step13K6InitSpec` for Step-13 `full_k6_init` (`R1` HWM + `L6a` split loops). -/
theorem full_k6_init_s13_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec) :
    ∀ a m Q X, step13K6InitSpec a m Q X → Func.wp Γ full_k6_init_body a m Q X := by
  rintro ⟨hPtr, nv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hret, hcont⟩
  have hsc_lt : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  c0_hsteps_nogrp
  refine s13_k6_maxV_call hMaxV hsc_lt ?_
  have hmv32_toNat :
      ((BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32).toNat = k6MaxV c.scratch_cap := by
    have hbd : k6MaxV c.scratch_cap ≤ 8192 := by
      by_cases hc : c.scratch_cap < k6MinScr
      · rw [k6MaxV_eq_zero hc]; decide
      · exact (k6MaxV_bounds (Nat.le_of_not_lt hc)).2.1
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  c0_hsplit
  · have hcap_lt : c.scratch_cap < k6MinScr := by
      by_cases hc : c.scratch_cap < k6MinScr; · exact hc
      · exfalso; have hb := (k6MaxV_bounds (Nat.le_of_not_lt hc)).1
        have h0 : ((BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32).toNat = 0 := by bv_omega
        omega
    c0_hsteps!; exact hret (Or.inl hcap_lt)
  · have hcap_ge : k6MinScr ≤ c.scratch_cap := by
      by_cases hc : k6MinScr ≤ c.scratch_cap; · exact hc
      · exfalso; have hz := k6MaxV_eq_zero (Nat.lt_of_not_le hc)
        have hne : ((BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32).toNat ≠ 0 := by bv_omega
        omega
    c0_hsplit
    · c0_hsteps!; exact hret (Or.inr (by bv_omega))
    · have hnv_le : nv.toNat ≤ k6MaxV c.scratch_cap := by bv_omega
      obtain ⟨L, hL_len, hL_mv, hhwm, hQ⟩ := hcont hcap_ge hnv_le
      have hmv_eq : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = L.mv32 := by
        unfold K6Layout.mv32; apply BitVec.eq_of_toNat_eq
        rw [hmv32_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := L.hmaxV; omega), ← hL_mv]
      have hgu_len : s.scratch.glue_used.length = 64 := hlen.scratch_ok.glue_used_len
      have hgu33_bd : (33 : BitVec 64).toNat < s.scratch.glue_used.length := by
        rw [hgu_len]; decide
      let hw := s.scratch.glue_used[33]'hgu33_bd
      have hhwm' : K6HwmClean L hw (k6StateOfScratch L s.scratch.scratch_buf) := by
        have hget : s.scratch.glue_used[33]?.getD 0#32 = hw := by
          rw [List.getElem?_eq_getElem (by rw [hgu_len]; decide), Option.getD_some]
        rwa [hget] at hhwm
      c0_hsteps_nogrp
      let lim0 := if nv == L.mv32 && hw.toNat < L.maxV then hw else nv
      refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
        (fun lim => lim = lim0) ?_ ?_
      · rintro _ lim rfl
        have hlim_le : lim0.toNat ≤ nv.toNat := by
          dsimp only [lim0]; split
          · next h =>
            have h1 := (Bool.and_eq_true _ _).mp h
            have hnv_val : nv.toNat = L.maxV := by rw [beq_iff_eq.mp h1.1, k6_mv32_toNat L]
            have hlt : hw.toNat < L.maxV := by simpa using h1.2
            omega
          · exact Nat.le_refl _
        have hlim_mv : lim0.toNat ≤ L.maxV := Nat.le_trans hlim_le (hL_mv ▸ hnv_le)
        let scr := s.scratch.scratch_buf
        have hscr_len : scr.length = L.scrLen := hlen.scratch_ok.scratch_buf_len.trans hL_len.symm
        let ks0 := K6State.ofSlab L (scr.drop L.k6Base)
        have hsh0 : ks0.ShapesOk L := K6State.shapesOk_ofSlab_eq (by
          rw [List.length_drop, hscr_len]; unfold K6Layout.scrLen; omega)
        have hmF : (FullK6Frame c L s ⋆ K6Mem L (L.kPtr c.pScratchBuf) ks0 ⋆ R) m := by
          rw [fullMem_eq_k6Frame hscr_len] at hm; exact sep_ac hm
        clear hm; c0_hsteps_nogrp; rw [hmv_eq, k6_ptr_base L c.pScratchBuf]
        let kPtr := L.kPtr c.pScratchBuf
        have hmHdr : (array (t := i32) kPtr (k6HdrWords ks0) ⋆
            ((K6Tree L kPtr ks0).rest (k6Path 0) ⋆ (FullK6Frame c L s ⋆ R))) m :=
          k6Focus_hdr (sep_ac hmF)
        clear hmF
        refine wp_while_state1 (fun p : BitVec 32 × List (BitVec 32) => p.1)
          (fun p => 32 - p.1.toNat) (fun p m' => p.1.toNat ≤ 32 ∧ p.2.length = 32 ∧
            (∀ j < p.1.toNat, p.2[j]? = some 0#32) ∧
            (array (t := i32) kPtr p.2 ⋆
              ((K6Tree L kPtr ks0).rest (k6Path 0) ⋆ (FullK6Frame c L s ⋆ R))) m') ?_ ?_
        · exact fun J hJ => wp_jump_state
            (proj := fun p : BitVec 32 × List (BitVec 32) => (p.1, ()))
            (0#32, k6HdrWords ks0) rfl
            (hJ _ m ⟨by simp, k6HdrWords_length hsh0, fun _ hj => by simp at hj, hmHdr⟩)
        · rintro J ⟨i, hdrWs⟩ m' ⟨hi_le, hlen_w, hzeros, hm'⟩ ih
          dsimp only at hi_le hlen_w hzeros hm'; c0_hsplit
          · have hi_lt : i.toNat < 32 := by bv_omega
            have hi_w : i.toNat < hdrWs.length := by rw [hlen_w]; exact hi_lt
            c0_hsteps!
            have hsw : (BitVec.setWidth 64 i).toNat = i.toNat := by have := i.isLt; simp; omega
            rw [hsw] at hm
            refine ih (i + 1#32, hdrWs.set i.toNat 0#32) _ (by bv_omega)
              ⟨by bv_omega, by simp [hlen_w], s13_k6_hdr_step_zeros hlen_w hi_lt hzeros, hm⟩
          · have hi_eq : i.toNat = 32 := by bv_omega
            obtain ⟨hsh1, hmA1⟩ :=
              s13_k6_hdr_zero_mem hsh0 hlen_w (fun j hj => hzeros j (by rw [hi_eq]; exact hj)) hm'
            clear hm'; c0_hsteps_nogrp
            have e_acap := s13_k6_acap_val_eq L c.hscr hL_len
            have e_max_orig : L.mv32 * 3#32 = BitVec.ofNat 32 L.maxOrig := by
              have := L.hmaxV; unfold K6Layout.mv32 K6Layout.maxOrig
              apply BitVec.eq_of_toNat_eq; bv_omega
            have e_max_cl : L.mv32 * 4#32 = BitVec.ofNat 32 L.maxCl := by
              have := L.hmaxV; unfold K6Layout.mv32 K6Layout.maxCl
              apply BitVec.eq_of_toNat_eq; bv_omega
            let acVal := ((BitVec.ofNat 64 c.scratch_cap -
              ((1280#32 + (L.mv32 <<< (1 : Nat))) + 32#32 + 38#32 * L.mv32).setWidth 64)).setWidth
                32
            let ksH := s13_init_ksH L nv acVal ks0
            obtain ⟨hshH, hInitH, hksH_arr⟩ := s13_init_ksH_props hsh1 e_acap
            let ac32 := BitVec.ofNat 32 L.acap
            refine wp_join0 (fun m2 => (K6MemA L kPtr ksH ⋆ (FullK6Frame c L s ⋆ R)) m2) ?_ ?_
            · intro _ m2 hm2; c0_hsteps_nogrp
              refine wp_join_state (proj := fun p : BitVec 32 × K6State => (p.1, ()))
                (fun p m3 => S13InitSt L nv ac32 ks0 p.2 lim0.toNat lim0.toNat lim0.toNat 0 0
                  lim0.toNat c s R m3) ?_ ?_
              · rintro _ ⟨_, st3⟩ m3 ⟨hsh3, hsc3, hvp3, hlp3, hm3⟩; c0_hsteps_nogrp
                have hnl_eq : (lim0 <<< (1 : Nat)).toNat = 2 * lim0.toNat := by
                  rw [k6_shl1_toNat]; have := L.hmaxV; omega
                refine wp_while_state1 (fun p : BitVec 32 × K6State => p.1)
                  (fun p => 2 * lim0.toNat - p.1.toNat) (fun p m4 => p.1.toNat ≤ 2 * lim0.toNat ∧
                    S13InitSt L nv ac32 ks0 p.2 lim0.toNat lim0.toNat lim0.toNat p.1.toNat 0
                      lim0.toNat c s R m4) ?_ ?_
                · exact fun Jv hJv => wp_jump_state
                    (proj := fun p : BitVec 32 × K6State => (p.1, ())) (0#32, st3) rfl
                    (hJv _ m3 ⟨by simp, hsh3, hsc3, hvp3, hlp3, hm3⟩)
                · rintro Jv ⟨k, stv⟩ m4 ⟨hk_le, hshv, hscv, hvpv, hlpv, hm4⟩ ihv
                  dsimp only at hk_le hshv hscv hvpv hlpv hm4; c0_hsplit
                  · have hk_lt : k.toNat < 2 * lim0.toNat := by rw [← hnl_eq]; bv_omega
                    have hk_mv2 : k.toNat < sz2V L := by unfold sz2V; omega
                    c0_hsteps!; have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
                    have hps := s13_prefix_step hk_lt (by rw [hshv.vals_len]; exact hk_mv2)
                      (by omega : 2 * lim0.toNat ≤ 2 * L.maxV) hlpv.1 hlpv.2.1
                    refine ihv (k + 1#32, stv.putArr .vals k.toNat 0#32) _
                      (by dsimp only; rw [hk1]; omega)
                      ⟨by rw [hk1]; omega, hshv.putArr .vals _ _, hscv.putArr .vals _ _,
                       s13_varPrefix_putOther hvpv (by decide) _ _,
                       ⟨by rw [hk1]; exact hps.1, hps.2, hlpv.2.2.1, hlpv.2.2.2⟩, hm⟩
                  · have hk_eq : k.toNat = 2 * lim0.toNat := by
                      have hnl : ¬ k.toNat < (lim0 <<< (1 : Nat)).toNat := ‹_›
                      rw [hnl_eq] at hnl; omega
                    rw [hk_eq] at hlpv; c0_hsteps_nogrp
                    refine wp_while_state1 (fun p : BitVec 32 × K6State => p.1)
                      (fun p => 2 * lim0.toNat - p.1.toNat)
                      (fun p m5 => p.1.toNat ≤ 2 * lim0.toNat ∧ S13InitSt L nv ac32 ks0 p.2
                        lim0.toNat lim0.toNat lim0.toNat (2 * lim0.toNat) p.1.toNat lim0.toNat c s R
                        m5) ?_ ?_
                    · exact fun Jw hJw => wp_jump_state
                        (proj := fun p : BitVec 32 × K6State => (p.1, ())) (0#32, stv) rfl
                        (hJw _ m4 ⟨by simp, hshv, hscv, hvpv, hlpv, hm4⟩)
                    · rintro Jw ⟨kw, stw⟩ m5 ⟨hkw_le, hshw, hscw, hvpw, hlpw, hm5⟩ ihw
                      dsimp only at hkw_le hshw hscw hvpw hlpw hm5; c0_hsplit
                      · have hkw_lt : kw.toNat < 2 * lim0.toNat := by rw [← hnl_eq]; bv_omega
                        have hkw_mv2 : kw.toNat < sz2V L := by unfold sz2V; omega
                        c0_hsteps!; have hkw1 : (kw + 1#32).toNat = kw.toNat + 1 := by bv_omega
                        have hps := s13_prefix_step hkw_lt (by rw [hshw.whead_len]; exact hkw_mv2)
                          (by omega : 2 * lim0.toNat ≤ 2 * L.maxV) hlpw.2.2.1 hlpw.2.2.2
                        refine ihw (kw + 1#32, stw.putArr .whead kw.toNat 0xFFFFFFFF#32) _
                          (by dsimp only; rw [hkw1]; omega) ⟨by rw [hkw1]; omega,
                           hshw.putArr .whead _ _, hscw.putArr .whead _ _,
                           s13_varPrefix_putOther hvpw (by decide) _ _,
                           ⟨hlpw.1, hlpw.2.1, by rw [hkw1]; exact hps.1, hps.2⟩, hm⟩
                      · have hkw_eq : kw.toNat = 2 * lim0.toNat := by
                          have hnl : ¬ kw.toNat < (lim0 <<< (1 : Nat)).toNat := ‹_›
                          rw [hnl_eq] at hnl; omega
                        rw [hkw_eq] at hlpw
                        have hfin := s13_k6_init_finish hshw hsh0 (hL_mv ▸ hnv_le) hhwm' rfl
                          hvpw hlpw hscw
                        obtain ⟨_, hm5'⟩ := k6MemA_to_mem hm5
                        have hkb_le : L.k6Base ≤ s.scratch.scratch_buf.length := by
                          change L.k6Base ≤ scr.length; rw [hscr_len]
                          unfold K6Layout.scrLen; omega
                        have hmJ : (FullMem c { s with scratch := { s.scratch with
                              scratch_buf := s.scratch.scratch_buf.take L.k6Base ++ stw.toSlab } }
                            ⋆ R) m5 :=
                          fullMem_join_k6 (c := c) (L := L) (s := s) (ks' := stw) (R := R)
                            hkb_le hshw (sep_ac hm5')
                        have hcontF := @s13_k6_init_finish_cont c s R L nv hw stw Q hlen hL_len
                          hshw hkb_le hfin hscw hQ
                        have h33 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 33) :
                            BitVec 64).toNat = 33 := rfl
                        c0_hsteps_nogrp
                        try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                        try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                        c0_hsplit
                        · c0_hsteps!; erw [h33] at hm
                          let gu1 := s.scratch.glue_used.set 33 0#32
                          have hset : (if nv == L.mv32 then 0#32
                              else if hw < nv then nv else hw) = 0#32 := by simp [‹nv = L.mv32›]
                          have hg1 : gu1[33]? = some (if nv == L.mv32 then 0#32
                              else if hw < nv then nv else hw) := by
                            dsimp only [gu1]
                            rw [List.getElem?_set_self (by rw [hgu_len]; decide), hset]
                          exact hcontF (gu' := gu1) (by simp [gu1, hgu_len])
                            (fun i _ hi => List.getElem?_set_ne (Ne.symm hi)) hg1 hm
                        · have hneq_mv : nv ≠ L.mv32 := ‹_›
                          have hbf : (nv == L.mv32) = false :=
                            Bool.eq_false_iff.mpr (fun h => hneq_mv (beq_iff_eq.mp h))
                          c0_hsteps_nogrp
                          try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                          c0_hsplit
                          · c0_hsteps!; erw [h33] at hm
                            let gu1 := s.scratch.glue_used.set 33 nv
                            have hhw_lt : hw < nv := ‹_›
                            have hset : (if nv == L.mv32 then 0#32
                                else if hw < nv then nv else hw) = nv := by simp [hbf, hhw_lt]
                            have hg1 : gu1[33]? = some (if nv == L.mv32 then 0#32
                                else if hw < nv then nv else hw) := by
                              dsimp only [gu1]
                              rw [List.getElem?_set_self (by rw [hgu_len]; decide), hset]
                            exact hcontF (gu' := gu1) (by simp [gu1, hgu_len])
                              (fun i _ hi => List.getElem?_set_ne (Ne.symm hi)) hg1 hm
                          · c0_hsteps!
                            have hhw_ge : ¬ hw < nv := ‹_›
                            have hset : (if nv == L.mv32 then 0#32
                                else if hw < nv then nv else hw) = hw := by simp [hbf, hhw_ge]
                            exact hcontF hgu_len (fun _ _ _ => rfl)
                              (by rw [List.getElem?_eq_getElem (by rw [hgu_len]; decide), hset])
                              hmJ
              · intro Jlim hJlim; c0_hsplit
                · have hlim_pos : 0 < lim0.toNat := hc
                  c0_hsteps_nogrp
                  refine wp_while_state1 (fun p : BitVec 32 × K6State => p.1)
                    (fun p => lim0.toNat - p.1.toNat) (fun p m3 => p.1.toNat ≤ lim0.toNat ∧
                      S13InitSt L nv ac32 ks0 p.2 p.1.toNat 0 0 0 0 lim0.toNat c s R m3) ?_ ?_
                  · exact fun Jl hJl => wp_jump_state
                      (proj := fun p : BitVec 32 × K6State => (p.1, ())) (0#32, ksH) rfl
                      (hJl _ m2 ⟨by simp, hshH, hInitH,
                        ⟨fun _ h => by simp at h, fun v _ _ => by rw [hksH_arr.1],
                         fun _ h => by simp at h, fun v _ _ => by rw [hksH_arr.2.1],
                         fun _ h => by simp at h, fun v _ _ => by rw [hksH_arr.2.2.1]⟩,
                        ⟨fun _ h => by simp at h, fun l _ _ => by rw [hksH_arr.2.2.2.1],
                         fun _ h => by simp at h, fun l _ _ => by rw [hksH_arr.2.2.2.2]⟩, hm2⟩)
                  · rintro Jl ⟨j1, st1⟩ m3 ⟨hj1_le, hsh1, hsc1, hvp1, hlp1, hm3⟩ ih1
                    dsimp only at hj1_le hsh1 hsc1 hvp1 hlp1 hm3; c0_hsplit
                    · have hj1_lt : j1.toNat < lim0.toNat := by bv_omega
                      have hj1_mv : j1.toNat < szV L := by unfold szV; omega
                      c0_hsteps!; have hj1s : (j1 + 1#32).toNat = j1.toNat + 1 := by bv_omega
                      have hps := s13_prefix_step hj1_lt (by rw [hsh1.lvlArr_len]; exact hj1_mv)
                        hlim_mv hvp1.1 hvp1.2.1
                      refine ih1 (j1 + 1#32, st1.putArr .lvlArr j1.toNat 0#32) _
                        (by dsimp only; rw [hj1s]; omega) ⟨by rw [hj1s]; omega,
                        hsh1.putArr .lvlArr _ _, hsc1.putArr .lvlArr _ _,
                        ⟨by rw [hj1s]; exact hps.1, hps.2, hvp1.2.2.1, hvp1.2.2.2.1,
                         hvp1.2.2.2.2.1, hvp1.2.2.2.2.2⟩,
                        s13_litPrefix_putVar hlp1 (by decide) _ _, hm⟩
                    · have hj1_eq : j1.toNat = lim0.toNat := by bv_omega
                      rw [hj1_eq] at hvp1; c0_hsteps_nogrp
                      refine wp_while_state1 (fun p : BitVec 32 × K6State => p.1)
                        (fun p => lim0.toNat - p.1.toNat) (fun p m4 => p.1.toNat ≤ lim0.toNat ∧
                          S13InitSt L nv ac32 ks0 p.2 lim0.toNat p.1.toNat 0 0 0 lim0.toNat c s R
                            m4) ?_ ?_
                      · exact fun Jr hJr => wp_jump_state
                          (proj := fun p : BitVec 32 × K6State => (p.1, ())) (0#32, st1) rfl
                          (hJr _ m3 ⟨by simp, hsh1, hsc1, hvp1, hlp1, hm3⟩)
                      · rintro Jr ⟨j2, st2⟩ m4 ⟨hj2_le, hsh2, hsc2, hvp2, hlp2, hm4⟩ ih2
                        dsimp only at hj2_le hsh2 hsc2 hvp2 hlp2 hm4; c0_hsplit
                        · have hj2_lt : j2.toNat < lim0.toNat := by bv_omega
                          have hj2_mv : j2.toNat < szV L := by unfold szV; omega
                          c0_hsteps!; have hj2s : (j2 + 1#32).toNat = j2.toNat + 1 := by bv_omega
                          have hps := s13_prefix_step hj2_lt (by rw [hsh2.rsn_len]; exact hj2_mv)
                            hlim_mv hvp2.2.2.1 hvp2.2.2.2.1
                          refine ih2 (j2 + 1#32, st2.putArr .rsn j2.toNat 0xFFFFFFFF#32) _
                            (by dsimp only; rw [hj2s]; omega) ⟨by rw [hj2s]; omega,
                            hsh2.putArr .rsn _ _, hsc2.putArr .rsn _ _, ⟨hvp2.1, hvp2.2.1,
                             by rw [hj2s]; exact hps.1, hps.2, hvp2.2.2.2.2.1, hvp2.2.2.2.2.2⟩,
                            s13_litPrefix_putVar hlp2 (by decide) _ _, hm⟩
                        · have hj2_eq : j2.toNat = lim0.toNat := by bv_omega
                          rw [hj2_eq] at hvp2; c0_hsteps_nogrp
                          refine wp_while_state1 (fun p : BitVec 32 × K6State => p.1)
                            (fun p => lim0.toNat - p.1.toNat)
                            (fun p m5 => p.1.toNat ≤ lim0.toNat ∧ S13InitSt L nv ac32 ks0 p.2
                              lim0.toNat lim0.toNat p.1.toNat 0 0 lim0.toNat c s R m5) ?_ ?_
                          · exact fun Jf hJf => wp_jump_state
                              (proj := fun p : BitVec 32 × K6State => (p.1, ())) (0#32, st2) rfl
                              (hJf _ m4 ⟨by simp, hsh2, hsc2, hvp2, hlp2, hm4⟩)
                          · rintro Jf ⟨j3, st3⟩ m5 ⟨hj3_le, hsh3, hsc3, hvp3, hlp3, hm5⟩ ih3
                            dsimp only at hj3_le hsh3 hsc3 hvp3 hlp3 hm5; c0_hsplit
                            · have hj3_lt : j3.toNat < lim0.toNat := by bv_omega
                              have hj3_mv : j3.toNat < szV L := by unfold szV; omega
                              c0_hsteps!
                              have hj3s : (j3 + 1#32).toNat = j3.toNat + 1 := by bv_omega
                              have hps := s13_prefix_step hj3_lt
                                (by rw [hsh3.flags_len]; exact hj3_mv) hlim_mv
                                hvp3.2.2.2.2.1 hvp3.2.2.2.2.2
                              refine ih3 (j3 + 1#32, st3.putArr .flags j3.toNat 0#32) _
                                (by dsimp only; rw [hj3s]; omega) ⟨by rw [hj3s]; omega,
                                hsh3.putArr .flags _ _, hsc3.putArr .flags _ _,
                                ⟨hvp3.1, hvp3.2.1, hvp3.2.2.1, hvp3.2.2.2.1,
                                 by rw [hj3s]; exact hps.1, hps.2⟩,
                                s13_litPrefix_putVar hlp3 (by decide) _ _, hm⟩
                            · have hj3_eq : j3.toNat = lim0.toNat := by bv_omega
                              rw [hj3_eq] at hvp3; c0_hsteps_nogrp
                              refine wp_while_state1 (fun p : BitVec 32 × K6State => p.1)
                                (fun p => lim0.toNat - p.1.toNat)
                                (fun p m6 => p.1.toNat ≤ lim0.toNat ∧ S13InitSt L nv ac32 ks0 p.2
                                  lim0.toNat lim0.toNat lim0.toNat 0 0 lim0.toNat c s R m6) ?_ ?_
                              · exact fun Jq hJq => wp_jump_state
                                  (proj := fun p : BitVec 32 × K6State => (p.1, ())) (0#32, st3) rfl
                                  (hJq _ m5 ⟨by simp, hsh3, hsc3, hvp3, hlp3, hm5⟩)
                              · rintro Jq ⟨j4, st4⟩ m6 ⟨hj4_le, hsh4, hsc4, hvp4, hlp4, hm6⟩ ih4
                                dsimp only at hj4_le hsh4 hsc4 hvp4 hlp4 hm6; c0_hsplit
                                · have hj4_lt : j4.toNat < lim0.toNat := by bv_omega
                                  have hj4_mv : j4.toNat < szV L := by unfold szV; omega
                                  c0_hsteps!
                                  have hj4s : (j4 + 1#32).toNat = j4.toNat + 1 := by bv_omega
                                  refine ih4 (j4 + 1#32, st4.putArr .qstampArr j4.toNat (j4 + 1#32))
                                    _ (by dsimp only; rw [hj4s]; omega) ⟨by rw [hj4s]; omega,
                                    hsh4.putArr .qstampArr _ _, hsc4.putArr .qstampArr _ _,
                                    s13_varPrefix_putOther hvp4 (by decide) _ _,
                                    s13_litPrefix_putVar hlp4 (by decide) _ _, hm⟩
                                · have h0_mv : 0 < szV L := by unfold szV; omega
                                  c0_hsteps_nogrp
                                  erw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) :
                                      BitVec 64) = (0#32 : BitVec 32).setWidth 64 from rfl]
                                  c0_hsteps!
                                  refine wp_while_state1 (fun p : BitVec 32 × K6State => p.1)
                                    (fun p => lim0.toNat - p.1.toNat)
                                    (fun p m7 => 1 ≤ p.1.toNat ∧ p.1.toNat ≤ lim0.toNat ∧
                                      S13InitSt L nv ac32 ks0 p.2 lim0.toNat lim0.toNat lim0.toNat
                                        0 0 lim0.toNat c s R m7) ?_ ?_
                                  · exact fun Jp hJp => wp_jump_state
                                      (proj := fun p : BitVec 32 × K6State => (p.1, ()))
                                      (1#32, st4.putArr .qprev 0 0xFFFFFFFF#32) rfl
                                      (hJp _ _ ⟨by dsimp only; decide,
                                        by rw [show (1#32 : BitVec 32).toNat = 1 from rfl]; omega,
                                        hsh4.putArr .qprev _ _, hsc4.putArr .qprev _ _,
                                        s13_varPrefix_putOther hvp4 (by decide) _ _,
                                        s13_litPrefix_putVar hlp4 (by decide) _ _, hm⟩)
                                  · rintro Jp ⟨j5, st5⟩ m7
                                      ⟨hj5_ge, hj5_le, hsh5, hsc5, hvp5, hlp5, hm7⟩ ih5
                                    dsimp only at hj5_ge hj5_le hsh5 hsc5 hvp5 hlp5 hm7; c0_hsplit
                                    · have hj5_lt : j5.toNat < lim0.toNat := by bv_omega
                                      have hj5_mv : j5.toNat < szV L := by unfold szV; omega
                                      c0_hsteps!
                                      have hj5s : (j5 + 1#32).toNat = j5.toNat + 1 := by bv_omega
                                      refine ih5 (j5 + 1#32, st5.putArr .qprev j5.toNat (j5 - 1#32))
                                        _ (by dsimp only; rw [hj5s]; omega) ⟨by rw [hj5s]; omega,
                                        by rw [hj5s]; omega, hsh5.putArr .qprev _ _,
                                        hsc5.putArr .qprev _ _,
                                        s13_varPrefix_putOther hvp5 (by decide) _ _,
                                        s13_litPrefix_putVar hlp5 (by decide) _ _, hm⟩
                                    · c0_hsteps_nogrp
                                      refine wp_while_state1 (fun p : BitVec 32 × K6State => p.1)
                                        (fun p => lim0.toNat - p.1.toNat) (fun p m8 =>
                                          p.1.toNat ≤ lim0.toNat ∧ S13InitSt L nv ac32 ks0
                                          p.2 lim0.toNat lim0.toNat lim0.toNat 0 0 lim0.toNat c s R
                                          m8) ?_ ?_
                                      · exact fun Jn hJn => wp_jump_state
                                          (proj := fun p : BitVec 32 × K6State =>
                                            (p.1, ())) (0#32, st5) rfl
                                          (hJn _ m7 ⟨by simp, hsh5, hsc5, hvp5, hlp5, hm7⟩)
                                      · rintro Jn ⟨j6, st6⟩ m8
                                          ⟨hj6_le, hsh6, hsc6, hvp6, hlp6, hm8⟩ ih6
                                        dsimp only at hj6_le hsh6 hsc6 hvp6 hlp6 hm8; c0_hsplit
                                        · have hj6_lt : j6.toNat < lim0.toNat := by bv_omega
                                          have hj6_mv : j6.toNat < szV L := by unfold szV; omega
                                          c0_hsteps!
                                          have hj6s : (j6 + 1#32).toNat = j6.toNat + 1 := by
                                            bv_omega
                                          refine ih6 (j6 + 1#32, st6.putArr .qnext j6.toNat
                                              (j6 + 1#32)) _ (by dsimp only; rw [hj6s]; omega)
                                            ⟨by rw [hj6s]; omega, hsh6.putArr .qnext _ _,
                                             hsc6.putArr .qnext _ _,
                                             s13_varPrefix_putOther hvp6 (by decide) _ _,
                                             s13_litPrefix_putVar hlp6 (by decide) _ _, hm⟩
                                        · c0_hsteps_nogrp
                                          try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                                          try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                                          c0_hsplit
                                          · have hnv_pos : 0 < nv.toNat := by bv_omega
                                            have hqn_mv : (nv - 1).toNat < szV L := by
                                              unfold szV; bv_omega
                                            c0_hsteps_nogrp
                                            try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                                            c0_hsplit
                                            · c0_hsteps!
                                              exact hJlim (_, st6.putArr .qnext (nv - 1).toNat
                                                  0xFFFFFFFF#32) _
                                                ⟨hsh6.putArr .qnext _ _, hsc6.putArr .qnext _ _,
                                                 s13_varPrefix_putOther hvp6 (by decide) _ _,
                                                 s13_litPrefix_putVar hlp6 (by decide) _ _, hm⟩
                                            · c0_hsteps!
                                              exact hJlim (_, st6) _ ⟨hsh6, hsc6, hvp6, hlp6, hm8⟩
                                          · c0_hsteps!
                                            exact hJlim (_, st6) _ ⟨hsh6, hsc6, hvp6, hlp6, hm8⟩
                · have hlim0 : lim0.toNat = 0 := by bv_omega
                  c0_hsteps!
                  exact hJlim (_, ksH) _ ⟨hshH, hInitH,
                    ⟨fun _ hv => absurd hv (by omega), fun v _ _ => by rw [hksH_arr.1],
                     fun _ hv => absurd hv (by omega), fun v _ _ => by rw [hksH_arr.2.1],
                     fun _ hv => absurd hv (by omega), fun v _ _ => by rw [hksH_arr.2.2.1]⟩,
                    ⟨fun _ hv => absurd hv (by omega), fun l _ _ => by rw [hksH_arr.2.2.2.1],
                     fun _ hv => absurd hv (by omega), fun l _ _ => by rw [hksH_arr.2.2.2.2]⟩, hm2⟩
            · intro J2 hJ2; c0_hsteps!
              · refine hJ2 _ (Eq.mp (congrArg (fun x =>
                  (K6MemA L kPtr x ⋆ (FullK6Frame c L s ⋆ R)) _) ?_) hm)
                have hnv0 : nv = 0#32 := by bv_omega
                dsimp only [ksH, s13_init_ksH, s13_init_ks1]; simp only [hnv0, beq_self_eq_true,
                  ite_true]; k6_ext <;> first | exact e_max_orig | exact e_max_cl
              · refine hJ2 _ (Eq.mp (congrArg (fun x =>
                  (K6MemA L kPtr x ⋆ (FullK6Frame c L s ⋆ R)) _) ?_) hm)
                have hne0 : (nv == 0#32) = false :=
                  Bool.eq_false_iff.mpr fun h => absurd (beq_iff_eq.mp h) (by bv_omega)
                dsimp only [ksH, s13_init_ksH, s13_init_ks1]; simp only [hne0, Bool.false_eq_true,
                  ite_false]; k6_ext <;> first | exact e_max_orig | exact e_max_cl
      · intro Jlim hJlim; have hmv_val := k6_mv32_toNat L; c0_hsteps!
        · have h1 : nv = L.mv32 := by rw [← hmv_eq]; assumption
          have h2 : hw.toNat < L.maxV := by
            change s.scratch.glue_used[33].toNat < _; rw [← hmv_val, ← hmv_eq]; assumption
          exact hJlim _ (by dsimp only [lim0]; simp [beq_iff_eq.mpr h1, h2]; rfl)
        · have h1 : nv = L.mv32 := by rw [← hmv_eq]; assumption
          have h2 : ¬ hw.toNat < L.maxV := by
            change ¬ s.scratch.glue_used[33].toNat < _; rw [← hmv_val, ← hmv_eq]; assumption
          exact hJlim _ (by dsimp only [lim0]; simp [beq_iff_eq.mpr h1, h2])
        · have h1 : nv ≠ L.mv32 := by rw [← hmv_eq]; assumption
          exact hJlim _ (by
            dsimp only [lim0]; simp [Bool.eq_false_iff.mpr fun h => h1 (beq_iff_eq.mp h)])

@[local c0_load] private theorem s13_load_glue_used_tail {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ R) m) :
    loadVal m i64 (c.hdr + 432) = some c.pGlueUsed := by
  have h := loadVal_array64 (xs := Full.hdrTailWords c s) (i := 50) (a := c.hdr + 32)
    (by simp [Full.hdrTailWords, Full.hdrTailWords0, Full.hdrTailWords1,
      Full.hdrTailWords2, Full.hdrTailWords3]) hm
  rw [show c.hdr + 32 + BitVec.ofNat 64 (8 * 50) = c.hdr + 432 by bv_omega] at h
  exact h

/-- Certifies `step13K6AddClauseSpec` for Step-13 `full_k6_add_clause` (`R1` `glue_used[33]` HWM
tracking + `full_k6_add_ticks`). -/
theorem full_k6_add_clause_s13_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hAssign : M6EnvSpec Γ "full_k6_assign" k6AssignSpec)
    (hAddTicks : M6EnvSpec Γ "full_k6_add_ticks" k6AddTicksSpec)
    (hWatch : M6EnvSpec Γ "full_k6_watch" k6WatchSpec) :
    ∀ a m Q X, step13K6AddClauseSpec a m Q X → Func.wp Γ full_k6_add_clause_body a m Q X := by
  rintro ⟨hPtr, litsPtr, sz, ⟨⟩⟩ m Q X
    ⟨c, s, P, L, scr, gu, xs, R, rfl, hlen, rfl, rfl, hL_len, hL_mv, hinv, hsync, hlvl0,
     hsz_xs, hsz_max, hxlits, hent, hhwm, hm, hQ⟩
  let scr0 := s.scratch.scratch_buf
  let ks := k6StateOfScratch L scr0
  have hinv : K6Inv L P ks := hinv
  have hsync : K6TrailSynced ks := hsync
  have hlvl0 : ks.lvl = 0#32 := hlvl0
  have hxlits : ∀ i < sz.toNat, (xs[i]?.getD 0#32).toNat < 2 * ks.nv.toNat := hxlits
  have hm_b := L.hmaxV; have hac_b := L.hacap
  have hsh := hinv.shapes; have hnv : ks.nv.toNat ≤ L.maxV := hinv.clauses.nv_le
  have hnc_le : ks.nc.toNat ≤ L.maxCl := hinv.clauses.nc_le
  have hal : ks.alen.toNat ≤ L.acap := hinv.clauses.alen_le
  have hmv_eq_ks : ks.max_v = L.mv32 := hinv.clauses.max_v_eq
  have hmc_eq : ks.max_cl = BitVec.ofNat 32 L.maxCl := hinv.clauses.max_cl_eq
  have hca_eq : ks.acap = BitVec.ofNat 32 L.acap := hinv.clauses.acap_eq
  have hscr_len : scr0.length = L.scrLen := hlen.scratch_ok.scratch_buf_len.trans hL_len.symm
  have hkb_le : L.k6Base ≤ scr0.length := by rw [hscr_len]; unfold K6Layout.scrLen; omega
  have hgu_len : s.scratch.glue_used.length = 64 := hlen.scratch_ok.glue_used_len
  have hgu33_bd : (33 : BitVec 64).toNat < s.scratch.glue_used.length := by rw [hgu_len]; decide
  let hw0 := s.scratch.glue_used[33]'(by rw [hgu_len]; decide)
  have hhwm0 : K6HwmClean L hw0 ks := by
    have hget : s.scratch.glue_used[33]?.getD 0#32 = hw0 := by
      rw [List.getElem?_eq_getElem (by rw [hgu_len]; decide), Option.getD_some]
    rwa [hget] at hhwm
  c0_hsteps_nogrp
  refine wp_join_state (ts := [i32]) (proj := fun p : BitVec 32 × List (BitVec 32) => (p.1, ()))
    (fun (hw', gu') m1 => gu'.length = 64 ∧
      (∀ i < 64, i ≠ 33 → gu'[i]? = s.scratch.glue_used[i]?) ∧ gu'[33]? = some hw' ∧
      K6HwmClean L hw' ks ∧
      (∀ i < sz.toNat, hw' = 0xFFFFFFFF#32 ∨ (xs[i]?.getD 0#32).toNat < 2 * hw'.toNat) ∧
      (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ array (t := i32) c.pScratchBuf scr0 ⋆
        array (t := i32) c.pGlueUsed gu' ⋆ array (t := i32) litsPtr xs ⋆ R) m1) ?_ ?_
  · rintro _ ⟨hw', gu'⟩ m1 ⟨hgu'_len, hgu'_oth, hgu'33, hhwm', hxs_hw', hm1⟩
    let s1 : FullState := { s with scratch := { s.scratch with glue_used := gu' } }
    have hlen1 : s1.LengthsOk c :=
      ⟨hlen.core_ok, { hlen.scratch_ok with glue_used_len := hgu'_len }⟩
    have hgu_d' : gu'[33]?.getD 0#32 = hw' := by rw [hgu'33, Option.getD_some]
    let kPtr := L.kPtr c.pScratchBuf
    let frame : Mem 64 → Prop :=
      array64 (c.hdr + 32) (Full.hdrTailWords c s1) ⋆
      array (t := i32) c.pScratchBuf (scr0.take L.k6Base) ⋆
      array (t := i32) c.pGlueUsed gu'
    have hsc_lt : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
    have hreorg : ∀ {ks' : K6State} {m' : Mem 64}, ks'.ShapesOk L →
        (K6MemA L kPtr ks' ⋆ (frame ⋆ (array (t := i32) litsPtr xs ⋆ R))) m' →
        let scr' := scr0.take L.k6Base ++ ks'.toSlab
        let s' : FullState :=
          { s with scratch := { s.scratch with scratch_buf := scr', glue_used := gu' } }
        s'.LengthsOk c ∧ (∀ i < L.k6Base, scr'[i]? = scr0[i]?) ∧
          (array64 (c.hdr + 32) (Full.hdrTailWords c s') ⋆ array (t := i32) c.pScratchBuf scr' ⋆
            array (t := i32) c.pGlueUsed gu' ⋆ array (t := i32) litsPtr xs ⋆ R) m' := by
      intro ks' m' hsh' hm'
      obtain ⟨_, hm0⟩ := k6MemA_to_mem hm'
      let scr' := scr0.take L.k6Base ++ ks'.toSlab
      have htk_len : (scr0.take L.k6Base).length = L.k6Base := List.length_take_of_le hkb_le
      have hscr'_len : scr'.length = c.scratch_cap := by
        dsimp only [scr']
        rw [List.length_append, htk_len, K6State.toSlab_length hsh', ← hL_len]
        unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed; omega
      have hhdr : Full.hdrTailWords c
          { s with scratch := { s.scratch with scratch_buf := scr', glue_used := gu' } } =
          Full.hdrTailWords c s1 := rfl
      refine ⟨k6_fullState_lengthsOk_scratch hlen1 hscr'_len, fun i hi => by
          rw [List.getElem?_append_left (by rw [htk_len]; exact hi), List.getElem?_take_of_lt hi],
        ?_⟩
      rw [hhdr, ← k6_append_eq_array_scratch htk_len hsh']
      dsimp only [frame] at hm0; exact sep_ac hm0
    have hof_slab : ∀ {ks' : K6State}, ks'.ShapesOk L →
        k6StateOfScratch L (scr0.take L.k6Base ++ ks'.toSlab) = ks' := by
      intro ks' hsh'; unfold k6StateOfScratch
      rw [k6_slab_drop_exact _ ks'.toSlab (List.length_take_of_le hkb_le)]
      exact K6State.ofSlab_toSlab hsh'
    have hscr_orig : scr0.take L.k6Base ++ ks.toSlab = scr0 := by
      have hle : L.k6Fixed ≤ (scr0.drop L.k6Base).length := by
        rw [List.length_drop, hscr_len]; unfold K6Layout.scrLen; omega
      dsimp only [ks, k6StateOfScratch]; rw [K6State.toSlab_ofSlab hle, List.take_append_drop]
    c0_hsteps_nogrp
    have hmA : (K6MemA L kPtr ks ⋆ (frame ⋆ (array (t := i32) litsPtr xs ⋆ R))) m1 := by
      have hhdr1 : Full.hdrTailWords c s1 = Full.hdrTailWords c s := rfl
      rw [array_scratch_eq_k6 hscr_len] at hm1
      dsimp only [frame]; rw [hhdr1]
      exact k6Mem_to_amem hsh (sep_ac hm1)
    dsimp only [frame] at hmA
    clear hm1
    refine s13_k6_maxV_call hMaxV hsc_lt ?_
    have hmv32_eq : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = L.mv32 := by
      rw [← hL_mv]; unfold K6Layout.mv32; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    c0_hsplit
    · exfalso; have hmv0 : L.mv32 = 0#32 := by rw [← hmv32_eq]; exact ‹_›
      have h0 := congrArg BitVec.toNat hmv0
      change (BitVec.ofNat 32 L.maxV).toNat = 0 at h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0; omega
    · rw [hmv32_eq]
      iterate 7 c0_hstep
      rw [k6_ptr_base L c.pScratchBuf]
      c0_hsplit
      · have hsz0 : sz = 0#32 := ‹_›
        have hent0 : SemEntails P [] := by
          have htk : (xs.take sz.toNat).map BitVec.toNat = [] := by rw [hsz0]; simp
          rwa [htk] at hent
        have hunsat : ∀ β, ¬ P β := SemEntails.unsat_of_nil hent0
        c0_hsteps!
        have hinv' := k6SetIncons_preserves_inv hinv hunsat
        have hmF := hreorg hinv'.shapes hm
        exact hQ true _ gu' _ hmF.1 hmF.2.1 hgu'_oth
          (by rw [hof_slab hinv'.shapes, hgu_d']; exact s13_k6_hwm_putHdr_incons hhwm')
          (by rw [hof_slab hinv'.shapes]; exact hinv') (by rw [hof_slab hinv'.shapes]; exact hsync)
          (by rw [hof_slab hinv'.shapes]; k6_field; exact hlvl0)
          (by rw [hof_slab hinv'.shapes]; rfl) (by rw [hof_slab hinv'.shapes]; rfl)
          (by unfold k6AssumpLitsS k6AssumpLits; rw [hof_slab hinv'.shapes]; rfl)
          (fun h => by cases h) (fun h2 => by rw [hsz0] at h2; simp at h2)
          (fun M _ hM htr => by
            rw [hof_slab hinv'.shapes]
            exact ⟨⟨fun c hc => hM.1 c hc, fun w hw => hM.2 w hw⟩, htr⟩) hmF.2.2
      · c0_hsplit
        · have hsz1 : sz = 1#32 := ‹_›
          have h0_xs : 0 < xs.length := by rw [hsz1] at hsz_xs; simp at hsz_xs; omega
          have hu_lt : (xs[0]'h0_xs).toNat < 2 * ks.nv.toNat := by
            have h := hxlits 0 (by rw [hsz1]; decide)
            rwa [List.getElem?_eq_getElem h0_xs, Option.getD_some] at h
          have hu_mv2 : (xs[0]'h0_xs).toNat < sz2V L := by unfold sz2V; omega
          have hent1 : SemEntails P [(xs[0]'h0_xs).toNat] := by
            have htk : (xs.take sz.toNat).map BitVec.toNat = [(xs[0]'h0_xs).toNat] := by
              rw [hsz1]; cases xs with | nil => simp at h0_xs | cons x _ => rfl
            rwa [htk] at hent
          c0_hsteps_nogrp
          try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
          c0_hsplit
          · have hfals : ks.vals[(xs[0]'h0_xs).toNat]? = some 2#32 := by
              have hv_eq : ks.vals[(xs[0]'h0_xs).toNat]?.getD 0#32 = 2#32 := by simpa using ‹_›
              rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hu_mv2),
                Option.getD_some] at hv_eq
              rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hu_mv2), hv_eq]
            have hunsat : ∀ β, ¬ P β := SemEntails.unsat_of_falsified hent1 fun x hx => by
              simp at hx; subst hx; exact (k6_falsified_lvl0_entails hinv hlvl0 hu_lt hfals).2
            c0_hsteps!
            have hinv' := k6SetIncons_preserves_inv hinv hunsat
            have hmF := hreorg hinv'.shapes hm
            exact hQ true _ gu' _ hmF.1 hmF.2.1 hgu'_oth
              (by rw [hof_slab hinv'.shapes, hgu_d']; exact s13_k6_hwm_putHdr_incons hhwm')
              (by rw [hof_slab hinv'.shapes]; exact hinv')
              (by rw [hof_slab hinv'.shapes]; exact hsync)
              (by rw [hof_slab hinv'.shapes]; k6_field; exact hlvl0)
              (by rw [hof_slab hinv'.shapes]; rfl)
              (by rw [hof_slab hinv'.shapes]; rfl)
              (by unfold k6AssumpLitsS k6AssumpLits; rw [hof_slab hinv'.shapes]; rfl)
              (fun h => by cases h) (fun h2 => by rw [hsz1] at h2; simp at h2)
              (fun M _ hM htr => by
                rw [hof_slab hinv'.shapes]
                exact ⟨⟨fun c hc => hM.1 c hc, fun w hw => hM.2 w hw⟩, htr⟩) hmF.2.2
          · try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
            c0_hsplit
            · have hun0 : ks.vals[(xs[0]'h0_xs).toNat]? = some 0#32 := by
                have hv_eq : ks.vals[(xs[0]'h0_xs).toNat]?.getD 0#32 = 0#32 := by simpa using ‹_›
                rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hu_mv2),
                  Option.getD_some] at hv_eq
                rw [List.getElem?_eq_getElem (by rw [hsh.vals_len]; exact hu_mv2), hv_eq]
              have hte_lt := k6_trl_end_lt_of_unassigned hsh hnv hinv.assign hu_lt (by simp [hun0])
              obtain ⟨hinv', hsync'⟩ := k6AssignStep_preserves_inv hinv hsync hu_lt hun0
                (fun _ => hent1) (fun hpos => by rw [hlvl0] at hpos; simp at hpos) (Or.inl rfl)
              have hu_hw : hw' = 0xFFFFFFFF#32 ∨ (xs[0]'h0_xs).toNat < 2 * hw'.toNat := by
                have hh := hxs_hw' 0 (by rw [hsz1]; decide)
                rwa [List.getElem?_eq_getElem h0_xs, Option.getD_some] at hh
              k6_call hAssign
              refine ⟨L, ks, _, hsh, hmv_eq_ks,
                (by change (xs[0]'h0_xs).toNat < 2 * L.maxV; omega),
                (by omega), (k6MemA_to_mem hmA).2, fun m' hm' => ?_⟩
              c0_hsteps!
              have hmF := hreorg hinv'.shapes (k6Mem_to_amem hinv'.shapes hm')
              exact hQ true _ gu' _ hmF.1 hmF.2.1 hgu'_oth
                (by rw [hof_slab hinv'.shapes, hgu_d']; exact s13_k6_hwm_assign hhwm' hu_hw)
                (by rw [hof_slab hinv'.shapes]; exact hinv')
                (by rw [hof_slab hinv'.shapes]; exact hsync')
                (by rw [hof_slab hinv'.shapes]; exact hlvl0)
                (by rw [hof_slab hinv'.shapes]; rfl) (by rw [hof_slab hinv'.shapes]; rfl)
                (by unfold k6AssumpLitsS k6AssumpLits; rw [hof_slab hinv'.shapes]; rfl)
                (fun h => by cases h) (fun h2 => by rw [hsz1] at h2; simp at h2)
                (fun M hxsM hM htr => by
                  rw [hof_slab hinv'.shapes]
                  refine ⟨⟨fun c hc => hM.1 c hc, fun w hw => hM.2 w hw⟩, fun l hl => ?_⟩
                  unfold k6TrailLits k6AssignStep at hl
                  dsimp only [K6State.putHdr, K6State.putArr] at hl
                  have hte1 : (ks.trl_end + 1#32).toNat = ks.trl_end.toNat + 1 := by
                    have := L.hmaxV; bv_omega
                  rw [hte1, List.mem_map] at hl; obtain ⟨b, hb, rfl⟩ := hl
                  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
                  simp only [List.length_take, List.length_set] at hj
                  have hj_lt : j < ks.trl_end.toNat + 1 := by omega
                  simp only [List.getElem_take]
                  by_cases hj_old : j < ks.trl_end.toNat
                  · rw [List.getElem_set_ne (Nat.ne_of_gt hj_old)]
                    have hjm : j < (ks.trl.take ks.trl_end.toNat).length := by
                      rw [List.length_take, hsh.trl_len, Nat.min_eq_left (by omega)]
                      exact hj_old
                    refine htr _ (List.mem_map.mpr ⟨(ks.trl.take ks.trl_end.toNat)[j]'hjm,
                      List.getElem_mem _, by simp only [List.getElem_take]⟩)
                  · have hj_eq : j = ks.trl_end.toNat := by omega
                    subst hj_eq; rw [List.getElem_set_self]
                    have hx0 := hxsM 0 (by rw [hsz1]; decide)
                    rwa [List.getElem?_eq_getElem h0_xs, Option.getD_some] at hx0) hmF.2.2
            · c0_hsteps!; have hmF := hreorg hsh hmA; rw [hscr_orig] at hmF
              exact hQ true scr0 gu' _ hmF.1 (fun _ _ => rfl) hgu'_oth
                (by rw [hgu_d']; exact hhwm') hinv hsync hlvl0 rfl rfl rfl (fun h => by cases h)
                (fun h2 => by rw [hsz1] at h2; simp at h2) (fun _ _ hM htr => ⟨hM, htr⟩) hmF.2.2
        · have hsz2 : 2 ≤ sz.toNat := by
            have hne0 : sz ≠ 0#32 := ‹_›; have hne1 : sz ≠ 1#32 := ‹_›
            have h0 : sz.toNat ≠ 0 := fun h => hne0 (BitVec.eq_of_toNat_eq h)
            have h1 : sz.toNat ≠ 1 := fun h => hne1 (BitVec.eq_of_toNat_eq h); omega
          c0_hsplit
          · c0_hsteps!; have hmF := hreorg hsh hmA; rw [hscr_orig] at hmF
            exact hQ false scr0 gu' _ hmF.1 (fun _ _ => rfl) hgu'_oth
              (by rw [hgu_d']; exact hhwm') hinv hsync hlvl0 rfl rfl rfl (fun _ => rfl)
              (fun _ => ⟨rfl, rfl, rfl, rfl⟩) (fun _ _ hM htr => ⟨hM, htr⟩) hmF.2.2
          · c0_hsplit
            · c0_hsteps!; have hmF := hreorg hsh hmA; rw [hscr_orig] at hmF
              exact hQ false scr0 gu' _ hmF.1 (fun _ _ => rfl) hgu'_oth
                (by rw [hgu_d']; exact hhwm') hinv hsync hlvl0 rfl rfl rfl (fun _ => rfl)
                (fun _ => ⟨rfl, rfl, rfl, rfl⟩) (fun _ _ hM htr => ⟨hM, htr⟩) hmF.2.2
            · have hnc_lt : ks.nc.toNat < L.maxCl := by
                have hmc_n : ks.max_cl.toNat = L.maxCl := by
                  rw [hmc_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
                    unfold K6Layout.maxCl; have := L.hmaxV; omega)]
                bv_omega
              have hoff_fit : ks.alen.toNat + sz.toNat ≤ L.acap := by
                have hcap_n : ks.acap.toNat = L.acap := by
                  rw [hca_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
                    unfold dimacsBound at hac_b; omega)]
                have hal_add : (ks.alen + sz).toNat = ks.alen.toNat + sz.toNat := by
                  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by unfold dimacsBound at hac_b; omega)]
                have hle_bv : (ks.alen + sz).toNat ≤ ks.acap.toNat := by bv_omega
                omega
              obtain ⟨Rfr, hRfr⟩ : ∃ Rfr : Mem 64 → Prop, Rfr = (frame ⋆ R) := ⟨_, rfl⟩
              have hmA_r : (K6MemA L kPtr ks ⋆ (array (t := i32) litsPtr xs ⋆ Rfr)) m1 := by
                rw [hRfr]; dsimp only [frame]; exact sep_ac hmA
              c0_hsteps_nogrp
              refine wp_while_state1 (fun p : BitVec 32 × List (BitVec 32) => p.1)
                (fun p => sz.toNat - p.1.toNat)
                (fun p m' => p.1.toNat ≤ sz.toNat ∧ p.2.length = L.acap ∧
                  (∀ j < ks.alen.toNat, p.2[j]? = ks.arena[j]?) ∧
                  (∀ j < p.1.toNat, p.2[ks.alen.toNat + j]? = xs[j]?) ∧
                  (K6MemA L kPtr { ks with arena := p.2 } ⋆ (array (t := i32) litsPtr xs ⋆ Rfr))
                    m') ?_ ?_
              · intro J hJ
                exact wp_jump_state (proj := fun p : BitVec 32 × List (BitVec 32) => (p.1, ()))
                  (0#32, ks.arena) rfl
                  (hJ _ m1 ⟨by simp, hsh.arena_len, fun _ _ => rfl, fun _ hj => by simp at hj,
                    hmA_r⟩)
              · rintro J ⟨i, ar⟩ m' ⟨hi_le, har_len, har_old, har_new, hm'⟩ ih
                dsimp only at hi_le har_len har_old har_new hm' ⊢
                obtain ⟨st, hst⟩ : ∃ x : K6State, x = { ks with arena := ar } := ⟨_, rfl⟩
                rw [← hst] at hm'
                c0_hsplit
                · have hi_lt : i.toNat < sz.toNat := by bv_omega
                  have hi_xs : i.toNat < xs.length := by omega
                  have hoff_i_ar : (ks.alen + i).toNat < szAr L := by
                    unfold szAr dimacsBound at *; bv_omega
                  c0_hsteps!
                  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
                  have hoi : (ks.alen + i).toNat = ks.alen.toNat + i.toNat := by
                    unfold szAr dimacsBound at *; bv_omega
                  rw [hoi] at hm
                  refine ih (i + 1#32, ar.set (ks.alen.toNat + i.toNat) (xs[i.toNat]'hi_xs)) _
                    (by dsimp only; rw [hi1]; omega)
                    ⟨by dsimp only; rw [hi1]; omega, by simp [har_len],
                     fun j hj => by rw [List.getElem?_set_ne (by omega)]; exact har_old j hj,
                     fun j hj => ?_, ?_⟩
                  · rw [hi1] at hj
                    by_cases hji : j = i.toNat
                    · subst hji; rw [List.getElem?_set_self (by rw [har_len]; omega),
                        List.getElem?_eq_getElem hi_xs]
                    · rw [List.getElem?_set_ne (by omega)]; exact har_new j (by omega)
                  · refine Eq.mp (congrArg (fun x =>
                      (K6MemA L kPtr x ⋆ (array (t := i32) litsPtr xs ⋆ Rfr)) _) ?_) hm
                    rw [hst]; k6_ext
                · have hi_eq : i.toNat = sz.toNat := by bv_omega
                  rw [hi_eq] at har_new
                  have h0_xs : 0 < xs.length := by omega
                  have h1_xs : 1 < xs.length := by omega
                  have hl0_lt : (xs[0]'h0_xs).toNat < 2 * ks.nv.toNat := by
                    have h := hxlits 0 (by omega)
                    rwa [List.getElem?_eq_getElem h0_xs, Option.getD_some] at h
                  have hl1_lt : (xs[1]'h1_xs).toNat < 2 * ks.nv.toNat := by
                    have h := hxlits 1 (by omega)
                    rwa [List.getElem?_eq_getElem h1_xs, Option.getD_some] at h
                  have hl0_hw : hw' = 0xFFFFFFFF#32 ∨ (xs[0]'h0_xs).toNat < 2 * hw'.toNat := by
                    have hh := hxs_hw' 0 (by omega)
                    rwa [List.getElem?_eq_getElem h0_xs, Option.getD_some] at hh
                  have hl1_hw : hw' = 0xFFFFFFFF#32 ∨ (xs[1]'h1_xs).toNat < 2 * hw'.toNat := by
                    have hh := hxs_hw' 1 (by omega)
                    rwa [List.getElem?_eq_getElem h1_xs, Option.getD_some] at hh
                  have hpres := k6AddClause_ge2_preserves hinv hsync hnc_lt hsz2 hsz_max hsz_xs
                    hoff_fit har_len har_old har_new hxlits hent
                  c0_hsteps_nogrp
                  obtain ⟨hshM, hmM⟩ := k6MemA_to_mem hm
                  k6_call hAddTicks
                  refine ⟨L, _, _, hshM, hmM, fun tk' mT hmT => ?_⟩
                  have hshT : ((((st.putHdr .alen (ks.alen + sz)).putArr .clOff ks.nc.toNat
                      ks.alen).putArr .clSz ks.nc.toNat sz).putHdr .nc (ks.nc + 1#32)).putHdr
                      .ticks tk' |>.ShapesOk L := hshM.putHdr .ticks tk'
                  have hmAT := k6Mem_to_amem hshT hmT
                  obtain ⟨_, hmMT⟩ := k6MemA_to_mem hmAT
                  c0_hsteps_nogrp
                  k6_call hWatch
                  refine ⟨L, _, _, hshT, (by rw [hst]; k6_field; exact hmv_eq_ks), hnc_lt,
                    (by change (xs[0]'h0_xs).toNat < 2 * L.maxV; omega),
                    (by change (xs[1]'h1_xs).toNat < 2 * L.maxV; omega),
                    hmMT, fun m2 hm2 => ?_⟩
                  c0_hsteps!
                  let stM0 : K6State := (((({ ks with arena := ar } : K6State).putHdr .alen
                    (ks.alen + sz)).putArr .clOff ks.nc.toNat ks.alen).putArr .clSz ks.nc.toNat
                    sz).putHdr .nc (ks.nc + 1#32)
                  let ksFinal := (k6WatchStep stM0 ks.nc (xs[0]'h0_xs) (xs[1]'h1_xs)).putHdr
                    .ticks tk'
                  have hFinalEq : k6WatchStep (stM0.putHdr .ticks tk') ks.nc
                      (xs[0]'h0_xs) (xs[1]'h1_xs) = ksFinal := rfl
                  have hsh' : ksFinal.ShapesOk L := (k6AddTicks_preserves_inv hpres.1 tk').shapes
                  have hhwmF : K6HwmClean L hw' ksFinal :=
                    s13_k6_hwm_add_ge2_any hhwm' rfl rfl rfl rfl rfl hl0_hw hl1_hw
                  have hm2_eq : (K6Mem L kPtr ksFinal ⋆
                      (array (t := i32) litsPtr xs ⋆ Rfr)) m2 := by
                    rw [← hFinalEq]; rw [hst] at hm2; exact hm2
                  have hmF := hreorg hsh' (by
                    have hA := k6Mem_to_amem hsh' hm2_eq; rw [hRfr] at hA; exact sep_ac hA)
                  have hinvF := k6AddTicks_preserves_inv hpres.1 tk'
                  exact hQ true _ gu' _ hmF.1 hmF.2.1 hgu'_oth
                    (by rw [hof_slab hsh', hgu_d']; exact hhwmF)
                    (by rw [hof_slab hsh']; exact hinvF)
                    (by rw [hof_slab hsh']; exact hpres.2.1)
                    (by rw [hof_slab hsh']; exact hpres.2.2.1.trans hlvl0)
                    (by rw [hof_slab hsh']; exact hpres.2.2.2.1)
                    (by rw [hof_slab hsh']; exact hpres.2.2.2.2.1)
                    (by unfold k6AssumpLitsS k6AssumpLits; rw [hof_slab hsh']
                        dsimp only [ksFinal, k6WatchStep, k6WatchStep0, stM0]
                        try congr 1 <;> first | exact hpres.2.2.2.2.1 | exact hpres.2.2.2.2.2.1)
                    (fun h => by cases h)
                    (fun _ => ⟨by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.1,
                      by rw [hof_slab hsh']
                         dsimp only [ksFinal, k6WatchStep, k6WatchStep0, stM0]; k6_field; rfl,
                      by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.1,
                      by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.1⟩)
                    (fun M hxsM hM htr => by
                      rw [hof_slab hsh']; refine ⟨hpres.2.2.2.2.2.2.2.2.2 M hxsM hM, ?_⟩
                      unfold k6TrailLits
                      dsimp only [ksFinal, k6WatchStep, k6WatchStep0, stM0]; k6_field; exact htr)
                    hmF.2.2
  · intro Jhw hJhw; c0_hsplit
    · have hne : hw0 ≠ 0xFFFFFFFF#32 := by simpa [hw0] using ‹_›
      have hhw0_le : hw0.toNat ≤ L.maxV := by
        rcases hhwm0 with h | h; · exact absurd h hne
        · exact h.1
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i32, i32])
        (fun rem (hwc, xi, ()) mw => xi.toNat ≤ sz.toNat ∧ rem = sz.toNat - xi.toNat ∧
          hwc.toNat ≤ L.maxV ∧ hw0.toNat ≤ hwc.toNat ∧
          (∀ i < xi.toNat, (xs[i]?.getD 0#32).toNat < 2 * hwc.toNat) ∧
          (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ array (t := i32) c.pScratchBuf scr0 ⋆
            array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
            array (t := i32) litsPtr xs ⋆ R) mw) ?_ ?_
      · rintro Jx rem ⟨hwc, xi, ⟨⟩⟩ mw hJx ⟨hxi_le, rfl, hwc_le, hwc_ge, hxi_lt, hmw⟩; c0_hsplit
        · have hxi_sz : xi.toNat < sz.toNat := by bv_omega
          have hxi_xs : xi.toNat < xs.length := by omega
          have hlit_nv : (xs[xi.toNat]'hxi_xs).toNat < 2 * ks.nv.toNat := by
            have h := hxlits xi.toNat hxi_sz
            rwa [List.getElem?_eq_getElem hxi_xs, Option.getD_some] at h
          have hxv_val : ((xs[xi.toNat]'hxi_xs >>> (1 : Nat)) + 1#32).toNat =
              (xs[xi.toNat]'hxi_xs).toNat / 2 + 1 := by
            rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
            simp only [Nat.reducePow, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
          c0_hsteps!; have hxi1 : (xi + 1#32).toNat = xi.toNat + 1 := by bv_omega
          c0_hsplit
          · let xv := (xs[xi.toNat]'hxi_xs >>> (1 : Nat)) + 1#32
            have hxv_gt : hwc.toNat < xv.toNat := ‹_›
            c0_hsteps!
            have hxv_le_max : xv.toNat ≤ L.maxV := by
              have hnv_k : ks.nv.toNat ≤ L.maxV := hnv
              dsimp only [ks, scr0] at hlit_nv hnv_k; dsimp only [xv]; rw [hxv_val]; omega
            refine hJx (sz.toNat - (xi + 1#32).toNat) (xv, xi + 1#32, ()) _
              (by rw [hxi1]; omega)
              ⟨by rw [hxi1]; omega, rfl, hxv_le_max, by omega, fun i hi => ?_, sep_ac hmw⟩
            rw [hxi1] at hi
            by_cases hix : i = xi.toNat
            · subst hix; rw [List.getElem?_eq_getElem hxi_xs, Option.getD_some]
              dsimp only [xv]; rw [hxv_val]; omega
            · exact Nat.lt_trans (hxi_lt i (by omega)) (by omega)
          · have hxv_le : ((xs[xi.toNat]'hxi_xs >>> (1 : Nat)) + 1#32).toNat ≤ hwc.toNat :=
              Nat.le_of_not_lt hc
            c0_hsteps!
            have hxi1 : (xi + 1#32).toNat = xi.toNat + 1 := by bv_omega
            refine hJx (sz.toNat - (xi + 1#32).toNat) (hwc, xi + 1#32, ()) _
              (by rw [hxi1]; omega)
              ⟨by rw [hxi1]; omega, rfl, hwc_le, hwc_ge, fun i hi => ?_, sep_ac hmw⟩
            rw [hxi1] at hi
            by_cases hix : i = xi.toNat
            · subst hix; rw [List.getElem?_eq_getElem hxi_xs, Option.getD_some]
              rw [hxv_val] at hxv_le; omega
            · exact hxi_lt i (by omega)
        · have hxi_eq : xi.toNat = sz.toNat := by bv_omega
          rw [hxi_eq] at hxi_lt; c0_hsteps!
          have h33 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 33) : BitVec 64).toNat = 33 := rfl
          erw [h33] at hm
          have hhdr_g : Full.hdrTailWords c s =
              Full.hdrTailWords c
                { s with scratch :=
                  { s.scratch with glue_used := s.scratch.glue_used.set 33 hwc } } :=
            rfl
          rw [hhdr_g] at hm
          exact hJhw (hwc, s.scratch.glue_used.set 33 hwc) _
            ⟨by simp [hgu_len], fun i _ hi => List.getElem?_set_ne (Ne.symm hi),
             List.getElem?_set_self (by rw [hgu_len]; decide),
             s13_k6_hwm_weaken hhwm0 hwc_ge hwc_le, fun i hi => Or.inr (hxi_lt i hi), sep_ac hm⟩
      · intro Jx hJx; c0_hsteps!
        exact hJx sz.toNat (hw0, 0#32, ()) m
          ⟨by simp, by simp, hhw0_le, Nat.le_refl _, fun _ h => by simp at h, sep_ac hm⟩
    · have heq : hw0 = 0xFFFFFFFF#32 := by simpa [hw0] using ‹_›
      c0_hsteps!; exact hJhw (hw0, s.scratch.glue_used) _ ⟨hgu_len, fun _ _ _ => rfl,
        by rw [List.getElem?_eq_getElem (by rw [hgu_len]; decide)],
        hhwm0, fun _ _ => Or.inl heq, sep_ac hm⟩

end S13CoreInitAddProof

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1