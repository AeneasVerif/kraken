module

public import LeanQbe.T.LeanLCNF.LcnfC0Rt
public import LeanQbe.T.LeanLCNF.LcnfC0StringsSpec
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof1
public import LeanQbe.T.Logic.C0Step
import all Kraken.Separation

/-!
# Allocator Rem-Progress Proof for `LcnfC0Strings`

Proves `lcnf_alloc_rem_wp : lcnfAllocRemSpec xs m Q X → Func.wp Γ lcnf_alloc_body xs m Q X`
directly from `LcnfC0Rt.lcnf_alloc_body` without editing `LcnfC0Rt*`, establishing both the
upper bound `st'.rem ≤ st.rem` and the lower bound `st.rem - bytes ≤ st'.rem` needed by
multi-allocation functions (`lcnf_string_to_list`, `lcnf_array_to_list`, `lcnf_nat_to_str`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T
open LeanQbe.T.C0Step
open Std.ExtHashMap

private theorem align8_bv_eq (sz : BitVec 64) (h : sz.toNat ≤ 268435448) :
    ((sz + 7) &&& 18446744073709551608) = BitVec.ofNat 64 (align8 sz.toNat) := by
  have hbits : ∀ (x : BitVec 64), x &&& (18446744073709551608 : BitVec 64) = ((x >>> 3) <<< 3) := by
    intro x
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    have hm : (18446744073709551608 : BitVec 64).getLsbD i = decide (3 ≤ i) := by
      revert i
      decide
    rw [hm]
    by_cases h3 : i < 3
    · have hnot : ¬ (3 ≤ i) := by omega
      simp [h3, hnot]
    · have h3le : 3 ≤ i := by omega
      simp [h3le, hi, h3]
  rw [hbits (sz + 7)]
  apply BitVec.eq_of_toNat_eq
  have h7 : (7 : BitVec 64).toNat = 7 := rfl
  have hlt : sz.toNat + 7 < 2 ^ 64 := by omega
  have ha : (sz.toNat + 7) / 8 * 8 < 2 ^ 64 := by unfold align8 at *; omega
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_add, h7,
    Nat.mod_eq_of_lt hlt, BitVec.toNat_ofNat]
  unfold align8
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    show (2 ^ 3 : Nat) = 8 from rfl, Nat.mod_eq_of_lt ha]

@[c0_load] private theorem c0_load_cell64_8 {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 (a + 8#64) v ⋆ R) m) : loadVal m i64 (a + 8) = some v :=
  loadVal_cell64 h

@[c0_load] private theorem c0_load_cell64_16 {a v : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (cell64 (a + 16#64) v ⋆ R) m) : loadVal m i64 (a + 16) = some v :=
  loadVal_cell64 h

@[c0_store] private theorem c0_store_cell64_8 {a v0 v : BitVec 64} {R : Mem 64 → Prop}
    {m : Mem 64} (h : (cell64 (a + 8#64) v0 ⋆ R) m) :
    storeOk m i64 (a + 8) ∧ (cell64 (a + 8#64) v ⋆ R) (storeMem m i64 (a + 8) v) :=
  store_cell64 v h

@[c0_load] private theorem c0_load_rt_fl {rt i : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 (rt + 33024#64) xs ⋆ R) m)
    (hi : i.toNat < xs.length) :
    loadVal m i64 (rt + 33024 + i * 8) = some xs[i.toNat] := by
  have heq : rt + 33024 + i * 8 = (rt + 33024#64) + BitVec.ofNat 64 (8 * i.toNat) := by
    rw [show (33024 : BitVec 64) = 33024#64 from rfl]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have h8 : (8 : BitVec 64).toNat = 8 := rfl
    rw [BitVec.toNat_mul, h8, BitVec.toNat_ofNat, Nat.mul_comm i.toNat 8]
  rw [heq]
  exact loadVal_array64 hi h

@[c0_store] private theorem c0_store_rt_fl {rt i v : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (array64 (rt + 33024#64) xs ⋆ R) m)
    (hi : i.toNat < xs.length) :
    storeOk m i64 (rt + 33024 + i * 8) ∧
      (array64 (rt + 33024#64) (xs.set i.toNat v) ⋆ R)
        (storeMem m i64 (rt + 33024 + i * 8) v) := by
  have heq : rt + 33024 + i * 8 = (rt + 33024#64) + BitVec.ofNat 64 (8 * i.toNat) := by
    rw [show (33024 : BitVec 64) = 33024#64 from rfl]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have h8 : (8 : BitVec 64).toNat = 8 := rfl
    rw [BitVec.toNat_mul, h8, BitVec.toNat_ofNat, Nat.mul_comm i.toNat 8]
  rw [heq]
  exact store_array64 v hi h

private theorem align8_div8_eq (sz : BitVec 64) (h : sz.toNat ≤ 268435448) :
    (((sz + 7) &&& 18446744073709551608) >>> 3) =
      BitVec.ofNat 64 (align8 sz.toNat / 8) := by
  rw [align8_bv_eq sz h]
  apply BitVec.eq_of_toNat_eq
  unfold align8
  have ha : (sz.toNat + 7) / 8 * 8 < 2 ^ 64 := by omega
  have hd : (sz.toNat + 7) / 8 * 8 / 8 = (sz.toNat + 7) / 8 := by omega
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.shiftRight_eq_div_pow, hd,
    Nat.mod_eq_of_lt (by omega : (sz.toNat + 7) / 8 < 2 ^ 64)]

private theorem align8_div8_mul8 {n : Nat} (h : n % 8 = 0) : 8 * (n / 8) = n := by omega

private theorem align8_ge_self (n : Nat) : n ≤ align8 n := by unfold align8; omega

private theorem list_getD_set_self (xs : List (BitVec 64)) (v d : BitVec 64) {i : Nat}
    (hi : i < xs.length) : (xs.set i v).getD i d = v := by
  simp [List.getD, hi]

private theorem list_getD_set_ne (xs : List (BitVec 64)) (v d : BitVec 64) {i j : Nat}
    (hne : j ≠ i) : (xs.set i v).getD j d = xs.getD j d := by
  simp only [List.getD]
  rw [List.getElem?_set_ne hne.symm]

private theorem smallPoolsAt_pop {fl : List (BitVec 64)} {pools : Nat → List (BitVec 64)}
    {cls : Nat} {Q : Mem 64 → Prop} {m : Mem 64}
    (hfl : fl.length = rtNumClasses) (h2 : 2 ≤ cls) (hlt : cls < rtNumClasses)
    (hne : fl[cls]'(by rw [hfl]; exact hlt) ≠ 0#64)
    (hm : (smallPoolsAt fl pools rtNumClasses ⋆ Q) m) :
    ∃ rest, pools cls = fl[cls]'(by rw [hfl]; exact hlt) :: rest ∧
      (fl[cls]'(by rw [hfl]; exact hlt)).toNat % 8 = 0 ∧
      ((((region (fl[cls]'(by rw [hfl]; exact hlt)) 8 ⋆
        cell64 (fl[cls]'(by rw [hfl]; exact hlt) + 8#64) (listHeadPtr rest)) ⋆
        region (fl[cls]'(by rw [hfl]; exact hlt) + 16#64) (8 * cls - 16)) ⋆
        smallFreeList (8 * cls) (listHeadPtr rest) rest ⋆
        smallPoolsExcl cls fl pools rtNumClasses) ⋆ Q) m := by
  rw [smallPoolsAt_split rtNumClasses fl pools hlt] at hm
  have hget : fl.getD cls 0#64 = fl[cls]'(by rw [hfl]; exact hlt) := by
    simp [List.getD, show cls < fl.length by rw [hfl]; exact hlt]
  rw [hget] at hm
  have hslot : smallPoolSlot cls (fl[cls]'(by rw [hfl]; exact hlt)) (pools cls) =
      smallFreeList (8 * cls) (fl[cls]'(by rw [hfl]; exact hlt)) (pools cls) := by
    simp [smallPoolSlot, h2]
  rw [hslot] at hm
  cases hpc : pools cls with
  | nil =>
    rw [hpc] at hm
    rcases hm with ⟨m1, m2, rfl, hd, h1, _⟩
    rcases h1 with ⟨m11, _, rfl, _, hzero, _⟩
    rcases hzero with ⟨heq, _⟩
    exact absurd heq hne
  | cons hdNode rest =>
    rw [hpc] at hm
    refine ⟨rest, ?_, ?_, ?_⟩
    · rcases hm with ⟨_, _, rfl, _, h1, _⟩
      rcases h1 with ⟨m11, _, rfl, _, hnd, _⟩
      rcases hnd with ⟨hnext, _⟩
      exact congrArg (· :: rest) hnext.symm
    · rcases hm with ⟨_, _, rfl, _, h1, _⟩
      rcases h1 with ⟨m11, _, rfl, _, hnd, _⟩
      rcases hnd with ⟨hnext, _, halign, _⟩
      rw [hnext]; exact halign
    · rcases hm with ⟨m1, m2, rfl, hd, h1, h2'⟩
      rcases h1 with ⟨m11, m12, rfl, hd1, hflst, hexcl⟩
      rcases hflst with ⟨hnext, _, _, hmem⟩
      rw [← hnext] at hmem
      unfold smallFreeNode at hmem
      have hAll : (((((region fl[cls] 8 ⋆ cell64 (fl[cls] + 8#64) (listHeadPtr rest)) ⋆
            region (fl[cls] + 16#64) (8 * cls - 16)) ⋆
          smallFreeList (8 * cls) (listHeadPtr rest) rest) ⋆
          smallPoolsExcl cls fl pools rtNumClasses) ⋆ Q) ((m11.union m12).union m2) :=
        ⟨m11.union m12, m2, rfl, hd, ⟨m11, m12, rfl, hd1, hmem, hexcl⟩, h2'⟩
      exact sep_cast hAll (by ac_rfl)

private theorem smallPoolsAt_zero_empty {fl : List (BitVec 64)} {pools : Nat → List (BitVec 64)}
    {cls : Nat} {Q : Mem 64 → Prop} {m : Mem 64}
    (hfl : fl.length = rtNumClasses) (h2 : 2 ≤ cls) (hlt : cls < rtNumClasses)
    (hz : fl[cls]'(by rw [hfl]; exact hlt) = 0#64)
    (hm : (smallPoolsAt fl pools rtNumClasses ⋆ Q) m) : pools cls = [] := by
  rw [smallPoolsAt_split rtNumClasses fl pools hlt] at hm
  have hget : fl.getD cls 0#64 = 0#64 := by
    simp [List.getD, show cls < fl.length by rw [hfl]; exact hlt, hz]
  rw [hget] at hm
  have hslot : smallPoolSlot cls 0#64 (pools cls) =
      smallFreeList (8 * cls) 0#64 (pools cls) := by simp [smallPoolSlot, h2]
  rw [hslot] at hm
  cases hpc : pools cls with
  | nil => rfl
  | cons _ _ =>
    rw [hpc] at hm
    rcases hm with ⟨_, _, rfl, _, ⟨_, _, rfl, _, ⟨hnext, hnz, _⟩, _⟩, _⟩
    exact absurd hnext.symm hnz

private theorem smallPoolsAt_pop_head {fl fl' : List (BitVec 64)}
    {pools pools' : Nat → List (BitVec 64)} {cls : Nat} {nxt : BitVec 64}
    {rest : List (BitVec 64)} {Q : Mem 64 → Prop} {m : Mem 64}
    (hlt : cls < rtNumClasses) (h2 : 2 ≤ cls)
    (hget : fl'.getD cls 0#64 = nxt) (hpcls : pools' cls = rest) (_hnxt : nxt = listHeadPtr rest)
    (hfl : ∀ i, i ≠ cls → fl'.getD i 0#64 = fl.getD i 0#64)
    (hp : ∀ i, i ≠ cls → pools' i = pools i)
    (h : ((smallFreeList (8 * cls) nxt rest ⋆
      smallPoolsExcl cls fl pools rtNumClasses) ⋆ Q) m) :
    (smallPoolsAt fl' pools' rtNumClasses ⋆ Q) m := by
  have hslotEq : smallFreeList (8 * cls) nxt rest = smallPoolSlot cls nxt rest := by
    simp [smallPoolSlot, h2]
  rw [hslotEq, ← hget, ← hpcls] at h
  rw [← smallPoolsExcl_update fl fl' pools pools' hfl hp] at h
  rwa [← smallPoolsAt_split rtNumClasses fl' pools' hlt] at h

private theorem bump_curLeEnd {cur sEnd : BitVec 64} {bytes : Nat}
    (hle : cur.toNat ≤ sEnd.toNat) (hmax : bytes < rtMaxObjBytes)
    (hrem : bytes ≤ sEnd.toNat - cur.toNat) :
    (cur + BitVec.ofNat 64 bytes).toNat ≤ sEnd.toNat := by
  have := sEnd.isLt
  have hlt : cur.toNat + bytes < 2 ^ 64 := by omega
  have hmod : (BitVec.ofNat 64 bytes).toNat = bytes := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)]
  rw [BitVec.toNat_add, hmod, Nat.mod_eq_of_lt hlt]
  omega

private theorem bump_cur_align {cur : BitVec 64} {bytes : Nat}
    (hal : cur.toNat % 8 = 0) {sEnd : BitVec 64} (hle : cur.toNat ≤ sEnd.toNat)
    (hrem : bytes ≤ sEnd.toNat - cur.toNat) (hmod : bytes % 8 = 0) :
    (cur + BitVec.ofNat 64 bytes).toNat % 8 = 0 := by
  have := sEnd.isLt
  have hlt : cur.toNat + bytes < 2 ^ 64 := by omega
  have hb : (BitVec.ofNat 64 bytes).toNat = bytes := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, hb, Nat.mod_eq_of_lt hlt]
  omega

private theorem bump_cur_nz {cur : BitVec 64} (hnz : cur ≠ 0#64) {sEnd : BitVec 64}
    (hle : cur.toNat ≤ sEnd.toNat) {bytes : Nat} (hrem : bytes ≤ sEnd.toNat - cur.toNat) :
    cur + BitVec.ofNat 64 bytes ≠ 0#64 := by
  intro heq
  have hlt : cur.toNat + bytes < 2 ^ 64 := by have := sEnd.isLt; omega
  have hb : (BitVec.ofNat 64 bytes).toNat = bytes := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hto := congrArg BitVec.toNat heq
  have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
  rw [BitVec.toNat_add, hb, Nat.mod_eq_of_lt hlt, h0] at hto
  apply hnz
  exact BitVec.eq_of_toNat_eq (by rw [h0]; omega)

private theorem bump_rem_eq {cur sEnd : BitVec 64} {bytes : Nat}
    (hle : cur.toNat ≤ sEnd.toNat) (hmax : bytes < rtMaxObjBytes)
    (hrem : bytes ≤ sEnd.toNat - cur.toNat) :
    sEnd.toNat - (cur + BitVec.ofNat 64 bytes).toNat = sEnd.toNat - cur.toNat - bytes := by
  have := sEnd.isLt
  have hlt : cur.toNat + bytes < 2 ^ 64 := by omega
  have hmod : (BitVec.ofNat 64 bytes).toNat = bytes := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)]
  rw [BitVec.toNat_add, hmod, Nat.mod_eq_of_lt hlt]
  omega

private theorem rem_of_not_gt {cur sEnd : BitVec 64} {bytes : Nat}
    (hle : cur.toNat ≤ sEnd.toNat) (hmax : bytes < rtMaxObjBytes)
    (hnot : ¬ BitVec.toNat (sEnd - cur) < (BitVec.ofNat 64 bytes).toNat) :
    bytes ≤ sEnd.toNat - cur.toNat := by
  rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)] at hnot
  omega

private def largeSegSplit (hd prev lcur : BitVec 64)
    (pfx sfx : List (BitVec 64 × Nat)) (m : Mem 64) : Prop :=
  lcur = largeSegNext 0#64 sfx ∧
  match pfx.reverse with
  | [] => prev = 0#64 ∧ hd = lcur ∧ largeSeg hd 0#64 sfx m
  | (prv, prvB) :: revMid =>
    prev = prv ∧ prv ≠ 0#64 ∧ prv.toNat % 8 = 0 ∧ 512 ≤ prvB ∧ prvB < rtMaxObjBytes ∧
    prvB % 8 = 0 ∧
    ((largeSeg hd prv revMid.reverse ⋆ largeFreeNode prvB prv lcur) ⋆
      largeSeg lcur 0#64 sfx) m

private theorem largeSegSplit_init {hd : BitVec 64} {nodes : List (BitVec 64 × Nat)} {m : Mem 64}
    (h : largeFreeList hd nodes m) : largeSegSplit hd 0#64 hd [] nodes m :=
  ⟨largeSeg_hd_eq_next h, rfl, rfl, h⟩

private theorem largeSegSplit_nil {hd prev : BitVec 64}
    {pfx : List (BitVec 64 × Nat)} {m : Mem 64}
    (h : largeSegSplit hd prev 0#64 pfx [] m) : largeFreeList hd pfx m := by
  rcases h with ⟨_, hs⟩
  cases hr : pfx.reverse with
  | nil =>
    rw [hr] at hs
    have hp : pfx = [] := List.reverse_eq_nil_iff.mp hr
    subst hp
    exact hs.2.2
  | cons hdRev tlRev =>
    rw [hr] at hs
    rcases hdRev with ⟨prv, prvB⟩
    rcases hs with ⟨_, hnz, hal, hlo, hhi, hmod, hmem⟩
    have hp : pfx = tlRev.reverse ++ [(prv, prvB)] := by
      rw [← List.reverse_reverse pfx, hr]; simp
    rw [hp]
    change ((largeSeg hd prv tlRev.reverse ⋆ largeFreeNode prvB prv 0#64) ⋆
      (fun m => 0#64 = 0#64 ∧ emp m)) m at hmem
    rw [sep_comm, sep_pure_l, emp_sep] at hmem
    exact largeSeg_split_snoc hnz hal hlo hhi hmod tlRev.reverse hmem.2

private theorem largeSegSplit_step {hd prev lcur nxt : BitVec 64} {b : Nat}
    {pfx rest : List (BitVec 64 × Nat)} {m : Mem 64}
    (hcur : lcur ≠ 0#64) (hal : lcur.toNat % 8 = 0)
    (hlo : 512 ≤ b) (hhi : b < rtMaxObjBytes) (hmod : b % 8 = 0)
    (hnxt : nxt = largeSegNext 0#64 rest)
    (hpfx : match pfx.reverse with
      | [] => prev = 0#64 ∧ hd = lcur ∧
        (largeFreeNode b lcur nxt ⋆ largeSeg nxt 0#64 rest) m
      | (prv, prvB) :: revMid =>
        prev = prv ∧ prv ≠ 0#64 ∧ prv.toNat % 8 = 0 ∧ 512 ≤ prvB ∧ prvB < rtMaxObjBytes ∧
        prvB % 8 = 0 ∧
        ((largeSeg hd prv revMid.reverse ⋆ largeFreeNode prvB prv lcur) ⋆
          (largeFreeNode b lcur nxt ⋆ largeSeg nxt 0#64 rest)) m) :
    largeSegSplit hd lcur nxt (pfx ++ [(lcur, b)]) rest m := by
  refine ⟨hnxt, ?_⟩
  have hrev : (pfx ++ [(lcur, b)]).reverse = (lcur, b) :: pfx.reverse := by simp
  rw [hrev]
  dsimp only
  rw [List.reverse_reverse]
  refine ⟨rfl, hcur, hal, hlo, hhi, hmod, ?_⟩
  cases hr : pfx.reverse with
  | nil =>
    rw [hr] at hpfx
    have hp : pfx = [] := List.reverse_eq_nil_iff.mp hr
    subst hp
    rcases hpfx with ⟨_, heq, hmem⟩
    subst heq
    change ((largeSeg hd hd [] ⋆ largeFreeNode b hd nxt) ⋆ largeSeg nxt 0#64 rest) m
    refine sep_mono (fun _ hx => ?_) hmem
    change ((fun m => hd = hd ∧ emp m) ⋆ largeFreeNode b hd nxt) _
    rw [sep_pure_l, emp_sep]
    exact ⟨rfl, hx⟩
  | cons hdRev tlRev =>
    rw [hr] at hpfx
    rcases hdRev with ⟨prv, prvB⟩
    rcases hpfx with ⟨_, hnz, halp, hlop, hhip, hmodp, hmem⟩
    have hp : pfx = tlRev.reverse ++ [(prv, prvB)] := by
      rw [← List.reverse_reverse pfx, hr]; simp
    rw [← sep_assoc] at hmem
    refine sep_mono (fun _ hx => sep_mono (fun _ hy => ?_) hx) hmem
    rw [hp]
    exact largeSeg_split_snoc hnz halp hlop hhip hmodp tlRev.reverse hy

private theorem largeSegSplit_sfx_nil_of_zero {hd prev : BitVec 64}
    {pfx sfx : List (BitVec 64 × Nat)} {m : Mem 64}
    (h : largeSegSplit hd prev 0#64 pfx sfx m) : sfx = [] := by
  rcases h with ⟨hnext, hs⟩
  cases sfx with
  | nil => rfl
  | cons x rest =>
    rcases x with ⟨p, b⟩
    dsimp only [largeSegNext] at hnext
    cases hr : pfx.reverse with
    | nil =>
      rw [hr] at hs
      rcases hs with ⟨_, _, hseg⟩
      rcases hseg with ⟨_, hnz, _⟩
      exact absurd hnext.symm hnz
    | cons _ _ =>
      rw [hr] at hs
      rcases hs with ⟨_, _, _, _, _, _, hmem⟩
      rcases hmem with ⟨_, _, _, _, _, hseg⟩
      rcases hseg with ⟨_, hnz, _⟩
      exact absurd hnext.symm hnz

private theorem alloc_small_repack {fl fl' : List (BitVec 64)}
    {pools pools' : Nat → List (BitVec 64)} {cls : Nat} {p nxt : BitVec 64}
    {rest : List (BitVec 64)} {Q : Mem 64 → Prop} {m : Mem 64}
    (hlt : cls < rtNumClasses) (h2 : 2 ≤ cls) (hmax : 8 * cls ≤ 2 ^ 64)
    (hget : fl'.getD cls 0#64 = nxt) (hpcls : pools' cls = rest) (hnxt : nxt = listHeadPtr rest)
    (hfl : ∀ i, i ≠ cls → fl'.getD i 0#64 = fl.getD i 0#64)
    (hp : ∀ i, i ≠ cls → pools' i = pools i)
    (h : (((region p 8 ⋆ cell64 (p + 8#64) nxt) ⋆ region (p + 16#64) (8 * cls - 16)) ⋆
      smallFreeList (8 * cls) nxt rest ⋆ smallPoolsExcl cls fl pools rtNumClasses ⋆ Q) m) :
    (smallPoolsAt fl' pools' rtNumClasses ⋆ region p (8 * cls) ⋆ Q) m := by
  have h1 : (((smallFreeList (8 * cls) nxt rest ⋆ smallPoolsExcl cls fl pools rtNumClasses) ⋆
      ((region p 8 ⋆ cell64 (p + 8#64) nxt) ⋆ region (p + 16#64) (8 * cls - 16))) ⋆ Q) m := by
    refine sep_mono (fun _ x => ?_) h
    rw [sep_comm ((region p 8 ⋆ cell64 (p + 8#64) nxt) ⋆ region (p + 16#64) (8 * cls - 16)),
      sep_assoc,
      sep_comm ((region p 8 ⋆ cell64 (p + 8#64) nxt) ⋆ region (p + 16#64) (8 * cls - 16)),
      ← sep_assoc] at x
    exact x
  rw [sep_assoc] at h1
  have h2' := smallPoolsAt_pop_head hlt h2 hget hpcls hnxt hfl hp h1
  rw [← sep_assoc] at h2'
  exact sep_mono
    (fun _ x => sep_mono_r (fun _ y => smallFreeNode_to_region (by omega) hmax y) x) h2'

private theorem alloc_bump_split {cur : BitVec 64} {bytes rem : Nat}
    {Q : Mem 64 → Prop} {m : Mem 64}
    (_hle : bytes ≤ rem) (hfit : bytes + (rem - bytes) ≤ 2 ^ 64)
    (h : (region cur rem ⋆ Q) m) :
    (region (cur + BitVec.ofNat 64 bytes) (rem - bytes) ⋆ region cur bytes ⋆ Q) m := by
  have hsplit : region cur rem =
      (region cur bytes ⋆ region (cur + BitVec.ofNat 64 bytes) (rem - bytes)) := by
    have hs := region_split (a := cur) (n1 := bytes) (n2 := rem - bytes) hfit
    rwa [show bytes + (rem - bytes) = rem by omega] at hs
  rw [hsplit] at h
  exact sep_mono (fun _ x => by rw [sep_comm]; exact x) h

private theorem largeSegSplit_unlink_head {hd _lcur nxt : BitVec 64}
    {b : Nat} {rest : List (BitVec 64 × Nat)} {Q : Mem 64 → Prop} {m : Mem 64}
    (h512 : 512 ≤ b) (hmax : b < 2 ^ 64)
    (h : ((largeFreeNode b hd nxt ⋆ largeSeg nxt 0#64 rest) ⋆ Q) m) :
    (largeFreeList nxt rest ⋆ region hd b ⋆ Q) m := by
  have h1 : ((region hd b ⋆ largeSeg nxt 0#64 rest) ⋆ Q) m :=
    sep_mono (fun _ hx => sep_mono (P := largeFreeNode b hd nxt)
      (fun _ hy => largeFreeNode_to_region (bytes := b) (by omega) (by omega) hy) hx) h
  exact sep_mono (fun _ x => by rw [sep_comm]; exact x) h1

private theorem largeSegSplit_unlink_mid {hd prv _lcur nxt : BitVec 64}
    {prvB : Nat} {revMid rest : List (BitVec 64 × Nat)} {m : Mem 64}
    (hnz : prv ≠ 0#64) (hal : prv.toNat % 8 = 0)
    (hlo : 512 ≤ prvB) (hhi : prvB < rtMaxObjBytes) (hmod : prvB % 8 = 0)
    (hm : ((largeSeg hd prv revMid.reverse ⋆ largeFreeNode prvB prv nxt) ⋆
      largeSeg nxt 0#64 rest) m) :
    largeFreeList hd (revMid.reverse ++ (prv, prvB) :: rest) m := by
  rw [show revMid.reverse ++ (prv, prvB) :: rest =
    (revMid.reverse ++ [(prv, prvB)]) ++ rest by simp]
  refine largeSeg_append (mid := nxt) _ rest ?_
  exact sep_mono (fun _ hx => largeSeg_split_snoc hnz hal hlo hhi hmod revMid.reverse hx) hm

private def RtC0State.withAllocStats (st : RtC0State) (bytesBV : BitVec 64)
    (updPeak : Bool) : RtC0State where
  extraArgs := st.extraArgs
  globals := st.globals
  freeList := st.freeList
  hdr :=
    { st.hdr with
      s_st_allocs := st.hdr.s_st_allocs + 1#64
      s_st_bytes := st.hdr.s_st_bytes + bytesBV
      s_st_live := st.hdr.s_st_live + 1#64
      s_st_peak_live :=
        if updPeak then st.hdr.s_st_live + 1#64 else st.hdr.s_st_peak_live }
  workBuf := st.workBuf
  smallPools := st.smallPools
  largeNodes := st.largeNodes
  extraLen := st.extraLen
  globalsLen := st.globalsLen
  freeListLen := st.freeListLen
  workLen := st.workLen
  curLeEnd := st.curLeEnd
  arenaAlign := st.arenaAlign
  curNz := st.curNz

private def RtC0State.withBump (st : RtC0State) (bytes : Nat) (hmax : bytes < rtMaxObjBytes)
    (hrem : bytes ≤ st.rem) (hmod : bytes % 8 = 0) : RtC0State where
  extraArgs := st.extraArgs
  globals := st.globals
  freeList := st.freeList
  hdr := { st.hdr with s_cur := st.hdr.s_cur + BitVec.ofNat 64 bytes }
  workBuf := st.workBuf
  smallPools := st.smallPools
  largeNodes := st.largeNodes
  extraLen := st.extraLen
  globalsLen := st.globalsLen
  freeListLen := st.freeListLen
  workLen := st.workLen
  curLeEnd := bump_curLeEnd st.curLeEnd hmax hrem
  arenaAlign := bump_cur_align st.arenaAlign st.curLeEnd hrem hmod
  curNz := bump_cur_nz st.curNz st.curLeEnd hrem

private theorem sep_mono_r' {P Q Q' : Mem 64 → Prop} {m : Mem 64}
    (hm : (P ⋆ Q) m) (h : ∀ x, Q x → Q' x) : (P ⋆ Q') m :=
  sep_mono_r h hm

private theorem sep_mono_7r {A1 A2 A3 A4 A5 A6 A7 X Y : Mem 64 → Prop} {m : Mem 64}
    (h : ∀ m', X m' → Y m')
    (hm : (A1 ⋆ (A2 ⋆ (A3 ⋆ (A4 ⋆ (A5 ⋆ (A6 ⋆ (A7 ⋆ X))))))) m) :
    (A1 ⋆ (A2 ⋆ (A3 ⋆ (A4 ⋆ (A5 ⋆ (A6 ⋆ (A7 ⋆ Y))))))) m :=
  sep_mono_r' hm fun _ h1 => sep_mono_r' h1 fun _ h2 => sep_mono_r' h2 fun _ h3 =>
    sep_mono_r' h3 fun _ h4 => sep_mono_r' h4 fun _ h5 => sep_mono_r' h5 fun _ h6 =>
      sep_mono_r' h6 h

private theorem rtC0_split_tail_region
    {A1 A2 A3 A4 A5 A6 A7 R : Mem 64 → Prop} {cur : BitVec 64} {rem bytes : Nat} {m : Mem 64}
    (hrem : bytes ≤ rem) (hsum : bytes + (rem - bytes) ≤ 2 ^ 64)
    (hm : (A1 ⋆ (A2 ⋆ (A3 ⋆ (A4 ⋆ (A5 ⋆ (A6 ⋆ (A7 ⋆ (region cur rem ⋆ R)))))))) m) :
    (A1 ⋆ (A2 ⋆ (A3 ⋆ (A4 ⋆ (A5 ⋆ (A6 ⋆ (A7 ⋆
      (region (cur + BitVec.ofNat 64 bytes) (rem - bytes) ⋆ region cur bytes ⋆ R)))))))) m :=
  sep_mono_7r (X := region cur rem ⋆ R)
    (Y := region (cur + BitVec.ofNat 64 bytes) (rem - bytes) ⋆ region cur bytes ⋆ R)
    (fun _ hx => alloc_bump_split hrem hsum hx) hm

private theorem sep_goal1_pull_cell {C1 C2 C3 S1 S2 D : Mem 64 → Prop} {m : Mem 64}
    (h : (C1 ⋆ C2 ⋆ C3 ⋆ S1 ⋆ S2 ⋆ D) m) : (C2 ⋆ (C1 ⋆ C3 ⋆ S1 ⋆ S2 ⋆ D)) m :=
  sep_cast h (by ac_rfl)

private theorem sep_rot4_bump {P1 P2 P3 P4 P5 P6 P7 P8 B R : Mem 64 → Prop} {m : Mem 64}
    (h : (P4 ⋆ (P1 ⋆ (P2 ⋆ (P3 ⋆ (P5 ⋆ (P6 ⋆ (P7 ⋆ (P8 ⋆ B ⋆ R)))))))) m) :
    ((P1 ⋆ P2 ⋆ P3 ⋆ P4 ⋆ P5 ⋆ P6 ⋆ P7 ⋆ P8) ⋆ B ⋆ R) m :=
  sep_cast h (by ac_rfl)

private theorem sep_goal1_rearrange {C1 C2 C3 S1 S2 H1 H2 H3 H4 H5 H7 H8 R : Mem 64 → Prop}
    {m : Mem 64}
    (h : (H4 ⋆ (H3 ⋆ (C2 ⋆ (C1 ⋆ (C3 ⋆ (S1 ⋆ (S2 ⋆ (H1 ⋆ (H2 ⋆ (H5 ⋆ (H7 ⋆ (H8 ⋆ R)))))))))))) m) :
    (((C1 ⋆ C2) ⋆ C3) ⋆ S1 ⋆ S2 ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H7 ⋆ H8 ⋆ R)) m :=
  sep_cast h (by ac_rfl)

private theorem sep_goal1_to_rtC0 {S6 B H1 H2 H3 H4 H5 H7 H8 R : Mem 64 → Prop} {m : Mem 64}
    (h : (S6 ⋆ B ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H7 ⋆ H8 ⋆ R)) m) :
    ((H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ S6 ⋆ H7 ⋆ H8) ⋆ B ⋆ R) m :=
  sep_cast h (by ac_rfl)

private theorem sep_swap_large_for_bump {P1 P2 P3 P4 P5 P6 P7 P8 R : Mem 64 → Prop} {m : Mem 64}
    (h : (P4 ⋆ (P7 ⋆ (P1 ⋆ (P2 ⋆ (P3 ⋆ (P5 ⋆ (P6 ⋆ (P8 ⋆ R)))))))) m) :
    (P4 ⋆ (P1 ⋆ (P2 ⋆ (P3 ⋆ (P5 ⋆ (P6 ⋆ (P7 ⋆ (P8 ⋆ R)))))))) m :=
  sep_cast h (by ac_rfl)

private theorem sep_large_intro {H1 H2 H3 H4 H5 H6 L H8 R : Mem 64 → Prop} {m : Mem 64}
    (h : (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ L ⋆ H8 ⋆ R) m) :
    (L ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R)) m :=
  sep_cast h (by ac_rfl)

private theorem sep_large_extro {H1 H2 H3 H4 H5 H6 L H8 R : Mem 64 → Prop} {m : Mem 64}
    (h : (L ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R)) m) :
    (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ L ⋆ H8 ⋆ R) m :=
  sep_cast h (by ac_rfl)

private theorem sep_lcur_nil {N1 N2 N3 N4 N5 H1 H2 H3 H4 H5 H6 H8 R : Mem 64 → Prop}
    {m : Mem 64}
    (h : ((N1 ⋆ N2 ⋆ N3 ⋆ N4 ⋆ N5) ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R)) m) :
    (N3 ⋆ (N2 ⋆ (N1 ⋆ (N4 ⋆ (N5 ⋆
      (H1 ⋆ (H2 ⋆ (H3 ⋆ (H4 ⋆ (H5 ⋆ (H6 ⋆ (H8 ⋆ R)))))))))))) m :=
  sep_cast h (by ac_rfl)

private theorem sep_lcur_nil_back {N1 N2 N3 N4 N5 H1 H2 H3 H4 H5 H6 H8 R : Mem 64 → Prop}
    {m : Mem 64}
    (h : (N3 ⋆ (N2 ⋆ (N1 ⋆ (N4 ⋆ (N5 ⋆
      (H1 ⋆ (H2 ⋆ (H3 ⋆ (H4 ⋆ (H5 ⋆ (H6 ⋆ (H8 ⋆ R)))))))))))) m) :
    (((N1 ⋆ N2 ⋆ N3 ⋆ N4) ⋆ N5) ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R)) m :=
  sep_cast h (by ac_rfl)

private theorem sep_lcur_cons {P1 P2 P3 P4 P5 N1 N2 N3 N4 N5 H1 H2 H3 H4 H5 H6 H8 R :
      Mem 64 → Prop} {m : Mem 64}
    (h : (((P1 ⋆ (P2 ⋆ P3 ⋆ P4 ⋆ P5)) ⋆ (N1 ⋆ N2 ⋆ N3 ⋆ N4 ⋆ N5)) ⋆
      (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R)) m) :
    (N3 ⋆ (N2 ⋆ (P3 ⋆ (P1 ⋆ (P2 ⋆ (P4 ⋆ (P5 ⋆ (N1 ⋆ (N4 ⋆ (N5 ⋆
      (H1 ⋆ (H2 ⋆ (H3 ⋆ (H4 ⋆ (H5 ⋆ (H6 ⋆ (H8 ⋆ R))))))))))))))))) m :=
  sep_cast h (by ac_rfl)

private theorem sep_swap_12 {A B D : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ D)) m) : (B ⋆ (A ⋆ D)) m :=
  sep_cast h (by ac_rfl)

private theorem sep_cons_bring_nxt {A B C D : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ (C ⋆ D))) m) : (B ⋆ (C ⋆ (A ⋆ D))) m :=
  sep_cast h (by ac_rfl)

private theorem sep_lcur_cons_back {P1 P2 P3 P4 P5 N1 N2 N3 N4 N5 H1 H2 H3 H4 H5 H6 H8 R :
      Mem 64 → Prop} {m : Mem 64}
    (h : (N2 ⋆ (P3 ⋆ (N3 ⋆ (P1 ⋆ (P2 ⋆ (P4 ⋆ (P5 ⋆ (N1 ⋆ (N4 ⋆ (N5 ⋆
      (H1 ⋆ (H2 ⋆ (H3 ⋆ (H4 ⋆ (H5 ⋆ (H6 ⋆ (H8 ⋆ R))))))))))))))))) m) :
    (((P1 ⋆ (P2 ⋆ P3 ⋆ P4 ⋆ P5)) ⋆ ((N1 ⋆ N2 ⋆ N3 ⋆ N4) ⋆ N5)) ⋆
      (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R)) m :=
  sep_cast h (by ac_rfl)

private theorem sep_head_repack {N1 N2 N3 N4 N5 H1 H2 H3 H4 H5 H6 H8 R : Mem 64 → Prop}
    {m : Mem 64}
    (h : (H4 ⋆ (N3 ⋆ (N2 ⋆ (N1 ⋆ (N4 ⋆ (N5 ⋆
      (H1 ⋆ (H2 ⋆ (H3 ⋆ (H5 ⋆ (H6 ⋆ (H8 ⋆ R)))))))))))) m) :
    (((N1 ⋆ N2 ⋆ N3 ⋆ N4) ⋆ N5) ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R)) m :=
  sep_cast h (by ac_rfl)

private theorem sep_head_to_rtC0 {L B H1 H2 H3 H4 H5 H6 H8 R : Mem 64 → Prop} {m : Mem 64}
    (h : (L ⋆ B ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R)) m) :
    ((H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ L ⋆ H8) ⋆ B ⋆ R) m :=
  sep_cast h (by ac_rfl)

private theorem sep_mid_to_unlink {P1 P2 P3 P4 P5 N1 N2 N3 N4 N5 H1 H2 H3 H4 H5 H6 H8 R :
      Mem 64 → Prop} {m : Mem 64}
    (h : (H4 ⋆ (P3 ⋆ (N2 ⋆ (N3 ⋆ (P1 ⋆ (P2 ⋆ (P4 ⋆ (P5 ⋆ (N1 ⋆ (N4 ⋆ (N5 ⋆
      (H1 ⋆ (H2 ⋆ (H3 ⋆ (H5 ⋆ (H6 ⋆ (H8 ⋆ R))))))))))))))))) m) :
    ((N1 ⋆ N2 ⋆ N3 ⋆ N4) ⋆
      (((P1 ⋆ (P2 ⋆ P3 ⋆ P4 ⋆ P5)) ⋆ N5) ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R))) m :=
  sep_cast h (by ac_rfl)

private theorem sep_mid_swap_region {L B D : Mem 64 → Prop} {m : Mem 64}
    (h : (B ⋆ (L ⋆ D)) m) : (L ⋆ (B ⋆ D)) m :=
  sep_cast h (by ac_rfl)

private theorem sep_mid_to_rtC0 {L B H1 H2 H3 H4 H5 H6 H8 R : Mem 64 → Prop} {m : Mem 64}
    (h : (L ⋆ (B ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ H8 ⋆ R))) m) :
    ((H1 ⋆ H2 ⋆ H3 ⋆ H4 ⋆ H5 ⋆ H6 ⋆ L ⋆ H8) ⋆ B ⋆ R) m :=
  sep_cast h (by ac_rfl)

private theorem rtC0_intro_largeSplit {rt : BitVec 64} {st : RtC0State}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
      array64 st.hdr.s_work st.workBuf ⋆
      smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      largeFreeList st.hdr.s_large_free st.largeNodes ⋆
      region st.hdr.s_cur st.rem ⋆ R) m) :
    (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
      array64 st.hdr.s_work st.workBuf ⋆
      smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      largeSegSplit st.hdr.s_large_free 0#64 st.hdr.s_large_free [] st.largeNodes ⋆
      region st.hdr.s_cur st.rem ⋆ R) m := by
  have h1 : (largeFreeList st.hdr.s_large_free st.largeNodes ⋆
      (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
        array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
        array64 st.hdr.s_work st.workBuf ⋆
        smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
        region st.hdr.s_cur st.rem ⋆ R)) m := by c0_frame
  have h2 := sep_mono (fun _ hx => largeSegSplit_init hx) h1
  exact sep_cast h2 (by ac_rfl)

private theorem rtC0_pull_smallPools {rt : BitVec 64} {st : RtC0State}
    {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
      array64 st.hdr.s_work st.workBuf ⋆
      smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      largeFreeList st.hdr.s_large_free st.largeNodes ⋆
      region st.hdr.s_cur st.rem ⋆ R) m) :
    (smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
        array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
        array64 st.hdr.s_work st.workBuf ⋆
        largeFreeList st.hdr.s_large_free st.largeNodes ⋆
        region st.hdr.s_cur st.rem ⋆ R)) m := by c0_frame

private theorem alloc_large_nil_finish {rt lcur : BitVec 64} {st : RtC0State}
    {b bytes : Nat} {rest : List (BitVec 64 × Nat)} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} (updPeak : Bool) (bytesBV : BitVec 64)
    (hcurNz : lcur ≠ 0#64) (hcurAl : lcur.toNat % 8 = 0)
    (hb512 : 512 ≤ b) (hbMax : b < rtMaxObjBytes) (hbEq : b = bytes)
    (hm : (LcnfC0Rt.At rt
        { st.hdr with
          s_large_free := largeSegNext 0#64 rest
          s_st_allocs := st.hdr.s_st_allocs + 1#64
          s_st_live := st.hdr.s_st_live + 1#64
          s_st_peak_live :=
            if updPeak then st.hdr.s_st_live + 1#64 else st.hdr.s_st_peak_live
          s_st_reused := st.hdr.s_st_reused + 1#64
          s_st_bytes := st.hdr.s_st_bytes + bytesBV } ⋆
      (cell64 (lcur + 16#64) (BitVec.ofNat 64 b) ⋆
      (cell64 (lcur + 8#64) (largeSegNext 0#64 rest) ⋆
      (region lcur 8 ⋆
      (region (lcur + 24#64) (b - 24) ⋆
      (largeSeg (largeSegNext 0#64 rest) 0#64 rest ⋆
      (array64 rt st.extraArgs ⋆
      (array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      (array64 (rt + 33024#64) st.freeList ⋆
      (array64 st.hdr.s_work st.workBuf ⋆
      (smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      (region st.hdr.s_cur st.rem ⋆ R)))))))))))) m)
    (hQ : ∀ (p : BitVec 64) (st' : RtC0State) (m' : Mem 64),
      p ≠ 0#64 → p.toNat % 8 = 0 → st'.PreservesMeta st →
      st'.rem ≤ st.rem → st.rem - bytes ≤ st'.rem →
      (rtC0Inv rt st' ⋆ region p bytes ⋆ R) m' → Q (p, ()) m') :
    Q (lcur, ()) m := by
  let st1 : RtC0State :=
    { st with
      hdr :=
        { st.hdr with
          s_large_free := largeSegNext 0#64 rest
          s_st_reused := st.hdr.s_st_reused + 1#64 }
      largeNodes := rest }
  let st2 := st1.withAllocStats bytesBV updPeak
  have hrep : ((largeFreeNode b lcur (largeSegNext 0#64 rest) ⋆
      largeSeg (largeSegNext 0#64 rest) 0#64 rest) ⋆
      (array64 rt st2.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st2.globals ⋆
        array64 (rt + 33024#64) st2.freeList ⋆ LcnfC0Rt.At rt st2.hdr ⋆
        array64 st2.hdr.s_work st2.workBuf ⋆
        smallPoolsAt st2.freeList st2.smallPools rtNumClasses ⋆
        region st2.hdr.s_cur st2.rem ⋆ R)) m := by
    unfold largeFreeNode
    exact sep_head_repack hm
  have hu := largeSegSplit_unlink_head (_lcur := lcur) hb512
    (by unfold rtMaxObjBytes at hbMax; omega) hrep
  rw [hbEq] at hu
  refine hQ lcur st2 m hcurNz hcurAl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (Nat.le_refl _) (Nat.sub_le _ _) ?_
  unfold rtC0Inv
  exact sep_head_to_rtC0 hu

private theorem alloc_large_mid_finish {rt prv lcur : BitVec 64} {st : RtC0State}
    {prvB b bytes : Nat} {revMid rest : List (BitVec 64 × Nat)} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} (updPeak : Bool) (bytesBV : BitVec 64)
    (hprvNz : prv ≠ 0#64) (hprvAl : prv.toNat % 8 = 0)
    (hprvLo : 512 ≤ prvB) (hprvMax : prvB < rtMaxObjBytes) (hprvMod : prvB % 8 = 0)
    (hcurNz : lcur ≠ 0#64) (hcurAl : lcur.toNat % 8 = 0)
    (hb512 : 512 ≤ b) (hbMax : b < rtMaxObjBytes) (hbEq : b = bytes)
    (hm : (LcnfC0Rt.At rt
        { st.hdr with
          s_st_allocs := st.hdr.s_st_allocs + 1#64
          s_st_live := st.hdr.s_st_live + 1#64
          s_st_peak_live :=
            if updPeak then st.hdr.s_st_live + 1#64 else st.hdr.s_st_peak_live
          s_st_reused := st.hdr.s_st_reused + 1#64
          s_st_bytes := st.hdr.s_st_bytes + bytesBV } ⋆
      (cell64 (prv + 8#64) (largeSegNext 0#64 rest) ⋆
      (cell64 (lcur + 8#64) (largeSegNext 0#64 rest) ⋆
      (cell64 (lcur + 16#64) (BitVec.ofNat 64 b) ⋆
      (largeSeg st.hdr.s_large_free prv revMid.reverse ⋆
      (region prv 8 ⋆
      (cell64 (prv + 16#64) (BitVec.ofNat 64 prvB) ⋆
      (region (prv + 24#64) (prvB - 24) ⋆
      (region lcur 8 ⋆
      (region (lcur + 24#64) (b - 24) ⋆
      (largeSeg (largeSegNext 0#64 rest) 0#64 rest ⋆
      (array64 rt st.extraArgs ⋆
      (array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      (array64 (rt + 33024#64) st.freeList ⋆
      (array64 st.hdr.s_work st.workBuf ⋆
      (smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      (region st.hdr.s_cur st.rem ⋆ R))))))))))))))))) m)
    (hQ : ∀ (p : BitVec 64) (st' : RtC0State) (m' : Mem 64),
      p ≠ 0#64 → p.toNat % 8 = 0 → st'.PreservesMeta st →
      st'.rem ≤ st.rem → st.rem - bytes ≤ st'.rem →
      (rtC0Inv rt st' ⋆ region p bytes ⋆ R) m' → Q (p, ()) m') :
    Q (lcur, ()) m := by
  let st1 : RtC0State :=
    { st with
      hdr := { st.hdr with s_st_reused := st.hdr.s_st_reused + 1#64 }
      largeNodes := revMid.reverse ++ (prv, prvB) :: rest }
  let st2 := st1.withAllocStats bytesBV updPeak
  have hun : (largeFreeNode b lcur (largeSegNext 0#64 rest) ⋆
      (((largeSeg st2.hdr.s_large_free prv revMid.reverse ⋆
        largeFreeNode prvB prv (largeSegNext 0#64 rest)) ⋆
        largeSeg (largeSegNext 0#64 rest) 0#64 rest) ⋆
        (array64 rt st2.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st2.globals ⋆
          array64 (rt + 33024#64) st2.freeList ⋆ LcnfC0Rt.At rt st2.hdr ⋆
          array64 st2.hdr.s_work st2.workBuf ⋆
          smallPoolsAt st2.freeList st2.smallPools rtNumClasses ⋆
          region st2.hdr.s_cur st2.rem ⋆ R))) m := by
    unfold largeFreeNode
    exact sep_mid_to_unlink hm
  have hreg := sep_mono (fun _ hx => largeFreeNode_to_region (by omega)
    (by unfold rtMaxObjBytes at hbMax; omega) hx) hun
  rw [hbEq] at hreg
  have hu := sep_mono (fun _ hx =>
    largeSegSplit_unlink_mid (_lcur := lcur) hprvNz hprvAl hprvLo hprvMax hprvMod hx)
    (sep_mid_swap_region hreg)
  refine hQ lcur st2 m hcurNz hcurAl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (Nat.le_refl _) (Nat.sub_le _ _) ?_
  unfold rtC0Inv
  exact sep_mid_to_rtC0 hu

private theorem alloc_small_finish {rt p : BitVec 64} {st : RtC0State}
    {bytes : Nat} {rest : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} (updPeak : Bool) (bytesBV : BitVec 64)
    (hflLen : st.freeList.length = 64) (hcls2 : 2 ≤ bytes / 8) (hclsLt : bytes / 8 < 64)
    (_hmax : bytes < rtMaxObjBytes) (hpNe : p ≠ 0#64) (hpalign : p.toNat % 8 = 0)
    (hbyEq : 8 * (bytes / 8) = bytes)
    (hm : (LcnfC0Rt.At rt
        { st.hdr with
          s_st_allocs := st.hdr.s_st_allocs + 1#64
          s_st_live := st.hdr.s_st_live + 1#64
          s_st_peak_live :=
            if updPeak then st.hdr.s_st_live + 1#64 else st.hdr.s_st_peak_live
          s_st_reused := st.hdr.s_st_reused + 1#64
          s_st_bytes := st.hdr.s_st_bytes + bytesBV } ⋆
      (array64 (rt + 33024#64) (st.freeList.set (bytes / 8) (listHeadPtr rest)) ⋆
      (cell64 (p + 8#64) (listHeadPtr rest) ⋆
      (region p 8 ⋆
      (region (p + 16#64) (8 * (bytes / 8) - 16) ⋆
      (smallFreeList (8 * (bytes / 8)) (listHeadPtr rest) rest ⋆
      (smallPoolsExcl (bytes / 8) st.freeList st.smallPools rtNumClasses ⋆
      (array64 rt st.extraArgs ⋆
      (array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      (array64 st.hdr.s_work st.workBuf ⋆
      (largeFreeList st.hdr.s_large_free st.largeNodes ⋆
      (region st.hdr.s_cur st.rem ⋆ R)))))))))))) m)
    (hQ : ∀ (p : BitVec 64) (st' : RtC0State) (m' : Mem 64),
      p ≠ 0#64 → p.toNat % 8 = 0 → st'.PreservesMeta st →
      st'.rem ≤ st.rem → st.rem - bytes ≤ st'.rem →
      (rtC0Inv rt st' ⋆ region p bytes ⋆ R) m' → Q (p, ()) m') :
    Q (p, ()) m := by
  let cls := bytes / 8
  let fl' := st.freeList.set cls (listHeadPtr rest)
  let pools' : Nat → List (BitVec 64) := fun i => if i = cls then rest else st.smallPools i
  let st1 : RtC0State :=
    { st with
      freeList := fl'
      hdr := { st.hdr with s_st_reused := st.hdr.s_st_reused + 1#64 }
      smallPools := pools'
      freeListLen := by dsimp [fl']; rw [List.length_set, hflLen]; rfl }
  let st2 := st1.withAllocStats bytesBV updPeak
  have hf : (((region p 8 ⋆ cell64 (p + 8#64) (listHeadPtr rest)) ⋆
      region (p + 16#64) (8 * cls - 16)) ⋆
      smallFreeList (8 * cls) (listHeadPtr rest) rest ⋆
      smallPoolsExcl cls st.freeList st.smallPools rtNumClasses ⋆
      (array64 rt st2.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st2.globals ⋆
        array64 (rt + 33024#64) st2.freeList ⋆ LcnfC0Rt.At rt st2.hdr ⋆
        array64 st2.hdr.s_work st2.workBuf ⋆
        largeFreeList st2.hdr.s_large_free st2.largeNodes ⋆
        region st2.hdr.s_cur st2.rem ⋆ R)) m :=
    sep_goal1_rearrange hm
  have hre := alloc_small_repack (fl := st.freeList) (fl' := fl') (pools := st.smallPools)
    (pools' := pools') (by unfold rtNumClasses; omega) hcls2
    (by omega)
    (list_getD_set_self st.freeList (listHeadPtr rest) 0#64 (by rw [hflLen]; exact hclsLt))
    (by dsimp only [pools']; split; rfl; contradiction) rfl
    (fun i hi => list_getD_set_ne st.freeList (listHeadPtr rest) 0#64 hi)
    (fun i hi => by dsimp only [pools']; split; contradiction; rfl) hf
  rw [hbyEq] at hre
  refine hQ p st2 m hpNe hpalign ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (Nat.le_refl _) (Nat.sub_le _ _) ?_
  unfold rtC0Inv
  exact sep_goal1_to_rtC0 hre

private theorem alloc_bump_finish {rt : BitVec 64} {st : RtC0State}
    {bytes : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} (updPeak : Bool) (bytesBV : BitVec 64)
    (hcurLe : st.hdr.s_cur.toNat ≤ st.hdr.s_end.toNat)
    (hmax : bytes < rtMaxObjBytes) (hrem : bytes ≤ st.rem) (hmod : bytes % 8 = 0)
    (hbyEq : bytesBV = BitVec.ofNat 64 bytes)
    (hm : (LcnfC0Rt.At rt
        { st.hdr with
          s_cur := st.hdr.s_cur + BitVec.ofNat 64 bytes
          s_st_allocs := st.hdr.s_st_allocs + 1#64
          s_st_live := st.hdr.s_st_live + 1#64
          s_st_peak_live :=
            if updPeak then st.hdr.s_st_live + 1#64 else st.hdr.s_st_peak_live
          s_st_bytes := st.hdr.s_st_bytes + BitVec.ofNat 64 bytes } ⋆
      (array64 rt st.extraArgs ⋆
      (array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
      (array64 (rt + 33024#64) st.freeList ⋆
      (array64 st.hdr.s_work st.workBuf ⋆
      (smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
      (largeFreeList st.hdr.s_large_free st.largeNodes ⋆
      (region st.hdr.s_cur st.rem ⋆ R)))))))) m)
    (hQ : ∀ (p : BitVec 64) (st' : RtC0State) (m' : Mem 64),
      p ≠ 0#64 → p.toNat % 8 = 0 → st'.PreservesMeta st →
      st'.rem ≤ st.rem → st.rem - bytes ≤ st'.rem →
      (rtC0Inv rt st' ⋆ region p bytes ⋆ R) m' → Q (p, ()) m') :
    Q (st.hdr.s_cur, ()) m := by
  have hsum : bytes + (st.rem - bytes) ≤ 2 ^ 64 := by
    have := st.hdr.s_end.isLt
    unfold RtC0State.rem at hrem ⊢
    omega
  have hsplit := rtC0_split_tail_region hrem hsum hm
  let st1 := (st.withBump bytes hmax hrem hmod).withAllocStats bytesBV updPeak
  have hst1Eq : st1.rem = st.rem - bytes := by
    unfold st1 RtC0State.withAllocStats RtC0State.withBump RtC0State.rem
    exact bump_rem_eq hcurLe hmax hrem
  refine hQ st.hdr.s_cur st1 m st.curNz st.arenaAlign
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by rw [hst1Eq]; omega)
    (by rw [hst1Eq]; exact Nat.le_refl _) ?_
  unfold rtC0Inv
  dsimp only [st1, RtC0State.withAllocStats, RtC0State.withBump, RtC0State.rem]
  rw [hbyEq]
  rw [show (st.hdr.s_end.toNat - (st.hdr.s_cur + BitVec.ofNat 64 bytes).toNat) = st.rem - bytes from
    bump_rem_eq hcurLe hmax hrem]
  exact sep_rot4_bump hsplit

private theorem lcnf_alloc_rem_small_wp (Γ : Env) (rt sz : Val i64) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) (hsmall : align8 sz.toNat / 8 < 64)
    (hspec : lcnfAllocRemSpec (rt, sz, ()) m Q X) :
    Func.wp Γ lcnf_alloc_body (rt, sz, ()) m Q X := by
  rcases hspec with ⟨st, R, hsz, hmin, hmax, havail, hm, hQ⟩
  have hflLen : st.freeList.length = 64 := st.freeListLen
  have hcurLe : st.hdr.s_cur.toNat ≤ st.hdr.s_end.toNat := st.curLeEnd
  have hbyBv := align8_bv_eq sz hsz
  have hclsEq := align8_div8_eq sz hsz
  have hbyMod : align8 sz.toNat % 8 = 0 := by unfold align8; omega
  have hby16 : ¬ ((sz + 7) &&& 18446744073709551608).toNat < 16 := by
    rw [hbyBv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)]
    unfold rtMinObjBytes at hmin
    omega
  let bytes := align8 sz.toNat
  let bytesBV : BitVec 64 := BitVec.ofNat 64 bytes
  have hbyBvNat : bytesBV.toNat = bytes := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)]
  unfold rtC0Inv at hm
  change LeanQbe.T.Func.wp _ _ _ _ _ _
  c0_steps
  · have hcls : (((sz + 7) &&& 18446744073709551608) >>> 3).toNat < (64 : BitVec 64).toNat := by
      assumption
    rw [hclsEq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)] at hcls
    have hclsLt : bytes / 8 < 64 := hcls
    have hcls2 : 2 ≤ bytes / 8 := by unfold rtMinObjBytes at hmin; omega
    have hbyEq : 8 * (bytes / 8) = bytes := align8_div8_mul8 hbyMod
    let cls := bytes / 8
    have hclsBvNat : (BitVec.ofNat 64 cls).toNat = cls := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cls < 2 ^ 64)]
    have hidxNat : (((sz + 7) &&& 18446744073709551608) >>> 3).toNat = cls := by
      rw [hclsEq, hclsBvNat]
    have hflEq : (st.freeList[(((sz + 7) &&& 18446744073709551608) >>> 3).toNat]'(by
        rw [hflLen, hidxNat]; exact hclsLt)) =
        st.freeList[cls]'(by rw [hflLen]; exact hclsLt) := by
      simp only [hidxNat]
    have hne : st.freeList[cls]'(by rw [hflLen]; exact hclsLt) ≠ 0#64 := by
      rw [← hflEq]
      exact hc
    obtain ⟨p, hpEq⟩ : ∃ p, p = st.freeList[cls]'(by rw [hflLen]; exact hclsLt) := ⟨_, rfl⟩
    have hpNe : p ≠ 0#64 := hpEq ▸ hne
    have hflIdx : (st.freeList[(((sz + 7) &&& 18446744073709551608) >>> 3).toNat]'(by
        rw [hflLen, hidxNat]; exact hclsLt)) = p :=
      hflEq.trans hpEq.symm
    simp only [hflIdx]
    obtain ⟨rest, _, hpalign, hmPop⟩ :=
      smallPoolsAt_pop st.freeListLen hcls2 (by unfold rtNumClasses; omega) hne
        (rtC0_pull_smallPools hm)
    have hpEq' : p = st.freeList[bytes / 8]'(by rw [hflLen]; exact hclsLt) := hpEq
    have hmLoad : (cell64 (p + 8#64) (listHeadPtr rest) ⋆
        (region p 8 ⋆ region (p + 16#64) (8 * cls - 16) ⋆
          smallFreeList (8 * cls) (listHeadPtr rest) rest ⋆
          smallPoolsExcl cls st.freeList st.smallPools rtNumClasses ⋆
          (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
            array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
            array64 st.hdr.s_work st.workBuf ⋆
            largeFreeList st.hdr.s_large_free st.largeNodes ⋆
            region st.hdr.s_cur st.rem ⋆ R))) m := by
      have hmPop0 : (((region p 8 ⋆ cell64 (p + 8#64) (listHeadPtr rest)) ⋆
          region (p + 16#64) (8 * cls - 16)) ⋆
          smallFreeList (8 * cls) (listHeadPtr rest) rest ⋆
          smallPoolsExcl cls st.freeList st.smallPools rtNumClasses ⋆
          (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
            array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
            array64 st.hdr.s_work st.workBuf ⋆
            largeFreeList st.hdr.s_large_free st.largeNodes ⋆
            region st.hdr.s_cur st.rem ⋆ R)) m := by
        simpa only [cls, ← hpEq'] using hmPop
      exact sep_goal1_pull_cell hmPop0
    clear hm hmPop
    change LeanQbe.T.wp _ _ _ _ _
    c0_steps
    · rw [hidxNat, hbyBv] at hm
      dsimp only [cls] at hm
      exact alloc_small_finish true (BitVec.ofNat 64 bytes) hflLen hcls2 hclsLt hmax
        hpNe (hpEq ▸ hpalign) hbyEq hm hQ
    · rw [hidxNat, hbyBv] at hm
      dsimp only [cls] at hm
      exact alloc_small_finish false (BitVec.ofNat 64 bytes) hflLen hcls2 hclsLt hmax
        hpNe (hpEq ▸ hpalign) hbyEq hm hQ
  · exfalso
    have hcls : (((sz + 7) &&& 18446744073709551608) >>> 3).toNat < (64 : BitVec 64).toNat := by
      assumption
    rw [hclsEq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)] at hcls
    have hclsLt : bytes / 8 < 64 := hcls
    have hcls2 : 2 ≤ bytes / 8 := by unfold rtMinObjBytes at hmin; omega
    let cls := bytes / 8
    have hclsBvNat : (BitVec.ofNat 64 cls).toNat = cls := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cls < 2 ^ 64)]
    have hz : st.freeList[(((sz + 7) &&& 18446744073709551608) >>> 3).toNat]'(by
        rw [hflLen, hclsEq, hclsBvNat]; exact hclsLt) = 0#64 := by
      assumption
    have hidxNat : (((sz + 7) &&& 18446744073709551608) >>> 3).toNat = cls := by
      rw [hclsEq, hclsBvNat]
    have hflEq : (st.freeList[(((sz + 7) &&& 18446744073709551608) >>> 3).toNat]'(by
        rw [hflLen, hidxNat]; exact hclsLt)) =
        st.freeList[cls]'(by rw [hflLen]; exact hclsLt) := by
      simp only [hidxNat]
    have hz' : st.freeList[cls]'(by rw [hflLen]; exact hclsLt) = 0#64 := by
      rw [← hflEq]
      exact hz
    have hpoolEmpty := smallPoolsAt_zero_empty hflLen hcls2 (by unfold rtNumClasses; omega) hz'
      (rtC0_pull_smallPools hm)
    have hlt512 : bytes < 512 := by omega
    have hrem : bytes ≤ st.rem := by
      rcases havail with (⟨_, hne⟩ | ⟨hge, _⟩) | hrem
      · exact absurd hpoolEmpty (by simpa [cls] using hne)
      · omega
      · exact hrem
    have hgt : BitVec.toNat (st.hdr.s_end - st.hdr.s_cur) <
        ((sz + 7) &&& 18446744073709551608).toNat := by assumption
    rw [BitVec.toNat_sub_of_le hcurLe, hbyBv, hbyBvNat] at hgt
    unfold RtC0State.rem at hrem
    omega
  · have hnot : ¬ BitVec.toNat (st.hdr.s_end - st.hdr.s_cur) <
        ((sz + 7) &&& 18446744073709551608).toNat := by assumption
    rw [hbyBv] at hnot
    have hrem : bytes ≤ st.rem := rem_of_not_gt hcurLe hmax hnot
    rw [hbyBv] at hm
    exact alloc_bump_finish true bytesBV hcurLe hmax hrem hbyMod rfl hm hQ
  · have hnot : ¬ BitVec.toNat (st.hdr.s_end - st.hdr.s_cur) <
        ((sz + 7) &&& 18446744073709551608).toNat := by assumption
    rw [hbyBv] at hnot
    have hrem : bytes ≤ st.rem := rem_of_not_gt hcurLe hmax hnot
    rw [hbyBv] at hm
    exact alloc_bump_finish false bytesBV hcurLe hmax hrem hbyMod rfl hm hQ

private theorem lcnf_alloc_rem_large_wp (Γ : Env) (rt sz : Val i64) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) (hlarge : ¬ align8 sz.toNat / 8 < 64)
    (hspec : lcnfAllocRemSpec (rt, sz, ()) m Q X) :
    Func.wp Γ lcnf_alloc_body (rt, sz, ()) m Q X := by
  rcases hspec with ⟨st, R, hsz, hmin, hmax, havail, hm, hQ⟩
  have hflLen : st.freeList.length = 64 := st.freeListLen
  have hcurLe : st.hdr.s_cur.toNat ≤ st.hdr.s_end.toNat := st.curLeEnd
  have hbyBv := align8_bv_eq sz hsz
  have hclsEq := align8_div8_eq sz hsz
  have hbyMod : align8 sz.toNat % 8 = 0 := by unfold align8; omega
  have hby16 : ¬ ((sz + 7) &&& 18446744073709551608).toNat < 16 := by
    rw [hbyBv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)]
    unfold rtMinObjBytes at hmin
    omega
  let bytes := align8 sz.toNat
  let bytesBV : BitVec 64 := BitVec.ofNat 64 bytes
  have hbyBvNat : bytesBV.toNat = bytes := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)]
  unfold rtC0Inv at hm
  change LeanQbe.T.Func.wp _ _ _ _ _ _
  c0_steps
  · have hcls : ¬ (((sz + 7) &&& 18446744073709551608) >>> 3).toNat < (64 : BitVec 64).toNat := by
      assumption
    rw [hclsEq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hmax; omega)] at hcls
    have h64 : (64 : BitVec 64).toNat = 64 := rfl
    rw [h64] at hcls
    have hge512 : 512 ≤ bytes := by omega
    let LInv : Nat → Tup Val [i64, i64] → Mem 64 → Prop := fun n (prev, lcur, ()) ml =>
      ∃ pfx sfx, sfx.length = n ∧ st.largeNodes = pfx ++ sfx ∧
        (∀ x ∈ pfx, x.2 ≠ bytes) ∧
        (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
          array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
          array64 st.hdr.s_work st.workBuf ⋆
          smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
          largeSegSplit st.hdr.s_large_free prev lcur pfx sfx ⋆
          region st.hdr.s_cur st.rem ⋆ R) ml
    refine wp_loop_group LInv ?_ ?_
    · intro L n ⟨prev, lcur, ⟨⟩⟩ ml hL ⟨pfx, sfx, hlen, hnodes, hnePfx, hmem⟩
      by_cases hlc0 : lcur = 0#64
      · subst hlc0
        have hlg := sep_large_intro hmem
        clear hm hmem
        obtain ⟨m1, m2, rfl, hd, hsp, hrest⟩ := hlg
        have hsfx : sfx = [] := largeSegSplit_sfx_nil_of_zero hsp
        subst hsfx
        have hnil := largeSegSplit_nil hsp
        rw [List.append_nil] at hnodes
        have hallNe : ∀ x ∈ st.largeNodes, x.2 ≠ bytes := by rw [hnodes]; exact hnePfx
        have hrem : bytes ≤ st.rem := by
          rcases havail with (⟨hlt, _⟩ | ⟨_, x, hx, heq⟩) | hrem
          · omega
          · exact absurd heq (hallNe x hx)
          · exact hrem
        have hm : (largeFreeList st.hdr.s_large_free st.largeNodes ⋆
            (array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
              array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
              array64 st.hdr.s_work st.workBuf ⋆
              smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
              region st.hdr.s_cur st.rem ⋆ R)) (m1.union m2) := by
          rw [hnodes]; exact ⟨m1, m2, rfl, hd, hnil, hrest⟩
        clear hd hsp hnil hrest
        change LeanQbe.T.wp _ _ _ _ _
        c0_steps
        · exfalso; exact absurd rfl (by assumption)
        · exfalso
          have hgt : (2 ^ 64 - st.hdr.s_cur.toNat + st.hdr.s_end.toNat) % 2 ^ 64 <
              ((sz + 7) &&& 18446744073709551608).toNat := by assumption
          rw [hbyBv, hbyBvNat] at hgt
          have hlt264 := st.hdr.s_end.isLt
          unfold RtC0State.rem at hrem
          omega
        · rw [hbyBv] at hm
          exact alloc_bump_finish true bytesBV hcurLe hmax hrem hbyMod rfl
            (sep_swap_large_for_bump hm) hQ
        · rw [hbyBv] at hm
          exact alloc_bump_finish false bytesBV hcurLe hmax hrem hbyMod rfl
            (sep_swap_large_for_bump hm) hQ
        · exfalso; have htf : true = false := (by assumption); cases htf
        · exfalso; have htf : true = false := (by assumption); cases htf
      · have hlg := sep_large_intro hmem
        clear hm hmem
        obtain ⟨m1, m2, rfl, hd, hsp, hrest⟩ := hlg
        cases sfx with
        | nil =>
          rcases hsp with ⟨hnext, _⟩
          simp [largeSegNext] at hnext
          exact absurd hnext hlc0
        | cons x rest =>
          rcases x with ⟨curp, b⟩
          rcases hsp with ⟨hnext, hpfxSplit⟩
          dsimp only [largeSegNext] at hnext
          subst hnext
          cases hr : pfx.reverse with
          | nil =>
            rw [hr] at hpfxSplit
            rcases hpfxSplit with ⟨hprev0, hhdEq, hseg⟩
            rcases hseg with ⟨_, hcurNz, hcurAl, hb512, hbMax, hbMod, hnodeSeg⟩
            rw [hprev0] at *
            unfold largeFreeNode at hnodeSeg
            have hm := sep_lcur_nil ⟨m1, m2, rfl, hd, hnodeSeg, hrest⟩
            clear hd hnodeSeg hrest
            change LeanQbe.T.wp _ _ _ _ _
            c0_steps
            · exfalso; exact absurd rfl (by assumption)
            · have hbc : BitVec.ofNat 64 b = ((sz + 7) &&& 18446744073709551608) := by
                assumption
              rw [hbyBv] at hbc
              have hbEq : b = bytes := by
                have hnat := congrArg BitVec.toNat hbc
                rw [BitVec.toNat_ofNat, hbyBvNat,
                  Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hbMax; omega)] at hnat
                exact hnat
              rw [hbyBv] at hm
              exact alloc_large_nil_finish true bytesBV hcurNz hcurAl hb512 hbMax hbEq hm hQ
            · have hbc : BitVec.ofNat 64 b = ((sz + 7) &&& 18446744073709551608) := by
                assumption
              rw [hbyBv] at hbc
              have hbEq : b = bytes := by
                have hnat := congrArg BitVec.toNat hbc
                rw [BitVec.toNat_ofNat, hbyBvNat,
                  Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hbMax; omega)] at hnat
                exact hnat
              rw [hbyBv] at hm
              exact alloc_large_nil_finish false bytesBV hcurNz hcurAl hb512 hbMax hbEq hm hQ
            · have hbc : ¬ BitVec.ofNat 64 b = ((sz + 7) &&& 18446744073709551608) := by
                assumption
              rw [hbyBv] at hbc
              have hbNe : b ≠ bytes := by
                intro hEq; apply hbc; subst hEq; rfl
              let nxt := largeSegNext 0#64 rest
              have hback := sep_lcur_nil_back hm
              obtain ⟨m1', m2', heq, hd', hm1', hrest'⟩ := hback
              have hmStep : largeSegSplit lcur lcur nxt ([] ++ [(lcur, b)]) rest m1' := by
                refine largeSegSplit_step (prev := 0#64) hcurNz hcurAl hb512 hbMax hbMod rfl ?_
                exact ⟨rfl, rfl, hm1'⟩
              have hmAll : (largeSegSplit st.hdr.s_large_free lcur nxt [(lcur, b)] rest ⋆
                  (array64 rt st.extraArgs ⋆
                    array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
                    array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
                    array64 st.hdr.s_work st.workBuf ⋆
                    smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
                    region st.hdr.s_cur st.rem ⋆ R)) (m1'.union m2') := by
                rw [hhdEq]
                exact ⟨m1', m2', rfl, hd', by simpa using hmStep, hrest'⟩
              rw [heq] at hmAll
              refine hL rest.length (lcur, nxt, ()) _
                (by simp only [List.length_cons] at hlen; omega)
                ⟨[(lcur, b)], rest, rfl, ?_, ?_, sep_large_extro hmAll⟩
              · rw [hnodes]
                have hpNil : pfx = [] := List.reverse_eq_nil_iff.mp hr
                simp [hpNil]
              · intro x hx
                simp only [List.mem_singleton] at hx
                subst hx
                exact hbNe
          | cons hdRev tlRev =>
            rw [hr] at hpfxSplit
            rcases hdRev with ⟨prv, prvB⟩
            rcases hpfxSplit with ⟨hprev, hprvNz, hprvAl, hprvLo, hprvMax, hprvMod, hseg⟩
            rw [hprev] at *
            obtain ⟨m11, m12, rfl, hd1, hprefMem, hsfxMem⟩ := hseg
            rcases hsfxMem with ⟨_, hcurNz, hcurAl, hb512, hbMax, hbMod, hnodeSeg⟩
            unfold largeFreeNode at hprefMem hnodeSeg
            have hm := sep_lcur_cons
              ⟨m11.union m12, m2, rfl, hd, ⟨m11, m12, rfl, hd1, hprefMem, hnodeSeg⟩, hrest⟩
            clear hd hd1 hprefMem hnodeSeg hrest
            change LeanQbe.T.wp _ _ _ _ _
            c0_steps
            · have hbc : BitVec.ofNat 64 b = ((sz + 7) &&& 18446744073709551608) := by
                assumption
              rw [hbyBv] at hbc
              have hbEq : b = bytes := by
                have hnat := congrArg BitVec.toNat hbc
                rw [BitVec.toNat_ofNat, hbyBvNat,
                  Nat.mod_eq_of_lt (by unfold rtMaxObjBytes at hbMax; omega)] at hnat
                exact hnat
              have hm0 := sep_cons_bring_nxt hm
              clear hm
              have hm := hm0
              clear hm0
              change LeanQbe.T.wp _ _ _ _ _
              c0_steps
              all_goals first
                | (exfalso; exact absurd rfl (by assumption))
                | (exfalso; have htf : true = false := (by assumption); cases htf)
                | (exfalso; exact hcurNz (by assumption))
                | (exfalso; have h0 : ¬ lcur ≠ 0#64 := (by assumption); exact h0 hcurNz)
                | (exfalso; exact hprvNz (by assumption))
                | (have hm1 := sep_swap_12 hm
                   clear hm
                   have hm := hm1
                   clear hm1
                   change LeanQbe.T.wp _ _ _ _ _
                   c0_steps
                   all_goals first
                     | (have hpk : st.hdr.s_st_peak_live.toNat <
                           (st.hdr.s_st_live.toNat + BitVec.toNat 1#64) % 2 ^ 64 := by assumption
                        rw [hbyBv] at hm
                        exact alloc_large_mid_finish true bytesBV hprvNz hprvAl hprvLo hprvMax
                          hprvMod hcurNz hcurAl hb512 hbMax hbEq hm hQ)
                     | (have hnpk : ¬ st.hdr.s_st_peak_live.toNat <
                           (st.hdr.s_st_live.toNat + BitVec.toNat 1#64) % 2 ^ 64 := by assumption
                        rw [hbyBv] at hm
                        exact alloc_large_mid_finish false bytesBV hprvNz hprvAl hprvLo hprvMax
                          hprvMod hcurNz hcurAl hb512 hbMax hbEq hm hQ))
            · have hbc : ¬ BitVec.ofNat 64 b = ((sz + 7) &&& 18446744073709551608) := by
                assumption
              rw [hbyBv] at hbc
              have hbNe : b ≠ bytes := by
                intro hEq; apply hbc; subst hEq; rfl
              let nxt := largeSegNext 0#64 rest
              have hm := sep_cons_bring_nxt hm
              change LeanQbe.T.wp _ _ _ _ _
              c0_steps
              have hback := sep_lcur_cons_back hm
              obtain ⟨m12', m2', heq, hd', hm12', hrest'⟩ := hback
              obtain ⟨m11', m12'', heq1, hd1', hp', hn'⟩ := hm12'
              have hmStep : largeSegSplit st.hdr.s_large_free lcur nxt (pfx ++ [(lcur, b)]) rest
                  (m11'.union m12'') := by
                refine largeSegSplit_step (prev := prv) hcurNz hcurAl hb512 hbMax hbMod rfl ?_
                rw [hr]
                exact ⟨rfl, hprvNz, hprvAl, hprvLo, hprvMax, hprvMod,
                  m11', m12'', rfl, hd1', hp', hn'⟩
              rw [heq1] at hmStep
              have hmAll : (largeSegSplit st.hdr.s_large_free lcur nxt (pfx ++ [(lcur, b)]) rest ⋆
                  (array64 rt st.extraArgs ⋆
                    array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
                    array64 (rt + 33024#64) st.freeList ⋆ LcnfC0Rt.At rt st.hdr ⋆
                    array64 st.hdr.s_work st.workBuf ⋆
                    smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
                    region st.hdr.s_cur st.rem ⋆ R)) (m12'.union m2') :=
                ⟨m12', m2', rfl, hd', hmStep, hrest'⟩
              rw [heq] at hmAll
              refine hL rest.length (lcur, nxt, ()) _
                (by simp only [List.length_cons] at hlen; omega)
                ⟨pfx ++ [(lcur, b)], rest, rfl,
                  by rw [hnodes]; simp only [List.append_assoc, List.singleton_append],
                  fun x hx => ?_, sep_large_extro hmAll⟩
              · rcases List.mem_append.mp hx with h | h
                · exact hnePfx x h
                · simp only [List.mem_singleton] at h; subst h; exact hbNe
    · intro L hL
      change LeanQbe.T.wp _ _ _ _ _
      c0_steps
      exact hL st.largeNodes.length (0#64, st.hdr.s_large_free, ()) m
        ⟨[], st.largeNodes, rfl, rfl,
          (fun x h => False.elim (List.not_mem_nil h)), rtC0_intro_largeSplit hm⟩

/-- Progress-aware `lcnf_alloc` WP theorem (`st.rem - bytes ≤ st'.rem`). -/
theorem lcnf_alloc_rem_wp (Γ : Env) :
    ∀ xs m Q X, lcnfAllocRemSpec xs m Q X → Func.wp Γ lcnf_alloc_body xs m Q X := by
  rintro ⟨rt, sz, ⟨⟩⟩ m Q X hspec
  by_cases hsmall : align8 sz.toNat / 8 < 64
  · exact lcnf_alloc_rem_small_wp Γ rt sz m Q X hsmall hspec
  · exact lcnf_alloc_rem_large_wp Γ rt sz m Q X hsmall hspec

end LeanQbe.T.LeanLCNF
