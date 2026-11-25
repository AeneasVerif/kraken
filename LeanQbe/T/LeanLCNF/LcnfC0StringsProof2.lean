module

public import LeanQbe.T.LeanLCNF.LcnfC0Strings
public import LeanQbe.T.LeanLCNF.LcnfC0StringsSpec
public import LeanQbe.T.LeanLCNF.LcnfC0StringsProof1
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof1
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof2
public import LeanQbe.T.LeanLCNF.LcnfC0ContainersProof3
import all Kraken.Separation

/-!
# Soundness Proofs for `LcnfC0Strings`, Part 2: String Push, Append, and Cmp Ops

Proves `Func.wp rtR2bEnv` for 3 exported string operations:
- `lcnf_string_push`
- `lcnf_string_append`
- `lcnf_string_cmp_op`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil

local macro "r2b_steps" : tactic => `(tactic| (try change LeanQbe.T.wp _ _ _ _ _; c0_steps))
local elab "r2b_to_group" : tactic => do
  let _ ← Lean.Elab.Tactic.tryTactic
    (Lean.Elab.Tactic.evalTactic (← `(tactic| change LeanQbe.T.wp _ _ _ _ _)))
  for _ in [:200] do
    let st0 ← Lean.Elab.Tactic.saveState
    let isGrp ← Lean.Elab.Tactic.tryTactic <| Lean.Elab.Tactic.evalTactic
      (← `(tactic| refine LeanQbe.T.wp_unroll_group fun _ _ => ?_))
    if isGrp then
      st0.restore
      break
    let gs0 ← Lean.Elab.Tactic.getGoals
    let ok ← Lean.Elab.Tactic.tryTactic (Lean.Elab.Tactic.evalTactic (← `(tactic| c0_step)))
    if !ok then
      st0.restore
      break
    let gs1 ← Lean.Elab.Tactic.getGoals
    if gs1.length > gs0.length then
      st0.restore
      break
local macro "r2b_call" h:term : tactic =>
  `(tactic| (refine LeanQbe.T.wp_call_of_spec _ _ ($h ?_); try c0_let_simp))

/-! ## 1. Shared String, Heap, and UTF-8 Lemmas -/

theorem str_sz_sub1_eq (o : LcnfObj) (hc : StrCanon o) :
    BitVec.ofNat 64 ((strPayload o).length + 1) - (1 : BitVec 64) =
      BitVec.ofNat 64 (strPayload o).length := by
  have hplen := strPayload_length hc
  rcases hc with ⟨_, _, _, _, _, _, ha1, hac, hcap, _, _, _⟩
  have hmax : (strPayload o).length + 1 < 2 ^ 64 := by unfold strMaxCap at hcap; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le]
  · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax,
      Nat.mod_eq_of_lt (by omega : (strPayload o).length < 2 ^ 64),
      show ((1 : BitVec 64)).toNat = 1 from rfl]
    omega
  · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax,
      show ((1 : BitVec 64)).toNat = 1 from rfl]
    omega

theorem str_sz_sub1_toNat_eq (o : LcnfObj) (hc : StrCanon o) :
    (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + ((strPayload o).length + 1)) % 2 ^ 64 =
      (strPayload o).length := by
  have hplen := strPayload_length hc
  rcases hc with ⟨_, _, _, _, _, _, ha1, hac, hcap, _, _, _⟩
  have hmax : (strPayload o).length + 1 < 2 ^ 64 := by unfold strMaxCap at hcap; omega
  rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
  omega

theorem str_sz_sub1_toNat_eq' (o : LcnfObj) (hc : StrCanon o) :
    (BitVec.ofNat 64 ((strPayload o).length + 1) - (1 : BitVec 64)).toNat =
      (strPayload o).length := by
  have hsub := str_sz_sub1_eq o hc
  have hplen := strPayload_length hc
  rcases hc with ⟨_, _, _, _, _, _, ha1, hac, hcap, _, _, _⟩
  have hmax : (strPayload o).length < 2 ^ 64 := by unfold strMaxCap at hcap; omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax]

theorem str_payload_lt_max (o : LcnfObj) (hc : StrCanon o) :
    (strPayload o).length < strMaxCap := by
  have hplen := strPayload_length hc
  rcases hc with ⟨_, _, _, _, _, _, ha1, hac, hcap, _, _, _⟩
  unfold strMaxCap at *; omega

theorem str_cap_lt_64 (o : LcnfObj) (hc : StrCanon o) : o.cap < 2 ^ 64 := by
  have := hc.2.2.2.2.2.2.2.2.1; unfold strMaxCap at this; omega

theorem bv_sub_mod64_of_le' (b : BitVec 64) (a : Nat) (ha : a ≤ b.toNat) :
    (2 ^ 64 - a % 2 ^ 64 + b.toNat) % 2 ^ 64 = b.toNat - a := by
  have hb := b.isLt
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt ha hb)]
  omega

theorem bv_sub_mod64_nat (b a : Nat) (hb : b < 2 ^ 64) (ha : a ≤ b) :
    (2 ^ 64 - a % 2 ^ 64 + b) % 2 ^ 64 = b - a := by
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt ha hb)]
  omega

theorem bv8_zext_mask_eq (b : UInt8) (mask : Nat) :
    (BitVec.setWidth 64 (BitVec.ofNat 8 b.toNat) &&& BitVec.ofNat 64 mask).toNat =
      b.toNat &&& mask := by
  have hblt : b.toNat < 256 := b.toBitVec.isLt
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.testBit_and]
  by_cases hi : i < 8
  · have h64 : i < 64 := by omega
    rw [Nat.mod_eq_of_lt hblt, Nat.mod_eq_of_lt (by omega), Nat.testBit_mod_two_pow]
    simp [h64]
  · have hpow : 256 ≤ 2 ^ i :=
      Nat.le_trans (by decide : 256 ≤ 2 ^ 8) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
    have hbf : b.toNat.testBit i = false := Nat.testBit_lt_two_pow (i := i) (by omega)
    rw [Nat.mod_eq_of_lt hblt]
    simp [hbf]

theorem str_len_lt_64 (o : LcnfObj) (hc : StrCanon o) : o.strLen < 2 ^ 64 :=
  hc.2.2.2.2.2.2.2.2.2.2.2

def strRest (o : LcnfObj) : Mem 64 → Prop :=
  cell64 o.addr o.header ⋆
    cell64 (o.addr + 8#64) (BitVec.ofNat 64 ((strPayload o).length + 1)) ⋆
    cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
    cell64 (o.addr + 24#64) (BitVec.ofNat 64 o.strLen) ⋆
    bytes (o.addr + 32#64 + BitVec.ofNat 64 (strPayload o).length) [(0 : UInt8)] ⋆
    region (o.addr + 32#64 + BitVec.ofNat 64 (strPayload o).length + 1#64)
      (strAllocBytes o.cap - (32 + (strPayload o).length + 1))

theorem strObj_eq_bytes_rest {o : LcnfObj} (hc : StrCanon o) :
    lcnfObjMem o = (bytes (o.addr + 32#64) (strPayload o) ⋆ strRest o) := by
  have hplen : (strPayload o).length = o.arrSize - 1 := strPayload_length hc
  have hdata : o.scalarData = strPayload o ++ [(0 : UInt8)] := str_scalarData_eq_payload_nul hc
  rcases hc with ⟨_, _, _, _, _, htag, ha1, hac, hcap, hsl, _, _⟩
  have htb : o.totalBytes = strAllocBytes o.cap := by
    unfold LcnfObj.totalBytes strAllocBytes; simp [htag, stringTag, arrayTag, sarrayTag]
  have hApp := bytes_append (o.addr + 32#64) (strPayload o) [(0 : UInt8)]
    (by simp only [List.length_singleton]; unfold strMaxCap at hcap; omega)
  have hPos : o.addr + 32#64 + BitVec.ofNat 64 (strPayload o).length + 1#64 =
      o.addr + BitVec.ofNat 64 (32 + o.scalarData.length) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hplen, hsl]
    omega
  rw [lcnfObjMem_string_eq htag, htb, ← hPos, hdata, hApp]
  rw [show o.arrSize = (strPayload o).length + 1 by omega,
    show 32 + (strPayload o ++ [(0 : UInt8)]).length =
      32 + (strPayload o).length + 1 by simp; omega]
  dsimp only [strRest]
  ac_rfl

theorem str_load_hdr {o : LcnfObj} (hc : StrCanon o) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ R) m) : loadVal m i64 o.addr = some o.header := by
  have hmE := lcnfObjMem_string_elim hc hm
  exact loadVal_cell64 (sep_cast hmE (by ac_rfl) :
    (cell64 o.addr o.header ⋆
      (cell64 (o.addr + 8#64) (BitVec.ofNat 64 ((strPayload o).length + 1)) ⋆
        cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
        cell64 (o.addr + 24#64) (BitVec.ofNat 64 o.strLen) ⋆
        bytes (o.addr + 32#64) (strPayload o) ⋆
        bytes (o.addr + 32#64 + BitVec.ofNat 64 (strPayload o).length) [(0 : UInt8)] ⋆
        region (o.addr + 32#64 + BitVec.ofNat 64 (strPayload o).length + 1#64)
          (strAllocBytes o.cap - (32 + (strPayload o).length + 1)) ⋆ R)) m)

theorem str_load_sz {o : LcnfObj} (hc : StrCanon o) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ R) m) :
    loadVal m i64 (o.addr + 8#64) = some (BitVec.ofNat 64 ((strPayload o).length + 1)) := by
  have hmE := lcnfObjMem_string_elim hc hm
  exact loadVal_cell64 (sep_cast hmE (by ac_rfl) :
    (cell64 (o.addr + 8#64) (BitVec.ofNat 64 ((strPayload o).length + 1)) ⋆
      (cell64 o.addr o.header ⋆ cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
        cell64 (o.addr + 24#64) (BitVec.ofNat 64 o.strLen) ⋆
        bytes (o.addr + 32#64) (strPayload o) ⋆
        bytes (o.addr + 32#64 + BitVec.ofNat 64 (strPayload o).length) [(0 : UInt8)] ⋆
        region (o.addr + 32#64 + BitVec.ofNat 64 (strPayload o).length + 1#64)
          (strAllocBytes o.cap - (32 + (strPayload o).length + 1)) ⋆ R)) m)

theorem str_load_cap {o : LcnfObj} (hc : StrCanon o) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ R) m) :
    loadVal m i64 (o.addr + 16#64) = some (BitVec.ofNat 64 o.cap) := by
  have hmE := lcnfObjMem_string_elim hc hm
  exact loadVal_cell64 (sep_cast hmE (by ac_rfl) :
    (cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
      (cell64 o.addr o.header ⋆
        cell64 (o.addr + 8#64) (BitVec.ofNat 64 ((strPayload o).length + 1)) ⋆
        cell64 (o.addr + 24#64) (BitVec.ofNat 64 o.strLen) ⋆
        bytes (o.addr + 32#64) (strPayload o) ⋆
        bytes (o.addr + 32#64 + BitVec.ofNat 64 (strPayload o).length) [(0 : UInt8)] ⋆
        region (o.addr + 32#64 + BitVec.ofNat 64 (strPayload o).length + 1#64)
          (strAllocBytes o.cap - (32 + (strPayload o).length + 1)) ⋆ R)) m)

theorem str_load_len {o : LcnfObj} (hc : StrCanon o) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (lcnfObjMem o ⋆ R) m) :
    loadVal m i64 (o.addr + 24#64) = some (BitVec.ofNat 64 o.strLen) := by
  have hmE := lcnfObjMem_string_elim hc hm
  exact loadVal_cell64 (sep_cast hmE (by ac_rfl) :
    (cell64 (o.addr + 24#64) (BitVec.ofNat 64 o.strLen) ⋆
      (cell64 o.addr o.header ⋆
        cell64 (o.addr + 8#64) (BitVec.ofNat 64 ((strPayload o).length + 1)) ⋆
        cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
        bytes (o.addr + 32#64) (strPayload o) ⋆
        bytes (o.addr + 32#64 + BitVec.ofNat 64 (strPayload o).length) [(0 : UInt8)] ⋆
        region (o.addr + 32#64 + BitVec.ofNat 64 (strPayload o).length + 1#64)
          (strAllocBytes o.cap - (32 + (strPayload o).length + 1)) ⋆ R)) m)

theorem strObj_expose_bytes {o : LcnfObj} (hc : StrCanon o)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfObjMem o ⋆ R) m) :
    ∃ Rest : Mem 64 → Prop,
      (bytes (o.addr + 32#64) (strPayload o) ⋆ Rest) m ∧
      (∀ m', (bytes (o.addr + 32#64) (strPayload o) ⋆ Rest) m' → (lcnfObjMem o ⋆ R) m') := by
  rw [strObj_eq_bytes_rest hc] at hm ⊢
  refine ⟨strRest o ⋆ R, sep_cast hm (by ac_rfl), fun m' hm' => sep_cast hm' (by ac_rfl)⟩

theorem bytes1_merge_region {a : BitVec 64} {b : UInt8} {rem : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (hfit : 1 + rem ≤ 2 ^ 64)
    (hm : (bytes a [b] ⋆ region (a + 1#64) rem ⋆ R) m) :
    (region a (1 + rem) ⋆ R) m := by
  have hm' : (bytes a [b] ⋆ (region (a + 1#64) rem ⋆ R)) m := sep_cast hm (by ac_rfl)
  have hr1 : (region a 1 ⋆ (region (a + 1#64) rem ⋆ R)) m := by
    obtain ⟨m1, m2, rfl, hd, hb1, hr⟩ := hm'
    exact ⟨m1, m2, rfl, hd, bytes_to_region hb1, hr⟩
  have hmg := region_merge_eq (a := a) (n1 := 1) (n2 := rem) (n := 1 + rem) rfl hfit
  rw [show a + BitVec.ofNat 64 1 = a + 1#64 from rfl] at hmg
  have hr1' : ((region a 1 ⋆ region (a + 1#64) rem) ⋆ R) m := sep_cast hr1 (by ac_rfl)
  rw [hmg] at hr1'
  exact hr1'

theorem utf8LenNat_bounds (cp : Nat) : 1 ≤ utf8LenNat cp ∧ utf8LenNat cp ≤ 4 := by
  unfold utf8LenNat
  repeat (first | omega | split)

theorem decColdRel_singleton_nil {s : BitVec 64} {sObj : LcnfObj}
    {objs' : List LcnfObj} (haddr : sObj.addr = s) (hrc1 : sObj.rc = 1#32)
    (hcold : DecColdRel s [sObj] objs') : objs' = [] := by
  cases objs' with
  | nil => rfl
  | cons o' tl =>
    have hmem := hcold.2.2.2.2.1 o' (by simp)
    rcases hmem with ⟨_, hne, o, hoMem, hoEq, _⟩
    simp only [List.mem_singleton] at hoMem
    rcases hoMem with rfl
    exact absurd (hoEq.symm.trans haddr) hne

theorem decObjRel_singleton_heap {s : BitVec 64} {sObj : LcnfObj}
    {objs' : List LcnfObj} (hcanon : StrCanon sObj) (haddr : sObj.addr = s)
    (hdec : DecObjRel s [sObj] objs') :
    lcnfHeap objs' =
      if sObj.rc = 1#32 then emp else lcnfObjMem (sObj.withRc (decNonExclRc sObj.rc)) := by
  have hs0 : s ≠ 0#64 := haddr ▸ hcanon.1
  have hs1 : (s &&& 1#64) = 0#64 := haddr ▸ bv64_and1_zero_of_mod8 hcanon.2.1
  have hnot : ¬ (s = 0#64 ∨ (s &&& 1#64) ≠ 0#64) := by simp [hs0, hs1]
  unfold DecObjRel at hdec
  rw [ite_eq_right hnot] at hdec
  rcases hdec with ⟨obj, hoMem, _, hbr⟩
  simp only [List.mem_singleton] at hoMem
  rw [hoMem] at hbr
  by_cases hrc1 : sObj.rc = 1#32
  · rw [ite_eq_left hrc1] at hbr ⊢
    rw [decColdRel_singleton_nil haddr hrc1 hbr]
    rfl
  · rw [ite_eq_right hrc1] at hbr ⊢
    rw [hbr]
    simp only [List.map_cons, List.map_nil, haddr, ↓reduceIte, lcnfHeap, sep_emp]

theorem rcSound_singleton_str {s : BitVec 64} {sObj : LcnfObj}
    (hcanon : StrCanon sObj) (haddr : sObj.addr = s) : RcSound s [sObj] := by
  rw [← handlesRcSound_singleton_iff]
  refine ⟨?_, ?_⟩
  · intro p hp _ f hf
    simp only [List.mem_singleton] at hp
    rw [hp] at hf
    simp [LcnfObj.childFields, hcanon.2.2.2.2.2.1, stringTag, closureTag, arrayTag] at hf
  · intro y hy hpos
    simp only [List.mem_singleton] at hy
    have hnp : nonPersistRefs [sObj] y.addr = 0 := by
      rw [hy]
      simp [nonPersistRefs, LcnfObj.childFields, hcanon.2.2.2.2.2.1,
        stringTag, closureTag, arrayTag]
    have hcnt : [s].count y.addr = 1 := by rw [hy, haddr]; simp
    rw [hnp, hcnt, hy]
    rw [hy] at hpos
    have hne0 : sObj.rc.toNat ≠ 0 := by
      intro h0
      have he : sObj.rc = 0#32 := BitVec.eq_of_toNat_eq h0
      rw [he] at hpos
      exact absurd hpos (by decide)
    omega

theorem lcnfHeapClosed_singleton_str {sObj : LcnfObj} (hcanon : StrCanon sObj) :
    lcnfHeapClosed [sObj] := by
  intro o ho f hf
  simp only [List.mem_singleton] at ho
  rw [ho] at hf
  simp [LcnfObj.childFields, hcanon.2.2.2.2.2.1, stringTag, closureTag, arrayTag] at hf

theorem mem_eraseIdx_of_addr_ne {objs : List LcnfObj} {k1 : Nat} (hk1 : k1 < objs.length)
    {o2 : LcnfObj} (h2 : o2 ∈ objs) (hne : o2.addr ≠ objs[k1].addr) :
    o2 ∈ objs.eraseIdx k1 := by
  obtain ⟨k2, hk2, hobj2⟩ := List.getElem_of_mem h2
  have hkNe : k2 ≠ k1 := by intro heq; apply hne; subst heq; rw [← hobj2]
  rw [List.eraseIdx_eq_take_drop_succ, List.mem_append]
  rcases Nat.lt_or_gt_of_ne hkNe with hlt | hgt
  · left
    have hltTake : k2 < (objs.take k1).length := by rw [List.length_take]; omega
    have heq : (objs.take k1)[k2] = o2 := by rw [List.getElem_take, hobj2]
    rw [← heq]
    exact List.getElem_mem hltTake
  · right
    have hltDrop : k2 - (k1 + 1) < (objs.drop (k1 + 1)).length := by
      rw [List.length_drop]; omega
    have heq : (objs.drop (k1 + 1))[k2 - (k1 + 1)] = o2 := by
      rw [← hobj2, List.getElem_drop]; congr 1; omega
    rw [← heq]
    exact List.getElem_mem hltDrop

theorem nodup_map_getElem_eq {α β : Type} (f : α → β) :
    ∀ {xs : List α}, (xs.map f).Nodup → ∀ {i j : Nat} (hi : i < xs.length) (hj : j < xs.length),
      f xs[i] = f xs[j] → i = j
  | [], _, _, _, _, hi, _ => by simp at hi
  | _ :: _, _, 0, 0, _, _, _ => rfl
  | _ :: xs, hnd, 0, j + 1, _, hj, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hj' : j < xs.length := by simp at hj; omega
    exact absurd ⟨xs[j], List.getElem_mem hj', h.symm⟩ hnd.1
  | _ :: xs, hnd, i + 1, 0, hi, _, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hi' : i < xs.length := by simp at hi; omega
    exact absurd ⟨xs[i], List.getElem_mem hi', h⟩ hnd.1
  | _ :: xs, hnd, i + 1, j + 1, hi, hj, h => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    exact congrArg Nat.succ
      (nodup_map_getElem_eq f hnd.2 (by simp at hi; omega) (by simp at hj; omega) h)

theorem list_set_eq_map_of_nodup {objs : List LcnfObj} {k : Nat} (hk : k < objs.length)
    (rObj : LcnfObj) (hnd : (objs.map LcnfObj.addr).Nodup) :
    objs.set k rObj = objs.map (fun o => if o.addr = objs[k].addr then rObj else o) := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp only [List.getElem_set, List.getElem_map]
    split
    · next heq => subst heq; simp
    · next hne =>
      have hiLen : i < objs.length := by simp at hi2; exact hi2
      have hneAddr : objs[i].addr ≠ objs[k].addr := by
        intro ha; exact hne (nodup_map_getElem_eq LcnfObj.addr hnd hk hiLen ha.symm)
      simp [hneAddr]

theorem eraseIdx_set_eq_self (xs : List LcnfObj) (k : Nat) (v : LcnfObj) :
    (xs.set k v).eraseIdx k = xs.eraseIdx k := by
  rw [List.eraseIdx_eq_take_drop_succ, List.eraseIdx_eq_take_drop_succ,
    List.take_set_of_le (Nat.le_refl _), List.drop_set_of_lt (Nat.lt_succ_self _)]

theorem lcnfHeap_focus_two {objs : List LcnfObj} {o1 o2 : LcnfObj}
    (h1 : o1 ∈ objs) (h2 : o2 ∈ objs) (hne : o1.addr ≠ o2.addr)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (lcnfHeap objs ⋆ R) m) :
    ∃ (objsRem : List LcnfObj),
      lcnfHeap objs = lcnfObjMem o1 ⋆ lcnfObjMem o2 ⋆ lcnfHeap objsRem ∧
      (lcnfObjMem o1 ⋆ lcnfObjMem o2 ⋆ lcnfHeap objsRem ⋆ R) m := by
  obtain ⟨k1, hk1, hobj1⟩ := List.getElem_of_mem h1
  have h2Er : o2 ∈ objs.eraseIdx k1 := by
    apply mem_eraseIdx_of_addr_ne hk1 h2
    rw [hobj1]; exact hne.symm
  obtain ⟨k2, hk2, hobj2⟩ := List.getElem_of_mem h2Er
  let rest := (objs.eraseIdx k1).eraseIdx k2
  have heq : lcnfHeap objs = lcnfObjMem o1 ⋆ lcnfObjMem o2 ⋆ lcnfHeap rest := by
    rw [lcnfHeap_focus objs hk1, hobj1, ← lcnfHeap_eraseIdx objs]
    rw [lcnfHeap_focus (objs.eraseIdx k1) hk2, hobj2, ← lcnfHeap_eraseIdx (objs.eraseIdx k1)]
    ext m'
    rw [sep_assoc]
  have hm' : (lcnfObjMem o1 ⋆ lcnfObjMem o2 ⋆ lcnfHeap rest ⋆ R) m := by
    rw [heq] at hm; exact sep_cast hm (by ac_rfl)
  exact ⟨rest, heq, hm'⟩

theorem lcnfObjMem_mkStr_replace {objs : List LcnfObj} {k : Nat} (hk : k < objs.length)
    {sObj rObj : LcnfObj} (hobj : objs[k] = sObj)
    (hnd : (objs.map LcnfObj.addr).Nodup) :
    lcnfHeap (objs.map fun o => if o.addr = sObj.addr then rObj else o) =
      lcnfObjMem rObj ⋆ lcnfHeap (objs.eraseIdx k) := by
  have hset : objs.set k rObj = objs.map fun o => if o.addr = sObj.addr then rObj else o := by
    rw [← hobj]
    exact list_set_eq_map_of_nodup hk rObj hnd
  rw [← hset, lcnfHeap_focus (objs.set k rObj) (by simpa), List.getElem_set_self,
    ← lcnfHeap_eraseIdx (objs.set k rObj), eraseIdx_set_eq_self]

theorem strGrowCap_props (rc : BitVec 32) (oldCap need : Nat)
    (hneed : need ≤ strMaxCap) :
    need ≤ strGrowCap rc oldCap need ∧ strGrowCap rc oldCap need ≤ strMaxCap := by
  unfold strGrowCap
  split <;> unfold strMaxCap at * <;> omega

theorem strGrowCap_case_dbl_cap {oldCap newSz : Nat}
    (hd : newSz + 1 < oldCap * 2) (hc : strMaxCap < oldCap * 2) :
    strGrowCap 1#32 oldCap (newSz + 1) = strMaxCap := by
  unfold strGrowCap strMaxCap at *; simp; omega

theorem strGrowCap_case_dbl {oldCap newSz : Nat}
    (hd : newSz + 1 < oldCap * 2) (hc : oldCap * 2 ≤ strMaxCap) :
    strGrowCap 1#32 oldCap (newSz + 1) = oldCap * 2 := by
  unfold strGrowCap strMaxCap at *; simp; omega

theorem strGrowCap_case_new {oldCap newSz : Nat}
    (hd : oldCap * 2 ≤ newSz + 1) (hc : newSz + 1 ≤ strMaxCap) :
    strGrowCap 1#32 oldCap (newSz + 1) = newSz + 1 := by
  unfold strGrowCap strMaxCap at *; simp; omega

theorem bv_ofNat_add1_mod64 (len : Nat) (h : len < 2 ^ 64) :
    BitVec.ofNat 64 len + 1#64 = BitVec.ofNat 64 ((len + 1) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt h, Nat.mod_mod]

theorem str_sub_mod_lt (a b : Nat) (ha : a < 2 ^ 64) (hb : b ≤ a) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b).toNat = a - b := by
  rw [BitVec.toNat_sub_of_le]
  · simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]
  · rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]
    exact hb

theorem cmpByteSlices_eq_one_len :
    ∀ (xs ys : List UInt8), cmpByteSlices xs ys = 1#64 → xs.length = ys.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [cmpByteSlices] at h
  | _ :: _, [], h => by simp [cmpByteSlices] at h
  | x :: xs, y :: ys, h => by
    simp only [cmpByteSlices] at h
    split at h
    · cases h
    · split at h
      · cases h
      · simp [cmpByteSlices_eq_one_len xs ys h]

theorem utf8CountFrom_step {bs : List UInt8} {idx : Nat} (h : idx < bs.length) :
    utf8CountFrom bs idx = 1 + utf8CountFrom bs (idx + utf8DecodeStepAt bs idx) := by
  unfold utf8CountFrom
  conv => lhs; unfold utf8DecodeFrom
  rw [dite_eq_left h, List.length_cons, Nat.add_comm]

theorem utf8CountFrom_end {bs : List UInt8} {idx : Nat} (h : ¬ idx < bs.length) :
    utf8CountFrom bs idx = 0 := by
  unfold utf8CountFrom
  conv => lhs; unfold utf8DecodeFrom
  rw [dite_eq_right h]; rfl

theorem str_copy_from_heap {objs : List LcnfObj} {sObj : LcnfObj}
    {dst s : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {outs : List Ty} {Q : Post outs} {X : XPost} {kRest : Expr Val Cont outs}
    (hsMem : sObj ∈ objs) (hsAddr : sObj.addr = s) (hcanon : StrCanon sObj)
    (hm : (region dst (strPayload sObj).length ⋆ lcnfHeap objs ⋆ R) m)
    (hk : ∀ m', (bytes dst (strPayload sObj) ⋆ lcnfHeap objs ⋆ R) m' → wp rtR2bEnv Q X kRest m') :
    wp rtR2bEnv Q X
      (Expr.call "r2b_mem_copy_bytes" (as := [i64, i64, i64]) (bs := [])
        (Arg.var dst, Arg.var (s + 32#64), Arg.var (BitVec.ofNat 64 (strPayload sObj).length), ())
        (fun _ => kRest)) m := by
  obtain ⟨k, hkLen, hobjk⟩ := List.getElem_of_mem hsMem
  have hfocus : lcnfHeap objs = lcnfObjMem sObj ⋆ lcnfHeap (objs.eraseIdx k) := by
    rw [lcnfHeap_focus objs hkLen, hobjk, ← lcnfHeap_eraseIdx objs]
  have hmExp : (bytes (s + 32#64) (strPayload sObj) ⋆
      (strRest sObj ⋆ lcnfHeap (objs.eraseIdx k) ⋆ region dst (strPayload sObj).length ⋆ R)) m := by
    rw [hfocus, strObj_eq_bytes_rest hcanon, hsAddr] at hm
    exact sep_cast hm (by ac_rfl)
  have hszLt := str_payload_lt_max sObj hcanon
  have hszTo : (BitVec.ofNat 64 (strPayload sObj).length).toNat = (strPayload sObj).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold strMaxCap at hszLt; omega)]
  r2b_call rtR2bEnv_r2b_mem_copy_bytes
  dsimp only [r2MemCopyBytesSpec, vals, Tup.map, Arg.val]
  refine ⟨strPayload sObj, (strPayload sObj).length,
    strRest sObj ⋆ lcnfHeap (objs.eraseIdx k) ⋆ R, hszTo.symm, Nat.le_of_eq hszTo,
    by unfold strMaxCap at hszLt; omega, sep_cast hmExp (by ac_rfl), fun m' hm' => ?_⟩
  rw [hszTo, Nat.sub_self, region_zero] at hm'
  simp only [sep_emp] at hm'
  have hmClose : (lcnfHeap objs ⋆ bytes dst (strPayload sObj) ⋆ R) m' := by
    rw [hfocus, strObj_eq_bytes_rest hcanon, hsAddr]
    exact sep_cast hm' (by ac_rfl)
  exact hk m' (sep_cast hmClose (by ac_rfl))


theorem bv64_sub_ule_true {M a b : Nat} (hM : M < 2 ^ 64) (ha : a ≤ M) (hb : b < 2 ^ 64)
    (h : M - a ≤ b) :
    ((BitVec.ofNat 64 M - BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b)) = true := by
  have heq : (BitVec.ofNat 64 M - BitVec.ofNat 64 a).toNat = M - a := by
    rw [BitVec.toNat_sub_of_le]
    · simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hM, Nat.mod_eq_of_lt (by omega : a < 2 ^ 64)]
    · rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hM, Nat.mod_eq_of_lt (by omega : a < 2 ^ 64)]
      exact ha
  rw [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, heq, decide_eq_true_iff]
  exact h

theorem bv64_sub_ule_false {M a b : Nat} (hM : M < 2 ^ 64) (ha : a ≤ M) (hb : b < 2 ^ 64)
    (h : ¬ (M - a ≤ b)) :
    ((BitVec.ofNat 64 M - BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b)) = false := by
  have heq : (BitVec.ofNat 64 M - BitVec.ofNat 64 a).toNat = M - a := by
    rw [BitVec.toNat_sub_of_le]
    · simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hM, Nat.mod_eq_of_lt (by omega : a < 2 ^ 64)]
    · rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hM, Nat.mod_eq_of_lt (by omega : a < 2 ^ 64)]
      exact ha
  rw [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, heq, decide_eq_false_iff_not]
  exact h

theorem r2b_wp_jnz_true {env : Env} {outs : List Ty} {Q : Post outs} {X : XPost}
    {t f : Expr Val Cont outs} {m : Mem 64} (h : wp env Q X t m) :
    wp env Q X (Expr.jnz (Arg.var true) t f) m := by
  dsimp only [LeanQbe.T.wp, Arg.val]; exact ⟨fun _ => h, fun hc => absurd hc (by decide)⟩

theorem r2b_wp_jnz_false {env : Env} {outs : List Ty} {Q : Post outs} {X : XPost}
    {t f : Expr Val Cont outs} {m : Mem 64} (h : wp env Q X f m) :
    wp env Q X (Expr.jnz (Arg.var false) t f) m := by
  dsimp only [LeanQbe.T.wp, Arg.val]; exact ⟨fun hc => absurd hc (by decide), fun _ => h⟩

/-! ## 2. `lcnf_string_push` WP Proof -/

theorem lcnf_string_push_wp :
    ∀ xs m Q X, lcnfStringPushSpec xs m Q X → Func.wp rtR2bEnv lcnf_string_push_body xs m Q X := by
  intro ⟨rt, s, c, ⟨⟩⟩
  revert c; dsimp only [Val]; intro c m Q X ⟨st, sObj, R, haddr, hcanon, hm, hPost⟩
  subst haddr
  dsimp only [Func.wp, lcnf_string_push_body]
  change LeanQbe.T.wp _ _ _ _ _
  let bs0 := strPayload sObj
  let cp := (c &&& 0xffffffff#64).toNat
  let encBs := utf8EncodeBytes cp
  let clen := utf8LenNat cp
  let newSz := bs0.length + clen
  have hencLen : encBs.length = clen := utf8EncodeBytes_length cp
  have hclenBnd := utf8LenNat_bounds cp
  have hszLt := str_payload_lt_max sObj hcanon
  have hcapLt := str_cap_lt_64 sObj hcanon
  have hlenLt := str_len_lt_64 sObj hcanon
  have hnewLenBs : (bs0 ++ encBs).length = newSz := by simp [newSz, hencLen]
  have hwf := hcanon.wf
  have hrcEq := header_and_mask_eq_rc sObj hwf
  have hmS : (lcnfObjMem sObj ⋆ (rtC0Inv rt st ⋆ R)) m := sep_cast hm (by ac_rfl)
  apply wp_load_of (str_load_sz hcanon hmS)
  r2b_steps
  simp only [str_sz_sub1_eq sObj hcanon] at *
  apply wp_load_of (str_load_cap hcanon hmS)
  r2b_steps
  apply wp_load_of (str_load_len hcanon hmS)
  r2b_steps
  apply wp_load_of (str_load_hdr hcanon hmS)
  r2b_steps
  r2b_call rtR2bEnv_r2b_utf8_len
  dsimp only [r2bUtf8LenSpec, vals, Tup.map, Arg.val]
  have hsubClen : ((268435415 : BitVec 64) - BitVec.ofNat 64 clen).toNat = 268435415 - clen :=
    str_sub_mod_lt 268435415 clen (by decide) (by omega)
  have hszTo : (BitVec.ofNat 64 bs0.length).toNat = bs0.length := by
    dsimp only [bs0]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold strMaxCap at hszLt; omega)]
  have hnewSzEq : BitVec.ofNat 64 (strPayload sObj).length + BitVec.ofNat 64 clen =
      BitVec.ofNat 64 newSz :=
    (BitVec.ofNat_add (strPayload sObj).length clen).symm
  dsimp only [clen, cp] at hnewSzEq
  have hclenLe : clen ≤ 268435415 := Nat.le_trans hclenBnd.2 (by decide)
  have hsz64 : (strPayload sObj).length < 2 ^ 64 := by
    unfold strMaxCap at hszLt; exact Nat.lt_trans hszLt (by decide)
  have hclen64 : clen < 2 ^ 64 := Nat.lt_of_le_of_lt hclenBnd.2 (by decide)
  have hsubClenMod : (2 ^ 64 - clen % 2 ^ 64 + 268435415) % 2 ^ 64 = 268435415 - clen :=
    bv_sub_mod64_nat 268435415 clen (by decide) hclenLe
  by_cases hov : strMaxCap ≤ newSz
  · rw [hnewLenBs, ite_eq_left hov] at hPost
    have hge : 268435415 - clen ≤ bs0.length := by
      dsimp only [newSz, bs0, clen] at hov ⊢; unfold strMaxCap at hov; omega
    r2b_to_group
    have hcond :
        ((268435415 - BitVec.ofNat 64 (utf8LenNat (c &&& 4294967295).toNat)).ule
          (BitVec.ofNat 64 (strPayload sObj).length)) = true := by
      rw [show (268435415 : BitVec 64) = BitVec.ofNat 64 268435415 from rfl,
        show (4294967295 : BitVec 64) = 4294967295#64 from rfl]
      exact bv64_sub_ule_true (by decide) hclenLe hsz64 hge
    rw [hcond]
    exact r2b_wp_jnz_true hPost
  · rw [hnewLenBs, ite_eq_right hov] at hPost
    have hnotGe : ¬ 268435415 - clen ≤ bs0.length := by
      dsimp only [newSz, bs0, clen] at hov ⊢; unfold strMaxCap at hov; omega
    have hnewLt : newSz < strMaxCap := by
      dsimp only [newSz, bs0, clen] at hov ⊢; unfold strMaxCap at hov ⊢; omega
    have hnew64 : newSz < 2 ^ 64 := by
      unfold strMaxCap at hnewLt; exact Nat.lt_trans hnewLt (by decide)
    have hnew1LeMax : newSz + 1 ≤ strMaxCap := Nat.succ_le_of_lt hnewLt
    have hnew164 : newSz + 1 < 2 ^ 64 :=
      Nat.lt_of_le_of_lt hnew1LeMax (by unfold strMaxCap; decide)
    have hnewTo : (BitVec.ofNat 64 newSz).toNat = newSz := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnew64]
    have hnew1To : (BitVec.ofNat 64 newSz + 1#64).toNat = newSz + 1 := by
      rw [bv_ofNat_add1_mod64 newSz hnew64, BitVec.toNat_ofNat, Nat.mod_mod,
        Nat.mod_eq_of_lt hnew164]
    have hcapTo : (BitVec.ofNat 64 sObj.cap).toNat = sObj.cap := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcapLt]
    r2b_to_group
    have hcond :
        ((268435415 - BitVec.ofNat 64 (utf8LenNat (c &&& 4294967295).toNat)).ule
          (BitVec.ofNat 64 (strPayload sObj).length)) = false := by
      rw [show (268435415 : BitVec 64) = BitVec.ofNat 64 268435415 from rfl,
        show (4294967295 : BitVec 64) = 4294967295#64 from rfl]
      exact bv64_sub_ule_false (by decide) hclenLe hsz64 hnotGe
    rw [hcond]
    apply r2b_wp_jnz_false
    focus
      try simp only [hnewSzEq] at *
      have hnewSzEq' : BitVec.ofNat 64 (strPayload sObj).length +
          BitVec.ofNat 64 (utf8LenNat (c &&& 4294967295#64).toNat) = BitVec.ofNat 64 newSz :=
        (BitVec.ofNat_add (strPayload sObj).length _).symm
      by_cases hinp : sObj.rc = 1#32 ∧ newSz + 1 ≤ sObj.cap
      · rw [ite_eq_left hinp] at hPost
        have hrc1 : sObj.rc = 1#32 := hinp.1
        have hcapOk : newSz + 1 ≤ sObj.cap := hinp.2
        rcases hPost with ⟨_, hpostK⟩
        have hmask1 : (sObj.header &&& 4294967295#64) = 1#64 := by rw [hrcEq, hrc1]; rfl
        have hhdrWord : sObj.header = strHeaderWord := by
          rcases hcanon with ⟨_, _, _, hcs, ho, htag, _, _, _, _, _, _⟩
          dsimp only [LcnfObj.header, strHeaderWord]
          rw [hrc1, hcs, ho, htag]; decide
        have hmElim := lcnfObjMem_string_elim hcanon hmS
        have hregFit : 1 + (strAllocBytes sObj.cap - (32 + bs0.length + 1)) ≤ 2 ^ 64 := by
          have := hc_cap_bound sObj.cap hcanon.2.2.2.2.2.2.2.2.1; omega
        have hmMerge : (region (sObj.addr + 32#64 + BitVec.ofNat 64 bs0.length)
              (1 + (strAllocBytes sObj.cap - (32 + bs0.length + 1))) ⋆
            (cell64 sObj.addr sObj.header ⋆
              cell64 (sObj.addr + 8#64) (BitVec.ofNat 64 (bs0.length + 1)) ⋆
              cell64 (sObj.addr + 16#64) (BitVec.ofNat 64 sObj.cap) ⋆
              cell64 (sObj.addr + 24#64) (BitVec.ofNat 64 sObj.strLen) ⋆
              bytes (sObj.addr + 32#64) bs0 ⋆ rtC0Inv rt st ⋆ R)) m :=
          bytes1_merge_region hregFit (sep_cast hmElim (by ac_rfl))
        have hremEq : 1 + (strAllocBytes sObj.cap - (32 + bs0.length + 1)) =
            strAllocBytes sObj.cap - (32 + bs0.length) := by
          have := strAllocBytes_ge sObj.cap
          have := hcanon.2.2.2.2.2.2.2.1
          have := strPayload_length hcanon
          omega
        rw [hremEq] at hmMerge
        have hallocGe := strAllocBytes_ge sObj.cap
        have hleReg : encBs.length ≤ strAllocBytes sObj.cap - (32 + bs0.length) := by
          rw [hencLen]; omega
        have hfitReg : strAllocBytes sObj.cap - (32 + bs0.length) ≤ 2 ^ 64 := by
          have := hc_cap_bound sObj.cap hcanon.2.2.2.2.2.2.2.2.1; omega
        have h1rem : 1 ≤ strAllocBytes sObj.cap - (32 + bs0.length) - clen := by omega
        have hfit1 : strAllocBytes sObj.cap - (32 + bs0.length) - clen ≤ 2 ^ 64 :=
          Nat.le_trans (Nat.sub_le _ _) hfitReg
        r2b_to_group
        c0_step
        r2b_to_group
        c0_step
        c0_step
        · r2b_to_group
          · r2b_call rtR2bEnv_r2b_utf8_write
            dsimp only [r2bUtf8WriteSpec, vals, Tup.map, Arg.val]
            have hcpEq : (c &&& (4294967295 : BitVec 64)).toNat = cp := rfl
            rw [hcpEq]
            refine ⟨strAllocBytes sObj.cap - (32 + bs0.length), _, hleReg, hfitReg, hmMerge,
              fun m1 hm1 => ?_⟩
            rw [hencLen] at hm1
            r2b_steps
            have hptrL : sObj.addr + 32 = sObj.addr + 32#64 := rfl
            dsimp only [encBs, clen, bs0, cp] at hm1 ⊢
            rw [hptrL] at hm1
            have hmReg1 : (region (sObj.addr + 32#64 + BitVec.ofNat 64 bs0.length +
                  BitVec.ofNat 64 clen) (strAllocBytes sObj.cap - (32 + bs0.length) - clen) ⋆
                (bytes (sObj.addr + 32#64 + BitVec.ofNat 64 bs0.length) encBs ⋆
                  cell64 sObj.addr sObj.header ⋆
                  cell64 (sObj.addr + 8#64) (BitVec.ofNat 64 (bs0.length + 1)) ⋆
                  cell64 (sObj.addr + 16#64) (BitVec.ofNat 64 sObj.cap) ⋆
                  cell64 (sObj.addr + 24#64) (BitVec.ofNat 64 sObj.strLen) ⋆
                  bytes (sObj.addr + 32#64) bs0 ⋆ rtC0Inv rt st ⋆ R)) m1 := by
              dsimp only [encBs, clen, bs0, cp]
              exact sep_cast hm1 (by ac_rfl)
            obtain ⟨bs1, hbs1Len, hmPop⟩ := region_pop_bytes h1rem hfit1 hmReg1
            rcases bs1 with _ | ⟨bNul, _ | _⟩ <;> simp at hbs1Len
            have hptrNew : sObj.addr + 32#64 + BitVec.ofNat 64 newSz =
                sObj.addr + 32#64 + BitVec.ofNat 64 bs0.length + BitVec.ofNat 64 clen := by
              apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod,
                newSz, bs0, clen, Nat.add_assoc]
            have hmNul : (bytes (sObj.addr + 32#64 + BitVec.ofNat 64 newSz) [bNul] ⋆
                (region (sObj.addr + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                    (strAllocBytes sObj.cap - (32 + bs0.length) - clen - 1) ⋆
                  bytes (sObj.addr + 32#64 + BitVec.ofNat 64 bs0.length) encBs ⋆
                  cell64 sObj.addr sObj.header ⋆
                  cell64 (sObj.addr + 8#64) (BitVec.ofNat 64 (bs0.length + 1)) ⋆
                  cell64 (sObj.addr + 16#64) (BitVec.ofNat 64 sObj.cap) ⋆
                  cell64 (sObj.addr + 24#64) (BitVec.ofNat 64 sObj.strLen) ⋆
                  bytes (sObj.addr + 32#64) bs0 ⋆ rtC0Inv rt st ⋆ R)) m1 := by
              rw [hptrNew]; exact sep_cast hmPop (by ac_rfl)
            obtain ⟨hokNul, hm2⟩ := r2b_c0_store_bytes_single (BitVec.truncate 8 0#64) hmNul
            try simp only [show (32 : BitVec 64) = 32#64 from rfl, hnewSzEq']
            apply wp_store_sep ⟨hokNul, hm2⟩
            intro m2 hm2'
            r2b_steps
            have hmCell8 : (cell64 (sObj.addr + 8#64) (BitVec.ofNat 64 (bs0.length + 1)) ⋆
                (bytes (sObj.addr + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
                  region (sObj.addr + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                    (strAllocBytes sObj.cap - (32 + bs0.length) - clen - 1) ⋆
                  bytes (sObj.addr + 32#64 + BitVec.ofNat 64 bs0.length) encBs ⋆
                  cell64 sObj.addr sObj.header ⋆
                  cell64 (sObj.addr + 16#64) (BitVec.ofNat 64 sObj.cap) ⋆
                  cell64 (sObj.addr + 24#64) (BitVec.ofNat 64 sObj.strLen) ⋆
                  bytes (sObj.addr + 32#64) bs0 ⋆ rtC0Inv rt st ⋆ R)) m2 := by
              have h0eq : UInt8.ofNat (BitVec.truncate 8 0#64).toNat = (0 : UInt8) := by decide
              rw [h0eq] at hm2'
              exact sep_cast hm2' (by ac_rfl)
            obtain ⟨hok8, hm3⟩ := r2_c0_store_cell64_add8 (BitVec.ofNat 64 newSz + 1#64) hmCell8
            try simp only [show (8 : BitVec 64) = 8#64 from rfl,
              show (1 : BitVec 64) = 1#64 from rfl]
            apply wp_store_sep ⟨hok8, hm3⟩
            intro m3 hm3'
            r2b_steps
            have hmCell24 : (cell64 (sObj.addr + 24#64) (BitVec.ofNat 64 sObj.strLen) ⋆
                (cell64 (sObj.addr + 8#64) (BitVec.ofNat 64 newSz + 1#64) ⋆
                  bytes (sObj.addr + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
                  region (sObj.addr + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                    (strAllocBytes sObj.cap - (32 + bs0.length) - clen - 1) ⋆
                  bytes (sObj.addr + 32#64 + BitVec.ofNat 64 bs0.length) encBs ⋆
                  cell64 sObj.addr sObj.header ⋆
                  cell64 (sObj.addr + 16#64) (BitVec.ofNat 64 sObj.cap) ⋆
                  bytes (sObj.addr + 32#64) bs0 ⋆ rtC0Inv rt st ⋆ R)) m3 :=
              sep_cast hm3' (by ac_rfl)
            obtain ⟨hok24, hm4⟩ :=
              r2b_c0_store_cell64_add24 (BitVec.ofNat 64 sObj.strLen + 1#64) hmCell24
            try simp only [show (24 : BitVec 64) = 24#64 from rfl]
            apply wp_store_sep ⟨hok24, hm4⟩
            intro m4 hm4'
            r2b_steps
            let newPay := bs0 ++ encBs
            let newLen := (sObj.strLen + 1) % 2 ^ 64
            let rObj := mkStrObj sObj.addr 1#32 sObj.cap newPay newLen
            have hcanR : StrCanon rObj :=
              mkStrObj_canon hcanon.1 hcanon.2.1 (by decide)
                (by rw [hnewLenBs]; exact hcapOk) hcanon.2.2.2.2.2.2.2.2.1
                (Nat.mod_lt _ (by decide))
            have hmR : (rtC0Inv rt st ⋆ lcnfObjMem rObj ⋆ emp ⋆ R) m4 := by
              have hparts : (cell64 sObj.addr strHeaderWord ⋆
                  cell64 (sObj.addr + 8#64) (BitVec.ofNat 64 (newPay.length + 1)) ⋆
                  cell64 (sObj.addr + 16#64) (BitVec.ofNat 64 sObj.cap) ⋆
                  cell64 (sObj.addr + 24#64) (BitVec.ofNat 64 newLen) ⋆
                  bytes (sObj.addr + 32#64) newPay ⋆
                  bytes (sObj.addr + 32#64 + BitVec.ofNat 64 newPay.length) [(0 : UInt8)] ⋆
                  region (sObj.addr + 32#64 + BitVec.ofNat 64 newPay.length + 1#64)
                    (strAllocBytes sObj.cap - (32 + newPay.length + 1)) ⋆
                  (rtC0Inv rt st ⋆ R)) m4 := by
                rw [hnewLenBs]
                have hApp := bytes_append (sObj.addr + 32#64) bs0 encBs
                  (by rw [hencLen]; unfold strMaxCap at hnewLt; omega)
                rw [bv_ofNat_add1_mod64 newSz hnew64, Nat.mod_eq_of_lt (by omega)] at hm4'
                rw [bv_ofNat_add1_mod64 sObj.strLen hlenLt] at hm4'
                have hremEnd : strAllocBytes sObj.cap - (32 + bs0.length) - clen - 1 =
                    strAllocBytes sObj.cap - (32 + newSz + 1) := by dsimp only [newSz]; omega
                rw [hremEnd] at hm4'
                have hm4a : (cell64 sObj.addr sObj.header ⋆
                    cell64 (sObj.addr + 8#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
                    cell64 (sObj.addr + 16#64) (BitVec.ofNat 64 sObj.cap) ⋆
                    cell64 (sObj.addr + 24#64) (BitVec.ofNat 64 ((sObj.strLen + 1) % 2 ^ 64)) ⋆
                    (bytes (sObj.addr + 32#64) bs0 ⋆
                      bytes (sObj.addr + 32#64 + BitVec.ofNat 64 bs0.length) encBs) ⋆
                    bytes (sObj.addr + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
                    region (sObj.addr + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                      (strAllocBytes sObj.cap - (32 + newSz + 1)) ⋆
                    (rtC0Inv rt st ⋆ R)) m4 := sep_cast hm4' (by ac_rfl)
                rw [← hhdrWord]
                rwa [← hApp] at hm4a
              have hmObj := mkStrObj_mem_of_parts hcanon.2.2.2.2.2.2.2.2.1
                (by rw [hnewLenBs]; exact hcapOk) hparts
              rw [sep_emp]
              exact sep_cast hmObj (by ac_rfl)
            exact hpostK sObj.addr st m4 hcanon.1 hcanon.2.1
              (RtC0State.PreservesMeta.refl st) (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
              hcanR (by rw [ite_eq_left hrc1]; exact sep_cast hmR (by ac_rfl))


      · rw [ite_eq_right hinp] at hPost
        rcases hPost with ⟨hneg, hpostK⟩
        obtain ⟨hav, hrc1Cap⟩ := hneg hinp
        let newCap := strGrowCap sObj.rc sObj.cap (newSz + 1)
        have hcapBnd := strGrowCap_props sObj.rc sObj.cap (newSz + 1)
          (by unfold strMaxCap at hnewLt ⊢; omega)
        have hnewCapLt64 : newCap < 2 ^ 64 := by unfold strMaxCap at *; omega
        have hnewCapTo : (BitVec.ofNat 64 newCap).toNat = newCap := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnewCapLt64]
        r2b_to_group
        c0_step
        r2b_to_group
        c0_step
        c0_step
        all_goals
          first
          | (have hcRc : (sObj.header &&& 4294967295#64) = 1#64 := by
               rw [show (4294967295 : BitVec 64) = 4294967295#64 from rfl,
                 show (1 : BitVec 64) = 1#64 from rfl] at hc
               exact hc
             have hrc1 := obj_rc_of_mask_eq1 hwf hcRc
             r2b_to_group
             try simp only [show (4294967295 : BitVec 64) = 4294967295#64 from rfl, hnewSzEq'])
          | (apply hJ () m; simp only [Blocks.get]; c0_step; r2b_to_group
             try simp only [show (4294967295 : BitVec 64) = 4294967295#64 from rfl, hnewSzEq'])
        all_goals
          refine wp_join_group
            (P := fun (xs : Tup Val [i64]) m1 => match xs with
              | (nc, PUnit.unit) => m1 = m ∧ nc = BitVec.ofNat 64 newCap) ?_ ?_
          · intro _ ⟨nc, ⟨⟩⟩ m1 ⟨rfl, hnc⟩
            subst hnc
            change LeanQbe.T.wp _ _ _ _ _
            try simp only [show (4294967295 : BitVec 64) = 4294967295#64 from rfl, hnewSzEq']
            r2b_call rtR2bEnv_r2b_str_alloc_cap
            dsimp only [r2bStrAllocCapSpec, vals, Tup.map, Arg.val]
            have hvalid : newSz < strMaxCap ∧ newSz < newCap ∧ newCap ≤ strMaxCap :=
              ⟨hnewLt, hcapBnd.1, hcapBnd.2⟩
            rw [hnewTo, hnewCapTo, ite_eq_left hvalid]
            refine ⟨st, lcnfObjMem sObj ⋆ R, hav, sep_cast hm (by ac_rfl),
              fun dst st1 m1 hdst0 hdst8 hpr1 hrem1 _ hm1 => ?_⟩
            have hregSp : region (dst + 32#64) newSz =
                region (dst + 32#64) bs0.length ⋆
                  region (dst + 32#64 + BitVec.ofNat 64 bs0.length) clen :=
              region_split (by unfold strMaxCap at hnewLt; omega)
            have hm1Sp : (region (dst + 32#64) bs0.length ⋆
                region (dst + 32#64 + BitVec.ofNat 64 bs0.length) clen ⋆
                rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
                cell64 (dst + 8#64) (BitVec.ofNat 64 newSz + 1#64) ⋆
                cell64 (dst + 16#64) (BitVec.ofNat 64 newCap) ⋆
                cell64 (dst + 24#64) (BitVec.ofNat 64 sObj.strLen + 1#64) ⋆
                bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
                region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                  (strAllocBytes newCap - (32 + newSz + 1)) ⋆
                lcnfObjMem sObj ⋆ R) m1 := by
              rw [show (1 : BitVec 64) = 1#64 from rfl] at hm1
              have hm1' : (region (dst + 32#64) newSz ⋆
                  rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
                  cell64 (dst + 8#64) (BitVec.ofNat 64 newSz + 1#64) ⋆
                  cell64 (dst + 16#64) (BitVec.ofNat 64 newCap) ⋆
                  cell64 (dst + 24#64) (BitVec.ofNat 64 sObj.strLen + 1#64) ⋆
                  bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
                  region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                    (strAllocBytes newCap - (32 + newSz + 1)) ⋆
                  lcnfObjMem sObj ⋆ R) m1 := sep_cast hm1 (by ac_rfl)
              rw [hregSp] at hm1'
              exact sep_cast hm1' (by ac_rfl)
            have hmS1 : (lcnfObjMem sObj ⋆
                (region (dst + 32#64) bs0.length ⋆
                  region (dst + 32#64 + BitVec.ofNat 64 bs0.length) clen ⋆
                  rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
                  cell64 (dst + 8#64) (BitVec.ofNat 64 newSz + 1#64) ⋆
                  cell64 (dst + 16#64) (BitVec.ofNat 64 newCap) ⋆
                  cell64 (dst + 24#64) (BitVec.ofNat 64 sObj.strLen + 1#64) ⋆
                  bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
                  region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                    (strAllocBytes newCap - (32 + newSz + 1)) ⋆ R)) m1 :=
              sep_cast hm1Sp (by ac_rfl)
            rw [strObj_eq_bytes_rest hcanon] at hmS1
            r2b_steps
            r2b_call rtR2bEnv_r2b_mem_copy_bytes
            dsimp only [r2MemCopyBytesSpec, vals, Tup.map, Arg.val]
            rw [show (32 : BitVec 64) = 32#64 from rfl]
            refine ⟨bs0, bs0.length,
              strRest sObj ⋆ region (dst + 32#64 + BitVec.ofNat 64 bs0.length) clen ⋆
                rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
                cell64 (dst + 8#64) (BitVec.ofNat 64 newSz + 1#64) ⋆
                cell64 (dst + 16#64) (BitVec.ofNat 64 newCap) ⋆
                cell64 (dst + 24#64) (BitVec.ofNat 64 sObj.strLen + 1#64) ⋆
                bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
                region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                  (strAllocBytes newCap - (32 + newSz + 1)) ⋆ R,
              hszTo.symm, Nat.le_of_eq hszTo,
              by dsimp only [bs0]; unfold strMaxCap at hszLt; omega,
              sep_cast hmS1 (by dsimp only [bs0]; ac_rfl), fun m2 hm2 => ?_⟩
            rw [hszTo, Nat.sub_self, region_zero] at hm2
            simp only [sep_emp] at hm2
            have hmSClose : (lcnfObjMem sObj ⋆
                (bytes (dst + 32#64) bs0 ⋆
                  region (dst + 32#64 + BitVec.ofNat 64 bs0.length) clen ⋆
                  rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
                  cell64 (dst + 8#64) (BitVec.ofNat 64 newSz + 1#64) ⋆
                  cell64 (dst + 16#64) (BitVec.ofNat 64 newCap) ⋆
                  cell64 (dst + 24#64) (BitVec.ofNat 64 sObj.strLen + 1#64) ⋆
                  bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
                  region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                    (strAllocBytes newCap - (32 + newSz + 1)) ⋆ R)) m2 := by
              rw [strObj_eq_bytes_rest hcanon]
              exact sep_cast hm2 (by dsimp only [bs0]; ac_rfl)
            r2b_steps
            r2b_call rtR2bEnv_r2b_utf8_write
            dsimp only [r2bUtf8WriteSpec, vals, Tup.map, Arg.val]
            refine ⟨clen,
              lcnfObjMem sObj ⋆ bytes (dst + 32#64) bs0 ⋆ rtC0Inv rt st1 ⋆
                cell64 dst strHeaderWord ⋆
                cell64 (dst + 8#64) (BitVec.ofNat 64 newSz + 1#64) ⋆
                cell64 (dst + 16#64) (BitVec.ofNat 64 newCap) ⋆
                cell64 (dst + 24#64) (BitVec.ofNat 64 sObj.strLen + 1#64) ⋆
                bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
                region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                  (strAllocBytes newCap - (32 + newSz + 1)) ⋆ R,
              by rw [hencLen]; exact Nat.le_refl _, by omega,
              sep_cast hmSClose (by dsimp only [bs0, clen, cp]; ac_rfl), fun m3 hm3 => ?_⟩
            rw [hencLen] at hm3
            dsimp only [bs0, clen, cp] at hm3
            let newPay := bs0 ++ encBs
            let newLen := (sObj.strLen + 1) % 2 ^ 64
            let rObj := mkStrObj dst 1#32 newCap newPay newLen
            have hcanR : StrCanon rObj :=
              mkStrObj_canon hdst0 hdst8 (by decide)
                (by rw [hnewLenBs]; exact hcapBnd.1) hcapBnd.2 (Nat.mod_lt _ (by decide))
            have hmR : (rtC0Inv rt st1 ⋆ lcnfHeap [sObj] ⋆ lcnfObjMem rObj ⋆ R) m3 := by
              have hparts : (cell64 dst strHeaderWord ⋆
                  cell64 (dst + 8#64) (BitVec.ofNat 64 (newPay.length + 1)) ⋆
                  cell64 (dst + 16#64) (BitVec.ofNat 64 newCap) ⋆
                  cell64 (dst + 24#64) (BitVec.ofNat 64 newLen) ⋆
                  bytes (dst + 32#64) newPay ⋆
                  bytes (dst + 32#64 + BitVec.ofNat 64 newPay.length) [(0 : UInt8)] ⋆
                  region (dst + 32#64 + BitVec.ofNat 64 newPay.length + 1#64)
                    (strAllocBytes newCap - (32 + newPay.length + 1)) ⋆
                  (rtC0Inv rt st1 ⋆ lcnfObjMem sObj ⋆ R)) m3 := by
                rw [hnewLenBs]
                have hApp := bytes_append (dst + 32#64) bs0 encBs
                  (by rw [hencLen]; unfold strMaxCap at hnewLt; omega)
                rw [bv_ofNat_add1_mod64 newSz hnew64, Nat.mod_eq_of_lt (by omega)] at hm3
                rw [bv_ofNat_add1_mod64 sObj.strLen hlenLt] at hm3
                have hm3a : (cell64 dst strHeaderWord ⋆
                    cell64 (dst + 8#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
                    cell64 (dst + 16#64) (BitVec.ofNat 64 newCap) ⋆
                    cell64 (dst + 24#64) (BitVec.ofNat 64 ((sObj.strLen + 1) % 2 ^ 64)) ⋆
                    (bytes (dst + 32#64) bs0 ⋆
                      bytes (dst + 32#64 + BitVec.ofNat 64 bs0.length) encBs) ⋆
                    bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
                    region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                      (strAllocBytes newCap - (32 + newSz + 1)) ⋆
                    (rtC0Inv rt st1 ⋆ lcnfObjMem sObj ⋆ R)) m3 := by
                  have hregZ : region (dst + 32#64 + BitVec.ofNat 64 bs0.length +
                      BitVec.ofNat 64 clen) (clen - clen) = emp := by
                    rw [Nat.sub_self, region_zero]
                  rw [hregZ, sep_emp] at hm3
                  exact sep_cast hm3 (by ac_rfl)
                rwa [← hApp] at hm3a
              have hmObj := mkStrObj_mem_of_parts hcapBnd.2
                (by rw [hnewLenBs]; exact hcapBnd.1) hparts
              simp only [lcnfHeap, sep_emp]
              exact sep_cast hmObj (by ac_rfl)
            r2b_call rtR2bEnv_r2b_dec_obj
            dsimp only [r2DecObjSpec, vals, Tup.map, Arg.val]
            have hnotNull : ¬ (sObj.addr = 0#64 ∨ (sObj.addr &&& 1#64) ≠ 0#64) :=
              by simp [hcanon.1, bv64_and1_zero_of_mod8 hcanon.2.1]
            rw [ite_eq_right hnotNull]
            refine ⟨st1, [sObj], lcnfObjMem rObj ⋆ R, ⟨sObj, by simp, rfl, fun hrc1 => ?_⟩,
              fun o ho => by simp at ho; subst ho; exact hwf, sep_cast hmR (by ac_rfl),
              fun st2 objs' m4 hpr2 hrem2 hdec hm4 => ?_⟩
            · rw [RtC0State.workCap_eq_of_preservesMeta hpr1]
              exact ⟨hrc1Cap hrc1, lcnfHeapClosed_singleton_str hcanon,
                rcSound_singleton_str hcanon rfl⟩
            · rw [decObjRel_singleton_heap hcanon rfl hdec] at hm4
              r2b_steps
              exact hpostK dst st2 m4 hdst0 hdst8 (hpr1.trans hpr2) (by omega)
                (fun h => absurd h hinp) hcanR (sep_cast hm4 (by ac_rfl))
          · intro Jcap hJcap
            by_cases hrc1 : sObj.rc = 1#32
            · have hmask1 : (sObj.header &&& 4294967295#64) = 1#64 := by rw [hrcEq, hrc1]; rfl
              have hcapMax := hcanon.2.2.2.2.2.2.2.2.1
              have hltDouble : sObj.cap * 2 < 2 ^ 64 := by unfold strMaxCap at *; omega
              have hmul : (BitVec.ofNat 64 sObj.cap * 2#64).toNat = sObj.cap * 2 := by
                rw [BitVec.toNat_mul, hcapTo, show (2#64 : BitVec 64).toNat = 2 from rfl,
                  Nat.mod_eq_of_lt hltDouble]
              have haddTo : (BitVec.ofNat 64 newSz + 1#64).toNat = newSz + 1 := hnew1To
              r2b_steps <;> first
                | (exfalso
                   have hne : (sObj.header &&& 4294967295#64) ≠ 1#64 := by assumption
                   exact hne hmask1)
                | (exfalso
                   have hgt : 268435415 < (BitVec.ofNat 64 newSz + 1#64).toNat := by assumption
                   rw [haddTo] at hgt
                   exact absurd hnew1LeMax (Nat.not_le_of_lt hgt))
                | (try simp only [hnewSzEq']
                   have hd : newSz + 1 < sObj.cap * 2 := by
                     have h0 : (newSz + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
                         sObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 := by
                       assumption
                     rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                       show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                       Nat.mod_eq_of_lt hnew164, Nat.mod_eq_of_lt hcapLt,
                       Nat.mod_eq_of_lt hltDouble] at h0
                     exact h0
                   have hgtCap : 268435415 < sObj.cap * 2 := by
                     have h0 : BitVec.toNat (268435415 : BitVec 64) <
                         sObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 := by
                       assumption
                     rw [show BitVec.toNat (268435415 : BitVec 64) = 268435415 from rfl,
                       show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                       Nat.mod_eq_of_lt hcapLt, Nat.mod_eq_of_lt hltDouble] at h0
                     exact h0
                   apply hJcap _ m
                   refine ⟨rfl, ?_⟩
                   dsimp only [newCap]
                   rw [hrc1, strGrowCap_case_dbl_cap hd hgtCap]
                   rfl)
                | (try simp only [hnewSzEq']
                   have hd : newSz + 1 < sObj.cap * 2 := by
                     have h0 : (newSz + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
                         sObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 := by
                       assumption
                     rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                       show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                       Nat.mod_eq_of_lt hnew164, Nat.mod_eq_of_lt hcapLt,
                       Nat.mod_eq_of_lt hltDouble] at h0
                     exact h0
                   have hnc : ¬ 268435415 < sObj.cap * 2 := by
                     have h0 : ¬ BitVec.toNat (268435415 : BitVec 64) <
                         sObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 := by
                       assumption
                     rw [show BitVec.toNat (268435415 : BitVec 64) = 268435415 from rfl,
                       show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                       Nat.mod_eq_of_lt hcapLt, Nat.mod_eq_of_lt hltDouble] at h0
                     exact h0
                   apply hJcap _ m
                   refine ⟨rfl, ?_⟩
                   dsimp only [newCap]
                   rw [hrc1, strGrowCap_case_dbl hd (Nat.not_lt.mp hnc)]
                   apply BitVec.eq_of_toNat_eq
                   rw [show (2 : BitVec 64) = 2#64 from rfl, hmul, BitVec.toNat_ofNat,
                     Nat.mod_eq_of_lt hltDouble])
                | (try simp only [hnewSzEq']
                   have hnd : ¬ newSz + 1 < sObj.cap * 2 := by
                     have h0 : ¬ (newSz + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
                         sObj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 := by
                       assumption
                     rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                       show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                       Nat.mod_eq_of_lt hnew164, Nat.mod_eq_of_lt hcapLt,
                       Nat.mod_eq_of_lt hltDouble] at h0
                     exact h0
                   apply hJcap _ m
                   refine ⟨rfl, ?_⟩
                   dsimp only [newCap]
                   rw [hrc1, strGrowCap_case_new (Nat.not_lt.mp hnd) hnew1LeMax]
                   rw [show (1 : BitVec 64) = 1#64 from rfl,
                     bv_ofNat_add1_mod64 newSz hnew64, Nat.mod_eq_of_lt hnew164])
            · have hmaskNe : (sObj.header &&& 4294967295#64) ≠ 1#64 := by
                intro h1; exact hrc1 (obj_rc_of_mask_eq1 hwf h1)
              r2b_steps <;> first
                | (exfalso
                   rename_i h1
                   rw [show (4294967295 : BitVec 64) = 4294967295#64 from rfl,
                     show (1 : BitVec 64) = 1#64 from rfl] at h1
                   exact hmaskNe h1)
                | (apply hJcap _ m
                   refine ⟨rfl, ?_⟩
                   dsimp only [newCap, strGrowCap]
                   rw [ite_eq_right hrc1, show (1 : BitVec 64) = 1#64 from rfl,
                     bv_ofNat_add1_mod64 newSz hnew64, Nat.mod_eq_of_lt hnew164])
where
  hc_cap_bound (cap : Nat) (h : cap ≤ strMaxCap) : strAllocBytes cap ≤ 2 ^ 64 := by
    unfold strAllocBytes align8 strMaxCap at *; omega

/-! ## 3. `lcnf_string_append` WP Proof -/

private theorem str_append_slow_wp {rt s1 s2 : BitVec 64} {st : RtC0State}
    {s1Obj s2Obj : LcnfObj} {objs : List LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hs1Mem : s1Obj ∈ objs) (hs1Addr : s1Obj.addr = s1) (hc1 : StrCanon s1Obj)
    (hs2Mem : s2Obj ∈ objs) (hs2Addr : s2Obj.addr = s2) (hc2 : StrCanon s2Obj)
    (hwfObjs : ∀ o ∈ objs, o.Wf)
    (_hnotIn : ¬ (s1Obj.rc = 1#32 ∧
      (strPayload s1Obj ++ strPayload s2Obj).length + 1 ≤ s1Obj.cap))
    (hnotOv : ¬ strMaxCap ≤ (strPayload s1Obj).length + (strPayload s2Obj).length)
    (_hav : st.hasFree (strAllocBytes
        (strGrowCap s1Obj.rc s1Obj.cap ((strPayload s1Obj ++ strPayload s2Obj).length + 1))) ∨
      strAllocBytes
        (strGrowCap s1Obj.rc s1Obj.cap ((strPayload s1Obj ++ strPayload s2Obj).length + 1)) ≤
        st.rem)
    (hrc1Ok : s1Obj.rc = 1#32 → objs.length ≤ st.workCap ∧ lcnfHeapClosed objs ∧ RcSound s1 objs)
    (_hm : (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m)
    (hk : ∀ r st' objs' m',
      r ≠ 0#64 → r.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
      (∃ objs1, DecObjRel s1 objs objs1 ∧
        objs' = mkStrObj r 1#32
          (strGrowCap s1Obj.rc s1Obj.cap ((strPayload s1Obj ++ strPayload s2Obj).length + 1))
          (strPayload s1Obj ++ strPayload s2Obj) ((s1Obj.strLen + s2Obj.strLen) % 2 ^ 64) ::
          objs1) →
      (rtC0Inv rt st' ⋆ lcnfHeap objs' ⋆ R) m' → Q (r, ()) m') :
    let newCap :=
      strGrowCap s1Obj.rc s1Obj.cap ((strPayload s1Obj ++ strPayload s2Obj).length + 1)
    let p1 := strPayload s1Obj
    let p2 := strPayload s2Obj
    let newSz := p1.length + p2.length
    ∀ dst st1 m1,
      dst ≠ 0#64 → dst.toNat % 8 = 0 → st1.PreservesMeta st → st1.rem ≤ st.rem →
      (rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
        cell64 (dst + 8#64) (BitVec.ofNat 64 newSz + 1#64) ⋆
        cell64 (dst + 16#64) (BitVec.ofNat 64 newCap) ⋆
        cell64 (dst + 24#64) (BitVec.ofNat 64 s1Obj.strLen + BitVec.ofNat 64 s2Obj.strLen) ⋆
        region (dst + 32#64) newSz ⋆
        bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
        region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
          (strAllocBytes newCap - (32 + newSz + 1)) ⋆
        lcnfHeap objs ⋆ R) m1 →
      wp rtR2bEnv Q X
        (Expr.call "r2b_mem_copy_bytes" (as := [i64, i64, i64]) (bs := [])
          (Arg.var (dst + 32#64), Arg.var (s1 + 32#64), Arg.var (BitVec.ofNat 64 p1.length), ())
          fun _ =>
            Expr.call "r2b_mem_copy_bytes" (as := [i64, i64, i64]) (bs := [])
              (Arg.var (dst + 32#64 + BitVec.ofNat 64 p1.length), Arg.var (s2 + 32#64),
                Arg.var (BitVec.ofNat 64 p2.length), ())
              fun _ =>
                Expr.call "r2b_dec_obj" (as := [i64, i64]) (bs := [])
                  (Arg.var rt, Arg.var s1, ()) fun _ => Expr.ret (Arg.var dst, ())) m1 := by
  intro newCap p1 p2 newSz dst st1 m1 hdst0 hdst8 hpr1 hrem1 hm1
  have hnewLen : (p1 ++ p2).length = newSz := by simp [p1, p2, newSz]
  have hnewLt : newSz < strMaxCap := by
    dsimp only [newSz, p1, p2] at *; unfold strMaxCap at hnotOv ⊢; omega
  have hcapBnd := strGrowCap_props s1Obj.rc s1Obj.cap (newSz + 1)
    (by unfold strMaxCap at hnewLt ⊢; omega)
  have hnewCapEq : strGrowCap s1Obj.rc s1Obj.cap ((p1 ++ p2).length + 1) = newCap := rfl
  have hregSp : region (dst + 32#64) newSz =
      region (dst + 32#64) p1.length ⋆
        region (dst + 32#64 + BitVec.ofNat 64 p1.length) p2.length := by
    rw [region_split (by unfold strMaxCap at hnewLt; omega)]
  have hm1Sp : (region (dst + 32#64) p1.length ⋆ lcnfHeap objs ⋆
      (region (dst + 32#64 + BitVec.ofNat 64 p1.length) p2.length ⋆
        rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
        cell64 (dst + 8#64) (BitVec.ofNat 64 newSz + 1#64) ⋆
        cell64 (dst + 16#64) (BitVec.ofNat 64 newCap) ⋆
        cell64 (dst + 24#64) (BitVec.ofNat 64 s1Obj.strLen + BitVec.ofNat 64 s2Obj.strLen) ⋆
        bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
        region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
          (strAllocBytes newCap - (32 + newSz + 1)) ⋆ R)) m1 := by
    have hm1' : (region (dst + 32#64) newSz ⋆ lcnfHeap objs ⋆
        rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
        cell64 (dst + 8#64) (BitVec.ofNat 64 newSz + 1#64) ⋆
        cell64 (dst + 16#64) (BitVec.ofNat 64 newCap) ⋆
        cell64 (dst + 24#64) (BitVec.ofNat 64 s1Obj.strLen + BitVec.ofNat 64 s2Obj.strLen) ⋆
        bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
        region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
          (strAllocBytes newCap - (32 + newSz + 1)) ⋆ R) m1 := sep_cast hm1 (by ac_rfl)
    rw [hregSp] at hm1'
    exact sep_cast hm1' (by ac_rfl)
  dsimp only [p1] at hm1Sp ⊢
  apply str_copy_from_heap hs1Mem hs1Addr hc1 hm1Sp
  intro m2 hm2
  have hm2Sp : (region (dst + 32#64 + BitVec.ofNat 64 (strPayload s1Obj).length) p2.length ⋆
      lcnfHeap objs ⋆
      (bytes (dst + 32#64) (strPayload s1Obj) ⋆ rtC0Inv rt st1 ⋆ cell64 dst strHeaderWord ⋆
        cell64 (dst + 8#64) (BitVec.ofNat 64 newSz + 1#64) ⋆
        cell64 (dst + 16#64) (BitVec.ofNat 64 newCap) ⋆
        cell64 (dst + 24#64) (BitVec.ofNat 64 s1Obj.strLen + BitVec.ofNat 64 s2Obj.strLen) ⋆
        bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
        region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
          (strAllocBytes newCap - (32 + newSz + 1)) ⋆ R)) m2 := sep_cast hm2 (by ac_rfl)
  dsimp only [p2] at hm2Sp ⊢
  apply str_copy_from_heap hs2Mem hs2Addr hc2 hm2Sp
  intro m3 hm3
  let newPay := p1 ++ p2
  let newLen := (s1Obj.strLen + s2Obj.strLen) % 2 ^ 64
  let rObj := mkStrObj dst 1#32 newCap newPay newLen
  have hmR : (rtC0Inv rt st1 ⋆ lcnfHeap objs ⋆ lcnfObjMem rObj ⋆ R) m3 := by
    have hparts : (cell64 dst strHeaderWord ⋆
        cell64 (dst + 8#64) (BitVec.ofNat 64 (newPay.length + 1)) ⋆
        cell64 (dst + 16#64) (BitVec.ofNat 64 newCap) ⋆
        cell64 (dst + 24#64) (BitVec.ofNat 64 newLen) ⋆
        bytes (dst + 32#64) newPay ⋆
        bytes (dst + 32#64 + BitVec.ofNat 64 newPay.length) [(0 : UInt8)] ⋆
        region (dst + 32#64 + BitVec.ofNat 64 newPay.length + 1#64)
          (strAllocBytes newCap - (32 + newPay.length + 1)) ⋆
        (rtC0Inv rt st1 ⋆ lcnfHeap objs ⋆ R)) m3 := by
      rw [hnewLen]
      have hApp := bytes_append (dst + 32#64) p1 p2
        (by unfold strMaxCap at hnewLt; omega)
      have hnew64 : newSz < 2 ^ 64 := by unfold strMaxCap at hnewLt; omega
      have hlen1 := str_len_lt_64 s1Obj hc1
      have hlen2 := str_len_lt_64 s2Obj hc2
      have haddLen : BitVec.ofNat 64 s1Obj.strLen + BitVec.ofNat 64 s2Obj.strLen =
          BitVec.ofNat 64 newLen := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add, BitVec.toNat_ofNat, newLen,
          Nat.mod_eq_of_lt hlen1, Nat.mod_eq_of_lt hlen2]
      have hnewLt' : newSz + 1 < 2 ^ 64 := by
        dsimp only [newSz, p1, p2] at hnewLt ⊢; unfold strMaxCap at hnewLt; omega
      rw [bv_ofNat_add1_mod64 newSz hnew64, Nat.mod_eq_of_lt hnewLt', haddLen] at hm3
      have hm3a : (cell64 dst strHeaderWord ⋆
          cell64 (dst + 8#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
          cell64 (dst + 16#64) (BitVec.ofNat 64 newCap) ⋆
          cell64 (dst + 24#64) (BitVec.ofNat 64 newLen) ⋆
          (bytes (dst + 32#64) p1 ⋆ bytes (dst + 32#64 + BitVec.ofNat 64 p1.length) p2) ⋆
          bytes (dst + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
          region (dst + 32#64 + BitVec.ofNat 64 newSz + 1#64)
            (strAllocBytes newCap - (32 + newSz + 1)) ⋆
          (rtC0Inv rt st1 ⋆ lcnfHeap objs ⋆ R)) m3 := sep_cast hm3 (by ac_rfl)
      rwa [← hApp] at hm3a
    have hcapBnd' : newSz + 1 ≤ newCap ∧ newCap ≤ strMaxCap := by
      rw [← hnewCapEq, hnewLen]; exact hcapBnd
    have hmObj := mkStrObj_mem_of_parts hcapBnd'.2 (by rw [hnewLen]; exact hcapBnd'.1) hparts
    exact sep_cast hmObj (by ac_rfl)
  r2b_call rtR2bEnv_r2b_dec_obj
  dsimp only [r2DecObjSpec, vals, Tup.map, Arg.val]
  have hnotNull : ¬ (s1 = 0#64 ∨ (s1 &&& 1#64) ≠ 0#64) := by
    simp [hs1Addr ▸ hc1.1, hs1Addr ▸ bv64_and1_zero_of_mod8 hc1.2.1]
  rw [ite_eq_right hnotNull]
  refine ⟨st1, objs, lcnfObjMem rObj ⋆ R, ⟨s1Obj, hs1Mem, hs1Addr, fun hrc1 => ?_⟩,
    hwfObjs, sep_cast hmR (by ac_rfl), fun st2 objs1 m4 hpr2 hrem2 hdec hm4 => ?_⟩
  · rw [RtC0State.workCap_eq_of_preservesMeta hpr1]; exact hrc1Ok hrc1
  · r2b_steps
    refine hk dst st2 (rObj :: objs1) m4 hdst0 hdst8 (hpr1.trans hpr2) (by omega)
      ⟨objs1, hdec, rfl⟩ ?_
    simp only [lcnfHeap]
    exact sep_cast hm4 (by ac_rfl)

theorem lcnf_string_append_wp :
    ∀ xs m Q X,
      lcnfStringAppendSpec xs m Q X → Func.wp rtR2bEnv lcnf_string_append_body xs m Q X := by
  intro ⟨rt, s1, s2, ⟨⟩⟩
  revert s1 s2
  dsimp only [Val]
  intro s1 s2 m Q X
    ⟨st, s1Obj, s2Obj, objs, R, hs1Mem, hs1Addr, hc1, hs2Mem, hs2Addr, hc2, hwfObjs, hm, hPost⟩
  dsimp only [Func.wp, lcnf_string_append_body]
  change LeanQbe.T.wp _ _ _ _ _
  let p1 := strPayload s1Obj
  let p2 := strPayload s2Obj
  have hp1Lt := str_payload_lt_max s1Obj hc1
  have hp2Lt := str_payload_lt_max s2Obj hc2
  have hp1_64 : p1.length < 2 ^ 64 := by
    dsimp only [p1]; unfold strMaxCap at hp1Lt; exact Nat.lt_trans hp1Lt (by decide)
  have hp2_64 : p2.length < 2 ^ 64 := by
    dsimp only [p2]; unfold strMaxCap at hp2Lt; exact Nat.lt_trans hp2Lt (by decide)
  have hcap1Lt := str_cap_lt_64 s1Obj hc1
  have hlen1Lt := str_len_lt_64 s1Obj hc1
  have hlen2Lt := str_len_lt_64 s2Obj hc2
  have hnd : (objs.map LcnfObj.addr).Nodup :=
    lcnfHeap_nodup_addrs (sep_cast hm (by ac_rfl) : (lcnfHeap objs ⋆ (rtC0Inv rt st ⋆ R)) m)
  obtain ⟨k2, hk2, hobj2⟩ := List.getElem_of_mem hs2Mem
  have hmS2 : (lcnfObjMem s2Obj ⋆ (lcnfHeap (objs.eraseIdx k2) ⋆ rtC0Inv rt st ⋆ R)) m := by
    have hf := lcnfHeap_focus objs hk2
    rw [hobj2, ← lcnfHeap_eraseIdx objs] at hf
    rw [hf] at hm
    exact sep_cast hm (by ac_rfl)
  have hloadSz2 := str_load_sz hc2 hmS2
  rw [hs2Addr] at hloadSz2
  r2b_steps
  apply wp_load_of hloadSz2
  r2b_to_group
  try simp only [str_sz_sub1_eq s2Obj hc2] at *
  by_cases hp2Zero : p2.length = 0
  · rw [ite_eq_left hp2Zero] at hPost
    have hzero : BitVec.ofNat 64 p2.length = 0#64 := by rw [hp2Zero]
    r2b_steps
    all_goals first
      | exact hPost
      | (exfalso; exact (by assumption : BitVec.ofNat 64 p2.length ≠ 0#64) hzero)
  · rw [ite_eq_right hp2Zero] at hPost
    have hnz : BitVec.ofNat 64 p2.length ≠ 0#64 := by
      intro h0
      have htn := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by dsimp only [p2]; unfold strMaxCap at hp2Lt; omega)] at htn
      exact hp2Zero htn
    obtain ⟨k1, hk1, hobj1⟩ := List.getElem_of_mem hs1Mem
    have hmS1 : (lcnfObjMem s1Obj ⋆ (lcnfHeap (objs.eraseIdx k1) ⋆ rtC0Inv rt st ⋆ R)) m := by
      have hf := lcnfHeap_focus objs hk1
      rw [hobj1, ← lcnfHeap_eraseIdx objs] at hf
      rw [hf] at hm
      exact sep_cast hm (by ac_rfl)
    have hloadSz1 := str_load_sz hc1 hmS1
    have hloadCap1 := str_load_cap hc1 hmS1
    have hloadLen1 := str_load_len hc1 hmS1
    have hloadHdr1 := str_load_hdr hc1 hmS1
    have hloadLen2 := str_load_len hc2 hmS2
    rw [hs1Addr] at hloadSz1 hloadCap1 hloadLen1 hloadHdr1
    rw [hs2Addr] at hloadLen2
    r2b_steps
    · exfalso; exact hnz (by assumption)
    · apply wp_load_of hloadSz1
      r2b_steps
      simp only [str_sz_sub1_eq s1Obj hc1] at *
      apply wp_load_of hloadCap1
      r2b_steps
      apply wp_load_of hloadLen1
      r2b_steps
      apply wp_load_of hloadLen2
      have hp1To : (BitVec.ofNat 64 p1.length).toNat = p1.length := by
        dsimp only [p1]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold strMaxCap at hp1Lt; omega)]
      have hp2To : (BitVec.ofNat 64 p2.length).toNat = p2.length := by
        dsimp only [p2]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold strMaxCap at hp2Lt; omega)]
      have hsubSz2 : ((268435415 : BitVec 64) - BitVec.ofNat 64 p2.length).toNat =
          268435415 - p2.length :=
        str_sub_mod_lt 268435415 p2.length (by decide)
          (by dsimp only [p2]; unfold strMaxCap at hp2Lt; omega)
      have hp2LeMax : p2.length ≤ 268435415 := by
        dsimp only [p2] at hp2Lt ⊢; exact Nat.le_of_lt hp2Lt
      have hsubP2Mod : (2 ^ 64 - p2.length % 2 ^ 64 + 268435415) % 2 ^ 64 = 268435415 - p2.length :=
        bv_sub_mod64_nat 268435415 p2.length (by decide) hp2LeMax
      by_cases hov : strMaxCap ≤ p1.length + p2.length
      · rw [ite_eq_left hov] at hPost
        have hge : 268435415 - p2.length ≤ p1.length := by
          dsimp only [p1, p2] at hov ⊢; unfold strMaxCap at hov; omega
        r2b_to_group
        c0_step
        · exfalso
          dsimp only [p2] at hp2Lt hp2_64
          rw [Nat.mod_eq_of_lt hp2_64] at hc
          exact Nat.not_le_of_lt hp2Lt hc
        · r2b_to_group
          have hcond :
              ((268435415 - BitVec.ofNat 64 (strPayload s2Obj).length).ule
                (BitVec.ofNat 64 (strPayload s1Obj).length)) = true := by
            rw [show (268435415 : BitVec 64) = BitVec.ofNat 64 268435415 from rfl]
            exact bv64_sub_ule_true (by decide) hp2LeMax hp1_64 hge
          rw [hcond]
          exact r2b_wp_jnz_true hPost
      · rw [ite_eq_right hov] at hPost
        have hnotGe : ¬ 268435415 - p2.length ≤ p1.length := by
          dsimp only [p1, p2] at hov ⊢; unfold strMaxCap at hov; omega
        let newSz := p1.length + p2.length
        have hnewLt : newSz < strMaxCap := by
          dsimp only [newSz, p1, p2] at hov ⊢; unfold strMaxCap at hov ⊢; omega
        have hnew64 : newSz < 2 ^ 64 := by
          unfold strMaxCap at hnewLt; exact Nat.lt_trans hnewLt (by decide)
        have hnew1LeMax : newSz + 1 ≤ strMaxCap := Nat.succ_le_of_lt hnewLt
        have hnew164 : newSz + 1 < 2 ^ 64 :=
          Nat.lt_of_le_of_lt hnew1LeMax (by unfold strMaxCap; decide)
        have hnewSzEq : BitVec.ofNat 64 (strPayload s1Obj).length +
            BitVec.ofNat 64 (strPayload s2Obj).length = BitVec.ofNat 64 newSz :=
          (BitVec.ofNat_add (strPayload s1Obj).length (strPayload s2Obj).length).symm
        have hnewTo : (BitVec.ofNat 64 newSz).toNat = newSz := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnew64]
        have hnew1To : (BitVec.ofNat 64 newSz + 1#64).toNat = newSz + 1 := by
          rw [bv_ofNat_add1_mod64 newSz hnew64, BitVec.toNat_ofNat, Nat.mod_mod,
            Nat.mod_eq_of_lt hnew164]
        have hcapTo : (BitVec.ofNat 64 s1Obj.cap).toNat = s1Obj.cap := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap1Lt]
        r2b_to_group
        c0_step
        · exfalso
          dsimp only [p2] at hp2Lt hp2_64
          rw [Nat.mod_eq_of_lt hp2_64] at hc
          exact Nat.not_le_of_lt hp2Lt hc
        · r2b_to_group
          have hcond :
              ((268435415 - BitVec.ofNat 64 (strPayload s2Obj).length).ule
                (BitVec.ofNat 64 (strPayload s1Obj).length)) = false := by
            rw [show (268435415 : BitVec 64) = BitVec.ofNat 64 268435415 from rfl]
            exact bv64_sub_ule_false (by decide) hp2LeMax hp1_64 hnotGe
          rw [hcond]
          apply r2b_wp_jnz_false
          focus
            try simp only [hnewSzEq] at *
            have hnewSzEq' : BitVec.ofNat 64 (strPayload s1Obj).length +
                BitVec.ofNat 64 (strPayload s2Obj).length = BitVec.ofNat 64 newSz :=
              (BitVec.ofNat_add (strPayload s1Obj).length (strPayload s2Obj).length).symm
            apply wp_load_of hloadHdr1
            have hwf1 := hc1.wf
            have hrc1Eq := header_and_mask_eq_rc s1Obj hwf1
            by_cases hinp : s1Obj.rc = 1#32 ∧ newSz + 1 ≤ s1Obj.cap
            · have hlenApp : (p1 ++ p2).length = newSz := by simp [newSz]
              have hinp' : s1Obj.rc = 1#32 ∧ (p1 ++ p2).length + 1 ≤ s1Obj.cap := by
                rw [hlenApp]; exact hinp
              rw [ite_eq_left hinp'] at hPost
              rcases hPost with ⟨_, hpostK⟩
              have hrc1 : s1Obj.rc = 1#32 := hinp.1
              have hcapOk : newSz + 1 ≤ s1Obj.cap := hinp.2
              have hmask1 : (s1Obj.header &&& 4294967295#64) = 1#64 := by
                rw [hrc1Eq, hrc1]; rfl
              have hhdrWord : s1Obj.header = strHeaderWord := by
                rcases hc1 with ⟨_, _, _, hcs, ho, htag, _, _, _, _, _, _⟩
                dsimp only [LcnfObj.header, strHeaderWord]; rw [hrc1, hcs, ho, htag]; decide
              have hregFit : 1 + (strAllocBytes s1Obj.cap - (32 + p1.length + 1)) ≤ 2 ^ 64 := by
                have := LcnfC0StringsProof2_cap_bound s1Obj.cap hc1.2.2.2.2.2.2.2.2.1; omega
              have hmElim := lcnfObjMem_string_elim hc1 hmS1
              have hmMerge : (region (s1Obj.addr + 32#64 + BitVec.ofNat 64 p1.length)
                    (1 + (strAllocBytes s1Obj.cap - (32 + p1.length + 1))) ⋆
                  (cell64 s1Obj.addr s1Obj.header ⋆
                    cell64 (s1Obj.addr + 8#64) (BitVec.ofNat 64 (p1.length + 1)) ⋆
                    cell64 (s1Obj.addr + 16#64) (BitVec.ofNat 64 s1Obj.cap) ⋆
                    cell64 (s1Obj.addr + 24#64) (BitVec.ofNat 64 s1Obj.strLen) ⋆
                    bytes (s1Obj.addr + 32#64) p1 ⋆
                    lcnfHeap (objs.eraseIdx k1) ⋆ rtC0Inv rt st ⋆ R)) m :=
                bytes1_merge_region hregFit (sep_cast hmElim (by ac_rfl))
              have hremEq : 1 + (strAllocBytes s1Obj.cap - (32 + p1.length + 1)) =
                  strAllocBytes s1Obj.cap - (32 + p1.length) := by
                have := strAllocBytes_ge s1Obj.cap
                have := hc1.2.2.2.2.2.2.2.1
                have := strPayload_length hc1
                omega
              rw [hremEq] at hmMerge
              r2b_to_group
              c0_step
              r2b_to_group
              try c0_step
              all_goals
                first
                | (exfalso
                   have hne : (s1Obj.header &&& 4294967295#64) ≠ 1#64 := by assumption
                   exact hne hmask1)
                | (try r2b_to_group
                   try c0_step)
              all_goals
                first
                | (exfalso
                   dsimp only [newSz, p1, p2] at hcapOk
                   unfold strMaxCap at hp1Lt hp2Lt
                   omega)
                | r2b_to_group
                have hallocGe := strAllocBytes_ge s1Obj.cap
                have hleReg : p2.length ≤ strAllocBytes s1Obj.cap - (32 + p1.length) := by
                  omega
                have hrunCopy : ∀ {kRest : Expr Val Cont [i64]},
                    (∀ m2,
                      (bytes (s1Obj.addr + 32#64 + BitVec.ofNat 64 p1.length) p2 ⋆
                        region (s1Obj.addr + 32#64 + BitVec.ofNat 64 p1.length +
                            BitVec.ofNat 64 p2.length)
                          (strAllocBytes s1Obj.cap - (32 + p1.length) - p2.length) ⋆
                        cell64 s1Obj.addr s1Obj.header ⋆
                        cell64 (s1Obj.addr + 8#64) (BitVec.ofNat 64 (p1.length + 1)) ⋆
                        cell64 (s1Obj.addr + 16#64) (BitVec.ofNat 64 s1Obj.cap) ⋆
                        cell64 (s1Obj.addr + 24#64) (BitVec.ofNat 64 s1Obj.strLen) ⋆
                        bytes (s1Obj.addr + 32#64) p1 ⋆
                        lcnfHeap (objs.eraseIdx k1) ⋆ rtC0Inv rt st ⋆ R) m2 →
                      wp rtR2bEnv Q X kRest m2) →
                    wp rtR2bEnv Q X
                      (Expr.call "r2b_mem_copy_bytes" (as := [i64, i64, i64]) (bs := [])
                        (Arg.var (s1 + 32#64 + BitVec.ofNat 64 p1.length),
                          Arg.var (s2 + 32#64), Arg.var (BitVec.ofNat 64 p2.length), ())
                        (fun _ => kRest)) m := by
                  intro kRest hkCopy
                  by_cases hsEq : s1 = s2
                  · have hkEq : k1 = k2 := by
                      apply nodup_map_getElem_eq LcnfObj.addr hnd hk1 hk2
                      rw [hobj1, hobj2, hs1Addr, hs2Addr, hsEq]
                    have hs2Eq1 : s2Obj = s1Obj := by subst hkEq; rw [← hobj1, ← hobj2]
                    have hp12 : p2 = p1 := by dsimp only [p1, p2]; rw [hs2Eq1]
                    r2b_call rtR2bEnv_r2b_mem_copy_bytes
                    dsimp only [r2MemCopyBytesSpec, vals, Tup.map, Arg.val]
                    rw [hs1Addr] at hmMerge
                    refine ⟨p1, strAllocBytes s1Obj.cap - (32 + p1.length),
                      cell64 s1 s1Obj.header ⋆
                        cell64 (s1 + 8#64) (BitVec.ofNat 64 (p1.length + 1)) ⋆
                        cell64 (s1 + 16#64) (BitVec.ofNat 64 s1Obj.cap) ⋆
                        cell64 (s1 + 24#64) (BitVec.ofNat 64 s1Obj.strLen) ⋆
                        lcnfHeap (objs.eraseIdx k1) ⋆ rtC0Inv rt st ⋆ R,
                      by rw [hp2To, hp12], by rw [hp2To]; exact hleReg,
                      by unfold strMaxCap at hp1Lt; omega,
                      by
                        rw [← hsEq]
                        try simp only [show (32 : BitVec 64) = 32#64 from rfl]
                        exact sep_cast hmMerge (by ac_rfl),
                      fun m2 hm2 => ?_⟩
                    have hm2' : (bytes (s1Obj.addr + 32#64 + BitVec.ofNat 64 p1.length) p2 ⋆
                        region (s1Obj.addr + 32#64 + BitVec.ofNat 64 p1.length +
                            BitVec.ofNat 64 p2.length)
                          (strAllocBytes s1Obj.cap - (32 + p1.length) - p2.length) ⋆
                        cell64 s1Obj.addr s1Obj.header ⋆
                        cell64 (s1Obj.addr + 8#64) (BitVec.ofNat 64 (p1.length + 1)) ⋆
                        cell64 (s1Obj.addr + 16#64) (BitVec.ofNat 64 s1Obj.cap) ⋆
                        cell64 (s1Obj.addr + 24#64) (BitVec.ofNat 64 s1Obj.strLen) ⋆
                        bytes (s1Obj.addr + 32#64) p1 ⋆
                        lcnfHeap (objs.eraseIdx k1) ⋆ rtC0Inv rt st ⋆ R) m2 := by
                      rw [hp2To, hp12, ← hsEq] at hm2
                      try simp only [show (32 : BitVec 64) = 32#64 from rfl] at hm2
                      rw [hp12, hs1Addr]
                      exact sep_cast hm2 (by ac_rfl)
                    exact hkCopy m2 hm2'
                  · have hne21 : s2Obj.addr ≠ s1Obj.addr := by
                      rw [hs1Addr, hs2Addr]; exact Ne.symm hsEq
                    have hs2Er : s2Obj ∈ objs.eraseIdx k1 := by
                      apply mem_eraseIdx_of_addr_ne hk1 hs2Mem; rw [hobj1]; exact hne21
                    obtain ⟨k2', hk2', hobj2'⟩ := List.getElem_of_mem hs2Er
                    have hf2 : lcnfHeap (objs.eraseIdx k1) =
                        lcnfObjMem s2Obj ⋆ lcnfHeap ((objs.eraseIdx k1).eraseIdx k2') := by
                      rw [lcnfHeap_focus (objs.eraseIdx k1) hk2', hobj2',
                        ← lcnfHeap_eraseIdx (objs.eraseIdx k1)]
                    have hm2Focus : (bytes (s2Obj.addr + 32#64) p2 ⋆
                        (strRest s2Obj ⋆ lcnfHeap ((objs.eraseIdx k1).eraseIdx k2') ⋆
                          region (s1Obj.addr + 32#64 + BitVec.ofNat 64 p1.length)
                            (strAllocBytes s1Obj.cap - (32 + p1.length)) ⋆
                          cell64 s1Obj.addr s1Obj.header ⋆
                          cell64 (s1Obj.addr + 8#64) (BitVec.ofNat 64 (p1.length + 1)) ⋆
                          cell64 (s1Obj.addr + 16#64) (BitVec.ofNat 64 s1Obj.cap) ⋆
                          cell64 (s1Obj.addr + 24#64) (BitVec.ofNat 64 s1Obj.strLen) ⋆
                          bytes (s1Obj.addr + 32#64) p1 ⋆ rtC0Inv rt st ⋆ R)) m := by
                      dsimp only [p2]
                      rw [hf2, strObj_eq_bytes_rest hc2] at hmMerge
                      exact sep_cast hmMerge (by ac_rfl)
                    r2b_call rtR2bEnv_r2b_mem_copy_bytes
                    dsimp only [r2MemCopyBytesSpec, vals, Tup.map, Arg.val]
                    rw [hs1Addr] at hmMerge
                    rw [hs1Addr, hs2Addr] at hm2Focus
                    refine ⟨p2, strAllocBytes s1Obj.cap - (32 + p1.length),
                      strRest s2Obj ⋆ lcnfHeap ((objs.eraseIdx k1).eraseIdx k2') ⋆
                        cell64 s1 s1Obj.header ⋆
                        cell64 (s1 + 8#64) (BitVec.ofNat 64 (p1.length + 1)) ⋆
                        cell64 (s1 + 16#64) (BitVec.ofNat 64 s1Obj.cap) ⋆
                        cell64 (s1 + 24#64) (BitVec.ofNat 64 s1Obj.strLen) ⋆
                        bytes (s1 + 32#64) p1 ⋆ rtC0Inv rt st ⋆ R,
                      hp2To.symm, by rw [hp2To]; exact hleReg, by unfold strMaxCap at hp2Lt; omega,
                      sep_cast hm2Focus (by ac_rfl), fun m2 hm2 => ?_⟩
                    have hmCl : (lcnfHeap (objs.eraseIdx k1) ⋆
                        bytes (s1 + 32#64 + BitVec.ofNat 64 p1.length) p2 ⋆
                        region (s1 + 32#64 + BitVec.ofNat 64 p1.length +
                            BitVec.ofNat 64 p2.length)
                          (strAllocBytes s1Obj.cap - (32 + p1.length) - p2.length) ⋆
                        cell64 s1 s1Obj.header ⋆
                        cell64 (s1 + 8#64) (BitVec.ofNat 64 (p1.length + 1)) ⋆
                        cell64 (s1 + 16#64) (BitVec.ofNat 64 s1Obj.cap) ⋆
                        cell64 (s1 + 24#64) (BitVec.ofNat 64 s1Obj.strLen) ⋆
                        bytes (s1 + 32#64) p1 ⋆ rtC0Inv rt st ⋆ R) m2 := by
                      dsimp only [p2] at *
                      rw [hp2To] at hm2
                      rw [hf2, strObj_eq_bytes_rest hc2, hs2Addr]
                      try simp only [show (32 : BitVec 64) = 32#64 from rfl] at hm2 ⊢
                      exact sep_cast hm2 (by ac_rfl)
                    rw [← hs1Addr] at hmCl
                    exact hkCopy m2 (sep_cast hmCl (by ac_rfl))
                apply hrunCopy
                intro m2 hm2
                r2b_steps
                have h1rem : 1 ≤ strAllocBytes s1Obj.cap - (32 + p1.length) - p2.length := by
                  omega
                have hfit1 :
                    strAllocBytes s1Obj.cap - (32 + p1.length) - p2.length ≤ 2 ^ 64 := by
                  have := LcnfC0StringsProof2_cap_bound s1Obj.cap hc1.2.2.2.2.2.2.2.2.1; omega
                have hmReg1 : (region (s1Obj.addr + 32#64 + BitVec.ofNat 64 p1.length +
                      BitVec.ofNat 64 p2.length)
                      (strAllocBytes s1Obj.cap - (32 + p1.length) - p2.length) ⋆
                    (bytes (s1Obj.addr + 32#64 + BitVec.ofNat 64 p1.length) p2 ⋆
                      cell64 s1Obj.addr s1Obj.header ⋆
                      cell64 (s1Obj.addr + 8#64) (BitVec.ofNat 64 (p1.length + 1)) ⋆
                      cell64 (s1Obj.addr + 16#64) (BitVec.ofNat 64 s1Obj.cap) ⋆
                      cell64 (s1Obj.addr + 24#64) (BitVec.ofNat 64 s1Obj.strLen) ⋆
                      bytes (s1Obj.addr + 32#64) p1 ⋆
                      lcnfHeap (objs.eraseIdx k1) ⋆ rtC0Inv rt st ⋆ R)) m2 :=
                  sep_cast hm2 (by ac_rfl)
                obtain ⟨bs1, hbs1Len, hmPop⟩ := region_pop_bytes h1rem hfit1 hmReg1
                rcases bs1 with _ | ⟨bNul, _ | _⟩ <;> simp at hbs1Len
                have hptrNew : s1Obj.addr + 32#64 + BitVec.ofNat 64 newSz =
                    s1Obj.addr + 32#64 + BitVec.ofNat 64 p1.length +
                      BitVec.ofNat 64 p2.length := by
                  apply BitVec.eq_of_toNat_eq
                  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod,
                    newSz, Nat.add_assoc]
                have hmNul : (bytes (s1Obj.addr + 32#64 + BitVec.ofNat 64 newSz) [bNul] ⋆
                    (region (s1Obj.addr + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                        (strAllocBytes s1Obj.cap - (32 + p1.length) - p2.length - 1) ⋆
                      bytes (s1Obj.addr + 32#64 + BitVec.ofNat 64 p1.length) p2 ⋆
                      cell64 s1Obj.addr s1Obj.header ⋆
                      cell64 (s1Obj.addr + 8#64) (BitVec.ofNat 64 (p1.length + 1)) ⋆
                      cell64 (s1Obj.addr + 16#64) (BitVec.ofNat 64 s1Obj.cap) ⋆
                      cell64 (s1Obj.addr + 24#64) (BitVec.ofNat 64 s1Obj.strLen) ⋆
                      bytes (s1Obj.addr + 32#64) p1 ⋆
                      lcnfHeap (objs.eraseIdx k1) ⋆ rtC0Inv rt st ⋆ R)) m2 := by
                  rw [hptrNew]; exact sep_cast hmPop (by ac_rfl)
                obtain ⟨hokNul, hm3⟩ :=
                  r2b_c0_store_bytes_single (BitVec.truncate 8 0#64) hmNul
                rw [hs1Addr] at hokNul hm3
                try simp only [show (32 : BitVec 64) = 32#64 from rfl, hnewSzEq']
                apply wp_store_sep ⟨hokNul, hm3⟩
                intro m3 hm3'
                r2b_steps
                have hmCell8 : (cell64 (s1Obj.addr + 8#64) (BitVec.ofNat 64 (p1.length + 1)) ⋆
                    (bytes (s1Obj.addr + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
                      region (s1Obj.addr + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                        (strAllocBytes s1Obj.cap - (32 + p1.length) - p2.length - 1) ⋆
                      bytes (s1Obj.addr + 32#64 + BitVec.ofNat 64 p1.length) p2 ⋆
                      cell64 s1Obj.addr s1Obj.header ⋆
                      cell64 (s1Obj.addr + 16#64) (BitVec.ofNat 64 s1Obj.cap) ⋆
                      cell64 (s1Obj.addr + 24#64) (BitVec.ofNat 64 s1Obj.strLen) ⋆
                      bytes (s1Obj.addr + 32#64) p1 ⋆
                      lcnfHeap (objs.eraseIdx k1) ⋆ rtC0Inv rt st ⋆ R)) m3 := by
                  have h0eq : (BitVec.truncate 8 0#64).toNat = 0 := rfl
                  rw [h0eq, ← hs1Addr] at hm3'
                  exact sep_cast hm3' (by ac_rfl)
                obtain ⟨hok8, hm4⟩ :=
                  r2_c0_store_cell64_add8 (BitVec.ofNat 64 newSz + 1#64) hmCell8
                rw [hs1Addr] at hok8 hm4
                try simp only [show (8 : BitVec 64) = 8#64 from rfl,
                  show (1 : BitVec 64) = 1#64 from rfl]
                apply wp_store_sep ⟨hok8, hm4⟩
                intro m4 hm4'
                r2b_steps
                have hmCell24 : (cell64 (s1Obj.addr + 24#64) (BitVec.ofNat 64 s1Obj.strLen) ⋆
                    (cell64 (s1Obj.addr + 8#64) (BitVec.ofNat 64 newSz + 1#64) ⋆
                      bytes (s1Obj.addr + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
                      region (s1Obj.addr + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                        (strAllocBytes s1Obj.cap - (32 + p1.length) - p2.length - 1) ⋆
                      bytes (s1Obj.addr + 32#64 + BitVec.ofNat 64 p1.length) p2 ⋆
                      cell64 s1Obj.addr s1Obj.header ⋆
                      cell64 (s1Obj.addr + 16#64) (BitVec.ofNat 64 s1Obj.cap) ⋆
                      bytes (s1Obj.addr + 32#64) p1 ⋆
                      lcnfHeap (objs.eraseIdx k1) ⋆ rtC0Inv rt st ⋆ R)) m4 :=
                  by rw [← hs1Addr] at hm4'; exact sep_cast hm4' (by ac_rfl)
                obtain ⟨hok24, hm5⟩ := r2b_c0_store_cell64_add24
                  (BitVec.ofNat 64 s1Obj.strLen + BitVec.ofNat 64 s2Obj.strLen) hmCell24
                rw [hs1Addr] at hok24 hm5
                try simp only [show (24 : BitVec 64) = 24#64 from rfl]
                apply wp_store_sep ⟨hok24, hm5⟩
                intro m5 hm5'
                r2b_steps
                let newPay := p1 ++ p2
                let newLen := (s1Obj.strLen + s2Obj.strLen) % 2 ^ 64
                let rObj := mkStrObj s1 1#32 s1Obj.cap newPay newLen
                let objs' := objs.map fun o => if o.addr = s1 then rObj else o
                have hm5Heap : (rtC0Inv rt st ⋆ lcnfHeap objs' ⋆ R) m5 := by
                  have hparts : (cell64 s1 strHeaderWord ⋆
                      cell64 (s1 + 8#64) (BitVec.ofNat 64 (newPay.length + 1)) ⋆
                      cell64 (s1 + 16#64) (BitVec.ofNat 64 s1Obj.cap) ⋆
                      cell64 (s1 + 24#64) (BitVec.ofNat 64 newLen) ⋆
                      bytes (s1 + 32#64) newPay ⋆
                      bytes (s1 + 32#64 + BitVec.ofNat 64 newPay.length) [(0 : UInt8)] ⋆
                      region (s1 + 32#64 + BitVec.ofNat 64 newPay.length + 1#64)
                        (strAllocBytes s1Obj.cap - (32 + newPay.length + 1)) ⋆
                      (rtC0Inv rt st ⋆ lcnfHeap (objs.eraseIdx k1) ⋆ R)) m5 := by
                    rw [hlenApp]
                    have hApp := bytes_append (s1 + 32#64) p1 p2
                      (by unfold strMaxCap at hnewLt; omega)
                    have haddLen :
                        BitVec.ofNat 64 s1Obj.strLen + BitVec.ofNat 64 s2Obj.strLen =
                          BitVec.ofNat 64 newLen := by
                      apply BitVec.eq_of_toNat_eq
                      simp [BitVec.toNat_add, BitVec.toNat_ofNat, newLen,
                        Nat.mod_eq_of_lt hlen1Lt, Nat.mod_eq_of_lt hlen2Lt]
                    rw [bv_ofNat_add1_mod64 newSz hnew64,
                      Nat.mod_eq_of_lt (by omega), haddLen] at hm5'
                    have hremEnd :
                        strAllocBytes s1Obj.cap - (32 + p1.length) - p2.length - 1 =
                        strAllocBytes s1Obj.cap - (32 + newSz + 1) := by
                      dsimp only [newSz]; omega
                    rw [hhdrWord, hremEnd] at hm5'
                    have hm5a : (cell64 s1 strHeaderWord ⋆
                        cell64 (s1 + 8#64) (BitVec.ofNat 64 (newSz + 1)) ⋆
                        cell64 (s1 + 16#64) (BitVec.ofNat 64 s1Obj.cap) ⋆
                        cell64 (s1 + 24#64) (BitVec.ofNat 64 newLen) ⋆
                        (bytes (s1 + 32#64) p1 ⋆
                          bytes (s1 + 32#64 + BitVec.ofNat 64 p1.length) p2) ⋆
                        bytes (s1 + 32#64 + BitVec.ofNat 64 newSz) [(0 : UInt8)] ⋆
                        region (s1 + 32#64 + BitVec.ofNat 64 newSz + 1#64)
                          (strAllocBytes s1Obj.cap - (32 + newSz + 1)) ⋆
                        (rtC0Inv rt st ⋆ lcnfHeap (objs.eraseIdx k1) ⋆ R)) m5 :=
                      sep_cast hm5' (by ac_rfl)
                    rwa [← hApp] at hm5a
                  have hmObj := mkStrObj_mem_of_parts hc1.2.2.2.2.2.2.2.2.1
                    (by rw [hlenApp]; exact hcapOk) hparts
                  have hrep :
                      lcnfHeap objs' = lcnfObjMem rObj ⋆ lcnfHeap (objs.eraseIdx k1) := by
                    dsimp only [objs']
                    rw [← hs1Addr]
                    exact lcnfObjMem_mkStr_replace hk1 hobj1 hnd
                  rw [hrep]
                  exact sep_cast hmObj (by ac_rfl)
                exact hpostK s1 st objs' m5 (hs1Addr ▸ hc1.1) (hs1Addr ▸ hc1.2.1)
                       (RtC0State.PreservesMeta.refl st) (Nat.le_refl _) (fun _ => ⟨rfl, rfl, rfl⟩)
                    (fun h => absurd hinp' h) hm5Heap
            · have hlenApp : (p1 ++ p2).length = newSz := by simp [newSz]
              have hnotIn' : ¬ (s1Obj.rc = 1#32 ∧ (p1 ++ p2).length + 1 ≤ s1Obj.cap) := by
                rw [hlenApp]; exact hinp
              rw [ite_eq_right hnotIn'] at hPost
              rcases hPost with ⟨hneg, hpostK⟩
              obtain ⟨hav, hrc1Ok⟩ := hneg hnotIn'
              let newCap := strGrowCap s1Obj.rc s1Obj.cap (newSz + 1)
              have hcapBnd := strGrowCap_props s1Obj.rc s1Obj.cap (newSz + 1)
                (by unfold strMaxCap at hnewLt ⊢; omega)
              have hnewCapLt64 : newCap < 2 ^ 64 := by unfold strMaxCap at *; omega
              have hnewCapTo : (BitVec.ofNat 64 newCap).toNat = newCap := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnewCapLt64]
              r2b_to_group
              c0_step
              r2b_to_group
              c0_step
              c0_step
              all_goals
                first
                | (have hcRc : (s1Obj.header &&& 4294967295#64) = 1#64 := by
                     rw [show (4294967295 : BitVec 64) = 4294967295#64 from rfl,
                       show (1 : BitVec 64) = 1#64 from rfl] at hc
                     exact hc
                   have hrc1 := obj_rc_of_mask_eq1 hwf1 hcRc
                   r2b_to_group
                   try simp only [show (4294967295 : BitVec 64) = 4294967295#64 from rfl,
                     hnewSzEq'])
                | (apply hJ () m; simp only [Blocks.get]; c0_step; r2b_to_group
                   try simp only [show (4294967295 : BitVec 64) = 4294967295#64 from rfl,
                     hnewSzEq'])
              all_goals
                refine wp_join_group
                  (P := fun (xs : Tup Val [i64]) m1 => match xs with
                    | (nc, PUnit.unit) => m1 = m ∧ nc = BitVec.ofNat 64 newCap) ?_ ?_
                · intro _ ⟨nc, ⟨⟩⟩ m1 ⟨rfl, hnc⟩
                  subst hnc
                  change LeanQbe.T.wp _ _ _ _ _
                  r2b_call rtR2bEnv_r2b_str_alloc_cap
                  dsimp only [r2bStrAllocCapSpec, vals, Tup.map, Arg.val]
                  have hvalid : newSz < strMaxCap ∧ newSz < newCap ∧ newCap ≤ strMaxCap :=
                    ⟨hnewLt, hcapBnd.1, hcapBnd.2⟩
                  rw [hnewTo, hnewCapTo, ite_eq_left hvalid]
                  refine ⟨st, lcnfHeap objs ⋆ R,
                    (by dsimp only [newCap]; rw [← hlenApp]; exact hav),
                    sep_cast hm (by ac_rfl), fun dst st1 m1 hdst0 hdst8 hpr1 hrem1 _ hm1 => ?_⟩
                  have hnewCapEq : newCap =
                      strGrowCap s1Obj.rc s1Obj.cap
                        ((strPayload s1Obj ++ strPayload s2Obj).length + 1) := by
                    dsimp only [newCap]; rw [hlenApp]
                  rw [hnewCapEq] at hm1
                  dsimp only [newSz, p1, p2] at hm1
                  exact str_append_slow_wp hs1Mem hs1Addr hc1 hs2Mem hs2Addr hc2 hwfObjs
                    hnotIn' hov hav hrc1Ok hm
                    (fun r st' objs' m' hr0 hr8 hpr hrem hneg =>
                      hpostK r st' objs' m' hr0 hr8 hpr hrem (fun h => absurd h hnotIn')
                        (fun _ => hneg))
                    dst st1 m1 hdst0 hdst8 hpr1 hrem1 (sep_cast hm1 (by ac_rfl))
                · intro Jcap hJcap
                  by_cases hrc1 : s1Obj.rc = 1#32
                  · have hmask1 : (s1Obj.header &&& 4294967295#64) = 1#64 := by
                      rw [hrc1Eq, hrc1]; rfl
                    have hcap1Max := hc1.2.2.2.2.2.2.2.2.1
                    have hltDouble : s1Obj.cap * 2 < 2 ^ 64 := by unfold strMaxCap at *; omega
                    have hmul : (BitVec.ofNat 64 s1Obj.cap * 2#64).toNat = s1Obj.cap * 2 := by
                      rw [BitVec.toNat_mul, hcapTo, show (2#64 : BitVec 64).toNat = 2 from rfl,
                        Nat.mod_eq_of_lt hltDouble]
                    have haddTo : (BitVec.ofNat 64 newSz + 1#64).toNat = newSz + 1 := hnew1To
                    r2b_steps <;> first
                      | (exfalso
                         have hne : (s1Obj.header &&& 4294967295#64) ≠ 1#64 := by assumption
                         exact hne hmask1)
                      | (exfalso
                         have hgt : 268435415 < (BitVec.ofNat 64 newSz + 1#64).toNat := by
                           assumption
                         rw [haddTo] at hgt
                         exact absurd hnew1LeMax (Nat.not_le_of_lt hgt))
                      | (try simp only [hnewSzEq']
                         have hd : newSz + 1 < s1Obj.cap * 2 := by
                           have h0 : (newSz + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
                               s1Obj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 := by
                             assumption
                           rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                             show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                             Nat.mod_eq_of_lt hnew164, Nat.mod_eq_of_lt hcap1Lt,
                             Nat.mod_eq_of_lt hltDouble] at h0
                           exact h0
                         have hgtCap : 268435415 < s1Obj.cap * 2 := by
                           have h0 : BitVec.toNat (268435415 : BitVec 64) <
                               s1Obj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 := by
                             assumption
                           rw [show BitVec.toNat (268435415 : BitVec 64) = 268435415 from rfl,
                             show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                             Nat.mod_eq_of_lt hcap1Lt, Nat.mod_eq_of_lt hltDouble] at h0
                           exact h0
                         apply hJcap _ m
                         refine ⟨rfl, ?_⟩
                         dsimp only [newCap]
                         rw [hrc1, strGrowCap_case_dbl_cap hd hgtCap]
                         rfl)
                      | (try simp only [hnewSzEq']
                         have hd : newSz + 1 < s1Obj.cap * 2 := by
                           have h0 : (newSz + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
                               s1Obj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 := by
                             assumption
                           rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                             show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                             Nat.mod_eq_of_lt hnew164, Nat.mod_eq_of_lt hcap1Lt,
                             Nat.mod_eq_of_lt hltDouble] at h0
                           exact h0
                         have hnc : ¬ 268435415 < s1Obj.cap * 2 := by
                           have h0 : ¬ BitVec.toNat (268435415 : BitVec 64) <
                               s1Obj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 := by
                             assumption
                           rw [show BitVec.toNat (268435415 : BitVec 64) = 268435415 from rfl,
                             show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                             Nat.mod_eq_of_lt hcap1Lt, Nat.mod_eq_of_lt hltDouble] at h0
                           exact h0
                         apply hJcap _ m
                         refine ⟨rfl, ?_⟩
                         dsimp only [newCap]
                         rw [hrc1, strGrowCap_case_dbl hd (Nat.not_lt.mp hnc)]
                         apply BitVec.eq_of_toNat_eq
                         rw [show (2 : BitVec 64) = 2#64 from rfl, hmul, BitVec.toNat_ofNat,
                           Nat.mod_eq_of_lt hltDouble])
                      | (try simp only [hnewSzEq']
                         have hnd : ¬ newSz + 1 < s1Obj.cap * 2 := by
                           have h0 : ¬ (newSz + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
                               s1Obj.cap % 2 ^ 64 * BitVec.toNat (2 : BitVec 64) % 2 ^ 64 := by
                             assumption
                           rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                             show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                             Nat.mod_eq_of_lt hnew164, Nat.mod_eq_of_lt hcap1Lt,
                             Nat.mod_eq_of_lt hltDouble] at h0
                           exact h0
                         apply hJcap _ m
                         refine ⟨rfl, ?_⟩
                         dsimp only [newCap]
                         rw [hrc1, strGrowCap_case_new (Nat.not_lt.mp hnd) hnew1LeMax]
                         rw [show (1 : BitVec 64) = 1#64 from rfl,
                           bv_ofNat_add1_mod64 newSz hnew64, Nat.mod_eq_of_lt hnew164])
                  · have hmaskNe : (s1Obj.header &&& 4294967295#64) ≠ 1#64 := by
                      intro h1; exact hrc1 (obj_rc_of_mask_eq1 hwf1 h1)
                    r2b_steps <;> first
                      | (exfalso
                         rename_i h1
                         rw [show (4294967295 : BitVec 64) = 4294967295#64 from rfl,
                           show (1 : BitVec 64) = 1#64 from rfl] at h1
                         exact hmaskNe h1)
                      | (apply hJcap _ m
                         refine ⟨rfl, ?_⟩
                         dsimp only [newCap, strGrowCap]
                         rw [ite_eq_right hrc1, show (1 : BitVec 64) = 1#64 from rfl,
                           bv_ofNat_add1_mod64 newSz hnew64, Nat.mod_eq_of_lt hnew164])
where
  LcnfC0StringsProof2_cap_bound (cap : Nat) (h : cap ≤ strMaxCap) : strAllocBytes cap ≤ 2 ^ 64 := by
    unfold strAllocBytes align8 strMaxCap at *; omega

/-! ## 4. `lcnf_string_cmp_op` WP Proof -/

theorem lcnf_string_cmp_op_wp :
    ∀ xs m Q X,
      lcnfStringCmpOpSpec xs m Q X → Func.wp rtR2bEnv lcnf_string_cmp_op_body xs m Q X := by
  intro ⟨rt, op, s1, s2, ⟨⟩⟩ m Q X hPre
  dsimp only [Func.wp, lcnf_string_cmp_op_body, lcnfStringCmpOpSpec] at hPre ⊢
  change LeanQbe.T.wp _ _ _ _ _
  by_cases hop : op = 0#64 ∨ op = 1#64 ∨ op = 2#64
  · rw [ite_eq_left hop] at hPre
    have hnotGt2 : ¬ (2#64 : BitVec 64).toNat < op.toNat := by
      rcases hop with rfl | rfl | rfl <;> decide
    r2b_to_group
    by_cases hs : s1 = s2
    · subst hs
      rw [ite_eq_left rfl] at hPre
      r2b_steps
      all_goals first
        | contradiction
        | (exfalso
           have hgt : 2 < op.toNat := by assumption
           rcases hop with rfl | rfl | rfl <;> decide)
        | (exfalso; exact (by assumption : s1 ≠ s1) rfl)
        | (have h0 : op = 0#64 := by assumption
           simpa [strCmpOpVal, h0, cmpByteSlices] using hPre)
        | (have h1 : op = 1#64 := by assumption
           simpa [strCmpOpVal, h1, cmpByteSlices] using hPre)
        | (have h2 : op = 2#64 := by assumption
           have h0 : op ≠ 0#64 := by assumption
           have h1 : op ≠ 1#64 := by assumption
           simpa [strCmpOpVal, h0, h1, cmpByteSlices] using hPre)
        | (exfalso
           rcases hop with rfl | rfl | rfl <;>
             exact (by assumption : ¬ _ = _) rfl)
    · rw [ite_eq_right hs] at hPre
      rcases hPre with ⟨s1Obj, s2Obj, R, hs1Addr, hc1, hs2Addr, hc2, hm, hPost⟩
      subst hs1Addr; subst hs2Addr
      have hp1Lt := str_payload_lt_max s1Obj hc1
      have hp2Lt := str_payload_lt_max s2Obj hc2
      have hp1To : (BitVec.ofNat 64 (strPayload s1Obj).length).toNat = (strPayload s1Obj).length :=
        by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold strMaxCap at hp1Lt; omega)]
      have hp2To : (BitVec.ofNat 64 (strPayload s2Obj).length).toNat = (strPayload s2Obj).length :=
        by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold strMaxCap at hp2Lt; omega)]
      have hm1 : (lcnfObjMem s1Obj ⋆ (lcnfObjMem s2Obj ⋆ R)) m := sep_cast hm (by ac_rfl)
      have hm2 : (lcnfObjMem s2Obj ⋆ (lcnfObjMem s1Obj ⋆ R)) m := sep_cast hm (by ac_rfl)
      have hload1 := str_load_sz hc1 hm1
      have hload2 := str_load_sz hc2 hm2
      rw [strObj_eq_bytes_rest hc1, strObj_eq_bytes_rest hc2] at hm1
      r2b_steps
      all_goals first
        | contradiction
        | (exfalso
           have hgt : 2 < op.toNat := by assumption
           rcases hop with rfl | rfl | rfl <;> contradiction)
        | (exfalso; exact hs (by assumption))
        | (apply wp_load_of hload1
           r2b_to_group
           try rw [str_sz_sub1_eq s1Obj hc1] at *
           apply wp_load_of hload2
           rcases hop with rfl | rfl | rfl
           · r2b_steps <;> (try rw [str_sz_sub1_eq s2Obj hc2] at *)
             all_goals first
               | contradiction
               | (have hne : BitVec.ofNat 64 (strPayload s1Obj).length ≠
                      BitVec.ofNat 64 (strPayload s2Obj).length := by assumption
                  have hneN : (strPayload s1Obj).length ≠ (strPayload s2Obj).length := by
                    intro h; apply hne; rw [h]
                  have hcmpNe : cmpByteSlices (strPayload s1Obj) (strPayload s2Obj) ≠ 1#64 :=
                    fun heq => hneN (cmpByteSlices_eq_one_len _ _ heq)
                  simpa [strCmpOpVal, hcmpNe] using hPost)
               | (r2b_call rtR2bEnv_r2b_cmp_byte_slices
                  dsimp only [r2CmpByteSlicesSpec, vals, Tup.map, Arg.val]
                  refine ⟨strPayload s1Obj, strPayload s2Obj,
                    strRest s1Obj ⋆ bytes (s2Obj.addr + 32#64) (strPayload s2Obj) ⋆
                      strRest s2Obj ⋆ R,
                    bytes (s1Obj.addr + 32#64) (strPayload s1Obj) ⋆ strRest s1Obj ⋆
                      strRest s2Obj ⋆ R,
                    hp1To.symm, hp2To.symm,
                    sep_cast (by simpa using hm1) (by ac_rfl),
                    sep_cast (by simpa using hm1) (by ac_rfl), ?_⟩
                  r2b_steps
                  · have h1 : cmpByteSlices (strPayload s1Obj) (strPayload s2Obj) = 1#64 := by
                      assumption
                    simpa [strCmpOpVal, h1] using hPost
                  · have hn1 : cmpByteSlices (strPayload s1Obj) (strPayload s2Obj) ≠ 1#64 := by
                      assumption
                    simpa [strCmpOpVal, hn1] using hPost)
           · r2b_steps <;> (try rw [str_sz_sub1_eq s2Obj hc2] at *)
             all_goals first
               | contradiction
               | (exfalso; exact (by decide : (1#64 : BitVec 64) ≠ 0#64) (by assumption))
               | (r2b_call rtR2bEnv_r2b_cmp_byte_slices
                  dsimp only [r2CmpByteSlicesSpec, vals, Tup.map, Arg.val]
                  refine ⟨strPayload s1Obj, strPayload s2Obj,
                    strRest s1Obj ⋆ bytes (s2Obj.addr + 32#64) (strPayload s2Obj) ⋆
                      strRest s2Obj ⋆ R,
                    bytes (s1Obj.addr + 32#64) (strPayload s1Obj) ⋆ strRest s1Obj ⋆
                      strRest s2Obj ⋆ R,
                    hp1To.symm, hp2To.symm,
                    sep_cast (by simpa using hm1) (by ac_rfl),
                    sep_cast (by simpa using hm1) (by ac_rfl), ?_⟩
                  r2b_steps
                  · have h0 : cmpByteSlices (strPayload s1Obj) (strPayload s2Obj) = 0#64 := by
                      assumption
                    simpa [strCmpOpVal, h0] using hPost
                  · have hn0 : cmpByteSlices (strPayload s1Obj) (strPayload s2Obj) ≠ 0#64 := by
                      assumption
                    simpa [strCmpOpVal, hn0] using hPost)
           · r2b_steps <;> (try rw [str_sz_sub1_eq s2Obj hc2] at *)
             all_goals first
               | contradiction
               | (exfalso; exact (by decide : (2#64 : BitVec 64) ≠ 0#64) (by assumption))
               | (exfalso; exact (by decide : (2#64 : BitVec 64) ≠ 1#64) (by assumption))
               | (r2b_call rtR2bEnv_r2b_cmp_byte_slices
                  dsimp only [r2CmpByteSlicesSpec, vals, Tup.map, Arg.val]
                  refine ⟨strPayload s1Obj, strPayload s2Obj,
                    strRest s1Obj ⋆ bytes (s2Obj.addr + 32#64) (strPayload s2Obj) ⋆
                      strRest s2Obj ⋆ R,
                    bytes (s1Obj.addr + 32#64) (strPayload s1Obj) ⋆ strRest s1Obj ⋆
                      strRest s2Obj ⋆ R,
                    hp1To.symm, hp2To.symm,
                    sep_cast (by simpa using hm1) (by ac_rfl),
                    sep_cast (by simpa using hm1) (by ac_rfl), ?_⟩
                  simpa [strCmpOpVal] using hPost))
  · rw [ite_eq_right hop] at hPre
    have hgt2 : 2 < op.toNat := by
      have h0 : op ≠ 0#64 := fun h => hop (Or.inl h)
      have h1 : op ≠ 1#64 := fun h => hop (Or.inr (Or.inl h))
      have h2 : op ≠ 2#64 := fun h => hop (Or.inr (Or.inr h))
      have hn0 : op.toNat ≠ 0 := fun hn => h0 (BitVec.eq_of_toNat_eq hn)
      have hn1 : op.toNat ≠ 1 := fun hn => h1 (BitVec.eq_of_toNat_eq hn)
      have hn2 : op.toNat ≠ 2 := fun hn => h2 (BitVec.eq_of_toNat_eq hn)
      omega
    r2b_steps
    exact hPre

end LeanQbe.T.LeanLCNF
