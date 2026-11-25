module

public import LeanQbe.T.LeanLCNF.LcnfC0RtProofCommon
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.ControlComb
import all Kraken.Separation

/-!
# Soundness Proofs for `LcnfC0Rt`, Part M0a (`lcnf_alloc`, `lcnf_free_obj`, `lcnf_clo_under`)

Proves `Func.wp` contracts for the three M0a runtime primitives, constructs `rtC0M0aEnv` and
`rtR0ModM0a`, and proves `rtR0ModM0a_ok` and `rtC0Env_clo_under_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T
open LeanQbe.T.C0Step
open Std.ExtHashMap
open LeanQbe.T.LeanLCNF.RtProof
open scoped LeanQbe.T.LeanLCNF.RtProof

@[local c0_load] private theorem c0_load_rt_allocs64 {p : BitVec 64} {s : LcnfC0Rt}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) :
    loadVal m i64 (p + 33608#64) = some s.s_st_allocs := LcnfC0Rt.load_s_st_allocs h
@[local c0_store] private theorem c0_store_rt_allocs64 {p : BitVec 64} {s : LcnfC0Rt}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) :
    storeOk m i64 (p + 33608#64) ∧ (LcnfC0Rt.At p { s with s_st_allocs := v } ⋆ R)
    (storeMem m i64 (p + 33608#64) v) := LcnfC0Rt.store_s_st_allocs v h
@[local c0_load] private theorem c0_load_rt_frees64 {p : BitVec 64} {s : LcnfC0Rt}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) :
    loadVal m i64 (p + 33616#64) = some s.s_st_frees := LcnfC0Rt.load_s_st_frees h
@[local c0_store] private theorem c0_store_rt_frees64 {p : BitVec 64} {s : LcnfC0Rt}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) :
    storeOk m i64 (p + 33616#64) ∧ (LcnfC0Rt.At p { s with s_st_frees := v } ⋆ R)
    (storeMem m i64 (p + 33616#64) v) := LcnfC0Rt.store_s_st_frees v h
@[local c0_load] private theorem c0_load_rt_live64 {p : BitVec 64} {s : LcnfC0Rt}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) :
    loadVal m i64 (p + 33624#64) = some s.s_st_live := LcnfC0Rt.load_s_st_live h
@[local c0_store] private theorem c0_store_rt_live64 {p : BitVec 64} {s : LcnfC0Rt}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) :
    storeOk m i64 (p + 33624#64) ∧ (LcnfC0Rt.At p { s with s_st_live := v } ⋆ R)
    (storeMem m i64 (p + 33624#64) v) := LcnfC0Rt.store_s_st_live v h
@[local c0_load] private theorem c0_load_rt_peak_live64 {p : BitVec 64} {s : LcnfC0Rt}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) :
    loadVal m i64 (p + 33632#64) = some s.s_st_peak_live := LcnfC0Rt.load_s_st_peak_live h
@[local c0_store] private theorem c0_store_rt_peak_live64 {p : BitVec 64} {s : LcnfC0Rt}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) :
    storeOk m i64 (p + 33632#64) ∧ (LcnfC0Rt.At p { s with s_st_peak_live := v } ⋆ R)
    (storeMem m i64 (p + 33632#64) v) := LcnfC0Rt.store_s_st_peak_live v h
@[local c0_load] private theorem c0_load_rt_bytes64 {p : BitVec 64} {s : LcnfC0Rt}
    {R : Mem 64 → Prop} {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) :
    loadVal m i64 (p + 33664#64) = some s.s_st_bytes := LcnfC0Rt.load_s_st_bytes h
@[local c0_store] private theorem c0_store_rt_bytes64 {p : BitVec 64} {s : LcnfC0Rt}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h : (LcnfC0Rt.At p s ⋆ R) m) :
    storeOk m i64 (p + 33664#64) ∧ (LcnfC0Rt.At p { s with s_st_bytes := v } ⋆ R)
    (storeMem m i64 (p + 33664#64) v) := LcnfC0Rt.store_s_st_bytes v h

private abbrev rtCore (rt : BitVec 64) (st : RtC0State) (fl : List (BitVec 64))
    (h : LcnfC0Rt) : Mem 64 → Prop :=
  array64 rt st.extraArgs ⋆ array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
    array64 (rt + 33024#64) fl ⋆ LcnfC0Rt.At rt h ⋆ array64 st.hdr.s_work st.workBuf

/-! ## 1. Small Freelist, `large_free`, and Bump Helpers -/

private theorem smallPoolSlot_hd_eq {cls : Nat} {hd : BitVec 64} {nodes : List (BitVec 64)}
    {m : Mem 64} (h2 : 2 ≤ cls) (h : smallPoolSlot cls hd nodes m) : hd = listHeadPtr nodes := by
  simp only [smallPoolSlot, h2, ↓reduceIte] at h
  cases nodes <;> exact h.1

private theorem smallPoolSlot_pop {cls : Nat} {hd : BitVec 64} {nodes : List (BitVec 64)}
    {m : Mem 64} (h2 : 2 ≤ cls) (hne : hd ≠ 0#64) (h : smallPoolSlot cls hd nodes m) :
    ∃ rest, nodes = hd :: rest ∧ hd.toNat % 8 = 0 ∧
    ((region hd 8 ⋆ cell64 (hd + 8#64) (listHeadPtr rest) ⋆ region (hd + 16#64) (8 * cls - 16)) ⋆
    smallFreeList (8 * cls) (listHeadPtr rest) rest) m := by
  simp only [smallPoolSlot, h2, ↓reduceIte] at h
  cases nodes with
  | nil => exact absurd h.1 hne
  | cons p rest =>
    rcases h with ⟨rfl, _, halign, hmem⟩; exact ⟨rest, rfl, halign, hmem⟩

private theorem smallPoolSlot_nil_of_zero {cls : Nat} {nodes : List (BitVec 64)}
    {m : Mem 64} (h2 : 2 ≤ cls) (h : smallPoolSlot cls 0#64 nodes m) : nodes = [] := by
  simp only [smallPoolSlot, h2, ↓reduceIte] at h
  cases nodes with
  | nil => rfl
  | cons _ _ => exact absurd h.1.symm h.2.1

private theorem smallPoolsAt_zero_empty {fl : List (BitVec 64)} {pools : Nat → List (BitVec 64)}
    {cls : Nat} {Q : Mem 64 → Prop} {m : Mem 64}
    (_hflLen : fl.length = rtNumClasses) (h2 : 2 ≤ cls) (hlt : cls < rtNumClasses)
    (hz : fl[cls]'(by omega) = 0#64)
    (h : (smallPoolsAt fl pools rtNumClasses ⋆ Q) m) : pools cls = [] := by
  rw [smallPoolsAt_split rtNumClasses fl pools hlt, sep_assoc] at h
  have hget : fl.getD cls 0#64 = 0#64 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : cls < fl.length), hz]
  rw [hget] at h; obtain ⟨m1, _, _, _, hs, _⟩ := h; exact smallPoolSlot_nil_of_zero h2 hs

private theorem smallPoolsAt_pop {fl : List (BitVec 64)} {pools : Nat → List (BitVec 64)}
    {cls : Nat} {Q : Mem 64 → Prop} {m : Mem 64}
    (_hflLen : fl.length = rtNumClasses) (h2 : 2 ≤ cls) (hlt : cls < rtNumClasses)
    (hne : fl[cls]'(by omega) ≠ 0#64) (h : (smallPoolsAt fl pools rtNumClasses ⋆ Q) m) :
    ∃ rest, pools cls = (fl[cls]'(by omega)) :: rest ∧ (fl[cls]'(by omega)).toNat % 8 = 0 ∧
    ((region (fl[cls]'(by omega)) 8 ⋆ cell64 ((fl[cls]'(by omega)) + 8#64) (listHeadPtr rest) ⋆
    region ((fl[cls]'(by omega)) + 16#64) (8 * cls - 16)) ⋆
    smallFreeList (8 * cls) (listHeadPtr rest) rest ⋆
    smallPoolsExcl cls fl pools rtNumClasses ⋆ Q) m := by
  rw [smallPoolsAt_split rtNumClasses fl pools hlt, sep_assoc] at h
  have hget : fl.getD cls 0#64 = fl[cls]'(by omega) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : cls < fl.length)]
  rw [hget] at h; obtain ⟨m1, m2, rfl, hd, hslot, hrest⟩ := h
  obtain ⟨rest, hp, halign, hlist⟩ := smallPoolSlot_pop h2 hne hslot
  refine ⟨rest, hp, halign, ?_⟩
  have h1 : (((region (fl[cls]'(by omega)) 8 ⋆
      cell64 ((fl[cls]'(by omega)) + 8#64) (listHeadPtr rest) ⋆
      region ((fl[cls]'(by omega)) + 16#64) (8 * cls - 16)) ⋆
      smallFreeList (8 * cls) (listHeadPtr rest) rest) ⋆
      (smallPoolsExcl cls fl pools rtNumClasses ⋆ Q)) (m1.union m2) :=
    ⟨m1, m2, rfl, hd, hlist, hrest⟩
  repeat rw [← sep_assoc] at h1; exact h1

private theorem smallPoolsAt_pop_head {fl fl' : List (BitVec 64)}
    {pools pools' : Nat → List (BitVec 64)} {cls : Nat} {nxt : BitVec 64}
    {rest : List (BitVec 64)} {Q : Mem 64 → Prop} {m : Mem 64}
    (hlt : cls < rtNumClasses) (h2 : 2 ≤ cls)
    (hget : fl'.getD cls 0#64 = nxt) (hpcls : pools' cls = rest) (hnxt : nxt = listHeadPtr rest)
    (hfl : ∀ i, i ≠ cls → fl'.getD i 0#64 = fl.getD i 0#64)
    (hp : ∀ i, i ≠ cls → pools' i = pools i) (h : ((smallFreeList (8 * cls) nxt rest ⋆
    smallPoolsExcl cls fl pools rtNumClasses) ⋆ Q) m) :
    (smallPoolsAt fl' pools' rtNumClasses ⋆ Q) m := by
  subst hpcls hnxt; rw [← hget] at h
  have hslot : ((smallPoolSlot cls (fl'.getD cls 0#64) (pools' cls) ⋆
      smallPoolsExcl cls fl' pools' rtNumClasses) ⋆ Q) m := by
    rw [smallPoolsExcl_update fl fl' pools pools' hfl hp]
    simpa only [smallPoolSlot, h2, ↓reduceIte] using h
  rwa [← smallPoolsAt_split rtNumClasses fl' pools' hlt] at hslot

private theorem smallPoolsAt_push_head {fl fl' : List (BitVec 64)}
    {pools pools' : Nat → List (BitVec 64)} {cls : Nat} {o oldHd : BitVec 64}
    {Q : Mem 64 → Prop} {m : Mem 64}
    (_hflLen : fl.length = rtNumClasses) (hlt : cls < rtNumClasses) (h2 : 2 ≤ cls)
    (hnz : o ≠ 0#64) (halign : o.toNat % 8 = 0)
    (hgetOld : fl.getD cls 0#64 = oldHd) (hgetNew : fl'.getD cls 0#64 = o)
    (hpcls : pools' cls = o :: pools cls) (hfl : ∀ i, i ≠ cls → fl'.getD i 0#64 = fl.getD i 0#64)
    (hp : ∀ i, i ≠ cls → pools' i = pools i)
    (h : (((region o 8 ⋆ cell64 (o + 8#64) oldHd) ⋆ region (o + 16#64) (8 * cls - 16)) ⋆
    (smallPoolsAt fl pools rtNumClasses ⋆ Q)) m) :
    (smallPoolsAt fl' pools' rtNumClasses ⋆ Q) m := by
  rw [smallPoolsAt_split rtNumClasses fl pools hlt, hgetOld] at h
  have hhd : oldHd = listHeadPtr (pools cls) := by
    obtain ⟨_, _, _, _, _, hs⟩ := h; rw [sep_assoc] at hs
    obtain ⟨_, _, _, _, hslot, _⟩ := hs; exact smallPoolSlot_hd_eq h2 hslot
  rw [hhd] at h
  have h1 : (((((region o 8 ⋆ cell64 (o + 8#64) (listHeadPtr (pools cls))) ⋆
      region (o + 16#64) (8 * cls - 16)) ⋆
      smallFreeList (8 * cls) (listHeadPtr (pools cls)) (pools cls)) ⋆
      smallPoolsExcl cls fl pools rtNumClasses) ⋆ Q) m := by
    have hslotEq : smallPoolSlot cls (listHeadPtr (pools cls)) (pools cls) =
        smallFreeList (8 * cls) (listHeadPtr (pools cls)) (pools cls) := by
      simp [smallPoolSlot, h2]
    have h' : ((((region o 8 ⋆ cell64 (o + 8#64) (listHeadPtr (pools cls))) ⋆
        region (o + 16#64) (8 * cls - 16)) ⋆
        smallPoolSlot cls (listHeadPtr (pools cls)) (pools cls) ⋆
        smallPoolsExcl cls fl pools rtNumClasses) ⋆ Q) m :=
      sep_cast h (by ac_rfl)
    rw [hslotEq] at h'; exact sep_cast h' (by ac_rfl)
  have hslot' : ((smallPoolSlot cls o (o :: pools cls) ⋆
      smallPoolsExcl cls fl pools rtNumClasses) ⋆ Q) m := by
    refine sep_mono (fun _ hx => sep_mono (fun _ hy => ?_) hx) h1
    simp only [smallPoolSlot, h2, ↓reduceIte]; exact ⟨rfl, hnz, halign, hy⟩
  rw [← hpcls, ← hgetNew, ← smallPoolsExcl_update fl fl' pools pools' hfl hp] at hslot'
  rwa [← smallPoolsAt_split rtNumClasses fl' pools' hlt] at hslot'

private def largeSegSplit (hd prev lcur : BitVec 64)
    (pfx sfx : List (BitVec 64 × Nat)) (m : Mem 64) : Prop :=
  lcur = largeSegNext 0#64 sfx ∧ match pfx.reverse with
  | [] => prev = 0#64 ∧ hd = lcur ∧ largeSeg hd 0#64 sfx m
  | (prv, prvB) :: revMid =>
    prev = prv ∧ prv ≠ 0#64 ∧ prv.toNat % 8 = 0 ∧ 512 ≤ prvB ∧ prvB < rtMaxObjBytes ∧
    prvB % 8 = 0 ∧
    ((largeSeg hd prv revMid.reverse ⋆ largeFreeNode prvB prv lcur) ⋆ largeSeg lcur 0#64 sfx) m

private theorem largeSegSplit_init {hd : BitVec 64} {nodes : List (BitVec 64 × Nat)}
    {m : Mem 64} (h : largeFreeList hd nodes m) : largeSegSplit hd 0#64 hd [] nodes m :=
  ⟨largeSeg_hd_eq_next h, rfl, rfl, h⟩

private theorem largeSegSplit_nil {hd prev : BitVec 64}
    {pfx : List (BitVec 64 × Nat)} {m : Mem 64}
    (h : largeSegSplit hd prev 0#64 pfx [] m) : largeFreeList hd pfx m := by
  rcases h with ⟨_, hs⟩
  cases hr : pfx.reverse with
  | nil =>
    rw [hr] at hs; have hp : pfx = [] := List.reverse_eq_nil_iff.mp hr; subst hp; exact hs.2.2
  | cons hdRev tlRev =>
    rw [hr] at hs; rcases hdRev with ⟨prv, prvB⟩
    rcases hs with ⟨_, hnz, hal, hlo, hhi, hmod, hmem⟩
    have hp : pfx = tlRev.reverse ++ [(prv, prvB)] := by rw [← List.reverse_reverse pfx, hr]; simp
    rw [hp]
    change ((largeSeg hd prv tlRev.reverse ⋆ largeFreeNode prvB prv 0#64) ⋆
      (fun m => 0#64 = 0#64 ∧ emp m)) m at hmem
    rw [sep_comm, sep_pure_l, emp_sep] at hmem
    exact largeSeg_split_snoc hnz hal hlo hhi hmod tlRev.reverse hmem.2

private theorem largeSegSplit_step {hd prev lcur nxt : BitVec 64} {b : Nat}
    {pfx rest : List (BitVec 64 × Nat)} {m : Mem 64}
    (hcur : lcur ≠ 0#64) (hal : lcur.toNat % 8 = 0)
    (hlo : 512 ≤ b) (hhi : b < rtMaxObjBytes) (hmod : b % 8 = 0)
    (hnxt : nxt = largeSegNext 0#64 rest) (hpfx : match pfx.reverse with
      | [] => prev = 0#64 ∧ hd = lcur ∧ (largeFreeNode b lcur nxt ⋆ largeSeg nxt 0#64 rest) m
      | (prv, prvB) :: revMid =>
        prev = prv ∧ prv ≠ 0#64 ∧ prv.toNat % 8 = 0 ∧ 512 ≤ prvB ∧ prvB < rtMaxObjBytes ∧
        prvB % 8 = 0 ∧
        ((largeSeg hd prv revMid.reverse ⋆ largeFreeNode prvB prv lcur) ⋆
          (largeFreeNode b lcur nxt ⋆ largeSeg nxt 0#64 rest)) m) :
    largeSegSplit hd lcur nxt (pfx ++ [(lcur, b)]) rest m := by
  refine ⟨hnxt, ?_⟩
  have hrev : (pfx ++ [(lcur, b)]).reverse = (lcur, b) :: pfx.reverse := by simp
  rw [hrev]; dsimp only; rw [List.reverse_reverse]
  refine ⟨rfl, hcur, hal, hlo, hhi, hmod, ?_⟩
  cases hr : pfx.reverse with
  | nil =>
    rw [hr] at hpfx; have hp : pfx = [] := List.reverse_eq_nil_iff.mp hr
    subst hp; rcases hpfx with ⟨_, heq, hmem⟩
    subst heq; change ((largeSeg hd hd [] ⋆ largeFreeNode b hd nxt) ⋆ largeSeg nxt 0#64 rest) m
    refine sep_mono (fun _ hx => ?_) hmem
    change ((fun m => hd = hd ∧ emp m) ⋆ largeFreeNode b hd nxt) _; rw [sep_pure_l, emp_sep]
    exact ⟨rfl, hx⟩
  | cons hdRev tlRev =>
    rw [hr] at hpfx; rcases hdRev with ⟨prv, prvB⟩
    rcases hpfx with ⟨_, hnz, halp, hlop, hhip, hmodp, hmem⟩
    have hp : pfx = tlRev.reverse ++ [(prv, prvB)] := by rw [← List.reverse_reverse pfx, hr]; simp
    rw [← sep_assoc] at hmem
    refine sep_mono (fun _ hx => sep_mono (fun _ hy => ?_) hx) hmem
    rw [hp]; exact largeSeg_split_snoc hnz halp hlop hhip hmodp tlRev.reverse hy

private theorem largeSegSplit_sfx_nil_of_zero {hd prev : BitVec 64}
    {pfx sfx : List (BitVec 64 × Nat)} {m : Mem 64}
    (h : largeSegSplit hd prev 0#64 pfx sfx m) : sfx = [] := by
  rcases h with ⟨hnext, hs⟩
  cases sfx with
  | nil => rfl
  | cons x rest =>
    dsimp only [largeSegNext] at hnext
    cases hr : pfx.reverse with
    | nil =>
      rw [hr] at hs; rcases hs with ⟨_, _, hseg⟩
      rcases hseg with ⟨_, hnz, _⟩; exact absurd hnext.symm hnz
    | cons _ _ =>
      rw [hr] at hs; rcases hs with ⟨_, _, _, _, _, _, hmem⟩
      rcases hmem with ⟨_, _, _, _, _, hseg⟩; rcases hseg with ⟨_, hnz, _⟩
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
      ((region p 8 ⋆ cell64 (p + 8#64) nxt) ⋆ region (p + 16#64) (8 * cls - 16))) ⋆ Q) m :=
    sep_cast h (by ac_rfl)
  rw [sep_assoc] at h1; have h2' := smallPoolsAt_pop_head hlt h2 hget hpcls hnxt hfl hp h1
  rw [← sep_assoc] at h2'
  exact sep_mono
    (fun _ x => sep_mono_r (fun _ y => smallFreeNode_to_region (by omega) hmax y) x) h2'

private theorem alloc_bump_split {cur : BitVec 64} {bytes rem : Nat}
    {Q : Mem 64 → Prop} {m : Mem 64} (_hle : bytes ≤ rem) (hfit : bytes + (rem - bytes) ≤ 2 ^ 64)
    (h : (region cur rem ⋆ Q) m) :
    (region (cur + BitVec.ofNat 64 bytes) (rem - bytes) ⋆ region cur bytes ⋆ Q) m := by
  have hsplit : region cur rem =
      (region cur bytes ⋆ region (cur + BitVec.ofNat 64 bytes) (rem - bytes)) := by
    have hs := region_split (a := cur) (n1 := bytes) (n2 := rem - bytes) hfit
    rwa [show bytes + (rem - bytes) = rem by omega] at hs
  rw [hsplit] at h; exact sep_cast h (by ac_rfl)

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
    largeSeg nxt 0#64 rest) m) : largeFreeList hd (revMid.reverse ++ (prv, prvB) :: rest) m := by
  rw [show revMid.reverse ++ (prv, prvB) :: rest =
    (revMid.reverse ++ [(prv, prvB)]) ++ rest by simp]
  refine largeSeg_append (mid := nxt) _ rest ?_
  exact sep_mono (fun _ hx => largeSeg_split_snoc hnz hal hlo hhi hmod revMid.reverse hx) hm

private def RtC0State.withBump (st : RtC0State) (bytes : Nat) (hmax : bytes < rtMaxObjBytes)
    (hrem : bytes ≤ st.rem) (hmod : bytes % 8 = 0) : RtC0State :=
  { st with
    hdr := { st.hdr with s_cur := st.hdr.s_cur + BitVec.ofNat 64 bytes }
    curLeEnd := bump_curLeEnd st.curLeEnd hmax hrem
    arenaAlign := bump_cur_align st.arenaAlign st.curLeEnd hrem hmod
    curNz := bump_cur_nz st.curNz st.curLeEnd hrem }

private theorem region_merge8 {a : BitVec 64} {n : Nat} (hlt : n ≤ 2 ^ 64) (h8 : 8 ≤ n) :
    (region a 8 ⋆ region (a + 8#64) (n - 8)) = region a n := by
  have hs := (region_split (a := a) (n1 := 8) (n2 := n - 8) (by omega)).symm
  rwa [show a + BitVec.ofNat 64 8 = a + 8#64 from rfl, show 8 + (n - 8) = n by omega] at hs

private theorem region_pop8_cell64 {a : BitVec 64} (n : Nat) {Q : Mem 64 → Prop} {m : Mem 64}
    (h8 : 8 ≤ n) (hlt : n ≤ 2 ^ 64) (h : (region a n ⋆ Q) m) :
    ∃ v : BitVec 64, (cell64 a v ⋆ region (a + 8#64) (n - 8) ⋆ Q) m := by
  rw [← region_merge8 hlt h8, sep_assoc] at h
  obtain ⟨m1, m2, rfl, hd, hr8, hRest⟩ := h; obtain ⟨v, hv⟩ := region_to_cell64 hr8
  have h1 : (cell64 a v ⋆ (region (a + 8#64) (n - 8) ⋆
      Q)) (m1.union m2) := ⟨m1, m2, rfl, hd, hv, hRest⟩
  exact ⟨v, sep_cast h1 (by ac_rfl)⟩

private theorem sep_mid_exists_pure {α : Type _} {φ1 φ2 : α → Prop} {A : Mem 64 → Prop}
    {P : α → Mem 64 → Prop} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (fun mf => ∃ x, φ1 x ∧ φ2 x ∧ P x mf) ⋆ R) m) :
    ∃ x, φ1 x ∧ φ2 x ∧ (A ⋆ P x ⋆ R) m := by
  obtain ⟨mAF, mR, rfl, hd1, ⟨mA, mF, rfl, hd2, hA, x, hx1, hx2, hP⟩, hR⟩ := h
  exact ⟨x, hx1, hx2, mA.union mF, mR, rfl, hd1, ⟨mA, mF, rfl, hd2, hA, hP⟩, hR⟩

private theorem bv64_eq_lt_max {a b : Nat} (ha : a < rtMaxObjBytes) (hb : b < rtMaxObjBytes)
    (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) : a = b := by
  unfold rtMaxObjBytes at ha hb; have := congrArg BitVec.toNat h
  simpa [Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]
    using this

/-! ## 2. `lcnf_alloc_wp` -/

private theorem alloc_bump_check_wp {Γ : Env} {rt : BitVec 64} {st : RtC0State}
    {bytes : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hmax : bytes < rtMaxObjBytes) (hmod : bytes % 8 = 0)
    (hrem : bytes ≤ st.rem) (hm : (rtCore rt st st.freeList st.hdr ⋆
    smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
    largeFreeList st.hdr.s_large_free st.largeNodes ⋆ region st.hdr.s_cur st.rem ⋆ R) m)
    {J : Cont [i64]} (hJ : ∀ (p : BitVec 64) (st' : RtC0State) (m' : Mem 64),
    p ≠ 0#64 → p.toNat % 8 = 0 → st'.PreservesMeta st → st'.rem ≤ st.rem →
    (rtC0Inv rt st' ⋆ region p bytes ⋆ R) m' → J (p, ()) m') : wp Γ Q X
    (.let_ (Op.mk (.add i64) (.var rt, .imm 33552, ())) fun p_12 =>
      .load i64 (.var p_12.fst) fun ld =>
    .let_ (Op.mk (.add i64) (.var rt, .imm 33560, ())) fun p_13 =>
      .load i64 (.var p_13.fst) fun ld_1 =>
    .group (sig := [[]]) (fun _Js => .cons (fun _ => .exit "lcnf_panic" (as := [i64, i64])
        (Arg.var rt, Arg.imm (t := i64) 3#64, ())) .nil) fun Js_1 =>
    .let_ (Op.mk (.cmp .ult i64) (.var ld_1, .var ld, ())) fun p_14 =>
    .jnz (.var p_14.fst) (.jump Js_1.fst ())
      (.let_ (Op.mk (.sub i64) (.var ld_1, .var ld, ())) fun p_15 =>
      .let_ (Op.mk (.cmp .ugt i64) (.var (BitVec.ofNat 64 bytes), .var p_15.fst, ())) fun p_16 =>
      .jnz (.var p_16.fst) (.jump Js_1.fst ())
        (.let_ (Op.mk (.add i64) (.var ld, .var (BitVec.ofNat 64 bytes), ())) fun p_17 =>
        .let_ (Op.mk (.add i64) (.var rt, .imm 33552, ())) fun p_18 =>
        .store (.var p_17.fst) (.var p_18.fst) (.jump J (.var ld, ()))))) m := by
  dsimp only [rtCore] at hm; iterate 4 c0_hstep
  refine wp_join_group (fun _ _ => False) (fun _ _ _ hf => False.elim hf) ?_
  intro _Js _hJs; c0_hsteps_nogrp
  · exfalso; have := st.curLeEnd; omega
  · exfalso
    have hcur : st.hdr.s_cur.toNat ≤ st.hdr.s_end.toNat := st.curLeEnd
    unfold RtC0State.rem at hrem
    have hsub : (2 ^ 64 - st.hdr.s_cur.toNat + st.hdr.s_end.toNat) % 2 ^ 64 =
        st.hdr.s_end.toNat - st.hdr.s_cur.toNat := by
      have := st.hdr.s_end.isLt
      rw [show 2 ^ 64 - st.hdr.s_cur.toNat + st.hdr.s_end.toNat =
        2 ^ 64 + (st.hdr.s_end.toNat - st.hdr.s_cur.toNat) by omega,
        Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
    rw [hsub] at hc; omega
  · have hsum : bytes + (st.rem - bytes) ≤ 2 ^ 64 := by
      have := st.hdr.s_end.isLt
      have hcur : st.hdr.s_cur.toNat ≤ st.hdr.s_end.toNat := st.curLeEnd
      unfold RtC0State.rem at hrem ⊢; omega
    let st1 := st.withBump bytes hmax hrem hmod
    have hm1 : (rtC0Inv rt st1 ⋆ region st.hdr.s_cur bytes ⋆ R) ‹_› := by
      have hmReg : (region st.hdr.s_cur st.rem ⋆
          (rtCore rt st st.freeList st1.hdr ⋆
            smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
            largeFreeList st.hdr.s_large_free st.largeNodes ⋆ R)) ‹_› := by
        dsimp [st1, RtC0State.withBump]; (try dsimp only [rtCore] at *); c0_frame
      have hsp := alloc_bump_split hrem hsum hmReg
      have hrem1 : st1.rem = st.rem - bytes := bump_rem_eq st.curLeEnd hmax hrem; unfold rtC0Inv
      rw [hrem1]; dsimp [st1, RtC0State.withBump] at hsp ⊢
      exact sep_cast hsp (by (try unfold rtCore); ac_rfl)
    refine hJ st.hdr.s_cur st1 _ st.curNz st.arenaAlign (by state_frame) ?_ hm1
    dsimp [st1, RtC0State.withBump]; unfold RtC0State.rem
    rw [bump_rem_eq st.curLeEnd hmax hrem]; omega

theorem lcnf_alloc_wp (Γ : Env) :
    ∀ xs m Q X, lcnfAllocSpec xs m Q X → Func.wp Γ lcnf_alloc_body xs m Q X := by
  rintro ⟨rt, sz, ⟨⟩⟩ m Q X ⟨st, R, hsz, hmin, hmax, havail, hm, hQ⟩; let bytes := align8 sz.toNat
  let bytesBV : BitVec 64 := BitVec.ofNat 64 bytes
  have hcurLe : st.hdr.s_cur.toNat ≤ st.hdr.s_end.toNat := st.curLeEnd
  have hflLen : st.freeList.length = 64 := st.freeListLen
  have hbyBv : (sz + 7) &&& 18446744073709551608 = bytesBV := align8_bv_eq sz hsz
  have hclsEq : ((sz + 7) &&& 18446744073709551608) >>> 3 = BitVec.ofNat 64 (bytes / 8) :=
    align8_div8_eq sz hsz
  have hbyMod : bytes % 8 = 0 := by unfold bytes align8; omega
  have hby16 : ¬ bytesBV.toNat < 16 := by
    unfold bytesBV bytes rtMinObjBytes rtMaxObjBytes at *
    have : align8 sz.toNat < 2 ^ 64 := by unfold align8; omega
    c0_bv_omega
  have hbyMax : bytes < rtMaxObjBytes := hmax; dsimp [Func.wp, lcnf_alloc_body]; c0_hsteps_nogrp
  · exfalso; unfold rtMinObjBytes align8 at hmin; omega
  have hbyBv' : sz + 7#64 &&& 18446744073709551608#64 = bytesBV := hbyBv
  have hclsBV : bytesBV >>> OfNat.ofNat 3 = BitVec.ofNat 64 (bytes / 8) := by
    rw [← hbyBv']; exact hclsEq
  dsimp only; rw [hbyBv', hclsBV]
  refine wp_join_state1 (t := i64) (fun st' : RtC0State × BitVec 64 => st'.2)
    (fun (st', p) m' => p ≠ 0#64 ∧ p.toNat % 8 = 0 ∧ st'.PreservesMeta st ∧ st'.rem ≤ st.rem ∧
      (rtC0Inv rt st' ⋆ region p bytes ⋆ R) m') ?_ ?_
  · rintro Jret ⟨st', p⟩ m' ⟨hpNz, hpAl, hMeta, hRem, hm'⟩
    unfold rtC0Inv at hm'; (try dsimp only [rtCore] at *); c0_hsteps
    · refine hQ p { st' with hdr := { st'.hdr with
          s_st_allocs := st'.hdr.s_st_allocs + 1#64
          s_st_bytes := bytesBV + st'.hdr.s_st_bytes
          s_st_live := st'.hdr.s_st_live + 1#64
          s_st_peak_live := st'.hdr.s_st_live + 1#64 } } _
        hpNz hpAl (by state_frame; all_goals exact ‹_›) hRem ?_
      unfold rtC0Inv; exact sep_cast ‹_› (by (try unfold rtCore); ac_rfl)
    · refine hQ p { st' with hdr := { st'.hdr with
          s_st_allocs := st'.hdr.s_st_allocs + 1#64
          s_st_bytes := bytesBV + st'.hdr.s_st_bytes
          s_st_live := st'.hdr.s_st_live + 1#64 } } _
        hpNz hpAl (by state_frame; all_goals exact ‹_›) hRem ?_
      unfold rtC0Inv; exact sep_cast ‹_› (by (try unfold rtCore); ac_rfl)
  ·
      intro Jret hJret; unfold rtC0Inv at hm
      have hbyLt64 : bytes < 2 ^ 64 := by dsimp [bytes]; unfold rtMaxObjBytes at hmax; omega
      by_cases hsmall : bytes / 8 < 64
      · have hcls2 : 2 ≤ bytes / 8 := by dsimp [bytes]; unfold rtMinObjBytes at hmin; omega
        have hbyEq : 8 * (bytes / 8) = bytes := align8_div8_mul8 hbyMod
        have hflLt : (BitVec.ofNat 64 (bytes / 8)).toNat < st.freeList.length := by
          rw [hflLen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hsmall
        c0_hsteps_nogrp
        refine wp_join_group (fun (q : Tup Val [i64]) m' =>
            ∃ st' : RtC0State, q.fst ≠ 0#64 ∧ q.fst.toNat % 8 = 0 ∧ st'.PreservesMeta st ∧
              st'.rem ≤ st.rem ∧ (rtC0Inv rt st' ⋆ region q.fst bytes ⋆ R) m')
          (fun _ q m' ⟨st', h1, h2, h3, h4, h5⟩ => hJret (st', q.fst) m' ⟨h1, h2, h3, h4, h5⟩) ?_
        intro Jp hJp
        by_cases hpz : st.freeList[bytes / 8]'(by rw [hflLen]; exact hsmall) = 0#64
        · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : bytes / 8 < 2 ^ 64)]
          rw [hpz]; c0_hstep; c0_hstep
          have hmPull : (smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
                (rtCore rt st st.freeList st.hdr ⋆
                  largeFreeList st.hdr.s_large_free st.largeNodes ⋆
                  region st.hdr.s_cur st.rem ⋆ R)) m := sep_cast hm
                    (by (try unfold rtCore); ac_rfl)
          have hpoolEmpty :=
            smallPoolsAt_zero_empty hflLen hcls2 (by unfold rtNumClasses; omega) hpz hmPull
          have hrem : bytes ≤ st.rem := by
            rcases havail with (⟨_, hne⟩ | ⟨hge, _⟩) | hrem
            · exact absurd hpoolEmpty hne
            · omega
            · exact hrem
          exact alloc_bump_check_wp hbyMax hbyMod hrem hm
            (fun p st' m' hp1 hp2 hM hR hm' => hJp (p, ()) m' ⟨st', hp1, hp2, hM, hR, hm'⟩)
        · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : bytes / 8 < 2 ^ 64)]
          obtain ⟨p, hpEq⟩ : ∃ p, p = st.freeList[bytes / 8]'(by rw [hflLen]; exact hsmall) :=
            ⟨_, rfl⟩
          have hpNe : p ≠ 0#64 := hpEq ▸ hpz
          have hmPull : (smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
              (rtCore rt st st.freeList st.hdr ⋆ largeFreeList st.hdr.s_large_free st.largeNodes ⋆
                region st.hdr.s_cur st.rem ⋆ R)) m := sep_cast hm (by (try unfold rtCore); ac_rfl)
          obtain ⟨rest, hpcls, hpAl, hmPop⟩ :=
            smallPoolsAt_pop hflLen hcls2 (by unfold rtNumClasses; omega) (hpEq ▸ hpNe) hmPull
          rw [← hpEq] at hmPop ⊢; dsimp only [rtCore] at hmPop; c0_hsteps_nogrp
          let fl' := st.freeList.set (bytes / 8) (listHeadPtr rest)
          let pools' : Nat → List (BitVec 64) :=
            fun i => if i = bytes / 8 then rest else st.smallPools i
          let hdr' : LcnfC0Rt := { st.hdr with s_st_reused := st.hdr.s_st_reused + 1#64 }
          let st' : RtC0State :=
            { st with
              freeList := fl'
              hdr := hdr'
              smallPools := pools'
              freeListLen := by dsimp [fl']; rw [List.length_set]; exact st.freeListLen }
          refine hJp (p, ()) m ⟨st', hpNe, hpEq ▸ hpAl, by state_frame, Nat.le_refl _, ?_⟩
          dsimp only
          have hidx : (BitVec.ofNat 64 (bytes / 8)).toNat = bytes / 8 :=
            Nat.mod_eq_of_lt (by omega)
          rw [hidx] at hm
          have hHdr : LcnfC0Rt.At rt { st.hdr with s_st_reused := st.hdr.s_st_reused + 1#64 } =
              LcnfC0Rt.At rt hdr' := rfl
          rw [hHdr] at hm
          have hmIn : (((region p 8 ⋆ cell64 (p + 8#64) (listHeadPtr rest)) ⋆
              region (p + 16#64) (8 * (bytes / 8) - 16)) ⋆
              smallFreeList (8 * (bytes / 8)) (listHeadPtr rest) rest ⋆
              smallPoolsExcl (bytes / 8) st.freeList st.smallPools rtNumClasses ⋆
              (rtCore rt st fl' hdr' ⋆ largeFreeList st.hdr.s_large_free st.largeNodes ⋆
                region st.hdr.s_cur st.rem ⋆ R)) m := by
            dsimp [fl']; simp only [sep_emp] at hm
            first | (dsimp only [rtCore] at *; c0_frame) |
              exact sep_cast hm (by (try unfold rtCore); ac_rfl)
          have hre := alloc_small_repack (pools' := pools') (by unfold rtNumClasses; omega)
            hcls2 (by omega)
            (list_getD_set_self st.freeList (listHeadPtr rest) 0#64
              (by rw [hflLen]; exact hsmall))
            (by dsimp [pools']; split <;> first | rfl | contradiction) rfl
            (fun i hi => list_getD_set_ne st.freeList (listHeadPtr rest) 0#64 hi)
            (fun i hi => by dsimp [pools']; split <;> first | contradiction | rfl) hmIn
          unfold rtC0Inv; rw [hbyEq] at hre
          dsimp only [st', fl', hdr']; exact sep_cast hre (by (try unfold rtCore); ac_rfl)
      · have hge512 : 512 ≤ bytes := by omega
        c0_hsteps_nogrp
        refine wp_join_group (fun (xs : Tup Val [i64, i64, i64]) m' =>
            ∃ st' : RtC0State,
              (if xs.fst = 0#64 then
                st' = st ∧ (∀ x ∈ st.largeNodes, x.2 ≠ bytes) ∧
                (rtCore rt st st.freeList st.hdr ⋆
                  smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
                  largeFreeList st.hdr.s_large_free st.largeNodes ⋆
                  region st.hdr.s_cur st.rem ⋆ R) m'
              else
                xs.fst.toNat % 8 = 0 ∧ st'.PreservesMeta st ∧ st'.rem ≤ st.rem ∧
                (rtC0Inv rt st' ⋆ region xs.fst bytes ⋆ R) m'))
          (fun _ xs m' ⟨st', hCase⟩ => by
            refine wp_join_group
              (fun (xp : Tup Val [i64]) mp => ∃ st1 : RtC0State,
                xp.fst ≠ 0#64 ∧ xp.fst.toNat % 8 = 0 ∧ st1.PreservesMeta st ∧ st1.rem ≤ st.rem ∧
                (rtC0Inv rt st1 ⋆ region xp.fst bytes ⋆ R) mp)
              (fun _ xp mp ⟨st1, h⟩ => hJret (st1, xp.fst) mp h) ?_
            intro Jbump hJbump
            by_cases hx0 : xs.fst = 0#64
            · simp only [hx0, ↓reduceIte] at hCase; rcases hCase with ⟨_, hNone, hm'⟩
              have hrem : bytes ≤ st.rem := by
                rcases havail with (⟨hlt, _⟩ | ⟨_, x, hx, heq⟩) | hrem
                · omega
                · exact absurd heq (hNone x hx)
                · exact hrem
              c0_hstep; c0_hstep
              exact alloc_bump_check_wp hbyMax hbyMod hrem hm'
                (fun p st1 m1 hp1 hp2 hM hR hm1 =>
                  hJbump (p, ()) m1 ⟨st1, hp1, hp2, hM, hR, hm1⟩)
            · simp only [hx0, ↓reduceIte] at hCase
              rcases hCase with ⟨hpAl, hM, hR, hm'⟩; c0_hsteps_nogrp
              exact hJbump (xs.fst, ()) m' ⟨st', hx0, hpAl, hM, hR, hm'⟩) ?_
        · intro Jout hJout
          let Rest_lg : Mem 64 → Prop := rtCore rt st st.freeList st.hdr ⋆
            smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
            region st.hdr.s_cur st.rem ⋆ R
          let LInv : Nat → Tup Val [i64, i64] → Mem 64 → Prop := fun n (prev, lcur, ()) ml =>
            ∃ pfx sfx, sfx.length = n ∧ st.largeNodes = pfx ++ sfx ∧ (∀ x ∈ pfx, x.2 ≠ bytes) ∧
              (largeSegSplit st.hdr.s_large_free prev lcur pfx sfx ⋆ Rest_lg) ml
          have hmLoop : (largeFreeList st.hdr.s_large_free st.largeNodes ⋆ Rest_lg) m :=
            sep_cast hm (by dsimp only [Rest_lg]; (try unfold rtCore); ac_rfl)
          refine wp_loop_group LInv ?_ (fun L hL =>
            hL st.largeNodes.length (0#64, st.hdr.s_large_free, ()) m
              ⟨[], st.largeNodes, rfl, rfl, (fun _ h => nomatch h),
                sep_mono (fun _ hx => largeSegSplit_init hx) hmLoop⟩)
          intro L n ⟨prev, lcur, ⟨⟩⟩ ml hL ⟨pfx, sfx, hlen, hnodes, hnePfx, hmem⟩
          by_cases hlc0 : lcur = 0#64
          · subst hlc0; obtain ⟨m1, m2, rfl, hd, hsp, hrest⟩ := hmem
            have hsfx : sfx = [] := largeSegSplit_sfx_nil_of_zero hsp; subst hsfx
            have hnil := largeSegSplit_nil hsp; rw [List.append_nil] at hnodes
            have hallNe : ∀ x ∈ st.largeNodes, x.2 ≠ bytes := by rw [hnodes]; exact hnePfx
            have hraw : (largeFreeList st.hdr.s_large_free pfx ⋆ Rest_lg) (m1.union m2) :=
              ⟨m1, m2, rfl, hd, hnil, hrest⟩
            rw [← hnodes] at hraw
            have hm' : (rtCore rt st st.freeList st.hdr ⋆
                smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
                largeFreeList st.hdr.s_large_free st.largeNodes ⋆
                region st.hdr.s_cur st.rem ⋆ R) (m1.union m2) :=
              sep_cast hraw (by dsimp only [Rest_lg]; (try unfold rtCore); ac_rfl)
            c0_hsteps_nogrp
            exact hJout (0#64, prev, 0#64, ()) _
              ⟨st, by simp only [↓reduceIte]; exact ⟨trivial, hallNe, by simpa using hm'⟩⟩
          · obtain ⟨m1, m2, rfl, hd, hsp, hrest⟩ := hmem
            cases sfx with
            | nil =>
              rcases hsp with ⟨hnext, _⟩; simp [largeSegNext] at hnext; exact absurd hnext hlc0
            | cons x rest =>
              rcases x with ⟨curp, b⟩; rcases hsp with ⟨hnext, hpfxSplit⟩
              dsimp only [largeSegNext] at hnext; subst hnext
              cases hr : pfx.reverse with
              | nil =>
                rw [hr] at hpfxSplit
                rcases hpfxSplit with ⟨hprev0, hhdEq, _, hcurNz, hcurAl, hb512, hbMax,
                  hbMod, hnodeSeg⟩
                rw [hprev0] at *; let nxt := largeSegNext 0#64 rest
                have hnodeMem : (cell64 (lcur + 8#64) nxt ⋆
                    cell64 (lcur + 16#64) (BitVec.ofNat 64 b) ⋆ region lcur 8 ⋆
                    region (lcur + 24#64) (b - 24) ⋆ largeSeg nxt 0#64 rest ⋆ Rest_lg)
                    (m1.union m2) := by
                  have htmp : ((largeFreeNode b lcur nxt ⋆ largeSeg nxt 0#64 rest) ⋆ Rest_lg)
                      (m1.union m2) := ⟨m1, m2, rfl, hd, hnodeSeg, hrest⟩
                  unfold largeFreeNode at htmp; exact sep_cast htmp (by ac_rfl)
                c0_hsteps_nogrp
                · have hbEq : b = bytes := bv64_eq_lt_max hbMax hbyMax ‹_›
                  subst hbEq; dsimp only [Rest_lg] at *; (try dsimp only [rtCore] at *); c0_hsteps
                  let st' : RtC0State :=
                    { st with
                      hdr := { st.hdr with
                        s_large_free := nxt
                        s_st_reused := st.hdr.s_st_reused + 1#64 }
                      largeNodes := rest }
                  refine hJout (lcur, 0#64, lcur, ()) _ ⟨st', ?_⟩
                  simp only [hcurNz, ↓reduceIte]
                  refine ⟨hcurAl, by state_frame, Nat.le_refl _, ?_⟩
                  unfold rtC0Inv
                  refine sep_cast (largeSegSplit_unlink_head (hd := lcur) (_lcur := lcur)
                    (nxt := nxt) (b := bytes) (rest := rest)
                    (Q := rtCore rt st' st'.freeList st'.hdr ⋆
                      smallPoolsAt st'.freeList st'.smallPools rtNumClasses ⋆
                      region st'.hdr.s_cur st'.rem ⋆ R)
                    hb512 (by unfold rtMaxObjBytes at hbMax; omega) ?_)
                    (by (try unfold rtCore); ac_rfl)
                  unfold largeFreeNode; rw [show st'.rem = st.rem from rfl]
                  dsimp only [st']; simp only [sep_emp] at *
                  (try dsimp only [rtCore] at *); c0_frame
                · have hbNe : b ≠ bytes := fun hEq => ‹BitVec.ofNat 64 b ≠ bytesBV› (hEq ▸ rfl)
                  have hmBack : (largeSegSplit lcur lcur nxt ([] ++ [(lcur, b)]) rest ⋆ Rest_lg)
                      (m1.union m2) := by
                    have hnode0 : ((largeFreeNode b lcur nxt ⋆ largeSeg nxt 0#64 rest) ⋆
                        Rest_lg) (m1.union m2) := by
                      unfold largeFreeNode; exact sep_cast hnodeMem (by ac_rfl)
                    exact sep_mono (P' := largeSegSplit lcur lcur nxt ([] ++ [(lcur, b)]) rest)
                      (fun _ hx => largeSegSplit_step hcurNz hcurAl hb512 hbMax hbMod rfl
                        ⟨rfl, rfl, hx⟩) hnode0
                  conv at hmBack => arg 1; arg 1; rw [← hhdEq]
                  refine hL rest.length (lcur, nxt, ()) _
                    (by simp only [List.length_cons] at hlen; omega)
                    ⟨[(lcur, b)], rest, rfl, by rw [hnodes]; simp [List.reverse_eq_nil_iff.mp hr],
                      fun y hy => (List.mem_singleton.mp hy) ▸ hbNe, by simpa using hmBack⟩
              | cons hdRev tlRev =>
                rw [hr] at hpfxSplit; rcases hdRev with ⟨prv, prvB⟩
                rcases hpfxSplit with ⟨hprev, hprvNz, hprvAl, hprvLo, hprvMax, hprvMod, m11,
                  m12, rfl, hd1, hprefMem, _, hcurNz, hcurAl, hb512, hbMax, hbMod, hnodeSeg⟩
                rw [hprev] at *; let nxt := largeSegNext 0#64 rest
                have hnodeMem : (cell64 (lcur + 8#64) nxt ⋆
                    cell64 (lcur + 16#64) (BitVec.ofNat 64 b) ⋆
                    cell64 (prv + 8#64) lcur ⋆ largeSeg st.hdr.s_large_free prv tlRev.reverse ⋆
                    region prv 8 ⋆ cell64 (prv + 16#64) (BitVec.ofNat 64 prvB) ⋆
                    region (prv + 24#64) (prvB - 24) ⋆ region lcur 8 ⋆
                    region (lcur + 24#64) (b - 24) ⋆ largeSeg nxt 0#64 rest ⋆ Rest_lg)
                    ((m11.union m12).union m2) := by
                  have h11 : (largeSeg st.hdr.s_large_free prv tlRev.reverse ⋆
                      region prv 8 ⋆ cell64 (prv + 8#64) lcur ⋆
                      cell64 (prv + 16#64) (BitVec.ofNat 64 prvB) ⋆
                      region (prv + 24#64) (prvB - 24)) m11 :=
                    sep_cast hprefMem (by unfold largeFreeNode; ac_rfl)
                  have h12 : (region lcur 8 ⋆ cell64 (lcur + 8#64) nxt ⋆
                      cell64 (lcur + 16#64) (BitVec.ofNat 64 b) ⋆
                      region (lcur + 24#64) (b - 24) ⋆ largeSeg nxt 0#64 rest) m12 :=
                    sep_cast hnodeSeg (by dsimp only [nxt]; unfold largeFreeNode; ac_rfl)
                  have htmp : (((largeSeg st.hdr.s_large_free prv tlRev.reverse ⋆
                        region prv 8 ⋆ cell64 (prv + 8#64) lcur ⋆
                        cell64 (prv + 16#64) (BitVec.ofNat 64 prvB) ⋆
                        region (prv + 24#64) (prvB - 24)) ⋆
                      (region lcur 8 ⋆ cell64 (lcur + 8#64) nxt ⋆
                        cell64 (lcur + 16#64) (BitVec.ofNat 64 b) ⋆
                        region (lcur + 24#64) (b - 24) ⋆ largeSeg nxt 0#64 rest)) ⋆ Rest_lg)
                      ((m11.union m12).union m2) :=
                    ⟨m11.union m12, m2, rfl, hd, ⟨m11, m12, rfl, hd1, h11, h12⟩, hrest⟩
                  exact sep_cast htmp (by ac_rfl)
                generalize hmemEq : (m11.union m12).union m2 = memCur at hnodeMem ⊢
                c0_hsteps_nogrp
                · have hbEq : b = bytes := bv64_eq_lt_max hbMax hbyMax ‹_›
                  subst hbEq; dsimp only [Rest_lg] at *; (try dsimp only [rtCore] at *); c0_hsteps
                  let st' : RtC0State :=
                    { st with
                      hdr := { st.hdr with s_st_reused := st.hdr.s_st_reused + 1#64 }
                      largeNodes := tlRev.reverse ++ (prv, prvB) :: rest }
                  refine hJout (lcur, prv, lcur, ()) _ ⟨st', ?_⟩
                  simp only [hcurNz, ↓reduceIte]
                  refine ⟨hcurAl, by state_frame, Nat.le_refl _, ?_⟩
                  unfold rtC0Inv
                  refine sep_cast (sep_mono
                    (P := (largeSeg st'.hdr.s_large_free prv tlRev.reverse ⋆
                        largeFreeNode prvB prv nxt) ⋆
                      largeSeg nxt 0#64 rest ⋆ largeFreeNode bytes lcur nxt)
                    (P' := largeFreeList st'.hdr.s_large_free st'.largeNodes ⋆ region lcur bytes)
                    (Q := rtCore rt st' st'.freeList st'.hdr ⋆
                      smallPoolsAt st'.freeList st'.smallPools rtNumClasses ⋆
                      region st'.hdr.s_cur st'.rem ⋆ R)
                    (fun _ hx => sep_mono_r (fun _ hy => largeFreeNode_to_region (by omega)
                      (by unfold rtMaxObjBytes at hbMax; omega) hy) (sep_mono (fun _ hy =>
                        largeSegSplit_unlink_mid (hd := st'.hdr.s_large_free) (prv := prv)
                          (_lcur := lcur) (nxt := nxt) (prvB := prvB) (revMid := tlRev)
                          (rest := rest) hprvNz hprvAl hprvLo hprvMax hprvMod hy) hx)) ?_)
                    (by (try unfold rtCore); ac_rfl)
                  unfold largeFreeNode; rw [show st'.rem = st.rem from rfl]
                  dsimp only [st']; simp only [sep_emp] at *
                  (try dsimp only [rtCore] at *); c0_frame
                · have hbNe : b ≠ bytes := fun hEq => ‹BitVec.ofNat 64 b ≠ bytesBV› (hEq ▸ rfl)
                  have hmBack : (largeSegSplit st.hdr.s_large_free lcur nxt (pfx ++ [(lcur, b)])
                      rest ⋆ Rest_lg) memCur := by
                    have hsplit0 : (((largeSeg st.hdr.s_large_free prv tlRev.reverse ⋆
                        largeFreeNode prvB prv lcur) ⋆
                        (largeFreeNode b lcur nxt ⋆ largeSeg nxt 0#64 rest)) ⋆ Rest_lg)
                        memCur := by
                      rw [← hmemEq]
                      exact ⟨m11.union m12, m2, rfl, hd, ⟨m11, m12, rfl, hd1, hprefMem,
                        hnodeSeg⟩, hrest⟩
                    refine sep_mono (fun _ hx => ?_) hsplit0
                    exact largeSegSplit_step (prev := prv) hcurNz hcurAl hb512 hbMax hbMod rfl
                      (hr ▸ ⟨rfl, hprvNz, hprvAl, hprvLo, hprvMax, hprvMod, hx⟩)
                  refine hL rest.length (lcur, nxt, ()) _
                    (by simp only [List.length_cons] at hlen; omega)
                    ⟨pfx ++ [(lcur, b)], rest, rfl, by rw [hnodes]; simp [List.append_assoc],
                      fun y hy => (List.mem_append.mp hy).elim (hnePfx y)
                        (fun h => (List.mem_singleton.mp h) ▸ hbNe), hmemEq ▸ hmBack⟩

/-! ## 3. `lcnf_free_obj_wp` -/

private def RtC0State.withFreeSmall (st : RtC0State) (cls : Nat) (o : BitVec 64) : RtC0State :=
  { st with
    freeList := st.freeList.set cls o
    smallPools := fun i => if i = cls then o :: st.smallPools i else st.smallPools i
    freeListLen := by rw [List.length_set]; exact st.freeListLen }

private def RtC0State.withFreeLarge (st : RtC0State) (o : BitVec 64) (bytes : Nat) : RtC0State :=
  { st with hdr := { st.hdr with s_large_free := o }, largeNodes := (o, bytes) :: st.largeNodes }

private def freeObjBody (o : BitVec 64) (bytes : Nat) (hdr : BitVec 64) : Mem 64 → Prop :=
  let tag := (hdr >>> 56).toNat
  if tag = arrayTag then fun m =>
    ∃ w16, w16.toNat ≤ 33554428 ∧ bytes = 24 + 8 * w16.toNat ∧
      (region (o + 8#64) 8 ⋆ cell64 (o + 16#64) w16 ⋆ region (o + 24#64) (bytes - 24)) m
  else if tag = sarrayTag then fun m =>
    ∃ w16, w16.toNat ≤ 268435455 ∧
      bytes = align8 (24 + ((hdr >>> 48).toNat % 128) * w16.toNat) ∧
      (region (o + 8#64) 8 ⋆ cell64 (o + 16#64) w16 ⋆ region (o + 24#64) (bytes - 24)) m
  else if tag = stringTag then fun m =>
    ∃ w16, w16.toNat ≤ 268435415 ∧ bytes = align8 (32 + w16.toNat) ∧
      (region (o + 8#64) 8 ⋆ cell64 (o + 16#64) w16 ⋆ region (o + 24#64) (bytes - 24)) m
  else if tag = mpzTag then fun m =>
    ∃ w8, (w8 &&& 4294967295#64).toNat ≤ 33554429 ∧
      bytes = 16 + 8 * (w8 &&& 4294967295#64).toNat ∧
      (cell64 (o + 8#64) w8 ⋆ region (o + 16#64) (bytes - 16)) m
  else fun m =>
    (hdr >>> 32 &&& 65535#64).toNat = bytes ∧ region (o + 8#64) (bytes - 8) m

private theorem freeObjLayout_to_cell_body {o : BitVec 64} {bytes : Nat} {hdr : BitVec 64}
    {m : Mem 64} (hm : freeObjLayout o bytes hdr m) :
    (cell64 o hdr ⋆ freeObjBody o bytes hdr) m := by
  unfold freeObjLayout at hm; unfold freeObjBody
  split at hm <;> rename_i ht
  · rw [ite_eq_left ht]; rcases hm with ⟨w, hw1, hw2, hmem⟩
    exact sep_mono_r (fun _ hb => ⟨w, hw1, hw2, hb⟩) (sep_cast hmem (by ac_rfl))
  · rw [ite_eq_right ht]; split at hm <;> rename_i ht2
    · rw [ite_eq_left ht2]; rcases hm with ⟨w, hw1, hw2, hmem⟩
      exact sep_mono_r (fun _ hb => ⟨w, hw1, hw2, hb⟩) (sep_cast hmem (by ac_rfl))
    · rw [ite_eq_right ht2]; split at hm <;> rename_i ht3
      · rw [ite_eq_left ht3]; rcases hm with ⟨w, hw1, hw2, hmem⟩
        exact sep_mono_r (fun _ hb => ⟨w, hw1, hw2, hb⟩) (sep_cast hmem (by ac_rfl))
      · rw [ite_eq_right ht3]; split at hm <;> rename_i ht4
        · rw [ite_eq_left ht4]; rcases hm with ⟨w, hw1, hw2, hmem⟩
          exact sep_mono_r (fun _ hb => ⟨w, hw1, hw2, hb⟩) (sep_cast hmem (by ac_rfl))
        · rw [ite_eq_right ht4]; exact sep_mono_r (fun _ hb => ⟨hm.1, hb⟩) hm.2

private theorem free_obj_tri_split_small {o w16 : BitVec 64} {bytes : Nat} {m : Mem 64}
    (hmax : bytes < rtMaxObjBytes)
    (hm : (region (o + 8#64) 8 ⋆ cell64 (o + 16#64) w16 ⋆ region (o + 24#64) (bytes - 24)) m)
    (h24 : 24 ≤ bytes) :
    ∃ v8 : BitVec 64, (cell64 (o + 8#64) v8 ⋆ region (o + 16#64) (bytes - 16)) m := by
  unfold rtMaxObjBytes at hmax
  have h0 : (cell64 (o + 16#64) w16 ⋆
      (region (o + 8#64) 8 ⋆ region (o + 24#64) (bytes - 24))) m := sep_cast hm (by ac_rfl)
  have h1 : (region (o + 8#64) 8 ⋆ region (o + 16#64) (bytes - 16)) m := by
    rw [← region_merge8 (a := o + 16#64) (n := bytes - 16) (by omega) (by omega), ptr_add_nat_p,
      show bytes - 16 - 8 = bytes - 24 by omega]
    exact sep_cast (sep_mono (P' := region (o + 16#64) 8) (fun _ hc => cell64_to_region hc) h0) (by
      rw [show (o + BitVec.ofNat 64 (8 + 16) : BitVec 64) = o + 24#64 from rfl]; ac_rfl)
  obtain ⟨m1, m2, rfl, hd, hr8, hr16⟩ := h1; obtain ⟨v8, hv8⟩ := region_to_cell64 hr8
  exact ⟨v8, m1, m2, rfl, hd, hv8, hr16⟩

private theorem free_obj_tri_split_large {o w16 : BitVec 64} {bytes : Nat} {m : Mem 64}
    (hm : (region (o + 8#64) 8 ⋆ cell64 (o + 16#64) w16 ⋆ region (o + 24#64) (bytes - 24)) m) :
    ∃ v8 v16 : BitVec 64,
    ((cell64 (o + 8#64) v8 ⋆ cell64 (o + 16#64) v16) ⋆ region (o + 24#64) (bytes - 24)) m := by
  have h0 : (region (o + 8#64) 8 ⋆
      (cell64 (o + 16#64) w16 ⋆ region (o + 24#64) (bytes - 24))) m := sep_cast hm (by ac_rfl)
  obtain ⟨m1, m2, rfl, hd, hr8, h23⟩ := h0; obtain ⟨v8, hc8⟩ := region_to_cell64 hr8
  have h1 : (cell64 (o + 8#64) v8 ⋆
      (cell64 (o + 16#64) w16 ⋆ region (o + 24#64) (bytes - 24))) (m1.union m2) :=
    ⟨m1, m2, rfl, hd, hc8, h23⟩
  exact ⟨v8, w16, sep_cast h1 (by ac_rfl)⟩

private theorem freeObjBody_split_small {o hdr : BitVec 64} {bytes : Nat} {m : Mem 64}
    (hmin : rtMinObjBytes ≤ bytes) (hmax : bytes < rtMaxObjBytes)
    (hm : freeObjBody o bytes hdr m) :
    ∃ v8 : BitVec 64, (cell64 (o + 8#64) v8 ⋆ region (o + 16#64) (bytes - 16)) m := by
  unfold freeObjBody at hm; unfold rtMinObjBytes at hmin; unfold rtMaxObjBytes at hmax
  split at hm
  · rcases hm with ⟨_, _, _, hm⟩; exact free_obj_tri_split_small hmax hm (by omega)
  · split at hm
    · rcases hm with ⟨_, _, hby, hm⟩
      exact free_obj_tri_split_small hmax hm (by unfold align8 at hby; omega)
    · split at hm
      · rcases hm with ⟨_, _, hby, hm⟩
        exact free_obj_tri_split_small hmax hm (by unfold align8 at hby; omega)
      · split at hm
        · rcases hm with ⟨w8, _, _, hm⟩; exact ⟨w8, hm⟩
        · rcases hm with ⟨_, hm⟩; rw [← sep_emp (region (o + 8#64) (bytes - 8))] at hm
          obtain ⟨v8, hv8⟩ := region_pop8_cell64 (bytes - 8) (by omega) (by omega) hm
          rw [ptr_add_nat_p, sep_assoc, sep_emp] at hv8; exact ⟨v8, hv8⟩

private theorem freeObjBody_split_large {o hdr : BitVec 64} {bytes : Nat} {m : Mem 64}
    (h24 : 24 ≤ bytes) (hmax : bytes < rtMaxObjBytes) (hm : freeObjBody o bytes hdr m) :
    ∃ v8 v16 : BitVec 64,
    ((cell64 (o + 8#64) v8 ⋆ cell64 (o + 16#64) v16) ⋆ region (o + 24#64) (bytes - 24)) m := by
  unfold freeObjBody at hm; unfold rtMaxObjBytes at hmax
  split at hm
  · rcases hm with ⟨_, _, _, hm⟩; exact free_obj_tri_split_large hm
  · split at hm
    · rcases hm with ⟨_, _, _, hm⟩; exact free_obj_tri_split_large hm
    · split at hm
      · rcases hm with ⟨_, _, _, hm⟩; exact free_obj_tri_split_large hm
      · split at hm
        · rcases hm with ⟨w8, _, _, hm⟩
          obtain ⟨v16, h1⟩ := region_pop8_cell64 (bytes - 16) (by omega) (by omega)
            (sep_cast hm (by ac_rfl) : (region (o + 16#64) (bytes - 16) ⋆ cell64 (o + 8#64) w8) m)
          rw [ptr_add_nat_p] at h1; exact ⟨w8, v16, sep_cast h1 (by ac_rfl)⟩
        · rcases hm with ⟨_, hm⟩; rw [← sep_emp (region (o + 8#64) (bytes - 8))] at hm
          obtain ⟨v8, h1⟩ := region_pop8_cell64 (bytes - 8) (by omega) (by omega) hm
          rw [ptr_add_nat_p, show (8 + 8 : Nat) = 16 from rfl,
            show bytes - 8 - 8 = bytes - 16 by omega] at h1
          have h1' : (region (o + 16#64) (bytes - 16) ⋆ (cell64 (o + 8#64) v8 ⋆ emp)) m :=
            sep_cast h1 (by ac_rfl)
          obtain ⟨v16, h2⟩ := region_pop8_cell64 (bytes - 16) (by omega) (by omega) h1'
          rw [ptr_add_nat_p, show (16 + 8 : Nat) = 24 from rfl,
            show bytes - 16 - 8 = bytes - 24 by omega, sep_emp (cell64 (o + 8#64) v8)] at h2
          exact ⟨v8, v16, sep_cast h2 (by ac_rfl)⟩

private theorem tag_bv_eq {hdr : BitVec 64} {n : Nat}
    (ht : (hdr >>> 56).toNat = n) (hn : n < 2 ^ 64) : hdr >>> 56 = BitVec.ofNat 64 n :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; exact ht)

private theorem tag_ne_of_bv_eq {hdr : BitVec 64} {n : Nat}
    (hne : (hdr >>> 56).toNat ≠ n) (hn : n < 2 ^ 64)
    (heq : hdr >>> 56 = BitVec.ofNat 64 n) : False :=
  hne (by rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn])

private theorem free_sarray_szEq {hdr w16 : BitVec 64} {bytes : Nat}
    (hw : w16.toNat ≤ 268435455)
    (hby : bytes = align8 (24 + ((hdr >>> 48).toNat % 128) * w16.toNat)) :
    (24#64 + (hdr >>> BitVec.signExtend 64 48#32 &&& 127#64) * w16 + 7#64 &&&
      18446744073709551608#64) = BitVec.ofNat 64 bytes := by
  have hmask : (hdr >>> BitVec.signExtend 64 48#32 &&& 127#64) =
      BitVec.ofNat 64 ((hdr >>> 48).toNat % 128) := by
    apply BitVec.eq_of_toNat_eq
    rw [show BitVec.signExtend 64 48#32 = 48#64 from by decide, BitVec.toNat_and,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 127 < 2 ^ 64),
      show (127 : Nat) = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp [BitVec.toNat_ushiftRight]
  have hle : ((hdr >>> 48).toNat % 128) * w16.toNat ≤ 127 * 268435455 :=
    Nat.mul_le_mul (by omega) hw
  rw [hmask, show 24#64 + BitVec.ofNat 64 ((hdr >>> 48).toNat % 128) * w16 =
    BitVec.ofNat 64 (24 + (hdr >>> 48).toNat % 128 * w16.toNat) by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]]
  simpa [hby] using bv64_align8_eq (n := 24 + (hdr >>> 48).toNat % 128 * w16.toNat) (by omega)

private theorem free_mpz_szEq {w8 : BitVec 64} {bytes : Nat} (hlt : bytes < 2 ^ 64)
    (hby : bytes = 16 + 8 * (w8 &&& 4294967295#64).toNat) :
    16#64 + 8#64 * (w8 &&& 4294967295#64) = BitVec.ofNat 64 bytes := by
  apply BitVec.eq_of_toNat_eq
  have hmask : (w8 &&& 4294967295#64).toNat = w8.toNat &&& 4294967295 := rfl
  have h8m : (8 : Nat) % 2 ^ 64 = 8 := rfl; have h16m : (16 : Nat) % 2 ^ 64 = 16 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8m, h16m, hmask,
    Nat.mod_eq_of_lt hlt]; omega

theorem lcnf_free_obj_wp (Γ : Env) :
    ∀ (xs : Tup Val lcnf_free_obj.as) (m : Mem 64) (Q : Post lcnf_free_obj.rs) (X : XPost),
    lcnfFreeObjSpec xs m Q X → Func.wp Γ lcnf_free_obj.body xs m Q X := by
  dsimp [lcnf_free_obj]; rintro ⟨rt, o, ⟨⟩⟩ m Q X hspec
  dsimp [Func.wp, lcnf_free_obj_body]; dsimp [lcnfFreeObjSpec] at hspec
  split at hspec
  · rcases hspec with ⟨st, R, hm, hQ⟩; c0_hsteps; exact hQ
  · rcases hspec with ⟨st, hdr, bytes, R, hoNz, hoAl, hmin, hmax, hmod, hm, hQ⟩
    have hm0 : (cell64 o hdr ⋆ (rtC0Inv rt st ⋆ freeObjBody o bytes hdr ⋆ R)) m :=
      sep_cast (sep_mono (fun _ => sep_mono_r
        (fun _ hf => freeObjLayout_to_cell_body hf)) hm) (by ac_rfl)
    c0_hsteps_nogrp
    · refine wp_join_state1 (fun _ : Unit => BitVec.ofNat 64 bytes)
        (fun () m' => (rtC0Inv rt st ⋆ freeObjLayout o bytes hdr ⋆ R) m') ?_ ?_
      · intro _ () m1 hm1
        refine wp_join_group (fun _ _ => False) (fun _ _ _ hf => False.elim hf) ?_
        intro _J0 _hJ0
        have hm0' : (cell64 o hdr ⋆ (rtC0Inv rt st ⋆ freeObjBody o bytes hdr ⋆ R)) m1 :=
          sep_cast (sep_mono (fun _ => sep_mono_r
            (fun _ hf => freeObjLayout_to_cell_body hf)) hm1) (by ac_rfl)
        c0_hsteps_nogrp
        · exfalso; unfold rtMaxObjBytes at hmax
          exact hc (bv_and7_eq_zero_of_mod8 (by simp [hmod]))
        · exfalso; unfold rtMinObjBytes rtMaxObjBytes at *
          simp only [Nat.mod_eq_of_lt (by omega : bytes < 2 ^ 64)] at hc; omega
        · exfalso; unfold rtMaxObjBytes at *
          simp only [Nat.mod_eq_of_lt (by omega : bytes < 2 ^ 64)] at hc; omega
        refine wp_join_state0
          (fun (stTmp : RtC0State) (m2 : Mem 64) =>
            stTmp.PreservesMeta st ∧ stTmp.rem = st.rem ∧ stTmp.workBuf = st.workBuf ∧
            (rtC0Inv rt stTmp ⋆ R) m2) ?_ ?_
        · intro _ stTmp m2 ⟨hMeta, hRem, hWb, hmem⟩; unfold rtC0Inv at hmem; c0_hsteps
          refine hQ { stTmp with hdr := { stTmp.hdr with
              s_st_frees := stTmp.hdr.s_st_frees + 1#64
              s_st_live := stTmp.hdr.s_st_live - 1#64 } } _
            (by state_frame; all_goals exact ‹_›) hRem hWb ?_
          unfold rtC0Inv; exact sep_cast ‹_› (by ac_rfl)
        ·
            intro Jepi hJepi
            have hBody : (freeObjBody o bytes hdr ⋆ (cell64 o 0#64 ⋆ rtC0Inv rt st ⋆ R)) _ :=
              sep_cast ‹_› (by ac_rfl)
            obtain ⟨mB, mRest, rfl, hdB, hB, hRest⟩ := hBody
            have hb : bytes < 2 ^ 64 := by unfold rtMaxObjBytes at hmax; omega
            by_cases hsmall : bytes / 8 < 64
            · obtain ⟨v8, hsp8⟩ := freeObjBody_split_small hmin hmax hB
              have hmSm0 : ((cell64 (o + 8#64) v8 ⋆ region (o + 16#64) (bytes - 16)) ⋆
                  (cell64 o 0#64 ⋆ rtC0Inv rt st ⋆ R)) (mB.union mRest) :=
                ⟨mB, mRest, rfl, hdB, hsp8, hRest⟩
              have hmSm : (cell64 (o + 8#64) v8 ⋆ region (o + 16#64) (bytes - 16) ⋆
                  cell64 o 0#64 ⋆ rtC0Inv rt st ⋆ R) (mB.union mRest) :=
                sep_cast hmSm0 (by ac_rfl)
              unfold rtC0Inv at hmSm
              have hclsLt : (BitVec.ofNat 64 bytes >>> 3).ult 64#64 = true := by
                simp [BitVec.ult, Nat.shiftRight_eq_div_pow]; exact hsmall
              have hcls2 : 2 ≤ bytes / 8 := by unfold rtMinObjBytes at hmin; omega
              have hflLen : st.freeList.length = rtNumClasses := st.freeListLen
              have hclsLtN : bytes / 8 < rtNumClasses := by unfold rtNumClasses; omega
              have hlen : bytes / 8 < st.freeList.length := by rw [hflLen]; exact hclsLtN
              have hidxNat : (BitVec.ofNat 64 bytes >>> 3).toNat = bytes / 8 :=
                bv64_shr3_toNat bytes hb
              have hclsBv : BitVec.ofNat 64 bytes >>> (OfNat.ofNat 3 : BitVec 64) =
                  BitVec.ofNat 64 (bytes / 8) := by
                apply BitVec.eq_of_toNat_eq
                simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
              have hclsBvNat : BitVec.ofNat 64 bytes >>> (3 : Nat) =
                  BitVec.ofNat 64 (bytes / 8) := by
                apply BitVec.eq_of_toNat_eq
                simp [Nat.shiftRight_eq_div_pow]
              have hflLt : (BitVec.ofNat 64 (bytes / 8)).toNat < st.freeList.length := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hlen
              have hgetOld : st.freeList.getD (bytes / 8) 0#64 = st.freeList[bytes / 8]'hlen := by
                simp [List.getD_eq_getElem?_getD, hlen]
              (try dsimp only [rtCore] at *); c0_hsteps
              · try rw [hclsBv]
                try rw [hclsBvNat]
                (try dsimp only [rtCore] at *); c0_hsteps
                refine hJepi (st.withFreeSmall (bytes / 8) o) m ⟨by state_frame, rfl, rfl, ?_⟩
                have hmIn : (((region o 8 ⋆ cell64 (o + 8#64) (st.freeList[bytes / 8]'hlen)) ⋆
                    region (o + 16#64) (8 * (bytes / 8) - 16)) ⋆
                    (smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
                      (rtCore rt st (st.freeList.set (bytes / 8) o) st.hdr ⋆
                        largeFreeList st.hdr.s_large_free st.largeNodes ⋆
                        region st.hdr.s_cur st.rem ⋆ R))) m := by
                  rw [align8_div8_mul8 hmod]
                  simp only [sep_emp, show (BitVec.ofNat 64 (bytes / 8)).toNat = bytes / 8 from
                    Nat.mod_eq_of_lt (by omega)] at hm
                  exact sep_cast (sep_mono (P := cell64 o 0#64) (P' := region o 8)
                    (fun _ hc => cell64_to_region hc)
                    (show (cell64 o 0#64 ⋆
                        (cell64 (o + 8#64) (st.freeList[bytes / 8]'hlen) ⋆
                          region (o + 16#64) (bytes - 16) ⋆
                          smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
                          rtCore rt st (st.freeList.set (bytes / 8) o) st.hdr ⋆
                          largeFreeList st.hdr.s_large_free st.largeNodes ⋆
                          region st.hdr.s_cur st.rem ⋆ R)) m from
                      sep_cast hm (by (try unfold rtCore); ac_rfl)))
                          (by (try unfold rtCore); ac_rfl)
                have hre := smallPoolsAt_push_head (pools' :=
                    (st.withFreeSmall (bytes / 8) o).smallPools)
                  hflLen hclsLtN hcls2 hoNz hoAl hgetOld
                  (list_getD_set_self st.freeList o 0#64 hlen)
                  (by simp [RtC0State.withFreeSmall])
                  (fun i hi => list_getD_set_ne st.freeList o 0#64 hi)
                  (fun i hi => by simp [RtC0State.withFreeSmall, hi]) hmIn
                unfold rtC0Inv RtC0State.withFreeSmall;
                    exact sep_cast hre (by (try unfold rtCore); ac_rfl)
              · exfalso
                rw [Nat.mod_eq_of_lt hb, show (64 : Nat) % 2 ^ 64 = 64 from rfl,
                  show (2 : Nat) ^ (OfNat.ofNat 3 : Nat) = 8 from rfl] at hc; omega
            · have h512 : 512 ≤ bytes := by omega
              obtain ⟨v8, v16, hspLg⟩ := freeObjBody_split_large (by omega) hmax hB
              have hmLg : (cell64 (o + 8#64) v8 ⋆ cell64 (o + 16#64) v16 ⋆
                  region (o + 24#64) (bytes - 24) ⋆ cell64 o 0#64 ⋆
                  largeFreeList st.hdr.s_large_free st.largeNodes ⋆
                  rtCore rt st st.freeList st.hdr ⋆
                      smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
                  region st.hdr.s_cur st.rem ⋆ R) (mB.union mRest) := by
                have h0 : ((cell64 (o + 8#64) v8 ⋆ cell64 (o + 16#64) v16 ⋆
                    region (o + 24#64) (bytes - 24)) ⋆
                    (cell64 o 0#64 ⋆ rtC0Inv rt st ⋆
                        R)) (mB.union mRest) := ⟨mB, mRest, rfl, hdB, hspLg, hRest⟩
                unfold rtC0Inv at h0; exact sep_cast h0 (by (try unfold rtCore); ac_rfl)
              have hOldHd : st.hdr.s_large_free = largeSegNext 0#64 st.largeNodes := by
                obtain ⟨_, _, _, _, hLF, _⟩ := (sep_cast hmLg (by (try unfold rtCore); ac_rfl) :
                  (largeFreeList st.hdr.s_large_free st.largeNodes ⋆
                    (cell64 (o + 8#64) v8 ⋆ cell64 (o + 16#64) v16 ⋆
                      region (o + 24#64) (bytes - 24) ⋆ cell64 o 0#64 ⋆
                      rtCore rt st st.freeList st.hdr ⋆
                      smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
                      region st.hdr.s_cur st.rem ⋆ R)) (mB.union mRest))
                exact largeSeg_hd_eq_next hLF
              have hnotSmall : (BitVec.ofNat 64 bytes >>> 3).ult 64#64 = false := by
                simp [BitVec.ult, Nat.shiftRight_eq_div_pow]; omega
              (try dsimp only [rtCore] at *); c0_hsteps
              · exfalso
                rw [Nat.mod_eq_of_lt hb, show (64 : Nat) % 2 ^ 64 = 64 from rfl,
                  show (2 : Nat) ^ (OfNat.ofNat 3 : Nat) = 8 from rfl] at hc; omega
              · refine hJepi (st.withFreeLarge o bytes) _ ⟨by state_frame, rfl, rfl, ?_⟩
                unfold rtC0Inv RtC0State.withFreeLarge; simp only [sep_emp] at *
                let R_lg : Mem 64 → Prop :=
                  rtCore rt st st.freeList { st.hdr with s_large_free := o } ⋆
                  smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
                      region st.hdr.s_cur st.rem ⋆ R
                refine sep_cast (sep_mono
                  (P := largeFreeNode bytes o st.hdr.s_large_free ⋆
                    largeFreeList st.hdr.s_large_free st.largeNodes)
                  (P' := largeFreeList o ((o, bytes) :: st.largeNodes)) (Q := R_lg)
                  (fun _ hx => by
                    unfold largeFreeList; rw [largeSeg.eq_2]
                    exact ⟨rfl, hoNz, hoAl, h512, hmax, hmod, hOldHd ▸ hx⟩) ?_)
                  (by dsimp only [R_lg]; (try unfold rtCore); ac_rfl)
                unfold largeFreeNode
                refine sep_cast (sep_mono (P := cell64 o 0#64) (P' := region o 8)
                  (Q := cell64 (o + 8#64) st.hdr.s_large_free ⋆
                    cell64 (o + 16#64) (BitVec.ofNat 64 bytes) ⋆ region (o + 24#64) (bytes - 24) ⋆
                    largeFreeList st.hdr.s_large_free st.largeNodes ⋆ R_lg)
                  (fun _ hc => cell64_to_region hc) ?_)
                  (by dsimp only [R_lg]; (try unfold rtCore); ac_rfl)
                dsimp only [R_lg]; exact sep_cast hm (by (try unfold rtCore); ac_rfl)
      · intro Jsw hJsw
        by_cases ht246 : (hdr >>> 56).toNat = arrayTag
        · have hmKeep := hm; unfold freeObjLayout at hm; rw [ite_eq_left ht246] at hm
          obtain ⟨w16, _, hby, h1⟩ := sep_mid_exists_pure hm
          have hm1 : (cell64 (o + 16#64) w16 ⋆ (rtC0Inv rt st ⋆ cell64 o hdr ⋆
              region (o + 8#64) 8 ⋆ region (o + 24#64) (bytes - 24) ⋆ R)) m :=
            sep_cast h1 (by ac_rfl)
          c0_hsteps_nogrp
          · have hby24 : 24#64 + 8#64 * w16 = BitVec.ofNat 64 bytes := by
              apply BitVec.eq_of_toNat_eq
              simp [BitVec.toNat_add, BitVec.toNat_mul, hby]
            rw [hby24]; exact hJsw () _ hmKeep
          · exfalso; exact absurd (tag_bv_eq ht246 (by decide)) hc
        · c0_hsteps_nogrp
          · exfalso; exact tag_ne_of_bv_eq ht246 (by decide) hc
          · refine wp_join_state1 (fun _ : Unit => BitVec.ofNat 64 bytes)
              (fun () m' => (rtC0Inv rt st ⋆ freeObjLayout o bytes hdr ⋆ R) m')
              (fun _ () m' h => hJsw () m' h) ?_
            intro Jsw hJsw
            by_cases ht248 : (hdr >>> 56).toNat = sarrayTag
            · have hmKeep := hm; unfold freeObjLayout at hm
              rw [ite_eq_right ht246, ite_eq_left ht248] at hm
              obtain ⟨w16, hw1, hby, h1⟩ := sep_mid_exists_pure hm
              have hm1 : (cell64 (o + 16#64) w16 ⋆ (rtC0Inv rt st ⋆ cell64 o hdr ⋆
                  region (o + 8#64) 8 ⋆ region (o + 24#64) (bytes - 24) ⋆ R)) m :=
                sep_cast h1 (by ac_rfl)
              c0_hsteps_nogrp
              · rw [show (hdr >>> OfNat.ofNat 48 : BitVec 64) = hdr >>> BitVec.signExtend 64 48#32
                  from rfl, free_sarray_szEq hw1 hby]
                exact hJsw () _ hmKeep
              · exfalso; exact absurd (tag_bv_eq ht248 (by decide)) hc
            · c0_hsteps_nogrp
              · exfalso; exact tag_ne_of_bv_eq ht248 (by decide) hc
              · refine wp_join_state1 (fun _ : Unit => BitVec.ofNat 64 bytes)
                  (fun () m' => (rtC0Inv rt st ⋆ freeObjLayout o bytes hdr ⋆ R) m')
                  (fun _ () m' h => hJsw () m' h) ?_
                intro Jsw hJsw
                by_cases ht249 : (hdr >>> 56).toNat = stringTag
                · have hmKeep := hm; unfold freeObjLayout at hm
                  rw [ite_eq_right ht246, ite_eq_right ht248, ite_eq_left ht249] at hm
                  obtain ⟨w16, _, hby, h1⟩ := sep_mid_exists_pure hm
                  have hm1 : (cell64 (o + 16#64) w16 ⋆ (rtC0Inv rt st ⋆ cell64 o hdr ⋆
                      region (o + 8#64) 8 ⋆ region (o + 24#64) (bytes - 24) ⋆ R)) m :=
                    sep_cast h1 (by ac_rfl)
                  c0_hsteps_nogrp
                  · rw [show 32#64 + w16 = BitVec.ofNat 64 (32 + w16.toNat) by
                      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add],
                      bv64_align8_eq (by omega), ← hby]
                    exact hJsw () _ hmKeep
                  · exfalso; exact absurd (tag_bv_eq ht249 (by decide)) hc
                · c0_hsteps_nogrp
                  · exfalso; exact tag_ne_of_bv_eq ht249 (by decide) hc
                  · refine wp_join_state1 (fun _ : Unit => BitVec.ofNat 64 bytes)
                      (fun () m' => (rtC0Inv rt st ⋆ freeObjLayout o bytes hdr ⋆ R) m')
                      (fun _ () m' h => hJsw () m' h) ?_
                    intro Jsw hJsw
                    by_cases ht250 : (hdr >>> 56).toNat = mpzTag
                    · have hmKeep := hm; unfold freeObjLayout at hm
                      rw [ite_eq_right ht246, ite_eq_right ht248, ite_eq_right ht249,
                        ite_eq_left ht250] at hm
                      obtain ⟨w8, _, hby, h1⟩ := sep_mid_exists_pure hm
                      have hm1 : (cell64 (o + 8#64) w8 ⋆ (rtC0Inv rt st ⋆ cell64 o hdr ⋆
                          region (o + 16#64) (bytes - 16) ⋆ R)) m := sep_cast h1 (by ac_rfl)
                      c0_hsteps_nogrp
                      · rw [free_mpz_szEq (by unfold rtMaxObjBytes at hmax; omega) hby]
                        exact hJsw () _ hmKeep
                      · exfalso; exact absurd (tag_bv_eq ht250 (by decide)) hc
                    · have hmKeep := hm; unfold freeObjLayout at hm
                      rw [ite_eq_right ht246, ite_eq_right ht248, ite_eq_right ht249,
                        ite_eq_right ht250] at hm
                      rcases hm with ⟨_, _, _, _, ⟨_, _, _, _, _, hby, _⟩, _⟩; c0_hsteps_nogrp
                      · exfalso; exact tag_ne_of_bv_eq ht250 (by decide) hc
                      · rw [show (hdr >>> 32 &&& 65535#64) = BitVec.ofNat 64 bytes by
                          apply BitVec.eq_of_toNat_eq; unfold rtMaxObjBytes at hmax
                          rw [hby, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]]
                        exact hJsw () _ hmKeep

/-! ## 4. `lcnf_clo_under_wp` & M0a `ModuleOk` -/

private theorem zip_mem_elim {α β : Type _} {xs : List α} {ys : List β}
    (hlen : ys.length = xs.length) {p : α × β} (hp : p ∈ xs.zip ys) :
    ∃ k : Nat, ∃ hk : k < xs.length, ∃ _ : k < ys.length, p = (xs[k], ys[k]) := by
  rw [List.mem_iff_getElem] at hp; obtain ⟨k, hk, rfl⟩ := hp
  have hk1 : k < xs.length := by rw [List.length_zip, hlen, Nat.min_self] at hk; exact hk
  exact ⟨k, hk1, by omega, by simp [List.getElem_zip]⟩

private theorem zip_mem_pair {α β : Type _} {xs : List α} {ys : List β}
    (hlen : ys.length = xs.length) {k : Nat} (hk : k < xs.length) (hk2 : k < ys.length) :
    (xs[k], ys[k]) ∈ xs.zip ys := by
  rw [List.mem_iff_getElem]
  exact ⟨k, by rw [List.length_zip, hlen, Nat.min_self]; exact hk, by simp [List.getElem_zip]⟩

private theorem cloUnderIncRel_init {objs : List LcnfObj}
    (hWf : ∀ obj ∈ objs, obj.Wf) (hCl : lcnfHeapClosed objs) : CloUnderIncRel [] objs objs := by
  refine ⟨rfl, hCl, ?_⟩
  intro p hp; obtain ⟨k, hk, _, hpeq⟩ := zip_mem_elim rfl hp
  rw [hpeq]; dsimp only; have hw := hWf objs[k] (List.getElem_mem hk)
  refine ⟨hw, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  by_cases h0 : objs[k].rc = 0#32
  · exact Or.inl ⟨h0, h0⟩
  · exact Or.inr ⟨objWf_rc_pos hw h0, by simp⟩

private theorem cloUnderIncRel_step_skip {pref : List (BitVec 64)} {p : BitVec 64}
    {objs curObjs : List LcnfObj} (hrel : CloUnderIncRel pref objs curObjs)
    (hp : p &&& 1#64 ≠ 0#64) : CloUnderIncRel (pref ++ [p]) objs curObjs := by
  rcases hrel with ⟨hlen, hCl, hforall⟩
  refine ⟨hlen, hCl, ?_⟩
  intro pr hpr; obtain ⟨k, hk, hk_cur, hpeq⟩ := zip_mem_elim hlen hpr; rw [hpeq]; dsimp only
  obtain ⟨hw, ha, hrest⟩ := hforall (objs[k], curObjs[k]) (zip_mem_pair hlen hk hk_cur)
  have hne : objs[k].addr ≠ p := fun heq => by
    have h0 := objWf_addr_even hw; rw [ha, heq] at h0; exact hp h0
  have hcnt : [p].count objs[k].addr = 0 := by simp [Ne.symm hne]
  exact ⟨hw, ha, by simpa [List.count_append, hcnt] using hrest⟩

private theorem cloUnderIncRel_row_keep {pref : List (BitVec 64)} {p : BitVec 64}
    {o1 o2 : LcnfObj} (hne : o1.addr ≠ p)
    (hrow : o2.Wf ∧ o2.addr = o1.addr ∧ o2.csSz = o1.csSz ∧ o2.other = o1.other ∧
      o2.tag = o1.tag ∧ o2.funId = o1.funId ∧ o2.arity = o1.arity ∧ o2.cap = o1.cap ∧
      o2.arrSize = o1.arrSize ∧ o2.strLen = o1.strLen ∧ o2.fields = o1.fields ∧
      o2.scalarData = o1.scalarData ∧ o2.limbs = o1.limbs ∧ ((o1.rc = 0#32 ∧ o2.rc = 0#32) ∨
      (0 < o1.rc.toInt ∧ o2.rc.toInt = o1.rc.toInt + (pref.count o1.addr : Int)))) :
    o2.Wf ∧ o2.addr = o1.addr ∧ o2.csSz = o1.csSz ∧ o2.other = o1.other ∧
      o2.tag = o1.tag ∧ o2.funId = o1.funId ∧ o2.arity = o1.arity ∧ o2.cap = o1.cap ∧
      o2.arrSize = o1.arrSize ∧ o2.strLen = o1.strLen ∧ o2.fields = o1.fields ∧
      o2.scalarData = o1.scalarData ∧ o2.limbs = o1.limbs ∧ ((o1.rc = 0#32 ∧ o2.rc = 0#32) ∨
      (0 < o1.rc.toInt ∧ o2.rc.toInt = o1.rc.toInt + ((pref ++ [p]).count o1.addr : Int))) := by
  obtain ⟨hw, ha, hrest⟩ := hrow; have hcnt : [p].count o1.addr = 0 := by simp [Ne.symm hne]
  exact ⟨hw, ha, by simpa [List.count_append, hcnt] using hrest⟩

private theorem cloUnderIncRel_step_zero {pref : List (BitVec 64)} {p : BitVec 64}
    {objs curObjs : List LcnfObj} {idx : Nat}
    (hrel : CloUnderIncRel pref objs curObjs) (hidx : idx < curObjs.length)
    (haddr : curObjs[idx].addr = p) (hrc0 : curObjs[idx].rc = 0#32)
    (huniq : ∀ j (hj : j < curObjs.length), j ≠ idx → curObjs[j].addr ≠ p) :
    CloUnderIncRel (pref ++ [p]) objs curObjs := by
  rcases hrel with ⟨hlen, hCl, hforall⟩; refine ⟨hlen, hCl, fun pr hpr => ?_⟩
  obtain ⟨k, hk, hk_cur, hpeq⟩ := zip_mem_elim hlen hpr; rw [hpeq]; dsimp only
  have hrow := hforall (objs[k], curObjs[k]) (zip_mem_pair hlen hk hk_cur); dsimp only at hrow
  by_cases hki : k = idx
  · subst hki; rcases hrow with ⟨hw, ha, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, hrc⟩
    refine ⟨hw, ha, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, ?_⟩
    rcases hrc with ⟨hz1, _⟩ | ⟨_, heq⟩
    · exact Or.inl ⟨hz1, hrc0⟩
    · exfalso; have hzNat : curObjs[k].rc.toInt = 0 := by rw [hrc0]; decide
      rw [hzNat] at heq; omega
  · exact cloUnderIncRel_row_keep (by rw [← hrow.2.1]; exact huniq k hk_cur hki) hrow

private theorem cloUnderIncRel_step_pos {pref : List (BitVec 64)} {p : BitVec 64}
    {objs curObjs : List LcnfObj} {idx : Nat}
    (hrel : CloUnderIncRel pref objs curObjs) (hidx : idx < curObjs.length)
    (haddr : curObjs[idx].addr = p) (hrcNz : curObjs[idx].rc ≠ 0#32)
    (hbound : curObjs[idx].rc.toInt < 2147483647)
    (huniq : ∀ j (hj : j < curObjs.length), j ≠ idx → curObjs[j].addr ≠ p) :
    CloUnderIncRel (pref ++ [p]) objs
      (curObjs.set idx (curObjs[idx].withRc (curObjs[idx].rc + 1#32))) := by
  rcases hrel with ⟨hlen, hCl, hforall⟩
  have hlen' : (curObjs.set idx (curObjs[idx].withRc (curObjs[idx].rc + 1#32))).length =
      objs.length := by simp [hlen]
  refine ⟨hlen', lcnfHeapClosed_set_withRc hCl hidx _, fun pr hpr => ?_⟩
  obtain ⟨k, hk, hk_cur', hpeq⟩ := zip_mem_elim hlen' hpr
  rw [hpeq]; dsimp only; have hk_cur : k < curObjs.length := by omega
  have hrow := hforall (objs[k], curObjs[k]) (zip_mem_pair hlen hk hk_cur); dsimp only at hrow
  by_cases hki : k = idx
  · subst hki; obtain ⟨hw, ha, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, hrc⟩ := hrow
    simp only [List.getElem_set_self]; have hnn := hw.2.2.1
    have hrc_toNat : curObjs[k].rc.toNat < 2147483647 := by
      rw [BitVec.toInt_eq_toNat_cond] at hnn hbound; split at hbound <;> omega
    have hinc_toInt : (curObjs[k].rc + 1#32).toInt = curObjs[k].rc.toInt + 1 := by
      rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
      have hsum : (curObjs[k].rc + 1#32).toNat = curObjs[k].rc.toNat + 1 := by bv_omega
      rw [hsum]; split <;> split <;> omega
    refine ⟨lcnfObjWf_withRc hw (by rw [hinc_toInt]; omega), ha, f1, f2, f3, f4, f5, f6,
      f7, f8, f9, f10, f11, ?_⟩
    rcases hrc with ⟨_, hz2⟩ | ⟨hpos, heq⟩
    · exact absurd hz2 hrcNz
    · right; refine ⟨hpos, ?_⟩
      have hcnt : [p].count objs[k].addr = 1 := by simp [← ha, haddr]
      simp only [LcnfObj.withRc]; rw [hinc_toInt, heq, List.count_append, hcnt]; omega
  · rw [List.getElem_set_ne (Ne.symm hki) hk_cur']
    exact cloUnderIncRel_row_keep (by rw [← hrow.2.1]; exact huniq k hk_cur hki) hrow

private theorem split_clo_region {c : BitVec 64} {nfix k : Nat}
    (hb : 24 + 8 * (nfix + k) ≤ 2 ^ 64) {m : Mem 64} (hr : region c (24 + 8 * (nfix + k)) m) :
    ∃ (v0 v8 v16 : BitVec 64) (dst : List (BitVec 64)), dst.length = nfix ∧
      (cell64 c v0 ⋆ cell64 (c + 8#64) v8 ⋆ cell64 (c + 16#64) v16 ⋆ array64 (c + 24#64) dst ⋆
      region (c + BitVec.ofNat 64 (24 + 8 * nfix)) (8 * k)) m := by
  have h1 : 24 + 8 * (nfix + k) = (24 + 8 * nfix) + 8 * k := by omega
  rw [h1, region_split (by omega)] at hr; obtain ⟨m1, mTail, rfl, hd1, h1m, hTail⟩ := hr
  obtain ⟨m24, mArr, rfl, hd24, h24m, hArm⟩ :=
    (region_split (a := c) (n1 := 24) (n2 := 8 * nfix) (by omega)) ▸ h1m
  obtain ⟨dst, hlen, hDst⟩ := region_to_array64 nfix (by omega) hArm
  obtain ⟨m0, m16, rfl, hd0, h0m, h16m⟩ :=
    (region_split (a := c) (n1 := 8) (n2 := 16) (by decide)) ▸ h24m
  have hsp8 : region (c + 8#64) 16 = (region (c + 8#64) 8 ⋆ region (c + 16#64) 8) := by
    rw [show c + 16#64 = c + 8#64 + 8#64 by bv_omega]
    exact region_split (a := c + 8#64) (n1 := 8) (n2 := 8) (by decide)
  obtain ⟨m8, m16', rfl, hd8, h8m, h16m'⟩ := hsp8 ▸ h16m
  obtain ⟨v0, hv0⟩ := region_to_cell64 h0m; obtain ⟨v8, hv8⟩ := region_to_cell64 h8m
  obtain ⟨v16, hv16⟩ := region_to_cell64 h16m'
  have hAll : (((cell64 c v0 ⋆ (cell64 (c + 8#64) v8 ⋆ cell64 (c + 16#64) v16)) ⋆
      array64 (c + 24#64) dst) ⋆ region (c + BitVec.ofNat 64 (24 + 8 * nfix)) (8 * k))
      (((m0.union (m8.union m16')).union mArr).union mTail) :=
    ⟨(m0.union (m8.union m16')).union mArr, mTail, rfl, hd1,
      ⟨m0.union (m8.union m16'), mArr, rfl, hd24,
        ⟨m0, m8.union m16', rfl, hd0, hv0, ⟨m8, m16', rfl, hd8, hv8, hv16⟩⟩, hDst⟩, hTail⟩
  exact ⟨v0, v8, v16, dst, hlen, sep_cast hAll (by ac_rfl)⟩

private theorem cloMetaWord_arity (a n : Nat) (ha : a < 65536) :
    cloMetaWord a n &&& 65535#64 = BitVec.ofNat 64 a := by
  unfold cloMetaWord; apply BitVec.eq_of_toNat_eq; apply Nat.eq_of_testBit_eq; intro i
  simp only [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    show (65535#64).toNat = 2 ^ 16 - 1 from rfl, Nat.mod_eq_of_lt (by omega : a < 2 ^ 64),
    Nat.testBit_and, Nat.testBit_or, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  by_cases hi : i < 16
  · simp [hi, Nat.testBit_shiftLeft, show ¬ 16 ≤ i by omega, show i < 64 by omega]
  · have ha0 : a.testBit i = false := Nat.testBit_lt_two_pow
      (show a < 2 ^ i from Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (n := 2) (by decide)
          (by omega : 16 ≤ i)))
    simp [hi, ha0]

private theorem fc_cloMeta_arity (fc : LcnfObj) (ha : fc.arity < 65536) :
    fc.cloMeta &&& 65535#64 = BitVec.ofNat 64 fc.arity :=
  cloMetaWord_arity fc.arity fc.fields.length ha

private theorem fc_cloMeta_nfix (fc : LcnfObj) (ha : fc.arity < 65536) (hn :
    fc.fields.length < 65536) :
    (fc.cloMeta >>> 16) &&& 65535#64 = BitVec.ofNat 64 fc.fields.length :=
  cloMetaWord_nfix fc.arity fc.fields.length ha hn

private theorem list_count_take_lt {α : Type _} [BEq α] [LawfulBEq α]
    (xs : List α) {i : Nat} (hi : i < xs.length) :
    (xs.take i).count xs[i] + 1 ≤ xs.count xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.take_succ_cons, List.getElem_cons_succ, List.count_cons]
      have ih' := ih (by simp at hi; omega)
      cases x == xs[i]'(by simp at hi; omega) <;> simp <;> omega

private theorem clo_take_eq_of_take_eq {α : Type _} {a b : List α} {n : Nat}
    (ha : a.length = n) (hb : b.length = n) (ht : a.take n = b.take n) : a = b := by
  rwa [List.take_of_length_le (Nat.le_of_eq ha), List.take_of_length_le (Nat.le_of_eq hb)] at ht

private theorem list_take_set_succ {α : Type _} {dst src : List α} {i : Nat}
    (hi : i < dst.length) (hs : i < src.length) (ht : dst.take i = src.take i) :
    (dst.set i src[i]).take (i + 1) = src.take (i + 1) := by
  rw [list_take_set_append dst hi src[i], ht, List.take_append_getElem hs]

private theorem lcnfObjMem_clo_eq (fc : LcnfObj) (ht : fc.tag = closureTag) : lcnfObjMem fc =
    (cell64 fc.addr fc.header ⋆ cell64 (fc.addr + 8#64) fc.funId ⋆
    cell64 (fc.addr + 16#64) fc.cloMeta ⋆ array64 (fc.addr + 24#64) fc.fields ⋆
    region (fc.addr + BitVec.ofNat 64 (24 + 8 * fc.fields.length))
    (fc.csSz - (24 + 8 * fc.fields.length))) := by
  unfold lcnfObjMem; rw [ite_eq_left ht]

private def cloNewObjMem (c : BitVec 64) (fc : LcnfObj) (sz k : Nat)
    (extra : List (BitVec 64)) : Mem 64 → Prop :=
  cell64 c (1#64 ||| BitVec.ofNat 64 sz <<< 32 ||| BitVec.ofNat 64 closureTag <<< 56) ⋆
  cell64 (c + 8#64) fc.funId ⋆ cell64 (c + 16#64) (cloMetaWord fc.arity (extra.length + k)) ⋆
  array64 (c + 24#64) extra ⋆ region (c + BitVec.ofNat 64 (24 + 8 * extra.length)) (8 * k)

private theorem clo_unpack_post {c : BitVec 64} {fc : LcnfObj} {sz k : Nat}
    {Rest : Mem 64 → Prop} {m : Mem 64} (hm : (cloNewObjMem c fc sz k fc.fields ⋆ Rest) m) :
    ((cell64 c (1#64 ||| BitVec.ofNat 64 sz <<< 32 ||| BitVec.ofNat 64 closureTag <<< 56) ⋆
    cell64 (c + 8#64) fc.funId ⋆
    cell64 (c + 16#64) (cloMetaWord fc.arity (fc.fields.length + k)) ⋆
    array64 (c + 24#64) fc.fields ⋆
    region (c + BitVec.ofNat 64 (24 + 8 * fc.fields.length)) (8 * k)) ⋆ Rest) m :=
  hm

theorem lcnf_clo_under_wp (Γ : Env)
    (hAlloc : ∀ xs m Q X, lcnfAllocSpec xs m Q X → Γ "lcnf_alloc" [i64, i64] [i64] xs m Q X)
    (hFree : ∀ xs m Q X, lcnfFreeObjSpec xs m Q X → Γ "lcnf_free_obj" [i64, i64] [] xs m Q X) :
    ∀ (xs : Tup Val lcnf_clo_under.as) (m : Mem 64) (Q : Post lcnf_clo_under.rs) (X : XPost),
    lcnfCloUnderSpec xs m Q X → Func.wp Γ lcnf_clo_under.body xs m Q X := by
  dsimp [lcnf_clo_under]
  rintro ⟨rt, f, k, ⟨⟩⟩ m Q X ⟨st, fc, objs, R, hfcAddr, hfcTag, hfcWf, hObjsWf, hObjsCl,
    hFieldsMem, hRcBound, hkPos, hkLe, hTotLe, hMinSz, hMaxSz, hRoom, hm, hPost⟩
  dsimp [Func.wp, lcnf_clo_under_body]; let nfix : Nat := fc.fields.length
  let sz : Nat := 24 + 8 * (nfix + k.toNat); have hsp := hfcWf.2.2.2.2.2.2.2.2.2
  simp only [hfcTag, ↓reduceIte] at hsp; have harity : fc.arity < 65536 := hsp.1
  have hnfix_lt : nfix < 65536 := hsp.2.1
  have hf_ne0 : f ≠ 0#64 := by rw [← hfcAddr]; exact hfcWf.1
  have hf_al : f.toNat % 8 = 0 := by rw [← hfcAddr]; exact hfcWf.2.1
  have hmUnpack : (cell64 (f + 16#64) fc.cloMeta ⋆ cell64 f fc.header ⋆
      cell64 (f + 8#64) fc.funId ⋆ array64 (f + 24#64) fc.fields ⋆
      region (f + BitVec.ofNat 64 (24 + 8 * nfix)) (fc.csSz - (24 + 8 * nfix)) ⋆
      rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m := by
    have h1 : (lcnfObjMem fc ⋆ rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m := sep_cast hm (by ac_rfl)
    rw [lcnfObjMem_clo_eq fc hfcTag, hfcAddr] at h1; exact sep_cast h1 (by ac_rfl)
  c0_hsteps_nogrp
  have hcloAr : fc.cloMeta &&& 65535#64 = BitVec.ofNat 64 fc.arity := fc_cloMeta_arity fc harity
  have hcloNf : (fc.cloMeta >>> (OfNat.ofNat 16 : BitVec 64)) &&& 65535#64 =
      BitVec.ofNat 64 nfix := by
    rw [show fc.cloMeta >>> (OfNat.ofNat 16 : BitVec 64) = fc.cloMeta >>> 16 from by
      apply BitVec.eq_of_toNat_eq; simp]
    exact fc_cloMeta_nfix fc harity hnfix_lt
  dsimp only; erw [hcloAr, hcloNf]
  refine wp_join_group (fun _ _ => False) (fun _ _ _ hf => False.elim hf) ?_
  intro _J0 _hJ0; c0_hsteps_nogrp; dsimp only
  have hv9 : BitVec.ofNat 64 nfix + k = BitVec.ofNat 64 (nfix + k.toNat) := by
    apply BitVec.eq_of_toNat_eq; simp
  have hv11 : 24#64 + 8#64 * (BitVec.ofNat 64 nfix + k) = BitVec.ofNat 64 sz := by
    rw [hv9]; apply BitVec.eq_of_toNat_eq; simp [sz]
  rw [hv11]
  have hmAlloc : (rtC0Inv rt st ⋆ (lcnfObjMem fc ⋆ lcnfHeap objs ⋆ R)) m := sep_cast hm (by ac_rfl)
  refine wp_call_ret1 _ _ (fun c m1 => ∃ st',
      c ≠ 0#64 ∧ c.toNat % 8 = 0 ∧ st'.PreservesMeta st ∧ st'.rem ≤ st.rem ∧
      ((rtC0Inv rt st' ⋆ region c sz) ⋆ (lcnfObjMem fc ⋆ lcnfHeap objs ⋆ R)) m1) ?_ ?_
  · apply hAlloc
    have hsz : (BitVec.ofNat 64 sz).toNat = sz := Nat.mod_eq_of_lt (by omega)
    have hal : align8 (BitVec.ofNat 64 sz).toNat = sz := by unfold align8; rw [hsz]; omega
    refine ⟨st, lcnfObjMem fc ⋆ lcnfHeap objs ⋆ R, by dsimp only [Arg.val]; rw [hsz]; omega,
      by dsimp only [Arg.val]; rw [hal]; exact hMinSz,
      by dsimp only [Arg.val]; rw [hal]
         exact Nat.lt_trans hMaxSz (by decide : 65536 < rtMaxObjBytes),
      by dsimp only [Arg.val]; rw [hal]; exact hRoom, hmAlloc,
      fun c st' m1 hc0 hcAl hmMeta hmRem hm1 => by
        dsimp only [Arg.val] at hm1; rw [hal] at hm1; exact ⟨st', hc0, hcAl, hmMeta, hmRem, hm1⟩⟩
  · intro c m1 ⟨st', hcNe0, hcAlign, hMeta1, hRem1, hm1⟩
    let F_tail : Mem 64 → Prop := cell64 f fc.header ⋆ cell64 (f + 8#64) fc.funId ⋆
      cell64 (f + 16#64) fc.cloMeta ⋆ array64 (f + 24#64) fc.fields ⋆
      region (f + BitVec.ofNat 64 (24 + 8 * nfix)) (fc.csSz - (24 + 8 * nfix)) ⋆
      rtC0Inv rt st' ⋆ lcnfHeap objs ⋆ R
    have hm1_r : (region c sz ⋆ F_tail) m1 := by
      have h1 : (region c sz ⋆ (lcnfObjMem fc ⋆ rtC0Inv rt st' ⋆ lcnfHeap objs ⋆ R)) m1 :=
        sep_cast hm1 (by ac_rfl)
      rw [lcnfObjMem_clo_eq fc hfcTag, hfcAddr] at h1
      exact sep_mono_r (fun _ x => sep_cast x (by dsimp only [F_tail])) h1
    obtain ⟨mr, mfr, hmrEq, hd, hmr, hmfr⟩ := hm1_r
    obtain ⟨v0, v8, v16, dst, hdstLen, hsplit⟩ := split_clo_region (by omega) hmr
    have hm1_raw : ((cell64 c v0 ⋆ cell64 (c + 8#64) v8 ⋆ cell64 (c + 16#64) v16 ⋆
        array64 (c + 24#64) dst ⋆ region (c + BitVec.ofNat 64 (24 + 8 * nfix)) (8 * k.toNat)) ⋆
        F_tail) (mr.union mfr) := ⟨mr, mfr, rfl, hd, hsplit, hmfr⟩
    have hm1' : (cell64 c v0 ⋆ cell64 (c + 8#64) v8 ⋆ cell64 (c + 16#64) v16 ⋆
        array64 (c + 24#64) dst ⋆ region (c + BitVec.ofNat 64 (24 + 8 * nfix)) (8 * k.toNat) ⋆
        F_tail) m1 := hmrEq ▸ sep_cast hm1_raw (by ac_rfl)
    dsimp only [F_tail] at hm1'
    let cHdr : BitVec 64 :=
      1#64 ||| BitVec.ofNat 64 sz <<< 32 ||| BitVec.ofNat 64 closureTag <<< 56
    let cMeta : BitVec 64 := cloMetaWord fc.arity (nfix + k.toNat)
    iterate 6 c0_hstep; dsimp only
    have hcHdrEq : (1#64 ||| BitVec.ofNat 64 sz <<< (OfNat.ofNat 32 : BitVec 64) |||
        245#64 <<< (OfNat.ofNat 56 : BitVec 64)) = cHdr := by dsimp [cHdr]; congr 1
    erw [hcHdrEq]; c0_hsteps_nogrp
    have hcMetaEq : (BitVec.ofNat 64 fc.arity |||
        (BitVec.ofNat 64 nfix + k) <<< (OfNat.ofNat 16 : BitVec 64)) = cMeta := by
      dsimp [cMeta, cloMetaWord]; rw [hv9]
    let F_L1 : Mem 64 → Prop :=
      cell64 c cHdr ⋆ cell64 (c + 8#64) fc.funId ⋆ cell64 (c + 16#64) cMeta ⋆
      region (c + BitVec.ofNat 64 (24 + 8 * nfix)) (8 * k.toNat) ⋆ cell64 f fc.header ⋆
      cell64 (f + 8#64) fc.funId ⋆ cell64 (f + 16#64) fc.cloMeta ⋆
      region (f + BitVec.ofNat 64 (24 + 8 * nfix)) (fc.csSz - (24 + 8 * nfix)) ⋆
      rtC0Inv rt st' ⋆ lcnfHeap objs ⋆ R
    have hm4 : (array64 (c + 24#64) dst ⋆ array64 (f + 24#64) fc.fields ⋆ F_L1) m := by
      erw [hcMetaEq] at hm; simp only [sep_emp] at hm; dsimp only [F_L1]; c0_frame
    refine wp_while_state (fun (s : Nat × List (BitVec 64)) => (BitVec.ofNat 64 s.1, ()))
      (fun s => nfix - s.1) (fun (i, curDst) curM => i ≤ nfix ∧ curDst.length = nfix ∧
        curDst.take i = fc.fields.take i ∧
        (array64 (c + 24#64) curDst ⋆ array64 (f + 24#64) fc.fields ⋆ F_L1) curM)
      (fun _ hJ1 => hJ1 (0, dst) m ⟨Nat.zero_le _, hdstLen, by simp, hm4⟩)
      (fun J1 (i, curDst) mL1 ⟨hiLe, hDstLen, hTakeEq, hmL1⟩ hIH1 => by
        dsimp; c0_hsteps_nogrp
        · have hiLt : i < nfix := by
            rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : nfix < 2 ^ 64)] at hc; exact hc
          c0_hsteps_nogrp
          have hiNat : (BitVec.ofNat 64 i).toNat = i := Nat.mod_eq_of_lt (by omega)
          erw [show BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) by
            apply BitVec.eq_of_toNat_eq; simp [Nat.add_mod]]
          refine hIH1 (i + 1, curDst.set i fc.fields[i]) _ (by omega)
            ⟨by omega, by simp [hDstLen], list_take_set_succ (by omega) hiLt hTakeEq, ?_⟩
          simp only [hiNat, sep_emp] at *; rw [sep_assoc]
          exact ‹(array64 (c + 24#64) (curDst.set i fc.fields[i]) ⋆ _) m›
        · have hiEq : i = nfix := by
            rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : nfix < 2 ^ 64)] at hc; omega
          subst hiEq
          have hCurEq : curDst = fc.fields := clo_take_eq_of_take_eq hDstLen rfl hTakeEq
          rw [hCurEq] at hmL1; let C_mem : Mem 64 → Prop := cloNewObjMem c fc sz k.toNat fc.fields
          have hCmemEq : (cell64 c cHdr ⋆ cell64 (c + 8#64) fc.funId ⋆
              cell64 (c + 16#64) cMeta ⋆ array64 (c + 24#64) fc.fields ⋆
              region (c + BitVec.ofNat 64 (24 + 8 * nfix)) (8 * k.toNat)) = C_mem := rfl
          have hmL1_pack : (rtC0Inv rt st' ⋆ lcnfObjMem fc ⋆ C_mem ⋆ lcnfHeap objs ⋆ R) mL1 := by
            dsimp [F_L1] at hmL1
            have h1 : (C_mem ⋆ (cell64 f fc.header ⋆ cell64 (f + 8#64) fc.funId ⋆
                cell64 (f + 16#64) fc.cloMeta ⋆ array64 (f + 24#64) fc.fields ⋆
                region (f + BitVec.ofNat 64 (24 + 8 * nfix)) (fc.csSz - (24 + 8 * nfix))) ⋆
                rtC0Inv rt st' ⋆ lcnfHeap objs ⋆ R) mL1 := by
              rw [← hCmemEq]; exact sep_cast hmL1 (by ac_rfl)
            rw [← hfcAddr, ← lcnfObjMem_clo_eq fc hfcTag] at h1; exact sep_cast h1 (by ac_rfl)
          have hmL1_hdr : (cell64 f fc.header ⋆ lcnfObjBody fc ⋆ rtC0Inv rt st' ⋆ C_mem ⋆
              lcnfHeap objs ⋆ R) mL1 := by
            rw [← hfcAddr, ← lcnfObjMem_eq_header_body fc]; exact sep_cast hmL1_pack (by ac_rfl)
          c0_hsteps_nogrp
          rw [LcnfObj.header_rc fc hfcWf.2.2.2.1 hfcWf.2.2.2.2.1 hfcWf.2.2.2.2.2.1]
          refine wp_join_group (fun _ m2 => Q (c, ()) m2) (fun _ _ m2 hQ => by dsimp; exact hQ) ?_
          intro J2 hJ2; c0_hsteps_nogrp
          · have hrc1 : fc.rc = 1#32 := BitVec.eq_of_toNat_eq (by
              have := congrArg BitVec.toNat (‹BitVec.ofNat 64 fc.rc.toNat = 1›)
              simpa [Nat.mod_eq_of_lt (by omega : fc.rc.toNat < 2 ^ 64)] using this)
            have hFreePre : (rtC0Inv rt st' ⋆ freeObjLayout f fc.totalBytes fc.header ⋆
                ((C_mem ⋆ lcnfHeap objs) ⋆ R)) mL1 := by
              have h1 : (lcnfObjMem fc ⋆ (rtC0Inv rt st' ⋆ (C_mem ⋆ lcnfHeap objs ⋆ R))) mL1 :=
                sep_cast hmL1_pack (by ac_rfl)
              rw [← hfcAddr]
              exact sep_cast (sep_mono (fun _ => lcnfObjMem_to_freeObjLayout hfcWf) h1) (by ac_rfl)
            refine wp_call_of_spec _ _ ?_; apply hFree
            have hEven : ¬(f &&& 1#64 ≠ 0#64) := fun h => h (BitVec.eq_of_toNat_eq (by
              rw [BitVec.toNat_and, BitVec.toNat_zero,
                show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]; omega))
            dsimp [lcnfFreeObjSpec]; simp only [hEven, ↓reduceIte]
            refine ⟨st', fc.header, fc.totalBytes, (C_mem ⋆ lcnfHeap objs) ⋆ R, hf_ne0, hf_al,
              hfcWf.2.2.2.2.2.2.1, hfcWf.2.2.2.2.2.2.2.1, hfcWf.2.2.2.2.2.2.2.2.1, hFreePre, ?_⟩
            intro st'' mFree hMeta2 hRem2 _ hmFree
            refine hJ2 () mFree (hPost c st'' objs mFree hcNe0 hcAlign
              (preservesMeta_trans hMeta1 hMeta2) (by omega) (by simp [hrc1]) ?_)
            simp only [hrc1, ↓reduceIte, sep_emp, C_mem, cloNewObjMem, sz, nfix, sep_assoc]
              at hmFree ⊢
            exact hmFree
          · have hrcNe1 : fc.rc ≠ 1#32 := fun hEq => hc (by rw [hEq]; rfl)
            let F_L3 : Mem 64 → Prop := rtC0Inv rt st' ⋆ C_mem ⋆ R
            refine wp_while_state (fun (s : Nat × List LcnfObj) => (BitVec.ofNat 64 s.1, ()))
              (fun s => nfix - s.1) (fun (j, curObjs) curM => j ≤ nfix ∧
                CloUnderIncRel (fc.fields.take j) objs curObjs ∧
                (lcnfHeap curObjs ⋆ (lcnfObjMem fc ⋆ F_L3)) curM)
              (fun _ hJ3 => hJ3 (0, objs) mL1 ⟨Nat.zero_le _, cloUnderIncRel_init hObjsWf hObjsCl,
                by dsimp [F_L3]; exact sep_cast hmL1_pack (by ac_rfl)⟩)
              (fun J3 (j, curObjs) mL3 ⟨hjLe, hRel, hmL3⟩ hIH3 => by
                dsimp; c0_hsteps_nogrp
                · have hjLt : j < nfix := by
                    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
                      Nat.mod_eq_of_lt (by omega : nfix < 2 ^ 64)] at hc; exact hc
                  have hmL3_arr : (array64 (f + 24#64) fc.fields ⋆
                      (cell64 f fc.header ⋆ cell64 (f + 8#64) fc.funId ⋆
                        cell64 (f + 16#64) fc.cloMeta ⋆
                        region (f + BitVec.ofNat 64 (24 + 8 * nfix)) (fc.csSz - (24 + 8 * nfix)) ⋆
                        lcnfHeap curObjs ⋆ F_L3)) mL3 := by
                    have h1 : (lcnfObjMem fc ⋆ (lcnfHeap curObjs ⋆ F_L3)) mL3 :=
                      sep_cast hmL3 (by ac_rfl)
                    rw [lcnfObjMem_clo_eq fc hfcTag, hfcAddr] at h1; exact sep_cast h1 (by ac_rfl)
                  c0_hsteps_nogrp
                  simp only [show (BitVec.ofNat 64 j).toNat = j from Nat.mod_eq_of_lt (by omega)]
                  let p : BitVec 64 := fc.fields[j]
                  refine wp_join_state0 (fun (curObjs' : List LcnfObj) (curM4 : Mem 64) =>
                      CloUnderIncRel (fc.fields.take (j + 1)) objs curObjs' ∧
                      (lcnfHeap curObjs' ⋆ (lcnfObjMem fc ⋆ F_L3)) curM4)
                    (fun _ curObjs' m4 ⟨hRel', hm4'⟩ => by
                      c0_hsteps_nogrp
                      erw [show BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) by
                        apply BitVec.eq_of_toNat_eq; simp [Nat.add_mod]]
                      exact hIH3 (j + 1, curObjs') m4 (by omega) ⟨by omega, hRel', hm4'⟩) ?_
                  intro J4 hJ4; c0_hsteps_nogrp
                  · obtain ⟨o0, ho0Mem, ho0Addr⟩ := hFieldsMem p (List.getElem_mem hjLt) ‹_›
                    rw [List.mem_iff_getElem] at ho0Mem; obtain ⟨idx, hidx0, rfl⟩ := ho0Mem
                    rcases hRel with ⟨hlenRel, hClRel, hForallRel⟩
                    have hidx : idx < curObjs.length := by omega
                    have hrow := hForallRel _ (zip_mem_pair hlenRel hidx0 hidx); dsimp only at hrow
                    rcases hrow with ⟨hCurWf, hCurAddr, _, _, _, _, _, _, _, _, _, _, _, hCurRc⟩
                    have hCurAddrP : curObjs[idx].addr = p := hCurAddr.trans ho0Addr
                    have huniq : ∀ j' (hj' : j' < curObjs.length),
                        j' ≠ idx → curObjs[j'].addr ≠ p := fun j' hj' hji => by
                      rw [← hCurAddrP]; exact (lcnfHeap_addr_ne hmL3 hidx hj' hji.symm).symm
                    refine wp_load_of (hCurAddrP ▸ lcnfHeap_load_header hidx hmL3) ?_
                    c0_hsteps_nogrp
                    rw [LcnfObj.header_rc curObjs[idx] hCurWf.2.2.2.1 hCurWf.2.2.2.2.1
                      hCurWf.2.2.2.2.2.1]
                    refine wp_join_state0 (fun (curObjs' : List LcnfObj) (curM5 : Mem 64) =>
                        CloUnderIncRel (fc.fields.take (j + 1)) objs curObjs' ∧
                        (lcnfHeap curObjs' ⋆ (lcnfObjMem fc ⋆ F_L3)) curM5)
                      (fun _ curObjs' m5 hm5 => hJ4 curObjs' m5 hm5) ?_
                    intro J5 hJ5
                    have hbound : curObjs[idx].rc.toInt < 2147483647 := by
                      rcases hCurRc with ⟨_, hz⟩ | ⟨hpos0, hrcSum⟩
                      · rw [hz]; decide
                      · have hle : (fc.fields.take j).count p + 1 ≤ fc.fields.count p := by
                          simpa [p] using list_count_take_lt fc.fields hjLt
                        have hB := hRcBound objs[idx] (List.getElem_mem hidx0) hpos0
                        rw [ho0Addr] at hB; rw [hrcSum, ho0Addr]; omega
                    c0_hsteps_nogrp
                    · have hRcNz32 : curObjs[idx].rc ≠ 0#32 := fun h0 =>
                        ‹¬BitVec.ofNat 64 curObjs[idx].rc.toNat = 0#64› (by rw [h0]; rfl)
                      have hst := lcnfHeap_store_rc hidx (curObjs[idx].rc + 1#32) hmL3
                      rw [hCurAddrP, ← lcnfObjHeader_add1 curObjs[idx] hCurWf.2.2.2.1
                        hCurWf.2.2.2.2.1 hCurWf.2.2.2.2.2.1 hCurWf.2.2.1 hbound] at hst
                      refine wp_store_sep hst (fun mL3' hmL3' => hJ5 _ mL3' ⟨?_, hmL3'⟩)
                      rw [← List.take_append_getElem hjLt]
                      exact cloUnderIncRel_step_pos ⟨hlenRel, hClRel, hForallRel⟩ hidx
                        hCurAddrP hRcNz32 hbound huniq
                    · exfalso
                      have hrcNat : curObjs[idx].rc.toNat < 2147483647 := by
                        have hnn := hCurWf.2.2.1; rw [BitVec.toInt_eq_toNat_cond] at hnn hbound
                        split at hbound <;> omega
                      rw [Nat.mod_eq_of_lt (Nat.lt_trans curObjs[idx].rc.isLt
                          (by decide : 2 ^ 32 < 2 ^ 64)),
                        show (2147483647 : Nat) % 2 ^ 64 = 2147483647 from rfl] at hc; omega
                    · have hRcZ32 : curObjs[idx].rc = 0#32 := BitVec.eq_of_toNat_eq (by
                        have := congrArg BitVec.toNat hc
                        simpa [Nat.mod_eq_of_lt (by omega : curObjs[idx].rc.toNat < 2 ^ 64)]
                          using this)
                      refine hJ5 curObjs mL3 ⟨?_, hmL3⟩; rw [← List.take_append_getElem hjLt]
                      exact cloUnderIncRel_step_zero ⟨hlenRel, hClRel, hForallRel⟩ hidx
                        hCurAddrP hRcZ32 huniq
                  · refine hJ4 curObjs mL3 ⟨?_, hmL3⟩; rw [← List.take_append_getElem hjLt]
                    exact cloUnderIncRel_step_skip hRel ‹_›
                · have hjEq : j = nfix := by
                    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
                      Nat.mod_eq_of_lt (by omega : nfix < 2 ^ 64)] at hc; omega
                  subst hjEq
                  have hRelFull : CloUnderIncRel fc.fields objs curObjs := by
                    rwa [List.take_of_length_le (Nat.le_refl _)] at hRel
                  refine wp_join_group (fun _ m6 => Q (c, ()) m6) (fun _ _ m6 hQ => hJ2 () m6 hQ) ?_
                  intro J6 hJ6; c0_hsteps_nogrp
                  · have hlt := objWf_rc_lt hfcWf
                    have hgt1 : 1 < fc.rc.toNat := by
                      have hprev := ‹1 % 2 ^ 64 < fc.rc.toNat % 2 ^ 64›
                      rwa [Nat.mod_eq_of_lt (by omega : fc.rc.toNat < 2 ^ 64)] at hprev
                    have hst := lcnfObjMem_store_rc (fc.rc - 1#32)
                      (show (lcnfObjMem fc ⋆ (lcnfHeap curObjs ⋆ F_L3)) mL3 from
                        sep_cast hmL3 (by ac_rfl))
                    rw [hfcAddr, ← lcnfObjHeader_sub1 fc hfcWf.2.2.2.1 hfcWf.2.2.2.2.1
                      hfcWf.2.2.2.2.2.1 hfcWf.2.2.1 hgt1] at hst
                    refine wp_store_sep hst (fun mL3' hmL3' => ?_)
                    have hrcNz : fc.rc ≠ 0#32 := fun h0 => by
                      have : fc.rc.toNat = 0 := by rw [h0]; rfl
                      omega
                    refine hJ6 () mL3' (hPost c st' curObjs mL3' hcNe0 hcAlign hMeta1 hRem1
                      (by simp only [hrcNe1, ↓reduceIte]; exact hRelFull) ?_)
                    simp only [hrcNe1, ↓reduceIte, hrcNz]; dsimp only [F_L3] at hmL3'
                    have hOrder : (rtC0Inv rt st' ⋆ C_mem ⋆ lcnfObjMem (fc.withRc (fc.rc - 1#32)) ⋆
                        lcnfHeap curObjs ⋆ R) mL3' := sep_cast hmL3' (by ac_rfl)
                    dsimp only [C_mem, cloNewObjMem, sz, nfix] at hOrder ⊢
                    simp only [sep_assoc] at hOrder ⊢; exact hOrder
                  · exfalso; have hrcLt : fc.rc.toNat < 2147483648 := objWf_rc_lt hfcWf
                    rw [Nat.mod_eq_of_lt (Nat.lt_trans fc.rc.isLt (by decide : 2 ^ 32 < 2 ^ 64)),
                      show (2147483648 : Nat) % 2 ^ 64 = 2147483648 from rfl] at hc; omega
                  · have hlt := objWf_rc_lt hfcWf
                    have hrc0 : fc.rc = 0#32 := by
                      rw [Nat.mod_eq_of_lt (by omega : fc.rc.toNat < 2 ^ 64)] at hc
                      exact BitVec.eq_of_toNat_eq (by
                        have : fc.rc.toNat ≠ 1 := fun h1 => hrcNe1 (BitVec.eq_of_toNat_eq
                          (by simpa using h1))
                        simp; omega)
                    refine hJ6 () mL3 (hPost c st' curObjs mL3 hcNe0 hcAlign hMeta1 hRem1
                      (by simp only [hrcNe1, ↓reduceIte]; exact hRelFull) ?_)
                    have hwr0 : fc.withRc 0#32 = fc := by
                      cases fc; simp only [LcnfObj.withRc] at hrc0 ⊢; subst hrc0; rfl
                    simp only [hrc0, show (0#32 : BitVec 32) ≠ 1#32 by decide, ↓reduceIte,
                      show (0#32 - 0#32 : BitVec 32) = 0#32 from rfl, hwr0]
                    dsimp only [F_L3] at hmL3
                    have hOrder : (rtC0Inv rt st' ⋆ C_mem ⋆ lcnfObjMem fc ⋆
                        lcnfHeap curObjs ⋆ R) mL3 := sep_cast hmL3 (by ac_rfl)
                    dsimp only [C_mem, cloNewObjMem, sz, nfix] at hOrder ⊢
                    simp only [sep_assoc] at hOrder ⊢; exact hOrder))

@[expose] def rtC0M0aSpecEntries : List SpecEntry :=
  [ SpecEntry.ofFn lcnf_alloc lcnfAllocSpec true
  , SpecEntry.ofFn lcnf_free_obj lcnfFreeObjSpec true
  , SpecEntry.ofFn lcnf_clo_under lcnfCloUnderSpec true
  ]

theorem rtC0M0aSpecEntries_nodup : (rtC0M0aSpecEntries.map SpecEntry.name).Nodup := by decide

@[expose] def rtC0M0aEnv : Env := Env.ofTable rtC0M0aSpecEntries

theorem rtC0M0aEnv_alloc : ∀ xs m Q X,
    lcnfAllocSpec xs m Q X → rtC0M0aEnv "lcnf_alloc" [i64, i64] [i64] xs m Q X :=
  fun _ _ _ _ h => Env.ofTable_of_mem (e := SpecEntry.ofFn lcnf_alloc lcnfAllocSpec true)
    (by simp [rtC0M0aSpecEntries]) rtC0M0aSpecEntries_nodup h

theorem rtC0M0aEnv_free_obj : ∀ xs m Q X,
    lcnfFreeObjSpec xs m Q X → rtC0M0aEnv "lcnf_free_obj" [i64, i64] [] xs m Q X :=
  fun _ _ _ _ h => Env.ofTable_of_mem (e := SpecEntry.ofFn lcnf_free_obj lcnfFreeObjSpec true)
    (by simp [rtC0M0aSpecEntries]) rtC0M0aSpecEntries_nodup h

theorem rtC0M0aEnv_clo_under : ∀ xs m Q X,
    lcnfCloUnderSpec xs m Q X → rtC0M0aEnv "lcnf_clo_under" [i64, i64, i64] [i64] xs m Q X :=
  fun _ _ _ _ h => Env.ofTable_of_mem (e := SpecEntry.ofFn lcnf_clo_under lcnfCloUnderSpec true)
    (by simp [rtC0M0aSpecEntries]) rtC0M0aSpecEntries_nodup h

@[expose] def rtR0ModM0a : Module :=
  { fns := [lcnf_alloc, lcnf_free_obj, lcnf_clo_under], exits := ["lcnf_panic"] }

theorem rtR0ModM0a_checkAcyclic : rtR0ModM0a.checkAcyclic = true := by decide

theorem rtR0ModM0a_ok : ModuleOk rtC0M0aEnv rtR0ModM0a := by
  refine Env.ofTable_moduleOk rtR0ModM0a_checkAcyclic ?_ ?_
  · refine ⟨lcnf_alloc_wf, lcnf_free_obj_wf, lcnf_clo_under_wf, trivial⟩
  · refine ⟨⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h => lcnf_alloc_wp rtC0M0aEnv xs m Q X h⟩,
      ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h => lcnf_free_obj_wp rtC0M0aEnv xs m Q X h⟩,
      ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X h =>
        lcnf_clo_under_wp rtC0M0aEnv rtC0M0aEnv_alloc rtC0M0aEnv_free_obj xs m Q X h⟩,
      trivial⟩

theorem rtC0Env_clo_under_wp : ∀ xs m Q X,
    lcnfCloUnderSpec xs m Q X → Func.wp rtC0Env lcnf_clo_under.body xs m Q X :=
  lcnf_clo_under_wp rtC0Env rtC0Env_alloc rtC0Env_free_obj

end LeanQbe.T.LeanLCNF
