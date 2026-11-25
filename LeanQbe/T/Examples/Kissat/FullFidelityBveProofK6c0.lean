module

public import LeanQbe.T.Examples.Kissat.FullFidelityBveProof0
import all LeanQbe.T.Examples.Kissat.FullFidelityBveProof0
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullFidelityBveTactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBve

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchSpecs
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityBve.FidK6Tactics

/-! ## State projections & C0 scratch/work framing tactics -/

/-- State differing from `s` only in `scratch_buf`. -/
abbrev FidP6Scr (s : FullState) (scr' : List (BitVec 32)) : FullState :=
  { s with scratch := { s.scratch with scratch_buf := scr' } }

/-- State differing from `s` in `core.tmp`, `wsort`, `tarjan_mark`, and `scratch_buf`. -/
abbrev FidP6Work (s : FullState)
    (tmp' wsort' tmk' scr' : List (BitVec 32)) : FullState :=
  { s with
    core := { s.core with tmp := tmp' }
    scratch := { s.scratch with
      wsort := wsort', tarjan_mark := tmk', scratch_buf := scr' } }

theorem fid_k6c_work_self (s : FullState) :
    FidP6Work s s.core.tmp s.scratch.wsort s.scratch.tarjan_mark
      s.scratch.scratch_buf = s := rfl

theorem fid_k6c_scr_self (s : FullState) :
    FidP6Scr s s.scratch.scratch_buf = s := rfl

theorem fid_k6c_work_to_scr (s : FullState) (tmp' wsort' tmk' scr' : List (BitVec 32)) :
    FidP6Work s tmp' wsort' tmk' scr' =
      FidP6Scr (FidP6Work s tmp' wsort' tmk' s.scratch.scratch_buf) scr' := rfl

theorem fid_k6c_scrBuf_split {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (FullMem c s ⋆ R) m) :
    (FullMem c (FidP6Scr s s.scratch.scratch_buf) ⋆ R) m := by
  rwa [fid_k6c_scr_self]

theorem fid_k6c_scrBuf_unsplit {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {scr' : List (BitVec 32)}
    (h : (FullMem c (FidP6Scr s scr') ⋆ R) m)
    (heq : scr' = s.scratch.scratch_buf) :
    (FullMem c s ⋆ R) m := by
  subst heq
  rwa [fid_k6c_scr_self] at h

theorem fid_k6c_fullMem_subst {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {scr1 scr2 : List (BitVec 32)} (heq : scr1 = scr2)
    (h : (FullMem c (FidP6Scr s scr1) ⋆ R) m) :
    (FullMem c (FidP6Scr s scr2) ⋆ R) m := heq ▸ h

theorem fid_k6c_workMem_subst {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {tmp1 tmp2 w1 w2 t1 t2 scr1 scr2 : List (BitVec 32)}
    (ht : tmp1 = tmp2) (hw : w1 = w2) (htm : t1 = t2) (hs : scr1 = scr2)
    (h : (FullMem c (FidP6Work s tmp1 w1 t1 scr1) ⋆ R) m) :
    (FullMem c (FidP6Work s tmp2 w2 t2 scr2) ⋆ R) m := by
  subst ht hw htm hs; exact h

theorem fid_k6c_work_lengthsOk {c : FullCfg} {s : FullState}
    {tmp' wsort' tmk' scr' : List (BitVec 32)}
    (hl : s.LengthsOk c) (ht : tmp'.length = c.max_vars)
    (hw : wsort'.length = 2 * c.max_vars) (htm : tmk'.length = 2 * c.max_vars)
    (hs : scr'.length = c.scratch_cap) :
    (FidP6Work s tmp' wsort' tmk' scr').LengthsOk c :=
  ⟨{ hl.core_ok with tmp_len_arr := ht },
   { hl.scratch_ok with
      wsort_len := hw, tarjan_mark_len := htm, scratch_buf_len := hs }⟩

theorem fid_k6c_fullDenseInvW_work {c : FullCfg} {F0 : Std.Sat.CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    {tmp' wsort' tmk' scr' : List (BitVec 32)}
    (hi : FullDenseInvW c F0 F_cur s) (ht : tmp'.length = c.max_vars)
    (hw : wsort'.length = 2 * c.max_vars) (htm : tmk'.length = 2 * c.max_vars)
    (hs : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur (FidP6Work s tmp' wsort' tmk' scr') := by
  have hi_tmp := FullM6BveFwd.m6_fullDenseInvW_with_tmp hi ht
  rcases hi with ⟨hl, _, hlm, hnd, hext, hlev, hdm⟩
  exact ⟨fid_k6c_work_lengthsOk hl ht hw htm hs, hi_tmp.2.1, hlm, hnd, hext, hlev, hdm⟩

namespace FidK6cTactics

@[scoped c0_load] theorem c0_load_fid_scr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {scr : List (BitVec 32)} {i : BitVec 64}
    (hi : i.toNat < scr.length) (hm : (FullMem c (FidP6Scr s scr) ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + i * 4) = some scr[i.toNat] :=
  c0_load_full_scratch_buf (s := FidP6Scr s scr) hi hm

@[scoped c0_store] theorem c0_store_fid_scr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {scr : List (BitVec 32)} {i : BitVec 64}
    (v : BitVec 32) (hi : i.toNat < scr.length)
    (hm : (FullMem c (FidP6Scr s scr) ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + i * 4) ∧
      (FullMem c (FidP6Scr s (scr.set i.toNat v)) ⋆ R)
        (storeMem m i32 (c.pScratchBuf + i * 4) v) :=
  c0_store_full_scratch_buf (s := FidP6Scr s scr) v hi hm

@[scoped c0_load] theorem c0_load_fid_w_scr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (hi : i.toNat < scr.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + i * 4) = some scr[i.toNat] :=
  c0_load_full_scratch_buf (s := FidP6Work s tmp wsort tmk scr) hi hm

@[scoped c0_store] theorem c0_store_fid_w_scr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (v : BitVec 32) (hi : i.toNat < scr.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + i * 4) ∧
      (FullMem c (FidP6Work s tmp wsort tmk (scr.set i.toNat v)) ⋆ R)
        (storeMem m i32 (c.pScratchBuf + i * 4) v) :=
  c0_store_full_scratch_buf (s := FidP6Work s tmp wsort tmk scr) v hi hm

@[scoped c0_load] theorem c0_load_fid_w_tmk {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (hi : i.toNat < tmk.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    loadVal m i32 (c.pTarjanMark + i * 4) = some tmk[i.toNat] :=
  c0_load_full_tarjan_mark (s := FidP6Work s tmp wsort tmk scr) hi hm

@[scoped c0_store] theorem c0_store_fid_w_tmk {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (v : BitVec 32) (hi : i.toNat < tmk.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    storeOk m i32 (c.pTarjanMark + i * 4) ∧
      (FullMem c (FidP6Work s tmp wsort (tmk.set i.toNat v) scr) ⋆ R)
        (storeMem m i32 (c.pTarjanMark + i * 4) v) :=
  c0_store_full_tarjan_mark (s := FidP6Work s tmp wsort tmk scr) v hi hm

@[scoped c0_load] theorem c0_load_fid_w_wsort {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (hi : i.toNat < wsort.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    loadVal m i32 (c.pWsort + i * 4) = some wsort[i.toNat] :=
  c0_load_full_wsort (s := FidP6Work s tmp wsort tmk scr) hi hm

@[scoped c0_store] theorem c0_store_fid_w_wsort {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (v : BitVec 32) (hi : i.toNat < wsort.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    storeOk m i32 (c.pWsort + i * 4) ∧
      (FullMem c (FidP6Work s tmp (wsort.set i.toNat v) tmk scr) ⋆ R)
        (storeMem m i32 (c.pWsort + i * 4) v) :=
  c0_store_full_wsort (s := FidP6Work s tmp wsort tmk scr) v hi hm

@[scoped c0_load] theorem c0_load_fid_w_tmp {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (hi : i.toNat < tmp.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    loadVal m i32 (c.pTmp + i * 4) = some tmp[i.toNat] :=
  c0_load_full_tmp (s := FidP6Work s tmp wsort tmk scr) hi hm

@[scoped c0_store] theorem c0_store_fid_w_tmp {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (v : BitVec 32) (hi : i.toNat < tmp.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    storeOk m i32 (c.pTmp + i * 4) ∧
      (FullMem c (FidP6Work s (tmp.set i.toNat v) wsort tmk scr) ⋆ R)
        (storeMem m i32 (c.pTmp + i * 4) v) :=
  c0_store_full_tmp (s := FidP6Work s tmp wsort tmk scr) v hi hm

@[scoped c0_load] theorem c0_load_fid_w_arena {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (hi : i.toNat < s.core.arena.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    loadVal m i32 (c.pArena + i * 4) = some s.core.arena[i.toNat] :=
  c0_load_full_arena (s := FidP6Work s tmp wsort tmk scr) hi hm

@[scoped c0_load] theorem c0_load_fid_w_vals {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (hi : i.toNat < s.core.vals.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    loadVal m i8 (c.pVals + i) = some s.core.vals[i.toNat] :=
  c0_load_full_vals (s := FidP6Work s tmp wsort tmk scr) hi hm

@[scoped c0_store] theorem c0_store_fid_scr_nat {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {scr : List (BitVec 32)} {n : Nat}
    (v : BitVec 32) (hn : n < scr.length) (hn64 : n < 2 ^ 30)
    (hm : (FullMem c (FidP6Scr s scr) ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf +
      BitVec.ofNat (@OfNat.ofNat Nat 64 (instOfNatNat 64))
        (@OfNat.ofNat Nat n (instOfNatNat n)) * 4) ∧
      (FullMem c (FidP6Scr s (scr.set n v)) ⋆ R)
        (storeMem m i32 (c.pScratchBuf +
          BitVec.ofNat (@OfNat.ofNat Nat 64 (instOfNatNat 64))
            (@OfNat.ofNat Nat n (instOfNatNat n)) * 4) v) := by
  have hi : (BitVec.ofNat 64 n).toNat < scr.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hn
  have h := c0_store_fid_scr (i := BitVec.ofNat 64 n) v hi hm
  change storeOk m i32 (c.pScratchBuf + BitVec.ofNat 64 n * 4) ∧
    (FullMem c (FidP6Scr s (scr.set (BitVec.ofNat 64 n).toNat v)) ⋆ R)
      (storeMem m i32 (c.pScratchBuf + BitVec.ofNat 64 n * 4) v) at h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
  exact h

end FidK6cTactics

open FidK6cTactics

/-! ## Pure arithmetic, `tmk`, mask, entry, and `FidK6BufOk` helpers -/

/-- Bijection between `wsort[0..nv)` and non-zero entries of `tarjan_mark[0..cur_vars)`. -/
def FidK6cTmkReg (nv cur_vars : Nat) (exp tmk : List (BitVec 32)) : Prop :=
  nv ≤ 2 * cur_vars ∧
  (∀ i, i < nv → (exp[i]?.getD 0#32).toNat < cur_vars ∧
    (tmk[(exp[i]?.getD 0#32).toNat]?.getD 0#32).toNat = i + 1) ∧
  (∀ v, v < cur_vars → tmk[v]?.getD 0#32 ≠ 0#32 →
    ∃ i, i < nv ∧ (exp[i]?.getD 0#32).toNat = v ∧
      (tmk[v]?.getD 0#32).toNat = i + 1)

theorem fid_k6c_tmkReg_init (cur_vars : Nat) (exp tmk : List (BitVec 32))
    (h0 : ∀ v, v < cur_vars → tmk[v]?.getD 0#32 = 0#32) :
    FidK6cTmkReg 0 cur_vars exp tmk :=
  ⟨Nat.zero_le _, fun _ hi => absurd hi (Nat.not_lt_zero _),
   fun v hv hne => absurd (h0 v hv) hne⟩

theorem fid_k6c_tmkReg_step {nv cur_vars v : Nat} {exp tmk : List (BitVec 32)}
    (hreg : FidK6cTmkReg nv cur_vars exp tmk) (hnv : nv < 2 * cur_vars)
    (hv : v < cur_vars) (hz : tmk[v]?.getD 0#32 = 0#32)
    (hexp : exp.length = 2 * cur_vars ∨ nv < exp.length)
    (htmk : v < tmk.length) (hcv : 2 * cur_vars < 2 ^ 30) :
    FidK6cTmkReg (nv + 1) cur_vars
      (exp.set nv (BitVec.ofNat 32 v))
      (tmk.set v (BitVec.ofNat 32 (nv + 1))) := by
  have hexplen : nv < exp.length := by rcases hexp with h | h <;> omega
  have hnv1 : nv + 1 < 2 ^ 32 := by omega
  have hv32 : v < 2 ^ 32 := by omega
  refine ⟨by omega, ?_, ?_⟩
  · intro i hi
    by_cases hin : i < nv
    · have hexpi := hreg.2.1 i hin
      have hne : (exp[i]?.getD 0#32).toNat ≠ v := by
        intro heq; have hnz := hexpi.2; rw [heq, hz] at hnz; simp at hnz
      have he1 : ((exp.set nv (BitVec.ofNat 32 v))[i]?.getD 0#32).toNat =
          (exp[i]?.getD 0#32).toNat := by simp [List.getElem?_set_ne (by omega : nv ≠ i)]
      rw [he1]
      have ht1 :
          ((tmk.set v (BitVec.ofNat 32 (nv + 1)))[(exp[i]?.getD 0#32).toNat]?.getD 0#32).toNat =
          (tmk[(exp[i]?.getD 0#32).toNat]?.getD 0#32).toNat := by
        simp [List.getElem?_set_ne (Ne.symm hne)]
      rw [ht1]; exact hexpi
    · have hieq : i = nv := by omega
      subst hieq
      simp [hexplen, htmk, Nat.mod_eq_of_lt hv32, Nat.mod_eq_of_lt hnv1, hv]
  · intro x hx hnz
    by_cases hxv : x = v
    · subst hxv; refine ⟨nv, by omega, ?_, ?_⟩
      · simp [hexplen, Nat.mod_eq_of_lt hv32]
      · simp [htmk, Nat.mod_eq_of_lt hnv1]
    · have ht1 : (tmk.set v (BitVec.ofNat 32 (nv + 1)))[x]? = tmk[x]? :=
        List.getElem?_set_ne (Ne.symm hxv)
      rw [ht1] at hnz
      rcases hreg.2.2 x hx hnz with ⟨i, hi, hexi, hti⟩
      refine ⟨i, by omega, ?_, ?_⟩
      · have : (exp.set nv (BitVec.ofNat 32 v))[i]? = exp[i]? :=
          List.getElem?_set_ne (by omega : nv ≠ i)
        simpa [this] using hexi
      · simpa [ht1] using hti

theorem fid_k6c_tmkReg_bound {nv cur_vars v : Nat} {exp tmk : List (BitVec 32)}
    (hreg : FidK6cTmkReg nv cur_vars exp tmk) (hv : v < cur_vars)
    (ht : v < tmk.length) (hnz : tmk[v] ≠ 0#32) :
    ∃ i, i < nv ∧ (tmk[v]).toNat = i + 1 := by
  have hnz' : tmk[v]?.getD 0#32 ≠ 0#32 := by simpa [List.getElem?_eq_getElem ht] using hnz
  rcases hreg.2.2 v hv hnz' with ⟨i, hi, _, hti⟩
  exact ⟨i, hi, by simpa [List.getElem?_eq_getElem ht] using hti⟩

/-- Partial-clearing invariant for `for (i = k; i < nv; i++) tmk[exp[i]] = 0;`. -/
def FidK6cTmkClearInv (k nv cur_vars : Nat) (exp tmk : List (BitVec 32)) : Prop :=
  k ≤ nv ∧
  (∀ i, k ≤ i → i < nv → (exp[i]?.getD 0#32).toNat < cur_vars ∧
    (tmk[(exp[i]?.getD 0#32).toNat]?.getD 0#32).toNat = i + 1) ∧
  (∀ v, v < cur_vars → tmk[v]?.getD 0#32 ≠ 0#32 →
    ∃ i, k ≤ i ∧ i < nv ∧ (exp[i]?.getD 0#32).toNat = v ∧
      (tmk[v]?.getD 0#32).toNat = i + 1)

theorem fid_k6c_tmkClear_init {nv cur_vars : Nat} {exp tmk : List (BitVec 32)}
    (hreg : FidK6cTmkReg nv cur_vars exp tmk) :
    FidK6cTmkClearInv 0 nv cur_vars exp tmk :=
  ⟨Nat.zero_le _, fun i _ hi => hreg.2.1 i hi,
   fun v hv hnz => by
     rcases hreg.2.2 v hv hnz with ⟨i, hi, hx, ht⟩
     exact ⟨i, Nat.zero_le _, hi, hx, ht⟩⟩

theorem fid_k6c_tmkClear_step {k nv cur_vars : Nat} {exp tmk : List (BitVec 32)}
    (hinv : FidK6cTmkClearInv k nv cur_vars exp tmk) (hk : k < nv)
    (hexp : k < exp.length) (htmk : cur_vars ≤ tmk.length) :
    FidK6cTmkClearInv (k + 1) nv cur_vars exp
      (tmk.set (exp[k]).toNat 0#32) := by
  have hkinfo := hinv.2.1 k (Nat.le_refl k) hk
  have hkget : exp[k]?.getD 0#32 = exp[k] := by simp [List.getElem?_eq_getElem hexp]
  rw [hkget] at hkinfo
  have hklt : (exp[k]).toNat < tmk.length := by omega
  refine ⟨by omega, ?_, ?_⟩
  · intro i hki hi
    have hiinfo := hinv.2.1 i (by omega) hi
    refine ⟨hiinfo.1, ?_⟩
    have hne : (exp[k]).toNat ≠ (exp[i]?.getD 0#32).toNat := by
      intro heq; have h2 := hiinfo.2; rw [← heq, hkinfo.2] at h2; omega
    simpa [List.getElem?_set_ne hne] using hiinfo.2
  · intro v hv hnz
    have hnev : (exp[k]).toNat ≠ v := by
      intro heq; subst heq
      have hset : (tmk.set (exp[k]).toNat 0#32)[(exp[k]).toNat]? = some 0#32 :=
        List.getElem?_set_self hklt
      simp [hset] at hnz
    rw [List.getElem?_set_ne hnev] at hnz
    rcases hinv.2.2 v hv hnz with ⟨i, hki, hi, hexi, hti⟩
    have hki' : k + 1 ≤ i := by
      by_cases hkeq : i = k
      · subst hkeq; rw [hkget] at hexi; exact absurd hexi hnev
      · omega
    exact ⟨i, hki', hi, hexi, by simpa [List.getElem?_set_ne hnev] using hti⟩

theorem fid_k6c_tmkClear_done {nv cur_vars : Nat} {exp tmk : List (BitVec 32)}
    (hinv : FidK6cTmkClearInv nv nv cur_vars exp tmk) :
    ∀ v, v < cur_vars → tmk[v]?.getD 0#32 = 0#32 := by
  intro v hv
  by_cases hz : tmk[v]?.getD 0#32 = 0#32
  · exact hz
  · rcases hinv.2.2 v hv hz with ⟨i, h1, h2, _, _⟩; omega

theorem fid_k6c_mask_widx {mbase eid : BitVec 32}
    (hm : mbase = 4002#32 ∨ mbase = 4066#32) (heid : eid.toNat < 2001) :
    let widx := mbase + (eid >>> 5)
    4002 ≤ widx.toNat ∧ widx.toNat < 4130 ∧
      widx.setWidth 64 = BitVec.ofNat 64 widx.toNat := by
  have hsh : (eid >>> 5).toNat = eid.toNat / 32 := by bv_omega
  have h0 : (4002#32 : BitVec 32).toNat = 4002 := rfl
  have h1 : (4066#32 : BitVec 32).toNat = 4066 := rfl
  have hbv : (mbase + (eid >>> 5)).toNat = mbase.toNat + eid.toNat / 32 := by
    rcases hm with rfl | rfl <;> bv_omega
  have hlo : 4002 ≤ (mbase + (eid >>> 5)).toNat := by
    rcases hm with rfl | rfl <;> omega
  have hhi : (mbase + (eid >>> 5)).toNat < 4130 := by
    rcases hm with rfl | rfl <;> omega
  refine ⟨hlo, hhi, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

theorem fid_k6c_add1_toNat {x : BitVec 32} {lim : Nat}
    (hx : x.toNat < lim) (hl : lim < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 :=
  m8_bv32_add1_toNat hx hl

theorem fid_k6c_bv32_shl1_add1_lt {x : BitVec 32} {n : Nat}
    (hx : x.toNat < n) (hn : 2 * n + 1 < 2 ^ 30) :
    (x <<< 1).toNat = 2 * x.toNat ∧
    (x <<< 1 ||| 1#32).toNat = 2 * x.toNat + 1 :=
  ⟨m8_bv32_shl1_toNat (by omega), m8_bv32_shl1_or1_toNat (by omega)⟩

theorem fid_k6c_eid_bits {side eid : BitVec 32}
    (hs : side = 0#32 ∨ side = 1#32) (he : eid.toNat < 2001) :
    let raw := (side <<< 11) ||| eid
    raw.toNat < 4096 ∧
    (raw &&& 2047#32).toNat = eid.toNat ∧
    (raw >>> 11 = 0#32 ↔ side = 0#32) ∧
    (raw &&& 2047#32) = eid := by
  have hlt11 : eid.toNat < 2 ^ 11 := by omega
  have hmask : ∀ r : BitVec 32, (r &&& 2047#32).toNat = r.toNat % 2048 := fun r => by
    rw [BitVec.toNat_and, show (2047#32 : BitVec 32).toNat = 2 ^ 11 - 1 by decide]
    exact Nat.and_two_pow_sub_one_eq_mod r.toNat 11
  have heid_m : eid &&& 2047#32 = eid := BitVec.eq_of_toNat_eq (by
    rw [hmask, Nat.mod_eq_of_lt hlt11])
  have heid_s : eid >>> 11 = 0#32 := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt11]
    rfl)
  rcases hs with rfl | rfl
  · have hz : (0#32 <<< 11 ||| eid) = eid := by simp [BitVec.zero_shiftLeft]
    rw [hz]
    exact ⟨by omega, by rw [heid_m], ⟨fun _ => rfl, fun _ => heid_s⟩, heid_m⟩
  · rw [show (1#32 <<< 11) = 2048#32 by decide]
    have hlt4k : (2048#32 ||| eid).toNat < 4096 := by
      rw [BitVec.toNat_or, show (2048#32 : BitVec 32).toNat = 2048 by decide]
      exact Nat.or_lt_two_pow (by decide : 2048 < 2 ^ 12) (by omega : eid.toNat < 2 ^ 12)
    have hm : (2048#32 ||| eid) &&& 2047#32 = eid := by
      rw [BitVec.and_or_distrib_right]
      have h0 : (2048#32 &&& 2047#32) = 0#32 := by decide
      rw [h0, heid_m, BitVec.zero_or]
    have hshr : (2048#32 ||| eid) >>> 11 ≠ 0#32 := by
      have : ((2048#32 ||| eid) >>> 11) = (2048#32 >>> 11) ||| (eid >>> 11) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, BitVec.toNat_or, BitVec.toNat_or,
          BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight]
        exact Nat.shiftRight_or_distrib
      rw [this, heid_s, show (2048#32 >>> 11) = 1#32 by decide]
      decide
    exact ⟨hlt4k, by rw [hm], ⟨fun h => absurd h hshr, fun h => by cases h⟩, hm⟩

theorem fid_k6c_entry_bin_bounds {F_cur : List (List Nat)} {s : FullState}
    {lit : Nat} {w : BitVec 32}
    (he : FullBveEntryOkW F_cur s lit w) (hbin : w &&& 2147483648#32 ≠ 0#32) :
    (w &&& 2147483647#32).toNat < 2 * s.core.cur_vars ∧
    (w &&& 2147483647#32).toNat / 2 < s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [lit, (w &&& 2147483647#32).toNat]) := by
  rw [FullBveEntryOkW] at he
  rw [ite_eq_left_iff.mpr (fun h => absurd hbin h)] at he
  exact ⟨he.1, by omega, he.2⟩

theorem fid_k6c_entry_large_bounds {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {lit : Nat} {w : BitVec 32}
    (hl : s.LengthsOk c) (ha : FullArenaClausesInv c F_cur s.core)
    (he : FullBveEntryOkW F_cur s lit w) (hnbin : w &&& 2147483648#32 = 0#32) :
    w.toNat + 3 ≤ s.core.arena_len ∧
    3 ≤ fullArenaClauseSizeCore s.core w.toNat ∧
    w.toNat + 3 + fullArenaClauseSizeCore s.core w.toNat ≤ s.core.arena_len ∧
    s.core.arena_len ≤ c.arena_cap ∧
    (∀ k, k < fullArenaClauseSizeCore s.core w.toNat →
      w.toNat + 3 + k < s.core.arena.length ∧
      (s.core.arena[w.toNat + 3 + k]?.getD 0#32).toNat < 2 * s.core.cur_vars) := by
  have hc : ¬ (w &&& 2147483648#32 ≠ 0#32) := by simp [hnbin]
  dsimp only [FullBveEntryOkW] at he
  simp only [hc, ite_false] at he
  have hw := ha.refs_wf w.toNat he.1
  have hlits := ha.lits_lt w.toNat he.1 he.2
  have harlen : s.core.arena_len ≤ c.arena_cap := hl.core_ok.arena_len_le
  have harlen2 : s.core.arena.length = c.arena_cap := hl.core_ok.arena_len_arr
  refine ⟨hw.1, hw.2.1, by omega, harlen, ?_⟩
  intro k hk
  have hklen : w.toNat + 3 + k < s.core.arena.length := by omega
  refine ⟨hklen, ?_⟩
  have hmem : (s.core.arena[w.toNat + 3 + k]?.getD 0#32).toNat ∈
      fullArenaClauseLitsCore s.core w.toNat := by
    simp only [fullArenaClauseLitsCore, List.mem_map]
    refine ⟨s.core.arena[w.toNat + 3 + k], ?_, ?_⟩
    · have hk' : k < List.length (List.take (fullArenaClauseSizeCore s.core w.toNat)
          (List.drop (w.toNat + 3) s.core.arena)) := by
        simp [List.length_take, List.length_drop]; omega
      have : (List.take (fullArenaClauseSizeCore s.core w.toNat)
          (List.drop (w.toNat + 3) s.core.arena))[k] =
          s.core.arena[w.toNat + 3 + k] := by
        simp [List.getElem_take, List.getElem_drop, Nat.add_assoc]
      rw [← this]
      exact List.getElem_mem hk'
    · simp [List.getElem?_eq_getElem hklen]
  exact hlits _ hmem

/-- Clause invariants held in scratch buffer before `init_solve`. -/
def FidK6cClsOk (mv_nat nc_n alen_n n_units_n : Nat)
    (scr : List (BitVec 32)) : Prop :=
  nc_n ≤ 4 * mv_nat ∧
  (∀ cid, cid < nc_n →
    let off := (scr[4224 + 29 * mv_nat + cid]?.getD 0#32).toNat
    let cm := scr[4224 + 33 * mv_nat + cid]?.getD 0#32
    let aux := scr[4224 + 37 * mv_nat + cid]?.getD 0#32
    let sz := (cm &&& 65535#32).toNat
    off + sz ≤ alen_n ∧ (cm &&& 1073741824#32) = 0#32 ∧
      aux.toNat < 4096 ∧ (aux &&& 2047#32).toNat < 2001) ∧
  n_units_n ≤ nc_n

theorem fid_k6c_clsOk_empty (mv_nat : Nat) (scr : List (BitVec 32)) :
    FidK6cClsOk mv_nat 0 0 0 scr :=
  ⟨Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _), Nat.le_refl _⟩

theorem fid_k6c_clsOk_frame {mv_nat nc_n alen_n n_units_n : Nat}
    {scr scr' : List (BitVec 32)}
    (h : FidK6cClsOk mv_nat nc_n alen_n n_units_n scr)
    (hpre : ∀ idx, 4224 + 29 * mv_nat ≤ idx → idx < 4224 + 41 * mv_nat →
      scr'[idx]? = scr[idx]?) :
    FidK6cClsOk mv_nat nc_n alen_n n_units_n scr' := by
  refine ⟨h.1, fun cid hcid => ?_, h.2.2⟩
  have hnc_le := h.1
  have hc := h.2.1 cid hcid
  have h1 := hpre (4224 + 29 * mv_nat + cid) (by omega) (by omega)
  have h2 := hpre (4224 + 33 * mv_nat + cid) (by omega) (by omega)
  have h3 := hpre (4224 + 37 * mv_nat + cid) (by omega) (by omega)
  simpa [h1, h2, h3] using hc

theorem fid_k6c_bufOk_of_init {scr : List (BitVec 32)} {mv_s nc alen acap_s : BitVec 32}
    {cap : Nat}
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hcap : 4224 + 45 * mv_s.toNat + acap_s.toNat ≤ scr.length)
    (hlen_lt : scr.length < 2 ^ 30)
    (hscr4193 : scr[4193]? = some nc) (hscr4206 : scr[4206]? = some alen)
    (hscr4207 : scr[4207]? = some acap_s) (hscr4214 : scr[4214]? = some mv_s)
    (hnc : nc.toNat ≤ 4 * mv_s.toNat) (halen : alen.toNat ≤ acap_s.toNat)
    (hcls : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat cap scr) :
    FidK6BufOk scr := by
  dsimp only [FidK6BufOk]
  rw [hscr4214, hscr4193, hscr4206, hscr4207]
  simp only [Option.getD_some]
  refine ⟨hmv_lo, hmv_hi, hcap, hlen_lt, hnc, halen, ?_⟩
  intro cid hcid
  have hc := hcls.2.1 cid hcid
  refine ⟨by omega, fun hlrn => absurd hc.2.1 hlrn⟩

theorem fid_k6c_bufOk_watch_frame {scr scr' : List (BitVec 32)} {mv : Nat}
    (hok : FidK6BufOk scr) (hscr' : scr'.length = scr.length)
    (hmv : mv = (scr[4214]?.getD 0#32).toNat)
    (hagree : ∀ idx, idx < scr.length → idx < 4224 + 11 * mv ∨ 4224 + 29 * mv ≤ idx →
      scr'[idx]? = scr[idx]?) :
    FidK6BufOk scr' := by
  subst hmv
  apply fidK6BufOk_of_frame hok hscr'
  intro idx hidx
  dsimp only
  intro hregion
  have hmv_lo := hok.mv_lo
  apply hagree idx hidx
  rcases hregion with rfl | rfl | rfl | rfl | ⟨h1, _⟩
  · left; omega
  · left; omega
  · left; omega
  · left; omega
  · right; exact h1

/-! ## Sub-phase 1: `watch_solve` (`watch` loop + `solve` + `core` + bitmask) -/

/-- Watch-solve sub-program theorem for `full_k6_extract_and_solve_fid`. -/
theorem fid_k6c_watch_solve_wp {Γ : Env}
    (hwatch : ∀ a m Q X, fidK6WatchSpec a m Q X →
      Γ "full_k6_watch_fid" [i64, i32, i32, i32, i32] [] a m Q X)
    (hsolve : ∀ a m Q X, fidK6SolveSpec a m Q X →
      Γ "full_k6_solve_fid" [i64, i32] [i64] a m Q X)
    (hcore : ∀ a m Q X, fidK6CoreSpec a m Q X →
      Γ "full_k6_core_fid" [i64] [] a m Q X)
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [Ty.bool]} {X : XPost}
    {scr scr0 : List (BitVec 32)} {nc tick_lim : BitVec 32}
    {mv_s o_cl_off o_cl_meta o_cl_aux o_arena : BitVec 32}
    (hinv : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s) (hcap : 16384 ≤ c.scratch_cap)
    (hscr_len : scr.length = c.scratch_cap)
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hoff_off : o_cl_off = 4224#32 + 29#32 * mv_s)
    (hoff_meta : o_cl_meta = 4224#32 + 33#32 * mv_s)
    (hoff_aux : o_cl_aux = 4224#32 + 37#32 * mv_s)
    (hoff_ar : o_arena = 4224#32 + 45#32 * mv_s)
    (hok : FidK6BufOk scr)
    (hscr4193 : scr[4193]? = some nc) (hscr4194 : scr[4194]? = some nc)
    (hscr4214 : scr[4214]? = some mv_s)
    (haux_ok : ∀ cid, cid < nc.toNat →
      let raw := scr[4224 + 37 * mv_s.toNat + cid]?.getD 0#32
      raw.toNat < 4096 ∧ (raw &&& 2047#32).toNat < 2001)
    (hpre0 : ∀ i, i < 4002 → scr[i]? = scr0[i]?)
    (hpre1 : ∀ i, 4132 ≤ i → i < 4192 → scr[i]? = scr0[i]?)
    (hm : (FullMem c (FidP6Scr s scr) ⋆ R) m)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i, i < 4002 → s'.scratch.scratch_buf[i]? = scr0[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → s'.scratch.scratch_buf[i]? = scr0[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X
      (Expr.group
        (fun Js : Tup Cont [[i32]] => Blocks.cons (fun p : Tup Val [i32] =>
          Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var p.fst, Arg.var nc, ()))
            fun p_1 =>
          Expr.jnz (Arg.var p_1.fst)
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_meta, Arg.var p.fst, ())) fun p_2 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_2.fst, ())) fun p_3 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_3.fst, Arg.imm 4, ())) fun p_4 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_4.fst, ()))
              fun p_5 =>
            Expr.load i32 (Arg.var p_5.fst) fun ld =>
            Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld, Arg.imm 65535, ())) fun p_6 =>
            Expr.group (fun _ : Tup Cont [[]] => Blocks.cons (fun _ =>
              Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.fst, Arg.imm 1, ())) fun p_7 =>
              Expr.jump Js.fst (Arg.var p_7.fst, ())) Blocks.nil) fun Js_1 =>
            Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl) (Arg.var p_6.fst, Arg.imm 2, ()))
              fun p_7 =>
            Expr.jnz (Arg.var p_7.fst)
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_off, Arg.var p.fst, ())) fun p_8 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_8.fst, ())) fun p_9 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_9.fst, Arg.imm 4, ())) fun p_10 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_10.fst, ()))
                fun p_11 =>
              Expr.load i32 (Arg.var p_11.fst) fun ld_1 =>
              Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_arena, Arg.var ld_1, ())) fun p_12 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_12.fst, ())) fun p_13 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_13.fst, Arg.imm 4, ())) fun p_14 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_14.fst, ()))
                fun p_15 =>
              Expr.load i32 (Arg.var p_15.fst) fun ld_2 =>
              Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_arena, Arg.var ld_1, ())) fun p_16 =>
              Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p_16.fst, Arg.imm 1, ())) fun p_17 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_17.fst, ())) fun p_18 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_18.fst, Arg.imm 4, ())) fun p_19 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_19.fst, ()))
                fun p_20 =>
              Expr.load i32 (Arg.var p_20.fst) fun ld_3 =>
              Expr.call (as := [i64, i32, i32, i32, i32]) (bs := []) "full_k6_watch_fid"
                (Arg.var c.hdr, Arg.var p.fst, Arg.var ld_2, Arg.var ld_3, Arg.var p_6.fst, ())
                fun _ : Tup Val [] => Expr.jump Js_1.fst ())
              (Expr.jump Js_1.fst ()))
            (Expr.call (as := [i64, i32]) (bs := [i64]) "full_k6_solve_fid"
              (Arg.var c.hdr, Arg.var tick_lim, ()) fun ret : Tup Val [i64] =>
            Expr.let_ (Op.mk (OpCode.cmp .ne i64 .bool rfl) (Arg.var ret.fst, Arg.imm 20, ()))
              fun p_2 =>
            Expr.jnz (Arg.var p_2.fst) (Expr.ret (Arg.imm false, ()))
              (Expr.call (as := [i64]) (bs := []) "full_k6_core_fid" (Arg.var c.hdr, ())
                fun _ : Tup Val [] =>
              Expr.group (fun Js_1 : Tup Cont [[i32]] => Blocks.cons (fun pz : Tup Val [i32] =>
                Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pz.fst, Arg.imm 128, ()))
                  fun p_3 =>
                Expr.jnz (Arg.var p_3.fst)
                  (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 4002, Arg.var pz.fst, ()))
                    fun p_4 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_4.fst, ())) fun p_5 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_5.fst, Arg.imm 4, ())) fun p_6 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_6.fst, ()))
                    fun p_7 =>
                  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_7.fst)
                    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pz.fst, Arg.imm 1, ()))
                      fun p_8 => Expr.jump Js_1.fst (Arg.var p_8.fst, ())))
                  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4194, ())) fun p_4 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_4.fst, Arg.imm 4, ())) fun p_5 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_5.fst, ()))
                    fun p_6 =>
                  Expr.load i32 (Arg.var p_6.fst) fun onc =>
                  Expr.group (fun Js_2 : Tup Cont [[i32, Ty.bool]] =>
                    Blocks.cons (fun pc : Tup Val [i32, Ty.bool] =>
                      Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl)
                        (Arg.var pc.fst, Arg.var onc, ())) fun p_7 =>
                      Expr.jnz (Arg.var p_7.fst)
                        (Expr.group (fun _ : Tup Cont [[Ty.bool]] =>
                          Blocks.cons (fun pn : Tup Val [Ty.bool] =>
                            Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pc.fst, Arg.imm 1, ()))
                              fun p_8 => Expr.jump Js_2.fst (Arg.var p_8.fst, Arg.var pn.fst, ()))
                            Blocks.nil) fun Js_3 =>
                        Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_meta, Arg.var pc.fst, ()))
                          fun p_8 =>
                        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_8.fst, ())) fun p_9 =>
                        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_9.fst, Arg.imm 4, ()))
                          fun p_10 =>
                        Expr.let_ (Op.mk (OpCode.add i64)
                          (Arg.var c.pScratchBuf, Arg.var p_10.fst, ())) fun p_11 =>
                        Expr.load i32 (Arg.var p_11.fst) fun cm =>
                        Expr.let_ (Op.mk (OpCode.and i32) (Arg.var cm, Arg.imm 2147483648, ()))
                          fun p_12 =>
                        Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl)
                          (Arg.var p_12.fst, Arg.imm 0, ())) fun p_13 =>
                        Expr.jnz (Arg.var p_13.fst)
                          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_aux, Arg.var pc.fst, ()))
                            fun p_14 =>
                          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_14.fst, ())) fun p_15 =>
                          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_15.fst, Arg.imm 4, ()))
                            fun p_16 =>
                          Expr.let_ (Op.mk (OpCode.add i64)
                            (Arg.var c.pScratchBuf, Arg.var p_16.fst, ())) fun p_17 =>
                          Expr.load i32 (Arg.var p_17.fst) fun raw =>
                          Expr.let_ (Op.mk (OpCode.and i32) (Arg.var raw, Arg.imm 2047, ()))
                            fun eid =>
                          Expr.group (fun _ : Tup Cont [[i32]] => Blocks.cons (fun pm =>
                            Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var eid.fst, Arg.imm 5, ()))
                              fun p_18 =>
                            Expr.let_ (Op.mk (OpCode.add i32)
                              (Arg.var pm.fst, Arg.var p_18.fst, ())) fun p_19 =>
                            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_19.fst, ()))
                              fun p_20 =>
                            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_20.fst, Arg.imm 4, ()))
                              fun p_21 =>
                            Expr.let_ (Op.mk (OpCode.add i64)
                              (Arg.var c.pScratchBuf, Arg.var p_21.fst, ())) fun p_22 =>
                            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_19.fst, ())) fun p_23 =>
                            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_23.fst, Arg.imm 4, ()))
                              fun p_24 =>
                            Expr.let_ (Op.mk (OpCode.add i64)
                              (Arg.var c.pScratchBuf, Arg.var p_24.fst, ())) fun p_25 =>
                            Expr.load i32 (Arg.var p_25.fst) fun cur =>
                            Expr.let_ (Op.mk (OpCode.and i32) (Arg.var eid.fst, Arg.imm 31, ()))
                              fun p_26 =>
                            Expr.let_ (Op.mk (OpCode.shl i32) (Arg.imm 1, Arg.var p_26.fst, ()))
                              fun p_27 =>
                            Expr.let_ (Op.mk (OpCode.or i32) (Arg.var cur, Arg.var p_27.fst, ()))
                              fun p_28 =>
                            Expr.store (Arg.var p_28.fst) (Arg.var p_22.fst)
                              (Expr.jump Js_3.fst (Arg.imm true, ()))) Blocks.nil)
                          fun Js_4 =>
                          Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var raw, Arg.imm 11, ()))
                            fun p_18 =>
                          Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                            (Arg.var p_18.fst, Arg.imm 0, ())) fun p_19 =>
                          Expr.jnz (Arg.var p_19.fst)
                            (Expr.jump Js_4.fst (Arg.imm 4002, ()))
                            (Expr.jump Js_4.fst (Arg.imm 4066, ())))
                          (Expr.jump Js_3.fst (Arg.var pc.snd.fst, ())))
                        (Expr.group (fun _ : Tup Cont [[]] =>
                          Blocks.cons (fun _ => Expr.ret (Arg.var pc.snd.fst, ())) Blocks.nil)
                          fun Js_3 =>
                        Expr.jnz (Arg.var pc.snd.fst)
                          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4130, ())) fun p_8 =>
                          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_8.fst, Arg.imm 4, ()))
                            fun p_9 =>
                          Expr.let_ (Op.mk (OpCode.add i64)
                            (Arg.var c.pScratchBuf, Arg.var p_9.fst, ())) fun p_10 =>
                          Expr.store (t := i32) (Arg.imm 1) (Arg.var p_10.fst)
                            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4131, ())) fun p_11 =>
                            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_11.fst, Arg.imm 4, ()))
                              fun p_12 =>
                            Expr.let_ (Op.mk (OpCode.add i64)
                              (Arg.var c.pScratchBuf, Arg.var p_12.fst, ())) fun p_13 =>
                            Expr.store (t := i32) (Arg.imm 1) (Arg.var p_13.fst)
                              (Expr.jump Js_3.fst ())))
                          (Expr.jump Js_3.fst ()))) Blocks.nil)
                    fun Js_2 => Expr.jump Js_2.fst (Arg.imm 0, Arg.imm false, ())))
              Blocks.nil) fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0, ())))) Blocks.nil)
        fun Js => Expr.jump Js.fst (Arg.imm 0, ()))
      m := by
  have hscr_lt := hok.length_lt
  have hnc_le := hok.nc_le
  rw [hscr4193, hscr4214] at hnc_le
  simp only [Option.getD_some] at hnc_le
  have hmv_lt2 : mv_s.toNat < 2 ^ 30 := by omega
  apply wp_loop_inv
    (Inv := fun (p : BitVec 32 × Unit) m1 => ∃ scr1 : List (BitVec 32),
      p.1.toNat ≤ nc.toNat ∧ scr1.length = scr.length ∧ FidK6BufOk scr1 ∧
      (∀ idx, idx < scr.length →
        idx < 4224 + 11 * mv_s.toNat ∨ 4224 + 29 * mv_s.toNat ≤ idx →
        scr1[idx]? = scr[idx]?) ∧
      (FullMem c (FidP6Scr s scr1) ⋆ R) m1)
    (μ := fun (p : BitVec 32 × Unit) _ => nc.toNat - p.1.toNat)
  · intro J hJ
    c0_hsteps
    exact hJ _ _ ⟨scr, Nat.zero_le _, rfl, hok, fun _ _ _ => rfl, hm⟩
  · intro J p m1 ⟨scr1, hp_le, hlen1, hok1, hag1, hm1⟩ hcont
    dsimp only [Blocks.get, Member.here]
    have hscr1_4214 : scr1[4214]? = some mv_s := by
      rw [hag1 4214 (by omega) (by left; omega), hscr4214]
    have hscr1_4193 : scr1[4193]? = some nc := by
      rw [hag1 4193 (by omega) (by left; omega), hscr4193]
    have hscr1_4194 : scr1[4194]? = some nc := by
      rw [hag1 4194 (by omega) (by left; omega), hscr4194]
    have hbase1 : 4224 + 45 * mv_s.toNat ≤ scr1.length := by
      have := hok1.base_ge
      rw [hscr1_4214] at this; simp only [Option.getD_some] at this; exact this
    c0_hsteps
    · -- Watch loop body: `p.fst < nc`
      have hp_lt : p.fst.toNat < nc.toNat := by bv_omega
      have hp1_toNat : (p.fst + 1#32).toNat = p.fst.toNat + 1 :=
        fid_k6c_add1_toNat hp_lt (by omega)
      let idx_meta := (BitVec.setWidth 64 (o_cl_meta + p.fst)).toNat
      let idx_off := (BitVec.setWidth 64 (o_cl_off + p.fst)).toNat
      have hidx_meta : idx_meta = 4224 + 33 * mv_s.toNat + p.fst.toNat := by
        dsimp only [idx_meta]; rw [hoff_meta]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
      have hidx_meta_lt : idx_meta < scr1.length := by omega
      have hidx_off : idx_off = 4224 + 29 * mv_s.toNat + p.fst.toNat := by
        dsimp only [idx_off]; rw [hoff_off]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
      have hidx_off_lt : idx_off < scr1.length := by omega
      have hscr1_4207 : scr1[4207]? = some (scr1[4207]?.getD 0#32) := by
        have hlt4207 : 4207 < scr1.length := by omega
        simp [List.getElem?_eq_getElem hlt4207]
      have hcl := hok1.clause_ok (cid := p.fst.toNat)
      rw [hscr1_4193, hscr1_4214] at hcl
      simp only [Option.getD_some] at hcl
      have hcl_p := hcl hp_lt
      have hlen_ge1 := hok1.length_ge
      rw [hscr1_4214] at hlen_ge1
      simp only [Option.getD_some] at hlen_ge1
      c0_hsteps
      · -- `2 ≤ sz`
        have hsz_ge2 : 2 ≤ (scr1[idx_meta] &&& 65535#32).toNat := by
          have heq : idx_meta = (o_cl_meta.toNat + p.fst.toNat) % 2 ^ 32 := by
            dsimp only [idx_meta]; bv_omega
          have hmlt2 : (o_cl_meta.toNat + p.fst.toNat) % 2 ^ 32 < scr1.length := by
            rw [← heq]; exact hidx_meta_lt
          have hel : scr1[idx_meta] = scr1[(o_cl_meta.toNat + p.fst.toNat) % 2 ^ 32] :=
            Option.some.inj (by
              rw [← List.getElem?_eq_getElem hidx_meta_lt, ← List.getElem?_eq_getElem hmlt2, heq])
          have hmod :
              (scr1[(o_cl_meta.toNat + p.fst.toNat) % 2 ^ 32] &&& 65535#32).toNat =
              scr1[(o_cl_meta.toNat + p.fst.toNat) % 2 ^ 32].toNat % 65536 := by
            rw [BitVec.toNat_and, show (65535#32).toNat = 2 ^ 16 - 1 from rfl,
              Nat.and_two_pow_sub_one_eq_mod]
          rw [hel, hmod]
          exact ‹2 ≤ scr1[(o_cl_meta.toNat + p.fst.toNat) % 2 ^ 32].toNat % 65536›
        have hoff_val : scr1[idx_off].toNat +
            (scr1[idx_meta] &&& 65535#32).toNat ≤
            (scr1[4207]?.getD 0#32).toNat := by
          have h1 := hcl_p.1
          rw [← hidx_off, List.getElem?_eq_getElem hidx_off_lt, Option.getD_some,
            ← hidx_meta, List.getElem?_eq_getElem hidx_meta_lt, Option.getD_some] at h1
          exact h1
        have hacap_le : 4224 + 45 * mv_s.toNat + (scr1[4207]?.getD 0#32).toNat ≤ scr1.length :=
          hlen_ge1
        let idx_l0 := (BitVec.setWidth 64 (o_arena + scr1[idx_off])).toNat
        let idx_l1 := (BitVec.setWidth 64 (o_arena + scr1[idx_off] + 1#32)).toNat
        have hl0_idx : idx_l0 = 4224 + 45 * mv_s.toNat + scr1[idx_off].toNat := by
          dsimp only [idx_l0]; rw [hoff_ar]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
        have hl0_lt : idx_l0 < scr1.length := by omega
        have hl1_idx : idx_l1 = 4224 + 45 * mv_s.toNat + scr1[idx_off].toNat + 1 := by
          dsimp only [idx_l1]; rw [hoff_ar]
          exact fid_k6_off_add2 hmv_hi (by omega) (by bv_omega)
        have hl1_lt : idx_l1 < scr1.length := by omega
        c0_hsteps
        fid_call hwatch
        apply fidK6WatchSpec_intro (c := c) (s := FidP6Scr s scr1) (R := R) rfl
          (fidScr_lengthsOk hinv.1 (hlen1.trans hscr_len)) hok1 hm1
        intro scr2 m2 hlen2 hag2 hm2
        have hscr2_len : scr2.length = scr.length := hlen2.trans hscr_len.symm
        have hok2 : FidK6BufOk scr2 := fid_k6c_bufOk_watch_frame (mv := mv_s.toNat) hok1
          (hlen2.trans (hlen1.trans hscr_len).symm)
          (by rw [hscr1_4214]; rfl)
          (fun idx hidx hr => hag2 idx (by omega) (by rw [hscr1_4214]; simpa using hr))
        have hag2' : ∀ idx, idx < scr.length →
            idx < 4224 + 11 * mv_s.toNat ∨ 4224 + 29 * mv_s.toNat ≤ idx →
            scr2[idx]? = scr[idx]? := by
          intro idx hidx hr
          have heq := hag2 idx (by omega) (by rw [hscr1_4214]; simpa using hr)
          exact heq.trans (hag1 idx hidx hr)
        c0_hsteps
        refine hcont _ _ (by bv_omega)
          ⟨scr2, by bv_omega, hscr2_len, hok2, hag2', fid_k6c_scrBuf_split hm2⟩
      · -- `sz < 2`
        refine hcont _ _ (by bv_omega) ⟨scr1, by bv_omega, hlen1, hok1, hag1, hm1⟩
    · -- Exit watch loop -> `full_k6_solve_fid`
      have hp_eq : p.fst.toNat = nc.toNat := by bv_omega
      fid_call hsolve
      apply fidK6SolveSpec_intro (c := c) (s := FidP6Scr s scr1) (R := R) rfl
        (fidScr_lengthsOk hinv.1 (hlen1.trans hscr_len)) hok1
        (by rw [hscr1_4194, hscr1_4193]; exact Nat.le_refl _) hm1
      intro r2 scr2 fuel2 m2; dsimp only
      intro hok2 hlen2 hag2_lt h4194 h4214 hnc2 haux2 hfuel2 hm2
      let s2 : FullState :=
        { core := { s.core with fuel := fuel2 }
          scratch := { s.scratch with scratch_buf := scr2 } }
      have hm2' : (FullMem c (FidP6Scr s2 scr2) ⋆ R) m2 := fid_k6c_scrBuf_split hm2
      have hinv2 : FullDenseInvW c F0 F_cur s2 := m8_fullDenseInvW_scr_fuel hinv hlen2 fuel2
      have hscr2_len : scr2.length = c.scratch_cap := hlen2
      have hscr2_4194 : scr2[4194]? = some nc := by rw [h4194, hscr1_4194]
      have hscr2_4214 : scr2[4214]? = some mv_s := by rw [h4214, hscr1_4214]
      have hscr2_pre0 : ∀ i, i < 4002 → scr2[i]? = scr0[i]? := fun i hi => by
        rw [hag2_lt i (by omega), hag1 i (by omega) (by left; omega), hpre0 i hi]
      have hscr2_pre1 : ∀ i, 4132 ≤ i → i < 4192 → scr2[i]? = scr0[i]? := fun i h1 h2 => by
        rw [hag2_lt i (by omega), hag1 i (by omega) (by left; omega), hpre1 i h1 h2]
      have htmk2 : TmkZero s2 := htmk
      c0_hsteps
      · -- `r2 ≠ 20` -> return `false`
        exact hQ false s2 m2 hinv2 htmk2 rfl rfl rfl hfuel2 hscr2_pre0 hscr2_pre1 hm2
      · -- `r2 = 20` -> `full_k6_core_fid` + clear + mask
        fid_call hcore
        apply fidK6CoreSpec_intro (c := c) (s := FidP6Scr s2 scr2) (R := R) rfl
          (fidScr_lengthsOk hinv2.1 hscr2_len) hok2 hm2'
        intro scr3 m3 hlen3 hag3 hok3 hm3
        have hm3' : (FullMem c (FidP6Scr s2 scr3) ⋆ R) m3 := fid_k6c_scrBuf_split hm3
        have hscr3_4194 : scr3[4194]? = some nc := by
          have := hag3 4194 (by omega) (by rw [hscr2_4214]; left; omega)
          rw [this, hscr2_4194]
        have hscr3_4214 : scr3[4214]? = some mv_s := by
          have := hag3 4214 (by omega) (by rw [hscr2_4214]; left; omega)
          rw [this, hscr2_4214]
        have hscr3_pre0 : ∀ i, i < 4002 → scr3[i]? = scr0[i]? := fun i hi => by
          have := hag3 i (by omega) (by rw [hscr2_4214]; left; omega)
          rw [this, hscr2_pre0 i hi]
        have hscr3_pre1 : ∀ i, 4132 ≤ i → i < 4192 → scr3[i]? = scr0[i]? := fun i h1 h2 => by
          have := hag3 i (by omega) (by rw [hscr2_4214]; left; omega)
          rw [this, hscr2_pre1 i h1 h2]
        have hscr3_aux : ∀ cid, cid < nc.toNat →
            scr3[4224 + 37 * mv_s.toNat + cid]? = scr[4224 + 37 * mv_s.toNat + cid]? := by
          intro cid hcid
          have hlt3 : 4224 + 37 * mv_s.toNat + cid < c.scratch_cap := by
            have := hok3.base_ge
            rw [hscr3_4214, hlen3] at this
            simp only [Option.getD_some] at this
            omega
          have h3 := hag3 (4224 + 37 * mv_s.toNat + cid) hlt3
            (by rw [hscr2_4214]; simp only [Option.getD_some]; right; right; omega)
          have h2 := haux2 cid (by rw [hscr1_4194]; exact hcid)
          rw [hscr1_4214] at h2
          simp only [Option.getD_some] at h2
          have h1 := hag1 (4224 + 37 * mv_s.toNat + cid) (by omega) (by right; omega)
          rw [h3, h2, h1]
        -- Loop `J256`: clear `4002..4129`
        apply wp_loop_inv
          (Inv := fun (pz : BitVec 32 × Unit) mZ => ∃ scrZ : List (BitVec 32),
            pz.1.toNat ≤ 128 ∧ scrZ.length = c.scratch_cap ∧
            (∀ i, i < 4002 ∨ 4130 ≤ i → scrZ[i]? = scr3[i]?) ∧
            (FullMem c (FidP6Scr s2 scrZ) ⋆ R) mZ)
          (μ := fun (pz : BitVec 32 × Unit) _ => 128 - pz.1.toNat)
        · intro Jz hJz
          c0_hsteps
          exact hJz _ _ ⟨scr3, Nat.zero_le _, hlen3, fun _ _ => rfl, hm3'⟩
        · intro Jz pz mZ ⟨scrZ, hz_le, hlenZ, hagZ, hmZ⟩ hcontZ
          dsimp only [Blocks.get, Member.here]
          c0_hsteps
          · have hz_lt : pz.fst.toNat < 128 := by bv_omega
            let idxZ := (BitVec.setWidth 64 (4002#32 + pz.fst)).toNat
            have hidxZ : idxZ = 4002 + pz.fst.toNat := by dsimp only [idxZ]; bv_omega
            have hidxZ_lt : idxZ < scrZ.length := by omega
            c0_hsteps
            refine hcontZ _ _ (by bv_omega) ⟨scrZ.set idxZ 0#32, by bv_omega, by simp [hlenZ],
              fun i hi => by
                have hne : idxZ ≠ i := by omega
                rw [List.getElem?_set_ne hne, hagZ i hi],
              hm⟩
          · -- Exit `J256` -> load `4194`, run `J268` mask loop
            have hscrZ_4194 : scrZ[4194]? = some nc := by
              rw [hagZ 4194 (by right; omega), hscr3_4194]
            have hZ_4194 : 4194 < scrZ.length := by omega
            have hscrZ_4194_val : scrZ[OfNat.ofNat 4194 % 2 ^ 64] = nc := by
              have hg : scrZ[OfNat.ofNat 4194 % 2 ^ 64]? =
                  some scrZ[OfNat.ofNat 4194 % 2 ^ 64] :=
                List.getElem?_eq_getElem hZ_4194
              change scrZ[4194]? = some _ at hg
              rw [hscrZ_4194] at hg
              exact (Option.some.inj hg).symm
            c0_hsteps
            apply wp_loop_inv
              (Inv := fun (pc : BitVec 32 × Bool × Unit) mC => ∃ scrC : List (BitVec 32),
                pc.1.toNat ≤ nc.toNat ∧ scrC.length = c.scratch_cap ∧
                (∀ i, i < 4002 ∨ 4130 ≤ i → scrC[i]? = scr3[i]?) ∧
                (FullMem c (FidP6Scr s2 scrC) ⋆ R) mC)
              (μ := fun (pc : BitVec 32 × Bool × Unit) _ => nc.toNat - pc.1.toNat)
            · intro Jc hJc
              c0_hsteps
              exact hJc _ _ ⟨scrZ, Nat.zero_le _, hlenZ, hagZ, hmZ⟩
            · intro Jc pc mC ⟨scrC, hc_le, hlenC, hagC, hmC⟩ hcontC
              dsimp only [Blocks.get, Member.here]
              c0_hsteps
              · have hc_lt : pc.fst.toNat < nc.toNat := by
                  rw [← hscrZ_4194_val]; bv_omega
                have hmbase_C : 4224 + 45 * mv_s.toNat ≤ scrC.length := by
                  have := hok3.base_ge; rw [hscr3_4214, hlen3] at this
                  simp only [Option.getD_some] at this; omega
                let idxM := (BitVec.setWidth 64 (o_cl_meta + pc.fst)).toNat
                let idxA := (BitVec.setWidth 64 (o_cl_aux + pc.fst)).toNat
                have hidxM : idxM = 4224 + 33 * mv_s.toNat + pc.fst.toNat := by
                  dsimp only [idxM]; rw [hoff_meta]
                  exact fid_k6_off_add hmv_hi (by omega) (by omega)
                have hidxM_lt : idxM < scrC.length := by omega
                have hidxA : idxA = 4224 + 37 * mv_s.toNat + pc.fst.toNat := by
                  dsimp only [idxA]; rw [hoff_aux]
                  exact fid_k6_off_add hmv_hi (by omega) (by omega)
                have hidxA_lt : idxA < scrC.length := by omega
                have hraw_eq :
                    scrC[idxA] = scr[4224 + 37 * mv_s.toNat + pc.fst.toNat]?.getD 0#32 := by
                  have hg2 : scrC[4224 + 37 * mv_s.toNat + pc.fst.toNat]? = some scrC[idxA] := by
                    rw [← hidxA]; exact List.getElem?_eq_getElem hidxA_lt
                  rw [hagC _ (by right; omega), hscr3_aux pc.fst.toNat hc_lt] at hg2
                  exact congrArg (Option.getD · 0#32) hg2.symm
                have hraw_ok := haux_ok pc.fst.toNat hc_lt
                rw [← hraw_eq] at hraw_ok
                c0_hsteps
                · -- `KM_CORE` bit set, `raw >>> 11 = 0#32` (`4002`)
                  have hwi := fid_k6c_mask_widx (Or.inl rfl) hraw_ok.2
                  let widx0 := (BitVec.setWidth 64
                    (4002#32 + ((scrC[idxA] &&& 2047#32) >>> 5))).toNat
                  have hwi_lt : widx0 < scrC.length := by
                    dsimp only [widx0]; rw [hwi.2.2]; simp only [BitVec.toNat_ofNat]; omega
                  c0_hsteps
                  refine hcontC (pc.fst + 1#32, true, ()) _ (by bv_omega)
                    ⟨scrC.set widx0 _, by bv_omega,
                      by simp [hlenC], fun i hi => by
                        have hne : widx0 ≠ i := by
                          dsimp only [widx0]
                          rw [hwi.2.2]; simp only [BitVec.toNat_ofNat]; omega
                        rw [List.getElem?_set_ne hne, hagC i hi],
                      hm⟩
                · -- `KM_CORE` bit set, `raw >>> 11 ≠ 0#32` (`4066`)
                  have hwi := fid_k6c_mask_widx (Or.inr rfl) hraw_ok.2
                  let widx1 := (BitVec.setWidth 64
                    (4066#32 + ((scrC[idxA] &&& 2047#32) >>> 5))).toNat
                  have hwi_lt : widx1 < scrC.length := by
                    dsimp only [widx1]; rw [hwi.2.2]; simp only [BitVec.toNat_ofNat]; omega
                  c0_hsteps
                  refine hcontC (pc.fst + 1#32, true, ()) _ (by bv_omega)
                    ⟨scrC.set widx1 _, by bv_omega,
                      by simp [hlenC], fun i hi => by
                        have hne : widx1 ≠ i := by
                          dsimp only [widx1]
                          rw [hwi.2.2]; simp only [BitVec.toNat_ofNat]; omega
                        rw [List.getElem?_set_ne hne, hagC i hi],
                      hm⟩
                · -- `KM_CORE` bit not set
                  refine hcontC (pc.fst + 1#32, pc.snd.fst, ()) _ (by bv_omega)
                    ⟨scrC, by bv_omega, hlenC, hagC, hmC⟩
              · -- Exit `J268` -> `J303`, `found = true`: `4130 := 1`, `4131 := 1`
                have hlt4130 : (BitVec.setWidth 64 4130#32).toNat < scrC.length := by bv_omega
                have hlt4131 : (BitVec.setWidth 64 4131#32).toNat <
                    (scrC.set (BitVec.setWidth 64 4130#32).toNat 1#32).length := by
                  simp [hlenC]; omega
                c0_hsteps
                try rw [hc]
                let scrOut := (scrC.set 4130 1#32).set 4131 1#32
                have htmkOut : TmkZero (FidP6Scr s2 scrOut) := htmk2
                have hinvOut : FullDenseInvW c F0 F_cur (FidP6Scr s2 scrOut) :=
                  m8_fullDenseInvW_scr_fuel hinv (by simp [scrOut, hlenC]) fuel2
                exact hQ true (FidP6Scr s2 scrOut) _ hinvOut htmkOut rfl rfl rfl hfuel2
                  (fun i hi => by
                    dsimp only [FidP6Scr, scrOut]
                    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                    rw [hagC i (Or.inl hi), hscr3_pre0 i hi])
                  (fun i h1 h2 => by
                    dsimp only [FidP6Scr, scrOut]
                    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                    rw [hagC i (Or.inr (by omega)), hscr3_pre1 i h1 h2])
                  hm
              · -- Exit `J268` -> `J303`, `found = false`: return `false` directly
                try rw [hc]
                exact hQ false (FidP6Scr s2 scrC) _
                  (m8_fullDenseInvW_scr_fuel hinv hlenC fuel2)
                  htmk2 rfl rfl rfl hfuel2
                  (fun i hi => by rw [hagC i (Or.inl hi), hscr3_pre0 i hi])
                  (fun i h1 h2 => by rw [hagC i (Or.inr (by omega)), hscr3_pre1 i h1 h2])
                  hmC

/-! ## Sub-phase 2: `copy_clause` (`J428` tmp -> scr arena + metadata + `J453` unit) -/

private theorem fid_k6c_csz_mask {csz : BitVec 32} (h : csz.toNat ≤ 65535) :
    (csz &&& 65535#32) = csz ∧ (csz &&& 1073741824#32) = 0#32 := by
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show (65535#32 : BitVec 32).toNat = 2 ^ 16 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    bv_omega
  · apply BitVec.eq_of_toNat_eq
    apply Nat.eq_of_testBit_eq
    intro i
    rw [BitVec.toNat_and, show (1073741824#32 : BitVec 32).toNat = 2 ^ 30 from rfl,
      Nat.testBit_and, Nat.testBit_two_pow, BitVec.toNat_zero, Nat.zero_testBit]
    by_cases h30 : i = 30
    · subst h30; simp [Nat.testBit_lt_two_pow (by omega : csz.toNat < 2 ^ 30)]
    · simp [Ne.symm h30]

/-- Copy `tmp[0..csz)` into scratch arena and record clause metadata + optional unit index. -/
theorem fid_k6c_copy_clause_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {K_next : Cont [i32, i32, i32, i32, Ty.bool, i32]}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr : List (BitVec 32)}
    {mv_s o_cl_off o_cl_meta o_cl_aux o_units o_arena : BitVec 32}
    {nc alen n_units csz trivial_eid eid : BitVec 32} {abort_in : Bool} {acap_n : Nat}
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hcap : 4224 + 45 * mv_s.toNat + acap_n ≤ c.scratch_cap)
    (hscr_lt : scr.length < 2 ^ 30) (hscr_len : scr.length = c.scratch_cap)
    (htmp_len : tmp.length = c.max_vars)
    (hoff_off : o_cl_off = 4224#32 + 29#32 * mv_s)
    (hoff_meta : o_cl_meta = 4224#32 + 33#32 * mv_s)
    (hoff_aux : o_cl_aux = 4224#32 + 37#32 * mv_s)
    (hoff_units : o_units = 4224#32 + 41#32 * mv_s)
    (hoff_ar : o_arena = 4224#32 + 45#32 * mv_s)
    (hcsz_pos : 1 ≤ csz.toNat) (hcsz_max : csz.toNat ≤ c.max_vars)
    (hcsz_65k : csz.toNat ≤ 65535)
    (hnc_lt : nc.toNat < 2 * mv_s.toNat) (hn_units : n_units.toNat ≤ nc.toNat)
    (halen_le : alen.toNat + csz.toNat ≤ acap_n)
    (heid : eid.toNat < 4096 ∧ (eid &&& 2047#32).toNat < 2001)
    (hcls : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m)
    (hK : ∀ (scr' : List (BitVec 32)) (pu k_out : BitVec 32) (m' : Mem 64),
      scr'.length = c.scratch_cap →
      (∀ i, i < 4224 + 29 * mv_s.toNat → scr'[i]? = scr[i]?) →
      FidK6cClsOk mv_s.toNat (nc + 1#32).toNat (alen + csz).toNat pu.toNat scr' →
      pu.toNat = (if csz = 1#32 then n_units.toNat + 1 else n_units.toNat) →
      (FullMem c (FidP6Work s tmp wsort tmk scr') ⋆ R) m' →
      K_next (nc + 1#32, alen + csz, pu, trivial_eid, abort_in, k_out, ()) m') :
    wp Γ Q X
      (Expr.group (fun Js : Tup Cont [[i32]] => Blocks.cons (fun p : Tup Val [i32] =>
        Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var p.fst, Arg.var csz, ()))
          fun p_1 =>
        Expr.jnz (Arg.var p_1.fst)
          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_arena, Arg.var alen, ())) fun p_2 =>
          Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p_2.fst, Arg.var p.fst, ())) fun p_3 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_3.fst, ())) fun p_4 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_4.fst, Arg.imm 4, ())) fun p_5 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_5.fst, ()))
            fun p_6 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.fst, ())) fun p_7 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_7.fst, Arg.imm 4, ())) fun p_8 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTmp, Arg.var p_8.fst, ())) fun p_9 =>
          Expr.load i32 (Arg.var p_9.fst) fun ld =>
          Expr.store (Arg.var ld) (Arg.var p_6.fst)
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.fst, Arg.imm 1, ())) fun p_10 =>
            Expr.jump Js.fst (Arg.var p_10.fst, ())))
          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_off, Arg.var nc, ())) fun p_2 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_2.fst, ())) fun p_3 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_3.fst, Arg.imm 4, ())) fun p_4 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_4.fst, ()))
            fun p_5 =>
          Expr.store (t := i32) (Arg.var alen) (Arg.var p_5.fst)
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_meta, Arg.var nc, ())) fun p_6 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_6.fst, ())) fun p_7 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_7.fst, Arg.imm 4, ())) fun p_8 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_8.fst, ()))
              fun p_9 =>
            Expr.store (t := i32) (Arg.var csz) (Arg.var p_9.fst)
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_aux, Arg.var nc, ())) fun p_10 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_10.fst, ())) fun p_11 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_11.fst, Arg.imm 4, ())) fun p_12 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_12.fst, ()))
                fun p_13 =>
              Expr.store (t := i32) (Arg.var eid) (Arg.var p_13.fst)
                (Expr.group (fun _Js_1 : Tup Cont [[i32]] => Blocks.cons (fun pu : Tup Val [i32] =>
                  Expr.let_ (Op.mk (OpCode.add i32) (Arg.var nc, Arg.imm 1, ())) fun p_14 =>
                  Expr.let_ (Op.mk (OpCode.add i32) (Arg.var alen, Arg.var csz, ())) fun p_15 =>
                  Expr.jump K_next (Arg.var p_14.fst, Arg.var p_15.fst, Arg.var pu.fst,
                    Arg.var trivial_eid, Arg.var abort_in, Arg.var p.fst, ())) Blocks.nil)
                  fun Js_1 =>
                Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var csz, Arg.imm 1, ()))
                  fun p_14 =>
                Expr.jnz (Arg.var p_14.fst)
                  (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_units, Arg.var n_units, ()))
                    fun p_15 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_15.fst, ())) fun p_16 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_16.fst, Arg.imm 4, ())) fun p_17 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_17.fst, ()))
                    fun p_18 =>
                  Expr.store (t := i32) (Arg.var nc) (Arg.var p_18.fst)
                    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var n_units, Arg.imm 1, ()))
                      fun p_19 =>
                    Expr.jump Js_1.fst (Arg.var p_19.fst, ())))
                  (Expr.jump Js_1.fst (Arg.var n_units, ()))))))) Blocks.nil)
      fun Js => Expr.jump Js.fst (Arg.imm 0, ())) m := by
  have hnc_add : (nc + 1#32).toNat = nc.toNat + 1 :=
    fid_k6c_add1_toNat hnc_lt (by omega)
  have halen_add : (alen + csz).toNat = alen.toNat + csz.toNat := by bv_omega
  have hnu_add : (n_units + 1#32).toNat = n_units.toNat + 1 := by bv_omega
  apply wp_loop_inv
    (Inv := fun (p : BitVec 32 × Unit) m1 => ∃ scr1 : List (BitVec 32),
      p.1.toNat ≤ csz.toNat ∧ scr1.length = c.scratch_cap ∧
      (∀ i, i < 4224 + 45 * mv_s.toNat → scr1[i]? = scr[i]?) ∧
      (FullMem c (FidP6Work s tmp wsort tmk scr1) ⋆ R) m1)
    (μ := fun (p : BitVec 32 × Unit) _ => csz.toNat - p.1.toNat)
  · intro J hJ
    c0_hsteps
    exact hJ _ _ ⟨scr, Nat.zero_le _, hscr_len, fun _ _ => rfl, hm⟩
  · intro J p m1 ⟨scr1, hp_le, hlen1, hag1, hm1⟩ hcont
    dsimp only [Blocks.get, Member.here]
    c0_hsteps
    · -- Loop body: `p.fst < csz`
      have hp_lt : p.fst.toNat < csz.toNat := by bv_omega
      have hp_tmp : (BitVec.setWidth 64 p.fst).toNat < tmp.length := by bv_omega
      let idx_ar := (BitVec.setWidth 64 (o_arena + alen + p.fst)).toNat
      have hidx_ar : idx_ar = 4224 + 45 * mv_s.toNat + alen.toNat + p.fst.toNat := by
        dsimp only [idx_ar]; rw [hoff_ar]; exact fid_k6_off_add2 hmv_hi (by omega) (by omega)
      have hidx_ar_lt : idx_ar < scr1.length := by omega
      c0_hsteps
      refine hcont (p.fst + 1#32, ()) _ (by bv_omega)
        ⟨scr1.set idx_ar _, by bv_omega, by simp [hlen1],
          fun i hi => by
            have hne : idx_ar ≠ i := by omega
            rw [List.getElem?_set_ne hne, hag1 i hi],
          hm⟩
    · -- Exit loop -> store metadata & optional unit -> jump `K_next`
      have hhp_eq : p.fst.toNat = csz.toNat := by bv_omega
      have hcls1 : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr1 :=
        fid_k6c_clsOk_frame hcls fun idx h1 _ => hag1 idx (by omega)
      let iOff := (BitVec.setWidth 64 (o_cl_off + nc)).toNat
      let iMeta := (BitVec.setWidth 64 (o_cl_meta + nc)).toNat
      let iAux := (BitVec.setWidth 64 (o_cl_aux + nc)).toNat
      have hiOff : iOff = 4224 + 29 * mv_s.toNat + nc.toNat := by
        dsimp only [iOff]; rw [hoff_off]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
      have hiMeta : iMeta = 4224 + 33 * mv_s.toNat + nc.toNat := by
        dsimp only [iMeta]; rw [hoff_meta]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
      have hiAux : iAux = 4224 + 37 * mv_s.toNat + nc.toNat := by
        dsimp only [iAux]; rw [hoff_aux]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
      have hiOff_lt : iOff < scr1.length := by omega
      have hiMeta_lt : iMeta < (scr1.set iOff alen).length := by simp [hlen1]; omega
      have hiAux_lt : iAux < ((scr1.set iOff alen).set iMeta csz).length := by
        simp [hlen1]; omega
      have hmk_cls : ∀ (scrF : List (BitVec 32)) (pu_n : Nat),
          (∀ i, i < 4224 + 29 * mv_s.toNat → scrF[i]? = scr1[i]?) →
          (∀ j, 4224 + 29 * mv_s.toNat ≤ j → j < 4224 + 41 * mv_s.toNat →
            j ≠ iOff → j ≠ iMeta → j ≠ iAux → scrF[j]? = scr1[j]?) →
          scrF[iOff]? = some alen → scrF[iMeta]? = some csz → scrF[iAux]? = some eid →
          pu_n ≤ nc.toNat + 1 →
          FidK6cClsOk mv_s.toNat (nc + 1#32).toNat (alen + csz).toNat pu_n scrF := by
        intro scrF pu_n _ hf_rest hf_off hf_meta hf_aux hpu_le
        refine ⟨by omega, fun cid hcid => ?_, by omega⟩
        rw [hnc_add] at hcid
        by_cases heq : cid = nc.toNat
        · subst heq
          have hcm := fid_k6c_csz_mask hcsz_65k
          have ho1 : scrF[4224 + 29 * mv_s.toNat + nc.toNat]? = some alen := by
            simpa [hiOff] using hf_off
          have hm1' : scrF[4224 + 33 * mv_s.toNat + nc.toNat]? = some csz := by
            simpa [hiMeta] using hf_meta
          have ha1 : scrF[4224 + 37 * mv_s.toNat + nc.toNat]? = some eid := by
            simpa [hiAux] using hf_aux
          rw [ho1, hm1', ha1]
          simp only [Option.getD_some, hcm.1, hcm.2, halen_add]
          exact ⟨by omega, trivial, heid.1, heid.2⟩
        · have hc_old := hcls1.2.1 cid (by omega)
          have h1 := hf_rest (4224 + 29 * mv_s.toNat + cid) (by omega) (by omega)
            (by omega) (by omega) (by omega)
          have h2 := hf_rest (4224 + 33 * mv_s.toNat + cid) (by omega) (by omega)
            (by omega) (by omega) (by omega)
          have h3 := hf_rest (4224 + 37 * mv_s.toNat + cid) (by omega) (by omega)
            (by omega) (by omega) (by omega)
          dsimp only at hc_old ⊢
          rw [h1, h2, h3, halen_add]
          exact ⟨by omega, hc_old.2.1, hc_old.2.2.1, hc_old.2.2.2⟩
      c0_hsteps
      · -- `csz = 1#32`: store unit in `o_units + n_units`
        have hcsz_eq1 : csz = 1#32 := by bv_omega
        let scrS := ((scr1.set iOff alen).set iMeta csz).set iAux eid
        let iUn := (BitVec.setWidth 64 (o_units + n_units)).toNat
        have hiUn : iUn = 4224 + 41 * mv_s.toNat + n_units.toNat := by
          dsimp only [iUn]; rw [hoff_units]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
        have hiUn_lt : iUn < scrS.length := by simp [scrS, hlen1]; omega
        c0_hsteps
        let scrF := scrS.set iUn nc
        refine hK scrF (n_units + 1#32) p.fst _ (by simp [scrF, scrS, hlen1])
          (fun i hi => by
            dsimp only [scrF, scrS]
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hag1 i (by omega)])
          (hmk_cls scrF (n_units + 1#32).toNat
            (fun i hi => by
              dsimp only [scrF, scrS]
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
            (fun j _ _ hn1 hn2 hn3 => by
              dsimp only [scrF, scrS]
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne hn3.symm,
                List.getElem?_set_ne hn2.symm, List.getElem?_set_ne hn1.symm])
            (by dsimp only [scrF, scrS]
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                  List.getElem?_set_ne (by omega), List.getElem?_set_self hiOff_lt])
            (by dsimp only [scrF, scrS]
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                  List.getElem?_set_self hiMeta_lt])
            (by dsimp only [scrF, scrS]
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hiAux_lt])
            (by omega))
          (by simp [hcsz_eq1, hnu_add]) hm
      · -- `csz ≠ 1#32`: keep `n_units`
        have hcsz_ne1 : csz ≠ 1#32 := by bv_omega
        let scrF := ((scr1.set iOff alen).set iMeta csz).set iAux eid
        refine hK scrF n_units p.fst _ (by simp [scrF, hlen1])
          (fun i hi => by
            dsimp only [scrF]
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_ne (by omega), hag1 i (by omega)])
          (hmk_cls scrF n_units.toNat
            (fun i hi => by
              dsimp only [scrF]
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                List.getElem?_set_ne (by omega)])
            (fun j _ _ hn1 hn2 hn3 => by
              dsimp only [scrF]
              rw [List.getElem?_set_ne hn3.symm, List.getElem?_set_ne hn2.symm,
                List.getElem?_set_ne hn1.symm])
            (by dsimp only [scrF]
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                  List.getElem?_set_self hiOff_lt])
            (by dsimp only [scrF]
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hiMeta_lt])
            (by dsimp only [scrF]; rw [List.getElem?_set_self hiAux_lt])
            (by omega))
          (by simp [hcsz_ne1]) hm

/-! ## Sub-phase 3: `scan_large` (`J463` large clause literal extraction) -/

private theorem fid_k6c_bv64_cur_shl1 {cv : Nat} (hcv : cv < 2 ^ 30) :
    (BitVec.ofNat 64 cv <<< BitVec.signExtend 64 1#32).toNat = 2 * cv := by
  have h1 : BitVec.signExtend 64 1#32 = 1#64 := by decide
  rw [h1]
  have h2 : (BitVec.ofNat 64 cv <<< (1#64 : BitVec 64)) = BitVec.ofNat 64 cv <<< (1 : Nat) := rfl
  rw [h2, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- Scan large clause `arena[off+3 .. off+3+sz)` into `tmp[0..csz)` and register vars. -/
theorem fid_k6c_scan_large_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {K_done : Cont [i32, Ty.bool, Ty.bool, i32, i32]}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr : List (BitVec 32)}
    {mv_s max_csz lit off sz nv0 : BitVec 32} {abort_in : Bool}
    (hl : s.LengthsOk c)
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hmcsz : max_csz.toNat ≤ c.max_vars)
    (htmp_len : tmp.length = c.max_vars) (hw_len : wsort.length = 2 * c.max_vars)
    (htmk_len : tmk.length = 2 * c.max_vars)
    (hnv0_mv : nv0.toNat ≤ mv_s.toNat) (hnv0_cv : nv0.toNat ≤ 2 * s.core.cur_vars)
    (hsz_ar : off.toNat + 3 + sz.toNat ≤ s.core.arena.length)
    (hsz_lits : ∀ k, k < sz.toNat →
      (s.core.arena[off.toNat + 3 + k]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hreg0 : FidK6cTmkReg nv0.toNat s.core.cur_vars wsort tmk)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m)
    (hK : ∀ (nv' csz' j' : BitVec 32) (ab' sat' : Bool)
      (tmp' wsort' tmk' : List (BitVec 32)) (m' : Mem 64),
      tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
      tmk'.length = 2 * c.max_vars →
      nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ 2 * s.core.cur_vars →
      csz'.toNat ≤ max_csz.toNat →
      FidK6cTmkReg nv'.toNat s.core.cur_vars wsort' tmk' →
      (FullMem c (FidP6Work s tmp' wsort' tmk' scr) ⋆ R) m' →
      K_done (nv', ab', sat', csz', j', ()) m') :
    wp Γ Q X
      (Expr.group (fun Js : Tup Cont [[i32, i32, i32]] =>
        Blocks.cons (fun p : Tup Val [i32, i32, i32] =>
          Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl)
            (Arg.var p.snd.snd.fst, Arg.var sz, ())) fun p_1 =>
          Expr.jnz (Arg.var p_1.fst)
            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var off, ())) fun p_2 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_2.fst, Arg.imm 3, ())) fun p_3 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.snd.snd.fst, ())) fun p_4 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_3.fst, Arg.var p_4.fst, ())) fun p_5 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_5.fst, Arg.imm 4, ())) fun p_6 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pArena, Arg.var p_6.fst, ())) fun p_7 =>
            Expr.load i32 (Arg.var p_7.fst) fun ld =>
            Expr.group (fun _Js_1 : Tup Cont [[i32, Ty.bool, Ty.bool, i32]] =>
              Blocks.cons (fun pn : Tup Val [i32, Ty.bool, Ty.bool, i32] =>
                Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.snd.snd.fst, Arg.imm 1, ()))
                  fun p_8 =>
                Expr.jump Js.fst (Arg.var pn.fst, Arg.var pn.snd.snd.snd.fst, Arg.var p_8.fst,
                  ())) Blocks.nil) fun Js_1 =>
            Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl) (Arg.var ld, Arg.var lit, ()))
              fun p_8 =>
            Expr.jnz (Arg.var p_8.fst)
              (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld, ())) fun p_9 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pVals, Arg.var p_9.fst, ())) fun p_10 =>
              Expr.load i8 (Arg.var p_10.fst) fun lv =>
              Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_11 =>
              Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var lv, ())) fun p_12 =>
              Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_11.fst, ())) fun p_13 =>
              Expr.let_ (Op.mk (OpCode.cmp .sgt i32 .bool rfl)
                (Arg.var p_12.fst, Arg.var p_13.fst, ())) fun p_14 =>
              Expr.jnz (Arg.var p_14.fst)
                (Expr.jump K_done (Arg.var p.fst, Arg.var abort_in, Arg.imm true,
                  Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ()))
                (Expr.group (fun _Js_2 : Tup Cont [[i32, Ty.bool, i32]] =>
                  Blocks.cons (fun pm : Tup Val [i32, Ty.bool, i32] =>
                    Expr.jump Js_1.fst (Arg.var pm.fst, Arg.var pm.snd.fst, Arg.imm false,
                      Arg.var pm.snd.snd.fst, ())) Blocks.nil) fun Js_2 =>
                Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_15 =>
                Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var lv, ())) fun p_16 =>
                Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_15.fst, ())) fun p_17 =>
                Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                  (Arg.var p_16.fst, Arg.var p_17.fst, ())) fun p_18 =>
                Expr.jnz (Arg.var p_18.fst)
                  (Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var ld, Arg.imm 1, ())) fun v =>
                  Expr.group (fun _Js_3 : Tup Cont [[i32, Ty.bool]] =>
                    Blocks.cons (fun pw : Tup Val [i32, Ty.bool] =>
                      Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
                        (Arg.var p.snd.fst, Arg.var max_csz, ())) fun p_19 =>
                      Expr.jnz (Arg.var p_19.fst)
                        (Expr.jump K_done (Arg.var pw.fst, Arg.imm true, Arg.imm false,
                          Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ()))
                        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.snd.fst, ())) fun p_20 =>
                        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_20.fst, Arg.imm 4, ()))
                          fun p_21 =>
                        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTmp, Arg.var p_21.fst, ()))
                          fun p_22 =>
                        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var v.fst, ())) fun p_23 =>
                        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_23.fst, Arg.imm 4, ()))
                          fun p_24 =>
                        Expr.let_ (Op.mk (OpCode.add i64)
                          (Arg.var c.pTarjanMark, Arg.var p_24.fst, ())) fun p_25 =>
                        Expr.load i32 (Arg.var p_25.fst) fun cv =>
                        Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var cv, Arg.imm 1, ())) fun p_26 =>
                        Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var p_26.fst, Arg.imm 1, ()))
                          fun p_27 =>
                        Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld, Arg.imm 1, ())) fun p_28 =>
                        Expr.let_ (Op.mk (OpCode.or i32) (Arg.var p_27.fst, Arg.var p_28.fst, ()))
                          fun p_29 =>
                        Expr.store (Arg.var p_29.fst) (Arg.var p_22.fst)
                          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.snd.fst, Arg.imm 1, ()))
                            fun p_30 =>
                          Expr.jump Js_2.fst (Arg.var pw.fst, Arg.var pw.snd.fst,
                            Arg.var p_30.fst, ())))) Blocks.nil) fun Js_3 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var v.fst, ())) fun p_19 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_19.fst, Arg.imm 4, ())) fun p_20 =>
                  Expr.let_ (Op.mk (OpCode.add i64)
                    (Arg.var c.pTarjanMark, Arg.var p_20.fst, ())) fun p_21 =>
                  Expr.load i32 (Arg.var p_21.fst) fun tmv =>
                  Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var tmv, Arg.imm 0, ()))
                    fun p_22 =>
                  Expr.jnz (Arg.var p_22.fst)
                    (Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
                      (Arg.var p.fst, Arg.var mv_s, ())) fun p_23 =>
                    Expr.jnz (Arg.var p_23.fst)
                      (Expr.jump K_done (Arg.var p.fst, Arg.imm true, Arg.imm false,
                        Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ()))
                      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.fst, ())) fun p_24 =>
                      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 776, ()))
                        fun p_25 =>
                      Expr.load i64 (Arg.var p_25.fst) fun cv64 =>
                      Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 1, ())) fun p_26 =>
                      Expr.let_ (Op.mk (OpCode.shl i64) (Arg.var cv64, Arg.var p_26.fst, ()))
                        fun p_27 =>
                      Expr.let_ (Op.mk (OpCode.cmp .uge i64 .bool rfl)
                        (Arg.var p_24.fst, Arg.var p_27.fst, ())) fun p_28 =>
                      Expr.jnz (Arg.var p_28.fst)
                        (Expr.jump K_done (Arg.var p.fst, Arg.imm true, Arg.imm false,
                          Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ()))
                        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.fst, ())) fun p_29 =>
                        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_29.fst, Arg.imm 4, ()))
                          fun p_30 =>
                        Expr.let_ (Op.mk (OpCode.add i64)
                          (Arg.var c.pWsort, Arg.var p_30.fst, ())) fun p_31 =>
                        Expr.store (Arg.var v.fst) (Arg.var p_31.fst)
                          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.fst, Arg.imm 1, ()))
                            fun p_32 =>
                          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var v.fst, ())) fun p_33 =>
                          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_33.fst, Arg.imm 4, ()))
                            fun p_34 =>
                          Expr.let_ (Op.mk (OpCode.add i64)
                            (Arg.var c.pTarjanMark, Arg.var p_34.fst, ())) fun p_35 =>
                          Expr.store (Arg.var p_32.fst) (Arg.var p_35.fst)
                            (Expr.jump Js_3.fst (Arg.var p_32.fst, Arg.var abort_in, ()))))))
                    (Expr.jump Js_3.fst (Arg.var p.fst, Arg.var abort_in, ())))
                  (Expr.jump Js_2.fst (Arg.var p.fst, Arg.var abort_in, Arg.var p.snd.fst, ()))))
              (Expr.jump Js_1.fst (Arg.var p.fst, Arg.var abort_in, Arg.imm false,
                Arg.var p.snd.fst, ())))
            (Expr.jump K_done (Arg.var p.fst, Arg.var abort_in, Arg.imm false,
              Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ()))) Blocks.nil)
      fun Js => Expr.jump Js.fst (Arg.var nv0, Arg.imm 0, Arg.imm 0, ())) m := by
  have hcv_lt : s.core.cur_vars ≤ c.max_vars := hl.core_ok.cur_vars_le
  have hmaxv_bd : c.max_vars < 2 * LeanQbe.T.Examples.LratBytes.dimacsBound := c.hmaxv
  have hdim_bd : LeanQbe.T.Examples.LratBytes.dimacsBound = 2 ^ 28 := rfl
  have hcv_29 : s.core.cur_vars < 2 ^ 29 := by omega
  have hvals_len : s.core.vals.length = 2 * c.max_vars := hl.core_ok.vals_len
  apply wp_loop_inv
    (Inv := fun (p : BitVec 32 × BitVec 32 × BitVec 32 × Unit) m1 =>
      ∃ tmp1 wsort1 tmk1 : List (BitVec 32),
        p.1.toNat ≤ mv_s.toNat ∧ p.1.toNat ≤ 2 * s.core.cur_vars ∧
        p.2.1.toNat ≤ max_csz.toNat ∧ p.2.2.1.toNat ≤ sz.toNat ∧
        tmp1.length = c.max_vars ∧ wsort1.length = 2 * c.max_vars ∧
        tmk1.length = 2 * c.max_vars ∧
        FidK6cTmkReg p.1.toNat s.core.cur_vars wsort1 tmk1 ∧
        (FullMem c (FidP6Work s tmp1 wsort1 tmk1 scr) ⋆ R) m1)
    (μ := fun (p : BitVec 32 × BitVec 32 × BitVec 32 × Unit) _ => sz.toNat - p.2.2.1.toNat)
  · intro J hJ
    c0_hsteps
    exact hJ _ _ ⟨tmp, wsort, tmk, hnv0_mv, hnv0_cv, Nat.zero_le _, Nat.zero_le _,
      htmp_len, hw_len, htmk_len, hreg0, hm⟩
  · intro J p m1 ⟨tmp1, wsort1, tmk1, hnv_mv, hnv_cv, hcsz_le, hj_le, ht1, hw1, htmk1,
        hreg1, hm1⟩ hcont
    dsimp only [Blocks.get, Member.here]
    c0_hsteps_nogrp
    · -- `j < sz`
      have hj_lt : p.snd.snd.fst.toNat < sz.toNat := by bv_omega
      let idxA := (BitVec.setWidth 64 off + 3#64 + BitVec.setWidth 64 p.snd.snd.fst).toNat
      have hidxA : idxA = off.toNat + 3 + p.snd.snd.fst.toNat := by
        dsimp only [idxA]; bv_omega
      have hidxA_lt : idxA < s.core.arena.length := by omega
      have hl_bound : s.core.arena[idxA].toNat < 2 * s.core.cur_vars := by
        have := hsz_lits p.snd.snd.fst.toNat hj_lt
        simpa [← hidxA, List.getElem?_eq_getElem hidxA_lt] using this
      have hl_vals : (BitVec.setWidth 64 s.core.arena[idxA]).toNat < s.core.vals.length := by
        bv_omega
      apply wp_unroll_group
      intro Js_1 hJs_1
      c0_hsteps_nogrp
      · -- `l ≠ lit` ∧ `vals[l] > 0`: satisfied clause
        exact hK p.fst p.snd.fst p.snd.snd.fst abort_in true tmp1 wsort1 tmk1 _
          ht1 hw1 htmk1 hnv_mv hnv_cv hcsz_le hreg1 hm1
      · -- `l ≠ lit` ∧ `vals[l] ≤ 0`: unroll `Js_2`
        apply wp_unroll_group
        intro Js_2 hJs_2
        c0_hsteps_nogrp
        · -- `vals[l] == 0`: variable registration & store in `tmp`
          let v := s.core.arena[idxA] >>> 1
          have hv_cv : v.toNat < s.core.cur_vars := by dsimp only [v]; bv_omega
          have hv_tmk : (BitVec.setWidth 64 v).toNat < tmk1.length := by
            dsimp only [v]; bv_omega
          apply wp_unroll_group
          intro Js_3 hJs_3
          have hJ3_run : ∀ (nv2 : BitVec 32) (w2 tm2 : List (BitVec 32)) (m2 : Mem 64),
              nv2.toNat ≤ mv_s.toNat → nv2.toNat ≤ 2 * s.core.cur_vars →
              w2.length = 2 * c.max_vars → tm2.length = 2 * c.max_vars →
              tm2[v.toNat]?.getD 0#32 ≠ 0#32 →
              FidK6cTmkReg nv2.toNat s.core.cur_vars w2 tm2 →
              (FullMem c (FidP6Work s tmp1 w2 tm2 scr) ⋆ R) m2 →
              Js_3 (nv2, abort_in, ()) m2 := by
            intro nv2 w2 tm2 m2 hnv2_mv hnv2_cv hw2 htmk2 hnz2 hreg2 hm2
            apply hJs_3
            dsimp only [Blocks.get, Member.here]
            c0_hsteps
            · -- `csz ≥ max_csz`: overflow abort
              exact hK nv2 p.snd.fst p.snd.snd.fst true false tmp1 w2 tm2 _
                ht1 hw2 htmk2 hnv2_mv hnv2_cv hcsz_le hreg2 hm2
            · -- `csz < max_csz`: load `tmk[v]`, store `tmp[csz]`
              have hcsz_lt : p.snd.fst.toNat < max_csz.toNat := by bv_omega
              have hcsz_tmp : (BitVec.setWidth 64 p.snd.fst).toNat < tmp1.length := by bv_omega
              have hv_tm2 : (BitVec.setWidth 64 v).toNat < tm2.length := by
                dsimp only [v]; bv_omega
              c0_hsteps
              exact hcont (nv2, p.snd.fst + 1#32, p.snd.snd.fst + 1#32, ()) _ (by bv_omega)
                ⟨tmp1.set _ _, w2, tm2, hnv2_mv, hnv2_cv, by bv_omega, by bv_omega,
                  by simp [ht1], hw2, htmk2, hreg2, hm⟩
          clear hJs_3
          c0_hsteps
          · -- `tmk1[v] == 0` ∧ `nv ≥ mv_s`: overflow
            exact hK p.fst p.snd.fst p.snd.snd.fst true false tmp1 wsort1 tmk1 _
              ht1 hw1 htmk1 hnv_mv hnv_cv hcsz_le hreg1 hm1
          · -- `tmk1[v] == 0` ∧ `nv < mv_s` ∧ `nv ≥ 2 * cur_vars`: overflow
            exact hK p.fst p.snd.fst p.snd.snd.fst true false tmp1 wsort1 tmk1 _
              ht1 hw1 htmk1 hnv_mv hnv_cv hcsz_le hreg1 hm1
          · -- `tmk1[v] == 0` ∧ register `v`: `wsort[nv] := v`, `tmk[v] := nv + 1`
            have hlt_cv2 : p.fst.toNat < 2 * s.core.cur_vars := by
              have hshl := fid_k6c_bv64_cur_shl1 (cv := s.core.cur_vars) (by omega)
              have hnot : ¬ (BitVec.ofNat 64 s.core.cur_vars <<<
                  BitVec.signExtend 64 1#32 ≤ BitVec.setWidth 64 p.fst) := by bv_omega
              have hlt64 : (BitVec.setWidth 64 p.fst).toNat <
                  (BitVec.ofNat 64 s.core.cur_vars <<< BitVec.signExtend 64 1#32).toNat :=
                BitVec.lt_def.mp (BitVec.not_le.mp hnot)
              rw [hshl] at hlt64; bv_omega
            have hlt_w : (BitVec.setWidth 64 p.fst).toNat < wsort1.length := by bv_omega
            have hlt_t : (BitVec.setWidth 64 v).toNat < tmk1.length := by
              dsimp only [v]; bv_omega
            have ht0 : tmk1[v.toNat]?.getD 0#32 = 0#32 := by
              have heq : (BitVec.setWidth 64 v).toNat = v.toNat := by bv_omega
              have hv_l2 : v.toNat < tmk1.length := by rw [← heq]; exact hv_tmk
              rw [List.getElem?_eq_getElem hv_l2, Option.getD_some]
              simp only [v, idxA, FidP6Work, bv_c0, Nat.reducePow, Nat.reduceMod] at *
              bv_omega
            c0_hsteps
            have hreg_step : FidK6cTmkReg (p.fst + 1#32).toNat s.core.cur_vars
                (wsort1.set (BitVec.setWidth 64 p.fst).toNat v)
                (tmk1.set (BitVec.setWidth 64 v).toNat (p.fst + 1#32)) := by
              have h1 : (p.fst + 1#32).toNat = p.fst.toNat + 1 :=
                fid_k6c_add1_toNat (by bv_omega : p.fst.toNat < mv_s.toNat) (by omega)
              have hw_idx : (BitVec.setWidth 64 p.fst).toNat = p.fst.toNat := by bv_omega
              have hv_idx : (BitVec.setWidth 64 v).toNat = v.toNat := by bv_omega
              have hval_nv1 : p.fst + 1#32 = BitVec.ofNat 32 (p.fst.toNat + 1) := by
                apply BitVec.eq_of_toNat_eq
                rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              have hval_v : v = BitVec.ofNat 32 v.toNat := by simp
              rw [h1, hw_idx, hv_idx, hval_nv1]
              simpa [← hval_v] using fid_k6c_tmkReg_step hreg1 hlt_cv2 hv_cv ht0
                (Or.inr (by omega)) (by omega) (by omega)
            have hnz_step :
                (tmk1.set (BitVec.setWidth 64 v).toNat
                  (p.fst + 1#32))[v.toNat]?.getD 0#32 ≠ 0#32 := by
              have hv_idx : (BitVec.setWidth 64 v).toNat = v.toNat := by bv_omega
              rw [hv_idx, List.getElem?_set_self (by omega), Option.getD_some]
              intro heq
              have hto := congrArg BitVec.toNat heq
              have h1 : (p.fst + 1#32).toNat = p.fst.toNat + 1 :=
                fid_k6c_add1_toNat (by bv_omega : p.fst.toNat < mv_s.toNat) (by omega)
              rw [h1] at hto; simp at hto
            exact hJ3_run (p.fst + 1#32) _ _ _ (by bv_omega) (by bv_omega)
              (by simp [hw1]) (by simp [htmk1]) hnz_step hreg_step hm
          · -- `tmk1[v] ≠ 0`: already registered
            have hnz : tmk1[v.toNat]?.getD 0#32 ≠ 0#32 := by
              have heq : (BitVec.setWidth 64 v).toNat = v.toNat := by bv_omega
              have hv_l2 : v.toNat < tmk1.length := by rw [← heq]; exact hv_tmk
              rw [List.getElem?_eq_getElem hv_l2, Option.getD_some]
              simp only [v, idxA, FidP6Work, bv_c0, Nat.reducePow, Nat.reduceMod] at *
              bv_omega
            exact hJ3_run p.fst wsort1 tmk1 m1 hnv_mv hnv_cv hw1 htmk1 hnz hreg1 hm1
        · -- `vals[l] ≠ 0` (`< 0`): false lit skipped
          exact hcont (p.fst, p.snd.fst, p.snd.snd.fst + 1#32, ()) _ (by bv_omega)
            ⟨tmp1, wsort1, tmk1, hnv_mv, hnv_cv, hcsz_le, by bv_omega,
              ht1, hw1, htmk1, hreg1, hm1⟩
      · -- `l = lit`: skip
        refine hcont (p.fst, p.snd.fst, p.snd.snd.fst + 1#32, ()) _ (by bv_omega)
          ⟨tmp1, wsort1, tmk1, hnv_mv, hnv_cv, hcsz_le, by bv_omega,
            ht1, hw1, htmk1, hreg1, hm1⟩
    · -- Exit loop `!(j < sz)`
      exact hK p.fst p.snd.fst p.snd.snd.fst abort_in false tmp1 wsort1 tmk1 _
        ht1 hw1 htmk1 hnv_mv hnv_cv hcsz_le hreg1 hm1

/-! ## Sub-phase 4: `init_solve` (25 header slots + `J172` + `J210` + tail `K_tail`) -/

private theorem fid_k6c_init_var_loop_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {K_next : Expr Val Cont [Ty.bool]}
    {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {scr1 scr scr0 : List (BitVec 32)}
    {nv nc alen acap mv_s : BitVec 32}
    {o_rsn o_qprev o_qnext o_qst o_flags : BitVec 32}
    (hcap : 16384 ≤ c.scratch_cap) (hscr1_len : scr1.length = c.scratch_cap)
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hoff_rsn : o_rsn = 4224#32 + mv_s) (hoff_qprev : o_qprev = 4224#32 + 2#32 * mv_s)
    (hoff_qnext : o_qnext = 4224#32 + 3#32 * mv_s)
    (hoff_qst : o_qst = 4224#32 + 4#32 * mv_s)
    (hoff_flags : o_flags = 4224#32 + 6#32 * mv_s)
    (hcap_ar : 4224 + 45 * mv_s.toNat + acap.toNat ≤ c.scratch_cap)
    (hnv_le : nv.toNat ≤ mv_s.toNat)
    (h1_93 : scr1[4193]? = some nc) (h1_94 : scr1[4194]? = some nc)
    (h1_06 : scr1[4206]? = some alen) (h1_07 : scr1[4207]? = some acap)
    (h1_14 : scr1[4214]? = some mv_s)
    (h1_hi : ∀ i, 4224 + 29 * mv_s.toNat ≤ i → scr1[i]? = scr[i]?)
    (hpre0 : ∀ i, i < 4002 → scr1[i]? = scr0[i]?)
    (hpre1 : ∀ i, 4132 ≤ i → i < 4192 → scr1[i]? = scr0[i]?)
    (hm : (FullMem c (FidP6Scr s scr1) ⋆ R) m)
    (hNext : ∀ (scrA : List (BitVec 32)) (m1 : Mem 64),
      scrA.length = c.scratch_cap →
      scrA[4193]? = some nc → scrA[4194]? = some nc → scrA[4206]? = some alen →
      scrA[4207]? = some acap → scrA[4214]? = some mv_s →
      (∀ i, 4224 + 29 * mv_s.toNat ≤ i → scrA[i]? = scr[i]?) →
      (∀ i, i < 4002 → scrA[i]? = scr0[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scrA[i]? = scr0[i]?) →
      (FullMem c (FidP6Scr s scrA) ⋆ R) m1 → wp Γ Q X K_next m1) :
    wp Γ Q X
      (Expr.group (fun Js : Tup Cont [[i32]] => Blocks.cons (fun pi : Tup Val [i32] =>
        Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pi.fst, Arg.var nv, ()))
          fun p77 =>
        Expr.jnz (Arg.var p77.fst)
          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 4224, Arg.var pi.fst, ())) fun p78 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p78.fst, ())) fun p79 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p79.fst, Arg.imm 4, ())) fun p80 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p80.fst, ())) fun p81 =>
          Expr.store (t := i32) (Arg.imm 0) (Arg.var p81.fst)
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_rsn, Arg.var pi.fst, ())) fun p82 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p82.fst, ())) fun p83 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p83.fst, Arg.imm 4, ())) fun p84 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p84.fst, ()))
              fun p85 =>
            Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p85.fst)
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_flags, Arg.var pi.fst, ())) fun p86 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p86.fst, ())) fun p87 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p87.fst, Arg.imm 4, ())) fun p88 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p88.fst, ()))
                fun p89 =>
              Expr.store (t := i32) (Arg.imm 0) (Arg.var p89.fst)
                (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_qst, Arg.var pi.fst, ())) fun p90 =>
                Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p90.fst, ())) fun p91 =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p91.fst, Arg.imm 4, ())) fun p92 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p92.fst, ()))
                  fun p93 =>
                Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ())) fun p94 =>
                Expr.store (Arg.var p94.fst) (Arg.var p93.fst)
                  (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_qprev, Arg.var pi.fst, ()))
                    fun p95 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p95.fst, ())) fun p96 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p96.fst, Arg.imm 4, ())) fun p97 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p97.fst, ()))
                    fun p98 =>
                  Expr.group (fun _Js_1 : Tup Cont [[i32]] => Blocks.cons (fun pq =>
                    Expr.store (Arg.var pq.fst) (Arg.var p98.fst)
                      (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_qnext, Arg.var pi.fst, ()))
                        fun p99 =>
                      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p99.fst, ())) fun p100 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p100.fst, Arg.imm 4, ()))
                        fun p101 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pScratchBuf, Arg.var p101.fst, ())) fun p102 =>
                      Expr.group (fun _Js_2 : Tup Cont [[i32]] => Blocks.cons (fun pqn =>
                        Expr.store (Arg.var pqn.fst) (Arg.var p102.fst)
                          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ()))
                            fun p103 => Expr.jump Js.fst (Arg.var p103.fst, ()))) Blocks.nil)
                        fun Js_2 =>
                      Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ())) fun p103 =>
                      Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
                        (Arg.var p103.fst, Arg.var nv, ())) fun p104 =>
                      Expr.jnz (Arg.var p104.fst)
                        (Expr.jump Js_2.fst (Arg.imm 4294967295, ()))
                        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ()))
                          fun p105 => Expr.jump Js_2.fst (Arg.var p105.fst, ())))) Blocks.nil)
                    fun Js_1 =>
                  Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                    (Arg.var pi.fst, Arg.imm 0, ())) fun p99 =>
                  Expr.jnz (Arg.var p99.fst)
                    (Expr.jump Js_1.fst (Arg.imm 4294967295, ()))
                    (Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var pi.fst, Arg.imm 1, ())) fun p100 =>
                    Expr.jump Js_1.fst (Arg.var p100.fst, ())))))))
          K_next) Blocks.nil)
      fun Js => Expr.jump Js.fst (Arg.imm 0, ())) m := by
  apply wp_loop_inv
    (Inv := fun (pi : BitVec 32 × Unit) m1 => ∃ scrA : List (BitVec 32),
      pi.1.toNat ≤ nv.toNat ∧ scrA.length = c.scratch_cap ∧
      scrA[4193]? = some nc ∧ scrA[4194]? = some nc ∧ scrA[4206]? = some alen ∧
      scrA[4207]? = some acap ∧ scrA[4214]? = some mv_s ∧
      (∀ i, 4224 + 29 * mv_s.toNat ≤ i → scrA[i]? = scr[i]?) ∧
      (∀ i, i < 4002 → scrA[i]? = scr0[i]?) ∧
      (∀ i, 4132 ≤ i → i < 4192 → scrA[i]? = scr0[i]?) ∧
      (FullMem c (FidP6Scr s scrA) ⋆ R) m1)
    (μ := fun (pi : BitVec 32 × Unit) _ => nv.toNat - pi.1.toNat)
  · intro J hJ
    c0_hsteps
    exact hJ _ _ ⟨scr1, Nat.zero_le _, hscr1_len, h1_93, h1_94, h1_06, h1_07, h1_14,
      h1_hi, hpre0, hpre1, hm⟩
  · intro J pi m1 ⟨scrA, hpi_le, hlenA, hA_93, hA_94, hA_06, hA_07, hA_14, hag_hi,
        hp0_1, hp1_1, hm1⟩ hcont
    dsimp only [Blocks.get, Member.here]
    c0_hsteps
    · -- `pi < nv`
      have hpi_lt : pi.fst.toNat < nv.toNat := by bv_omega
      have hi0 : (BitVec.setWidth 64 (4224#32 + pi.fst)).toNat = 4224 + pi.fst.toNat :=
        fid_k6_off_add0 (by omega)
      have hi0' : (BitVec.setWidth 64 ((4224 : Val i32) + pi.fst)).toNat = 4224 + pi.fst.toNat :=
        hi0
      have hi1 : (BitVec.setWidth 64 (o_rsn + pi.fst)).toNat =
          4224 + mv_s.toNat + pi.fst.toNat := by
        rw [hoff_rsn]; exact fid_k6_off_add1 hmv_hi (by omega)
      have hi2 : (BitVec.setWidth 64 (o_flags + pi.fst)).toNat =
          4224 + 6 * mv_s.toNat + pi.fst.toNat := by
        rw [hoff_flags]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
      have hi3 : (BitVec.setWidth 64 (o_qst + pi.fst)).toNat =
          4224 + 4 * mv_s.toNat + pi.fst.toNat := by
        rw [hoff_qst]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
      have hi4 : (BitVec.setWidth 64 (o_qprev + pi.fst)).toNat =
          4224 + 2 * mv_s.toNat + pi.fst.toNat := by
        rw [hoff_qprev]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
      have hi5 : (BitVec.setWidth 64 (o_qnext + pi.fst)).toNat =
          4224 + 3 * mv_s.toNat + pi.fst.toNat := by
        rw [hoff_qnext]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
      have hb1 : 4224 + 7 * mv_s.toNat ≤ scrA.length := by omega
      have hlt0 : (BitVec.setWidth 64 (4224#32 + pi.fst)).toNat < scrA.length := by omega
      have hlt1 : (BitVec.setWidth 64 (o_rsn + pi.fst)).toNat < scrA.length := by omega
      have hlt2 : (BitVec.setWidth 64 (o_flags + pi.fst)).toNat < scrA.length := by omega
      have hlt3 : (BitVec.setWidth 64 (o_qst + pi.fst)).toNat < scrA.length := by omega
      c0_hsteps_nogrp
      apply wp_unroll_group
      intro Js_1 hJs_1
      have hJ1 : ∀ (pq : BitVec 32) (scr4 : List (BitVec 32)) (m' : Mem 64),
          scr4.length = c.scratch_cap →
          scr4[4193]? = some nc → scr4[4194]? = some nc → scr4[4206]? = some alen →
          scr4[4207]? = some acap → scr4[4214]? = some mv_s →
          (∀ i, 4224 + 29 * mv_s.toNat ≤ i → scr4[i]? = scr[i]?) →
          (∀ i, i < 4002 → scr4[i]? = scr0[i]?) →
          (∀ i, 4132 ≤ i → i < 4192 → scr4[i]? = scr0[i]?) →
          (FullMem c (FidP6Scr s scr4) ⋆ R) m' → Js_1 (pq, ()) m' := by
        intro pq scr4 m' hl4 h4_93 h4_94 h4_06 h4_07 h4_14 h4_ag h4_p0 h4_p1 hm'
        apply hJs_1; dsimp only [Blocks.get, Member.here]
        have hlt4 : (BitVec.setWidth 64 (o_qprev + pi.fst)).toNat < scr4.length := by omega
        c0_hsteps_nogrp
        apply wp_unroll_group
        intro Js_2 hJs_2
        have hJ2 : ∀ (pqn : BitVec 32) (scr5 : List (BitVec 32)) (m'' : Mem 64),
            scr5.length = c.scratch_cap →
            scr5[4193]? = some nc → scr5[4194]? = some nc → scr5[4206]? = some alen →
            scr5[4207]? = some acap → scr5[4214]? = some mv_s →
            (∀ i, 4224 + 29 * mv_s.toNat ≤ i → scr5[i]? = scr[i]?) →
            (∀ i, i < 4002 → scr5[i]? = scr0[i]?) →
            (∀ i, 4132 ≤ i → i < 4192 → scr5[i]? = scr0[i]?) →
            (FullMem c (FidP6Scr s scr5) ⋆ R) m'' → Js_2 (pqn, ()) m'' := by
          intro pqn scr5 m'' hl5 h5_93 h5_94 h5_06 h5_07 h5_14 h5_ag h5_p0 h5_p1 hm''
          apply hJs_2; dsimp only [Blocks.get, Member.here]
          have hlt5 : (BitVec.setWidth 64 (o_qnext + pi.fst)).toNat < scr5.length := by omega
          c0_hsteps
          try dsimp only [FidP6Scr] at hm
          try rw [hi5] at hm
          have hpi1 : (pi.fst + 1#32).toNat = pi.fst.toNat + 1 :=
            fid_k6c_add1_toNat hpi_lt (by omega)
          refine hcont (pi.fst + 1#32, ()) _ (by dsimp only; omega)
            ⟨_, by dsimp only; omega, by simp [hl5], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm⟩
          · rw [List.getElem?_set_ne (by omega)]; exact h5_93
          · rw [List.getElem?_set_ne (by omega)]; exact h5_94
          · rw [List.getElem?_set_ne (by omega)]; exact h5_06
          · rw [List.getElem?_set_ne (by omega)]; exact h5_07
          · rw [List.getElem?_set_ne (by omega)]; exact h5_14
          · intro i hi; rw [List.getElem?_set_ne (by omega : _ ≠ i)]; exact h5_ag i hi
          · intro i hi; rw [List.getElem?_set_ne (by omega : _ ≠ i)]; exact h5_p0 i hi
          · intro i h1 h2; rw [List.getElem?_set_ne (by omega : _ ≠ i)]; exact h5_p1 i h1 h2
        clear hJs_2
        c0_hsteps <;>
          (try dsimp only [FidP6Scr] at hm
           try rw [hi4] at hm
           exact hJ2 _ _ _ (by simp [hl4])
            (by rw [List.getElem?_set_ne (by omega)]; exact h4_93)
            (by rw [List.getElem?_set_ne (by omega)]; exact h4_94)
            (by rw [List.getElem?_set_ne (by omega)]; exact h4_06)
            (by rw [List.getElem?_set_ne (by omega)]; exact h4_07)
            (by rw [List.getElem?_set_ne (by omega)]; exact h4_14)
            (fun i hi => by rw [List.getElem?_set_ne (by omega : _ ≠ i)]; exact h4_ag i hi)
            (fun i hi => by rw [List.getElem?_set_ne (by omega : _ ≠ i)]; exact h4_p0 i hi)
            (fun i h1 h2 => by rw [List.getElem?_set_ne (by omega : _ ≠ i)]; exact h4_p1 i h1 h2)
            hm)
      clear hJs_1
      c0_hsteps <;>
        (try dsimp only [FidP6Scr] at hm
         try rw [hi0'] at hm
         try rw [hi1] at hm
         try rw [hi2] at hm
         try rw [hi3] at hm
         refine hJ1 _ _ _ (by simp [hlenA]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm
         · (repeat rw [List.getElem?_set_ne (by omega)]); exact hA_93
         · (repeat rw [List.getElem?_set_ne (by omega)]); exact hA_94
         · (repeat rw [List.getElem?_set_ne (by omega)]); exact hA_06
         · (repeat rw [List.getElem?_set_ne (by omega)]); exact hA_07
         · (repeat rw [List.getElem?_set_ne (by omega)]); exact hA_14
         · intro i hi; (repeat rw [List.getElem?_set_ne (by omega : _ ≠ i)]); exact hag_hi i hi
         · intro i hi; (repeat rw [List.getElem?_set_ne (by omega : _ ≠ i)]); exact hp0_1 i hi
         · intro i h1 h2
           (repeat rw [List.getElem?_set_ne (by omega : _ ≠ i)])
           exact hp1_1 i h1 h2)
    · -- Exit `J172` -> `K_next`
      exact hNext scrA m1 hlenA hA_93 hA_94 hA_06 hA_07 hA_14 hag_hi hp0_1 hp1_1 hm1

private theorem fid_k6c_init_lit_loop_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {K_tail : Expr Val Cont [Ty.bool]}
    {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m1 : Mem 64} {scrA scr scr0 : List (BitVec 32)}
    {nv nc alen acap n_units mv_s : BitVec 32}
    {o_vals o_whead : BitVec 32}
    (hcap : 16384 ≤ c.scratch_cap) (hscr_lt : c.scratch_cap < 2 ^ 30)
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hoff_vals : o_vals = 4224#32 + 9#32 * mv_s)
    (hoff_whead : o_whead = 4224#32 + 11#32 * mv_s)
    (hcap_ar : 4224 + 45 * mv_s.toNat + acap.toNat ≤ c.scratch_cap)
    (hnv_le : nv.toNat ≤ mv_s.toNat) (halen_le : alen.toNat ≤ acap.toNat)
    (hcls : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr)
    (hlenA : scrA.length = c.scratch_cap)
    (hA_93 : scrA[4193]? = some nc) (hA_94 : scrA[4194]? = some nc)
    (hA_06 : scrA[4206]? = some alen) (hA_07 : scrA[4207]? = some acap)
    (hA_14 : scrA[4214]? = some mv_s)
    (hag_hi : ∀ i, 4224 + 29 * mv_s.toNat ≤ i → scrA[i]? = scr[i]?)
    (hp0_1 : ∀ i, i < 4002 → scrA[i]? = scr0[i]?)
    (hp1_1 : ∀ i, 4132 ≤ i → i < 4192 → scrA[i]? = scr0[i]?)
    (hm1 : (FullMem c (FidP6Scr s scrA) ⋆ R) m1)
    (hTail : ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
      scr'.length = c.scratch_cap → FidK6BufOk scr' →
      scr'[4193]? = some nc → scr'[4194]? = some nc → scr'[4214]? = some mv_s →
      (∀ cid, cid < nc.toNat →
        let raw := scr'[4224 + 37 * mv_s.toNat + cid]?.getD 0#32
        raw.toNat < 4096 ∧ (raw &&& 2047#32).toNat < 2001) →
      (∀ i, i < 4002 → scr'[i]? = scr0[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = scr0[i]?) →
      (FullMem c (FidP6Scr s scr') ⋆ R) m' → wp Γ Q X K_tail m') :
    wp Γ Q X
      (Expr.group (fun Js_1 : Tup Cont [[i32]] => Blocks.cons (fun pi : Tup Val [i32] =>
        Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var nv, Arg.imm 1, ())) fun p78 =>
        Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pi.fst, Arg.var p78.fst, ()))
          fun p79 =>
        Expr.jnz (Arg.var p79.fst)
          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_vals, Arg.var pi.fst, ())) fun p80 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p80.fst, ())) fun p81 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p81.fst, Arg.imm 4, ())) fun p82 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p82.fst, ()))
            fun p83 =>
          Expr.store (t := i32) (Arg.imm 0) (Arg.var p83.fst)
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_whead, Arg.var pi.fst, ())) fun p84 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p84.fst, ())) fun p85 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p85.fst, Arg.imm 4, ())) fun p86 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p86.fst, ()))
              fun p87 =>
            Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p87.fst)
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ())) fun p88 =>
              Expr.jump Js_1.fst (Arg.var p88.fst, ()))))
          K_tail) Blocks.nil)
      fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0, ())) m1 := by
  apply wp_loop_inv
    (Inv := fun (pj : BitVec 32 × Unit) m2 => ∃ scr2 : List (BitVec 32),
      pj.1.toNat ≤ 2 * nv.toNat ∧ scr2.length = c.scratch_cap ∧
      scr2[4193]? = some nc ∧ scr2[4194]? = some nc ∧ scr2[4206]? = some alen ∧
      scr2[4207]? = some acap ∧ scr2[4214]? = some mv_s ∧
      (∀ i, 4224 + 29 * mv_s.toNat ≤ i → scr2[i]? = scr[i]?) ∧
      (∀ i, i < 4002 → scr2[i]? = scr0[i]?) ∧
      (∀ i, 4132 ≤ i → i < 4192 → scr2[i]? = scr0[i]?) ∧
      (FullMem c (FidP6Scr s scr2) ⋆ R) m2)
    (μ := fun (pj : BitVec 32 × Unit) _ => 2 * nv.toNat - pj.1.toNat)
  · intro J2 hJ2
    c0_hsteps
    exact hJ2 _ _ ⟨scrA, Nat.zero_le _, hlenA, hA_93, hA_94, hA_06, hA_07, hA_14,
      hag_hi, hp0_1, hp1_1, hm1⟩
  · intro J2 pj m2 ⟨scr2, hpj_le, hlen2, h2_93, h2_94, h2_06, h2_07, h2_14, hag2_hi,
        hp0_2, hp1_2, hm2⟩ hcont2
    dsimp only [Blocks.get, Member.here]
    have hshl2 : (nv <<< 1).toNat = 2 * nv.toNat := m8_bv32_shl1_toNat (by omega)
    c0_hsteps
    · -- `pj < 2 * nv`
      change pj.fst.toNat < nv.toNat * 2 ^ 1 % 2 ^ 32 at hc
      have hpj_lt : pj.fst.toNat < 2 * nv.toNat := by omega
      have hva : (BitVec.setWidth 64 (o_vals + pj.fst)).toNat =
          4224 + 9 * mv_s.toNat + pj.fst.toNat := by
        rw [hoff_vals]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
      have hwh : (BitVec.setWidth 64 (o_whead + pj.fst)).toNat =
          4224 + 11 * mv_s.toNat + pj.fst.toNat := by
        rw [hoff_whead]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
      have hlt_va : (BitVec.setWidth 64 (o_vals + pj.fst)).toNat < scr2.length := by omega
      have hlt_wh : (BitVec.setWidth 64 (o_whead + pj.fst)).toNat <
          (scr2.set (BitVec.setWidth 64 (o_vals + pj.fst)).toNat 0#32).length := by
        simp only [List.length_set, hlen2]; omega
      c0_hsteps
      try dsimp only [FidP6Scr] at hm
      try rw [hva] at hm
      try rw [hwh] at hm
      have hpj1 : (pj.fst + 1#32).toNat = pj.fst.toNat + 1 :=
        fid_k6c_add1_toNat hpj_lt (by omega)
      refine hcont2 (pj.fst + 1#32, ()) _ (by dsimp only; omega)
        ⟨_, by dsimp only; omega, by simp [hlen2], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm⟩
      · (repeat rw [List.getElem?_set_ne (by omega)]); exact h2_93
      · (repeat rw [List.getElem?_set_ne (by omega)]); exact h2_94
      · (repeat rw [List.getElem?_set_ne (by omega)]); exact h2_06
      · (repeat rw [List.getElem?_set_ne (by omega)]); exact h2_07
      · (repeat rw [List.getElem?_set_ne (by omega)]); exact h2_14
      · intro i hi; (repeat rw [List.getElem?_set_ne (by omega : _ ≠ i)]); exact hag2_hi i hi
      · intro i hi; (repeat rw [List.getElem?_set_ne (by omega : _ ≠ i)]); exact hp0_2 i hi
      · intro i h1 h2; (repeat rw [List.getElem?_set_ne (by omega : _ ≠ i)]); exact hp1_2 i h1 h2
    · -- Exit `J210` -> call `K_tail`
      have hcls2 : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr2 :=
        fid_k6c_clsOk_frame hcls fun idx h1 _ => hag2_hi idx h1
      have hbuf : FidK6BufOk scr2 := fid_k6c_bufOk_of_init (cap := n_units.toNat)
        hmv_lo hmv_hi (by omega) (by omega) h2_93 h2_06 h2_07 h2_14 hcls2.1 halen_le hcls2
      have haux : ∀ cid, cid < nc.toNat →
          let raw := scr2[4224 + 37 * mv_s.toNat + cid]?.getD 0#32
          raw.toNat < 4096 ∧ (raw &&& 2047#32).toNat < 2001 := fun cid hcid =>
        (hcls2.2.1 cid hcid).2.2
      exact hTail scr2 m2 hlen2 hbuf h2_93 h2_94 h2_14 haux hp0_2 hp1_2 hm2

private theorem fid_k6c_init_hdr1_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {K_next : Expr Val Cont [Ty.bool]}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {scr scr0 : List (BitVec 32)}
    {nv nc tick_lim : BitVec 32}
    (hcap : 16384 ≤ c.scratch_cap) (hscr_len : scr.length = c.scratch_cap)
    (hpre0 : ∀ i, i < 4002 → scr[i]? = scr0[i]?)
    (hpre1 : ∀ i, 4132 ≤ i → i < 4192 → scr[i]? = scr0[i]?)
    (hm : (FullMem c (FidP6Scr s scr) ⋆ R) m)
    (hK : ∀ (scr1 : List (BitVec 32)) (m1 : Mem 64),
      scr1.length = c.scratch_cap →
      scr1[4193]? = some nc → scr1[4194]? = some nc →
      (∀ i, 4224 ≤ i → scr1[i]? = scr[i]?) →
      (∀ i, i < 4002 → scr1[i]? = scr0[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scr1[i]? = scr0[i]?) →
      (FullMem c (FidP6Scr s scr1) ⋆ R) m1 → wp Γ Q X K_next m1) :
    wp Γ Q X
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4192, ())) fun p0 =>
      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p0.fst, Arg.imm 4, ())) fun p1 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p1.fst, ())) fun p2 =>
      Expr.store (t := i32) (Arg.var nv) (Arg.var p2.fst)
        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4193, ())) fun p3 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p3.fst, Arg.imm 4, ())) fun p4 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p4.fst, ())) fun p5 =>
        Expr.store (t := i32) (Arg.var nc) (Arg.var p5.fst)
          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4194, ())) fun p6 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p6.fst, Arg.imm 4, ())) fun p7 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p7.fst, ())) fun p8 =>
          Expr.store (t := i32) (Arg.var nc) (Arg.var p8.fst)
            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4195, ())) fun p9 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p9.fst, Arg.imm 4, ())) fun p10 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p10.fst, ()))
              fun p11 =>
            Expr.store (t := i32) (Arg.imm 0) (Arg.var p11.fst)
              (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4196, ())) fun p12 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p12.fst, Arg.imm 4, ())) fun p13 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p13.fst, ()))
                fun p14 =>
              Expr.store (t := i32) (Arg.imm 0) (Arg.var p14.fst)
                (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4197, ())) fun p15 =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p15.fst, Arg.imm 4, ())) fun p16 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p16.fst, ()))
                  fun p17 =>
                Expr.store (t := i32) (Arg.imm 0) (Arg.var p17.fst)
                  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4198, ())) fun p18 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p18.fst, Arg.imm 4, ())) fun p19 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p19.fst, ()))
                    fun p20 =>
                  Expr.store (t := i32) (Arg.var nv) (Arg.var p20.fst)
                    (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4199, ())) fun p21 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p21.fst, Arg.imm 4, ())) fun p22 =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                      (Arg.var c.pScratchBuf, Arg.var p22.fst, ())) fun p23 =>
                    Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p23.fst)
                      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4200, ())) fun p24 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p24.fst, Arg.imm 4, ())) fun p25 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pScratchBuf, Arg.var p25.fst, ())) fun p26 =>
                      Expr.store (t := i32) (Arg.imm 0) (Arg.var p26.fst)
                        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4201, ())) fun p27 =>
                        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p27.fst, Arg.imm 4, ()))
                          fun p28 =>
                        Expr.let_ (Op.mk (OpCode.add i64)
                          (Arg.var c.pScratchBuf, Arg.var p28.fst, ())) fun p29 =>
                        Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var nv, Arg.imm 1, ())) fun p30 =>
                        Expr.store (Arg.var p30.fst) (Arg.var p29.fst)
                          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4202, ())) fun p31 =>
                          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p31.fst, Arg.imm 4, ()))
                            fun p32 =>
                          Expr.let_ (Op.mk (OpCode.add i64)
                            (Arg.var c.pScratchBuf, Arg.var p32.fst, ())) fun p33 =>
                          Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var nv, Arg.imm 1, ())) fun p34 =>
                          Expr.store (Arg.var p34.fst) (Arg.var p33.fst)
                            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4203, ())) fun p35 =>
                            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p35.fst, Arg.imm 4, ()))
                              fun p36 =>
                            Expr.let_ (Op.mk (OpCode.add i64)
                              (Arg.var c.pScratchBuf, Arg.var p36.fst, ())) fun p37 =>
                            Expr.store (t := i32) (Arg.var nv) (Arg.var p37.fst)
                              (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4204, ())) fun p38 =>
                              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p38.fst, Arg.imm 4, ()))
                                fun p39 =>
                              Expr.let_ (Op.mk (OpCode.add i64)
                                (Arg.var c.pScratchBuf, Arg.var p39.fst, ())) fun p40 =>
                              Expr.store (t := i32) (Arg.imm 0) (Arg.var p40.fst)
                                (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4205, ()))
                                  fun p41 =>
                                Expr.let_ (Op.mk (OpCode.mul i64)
                                  (Arg.var p41.fst, Arg.imm 4, ())) fun p42 =>
                                Expr.let_ (Op.mk (OpCode.add i64)
                                  (Arg.var c.pScratchBuf, Arg.var p42.fst, ())) fun p43 =>
                                Expr.store (t := i32) (Arg.var tick_lim) (Arg.var p43.fst)
                                  K_next)))))))))))))) m := by
  have hscr_ge : 4224 ≤ scr.length := by omega
  c0_hsteps
  try dsimp only [FidP6Scr] at hm
  refine hK _ _ (by simp only [List.length_set, hscr_len]) ?_ ?_ ?_ ?_ ?_ hm
  · (repeat rw [List.getElem?_set_ne (by decide)])
    exact List.getElem?_set_self (by simp only [List.length_set, hscr_len]; omega)
  · (repeat rw [List.getElem?_set_ne (by decide)])
    exact List.getElem?_set_self (by simp only [List.length_set, hscr_len]; omega)
  · intro i hi; (repeat rw [List.getElem?_set_ne (by omega : _ ≠ i)]); try rfl
  · intro i hi; (repeat rw [List.getElem?_set_ne (by omega : _ ≠ i)]); exact hpre0 i hi
  · intro i h1 h2; (repeat rw [List.getElem?_set_ne (by omega : _ ≠ i)]); exact hpre1 i h1 h2

private theorem fid_k6c_init_hdr2_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {K_next : Expr Val Cont [Ty.bool]}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {scr1 scr scr0 : List (BitVec 32)}
    {nc alen acap n_units mv_s mc_s max_orig_s : BitVec 32}
    (hcap : 16384 ≤ c.scratch_cap) (hscr1_len : scr1.length = c.scratch_cap)
    (h1_93 : scr1[4193]? = some nc) (h1_94 : scr1[4194]? = some nc)
    (h1_hi : ∀ i, 4224 ≤ i → scr1[i]? = scr[i]?)
    (hpre0 : ∀ i, i < 4002 → scr1[i]? = scr0[i]?)
    (hpre1 : ∀ i, 4132 ≤ i → i < 4192 → scr1[i]? = scr0[i]?)
    (hm : (FullMem c (FidP6Scr s scr1) ⋆ R) m)
    (hK : ∀ (scr2 : List (BitVec 32)) (m2 : Mem 64),
      scr2.length = c.scratch_cap →
      scr2[4193]? = some nc → scr2[4194]? = some nc →
      scr2[4206]? = some alen → scr2[4207]? = some acap → scr2[4214]? = some mv_s →
      (∀ i, 4224 ≤ i → scr2[i]? = scr[i]?) →
      (∀ i, i < 4002 → scr2[i]? = scr0[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scr2[i]? = scr0[i]?) →
      (FullMem c (FidP6Scr s scr2) ⋆ R) m2 → wp Γ Q X K_next m2) :
    wp Γ Q X
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4206, ())) fun p44 =>
      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p44.fst, Arg.imm 4, ())) fun p45 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p45.fst, ())) fun p46 =>
      Expr.store (t := i32) (Arg.var alen) (Arg.var p46.fst)
        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4207, ())) fun p47 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p47.fst, Arg.imm 4, ())) fun p48 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p48.fst, ())) fun p49 =>
        Expr.store (t := i32) (Arg.var acap) (Arg.var p49.fst)
          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4208, ())) fun p50 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p50.fst, Arg.imm 4, ())) fun p51 =>
          Expr.let_ (Op.mk (OpCode.add i64)
            (Arg.var c.pScratchBuf, Arg.var p51.fst, ())) fun p52 =>
          Expr.store (t := i32) (Arg.imm 0) (Arg.var p52.fst)
            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4209, ())) fun p53 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p53.fst, Arg.imm 4, ())) fun p54 =>
            Expr.let_ (Op.mk (OpCode.add i64)
              (Arg.var c.pScratchBuf, Arg.var p54.fst, ())) fun p55 =>
            Expr.store (t := i32) (Arg.imm 0) (Arg.var p55.fst)
              (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4210, ())) fun p56 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p56.fst, Arg.imm 4, ())) fun p57 =>
              Expr.let_ (Op.mk (OpCode.add i64)
                (Arg.var c.pScratchBuf, Arg.var p57.fst, ())) fun p58 =>
              Expr.store (t := i32) (Arg.imm 0) (Arg.var p58.fst)
                (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4211, ())) fun p59 =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p59.fst, Arg.imm 4, ())) fun p60 =>
                Expr.let_ (Op.mk (OpCode.add i64)
                  (Arg.var c.pScratchBuf, Arg.var p60.fst, ())) fun p61 =>
                Expr.store (t := i32) (Arg.var n_units) (Arg.var p61.fst)
                  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4212, ())) fun p62 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p62.fst, Arg.imm 4, ())) fun p63 =>
                  Expr.let_ (Op.mk (OpCode.add i64)
                    (Arg.var c.pScratchBuf, Arg.var p63.fst, ())) fun p64 =>
                  Expr.store (t := i32) (Arg.imm 0) (Arg.var p64.fst)
                    (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4213, ())) fun p65 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p65.fst, Arg.imm 4, ())) fun p66 =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                      (Arg.var c.pScratchBuf, Arg.var p66.fst, ())) fun p67 =>
                    Expr.store (t := i32) (Arg.imm 0) (Arg.var p67.fst)
                      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4214, ())) fun p68 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p68.fst, Arg.imm 4, ())) fun p69 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pScratchBuf, Arg.var p69.fst, ())) fun p70 =>
                      Expr.store (t := i32) (Arg.var mv_s) (Arg.var p70.fst)
                        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4215, ())) fun p71 =>
                        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p71.fst, Arg.imm 4, ()))
                          fun p72 =>
                        Expr.let_ (Op.mk (OpCode.add i64)
                          (Arg.var c.pScratchBuf, Arg.var p72.fst, ())) fun p73 =>
                        Expr.store (t := i32) (Arg.var mc_s) (Arg.var p73.fst)
                          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4216, ())) fun p74 =>
                          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p74.fst, Arg.imm 4, ()))
                            fun p75 =>
                          Expr.let_ (Op.mk (OpCode.add i64)
                            (Arg.var c.pScratchBuf, Arg.var p75.fst, ())) fun p76 =>
                          Expr.store (t := i32) (Arg.var max_orig_s) (Arg.var p76.fst)
                            K_next))))))))))) m := by
  have hscr_ge : 4224 ≤ scr1.length := by omega
  c0_hsteps
  try dsimp only [FidP6Scr] at hm
  refine hK _ _ (by simp only [List.length_set, hscr1_len]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm
  · (repeat rw [List.getElem?_set_ne (by decide)]); exact h1_93
  · (repeat rw [List.getElem?_set_ne (by decide)]); exact h1_94
  · (repeat rw [List.getElem?_set_ne (by decide)])
    exact List.getElem?_set_self (by simp only [hscr1_len]; omega)
  · (repeat rw [List.getElem?_set_ne (by decide)])
    exact List.getElem?_set_self (by simp only [List.length_set, hscr1_len]; omega)
  · (repeat rw [List.getElem?_set_ne (by decide)])
    exact List.getElem?_set_self (by simp only [List.length_set, hscr1_len]; omega)
  · intro i hi; (repeat rw [List.getElem?_set_ne (by omega : _ ≠ i)]); exact h1_hi i hi
  · intro i hi; (repeat rw [List.getElem?_set_ne (by omega : _ ≠ i)]); exact hpre0 i hi
  · intro i h1 h2; (repeat rw [List.getElem?_set_ne (by omega : _ ≠ i)]); exact hpre1 i h1 h2

/-- Initialize header `4192..4216` and dense var/lit arrays, then run `K_tail`. -/
theorem fid_k6c_init_solve_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {K_tail : Expr Val Cont [Ty.bool]}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {scr scr0 : List (BitVec 32)}
    {nv nc alen acap n_units tick_lim mv_s mc_s max_orig_s : BitVec 32}
    {o_rsn o_qprev o_qnext o_qst o_flags o_vals o_whead : BitVec 32}
    (_hinv : FullDenseInvW c F0 F_cur s) (_htmk : TmkZero s) (hcap : 16384 ≤ c.scratch_cap)
    (_hscr_lt : scr.length < 2 ^ 30) (hscr_len : scr.length = c.scratch_cap)
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (_hmc_s : mc_s = mv_s <<< 2) (_hmax_orig_s : max_orig_s = mv_s <<< 1)
    (hoff_rsn : o_rsn = 4224#32 + mv_s) (hoff_qprev : o_qprev = 4224#32 + 2#32 * mv_s)
    (hoff_qnext : o_qnext = 4224#32 + 3#32 * mv_s)
    (hoff_qst : o_qst = 4224#32 + 4#32 * mv_s)
    (hoff_flags : o_flags = 4224#32 + 6#32 * mv_s)
    (hoff_vals : o_vals = 4224#32 + 9#32 * mv_s)
    (hoff_whead : o_whead = 4224#32 + 11#32 * mv_s)
    (hcap_ar : 4224 + 45 * mv_s.toNat + acap.toNat ≤ c.scratch_cap)
    (_hnv_pos : 1 ≤ nv.toNat) (hnv_le : nv.toNat ≤ mv_s.toNat) (_hnc_ge : 2 ≤ nc.toNat)
    (halen_le : alen.toNat ≤ acap.toNat)
    (hcls : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr)
    (hpre0 : ∀ i, i < 4002 → scr[i]? = scr0[i]?)
    (hpre1 : ∀ i, 4132 ≤ i → i < 4192 → scr[i]? = scr0[i]?)
    (hm : (FullMem c (FidP6Scr s scr) ⋆ R) m)
    (hTail : ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
      scr'.length = c.scratch_cap → FidK6BufOk scr' →
      scr'[4193]? = some nc → scr'[4194]? = some nc → scr'[4214]? = some mv_s →
      (∀ cid, cid < nc.toNat →
        let raw := scr'[4224 + 37 * mv_s.toNat + cid]?.getD 0#32
        raw.toNat < 4096 ∧ (raw &&& 2047#32).toNat < 2001) →
      (∀ i, i < 4002 → scr'[i]? = scr0[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = scr0[i]?) →
      (FullMem c (FidP6Scr s scr') ⋆ R) m' → wp Γ Q X K_tail m') :
    wp Γ Q X
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4192, ())) fun p0 =>
      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p0.fst, Arg.imm 4, ())) fun p1 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p1.fst, ())) fun p2 =>
      Expr.store (t := i32) (Arg.var nv) (Arg.var p2.fst)
        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4193, ())) fun p3 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p3.fst, Arg.imm 4, ())) fun p4 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p4.fst, ())) fun p5 =>
        Expr.store (t := i32) (Arg.var nc) (Arg.var p5.fst)
          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4194, ())) fun p6 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p6.fst, Arg.imm 4, ())) fun p7 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p7.fst, ())) fun p8 =>
          Expr.store (t := i32) (Arg.var nc) (Arg.var p8.fst)
            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4195, ())) fun p9 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p9.fst, Arg.imm 4, ())) fun p10 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p10.fst, ()))
              fun p11 =>
            Expr.store (t := i32) (Arg.imm 0) (Arg.var p11.fst)
              (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4196, ())) fun p12 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p12.fst, Arg.imm 4, ())) fun p13 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p13.fst, ()))
                fun p14 =>
              Expr.store (t := i32) (Arg.imm 0) (Arg.var p14.fst)
                (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4197, ())) fun p15 =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p15.fst, Arg.imm 4, ())) fun p16 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p16.fst, ()))
                  fun p17 =>
                Expr.store (t := i32) (Arg.imm 0) (Arg.var p17.fst)
                  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4198, ())) fun p18 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p18.fst, Arg.imm 4, ())) fun p19 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p19.fst, ()))
                    fun p20 =>
                  Expr.store (t := i32) (Arg.var nv) (Arg.var p20.fst)
                    (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4199, ())) fun p21 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p21.fst, Arg.imm 4, ())) fun p22 =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                      (Arg.var c.pScratchBuf, Arg.var p22.fst, ())) fun p23 =>
                    Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p23.fst)
                      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4200, ())) fun p24 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p24.fst, Arg.imm 4, ())) fun p25 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pScratchBuf, Arg.var p25.fst, ())) fun p26 =>
                      Expr.store (t := i32) (Arg.imm 0) (Arg.var p26.fst)
                        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4201, ())) fun p27 =>
                        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p27.fst, Arg.imm 4, ()))
                          fun p28 =>
                        Expr.let_ (Op.mk (OpCode.add i64)
                          (Arg.var c.pScratchBuf, Arg.var p28.fst, ())) fun p29 =>
                        Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var nv, Arg.imm 1, ())) fun p30 =>
                        Expr.store (Arg.var p30.fst) (Arg.var p29.fst)
                          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4202, ())) fun p31 =>
                          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p31.fst, Arg.imm 4, ()))
                            fun p32 =>
                          Expr.let_ (Op.mk (OpCode.add i64)
                            (Arg.var c.pScratchBuf, Arg.var p32.fst, ())) fun p33 =>
                          Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var nv, Arg.imm 1, ())) fun p34 =>
                          Expr.store (Arg.var p34.fst) (Arg.var p33.fst)
                            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4203, ())) fun p35 =>
                            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p35.fst, Arg.imm 4, ()))
                              fun p36 =>
                            Expr.let_ (Op.mk (OpCode.add i64)
                              (Arg.var c.pScratchBuf, Arg.var p36.fst, ())) fun p37 =>
                            Expr.store (t := i32) (Arg.var nv) (Arg.var p37.fst)
                              (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4204, ())) fun p38 =>
                              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p38.fst, Arg.imm 4, ()))
                                fun p39 =>
                              Expr.let_ (Op.mk (OpCode.add i64)
                                (Arg.var c.pScratchBuf, Arg.var p39.fst, ())) fun p40 =>
                              Expr.store (t := i32) (Arg.imm 0) (Arg.var p40.fst)
                                (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4205, ()))
                                  fun p41 =>
                                Expr.let_ (Op.mk (OpCode.mul i64)
                                  (Arg.var p41.fst, Arg.imm 4, ())) fun p42 =>
                                Expr.let_ (Op.mk (OpCode.add i64)
                                  (Arg.var c.pScratchBuf, Arg.var p42.fst, ())) fun p43 =>
                                Expr.store (t := i32) (Arg.var tick_lim) (Arg.var p43.fst)
                                  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4206, ()))
                                    fun p44 =>
                                  Expr.let_ (Op.mk (OpCode.mul i64)
                                    (Arg.var p44.fst, Arg.imm 4, ())) fun p45 =>
                                  Expr.let_ (Op.mk (OpCode.add i64)
                                    (Arg.var c.pScratchBuf, Arg.var p45.fst, ())) fun p46 =>
                                  Expr.store (t := i32) (Arg.var alen) (Arg.var p46.fst)
                                    (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4207, ()))
                                      fun p47 =>
                                    Expr.let_ (Op.mk (OpCode.mul i64)
                                      (Arg.var p47.fst, Arg.imm 4, ())) fun p48 =>
                                    Expr.let_ (Op.mk (OpCode.add i64)
                                      (Arg.var c.pScratchBuf, Arg.var p48.fst, ())) fun p49 =>
                                    Expr.store (t := i32) (Arg.var acap) (Arg.var p49.fst)
                                      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4208, ()))
                                        fun p50 =>
                                      Expr.let_ (Op.mk (OpCode.mul i64)
                                        (Arg.var p50.fst, Arg.imm 4, ())) fun p51 =>
                                      Expr.let_ (Op.mk (OpCode.add i64)
                                        (Arg.var c.pScratchBuf, Arg.var p51.fst, ())) fun p52 =>
                                      Expr.store (t := i32) (Arg.imm 0) (Arg.var p52.fst)
                                        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4209, ()))
                                          fun p53 =>
                                        Expr.let_ (Op.mk (OpCode.mul i64)
                                          (Arg.var p53.fst, Arg.imm 4, ())) fun p54 =>
                                        Expr.let_ (Op.mk (OpCode.add i64)
                                          (Arg.var c.pScratchBuf, Arg.var p54.fst, ())) fun p55 =>
                                        Expr.store (t := i32) (Arg.imm 0) (Arg.var p55.fst)
                                          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4210, ()))
                                            fun p56 =>
                                          Expr.let_ (Op.mk (OpCode.mul i64)
                                            (Arg.var p56.fst, Arg.imm 4, ())) fun p57 =>
                                          Expr.let_ (Op.mk (OpCode.add i64)
                                            (Arg.var c.pScratchBuf, Arg.var p57.fst, ())) fun p58 =>
                                          Expr.store (t := i32) (Arg.imm 0) (Arg.var p58.fst)
                                            (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                              (Arg.imm 4211, ()))
                                              fun p59 =>
                                            Expr.let_ (Op.mk (OpCode.mul i64)
                                              (Arg.var p59.fst, Arg.imm 4, ())) fun p60 =>
                                            Expr.let_ (Op.mk (OpCode.add i64)
                                              (Arg.var c.pScratchBuf, Arg.var p60.fst, ()))
                                              fun p61 =>
                                            Expr.store (t := i32) (Arg.var n_units)
                                              (Arg.var p61.fst)
                                              (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                                (Arg.imm 4212, ())) fun p62 =>
                                              Expr.let_ (Op.mk (OpCode.mul i64)
                                                (Arg.var p62.fst, Arg.imm 4, ())) fun p63 =>
                                              Expr.let_ (Op.mk (OpCode.add i64)
                                                (Arg.var c.pScratchBuf, Arg.var p63.fst, ()))
                                                fun p64 =>
                                              Expr.store (t := i32) (Arg.imm 0) (Arg.var p64.fst)
                                                (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                                  (Arg.imm 4213, ())) fun p65 =>
                                                Expr.let_ (Op.mk (OpCode.mul i64)
                                                  (Arg.var p65.fst, Arg.imm 4, ())) fun p66 =>
                                                Expr.let_ (Op.mk (OpCode.add i64)
                                                  (Arg.var c.pScratchBuf, Arg.var p66.fst, ()))
                                                  fun p67 =>
                                                Expr.store (t := i32) (Arg.imm 0) (Arg.var p67.fst)
                                                  (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                                    (Arg.imm 4214, ())) fun p68 =>
                                                  Expr.let_ (Op.mk (OpCode.mul i64)
                                                    (Arg.var p68.fst, Arg.imm 4, ())) fun p69 =>
                                                  Expr.let_ (Op.mk (OpCode.add i64)
                                                    (Arg.var c.pScratchBuf, Arg.var p69.fst, ()))
                                                    fun p70 =>
                                                  Expr.store (t := i32) (Arg.var mv_s)
                                                    (Arg.var p70.fst)
                                                    (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                                      (Arg.imm 4215, ())) fun p71 =>
                                                    Expr.let_ (Op.mk (OpCode.mul i64)
                                                      (Arg.var p71.fst, Arg.imm 4, ())) fun p72 =>
                                                    Expr.let_ (Op.mk (OpCode.add i64)
                                                      (Arg.var c.pScratchBuf, Arg.var p72.fst, ()))
                                                      fun p73 =>
                                                    Expr.store (t := i32) (Arg.var mc_s)
                                                      (Arg.var p73.fst)
                                                      (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                                        (Arg.imm 4216, ())) fun p74 =>
                                                      Expr.let_ (Op.mk (OpCode.mul i64)
                                                        (Arg.var p74.fst, Arg.imm 4, ()))
                                                        fun p75 =>
                                                      Expr.let_ (Op.mk (OpCode.add i64)
                                                        (Arg.var c.pScratchBuf, Arg.var p75.fst,
                                                          ())) fun p76 =>
                                                      Expr.store (t := i32) (Arg.var max_orig_s)
                                                        (Arg.var p76.fst)
      (Expr.group (fun Js : Tup Cont [[i32]] => Blocks.cons (fun pi : Tup Val [i32] =>
        Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pi.fst, Arg.var nv, ()))
          fun p77 =>
        Expr.jnz (Arg.var p77.fst)
          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 4224, Arg.var pi.fst, ())) fun p78 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p78.fst, ())) fun p79 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p79.fst, Arg.imm 4, ())) fun p80 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p80.fst, ())) fun p81 =>
          Expr.store (t := i32) (Arg.imm 0) (Arg.var p81.fst)
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_rsn, Arg.var pi.fst, ())) fun p82 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p82.fst, ())) fun p83 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p83.fst, Arg.imm 4, ())) fun p84 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p84.fst, ()))
              fun p85 =>
            Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p85.fst)
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_flags, Arg.var pi.fst, ())) fun p86 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p86.fst, ())) fun p87 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p87.fst, Arg.imm 4, ())) fun p88 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p88.fst, ()))
                fun p89 =>
              Expr.store (t := i32) (Arg.imm 0) (Arg.var p89.fst)
                (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_qst, Arg.var pi.fst, ())) fun p90 =>
                Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p90.fst, ())) fun p91 =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p91.fst, Arg.imm 4, ())) fun p92 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p92.fst, ()))
                  fun p93 =>
                Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ())) fun p94 =>
                Expr.store (Arg.var p94.fst) (Arg.var p93.fst)
                  (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_qprev, Arg.var pi.fst, ()))
                    fun p95 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p95.fst, ())) fun p96 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p96.fst, Arg.imm 4, ())) fun p97 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p97.fst, ()))
                    fun p98 =>
                  Expr.group (fun _Js_1 : Tup Cont [[i32]] => Blocks.cons (fun pq =>
                    Expr.store (Arg.var pq.fst) (Arg.var p98.fst)
                      (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_qnext, Arg.var pi.fst, ()))
                        fun p99 =>
                      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p99.fst, ())) fun p100 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p100.fst, Arg.imm 4, ()))
                        fun p101 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pScratchBuf, Arg.var p101.fst, ())) fun p102 =>
                      Expr.group (fun _Js_2 : Tup Cont [[i32]] => Blocks.cons (fun pqn =>
                        Expr.store (Arg.var pqn.fst) (Arg.var p102.fst)
                          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ()))
                            fun p103 => Expr.jump Js.fst (Arg.var p103.fst, ()))) Blocks.nil)
                        fun Js_2 =>
                      Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ())) fun p103 =>
                      Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
                        (Arg.var p103.fst, Arg.var nv, ())) fun p104 =>
                      Expr.jnz (Arg.var p104.fst)
                        (Expr.jump Js_2.fst (Arg.imm 4294967295, ()))
                        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ()))
                          fun p105 => Expr.jump Js_2.fst (Arg.var p105.fst, ())))) Blocks.nil)
                    fun Js_1 =>
                  Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                    (Arg.var pi.fst, Arg.imm 0, ())) fun p99 =>
                  Expr.jnz (Arg.var p99.fst)
                    (Expr.jump Js_1.fst (Arg.imm 4294967295, ()))
                    (Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var pi.fst, Arg.imm 1, ())) fun p100 =>
                    Expr.jump Js_1.fst (Arg.var p100.fst, ())))))))
          (Expr.group (fun Js_1 : Tup Cont [[i32]] => Blocks.cons (fun pi : Tup Val [i32] =>
            Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var nv, Arg.imm 1, ())) fun p78 =>
            Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pi.fst, Arg.var p78.fst, ()))
              fun p79 =>
            Expr.jnz (Arg.var p79.fst)
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_vals, Arg.var pi.fst, ())) fun p80 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p80.fst, ())) fun p81 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p81.fst, Arg.imm 4, ())) fun p82 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p82.fst, ()))
                fun p83 =>
              Expr.store (t := i32) (Arg.imm 0) (Arg.var p83.fst)
                (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_whead, Arg.var pi.fst, ())) fun p84 =>
                Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p84.fst, ())) fun p85 =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p85.fst, Arg.imm 4, ())) fun p86 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p86.fst, ()))
                  fun p87 =>
                Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p87.fst)
                  (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ())) fun p88 =>
                  Expr.jump Js_1.fst (Arg.var p88.fst, ()))))
              K_tail) Blocks.nil)
          fun Js_1 => Expr.jump Js_1.fst (Arg.imm 0, ()))) Blocks.nil)
      fun Js => Expr.jump Js.fst (Arg.imm 0, ())))))))))))))))))))))))))))
      m := by
  refine fid_k6c_init_hdr1_wp hcap hscr_len hpre0 hpre1 hm ?_
  intro scr1 m1 h1_len h1_93 h1_94 h1_hi h1_p0 h1_p1 hm1
  refine fid_k6c_init_hdr2_wp hcap h1_len h1_93 h1_94 h1_hi h1_p0 h1_p1 hm1 ?_
  intro scr2 m2 h2_len h2_93 h2_94 h2_06 h2_07 h2_14 h2_hi h2_p0 h2_p1 hm2
  refine fid_k6c_init_var_loop_wp hcap h2_len hmv_lo hmv_hi hoff_rsn hoff_qprev hoff_qnext
    hoff_qst hoff_flags hcap_ar hnv_le h2_93 h2_94 h2_06 h2_07 h2_14
    (fun i hi => h2_hi i (by omega)) h2_p0 h2_p1 hm2 ?_
  intro scrA m3 hlenA hA_93 hA_94 hA_06 hA_07 hA_14 hag_hi hp0_1 hp1_1 hm3
  exact fid_k6c_init_lit_loop_wp hcap (by omega) hmv_lo hmv_hi hoff_vals hoff_whead hcap_ar
    hnv_le halen_le hcls hlenA hA_93 hA_94 hA_06 hA_07 hA_14 hag_hi hp0_1 hp1_1 hm3 hTail
