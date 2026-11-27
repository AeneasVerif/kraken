module

public import LeanQbe.T.LeanLCNF.Sem.Perceus4
import LeanQbe.T.Logic.ProofKit

/-!
# LCNF Perceus-Sound Simulation: `inc` Step and Heap Helpers

Monotonicity and invariant preservation lemmas for `LcCode.inc` and shared heap
object updates in the LCNF P-tier → H-tier Perceus soundness proof (`L4b`).
-/

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T.LeanLCNF

section IncDelHelpers

/-- `NonPersistReach` is monotone when every well-formed object survives with the same address
    and child fields, persistent objects stay persistent, and positive-RC objects stay nonzero. -/
public theorem nonPersistReach_mono_rc_pos {objs objs' : List LcnfObj}
    (hmap : ∀ o ∈ objs, o.Wf → ∃ o' ∈ objs',
      o'.addr = o.addr ∧ o'.childFields = o.childFields ∧
      (o.rc = 0#32 → o'.rc = 0#32) ∧ (0 < o.rc.toInt → o'.rc ≠ 0#32))
    (hwf : ∀ o ∈ objs, o.Wf)
    {r a : BitVec 64} (hreach : NonPersistReach objs r a) :
    NonPersistReach objs' r a := by
  induction hreach with
  | refl h =>
    obtain ⟨o, ho, hoa, horc⟩ := h
    have howf := hwf o ho
    have hpos := rc_toInt_pos_of_ne_zero howf.2.2.1 horc
    obtain ⟨o', ho', hoa', _, _, horc'⟩ := hmap o ho howf
    exact NonPersistReach.refl ⟨o', ho', hoa' ▸ hoa, horc' hpos⟩
  | step _ hchild hev hnz ih =>
    obtain ⟨o, ho, hoa, hmem⟩ := hchild
    obtain ⟨o', ho', hoa', hcf', _, _⟩ := hmap o ho (hwf o ho)
    obtain ⟨ov, hov, hova, hovrc⟩ := hnz
    have hovwf := hwf ov hov
    have hpos := rc_toInt_pos_of_ne_zero hovwf.2.2.1 hovrc
    obtain ⟨ov', hov', hova', _, _, hovrc'⟩ := hmap ov hov hovwf
    exact NonPersistReach.step ih ⟨o', ho', hoa' ▸ hoa, hcf' ▸ hmem⟩ hev
      ⟨ov', hov', hova' ▸ hova, hovrc' hpos⟩

/-- `Backed` lifts along an RC-increasing heap map. -/
public theorem backed_mono_rc_pos {objs objs' : List LcnfObj}
    (hmap : ∀ o ∈ objs, o.Wf → ∃ o' ∈ objs',
      o'.addr = o.addr ∧ o'.childFields = o.childFields ∧
      (o.rc = 0#32 → o'.rc = 0#32) ∧ (0 < o.rc.toInt → o'.rc ≠ 0#32))
    (hwf : ∀ o ∈ objs, o.Wf)
    {r1 r2 : List (BitVec 64)} (hroots : ∀ r, r ∈ r1 → r ∈ r2)
    {a : BitVec 64} (hb : Backed objs r1 a) :
    Backed objs' r2 a := by
  rcases hb with ⟨o, ho, hoa, horc⟩ | ⟨r, hr, hreach⟩
  · obtain ⟨o', ho', hoa', _, horc', _⟩ := hmap o ho (hwf o ho)
    exact Or.inl ⟨o', ho', hoa' ▸ hoa, horc' horc⟩
  · exact Or.inr ⟨r, hroots r hr, nonPersistReach_mono_rc_pos hmap hwf hreach⟩

/-- Element upper bound by list sum for `Nat`. -/
public theorem nat_le_sum_of_mem {a : Nat} {xs : List Nat} (hm : a ∈ xs) : a ≤ xs.sum := by
  induction xs with
  | nil => cases hm
  | cons x rest ih =>
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hrest
    · simp
    · have := ih hrest; simp; omega

/-- Distinctness of mapped keys implies `getElem` injectivity. -/
public theorem nodup_map_getElem_inj {α β : Type} {xs : List α} {f : α → β}
    (hn : (xs.map f).Nodup) {i j : Nat} (hi : i < xs.length) (hj : j < xs.length)
    (heq : f xs[i] = f xs[j]) : i = j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons x rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        exfalso
        have hj' : j' < rest.length := by simp at hj; omega
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact hn.1 (List.mem_map.mpr ⟨rest[j'], List.getElem_mem hj', heq.symm⟩)
    | succ i' =>
      cases j with
      | zero =>
        exfalso
        have hi' : i' < rest.length := by simp at hi; omega
        simp only [List.getElem_cons_succ, List.getElem_cons_zero] at heq
        exact hn.1 (List.mem_map.mpr ⟨rest[i'], List.getElem_mem hi', heq⟩)
      | succ j' =>
        simp only [List.getElem_cons_succ] at heq
        have hi' : i' < rest.length := by simp at hi; omega
        have hj' : j' < rest.length := by simp at hj; omega
        exact congrArg Nat.succ (ih hn.2 hi' hj' heq)

/-- `nonPersistRefs` is strictly positive when a non-persistent heap object points to `a`. -/
public theorem nonPersistRefs_pos_of_mem_cf {objs : List LcnfObj} {o : LcnfObj} {a : BitVec 64}
    (ho : o ∈ objs) (hrc : o.rc ≠ 0#32) (hcf : a ∈ o.childFields) :
    0 < nonPersistRefs objs a := by
  obtain ⟨idx, hidx, hget⟩ := obj_mem_idx ho
  rw [nonPersistRefs_focus objs hidx a, hget]
  simp only [hrc, ite_false]
  have hpos : 0 < List.count a o.childFields := List.count_pos_iff.mpr hcf
  omega

/-- Updating only `o.rc` (preserving `rc = 0#32 ↔ rc' = 0#32`) preserves `nonPersistRefs`. -/
public theorem nonPersistRefs_set_withRc {objs : List LcnfObj}
    {idx : Nat} (hidx : idx < objs.length)
    {rc' : BitVec 32} (hflag : objs[idx].rc = 0#32 ↔ rc' = 0#32) (a : BitVec 64) :
    nonPersistRefs (objs.set idx (objs[idx].withRc rc')) a = nonPersistRefs objs a := by
  have hidx' : idx < (objs.set idx (objs[idx].withRc rc')).length := by simp [hidx]
  rw [nonPersistRefs_focus objs hidx a, nonPersistRefs_focus _ hidx' a]
  have hget : (objs.set idx (objs[idx].withRc rc'))[idx] = objs[idx].withRc rc' := by simp
  have hcf : (objs[idx].withRc rc').childFields = objs[idx].childFields := rfl
  have her : (objs.set idx (objs[idx].withRc rc')).eraseIdx idx = objs.eraseIdx idx := by
    simp [List.eraseIdx_eq_take_drop_succ, List.take_set_of_le, List.drop_set_of_lt]
  rw [hget, hcf, her]
  by_cases h0 : objs[idx].rc = 0#32
  · have h0' : rc' = 0#32 := hflag.mp h0
    simp [LcnfObj.withRc, h0, h0']
  · have h0' : rc' ≠ 0#32 := fun hc => h0 (hflag.mpr hc)
    simp [LcnfObj.withRc, h0, h0']

/-- Any object in `objs` with `o.addr ≠ objs[idx].addr` survives in `objs.eraseIdx idx`. -/
public theorem mem_eraseIdx_of_addr_ne {objs : List LcnfObj} {idx : Nat} (hidx : idx < objs.length)
    {o : LcnfObj} (ho : o ∈ objs) (hne : o.addr ≠ objs[idx].addr) :
    o ∈ objs.eraseIdx idx := by
  induction objs generalizing idx with
  | nil => simp at hidx
  | cons q rest ih =>
    cases idx with
    | zero =>
      simp only [List.mem_cons] at ho
      rcases ho with rfl | hrest
      · exfalso; exact hne rfl
      · simpa [List.eraseIdx_zero] using hrest
    | succ idx' =>
      simp only [List.eraseIdx_cons_succ, List.mem_cons] at ho ⊢
      rcases ho with rfl | hrest
      · exact Or.inl rfl
      · exact Or.inr (ih (by simp at hidx; omega) hrest hne)

/-- Every member of `objs.eraseIdx idx` belongs to `objs` and has `addr ≠ objs[idx].addr`. -/
public theorem mem_of_mem_eraseIdx_nodup {objs : List LcnfObj}
    (hnodup : (objs.map LcnfObj.addr).Nodup) {idx : Nat} (hidx : idx < objs.length)
    {o : LcnfObj} (ho : o ∈ objs.eraseIdx idx) :
    o ∈ objs ∧ o.addr ≠ objs[idx].addr := by
  induction objs generalizing idx with
  | nil => simp at hidx
  | cons q rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    cases idx with
    | zero =>
      simp only [List.eraseIdx_zero, List.tail_cons] at ho
      refine ⟨List.mem_cons_of_mem q ho, ?_⟩
      intro heq
      exact hnodup.1 (List.mem_map.mpr ⟨o, ho, heq⟩)
    | succ idx' =>
      have hidx' : idx' < rest.length := by simp at hidx; omega
      simp only [List.eraseIdx_cons_succ, List.mem_cons] at ho
      rcases ho with rfl | hrest
      · refine ⟨List.mem_cons_self, ?_⟩
        intro heq
        exact hnodup.1 (List.mem_map.mpr ⟨rest[idx'], List.getElem_mem hidx', heq.symm⟩)
      · obtain ⟨hm, hne⟩ := ih hnodup.2 hidx' hrest
        exact ⟨List.mem_cons_of_mem q hm, hne⟩

/-- `LcnfObj.Wf` is preserved by `withRc rc'` when `0 ≤ rc'.toInt`. -/
public theorem lcnfObj_wf_withRc {o : LcnfObj} (hwf : o.Wf)
    {rc' : BitVec 32} (hnn : 0 ≤ rc'.toInt) :
    (o.withRc rc').Wf := by
  rcases hwf with ⟨h1, h2, _, h4, h5, h6, h7, h8, h9, h10⟩
  cases o
  exact ⟨h1, h2, hnn, h4, h5, h6, h7, h8, h9, h10⟩

end IncDelHelpers

section IncStep

/-- `CleanVar` is preserved by `.inc` on a non-noRc, non-persistent variable. -/
public theorem inc_cleanVar {v : RcVar} (hcv : CleanVar v) (hno : v.noRc = false)
    (hpers : v.persistent = false) (n : Nat) :
    CleanVar { v with owned := v.owned + n, excl := false } := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, hcv.2.2.2.2⟩
  · intro hn; simp [hno] at hn
  · exact hcv.1.2
  · intro hp; simp [hpers] at hp
  · intro _; exact ⟨hno, hpers, rfl⟩
  · exact hcv.2.2.2.1

/-- `ParentsOwned` is preserved by `.inc` (`ctx.put v'`). -/
public theorem inc_parentsOwned {ctx : RcCtx} (hnodup : (ctx.vars.map RcVar.id).Nodup)
    (hclean : CleanVars ctx) (hpo : ParentsOwned ctx)
    {v : RcVar} (hv : v ∈ ctx.vars) (hno : v.noRc = false)
    (hpers : v.persistent = false) {n : Nat} (hn : 0 < n) :
    ParentsOwned (ctx.put { v with owned := v.owned + n, excl := false }) := by
  let v' : RcVar := { v with owned := v.owned + n, excl := false }
  intro u hu p hup
  rw [RcCtx.put_mem_iff hnodup] at hu
  rcases hu with rfl | ⟨hu_mem, _⟩
  · obtain ⟨pv, hpv_mem, hpv_id, hpv_no, hpv_pers, hpv_pos, hpv_bor⟩ := hpo v hv p hup
    have hv_bor : v.borrowed = true := by
      cases hb : v.borrowed
      · have := (hclean v hv).2.2.2.1 hb; rw [this] at hup; cases hup
      · rfl
    have hne : pv.id ≠ v'.id := by
      intro heq
      have heq' : pv = v := rcVar_eq_of_mem_nodup hnodup hpv_mem hv heq
      rw [heq'] at hpv_bor
      rw [hpv_bor] at hv_bor
      cases hv_bor
    refine ⟨pv, (RcCtx.put_mem_iff hnodup).mpr (Or.inr ⟨hpv_mem, hne⟩),
      hpv_id, hpv_no, hpv_pers, hpv_pos, hpv_bor⟩
  · obtain ⟨pv, hpv_mem, hpv_id, hpv_no, hpv_pers, hpv_pos, hpv_bor⟩ := hpo u hu_mem p hup
    by_cases hpid : pv.id = v'.id
    · have hpv_eq : pv = v := rcVar_eq_of_mem_nodup hnodup hpv_mem hv hpid
      refine ⟨v', (RcCtx.put_mem_iff hnodup).mpr (Or.inl rfl),
        ?_, hno, hpers, by simp [v']; omega, ?_⟩
      · simp [v', ← hpv_eq, hpv_id]
      · simp [v', ← hpv_eq, hpv_bor]
    · exact ⟨pv, (RcCtx.put_mem_iff hnodup).mpr (Or.inr ⟨hpv_mem, hpid⟩),
        hpv_id, hpv_no, hpv_pers, hpv_pos, hpv_bor⟩

/-- Handle counts after `.inc` when `v.owned` increases by `n`. -/
public theorem inc_frameHandles_count {rf : RcFrame}
    (hnodup : (rf.ctx.vars.map RcVar.id).Nodup) (hclean : CleanVars rf.ctx)
    {x n : Nat} {v : RcVar} (hget : rf.ctx.get? x = some v)
    (hno : v.noRc = false) (hpers : v.persistent = false)
    {bv : BitVec 64} (henvh : rf.envH x = some (v.ty, Word.i64 bv)) :
    let v' : RcVar := { v with owned := v.owned + n, excl := false }
    let rf' : RcFrame := { rf with ctx := rf.ctx.put v' }
    ∀ a, List.count a (frameHandles rf') =
      List.count a (frameHandles rf) +
        (if bv &&& 1#64 = 0#64 then if a = bv then n else 0 else 0) := by
  intro v' rf' a
  obtain ⟨hvm, rfl⟩ := RcCtx.get?_mem hget
  have hrt : v.resetTok = false := (hclean v hvm).2.2.2.2
  have hput := localHandles_put_perm hnodup rf.envH v'
  have hcur := localHandles_perm_filter hnodup rf.envH v hvm
  have hvid : v'.id = v.id := rfl
  rw [hvid] at hput
  simp only [frameHandles, rf']
  rw [List.count_append, List.count_append, List.count_append, List.count_append,
    hput.count_eq a, hcur.count_eq a, List.count_append, List.count_append]
  have htbv : (Word.i64 bv).toBV64? = some bv := rfl
  have hvh : List.count a (varHandles rf.envH v') =
      List.count a (varHandles rf.envH v) +
        (if bv &&& 1#64 = 0#64 then if a = bv then n else 0 else 0) := by
    by_cases hev : bv &&& 1#64 = 0#64
    · by_cases hn0 : n = 0
      · subst hn0
        have hveq : varHandles rf.envH v' = varHandles rf.envH v := by simp [varHandles, v']
        simp [hev, hveq]
      · have hpos' : (v.owned + n == 0) = false := by simp; omega
        have hv' : varHandles rf.envH v' = List.replicate (v.owned + n) bv := by
          simp [varHandles, v', hno, hpers, hrt, hpos', henvh, htbv, hev]
        by_cases ho0 : v.owned = 0
        · have hv0 : varHandles rf.envH v = [] := by simp [varHandles, ho0]
          rw [hv', hv0, ho0, Nat.zero_add, List.count_nil, Nat.zero_add]
          simp only [hev, ite_true, List.count_replicate]
          by_cases ha : a = bv
          · subst ha; simp
          · simp [ha, Ne.symm ha]
        · have hpos : (v.owned == 0) = false := by simp [ho0]
          have hv : varHandles rf.envH v = List.replicate v.owned bv := by
            simp [varHandles, hno, hpers, hrt, hpos, henvh, htbv, hev]
          rw [hv', hv]
          simp only [hev, ite_true, List.count_replicate]
          by_cases ha : a = bv
          · subst ha; simp
          · simp [ha, Ne.symm ha]
    · have hv0 : varHandles rf.envH v = [] := by
        cases hown : v.owned == 0
        · simp [varHandles, hno, hpers, hrt, hown, henvh, htbv, hev]
        · simp [varHandles, hno, hpers, hrt, hown]
      have hv'0 : varHandles rf.envH v' = [] := by
        cases hown : v.owned + n == 0
        · simp [varHandles, v', hno, hpers, hrt, hown, henvh, htbv, hev]
        · simp [varHandles, v', hno, hpers, hrt, hown]
      simp [hv0, hv'0, hev]
  omega

/-- An incremented heap variable `x` cannot alias an exclusive `SharedPredInv` zero target
`s ≠ x`. -/
public theorem inc_bv_ne_shared_zero {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (_ : ParentsOwned rf.ctx)
    (hpcb : ParentChildBacked rf σ.objs)
    {x : Nat} {v : RcVar} (hget : rf.ctx.get? x = some v) (hlive : v.isLive = true)
    (hno : v.noRc = false) (hpers : v.persistent = false)
    {bv : BitVec 64} (henvh : rf.envH x = some (v.ty, Word.i64 bv)) (hev : bv &&& 1#64 = 0#64)
    {p : Nat × Nat} (hp : p ∈ rf.ctx.sharedPreds) (hpne : p.2 ≠ x)
    {vb vs : RcVar} (hgb : rf.ctx.get? p.1 = some vb) (hgs : rf.ctx.get? p.2 = some vs)
    (hblive : vb.isLive = true) (hsno : vs.noRc = false) (hspers : vs.persistent = false)
    (htag : (rf.envP p.1).bind PVal.tag? = some 0) (hspos : 0 < vs.owned)
    {bvs : BitVec 64} (henvs : rf.envH p.2 = some (vs.ty, Word.i64 bvs)) :
    bv ≠ bvs := by
  intro heq
  subst heq
  obtain ⟨hheap, _, hsound, hvars, hsp⟩ := hinv
  have hsp_p := (hsp p hp vb vs hgb hgs hblive hsno hspers).1 htag
  obtain ⟨bvs', henvs', _, hrest⟩ := hsp_p
  rw [henvs] at henvs'
  cases henvs'
  obtain ⟨hcnt0, o_s, ho_s, ho_sa, ho_src⟩ := hrest hspos
  have ho_snz : o_s.rc ≠ 0#32 := by
    intro h0
    rw [h0] at ho_src
    change (0#32).toNat = vs.owned at ho_src
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at ho_src
    omega
  obtain ⟨hvm, rfl⟩ := RcCtx.get?_mem hget
  have hrt : v.resetTok = false := (hclean v hvm).2.2.2.2
  by_cases hvpos : 0 < v.owned
  · have hown0 : (v.owned == 0) = false := by simp; omega
    have htbv : (Word.i64 bv).toBV64? = some bv := rfl
    have hcnt_v : 0 < List.count bv (varHandles rf.envH v) := by
      simp [varHandles, hno, hpers, hrt, hown0, henvh, htbv, hev]
      omega
    have hvfilt : v ∈ rf.ctx.vars.filter (fun u => u.id != p.2) :=
      List.mem_filter.mpr ⟨hvm, by simp [hpne.symm]⟩
    have hcnt_ex : 0 < List.count bv (localHandlesExcept rf.ctx rf.envH p.2) := by
      simp only [localHandlesExcept, count_flatten]
      have hmem_map : List.count bv (varHandles rf.envH v) ∈
          (List.map (varHandles rf.envH) (rf.ctx.vars.filter (fun u => u.id != p.2))).map
            (List.count bv) :=
        List.mem_map.mpr ⟨varHandles rf.envH v, List.mem_map.mpr ⟨v, hvfilt, rfl⟩, rfl⟩
      exact Nat.lt_of_lt_of_le hcnt_v (nat_le_sum_of_mem hmem_map)
    rw [List.count_append, List.count_append] at hcnt0
    omega
  · have hv0 : v.owned = 0 := by omega
    have hbor : v.borrowed = true := by
      have hlive' := hlive
      simp [RcVar.isLive, hno, hpers, hrt, hv0] at hlive'
      exact hlive'
    obtain ⟨_, _, _, hh_v, _, hnon⟩ := hvars v hvm hlive
    have hnonsc : ¬v.ty.isScalar = true :=
      fun hs => by have := (hclean v hvm).1.2 hs; simp [hno] at this
    obtain ⟨bvv, hweq_v, _, _, _, hbor_v⟩ := hnon hnonsc
    have heqv := henvh.symm.trans (hweq_v ▸ hh_v)
    cases heqv
    have hbk := hbor_v hno hpers hbor hev
    have hnot_ext : ¬Backed σ.objs (rf.extH ++ rf.ghostH) bv := by
      apply not_backed_of_excl hheap.2 ho_s ho_sa ho_snz (by omega)
      simp only [List.count_append] at hcnt0 ⊢
      omega
    cases hpar : v.parent? with
    | none =>
      have hbk0 := hbk.2
      rw [hpar] at hbk0
      exact hnot_ext hbk0
    | some q =>
      rcases hpcb v hvm hlive hno hpers hbor q hpar bv henvh hev with hext | hch
      · exact hnot_ext hext
      · obtain ⟨_, o_q, _, _, ho_q, o_mid, hom_m, hreach_mid, hcf⟩ := hch
        by_cases hqrc : o_mid.rc = 0#32
        · obtain ⟨q0, hq0, hq0a, hq0rc⟩ := hsound.1 o_mid hom_m hqrc bv hcf hev
          have hqeq : q0 = o_s := obj_eq_of_addr_nodup hheap.2 hq0 ho_s (hq0a.trans ho_sa.symm)
          rw [hqeq] at hq0rc
          exact ho_snz hq0rc
        · have hpos_np := nonPersistRefs_pos_of_mem_cf hom_m hqrc hcf
          omega

/-- Tagged-value `.inc` preserves `RcInv`, `CleanVars`, `ParentsOwned`, `NoRcCorrect`,
    `ParentChildBacked`, `SharedTargetsHeap`, `HandlesInHeap`, and `EntryPres`. -/
public theorem inc_tag_rcInv {rt : BitVec 64} {rf rf0 : RcFrame} {σ σ0 : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ)
    {x n : Nat} {v : RcVar} (hget : rf.ctx.get? x = some v) (hlive : v.isLive = true)
    (hno : v.noRc = false) (hpers : v.persistent = false) (hn : 0 < n)
    {bv : BitVec 64} (henvh : rf.envH x = some (v.ty, Word.i64 bv))
    (hodd : bv &&& 1#64 ≠ 0#64) :
    let v' : RcVar := { v with owned := v.owned + n, excl := false }
    let rf' : RcFrame := { rf with ctx := rf.ctx.put v' }
    RcInv rt rf' σ ∧ CleanVars rf'.ctx ∧ ParentsOwned rf'.ctx ∧ NoRcCorrect rf'.ctx ∧
      ParentChildBacked rf' σ.objs ∧ SharedTargetsHeap rf' ∧
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ.objs ∧ EntryPres rf0 σ0 rf' σ := by
  intro v' rf'
  obtain ⟨hheap, hnodup, hsound, hvars, hsp⟩ := hinv
  obtain ⟨hvm, rfl⟩ := RcCtx.get?_mem hget
  have hcv' : CleanVar v' := inc_cleanVar (hclean v hvm) hno hpers n
  have hnodup' : (rf'.ctx.vars.map RcVar.id).Nodup := RcCtx.put_nodup hnodup v'
  have hclean' : CleanVars rf'.ctx := cleanVars_put hnodup hclean hcv'
  have hpo' : ParentsOwned rf'.ctx := inc_parentsOwned hnodup hclean hpo hvm hno hpers hn
  have hcnt_eq : ∀ a, List.count a (frameHandles rf') = List.count a (frameHandles rf) := by
    intro a
    have hc := inc_frameHandles_count (n := n) hnodup hclean hget hno hpers henvh a
    simpa [hodd] using hc
  have hperm : (frameHandles rf').Perm (frameHandles rf) :=
    List.perm_iff_count.mpr hcnt_eq
  have hsound' : HandlesRcSound (frameHandles rf') σ.objs :=
    handlesRcSound_of_perm hperm.symm hsound
  have hvars' : ∀ u ∈ rf'.ctx.vars, VarInv u rf' σ.objs := by
    intro u hu hulive
    rw [RcCtx.put_mem_iff hnodup] at hu
    rcases hu with rfl | ⟨hu_mem, _⟩
    · obtain ⟨pu, wu, hp, hh, hrep, hnon⟩ := hvars v hvm hlive
      refine ⟨pu, wu, hp, hh, hrep, ?_⟩
      intro hns
      obtain ⟨bvu, hwu, hno_u, hpers_u, _, hbor_u⟩ := hnon hns
      refine ⟨bvu, hwu, hno_u, hpers_u, ?_, ?_⟩
      · intro hex; simp [v'] at hex
      · intro _ _ _ hevu
        have heq := henvh.symm.trans (hwu ▸ hh)
        cases heq
        exact absurd hevu hodd
    · obtain ⟨pu, wu, hp, hh, hrep, hnon⟩ := hvars u hu_mem hulive
      refine ⟨pu, wu, hp, hh, hrep, ?_⟩
      intro hns
      obtain ⟨bvu, hwu, hno_u, hpers_u, hex_u, hbor_u⟩ := hnon hns
      refine ⟨bvu, hwu, hno_u, hpers_u, hex_u, ?_⟩
      intro hno' hpers' hbor' hevu
      obtain ⟨hbk1, hbk2⟩ := hbor_u hno' hpers' hbor' hevu
      refine ⟨backed_mono_roots (fun r hr => hperm.symm.mem_iff.mp hr) hbk1, ?_⟩
      cases hpar : u.parent? with
      | none => rw [hpar] at hbk2; exact hbk2
      | some p =>
        rw [hpar] at hbk2
        obtain ⟨pv, hpv_mem, hpv_id, hpv_no, hpv_pers, hpv_pos, hpv_bk⟩ := hbk2
        by_cases hpid : pv.id = v'.id
        · have hpv_eq : pv = v := rcVar_eq_of_mem_nodup hnodup hpv_mem hvm hpid
          refine ⟨v', (RcCtx.put_mem_iff hnodup).mpr (Or.inl rfl),
            by simp [v', ← hpv_eq, hpv_id], hno, hpers, Or.inl (by simp [v']; omega), hpv_bk⟩
        · exact ⟨pv, (RcCtx.put_mem_iff hnodup).mpr (Or.inr ⟨hpv_mem, hpid⟩),
            hpv_id, hpv_no, hpv_pers, hpv_pos, hpv_bk⟩
  have hsp' : SharedPredInv rf' σ.objs := by
    intro p hp vb vs hgb hgs hblive hsno hspers
    have hp_old : p ∈ rf.ctx.sharedPreds := hp
    have hnot_x : p.2 ≠ v.id := by
      intro heq
      obtain ⟨bvs, henvs, hbevs⟩ := hsth p hp_old v (by rw [heq]; exact hget) hno
      have hheq : rf.envH v.id = some (v.ty, Word.i64 bvs) := heq ▸ henvs
      have := henvh.symm.trans hheq
      cases this
      exact hodd hbevs
    have hgs_old : rf.ctx.get? p.2 = some vs := by
      rw [RcCtx.put_get? hnodup] at hgs
      have hne : (p.2 == v'.id) = false := beq_false_of_ne hnot_x
      simp [hne] at hgs
      exact hgs
    have hgb_old : ∃ vb0, rf.ctx.get? p.1 = some vb0 ∧ vb0.isLive = true := by
      rw [RcCtx.put_get? hnodup] at hgb
      by_cases hp1 : p.1 = v'.id
      · simp [hp1] at hgb; subst hgb; exact ⟨v, hp1.symm ▸ hget, hlive⟩
      · simp [hp1] at hgb; exact ⟨vb, hgb, hblive⟩
    obtain ⟨vb0, hgb0, hblive0⟩ := hgb_old
    have hsp_old := hsp p hp_old vb0 vs hgb0 hgs_old hblive0 hsno hspers
    have hex_perm : (localHandlesExcept rf'.ctx rf.envH p.2).Perm
        (localHandlesExcept rf.ctx rf.envH p.2) := by
      apply List.perm_iff_count.mpr
      intro a
      have h_all := localHandles_count_eq_add hnodup rf.envH (RcCtx.get?_mem hgs_old).1 a
      have h_all' := localHandles_count_eq_add hnodup' rf.envH (RcCtx.get?_mem hgs).1 a
      have hvs_id : vs.id = p.2 := (RcCtx.get?_mem hgs).2
      have hc := inc_frameHandles_count (n := n) hnodup hclean hget hno hpers henvh a
      simp only [frameHandles, List.count_append, hodd, ite_false, Nat.add_zero] at hc
      dsimp only [rf', v'] at hc h_all' ⊢
      rw [hvs_id] at h_all h_all'
      omega
    refine ⟨fun htag => ?_, fun htag hspos => ?_⟩
    · obtain ⟨bvs, henvs, hevs, hrest⟩ := hsp_old.1 htag
      refine ⟨bvs, henvs, hevs, fun hspos => ?_⟩
      obtain ⟨hc0, o_s, ho_s, ho_sa, ho_src⟩ := hrest hspos
      refine ⟨?_, o_s, ho_s, ho_sa, ho_src⟩
      rw [List.count_append, List.count_append, hex_perm.count_eq bvs]
      rw [List.count_append, List.count_append] at hc0
      exact hc0
    · exact hsp_old.2 htag hspos
  have hnorc' : NoRcCorrect rf'.ctx :=
    noRcCorrect_put hnodup hnorc (fun _ => hnorc v hvm hno)
  have hpcb' : ParentChildBacked rf' σ.objs := by
    intro u hu hulive huno hupers hubor q hpar bvu henvu hevu
    rw [RcCtx.put_mem_iff hnodup] at hu
    rcases hu with rfl | ⟨hu_mem, _⟩
    · have := henvh.symm.trans henvu; cases this; exact absurd hevu hodd
    · exact hpcb u hu_mem hulive huno hupers hubor q hpar bvu henvu hevu
  have hsth' : SharedTargetsHeap rf' :=
    sharedTargetsHeap_put_same hnodup hsth hget rfl rfl rfl
  have hepres' : EntryPres rf0 σ0 rf' σ :=
    entryPres_put_same_var hnodup hvm rfl rfl (fun _ => hlive) hepres
  exact ⟨⟨hheap, hnodup', hsound', hvars', hsp'⟩, hclean', hpo', hnorc',
    hpcb', hsth', hhih, hepres'⟩

/-- `HeapClean` and `HandlesRcSound` preservation for heap-pointer `.inc`. -/
public theorem inc_heap_clean_sound {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx)
    {x n : Nat} {v : RcVar} (hget : rf.ctx.get? x = some v)
    (hno : v.noRc = false) (hpers : v.persistent = false)
    {bv : BitVec 64} (henvh : rf.envH x = some (v.ty, Word.i64 bv)) (hev : bv &&& 1#64 = 0#64)
    {idx : Nat} (hidx : idx < σ.objs.length) (haddr : σ.objs[idx].addr = bv)
    (hbd : 0 < σ.objs[idx].rc.toInt → σ.objs[idx].rc.toNat + n < 2 ^ 31 - 1) :
    let v' : RcVar := { v with owned := v.owned + n, excl := false }
    let o := σ.objs[idx]
    let rc' := if 0 < o.rc.toInt then o.rc + BitVec.ofNat 32 n else o.rc
    let σ' : HState :=
      { st := σ.st, objs := σ.objs.set idx (o.withRc rc'),
        scr := σ.scr, scrLimbs := σ.scrLimbs }
    let rf' : RcFrame := { rf with ctx := rf.ctx.put v' }
    HeapClean rt σ' ∧
      HandlesRcSound (frameHandles rf') σ'.objs ∧
      (∀ q ∈ σ.objs, q.Wf → ∃ q' ∈ σ'.objs,
        ObjDataEq q q' ∧ (q.rc = 0#32 → q'.rc = 0#32) ∧
        (0 < q.rc.toInt → 0 < q'.rc.toInt) ∧ (q'.rc = 0#32 → q.rc = 0#32)) ∧
      (0 < o.rc.toInt → rc'.toNat = o.rc.toNat + n ∧ rc'.toNat < 2 ^ 31 - 1 ∧ 0 < rc'.toInt) ∧
      (o.rc = 0#32 ↔ rc' = 0#32) := by
  intro v' o rc' σ' rf'
  obtain ⟨hheap, hnodup, hsound, _, _⟩ := hinv
  obtain ⟨hbn, hwf_all, hclosed, hcap, hrc_all⟩ := hheap.1
  have hnodup_objs := hheap.2
  have howf : o.Wf := hwf_all o (List.getElem_mem hidx)
  have hrc'_props : (o.rc = 0#32 → rc' = 0#32) ∧
      (0 < o.rc.toInt → rc'.toNat = o.rc.toNat + n ∧ rc'.toNat < 2 ^ 31 - 1 ∧
        0 < rc'.toInt) ∧
      0 ≤ rc'.toInt ∧ rc'.toNat < 2 ^ 31 - 1 := by
    by_cases hpos : 0 < o.rc.toInt
    · have hne0 : o.rc ≠ 0#32 := by intro h0; simp [h0] at hpos
      obtain ⟨heq, hlt⟩ := rc_add_nat_eq (hbd hpos)
      obtain ⟨hnn, htoInt⟩ := rc_lt_bound_of_toNat hlt
      have hoeq : o = σ.objs[idx] := rfl
      have hrc_def : rc' = o.rc + BitVec.ofNat 32 n := by simp [rc', hpos]
      rw [← hoeq] at heq hlt hnn htoInt
      rw [← hrc_def] at heq hlt hnn htoInt
      have ho_pos : 0 < o.rc.toNat := by
        have := (rc_lt_bound_of_toNat (hrc_all o (List.getElem_mem hidx))).2
        omega
      have hrc_pos : 0 < rc'.toInt := by omega
      exact ⟨fun h0 => absurd h0 hne0, fun _ => ⟨heq, hlt, hrc_pos⟩, hnn, hlt⟩
    · have h0i : o.rc.toInt = (0#32).toInt := by
        have := howf.2.2.1; simp only [BitVec.toInt_zero]; omega
      have h0 : o.rc = 0#32 := BitVec.eq_of_toInt_eq h0i
      refine ⟨fun _ => by simp [rc', h0], fun hp => absurd hp hpos,
        by simp [rc', h0], by simp [rc', h0]⟩
  have hidx_len : idx < σ'.objs.length := by simp [σ', hidx]
  have hmap : ∀ q ∈ σ.objs, q.Wf → ∃ q' ∈ σ'.objs,
      ObjDataEq q q' ∧ (q.rc = 0#32 → q'.rc = 0#32) ∧
      (0 < q.rc.toInt → 0 < q'.rc.toInt) ∧
      (q'.rc = 0#32 → q.rc = 0#32) := by
    intro q hq hqwf
    obtain ⟨j, hj, hget_j⟩ := obj_mem_idx hq
    by_cases hji : j = idx
    · subst hji
      have hqeq : q = o := hget_j.symm
      subst hqeq
      refine ⟨o.withRc rc', ?_, objDataEq_withRc howf rc' hrc'_props.2.2.1,
        hrc'_props.1, fun hp => (hrc'_props.2.1 hp).2.2, fun h0 => ?_⟩
      · rw [show σ'.objs = σ.objs.set j (o.withRc rc') from rfl]
        exact List.mem_iff_getElem.mpr ⟨j, hidx_len, by simp⟩
      · by_cases hne0 : o.rc = 0#32
        · exact hne0
        · exfalso
          have hpos := rc_toInt_pos_of_ne_zero howf.2.2.1 hne0
          have hpos' := (hrc'_props.2.1 hpos).2.2
          have h0' : rc' = 0#32 := by simpa [LcnfObj.withRc] using h0
          simp [h0'] at hpos'
    · refine ⟨q, ?_, objDataEq_refl q hqwf, id, id, id⟩
      dsimp only [σ']
      exact (list_mem_set_iff hidx).mpr (Or.inr ⟨j, hj, hji, hget_j⟩)
  have hnodup_objs' : (σ'.objs.map LcnfObj.addr).Nodup := by
    dsimp only [σ']
    rw [list_map_addr_set_eq hidx (by rfl)]
    exact hnodup_objs
  have hwf_all' : ∀ q' ∈ σ'.objs, q'.Wf := by
    intro q' hq'
    dsimp only [σ'] at hq'
    rw [list_mem_set_iff hidx] at hq'
    rcases hq' with rfl | ⟨j, hj, _, hget_j⟩
    · exact lcnfObj_wf_withRc howf hrc'_props.2.2.1
    · rw [← hget_j]; exact hwf_all _ (List.getElem_mem hj)
  have hclosed' : lcnfHeapClosed σ'.objs := by
    intro q' hq' f hf hevf
    dsimp only [σ'] at hq'
    rw [list_mem_set_iff hidx] at hq'
    have ⟨q, hq, hqcf⟩ : ∃ q ∈ σ.objs, q.childFields = q'.childFields := by
      rcases hq' with rfl | ⟨j, hj, _, hget_j⟩
      · exact ⟨o, List.getElem_mem hidx, rfl⟩
      · exact ⟨q', hget_j ▸ List.getElem_mem hj, rfl⟩
    rw [← hqcf] at hf
    obtain ⟨t, ht, hta⟩ := hclosed q hq f hf hevf
    obtain ⟨t', ht', htdeq, _⟩ := hmap t ht (hwf_all t ht)
    exact ⟨t', ht', htdeq.1.trans hta⟩
  have hcap' : σ'.objs.length ≤ σ'.st.workCap := by simpa [σ'] using hcap
  have hrc_all' : ∀ q' ∈ σ'.objs, q'.rc.toNat < 2 ^ 31 - 1 := by
    intro q' hq'
    dsimp only [σ'] at hq'
    rw [list_mem_set_iff hidx] at hq'
    rcases hq' with rfl | ⟨j, hj, _, hget_j⟩
    · simpa [LcnfObj.withRc] using hrc'_props.2.2.2
    · rw [← hget_j]; exact hrc_all _ (List.getElem_mem hj)
  have hflag : o.rc = 0#32 ↔ rc' = 0#32 := by
    constructor
    · exact hrc'_props.1
    · intro h0
      by_cases hne0 : o.rc = 0#32
      · exact hne0
      · exfalso
        have hpos := rc_toInt_pos_of_ne_zero howf.2.2.1 hne0
        have hpos' := (hrc'_props.2.1 hpos).2.2
        simp [h0] at hpos'
  have hnpre_eq : ∀ a, nonPersistRefs σ'.objs a = nonPersistRefs σ.objs a :=
    fun a => nonPersistRefs_set_withRc hidx hflag a
  have hcnt_f : ∀ a, List.count a (frameHandles rf') =
      List.count a (frameHandles rf) + (if a = bv then n else 0) := by
    intro a
    have hc := inc_frameHandles_count (n := n) hnodup hclean hget hno hpers henvh a
    simpa [hev] using hc
  have hoa : o.addr = bv := haddr
  have hsound' : HandlesRcSound (frameHandles rf') σ'.objs := by
    refine ⟨?_, ?_⟩
    · intro p' hp' hp'0 f hf hevf
      dsimp only [σ'] at hp'
      rw [list_mem_set_iff hidx] at hp'
      have ⟨p, hp, hpcf, hp0⟩ : ∃ p ∈ σ.objs, p.childFields = p'.childFields ∧ p.rc = 0#32 := by
        rcases hp' with rfl | ⟨j, hj, _, hget_j⟩
        · have : rc' = 0#32 := by simpa [LcnfObj.withRc] using hp'0
          exact ⟨o, List.getElem_mem hidx, rfl, hflag.mpr this⟩
        · exact ⟨p', hget_j ▸ List.getElem_mem hj, rfl, hp'0⟩
      rw [← hpcf] at hf
      obtain ⟨q, hq, hqa, hq0⟩ := hsound.1 p hp hp0 f hf hevf
      obtain ⟨q', hq', hqdeq, hq0', _⟩ := hmap q hq (hwf_all q hq)
      exact ⟨q', hq', hqdeq.1.trans hqa, hq0' hq0⟩
    · intro y' hy' hy'pos
      rw [hnpre_eq y'.addr]
      dsimp only [σ'] at hy'
      rw [list_mem_set_iff hidx] at hy'
      rcases hy' with rfl | ⟨j, hj, hjne, hget_j⟩
      · have hy'pos' : 0 < rc'.toInt := by simpa [LcnfObj.withRc] using hy'pos
        have hopos : 0 < o.rc.toInt := by
          by_cases hpos : 0 < o.rc.toInt
          · exact hpos
          · exfalso
            have h0i : o.rc.toInt = (0#32).toInt := by
              have := howf.2.2.1; simp only [BitVec.toInt_zero]; omega
            have h0' := hrc'_props.1 (BitVec.eq_of_toInt_eq h0i)
            simp [h0'] at hy'pos'
        have hrc_eq : rc'.toNat = o.rc.toNat + n := (hrc'_props.2.1 hopos).1
        have hbase := hsound.2 o (List.getElem_mem hidx) hopos
        have hcnt_y := hcnt_f o.addr
        simp only [LcnfObj.withRc]
        rw [hoa] at hcnt_y hbase ⊢
        simp only [ite_true] at hcnt_y
        rw [hcnt_y, hrc_eq]
        omega
      · have hy_mem : y' ∈ σ.objs := hget_j ▸ List.getElem_mem hj
        have hne_bv : y'.addr ≠ bv := by
          intro heq
          have hj_eq := nodup_map_getElem_inj hnodup_objs hj hidx
            (by rw [hget_j, heq, haddr])
          exact hjne hj_eq
        have hbase := hsound.2 y' hy_mem hy'pos
        have hcnt_y := hcnt_f y'.addr
        simp only [hne_bv, ite_false, Nat.add_zero] at hcnt_y
        rw [hcnt_y]
        exact hbase
  exact ⟨⟨⟨hbn, hwf_all', hclosed', hcap', hrc_all'⟩, hnodup_objs'⟩,
    hsound', hmap, hrc'_props.2.1, hflag⟩

/-- `VarInv` preservation across heap-pointer `.inc`. -/
public theorem inc_heap_varsInv {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hpcb : ParentChildBacked rf σ.objs)
    {x n : Nat} (hn : 0 < n) {v : RcVar} (hget : rf.ctx.get? x = some v) (hlive : v.isLive = true)
    (hno : v.noRc = false) (hpers : v.persistent = false)
    {bv : BitVec 64} (henvh : rf.envH x = some (v.ty, Word.i64 bv)) (hev : bv &&& 1#64 = 0#64)
    {idx : Nat} (hidx : idx < σ.objs.length) (haddr : σ.objs[idx].addr = bv)
    {rc' : BitVec 32}
    (hmap : ∀ q ∈ σ.objs, q.Wf → ∃ q' ∈ (σ.objs.set idx (σ.objs[idx].withRc rc')),
      ObjDataEq q q' ∧ (q.rc = 0#32 → q'.rc = 0#32) ∧
      (0 < q.rc.toInt → 0 < q'.rc.toInt) ∧ (q'.rc = 0#32 → q.rc = 0#32)) :
    let v' : RcVar := { v with owned := v.owned + n, excl := false }
    let σ' : HState :=
      { st := σ.st, objs := σ.objs.set idx (σ.objs[idx].withRc rc'),
        scr := σ.scr, scrLimbs := σ.scrLimbs }
    let rf' : RcFrame := { rf with ctx := rf.ctx.put v' }
    ∀ u ∈ rf'.ctx.vars, VarInv u rf' σ'.objs := by
  intro v' σ' rf' u hu hulive
  have ⟨hheap, hnodup, hsound, hvars, hsp⟩ := hinv
  have hwf_all := hheap.1.2.1
  obtain ⟨hvm, hxid⟩ := RcCtx.get?_mem hget
  have hmap_rc : ∀ q ∈ σ.objs, q.Wf → ∃ q' ∈ σ'.objs,
      q'.addr = q.addr ∧ q'.childFields = q.childFields ∧
      (q.rc = 0#32 → q'.rc = 0#32) ∧ (0 < q.rc.toInt → q'.rc ≠ 0#32) := by
    intro q hq hqwf
    obtain ⟨q', hq', hdeq, h0, hpos, _⟩ := hmap q hq hqwf
    exact ⟨q', hq', hdeq.1, objDataEq_childFields hdeq, h0, fun hp h0' => by
      have := hpos hp; simp [h0'] at this⟩
  have hcnt_f : ∀ a, List.count a (frameHandles rf') =
      List.count a (frameHandles rf) + (if a = bv then n else 0) := by
    intro a
    have hc := inc_frameHandles_count (n := n) hnodup hclean hget hno hpers henvh a
    simpa [hev] using hc
  have hback_frame : ∀ a, Backed σ.objs (frameHandles rf) a →
      Backed σ'.objs (frameHandles rf') a := by
    intro a hb
    refine backed_mono_rc_pos hmap_rc hwf_all (fun r hr => ?_) hb
    have hpos : 0 < List.count r (frameHandles rf) := List.count_pos_iff.mpr hr
    have hcnt_r := hcnt_f r
    exact List.count_pos_iff.mp (by omega)
  rw [RcCtx.put_mem_iff hnodup] at hu
  rcases hu with rfl | ⟨hu_mem, hu_ne⟩
  · obtain ⟨pu, wu, hp, hh, hrep, hnon⟩ := hvars v hvm hlive
    have hrep' : ValRep v'.ty pu wu σ'.objs := by
      refine valRep_mono_pred (P := fun _ => True) (fun q hq hqwf _ => ?_)
        (fun _ _ _ _ _ _ _ => trivial) hrep (fun _ _ _ _ => trivial)
      obtain ⟨q', hq', hdeq, _⟩ := hmap q hq hqwf
      exact ⟨q', hq', hdeq⟩
    refine ⟨pu, wu, hp, hh, hrep', ?_⟩
    intro hns
    obtain ⟨bvu, hwu, hno_u, hpers_u, _, hbor_u⟩ := hnon hns
    refine ⟨bvu, hwu, hno_u, fun hp' hev' => ?_, ?_, ?_⟩
    · obtain ⟨q, hq, hqa, hq0⟩ := hpers_u hp' hev'
      obtain ⟨q', hq', hdeq, h0', _⟩ := hmap q hq (hwf_all q hq)
      exact ⟨q', hq', hdeq.1.trans hqa, h0' hq0⟩
    · intro hex; simp [v'] at hex
    · intro hno' hpers' hbor' hevu
      obtain ⟨hbk1, hbk2⟩ := hbor_u hno' hpers' hbor' hevu
      refine ⟨hback_frame bvu hbk1, ?_⟩
      cases hpar : v'.parent? with
      | none =>
        rw [hpar] at hbk2
        exact backed_mono_rc_pos hmap_rc hwf_all (fun _ hr => hr) hbk2
      | some p =>
        rw [hpar] at hbk2
        obtain ⟨pv, hpv_mem, hpv_id, hpv_no, hpv_pers, hpv_pos, hpv_bk⟩ := hbk2
        have hpv_ne : pv.id ≠ v'.id := by
          intro heq
          obtain ⟨pv0, hpv0_mem, hpv0_id, _, _, _, hpv0_bor⟩ := hpo v hvm p hpar
          have hpv0_eq : pv0 = v :=
            rcVar_eq_of_mem_nodup hnodup hpv0_mem hvm (hpv0_id.trans hpv_id.symm |>.trans heq)
          rw [hpv0_eq] at hpv0_bor
          have hv_bor : v.borrowed = true := hbor'
          rw [hpv0_bor] at hv_bor
          cases hv_bor
        exact ⟨pv, (RcCtx.put_mem_iff hnodup).mpr (Or.inr ⟨hpv_mem, hpv_ne⟩),
          hpv_id, hpv_no, hpv_pers, hpv_pos,
          backed_mono_rc_pos hmap_rc hwf_all (fun _ hr => hr) hpv_bk⟩
  · obtain ⟨pu, wu, hp, hh, hrep, hnon⟩ := hvars u hu_mem hulive
    have hrep' : ValRep u.ty pu wu σ'.objs := by
      refine valRep_mono_pred (P := fun _ => True) (fun q hq hqwf _ => ?_)
        (fun _ _ _ _ _ _ _ => trivial) hrep (fun _ _ _ _ => trivial)
      obtain ⟨q', hq', hdeq, _⟩ := hmap q hq hqwf
      exact ⟨q', hq', hdeq⟩
    refine ⟨pu, wu, hp, hh, hrep', ?_⟩
    intro hns
    obtain ⟨bvu, hwu, hno_u, hpers_u, hex_u, hbor_u⟩ := hnon hns
    refine ⟨bvu, hwu, hno_u, fun hp' hev' => ?_, ?_, ?_⟩
    · obtain ⟨q, hq, hqa, hq0⟩ := hpers_u hp' hev'
      obtain ⟨q', hq', hdeq, h0', _⟩ := hmap q hq (hwf_all q hq)
      exact ⟨q', hq', hdeq.1.trans hqa, h0' hq0⟩
    · intro hex
      obtain ⟨hxno, hxpers, hxown, hxo⟩ := hex_u hex
      refine ⟨hxno, hxpers, hxown, fun hevu => ?_⟩
      obtain ⟨o_u, ho_u, ho_ua, ho_urc⟩ := hxo hevu
      have ho_uwf : o_u.Wf := hwf_all o_u ho_u
      obtain ⟨_, _, _, hlive_ne, _⟩ := excl_disjoint_facts hinv hclean hpo hpcb hu_mem
        hxno hxpers (hclean u hu_mem).2.2.2.2 hxown (hwu ▸ hh) ho_u ho_uwf ho_ua ho_urc
      have hne_bv : bv ≠ o_u.addr := by
        have hvid_ne : v.id ≠ u.id := by
          intro h; apply hu_ne; simpa [v', hxid] using h.symm
        have hnsv : !v.ty.isScalar = true := by
          cases hs : v.ty.isScalar
          · rfl
          · exact absurd ((hclean v hvm).1.2 hs) (by simp [hno])
        have := hlive_ne v hvm hvid_ne hlive hnsv bv (hxid ▸ henvh)
        simpa [ho_ua] using this
      obtain ⟨j, hj, hget_j⟩ := obj_mem_idx ho_u
      have hjne : j ≠ idx := by
        intro hjeq; subst hjeq; exact hne_bv (by rw [← haddr, hget_j])
      refine ⟨o_u, ?_, ho_ua, ho_urc⟩
      dsimp only [σ']
      exact (list_mem_set_iff hidx).mpr (Or.inr ⟨j, hj, hjne, hget_j⟩)
    · intro hno' hpers' hbor' hevu
      obtain ⟨hbk1, hbk2⟩ := hbor_u hno' hpers' hbor' hevu
      refine ⟨hback_frame bvu hbk1, ?_⟩
      cases hpar : u.parent? with
      | none =>
        rw [hpar] at hbk2
        exact backed_mono_rc_pos hmap_rc hwf_all (fun _ hr => hr) hbk2
      | some p =>
        rw [hpar] at hbk2
        obtain ⟨pv, hpv_mem, hpv_id, hpv_no, hpv_pers, hpv_pos, hpv_bk⟩ := hbk2
        have hbk' := backed_mono_rc_pos hmap_rc hwf_all (fun _ hr => hr) hpv_bk
        by_cases hpid : pv.id = v'.id
        · have hpv_eq : pv = v := rcVar_eq_of_mem_nodup hnodup hpv_mem hvm hpid
          refine ⟨v', (RcCtx.put_mem_iff hnodup).mpr (Or.inl rfl),
            by simp [v', ← hpv_eq, hpv_id], hno, hpers, Or.inl (by simp [v']; omega), hbk'⟩
        · exact ⟨pv, (RcCtx.put_mem_iff hnodup).mpr (Or.inr ⟨hpv_mem, hpid⟩),
            hpv_id, hpv_no, hpv_pers, hpv_pos, hbk'⟩

/-- `SharedPredInv` preservation across heap-pointer `.inc`. -/
public theorem inc_heap_sharedPredInv {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hpcb : ParentChildBacked rf σ.objs)
    {x n : Nat} {v : RcVar} (hget : rf.ctx.get? x = some v) (hlive : v.isLive = true)
    (hno : v.noRc = false) (hpers : v.persistent = false)
    (hsp_x : 0 < v.owned ∨ (rf.ctx.sharedPreds.all (fun p => p.2 != x)) = true)
    {bv : BitVec 64} (henvh : rf.envH x = some (v.ty, Word.i64 bv)) (hev : bv &&& 1#64 = 0#64)
    {idx : Nat} (hidx : idx < σ.objs.length) (haddr : σ.objs[idx].addr = bv)
    {rc' : BitVec 32}
    (hnodup_objs' : ((σ.objs.set idx (σ.objs[idx].withRc rc')).map LcnfObj.addr).Nodup)
    (hmap : ∀ q ∈ σ.objs, q.Wf → ∃ q' ∈ (σ.objs.set idx (σ.objs[idx].withRc rc')),
      ObjDataEq q q' ∧ (q.rc = 0#32 → q'.rc = 0#32) ∧
      (0 < q.rc.toInt → 0 < q'.rc.toInt) ∧ (q'.rc = 0#32 → q.rc = 0#32))
    (hpos_rc' : 0 < σ.objs[idx].rc.toInt →
      rc'.toNat = σ.objs[idx].rc.toNat + n ∧ rc'.toNat < 2 ^ 31 - 1 ∧ 0 < rc'.toInt)
    (h0_rc' : σ.objs[idx].rc = 0#32 → rc' = 0#32)
    (hnpre_eq : ∀ a, nonPersistRefs (σ.objs.set idx (σ.objs[idx].withRc rc')) a =
      nonPersistRefs σ.objs a) :
    let v' : RcVar := { v with owned := v.owned + n, excl := false }
    let σ' : HState :=
      { st := σ.st, objs := σ.objs.set idx (σ.objs[idx].withRc rc'),
        scr := σ.scr, scrLimbs := σ.scrLimbs }
    let rf' : RcFrame := { rf with ctx := rf.ctx.put v' }
    SharedPredInv rf' σ'.objs := by
  intro v' σ' rf' p hp vb vs hgb hgs hblive hsno hspers
  have ⟨hheap, hnodup, _, _, hsp⟩ := hinv
  have hwf_all := hheap.1.2.1
  have hnodup_objs := hheap.2
  let o := σ.objs[idx]
  have howf : o.Wf := hwf_all o (List.getElem_mem hidx)
  have hidx_len : idx < σ'.objs.length := by simp [σ', hidx]
  have hnodup' : (rf'.ctx.vars.map RcVar.id).Nodup := RcCtx.put_nodup hnodup v'
  obtain ⟨hvm, hxid⟩ := RcCtx.get?_mem hget
  have hcnt_f : ∀ a, List.count a (frameHandles rf') =
      List.count a (frameHandles rf) + (if a = bv then n else 0) := by
    intro a
    have hc := inc_frameHandles_count (n := n) hnodup hclean hget hno hpers henvh a
    simpa [hev] using hc
  have hp_old : p ∈ rf.ctx.sharedPreds := hp
  by_cases hpx : p.2 = x
  · have hvpos : 0 < v.owned := by
      rcases hsp_x with hpos | hall
      · exact hpos
      · exfalso; have := (List.all_eq_true.mp hall) p hp_old; simp [hpx] at this
    have hgs_eq : vs = v' := by
      rw [RcCtx.put_get? hnodup] at hgs
      have hvs_eq : v' = vs := by simpa [hpx, v', hxid] using hgs
      exact hvs_eq.symm
    have hgb_old : ∃ vb0, rf.ctx.get? p.1 = some vb0 ∧ vb0.isLive = true := by
      rw [RcCtx.put_get? hnodup] at hgb
      by_cases hp1 : p.1 = v'.id
      · simp [hp1] at hgb; subst hgb; exact ⟨v, (hp1.trans hxid).symm ▸ hget, hlive⟩
      · simp [hp1] at hgb; exact ⟨vb, hgb, hblive⟩
    obtain ⟨vb0, hgb0, hblive0⟩ := hgb_old
    have hsp_old := hsp p hp_old vb0 v hgb0 (hpx.symm ▸ hget) hblive0 hno hpers
    have hex_same : localHandlesExcept rf'.ctx rf.envH p.2 =
        localHandlesExcept rf.ctx rf.envH p.2 := by
      rw [hpx, ← hxid]; exact localHandlesExcept_put hnodup rf.envH v'
    have hoa : o.addr = bv := haddr
    have henvh_s : rf'.envH p.2 = some (vs.ty, Word.i64 bv) := by
      rw [hpx, hgs_eq]; simpa [v'] using henvh
    refine ⟨fun htag => ?_, fun htag _ => ?_⟩
    · obtain ⟨bvs, henvs, _, hrest⟩ := hsp_old.1 htag
      have heq_bv : bvs = bv := by
        have := (hpx ▸ henvh).symm.trans henvs; cases this; rfl
      rw [heq_bv] at hrest
      obtain ⟨hc0, o_s, ho_s, ho_sa, ho_src⟩ := hrest hvpos
      have ho_seq : o_s = o := obj_eq_of_addr_nodup hnodup_objs ho_s
        (List.getElem_mem hidx) (ho_sa.trans haddr.symm)
      rw [ho_seq] at ho_src
      have hopos : 0 < o.rc.toInt := by
        have := howf.2.2.1
        have hne0 : o.rc ≠ 0#32 := by
          intro h0; rw [h0] at ho_src
          change (0#32).toNat = v.owned at ho_src
          simp only [BitVec.toNat_ofNat, Nat.zero_mod] at ho_src
          omega
        exact rc_toInt_pos_of_ne_zero this hne0
      have hrc_eq : rc'.toNat = σ.objs[idx].rc.toNat + n := (hpos_rc' hopos).1
      have hoeq : o = σ.objs[idx] := rfl
      refine ⟨bv, henvh_s, hev, fun _ => ⟨?_, o.withRc rc', ?_, hoa, ?_⟩⟩
      · rw [hnpre_eq bv, hex_same]
        exact hc0
      · dsimp only [σ']
        exact List.mem_iff_getElem.mpr ⟨idx, hidx_len, by simp [o]⟩
      · rw [LcnfObj.withRc, hrc_eq, ← hoeq, ho_src, hgs_eq]
    · obtain ⟨bvs, henvs, _, o_s, ho_s, ho_sa, horc⟩ := hsp_old.2 htag hvpos
      have heq_bv : bvs = bv := by
        have := (hpx ▸ henvh).symm.trans henvs; cases this; rfl
      rw [heq_bv] at ho_sa
      have ho_seq : o_s = o := obj_eq_of_addr_nodup hnodup_objs ho_s
        (List.getElem_mem hidx) (ho_sa.trans haddr.symm)
      rw [ho_seq] at horc
      refine ⟨bv, henvh_s, hev, o.withRc rc', ?_, hoa, ?_⟩
      · dsimp only [σ']
        exact List.mem_iff_getElem.mpr ⟨idx, hidx_len, by simp [o]⟩
      · rcases horc with h0 | hlt
        · left; simp [LcnfObj.withRc, h0_rc' h0]
        · right
          have hopos : 0 < o.rc.toInt := by
            have := howf.2.2.1
            have hne0 : o.rc ≠ 0#32 := by
              intro h0'; rw [h0'] at hlt
              change v.owned < (0#32).toNat at hlt
              simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hlt
              omega
            exact rc_toInt_pos_of_ne_zero this hne0
          have hrc_eq := (hpos_rc' hopos).1
          have hoeq : o = σ.objs[idx] := rfl
          rw [LcnfObj.withRc, hrc_eq, ← hoeq, hgs_eq]
          simp only [v']
          omega
  · have hgs_old : rf.ctx.get? p.2 = some vs := by
      rw [RcCtx.put_get? hnodup] at hgs
      have hne : (p.2 == v'.id) = false := beq_false_of_ne (by simpa [v', hxid] using hpx)
      simp [hne] at hgs
      exact hgs
    have hgb_old : ∃ vb0, rf.ctx.get? p.1 = some vb0 ∧ vb0.isLive = true := by
      rw [RcCtx.put_get? hnodup] at hgb
      by_cases hp1 : p.1 = v'.id
      · simp [hp1] at hgb; subst hgb; exact ⟨v, (hp1.trans hxid).symm ▸ hget, hlive⟩
      · simp [hp1] at hgb; exact ⟨vb, hgb, hblive⟩
    obtain ⟨vb0, hgb0, hblive0⟩ := hgb_old
    have hsp_old := hsp p hp_old vb0 vs hgb0 hgs_old hblive0 hsno hspers
    refine ⟨fun htag => ?_, fun htag hspos => ?_⟩
    · obtain ⟨bvs, henvs, hevs, hrest⟩ := hsp_old.1 htag
      refine ⟨bvs, henvs, hevs, fun hspos => ?_⟩
      obtain ⟨hc0, o_s, ho_s, ho_sa, ho_src⟩ := hrest hspos
      have hne_bv : bv ≠ bvs := inc_bv_ne_shared_zero hinv
        hclean hpo hpcb hget hlive hno hpers henvh hev hp hpx hgb0 hgs_old
        hblive0 hsno hspers htag hspos henvs
      have hoa : o.addr = bv := haddr
      have hne_os : o_s.addr ≠ o.addr := by rw [ho_sa, hoa]; exact hne_bv.symm
      obtain ⟨j, hj, hget_j⟩ := obj_mem_idx ho_s
      have hjne : j ≠ idx := by
        intro hjeq; subst hjeq; exact hne_os (by rw [← hget_j])
      have hcnt_ex : List.count bvs (localHandlesExcept rf'.ctx rf.envH p.2) =
          List.count bvs (localHandlesExcept rf.ctx rf.envH p.2) := by
        have h_all := localHandles_count_eq_add hnodup rf.envH (RcCtx.get?_mem hgs_old).1 bvs
        have h_all' := localHandles_count_eq_add hnodup' rf.envH (RcCtx.get?_mem hgs).1 bvs
        have hvs_id : vs.id = p.2 := (RcCtx.get?_mem hgs).2
        have hc := hcnt_f bvs
        simp only [frameHandles, List.count_append, hne_bv.symm, ite_false, Nat.add_zero] at hc
        dsimp only [rf'] at hc h_all' ⊢
        rw [hvs_id] at h_all h_all'
        omega
      refine ⟨?_, o_s, ?_, ho_sa, ho_src⟩
      · rw [hnpre_eq bvs, List.count_append, List.count_append, hcnt_ex]
        rw [List.count_append, List.count_append] at hc0
        exact hc0
      · dsimp only [σ']
        exact (list_mem_set_iff hidx).mpr (Or.inr ⟨j, hj, hjne, hget_j⟩)
    · obtain ⟨bvs, henvs, hevs, o_s, ho_s, ho_sa, horc⟩ := hsp_old.2 htag hspos
      refine ⟨bvs, henvs, hevs, ?_⟩
      obtain ⟨o_s', ho_s', hdeq, h0, _, _⟩ := hmap o_s ho_s (hwf_all o_s ho_s)
      refine ⟨o_s', ho_s', hdeq.1.trans ho_sa, ?_⟩
      rcases horc with h0eq | hlt
      · exact Or.inl (h0 h0eq)
      · right
        obtain ⟨j, hj, hget_j⟩ := obj_mem_idx ho_s
        by_cases hji : j = idx
        · subst hji
          have hoeq : o_s = o := hget_j.symm
          have ho_seq : o_s' = o.withRc rc' := by
            apply obj_eq_of_addr_nodup hnodup_objs' ho_s'
            · exact List.mem_iff_getElem.mpr ⟨j, hidx_len, by simp [o]⟩
            · exact hdeq.1.trans (by rw [hoeq]; rfl)
          have hopos : 0 < o.rc.toInt := by
            have := howf.2.2.1
            have hne0 : o.rc ≠ 0#32 := by
              intro h0'; rw [hoeq, h0'] at hlt
              change vs.owned < (0#32).toNat at hlt
              simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hlt
              omega
            exact rc_toInt_pos_of_ne_zero this hne0
          have hrc_eq := (hpos_rc' hopos).1
          have hoeq_j : o = σ.objs[j] := rfl
          rw [ho_seq, LcnfObj.withRc, hrc_eq, ← hoeq_j, ← hoeq]
          omega
        · have ho_s_eq : o_s' = o_s := by
            apply obj_eq_of_addr_nodup hnodup_objs' ho_s' _ hdeq.1
            exact (list_mem_set_iff hidx).mpr (Or.inr ⟨j, hj, hji, hget_j⟩)
          rw [ho_s_eq]
          exact hlt

/-- Heap-pointer `.inc` preserves `RcInv`, `CleanVars`, `ParentsOwned`, `NoRcCorrect`,
    `ParentChildBacked`, `SharedTargetsHeap`, `HandlesInHeap`, and `EntryPres`. -/
public theorem inc_heap_rcInv {rt : BitVec 64} {rf rf0 : RcFrame} {σ σ0 : HState}
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ)
    {x n : Nat} {v : RcVar} (hget : rf.ctx.get? x = some v) (hlive : v.isLive = true)
    (hno : v.noRc = false) (hpers : v.persistent = false) (hn : 0 < n)
    (hsp_x : 0 < v.owned ∨ (rf.ctx.sharedPreds.all (fun p => p.2 != x)) = true)
    {bv : BitVec 64} (henvh : rf.envH x = some (v.ty, Word.i64 bv)) (hev : bv &&& 1#64 = 0#64)
    {idx : Nat} (hidx : idx < σ.objs.length) (haddr : σ.objs[idx].addr = bv)
    (hbd : 0 < σ.objs[idx].rc.toInt → σ.objs[idx].rc.toNat + n < 2 ^ 31 - 1) :
    let v' : RcVar := { v with owned := v.owned + n, excl := false }
    let o := σ.objs[idx]
    let rc' := if 0 < o.rc.toInt then o.rc + BitVec.ofNat 32 n else o.rc
    let σ' : HState :=
      { st := σ.st, objs := σ.objs.set idx (o.withRc rc'),
        scr := σ.scr, scrLimbs := σ.scrLimbs }
    let rf' : RcFrame := { rf with ctx := rf.ctx.put v' }
    RcInv rt rf' σ' ∧ CleanVars rf'.ctx ∧ ParentsOwned rf'.ctx ∧ NoRcCorrect rf'.ctx ∧
      ParentChildBacked rf' σ'.objs ∧ SharedTargetsHeap rf' ∧
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs ∧ EntryPres rf0 σ0 rf' σ' := by
  intro v' o rc' σ' rf'
  obtain ⟨hheap', hsound', hmap, hpos_rc', hflag⟩ :=
    inc_heap_clean_sound hinv hclean hget hno hpers henvh hev hidx haddr hbd
  have hvars' := inc_heap_varsInv hinv hclean hpo hpcb hn hget hlive hno hpers henvh hev
    hidx haddr hmap
  have hnpre_eq : ∀ a, nonPersistRefs σ'.objs a = nonPersistRefs σ.objs a :=
    fun a => nonPersistRefs_set_withRc hidx hflag a
  have hsp' := inc_heap_sharedPredInv hinv hclean hpo hpcb hget hlive hno hpers hsp_x
    henvh hev hidx haddr hheap'.2 hmap hpos_rc' hflag.mp hnpre_eq
  obtain ⟨hheap, hnodup, _, _, _⟩ := hinv
  have hwf_all := hheap.1.2.1
  obtain ⟨hvm, hxid⟩ := RcCtx.get?_mem hget
  have hcv' : CleanVar v' := inc_cleanVar (hclean v hvm) hno hpers n
  have hnodup' : (rf'.ctx.vars.map RcVar.id).Nodup := RcCtx.put_nodup hnodup v'
  have hclean' : CleanVars rf'.ctx := cleanVars_put hnodup hclean hcv'
  have hpo' : ParentsOwned rf'.ctx := inc_parentsOwned hnodup hclean hpo hvm hno hpers hn
  have hnorc' : NoRcCorrect rf'.ctx := noRcCorrect_put hnodup hnorc (fun _ => hnorc v hvm hno)
  have hmap_rc : ∀ q ∈ σ.objs, q.Wf → ∃ q' ∈ σ'.objs,
      q'.addr = q.addr ∧ q'.childFields = q.childFields ∧
      (q.rc = 0#32 → q'.rc = 0#32) ∧ (0 < q.rc.toInt → q'.rc ≠ 0#32) := by
    intro q hq hqwf
    obtain ⟨q', hq', hdeq, h0, hpos, _⟩ := hmap q hq hqwf
    exact ⟨q', hq', hdeq.1, objDataEq_childFields hdeq, h0, fun hp h0' => by
      have := hpos hp; simp [h0'] at this⟩
  have hpcb' : ParentChildBacked rf' σ'.objs := by
    intro u hu hulive huno hupers hubor q hpar bvu henvu hevu
    rw [RcCtx.put_mem_iff hnodup] at hu
    have hback_ext : ∀ a, Backed σ.objs (rf.extH ++ rf.ghostH) a →
        Backed σ'.objs (rf'.extH ++ rf'.ghostH) a :=
      fun a hb => backed_mono_rc_pos hmap_rc hwf_all (fun _ hr => hr) hb
    rcases hu with rfl | ⟨hu_mem, _⟩
    · rcases hpcb v hvm hlive hno hpers hubor q hpar bvu (hxid ▸ henvu) hevu with hext | hch
      · exact Or.inl (hback_ext bvu hext)
      · right
        obtain ⟨wp, o_q, hwp, hqaddr, ho_q, o_mid, hom_m, hreach_mid, hcf⟩ := hch
        obtain ⟨o_q', ho_q', hdeq, _⟩ := hmap o_q ho_q (hwf_all o_q ho_q)
        obtain ⟨o_mid', hom'm, hdeq_m, _⟩ := hmap o_mid hom_m (hwf_all o_mid hom_m)
        have hreach' := nonPersistReach_mono_rc_pos hmap_rc hwf_all hreach_mid
        exact ⟨wp, o_q', hwp, hdeq.1.symm ▸ hqaddr, ho_q', o_mid', hom'm,
          hdeq.1.symm ▸ hdeq_m.1.symm ▸ hreach', objDataEq_childFields hdeq_m ▸ hcf⟩
    · rcases hpcb u hu_mem hulive huno hupers hubor q hpar bvu henvu hevu with hext | hch
      · exact Or.inl (hback_ext bvu hext)
      · right
        obtain ⟨wp, o_q, hwp, hqaddr, ho_q, o_mid, hom_m, hreach_mid, hcf⟩ := hch
        obtain ⟨o_q', ho_q', hdeq, _⟩ := hmap o_q ho_q (hwf_all o_q ho_q)
        obtain ⟨o_mid', hom'm, hdeq_m, _⟩ := hmap o_mid hom_m (hwf_all o_mid hom_m)
        have hreach' := nonPersistReach_mono_rc_pos hmap_rc hwf_all hreach_mid
        exact ⟨wp, o_q', hwp, hdeq.1.symm ▸ hqaddr, ho_q', o_mid', hom'm,
          hdeq.1.symm ▸ hdeq_m.1.symm ▸ hreach', objDataEq_childFields hdeq_m ▸ hcf⟩
  have hsth' : SharedTargetsHeap rf' :=
    sharedTargetsHeap_put_same hnodup hsth (v := v) (v' := v') (hxid ▸ hget) rfl rfl rfl
  have hhih' : HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs := by
    intro a ha
    obtain ⟨q, hq, hqa⟩ := hhih a ha
    obtain ⟨q', hq', hdeq, _⟩ := hmap q hq (hwf_all q hq)
    exact ⟨q', hq', hdeq.1.trans hqa⟩
  have hepres' : EntryPres rf0 σ0 rf' σ' := by
    obtain ⟨hhs0, hiso0, hext0, hgh0⟩ := hepres
    have hhs_step : HeapStepRel (rf0.extH ++ rf0.ghostH) σ σ' := by
      refine ⟨by dsimp only [σ']; simp [RtC0State.PreservesMeta], rfl, rfl,
        fun q hq hqwf _ => ?_, fun a hb => ?_⟩
      · obtain ⟨q', hq', hdeq, h0, hpos, _⟩ := hmap q hq hqwf
        exact ⟨q', hq', hdeq, h0, hpos⟩
      · exact backed_mono_rc_pos hmap_rc hwf_all (fun _ hr => hr) hb
    refine ⟨heapStepRel_trans hhs0 hhs_step, ?_, hext0, hgh0⟩
    intro a ha hiso_a0
    obtain ⟨hiso_a, ha_rc1⟩ := hiso0 a ha hiso_a0
    obtain ⟨hiso_live, hiso_np, o_a, ho_a, ho_awf, ho_aa, ho_arc1⟩ := hiso_a
    have hnsv : !v.ty.isScalar = true := by
      cases hs : v.ty.isScalar
      · rfl
      · exact absurd ((hclean v hvm).1.2 hs) (by simp [hno])
    have hne_bv : bv ≠ a := fun heq =>
      hiso_live v hvm hlive hnsv (Word.i64 bv) (hxid ▸ henvh) (by subst heq; rfl)
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro u hu hulive huns w hw
      rw [RcCtx.put_mem_iff hnodup] at hu
      rcases hu with rfl | ⟨hu_mem, _⟩
      · exact hiso_live v hvm hlive huns w hw
      · exact hiso_live u hu_mem hulive huns w hw
    · rw [hnpre_eq a]; exact hiso_np
    · obtain ⟨j, hj, hget_j⟩ := obj_mem_idx ho_a
      have hjne : j ≠ idx := by
        intro hjeq; subst hjeq; exact hne_bv (by rw [← haddr, ← ho_aa, hget_j])
      refine ⟨o_a, ?_, ho_awf, ho_aa, ho_arc1⟩
      dsimp only [σ']
      exact (list_mem_set_iff hidx).mpr (Or.inr ⟨j, hj, hjne, hget_j⟩)
    · intro q hq0 hqa0
      obtain ⟨q', hq', hdeq, hq'1⟩ := ha_rc1 q hq0 hqa0
      obtain ⟨j, hj, hget_j⟩ := obj_mem_idx hq'
      have hjne : j ≠ idx := by
        intro hjeq; subst hjeq; exact hne_bv (by rw [← haddr, ← hqa0, ← hdeq.1, hget_j])
      refine ⟨q', ?_, hdeq, hq'1⟩
      dsimp only [σ']
      exact (list_mem_set_iff hidx).mpr (Or.inr ⟨j, hj, hjne, hget_j⟩)
  exact ⟨⟨hheap', hnodup', hsound', hvars', hsp'⟩, hclean', hpo', hnorc',
    hpcb', hsth', hhih', hepres'⟩

private theorem tobject_of_ne_even {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hinv : RcInv rt rf σ) {x : Nat} {v : RcVar} (hget : rf.ctx.get? x = some v)
    (hlive : v.isLive = true) (hneeds : v.ty.needsRc = true) {bv : BitVec 64}
    (henvh : rf.envH x = some (v.ty, Word.i64 bv)) (hodd : bv &&& 1#64 ≠ 0#64) :
    v.ty = LcTy.tobject := by
  have ⟨hvm, hxid⟩ := RcCtx.get?_mem hget
  have hnonsc : ¬v.ty.isScalar = true := by
    cases hty : v.ty <;> simp_all [LcTy.needsRc, LcTy.isScalar]
  have ⟨_, wu, _, hwu, hrep, _⟩ := hinv.2.2.2.1 v hvm hlive
  rw [← hxid, hwu] at henvh
  cases henvh
  simp only [ValRep, hnonsc] at hrep
  obtain ⟨bvp, hwp, _, hobj_even, _⟩ := hrep
  cases hwp
  cases hty : v.ty with
  | object => exact absurd (hobj_even hty) hodd
  | tobject => rfl
  | tagged | erased | void | uint8 | uint16 | uint32 | uint64 | usize | float =>
    rw [hty] at hneeds; cases hneeds

/-- Stepwise simulation for `LcCode.inc` exposing the exact post-step `RcFrame`. -/
public theorem inc_step_ctx {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {J : HJEnv} {Jp : PResJEnv}
    {Q : PResPost} {Xp : PResXPost} {Qh : HPost} {Xh : HXPost}
    {jps : List RcJpInfo} {rf rf0 : RcFrame} {σ σ0 : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr : Nat}
    {x n : Nat} {chk : Bool} {k : LcCode}
    (hwf : perceusCodeWf env retTy jps rf.ctx sm (LcCode.inc x n chk k) = true)
    (hpr : PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Q Xp (LcCode.inc x n chk k))
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ) (hres : ResStateInv σ rem wr rcr)
    (hk : ∀ {rf' : RcFrame} {σ' : HState} {rcr' : Nat},
      perceusCodeWf env retTy jps rf'.ctx sm k = true →
      PRWp m env retTy Δr jps rf'.ctx Jp ρP rem wr rcr' Q Xp k →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs →
      EntryPres rf0 σ0 rf' σ' → ResStateInv σ' rem wr rcr' →
      (∀ q' ∈ σ'.objs, ∀ q ∈ σ.objs, q'.addr = q.addr → ObjDataEq q q') →
      rf'.envP = rf.envP ∧ rf'.envH = rf.envH ∧ rf'.extH = rf.extH ∧
        ((∃ v, rf.ctx.get? x = some v ∧ (v.noRc || v.persistent || n == 0) = true ∧
            rf'.ctx = rf.ctx) ∨
         ∃ v, rf.ctx.get? x = some v ∧ (v.noRc || v.persistent || n == 0) = false ∧
            rf'.ctx = rf.ctx.put { v with owned := v.owned + n, excl := false }) →
      HWp Δh rt retTy J rf'.envH Qh Xh k σ') :
    HWp Δh rt retTy J rf.envH Qh Xh (LcCode.inc x n chk k) σ := by
  rw [perceusCodeWf.eq_15] at hwf
  rw [PRWp.eq_11] at hpr
  rw [HWp.eq_11]
  cases hget : rf.ctx.get? x with
  | none => simp [hget] at hpr
  | some v =>
    simp only [hget, Bool.and_eq_true, decide_eq_true_eq] at hwf hpr
    rcases hwf with ⟨_, ⟨⟨⟨hlive, hw64⟩, hchk⟩, hrest⟩⟩
    have hnodup_objs := hinv.1.2
    have hwf_all := hinv.1.1.2.1
    obtain ⟨bv, henvh, htbv⟩ := getTypedBV64?_of_varInv hinv.2.2.2.1
      (RcCtx.get?_mem hget).1 hlive (by simpa using hw64)
    have henvh_x : rf.envH x = some (v.ty, Word.i64 bv) :=
      (RcCtx.get?_mem hget).2 ▸ henvh
    have htbv_x : rf.envH.getTypedBV64? x = some (v.ty, bv) :=
      (RcCtx.get?_mem hget).2 ▸ htbv
    rw [htbv_x]
    by_cases hskip_v : (v.noRc || v.persistent || n == 0) = true
    · simp only [hskip_v, ite_true] at hrest hpr
      by_cases hskip_ty : (!v.ty.needsRc || n == 0) = true
      · simp only [hskip_ty, ite_true]
        exact hk hrest hpr hinv hclean hpo hnorc hpcb hsth hhih hepres hres
          (fun _ hq' q hq hqa => by
            have hqwf := hwf_all q hq
            have hqeq := obj_eq_of_addr_nodup hnodup_objs hq' hq hqa
            rw [hqeq]; exact objDataEq_refl q hqwf)
          ⟨rfl, rfl, rfl, Or.inl ⟨v, hget, hskip_v, rfl⟩⟩
      · simp [hskip_ty]
        have hneeds : v.ty.needsRc = true := by
          cases hnrc : v.ty.needsRc <;> simp_all
        have hn0 : n ≠ 0 := by intro h0; simp [h0] at hskip_ty
        have hnonsc : ¬v.ty.isScalar = true := by
          cases hty : v.ty <;> simp_all [LcTy.needsRc, LcTy.isScalar]
        obtain ⟨_, _, _, hhu, _, hnon⟩ := hinv.2.2.2.1 v (RcCtx.get?_mem hget).1 hlive
        obtain ⟨bvv, hweq, hno_r, hpers_r, _⟩ := hnon hnonsc
        have heq_bv : bv = bvv := by
          have := henvh.symm.trans (hweq ▸ hhu); cases this; rfl
        have hvp : v.noRc = true ∨ v.persistent = true := by
          simp [hn0] at hskip_v; exact hskip_v
        rcases hvp with hno | hpers
        · have hodd : bv &&& 1#64 ≠ 0#64 := heq_bv ▸ hno_r hno
          have htobj : v.ty = LcTy.tobject :=
            tobject_of_ne_even hinv hget hlive hneeds henvh_x hodd
          simp [hodd]
          exact ⟨hchk (by rw [htobj]; rfl), htobj,
            hk hrest hpr hinv hclean hpo hnorc hpcb hsth hhih hepres hres
              (fun _ hq' q hq hqa => by
                have hqwf := hwf_all q hq
                have hqeq := obj_eq_of_addr_nodup hnodup_objs hq' hq hqa
                rw [hqeq]; exact objDataEq_refl q hqwf)
              ⟨rfl, rfl, rfl, Or.inl ⟨v, hget, hskip_v, rfl⟩⟩⟩
        · by_cases hev : bv &&& 1#64 = 0#64
          · obtain ⟨o, ho, hoa, ho0⟩ := hpers_r hpers (heq_bv ▸ hev)
            obtain ⟨idx, hidx, hget_idx⟩ := obj_mem_idx ho
            have hnot_pos : ¬(0 < o.rc.toInt) := by simp [ho0]
            have hoset : σ.objs.set idx (o.withRc (if 0 < o.rc.toInt then
                o.rc + BitVec.ofNat 32 n else o.rc)) = σ.objs := by
              have hweq : o.withRc o.rc = o := by cases o; rfl
              simp only [hnot_pos, ite_false, hweq]
              rw [← hget_idx]
              simp [List.set_getElem_self]
            simp [hev]
            refine ⟨idx, hidx, ?_, fun hp => ?_, ?_⟩
            · simp [hget_idx, hoa, heq_bv]
            · simp [hget_idx, ho0] at hp
            · rw [show σ.objs[idx] = o from hget_idx, hoset]
              exact hk hrest hpr hinv hclean hpo hnorc hpcb hsth hhih hepres hres
                (fun _ hq' q hq hqa => by
                  have hqwf := hwf_all q hq
                  have hqeq := obj_eq_of_addr_nodup hnodup_objs hq' hq hqa
                  rw [hqeq]; exact objDataEq_refl q hqwf)
                ⟨rfl, rfl, rfl, Or.inl ⟨v, hget, hskip_v, rfl⟩⟩
          · have htobj : v.ty = LcTy.tobject :=
              tobject_of_ne_even hinv hget hlive hneeds henvh_x hev
            simp [hev]
            exact ⟨hchk (by rw [htobj]; rfl), htobj,
              hk hrest hpr hinv hclean hpo hnorc hpcb hsth hhih hepres hres
                (fun _ hq' q hq hqa => by
                  have hqwf := hwf_all q hq
                  have hqeq := obj_eq_of_addr_nodup hnodup_objs hq' hq hqa
                  rw [hqeq]; exact objDataEq_refl q hqwf)
                ⟨rfl, rfl, rfl, Or.inl ⟨v, hget, hskip_v, rfl⟩⟩⟩
    · simp [hskip_v] at hrest hpr
      have hskip_v' : v.noRc = false ∧ v.persistent = false ∧ (n == 0) = false := by
        revert hskip_v
        cases v.noRc <;> cases v.persistent <;> cases n == 0 <;> simp
      obtain ⟨hno, hpers, hn0⟩ := hskip_v'
      have hn : 0 < n := by simp at hn0; omega
      have hneeds : v.ty.needsRc = true := hnorc v (RcCtx.get?_mem hget).1 hno
      have hskip_ty : (!v.ty.needsRc || n == 0) = false := by
        simp [hneeds, Nat.ne_of_gt hn]
      simp [hskip_ty]
      rcases hrest with ⟨hsp_x0, hwf_k⟩
      have hsp_x : 0 < v.owned ∨ (rf.ctx.sharedPreds.all (fun p => p.2 != x)) = true := by
        rcases hsp_x0 with h | h
        · exact Or.inl h
        · exact Or.inr (List.all_eq_true.mpr fun q hq => by simp [h q.1 q.2 hq])
      rcases hpr with ⟨hnrcr, hpr_k⟩
      by_cases hev : bv &&& 1#64 = 0#64
      · simp [hev]
        obtain ⟨pv, wu, _, hwu, hrep, _⟩ := hinv.2.2.2.1 v (RcCtx.get?_mem hget).1 hlive
        rw [hwu] at henvh; cases henvh
        have hnonsc : ¬v.ty.isScalar = true :=
          fun hs => by have := (hclean v (RcCtx.get?_mem hget).1).1.2 hs; simp [hno] at this
        simp only [ValRep, hnonsc] at hrep
        obtain ⟨bvp, hwp, hrep_obj, _, _⟩ := hrep
        cases hwp
        obtain ⟨o, ho, hoa⟩ := objRep_even_mem hrep_obj hev
        obtain ⟨idx, hidx, hget_idx⟩ := obj_mem_idx ho
        have hbd_o : 0 < σ.objs[idx].rc.toInt → σ.objs[idx].rc.toNat + n < 2 ^ 31 - 1 := by
          intro _
          have hle := le_maxObjRc_of_mem (List.getElem_mem hidx)
          have hle2 : maxObjRc σ.objs ≤ Nat.max 1 (maxObjRc σ.objs) := Nat.le_max_right _ _
          have hmax := hres.2.2
          omega
        have hcore := inc_heap_rcInv hinv hclean hpo hnorc hpcb hsth hhih hepres
          hget hlive hno hpers hn hsp_x henvh_x hev hidx (hget_idx ▸ hoa) hbd_o
        obtain ⟨hinv', hclean', hpo', hnorc', hpcb', hsth', hhih', hepres'⟩ := hcore
        let o0 := σ.objs[idx]
        let rc' := if 0 < o0.rc.toInt then o0.rc + BitVec.ofNat 32 n else o0.rc
        let σ' : HState :=
          { st := σ.st, objs := σ.objs.set idx (o0.withRc rc'),
            scr := σ.scr, scrLimbs := σ.scrLimbs }
        have hres' : ResStateInv σ' rem wr (rcr - n) := by
          refine ⟨hres.1, by simpa [σ'] using hres.2.1, ?_⟩
          by_cases hopos : 0 < o0.rc.toInt
          · simpa [σ', rc', hopos, o0] using
              maxObjRc_set_inc_lt hidx hnrcr hres.2.2
          · have hrc'_le : ∀ (hidx' : idx < σ.objs.length),
                (o0.withRc rc').rc.toNat ≤ σ.objs[idx].rc.toNat := by
              intro _; simp [LcnfObj.withRc, rc', hopos, o0]
            have hle_m := maxObjRc_set_le σ.objs idx (o0.withRc rc') hrc'_le
            have hmax_le : Nat.max 1 (maxObjRc (σ.objs.set idx (o0.withRc rc'))) ≤
                Nat.max 1 (maxObjRc σ.objs) :=
              Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hle_m (Nat.le_max_right _ _)⟩
            have := hres.2.2
            simp only [σ']
            omega
        have hdeq_fn : ∀ q' ∈ σ'.objs, ∀ q ∈ σ.objs, q'.addr = q.addr → ObjDataEq q q' := by
          intro q' hq' q hq hqa
          dsimp only [σ'] at hq'
          rw [list_mem_set_iff hidx] at hq'
          rcases hq' with rfl | ⟨j, hj, _, hget_j⟩
          · have hqeq : q = o0 := obj_eq_of_addr_nodup hnodup_objs hq (List.getElem_mem hidx)
              (by simpa [LcnfObj.withRc, o0] using hqa.symm)
            subst hqeq
            have hnn_rc' : 0 ≤ rc'.toInt := by
              have hq'in : o0.withRc rc' ∈ σ'.objs := by
                dsimp only [σ']
                exact List.mem_iff_getElem.mpr ⟨idx, by simp [hidx], by simp⟩
              exact (hinv'.1.1.2.1 _ hq'in).2.2.1
            exact objDataEq_withRc (hwf_all _ (List.getElem_mem hidx)) rc' hnn_rc'
          · have hqeq : q = q' := obj_eq_of_addr_nodup hnodup_objs hq
              (hget_j ▸ List.getElem_mem hj) hqa.symm
            subst hqeq; exact objDataEq_refl q (hwf_all q hq)
        refine ⟨idx, hidx, hget_idx ▸ hoa, hbd_o, ?_⟩
        exact hk
          (rf' := { rf with ctx := rf.ctx.put { v with owned := v.owned + n, excl := false } })
          (σ' := σ') (rcr' := rcr - n)
          hwf_k hpr_k hinv' hclean' hpo' hnorc' hpcb' hsth' hhih' hepres' hres' hdeq_fn
          ⟨rfl, rfl, rfl, Or.inr ⟨v, hget, by simp [hno, hpers, hn0], rfl⟩⟩
      · have htobj : v.ty = LcTy.tobject :=
          tobject_of_ne_even hinv hget hlive hneeds henvh_x hev
        simp [hev]
        have hcore := inc_tag_rcInv hinv hclean hpo hnorc hpcb hsth hhih hepres
          hget hlive hno hpers hn henvh_x hev
        obtain ⟨hinv', hclean', hpo', hnorc', hpcb', hsth', hhih', hepres'⟩ := hcore
        have hres' : ResStateInv σ rem wr (rcr - n) :=
          ⟨hres.1, hres.2.1, by have := hres.2.2; omega⟩
        exact ⟨hchk (by rw [htobj]; rfl), htobj,
          hk
            (rf' := { rf with ctx := rf.ctx.put { v with owned := v.owned + n, excl := false } })
            (σ' := σ) (rcr' := rcr - n)
            hwf_k hpr_k hinv' hclean' hpo' hnorc' hpcb' hsth' hhih' hepres' hres'
            (fun _ hq' q hq hqa => by
              have hqwf := hwf_all q hq
              have hqeq := obj_eq_of_addr_nodup hnodup_objs hq' hq hqa
              rw [hqeq]; exact objDataEq_refl q hqwf)
            ⟨rfl, rfl, rfl, Or.inr ⟨v, hget, by simp [hno, hpers, hn0], rfl⟩⟩⟩

/-- Stepwise simulation for `LcCode.inc`: advances `HWp` given `perceusCodeWf`, `PRWp`,
    and the Perceus frame/resource invariants. -/
public theorem inc_step {m : LcModule} {env : RcModEnv} {retTy : LcTy} {Δr : PResEnv}
    {Δh : HEnv} {rt : BitVec 64} {J : HJEnv} {Jp : PResJEnv}
    {Q : PResPost} {Xp : PResXPost} {Qh : HPost} {Xh : HXPost}
    {jps : List RcJpInfo} {rf rf0 : RcFrame} {σ σ0 : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr : Nat}
    {x n : Nat} {chk : Bool} {k : LcCode}
    (hwf : perceusCodeWf env retTy jps rf.ctx sm (LcCode.inc x n chk k) = true)
    (hpr : PRWp m env retTy Δr jps rf.ctx Jp ρP rem wr rcr Q Xp (LcCode.inc x n chk k))
    (hinv : RcInv rt rf σ) (hclean : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hnorc : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hepres : EntryPres rf0 σ0 rf σ) (hres : ResStateInv σ rem wr rcr)
    (hk : ∀ {rf' : RcFrame} {σ' : HState} {rcr' : Nat},
      perceusCodeWf env retTy jps rf'.ctx sm k = true →
      PRWp m env retTy Δr jps rf'.ctx Jp ρP rem wr rcr' Q Xp k →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs →
      EntryPres rf0 σ0 rf' σ' → ResStateInv σ' rem wr rcr' →
      (∀ q' ∈ σ'.objs, ∀ q ∈ σ.objs, q'.addr = q.addr → ObjDataEq q q') →
      HWp Δh rt retTy J rf'.envH Qh Xh k σ') :
    HWp Δh rt retTy J rf.envH Qh Xh (LcCode.inc x n chk k) σ :=
  inc_step_ctx hwf hpr hinv hclean hpo hnorc hpcb hsth hhih hepres hres
    fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 _ => hk h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

end IncStep

end LeanQbe.T.LeanLCNF.Sem
