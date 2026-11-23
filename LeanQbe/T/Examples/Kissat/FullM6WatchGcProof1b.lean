module

public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof1

/-!
# Kissat M6 Watch/GC Proofs Part 1b: Binary Dedup & Watch Sweep (`full_sweep_bins_m6`)

Proves `WatchSliceLtOk`, `full_sweep_bins_range_m6_wp`, and `full_sweep_bins_m6_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6WatchGc

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat.Full
open FullReduceHelpers
open FullReduceSpecs (ModeWatchSliceOk BinOnlyWatchSliceOk)
open Kraken.Bedrock2.Test
open scoped FullArenaTactics M6Tactics1

private theorem bv64_ofNat_toNat_id {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem bv64_add1_nat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

inductive WatchSliceLtOk (keep : Nat) (F_cur : List (List Nat)) (k : FullCoreState) (lit : Nat) :
    Nat → Nat → Prop where
  | empty {p} : WatchSliceLtOk keep F_cur k lit p 0
  | bin {p rem w0} :
      k.wstk[p]? = some w0 → (w0 &&& 0x80000000#32) ≠ 0#32 → w0 ≠ 0xFFFFFFFF#32 →
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) →
      WatchSliceLtOk keep F_cur k lit (p + 1) rem → WatchSliceLtOk keep F_cur k lit p (rem + 1)
  | large {p rem w0 cref} :
      k.wstk[p]? = some w0 → k.wstk[p + 1]? = some cref →
      (w0 &&& 0x80000000#32) = 0#32 → cref.toNat < 0x80000000 → cref.toNat < keep →
      cref.toNat ∈ fullArenaClauseRefsCore k →
      WatchSliceLtOk keep F_cur k lit (p + 2) rem → WatchSliceLtOk keep F_cur k lit p (rem + 2)

theorem WatchSliceLtOk.toBinOnly {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    (h : WatchSliceLtOk 0 F_cur k lit p rem) : BinOnlyWatchSliceOk F_cur k lit p rem := by
  induction h with
  | empty => exact .empty
  | bin hp hf hne hlt hent _ ih => exact .bin hp hf hne hlt hent ih
  | large _ _ _ _ hk => cases hk

theorem WatchSliceLtOk.toWatchSliceOk {keep : Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {lit p rem : Nat}
    (h : WatchSliceLtOk keep F_cur k lit p rem) : WatchSliceOk F_cur k lit p rem := by
  induction h with
  | empty => exact .empty
  | bin hp hf hne hlt hent _ ih => exact .bin hp hf hne hlt hent ih
  | large hp1 hp2 hflag hlt _ hcref _ ih => exact .large hp1 hp2 hflag hlt hcref ih

theorem WatchSliceLtOk.ne_sentinel {keep : Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {lit p rem : Nat}
    (h : WatchSliceLtOk keep F_cur k lit p rem) :
    ∀ idx < rem, k.wstk[p + idx]? ≠ some 0xFFFFFFFF#32 :=
  h.toWatchSliceOk.ne_sentinel

theorem WatchSliceLtOk.relocate {keep : Nat} {F F' : List (List Nat)}
    {k k' : FullCoreState} {lit p p' rem : Nat}
    (hF : (cnfOfClauses F').Entails (cnfOfClauses F)) (hvars : k.cur_vars ≤ k'.cur_vars)
    (hkeep : ∀ r ∈ fullArenaClauseRefsCore k, r < keep → r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ j < rem, k'.wstk[p' + j]? = k.wstk[p + j]?)
    (h : WatchSliceLtOk keep F k lit p rem) : WatchSliceLtOk keep F' k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hf hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hne (by omega)
      (CNF.entails_clause_trans hF hent) (ih (p' := p' + 1) fun j hj => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 1) (by omega))
  | @large p rem w0 cref hp1 hp2 hfl hlt hkp hcr _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp1)
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (hwstk 1 (by omega)).trans hp2)
      hfl hlt hkp (hkeep cref.toNat hcr hkp)
      (ih (p' := p' + 2) fun j hj => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 2) (by omega))

theorem WatchSliceLtOk.append_bin {keep : Nat} {F_cur : List (List Nat)}
    {k k' : FullCoreState} {lit p p' rem : Nat} {w0 : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hkeep : ∀ r ∈ fullArenaClauseRefsCore k, r < keep → r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ j < rem, k'.wstk[p' + j]? = k.wstk[p + j]?)
    (h : WatchSliceLtOk keep F_cur k lit p rem) (hw0 : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    WatchSliceLtOk keep F_cur k' lit p' (rem + 1) := by
  induction h generalizing p' with
  | empty => exact .bin (by simpa using hw0) hflag hne hlt hent .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he
      (ih (p' := p' + 1)
        (fun j hj => by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 1) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0))
  | @large p rem w cref hp1 hp2 hfl hltc hkp hcr _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp1)
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (hwstk 1 (by omega)).trans hp2)
      hfl hltc hkp (hkeep cref.toNat hcr hkp)
      (ih (p' := p' + 2)
        (fun j hj => by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 2) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0))

theorem WatchSliceLtOk.append_large {keep : Nat} {F_cur : List (List Nat)}
    {k k' : FullCoreState} {lit p p' rem : Nat} {w0 cref : BitVec 32}
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hkeep : ∀ r ∈ fullArenaClauseRefsCore k, r < keep → r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ j < rem, k'.wstk[p' + j]? = k.wstk[p + j]?)
    (h : WatchSliceLtOk keep F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0) (hcr : k'.wstk[p' + rem + 1]? = some cref)
    (hfl : (w0 &&& 0x80000000#32) = 0#32) (hltc : cref.toNat < 0x80000000)
    (hkp : cref.toNat < keep) (href : cref.toNat ∈ fullArenaClauseRefsCore k') :
    WatchSliceLtOk keep F_cur k' lit p' (rem + 2) := by
  induction h generalizing p' with
  | empty =>
    exact .large (by simpa using hw0) (by simpa [Nat.add_assoc] using hcr) hfl hltc hkp href .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he
      (ih (p' := p' + 1) (fun j hj => by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 1) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcr))
  | @large p rem w cr hp1 hp2 hfl2 hltc2 hkp2 hcr2 _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp1)
      (by simpa [Nat.add_assoc, Nat.add_comm] using (hwstk 1 (by omega)).trans hp2)
      hfl2 hltc2 hkp2 (hkeep cr.toNat hcr2 hkp2)
      (ih (p' := p' + 2) (fun j hj => by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 2) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcr))

def fullSweepBinsRangeSpec : Spec [i64, i64] [] := fun (h, keep_before, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (0 < keep_before.toNat → s.core.dense_mode = 0#64) ∧
    FullWitnessInv c F0 F_cur s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wlen' nb' ws' m',
      let s' : FullState :=
        { s with
          core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                wusable := 0#64, num_binary := nb' }
          scratch := { s.scratch with wsort := ws' } }
      s'.LengthsOk c → WatchStackLayout s'.core →
      (∀ l < 2 * s.core.cur_vars,
        WatchSliceLtOk keep_before.toNat F_cur s'.core l (fullWatchOff s' l) (fullWatchSize s' l)) →
      FullWitnessInv c F0 F_cur s'.core → (FullMem c s' ⋆ R) m' → Q () m'

theorem fullSweepBinsRangeSpec.intro {h keep_before : BitVec 64} {m : Mem 64}
    {Q : Post []} {X : XPost} (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (hh : h = c.hdr) (hlen : s.LengthsOk c)
    (hdkp : 0 < keep_before.toNat → s.core.dense_mode = 0#64)
    (hw : FullWitnessInv c F0 F_cur s.core) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ wvec' wstk' wlen' nb' ws' m',
      let s' : FullState :=
        { s with
          core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                wusable := 0#64, num_binary := nb' }
          scratch := { s.scratch with wsort := ws' } }
      s'.LengthsOk c → WatchStackLayout s'.core →
      (∀ l < 2 * s.core.cur_vars,
        WatchSliceLtOk keep_before.toNat F_cur s'.core l
          (fullWatchOff s' l) (fullWatchSize s' l)) →
      FullWitnessInv c F0 F_cur s'.core → (FullMem c s' ⋆ R) m' → Q () m') :
    fullSweepBinsRangeSpec (h, keep_before, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hlen, hdkp, hw, hm, hQ⟩

private theorem full_sweep_bins_range_finish_lit {c : FullCfg} {F_cur : List (List Nat)}
    {keep : Nat} {kL : FullCoreState} {sc : FullScratch} {wstk1 wstk2 : List (BitVec 32)}
    {wu' nb1 : BitVec 64} {l q_nat : Nat}
    (hlenL : kL.LengthsOk c) (hscrL : sc.LengthsOk c) (hdkp : 0 < keep → kL.dense_mode = 0#64)
    (hwatL : ModeWatchesInv F_cur kL)
    (hltL : ∀ j < l, WatchSliceLtOk keep F_cur kL j (fullWatchOffCore kL j)
      (fullWatchSizeCore kL j))
    (hl_lt : l < 2 * kL.cur_vars) (hlen2 : wstk2.length = c.wcap)
    (hoq : fullWatchOffCore kL l ≤ q_nat)
    (hqe : q_nat ≤ fullWatchOffCore kL l + fullWatchSizeCore kL l)
    (hout1 : ∀ i, i < fullWatchOffCore kL l ∨ fullWatchOffCore kL l + fullWatchSizeCore kL l ≤ i →
      wstk1[i]? = kL.wstk[i]?)
    (hout2 : ∀ i, i < q_nat ∨ fullWatchOffCore kL l + fullWatchSizeCore kL l ≤ i →
      wstk2[i]? = wstk1[i]?)
    (hpre1 : WatchSliceLtOk keep F_cur { kL with wstk := wstk1 } l (fullWatchOffCore kL l)
      (q_nat - fullWatchOffCore kL l))
    (kL' : FullCoreState)
    (hk' : kL' = { kL with wvec := kL.wvec.set (2 * l + 1)
                                     (BitVec.ofNat 32 (q_nat - fullWatchOffCore kL l)),
                           wstk := wstk2, wusable := wu', num_binary := nb1 }) :
    FullState.LengthsOk c ⟨kL', sc⟩ ∧ ModeWatchesInv F_cur kL' ∧
    ∀ j < l + 1, WatchSliceLtOk keep F_cur kL' j (fullWatchOffCore kL' j)
      (fullWatchSizeCore kL' j) := by
  subst hk'
  let off0 := fullWatchOffCore kL l; let sz0 := fullWatchSizeCore kL l
  let wvec' := kL.wvec.set (2 * l + 1) (BitVec.ofNat 32 (q_nat - off0))
  have hout_fin : ∀ i, i < off0 ∨ off0 + sz0 ≤ i → wstk2[i]? = kL.wstk[i]? :=
    fun i hi => by rw [hout2 i (by omega), hout1 i (by omega)]
  have hlt_l : WatchSliceLtOk keep F_cur { kL with wstk := wstk2 } l off0 (q_nat - off0) :=
    WatchSliceLtOk.relocate (k := { kL with wstk := wstk1 }) (k' := { kL with wstk := wstk2 })
      (p := off0) (p' := off0) (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _)
      (fun _ hr _ => hr) (fun j hj => hout2 (off0 + j) (Or.inl (by omega))) hpre1
  have hmode_l : ModeWatchSliceOk (decide (kL.dense_mode ≠ 0#64)) F_cur { kL with wstk := wstk2 }
      l off0 (q_nat - off0) := by
    by_cases hd : decide (kL.dense_mode ≠ 0#64) = true
    · simp only [ModeWatchSliceOk, hd, ↓reduceIte]
      by_cases hkz : keep = 0
      · subst hkz; exact hlt_l.toBinOnly.toDenseWatchSliceOk
      · exfalso; have h0 := hdkp (Nat.pos_of_ne_zero hkz); simp [h0] at hd
    · simp only [ModeWatchSliceOk, hd, Bool.false_eq_true, ↓reduceIte]; exact hlt_l.toWatchSliceOk
  have hwat' := modeWatchesInv_shrink_slice hwatL hlenL hl_lt (new_sz := q_nat - off0) (by omega)
    hout_fin wu' nb1 hmode_l
  obtain ⟨_, hoff_self, hsz_self, hother⟩ :=
    watchStackLayout_shrink_slice hwatL.layout hlenL hl_lt
      (new_sz := q_nat - off0) (by omega) hout_fin hlt_l.ne_sentinel wu' nb1
  refine ⟨⟨{ hlenL with wvec_len := by simp [hlenL.wvec_len],
                        wstk_len_arr := hlen2 }, hscrL⟩, hwat', fun j hj => ?_⟩
  by_cases hjl : j = l
  · subst j; rw [hoff_self, hsz_self]
    exact WatchSliceLtOk.relocate (k := { kL with wstk := wstk2 })
      (k' := { kL with wvec := wvec', wstk := wstk2, wusable := wu', num_binary := nb1 })
      (p := off0) (p' := off0) (by rw [CNF.entails_def]; exact fun _ p => p)
      (Nat.le_refl _) (fun _ hr _ => hr) (fun _ _ => rfl) hlt_l
  · obtain ⟨ho, hs, hws⟩ := hother j (by omega) hjl; rw [ho, hs]
    exact WatchSliceLtOk.relocate (k := kL)
      (k' := { kL with wvec := wvec', wstk := wstk2, wusable := wu', num_binary := nb1 })
      (p := fullWatchOffCore kL j) (p' := fullWatchOffCore kL j)
      (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _)
      (fun _ hr _ => hr) hws (hltL j (by omega))

private abbrev sweepBinState (s : FullState) (wvecL wstk1 : List (BitVec 32))
    (wuL nb1 : BitVec 64) (ws1 : List (BitVec 32)) : FullState :=
  { s with
    core := { s.core with wvec := wvecL, wstk := wstk1, wusable := wuL, num_binary := nb1 }
    scratch := { s.scratch with wsort := ws1 } }

private def SweepBinPInv (c : FullCfg) (F_cur : List (List Nat)) (s sL : FullState)
    (R : Mem 64 → Prop) (dense : Bool) (keep_before : Nat)
    (l : BitVec 64) (off0 end0 : Nat) (wvecL wstkL : List (BitVec 32)) (wuL nbL : BitVec 64)
    (arg : Tup Val [i64, i64]) (m1 : Mem 64) : Prop :=
  let (p, q, ()) := arg
  off0 ≤ q.toNat ∧ q.toNat ≤ p.toNat ∧ p.toNat ≤ end0 ∧
  ∃ wstk1 nb1 ws1, wstk1.length = c.wcap ∧ ws1.length = 2 * c.max_vars ∧
    (∀ i, i < off0 ∨ p.toNat ≤ i → wstk1[i]? = wstkL[i]?) ∧
    ModeWatchSliceOk dense F_cur sL.core l.toNat p.toNat (end0 - p.toNat) ∧
    WatchSliceLtOk keep_before F_cur
      (sweepBinState s wvecL wstk1 wuL nbL ws1).core l.toNat off0 (q.toNat - off0) ∧
    (FullMem c (sweepBinState s wvecL wstk1 wuL nb1 ws1) ⋆ R) m1

private def SweepBinBInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (keep_before : Nat) (l : BitVec 64) (off0 p0 : Nat)
    (wvecL wstkL : List (BitVec 32)) (wuL nbL : BitVec 64)
    (arg : Tup Val [i64, i64]) (mB : Mem 64) : Prop :=
  let (p', q', ()) := arg
  p0 ≤ p'.toNat ∧ off0 ≤ q'.toNat ∧ q'.toNat ≤ p'.toNat ∧
  ∃ wstk' nb' ws', wstk'.length = c.wcap ∧ ws'.length = 2 * c.max_vars ∧
    (∀ i, i < off0 ∨ p'.toNat ≤ i → wstk'[i]? = wstkL[i]?) ∧
    WatchSliceLtOk keep_before F_cur
      (sweepBinState s wvecL wstk' wuL nbL ws').core l.toNat off0 (q'.toNat - off0) ∧
    (FullMem c (sweepBinState s wvecL wstk' wuL nb' ws') ⋆ R) mB

private def SweepBinQInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (keep_before : Nat) (l : BitVec 64) (off0 pend : Nat)
    (wvecL wstkL : List (BitVec 32)) (wuL nbL : BitVec 64)
    (arg : Tup Val [i64]) (mQ : Mem 64) : Prop :=
  let (q', ()) := arg
  off0 ≤ q'.toNat ∧ q'.toNat ≤ pend ∧
  ∃ wstk' nb' ws', wstk'.length = c.wcap ∧ ws'.length = 2 * c.max_vars ∧
    (∀ i, i < off0 ∨ pend ≤ i → wstk'[i]? = wstkL[i]?) ∧
    WatchSliceLtOk keep_before F_cur
      (sweepBinState s wvecL wstk' wuL nbL ws').core l.toNat off0 (q'.toNat - off0) ∧
    (FullMem c (sweepBinState s wvecL wstk' wuL nb' ws') ⋆ R) mQ

private abbrev lfixOp1 {t r : Ty} (code : OpCode [t] [r]) (a : Arg Val t) : Op Val [r] :=
  Op.mk code (a, ())

private abbrev lfixOp2 {t r : Ty} (code : OpCode [t, t] [r]) (a b : Arg Val t) : Op Val [r] :=
  Op.mk code (a, b, ())

open Lean Elab Tactic in
local elab "lfix_steps" : tactic => do
  for _ in [:100] do
    let _ ← evalTactic (← `(tactic| try m6_unmdata))
    let ty := (← Lean.instantiateMVars (← (← getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
      let e := (ty.getArg! 4).consumeMData.headBeta
      if e.isAppOf ``LeanQbe.T.Expr.load || e.isAppOf ``LeanQbe.T.Expr.jnz then break
    let _ ← evalTactic (← `(tactic| repeat m6_strip))
    if !(← LeanQbe.T.C0Step.stepOnce) then break

/-- `vals[l] > 0 || (prop_done && vals[l] < 0)` tail (two `i8` reloads of `vals[l]`). -/
private abbrev lfixValsTail {rs : List Ty} (J : Cont [Ty.bool]) (pVals l : Val i64)
    (pd : Val Ty.bool) : Expr Val Cont rs :=
  Expr.let_ (lfixOp2 (.add i64) (Arg.var pVals) (Arg.var l)) fun p =>
    Expr.load i8 (Arg.var p.fst) fun ld =>
      Expr.let_ (lfixOp1 (.trunc 32 8) (Arg.imm 0)) fun p =>
        Expr.let_ (lfixOp1 (.sext 8 32) (Arg.var ld)) fun p_1 =>
          Expr.let_ (lfixOp1 (.sext 8 32) (Arg.var p.fst)) fun p =>
            Expr.let_ (lfixOp2 (.cmp .sgt i32 .bool (by decide)) (Arg.var p_1.fst) (Arg.var p.fst))
              fun p =>
              Expr.jnz (Arg.var p.fst) (Expr.jump (J, ()).fst (Arg.imm true, ()))
                (Expr.jnz (Arg.var pd)
                  (Expr.let_ (lfixOp2 (.add i64) (Arg.var pVals) (Arg.var l)) fun p =>
                    Expr.load i8 (Arg.var p.fst) fun ld =>
                      Expr.let_ (lfixOp1 (.trunc 32 8) (Arg.imm 0)) fun p =>
                        Expr.let_ (lfixOp1 (.sext 8 32) (Arg.var ld)) fun p_1 =>
                          Expr.let_ (lfixOp1 (.sext 8 32) (Arg.var p.fst)) fun p =>
                            Expr.let_ (lfixOp2 (.cmp .slt i32 .bool (by decide))
                              (Arg.var p_1.fst) (Arg.var p.fst)) fun p =>
                              Expr.jnz (Arg.var p.fst) (Expr.jump (J, ()).fst (Arg.imm true, ()))
                                (Expr.jump (J, ()).fst (Arg.imm false, ())))
                  (Expr.jump (J, ()).fst (Arg.imm false, ())))

private theorem sweep_bins_vals_tail_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {pVals l : Val i64} {pd : Val Ty.bool} {valV : BitVec 8}
    (J : Cont [Ty.bool]) (h2 : loadVal m i8 (pVals + l) = some valV)
    (hJ : ∀ b : Bool, J (b, ()) m) :
    wp Γ Q X (lfixValsTail J pVals l pd) m := by
  unfold lfixValsTail
  lfix_steps; rw [wp_load]; refine ⟨valV, h2, ?_⟩
  lfix_steps; refine wp_jnz_of (fun _ => by lfix_steps; exact hJ true) (fun _ => ?_)
  lfix_steps; refine wp_jnz_of (fun _ => ?_) (fun _ => by lfix_steps; exact hJ false)
  lfix_steps; rw [wp_load]; refine ⟨valV, h2, ?_⟩
  lfix_steps; refine wp_jnz_of (fun _ => by lfix_steps; exact hJ true)
    (fun _ => by lfix_steps; exact hJ false)

private theorem sweep_bins_lfix_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {pLvl pVals l : Val i64} {pd : Val Ty.bool} {lvlV : BitVec 32}
    {valV : BitVec 8}
    (J : Cont [Ty.bool])
    (h1 : loadVal m i32 (pLvl + (l >>> (1 : Nat)) * 4#64) = some lvlV)
    (h2 : loadVal m i8 (pVals + l) = some valV)
    (hJ : ∀ b : Bool, J (b, ()) m) :
    wp Γ Q X
      (Expr.let_ (lfixOp1 (.sext 32 64) (Arg.imm 1)) fun p =>
        Expr.let_ (lfixOp2 (.lshr i64) (Arg.var l) (Arg.var p.fst)) fun p =>
          Expr.let_ (lfixOp2 (.mul i64) (Arg.var p.fst) (Arg.imm 4)) fun p =>
            Expr.let_ (lfixOp2 (.add i64) (Arg.var pLvl) (Arg.var p.fst)) fun p =>
              Expr.load i32 (Arg.var p.fst) fun ld =>
                Expr.let_ (lfixOp2 (.cmp .eq i32 .bool (by decide)) (Arg.var ld) (Arg.imm 0))
                  fun p =>
                  Expr.jnz (Arg.var p.fst) (lfixValsTail J pVals l pd)
                    (Expr.jump (J, ()).fst (Arg.imm false, ()))) m := by
  lfix_steps
  rw [wp_load]; refine ⟨lvlV, ?_, ?_⟩
  · simpa [BitVec.ushiftRight] using h1
  · lfix_steps; refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
    · exact sweep_bins_vals_tail_wp J h2 hJ
    · lfix_steps; exact hJ false

/-- `vals[ot] > 0 || (prop_done && vals[ot] < 0)` tail for a `u32` literal `ot`. -/
private abbrev ofixValsTail {rs : List Ty} (J : Cont [Ty.bool]) (pVals : Val i64) (ot : Val i32)
    (pd : Val Ty.bool) : Expr Val Cont rs :=
  Expr.let_ (lfixOp1 (.zext 32 64) (Arg.var ot)) fun p =>
    Expr.let_ (lfixOp2 (.add i64) (Arg.var pVals) (Arg.var p.fst)) fun p =>
      Expr.load i8 (Arg.var p.fst) fun ld =>
        Expr.let_ (lfixOp1 (.trunc 32 8) (Arg.imm 0)) fun p =>
          Expr.let_ (lfixOp1 (.sext 8 32) (Arg.var ld)) fun p_1 =>
            Expr.let_ (lfixOp1 (.sext 8 32) (Arg.var p.fst)) fun p =>
              Expr.let_ (lfixOp2 (.cmp .sgt i32 .bool (by decide)) (Arg.var p_1.fst)
                (Arg.var p.fst)) fun p =>
                Expr.jnz (Arg.var p.fst) (Expr.jump (J, ()).fst (Arg.imm true, ()))
                  (Expr.jnz (Arg.var pd)
                    (Expr.let_ (lfixOp1 (.zext 32 64) (Arg.var ot)) fun p =>
                      Expr.let_ (lfixOp2 (.add i64) (Arg.var pVals) (Arg.var p.fst)) fun p =>
                        Expr.load i8 (Arg.var p.fst) fun ld =>
                          Expr.let_ (lfixOp1 (.trunc 32 8) (Arg.imm 0)) fun p =>
                            Expr.let_ (lfixOp1 (.sext 8 32) (Arg.var ld)) fun p_1 =>
                              Expr.let_ (lfixOp1 (.sext 8 32) (Arg.var p.fst)) fun p =>
                                Expr.let_ (lfixOp2 (.cmp .slt i32 .bool (by decide))
                                  (Arg.var p_1.fst) (Arg.var p.fst)) fun p =>
                                  Expr.jnz (Arg.var p.fst)
                                    (Expr.jump (J, ()).fst (Arg.imm true, ()))
                                    (Expr.jump (J, ()).fst (Arg.imm false, ())))
                    (Expr.jump (J, ()).fst (Arg.imm false, ())))

private theorem sweep_bins_ofix_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {pLvl pVals nlits : Val i64} {ot : Val i32} {pd : Val Ty.bool}
    {lvlV : BitVec 32} {valV : BitVec 8}
    (J : Cont [Ty.bool])
    (h1 : loadVal m i32 (pLvl + (ot.setWidth 64 >>> (1 : Nat)) * 4#64) = some lvlV)
    (h2 : loadVal m i8 (pVals + ot.setWidth 64) = some valV)
    (hJ : ∀ b : Bool, J (b, ()) m) :
    wp Γ Q X
      (Expr.let_ (lfixOp1 (.zext 32 64) (Arg.var ot)) fun p =>
        Expr.let_ (lfixOp2 (.cmp .ult i64 .bool (by decide)) (Arg.var p.fst) (Arg.var nlits))
          fun p =>
          Expr.jnz (Arg.var p.fst)
            (Expr.let_ (lfixOp2 (.lshr i32) (Arg.var ot) (Arg.imm 1)) fun p =>
              Expr.let_ (lfixOp1 (.zext 32 64) (Arg.var p.fst)) fun p =>
                Expr.let_ (lfixOp2 (.mul i64) (Arg.var p.fst) (Arg.imm 4)) fun p =>
                  Expr.let_ (lfixOp2 (.add i64) (Arg.var pLvl) (Arg.var p.fst)) fun p =>
                    Expr.load i32 (Arg.var p.fst) fun ld =>
                      Expr.let_ (lfixOp2 (.cmp .eq i32 .bool (by decide)) (Arg.var ld)
                        (Arg.imm 0)) fun p =>
                        Expr.jnz (Arg.var p.fst) (ofixValsTail J pVals ot pd)
                          (Expr.jump (J, ()).fst (Arg.imm false, ())))
            (Expr.jump (J, ()).fst (Arg.imm false, ()))) m := by
  lfix_steps; refine wp_jnz_of (fun _ => ?_) (fun _ => by lfix_steps; exact hJ false)
  lfix_steps; rw [wp_load]; refine ⟨lvlV, ?_, ?_⟩
  · simpa [BitVec.ushiftRight, BitVec.setWidth_ushiftRight] using h1
  lfix_steps; refine wp_jnz_of (fun _ => ?_) (fun _ => by lfix_steps; exact hJ false)
  unfold ofixValsTail
  lfix_steps; rw [wp_load]; refine ⟨valV, by simpa using h2, ?_⟩
  lfix_steps; refine wp_jnz_of (fun _ => by lfix_steps; exact hJ true) (fun _ => ?_)
  lfix_steps; refine wp_jnz_of (fun _ => ?_) (fun _ => by lfix_steps; exact hJ false)
  lfix_steps; rw [wp_load]; refine ⟨valV, by simpa using h2, ?_⟩
  lfix_steps; refine wp_jnz_of (fun _ => by lfix_steps; exact hJ true)
    (fun _ => by lfix_steps; exact hJ false)

theorem full_sweep_bins_range_m6_wp (Γ : Env)
    (hdefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag_m6" [i64] [] a m Q X) :
    ∀ a m Q X, fullSweepBinsRangeSpec a m Q X →
      Func.wp Γ full_sweep_bins_range_m6_body a m Q X := by
  rintro ⟨h, keep_before, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hdkp, hw, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le; have hwv_len := hlen.core_ok.wvec_len
  have hws_len := hlen.core_ok.wstk_len_arr; have hwl_le := hlen.core_ok.wlen_le
  have hv_len := hlen.core_ok.vals_len; have hl_len := hlen.core_ok.lvl_len
  have hwsrt_len := hlen.scratch_ok.wsort_len
  have hmax_lt : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hwcap_lt : c.wcap < 2 * dimacsBound := c.hwcap
  unfold dimacsBound at hmax_lt hwcap_lt; let dense : Bool := decide (s.core.dense_mode ≠ 0#64)
  have hnlits_eq : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat =
      2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, bv64_ofNat_toNat_id (by omega)]; simp [Nat.shiftLeft_eq]; omega
  m6_to_group
  -- Loop 0: initialize `seen[0 .. nlits) = 0xFFFFFFFFu`
  refine wp_loop_inv
    (fun (s0, ()) m0 => s0.toNat ≤ 2 * s.core.cur_vars ∧ ∃ ws0 : List (BitVec 32),
      ws0.length = 2 * c.max_vars ∧
      (FullMem c { s with scratch := { s.scratch with wsort := ws0 } } ⋆ R) m0)
    (fun (s0, ()) _ => 2 * s.core.cur_vars - s0.toNat) (fun J0 hLoop0 => ?_) ?_
  · m6_steps; exact hLoop0 (0#64, ()) m ⟨Nat.zero_le _, s.scratch.wsort, hwsrt_len, hm⟩
  · rintro J0 ⟨s0, ⟨⟩⟩ m0 ⟨hs0_le, ws0, hws0, hm0⟩ hLoop0
    clear hm
    m6_split_fast
    · have hs0_lt : s0.toNat < 2 * s.core.cur_vars := by
        have : s0.toNat < ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
        omega
      have hs0p1 : (s0 + 1#64).toNat = s0.toNat + 1 := bv64_add1_nat (by omega)
      m6_c0_steps
      exact hLoop0 (s0 + 1#64, ()) _ (by dsimp only; rw [hs0p1]; omega)
        ⟨by rw [hs0p1]; omega, ws0.set s0.toNat 0xFFFFFFFF#32, by simp [hws0], hm⟩
    · have hs0_eq : s0.toNat = 2 * s.core.cur_vars := by
        have : ¬ (s0.toNat < ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat) := by
          c0_bound
        omega
      clear hc J0 hLoop0 s0 hs0_le hs0_eq
      m6_c0_steps
      refine wp_loop_inv
        (fun (l, ()) mL =>
          l.toNat ≤ 2 * s.core.cur_vars ∧
          ∃ wvecL wstkL wuL nbL wsL,
            let sL := sweepBinState s wvecL wstkL wuL nbL wsL
            sL.LengthsOk c ∧ ModeWatchesInv F_cur sL.core ∧
            (∀ j < l.toNat, WatchSliceLtOk keep_before.toNat F_cur sL.core j
                (fullWatchOff sL j) (fullWatchSize sL j)) ∧
            (FullMem c sL ⋆ R) mL)
        (fun (l, ()) _ => 2 * s.core.cur_vars - l.toNat) (fun JL hLoopL => ?_) ?_
      · m6_c0_steps
        exact hLoopL (0#64, ()) m0 ⟨Nat.zero_le _, s.core.wvec, s.core.wstk, s.core.wusable,
          s.core.num_binary, ws0, ⟨hlen.core_ok, { hlen.scratch_ok with wsort_len := hws0 }⟩,
          hw.watches, fun _ hj => absurd hj (Nat.not_lt_zero _), hm0⟩
      · rintro JL ⟨l, ⟨⟩⟩ mL ⟨hl_le, wvecL, wstkL, wuL, nbL, wsL, hlenL, hwatL, hltL, hmL⟩ hLoopL
        let sL := sweepBinState s wvecL wstkL wuL nbL wsL
        have hwvL_len : wvecL.length = 4 * c.max_vars := hlenL.core_ok.wvec_len
        have hwsL_len : wsL.length = 2 * c.max_vars := hlenL.scratch_ok.wsort_len
        m6_split_fast
        · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
            have : l.toNat < ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
            omega
          have hl1_eq : (l + 1#64).toNat = l.toNat + 1 := bv64_add1_nat (by omega)
          have h2l_eq : (l <<< (1 : Nat)).toNat = 2 * l.toNat := by
            rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
          have h2l1_eq : ((l <<< (1 : Nat)) + 1#64).toNat = 2 * l.toNat + 1 := by
            rw [bv64_add1_nat (by omega), h2l_eq]
          have h2l_lt : 2 * l.toNat < wvecL.length := by omega
          have h2l1_lt : 2 * l.toNat + 1 < wvecL.length := by omega
          have hmod0 : 2 * l.toNat % 2 ^ 64 = 2 * l.toNat := Nat.mod_eq_of_lt (by omega)
          have hmod1 : (2 * l.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
              2 * l.toNat + 1 := by
            rw [show (1 : BitVec 64).toNat = 1 from rfl]; exact Nat.mod_eq_of_lt (by omega)
          let off0 : Nat := fullWatchOff sL l.toNat
          let sz0 : Nat := fullWatchSize sL l.toNat
          let offW : BitVec 32 := wvecL[(l <<< (1 : Nat)).toNat]'(by omega)
          let szW : BitVec 32 := wvecL[((l <<< (1 : Nat)) + 1#64).toNat]'(by omega)
          have hoff_idx : (wvecL[2 * l.toNat]'h2l_lt).toNat = off0 := by
            unfold off0 fullWatchOff fullWatchOffCore sL sweepBinState
            rw [List.getElem?_eq_getElem h2l_lt, Option.getD_some]
          have hsz_idx : (wvecL[2 * l.toNat + 1]'h2l1_lt).toNat = sz0 := by
            unfold sz0 fullWatchSize fullWatchSizeCore sL sweepBinState
            rw [List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
          have hoff_eq : offW.toNat = off0 := by unfold offW; simp only [h2l_eq]; exact hoff_idx
          have hsz_eq : szW.toNat = sz0 := by unfold szW; simp only [h2l1_eq]; exact hsz_idx
          have hbd_end : off0 + sz0 ≤ s.core.wlen := hwatL.bounds l.toNat hl_lt
          have hslice0 : ModeWatchSliceOk dense F_cur sL.core l.toNat off0 sz0 :=
            modeWatchesInv_slice_of_lt hwatL hl_lt
          clear hwv_len hws_len hw hlen hm0 hdefrag hQ
          m6_split_fast
          · -- `sz == 0`: advance `l + 1`
            have hsz0 : sz0 = 0 := by
              have h1 := congrArg BitVec.toNat hc
              simp only [hmod1] at h1
              rw [zext_toNat (wvecL[2 * l.toNat + 1]'h2l1_lt) (by decide), hsz_idx] at h1
              exact h1
            m6_c0_steps
            refine hLoopL (l + 1#64, ()) mL (by dsimp only; rw [hl1_eq]; omega)
              ⟨by rw [hl1_eq]; omega, wvecL, wstkL, wuL, nbL, wsL, hlenL, hwatL,
               fun j hj => ?_, hmL⟩
            rw [hl1_eq] at hj
            by_cases hjl : j = l.toNat
            · subst hjl; change WatchSliceLtOk keep_before.toNat F_cur sL.core l.toNat off0 sz0
              rw [hsz0]; exact .empty
            · exact hltL j (by omega)
          · -- `sz > 0`
            have hlv_eq : (l >>> (1 : Nat)).toNat = l.toNat / 2 := by
              simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
            have hlv_lt : (l >>> (1 : Nat)).toNat < s.core.lvl.length := by rw [hlv_eq]; omega
            have hl_v : l.toNat < s.core.vals.length := by omega
            let end0 : Nat := off0 + sz0
            m6_to_group
            refine wp_join_group (fun (_lfix, ()) mF => mL = mF) ?_ ?_
            · rintro _ ⟨lfix, ⟨⟩⟩ _ rfl
              m6_c0_steps
              refine wp_loop_inv
                (SweepBinPInv c F_cur s sL R dense keep_before.toNat l off0 end0 wvecL wstkL
                  wuL nbL)
                (fun (p, _, ()) _ => end0 - p.toNat) (fun J1 hLoop1 => ?_) ?_
              · m6_c0_steps
                have hoff64 : (offW.setWidth 64).toNat = off0 := by
                  rw [zext_toNat offW (by decide), hoff_eq]
                refine hLoop1 _ mL ⟨by rw [hoff64]; exact Nat.le_refl _,
                  by rw [hoff64]; exact Nat.le_refl _, by rw [hoff64]; omega,
                  wstkL, nbL, wsL, hlenL.core_ok.wstk_len_arr, hwsL_len,
                  fun _ _ => rfl, ?_, ?_, hmL⟩
                · rw [hoff64, show end0 - off0 = sz0 by omega]; exact hslice0
                · rw [hoff64, Nat.sub_self]; exact .empty
              · rintro J1 ⟨p, q, ⟨⟩⟩ m1 ⟨hoq, hqp, hpe, wstk1, nb1, ws1, hlen1, hws1,
                  hout1, hrem1, hpre1, hm1⟩ hLoop1
                m6_split_fast
                · have hp_lt : p.toNat < end0 := by
                    have h1 := hc; simp only [hmod0, hmod1, hoff_idx, hsz_idx] at h1; omega
                  have hp_w : p.toNat < wstk1.length := by omega
                  have hq_w : q.toNat < wstk1.length := by omega
                  let w0 := wstk1[p.toNat]'hp_w
                  have hw0_orig : sL.core.wstk[p.toNat]? = some w0 := by
                    dsimp only [sL, sweepBinState]
                    rw [← hout1 p.toNat (Or.inr (Nat.le_refl _)), List.getElem?_eq_getElem hp_w]
                  have hstep := hrem1.step (by omega) hw0_orig
                  m6_to_group
                  refine wp_join_group (ts := [i64, i64])
                    (fun (p', q', ()) mB => p.toNat < p'.toNat ∧ p'.toNat ≤ end0 ∧
                      off0 ≤ q'.toNat ∧ q'.toNat ≤ p'.toNat ∧
                      ∃ wstk' nb' ws', wstk'.length = c.wcap ∧ ws'.length = 2 * c.max_vars ∧
                        (∀ i, i < off0 ∨ p'.toNat ≤ i → wstk'[i]? = wstkL[i]?) ∧
                        ModeWatchSliceOk dense F_cur sL.core l.toNat p'.toNat
                          (end0 - p'.toNat) ∧
                        WatchSliceLtOk keep_before.toNat F_cur
                          (sweepBinState s wvecL wstk' wuL nbL ws').core l.toNat off0
                          (q'.toNat - off0) ∧
                        (FullMem c (sweepBinState s wvecL wstk' wuL nb' ws') ⋆ R) mB) ?_ ?_
                  · rintro _ ⟨p', q', ⟨⟩⟩ mB ⟨hpp', hpe', hoq', hqp', wstk', nb', ws', hlen',
                      hws', hout', hrem'', hpre', hmB⟩
                    m6_nojoin
                    exact hLoop1 (p', q', ()) mB (by dsimp only; omega)
                      ⟨hoq', hqp', hpe', wstk', nb', ws', hlen', hws', hout', hrem'', hpre', hmB⟩
                  · intro JB hJB
                    m6_split_fast
                    · -- Binary watch
                      have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := by
                        change ((wstk1[p.toNat]'hp_w) &&& 0x80000000#32) ≠ 0#32; assumption
                      obtain ⟨hne, hlt_o, hent_o, hrem'⟩ := hstep.1 hbin
                      have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := bv64_add1_nat (by omega)
                      have hq1_eq : (q + 1#64).toNat = q.toNat + 1 := bv64_add1_nat (by omega)
                      have hot_lt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := hlt_o
                      have hot_v :
                          ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat < s.core.vals.length := by
                        rw [zext_toNat _ (by decide)]; omega
                      have hot_l : (((w0 &&& 0x7FFFFFFF#32).setWidth 64) >>> (1 : Nat)).toNat <
                          s.core.lvl.length := by
                        rw [BitVec.toNat_ushiftRight, zext_toNat _ (by decide),
                          Nat.shiftRight_eq_div_pow]
                        omega
                      m6_to_group
                      refine wp_join_group (fun (_ofix, ()) mO => m1 = mO) ?_ ?_
                      · rintro _ ⟨_ofix, ⟨⟩⟩ _ rfl
                        m6_to_group
                        refine wp_join_group (ts := [i64])
                          (SweepBinQInv c F_cur s R keep_before.toNat l off0 (p.toNat + 1)
                            wvecL wstkL wuL nbL) ?_ ?_
                        · rintro _ ⟨q', ⟨⟩⟩ mQ ⟨hoq', hqp', wstk', nb', ws', hlen', hws', hout',
                            hpre', hmQ⟩
                          m6_nojoin
                          exact hJB (p + 1#64, q', ()) mQ
                            ⟨by rw [hp1_eq]; omega, by rw [hp1_eq]; omega, hoq',
                             by rw [hp1_eq]; omega, wstk', nb', ws', hlen', hws',
                             by rw [hp1_eq]; exact hout',
                             by rw [hp1_eq,
                                  show end0 - (p.toNat + 1) = end0 - p.toNat - 1 by omega]
                                exact hrem', hpre', hmQ⟩
                        · intro Jq hJq
                          m6_to_group
                          refine wp_join_group (fun () mD => m1 = mD) ?_ ?_
                          · rintro _ ⟨⟩ mD hmD; subst mD
                            m6_to_group
                            refine wp_join_group
                              (fun () mN => ∃ nb',
                                (FullMem c (sweepBinState s wvecL wstk1 wuL nb' ws1) ⋆ R) mN)
                              ?_ ?_
                            · rintro _ ⟨⟩ mN ⟨nb', hmN⟩; m6_nojoin
                              exact hJq (q, ()) mN ⟨hoq, by omega, wstk1, nb', ws1, hlen1,
                                hws1, fun i hi => hout1 i (by omega), hpre1, hmN⟩
                            · intro JN hJN
                              m6_split_fast
                              · m6_split_fast
                                · m6_nojoin; exact hJN () _ ⟨nb1 - 1#64, hm⟩
                                · m6_nojoin; exact hJN () m1 ⟨nb1, hm1⟩
                              · m6_nojoin; exact hJN () m1 ⟨nb1, hm1⟩
                          · intro Jd hJd
                            clear hLoopL JL hwatL hlenL hslice0 hrem1 hstep
                            m6_to_jnz
                            refine wp_jnz_of (fun hc_l => ?_) (fun hc_nl => ?_)
                            · exact hJd () m1 rfl
                            · m6_to_jnz
                              refine wp_jnz_of (fun hc_o => ?_) (fun hc_no => ?_)
                              · exact hJd () m1 rfl
                              · m6_to_group
                                refine wp_join_group
                                  (SweepBinQInv c F_cur s R keep_before.toNat l off0 (p.toNat + 1)
                                    wvecL wstkL wuL nbL) ?_ ?_
                                · rintro _ ⟨q', ⟨⟩⟩ mQ hq; m6_nojoin; exact hJq (q', ()) mQ hq
                                · intro Jq' hJq'
                                  m6_to_jnz
                                  refine wp_jnz_of (fun hc_f => ?_) (fun hc_nf => ?_)
                                  · simp only [Arg.val_var] at hc_f hc_nl
                                    exfalso; cases hc_nl.symm.trans hc_f
                                  · m6_to_group
                                    refine wp_join_group
                                      (SweepBinQInv c F_cur s R keep_before.toNat l off0
                                        (p.toNat + 1) wvecL wstkL wuL nbL) ?_ ?_
                                    · rintro _ ⟨q', ⟨⟩⟩ mQ hq
                                      m6_nojoin; exact hJq' (q', ()) mQ hq
                                    · intro Jq'' hJq''
                                      have hot_64 : ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                                          ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat :=
                                        by rw [zext_toNat _ (by decide), hnlits_eq]; exact hot_lt
                                      have hot_ws : ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                                          ws1.length := by
                                        rw [zext_toNat _ (by decide)]; omega
                                      have h_t : (((w0 &&& 0x7FFFFFFF#32).setWidth 64).ult
                                          ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat))) =
                                          true := by
                                        simpa [BitVec.ult, decide_eq_true_eq] using hot_64
                                      m6_to_jnz
                                      refine wp_jnz_of (fun hc_lt => ?_) (fun hc_nlt => by
                                        simp only [Arg.val_var] at hc_nlt
                                        cases hc_nlt.symm.trans h_t)
                                      m6_to_jnz
                                      refine wp_jnz_of (fun hc_eq => ?_) (fun hc_neq => ?_)
                                      · m6_to_group
                                        refine wp_join_group
                                          (fun () mN => ∃ nb',
                                            (FullMem c (sweepBinState s wvecL wstk1 wuL nb' ws1) ⋆
                                              R) mN) ?_ ?_
                                        · rintro _ ⟨⟩ mN ⟨nb', hmN⟩; m6_nojoin
                                          exact hJq'' (q, ()) mN ⟨hoq, by omega, wstk1, nb', ws1,
                                            hlen1, hws1, fun i hi => hout1 i (by omega), hpre1,
                                            hmN⟩
                                        · intro JN hJN
                                          m6_split_fast
                                          · m6_split_fast
                                            · m6_nojoin; exact hJN () _ ⟨nb1 - 1#64, hm⟩
                                            · m6_nojoin; exact hJN () m1 ⟨nb1, hm1⟩
                                          · m6_nojoin; exact hJN () m1 ⟨nb1, hm1⟩
                                      · m6_to_group
                                        refine wp_join_group
                                          (fun () mS => ∃ wsS : List (BitVec 32),
                                            wsS.length = 2 * c.max_vars ∧
                                            (FullMem c (sweepBinState s wvecL wstk1 wuL nb1 wsS) ⋆
                                              R) mS) ?_ ?_
                                        · rintro _ ⟨⟩ mS ⟨wsS, hwsS, hmS⟩; m6_nojoin
                                          refine hJq'' (q + 1#64, ()) _
                                            ⟨by rw [hq1_eq]; omega, by rw [hq1_eq]; omega,
                                             wstk1.set q.toNat w0, nb1, wsS, by simp [hlen1], hwsS,
                                             fun i hi => by
                                               rw [List.getElem?_set_ne (by omega)]
                                               exact hout1 i (by omega), ?_, hm⟩
                                          rw [hq1_eq,
                                            show q.toNat + 1 - off0 = (q.toNat - off0) + 1 by omega]
                                          exact WatchSliceLtOk.append_bin
                                            (k := (sweepBinState s wvecL wstk1 wuL nbL ws1).core)
                                            (k' := (sweepBinState s wvecL (wstk1.set q.toNat w0) wuL
                                              nbL ws1).core)
                                            (p := off0) (p' := off0) (Nat.le_refl _)
                                            (fun _ hr _ => hr)
                                            (fun j hj => List.getElem?_set_ne (by omega)) hpre1
                                            (by rw [show off0 + (q.toNat - off0) = q.toNat by omega]
                                                exact List.getElem?_set_self hq_w)
                                            hbin hne hlt_o hent_o
                                        · intro Js hJs; m6_to_jnz
                                          refine wp_jnz_of (fun hc_lt2 => ?_) (fun hc_nlt2 => by
                                            simp only [Arg.val_var] at hc_nlt2
                                            cases hc_nlt2.symm.trans h_t)
                                          m6_usteps; apply wp_store_sep
                                          · exact FullArenaTactics.c0_store_full_wsort _ hot_ws hm1
                                          intro m hm; m6_nojoin
                                          exact hJs () _ ⟨_, by simp [hws1], hm⟩
                      · intro Jo hJo
                        exact sweep_bins_ofix_wp Jo
                          (@FullArenaTactics.c0_load_full_lvl c
                            (sweepBinState s wvecL wstk1 wuL nb1 ws1) R m1 _ hot_l hm1)
                          (@FullArenaTactics.c0_load_full_vals c
                            (sweepBinState s wvecL wstk1 wuL nb1 ws1) R m1 _ hot_v hm1)
                          (fun _ => hJo _ _ rfl)
                    · -- Large watch `(w0, cr)`
                      have hlg : (w0 &&& 0x80000000#32) = 0#32 := by
                        change ((wstk1[p.toNat]'hp_w) &&& 0x80000000#32) = 0#32; assumption
                      obtain ⟨h2rem, cr, hcr_orig, _hsz32, hcr_lt, hcr_ref, hrem'⟩ := hstep.2 hlg
                      have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := bv64_add1_nat (by omega)
                      have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := by
                        rw [BitVec.toNat_add, show (2#64).toNat = 2 from rfl]; omega
                      have hp1_lt : (p + 1#64).toNat < end0 := by omega
                      have hp1_w : (p + 1#64).toNat < wstk1.length := by omega
                      have hcr_eq : wstk1[(p + 1#64).toNat]'hp1_w = cr := by
                        have h1 := hout1 (p.toNat + 1) (Or.inr (by omega))
                        rw [List.getElem?_eq_getElem (by omega : p.toNat + 1 < wstk1.length),
                          hcr_orig] at h1
                        simpa [hp1_eq] using Option.some.inj h1
                      clear hLoopL JL hwatL hlenL hslice0 hstep
                      let invL : Tup Val [i64] → Mem 64 → Prop := fun (q', ()) mK =>
                        off0 ≤ q'.toNat ∧ q'.toNat ≤ p.toNat + 2 ∧
                        ∃ wstk' : List (BitVec 32), wstk'.length = c.wcap ∧
                          (∀ i, i < off0 ∨ p.toNat + 2 ≤ i → wstk'[i]? = wstkL[i]?) ∧
                          WatchSliceLtOk keep_before.toNat F_cur
                            (sweepBinState s wvecL wstk' wuL nbL ws1).core l.toNat off0
                            (q'.toNat - off0) ∧
                          (FullMem c (sweepBinState s wvecL wstk' wuL nb1 ws1) ⋆ R) mK
                      m6_to_group
                      refine wp_join_group (ts := [i64]) invL ?_ ?_
                      · rintro _ ⟨q', ⟨⟩⟩ mK ⟨hoq', hqp', wstk', hlen', hout', hpre', hmK⟩
                        m6_nojoin
                        exact hJB (p + 2#64, q', ()) mK
                          ⟨by rw [hp2_eq]; omega, by rw [hp2_eq]; omega, hoq',
                           by rw [hp2_eq]; omega, wstk', nb1, ws1, hlen', hws1,
                           fun i hi => by rw [hp2_eq] at hi; exact hout' i (by omega),
                           by rw [hp2_eq, show end0 - (p.toNat + 2) = end0 - p.toNat - 2 by omega]
                              exact hrem', hpre', hmK⟩
                      · intro Jp hJp
                        m6_to_jnz
                        refine wp_jnz_of (fun hc_p1 => ?_) (fun hc_np1 => ?_)
                        · m6_to_group
                          refine wp_join_group (ts := [i64]) invL ?_ ?_
                          · rintro _ ⟨q', ⟨⟩⟩ mK hinvK
                            m6_nojoin; exact hJp (q', ()) mK hinvK
                          · intro Jq hJq
                            let d := hJq (q, ()) m1 ⟨hoq, by omega, wstk1, hlen1,
                              fun i hi => hout1 i (by omega), hpre1, hm1⟩
                            m6_to_jnz
                            refine wp_jnz_of (fun hc_kb => ?_) (fun _ => by m6_nojoin; exact d)
                            m6_to_jnz
                            refine wp_jnz_of (fun hc_cr => ?_) (fun _ => by m6_nojoin; exact d)
                            have hkp : cr.toNat < keep_before.toNat := by
                              simp only [Arg.val_var, BitVec.ult, decide_eq_true_eq] at hc_cr
                              have h2 : ((wstk1[(p + 1#64).toNat]'hp1_w).setWidth 64).toNat <
                                  keep_before.toNat := hc_cr
                              rwa [zext_toNat _ (by decide), hcr_eq] at h2
                            have hq1_eq : (q + 1#64).toNat = q.toNat + 1 :=
                              bv64_add1_nat (by omega)
                            have hq2_eq : (q + 2#64).toNat = q.toNat + 2 := by
                              rw [BitVec.toNat_add, show (2#64).toNat = 2 from rfl]; omega
                            have hq1_w : (q + 1#64).toNat < wstk1.length := by omega
                            m6_nojoin
                            let wstk2 := (wstk1.set q.toNat w0).set (q.toNat + 1) cr
                            have hm_eq : (wstk1.set q.toNat w0).set (q + 1#64).toNat
                                (wstk1[(p + 1#64).toNat]'hp1_w) = wstk2 := by
                              simp only [wstk2, hq1_eq, hcr_eq]
                            refine hJq (q + 2#64, ()) _
                              ⟨by rw [hq2_eq]; omega, by rw [hq2_eq]; omega, wstk2,
                               by simp [wstk2, hlen1], fun i hi => by
                                 dsimp only [wstk2]; rw [List.getElem?_set_ne (by omega),
                                   List.getElem?_set_ne (by omega)]; exact hout1 i (by omega),
                               ?_, by rw [← hm_eq]; exact hm⟩
                            rw [hq2_eq, show q.toNat + 2 - off0 = (q.toNat - off0) + 2 by omega]
                            refine WatchSliceLtOk.append_large
                              (k := (sweepBinState s wvecL wstk1 wuL nbL ws1).core)
                              (k' := (sweepBinState s wvecL wstk2 wuL nbL ws1).core)
                              (p := off0) (p' := off0) (Nat.le_refl _) (fun _ hr _ => hr)
                              (fun j hj => by
                                dsimp only [wstk2]; rw [List.getElem?_set_ne (by omega),
                                  List.getElem?_set_ne (by omega)])
                              hpre1
                              (by dsimp only [wstk2]; rw [show off0 + (q.toNat - off0) = q.toNat
                                    by omega, List.getElem?_set_ne (by omega),
                                    List.getElem?_set_self hq_w])
                              (by dsimp only [wstk2]; rw [show off0 + (q.toNat - off0) + 1 =
                                    q.toNat + 1 by omega, List.getElem?_set_self (by simp; omega)])
                              hlg hcr_lt hkp hcr_ref
                        · exfalso
                          rw [Arg.val_var, BitVec.ult, decide_eq_false_iff_not] at hc_np1
                          apply hc_np1
                          change (p + 1#64).toNat <
                            (offW.setWidth 64 + szW.setWidth 64).toNat
                          rw [bv64_add1_nat (by omega), BitVec.toNat_add,
                            zext_toNat offW (by decide), zext_toNat szW (by decide),
                            hoff_eq, hsz_eq, Nat.mod_eq_of_lt (by omega)]
                          omega
                · -- Loop 1 exit (`p = end0`): sentinel fill `[q, end0)`
                  have hp_end : p.toNat = end0 := by
                    have h1 := hc; simp only [hmod0, hmod1, hoff_idx, hsz_idx] at h1; omega
                  m6_c0_steps
                  refine wp_loop_inv
                    (fun (k, ()) m2 =>
                      q.toNat ≤ k.toNat ∧ k.toNat ≤ end0 ∧
                      ∃ wstk2 : List (BitVec 32), wstk2.length = c.wcap ∧
                        (∀ i, i < q.toNat ∨ end0 ≤ i → wstk2[i]? = wstk1[i]?) ∧
                        (FullMem c (sweepBinState s wvecL wstk2 wuL nb1 ws1) ⋆ R) m2)
                    (fun (k, ()) _ => end0 - k.toNat) (fun J2 hLoop2 => ?_) ?_
                  · m6_c0_steps; exact hLoop2 (q, ()) m1 ⟨Nat.le_refl _, by omega, wstk1, hlen1,
                      fun _ _ => rfl, hm1⟩
                  · rintro J2 ⟨k, ⟨⟩⟩ m2 ⟨hqk, hke, wstk2, hlen2, hout2, hm2⟩ hLoop2
                    m6_split_fast
                    · have hk_lt : k.toNat < end0 := by
                        have h1 := hc; simp only [hmod0, hmod1, hoff_idx, hsz_idx] at h1; omega
                      have hk1_eq : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_nat (by omega)
                      m6_c0_steps
                      exact hLoop2 (k + 1#64, ()) _ (by dsimp only; rw [hk1_eq]; omega)
                        ⟨by rw [hk1_eq]; omega, by rw [hk1_eq]; omega,
                         wstk2.set k.toNat 0xFFFFFFFF#32, by simp [hlen2],
                         fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hout2 i hi, hm⟩
                    · -- Exit loop 2: update `wvec[2*l + 1] = q - off`, `wusable += end - q`
                      have hqoff_bv : (q - offW.setWidth 64).setWidth 32
                          = BitVec.ofNat 32 (q.toNat - off0) := by
                        apply BitVec.eq_of_toNat_eq
                        rw [BitVec.toNat_setWidth, BitVec.toNat_sub, zext_toNat offW (by decide),
                          hoff_eq]
                        have hlt32 : q.toNat - off0 < 2 ^ 32 := by omega
                        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32]
                        have : (2 ^ 64 - off0 + q.toNat) % 2 ^ 64 = q.toNat - off0 := by omega
                        rw [this, Nat.mod_eq_of_lt hlt32]
                      m6_c0_steps
                      let wvec' := wvecL.set (2 * l.toNat + 1)
                        (BitVec.ofNat 32 (q.toNat - off0))
                      let wu' := wuL + ((offW.setWidth 64 + szW.setWidth 64) - q)
                      let kL' : FullCoreState := { sL.core with
                        wvec := wvec', wstk := wstk2, wusable := wu', num_binary := nb1 }
                      have hq_end : q.toNat ≤ end0 := by rw [← hp_end]; exact hqp
                      have hout1' : ∀ i, i < off0 ∨ end0 ≤ i → wstk1[i]? = sL.core.wstk[i]? :=
                        fun i hi => hout1 i (by rw [hp_end]; exact hi)
                      have hfin := full_sweep_bins_range_finish_lit (F_cur := F_cur)
                        (kL := sL.core) (wstk1 := wstk1) (wstk2 := wstk2)
                        (keep := keep_before.toNat) hlenL.core_ok
                        hlenL.scratch_ok hdkp hwatL hltL hl_lt hlen2
                        hoq hq_end hout1' hout2 hpre1 kL' rfl
                      have hwv_eq : wvecL.set ((l <<< (1 : Nat)) + 1#64).toNat
                          ((q - offW.setWidth 64).setWidth 32) = wvec' := by
                        simp only [wvec', h2l1_eq, hqoff_bv]
                      refine hLoopL (l + 1#64, ()) _ (by dsimp only; rw [hl1_eq]; omega)
                        ⟨by rw [hl1_eq]; omega, wvec', wstk2, wu', nb1, ws1,
                         ⟨hfin.1.core_ok, { hlenL.scratch_ok with wsort_len := hws1 }⟩,
                         hfin.2.1, fun j hj => hfin.2.2 j (hl1_eq ▸ hj),
                         by rw [← hwv_eq]; exact hm⟩
            · intro J hJ
              exact sweep_bins_lfix_wp J
                (@FullArenaTactics.c0_load_full_lvl c sL R mL (l >>> (1 : Nat)) hlv_lt hmL)
                (@FullArenaTactics.c0_load_full_vals c sL R mL l hl_v hmL)
                (fun _ => hJ _ _ rfl)
        · have hl_eq : l.toNat = 2 * s.core.cur_vars := by
            have : ¬ (l.toNat < ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat) := by
              c0_bound
            omega
          rw [hl_eq] at hltL; clear hwv_len hws_len hm0 hc
          m6_steps; c0_call hdefrag
          refine ⟨c, sL, R, rfl, hlenL, hwatL.layout, hmL,
            fun wvec' wstk' wlen' wsort' m' hlen' hlay' _ hslice' hm' => ?_⟩
          let s' : FullState :=
            { sL with
              core := { sL.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                     wusable := 0#64 }
              scratch := { sL.scratch with wsort := wsort' } }
          have hlt' : ∀ j < 2 * s.core.cur_vars, WatchSliceLtOk keep_before.toNat F_cur s'.core j
              (fullWatchOff s' j) (fullWatchSize s' j) := fun j hj => by
            obtain ⟨hsz_j, hws_j⟩ := hslice' j hj; rw [hsz_j]
            exact WatchSliceLtOk.relocate (k := sL.core) (k' := s'.core)
              (p := fullWatchOff sL j) (p' := fullWatchOff s' j)
              (by rw [CNF.entails_def]; exact fun _ p => p) (Nat.le_refl _)
              (fun _ hr _ => hr) (fun k hk => hws_j k hk) (hltL j hj)
          have hwat' : ModeWatchesInv F_cur s'.core := by
            unfold ModeWatchesInv
            split
            · exact ⟨hlay', fun j hj => (hlt' j hj).toWatchSliceOk⟩
            · next hd =>
              by_cases hkz : keep_before.toNat = 0
              · exact ⟨hlay', fun j hj => (hkz ▸ hlt' j hj).toBinOnly.toDenseWatchSliceOk⟩
              · exfalso; exact hd (by simpa [s', sL] using hdkp (Nat.pos_of_ne_zero hkz))
          exact hQ wvec' wstk' wlen' nbL wsort' _ hlen' hlay' hlt'
            { hw with
              arena := { hw.arena with len_ok := hw.arena.len_ok }
              watches := hwat' } hm'

theorem full_sweep_bins_m6_wp (Γ : Env)
    (hRange : ∀ a m Q X, fullSweepBinsRangeSpec a m Q X →
      Γ "full_sweep_bins_range_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullSweepBinsSpec a m Q X → Func.wp Γ full_sweep_bins_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, hQ⟩
  m6_steps; c0_call hRange
  refine ⟨c, F0, F_cur, s, R, rfl, hlen, by intro hpos; exfalso; revert hpos; decide,
    hw, hm, fun wvec' wstk' wlen' nb' ws' m' hlen' hlay' hlt' hw' hm' => ?_⟩
  let s' : FullState :=
    { s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64,
                            num_binary := nb' }
      scratch := { s.scratch with wsort := ws' } }
  have hbin' : FullReduceSpecs.BinOnlyWatchesInv F_cur s'.core :=
    ⟨hlay', fun j hj => by simpa using (hlt' j hj).toBinOnly⟩
  exact hQ wvec' wstk' wlen' nb' ws' _ hlen' hbin'.toFull hbin'.toDenseWatchesInv hw' hm'

theorem fullSweepBinsRangeSpec_xirrel {a m Q X X'}
    (h : fullSweepBinsRangeSpec a m Q X) : fullSweepBinsRangeSpec a m Q X' := h

end LeanQbe.T.Examples.Kissat.FullM6WatchGc

