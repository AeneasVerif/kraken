module

public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.BitVec
public import LeanQbe.T.Module
public import Kraken.Mem
public import Kraken.Separation

/-!
# Tests & Axiom Audit for `FullM6ProofUtil`

Exercises:
1. Opaque `FullState` / `M6Hdr` record-update abstraction & `probeStep_trans` chaining.
2. `M6Hdr <-> FullHdr` bridge combinators (`SafetySlice`, `Full1..5` & `M6Hdr` WP call lifts).
3. Kernel `BitVec 64` / `BitVec 32` lemmas & `c0_hfast` frame-lift glue (`M6ProofUtilTactics`).
4. `ModuleOk` / `Env.noExit` composition & `tableImpl_prefix_of_moduleOk` transport.
-/

set_option autoImplicit false

public section

namespace LeanQbeLegacyTest.KissatM6ProofUtilTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics
open Kraken.Bedrock2.Test

/-! ## 1. Record-Update Abstraction Tests -/

theorem test_upd_1 {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} (h : FullM6HdrInv c F0 ext s) :
    FullM6HdrInv c F0 (ext.set m6WTier1 42#64)
      { s with
        scratch :=
          { s.scratch with
            search_ticks := 100#64 } } ∧
    FullM6HdrInv c F0 ext { s with scratch := { s.scratch with tier1 := 1#64 } } ∧
    FullM6HdrInv c F0 ext { s with scratch := { s.scratch with tier2 := 2#64 } } ∧
    FullM6HdrInv c F0 ext
      { s with
        scratch :=
          { s.scratch with
            ema_fast_biased := 3#64, ema_fast_exp := 4#64
            ema_slow_biased := 5#64, ema_slow_exp := 6#64 } } ∧
    FullM6HdrInv c F0 ext { s with scratch := { s.scratch with rng_state := 7#64 } } ∧
    FullM6HdrInv c F0 ext
      { s with scratch := { s.scratch with delayed := s.scratch.delayed.set 0 9#32 } } ∧
    FullM6HdrInv c F0 ext
      { s with scratch := { s.scratch with scratch_buf := s.scratch.scratch_buf.set 0 11#32 } } ∧
    FullM6HdrInv c F0 ext
      { s with scratch := { s.scratch with work_stk1 := s.scratch.work_stk1.set 0 12#32 } } ∧
    FullM6HdrInv c F0 ext
      { s with scratch := { s.scratch with work_stk2 := s.scratch.work_stk2.set 0 13#32 } } :=
  ⟨fullM6HdrInv_set_ext (fullM6HdrInv_upd_search_ticks h 100#64) m6WTier1 42#64,
   fullM6HdrInv_upd_tier1 h 1#64,
   fullM6HdrInv_upd_tier2 h 2#64,
   fullM6HdrInv_upd_ema h 3#64 4#64 5#64 6#64,
   fullM6HdrInv_upd_rng_state h 7#64,
   fullM6HdrInv_upd_delayed_set h 0 9#32,
   fullM6HdrInv_upd_scratch_buf_set h 0 11#32,
   fullM6HdrInv_upd_work_stk1_set h 0 12#32,
   fullM6HdrInv_upd_work_stk2_set h 0 13#32⟩

theorem test_chain {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} (h : FullM6HdrInv c F0 ext s) :
    let s1 : FullState := { s with scratch := { s.scratch with search_ticks := 10#64 } }
    let s2 : FullState := { s1 with scratch := { s1.scratch with tier1 := 20#64, tier2 := 30#64 } }
    let s3 : FullState := { s2 with scratch := { s2.scratch with rng_state := 99#64 } }
    FullM6HdrInv c F0 ext s3 ∧ FullProbeScratchPres s s3 ∧ s3.core = s.core := by
  intro s1 s2 s3
  have st1 := fullState_upd_search_ticks_step h.sparse.lengths 10#64
  have st2 := fullState_upd_tiers_step st1.1 20#64 30#64
  have st3 := fullState_upd_rng_state_step st2.1 99#64
  have hchain := probeStep_trans (probeStep_trans st1 st2) st3
  exact ⟨fullM6HdrInv_of_probeStep h hchain, hchain.2.2.1, hchain.2.1⟩

theorem test_m6Hdr_ext_w2b_pres {ext : List (BitVec 64)} :
    M6ExtW2bPres ext ((ext.set m6WTier1 1#64).set (m6WDelayCnt + 2) 5#64) :=
  M6ExtW2bPres.trans (m6ExtW2bPres_set_tier1 (k := 0) 1#64)
    (m6ExtW2bPres_set_delayCnt (k := 2) 5#64)

/-! ## 2. `M6Hdr <-> FullHdr` Bridge Combinator Tests -/

theorem test_m6_bridge_safetyVoid {Γ : Env} {ret : List Ty}
    {k : Tup Val [] → Expr Val Cont ret} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post ret} {X : XPost}
    (hΓ : ∀ Q' X', fullSafetyVoidSpec (c.hdr, ()) m Q' X' →
      Γ "full_switch_mode" [i64] [] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ s' m', FullM6HdrInv c F0 ext s' → FullProbeScratchPres s s' →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_switch_mode" (as := [i64]) (bs := []) (Arg.var c.hdr, ()) k) m :=
  m6Hdr_call_safetyVoid_inv rfl hΓ hinv hm hk

theorem test_probe {Γ : Env} {ret : List Ty}
    {k : Tup Val [i64] → Expr Val Cont ret} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post ret} {X : XPost}
    (hΓ : ∀ Q' X', fullProbeSpec (c.hdr, ()) m Q' X' →
      Γ "full_probe" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r s' m', s'.LengthsOk c → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c F0 ext s' ∧ s'.core.cur_level = 0) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_probe" (as := [i64]) (bs := [i64]) (Arg.var c.hdr, ()) k) m :=
  m6Hdr_call_fullProbe_inv rfl hΓ hinv hl0 hm hk

theorem test_m6_bridge_search {Γ : Env} {ret : List Ty}
    {k : Tup Val [i64] → Expr Val Cont ret} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post ret} {X : XPost}
    (hΓ : ∀ Q' X', fullSearchSpec (c.hdr, ()) m Q' X' →
      Γ "full_search" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInv c F0 ext s) (hl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r s' m', s'.LengthsOk c → (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_search" (as := [i64]) (bs := [i64]) (Arg.var c.hdr, ()) k) m :=
  m6Hdr_call_fullSearch_inv rfl hΓ hinv hl0 hm hk

theorem test_dense {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hΓ : ∀ Q' X', fullPropagateSpec (c.hdr, ()) m Q' X' →
      Γ "full_propagate" [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r s' m', FullM6HdrInvW c F0 F_cur ext s' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) → (FullM6HdrMem c ext s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (.call "full_propagate" (as := [i64]) (bs := [i64])
      (Arg.var c.hdr, ()) (fun r => .ret (Arg.var r.1, ()))) m :=
  m6Hdr_call_fullPropagate_invW rfl hΓ hinv hm
    (fun r s' m' hinv' _ _ _ hr _ _ _ _ hm' => by
      rw [wp_ret]
      exact hk r s' m' hinv' hr hm')

/-! ## 3. Kernel `BitVec` Arithmetic & `c0_hfast` Frame-Lift Tests -/

theorem test_bv {a d cap x sz : BitVec 64} {lit : BitVec 32} {mv alen : Nat}
    {p k clen : BitVec 64}
    (ha : a.toNat ≤ cap.toNat) (hd : d.toNat ≤ cap.toNat) (hsz : 0 < sz.toNat)
    (hl : lit.toNat < 2 * mv) (hp : p.toNat + 3 ≤ alen) (hfit : alen < 2 ^ 64)
    (hle : clen ≤ BitVec.ofNat 64 alen - (p + 3#64)) (hk : k.toNat < clen.toNat) :
    (if cap - d < a then cap else a + d).toNat = min (a.toNat + d.toNat) cap.toNat ∧
    (x &&& (sz - 1#64)).toNat < sz.toNat ∧
    (lit >>> 1#32).toNat < mv ∧ (lit ^^^ 1#32).toNat < 2 * mv ∧
    (lit ^^^ 1#32) >>> 1#32 = lit >>> 1#32 ∧
    (p + 3#64 + k).toNat = p.toNat + 3 + k.toNat ∧ (p + 3#64 + k).toNat < alen :=
  let hcl := bv64_arena_clen_le hp hfit hle
  let hk' : k.toNat < alen - (p.toNat + 3) := Nat.lt_of_lt_of_le hk hcl
  let ha3 := bv64_arena_p3_add_k_toNat hp hk' hfit
  ⟨bv64_sat_add_eq ha hd, bv64_and_sub1_lt hsz, bv32_lit_var_lt hl, bv32_lit_neg_lt hl,
   bv32_xor1_shr1 lit, ha3.1, ha3.2⟩

theorem test_hfast {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    let off1 : BitVec 64 := BitVec.ofNat 64 (8 * m6WTier1)
    let off2 : BitVec 64 := BitVec.ofNat 64 (8 * m6WTier2)
    let prog : Expr Val Cont [i64] :=
      .let_ (op2 (.sub i64) (Arg.var c.hdr) (Arg.imm 2304#64)) fun (base, ()) =>
      .let_ (op2 (.add i64) (Arg.var base) (Arg.imm off1)) fun (a1, ()) =>
      .load i64 (Arg.var a1) fun v =>
      .let_ (op2 (.add i64) (Arg.var base) (Arg.imm off2)) fun (a2, ()) =>
      .store (Arg.var v) (Arg.var a2) (.ret (Arg.var v, ()))
    wp Γ (fun (r : Tup Val [i64]) m' =>
      ∃ ext', FullM6HdrInv c F0 ext' s ∧ M6ExtW2bPres ext ext' ∧
        r.1 = ext[m6WTier1]'(by have := hinv.extOk.len; dsimp [m6WTier1]; omega) ∧
        (FullM6HdrMem c ext' s ⋆ R) m') (fun _ _ _ _ => False) prog m := by
  intro off1 off2 prog
  have hlt1 : m6WTier1 < ext.length := by have := hinv.extOk.len; dsimp [m6WTier1]; omega
  have hlt2 : m6WTier2 < ext.length := by have := hinv.extOk.len; dsimp [m6WTier2]; omega
  have hb1 : m6WTier1 < 2 ^ 61 := by dsimp [m6WTier1]; omega
  have hb2 : m6WTier2 < 2 ^ 61 := by dsimp [m6WTier2]; omega
  c0_hfast
  refine ⟨ext.set m6WTier2 (ext[m6WTier1]'hlt1),
    fullM6HdrInv_set_ext hinv m6WTier2 (ext[m6WTier1]'hlt1),
    m6ExtW2bPres_set_tier2 (k := 0) (ext[m6WTier1]'hlt1), rfl, hm⟩

/-! ## 4. `ModuleOk` / `Env.noExit` & Segment Transport Tests -/

private def testFn1 : Fn := ⟨"m6u_f1", [i64], [i64], fun V _C (x, ()) =>
  Expr.ret (Arg.var (x : V i64), ())⟩

private def testFn2 : Fn := ⟨"m6u_f2", [i64], [i64], fun V _C (x, ()) =>
  Expr.call "m6u_f1" (as := [i64]) (bs := [i64]) (Arg.var (x : V i64), ()) fun r =>
    Expr.ret (Arg.var r.1, ())⟩

private def testFn3 : Fn := ⟨"m6u_f3", [i64], [i64], fun V _C (x, ()) =>
  Expr.call "m6u_f2" (as := [i64]) (bs := [i64]) (Arg.var (x : V i64), ()) fun r =>
    Expr.ret (Arg.var r.1, ())⟩

private def testIdSpec : Spec [i64] [i64] := fun (x, ()) m Q _ => Q (x, ()) m

private def testMod1 : Module := ⟨[testFn1, testFn2], [], []⟩

private def testMod2 : Module := ⟨[testFn1, testFn2, testFn3], [], []⟩

private def testTbl1 : List SpecEntry :=
  [ ⟨"m6u_f1", [i64], [i64], testIdSpec, true⟩
  , ⟨"m6u_f2", [i64], [i64], testIdSpec, true⟩ ]

private def testTbl2 : List SpecEntry :=
  testTbl1 ++ [⟨"m6u_f3", [i64], [i64], testIdSpec, true⟩]

private theorem testMod1_ok : ModuleOk (Env.ofTable testTbl1) testMod1 := by
  have hchk : testMod1.checkAcyclic = true := rfl
  have hnd : (testTbl1.map SpecEntry.name).Nodup := tbl_nodup_of_sigs hchk rfl
  have hwf : AllFns Fn.Wf testMod1.fns := by
    refine allFns_cons ?_ (allFns_cons ?_ (allFns_nil _))
    · intro _ _ _ _ _ _
      exact Wf.ret (.cons (ArgRel.var List.mem_cons_self) .nil)
    · intro _ _ _ _ _ _
      exact Wf.call "m6u_f1" (.cons (ArgRel.var List.mem_cons_self) .nil)
        (fun _ _ => Wf.ret (.cons (ArgRel.var List.mem_cons_self) .nil))
  have himpl : TableImpl (Env.ofTable testTbl1) testMod1.fns testTbl1 := by
    refine tableImpl_cons ?_ (tableImpl_cons ?_ (tableImpl_nil _ _))
    · refine SpecEntry.Impl.of (fun (x, ()) m Q _ h => by
        simp only [Func.wp, testFn1]
        exact h)
    · refine SpecEntry.Impl.of (fun (x, ()) m Q _ h => ?_)
      simp only [Func.wp, testFn2]
      refine wp_call_of_spec _ _ (env_ofTable_row_at (idx := 0) rfl hnd ?_)
      exact h
  exact Env.ofTable_moduleOk hchk hwf himpl

theorem test_modok :
    ∃ (tbl : List SpecEntry) (M : Module),
      ModuleOk (Env.ofTable tbl) M ∧
      (∀ f as bs xs m Q X X',
        Env.ofTable tbl f as bs xs m Q X → Env.ofTable tbl f as bs xs m Q X') := by
  have hchk2 : testMod2.checkAcyclic = true := rfl
  have hnd1 : (testTbl1.map SpecEntry.name).Nodup := tbl_nodup_of_sigs (M := testMod1) rfl rfl
  have hnd2 : (testTbl2.map SpecEntry.name).Nodup := tbl_nodup_of_sigs hchk2 rfl
  have hpre := tableImpl_prefix_of_moduleOk 2 testMod1_ok rfl rfl
    (fun e he => by
      simp only [testTbl1, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact ⟨testFn1, List.mem_cons_self, rfl, rfl, rfl⟩
      · exact ⟨testFn2, .tail _ List.mem_cons_self, rfl, rfl, rfl⟩)
    hnd1 hnd2 rfl rfl (fun i hi => by
      have hi2 : i < 2 := hi
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl)
  have hwf3 : AllFns Fn.Wf [testFn3] := by
    refine allFns_cons (fun _ _ _ _ _ _ => Wf.call "m6u_f2"
      (.cons (ArgRel.var List.mem_cons_self) .nil)
      (fun _ _ => Wf.ret (.cons (ArgRel.var List.mem_cons_self) .nil))) (allFns_nil _)
  have himpl3 : TableImpl (Env.ofTable testTbl2) [testFn3]
      [⟨"m6u_f3", [i64], [i64], testIdSpec, true⟩] := by
    refine tableImpl_cons (SpecEntry.Impl.of (fun (x, ()) m Q _ h => ?_)) (tableImpl_nil _ _)
    simp only [Func.wp, testFn3]
    refine wp_call_of_spec _ _ (env_ofTable_row_at (idx := 1) rfl hnd2 ?_)
    exact h
  have hmod2 : ModuleOk (Env.ofTable testTbl2) testMod2 :=
    moduleOk_of_two_segments hchk2 rfl rfl hpre.1 hwf3 hpre.2 himpl3
  exact ⟨testTbl2, testMod2, hmod2, env_ofTable_noExit_all (tbl_all_noExit_append rfl rfl)⟩

#print axioms LeanQbeLegacyTest.KissatM6ProofUtilTest.test_upd_1
#print axioms LeanQbeLegacyTest.KissatM6ProofUtilTest.test_chain
#print axioms LeanQbeLegacyTest.KissatM6ProofUtilTest.test_probe
#print axioms LeanQbeLegacyTest.KissatM6ProofUtilTest.test_dense
#print axioms LeanQbeLegacyTest.KissatM6ProofUtilTest.test_bv
#print axioms LeanQbeLegacyTest.KissatM6ProofUtilTest.test_hfast
#print axioms LeanQbeLegacyTest.KissatM6ProofUtilTest.test_modok

end LeanQbeLegacyTest.KissatM6ProofUtilTest
