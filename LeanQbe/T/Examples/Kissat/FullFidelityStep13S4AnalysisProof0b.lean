/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4Analysis
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4EVSIDSReorderProof1
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4RestoreProof
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 S4-B Proofs Part 0b (`full_analyze_reasons_fid`)

UNSAT-only, callee-parametric `Func.wp` proof (`public section`, `0` `@[expose]` on theorems,
`0` `import all`, `XPost`-polymorphic) for Step-13 `full_analyze_reasons_fid` (including the
Option-1B `mrk` clear loop preserving `FullMrkZero` while leaving `min_clr_len` & `work_stk1`
ready for post-learn `full_bump_analyzed_mode_fid(h, false)`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open Kraken.Bedrock2.Test

/-! ## 1. Step-13 `s13AnalyzeReasonsSpecP` Specification -/

/-- Step-13 `full_analyze_reasons_fid` specification over `FullM6HdrMem`.
Requires `FullMrkZero c s` and restores `FullMrkZero c s'` via the Option-1B clear loop, while
populating `min_clr_len ≤ cur_vars` and valid variable indices `< cur_vars` in
`work_stk1[0..min_clr_len)` when `probing == 0`. -/
def s13AnalyzeReasonsSpecP (Pext : List (BitVec 64) → List (BitVec 64) → Prop) : Spec [i64] [] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ mrk' mcl' sc' ext' m',
        let s' : FullState :=
          { core := { s.core with mrk := mrk', min_clr_len := mcl' }
            scratch := sc' }
        s'.LengthsOk c →
        (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
        (s.core.probing = 0#64 → mcl' ≤ s.core.cur_vars ∧
          ∀ k < mcl', (sc'.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) →
        (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
        FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ Pext ext ext') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

theorem s13AnalyzeReasonsSpecP_monoX
    {Pext : List (BitVec 64) → List (BitVec 64) → Prop}
    {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : s13AnalyzeReasonsSpecP Pext xs m Q X) :
    s13AnalyzeReasonsSpecP Pext xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem s13AnalyzeReasonsSpecP_of
    {Pext : List (BitVec 64) → List (BitVec 64) → Prop}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hmrk0 : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ mrk' mcl' sc' ext' m',
      let s' : FullState :=
        { core := { s.core with mrk := mrk', min_clr_len := mcl' }
          scratch := sc' }
      s'.LengthsOk c →
      (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (s.core.probing = 0#64 → mcl' ≤ s.core.cur_vars ∧
        ∀ k < mcl', (sc'.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ Pext ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    s13AnalyzeReasonsSpecP Pext (c.hdr, ()) m Q X :=
  ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hmrk0, hm, hQ⟩

/-! ## 2. Private Helpers -/

section AnalyzeReasonsHelpers

attribute [local bv_c0] Bool.true_eq_false Bool.false_eq_true

private theorem s13ar_bv32_lshr1 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  rw [show x >>> 1#32 = x >>> 1 from rfl]; bv_omega

private theorem s13ar_bv32_setWidth64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  bv_omega

private theorem s13ar_bv32_lshr_nat1 (x : BitVec 32) : (x >>> 1).toNat = x.toNat / 2 := by
  bv_omega

private theorem s13ar_bv32_mod64 (x : BitVec 32) : x.toNat % 2 ^ 64 = x.toNat :=
  Nat.mod_eq_of_lt (lt_trans x.isLt (by decide))

attribute [local bv_c0] s13ar_bv32_lshr1 s13ar_bv32_setWidth64 s13ar_bv32_lshr_nat1

private theorem s13ar_bv8_zext32_eq0_iff {x : BitVec 8} :
    BitVec.setWidth 32 x = 0#32 ↔ x = 0#8 := by
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32),
      show (0#32 : BitVec 32).toNat = 0 from rfl] at ht
    exact BitVec.eq_of_toNat_eq ht
  · rintro rfl; rfl

private theorem s13ar_k_lt_of_mod {k n : Nat} (hk : k < 2 ^ 64) (hn : n < 2 ^ 64)
    (h : k % 2 ^ 64 < n % 2 ^ 64) : k < n := by
  rwa [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hn] at h

private theorem s13ar_ofNat64_add1 {k : Nat} (_hk : k + 1 < 2 ^ 64) :
    BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (1 : BitVec 64).toNat = 1 from rfl]; omega

private theorem s13ar_getElem_congr {α : Type} {l : List α} {i j : Nat}
    {hi : i < l.length} {hj : j < l.length} (h : i = j) : l[i]'hi = l[j]'hj := by
  subst h; rfl

private abbrev mkArState (s : FullState) (sc : FullScratch) (mrk : List (BitVec 8))
    (mcl : Nat) (ws1 : List (BitVec 32)) (tk : BitVec 64) : FullState :=
  { s with
    core := { s.core with mrk := mrk, min_clr_len := mcl }
    scratch := { sc with work_stk1 := ws1, search_ticks := tk } }

private abbrev ArSt := List (BitVec 8) × Nat × List (BitVec 32) × BitVec 64

private theorem mkArState_lengths {c : FullCfg} {s : FullState} {sc : FullScratch}
    (hlen : ({ s with scratch := sc } : FullState).LengthsOk c)
    {mrk : List (BitVec 8)} {mcl : Nat} {ws1 : List (BitVec 32)} {tk : BitVec 64}
    (hmrk : mrk.length = c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hmcl : mcl ≤ c.max_vars) :
    (mkArState s sc mrk mcl ws1 tk).LengthsOk c :=
  ⟨{ hlen.core_ok with mrk_len := hmrk, min_clr_len_le := hmcl },
   { hlen.scratch_ok with work_stk1_len := hws1 }⟩

private theorem s13ar_push_cov {c : FullCfg} {s : FullState} {sc : FullScratch}
    {mrk : List (BitVec 8)} {mcl : Nat} {ws1 : List (BitVec 32)} {tk : BitVec 64}
    {ov : BitVec 32} (hmrk : mrk.length = c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hcov : FullAnaMarksCov c (mkArState s sc mrk mcl ws1 tk))
    (hov_cv : ov.toNat < s.core.cur_vars)
    (hov_z : mrk[ov.toNat]?.getD 0#8 = 0#8) (hmcl_lt : mcl < s.core.cur_vars) :
    FullAnaMarksCov c (mkArState s sc (mrk.set ov.toNat 1#8) (mcl + 1) (ws1.set mcl ov) tk) :=
  s13b_push_marksCov_gen (s := { s with scratch := { sc with search_ticks := tk } })
    hmrk hws1 hcv hcov hov_cv hmcl_lt hov_z

private theorem s13ar_pop_cov {c : FullCfg} {s : FullState} {sc : FullScratch}
    {mrk : List (BitVec 8)} {mcl : Nat} {ws1 : List (BitVec 32)} {tk : BitVec 64}
    (hmrk : mrk.length = c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hcov : FullAnaMarksCov c (mkArState s sc mrk mcl ws1 tk)) (hmcl_pos : 0 < mcl) :
    let rv := (ws1[mcl - 1]'(by have := hcov.1; dsimp only [mkArState] at this; omega)).toNat
    FullAnaMarksCov c (mkArState s sc (mrk.set rv 0#8) (mcl - 1) ws1 tk) := by
  unfold FullAnaMarksCov at hcov ⊢
  have hmcl_cv : mcl ≤ s.core.cur_vars := hcov.1
  have hmcl_ws : mcl - 1 < ws1.length := by omega
  let rv := (ws1[mcl - 1]'hmcl_ws).toNat
  have hrv_cv : rv < s.core.cur_vars := by
    have h1 := (hcov.2.2.1 (mcl - 1) (by dsimp only [mkArState]; omega)).1
    dsimp only [mkArState] at h1
    rwa [List.getElem?_eq_getElem hmcl_ws, Option.getD_some] at h1
  have h1 := hcov.2.1; have h2 := hcov.2.2.1; have h3 := hcov.2.2.2
  dsimp only [mkArState] at h1 h2 h3 ⊢
  have hnd_prev : ((ws1.take (mcl - 1)).map BitVec.toNat).Nodup := by
    have hsub : ws1.take (mcl - 1) = (ws1.take mcl).take (mcl - 1) := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [hsub, List.map_take]; exact List.Pairwise.take h1
  have hrv_ne : ∀ k < mcl - 1, (ws1[k]?.getD 0#32).toNat ≠ rv := fun k hk heq => by
    have hlt1 : k < ((ws1.take mcl).map BitVec.toNat).length := by
      rw [List.length_map, List.length_take]; omega
    have hlt2 : mcl - 1 < ((ws1.take mcl).map BitVec.toNat).length := by
      rw [List.length_map, List.length_take]; omega
    have hne := List.pairwise_iff_getElem.mp h1 k (mcl - 1) hlt1 hlt2 (by omega)
    apply hne
    simp only [List.getElem_map, List.getElem_take]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq; exact heq
  refine ⟨by omega, hnd_prev, fun k hk => ?_, fun v hv hnz => ?_⟩
  · obtain ⟨hkl, hkn⟩ := h2 k (by omega)
    exact ⟨hkl, by rw [List.getElem?_set_ne (Ne.symm (hrv_ne k hk))]; exact hkn⟩
  · by_cases hvr : v = rv
    · subst hvr; rw [List.getElem?_set_self (by omega), Option.getD_some] at hnz
      exact absurd rfl hnz
    · rw [List.getElem?_set_ne (Ne.symm hvr)] at hnz
      obtain ⟨k, hk, heq⟩ := h3 v hv hnz
      refine ⟨k, ?_, heq⟩
      exact Classical.byContradiction fun hge => by
        have hke : k = mcl - 1 := by omega
        subst hke; rw [List.getElem?_eq_getElem hmcl_ws, Option.getD_some] at heq
        exact hvr heq.symm

private abbrev arAllowInv (c : FullCfg) (s : FullState) (sc0 : FullScratch)
    (R_hdr : Mem 64 → Prop) (st : ArSt) (m : Mem 64) : Prop :=
  st.1.length = c.max_vars ∧ st.2.2.1.length = 2 * c.max_vars ∧
  FullAnaMarksCov c (mkArState s sc0 st.1 st.2.1 st.2.2.1 st.2.2.2) ∧
  (FullMem c (mkArState s sc0 st.1 st.2.1 st.2.2.1 st.2.2.2) ⋆ R_hdr) m

private abbrev arPostInv (c : FullCfg) (s : FullState) (ext : List (BitVec 64))
    (R : Mem 64 → Prop) (m : Mem 64) : Prop :=
  ∃ (ext' : List (BitVec 64)) (sc' : FullScratch) (mrk' : List (BitVec 8)) (mcl' : Nat),
    let s' : FullState :=
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
    M6HdrExtOk ext' ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') ∧
    s'.LengthsOk c ∧ FullAnaMarksCov c s' ∧ FullExtScratchPres s s' ∧
    sc'.work_stk2 = s.scratch.work_stk2 ∧
    (FullMem c s' ⋆ (array64 (c.hdr - 2304) ext' ⋆ R)) m

private theorem arPostInv_of_w2a {c : FullCfg} {s : FullState} {sc0 : FullScratch}
    {ext ext1 ext2 : List (BitVec 64)} {R : Mem 64 → Prop}
    {mrk_a : List (BitVec 8)} {mcl_a : Nat} {ws_a : List (BitVec 32)} {tk_a : BitVec 64}
    {s' : FullState} {m' : Mem 64}
    (hpre0 : FullExtScratchPres s { s with scratch := sc0 })
    (hws20 : sc0.work_stk2 = s.scratch.work_stk2)
    (hinit_pres : M6HdrExtInitOk ext → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext ext1)
    (hcov_a : FullAnaMarksCov c (mkArState s sc0 mrk_a mcl_a ws_a tk_a))
    (hcore' : s'.core = (mkArState s sc0 mrk_a mcl_a ws_a tk_a).core)
    (hlen' : s'.LengthsOk c)
    (hsc' : M6HdrScratchPres (mkArState s sc0 mrk_a mcl_a ws_a tk_a) s')
    (hext2 : M6HdrExtOk ext2)
    (hw2 : M6HdrExtInitOk ext1 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext1 ext2)
    (hm' : (FullMem c s' ⋆ (array64 (c.hdr - 2304) ext2 ⋆ R)) m') :
    arPostInv c s ext R m' := by
  obtain ⟨core', sc'⟩ := s'; dsimp only [mkArState] at hcore' hlen' hsc' hm' ⊢
  subst hcore'
  refine ⟨ext2, sc', mrk_a, mcl_a, hext2,
    fun hi => ⟨(hw2 (hinit_pres hi).1).1, (hinit_pres hi).2.trans (hw2 (hinit_pres hi).1).2⟩,
    hlen', ?_, ⟨hsc'.extPres.1.trans hpre0.1, hsc'.extPres.2.trans hpre0.2⟩,
    hsc'.ws2.trans hws20, hm'⟩
  obtain ⟨h1, h2, h3, h4⟩ := hcov_a
  have hws_eq : sc'.work_stk1 = ws_a := hsc'.ws1
  exact ⟨h1, by rw [hws_eq]; exact h2, by rw [hws_eq]; exact h3,
    fun v hv hnz => let ⟨k, hk, heq⟩ := h4 v hv hnz; ⟨k, hk, by rw [hws_eq]; exact heq⟩⟩

end AnalyzeReasonsHelpers

local macro "m6h_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 2b. Factored Phase Helpers for `full_analyze_reasons_fid` -/

private def s13ArPushOvExpr {V : Ty → Type} {C : List Ty → Type}
    (h pMrk pAna pLvl cv : V i64) (ov : V i32) (Jout : C []) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .let_ (Op.mk (.zext 32 64) (.var ov, ())) fun p1 =>
  .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p1.fst, .var cv, ())) fun p2 =>
  .jnz (.var p2.fst)
    (.let_ (Op.mk (.zext 32 64) (.var ov, ())) fun p3 =>
     .let_ (op64 (.mul i64) (.var p3.fst) (.imm 4)) fun p4 =>
     .let_ (op64 (.add i64) (.var pLvl) (.var p4.fst)) fun p5 =>
     .load i32 (.var p5.fst) fun ld1 =>
     .let_ (Op.mk (.cmp .ugt i32 .bool rfl) (.var ld1, .imm 0, ())) fun p6 =>
     .jnz (.var p6.fst)
       (.let_ (Op.mk (.zext 32 64) (.var ov, ())) fun p7 =>
        .let_ (op64 (.add i64) (.var pMrk) (.var p7.fst)) fun p8 =>
        .load i8 (.var p8.fst) fun ld2 =>
        .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun p9 =>
        .let_ (Op.mk (.zext 8 32) (.var ld2, ())) fun p10 =>
        .let_ (Op.mk (.zext 8 32) (.var p9.fst, ())) fun p11 =>
        .let_ (Op.mk (.cmp .eq i32 .bool rfl) (.var p10.fst, .var p11.fst, ())) fun p12 =>
        .jnz (.var p12.fst)
          (.let_ (op64 (.add i64) (.var h) (.imm 272)) fun p13 =>
           .load i64 (.var p13.fst) fun ld3 =>
           .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var ld3, .var cv, ())) fun p14 =>
           .jnz (.var p14.fst)
             (.let_ (Op.mk (.zext 32 64) (.var ov, ())) fun p15 =>
              .let_ (op64 (.add i64) (.var pMrk) (.var p15.fst)) fun p16 =>
              .let_ (Op.mk (.trunc 32 8) (.imm 1, ())) fun p17 =>
              .store (.var p17.fst) (.var p16.fst)
                (.let_ (op64 (.add i64) (.var h) (.imm 272)) fun p18 =>
                 .load i64 (.var p18.fst) fun ld4 =>
                 .let_ (op64 (.mul i64) (.var ld4) (.imm 4)) fun p19 =>
                 .let_ (op64 (.add i64) (.var pAna) (.var p19.fst)) fun p20 =>
                 .store (.var ov) (.var p20.fst)
                   (.let_ (op64 (.add i64) (.var h) (.imm 272)) fun p21 =>
                    .load i64 (.var p21.fst) fun ld5 =>
                    .let_ (op64 (.add i64) (.var ld5) (.imm 1)) fun p22 =>
                    .let_ (op64 (.add i64) (.var h) (.imm 272)) fun p23 =>
                    .store (.var p22.fst) (.var p23.fst) (.jump Jout ()))))
             (.jump Jout ()))
          (.jump Jout ()))
       (.jump Jout ()))
    (.jump Jout ())

private theorem s13_ar_push_ov_wp {Γ : Env} {Q : Post []} {X : XPost}
    {c : FullCfg} {s : FullState} {sc0 : FullScratch} {R_hdr : Mem 64 → Prop}
    {st : ArSt} {ov : BitVec 32} {m0 : Mem 64} {Jout : Cont []}
    (hlen : s.LengthsOk c) (hinv : arAllowInv c s sc0 R_hdr st m0)
    (hJ : ∀ st' m', arAllowInv c s sc0 R_hdr st' m' → Jout () m') :
    wp Γ Q X (s13ArPushOvExpr c.hdr c.pMark c.pWorkStk1 c.pLevel
      (BitVec.ofNat 64 s.core.cur_vars) ov Jout) m0 := by
  rcases st with ⟨mrk_i, mcl_i, ws_i, tk_i⟩
  rcases hinv with ⟨hmrk_i, hws_i, hcov_i, hm0⟩
  dsimp only at hmrk_i hws_i hcov_i hm0
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hco := hlen.core_ok; have hcv_le := hco.cur_vars_le
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
  have hmcl_i_cv : mcl_i ≤ s.core.cur_vars := hcov_i.1
  let si := mkArState s sc0 mrk_i mcl_i ws_i tk_i
  dsimp only [s13ArPushOvExpr]
  c0_hsteps_nogrp
  · have hov_cv : ov.toNat < s.core.cur_vars := by
      have h1 : ov.toNat < s.core.cur_vars % 2 ^ 64 := by
        simpa only [s13ar_bv32_setWidth64, BitVec.toNat_ofNat] using (by assumption : _)
      rwa [Nat.mod_eq_of_lt hcv_lt64] at h1
    have hov_lvl : (ov.setWidth 64).toNat < si.core.lvl.length := by
      rw [s13ar_bv32_setWidth64, show si.core.lvl = s.core.lvl from rfl, hco.lvl_len]; omega
    have hov_mrk : (ov.setWidth 64).toNat < mrk_i.length := by
      rw [s13ar_bv32_setWidth64, hmrk_i]; omega
    c0_hsteps_nogrp
    · have hov_z : mrk_i[ov.toNat]?.getD 0#8 = 0#8 := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact s13ar_bv8_zext32_eq0_iff.mp (by
          simpa only [s13ar_bv32_setWidth64] using (by assumption : _))
      have hmcl_lt : mcl_i < s.core.cur_vars := s13ar_k_lt_of_mod
        (by have := hcov_i.1; dsimp only [mkArState] at this; omega) hcv_lt64
        (by simpa [si, mkArState, BitVec.toNat_ofNat] using (by assumption : _))
      have hmcl_ws : (BitVec.ofNat 64 mcl_i).toNat < ws_i.length := by
        rw [bv64_ofNat_toNat (by omega), hws_i]; omega
      c0_hsteps
      have hcov' := s13ar_push_cov hmrk_i hws_i hcv_le hcov_i hov_cv hov_z hmcl_lt
      have hmcl1_bv : (BitVec.ofNat 64 mcl_i + 1).toNat = mcl_i + 1 := by
        rw [s13ar_ofNat64_add1 (by omega), bv64_ofNat_toNat (by omega)]
      exact hJ (mrk_i.set ov.toNat 1#8, mcl_i + 1, ws_i.set mcl_i ov, tk_i) _
        ⟨by rw [List.length_set, hmrk_i], by rw [List.length_set, hws_i], hcov', by
          simpa only [si, mkArState, s13ar_bv32_setWidth64, hmcl1_bv,
            bv64_ofNat_toNat (by omega : mcl_i < 2 ^ 64),
            show BitVec.ofNat 8 1 = 1#8 from rfl] using hm⟩
    all_goals exact hJ (mrk_i, mcl_i, ws_i, tk_i) m0 ⟨hmrk_i, hws_i, hcov_i, hm0⟩
  · exact hJ (mrk_i, mcl_i, ws_i, tk_i) m0 ⟨hmrk_i, hws_i, hcov_i, hm0⟩

private def s13ArClearExpr {V : Ty → Type} {C : List Ty → Type}
    (h pMrk pAna cv : V i64) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[i64]]) (fun Jc => .cons (fun (xs : Tup V [i64]) =>
    let ci := xs.fst
    .let_ (op64 (.add i64) (.var h) (.imm 272)) fun p1 =>
    .load i64 (.var p1.fst) fun mcl =>
    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var ci, .var mcl, ())) fun p2 =>
    .jnz (.var p2.fst)
      (.let_ (op64 (.mul i64) (.var ci) (.imm 4)) fun p3 =>
       .let_ (op64 (.add i64) (.var pAna) (.var p3.fst)) fun p4 =>
       .load i32 (.var p4.fst) fun cvi =>
       .group (sig := [[]]) (fun _ => .cons (fun _ =>
         .let_ (op64 (.add i64) (.var ci) (.imm 1)) fun ci1 =>
         .jump Jc.fst (.var ci1.fst, ())) .nil)
         fun J18 =>
           .let_ (Op.mk (.zext 32 64) (.var cvi, ())) fun p5 =>
           .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p5.fst, .var cv, ())) fun p6 =>
           .jnz (.var p6.fst)
             (.let_ (Op.mk (.zext 32 64) (.var cvi, ())) fun p7 =>
              .let_ (op64 (.add i64) (.var pMrk) (.var p7.fst)) fun p8 =>
              .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun p9 =>
              .store (.var p9.fst) (.var p8.fst) (.jump J18.fst ()))
             (.jump J18.fst ()))
      (.ret ())) .nil)
    fun Jc => .jump Jc.fst (.imm 0, ())

private theorem s13_ar_clear_wp {Γ : Env} {Q : Post []} {X : XPost}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m_post : Mem 64}
    (hpr0 : s.core.probing = 0#64) (hpost : arPostInv c s ext R m_post)
    (hQ : ∀ mrk' mcl' sc' ext' m',
      let s' : FullState :=
        { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
      s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (s.core.probing = 0#64 → mcl' ≤ s.core.cur_vars ∧
        ∀ k < mcl', (sc'.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    wp Γ Q X (s13ArClearExpr c.hdr c.pMark c.pWorkStk1 (BitVec.ofNat 64 s.core.cur_vars))
      m_post := by
  rcases hpost with
    ⟨ext_p, sc_p, mrk_p, mcl_p, hext_p, hinit_p, hlen_p, hcov_p, hpre_p, hws2_p, hm_p⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen_p.core_ok.cur_vars_le
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
  let R_p : Mem 64 → Prop := array64 (c.hdr - 2304) ext_p ⋆ R
  have hmcl_p_cv : mcl_p ≤ s.core.cur_vars := hcov_p.1
  have hmcl_p_lt64 : mcl_p < 2 ^ 64 := by omega
  have hmrk_p_len : mrk_p.length = c.max_vars := hlen_p.core_ok.mrk_len
  have hws1_p_len : sc_p.work_stk1.length = 2 * c.max_vars := hlen_p.scratch_ok.work_stk1_len
  dsimp only [s13ArClearExpr]
  refine wp_while_state1 (t := i64) (α := Nat × List (BitVec 8))
    (proj := fun st => BitVec.ofNat 64 st.1) (μ := fun st => mcl_p - st.1)
    (Inv := fun st mc => st.1 ≤ mcl_p ∧ st.2.length = c.max_vars ∧
      (∀ v < c.max_vars, st.2[v]?.getD 0#8 ≠ 0#8 →
        ∃ k, st.1 ≤ k ∧ k < mcl_p ∧ (sc_p.work_stk1[k]?.getD 0#32).toNat = v) ∧
      (FullMem c { core := { s.core with mrk := st.2, min_clr_len := mcl_p },
                   scratch := sc_p } ⋆ R_p) mc)
    (fun Jc hJc => by
      c0_hsteps
      exact hJc (0, mrk_p) m_post ⟨Nat.zero_le _, hmrk_p_len, fun v hv hnz =>
        let ⟨k, hk, heq⟩ := hcov_p.2.2.2 v hv hnz; ⟨k, Nat.zero_le _, hk, heq⟩, hm_p⟩)
    (fun Jc ⟨ci, mrkC⟩ mc ⟨hci_le, hmrkC, hremC, hmc⟩ ihc => ?_)
  dsimp only at hci_le hmrkC hremC hmc ihc; rw [Blocks.get_here]; dsimp only
  c0_hsteps_nogrp
  · have hci_lt : ci < mcl_p := s13ar_k_lt_of_mod (by omega) hmcl_p_lt64
      (by simpa [BitVec.toNat_ofNat] using (by assumption : _))
    have hci_ws : (BitVec.ofNat 64 ci).toNat < sc_p.work_stk1.length := by
      rw [bv64_ofNat_toNat (by omega), hws1_p_len]; omega
    c0_hsteps_nogrp
    let cvi := sc_p.work_stk1[(BitVec.ofNat 64 ci).toNat]'hci_ws
    have hcvi_eq : cvi.toNat = (sc_p.work_stk1[ci]?.getD 0#32).toNat := by
      dsimp only [cvi]
      rw [s13ar_getElem_congr (j := ci) (hj := by rw [hws1_p_len]; omega)
        (bv64_ofNat_toNat (by omega)),
        List.getElem?_eq_getElem (by rw [hws1_p_len]; omega), Option.getD_some]
    have hcvi_cv : cvi.toNat < s.core.cur_vars := by
      rw [hcvi_eq]; exact (hcov_p.2.2.1 ci hci_lt).1
    have hcvi_mrk : (cvi.setWidth 64).toNat < mrkC.length := by
      rw [s13ar_bv32_setWidth64, hmrkC]; omega
    refine wp_join_group (ts := [])
      (fun _ mc' => ∃ mrk' : List (BitVec 8), mrk'.length = c.max_vars ∧
        (∀ v < c.max_vars, mrk'[v]?.getD 0#8 ≠ 0#8 →
          ∃ k, ci + 1 ≤ k ∧ k < mcl_p ∧ (sc_p.work_stk1[k]?.getD 0#32).toNat = v) ∧
        (FullMem c { core := { s.core with mrk := mrk', min_clr_len := mcl_p },
                     scratch := sc_p } ⋆ R_p) mc')
      (fun _ _ mc' ⟨mrk', hml', hrem', hmc'⟩ => by
        rw [Blocks.get_here]; c0_hsteps; rw [s13ar_ofNat64_add1 (by omega)]
        exact ihc (ci + 1, mrk') mc' (by change mcl_p - (ci + 1) < mcl_p - ci; omega)
          ⟨by change ci + 1 ≤ mcl_p; omega, hml', hrem', hmc'⟩)
      (fun J18 hJ18 => ?_)
    c0_hsteps_nogrp
    · c0_hsteps
      refine hJ18 () _
        ⟨mrkC.set cvi.toNat 0#8, by rw [List.length_set, hmrkC], fun v hv hnz => ?_, ?_⟩
      · by_cases hvc : v = cvi.toNat
        · subst hvc; rw [List.getElem?_set_self (by omega), Option.getD_some] at hnz
          exact absurd rfl hnz
        · rw [List.getElem?_set_ne (Ne.symm hvc)] at hnz
          obtain ⟨k, hge, hlt, heq⟩ := hremC v hv hnz
          refine ⟨k, ?_, hlt, heq⟩
          have hne_ci : k ≠ ci := fun h => by subst h; exact hvc (heq.symm.trans hcvi_eq.symm)
          omega
      · simpa only [cvi, s13ar_bv32_setWidth64, show BitVec.ofNat 8 0 = 0#8 from rfl] using hm
    · exfalso
      have h1 : ¬ cvi.toNat < s.core.cur_vars % 2 ^ 64 := by
        simpa only [cvi, s13ar_bv32_setWidth64, BitVec.toNat_ofNat] using (by assumption : _)
      rw [Nat.mod_eq_of_lt hcv_lt64] at h1; exact h1 hcvi_cv
  · have hci_eq : ci = mcl_p := by
      have h1 : ¬ ci % 2 ^ 64 < mcl_p % 2 ^ 64 := by
        simpa only [BitVec.toNat_ofNat] using (by assumption : _)
      rw [Nat.mod_eq_of_lt (by omega : ci < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : mcl_p < 2 ^ 64)] at h1; omega
    have hmrkC_0 : ∀ v < c.max_vars, mrkC[v]?.getD 0#8 = 0#8 := fun v hv =>
      Classical.byContradiction fun hnz => by
        obtain ⟨k, hge, hlt, _⟩ := hremC v hv hnz; omega
    c0_hsteps
    exact hQ mrkC mcl_p sc_p ext_p mc
      ⟨{ hlen_p.core_ok with mrk_len := hmrkC }, hlen_p.scratch_ok⟩ hmrkC_0
      (fun _ => ⟨hmcl_p_cv, fun k hk => (hcov_p.2.2.1 k hk).1⟩)
      (fun h => absurd hpr0 h) hpre_p hws2_p hext_p hinit_p ((fullM6HdrMem_iff ..).mpr hmc)

private def s13ArRollbackExpr {V : Ty → Type} {C : List Ty → Type}
    (h pMrk pAna cv saved lim : V i64) (Jpost : C []) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[]]) (fun _ => .cons (fun _ => .jump Jpost ()) .nil)
    fun J24 =>
      .let_ (op64 (.add i64) (.var h) (.imm 272)) fun p1 =>
      .load i64 (.var p1.fst) fun mcl =>
      .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var mcl, .var lim, ())) fun p2 =>
      .jnz (.var p2.fst)
        (.group (sig := [[]]) (fun J28 => .cons (fun _ =>
          .let_ (op64 (.add i64) (.var h) (.imm 272)) fun p3 =>
          .load i64 (.var p3.fst) fun mcl2 =>
          .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var mcl2, .var saved, ())) fun p4 =>
          .jnz (.var p4.fst)
            (.let_ (op64 (.add i64) (.var h) (.imm 272)) fun p5 =>
             .load i64 (.var p5.fst) fun mcl3 =>
             .let_ (op64 (.sub i64) (.var mcl3) (.imm 1)) fun m1 =>
             .let_ (op64 (.add i64) (.var h) (.imm 272)) fun p6 =>
             .store (.var m1.fst) (.var p6.fst)
               (.let_ (op64 (.add i64) (.var h) (.imm 272)) fun p7 =>
                .load i64 (.var p7.fst) fun mcl4 =>
                .let_ (op64 (.mul i64) (.var mcl4) (.imm 4)) fun p8 =>
                .let_ (op64 (.add i64) (.var pAna) (.var p8.fst)) fun p9 =>
                .load i32 (.var p9.fst) fun rv =>
                .group (sig := [[]]) (fun _ => .cons (fun _ => .jump J28.fst ()) .nil)
                  fun J32 =>
                    .let_ (Op.mk (.zext 32 64) (.var rv, ())) fun p10 =>
                    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p10.fst, .var cv, ())) fun p11 =>
                    .jnz (.var p11.fst)
                      (.let_ (Op.mk (.zext 32 64) (.var rv, ())) fun p12 =>
                       .let_ (op64 (.add i64) (.var pMrk) (.var p12.fst)) fun p13 =>
                       .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun p14 =>
                       .store (.var p14.fst) (.var p13.fst) (.jump J32.fst ()))
                      (.jump J32.fst ())))
            (.call "m6_hdr_bump_delay" (as := [i64, i64]) (bs := []) (.var h, .imm 0, ())
              fun _ => .jump J24.fst ())) .nil)
          fun J28 => .jump J28.fst ())
        (.call "m6_hdr_reduce_delay" (as := [i64, i64]) (bs := []) (.var h, .imm 0, ())
          fun _ => .jump J24.fst ())

private theorem s13_ar_rollback_wp {Γ : Env} {Q : Post []} {X : XPost}
    (hBumpDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hReduceDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    {c : FullCfg} {ext ext1 : List (BitVec 64)} {s : FullState} {sc0 : FullScratch}
    {R : Mem 64 → Prop} {w2 : Nat} {lim : BitVec 64} {st_a : ArSt} {mr : Mem 64} {Jpost : Cont []}
    (hcfg : FullM6HdrCfgOk c) (hext1 : M6HdrExtOk ext1)
    (hlen0 : ({ s with scratch := sc0 } : FullState).LengthsOk c)
    (hpre0 : FullExtScratchPres s { s with scratch := sc0 })
    (hws20 : sc0.work_stk2 = s.scratch.work_stk2)
    (hinit_pres : M6HdrExtInitOk ext → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext ext1)
    (_hw2_lt64 : w2 < 2 ^ 64)
    (hinv_a : arAllowInv c s sc0 (array64 (c.hdr - 2304) ext1 ⋆ R) st_a mr)
    (hJpost : ∀ m', arPostInv c s ext R m' → Jpost () m') :
    wp Γ Q X (s13ArRollbackExpr c.hdr c.pMark c.pWorkStk1 (BitVec.ofNat 64 s.core.cur_vars)
      (BitVec.ofNat 64 w2) lim Jpost) mr := by
  rcases st_a with ⟨mrk_a, mcl_a, ws_a, tk_a⟩
  rcases hinv_a with ⟨hmrk_a, hws_a, hcov_a, hmr⟩
  dsimp only at hmrk_a hws_a hcov_a hmr
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen0.core_ok.cur_vars_le
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
  let R_hdr : Mem 64 → Prop := array64 (c.hdr - 2304) ext1 ⋆ R
  dsimp only [s13ArRollbackExpr]
  refine wp_join_group (ts := []) (fun _ m' => arPostInv c s ext R m')
    (fun _ _ m' hp => by rw [Blocks.get_here]; exact hJpost m' hp) (fun Jrb hJrb => ?_)
  c0_hsteps_nogrp
  · refine wp_while_state0 (α := ArSt) (μ := fun st => st.2.1)
      (Inv := fun st mr' => arAllowInv c s sc0 R_hdr st mr')
      (fun Jr hJr => by
        c0_hsteps; exact hJr (mrk_a, mcl_a, ws_a, tk_a) mr ⟨hmrk_a, hws_a, hcov_a, hmr⟩)
      (fun Jr ⟨mrk_r, mcl_r, ws_r, tk_r⟩ mr' ⟨hmrk_r, hws_r, hcov_r, hmr'⟩ ihr => ?_)
    dsimp only at hmrk_r hws_r hcov_r hmr' ihr; rw [Blocks.get_here]; dsimp only
    let sr := mkArState s sc0 mrk_r mcl_r ws_r tk_r
    have hmcl_r_cv : mcl_r ≤ s.core.cur_vars := hcov_r.1
    c0_hsteps_nogrp
    · have hmcl_r_pos : 0 < mcl_r := by
        have h1 : w2 % 2 ^ 64 < mcl_r % 2 ^ 64 := by
          simpa [sr, mkArState, BitVec.toNat_ofNat] using (by assumption : _)
        rw [Nat.mod_eq_of_lt (by omega : mcl_r < 2 ^ 64)] at h1; omega
      have hmcl_m1_bv : (BitVec.ofNat 64 mcl_r - 1).toNat = mcl_r - 1 := by
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
          rw [bv64_ofNat_toNat (by omega)]; exact hmcl_r_pos)),
          bv64_ofNat_toNat (by omega)]; rfl
      have hmcl_ws' : (BitVec.ofNat 64 (mcl_r - 1)).toNat < ws_r.length := by
        rw [bv64_ofNat_toNat (by omega), hws_r]; omega
      have hm_m1 : (FullMem c (mkArState s sc0 mrk_r (mcl_r - 1) ws_r tk_r) ⋆ R_hdr) m := by
        simpa only [sr, mkArState, hmcl_m1_bv] using hm
      c0_hsteps_nogrp
      let rv := ws_r[(BitVec.ofNat 64 (mcl_r - 1)).toNat]'hmcl_ws'
      have hrv_eq : rv = ws_r[mcl_r - 1]'(by rw [hws_r]; omega) :=
        s13ar_getElem_congr (bv64_ofNat_toNat (by omega))
      have hrv_cv : rv.toNat < s.core.cur_vars := by
        have h1 := (hcov_r.2.2.1 (mcl_r - 1) (by change mcl_r - 1 < mcl_r; omega)).1
        dsimp only [mkArState] at h1
        rwa [List.getElem?_eq_getElem (by rw [hws_r]; omega), Option.getD_some, ← hrv_eq] at h1
      have hrv_mrk : (rv.setWidth 64).toNat < mrk_r.length := by
        rw [s13ar_bv32_setWidth64, hmrk_r]; omega
      refine wp_join_group (ts := [])
        (fun _ mr'' => ∃ st : ArSt, st.2.1 < mcl_r ∧ arAllowInv c s sc0 R_hdr st mr'')
        (fun _ _ mr'' ⟨st, hm_lt, hinv⟩ => by
          rw [Blocks.get_here]; c0_hsteps; exact ihr st mr'' hm_lt hinv)
        (fun Js2 hJs2 => ?_)
      c0_hsteps_nogrp
      · have hcov_pop := s13ar_pop_cov hmrk_r hws_r hcv_le hcov_r hmcl_r_pos
        c0_hsteps
        exact hJs2 () _ ⟨(mrk_r.set rv.toNat 0#8, mcl_r - 1, ws_r, tk_r),
          by change mcl_r - 1 < mcl_r; omega, by rw [List.length_set, hmrk_r], hws_r,
          by simpa [hrv_eq] using hcov_pop, by
            simpa only [mkArState, rv, hmcl_m1_bv, s13ar_bv32_setWidth64,
              show BitVec.ofNat 8 0 = 0#8 from rfl] using hm⟩
      · exfalso
        have hidx_eq : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + mcl_r) % 2 ^ 64 % 2 ^ 64 =
            mcl_r - 1 := by simp only [show (1 : BitVec 64).toNat = 1 from rfl]; omega
        have hc' : ¬ (ws_r[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + mcl_r) % 2 ^ 64 % 2 ^ 64]'(
            by rw [hidx_eq, hws_r]; omega)).toNat < s.core.cur_vars % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt hcv_lt64,
          s13ar_getElem_congr hidx_eq (hj := by rw [hws_r]; omega)] at hc'
        rw [hrv_eq] at hrv_cv; exact hc' hrv_cv
    · have hlen_r := mkArState_lengths (mcl := mcl_r) (tk := tk_r) hlen0 hmrk_r hws_r (by omega)
      m6h_call hBumpDelay
      refine m6HdrW2aSpec_of rfl hcfg hext1 hlen_r ((fullM6HdrMem_iff ..).mpr hmr')
        fun () ext2 s' m' hcore' hlen' hsc' hext2 hw2 hm' => ?_
      rw [fullM6HdrMem_iff] at hm'; c0_hsteps
      exact hJrb () m'
        (arPostInv_of_w2a hpre0 hws20 hinit_pres hcov_r hcore' hlen' hsc' hext2 hw2 hm')
  · have hlen_a := mkArState_lengths (mcl := mcl_a) (tk := tk_a) hlen0 hmrk_a hws_a
      (by have := hcov_a.1; dsimp only [mkArState] at this; omega)
    m6h_call hReduceDelay
    refine m6HdrW2aSpec_of rfl hcfg hext1 hlen_a ((fullM6HdrMem_iff ..).mpr hmr)
      fun () ext2 s' m' hcore' hlen' hsc' hext2 hw2 hm' => ?_
    rw [fullM6HdrMem_iff] at hm'; c0_hsteps
    exact hJrb () m'
      (arPostInv_of_w2a hpre0 hws20 hinit_pres hcov_a hcore' hlen' hsc' hext2 hw2 hm')

private def s13ArRsnBodyExpr {V : Ty → Type} {C : List Ty → Type}
    (h pMrk pAna pLvl pAr cv lim : V i64) (rsn : V i32) (Jrs : C []) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[]]) (fun _ => .cons (fun _ =>
    .group (sig := [[]]) (fun _ => .cons (fun _ => .jump Jrs ()) .nil)
      fun J34 =>
        .let_ (Op.mk (.cmp .ne i32 .bool rfl) (.var rsn, .imm 4294967295, ())) fun q1 =>
        .jnz (.var q1.fst)
          (.let_ (Op.mk (.zext 32 64) (.var rsn, ())) fun q2 =>
           .let_ (op64 (.add i64) (.var q2.fst) (.imm 3)) fun q3 =>
           .let_ (op64 (.add i64) (.var h) (.imm 48)) fun q4 =>
           .load i64 (.var q4.fst) fun al1 =>
           .let_ (Op.mk (.cmp .ule i64 .bool rfl) (.var q3.fst, .var al1, ())) fun q5 =>
           .jnz (.var q5.fst)
             (.let_ (Op.mk (.zext 32 64) (.var rsn, ())) fun q6 =>
              .let_ (op64 (.add i64) (.var q6.fst) (.imm 2)) fun q7 =>
              .let_ (op64 (.mul i64) (.var q7.fst) (.imm 4)) fun q8 =>
              .let_ (op64 (.add i64) (.var pAr) (.var q8.fst)) fun q9 =>
              .load i32 (.var q9.fst) fun sz =>
              .group (sig := [[]]) (fun _ => .cons (fun _ => .jump J34.fst ()) .nil)
                fun J40 =>
                  .let_ (Op.mk (.cmp .uge i32 .bool rfl) (.var sz, .imm 3, ())) fun q10 =>
                  .jnz (.var q10.fst)
                    (.let_ (Op.mk (.zext 32 64) (.var rsn, ())) fun q11 =>
                     .let_ (op64 (.add i64) (.var q11.fst) (.imm 3)) fun q12 =>
                     .let_ (Op.mk (.zext 32 64) (.var sz, ())) fun q13 =>
                     .let_ (op64 (.add i64) (.var q12.fst) (.var q13.fst)) fun q14 =>
                     .let_ (op64 (.add i64) (.var h) (.imm 48)) fun q15 =>
                     .load i64 (.var q15.fst) fun al2 =>
                     .let_ (Op.mk (.cmp .ule i64 .bool rfl) (.var q14.fst, .var al2, ())) fun q16 =>
                     .jnz (.var q16.fst)
                       (.let_ (op64 (.add i64) (.var h) (.imm 600)) fun t1 =>
                        .load i64 (.var t1.fst) fun tk =>
                        .let_ (op64 (.add i64) (.var tk) (.imm 1)) fun tk1 =>
                        .let_ (op64 (.add i64) (.var h) (.imm 600)) fun t2 =>
                        .store (.var tk1.fst) (.var t2.fst)
                          (.group (sig := [[i32]]) (fun J46 => .cons (fun (j_t : Tup V [i32]) =>
                            let j := j_t.fst
                            .let_ (Op.mk (.cmp .ult i32 .bool rfl) (.var j, .var sz, ())) fun r1 =>
                            .jnz (.var r1.fst)
                              (.let_ (op64 (.add i64) (.var h) (.imm 272)) fun r2 =>
                               .load i64 (.var r2.fst) fun mcl =>
                               .let_ (Op.mk (.cmp .ule i64 .bool rfl) (.var mcl, .var lim, ()))
                                 fun r3 =>
                               .jnz (.var r3.fst)
                                 (.let_ (Op.mk (.zext 32 64) (.var rsn, ())) fun r4 =>
                                  .let_ (op64 (.add i64) (.var r4.fst) (.imm 3)) fun r5 =>
                                  .let_ (Op.mk (.zext 32 64) (.var j, ())) fun r6 =>
                                  .let_ (op64 (.add i64) (.var r5.fst) (.var r6.fst)) fun r7 =>
                                  .let_ (op64 (.mul i64) (.var r7.fst) (.imm 4)) fun r8 =>
                                  .let_ (op64 (.add i64) (.var pAr) (.var r8.fst)) fun r9 =>
                                  .load i32 (.var r9.fst) fun lit =>
                                  .let_ (Op.mk (.lshr i32) (.var lit, .imm 1, ())) fun ov =>
                                  .group (sig := [[]]) (fun _ => .cons (fun _ =>
                                    .let_ (Op.mk (.add i32) (.var j, .imm 1, ())) fun j1 =>
                                    .jump J46.fst (.var j1.fst, ())) .nil)
                                    fun J52 =>
                                      s13ArPushOvExpr h pMrk pAna pLvl cv ov.fst J52.fst)
                                 (.jump J40.fst ()))
                              (.jump J40.fst ())) .nil)
                            fun J46 => .jump J46.fst (.imm 0, ())))
                       (.jump J40.fst ()))
                    (.jump J40.fst ()))
             (.jump J34.fst ()))
          (.jump J34.fst ())) .nil)
    fun J32 =>
      .let_ (Op.mk (.cmp .ne i32 .bool rfl) (.var rsn, .imm 4294967295, ())) fun b1 =>
      .jnz (.var b1.fst)
        (.let_ (Op.mk (.and i32) (.var rsn, .imm 2147483648, ())) fun b2 =>
         .let_ (Op.mk (.cmp .ne i32 .bool rfl) (.var b2.fst, .imm 0, ())) fun b3 =>
         .jnz (.var b3.fst)
           (.let_ (Op.mk (.and i32) (.var rsn, .imm 2147483647, ())) fun b4 =>
            .let_ (Op.mk (.lshr i32) (.var b4.fst, .imm 1, ())) fun ov =>
            .group (sig := [[]]) (fun _ => .cons (fun _ => .jump Jrs ()) .nil)
              fun J38 => s13ArPushOvExpr h pMrk pAna pLvl cv ov.fst J38.fst)
           (.jump J32.fst ()))
        (.jump J32.fst ())

private theorem s13_ar_rsn_body_wp {Γ : Env} {Q : Post []} {X : XPost}
    {c : FullCfg} {s : FullState} {sc0 : FullScratch} {R_hdr : Mem 64 → Prop}
    {lim : BitVec 64} {rsn : BitVec 32} {st_i : ArSt} {mi : Mem 64} {Jrs : Cont []}
    (hlen : s.LengthsOk c) (hinv_i : arAllowInv c s sc0 R_hdr st_i mi)
    (hJrs : ∀ st' m', arAllowInv c s sc0 R_hdr st' m' → Jrs () m') :
    wp Γ Q X (s13ArRsnBodyExpr c.hdr c.pMark c.pWorkStk1 c.pLevel c.pArena
      (BitVec.ofNat 64 s.core.cur_vars) lim rsn Jrs) mi := by
  rcases st_i with ⟨mrk_i, mcl_i, ws_i, tk_i⟩
  rcases hinv_i with ⟨hmrk_i, hws_i, hcov_i, hmi⟩
  dsimp only at hmrk_i hws_i hcov_i hmi
  have hco := hlen.core_ok
  have hal64 : s.core.arena_len < 2 ^ 64 := by
    have := hco.arena_len_le; have := c.harena; unfold dimacsBound at this; omega
  let si := mkArState s sc0 mrk_i mcl_i ws_i tk_i
  dsimp only [s13ArRsnBodyExpr]
  refine wp_join_group (ts := []) (fun _ m' => m' = mi) (fun _ _ m' hm' => ?_)
    (fun J32 hJ32 => by
      c0_hsteps_nogrp
      · refine wp_join_group (ts := []) (fun _ m'' => ∃ st', arAllowInv c s sc0 R_hdr st' m'')
          (fun _ _ m'' ⟨st', hst'⟩ => by rw [Blocks.get_here]; exact hJrs st' m'' hst')
          (fun J38 hJ38 => s13_ar_push_ov_wp (st := (mrk_i, mcl_i, ws_i, tk_i)) hlen
            ⟨hmrk_i, hws_i, hcov_i, hmi⟩ fun st' m'' hst' => hJ38 () m'' ⟨st', hst'⟩)
      all_goals exact hJ32 () mi rfl)
  subst m'; rw [Blocks.get_here]
  refine wp_join_group (ts := []) (fun _ m' => ∃ st', arAllowInv c s sc0 R_hdr st' m')
    (fun _ _ m' ⟨st', hst'⟩ => by rw [Blocks.get_here]; exact hJrs st' m' hst')
    (fun J34 hJ34 => ?_)
  c0_hsteps_nogrp
  · have hrsn_3 : (rsn.setWidth 64 + 3).toNat ≤ s.core.arena_len := by
      have h1 : (rsn.toNat + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 ≤ s.core.arena_len % 2 ^ 64 :=
        by assumption
      rw [Nat.mod_eq_of_lt hal64] at h1; bv_omega
    have hsz_lt : (rsn.setWidth 64 + 2).toNat < si.core.arena.length := by
      have h2 : (rsn.setWidth 64 + 2).toNat = rsn.toNat + 2 := by bv_omega
      have h3 : (rsn.setWidth 64 + 3).toNat = rsn.toNat + 3 := by bv_omega
      rw [show si.core.arena = s.core.arena from rfl, hco.arena_len_arr]
      have := hco.arena_len_le; omega
    c0_hsteps_nogrp
    let sz_bv := si.core.arena[(rsn.setWidth 64 + 2).toNat]'hsz_lt
    refine wp_join_group (ts := []) (fun _ m' => ∃ st', arAllowInv c s sc0 R_hdr st' m')
      (fun _ _ m' ⟨st', hst'⟩ => by rw [Blocks.get_here]; exact hJ34 () m' ⟨st', hst'⟩)
      (fun J40 hJ40 => ?_)
    c0_hsteps_nogrp
    · have hsz_fit : rsn.toNat + 3 + sz_bv.toNat ≤ s.core.arena_len := by
        have hidx : (rsn.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
            (rsn.setWidth 64 + 2).toNat := by bv_omega
        have hidx_lt :
            (rsn.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 < s.core.arena.length := by
          rw [hidx]; exact hsz_lt
        have h1 : (rsn.toNat + BitVec.toNat (3 : BitVec 64) +
            (s.core.arena[(rsn.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'hidx_lt).toNat) %
            2 ^ 64 ≤ s.core.arena_len % 2 ^ 64 := by assumption
        have hsz_eq : s.core.arena[(rsn.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'hidx_lt =
            sz_bv := s13ar_getElem_congr hidx
        rw [hsz_eq, Nat.mod_eq_of_lt hal64] at h1; bv_omega
      have htk_m : (FullMem c (mkArState s sc0 mrk_i mcl_i ws_i (tk_i + 1)) ⋆ R_hdr) m := by
        simpa only [si, mkArState] using hm
      refine wp_while_state1 (t := i32) (α := Nat × ArSt)
        (proj := fun st => BitVec.ofNat 32 st.1) (μ := fun st => sz_bv.toNat - st.1)
        (Inv := fun st mj => st.1 ≤ sz_bv.toNat ∧ arAllowInv c s sc0 R_hdr st.2 mj)
        (fun J46 hJ46 => by
          c0_hsteps; exact hJ46 (0, mrk_i, mcl_i, ws_i, tk_i + 1) _
            ⟨Nat.zero_le _, hmrk_i, hws_i, hcov_i, htk_m⟩)
        (fun J46 ⟨j, mrk_j, mcl_j, ws_j, tk_j⟩ mj ⟨hj_le, hmrk_j, hws_j, hcov_j, hmj⟩ ihj => ?_)
      dsimp only at hj_le hmrk_j hws_j hcov_j hmj ihj; rw [Blocks.get_here]; dsimp only
      let sj := mkArState s sc0 mrk_j mcl_j ws_j tk_j
      c0_hsteps_nogrp
      · have hj_lt : j < sz_bv.toNat := by
          have h1 : j % 2 ^ 32 < sz_bv.toNat := by
            simpa only [BitVec.toNat_ofNat] using (by assumption : _)
          rwa [Nat.mod_eq_of_lt (by omega : j < 2 ^ 32)] at h1
        have hj_ar : (rsn.setWidth 64 + 3 + (BitVec.ofNat 32 j).setWidth 64).toNat <
            sj.core.arena.length := by
          have hj32 : (BitVec.ofNat 32 j).toNat = j := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hsum : (rsn.setWidth 64 + 3 + (BitVec.ofNat 32 j).setWidth 64).toNat =
              rsn.toNat + 3 + j := by bv_omega
          rw [hsum, show sj.core.arena = s.core.arena from rfl, hco.arena_len_arr]
          have := hco.arena_len_le; omega
        c0_hsteps_nogrp
        refine wp_join_group (ts := [])
          (fun _ mj' => ∃ st : ArSt, arAllowInv c s sc0 R_hdr st mj')
          (fun _ _ mj' ⟨st, hinv⟩ => by
            rw [Blocks.get_here]; c0_hsteps
            have hj1 : BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                show (1 : BitVec 32).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega : j < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ 32)]
            rw [hj1]
            exact ihj (j + 1, st) mj' (by change sz_bv.toNat - (j + 1) < sz_bv.toNat - j; omega)
              ⟨by change j + 1 ≤ sz_bv.toNat; omega, hinv⟩)
          (fun J52 hJ52 => s13_ar_push_ov_wp (st := (mrk_j, mcl_j, ws_j, tk_j)) hlen
            ⟨hmrk_j, hws_j, hcov_j, hmj⟩ fun st' m'' hst' => hJ52 () m'' ⟨st', hst'⟩)
      all_goals exact hJ40 () mj ⟨(mrk_j, mcl_j, ws_j, tk_j), hmrk_j, hws_j, hcov_j, hmj⟩
    all_goals exact hJ40 () mi ⟨(mrk_i, mcl_i, ws_i, tk_i), hmrk_i, hws_i, hcov_i, hmi⟩
  all_goals exact hJ34 () mi ⟨(mrk_i, mcl_i, ws_i, tk_i), hmrk_i, hws_i, hcov_i, hmi⟩

/-! ## 3. `full_analyze_reasons_fid_step13_wp` -/

/-- Step-13 `full_analyze_reasons_fid` satisfies `s13AnalyzeReasonsSpecP M6ExtW2bPres`. -/
theorem full_analyze_reasons_fid_step13_wp (Γ : Env)
    (hDelaying : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hDrAllow : ∀ a m Q X, m6HdrDrAllowSpec a m Q X → Γ "m6_hdr_dr_allow" [i64] [.bool] a m Q X)
    (hBumpDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hReduceDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X) :
    ∀ a m Q X, s13AnalyzeReasonsSpecP M6ExtW2bPres a m Q X →
      Func.wp Γ fidStep13S4AnalyzeReasonsFidFn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hmrk0, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hco := hlen.core_ok; have hso := hlen.scratch_ok
  have hcv_le := hco.cur_vars_le; have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
  have hmrk0_len := hco.mrk_len; have hws10_len := hso.work_stk1_len
  unfold Func.wp fidStep13S4AnalyzeReasonsFidFn full_analyze_reasons_fid_body
  rw [fullM6HdrMem_iff] at hm
  let R0 : Mem 64 → Prop := array64 (c.hdr - 2304) ext ⋆ R
  dsimp only; c0_hsteps_nogrp
  · have hpr_ne : s.core.probing ≠ 0#64 := by bv_omega
    exact hQ s.core.mrk s.core.min_clr_len s.scratch ext m hlen hmrk0
      (fun h0 => absurd h0 hpr_ne) (fun _ => rfl) ⟨rfl, rfl⟩ rfl hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) (by cases s; exact (fullM6HdrMem_iff ..).mpr hm)
  · have hpr0 : s.core.probing = 0#64 := by assumption
    refine wp_join_state1 (t := i64) (α := Nat) (proj := BitVec.ofNat 64)
      (Inv := fun an ma => an ≤ s.core.cur_vars ∧ ma = m)
      (fun Jan ana_n ma ⟨hana_le, hma⟩ => ?_) (fun Jan hJan => ?_)
    · subst ma; rw [Blocks.get_here]; dsimp only; c0_hsteps_nogrp
      refine wp_while_state (ts := [i64, i64])
        (α := Nat × Nat × List (BitVec 8) × List (BitVec 32))
        (proj := fun st => (BitVec.ofNat 64 st.1, BitVec.ofNat 64 st.2.1, ()))
        (μ := fun st => ana_n - st.2.1)
        (Inv := fun st m1 => st.2.1 ≤ ana_n ∧ st.1 ≤ st.2.1 ∧
          st.2.2.1.length = c.max_vars ∧ st.2.2.2.length = 2 * c.max_vars ∧
          FullAnaMarksCov c (mkArState s s.scratch st.2.2.1 st.1 st.2.2.2 s.scratch.search_ticks) ∧
          (FullMem c (mkArState s s.scratch st.2.2.1 s.core.min_clr_len st.2.2.2
            s.scratch.search_ticks) ⋆ R0) m1)
        (fun Jk hJk => by
          c0_hsteps
          exact hJk (0, 0, s.core.mrk, s.scratch.work_stk1) m
            ⟨Nat.zero_le _, Nat.zero_le _, hmrk0_len, hws10_len,
             ⟨Nat.zero_le _, by simp, fun _ hk => by dsimp only [mkArState] at hk; omega,
              fun v hv hnz => absurd (hmrk0 v hv) hnz⟩, by cases s; exact hm⟩)
        (fun Jk ⟨w, k, mrk1, ws1⟩ m1 ⟨hk_le, hw_le, hmrk1, hws1, hcov1, hm1⟩ ihk => ?_)
      dsimp only at hk_le hw_le hmrk1 hws1 hcov1 hm1 ihk; rw [Blocks.get_here]; dsimp only
      c0_hsteps_nogrp
      · have hk_lt : k < ana_n := s13ar_k_lt_of_mod (by omega) (by omega)
          (by simpa [BitVec.toNat_ofNat] using (by assumption : _))
        have hk_ws : (BitVec.ofNat 64 k).toNat < ws1.length := by
          rw [bv64_ofNat_toNat (by omega), hws1]; omega
        let av := ws1[(BitVec.ofNat 64 k).toNat]'hk_ws
        refine wp_join_state1 (t := i64) (α := Nat × List (BitVec 8) × List (BitVec 32))
          (proj := fun st => BitVec.ofNat 64 st.1)
          (Inv := fun st m1' => st.1 ≤ k + 1 ∧ st.2.1.length = c.max_vars ∧
            st.2.2.length = 2 * c.max_vars ∧
            FullAnaMarksCov c (mkArState s s.scratch st.2.1 st.1 st.2.2 s.scratch.search_ticks) ∧
            (FullMem c (mkArState s s.scratch st.2.1 s.core.min_clr_len st.2.2
              s.scratch.search_ticks) ⋆ R0) m1')
          (fun _ ⟨w', mrk', ws'⟩ m1' ⟨hw', hml', hwsl', hcov', hm1'⟩ => by
            rw [Blocks.get_here]; c0_hsteps; rw [s13ar_ofNat64_add1 (by omega)]
            exact ihk (w', k + 1, mrk', ws') m1' (by change ana_n - (k + 1) < ana_n - k; omega)
              ⟨by change k + 1 ≤ ana_n; omega, hw', hml', hwsl', hcov', hm1'⟩)
          (fun Js1 hJs1 => ?_)
        c0_hsteps_nogrp
        · have hav_cv : av.toNat < s.core.cur_vars := by
            have h1 : av.toNat < s.core.cur_vars % 2 ^ 64 := by
              simpa only [av, s13ar_bv32_setWidth64, BitVec.toNat_ofNat] using (by assumption : _)
            rwa [Nat.mod_eq_of_lt hcv_lt64] at h1
          have hav_mrk : (av.setWidth 64).toNat < mrk1.length := by
            rw [s13ar_bv32_setWidth64, hmrk1]; omega
          have hav_z : mrk1[av.toNat]?.getD 0#8 = 0#8 := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            exact s13ar_bv8_zext32_eq0_iff.mp (by
              simpa only [av, s13ar_bv32_setWidth64] using (by assumption : _))
          have hw_ws : (BitVec.ofNat 64 w).toNat < ws1.length := by
            rw [bv64_ofNat_toNat (by omega), hws1]; omega
          c0_hsteps; rw [s13ar_ofNat64_add1 (by omega)]
          refine hJs1 (w + 1, mrk1.set av.toNat 1#8, ws1.set w av) _
            ⟨by omega, by rw [List.length_set, hmrk1], by rw [List.length_set, hws1],
             s13ar_push_cov hmrk1 hws1 hcv_le hcov1 hav_cv hav_z (by omega), ?_⟩
          simpa only [mkArState, av, s13ar_bv32_setWidth64,
            bv64_ofNat_toNat (by omega : w < 2 ^ 64), show BitVec.ofNat 8 1 = 1#8 from rfl] using hm
        all_goals exact hJs1 (w, mrk1, ws1) m1 ⟨by omega, hmrk1, hws1, hcov1, hm1⟩
      · refine wp_join_state1 (t := i64) (α := Nat × List (BitVec 8) × List (BitVec 32))
          (proj := fun st => BitVec.ofNat 64 st.1)
          (Inv := fun st m2 => st.1 ≤ s.core.cur_vars ∧ st.2.1.length = c.max_vars ∧
            st.2.2.length = 2 * c.max_vars ∧
            FullAnaMarksCov c (mkArState s s.scratch st.2.1 st.1 st.2.2 s.scratch.search_ticks) ∧
            (FullMem c (mkArState s s.scratch st.2.1 s.core.min_clr_len st.2.2
              s.scratch.search_ticks) ⋆ R0) m2)
          (fun _ ⟨w2, mrk2, ws2⟩ m2 ⟨hw2_cv, hmrk2, hws2, hcov2, hm2⟩ => ?_)
          (fun Jt2 hJt2 => ?_)
        · rw [Blocks.get_here]; dsimp only
          have hw2_lt64 : w2 < 2 ^ 64 := by omega
          have hlen2 : (mkArState s s.scratch mrk2 w2 ws2 s.scratch.search_ticks).LengthsOk c :=
            mkArState_lengths hlen hmrk2 hws2 (by omega)
          c0_hsteps_nogrp
          · have hm2s : (FullMem c (mkArState s s.scratch mrk2 w2 ws2 s.scratch.search_ticks) ⋆ R0)
                m := by simpa only [mkArState, bv64_ofNat_toNat hw2_lt64] using hm
            have hw2_z : w2 = 0 := by
              have h1 : BitVec.ofNat 64 w2 = 0#64 := by assumption
              have h2 := congrArg BitVec.toNat h1
              rw [bv64_ofNat_toNat hw2_lt64] at h2; exact h2
            have hmrk2_0 : ∀ v < c.max_vars, mrk2[v]?.getD 0#8 = 0#8 := fun v hv =>
              Classical.byContradiction fun hnz => by
                obtain ⟨k, hk, _⟩ := hcov2.2.2.2 v hv hnz; dsimp only [mkArState] at hk; omega
            exact hQ mrk2 w2 { s.scratch with work_stk1 := ws2 } ext m hlen2 hmrk2_0
              (fun _ => ⟨hw2_cv, fun k hk => by omega⟩) (fun h => absurd hpr0 h)
              ⟨rfl, rfl⟩ rfl hext (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩)
              ((fullM6HdrMem_iff ..).mpr hm2s)
          · have hm2s : (FullMem c (mkArState s s.scratch mrk2 w2 ws2 s.scratch.search_ticks) ⋆ R0)
                m := by simpa only [mkArState, bv64_ofNat_toNat hw2_lt64] using hm
            refine wp_join_group (ts := []) (fun _ m_post => arPostInv c s ext R m_post)
              (fun _ _ m_post hpost => by
                rw [Blocks.get_here]; exact s13_ar_clear_wp hpr0 hpost hQ)
              (fun Jpost hJpost => ?_)
            let s2 := mkArState s s.scratch mrk2 w2 ws2 s.scratch.search_ticks
            m6h_call hDelaying
            refine m6HdrW2aSpec_of rfl hcfg hext hlen2 ((fullM6HdrMem_iff ..).mpr hm2s)
              fun ⟨dl, ⟨⟩⟩ ext0 s0 m0 hcore0 hlen0 hsc0 hext0 hw0 hm0 => ?_
            obtain ⟨sc0, rfl⟩ : ∃ sc0 : FullScratch, s0 = { s2 with scratch := sc0 } := by
              obtain ⟨core0, sc0⟩ := s0; dsimp only at hcore0; subst hcore0; exact ⟨sc0, rfl⟩
            have hws1_eq : sc0.work_stk1 = ws2 := hsc0.ws1
            have hcov0 : FullAnaMarksCov c { s2 with scratch := sc0 } := by
              obtain ⟨h1, h2, h3, h4⟩ := hcov2
              exact ⟨h1, by dsimp only [s2, mkArState]; rw [hws1_eq]; exact h2,
                by dsimp only [s2, mkArState]; rw [hws1_eq]; exact h3,
                fun v hv hnz => let ⟨k, hk, heq⟩ := h4 v hv hnz
                  ⟨k, hk, by dsimp only [s2, mkArState]; rw [hws1_eq]; exact heq⟩⟩
            have hpre0 : FullExtScratchPres s { s with scratch := sc0 } := hsc0.extPres
            have hws20 : sc0.work_stk2 = s.scratch.work_stk2 := hsc0.ws2
            have hws10_l : sc0.work_stk1.length = 2 * c.max_vars := hlen0.scratch_ok.work_stk1_len
            rw [fullM6HdrMem_iff] at hm0; c0_hsteps_nogrp
            · exact hJpost () m0 ⟨ext0, sc0, mrk2, w2, hext0, hw0, hlen0, hcov0, hpre0, hws20, hm0⟩
            m6h_call hDrAllow
            refine m6HdrDrAllowSpec_of hcfg hext0 hlen0 ((fullM6HdrMem_iff ..).mpr hm0)
              fun allow ext1 m1 hinit1 hext_eq hm1 => ?_
            have hext1 : M6HdrExtOk ext1 := hinit1.toOk
            have hinit_pres : M6HdrExtInitOk ext → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext ext1 :=
              fun hi => ⟨hinit1, by rw [hext_eq (hw0 hi).1]; exact (hw0 hi).2⟩
            rw [fullM6HdrMem_iff] at hm1
            let R_hdr : Mem 64 → Prop := array64 (c.hdr - 2304) ext1 ⋆ R
            c0_hsteps_nogrp
            · refine wp_join_state1 (t := i64) (α := Nat) (proj := BitVec.ofNat 64)
                (Inv := fun tlen mt => tlen ≤ s.core.cur_vars ∧ mt = m1)
                (fun Jt tlen mt ⟨htlen_le, hmt⟩ => ?_) (fun Jt hJt => ?_)
              · subst mt; rw [Blocks.get_here]; dsimp only; c0_hsteps_nogrp
                refine wp_while_state1 (t := i64) (α := Nat × ArSt)
                  (proj := fun st => BitVec.ofNat 64 st.1) (μ := fun st => tlen - st.1)
                  (Inv := fun st mi => st.1 ≤ tlen ∧ arAllowInv c s sc0 R_hdr st.2 mi)
                  (fun Ji hJi => by
                    c0_hsteps
                    exact hJi (0, mrk2, w2, sc0.work_stk1, sc0.search_ticks) m1
                      ⟨Nat.zero_le _, hmrk2, hws10_l, by cases sc0; exact hcov0,
                       by cases sc0; exact hm1⟩)
                  (fun Ji ⟨i, mrk_i, mcl_i, ws_i, tk_i⟩ mi ⟨hi_le, hmrk_i, hws_i, hcov_i, hmi⟩
                      ihi => ?_)
                dsimp only at hi_le hmrk_i hws_i hcov_i hmi ihi; rw [Blocks.get_here]; dsimp only
                let si := mkArState s sc0 mrk_i mcl_i ws_i tk_i
                refine wp_join_group (ts := []) (fun _ mr => ∃ st_a : ArSt,
                    arAllowInv c s sc0 R_hdr st_a mr)
                  (fun _ _ mr ⟨st_a, hinv_a⟩ => by
                    rw [Blocks.get_here]
                    have hlen_sc0 : ({ s with scratch := sc0 } : FullState).LengthsOk c :=
                      ⟨hlen.core_ok, hlen0.scratch_ok⟩
                    exact s13_ar_rollback_wp hBumpDelay hReduceDelay hcfg hext1
                      hlen_sc0 hpre0 hws20 hinit_pres hw2_lt64 hinv_a
                      (fun m' hp => hJpost () m' hp))
                  (fun Jafter hJafter => ?_)
                c0_hsteps_nogrp
                · have hi_lt : i < tlen := s13ar_k_lt_of_mod (by omega) (by omega)
                    (by simpa [BitVec.toNat_ofNat] using (by assumption : _))
                  have hi_tmp_bv : (BitVec.ofNat 64 i).toNat < si.core.tmp.length := by
                    rw [bv64_ofNat_toNat (by omega), show si.core.tmp = s.core.tmp from rfl,
                      hco.tmp_len_arr]; omega
                  c0_hsteps_nogrp
                  refine wp_join_state1 (t := i32) (α := BitVec 32) (proj := id)
                    (Inv := fun _ m' => m' = mi)
                    (fun Jrsn rsn mr' hmr' => ?_) (fun Jrsn hJrsn => ?_)
                  · subst mr'; rw [Blocks.get_here]
                    refine wp_join_group (ts := [])
                      (fun _ mi' => ∃ st : ArSt, arAllowInv c s sc0 R_hdr st mi')
                      (fun _ _ mi' ⟨st, hinv⟩ => by
                        rw [Blocks.get_here]; c0_hsteps; rw [s13ar_ofNat64_add1 (by omega)]
                        exact ihi (i + 1, st) mi' (by change tlen - (i + 1) < tlen - i; omega)
                          ⟨by change i + 1 ≤ tlen; omega, hinv⟩)
                      (fun Jrs hJrs => s13_ar_rsn_body_wp (st_i := (mrk_i, mcl_i, ws_i, tk_i))
                        hlen ⟨hmrk_i, hws_i, hcov_i, hmi⟩
                        fun st' m'' hst' => hJrs () m'' ⟨st', hst'⟩)
                  · c0_hsteps_nogrp
                    · let uv := (si.core.tmp[(BitVec.ofNat 64 i).toNat]'hi_tmp_bv) >>> 1
                      have huv_rsn : (uv.setWidth 64).toNat < si.core.rsns.length := by
                        have huv_cv : uv.toNat < s.core.cur_vars := by
                          have h1 : uv.toNat < s.core.cur_vars % 2 ^ 64 := by
                            simpa only [uv, s13ar_bv32_setWidth64, BitVec.toNat_ofNat] using
                              (by assumption : _)
                          rwa [Nat.mod_eq_of_lt hcv_lt64] at h1
                        rw [s13ar_bv32_setWidth64, show si.core.rsns = s.core.rsns from rfl,
                          hco.rsns_len]; omega
                      c0_hsteps; exact hJrsn _ mi rfl
                    · c0_hsteps; exact hJrsn _ mi rfl
                all_goals (
                  exact hJafter () mi ⟨(mrk_i, mcl_i, ws_i, tk_i), hmrk_i, hws_i, hcov_i, hmi⟩)
              · c0_hsteps_nogrp
                · exact hJt s.core.cur_vars m1 ⟨le_refl _, rfl⟩
                · have ht_le : s.core.tmp_len ≤ s.core.cur_vars := by
                    have h1 : ¬ s.core.cur_vars % 2 ^ 64 < s.core.tmp_len % 2 ^ 64 := by
                      assumption
                    rw [Nat.mod_eq_of_lt hcv_lt64,
                      Nat.mod_eq_of_lt (by have := hco.tmp_len_le; omega)] at h1; omega
                  exact hJt s.core.tmp_len m1 ⟨ht_le, rfl⟩
            · exact hJpost () m1 ⟨ext1, sc0, mrk2, w2, hext1, hinit_pres, hlen0, hcov0, hpre0,
                hws20, hm1⟩
        · c0_hsteps_nogrp
          · have htlen_cv : s.core.tmp_len ≤ s.core.cur_vars := by
              have h1 : s.core.tmp_len % 2 ^ 64 ≤ s.core.cur_vars % 2 ^ 64 := by
                simpa [mkArState, BitVec.toNat_ofNat] using (by assumption : _)
              rwa [Nat.mod_eq_of_lt (by have := hco.tmp_len_le; omega),
                Nat.mod_eq_of_lt hcv_lt64] at h1
            refine wp_while_state (ts := [i64, i64])
              (α := Nat × Nat × List (BitVec 8) × List (BitVec 32))
              (proj := fun st => (BitVec.ofNat 64 st.1, BitVec.ofNat 64 st.2.1, ()))
              (μ := fun st => s.core.tmp_len - st.2.1)
              (Inv := fun st m2 => st.2.1 ≤ s.core.tmp_len ∧ st.1 ≤ s.core.cur_vars ∧
                st.2.2.1.length = c.max_vars ∧ st.2.2.2.length = 2 * c.max_vars ∧
                FullAnaMarksCov c (mkArState s s.scratch st.2.2.1 st.1 st.2.2.2
                  s.scratch.search_ticks) ∧
                (FullMem c (mkArState s s.scratch st.2.2.1 s.core.min_clr_len st.2.2.2
                  s.scratch.search_ticks) ⋆ R0) m2)
              (fun Jti hJti => by
                c0_hsteps
                exact hJti (w, 0, mrk1, ws1) m1
                  ⟨Nat.zero_le _, by omega, hmrk1, hws1, hcov1, hm1⟩)
              (fun Jti ⟨wt, ti, mrkT, wsT⟩ m2 ⟨hti_le, hwt_cv, hmrkT, hwsT, hcovT, hm2⟩ ihti => ?_)
            dsimp only at hti_le hwt_cv hmrkT hwsT hcovT hm2 ihti; rw [Blocks.get_here]; dsimp only
            c0_hsteps_nogrp
            · have hti_lt : ti < s.core.tmp_len := s13ar_k_lt_of_mod (by omega) (by omega)
                (by simpa [BitVec.toNat_ofNat] using (by assumption : _))
              have hti_tmp : (BitVec.ofNat 64 ti).toNat < s.core.tmp.length := by
                rw [bv64_ofNat_toNat (by omega), hco.tmp_len_arr]; omega
              c0_hsteps_nogrp
              let tv := (s.core.tmp[(BitVec.ofNat 64 ti).toNat]'hti_tmp) >>> 1
              refine wp_join_state1 (t := i64) (α := Nat × List (BitVec 8) × List (BitVec 32))
                (proj := fun st => BitVec.ofNat 64 st.1)
                (Inv := fun st m2' => st.1 ≤ s.core.cur_vars ∧ st.2.1.length = c.max_vars ∧
                  st.2.2.length = 2 * c.max_vars ∧
                  FullAnaMarksCov c (mkArState s s.scratch st.2.1 st.1 st.2.2
                    s.scratch.search_ticks) ∧
                  (FullMem c (mkArState s s.scratch st.2.1 s.core.min_clr_len st.2.2
                    s.scratch.search_ticks) ⋆ R0) m2')
                (fun _ ⟨wt', mrk', ws'⟩ m2' ⟨hwt', hml', hwsl', hcov', hm2'⟩ => by
                  rw [Blocks.get_here]; c0_hsteps; rw [s13ar_ofNat64_add1 (by omega)]
                  exact ihti (wt', ti + 1, mrk', ws') m2'
                    (by change s.core.tmp_len - (ti + 1) < s.core.tmp_len - ti; omega)
                    ⟨by change ti + 1 ≤ s.core.tmp_len; omega, hwt', hml', hwsl', hcov', hm2'⟩)
                (fun Js2 hJs2 => ?_)
              c0_hsteps_nogrp
              · have htv_cv : tv.toNat < s.core.cur_vars := by
                  have h1 : tv.toNat < s.core.cur_vars % 2 ^ 64 := by
                    simpa only [tv, s13ar_bv32_setWidth64, BitVec.toNat_ofNat] using
                      (by assumption : _)
                  rwa [Nat.mod_eq_of_lt hcv_lt64] at h1
                have htv_lvl : (tv.setWidth 64).toNat < s.core.lvl.length := by
                  rw [s13ar_bv32_setWidth64, hco.lvl_len]; omega
                have htv_mrk : (tv.setWidth 64).toNat < mrkT.length := by
                  rw [s13ar_bv32_setWidth64, hmrkT]; omega
                c0_hsteps_nogrp
                · have htv_z : mrkT[tv.toNat]?.getD 0#8 = 0#8 := by
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                    exact s13ar_bv8_zext32_eq0_iff.mp (by
                      simpa only [tv, s13ar_bv32_setWidth64] using (by assumption : _))
                  have hwt_lt : wt < s.core.cur_vars := s13ar_k_lt_of_mod (by omega) hcv_lt64
                    (by simpa [BitVec.toNat_ofNat] using (by assumption : _))
                  have hwt_ws : (BitVec.ofNat 64 wt).toNat < wsT.length := by
                    rw [bv64_ofNat_toNat (by omega), hwsT]; omega
                  c0_hsteps; rw [s13ar_ofNat64_add1 (by omega)]
                  refine hJs2 (wt + 1, mrkT.set tv.toNat 1#8, wsT.set wt tv) _
                    ⟨by omega, by rw [List.length_set, hmrkT], by rw [List.length_set, hwsT],
                     s13ar_push_cov hmrkT hwsT hcv_le hcovT htv_cv htv_z hwt_lt, ?_⟩
                  simpa only [mkArState, tv, s13ar_bv32_setWidth64,
                    bv64_ofNat_toNat (by omega : wt < 2 ^ 64),
                    show BitVec.ofNat 8 1 = 1#8 from rfl] using hm
                all_goals exact hJs2 (wt, mrkT, wsT) m2 ⟨hwt_cv, hmrkT, hwsT, hcovT, hm2⟩
              · exact hJs2 (wt, mrkT, wsT) m2 ⟨hwt_cv, hmrkT, hwsT, hcovT, hm2⟩
            · exact hJt2 (wt, mrkT, wsT) m2 ⟨hwt_cv, hmrkT, hwsT, hcovT, hm2⟩
          · exact hJt2 (w, mrk1, ws1) m1 ⟨by omega, hmrk1, hws1, hcov1, hm1⟩
    · c0_hsteps_nogrp
      · exact hJan s.core.cur_vars m ⟨le_refl _, rfl⟩
      · have hr_le : s.scratch.res_sz.toNat ≤ s.core.cur_vars := by
          have h1 : ¬ s.core.cur_vars % 2 ^ 64 < s.scratch.res_sz.toNat := by assumption
          rw [Nat.mod_eq_of_lt hcv_lt64] at h1; omega
        have hres_eq : BitVec.ofNat 64 s.scratch.res_sz.toNat = s.scratch.res_sz := by simp
        rw [← hres_eq]
        exact hJan s.scratch.res_sz.toNat m ⟨hr_le, rfl⟩

/-! ## 4. Wrapper Specs & Proofs (`full_bump_analyzed_m6_hdr`, `full_restore_bump_ana_m6_hdr`) -/

/-- Step-13 `full_bump_analyzed_m6_hdr` specification over `FullM6HdrMem`, allowing
length-preserving `s.core.repr'` from `PERF-R3` `full_sort_ana_qs_m6`. -/
def s13BumpAnalyzedM6HdrSpecP (Pext : List (BitVec 64) → List (BitVec 64) → Prop) :
    Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    FullAnaMarksCov c s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ mrk' mcl' repr' sc' ext' m',
      let s' : FullState :=
        { s with
          core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
          scratch := sc' }
      s'.LengthsOk c → FullAnaMarksCov c s' →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ Pext ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

theorem s13BumpAnalyzedM6HdrSpecP_monoX
    {Pext : List (BitVec 64) → List (BitVec 64) → Prop}
    {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : s13BumpAnalyzedM6HdrSpecP Pext xs m Q X) :
    s13BumpAnalyzedM6HdrSpecP Pext xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem s13BumpAnalyzedM6HdrSpecP_of
    {Pext : List (BitVec 64) → List (BitVec 64) → Prop}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hcov : FullAnaMarksCov c s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ mrk' mcl' repr' sc' ext' m',
      let s' : FullState :=
        { s with
          core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
          scratch := sc' }
      s'.LengthsOk c → FullAnaMarksCov c s' →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ Pext ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    s13BumpAnalyzedM6HdrSpecP Pext (c.hdr, ()) m Q X :=
  ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hcov, hm, hQ⟩

theorem s13BumpAnalyzedM6HdrSpecP_elim
    {Pext : List (BitVec 64) → List (BitVec 64) → Prop}
    {h : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hs : s13BumpAnalyzedM6HdrSpecP Pext (h, ()) m Q X) :
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      FullAnaMarksCov c s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ mrk' mcl' repr' sc' ext' m',
        let s' : FullState :=
          { s with
            core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
            scratch := sc' }
        s'.LengthsOk c → FullAnaMarksCov c s' →
        FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ Pext ext ext') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m' :=
  hs

/-- Step-13 `full_restore_bump_ana_m6_hdr` specification over `FullM6HdrMem`, allowing
length-preserving `s.core.repr'` from `PERF-R3` `full_sort_ana_qs_m6`. -/
def s13RestoreBumpAnaM6HdrSpecP (Pext : List (BitVec 64) → List (BitVec 64) → Prop) :
    Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ mrk' mcl' repr' sc' ext' m',
      let s' : FullState :=
        { core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
          scratch := sc' }
      s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (s.core.probing = 0#64 → mcl' = 0) →
      (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ Pext ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

theorem s13RestoreBumpAnaM6HdrSpecP_monoX
    {Pext : List (BitVec 64) → List (BitVec 64) → Prop}
    {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : s13RestoreBumpAnaM6HdrSpecP Pext xs m Q X) :
    s13RestoreBumpAnaM6HdrSpecP Pext xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem s13RestoreBumpAnaM6HdrSpecP_of
    {Pext : List (BitVec 64) → List (BitVec 64) → Prop}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hmrk0 : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ mrk' mcl' repr' sc' ext' m',
      let s' : FullState :=
        { core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
          scratch := sc' }
      s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (s.core.probing = 0#64 → mcl' = 0) →
      (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ Pext ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    s13RestoreBumpAnaM6HdrSpecP Pext (c.hdr, ()) m Q X :=
  ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hmrk0, hm, hQ⟩

theorem s13RestoreBumpAnaM6HdrSpecP_elim
    {Pext : List (BitVec 64) → List (BitVec 64) → Prop}
    {h : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hs : s13RestoreBumpAnaM6HdrSpecP Pext (h, ()) m Q X) :
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ mrk' mcl' repr' sc' ext' m',
        let s' : FullState :=
          { core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
            scratch := sc' }
        s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
        (s.core.probing = 0#64 → mcl' = 0) →
        (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
        FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ Pext ext ext') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m' :=
  hs

/-- Step-13 `full_bump_analyzed_m6_hdr` delegates directly to `full_bump_analyzed_mode_fid`. -/
theorem full_bump_analyzed_m6_hdr_step13_wp (Γ : Env)
    (hBumpMode : ∀ a m Q X, s13BumpAnalyzedModeSpecP M6ExtW2bPres a m Q X →
      Γ "full_bump_analyzed_mode_fid" [i64, .bool] [] a m Q X) :
    ∀ a m Q X, s13BumpAnalyzedM6HdrSpecP M6ExtW2bPres a m Q X →
      Func.wp Γ fidStep13S4BumpAnalyzedM6HdrFn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hcov, hm, hQ⟩ := s13BumpAnalyzedM6HdrSpecP_elim hs
  unfold Func.wp fidStep13S4BumpAnalyzedM6HdrFn full_bump_analyzed_m6_hdr_body
  c0_hsteps_nogrp
  refine wp_call_of_spec _ _ (hBumpMode _ _ _ _
    (s13BumpAnalyzedModeSpecP_of hcfg hext hlen (s13BumpPre_of_cov true hcov) hm
      fun mrk' mcl' repr' sc' ext' m' hlen' hcov' _ _ hpre' hws2' hext' hinit' hm' => ?_))
  c0_hsteps
  exact hQ mrk' mcl' repr' sc' ext' m' hlen' (hcov' hcov) hpre' hws2' hext' hinit' hm'

/-- Step-13 `full_restore_bump_ana_m6_hdr` delegates to `full_restore_bump_ana_mode_fid`. -/
theorem full_restore_bump_ana_m6_hdr_step13_wp (Γ : Env)
    (hRestoreMode : ∀ a m Q X, s13RestoreBumpAnaModeSpecP M6ExtW2bPres a m Q X →
      Γ "full_restore_bump_ana_mode_fid" [i64, .bool] [] a m Q X) :
    ∀ a m Q X, s13RestoreBumpAnaM6HdrSpecP M6ExtW2bPres a m Q X →
      Func.wp Γ fidStep13S4RestoreBumpAnaM6HdrFn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hmrk0, hm, hQ⟩ :=
    s13RestoreBumpAnaM6HdrSpecP_elim hs
  unfold Func.wp fidStep13S4RestoreBumpAnaM6HdrFn full_restore_bump_ana_m6_hdr_body
  c0_hsteps_nogrp
  refine wp_call_of_spec _ _ (hRestoreMode _ _ _ _
    (s13RestoreBumpAnaModeSpecP_of hcfg hext hlen hmrk0 hm
      fun mrk' mcl' repr' sc' ext' m' hlen' hmrk0' hp0 hpne hpre' hws2' hext' hinit' hm' => ?_))
  c0_hsteps
  exact hQ mrk' mcl' repr' sc' ext' m' hlen' hmrk0' hp0 hpne hpre' hws2' hext' hinit' hm'

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

end
