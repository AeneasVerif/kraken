/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2BCPWatchProof2a
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat Fidelity Step 13 Shard S2-A Post-Scan Proofs (`FullFidelityStep13S2BCPWatchProof2b`)

Plain `public section` (`@[expose]` ONLY on concrete AST `Expr` builders, `0` `@[expose]` on
theorems, `0` `import all`, `<= 100` cols, every theorem `<= 280` lines):
1. `S13Scr`, `S13HQ`, and exit/ticks lemmas (`s13_post_ticks_wp`, `s13_exit_hQ`,
   `s13_outer_flush_ret`, `s13_post_exit_brk2`, `s13_post_exit_brk1`).
2. Parameterized post-scan AST builders (`s13PostTicksExpr`, `s13PostBrkContExpr`,
   `s13PostFlushExpr`, `s13CompactAndPostExpr`).
3. Post-scan WP proofs (`s13_post_brk_cont_wp`, `s13_post_flush_wp`, `s13_compact_post_wp`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM7BcpHot
open LeanQbe.T.Examples.Kissat.FullFidelityBcp
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullWatchPushSpec fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

attribute [local irreducible] fastPropMem

local macro "s13_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local macro "s13_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

local macro "s13_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

/-! ## 1. `S13Scr`, `S13HQ` & Exit / Ticks Helpers -/

/-- Step-13 BCP scratch-frame predicate before exit `m6_hdr_add_ticks`: only `search_ticks`,
`wsort`, `phases`, and `delayed` may change from `s0.scratch`. -/
abbrev S13Scr (s0 s1 : FullState) : Prop :=
  s1.scratch = { s0.scratch with
    search_ticks := s1.scratch.search_ticks, wsort := s1.scratch.wsort,
    phases := s1.scratch.phases, delayed := s1.scratch.delayed }

theorem s13_scr_of_pi {s0 s_pi st : FullState}
    (hpi : st.scratch = { s_pi.scratch with
      search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
      phases := st.scratch.phases })
    (h0 : S13Scr s0 s_pi) : S13Scr s0 st := by
  unfold S13Scr at *; rw [hpi, h0]

theorem s13_probePres_of_S13Scr {s st : FullState} (h : S13Scr s st) :
    FullProbeScratchPres { s with scratch := { s.scratch with
      search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
      phases := st.scratch.phases, delayed := st.scratch.delayed } } st := by
  rw [← h]; exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Unified postcondition continuation for `full_propagate_ignore{_hot}` (`isBeyond = false`)
and `full_propagate_beyond_m7` (`isBeyond = true`). -/
abbrev S13HQ (isBeyond : Bool) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (ext0 : List (BitVec 64)) (s : FullState) (ignore_ref : BitVec 64)
    (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (vals' : List (BitVec 8))
    (flags' lvl' rsns' trl' tp' : List (BitVec 32)) (te' prop' : Nat)
    (unas' unfl' : BitVec 64) (wvec' arena' wstk' : List (BitVec 32)) (wlen' : Nat)
    (wu' fuel' ctype' cref' c0' c1' oom' : BitVec 64) (sc' : FullScratch) (m' : Mem 64),
    let s' : FullState :=
      { s with
        core :=
          { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', propagated := prop', unassigned := unas',
            unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
            wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
            confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := sc' }
    M6HdrExtOk ext' →
    (M6HdrExtInitOk ext0 → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext0 ext') →
    s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
    FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
    FullProbeScratchPres { s with scratch := { s.scratch with
      search_ticks := sc'.search_ticks, wsort := sc'.wsort,
      phases := sc'.phases, delayed := sc'.delayed } } s' →
    sc'.red_refs = s.scratch.red_refs →
    sc'.delayed_len = s.scratch.delayed_len →
    (s.core.probing = 0#64 → sc' = { s.scratch with
      search_ticks := sc'.search_ticks, wsort := sc'.wsort,
      phases := sc'.phases, delayed := sc'.delayed }) →
    (c.delayed_cap = 0 → sc'.delayed = s.scratch.delayed) →
    fuel'.toNat ≤ s.core.fuel.toNat →
    (if isBeyond then (r = 0#64 ∨ r = 2#64) else (r = 0#64 ∨ r = 1#64 ∨ r = 2#64)) →
    (isBeyond = true → ctype' = s.core.confl_type ∧ cref' = s.core.confl_ref ∧
      c0' = s.core.confl_lit0 ∧ c1' = s.core.confl_lit1) →
    (r = 0#64 → prop' = te' ∧ (isBeyond = false → ctype' = s.core.confl_type) ∧
      (s.core.oom = 0#64 → oom' = 0#64) ∧
      (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
    (isBeyond = false → r = 1#64 →
      fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s' ∧
      (ctype' = 2#64 → cref' ≠ ignore_ref)) →
    (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
    (s.core.propagated = s.core.trail_end → r = 0#64 ∧ ext' = ext0 ∧ s' = s) →
    (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem s13_exit_hQ {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext0 ext' : List (BitVec 64)} {s st : FullState} {ignore_ref r : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {m' : Mem 64}
    (hQ : S13HQ isBeyond c F0 F_cur ext0 s ignore_ref R Q)
    (hext' : M6HdrExtOk ext')
    (hw2b : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext0 ext')
    (hag : AgreesExcept fidCoreMask s.core st.core)
    (hpres : FullProbeScratchPres { s with scratch := { s.scratch with
      search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
      phases := st.scratch.phases, delayed := st.scratch.delayed } } st)
    (hred : st.scratch.red_refs = s.scratch.red_refs)
    (hdlen : st.scratch.delayed_len = s.scratch.delayed_len)
    (hnp : s.core.probing = 0#64 → st.scratch = { s.scratch with
      search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
      phases := st.scratch.phases, delayed := st.scratch.delayed })
    (hlen : st.LengthsOk c) (hw : FullWitnessInv c F0 F_cur st.core)
    (htr : FullTrailExt s.core st.core) (hperm : FullArenaPermEq s.core st.core)
    (hd0 : c.delayed_cap = 0 → st.scratch.delayed = s.scratch.delayed)
    (hfuel : st.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hr : if isBeyond then (r = 0#64 ∨ r = 2#64) else (r = 0#64 ∨ r = 1#64 ∨ r = 2#64))
    (hbcf : isBeyond = true → S13ConflEq s.core st.core)
    (hr0 : r = 0#64 → st.core.propagated = st.core.trail_end ∧
      (isBeyond = false → st.core.confl_type = s.core.confl_type) ∧
      (s.core.oom = 0#64 → st.core.oom = 0#64) ∧
      (s.core.propagated < s.core.trail_end → st.core.fuel.toNat < s.core.fuel.toNat))
    (hr1 : isBeyond = false → r = 1#64 →
      st.core.fuel.toNat < s.core.fuel.toNat ∧ st.core.oom = 0#64 ∧
      FullPropDecSpecs.FullConflOkW F_cur st.core ∧
      (st.core.confl_type = 2#64 → st.core.confl_ref ≠ ignore_ref))
    (hr2 : r = 2#64 → st.core.oom ≠ 0#64 ∨ st.core.fuel = 0#64)
    (hnoop : s.core.propagated = s.core.trail_end → r = 0#64 ∧ ext' = ext0 ∧ st = s)
    (hm : (FullM6HdrMem c ext' st ⋆ R) m') : Q (r, ()) m' := by
  have hst_eq :
      ({ s with
          core :=
            { s.core with
              vals := st.core.vals, flags := st.core.flags, lvl := st.core.lvl,
              rsns := st.core.rsns, trl := st.core.trl, trail_pos := st.core.trail_pos,
              trail_end := st.core.trail_end, propagated := st.core.propagated,
              unassigned := st.core.unassigned, unflushed := st.core.unflushed,
              wvec := st.core.wvec, arena := st.core.arena, wstk := st.core.wstk,
              wlen := st.core.wlen, wusable := st.core.wusable, fuel := st.core.fuel,
              confl_type := st.core.confl_type, confl_ref := st.core.confl_ref,
              confl_lit0 := st.core.confl_lit0, confl_lit1 := st.core.confl_lit1,
              oom := st.core.oom }
          scratch := st.scratch } : FullState) = st := by
    cases st; dsimp only; congr 1
    exact fid_core_eq_of_agrees s.core _ hag
  exact hQ r ext' st.core.vals st.core.flags st.core.lvl st.core.rsns st.core.trl
    st.core.trail_pos st.core.trail_end st.core.propagated st.core.unassigned st.core.unflushed
    st.core.wvec st.core.arena st.core.wstk st.core.wlen st.core.wusable st.core.fuel
    st.core.confl_type st.core.confl_ref st.core.confl_lit0 st.core.confl_lit1 st.core.oom
    st.scratch m' hext' hw2b (hst_eq.symm ▸ hlen) (hst_eq.symm ▸ hw)
    (hst_eq.symm ▸ htr) (hst_eq.symm ▸ hperm)
    hpres hred hdlen hnp hd0 hfuel hr hbcf hr0
    (fun hb h1 => by
      obtain ⟨h1a, h1b, h1c, h1d⟩ := hr1 hb h1
      refine ⟨h1a, h1b, ?_, h1d⟩
      rw [hst_eq]; exact fullConflOkW_to_fullConflictOkW h1c)
    hr2 (fun h => by simpa [hst_eq] using hnoop h) (hst_eq.symm ▸ hm)

/-! ## 2. Post-Scan AST Builders -/

/-- `if (h->probing != 0ULL) { m6_hdr_add_ticks(h, ticks); }
else { h->search_ticks = h->search_ticks + ticks; } return brk;` -/
@[expose] def s13PostTicksExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (h_p tk_b brk_c : Val i64) : Expr Val Cont [i64] :=
  .group (sig := [[]])
    (fun _Jt => .cons (fun _ => .ret (.var brk_c, ())) .nil)
    (fun Jt =>
      .let_ (Op.mk (.add i64) (.var h_p, (.imm 520, ()))) fun ppr =>
      .load i64 (.var ppr.1) fun prb =>
      .let_ (Op.mk (.cmp .ne i64) (.var prb, (.imm 0, ()))) fun cpr =>
      .jnz (.var cpr.1)
        (@Expr.call _ _ [i64] "m6_hdr_add_ticks" [i64, i64] [] (.var h_p, (.var tk_b, ()))
          fun _ => .jump Jt.1 ())
        (.let_ (Op.mk (.add i64) (.var h_p, (.imm 600, ()))) fun p1 =>
         .load i64 (.var p1.1) fun ld =>
         .let_ (Op.mk (.add i64) (.var ld, (.var tk_b, ()))) fun p2 =>
         .let_ (Op.mk (.add i64) (.var h_p, (.imm 600, ()))) fun p3 =>
         .store (.var p2.1) (.var p3.1) (.jump Jt.1 ())))

/-- `if (brk != 0) { if (brk == 2) h->oom = 1; h->fuel = fuel; ...; post_ticks; return brk; }`,
else continue with `prop + 1`. -/
@[expose] def s13PostBrkContExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (J_out : Cont [i64, i64, i64, i64, i64, i64])
    (h_p prop_v fuel1 te_b un_b uf_b tk_b brk_c : Val i64) : Expr Val Cont [i64] :=
  .let_ (Op.mk (.cmp .ne i64) (.var brk_c, (.imm 0, ()))) fun c0 =>
  .jnz (.var c0.1)
    (.group (sig := [[]])
      (fun _Js_brk => .cons (fun _ =>
        .let_ (Op.mk (.add i64) (.var h_p, (.imm 168, ()))) fun p0 =>
        .store (.var fuel1) (.var p0.1) (
          .let_ (Op.mk (.add i64) (.var prop_v, (.imm 1, ()))) fun p1 =>
          .let_ (Op.mk (.add i64) (.var h_p, (.imm 152, ()))) fun p2 =>
          .store (.var p1.1) (.var p2.1) (
            .let_ (Op.mk (.add i64) (.var h_p, (.imm 144, ()))) fun p3 =>
            .store (.var te_b) (.var p3.1) (
              .let_ (Op.mk (.add i64) (.var h_p, (.imm 792, ()))) fun p4 =>
              .store (.var un_b) (.var p4.1) (
                .let_ (Op.mk (.add i64) (.var h_p, (.imm 512, ()))) fun p5 =>
                .store (.var uf_b) (.var p5.1)
                  (s13PostTicksExpr h_p tk_b brk_c)))))) .nil)
      (fun Js_brk =>
        .let_ (Op.mk (.cmp .eq i64) (.var brk_c, (.imm 2, ()))) fun c2 =>
        .jnz (.var c2.1)
          (.let_ (Op.mk (.add i64) (.var h_p, (.imm 760, ()))) fun p6 =>
           .store (t := i64) (.imm 1) (.var p6.1) (.jump Js_brk.1 ()))
          (.jump Js_brk.1 ())))
    (.let_ (Op.mk (.add i64) (.var prop_v, (.imm 1, ()))) fun p7 =>
     .jump J_out (.var p7.1, (.var te_b, (.var fuel1, (.var un_b, (.var uf_b,
       (.var tk_b, ())))))))

/-- Final delayed-watch flush `if (di > 0) { if (!full_prop_flush_del_fid(h, di)) brk = 2; }`
followed by ticks writeback / return / outer loop continue. -/
@[expose] def s13PostFlushExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (J_out : Cont [i64, i64, i64, i64, i64, i64])
    (h_p prop_v fuel1 te_b un_b uf_b tk_b di_b brk_b : Val i64) : Expr Val Cont [i64] :=
  .group (sig := [[i64]])
    (fun _Jfl => .cons (fun brk_f =>
      s13PostBrkContExpr J_out h_p prop_v fuel1 te_b un_b uf_b tk_b brk_f.1) .nil)
    (fun Jfl =>
      .let_ (Op.mk (.cmp .ugt i64) (.var di_b, (.imm 0, ()))) fun cd =>
      .jnz (.var cd.1)
        (.group (sig := [[i64]])
          (fun _Js_5 => .cons (fun r => .jump Jfl.1 (.var r.1, ())) .nil)
          (fun Js_5 =>
            @Expr.call _ _ [i64] "full_prop_flush_del_fid" [i64, i64] [.bool]
              (.var h_p, (.var di_b, ())) fun ok =>
            .jnz (.var ok.1)
              (.jump Js_5.1 (.var brk_b, ()))
              (.jump Js_5.1 (.imm 2, ()))))
        (.jump Jfl.1 (.var brk_b, ())))

/-- Watch compaction tail copy, slice-size store, sentinel fill, then final flush / exit. -/
@[expose] def s13CompactAndPostExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (J_out : Cont [i64, i64, i64, i64, i64, i64])
    (h_p pWstk pWvec nl64 prop_v fuel1 te_b un_b uf_b tk_b off_b p_b q_b end_b di_b
      brk_b : Val i64) : Expr Val Cont [i64] :=
  .group (sig := [[i64, i64]])
    (fun Jc => .cons (fun pc_qc =>
      .let_ (Op.mk (.cmp .ult i64) (.var pc_qc.1, (.var end_b, ()))) fun c_lt =>
      .jnz (.var c_lt.1)
        (.let_ (Op.mk (.mul i64) (.var pc_qc.2.1, (.imm 4, ()))) fun oq =>
         .let_ (Op.mk (.add i64) (.var pWstk, (.var oq.1, ()))) fun pq =>
         .let_ (Op.mk (.mul i64) (.var pc_qc.1, (.imm 4, ()))) fun op =>
         .let_ (Op.mk (.add i64) (.var pWstk, (.var op.1, ()))) fun pp =>
         .load i32 (.var pp.1) fun ld =>
         .store (.var ld) (.var pq.1) (
           .let_ (Op.mk (.add i64) (.var pc_qc.2.1, (.imm 1, ()))) fun qc1 =>
           .let_ (Op.mk (.add i64) (.var pc_qc.1, (.imm 1, ()))) fun pc1 =>
           .jump Jc.1 (.var pc1.1, (.var qc1.1, ()))))
        (.let_ (Op.mk (.add i64) (.var nl64, (.imm 1, ()))) fun idx1 =>
         .let_ (Op.mk (.mul i64) (.var idx1.1, (.imm 4, ()))) fun off1 =>
         .let_ (Op.mk (.add i64) (.var pWvec, (.var off1.1, ()))) fun ptr1 =>
         .let_ (Op.mk (.sub i64) (.var pc_qc.2.1, (.var off_b, ()))) fun dif =>
         .let_ (Op.mk (.trunc 64 32) (.var dif.1, ())) fun sz32 =>
         .store (.var sz32.1) (.var ptr1.1)
           (.group (sig := [[]])
             (fun _Jfn => .cons (fun _ =>
               s13PostFlushExpr J_out h_p prop_v fuel1 te_b un_b uf_b tk_b di_b brk_b) .nil)
             (fun Jfn =>
               .let_ (Op.mk (.cmp .ult i64) (.var pc_qc.2.1, (.var end_b, ()))) fun ck =>
               .jnz (.var ck.1)
                 (.let_ (Op.mk (.add i64) (.var h_p, (.imm 464, ()))) fun pwu =>
                  .load i64 (.var pwu.1) fun wu =>
                  .let_ (Op.mk (.sub i64) (.var end_b, (.var pc_qc.2.1, ()))) fun df =>
                  .let_ (Op.mk (.add i64) (.var wu, (.var df.1, ()))) fun wu1 =>
                  .let_ (Op.mk (.add i64) (.var h_p, (.imm 464, ()))) fun pwu2 =>
                  .store (.var wu1.1) (.var pwu2.1)
                    (.group (sig := [[i64]])
                      (fun Jk => .cons (fun k =>
                        .let_ (Op.mk (.cmp .ult i64) (.var k.1, (.var end_b, ()))) fun c_k =>
                        .jnz (.var c_k.1)
                          (.let_ (Op.mk (.mul i64) (.var k.1, (.imm 4, ()))) fun ok =>
                           .let_ (Op.mk (.add i64) (.var pWstk, (.var ok.1, ()))) fun pk =>
                           .store (t := i32) (.imm 0xFFFFFFFF) (.var pk.1) (
                             .let_ (Op.mk (.add i64) (.var k.1, (.imm 1, ()))) fun k1 =>
                             .jump Jk.1 (.var k1.1, ())))
                          (.jump Jfn.1 ())) .nil)
                      (fun Jk => .jump Jk.1 (.var pc_qc.2.1, ()))))
                 (.jump Jfn.1 ()))))) .nil)
    (fun Jc => .jump Jc.1 (.var p_b, (.var q_b, ())))

/-! ## 3. Exit Ticks & Branch WP Helpers -/

private theorem s13_probePres_of_step {s st st2 : FullState}
    (hsc : S13Scr s st) (hp2 : FullProbeScratchPres st st2) :
    FullProbeScratchPres { s with scratch := { s.scratch with
      search_ticks := st2.scratch.search_ticks, wsort := st2.scratch.wsort,
      phases := st2.scratch.phases, delayed := st2.scratch.delayed } } st2 := by
  unfold S13Scr at hsc
  rcases hp2 with ⟨⟨h1, h2⟩, h3, h4, h5, h6, h7, h8, h9⟩
  rw [hsc] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨⟨h1, h2⟩, h3, h4, h5, h6, h7, h8, h9⟩

theorem s13_post_ticks_wp {Γ : Env} {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext0 ext1 : List (BitVec 64)} {s st : FullState}
    {ignore_ref tk_b r : BitVec 64} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    (hAddTicks : ∀ args m Q X, step13AddTicksSpec args m Q X →
      Γ "m6_hdr_add_ticks" [i64, i64] [] args m Q X)
    (hQ : S13HQ isBeyond c F0 F_cur ext0 s ignore_ref R Q)
    (hcfg : FullM6HdrCfgOk c) (hext1 : M6HdrExtOk ext1)
    (hw2b1 : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1)
    (hag : AgreesExcept fidCoreMask s.core st.core)
    (hsc : S13Scr s st) (hlen : st.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur st.core)
    (htr : FullTrailExt s.core st.core) (hperm : FullArenaPermEq s.core st.core)
    (hd0 : c.delayed_cap = 0 → st.scratch.delayed = s.scratch.delayed)
    (hpr_lt : s.core.propagated < s.core.trail_end)
    (hfuel : st.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hr : if isBeyond then (r = 0#64 ∨ r = 2#64) else (r = 0#64 ∨ r = 1#64 ∨ r = 2#64))
    (hbcf : isBeyond = true → S13ConflEq s.core st.core)
    (hr0 : r = 0#64 → st.core.propagated = st.core.trail_end ∧
      (isBeyond = false → st.core.confl_type = s.core.confl_type) ∧
      (s.core.oom = 0#64 → st.core.oom = 0#64) ∧
      (s.core.propagated < s.core.trail_end → st.core.fuel.toNat < s.core.fuel.toNat))
    (hr1 : isBeyond = false → r = 1#64 →
      st.core.fuel.toNat < s.core.fuel.toNat ∧ st.core.oom = 0#64 ∧
      FullPropDecSpecs.FullConflOkW F_cur st.core ∧
      (st.core.confl_type = 2#64 → st.core.confl_ref ≠ ignore_ref))
    (hr2 : r = 2#64 → st.core.oom ≠ 0#64 ∨ st.core.fuel = 0#64)
    (hm : (FullM6HdrMem c ext1 st ⋆ R) m) :
    wp Γ Q X (s13PostTicksExpr c.hdr tk_b r) m := by
  unfold s13PostTicksExpr
  refine wp_join_group (fun _ m2 => ∃ (ext2 : List (BitVec 64)) (st2 : FullState),
      M6HdrExtOk ext2 ∧ (M6HdrExtInitOk ext0 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext0 ext2) ∧
      st2.core = st.core ∧ st2.LengthsOk c ∧
      FullProbeScratchPres { s with scratch := { s.scratch with
        search_ticks := st2.scratch.search_ticks, wsort := st2.scratch.wsort,
        phases := st2.scratch.phases, delayed := st2.scratch.delayed } } st2 ∧
      st2.scratch.red_refs = s.scratch.red_refs ∧ st2.scratch.delayed_len = s.scratch.delayed_len ∧
      (s.core.probing = 0#64 → st2.scratch = { s.scratch with
        search_ticks := st2.scratch.search_ticks, wsort := st2.scratch.wsort,
        phases := st2.scratch.phases, delayed := st2.scratch.delayed }) ∧
      (c.delayed_cap = 0 → st2.scratch.delayed = s.scratch.delayed) ∧
      (FullM6HdrMem c ext2 st2 ⋆ R) m2) ?_ ?_
  · rintro _ ⟨⟩ m2 ⟨ext2, st2, hext2, hw2b2, hcore2, hlen2, hpres2, hred2, hdlen2,
      hnp2, hd0_2, hm2⟩
    s13_hsteps
    exact s13_exit_hQ hQ hext2 hw2b2 (hcore2 ▸ hag) hpres2 hred2 hdlen2 hnp2 hlen2
      (hcore2 ▸ hw) (hcore2 ▸ htr) (hcore2 ▸ hperm) hd0_2 (by rw [hcore2]; exact hfuel) hr
      (fun hb => by rw [hcore2]; exact hbcf hb) (fun h => by rw [hcore2]; exact hr0 h)
      (fun hb h => by rw [hcore2]; exact hr1 hb h) (fun h => by rw [hcore2]; exact hr2 h)
      (fun h => absurd h (Nat.ne_of_lt hpr_lt)) hm2
  · intro Jt hJt
    rw [fullM6HdrMem_iff] at hm; s13_hsteps_nogrp; s13_hsplit
    · have hm_hdr : (FullM6HdrMem c ext1 st ⋆ R) m := (fullM6HdrMem_iff ..).mpr hm
      c0_call hAddTicks
      refine step13AddTicksSpec_of rfl hcfg hext1 hlen hm_hdr
        fun _ ext2 st2 m2 hcore2 hlen2 hpres2 hred2_in hdlen2_in hext2 hw2b2 hm2 => ?_
      have hpres_s := s13_probePres_of_step hsc hpres2.probePres
      have hprob_ne : s.core.probing ≠ 0#64 := by
        have hpr_st : st.core.probing = s.core.probing := hag.get FullCoreState.probing
        rw [← hpr_st]; exact hc
      have hred2 : st2.scratch.red_refs = s.scratch.red_refs := hred2_in.trans (by rw [hsc])
      have hdlen2 : st2.scratch.delayed_len = s.scratch.delayed_len := hdlen2_in.trans (by rw [hsc])
      have hdel2 : c.delayed_cap = 0 → st2.scratch.delayed = s.scratch.delayed := fun h0 =>
        ((List.eq_nil_of_length_eq_zero
          (by simpa only [h0] using hlen2.scratch_ok.delayed_len_arr)).trans
          (List.eq_nil_of_length_eq_zero
            (by simpa only [h0] using hlen.scratch_ok.delayed_len_arr)).symm).trans (hd0 h0)
      exact hJt () m2 ⟨ext2, st2, hext2,
        fun hi => let ⟨h1, h2⟩ := hw2b1 hi; let ⟨h3, h4⟩ := hw2b2 h1; ⟨h3, h2.trans h4⟩,
        hcore2, hlen2, hpres_s, hred2, hdlen2, fun h0 => absurd h0 hprob_ne, hdel2, hm2⟩
    · s13_hsteps
      let st2 : FullState :=
        { st with scratch := { st.scratch with search_ticks := st.scratch.search_ticks + tk_b } }
      have hsc2 : S13Scr s st2 := by unfold S13Scr at hsc ⊢; dsimp only [st2]; rw [hsc]
      exact hJt () _ ⟨ext1, st2, hext1, hw2b1, rfl, ⟨hlen.core_ok, { hlen.scratch_ok with }⟩,
        s13_probePres_of_S13Scr hsc2, by rw [hsc2], by rw [hsc2], fun _ => hsc2, hd0,
        (fullM6HdrMem_iff ..).mpr (by assumption)⟩

theorem s13_outer_flush_ret {Γ : Env} {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext0 ext1 : List (BitVec 64)} {s sem : FullState}
    {ignore_ref prop_v tend_v fuel_v unass_v unfl_v tk_b r : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    (hAddTicks : ∀ args m Q X, step13AddTicksSpec args m Q X →
      Γ "m6_hdr_add_ticks" [i64, i64] [] args m Q X)
    (hQ : S13HQ isBeyond c F0 F_cur ext0 s ignore_ref R Q)
    (hcfg : FullM6HdrCfgOk c) (hext1 : M6HdrExtOk ext1)
    (hw2b1 : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1)
    (hlen_o : sem.LengthsOk c) (hw_o : FullWitnessInv c F0 F_cur sem.core)
    (htr_o : FullTrailExt s.core sem.core) (hperm_o : FullArenaPermEq s.core sem.core)
    (hag_o : AgreesExcept fidCoreMask s.core sem.core) (hsc_o : S13Scr s sem)
    (hd0_o : c.delayed_cap = 0 → sem.scratch.delayed = s.scratch.delayed)
    (hprop_eq : sem.core.propagated = prop_v.toNat) (htend_eq : sem.core.trail_end = tend_v.toNat)
    (hfuel_eq : sem.core.fuel = fuel_v) (hunass_eq : sem.core.unassigned = unass_v)
    (hunfl_eq : sem.core.unflushed = unfl_v)
    (hfuel_le : sem.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hpr_lt : s.core.propagated < s.core.trail_end)
    (hr : if isBeyond then (r = 0#64 ∨ r = 2#64) else (r = 0#64 ∨ r = 1#64 ∨ r = 2#64))
    (hbcf : isBeyond = true → S13ConflEq s.core sem.core)
    (hr0 : r = 0#64 → prop_v.toNat = tend_v.toNat ∧
      (isBeyond = false → sem.core.confl_type = s.core.confl_type) ∧
      (s.core.oom = 0#64 → sem.core.oom = 0#64) ∧
      (s.core.propagated < s.core.trail_end → sem.core.fuel.toNat < s.core.fuel.toNat))
    (hr1 : isBeyond = false → r ≠ 1#64)
    (hr2 : r = 2#64 → sem.core.oom ≠ 0#64 ∨ sem.core.fuel = 0#64)
    (hm : (FullM6HdrMem c ext1
      { sem with core := { sem.core with
        fuel := fuel_v, propagated := prop_v.toNat, trail_end := tend_v.toNat,
        unassigned := unass_v, unflushed := unfl_v } } ⋆ R) m) :
    wp Γ Q X (s13PostTicksExpr c.hdr tk_b r) m := by
  let sem_fin : FullState :=
    { sem with core := { sem.core with
      fuel := fuel_v, propagated := prop_v.toNat, trail_end := tend_v.toNat,
      unassigned := unass_v, unflushed := unfl_v } }
  have hfin_core : sem_fin.core = sem.core := by
    dsimp only [sem_fin]; rw [← hfuel_eq, ← hprop_eq, ← htend_eq, ← hunass_eq, ← hunfl_eq]
  have hfin_state : sem_fin = sem := by
    cases sem; dsimp only [sem_fin] at hfin_core ⊢; congr 1
  exact s13_post_ticks_wp hAddTicks hQ hcfg hext1 hw2b1 hag_o
    hsc_o hlen_o hw_o htr_o hperm_o hd0_o hpr_lt hfuel_le hr hbcf
    (by simpa only [← hprop_eq, ← htend_eq] using hr0)
    (fun hb h => absurd h (hr1 hb)) hr2 (hfin_state ▸ hm)

theorem s13_post_exit_brk2 {Γ : Env} {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext0 ext1 : List (BitVec 64)} {s st_c : FullState}
    {ignore_ref te_b un_b uf_b prop_v fuel1 tk_b ticks_fin : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    (hAddTicks : ∀ args m Q X, step13AddTicksSpec args m Q X →
      Γ "m6_hdr_add_ticks" [i64, i64] [] args m Q X)
    (hQ : S13HQ isBeyond c F0 F_cur ext0 s ignore_ref R Q)
    (hcfg : FullM6HdrCfgOk c) (hext1 : M6HdrExtOk ext1)
    (hw2b1 : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1)
    (hlen_c : st_c.LengthsOk c) (hwf_c : FullWitnessInv c F0 F_cur st_c.core)
    (htr_s_c : FullTrailExt s.core st_c.core) (hperm_s_c : FullArenaPermEq s.core st_c.core)
    (hag_sc : AgreesExcept fidCoreMask s.core st_c.core) (hdm_c : st_c.core.dense_mode = 0#64)
    (hfuel1 : fuel1.toNat ≤ s.core.fuel.toNat) (hsc_c : S13Scr s st_c)
    (hbcf_c : isBeyond = true → S13ConflEq s.core st_c.core)
    (hd0_c : c.delayed_cap = 0 → st_c.scratch.delayed = s.scratch.delayed)
    (hte_c_eq : te_b.toNat = st_c.core.trail_end)
    (hpr_lt : s.core.propagated < s.core.trail_end) (hpr_lt_teb : prop_v.toNat + 1 ≤ te_b.toNat)
    (hm : (FullM6HdrMem c ext1 { st_c with
      core := { st_c.core with
        oom := 1#64, fuel := fuel1, propagated := prop_v.toNat + 1,
        trail_end := te_b.toNat, unassigned := un_b, unflushed := uf_b }
      scratch := { st_c.scratch with search_ticks := ticks_fin } } ⋆ R) m) :
    wp Γ Q X (s13PostTicksExpr c.hdr tk_b 2#64) m := by
  let st_fin2 : FullState :=
    { st_c with
      core := { st_c.core with
        oom := 1#64, fuel := fuel1, propagated := prop_v.toNat + 1,
        trail_end := te_b.toNat, unassigned := un_b, unflushed := uf_b }
      scratch := { st_c.scratch with search_ticks := ticks_fin } }
  have hlen_f2 : st_fin2.LengthsOk c :=
    ⟨{ hlen_c.core_ok with
        trail_end_le := by dsimp only [st_fin2]; rw [hte_c_eq]; exact hlen_c.core_ok.trail_end_le
        propagated_le := hpr_lt_teb },
     { hlen_c.scratch_ok with }⟩
  have hwf_f2 : FullWitnessInv c F0 F_cur st_fin2.core := by
    have hnw := fullWitnessInv_nw_congr hlen_f2.core_ok.cur_vars_le
      (fullWitnessInv_to_nw hlen_c.core_ok.cur_vars_le hwf_c)
      rfl rfl rfl rfl hte_c_eq rfl rfl rfl rfl rfl rfl rfl rfl
    have hwat_f2 : WatchesInv F_cur st_fin2.core := by
      have hw_sp : ModeWatchesInv F_cur st_fin2.core :=
        hwf_c.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
      simpa only [ModeWatchesInv, st_fin2, hdm_c, ↓reduceIte] using hw_sp
    exact fullWitnessInv_of_nw hnw hdm_c hwat_f2
  exact s13_post_ticks_wp (st := st_fin2) hAddTicks hQ hcfg hext1 hw2b1
    (hag_sc.update (fun k => { k with
      oom := 1#64, fuel := fuel1, propagated := prop_v.toNat + 1,
      trail_end := te_b.toNat, unassigned := un_b, unflushed := uf_b }))
    (by unfold S13Scr at hsc_c ⊢; dsimp only [st_fin2]; rw [hsc_c])
    hlen_f2 hwf_f2
    ⟨by simpa [st_fin2, hte_c_eq] using htr_s_c.1,
     by simpa [st_fin2, hte_c_eq] using htr_s_c.2.1,
     by simpa [st_fin2, hte_c_eq] using htr_s_c.2.2⟩
    ⟨hperm_s_c.1, hperm_s_c.2.1, fun r hr => hperm_s_c.2.2 r hr⟩ hd0_c hpr_lt hfuel1
    (by cases isBeyond <;> simp) (fun hb => by simp only [st_fin2]; exact hbcf_c hb)
    (fun h => absurd h (by decide))
    (fun _ h => absurd h (by decide)) (fun _ => Or.inl (by simp [st_fin2])) hm

theorem s13_post_exit_brk1 {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext0 ext1 : List (BitVec 64)} {s st_c : FullState}
    {ignore_ref te_b un_b uf_b prop_v fuel1 tk_b ticks_fin : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    (hAddTicks : ∀ args m Q X, step13AddTicksSpec args m Q X →
      Γ "m6_hdr_add_ticks" [i64, i64] [] args m Q X)
    (hQ : S13HQ false c F0 F_cur ext0 s ignore_ref R Q)
    (hcfg : FullM6HdrCfgOk c) (hext1 : M6HdrExtOk ext1)
    (hw2b1 : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1)
    (hlen_c : st_c.LengthsOk c) (hwf_c : FullWitnessInv c F0 F_cur st_c.core)
    (htr_s_c : FullTrailExt s.core st_c.core) (hperm_s_c : FullArenaPermEq s.core st_c.core)
    (hag_sc : AgreesExcept fidCoreMask s.core st_c.core) (hdm_c : st_c.core.dense_mode = 0#64)
    (hfuel_lt : fuel1.toNat < s.core.fuel.toNat) (hoom_c : st_c.core.oom = 0#64)
    (hconfl_w : FullPropDecSpecs.FullConflOkW F_cur st_c.core)
    (hc2_ign : st_c.core.confl_type = 2#64 → st_c.core.confl_ref ≠ ignore_ref)
    (hsc_c : S13Scr s st_c) (hd0_c : c.delayed_cap = 0 → st_c.scratch.delayed = s.scratch.delayed)
    (hte_c_eq : te_b.toNat = st_c.core.trail_end)
    (hpr_lt : s.core.propagated < s.core.trail_end) (hpr_lt_teb : prop_v.toNat + 1 ≤ te_b.toNat)
    (hm : (FullM6HdrMem c ext1 { st_c with
      core := { st_c.core with
        fuel := fuel1, propagated := prop_v.toNat + 1, trail_end := te_b.toNat,
        unassigned := un_b, unflushed := uf_b }
      scratch := { st_c.scratch with search_ticks := ticks_fin } } ⋆ R) m) :
    wp Γ Q X (s13PostTicksExpr c.hdr tk_b 1#64) m := by
  let st_fin1 : FullState :=
    { st_c with
      core := { st_c.core with
        fuel := fuel1, propagated := prop_v.toNat + 1, trail_end := te_b.toNat,
        unassigned := un_b, unflushed := uf_b }
      scratch := { st_c.scratch with search_ticks := ticks_fin } }
  have hlen_f1 : st_fin1.LengthsOk c :=
    ⟨{ hlen_c.core_ok with
        trail_end_le := by dsimp only [st_fin1]; rw [hte_c_eq]; exact hlen_c.core_ok.trail_end_le
        propagated_le := hpr_lt_teb },
     { hlen_c.scratch_ok with }⟩
  have hwf_f1 : FullWitnessInv c F0 F_cur st_fin1.core := by
    have hnw := fullWitnessInv_nw_congr hlen_f1.core_ok.cur_vars_le
      (fullWitnessInv_to_nw hlen_c.core_ok.cur_vars_le hwf_c)
      rfl rfl rfl rfl hte_c_eq rfl rfl rfl rfl rfl rfl rfl rfl
    have hwat_f1 : WatchesInv F_cur st_fin1.core := by
      have hw_sp : ModeWatchesInv F_cur st_fin1.core :=
        hwf_c.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
      simpa only [ModeWatchesInv, st_fin1, hdm_c, ↓reduceIte] using hw_sp
    exact fullWitnessInv_of_nw hnw hdm_c hwat_f1
  have hconfl_f1 : FullPropDecSpecs.FullConflOkW F_cur st_fin1.core :=
    m7_fullConflOkW_of_perm
      (m7_arenaPermEq_congr rfl rfl rfl rfl (.refl st_c.core))
      rfl rfl rfl rfl rfl rfl hconfl_w
  exact s13_post_ticks_wp (st := st_fin1) hAddTicks hQ hcfg hext1 hw2b1
    (hag_sc.update (fun k => { k with
      fuel := fuel1, propagated := prop_v.toNat + 1, trail_end := te_b.toNat,
      unassigned := un_b, unflushed := uf_b }))
    (by unfold S13Scr at hsc_c ⊢; dsimp only [st_fin1]; rw [hsc_c])
    hlen_f1 hwf_f1
    ⟨by simpa [st_fin1, hte_c_eq] using htr_s_c.1,
     by simpa [st_fin1, hte_c_eq] using htr_s_c.2.1,
     by simpa [st_fin1, hte_c_eq] using htr_s_c.2.2⟩
    ⟨hperm_s_c.1, hperm_s_c.2.1, fun r hr => hperm_s_c.2.2 r hr⟩ hd0_c hpr_lt
    (Nat.le_of_lt hfuel_lt) (Or.inr (Or.inl rfl)) (fun h => absurd h (by decide))
    (fun h => absurd h (by decide))
    (fun _ _ => ⟨hfuel_lt, by simp [st_fin1, hoom_c], hconfl_f1,
      fun h2 => by simpa [st_fin1] using hc2_ign h2⟩)
    (fun h => absurd h (by decide)) hm

/-! ## 4. Post-Compaction Break/Continue, Final Flush & Compaction -/

theorem s13_post_brk_cont_wp {Γ : Env} {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext0 ext1 : List (BitVec 64)}
    {s sem s_base s_disk sem_b st_c : FullState}
    {ignore_ref prop_v fuel1 te_b un_b uf_b tk_b brk_c : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mc0 : Mem 64}
    {J_out : Cont [i64, i64, i64, i64, i64, i64]}
    (hAddTicks : ∀ args m Q X, step13AddTicksSpec args m Q X →
      Γ "m6_hdr_add_ticks" [i64, i64] [] args m Q X)
    (hQ : S13HQ isBeyond c F0 F_cur ext0 s ignore_ref R Q)
    (hJ_out : ∀ (sem_next : FullState) (te_mc : Nat) (mc0 : Mem 64),
      sem_next.LengthsOk c → FullWitnessInv c F0 F_cur sem_next.core →
      FullTrailExt s.core sem_next.core → FullArenaPermEq s.core sem_next.core →
      AgreesExcept fidCoreMask s.core sem_next.core →
      sem_next.core.propagated = (prop_v + 1#64).toNat →
      sem_next.core.fuel = fuel1 → sem_next.core.trail_end = te_b.toNat →
      sem_next.core.unassigned = un_b → sem_next.core.unflushed = uf_b →
      sem_next.core.oom = 0#64 →
      (isBeyond = false → sem_next.core.confl_type = s.core.confl_type) →
      (isBeyond = true → S13ConflEq s.core sem_next.core) →
      sem_next.core.dense_mode = 0#64 → sem_next.core.cur_vars = s.core.cur_vars →
      sem_next.core.cur_level = s.core.cur_level → sem_next.core.probing = s.core.probing →
      sem_next.core.arena_len = s.core.arena_len →
      sem_next.core.fuel.toNat < sem.core.fuel.toNat →
      sem_next.core.fuel.toNat < s.core.fuel.toNat →
      sem_next.core.fuel.toNat ≤ s.core.fuel.toNat →
      s.core.propagated ≤ sem_next.core.propagated → te_mc ≤ sem_next.core.trail_end →
      s.core.propagated ≤ te_mc → S13Scr s sem_next →
      (c.delayed_cap = 0 → sem_next.scratch.delayed = s.scratch.delayed) →
      (FullM6HdrMem c ext1 (fastPropMem { s with core := { s.core with trail_end := te_mc } }
        { sem_next with core :=
          { sem_next.core with propagated := s.core.propagated, fuel := s.core.fuel } }) ⋆ R) mc0 →
      wp Γ Q X (Expr.jump J_out (.var (prop_v + 1#64), (.var te_b, (.var fuel1, (.var un_b,
        (.var uf_b, (.var tk_b, ()))))))) mc0)
    (hcfg : FullM6HdrCfgOk c) (hext1 : M6HdrExtOk ext1)
    (hw2b1 : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1)
    (hlen0 : s.LengthsOk c) (hpr_lt : s.core.propagated < s.core.trail_end)
    (hs_base : s_base = { sem with core := { sem.core with
      propagated := s.core.propagated, fuel := s.core.fuel } })
    (hfuel1 : fuel1 = sem.core.fuel - 1#64)
    (hs_disk : ∃ te_mem, s_disk = { s with core := { s.core with trail_end := te_mem } } ∧
      te_mem ≤ sem.core.trail_end ∧ s.core.propagated ≤ te_mem)
    (htr_o : FullTrailExt s.core sem.core) (hperm_o : FullArenaPermEq s.core sem.core)
    (hag_o : AgreesExcept fidCoreMask s.core sem.core)
    (hcv_o : sem.core.cur_vars = s.core.cur_vars)
    (hcl_o : sem.core.cur_level = s.core.cur_level)
    (hprob_o : sem.core.probing = s.core.probing) (halen_o : sem.core.arena_len = s.core.arena_len)
    (_hsc_o : S13Scr s sem)
    (hfl_rem_dec : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat)
    (hfuel_le : sem.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hp1_prop : (prop_v + 1#64).toNat = prop_v.toNat + 1)
    (hp_lt_o : prop_v.toNat < sem.core.trail_end) (_hpr_ge : s.core.propagated ≤ prop_v.toNat)
    (_hpi_b_len : sem_b.LengthsOk c) (hpi_b_cv : sem_b.core.cur_vars = s_base.core.cur_vars)
    (hpi_b_tr : FullPropDecSpecs.FullTrailExt s_base.core sem_b.core)
    (hdense_b : s_base.core.dense_mode = 0#64) (hte_b : te_b.toNat = sem_b.core.trail_end)
    (hun_b : un_b = sem_b.core.unassigned) (huf_b : uf_b = sem_b.core.unflushed)
    (hbr0 : brk_c = 0#64 → sem_b.core.oom = 0#64 ∧
      (isBeyond = false → sem_b.core.confl_type = s.core.confl_type))
    (hbr_cf : isBeyond = true → S13ConflEq s.core sem_b.core)
    (hbr1 : brk_c = 1#64 → isBeyond = false ∧ PropLitConfl F_cur ignore_ref sem_b.core ∧
      sem_b.core.oom = 0#64)
    (hbr_cases : if isBeyond then (brk_c = 0#64 ∨ brk_c = 2#64)
      else (brk_c = 0#64 ∨ brk_c = 1#64 ∨ brk_c = 2#64))
    (hlen_c : st_c.LengthsOk c) (hwf_c : FullWitnessInv c F0 F_cur st_c.core)
    (hag_l : AgreesExcept propLitCoreMask s_base.core st_c.core)
    (htr_l : FullPropDecSpecs.FullTrailExt s_base.core st_c.core)
    (hperm_l : FullPropDecSpecs.FullArenaPermEq s_base.core st_c.core)
    (hoom_c : st_c.core.oom = sem_b.core.oom)
    (hct_c : st_c.core.confl_type = sem_b.core.confl_type)
    (hcr_c : st_c.core.confl_ref = sem_b.core.confl_ref)
    (hc0_c : st_c.core.confl_lit0 = sem_b.core.confl_lit0)
    (hc1_c : st_c.core.confl_lit1 = sem_b.core.confl_lit1)
    (hcv_c : st_c.core.cur_vars = sem_b.core.cur_vars)
    (hvals_c : st_c.core.vals = sem_b.core.vals)
    (hte_c : st_c.core.trail_end = sem_b.core.trail_end)
    (hun_c : st_c.core.unassigned = sem_b.core.unassigned)
    (huf_c : st_c.core.unflushed = sem_b.core.unflushed)
    (halen_c : st_c.core.arena_len = sem_b.core.arena_len)
    (hcl_c : st_c.core.cur_level = sem_b.core.cur_level)
    (har_c : st_c.core.arena = sem_b.core.arena) (hsc_c : S13Scr s st_c)
    (hd0_c : c.delayed_cap = 0 → st_c.scratch.delayed = s.scratch.delayed)
    (hmc0 : (FullMem c (fastPropMem s_disk st_c) ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mc0) :
    wp Γ Q X (s13PostBrkContExpr J_out c.hdr prop_v fuel1 te_b un_b uf_b tk_b brk_c) mc0 := by
  obtain ⟨te_mem, rfl, htem_le, hpr_tem⟩ := hs_disk
  have hte_sem_le : sem.core.trail_end ≤ sem_b.core.trail_end := by
    have := hpi_b_tr.te_ge; rw [hs_base] at this; exact this
  have hpr_lt_teb : prop_v.toNat + 1 ≤ te_b.toNat := by
    rw [hte_b]; exact Nat.le_trans hp_lt_o hte_sem_le
  have hfuel1_lt : fuel1.toNat < s.core.fuel.toNat := by
    rw [hfuel1]; exact Nat.lt_of_lt_of_le hfl_rem_dec hfuel_le
  have hag_base : AgreesExcept fidCoreMask s.core s_base.core := by
    unfold AgreesExcept fidCoreMask at hag_o ⊢; rw [hs_base]; exact hag_o
  have hag_sc : AgreesExcept fidCoreMask s.core st_c.core :=
    hag_base.trans_mono hag_l (fun _ => rfl) (fun _ => rfl)
  have hdm_c : st_c.core.dense_mode = 0#64 :=
    (hag_l.get FullCoreState.dense_mode).trans hdense_b
  have hpr_c : st_c.core.propagated = s.core.propagated := by
    simpa [hs_base] using hag_l.get FullCoreState.propagated
  have hfuel_cs : st_c.core.fuel = s.core.fuel := by
    rw [hag_l.get FullCoreState.fuel, hs_base]
  have hprob_c : st_c.core.probing = s.core.probing := by
    rw [hag_l.get FullCoreState.probing, hs_base]; exact hprob_o
  have htemc_le : te_mem ≤ st_c.core.trail_end := hte_c ▸ Nat.le_trans htem_le hte_sem_le
  let s_dmc : FullState := { s with core := { s.core with trail_end := te_mem } }
  have hsdmc_len : s_dmc.LengthsOk c :=
    ⟨{ hlen0.core_ok with
        trail_end_le := by
          dsimp only [s_dmc]
          rw [← hcv_o, show sem.core.cur_vars = st_c.core.cur_vars from by
            rw [hcv_c, hpi_b_cv, hs_base]]
          exact Nat.le_trans htemc_le hlen_c.core_ok.trail_end_le
        propagated_le := hpr_tem }, hlen0.scratch_ok⟩
  have hmem_c_len' := fastPropMem_lengthsOk hsdmc_len hlen_c
    (by simpa [s_dmc, hcv_c, hpi_b_cv, hs_base] using hcv_o) (by simp [s_dmc, hpr_c]) rfl
  have hte_c_eq : te_b.toNat = st_c.core.trail_end := hte_b.trans hte_c.symm
  have hun_c_eq : un_b = st_c.core.unassigned := hun_b.trans hun_c.symm
  have huf_c_eq : uf_b = st_c.core.unflushed := huf_b.trans huf_c.symm
  have htr_c' : FullTrailExt sem.core st_c.core := by
    rw [hs_base] at htr_l; exact ⟨htr_l.te_ge, htr_l.trl_pref, htr_l.lvl_pres⟩
  have htr_s_c : FullTrailExt s.core st_c.core :=
    ⟨Nat.le_trans htr_o.1 htr_c'.1,
     fun i hi => (htr_c'.2.1 i (Nat.lt_of_lt_of_le hi htr_o.1)).trans (htr_o.2.1 i hi),
     fun i hi => by
       have h1 := htr_o.2.2 i hi
       have h2 := htr_c'.2.2 i (Nat.lt_of_lt_of_le hi htr_o.1)
       have htrl := htr_o.2.1 i hi
       have ht1 : st_c.core.trl[i]?.getD 0#32 = s.core.trl[i]?.getD 0#32 := by
         rw [htr_c'.2.1 i (Nat.lt_of_lt_of_le hi htr_o.1), htrl]
       have htl' : sem.core.trl[i]?.getD 0#32 = s.core.trl[i]?.getD 0#32 := by rw [htrl]
       rw [htl'] at h2; exact h2.trans h1⟩
  have hperm_c' : FullArenaPermEq sem.core st_c.core := by
    rw [hs_base] at hperm_l
    exact ⟨by rw [hag_l.get FullCoreState.arena_len, hs_base], hperm_l.1,
      fun r hr => hperm_l.2 r hr⟩
  have hperm_s_c : FullArenaPermEq s.core st_c.core :=
    ⟨hperm_c'.1.trans hperm_o.1, hperm_c'.2.1.trans hperm_o.2.1, fun r hr => by
      have h1 := hperm_o.2.2 r hr
      have h2 := hperm_c'.2.2 r (hperm_o.2.1 ▸ hr)
      exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩⟩
  have hperm_bc : FullPropDecSpecs.FullArenaPermEq sem_b.core st_c.core :=
    m7_arenaPermEq_congr rfl rfl har_c halen_c (.refl sem_b.core)
  unfold s13PostBrkContExpr
  s13_hsplit
  · have hbrk_ne0 : brk_c ≠ 0#64 := hc
    clear hc
    refine wp_unroll_group fun Js_brk hJs_brk => ?_
    s13_hsplit
    · subst hc; s13_hsteps
      exact s13_post_exit_brk2 hAddTicks hQ hcfg hext1 hw2b1 hlen_c hwf_c htr_s_c hperm_s_c
        hag_sc hdm_c (Nat.le_of_lt hfuel1_lt) hsc_c
        (fun hb => by
          have ⟨h1, h2, h3, h4⟩ := hbr_cf hb
          exact ⟨hct_c.trans h1, hcr_c.trans h2, hc0_c.trans h3, hc1_c.trans h4⟩)
        hd0_c hte_c_eq hpr_lt hpr_lt_teb
        (fullM6HdrMem_unfocus_full (by
          simpa only [fastPropMem, s_dmc, hp1_prop, hte_c_eq, BitVec.ofNat_eq_ofNat] using hm))
    · have hbrk1 : isBeyond = false ∧ brk_c = 1#64 := by
        cases isBeyond
        · rcases hbr_cases with rfl | rfl | rfl
          · exact absurd rfl hbrk_ne0
          · exact ⟨rfl, rfl⟩
          · exact absurd rfl hc
        · rcases hbr_cases with rfl | rfl
          · exact absurd rfl hbrk_ne0
          · exact absurd rfl hc
      obtain ⟨rfl, rfl⟩ := hbrk1
      have ⟨_, hconfl_c, hoom_b⟩ := hbr1 rfl
      have hoom_c : st_c.core.oom = 0#64 := hoom_c.trans hoom_b
      have hconfl_w : FullPropDecSpecs.FullConflOkW F_cur st_c.core := by
        rcases hconfl_c with hne0 | hok
        · exact absurd hoom_b hne0
        · exact m7_fullConflOkW_of_perm hperm_bc hcv_c hvals_c hct_c hcr_c hc0_c hc1_c hok.1
      have hc2_ign : st_c.core.confl_type = 2#64 → st_c.core.confl_ref ≠ ignore_ref := by
        rcases hconfl_c with hne0 | hok
        · exact absurd hoom_b hne0
        · intro h2; rw [hct_c] at h2; simpa [hcr_c] using hok.2 h2
      s13_hsteps
      exact s13_post_exit_brk1 hAddTicks hQ hcfg hext1 hw2b1 hlen_c hwf_c htr_s_c hperm_s_c
        hag_sc hdm_c hfuel1_lt hoom_c hconfl_w hc2_ign hsc_c hd0_c hte_c_eq hpr_lt hpr_lt_teb
        (fullM6HdrMem_unfocus_full (by
          simpa only [fastPropMem, s_dmc, hp1_prop, hte_c_eq, BitVec.ofNat_eq_ofNat] using hm))
  · have ⟨hoom_b0, hct_b0⟩ := hbr0 hc
    have hoom_c0 : st_c.core.oom = 0#64 := hoom_c.trans hoom_b0
    s13_hsteps
    let sem_next : FullState :=
      { st_c with core := { st_c.core with propagated := prop_v.toNat + 1, fuel := fuel1 } }
    have hlen_next : sem_next.LengthsOk c :=
      ⟨{ hlen_c.core_ok with propagated_le := by rw [← hte_c_eq]; exact hpr_lt_teb },
       hlen_c.scratch_ok⟩
    have hwf_next : FullWitnessInv c F0 F_cur sem_next.core := by
      have hnw := fullWitnessInv_nw_congr hlen_next.core_ok.cur_vars_le
        (fullWitnessInv_to_nw hlen_c.core_ok.cur_vars_le hwf_c)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      have hwat_next : WatchesInv F_cur sem_next.core := by
        have hw_sp : ModeWatchesInv F_cur sem_next.core :=
          hwf_c.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
        simpa only [ModeWatchesInv, sem_next, hdm_c, ↓reduceIte] using hw_sp
      exact fullWitnessInv_of_nw hnw hdm_c hwat_next
    have hcl_sb : sem_b.core.cur_level = s.core.cur_level := by
      have h1 : st_c.core.cur_level = s_base.core.cur_level := hag_l.get FullCoreState.cur_level
      rw [← hcl_c, h1, hs_base]; exact hcl_o
    have halen_sb : sem_b.core.arena_len = s.core.arena_len := by
      have h1 : st_c.core.arena_len = s_base.core.arena_len := hag_l.get FullCoreState.arena_len
      rw [← halen_c, h1, hs_base]; exact halen_o
    exact hJ_out sem_next te_mem mc0 hlen_next hwf_next
      ⟨by simpa [sem_next] using htr_s_c.1,
       by simpa [sem_next] using htr_s_c.2.1,
       by simpa [sem_next] using htr_s_c.2.2⟩
      ⟨hperm_s_c.1, hperm_s_c.2.1, fun r hr => hperm_s_c.2.2 r hr⟩
      (hag_sc.update (fun k => { k with propagated := prop_v.toNat + 1, fuel := fuel1 }))
      (by simp [sem_next, hp1_prop]) rfl hte_c_eq.symm hun_c_eq.symm huf_c_eq.symm
      (by simp [sem_next, hoom_c0])
      (fun hb => by simp only [sem_next]; exact hct_c.trans (hct_b0 hb))
      (fun hb => by
        simp only [sem_next]
        have ⟨h1, h2, h3, h4⟩ := hbr_cf hb
        exact ⟨hct_c.trans h1, hcr_c.trans h2, hc0_c.trans h3, hc1_c.trans h4⟩)
      hdm_c
      (by rw [hcv_c, hpi_b_cv, hs_base]; exact hcv_o)
      (by rw [hcl_c]; exact hcl_sb) hprob_c (by rw [halen_c]; exact halen_sb)
      (by dsimp only [sem_next]; rw [hfuel1]; exact hfl_rem_dec)
      hfuel1_lt (Nat.le_of_lt hfuel1_lt) (by simp [sem_next]; omega) htemc_le hpr_tem
      (by unfold S13Scr at hsc_c ⊢; exact hsc_c) hd0_c
      (fullM6HdrMem_unfocus_full (by simpa [sem_next, fastPropMem, hpr_c, hfuel_cs] using hmc0))

theorem s13_post_flush_wp {Γ : Env} {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext0 ext1 : List (BitVec 64)}
    {s sem s_base s_disk sem_b st_fin : FullState}
    {ignore_ref prop_v fuel1 te_b un_b uf_b tk_b di_b brk_b : BitVec 64}
    {not_lit : BitVec 32} {dlen_b : Nat}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mf : Mem 64}
    {J_out : Cont [i64, i64, i64, i64, i64, i64]}
    (hFlush : ∀ args m Q X, fidPropFlushDelSpec args m Q X →
      Γ "full_prop_flush_del_fid" [i64, i64] [.bool] args m Q X)
    (hAddTicks : ∀ args m Q X, step13AddTicksSpec args m Q X →
      Γ "m6_hdr_add_ticks" [i64, i64] [] args m Q X)
    (hQ : S13HQ isBeyond c F0 F_cur ext0 s ignore_ref R Q)
    (hJ_out : ∀ (sem_next : FullState) (te_mc : Nat) (mc0 : Mem 64),
      sem_next.LengthsOk c → FullWitnessInv c F0 F_cur sem_next.core →
      FullTrailExt s.core sem_next.core → FullArenaPermEq s.core sem_next.core →
      AgreesExcept fidCoreMask s.core sem_next.core →
      sem_next.core.propagated = (prop_v + 1#64).toNat →
      sem_next.core.fuel = fuel1 → sem_next.core.trail_end = te_b.toNat →
      sem_next.core.unassigned = un_b → sem_next.core.unflushed = uf_b →
      sem_next.core.oom = 0#64 →
      (isBeyond = false → sem_next.core.confl_type = s.core.confl_type) →
      (isBeyond = true → S13ConflEq s.core sem_next.core) →
      sem_next.core.dense_mode = 0#64 → sem_next.core.cur_vars = s.core.cur_vars →
      sem_next.core.cur_level = s.core.cur_level → sem_next.core.probing = s.core.probing →
      sem_next.core.arena_len = s.core.arena_len →
      sem_next.core.fuel.toNat < sem.core.fuel.toNat →
      sem_next.core.fuel.toNat < s.core.fuel.toNat →
      sem_next.core.fuel.toNat ≤ s.core.fuel.toNat →
      s.core.propagated ≤ sem_next.core.propagated → te_mc ≤ sem_next.core.trail_end →
      s.core.propagated ≤ te_mc → S13Scr s sem_next →
      (c.delayed_cap = 0 → sem_next.scratch.delayed = s.scratch.delayed) →
      (FullM6HdrMem c ext1 (fastPropMem { s with core := { s.core with trail_end := te_mc } }
        { sem_next with core :=
          { sem_next.core with propagated := s.core.propagated, fuel := s.core.fuel } }) ⋆ R) mc0 →
      wp Γ Q X (Expr.jump J_out (.var (prop_v + 1#64), (.var te_b, (.var fuel1, (.var un_b,
        (.var uf_b, (.var tk_b, ()))))))) mc0)
    (hcfg : FullM6HdrCfgOk c) (hext1 : M6HdrExtOk ext1)
    (hw2b1 : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1)
    (hlen0 : s.LengthsOk c) (hpr_lt : s.core.propagated < s.core.trail_end)
    (hs_base : s_base = { sem with core := { sem.core with
      propagated := s.core.propagated, fuel := s.core.fuel } })
    (hfuel1 : fuel1 = sem.core.fuel - 1#64)
    (hs_disk : ∃ te_mem, s_disk = { s with core := { s.core with trail_end := te_mem } } ∧
      te_mem ≤ sem.core.trail_end ∧ s.core.propagated ≤ te_mem)
    (htr_o : FullTrailExt s.core sem.core) (hperm_o : FullArenaPermEq s.core sem.core)
    (hag_o : AgreesExcept fidCoreMask s.core sem.core)
    (hcv_o : sem.core.cur_vars = s.core.cur_vars)
    (hcl_o : sem.core.cur_level = s.core.cur_level)
    (hprob_o : sem.core.probing = s.core.probing) (halen_o : sem.core.arena_len = s.core.arena_len)
    (_hsc_o : S13Scr s sem)
    (hfl_rem_dec : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat)
    (hfuel_le : sem.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hp1_prop : (prop_v + 1#64).toNat = prop_v.toNat + 1)
    (hp_lt_o : prop_v.toNat < sem.core.trail_end) (hpr_ge : s.core.propagated ≤ prop_v.toNat)
    (hpi_b_len : sem_b.LengthsOk c) (hpi_b_cv : sem_b.core.cur_vars = s_base.core.cur_vars)
    (hpi_b_tr : FullPropDecSpecs.FullTrailExt s_base.core sem_b.core)
    (hdense_b : s_base.core.dense_mode = 0#64) (hte_b : te_b.toNat = sem_b.core.trail_end)
    (hun_b : un_b = sem_b.core.unassigned) (huf_b : uf_b = sem_b.core.unflushed)
    (hbr0 : brk_b = 0#64 → sem_b.core.oom = 0#64 ∧
      (isBeyond = false → sem_b.core.confl_type = s.core.confl_type))
    (hbr_cf : isBeyond = true → S13ConflEq s.core sem_b.core)
    (hbr1 : brk_b = 1#64 → isBeyond = false ∧ PropLitConfl F_cur ignore_ref sem_b.core ∧
      sem_b.core.oom = 0#64)
    (hbr_cases : if isBeyond then (brk_b = 0#64 ∨ brk_b = 2#64)
      else (brk_b = 0#64 ∨ brk_b = 1#64 ∨ brk_b = 2#64))
    (hdi_b : di_b.toNat = 3 * dlen_b) (hdlen_b : dlen_b ≤ c.delayed_cap)
    (hdok_b : DelayedWatchesOk s_base.core st_fin.scratch.delayed dlen_b not_lit.toNat)
    (hlen_f : st_fin.LengthsOk c) (hwf_f : FullWitnessInv c F0 F_cur st_fin.core)
    (hag_f : AgreesExcept propLitCoreMask s_base.core st_fin.core)
    (htr_f : FullPropDecSpecs.FullTrailExt s_base.core st_fin.core)
    (hperm_f : FullPropDecSpecs.FullArenaPermEq s_base.core st_fin.core)
    (hoom_f : st_fin.core.oom = sem_b.core.oom)
    (hct_f : st_fin.core.confl_type = sem_b.core.confl_type)
    (hcr_f : st_fin.core.confl_ref = sem_b.core.confl_ref)
    (hc0_f : st_fin.core.confl_lit0 = sem_b.core.confl_lit0)
    (hc1_f : st_fin.core.confl_lit1 = sem_b.core.confl_lit1)
    (hcv_f : st_fin.core.cur_vars = sem_b.core.cur_vars)
    (hvals_f : st_fin.core.vals = sem_b.core.vals)
    (hte_f : st_fin.core.trail_end = sem_b.core.trail_end)
    (hun_f : st_fin.core.unassigned = sem_b.core.unassigned)
    (huf_f : st_fin.core.unflushed = sem_b.core.unflushed)
    (halen_f : st_fin.core.arena_len = sem_b.core.arena_len)
    (hcl_f : st_fin.core.cur_level = sem_b.core.cur_level)
    (har_f : st_fin.core.arena = sem_b.core.arena) (hscr_f : S13Scr s st_fin)
    (hd0_f : c.delayed_cap = 0 → st_fin.scratch.delayed = s.scratch.delayed)
    (hmf : (FullMem c (fastPropMem s_disk st_fin) ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mf) :
    wp Γ Q X (s13PostFlushExpr J_out c.hdr prop_v fuel1 te_b un_b uf_b tk_b di_b brk_b) mf := by
  let P : BitVec 64 → Mem 64 → Prop := fun brk_f mfl =>
    ∃ st_fl : FullState,
      st_fl.LengthsOk c ∧ FullWitnessInv c F0 F_cur st_fl.core ∧
      AgreesExcept propLitCoreMask s_base.core st_fl.core ∧
      FullPropDecSpecs.FullTrailExt s_base.core st_fl.core ∧
      FullPropDecSpecs.FullArenaPermEq s_base.core st_fl.core ∧
      st_fl.core.oom = sem_b.core.oom ∧ st_fl.core.confl_type = sem_b.core.confl_type ∧
      st_fl.core.confl_ref = sem_b.core.confl_ref ∧
      st_fl.core.confl_lit0 = sem_b.core.confl_lit0 ∧
      st_fl.core.confl_lit1 = sem_b.core.confl_lit1 ∧
      st_fl.core.cur_vars = sem_b.core.cur_vars ∧ st_fl.core.vals = sem_b.core.vals ∧
      st_fl.core.trail_end = sem_b.core.trail_end ∧
      st_fl.core.unassigned = sem_b.core.unassigned ∧
      st_fl.core.unflushed = sem_b.core.unflushed ∧
      st_fl.core.arena_len = sem_b.core.arena_len ∧
      st_fl.core.cur_level = sem_b.core.cur_level ∧ st_fl.core.arena = sem_b.core.arena ∧
      S13Scr s st_fl ∧ (c.delayed_cap = 0 → st_fl.scratch.delayed = s.scratch.delayed) ∧
      (brk_f = 0#64 → brk_b = 0#64) ∧ (brk_f = 1#64 → brk_b = 1#64) ∧
      (if isBeyond then (brk_f = 0#64 ∨ brk_f = 2#64)
        else (brk_f = 0#64 ∨ brk_f = 1#64 ∨ brk_f = 2#64)) ∧
      (FullMem c (fastPropMem s_disk st_fl) ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mfl
  have hP_fin : ∀ brk_f, (brk_f = 0#64 → brk_b = 0#64) → (brk_f = 1#64 → brk_b = 1#64) →
      (if isBeyond then (brk_f = 0#64 ∨ brk_f = 2#64)
        else (brk_f = 0#64 ∨ brk_f = 1#64 ∨ brk_f = 2#64)) → P brk_f mf := fun brk_f h0 h1 hc =>
    ⟨st_fin, hlen_f, hwf_f, hag_f, htr_f, hperm_f, hoom_f, hct_f, hcr_f, hc0_f, hc1_f, hcv_f,
      hvals_f, hte_f, hun_f, huf_f, halen_f, hcl_f, har_f, hscr_f, hd0_f, h0, h1, hc, hmf⟩
  unfold s13PostFlushExpr
  refine wp_join_group (fun (brk_f, ()) mfl => P brk_f mfl) ?_ ?_
  · rintro _ ⟨brk_f, ⟨⟩⟩ mfl ⟨st_fl, hlen_l, hwf_l, hag_l, htr_l, hperm_l, hoom_l, hct_l, hcr_l,
      hc0_l, hc1_l, hcv_l, hvals_l, hte_l, hun_l, huf_l, halen_l, hcl_l, har_l, hscr_l, hd0_l,
      hb0, hb1, hbc, hmfl⟩
    exact s13_post_brk_cont_wp hAddTicks hQ hJ_out hcfg hext1 hw2b1 hlen0 hpr_lt hs_base hfuel1
      hs_disk htr_o hperm_o hag_o hcv_o hcl_o hprob_o halen_o _hsc_o hfl_rem_dec hfuel_le hp1_prop
      hp_lt_o hpr_ge hpi_b_len hpi_b_cv hpi_b_tr hdense_b hte_b hun_b huf_b
      (fun h => hbr0 (hb0 h)) hbr_cf (fun h => hbr1 (hb1 h)) hbc hlen_l hwf_l hag_l htr_l hperm_l
      hoom_l hct_l hcr_l hc0_l hc1_l hcv_l hvals_l hte_l hun_l huf_l halen_l hcl_l har_l
      hscr_l hd0_l hmfl
  · intro Jfl hJfl
    s13_hsplit
    · refine wp_join_group (fun (r, ()) m5 => P r m5) ?_ ?_
      · rintro _ ⟨r, ⟨⟩⟩ m5 h5; s13_hsteps; exact hJfl (r, ()) m5 h5
      · intro J5 hJ5
        obtain ⟨te_mem, hsd_eq, htem_le, hpr_tem⟩ := hs_disk
        have hdm_f : st_fin.core.dense_mode = 0#64 :=
          (hag_f.get FullCoreState.dense_mode).trans hdense_b
        have hcv_fb : st_fin.core.cur_vars = s_base.core.cur_vars :=
          hag_f.get FullCoreState.cur_vars
        have hsd_len : s_disk.LengthsOk c := by
          rw [hsd_eq]
          exact ⟨{ hlen0.core_ok with
            trail_end_le := by
              have h1 := hpi_b_tr.te_ge; have h2 := hlen_f.core_ok.trail_end_le
              rw [hs_base] at h1; rw [hcv_fb, hs_base] at h2
              dsimp only at h1 h2 ⊢; rw [← hcv_o]; omega
            propagated_le := hpr_tem }, hlen0.scratch_ok⟩
        have hlen_mem : (fastPropMem s_disk st_fin).LengthsOk c :=
          fastPropMem_lengthsOk hsd_len hlen_f
            (by rw [hsd_eq, hcv_fb, hs_base]; exact hcv_o)
            (by rw [hsd_eq, hag_f.get FullCoreState.propagated, hs_base]) rfl
        have hwat_f : WatchesInv F_cur st_fin.core := by
          have hw_sp := hwf_f.watches; simpa only [ModeWatchesInv, hdm_f, ↓reduceIte] using hw_sp
        have hlay_mem : WatchStackLayout (fastPropMem s_disk st_fin).core :=
          fastPropMem_watchLayout hwat_f.layout rfl
        have hdok_mem : DelayedWatchesOk (fastPropMem s_disk st_fin).core
            (fastPropMem s_disk st_fin).scratch.delayed dlen_b not_lit.toNat := by
          rw [fastPropMem_delayed]
          exact delayedWatchesOk_congr (k1 := s_base.core)
            (by rw [fastPropMem_def]; exact hcv_fb)
            (by rw [fastPropMem_def]; exact hperm_f.1) hdok_b
        c0_call hFlush
        refine fidPropFlushDelSpec_of (F_cur := F_cur) hlen_mem hlay_mem hdi_b hdlen_b hdok_mem hmf
          fun ok wv' ws' wl' wu' wso' m' hlen' hlay' hwat' _hsw' hm' => ?_
        let st_fl : FullState :=
          { st_fin with
            core := { st_fin.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
            scratch := { st_fin.scratch with wsort := wso' } }
        have hlen_l : st_fl.LengthsOk c := by
          simp only [fastPropMem_def] at hlen'
          have hso := hlen'.scratch_ok
          have hscr4 : st_fl.scratch.LengthsOk c :=
            ⟨hso.1, hso.2, hso.3, hso.4, hso.5, hso.6, hso.7, hso.8, hso.9, hso.10, hso.11,
             hso.12, hso.13, hso.14, hso.15, hso.16, hso.17, hso.18, hso.19, hso.20, hso.21,
             hso.22, hso.23, hso.24⟩
          exact ⟨{ hlen'.core_ok with
              trail_end_le := hlen_f.core_ok.trail_end_le
              propagated_le := hlen_f.core_ok.propagated_le }, hscr4⟩
        have hwat_mem : WatchesInv F_cur (fastPropMem s_disk st_fin).core :=
          fid_watches_congr hwat_f hdm_f (by rw [fastPropMem_def]) (by rw [fastPropMem_def])
            (by rw [fastPropMem_def]) (by rw [fastPropMem_def]) (by rw [fastPropMem_def])
            (by unfold fullArenaClauseRefsCore; rw [fastPropMem_def])
        have hwat_l : WatchesInv F_cur st_fl.core :=
          fid_watches_congr (hwat' hwat_mem) (by rw [fastPropMem_def]; exact hdm_f)
            (by rw [fastPropMem_def]) (by rw [fastPropMem_def]) (by rw [fastPropMem_def])
            (by rw [fastPropMem_def]) (by rw [fastPropMem_def])
            (by unfold fullArenaClauseRefsCore; rw [fastPropMem_def])
        have hnw_l : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st_fl.core) :=
          fullWitnessInv_nw_congr hlen_l.core_ok.cur_vars_le
            (fullWitnessInv_to_nw hlen_f.core_ok.cur_vars_le hwf_f)
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        have hwf_l : FullWitnessInv c F0 F_cur st_fl.core :=
          fullWitnessInv_of_nw hnw_l hdm_f hwat_l
        have hm_l : (FullMem c (fastPropMem s_disk st_fl) ⋆
            (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m' := by
          simpa only [st_fl, fastPropMem_def] using hm'
        have hscr_l : S13Scr s st_fl := by
          unfold S13Scr at hscr_f ⊢; dsimp only [st_fl]; rw [hscr_f]
        have hag_l : AgreesExcept propLitCoreMask s_base.core st_fl.core :=
          hag_f.update (fun k => { k with wvec := wv', wstk := ws', wlen := wl', wusable := wu' })
        have htr_l : FullPropDecSpecs.FullTrailExt s_base.core st_fl.core :=
          ⟨htr_f.te_ge, htr_f.trl_pref, htr_f.lvl_pres⟩
        have hperm_l : FullPropDecSpecs.FullArenaPermEq s_base.core st_fl.core :=
          m7_arenaPermEq_congr rfl rfl rfl rfl hperm_f
        s13_hsplit
        · s13_hsteps
          exact hJ5 (brk_b, ()) m' ⟨st_fl, hlen_l, hwf_l, hag_l, htr_l, hperm_l, hoom_f, hct_f,
            hcr_f, hc0_f, hc1_f, hcv_f, hvals_f, hte_f, hun_f, huf_f, halen_f, hcl_f, har_f,
            hscr_l, hd0_f, id, id, hbr_cases, hm_l⟩
        · s13_hsteps
          exact hJ5 (2#64, ()) m' ⟨st_fl, hlen_l, hwf_l, hag_l, htr_l, hperm_l, hoom_f, hct_f,
            hcr_f, hc0_f, hc1_f, hcv_f, hvals_f, hte_f, hun_f, huf_f, halen_f, hcl_f, har_f,
            hscr_l, hd0_f, fun h => absurd h (by decide), fun h => absurd h (by decide),
            by cases isBeyond <;> simp, hm_l⟩
    · s13_hsteps
      exact hJfl (brk_b, ()) mf (hP_fin brk_b id id hbr_cases)

theorem s13_compact_post_wp {Γ : Env} {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext0 ext1 : List (BitVec 64)}
    {s sem s_base s_disk sem_b : FullState}
    {ignore_ref prop_v fuel1 te_b un_b uf_b tk_b off_b p_b q_b end_b di_b brk_b
      nl64 : BitVec 64}
    {not_lit : BitVec 32} {dlen_b : Nat}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mb : Mem 64}
    {J_out : Cont [i64, i64, i64, i64, i64, i64]}
    (hFlush : ∀ args m Q X, fidPropFlushDelSpec args m Q X →
      Γ "full_prop_flush_del_fid" [i64, i64] [.bool] args m Q X)
    (hAddTicks : ∀ args m Q X, step13AddTicksSpec args m Q X →
      Γ "m6_hdr_add_ticks" [i64, i64] [] args m Q X)
    (hQ : S13HQ isBeyond c F0 F_cur ext0 s ignore_ref R Q)
    (hJ_out : ∀ (sem_next : FullState) (te_mc : Nat) (mc0 : Mem 64),
      sem_next.LengthsOk c → FullWitnessInv c F0 F_cur sem_next.core →
      FullTrailExt s.core sem_next.core → FullArenaPermEq s.core sem_next.core →
      AgreesExcept fidCoreMask s.core sem_next.core →
      sem_next.core.propagated = (prop_v + 1#64).toNat →
      sem_next.core.fuel = fuel1 → sem_next.core.trail_end = te_b.toNat →
      sem_next.core.unassigned = un_b → sem_next.core.unflushed = uf_b →
      sem_next.core.oom = 0#64 →
      (isBeyond = false → sem_next.core.confl_type = s.core.confl_type) →
      (isBeyond = true → S13ConflEq s.core sem_next.core) →
      sem_next.core.dense_mode = 0#64 → sem_next.core.cur_vars = s.core.cur_vars →
      sem_next.core.cur_level = s.core.cur_level → sem_next.core.probing = s.core.probing →
      sem_next.core.arena_len = s.core.arena_len →
      sem_next.core.fuel.toNat < sem.core.fuel.toNat →
      sem_next.core.fuel.toNat < s.core.fuel.toNat →
      sem_next.core.fuel.toNat ≤ s.core.fuel.toNat →
      s.core.propagated ≤ sem_next.core.propagated → te_mc ≤ sem_next.core.trail_end →
      s.core.propagated ≤ te_mc → S13Scr s sem_next →
      (c.delayed_cap = 0 → sem_next.scratch.delayed = s.scratch.delayed) →
      (FullM6HdrMem c ext1 (fastPropMem { s with core := { s.core with trail_end := te_mc } }
        { sem_next with core :=
          { sem_next.core with propagated := s.core.propagated, fuel := s.core.fuel } }) ⋆ R) mc0 →
      wp Γ Q X (Expr.jump J_out (.var (prop_v + 1#64), (.var te_b, (.var fuel1, (.var un_b,
        (.var uf_b, (.var tk_b, ()))))))) mc0)
    (hcfg : FullM6HdrCfgOk c) (hext1 : M6HdrExtOk ext1)
    (hw2b1 : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1)
    (hwc : c.wcap < 2 * dimacsBound) (_hmaxv : c.max_vars < 2 * dimacsBound)
    (hlen0 : s.LengthsOk c) (hpr_lt : s.core.propagated < s.core.trail_end)
    (hs_base : s_base = { sem with core := { sem.core with
      propagated := s.core.propagated, fuel := s.core.fuel } })
    (hfuel1 : fuel1 = sem.core.fuel - 1#64)
    (hs_disk : ∃ te_mem, s_disk = { s with core := { s.core with trail_end := te_mem } } ∧
      te_mem ≤ sem.core.trail_end ∧ s.core.propagated ≤ te_mem)
    (htr_o : FullTrailExt s.core sem.core) (hperm_o : FullArenaPermEq s.core sem.core)
    (hag_o : AgreesExcept fidCoreMask s.core sem.core)
    (hcv_o : sem.core.cur_vars = s.core.cur_vars)
    (hcl_o : sem.core.cur_level = s.core.cur_level)
    (hprob_o : sem.core.probing = s.core.probing) (halen_o : sem.core.arena_len = s.core.arena_len)
    (hsc_o : S13Scr s sem)
    (hfl_rem_dec : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat)
    (hfuel_le : sem.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hp1_prop : (prop_v + 1#64).toNat = prop_v.toNat + 1)
    (hp_lt_o : prop_v.toNat < sem.core.trail_end) (hpr_ge : s.core.propagated ≤ prop_v.toNat)
    (hnl64 : nl64 = not_lit.setWidth 64 <<< (1 : Nat))
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars) (hdense_b : s_base.core.dense_mode = 0#64)
    (hpi_b : PropLitInv c F0 F_cur
      { s_base with scratch := { s_base.scratch with delayed := sem_b.scratch.delayed } }
      sem_b not_lit.toNat off_b.toNat q_b.toNat p_b.toNat end_b.toNat)
    (hdi_b : di_b.toNat = 3 * dlen_b) (hdlen_b : dlen_b ≤ c.delayed_cap)
    (hdok_b : DelayedWatchesOk s_base.core sem_b.scratch.delayed dlen_b not_lit.toNat)
    (hd0_b : c.delayed_cap = 0 → sem_b.scratch.delayed = s.scratch.delayed)
    (hte_b : te_b.toNat = sem_b.core.trail_end)
    (hun_b : un_b = sem_b.core.unassigned) (huf_b : uf_b = sem_b.core.unflushed)
    (hbr0 : brk_b = 0#64 → sem_b.core.oom = 0#64 ∧
      (isBeyond = false → sem_b.core.confl_type = s.core.confl_type))
    (hbr_cf : isBeyond = true → S13ConflEq s.core sem_b.core)
    (hbr1 : brk_b = 1#64 → isBeyond = false ∧ PropLitConfl F_cur ignore_ref sem_b.core ∧
      sem_b.core.oom = 0#64)
    (hbr_cases : if isBeyond then (brk_b = 0#64 ∨ brk_b = 2#64)
      else (brk_b = 0#64 ∨ brk_b = 1#64 ∨ brk_b = 2#64))
    (hmb : (FullMem c (fastPropMem s_disk sem_b) ⋆
      (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mb) :
    wp Γ Q X (s13CompactAndPostExpr J_out c.hdr c.pWstk c.pWvec nl64 prop_v fuel1 te_b un_b
      uf_b tk_b off_b p_b q_b end_b di_b brk_b) mb := by
  subst nl64
  obtain ⟨te_mem, hs_disk_eq, htem_le, hpr_tem⟩ := hs_disk
  have hnot_b : not_lit.toNat < 2 * sem_b.core.cur_vars := by
    rw [hpi_b.cur_vars_eq, hs_base]; exact hnot_lt
  have hend_b_le : end_b.toNat ≤ c.wcap := by have := hpi_b.end_lt_wcap hnot_b; omega
  have hwc64 : c.wcap + 1 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 1) (by decide)
  have hq_ge_b := hpi_b.sw.q_ge; have hq_le_b := hpi_b.sw.q_le_p; have hp_le_b := hpi_b.sw.p_le_end
  have hte_sem_le : sem.core.trail_end ≤ sem_b.core.trail_end := by
    have := hpi_b.tr.te_ge; subst hs_base; exact this
  have hsd_len : s_disk.LengthsOk c := by
    subst hs_disk_eq
    exact ⟨{ hlen0.core_ok with
        trail_end_le := Nat.le_trans htem_le (Nat.le_trans hte_sem_le (by
          rw [← hcv_o]
          have hcv_b : sem_b.core.cur_vars = sem.core.cur_vars := by
            rw [hpi_b.cur_vars_eq, hs_base]
          rw [← hcv_b]; exact hpi_b.len.core_ok.trail_end_le))
        propagated_le := hpr_tem }, hlen0.scratch_ok⟩
  have hnot_b_mv : not_lit.toNat < 2 * c.max_vars := by
    have := hpi_b.len.core_ok.cur_vars_le; omega
  have hnl64_1_idx : ((BitVec.setWidth 64 not_lit <<< (1 : Nat)) + (1 : BitVec 64)).toNat =
      2 * not_lit.toNat + 1 := by
    simpa only [BitVec.ofNat_eq_ofNat] using m7_bv64_shl1_add1_nat not_lit
  let s_pi_b : FullState :=
    { s_base with scratch := { s_base.scratch with delayed := sem_b.scratch.delayed } }
  have hscr_spi : S13Scr s s_pi_b := by
    unfold S13Scr at hsc_o ⊢; dsimp only [s_pi_b]; rw [hs_base]; dsimp only; rw [hsc_o]
  have hscr_b : S13Scr s sem_b := s13_scr_of_pi hpi_b.sc_eq hscr_spi
  unfold s13CompactAndPostExpr
  refine wp_loop_group (fun rem_c (pc_v, qc_v, ()) mc =>
    ∃ wstk_c : List (BitVec 32),
      rem_c = end_b.toNat - pc_v.toNat ∧ wstk_c.length = c.wcap ∧
      p_b.toNat ≤ pc_v.toNat ∧ pc_v.toNat ≤ end_b.toNat ∧
      qc_v.toNat = q_b.toNat + (pc_v.toNat - p_b.toNat) ∧
      (∀ k, off_b.toNat ≤ k → k < q_b.toNat → wstk_c[k]? = sem_b.core.wstk[k]?) ∧
      (∀ k < pc_v.toNat - p_b.toNat, wstk_c[q_b.toNat + k]? = sem_b.core.wstk[p_b.toNat + k]?) ∧
      (∀ k, pc_v.toNat ≤ k → k < end_b.toNat → wstk_c[k]? = sem_b.core.wstk[k]?) ∧
      (∀ k, (k < off_b.toNat ∨ end_b.toNat ≤ k) → wstk_c[k]? = sem_b.core.wstk[k]?) ∧
      (FullMem c (fastPropMem s_disk { sem_b with core :=
        { sem_b.core with wstk := wstk_c } }) ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mc) ?_ ?_
  · rintro Jc rem_c ⟨pc_v, qc_v, ⟨⟩⟩ mc ih_c ⟨wstk_c, rfl, hwc_len, hp_pc, hpc_end,
        hqc_n, hpre_c, hsuf_c, hrem_c, hout_c, hmc⟩
    have hmem_c_len : (fastPropMem s_disk
        { sem_b with core := { sem_b.core with wstk := wstk_c } }).LengthsOk c :=
      fastPropMem_lengthsOk hsd_len
        (sem := { sem_b with core := { sem_b.core with wstk := wstk_c } })
        ⟨{ hpi_b.len.core_ok with wstk_len_arr := hwc_len }, hpi_b.len.scratch_ok⟩
        (by rw [hpi_b.cur_vars_eq, hs_base, hs_disk_eq]; exact hcv_o)
        (by rw [hs_disk_eq]; dsimp only; rw [hpi_b.ag.get FullCoreState.propagated, hs_base]) rfl
    have hwc_mem : (fastPropMem s_disk
        { sem_b with core := { sem_b.core with wstk := wstk_c } }).core.wstk.length =
        c.wcap := by rw [fastPropMem_wstk]; exact hwc_len
    s13_hsplit
    · have hpc_lt : pc_v.toNat < end_b.toNat := hc
      have hpc_lt_w : pc_v.toNat < wstk_c.length := by rw [hwc_len]; omega
      have hqc_lt_w : qc_v.toNat < wstk_c.length := by rw [hwc_len]; omega
      have hpc1_n : (pc_v + 1#64).toNat = pc_v.toNat + 1 := m7_bv64_add1_toNat (by omega)
      have hqc1_n : (qc_v + 1#64).toNat = qc_v.toNat + 1 := m7_bv64_add1_toNat (by omega)
      let v_p := wstk_c[pc_v.toNat]'hpc_lt_w
      let wstk_c' := wstk_c.set qc_v.toNat v_p
      have hstep := propLit_loop2_step hq_ge_b hq_le_b hp_pc hpc_lt hpc_lt_w
        (by rw [← hqc_n]; exact hqc_lt_w) hpre_c hsuf_c hrem_c hout_c
      rw [← hqc_n] at hstep
      s13_hsteps
      exact ih_c _ (pc_v + 1#64, qc_v + 1#64, ()) m (by rw [hpc1_n]; omega)
        ⟨wstk_c', rfl, by simp [wstk_c', hwc_len], by rw [hpc1_n]; omega,
          by rw [hpc1_n]; omega, by rw [hqc1_n, hpc1_n]; omega,
          hstep.1, fun k hk => by rw [hpc1_n] at hk; exact hstep.2.1 k hk,
          fun k hk1 hk2 => by rw [hpc1_n] at hk1; exact hstep.2.2.1 k hk1 hk2,
          hstep.2.2.2, by
            simpa only [wstk_c', v_p, fastPropMem_with_wstk, fastPropMem_wstk] using hm⟩
    · have hpc_eq : pc_v = end_b := BitVec.eq_of_toNat_eq (by omega)
      rw [hpc_eq] at hqc_n hsuf_c
      s13_hsteps_nogrp
      refine wp_store_sep (FullArenaTactics.c0_store_full_wvec
        (BitVec.setWidth 32 (qc_v - off_b)) ?_ hmc) ?_
      next =>
        dsimp only; erw [hnl64_1_idx]; rw [fastPropMem_wvec, hpi_b.len.core_ok.wvec_len]
        change 2 * not_lit.toNat + 1 < 4 * c.max_vars; omega
      intro m hm; dsimp only at hm; erw [hnl64_1_idx] at hm; rw [fastPropMem_wvec] at hm
      replace hm : (FullMem c (fastPropMem s_disk { sem_b with core :=
          { sem_b.core with
            wstk := wstk_c
            wvec := sem_b.core.wvec.set (2 * not_lit.toNat + 1)
              ((qc_v - off_b).setWidth 32) } }) ⋆
          (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m := by simpa only [fastPropMem] using hm
      refine wp_join_group (ts := []) (fun () mf => ∃ st_fin : FullState,
        st_fin.LengthsOk c ∧ FullWitnessInv c F0 F_cur st_fin.core ∧
        AgreesExcept propLitCoreMask s_base.core st_fin.core ∧
        FullPropDecSpecs.FullTrailExt s_base.core st_fin.core ∧
        FullPropDecSpecs.FullArenaPermEq s_base.core st_fin.core ∧
        st_fin.core.oom = sem_b.core.oom ∧ st_fin.core.confl_type = sem_b.core.confl_type ∧
        st_fin.core.confl_ref = sem_b.core.confl_ref ∧
        st_fin.core.confl_lit0 = sem_b.core.confl_lit0 ∧
        st_fin.core.confl_lit1 = sem_b.core.confl_lit1 ∧
        st_fin.core.cur_vars = sem_b.core.cur_vars ∧ st_fin.core.vals = sem_b.core.vals ∧
        st_fin.core.trail_end = sem_b.core.trail_end ∧
        st_fin.core.unassigned = sem_b.core.unassigned ∧
        st_fin.core.unflushed = sem_b.core.unflushed ∧
        st_fin.core.arena_len = sem_b.core.arena_len ∧
        st_fin.core.cur_level = sem_b.core.cur_level ∧ st_fin.core.arena = sem_b.core.arena ∧
        S13Scr s st_fin ∧ (c.delayed_cap = 0 → st_fin.scratch.delayed = s.scratch.delayed) ∧
        DelayedWatchesOk s_base.core st_fin.scratch.delayed dlen_b not_lit.toNat ∧
        (FullMem c (fastPropMem s_disk st_fin) ⋆
          (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mf) ?_ ?_
      · rintro _ ⟨⟩ mf ⟨st_fin, hlen_f, hwf_f, hag_f, htr_f, hperm_f, hoom_f, hct_f, hcr_f,
            hc0_f, hc1_f, hcv_f, hvals_f, hte_f, hun_f, huf_f, halen_f, hcl_f, har_f, hscr_f,
            hd0_f, hdok_f, hmf⟩
        exact s13_post_flush_wp hFlush hAddTicks hQ hJ_out hcfg hext1 hw2b1 hlen0 hpr_lt hs_base
          hfuel1 ⟨te_mem, hs_disk_eq, htem_le, hpr_tem⟩ htr_o hperm_o hag_o hcv_o hcl_o hprob_o
          halen_o hsc_o hfl_rem_dec hfuel_le hp1_prop hp_lt_o hpr_ge hpi_b.len hpi_b.cur_vars_eq
          hpi_b.tr hdense_b hte_b hun_b huf_b hbr0 hbr_cf hbr1 hbr_cases hdi_b hdlen_b hdok_f
          hlen_f hwf_f hag_f htr_f hperm_f hoom_f hct_f hcr_f hc0_f hc1_f hcv_f hvals_f hte_f
          hun_f huf_f halen_f hcl_f har_f hscr_f hd0_f hmf
      · intro Jfn hJfn
        have hqc_v_eq : qc_v.toNat = q_b.toNat + (end_b.toNat - p_b.toNat) := hqc_n
        have hqc_le_end : qc_v.toNat ≤ end_b.toNat := by omega
        have hidx1_lt : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat <
            sem_b.core.wvec.length := by
          rw [hpi_b.len.core_ok.wvec_len, m7_bv64_shl1_add1_nat]; omega
        let wvec_f := sem_b.core.wvec.set (2 * not_lit.toNat + 1) ((qc_v - off_b).setWidth 32)
        let wu_f := sem_b.core.wusable + (end_b - qc_v)
        s13_hsplit
        · s13_hsteps
          refine wp_loop_group (fun rem_k (k_v, ()) mk => ∃ wstk_k : List (BitVec 32),
            rem_k = end_b.toNat - k_v.toNat ∧ wstk_k.length = c.wcap ∧
            qc_v.toNat ≤ k_v.toNat ∧ k_v.toNat ≤ end_b.toNat ∧
            (∀ i, (i < qc_v.toNat ∨ end_b.toNat ≤ i) → wstk_k[i]? = wstk_c[i]?) ∧
            (FullMem c (fastPropMem s_disk { sem_b with core :=
              { sem_b.core with wstk := wstk_k, wvec := wvec_f, wusable := wu_f } }) ⋆
              (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mk) ?_ ?_
          · rintro Jk rem_k ⟨k_v, ⟨⟩⟩ mk ih_k ⟨wstk_k, rfl, hwk_len, hq_k, hk_end, hk_keep, hmk⟩
            have hmem_k_len : (fastPropMem s_disk { sem_b with core :=
                { sem_b.core with wstk := wstk_k, wvec := wvec_f, wusable := wu_f } }).LengthsOk
                c :=
              fastPropMem_lengthsOk hsd_len
                (sem := { sem_b with core :=
                  { sem_b.core with wstk := wstk_k, wvec := wvec_f, wusable := wu_f } })
                ⟨{ hpi_b.len.core_ok with
                    wvec_len := by simp only [wvec_f, List.length_set, hpi_b.len.core_ok.wvec_len]
                    wstk_len_arr := hwk_len }, hpi_b.len.scratch_ok⟩
                (by rw [hpi_b.cur_vars_eq, hs_base, hs_disk_eq]; exact hcv_o)
                (by rw [hs_disk_eq]; dsimp only
                    rw [hpi_b.ag.get FullCoreState.propagated, hs_base]) rfl
            have hwk_mem : (fastPropMem s_disk { sem_b with core :=
                { sem_b.core with wstk := wstk_k, wvec := wvec_f, wusable := wu_f }
                }).core.wstk.length = c.wcap := by rw [fastPropMem_wstk]; exact hwk_len
            s13_hsplit
            · have hk_lt : k_v.toNat < end_b.toNat := hc
              have hk_lt_w : k_v.toNat < wstk_k.length := by rw [hwk_len]; omega
              have hk1_n : (k_v + 1#64).toNat = k_v.toNat + 1 := m7_bv64_add1_toNat (by omega)
              refine wp_store_sep (FullArenaTactics.c0_store_full_wstk 0xFFFFFFFF#32
                (by rw [hwk_mem]; exact Nat.lt_of_lt_of_eq hk_lt_w hwk_len) hmk) ?_
              intro m hm; clear hmk hwk_mem; s13_hsteps; dsimp only [Arg.val] at hm
              exact ih_k (end_b.toNat - (k_v + 1#64).toNat) (k_v + 1#64, ()) m (by omega)
                ⟨wstk_k.set k_v.toNat 0xFFFFFFFF#32, rfl, by rw [List.length_set, hwk_len],
                  by omega, by omega, propLit_loop3_step hq_k hk_lt hk_keep,
                  by simpa only [fastPropMem_with_wstk, fastPropMem_wstk] using hm⟩
            · s13_hsteps
              have hfin := m7_compact_finish_step hpi_b hdense_b hnot_b hwk_len
                hqc_v_eq hpre_c hsuf_c hout_c hk_keep
              let st_fin_k : FullState :=
                { sem_b with core :=
                  { sem_b.core with wstk := wstk_k, wvec := wvec_f, wusable := wu_f } }
              exact hJfn () mk ⟨st_fin_k, hfin.1, hfin.2.1, hfin.2.2.1, hfin.2.2.2.1,
                hfin.2.2.2.2.1, hfin.2.2.2.2.2.1, hfin.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
                rfl, hscr_b, hd0_b, hdok_b, hmk⟩
          · intro Jk hJk
            exact hJk _ (qc_v, ()) m ⟨wstk_c, rfl, hwc_len, Nat.le_refl _, hqc_le_end,
              fun _ _ => rfl,
              by simpa only [wvec_f, wu_f, fastPropMem_wusable, fastPropMem] using hm⟩
        · have hqc_eq_end : qc_v = end_b := BitVec.eq_of_toNat_eq (by omega)
          have hsub0 : end_b - qc_v = 0#64 := by rw [hqc_eq_end]; simp
          have hfin := m7_compact_finish_step hpi_b hdense_b hnot_b hwc_len
            hqc_v_eq hpre_c hsuf_c hout_c (fun _ _ => rfl)
          have hwu0 : sem_b.core.wusable + (end_b - qc_v) = sem_b.core.wusable := by
            rw [hsub0]; simp
          let st_fin_0 : FullState :=
            { sem_b with core := { sem_b.core with
              wstk := wstk_c, wvec := wvec_f, wusable := sem_b.core.wusable + (end_b - qc_v) } }
          exact hJfn () m ⟨st_fin_0, hfin.1, hfin.2.1, hfin.2.2.1, hfin.2.2.2.1,
            hfin.2.2.2.2.1, hfin.2.2.2.2.2.1, hfin.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
            rfl, hscr_b, hd0_b, hdok_b, by simpa only [st_fin_0, wvec_f, hwu0] using hm⟩
  · intro Jc hJc
    s13_hsteps
    exact hJc _ (p_b, q_b, ()) mb ⟨sem_b.core.wstk, rfl, hpi_b.len.core_ok.wstk_len_arr,
      Nat.le_refl _, hp_le_b, by simp, fun _ _ _ => rfl, fun _ hk => absurd hk (by omega),
      fun _ _ _ => rfl, fun _ _ => rfl, hmb⟩

/-- Step-13 `while (ovf)` header signature (`10` args when `isBeyond = true`, `11` when `false`). -/
abbrev s13LoSig (isBeyond : Bool) : List Ty :=
  if isBeyond then [i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool]
  else [i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool]

/-- Step-13 `while (ovf)` jump (`brk` omitted when `isBeyond = true`). -/
abbrev s13LoJump {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (isBeyond : Bool) (Lo : L (s13LoSig isBeyond))
    (te un uf tk off p q ed di brk : Arg V i64) (ovf : Arg V Ty.bool) : Expr V L rs :=
  match isBeyond, Lo with
  | true, L0 => Expr.jump L0 (te, un, uf, tk, off, p, q, ed, di, ovf, ())
  | false, L0 => Expr.jump L0 (te, un, uf, tk, off, p, q, ed, di, brk, ovf, ())

/-- Step-13 post-scan overflow handler parameterized over `isBeyond`. -/
@[expose] def s13PostLpOvfExpr (isBeyond : Bool) (c : FullCfg) (nl64 : Val i64)
    (not_lit_v : Val i32) (off_o end_o : Val i64)
    (Bo : Cont [i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool])
    (Lo : Cont (s13LoSig isBeyond))
    (te_p un_p uf_p tk_p p_p q_p di_p brk_p : Val i64) (ovf_p : Val Ty.bool)
    (ovf_rw_p ovf_oth_p ovf_cr_p : Val i32) (ovf_ri_p : Val i64) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i64, i64, i64, i64, i64, i64]])
    (fun _Js0 => Blocks.cons
      (fun p1 => s13LoJump isBeyond Lo (Arg.var te_p) (Arg.var un_p) (Arg.var uf_p)
        (Arg.var tk_p) (Arg.var p1.fst) (Arg.var p1.snd.fst) (Arg.var p1.snd.snd.fst)
        (Arg.var p1.snd.snd.snd.fst) (Arg.var p1.snd.snd.snd.snd.fst)
        (Arg.var p1.snd.snd.snd.snd.snd.fst) (Arg.var ovf_p))
      Blocks.nil)
    (fun Js0 =>
      Expr.jnz (Arg.var ovf_p)
        (Expr.group (sig := [[i64, Ty.bool]])
          (fun _Jf => Blocks.cons
            (fun pf =>
              Expr.group (sig := [[Ty.bool]])
                (fun _Jp => Blocks.cons
                  (fun pk =>
                    Expr.let_ ⟨OpCode.mul i64, (Arg.var nl64, Arg.imm 4, ())⟩ fun boff =>
                    Expr.let_ ⟨OpCode.add i64, (Arg.var c.pWvec, Arg.var boff.fst, ())⟩ fun a =>
                    Expr.load i32 (Arg.var a.fst) fun noff32 =>
                    Expr.let_ ⟨OpCode.zext 32 64, (Arg.var noff32, ())⟩ fun noff =>
                    Expr.group (sig := [[i64, i64, i64, i64]])
                      (fun _Jn => Blocks.cons
                        (fun pn =>
                          Expr.jnz (Arg.var pk.fst)
                            (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ovf_cr_p, ())⟩ fun cr64 =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var cr64.fst, Arg.imm 3, ())⟩ fun ob =>
                            Expr.let_ ⟨OpCode.mul i64, (Arg.var ob.fst, Arg.imm 4, ())⟩ fun b3 =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var c.pArena, Arg.var b3.fst, ())⟩
                              fun a3 =>
                            Expr.store (Arg.var ovf_oth_p) (Arg.var a3.fst) $
                            Expr.let_ ⟨OpCode.add i64, (Arg.var ob.fst, Arg.imm 1, ())⟩ fun ob1 =>
                            Expr.let_ ⟨OpCode.mul i64, (Arg.var ob1.fst, Arg.imm 4, ())⟩ fun b4 =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var c.pArena, Arg.var b4.fst, ())⟩
                              fun a4 =>
                            Expr.store (Arg.var ovf_rw_p) (Arg.var a4.fst) $
                            Expr.let_ ⟨OpCode.add i64, (Arg.var ob.fst, Arg.var ovf_ri_p, ())⟩
                              fun obri =>
                            Expr.let_ ⟨OpCode.mul i64, (Arg.var obri.fst, Arg.imm 4, ())⟩ fun bri =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var c.pArena, Arg.var bri.fst, ())⟩
                              fun ari =>
                            Expr.store (Arg.var not_lit_v) (Arg.var ari.fst) $
                            Expr.jump Js0.fst
                              (Arg.var pn.fst, Arg.var pn.snd.fst, Arg.var pn.snd.snd.fst,
                                Arg.var pn.snd.snd.snd.fst, Arg.var pf.fst,
                                if isBeyond then Arg.imm 0 else Arg.var brk_p, ()))
                            (Expr.let_ ⟨OpCode.mul i64, (Arg.var pn.snd.snd.fst, Arg.imm 4, ())⟩
                              fun bq =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var c.pWstk, Arg.var bq.fst, ())⟩
                              fun aq =>
                            Expr.store (Arg.var ovf_oth_p) (Arg.var aq.fst) $
                            Expr.let_ ⟨OpCode.add i64, (Arg.var pn.snd.snd.fst, Arg.imm 1, ())⟩
                              fun q1 =>
                            Expr.let_ ⟨OpCode.mul i64, (Arg.var q1.fst, Arg.imm 4, ())⟩ fun bq1 =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var c.pWstk, Arg.var bq1.fst, ())⟩
                              fun aq1 =>
                            Expr.store (Arg.var ovf_cr_p) (Arg.var aq1.fst) $
                            Expr.let_ ⟨OpCode.add i64, (Arg.var pn.snd.snd.fst, Arg.imm 2, ())⟩
                              fun q2 =>
                            Expr.jump Bo
                              (Arg.var te_p, Arg.var un_p, Arg.var uf_p, Arg.var tk_p,
                                Arg.var pn.fst, Arg.var pn.snd.fst, Arg.var q2.fst,
                                Arg.var pn.snd.snd.snd.fst, Arg.var pf.fst, Arg.imm 2,
                                Arg.var ovf_p, ())))
                        Blocks.nil)
                      (fun Jn =>
                        Expr.let_ ⟨OpCode.cmp CmpOp.ne i64, (Arg.var noff.fst, Arg.var off_o, ())⟩
                          fun ne =>
                        Expr.jnz (Arg.var ne.fst)
                          (Expr.let_ ⟨OpCode.sub i64, (Arg.var q_p, Arg.var off_o, ())⟩ fun qoff =>
                          Expr.let_ ⟨OpCode.add i64, (Arg.var noff.fst, Arg.var qoff.fst, ())⟩
                            fun qn =>
                          Expr.let_ ⟨OpCode.sub i64, (Arg.var p_p, Arg.var off_o, ())⟩ fun poff =>
                          Expr.let_ ⟨OpCode.add i64, (Arg.var noff.fst, Arg.var poff.fst, ())⟩
                            fun pn =>
                          Expr.let_ ⟨OpCode.sub i64, (Arg.var end_o, Arg.var off_o, ())⟩ fun eoff =>
                          Expr.let_ ⟨OpCode.add i64, (Arg.var noff.fst, Arg.var eoff.fst, ())⟩
                            fun en =>
                          Expr.jump Jn.fst
                            (Arg.var noff.fst, Arg.var pn.fst, Arg.var qn.fst, Arg.var en.fst, ()))
                          (Expr.jump Jn.fst
                            (Arg.var off_o, Arg.var p_p, Arg.var q_p, Arg.var end_o, ()))))
                  Blocks.nil)
                (fun Jp =>
                  Expr.jnz (Arg.var pf.snd.fst)
                    (Expr.call (as := [i64, i32, i32, i32]) (bs := [.bool])
                      "full_prop_lit_ovf_hot"
                      (Arg.var c.hdr, Arg.var ovf_rw_p, Arg.var ovf_oth_p, Arg.var ovf_cr_p, ())
                      fun pok =>
                    Expr.jump Jp.fst (Arg.var pok.fst, ()))
                    (Expr.jump Jp.fst (Arg.imm false, ()))))
            Blocks.nil)
          (fun Jf =>
            Expr.let_ ⟨OpCode.cmp CmpOp.ugt i64, (Arg.var di_p, Arg.imm 0, ())⟩ fun cd =>
            Expr.jnz (Arg.var cd.fst)
              (Expr.call (as := [i64, i64]) (bs := [.bool]) "full_prop_flush_del_fid"
                (Arg.var c.hdr, Arg.var di_p, ()) fun fok =>
              Expr.jump Jf.fst (Arg.imm 0, Arg.var fok.fst, ()))
              (Expr.jump Jf.fst (Arg.var di_p, Arg.imm true, ()))))
        (Expr.jump Js0.fst (Arg.var off_o, Arg.var p_p, Arg.var q_p, Arg.var end_o,
          Arg.var di_p, if isBeyond then Arg.imm 0 else Arg.var brk_p, ())))

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

end
