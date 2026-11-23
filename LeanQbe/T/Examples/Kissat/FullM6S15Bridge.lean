module

public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
public import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
public import LeanQbe.T.Examples.Kissat.FullLuckyLemmas1
public import LeanQbe.T.Examples.Kissat.FullSubstLemmas1
public import LeanQbe.T.Examples.Kissat.FullProbeTransLemmas5
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof4c

/-!
# Kissat M6 `S1.5` Delayed-Watch Spec & Bridge Helpers (`FullM6S15Bridge`)

Purely additive bridges connecting `FullM6BcpS15.fullBcpS15Spec` /
`FullM6BcpS15.fullPropagateIgnoreS15Spec` to `Full.fullPropagateDelSpec` /
`Full.fullPropagateIgnoreDelSpec`, `FullDenseWatchSpecs.fullPropagateSpec`,
`FullLuckySpecs.fullPropagateSpec`, `FullSubstSpecs.fullPropagateDelSpec`,
`FullM6VivBackbone.full_probe_assume_pair_m6_del_wp`, and `FullM6HdrInvW` (`M6`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6S15Bridge

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone

/-! ## 1. `fullBcpS15Spec` / `fullPropagateIgnoreS15Spec` ↔ `*_del` Adapters -/

theorem fullBcpS15Spec_of_del {a : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : Full.fullPropagateDelSpec a m Q X) : fullBcpS15Spec a m Q X := by
  rcases a with ⟨hptr, ⟨⟩⟩
  obtain ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, hQ⟩ := h
  exact ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm,
    fun r v f lv rs tr tp te pr un uf wv ar ws wl wu fu ct cr c0 c1 oo tk wso ph del m'
        hlen' hw' htr hap _ hfl hr h0 h1 h2 heq hm' =>
      hQ r v f lv rs tr tp te pr un uf wv ar ws wl wu fu ct cr c0 c1 oo tk wso ph del m'
        hlen' hw' htr hap hfl hr h0 h1 h2 heq hm'⟩

theorem s15_to_propagateDel {Γ : Env} {f : Sym}
    (hS15 : ∀ a m Q X, fullBcpS15Spec a m Q X → Γ f [i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullPropagateDelSpec a m Q X → Γ f [i64] [i64] a m Q X :=
  fun _ _ _ _ h => hS15 _ _ _ _ (fullBcpS15Spec_of_del h)

theorem fullPropagateIgnoreS15Spec_of_del {a : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : Full.fullPropagateIgnoreDelSpec a m Q X) : fullPropagateIgnoreS15Spec a m Q X := by
  rcases a with ⟨hptr, ignore_ref, ⟨⟩⟩
  obtain ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, hQ⟩ := h
  exact ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm,
    fun r v f lv rs tr tp te pr un uf wv ar ws wl wu fu ct cr c0 c1 oo tk wso ph del m'
        hlen' hw' htr hap _ hfl hr h0 h1 h2 heq hm' =>
      hQ r v f lv rs tr tp te pr un uf wv ar ws wl wu fu ct cr c0 c1 oo tk wso ph del m'
        hlen' hw' htr hap hfl hr h0 h1 h2 heq hm'⟩

theorem s15_to_propagateIgnoreDel {Γ : Env} {f : Sym}
    (hS15 : ∀ a m Q X, fullPropagateIgnoreS15Spec a m Q X →
      Γ f [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullPropagateIgnoreDelSpec a m Q X → Γ f [i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => hS15 _ _ _ _ (fullPropagateIgnoreS15Spec_of_del h)

/-! ## 2. Stage-4 `FullDenseWatchSpecs` & `FullLuckySpecs` `S1.5` Adapters -/

theorem s15_to_dwPropagate {Γ : Env} {f : Sym}
    (hS15 : ∀ a m Q X, fullBcpS15Spec a m Q X → Γ f [i64] [i64] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullPropagateSpec a m Q X → Γ f [i64] [i64] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hdm, hm, hQ⟩
  refine hS15 _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, ?_⟩
  dsimp only
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m'
    hlen' hw' htr hperm _ hfl hr hr0 hr1 _ _ hm'
  let sc' : FullScratch :=
    { s.scratch with
      search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' }
  have hnd' : FullDenseWatchSpecs.FullArenaVarsNodup
      { s with
        core := { s.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
          unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
          wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
          confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := sc' } := by
    intro ref href hng
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hnd ref href0 (hgb.symm.trans hng))
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' sc' m' hlen' hw' hnd'
    (fun ref href => by change ref ∈ fullArenaClauseRefsCore _; rw [hperm.2.1]; exact href)
    rfl rfl rfl htr.1 hfl hr (fun h0 => (hr0 h0).2.1)
    (fun h1 => (hr1 h1).2.2.elim
      (fun ⟨ht, h0, h1', hf0, hf1, hent⟩ => Or.inl ⟨ht, h0, h1', hent, hf0, hf1⟩) Or.inr) hm'

theorem s15_to_luckyPropagate {Γ : Env} {f : Sym}
    (hS15 : ∀ a m Q X, fullBcpS15Spec a m Q X → Γ f [i64] [i64] a m Q X) :
    ∀ a m Q X, FullLuckySpecs.fullPropagateSpec a m Q X → Γ f [i64] [i64] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hdm, hm, hQ⟩
  refine hS15 _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, ?_⟩
  dsimp only
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m'
    hlen' hw' htr hperm _ hfl hr hr0 hr1 hr2 heq hm'
  let sc' : FullScratch :=
    { s.scratch with
      search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' }
  have hnd' : FullLuckySpecs.FullArenaVarsNodup
      { s with
        core := { s.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
          unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
          wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
          confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := sc' } := by
    intro ref href hng
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hnd ref href0 (hgb.symm.trans hng))
  have hps : FullLuckySpecs.FullProbeScratchPres s
      { s with
        core := { s.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
          unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
          wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
          confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := sc' } :=
    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' sc' m' hlen' hw' hnd' hps htr hfl
    (fun ref href => by change ref ∈ fullArenaClauseRefsCore _; rw [hperm.2.1]; exact href)
    hr hr0
    (fun h1 => let ⟨hf, ho, hc⟩ := hr1 h1
      ⟨hf, ho, hc.elim Or.inl fun ⟨ht2, hrest⟩ => Or.inr ⟨by rw [ht2]; decide, hrest⟩⟩)
    hr2 heq hm'

/-! ## 3. `FullM6HdrInvW` `fullBcpS15Spec` Call Combinator -/

theorem m6Hdr_call_fullBcpS15_invW {Γ : Env} {f : Sym} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ Q' X', fullBcpS15Spec (c.hdr, ()) m Q' X' → Γ f [i64] [i64] (c.hdr, ()) m Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ r s' m', FullM6HdrInvW c F0 F_cur ext s' →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → s'.core.propagated = s'.core.trail_end ∧
        (s.core.oom = 0#64 → s'.core.oom = 0#64) ∧
        (s.core.propagated < s.core.trail_end → s'.core.fuel.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullConflictOkW F_cur s') →
      (r = 2#64 → s'.core.oom ≠ 0#64 ∨ s'.core.fuel = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call f (as := [i64]) (bs := [i64]) args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hΓ _ X ⟨c, F0, F_cur, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R,
    rfl, hinv.sparseW.1, hinv.sparseW.2.1, hinv.sparseW.2.2.2.2.2,
    fullM6HdrMem_focus_full hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk'
    wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' s'
    hs' hw' hte hap _ hfl hdom h0 h1 h2 hs_eq hm'
  have hmc : FullLitMarksClear c s' := by
    have hmc0 := hinv.sparseW.2.2.1
    exact hmc0
  have hnd : FullArenaVarsNodup s' := fun ref href hng => by
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hap.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hap.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hinv.sparseW.2.2.2.1 ref href0 (hgb.symm.trans hng))
  have hll : FullLastLearnedWf s' :=
    hinv.sparseW.2.2.2.2.1.1.of_refs_subset rfl (fun _ hr => by
      change _ ∈ fullArenaClauseRefsCore _ at hr ⊢; rw [hap.2.1]; exact hr)
  have hinv' : FullM6HdrInvW c F0 F_cur ext s' :=
    FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
      ⟨hs', hw', hmc, hnd, ⟨hll, hinv.sparseW.2.2.2.2.1.2⟩, hinv.sparseW.2.2.2.2.2⟩
  exact hk r s' m' hinv' hte hap hfl hdom h0 h1 h2 hs_eq (fullM6HdrMem_unfocus_full hm')

/-! ## 4. Canonical `full_subst_elim_vars_del_wp` & `full_probe_assume_pair_m6_del_wp` Bridges -/

theorem substPropagateDel_adapter {Γ : Env} {f : Sym}
    (hProp : ∀ a m Q X, Full.fullPropagateDelSpec a m Q X → Γ f [i64] [i64] a m Q X) :
    ∀ a m Q X, FullSubstSpecs.fullPropagateDelSpec a m Q X → Γ f [i64] [i64] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, hQ⟩
  refine hProp _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, ?_⟩
  dsimp only
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m'
    hlen' hw' htr hperm hfl hr hr0 hr1 hr2 hnp hm'
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m'
    hlen' hw' htr hperm hfl hr hr0
    (fun h1 => let ⟨hf, ho, hc⟩ := hr1 h1
      ⟨hf, ho, hc.elim Or.inl fun ⟨ht2, hrest⟩ => Or.inr ⟨by rw [ht2]; decide, hrest⟩⟩)
    hr2 hnp hm'

theorem full_subst_elim_vars_del_canon_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateDelSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hExtPush2 : ∀ a m Q X, fullExtendPush2Spec a m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] a m Q X)
    (hSetInact : ∀ a m Q X, fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullSubstElimVarsSpec a m Q X → Func.wp Γ full_subst_elim_vars_body a m Q X :=
  full_subst_elim_vars_del_wp Γ hAddUnit (substPropagateDel_adapter hProp) hExtPush2 hSetInact

theorem full_subst_elim_vars_s15_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hProp : ∀ a m Q X, fullBcpS15Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hExtPush2 : ∀ a m Q X, fullExtendPush2Spec a m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] a m Q X)
    (hSetInact : ∀ a m Q X, fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullSubstElimVarsSpec a m Q X → Func.wp Γ full_subst_elim_vars_body a m Q X :=
  full_subst_elim_vars_del_canon_wp Γ hAddUnit (s15_to_propagateDel hProp) hExtPush2 hSetInact

private theorem otfs_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullProbeTransSpecs.FullOtfsWitnessInv c F0 F_cur k) :
    FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem backtrack_adapter {Γ : Env}
    (hBt : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullProbeTransSpecs.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X := by
  rintro ⟨h, tgt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm, hQ⟩
  refine hBt _ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm,
    fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
      hlen' hte hpr hcl' hps hsc htrl' hvl hw_w hw_o hm' => ?_⟩
  have hshrk : sc'.shrink_stk = s.scratch.shrink_stk := by
    rcases hsc with ⟨_, _, _, _, _, _, _, _, _, rfl⟩; rfl
  exact hQ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
    hlen' hte hpr hcl' hps hshrk htrl'
    (fun ⟨F0, Fc, hwo⟩ => hvl ⟨F0, Fc, hwo.elim Or.inl (Or.inr ∘ otfs_to_canon)⟩)
    hw_w (fun F0 Fc ho hlt => hw_o F0 Fc (otfs_to_canon ho) hlt) hm'

theorem full_probe_assume_pair_m6_canon_del_wp (Γ : Env)
    (hAssign : ∀ args m Q X, Full.fullAssignSpec args m Q X →
      Γ "full_assign" [i64, i32, i32] [] args m Q X)
    (hProbeProp : ∀ args m Q X, FullProbeTransSpecs.fullProbePropExtSpec args m Q X →
      Γ "full_probe_prop" [i64] [i64] args m Q X)
    (hBacktrack : ∀ args m Q X, Full.fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hAnalyze : ∀ args m Q X, FullProbeTransSpecs.fullAnalyze20Spec args m Q X →
      Γ "full_analyze" [i64] [i64] args m Q X)
    (hPropagate : ∀ args m Q X, Full.fullPropagateDelSpec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X)
    (hFlushHbr : ∀ args m Q X, FullProbeTransSpecs.fullProbeFlushHbrSpec args m Q X →
      Γ "full_probe_flush_hbr" [i64, i64] [i64] args m Q X)
    (hAddUnit : ∀ args m Q X, Full.fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, Full.fullProbeAssumePairSpec args m Q X →
      Func.wp Γ full_probe_assume_pair_m6_body args m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hlt, hun, hm, hQ⟩
  refine full_probe_assume_pair_m6_del_wp Γ hAssign hProbeProp (backtrack_adapter hBacktrack)
    hAnalyze hPropagate hFlushHbr hAddUnit (c.hdr, lit, ()) m Q X
    ⟨c, F0, s, R, rfl, hsp, hcl0, hlt, hun, hm, fun r s' m' h12 h20 hcv hfu hr hm' => ?_⟩
  exact hQ r s' m' h12
    (fun h => let ⟨hu, Fc, ho⟩ := h20 h; ⟨hu, Fc, ⟨ho.1, otfs_to_canon ho.2.1, ho.2.2⟩⟩)
    hcv hfu hr hm'

theorem full_probe_assume_pair_m6_s15_wp (Γ : Env)
    (hAssign : ∀ args m Q X, Full.fullAssignSpec args m Q X →
      Γ "full_assign" [i64, i32, i32] [] args m Q X)
    (hProbeProp : ∀ args m Q X, FullProbeTransSpecs.fullProbePropExtSpec args m Q X →
      Γ "full_probe_prop" [i64] [i64] args m Q X)
    (hBacktrack : ∀ args m Q X, Full.fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hAnalyze : ∀ args m Q X, FullProbeTransSpecs.fullAnalyze20Spec args m Q X →
      Γ "full_analyze" [i64] [i64] args m Q X)
    (hPropagate : ∀ args m Q X, fullBcpS15Spec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X)
    (hFlushHbr : ∀ args m Q X, FullProbeTransSpecs.fullProbeFlushHbrSpec args m Q X →
      Γ "full_probe_flush_hbr" [i64, i64] [i64] args m Q X)
    (hAddUnit : ∀ args m Q X, Full.fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, Full.fullProbeAssumePairSpec args m Q X →
      Func.wp Γ full_probe_assume_pair_m6_body args m Q X :=
  full_probe_assume_pair_m6_canon_del_wp Γ hAssign hProbeProp hBacktrack hAnalyze
    (s15_to_propagateDel hPropagate) hFlushHbr hAddUnit

theorem full_probe_flush_hbr_s15_wp (Γ : Env)
    (hAddBin : ∀ args m Q X, fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    (hProp : ∀ args m Q X, fullBcpS15Spec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X) :
    ∀ args m Q X, fullProbeFlushHbrSpec args m Q X →
      Func.wp Γ full_probe_flush_hbr_body args m Q X :=
  full_probe_flush_hbr_del_wp Γ hAddBin (s15_to_propagateDel hProp)

end LeanQbe.T.Examples.Kissat.FullM6S15Bridge
