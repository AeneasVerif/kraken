/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM4Proof1
public import LeanQbe.T.Examples.Kissat.FullM4BvaProof
public import LeanQbe.T.Examples.Kissat.FullM4TernaryProof
public import LeanQbe.T.Examples.Kissat.FullM4CompactProof
public import LeanQbe.T.Examples.Kissat.FullM4BumpProof
public import LeanQbe.T.Examples.Kissat.FullM4BcpProof

/-!
# Kissat `D-Full` Unified M4 `ModuleOk` Assembly (`FullM4Proof`, `231/231` Closed)

Assembles unconditional `231`-function `ModuleOk` for `FullM4.m4Module` (`externs := []`,
`exits := []`):
- `mkM4Env_moduleOk : ModuleOk (mkM4Env mainSpec) m4Module`
- `m4Env_moduleOk : ModuleOk m4Env m4Module`
- `m4UnsatEnv_moduleOk : ModuleOk m4UnsatEnv m4Module`

Transports all `193` unchanged/BVA-upgraded functions from `FullM4Bva.mkM4BvaFullEnv_moduleOk`,
closes `full_learn_clause` (`full_reduce(h, true)`) via `wp_env_agree_of_callsReduceTrue`, and
discharges all `37` new/upgraded/respecced M4 functions (`M4a` `13`, `M4c` `14`, `M4e` `1`, `M4g`
`1`, and `8` unified M4 orchestrators/`full_search`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Table-Agreement, List-Membership, & `full_reduce(h, true)` Transport Helpers -/

private theorem allFns_of_forall {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h =>
    ⟨h _ List.mem_cons_self, allFns_of_forall fun f hf => h f (List.mem_cons_of_mem _ hf)⟩

private theorem fn_eq_of_mem_nodup {fs : List Fn} (hnd : (fs.map Fn.name).Nodup)
    {f g : Fn} (hf : f ∈ fs) (hg : g ∈ fs) (hnm : f.name = g.name) : f = g := by
  induction fs with
  | nil => nomatch hf
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hf with rfl | hf' <;> rcases List.mem_cons.mp hg with rfl | hg'
    · rfl
    · exact absurd (hnm ▸ List.mem_map_of_mem hg') hnd.1
    · exact absurd (hnm.symm ▸ List.mem_map_of_mem hf') hnd.1
    · exact ih hnd.2 hf' hg'

private theorem m4_ofTable_iff {tbl : List SpecEntry} {e : SpecEntry} (he : e ∈ tbl)
    (hnd : (tbl.map SpecEntry.name).Nodup) {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs}
    {X : XPost} :
    Env.ofTable tbl e.name e.as e.rs xs m Q X ↔ e.eff xs m Q X := by
  induction tbl with
  | nil => nomatch he
  | cons e' es ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | hmem
    · exact Env.ofTable_cons_self _ _ _ _ _ _
    · have hne : e'.name ≠ e.name := fun h' => hnd.1 (h' ▸ List.mem_map_of_mem hmem)
      exact (Env.ofTable_cons_ne hne _ _ _ _).trans (ih hmem hnd.2)

private theorem ofTable_false_of_not_mem {tbl : List SpecEntry} {f : Sym}
    (hf : f ∉ tbl.map SpecEntry.name) {as bs : List Ty} (xs : Tup Val as) (m : Mem 64)
    (Q : Post bs) (X : XPost) : ¬ Env.ofTable tbl f as bs xs m Q X := by
  induction tbl with
  | nil => exact fun h => h
  | cons e es ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hf
    rw [Env.ofTable_cons_ne (Ne.symm hf.1)]
    exact ih hf.2

private theorem m4_ofTable_off_sig {tbl : List SpecEntry} {e : SpecEntry} (he : e ∈ tbl)
    (hnd : (tbl.map SpecEntry.name).Nodup) {as bs : List Ty}
    (hne : ¬ (e.as = as ∧ e.rs = bs))
    (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    ¬ Env.ofTable tbl e.name as bs xs m Q X := by
  induction tbl with
  | nil => nomatch he
  | cons e' es ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | hmem
    · intro h
      rcases h with ⟨⟨_, ha, hb⟩, _⟩ | ⟨_, htail⟩
      · exact hne ⟨ha, hb⟩
      · exact absurd htail (ofTable_false_of_not_mem hnd.1 xs m Q X)
    · have hne' : e'.name ≠ e.name := fun h' => hnd.1 (h' ▸ List.mem_map_of_mem hmem)
      rw [Env.ofTable_cons_ne hne']
      exact ih hmem hnd.2

private theorem m4_ofTable_agree_of_mem_both {tbl1 tbl2 : List SpecEntry} {e : SpecEntry}
    (he1 : e ∈ tbl1) (hnd1 : (tbl1.map SpecEntry.name).Nodup)
    (he2 : e ∈ tbl2) (hnd2 : (tbl2.map SpecEntry.name).Nodup)
    {as bs : List Ty} (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    Env.ofTable tbl1 e.name as bs xs m Q X ↔ Env.ofTable tbl2 e.name as bs xs m Q X := by
  by_cases hs : e.as = as ∧ e.rs = bs
  · rcases hs with ⟨rfl, rfl⟩
    exact (m4_ofTable_iff he1 hnd1).trans (m4_ofTable_iff he2 hnd2).symm
  · exact iff_of_false (m4_ofTable_off_sig he1 hnd1 hs xs m Q X)
      (m4_ofTable_off_sig he2 hnd2 hs xs m Q X)

private theorem wp_noExit_lift {Γ : Env} {rs : List Ty} {e : Expr Val Cont rs} {m : Mem 64}
    {Q : Post rs} {X : XPost} (h : wp Γ Q (fun _ _ _ _ => False) e m) :
    wp Γ Q X e m :=
  wp_mono (fun _ _ hq => hq) (fun _ _ _ _ hf => hf.elim) e m h

mutual
private def checkCallsReduceTrueExpr (allowed : List SigEntry) {rs : List Ty} :
    Expr (fun _ => Unit) (fun _ => Unit) rs → Bool
  | .let_ _ k => checkCallsReduceTrueExpr allowed (k (Tup.units _))
  | .load _ _ k => checkCallsReduceTrueExpr allowed (k ())
  | .store _ _ k => checkCallsReduceTrueExpr allowed k
  | .call f (as := as) (bs := bs) args k =>
      let okCall :=
        if f == "full_reduce" then
          match as, bs, args with
          | [.bits 64, .bool], [.bits 64], (_, Arg.imm true, ()) => true
          | _, _, _ => false
        else allowed.any (SigEntry.beq (f, as, bs))
      okCall && checkCallsReduceTrueExpr allowed (k (Tup.units bs))
  | .jnz _ t e => checkCallsReduceTrueExpr allowed t && checkCallsReduceTrueExpr allowed e
  | .jump _ _ | .ret _ | .hlt => true
  | .exit _ _ => false
  | .group (sig := sig) bodies k =>
      checkCallsReduceTrueBlocks allowed (bodies (Tup.units sig)) &&
        checkCallsReduceTrueExpr allowed (k (Tup.units sig))

private def checkCallsReduceTrueBlocks (allowed : List SigEntry) {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig → Bool
  | _, .nil => true
  | _, .cons b bs =>
      checkCallsReduceTrueExpr allowed (b (Tup.units _)) &&
        checkCallsReduceTrueBlocks allowed bs
end

private theorem checkCallsReduceTrueBlocks_get {allowed : List SigEntry} {rs : List Ty} :
    {sig : List (List Ty)} → {bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig} →
    checkCallsReduceTrueBlocks allowed bs = true → ∀ {ts} (i : Member ts sig),
    checkCallsReduceTrueExpr allowed (bs.get i (Tup.units ts)) = true
  | _, .cons _ _, h, _, .here => by
    simp only [checkCallsReduceTrueBlocks, Bool.and_eq_true] at h; exact h.1
  | _, .cons _ _, h, _, .there i => by
    simp only [checkCallsReduceTrueBlocks, Bool.and_eq_true] at h
    exact checkCallsReduceTrueBlocks_get h.2 i

private theorem wp_env_agree_of_callsReduceTrue {Γ Γ' : Env} {allowed : List SigEntry}
    {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx Val (fun _ => Unit)} {D : Ctx Cont (fun _ => Unit)}
    {e₁ : Expr Val Cont rs} {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) (hcalls : checkCallsReduceTrueExpr allowed e₂ = true)
    (hΓ : ∀ f as bs, (f, as, bs) ∈ allowed →
      ∀ xs m P E, Γ f as bs xs m P E → Γ' f as bs xs m P E)
    (hRed : ∀ (h : BitVec 64) m P E,
      Γ "full_reduce" [i64, .bool] [i64] (h, true, ()) m P E →
      Γ' "full_reduce" [i64, .bool] [i64] (h, true, ()) m P E) :
    ∀ m, wp Γ Q X e₁ m → wp Γ' Q X e₁ m := by
  induction hwf using Wf.induct with
  | let_ _ _ ih => intro m h; exact Op.wp_mono (fun r => ih r (Tup.units _) hcalls m) h
  | load _ _ _ ih => intro m ⟨v, hv, h⟩; exact ⟨v, hv, ih v () hcalls m h⟩
  | store _ _ _ ih => intro m ⟨hok, h⟩; exact ⟨hok, ih hcalls _ h⟩
  | call f hargs _ ih =>
    intro m ⟨P, E, hG, hP, hE⟩
    simp only [checkCallsReduceTrueExpr, Bool.and_eq_true] at hcalls
    rcases hcalls with ⟨hok, hk⟩
    refine ⟨P, E, ?_, fun r m' hr => ih r (Tup.units _) hk m' (hP r m' hr), hE⟩
    by_cases hf : f = "full_reduce"
    · subst hf
      simp only [beq_self_eq_true, ↓reduceIte] at hok
      split at hok
      · cases hargs with
        | cons _ htail =>
          cases htail with
          | cons hb hnil =>
            cases hnil
            cases hb
            exact hRed _ m P E hG
      · contradiction
    · simp only [beq_iff_eq, hf, ↓reduceIte, List.any_eq_true, SigEntry.beq_iff_eq] at hok
      rcases hok with ⟨s, hs, heq⟩
      exact hΓ f _ _ (heq ▸ hs) _ m P E hG
  | jnz _ _ _ iht ihe =>
    intro m h
    simp only [checkCallsReduceTrueExpr, Bool.and_eq_true] at hcalls
    exact ⟨fun hc => iht hcalls.1 m (h.1 hc), fun hc => ihe hcalls.2 m (h.2 hc)⟩
  | jump _ _ | ret _ | hlt => intro _ h; exact h
  | exit _ _ => simp [checkCallsReduceTrueExpr] at hcalls
  | group _ _ ihb ihk =>
    intro m h Js hc
    simp only [checkCallsReduceTrueExpr, Bool.and_eq_true] at hcalls
    refine ihk Js (Tup.units _) hcalls.2 m (h Js ?_)
    rw [closed_iff] at hc ⊢
    exact fun i xs m' hb => hc i xs m'
      (ihb Js (Tup.units _) i xs (Tup.units _) (checkCallsReduceTrueBlocks_get hcalls.1 i) m' hb)

/-! ## 2. Transport from `FullM4Bva` (`193` Unchanged/BVA-Upgraded Functions) -/

private def m4RespecBva4 : List Sym :=
  ["full_reduce", "full_preprocess", "full_simplify", "full_search"]

private def m4BvaChanged10 : List Sym :=
  [ "full_bva_hop1", "full_bva_hop2", "full_bva_hop3", "full_bva_pick_cand"
  , "full_bva_filter_row", "full_bva_commit", "full_bva_try_lit", "full_factor"
  , "full_eliminate", "full_preprocess" ]

private def m4AllowedFromBva : List SigEntry :=
  (FullM4Bva.m4BvaFullFns.filter (fun fn => !m4RespecBva4.contains fn.name)).map Fn.sig

private theorem m4BvaFullFns_nodup : (FullM4Bva.m4BvaFullFns.map Fn.name).Nodup := by
  have hchk := FullM4Bva.m4BvaFull_acyclic
  simp only [FullM4Bva.m4BvaFullModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem m4BvaSplice_name (f : Fn) : (FullM4Bva.m4BvaSplice f).name = f.name := by
  unfold FullM4Bva.m4BvaSplice
  repeat (first | rfl | (split; · next h => exact h.symm))

private theorem m4BvaSpecSplice_name (e : SpecEntry) :
    (FullM4Bva.m4BvaFullSpecSplice e).name = e.name := by
  unfold FullM4Bva.m4BvaFullSpecSplice
  repeat (first | rfl | (split; · next h => exact h.symm))

private theorem m4BvaSpecTable_names (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (FullM4Bva.m4BvaFullSpecTable mainSpec).map SpecEntry.name =
      FullM4Bva.m4BvaFullFns.map Fn.name := by
  unfold FullM4Bva.m4BvaFullSpecTable FullM4Bva.m4BvaFullFns
  have hm := congrArg (List.map Prod.fst) (FullM3.m3SpecTable_sigs mainSpec)
  simp only [List.map_map, Function.comp_def] at hm
  rw [List.map_map, List.map_map]
  calc
    (FullM3.m3SpecTable mainSpec).map (fun x => (FullM4Bva.m4BvaFullSpecSplice x).name)
      = (FullM3.m3SpecTable mainSpec).map SpecEntry.name :=
        List.map_congr_left fun e _ => m4BvaSpecSplice_name e
    _ = FullM3.m3Fns.map Fn.name := hm
    _ = FullM3.m3Fns.map (fun x => (FullM4Bva.m4BvaSplice x).name) :=
        (List.map_congr_left fun f _ => m4BvaSplice_name f).symm

private theorem m4BvaSpecTable_nodup (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((FullM4Bva.m4BvaFullSpecTable mainSpec).map SpecEntry.name).Nodup := by
  rw [m4BvaSpecTable_names]; exact m4BvaFullFns_nodup

private theorem m4Spec_slice1 (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m4SpecTable mainSpec).take 62 = (FullM4Bva.m4BvaFullSpecTable mainSpec).take 62 := by
  simp only [m4SpecTable, FullM4Bva.m4BvaFullSpecTable, FullM3.m3SpecTable]; rfl

private theorem m4Spec_slice2 (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((m4SpecTable mainSpec).drop 66).take 125 =
      ((FullM4Bva.m4BvaFullSpecTable mainSpec).drop 63).take 125 := by
  simp only [m4SpecTable, FullM4Bva.m4BvaFullSpecTable, FullM3.m3SpecTable]; rfl

private theorem m4Spec_slice3 (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    ((m4SpecTable mainSpec).drop 215).take 12 =
      ((FullM4Bva.m4BvaFullSpecTable mainSpec).drop 188).take 12 := by
  simp only [m4SpecTable, FullM4Bva.m4BvaFullSpecTable, FullM3.m3SpecTable]; rfl

private theorem m4Spec_row230 (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m4SpecTable mainSpec)[230]? =
      some ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩ := by
  simp only [m4SpecTable]; rfl

private theorem mem_m4Spec_of_mem_bva (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    {e : SpecEntry} (he : e ∈ FullM4Bva.m4BvaFullSpecTable mainSpec)
    (hn : m4RespecBva4.contains e.name = false) :
    e ∈ m4SpecTable mainSpec := by
  let tbl := FullM4Bva.m4BvaFullSpecTable mainSpec
  change e ∈ tbl at he
  have hdrop62 : tbl.drop 62 =
      ⟨"full_reduce", [i64, .bool], [i64], fullReduceSpec, true⟩ :: tbl.drop 63 := by
    simp only [tbl, FullM4Bva.m4BvaFullSpecTable, FullM3.m3SpecTable]; rfl
  have hdrop200 : tbl.drop 200 =
      [ ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩
      , ⟨"full_simplify", [i64, .bool, .bool], [i64], FullFastSched.schedSimplifySpec, true⟩
      , ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩
      , ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩ ] := by
    simp only [tbl, FullM4Bva.m4BvaFullSpecTable, FullM3.m3SpecTable]; rfl
  rw [← List.take_append_drop 62 tbl] at he
  rcases List.mem_append.mp he with h1 | hrest1
  · rw [← m4Spec_slice1 mainSpec] at h1
    exact List.mem_of_mem_take h1
  · rw [hdrop62, List.mem_cons] at hrest1
    rcases hrest1 with rfl | hrest2
    · simp [m4RespecBva4] at hn
    · rw [← List.take_append_drop 125 (tbl.drop 63), List.drop_drop] at hrest2
      rcases List.mem_append.mp hrest2 with h2 | hrest3
      · rw [← m4Spec_slice2 mainSpec] at h2
        exact List.mem_of_mem_drop (List.mem_of_mem_take h2)
      · rw [← List.take_append_drop 12 (tbl.drop 188), List.drop_drop] at hrest3
        rcases List.mem_append.mp hrest3 with h3 | hrest4
        · rw [← m4Spec_slice3 mainSpec] at h3
          exact List.mem_of_mem_drop (List.mem_of_mem_take h3)
        · rw [hdrop200] at hrest4
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hrest4
          rcases hrest4 with rfl | rfl | rfl | rfl
          · simp [m4RespecBva4] at hn
          · simp [m4RespecBva4] at hn
          · simp [m4RespecBva4] at hn
          · exact List.mem_of_getElem? (m4Spec_row230 mainSpec)

private theorem m4Env_agree_bva (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {f : Sym}
    (hf : m4RespecBva4.contains f = false)
    (hbva : f ∈ FullM4Bva.m4BvaFullFns.map Fn.name)
    {as bs : List Ty} (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    mkM4Env mainSpec f as bs xs m Q X ↔ FullM4Bva.mkM4BvaFullEnv mainSpec f as bs xs m Q X := by
  rw [← m4BvaSpecTable_names mainSpec, List.mem_map] at hbva
  obtain ⟨e, he_bva, rfl⟩ := hbva
  exact m4_ofTable_agree_of_mem_both (mem_m4Spec_of_mem_bva mainSpec he_bva hf)
    (m4SpecTable_nodup mainSpec) he_bva (m4BvaSpecTable_nodup mainSpec) xs m Q X

private theorem m4_transport_bva (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBva : ModuleOk (FullM4Bva.mkM4BvaFullEnv mainSpec) FullM4Bva.m4BvaFullModule)
    {fn : Fn} (hmem : fn ∈ FullM4Bva.m4BvaFullFns)
    (hnot_rsp : m4RespecBva4.contains fn.name = false)
    (hcalls : fn.callsOk m4AllowedFromBva [])
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (hs : mkM4Env mainSpec fn.name fn.as fn.rs xs m Q X) :
    Func.wp (mkM4Env mainSpec) fn.body xs m Q X := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have ⟨hwf, _, hwp0⟩ := hBva.fnsOk pre fn post hsplit
  have hs0 : FullM4Bva.mkM4BvaFullEnv mainSpec fn.name fn.as fn.rs xs m Q X :=
    (m4Env_agree_bva mainSpec hnot_rsp (List.mem_map_of_mem hmem) xs m Q X).mp hs
  refine wp_env_agree_of_callsOk (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units fn.as))
    hcalls (fun g as bs hmem_g ys m' P E hG => ?_) m (hwp0 xs m Q X hs0)
  obtain ⟨fn', hfn', hsig⟩ := List.mem_map.mp hmem_g
  have hfn'_f := (List.mem_filter.mp hfn').2
  have hg_nr : m4RespecBva4.contains g = false := by
    have hgn : fn'.name = g := congrArg Prod.fst hsig
    rw [← hgn]; simpa using hfn'_f
  have hg_bva : g ∈ FullM4Bva.m4BvaFullFns.map Fn.name := by
    have hgn : fn'.name = g := congrArg Prod.fst hsig
    rw [← hgn]; exact List.mem_map_of_mem (List.mem_filter.mp hfn').1
  exact (m4Env_agree_bva mainSpec hg_nr hg_bva ys m' P E).mpr hG

private def m4UnchPrefix : List Fn :=
  Full.fullFns.take 21 ++
  (Full.fullFns.drop 22).take 3 ++
  [FullM3VivChrono.m3TickRelFn] ++
  (Full.fullFns.drop 26).take 10 ++
  FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
  (Full.fullFns.drop 37).take 10 ++
  [FullM3VivChrono.m3PropLitFn] ++
  FastCore.fastCore_fns.drop 1 ++
  (Full.fullFns.drop 50).take 7 ++
  FullFastSched.sched_fns.take 1 ++
  (Full.fullFns.drop 58).take 3 ++
  (Full.fullFns.drop 62).take 1 ++
  [FullM3VivChrono.m3AnalyzeRsnFn] ++
  (Full.fullFns.drop 64).take 32 ++
  (Full.fullFns.drop 97).take 14 ++
  [FullM3.m3ProbeRunFn] ++
  (Full.fullFns.drop 112).take 1 ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
  (Full.fullFns.drop 114).take 5 ++
  [FullM3VivChrono.m3VivifyFn] ++
  (Full.fullFns.drop 120).take 1 ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
  (Full.fullFns.drop 122).take 3 ++
  (FullFastSched.sched_fns.drop 1).take 2 ++
  (Full.fullFns.drop 127).take 1

private def m4UnchSuffix : List Fn :=
  Full.fullKitten_fns ++
  (Full.fullFns.drop 128).take 7 ++
  (FullDefSweep.full_def_sweep_fns.drop 3).take 1 ++
  [ FullM3CongBva.m3MarkTrailFn
  , FullM3CongBva.m3UnitFoldFn
  , FullM3CongBva.m3EquivFoldFn
  , FullM3CongBva.m3AndMatchFn
  , FullM3CongBva.m3CongWorkStepFn
  , FullM3CongBva.m3CongruenceDenseFn ] ++
  FullDefSweep.full_def_sweep_fns.drop 5 ++
  (Full.fullFns.drop 145).take 2 ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++
  (Full.fullFns.drop 148).take 1 ++
  FullDefSweep.full_def_sweep_fns.take 3 ++
  (Full.fullFns.drop 151).take 5 ++
  FullFastBveBudgets.fastBveBudgets_fns.drop 6 ++
  (FullFastSched.sched_fns.drop 3).take 4 ++
  [FullM3.m3BackboneLitFn, FullM3.m3BackboneFn, FullM3.m3ProbeTailFn] ++
  (FullFastSched.sched_fns.drop 9).take 1 ++
  [FullM3CongBva.m3ElimCollectNbrsFn, FullM3CongBva.m3ElimBveFn]

private def m4UnchangedCore : List Fn := m4UnchPrefix ++ m4UnchSuffix

private theorem m4UnchangedCore_ok :
    m4UnchangedCore.all (fun fn =>
      !m4BvaChanged10.contains fn.name && !m4RespecBva4.contains fn.name &&
      (fn.name == "full_learn_clause" || fn.checkCallsOk m4AllowedFromBva [])) = true := by
  t_kernel_rfl

private theorem m4BvaFns_ok :
    m4BvaFns.all (fun fn =>
      !m4RespecBva4.contains fn.name && fn.checkCallsOk m4AllowedFromBva []) = true := by
  t_kernel_rfl

private def m4LearnClauseFn : Fn :=
  ⟨"full_learn_clause", [i64, i64], [i64], Full.full_learn_clause_body⟩

private theorem m4LearnClause_callsOk :
    checkCallsReduceTrueExpr m4AllowedFromBva
      (m4LearnClauseFn.body (fun _ => Unit) (fun _ => Unit) (Tup.units [i64, i64])) = true := by
  t_kernel_rfl

private theorem m4LearnClause_mem_m4 : m4LearnClauseFn ∈ m4Fns := by
  have h81 : Full.fullFns[81]? = some m4LearnClauseFn := rfl
  have hget : ((Full.fullFns.drop 64).take 32)[17]? = some m4LearnClauseFn := by
    rw [List.getElem?_take, List.getElem?_drop]; simp [h81]
  have hmem : m4LearnClauseFn ∈ (Full.fullFns.drop 64).take 32 := List.mem_of_getElem? hget
  simp only [m4Fns, m4FnsPrefix, List.mem_append, hmem, true_or, or_true]

private theorem forall_mem_append {α : Type _} {P : α → Prop} {a b : List α}
    (ha : ∀ x ∈ a, P x) (hb : ∀ x ∈ b, P x) : ∀ x ∈ a ++ b, P x :=
  fun x hx => (List.mem_append.mp hx).elim (ha x) (hb x)

private theorem forall_mem_cons {α : Type _} {P : α → Prop} {x : α} {a : List α}
    (hx : P x) (ha : ∀ y ∈ a, P y) : ∀ y ∈ x :: a, P y :=
  fun y hy => (List.mem_cons.mp hy).elim (fun e => e ▸ hx) (ha y)

private theorem forall_mem_one {α : Type _} {P : α → Prop} {x : α} (hx : P x) :
    ∀ y ∈ [x], P y :=
  fun _ hy => (List.mem_singleton.mp hy) ▸ hx

private theorem mem_take_of_mem_drop_take {α : Type _} {xs : List α} {a b n : Nat}
    (h : a + b ≤ n) {x : α} (hx : x ∈ (xs.drop a).take b) : x ∈ xs.take n := by
  have ht := List.take_append_drop a (xs.take n)
  rw [List.take_take, Nat.min_eq_left (Nat.le_trans (Nat.le_add_right a b) h)] at ht
  rw [← ht]
  refine List.mem_append_right _ ?_
  have hd : (xs.take n).drop a = (xs.drop a).take (n - a) := List.drop_take
  rw [hd]
  have ht2 := List.take_append_drop b ((xs.drop a).take (n - a))
  rw [List.take_take, Nat.min_eq_left (by omega)] at ht2
  rw [← ht2]
  exact List.mem_append_left _ hx

private theorem mem_drop_take_sub {α : Type _} {xs : List α} {a0 b0 a b : Nat}
    (ha : a0 ≤ a) (hb : a + b ≤ a0 + b0) {x : α}
    (hx : x ∈ (xs.drop a).take b) : x ∈ (xs.drop a0).take b0 := by
  have hx' : x ∈ ((xs.drop a0).drop (a - a0)).take b := by
    rwa [List.drop_drop, show a0 + (a - a0) = a by omega]
  exact mem_take_of_mem_drop_take (by omega) hx'

private theorem m4UnchPrefix_mem_m3 : ∀ f ∈ m4UnchPrefix, f ∈ FullM3.m3FnsPrefix := by
  unfold m4UnchPrefix
  repeat' apply forall_mem_append
  · exact fun _ h => by
      have h1 := mem_take_of_mem_drop_take (a := 0) (b := 21) (n := 25)
        (by decide) (by simpa using h)
      simp [FullM3.m3FnsPrefix, h1]
  · exact fun _ h => by
      have h1 := mem_take_of_mem_drop_take (a := 22) (b := 3) (n := 25) (by decide) h
      simp [FullM3.m3FnsPrefix, h1]
  · exact forall_mem_one (by simp [FullM3.m3FnsPrefix])
  · exact fun _ h => by simp [FullM3.m3FnsPrefix, h]
  · exact fun _ h => by simp [FullM3.m3FnsPrefix, h]
  · exact fun _ h => by simp [FullM3.m3FnsPrefix, h]
  · exact forall_mem_one (by simp [FullM3.m3FnsPrefix])
  · exact fun _ h => by rw [List.drop_one] at h; simp [FullM3.m3FnsPrefix, h]
  · exact fun _ h => by simp [FullM3.m3FnsPrefix, h]
  · exact fun _ h => by simp [FullM3.m3FnsPrefix, h]
  · exact fun _ h => by
      have h1 := mem_drop_take_sub (a0 := 58) (b0 := 5) (a := 58) (b := 3)
        (by decide) (by decide) h
      simp [FullM3.m3FnsPrefix, h1]
  · exact fun _ h => by
      have h1 := mem_drop_take_sub (a0 := 58) (b0 := 5) (a := 62) (b := 1)
        (by decide) (by decide) h
      simp [FullM3.m3FnsPrefix, h1]
  · exact forall_mem_one (by simp [FullM3.m3FnsPrefix])
  · exact fun _ h => by
      have h1 := mem_drop_take_sub (a0 := 64) (b0 := 47) (a := 64) (b := 32)
        (by decide) (by decide) h
      simp [FullM3.m3FnsPrefix, h1]
  · exact fun _ h => by
      have h1 := mem_drop_take_sub (a0 := 64) (b0 := 47) (a := 97) (b := 14)
        (by decide) (by decide) h
      simp [FullM3.m3FnsPrefix, h1]
  · exact forall_mem_one (by simp [FullM3.m3FnsPrefix])
  · exact fun _ h => by simp [FullM3.m3FnsPrefix, h]
  · exact fun _ h => by simp [FullM3.m3FnsPrefix, h]
  · exact fun _ h => by simp [FullM3.m3FnsPrefix, h]
  · exact forall_mem_one (by simp [FullM3.m3FnsPrefix])
  · exact fun _ h => by simp [FullM3.m3FnsPrefix, h]
  · exact fun _ h => by simp [FullM3.m3FnsPrefix, h]
  · exact fun _ h => by simp [FullM3.m3FnsPrefix, h]
  · exact fun _ h => by rw [List.drop_one] at h; simp [FullM3.m3FnsPrefix, h]
  · exact fun _ h => by simp [FullM3.m3FnsPrefix, h]

private theorem m4UnchSuffix_mem_m3 : ∀ f ∈ m4UnchSuffix, f ∈ FullM3.m3FnsSuffix := by
  unfold m4UnchSuffix
  repeat' apply forall_mem_append
  · exact fun _ h => by simp [FullM3.m3FnsSuffix, h]
  · exact fun _ h => by simp [FullM3.m3FnsSuffix, h]
  · exact fun _ h => by simp [FullM3.m3FnsSuffix, h]
  · refine forall_mem_cons ?_ (forall_mem_cons ?_ (forall_mem_cons ?_
        (forall_mem_cons ?_ (forall_mem_cons ?_ (forall_mem_one ?_))))) <;>
      simp [FullM3.m3FnsSuffix]
  · exact fun _ h => by simp [FullM3.m3FnsSuffix, h]
  · exact fun _ h => by simp [FullM3.m3FnsSuffix, h]
  · exact fun _ h => by simp [FullM3.m3FnsSuffix, h]
  · exact fun _ h => by simp [FullM3.m3FnsSuffix, h]
  · exact fun _ h => by simp [FullM3.m3FnsSuffix, h]
  · exact fun _ h => by simp [FullM3.m3FnsSuffix, h]
  · exact fun _ h => by simp [FullM3.m3FnsSuffix, h]
  · exact fun _ h => by simp [FullM3.m3FnsSuffix, h]
  · exact fun _ h => by
      simp only [FullM3.m3FnsSuffix] at h ⊢
      rcases List.mem_cons.mp h with rfl | h
      · simp
      · rcases List.mem_cons.mp h with rfl | h
        · simp
        · rw [List.mem_singleton.mp h]; simp
  · exact fun _ h => by simp [FullM3.m3FnsSuffix, h]
  · refine forall_mem_cons ?_ (forall_mem_one ?_) <;>
      simp [FullM3.m3FnsSuffix]

private theorem m4UnchangedCore_mem_bva {f : Fn} (hf : f ∈ m4UnchangedCore) :
    f ∈ FullM4Bva.m4BvaFullFns := by
  have hm3 : f ∈ FullM3.m3Fns := by
    unfold m4UnchangedCore at hf
    rcases List.mem_append.mp hf with hp | hs
    · exact List.mem_append_left _ (m4UnchPrefix_mem_m3 f hp)
    · exact List.mem_append_right _ (m4UnchSuffix_mem_m3 f hs)
  have hall := List.all_eq_true.mp m4UnchangedCore_ok f hf
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hall
  have hnot_chg : m4BvaChanged10.contains f.name = false := hall.1.1
  have hsp : FullM4Bva.m4BvaSplice f = f := by
    unfold FullM4Bva.m4BvaSplice
    simp only [m4BvaChanged10, List.contains_cons, List.contains_nil, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne] at hnot_chg
    rcases hnot_chg with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  rw [← hsp]
  exact List.mem_map_of_mem hm3

private theorem m4BvaFns_mem_bva {f : Fn} (hf : f ∈ m4BvaFns) :
    f ∈ FullM4Bva.m4BvaFullFns := by
  have hsub : m4BvaFns = FullBvaHeap.bvaHeap_fns.map FullM4Bva.m4BvaSplice := rfl
  rw [hsub, List.mem_map] at hf
  obtain ⟨g, hg, rfl⟩ := hf
  have hm3 : g ∈ FullM3.m3Fns := by
    simp only [FullM3.m3Fns, FullM3.m3FnsSuffix, List.mem_append, hg, true_or, or_true]
  exact List.mem_map_of_mem hm3

private theorem m4UnchangedCore_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBva : ModuleOk (FullM4Bva.mkM4BvaFullEnv mainSpec) FullM4Bva.m4BvaFullModule)
    {fn : Fn} (hf : fn ∈ m4UnchangedCore) :
    ∀ xs m Q X, mkM4Env mainSpec fn.name fn.as fn.rs xs m Q X →
      Func.wp (mkM4Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM4Env mainSpec
  by_cases hlc : fn.name = "full_learn_clause"
  · have hm4 : fn ∈ m4Fns := by
      have hm3 : fn ∈ FullM3.m3Fns := by
        unfold m4UnchangedCore at hf
        rcases List.mem_append.mp hf with hp | hs
        · exact List.mem_append_left _ (m4UnchPrefix_mem_m3 fn hp)
        · exact List.mem_append_right _ (m4UnchSuffix_mem_m3 fn hs)
      unfold m4UnchangedCore at hf
      have h81 : Full.fullFns[81]? = some m4LearnClauseFn := rfl
      have hget : ((Full.fullFns.drop 64).take 32)[17]? = some m4LearnClauseFn := by
        rw [List.getElem?_take, List.getElem?_drop]; simp [h81]
      have hm3_lc : m4LearnClauseFn ∈ FullM3.m3Fns := by
        have hmem := List.mem_of_getElem? hget
        have h1 := mem_drop_take_sub (a0 := 64) (b0 := 47) (a := 64) (b := 32)
          (by decide) (by decide) hmem
        simp [FullM3.m3Fns, FullM3.m3FnsPrefix, h1]
      have hm3_nd : (FullM3.m3Fns.map Fn.name).Nodup := by
        have hchk := FullM3.m3_acyclic
        simp only [FullM3.m3Module, Module.checkAcyclic, Bool.and_eq_true] at hchk
        exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1
      rw [fn_eq_of_mem_nodup hm3_nd hm3 hm3_lc hlc]
      exact m4LearnClause_mem_m4
    have hfeq : fn = m4LearnClauseFn :=
      fn_eq_of_mem_nodup m4Fns_nodup hm4 m4LearnClause_mem_m4 hlc
    subst hfeq
    intro xs m Q X hs
    let h14 := mkM4Env_row_at (mainSpec := mainSpec) 14
      ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
    let h27 := mkM4Env_row_at (mainSpec := mainSpec) 27
      ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
    let h30 := mkM4Env_row_at (mainSpec := mainSpec) 30
      ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
    let h31 := mkM4Env_row_at (mainSpec := mainSpec) 31
      ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], fullAddClauseSpec, true⟩
    let h65 := mkM4Env_row_at (mainSpec := mainSpec) 65
      ⟨"full_reduce", [i64, .bool], [i64], m4ReduceSpec, true⟩
    let h81 := mkM4Env_row_at (mainSpec := mainSpec) 81
      ⟨"full_det_new_level", [i64, i64], [i64], fullDetNewLevelSpec, true⟩
    let h84 := mkM4Env_row_at (mainSpec := mainSpec) 84
      ⟨"full_eager_subsume", [i64, i64], [], fullEagerSubsumeSpec, true⟩
    let Γ' : Env := fun f as bs =>
      if f = "full_reduce" then
        fun ys m' Q' X' => match as, bs, ys with
          | [.bits 64, .bool], [.bits 64], ys => fullReduceSpec ys m' Q' X'
          | _, _, _ => False
      else Γ f as bs
    have hspec := mkM4Env_row_elim 85 ⟨"full_learn_clause", [i64, i64], [i64],
      fullLearnClauseSpec, true⟩ rfl rfl hs
    have hwp' : Func.wp Γ' m4LearnClauseFn.body xs m Q (fun _ _ _ _ => False) :=
      full_learn_clause_bridge_wp Γ' h30 h27 h81 h14 (fun _ _ _ _ h => by simpa [Γ'] using h)
        h31 h84 xs m Q _ hspec
    have hwf := Full.fullFns_wf _ (List.mem_of_getElem? (show Full.fullFns[81]? =
      some m4LearnClauseFn from rfl)) Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units _)
    refine wp_noExit_lift (wp_env_agree_of_callsReduceTrue hwf m4LearnClause_callsOk
      (fun g as bs hmem ys m' P E hG => ?_) (fun hh m' P E hG => h65 (hh, true, ()) m' P E hG)
      m hwp')
    obtain ⟨fn', hfn', hsig⟩ := List.mem_map.mp hmem
    have hnr : m4RespecBva4.contains g = false := by
      have hgn : fn'.name = g := congrArg Prod.fst hsig
      rw [← hgn]; simpa using (List.mem_filter.mp hfn').2
    have hne : g ≠ "full_reduce" := by
      intro h; rw [h] at hnr; cases hnr
    simpa [Γ', hne] using hG
  · intro xs m Q X hs
    have hall := List.all_eq_true.mp m4UnchangedCore_ok fn hf
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hall
    have hcalls : fn.callsOk m4AllowedFromBva [] :=
      Fn.callsOk_of_checkCallsOk (hall.2.resolve_left hlc)
    exact m4_transport_bva mainSpec hBva (m4UnchangedCore_mem_bva hf) hall.1.2 hcalls hs

/-! ## 3. New & Upgraded M4 Functions (`m4PromoteFns`, `compact_fns`, `m4ReorderTernaryFns`) -/

private theorem m4_promote_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    {fn : Fn} (hmem : fn ∈ m4PromoteFns) :
    ∀ xs m Q X, mkM4Env mainSpec fn.name fn.as fn.rs xs m Q X →
      Func.wp (mkM4Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM4Env mainSpec
  let h62 := mkM4Env_row_at (mainSpec := mainSpec) 62
    ⟨"full_compute_lbd", [i64, i32], [i32], FullM4Ternary.fullComputeLbdSpec, true⟩
  let h63 := mkM4Env_row_at (mainSpec := mainSpec) 63
    ⟨"full_promote_clause", [i64, i32], [.bool], FullM4Ternary.fullPromoteClauseSpec, true⟩
  unfold m4PromoteFns FullM4Ternary.full_m4_ternary_fns at hmem
  simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl <;> intro xs m Q X hs
  · exact wp_noExit_lift (FullM4Ternary.full_compute_lbd_wp Γ xs m Q _
      (mkM4Env_row_elim 62 ⟨"full_compute_lbd", [i64, i32], [i32],
        FullM4Ternary.fullComputeLbdSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Ternary.full_promote_clause_wp Γ h62 xs m Q _
      (mkM4Env_row_elim 63 ⟨"full_promote_clause", [i64, i32], [.bool],
        FullM4Ternary.fullPromoteClauseSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Ternary.full_promote_reasons_wp Γ h63 xs m Q _
      (mkM4Env_row_elim 64 ⟨"full_promote_reasons", [i64], [i64],
        FullM4Ternary.fullPromoteReasonsSpec, true⟩ rfl rfl hs))

private theorem m4_compact_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    {fn : Fn} (hmem : fn ∈ FullM4Compact.compact_fns) :
    ∀ xs m Q X, mkM4Env mainSpec fn.name fn.as fn.rs xs m Q X →
      Func.wp (mkM4Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM4Env mainSpec
  let h11 := mkM4Env_row_at (mainSpec := mainSpec) 11
    ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  let h14 := mkM4Env_row_at (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let h15 := mkM4Env_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h30 := mkM4Env_row_at (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let h50 := mkM4Env_row_at (mainSpec := mainSpec) 50
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let h60 := mkM4Env_row_at (mainSpec := mainSpec) 60
    ⟨"full_rewatch_arena", [i64, i64], [.bool], fullRewatchArenaSpec, true⟩
  let h61 := mkM4Env_row_at (mainSpec := mainSpec) 61
    ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  let h192 := mkM4Env_row_at (mainSpec := mainSpec) 192
    ⟨"full_compact_flush", [i64], [i64], FullM4Compact.fullCompactFlushSpec, true⟩
  let h193 := mkM4Env_row_at (mainSpec := mainSpec) 193
    ⟨"full_compact_mark_live", [i64], [], FullM4Compact.fullCompactMarkLiveSpec, true⟩
  let h194 := mkM4Env_row_at (mainSpec := mainSpec) 194
    ⟨"full_compact_assign_map", [i64], [i64], FullM4Compact.fullCompactAssignMapSpec, true⟩
  let h195 := mkM4Env_row_at (mainSpec := mainSpec) 195
    ⟨"full_compact_record_ext", [i64, i64, i64], [], FullM4Compact.fullCompactRecordExtSpec, true⟩
  let h196 := mkM4Env_row_at (mainSpec := mainSpec) 196
    ⟨"full_compact_bins", [i64, i64, i64], [], FullM4Compact.fullCompactBinsSpec, true⟩
  let h197 := mkM4Env_row_at (mainSpec := mainSpec) 197
    ⟨"full_compact_arena", [i64, i64], [i64], FullM4Compact.fullCompactArenaSpec, true⟩
  let h198 := mkM4Env_row_at (mainSpec := mainSpec) 198
    ⟨"full_compact_vars", [i64, i64, i64], [], FullM4Compact.fullCompactVarsSpec, true⟩
  let h199 := mkM4Env_row_at (mainSpec := mainSpec) 199
    ⟨"full_compact_sift_q", [i64, i64, i64, i64], [], FullM4Compact.fullCompactSiftQSpec, true⟩
  let h200 := mkM4Env_row_at (mainSpec := mainSpec) 200
    ⟨"full_compact_vmtf", [i64, i64], [], FullM4Compact.fullCompactVmtfSpec, true⟩
  let h201 := mkM4Env_row_at (mainSpec := mainSpec) 201
    ⟨"full_compact_sift_h", [i64, i64, i64, i64, i64], [],
      FullM4Compact.fullCompactSiftHSpec, true⟩
  let h202 := mkM4Env_row_at (mainSpec := mainSpec) 202
    ⟨"full_compact_heap", [i64, i64], [], FullM4Compact.fullCompactHeapSpec, true⟩
  unfold FullM4Compact.compact_fns at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  intro xs m Q X hs
  · exact wp_noExit_lift (FullM4Compact.full_compact_needed_wp Γ xs m Q _
      (mkM4Env_row_elim 191 ⟨"full_compact_needed", [i64], [.bool],
        FullM4Compact.fullCompactNeededSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Compact.full_compact_flush_wp Γ h30 h50 h61 xs m Q _
      (mkM4Env_row_elim 192 ⟨"full_compact_flush", [i64], [i64],
        FullM4Compact.fullCompactFlushSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Compact.full_compact_mark_live_wp Γ h11 xs m Q _
      (mkM4Env_row_elim 193 ⟨"full_compact_mark_live", [i64], [],
        FullM4Compact.fullCompactMarkLiveSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Compact.full_compact_assign_map_wp Γ xs m Q _
      (mkM4Env_row_elim 194 ⟨"full_compact_assign_map", [i64], [i64],
        FullM4Compact.fullCompactAssignMapSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Compact.full_compact_record_ext_wp Γ xs m Q _
      (mkM4Env_row_elim 195 ⟨"full_compact_record_ext", [i64, i64, i64], [],
        FullM4Compact.fullCompactRecordExtSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Compact.full_compact_bins_wp Γ xs m Q _
      (mkM4Env_row_elim 196 ⟨"full_compact_bins", [i64, i64, i64], [],
        FullM4Compact.fullCompactBinsSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Compact.full_compact_arena_wp Γ h11 h15 xs m Q _
      (mkM4Env_row_elim 197 ⟨"full_compact_arena", [i64, i64], [i64],
        FullM4Compact.fullCompactArenaSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Compact.full_compact_vars_wp Γ xs m Q _
      (mkM4Env_row_elim 198 ⟨"full_compact_vars", [i64, i64, i64], [],
        FullM4Compact.fullCompactVarsSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Compact.full_compact_sift_q_wp Γ xs m Q _
      (mkM4Env_row_elim 199 ⟨"full_compact_sift_q", [i64, i64, i64, i64], [],
        FullM4Compact.fullCompactSiftQSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Compact.full_compact_vmtf_wp Γ h199 xs m Q _
      (mkM4Env_row_elim 200 ⟨"full_compact_vmtf", [i64, i64], [],
        FullM4Compact.fullCompactVmtfSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Compact.full_compact_sift_h_wp Γ xs m Q _
      (mkM4Env_row_elim 201 ⟨"full_compact_sift_h", [i64, i64, i64, i64, i64], [],
        FullM4Compact.fullCompactSiftHSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Compact.full_compact_heap_wp Γ h201 xs m Q _
      (mkM4Env_row_elim 202 ⟨"full_compact_heap", [i64, i64], [],
        FullM4Compact.fullCompactHeapSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Compact.full_compact_wp Γ h192 h193 h194 h195 h196 h14 h197
      h198 h200 h202 h60 xs m Q _
      (mkM4Env_row_elim 203 ⟨"full_compact", [i64], [i64], FullM4Compact.fullCompactSpec, true⟩
        rfl rfl hs))

private theorem m4_reorder_ternary_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    {fn : Fn} (hmem : fn ∈ m4ReorderTernaryFns) :
    ∀ xs m Q X, mkM4Env mainSpec fn.name fn.as fn.rs xs m Q X →
      Func.wp (mkM4Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM4Env mainSpec
  let h10 := mkM4Env_row_at (mainSpec := mainSpec) 10
    ⟨"full_rng_next", [i64], [i64], fullRngNextSpec, true⟩
  let h11 := mkM4Env_row_at (mainSpec := mainSpec) 11
    ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  let h18 := mkM4Env_row_at (mainSpec := mainSpec) 18
    ⟨"full_heap_push", [i64, i32], [], fullHeapPushSpec, true⟩
  let h30 := mkM4Env_row_at (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let h50 := mkM4Env_row_at (mainSpec := mainSpec) 50
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let h102 := mkM4Env_row_at (mainSpec := mainSpec) 102
    ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  let h204 := mkM4Env_row_at (mainSpec := mainSpec) 204
    ⟨"full_score_sift", [i64, i64, i64], [], FullM4Ternary.fullScoreSiftSpec, true⟩
  let h205 := mkM4Env_row_at (mainSpec := mainSpec) 205
    ⟨"full_reorder_queue", [i64], [i64], FullM4Ternary.fullReorderQueueSpec, true⟩
  let h206 := mkM4Env_row_at (mainSpec := mainSpec) 206
    ⟨"full_reorder_heap", [i64], [i64], FullM4Ternary.fullReorderHeapSpec, true⟩
  let h207 := mkM4Env_row_at (mainSpec := mainSpec) 207
    ⟨"full_tumble_clause", [i64, i32], [.bool], FullM4Ternary.fullTumbleClauseSpec, true⟩
  let h208 := mkM4Env_row_at (mainSpec := mainSpec) 208
    ⟨"full_tumble_clauses", [i64, i64], [i64], FullM4Ternary.fullTumbleClausesSpec, true⟩
  let h210 := mkM4Env_row_at (mainSpec := mainSpec) 210
    ⟨"full_ternary_match_bin", [i32, i32, i32, i32, i32, i32], [.bool],
      FullM4Ternary.fullTernaryMatchBinSpec, true⟩
  let h211 := mkM4Env_row_at (mainSpec := mainSpec) 211
    ⟨"full_ternary_collect", [i64, i64], [i64], FullM4Ternary.fullTernaryCollectSpec, true⟩
  let h212 := mkM4Env_row_at (mainSpec := mainSpec) 212
    ⟨"full_ternary_resolve_bin", [i64, i32, i32], [i64],
      FullM4Ternary.fullTernaryResolveBinSpec, true⟩
  let h213 := mkM4Env_row_at (mainSpec := mainSpec) 213
    ⟨"full_ternary_round", [i64, i64, i64], [i64], FullM4Ternary.fullTernaryRoundSpec, true⟩
  unfold m4ReorderTernaryFns FullM4Ternary.full_m4_ternary_fns at hmem
  simp only [List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  intro xs m Q X hs
  · exact wp_noExit_lift (FullM4Ternary.full_score_sift_wp Γ xs m Q _
      (mkM4Env_row_elim 204 ⟨"full_score_sift", [i64, i64, i64], [],
        FullM4Ternary.fullScoreSiftSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Ternary.full_reorder_queue_wp Γ h204 xs m Q _
      (mkM4Env_row_elim 205 ⟨"full_reorder_queue", [i64], [i64],
        FullM4Ternary.fullReorderQueueSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Ternary.full_reorder_heap_wp Γ h18 xs m Q _
      (mkM4Env_row_elim 206 ⟨"full_reorder_heap", [i64], [i64],
        FullM4Ternary.fullReorderHeapSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Ternary.full_tumble_clause_wp Γ h10 xs m Q _
      (mkM4Env_row_elim 207 ⟨"full_tumble_clause", [i64, i32], [.bool],
        FullM4Ternary.fullTumbleClauseSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Ternary.full_tumble_clauses_wp Γ h11 h207 xs m Q _
      (mkM4Env_row_elim 208 ⟨"full_tumble_clauses", [i64, i64], [i64],
        FullM4Ternary.fullTumbleClausesSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (m4_reorder_wp Γ h205 h206 h208 xs m Q _
      (mkM4Env_row_elim 209 ⟨"full_reorder", [i64, i64], [i64], m4ReorderSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Ternary.full_ternary_match_bin_wp Γ xs m Q _
      (mkM4Env_row_elim 210 ⟨"full_ternary_match_bin", [i32, i32, i32, i32, i32, i32], [.bool],
        FullM4Ternary.fullTernaryMatchBinSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Ternary.full_ternary_collect_wp Γ h11 xs m Q _
      (mkM4Env_row_elim 211 ⟨"full_ternary_collect", [i64, i64], [i64],
        FullM4Ternary.fullTernaryCollectSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Ternary.full_ternary_resolve_bin_wp Γ h210 h102 xs m Q _
      (mkM4Env_row_elim 212 ⟨"full_ternary_resolve_bin", [i64, i32, i32], [i64],
        FullM4Ternary.fullTernaryResolveBinSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Ternary.full_ternary_round_wp Γ h212 h50 xs m Q _
      (mkM4Env_row_elim 213 ⟨"full_ternary_round", [i64, i64, i64], [i64],
        FullM4Ternary.fullTernaryRoundSpec, true⟩ rfl rfl hs))
  · exact wp_noExit_lift (FullM4Ternary.full_ternary_wp Γ h30 h50 h211 h213 xs m Q _
      (mkM4Env_row_elim 214 ⟨"full_ternary", [i64, i64, i64], [i64],
        FullM4Ternary.fullTernarySpec, true⟩ rfl rfl hs))

/-! ## 4. Unconditional Closed `231/231` `ModuleOk` Assembly -/

private theorem m4_bva_all_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBva : ModuleOk (FullM4Bva.mkM4BvaFullEnv mainSpec) FullM4Bva.m4BvaFullModule) :
    ∀ fn ∈ m4BvaFns, ∀ xs m Q X, mkM4Env mainSpec fn.name fn.as fn.rs xs m Q X →
      Func.wp (mkM4Env mainSpec) fn.body xs m Q X := by
  intro fn h xs m Q X hs
  have hall := List.all_eq_true.mp m4BvaFns_ok fn h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hall
  exact m4_transport_bva mainSpec hBva (m4BvaFns_mem_bva h) hall.1
    (Fn.callsOk_of_checkCallsOk hall.2) hs

private theorem m4Prefix_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hBva : ModuleOk (FullM4Bva.mkM4BvaFullEnv mainSpec) FullM4Bva.m4BvaFullModule) :
    ∀ fn ∈ m4FnsPrefix, ∀ xs m Q X, mkM4Env mainSpec fn.name fn.as fn.rs xs m Q X →
      Func.wp (mkM4Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM4Env mainSpec
  have unch : ∀ {g : Fn}, g ∈ m4UnchPrefix →
      ∀ xs m Q X, Γ g.name g.as g.rs xs m Q X → Func.wp Γ g.body xs m Q X :=
    fun hg => m4UnchangedCore_wp mainSpec hBva (List.mem_append_left _ hg)
  unfold m4FnsPrefix
  repeat' (first
    | exact fun _ h => m4_promote_wp mainSpec h
    | apply forall_mem_append)
  · exact fun _ h => unch (by simp [m4UnchPrefix, h])
  · refine forall_mem_one fun xs m Q X hs => ?_
    let h16 := mkM4Env_row_at (mainSpec := mainSpec) 16
      ⟨"full_heap_up", [i64, i32], [], fullHeapUpSpec, true⟩
    let h20 := mkM4Env_row_at (mainSpec := mainSpec) 20
      ⟨"full_rescale", [i64], [], fullRescaleSpec, true⟩
    exact wp_noExit_lift (FullM4Bump.full_bump_var_m4_wp Γ h16 h20 xs m Q _
      (mkM4Env_row_elim 21 ⟨"full_bump_var", [i64, i32], [], fullBumpVarSpec, true⟩ rfl rfl hs))
  · exact fun _ h => unch (by simp [m4UnchPrefix, h])
  · exact forall_mem_one (unch (by simp [m4UnchPrefix]))
  · exact fun _ h => unch (by simp [m4UnchPrefix, h])
  · exact fun _ h => unch (by simp [m4UnchPrefix, h])
  · exact fun _ h => unch (by simp [m4UnchPrefix, h])
  · refine forall_mem_cons (fun xs m Q X hs => ?_) (forall_mem_one (unch (by simp [m4UnchPrefix])))
    let h15 := mkM4Env_row_at (mainSpec := mainSpec) 15
      ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
    exact wp_noExit_lift (FullM4Bcp.full_prop_lit_m4_wp Γ h15 xs m Q _
      (mkM4Env_row_elim 47 ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool],
        fullPropLitSpec, true⟩ rfl rfl hs))
  · exact fun _ h => unch (by rw [List.drop_one] at h; simp [m4UnchPrefix, h])
  · exact fun _ h => unch (by simp [m4UnchPrefix, h])
  · exact fun _ h => unch (by simp [m4UnchPrefix, h])
  · exact fun _ h => unch (by simp [m4UnchPrefix, h])
  · refine forall_mem_one fun xs m Q X hs => ?_
    let h8 := mkM4Env_row_at (mainSpec := mainSpec) 8
      ⟨"full_isqrt", [i64], [i64], fullIsqrtSpec, true⟩
    let h9 := mkM4Env_row_at (mainSpec := mainSpec) 9
      ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
    let h11 := mkM4Env_row_at (mainSpec := mainSpec) 11
      ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
    let h30 := mkM4Env_row_at (mainSpec := mainSpec) 30
      ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
    let h50 := mkM4Env_row_at (mainSpec := mainSpec) 50
      ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
    let h51 := mkM4Env_row_at (mainSpec := mainSpec) 51
      ⟨"full_recompute_tiers", [i64], [], fullRecomputeTiersSpec, true⟩
    let h52 := mkM4Env_row_at (mainSpec := mainSpec) 52
      ⟨"full_mark_reasons", [i64, .bool], [], fullMarkReasonsSpec, true⟩
    let h55 := mkM4Env_row_at (mainSpec := mainSpec) 55
      ⟨"full_sort_reds", [i64, i64], [], fullSortRedsSpec, true⟩
    let h61 := mkM4Env_row_at (mainSpec := mainSpec) 61
      ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
    let h64 := mkM4Env_row_at (mainSpec := mainSpec) 64
      ⟨"full_promote_reasons", [i64], [i64], FullM4Ternary.fullPromoteReasonsSpec, true⟩
    exact wp_noExit_lift (m4_reduce_wp Γ h8 h9 h11 h64 h51 h52 h55 h30 h50 h61 xs m Q _
      (mkM4Env_row_elim 65 ⟨"full_reduce", [i64, .bool], [i64], m4ReduceSpec, true⟩ rfl rfl hs))
  · exact fun _ h => unch (by simp [m4UnchPrefix, h])
  · exact forall_mem_one (unch (by simp [m4UnchPrefix]))
  · exact fun _ h => unch (by simp [m4UnchPrefix, h])
  · refine forall_mem_one fun xs m Q X hs => ?_
    exact wp_noExit_lift (m4_extend_wp Γ xs m Q _
      (mkM4Env_row_elim 100 ⟨"full_extend", [i64], [], fullExtendSpec, true⟩ rfl rfl hs))
  · exact fun _ h => unch (by simp [m4UnchPrefix, h])
  · exact forall_mem_one (unch (by simp [m4UnchPrefix]))
  · exact fun _ h => unch (by simp [m4UnchPrefix, h])
  · exact fun _ h => unch (by simp [m4UnchPrefix, h])
  · exact fun _ h => unch (by simp [m4UnchPrefix, h])
  · exact forall_mem_one (unch (by simp [m4UnchPrefix]))
  · exact fun _ h => unch (by simp [m4UnchPrefix, h])
  · exact fun _ h => unch (by simp [m4UnchPrefix, h])
  · exact fun _ h => unch (by simp [m4UnchPrefix, h])
  · exact fun _ h => unch (by rw [List.drop_one] at h; simp [m4UnchPrefix, h])
  · exact fun _ h => unch (by simp [m4UnchPrefix, h])

private theorem m4Suffix_wp (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X)
    (hBva : ModuleOk (FullM4Bva.mkM4BvaFullEnv mainSpec) FullM4Bva.m4BvaFullModule) :
    ∀ fn ∈ m4FnsSuffix, ∀ xs m Q X, mkM4Env mainSpec fn.name fn.as fn.rs xs m Q X →
      Func.wp (mkM4Env mainSpec) fn.body xs m Q X := by
  let Γ := mkM4Env mainSpec
  have unch : ∀ {g : Fn}, g ∈ m4UnchSuffix →
      ∀ xs m Q X, Γ g.name g.as g.rs xs m Q X → Func.wp Γ g.body xs m Q X :=
    fun hg => m4UnchangedCore_wp mainSpec hBva (List.mem_append_right _ hg)
  unfold m4FnsSuffix
  repeat' (first
    | exact m4_bva_all_wp mainSpec hBva
    | exact fun _ h => m4_compact_wp mainSpec h
    | exact fun _ h => m4_reorder_ternary_wp mainSpec h
    | apply forall_mem_append)
  · exact fun _ h => unch (by simp [m4UnchSuffix, h])
  · exact fun _ h => unch (by simp [m4UnchSuffix, h])
  · exact fun _ h => unch (by simp [m4UnchSuffix, h])
  · refine forall_mem_cons ?_ (forall_mem_cons ?_ (forall_mem_cons ?_
        (forall_mem_cons ?_ (forall_mem_cons ?_ (forall_mem_one ?_))))) <;>
      exact unch (by simp [m4UnchSuffix])
  · exact fun _ h => unch (by simp [m4UnchSuffix, h])
  · exact fun _ h => unch (by simp [m4UnchSuffix, h])
  · exact fun _ h => unch (by simp [m4UnchSuffix, h])
  · exact fun _ h => unch (by simp [m4UnchSuffix, h])
  · exact fun _ h => unch (by simp [m4UnchSuffix, h])
  · exact fun _ h => unch (by simp [m4UnchSuffix, h])
  · exact fun _ h => unch (by simp [m4UnchSuffix, h])
  · exact fun _ h => unch (by simp [m4UnchSuffix, h])
  · refine forall_mem_cons ?_ (forall_mem_cons ?_ (forall_mem_cons ?_ (forall_mem_one ?_)))
    · exact unch (by simp [m4UnchSuffix])
    · exact unch (by simp [m4UnchSuffix])
    · exact unch (by simp [m4UnchSuffix])
    · intro xs m Q X hs
      let h9 := mkM4Env_row_at (mainSpec := mainSpec) 9
        ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
      let h115 := mkM4Env_row_at (mainSpec := mainSpec) 115
        ⟨"full_probe_run", [i64, i64], [i64], FullM3Backbone.fullProbeRunCursorSpec, true⟩
      let h117 := mkM4Env_row_at (mainSpec := mainSpec) 117
        ⟨"full_transitive", [i64, i64], [i64], FullFastBveBudgets.fullTransitiveFastSpec, true⟩
      let h129 := mkM4Env_row_at (mainSpec := mainSpec) 129
        ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩
      let h130 := mkM4Env_row_at (mainSpec := mainSpec) 130
        ⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩
      let h131 := mkM4Env_row_at (mainSpec := mainSpec) 131
        ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
      let h160 := mkM4Env_row_at (mainSpec := mainSpec) 160
        ⟨"full_congruence_dense", [i64, i64], [i64], FullM3CongBva.m3CongruenceDenseSpec, true⟩
      let h164 := mkM4Env_row_at (mainSpec := mainSpec) 164
        ⟨"full_sweep_dense", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩
      let h214 := mkM4Env_row_at (mainSpec := mainSpec) 214
        ⟨"full_ternary", [i64, i64, i64], [i64], FullM4Ternary.fullTernarySpec, true⟩
      let h215 := mkM4Env_row_at (mainSpec := mainSpec) 215
        ⟨"full_scale_delta", [i64, i64], [i64], FullFastSched.schedScaleDeltaSpec, true⟩
      let h216 := mkM4Env_row_at (mainSpec := mainSpec) 216
        ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩
      let h218 := mkM4Env_row_at (mainSpec := mainSpec) 218
        ⟨"full_probe_dticks", [i64, .bool], [i64], FullFastSched.schedProbeDticksSpec, true⟩
      let h220 := mkM4Env_row_at (mainSpec := mainSpec) 220
        ⟨"full_backbone", [i64, i64], [i64], FullM3Backbone.fullBackboneSpec, true⟩
      let h221 := mkM4Env_row_at (mainSpec := mainSpec) 221
        ⟨"full_probe_tail", [i64, i64], [i64], FullFastSched.schedProbeTailSpec, true⟩
      exact wp_noExit_lift (m4_probe_wp Γ h218 h9 h215 h129 h130 h216 h160 h164 h131 h214 h220
        h117 h115 h221 xs m Q _
        (mkM4Env_row_elim 222 ⟨"full_probe", [i64, .bool], [i64],
          FullFastSched.schedProbeSpec, true⟩ rfl rfl hs))
  · exact fun _ h => unch (by simp [m4UnchSuffix, h])
  · refine forall_mem_cons ?_ (forall_mem_cons ?_ (forall_mem_cons ?_ (forall_mem_cons ?_
        (forall_mem_one ?_))))
    · exact unch (by simp [m4UnchSuffix])
    · exact unch (by simp [m4UnchSuffix])
    · intro xs m Q X hs
      let h8 := mkM4Env_row_at (mainSpec := mainSpec) 8
        ⟨"full_isqrt", [i64], [i64], fullIsqrtSpec, true⟩
      let h9 := mkM4Env_row_at (mainSpec := mainSpec) 9
        ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
      let h130 := mkM4Env_row_at (mainSpec := mainSpec) 130
        ⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩
      let h131 := mkM4Env_row_at (mainSpec := mainSpec) 131
        ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
      let h167 := mkM4Env_row_at (mainSpec := mainSpec) 167
        ⟨"full_forward_sub", [i64, i64], [i64], FullFastBveBudgets.fullForwardSubFastSpec, true⟩
      let h190 := mkM4Env_row_at (mainSpec := mainSpec) 190
        ⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩
      let h215 := mkM4Env_row_at (mainSpec := mainSpec) 215
        ⟨"full_scale_delta", [i64, i64], [i64], FullFastSched.schedScaleDeltaSpec, true⟩
      let h216 := mkM4Env_row_at (mainSpec := mainSpec) 216
        ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩
      let h223 := mkM4Env_row_at (mainSpec := mainSpec) 223
        ⟨"full_elim_dticks", [i64, .bool], [i64], FullFastSched.schedElimDticksSpec, true⟩
      let h225 := mkM4Env_row_at (mainSpec := mainSpec) 225
        ⟨"full_elim_bve", [i64, i64], [i64], FullM3CongBva.m3ElimBveSpec, true⟩
      exact wp_noExit_lift (m4_eliminate_wp Γ h223 h9 h8 h215 h130 h167 h216 h225 h190 h131
        xs m Q _
        (mkM4Env_row_elim 226 ⟨"full_eliminate", [i64, .bool], [i64],
          FullFastSched.schedEliminateSpec, true⟩ rfl rfl hs))
    · intro xs m Q X hs
      let h50 := mkM4Env_row_at (mainSpec := mainSpec) 50
        ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
      let h61 := mkM4Env_row_at (mainSpec := mainSpec) 61
        ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
      let h191 := mkM4Env_row_at (mainSpec := mainSpec) 191
        ⟨"full_compact_needed", [i64], [.bool], FullM4Compact.fullCompactNeededSpec, true⟩
      let h203 := mkM4Env_row_at (mainSpec := mainSpec) 203
        ⟨"full_compact", [i64], [i64], FullM4Compact.fullCompactSpec, true⟩
      let h215 := mkM4Env_row_at (mainSpec := mainSpec) 215
        ⟨"full_scale_delta", [i64, i64], [i64], FullFastSched.schedScaleDeltaSpec, true⟩
      let h216 := mkM4Env_row_at (mainSpec := mainSpec) 216
        ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩
      let h222 := mkM4Env_row_at (mainSpec := mainSpec) 222
        ⟨"full_probe", [i64, .bool], [i64], FullFastSched.schedProbeSpec, true⟩
      let h226 := mkM4Env_row_at (mainSpec := mainSpec) 226
        ⟨"full_eliminate", [i64, .bool], [i64], FullFastSched.schedEliminateSpec, true⟩
      exact wp_noExit_lift (m4_preprocess_wp Γ h50 h61 h215 h216 h222 h226 h191 h203 xs m Q _
        (mkM4Env_row_elim 227 ⟨"full_preprocess", [i64], [i64], m4PreprocessSpec, true⟩ rfl rfl hs))
    · intro xs m Q X hs
      let h30 := mkM4Env_row_at (mainSpec := mainSpec) 30
        ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
      let h65 := mkM4Env_row_at (mainSpec := mainSpec) 65
        ⟨"full_reduce", [i64, .bool], [i64], m4ReduceSpec, true⟩
      let h191 := mkM4Env_row_at (mainSpec := mainSpec) 191
        ⟨"full_compact_needed", [i64], [.bool], FullM4Compact.fullCompactNeededSpec, true⟩
      let h203 := mkM4Env_row_at (mainSpec := mainSpec) 203
        ⟨"full_compact", [i64], [i64], FullM4Compact.fullCompactSpec, true⟩
      let h209 := mkM4Env_row_at (mainSpec := mainSpec) 209
        ⟨"full_reorder", [i64, i64], [i64], m4ReorderSpec, true⟩
      let h222 := mkM4Env_row_at (mainSpec := mainSpec) 222
        ⟨"full_probe", [i64, .bool], [i64], FullFastSched.schedProbeSpec, true⟩
      let h226 := mkM4Env_row_at (mainSpec := mainSpec) 226
        ⟨"full_eliminate", [i64, .bool], [i64], FullFastSched.schedEliminateSpec, true⟩
      exact wp_noExit_lift (m4_simplify_wp Γ h30 h65 h222 h226 h191 h203 h209 xs m Q _
        (mkM4Env_row_elim 228 ⟨"full_simplify", [i64, .bool, .bool], [i64],
          m4SimplifySpec, true⟩ rfl rfl hs))
  · have hs_eq : FullFastSched.sched_fns.drop 14 =
        [⟨"full_search", [i64], [i64], FullFastSched.full_search_body⟩] := rfl
    rw [hs_eq]
    refine forall_mem_one fun xs m Q X hs => ?_
    let h50 := mkM4Env_row_at (mainSpec := mainSpec) 50
      ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
    let h65 := mkM4Env_row_at (mainSpec := mainSpec) 65
      ⟨"full_reduce", [i64, .bool], [i64], m4ReduceSpec, true⟩
    let h86 := mkM4Env_row_at (mainSpec := mainSpec) 86
      ⟨"full_analyze", [i64], [i64], fullAnalyzeSpec, true⟩
    let h88 := mkM4Env_row_at (mainSpec := mainSpec) 88
      ⟨"full_decide", [i64], [i64], fullDecideSpec, true⟩
    let h89 := mkM4Env_row_at (mainSpec := mainSpec) 89
      ⟨"full_warmup", [i64], [], fullWarmupSpec, true⟩
    let h94 := mkM4Env_row_at (mainSpec := mainSpec) 94
      ⟨"full_rephase", [i64], [], fullRephaseSpec, true⟩
    let h95 := mkM4Env_row_at (mainSpec := mainSpec) 95
      ⟨"full_switch_mode", [i64], [], fullSwitchModeSpec, true⟩
    let h96 := mkM4Env_row_at (mainSpec := mainSpec) 96
      ⟨"full_restart_due", [i64], [i64], fullRestartDueSpec, true⟩
    let h97 := mkM4Env_row_at (mainSpec := mainSpec) 97
      ⟨"full_restart", [i64], [], fullRestartSpec, true⟩
    let h109 := mkM4Env_row_at (mainSpec := mainSpec) 109
      ⟨"full_lucky", [i64], [i64], fullLuckySpec, true⟩
    let h228 := mkM4Env_row_at (mainSpec := mainSpec) 228
      ⟨"full_simplify", [i64, .bool, .bool], [i64], m4SimplifySpec, true⟩
    exact wp_noExit_lift (m4_search_wp Γ h109 h89 h50 h86 h95 h94 h65 h228 h96 h97 h88 xs m Q _
      (mkM4Env_row_elim 229 ⟨"full_search", [i64], [i64], m4SearchSpec, true⟩ rfl rfl hs))
  · refine forall_mem_one fun xs m Q X hs => ?_
    let h7 := mkM4Env_row_at (mainSpec := mainSpec) 7
      ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
    let h41 := mkM4Env_row_at (mainSpec := mainSpec) 41
      ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩
    let h44 := mkM4Env_row_at (mainSpec := mainSpec) 44
      ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩
    let h100 := mkM4Env_row_at (mainSpec := mainSpec) 100
      ⟨"full_extend", [i64], [], fullExtendSpec, true⟩
    let h227 := mkM4Env_row_at (mainSpec := mainSpec) 227
      ⟨"full_preprocess", [i64], [i64], m4PreprocessSpec, true⟩
    let h229 := mkM4Env_row_at (mainSpec := mainSpec) 229
      ⟨"full_search", [i64], [i64], m4SearchSpec, true⟩
    exact wp_noExit_lift (m4_kissat_solve_bytes_core_wp Γ h41 h44 h227 h229 h100 h7 xs m Q _
      (hweaken xs m Q _ (mkM4Env_row_elim 230
        ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩ rfl rfl hs)))

/-- Unconditional `231`-function `ModuleOk` assembly for `mkM4Env mainSpec` on `m4Module`. -/
theorem mkM4Env_moduleOk
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    ModuleOk (mkM4Env mainSpec) m4Module := by
  let hBva := FullM4Bva.mkM4BvaFullEnv_moduleOk mainSpec hweaken
  refine Module.moduleOk_of_checkAcyclic m4_acyclic m4Fns_wf ?_
  intro fn hfn
  rcases List.mem_append.mp hfn with hp | hs
  · exact m4Prefix_wp mainSpec hBva fn hp
  · exact m4Suffix_wp mainSpec hweaken hBva fn hs

/-- Unconditional closed `ModuleOk m4Env m4Module` certifying all `231 / 231` functions of
Unified Kissat M4 against canonical UNSAT-only `m4Env` (`0` SAT/model proofs). -/
theorem m4Env_moduleOk : ModuleOk m4Env m4Module :=
  mkM4Env_moduleOk fullSolveBytesSpec (fun _ _ _ _ => fullSolveBytesCoreSpec_of_spec)

/-- Unconditional closed `ModuleOk m4UnsatEnv m4Module` (`231 / 231`, concrete `Mem 64` UNSAT
non-vacuity environment). -/
theorem m4UnsatEnv_moduleOk : ModuleOk m4UnsatEnv m4Module :=
  mkM4Env_moduleOk fullUnsatWitnessSpec (fun _ _ _ _ => fullSolveBytesCoreSpec_of_unsatWitness)

end LeanQbe.T.Examples.Kissat.FullM4
