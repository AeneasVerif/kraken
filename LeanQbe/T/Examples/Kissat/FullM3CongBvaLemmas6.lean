module

public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas5
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas
public import LeanQbe.T.Examples.Kissat.FullKittenSpec1
public import LeanQbe.T.Examples.Kissat.FullProof

/-!
# Kissat `D-Full` M3b — Prefix `Full` & `Fast` Slice `TableImpl` Helpers

Reusable `List` / `TableImpl` combinators and abstract-`Γ` `TableImpl` proofs for the unchanged
`Full` and `Fast` prefix function slices `[0..128)` used in assembling `201`-row `ModuleOk`.
Parameterizing every proof over an abstract `Γ : Env` keeps `Env.ofTable` tables completely out of
slice-wise `isDefEq` unification.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM3CongBva

open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched

theorem m3_allFns_of_forall {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h =>
    ⟨h _ List.mem_cons_self, m3_allFns_of_forall fun f hf => h f (List.mem_cons_of_mem _ hf)⟩

theorem m3_dimacs_len : dimacs_fns.length = 8 := by t_kernel_rfl
theorem m3_full1_len : Full.full1_fns.length = 51 := by t_kernel_rfl
theorem m3_full2_len : Full.full2_fns.length = 38 := by t_kernel_rfl
theorem m3_full3_len : Full.full3_fns.length = 31 := by t_kernel_rfl
theorem m3_full4_len : Full.full4_fns.length = 38 := by t_kernel_rfl
theorem m3_fullFns_len : Full.fullFns.length = 166 := by t_kernel_rfl
theorem m3_fullSpecTable_len (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (fullSpecTable mainSpec).length = 166 := by
  rw [← List.length_map (f := fun e => (e.name, e.as, e.rs)), fullSpecTable_sigs,
    List.length_map, m3_fullFns_len]
theorem m3_fastBveBudgets_len : FullFastBveBudgets.fastBveBudgets_fns.length = 7 := by t_kernel_rfl
theorem m3_fastCore_len : FastCore.fastCore_fns.length = 3 := by t_kernel_rfl
theorem m3_sched_len : FullFastSched.sched_fns.length = 15 := by t_kernel_rfl
theorem m3_fastOrch_len : FullFast.fastOrch_fns.length = 3 := by t_kernel_rfl
theorem m3_kitten_len : Full.fullKitten_fns.length = 15 := by t_kernel_rfl
theorem m3_defSweep_len : FullDefSweep.full_def_sweep_fns.length = 9 := by t_kernel_rfl
theorem m3_bvaHeap_len : FullBvaHeap.bvaHeap_fns.length = 13 := by t_kernel_rfl

theorem m3_drop_append_left {α : Type _} {xs ys : List α} {n : Nat} (h : xs.length = n) :
    (xs ++ ys).drop n = ys := by
  subst h; simp

theorem m3_take_append_left {α : Type _} {xs ys : List α} {n : Nat} (h : xs.length = n) :
    (xs ++ ys).take n = xs := by
  subst h; simp

theorem m3_list_take_add {α : Type _} :
    ∀ (a b : Nat) (l : List α), l.take (a + b) = l.take a ++ (l.drop a).take b
  | 0, _, _ => by simp
  | a + 1, b, [] => by simp
  | a + 1, b, x :: xs => by
    rw [Nat.add_right_comm, List.take_succ_cons, List.take_succ_cons, List.drop_succ_cons,
      List.cons_append, m3_list_take_add a b xs]

theorem m3_list_drop_add {α : Type _} :
    ∀ (a b : Nat) (l : List α), l.drop (a + b) = (l.drop a).drop b
  | 0, _, _ => by simp
  | a + 1, b, [] => by simp
  | a + 1, b, _ :: xs => by
    rw [Nat.add_right_comm, List.drop_succ_cons, List.drop_succ_cons, m3_list_drop_add a b xs]

theorem m3_list_drop_take_add {α : Type _} (i a b : Nat) (l : List α) :
    (l.drop i).take (a + b) = (l.drop i).take a ++ (l.drop (i + a)).take b := by
  rw [m3_list_take_add, m3_list_drop_add]

theorem m3_getElem?_append_seg {α : Type _} {pre mid post : List α} {k i : Nat}
    (hpre : pre.length = k) (hi : i < mid.length) :
    (pre ++ (mid ++ post))[k + i]? = mid[i]? := by
  subst hpre
  rw [List.getElem?_append_right (by omega), show pre.length + i - pre.length = i by omega,
    List.getElem?_append_left hi]

theorem m3_fullFns_eq_blocks :
    Full.fullFns = dimacs_fns ++
      (Full.full1_fns ++ (Full.full2_fns ++ (Full.full3_fns ++ Full.full4_fns))) := by
  simp only [Full.fullFns, List.append_assoc]

theorem m3_fullFns_take8 : Full.fullFns.take 8 = dimacs_fns := by
  rw [m3_fullFns_eq_blocks]; exact m3_take_append_left m3_dimacs_len

theorem m3_fullFns_drop8 :
    Full.fullFns.drop 8 =
      Full.full1_fns ++ (Full.full2_fns ++ (Full.full3_fns ++ Full.full4_fns)) := by
  rw [m3_fullFns_eq_blocks]; exact m3_drop_append_left m3_dimacs_len

theorem m3_fullFns_drop59 :
    Full.fullFns.drop 59 = Full.full2_fns ++ (Full.full3_fns ++ Full.full4_fns) := by
  rw [show (59 : Nat) = 8 + 51 from rfl, m3_list_drop_add 8 51, m3_fullFns_drop8]
  exact m3_drop_append_left m3_full1_len

theorem m3_fullFns_drop97 :
    Full.fullFns.drop 97 = Full.full3_fns ++ Full.full4_fns := by
  rw [show (97 : Nat) = 59 + 38 from rfl, m3_list_drop_add 59 38, m3_fullFns_drop59]
  exact m3_drop_append_left m3_full2_len

theorem m3_fullFns_drop128 :
    Full.fullFns.drop 128 = Full.full4_fns := by
  rw [show (128 : Nat) = 97 + 31 from rfl, m3_list_drop_add 97 31, m3_fullFns_drop97]
  exact m3_drop_append_left m3_full3_len

private theorem m3_drop_take_append_left {α : Type _} {xs ys : List α} {i k : Nat}
    (h : i + k ≤ xs.length) :
    ((xs ++ ys).drop i).take k = (xs.drop i).take k := by
  rw [List.drop_append, Nat.sub_eq_zero_of_le (by omega), List.drop_zero,
    List.take_append_of_le_length (by simp [List.length_drop]; omega)]

theorem m3_fullFns_drop_slice1 {i k : Nat} (hk : i + k ≤ 51) :
    (Full.fullFns.drop (8 + i)).take k = (Full.full1_fns.drop i).take k := by
  rw [m3_list_drop_add 8 i, m3_fullFns_drop8]
  exact m3_drop_take_append_left (by simp [m3_full1_len]; omega)

theorem m3_fullFns_drop_slice2 {i k : Nat} (hk : i + k ≤ 38) :
    (Full.fullFns.drop (59 + i)).take k = (Full.full2_fns.drop i).take k := by
  rw [m3_list_drop_add 59 i, m3_fullFns_drop59]
  exact m3_drop_take_append_left (by simp [m3_full2_len]; omega)

theorem m3_fullFns_drop_slice3 {i k : Nat} (hk : i + k ≤ 31) :
    (Full.fullFns.drop (97 + i)).take k = (Full.full3_fns.drop i).take k := by
  rw [m3_list_drop_add 97 i, m3_fullFns_drop97]
  exact m3_drop_take_append_left (by simp [m3_full3_len]; omega)

theorem m3_fullFns_drop_slice4 {i k : Nat} :
    (Full.fullFns.drop (128 + i)).take k = (Full.full4_fns.drop i).take k := by
  rw [m3_list_drop_add 128 i, m3_fullFns_drop128]

theorem m3_tableImpl_append {Γ : Env} :
    ∀ {fs₁ tbl₁ fs₂ tbl₂},
    TableImpl Γ fs₁ tbl₁ → TableImpl Γ fs₂ tbl₂ →
    (hlen : fs₁.length = tbl₁.length := by rfl) →
    TableImpl Γ (fs₁ ++ fs₂) (tbl₁ ++ tbl₂)
  | [], [], _, _, _, h2, _ => h2
  | [], _ :: _, _, _, _, _, hlen => False.elim (by simp at hlen)
  | _ :: _, [], _, _, _, _, hlen => False.elim (by simp at hlen)
  | _ :: _, _ :: _, _, _, ⟨h1, hr⟩, h2, hlen =>
    ⟨h1, m3_tableImpl_append hr h2 (by simpa using hlen)⟩

theorem m3_tableImpl_singleton {Γ : Env} {fs : List Fn} {tbl : List SpecEntry}
    {fn : Fn} {e : SpecEntry}
    (hf : fs[0]? = some fn) (he : tbl[0]? = some e)
    (hfl : fs.length = 1) (htl : tbl.length = 1)
    (himpl : SpecEntry.Impl Γ fn e) :
    TableImpl Γ fs tbl := by
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hfl
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp htl
  subst ha; subst hb
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hf he
  subst hf; subst he
  exact ⟨himpl, trivial⟩

theorem m3_tableImpl_drop_step {Γ : Env} {fs : List Fn} {tbl : List SpecEntry}
    {i : Nat} {fn : Fn} {e : SpecEntry}
    (hf : fs[i]? = some fn) (he : tbl[i]? = some e)
    (himpl : SpecEntry.Impl Γ fn e)
    (hrest : TableImpl Γ (fs.drop (i + 1)) (tbl.drop (i + 1))) :
    TableImpl Γ (fs.drop i) (tbl.drop i) := by
  have hfi : i < fs.length := (List.getElem?_eq_some_iff.mp hf).1
  have hei : i < tbl.length := (List.getElem?_eq_some_iff.mp he).1
  rw [List.drop_eq_getElem_cons hfi, List.drop_eq_getElem_cons hei]
  have hfe : fs[i]'hfi = fn := Option.some.inj ((List.getElem?_eq_getElem hfi).symm.trans hf)
  have hee : tbl[i]'hei = e := Option.some.inj ((List.getElem?_eq_getElem hei).symm.trans he)
  rw [hfe, hee]
  exact ⟨himpl, hrest⟩

theorem m3_tableImpl_drop_nil {Γ : Env} {fs : List Fn} {tbl : List SpecEntry}
    {k : Nat} (hf : fs.length = k) (ht : tbl.length = k) :
    TableImpl Γ (fs.drop k) (tbl.drop k) := by
  rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]
  trivial

theorem m3_list_drop_take_eq_cons {α : Type _} {xs : List α} {b k : Nat} {x : α}
    (hk : 0 < k) (hx : xs[b]? = some x) :
    (xs.drop b).take k = x :: (xs.drop (b + 1)).take (k - 1) := by
  have hb : b < xs.length := (List.getElem?_eq_some_iff.mp hx).1
  have hxb : xs[b]'hb = x := Option.some.inj ((List.getElem?_eq_getElem hb).symm.trans hx)
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [List.drop_eq_getElem_cons hb, hxb, List.take_succ_cons, Nat.succ_sub_one]

theorem m3_tableImpl_fullSlice_step {Γ : Env}
    {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    {fs : List Fn} {b k i : Nat} {fn : Fn} {e : SpecEntry}
    (hik : i < k) (hf : fs[i]? = some fn)
    (he : (fullSpecTable mainSpec)[b + i]? = some e)
    (himpl : SpecEntry.Impl Γ fn e)
    (hrest : TableImpl Γ (fs.drop (i + 1))
      (((fullSpecTable mainSpec).drop (b + (i + 1))).take (k - (i + 1)))) :
    TableImpl Γ (fs.drop i) (((fullSpecTable mainSpec).drop (b + i)).take (k - i)) := by
  have hfi : i < fs.length := (List.getElem?_eq_some_iff.mp hf).1
  have hfe : fs[i]'hfi = fn := Option.some.inj ((List.getElem?_eq_getElem hfi).symm.trans hf)
  rw [List.drop_eq_getElem_cons hfi, hfe, m3_list_drop_take_eq_cons (by omega) he,
    show b + i + 1 = b + (i + 1) by omega, show k - i - 1 = k - (i + 1) by omega]
  exact ⟨himpl, hrest⟩

theorem m3_tableImpl_fullSlice_nil {Γ : Env}
    {mainSpec : Spec [i64, i64, i64, i64, i64] [i64]}
    {fs : List Fn} {b k : Nat} (hf : fs.length = k) :
    TableImpl Γ (fs.drop k) (((fullSpecTable mainSpec).drop (b + k)).take (k - k)) := by
  rw [List.drop_of_length_le (by omega), Nat.sub_self, List.take_zero]
  trivial

theorem m3_tableImpl_of_getElem? {Γ : Env} :
    ∀ {fs : List Fn} {tbl : List SpecEntry},
    fs.length = tbl.length →
    (∀ i, i < fs.length →
      ∃ fn e, fs[i]? = some fn ∧ tbl[i]? = some e ∧ SpecEntry.Impl Γ fn e) →
    TableImpl Γ fs tbl
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, hlen, h => by
    obtain ⟨f', e', hf0, he0, himpl⟩ := h 0 (by simp)
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hf0 he0
    subst hf0; subst he0
    exact ⟨himpl, m3_tableImpl_of_getElem? (by simpa using hlen)
      fun i hi => h (i + 1) (by simp only [List.length_cons]; omega)⟩

theorem m3_extPush2Tmk_of_canon {a m Q X}
    (h : Full.fullExtendPush2Spec a m Q X) : fullExtendPush2TmkSpec a m Q X := by
  rcases h with ⟨c, s, R, hpre, hlen, hm, hQ⟩
  exact ⟨c, s, R, hpre, hlen, hm, fun r s' m' hpr hln hpost hm' =>
    hQ r s' m' hpr hln ⟨hpost.1, hpost.2.1, hpost.2.2.1⟩ hm'⟩

theorem m3Full_impl_0_8_gen (Γ : Env)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (h0 : ∀ xs m Q X, kissatIsWsSpec xs m Q X → Γ "kissat_is_ws" [i64] [.bool] xs m Q X)
    (h1 : ∀ xs m Q X, kissatIsDigitSpec xs m Q X → Γ "kissat_is_digit" [i64] [.bool] xs m Q X)
    (h2 : ∀ xs m Q X, kissatSkipWsCommentsSpec xs m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] xs m Q X)
    (h3 : ∀ xs m Q X, kissatSkipWs1Spec xs m Q X →
      Γ "kissat_skip_ws1" [i64, i64] [.bool] xs m Q X)
    (h4 : ∀ xs m Q X, kissatReadNatSpec xs m Q X →
      Γ "kissat_read_nat" [i64, i64] [.bool] xs m Q X)
    (h5 : ∀ xs m Q X, kissatParseHeaderSpec xs m Q X →
      Γ "kissat_parse_header" [i64, i64, i64] [.bool] xs m Q X)
    (h6 : ∀ xs m Q X, kissatNextLitSpec xs m Q X →
      Γ "kissat_next_lit" [i64, i64] [i64] xs m Q X) :
    TableImpl Γ dimacs_fns ((fullSpecTable mainSpec).take 8) := by
  change TableImpl Γ (dimacs_fns.drop 0) (((fullSpecTable mainSpec).drop (0 + 0)).take (8 - 0))
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (kissat_is_ws_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (kissat_is_digit_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (kissat_skip_ws_comments_bridge_wp Γ h0)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (kissat_skip_ws1_bridge_wp Γ h0)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (kissat_read_nat_bridge_wp Γ h1 h0)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (kissat_parse_header_bridge_wp Γ h2 h3 h4)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (kissat_next_lit_bridge_wp Γ h2 h4)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (kissat_check_model_bridge_wp Γ h5 h6 h2)) ?_
  exact m3_tableImpl_fullSlice_nil m3_dimacs_len

theorem m3Full_impl_8_22_gen (Γ : Env)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (h13 : ∀ xs m Q X, fullWsortSiftSpec xs m Q X →
      Γ "full_wsort_sift" [i64, i64, i64, i64] [] xs m Q X)
    (h14 : ∀ xs m Q X, fullWstackDefragSpec xs m Q X →
      Γ "full_wstack_defrag" [i64] [] xs m Q X)
    (h16 : ∀ xs m Q X, fullHeapUpSpec xs m Q X → Γ "full_heap_up" [i64, i32] [] xs m Q X)
    (h17 : ∀ xs m Q X, fullHeapDownSpec xs m Q X → Γ "full_heap_down" [i64, i32] [] xs m Q X)
    (h20 : ∀ xs m Q X, fullRescaleSpec xs m Q X → Γ "full_rescale" [i64] [] xs m Q X) :
    TableImpl Γ (Full.full1_fns.take 14) (((fullSpecTable mainSpec).drop 8).take 14) := by
  change TableImpl Γ ((Full.full1_fns.take 14).drop 0)
    (((fullSpecTable mainSpec).drop (8 + 0)).take (14 - 0))
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_isqrt_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_ilog10_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_rng_next_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_arena_next_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_alloc_cl_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_wsort_sift_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_wstack_defrag_bridge_wp Γ h13)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_watch_push_bridge_wp Γ h14)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_heap_up_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_heap_down_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_heap_push_bridge_wp Γ h16)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_heap_pop_bridge_wp Γ h17)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_rescale_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_bump_var_bridge_wp Γ h16 h20)) ?_
  exact m3_tableImpl_fullSlice_nil (by simp [m3_full1_len])

theorem m3Full_impl_22_36_gen (Γ : Env)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (h12 : ∀ xs m Q X, fullAllocClSpec xs m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] xs m Q X)
    (h15 : ∀ xs m Q X, fullWatchPushSpec xs m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (h18 : ∀ xs m Q X, fullHeapPushSpec xs m Q X → Γ "full_heap_push" [i64, i32] [] xs m Q X)
    (h20 : ∀ xs m Q X, fullRescaleSpec xs m Q X → Γ "full_rescale" [i64] [] xs m Q X)
    (h23 : ∀ xs m Q X, fullQueueRenumberSpec xs m Q X →
      Γ "full_queue_renumber" [i64] [] xs m Q X)
    (h27 : ∀ xs m Q X, fullAssignLvlSpec xs m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] xs m Q X)
    (h29 : ∀ xs m Q X, fullSaveTargetBestSpec xs m Q X →
      Γ "full_save_target_best" [i64] [] xs m Q X) :
    TableImpl Γ ((Full.full1_fns.drop 14).take 14)
      (((fullSpecTable mainSpec).drop 22).take 14) := by
  change TableImpl Γ (((Full.full1_fns.drop 14).take 14).drop 0)
    (((fullSpecTable mainSpec).drop (22 + 0)).take (14 - 0))
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_bump_decay_bridge_wp Γ h20)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_queue_renumber_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_queue_mtf_bridge_wp Γ h23)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_tick_rel_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_ema_update_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_assign_lvl_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_assign_bridge_wp Γ h27)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_save_target_best_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_backtrack_bridge_wp Γ h29 h18)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_add_clause_bridge_wp Γ h12 h15)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_zero_tables1_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_zero_tables2_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_fixed_bytes_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_init_ptrs_bridge_wp Γ)) ?_
  exact m3_tableImpl_fullSlice_nil (by simp [m3_full1_len])

theorem m3Full_impl_37_47_gen (Γ : Env)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (h2 : ∀ xs m Q X, kissatSkipWsCommentsSpec xs m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] xs m Q X)
    (h5 : ∀ xs m Q X, kissatParseHeaderSpec xs m Q X →
      Γ "kissat_parse_header" [i64, i64, i64] [.bool] xs m Q X)
    (h6 : ∀ xs m Q X, kissatNextLitSpec xs m Q X →
      Γ "kissat_next_lit" [i64, i64] [i64] xs m Q X)
    (h27 : ∀ xs m Q X, fullAssignLvlSpec xs m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] xs m Q X)
    (h31 : ∀ xs m Q X, fullAddClauseSpec xs m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] xs m Q X)
    (h32 : ∀ xs m Q X, fullZeroTables1Spec xs m Q X → Γ "full_zero_tables1" [i64] [] xs m Q X)
    (h33 : ∀ xs m Q X, fullZeroTables2Spec xs m Q X → Γ "full_zero_tables2" [i64] [] xs m Q X)
    (h34 : ∀ xs m Q X, fullFixedBytesSpec xs m Q X → Γ "full_fixed_bytes" [i64] [i64] xs m Q X)
    (h35 : ∀ xs m Q X, fullInitPtrsSpec xs m Q X →
      Γ "full_init_ptrs" [i64, i64, i64] [] xs m Q X)
    (h36 : ∀ xs m Q X, fullInitHdrSpec xs m Q X →
      Γ "full_init_hdr" [i64, i64, i64, i64] [] xs m Q X)
    (h37 : ∀ xs m Q X, fullCalcMaxVSpec xs m Q X →
      Γ "full_calc_max_v" [i64, i64, i64, i64] [i64] xs m Q X)
    (h38 : ∀ xs m Q X, fullCalcExtCapSpec xs m Q X → Γ "full_calc_ext_cap" [i64] [i64] xs m Q X)
    (h39 : ∀ xs m Q X, fullCalcScrCapSpec xs m Q X → Γ "full_calc_scr_cap" [i64] [i64] xs m Q X)
    (h40 : ∀ xs m Q X, fullInitArenasSpec xs m Q X →
      Γ "full_init_arenas" [i64, i64, i64, i64] [] xs m Q X)
    (h42 : ∀ xs m Q X, fullSkipClSpec xs m Q X →
      Γ "full_skip_cl" [i64, i64] [.bool] xs m Q X)
    (h43 : ∀ xs m Q X, fullIngestClSpec xs m Q X → Γ "full_ingest_cl" [i64, i64] [i64] xs m Q X) :
    TableImpl Γ ((Full.full1_fns.drop 29).take 10)
      (((fullSpecTable mainSpec).drop 37).take 10) := by
  change TableImpl Γ (((Full.full1_fns.drop 29).take 10).drop 0)
    (((fullSpecTable mainSpec).drop (37 + 0)).take (10 - 0))
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_calc_max_v_bridge_wp Γ h34)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_calc_ext_cap_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_calc_scr_cap_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_init_arenas_bridge_wp Γ h35)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_init_state_bridge_wp Γ h5 h34 h37 h38 h39 h40 h36 h32 h33)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_skip_cl_bridge_wp Γ h6)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_ingest_cl_bridge_wp Γ h6 h27 h31)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_parse_body_bridge_wp Γ h42 h43 h2)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_find_repl_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_assign_level_bridge_wp Γ)) ?_
  exact m3_tableImpl_fullSlice_nil (by simp [m3_full1_len])

theorem m3Full_impl_50_57_gen (Γ : Env)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (h52 : ∀ xs m Q X, fullRedLessSpec xs m Q X →
      Γ "full_red_less" [i64, i32, i32] [.bool] xs m Q X)
    (h53 : ∀ xs m Q X, fullRedSiftSpec xs m Q X →
      Γ "full_red_sift" [i64, i64, i64, i64] [] xs m Q X) :
    TableImpl Γ ((Full.full1_fns.drop 42).take 7) (((fullSpecTable mainSpec).drop 50).take 7) := by
  change TableImpl Γ (((Full.full1_fns.drop 42).take 7).drop 0)
    (((fullSpecTable mainSpec).drop (50 + 0)).take (7 - 0))
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_recompute_tiers_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_mark_reasons_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_red_less_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_red_sift_bridge_wp Γ h52)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_sort_reds_bridge_wp Γ h53)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_lit_rank_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_unwatch_large_bridge_wp Γ)) ?_
  exact m3_tableImpl_fullSlice_nil (by simp [m3_full1_len])

theorem m3Full_impl_59_76_gen (Γ : Env)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (h8 : ∀ xs m Q X, fullIsqrtSpec xs m Q X → Γ "full_isqrt" [i64] [i64] xs m Q X)
    (h9 : ∀ xs m Q X, fullIlog10Spec xs m Q X → Γ "full_ilog10" [i64] [i64] xs m Q X)
    (h11 : ∀ xs m Q X, fullArenaNextSpec xs m Q X → Γ "full_arena_next" [i64, i32] [i32] xs m Q X)
    (h15 : ∀ xs m Q X, fullWatchPushSpec xs m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (h21 : ∀ xs m Q X, fullBumpVarSpec xs m Q X → Γ "full_bump_var" [i64, i32] [] xs m Q X)
    (h22 : ∀ xs m Q X, fullBumpDecaySpec xs m Q X → Γ "full_bump_decay" [i64] [] xs m Q X)
    (h24 : ∀ xs m Q X, fullQueueMtfSpec xs m Q X → Γ "full_queue_mtf" [i64, i32] [] xs m Q X)
    (h30 : ∀ xs m Q X, fullBacktrackSpec xs m Q X → Γ "full_backtrack" [i64, i64] [] xs m Q X)
    (h49 : ∀ xs m Q X, fullPropagateSpec xs m Q X → Γ "full_propagate" [i64] [i64] xs m Q X)
    (h50 : ∀ xs m Q X, fullRecomputeTiersSpec xs m Q X →
      Γ "full_recompute_tiers" [i64] [] xs m Q X)
    (h51 : ∀ xs m Q X, fullMarkReasonsSpec xs m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] xs m Q X)
    (h54 : ∀ xs m Q X, fullSortRedsSpec xs m Q X → Γ "full_sort_reds" [i64, i64] [] xs m Q X)
    (h55 : ∀ xs m Q X, fullLitRankSpec xs m Q X → Γ "full_lit_rank" [i64, i64, i32] [i64] xs m Q X)
    (h56 : ∀ xs m Q X, fullUnwatchLargeSpec xs m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] xs m Q X)
    (h57 : ∀ xs m Q X, fullSweepBinsSpec xs m Q X → Γ "full_sweep_bins" [i64] [] xs m Q X)
    (h58 : ∀ xs m Q X, fullSweepCopySpec xs m Q X →
      Γ "full_sweep_copy" [i64, i64, i64, i32, .bool] [i64] xs m Q X)
    (h59 : ∀ xs m Q X, fullRewatchArenaSpec xs m Q X →
      Γ "full_rewatch_arena" [i64, i64] [.bool] xs m Q X)
    (h60 : ∀ xs m Q X, fullArenaSweepSpec xs m Q X → Γ "full_arena_sweep" [i64] [i64] xs m Q X)
    (h62 : ∀ xs m Q X, fullAnalyzeLitSpec xs m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] xs m Q X)
    (h69 : ∀ xs m Q X, fullMinMarkSpec xs m Q X → Γ "full_min_mark" [i64, i32, i8] [] xs m Q X)
    (h70 : ∀ xs m Q X, fullMinLitSpec xs m Q X → Γ "full_min_lit" [i64, i32] [.bool] xs m Q X)
    (h71 : ∀ xs m Q X, fullTmpLessSpec xs m Q X →
      Γ "full_tmp_less" [i64, i64, i32, i32] [.bool] xs m Q X)
    (h72 : ∀ xs m Q X, fullSortTmpSiftSpec xs m Q X →
      Γ "full_sort_tmp_sift" [i64, i64, i64, i64, i64] [] xs m Q X)
    (h74 : ∀ xs m Q X, fullShrinkLowerSpec xs m Q X →
      Γ "full_shrink_lower" [i64, i32, i32] [.bool] xs m Q X) :
    TableImpl Γ (Full.full2_fns.take 17) (((fullSpecTable mainSpec).drop 59).take 17) := by
  change TableImpl Γ ((Full.full2_fns.take 17).drop 0)
    (((fullSpecTable mainSpec).drop (59 + 0)).take (17 - 0))
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_rewatch_arena_bridge_wp Γ h55 h15)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_arena_sweep_bridge_wp Γ h57 h11 h58 h59)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_reduce_bridge_wp Γ h8 h9 h11 h50 h51 h54 h30 h49 h60)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_analyze_lit_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_analyze_rsn_bridge_wp Γ h62)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_clear_ana_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_bump_analyzed_bridge_wp Γ h21 h24 h22)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_otfs_large_bridge_wp Γ h56 h15)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_otfs_bin_bridge_wp Γ h56 h15)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_otfs_subsume_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_min_mark_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_min_lit_bridge_wp Γ h69)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_tmp_less_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_sort_tmp_sift_bridge_wp Γ h71)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_sort_tmp_bridge_wp Γ h72)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_shrink_lower_bridge_wp Γ h69 h70)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_shrink_blk_bridge_wp Γ h74 h69)) ?_
  exact m3_tableImpl_fullSlice_nil (by simp [m3_full2_len])

theorem m3Full_impl_76_94_gen (Γ : Env)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (h9 : ∀ xs m Q X, fullIlog10Spec xs m Q X → Γ "full_ilog10" [i64] [i64] xs m Q X)
    (h10 : ∀ xs m Q X, fullRngNextSpec xs m Q X → Γ "full_rng_next" [i64] [i64] xs m Q X)
    (h11 : ∀ xs m Q X, fullArenaNextSpec xs m Q X → Γ "full_arena_next" [i64, i32] [i32] xs m Q X)
    (h14 : ∀ xs m Q X, fullWstackDefragSpec xs m Q X → Γ "full_wstack_defrag" [i64] [] xs m Q X)
    (h15 : ∀ xs m Q X, fullWatchPushSpec xs m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (h17 : ∀ xs m Q X, fullHeapDownSpec xs m Q X → Γ "full_heap_down" [i64, i32] [] xs m Q X)
    (h19 : ∀ xs m Q X, fullHeapPopSpec xs m Q X → Γ "full_heap_pop" [i64] [i64] xs m Q X)
    (h25 : ∀ xs m Q X, fullTickRelSpec xs m Q X → Γ "full_tick_rel" [i64] [] xs m Q X)
    (h26 : ∀ xs m Q X, fullEmaUpdateSpec xs m Q X → Γ "full_ema_update" [i64, i64] [] xs m Q X)
    (h27 : ∀ xs m Q X, fullAssignLvlSpec xs m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] xs m Q X)
    (h28 : ∀ xs m Q X, fullAssignSpec xs m Q X → Γ "full_assign" [i64, i32, i32] [] xs m Q X)
    (h30 : ∀ xs m Q X, fullBacktrackSpec xs m Q X → Γ "full_backtrack" [i64, i64] [] xs m Q X)
    (h31 : ∀ xs m Q X, fullAddClauseSpec xs m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] xs m Q X)
    (h49 : ∀ xs m Q X, fullPropagateSpec xs m Q X → Γ "full_propagate" [i64] [i64] xs m Q X)
    (h56 : ∀ xs m Q X, fullUnwatchLargeSpec xs m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] xs m Q X)
    (h61 : ∀ xs m Q X, fullReduceSpec xs m Q X → Γ "full_reduce" [i64, .bool] [i64] xs m Q X)
    (h62 : ∀ xs m Q X, fullAnalyzeLitSpec xs m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] xs m Q X)
    (h63 : ∀ xs m Q X, fullAnalyzeRsnSpec xs m Q X →
      Γ "full_analyze_rsn" [i64, i32, i32] [.bool] xs m Q X)
    (h64 : ∀ xs m Q X, fullClearAnaSpec xs m Q X → Γ "full_clear_ana" [i64] [] xs m Q X)
    (h65 : ∀ xs m Q X, fullBumpAnalyzedSpec xs m Q X → Γ "full_bump_analyzed" [i64] [] xs m Q X)
    (h66 : ∀ xs m Q X, fullOtfsLargeSpec xs m Q X →
      Γ "full_otfs_large" [i64, i32, i32] [.bool] xs m Q X)
    (h67 : ∀ xs m Q X, fullOtfsBinSpec xs m Q X →
      Γ "full_otfs_bin" [i64, i32, i32] [.bool] xs m Q X)
    (h68 : ∀ xs m Q X, fullOtfsSubsumeSpec xs m Q X →
      Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] xs m Q X)
    (h69 : ∀ xs m Q X, fullMinMarkSpec xs m Q X → Γ "full_min_mark" [i64, i32, i8] [] xs m Q X)
    (h70 : ∀ xs m Q X, fullMinLitSpec xs m Q X → Γ "full_min_lit" [i64, i32] [.bool] xs m Q X)
    (h73 : ∀ xs m Q X, fullSortTmpSpec xs m Q X → Γ "full_sort_tmp" [i64] [] xs m Q X)
    (h75 : ∀ xs m Q X, fullShrinkBlkSpec xs m Q X →
      Γ "full_shrink_blk" [i64, i64, i64, i32, i64] [] xs m Q X)
    (h76 : ∀ xs m Q X, fullMinShrinkSpec xs m Q X → Γ "full_min_shrink" [i64] [] xs m Q X)
    (h77 : ∀ xs m Q X, fullDetNewLevelSpec xs m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] xs m Q X)
    (h78 : ∀ xs m Q X, fullOneLitConflSpec xs m Q X →
      Γ "full_one_lit_confl" [i64] [i64] xs m Q X)
    (h79 : ∀ xs m Q X, fullDeduce1uipSpec xs m Q X → Γ "full_deduce_1uip" [i64] [i64] xs m Q X)
    (h80 : ∀ xs m Q X, fullEagerSubsumeSpec xs m Q X →
      Γ "full_eager_subsume" [i64, i64] [] xs m Q X)
    (h81 : ∀ xs m Q X, fullLearnClauseSpec xs m Q X →
      Γ "full_learn_clause" [i64, i64] [i64] xs m Q X)
    (h83 : ∀ xs m Q X, fullNextDecVarSpec xs m Q X →
      Γ "full_next_dec_var" [i64] [i64] xs m Q X)
    (h86 : ∀ xs m Q X, fullWalkCollectSpec xs m Q X →
      Γ "full_walk_collect" [i64] [i64] xs m Q X)
    (h87 : ∀ xs m Q X, fullWalkClSatSpec xs m Q X →
      Γ "full_walk_cl_sat" [i64, i64, i64] [.bool] xs m Q X)
    (h88 : ∀ xs m Q X, fullWalkPickLitSpec xs m Q X →
      Γ "full_walk_pick_lit" [i64, i64, i64] [i32] xs m Q X)
    (h89 : ∀ xs m Q X, fullWalkSpec xs m Q X → Γ "full_walk" [i64] [] xs m Q X) :
    TableImpl Γ ((Full.full2_fns.drop 17).take 18)
      (((fullSpecTable mainSpec).drop 76).take 18) := by
  change TableImpl Γ (((Full.full2_fns.drop 17).take 18).drop 0)
    (((fullSpecTable mainSpec).drop (76 + 0)).take (18 - 0))
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_min_shrink_bridge_wp Γ h73 h69 h70 h75)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_det_new_level_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_one_lit_confl_wp Γ h77 h30 h27 h56 h15)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_deduce_1uip_wp Γ h62 h63 h64 h65 h66 h67 h68)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_eager_subsume_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_learn_clause_bridge_wp Γ h30 h27 h77 h14 h61 h31 h80)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_analyze_bridge_wp Γ h78 h79 h76 h25 h26 h81)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_next_dec_var_bridge_wp Γ h19)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_decide_bridge_wp Γ h83 h28)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_warmup_bridge_wp Γ h83 h28 h49 h30)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_walk_collect_bridge_wp Γ h11)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_walk_cl_sat_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_walk_pick_lit_bridge_wp Γ h10)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_walk_bridge_wp Γ h86 h87 h10 h88)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_rephase_bridge_wp Γ h30 h89 h9)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_switch_mode_bridge_wp Γ h17 h9)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_restart_due_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_restart_bridge_wp Γ h83 h30)) ?_
  exact m3_tableImpl_fullSlice_nil (by simp [m3_full2_len])

theorem m3Full_impl_97_111_gen (Γ : Env)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (h11 : ∀ xs m Q X, fullArenaNextSpec xs m Q X → Γ "full_arena_next" [i64, i32] [i32] xs m Q X)
    (h15 : ∀ xs m Q X, fullWatchPushSpec xs m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (h27 : ∀ xs m Q X, fullAssignLvlSpec xs m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] xs m Q X)
    (h28 : ∀ xs m Q X, fullAssignSpec xs m Q X → Γ "full_assign" [i64, i32, i32] [] xs m Q X)
    (h30 : ∀ xs m Q X, fullBacktrackSpec xs m Q X → Γ "full_backtrack" [i64, i64] [] xs m Q X)
    (h45 : ∀ xs m Q X, fullFindReplSpec xs m Q X → Γ "full_find_repl" [i64, i64] [i64] xs m Q X)
    (h49 : ∀ xs m Q X, fullPropagateSpec xs m Q X → Γ "full_propagate" [i64] [i64] xs m Q X)
    (h82 : ∀ xs m Q X, fullAnalyzeSpec xs m Q X → Γ "full_analyze" [i64] [i64] xs m Q X)
    (h97 : ∀ xs m Q X, fullHasBinSpec xs m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] xs m Q X)
    (h98 : ∀ xs m Q X, fullAddBinSpec xs m Q X → Γ "full_add_bin" [i64, i32, i32] [i64] xs m Q X)
    (h99 : ∀ xs m Q X, fullDeleteBinSideSpec xs m Q X →
      Γ "full_delete_bin_side" [i64, i32, i32] [] xs m Q X)
    (h102 : ∀ xs m Q X, fullAddUnitSpec xs m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] xs m Q X)
    (h103 : ∀ xs m Q X, fullLuckyScanSpec xs m Q X →
      Γ "full_lucky_scan" [i64, .bool, .bool] [i64] xs m Q X)
    (h104 : ∀ xs m Q X, fullLuckyPolarSpec xs m Q X → Γ "full_lucky_polar" [i64] [i64] xs m Q X)
    (h106 : ∀ xs m Q X, fullHbrDomSpec xs m Q X →
      Γ "full_hbr_dom" [i64, i32, i32] [i32] xs m Q X)
    (h107 : ∀ xs m Q X, fullProbePropLitSpec xs m Q X →
      Γ "full_probe_prop_lit" [i64, i32] [.bool] xs m Q X)
    (h108 : ∀ xs m Q X, fullProbePropSpec xs m Q X → Γ "full_probe_prop" [i64] [i64] xs m Q X)
    (h109 : ∀ xs m Q X, fullProbeFlushHbrSpec xs m Q X →
      Γ "full_probe_flush_hbr" [i64, i64] [i64] xs m Q X) :
    TableImpl Γ (Full.full3_fns.take 14) (((fullSpecTable mainSpec).drop 97).take 14) := by
  change TableImpl Γ ((Full.full3_fns.take 14).drop 0)
    (((fullSpecTable mainSpec).drop (97 + 0)).take (14 - 0))
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_has_bin_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_add_bin_bridge_wp Γ h97 h27 h15)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_delete_bin_side_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_delete_binary_bridge_wp Γ h99)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_set_inactive_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_add_unit_bridge_wp Γ h30 h27)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_lucky_scan_bridge_wp Γ h28 h30 h49 h82)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_lucky_polar_bridge_wp Γ h11)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_lucky_bridge_wp Γ h104 h103 h28 h30 h49)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_hbr_dom_bridge_wp Γ)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_probe_prop_lit_bridge_wp Γ h45 h15 h106 h27)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_probe_prop_bridge_wp Γ h107)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_probe_flush_hbr_bridge_wp Γ h98 h49)) ?_
  refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
    (.of (full_probe_assume_pair_bridge_wp Γ h28 h108 h30 h82 h49 h109 h102)) ?_
  exact m3_tableImpl_fullSlice_nil (by simp [m3_full3_len])

theorem m3Full_impl_111_128_gen (Γ : Env)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (h11 : ∀ xs m Q X, fullArenaNextSpec xs m Q X → Γ "full_arena_next" [i64, i32] [i32] xs m Q X)
    (h14 : ∀ xs m Q X, fullWstackDefragSpec xs m Q X → Γ "full_wstack_defrag" [i64] [] xs m Q X)
    (h15 : ∀ xs m Q X, fullWatchPushSpec xs m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (h28 : ∀ xs m Q X, fullAssignSpec xs m Q X → Γ "full_assign" [i64, i32, i32] [] xs m Q X)
    (h30 : ∀ xs m Q X, fullBacktrackSpec xs m Q X → Γ "full_backtrack" [i64, i64] [] xs m Q X)
    (h48 : ∀ xs m Q X, fullPropagateIgnoreSpec xs m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] xs m Q X)
    (h49 : ∀ xs m Q X, fullPropagateSpec xs m Q X → Γ "full_propagate" [i64] [i64] xs m Q X)
    (h56 : ∀ xs m Q X, fullUnwatchLargeSpec xs m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] xs m Q X)
    (h57 : ∀ xs m Q X, fullSweepBinsSpec xs m Q X → Γ "full_sweep_bins" [i64] [] xs m Q X)
    (h60 : ∀ xs m Q X, fullArenaSweepSpec xs m Q X → Γ "full_arena_sweep" [i64] [i64] xs m Q X)
    (h94 : ∀ xs m Q X, fullExtendPush2Spec xs m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] xs m Q X)
    (h98 : ∀ xs m Q X, fullAddBinSpec xs m Q X → Γ "full_add_bin" [i64, i32, i32] [i64] xs m Q X)
    (h99 : ∀ xs m Q X, fullDeleteBinSideSpec xs m Q X →
      Γ "full_delete_bin_side" [i64, i32, i32] [] xs m Q X)
    (h101 : ∀ xs m Q X, fullSetInactiveSpec xs m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] xs m Q X)
    (h102 : ∀ xs m Q X, fullAddUnitSpec xs m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] xs m Q X)
    (h110 : ∀ xs m Q X, fullProbeAssumePairSpec xs m Q X →
      Γ "full_probe_assume_pair" [i64, i32] [i64] xs m Q X)
    (h112 : ∀ xs m Q X, fullTransLitSpec xs m Q X →
      Γ "full_trans_lit" [i64, i32] [.bool] xs m Q X)
    (h114 : ∀ xs m Q X, fullVivSimplifySpec xs m Q X →
      Γ "full_viv_simplify" [i64, i32] [i64] xs m Q X)
    (h115 : ∀ xs m Q X, fullVivSortLitsSpec xs m Q X →
      Γ "full_viv_sort_lits" [i64, i64, i32] [] xs m Q X)
    (h116 : ∀ xs m Q X, fullVivDeduceSpec xs m Q X →
      Γ "full_viv_deduce" [i64, i32, i32, i64] [i32] xs m Q X)
    (h117 : ∀ xs m Q X, fullVivCommitSpec xs m Q X →
      Γ "full_viv_commit" [i64, i32, i64, i32, .bool] [i64] xs m Q X)
    (h118 : ∀ xs m Q X, fullVivClauseSpec xs m Q X →
      Γ "full_viv_clause" [i64, i32] [i64] xs m Q X)
    (h120 : ∀ xs m Q X, fullTarjanPopSccSpec xs m Q X →
      Γ "full_tarjan_pop_scc" [i64, i32, i32, i32] [.bool] xs m Q X)
    (h121 : ∀ xs m Q X, fullTarjanSccSpec xs m Q X →
      Γ "full_tarjan_scc" [i64] [i64] xs m Q X)
    (h122 : ∀ xs m Q X, fullSubstElimVarsSpec xs m Q X →
      Γ "full_subst_elim_vars" [i64, i64] [.bool] xs m Q X)
    (h123 : ∀ xs m Q X, fullSubstRewriteBinsSpec xs m Q X →
      Γ "full_subst_rewrite_bins" [i64] [.bool] xs m Q X)
    (h124 : ∀ xs m Q X, fullSubstRewriteArSpec xs m Q X →
      Γ "full_subst_rewrite_ar" [i64] [.bool] xs m Q X) :
    TableImpl Γ
      ((FullFastBveBudgets.fastBveBudgets_fns.drop 1).take 1 ++
       (Full.full3_fns.drop 15).take 1 ++ (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
       (Full.full3_fns.drop 17).take 5 ++ (FullFastBveBudgets.fastBveBudgets_fns.drop 3).take 1 ++
       (Full.full3_fns.drop 23).take 1 ++ (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
       (Full.full3_fns.drop 25).take 3 ++ (FullFastSched.sched_fns.drop 1).take 2 ++
       Full.full3_fns.drop 30)
      ([⟨"full_probe_run", [i64, i64], [i64], fullProbeRunFastSpec, true⟩] ++
       ((fullSpecTable mainSpec).drop 112).take 1 ++
       [⟨"full_transitive", [i64, i64], [i64], fullTransitiveFastSpec, true⟩] ++
       ((fullSpecTable mainSpec).drop 114).take 5 ++
       [⟨"full_vivify", [i64, i64, i64], [i64], fullVivifyFastSpec, true⟩] ++
       ((fullSpecTable mainSpec).drop 120).take 1 ++
       [⟨"full_tarjan_scc", [i64], [i64], fullTarjanSccFastSpec, true⟩] ++
       ((fullSpecTable mainSpec).drop 122).take 3 ++
       (((fullSpecTable mainSpec).drop 125).take 1 ++
         [⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩]) ++
       ((fullSpecTable mainSpec).drop 127).take 1) := by
  rw [show (2 : Nat) = 1 + 1 from rfl, m3_list_drop_take_add]
  simp only [List.append_assoc]
  refine m3_tableImpl_append ?s111 ?_
  · exact m3_tableImpl_singleton rfl rfl rfl rfl (.of (fast_probe_run_wp Γ h30 h110))
  refine m3_tableImpl_append ?s112 ?_ (by simp [m3_full3_len, m3_fullSpecTable_len])
  · change TableImpl Γ (((Full.full3_fns.drop 15).take 1).drop 0)
      (((fullSpecTable mainSpec).drop (112 + 0)).take (1 - 0))
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
      (.of (full_trans_lit_bridge_wp Γ h99 h102))
      (m3_tableImpl_fullSlice_nil (by simp [m3_full3_len]))
  refine m3_tableImpl_append ?s113 ?_
  · exact m3_tableImpl_singleton rfl rfl rfl rfl (.of (fast_transitive_wp Γ h30 h112 h49 h14))
  refine m3_tableImpl_append ?s114 ?_ (by simp [m3_full3_len, m3_fullSpecTable_len])
  · change TableImpl Γ (((Full.full3_fns.drop 17).take 5).drop 0)
      (((fullSpecTable mainSpec).drop (114 + 0)).take (5 - 0))
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
      (.of (full_viv_simplify_bridge_wp Γ h56 h102 h98 h15)) ?_
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_viv_sort_lits_bridge_wp Γ)) ?_
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl (.of (full_viv_deduce_bridge_wp Γ)) ?_
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
      (.of (full_viv_commit_bridge_wp Γ h56 h102 h98 h15)) ?_
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
      (.of (full_viv_clause_bridge_wp Γ h114 h115 h28 h48 h30 h116 h117)) ?_
    exact m3_tableImpl_fullSlice_nil (by simp [m3_full3_len])
  refine m3_tableImpl_append ?s119 ?_
  · exact m3_tableImpl_singleton rfl rfl rfl rfl (.of (fast_vivify_wp Γ h30 h11 h118 h49))
  refine m3_tableImpl_append ?s120 ?_ (by simp [m3_full3_len, m3_fullSpecTable_len])
  · change TableImpl Γ (((Full.full3_fns.drop 23).take 1).drop 0)
      (((fullSpecTable mainSpec).drop (120 + 0)).take (1 - 0))
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
      (.of (full_tarjan_pop_scc_bridge_wp Γ)) (m3_tableImpl_fullSlice_nil (by simp [m3_full3_len]))
  refine m3_tableImpl_append ?s121 ?_
  · exact m3_tableImpl_singleton rfl rfl rfl rfl (.of (fast_tarjan_scc_wp Γ h120))
  refine m3_tableImpl_append ?s122 ?_ (by simp [m3_full3_len, m3_fullSpecTable_len])
  · change TableImpl Γ (((Full.full3_fns.drop 25).take 3).drop 0)
      (((fullSpecTable mainSpec).drop (122 + 0)).take (3 - 0))
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
      (.of (full_subst_elim_vars_bridge_wp Γ h102 h49 h94 h101)) ?_
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
      (.of (full_subst_rewrite_bins_bridge_wp Γ h102 h98)) ?_
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
      (.of (full_subst_rewrite_ar_bridge_wp Γ h11 h102 h98)) ?_
    exact m3_tableImpl_fullSlice_nil (by simp [m3_full3_len])
  refine m3_tableImpl_append ?s125 ?_ (by simp [m3_sched_len, m3_fullSpecTable_len])
  · exact m3_tableImpl_singleton rfl rfl rfl (by simp [m3_fullSpecTable_len])
      (.of (sched_substitute_wp Γ h30 h121 h122 h123 h124 h60 h49))
  refine m3_tableImpl_append ?s126 ?_
  · exact m3_tableImpl_singleton rfl rfl rfl rfl
      (.of (sched_enter_dense_wp Γ h30 h49 h57 h15 h60 h11))
  · change TableImpl Γ ((Full.full3_fns.drop 30).drop 0)
      (((fullSpecTable mainSpec).drop (127 + 0)).take (1 - 0))
    refine m3_tableImpl_fullSlice_step (by omega) rfl rfl
      (.of (full_rebuild_watches_bridge_wp Γ h60 h49))
      (m3_tableImpl_fullSlice_nil (by simp [m3_full3_len]))

/-- Non-reducing indexed version of `TableImpl` avoiding `whnf` on long `List.append` chains. -/
def IndexedImpl (Γ : Env) (fs : List Fn) (tbl : List SpecEntry) : Prop :=
  fs.length = tbl.length ∧
    ∀ i, i < fs.length →
      ∃ fn e, fs[i]? = some fn ∧ tbl[i]? = some e ∧ SpecEntry.Impl Γ fn e

theorem m3_getElem?_of_tableImpl {Γ : Env} :
    ∀ {fs : List Fn} {tbl : List SpecEntry},
    TableImpl Γ fs tbl → ∀ i, i < fs.length → i < tbl.length →
      ∃ fn e, fs[i]? = some fn ∧ tbl[i]? = some e ∧ SpecEntry.Impl Γ fn e
  | _ :: _, _ :: _, ⟨h, _⟩, 0, _, _ => ⟨_, _, rfl, rfl, h⟩
  | _ :: _, _ :: _, ⟨_, hr⟩, i + 1, h1, h2 =>
    m3_getElem?_of_tableImpl hr i (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)

theorem m3_indexedImpl_of_tableImpl {Γ : Env} {fs : List Fn} {tbl : List SpecEntry}
    (hlen : fs.length = tbl.length := by rfl)
    (ht : TableImpl Γ fs tbl) : IndexedImpl Γ fs tbl :=
  ⟨hlen, fun i hi => m3_getElem?_of_tableImpl ht i hi (hlen ▸ hi)⟩

theorem m3_indexedImpl_append {Γ : Env} {fs₁ fs₂ : List Fn} {tbl₁ tbl₂ : List SpecEntry}
    (h1 : IndexedImpl Γ fs₁ tbl₁) (h2 : IndexedImpl Γ fs₂ tbl₂) :
    IndexedImpl Γ (fs₁ ++ fs₂) (tbl₁ ++ tbl₂) := by
  refine ⟨by simp [h1.1, h2.1], fun i hi => ?_⟩
  simp only [List.length_append] at hi
  by_cases hlt : i < fs₁.length
  · obtain ⟨fn, e, hf, he, himpl⟩ := h1.2 i hlt
    exact ⟨fn, e, by rwa [List.getElem?_append_left hlt],
      by rwa [List.getElem?_append_left (h1.1 ▸ hlt)], himpl⟩
  · have hi2 : i - fs₁.length < fs₂.length := by omega
    obtain ⟨fn, e, hf, he, himpl⟩ := h2.2 (i - fs₁.length) hi2
    have hl1 : fs₁.length ≤ i := by omega
    have hl2 : tbl₁.length ≤ i := h1.1 ▸ hl1
    refine ⟨fn, e, ?_, ?_, himpl⟩
    · rw [List.getElem?_append_right hl1, hf]
    · rw [List.getElem?_append_right hl2, ← h1.1, he]

theorem m3_indexedImpl_of_eq {Γ : Env} {fs fs' : List Fn} {tbl tbl' : List SpecEntry}
    (hf : fs = fs') (ht : tbl = tbl') (h : IndexedImpl Γ fs' tbl') :
    IndexedImpl Γ fs tbl := by
  subst hf; subst ht; exact h

theorem m3_fastFnsPrefix_len : FullFast.fastFnsPrefix.length = 128 := by
  simp [FullFast.fastFnsPrefix, m3_fullFns_len, m3_fastBveBudgets_len, m3_fastCore_len,
    m3_sched_len]

theorem m3_fastFnsPrefix_eq_chunks : FullFast.fastFnsPrefix =
    dimacs_fns ++ Full.full1_fns.take 14 ++ (Full.full1_fns.drop 14).take 14 ++
    FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
    (Full.full1_fns.drop 29).take 10 ++ FastCore.fastCore_fns ++
    (Full.full1_fns.drop 42).take 7 ++ FullFastSched.sched_fns.take 1 ++
    Full.full1_fns.drop 50 ++ Full.full2_fns.take 17 ++ (Full.full2_fns.drop 17).take 18 ++
    (Full.full2_fns.drop 35).take 2 ++ Full.full2_fns.drop 37 ++
    Full.full3_fns.take 14 ++
    ((FullFastBveBudgets.fastBveBudgets_fns.drop 1).take 1 ++
     (Full.full3_fns.drop 15).take 1 ++ (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
     (Full.full3_fns.drop 17).take 5 ++ (FullFastBveBudgets.fastBveBudgets_fns.drop 3).take 1 ++
     (Full.full3_fns.drop 23).take 1 ++ (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
     (Full.full3_fns.drop 25).take 3 ++ (FullFastSched.sched_fns.drop 1).take 2 ++
     Full.full3_fns.drop 30) := by
  have hs1 : Full.fullFns.take 36 =
      dimacs_fns ++ Full.full1_fns.take 14 ++ (Full.full1_fns.drop 14).take 14 := by
    rw [show (36 : Nat) = 8 + 28 from rfl, m3_list_take_add, m3_fullFns_take8, m3_fullFns_drop8,
      List.take_append_of_le_length (by simp [m3_full1_len]),
      show (28 : Nat) = 14 + 14 from rfl, m3_list_take_add, List.append_assoc]
  have hs2 : (Full.fullFns.drop 37).take 10 = (Full.full1_fns.drop 29).take 10 :=
    m3_fullFns_drop_slice1 (i := 29) (k := 10) (by omega)
  have hs3 : (Full.fullFns.drop 50).take 7 = (Full.full1_fns.drop 42).take 7 :=
    m3_fullFns_drop_slice1 (i := 42) (k := 7) (by omega)
  have hs4 : (Full.fullFns.drop 58).take 53 =
      Full.full1_fns.drop 50 ++ Full.full2_fns.take 17 ++ (Full.full2_fns.drop 17).take 18 ++
      (Full.full2_fns.drop 35).take 2 ++ Full.full2_fns.drop 37 ++ Full.full3_fns.take 14 := by
    rw [show (53 : Nat) = 1 + 52 from rfl, m3_list_drop_take_add,
      m3_fullFns_drop_slice1 (i := 50) (k := 1) (by omega),
      show (Full.full1_fns.drop 50).take 1 = Full.full1_fns.drop 50 by
        rw [List.take_of_length_le (by simp [m3_full1_len])],
      show (52 : Nat) = 38 + 14 from rfl, m3_list_drop_take_add,
      show (38 : Nat) = 17 + 21 from rfl, m3_list_drop_take_add,
      show (21 : Nat) = 18 + 3 from rfl, m3_list_drop_take_add,
      show (3 : Nat) = 2 + 1 from rfl, m3_list_drop_take_add,
      m3_fullFns_drop_slice2 (i := 0) (k := 17) (by omega), List.drop_zero,
      m3_fullFns_drop_slice2 (i := 17) (k := 18) (by omega),
      m3_fullFns_drop_slice2 (i := 35) (k := 2) (by omega),
      m3_fullFns_drop_slice2 (i := 37) (k := 1) (by omega),
      show (Full.full2_fns.drop 37).take 1 = Full.full2_fns.drop 37 by
        rw [List.take_of_length_le (by simp [m3_full2_len])],
      m3_fullFns_drop_slice3 (i := 0) (k := 14) (by omega), List.drop_zero]
    simp only [List.append_assoc]
  have hs5 : (Full.fullFns.drop 112).take 1 = (Full.full3_fns.drop 15).take 1 :=
    m3_fullFns_drop_slice3 (i := 15) (k := 1) (by omega)
  have hs6 : (Full.fullFns.drop 114).take 5 = (Full.full3_fns.drop 17).take 5 :=
    m3_fullFns_drop_slice3 (i := 17) (k := 5) (by omega)
  have hs7 : (Full.fullFns.drop 120).take 1 = (Full.full3_fns.drop 23).take 1 :=
    m3_fullFns_drop_slice3 (i := 23) (k := 1) (by omega)
  have hs8 : (Full.fullFns.drop 122).take 3 = (Full.full3_fns.drop 25).take 3 :=
    m3_fullFns_drop_slice3 (i := 25) (k := 3) (by omega)
  have hs9 : (Full.fullFns.drop 127).take 1 = Full.full3_fns.drop 30 := by
    rw [m3_fullFns_drop_slice3 (i := 30) (k := 1) (by omega),
      List.take_of_length_le (by simp [m3_full3_len])]
  simp only [FullFast.fastFnsPrefix, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9,
    List.append_assoc]

/-- Unlanded internal M2b helper contracts (`FullDefSweep` / `FullBvaHeap` internals) parameterized
so `m3FullSpecTable` and `m3Full_moduleOk_of_m2b` accept arbitrary concrete M2b proofs. -/
structure M2bInternalSpecs where
  find_definition : Spec [i64, i32, i32, i32] []
  sweep_cone : Spec [i64, i32] [i64]
  sweep_refine_kitten : Spec [i64, i32, i32] []
  sweep_var : Spec [i64, i32, i64] [i64]
  bva_hop1 : Spec [i64, i32, i32] [i64]
  bva_hop2 : Spec [i64, i32, i32] [i64]
  bva_hop3 : Spec [i64, i32, i32] [i64]
  bva_match_large : Spec [i64, i32, i32, i32] [.bool]
  bva_scan_cands : Spec [i64, i32, i32, i64] [i32]
  bva_pick_cand : Spec [i64, i32, i32] [i32]
  bva_filter_row : Spec [i64, i32, i32, i32, i32, i32] [i32]
  bva_commit : Spec [i64, i32] [.bool]
  bva_try_lit : Spec [i64, i32, i64] [.bool]
  fheap_up : Spec [i64, i64, i64, i32] []
  fheap_down : Spec [i64, i64, i64, i32, i32] []

/-- Default instantiation for the `15` private unlanded M2b internal helpers (unused along
top-level UNSAT soundness & concrete non-vacuity executions). -/
def m3DefaultExtSpecs : M2bInternalSpecs where
  find_definition := fun _ _ _ _ => False
  sweep_cone := fun _ _ _ _ => False
  sweep_refine_kitten := fun _ _ _ _ => False
  sweep_var := fun _ _ _ _ => False
  bva_hop1 := fun _ _ _ _ => False
  bva_hop2 := fun _ _ _ _ => False
  bva_hop3 := fun _ _ _ _ => False
  bva_match_large := fun _ _ _ _ => False
  bva_scan_cands := fun _ _ _ _ => False
  bva_pick_cand := fun _ _ _ _ => False
  bva_filter_row := fun _ _ _ _ => False
  bva_commit := fun _ _ _ _ => False
  bva_try_lit := fun _ _ _ _ => False
  fheap_up := fun _ _ _ _ => False
  fheap_down := fun _ _ _ _ => False

/-- Prefix `[0..128)` specification table matching `FullFast.fastFnsPrefix` 1-to-1. -/
def m3FullSpecPrefix (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : List SpecEntry :=
  let base := fullSpecTable mainSpec
  base.take 36 ++
  ([ ⟨"full_init_hdr", [i64, i64, i64, i64], [], fullFastInitHdrSpec, true⟩ ] ++
  ((base.drop 37).take 57 ++
  ([ ⟨"full_extend_push2", [i64, i32, i32], [.bool], fullExtendPush2TmkSpec, true⟩
   , ⟨"full_extend_push_cl", [i64, i32, i32], [.bool], fullExtendPushClTmkSpec, true⟩ ] ++
  ((base.drop 96).take 15 ++
  ([ ⟨"full_probe_run", [i64, i64], [i64], fullProbeRunFastSpec, true⟩ ] ++
  ((base.drop 112).take 1 ++
  ([ ⟨"full_transitive", [i64, i64], [i64], fullTransitiveFastSpec, true⟩ ] ++
  ((base.drop 114).take 5 ++
  ([ ⟨"full_vivify", [i64, i64, i64], [i64], fullVivifyFastSpec, true⟩ ] ++
  ((base.drop 120).take 1 ++
  ([ ⟨"full_tarjan_scc", [i64], [i64], fullTarjanSccFastSpec, true⟩ ] ++
  ((base.drop 122).take 4 ++
  ([ ⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩ ] ++
  (base.drop 127).take 1)))))))))))))

def m3SufCong6 : List SpecEntry :=
  [ ⟨"full_cong_mark_trail", [i64, i64, i32], [], m3CongMarkTrailSpec, true⟩
  , ⟨"full_cong_unit_fold", [i64, i32, i32], [i64], m3CongUnitFoldSpec, true⟩
  , ⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64], m3CongEquivFoldSpec, true⟩
  , ⟨"full_cong_and_match", [i64, i32, i32], [.bool], m3CongAndMatchSpec, true⟩
  , ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64], m3CongWorkStepSpec, true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], m3CongruenceDenseSpec, true⟩ ]

def m3SufSweep4 (ext : M2bInternalSpecs) : List SpecEntry :=
  [ ⟨"full_sweep_cone", [i64, i32], [i64], ext.sweep_cone, true⟩
  , ⟨"full_sweep_refine_kitten", [i64, i32, i32], [], ext.sweep_refine_kitten, true⟩
  , ⟨"full_sweep_var", [i64, i32, i64], [i64], ext.sweep_var, true⟩
  , ⟨"full_sweep_dense", [i64, i64, i64], [i64], fullSweepDenseSpec, true⟩ ]

def m3SufDef3 (ext : M2bInternalSpecs) : List SpecEntry :=
  [ ⟨"full_bve_mark_and", [i64, i32, i32, i32, i32], [.bool], fullBveMarkAndSpec, true⟩
  , ⟨"full_find_definition", [i64, i32, i32, i32], [], ext.find_definition, true⟩
  , ⟨"full_bve_gates", [i64, i32, i32, i32], [], fullBveGatesDefFastSpec, true⟩ ]

def m3SufBvaHeap (ext : M2bInternalSpecs) : List SpecEntry :=
  [ ⟨"full_init_fresh_var", [i64, i32], [], fullInitFreshVarSpec, true⟩
  , ⟨"full_bva_hop1", [i64, i32, i32], [i64], ext.bva_hop1, true⟩
  , ⟨"full_bva_hop2", [i64, i32, i32], [i64], ext.bva_hop2, true⟩
  , ⟨"full_bva_hop3", [i64, i32, i32], [i64], ext.bva_hop3, true⟩
  , ⟨"full_bva_match_large", [i64, i32, i32, i32], [.bool], ext.bva_match_large, true⟩
  , ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32], ext.bva_scan_cands, true⟩
  , ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], ext.bva_pick_cand, true⟩
  , ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32], ext.bva_filter_row, true⟩
  , ⟨"full_bva_commit", [i64, i32], [.bool], ext.bva_commit, true⟩
  , ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], ext.bva_try_lit, true⟩
  , ⟨"full_fheap_up", [i64, i64, i64, i32], [], ext.fheap_up, true⟩
  , ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [], ext.fheap_down, true⟩
  , ⟨"full_factor", [i64, i64], [i64], fullFactorHeapSpec, true⟩ ]

def m3SufTail : List SpecEntry :=
  [ ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
  , ⟨"full_max_u64", [i64, i64], [i64], schedMaxU64Spec, true⟩
  , ⟨"full_probe_dticks", [i64, .bool], [i64], schedProbeDticksSpec, true⟩
  , ⟨"full_probe_tail", [i64, i64], [i64], schedProbeTailSpec, true⟩
  , ⟨"full_probe", [i64, .bool], [i64], m3ProbeSpec, true⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩
  , ⟨"full_elim_collect_nbrs", [i64, i32], [i64], m3ElimCollectNbrsSpec, true⟩
  , ⟨"full_elim_bve", [i64, i64], [i64], m3ElimBveSpec, true⟩
  , ⟨"full_eliminate", [i64, .bool], [i64], m3EliminateSpec, true⟩
  , ⟨"full_preprocess", [i64], [i64], m3PreprocessSpec, true⟩
  , ⟨"full_simplify", [i64, .bool, .bool], [i64], schedSimplifySpec, true⟩
  , ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩ ]

/-- Suffix `[128..201)` specification table matching `FullFast.fastFnsSuffix.flatMap m3Splice`
1-to-1 (`73` rows). -/
def m3FullSpecSuffix (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : List SpecEntry :=
  let base := fullSpecTable mainSpec
  fullKittenSpecTable ++
  (base.drop 128).take 7 ++
  [ ⟨"full_cong_extract", [i64, i64, i64], [i64], fullCongExtractTickSpec, true⟩ ] ++
  m3SufCong6 ++
  m3SufSweep4 ext ++
  (base.drop 145).take 2 ++
  [ ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩ ] ++
  (base.drop 148).take 1 ++
  m3SufDef3 ext ++
  (base.drop 151).take 1 ++
  [ ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool], fullBveWeakenTmkSpec, true⟩ ] ++
  (base.drop 153).take 1 ++
  [ ⟨"full_bve_commit_res", [i64, i64, i64], [i64], fullBveCommitResTmkSpec, true⟩ ] ++
  (base.drop 155).take 1 ++
  [ ⟨"full_bve_var", [i64, i32], [i64], fullBveVarDefSpec, true⟩ ] ++
  m3SufBvaHeap ext ++
  m3SufTail ++
  base.drop 165

/-- Complete `201`-row specification table aligned 1-to-1 with `m3Fns`. -/
def m3FullSpecTable (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) : List SpecEntry :=
  m3FullSpecPrefix mainSpec ++ m3FullSpecSuffix ext mainSpec

theorem fullSpecTable_len (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (fullSpecTable mainSpec).length = 166 := by
  rw [← List.length_map (f := fun e => (e.name, e.as, e.rs)), fullSpecTable_sigs,
    List.length_map, m3_fullFns_len]

theorem kittenSpecTable_len : fullKittenSpecTable.length = 15 := by
  simp [fullKittenSpecTable]

theorem m3SufCong6_len : m3SufCong6.length = 6 := by simp [m3SufCong6]
theorem m3SufSweep4_len (ext : M2bInternalSpecs) : (m3SufSweep4 ext).length = 4 := by
  simp [m3SufSweep4]
theorem m3SufDef3_len (ext : M2bInternalSpecs) : (m3SufDef3 ext).length = 3 := by
  simp [m3SufDef3]
theorem m3SufBvaHeap_len (ext : M2bInternalSpecs) : (m3SufBvaHeap ext).length = 13 := by
  simp [m3SufBvaHeap]
theorem m3SufTail_len : m3SufTail.length = 13 := by simp [m3SufTail]

theorem m3FullSpecPrefix_len (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecPrefix mainSpec).length = 128 := by
  simp [m3FullSpecPrefix, fullSpecTable_len]

theorem m3FullSpecPrefix_getElem?_lt36
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {n : Nat} (hn : n < 36) :
    (m3FullSpecPrefix mainSpec)[n]? = (fullSpecTable mainSpec)[n]? := by
  unfold m3FullSpecPrefix
  simp only [List.getElem?_append, List.length_take, fullSpecTable_len,
    show min 36 166 = 36 from rfl, hn, ↓reduceIte, List.getElem?_take]

theorem m3FullSpecPrefix_getElem?_36
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecPrefix mainSpec)[36]? =
      some ⟨"full_init_hdr", [i64, i64, i64, i64], [], fullFastInitHdrSpec, true⟩ := by
  unfold m3FullSpecPrefix
  simp only [List.getElem?_append, List.length_take, fullSpecTable_len,
    List.length_singleton, show min 36 166 = 36 from rfl,
    show ¬(36 < 36) by omega, show 36 - 36 < 1 by omega, ↓reduceIte]
  rfl

theorem m3FullSpecPrefix_getElem?_37_94
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {n : Nat} (h1 : 37 ≤ n) (h2 : n < 94) :
    (m3FullSpecPrefix mainSpec)[n]? = (fullSpecTable mainSpec)[n]? := by
  unfold m3FullSpecPrefix
  simp only [List.getElem?_append, List.length_take, List.length_drop,
    fullSpecTable_len, List.length_singleton,
    show min 36 166 = 36 from rfl, show min 57 (166 - 37) = 57 from rfl,
    show ¬(n < 36) by omega, show ¬(n - 36 < 1) by omega, show n - 36 - 1 < 57 by omega,
    ↓reduceIte, List.getElem?_take, List.getElem?_drop]
  rw [show 37 + (n - 36 - 1) = n by omega]

theorem m3FullSpecPrefix_getElem?_94_96
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {k : Nat} (hk : k < 2) :
    (m3FullSpecPrefix mainSpec)[94 + k]? =
      ([ ⟨"full_extend_push2", [i64, i32, i32], [.bool], fullExtendPush2TmkSpec, true⟩
       , ⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
          fullExtendPushClTmkSpec, true⟩ ])[k]? := by
  unfold m3FullSpecPrefix
  simp only [List.getElem?_append, List.length_take, List.length_drop,
    fullSpecTable_len, List.length_cons, List.length_nil,
    show min 36 166 = 36 from rfl, show (0 : Nat) + 1 = 1 from rfl,
    show min 57 (166 - 37) = 57 from rfl, show 0 + 1 + 1 = 2 from rfl,
    show ¬(94 + k < 36) by omega, show ¬(94 + k - 36 < 1) by omega,
    show ¬(94 + k - 36 - 1 < 57) by omega, show 94 + k - 36 - 1 - 57 < 2 by omega, ↓reduceIte]
  rw [show 94 + k - 36 - 1 - 57 = k by omega]

theorem m3FullSpecPrefix_getElem?_96_111
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {n : Nat} (h1 : 96 ≤ n) (h2 : n < 111) :
    (m3FullSpecPrefix mainSpec)[n]? = (fullSpecTable mainSpec)[n]? := by
  unfold m3FullSpecPrefix
  simp only [List.getElem?_append, List.length_take, List.length_drop,
    fullSpecTable_len, List.length_cons, List.length_nil,
    show min 36 166 = 36 from rfl, show (0 : Nat) + 1 = 1 from rfl,
    show min 57 (166 - 37) = 57 from rfl, show 0 + 1 + 1 = 2 from rfl,
    show min 15 (166 - 96) = 15 from rfl, show ¬(n < 36) by omega,
    show ¬(n - 36 < 1) by omega, show ¬(n - 36 - 1 < 57) by omega,
    show ¬(n - 36 - 1 - 57 < 2) by omega, show n - 36 - 1 - 57 - 2 < 15 by omega,
    ↓reduceIte, List.getElem?_take, List.getElem?_drop]
  rw [show 96 + (n - 36 - 1 - 57 - 2) = n by omega]

theorem m3FullSpecPrefix_getElem?_122_126
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {n : Nat} (h1 : 122 ≤ n) (h2 : n < 126) :
    (m3FullSpecPrefix mainSpec)[n]? = (fullSpecTable mainSpec)[n]? := by
  unfold m3FullSpecPrefix
  simp only [List.getElem?_append, List.length_take, List.length_drop,
    fullSpecTable_len, List.length_cons, List.length_nil,
    show min 36 166 = 36 from rfl, show (0 : Nat) + 1 = 1 from rfl,
    show min 57 (166 - 37) = 57 from rfl, show 0 + 1 + 1 = 2 from rfl,
    show min 15 (166 - 96) = 15 from rfl, show min 1 (166 - 112) = 1 from rfl,
    show min 5 (166 - 114) = 5 from rfl, show min 1 (166 - 120) = 1 from rfl,
    show min 4 (166 - 122) = 4 from rfl, show ¬(n < 36) by omega,
    show ¬(n - 36 < 1) by omega, show ¬(n - 36 - 1 < 57) by omega,
    show ¬(n - 36 - 1 - 57 < 2) by omega, show ¬(n - 36 - 1 - 57 - 2 < 15) by omega,
    show ¬(n - 36 - 1 - 57 - 2 - 15 < 1) by omega,
    show ¬(n - 36 - 1 - 57 - 2 - 15 - 1 < 1) by omega,
    show ¬(n - 36 - 1 - 57 - 2 - 15 - 1 - 1 < 1) by omega,
    show ¬(n - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 < 5) by omega,
    show ¬(n - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 < 1) by omega,
    show ¬(n - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 - 1 < 1) by omega,
    show ¬(n - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 - 1 - 1 < 1) by omega,
    show n - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 - 1 - 1 - 1 < 4 by omega,
    ↓reduceIte, List.getElem?_take, List.getElem?_drop]
  rw [show 122 + (n - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 - 1 - 1 - 1) = n by omega]

theorem m3FullSpecPrefix_getElem?_126
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecPrefix mainSpec)[126]? =
      some ⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩ := by
  unfold m3FullSpecPrefix
  simp only [List.getElem?_append, List.length_take, List.length_drop,
    fullSpecTable_len, List.length_cons, List.length_nil,
    show min 36 166 = 36 from rfl, show (0 : Nat) + 1 = 1 from rfl,
    show min 57 (166 - 37) = 57 from rfl, show 0 + 1 + 1 = 2 from rfl,
    show min 15 (166 - 96) = 15 from rfl, show min 1 (166 - 112) = 1 from rfl,
    show min 5 (166 - 114) = 5 from rfl, show min 1 (166 - 120) = 1 from rfl,
    show min 4 (166 - 122) = 4 from rfl, show ¬(126 < 36) by omega,
    show ¬(126 - 36 < 1) by omega, show ¬(126 - 36 - 1 < 57) by omega,
    show ¬(126 - 36 - 1 - 57 < 2) by omega, show ¬(126 - 36 - 1 - 57 - 2 < 15) by omega,
    show ¬(126 - 36 - 1 - 57 - 2 - 15 < 1) by omega,
    show ¬(126 - 36 - 1 - 57 - 2 - 15 - 1 < 1) by omega,
    show ¬(126 - 36 - 1 - 57 - 2 - 15 - 1 - 1 < 1) by omega,
    show ¬(126 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 < 5) by omega,
    show ¬(126 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 < 1) by omega,
    show ¬(126 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 - 1 < 1) by omega,
    show ¬(126 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 - 1 - 1 < 1) by omega,
    show ¬(126 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 - 1 - 1 - 1 < 4) by omega,
    show 126 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 - 1 - 1 - 1 - 4 < 1 by omega,
    ↓reduceIte]
  rfl

theorem m3FullSpecPrefix_getElem?_127
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecPrefix mainSpec)[127]? = (fullSpecTable mainSpec)[127]? := by
  unfold m3FullSpecPrefix
  simp only [List.getElem?_append, List.length_take, List.length_drop,
    fullSpecTable_len, List.length_cons, List.length_nil,
    show min 36 166 = 36 from rfl, show (0 : Nat) + 1 = 1 from rfl,
    show min 57 (166 - 37) = 57 from rfl, show 0 + 1 + 1 = 2 from rfl,
    show min 15 (166 - 96) = 15 from rfl, show min 1 (166 - 112) = 1 from rfl,
    show min 5 (166 - 114) = 5 from rfl, show min 1 (166 - 120) = 1 from rfl,
    show min 4 (166 - 122) = 4 from rfl,
    show ¬(127 < 36) by omega, show ¬(127 - 36 < 1) by omega,
    show ¬(127 - 36 - 1 < 57) by omega, show ¬(127 - 36 - 1 - 57 < 2) by omega,
    show ¬(127 - 36 - 1 - 57 - 2 < 15) by omega,
    show ¬(127 - 36 - 1 - 57 - 2 - 15 < 1) by omega,
    show ¬(127 - 36 - 1 - 57 - 2 - 15 - 1 < 1) by omega,
    show ¬(127 - 36 - 1 - 57 - 2 - 15 - 1 - 1 < 1) by omega,
    show ¬(127 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 < 5) by omega,
    show ¬(127 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 < 1) by omega,
    show ¬(127 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 - 1 < 1) by omega,
    show ¬(127 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 - 1 - 1 < 1) by omega,
    show ¬(127 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 - 1 - 1 - 1 < 4) by omega,
    show ¬(127 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 - 1 - 1 - 1 - 4 < 1) by omega,
    ↓reduceIte, List.getElem?_take, List.getElem?_drop]
  rfl

theorem m3FullSpecPrefix_getElem?_111
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecPrefix mainSpec)[111]? =
      some ⟨"full_probe_run", [i64, i64], [i64], fullProbeRunFastSpec, true⟩ := by
  unfold m3FullSpecPrefix
  simp only [List.getElem?_append, List.length_take, List.length_drop,
    fullSpecTable_len, List.length_cons, List.length_nil,
    show min 36 166 = 36 from rfl, show (0 : Nat) + 1 = 1 from rfl,
    show min 57 (166 - 37) = 57 from rfl, show 0 + 1 + 1 = 2 from rfl,
    show min 15 (166 - 96) = 15 from rfl, show ¬(111 < 36) by omega,
    show ¬(111 - 36 < 1) by omega, show ¬(111 - 36 - 1 < 57) by omega,
    show ¬(111 - 36 - 1 - 57 < 2) by omega, show ¬(111 - 36 - 1 - 57 - 2 < 15) by omega,
    show 111 - 36 - 1 - 57 - 2 - 15 < 1 by omega, ↓reduceIte]
  rfl

theorem m3FullSpecPrefix_getElem?_112
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecPrefix mainSpec)[112]? = (fullSpecTable mainSpec)[112]? := by
  unfold m3FullSpecPrefix
  simp only [List.getElem?_append, List.length_take, List.length_drop,
    fullSpecTable_len, List.length_cons, List.length_nil,
    show min 36 166 = 36 from rfl, show (0 : Nat) + 1 = 1 from rfl,
    show min 57 (166 - 37) = 57 from rfl, show 0 + 1 + 1 = 2 from rfl,
    show min 15 (166 - 96) = 15 from rfl, show min 1 (166 - 112) = 1 from rfl,
    show ¬(112 < 36) by omega, show ¬(112 - 36 < 1) by omega,
    show ¬(112 - 36 - 1 < 57) by omega, show ¬(112 - 36 - 1 - 57 < 2) by omega,
    show ¬(112 - 36 - 1 - 57 - 2 < 15) by omega,
    show ¬(112 - 36 - 1 - 57 - 2 - 15 < 1) by omega,
    show 112 - 36 - 1 - 57 - 2 - 15 - 1 < 1 by omega, ↓reduceIte,
    List.getElem?_take, List.getElem?_drop]

theorem m3FullSpecPrefix_getElem?_113
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecPrefix mainSpec)[113]? =
      some ⟨"full_transitive", [i64, i64], [i64], fullTransitiveFastSpec, true⟩ := by
  unfold m3FullSpecPrefix
  simp only [List.getElem?_append, List.length_take, List.length_drop,
    fullSpecTable_len, List.length_cons, List.length_nil,
    show min 36 166 = 36 from rfl, show (0 : Nat) + 1 = 1 from rfl,
    show min 57 (166 - 37) = 57 from rfl, show 0 + 1 + 1 = 2 from rfl,
    show min 15 (166 - 96) = 15 from rfl, show min 1 (166 - 112) = 1 from rfl,
    show ¬(113 < 36) by omega, show ¬(113 - 36 < 1) by omega,
    show ¬(113 - 36 - 1 < 57) by omega, show ¬(113 - 36 - 1 - 57 < 2) by omega,
    show ¬(113 - 36 - 1 - 57 - 2 < 15) by omega,
    show ¬(113 - 36 - 1 - 57 - 2 - 15 < 1) by omega,
    show ¬(113 - 36 - 1 - 57 - 2 - 15 - 1 < 1) by omega,
    show 113 - 36 - 1 - 57 - 2 - 15 - 1 - 1 < 1 by omega, ↓reduceIte]
  rfl

theorem m3FullSpecPrefix_getElem?_114_119
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {n : Nat} (h1 : 114 ≤ n) (h2 : n < 119) :
    (m3FullSpecPrefix mainSpec)[n]? = (fullSpecTable mainSpec)[n]? := by
  unfold m3FullSpecPrefix
  simp only [List.getElem?_append, List.length_take, List.length_drop,
    fullSpecTable_len, List.length_cons, List.length_nil,
    show min 36 166 = 36 from rfl, show (0 : Nat) + 1 = 1 from rfl,
    show min 57 (166 - 37) = 57 from rfl, show 0 + 1 + 1 = 2 from rfl,
    show min 15 (166 - 96) = 15 from rfl, show min 1 (166 - 112) = 1 from rfl,
    show min 5 (166 - 114) = 5 from rfl, show ¬(n < 36) by omega,
    show ¬(n - 36 < 1) by omega, show ¬(n - 36 - 1 < 57) by omega,
    show ¬(n - 36 - 1 - 57 < 2) by omega, show ¬(n - 36 - 1 - 57 - 2 < 15) by omega,
    show ¬(n - 36 - 1 - 57 - 2 - 15 < 1) by omega,
    show ¬(n - 36 - 1 - 57 - 2 - 15 - 1 < 1) by omega,
    show ¬(n - 36 - 1 - 57 - 2 - 15 - 1 - 1 < 1) by omega,
    show n - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 < 5 by omega, ↓reduceIte,
    List.getElem?_take, List.getElem?_drop]
  rw [show 114 + (n - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1) = n by omega]

theorem m3FullSpecPrefix_getElem?_119
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecPrefix mainSpec)[119]? =
      some ⟨"full_vivify", [i64, i64, i64], [i64], fullVivifyFastSpec, true⟩ := by
  unfold m3FullSpecPrefix
  simp only [List.getElem?_append, List.length_take, List.length_drop,
    fullSpecTable_len, List.length_cons, List.length_nil,
    show min 36 166 = 36 from rfl, show (0 : Nat) + 1 = 1 from rfl,
    show min 57 (166 - 37) = 57 from rfl, show 0 + 1 + 1 = 2 from rfl,
    show min 15 (166 - 96) = 15 from rfl, show min 1 (166 - 112) = 1 from rfl,
    show min 5 (166 - 114) = 5 from rfl, show ¬(119 < 36) by omega,
    show ¬(119 - 36 < 1) by omega, show ¬(119 - 36 - 1 < 57) by omega,
    show ¬(119 - 36 - 1 - 57 < 2) by omega, show ¬(119 - 36 - 1 - 57 - 2 < 15) by omega,
    show ¬(119 - 36 - 1 - 57 - 2 - 15 < 1) by omega,
    show ¬(119 - 36 - 1 - 57 - 2 - 15 - 1 < 1) by omega,
    show ¬(119 - 36 - 1 - 57 - 2 - 15 - 1 - 1 < 1) by omega,
    show ¬(119 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 < 5) by omega,
    show 119 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 < 1 by omega, ↓reduceIte]
  rfl

theorem m3FullSpecPrefix_getElem?_120
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecPrefix mainSpec)[120]? = (fullSpecTable mainSpec)[120]? := by
  unfold m3FullSpecPrefix
  simp only [List.getElem?_append, List.length_take, List.length_drop,
    fullSpecTable_len, List.length_cons, List.length_nil,
    show min 36 166 = 36 from rfl, show (0 : Nat) + 1 = 1 from rfl,
    show min 57 (166 - 37) = 57 from rfl, show 0 + 1 + 1 = 2 from rfl,
    show min 15 (166 - 96) = 15 from rfl, show min 1 (166 - 112) = 1 from rfl,
    show min 5 (166 - 114) = 5 from rfl, show min 1 (166 - 120) = 1 from rfl,
    show ¬(120 < 36) by omega, show ¬(120 - 36 < 1) by omega,
    show ¬(120 - 36 - 1 < 57) by omega, show ¬(120 - 36 - 1 - 57 < 2) by omega,
    show ¬(120 - 36 - 1 - 57 - 2 < 15) by omega,
    show ¬(120 - 36 - 1 - 57 - 2 - 15 < 1) by omega,
    show ¬(120 - 36 - 1 - 57 - 2 - 15 - 1 < 1) by omega,
    show ¬(120 - 36 - 1 - 57 - 2 - 15 - 1 - 1 < 1) by omega,
    show ¬(120 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 < 5) by omega,
    show ¬(120 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 < 1) by omega,
    show 120 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 - 1 < 1 by omega, ↓reduceIte,
    List.getElem?_take, List.getElem?_drop]

theorem m3FullSpecPrefix_getElem?_121
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecPrefix mainSpec)[121]? =
      some ⟨"full_tarjan_scc", [i64], [i64], fullTarjanSccFastSpec, true⟩ := by
  unfold m3FullSpecPrefix
  simp only [List.getElem?_append, List.length_take, List.length_drop,
    fullSpecTable_len, List.length_cons, List.length_nil,
    show min 36 166 = 36 from rfl, show (0 : Nat) + 1 = 1 from rfl,
    show min 57 (166 - 37) = 57 from rfl, show 0 + 1 + 1 = 2 from rfl,
    show min 15 (166 - 96) = 15 from rfl, show min 1 (166 - 112) = 1 from rfl,
    show min 5 (166 - 114) = 5 from rfl, show min 1 (166 - 120) = 1 from rfl,
    show ¬(121 < 36) by omega, show ¬(121 - 36 < 1) by omega,
    show ¬(121 - 36 - 1 < 57) by omega, show ¬(121 - 36 - 1 - 57 < 2) by omega,
    show ¬(121 - 36 - 1 - 57 - 2 < 15) by omega,
    show ¬(121 - 36 - 1 - 57 - 2 - 15 < 1) by omega,
    show ¬(121 - 36 - 1 - 57 - 2 - 15 - 1 < 1) by omega,
    show ¬(121 - 36 - 1 - 57 - 2 - 15 - 1 - 1 < 1) by omega,
    show ¬(121 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 < 5) by omega,
    show ¬(121 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 < 1) by omega,
    show ¬(121 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 - 1 < 1) by omega,
    show 121 - 36 - 1 - 57 - 2 - 15 - 1 - 1 - 1 - 5 - 1 - 1 < 1 by omega, ↓reduceIte]
  rfl

theorem m3FullSpecTable_getElem?_lt128 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {n : Nat} (hn : n < 128) :
    (m3FullSpecTable ext mainSpec)[n]? = (m3FullSpecPrefix mainSpec)[n]? := by
  unfold m3FullSpecTable
  rw [List.getElem?_append_left (by rw [m3FullSpecPrefix_len]; exact hn)]

theorem m3FullSpecTable_getElem?_suf (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {k : Nat} :
    (m3FullSpecTable ext mainSpec)[128 + k]? = (m3FullSpecSuffix ext mainSpec)[k]? := by
  unfold m3FullSpecTable
  have h128 : (m3FullSpecPrefix mainSpec).length = 128 := m3FullSpecPrefix_len mainSpec
  rw [List.getElem?_append_right (by omega), h128, show 128 + k - 128 = k by omega]

theorem m3FullSpecTable_getElem?_suf_at (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) (n k : Nat)
    (h : n = 128 + k := by omega) :
    (m3FullSpecTable ext mainSpec)[n]? = (m3FullSpecSuffix ext mainSpec)[k]? := by
  subst h; exact m3FullSpecTable_getElem?_suf ext mainSpec

theorem m3FullSpecSuffix_getElem?_lt15 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {k : Nat} (hk : k < 15) :
    (m3FullSpecSuffix ext mainSpec)[k]? = fullKittenSpecTable[k]? := by
  unfold m3FullSpecSuffix
  simp only [List.append_assoc]
  rw [List.getElem?_append_left (by rw [kittenSpecTable_len]; exact hk)]

theorem m3FullSpecSuffix_getElem?_15_22 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {k : Nat} (_hk : k < 7) :
    (m3FullSpecSuffix ext mainSpec)[15 + k]? = (fullSpecTable mainSpec)[128 + k]? := by
  unfold m3FullSpecSuffix
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullSpecTable_len, kittenSpecTable_len, show min 7 (166 - 128) = 7 from rfl,
    show ¬(15 + k < 15) by omega, show 15 + k - 15 < 7 by omega, ↓reduceIte,
    List.getElem?_take, List.getElem?_drop]
  rw [show 128 + (15 + k - 15) = 128 + k by omega]

theorem m3FullSpecSuffix_getElem?_22 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecSuffix ext mainSpec)[22]? =
      some ⟨"full_cong_extract", [i64, i64, i64], [i64], fullCongExtractTickSpec, true⟩ := by
  unfold m3FullSpecSuffix
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_singleton, fullSpecTable_len, kittenSpecTable_len,
    show min 7 (166 - 128) = 7 from rfl, show ¬(22 < 15) by omega,
    show ¬(22 - 15 < 7) by omega, show 22 - 15 - 7 < 1 by omega, ↓reduceIte]
  rfl

theorem m3FullSpecSuffix_getElem?_23_29 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {k : Nat} (hk : k < 6) :
    (m3FullSpecSuffix ext mainSpec)[23 + k]? = m3SufCong6[k]? := by
  unfold m3FullSpecSuffix
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_singleton, fullSpecTable_len, kittenSpecTable_len, m3SufCong6_len,
    show min 7 (166 - 128) = 7 from rfl, show ¬(23 + k < 15) by omega,
    show ¬(23 + k - 15 < 7) by omega, show ¬(23 + k - 15 - 7 < 1) by omega,
    show 23 + k - 15 - 7 - 1 < 6 by omega, ↓reduceIte]
  rw [show 23 + k - 15 - 7 - 1 = k by omega]

theorem m3FullSpecSuffix_getElem?_29_33 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {k : Nat} (hk : k < 4) :
    (m3FullSpecSuffix ext mainSpec)[29 + k]? = (m3SufSweep4 ext)[k]? := by
  unfold m3FullSpecSuffix
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_singleton, fullSpecTable_len, kittenSpecTable_len, m3SufCong6_len, m3SufSweep4_len,
    show min 7 (166 - 128) = 7 from rfl, show ¬(29 + k < 15) by omega,
    show ¬(29 + k - 15 < 7) by omega, show ¬(29 + k - 15 - 7 < 1) by omega,
    show ¬(29 + k - 15 - 7 - 1 < 6) by omega, show 29 + k - 15 - 7 - 1 - 6 < 4 by omega,
    ↓reduceIte]
  rw [show 29 + k - 15 - 7 - 1 - 6 = k by omega]

theorem m3FullSpecSuffix_getElem?_33_35 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {k : Nat} (hk : k < 2) :
    (m3FullSpecSuffix ext mainSpec)[33 + k]? = (fullSpecTable mainSpec)[145 + k]? := by
  unfold m3FullSpecSuffix
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_singleton, fullSpecTable_len, kittenSpecTable_len, m3SufCong6_len,
    m3SufSweep4_len, show min 7 (166 - 128) = 7 from rfl, show min 2 (166 - 145) = 2 from rfl,
    show ¬(33 + k < 15) by omega, show ¬(33 + k - 15 < 7) by omega,
    show ¬(33 + k - 15 - 7 < 1) by omega, show ¬(33 + k - 15 - 7 - 1 < 6) by omega,
    show ¬(33 + k - 15 - 7 - 1 - 6 < 4) by omega,
    show 33 + k - 15 - 7 - 1 - 6 - 4 < 2 by omega, ↓reduceIte,
    List.getElem?_take, List.getElem?_drop]
  rw [show 145 + (33 + k - 15 - 7 - 1 - 6 - 4) = 145 + k by omega]

theorem m3FullSpecSuffix_getElem?_35 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecSuffix ext mainSpec)[35]? =
      some ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩ := by
  unfold m3FullSpecSuffix
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_singleton, fullSpecTable_len, kittenSpecTable_len, m3SufCong6_len,
    m3SufSweep4_len, show min 7 (166 - 128) = 7 from rfl, show min 2 (166 - 145) = 2 from rfl,
    show ¬(35 < 15) by omega, show ¬(35 - 15 < 7) by omega, show ¬(35 - 15 - 7 < 1) by omega,
    show ¬(35 - 15 - 7 - 1 < 6) by omega, show ¬(35 - 15 - 7 - 1 - 6 < 4) by omega,
    show ¬(35 - 15 - 7 - 1 - 6 - 4 < 2) by omega,
    show 35 - 15 - 7 - 1 - 6 - 4 - 2 < 1 by omega, ↓reduceIte]
  rfl

theorem m3FullSpecSuffix_getElem?_36 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecSuffix ext mainSpec)[36]? = (fullSpecTable mainSpec)[148]? := by
  unfold m3FullSpecSuffix
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_singleton, fullSpecTable_len, kittenSpecTable_len, m3SufCong6_len,
    m3SufSweep4_len, show min 7 (166 - 128) = 7 from rfl, show min 2 (166 - 145) = 2 from rfl,
    show min 1 (166 - 148) = 1 from rfl, show ¬(36 < 15) by omega,
    show ¬(36 - 15 < 7) by omega, show ¬(36 - 15 - 7 < 1) by omega,
    show ¬(36 - 15 - 7 - 1 < 6) by omega, show ¬(36 - 15 - 7 - 1 - 6 < 4) by omega,
    show ¬(36 - 15 - 7 - 1 - 6 - 4 < 2) by omega,
    show ¬(36 - 15 - 7 - 1 - 6 - 4 - 2 < 1) by omega,
    show 36 - 15 - 7 - 1 - 6 - 4 - 2 - 1 < 1 by omega, ↓reduceIte,
    List.getElem?_take, List.getElem?_drop]

theorem m3FullSpecSuffix_getElem?_37_40 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {k : Nat} (hk : k < 3) :
    (m3FullSpecSuffix ext mainSpec)[37 + k]? = (m3SufDef3 ext)[k]? := by
  unfold m3FullSpecSuffix
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_singleton, fullSpecTable_len, kittenSpecTable_len, m3SufCong6_len,
    m3SufSweep4_len, m3SufDef3_len, show min 7 (166 - 128) = 7 from rfl,
    show min 2 (166 - 145) = 2 from rfl, show min 1 (166 - 148) = 1 from rfl,
    show ¬(37 + k < 15) by omega, show ¬(37 + k - 15 < 7) by omega,
    show ¬(37 + k - 15 - 7 < 1) by omega, show ¬(37 + k - 15 - 7 - 1 < 6) by omega,
    show ¬(37 + k - 15 - 7 - 1 - 6 < 4) by omega,
    show ¬(37 + k - 15 - 7 - 1 - 6 - 4 < 2) by omega,
    show ¬(37 + k - 15 - 7 - 1 - 6 - 4 - 2 < 1) by omega,
    show ¬(37 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 < 1) by omega,
    show 37 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 < 3 by omega, ↓reduceIte]
  rw [show 37 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 = k by omega]

theorem m3FullSpecSuffix_getElem?_40 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecSuffix ext mainSpec)[40]? = (fullSpecTable mainSpec)[151]? := by
  unfold m3FullSpecSuffix
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_singleton, fullSpecTable_len, kittenSpecTable_len, m3SufCong6_len,
    m3SufSweep4_len, m3SufDef3_len, show min 7 (166 - 128) = 7 from rfl,
    show min 2 (166 - 145) = 2 from rfl, show min 1 (166 - 148) = 1 from rfl,
    show min 1 (166 - 151) = 1 from rfl, show ¬(40 < 15) by omega,
    show ¬(40 - 15 < 7) by omega, show ¬(40 - 15 - 7 < 1) by omega,
    show ¬(40 - 15 - 7 - 1 < 6) by omega, show ¬(40 - 15 - 7 - 1 - 6 < 4) by omega,
    show ¬(40 - 15 - 7 - 1 - 6 - 4 < 2) by omega, show ¬(40 - 15 - 7 - 1 - 6 - 4 - 2 < 1) by omega,
    show ¬(40 - 15 - 7 - 1 - 6 - 4 - 2 - 1 < 1) by omega,
    show ¬(40 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 < 3) by omega,
    show 40 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 < 1 by omega,
    ↓reduceIte, List.getElem?_take, List.getElem?_drop]

theorem m3FullSpecSuffix_getElem?_41 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecSuffix ext mainSpec)[41]? =
      some ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool], fullBveWeakenTmkSpec, true⟩ := by
  unfold m3FullSpecSuffix
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_singleton, fullSpecTable_len, kittenSpecTable_len, m3SufCong6_len,
    m3SufSweep4_len, m3SufDef3_len, show min 7 (166 - 128) = 7 from rfl,
    show min 2 (166 - 145) = 2 from rfl, show min 1 (166 - 148) = 1 from rfl,
    show min 1 (166 - 151) = 1 from rfl, show ¬(41 < 15) by omega,
    show ¬(41 - 15 < 7) by omega, show ¬(41 - 15 - 7 < 1) by omega,
    show ¬(41 - 15 - 7 - 1 < 6) by omega, show ¬(41 - 15 - 7 - 1 - 6 < 4) by omega,
    show ¬(41 - 15 - 7 - 1 - 6 - 4 < 2) by omega, show ¬(41 - 15 - 7 - 1 - 6 - 4 - 2 < 1) by omega,
    show ¬(41 - 15 - 7 - 1 - 6 - 4 - 2 - 1 < 1) by omega,
    show ¬(41 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 < 3) by omega,
    show ¬(41 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 < 1) by omega,
    show 41 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 < 1 by omega, ↓reduceIte]
  rfl

theorem m3FullSpecSuffix_getElem?_42 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecSuffix ext mainSpec)[42]? = (fullSpecTable mainSpec)[153]? := by
  unfold m3FullSpecSuffix
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_singleton, fullSpecTable_len, kittenSpecTable_len, m3SufCong6_len,
    m3SufSweep4_len, m3SufDef3_len, show min 7 (166 - 128) = 7 from rfl,
    show min 2 (166 - 145) = 2 from rfl, show min 1 (166 - 148) = 1 from rfl,
    show min 1 (166 - 151) = 1 from rfl, show min 1 (166 - 153) = 1 from rfl,
    show ¬(42 < 15) by omega, show ¬(42 - 15 < 7) by omega, show ¬(42 - 15 - 7 < 1) by omega,
    show ¬(42 - 15 - 7 - 1 < 6) by omega, show ¬(42 - 15 - 7 - 1 - 6 < 4) by omega,
    show ¬(42 - 15 - 7 - 1 - 6 - 4 < 2) by omega, show ¬(42 - 15 - 7 - 1 - 6 - 4 - 2 < 1) by omega,
    show ¬(42 - 15 - 7 - 1 - 6 - 4 - 2 - 1 < 1) by omega,
    show ¬(42 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 < 3) by omega,
    show ¬(42 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 < 1) by omega,
    show ¬(42 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 < 1) by omega,
    show 42 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 < 1 by omega,
    ↓reduceIte, List.getElem?_take, List.getElem?_drop]

theorem m3FullSpecSuffix_getElem?_43 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecSuffix ext mainSpec)[43]? =
      some ⟨"full_bve_commit_res", [i64, i64, i64], [i64], fullBveCommitResTmkSpec, true⟩ := by
  unfold m3FullSpecSuffix
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_singleton, fullSpecTable_len, kittenSpecTable_len, m3SufCong6_len,
    m3SufSweep4_len, m3SufDef3_len, show min 7 (166 - 128) = 7 from rfl,
    show min 2 (166 - 145) = 2 from rfl, show min 1 (166 - 148) = 1 from rfl,
    show min 1 (166 - 151) = 1 from rfl, show min 1 (166 - 153) = 1 from rfl,
    show ¬(43 < 15) by omega, show ¬(43 - 15 < 7) by omega, show ¬(43 - 15 - 7 < 1) by omega,
    show ¬(43 - 15 - 7 - 1 < 6) by omega, show ¬(43 - 15 - 7 - 1 - 6 < 4) by omega,
    show ¬(43 - 15 - 7 - 1 - 6 - 4 < 2) by omega, show ¬(43 - 15 - 7 - 1 - 6 - 4 - 2 < 1) by omega,
    show ¬(43 - 15 - 7 - 1 - 6 - 4 - 2 - 1 < 1) by omega,
    show ¬(43 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 < 3) by omega,
    show ¬(43 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 < 1) by omega,
    show ¬(43 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 < 1) by omega,
    show ¬(43 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 < 1) by omega,
    show 43 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 < 1 by omega, ↓reduceIte]
  rfl

theorem m3FullSpecSuffix_getElem?_44 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecSuffix ext mainSpec)[44]? = (fullSpecTable mainSpec)[155]? := by
  unfold m3FullSpecSuffix
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_singleton, fullSpecTable_len, kittenSpecTable_len, m3SufCong6_len,
    m3SufSweep4_len, m3SufDef3_len, show min 7 (166 - 128) = 7 from rfl,
    show min 2 (166 - 145) = 2 from rfl, show min 1 (166 - 148) = 1 from rfl,
    show min 1 (166 - 151) = 1 from rfl, show min 1 (166 - 153) = 1 from rfl,
    show min 1 (166 - 155) = 1 from rfl, show ¬(44 < 15) by omega,
    show ¬(44 - 15 < 7) by omega, show ¬(44 - 15 - 7 < 1) by omega,
    show ¬(44 - 15 - 7 - 1 < 6) by omega, show ¬(44 - 15 - 7 - 1 - 6 < 4) by omega,
    show ¬(44 - 15 - 7 - 1 - 6 - 4 < 2) by omega, show ¬(44 - 15 - 7 - 1 - 6 - 4 - 2 < 1) by omega,
    show ¬(44 - 15 - 7 - 1 - 6 - 4 - 2 - 1 < 1) by omega,
    show ¬(44 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 < 3) by omega,
    show ¬(44 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 < 1) by omega,
    show ¬(44 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 < 1) by omega,
    show ¬(44 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 < 1) by omega,
    show ¬(44 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 < 1) by omega,
    show 44 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 - 1 < 1 by omega,
    ↓reduceIte, List.getElem?_take, List.getElem?_drop]

theorem m3FullSpecSuffix_getElem?_45 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecSuffix ext mainSpec)[45]? =
      some ⟨"full_bve_var", [i64, i32], [i64], fullBveVarDefSpec, true⟩ := by
  unfold m3FullSpecSuffix
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_singleton, fullSpecTable_len, kittenSpecTable_len, m3SufCong6_len,
    m3SufSweep4_len, m3SufDef3_len, show min 7 (166 - 128) = 7 from rfl,
    show min 2 (166 - 145) = 2 from rfl, show min 1 (166 - 148) = 1 from rfl,
    show min 1 (166 - 151) = 1 from rfl, show min 1 (166 - 153) = 1 from rfl,
    show min 1 (166 - 155) = 1 from rfl, show ¬(45 < 15) by omega,
    show ¬(45 - 15 < 7) by omega, show ¬(45 - 15 - 7 < 1) by omega,
    show ¬(45 - 15 - 7 - 1 < 6) by omega, show ¬(45 - 15 - 7 - 1 - 6 < 4) by omega,
    show ¬(45 - 15 - 7 - 1 - 6 - 4 < 2) by omega, show ¬(45 - 15 - 7 - 1 - 6 - 4 - 2 < 1) by omega,
    show ¬(45 - 15 - 7 - 1 - 6 - 4 - 2 - 1 < 1) by omega,
    show ¬(45 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 < 3) by omega,
    show ¬(45 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 < 1) by omega,
    show ¬(45 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 < 1) by omega,
    show ¬(45 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 < 1) by omega,
    show ¬(45 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 < 1) by omega,
    show ¬(45 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 - 1 < 1) by omega,
    show 45 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 - 1 - 1 < 1 by omega, ↓reduceIte]
  rfl

theorem m3FullSpecSuffix_getElem?_46_59 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {k : Nat} (hk : k < 13) :
    (m3FullSpecSuffix ext mainSpec)[46 + k]? = (m3SufBvaHeap ext)[k]? := by
  unfold m3FullSpecSuffix
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_singleton, fullSpecTable_len, kittenSpecTable_len, m3SufCong6_len,
    m3SufSweep4_len, m3SufDef3_len, m3SufBvaHeap_len, show min 7 (166 - 128) = 7 from rfl,
    show min 2 (166 - 145) = 2 from rfl, show min 1 (166 - 148) = 1 from rfl,
    show min 1 (166 - 151) = 1 from rfl, show min 1 (166 - 153) = 1 from rfl,
    show min 1 (166 - 155) = 1 from rfl, show ¬(46 + k < 15) by omega,
    show ¬(46 + k - 15 < 7) by omega, show ¬(46 + k - 15 - 7 < 1) by omega,
    show ¬(46 + k - 15 - 7 - 1 < 6) by omega, show ¬(46 + k - 15 - 7 - 1 - 6 < 4) by omega,
    show ¬(46 + k - 15 - 7 - 1 - 6 - 4 < 2) by omega,
    show ¬(46 + k - 15 - 7 - 1 - 6 - 4 - 2 < 1) by omega,
    show ¬(46 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 < 1) by omega,
    show ¬(46 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 < 3) by omega,
    show ¬(46 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 < 1) by omega,
    show ¬(46 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 < 1) by omega,
    show ¬(46 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 < 1) by omega,
    show ¬(46 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 < 1) by omega,
    show ¬(46 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 - 1 < 1) by omega,
    show ¬(46 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 - 1 - 1 < 1) by omega,
    show 46 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 - 1 - 1 - 1 < 13 by omega,
    ↓reduceIte]
  rw [show 46 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 - 1 - 1 - 1 = k by omega]

theorem m3FullSpecSuffix_getElem?_59_72 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {k : Nat} (hk : k < 13) :
    (m3FullSpecSuffix ext mainSpec)[59 + k]? = m3SufTail[k]? := by
  unfold m3FullSpecSuffix
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_singleton, fullSpecTable_len, kittenSpecTable_len, m3SufCong6_len,
    m3SufSweep4_len, m3SufDef3_len, m3SufBvaHeap_len, m3SufTail_len,
    show min 7 (166 - 128) = 7 from rfl, show min 2 (166 - 145) = 2 from rfl,
    show min 1 (166 - 148) = 1 from rfl, show min 1 (166 - 151) = 1 from rfl,
    show min 1 (166 - 153) = 1 from rfl, show min 1 (166 - 155) = 1 from rfl,
    show ¬(59 + k < 15) by omega, show ¬(59 + k - 15 < 7) by omega,
    show ¬(59 + k - 15 - 7 < 1) by omega, show ¬(59 + k - 15 - 7 - 1 < 6) by omega,
    show ¬(59 + k - 15 - 7 - 1 - 6 < 4) by omega,
    show ¬(59 + k - 15 - 7 - 1 - 6 - 4 < 2) by omega,
    show ¬(59 + k - 15 - 7 - 1 - 6 - 4 - 2 < 1) by omega,
    show ¬(59 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 < 1) by omega,
    show ¬(59 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 < 3) by omega,
    show ¬(59 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 < 1) by omega,
    show ¬(59 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 < 1) by omega,
    show ¬(59 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 < 1) by omega,
    show ¬(59 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 < 1) by omega,
    show ¬(59 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 - 1 < 1) by omega,
    show ¬(59 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 - 1 - 1 < 1) by omega,
    show ¬(59 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 - 1 - 1 - 1 < 13) by omega,
    show 59 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 - 1 - 1 - 1 - 13 < 13 by omega,
    ↓reduceIte]
  rw [show 59 + k - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 - 1 - 1 - 1 - 13 = k by omega]

theorem m3FullSpecSuffix_getElem?_72 (ext : M2bInternalSpecs)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (m3FullSpecSuffix ext mainSpec)[72]? =
      some ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩ := by
  unfold m3FullSpecSuffix
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_singleton, fullSpecTable_len, kittenSpecTable_len, m3SufCong6_len,
    m3SufSweep4_len, m3SufDef3_len, m3SufBvaHeap_len, m3SufTail_len,
    show min 7 (166 - 128) = 7 from rfl, show min 2 (166 - 145) = 2 from rfl,
    show min 1 (166 - 148) = 1 from rfl, show min 1 (166 - 151) = 1 from rfl,
    show min 1 (166 - 153) = 1 from rfl, show min 1 (166 - 155) = 1 from rfl,
    show ¬(72 < 15) by omega, show ¬(72 - 15 < 7) by omega,
    show ¬(72 - 15 - 7 < 1) by omega, show ¬(72 - 15 - 7 - 1 < 6) by omega,
    show ¬(72 - 15 - 7 - 1 - 6 < 4) by omega, show ¬(72 - 15 - 7 - 1 - 6 - 4 < 2) by omega,
    show ¬(72 - 15 - 7 - 1 - 6 - 4 - 2 < 1) by omega,
    show ¬(72 - 15 - 7 - 1 - 6 - 4 - 2 - 1 < 1) by omega,
    show ¬(72 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 < 3) by omega,
    show ¬(72 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 < 1) by omega,
    show ¬(72 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 < 1) by omega,
    show ¬(72 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 < 1) by omega,
    show ¬(72 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 < 1) by omega,
    show ¬(72 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 - 1 < 1) by omega,
    show ¬(72 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 - 1 - 1 < 1) by omega,
    show ¬(72 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 - 1 - 1 - 1 < 13) by omega,
    show ¬(72 - 15 - 7 - 1 - 6 - 4 - 2 - 1 - 1 - 3 - 1 - 1 - 1 - 1 - 1 - 1 - 13 < 13) by omega,
    ↓reduceIte, List.getElem?_drop]
  rfl

end LeanQbe.T.Examples.Kissat.FullM3CongBva
