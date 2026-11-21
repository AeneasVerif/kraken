module

public import LeanQbe.T.Examples.Kissat.FullM3Proof1

/-!
# Kissat `D-Full` Unified M3 `ModuleOk` Assembly (`FullM3Proof`, `204/204` Closed)

Assembles unconditional `204`-row `TableImpl` & `ModuleOk` for `FullM3.m3Module`
(`externs := []`, `exits := []`):
- `mkM3Env_tableImpl : TableImpl (mkM3Env mainSpec) m3Fns (m3SpecTable mainSpec)` (`204/204`)
- `mkM3Env_moduleOk : ModuleOk (mkM3Env mainSpec) m3Module`
- `m3Env_moduleOk : ModuleOk m3Env m3Module`
- `m3UnsatEnv_moduleOk : ModuleOk m3UnsatEnv m3Module`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM3

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFast
open Kraken.Bedrock2.Test

private theorem allFns_of_forall {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h =>
    ⟨h _ List.mem_cons_self, allFns_of_forall fun f hf => h f (List.mem_cons_of_mem _ hf)⟩

private theorem m3_tableImpl_step {Γ : Env} {fs : List Fn} {tbl : List SpecEntry}
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

private theorem m3_tableImpl_nil (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    TableImpl (mkM3Env mainSpec) (m3Fns.drop 204) ((m3SpecTable mainSpec).drop 204) := by
  rw [List.drop_of_length_le (by rw [m3Fns_length]; omega),
    List.drop_of_length_le (by rw [m3SpecTable_length]; omega)]
  trivial

/-! ## Fast `O(1)` `m3Fns[i]?` Lookup Lemmas -/

private theorem fullFns_len' : Full.fullFns.length = 166 := by t_kernel_rfl
private theorem fastCore_len' : FastCore.fastCore_fns.length = 3 := by t_kernel_rfl
private theorem bveBudgets_len' : FullFastBveBudgets.fastBveBudgets_fns.length = 7 := by
  t_kernel_rfl
private theorem sched_len' : FullFastSched.sched_fns.length = 15 := by t_kernel_rfl
private theorem kitten_len' : Full.fullKitten_fns.length = 15 := by t_kernel_rfl
private theorem defSweep_len' : FullDefSweep.full_def_sweep_fns.length = 9 := by t_kernel_rfl
private theorem bvaHeap_len' : FullBvaHeap.bvaHeap_fns.length = 13 := by t_kernel_rfl

private theorem drop_append_l {α : Type _} {xs ys : List α} {n : Nat} (h : xs.length = n) :
    (xs ++ ys).drop n = ys := by subst h; simp

private def m3Seg0_51 : List Fn :=
  Full.fullFns.take 25 ++ [FullM3VivChrono.m3TickRelFn] ++
  (Full.fullFns.drop 26).take 10 ++ FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
  (Full.fullFns.drop 37).take 10 ++ [m3PropLitRawFn, FullM3VivChrono.m3PropLitFn] ++
  FastCore.fastCore_fns.drop 1

private def m3Seg51_112 : List Fn :=
  (Full.fullFns.drop 50).take 7 ++ FullFastSched.sched_fns.take 1 ++
  (Full.fullFns.drop 58).take 5 ++ [FullM3VivChrono.m3AnalyzeRsnFn] ++
  (Full.fullFns.drop 64).take 47

private def m3Seg112_129 : List Fn :=
  [m3ProbeRunFn] ++ (Full.fullFns.drop 112).take 1 ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
  (Full.fullFns.drop 114).take 5 ++ [FullM3VivChrono.m3VivifyFn] ++
  (Full.fullFns.drop 120).take 1 ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
  (Full.fullFns.drop 122).take 3 ++ (FullFastSched.sched_fns.drop 1).take 2 ++
  (Full.fullFns.drop 127).take 1

private def m3Seg144_162 : List Fn :=
  (Full.fullFns.drop 128).take 7 ++ (FullDefSweep.full_def_sweep_fns.drop 3).take 1 ++
  [ FullM3CongBva.m3MarkTrailFn, FullM3CongBva.m3UnitFoldFn, FullM3CongBva.m3EquivFoldFn
  , FullM3CongBva.m3AndMatchFn, FullM3CongBva.m3CongWorkStepFn
  , FullM3CongBva.m3CongruenceDenseFn ] ++
  FullDefSweep.full_def_sweep_fns.drop 5

private def m3Seg162_188 : List Fn :=
  (Full.fullFns.drop 145).take 2 ++
  (FullFastBveBudgets.fastBveBudgets_fns.drop 5).take 1 ++
  (Full.fullFns.drop 148).take 1 ++ FullDefSweep.full_def_sweep_fns.take 3 ++
  (Full.fullFns.drop 151).take 5 ++ FullFastBveBudgets.fastBveBudgets_fns.drop 6 ++
  FullBvaHeap.bvaHeap_fns

private def m3Seg188_204 : List Fn :=
  (FullFastSched.sched_fns.drop 3).take 4 ++
  [m3BackboneLitFn, m3BackboneFn, m3ProbeTailFn, m3ProbeFn] ++
  (FullFastSched.sched_fns.drop 9).take 1 ++
  [ FullM3CongBva.m3ElimCollectNbrsFn, FullM3CongBva.m3ElimBveFn
  , FullM3CongBva.m3EliminateFn, FullM3CongBva.m3PreprocessFn ] ++
  FullFastSched.sched_fns.drop 13 ++ Full.fullFns.drop 165

private theorem m3Seg0_51_len : m3Seg0_51.length = 51 := by
  simp [m3Seg0_51, fullFns_len', bveBudgets_len', fastCore_len']

private theorem m3Seg51_112_len : m3Seg51_112.length = 61 := by
  simp [m3Seg51_112, fullFns_len', sched_len']

private theorem m3Seg112_129_len : m3Seg112_129.length = 17 := by
  simp [m3Seg112_129, fullFns_len', bveBudgets_len', sched_len']

private theorem m3Seg144_162_len : m3Seg144_162.length = 18 := by
  simp [m3Seg144_162, fullFns_len', defSweep_len']

private theorem m3Seg162_188_len : m3Seg162_188.length = 26 := by
  simp [m3Seg162_188, fullFns_len', bveBudgets_len', defSweep_len', bvaHeap_len']

private theorem m3FnsPrefix_segs : m3FnsPrefix = m3Seg0_51 ++ (m3Seg51_112 ++ m3Seg112_129) := by
  simp only [m3FnsPrefix, m3Seg0_51, m3Seg51_112, m3Seg112_129, List.append_assoc]

private theorem m3FnsSuffix_segs :
    m3FnsSuffix = Full.fullKitten_fns ++ (m3Seg144_162 ++ (m3Seg162_188 ++ m3Seg188_204)) := by
  simp only [m3FnsSuffix, m3Seg144_162, m3Seg162_188, m3Seg188_204, List.append_assoc]

private theorem m3Fns_segs :
    m3Fns = m3Seg0_51 ++ (m3Seg51_112 ++ (m3Seg112_129 ++ m3FnsSuffix)) := by
  rw [m3Fns, m3FnsPrefix_segs]; simp only [List.append_assoc]

private theorem m3Fns_drop_51_eq :
    m3Fns.drop 51 = m3Seg51_112 ++ (m3Seg112_129 ++ m3FnsSuffix) := by
  rw [m3Fns_segs, drop_append_l m3Seg0_51_len]

private theorem m3Fns_drop_112_eq : m3Fns.drop 112 = m3Seg112_129 ++ m3FnsSuffix := by
  rw [show (112 : Nat) = 51 + 61 from rfl, ← List.drop_drop, m3Fns_drop_51_eq,
    drop_append_l m3Seg51_112_len]

private theorem m3Fns_drop_129_eq :
    m3Fns.drop 129 = Full.fullKitten_fns ++ (m3Seg144_162 ++ (m3Seg162_188 ++ m3Seg188_204)) := by
  rw [m3Fns, drop_append_l m3FnsPrefix_length, m3FnsSuffix_segs]

private theorem m3Fns_drop_144_eq :
    m3Fns.drop 144 = m3Seg144_162 ++ (m3Seg162_188 ++ m3Seg188_204) := by
  rw [show (144 : Nat) = 129 + 15 from rfl, ← List.drop_drop, m3Fns_drop_129_eq,
    drop_append_l kitten_len']

private theorem m3Fns_drop_162_eq : m3Fns.drop 162 = m3Seg162_188 ++ m3Seg188_204 := by
  rw [show (162 : Nat) = 144 + 18 from rfl, ← List.drop_drop, m3Fns_drop_144_eq,
    drop_append_l m3Seg144_162_len]

private theorem m3Fns_drop_188_eq : m3Fns.drop 188 = m3Seg188_204 := by
  rw [show (188 : Nat) = 162 + 26 from rfl, ← List.drop_drop, m3Fns_drop_162_eq,
    drop_append_l m3Seg162_188_len]

private theorem m3_0_25 {i : Nat} {fn : Fn} (hi : i < 25 := by omega)
    (h : Full.fullFns[i]? = some fn := by rfl) : m3Fns[i]? = some fn := by
  have hd := congrArg (·[i]?) m3Fns_segs
  rw [hd, List.getElem?_append_left (by rw [m3Seg0_51_len]; omega)]
  unfold m3Seg0_51
  simp only [List.append_assoc]
  rw [List.getElem?_append_left (by simp [fullFns_len']; omega), List.getElem?_take_of_lt hi]
  exact h

private theorem m3_25 : m3Fns[25]? = some FullM3VivChrono.m3TickRelFn := by
  have hd := congrArg (·[25]?) m3Fns_segs
  rw [hd, List.getElem?_append_left (by rw [m3Seg0_51_len]; omega)]
  simp [m3Seg0_51, List.length_take, fullFns_len']

private theorem m3_26_36 {i : Nat} {fn : Fn} (h1 : 26 ≤ i := by omega) (h2 : i < 36 := by omega)
    (h : Full.fullFns[i]? = some fn := by rfl) : m3Fns[i]? = some fn := by
  have hd := congrArg (·[i]?) m3Fns_segs
  rw [hd, List.getElem?_append_left (by rw [m3Seg0_51_len]; omega)]
  unfold m3Seg0_51
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_cons, List.length_nil, fullFns_len', show min 25 166 = 25 from rfl,
    show min 10 (166 - 26) = 10 from rfl, show ¬(i < 25) by omega, show ¬(i - 25 < 1) by omega,
    show i - 25 - 1 < 10 by omega, ↓reduceIte, List.getElem?_take, List.getElem?_drop]
  rw [show 26 + (i - 25 - 1) = i by omega]; exact h

private theorem m3_36 {fn : Fn}
    (h : FullFastBveBudgets.fastBveBudgets_fns[0]? = some fn := by rfl) :
    m3Fns[36]? = some fn := by
  have hd := congrArg (·[36]?) m3Fns_segs
  rw [hd, List.getElem?_append_left (by rw [m3Seg0_51_len]; omega)]
  unfold m3Seg0_51
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_cons, List.length_nil, fullFns_len', bveBudgets_len',
    show min 25 166 = 25 from rfl, show min 10 (166 - 26) = 10 from rfl,
    show min 1 7 = 1 from rfl, show ¬(36 < 25) by omega, show ¬(36 - 25 < 1) by omega,
    show ¬(36 - 25 - 1 < 10) by omega, show 36 - 25 - 1 - 10 < 1 by omega, ↓reduceIte,
    List.getElem?_take]
  exact h

private theorem m3_37_47 {i : Nat} {fn : Fn} (h1 : 37 ≤ i := by omega) (h2 : i < 47 := by omega)
    (h : Full.fullFns[i]? = some fn := by rfl) : m3Fns[i]? = some fn := by
  have hd := congrArg (·[i]?) m3Fns_segs
  rw [hd, List.getElem?_append_left (by rw [m3Seg0_51_len]; omega)]
  unfold m3Seg0_51
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_cons, List.length_nil, fullFns_len', bveBudgets_len',
    show min 25 166 = 25 from rfl, show min 10 (166 - 26) = 10 from rfl,
    show min 1 7 = 1 from rfl, show min 10 (166 - 37) = 10 from rfl,
    show ¬(i < 25) by omega, show ¬(i - 25 < 1) by omega, show ¬(i - 25 - 1 < 10) by omega,
    show ¬(i - 25 - 1 - 10 < 1) by omega, show i - 25 - 1 - 10 - 1 < 10 by omega, ↓reduceIte,
    List.getElem?_take, List.getElem?_drop]
  rw [show 37 + (i - 25 - 1 - 10 - 1) = i by omega]; exact h

private theorem m3_47_51 {i : Nat} {fn : Fn} (h1 : 47 ≤ i := by omega) (h2 : i < 51 := by omega)
    (h : ([m3PropLitRawFn, FullM3VivChrono.m3PropLitFn] ++ FastCore.fastCore_fns.drop 1)[i - 47]? =
      some fn := by rfl) :
    m3Fns[i]? = some fn := by
  have h47 : (Full.fullFns.take 25 ++ [FullM3VivChrono.m3TickRelFn] ++
      (Full.fullFns.drop 26).take 10 ++ FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
      (Full.fullFns.drop 37).take 10).length = 47 := by
    simp [fullFns_len', bveBudgets_len']
  have hs : m3Seg0_51 =
      (Full.fullFns.take 25 ++ [FullM3VivChrono.m3TickRelFn] ++
       (Full.fullFns.drop 26).take 10 ++ FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
       (Full.fullFns.drop 37).take 10) ++
      ([m3PropLitRawFn, FullM3VivChrono.m3PropLitFn] ++ FastCore.fastCore_fns.drop 1) := by
    simp only [m3Seg0_51, List.append_assoc]
  have hd := congrArg (·[i]?) m3Fns_segs
  rw [hd, List.getElem?_append_left (by rw [m3Seg0_51_len]; omega), hs,
    List.getElem?_append_right (by rw [h47]; omega), h47]
  exact h

private theorem m3_51_58 {i : Nat} {fn : Fn} (h1 : 51 ≤ i := by omega) (h2 : i < 58 := by omega)
    (h : Full.fullFns[i - 1]? = some fn := by rfl) : m3Fns[i]? = some fn := by
  have hd := congrArg (·[i - 51]?) m3Fns_drop_51_eq
  simp only [List.getElem?_drop, show 51 + (i - 51) = i by omega] at hd
  rw [hd, List.getElem?_append_left (by rw [m3Seg51_112_len]; omega)]
  unfold m3Seg51_112
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_len', show min 7 (166 - 50) = 7 from rfl, show i - 51 < 7 by omega, ↓reduceIte,
    List.getElem?_take, List.getElem?_drop]
  rw [show 50 + (i - 51) = i - 1 by omega]; exact h

private theorem m3_58 {fn : Fn} (h : FullFastSched.sched_fns[0]? = some fn := by rfl) :
    m3Fns[58]? = some fn := by
  have hd := congrArg (·[7]?) m3Fns_drop_51_eq
  simp only [List.getElem?_drop] at hd
  rw [hd, List.getElem?_append_left (by rw [m3Seg51_112_len]; omega)]
  unfold m3Seg51_112
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_len', sched_len', show min 7 (166 - 50) = 7 from rfl, show min 1 15 = 1 from rfl,
    show ¬(7 < 7) by omega, show 7 - 7 < 1 by omega, ↓reduceIte, List.getElem?_take]
  exact h

private theorem m3_59_64 {i : Nat} {fn : Fn} (h1 : 59 ≤ i := by omega) (h2 : i < 64 := by omega)
    (h : Full.fullFns[i - 1]? = some fn := by rfl) : m3Fns[i]? = some fn := by
  have hd := congrArg (·[i - 51]?) m3Fns_drop_51_eq
  simp only [List.getElem?_drop, show 51 + (i - 51) = i by omega] at hd
  rw [hd, List.getElem?_append_left (by rw [m3Seg51_112_len]; omega)]
  unfold m3Seg51_112
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    fullFns_len', sched_len', show min 7 (166 - 50) = 7 from rfl, show min 1 15 = 1 from rfl,
    show min 5 (166 - 58) = 5 from rfl, show ¬(i - 51 < 7) by omega,
    show ¬(i - 51 - 7 < 1) by omega, show i - 51 - 7 - 1 < 5 by omega, ↓reduceIte,
    List.getElem?_take, List.getElem?_drop]
  rw [show 58 + (i - 51 - 7 - 1) = i - 1 by omega]; exact h

private theorem m3_64 : m3Fns[64]? = some FullM3VivChrono.m3AnalyzeRsnFn := by
  have hd := congrArg (·[13]?) m3Fns_drop_51_eq
  simp only [List.getElem?_drop] at hd
  rw [hd, List.getElem?_append_left (by rw [m3Seg51_112_len]; omega)]
  simp [m3Seg51_112, List.length_take, List.length_drop, fullFns_len', sched_len']

private theorem m3_65_112 {i : Nat} {fn : Fn} (h1 : 65 ≤ i := by omega) (h2 : i < 112 := by omega)
    (h : Full.fullFns[i - 1]? = some fn := by rfl) : m3Fns[i]? = some fn := by
  have hd := congrArg (·[i - 51]?) m3Fns_drop_51_eq
  simp only [List.getElem?_drop, show 51 + (i - 51) = i by omega] at hd
  rw [hd, List.getElem?_append_left (by rw [m3Seg51_112_len]; omega)]
  unfold m3Seg51_112
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_cons, List.length_nil, fullFns_len', sched_len',
    show min 7 (166 - 50) = 7 from rfl, show min 1 15 = 1 from rfl,
    show min 5 (166 - 58) = 5 from rfl, show ¬(i - 51 < 7) by omega,
    show ¬(i - 51 - 7 < 1) by omega, show ¬(i - 51 - 7 - 1 < 5) by omega,
    show ¬(i - 51 - 7 - 1 - 5 < 1) by omega, show i - 51 - 7 - 1 - 5 - 1 < 47 by omega,
    ↓reduceIte, List.getElem?_take, List.getElem?_drop]
  rw [show 64 + (i - 51 - 7 - 1 - 5 - 1) = i - 1 by omega]; exact h

private theorem m3_112_129 {i : Nat} {fn : Fn} (h1 : 112 ≤ i := by omega)
    (h2 : i < 129 := by omega) (h : m3Seg112_129[i - 112]? = some fn := by rfl) :
    m3Fns[i]? = some fn := by
  have hd := congrArg (·[i - 112]?) m3Fns_drop_112_eq
  simp only [List.getElem?_drop, show 112 + (i - 112) = i by omega] at hd
  rw [hd, List.getElem?_append_left (by rw [m3Seg112_129_len]; omega)]; exact h

private theorem m3_129_144 {i : Nat} {fn : Fn} (h1 : 129 ≤ i := by omega)
    (h2 : i < 144 := by omega) (h : Full.fullKitten_fns[i - 129]? = some fn := by rfl) :
    m3Fns[i]? = some fn := by
  have hd := congrArg (·[i - 129]?) m3Fns_drop_129_eq
  simp only [List.getElem?_drop, show 129 + (i - 129) = i by omega] at hd
  rw [hd, List.getElem?_append_left (by rw [kitten_len']; omega)]; exact h

private theorem m3_144_162 {i : Nat} {fn : Fn} (h1 : 144 ≤ i := by omega)
    (h2 : i < 162 := by omega) (h : m3Seg144_162[i - 144]? = some fn := by rfl) :
    m3Fns[i]? = some fn := by
  have hd := congrArg (·[i - 144]?) m3Fns_drop_144_eq
  simp only [List.getElem?_drop, show 144 + (i - 144) = i by omega] at hd
  rw [hd, List.getElem?_append_left (by rw [m3Seg144_162_len]; omega)]; exact h

private theorem m3_162_188 {i : Nat} {fn : Fn} (h1 : 162 ≤ i := by omega)
    (h2 : i < 188 := by omega) (h : m3Seg162_188[i - 162]? = some fn := by rfl) :
    m3Fns[i]? = some fn := by
  have hd := congrArg (·[i - 162]?) m3Fns_drop_162_eq
  simp only [List.getElem?_drop, show 162 + (i - 162) = i by omega] at hd
  rw [hd, List.getElem?_append_left (by rw [m3Seg162_188_len]; omega)]; exact h

private theorem m3_188_204 {i : Nat} {fn : Fn} (h1 : 188 ≤ i := by omega)
    (h2 : i < 204 := by omega) (h : m3Seg188_204[i - 188]? = some fn := by rfl) :
    m3Fns[i]? = some fn := by
  have hd := congrArg (·[i - 188]?) m3Fns_drop_188_eq
  simp only [List.getElem?_drop, show 188 + (i - 188) = i by omega] at hd
  rw [hd]; exact h

/-! ## Unconditional `204`-Row `TableImpl` & `ModuleOk` Assembly (`204/204`) -/

private theorem m3_table_drop_162
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    TableImpl (mkM3Env mainSpec) (m3Fns.drop 162) ((m3SpecTable mainSpec).drop 162) := by
  let Γ := mkM3Env mainSpec
  let h7 := mkM3Env_row_at (mainSpec := mainSpec) 7
    ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64], kissatCheckModelExactSpec, true⟩
  let h9 := mkM3Env_row_at (mainSpec := mainSpec) 9
    ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  let h11 := mkM3Env_row_at (mainSpec := mainSpec) 11
    ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  let h12 := mkM3Env_row_at (mainSpec := mainSpec) 12
    ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], fullAllocClSpec, true⟩
  let h14 := mkM3Env_row_at (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let h15 := mkM3Env_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h30 := mkM3Env_row_at (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let h41 := mkM3Env_row_at (mainSpec := mainSpec) 41
    ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec, true⟩
  let h44 := mkM3Env_row_at (mainSpec := mainSpec) 44
    ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩
  let h50 := mkM3Env_row_at (mainSpec := mainSpec) 50
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let h57 := mkM3Env_row_at (mainSpec := mainSpec) 57
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  let h61 := mkM3Env_row_at (mainSpec := mainSpec) 61
    ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  let h62 := mkM3Env_row_at (mainSpec := mainSpec) 62
    ⟨"full_reduce", [i64, .bool], [i64], fullReduceSpec, true⟩
  let h83 := mkM3Env_row_at (mainSpec := mainSpec) 83
    ⟨"full_analyze", [i64], [i64], fullAnalyzeSpec, true⟩
  let h85 := mkM3Env_row_at (mainSpec := mainSpec) 85
    ⟨"full_decide", [i64], [i64], fullDecideSpec, true⟩
  let h86 := mkM3Env_row_at (mainSpec := mainSpec) 86
    ⟨"full_warmup", [i64], [], fullWarmupSpec, true⟩
  let h91 := mkM3Env_row_at (mainSpec := mainSpec) 91
    ⟨"full_rephase", [i64], [], fullRephaseSpec, true⟩
  let h92 := mkM3Env_row_at (mainSpec := mainSpec) 92
    ⟨"full_switch_mode", [i64], [], fullSwitchModeSpec, true⟩
  let h93 := mkM3Env_row_at (mainSpec := mainSpec) 93
    ⟨"full_restart_due", [i64], [i64], fullRestartDueSpec, true⟩
  let h94 := mkM3Env_row_at (mainSpec := mainSpec) 94
    ⟨"full_restart", [i64], [], fullRestartSpec, true⟩
  let h95 := mkM3Env_row_at (mainSpec := mainSpec) 95
    ⟨"full_extend_push2", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩
  let h96 := mkM3Env_row_at (mainSpec := mainSpec) 96
    ⟨"full_extend_push_cl", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPushClTmkSpec, true⟩
  let h97 := mkM3Env_row_at (mainSpec := mainSpec) 97
    ⟨"full_extend", [i64], [], fullExtendSpec, true⟩
  let h99 := mkM3Env_row_at (mainSpec := mainSpec) 99
    ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  let h101 := mkM3Env_row_at (mainSpec := mainSpec) 101
    ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  let h102 := mkM3Env_row_at (mainSpec := mainSpec) 102
    ⟨"full_set_inactive", [i64, i32, i32], [], fullSetInactiveSpec, true⟩
  let h103 := mkM3Env_row_at (mainSpec := mainSpec) 103
    ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  let h106 := mkM3Env_row_at (mainSpec := mainSpec) 106
    ⟨"full_lucky", [i64], [i64], fullLuckySpec, true⟩
  let h112 := mkM3Env_row_at (mainSpec := mainSpec) 112
    ⟨"full_probe_run", [i64, i64], [i64], FullM3Backbone.fullProbeRunCursorSpec, true⟩
  let h114 := mkM3Env_row_at (mainSpec := mainSpec) 114
    ⟨"full_transitive", [i64, i64], [i64], FullFastBveBudgets.fullTransitiveFastSpec, true⟩
  let h120 := mkM3Env_row_at (mainSpec := mainSpec) 120
    ⟨"full_vivify", [i64, i64, i64], [i64], FullFastBveBudgets.fullVivifyFastSpec, true⟩
  let h126 := mkM3Env_row_at (mainSpec := mainSpec) 126
    ⟨"full_substitute", [i64], [i64], fullSubstituteSpec, true⟩
  let h127 := mkM3Env_row_at (mainSpec := mainSpec) 127
    ⟨"full_enter_dense", [i64], [.bool], FullFastSched.schedEnterDenseSpec, true⟩
  let h128 := mkM3Env_row_at (mainSpec := mainSpec) 128
    ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  let h129 := mkM3Env_row_at (mainSpec := mainSpec) 129
    ⟨"full_kitten_init", [i64, i32, i32], [], fullKittenInitSpec, true⟩
  let h131 := mkM3Env_row_at (mainSpec := mainSpec) 131
    ⟨"full_kitten_add_clause", [i64, i32, i64, i32], [.bool], fullKittenAddClauseSpec, true⟩
  let h140 := mkM3Env_row_at (mainSpec := mainSpec) 140
    ⟨"full_kitten_solve", [i64, i64], [i64], fullKittenSolveSpec, true⟩
  let h141 := mkM3Env_row_at (mainSpec := mainSpec) 141
    ⟨"full_kitten_core", [i64], [i32], fullKittenCoreSpec, true⟩
  let h142 := mkM3Env_row_at (mainSpec := mainSpec) 142
    ⟨"full_kitten_shrink", [i64], [], fullKittenShrinkSpec, true⟩
  let h157 := mkM3Env_row_at (mainSpec := mainSpec) 157
    ⟨"full_congruence_dense", [i64, i64], [i64], FullM3CongBva.m3CongruenceDenseSpec, true⟩
  let h161 := mkM3Env_row_at (mainSpec := mainSpec) 161
    ⟨"full_sweep_dense", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec, true⟩
  let h162 := mkM3Env_row_at (mainSpec := mainSpec) 162
    ⟨"full_fwd_dedup_bins", [i64], [.bool], fullFwdDedupBinsSpec, true⟩
  let h163 := mkM3Env_row_at (mainSpec := mainSpec) 163
    ⟨"full_fwd_check_cl", [i64, i32], [.bool], fullFwdCheckClSpec, true⟩
  let h164 := mkM3Env_row_at (mainSpec := mainSpec) 164
    ⟨"full_forward_sub", [i64, i64], [i64], FullFastBveBudgets.fullForwardSubFastSpec, true⟩
  let h165 := mkM3Env_row_at (mainSpec := mainSpec) 165
    ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩
  let h166 := mkM3Env_row_at (mainSpec := mainSpec) 166
    ⟨"full_bve_mark_and", [i64, i32, i32, i32, i32], [.bool],
      FullDefSweep.fullBveMarkAndDefSpec, true⟩
  let h167 := mkM3Env_row_at (mainSpec := mainSpec) 167
    ⟨"full_find_definition", [i64, i32, i32, i32], [],
      FullDefSweep.fullFindDefinitionSpec, true⟩
  let h168_def := mkM3Env_row_at (mainSpec := mainSpec) 168
    ⟨"full_bve_gates", [i64, i32, i32, i32], [], FullDefSweep.fullBveGatesDefSpec, true⟩
  let h168 := fast_bve_gates_def_adapter h168_def
  let h169 := mkM3Env_row_at (mainSpec := mainSpec) 169
    ⟨"full_bve_resolve_pair", [i64, i32, i32, i32], [.bool], fullBveResolvePairSpec, true⟩
  let h170 := mkM3Env_row_at (mainSpec := mainSpec) 170
    ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool],
      FullFastBveBudgets.fullBveWeakenTmkSpec, true⟩
  let h171 := mkM3Env_row_at (mainSpec := mainSpec) 171
    ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool], fullBveTryBceSpec, true⟩
  let h172 := mkM3Env_row_at (mainSpec := mainSpec) 172
    ⟨"full_bve_commit_res", [i64, i64, i64], [i64],
      FullFastBveBudgets.fullBveCommitResTmkSpec, true⟩
  let h173 := mkM3Env_row_at (mainSpec := mainSpec) 173
    ⟨"full_bve_ext_need", [i64, i32, i32], [i64], fullBveExtNeedSpec, true⟩
  let h174 := mkM3Env_row_at (mainSpec := mainSpec) 174
    ⟨"full_bve_var", [i64, i32], [i64], FullFastBveBudgets.fullBveVarDefSpec, true⟩
  let h175 := mkM3Env_row_at (mainSpec := mainSpec) 175
    ⟨"full_init_fresh_var", [i64, i32], [], FullBvaHeap.fullInitFreshVarHeapSpec, true⟩
  let h176 := mkM3Env_row_at (mainSpec := mainSpec) 176
    ⟨"full_bva_hop1", [i64, i32, i32], [i64], FullBvaHeap.fullBvaHop1Spec, true⟩
  let h177 := mkM3Env_row_at (mainSpec := mainSpec) 177
    ⟨"full_bva_hop2", [i64, i32, i32], [i64], FullBvaHeap.fullBvaHop2Spec, true⟩
  let h178 := mkM3Env_row_at (mainSpec := mainSpec) 178
    ⟨"full_bva_hop3", [i64, i32, i32], [i64], FullBvaHeap.fullBvaHop3Spec, true⟩
  let h179 := mkM3Env_row_at (mainSpec := mainSpec) 179
    ⟨"full_bva_match_large", [i64, i32, i32, i32], [.bool],
      FullBvaHeap.fullBvaMatchLargeSpec, true⟩
  let h180 := mkM3Env_row_at (mainSpec := mainSpec) 180
    ⟨"full_bva_scan_cands", [i64, i32, i32, i64], [i32],
      FullBvaHeap.fullBvaScanCandsSpec, true⟩
  let h181 := mkM3Env_row_at (mainSpec := mainSpec) 181
    ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], FullBvaHeap.fullBvaPickCandSpec, true⟩
  let h182 := mkM3Env_row_at (mainSpec := mainSpec) 182
    ⟨"full_bva_filter_row", [i64, i32, i32, i32, i32, i32], [i32],
      FullBvaHeap.fullBvaFilterRowSpec, true⟩
  let h183 := mkM3Env_row_at (mainSpec := mainSpec) 183
    ⟨"full_bva_commit", [i64, i32], [.bool], FullBvaHeap.fullBvaCommitSpec, true⟩
  let h184 := mkM3Env_row_at (mainSpec := mainSpec) 184
    ⟨"full_bva_try_lit", [i64, i32, i64], [.bool], FullBvaHeap.fullBvaTryLitHeapSpec, true⟩
  let h185 := mkM3Env_row_at (mainSpec := mainSpec) 185
    ⟨"full_fheap_up", [i64, i64, i64, i32], [], FullBvaHeap.fullFheapUpSpec, true⟩
  let h186 := mkM3Env_row_at (mainSpec := mainSpec) 186
    ⟨"full_fheap_down", [i64, i64, i64, i32, i32], [], FullBvaHeap.fullFheapDownSpec, true⟩
  let h187 := mkM3Env_row_at (mainSpec := mainSpec) 187
    ⟨"full_factor", [i64, i64], [i64], FullBvaHeap.fullFactorHeapSpec, true⟩
  let h188 := mkM3Env_row_at (mainSpec := mainSpec) 188
    ⟨"full_scale_delta", [i64, i64], [i64], FullFastSched.schedScaleDeltaSpec, true⟩
  let h189 := mkM3Env_row_at (mainSpec := mainSpec) 189
    ⟨"full_min_u64", [i64, i64], [i64], FullFastSched.schedMinU64Spec, true⟩
  let h190 := mkM3Env_row_at (mainSpec := mainSpec) 190
    ⟨"full_max_u64", [i64, i64], [i64], FullFastSched.schedMaxU64Spec, true⟩
  let h191 := mkM3Env_row_at (mainSpec := mainSpec) 191
    ⟨"full_probe_dticks", [i64, .bool], [i64], FullFastSched.schedProbeDticksSpec, true⟩
  let h192 := mkM3Env_row_at (mainSpec := mainSpec) 192
    ⟨"full_backbone_lit", [i64, i32], [i64], FullM3Backbone.fullBackboneLitSpec, true⟩
  let h193 := mkM3Env_row_at (mainSpec := mainSpec) 193
    ⟨"full_backbone", [i64, i64], [i64], FullM3Backbone.fullBackboneSpec, true⟩
  let h194 := mkM3Env_row_at (mainSpec := mainSpec) 194
    ⟨"full_probe_tail", [i64, i64], [i64], FullFastSched.schedProbeTailSpec, true⟩
  let h195 := mkM3Env_row_at (mainSpec := mainSpec) 195
    ⟨"full_probe", [i64, .bool], [i64], FullFastSched.schedProbeSpec, true⟩
  let h196 := mkM3Env_row_at (mainSpec := mainSpec) 196
    ⟨"full_elim_dticks", [i64, .bool], [i64], FullFastSched.schedElimDticksSpec, true⟩
  let h197 := mkM3Env_row_at (mainSpec := mainSpec) 197
    ⟨"full_elim_collect_nbrs", [i64, i32], [i64], FullM3CongBva.m3ElimCollectNbrsSpec, true⟩
  let h198 := mkM3Env_row_at (mainSpec := mainSpec) 198
    ⟨"full_elim_bve", [i64, i64], [i64], FullM3CongBva.m3ElimBveSpec, true⟩
  let h199 := mkM3Env_row_at (mainSpec := mainSpec) 199
    ⟨"full_eliminate", [i64, .bool], [i64], FullFastSched.schedEliminateSpec, true⟩
  let h200 := mkM3Env_row_at (mainSpec := mainSpec) 200
    ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩
  let h201 := mkM3Env_row_at (mainSpec := mainSpec) 201
    ⟨"full_simplify", [i64, .bool, .bool], [i64], FullFastSched.schedSimplifySpec, true⟩
  let h202 := mkM3Env_row_at (mainSpec := mainSpec) 202
    ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩
  refine m3_tableImpl_step m3_162_188 rfl (.of (full_fwd_dedup_bins_bridge_wp Γ h103)) ?_
  refine m3_tableImpl_step m3_162_188 rfl (.of (full_fwd_check_cl_bridge_wp Γ h57 h103 h99)) ?_
  refine m3_tableImpl_step m3_162_188 rfl
    (.of (FullFastBveBudgets.fast_forward_sub_wp Γ h162 h11 h163)) ?_
  refine m3_tableImpl_step m3_162_188 rfl (.of (full_bve_collect_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_162_188 rfl (.of (FullDefSweep.full_bve_mark_and_wp Γ)) ?_
  refine m3_tableImpl_step m3_162_188 rfl
    (.of (FullDefSweep.full_find_definition_wp Γ fastKInv_laws
      (fast_kitten_init_adapter h129) (fast_kitten_add_clause_adapter h131)
      (fast_kitten_solve_adapter h140) (fast_kitten_core_adapter h141)
      (fast_kitten_shrink_adapter h142))) ?_
  refine m3_tableImpl_step m3_162_188 rfl
    (.of (FullDefSweep.full_bve_gates_wp Γ h166 h167)) ?_
  refine m3_tableImpl_step m3_162_188 rfl (.of (full_bve_resolve_pair_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_162_188 rfl (.of (fast_bve_weaken_tmk_wp Γ h95 h101 h96)) ?_
  refine m3_tableImpl_step m3_162_188 rfl (.of (full_bve_try_bce_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_162_188 rfl
    (.of (fast_bve_commit_res_tmk_wp Γ h12 h15 h99 h103)) ?_
  refine m3_tableImpl_step m3_162_188 rfl (.of (full_bve_ext_need_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_162_188 rfl
    (.of (FullFastBveBudgets.fast_bve_var_def_wp Γ h165 h173 h170 h102 h168 h169 h172 h171
      h95 h101 h96)) ?_
  refine m3_tableImpl_step m3_162_188 rfl (.of (FullBvaHeap.full_init_fresh_var_heap_wp Γ)) ?_
  refine m3_tableImpl_step m3_162_188 rfl (.of (FullBvaHeap.full_bva_hop1_wp Γ)) ?_
  refine m3_tableImpl_step m3_162_188 rfl (.of (FullBvaHeap.full_bva_hop2_wp Γ h176)) ?_
  refine m3_tableImpl_step m3_162_188 rfl (.of (FullBvaHeap.full_bva_hop3_wp Γ h177)) ?_
  refine m3_tableImpl_step m3_162_188 rfl (.of (FullBvaHeap.full_bva_match_large_wp Γ)) ?_
  refine m3_tableImpl_step m3_162_188 rfl (.of (FullBvaHeap.full_bva_scan_cands_wp Γ)) ?_
  refine m3_tableImpl_step m3_162_188 rfl (.of (FullBvaHeap.full_bva_pick_cand_wp Γ h178)) ?_
  refine m3_tableImpl_step m3_162_188 rfl (.of (FullBvaHeap.full_bva_filter_row_wp Γ h179)) ?_
  refine m3_tableImpl_step m3_162_188 rfl
    (.of (FullBvaHeap.full_bva_commit_wp Γ h14 h175 h99 h12 h15 h101 h57)) ?_
  refine m3_tableImpl_step m3_162_188 rfl
    (.of (FullBvaHeap.full_bva_try_lit_wp Γ h180 h181 h182 h183)) ?_
  refine m3_tableImpl_step m3_162_188 rfl (.of (FullBvaHeap.full_fheap_up_wp Γ)) ?_
  refine m3_tableImpl_step m3_162_188 rfl (.of (FullBvaHeap.full_fheap_down_wp Γ)) ?_
  refine m3_tableImpl_step m3_162_188 rfl (.of (FullBvaHeap.full_factor_wp Γ h185 h186 h184)) ?_
  refine m3_tableImpl_step m3_188_204 rfl (.of (FullFastSched.sched_scale_delta_wp Γ h9)) ?_
  refine m3_tableImpl_step m3_188_204 rfl (.of (FullFastSched.sched_min_u64_wp Γ)) ?_
  refine m3_tableImpl_step m3_188_204 rfl (.of (FullFastSched.sched_max_u64_wp Γ)) ?_
  refine m3_tableImpl_step m3_188_204 rfl (.of (FullFastSched.sched_probe_dticks_wp Γ h190)) ?_
  refine m3_tableImpl_step m3_188_204 rfl (.of (FullM3Backbone.m3_backbone_lit_wp Γ h103)) ?_
  refine m3_tableImpl_step m3_188_204 rfl (.of (FullM3Backbone.m3_backbone_wp Γ h30 h50 h192)) ?_
  refine m3_tableImpl_step m3_188_204 rfl
    (.of (m3_probe_tail_wp Γ h193 h114 h189 h112 h120)) ?_
  refine m3_tableImpl_step m3_188_204 rfl
    (.of (m3_probe_wp Γ h191 h9 h188 h126 h127 h189 h157 h161 h128 h193 h114 h112 h194)) ?_
  refine m3_tableImpl_step m3_188_204 rfl (.of (FullFastSched.sched_elim_dticks_wp Γ)) ?_
  refine m3_tableImpl_step m3_188_204 rfl (.of (FullM3CongBva.m3_elim_collect_nbrs_wp Γ)) ?_
  refine m3_tableImpl_step m3_188_204 rfl
    (.of (FullM3CongBva.m3_elim_bve_wp Γ h197 h174)) ?_
  refine m3_tableImpl_step m3_188_204 rfl
    (.of (FullM3CongBva.m3_eliminate_wp Γ h196 h9 h188 h127 h164 h189 h198 h187 h128)) ?_
  refine m3_tableImpl_step m3_188_204 rfl
    (.of (FullM3CongBva.m3_preprocess_wp Γ h50 h61 h188 h195 h199)) ?_
  refine m3_tableImpl_step m3_188_204 rfl
    (.of (FullFastSched.sched_simplify_wp Γ h30 h62 h195 h199)) ?_
  refine m3_tableImpl_step m3_188_204 rfl
    (.of (FullFastSched.sched_search_wp Γ h106 h86 h50 h83 h92 h91 h62 h201 h93 h94 h85)) ?_
  refine m3_tableImpl_step m3_188_204 rfl
    (.of (fun a m Q X h => FullFastSched.sched_kissat_solve_bytes_core_wp Γ
      h41 h44 h200 h202 h97 h7 a m Q X (hweaken a m Q X h))) ?_
  exact m3_tableImpl_nil mainSpec

private theorem m3_table_drop_112
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    TableImpl (mkM3Env mainSpec) (m3Fns.drop 112) ((m3SpecTable mainSpec).drop 112) := by
  let Γ := mkM3Env mainSpec
  let h11 := mkM3Env_row_at (mainSpec := mainSpec) 11
    ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  let h14 := mkM3Env_row_at (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let h15 := mkM3Env_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h30 := mkM3Env_row_at (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let h49 := mkM3Env_row_at (mainSpec := mainSpec) 49
    ⟨"full_propagate_ignore", [i64, i64], [i64], fullPropagateIgnoreSpec, true⟩
  let h50 := mkM3Env_row_at (mainSpec := mainSpec) 50
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let h57 := mkM3Env_row_at (mainSpec := mainSpec) 57
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  let h58 := mkM3Env_row_at (mainSpec := mainSpec) 58
    ⟨"full_sweep_bins", [i64], [], fullSweepBinsSpec, true⟩
  let h61 := mkM3Env_row_at (mainSpec := mainSpec) 61
    ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  let h95 := fast_extend_push2_adapter (mkM3Env_row_at (mainSpec := mainSpec) 95
    ⟨"full_extend_push2", [i64, i32, i32], [.bool],
      FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩)
  let h98 := mkM3Env_row_at (mainSpec := mainSpec) 98
    ⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩
  let h99 := mkM3Env_row_at (mainSpec := mainSpec) 99
    ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  let h100 := mkM3Env_row_at (mainSpec := mainSpec) 100
    ⟨"full_delete_bin_side", [i64, i32, i32], [], fullDeleteBinSideSpec, true⟩
  let h102 := mkM3Env_row_at (mainSpec := mainSpec) 102
    ⟨"full_set_inactive", [i64, i32, i32], [], fullSetInactiveSpec, true⟩
  let h103 := mkM3Env_row_at (mainSpec := mainSpec) 103
    ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  let h111 := mkM3Env_row_at (mainSpec := mainSpec) 111
    ⟨"full_probe_assume_pair", [i64, i32], [i64], fullProbeAssumePairSpec, true⟩
  let h113 := mkM3Env_row_at (mainSpec := mainSpec) 113
    ⟨"full_trans_lit", [i64, i32], [.bool], fullTransLitSpec, true⟩
  let h115 := mkM3Env_row_at (mainSpec := mainSpec) 115
    ⟨"full_viv_simplify", [i64, i32], [i64], fullVivSimplifySpec, true⟩
  let h116 := mkM3Env_row_at (mainSpec := mainSpec) 116
    ⟨"full_viv_sort_lits", [i64, i64, i32], [], fullVivSortLitsSpec, true⟩
  let h117 := mkM3Env_row_at (mainSpec := mainSpec) 117
    ⟨"full_viv_deduce", [i64, i32, i32, i64], [i32], fullVivDeduceSpec, true⟩
  let h118 := mkM3Env_row_at (mainSpec := mainSpec) 118
    ⟨"full_viv_commit", [i64, i32, i64, i32, .bool], [i64], fullVivCommitSpec, true⟩
  let h119 := mkM3Env_row_at (mainSpec := mainSpec) 119
    ⟨"full_viv_clause", [i64, i32], [i64], fullVivClauseSpec, true⟩
  let h121 := mkM3Env_row_at (mainSpec := mainSpec) 121
    ⟨"full_tarjan_pop_scc", [i64, i32, i32, i32], [.bool], fullTarjanPopSccSpec, true⟩
  let h122_fast := mkM3Env_row_at (mainSpec := mainSpec) 122
    ⟨"full_tarjan_scc", [i64], [i64], FullFastBveBudgets.fullTarjanSccFastSpec, true⟩
  let h122 : ∀ a m Q X, fullTarjanSccSpec a m Q X → Γ "full_tarjan_scc" [i64] [i64] a m Q X :=
    fun a m Q X h => h122_fast a m Q X (FullFastBveBudgets.fullTarjanSccFastSpec_of_canon h)
  let h123 := mkM3Env_row_at (mainSpec := mainSpec) 123
    ⟨"full_subst_elim_vars", [i64, i64], [.bool], fullSubstElimVarsSpec, true⟩
  let h124 := mkM3Env_row_at (mainSpec := mainSpec) 124
    ⟨"full_subst_rewrite_bins", [i64], [.bool], fullSubstRewriteBinsSpec, true⟩
  let h125 := mkM3Env_row_at (mainSpec := mainSpec) 125
    ⟨"full_subst_rewrite_ar", [i64], [.bool], fullSubstRewriteArSpec, true⟩
  let h129 := mkM3Env_row_at (mainSpec := mainSpec) 129
    ⟨"full_kitten_init", [i64, i32, i32], [], fullKittenInitSpec, true⟩
  let h130 := mkM3Env_row_at (mainSpec := mainSpec) 130
    ⟨"full_kitten_watch", [i64, i32, i32, i32], [], fullKittenWatchSpec, true⟩
  let h131 := mkM3Env_row_at (mainSpec := mainSpec) 131
    ⟨"full_kitten_add_clause", [i64, i32, i64, i32], [.bool], fullKittenAddClauseSpec, true⟩
  let h132 := mkM3Env_row_at (mainSpec := mainSpec) 132
    ⟨"full_kitten_assign", [i64, i32, i32], [], fullKittenAssignSpec, true⟩
  let h133 := mkM3Env_row_at (mainSpec := mainSpec) 133
    ⟨"full_kitten_mtf", [i64, i32], [], fullKittenMtfSpec, true⟩
  let h134 := mkM3Env_row_at (mainSpec := mainSpec) 134
    ⟨"full_kitten_backtrack", [i64, i32], [], fullKittenBacktrackSpec, true⟩
  let h135 := mkM3Env_row_at (mainSpec := mainSpec) 135
    ⟨"full_kitten_learn_unit0", [i64, i32, i32, .bool], [i32], fullKittenLearnUnit0Spec, true⟩
  let h136 := mkM3Env_row_at (mainSpec := mainSpec) 136
    ⟨"full_kitten_propagate", [i64], [i32], fullKittenPropagateSpec, true⟩
  let h137 := mkM3Env_row_at (mainSpec := mainSpec) 137
    ⟨"full_kitten_ana_clause", [i64, i32, i32], [], fullKittenAnaClauseSpec, true⟩
  let h138 := mkM3Env_row_at (mainSpec := mainSpec) 138
    ⟨"full_kitten_analyze", [i64, i32], [.bool], fullKittenAnalyzeSpec, true⟩
  let h139 := mkM3Env_row_at (mainSpec := mainSpec) 139
    ⟨"full_kitten_build_failing", [i64, i32], [], fullKittenBuildFailingSpec, true⟩
  let h140 := mkM3Env_row_at (mainSpec := mainSpec) 140
    ⟨"full_kitten_solve", [i64, i64], [i64], fullKittenSolveSpec, true⟩
  let h143 := mkM3Env_row_at (mainSpec := mainSpec) 143
    ⟨"full_kitten_flip", [i64, i32], [.bool], fullKittenFlipSpec, true⟩
  let h144 := mkM3Env_row_at (mainSpec := mainSpec) 144
    ⟨"full_cong_find", [i64, i32], [i32], fullCongFindSpec, true⟩
  let h145 := mkM3Env_row_at (mainSpec := mainSpec) 145
    ⟨"full_cong_merge", [i64, i32, i32], [.bool], fullCongMergeSpec, true⟩
  let h146 := mkM3Env_row_at (mainSpec := mainSpec) 146
    ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], fullHasTernarySpec, true⟩
  let h147 := mkM3Env_row_at (mainSpec := mainSpec) 147
    ⟨"full_sort_u32", [i64, i32], [], fullSortU32Spec, true⟩
  let h148 := mkM3Env_row_at (mainSpec := mainSpec) 148
    ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64], fullCongExtractIteSpec, true⟩
  let h149 := mkM3Env_row_at (mainSpec := mainSpec) 149
    ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64], fullCongEmitXorSpec, true⟩
  let h150 := mkM3Env_row_at (mainSpec := mainSpec) 150
    ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64],
      fullCongTryXorIteSpec, true⟩
  let h151 := mkM3Env_row_at (mainSpec := mainSpec) 151
    ⟨"full_cong_extract", [i64, i64, i64], [i64], FullDefSweep.fullCongExtractTickSpec, true⟩
  let h152 := mkM3Env_row_at (mainSpec := mainSpec) 152
    ⟨"full_cong_mark_trail", [i64, i64, i32], [], FullM3CongBva.m3CongMarkTrailSpec, true⟩
  let h153 := mkM3Env_row_at (mainSpec := mainSpec) 153
    ⟨"full_cong_unit_fold", [i64, i32, i32], [i64], FullM3CongBva.m3CongUnitFoldSpec, true⟩
  let h154 := mkM3Env_row_at (mainSpec := mainSpec) 154
    ⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64],
      FullM3CongBva.m3CongEquivFoldSpec, true⟩
  let h155 := mkM3Env_row_at (mainSpec := mainSpec) 155
    ⟨"full_cong_and_match", [i64, i32, i32], [.bool], FullM3CongBva.m3CongAndMatchSpec, true⟩
  let h156 := mkM3Env_row_at (mainSpec := mainSpec) 156
    ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64],
      FullM3CongBva.m3CongWorkStepSpec, true⟩
  let h158 := mkM3Env_row_at (mainSpec := mainSpec) 158
    ⟨"full_sweep_cone", [i64, i32], [i64],
      FullDefSweep.fullSweepConeKittenSpec FullFast.fastKInv, true⟩
  let h159 := mkM3Env_row_at (mainSpec := mainSpec) 159
    ⟨"full_sweep_refine_kitten", [i64, i32, i32], [],
      FullDefSweep.fullSweepRefineKittenSpec, true⟩
  let h160 := mkM3Env_row_at (mainSpec := mainSpec) 160
    ⟨"full_sweep_var", [i64, i32, i64], [i64], FullDefSweep.fullSweepVarKittenSpec, true⟩
  let h28 := mkM3Env_row_at (mainSpec := mainSpec) 28
    ⟨"full_assign", [i64, i32, i32], [], fullAssignSpec, true⟩
  refine m3_tableImpl_step m3_112_129 rfl (.of (FullM3Backbone.m3_probe_run_cursor_wp Γ h30 h111))
    ?_
  refine m3_tableImpl_step m3_112_129 rfl (.of (full_trans_lit_bridge_wp Γ h100 h103)) ?_
  refine m3_tableImpl_step m3_112_129 rfl
    (.of (FullFastBveBudgets.fast_transitive_wp Γ h30 h113 h50 h14)) ?_
  refine m3_tableImpl_step m3_112_129 rfl
    (.of (full_viv_simplify_bridge_wp Γ h57 h103 h99 h15)) ?_
  refine m3_tableImpl_step m3_112_129 rfl (.of (full_viv_sort_lits_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_112_129 rfl (.of (full_viv_deduce_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_112_129 rfl (.of (full_viv_commit_bridge_wp Γ h57 h103 h99 h15)) ?_
  refine m3_tableImpl_step m3_112_129 rfl
    (.of (full_viv_clause_bridge_wp Γ h115 h116 h28 h49 h30 h117 h118)) ?_
  refine m3_tableImpl_step m3_112_129 rfl
    (.of (FullM3VivChrono.m3_vivify_wp Γ h30 h11 h119 h50)) ?_
  refine m3_tableImpl_step m3_112_129 rfl (.of (full_tarjan_pop_scc_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_112_129 rfl (.of (FullFastBveBudgets.fast_tarjan_scc_wp Γ h121)) ?_
  refine m3_tableImpl_step m3_112_129 rfl
    (.of (full_subst_elim_vars_bridge_wp Γ h103 h50 h95 h102)) ?_
  refine m3_tableImpl_step m3_112_129 rfl (.of (full_subst_rewrite_bins_bridge_wp Γ h103 h99)) ?_
  refine m3_tableImpl_step m3_112_129 rfl
    (.of (full_subst_rewrite_ar_bridge_wp Γ h11 h103 h99)) ?_
  refine m3_tableImpl_step m3_112_129 rfl
    (.of (FullFastSched.sched_substitute_wp Γ h30 h122 h123 h124 h125 h61 h50)) ?_
  refine m3_tableImpl_step m3_112_129 rfl
    (.of (FullFastSched.sched_enter_dense_wp Γ h30 h50 h58 h15 h61 h11)) ?_
  refine m3_tableImpl_step m3_112_129 rfl (.of (full_rebuild_watches_bridge_wp Γ h61 h50)) ?_
  refine m3_tableImpl_step m3_129_144 rfl (.of (full_kitten_init_wp Γ)) ?_
  refine m3_tableImpl_step m3_129_144 rfl (.of (full_kitten_watch_wp Γ)) ?_
  refine m3_tableImpl_step m3_129_144 rfl (.of (full_kitten_add_clause_wp Γ h130)) ?_
  refine m3_tableImpl_step m3_129_144 rfl (.of (full_kitten_assign_wp Γ)) ?_
  refine m3_tableImpl_step m3_129_144 rfl (.of (full_kitten_mtf_wp Γ)) ?_
  refine m3_tableImpl_step m3_129_144 rfl (.of (full_kitten_backtrack_wp Γ)) ?_
  refine m3_tableImpl_step m3_129_144 rfl (.of (full_kitten_learn_unit0_wp Γ)) ?_
  refine m3_tableImpl_step m3_129_144 rfl (.of (full_kitten_propagate_wp Γ h132 h135)) ?_
  refine m3_tableImpl_step m3_129_144 rfl (.of (full_kitten_ana_clause_wp Γ)) ?_
  refine m3_tableImpl_step m3_129_144 rfl
    (.of (full_kitten_analyze_wp Γ h137 h134 h133 h135 h132 h130)) ?_
  refine m3_tableImpl_step m3_129_144 rfl (.of (full_kitten_build_failing_wp Γ)) ?_
  refine m3_tableImpl_step m3_129_144 rfl
    (.of (full_kitten_solve_wp Γ h134 h132 h136 h138 h139)) ?_
  refine m3_tableImpl_step m3_129_144 rfl (.of (full_kitten_core_wp Γ)) ?_
  refine m3_tableImpl_step m3_129_144 rfl (.of (full_kitten_shrink_wp Γ h130)) ?_
  refine m3_tableImpl_step m3_129_144 rfl (.of (full_kitten_flip_wp Γ)) ?_
  refine m3_tableImpl_step m3_144_162 rfl (.of (full_cong_find_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_144_162 rfl (.of (full_cong_merge_bridge_wp Γ h144 h99)) ?_
  refine m3_tableImpl_step m3_144_162 rfl (.of (full_has_ternary_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_144_162 rfl (.of (full_sort_u32_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_144_162 rfl (.of (full_cong_extract_ite_bridge_wp Γ h146)) ?_
  refine m3_tableImpl_step m3_144_162 rfl (.of (full_cong_emit_xor_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_144_162 rfl
    (.of (full_cong_try_xor_ite_bridge_wp Γ h146 h149 h148)) ?_
  refine m3_tableImpl_step m3_144_162 rfl
    (.of (FullDefSweep.full_cong_extract_wp Γ h11 h98 (fast_cong_try_xor_ite_adapter h150))) ?_
  refine m3_tableImpl_step m3_144_162 rfl (.of (FullM3CongBva.m3_cong_mark_trail_wp Γ h144)) ?_
  refine m3_tableImpl_step m3_144_162 rfl
    (.of (FullM3CongBva.m3_cong_unit_fold_wp Γ h103 h152)) ?_
  refine m3_tableImpl_step m3_144_162 rfl
    (.of (FullM3CongBva.m3_cong_equiv_fold_wp Γ h144 h103 h152 h145)) ?_
  refine m3_tableImpl_step m3_144_162 rfl (.of (FullM3CongBva.m3_cong_and_match_wp Γ h144)) ?_
  refine m3_tableImpl_step m3_144_162 rfl
    (.of (FullM3CongBva.m3_cong_work_step_wp Γ h144 h147 h153 h154 h155)) ?_
  refine m3_tableImpl_step m3_144_162 rfl
    (.of (FullM3CongBva.m3_congruence_dense_wp Γ h151 h156)) ?_
  refine m3_tableImpl_step m3_144_162 rfl
    (.of (FullDefSweep.full_sweep_cone_wp Γ fastKInv_laws
      (fast_kitten_init_adapter h129) (fast_kitten_add_clause_adapter h131))) ?_
  refine m3_tableImpl_step m3_144_162 rfl (.of (FullDefSweep.full_sweep_refine_kitten_wp Γ)) ?_
  refine m3_tableImpl_step m3_144_162 rfl
    (.of (FullDefSweep.full_sweep_var_wp Γ fastKInv_laws h158
      (fast_kitten_solve_adapter h140) h159 (fast_kitten_flip_adapter h143)
      (fast_sweep_add_unit_adapter h103) h99)) ?_
  refine m3_tableImpl_step m3_144_162 rfl (.of (FullDefSweep.full_sweep_dense_wp Γ h160)) ?_
  exact m3_table_drop_162 mainSpec hweaken

private theorem m3_table_drop_51
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    TableImpl (mkM3Env mainSpec) (m3Fns.drop 51) ((m3SpecTable mainSpec).drop 51) := by
  let Γ := mkM3Env mainSpec
  let h8 := mkM3Env_row_at (mainSpec := mainSpec) 8
    ⟨"full_isqrt", [i64], [i64], fullIsqrtSpec, true⟩
  let h9 := mkM3Env_row_at (mainSpec := mainSpec) 9
    ⟨"full_ilog10", [i64], [i64], fullIlog10Spec, true⟩
  let h10 := mkM3Env_row_at (mainSpec := mainSpec) 10
    ⟨"full_rng_next", [i64], [i64], fullRngNextSpec, true⟩
  let h11 := mkM3Env_row_at (mainSpec := mainSpec) 11
    ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  let h14 := mkM3Env_row_at (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let h15 := mkM3Env_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h17 := mkM3Env_row_at (mainSpec := mainSpec) 17
    ⟨"full_heap_down", [i64, i32], [], fullHeapDownSpec, true⟩
  let h19 := mkM3Env_row_at (mainSpec := mainSpec) 19
    ⟨"full_heap_pop", [i64], [i64], fullHeapPopSpec, true⟩
  let h21 := mkM3Env_row_at (mainSpec := mainSpec) 21
    ⟨"full_bump_var", [i64, i32], [], fullBumpVarSpec, true⟩
  let h22 := mkM3Env_row_at (mainSpec := mainSpec) 22
    ⟨"full_bump_decay", [i64], [], fullBumpDecaySpec, true⟩
  let h24 := mkM3Env_row_at (mainSpec := mainSpec) 24
    ⟨"full_queue_mtf", [i64, i32], [], fullQueueMtfSpec, true⟩
  let h25 := mkM3Env_row_at (mainSpec := mainSpec) 25
    ⟨"full_tick_rel", [i64], [], fullTickRelSpec, true⟩
  let h26 := mkM3Env_row_at (mainSpec := mainSpec) 26
    ⟨"full_ema_update", [i64, i64], [], fullEmaUpdateSpec, true⟩
  let h27 := mkM3Env_row_at (mainSpec := mainSpec) 27
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  let h28 := mkM3Env_row_at (mainSpec := mainSpec) 28
    ⟨"full_assign", [i64, i32, i32], [], fullAssignSpec, true⟩
  let h30 := mkM3Env_row_at (mainSpec := mainSpec) 30
    ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  let h31 := mkM3Env_row_at (mainSpec := mainSpec) 31
    ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], fullAddClauseSpec, true⟩
  let h45 := mkM3Env_row_at (mainSpec := mainSpec) 45
    ⟨"full_find_repl", [i64, i64], [i64], fullFindReplSpec, true⟩
  let h50 := mkM3Env_row_at (mainSpec := mainSpec) 50
    ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  let h51 := mkM3Env_row_at (mainSpec := mainSpec) 51
    ⟨"full_recompute_tiers", [i64], [], fullRecomputeTiersSpec, true⟩
  let h52 := mkM3Env_row_at (mainSpec := mainSpec) 52
    ⟨"full_mark_reasons", [i64, .bool], [], fullMarkReasonsSpec, true⟩
  let h53 := mkM3Env_row_at (mainSpec := mainSpec) 53
    ⟨"full_red_less", [i64, i32, i32], [.bool], fullRedLessSpec, true⟩
  let h54 := mkM3Env_row_at (mainSpec := mainSpec) 54
    ⟨"full_red_sift", [i64, i64, i64, i64], [], fullRedSiftSpec, true⟩
  let h55 := mkM3Env_row_at (mainSpec := mainSpec) 55
    ⟨"full_sort_reds", [i64, i64], [], fullSortRedsSpec, true⟩
  let h56 := mkM3Env_row_at (mainSpec := mainSpec) 56
    ⟨"full_lit_rank", [i64, i64, i32], [i64], fullLitRankSpec, true⟩
  let h57 := mkM3Env_row_at (mainSpec := mainSpec) 57
    ⟨"full_unwatch_large", [i64, i32, i32], [], fullUnwatchLargeSpec, true⟩
  let h58 := mkM3Env_row_at (mainSpec := mainSpec) 58
    ⟨"full_sweep_bins", [i64], [], fullSweepBinsSpec, true⟩
  let h59 := mkM3Env_row_at (mainSpec := mainSpec) 59
    ⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64], fullSweepCopySpec, true⟩
  let h60 := mkM3Env_row_at (mainSpec := mainSpec) 60
    ⟨"full_rewatch_arena", [i64, i64], [.bool], fullRewatchArenaSpec, true⟩
  let h61 := mkM3Env_row_at (mainSpec := mainSpec) 61
    ⟨"full_arena_sweep", [i64], [i64], fullArenaSweepSpec, true⟩
  let h62 := mkM3Env_row_at (mainSpec := mainSpec) 62
    ⟨"full_reduce", [i64, .bool], [i64], fullReduceSpec, true⟩
  let h63 := mkM3Env_row_at (mainSpec := mainSpec) 63
    ⟨"full_analyze_lit", [i64, i32, i32], [.bool], fullAnalyzeLitSpec, true⟩
  let h64 := mkM3Env_row_at (mainSpec := mainSpec) 64
    ⟨"full_analyze_rsn", [i64, i32, i32], [.bool], fullAnalyzeRsnSpec, true⟩
  let h65 := mkM3Env_row_at (mainSpec := mainSpec) 65
    ⟨"full_clear_ana", [i64], [], fullClearAnaSpec, true⟩
  let h66 := mkM3Env_row_at (mainSpec := mainSpec) 66
    ⟨"full_bump_analyzed", [i64], [], fullBumpAnalyzedSpec, true⟩
  let h67 := mkM3Env_row_at (mainSpec := mainSpec) 67
    ⟨"full_otfs_large", [i64, i32, i32], [.bool], fullOtfsLargeSpec, true⟩
  let h68 := mkM3Env_row_at (mainSpec := mainSpec) 68
    ⟨"full_otfs_bin", [i64, i32, i32], [.bool], fullOtfsBinSpec, true⟩
  let h69 := mkM3Env_row_at (mainSpec := mainSpec) 69
    ⟨"full_otfs_subsume", [i64, i32, i64, i64, .bool], [], fullOtfsSubsumeSpec, true⟩
  let h70 := mkM3Env_row_at (mainSpec := mainSpec) 70
    ⟨"full_min_mark", [i64, i32, i8], [], fullMinMarkSpec, true⟩
  let h71 := mkM3Env_row_at (mainSpec := mainSpec) 71
    ⟨"full_min_lit", [i64, i32], [.bool], fullMinLitSpec, true⟩
  let h72 := mkM3Env_row_at (mainSpec := mainSpec) 72
    ⟨"full_tmp_less", [i64, i64, i32, i32], [.bool], fullTmpLessSpec, true⟩
  let h73 := mkM3Env_row_at (mainSpec := mainSpec) 73
    ⟨"full_sort_tmp_sift", [i64, i64, i64, i64, i64], [], fullSortTmpSiftSpec, true⟩
  let h74 := mkM3Env_row_at (mainSpec := mainSpec) 74
    ⟨"full_sort_tmp", [i64], [], fullSortTmpSpec, true⟩
  let h75 := mkM3Env_row_at (mainSpec := mainSpec) 75
    ⟨"full_shrink_lower", [i64, i32, i32], [.bool], fullShrinkLowerSpec, true⟩
  let h76 := mkM3Env_row_at (mainSpec := mainSpec) 76
    ⟨"full_shrink_blk", [i64, i64, i64, i32, i64], [], fullShrinkBlkSpec, true⟩
  let h77 := mkM3Env_row_at (mainSpec := mainSpec) 77
    ⟨"full_min_shrink", [i64], [], fullMinShrinkSpec, true⟩
  let h78 := mkM3Env_row_at (mainSpec := mainSpec) 78
    ⟨"full_det_new_level", [i64, i64], [i64], fullDetNewLevelSpec, true⟩
  let h79 := mkM3Env_row_at (mainSpec := mainSpec) 79
    ⟨"full_one_lit_confl", [i64], [i64], fullOneLitConflSpec, true⟩
  let h80 := mkM3Env_row_at (mainSpec := mainSpec) 80
    ⟨"full_deduce_1uip", [i64], [i64], fullDeduce1uipSpec, true⟩
  let h81 := mkM3Env_row_at (mainSpec := mainSpec) 81
    ⟨"full_eager_subsume", [i64, i64], [], fullEagerSubsumeSpec, true⟩
  let h82 := mkM3Env_row_at (mainSpec := mainSpec) 82
    ⟨"full_learn_clause", [i64, i64], [i64], fullLearnClauseSpec, true⟩
  let h83 := mkM3Env_row_at (mainSpec := mainSpec) 83
    ⟨"full_analyze", [i64], [i64], fullAnalyzeSpec, true⟩
  let h84 := mkM3Env_row_at (mainSpec := mainSpec) 84
    ⟨"full_next_dec_var", [i64], [i64], fullNextDecVarSpec, true⟩
  let h87 := mkM3Env_row_at (mainSpec := mainSpec) 87
    ⟨"full_walk_collect", [i64], [i64], fullWalkCollectSpec, true⟩
  let h88 := mkM3Env_row_at (mainSpec := mainSpec) 88
    ⟨"full_walk_cl_sat", [i64, i64, i64], [.bool], fullWalkClSatSpec, true⟩
  let h89 := mkM3Env_row_at (mainSpec := mainSpec) 89
    ⟨"full_walk_pick_lit", [i64, i64, i64], [i32], fullWalkPickLitSpec, true⟩
  let h90 := mkM3Env_row_at (mainSpec := mainSpec) 90
    ⟨"full_walk", [i64], [], fullWalkSpec, true⟩
  let h98 := mkM3Env_row_at (mainSpec := mainSpec) 98
    ⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩
  let h99 := mkM3Env_row_at (mainSpec := mainSpec) 99
    ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  let h100 := mkM3Env_row_at (mainSpec := mainSpec) 100
    ⟨"full_delete_bin_side", [i64, i32, i32], [], fullDeleteBinSideSpec, true⟩
  let h103 := mkM3Env_row_at (mainSpec := mainSpec) 103
    ⟨"full_add_unit", [i64, i32], [.bool], fullAddUnitSpec, true⟩
  let h104 := mkM3Env_row_at (mainSpec := mainSpec) 104
    ⟨"full_lucky_scan", [i64, .bool, .bool], [i64], fullLuckyScanSpec, true⟩
  let h105 := mkM3Env_row_at (mainSpec := mainSpec) 105
    ⟨"full_lucky_polar", [i64], [i64], fullLuckyPolarSpec, true⟩
  let h107 := mkM3Env_row_at (mainSpec := mainSpec) 107
    ⟨"full_hbr_dom", [i64, i32, i32], [i32], fullHbrDomSpec, true⟩
  let h108 := mkM3Env_row_at (mainSpec := mainSpec) 108
    ⟨"full_probe_prop_lit", [i64, i32], [.bool], fullProbePropLitSpec, true⟩
  let h109 := mkM3Env_row_at (mainSpec := mainSpec) 109
    ⟨"full_probe_prop", [i64], [i64], fullProbePropSpec, true⟩
  let h110 := mkM3Env_row_at (mainSpec := mainSpec) 110
    ⟨"full_probe_flush_hbr", [i64, i64], [i64], fullProbeFlushHbrSpec, true⟩
  refine m3_tableImpl_step m3_51_58 rfl (.of (full_recompute_tiers_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_51_58 rfl (.of (full_mark_reasons_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_51_58 rfl (.of (full_red_less_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_51_58 rfl (.of (full_red_sift_bridge_wp Γ h53)) ?_
  refine m3_tableImpl_step m3_51_58 rfl (.of (full_sort_reds_bridge_wp Γ h54)) ?_
  refine m3_tableImpl_step m3_51_58 rfl (.of (full_lit_rank_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_51_58 rfl (.of (full_unwatch_large_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_58 rfl (.of (FullFastSched.sched_sweep_bins_wp Γ h14)) ?_
  refine m3_tableImpl_step m3_59_64 rfl (.of (full_sweep_copy_bridge_wp Γ h27 h15)) ?_
  refine m3_tableImpl_step m3_59_64 rfl (.of (full_rewatch_arena_bridge_wp Γ h56 h15)) ?_
  refine m3_tableImpl_step m3_59_64 rfl (.of (full_arena_sweep_bridge_wp Γ h58 h11 h59 h60)) ?_
  refine m3_tableImpl_step m3_59_64 rfl
    (.of (full_reduce_bridge_wp Γ h8 h9 h11 h51 h52 h55 h30 h50 h61)) ?_
  refine m3_tableImpl_step m3_59_64 rfl (.of (full_analyze_lit_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_64 rfl (.of (FullM3VivChrono.m3_analyze_rsn_wp Γ h63)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_clear_ana_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_bump_analyzed_bridge_wp Γ h21 h24 h22)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_otfs_large_bridge_wp Γ h57 h15)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_otfs_bin_bridge_wp Γ h57 h15)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_otfs_subsume_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_min_mark_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_min_lit_bridge_wp Γ h70)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_tmp_less_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_sort_tmp_sift_bridge_wp Γ h72)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_sort_tmp_bridge_wp Γ h73)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_shrink_lower_bridge_wp Γ h70 h71)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_shrink_blk_bridge_wp Γ h75 h70)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_min_shrink_bridge_wp Γ h74 h70 h71 h76)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_det_new_level_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_65_112 rfl
    (.of (full_one_lit_confl_wp Γ h78 h30 h27 h57 h15)) ?_
  refine m3_tableImpl_step m3_65_112 rfl
    (.of (full_deduce_1uip_wp Γ h63 h64 h65 h66 h67 h68 h69)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_eager_subsume_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_65_112 rfl
    (.of (full_learn_clause_bridge_wp Γ h30 h27 h78 h14 h62 h31 h81)) ?_
  refine m3_tableImpl_step m3_65_112 rfl
    (.of (full_analyze_bridge_wp Γ h79 h80 h77 h25 h26 h82)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_next_dec_var_bridge_wp Γ h19)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_decide_bridge_wp Γ h84 h28)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_warmup_bridge_wp Γ h84 h28 h50 h30)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_walk_collect_bridge_wp Γ h11)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_walk_cl_sat_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_walk_pick_lit_bridge_wp Γ h10)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_walk_bridge_wp Γ h87 h88 h10 h89)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_rephase_bridge_wp Γ h30 h90 h9)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_switch_mode_bridge_wp Γ h17 h9)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_restart_due_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_restart_bridge_wp Γ h84 h30)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (fast_extend_push2_tmk_wp Γ)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (fast_extend_push_cl_tmk_wp Γ)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_extend_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_has_bin_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_add_bin_bridge_wp Γ h98 h27 h15)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_delete_bin_side_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_delete_binary_bridge_wp Γ h100)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_set_inactive_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_add_unit_bridge_wp Γ h30 h27)) ?_
  refine m3_tableImpl_step m3_65_112 rfl
    (.of (full_lucky_scan_bridge_wp Γ h28 h30 h50 h83)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_lucky_polar_bridge_wp Γ h11)) ?_
  refine m3_tableImpl_step m3_65_112 rfl
    (.of (full_lucky_bridge_wp Γ h105 h104 h28 h30 h50)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_hbr_dom_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_65_112 rfl
    (.of (full_probe_prop_lit_bridge_wp Γ h45 h15 h107 h27)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_probe_prop_bridge_wp Γ h108)) ?_
  refine m3_tableImpl_step m3_65_112 rfl (.of (full_probe_flush_hbr_bridge_wp Γ h99 h50)) ?_
  refine m3_tableImpl_step m3_65_112 rfl
    (.of (full_probe_assume_pair_bridge_wp Γ h28 h109 h30 h83 h50 h110 h103)) ?_
  exact m3_table_drop_112 mainSpec hweaken

private theorem m3_table_drop_8
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    TableImpl (mkM3Env mainSpec) (m3Fns.drop 8) ((m3SpecTable mainSpec).drop 8) := by
  let Γ := mkM3Env mainSpec
  let h2 := mkM3Env_row_at (mainSpec := mainSpec) 2
    ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩
  let h5 := mkM3Env_row_at (mainSpec := mainSpec) 5
    ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩
  let h6 := mkM3Env_row_at (mainSpec := mainSpec) 6
    ⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩
  let h12 := mkM3Env_row_at (mainSpec := mainSpec) 12
    ⟨"full_alloc_cl", [i64, i32, i32, .bool], [i64], fullAllocClSpec, true⟩
  let h13 := mkM3Env_row_at (mainSpec := mainSpec) 13
    ⟨"full_wsort_sift", [i64, i64, i64, i64], [], fullWsortSiftSpec, true⟩
  let h14 := mkM3Env_row_at (mainSpec := mainSpec) 14
    ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  let h15 := mkM3Env_row_at (mainSpec := mainSpec) 15
    ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], fullWatchPushSpec, true⟩
  let h16 := mkM3Env_row_at (mainSpec := mainSpec) 16
    ⟨"full_heap_up", [i64, i32], [], fullHeapUpSpec, true⟩
  let h17 := mkM3Env_row_at (mainSpec := mainSpec) 17
    ⟨"full_heap_down", [i64, i32], [], fullHeapDownSpec, true⟩
  let h18 := mkM3Env_row_at (mainSpec := mainSpec) 18
    ⟨"full_heap_push", [i64, i32], [], fullHeapPushSpec, true⟩
  let h20 := mkM3Env_row_at (mainSpec := mainSpec) 20
    ⟨"full_rescale", [i64], [], fullRescaleSpec, true⟩
  let h23 := mkM3Env_row_at (mainSpec := mainSpec) 23
    ⟨"full_queue_renumber", [i64], [], fullQueueRenumberSpec, true⟩
  let h27 := mkM3Env_row_at (mainSpec := mainSpec) 27
    ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  let h29 := mkM3Env_row_at (mainSpec := mainSpec) 29
    ⟨"full_save_target_best", [i64], [], fullSaveTargetBestSpec, true⟩
  let h31 := mkM3Env_row_at (mainSpec := mainSpec) 31
    ⟨"full_add_clause", [i64, i32, i32, .bool], [i64], fullAddClauseSpec, true⟩
  let h32 := mkM3Env_row_at (mainSpec := mainSpec) 32
    ⟨"full_zero_tables1", [i64], [], fullZeroTables1Spec, true⟩
  let h33 := mkM3Env_row_at (mainSpec := mainSpec) 33
    ⟨"full_zero_tables2", [i64], [], fullZeroTables2Spec, true⟩
  let h34 := mkM3Env_row_at (mainSpec := mainSpec) 34
    ⟨"full_fixed_bytes", [i64], [i64], fullFixedBytesSpec, true⟩
  let h35 := mkM3Env_row_at (mainSpec := mainSpec) 35
    ⟨"full_init_ptrs", [i64, i64, i64], [], fullInitPtrsSpec, true⟩
  let h36_fast := mkM3Env_row_at (mainSpec := mainSpec) 36
    ⟨"full_init_hdr", [i64, i64, i64, i64], [], FullFastBveBudgets.fullFastInitHdrSpec, true⟩
  let h36 : ∀ a m Q X, fullInitHdrSpec a m Q X →
      Γ "full_init_hdr" [i64, i64, i64, i64] [] a m Q X :=
    fun a m Q X h => h36_fast a m Q X (FullFastBveBudgets.fullFastInitHdrSpec_of_canon h)
  let h37 := mkM3Env_row_at (mainSpec := mainSpec) 37
    ⟨"full_calc_max_v", [i64, i64, i64, i64], [i64], fullCalcMaxVSpec, true⟩
  let h38 := mkM3Env_row_at (mainSpec := mainSpec) 38
    ⟨"full_calc_ext_cap", [i64], [i64], fullCalcExtCapSpec, true⟩
  let h39 := mkM3Env_row_at (mainSpec := mainSpec) 39
    ⟨"full_calc_scr_cap", [i64], [i64], fullCalcScrCapSpec, true⟩
  let h40 := mkM3Env_row_at (mainSpec := mainSpec) 40
    ⟨"full_init_arenas", [i64, i64, i64, i64], [], fullInitArenasSpec, true⟩
  let h42 := mkM3Env_row_at (mainSpec := mainSpec) 42
    ⟨"full_skip_cl", [i64, i64], [.bool], fullSkipClSpec, true⟩
  let h43 := mkM3Env_row_at (mainSpec := mainSpec) 43
    ⟨"full_ingest_cl", [i64, i64], [i64], fullIngestClSpec, true⟩
  let h47 := mkM3Env_row_at (mainSpec := mainSpec) 47
    ⟨"full_prop_lit_raw", [i64, i32, i64], [.bool], fullPropLitSpec, true⟩
  let h48 := mkM3Env_row_at (mainSpec := mainSpec) 48
    ⟨"full_prop_lit", [i64, i32, i64], [.bool], fullPropLitSpec, true⟩
  let h49 := mkM3Env_row_at (mainSpec := mainSpec) 49
    ⟨"full_propagate_ignore", [i64, i64], [i64], fullPropagateIgnoreSpec, true⟩
  refine m3_tableImpl_step m3_0_25 rfl (.of (full_isqrt_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (full_ilog10_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (full_rng_next_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (full_arena_next_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (full_alloc_cl_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (full_wsort_sift_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (full_wstack_defrag_bridge_wp Γ h13)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (full_watch_push_bridge_wp Γ h14)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (full_heap_up_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (full_heap_down_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (full_heap_push_bridge_wp Γ h16)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (full_heap_pop_bridge_wp Γ h17)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (full_rescale_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (full_bump_var_bridge_wp Γ h16 h20)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (full_bump_decay_bridge_wp Γ h20)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (full_queue_renumber_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (full_queue_mtf_bridge_wp Γ h23)) ?_
  refine m3_tableImpl_step m3_25 rfl (.of (FullM3VivChrono.m3_tick_rel_wp Γ)) ?_
  refine m3_tableImpl_step m3_26_36 rfl (.of (full_ema_update_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_26_36 rfl (.of (full_assign_lvl_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_26_36 rfl (.of (full_assign_bridge_wp Γ h27)) ?_
  refine m3_tableImpl_step m3_26_36 rfl (.of (full_save_target_best_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_26_36 rfl (.of (full_backtrack_bridge_wp Γ h29 h18)) ?_
  refine m3_tableImpl_step m3_26_36 rfl (.of (full_add_clause_bridge_wp Γ h12 h15)) ?_
  refine m3_tableImpl_step m3_26_36 rfl (.of (full_zero_tables1_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_26_36 rfl (.of (full_zero_tables2_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_26_36 rfl (.of (full_fixed_bytes_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_26_36 rfl (.of (full_init_ptrs_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_36 rfl (.of (FullFastBveBudgets.fast_init_hdr_wp Γ)) ?_
  refine m3_tableImpl_step m3_37_47 rfl (.of (full_calc_max_v_bridge_wp Γ h34)) ?_
  refine m3_tableImpl_step m3_37_47 rfl (.of (full_calc_ext_cap_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_37_47 rfl (.of (full_calc_scr_cap_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_37_47 rfl (.of (full_init_arenas_bridge_wp Γ h35)) ?_
  refine m3_tableImpl_step m3_37_47 rfl
    (.of (full_init_state_bridge_wp Γ h5 h34 h37 h38 h39 h40 h36 h32 h33)) ?_
  refine m3_tableImpl_step m3_37_47 rfl (.of (full_skip_cl_bridge_wp Γ h6)) ?_
  refine m3_tableImpl_step m3_37_47 rfl (.of (full_ingest_cl_bridge_wp Γ h6 h27 h31)) ?_
  refine m3_tableImpl_step m3_37_47 rfl (.of (full_parse_body_bridge_wp Γ h42 h43 h2)) ?_
  refine m3_tableImpl_step m3_37_47 rfl (.of (full_find_repl_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_37_47 rfl (.of (full_assign_level_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_47_51 rfl (.of (FastCore.full_prop_lit_wp Γ h15)) ?_
  refine m3_tableImpl_step m3_47_51 rfl (.of (FullM3VivChrono.m3_prop_lit_wp Γ h47 h15)) ?_
  refine m3_tableImpl_step m3_47_51 rfl (.of (FastCore.full_propagate_ignore_wp Γ h48)) ?_
  refine m3_tableImpl_step m3_47_51 rfl (.of (FastCore.full_propagate_wp Γ h49)) ?_
  exact m3_table_drop_51 mainSpec hweaken

/-- Unconditional row-by-row `TableImpl` discharging all `204 / 204` functions of `m3Fns`
against `m3SpecTable mainSpec`. -/
theorem mkM3Env_tableImpl
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    TableImpl (mkM3Env mainSpec) m3Fns (m3SpecTable mainSpec) := by
  let Γ := mkM3Env mainSpec
  let h0 := mkM3Env_row_at (mainSpec := mainSpec) 0
    ⟨"kissat_is_ws", [i64], [.bool], kissatIsWsSpec, true⟩
  let h1 := mkM3Env_row_at (mainSpec := mainSpec) 1
    ⟨"kissat_is_digit", [i64], [.bool], kissatIsDigitSpec, true⟩
  let h2 := mkM3Env_row_at (mainSpec := mainSpec) 2
    ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩
  let h3 := mkM3Env_row_at (mainSpec := mainSpec) 3
    ⟨"kissat_skip_ws1", [i64, i64], [.bool], kissatSkipWs1Spec, true⟩
  let h4 := mkM3Env_row_at (mainSpec := mainSpec) 4
    ⟨"kissat_read_nat", [i64, i64], [.bool], kissatReadNatSpec, true⟩
  let h5 := mkM3Env_row_at (mainSpec := mainSpec) 5
    ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩
  let h6 := mkM3Env_row_at (mainSpec := mainSpec) 6
    ⟨"kissat_next_lit", [i64, i64], [i64], kissatNextLitSpec, true⟩
  change TableImpl Γ (m3Fns.drop 0) ((m3SpecTable mainSpec).drop 0)
  refine m3_tableImpl_step m3_0_25 rfl (.of (kissat_is_ws_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (kissat_is_digit_bridge_wp Γ)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (kissat_skip_ws_comments_bridge_wp Γ h0)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (kissat_skip_ws1_bridge_wp Γ h0)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (kissat_read_nat_bridge_wp Γ h1 h0)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (kissat_parse_header_bridge_wp Γ h2 h3 h4)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (kissat_next_lit_bridge_wp Γ h2 h4)) ?_
  refine m3_tableImpl_step m3_0_25 rfl (.of (kissat_check_model_bridge_wp Γ h5 h6 h2)) ?_
  exact m3_table_drop_8 mainSpec hweaken

/-- Unconditional `ModuleOk` assembly for `mkM3Env mainSpec` on `m3Module` (`204/204`). -/
theorem mkM3Env_moduleOk
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ a m Q X, mainSpec a m Q X → fullSolveBytesCoreSpec a m Q X) :
    ModuleOk (mkM3Env mainSpec) m3Module :=
  Env.ofTable_moduleOk m3_acyclic (allFns_of_forall m3Fns_wf)
    (mkM3Env_tableImpl mainSpec hweaken)

/-- Unconditional `ModuleOk m3Env m3Module` certifying all `204 / 204` functions of Unified
Kissat M3 against canonical UNSAT-only `m3Env` (`0` SAT model proofs). -/
theorem m3Env_moduleOk : ModuleOk m3Env m3Module :=
  mkM3Env_moduleOk fullSolveBytesSpec (fun _ _ _ _ => fullSolveBytesCoreSpec_of_spec)

/-- Unconditional `ModuleOk m3UnsatEnv m3Module` (`204/204`, concrete UNSAT witness). -/
theorem m3UnsatEnv_moduleOk : ModuleOk m3UnsatEnv m3Module :=
  mkM3Env_moduleOk fullUnsatWitnessSpec (fun _ _ _ _ => fullSolveBytesCoreSpec_of_unsatWitness)

end LeanQbe.T.Examples.Kissat.FullM3
