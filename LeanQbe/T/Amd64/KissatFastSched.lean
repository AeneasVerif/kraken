module

public import LeanQbe.T.Amd64.KissatFastSchedCert
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
import LeanQbe.T.Amd64.TargLemmas
import all Std.Sat.CNF.Basic
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat M2 Fast-Scheduler (`FullFastSched`) End-to-End SysV x64 Theorems

Lifts the `173`-function kernel-checked native compilation certificate
(`KissatFastSchedCert.schedCert`) and `schedEnv` contracts (`FullFastSchedLemmas`) to
arbitrary-`Host` SysV x64 `Eventually (step1 Host.exe)` UNSAT soundness and concrete UNSAT
non-vacuity, cleanly parameterized over `(hmok : ModuleOk schedEnv schedModule)`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFastSched

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Amd64 Kraken

/-- Compiled `LinkedCert` for `schedModule` (`173` functions) on SysV x64. -/
@[reducible] def kissatFastSched_compiled_x64 :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean schedModule :=
  KissatFastSchedCert.schedCert

private theorem solve_in_schedModule : Full.kissat_solve_bytes ∈ schedModule.fns := by
  change Full.kissat_solve_bytes ∈ schedSplicedFns
  dsimp only [schedSplicedFns]
  repeat apply List.mem_append_right
  have h128 :
      (dimacs_fns ++ Full.full1_fns ++ Full.full2_fns ++ Full.full3_fns).length = 128 := by
    t_kernel_rfl
  change Full.kissat_solve_bytes ∈
    (dimacs_fns ++ Full.full1_fns ++ Full.full2_fns ++ Full.full3_fns ++
      Full.full4_fns).drop 165
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, h128]
  exact List.mem_of_getElem? (rfl : (Full.full4_fns.drop 37)[0]? = some Full.kissat_solve_bytes)

private theorem schedSplicedFns_nodup : (schedSplicedFns.map Fn.name).Nodup := by
  have hchk := sched_acyclic
  simp only [schedModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

private theorem schedSpecTable_getElem?_lt126
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {n : Nat} (hn : n < 126) :
    (schedSpecTable mainSpec)[n]? = (fullSpecTable mainSpec)[n]? := by
  unfold schedSpecTable
  simp only [List.append_assoc, List.getElem?_append, List.length_take,
    show (fullSpecTable mainSpec).length = 166 from rfl,
    show min 126 166 = 126 from rfl, hn, ↓reduceIte, List.getElem?_take]

private theorem schedSpecTable_getElem?_tail
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) {k : Nat} (hk : k < 12) :
    (schedSpecTable mainSpec)[160 + k]? =
      ([ ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
       , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
       , ⟨"full_max_u64", [i64, i64], [i64], schedMaxU64Spec, true⟩
       , ⟨"full_probe_dticks", [i64, .bool], [i64], schedProbeDticksSpec, true⟩
       , ⟨"full_probe_tail", [i64, i64], [i64], schedProbeTailSpec, true⟩
       , ⟨"full_probe", [i64, .bool], [i64], schedProbeSpec, true⟩
       , ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩
       , ⟨"full_elim_bve", [i64, i64], [i64], schedElimBveSpec, true⟩
       , ⟨"full_eliminate", [i64, .bool], [i64], schedEliminateSpec, true⟩
       , ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩
       , ⟨"full_simplify", [i64, .bool, .bool], [i64], schedSimplifySpec, true⟩
       , ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩ ])[k]? := by
  unfold schedSpecTable
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_cons, List.length_nil, show (fullSpecTable mainSpec).length = 166 from rfl,
    show min 126 166 = 126 from rfl, show (0 : Nat) + 1 = 1 from rfl,
    show min 33 (166 - 127) = 33 from rfl,
    show (0 : Nat) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 12 from rfl]
  simp only [show ¬(160 + k < 126) by omega, show ¬(160 + k - 126 < 1) by omega,
    show ¬(160 + k - 126 - 1 < 33) by omega, show 160 + k - 126 - 1 - 33 < 12 by omega, ↓reduceIte]
  rw [show 160 + k - 126 - 1 - 33 = k by omega]

private theorem schedSpecTable_getElem?_172
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (schedSpecTable mainSpec)[172]? =
      some ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], mainSpec, true⟩ := by
  unfold schedSpecTable
  simp only [List.append_assoc, List.getElem?_append, List.length_take, List.length_drop,
    List.length_cons, List.length_nil, show (fullSpecTable mainSpec).length = 166 from rfl,
    show min 126 166 = 126 from rfl, show (0 : Nat) + 1 = 1 from rfl,
    show min 33 (166 - 127) = 33 from rfl,
    show (0 : Nat) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 12 from rfl]
  simp only [show ¬(172 < 126) by omega, show ¬(172 - 126 < 1) by omega,
    show ¬(172 - 126 - 1 < 33) by omega, show ¬(172 - 126 - 1 - 33 < 12) by omega,
    ↓reduceIte, List.getElem?_drop]
  rfl

private theorem schedEnv_names_eq (spec : Spec [i64, i64, i64, i64, i64] [i64]) :
    (schedSpecTable spec).map SpecEntry.name = schedSplicedFns.map Fn.name := by
  have h := congrArg (List.map Prod.fst) (schedSpecTable_sigs spec)
  simpa only [List.map_map, Function.comp_def] using h

/-- Whole-module `Defined` + `FnSpec` for every function in `schedModule` under `schedEnv` on
SysV x64, parameterized over `hmok : ModuleOk schedEnv schedModule`. -/
theorem sched_module_fnspec [hh : Host] (hmok : ModuleOk schedEnv schedModule) (k₀ : Nat)
    (hc : kissatFastSched_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ schedModule.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (schedEnv f.name f.as f.rs)
        (kissatFastSched_compiled_x64.bound f.name) 0 := by
  refine KissatFastSchedCert.mk_module_fnspec schedEnv (fun g hg args m Q X hs => ?_)
    (fun g _ args m Q X X' => Env.ofTable_noExit (schedSpecTable_noExit fullSolveBytesSpec)
      g.name g.as g.rs args m Q X X') k₀ hc hu hf
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hg
  exact (hmok.fnsOk pre g post hsp).2.2 args m Q X hs

section Unsat

variable [hh : Host] (hmok : ModuleOk schedEnv schedModule) (k₀ : Nat)
  (hc : kissatFastSched_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
  (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
  (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
  (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
  (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
  (hrdi : s.regs.get64 .rdi = cnf_ptr)
  (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)
  (hrdx : s.regs.get64 .rdx = work_ptr)
  (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 wlen)
  (hr8 : s.regs.get64 .r8 = fuel)
  (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
  (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
    (region (s.regs.get64 .rsp - BitVec.ofNat 64
        (kissatFastSched_compiled_x64.bound "kissat_solve_bytes"))
      (kissatFastSched_compiled_x64.bound "kissat_solve_bytes") ⋆
    cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem)
include hh hmok k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R hrdi hrsi hrdx hrcx
  hr8 hsp hmem

/-- End-to-end SysV x64 UNSAT soundness with full register, stack, and separation-logic framing
for `FullFastSched.schedModule` (`173` functions). -/
theorem sched_solve_bytes_unsat_x64 :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨
          st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64
              (kissatFastSched_compiled_x64.bound "kissat_solve_bytes"))
            (kissatFastSched_compiled_x64.bound "kissat_solve_bytes" + 8) ⋆ R)
          st.data.dmem)
      ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  have hfn := (sched_module_fnspec hmok k₀ hc hu solve_in_schedModule).2
  rcases hmem with ⟨ms, mr, u1, d1, ⟨m, mc, u2, d2, hm_in, hc0⟩, hm_r⟩
  have hspec : schedEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64]
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun r m' =>
        (r.fst = 0#64 ∨ r.fst = 10#64 ∨ r.fst = 20#64) ∧
        (r.fst = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) m')
      (fun _ _ _ _ => False) :=
    Env.ofTable_of_mem (List.mem_of_getElem? (schedSpecTable_getElem?_172 fullSolveBytesSpec))
      (by rw [schedEnv_names_eq fullSolveBytesSpec]; exact schedSplicedFns_nodup)
      ⟨cnfBytes, wlen, emp, rfl, rfl, hcfit, hwfit, by rw [sep_emp]; exact hm_in,
        fun _ _ h u' m' => by rw [sep_emp] at m'; exact ⟨h, u', m'⟩⟩
  refine eventually_weaken _ _ _ _ ?_
    (KissatFastSchedCert.solve_x64_of_fnspec hfn cnf_ptr _ work_ptr _ fuel hspec s ra R
      hrdi hrsi hrdx hrcx hr8 hsp ⟨ms, mr, u1, d1, ⟨m, mc, u2, d2, rfl, hc0⟩, hm_r⟩)
  rintro st ⟨hpc, hcal, hrsp, m', ⟨hdom, hu', hm'⟩,
    ⟨ma, mr2, u3, d3, ⟨_, ms2, u4, d4, rfl, hs⟩, hr⟩⟩
  exact ⟨hpc, hdom, hu', hcal, hrsp, ⟨ma, mr2, u3, d3, ⟨m', ms2, u4, d4, hm', hs⟩, hr⟩⟩

/-- Answer-only SysV x64 UNSAT soundness corollary for `FullFastSched.schedModule`. -/
theorem sched_solve_bytes_unsat_sound_x64 :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨
          st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label "kissat_solve_bytes"⟩ :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (sched_solve_bytes_unsat_x64 hmok k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit
      s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem)

end Unsat

private def nvEntry : SpecEntry :=
  ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64], schedUnsatWitnessSpec, true⟩

private abbrev nvEnv : Env := Env.ofTable (nvEntry :: schedSpecTable fullSolveBytesSpec)

private theorem nv_row (n : Nat) (e : SpecEntry)
    (hget : (schedSpecTable fullSolveBytesSpec)[n]? = some e)
    (hnd : ((schedSpecTable fullSolveBytesSpec).map SpecEntry.name).Nodup)
    (hne : e.name ≠ "kissat_solve_bytes") (hno : e.noExit = true)
    (hnoex : ∀ a m Q X, e.spec a m Q X → e.spec a m Q (fun _ _ _ _ => False) :=
      by intro _ _ _ _ h; exact h) :
    ∀ a m Q X, e.spec a m Q X → nvEnv e.name e.as e.rs a m Q X := by
  intro a m Q X hs
  dsimp only [nvEnv, nvEntry]
  rw [Env.ofTable_cons_ne (Ne.symm hne)]
  exact Env.ofTable_of_mem (List.mem_of_getElem? hget) hnd
    (by simp only [SpecEntry.eff, hno, ↓reduceIte]; exact hnoex a m Q X hs)

private theorem eq_of_map_nodup : ∀ {l : List Fn} (_ : (l.map Fn.name).Nodup) {a b : Fn},
    a ∈ l → b ∈ l → a.name = b.name → a = b
  | _ :: _, _, _, _, .head _, .head _, _ => rfl
  | _ :: _, h, _, _, .head _, .tail _ hb, e =>
    absurd (e.symm ▸ List.mem_map.mpr ⟨_, hb, rfl⟩) (List.nodup_cons.mp h).1
  | _ :: _, h, _, _, .tail _ ha, .head _, e =>
    absurd (e ▸ List.mem_map.mpr ⟨_, ha, rfl⟩) (List.nodup_cons.mp h).1
  | _ :: _, h, _, _, .tail _ ha, .tail _ hb, e =>
    eq_of_map_nodup (List.nodup_cons.mp h).2 ha hb e

private theorem pre_ne_solve {pre post : List Fn} {fn : Fn}
    (hsp : schedModule.fns = pre ++ fn :: post)
    (hnd : (schedSplicedFns.map Fn.name).Nodup) {g : Fn} (hg : g ∈ pre) :
    g.name ≠ "kissat_solve_bytes" := by
  intro hgn
  have hlast : (schedSplicedFns.map Fn.name).getLast? = some "kissat_solve_bytes" := by
    t_kernel_rfl
  have hm : (pre.map Fn.name ++ (fn :: post).map Fn.name).getLast? =
      some "kissat_solve_bytes" := by
    rw [← List.map_append, ← hsp]; exact hlast
  rw [List.getLast?_append] at hm
  cases he : ((fn :: post).map Fn.name).getLast?
  · simp at he
  · rw [he] at hm; cases hm
    have hnd' := List.nodup_append.mp (by rw [← List.map_append, ← hsp]; exact hnd)
    exact hnd'.2.2 _ (List.mem_map.mpr ⟨g, hg, hgn⟩) _ (List.mem_of_getLast? he) rfl

/-- Concrete SysV x64 UNSAT non-vacuity for `FullFastSched.schedModule`: assuming `hmok`,
there exists a well-formed call on `schedNvUnsatBytes` (`4096`-byte workspace, `fuel = 16`)
that deterministically returns `rax = 20#64` with `parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`. -/
theorem sched_unsat_nonvacuous_x64 [hh : Host] (hmok : ModuleOk schedEnv schedModule) (k₀ : Nat)
    (hc : kissatFastSched_compiled_x64.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      s.regs.get64 .rdi = cnf_ptr ∧
      s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length ∧
      s.regs.get64 .rdx = work_ptr ∧
      s.regs.get64 .rcx = BitVec.ofNat 64 wlen ∧
      s.regs.get64 .r8 = fuel ∧
      (s.regs.get64 .rsp + 8#64).toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        (region (s.regs.get64 .rsp - BitVec.ofNat 64
              (kissatFastSched_compiled_x64.bound "kissat_solve_bytes"))
            (kissatFastSched_compiled_x64.bound "kissat_solve_bytes") ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label "kissat_solve_bytes"⟩ := by
  have hnd : (schedSplicedFns.map Fn.name).Nodup := schedSplicedFns_nodup
  have hnd_tbl : ((schedSpecTable fullSolveBytesSpec).map SpecEntry.name).Nodup := by
    rw [schedEnv_names_eq fullSolveBytesSpec]; exact hnd
  have hfn : x64Target.FnSpec hh "kissat_solve_bytes"
      (nvEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64])
      (kissatFastSched_compiled_x64.bound "kissat_solve_bytes") 0 := by
    refine (KissatFastSchedCert.mk_module_fnspec nvEnv (fun g hg args m Q X hs => ?_)
      (fun g _ args m Q X X' => Env.ofTable_noExit (fun e he =>
        List.mem_cons.mp he |>.elim (fun h => h ▸ rfl)
          (schedSpecTable_noExit fullSolveBytesSpec e)) g.name g.as g.rs args m Q X X')
      k₀ hc hu solve_in_schedModule).2
    by_cases hnm : g.name = "kissat_solve_bytes"
    · have heq := eq_of_map_nodup hnd hg solve_in_schedModule hnm
      subst heq
      dsimp only [Full.kissat_solve_bytes] at args Q hs
      dsimp only [nvEnv, nvEntry] at hs
      rw [Env.ofTable_cons_self] at hs
      exact sched_kissat_solve_bytes_core_wp nvEnv
        (nv_row 41 ⟨"full_init_state", [i64, i64, i64, i64, i64], [.bool], fullInitStateSpec,
          true⟩ ((schedSpecTable_getElem?_lt126 _ (by omega)).trans rfl) hnd_tbl (by decide) rfl)
        (nv_row 44 ⟨"full_parse_body", [i64, i64], [i64], fullParseBodySpec, true⟩
          ((schedSpecTable_getElem?_lt126 _ (by omega)).trans rfl) hnd_tbl (by decide) rfl)
        (nv_row 169 ⟨"full_preprocess", [i64], [i64], fullPreprocessSpec, true⟩
          ((schedSpecTable_getElem?_tail _ (k := 9) (by omega)).trans rfl) hnd_tbl
          (by decide) rfl)
        (nv_row 171 ⟨"full_search", [i64], [i64], fullSearchSpec, true⟩
          ((schedSpecTable_getElem?_tail _ (k := 11) (by omega)).trans rfl) hnd_tbl
          (by decide) rfl)
        (nv_row 96 ⟨"full_extend", [i64], [], fullExtendSpec, true⟩
          ((schedSpecTable_getElem?_lt126 _ (by omega)).trans rfl) hnd_tbl (by decide) rfl)
        (nv_row 7 ⟨"kissat_check_model", [i64, i64, i64, i64, i64], [i64],
          kissatCheckModelExactSpec, true⟩
          ((schedSpecTable_getElem?_lt126 _ (by omega)).trans rfl) hnd_tbl (by decide) rfl)
        args m Q X (fullSolveBytesCoreSpec_of_schedUnsatWitness hs)
    · obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hg
      obtain ⟨hwf, hca, hbd⟩ := hmok.fnsOk pre g post hsp
      dsimp only [nvEnv, nvEntry] at hs
      rw [Env.ofTable_cons_ne (Ne.symm hnm)] at hs
      refine wp_env_agree_of_callsOk (hwf _ (fun _ => Unit) _ (fun _ => Unit) args (Tup.units g.as))
        hca (fun fnm _ _ hc' _ _ _ _ hf => ?_) m (hbd args m Q X hs)
      have hne : fnm ≠ "kissat_solve_bytes" := by
        rcases List.mem_append.mp hc' with h | h
        · obtain ⟨z, hz, hs'⟩ := List.mem_map.mp h; cases hs'; exact pre_ne_solve hsp hnd hz
        · simp [schedModule] at h
      dsimp only [nvEnv, nvEntry]; rw [Env.ofTable_cons_ne (Ne.symm hne)]; exact hf
  let b := kissatFastSched_compiled_x64.bound "kissat_solve_bytes"
  let bs := schedPayload schedNvUnsatBytes
  let s := x64InitState b bs (as := [i64, i64, i64, i64, i64])
    (schedNvCnfPtr, BitVec.ofNat 64 schedNvUnsatBytes.length,
      schedNvWorkPtr schedNvUnsatBytes, 4096#64, 16#64, ())
  have h1 := x64InitMem_entry b 0x1234 bs (by decide) (by
    rw [show bs = schedNvUnsatBytes ++ List.replicate 4096 0 from rfl,
      List.length_append, List.length_replicate]; decide)
  change (Eq (bs.At 0x1000#64) ⋆ x64Target.Entry 0x0ff8#64 0x1234 b ⋆ emp) s.dmem at h1
  rw [show bs = schedNvUnsatBytes ++ List.replicate 4096 0 from rfl,
    Mem.At_append_sep schedNvUnsatBytes (List.replicate 4096 0) 0x1000#64
      (by rw [List.length_replicate]; decide), sep_assoc] at h1
  have hdm : (bytes schedNvCnfPtr schedNvUnsatBytes ⋆
      region (schedNvWorkPtr schedNvUnsatBytes) 4096 ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆
        cell64 (s.regs.get64 .rsp) (0x1234 : Int64).toBitVec) ⋆ emp) s.dmem := by
    rw [show s.regs.get64 .rsp = 0x0ff8#64 from rfl]
    have h3 := sep_mono_mid (fun _ h => show region (schedNvWorkPtr schedNvUnsatBytes) 4096 _ from
      ⟨List.replicate 4096 0, List.length_replicate, h.symm⟩) h1
    dsimp only [Target.Entry, x64Target, x64FrameSpec] at h3
    simp only [sep_emp] at h3 ⊢; exact h3
  have hhsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0 := by
    rw [show s.regs.get64 .rsp = 0x0ff8#64 from rfl]; decide
  refine ⟨schedNvCnfPtr, schedNvWorkPtr schedNvUnsatBytes, 16#64, schedNvUnsatBytes, 4096,
    s, 0x1234, emp, by decide, by decide, rfl, rfl, rfl, rfl, rfl, hhsp, hdm, ?_⟩
  rcases hdm with ⟨ms, mr, u1, d1, ⟨m, mc, u2, d2, hm_in, hc0⟩, hm_r⟩
  have hspec : nvEnv "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64]
      (schedNvCnfPtr, BitVec.ofNat 64 schedNvUnsatBytes.length,
        schedNvWorkPtr schedNvUnsatBytes, 4096#64, 16#64, ()) m
      (fun r _ => r.fst = 20#64) (fun _ _ _ _ => False) := by
    dsimp only [nvEnv, nvEntry]
    rw [Env.ofTable_cons_self]
    exact ⟨emp, by decide, by decide, rfl, rfl, rfl, by decide, by decide,
      by rw [sep_emp]; exact hm_in, fun _ _ _ => rfl⟩
  have hev := KissatFastSchedCert.solve_x64_of_fnspec hfn schedNvCnfPtr _
    (schedNvWorkPtr schedNvUnsatBytes) _ 16#64 hspec s 0x1234 emp
    rfl rfl rfl rfl rfl hhsp ⟨ms, mr, u1, d1, ⟨m, mc, u2, d2, rfl, hc0⟩, hm_r⟩
  exact eventually_weaken _ _ _ _ (fun _ ⟨hpc, _, _, _, h20, _⟩ =>
    ⟨hpc, h20, schedNvUnsatCnf, parseDimacs_schedNvUnsatBytes, by
      intro a; cases ha1 : a 1 <;>
        simp [schedNvUnsatCnf, CNF.eval_add, CNF.eval_empty, CNF.Clause.ofLiterals,
          CNF.Clause.eval_add, CNF.Clause.eval_empty, ha1]⟩) hev

end LeanQbe.T.Amd64.KissatFastSched
