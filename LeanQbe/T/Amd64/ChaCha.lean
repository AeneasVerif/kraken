module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.ChaCha
public import LeanQbe.T.MainSplice
import all Kraken.Mem
import all Kraken.Separation
meta import Lean
meta import LeanQbe.T.MainSplice
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.ChaCha

/-!
# ChaCha20 Block (`v4i32` SIMD) on SysV x64 (`T14`)

Instantiates `chacha20Module` (`chacha20Block`) on `x64Target` (`x64LegalTarget`, `x64Layout`,
`x64LabelClean`) with:
* external hint splicing (`chacha20Hints`) via `splice_module_hints`;
* single-kernel-reduction compilation check (`t_kernel_rfl`, default 200k heartbeats, zero spills);
* `chacha20_module_fnspec` and closed Kraken x64 correctness theorem `chacha20Block_x64_correct`;
* concrete RFC 8439 §2.3.2 execution witness `rfc8439_vector_x64_nonvacuous` verifying the exact
  16-word / 64-byte output in `dmem` via `x64Init`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.ChaCha

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.ChaCha LeanQbe.T.Amd64 Kraken

splice_module_hints chacha20Hints (x64Target.toIsa) x64LegalTarget chacha20Module.fns

/-! ## 1. Compiled Kernel Certificate & Source Support -/

theorem compiled_check :
    checkCompile x64Target x64Layout x64LegalTarget [] [] 0
      chacha20Module.fns chacha20Hints 2048 = true := by
  t_kernel_rfl

/-- Single kernel evaluation of `chacha20Block` for SysV x64 (`v4i32` SIMD, `bound = 8`). -/
def compiled : Compiled x64Target x64LegalTarget [] [] 0 chacha20Module.fns chacha20Hints 2048 :=
  compileChecked x64Target x64Layout x64LegalTarget x64LabelClean
    [] [] 0 chacha20Module.fns chacha20Hints 2048 compiled_check

private theorem chacha20Fns_supportsSource_all :
    chacha20Module.fns.all (fun f => (f.earlyOpt).body.supportsSource x64LegalTarget) = true := by
  t_kernel_rfl

theorem chacha20Fns_supportsSource :
    ∀ f ∈ chacha20Module.fns, (f.earlyOpt).body.supportsSource x64LegalTarget = true :=
  fun f hf => List.all_eq_true.mp chacha20Fns_supportsSource_all f hf

/-! ## 2. Generic `FnSpec` and Closed Kraken x64 Theorem -/

section Generic
variable [hh : Host]

/-- Closed `FnSpec` for every function in `chacha20Module` on `x64Target`. -/
theorem chacha20_module_fnspec (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ chacha20Module.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (chacha20Env f.name f.as f.rs)
        (compiled.bound f.name) 0 := by
  obtain ⟨hdef, hspec⟩ := compiled.fnSpec chacha20Module rfl hh chacha20Env k₀ hc hu
    chacha20Module_checkAcyclic
    (fun g hg => by
      simp only [chacha20Module, List.mem_singleton] at hg; subst hg; exact chacha20Block_wf)
    chacha20Fns_supportsSource
    (fun g hg => by
      simp only [chacha20Module, List.mem_singleton] at hg; subst hg
      exact chacha20Block_correct chacha20Env)
    (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    (fun _ h => nomatch h) hf
  have hmem := hf
  simp only [chacha20Module, List.mem_singleton] at hmem; subst hmem
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq_noExit rfl rfl
    (List.mem_append_left _ (List.mem_map_of_mem hf)) (fun _ _ _ _ _ h => h) hspec⟩

/-- End-to-end correctness of compiled `chacha20Block` on Kraken x64. -/
theorem chacha20Block_x64_correct (k₀ : Nat)
    (hc : compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (out inp : BitVec 64) (init : State) (old : List Row) (hold : old.length = 4)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout : s.regs.get64 .rdi = out) (hinp : s.regs.get64 .rsi = inp)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (array (t := v4i32) out old ⋆ array (t := v4i32) inp init.toRows) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "chacha20Block"))
          (compiled.bound "chacha20Block") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (array (t := v4i32) out (rfcChaCha20Core init).toRows ⋆
            array (t := v4i32) inp init.toRows) ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "chacha20Block"))
            (compiled.bound "chacha20Block" + 8) ⋆ R))
      ⟨s, Labels.label "chacha20Block"⟩ := by
  have hargs : x64Target.ArgsIn (as := [i64, i64]) (out, inp, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using hout⟩ (.cons ⟨by decide, by simpa using hinp⟩ .nil)⟩
  obtain ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, hm, hf⟩, hmR⟩ := hmem
  have hmEq : s.dmem =⋆ Eq m ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (compiled.bound "chacha20Block"))
          (compiled.bound "chacha20Block") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R :=
    ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, rfl, hf⟩, hmR⟩
  have hfn : x64Target.FnSpec hh "chacha20Block" chacha20BlockSpec
      (compiled.bound "chacha20Block") 0 :=
    (chacha20_module_fnspec k₀ hc hu List.mem_cons_self).2
  have hspec : chacha20BlockSpec (out, inp, ()) m
      (fun _ m' => (array (t := v4i32) out (rfcChaCha20Core init).toRows ⋆
        array (t := v4i32) inp init.toRows) m')
      (fun _ _ _ _ => False) :=
    ⟨init, old, emp, hold, by rw [sep_emp]; exact sep_ac hm,
      fun _ hm' => by rw [sep_emp] at hm'; exact sep_ac hm'⟩
  refine eventually_weaken _ _ _ _ ?_ (x64_of_returns hfn hspec s ra R hargs hsp hmEq)
  rintro st ⟨hpc, hcs, hsp', _, m', hP, _, hm'⟩
  exact ⟨hpc, hcs, hsp', sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP)) hm'⟩

end Generic

/-! ## 3. Concrete RFC 8439 §2.3.2 Witness in `compiled.host` -/

private theorem array_eq_bytesOf {t : Ty} (a : BitVec 64) (xs : List (Val t))
    (h : t.bytes * xs.length ≤ 2 ^ 64) {m : Mem 64} (hm : array a xs m) :
    m = (bytesOf xs).At a := by
  induction xs generalizing a m with
  | nil =>
    simp only [array_nil, bytesOf, List.flatMap_nil] at hm ⊢
    have hm0 : m = ∅ := hm; subst hm0
    apply ExtHashMap.ext_getElem?; intro k; simp [List.At]
  | cons x xs ih =>
    rw [array_cons] at hm
    obtain ⟨m1, m2, rfl, hd, h1, h2⟩ := hm
    have h1' : m1 = (Int.toBytes t.bytes ((toBits t x).setWidth (8 * t.bytes)).toInt).At a :=
      h1.symm
    have h2' : m2 = (bytesOf xs).At (a + BitVec.ofNat 64 t.bytes) :=
      ih _ (by simp only [List.length_cons, Nat.mul_succ] at h; omega) h2
    have hl : (Int.toBytes t.bytes ((toBits t x).setWidth (8 * t.bytes)).toInt).length +
        (bytesOf xs).length ≤ 2 ^ 64 := by
      simp only [Int.toBytes_length, bytesOf_length]
      simp only [List.length_cons, Nat.mul_succ] at h; omega
    have hat := List.At_append
      (Int.toBytes t.bytes ((toBits t x).setWidth (8 * t.bytes)).toInt) (bytesOf xs) a hl
    rw [Int.toBytes_length] at hat
    rw [h1', h2', ← hat]
    rfl

private theorem mapM_id_map_some {α : Type} :
    ∀ xs : List α, (xs.map some).mapM id = some xs
  | [] => rfl
  | x :: xs => by simp [mapM_id_map_some xs]

private theorem loadBytes_sep_At {a : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (hlen : bs.length ≤ 2 ^ 64)
    (hm : (Eq (bs.At a) ⋆ R) m) :
    m.loadBytes a bs.length = some bs := by
  obtain ⟨m1, m2, hm_eq, hd, rfl, _⟩ := hm
  subst hm_eq
  unfold Mem.loadBytes
  have hmap : (List.range bs.length).map
      (fun i => (bs.At a ∪ m2).get? (a + .ofNat 64 i)) = bs.map some := by
    apply List.ext_getElem (by simp)
    intro i hi1 hi2
    simp only [List.length_map, List.length_range] at hi1
    simp only [List.getElem_map, List.getElem_range]
    have hmem : a + BitVec.ofNat 64 i ∈ bs.At a :=
      (mem_At_iff bs a _).mpr ⟨i, hi1, rfl⟩
    have hnot : a + BitVec.ofNat 64 i ∉ m2 := fun h2 =>
      (ExtHashMap.eq_empty_iff_forall_not_mem.mp hd _)
        (by rw [ExtHashMap.inter_eq, ExtHashMap.mem_inter_iff]; exact ⟨hmem, h2⟩)
    rw [ExtHashMap.get?_eq_getElem?, ExtHashMap.getElem?_union,
      ExtHashMap.getElem?_eq_none hnot, Option.none_or, ← ExtHashMap.get?_eq_getElem?]
    rw [get?_At_idx bs a i (Nat.lt_of_lt_of_le hi1 hlen) hlen, List.getElem?_eq_getElem hi1]
  rw [← ExtHashMap.union_eq] at hmap
  rw [hmap, mapM_id_map_some]

private theorem rfc8439_expected_bytes_eq_bytesOf :
    bytesOf (t := v4i32) (rfcChaCha20Core rfc8439_test_init).toRows = rfc8439_expected_bytes := by
  decide

abbrev chachaHost : Host := compiled.host
attribute [local instance] chachaHost

def chachaOut0 : List Row := List.replicate 4 (mkRow 0#32 0#32 0#32 0#32)
def chachaInitBytes : List UInt8 := bytesOf (t := v4i32) (chachaOut0 ++ rfc8439_test_init.toRows)

private theorem chachaInitBytes_length : chachaInitBytes.length ≤ 8192 := by
  simp [chachaInitBytes, bytesOf_length, chachaOut0, State.toRows, Ty.bytes, Ty.size]

def chachaState0 : MachineData :=
  x64Init.initState (as := [i64, i64]) (compiled.bound "chacha20Block") chachaInitBytes
    (0x1000#64, 0x1040#64, ())

/-- Concrete RFC 8439 §2.3.2 execution witness of `chacha20Block` in `compiled.host`, verifying
both the 16-word separation-logic state and the exact 64-byte output in `dmem`. -/
theorem rfc8439_vector_x64_nonvacuous :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        st.data.dmem.loadBytes 0x1000#64 64 = some rfc8439_expected_bytes ∧
        ∃ res : State,
          res.toWords = rfc8439_expected_words ∧ res.toBytes = rfc8439_expected_bytes ∧
          (st.data.dmem =⋆
            (array (t := v4i32) 0x1000#64 res.toRows ⋆
              array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows) ⋆
            region (0x0ff8#64 - BitVec.ofNat 64 (compiled.bound "chacha20Block"))
              (compiled.bound "chacha20Block" + 8) ⋆ emp))
      ⟨chachaState0, Labels.label "chacha20Block"⟩ := by
  have hfn : x64Target.FnSpec chachaHost "chacha20Block" chacha20BlockSpec
      (compiled.bound "chacha20Block") 0 :=
    (chacha20_module_fnspec 0 compiled.code_infix_host compiled.labelsUnique
      List.mem_cons_self).2
  have hm0 : (array (t := v4i32) 0x1000#64 chachaOut0 ⋆
      array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows)
      (chachaInitBytes.At 0x1000#64) := by
    have ha := array_bytes (t := v4i32) 0x1000#64 (chachaOut0 ++ rfc8439_test_init.toRows)
      (by simp [chachaOut0, State.toRows, Ty.bytes, Ty.size])
    rw [array_append] at ha
    simpa only [chachaInitBytes, chachaOut0, List.length_replicate, Ty.bytes, Ty.size,
      Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd]
      using ha
  have hspec : chacha20BlockSpec (0x1000#64, 0x1040#64, ()) (chachaInitBytes.At 0x1000#64)
      (fun _ m' =>
        (array (t := v4i32) 0x1000#64 (rfcChaCha20Core rfc8439_test_init).toRows ⋆
          array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows) m')
      (fun _ _ _ _ => False) :=
    ⟨rfc8439_test_init, chachaOut0, emp, rfl, by rw [sep_emp]; exact sep_ac hm0,
      fun _ hm' => by rw [sep_emp] at hm'; exact sep_ac hm'⟩
  refine x64Init.run_fnSpec compiled hfn chachaInitBytes (0x1000#64, 0x1040#64, ())
    chachaInitBytes_length rfl hspec ?_
  rintro st (⟨hpc, _, m', hP, _, hm'⟩ | ⟨_, _, _, _, hx, _⟩)
  · have hdmem : st.data.dmem =⋆
        (array (t := v4i32) 0x1000#64 (rfcChaCha20Core rfc8439_test_init).toRows ⋆
          array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows) ⋆
        region (0x0ff8#64 - BitVec.ofNat 64 (compiled.bound "chacha20Block"))
          (compiled.bound "chacha20Block" + 8) ⋆ emp := by
      simpa only [Target.Exit, x64Target, x64FrameSpec, x64Frame, x64Init] using
        sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP)) hm'
    have hdmem_ac : (array (t := v4i32) 0x1000#64 (rfcChaCha20Core rfc8439_test_init).toRows ⋆
        (array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows ⋆
          region (0x0ff8#64 - BitVec.ofNat 64 (compiled.bound "chacha20Block"))
            (compiled.bound "chacha20Block" + 8) ⋆ emp)) st.data.dmem := sep_ac hdmem
    have hflat : (Eq (rfc8439_expected_bytes.At 0x1000#64) ⋆
        (array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows ⋆
          region (0x0ff8#64 - BitVec.ofNat 64 (compiled.bound "chacha20Block"))
            (compiled.bound "chacha20Block" + 8) ⋆ emp)) st.data.dmem := by
      refine sep_mono (fun _ h => ?_) hdmem_ac
      rw [← rfc8439_expected_bytes_eq_bytesOf]
      exact (array_eq_bytesOf 0x1000#64 _ (by simp [State.toRows, Ty.bytes, Ty.size]) h).symm
    have hload := loadBytes_sep_At (by decide) hflat
    refine ⟨hpc, hload, rfcChaCha20Core rfc8439_test_init,
      rfc8439_test_vector_words, rfc8439_test_vector_bytes, hdmem⟩
  · exact hx.elim

end LeanQbe.T.Amd64.ChaCha
