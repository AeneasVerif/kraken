module

public import LeanQbe.T.BenchmarkCertKit
public import LeanQbe.T.Examples.ChaCha
public import LeanQbe.T.Examples.Bignum
public import LeanQbe.T.Examples.UnionFindLemmas
public import LeanQbe.T.Examples.LitmusProgsLemmas
public import LeanQbe.T.Examples.LinkRec
public import LeanQbe.T.Examples.LratBytesLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.FlatLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Target-Parametric Benchmarks, `FnSpec`s, and Execution Witnesses (`Examples.BenchmarkCertKit`)

Arch-neutral shared data, pure lemmas, spec witnesses, `FnSpec` instantiations, and `TargetInit`
non-vacuous execution proofs for `ChaCha`, `Bignum`, `UnionFind`, `Litmus`, and `LinkRec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.BenchmarkCertKit

open Std Std.ExtHashMap Std.Sat
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.BenchmarkCertKit LeanQbe.T.LinkRec Kraken

/-! ## 1. ChaCha20 (`chacha20Module`) -/

section ChaChaKit

open LeanQbe.T.Examples.ChaCha

theorem rfc8439_expected_bytes_eq_bytesOf :
    bytesOf (t := v4i32) (rfcChaCha20Core rfc8439_test_init).toRows =
      rfc8439_expected_bytes := by
  decide

@[expose] def chachaOut0 : List Row := List.replicate 4 (mkRow 0#32 0#32 0#32 0#32)

@[expose] def chachaInitBytes : List UInt8 :=
  bytesOf (t := v4i32) (chachaOut0 ++ rfc8439_test_init.toRows)

theorem chachaInitBytes_length : chachaInitBytes.length ≤ 8192 := by
  simp [chachaInitBytes, bytesOf_length, chachaOut0, State.toRows, Ty.bytes, Ty.size]

theorem chacha20_module_fnspec_gen {T : Target} {lt : LegalTarget}
    {hints : List T.toIsa.Hints}
    (M : Compiled T lt [] [] 0 chacha20Module.fns hints 2048)
    (hh : T.mach.Host)
    (hi64 : lt.legalSig [i64] = [i64])
    (hsupp : ∀ f ∈ chacha20Module.fns, (f.earlyOpt).body.supportsSource lt = true)
    (k₀ : Nat) (hc : M.code.IsInfixAt (T.mach.prog hh) k₀) (hu : T.LabelsUnique hh)
    {f : Fn} (hf : f ∈ chacha20Module.fns) :
    T.Defined hh f.name ∧
      T.FnSpec hh f.name (chacha20Env f.name f.as f.rs) (M.bound f.name) 0 := by
  have hmem := hf
  simp only [chacha20Module, List.mem_singleton] at hmem; subst hmem
  exact M.fnSpec_noExit_id chacha20Module rfl hh chacha20Env k₀ hc hu
    chacha20Module_checkAcyclic
    (fun g hg => by
      simp only [chacha20Module, List.mem_singleton] at hg; subst hg; exact chacha20Block_wf)
    hsupp
    (fun g hg => by
      simp only [chacha20Module, List.mem_singleton] at hg; subst hg
      exact chacha20Block_correct chacha20Env)
    hf (legalSig_two_i64 hi64) rfl (fun _ _ _ _ _ h => h)

theorem chacha20_spec_ok {out inp : BitVec 64} {init : State} {old : List Row}
    (hold : old.length = 4) {m : Mem 64}
    (hm : (array (t := v4i32) out old ⋆ array (t := v4i32) inp init.toRows) m) :
    chacha20BlockSpec (out, inp, ()) m
      (fun _ m' => (array (t := v4i32) out (rfcChaCha20Core init).toRows ⋆
        array (t := v4i32) inp init.toRows) m')
      (fun _ _ _ _ => False) :=
  ⟨init, old, emp, hold, by rw [sep_emp]; exact sep_ac hm,
    fun _ hm' => by rw [sep_emp] at hm'; exact sep_ac hm'⟩

theorem rfc8439_vector_target_nonvacuous {T : Target} (I : TargetInit T 2048 8192)
    {lt : LegalTarget} {hints : List T.toIsa.Hints}
    (M : Compiled T lt [] [] 0 chacha20Module.fns hints 2048)
    (hfn : T.FnSpec M.host "chacha20Block" chacha20BlockSpec (M.bound "chacha20Block") 0)
    (hargs : (T.toIsa.assignArgs [i64, i64]).isSome = true) :
    Eventually (T.mach.step M.host)
      (fun st => T.mach.pc st = I.ra0 ∧
        (T.mach.mem (T.mach.data st)).loadBytes 0x1000#64 64 = some rfc8439_expected_bytes ∧
        ∃ res : State,
          res.toWords = rfc8439_expected_words ∧ res.toBytes = rfc8439_expected_bytes ∧
          (T.mach.mem (T.mach.data st) =⋆
            (array (t := v4i32) 0x1000#64 res.toRows ⋆
              array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows) ⋆
            T.Exit I.sp0 (M.bound "chacha20Block") ⋆ emp))
      (T.mach.mkState (I.initState (M.bound "chacha20Block") chachaInitBytes
          (as := [i64, i64]) (0x1000#64, 0x1040#64, ()))
        (T.mach.labelAddr M.host "chacha20Block")) := by
  have hm0 : (array (t := v4i32) 0x1000#64 chachaOut0 ⋆
      array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows)
      (chachaInitBytes.At 0x1000#64) := by
    have ha := array_bytes (t := v4i32) 0x1000#64 (chachaOut0 ++ rfc8439_test_init.toRows)
      (by simp [chachaOut0, State.toRows, Ty.bytes, Ty.size])
    rw [array_append] at ha
    simpa only [chachaInitBytes, chachaOut0, List.length_replicate, Ty.bytes, Ty.size,
      Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd]
      using ha
  refine I.run_fnSpec M hfn chachaInitBytes (0x1000#64, 0x1040#64, ())
    chachaInitBytes_length hargs (chacha20_spec_ok rfl hm0) ?_
  rintro st (⟨hpc, _, m', hP, _, hm'⟩ | ⟨_, _, _, _, hx, _⟩)
  · have hdmem : T.mach.mem (T.mach.data st) =⋆
        (array (t := v4i32) 0x1000#64 (rfcChaCha20Core rfc8439_test_init).toRows ⋆
          array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows) ⋆
        T.Exit I.sp0 (M.bound "chacha20Block") ⋆ emp :=
      sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP)) hm'
    have hdmem_ac : (array (t := v4i32) 0x1000#64 (rfcChaCha20Core rfc8439_test_init).toRows ⋆
        (array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows ⋆
          T.Exit I.sp0 (M.bound "chacha20Block") ⋆ emp))
        (T.mach.mem (T.mach.data st)) := sep_ac hdmem
    have hflat : (Eq (rfc8439_expected_bytes.At 0x1000#64) ⋆
        (array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows ⋆
          T.Exit I.sp0 (M.bound "chacha20Block") ⋆ emp))
        (T.mach.mem (T.mach.data st)) := by
      refine sep_mono (fun _ h => ?_) hdmem_ac
      rw [← rfc8439_expected_bytes_eq_bytesOf]
      exact (array_eq_bytesOf 0x1000#64 _ (by simp [State.toRows, Ty.bytes, Ty.size]) h).symm
    have hload := loadBytes_sep_At (by decide) hflat
    refine ⟨hpc, hload, rfcChaCha20Core rfc8439_test_init,
      rfc8439_test_vector_words, rfc8439_test_vector_bytes, hdmem⟩
  · exact hx.elim

end ChaChaKit

/-! ## 2. Curve25519 Bignum Kernels -/

section BignumKit

open LeanQbe.T.Examples.Bignum

theorem array64_split3 (a : BitVec 64) (xs ys zs : List (BitVec 64))
    (h : 8 * (xs ++ ys ++ zs).length ≤ 2 ^ 64) :
    (array64 a xs ⋆ array64 (a + BitVec.ofNat 64 (8 * xs.length)) ys ⋆
      array64 (a + BitVec.ofNat 64 (8 * (xs.length + ys.length))) zs)
      ((bytes64 (xs ++ ys ++ zs)).At a) := by
  have ha := array64_bytes a (xs ++ ys ++ zs) h
  rwa [array64_append, array64_append, List.length_append] at ha

@[expose] def nvMulA : List (BitVec 64) := [p0, p1, p2, p3]
@[expose] def nvMulB : List (BitVec 64) := [2#64, 0#64, 0#64, 1#64]
@[expose] def nvMulOut0 : List (BitVec 64) := List.replicate 8 0#64
@[expose] def nvMulBytes : List UInt8 := bytes64 (nvMulOut0 ++ nvMulA ++ nvMulB)

theorem nvMulBytes_length : nvMulBytes.length ≤ 8192 := by
  simp [nvMulBytes, bytes64_length, nvMulOut0, nvMulA, nvMulB]

@[expose] def nvAddA : List (BitVec 64) := [p0 - 1#64, p1, p2, p3]
@[expose] def nvAddB : List (BitVec 64) := [20#64, 0#64, 0#64, 0#64]
@[expose] def nv4Out0 : List (BitVec 64) := List.replicate 4 0#64
@[expose] def nvAddBytes : List UInt8 := bytes64 (nv4Out0 ++ nvAddA ++ nvAddB)

theorem nvAddBytes_length : nvAddBytes.length ≤ 8192 := by
  simp [nvAddBytes, bytes64_length, nv4Out0, nvAddA, nvAddB]

theorem p25519_gt_100 : 100 < p25519 := by
  unfold p25519
  have h1 : 2 ^ 64 ≤ (2 : Nat) ^ 255 := Nat.pow_le_pow_right (by decide) (by decide)
  have h2 : 119 < 2 ^ 64 := by decide
  omega

theorem nvAddA_val : limbsVal nvAddA = p25519 - 1 := by
  have hp := limbsVal_p25519
  have h0 : (p0 - 1#64).toNat + 1 = p0.toNat := by decide
  have hsum : limbsVal nvAddA + 1 = p25519 := by
    rw [← hp]
    simp only [nvAddA, limbsVal4_eq]
    omega
  omega

theorem nvAddB_val : limbsVal nvAddB = 20 := by
  simp [nvAddB, limbsVal]

theorem nvAdd_mod : (limbsVal nvAddA + limbsVal nvAddB) % p25519 = 19 := by
  rw [nvAddA_val, nvAddB_val]
  have hgt := p25519_gt_100
  rw [show p25519 - 1 + 20 = 19 + p25519 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

@[expose] def nvSubA : List (BitVec 64) := [5#64, 0#64, 0#64, 0#64]
@[expose] def nvSubB : List (BitVec 64) := [25#64, 0#64, 0#64, 0#64]
@[expose] def nvSubBytes : List UInt8 := bytes64 (nv4Out0 ++ nvSubA ++ nvSubB)

theorem nvSubBytes_length : nvSubBytes.length ≤ 8192 := by
  simp [nvSubBytes, bytes64_length, nv4Out0, nvSubA, nvSubB]

theorem nvSubA_val : limbsVal nvSubA = 5 := by simp [nvSubA, limbsVal]
theorem nvSubB_val : limbsVal nvSubB = 25 := by simp [nvSubB, limbsVal]

theorem nvSub_val :
    (if limbsVal nvSubB ≤ limbsVal nvSubA then limbsVal nvSubA - limbsVal nvSubB
     else limbsVal nvSubA + p25519 - limbsVal nvSubB) = p25519 - 20 := by
  rw [nvSubA_val, nvSubB_val]; have := p25519_gt_100; simp; omega

theorem mul4x4_spec_ok {out pa pb : BitVec 64} {as bs out0 : List (BitVec 64)}
    (has : as.length = 4) (hbs : bs.length = 4) (hout : out0.length = 8) {m : Mem 64}
    (hm : (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) m) :
    mul4x4Spec (out, pa, pb, ()) m
      (fun _ m' => ∃ rs : List (BitVec 64), rs.length = 8 ∧
        limbsVal rs = limbsVal as * limbsVal bs ∧
        (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs) m')
      (fun _ _ _ _ => False) :=
  ⟨as, bs, out0, emp, has, hbs, hout, by rw [sep_emp]; exact sep_ac hm,
    fun rs m' hrs hmul hm' => ⟨rs, hrs, hmul, by rw [sep_emp] at hm'; exact sep_ac hm'⟩⟩

theorem addMod25519_spec_ok {out pa pb : BitVec 64} {as bs out0 : List (BitVec 64)}
    (has : as.length = 4) (hbs : bs.length = 4) (hout : out0.length = 4)
    (ha_lt : limbsVal as < p25519) (hb_lt : limbsVal bs < p25519) {m : Mem 64}
    (hm : (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) m) :
    addMod25519Spec (out, pa, pb, ()) m
      (fun _ m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧
        limbsVal rs = (limbsVal as + limbsVal bs) % p25519 ∧ limbsVal rs < p25519 ∧
        (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs) m')
      (fun _ _ _ _ => False) :=
  ⟨as, bs, out0, emp, has, hbs, hout, ha_lt, hb_lt, by rw [sep_emp]; exact sep_ac hm,
    fun rs m' hrs hmod hlt hm' =>
      ⟨rs, hrs, hmod, hlt, by rw [sep_emp] at hm'; exact sep_ac hm'⟩⟩

theorem subMod25519_spec_ok {out pa pb : BitVec 64} {as bs out0 : List (BitVec 64)}
    (has : as.length = 4) (hbs : bs.length = 4) (hout : out0.length = 4)
    (ha_lt : limbsVal as < p25519) (hb_lt : limbsVal bs < p25519) {m : Mem 64}
    (hm : (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) m) :
    subMod25519Spec (out, pa, pb, ()) m
      (fun _ m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧
        limbsVal rs = (if limbsVal bs ≤ limbsVal as then limbsVal as - limbsVal bs
                       else limbsVal as + p25519 - limbsVal bs) ∧
        limbsVal rs < p25519 ∧
        (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs) m')
      (fun _ _ _ _ => False) :=
  ⟨as, bs, out0, emp, has, hbs, hout, ha_lt, hb_lt, by rw [sep_emp]; exact sep_ac hm,
    fun rs m' hrs hsub hlt hm' =>
      ⟨rs, hrs, hsub, hlt, by rw [sep_emp] at hm'; exact sep_ac hm'⟩⟩

theorem bignum_single_fnspec_gen {T : Target} {lt : LegalTarget} {f : Fn}
    {hints : List T.toIsa.Hints}
    (M : Compiled T lt [] [] 0 [f] hints 2048) (hh : T.mach.Host)
    (hacyc : ({ fns := [f], externs := [], exits := [] } : Module).checkAcyclic = true)
    (hwf : f.Wf) (hsupp_mem : f ∈ [mul4x4Fn, addMod25519Fn, subMod25519Fn])
    (hsuppAll : ∀ g ∈ [mul4x4Fn, addMod25519Fn, subMod25519Fn],
      (g.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ xs m Q X, bignumEnv f.name f.as f.rs xs m Q X → Func.wp bignumEnv f.body xs m Q X)
    (k₀ : Nat) (hc : M.code.IsInfixAt (T.mach.prog hh) k₀) (hu : T.LabelsUnique hh)
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X',
      bignumEnv f.name f.as f.rs args m Q X → bignumEnv f.name f.as f.rs args m Q X') :
    T.Defined hh f.name ∧ T.FnSpec hh f.name (bignumEnv f.name f.as f.rs) (M.bound f.name) 0 :=
  single_fnspec_gen M hh bignumEnv hacyc hwf (hsuppAll f hsupp_mem) hwp k₀ hc hu has hrs hnoex

theorem nvMul_spec_ok :
    mul4x4Spec (0x1000#64, 0x1040#64, 0x1060#64, ()) (nvMulBytes.At 0x1000#64)
      (fun _ m' => ∃ rs : List (BitVec 64), rs.length = 8 ∧
        limbsVal rs = limbsVal nvMulA * limbsVal nvMulB ∧
        (array64 0x1000#64 rs ⋆ array64 0x1040#64 nvMulA ⋆ array64 0x1060#64 nvMulB) m')
      (fun _ _ _ _ => False) := by
  refine mul4x4_spec_ok (as := nvMulA) (bs := nvMulB) (out0 := nvMulOut0) rfl rfl rfl ?_
  simpa only [nvMulBytes, nvMulOut0, nvMulA, nvMulB, List.length_replicate,
    List.length_cons, List.length_nil, Nat.reduceMul, Nat.reduceAdd,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
    array64_split3 0x1000#64 nvMulOut0 nvMulA nvMulB (by simp [nvMulOut0, nvMulA, nvMulB])

theorem nvAdd_spec_ok :
    addMod25519Spec (0x1000#64, 0x1020#64, 0x1040#64, ()) (nvAddBytes.At 0x1000#64)
      (fun _ m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧ limbsVal rs = 19 ∧
        (array64 0x1000#64 rs ⋆ array64 0x1020#64 nvAddA ⋆ array64 0x1040#64 nvAddB) m')
      (fun _ _ _ _ => False) := by
  have hm0 : (array64 0x1000#64 nv4Out0 ⋆ array64 0x1020#64 nvAddA ⋆
      array64 0x1040#64 nvAddB) (nvAddBytes.At 0x1000#64) := by
    simpa only [nvAddBytes, nv4Out0, nvAddA, nvAddB, List.length_replicate,
      List.length_cons, List.length_nil, Nat.reduceMul, Nat.reduceAdd,
      BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
      array64_split3 0x1000#64 nv4Out0 nvAddA nvAddB (by simp [nv4Out0, nvAddA, nvAddB])
  have hAlt : limbsVal nvAddA < p25519 := by rw [nvAddA_val]; have := p25519_gt_100; omega
  have hBlt : limbsVal nvAddB < p25519 := by rw [nvAddB_val]; have := p25519_gt_100; omega
  exact ⟨nvAddA, nvAddB, nv4Out0, emp, rfl, rfl, rfl, hAlt, hBlt, by rw [sep_emp]; exact sep_ac hm0,
    fun rs m' hrs hmod _ hm' =>
      ⟨rs, hrs, hmod.trans nvAdd_mod, by rw [sep_emp] at hm'; exact sep_ac hm'⟩⟩

theorem nvSub_spec_ok :
    subMod25519Spec (0x1000#64, 0x1020#64, 0x1040#64, ()) (nvSubBytes.At 0x1000#64)
      (fun _ m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧ limbsVal rs = p25519 - 20 ∧
        (array64 0x1000#64 rs ⋆ array64 0x1020#64 nvSubA ⋆ array64 0x1040#64 nvSubB) m')
      (fun _ _ _ _ => False) := by
  have hm0 : (array64 0x1000#64 nv4Out0 ⋆ array64 0x1020#64 nvSubA ⋆
      array64 0x1040#64 nvSubB) (nvSubBytes.At 0x1000#64) := by
    simpa only [nvSubBytes, nv4Out0, nvSubA, nvSubB, List.length_replicate,
      List.length_cons, List.length_nil, Nat.reduceMul, Nat.reduceAdd,
      BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using
      array64_split3 0x1000#64 nv4Out0 nvSubA nvSubB (by simp [nv4Out0, nvSubA, nvSubB])
  have hAlt : limbsVal nvSubA < p25519 := by rw [nvSubA_val]; have := p25519_gt_100; omega
  have hBlt : limbsVal nvSubB < p25519 := by rw [nvSubB_val]; have := p25519_gt_100; omega
  exact ⟨nvSubA, nvSubB, nv4Out0, emp, rfl, rfl, rfl, hAlt, hBlt, by rw [sep_emp]; exact sep_ac hm0,
    fun rs m' hrs hsub _ hm' =>
      ⟨rs, hrs, hsub.trans nvSub_val, by rw [sep_emp] at hm'; exact sep_ac hm'⟩⟩

end BignumKit

/-! ## 3. Union-Find (`ufModule`) -/

section UnionFindKit

open LeanQbe.T.Examples.UnionFind

@[expose] def ufInitBytes : List UInt8 := bytes64 (init 4)

theorem ufInitBytes_length : ufInitBytes.length ≤ 8192 := by
  simp [ufInitBytes, bytes64_length, init]

theorem uf_module_fnspec_gen {T : Target} {lt : LegalTarget}
    {hints : List T.toIsa.Hints}
    (M : Compiled T lt [] [] 0 ufFns hints 2048) (hh : T.mach.Host)
    (hi64 : lt.legalSig [i64] = [i64])
    (hsupp : ∀ f ∈ ufModule.fns, (f.earlyOpt).body.supportsSource lt = true)
    (k₀ : Nat) (hc : M.code.IsInfixAt (T.mach.prog hh) k₀) (hu : T.LabelsUnique hh)
    {f : Fn} (hf : f ∈ ufModule.fns) :
    T.Defined hh f.name ∧ T.FnSpec hh f.name (ufEnv f.name f.as f.rs) (M.bound f.name) 0 := by
  have hmem := hf
  simp only [ufModule, ufFns, List.mem_cons, List.not_mem_nil, or_false] at hmem
  have ⟨has, hrs, hnoex⟩ :
      lt.legalSig f.as = f.as ∧ lt.legalSig f.rs = f.rs ∧
        (∀ args m Q X X',
          ufEnv f.name f.as f.rs args m Q X → ufEnv f.name f.as f.rs args m Q X') := by
    rcases hmem with rfl | rfl | rfl
    · exact ⟨legalSig_two_i64 hi64, hi64, fun _ _ _ _ _ h => h⟩
    · exact ⟨legalSig_three_i64 hi64, rfl, fun _ _ _ _ _ h => h⟩
    · exact ⟨legalSig_three_i64 hi64, rfl, fun _ _ _ _ _ h => h⟩
  exact M.fnSpec_noExit_id ufModule rfl hh ufEnv k₀ hc hu ufModule_checkAcyclic ufFns_wf
    hsupp ufEnv_sound hf has hrs hnoex

theorem find_spec_ok {p x : BitVec 64} {n : Nat} {rep : BitVec 64 → BitVec 64}
    (hx : x.toNat < n) {m : Mem 64} (hm : uf p n rep m) :
    findSpec (p, x, ()) m (fun r m' => r = (rep x, ()) ∧ uf p n rep m')
      (fun _ _ _ _ => False) :=
  ⟨n, rep, emp, by rw [sep_emp]; exact hm, hx, fun _ hm' => ⟨rfl, by rwa [sep_emp] at hm'⟩⟩

theorem union_spec_ok {p x y : BitVec 64} {n : Nat} {rep : BitVec 64 → BitVec 64}
    (hx : x.toNat < n) (hy : y.toNat < n) {m : Mem 64} (hm : uf p n rep m) :
    unionSpec (p, x, y, ()) m (fun _ m' => uf p n (merge rep x y) m')
      (fun _ _ _ _ => False) :=
  ⟨n, rep, emp, by rw [sep_emp]; exact hm, hx, hy, fun _ hm' => by rwa [sep_emp] at hm'⟩

end UnionFindKit

/-! ## 4. Scalar Litmus Suite (`allFns`, 10 Modules) -/

section LitmusKit

open LeanQbe.T.Examples.Litmus

theorem litmus_allFns_wf : ∀ fn ∈ allFns, fn.Wf := by
  intro fn hfn
  simp only [allFns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tracer_wf
  · exact ifelse_wf
  · exact sumto_wf
  · exact evenodd_wf
  · exact nested_wf
  · exact swap_wf
  · exact inc_wf
  · exact callinc_wf
  · exact check_wf
  · exact twice_wf
  · exact spill10_wf
  · exact sumcall_wf

theorem litmus_noExit_fnspec_gen {T : Target} {lt : LegalTarget} {mod : Module}
    {hints : List T.toIsa.Hints}
    (M : Compiled T lt [] [] 0 mod.fns hints 2048) (hh : T.mach.Host)
    (hsupp : ∀ fn ∈ allFns, (fn.earlyOpt).body.supportsSource lt = true)
    (hacyc : mod.checkAcyclic = true) (hsub : ∀ fn ∈ mod.fns, fn ∈ allFns)
    (k₀ : Nat) (hc : M.code.IsInfixAt (T.mach.prog hh) k₀) (hu : T.LabelsUnique hh)
    {fn : Fn} (hf : fn ∈ mod.fns)
    (has : lt.legalSig fn.as = fn.as) (hrs : lt.legalSig fn.rs = fn.rs)
    (hnoex : ∀ args m Q X X',
      litmusEnv fn.name fn.as fn.rs args m Q X → litmusEnv fn.name fn.as fn.rs args m Q X') :
    T.Defined hh fn.name ∧
      T.FnSpec hh fn.name (litmusEnv fn.name fn.as fn.rs) (M.bound fn.name) 0 :=
  M.fnSpec_noExit_id mod rfl hh litmusEnv k₀ hc hu hacyc
    (fun g hg => litmus_allFns_wf g (hsub g hg))
    (fun g hg => hsupp g (hsub g hg))
    (fun g hg => litmusEnv_sound g (hsub g hg))
    hf has hrs hnoex

theorem litmus_single_fnspec_gen {T : Target} {lt : LegalTarget} {f : Fn}
    {hints : List T.toIsa.Hints}
    (M : Compiled T lt [] [] 0 [f] hints 2048) (hh : T.mach.Host)
    (hsupp : ∀ fn ∈ allFns, (fn.earlyOpt).body.supportsSource lt = true)
    (hacyc : ({ fns := [f], externs := [], exits := [] } : Module).checkAcyclic = true)
    (hf : f ∈ allFns) (k₀ : Nat) (hc : M.code.IsInfixAt (T.mach.prog hh) k₀)
    (hu : T.LabelsUnique hh)
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X',
      litmusEnv f.name f.as f.rs args m Q X → litmusEnv f.name f.as f.rs args m Q X') :
    T.Defined hh f.name ∧
      T.FnSpec hh f.name (litmusEnv f.name f.as f.rs) (M.bound f.name) 0 :=
  litmus_noExit_fnspec_gen (mod := ⟨[f], [], []⟩) M hh hsupp hacyc
    (fun g hg => by simp at hg; subst hg; exact hf) k₀ hc hu List.mem_cons_self has hrs hnoex

theorem litmus_twoFn_fnspec_gen {T : Target} {lt : LegalTarget}
    (mod : Module) {f1 f2 : Fn} {hints : List T.toIsa.Hints}
    (hm : mod.fns = [f1, f2]) (hacyc : mod.checkAcyclic = true)
    (h1 : f1.as = [i64] ∧ f1.rs = [i64]) (h2 : f2.as = [i64, i64] ∧ f2.rs = [i64])
    (hsub : ∀ g ∈ mod.fns, g ∈ allFns)
    (hnoex : ∀ g ∈ mod.fns, ∀ args m Q X X',
      litmusEnv g.name g.as g.rs args m Q X → litmusEnv g.name g.as g.rs args m Q X')
    (M : Compiled T lt [] [] 0 mod.fns hints 2048) (hh : T.mach.Host)
    (hi64 : lt.legalSig [i64] = [i64])
    (hsupp : ∀ fn ∈ allFns, (fn.earlyOpt).body.supportsSource lt = true)
    (k₀ : Nat) (hc : M.code.IsInfixAt (T.mach.prog hh) k₀) (hu : T.LabelsUnique hh)
    {fn : Fn} (hf : fn ∈ mod.fns) :
    T.Defined hh fn.name ∧
      T.FnSpec hh fn.name (litmusEnv fn.name fn.as fn.rs) (M.bound fn.name) 0 := by
  have hmem := hf
  rw [hm] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  have ⟨has, hrs⟩ : lt.legalSig fn.as = fn.as ∧ lt.legalSig fn.rs = fn.rs := by
    rcases hmem with rfl | rfl
    · rw [h1.1, h1.2]; exact ⟨hi64, hi64⟩
    · rw [h2.1, h2.2]; exact ⟨legalSig_two_i64 hi64, hi64⟩
  exact litmus_noExit_fnspec_gen M hh hsupp hacyc hsub k₀ hc hu hf has hrs (hnoex fn hf)

theorem twice_module_fnspec_gen {T : Target} {lt : LegalTarget}
    {hints : List T.toIsa.Hints}
    (M : Compiled T lt [] ["fail"] 0 twiceModule.fns hints 2048) (hh : T.mach.Host)
    (hi64 : lt.legalSig [i64] = [i64])
    (hsupp : ∀ fn ∈ allFns, (fn.earlyOpt).body.supportsSource lt = true)
    (k₀ : Nat) (hc : M.code.IsInfixAt (T.mach.prog hh) k₀) (hu : T.LabelsUnique hh)
    (hfail : T.Defined hh "fail") {fn : Fn} (hf : fn ∈ twiceModule.fns) :
    T.Defined hh fn.name ∧
      T.FnSpec hh fn.name (litmusEnv fn.name fn.as fn.rs) (M.bound fn.name) 0 := by
  have hsub : ∀ g ∈ twiceModule.fns, g ∈ allFns := fun g hg => by
    simp [twiceModule] at hg; rcases hg with rfl | rfl <;> simp [allFns]
  obtain ⟨hdef, hspec⟩ := M.fnSpec twiceModule rfl hh litmusEnv k₀ hc hu
    twiceModule_acyclic
    (fun g hg => litmus_allFns_wf g (hsub g hg))
    (fun g hg => hsupp g (hsub g hg))
    (fun g hg => litmusEnv_sound g (hsub g hg))
    (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    (fun g hg => by simp at hg; subst hg; exact hfail) hf
  have hmem := hf
  simp only [twiceModule, List.mem_cons, List.not_mem_nil, or_false] at hmem
  have ⟨has, hrs⟩ : lt.legalSig fn.as = fn.as ∧ lt.legalSig fn.rs = fn.rs := by
    rcases hmem with rfl | rfl
    · exact ⟨hi64, hi64⟩
    · exact ⟨legalSig_two_i64 hi64, hi64⟩
  have hfn' := fnSpec_of_legalEnv_legalSig_eq has hrs
    (List.mem_append_left _ (List.mem_map_of_mem hf)) hspec
  refine ⟨hdef, fun args m Q X hs => hfn' args m Q X ?_⟩
  rcases hmem with rfl | rfl
  · exact ⟨hs.1, fun hna => legal_xpost_i64 (lt := lt) hi64 (hs.2 hna)⟩
  · exact ⟨hs.1, fun hna => legal_xpost_i64 (lt := lt) hi64 (hs.2.1 hna),
      fun ha hnb => legal_xpost_i64 (lt := lt) hi64 (hs.2.2 ha hnb)⟩

theorem tracer_spec_ok (a b p v0 : BitVec 64) {m : Mem 64} (hm : cell64 p v0 m) :
    tracerContract (a, b, p, ()) m
      (fun r m' => r = (a + b, ()) ∧ cell64 p (a + b) m') (fun _ _ _ _ => False) :=
  ⟨v0, emp, by rw [sep_emp]; exact hm, fun _ hm' => ⟨rfl, by rwa [sep_emp] at hm'⟩⟩

theorem twice_spec_ok (a b : BitVec 64) :
    twiceContract (a, b, ()) ∅
      (fun r m' => Truthy a ∧ Truthy b ∧ r = (a + b, ()) ∧ m' = ∅)
      (fun sym cs xs m' => ∃ h : cs = [i64], sym = "fail" ∧ m' = ∅ ∧
        ((¬Truthy a ∧ xs = h ▸ (a, ())) ∨ (Truthy a ∧ ¬Truthy b ∧ xs = h ▸ (b, ())))) :=
  ⟨fun ha hb => ⟨ha, hb, rfl, rfl⟩,
   fun hna => ⟨rfl, rfl, rfl, Or.inl ⟨hna, rfl⟩⟩,
   fun ha hnb => ⟨rfl, rfl, rfl, Or.inr ⟨ha, hnb, rfl⟩⟩⟩

@[expose] def zeros8 : List UInt8 := Int.toBytes 8 (0#64).toInt

end LitmusKit

/-! ## 5. Cyclic & Mutual Recursion (`LinkRec`) -/

section LinkRecKit

open LeanQbe.T.LinkRec

theorem evenOdd_wf_mem : ∀ f ∈ evenOddRecMod.fns, f.Wf := by
  intro f hf
  simp only [evenOddRecMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> first | exact isEven_wf | exact isOdd_wf

theorem evenOdd_module_fnspec_gen {T : Target} {lt : LegalTarget}
    {hints : List T.toIsa.Hints}
    (M : CompiledRec T lt [] [] 0 32 evenOddRecMod.fns hints 2048) (hh : T.mach.Host)
    (hi64 : lt.legalSig [i64] = [i64])
    (hsupp : ∀ f ∈ evenOddRecMod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (k₀ : Nat) (hc : M.code.IsInfixAt (T.mach.prog hh) k₀) (hu : T.LabelsUnique hh)
    {k : Nat} (hk : k ≤ 32) {fn : Fn} (hf : fn ∈ evenOddRecMod.fns) :
    T.Defined hh fn.name ∧
      T.FnSpec hh fn.name (evenOddRecEnv k fn.name fn.as fn.rs) (M.boundAt k) 0 := by
  have hmem := hf
  simp only [evenOddRecMod, List.mem_cons, List.not_mem_nil, or_false] at hmem
  have ⟨has, hrs, hnoex⟩ : lt.legalSig fn.as = fn.as ∧ lt.legalSig fn.rs = fn.rs ∧
      (∀ args m Q X X', evenOddRecEnv k fn.name fn.as fn.rs args m Q X →
        evenOddRecEnv k fn.name fn.as fn.rs args m Q X') := by
    rcases hmem with rfl | rfl <;> exact ⟨hi64, hi64, fun _ _ _ _ _ h => h⟩
  have hrec := link_rec_compiled M evenOddRecMod rfl hh evenOddRecEnv
    (fun _ _ _ _ _ _ _ => False) k₀ hc hu evenOddRecMod_checkCyclic evenOdd_wf_mem
    hsupp (fun k' _ fn' hf' => evenOddRecMod_wp_step k' fn' hf')
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h) k hk fn hf
  exact ⟨hrec.1, Target.FnSpec.of_spec T (fnSpec_of_legalEnv_onlyFn has hrs hrec.2)
    fun args m Q X h => hnoex args m Q X _ h⟩

theorem recSum_module_fnspec_gen {T : Target} {lt : LegalTarget}
    {hints : List T.toIsa.Hints}
    (M : CompiledRec T lt [] ["out_of_fuel"] 16 16 recSumMod.fns hints 2048) (hh : T.mach.Host)
    (hi64 : lt.legalSig [i64] = [i64])
    (hsupp : ∀ f ∈ recSumMod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (k₀ : Nat) (hc : M.code.IsInfixAt (T.mach.prog hh) k₀) (hu : T.LabelsUnique hh)
    (hexit : T.Defined hh "out_of_fuel") {k : Nat} (hk : k ≤ 16) :
    T.Defined hh "recSum" ∧ T.FnSpec hh "recSum" (recSumSpec k) (M.boundAt k) 16 := by
  have hrec := link_rec_compiled M recSumMod rfl hh recSumRecEnv
    (fun _ _ _ _ _ _ _ => False) k₀ hc hu recSumMod_checkCyclic
    (fun f hf => by simp [recSumMod] at hf; subst hf; exact recSum_wf)
    hsupp (fun k' _ fn' hf' => recSumMod_wp_step k' fn' hf')
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun g hg => by simp at hg; subst hg; exact hexit)
    k hk recSum List.mem_cons_self
  have hfn' := fnSpec_of_legalEnv_onlyFn (f := recSum) (Γ := recSumRecEnv k)
    (legalSig_two_i64 hi64) hi64 hrec.2
  refine ⟨hrec.1, Target.FnSpec.of_spec T hfn' ?_⟩
  rintro ⟨n, f, ⟨⟩⟩ m Q X ⟨hf, hout⟩
  refine ⟨hf, ?_⟩
  cases ho : recSumOutcome n f.toNat with
  | inl s => rw [ho] at hout; exact hout
  | inr rem => rw [ho] at hout; exact legal_xpost_i64 (lt := lt) hi64 hout

theorem recSum_spec_ok {k : Nat} (n f : BitVec 64) (hf : f.toNat ≤ k) :
    recSumSpec k (n, f, ()) ∅
      (fun r _ => ∃ sum, recSumOutcome n f.toNat = .inl sum ∧ r = (sum, ()))
      (fun g cs xs _ => ∃ h : cs = [i64], ∃ rem, recSumOutcome n f.toNat = .inr rem ∧
        g = "out_of_fuel" ∧ xs = h ▸ (rem, ())) := by
  refine ⟨hf, ?_⟩
  cases ho : recSumOutcome n f.toNat with
  | inl s' => exact ⟨s', rfl, rfl⟩
  | inr rem => exact ⟨rfl, rem, rfl, rfl, rfl⟩

theorem evenOdd_target_nonvacuous {T : Target} (I : TargetInit T 2048 8192)
    {lt : LegalTarget} {hints : List T.toIsa.Hints}
    (M : CompiledRec T lt [] [] 0 32 evenOddRecMod.fns hints 2048)
    (nm : Sym) {k : Nat} (hk : k ≤ 32) {n v : BitVec 64}
    (hfn : T.FnSpec M.host nm (evenOddRecEnv k nm [i64] [i64]) (M.boundAt k) 0)
    (hargs : (T.toIsa.assignArgs [i64]).isSome = true)
    (hsp : evenOddRecEnv k nm [i64] [i64] (n, ()) (([] : List UInt8).At 0x1000#64)
      (fun r _ => r = (v, ())) (fun _ _ _ _ => False)) :
    Eventually (T.mach.step M.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v)
      (T.mach.mkState (I.initState (M.boundAt k) [] (as := [i64]) (n, ()))
        (T.mach.labelAddr M.host nm)) :=
  run_rec_ret1_i64 I M hk hfn [] (n, ()) v (by decide) hargs hsp fun _ _ h => h

end LinkRecKit

/-! ## 6. Generic `BenchAbi` Correctness & Non-Vacuity Combinators -/

section AbiWorkloads

open LeanQbe.T.Examples.ChaCha
open LeanQbe.T.Examples.Bignum
open LeanQbe.T.Examples.UnionFind
open LeanQbe.T.Examples.Litmus
open LeanQbe.T.Examples.LratBytes

/-! ### 6.1 `ChaCha` -/

theorem chacha20Block_abi_correct (A : BenchAbi) (hh : A.T.mach.Host)
    {hints : List A.T.toIsa.Hints} (M : Compiled A.T A.lt [] [] 0 chacha20Module.fns hints 2048)
    (hsupp : ∀ f ∈ chacha20Module.fns, (f.earlyOpt).body.supportsSource A.lt = true)
    (k₀ : Nat) (hc : M.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (out inp : BitVec 64) (init : ChaCha.State) (old : List ChaCha.Row) (hold : old.length = 4)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hout : A.argAt 0 s = out) (hinp : A.argAt 1 s = inp) (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆
      (array (t := v4i32) out old ⋆ array (t := v4i32) inp init.toRows) ⋆
      A.entryFrame s ra (M.bound "chacha20Block") ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st => A.T.mach.pc st = ra ∧
        A.calleeSavedOk s (A.T.mach.data st) ∧ A.spRestored s (A.T.mach.data st) ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆
          (array (t := v4i32) out (rfcChaCha20Core init).toRows ⋆
            array (t := v4i32) inp init.toRows) ⋆
          A.exitFrame s (M.bound "chacha20Block") ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh "chacha20Block")) :=
  abi_of_returns_sep0 A hh
    (chacha20_module_fnspec_gen M hh A.legalSig_i64 hsupp k₀ hc hu List.mem_cons_self).2
    s ra R (A.argsIn_2 hout hinp) hsp hmem (fun _ => chacha20_spec_ok hold)

theorem rfc8439_vector_abi_nonvacuous (A : BenchAbi)
    {hints : List A.T.toIsa.Hints} (M : Compiled A.T A.lt [] [] 0 chacha20Module.fns hints 2048)
    (hsupp : ∀ f ∈ chacha20Module.fns, (f.earlyOpt).body.supportsSource A.lt = true) :
    Eventually (A.T.mach.step M.host)
      (fun st => A.T.mach.pc st = A.init.ra0 ∧
        (A.T.mach.mem (A.T.mach.data st)).loadBytes 0x1000#64 64 =
          some rfc8439_expected_bytes ∧
        ∃ res : ChaCha.State,
          res.toWords = rfc8439_expected_words ∧ res.toBytes = rfc8439_expected_bytes ∧
          (A.T.mach.mem (A.T.mach.data st) =⋆
            (array (t := v4i32) 0x1000#64 res.toRows ⋆
              array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows) ⋆
            A.initExitFrame (M.bound "chacha20Block") ⋆ emp))
      (A.T.mach.mkState (A.init.initState (M.bound "chacha20Block") chachaInitBytes
          (as := [i64, i64]) (0x1000#64, 0x1040#64, ()))
        (A.T.mach.labelAddr M.host "chacha20Block")) := by
  have hfn : A.T.FnSpec M.host "chacha20Block" chacha20BlockSpec (M.bound "chacha20Block") 0 :=
    (chacha20_module_fnspec_gen M M.host A.legalSig_i64 hsupp 0
      M.code_infix_host M.labelsUnique List.mem_cons_self).2
  have hmem := A.init.mem_entry (M.bound "chacha20Block") chachaInitBytes (as := [i64, i64])
    (0x1000#64, 0x1040#64, ()) (Nat.le_trans (M.bound_le_max "chacha20Block") A.maxStack_ge)
    (Nat.le_trans chachaInitBytes_length A.maxMem_ge)
  rw [← A.init.get_sp (M.bound "chacha20Block") chachaInitBytes (as := [i64, i64])
    (0x1000#64, 0x1040#64, ())] at hmem
  have hm0 : (array (t := v4i32) 0x1000#64 chachaOut0 ⋆
      array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows)
      (chachaInitBytes.At 0x1000#64) := by
    have ha := array_bytes (t := v4i32) 0x1000#64 (chachaOut0 ++ rfc8439_test_init.toRows)
      (by simp [chachaOut0, ChaCha.State.toRows, Ty.bytes, Ty.size])
    rw [array_append] at ha
    simpa only [chachaInitBytes, chachaOut0, List.length_replicate, Ty.bytes, Ty.size,
      Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd]
      using ha
  refine A.init.run_fnSpec M hfn chachaInitBytes (0x1000#64, 0x1040#64, ())
    (Nat.le_trans chachaInitBytes_length A.maxMem_ge) (A.assignArgs_i64 2 (by decide))
    (chacha20_spec_ok rfl hm0) ?_ A.maxStack_ge
  rintro st (⟨hpc, _, m', hP, _, hm'⟩ | ⟨_, _, _, _, hx, _⟩)
  · have hdmem : A.T.mach.mem (A.T.mach.data st) =⋆
        (array (t := v4i32) 0x1000#64 (rfcChaCha20Core rfc8439_test_init).toRows ⋆
          array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows) ⋆
        A.initExitFrame (M.bound "chacha20Block") ⋆ emp :=
      sep_mono_mid (fun _ hex => A.initExitFrame_of_exit hex)
        (sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP)) hm')
    have hdmem_ac : (array (t := v4i32) 0x1000#64 (rfcChaCha20Core rfc8439_test_init).toRows ⋆
        (array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows ⋆
          A.initExitFrame (M.bound "chacha20Block") ⋆ emp))
        (A.T.mach.mem (A.T.mach.data st)) := sep_ac hdmem
    have hflat : (Eq (rfc8439_expected_bytes.At 0x1000#64) ⋆
        (array (t := v4i32) 0x1040#64 rfc8439_test_init.toRows ⋆
          A.initExitFrame (M.bound "chacha20Block") ⋆ emp))
        (A.T.mach.mem (A.T.mach.data st)) := by
      refine sep_mono (fun _ h => ?_) hdmem_ac
      rw [← rfc8439_expected_bytes_eq_bytesOf]
      exact (array_eq_bytesOf 0x1000#64 _
        (by simp [ChaCha.State.toRows, Ty.bytes, Ty.size]) h).symm
    exact ⟨hpc, loadBytes_sep_At (by decide) hflat, rfcChaCha20Core rfc8439_test_init,
      rfc8439_test_vector_words, rfc8439_test_vector_bytes, hdmem⟩
  · exact hx.elim

/-! ### 6.2 `Bignum` -/

theorem bignum_abi_correct (A : BenchAbi) (hh : A.T.mach.Host)
    {f : Fn} {hints : List A.T.toIsa.Hints}
    (M : Compiled A.T A.lt [] [] 0 [f] hints 2048)
    (hacyc : ({ fns := [f], externs := [], exits := [] } : Module).checkAcyclic = true)
    (hwf : f.Wf) (hmem_f : f ∈ [mul4x4Fn, addMod25519Fn, subMod25519Fn])
    (hsupp : ∀ g ∈ [mul4x4Fn, addMod25519Fn, subMod25519Fn],
      (g.earlyOpt).body.supportsSource A.lt = true)
    (hwp : ∀ xs m Q X, bignumEnv f.name f.as f.rs xs m Q X → Func.wp bignumEnv f.body xs m Q X)
    (has_sig : A.lt.legalSig f.as = f.as) (hrs_sig : A.lt.legalSig f.rs = f.rs)
    (hf_sig : f.as = [i64, i64, i64] ∧ f.rs = [])
    (k₀ : Nat) (hc : M.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (out pa pb : BitVec 64) (as bs out0 : List (BitVec 64))
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hout_reg : A.argAt 0 s = out) (hpa : A.argAt 1 s = pa) (hpb : A.argAt 2 s = pb)
    (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆ (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) ⋆
      A.entryFrame s ra (M.bound f.name) ⋆ R))
    {P' : Mem 64 → Prop}
    (hspec : ∀ m, (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) m →
      bignumEnv f.name [i64, i64, i64] [] (out, pa, pb, ()) m
        (fun _ m' => P' m') (fun _ _ _ _ => False)) :
    Eventually (A.T.mach.step hh)
      (fun st => A.T.mach.pc st = ra ∧
        A.calleeSavedOk s (A.T.mach.data st) ∧ A.spRestored s (A.T.mach.data st) ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆ P' ⋆ A.exitFrame s (M.bound f.name) ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh f.name)) := by
  have hnoex : ∀ args m Q X X',
      bignumEnv f.name f.as f.rs args m Q X → bignumEnv f.name f.as f.rs args m Q X' := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem_f
    rcases hmem_f with rfl | rfl | rfl <;> exact fun _ _ _ _ _ h => h
  have hfn := (bignum_single_fnspec_gen M hh hacyc hwf hmem_f hsupp hwp k₀ hc hu
    has_sig hrs_sig hnoex).2
  rcases hf_sig with ⟨hfa, hfr⟩
  rw [hfa, hfr] at hfn
  exact abi_of_returns_sep0 A hh hfn s ra R (A.argsIn_3 hout_reg hpa hpb) hsp hmem hspec

theorem bignum_abi_nonvacuous (A : BenchAbi)
    {f : Fn} {hints : List A.T.toIsa.Hints}
    (M : Compiled A.T A.lt [] [] 0 [f] hints 2048)
    (hacyc : ({ fns := [f], externs := [], exits := [] } : Module).checkAcyclic = true)
    (hwf : f.Wf) (hmem_f : f ∈ [mul4x4Fn, addMod25519Fn, subMod25519Fn])
    (hsupp : ∀ g ∈ [mul4x4Fn, addMod25519Fn, subMod25519Fn],
      (g.earlyOpt).body.supportsSource A.lt = true)
    (hwp : ∀ xs m Q X, bignumEnv f.name f.as f.rs xs m Q X → Func.wp bignumEnv f.body xs m Q X)
    (has_sig : A.lt.legalSig f.as = f.as) (hrs_sig : A.lt.legalSig f.rs = f.rs)
    (hf_sig : f.as = [i64, i64, i64] ∧ f.rs = [])
    (bytes : List UInt8) (xs : Tup Val [i64, i64, i64]) (hlen : bytes.length ≤ 8192)
    {P : Mem 64 → Prop}
    (hspec : bignumEnv f.name [i64, i64, i64] [] xs (bytes.At 0x1000#64)
      (fun _ m' => P m') (fun _ _ _ _ => False)) :
    Eventually (A.T.mach.step M.host)
      (fun st => A.T.mach.pc st = A.init.ra0 ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆ P ⋆ A.initExitFrame (M.bound f.name) ⋆ emp))
      (A.T.mach.mkState (A.init.initState (M.bound f.name) bytes xs)
        (A.T.mach.labelAddr M.host f.name)) := by
  have hnoex : ∀ args m Q X X',
      bignumEnv f.name f.as f.rs args m Q X → bignumEnv f.name f.as f.rs args m Q X' := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem_f
    rcases hmem_f with rfl | rfl | rfl <;> exact fun _ _ _ _ _ h => h
  have hfn := (bignum_single_fnspec_gen M M.host hacyc hwf hmem_f hsupp hwp 0
    M.code_infix_host M.labelsUnique has_sig hrs_sig hnoex).2
  rcases hf_sig with ⟨hfa, hfr⟩
  rw [hfa, hfr] at hfn
  exact abi_run_sep0 A M hfn bytes xs hlen (A.assignArgs_i64 3 (by decide)) hspec

/-! ### 6.3 `UnionFind` -/

theorem uf_find_abi_correct (A : BenchAbi) (hh : A.T.mach.Host)
    {hints : List A.T.toIsa.Hints} (M : Compiled A.T A.lt [] [] 0 ufFns hints 2048)
    (hsupp : ∀ f ∈ ufModule.fns, (f.earlyOpt).body.supportsSource A.lt = true)
    (k₀ : Nat) (hc : M.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (p x : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64) (hx : x.toNat < n)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hp : A.argAt 0 s = p) (hxx : A.argAt 1 s = x) (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆ uf p n rep ⋆ A.entryFrame s ra (M.bound "find") ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st => A.T.mach.pc st = ra ∧ A.retGpr (A.T.mach.data st) = rep x ∧
        A.calleeSavedOk s (A.T.mach.data st) ∧ A.spRestored s (A.T.mach.data st) ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆ uf p n rep ⋆
          A.exitFrame s (M.bound "find") ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh "find")) := by
  have hfn : A.T.FnSpec hh "find" findSpec (M.bound "find") 0 :=
    (uf_module_fnspec_gen M hh A.legalSig_i64 hsupp k₀ hc hu
      (by simp [ufModule, ufFns] : (⟨"find", [i64, i64], [i64], find⟩ : Fn) ∈ ufModule.fns)).2
  exact abi_of_returns_ret1_sep A hh hfn s ra R (A.argsIn_2 hp hxx) hsp hmem
    (fun _ => find_spec_ok hx)

theorem uf_unionLike_abi_correct (A : BenchAbi) (hh : A.T.mach.Host)
    {hints : List A.T.toIsa.Hints} (M : Compiled A.T A.lt [] [] 0 ufFns hints 2048)
    (hsupp : ∀ f ∈ ufModule.fns, (f.earlyOpt).body.supportsSource A.lt = true)
    (k₀ : Nat) (hc : M.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    {fn : Fn} (hfn_mem : fn ∈ ufModule.fns) (has : fn.as = [i64, i64, i64]) (hrs : fn.rs = [])
    (hspec_eq : ufEnv fn.name [i64, i64, i64] [] = unionSpec)
    (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hp : A.argAt 0 s = p) (hxx : A.argAt 1 s = x) (hyy : A.argAt 2 s = y)
    (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆ uf p n rep ⋆ A.entryFrame s ra (M.bound fn.name) ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st => A.T.mach.pc st = ra ∧
        A.calleeSavedOk s (A.T.mach.data st) ∧ A.spRestored s (A.T.mach.data st) ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆ uf p n (merge rep x y) ⋆
          A.exitFrame s (M.bound fn.name) ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh fn.name)) := by
  have hfn0 := (uf_module_fnspec_gen M hh A.legalSig_i64 hsupp k₀ hc hu hfn_mem).2
  rw [has, hrs, hspec_eq] at hfn0
  exact abi_of_returns_sep0 A hh hfn0 s ra R (A.argsIn_3 hp hxx hyy) hsp hmem
    (fun _ => union_spec_ok hx hy)

theorem uf_find_abi_nonvacuous (A : BenchAbi)
    {hints : List A.T.toIsa.Hints} (M : Compiled A.T A.lt [] [] 0 ufFns hints 2048)
    (hsupp : ∀ f ∈ ufModule.fns, (f.earlyOpt).body.supportsSource A.lt = true) :
    Eventually (A.T.mach.step M.host)
      (fun st => A.T.mach.pc st = A.init.ra0 ∧ A.retGpr (A.T.mach.data st) = 3#64 ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆ uf 0x1000#64 4 id ⋆
          A.initExitFrame (M.bound "find") ⋆ emp))
      (A.T.mach.mkState (A.init.initState (M.bound "find") ufInitBytes
          (as := [i64, i64]) (0x1000#64, 3#64, ()))
        (A.T.mach.labelAddr M.host "find")) := by
  have hfn : A.T.FnSpec M.host "find" findSpec (M.bound "find") 0 :=
    (uf_module_fnspec_gen M M.host A.legalSig_i64 hsupp 0 M.code_infix_host M.labelsUnique
      (by simp [ufModule, ufFns] : (⟨"find", [i64, i64], [i64], find⟩ : Fn) ∈ ufModule.fns)).2
  exact abi_run_ret1_sep_i64 A M hfn ufInitBytes (0x1000#64, 3#64, ()) 3#64
    (uf 0x1000#64 4 id) ufInitBytes_length (A.assignArgs_i64 2 (by decide)) find_nonvacuous
    fun _ _ ⟨hr, hm⟩ => ⟨hr, by rwa [sep_emp] at hm⟩

theorem uf_unionLike_abi_nonvacuous (A : BenchAbi)
    {hints : List A.T.toIsa.Hints} (M : Compiled A.T A.lt [] [] 0 ufFns hints 2048)
    (hsupp : ∀ f ∈ ufModule.fns, (f.earlyOpt).body.supportsSource A.lt = true)
    {fn : Fn} (hfn_mem : fn ∈ ufModule.fns) (has : fn.as = [i64, i64, i64]) (hrs : fn.rs = [])
    (hspec_eq : ufEnv fn.name [i64, i64, i64] [] = unionSpec) :
    Eventually (A.T.mach.step M.host)
      (fun st => A.T.mach.pc st = A.init.ra0 ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆ uf 0x1000#64 4 (merge id 1 2) ⋆
          A.initExitFrame (M.bound fn.name) ⋆ emp) ∧
        merge id 1 2 1 = merge id 1 2 2 ∧ merge id 1 2 0 ≠ merge id 1 2 1)
      (A.T.mach.mkState (A.init.initState (M.bound fn.name) ufInitBytes
          (as := [i64, i64, i64]) (0x1000#64, 1#64, 2#64, ()))
        (A.T.mach.labelAddr M.host fn.name)) := by
  have hfn := (uf_module_fnspec_gen M M.host A.legalSig_i64 hsupp 0
    M.code_infix_host M.labelsUnique hfn_mem).2
  rw [has, hrs, hspec_eq] at hfn
  refine A.init.run_fnSpec M hfn ufInitBytes (0x1000#64, 1#64, 2#64, ())
    (Nat.le_trans ufInitBytes_length A.maxMem_ge) (A.assignArgs_i64 3 (by decide))
    union_nonvacuous ?_ A.maxStack_ge
  rintro st (⟨hpc, _, m', ⟨rfl, huf'⟩, _, hm'⟩ | ⟨_, _, _, _, hx, _⟩)
  · rw [sep_emp] at huf'
    exact ⟨hpc, sep_mono_mid (fun _ hex => A.initExitFrame_of_exit hex)
      (sep_mono (fun _ => sep_mono (fun _ e => e ▸ huf')) hm'), merge_init_1_2⟩
  · exact hx.elim

/-! ### 6.4 `Litmus` -/

theorem litmus_tracer_abi_correct (A : BenchAbi) (hh : A.T.mach.Host)
    {hints : List A.T.toIsa.Hints}
    (M : Compiled A.T A.lt [] [] 0 tracerModule.fns hints 2048)
    (hsupp : ∀ fn ∈ allFns, (fn.earlyOpt).body.supportsSource A.lt = true)
    (k₀ : Nat) (hc : M.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (a b p v0 : BitVec 64) (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (ha : A.argAt 0 s = a) (hb : A.argAt 1 s = b) (hpp : A.argAt 2 s = p)
    (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆ cell64 p v0 ⋆ A.entryFrame s ra (M.bound "tracer") ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st => A.T.mach.pc st = ra ∧ A.retGpr (A.T.mach.data st) = a + b ∧
        A.calleeSavedOk s (A.T.mach.data st) ∧ A.spRestored s (A.T.mach.data st) ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆ cell64 p (a + b) ⋆
          A.exitFrame s (M.bound "tracer") ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh "tracer")) :=
  abi_of_returns_ret1_sep A hh
    (litmus_single_fnspec_gen M hh hsupp tracerModule_acyclic (by simp [allFns]) k₀ hc hu
      (legalSig_three_i64 A.legalSig_i64) A.legalSig_i64 (fun _ _ _ _ _ h => h)).2
    s ra R (A.argsIn_3 ha hb hpp) hsp hmem (fun _ hm => tracer_spec_ok a b p v0 hm)

theorem litmus_ret1_abi_correct (A : BenchAbi) (hh : A.T.mach.Host)
    {sym : Sym} {b : Nat} {spec : Spec [i64] [i64]} {n v : BitVec 64}
    (hfn : A.T.FnSpec hh sym spec b 0)
    (hspec : spec (n, ()) ∅ (fun r m' => r = (v, ()) ∧ emp m') (fun _ _ _ _ => False))
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hn : A.argAt 0 s = n) (hsp : A.stackPre s ra)
    (hmem : (A.entryFrame s ra b ⋆ R) (A.T.mach.mem s)) :
    Eventually (A.T.mach.step hh)
      (fun st => A.T.mach.pc st = ra ∧ A.retGpr (A.T.mach.data st) = v ∧
        A.calleeSavedOk s (A.T.mach.data st) ∧ A.spRestored s (A.T.mach.data st) ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆ A.exitFrame s b ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh sym)) :=
  abi_of_returns_ret1_emp A hh hfn hspec s ra R (A.argsIn_1 hn) hsp hmem

theorem litmus_ret2_abi_correct (A : BenchAbi) (hh : A.T.mach.Host)
    {sym : Sym} {b : Nat} {spec : Spec [i64, i64] [i64]} {x y v : BitVec 64}
    (hfn : A.T.FnSpec hh sym spec b 0)
    (hspec : spec (x, y, ()) ∅ (fun r m' => r = (v, ()) ∧ emp m') (fun _ _ _ _ => False))
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hx : A.argAt 0 s = x) (hy : A.argAt 1 s = y) (hsp : A.stackPre s ra)
    (hmem : (A.entryFrame s ra b ⋆ R) (A.T.mach.mem s)) :
    Eventually (A.T.mach.step hh)
      (fun st => A.T.mach.pc st = ra ∧ A.retGpr (A.T.mach.data st) = v ∧
        A.calleeSavedOk s (A.T.mach.data st) ∧ A.spRestored s (A.T.mach.data st) ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆ A.exitFrame s b ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh sym)) :=
  abi_of_returns_ret1_emp A hh hfn hspec s ra R (A.argsIn_2 hx hy) hsp hmem

theorem litmus_twice_abi_correct (A : BenchAbi) (hh : A.T.mach.Host)
    {hints : List A.T.toIsa.Hints}
    (M : Compiled A.T A.lt [] ["fail"] 0 twiceModule.fns hints 2048)
    (hsupp : ∀ fn ∈ allFns, (fn.earlyOpt).body.supportsSource A.lt = true)
    (k₀ : Nat) (hc : M.code.IsInfixAt (A.T.mach.prog hh) k₀)
    (hfail : A.T.Defined hh "fail") (hu : A.T.LabelsUnique hh)
    (a b : BitVec 64) (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (ha : A.argAt 0 s = a) (hb : A.argAt 1 s = b) (hsp : A.stackPre s ra)
    (hmem : (A.entryFrame s ra (M.bound "twice") ⋆ R) (A.T.mach.mem s)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        (Truthy a ∧ Truthy b ∧ A.T.mach.pc st = ra ∧
          A.retGpr (A.T.mach.data st) = a + b ∧
          A.calleeSavedOk s (A.T.mach.data st) ∧ A.spRestored s (A.T.mach.data st)) ∨
        ((¬Truthy a ∧ A.T.mach.pc st = A.T.mach.labelAddr hh "fail" ∧
          A.argAt 0 (A.T.mach.data st) = a ∧ A.exitSpOk (A.T.mach.data st)) ∨
         (Truthy a ∧ ¬Truthy b ∧ A.T.mach.pc st = A.T.mach.labelAddr hh "fail" ∧
          A.argAt 0 (A.T.mach.data st) = b ∧ A.exitSpOk (A.T.mach.data st))))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh "twice")) := by
  have hfn : A.T.FnSpec hh "twice" twiceContract (M.bound "twice") 0 :=
    (twice_module_fnspec_gen M hh A.legalSig_i64 hsupp k₀ hc hu hfail
      (fn := twice) (by simp [twiceModule])).2
  refine eventually_weaken _ _ _ _ ?_
    (abi_of_call_emp A hh hfn (twice_spec_ok a b) s ra R (A.argsIn_2 ha hb) hsp hmem)
  rintro st (⟨hpc, hcs, hsp', _, _, ⟨hta, htb, rfl, _⟩, hrets, _⟩ |
    ⟨_, _, _, _, ⟨rfl, rfl, _, hcase⟩, _, hpc, has', hspE⟩)
  · exact Or.inl ⟨hta, htb, hpc, A.retGpr_eq_of_retsIn hrets, hcs, hsp'⟩
  · rcases hcase with ⟨hna, rfl⟩ | ⟨hta, hnb, rfl⟩
    · exact Or.inr (Or.inl ⟨hna, hpc, A.arg0_eq_of_argsIn has', hspE⟩)
    · exact Or.inr (Or.inr ⟨hta, hnb, hpc, A.arg0_eq_of_argsIn has', hspE⟩)

theorem litmus_twice_exit_abi_nonvacuous (A : BenchAbi)
    {hints : List A.T.toIsa.Hints}
    (M : Compiled A.T A.lt [] ["fail"] 0 twiceModule.fns hints 2048)
    (hsupp : ∀ fn ∈ allFns, (fn.earlyOpt).body.supportsSource A.lt = true) :
    Eventually (A.T.mach.step M.host)
      (fun st => A.T.mach.pc st = A.T.mach.labelAddr M.host "fail" ∧
        A.argAt 0 (A.T.mach.data st) = 0#64)
      (A.T.mach.mkState (A.init.initState (M.bound "twice") [] (as := [i64, i64]) (20#64, 0#64, ()))
        (A.T.mach.labelAddr M.host "twice")) := by
  have hfn : A.T.FnSpec M.host "twice" twiceContract (M.bound "twice") 0 :=
    (twice_module_fnspec_gen M M.host A.legalSig_i64 hsupp 0 M.code_infix_host M.labelsUnique
      (M.defined_exit_host (by simp)) (fn := twice) (by simp [twiceModule])).2
  exact abi_run_exit1_i64 A M hfn [] (20#64, 0#64, ()) "fail" 0#64
    (by decide) (A.assignArgs_i64 2 (by decide))
    ⟨fun _ h0 => absurd h0 (by simp [Truthy]),
      fun h20 => absurd (by simp [Truthy] : Truthy 20#64) h20, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
    fun _ _ _ _ h => h

/-! ### 6.5 `LinkRec` -/

theorem linkrec_evenOdd_abi_correct (A : BenchAbi) (hh : A.T.mach.Host)
    {hints : List A.T.toIsa.Hints}
    (M : CompiledRec A.T A.lt [] [] 0 32 evenOddRecMod.fns hints 2048)
    (hsupp : ∀ f ∈ evenOddRecMod.fns, (f.earlyOpt).body.supportsSource A.lt = true)
    (k₀ : Nat) (hc : M.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    {k : Nat} (hk : k ≤ 32) {fn : Fn} (hf : fn ∈ evenOddRecMod.fns)
    (hfn_sig : fn.as = [i64] ∧ fn.rs = [i64])
    {spec : Spec [i64] [i64]}
    (hspec_eq : evenOddRecEnv k fn.name [i64] [i64] = spec)
    {valFn : BitVec 64 → BitVec 64} {n : BitVec 64}
    (hspec_ok : spec (n, ()) ∅ (fun r m' => r = (valFn n, ()) ∧ emp m') (fun _ _ _ _ => False))
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (harg : A.argAt 0 s = n) (hsp : A.stackPre s ra)
    (hmem : (A.entryFrame s ra (M.boundAt k) ⋆ R) (A.T.mach.mem s)) :
    Eventually (A.T.mach.step hh)
      (fun st => A.T.mach.pc st = ra ∧ A.retGpr (A.T.mach.data st) = valFn n ∧
        A.calleeSavedOk s (A.T.mach.data st) ∧ A.spRestored s (A.T.mach.data st) ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆ A.exitFrame s (M.boundAt k) ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh fn.name)) := by
  have hfn0 := (evenOdd_module_fnspec_gen M hh A.legalSig_i64 hsupp k₀ hc hu hk hf).2
  rw [hfn_sig.1, hfn_sig.2, hspec_eq] at hfn0
  exact abi_of_returns_ret1_emp A hh hfn0 hspec_ok s ra R (A.argsIn_1 harg) hsp hmem

theorem linkrec_recSum_abi_correct (A : BenchAbi) (hh : A.T.mach.Host)
    {hints : List A.T.toIsa.Hints}
    (M : CompiledRec A.T A.lt [] ["out_of_fuel"] 16 16 recSumMod.fns hints 2048)
    (hsupp : ∀ f ∈ recSumMod.fns, (f.earlyOpt).body.supportsSource A.lt = true)
    (k₀ : Nat) (hc : M.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (hexit : A.T.Defined hh "out_of_fuel")
    {k : Nat} (hk : k ≤ 16) (n f : BitVec 64) (hf : f.toNat ≤ k)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hn : A.argAt 0 s = n) (hf_arg : A.argAt 1 s = f) (hsp : A.stackPre s ra)
    (hmem : (A.entryFrame s ra (M.boundAt k) ⋆ R) (A.T.mach.mem s)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        (∃ sum, recSumOutcome n f.toNat = .inl sum ∧
          A.T.mach.pc st = ra ∧ A.retGpr (A.T.mach.data st) = sum ∧
          A.calleeSavedOk s (A.T.mach.data st) ∧ A.spRestored s (A.T.mach.data st)) ∨
        (∃ rem, recSumOutcome n f.toNat = .inr rem ∧
          A.T.mach.pc st = A.T.mach.labelAddr hh "out_of_fuel" ∧
          A.argAt 0 (A.T.mach.data st) = rem ∧ A.exitSpOk (A.T.mach.data st)))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh "recSum")) := by
  have hfn := (recSum_module_fnspec_gen M hh A.legalSig_i64 hsupp k₀ hc hu hexit hk).2
  refine eventually_weaken _ _ _ _ ?_
    (abi_of_call_emp A hh hfn (recSum_spec_ok n f hf) s ra R (A.argsIn_2 hn hf_arg) hsp hmem)
  rintro st (⟨hpc, hcs, hsp', _, _, ⟨sum, hsum, rfl⟩, hrets, _⟩ |
    ⟨_, _, _, _, ⟨rfl, rem, hrem, rfl, rfl⟩, _, hpc, has', hspE⟩)
  · exact Or.inl ⟨sum, hsum, hpc, A.retGpr_eq_of_retsIn hrets, hcs, hsp'⟩
  · exact Or.inr ⟨rem, hrem, hpc, A.arg0_eq_of_argsIn has', hspE⟩

theorem linkrec_recSum_normal_abi_nv (A : BenchAbi)
    {hints : List A.T.toIsa.Hints}
    (M : CompiledRec A.T A.lt [] ["out_of_fuel"] 16 16 recSumMod.fns hints 2048)
    (hsupp : ∀ f ∈ recSumMod.fns, (f.earlyOpt).body.supportsSource A.lt = true) :
    Eventually (A.T.mach.step M.host)
      (fun st => A.T.mach.pc st = A.init.ra0 ∧ A.retGpr (A.T.mach.data st) = 6#64)
      (A.T.mach.mkState (A.init.initState (M.boundAt 5) [] (as := [i64, i64]) (3#64, 5#64, ()))
        (A.T.mach.labelAddr M.host "recSum")) := by
  have hfn := (recSum_module_fnspec_gen M M.host A.legalSig_i64 hsupp 0
    M.code_infix_host M.labelsUnique (M.defined_exit_host (by simp)) (by decide : 5 ≤ 16)).2
  have ho : recSumOutcome 3#64 (5#64).toNat = .inl 6#64 := by decide
  exact abi_run_rec_ret1_i64 A M (by decide : 5 ≤ 16) hfn [] (3#64, 5#64, ()) 6#64
    (by decide) (A.assignArgs_i64 2 (by decide))
    ⟨by decide, by change match recSumOutcome 3#64 (5#64).toNat with
      | .inl s => (s, ()) = (6#64, ()) | .inr _ => False; rw [ho]⟩
    fun _ _ h => h

theorem linkrec_recSum_exit_abi_nv (A : BenchAbi)
    {hints : List A.T.toIsa.Hints}
    (M : CompiledRec A.T A.lt [] ["out_of_fuel"] 16 16 recSumMod.fns hints 2048)
    (hsupp : ∀ f ∈ recSumMod.fns, (f.earlyOpt).body.supportsSource A.lt = true) :
    Eventually (A.T.mach.step M.host)
      (fun st => A.T.mach.pc st = A.T.mach.labelAddr M.host "out_of_fuel" ∧
        A.argAt 0 (A.T.mach.data st) = 3#64)
      (A.T.mach.mkState (A.init.initState (M.boundAt 2) [] (as := [i64, i64]) (5#64, 2#64, ()))
        (A.T.mach.labelAddr M.host "recSum")) := by
  have hfn := (recSum_module_fnspec_gen M M.host A.legalSig_i64 hsupp 0
    M.code_infix_host M.labelsUnique (M.defined_exit_host (by simp)) (by decide : 2 ≤ 16)).2
  have ho : recSumOutcome 5#64 (2#64).toNat = .inr 3#64 := by decide
  exact abi_run_rec_exit1_i64 A M (by decide : 2 ≤ 16) hfn [] (5#64, 2#64, ())
    "out_of_fuel" 3#64 (by decide) (A.assignArgs_i64 2 (by decide))
    (X := fun g cs xs _ => g = "out_of_fuel" ∧ cs = [i64] ∧
      HEq xs ((3#64, ()) : Tup Val [i64]))
    ⟨by decide, by rw [ho]; exact ⟨rfl, rfl, HEq.rfl⟩⟩
    fun _ _ _ _ h => h

/-! ### 6.6 `LratBytes` -/

theorem lrat_mk_module_fnspec_abi (A : BenchAbi) (hh : A.T.mach.Host)
    {hints : List A.T.toIsa.Hints}
    (M : Compiled A.T A.lt [] [] 0 lratBytesFns hints 2048)
    (hsupp : ∀ f ∈ lratBytesModule.fns, (f.earlyOpt).body.supportsSource A.lt = true)
    (mainSpec : Spec [i64, i64, i64, i64, i64, i64] [i64])
    (hsound : ∀ f ∈ lratBytesFns, ∀ args m Q X,
      mkLratBytesEnv mainSpec f.name f.as f.rs args m Q X →
      Func.spec (mkLratBytesEnv mainSpec) f.body args m Q X)
    (hnoex_main : ∀ args m Q X X', mainSpec args m Q X → mainSpec args m Q X')
    (k₀ : Nat) (hc : M.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    {f : Fn} (hf : f ∈ lratBytesModule.fns) :
    A.T.Defined hh f.name ∧
      A.T.FnSpec hh f.name (mkLratBytesEnv mainSpec f.name f.as f.rs) (M.bound f.name) 0 := by
  have hmem := hf
  simp only [lratBytesModule, lratBytesFns, List.mem_cons, List.not_mem_nil, or_false] at hmem
  have h2 := legalSig_two_i64 A.legalSig_i64
  have h3 := legalSig_three_i64 A.legalSig_i64
  have h4 : A.lt.legalSig [i64, i64, i64, i64] = [i64, i64, i64, i64] := by
    simp only [LegalTarget.legalSig, legalSig_singleton_i64_tys A.legalSig_i64,
      List.cons_append, List.nil_append]
  have h6 := legalSig_six_i64 A.legalSig_i64
  have ⟨has, hrs, hnoex⟩ :
      A.lt.legalSig f.as = f.as ∧ A.lt.legalSig f.rs = f.rs ∧
        (∀ args m Q X X',
          mkLratBytesEnv mainSpec f.name f.as f.rs args m Q X →
          mkLratBytesEnv mainSpec f.name f.as f.rs args m Q X') := by
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨h3, A.legalSig_i64, fun _ _ _ _ _ h => h⟩
    · exact ⟨h2, A.legalSig_i64, fun _ _ _ _ _ h => h⟩
    · exact ⟨h2, A.legalSig_i64, fun _ _ _ _ _ h => h⟩
    · exact ⟨h4, A.legalSig_i64, fun _ _ _ _ _ h => h⟩
    · exact ⟨h2, A.legalSig_i64, fun _ _ _ _ _ h => h⟩
    · exact ⟨h6, A.legalSig_i64, hnoex_main⟩
  exact M.fnSpec_noExit_id lratBytesModule rfl hh (mkLratBytesEnv mainSpec) k₀ hc hu
    lratBytesModule_checkAcyclic lratBytesFns_wf hsupp hsound hf has hrs hnoex

theorem lrat_check_bytes_of_fnspec_abi (A : BenchAbi) (hh : A.T.mach.Host) {b : Nat}
    (hfnspec : A.T.FnSpec hh "lrat_check_bytes" lratCheckBytesSpec b 0)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (ha0 : A.argAt 0 s = cnf_ptr)
    (ha1 : A.argAt 1 s = BitVec.ofNat 64 cnfBytes.length)
    (ha2 : A.argAt 2 s = prf_ptr)
    (ha3 : A.argAt 3 s = BitVec.ofNat 64 prfBytes.length)
    (ha4 : A.argAt 4 s = work_ptr)
    (ha5 : A.argAt 5 s = BitVec.ofNat 64 work_len)
    (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      A.entryFrame s ra b ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        (A.retGpr (A.T.mach.data st) = 0 ∨ A.retGpr (A.T.mach.data st) = 1) ∧
        (A.retGpr (A.T.mach.data st) = 1 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        A.calleeSavedOk s (A.T.mach.data st) ∧ A.spRestored s (A.T.mach.data st) ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆
          (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
          A.exitFrame s b ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh "lrat_check_bytes")) := by
  obtain ⟨m, hm, hmEq⟩ := sep_extract_eq hmem
  have hspec : lratCheckBytesSpec
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length,
       prf_ptr, BitVec.ofNat 64 prfBytes.length,
       work_ptr, BitVec.ofNat 64 work_len, ())
      m
      (fun rs m' => ∃ r : BitVec 64, rs = (r, ()) ∧ (r = 0 ∨ r = 1) ∧
        (r = 1 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) m')
      (fun _ _ _ _ => False) :=
    ⟨cnf_ptr, prf_ptr, work_ptr, cnfBytes, prfBytes, work_len, emp,
      rfl, hcnf, hprf, hwork, by rwa [sep_emp],
      fun r m' hr01 hunsat hm' => ⟨r, rfl, hr01, hunsat, by rwa [sep_emp] at hm'⟩⟩
  refine eventually_weaken _ _ _ _ ?_
    (abi_of_returns A hh hfnspec hspec s ra R (A.argsIn_6 ha0 ha1 ha2 ha3 ha4 ha5) hsp hmEq)
  rintro st ⟨hpc, hcs, hsp', _, m', ⟨r, rfl, hr01, hunsat, hm'⟩, hrets, hm''⟩
  rw [← A.retGpr_eq_of_retsIn hrets] at hr01 hunsat
  exact ⟨hpc, hr01, hunsat, hcs, hsp', sep_mono (fun _ => sep_mono (fun _ e => e ▸ hm')) hm''⟩

theorem lrat_check_bytes_correct_abi (A : BenchAbi) (hh : A.T.mach.Host)
    {hints : List A.T.toIsa.Hints}
    (M : Compiled A.T A.lt [] [] 0 lratBytesFns hints 2048)
    (hsupp : ∀ f ∈ lratBytesModule.fns, (f.earlyOpt).body.supportsSource A.lt = true)
    (k₀ : Nat) (hc : M.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (ha0 : A.argAt 0 s = cnf_ptr)
    (ha1 : A.argAt 1 s = BitVec.ofNat 64 cnfBytes.length)
    (ha2 : A.argAt 2 s = prf_ptr)
    (ha3 : A.argAt 3 s = BitVec.ofNat 64 prfBytes.length)
    (ha4 : A.argAt 4 s = work_ptr)
    (ha5 : A.argAt 5 s = BitVec.ofNat 64 work_len)
    (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆
      (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      A.entryFrame s ra (M.bound "lrat_check_bytes") ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        (A.retGpr (A.T.mach.data st) = 0 ∨ A.retGpr (A.T.mach.data st) = 1) ∧
        (A.retGpr (A.T.mach.data st) = 1 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        A.calleeSavedOk s (A.T.mach.data st) ∧ A.spRestored s (A.T.mach.data st) ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆
          (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
          A.exitFrame s (M.bound "lrat_check_bytes") ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh "lrat_check_bytes")) :=
  lrat_check_bytes_of_fnspec_abi A hh
    (by simpa [mkLratBytesEnv] using
      (lrat_mk_module_fnspec_abi A hh M hsupp lratCheckBytesSpec lratBytesEnv_sound
        (fun _ _ _ _ _ h => h) k₀ hc hu
        (f := ⟨"lrat_check_bytes", [i64, i64, i64, i64, i64, i64], [i64], lratCheckBytes⟩)
        (by simp [lratBytesModule, lratBytesFns])).2)
    cnf_ptr prf_ptr work_ptr cnfBytes prfBytes work_len
    hcnf hprf hwork s ra R ha0 ha1 ha2 ha3 ha4 ha5 hsp hmem

theorem lrat_check_bytes_unsat_abi (A : BenchAbi) (hh : A.T.mach.Host)
    {hints : List A.T.toIsa.Hints}
    (M : Compiled A.T A.lt [] [] 0 lratBytesFns hints 2048)
    (hsupp : ∀ f ∈ lratBytesModule.fns, (f.earlyOpt).body.supportsSource A.lt = true)
    (k₀ : Nat) (hc : M.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (cnf : CNF Nat) (hvalid : ValidDimacsCnf cnf)
    (cnf_ptr prf_ptr work_ptr : BitVec 64)
    (prfBytes : List UInt8) (work_len : Nat)
    (hcnf : cnf_ptr.toNat + (encodeDimacs cnf).length < 2 ^ 64)
    (hprf : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hwork : work_ptr.toNat + work_len < 2 ^ 64)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (ha0 : A.argAt 0 s = cnf_ptr)
    (ha1 : A.argAt 1 s = BitVec.ofNat 64 (encodeDimacs cnf).length)
    (ha2 : A.argAt 2 s = prf_ptr)
    (ha3 : A.argAt 3 s = BitVec.ofNat 64 prfBytes.length)
    (ha4 : A.argAt 4 s = work_ptr)
    (ha5 : A.argAt 5 s = BitVec.ofNat 64 work_len)
    (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆
      (Eq ((encodeDimacs cnf).At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
        region work_ptr work_len) ⋆
      A.entryFrame s ra (M.bound "lrat_check_bytes") ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st => A.T.mach.pc st = ra ∧
        (A.retGpr (A.T.mach.data st) = 0 ∨ A.retGpr (A.T.mach.data st) = 1) ∧
        (A.retGpr (A.T.mach.data st) = 1 → cnf.Unsat))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh "lrat_check_bytes")) := by
  refine eventually_weaken _ _ _ _ ?_
    (lrat_check_bytes_correct_abi A hh M hsupp k₀ hc hu cnf_ptr prf_ptr work_ptr
      (encodeDimacs cnf) prfBytes work_len hcnf hprf hwork s ra R
      ha0 ha1 ha2 ha3 ha4 ha5 hsp hmem)
  have hparse := parseDimacs_encodeDimacs hvalid
  rintro st ⟨hpc, h01, hu', _⟩
  refine ⟨hpc, h01, fun h1 => ?_⟩
  obtain ⟨cnf', hp', hc'⟩ := hu' h1
  rw [hparse] at hp'
  cases Option.some.inj hp'
  exact hc'

@[expose] def lratBytesArgs (cnfBytes prfBytes : List UInt8) :
    Tup Val [i64, i64, i64, i64, i64, i64] :=
  (nvCnfPtr, BitVec.ofNat 64 cnfBytes.length,
   nvPrfPtr cnfBytes, BitVec.ofNat 64 prfBytes.length,
   nvWorkPtr cnfBytes prfBytes, 512#64, ())

theorem lrat_check_bytes_accepts_abi (A : BenchAbi)
    {hints : List A.T.toIsa.Hints}
    (M : Compiled A.T A.lt [] [] 0 lratBytesFns hints 2048)
    (hsupp : ∀ f ∈ lratBytesModule.fns, (f.earlyOpt).body.supportsSource A.lt = true) :
    Eventually (A.T.mach.step M.host)
      (fun st => A.T.mach.pc st = A.init.ra0 ∧
        A.retGpr (A.T.mach.data st) = 1 ∧ nvBytesCnf.Unsat)
      (A.T.mach.mkState
        (A.init.initState (as := [i64, i64, i64, i64, i64, i64])
          (M.bound "lrat_check_bytes")
          (lratBytesPayload nvDimacsBytes nvLratAcceptBytes)
          (lratBytesArgs nvDimacsBytes nvLratAcceptBytes))
        (A.T.mach.labelAddr M.host "lrat_check_bytes")) := by
  have hfn : A.T.FnSpec M.host "lrat_check_bytes" lratCheckBytesAcceptSpec
      (M.bound "lrat_check_bytes") 0 := by
    simpa [mkLratBytesEnv] using
      (lrat_mk_module_fnspec_abi A M.host M hsupp lratCheckBytesAcceptSpec
        lratBytesAcceptEnv_sound (fun _ _ _ _ _ h => h) 0 M.code_infix_host M.labelsUnique
        (f := ⟨"lrat_check_bytes", [i64, i64, i64, i64, i64, i64], [i64], lratCheckBytes⟩)
        (by simp [lratBytesModule, lratBytesFns])).2
  have hspec : lratCheckBytesAcceptSpec (lratBytesArgs nvDimacsBytes nvLratAcceptBytes)
      ((lratBytesPayload nvDimacsBytes nvLratAcceptBytes).At 0x1000#64)
      (fun rs _ => rs = (1, ()) ∧ nvBytesCnf.Unsat) (fun _ _ _ _ => False) :=
    ⟨nvCnfPtr, nvPrfPtr nvDimacsBytes, nvWorkPtr nvDimacsBytes nvLratAcceptBytes, emp,
      rfl, by simp [nvCnfPtr], by simp [nvPrfPtr, nvCnfPtr],
      by simp [nvWorkPtr, nvPrfPtr, nvCnfPtr],
      by rw [sep_emp]; exact lratBytesPayload_sep _ _ (by simp) (by simp),
      fun _ hu _ => ⟨rfl, hu⟩⟩
  refine A.init.run_fnSpec M hfn (lratBytesPayload nvDimacsBytes nvLratAcceptBytes)
    (lratBytesArgs nvDimacsBytes nvLratAcceptBytes)
    (Nat.le_trans (by simp [lratBytesPayload_length]) A.maxMem_ge)
    (A.assignArgs_i64 6 (by decide)) hspec ?_ A.maxStack_ge
  rintro st (⟨hpc, _, _, ⟨rfl, hu⟩, hrets, _⟩ | ⟨_, _, _, _, hx, _⟩)
  · exact ⟨hpc, A.retGpr_eq_of_retsIn hrets, hu⟩
  · exact hx.elim

theorem lrat_check_bytes_rejects_abi (A : BenchAbi)
    {hints : List A.T.toIsa.Hints}
    (M : Compiled A.T A.lt [] [] 0 lratBytesFns hints 2048)
    (hsupp : ∀ f ∈ lratBytesModule.fns, (f.earlyOpt).body.supportsSource A.lt = true) :
    Eventually (A.T.mach.step M.host)
      (fun st => A.T.mach.pc st = A.init.ra0 ∧ A.retGpr (A.T.mach.data st) = 0)
      (A.T.mach.mkState
        (A.init.initState (as := [i64, i64, i64, i64, i64, i64])
          (M.bound "lrat_check_bytes")
          (lratBytesPayload nvDimacsBytes nvLratRejectBytes)
          (lratBytesArgs nvDimacsBytes nvLratRejectBytes))
        (A.T.mach.labelAddr M.host "lrat_check_bytes")) := by
  have hfn : A.T.FnSpec M.host "lrat_check_bytes" lratCheckBytesRejectSpec
      (M.bound "lrat_check_bytes") 0 := by
    simpa [mkLratBytesEnv] using
      (lrat_mk_module_fnspec_abi A M.host M hsupp lratCheckBytesRejectSpec
        lratBytesRejectEnv_sound (fun _ _ _ _ _ h => h) 0 M.code_infix_host M.labelsUnique
        (f := ⟨"lrat_check_bytes", [i64, i64, i64, i64, i64, i64], [i64], lratCheckBytes⟩)
        (by simp [lratBytesModule, lratBytesFns])).2
  have hspec : lratCheckBytesRejectSpec (lratBytesArgs nvDimacsBytes nvLratRejectBytes)
      ((lratBytesPayload nvDimacsBytes nvLratRejectBytes).At 0x1000#64)
      (fun rs _ => rs = (0, ())) (fun _ _ _ _ => False) :=
    ⟨nvCnfPtr, nvPrfPtr nvDimacsBytes, nvWorkPtr nvDimacsBytes nvLratRejectBytes, emp,
      rfl, by simp [nvCnfPtr], by simp [nvPrfPtr, nvCnfPtr],
      by simp [nvWorkPtr, nvPrfPtr, nvCnfPtr],
      by rw [sep_emp]; exact lratBytesPayload_sep _ _ (by simp) (by simp),
      fun _ _ => rfl⟩
  exact abi_run_ret1_i64 A M hfn (lratBytesPayload nvDimacsBytes nvLratRejectBytes)
    (lratBytesArgs nvDimacsBytes nvLratRejectBytes) 0
    (by simp [lratBytesPayload_length]) (A.assignArgs_i64 6 (by decide)) hspec fun _ _ h => h

end AbiWorkloads

end LeanQbe.T.Examples.BenchmarkCertKit
