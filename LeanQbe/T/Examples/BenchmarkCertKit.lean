module

public import LeanQbe.T.BenchmarkCertKit
public import LeanQbe.T.Examples.ChaCha
public import LeanQbe.T.Examples.Bignum
public import LeanQbe.T.Examples.UnionFindLemmas
public import LeanQbe.T.Examples.LitmusProgsLemmas
public import LeanQbe.T.Examples.LinkRec
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.FlatLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Target-Parametric Benchmarks, `FnSpec`s, and Execution Witnesses (`Examples.BenchmarkCertKit`)

Arch-neutral shared data, pure lemmas, spec witnesses, `FnSpec` instantiations, and `TargetInit`
non-vacuous execution proofs for `ChaCha`, `Bignum`, `UnionFind`, `Litmus`, and `LinkRec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.BenchmarkCertKit

open Std Std.ExtHashMap
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

end LeanQbe.T.Examples.BenchmarkCertKit
