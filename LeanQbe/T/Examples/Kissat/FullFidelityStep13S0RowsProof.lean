/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S0Rows
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S0Proof0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S0Proof1

/-!
# Kissat Step-13 Shard `S0` Proof Rows & Parametric `Impl` (`FullFidelityStep13S0RowsProof`)

Exports the `14` inserted `S0` helper specification rows (`fidStep13S0AddRows`), the `3`
replacement rows (`fidStep13S0ReplRows`), combined `fidStep13S0AllRows`, name/signature/`noExit`
alignment theorems, `XFree` lemmas, `17/17` kernel-checked `checkCallsOk` certificates, and
`17/17` callee-parametric `SpecEntry.Impl` lemmas (`0` `import all`, `0` `@[expose]` on
theorems/lemmas, `<= std3`, `XPost`-polymorphic).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S0

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr

@[expose] public section

/-- The `14` inserted `S0` specification rows aligned 1-to-1 with `fidStep13S0AddFns`. -/
def fidStep13S0AddRows : List SpecEntry :=
  [ ⟨"f64u_msb64", [i64], [i64], f64uMsb64Spec, true⟩
  , ⟨"f64u_round_pack", [i64, i64], [i64], f64uPure2Spec, true⟩
  , ⟨"f64u_add", [i64, i64], [i64], f64uPure2Spec, true⟩
  , ⟨"f64u_sub", [i64, i64], [i64], f64uPure2Spec, true⟩
  , ⟨"f64u_mul", [i64, i64], [i64], f64uPure2Spec, true⟩
  , ⟨"f64u_div", [i64, i64], [i64], f64uPure2Spec, true⟩
  , ⟨"f64u_inv_u64", [i64], [i64], f64uPure1Spec, true⟩
  , ⟨"f64u_from_u64", [i64], [i64], f64uPure1Spec, true⟩
  , ⟨"f64u_to_u64", [i64], [i64], f64uPure1Spec, true⟩
  , ⟨"u64_mul128", [i64, i64], [i64, i64], u64Mul128Spec, true⟩
  , ⟨"f64u_log10_u64", [i64], [i64], f64uPure1Spec, true⟩
  , ⟨"f64u_nlogpown", [i64, i64], [i64], f64uPure2Spec, true⟩
  , ⟨"m6_wm4_get", [i64], [i64], m6Wm4GetSpec, true⟩
  , ⟨"m6_wm4_set", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩ ]

/-- The `3` replacement `S0` specification rows aligned 1-to-1 with `fidStep13S0Repls`. -/
def fidStep13S0ReplRows : List SpecEntry :=
  [ ⟨"full_init_hdr", [i64, i64, i64, i64], [], Full.fullInitHdrSpec, true⟩
  , ⟨"m6_hdr_init", [i64], [], s13M6HdrInitSpec, true⟩
  , ⟨"m6_hdr_recompute_tiers_mode", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩ ]

/-- Combined `17`-row `S0` specification table aligned 1-to-1 with `fidStep13S0AllFns`. -/
def fidStep13S0AllRows : List SpecEntry :=
  fidStep13S0AddRows ++ fidStep13S0ReplRows

end

public section

/-! ## 1. Name, Signature, `noExit`, & `XFree` Alignment -/

theorem fidStep13S0AddRows_length : fidStep13S0AddRows.length = 14 := rfl
theorem fidStep13S0ReplRows_length : fidStep13S0ReplRows.length = 3 := rfl
theorem fidStep13S0AllRows_length : fidStep13S0AllRows.length = 17 := rfl

theorem fidStep13S0AddRows_names :
    fidStep13S0AddRows.map SpecEntry.name = fidStep13S0AddNames := rfl

theorem fidStep13S0ReplRows_names :
    fidStep13S0ReplRows.map SpecEntry.name = fidStep13S0ReplNames := rfl

theorem fidStep13S0AllRows_names :
    fidStep13S0AllRows.map SpecEntry.name = fidStep13S0AllNames := rfl

theorem fidStep13S0AddRows_sigs :
    fidStep13S0AddRows.map (fun e => (e.name, e.as, e.rs)) = fidStep13S0AddFns.map Fn.sig := by
  t_kernel_rfl

theorem fidStep13S0ReplRows_sigs :
    fidStep13S0ReplRows.map (fun e => (e.name, e.as, e.rs)) = fidStep13S0Repls.map Fn.sig := by
  t_kernel_rfl

theorem fidStep13S0AllRows_sigs :
    fidStep13S0AllRows.map (fun e => (e.name, e.as, e.rs)) = fidStep13S0AllFns.map Fn.sig := by
  t_kernel_rfl

theorem fidStep13S0AddRows_noExit :
    fidStep13S0AddRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

theorem fidStep13S0ReplRows_noExit :
    fidStep13S0ReplRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

theorem fidStep13S0AllRows_noExit :
    fidStep13S0AllRows.all SpecEntry.noExit = true := by
  t_kernel_rfl

theorem fullInitHdrSpec_s13_xfree : Full.fullInitHdrSpec.XFree := by xfree

theorem m6HdrW2aSpec_s13_xfree (ea rs : List Ty) : (m6HdrW2aSpec ea rs).XFree :=
  fun _ _ _ _ _ h => m6HdrW2aSpec_monoX h

theorem fidStep13S0AllRows_xfree : ∀ e ∈ fidStep13S0AllRows, e.eff.XFree := by
  intro e he
  have hno : e.noExit = true := (List.all_eq_true.mp fidStep13S0AllRows_noExit) e he
  intro _ _ _ _ _ h
  simp only [SpecEntry.eff, hno, ↓reduceIte] at h ⊢
  exact h

/-! ## 2. Per-Function `checkCallsOk` (`17/17`) -/

theorem f64u_msb64_s13_callsOk : f64u_msb64.checkCallsOk [] [] = true := by t_kernel_rfl

theorem f64u_round_pack_s13_callsOk :
    f64u_round_pack.checkCallsOk [("f64u_msb64", [i64], [i64])] [] = true := by t_kernel_rfl

theorem f64u_add_s13_callsOk :
    f64u_add.checkCallsOk [("f64u_round_pack", [i64, i64], [i64])] [] = true := by t_kernel_rfl

theorem f64u_sub_s13_callsOk :
    f64u_sub.checkCallsOk [("f64u_round_pack", [i64, i64], [i64])] [] = true := by t_kernel_rfl

theorem f64u_mul_s13_callsOk :
    f64u_mul.checkCallsOk
      [("f64u_msb64", [i64], [i64]), ("f64u_round_pack", [i64, i64], [i64])] [] = true := by
  t_kernel_rfl

theorem f64u_div_s13_callsOk :
    f64u_div.checkCallsOk
      [("f64u_msb64", [i64], [i64]), ("f64u_round_pack", [i64, i64], [i64])] [] = true := by
  t_kernel_rfl

theorem f64u_inv_u64_s13_callsOk :
    f64u_inv_u64.checkCallsOk
      [("f64u_msb64", [i64], [i64]), ("f64u_round_pack", [i64, i64], [i64])] [] = true := by
  t_kernel_rfl

theorem f64u_from_u64_s13_callsOk :
    f64u_from_u64.checkCallsOk [("f64u_msb64", [i64], [i64])] [] = true := by t_kernel_rfl

theorem f64u_to_u64_s13_callsOk : f64u_to_u64.checkCallsOk [] [] = true := by t_kernel_rfl

theorem u64_mul128_s13_callsOk : u64_mul128.checkCallsOk [] [] = true := by t_kernel_rfl

theorem f64u_log10_u64_s13_callsOk :
    f64u_log10_u64.checkCallsOk
      [ ("f64u_msb64", [i64], [i64])
      , ("u64_mul128", [i64, i64], [i64, i64])
      , ("f64u_round_pack", [i64, i64], [i64]) ] [] = true := by t_kernel_rfl

theorem f64u_nlogpown_s13_callsOk :
    f64u_nlogpown.checkCallsOk
      [ ("f64u_log10_u64", [i64], [i64])
      , ("f64u_mul", [i64, i64], [i64])
      , ("f64u_from_u64", [i64], [i64]) ] [] = true := by t_kernel_rfl

theorem m6_wm4_get_s13_callsOk : m6_wm4_get.checkCallsOk [] [] = true := by t_kernel_rfl

theorem m6_wm4_set_s13_callsOk : m6_wm4_set.checkCallsOk [] [] = true := by t_kernel_rfl

theorem full_init_hdr_s13_callsOk : full_init_hdr.checkCallsOk [] [] = true := by t_kernel_rfl

theorem m6_hdr_init_s13_callsOk : m6_hdr_init.checkCallsOk [] [] = true := by t_kernel_rfl

theorem m6_hdr_recompute_tiers_mode_s13_callsOk :
    m6_hdr_recompute_tiers_mode.checkCallsOk
      [ ("m6_ext_ensure_init", [i64], [])
      , ("f64u_from_u64", [i64], [i64])
      , ("f64u_mul", [i64, i64], [i64])
      , ("f64u_to_u64", [i64], [i64])
      , ("m6_hdr_sync_legacy_tiers", [i64], []) ] [] = true := by t_kernel_rfl

/-! ## 3. Callee-Parametric `SpecEntry.Impl` Lemmas (`17/17`) -/

theorem f64u_msb64_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ f64u_msb64 (fidStep13S0AddRows[0]'(by decide)) :=
  SpecEntry.Impl.of (f64u_msb64_wp Γ)

theorem f64u_round_pack_s13_impl (Γ : Env)
    (hMsb : Γ.Has "f64u_msb64" f64uMsb64Spec) :
    SpecEntry.Impl Γ f64u_round_pack (fidStep13S0AddRows[1]'(by decide)) :=
  SpecEntry.Impl.of (f64u_round_pack_wp Γ (has_f64uMsb64_to_pure hMsb))

theorem f64u_add_s13_impl (Γ : Env)
    (hPack : Γ.Has "f64u_round_pack" f64uPure2Spec) :
    SpecEntry.Impl Γ f64u_add (fidStep13S0AddRows[2]'(by decide)) :=
  SpecEntry.Impl.of (f64u_add_wp Γ hPack)

theorem f64u_sub_s13_impl (Γ : Env)
    (hPack : Γ.Has "f64u_round_pack" f64uPure2Spec) :
    SpecEntry.Impl Γ f64u_sub (fidStep13S0AddRows[3]'(by decide)) :=
  SpecEntry.Impl.of (f64u_sub_wp Γ hPack)

theorem f64u_mul_s13_impl (Γ : Env)
    (hMsb : Γ.Has "f64u_msb64" f64uMsb64Spec)
    (hPack : Γ.Has "f64u_round_pack" f64uPure2Spec) :
    SpecEntry.Impl Γ f64u_mul (fidStep13S0AddRows[4]'(by decide)) :=
  SpecEntry.Impl.of (f64u_mul_wp Γ (has_f64uMsb64_to_pure hMsb) hPack)

theorem f64u_div_s13_impl (Γ : Env)
    (hMsb : Γ.Has "f64u_msb64" f64uMsb64Spec)
    (hPack : Γ.Has "f64u_round_pack" f64uPure2Spec) :
    SpecEntry.Impl Γ f64u_div (fidStep13S0AddRows[5]'(by decide)) :=
  SpecEntry.Impl.of (f64u_div_wp Γ (has_f64uMsb64_to_pure hMsb) hPack)

theorem f64u_inv_u64_s13_impl (Γ : Env)
    (hMsb : Γ.Has "f64u_msb64" f64uMsb64Spec)
    (hPack : Γ.Has "f64u_round_pack" f64uPure2Spec) :
    SpecEntry.Impl Γ f64u_inv_u64 (fidStep13S0AddRows[6]'(by decide)) :=
  SpecEntry.Impl.of (f64u_inv_u64_wp Γ hMsb hPack)

theorem f64u_from_u64_s13_impl (Γ : Env)
    (hMsb : Γ.Has "f64u_msb64" f64uMsb64Spec) :
    SpecEntry.Impl Γ f64u_from_u64 (fidStep13S0AddRows[7]'(by decide)) :=
  SpecEntry.Impl.of (f64u_from_u64_wp Γ (has_f64uMsb64_to_pure hMsb))

theorem f64u_to_u64_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ f64u_to_u64 (fidStep13S0AddRows[8]'(by decide)) :=
  SpecEntry.Impl.of (f64u_to_u64_wp Γ)

theorem u64_mul128_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ u64_mul128 (fidStep13S0AddRows[9]'(by decide)) :=
  SpecEntry.Impl.of (u64_mul128_wp Γ)

theorem f64u_log10_u64_s13_impl (Γ : Env)
    (hMsb : Γ.Has "f64u_msb64" f64uMsb64Spec)
    (hPack : Γ.Has "f64u_round_pack" f64uPure2Spec)
    (hMul128 : Γ.Has "u64_mul128" u64Mul128Spec) :
    SpecEntry.Impl Γ f64u_log10_u64 (fidStep13S0AddRows[10]'(by decide)) :=
  SpecEntry.Impl.of (f64u_log10_u64_wp Γ (has_f64uMsb64_to_pure hMsb) hPack hMul128)

theorem f64u_nlogpown_s13_impl (Γ : Env)
    (hLog : Γ.Has "f64u_log10_u64" f64uPure1Spec)
    (hMul : Γ.Has "f64u_mul" f64uPure2Spec)
    (hFrom : Γ.Has "f64u_from_u64" f64uPure1Spec) :
    SpecEntry.Impl Γ f64u_nlogpown (fidStep13S0AddRows[11]'(by decide)) :=
  SpecEntry.Impl.of (f64u_nlogpown_wp Γ hLog hMul hFrom)

theorem m6_wm4_get_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ m6_wm4_get (fidStep13S0AddRows[12]'(by decide)) :=
  SpecEntry.Impl.of (m6_wm4_get_s13_wp Γ)

theorem m6_wm4_set_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ m6_wm4_set (fidStep13S0AddRows[13]'(by decide)) :=
  SpecEntry.Impl.of (m6_wm4_set_s13_wp Γ)

theorem full_init_hdr_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ full_init_hdr (fidStep13S0ReplRows[0]'(by decide)) :=
  SpecEntry.Impl.of (full_init_hdr_s13_wp Γ)

theorem m6_hdr_init_s13_impl (Γ : Env) :
    SpecEntry.Impl Γ m6_hdr_init (fidStep13S0ReplRows[1]'(by decide)) :=
  SpecEntry.Impl.of (m6_hdr_init_s13_wp Γ)

theorem m6_hdr_recompute_tiers_mode_s13_impl (Γ : Env)
    (hEnsure : Γ.Has "m6_ext_ensure_init" m6ExtEnsureInitSpec)
    (hSync : Γ.Has "m6_hdr_sync_legacy_tiers" (m6HdrW2aSpec [] []))
    (hFrom : Γ.Has "f64u_from_u64" f64uPure1Spec)
    (hMul : Γ.Has "f64u_mul" f64uPure2Spec)
    (hTo : Γ.Has "f64u_to_u64" f64uPure1Spec) :
    SpecEntry.Impl Γ m6_hdr_recompute_tiers_mode (fidStep13S0ReplRows[2]'(by decide)) :=
  SpecEntry.Impl.of (m6_hdr_recompute_tiers_mode_s13_wp Γ hEnsure hSync hFrom hMul hTo)

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S0
