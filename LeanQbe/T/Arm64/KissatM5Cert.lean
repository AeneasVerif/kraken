module

public import LeanQbe.T.MainCertInline
public import LeanQbe.T.Arm64.KissatM5Cert1
public import LeanQbe.T.Arm64.KissatM5Cert2
public import LeanQbe.T.Arm64.KissatM5Cert3
public import LeanQbe.T.Arm64.KissatM5Cert4
public import LeanQbe.T.Arm64.KissatM5Cert5
public import LeanQbe.T.Arm64.KissatM5Cert6
public import LeanQbe.T.Arm64.KissatM5Cert7
public import LeanQbe.T.Arm64.KissatM5Cert8
public import LeanQbe.T.Arm64.KissatM5Cert9
public import LeanQbe.T.Arm64.KissatM5Cert10
public import LeanQbe.T.Arm64.KissatM5Cert11
public import LeanQbe.T.Arm64.KissatM5Cert12
public import LeanQbe.T.Arm64.KissatM5Cert13
public import LeanQbe.T.Arm64.KissatM5Cert14
public import LeanQbe.T.Arm64.KissatM5Cert15
public import LeanQbe.T.Arm64.KissatM5Cert16
public import LeanQbe.T.Arm64.KissatM5Cert17
public import LeanQbe.T.Arm64.KissatM5Cert18
public import LeanQbe.T.Arm64.KissatM5Cert19
public import LeanQbe.T.Arm64.KissatM5Cert20
public import LeanQbe.T.Arm64.KissatM5Cert21
public import LeanQbe.T.Arm64.KissatM5Cert22
public import LeanQbe.T.Arm64.KissatM5Cert23
public import LeanQbe.T.Arm64.KissatM5Cert24
public import LeanQbe.T.Arm64.KissatM5Cert25
public import LeanQbe.T.Arm64.KissatM5Cert26
public import LeanQbe.T.Arm64.KissatM5Cert27
public import LeanQbe.T.Arm64.KissatM5Cert28
public import LeanQbe.T.Arm64.KissatM5Cert29
public import LeanQbe.T.Arm64.KissatM5Cert30
public import LeanQbe.T.Arm64.KissatM5Cert31
public import LeanQbe.T.Arm64.KissatM5Cert32
public import LeanQbe.T.Arm64.KissatM5Cert33
public import LeanQbe.T.Arm64.KissatM5Cert34
public import LeanQbe.T.Examples.Kissat.FullM5
public import LeanQbe.T.Examples.Kissat.FullM5InlB5
meta import Lean
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM5InlB5

/-!
# KissatM5 (`InlinePolicy.b5`) Native Compilation Certificate on AAPCS64 Arm64

Combines all `34` flat 1-tier slices (`KissatM5Cert1`..`KissatM5Cert34`) via `LinkedCert.append`
into `m5InlB5Cert` over `LeanQbe.T.Examples.Kissat.FullM5InlB5.m5InlB5Mod` (`270` functions) and
transports via `LinkedCert.castModule m5InlB5Mod.eq` into `m5Cert` over
`FullM5.m5Module.optInlinePolicy InlinePolicy.b5`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatM5Cert

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM5
open LeanQbe.T.Examples.Kissat.FullM5InlB5
open LeanQbe.T.Arm64.KissatM5Cert1 LeanQbe.T.Arm64.KissatM5Cert2 LeanQbe.T.Arm64.KissatM5Cert3
open LeanQbe.T.Arm64.KissatM5Cert4 LeanQbe.T.Arm64.KissatM5Cert5 LeanQbe.T.Arm64.KissatM5Cert6
open LeanQbe.T.Arm64.KissatM5Cert7 LeanQbe.T.Arm64.KissatM5Cert8 LeanQbe.T.Arm64.KissatM5Cert9
open LeanQbe.T.Arm64.KissatM5Cert10 LeanQbe.T.Arm64.KissatM5Cert11 LeanQbe.T.Arm64.KissatM5Cert12
open LeanQbe.T.Arm64.KissatM5Cert13 LeanQbe.T.Arm64.KissatM5Cert14 LeanQbe.T.Arm64.KissatM5Cert15
open LeanQbe.T.Arm64.KissatM5Cert16 LeanQbe.T.Arm64.KissatM5Cert17 LeanQbe.T.Arm64.KissatM5Cert18
open LeanQbe.T.Arm64.KissatM5Cert19 LeanQbe.T.Arm64.KissatM5Cert20 LeanQbe.T.Arm64.KissatM5Cert21
open LeanQbe.T.Arm64.KissatM5Cert22 LeanQbe.T.Arm64.KissatM5Cert23 LeanQbe.T.Arm64.KissatM5Cert24
open LeanQbe.T.Arm64.KissatM5Cert25 LeanQbe.T.Arm64.KissatM5Cert26 LeanQbe.T.Arm64.KissatM5Cert27
open LeanQbe.T.Arm64.KissatM5Cert28 LeanQbe.T.Arm64.KissatM5Cert29 LeanQbe.T.Arm64.KissatM5Cert30
open LeanQbe.T.Arm64.KissatM5Cert31 LeanQbe.T.Arm64.KissatM5Cert32 LeanQbe.T.Arm64.KissatM5Cert33
open LeanQbe.T.Arm64.KissatM5Cert34

/-- Prefix sub-module `[0, 18)`. -/
private def pref2Mod : Module := { fns := m5InlB5Fns.take 18 }

/-- Prefix sub-module `[0, 30)`. -/
private def pref3Mod : Module := { fns := m5InlB5Fns.take 30 }

/-- Prefix sub-module `[0, 40)`. -/
private def pref4Mod : Module := { fns := m5InlB5Fns.take 40 }

/-- Prefix sub-module `[0, 52)`. -/
private def pref5Mod : Module := { fns := m5InlB5Fns.take 52 }

/-- Prefix sub-module `[0, 53)`. -/
private def pref6Mod : Module := { fns := m5InlB5Fns.take 53 }

/-- Prefix sub-module `[0, 65)`. -/
private def pref7Mod : Module := { fns := m5InlB5Fns.take 65 }

/-- Prefix sub-module `[0, 72)`. -/
private def pref8Mod : Module := { fns := m5InlB5Fns.take 72 }

/-- Prefix sub-module `[0, 79)`. -/
private def pref9Mod : Module := { fns := m5InlB5Fns.take 79 }

/-- Prefix sub-module `[0, 87)`. -/
private def pref10Mod : Module := { fns := m5InlB5Fns.take 87 }

/-- Prefix sub-module `[0, 94)`. -/
private def pref11Mod : Module := { fns := m5InlB5Fns.take 94 }

/-- Prefix sub-module `[0, 104)`. -/
private def pref12Mod : Module := { fns := m5InlB5Fns.take 104 }

/-- Prefix sub-module `[0, 115)`. -/
private def pref13Mod : Module := { fns := m5InlB5Fns.take 115 }

/-- Prefix sub-module `[0, 122)`. -/
private def pref14Mod : Module := { fns := m5InlB5Fns.take 122 }

/-- Prefix sub-module `[0, 133)`. -/
private def pref15Mod : Module := { fns := m5InlB5Fns.take 133 }

/-- Prefix sub-module `[0, 143)`. -/
private def pref16Mod : Module := { fns := m5InlB5Fns.take 143 }

/-- Prefix sub-module `[0, 155)`. -/
private def pref17Mod : Module := { fns := m5InlB5Fns.take 155 }

/-- Prefix sub-module `[0, 164)`. -/
private def pref18Mod : Module := { fns := m5InlB5Fns.take 164 }

/-- Prefix sub-module `[0, 174)`. -/
private def pref19Mod : Module := { fns := m5InlB5Fns.take 174 }

/-- Prefix sub-module `[0, 175)`. -/
private def pref20Mod : Module := { fns := m5InlB5Fns.take 175 }

/-- Prefix sub-module `[0, 187)`. -/
private def pref21Mod : Module := { fns := m5InlB5Fns.take 187 }

/-- Prefix sub-module `[0, 188)`. -/
private def pref22Mod : Module := { fns := m5InlB5Fns.take 188 }

/-- Prefix sub-module `[0, 198)`. -/
private def pref23Mod : Module := { fns := m5InlB5Fns.take 198 }

/-- Prefix sub-module `[0, 203)`. -/
private def pref24Mod : Module := { fns := m5InlB5Fns.take 203 }

/-- Prefix sub-module `[0, 211)`. -/
private def pref25Mod : Module := { fns := m5InlB5Fns.take 211 }

/-- Prefix sub-module `[0, 217)`. -/
private def pref26Mod : Module := { fns := m5InlB5Fns.take 217 }

/-- Prefix sub-module `[0, 224)`. -/
private def pref27Mod : Module := { fns := m5InlB5Fns.take 224 }

/-- Prefix sub-module `[0, 225)`. -/
private def pref28Mod : Module := { fns := m5InlB5Fns.take 225 }

/-- Prefix sub-module `[0, 227)`. -/
private def pref29Mod : Module := { fns := m5InlB5Fns.take 227 }

/-- Prefix sub-module `[0, 228)`. -/
private def pref30Mod : Module := { fns := m5InlB5Fns.take 228 }

/-- Prefix sub-module `[0, 237)`. -/
private def pref31Mod : Module := { fns := m5InlB5Fns.take 237 }

/-- Prefix sub-module `[0, 248)`. -/
private def pref32Mod : Module := { fns := m5InlB5Fns.take 248 }

/-- Prefix sub-module `[0, 260)`. -/
private def pref33Mod : Module := { fns := m5InlB5Fns.take 260 }

/-- Linked certificate for prefix `[0, 18)`. -/
private noncomputable def pref2Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref2Mod [] [] 0 2048 :=
  cert1.append cert2 (by exact List.take_add (l := m5InlB5Fns) (i := 12) (j := 6))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 30)`. -/
private noncomputable def pref3Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref3Mod [] [] 0 2048 :=
  pref2Cert.append cert3 (by exact List.take_add (l := m5InlB5Fns) (i := 18) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 40)`. -/
private noncomputable def pref4Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref4Mod [] [] 0 2048 :=
  pref3Cert.append cert4 (by exact List.take_add (l := m5InlB5Fns) (i := 30) (j := 10))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 52)`. -/
private noncomputable def pref5Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref5Mod [] [] 0 2048 :=
  pref4Cert.append cert5 (by exact List.take_add (l := m5InlB5Fns) (i := 40) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 53)`. -/
private noncomputable def pref6Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref6Mod [] [] 0 2048 :=
  pref5Cert.append cert6 (by exact List.take_add (l := m5InlB5Fns) (i := 52) (j := 1))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 65)`. -/
private noncomputable def pref7Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref7Mod [] [] 0 2048 :=
  pref6Cert.append cert7 (by exact List.take_add (l := m5InlB5Fns) (i := 53) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 72)`. -/
private noncomputable def pref8Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref8Mod [] [] 0 2048 :=
  pref7Cert.append cert8 (by exact List.take_add (l := m5InlB5Fns) (i := 65) (j := 7))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 79)`. -/
private noncomputable def pref9Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref9Mod [] [] 0 2048 :=
  pref8Cert.append cert9 (by exact List.take_add (l := m5InlB5Fns) (i := 72) (j := 7))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 87)`. -/
private noncomputable def pref10Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref10Mod [] [] 0 2048 :=
  pref9Cert.append cert10 (by exact List.take_add (l := m5InlB5Fns) (i := 79) (j := 8))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 94)`. -/
private noncomputable def pref11Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref11Mod [] [] 0 2048 :=
  pref10Cert.append cert11 (by exact List.take_add (l := m5InlB5Fns) (i := 87) (j := 7))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 104)`. -/
private noncomputable def pref12Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref12Mod [] [] 0 2048 :=
  pref11Cert.append cert12 (by exact List.take_add (l := m5InlB5Fns) (i := 94) (j := 10))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 115)`. -/
private noncomputable def pref13Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref13Mod [] [] 0 2048 :=
  pref12Cert.append cert13 (by exact List.take_add (l := m5InlB5Fns) (i := 104) (j := 11))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 122)`. -/
private noncomputable def pref14Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref14Mod [] [] 0 2048 :=
  pref13Cert.append cert14 (by exact List.take_add (l := m5InlB5Fns) (i := 115) (j := 7))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 133)`. -/
private noncomputable def pref15Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref15Mod [] [] 0 2048 :=
  pref14Cert.append cert15 (by exact List.take_add (l := m5InlB5Fns) (i := 122) (j := 11))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 143)`. -/
private noncomputable def pref16Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref16Mod [] [] 0 2048 :=
  pref15Cert.append cert16 (by exact List.take_add (l := m5InlB5Fns) (i := 133) (j := 10))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 155)`. -/
private noncomputable def pref17Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref17Mod [] [] 0 2048 :=
  pref16Cert.append cert17 (by exact List.take_add (l := m5InlB5Fns) (i := 143) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 164)`. -/
private noncomputable def pref18Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref18Mod [] [] 0 2048 :=
  pref17Cert.append cert18 (by exact List.take_add (l := m5InlB5Fns) (i := 155) (j := 9))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 174)`. -/
private noncomputable def pref19Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref19Mod [] [] 0 2048 :=
  pref18Cert.append cert19 (by exact List.take_add (l := m5InlB5Fns) (i := 164) (j := 10))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 175)`. -/
private noncomputable def pref20Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref20Mod [] [] 0 2048 :=
  pref19Cert.append cert20 (by exact List.take_add (l := m5InlB5Fns) (i := 174) (j := 1))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 187)`. -/
private noncomputable def pref21Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref21Mod [] [] 0 2048 :=
  pref20Cert.append cert21 (by exact List.take_add (l := m5InlB5Fns) (i := 175) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 188)`. -/
private noncomputable def pref22Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref22Mod [] [] 0 2048 :=
  pref21Cert.append cert22 (by exact List.take_add (l := m5InlB5Fns) (i := 187) (j := 1))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 198)`. -/
private noncomputable def pref23Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref23Mod [] [] 0 2048 :=
  pref22Cert.append cert23 (by exact List.take_add (l := m5InlB5Fns) (i := 188) (j := 10))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 203)`. -/
private noncomputable def pref24Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref24Mod [] [] 0 2048 :=
  pref23Cert.append cert24 (by exact List.take_add (l := m5InlB5Fns) (i := 198) (j := 5))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 211)`. -/
private noncomputable def pref25Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref25Mod [] [] 0 2048 :=
  pref24Cert.append cert25 (by exact List.take_add (l := m5InlB5Fns) (i := 203) (j := 8))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 217)`. -/
private noncomputable def pref26Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref26Mod [] [] 0 2048 :=
  pref25Cert.append cert26 (by exact List.take_add (l := m5InlB5Fns) (i := 211) (j := 6))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 224)`. -/
private noncomputable def pref27Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref27Mod [] [] 0 2048 :=
  pref26Cert.append cert27 (by exact List.take_add (l := m5InlB5Fns) (i := 217) (j := 7))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 225)`. -/
private noncomputable def pref28Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref28Mod [] [] 0 2048 :=
  pref27Cert.append cert28 (by exact List.take_add (l := m5InlB5Fns) (i := 224) (j := 1))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 227)`. -/
private noncomputable def pref29Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref29Mod [] [] 0 2048 :=
  pref28Cert.append cert29 (by exact List.take_add (l := m5InlB5Fns) (i := 225) (j := 2))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 228)`. -/
private noncomputable def pref30Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref30Mod [] [] 0 2048 :=
  pref29Cert.append cert30 (by exact List.take_add (l := m5InlB5Fns) (i := 227) (j := 1))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 237)`. -/
private noncomputable def pref31Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref31Mod [] [] 0 2048 :=
  pref30Cert.append cert31 (by exact List.take_add (l := m5InlB5Fns) (i := 228) (j := 9))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 248)`. -/
private noncomputable def pref32Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref32Mod [] [] 0 2048 :=
  pref31Cert.append cert32 (by exact List.take_add (l := m5InlB5Fns) (i := 237) (j := 11))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 260)`. -/
private noncomputable def pref33Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref33Mod [] [] 0 2048 :=
  pref32Cert.append cert33 (by exact List.take_add (l := m5InlB5Fns) (i := 248) (j := 12))
    (by t_kernel_rfl)

/-- Full kernel-checked cert covering all `270` functions in `m5InlB5Mod` on AAPCS64 Arm64. -/
private noncomputable def m5InlB5Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean m5InlB5Mod [] [] 0 2048 :=
  pref33Cert.append cert34
    (by
      dsimp only [pref33Mod, slice34Mod, m5InlB5Fns]
      exact (List.take_append_drop 260 m5InlB5Mod.fns).symm)
    (by t_kernel_rfl)

/-- Full kernel-checked `InlinePolicy.b5` cert over `m5Module.optInlinePolicy InlinePolicy.b5`
on AAPCS64 Arm64, transported in O(1) via `LinkedCert.castModule m5InlB5Mod.eq`. -/
noncomputable def m5Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      (m5Module.optInlinePolicy InlinePolicy.b5) [] [] 0 2048 :=
  m5InlB5Cert.castModule m5InlB5Mod.eq

#print axioms m5Cert
end LeanQbe.T.Arm64.KissatM5Cert
