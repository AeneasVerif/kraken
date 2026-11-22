module

public import LeanQbe.T.MainCertProof
public import LeanQbe.T.Arm64.KissatM4Cert1
public import LeanQbe.T.Arm64.KissatM4Cert2
public import LeanQbe.T.Arm64.KissatM4Cert3
public import LeanQbe.T.Arm64.KissatM4Cert4
public import LeanQbe.T.Arm64.KissatM4Cert5
public import LeanQbe.T.Arm64.KissatM4Cert6
public import LeanQbe.T.Arm64.KissatM4Cert7
public import LeanQbe.T.Arm64.KissatM4Cert8
public import LeanQbe.T.Arm64.KissatM4Cert9
public import LeanQbe.T.Arm64.KissatM4Cert10
public import LeanQbe.T.Arm64.KissatM4Cert11
public import LeanQbe.T.Arm64.KissatM4Cert12
public import LeanQbe.T.Arm64.KissatM4Cert13
public import LeanQbe.T.Arm64.KissatM4Cert14
public import LeanQbe.T.Arm64.KissatM4Cert15
public import LeanQbe.T.Arm64.KissatM4Cert16
public import LeanQbe.T.Arm64.KissatM4Cert17
public import LeanQbe.T.Arm64.KissatM4Cert18
public import LeanQbe.T.Arm64.KissatM4Cert19
public import LeanQbe.T.Arm64.KissatM4Cert20
public import LeanQbe.T.Arm64.KissatM4Cert21
public import LeanQbe.T.Arm64.KissatM4Cert22
public import LeanQbe.T.Arm64.KissatM4Cert23
public import LeanQbe.T.Arm64.KissatM4Cert24
public import LeanQbe.T.Arm64.KissatM4Cert25
public import LeanQbe.T.Arm64.KissatM4Cert26
public import LeanQbe.T.Arm64.KissatM4Cert27
public import LeanQbe.T.Examples.Kissat.FullM4
meta import Lean
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM4

/-!
# KissatM4 Native Compilation Certificate on AAPCS64 Arm64

Combines all `27` flat 1-tier slices (`KissatM4Cert1`..`KissatM4Cert27`) via `LinkedCert.append`
into `m4Cert` over `LeanQbe.T.Examples.Kissat.FullM4.m4Module` (`231` functions).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM4Cert

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM4
open LeanQbe.T.Arm64.KissatM4Cert1 LeanQbe.T.Arm64.KissatM4Cert2 LeanQbe.T.Arm64.KissatM4Cert3
open LeanQbe.T.Arm64.KissatM4Cert4 LeanQbe.T.Arm64.KissatM4Cert5 LeanQbe.T.Arm64.KissatM4Cert6
open LeanQbe.T.Arm64.KissatM4Cert7 LeanQbe.T.Arm64.KissatM4Cert8 LeanQbe.T.Arm64.KissatM4Cert9
open LeanQbe.T.Arm64.KissatM4Cert10 LeanQbe.T.Arm64.KissatM4Cert11 LeanQbe.T.Arm64.KissatM4Cert12
open LeanQbe.T.Arm64.KissatM4Cert13 LeanQbe.T.Arm64.KissatM4Cert14 LeanQbe.T.Arm64.KissatM4Cert15
open LeanQbe.T.Arm64.KissatM4Cert16 LeanQbe.T.Arm64.KissatM4Cert17 LeanQbe.T.Arm64.KissatM4Cert18
open LeanQbe.T.Arm64.KissatM4Cert19 LeanQbe.T.Arm64.KissatM4Cert20 LeanQbe.T.Arm64.KissatM4Cert21
open LeanQbe.T.Arm64.KissatM4Cert22 LeanQbe.T.Arm64.KissatM4Cert23 LeanQbe.T.Arm64.KissatM4Cert24
open LeanQbe.T.Arm64.KissatM4Cert25 LeanQbe.T.Arm64.KissatM4Cert26 LeanQbe.T.Arm64.KissatM4Cert27

/-- Prefix sub-module `[0, 24)`. -/
def pref2Mod : Module := { fns := m4Fns.take 24 }

/-- Prefix sub-module `[0, 35)`. -/
def pref3Mod : Module := { fns := m4Fns.take 35 }

/-- Prefix sub-module `[0, 47)`. -/
def pref4Mod : Module := { fns := m4Fns.take 47 }

/-- Prefix sub-module `[0, 48)`. -/
def pref5Mod : Module := { fns := m4Fns.take 48 }

/-- Prefix sub-module `[0, 60)`. -/
def pref6Mod : Module := { fns := m4Fns.take 60 }

/-- Prefix sub-module `[0, 70)`. -/
def pref7Mod : Module := { fns := m4Fns.take 70 }

/-- Prefix sub-module `[0, 81)`. -/
def pref8Mod : Module := { fns := m4Fns.take 81 }

/-- Prefix sub-module `[0, 91)`. -/
def pref9Mod : Module := { fns := m4Fns.take 91 }

/-- Prefix sub-module `[0, 103)`. -/
def pref10Mod : Module := { fns := m4Fns.take 103 }

/-- Prefix sub-module `[0, 112)`. -/
def pref11Mod : Module := { fns := m4Fns.take 112 }

/-- Prefix sub-module `[0, 120)`. -/
def pref12Mod : Module := { fns := m4Fns.take 120 }

/-- Prefix sub-module `[0, 127)`. -/
def pref13Mod : Module := { fns := m4Fns.take 127 }

/-- Prefix sub-module `[0, 139)`. -/
def pref14Mod : Module := { fns := m4Fns.take 139 }

/-- Prefix sub-module `[0, 147)`. -/
def pref15Mod : Module := { fns := m4Fns.take 147 }

/-- Prefix sub-module `[0, 159)`. -/
def pref16Mod : Module := { fns := m4Fns.take 159 }

/-- Prefix sub-module `[0, 160)`. -/
def pref17Mod : Module := { fns := m4Fns.take 160 }

/-- Prefix sub-module `[0, 164)`. -/
def pref18Mod : Module := { fns := m4Fns.take 164 }

/-- Prefix sub-module `[0, 170)`. -/
def pref19Mod : Module := { fns := m4Fns.take 170 }

/-- Prefix sub-module `[0, 175)`. -/
def pref20Mod : Module := { fns := m4Fns.take 175 }

/-- Prefix sub-module `[0, 183)`. -/
def pref21Mod : Module := { fns := m4Fns.take 183 }

/-- Prefix sub-module `[0, 184)`. -/
def pref22Mod : Module := { fns := m4Fns.take 184 }

/-- Prefix sub-module `[0, 188)`. -/
def pref23Mod : Module := { fns := m4Fns.take 188 }

/-- Prefix sub-module `[0, 197)`. -/
def pref24Mod : Module := { fns := m4Fns.take 197 }

/-- Prefix sub-module `[0, 209)`. -/
def pref25Mod : Module := { fns := m4Fns.take 209 }

/-- Prefix sub-module `[0, 221)`. -/
def pref26Mod : Module := { fns := m4Fns.take 221 }

/-- Linked certificate for prefix `[0, 24)`. -/
noncomputable def pref2Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref2Mod [] [] 0 2048 :=
  cert1.append cert2 (by exact List.take_add (l := m4Fns) (i := 12) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 35)`. -/
noncomputable def pref3Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref3Mod [] [] 0 2048 :=
  pref2Cert.append cert3 (by exact List.take_add (l := m4Fns) (i := 24) (j := 11))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 47)`. -/
noncomputable def pref4Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref4Mod [] [] 0 2048 :=
  pref3Cert.append cert4 (by exact List.take_add (l := m4Fns) (i := 35) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 48)`. -/
noncomputable def pref5Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref5Mod [] [] 0 2048 :=
  pref4Cert.append cert5 (by exact List.take_add (l := m4Fns) (i := 47) (j := 1))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 60)`. -/
noncomputable def pref6Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref6Mod [] [] 0 2048 :=
  pref5Cert.append cert6 (by exact List.take_add (l := m4Fns) (i := 48) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 70)`. -/
noncomputable def pref7Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref7Mod [] [] 0 2048 :=
  pref6Cert.append cert7 (by exact List.take_add (l := m4Fns) (i := 60) (j := 10))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 81)`. -/
noncomputable def pref8Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref8Mod [] [] 0 2048 :=
  pref7Cert.append cert8 (by exact List.take_add (l := m4Fns) (i := 70) (j := 11))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 91)`. -/
noncomputable def pref9Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref9Mod [] [] 0 2048 :=
  pref8Cert.append cert9 (by exact List.take_add (l := m4Fns) (i := 81) (j := 10))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 103)`. -/
noncomputable def pref10Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref10Mod [] [] 0 2048 :=
  pref9Cert.append cert10 (by exact List.take_add (l := m4Fns) (i := 91) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 112)`. -/
noncomputable def pref11Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref11Mod [] [] 0 2048 :=
  pref10Cert.append cert11 (by exact List.take_add (l := m4Fns) (i := 103) (j := 9))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 120)`. -/
noncomputable def pref12Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref12Mod [] [] 0 2048 :=
  pref11Cert.append cert12 (by exact List.take_add (l := m4Fns) (i := 112) (j := 8))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 127)`. -/
noncomputable def pref13Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref13Mod [] [] 0 2048 :=
  pref12Cert.append cert13 (by exact List.take_add (l := m4Fns) (i := 120) (j := 7))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 139)`. -/
noncomputable def pref14Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref14Mod [] [] 0 2048 :=
  pref13Cert.append cert14 (by exact List.take_add (l := m4Fns) (i := 127) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 147)`. -/
noncomputable def pref15Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref15Mod [] [] 0 2048 :=
  pref14Cert.append cert15 (by exact List.take_add (l := m4Fns) (i := 139) (j := 8))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 159)`. -/
noncomputable def pref16Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref16Mod [] [] 0 2048 :=
  pref15Cert.append cert16 (by exact List.take_add (l := m4Fns) (i := 147) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 160)`. -/
noncomputable def pref17Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref17Mod [] [] 0 2048 :=
  pref16Cert.append cert17 (by exact List.take_add (l := m4Fns) (i := 159) (j := 1))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 164)`. -/
noncomputable def pref18Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref18Mod [] [] 0 2048 :=
  pref17Cert.append cert18 (by exact List.take_add (l := m4Fns) (i := 160) (j := 4))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 170)`. -/
noncomputable def pref19Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref19Mod [] [] 0 2048 :=
  pref18Cert.append cert19 (by exact List.take_add (l := m4Fns) (i := 164) (j := 6))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 175)`. -/
noncomputable def pref20Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref20Mod [] [] 0 2048 :=
  pref19Cert.append cert20 (by exact List.take_add (l := m4Fns) (i := 170) (j := 5))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 183)`. -/
noncomputable def pref21Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref21Mod [] [] 0 2048 :=
  pref20Cert.append cert21 (by exact List.take_add (l := m4Fns) (i := 175) (j := 8))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 184)`. -/
noncomputable def pref22Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref22Mod [] [] 0 2048 :=
  pref21Cert.append cert22 (by exact List.take_add (l := m4Fns) (i := 183) (j := 1))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 188)`. -/
noncomputable def pref23Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref23Mod [] [] 0 2048 :=
  pref22Cert.append cert23 (by exact List.take_add (l := m4Fns) (i := 184) (j := 4))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 197)`. -/
noncomputable def pref24Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref24Mod [] [] 0 2048 :=
  pref23Cert.append cert24 (by exact List.take_add (l := m4Fns) (i := 188) (j := 9))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 209)`. -/
noncomputable def pref25Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref25Mod [] [] 0 2048 :=
  pref24Cert.append cert25 (by exact List.take_add (l := m4Fns) (i := 197) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for prefix `[0, 221)`. -/
noncomputable def pref26Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean pref26Mod [] [] 0 2048 :=
  pref25Cert.append cert26 (by exact List.take_add (l := m4Fns) (i := 209) (j := 12))
    (by t_kernel_rfl)

/-- Full kernel-checked cert covering all `231` functions in `m4Module` on AAPCS64 Arm64. -/
noncomputable def m4Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean m4Module [] [] 0 2048 :=
  pref26Cert.append cert27 (by exact (List.take_append_drop 221 m4Fns).symm)
    (by t_kernel_rfl)


#print axioms m4Cert
end LeanQbe.T.Arm64.KissatM4Cert
