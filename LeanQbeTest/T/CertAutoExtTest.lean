module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ

/-!
# Auto-Computed Prefix Bounds (`eval_prefix_ext!`) Test on SysV x64

Tests `LeanQbe.T.eval_prefix_ext!` across multi-slice `compile_linked_chunks!` calls with zero
hardcoded stack bounds, linking all slices via `LinkedCert.append` and checking
`checkLinkList x64Layout [] fullCert.chunks = true` with zero `Kraken.AArch64` co-imports.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.CertAutoExtTest

open LeanQbe.T LeanQbe.T.Amd64

def fnInc : Fn :=
  ⟨"inc", [i64, i64], [i64], fun _ _ (p, d, ()) =>
    .load i64 (.var p) fun v =>
    .let_ ⟨.add i64, (.var v, .var d, ())⟩ fun (s, ()) =>
    .store (.var s) (.var p) (.ret (.var s, ()))⟩

def fnScale : Fn :=
  ⟨"scale", [i64], [i64], fun _ _ (x, ()) =>
    .let_ ⟨.add i64, (.var x, .var x, ())⟩ fun (s, ()) =>
    .ret (.var s, ())⟩

def fnStep : Fn :=
  ⟨"step", [i64, i64], [i64], fun _ _ (p, d, ()) =>
    .call "inc" (as := [i64, i64]) (bs := [i64]) (.var p, .var d, ()) fun (r1, ()) =>
    .call "scale" (as := [i64]) (bs := [i64]) (.var d, ()) fun (r2, ()) =>
    .let_ ⟨.add i64, (.var r1, .var r2, ())⟩ fun (s, ()) =>
    .ret (.var s, ())⟩

def fnPair : Fn :=
  ⟨"pair", [i64, i64], [i64], fun _ _ (p, d, ()) =>
    .call "step" (as := [i64, i64]) (bs := [i64]) (.var p, .var d, ()) fun (r1, ()) =>
    .let_ ⟨.add i64, (.var d, .imm 1#64, ())⟩ fun (d1, ()) =>
    .call "step" (as := [i64, i64]) (bs := [i64]) (.var p, .var d1, ()) fun (r2, ()) =>
    .let_ ⟨.add i64, (.var r1, .var r2, ())⟩ fun (s, ()) =>
    .ret (.var s, ())⟩

def fnWrap : Fn :=
  ⟨"wrap", [i64, i64], [i64], fun _ _ (p, d, ()) =>
    .call "pair" (as := [i64, i64]) (bs := [i64]) (.var p, .var d, ()) fun (r, ()) =>
    .let_ ⟨.add i64, (.var r, .imm 7#64, ())⟩ fun (s, ()) =>
    .ret (.var s, ())⟩

def fnMain : Fn :=
  ⟨"main_entry", [i64, i64], [i64], fun _ _ (p, d, ()) =>
    .call "wrap" (as := [i64, i64]) (bs := [i64]) (.var p, .var d, ()) fun (r1, ()) =>
    .call "scale" (as := [i64]) (bs := [i64]) (.var d, ()) fun (r2, ()) =>
    .let_ ⟨.add i64, (.var r1, .var r2, ())⟩ fun (s, ()) =>
    .ret (.var s, ())⟩

def autoFns : List Fn := [fnInc, fnScale, fnStep, fnPair, fnWrap, fnMain]

def slice1Mod : Module := { fns := autoFns.take 2 }
def slice2Mod : Module := { fns := (autoFns.drop 2).take 2 }
def slice3Mod : Module := { fns := autoFns.drop 4 }
def pref2Mod : Module := { fns := autoFns.take 4 }
def fullMod : Module := { fns := autoFns }

compile_linked_chunks! cert1
  x64Target x64Layout x64LegalTarget x64LabelClean slice1Mod 1

eval_prefix_ext! ext1 x64Target x64LegalTarget (autoFns.take 2)

compile_linked_chunks! cert2
  x64Target x64Layout x64LegalTarget x64LabelClean slice2Mod 2 (ext := ext1)

eval_prefix_ext! ext2 x64Target x64LegalTarget ((autoFns.drop 2).take 2)
  (ext := ext1) (maxBound := 1024)

compile_linked_chunks! cert3
  x64Target x64Layout x64LegalTarget x64LabelClean slice3Mod 1
  (ext := ext2) (maxBound := 1024)

def pref2Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref2Mod [] [] 0 2048 :=
  cert1.append cert2 (by exact List.take_add (l := autoFns) (i := 2) (j := 2))
    (by t_kernel_rfl)

def fullCert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean fullMod [] [] 0 2048 :=
  pref2Cert.append cert3 (by exact (List.take_append_drop 4 autoFns).symm)
    (by t_kernel_rfl)

theorem link_check_ok :
    checkLinkList x64Layout [] fullCert.chunks = true := by
  t_kernel_rfl

theorem ext1_len : ext1.length = 2 := rfl
theorem ext2_len : ext2.length = 4 := rfl
theorem fullCert_chunks : fullCert.numChunks = 5 := rfl
theorem fullCert_bound_pos : 0 < fullCert.bound "main_entry" := by decide

#print axioms fullCert
#print axioms link_check_ok

end LeanQbeTest.T.CertAutoExtTest
