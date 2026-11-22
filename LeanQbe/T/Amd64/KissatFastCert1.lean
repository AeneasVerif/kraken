module

public import LeanQbe.T.Amd64.KissatFullCert1
public import LeanQbe.T.Examples.Kissat.FullFast
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast
meta import LeanQbe.T.Amd64.KissatFullCert1

/-!
# Kissat M2 Unified Fast (`FullFast`) Certificate Slice 1/9 on SysV x64

Reuses the first `10` compiled chunks (`[0, 34)`, `34` functions) of `KissatFullCert1.cert1` via
`FullFast.fastFns_take_36` and compiles `[34, 36)` (`2` functions) on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFastCert1

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFast

/-- Prefix sub-module (`[0, 34)`, `34` functions). -/
def pref1Mod : Module := { fns := fastFns.take 34 }

/-- Tail sub-module (`[34, 36)`, `2` functions). -/
def tail1Mod : Module := { fns := (fastFns.drop 34).take 2 }

/-- Slice 1 sub-module (`[0, 36)`, `36` functions). -/
def slice1Mod : Module := { fns := fastFns.take 36 }

theorem chunksMaxBound_take_le {T : Target} {lt : LegalTarget} {exits : List Sym}
    {nX : Nat} : ∀ (n : Nat) (cs : List (CompiledChunk T lt exits nX)),
      chunksMaxBound (cs.take n) ≤ chunksMaxBound cs
  | 0, _ => Nat.zero_le _
  | _ + 1, [] => Nat.zero_le _
  | n + 1, _ :: cs => Nat.max_le.mpr
    ⟨Nat.le_max_left _ _, Nat.le_trans (chunksMaxBound_take_le n cs) (Nat.le_max_right _ _)⟩

private theorem fastFns_take_34 : fastFns.take 34 = Full.fullFns.take 34 := by
  have h1 : fastFns.take 34 = (fastFns.take 36).take 34 := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  have h2 : Full.fullFns.take 34 = (Full.fullFns.take 36).take 34 := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  rw [h1, fastFns_take_36, ← h2]

theorem pref1_fns_eq :
    pref1Mod.fns = chunksFns (KissatFullCert1.cert1.chunks.take 10) := by
  have hlen : (chunksFns (KissatFullCert1.cert1.chunks.take 10)).length = 34 := by
    t_kernel_rfl
  have h34 : Full.fullFns.take 34 = (Full.fullFns.take 38).take 34 := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  have hcf : chunksFns KissatFullCert1.cert1.chunks =
      chunksFns (KissatFullCert1.cert1.chunks.take 10) ++
        chunksFns (KissatFullCert1.cert1.chunks.drop 10) := by
    rw [← chunksFns_append, List.take_append_drop]
  change fastFns.take 34 = _
  rw [fastFns_take_34, h34]
  change KissatFullCert1.slice1Mod.fns.take 34 = _
  rw [KissatFullCert1.cert1.fns_eq, hcf, List.take_append_of_le_length (by omega),
    ← hlen, List.take_length]

theorem pref1_supportsAll :
    ∀ f ∈ pref1Mod.fns, (f.earlyOpt).body.supportsSource x64LegalTarget = true := by
  intro f hf
  change f ∈ fastFns.take 34 at hf
  rw [fastFns_take_34] at hf
  have h34 : Full.fullFns.take 34 = (Full.fullFns.take 38).take 34 := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  rw [h34] at hf
  exact KissatFullCert1.cert1.supportsAll f (List.mem_of_mem_take hf)

/-- Linked certificate for prefix `[0, 34)` reusing `KissatFullCert1.cert1`. -/
def prefCert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref1Mod [] [] 0 2048 where
  chunks := KissatFullCert1.cert1.chunks.take 10
  linkCheck := by t_kernel_rfl
  fns_eq := pref1_fns_eq
  supportsAll := pref1_supportsAll
  maxBound_le :=
    Nat.le_trans (chunksMaxBound_take_le 10 _) KissatFullCert1.cert1.maxBound_le

-- Auto-computed callee signatures and stack bounds for prefix.
eval_prefix_ext! ext34 x64Target x64LegalTarget (fastFns.take 34)

compile_linked_chunks! tailCert x64Target x64Layout x64LegalTarget x64LabelClean
  tail1Mod 2 (ext := ext34) (maxDirs := 450)

/-- Linked certificate for prefix `[0, 36)` combining `prefCert` and `tailCert`. -/
def cert1 :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean slice1Mod [] [] 0 2048 :=
  prefCert.append tailCert (by exact List.take_add (l := fastFns) (i := 34) (j := 2))
    (by t_kernel_rfl)

end LeanQbe.T.Amd64.KissatFastCert1
