module

public import LeanQbe.T.Amd64.KissatFullCert1
public import LeanQbe.T.Examples.Kissat.FullFast
meta import LeanQbe.T.Examples.Kissat.FullFast
meta import LeanQbe.T.Amd64.KissatFullCert1

/-!
# Kissat M2 Unified Fast (`FullFast`) Certificate Slice 1/9 on SysV x64

Reuses the first `12` compiled chunks (`[0, 36)`, `36` functions) of
`KissatFullCert1.cert1` via `FullFast.fastFns_take_36` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFastCert1

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullFast

/-- Slice 1 sub-module (`[0, 36)`, `36` functions). -/
def slice1Mod : Module := { fns := fastFns.take 36 }

theorem chunksMaxBound_take_le {T : Target} {lt : LegalTarget} {exits : List Sym}
    {nX : Nat} : ∀ (n : Nat) (cs : List (CompiledChunk T lt exits nX)),
      chunksMaxBound (cs.take n) ≤ chunksMaxBound cs
  | 0, _ => Nat.zero_le _
  | _ + 1, [] => Nat.zero_le _
  | n + 1, _ :: cs => Nat.max_le.mpr
    ⟨Nat.le_max_left _ _, Nat.le_trans (chunksMaxBound_take_le n cs) (Nat.le_max_right _ _)⟩

theorem slice1_fns_eq :
    slice1Mod.fns = chunksFns (KissatFullCert1.cert1.chunks.take 12) := by
  have hlen : (chunksFns (KissatFullCert1.cert1.chunks.take 12)).length = 36 := by
    t_kernel_rfl
  have h36 : Full.fullFns.take 36 = (Full.fullFns.take 38).take 36 := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  have hcf : chunksFns KissatFullCert1.cert1.chunks =
      chunksFns (KissatFullCert1.cert1.chunks.take 12) ++
        chunksFns (KissatFullCert1.cert1.chunks.drop 12) := by
    rw [← chunksFns_append, List.take_append_drop]
  change fastFns.take 36 = _
  rw [fastFns_take_36, h36]
  change KissatFullCert1.slice1Mod.fns.take 36 = _
  rw [KissatFullCert1.cert1.fns_eq, hcf, List.take_append_of_le_length (by omega),
    ← hlen, List.take_length]

theorem slice1_supportsAll :
    ∀ f ∈ slice1Mod.fns, (f.earlyOpt).body.supportsSource x64LegalTarget = true := by
  intro f hf
  change f ∈ fastFns.take 36 at hf
  rw [fastFns_take_36] at hf
  have h36 : Full.fullFns.take 36 = (Full.fullFns.take 38).take 36 := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  rw [h36] at hf
  exact KissatFullCert1.cert1.supportsAll f (List.mem_of_mem_take hf)

/-- Linked certificate for prefix `[0, 36)` reusing `KissatFullCert1.cert1`. -/
def cert1 :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean slice1Mod [] [] 0 2048 where
  chunks := KissatFullCert1.cert1.chunks.take 12
  linkCheck := by t_kernel_rfl
  fns_eq := slice1_fns_eq
  supportsAll := slice1_supportsAll
  maxBound_le :=
    Nat.le_trans (chunksMaxBound_take_le 12 _) KissatFullCert1.cert1.maxBound_le

end LeanQbe.T.Amd64.KissatFastCert1
