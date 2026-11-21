module

public import LeanQbe.T.Amd64.KissatFastCert1
public import LeanQbe.T.Amd64.KissatFastCert2
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3
meta import LeanQbe.T.Amd64.KissatFastCert1
meta import LeanQbe.T.Amd64.KissatFastCert2

/-!
# Kissat M3 (`FullM3`) Certificate Slice 1/17 on SysV x64

Reuses `KissatFastCert1.cert1` chunks `[0..6]` (`[0, 24)`) and `[8..10]` (`[27, 36)`), compiles
`[24, 27)` (`full_queue_mtf`, `full_tick_rel`, `full_ema_update`), and reuses
`KissatFastCert2.cert2` chunks `[0..2]` (`[36, 47)`), assembling `cert1` over
`FullM3.m3Fns.take 47` (`47` functions; `44` reused).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM3Cert1

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM3

private theorem fullFns_len : Full.fullFns.length = 166 := by t_kernel_rfl
private theorem bveBudgets_len : FullFastBveBudgets.fastBveBudgets_fns.length = 7 := by
  t_kernel_rfl

/-- Stack bounds for `[0, 24)` matching `KissatFastCert1.cert1.chunks.take 7`. -/
def slice0Bounds : List Nat :=
  [8, 8, 40, 56, 72, 104, 104, 152, 8, 8, 8, 8, 8, 8, 72, 168, 40, 88, 56, 120, 8, 72, 24, 8]

/-- Exported callee signatures and stack bounds for prefix `[0, 24)`. -/
def ext0 : List (SigEntry × Nat) :=
  (m3Fns.take 24).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice0Bounds

/-- Mid slice `[24, 27)` (`full_queue_mtf`, `full_tick_rel`, `full_ema_update`, `3` fns). -/
def sliceMidMod : Module := { fns := (m3Fns.drop 24).take 3 }

compile_linked_chunks! certMid x64Target x64Layout x64LegalTarget x64LabelClean
  sliceMidMod 4 (ext := ext0) (maxDirs := 450)

/-- Slice 1 sub-module (`[0, 47)`, `47` functions). -/
def slice1Mod : Module := { fns := m3Fns.take 47 }

theorem chunksMaxBound_take_le {T : Target} {lt : LegalTarget} {exits : List Sym}
    {nX : Nat} : ∀ (n : Nat) (cs : List (CompiledChunk T lt exits nX)),
      chunksMaxBound (cs.take n) ≤ chunksMaxBound cs
  | 0, _ => Nat.zero_le _
  | _ + 1, [] => Nat.zero_le _
  | n + 1, _ :: cs => Nat.max_le.mpr
    ⟨Nat.le_max_left _ _, Nat.le_trans (chunksMaxBound_take_le n cs) (Nat.le_max_right _ _)⟩

theorem chunksMaxBound_drop_le {T : Target} {lt : LegalTarget} {exits : List Sym}
    {nX : Nat} : ∀ (n : Nat) (cs : List (CompiledChunk T lt exits nX)),
      chunksMaxBound (cs.drop n) ≤ chunksMaxBound cs
  | 0, _ => Nat.le_refl _
  | _ + 1, [] => Nat.zero_le _
  | n + 1, _ :: cs =>
    Nat.le_trans (chunksMaxBound_drop_le n cs) (Nat.le_max_right _ _)

private theorem take_append_left {α : Type _} {xs ys : List α} {n : Nat} (h : xs.length = n) :
    (xs ++ ys).take n = xs := by subst h; simp

private theorem drop_append_left {α : Type _} {xs ys : List α} {n : Nat} (h : xs.length = n) :
    (xs ++ ys).drop n = ys := by subst h; simp

private theorem take_append_ge {α : Type _} {xs ys : List α} {n : Nat} (h : xs.length ≤ n) :
    (xs ++ ys).take n = xs ++ ys.take (n - xs.length) := by
  rw [List.take_append, List.take_of_length_le h]

private theorem take_append2_left {α : Type _} {xs ys zs : List α} {n : Nat}
    (h : xs.length + ys.length = n) :
    (xs ++ (ys ++ zs)).take n = xs ++ ys := by
  rw [← List.append_assoc, take_append_left (by simp [h])]

private theorem take_append3_left {α : Type _} {xs ys ws zs : List α} {n : Nat}
    (h : xs.length + ys.length + ws.length = n) :
    (xs ++ (ys ++ (ws ++ zs))).take n = xs ++ ys ++ ws := by
  rw [← List.append_assoc ys ws zs, ← List.append_assoc xs (ys ++ ws) zs,
    ← List.append_assoc xs ys ws, take_append_left (by simp only [List.length_append]; omega)]

private theorem take_append3_ge {α : Type _} {xs ys ws zs : List α} {n : Nat}
    (h : xs.length + ys.length + ws.length ≤ n) :
    (xs ++ (ys ++ (ws ++ zs))).take n =
      xs ++ (ys ++ (ws ++ zs.take (n - (xs.length + ys.length + ws.length)))) := by
  rw [← List.append_assoc ys ws zs, ← List.append_assoc xs (ys ++ ws) zs,
    take_append_ge (by simp only [List.length_append]; omega), List.length_append,
    List.length_append, ← Nat.add_assoc, List.append_assoc, List.append_assoc]

private theorem m3_take_47_eq :
    m3Fns.take 47 =
      Full.fullFns.take 24 ++ ((m3Fns.drop 24).take 3 ++
        ((Full.fullFns.drop 27).take 9 ++
          (FullFastBveBudgets.fastBveBudgets_fns.take 1 ++ (Full.fullFns.drop 37).take 10))) := by
  have h25 : Full.fullFns.take 25 = Full.fullFns.take 24 ++ (Full.fullFns.drop 24).take 1 := by
    simpa using List.take_add (l := Full.fullFns) (i := 24) (j := 1)
  have h26 : (Full.fullFns.drop 26).take 10 =
      (Full.fullFns.drop 26).take 1 ++ (Full.fullFns.drop 27).take 9 := by
    have h := List.take_add (l := Full.fullFns.drop 26) (i := 1) (j := 9)
    simpa [List.drop_drop] using h
  have hp : m3FnsPrefix =
      Full.fullFns.take 24 ++ ((Full.fullFns.drop 24).take 1 ++ [FullM3VivChrono.m3TickRelFn] ++
        (Full.fullFns.drop 26).take 1 ++
        ((Full.fullFns.drop 27).take 9 ++ (FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
          ((Full.fullFns.drop 37).take 10 ++
            ([m3PropLitRawFn, FullM3VivChrono.m3PropLitFn] ++
              FastCore.fastCore_fns.drop 1 ++ (Full.fullFns.drop 50).take 7 ++
              FullFastSched.sched_fns.take 1 ++ (Full.fullFns.drop 58).take 5 ++
              [FullM3VivChrono.m3AnalyzeRsnFn] ++ (Full.fullFns.drop 64).take 47 ++
              [m3ProbeRunFn] ++ (Full.fullFns.drop 112).take 1 ++
              (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
              (Full.fullFns.drop 114).take 5 ++ [FullM3VivChrono.m3VivifyFn] ++
              (Full.fullFns.drop 120).take 1 ++
              (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
              (Full.fullFns.drop 122).take 3 ++ (FullFastSched.sched_fns.drop 1).take 2 ++
              (Full.fullFns.drop 127).take 1))))) := by
    simp only [m3FnsPrefix, h25, h26, List.append_assoc]
  have h24len : (Full.fullFns.take 24).length = 24 := by simp [fullFns_len]
  have h3len : ((Full.fullFns.drop 24).take 1).length +
      ([FullM3VivChrono.m3TickRelFn]).length + ((Full.fullFns.drop 26).take 1).length = 3 := by
    simp [fullFns_len]
  have h9len : ((Full.fullFns.drop 27).take 9).length = 9 := by simp [fullFns_len]
  have h11len : (FullFastBveBudgets.fastBveBudgets_fns.take 1).length +
      ((Full.fullFns.drop 37).take 10).length = 11 := by
    simp [fullFns_len, bveBudgets_len]
  have h24_27 : (m3Fns.drop 24).take 3 =
      (Full.fullFns.drop 24).take 1 ++ [FullM3VivChrono.m3TickRelFn] ++
        (Full.fullFns.drop 26).take 1 := by
    rw [m3Fns, hp]; simp only [List.append_assoc]
    rw [drop_append_left h24len]
    exact take_append3_left h3len
  rw [h24_27, m3Fns, hp]; simp only [List.append_assoc]
  rw [take_append_ge (by omega), h24len, show 47 - 24 = 23 from rfl]
  rw [take_append3_ge (by omega), h3len, show 23 - 3 = 20 from rfl]
  rw [take_append_ge (by omega), h9len, show 20 - 9 = 11 from rfl]
  rw [take_append2_left h11len]

def slice1Chunks :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  KissatFastCert1.cert1.chunks.take 7 ++
    (certMid.chunks ++ (KissatFastCert1.cert1.chunks.drop 8 ++
      KissatFastCert2.cert2.chunks.take 3))

theorem slice1_fns_eq : slice1Mod.fns = chunksFns slice1Chunks := by
  have h7len : (chunksFns (KissatFastCert1.cert1.chunks.take 7)).length = 24 := by t_kernel_rfl
  have h8len : (chunksFns (KissatFastCert1.cert1.chunks.take 8)).length = 27 := by t_kernel_rfl
  have h3len : (chunksFns (KissatFastCert2.cert2.chunks.take 3)).length = 11 := by t_kernel_rfl
  have hcf1a : chunksFns KissatFastCert1.cert1.chunks =
      chunksFns (KissatFastCert1.cert1.chunks.take 7) ++
        chunksFns (KissatFastCert1.cert1.chunks.drop 7) := by
    rw [← chunksFns_append, List.take_append_drop]
  have hcf1b : chunksFns KissatFastCert1.cert1.chunks =
      chunksFns (KissatFastCert1.cert1.chunks.take 8) ++
        chunksFns (KissatFastCert1.cert1.chunks.drop 8) := by
    rw [← chunksFns_append, List.take_append_drop]
  have hcf2 : chunksFns KissatFastCert2.cert2.chunks =
      chunksFns (KissatFastCert2.cert2.chunks.take 3) ++
        chunksFns (KissatFastCert2.cert2.chunks.drop 3) := by
    rw [← chunksFns_append, List.take_append_drop]
  have hcA : chunksFns (KissatFastCert1.cert1.chunks.take 7) = Full.fullFns.take 24 := by
    have h := congrArg (List.take 24) KissatFastCert1.cert1.fns_eq
    change (FullFast.fastFns.take 36).take 24 =
      (chunksFns KissatFastCert1.cert1.chunks).take 24 at h
    rw [FullFast.fastFns_take_36, List.take_take, Nat.min_eq_left (by omega), hcf1a,
      take_append_left h7len] at h
    exact h.symm
  have hcB : chunksFns (KissatFastCert1.cert1.chunks.drop 8) = (Full.fullFns.drop 27).take 9 := by
    have h := congrArg (List.drop 27) KissatFastCert1.cert1.fns_eq
    change (FullFast.fastFns.take 36).drop 27 =
      (chunksFns KissatFastCert1.cert1.chunks).drop 27 at h
    rw [FullFast.fastFns_take_36, List.drop_take, hcf1b, drop_append_left h8len] at h
    simpa using h.symm
  have hcC : chunksFns (KissatFastCert2.cert2.chunks.take 3) =
      FullFastBveBudgets.fastBveBudgets_fns.take 1 ++ (Full.fullFns.drop 37).take 10 := by
    have h := congrArg (List.take 11) KissatFastCert2.cert2.fns_eq
    change ((FullFast.fastFns.drop 36).take 20).take 11 =
      (chunksFns KissatFastCert2.cert2.chunks).take 11 at h
    rw [List.take_take, Nat.min_eq_left (by omega), hcf2, take_append_left h3len] at h
    have hf36 : (FullFast.fastFns.drop 36).take 11 =
        FullFastBveBudgets.fastBveBudgets_fns.take 1 ++ (Full.fullFns.drop 37).take 10 := by
      have h36len : (Full.fullFns.take 36).length = 36 := by simp [fullFns_len]
      have h11 : (FullFastBveBudgets.fastBveBudgets_fns.take 1).length +
          ((Full.fullFns.drop 37).take 10).length = 11 := by
        simp [fullFns_len, bveBudgets_len]
      have hff : FullFast.fastFns = Full.fullFns.take 36 ++
          FullFastBveBudgets.fastBveBudgets_fns.take 1 ++ (Full.fullFns.drop 37).take 10 ++
          FastCore.fastCore_fns ++ (Full.fullFns.drop 50).take 7 ++
          FullFastSched.sched_fns.take 1 ++ (Full.fullFns.drop 58).take 53 ++
          (FullFastBveBudgets.fastBveBudgets_fns.drop 1).take 1 ++
          (Full.fullFns.drop 112).take 1 ++
          (FullFastBveBudgets.fastBveBudgets_fns.drop 2).take 1 ++
          (Full.fullFns.drop 114).take 5 ++
          (FullFastBveBudgets.fastBveBudgets_fns.drop 3).take 1 ++
          (Full.fullFns.drop 120).take 1 ++
          (FullFastBveBudgets.fastBveBudgets_fns.drop 4).take 1 ++
          (Full.fullFns.drop 122).take 3 ++
          (FullFastSched.sched_fns.drop 1).take 2 ++
          (Full.fullFns.drop 127).take 1 ++ FullFast.fastFnsSuffix := by
        simp only [FullFast.fastFns, FullFast.fastFnsPrefix, List.append_assoc]
      rw [hff]; simp only [List.append_assoc]
      rw [drop_append_left h36len]
      exact take_append2_left h11
    exact h.symm.trans hf36
  change m3Fns.take 47 = _
  simp only [slice1Chunks, chunksFns_append]
  rw [← certMid.fns_eq, hcA, hcB, hcC]
  exact m3_take_47_eq

theorem slice1_supportsAll :
    ∀ f ∈ slice1Mod.fns, (f.earlyOpt).body.supportsSource x64LegalTarget = true := by
  intro f hf
  rw [slice1_fns_eq] at hf
  simp only [slice1Chunks, chunksFns_append, List.mem_append] at hf
  rcases hf with h1 | h2 | h3 | h4
  · have hm : f ∈ chunksFns KissatFastCert1.cert1.chunks := by
      rw [← List.take_append_drop 7 KissatFastCert1.cert1.chunks, chunksFns_append]
      exact List.mem_append_left _ h1
    exact KissatFastCert1.cert1.supportsAll f (KissatFastCert1.cert1.fns_eq ▸ hm)
  · exact certMid.supportsAll f (certMid.fns_eq ▸ h2)
  · have hm : f ∈ chunksFns KissatFastCert1.cert1.chunks := by
      rw [← List.take_append_drop 8 KissatFastCert1.cert1.chunks, chunksFns_append]
      exact List.mem_append_right _ h3
    exact KissatFastCert1.cert1.supportsAll f (KissatFastCert1.cert1.fns_eq ▸ hm)
  · have hm : f ∈ chunksFns KissatFastCert2.cert2.chunks := by
      rw [← List.take_append_drop 3 KissatFastCert2.cert2.chunks, chunksFns_append]
      exact List.mem_append_left _ h4
    exact KissatFastCert2.cert2.supportsAll f (KissatFastCert2.cert2.fns_eq ▸ hm)

/-- Linked certificate for prefix `[0, 47)` reusing `KissatFastCert1` + `KissatFastCert2`. -/
def cert1 :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean slice1Mod [] [] 0 2048 where
  chunks := slice1Chunks
  linkCheck := by t_kernel_rfl
  fns_eq := slice1_fns_eq
  supportsAll := slice1_supportsAll
  maxBound_le := by
    simp only [slice1Chunks, chunksMaxBound_append]
    exact Nat.max_le.mpr
      ⟨Nat.le_trans (chunksMaxBound_take_le 7 _) KissatFastCert1.cert1.maxBound_le,
        Nat.max_le.mpr
          ⟨certMid.maxBound_le,
            Nat.max_le.mpr
              ⟨Nat.le_trans (chunksMaxBound_drop_le 8 _) KissatFastCert1.cert1.maxBound_le,
                Nat.le_trans (chunksMaxBound_take_le 3 _) KissatFastCert2.cert2.maxBound_le⟩⟩⟩

end LeanQbe.T.Amd64.KissatM3Cert1
