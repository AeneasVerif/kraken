module

public import LeanQbe.T.Arm64.KissatFastCert1
public import LeanQbe.T.Arm64.KissatFastCert2
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3
meta import LeanQbe.T.Arm64.KissatFastCert1
meta import LeanQbe.T.Arm64.KissatFastCert2

/-!
# Kissat M3 (`FullM3`) Certificate Slice 1/17 on AAPCS64 Arm64

Reuses `KissatFastCert1.cert1` chunks `[0..5]` (`[0, 21)`) and `[8..9]` (`[29, 36)`), compiles
`[21, 29)` (`8` functions including `full_tick_rel`), and reuses `KissatFastCert2.cert2` chunks
`[0..3]` (`[36, 47)`), assembling `cert1` over `FullM3.m3Fns.take 47` (`47` fns; `39` reused).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert1

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FullM3

private theorem fullFns_len : Full.fullFns.length = 166 := by t_kernel_rfl
private theorem bveBudgets_len : FullFastBveBudgets.fastBveBudgets_fns.length = 7 := by
  t_kernel_rfl

/-- Stack bounds for `[0, 21)` matching `KissatFastCert1.cert1.chunks.take 6`. -/
def slice0Bounds : List Nat :=
  [16, 16, 48, 64, 80, 112, 112, 160, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16]

/-- Exported callee signatures and stack bounds for prefix `[0, 21)`. -/
def ext0 : List (SigEntry × Nat) :=
  (m3Fns.take 21).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice0Bounds

/-- Mid slice `[21, 29)` (`8` functions including `full_tick_rel`). -/
def sliceMidMod : Module := { fns := (m3Fns.drop 21).take 8 }

compile_linked_chunks! certMid armTarget armLayout armLegalTarget armLabelClean
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
      Full.fullFns.take 21 ++ ((m3Fns.drop 21).take 8 ++
        ((Full.fullFns.drop 29).take 7 ++
          (FullFastBveBudgets.fastBveBudgets_fns.take 1 ++ (Full.fullFns.drop 37).take 10))) := by
  have h24 : Full.fullFns.take 24 = Full.fullFns.take 21 ++ (Full.fullFns.drop 21).take 3 := by
    simpa using List.take_add (l := Full.fullFns) (i := 21) (j := 3)
  have h25 : Full.fullFns.take 25 = Full.fullFns.take 24 ++ (Full.fullFns.drop 24).take 1 := by
    simpa using List.take_add (l := Full.fullFns) (i := 24) (j := 1)
  have h21_4 : (Full.fullFns.drop 21).take 3 ++ (Full.fullFns.drop 24).take 1 =
      (Full.fullFns.drop 21).take 4 := by
    have h := List.take_add (l := Full.fullFns.drop 21) (i := 3) (j := 1)
    simpa [List.drop_drop] using h.symm
  have h26 : (Full.fullFns.drop 26).take 10 =
      (Full.fullFns.drop 26).take 3 ++ (Full.fullFns.drop 29).take 7 := by
    have h := List.take_add (l := Full.fullFns.drop 26) (i := 3) (j := 7)
    simpa [List.drop_drop] using h
  have hp : m3FnsPrefix =
      Full.fullFns.take 21 ++ ((Full.fullFns.drop 21).take 4 ++ [FullM3VivChrono.m3TickRelFn] ++
        (Full.fullFns.drop 26).take 3 ++
        ((Full.fullFns.drop 29).take 7 ++ (FullFastBveBudgets.fastBveBudgets_fns.take 1 ++
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
    simp only [m3FnsPrefix, h25, h24, h26, List.append_assoc]
    rw [← List.append_assoc ((Full.fullFns.drop 21).take 3), h21_4]
  have h21len : (Full.fullFns.take 21).length = 21 := by simp [fullFns_len]
  have h8len : ((Full.fullFns.drop 21).take 4).length +
      ([FullM3VivChrono.m3TickRelFn]).length + ((Full.fullFns.drop 26).take 3).length = 8 := by
    simp [fullFns_len]
  have h7len : ((Full.fullFns.drop 29).take 7).length = 7 := by simp [fullFns_len]
  have h11len : (FullFastBveBudgets.fastBveBudgets_fns.take 1).length +
      ((Full.fullFns.drop 37).take 10).length = 11 := by
    simp [fullFns_len, bveBudgets_len]
  have h21_29 : (m3Fns.drop 21).take 8 =
      (Full.fullFns.drop 21).take 4 ++ [FullM3VivChrono.m3TickRelFn] ++
        (Full.fullFns.drop 26).take 3 := by
    rw [m3Fns, hp]; simp only [List.append_assoc]
    rw [drop_append_left h21len]
    exact take_append3_left h8len
  rw [h21_29, m3Fns, hp]; simp only [List.append_assoc]
  rw [take_append_ge (by omega), h21len, show 47 - 21 = 26 from rfl]
  rw [take_append3_ge (by omega), h8len, show 26 - 8 = 18 from rfl]
  rw [take_append_ge (by omega), h7len, show 18 - 7 = 11 from rfl]
  rw [take_append2_left h11len]

def slice1Chunks :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  KissatFastCert1.cert1.chunks.take 6 ++
    (certMid.chunks ++ (KissatFastCert1.cert1.chunks.drop 8 ++
      KissatFastCert2.cert2.chunks.take 4))

theorem slice1_fns_eq : slice1Mod.fns = chunksFns slice1Chunks := by
  have h6len : (chunksFns (KissatFastCert1.cert1.chunks.take 6)).length = 21 := by t_kernel_rfl
  have h8len : (chunksFns (KissatFastCert1.cert1.chunks.take 8)).length = 29 := by t_kernel_rfl
  have h4len : (chunksFns (KissatFastCert2.cert2.chunks.take 4)).length = 11 := by t_kernel_rfl
  have hcf1a : chunksFns KissatFastCert1.cert1.chunks =
      chunksFns (KissatFastCert1.cert1.chunks.take 6) ++
        chunksFns (KissatFastCert1.cert1.chunks.drop 6) := by
    rw [← chunksFns_append, List.take_append_drop]
  have hcf1b : chunksFns KissatFastCert1.cert1.chunks =
      chunksFns (KissatFastCert1.cert1.chunks.take 8) ++
        chunksFns (KissatFastCert1.cert1.chunks.drop 8) := by
    rw [← chunksFns_append, List.take_append_drop]
  have hcf2 : chunksFns KissatFastCert2.cert2.chunks =
      chunksFns (KissatFastCert2.cert2.chunks.take 4) ++
        chunksFns (KissatFastCert2.cert2.chunks.drop 4) := by
    rw [← chunksFns_append, List.take_append_drop]
  have hcA : chunksFns (KissatFastCert1.cert1.chunks.take 6) = Full.fullFns.take 21 := by
    have h := congrArg (List.take 21) KissatFastCert1.cert1.fns_eq
    change (FullFast.fastFns.take 36).take 21 =
      (chunksFns KissatFastCert1.cert1.chunks).take 21 at h
    rw [FullFast.fastFns_take_36, List.take_take, Nat.min_eq_left (by omega), hcf1a,
      take_append_left h6len] at h
    exact h.symm
  have hcB : chunksFns (KissatFastCert1.cert1.chunks.drop 8) = (Full.fullFns.drop 29).take 7 := by
    have h := congrArg (List.drop 29) KissatFastCert1.cert1.fns_eq
    change (FullFast.fastFns.take 36).drop 29 =
      (chunksFns KissatFastCert1.cert1.chunks).drop 29 at h
    rw [FullFast.fastFns_take_36, List.drop_take, hcf1b, drop_append_left h8len] at h
    simpa using h.symm
  have hcC : chunksFns (KissatFastCert2.cert2.chunks.take 4) =
      FullFastBveBudgets.fastBveBudgets_fns.take 1 ++ (Full.fullFns.drop 37).take 10 := by
    have h := congrArg (List.take 11) KissatFastCert2.cert2.fns_eq
    change ((FullFast.fastFns.drop 36).take 20).take 11 =
      (chunksFns KissatFastCert2.cert2.chunks).take 11 at h
    rw [List.take_take, Nat.min_eq_left (by omega), hcf2, take_append_left h4len] at h
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
    ∀ f ∈ slice1Mod.fns, (f.earlyOpt).body.supportsSource armLegalTarget = true := by
  intro f hf
  rw [slice1_fns_eq] at hf
  simp only [slice1Chunks, chunksFns_append, List.mem_append] at hf
  rcases hf with h1 | h2 | h3 | h4
  · have hm : f ∈ chunksFns KissatFastCert1.cert1.chunks := by
      rw [← List.take_append_drop 6 KissatFastCert1.cert1.chunks, chunksFns_append]
      exact List.mem_append_left _ h1
    exact KissatFastCert1.cert1.supportsAll f (KissatFastCert1.cert1.fns_eq ▸ hm)
  · exact certMid.supportsAll f (certMid.fns_eq ▸ h2)
  · have hm : f ∈ chunksFns KissatFastCert1.cert1.chunks := by
      rw [← List.take_append_drop 8 KissatFastCert1.cert1.chunks, chunksFns_append]
      exact List.mem_append_right _ h3
    exact KissatFastCert1.cert1.supportsAll f (KissatFastCert1.cert1.fns_eq ▸ hm)
  · have hm : f ∈ chunksFns KissatFastCert2.cert2.chunks := by
      rw [← List.take_append_drop 4 KissatFastCert2.cert2.chunks, chunksFns_append]
      exact List.mem_append_left _ h4
    exact KissatFastCert2.cert2.supportsAll f (KissatFastCert2.cert2.fns_eq ▸ hm)

/-- Linked certificate for prefix `[0, 47)` reusing `KissatFastCert1` + `KissatFastCert2`. -/
def cert1 :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean slice1Mod [] [] 0 2048 where
  chunks := slice1Chunks
  linkCheck := by t_kernel_rfl
  fns_eq := slice1_fns_eq
  supportsAll := slice1_supportsAll
  maxBound_le := by
    simp only [slice1Chunks, chunksMaxBound_append]
    exact Nat.max_le.mpr
      ⟨Nat.le_trans (chunksMaxBound_take_le 6 _) KissatFastCert1.cert1.maxBound_le,
        Nat.max_le.mpr
          ⟨certMid.maxBound_le,
            Nat.max_le.mpr
              ⟨Nat.le_trans (chunksMaxBound_drop_le 8 _) KissatFastCert1.cert1.maxBound_le,
                Nat.le_trans (chunksMaxBound_take_le 4 _) KissatFastCert2.cert2.maxBound_le⟩⟩⟩

end LeanQbe.T.Arm64.KissatM3Cert1
