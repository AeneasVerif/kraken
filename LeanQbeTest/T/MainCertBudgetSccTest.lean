module

import LeanQbe.T.MainCertScc
import LeanQbe.T.Notation
import LeanQbe.T.Logic.Rules
import LeanQbeTest.T.MainTest
import LeanQbeTest.T.MainCertSccFixtures
meta import LeanQbeTest.T.MainCertSccFixtures
meta import Lean
meta import LeanQbe.T.MainCertScc
meta import LeanQbeTest.T.RegaLitmusTarget

/-!
# End-to-End Compiled Stack-Budget SCC Tests (`MainLinkScc` + `MainCertScc`)

Tests `compile_linked_budget_scc!` and `link_scc_budget_lfp` using shared helpers from
`MainCertSccFixtures`:
1. Non-uniform compiled mutual recursion (`16 → 80 → 16`), closed `BudgetEnv.lfp_wf_mkSccOp` +
   `LinkedCertScc.recBudgetChunk_sem_of_budgetSemScc` linking, and concrete execution.
2. Per-function `bfn.minEntry` isolation and fail-closed compiler rejections.
3. Preservation of exact acyclic `effFrame + raBytes` via `LinkedCertScc.ofLinkedCert`.
4. Single-line `#print axioms` audit strictly `⊆ [propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.MainCertBudgetSccTest

open LeanQbe.T LeanQbe.T.LinkRec LeanQbe.T.LinkScc
open LeanQbe.T.Notation LeanQbe.T.RegaLitmus LeanQbeTest.T.MainTest
open LeanQbeTest.T.MainCertSccFixtures
open Std Std.ExtHashMap Kraken.Bedrock2.Test

/-! ## 1. Non-Uniform Compiled Mutual Recursion (`16 → 80 → 16`, `112 * d + 16 < 240 * d`) -/

/-- Acyclic leaf helper (`effFrame + raBytes = 8`). -/
def fnInc1B : Fn := tqbe $inc1B(%n:l) -> l {
  %r =l add %n, 1
  ret %r
}

/-- Mutually recursive `fnF(n)` (`1` var live across call → `effFrame + raBytes = 16`). -/
def fnF : Fn := tqbe $f(%n:l) -> l {
  %c =b ceql %n, 0
  jnz %c, {
    ret 1
  }, {
    %n1 =l sub %n, 1
    %r =l call $g(%n1)
    %s =l add %r, %n
    ret %s
  }
}

/-- Heavy mutually recursive `fnG(n)` (`9` live values across call → `effFrame + raBytes = 80`). -/
def fnG : Fn := tqbe $g(%n:l) -> l {
  %c =b ceql %n, 0
  jnz %c, {
    ret 1
  }, {
    %n1 =l sub %n, 1
    %v1 =l add %n, 1
    %v2 =l add %n, 2
    %v3 =l add %n, 3
    %v4 =l add %n, 4
    %v5 =l add %n, 5
    %v6 =l add %n, 6
    %v7 =l add %n, 7
    %v8 =l add %n, 8
    %v9 =l add %n, 9
    %r =l call $h(%n1)
    %a1 =l add %r, %v1
    %a2 =l add %a1, %v2
    %a3 =l add %a2, %v3
    %a4 =l add %a3, %v4
    %a5 =l add %a4, %v5
    %a6 =l add %a5, %v6
    %a7 =l add %a6, %v7
    %a8 =l add %a7, %v8
    %a9 =l add %a8, %v9
    ret %a9
  }
}

/-- Mutually recursive `fnH(n)` (`1` var live across call → `effFrame + raBytes = 16`). -/
def fnH : Fn := tqbe $h(%n:l) -> l {
  %c =b ceql %n, 0
  jnz %c, {
    ret 1
  }, {
    %n1 =l sub %n, 1
    %r =l call $f(%n1)
    %s =l add %r, %n
    ret %s
  }
}

/-- Acyclic top caller (`1` var live across `$f`, exact `effFrame + raBytes = 16`, total `144`). -/
def fnTopB : Fn := tqbe $topB(%n:l) -> l {
  %b =l call $f(%n)
  %s =l add %b, %n
  %r =l call $inc1B(%s)
  ret %r
}

-- Verify exact compiled frame sizes (`8`, `16`, `80`, `16`, `16`).
splice_module_hints cycHints litmusTarget.toIsa LegalTarget.aarch64
  [fnInc1B, fnF, fnG, fnH, fnTopB]

#guard match cycHints with
  | [h0, h1, h2, h3, h4] =>
      compiledFrameBytes fnInc1B h0 == 8 &&
      compiledFrameBytes fnF h1 == 16 &&
      compiledFrameBytes fnG h2 == 80 &&
      compiledFrameBytes fnH h3 == 16 &&
      compiledFrameBytes fnTopB h4 == 16
  | _ => false

def cycBudgetMod : BudgetModule :=
  { fns := [⟨fnInc1B, 8, 8⟩, ⟨fnF, 16, 16⟩, ⟨fnG, 80, 80⟩, ⟨fnH, 16, 16⟩, ⟨fnTopB, 144, 144⟩] }

theorem cycBudgetMod_wf : ∀ f ∈ cycBudgetMod.toModule.fns, f.Wf :=
  wf_of_map_renorm (by t_kernel_rfl)

theorem fnInc1B_wf : fnInc1B.Wf := cycBudgetMod_wf _ (by simp [cycBudgetMod, BudgetModule.toModule])
theorem fnF_wf     : fnF.Wf     := cycBudgetMod_wf _ (by simp [cycBudgetMod, BudgetModule.toModule])
theorem fnG_wf     : fnG.Wf     := cycBudgetMod_wf _ (by simp [cycBudgetMod, BudgetModule.toModule])
theorem fnH_wf     : fnH.Wf     := cycBudgetMod_wf _ (by simp [cycBudgetMod, BudgetModule.toModule])
theorem fnTopB_wf  : fnTopB.Wf  := cycBudgetMod_wf _ (by simp [cycBudgetMod, BudgetModule.toModule])

-- Compile with `chunkSize := 1` (splits `[fnF, fnG, fnH]` into 3 `RecBudgetSubChunk`s)
-- and tight `exportBounds` (`"f" ↦ 128 = 112 * 1 + 16 < 240`).
compile_linked_budget_scc! cycBudgetCert litmusTarget litmusLayout LegalTarget.aarch64
  litmusLabelClean cycBudgetMod 1 (maxBound := 256)
  (exportBounds := [("f", 128), ("g", 192), ("h", 144)])

theorem cycBudgetCert_numChunks : cycBudgetCert.numChunks = 3 := by rfl
theorem cycBudgetCert_inc1B_bound : cycBudgetCert.bound "inc1B" = 0 := by rfl
theorem cycBudgetCert_f_bound : cycBudgetCert.bound "f" = 128 := by rfl
theorem cycBudgetCert_g_bound : cycBudgetCert.bound "g" = 192 := by rfl
theorem cycBudgetCert_h_bound : cycBudgetCert.bound "h" = 144 := by rfl
theorem cycBudgetCert_topB_bound : cycBudgetCert.bound "topB" = 144 := by rfl

-- Prove concrete non-uniform semantics `cyc_f_3` (`128 < 240`) and `cyc_topB_3` (`144`).
private noncomputable abbrev bc0 : Chunk litmusTarget LegalTarget.aarch64 [] 0 :=
  cycBudgetCert.chunks[0]'(by decide)
private noncomputable abbrev bc1 : Chunk litmusTarget LegalTarget.aarch64 [] 0 :=
  cycBudgetCert.chunks[1]'(by decide)
private noncomputable abbrev bc2 : Chunk litmusTarget LegalTarget.aarch64 [] 0 :=
  cycBudgetCert.chunks[2]'(by decide)

private theorem cyc_chunks_eq : cycBudgetCert.chunks = [bc0, bc1, bc2] := rfl

def inc1BSpec : Spec [i64] [i64] := fun (x, ()) m Q _ => Q (x + 1#64, ()) m

private theorem bc0_sem_inc1B :
    ∀ xs m Q X, inc1BSpec xs m Q X → bc0.sem [] botEnv "inc1B" [i64] [i64] xs m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  refine acyc_single_sem (f := fnInc1B) ⟨_, rfl, rfl⟩ rfl rfl rfl (x, ()) m Q X ?_
  dsimp only [Func.wp, fnInc1B]; wp_unfold; exact hQ

private inductive CycIdx | f0 | h1 | g2 | f3 deriving DecidableEq

private def cycRank : CycIdx → Nat | .f0 => 0 | .h1 => 1 | .g2 => 2 | .f3 => 3
private def cycBudgetReq : CycIdx → Nat | .f0 => 16 | .h1 => 32 | .g2 => 112 | .f3 => 128

private def cycSpec : CycIdx → Env
  | .f0 => fun nm as bs xs m Q _ => nm = "f" ∧ ∃ (ha : as = [i64]) (hb : bs = [i64]),
      (ha ▸ xs).1 = 0#64 ∧ Q (hb ▸ (1#64, ())) m
  | .h1 => fun nm as bs xs m Q _ => nm = "h" ∧ ∃ (ha : as = [i64]) (hb : bs = [i64]),
      (ha ▸ xs).1 = 1#64 ∧ Q (hb ▸ (2#64, ())) m
  | .g2 => fun nm as bs xs m Q _ => nm = "g" ∧ ∃ (ha : as = [i64]) (hb : bs = [i64]),
      (ha ▸ xs).1 = 2#64 ∧ Q (hb ▸ (65#64, ())) m
  | .f3 => fun nm as bs xs m Q _ => nm = "f" ∧ ∃ (ha : as = [i64]) (hb : bs = [i64]),
      (ha ▸ xs).1 = 3#64 ∧ Q (hb ▸ (68#64, ())) m

def f3Spec    : Spec [i64] [i64] := fun (n, ()) m Q _ => n = 3#64 ∧ Q (68#64, ()) m
def topB3Spec : Spec [i64] [i64] := fun (n, ()) m Q _ => n = 3#64 ∧ Q (72#64, ()) m

private theorem bc1_sem_f3 :
    ∀ xs m Q X, f3Spec xs m Q X →
      bc1.sem [fnInc1B.sig] (bc0.sem [] botEnv) "f" [i64] [i64] xs m Q X := by
  rintro ⟨n, ⟨⟩⟩ m Q X ⟨rfl, hQ⟩
  let Γ₀ := bc0.sem [] botEnv
  have hcr : ∃ ext bfs hints maxB expB cbr,
      bc1 = Chunk.recBudgetSCC ext bfs hints maxB expB cbr ∧
      bfs = [⟨fnF, 16, 16⟩, ⟨fnG, 80, 80⟩, ⟨fnH, 16, 16⟩] ∧
      maxB = 256 ∧ expB = [("f", 128), ("g", 192), ("h", 144)] :=
    ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl⟩
  rcases hcr with ⟨ext, bfs, hints, maxB, expB, cbr, hceq, hbfs, hmaxB, hexpB⟩; rw [hceq]
  let bfF : BudgetFn := ⟨fnF, 16, 16⟩
  let bfG : BudgetFn := ⟨fnG, 80, 80⟩
  let bfH : BudgetFn := ⟨fnH, 16, 16⟩
  have hsb : 128 ≤ budgetBound expB maxB bfF.toFn.name := by rw [hexpB, hmaxB]; decide
  refine LinkedCertScc.recBudgetChunk_sem_of_budgetSemScc cbr
    (by rw [hbfs]; exact List.mem_cons_self) hsb ?_
  rw [hbfs]
  let BM : BudgetModule := ⟨[bfF, bfG, bfH], externsOfSigs [fnInc1B.sig], []⟩
  refine BudgetEnv.lfp_wf_mkSccOp (lt := InvImage Nat.lt cycRank)
    (InvImage.wf cycRank Nat.lt_wfRel.wf) cycBudgetReq BM
    (BudgetEnv.const Γ₀) (evalFn := fun Γcall _ bfn => Func.wp Γcall bfn.toFn.body)
    budget_wp_mono cycSpec
    (fun idx sb hsb' bfn hbfn Γcall _ hcall _ _ _ xs m' Q' X' hspec => by
      dsimp only [BM, bfF, bfG, bfH] at hbfn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbfn
      cases idx <;> dsimp only [cycSpec] at hspec <;>
        rcases hspec with ⟨hnm, ha, hb, harg, hq⟩ <;>
        rcases hbfn with rfl | rfl | rfl
      all_goals first | exact absurd hnm (by decide) | skip
      · refine ⟨hsb', hsb', ?_⟩; dsimp only [fnF] at xs m' Q' X' harg hq ⊢
        dsimp only [Func.wp]; wp_unfold
        exact ⟨fun _ => hq, fun hne => absurd harg hne⟩
      · dsimp only [cycBudgetReq] at hsb'
        refine ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩
        dsimp only [fnH] at xs m' Q' X' harg hq ⊢; dsimp only [Func.wp]; wp_unfold
        refine ⟨fun h0 => absurd h0 (by rw [harg]; decide), fun _ => ?_⟩; rw [harg]
        exact wp_call_of_spec _ _ (hcall .f0 (by dsimp [InvImage, cycRank]; omega)
          (by dsimp only [cycBudgetReq]; omega) "f" [i64] [i64] (0#64, ()) m'
          (fun r m'' => Q' (r.1 + 1#64, ()) m'') X'
          ⟨by simp [BM, BudgetModule.fnSigs, bfF, fnF, Fn.sig], rfl, rfl, rfl, rfl, hq⟩)
      · dsimp only [cycBudgetReq] at hsb'
        refine ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩
        dsimp only [fnG] at xs m' Q' X' harg hq ⊢; dsimp only [Func.wp]; wp_unfold
        refine ⟨fun h0 => absurd h0 (by rw [harg]; decide), fun _ => ?_⟩; rw [harg]
        exact wp_call_of_spec _ _ (hcall .h1 (by dsimp [InvImage, cycRank]; omega)
          (by dsimp only [cycBudgetReq]; omega) "h" [i64] [i64] (1#64, ()) m'
          (fun r m'' => Q'
            (((((((((r.1 + (2#64 + 1#64)) + (2#64 + 2#64)) + (2#64 + 3#64)) + (2#64 + 4#64)) +
              (2#64 + 5#64)) + (2#64 + 6#64)) + (2#64 + 7#64)) + (2#64 + 8#64)) +
              (2#64 + 9#64), ()) m'') X'
          ⟨by simp [BM, BudgetModule.fnSigs, bfH, fnH, Fn.sig], rfl, rfl, rfl, rfl, hq⟩)
      · dsimp only [cycBudgetReq] at hsb'
        refine ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩
        dsimp only [fnF] at xs m' Q' X' harg hq ⊢; dsimp only [Func.wp]; wp_unfold
        refine ⟨fun h0 => absurd h0 (by rw [harg]; decide), fun _ => ?_⟩; rw [harg]
        exact wp_call_of_spec _ _ (hcall .g2 (by dsimp [InvImage, cycRank]; omega)
          (by dsimp only [cycBudgetReq]; omega) "g" [i64] [i64] (2#64, ()) m'
          (fun r m'' => Q' (r.1 + 3#64, ()) m'') X'
          ⟨by simp [BM, BudgetModule.fnSigs, bfG, fnG, Fn.sig], rfl, rfl, rfl, rfl, hq⟩))
    .f3 128 (Nat.le_refl 128) "f" [i64] [i64] (3#64, ()) m Q X
    ⟨by simp [BM, BudgetModule.fnSigs, bfF, fnF, Fn.sig], rfl, rfl, rfl, rfl, hQ⟩

private theorem cyc_f3_sem :
    ∀ xs m Q X, f3Spec xs m Q X → cycBudgetCert.sem botEnv "f" [i64] [i64] xs m Q X := by
  intro xs m Q X h; dsimp only [LinkedCertScc.sem]; rw [cyc_chunks_eq]
  change semChunks [fnInc1B.sig] (bc0.sem [] botEnv) [bc1, bc2] "f" [i64] [i64] xs m Q X
  exact LinkedCertScc.semChunks_of_head (f := fnF) (by decide) xs m Q X (bc1_sem_f3 xs m Q X h)

private theorem cyc_topB3_sem :
    ∀ xs m Q X, topB3Spec xs m Q X →
      cycBudgetCert.sem botEnv "topB" [i64] [i64] xs m Q X := by
  rintro ⟨n, ⟨⟩⟩ m Q X ⟨rfl, hQ⟩; dsimp only [LinkedCertScc.sem]; rw [cyc_chunks_eq]
  change semChunks [fnF.sig, fnG.sig, fnH.sig, fnInc1B.sig]
    (bc1.sem [fnInc1B.sig] (bc0.sem [] botEnv)) [bc2] "topB" [i64] [i64] (3#64, ()) m Q X
  refine LinkedCertScc.semChunks_of_head (f := fnTopB) (by decide) (3#64, ()) m Q X ?_
  refine acyc_single_sem (f := fnTopB) ⟨_, rfl, rfl⟩ rfl rfl rfl (3#64, ()) m Q X ?_
  dsimp only [Func.wp, fnTopB]
  let Γprev := bc1.sem [fnInc1B.sig] (bc0.sem [] botEnv)
  have hfP : Γprev "f" [i64] [i64] (3#64, ()) m (fun r m' => r = (68#64, ()) ∧ m' = m) X :=
    bc1_sem_f3 (3#64, ()) m _ X ⟨rfl, ⟨rfl, rfl⟩⟩
  have hincP : Γprev "inc1B" [i64] [i64] (71#64, ()) m Q X :=
    Or.inr ⟨by decide, bc0_sem_inc1B (71#64, ()) m Q X hQ⟩
  refine ⟨fun r m' => r = (68#64, ()) ∧ m' = m, X, ⟨by decide, hfP⟩, ?_, fun _ _ _ _ h => h⟩
  rintro ⟨b, ⟨⟩⟩ m' ⟨hr, hm'⟩; obtain rfl : b = 68#64 := (Prod.ext_iff.mp hr).1; subst hm'
  wp_unfold; exact wp_call_of_spec _ _ ⟨by decide, hincP⟩

theorem fnF_litmus_fnSpec :
    litmusTarget.Defined cycBudgetCert.host "f" ∧
      litmusTarget.FnSpec cycBudgetCert.host "f" f3Spec (cycBudgetCert.bound "f") 0 :=
  litmus_fnSpec cycBudgetCert cycBudgetMod_wf
    (f := fnF) (by simp [cycBudgetMod, BudgetModule.toModule]) rfl rfl f3Spec cyc_f3_sem

theorem fnF_3_exec :
    Eventually (litmusTarget.mach.step cycBudgetCert.host)
      (fun st => litmusTarget.mach.pc st = litmusInit.ra0 ∧
        litmusTarget.mach.getGpr (litmusTarget.mach.data st) litmusInit.ret0 = 68#64)
      (litmusTarget.mach.mkState
        (litmusInit.initState (as := [i64]) (cycBudgetCert.bound "f") []
          ((3#64, ()) : Tup Val [i64]))
        (litmusTarget.mach.labelAddr cycBudgetCert.host "f")) :=
  litmus_ret1_exec cycBudgetCert cycBudgetMod_wf
    (f := fnF) (by simp [cycBudgetMod, BudgetModule.toModule]) rfl rfl rfl
    f3Spec cyc_f3_sem ((3#64, ()) : Tup Val [i64]) 68#64 (by decide) ⟨rfl, by decide⟩

theorem fnTopB_3_exec :
    Eventually (litmusTarget.mach.step cycBudgetCert.host)
      (fun st => litmusTarget.mach.pc st = litmusInit.ra0 ∧
        litmusTarget.mach.getGpr (litmusTarget.mach.data st) litmusInit.ret0 = 72#64)
      (litmusTarget.mach.mkState
        (litmusInit.initState (as := [i64]) (cycBudgetCert.bound "topB") []
          ((3#64, ()) : Tup Val [i64]))
        (litmusTarget.mach.labelAddr cycBudgetCert.host "topB")) :=
  litmus_ret1_exec cycBudgetCert cycBudgetMod_wf
    (f := fnTopB) (by simp [cycBudgetMod, BudgetModule.toModule]) rfl rfl rfl
    topB3Spec cyc_topB3_sem ((3#64, ()) : Tup Val [i64]) 72#64 (by decide) ⟨rfl, by decide⟩

/-! ## 2. Per-Fn `minEntry` Isolation & Fail-Closed Compiler Checks -/

/-- Acyclic helper with `effFrame + raBytes = 32` (`3` live values across a dummy or `3` slots). -/
def fnExt32 : Fn := tqbe $ext32(%n:l) -> l {
  %a =l add %n, 1
  %b =l add %n, 2
  %c =l add %n, 3
  %r =l call $inc1B(%n)
  %s1 =l add %a, %b
  %s2 =l add %s1, %c
  %s3 =l add %s2, %r
  ret %s3
}

/-- Sibling A calls external `ext32` (`16 + 32 = 48 ≤ minEntry = 48`) and sibling B. -/
def fnSibA : Fn := tqbe $sibA(%n:l) -> l {
  %c =b ceql %n, 0
  jnz %c, {
    %e =l call $ext32(%n)
    ret %e
  }, {
    %n1 =l sub %n, 1
    %r =l call $sibB(%n1)
    %s =l add %r, %n
    ret %s
  }
}

/-- Sibling B calls only `sibA`; does not inherit `sibA`'s `minEntry = 48` (`minEntry = 16`). -/
def fnSibB : Fn := tqbe $sibB(%n:l) -> l {
  %c =b ceql %n, 0
  jnz %c, {
    ret 1
  }, {
    %n1 =l sub %n, 1
    %r =l call $sibA(%n1)
    %s =l add %r, %n
    ret %s
  }
}

def minEntryIsoMod : BudgetModule :=
  { fns := [⟨fnInc1B, 8, 8⟩, ⟨fnExt32, 32, 32⟩, ⟨fnSibA, 16, 48⟩, ⟨fnSibB, 16, 16⟩] }

-- Succeeds with `sibB.minEntry = 16 < 48` (no SCC-wide bleed).
compile_linked_budget_scc! minEntryIsoCert litmusTarget litmusLayout LegalTarget.aarch64
  litmusLabelClean minEntryIsoMod 1 (maxBound := 256)

theorem minEntryIsoCert_inc1B_bound : minEntryIsoCert.bound "inc1B" = 0 := by rfl
theorem minEntryIsoCert_ext32_bound : minEntryIsoCert.bound "ext32" = 32 := by rfl
-- Fails closed if `fnG` (`effFrame + raBytes = 80`) is given `maxFrame = 72 < 80`.
#guard (compileModuleBudgetRec litmusTarget.toIsa LegalTarget.aarch64
  litmusTarget.frame.raBytes [] [] 0 256
  [⟨fnF, 16, 16⟩, ⟨fnG, 72, 72⟩, ⟨fnH, 16, 16⟩]
  (match cycHints with | [_, h1, h2, h3, _] => [h1, h2, h3] | _ => [])).toOption.isNone
#guard (evalLinkedBudgetSccChunks litmusTarget.toIsa LegalTarget.aarch64
  litmusTarget.frame.raBytes [] [] [] 0
  [⟨fnF, 16, 16⟩, ⟨fnG, 72, 72⟩, ⟨fnH, 16, 16⟩] 2 256 0).toOption.isNone

-- Fails closed if `fnSibA` (`16 + 32 = 48`) is given `minEntry = 40 < 48` below `ext32`.
#guard (evalLinkedBudgetSccChunks litmusTarget.toIsa LegalTarget.aarch64
  litmusTarget.frame.raBytes [] [] [] 0
  [⟨fnInc1B, 8, 8⟩, ⟨fnExt32, 32, 32⟩, ⟨fnSibA, 16, 40⟩, ⟨fnSibB, 16, 16⟩]
  2 256 0).toOption.isNone

/-! ## 3. Acyclic Exact `effFrame + raBytes` Preservation Check -/

def acycBudgetMod : Module := { fns := [fnInc1B, fnExt32] }
-- Notice `fnExt32` calls `fnInc1B` inside an acyclic module; exact bound `32 < 2048`.
compile_linked_chunks! acycPreserveCert litmusTarget litmusLayout LegalTarget.aarch64
  litmusLabelClean acycBudgetMod 2 (maxBound := 2048)

private theorem acycPreserve_calls :
    checkChunksCalls [] [] (acycPreserveCert.chunks.map Chunk.acyc) = true := by rfl

noncomputable def acycPreserve_scc :
    LinkedCertScc litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
      acycBudgetMod :=
  LinkedCertScc.ofLinkedCert acycPreserveCert rfl acycPreserve_calls

theorem acycPreserve_exact : acycPreserve_scc.bound "ext32" = 32 := by rfl

/-! ## 4. Single-Line Axiom Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.link_scc_budget_lfp
#print axioms LeanQbe.T.link_scc_budget_lfp_host
#print axioms LeanQbe.T.linkBudgetRecSubchunks
#print axioms LeanQbe.T.linkChunks_fnSpec
#print axioms LeanQbe.T.LinkedCertScc.recBudgetChunk_sem_of_budgetSemScc
#print axioms cycBudgetCert
#print axioms minEntryIsoCert
#print axioms acycPreserve_scc
#print axioms fnF_litmus_fnSpec
#print axioms fnF_3_exec
#print axioms fnTopB_3_exec

end LeanQbeTest.T.MainCertBudgetSccTest