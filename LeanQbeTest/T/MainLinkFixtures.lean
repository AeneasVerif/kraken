module

public import LeanQbe.T.MainLink
public import LeanQbe.T.MainLemmas
public import LeanQbe.T.WP
public import LeanQbe.T.Logic.MemLemmas
public import Kraken.Layout
public import Kraken.Separation
import LeanQbe.T.FlatLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Shared Multi-Chunk Linking Fixtures & Specifications (`MainLinkFixtures`)

Target-neutral IR functions, chunks, multi-chunk modules, and semantic specifications
shared between `MainLinkAmd64Test` and `MainLinkArm64Test`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.MainLinkFixtures

open Std Std.ExtHashMap
open LeanQbe.T Kraken

/-! ## 1. Typed-IR functions, chunks, and specs -/

def fnBump : Fn :=
  ⟨"bump", [i64, i64], [i64], fun _ _ (p, d, ()) =>
    .load i64 (.var p) fun v =>
    .let_ ⟨.add i64, (.var v, .var d, ())⟩ fun (s, ()) =>
    .store (.var s) (.var p) (.ret (.var s, ()))⟩

def fnDoubleBump : Fn :=
  ⟨"doubleBump", [i64, i64], [i64], fun _ _ (p, x, ()) =>
    .call "bump" (as := [i64, i64]) (bs := [i64]) (.var p, .var x, ()) fun (r1, ()) =>
    .let_ ⟨.add i64, (.var x, .imm 1#64, ())⟩ fun (x1, ()) =>
    .call "bump" (as := [i64, i64]) (bs := [i64]) (.var p, .var x1, ()) fun (r2, ()) =>
    .let_ ⟨.add i64, (.var r1, .var r2, ())⟩ fun (sum, ()) =>
    .ret (.var sum, ())⟩

def fnTop : Fn :=
  ⟨"top", [i64, i64], [i64], fun _ _ (p, x, ()) =>
    .call "doubleBump" (as := [i64, i64]) (bs := [i64]) (.var p, .var x, ()) fun (r, ()) =>
    .let_ ⟨.add i64, (.var r, .imm 1#64, ())⟩ fun (res, ()) =>
    .ret (.var res, ())⟩

def chunk1Fns : List Fn := [fnBump]
def chunk2Fns : List Fn := [fnDoubleBump]
def chunk3Fns : List Fn := [fnTop]

def twoChunkMod : Module where
  fns := chunk1Fns ++ chunk2Fns

def threeChunkMod : Module where
  fns := chunk1Fns ++ chunk2Fns ++ chunk3Fns

theorem twoChunkMod_acyclic : twoChunkMod.checkAcyclic = true := by t_kernel_rfl
theorem threeChunkMod_acyclic : threeChunkMod.checkAcyclic = true := by t_kernel_rfl

theorem fnBump_wf : fnBump.Wf := by t_wf_reify
theorem fnDoubleBump_wf : fnDoubleBump.Wf := by t_wf_reify
theorem fnTop_wf : fnTop.Wf := by t_wf_reify

theorem twoChunkMod_wf : ∀ f ∈ twoChunkMod.fns, f.Wf := by
  intro f hf
  simp only [twoChunkMod, chunk1Fns, chunk2Fns, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact fnBump_wf
  · exact fnDoubleBump_wf

theorem threeChunkMod_wf : ∀ f ∈ threeChunkMod.fns, f.Wf := by
  intro f hf
  simp only [threeChunkMod, chunk1Fns, chunk2Fns, chunk3Fns, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact fnBump_wf
  · exact fnDoubleBump_wf
  · exact fnTop_wf

def bumpSpec : Spec [i64, i64] [i64] := fun (p, d, ()) m Q _ =>
  ∃ v R, (m =⋆ cell64 p v ⋆ R) ∧ (∀ m', (m' =⋆ cell64 p (v + d) ⋆ R) → Q (v + d, ()) m')

def doubleBumpSpec : Spec [i64, i64] [i64] := fun (p, x, ()) m Q _ =>
  ∃ v R, (m =⋆ cell64 p v ⋆ R) ∧
    (∀ m', (m' =⋆ cell64 p (v + x + (x + 1#64)) ⋆ R) →
      Q ((v + x) + (v + x + (x + 1#64)), ()) m')

def topSpec : Spec [i64, i64] [i64] := fun (p, x, ()) m Q _ =>
  ∃ v R, (m =⋆ cell64 p v ⋆ R) ∧
    (∀ m', (m' =⋆ cell64 p (v + x + (x + 1#64)) ⋆ R) →
      Q ((v + x) + (v + x + (x + 1#64)) + 1#64, ()) m')

def linkΓ : Env
  | "bump", [.bits 64, .bits 64], [.bits 64], args, m, Q, X => bumpSpec args m Q X
  | "doubleBump", [.bits 64, .bits 64], [.bits 64], args, m, Q, X => doubleBumpSpec args m Q X
  | "top", [.bits 64, .bits 64], [.bits 64], args, m, Q, X => topSpec args m Q X
  | _, _, _, _, _, _, _ => False

private theorem bump_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : bumpSpec xs m Q X) : Func.wp linkΓ fnBump.body xs m Q X := by
  rcases xs with ⟨p, d, ⟨⟩⟩
  rcases h with ⟨v, R, hm, hQ⟩
  dsimp only [Func.wp, fnBump, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
  refine ⟨v, loadVal_cell64 hm, ?_⟩
  obtain ⟨hok, hst⟩ := store_cell64 (v + d) hm
  exact ⟨hok, hQ _ hst⟩

private theorem doubleBump_wp {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : doubleBumpSpec xs m Q X) :
    Func.wp linkΓ fnDoubleBump.body xs m Q X := by
  rcases xs with ⟨p, x, ⟨⟩⟩
  rcases h with ⟨v, R, hm, hQ⟩
  dsimp only [Func.wp, fnDoubleBump, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
  refine ⟨fun (r, _) m₁ => r = v + x ∧ (m₁ =⋆ cell64 p (v + x) ⋆ R), X,
    ⟨v, R, hm, fun m' hm' => ⟨rfl, hm'⟩⟩, ?_, fun _ _ _ _ hx => hx⟩
  rintro ⟨r₁, ⟨⟩⟩ m₁ ⟨rfl, hm₁⟩
  refine ⟨fun (r₂, _) m₂ => r₂ = v + x + (x + 1#64) ∧ (m₂ =⋆ cell64 p (v + x + (x + 1#64)) ⋆ R),
    X, ⟨v + x, R, hm₁, fun m' hm' => ⟨rfl, hm'⟩⟩, ?_, fun _ _ _ _ hx => hx⟩
  rintro ⟨r₂, ⟨⟩⟩ m₂ ⟨rfl, hm₂⟩
  exact hQ m₂ hm₂

private theorem top_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : topSpec xs m Q X) : Func.wp linkΓ fnTop.body xs m Q X := by
  rcases xs with ⟨p, x, ⟨⟩⟩
  rcases h with ⟨v, R, hm, hQ⟩
  dsimp only [Func.wp, fnTop, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
  refine ⟨fun (r, _) m₁ => r = (v + x) + (v + x + (x + 1#64)) ∧
      (m₁ =⋆ cell64 p (v + x + (x + 1#64)) ⋆ R),
    X, ⟨v, R, hm, fun m' hm' => ⟨rfl, hm'⟩⟩, ?_, fun _ _ _ _ hx => hx⟩
  rintro ⟨r, ⟨⟩⟩ m₁ ⟨rfl, hm₁⟩
  exact hQ m₁ hm₁

theorem twoChunkMod_wp : ∀ f ∈ twoChunkMod.fns, ∀ xs m Q X,
    linkΓ f.name f.as f.rs xs m Q X → Func.wp linkΓ f.body xs m Q X := by
  intro f hf xs m Q X hΓ
  simp only [twoChunkMod, chunk1Fns, chunk2Fns, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact bump_wp hΓ
  · exact doubleBump_wp hΓ

theorem threeChunkMod_wp : ∀ f ∈ threeChunkMod.fns, ∀ xs m Q X,
    linkΓ f.name f.as f.rs xs m Q X → Func.wp linkΓ f.body xs m Q X := by
  intro f hf xs m Q X hΓ
  simp only [threeChunkMod, chunk1Fns, chunk2Fns, chunk3Fns, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact bump_wp hΓ
  · exact doubleBump_wp hΓ
  · exact top_wp hΓ

def initMemBytes : List UInt8 := bytes64 [10#64]

theorem initMemBytes_len : initMemBytes.length ≤ 8192 := by
  simp [initMemBytes, bytes64_length]

theorem initMemBytes_cell : (cell64 0x1000#64 10#64 ⋆ emp) (initMemBytes.At 0x1000#64) := by
  have h := array64_bytes 0x1000#64 [10#64] (by decide)
  simpa [initMemBytes, array64, array] using h

end LeanQbeTest.T.MainLinkFixtures
