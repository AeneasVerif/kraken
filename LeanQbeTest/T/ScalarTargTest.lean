module

public import LeanQbe.T.Amd64.ScalarTarg
public import LeanQbe.T.MainCertProof
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Notation
public import LeanQbe.T.Logic.Rules
import LeanQbe.T.Logic.MemLemmas
public meta import Lean
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.Amd64.ScalarTarg

/-!
# Verification Suite for Scalar x64 Target Firewall (`x64ScalarTarget`)

Verifies `LeanQbe.T.Amd64.ScalarTarg`:
1. Compiles a sample scalar `T` module (`add_fn` + `loop_fn` with `.load`, `.group` loop,
   cross-function `.call`, `.store`, `.ret`) via `compile_linked_chunks!` over `x64ScalarTarget`
   producing a `LinkedCert` across 2 chunks (`chunkSize = 1`).
2. Proves whole-module `x64ScalarTarget.FnSpec` and concrete `Mem 64` `Eventually` execution
   (`XPost := False`, `rax = 25#64`, `cell64 0x1000#64 25#64`) via `x64ScalarInit`.
3. Audits `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`).
4. Runs a MetaM assertion over `LeanQbe.T.Amd64.ScalarTarg`'s transitive import closure verifying
   zero `IselVec` / `Arm64` / `Kraken.AArch64` modules.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.ScalarTargTest

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Notation Kraken

/-! ## 1. Sample Scalar `T` Module (`add_fn` + `loop_fn`) -/

/-- `add_fn(a, b) = a + b`. -/
def addFn : Fn := tqbe $add_fn(%a:l, %b:l) -> l {
  %s =l add %a, %b
  ret %s
}

/-- `loop_fn(p, n)`: adds `1 + 2 + … + n` into `*p` via `add_fn` and stores/returns the sum. -/
def loopFn : Fn := tqbe $loop_fn(%p:l, %n:l) -> l {
  %acc0 =l load %p
  loop @loop(%i:l = %n, %s:l = %acc0) {
    %w =w trunc %i
    %c =b cnew %w, 0
    jnz %c, {
      %s' =l call $add_fn(%s, %i)
      %i' =l sub %i, 1
      continue @loop(%i', %s')
    }, {
      store l %s, %p
      ret %s
    }
  }
}

def scalarMod : Module :=
  { fns := [addFn, loopFn] }

theorem addFn_wf : addFn.Wf := by t_wf_reify
theorem loopFn_wf : loopFn.Wf := by t_wf_reify

theorem scalarMod_wf : ∀ f ∈ scalarMod.fns, f.Wf := by
  intro f hf
  simp only [scalarMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact addFn_wf
  · exact loopFn_wf

theorem scalarMod_acyclic : scalarMod.checkAcyclic = true := by t_kernel_rfl

theorem scalarMod_legalSig : LegalSigAll x64ScalarLegalTarget scalarMod.fns :=
  legalSigAll_of_check (by t_kernel_rfl)

/-! ## 2. Source Specifications and `Func.wp` Proofs -/

/-- `1 + 2 + … + k` in 64-bit arithmetic. -/
def tri64 : Nat → BitVec 64
  | 0 => 0
  | k + 1 => tri64 k + BitVec.ofNat 64 (k + 1)

private theorem truthy_ofNat_succ {k : Nat} (hk : k + 1 < 2 ^ 32) :
    (BitVec.ofNat 64 (k + 1)).setWidth 32 ≠ 0#32 := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64), Nat.mod_eq_of_lt hk] at this
  omega

private theorem bv64_succ_sub_one (k : Nat) :
    BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k := by grind

def addSpec : Spec [i64, i64] [i64] := fun (a, b, ()) m Q _ =>
  Q (a + b, ()) m

def loopSpec : Spec [i64, i64] [i64] := fun (p, n, ()) m Q _ =>
  n.toNat < 2 ^ 32 ∧ ∃ v0 R, (cell64 p v0 ⋆ R) m ∧
    ∀ m', (cell64 p (v0 + tri64 n.toNat) ⋆ R) m' → Q (v0 + tri64 n.toNat, ()) m'

def scalarΓ : Env
  | "add_fn", [.bits 64, .bits 64], [.bits 64], xs, m, Q, X => addSpec xs m Q X
  | "loop_fn", [.bits 64, .bits 64], [.bits 64], xs, m, Q, X => loopSpec xs m Q X
  | _, _, _, _, _, _, _ => False

theorem scalarΓ_noExit : ∀ f as bs xs m Q X X',
    scalarΓ f as bs xs m Q X → scalarΓ f as bs xs m Q X' := by
  intro f as bs xs m Q X X' h
  unfold scalarΓ at h ⊢
  split at h <;> exact h

private theorem addFn_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : addSpec xs m Q X) : Func.wp scalarΓ addFn.body xs m Q X := by
  rcases xs with ⟨a, b, ⟨⟩⟩
  dsimp only [Func.wp, addFn, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
  exact h

private theorem loopFn_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : loopSpec xs m Q X) : Func.wp scalarΓ loopFn.body xs m Q X := by
  rcases xs with ⟨p, n, ⟨⟩⟩
  rcases h with ⟨hn, v0, R, hm, hQ⟩
  dsimp only [Func.wp, loopFn]
  wp_unfold
  refine ⟨v0, loadVal_cell64 hm, ?_⟩
  refine wp_loop_group
    (fun k ys m' => k ≤ n.toNat ∧ ys.1 = BitVec.ofNat 64 k ∧
      ys.2.1 + tri64 k = v0 + tri64 n.toNat ∧ m' = m)
    (fun J k ⟨i, s, ⟨⟩⟩ m' hlt ⟨hk, hi, hs, hm'⟩ => ?_)
    (fun J hJ => ?_)
  · dsimp only at hi hs hm'; subst hi; rw [hm']
    dsimp only [Blocks.get_here]; wp_unfold
    cases k with
    | zero =>
      refine ⟨fun h0 => by simp at h0, fun _ => ?_⟩
      change s + tri64 0 = v0 + tri64 n.toNat at hs
      have hs' : s = v0 + tri64 n.toNat := by simpa [tri64] using hs
      rw [hs']
      obtain ⟨hok, hm_post⟩ := store_cell64 (v0 + tri64 n.toNat) hm
      exact ⟨hok, hQ _ hm_post⟩
    | succ k' =>
      have ht := truthy_ofNat_succ (k := k') (by omega)
      refine ⟨fun _ => ?_, fun h0 => absurd h0 ht⟩
      refine ⟨fun (r, _) m₁ => r = s + BitVec.ofNat 64 (k' + 1) ∧ m₁ = m, X,
        ⟨rfl, rfl⟩, ?_, fun _ _ _ _ hx => hx⟩
      rintro ⟨r₁, ⟨⟩⟩ m₁ ⟨rfl, rfl⟩
      wp_unfold
      rw [bv64_succ_sub_one]
      refine hlt k' _ _ (by omega) ⟨by omega, rfl, ?_, rfl⟩
      dsimp only
      rw [← hs, tri64]
      ac_rfl
  · wp_unfold
    exact hJ n.toNat (n, v0, ()) m ⟨Nat.le_refl _, by simp, rfl, rfl⟩

theorem scalarMod_wp : ∀ f ∈ scalarMod.fns, ∀ xs m Q X,
    scalarΓ f.name f.as f.rs xs m Q X → Func.wp scalarΓ f.body xs m Q X := by
  intro f hf xs m Q X hΓ
  simp only [scalarMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact addFn_wp hΓ
  · exact loopFn_wp hΓ

/-! ## 3. Chunked Native Compilation Certificate on `x64ScalarTarget` -/

compile_linked_chunks! scalarCert
  x64ScalarTarget x64ScalarLayout x64ScalarLegalTarget x64ScalarLabelClean scalarMod 1

theorem scalarCert_chunks : scalarCert.numChunks = 2 := rfl

theorem scalar_module_fnspec [hh : Host] (k₀ : Nat)
    (hc : scalarCert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ scalarMod.fns) :
    x64ScalarTarget.Defined hh f.name ∧
      x64ScalarTarget.FnSpec hh f.name (scalarΓ f.name f.as f.rs) (scalarCert.bound f.name) 0 :=
  scalarCert.fnSpec_noExit_of_legalSigAll hh scalarΓ k₀ hc hu
    scalarMod_acyclic scalarMod_wf scalarMod_legalSig scalarMod_wp hf
    (scalarΓ_noExit f.name f.as f.rs)

/-! ## 4. Concrete `Mem 64` `Eventually` Execution Witness (`XPost := False`) -/

def initMemBytes : List UInt8 := bytes64 [10#64]

private theorem initMemBytes_len : initMemBytes.length ≤ 8192 := by
  simp [initMemBytes, bytes64_length]

private theorem initMemBytes_cell :
    (cell64 0x1000#64 10#64 ⋆ emp) (initMemBytes.At 0x1000#64) := by
  have h := array64_bytes 0x1000#64 [10#64] (by decide)
  simpa [initMemBytes, array64, array] using h

/-- Concrete `Mem 64` `Eventually` execution witness on `scalarCert.host` (`XPost := False`):
`loop_fn(0x1000, 5)` returns `25#64` (`10 + 15`) and updates `cell64 0x1000#64 25#64`. -/
theorem scalar_loop_run_sep :
    Eventually (x64ScalarTarget.mach.step scalarCert.host)
      (fun st => x64ScalarTarget.mach.pc st = x64ScalarInit.ra0 ∧
        x64ScalarTarget.mach.getGpr (x64ScalarTarget.mach.data st) x64ScalarInit.ret0 = 25#64 ∧
        (x64ScalarTarget.mach.mem (x64ScalarTarget.mach.data st) =⋆
          (cell64 0x1000#64 25#64 ⋆ emp) ⋆
          x64ScalarTarget.Exit x64ScalarInit.sp0 (scalarCert.bound "loop_fn") ⋆ emp))
      (x64ScalarTarget.mach.mkState
        (x64ScalarInit.initState (as := [i64, i64]) (scalarCert.bound "loop_fn") initMemBytes
          (0x1000#64, 5#64, ()))
        (x64ScalarTarget.mach.labelAddr scalarCert.host "loop_fn")) := by
  refine scalarCert.eventually_ret1_sep_i64_of_legalSigAll x64ScalarInit scalarΓ
    scalarMod_acyclic scalarMod_wf scalarMod_legalSig scalarMod_wp
    (f := loopFn) (by simp [scalarMod]) rfl (scalarΓ_noExit "loop_fn" [i64, i64] [i64])
    initMemBytes (0x1000#64, 5#64, ()) 25#64 (cell64 0x1000#64 25#64 ⋆ emp) initMemBytes_len rfl
    (Q := fun rets m' => rets = (25#64, ()) ∧ (cell64 0x1000#64 25#64 ⋆ emp) m') ?_
    (fun _ _ h => h) (by decide)
  refine ⟨by decide, 10#64, emp, initMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  simpa [tri64] using hm'

/-! ## 5. `#print axioms` Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.Amd64.x64ScalarLegalTarget_valid
#print axioms LeanQbe.T.Amd64.x64Scalar_gprSpec
#print axioms LeanQbe.T.Amd64.x64Scalar_frameSpec
#print axioms LeanQbe.T.Amd64.x64ScalarLabelClean
#print axioms LeanQbe.T.Amd64.x64ScalarLayout
#print axioms LeanQbe.T.Amd64.x64ScalarInit
#print axioms LeanQbe.T.Amd64.x64ScalarSupportsOp_checks
#print axioms scalarCert
#print axioms scalar_module_fnspec
#print axioms scalar_loop_run_sep

/-! ## 6. MetaM Import-Closure Firewall Assertion (Zero `IselVec` / `Arm64` / `Kraken.AArch64`) -/

meta section

open Lean

private def isForbiddenBootstrapImport (m : Name) : Bool :=
  let s := m.toString
  (s.splitOn "IselVec").length > 1 ||
  (s.splitOn "Arm64").length > 1 ||
  s.startsWith "Kraken.AArch64"

#eval show MetaM Unit from do
  let scalarEnv ← importModules #[{ module := `LeanQbe.T.Amd64.ScalarTarg }] {}
  let mods := scalarEnv.header.moduleNames
  let bad := mods.filter isForbiddenBootstrapImport
  if !bad.isEmpty then
    throwError "ScalarTarg import closure contains forbidden modules: {bad.toList}"
  if !mods.contains `LeanQbe.T.Amd64.ScalarTarg then
    throwError "ScalarTarg missing from its own imported environment"
  let testMods := (← getEnv).header.moduleNames
  let badTest := testMods.filter isForbiddenBootstrapImport
  if !badTest.isEmpty then
    throwError "ScalarTargTest import closure contains forbidden modules: {badTest.toList}"
  IO.println s!"ScalarTarg import closure OK: {mods.size} modules, 0 IselVec/Arm64/Kraken.AArch64"
  IO.println
    s!"ScalarTargTest import closure OK: {testMods.size} modules, 0 IselVec/Arm64/Kraken.AArch64"

end

end LeanQbeTest.T.ScalarTargTest
