module

public import LeanQbe.T.Unified.Frontend.Bedrock2
public import LeanQbe.T.Unified.DriverLemmas
public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Logic.MemLemmas
public import Kraken.Bedrock2.Test.Cases
public meta import Lean
import all Kraken.Bedrock2.SemanticsLemmas
import all Kraken.Separation

/-!
# Arch-Free Unified `Bedrock2` Frontend Test (`UnifiedBedrock2Test`)

Verifies arch-isolation (`Kraken.X64`/`Kraken.AArch64`/`Amd64`/`Arm64`-free), `bedrock2Frontend`
direct routing (`caps = {}`, `unified_eq_legacy`), `bedrock2ModMid` over both scalar64 and
aarch64 legal targets, whole-module `bedrock2Module_moduleOk`, pure `std3` verified kernel
contracts (`swap`, `set_bytes`, `mulh`, `use_divmod`, and `bitcopy_store` with `stackalloc`),
and end-to-end `unified` soundness over `refBackend` without importing any ISA backend.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.UnifiedBedrock2Test

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Unified LeanQbe.T.Bedrock2
open Kraken Kraken.Bedrock2 Kraken.Bedrock2.Test

/-! ## 1. Strict Arch-Isolation & Cross-Frontend Import Audit -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.allImportedModuleNames
  let banned : Array Name := #[
    `Kraken.X64, `Kraken.AArch64,
    `LeanQbe.T.Amd64, `LeanQbe.T.Arm64,
    `LeanQbe.T.Unified.Frontend.Bootstrap0,
    `LeanQbe.T.Unified.Frontend.Lcnf
  ]
  for m in mods do
    for b in banned do
      if b.isPrefixOf m then
        throwError s!"arch/frontend leak `{m}` (matches `{b}`) in UnifiedBedrock2Test"
  IO.println s!"arch-free Bedrock2 test closure ok ({mods.size} imported modules, 0 leaks)"

theorem except_of_isOk {ε : Type _} {α : Type _} {x : Except ε α} (d : α)
    (h : x.isOk = true) :
    x = .ok (match x with | .ok v => v | .error _ => d) := by
  cases x with
  | error _ => contradiction
  | ok _ => rfl

theorem except_isOk_getD {ε : Type _} {α : Type _} (x : Except ε α) (d : α)
    (h : x.isOk = true) : x = .ok (x.toOption.getD d) := by
  cases x with
  | error _ => contradiction
  | ok _ => rfl

@[expose] def emptyModuleFallback : Module :=
  { fns := [], externs := [], exits := [] }

@[expose] def modOf (fs : List B2NamedFunc) (exts : List Extern := []) : Module :=
  match bedrock2Module fs exts [] with
  | .ok M => M
  | .error _ => emptyModuleFallback

@[expose] def b2LowerDefault (p : B2NamedFunc) : Fn :=
  match b2NamedFuncToFn? .default p with
  | .ok fn => fn
  | .error _ => ⟨"", [], [], fun _ _ _ => .ret ()⟩

/-! ## 2. Sample Kernels, Bundles & Negative Checks -/

@[expose] def incKrakenFn : Kraken.Bedrock2.Func where
  params := ["x"]
  rets := ["y"]
  body := .set "y" (.op .add (.var "x") (.literal 1))

@[expose] def krakenCallTxFn : Kraken.Bedrock2.Func where
  params := ["x"]
  rets := ["rc"]
  body :=
    .seq (.call ["y"] "inc" [.var "x"])
      (.interact ["rc"] "tx_word" [.var "y"])

@[expose] def krakenStoreTxFn : Kraken.Bedrock2.Func where
  params := ["p", "x"]
  rets := ["rc"]
  body :=
    .seq (.set "y" (.op .add (.var "x") (.literal 1)))
      (.seq (.store .eight (.var "p") (.var "y"))
        (.interact ["rc"] "tx_word" [.var "p"]))

@[expose] def swapFs : List B2NamedFunc := [Examples.swap 64]
@[expose] def setBytesFs : List B2NamedFunc := [Examples.set_bytes]
@[expose] def mulhFs : List B2NamedFunc := [mulh]
@[expose] def divmodFs : List B2NamedFunc := [divmod, useDivmod]
@[expose] def bitcopyFs : List B2NamedFunc := [Examples.bitcopy_store]
@[expose] def bitcopyExtCallees : List (SigEntry × Nat) :=
  [(("__b2_stackalloc", [i64], [i64]), 0), (("__b2_stackfree", [i64, i64], []), 0)]

@[expose] def coreBundle : List B2NamedFunc :=
  [ Examples.swap 64, Examples.set_bytes, divmod, useDivmod, mulh,
    sum, wide, absdiff ]

@[expose] def txBundle : List B2NamedFunc :=
  [ ("inc", incKrakenFn), ("krakenCallTxFn", krakenCallTxFn),
    ("krakenStoreTxFn", krakenStoreTxFn) ]

@[expose] def fullBundle : List B2NamedFunc :=
  coreBundle ++ [stackNested, Examples.bitcopy_store] ++ txBundle

@[expose] def coreMod : Module := modOf coreBundle
@[expose] def stackMod : Module := modOf [stackNested, Examples.bitcopy_store] bedrock2StackExterns

theorem fib_rejected :
    (bedrock2Frontend.lower.run Kraken.Bedrock2.Test.fib).toOption.isNone = true := by
  rfl

theorem bedrock2Frontend_caps_empty (p : B2NamedFunc) :
    bedrock2Frontend.caps p = {} :=
  bedrock2Frontend_caps .default p

theorem bedrock2Frontend_route_direct (p : B2NamedFunc) :
    route (bedrock2Frontend.caps p) = .direct :=
  bedrock2Frontend_direct .default p

theorem bedrock2Frontend_unified_eq (t : LegalTarget) (B : Backend.{0}) (p : B2NamedFunc) :
    (unified bedrock2Frontend t B).run p =
      bindE (bedrock2Frontend.lower.run p) fun q => bindE (legacyMid t q) B.lower :=
  bedrock2Frontend_unified_eq_legacy .default t B p

theorem coreBundle_namesValid : Bedrock2NamesValid .default bedrock2ExtEmpty coreBundle :=
  bedrock2NamesValid_empty (by decide)

theorem stackBundle_namesValid :
    Bedrock2NamesValid .default bedrock2ExtEmpty [stackNested, Examples.bitcopy_store] :=
  bedrock2NamesValid_empty (by decide)

theorem coreMod_ok : bedrock2Module coreBundle [] [] = .ok coreMod := by
  exact except_of_isOk emptyModuleFallback (by decide)

theorem coreMod_acyclic : coreMod.checkAcyclic = true := by
  decide

theorem coreMod_moduleOk :
    ModuleOk (bedrock2Env .default bedrock2ExtEmpty coreBundle) coreMod :=
  bedrock2Module_moduleOk coreMod_ok coreMod_acyclic coreBundle_namesValid

theorem stackMod_ok :
    bedrock2Module [stackNested, Examples.bitcopy_store] bedrock2StackExterns [] =
      .ok stackMod := by
  exact except_of_isOk emptyModuleFallback (by decide)

theorem stackMod_acyclic : stackMod.checkAcyclic = true := by
  decide

theorem stackMod_moduleOk :
    ModuleOk (bedrock2Env .default bedrock2ExtEmpty [stackNested, Examples.bitcopy_store])
      stackMod :=
  bedrock2Module_moduleOk stackMod_ok stackMod_acyclic stackBundle_namesValid

/-! ## 3. Shared `bedrock2ModMid` over Both `scalar64` and `aarch64` Legal Targets -/

theorem fullBundle_scalar64_mid_ok :
    (bedrock2ModMid LegalTarget.scalar64 fullBundle).isOk = true := by
  t_kernel_rfl

theorem fullBundle_aarch64_mid_ok :
    (bedrock2ModMid LegalTarget.aarch64 fullBundle).isOk = true := by
  t_kernel_rfl

theorem coreBundle_scalar64_mid_sound {qs : List Fn}
    (h : bedrock2ModMid LegalTarget.scalar64 coreBundle = .ok qs) :
    ∀ q ∈ qs, ∃ p ∈ coreBundle,
      (bedrock2Frontend.lower ≫ midEnd LegalTarget.scalar64).run p = .ok q ∧
      ssa.Ok q ∧
      ssa.Sat q ((bedrock2Frontend.lower ≫ midEnd LegalTarget.scalar64).tr p
        (B2Spec.ofEnv bedrock2ExtEmpty coreBundle)) :=
  bedrock2ModMid_ofEnv_sound LegalTarget.scalar64 bedrock2ExtEmpty coreBundle (by decide) qs
    .default h

theorem coreBundle_aarch64_mid_sound {qs : List Fn}
    (h : bedrock2ModMid LegalTarget.aarch64 coreBundle = .ok qs) :
    ∀ q ∈ qs, ∃ p ∈ coreBundle,
      (bedrock2Frontend.lower ≫ midEnd LegalTarget.aarch64).run p = .ok q ∧
      ssa.Ok q ∧
      ssa.Sat q ((bedrock2Frontend.lower ≫ midEnd LegalTarget.aarch64).tr p
        (B2Spec.ofEnv bedrock2ExtEmpty coreBundle)) :=
  bedrock2ModMid_ofEnv_sound LegalTarget.aarch64 bedrock2ExtEmpty coreBundle (by decide) qs
    .default h

/-! ## 4. Pure-`std3` Operational Proofs (`mulh`, `useDivmod`, `bitcopy_store`) -/

theorem mulh_exec (x y : BitVec 64) (m0 : Mem 64) :
    Exec bedrock2ExtEmpty mulhFs 0 mulh.2.body [] m0
      ((∅ : Locals 64).insertMany (mulh.2.params.zip [x, y]))
      (fun _ m' l' => ∃ retvs, getMany l' mulh.2.rets = some retvs ∧
        ∀ resTup : Tup Val (List.replicate 2 i64),
          Bedrock2.tupToList resTup = retvs →
          resTup = (interpBinop .mulhuu x y, x * y, ()) ∧ m' = m0) := by
  refine Exec.seq _ _ 0 [] m0 _ _
    (fun t' m' l' => t' = [] ∧ m' = m0 ∧ l'["h"]? = some (interpBinop .mulhuu x y) ∧
      l'["x"]? = some x ∧ l'["y"]? = some y) ?_ ?_
  · exact Exec.set "h" (.op .mulhuu (.var "x") (.var "y")) 0 [] m0 _ _
      (interpBinop .mulhuu x y)
      (by simp [mulh, Expr.eval, insertMany_cons, insertMany_nil])
      ⟨rfl, rfl, by simp [mulh, insertMany_cons, insertMany_nil],
        by simp [mulh, insertMany_cons, insertMany_nil],
        by simp [mulh, insertMany_cons, insertMany_nil]⟩
  · rintro t' m' l' ⟨ht, hm, hh, hx, hy⟩
    refine Exec.set "l" (.op .mul (.var "x") (.var "y")) 0 t' m' l' _ (x * y)
      (by simp [Expr.eval, interpBinop, hx, hy]) ?_
    refine ⟨[interpBinop .mulhuu x y, x * y], ?_, ?_⟩
    · simp [mulh, getMany, hh]
    · rintro ⟨h, l, ⟨⟩⟩ heq
      simp only [Bedrock2.tupToList, List.cons.injEq, and_true] at heq
      exact ⟨by simp [heq.1, heq.2], hm⟩

private theorem divmod_exec (x y : BitVec 64) (t0 : Trace 64) (m0 : Mem 64) :
    Exec bedrock2ExtEmpty divmodFs 0 divmod.2.body t0 m0
      ((∅ : Locals 64).insertMany (divmod.2.params.zip [x, y]))
      (fun t' m' l' => t' = t0 ∧ m' = m0 ∧ ∃ retvs, getMany l' divmod.2.rets = some retvs ∧
        retvs = [interpBinop .divu x y, interpBinop .remu x y]) := by
  refine Exec.seq _ _ 0 t0 m0 _ _
    (fun t' m' l' => t' = t0 ∧ m' = m0 ∧ l'["q"]? = some (interpBinop .divu x y) ∧
      l'["x"]? = some x ∧ l'["y"]? = some y) ?_ ?_
  · exact Exec.set "q" (.op .divu (.var "x") (.var "y")) 0 t0 m0 _ _
      (interpBinop .divu x y)
      (by simp [divmod, Expr.eval, insertMany_cons, insertMany_nil])
      ⟨rfl, rfl, by simp [divmod, insertMany_cons, insertMany_nil],
        by simp [divmod, insertMany_cons, insertMany_nil],
        by simp [divmod, insertMany_cons, insertMany_nil]⟩
  · rintro t₁ m₁ l' ⟨ht, hm, hq, hx, hy⟩
    refine Exec.set "r" (.op .remu (.var "x") (.var "y")) 0 t₁ m₁ l' _
      (interpBinop .remu x y) (by simp [Expr.eval, hx, hy]) ?_
    exact ⟨ht, hm, [interpBinop .divu x y, interpBinop .remu x y],
      by simp [divmod, getMany, hq], rfl⟩

theorem useDivmod_exec (x y : BitVec 64) (hy : y ≠ 0#64) (m0 : Mem 64) :
    Exec bedrock2ExtEmpty divmodFs 0 useDivmod.2.body [] m0
      ((∅ : Locals 64).insertMany (useDivmod.2.params.zip [x, y]))
      (fun _ m' l' => ∃ retvs, getMany l' useDivmod.2.rets = some retvs ∧
        ∀ resTup : Tup Val (List.replicate 2 i64),
          Bedrock2.tupToList resTup = retvs →
          resTup = ((x / y) * 0x3e8#64 + (x % y), x % y, ()) ∧ m' = m0) := by
  have hdiv : interpBinop .divu x y = x / y := by simp [interpBinop, hy]
  have hrem : interpBinop .remu x y = x % y := rfl
  refine Exec.seq _ _ 0 [] m0 _ _
    (fun t' m' l' => t' = [] ∧ m' = m0 ∧ l'["q"]? = some (x / y) ∧ l'["r"]? = some (x % y))
    ?_ ?_
  · refine Exec.call ["q", "r"] "divmod" [.var "x", .var "y"] 0 [] m0 _ _ divmod.2
      [x, y] ((∅ : Locals 64).insertMany (divmod.2.params.zip [x, y])) _
      rfl (by simp [useDivmod, evalArgs, Expr.eval, insertMany_cons, insertMany_nil])
      (by simp [divmod, putManyZip]) (divmod_exec x y [] m0) ?_
    rintro t' m' st1 ⟨ht, hm, retvs, hget, hrv⟩
    rw [hrv] at hget
    let l₁ := (((∅ : Locals 64).insertMany (useDivmod.2.params.zip [x, y])).insert
      "q" (interpBinop .divu x y)).insert "r" (interpBinop .remu x y)
    refine ⟨[interpBinop .divu x y, interpBinop .remu x y], hget, l₁, ?_, ht, hm, ?_, ?_⟩
    · simp [l₁, putManyZip, insertMany_cons, insertMany_nil]
    · simp [l₁, hdiv]
    · simp [l₁, hrem]
  · rintro t₁ m₁ l₁ ⟨ht, hm, h1, h2⟩
    refine Exec.seq _ _ 0 t₁ m₁ l₁ _
      (fun t' m' l' => t' = [] ∧ m' = m0 ∧
        l'["s"]? = some ((x / y) * 0x3e8#64 + (x % y)) ∧ l'["r"]? = some (x % y)) ?_ ?_
    · exact Exec.set "s" (.op .add (.op .mul (.var "q") (.literal 0x3e8)) (.var "r")) 0 t₁ m₁ l₁ _
        ((x / y) * 0x3e8#64 + (x % y)) (by simp [Expr.eval, interpBinop, h1, h2])
        ⟨ht, hm, by simp, by simp [h2]⟩
    · rintro t₂ m₂ l₂ ⟨ht2, hm2, hs, hr⟩
      refine Exec.set "t" (.var "r") 0 t₂ m₂ l₂ _ (x % y) (by simp [Expr.eval, hr]) ?_
      refine ⟨[(x / y) * 0x3e8#64 + (x % y), x % y], ?_, ?_⟩
      · simp [useDivmod, getMany, hs]
      · rintro ⟨s, t, ⟨⟩⟩ heq
        simp only [Bedrock2.tupToList, List.cons.injEq, and_true] at heq
        exact ⟨by simp [heq.1, heq.2], hm2⟩

private theorem mem_split_comm {w : Nat} {m m1 m2 : Mem w} (h : split m m1 m2) :
    split m m2 m1 := by
  rw [Kraken.Bedrock2.split_iff_sep, sep_comm, ← Kraken.Bedrock2.split_iff_sep]
  exact h

private theorem anybytes_eq_split {w : Nat} {mSmall mStack mComb : Mem w} {a : BitVec w} {n : Nat}
    (hany : anybytes a n mStack) (hsp : split mComb mSmall mStack) :
    ∃ bs : List UInt8, bs.length = n ∧ n ≤ 2 ^ w ∧ (Eq (bs.At a) ⋆ Eq mSmall) mComb := by
  rcases hany with ⟨bs, rfl, hlen, hle⟩
  rw [Kraken.Bedrock2.split_iff_sep, sep_comm] at hsp
  exact ⟨bs, hlen, hle, hsp⟩

private theorem bitcopy_loop_std3 {ext : ExtSpec 64} {e : Kraken.Bedrock2.Env} {B : Nat}
    (x v : BitVec 64) (t : Trace 64) (m : Mem 64) (k : Nat) (hk : k ≤ 64)
    (hi : ∀ j, j < 64 → v.getLsbD j = if j < k then x.getLsbD j else false) :
    Exec ext e B
      (Cmd.while (Expr.var "b")
        ((Cmd.cond (Expr.op .and (Expr.var "x") (Expr.var "b"))
            (Cmd.set "i" (Expr.op .or (Expr.var "i") (Expr.var "b"))) Cmd.skip).seq
          (Cmd.set "b" (Expr.op .slu (Expr.var "b") (Expr.literal 1)))))
      t m
      (Std.ExtHashMap.insert (Std.ExtHashMap.insert (Std.ExtHashMap.insert ∅ "x" x) "i" v) "b"
        (1#64 <<< k))
      fun t' m' l' => t' = t ∧ m' = m ∧ l'["x"]? = some x ∧ l'["i"]? = some x := by
  refine Exec.while_wf (Measure := Nat) (lt := (· < ·)) Nat.lt_wfRel.wf
    (fun rem t' m' l' => t' = t ∧ m' = m ∧ ∃ k', k' ≤ 64 ∧ rem = 64 - k' ∧
      l'["x"]? = some x ∧
      (∃ v', l'["i"]? = some v' ∧
        ∀ j, j < 64 → v'.getLsbD j = if j < k' then x.getLsbD j else false) ∧
      l'["b"]? = some (1#64 <<< k'))
    (64 - k) ⟨rfl, rfl, k, hk, rfl, by simp, ⟨v, by simp, hi⟩, by simp⟩ ?_
  rintro rem t' m' l' ⟨ht', hm', k', hk', hrem, hx, ⟨v', hv', hiv⟩, hb⟩
  refine ⟨1#64 <<< k', by simp [Expr.eval, hb], ?_, ?_⟩
  · intro hnz
    have hlt64 : k' < 64 := by
      rcases Nat.eq_or_lt_of_le hk' with rfl | hlt
      · exfalso; apply hnz; decide
      · exact hlt
    have hshl : 1#64 <<< (k' + 1) = interpBinop .slu (1#64 <<< k') 1#64 := by
      simp only [interpBinop, shamt]
      have : (1#64 : BitVec 64).toNat % 2 ^ Nat.log2 64 = 1 := by decide
      rw [this, BitVec.shiftLeft_add]
    have hbit : ∀ j, j < 64 → (1#64 <<< k').getLsbD j = decide (j = k') := by
      intro j hj
      simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one]
      by_cases hjk : j < k'
      · have hne : j ≠ k' := by omega
        simp [hjk, hne]
      · by_cases heq : j = k'
        · subst heq; simp [hlt64]
        · have hne0 : j - k' ≠ 0 := by omega
          simp [hj, hjk, hne0, heq]
    have hzero_iff : x &&& (1#64 <<< k') = 0#64 ↔ x.getLsbD k' = false := by
      constructor
      · intro h
        have := congrArg (·.getLsbD k') h
        simpa [BitVec.getLsbD_and, hbit k' hlt64] using this
      · intro hf
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero, hbit j hj]
        by_cases heq : j = k'
        · subst heq; simp [hf]
        · simp [heq]
    by_cases hcz : x &&& (1#64 <<< k') = 0#64
    · have hxf : x.getLsbD k' = false := hzero_iff.mp hcz
      refine Exec.seq _ _ _ t' m' l' _
        (fun t'' m'' l'' => t'' = t' ∧ m'' = m' ∧ l'' = l') ?_ ?_
      · refine Exec.if_false B t' m' l' _ _ _ _ (x &&& (1#64 <<< k'))
          (by simp [Expr.eval, hx, hb, interpBinop]) hcz (Exec.skip _ _ _ _ _ ⟨rfl, rfl, rfl⟩)
      · rintro t'' m'' l'' ⟨ht'', hm'', hl''⟩
        refine Exec.set "b" _ B t'' m'' l'' _ (1#64 <<< (k' + 1))
          (by simp [Expr.eval, hl'', hb, hshl]) ?_
        refine ⟨64 - (k' + 1),
          ⟨ht''.trans ht', hm''.trans hm', k' + 1, hlt64, rfl, ?_, ⟨v', ?_, ?_⟩, ?_⟩, by omega⟩
        · simp [hl'', hx]
        · simp [hl'', hv']
        · intro j hj
          by_cases hjk : j = k'
          · subst hjk
            have hvk := hiv j hj
            simp only [Nat.lt_irrefl, ↓reduceIte] at hvk
            simp only [Nat.lt_succ_self, ↓reduceIte, hxf, hvk]
          · by_cases hlt1 : j < k' <;> simp [hlt1, show j < k' + 1 ↔ j < k' by omega, hiv j hj]
        · simp
    · have hxt : x.getLsbD k' = true := by
        cases hgx : x.getLsbD k'
        · exact False.elim (hcz (hzero_iff.mpr hgx))
        · rfl
      refine Exec.seq _ _ _ t' m' l' _
        (fun t'' m'' l'' => t'' = t' ∧ m'' = m' ∧
          l'' = l'.insert "i" (v' ||| (1#64 <<< k'))) ?_ ?_
      · refine Exec.if_true B t' m' l' _ _ _ _ (x &&& (1#64 <<< k'))
          (by simp [Expr.eval, hx, hb, interpBinop]) hcz ?_
        exact Exec.set "i" _ B t' m' l' _ (v' ||| (1#64 <<< k'))
          (by simp [Expr.eval, hv', hb, interpBinop]) ⟨rfl, rfl, rfl⟩
      · rintro t'' m'' l'' ⟨ht'', hm'', hl''⟩
        refine Exec.set "b" _ B t'' m'' l'' _ (1#64 <<< (k' + 1))
          (by simp [Expr.eval, hl'', hb, hshl]) ?_
        refine ⟨64 - (k' + 1),
          ⟨ht''.trans ht', hm''.trans hm', k' + 1, hlt64, rfl, ?_,
            ⟨v' ||| (1#64 <<< k'), ?_, ?_⟩, ?_⟩, by omega⟩
        · simp [hl'', hx]
        · simp [hl'']
        · intro j hj
          simp only [BitVec.getLsbD_or, hbit j hj, hiv j hj]
          by_cases hjk : j = k'
          · subst hjk; simp [hlt64, hxt]
          · by_cases hlt1 : j < k' <;> simp [hlt1, hjk, show j < k' + 1 ↔ j < k' by omega]
        · simp
  · intro hz
    have hk64 : k' = 64 := by
      rcases Nat.eq_or_lt_of_le hk' with rfl | hlt
      · rfl
      · exfalso
        have hnz : (1#64 <<< k').getLsbD k' = true := by simp [hlt]
        rw [hz] at hnz
        simp at hnz
    subst hk64
    refine ⟨ht', hm', hx, ?_⟩
    have hvx : v' = x := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simpa [hj] using hiv j hj
    rwa [← hvx]

theorem bitcopy_store_ok_std3 {ext : ExtSpec 64} {e : Kraken.Bedrock2.Env}
    (he : List.lookup Examples.bitcopy_store.1 e = some Examples.bitcopy_store.2)
    (t : Trace 64) (m : Mem 64) :
    call ext e 8 Examples.bitcopy_store.1 t m [] fun t' m' rets =>
      t' = t ∧ m' = m ∧ rets = [15#64] := by
  refine call.of_body he rfl ?_
  refine Exec.stackalloc "x" 8 _ 8 t m _ _ (by decide) ?_
  intro x mStack mComb hany hsp
  obtain ⟨bs0, hlen0, _, hm0⟩ := anybytes_eq_split hany hsp
  dsimp only [Examples.bitcopy_store]
  refine Exec.seq _ _ 0 t mComb _ _
    (fun t' m' l' => t' = t ∧ l' = Std.ExtHashMap.insert ∅ "x" x ∧
      (Eq ((Int.toBytes 8 (0#64).toNat).At x) ⋆ Eq m) m') ?_ ?_
  · exact Exec.store_sep (by simp [Expr.eval]) (by simp [Expr.eval])
      hm0 (by simpa [AccessSize.bytes] using hlen0) (by decide)
      fun m₁ hm₁ => ⟨rfl, by simp [insertMany], hm₁⟩
  · rintro t₁ m₁ l₀ ⟨ht₁, hl₀, hm₁⟩
    refine Exec.seq _ _ 0 t₁ m₁ l₀ _
      (fun t' m' l' => t' = t₁ ∧ m' = m₁ ∧
        l' = Std.ExtHashMap.insert (Std.ExtHashMap.insert ∅ "x" x) "i" 0#64) ?_ ?_
    · exact Exec.set "i" (.literal 0) 0 t₁ m₁ l₀ _ 0#64 rfl ⟨rfl, rfl, by simp [hl₀]⟩
    · rintro t₂ m₂a l₂a ⟨ht₂, hm₂a, hl₂⟩
      refine Exec.seq _ _ 0 t₂ m₂a l₂a _
        (fun t' m' l' => t' = t₂ ∧ m' = m₂a ∧
          l' = Std.ExtHashMap.insert
            (Std.ExtHashMap.insert (Std.ExtHashMap.insert ∅ "x" x) "i" 0#64) "b" 1#64) ?_ ?_
      · exact Exec.set "b" (.literal 1) 0 t₂ m₂a l₂a _ 1#64 rfl ⟨rfl, rfl, by simp [hl₂]⟩
      · rintro t₃ m₃ l₃ ⟨ht₃, hm₃, hl₃⟩
        refine Exec.seq _ _ 0 t₃ m₃ l₃ _
          (fun t' m' l' => t' = t₃ ∧ m' = m₃ ∧ l'["x"]? = some x ∧ l'["i"]? = some x) ?_ ?_
        · rw [hm₃, hm₂a, hl₃]
          simpa using bitcopy_loop_std3 x 0#64 t₃ m₁ 0 (by omega) (fun j _ => by simp)
        · rintro t₄ m₄ l₁ ⟨ht₄, hm₄, hlx, hl1⟩
          refine Exec.seq _ _ 0 t₄ m₄ l₁ _
            (fun t' m' l' => t' = t₄ ∧ l' = l₁ ∧
              (Eq ((Int.toBytes 8 (15#64).toNat).At x) ⋆ Eq m) m') ?_ ?_
          · rw [hm₄, hm₃, hm₂a]
            exact Exec.store_sep (sz := .eight) (bs := Int.toBytes 8 (0#64).toNat) (R := Eq m)
              (by simp [Expr.eval, hl1]) (by simp [Expr.eval])
              hm₁ (by decide) (by decide) fun m₂ hm₂ => ⟨rfl, rfl, hm₂⟩
          · rintro t₅ m₂ l₂ ⟨ht₅, hl₂, hm₂⟩
            have hld : Expr.eval m₂ l₂ (.load .eight (.var "x")) = some 15#64 := by
              have hlx2 : l₂["x"]? = some x := hl₂ ▸ hlx
              change (l₂["x"]?.bind (load? .eight m₂)) = some 15#64
              rw [hlx2, Option.bind_some, load?_sep hm₂ (by decide) (by decide)]
              rfl
            refine Exec.set "r" _ 0 t₅ m₂ l₂ _ 15#64 hld ?_
            rcases hm₂ with ⟨mStack', m', hu', hi', hmStack', hm'⟩
            subst hm'
            refine ⟨m, mStack', ⟨Int.toBytes 8 (15#64).toNat, hmStack', by decide, by decide⟩,
              mem_split_comm (Kraken.Bedrock2.split_iff_sep.mpr
                ⟨mStack', m, hu', hi', rfl, rfl⟩),
              [15#64], ?_, ht₅.trans (ht₄.trans (ht₃.trans (ht₂.trans ht₁))), rfl, rfl⟩
            simp [getMany]

/-! ## 5. End-to-End `unified ... refBackend` Soundness & Shared `B2Spec`s -/

@[expose] def swapB2Spec : B2Spec where
  ext := bedrock2ExtEmpty
  e := [Examples.swap 64]
  Pre sym nArgs nRets args m post :=
    sym = (Examples.swap 64).1 ∧ nArgs = 2 ∧ nRets = 0 ∧
    ∃ (pa pb : BitVec 64) (bsa bsb : List UInt8) (R : Mem 64 → Prop),
      args = [pa, pb] ∧ bsa.length = 8 ∧ bsb.length = 8 ∧
      (Eq (bsa.At pa) ⋆ Eq (bsb.At pb) ⋆ R) m ∧
      (∀ m', (Eq (bsb.At pa) ⋆ Eq (bsa.At pb) ⋆ R) m' → post [] m' [])

theorem swap_sat_b2Spec : bedrock2Src.Sat (Examples.swap 64) swapB2Spec := by
  refine bedrock2Src_sat_of_call (p := Examples.swap 64) (s := swapB2Spec) rfl ?_
  rintro xs m post ⟨_, _, _, pa, pb, bsa, bsb, R, rfl, hla, hlb, hm, hcont⟩
  refine ⟨0, by decide, ?_⟩
  have hcall := @Examples.swap_ok 64 (Or.inr rfl) bedrock2ExtEmpty [Examples.swap 64] 0 rfl
    [] m pa pb bsa bsb R hla hlb hm
  exact hcall.weaken fun _ m' rets ⟨hrets, ht, hm'⟩ => by
    subst ht; subst hrets; exact hcont m' hm'

@[expose] def setBytesB2Spec : B2Spec where
  ext := bedrock2ExtEmpty
  e := [Examples.set_bytes]
  Pre sym nArgs nRets args m post :=
    sym = Examples.set_bytes.1 ∧ nArgs = 3 ∧ nRets = 0 ∧
    ∃ (p n v : BitVec 64) (bs : List UInt8) (R : Mem 64 → Prop),
      args = [p, n, v] ∧ bs.length = n.toNat ∧
      (Eq (bs.At p) ⋆ R) m ∧
      (∀ m', (Eq ((List.replicate n.toNat v.toNat.toUInt8).At p) ⋆ R) m' → post [] m' [])

theorem setBytes_sat_b2Spec : bedrock2Src.Sat Examples.set_bytes setBytesB2Spec := by
  refine bedrock2Src_sat_of_call (p := Examples.set_bytes) (s := setBytesB2Spec) rfl ?_
  rintro xs m post ⟨_, _, _, p, n, v, bs, R, rfl, hlen, hm, hcont⟩
  refine ⟨0, by decide, ?_⟩
  have hcall := @Examples.set_bytes_ok 64 bedrock2ExtEmpty [Examples.set_bytes] 0 rfl
    [] m p n v bs R hlen hm
  exact hcall.weaken fun _ m' rets ⟨hrets, ht, hm'⟩ => by
    subst ht; subst hrets; exact hcont m' hm'

@[expose] def bitcopyB2Spec : B2Spec where
  ext := bedrock2ExtEmpty
  e := [Examples.bitcopy_store]
  Pre sym nArgs nRets args m post :=
    sym = "bitcopy_store" ∧ nArgs = 0 ∧ nRets = 1 ∧ args = [] ∧ post [] m [15#64]

theorem bitcopy_sat_b2Spec : bedrock2Src.Sat Examples.bitcopy_store bitcopyB2Spec := by
  refine bedrock2Src_sat_of_call (p := Examples.bitcopy_store) (s := bitcopyB2Spec) rfl ?_
  rintro xs m post ⟨_, _, _, rfl, hcont⟩
  refine ⟨8, by decide, ?_⟩
  have hcall := bitcopy_store_ok_std3 (ext := bedrock2ExtEmpty) (e := [Examples.bitcopy_store])
    rfl [] m
  exact hcall.weaken fun _ _ _ ⟨ht, hm', hrets⟩ => by
    subst ht; subst hm'; subst hrets; exact hcont

theorem unified_swap_ref_sound (t : LegalTarget) {fn : Fn}
    (h : (unified bedrock2Frontend t refBackend).run (Examples.swap 64) = .ok [fn]) :
    refBackend.MSat [fn]
      ((unified bedrock2Frontend t refBackend).tr (Examples.swap 64) swapB2Spec) :=
  (unified bedrock2Frontend t refBackend).sound (Examples.swap 64) [fn] swapB2Spec trivial h
    swap_sat_b2Spec

theorem unified_setBytes_ref_sound (t : LegalTarget) {fn : Fn}
    (h : (unified bedrock2Frontend t refBackend).run Examples.set_bytes = .ok [fn]) :
    refBackend.MSat [fn]
      ((unified bedrock2Frontend t refBackend).tr Examples.set_bytes setBytesB2Spec) :=
  (unified bedrock2Frontend t refBackend).sound Examples.set_bytes [fn] setBytesB2Spec trivial h
    setBytes_sat_b2Spec

theorem unified_bitcopy_ref_sound (t : LegalTarget) {fn : Fn}
    (h : (unified bedrock2Frontend t refBackend).run Examples.bitcopy_store = .ok [fn]) :
    refBackend.MSat [fn]
      ((unified bedrock2Frontend t refBackend).tr Examples.bitcopy_store bitcopyB2Spec) :=
  (unified bedrock2Frontend t refBackend).sound Examples.bitcopy_store [fn] bitcopyB2Spec trivial
    h bitcopy_sat_b2Spec

theorem unified_swap_scalar64_ref_ok :
    ((unified bedrock2Frontend LegalTarget.scalar64 refBackend).run (Examples.swap 64)).isOk =
      true := by
  t_kernel_rfl

theorem unified_swap_aarch64_ref_ok :
    ((unified bedrock2Frontend LegalTarget.aarch64 refBackend).run (Examples.swap 64)).isOk =
      true := by
  t_kernel_rfl

theorem unified_setBytes_scalar64_ref_ok :
    ((unified bedrock2Frontend LegalTarget.scalar64 refBackend).run Examples.set_bytes).isOk =
      true := by
  t_kernel_rfl

theorem unified_bitcopy_aarch64_ref_ok :
    ((unified bedrock2Frontend LegalTarget.aarch64 refBackend).run Examples.bitcopy_store).isOk =
      true := by
  t_kernel_rfl

end LeanQbeTest.T.UnifiedBedrock2Test

#print axioms LeanQbe.T.Unified.bedrock2Lower
#print axioms LeanQbe.T.Unified.bedrock2Frontend
#print axioms LeanQbe.T.Unified.bedrock2Module_moduleOk
#print axioms LeanQbe.T.Unified.bedrock2ModMid_sound
#print axioms LeanQbe.T.Unified.bedrock2TargetBackend
#print axioms LeanQbe.T.Unified.bedrock2_unified_fnSpec
#print axioms LeanQbe.T.Unified.bedrock2Module_compiled_run_exec
#print axioms LeanQbe.T.Unified.bedrock2Module_compiled_run_call
#print axioms LeanQbeTest.T.UnifiedBedrock2Test.coreMod_moduleOk
#print axioms LeanQbeTest.T.UnifiedBedrock2Test.stackMod_moduleOk
#print axioms LeanQbeTest.T.UnifiedBedrock2Test.coreBundle_scalar64_mid_sound
#print axioms LeanQbeTest.T.UnifiedBedrock2Test.coreBundle_aarch64_mid_sound
#print axioms LeanQbeTest.T.UnifiedBedrock2Test.bitcopy_store_ok_std3
#print axioms LeanQbeTest.T.UnifiedBedrock2Test.unified_swap_ref_sound
#print axioms LeanQbeTest.T.UnifiedBedrock2Test.unified_setBytes_ref_sound
#print axioms LeanQbeTest.T.UnifiedBedrock2Test.unified_bitcopy_ref_sound
