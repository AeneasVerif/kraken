module

public import LeanQbe.T.Wasm.Decode
public import LeanQbe.T.Wasm.Safety
public import LeanQbe.T.Main
public import LeanQbe.T.MainLinkScc
public import LeanQbe.T.MainCertProof
meta import LeanQbe.T.Wasm.Decode
meta import LeanQbe.T.Main
meta import LeanQbe.T.MainLinkScc
meta import LeanQbe.T.Module

/-!
# WebAssembly Phase 2B Bulk-Memory & Growth Verification (`WasmBulkMemTest`)

Arch-neutral verification and test suite for WebAssembly linear-memory growth and bulk-memory
instructions (`memory.size`, `memory.grow`, `memory.fill`, `memory.copy`):

1. Binary decode & validation unit + negative tests (`0x3F 0x00`, `0x40 0x00`,
   `0xFC 0x0A 0x00 0x00`, `0xFC 0x0B 0x00`, non-zero memidx / missing memory rejections).
2. Real `clang --target=wasm32 -O2 -mbulk-memory` binary test (`probeWasm` -> `bulkMod`/`bulkQbe`):
   decoded, validated, compiled for both `LegalTarget.x64` and `LegalTarget.aarch64`, and
   verified via `lowerModule_moduleOk` & `decodeAndLowerWasm_semScc`.
3. Concrete `Func.wp` behavioral & adversarial soundness theorems:
   - `bm_size_ok`: `memory.size` returns current pages without modifying memory or host frame `R`.
   - `bm_grow_ok`: `memory.grow` zeroes newly exposed 64 KiB page (`8192` 8-byte words), updates
     `[vmCtx + 8]`, returns old page count, and preserves existing pages & `R`.
   - `bm_grow_fail`: over-cap `memory.grow` returns `-1#32` (`0xFFFFFFFF#32`) with `mem' = mem`.
   - `bm_fill_ok`: `memory.fill` matches `listFillAux` and preserves host frame `R`.
   - `bm_copy_fwd` / `bm_copy_bwd`: overlapping forward (`dst ≤ src`) and backward (`src < dst`)
     `memory.copy` match `listCopyFwdAux`/`listCopyBwdAux` (`memmove` semantics) and preserve `R`.
   - `bm_fill_oob` / `bm_copy_wrap`: adversarial `u32` wraparound (`dst = 0xFFFFFFF0, n = 32`)
     traps cleanly (`status = 1#32`) with `mem' = mem` (zero writes) and `R mem'`.

This module imports neither `Kraken.X64` nor `Kraken.AArch64` and defines zero `@[expose]` tags.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.WasmBulkMemTest

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Wasm LeanQbe.T.LinkScc

/-! ## 1. Arch-Neutral Compilation Harness & Opcode / Validation Tests -/

/-- Pure target-neutral GPR ISA configuration supporting all 64-bit scalar operations. -/
@[expose] def bmTestGpr : GprIsa Nat Empty Nat Unit where
  condReads _ := 0#8
  negCond c := c
  zeroFlags := []
  clearFlags := []
  mov _ _ := [()]
  movi _ _ := [()]
  setcc _ _ := [()]
  jmp _ := [()]
  jcc _ _ := [()]
  jnzGpr _ _ := ([()], 0#8)
  op _ _ _ _ := some ([()], 0#8)
  load _ _ _ := some ([()], 0#8)
  store _ _ _ := some ([()], 0#8)
  supportsScalarOp := defaultSupportsScalarOp [8, 16, 32, 64] true true true

/-- Pure target-neutral Frame ISA configuration with 8 arg/return registers. -/
@[expose] def bmTestFrame : FrameIsa Nat Unit where
  label _ := ()
  sp := 100
  scratch := [10, 11]
  allocatable := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  calleeSaved := [8, 9]
  raRegs := []
  argRegs := [0, 1, 2, 3, 4, 5, 6, 7]
  retRegs := [0, 1, 2, 3, 4, 5, 6, 7]
  raBytes := 8
  frameSize n := n * 8
  prologue _ := ([()], 0#8)
  epilogue _ := ([()], 0#8)
  slotSt _ _ := [()]
  slotLd _ _ := [()]
  canonAbi _ _ := ([()], 0#8)
  call _ := [()]
  exitJmp _ := [()]
  ret := [()]

/-- Target-neutral `Isa` for `#guard` compilation checks across x64 and AArch64 legal targets. -/
@[expose] def bmTestIsa : Isa where
  Reg := Nat
  VReg := Empty
  Cond := Nat
  Directive := Unit
  gpr := bmTestGpr
  vec := VecIsa.empty Nat Nat Unit
  frame := bmTestFrame

/-- Check acyclic compilation of `qm` against `lt` on `bmTestIsa`. -/
def checkBmCompile (lt : LegalTarget) (qm : Module) : Bool :=
  let hints : List bmTestIsa.Hints := qm.fns.map (Fn.computeHints bmTestIsa lt)
  (compileModule bmTestIsa lt bmTestIsa.frame.raBytes [] [] 0 qm.fns hints).isOk

-- 1.1 Valid bulk-memory & growth opcode decoding
#guard match decodeOneInstr 10 0x3f ⟨⟨#[0x00]⟩, 0⟩ with
  | .ok (.memory_size, r) => r.remaining == 0
  | _ => false

#guard match decodeOneInstr 10 0x40 ⟨⟨#[0x00]⟩, 0⟩ with
  | .ok (.memory_grow, r) => r.remaining == 0
  | _ => false

#guard match decodeOneInstr 10 0xfc ⟨⟨#[0x0a, 0x00, 0x00]⟩, 0⟩ with
  | .ok (.memory_copy, r) => r.remaining == 0
  | _ => false

#guard match decodeOneInstr 10 0xfc ⟨⟨#[0x0b, 0x00]⟩, 0⟩ with
  | .ok (.memory_fill, r) => r.remaining == 0
  | _ => false

-- 1.2 Rejection of non-zero memory indices, unsupported `0xFC` sub-opcodes, and truncation
#guard !(decodeOneInstr 10 0x3f ⟨⟨#[0x01]⟩, 0⟩).isOk
#guard !(decodeOneInstr 10 0x40 ⟨⟨#[0x01]⟩, 0⟩).isOk
#guard !(decodeOneInstr 10 0xfc ⟨⟨#[0x0a, 0x01, 0x00]⟩, 0⟩).isOk
#guard !(decodeOneInstr 10 0xfc ⟨⟨#[0x0a, 0x00, 0x01]⟩, 0⟩).isOk
#guard !(decodeOneInstr 10 0xfc ⟨⟨#[0x0b, 0x01]⟩, 0⟩).isOk
#guard !(decodeOneInstr 10 0xfc ⟨⟨#[0x08, 0x00, 0x00]⟩, 0⟩).isOk
#guard !(decodeOneInstr 10 0xfc ⟨⟨#[0x09, 0x00]⟩, 0⟩).isOk
#guard !(decodeOneInstr 10 0xfc ⟨⟨#[0x0c, 0x00, 0x00]⟩, 0⟩).isOk
#guard !(decodeOneInstr 10 0xfc ⟨⟨#[]⟩, 0⟩).isOk
#guard !(decodeOneInstr 10 0xfc ⟨⟨#[0x0a, 0x00]⟩, 0⟩).isOk

-- 1.3 Validation rejections: missing memory, stack type errors, invalid memory limits
private def noMemMod (ft : WFuncTy) (bd : List WInstr) : WModule :=
  { types := [ft], funcs := [{ name := "f", typeIdx := 0, body := bd }], memory := none }

#guard !validateModule (noMemMod { results := [.i32] } [.memory_size])
#guard !validateModule (noMemMod { params := [.i32], results := [.i32] }
  [.local_get 0, .memory_grow])
#guard !validateModule (noMemMod { params := [.i32, .i32, .i32] }
  [.local_get 0, .local_get 1, .local_get 2, .memory_fill])
#guard !validateModule (noMemMod { params := [.i32, .i32, .i32] }
  [.local_get 0, .local_get 1, .local_get 2, .memory_copy])
private def badFillTyMod : WModule :=
  { types := [{ params := [.i32, .i32, .i64] }],
    funcs :=
      [{ name := "f", typeIdx := 0,
         body := [.local_get 0, .local_get 1, .local_get 2, .memory_fill] }],
    memory := some { initPages := 1 } }

#guard !validateModule badFillTyMod
#guard !validateModule { memory := some { initPages := 65537 } }
#guard !validateModule { memory := some { initPages := 1, maxPages := some 65537 } }
#guard !validateModule { memory := some { initPages := 2, maxPages := some 1 } }

/-! ## 2. Real Compiled C Guest Binary (`clang --target=wasm32 -O2 -mbulk-memory`) -/

/-- Real WebAssembly binary compiled from C with
`clang --target=wasm32 -O2 -nostdlib -mbulk-memory -Wl,--no-entry -Wl,--export-all -Wl,--strip-all`
exposing `test_mem_size`, `test_mem_grow`, `test_mem_fill`, `test_mem_copy` (unused
`__stack_pointer` global mutability byte set from `0x01` to `0x00` for sandbox immutability). -/
def probeWasm : ByteArray := ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x10, 0x03, 0x60, 0x00, 0x01, 0x7f, 0x60,
  0x01, 0x7f, 0x01, 0x7f, 0x60, 0x03, 0x7f, 0x7f,
  0x7f, 0x00, 0x03, 0x05, 0x04, 0x00, 0x01, 0x02,
  0x02, 0x05, 0x03, 0x01, 0x00, 0x02, 0x06, 0x08,
  0x01, 0x7f, 0x00, 0x41, 0x80, 0x88, 0x04, 0x0b,
  0x07, 0x4a, 0x05, 0x06, 0x6d, 0x65, 0x6d, 0x6f,
  0x72, 0x79, 0x02, 0x00, 0x0d, 0x74, 0x65, 0x73,
  0x74, 0x5f, 0x6d, 0x65, 0x6d, 0x5f, 0x73, 0x69,
  0x7a, 0x65, 0x00, 0x00, 0x0d, 0x74, 0x65, 0x73,
  0x74, 0x5f, 0x6d, 0x65, 0x6d, 0x5f, 0x67, 0x72,
  0x6f, 0x77, 0x00, 0x01, 0x0d, 0x74, 0x65, 0x73,
  0x74, 0x5f, 0x6d, 0x65, 0x6d, 0x5f, 0x66, 0x69,
  0x6c, 0x6c, 0x00, 0x02, 0x0d, 0x74, 0x65, 0x73,
  0x74, 0x5f, 0x6d, 0x65, 0x6d, 0x5f, 0x63, 0x6f,
  0x70, 0x79, 0x00, 0x03, 0x0a, 0x36, 0x04, 0x04,
  0x00, 0x3f, 0x00, 0x0b, 0x06, 0x00, 0x20, 0x00,
  0x40, 0x00, 0x0b, 0x13, 0x00, 0x02, 0x40, 0x20,
  0x02, 0x45, 0x0d, 0x00, 0x20, 0x00, 0x20, 0x01,
  0x20, 0x02, 0xfc, 0x0b, 0x00, 0x0b, 0x0b, 0x14,
  0x00, 0x02, 0x40, 0x20, 0x02, 0x45, 0x0d, 0x00,
  0x20, 0x00, 0x20, 0x01, 0x20, 0x02, 0xfc, 0x0a,
  0x00, 0x00, 0x0b, 0x0b
]⟩

@[expose] def fnSize : WFunc :=
  { name := "test_mem_size", typeIdx := 0, locals := [], body := [.memory_size] }

@[expose] def fnGrow : WFunc :=
  { name := "test_mem_grow", typeIdx := 1, locals := [],
    body := [.local_get 0, .memory_grow] }

@[expose] def fnFill : WFunc :=
  { name := "test_mem_fill", typeIdx := 2, locals := [],
    body :=
      [ .block .empty
          [ .local_get 2, .eqz .i32, .br_if 0
          , .local_get 0, .local_get 1, .local_get 2, .memory_fill ] ] }

@[expose] def fnCopy : WFunc :=
  { name := "test_mem_copy", typeIdx := 2, locals := [],
    body :=
      [ .block .empty
          [ .local_get 2, .eqz .i32, .br_if 0
          , .local_get 0, .local_get 1, .local_get 2, .memory_copy ] ] }

@[expose] def bulkMod : WModule :=
  { types :=
      [ { params := [], results := [.i32] }
      , { params := [.i32], results := [.i32] }
      , { params := [.i32, .i32, .i32], results := [] } ]
    funcs := [fnSize, fnGrow, fnFill, fnCopy]
    memory := some { initPages := 2, maxPages := none }
    globals := [{ ty := .i32, mut_ := false, init := 66560#64 }] }

@[expose] def bulkQbe : Module := lowerModule bulkMod

#guard match decodeAndLowerWasm probeWasm with
  | .ok (m, qm) =>
    m.types == bulkMod.types &&
    m.memory == bulkMod.memory &&
    m.globals == bulkMod.globals &&
    m.funcs.map (·.name) == bulkMod.funcs.map (·.name) &&
    (match m.funcs with
      | [f0, f1, f2, f3] =>
        match f0.body, f1.body, f2.body, f3.body with
        | [.memory_size], [.local_get 0, .memory_grow],
          [.block .empty [.local_get 2, .eqz .i32, .br_if 0,
            .local_get 0, .local_get 1, .local_get 2, .memory_fill]],
          [.block .empty [.local_get 2, .eqz .i32, .br_if 0,
            .local_get 0, .local_get 1, .local_get 2, .memory_copy]] => true
        | _, _, _, _ => false
      | _ => false) &&
    checkBmCompile LegalTarget.x64 qm &&
    checkBmCompile LegalTarget.aarch64 qm
  | .error _ => false

theorem bm_probe_scc {m : WModule} {qm : Module}
    (h : decodeAndLowerWasm probeWasm = .ok (m, qm)) (Γext : Env) :
    ∀ i : Nat, ((WasmSandboxEnv m i).restrict (qm.fns.map Fn.sig)).le (Env.semScc qm Γext) :=
  decodeAndLowerWasm_semScc h Γext

theorem bm_valid : validateModule bulkMod = true := by decide

theorem bm_acyclic : bulkQbe.checkAcyclic = true :=
  lowerModule_checkAcyclic bm_valid (by decide)

theorem bm_wf : ∀ fn ∈ bulkQbe.fns, fn.Wf := lowerModule_wf bulkMod

theorem bm_modOk : ModuleOk (WasmSandboxEnvAny bulkMod) bulkQbe :=
  lowerModule_moduleOk bm_valid bm_acyclic

theorem bm_wp :
    ∀ f ∈ bulkQbe.fns, ∀ (xs : Tup Val f.as) (m : Mem 64)
      (Q : Post f.rs) (X : XPost),
      WasmSandboxEnvAny bulkMod f.name f.as f.rs xs m Q X →
      Func.wp (WasmSandboxEnvAny bulkMod) f.body xs m Q X := by
  intro f hf
  rcases List.mem_iff_append.mp hf with ⟨pre, post, hsp⟩
  exact (bm_modOk.fnsOk pre f post hsp).2.2

theorem bm_semScc (Γext : Env) :
    ∀ i : Nat,
      ((WasmSandboxEnv bulkMod i).restrict (bulkQbe.fns.map Fn.sig)).le
        (Env.semScc bulkQbe Γext) :=
  lowerModule_semScc bm_valid Γext

theorem bm_any_monoX (f : Sym) (as bs : List Ty) (xs : Tup Val as)
    (mem : Mem 64) (Q : Post bs) (X X' : XPost)
    (h : WasmSandboxEnvAny bulkMod f as bs xs mem Q X) :
    WasmSandboxEnvAny bulkMod f as bs xs mem Q X' :=
  h

theorem bm_fn_size_qbe : lowerFn bulkMod fnSize ∈ bulkQbe.fns := by
  simp [bulkQbe, lowerModule, bulkMod]

theorem bm_fn_grow_qbe : lowerFn bulkMod fnGrow ∈ bulkQbe.fns := by
  simp [bulkQbe, lowerModule, bulkMod]

theorem bm_fn_fill_qbe : lowerFn bulkMod fnFill ∈ bulkQbe.fns := by
  simp [bulkQbe, lowerModule, bulkMod]

theorem bm_fn_copy_qbe : lowerFn bulkMod fnCopy ∈ bulkQbe.fns := by
  simp [bulkQbe, lowerModule, bulkMod]

/-! ## 3. Separation & Functional `memory.fill` / `memory.copy` / Zero-Page Helpers -/

private theorem array64_nil_eq (base : BitVec 64) : array64 base [] = emp := rfl

theorem array64_sep_to_region (base : BitVec 64) :
    ∀ (ws : List (BitVec 64)) {R : Mem 64 → Prop} {m : Mem 64},
      8 * ws.length ≤ 2 ^ 64 → (array64 base ws ⋆ R) m → (region base (8 * ws.length) ⋆ R) m := by
  intro ws
  induction ws generalizing base with
  | nil =>
    intro R m _ hm
    simpa [array64_nil_eq, region_zero] using hm
  | cons w ws ih =>
    intro R m hlen hm
    rw [array64_cons, sep_assoc] at hm
    have hm1 : (region base 8 ⋆ (array64 (base + 8#64) ws ⋆ R)) m :=
      sep_mono (fun m1 h1 => by
        rw [cell64_eq_word8] at h1
        have hlen8 : (Int.toBytes 8 w.toNat).length = 8 := Int.toBytes_length _ _
        have hr : region base (Int.toBytes 8 w.toNat).length m1 :=
          bytes_to_region (a := base) (bs := Int.toBytes 8 w.toNat) h1
        rwa [hlen8] at hr) hm
    have hm2 : (array64 (base + 8#64) ws ⋆ (region base 8 ⋆ R)) m := sep_cast hm1 (by ac_rfl)
    have hlen' : 8 * ws.length ≤ 2 ^ 64 := by simp at hlen; omega
    have hm3 := ih (base + 8#64) hlen' hm2
    have hsp : 8 + 8 * ws.length ≤ 2 ^ 64 := by simp at hlen; omega
    have hm4 : ((region base 8 ⋆ region (base + 8#64) (8 * ws.length)) ⋆ R) m :=
      sep_cast hm3 (by ac_rfl)
    rw [← region_split hsp] at hm4
    have hmul : 8 + 8 * ws.length = 8 * (w :: ws).length := by
      simp [List.length_cons]; omega
    rwa [hmul] at hm4

private theorem replicate_snoc (n : Nat) (a : BitVec 64) :
    List.replicate (n + 1) a = List.replicate n a ++ [a] := by
  induction n with
  | zero => rfl
  | succ k ih =>
    calc a :: List.replicate (k + 1) a
        = a :: (List.replicate k a ++ [a]) := congrArg (a :: ·) ih
      _ = (a :: List.replicate k a) ++ [a] := by rw [List.cons_append]
      _ = List.replicate (k + 1) a ++ [a] := rfl

private theorem replicate_drop_set {done : Nat} (hd : done < 8192)
    {ws : List (BitVec 64)} (hl : ws.length = 8192) :
    (List.replicate done 0#64 ++ ws.drop done).set done 0#64 =
      List.replicate (done + 1) 0#64 ++ ws.drop (done + 1) := by
  have hd' : done < ws.length := by omega
  rw [List.drop_eq_getElem_cons hd', List.set_append]
  simp only [List.length_replicate, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self, List.set_cons_zero,
    replicate_snoc, List.append_assoc, List.singleton_append]

private theorem bv64_8_mul_ne_zero {d : Nat} (hd : d < 8192) :
    BitVec.ofNat 64 (8 * (8192 - d)) ≠ 0#64 := by
  intro h
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at hn
  rw [Nat.mod_eq_of_lt (by omega)] at hn
  omega

private theorem bv64_8_mul_sub {d : Nat} (hd : d < 8192) :
    BitVec.ofNat 64 (8 * (8192 - d)) - 8#64 = BitVec.ofNat 64 (8 * (8192 - (d + 1))) := by
  apply BitVec.eq_of_toNat_eq
  have hle : (8#64 : BitVec 64) ≤ BitVec.ofNat 64 (8 * (8192 - d)) := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      BitVec.toNat_ofNat]
    omega
  rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem emitMemZeroPage_zero {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {base : BitVec 64} {ws : List (BitVec 64)} {R' : Mem 64 → Prop} {mem : Mem 64}
    (hlen : ws.length = 8192)
    (pagePtr : Arg Val i64) (hptr : pagePtr.val = base)
    (hm : (array64 base ws ⋆ R') mem)
    (kDone : Expr Val Cont rs)
    (hk : ∀ m', (array64 base (List.replicate 8192 0#64) ⋆ R') m' → wp Γ Q X kDone m') :
    wp Γ Q X (emitMemZeroPage pagePtr kDone) mem := by
  simp only [emitMemZeroPage]
  refine wp_join_group (fun _ m' => (array64 base (List.replicate 8192 0#64) ⋆ R') m')
    (fun _ _ m' hm' => hk m' hm') (fun jDone hjDone => ?_)
  let Inv : Nat → Tup Val [i64, i64] → Mem 64 → Prop := fun n zxs m' =>
    ∃ done, done ≤ 8192 ∧ n = 8192 - done ∧
      zxs.1 = BitVec.ofNat 64 (8 * (8192 - done)) ∧
      zxs.2.1 = base + BitVec.ofNat 64 (8 * done) ∧
      (array64 base (List.replicate done 0#64 ++ ws.drop done) ⋆ R') m'
  refine wp_loop_group Inv (fun lZero n zxs m' hlZero hinv => ?_)
    (fun lZero hlZero => ?_)
  · rcases zxs with ⟨zRem, zPtr, ⟨⟩⟩
    rcases hinv with ⟨done, hle, rfl, hzRem, hzPtr, hm'⟩
    dsimp only at hzRem hzPtr
    dsimp only [Blocks.get_here]
    rw [wp_let_]
    dsimp only [Op.wp, vals, Arg.val]
    simp only [OpCode.wp, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
    rw [wp_jnz_]
    refine ⟨fun hz => ?_, fun hnz => ?_⟩
    · have hz' : zRem = 0#64 := by
        by_cases h : zRem = 0#64
        · exact h
        · simp [Arg.val, h] at hz
      have hdone : done = 8192 := by
        apply Classical.byContradiction; intro hne
        exact bv64_8_mul_ne_zero (by omega) (hzRem ▸ hz')
      subst hdone
      rw [List.drop_of_length_le (by omega), List.append_nil] at hm'
      rw [wp_jump_]
      exact hjDone () m' hm'
    · have hdn : done < 8192 := by
        apply Classical.byContradiction; intro hge
        have hdone : done = 8192 := by omega
        subst hdone
        simp only [Nat.sub_self, Nat.mul_zero] at hzRem
        simp [Arg.val, hzRem] at hnz
      have hcurLen : done < (List.replicate done 0#64 ++ ws.drop done).length := by
        simp [hlen]; omega
      rw [wp_store_]
      obtain ⟨hsok, hm''⟩ := store_array64 0#64 hcurLen hm'
      refine ⟨by simpa [Arg.val, hzPtr] using hsok, ?_⟩
      rw [replicate_drop_set hdn hlen] at hm''
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      rw [wp_jump_]
      refine hlZero (8192 - (done + 1)) (zRem - 8#64, zPtr + 8#64, ()) _ (by omega) ?_
      refine ⟨done + 1, by omega, rfl, ?_, ?_, by simpa [hzPtr] using hm''⟩
      · rw [hzRem, bv64_8_mul_sub hdn]
      · have hadd : BitVec.ofNat 64 (8 * done) + 8#64 = BitVec.ofNat 64 (8 * (done + 1)) := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by decide : 8 < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        rw [hzPtr, BitVec.add_assoc, hadd]
  · rw [wp_jump_]
    refine hlZero 8192 (65536#64, pagePtr.val, ()) mem ?_
    refine ⟨0, by omega, rfl, rfl, ?_, ?_⟩
    · simp [hptr]
    · simpa using hm

/-- Reference specification for filling `d` bytes from `dst` with `b`. -/
def listFillAux (b : BitVec 8) (dst : Nat) : Nat → List (BitVec 8) → List (BitVec 8)
  | 0, bs => bs
  | d + 1, bs => (listFillAux b dst d bs).set (dst + d) b

private theorem listFillAux_succ (b : BitVec 8) (dst d : Nat) (bs : List (BitVec 8)) :
    listFillAux b dst (d + 1) bs = (listFillAux b dst d bs).set (dst + d) b := rfl

theorem listFillAux_length (b : BitVec 8) (dst : Nat) :
    ∀ d bs, (listFillAux b dst d bs).length = bs.length
  | 0, _ => rfl
  | d + 1, bs => by simp [listFillAux_succ, listFillAux_length b dst d bs]

/-- Reference specification for forward copy (`dst ≤ src`) of `d` bytes. -/
def listCopyFwdAux (dst src : Nat) : Nat → List (BitVec 8) → List (BitVec 8)
  | 0, bs => bs
  | d + 1, bs =>
    let cur := listCopyFwdAux dst src d bs
    cur.set (dst + d) (cur[src + d]?.getD 0#8)

private theorem listCopyFwdAux_zero (dst src : Nat) (bs : List (BitVec 8)) :
    listCopyFwdAux dst src 0 bs = bs := rfl

private theorem listCopyFwdAux_succ (dst src d : Nat) (bs : List (BitVec 8)) :
    listCopyFwdAux dst src (d + 1) bs =
      (listCopyFwdAux dst src d bs).set (dst + d)
        ((listCopyFwdAux dst src d bs)[src + d]?.getD 0#8) := rfl

theorem listCopyFwdAux_length (dst src : Nat) :
    ∀ d bs, (listCopyFwdAux dst src d bs).length = bs.length
  | 0, _ => rfl
  | d + 1, bs => by simp [listCopyFwdAux_succ, listCopyFwdAux_length dst src d bs]

theorem listCopyFwdAux_memmove (dst src : Nat) (hle : dst ≤ src) :
    ∀ d (bs : List (BitVec 8)), dst + d ≤ bs.length → src + d ≤ bs.length →
      ∀ i, i < bs.length →
        (listCopyFwdAux dst src d bs)[i]?.getD 0#8 =
          if dst ≤ i ∧ i < dst + d then bs[src + (i - dst)]?.getD 0#8
          else bs[i]?.getD 0#8
  | 0, bs, _, _, i, _ => by
    simp only [listCopyFwdAux_zero]
    split
    · omega
    · rfl
  | d + 1, bs, hd, hs, i, hi => by
    have ih := listCopyFwdAux_memmove dst src hle d bs (by omega) (by omega)
    have hcurLen : (listCopyFwdAux dst src d bs).length = bs.length :=
      listCopyFwdAux_length dst src d bs
    have hdd : dst + d < (listCopyFwdAux dst src d bs).length := by omega
    have hsrcOrig : (listCopyFwdAux dst src d bs)[src + d]?.getD 0#8 =
        bs[src + d]?.getD 0#8 := by
      have h := ih (src + d) (by omega)
      have hnot : ¬ (dst ≤ src + d ∧ src + d < dst + d) := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnot)] at h
      exact h
    by_cases heq : i = dst + d
    · subst heq
      simp only [listCopyFwdAux_succ, List.getElem?_set_self hdd, Option.getD_some, hsrcOrig]
      have hcond : dst ≤ dst + d ∧ dst + d < dst + (d + 1) := by omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true hcond), Nat.add_sub_cancel_left]
    · simp only [listCopyFwdAux_succ, List.getElem?_set_ne (Ne.symm heq)]
      rw [ih i hi]
      have hc : (dst ≤ i ∧ i < dst + d) ↔ (dst ≤ i ∧ i < dst + (d + 1)) := by omega
      simp [hc]

/-- Reference specification for backward copy (`src < dst`) of `d` steps out of `n`. -/
def listCopyBwdAux (dst src n : Nat) : Nat → List (BitVec 8) → List (BitVec 8)
  | 0, bs => bs
  | d + 1, bs =>
    let cur := listCopyBwdAux dst src n d bs
    let k := n - 1 - d
    cur.set (dst + k) (cur[src + k]?.getD 0#8)

private theorem listCopyBwdAux_zero (dst src n : Nat) (bs : List (BitVec 8)) :
    listCopyBwdAux dst src n 0 bs = bs := rfl

private theorem listCopyBwdAux_succ (dst src n d : Nat) (bs : List (BitVec 8)) :
    listCopyBwdAux dst src n (d + 1) bs =
      (listCopyBwdAux dst src n d bs).set (dst + (n - 1 - d))
        ((listCopyBwdAux dst src n d bs)[src + (n - 1 - d)]?.getD 0#8) := rfl

theorem listCopyBwdAux_length (dst src n : Nat) :
    ∀ d bs, (listCopyBwdAux dst src n d bs).length = bs.length
  | 0, _ => rfl
  | d + 1, bs => by simp [listCopyBwdAux_succ, listCopyBwdAux_length dst src n d bs]

theorem listCopyBwdAux_memmove (dst src n : Nat) (hlt : src < dst) :
    ∀ d (bs : List (BitVec 8)), d ≤ n → dst + n ≤ bs.length → src + n ≤ bs.length →
      ∀ i, i < bs.length →
        (listCopyBwdAux dst src n d bs)[i]?.getD 0#8 =
          if dst + (n - d) ≤ i ∧ i < dst + n then bs[src + (i - dst)]?.getD 0#8
          else bs[i]?.getD 0#8
  | 0, bs, _, _, _, i, _ => by
    simp only [listCopyBwdAux_zero, Nat.sub_zero]
    split
    · omega
    · rfl
  | d + 1, bs, hdn, hd, hs, i, hi => by
    have ih := listCopyBwdAux_memmove dst src n hlt d bs (by omega) hd hs
    have hcurLen : (listCopyBwdAux dst src n d bs).length = bs.length :=
      listCopyBwdAux_length dst src n d bs
    have hk : n - 1 - d < n := by omega
    have hdk : dst + (n - 1 - d) < (listCopyBwdAux dst src n d bs).length := by omega
    have hsrcOrig : (listCopyBwdAux dst src n d bs)[src + (n - 1 - d)]?.getD 0#8 =
        bs[src + (n - 1 - d)]?.getD 0#8 := by
      have h := ih (src + (n - 1 - d)) (by omega)
      have hnot : ¬ (dst + (n - d) ≤ src + (n - 1 - d) ∧
          src + (n - 1 - d) < dst + n) := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnot)] at h
      exact h
    by_cases heq : i = dst + (n - 1 - d)
    · subst heq
      simp only [listCopyBwdAux_succ, List.getElem?_set_self hdk, Option.getD_some, hsrcOrig]
      have hcond : dst + (n - (d + 1)) ≤ dst + (n - 1 - d) ∧
          dst + (n - 1 - d) < dst + n := by omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true hcond), Nat.add_sub_cancel_left]
    · simp only [listCopyBwdAux_succ, List.getElem?_set_ne (Ne.symm heq)]
      rw [ih i hi]
      have hc : (dst + (n - d) ≤ i ∧ i < dst + n) ↔
          (dst + (n - (d + 1)) ≤ i ∧ i < dst + n) := by omega
      simp [hc]

private theorem bv64_sub_ne_zero {a b : Nat} (hlt : b < a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 (a - b) ≠ 0#64 := by
  intro h
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at hn
  rw [Nat.mod_eq_of_lt (by omega)] at hn
  omega

private theorem bv64_sub_one_nat {a b : Nat} (hlt : b < a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 (a - b) - 1#64 = BitVec.ofNat 64 (a - (b + 1)) := by
  apply BitVec.eq_of_toNat_eq
  have hle1 : (1#64 : BitVec 64) ≤ BitVec.ofNat 64 (a - b) := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [BitVec.toNat_sub_of_le hle1]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

private theorem bv64_add_one_nat (base : BitVec 64) (off : Nat) :
    (base + BitVec.ofNat 64 off) + 1#64 = base + BitVec.ofNat 64 (off + 1) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

private theorem bv64_sub_one_nat_addr (base : BitVec 64) {x : Nat} (hx : 0 < x) :
    (base + BitVec.ofNat 64 x) - 1#64 = base + BitVec.ofNat 64 (x - 1) := by
  have h1 : BitVec.ofNat 64 (x - 1) + 1#64 = BitVec.ofNat 64 x := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hx' : x - 1 + 1 = x := by omega
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, hx']
  calc
    (base + BitVec.ofNat 64 x) - 1#64
      = (base + BitVec.ofNat 64 (x - 1) + 1#64) - 1#64 := by rw [← h1, BitVec.add_assoc]
    _ = base + BitVec.ofNat 64 (x - 1) := BitVec.add_sub_cancel _ _

theorem emitMemFillLoop_bytes {Γ : Env} {X : XPost} {retTys : List WValTy}
    {Q : Post (wasmRetSig retTys)} {memBase f n64 dstPtr0 : BitVec 64}
    {dstOff : Nat} {byteVal : BitVec 8} {bs : List (BitVec 8)}
    {R' : Mem 64 → Prop} {mem : Mem 64} (jAfter : Cont [i64])
    (hfn : n64.toNat ≤ f.toNat) (hbnd : dstOff + n64.toNat ≤ bs.length)
    (hdst : dstPtr0 = memBase + BitVec.ofNat 64 dstOff)
    (hm : (array (t := i8) memBase bs ⋆ R') mem)
    (hj : ∀ m', (array (t := i8) memBase (listFillAux byteVal dstOff n64.toNat bs) ⋆ R') m' →
      jAfter (BitVec.ofNat 64 (f.toNat - n64.toNat), ()) m') :
    wp Γ Q X (emitMemFillLoop retTys jAfter (.var byteVal) (.var f) (.var n64) (.var dstPtr0))
      mem := by
  simp only [emitMemFillLoop]
  let Inv : Nat → Tup Val [i64, i64, i64] → Mem 64 → Prop := fun r lxs m' =>
    ∃ done, done ≤ n64.toNat ∧ r = n64.toNat - done ∧
      lxs.1 = BitVec.ofNat 64 (f.toNat - done) ∧
      lxs.2.1 = BitVec.ofNat 64 (n64.toNat - done) ∧
      lxs.2.2.1 = memBase + BitVec.ofNat 64 (dstOff + done) ∧
      (array (t := i8) memBase (listFillAux byteVal dstOff done bs) ⋆ R') m'
  refine wp_loop_group Inv (fun lLoop r lxs m' hlLoop hinv => ?_)
    (fun lLoop hlLoop => ?_)
  · rcases lxs with ⟨fHdr, rem, ptr, ⟨⟩⟩
    rcases hinv with ⟨done, hle, rfl, hfHdr, hrem, hptr, hm'⟩
    dsimp only at hfHdr hrem hptr
    dsimp only [Blocks.get_here]
    rw [wp_let_]
    dsimp only [Op.wp, vals, Arg.val]
    simp only [OpCode.wp, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
    rw [wp_jnz_]
    refine ⟨fun hz => ?_, fun hnz => ?_⟩
    · have hz' : rem = 0#64 := by
        by_cases h : rem = 0#64
        · exact h
        · simp [Arg.val, h] at hz
      have hdone : done = n64.toNat := by
        apply Classical.byContradiction; intro hne
        exact bv64_sub_ne_zero (by omega) n64.isLt (hrem ▸ hz')
      subst hdone
      rw [wp_jump_]
      have hfEq : fHdr = BitVec.ofNat 64 (f.toNat - n64.toNat) := hfHdr
      rw [hfEq]
      exact hj m' hm'
    · have hdn : done < n64.toNat := by
        apply Classical.byContradiction; intro hge
        have hdone : done = n64.toNat := by omega
        subst hdone
        simp only [Nat.sub_self] at hrem; simp [Arg.val, hrem] at hnz
      have hfne : fHdr ≠ 0#64 := hfHdr ▸ bv64_sub_ne_zero (by omega) f.isLt
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, Arg.val, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
      rw [wp_jnz_]
      refine ⟨fun hfz => by simp [Arg.val, hfne] at hfz, fun _ => ?_⟩
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      have hidxLt : dstOff + done < (listFillAux byteVal dstOff done bs).length := by
        rw [listFillAux_length]; omega
      have hi8 : (i8 : Ty).bytes = 1 := rfl
      rw [wp_store_]
      obtain ⟨hsok, hm''⟩ := store_array (t := i8) byteVal (by decide) hidxLt hm'
      rw [hi8, Nat.one_mul, ← hptr] at hsok hm''
      refine ⟨by simpa [Arg.val] using hsok, ?_⟩
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      rw [wp_jump_]
      refine hlLoop (n64.toNat - (done + 1)) (fHdr - 1#64, rem - 1#64, ptr + 1#64, ())
        _ (by omega) ?_
      refine ⟨done + 1, by omega, rfl, ?_, ?_, ?_, hm''⟩
      · rw [hfHdr, bv64_sub_one_nat (by omega) f.isLt]
      · rw [hrem, bv64_sub_one_nat hdn n64.isLt]
      · rw [hptr, bv64_add_one_nat, Nat.add_assoc]
  · rw [wp_jump_]
    refine hlLoop n64.toNat (f, n64, dstPtr0, ()) mem ?_
    refine ⟨0, Nat.zero_le _, rfl, ?_, ?_, ?_, hm⟩
    · simp [BitVec.ofNat_toNat]
    · simp [BitVec.ofNat_toNat]
    · simp [hdst]

theorem emitMemCopyLoop_fwd_bytes {Γ : Env} {X : XPost} {retTys : List WValTy}
    {Q : Post (wasmRetSig retTys)} {memBase f n64 dstPtr0 srcPtr0 : BitVec 64}
    {dstOff srcOff : Nat} {bs : List (BitVec 8)}
    {R' : Mem 64 → Prop} {mem : Mem 64} (jAfter : Cont [i64])
    (hfn : n64.toNat ≤ f.toNat) (hdBnd : dstOff + n64.toNat ≤ bs.length)
    (hsBnd : srcOff + n64.toNat ≤ bs.length)
    (hdst : dstPtr0 = memBase + BitVec.ofNat 64 dstOff)
    (hsrc : srcPtr0 = memBase + BitVec.ofNat 64 srcOff)
    (hm : (array (t := i8) memBase bs ⋆ R') mem)
    (hj : ∀ m',
      (array (t := i8) memBase (listCopyFwdAux dstOff srcOff n64.toNat bs) ⋆ R') m' →
      jAfter (BitVec.ofNat 64 (f.toNat - n64.toNat), ()) m') :
    wp Γ Q X (emitMemCopyLoop true retTys jAfter (.var f) (.var n64) (.var dstPtr0) (.var srcPtr0))
      mem := by
  simp only [emitMemCopyLoop]
  let Inv : Nat → Tup Val [i64, i64, i64, i64] → Mem 64 → Prop := fun r lxs m' =>
    ∃ done, done ≤ n64.toNat ∧ r = n64.toNat - done ∧
      lxs.1 = BitVec.ofNat 64 (f.toNat - done) ∧
      lxs.2.1 = BitVec.ofNat 64 (n64.toNat - done) ∧
      lxs.2.2.1 = memBase + BitVec.ofNat 64 (dstOff + done) ∧
      lxs.2.2.2.1 = memBase + BitVec.ofNat 64 (srcOff + done) ∧
      (array (t := i8) memBase (listCopyFwdAux dstOff srcOff done bs) ⋆ R') m'
  refine wp_loop_group Inv (fun lLoop r lxs m' hlLoop hinv => ?_)
    (fun lLoop hlLoop => ?_)
  · rcases lxs with ⟨fHdr, rem, dPtr, sPtr, ⟨⟩⟩
    rcases hinv with ⟨done, hle, rfl, hfHdr, hrem, hdPtr, hsPtr, hm'⟩
    dsimp only at hfHdr hrem hdPtr hsPtr
    dsimp only [Blocks.get_here]
    rw [wp_let_]
    dsimp only [Op.wp, vals, Arg.val]
    simp only [OpCode.wp, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
    rw [wp_jnz_]
    refine ⟨fun hz => ?_, fun hnz => ?_⟩
    · have hz' : rem = 0#64 := by
        by_cases h : rem = 0#64
        · exact h
        · simp [Arg.val, h] at hz
      have hdone : done = n64.toNat := by
        apply Classical.byContradiction; intro hne
        exact bv64_sub_ne_zero (by omega) n64.isLt (hrem ▸ hz')
      subst hdone
      rw [wp_jump_]
      have hfEq : fHdr = BitVec.ofNat 64 (f.toNat - n64.toNat) := hfHdr
      rw [hfEq]
      exact hj m' hm'
    · have hdn : done < n64.toNat := by
        apply Classical.byContradiction; intro hge
        have hdone : done = n64.toNat := by omega
        subst hdone
        simp only [Nat.sub_self] at hrem; simp [Arg.val, hrem] at hnz
      have hfne : fHdr ≠ 0#64 := hfHdr ▸ bv64_sub_ne_zero (by omega) f.isLt
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, Arg.val, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
      rw [wp_jnz_]
      refine ⟨fun hfz => by simp [Arg.val, hfne] at hfz, fun _ => ?_⟩
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      have hsLt : srcOff + done < (listCopyFwdAux dstOff srcOff done bs).length := by
        rw [listCopyFwdAux_length]; omega
      have hdLt : dstOff + done < (listCopyFwdAux dstOff srcOff done bs).length := by
        rw [listCopyFwdAux_length]; omega
      have hi8 : (i8 : Ty).bytes = 1 := rfl
      rw [wp_load_]
      have hload := loadVal_array (t := i8) (by decide) hsLt hm'
      rw [hi8, Nat.one_mul, ← hsPtr] at hload
      refine ⟨(listCopyFwdAux dstOff srcOff done bs)[srcOff + done], by simpa [Arg.val] using hload,
        ?_⟩
      rw [wp_store_]
      obtain ⟨hsok, hm''⟩ := store_array (t := i8)
        ((listCopyFwdAux dstOff srcOff done bs)[srcOff + done]) (by decide) hdLt hm'
      rw [hi8, Nat.one_mul, ← hdPtr] at hsok hm''
      refine ⟨by simpa [Arg.val] using hsok, ?_⟩
      have hm''' : (array (t := i8) memBase (listCopyFwdAux dstOff srcOff (done + 1) bs) ⋆ R')
          (storeMem m' i8 dPtr (listCopyFwdAux dstOff srcOff done bs)[srcOff + done]) := by
        simpa [listCopyFwdAux_succ, List.getElem?_eq_getElem hsLt] using hm''
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      rw [wp_jump_]
      refine hlLoop (n64.toNat - (done + 1))
        (fHdr - 1#64, rem - 1#64, dPtr + 1#64, sPtr + 1#64, ()) _ (by omega) ?_
      refine ⟨done + 1, by omega, rfl, ?_, ?_, ?_, ?_, by simpa [Arg.val] using hm'''⟩
      · rw [hfHdr, bv64_sub_one_nat (by omega) f.isLt]
      · rw [hrem, bv64_sub_one_nat hdn n64.isLt]
      · rw [hdPtr, bv64_add_one_nat, Nat.add_assoc]
      · rw [hsPtr, bv64_add_one_nat, Nat.add_assoc]
  · rw [wp_jump_]
    refine hlLoop n64.toNat (f, n64, dstPtr0, srcPtr0, ()) mem ?_
    refine ⟨0, Nat.zero_le _, rfl, ?_, ?_, ?_, ?_, hm⟩
    · simp [BitVec.ofNat_toNat]
    · simp [BitVec.ofNat_toNat]
    · simp [hdst]
    · simp [hsrc]

theorem emitMemCopyLoop_bwd_bytes {Γ : Env} {X : XPost} {retTys : List WValTy}
    {Q : Post (wasmRetSig retTys)} {memBase f n64 dstPtr0 srcPtr0 : BitVec 64}
    {dstOff srcOff : Nat} {bs : List (BitVec 8)}
    {R' : Mem 64 → Prop} {mem : Mem 64} (jAfter : Cont [i64])
    (hfn : n64.toNat ≤ f.toNat) (hdBnd : dstOff + n64.toNat ≤ bs.length)
    (hsBnd : srcOff + n64.toNat ≤ bs.length)
    (hdst : dstPtr0 = memBase + BitVec.ofNat 64 (dstOff + n64.toNat))
    (hsrc : srcPtr0 = memBase + BitVec.ofNat 64 (srcOff + n64.toNat))
    (hm : (array (t := i8) memBase bs ⋆ R') mem)
    (hj : ∀ m',
      (array (t := i8) memBase (listCopyBwdAux dstOff srcOff n64.toNat n64.toNat bs) ⋆ R') m' →
      jAfter (BitVec.ofNat 64 (f.toNat - n64.toNat), ()) m') :
    wp Γ Q X (emitMemCopyLoop false retTys jAfter (.var f) (.var n64) (.var dstPtr0) (.var srcPtr0))
      mem := by
  simp only [emitMemCopyLoop]
  let Inv : Nat → Tup Val [i64, i64, i64, i64] → Mem 64 → Prop := fun r lxs m' =>
    ∃ done, done ≤ n64.toNat ∧ r = n64.toNat - done ∧
      lxs.1 = BitVec.ofNat 64 (f.toNat - done) ∧
      lxs.2.1 = BitVec.ofNat 64 (n64.toNat - done) ∧
      lxs.2.2.1 = memBase + BitVec.ofNat 64 (dstOff + (n64.toNat - done)) ∧
      lxs.2.2.2.1 = memBase + BitVec.ofNat 64 (srcOff + (n64.toNat - done)) ∧
      (array (t := i8) memBase (listCopyBwdAux dstOff srcOff n64.toNat done bs) ⋆ R') m'
  refine wp_loop_group Inv (fun lLoop r lxs m' hlLoop hinv => ?_)
    (fun lLoop hlLoop => ?_)
  · rcases lxs with ⟨fHdr, rem, dPtr, sPtr, ⟨⟩⟩
    rcases hinv with ⟨done, hle, rfl, hfHdr, hrem, hdPtr, hsPtr, hm'⟩
    dsimp only at hfHdr hrem hdPtr hsPtr
    dsimp only [Blocks.get_here]
    rw [wp_let_]
    dsimp only [Op.wp, vals, Arg.val]
    simp only [OpCode.wp, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
    rw [wp_jnz_]
    refine ⟨fun hz => ?_, fun hnz => ?_⟩
    · have hz' : rem = 0#64 := by
        by_cases h : rem = 0#64
        · exact h
        · simp [Arg.val, h] at hz
      have hdone : done = n64.toNat := by
        apply Classical.byContradiction; intro hne
        exact bv64_sub_ne_zero (by omega) n64.isLt (hrem ▸ hz')
      subst hdone
      rw [wp_jump_]
      have hfEq : fHdr = BitVec.ofNat 64 (f.toNat - n64.toNat) := hfHdr
      rw [hfEq]
      exact hj m' hm'
    · have hdn : done < n64.toNat := by
        apply Classical.byContradiction; intro hge
        have hdone : done = n64.toNat := by omega
        subst hdone
        simp only [Nat.sub_self] at hrem; simp [Arg.val, hrem] at hnz
      have hfne : fHdr ≠ 0#64 := hfHdr ▸ bv64_sub_ne_zero (by omega) f.isLt
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, Arg.val, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
      rw [wp_jnz_]
      refine ⟨fun hfz => by simp [Arg.val, hfne] at hfz, fun _ => ?_⟩
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      rw [wp_let_]
      simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte]
      let k : Nat := n64.toNat - 1 - done
      have hkEq : dstOff + (n64.toNat - done) - 1 = dstOff + k := by omega
      have hskEq : srcOff + (n64.toNat - done) - 1 = srcOff + k := by omega
      have hdSub : dPtr - 1#64 = memBase + BitVec.ofNat 64 (dstOff + k) := by
        rw [hdPtr, bv64_sub_one_nat_addr memBase (by omega), hkEq]
      have hsSub : sPtr - 1#64 = memBase + BitVec.ofNat 64 (srcOff + k) := by
        rw [hsPtr, bv64_sub_one_nat_addr memBase (by omega), hskEq]
      have hsLt : srcOff + k < (listCopyBwdAux dstOff srcOff n64.toNat done bs).length := by
        rw [listCopyBwdAux_length]; omega
      have hdLt : dstOff + k < (listCopyBwdAux dstOff srcOff n64.toNat done bs).length := by
        rw [listCopyBwdAux_length]; omega
      have hi8 : (i8 : Ty).bytes = 1 := rfl
      rw [wp_load_]
      have hload := loadVal_array (t := i8) (by decide) hsLt hm'
      rw [hi8, Nat.one_mul, ← hsSub] at hload
      refine ⟨(listCopyBwdAux dstOff srcOff n64.toNat done bs)[srcOff + k],
        by simpa [Arg.val] using hload, ?_⟩
      rw [wp_store_]
      obtain ⟨hsok, hm''⟩ := store_array (t := i8)
        ((listCopyBwdAux dstOff srcOff n64.toNat done bs)[srcOff + k]) (by decide) hdLt hm'
      rw [hi8, Nat.one_mul, ← hdSub] at hsok hm''
      refine ⟨by simpa [Arg.val] using hsok, ?_⟩
      have hm''' :
          (array (t := i8) memBase (listCopyBwdAux dstOff srcOff n64.toNat (done + 1) bs) ⋆ R')
            (storeMem m' i8 (dPtr - 1#64)
              (listCopyBwdAux dstOff srcOff n64.toNat done bs)[srcOff + k]) := by
        simpa [listCopyBwdAux_succ, k, List.getElem?_eq_getElem hsLt] using hm''
      rw [wp_jump_]
      refine hlLoop (n64.toNat - (done + 1))
        (fHdr - 1#64, rem - 1#64, dPtr - 1#64, sPtr - 1#64, ()) _ (by omega) ?_
      refine ⟨done + 1, by omega, rfl, ?_, ?_, ?_, ?_, by simpa [Arg.val] using hm'''⟩
      · rw [hfHdr, bv64_sub_one_nat (by omega) f.isLt]
      · rw [hrem, bv64_sub_one_nat hdn n64.isLt]
      · rw [hdSub]
        exact congrArg (fun x => memBase + BitVec.ofNat 64 (dstOff + x)) (by dsimp only [k]; omega)
      · rw [hsSub]
        exact congrArg (fun x => memBase + BitVec.ofNat 64 (srcOff + x)) (by dsimp only [k]; omega)
  · rw [wp_jump_]
    refine hlLoop n64.toNat (f, n64, dstPtr0, srcPtr0, ()) mem ?_
    refine ⟨0, Nat.zero_le _, rfl, ?_, ?_, ?_, ?_, hm⟩
    · simp [BitVec.ofNat_toNat]
    · simp [BitVec.ofNat_toNat]
    · simpa [Nat.sub_zero] using hdst
    · simpa [Nat.sub_zero] using hsrc

/-! ## 4. Concrete Behavioral & Adversarial `Func.wp` Proofs -/

private theorem get?Int_zero {α : Type} (a : α) (xs : List α) :
    List.get?Internal (a :: xs) 0 = some a := rfl

private theorem get?Int_succ {α : Type} (a : α) (xs : List α) (n : Nat) :
    List.get?Internal (a :: xs) (n + 1) = List.get?Internal xs n := rfl

private theorem appendZeroLocals_nil {V : Ty → Type} (xs : Tup (Arg V) []) :
    appendZeroLocals [] [] xs = () := rfl

private theorem bv32_toNat_eq_setWidth64 (v : BitVec 32) :
    (v.setWidth 64).toNat = v.toNat := by
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

private theorem bv32_setWidth64_eq_ofNat (v : BitVec 32) :
    v.setWidth 64 = BitVec.ofNat 64 v.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [bv32_toNat_eq_setWidth64, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

/-- Concrete `Func.wp` behavioral proof for `memory.size`: returns current pages
`(curLen >>> 16).setWidth 32` without touching memory (`mem' = mem`) or host frame `R`. -/
theorem bm_size_ok (Γ : Env) (vmCtx memBase curLen memCap fuel : BitVec 64)
    (R : Mem 64 → Prop) (mem : Mem 64) (X : XPost)
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem) :
    Func.wp Γ (lowerFn bulkMod fnSize).body (vmCtx, fuel, ()) mem
      (fun ys m' => ys = (0#32, fuel, (curLen >>> 16).setWidth 32, ()) ∧ m' = mem ∧
        WasmMemInv true vmCtx memBase curLen memCap R m') X := by
  simp only [Func.wp, lowerFn, lowerFuncBody, bulkMod, fnSize,
    GetElem?.getElem?, get?Int_zero, Option.getD, Option.map, Option.isSome,
    List.map, List.append, List.nil_append, WMemSpec.maxBytes, WMemSpec.effectiveMaxPages,
    WValTy.toTy, labelSig]
  refine wp_join_group
    (fun xs m' => xs = (fuel, (curLen >>> 16).setWidth 32, ()) ∧ m' = mem ∧
      WasmMemInv true vmCtx memBase curLen memCap R m')
    (fun jRet xs m' h => ?_) (fun _ _ => ?_)
  · rcases xs with ⟨fRet, rRet, ⟨⟩⟩
    rcases h with ⟨hxs, rfl, hRm⟩
    have hf : fRet = fuel := by cases hxs; rfl
    have hr : rRet = (curLen >>> 16).setWidth 32 := by cases hxs; rfl
    dsimp only [Blocks.get_here, tupSplit, varsTup]
    rw [wp_ret_]
    exact ⟨by simp [vals, hf, hr], rfl, hRm⟩
  · simp only [lowerSeq, lowerSimpleInstr, appendZeroLocals_nil,
      popArgsAux, popExpectS, Bind.bind, Option.bind, ↓reduceIte]
    refine emitMemSize_wp (.var vmCtx) rfl hm _ ?_
    rw [wp_ret_]
    exact ⟨by simp [vals], rfl, hm⟩

/-- Concrete `Func.wp` behavioral proof for valid `memory.grow (delta := 1#32)`: zeroes all `8192`
64-bit words in `[memBase + 65536, memBase + 131072)`, updates `[vmCtx + 8]` to `131072#64`,
returns `(0#32, fuel - 1#64, 1#32, ())`, and preserves `memBase..+65536` and host frame `R`. -/
theorem bm_grow_ok (Γ : Env) (vmCtx memBase fuel : BitVec 64)
    (oldWs : List (BitVec 64)) (hlen : oldWs.length = 8192)
    (R : Mem 64 → Prop) (mem : Mem 64) (X : XPost) (hf : 1 ≤ fuel.toNat)
    (hm : (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) 65536#64 ⋆
      cell64 (vmCtx + 16#64) 131072#64 ⋆ region memBase 65536 ⋆
      array64 (memBase + 65536#64) oldWs ⋆ R) mem) :
    Func.wp Γ (lowerFn bulkMod fnGrow).body (vmCtx, fuel, 1#32, ()) mem
      (fun ys m' => ys = (0#32, fuel - 1#64, 1#32, ()) ∧
        (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) 131072#64 ⋆
          cell64 (vmCtx + 16#64) 131072#64 ⋆ region memBase 65536 ⋆
          array64 (memBase + 65536#64) (List.replicate 8192 0#64) ⋆ R) m') X := by
  simp only [Func.wp, lowerFn, lowerFuncBody, bulkMod, fnGrow,
    GetElem?.getElem?, get?Int_succ, get?Int_zero, Option.getD, Option.map, Option.isSome,
    List.map, List.append, List.cons_append, List.nil_append,
    WMemSpec.maxBytes, WMemSpec.effectiveMaxPages, WValTy.toTy, labelSig]
  refine wp_join_group
    (fun xs m' => xs.1 = fuel - 1#64 ∧ xs.2.2.1 = 1#32 ∧
      (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) 131072#64 ⋆
        cell64 (vmCtx + 16#64) 131072#64 ⋆ region memBase 65536 ⋆
        array64 (memBase + 65536#64) (List.replicate 8192 0#64) ⋆ R) m')
    (fun _ xs m' h => ?_) (fun _ _ => ?_)
  · rcases xs with ⟨fRet, dLoc, rRet, ⟨⟩⟩
    rcases h with ⟨hfEq, hrEq, hm'⟩
    dsimp only at hfEq hrEq
    dsimp only [Blocks.get_here, tupSplit, varsTup]
    rw [wp_ret_]
    rw [hfEq, hrEq]
    exact ⟨rfl, hm'⟩
  · simp only [lowerSeq, lowerSimpleInstr, pop32, popArgsAux, popExpectS, Bind.bind,
      Option.bind, varsTup, ↓reduceIte]
    simp only [emitMemGrow]
    refine wp_join_group
      (fun xs m' => xs = (fuel - 1#64, 1#32, ()) ∧
        (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) 131072#64 ⋆
          cell64 (vmCtx + 16#64) 131072#64 ⋆ region memBase 65536 ⋆
          array64 (memBase + 65536#64) (List.replicate 8192 0#64) ⋆ R) m')
      (fun _ xs m' ⟨hxs, hm'⟩ => by
        rcases xs with ⟨fD, rD, ⟨⟩⟩
        dsimp only [Blocks.get_here]
        rw [wp_ret_]
        rcases hxs with ⟨rfl, rfl⟩
        exact ⟨rfl, hm'⟩)
      (fun jDone hjDone => ?_)
    have h0 : (cell64 vmCtx memBase ⋆ (cell64 (vmCtx + 8#64) 65536#64 ⋆
        cell64 (vmCtx + 16#64) 131072#64 ⋆ region memBase 65536 ⋆
        array64 (memBase + 65536#64) oldWs ⋆ R)) mem :=
      sep_cast hm (by ac_rfl)
    rw [wp_load_]
    refine ⟨memBase, loadVal_cell64 h0, ?_⟩
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    rw [wp_load_]
    have h8 : (cell64 (vmCtx + 8#64) 65536#64 ⋆ (cell64 vmCtx memBase ⋆
        cell64 (vmCtx + 16#64) 131072#64 ⋆ region memBase 65536 ⋆
        array64 (memBase + 65536#64) oldWs ⋆ R)) mem :=
      sep_cast hm (by ac_rfl)
    refine ⟨65536#64, loadVal_cell64 h8, ?_⟩
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    rw [wp_load_]
    have h16 : (cell64 (vmCtx + 16#64) 131072#64 ⋆ (cell64 vmCtx memBase ⋆
        cell64 (vmCtx + 8#64) 65536#64 ⋆ region memBase 65536 ⋆
        array64 (memBase + 65536#64) oldWs ⋆ R)) mem :=
      sep_cast hm (by ac_rfl)
    refine ⟨131072#64, loadVal_cell64 h16, ?_⟩
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val]
    refine ⟨by decide, ?_⟩
    rw [wp_let_]
    dsimp only [Op.wp, vals, Arg.val]
    simp only [OpCode.wp, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
    rw [wp_jnz_]
    refine ⟨fun hz => by exfalso; dsimp only [Arg.val] at hz; revert hz; decide, fun _ => ?_⟩
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals]
    refine ⟨by decide, ?_⟩
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    rw [wp_let_]
    dsimp only [Op.wp, vals, Arg.val]
    simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
      liftCmp, CmpOp.evalBits]
    rw [wp_let_]
    dsimp only [Op.wp, vals, Arg.val]
    simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
      liftCmp, CmpOp.evalBits]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, Ty.hasFloat, Bool.false_eq_true,
      ↓reduceIte, liftCmp, CmpOp.evalBits]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2]
    rw [wp_jnz_]
    refine ⟨fun _ => ?_, fun hbad => by
      exfalso; revert hbad
      dsimp only [Arg.val]; decide⟩
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    simp only [emitMemGrowLoop]
    refine wp_unroll_group (fun lPage hlPage => ?_)
    rw [wp_jump_]
    apply hlPage (fuel, 1#64, memBase + 65536#64, ()) mem
    dsimp only [Blocks.get_here]
    rw [wp_let_]
    dsimp only [Op.wp, vals, Arg.val]
    simp only [OpCode.wp, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
    rw [wp_jnz_]
    refine ⟨fun h0 => by exfalso; dsimp only [Arg.val] at h0; revert h0; decide, fun _ => ?_⟩
    have hfne : fuel ≠ 0#64 := fun h0 => by simp [h0] at hf
    rw [wp_let_]
    dsimp only [Op.wp, vals, Arg.val]
    simp only [OpCode.wp, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
    rw [wp_jnz_]
    refine ⟨fun hfz => by simp [Arg.val, hfne] at hfz, fun _ => ?_⟩
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    have hpage : (array64 (memBase + 65536#64) oldWs ⋆ (cell64 vmCtx memBase ⋆
        cell64 (vmCtx + 8#64) 65536#64 ⋆ cell64 (vmCtx + 16#64) 131072#64 ⋆
        region memBase 65536 ⋆ R)) mem :=
      sep_cast hm (by ac_rfl)
    refine emitMemZeroPage_zero hlen (.var (memBase + 65536#64)) rfl hpage _ fun m' hm' => ?_
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    rw [wp_jump_]
    apply hlPage (fuel - 1#64, 0#64, memBase + 65536#64 + 65536#64, ()) m'
    dsimp only [Blocks.get_here]
    rw [wp_let_]
    dsimp only [Op.wp, vals, Arg.val]
    simp only [OpCode.wp, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
    rw [wp_jnz_]
    refine ⟨fun _ => ?_, fun hnz => by exfalso; dsimp only [Arg.val] at hnz; revert hnz; decide⟩
    have hm'8 : (cell64 (vmCtx + 8#64) 65536#64 ⋆ (cell64 vmCtx memBase ⋆
        cell64 (vmCtx + 16#64) 131072#64 ⋆ region memBase 65536 ⋆
        array64 (memBase + 65536#64) (List.replicate 8192 0#64) ⋆ R)) m' :=
      sep_cast hm' (by ac_rfl)
    rw [wp_store_]
    obtain ⟨hsok, hm''⟩ := store_cell64 (131072#64) hm'8
    refine ⟨by simpa [Arg.val,
        show ((1#32 : BitVec 32).setWidth 64 <<< 16) = 65536#64 by decide,
        show (65536#64 + 65536#64 : BitVec 64) = 131072#64 by decide] using hsok, ?_⟩
    rw [wp_jump_]
    exact hjDone (fuel - 1#64, ((65536#64 >>> 16 : BitVec 64).setWidth 32), ()) _
      ⟨rfl, sep_cast hm'' (by ac_rfl)⟩

/-- Concrete `Func.wp` behavioral proof for over-cap `memory.grow (delta := 2#32)`: returns
`0xFFFFFFFF#32` (`-1`) with `status = 0#32`, `mem' = mem` (zero writes), and `R mem'`. -/
theorem bm_grow_fail (Γ : Env) (vmCtx memBase fuel : BitVec 64)
    (R : Mem 64 → Prop) (mem : Mem 64) (X : XPost)
    (hm : WasmMemInv true vmCtx memBase 65536#64 131072#64 R mem) :
    Func.wp Γ (lowerFn bulkMod fnGrow).body (vmCtx, fuel, 2#32, ()) mem
      (fun ys m' => ys = (0#32, fuel, 0xFFFFFFFF#32, ()) ∧ m' = mem ∧
        WasmMemInv true vmCtx memBase 65536#64 131072#64 R m') X := by
  rcases hm with ⟨hcap, hsep⟩
  simp only [Func.wp, lowerFn, lowerFuncBody, bulkMod, fnGrow,
    GetElem?.getElem?, get?Int_succ, get?Int_zero, Option.getD, Option.map, Option.isSome,
    List.map, List.append, List.cons_append, List.nil_append,
    WMemSpec.maxBytes, WMemSpec.effectiveMaxPages, WValTy.toTy, labelSig]
  refine wp_join_group
    (fun xs m' => xs.1 = fuel ∧ xs.2.2.1 = 0xFFFFFFFF#32 ∧ m' = mem ∧
      WasmMemInv true vmCtx memBase 65536#64 131072#64 R m')
    (fun _ xs m' h => ?_) (fun _ _ => ?_)
  · rcases xs with ⟨fRet, dLoc, rRet, ⟨⟩⟩
    rcases h with ⟨hfEq, hrEq, rfl, hm'⟩
    dsimp only at hfEq hrEq
    dsimp only [Blocks.get_here, tupSplit, varsTup]
    rw [wp_ret_]
    rw [hfEq, hrEq]
    exact ⟨rfl, rfl, hm'⟩
  · simp only [lowerSeq, lowerSimpleInstr, pop32, popArgsAux, popExpectS, Bind.bind,
      Option.bind, varsTup, ↓reduceIte]
    simp only [emitMemGrow]
    refine wp_join_group
      (fun xs m' => xs = (fuel, 0xFFFFFFFF#32, ()) ∧ m' = mem ∧
        WasmMemInv true vmCtx memBase 65536#64 131072#64 R m')
      (fun _ xs m' ⟨hxs, hmeq, hm'⟩ => by
        rcases xs with ⟨fD, rD, ⟨⟩⟩
        dsimp only [Blocks.get_here]
        rw [wp_ret_]
        rcases hxs with ⟨rfl, rfl⟩
        exact ⟨rfl, hmeq, hm'⟩)
      (fun jDone hjDone => ?_)
    have h0 : (cell64 vmCtx memBase ⋆ (cell64 (vmCtx + 8#64) 65536#64 ⋆
        cell64 (vmCtx + 16#64) 131072#64 ⋆ region memBase 131072 ⋆ R)) mem :=
      sep_cast hsep (by ac_rfl)
    rw [wp_load_]
    refine ⟨memBase, loadVal_cell64 h0, ?_⟩
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    rw [wp_load_]
    have h8 : (cell64 (vmCtx + 8#64) 65536#64 ⋆ (cell64 vmCtx memBase ⋆
        cell64 (vmCtx + 16#64) 131072#64 ⋆ region memBase 131072 ⋆ R)) mem :=
      sep_cast hsep (by ac_rfl)
    refine ⟨65536#64, loadVal_cell64 h8, ?_⟩
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    rw [wp_load_]
    have h16 : (cell64 (vmCtx + 16#64) 131072#64 ⋆ (cell64 vmCtx memBase ⋆
        cell64 (vmCtx + 8#64) 65536#64 ⋆ region memBase 131072 ⋆ R)) mem :=
      sep_cast hsep (by ac_rfl)
    refine ⟨131072#64, loadVal_cell64 h16, ?_⟩
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val]
    refine ⟨by decide, ?_⟩
    rw [wp_let_]
    dsimp only [Op.wp, vals, Arg.val]
    simp only [OpCode.wp, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
    rw [wp_jnz_]
    refine ⟨fun hz => by exfalso; dsimp only [Arg.val] at hz; revert hz; decide, fun _ => ?_⟩
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals]
    refine ⟨by decide, ?_⟩
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
      Bool.false_eq_true, ↓reduceIte]
    rw [wp_let_]
    dsimp only [Op.wp, vals, Arg.val]
    simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
      liftCmp, CmpOp.evalBits]
    rw [wp_let_]
    dsimp only [Op.wp, vals, Arg.val]
    simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
      liftCmp, CmpOp.evalBits]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, Ty.hasFloat, Bool.false_eq_true,
      ↓reduceIte, liftCmp, CmpOp.evalBits]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2]
    rw [wp_let_]
    simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2]
    rw [wp_jnz_]
    refine ⟨fun hok => by exfalso; revert hok; decide, fun _ => ?_⟩
    rw [wp_jump_]
    exact hjDone (fuel, 0xFFFFFFFF#32, ()) mem ⟨rfl, rfl, ⟨hcap, hsep⟩⟩

/-- Concrete `Func.wp` behavioral proof for `memory.fill`: fills `[dst .. dst+n)` with
`val.setWidth 8`, preserves `R`, and deducts `n` fuel units. -/
theorem bm_fill_ok (Γ : Env) (vmCtx memBase memLen memCap fuel : BitVec 64)
    (dst val n : BitVec 32) (bs : List (BitVec 8))
    (R : Mem 64 → Prop) (mem : Mem 64) (X : XPost)
    (hnNz : n ≠ 0#32) (hfn : n.toNat ≤ fuel.toNat)
    (hleLen : dst.toNat + n.toNat ≤ memLen.toNat)
    (hleBs : dst.toNat + n.toNat ≤ bs.length)
    (hm : (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ array (t := i8) memBase bs ⋆ R) mem) :
    Func.wp Γ (lowerFn bulkMod fnFill).body (vmCtx, fuel, dst, val, n, ()) mem
      (fun ys m' => ys = (0#32, BitVec.ofNat 64 (fuel.toNat - n.toNat), ()) ∧
        (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆
          cell64 (vmCtx + 16#64) memCap ⋆
          array (t := i8) memBase (listFillAux (val.setWidth 8) dst.toNat n.toNat bs) ⋆ R) m')
      X := by
  let fEnd := BitVec.ofNat 64 (fuel.toNat - n.toNat)
  let bs' := listFillAux (val.setWidth 8) dst.toNat n.toNat bs
  let InvPost := fun (m' : Mem 64) =>
    (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ array (t := i8) memBase bs' ⋆ R) m'
  simp only [Func.wp, lowerFn, lowerFuncBody, bulkMod, fnFill,
    GetElem?.getElem?, get?Int_succ, get?Int_zero, Option.getD, Option.map, Option.isSome,
    List.map, List.append, List.cons_append, List.nil_append,
    WMemSpec.maxBytes, WMemSpec.effectiveMaxPages, WValTy.toTy, labelSig]
  refine wp_join_group (fun xs m' => xs.1 = fEnd ∧ InvPost m')
    (fun _ xs m' ⟨hfEq, hm'⟩ => by
      rcases xs with ⟨fRet, b0, b1, b2, ⟨⟩⟩
      dsimp only at hfEq
      dsimp only [Blocks.get_here, tupSplit, varsTup]
      rw [wp_ret_]
      rw [hfEq]
      exact ⟨rfl, hm'⟩)
    (fun _ _ => ?_)
  simp only [lowerSeq, WBlockTy.resolve, varsTup, popArgsAux, labelSig,
    List.map, List.cons_append, List.nil_append]
  refine wp_join_group (fun xs m' => xs.1 = fEnd ∧ InvPost m')
    (fun _ xs m' ⟨hfEq, hm'⟩ => by
      rcases xs with ⟨fBlk, b0, b1, b2, ⟨⟩⟩
      dsimp only at hfEq
      dsimp only [Blocks.get_here, tupSplit, varsTup]
      rw [wp_ret_]
      rw [hfEq]
      exact ⟨rfl, hm'⟩)
    (fun jBlk hjBlk => ?_)
  simp only [lowerSimpleInstr]
  dsimp only [appendZeroLocals, zeroArgs, pushArgsAux, getLocal,
    GetElem?.getElem?, List.get?Internal]
  simp only [popArgsAux, pop32, ↓reduceIte]
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val]
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
  rw [wp_jnz_]
  refine ⟨fun hz => by
    have hFalse : decide (n = 0#32) = false := decide_eq_false hnNz
    simp [Arg.val, hFalse] at hz, fun _ => ?_⟩
  simp only [emitMemFill, emitLoadVmCtx]
  have h0 : (cell64 vmCtx memBase ⋆ (cell64 (vmCtx + 8#64) memLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ array (t := i8) memBase bs ⋆ R)) mem :=
    sep_cast hm (by ac_rfl)
  rw [wp_load_]
  refine ⟨memBase, loadVal_cell64 h0, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_load_]
  have h8 : (cell64 (vmCtx + 8#64) memLen ⋆ (cell64 vmCtx memBase ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ array (t := i8) memBase bs ⋆ R)) mem :=
    sep_cast hm (by ac_rfl)
  refine ⟨memLen, loadVal_cell64 h8, ?_⟩
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
    liftCmp, CmpOp.evalBits]
  rw [wp_jnz_]
  refine ⟨fun _ => ?_, fun hnot => by
    exfalso
    have hule : (dst.setWidth 64 + n.setWidth 64).ule memLen = true := by
      rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add,
        bv32_toNat_eq_setWidth64, bv32_toNat_eq_setWidth64,
        Nat.mod_eq_of_lt (by have := dst.isLt; have := n.isLt; omega)]
      exact hleLen
    rw [hule] at hnot
    cases hnot⟩
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  refine wp_join_group (fun xs m' => xs.1 = fEnd ∧ InvPost m')
    (fun jAfter xs m' ⟨hfEq, hm'⟩ => by
      rcases xs with ⟨fA, ⟨⟩⟩
      dsimp only [Blocks.get_here, lowerSeq, popArgsAux, varsTup]
      rw [wp_jump_]
      exact hjBlk (fA, dst, val, n, ()) m' ⟨hfEq, hm'⟩)
    (fun jAfter hjAfter => ?_)
  have hmArr : (array (t := i8) memBase bs ⋆ (cell64 vmCtx memBase ⋆
      cell64 (vmCtx + 8#64) memLen ⋆ cell64 (vmCtx + 16#64) memCap ⋆ R)) mem :=
    sep_cast hm (by ac_rfl)
  have htrunc : val.setWidth 8 = (val.setWidth 8) := rfl
  refine emitMemFillLoop_bytes jAfter
    (n64 := n.setWidth 64) (dstOff := dst.toNat) (byteVal := val.setWidth 8)
    (by rwa [bv32_toNat_eq_setWidth64]) (by rwa [bv32_toNat_eq_setWidth64])
    (by rw [bv32_setWidth64_eq_ofNat]) hmArr fun m' hm' => ?_
  apply hjAfter
  refine ⟨by rw [bv32_toNat_eq_setWidth64], ?_⟩
  rw [bv32_toNat_eq_setWidth64] at hm'
  dsimp only [InvPost, bs']
  exact sep_cast hm' (by ac_rfl)

/-- Concrete `Func.wp` behavioral proof for overlapping forward `memory.copy` (`dst ≤ src`):
matches `listCopyFwdAux` (exact `memmove`), preserves host frame `R`, and deducts `n` fuel. -/
theorem bm_copy_fwd (Γ : Env) (vmCtx memBase memLen memCap fuel : BitVec 64)
    (dst src n : BitVec 32) (bs : List (BitVec 8))
    (R : Mem 64 → Prop) (mem : Mem 64) (X : XPost)
    (hnNz : n ≠ 0#32) (hfwd : dst.toNat ≤ src.toNat) (hfn : n.toNat ≤ fuel.toNat)
    (hdLen : dst.toNat + n.toNat ≤ memLen.toNat) (hsLen : src.toNat + n.toNat ≤ memLen.toNat)
    (hdBs : dst.toNat + n.toNat ≤ bs.length) (hsBs : src.toNat + n.toNat ≤ bs.length)
    (hm : (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ array (t := i8) memBase bs ⋆ R) mem) :
    Func.wp Γ (lowerFn bulkMod fnCopy).body (vmCtx, fuel, dst, src, n, ()) mem
      (fun ys m' => ys = (0#32, BitVec.ofNat 64 (fuel.toNat - n.toNat), ()) ∧
        (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆
          cell64 (vmCtx + 16#64) memCap ⋆
          array (t := i8) memBase (listCopyFwdAux dst.toNat src.toNat n.toNat bs) ⋆ R) m') X := by
  let fEnd := BitVec.ofNat 64 (fuel.toNat - n.toNat)
  let bs' := listCopyFwdAux dst.toNat src.toNat n.toNat bs
  let InvPost := fun (m' : Mem 64) =>
    (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ array (t := i8) memBase bs' ⋆ R) m'
  simp only [Func.wp, lowerFn, lowerFuncBody, bulkMod, fnCopy,
    GetElem?.getElem?, get?Int_succ, get?Int_zero, Option.getD, Option.map, Option.isSome,
    List.map, List.append, List.cons_append, List.nil_append,
    WMemSpec.maxBytes, WMemSpec.effectiveMaxPages, WValTy.toTy, labelSig]
  refine wp_join_group (fun xs m' => xs.1 = fEnd ∧ InvPost m')
    (fun _ xs m' ⟨hfEq, hm'⟩ => by
      rcases xs with ⟨fRet, b0, b1, b2, ⟨⟩⟩
      dsimp only at hfEq
      dsimp only [Blocks.get_here, tupSplit, varsTup]
      rw [wp_ret_]
      rw [hfEq]
      exact ⟨rfl, hm'⟩)
    (fun _ _ => ?_)
  simp only [lowerSeq, WBlockTy.resolve, varsTup, popArgsAux, labelSig,
    List.map, List.cons_append, List.nil_append]
  refine wp_join_group (fun xs m' => xs.1 = fEnd ∧ InvPost m')
    (fun _ xs m' ⟨hfEq, hm'⟩ => by
      rcases xs with ⟨fBlk, b0, b1, b2, ⟨⟩⟩
      dsimp only at hfEq
      dsimp only [Blocks.get_here, tupSplit, varsTup]
      rw [wp_ret_]
      rw [hfEq]
      exact ⟨rfl, hm'⟩)
    (fun jBlk hjBlk => ?_)
  simp only [lowerSimpleInstr]
  dsimp only [appendZeroLocals, zeroArgs, pushArgsAux, getLocal,
    GetElem?.getElem?, List.get?Internal]
  simp only [popArgsAux, pop32, ↓reduceIte]
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val]
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
  rw [wp_jnz_]
  refine ⟨fun hz => by
    have hFalse : decide (n = 0#32) = false := decide_eq_false hnNz
    simp [Arg.val, hFalse] at hz, fun _ => ?_⟩
  simp only [emitMemCopy, emitLoadVmCtx]
  have h0 : (cell64 vmCtx memBase ⋆ (cell64 (vmCtx + 8#64) memLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ array (t := i8) memBase bs ⋆ R)) mem :=
    sep_cast hm (by ac_rfl)
  rw [wp_load_]
  refine ⟨memBase, loadVal_cell64 h0, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_load_]
  have h8 : (cell64 (vmCtx + 8#64) memLen ⋆ (cell64 vmCtx memBase ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ array (t := i8) memBase bs ⋆ R)) mem :=
    sep_cast hm (by ac_rfl)
  refine ⟨memLen, loadVal_cell64 h8, ?_⟩
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
    liftCmp, CmpOp.evalBits]
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
    liftCmp, CmpOp.evalBits]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2]
  rw [wp_jnz_]
  refine ⟨fun _ => ?_, fun hnot => by
    exfalso
    have hu1 : (dst.setWidth 64 + n.setWidth 64).ule memLen = true := by
      rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add,
        bv32_toNat_eq_setWidth64, bv32_toNat_eq_setWidth64,
        Nat.mod_eq_of_lt (by have := dst.isLt; have := n.isLt; omega)]
      exact hdLen
    have hu2 : (src.setWidth 64 + n.setWidth 64).ule memLen = true := by
      rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add,
        bv32_toNat_eq_setWidth64, bv32_toNat_eq_setWidth64,
        Nat.mod_eq_of_lt (by have := src.isLt; have := n.isLt; omega)]
      exact hsLen
    rw [Arg.val, hu1, hu2] at hnot
    cases hnot⟩
  refine wp_join_group (fun xs m' => xs.1 = fEnd ∧ InvPost m')
    (fun jAfter xs m' ⟨hfEq, hm'⟩ => by
      rcases xs with ⟨fA, ⟨⟩⟩
      dsimp only [Blocks.get_here, lowerSeq, popArgsAux, varsTup]
      rw [wp_jump_]
      exact hjBlk (fA, dst, src, n, ()) m' ⟨hfEq, hm'⟩)
    (fun jAfter hjAfter => ?_)
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
    liftCmp, CmpOp.evalBits]
  rw [wp_jnz_]
  refine ⟨fun _ => ?_, fun hnot => by
    exfalso
    have hule : (dst.setWidth 64).ule (src.setWidth 64) = true := by
      rw [BitVec.ule_eq_decide, decide_eq_true_eq,
        bv32_toNat_eq_setWidth64, bv32_toNat_eq_setWidth64]
      exact hfwd
    rw [hule] at hnot
    cases hnot⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  have hmArr : (array (t := i8) memBase bs ⋆ (cell64 vmCtx memBase ⋆
      cell64 (vmCtx + 8#64) memLen ⋆ cell64 (vmCtx + 16#64) memCap ⋆ R)) mem :=
    sep_cast hm (by ac_rfl)
  refine emitMemCopyLoop_fwd_bytes jAfter
    (n64 := n.setWidth 64) (dstOff := dst.toNat) (srcOff := src.toNat)
    (by rwa [bv32_toNat_eq_setWidth64]) (by rwa [bv32_toNat_eq_setWidth64])
    (by rwa [bv32_toNat_eq_setWidth64])
    (by rw [bv32_setWidth64_eq_ofNat]) (by rw [bv32_setWidth64_eq_ofNat]) hmArr fun m' hm' => ?_
  apply hjAfter
  refine ⟨by rw [bv32_toNat_eq_setWidth64], ?_⟩
  rw [bv32_toNat_eq_setWidth64] at hm'
  dsimp only [InvPost, bs']
  exact sep_cast hm' (by ac_rfl)

/-- Concrete `Func.wp` behavioral proof for overlapping backward `memory.copy` (`src < dst`):
matches `listCopyBwdAux` (exact `memmove`), preserves host frame `R`, and deducts `n` fuel. -/
theorem bm_copy_bwd (Γ : Env) (vmCtx memBase memLen memCap fuel : BitVec 64)
    (dst src n : BitVec 32) (bs : List (BitVec 8))
    (R : Mem 64 → Prop) (mem : Mem 64) (X : XPost)
    (hnNz : n ≠ 0#32) (hbwd : src.toNat < dst.toNat) (hfn : n.toNat ≤ fuel.toNat)
    (hdLen : dst.toNat + n.toNat ≤ memLen.toNat) (hsLen : src.toNat + n.toNat ≤ memLen.toNat)
    (hdBs : dst.toNat + n.toNat ≤ bs.length) (hsBs : src.toNat + n.toNat ≤ bs.length)
    (hm : (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ array (t := i8) memBase bs ⋆ R) mem) :
    Func.wp Γ (lowerFn bulkMod fnCopy).body (vmCtx, fuel, dst, src, n, ()) mem
      (fun ys m' => ys = (0#32, BitVec.ofNat 64 (fuel.toNat - n.toNat), ()) ∧
        (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆
          cell64 (vmCtx + 16#64) memCap ⋆
          array (t := i8) memBase
            (listCopyBwdAux dst.toNat src.toNat n.toNat n.toNat bs) ⋆ R) m') X := by
  let fEnd := BitVec.ofNat 64 (fuel.toNat - n.toNat)
  let bs' := listCopyBwdAux dst.toNat src.toNat n.toNat n.toNat bs
  let InvPost := fun (m' : Mem 64) =>
    (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ array (t := i8) memBase bs' ⋆ R) m'
  simp only [Func.wp, lowerFn, lowerFuncBody, bulkMod, fnCopy,
    GetElem?.getElem?, get?Int_succ, get?Int_zero, Option.getD, Option.map, Option.isSome,
    List.map, List.append, List.cons_append, List.nil_append,
    WMemSpec.maxBytes, WMemSpec.effectiveMaxPages, WValTy.toTy, labelSig]
  refine wp_join_group (fun xs m' => xs.1 = fEnd ∧ InvPost m')
    (fun _ xs m' ⟨hfEq, hm'⟩ => by
      rcases xs with ⟨fRet, b0, b1, b2, ⟨⟩⟩
      dsimp only at hfEq
      dsimp only [Blocks.get_here, tupSplit, varsTup]
      rw [wp_ret_]
      rw [hfEq]
      exact ⟨rfl, hm'⟩)
    (fun _ _ => ?_)
  simp only [lowerSeq, WBlockTy.resolve, varsTup, popArgsAux, labelSig,
    List.map, List.cons_append, List.nil_append]
  refine wp_join_group (fun xs m' => xs.1 = fEnd ∧ InvPost m')
    (fun _ xs m' ⟨hfEq, hm'⟩ => by
      rcases xs with ⟨fBlk, b0, b1, b2, ⟨⟩⟩
      dsimp only at hfEq
      dsimp only [Blocks.get_here, tupSplit, varsTup]
      rw [wp_ret_]
      rw [hfEq]
      exact ⟨rfl, hm'⟩)
    (fun jBlk hjBlk => ?_)
  simp only [lowerSimpleInstr]
  dsimp only [appendZeroLocals, zeroArgs, pushArgsAux, getLocal,
    GetElem?.getElem?, List.get?Internal]
  simp only [popArgsAux, pop32, ↓reduceIte]
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val]
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
  rw [wp_jnz_]
  refine ⟨fun hz => by
    have hFalse : decide (n = 0#32) = false := decide_eq_false hnNz
    simp [Arg.val, hFalse] at hz, fun _ => ?_⟩
  simp only [emitMemCopy, emitLoadVmCtx]
  have h0 : (cell64 vmCtx memBase ⋆ (cell64 (vmCtx + 8#64) memLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ array (t := i8) memBase bs ⋆ R)) mem :=
    sep_cast hm (by ac_rfl)
  rw [wp_load_]
  refine ⟨memBase, loadVal_cell64 h0, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_load_]
  have h8 : (cell64 (vmCtx + 8#64) memLen ⋆ (cell64 vmCtx memBase ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ array (t := i8) memBase bs ⋆ R)) mem :=
    sep_cast hm (by ac_rfl)
  refine ⟨memLen, loadVal_cell64 h8, ?_⟩
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
    liftCmp, CmpOp.evalBits]
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
    liftCmp, CmpOp.evalBits]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2]
  rw [wp_jnz_]
  refine ⟨fun _ => ?_, fun hnot => by
    exfalso
    have hu1 : (dst.setWidth 64 + n.setWidth 64).ule memLen = true := by
      rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add,
        bv32_toNat_eq_setWidth64, bv32_toNat_eq_setWidth64,
        Nat.mod_eq_of_lt (by have := dst.isLt; have := n.isLt; omega)]
      exact hdLen
    have hu2 : (src.setWidth 64 + n.setWidth 64).ule memLen = true := by
      rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add,
        bv32_toNat_eq_setWidth64, bv32_toNat_eq_setWidth64,
        Nat.mod_eq_of_lt (by have := src.isLt; have := n.isLt; omega)]
      exact hsLen
    rw [Arg.val, hu1, hu2] at hnot
    cases hnot⟩
  refine wp_join_group (fun xs m' => xs.1 = fEnd ∧ InvPost m')
    (fun jAfter xs m' ⟨hfEq, hm'⟩ => by
      rcases xs with ⟨fA, ⟨⟩⟩
      dsimp only [Blocks.get_here, lowerSeq, popArgsAux, varsTup]
      rw [wp_jump_]
      exact hjBlk (fA, dst, src, n, ()) m' ⟨hfEq, hm'⟩)
    (fun jAfter hjAfter => ?_)
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
    liftCmp, CmpOp.evalBits]
  rw [wp_jnz_]
  refine ⟨fun hnot => by
    have hule : (dst.setWidth 64).ule (src.setWidth 64) = false := by
      rw [BitVec.ule_eq_decide, decide_eq_false_iff_not,
        bv32_toNat_eq_setWidth64, bv32_toNat_eq_setWidth64]
      omega
    dsimp only [Arg.val] at hnot
    rw [hule] at hnot
    exact absurd hnot Bool.false_ne_true, fun _ => ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  have hmArr : (array (t := i8) memBase bs ⋆ (cell64 vmCtx memBase ⋆
      cell64 (vmCtx + 8#64) memLen ⋆ cell64 (vmCtx + 16#64) memCap ⋆ R)) mem :=
    sep_cast hm (by ac_rfl)
  have hdEnd : memBase + (dst.setWidth 64 + n.setWidth 64) =
      memBase + BitVec.ofNat 64 (dst.toNat + n.toNat) := by congr 1
  have hsEnd : memBase + (src.setWidth 64 + n.setWidth 64) =
      memBase + BitVec.ofNat 64 (src.toNat + n.toNat) := by congr 1
  refine emitMemCopyLoop_bwd_bytes jAfter
    (n64 := n.setWidth 64) (dstOff := dst.toNat) (srcOff := src.toNat)
    (by rwa [bv32_toNat_eq_setWidth64]) (by rwa [bv32_toNat_eq_setWidth64])
    (by rwa [bv32_toNat_eq_setWidth64])
    (by rwa [bv32_toNat_eq_setWidth64]) (by rwa [bv32_toNat_eq_setWidth64])
    hmArr fun m' hm' => ?_
  apply hjAfter
  refine ⟨by rw [bv32_toNat_eq_setWidth64], ?_⟩
  rw [bv32_toNat_eq_setWidth64] at hm'
  dsimp only [InvPost, bs']
  exact sep_cast hm' (by ac_rfl)

-- Concrete 8-byte checks for fill, forward overlap copy, and backward overlap `memmove`
private def exBytes : List (BitVec 8) :=
  [0x10#8, 0x11#8, 0x12#8, 0x13#8, 0x14#8, 0x15#8, 0x16#8, 0x17#8]

#guard listFillAux 0xAB#8 2 4 exBytes ==
  [0x10#8, 0x11#8, 0xAB#8, 0xAB#8, 0xAB#8, 0xAB#8, 0x16#8, 0x17#8]

#guard listCopyFwdAux 1 3 4 exBytes ==
  [0x10#8, 0x13#8, 0x14#8, 0x15#8, 0x16#8, 0x15#8, 0x16#8, 0x17#8]

#guard listCopyBwdAux 3 1 4 4 exBytes ==
  [0x10#8, 0x11#8, 0x12#8, 0x11#8, 0x12#8, 0x13#8, 0x14#8, 0x17#8]

/-- Adversarial `u32` wraparound OOB `memory.fill (dst = 0xFFFFFFF0, n = 32)` on 64 KiB memory:
traps cleanly (`status = 1#32`) with zero memory writes (`mem' = mem`) and `R mem'`. -/
theorem bm_fill_oob (Γ : Env) (vmCtx memBase memCap fuel : BitVec 64)
    (R : Mem 64 → Prop) (mem : Mem 64) (X : XPost)
    (hm : WasmMemInv true vmCtx memBase 65536#64 memCap R mem) :
    Func.wp Γ (lowerFn bulkMod fnFill).body (vmCtx, fuel, 0xFFFFFFF0#32, 0xAB#32, 32#32, ()) mem
      (fun ys m' => ys = (1#32, fuel, ()) ∧ m' = mem ∧
        WasmMemInv true vmCtx memBase 65536#64 memCap R m') X := by
  rcases hm with ⟨hcap, hsep⟩
  simp only [Func.wp, lowerFn, lowerFuncBody, bulkMod, fnFill,
    GetElem?.getElem?, get?Int_succ, get?Int_zero, Option.getD, Option.map, Option.isSome,
    List.map, List.append, List.cons_append, List.nil_append,
    WMemSpec.maxBytes, WMemSpec.effectiveMaxPages, WValTy.toTy, labelSig]
  refine wp_join_group (fun _ _ => False) (fun _ _ _ h => False.elim h) (fun _ _ => ?_)
  simp only [lowerSeq, WBlockTy.resolve, varsTup, popArgsAux, labelSig,
    List.map, List.cons_append, List.nil_append]
  refine wp_join_group (fun _ _ => False) (fun _ _ _ h => False.elim h) (fun _ _ => ?_)
  simp only [lowerSimpleInstr]
  dsimp only [appendZeroLocals, zeroArgs, pushArgsAux, getLocal,
    GetElem?.getElem?, List.get?Internal]
  simp only [popArgsAux, pop32, ↓reduceIte]
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val]
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
  rw [wp_jnz_]
  refine ⟨fun hz => by exfalso; dsimp only [Arg.val] at hz; revert hz; decide, fun _ => ?_⟩
  simp only [emitMemFill, emitLoadVmCtx]
  have h0 : (cell64 vmCtx memBase ⋆ (cell64 (vmCtx + 8#64) 65536#64 ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat ⋆ R)) mem :=
    sep_cast hsep (by ac_rfl)
  rw [wp_load_]
  refine ⟨memBase, loadVal_cell64 h0, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_load_]
  have h8 : (cell64 (vmCtx + 8#64) 65536#64 ⋆ (cell64 vmCtx memBase ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat ⋆ R)) mem :=
    sep_cast hsep (by ac_rfl)
  refine ⟨65536#64, loadVal_cell64 h8, ?_⟩
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
    liftCmp, CmpOp.evalBits]
  rw [wp_jnz_]
  refine ⟨fun hin => by
    exfalso
    have hsum : ((0xFFFFFFF0#32 : BitVec 32).setWidth 64 +
        (32#32 : BitVec 32).setWidth 64) = 0x100000010#64 := rfl
    dsimp only [Arg.val] at hin
    rw [hsum] at hin
    revert hin; decide, fun _ => ?_⟩
  rw [wp_ret_]
  exact ⟨by simp [vals], rfl, ⟨hcap, hsep⟩⟩

/-- Adversarial `u32` wraparound OOB `memory.copy (dst = 0xFFFFFFF0, src = 0, n = 32)` on 64 KiB
memory: traps cleanly (`status = 1#32`) with zero memory writes (`mem' = mem`) and `R mem'`. -/
theorem bm_copy_wrap (Γ : Env) (vmCtx memBase memCap fuel : BitVec 64)
    (R : Mem 64 → Prop) (mem : Mem 64) (X : XPost)
    (hm : WasmMemInv true vmCtx memBase 65536#64 memCap R mem) :
    Func.wp Γ (lowerFn bulkMod fnCopy).body (vmCtx, fuel, 0xFFFFFFF0#32, 0#32, 32#32, ()) mem
      (fun ys m' => ys = (1#32, fuel, ()) ∧ m' = mem ∧
        WasmMemInv true vmCtx memBase 65536#64 memCap R m') X := by
  rcases hm with ⟨hcap, hsep⟩
  simp only [Func.wp, lowerFn, lowerFuncBody, bulkMod, fnCopy,
    GetElem?.getElem?, get?Int_succ, get?Int_zero, Option.getD, Option.map, Option.isSome,
    List.map, List.append, List.cons_append, List.nil_append,
    WMemSpec.maxBytes, WMemSpec.effectiveMaxPages, WValTy.toTy, labelSig]
  refine wp_join_group (fun _ _ => False) (fun _ _ _ h => False.elim h) (fun _ _ => ?_)
  simp only [lowerSeq, WBlockTy.resolve, varsTup, popArgsAux, labelSig,
    List.map, List.cons_append, List.nil_append]
  refine wp_join_group (fun _ _ => False) (fun _ _ _ h => False.elim h) (fun _ _ => ?_)
  simp only [lowerSimpleInstr]
  dsimp only [appendZeroLocals, zeroArgs, pushArgsAux, getLocal,
    GetElem?.getElem?, List.get?Internal]
  simp only [popArgsAux, pop32, ↓reduceIte]
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val]
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte, liftCmp, CmpOp.evalBits]
  rw [wp_jnz_]
  refine ⟨fun hz => by exfalso; dsimp only [Arg.val] at hz; revert hz; decide, fun _ => ?_⟩
  simp only [emitMemCopy, emitLoadVmCtx]
  have h0 : (cell64 vmCtx memBase ⋆ (cell64 (vmCtx + 8#64) 65536#64 ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat ⋆ R)) mem :=
    sep_cast hsep (by ac_rfl)
  rw [wp_load_]
  refine ⟨memBase, loadVal_cell64 h0, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_load_]
  have h8 : (cell64 (vmCtx + 8#64) 65536#64 ⋆ (cell64 vmCtx memBase ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ region memBase memCap.toNat ⋆ R)) mem :=
    sep_cast hsep (by ac_rfl)
  refine ⟨65536#64, loadVal_cell64 h8, ?_⟩
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]; simp only [Op.wp, OpCode.wp, vals]; refine ⟨by decide, ?_⟩
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat,
    Bool.false_eq_true, ↓reduceIte]
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
    liftCmp, CmpOp.evalBits]
  rw [wp_let_]
  dsimp only [Op.wp, vals, Arg.val]
  simp only [OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
    liftCmp, CmpOp.evalBits]
  rw [wp_let_]
  simp only [Op.wp, OpCode.wp, vals, Arg.val, lift2]
  rw [wp_jnz_]
  refine ⟨fun hin => by
    exfalso
    have hsum : ((0xFFFFFFF0#32 : BitVec 32).setWidth 64 +
        (32#32 : BitVec 32).setWidth 64) = 0x100000010#64 := rfl
    dsimp only [Arg.val] at hin
    rw [hsum] at hin
    revert hin; decide, fun _ => ?_⟩
  rw [wp_ret_]
  exact ⟨by simp [vals], rfl, ⟨hcap, hsep⟩⟩

/-! ## 5. Axiom Audit (`< 115c` Single-Line `std3`) -/

#print axioms bm_valid
#print axioms bm_acyclic
#print axioms bm_modOk
#print axioms bm_semScc
#print axioms bm_probe_scc
#print axioms bm_size_ok
#print axioms bm_grow_ok
#print axioms bm_grow_fail
#print axioms bm_fill_ok
#print axioms bm_copy_fwd
#print axioms bm_copy_bwd
#print axioms bm_fill_oob
#print axioms bm_copy_wrap

end LeanQbeTest.T.WasmBulkMemTest
