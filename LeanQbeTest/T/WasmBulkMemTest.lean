module

import LeanQbe.T.Logic.ProofKit
public import LeanQbe.T.Wasm.Decode
public import LeanQbe.T.Wasm.Safety
public import LeanQbe.T.Main
public import LeanQbe.T.MainLinkScc
public import LeanQbe.T.MainCertProof
public import LeanQbeTest.T.WasmCertKit
meta import LeanQbe.T.Wasm.Decode
meta import LeanQbe.T.Main
meta import LeanQbe.T.MainLinkScc
meta import LeanQbe.T.Module
meta import LeanQbeTest.T.WasmCertKit

/-!
# WebAssembly Bulk-Memory & Growth Verification (`WasmBulkMemTest`)

Arch-neutral verification and test suite for WebAssembly linear-memory growth and bulk-memory
instructions (`memory.size`, `memory.grow`, `memory.fill`, `memory.copy`):

1. Binary decode & validation unit + negative tests (`0x3F 0x00`, `0x40 0x00`,
   `0xFC 0x0A 0x00 0x00`, `0xFC 0x0B 0x00`, non-zero memidx / missing memory rejections).
2. `clang --target=wasm32 -O2 -mbulk-memory` binary test (`probeWasm` -> `bulkMod`/`bulkQbe`):
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
@[expose] def bmTestGpr := WasmCertKit.wasmTestGpr

/-- Pure target-neutral Frame ISA configuration with 8 arg/return registers. -/
@[expose] def bmTestFrame := WasmCertKit.wasmTestFrame

/-- Target-neutral `Isa` for `#guard` compilation checks across x64 and AArch64 legal targets. -/
@[expose] def bmTestIsa := WasmCertKit.wasmTestIsa

/-- Check acyclic compilation of `qm` against `lt` on `bmTestIsa`. -/
def checkBmCompile := WasmCertKit.wasmCheckCompile

private def isBmInstr (op : UInt8) (bs : Array UInt8) (p : WInstr → Bool) : Bool :=
  match decodeOneInstr 10 op ⟨⟨bs⟩, 0⟩ with
  | .ok (i, r) => p i && r.remaining == 0
  | _ => false

-- 1.1 Valid bulk-memory & growth opcode decoding
#guard isBmInstr 0x3f #[0x00] (fun | .memory_size => true | _ => false) &&
  isBmInstr 0x40 #[0x00] (fun | .memory_grow => true | _ => false) &&
  isBmInstr 0xfc #[0x0a, 0x00, 0x00] (fun | .memory_copy => true | _ => false) &&
  isBmInstr 0xfc #[0x0b, 0x00] (fun | .memory_fill => true | _ => false)

-- 1.2 Rejection of non-zero memory indices, unsupported `0xFC` sub-opcodes, and truncation
#guard ([(0x3f, #[0x01]), (0x40, #[0x01]), (0xfc, #[0x0a, 0x01, 0x00]),
  (0xfc, #[0x0a, 0x00, 0x01]), (0xfc, #[0x0b, 0x01]), (0xfc, #[0x08, 0x00, 0x00]),
  (0xfc, #[0x09, 0x00]), (0xfc, #[0x0c, 0x00, 0x00]), (0xfc, #[]), (0xfc, #[0x0a, 0x00])] :
  List (UInt8 × Array UInt8)).all fun (op, bs) => !(decodeOneInstr 10 op ⟨⟨bs⟩, 0⟩).isOk

private def badBmMod (ft : WFuncTy) (bd : List WInstr) (mem : Option WMemSpec := none) : Bool :=
  !validateModule
    { types := [ft], funcs := [{ name := "f", typeIdx := 0, body := bd }], memory := mem }

#guard badBmMod { results := [.i32] } [.memory_size] &&
  badBmMod { params := [.i32], results := [.i32] } [.local_get 0, .memory_grow] &&
  badBmMod { params := [.i32, .i32, .i32] } [.local_get 0, .local_get 1, .local_get 2,
    .memory_fill] &&
  badBmMod { params := [.i32, .i32, .i32] } [.local_get 0, .local_get 1, .local_get 2,
    .memory_copy] &&
  badBmMod { params := [.i32, .i32, .i64] } [.local_get 0, .local_get 1, .local_get 2,
    .memory_fill] (some { initPages := 1 }) &&
  ([{ initPages := 65537 }, { initPages := 1, maxPages := some 65537 },
    { initPages := 2, maxPages := some 1 }] : List WMemSpec).all fun ms =>
    !validateModule { memory := some ms }

/-! ## 2. Real Compiled C Guest Binary (`clang --target=wasm32 -O2 -mbulk-memory`) -/

/-- Real WebAssembly binary compiled from C with
`clang --target=wasm32 -O2 -nostdlib -mbulk-memory -Wl,--no-entry -Wl,--export-all -Wl,--strip-all`
exposing `test_mem_size`, `test_mem_grow`, `test_mem_fill`, `test_mem_copy` (unused
`__stack_pointer` global mutability byte set from `0x01` to `0x00` for sandbox immutability). -/
def probeWasm : ByteArray := ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x10, 0x03, 0x60, 0x00, 0x01,
  0x7f, 0x60, 0x01, 0x7f, 0x01, 0x7f, 0x60, 0x03, 0x7f, 0x7f, 0x7f, 0x00, 0x03, 0x05,
  0x04, 0x00, 0x01, 0x02, 0x02, 0x05, 0x03, 0x01, 0x00, 0x02, 0x06, 0x08, 0x01, 0x7f,
  0x00, 0x41, 0x80, 0x88, 0x04, 0x0b, 0x07, 0x4a, 0x05, 0x06, 0x6d, 0x65, 0x6d, 0x6f,
  0x72, 0x79, 0x02, 0x00, 0x0d, 0x74, 0x65, 0x73, 0x74, 0x5f, 0x6d, 0x65, 0x6d, 0x5f,
  0x73, 0x69, 0x7a, 0x65, 0x00, 0x00, 0x0d, 0x74, 0x65, 0x73, 0x74, 0x5f, 0x6d, 0x65,
  0x6d, 0x5f, 0x67, 0x72, 0x6f, 0x77, 0x00, 0x01, 0x0d, 0x74, 0x65, 0x73, 0x74, 0x5f,
  0x6d, 0x65, 0x6d, 0x5f, 0x66, 0x69, 0x6c, 0x6c, 0x00, 0x02, 0x0d, 0x74, 0x65, 0x73,
  0x74, 0x5f, 0x6d, 0x65, 0x6d, 0x5f, 0x63, 0x6f, 0x70, 0x79, 0x00, 0x03, 0x0a, 0x36,
  0x04, 0x04, 0x00, 0x3f, 0x00, 0x0b, 0x06, 0x00, 0x20, 0x00, 0x40, 0x00, 0x0b, 0x13,
  0x00, 0x02, 0x40, 0x20, 0x02, 0x45, 0x0d, 0x00, 0x20, 0x00, 0x20, 0x01, 0x20, 0x02,
  0xfc, 0x0b, 0x00, 0x0b, 0x0b, 0x14, 0x00, 0x02, 0x40, 0x20, 0x02, 0x45, 0x0d, 0x00,
  0x20, 0x00, 0x20, 0x01, 0x20, 0x02, 0xfc, 0x0a, 0x00, 0x00, 0x0b, 0x0b
]⟩

@[expose] def fnSize : WFunc :=
  { name := "test_mem_size", typeIdx := 0, locals := [], body := [.memory_size] }
@[expose] def fnGrow : WFunc :=
  { name := "test_mem_grow", typeIdx := 1, locals := [], body := [.local_get 0, .memory_grow] }
@[expose] def fnFill : WFunc :=
  { name := "test_mem_fill", typeIdx := 2, locals := [], body :=
      [.block .empty [.local_get 2, .eqz .i32, .br_if 0,
        .local_get 0, .local_get 1, .local_get 2, .memory_fill]] }
@[expose] def fnCopy : WFunc :=
  { name := "test_mem_copy", typeIdx := 2, locals := [], body :=
      [.block .empty [.local_get 2, .eqz .i32, .br_if 0,
        .local_get 0, .local_get 1, .local_get 2, .memory_copy]] }

@[expose] def bulkMod : WModule :=
  { types := [{ params := [], results := [.i32] }, { params := [.i32], results := [.i32] },
      { params := [.i32, .i32, .i32], results := [] }]
    funcs := [fnSize, fnGrow, fnFill, fnCopy]
    memory := some { initPages := 2, maxPages := none }
    globals := [{ ty := .i32, mut_ := false, init := 66560#64 }] }

@[expose] def bulkQbe : Module := lowerModule bulkMod

#guard match decodeAndLowerWasm probeWasm with
  | .ok (m, qm) =>
    m.types == bulkMod.types && m.memory == bulkMod.memory && m.globals == bulkMod.globals &&
    m.funcs.map (·.name) == bulkMod.funcs.map (·.name) &&
    (match m.funcs with
      | [f0, f1, f2, f3] => match f0.body, f1.body, f2.body, f3.body with
        | [.memory_size], [.local_get 0, .memory_grow],
          [.block .empty [.local_get 2, .eqz .i32, .br_if 0,
            .local_get 0, .local_get 1, .local_get 2, .memory_fill]],
          [.block .empty [.local_get 2, .eqz .i32, .br_if 0,
            .local_get 0, .local_get 1, .local_get 2, .memory_copy]] => true
        | _, _, _, _ => false
      | _ => false) &&
    checkBmCompile LegalTarget.x64 qm && checkBmCompile LegalTarget.aarch64 qm
  | .error _ => false

theorem bm_probe_scc {m : WModule} {qm : Module}
    (h : decodeAndLowerWasm probeWasm = .ok (m, qm)) (Γext : Env) :
    ∀ i : Nat, ((WasmSandboxEnv m i).restrict (qm.fns.map Fn.sig)).le (Env.semScc qm Γext) :=
  decodeAndLowerWasm_semScc h Γext

theorem bm_valid : validateModule bulkMod = true := by decide
theorem bm_acyclic : bulkQbe.checkAcyclic = true := lowerModule_checkAcyclic bm_valid (by decide)
theorem bm_wf : ∀ fn ∈ bulkQbe.fns, fn.Wf := lowerModule_wf bulkMod
theorem bm_modOk : ModuleOk (WasmSandboxEnvAny bulkMod) bulkQbe :=
  lowerModule_moduleOk bm_valid bm_acyclic

theorem bm_wp : ∀ f ∈ bulkQbe.fns, ∀ (xs : Tup Val f.as) (m : Mem 64)
    (Q : Post f.rs) (X : XPost), WasmSandboxEnvAny bulkMod f.name f.as f.rs xs m Q X →
    Func.wp (WasmSandboxEnvAny bulkMod) f.body xs m Q X := by
  intro f hf; rcases List.mem_iff_append.mp hf with ⟨pre, post, hsp⟩
  exact (bm_modOk.fnsOk pre f post hsp).2.2

theorem bm_semScc (Γext : Env) : ∀ i : Nat,
    ((WasmSandboxEnv bulkMod i).restrict (bulkQbe.fns.map Fn.sig)).le (Env.semScc bulkQbe Γext) :=
  lowerModule_semScc bm_valid Γext

theorem bm_any_monoX (f : Sym) (as bs : List Ty) (xs : Tup Val as) (mem : Mem 64) (Q : Post bs)
    (X X' : XPost) (h : WasmSandboxEnvAny bulkMod f as bs xs mem Q X) :
    WasmSandboxEnvAny bulkMod f as bs xs mem Q X' := h

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
      8 * ws.length ≤ 2 ^ 64 → (array64 base ws ⋆ R) m → (region base (8 * ws.length) ⋆ R) m
  | [], _, _, _, hm => by simpa [array64_nil_eq, region_zero] using hm
  | w :: ws, R, m, hlen, hm => by
    rw [array64_cons, sep_assoc] at hm
    have hm1 := sep_mono (fun m1 h1 => by
      rw [cell64_eq_word8] at h1
      simpa [Int.toBytes_length] using
        bytes_to_region (a := base) (bs := Int.toBytes 8 w.toNat) h1) hm
    have hm2 : (array64 (base + 8#64) ws ⋆ (region base 8 ⋆ R)) m :=
      sep_cast hm1 (by simp only [show (8 : BitVec 64) = 8#64 from rfl]; ac_rfl)
    have hm3 := array64_sep_to_region (base + 8#64) ws (by simp at hlen; omega) hm2
    have hm4 : ((region base 8 ⋆ region (base + 8#64) (8 * ws.length)) ⋆ R) m :=
      sep_cast hm3 (by ac_rfl)
    rw [← region_split (by simp at hlen; omega)] at hm4
    rwa [show 8 + 8 * ws.length = 8 * (w :: ws).length by simp; omega] at hm4

private theorem replicate_snoc (n : Nat) (a : BitVec 64) :
    List.replicate (n + 1) a = List.replicate n a ++ [a] := by
  induction n with | zero => rfl | succ _ ih =>
    exact List.replicate_succ.trans ((congrArg (a :: ·) ih).trans List.cons_append.symm)

private theorem replicate_drop_set {done : Nat} (hd : done < 8192)
    {ws : List (BitVec 64)} (hl : ws.length = 8192) :
    (List.replicate done 0#64 ++ ws.drop done).set done 0#64 =
      List.replicate (done + 1) 0#64 ++ ws.drop (done + 1) := by
  rw [List.drop_eq_getElem_cons (by omega : done < ws.length), List.set_append]
  simp only [List.length_replicate, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self, List.set_cons_zero,
    replicate_snoc, List.append_assoc, List.singleton_append]

private theorem bv64_8_mul_eq_zero {d : Nat} (hle : d ≤ 8192)
    (h : BitVec.ofNat 64 (8 * (8192 - d)) = 0#64) : d = 8192 := by c0_bv_omega
private theorem bv64_8_mul_ne_zero {d : Nat} (hle : d ≤ 8192)
    (h : BitVec.ofNat 64 (8 * (8192 - d)) ≠ 0#64) : d < 8192 := by c0_bv_omega
private theorem bv64_8_mul_sub {d : Nat} (_hd : d < 8192) :
    BitVec.ofNat 64 (8 * (8192 - d)) - 8#64 = BitVec.ofNat 64 (8 * (8192 - (d + 1))) := by
  c0_bv_omega

theorem emitMemZeroPage_zero {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {base : BitVec 64} {ws : List (BitVec 64)} {R' : Mem 64 → Prop} {mem : Mem 64}
    (hlen : ws.length = 8192) (pagePtr : Arg Val i64) (hptr : pagePtr.val = base)
    (hm : (array64 base ws ⋆ R') mem) (kDone : Expr Val Cont rs)
    (hk : ∀ m', (array64 base (List.replicate 8192 0#64) ⋆ R') m' → wp Γ Q X kDone m') :
    wp Γ Q X (emitMemZeroPage pagePtr kDone) mem := by
  simp only [emitMemZeroPage]
  refine wp_join_group (fun _ m' => (array64 base (List.replicate 8192 0#64) ⋆ R') m')
    (fun _ _ m' hm' => hk m' hm') (fun jDone hjDone => ?_)
  let Inv : Nat → Tup Val [i64, i64] → Mem 64 → Prop := fun n zxs m' =>
    ∃ done, done ≤ 8192 ∧ n = 8192 - done ∧ zxs.1 = BitVec.ofNat 64 (8 * (8192 - done)) ∧
      zxs.2.1 = base + BitVec.ofNat 64 (8 * done) ∧
      (array64 base (List.replicate done 0#64 ++ ws.drop done) ⋆ R') m'
  refine wp_loop_group Inv (fun lZero n (zRem, zPtr, ()) m' hlZero
      ⟨done, hle, hn, hzRem, hzPtr, hm'⟩ => by
    subst hn; dsimp only [Blocks.get_here] at hzRem hzPtr ⊢; wasm_wp_let; rw [wp_jnz_]
    refine ⟨fun hz => ?_, fun hnz => ?_⟩
    · have hdone := bv64_8_mul_eq_zero hle
        (hzRem ▸ of_decide_eq_true (by simp only [arg_var_val] at hz; exact hz))
      subst hdone; rw [List.drop_of_length_le (by omega), List.append_nil] at hm'
      rw [wp_jump_]; exact hjDone () m' hm'
    · have hdn := bv64_8_mul_ne_zero hle fun h0 => by revert hnz; simp [hzRem, h0]
      rw [wp_store_]
      obtain ⟨hsok, hm''⟩ := store_array64 (i := done) 0#64 (by simp [hlen]; omega) hm'
      refine ⟨by simpa [Arg.val, hzPtr] using hsok, ?_⟩
      rw [replicate_drop_set hdn hlen] at hm''; wasm_wp_lets; rw [wp_jump_]
      exact hlZero _ (zRem - 8#64, zPtr + 8#64, ()) _ (by omega)
        ⟨done + 1, by omega, rfl, hzRem ▸ bv64_8_mul_sub hdn,
          by rw [hzPtr, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, bv64_ptr_add,
               show 8 * done + 8 = 8 * (done + 1) by omega],
          by simpa [Arg.val, hzPtr] using hm''⟩)
    fun lZero hlZero => by
      rw [wp_jump_]; exact hlZero 8192 (65536#64, pagePtr.val, ()) mem
        ⟨0, by omega, rfl, rfl, by simp [hptr], by simpa using hm⟩

/-- Reference specification for filling `d` bytes from `dst` with `b`. -/
def listFillAux (b : BitVec 8) (dst : Nat) : Nat → List (BitVec 8) → List (BitVec 8)
  | 0, bs => bs
  | d + 1, bs => (listFillAux b dst d bs).set (dst + d) b

theorem listFillAux_length (b : BitVec 8) (dst : Nat) :
    ∀ d bs, (listFillAux b dst d bs).length = bs.length
  | 0, _ => rfl
  | d + 1, bs => by simp [listFillAux, listFillAux_length b dst d bs]

/-- Unified `memmove` specification parameterized by direction (`fwd = true` copies `0..d`,
`fwd = false` copies `n-1..n-d`). -/
def listCopyMemmove (fwd : Bool) (dst src n : Nat) : Nat → List (BitVec 8) → List (BitVec 8)
  | 0, bs => bs
  | d + 1, bs =>
    let cur := listCopyMemmove fwd dst src n d bs
    let k := if fwd then d else n - 1 - d
    cur.set (dst + k) (cur[src + k]?.getD 0#8)

private theorem listCopyMemmove_succ (fwd : Bool) (dst src n d : Nat) (bs : List (BitVec 8)) :
    listCopyMemmove fwd dst src n (d + 1) bs =
      let k := if fwd then d else n - 1 - d
      (listCopyMemmove fwd dst src n d bs).set (dst + k)
        ((listCopyMemmove fwd dst src n d bs)[src + k]?.getD 0#8) := rfl

private theorem listCopyMemmove_true_n (dst src n : Nat) :
    ∀ d bs, listCopyMemmove true dst src n d bs = listCopyMemmove true dst src 0 d bs
  | 0, _ => rfl
  | d + 1, bs => by simp [listCopyMemmove, listCopyMemmove_true_n dst src n d bs]

theorem listCopyMemmove_length (fwd : Bool) (dst src n : Nat) :
    ∀ d bs, (listCopyMemmove fwd dst src n d bs).length = bs.length
  | 0, _ => rfl
  | d + 1, bs => by simp [listCopyMemmove_succ, listCopyMemmove_length fwd dst src n d bs]

theorem listCopyMemmove_memmove (fwd : Bool) (dst src n : Nat)
    (hdir : if fwd then dst ≤ src else src < dst) :
    ∀ d (bs : List (BitVec 8)), (fwd = false → d ≤ n) →
      (if fwd then dst + d else dst + n) ≤ bs.length →
      (if fwd then src + d else src + n) ≤ bs.length → ∀ i, i < bs.length →
        (listCopyMemmove fwd dst src n d bs)[i]?.getD 0#8 =
          if (if fwd then dst else dst + (n - d)) ≤ i ∧
              i < (if fwd then dst + d else dst + n) then
            bs[src + (i - dst)]?.getD 0#8
          else bs[i]?.getD 0#8
  | 0, bs, _, _, _, i, _ => by
    simp only [listCopyMemmove, Nat.sub_zero]
    cases fwd <;> simp only [↓reduceIte, Bool.false_eq_true] <;> split <;> first | omega | rfl
  | d + 1, bs, hdn, hd, hs, i, hi => by
    have ih := listCopyMemmove_memmove fwd dst src n hdir d bs (fun hf => by have := hdn hf; omega)
      (by cases fwd <;> simp only [↓reduceIte, Bool.false_eq_true] at hd ⊢ <;> omega)
      (by cases fwd <;> simp only [↓reduceIte, Bool.false_eq_true] at hs ⊢ <;> omega)
    have hcurLen := listCopyMemmove_length fwd dst src n d bs
    cases fwd <;>
      simp only [listCopyMemmove_succ, ↓reduceIte, Bool.false_eq_true] at hdir hd hs ih ⊢
    · have hdn' := hdn rfl
      have hsrcOrig : (listCopyMemmove false dst src n d bs)[src + (n - 1 - d)]?.getD 0#8 =
          bs[src + (n - 1 - d)]?.getD 0#8 := by
        have h := ih (src + (n - 1 - d)) (by omega)
        rwa [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at h
      by_cases heq : i = dst + (n - 1 - d)
      · subst heq; rw [List.getElem?_set_self (by rw [hcurLen]; omega), Option.getD_some,
          hsrcOrig, ite_eq_left_of_eq_true _ _ (eq_true (by omega)), Nat.add_sub_cancel_left]
      · rw [List.getElem?_set_ne (Ne.symm heq), ih i hi]
        simp [show (dst + (n - d) ≤ i ∧ i < dst + n) ↔
          (dst + (n - (d + 1)) ≤ i ∧ i < dst + n) by omega]
    · have hsrcOrig : (listCopyMemmove true dst src n d bs)[src + d]?.getD 0#8 =
          bs[src + d]?.getD 0#8 := by
        have h := ih (src + d) (by omega)
        rwa [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at h
      by_cases heq : i = dst + d
      · subst heq; rw [List.getElem?_set_self (by rw [hcurLen]; omega), Option.getD_some,
          hsrcOrig, ite_eq_left_of_eq_true _ _ (eq_true (by omega)), Nat.add_sub_cancel_left]
      · rw [List.getElem?_set_ne (Ne.symm heq), ih i hi]
        simp [show (dst ≤ i ∧ i < dst + d) ↔ (dst ≤ i ∧ i < dst + (d + 1)) by omega]

/-- Reference specification for forward copy (`dst ≤ src`) of `d` bytes. -/
def listCopyFwdAux (dst src : Nat) : Nat → List (BitVec 8) → List (BitVec 8) :=
  listCopyMemmove true dst src 0

theorem listCopyFwdAux_length (dst src : Nat) :
    ∀ d bs, (listCopyFwdAux dst src d bs).length = bs.length :=
  listCopyMemmove_length true dst src 0

theorem listCopyFwdAux_memmove (dst src : Nat) (hle : dst ≤ src) :
    ∀ d (bs : List (BitVec 8)), dst + d ≤ bs.length → src + d ≤ bs.length →
      ∀ i, i < bs.length →
        (listCopyFwdAux dst src d bs)[i]?.getD 0#8 =
          if dst ≤ i ∧ i < dst + d then bs[src + (i - dst)]?.getD 0#8
          else bs[i]?.getD 0#8 :=
  fun d bs => listCopyMemmove_memmove true dst src 0 hle d bs (fun h => by cases h)

/-- Reference specification for backward copy (`src < dst`) of `d` steps out of `n`. -/
def listCopyBwdAux (dst src n : Nat) : Nat → List (BitVec 8) → List (BitVec 8) :=
  listCopyMemmove false dst src n

theorem listCopyBwdAux_length (dst src n : Nat) :
    ∀ d bs, (listCopyBwdAux dst src n d bs).length = bs.length :=
  listCopyMemmove_length false dst src n

theorem listCopyBwdAux_memmove (dst src n : Nat) (hlt : src < dst) :
    ∀ d (bs : List (BitVec 8)), d ≤ n → dst + n ≤ bs.length → src + n ≤ bs.length →
      ∀ i, i < bs.length →
        (listCopyBwdAux dst src n d bs)[i]?.getD 0#8 =
          if dst + (n - d) ≤ i ∧ i < dst + n then bs[src + (i - dst)]?.getD 0#8
          else bs[i]?.getD 0#8 :=
  fun d bs hdn => listCopyMemmove_memmove false dst src n hlt d bs (fun _ => hdn)

private theorem bv64_sub_one_nat {a b : Nat} (hlt : b < a) (_ha : a < 2 ^ 64) :
    BitVec.ofNat 64 (a - b) - 1#64 = BitVec.ofNat 64 (a - (b + 1)) := by c0_bv_omega

private theorem bv64_sub_done_eq_zero {n done : Nat} (hle : done ≤ n) (_hn : n < 2 ^ 64)
    (h : BitVec.ofNat 64 (n - done) = 0#64) : done = n := by c0_bv_omega

private theorem bv64_sub_done_ne_zero {n done : Nat} (hle : done ≤ n) (_hn : n < 2 ^ 64)
    (h : BitVec.ofNat 64 (n - done) ≠ 0#64) : done < n := by c0_bv_omega

private theorem bv64_sub_toNat_le {f n done : Nat} (hle : n ≤ f) (_hf : f < 2 ^ 64)
    (hd : done ≤ n) :
    (BitVec.ofNat 64 (n - done)).toNat ≤ (BitVec.ofNat 64 (f - done)).toNat := by c0_bv_omega

private theorem bv64_ptr_succ {base : BitVec 64} {a : Nat} :
    (base + BitVec.ofNat 64 a) + 1#64 = base + BitVec.ofNat 64 (a + 1) := by c0_bv_omega

theorem emitMemFillLoop_bytes {Γ : Env} {X : XPost} {retTys : List WValTy}
    {Q : Post (wasmRetSig retTys)} {memBase f n64 dstPtr0 : BitVec 64} {dstOff : Nat}
    {byteVal : BitVec 8} {bs : List (BitVec 8)} {R' : Mem 64 → Prop} {mem : Mem 64}
    (jAfter : Cont [i64]) (hfn : n64.toNat ≤ f.toNat) (hbnd : dstOff + n64.toNat ≤ bs.length)
    (hdst : dstPtr0 = memBase + BitVec.ofNat 64 dstOff) (hm : (array (t := i8) memBase bs ⋆ R') mem)
    (hj : ∀ m', (array (t := i8) memBase (listFillAux byteVal dstOff n64.toNat bs) ⋆ R') m' →
      jAfter (BitVec.ofNat 64 (f.toNat - n64.toNat), ()) m') :
    wp Γ Q X (emitMemFillLoop retTys jAfter (.var byteVal) (.var f) (.var n64) (.var dstPtr0))
      mem := by
  simp only [emitMemFillLoop]
  let Inv : BitVec 64 → BitVec 64 → Tup Val [i64] → Mem 64 → Prop := fun fHdr rem st m' =>
    ∃ done, done ≤ n64.toNat ∧ fHdr = BitVec.ofNat 64 (f.toNat - done) ∧
      rem = BitVec.ofNat 64 (n64.toNat - done) ∧ st.1 = memBase + BitVec.ofNat 64 (dstOff + done) ∧
      (array (t := i8) memBase (listFillAux byteVal dstOff done bs) ⋆ R') m'
  refine wp_exact_fuel_loop Inv
    (fun _ _ _ _ ⟨_, hle, hf, hr, _⟩ => hf ▸ hr ▸ bv64_sub_toNat_le hfn f.isLt hle)
    (.var f, .var n64, .var dstPtr0, ()) mem (fun fHdr _ => .jump jAfter (.var fHdr, ()))
    (fun lLoop fNext rem st => .store (t := i8) (.var byteVal) (.var st.1)
      (.let_ (.mk (.sub i64) (.var rem, .imm 1#64, ())) fun remN =>
       .let_ (.mk (.add i64) (.var st.1, .imm 1#64, ())) fun ptrN =>
         .jump lLoop (.var fNext, .var remN.1, .var ptrN.1, ())))
    ⟨0, Nat.zero_le _, by simp [BitVec.ofNat_toNat], by simp [BitVec.ofNat_toNat],
      by simpa using hdst, hm⟩
    (fun fHdr _ m' ⟨done, hle, hfHdr, hrem, _, hm'⟩ => by
      have hd := bv64_sub_done_eq_zero hle n64.isLt hrem.symm; subst hd
      rw [wp_jump_, hfHdr]; exact hj m' hm')
    fun lLoop fHdr rem st m' hneR _ _ hRec ⟨done, hle, hfHdr, hrem, hptr, hm'⟩ => by
      have hdn := bv64_sub_done_ne_zero hle n64.isLt fun h => hneR (hrem ▸ h)
      have hidxLt : dstOff + done < (listFillAux byteVal dstOff done bs).length := by
        rw [listFillAux_length]; omega
      rw [wp_store_]; obtain ⟨hsok, hm''⟩ := store_array (t := i8) byteVal (by decide) hidxLt hm'
      rw [show (i8 : Ty).bytes = 1 from rfl, Nat.one_mul, ← hptr] at hsok hm''
      refine ⟨by simpa [arg_var_val] using hsok, ?_⟩; wasm_wp_lets; rw [wp_jump_]
      exact hRec _ (rem - 1#64) (st.1 + 1#64, ()) _ (bv64_sub_one_lt hneR)
        ⟨done + 1, by omega, hfHdr ▸ bv64_sub_one_nat (by omega) f.isLt,
          hrem ▸ bv64_sub_one_nat hdn n64.isLt, by rw [hptr, bv64_ptr_succ, Nat.add_assoc], hm''⟩

private theorem wp_copy_byte_step {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {memBase dAddr sAddr : BitVec 64} {fwd : Bool} {dstOff srcOff n done : Nat}
    {bs : List (BitVec 8)} {R' : Mem 64 → Prop} {m : Mem 64} {cont : Val i8 → Expr Val Cont rs}
    (hsBnd : srcOff + (if fwd then done else n - 1 - done) < bs.length)
    (hdBnd : dstOff + (if fwd then done else n - 1 - done) < bs.length)
    (hsAddr : sAddr = memBase + BitVec.ofNat 64 (srcOff + (if fwd then done else n - 1 - done)))
    (hdAddr : dAddr = memBase + BitVec.ofNat 64 (dstOff + (if fwd then done else n - 1 - done)))
    (hm : (array (t := i8) memBase (listCopyMemmove fwd dstOff srcOff n done bs) ⋆ R') m)
    (hk : ∀ b : Val i8, ∀ m',
      (array (t := i8) memBase (listCopyMemmove fwd dstOff srcOff n (done + 1) bs) ⋆ R') m' →
      wp Γ Q X (cont b) m') :
    wp Γ Q X
      (.load i8 (.var sAddr) fun b => .store (t := i8) (.var b) (.var dAddr) (cont b)) m := by
  let cur := listCopyMemmove fwd dstOff srcOff n done bs
  let k := if fwd then done else n - 1 - done
  have hsLt : srcOff + k < cur.length := by rw [listCopyMemmove_length]; exact hsBnd
  have hdLt : dstOff + k < cur.length := by rw [listCopyMemmove_length]; exact hdBnd
  have hi8 : (i8 : Ty).bytes = 1 := rfl; rw [wp_load_]
  have hload := loadVal_array (t := i8) (by decide) hsLt hm
  rw [hi8, Nat.one_mul, ← hsAddr] at hload
  refine ⟨cur[srcOff + k], by simpa [arg_var_val] using hload, ?_⟩
  rw [wp_store_]; obtain ⟨hsok, hm'⟩ := store_array (t := i8) cur[srcOff + k] (by decide) hdLt hm
  rw [hi8, Nat.one_mul, ← hdAddr] at hsok hm'; refine ⟨by simpa [arg_var_val] using hsok, hk _ _ ?_⟩
  simpa [cur, k, listCopyMemmove_succ, List.getElem?_eq_getElem hsLt] using hm'

private theorem emitMemCopyLoop_bytes {Γ : Env} {X : XPost} {retTys : List WValTy}
    {Q : Post (wasmRetSig retTys)} {fwd : Bool}
    {memBase f n64 dstPtr0 srcPtr0 : BitVec 64} {dstOff srcOff : Nat} {bs : List (BitVec 8)}
    {R' : Mem 64 → Prop} {mem : Mem 64} (jAfter : Cont [i64]) (hfn : n64.toNat ≤ f.toNat)
    (hdBnd : dstOff + n64.toNat ≤ bs.length) (hsBnd : srcOff + n64.toNat ≤ bs.length)
    (hdst : dstPtr0 = memBase + BitVec.ofNat 64 (dstOff + if fwd then 0 else n64.toNat))
    (hsrc : srcPtr0 = memBase + BitVec.ofNat 64 (srcOff + if fwd then 0 else n64.toNat))
    (hm : (array (t := i8) memBase bs ⋆ R') mem) (hj : ∀ m',
      (array (t := i8) memBase (listCopyMemmove fwd dstOff srcOff n64.toNat n64.toNat bs) ⋆ R') m' →
      jAfter (BitVec.ofNat 64 (f.toNat - n64.toNat), ()) m') :
    wp Γ Q X (emitMemCopyLoop fwd retTys jAfter (.var f) (.var n64) (.var dstPtr0) (.var srcPtr0))
      mem := by
  simp only [emitMemCopyLoop]
  let Inv : BitVec 64 → BitVec 64 → Tup Val [i64, i64] → Mem 64 → Prop := fun fHdr rem st m' =>
    ∃ done, done ≤ n64.toNat ∧ fHdr = BitVec.ofNat 64 (f.toNat - done) ∧
      rem = BitVec.ofNat 64 (n64.toNat - done) ∧ let off := if fwd then done else n64.toNat - done
      st.1 = memBase + BitVec.ofNat 64 (dstOff + off) ∧
      st.2.1 = memBase + BitVec.ofNat 64 (srcOff + off) ∧
      (array (t := i8) memBase (listCopyMemmove fwd dstOff srcOff n64.toNat done bs) ⋆ R') m'
  refine wp_exact_fuel_loop Inv
    (fun _ _ _ _ ⟨_, hle, hf, hr, _⟩ => hf ▸ hr ▸ bv64_sub_toNat_le hfn f.isLt hle)
    (.var f, .var n64, .var dstPtr0, .var srcPtr0, ()) mem
    (fun fHdr _ => .jump jAfter (.var fHdr, ()))
    (fun lLoop fNext rem st =>
      .let_ (.mk (.sub i64) (.var rem, .imm 1#64, ())) fun remN =>
      if fwd then
        .load i8 (.var st.2.1) fun b => .store (t := i8) (.var b) (.var st.1)
          (.let_ (.mk (.add i64) (.var st.1, .imm 1#64, ())) fun dPtrN =>
           .let_ (.mk (.add i64) (.var st.2.1, .imm 1#64, ())) fun sPtrN =>
             .jump lLoop (.var fNext, .var remN.1, .var dPtrN.1, .var sPtrN.1, ()))
      else
        .let_ (.mk (.sub i64) (.var st.1, .imm 1#64, ())) fun dPtrP =>
        .let_ (.mk (.sub i64) (.var st.2.1, .imm 1#64, ())) fun sPtrP =>
        .load i8 (.var sPtrP.1) fun b => .store (t := i8) (.var b) (.var dPtrP.1)
          (.jump lLoop (.var fNext, .var remN.1, .var dPtrP.1, .var sPtrP.1, ())))
    ⟨0, Nat.zero_le _, by simp [BitVec.ofNat_toNat], by simp [BitVec.ofNat_toNat],
      by simpa [Nat.sub_zero] using hdst, by simpa [Nat.sub_zero] using hsrc, hm⟩
    (fun fHdr _ m' ⟨done, hle, hfHdr, hrem, _, _, hm'⟩ => by
      have hd := bv64_sub_done_eq_zero hle n64.isLt hrem.symm; subst hd
      rw [wp_jump_, hfHdr]; exact hj m' hm')
    fun lLoop fHdr rem st m' hneR _ _ hRec ⟨done, hle, hfHdr, hrem, hdPtr, hsPtr, hm'⟩ => by
      have hdn := bv64_sub_done_ne_zero hle n64.isLt fun h => hneR (hrem ▸ h)
      have hfNext := hfHdr ▸ bv64_sub_one_nat (by omega) f.isLt
      have hremNext := hrem ▸ bv64_sub_one_nat hdn n64.isLt
      have hRemLt := bv64_sub_one_lt hneR; wasm_wp_let
      cases fwd <;> simp only [↓reduceIte, Bool.false_eq_true] at hdPtr hsPtr hm' ⊢
      · wasm_wp_lets
        have hsSub : st.2.1 - 1#64 =
            memBase + BitVec.ofNat 64 (srcOff + (n64.toNat - 1 - done)) := by
          rw [hsPtr, bv64_ptr_sub_one (by omega),
            show srcOff + (n64.toNat - done) - 1 = srcOff + (n64.toNat - 1 - done) by omega]
        have hdSub : st.1 - 1#64 =
            memBase + BitVec.ofNat 64 (dstOff + (n64.toNat - 1 - done)) := by
          rw [hdPtr, bv64_ptr_sub_one (by omega),
            show dstOff + (n64.toNat - done) - 1 = dstOff + (n64.toNat - 1 - done) by omega]
        refine wp_copy_byte_step (fwd := false) (by simpa using (by omega : _))
          (by simpa using (by omega : _)) hsSub hdSub hm' fun _ m'' hm'' => ?_; rw [wp_jump_]
        exact hRec _ (rem - 1#64) (st.1 - 1#64, st.2.1 - 1#64, ()) m'' hRemLt
          ⟨done + 1, by omega, hfNext, hremNext, by rw [hdSub]; simp; congr 2; omega,
            by rw [hsSub]; simp; congr 2; omega, hm''⟩
      · refine wp_copy_byte_step (fwd := true) (by simpa using (by omega : _))
          (by simpa using (by omega : _)) hsPtr hdPtr hm' fun _ m'' hm'' => ?_
        wasm_wp_lets; rw [wp_jump_]
        exact hRec _ (rem - 1#64) (st.1 + 1#64, st.2.1 + 1#64, ()) m'' hRemLt
          ⟨done + 1, by omega, hfNext, hremNext,
            by rw [hdPtr, bv64_ptr_succ]; simp [Nat.add_assoc],
            by rw [hsPtr, bv64_ptr_succ]; simp [Nat.add_assoc], hm''⟩

theorem emitMemCopyLoop_fwd_bytes {Γ : Env} {X : XPost} {retTys : List WValTy}
    {Q : Post (wasmRetSig retTys)} {memBase f n64 dstPtr0 srcPtr0 : BitVec 64}
    {dstOff srcOff : Nat} {bs : List (BitVec 8)} {R' : Mem 64 → Prop} {mem : Mem 64}
    (jAfter : Cont [i64]) (hfn : n64.toNat ≤ f.toNat) (hdBnd : dstOff + n64.toNat ≤ bs.length)
    (hsBnd : srcOff + n64.toNat ≤ bs.length) (hdst : dstPtr0 = memBase + BitVec.ofNat 64 dstOff)
    (hsrc : srcPtr0 = memBase + BitVec.ofNat 64 srcOff) (hm : (array (t := i8) memBase bs ⋆ R') mem)
    (hj : ∀ m', (array (t := i8) memBase (listCopyFwdAux dstOff srcOff n64.toNat bs) ⋆ R') m' →
      jAfter (BitVec.ofNat 64 (f.toNat - n64.toNat), ()) m') :
    wp Γ Q X (emitMemCopyLoop true retTys jAfter (.var f) (.var n64) (.var dstPtr0) (.var srcPtr0))
      mem :=
  emitMemCopyLoop_bytes (fwd := true) jAfter hfn hdBnd hsBnd
    (by simpa using hdst) (by simpa using hsrc) hm fun m' hm' => by
      rw [listCopyMemmove_true_n] at hm'; exact hj m' hm'

theorem emitMemCopyLoop_bwd_bytes {Γ : Env} {X : XPost} {retTys : List WValTy}
    {Q : Post (wasmRetSig retTys)} {memBase f n64 dstPtr0 srcPtr0 : BitVec 64}
    {dstOff srcOff : Nat} {bs : List (BitVec 8)} {R' : Mem 64 → Prop} {mem : Mem 64}
    (jAfter : Cont [i64]) (hfn : n64.toNat ≤ f.toNat) (hdBnd : dstOff + n64.toNat ≤ bs.length)
    (hsBnd : srcOff + n64.toNat ≤ bs.length)
    (hdst : dstPtr0 = memBase + BitVec.ofNat 64 (dstOff + n64.toNat))
    (hsrc : srcPtr0 = memBase + BitVec.ofNat 64 (srcOff + n64.toNat))
    (hm : (array (t := i8) memBase bs ⋆ R') mem) (hj : ∀ m', (array (t := i8) memBase
      (listCopyBwdAux dstOff srcOff n64.toNat n64.toNat bs) ⋆ R') m' →
      jAfter (BitVec.ofNat 64 (f.toNat - n64.toNat), ()) m') :
    wp Γ Q X (emitMemCopyLoop false retTys jAfter (.var f) (.var n64) (.var dstPtr0) (.var srcPtr0))
      mem :=
  emitMemCopyLoop_bytes (fwd := false) jAfter hfn hdBnd hsBnd hdst hsrc hm hj

/-! ## 4. Concrete Behavioral & Adversarial `Func.wp` Proofs -/

private theorem get?Int_zero {α : Type} (a : α) (xs : List α) :
    List.get?Internal (a :: xs) 0 = some a := rfl

private theorem get?Int_succ {α : Type} (a : α) (xs : List α) (n : Nat) :
    List.get?Internal (a :: xs) (n + 1) = List.get?Internal xs n := rfl

private theorem appendZeroLocals_nil {V : Ty → Type} (xs : Tup (Arg V) []) :
    appendZeroLocals [] [] xs = () := rfl

private theorem wp_load_ctx {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vmCtx memBase memLen memCap addr v : BitVec 64} {R' : Mem 64 → Prop} {mem : Mem 64}
    {k : Val i64 → Expr Val Cont rs}
    (hm : (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ R') mem)
    (hc : (addr = vmCtx ∧ v = memBase) ∨ (addr = vmCtx + 8#64 ∧ v = memLen) ∨
      (addr = vmCtx + 16#64 ∧ v = memCap))
    (hk : wp Γ Q X (k v) mem) :
    wp Γ Q X (.load i64 (.var addr) k) mem := by
  rw [wp_load_, arg_var_val]
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, loadVal_cell64 (R := cell64 (addr + 8#64) memLen ⋆ cell64 (addr + 16#64) memCap ⋆ R')
      (sep_cast hm (by ac_rfl)), hk⟩
  · exact ⟨_, loadVal_cell64 (R := cell64 vmCtx memBase ⋆ cell64 (vmCtx + 16#64) memCap ⋆ R')
      (sep_cast hm (by ac_rfl)), hk⟩
  · exact ⟨_, loadVal_cell64 (R := cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆ R')
      (sep_cast hm (by ac_rfl)), hk⟩

private theorem sep_ctx_arr {vmCtx b l c : BitVec 64} {bs : List (BitVec 8)}
    {R : Mem 64 → Prop} {m : Mem 64} :
    ((cell64 vmCtx b ⋆ cell64 (vmCtx + 8#64) l ⋆ cell64 (vmCtx + 16#64) c ⋆
      array (t := i8) b bs ⋆ R) m) ↔
    ((array (t := i8) b bs ⋆ (cell64 vmCtx b ⋆ cell64 (vmCtx + 8#64) l ⋆
      cell64 (vmCtx + 16#64) c ⋆ R)) m) :=
  ⟨fun h => sep_cast h (by ac_rfl), fun h => sep_cast h (by ac_rfl)⟩

/-- Concrete `Func.wp` behavioral proof for `memory.size`: returns current pages
`(curLen >>> 16).setWidth 32` without touching memory (`mem' = mem`) or host frame `R`. -/
theorem bm_size_ok (Γ : Env) (vmCtx memBase curLen memCap fuel : BitVec 64)
    (R : Mem 64 → Prop) (mem : Mem 64) (X : XPost)
    (hm : WasmMemInv true vmCtx memBase curLen memCap R mem) :
    Func.wp Γ (lowerFn bulkMod fnSize).body (vmCtx, fuel, ()) mem
      (fun ys m' => ys = (0#32, fuel, (curLen >>> 16).setWidth 32, ()) ∧ m' = mem ∧
        WasmMemInv true vmCtx memBase curLen memCap R m') X := by
  simp only [Func.wp, lowerFn, lowerFuncBody, bulkMod, fnSize, GetElem?.getElem?, get?Int_zero,
    Option.getD, Option.map, Option.isSome, List.map, List.append, List.nil_append,
    WMemSpec.maxBytes, WMemSpec.effectiveMaxPages, WValTy.toTy, labelSig]
  refine wp_join_group (fun xs m' => xs = (fuel, (curLen >>> 16).setWidth 32, ()) ∧ m' = mem ∧
      WasmMemInv true vmCtx memBase curLen memCap R m')
    (fun _ ⟨_, _, ⟨⟩⟩ _ ⟨hxs, rfl, hRm⟩ => by
      cases hxs; dsimp only [Blocks.get_here, tupSplit, varsTup]; rw [wp_ret_]
      exact ⟨by simp [vals], rfl, hRm⟩)
    fun _ _ => by
      simp only [lowerSeq, lowerSimpleInstr, appendZeroLocals_nil,
        popArgsAux, popExpectS, Bind.bind, Option.bind, ↓reduceIte]
      refine emitMemSize_wp (.var vmCtx) rfl hm _ ?_; rw [wp_ret_]; exact ⟨by simp [vals], rfl, hm⟩

private theorem fnGrow_wp_step {Γ : Env} {X : XPost}
    {vmCtx memBase curLen memCap fuel : BitVec 64} {delta32 : BitVec 32}
    {R' : Mem 64 → Prop} {mem : Mem 64} {P : BitVec 64 → BitVec 32 → Mem 64 → Prop}
    {PostQ : Post (wasmRetSig [.i32])} (hNz : delta32 ≠ 0#32)
    (hDone : ∀ f' r' m', P f' r' m' → PostQ (0#32, f', r', ()) m')
    (hm : (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) curLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ R') mem)
    (hFail : (curLen.ule (curLen + (delta32.setWidth 64 <<< 16)) &&
        ((curLen + (delta32.setWidth 64 <<< 16)).ule memCap &&
         (curLen + (delta32.setWidth 64 <<< 16)).ule 4294967296#64)) = false →
      P fuel 0xFFFFFFFF#32 mem)
    (hGrow : (curLen.ule (curLen + (delta32.setWidth 64 <<< 16)) &&
        ((curLen + (delta32.setWidth 64 <<< 16)).ule memCap &&
         (curLen + (delta32.setWidth 64 <<< 16)).ule 4294967296#64)) = true →
      ∀ jDone : Cont [i64, i32], (∀ f' r' m', P f' r' m' → jDone (f', r', ()) m') →
        wp Γ PostQ X (emitMemGrowLoop [.i32] jDone (.var (vmCtx + 8#64))
          (.var (curLen + (delta32.setWidth 64 <<< 16))) (.var ((curLen >>> 16).setWidth 32))
          (.var fuel) (.var (delta32.setWidth 64)) (.var (memBase + curLen))) mem) :
    Func.wp Γ (lowerFn bulkMod fnGrow).body (vmCtx, fuel, delta32, ()) mem PostQ X := by
  simp only [Func.wp, lowerFn, lowerFuncBody, bulkMod, fnGrow, GetElem?.getElem?, get?Int_succ,
    get?Int_zero, Option.getD, Option.map, Option.isSome, List.map, List.append, List.cons_append,
    List.nil_append, WMemSpec.maxBytes, WMemSpec.effectiveMaxPages, WValTy.toTy, labelSig]
  refine wp_join_group (fun xs m' => P xs.1 xs.2.2.1 m')
    (fun _ ⟨fRet, _, rRet, ⟨⟩⟩ m' h => by
      dsimp only [Blocks.get_here, tupSplit, varsTup]; rw [wp_ret_]; exact hDone fRet rRet m' h)
    fun _ _ => ?_
  simp only [lowerSeq, lowerSimpleInstr, pop32, popArgsAux, popExpectS, Bind.bind, Option.bind,
    varsTup, ↓reduceIte, emitMemGrow]
  refine wp_join_group (fun xs m' => P xs.1 xs.2.1 m')
    (fun _ ⟨fD, rD, ⟨⟩⟩ m' h => by
      dsimp only [Blocks.get_here]; rw [wp_ret_]; exact hDone fD rD m' h)
    fun jDone hjDone => ?_
  refine wp_load_ctx hm (Or.inl ⟨rfl, rfl⟩) ?_; wasm_wp_let
  refine wp_load_ctx hm (Or.inr (Or.inl ⟨rfl, rfl⟩)) ?_; wasm_wp_let
  refine wp_load_ctx hm (Or.inr (Or.inr ⟨rfl, rfl⟩)) ?_
  have hsh16 : ((16#64 : BitVec 64).toNat % 64) = 16 := rfl
  wasm_wp_let; simp only [hsh16]; wasm_wp_lets; rw [wp_jnz_]
  refine ⟨fun hzero => absurd (of_decide_eq_true
      (by simp only [arg_var_val] at hzero; exact hzero)) hNz, fun _ => ?_⟩
  wasm_wp_let; wasm_wp_let; simp only [hsh16]; wasm_wp_lets; rw [wp_jnz_]
  refine ⟨fun hok => ?_, fun hnot => ?_⟩
  · rw [arg_var_val, Bool.and_assoc,
      show BitVec.ofNat 64 (Nat.min 65536 65536 * 65536) = 4294967296#64 from by decide] at hok
    wasm_wp_let; exact hGrow hok jDone fun f' r' m' h => hjDone (f', r', ()) m' h
  · rw [arg_var_val, Bool.and_assoc,
      show BitVec.ofNat 64 (Nat.min 65536 65536 * 65536) = 4294967296#64 from by decide] at hnot
    rw [wp_jump_]; exact hjDone (fuel, 0xFFFFFFFF#32, ()) mem (hFail hnot)

/-- Concrete `Func.wp` behavioral proof for valid `memory.grow (delta := 1#32)`: zeroes all `8192`
64-bit words in `[memBase + 65536, memBase + 131072)`, updates `[vmCtx + 8]` to `131072#64`,
returns `(0#32, fuel - 1#64, 1#32, ())`, and preserves `memBase..+65536` and host frame `R`. -/
theorem bm_grow_ok (Γ : Env) (vmCtx memBase fuel : BitVec 64)
    (oldWs : List (BitVec 64)) (hlen : oldWs.length = 8192) (R : Mem 64 → Prop) (mem : Mem 64)
    (X : XPost) (hf : 1 ≤ fuel.toNat)
    (hm : (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) 65536#64 ⋆
      cell64 (vmCtx + 16#64) 131072#64 ⋆ region memBase 65536 ⋆
      array64 (memBase + 65536#64) oldWs ⋆ R) mem) :
    Func.wp Γ (lowerFn bulkMod fnGrow).body (vmCtx, fuel, 1#32, ()) mem
      (fun ys m' => ys = (0#32, fuel - 1#64, 1#32, ()) ∧
        (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) 131072#64 ⋆
          cell64 (vmCtx + 16#64) 131072#64 ⋆ region memBase 65536 ⋆
          array64 (memBase + 65536#64) (List.replicate 8192 0#64) ⋆ R) m') X := by
  let PostQ : Post (wasmRetSig [.i32]) := fun ys m' => ys = (0#32, fuel - 1#64, 1#32, ()) ∧
    (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) 131072#64 ⋆ cell64 (vmCtx + 16#64) 131072#64 ⋆
      region memBase 65536 ⋆ array64 (memBase + 65536#64) (List.replicate 8192 0#64) ⋆ R) m'
  change Func.wp Γ (lowerFn bulkMod fnGrow).body (vmCtx, fuel, 1#32, ()) mem PostQ X
  refine fnGrow_wp_step (R' := region memBase 65536 ⋆ array64 (memBase + 65536#64) oldWs ⋆ R)
    (P := fun f' r' m' => f' = fuel - 1#64 ∧ r' = 1#32 ∧ (cell64 vmCtx memBase ⋆
      cell64 (vmCtx + 8#64) 131072#64 ⋆ cell64 (vmCtx + 16#64) 131072#64 ⋆
      region memBase 65536 ⋆ array64 (memBase + 65536#64) (List.replicate 8192 0#64) ⋆ R) m')
    (PostQ := PostQ) (by decide) (fun _ _ _ ⟨hf', hr', hm'⟩ => by subst hf' hr'; exact ⟨rfl, hm'⟩)
    (sep_cast hm (by ac_rfl)) (fun h => by exfalso; revert h; decide) fun _ jDone hjDone => ?_
  simp only [emitMemGrowLoop]; refine wp_unroll_group fun lPage hlPage => ?_
  rw [wp_jump_]; apply hlPage (fuel, 1#64, memBase + 65536#64, ()) mem
  dsimp only [Blocks.get_here]; wasm_wp_let; rw [wp_jnz_]
  refine ⟨fun h0 => by exfalso; revert h0; decide, fun _ => ?_⟩
  have hfne : fuel ≠ 0#64 := fun h0 => by simp [h0] at hf
  wasm_wp_let; rw [wp_jnz_]
  refine ⟨fun hfz => by dsimp only [arg_var_val] at hfz; simp [hfne] at hfz, fun _ => ?_⟩
  wasm_wp_let; refine emitMemZeroPage_zero (base := memBase + 65536#64)
    (R' := cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) 65536#64 ⋆
      cell64 (vmCtx + 16#64) 131072#64 ⋆ region memBase 65536 ⋆ R)
    hlen (.var (memBase + 65536#64)) rfl (sep_cast hm (by ac_rfl)) _ fun m' hm' => ?_
  wasm_wp_lets; rw [wp_jump_]
  apply hlPage (fuel - 1#64, 0#64, memBase + 65536#64 + 65536#64, ()) m'
  dsimp only [Blocks.get_here]; wasm_wp_let; rw [wp_jnz_]
  refine ⟨fun _ => ?_, fun hnz => by exfalso; revert hnz; decide⟩; rw [wp_store_]
  have hm'c : (cell64 (vmCtx + 8#64) 65536#64 ⋆ (cell64 vmCtx memBase ⋆
      cell64 (vmCtx + 16#64) 131072#64 ⋆ region memBase 65536 ⋆
      array64 (memBase + 65536#64) (List.replicate 8192 0#64) ⋆ R)) m' := sep_cast hm' (by ac_rfl)
  obtain ⟨hsok, hm''⟩ := store_cell64 (131072#64) hm'c
  refine ⟨by simpa [arg_var_val,
      show ((1#32 : BitVec 32).setWidth 64 <<< 16) = 65536#64 by decide,
      show (65536#64 + 65536#64 : BitVec 64) = 131072#64 by decide] using hsok, ?_⟩
  rw [wp_jump_]; exact hjDone _ _ _ ⟨rfl, by decide, sep_cast hm'' (by ac_rfl)⟩

/-- Concrete `Func.wp` behavioral proof for over-cap `memory.grow (delta := 2#32)`: returns
`0xFFFFFFFF#32` (`-1`) with `status = 0#32`, `mem' = mem` (zero writes), and `R mem'`. -/
theorem bm_grow_fail (Γ : Env) (vmCtx memBase fuel : BitVec 64)
    (R : Mem 64 → Prop) (mem : Mem 64) (X : XPost)
    (hm : WasmMemInv true vmCtx memBase 65536#64 131072#64 R mem) :
    Func.wp Γ (lowerFn bulkMod fnGrow).body (vmCtx, fuel, 2#32, ()) mem
      (fun ys m' => ys = (0#32, fuel, 0xFFFFFFFF#32, ()) ∧ m' = mem ∧
        WasmMemInv true vmCtx memBase 65536#64 131072#64 R m') X :=
  fnGrow_wp_step
    (P := fun f' r' m' => f' = fuel ∧ r' = 0xFFFFFFFF#32 ∧ m' = mem ∧
      WasmMemInv true vmCtx memBase 65536#64 131072#64 R m')
    (R' := region memBase 131072 ⋆ R) (by decide)
    (fun _ _ _ ⟨hf', hr', hmEq, hm'⟩ => by subst hf'; subst hr'; exact ⟨rfl, hmEq, hm'⟩)
    (sep_cast hm.2 (by ac_rfl)) (fun _ => ⟨rfl, rfl, rfl, hm⟩)
    (fun hok _ _ => by exfalso; revert hok; decide)

local macro "wasm_bm_void3_head"
    fnId:ident loopPost:ident n:ident jBlk:ident hjBlk:ident
    hnNz:term "," hm:term "," hDone:term : tactic => `(tactic| (
  simp only [Func.wp, lowerFn, lowerFuncBody, bulkMod, $fnId:ident, GetElem?.getElem?, get?Int_succ,
    get?Int_zero, Option.getD, Option.map, Option.isSome, List.map, List.append, List.cons_append,
    List.nil_append, WMemSpec.maxBytes, WMemSpec.effectiveMaxPages, WValTy.toTy, labelSig]
  refine wp_join_group (fun xs m' => $loopPost:ident xs.1 m')
    (fun _ xs m' h => by
      rcases xs with ⟨fRet, _, _, _, ⟨⟩⟩
      dsimp only [Blocks.get_here, tupSplit, varsTup]; rw [wp_ret_]; exact $hDone fRet m' h)
    (fun _ _ => ?_)
  simp only [lowerSeq, WBlockTy.resolve, varsTup, popArgsAux, List.map]
  refine wp_join_group (fun xs m' => $loopPost:ident xs.1 m')
    (fun _ xs m' h => by
      rcases xs with ⟨fBlk, _, _, _, ⟨⟩⟩
      dsimp only [Blocks.get_here, tupSplit, varsTup]; rw [wp_ret_]; exact $hDone fBlk m' h)
    (fun $jBlk:ident $hjBlk:ident => ?_)
  simp only [lowerSimpleInstr]
  dsimp only [appendZeroLocals, zeroArgs, pushArgsAux, getLocal,
    GetElem?.getElem?, List.get?Internal]
  simp only [popArgsAux, pop32, ↓reduceIte]
  wasm_wp_lets; rw [wp_jnz_]
  refine ⟨fun hz => False.elim <| (by
    intro h; rw [decide_eq_false $hnNz] at h; revert h; decide :
    decide (BitVec.ofNat 32 (decide ($n:ident = 0#32)).toNat ≠ 0#32) = true → False) hz,
    fun _ => ?_⟩
  simp only [emitMemFill, emitMemCopy, emitLoadVmCtx]
  refine wp_load_ctx $hm (Or.inl ⟨rfl, rfl⟩) ?_; wasm_wp_let
  refine wp_load_ctx $hm (Or.inr (Or.inl ⟨rfl, rfl⟩)) ?_))

private theorem fnFill_wp_step {Γ : Env} {X : XPost}
    {vmCtx memBase memLen memCap fuel : BitVec 64} {dst val n : BitVec 32}
    {R' : Mem 64 → Prop} {mem : Mem 64}
    {LoopPost : BitVec 64 → Mem 64 → Prop} {PostQ : Post (wasmRetSig [])}
    (hnNz : n ≠ 0#32)
    (hm : (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ R') mem)
    (hDone : ∀ fA m', LoopPost fA m' → PostQ (0#32, fA, ()) m')
    (hTrap : (dst.setWidth 64 + n.setWidth 64).ule memLen = false →
      PostQ (1#32, fuel, ()) mem)
    (hIn : (dst.setWidth 64 + n.setWidth 64).ule memLen = true →
      ∀ jAfter : Cont [i64], (∀ fA m', LoopPost fA m' → jAfter (fA, ()) m') →
        wp Γ PostQ X (emitMemFillLoop [] jAfter (.var (val.setWidth 8)) (.var fuel)
          (.var (n.setWidth 64)) (.var (memBase + dst.setWidth 64))) mem) :
    Func.wp Γ (lowerFn bulkMod fnFill).body (vmCtx, fuel, dst, val, n, ()) mem PostQ X := by
  wasm_bm_void3_head fnFill LoopPost n jBlk hjBlk hnNz, hm, hDone
  wasm_wp_lets; rw [wp_jnz_]
  refine ⟨fun hok => ?_, fun hnot => by rw [wp_ret_]; exact hTrap (by simpa [Arg.val] using hnot)⟩
  wasm_wp_lets
  refine wp_join_group (fun xs m' => LoopPost xs.1 m')
    (fun _ ⟨fA, ⟨⟩⟩ m' h => by
      dsimp only [Blocks.get_here, lowerSeq, popArgsAux, varsTup]
      rw [wp_jump_]; exact hjBlk (fA, dst, val, n, ()) m' h)
    fun jAfter hjAfter =>
      hIn (by simpa [Arg.val] using hok) jAfter fun fA m' h => hjAfter (fA, ()) m' h

private theorem u32Add_ule_true {a b : BitVec 32} {memLen : BitVec 64}
    (h : a.toNat + b.toNat ≤ memLen.toNat) :
    (a.setWidth 64 + b.setWidth 64).ule memLen = true := by c0_bv_omega
private theorem u32_ule_true {a b : BitVec 32} (h : a.toNat ≤ b.toNat) :
    (a.setWidth 64).ule (b.setWidth 64) = true := by c0_bv_omega
private theorem u32_ule_false {a b : BitVec 32} (h : b.toNat < a.toNat) :
    (a.setWidth 64).ule (b.setWidth 64) = false := by c0_bv_omega

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
      X :=
  fnFill_wp_step (LoopPost := fun fA m' => fA = BitVec.ofNat 64 (fuel.toNat - n.toNat) ∧
      (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆ cell64 (vmCtx + 16#64) memCap ⋆
        array (t := i8) memBase (listFillAux (val.setWidth 8) dst.toNat n.toNat bs) ⋆ R) m')
    (R' := array (t := i8) memBase bs ⋆ R) hnNz (sep_cast hm (by ac_rfl))
    (fun _ _ ⟨hfEq, hm'⟩ => ⟨by rw [hfEq], hm'⟩)
    (fun hnot => by exfalso; rw [u32Add_ule_true hleLen] at hnot; cases hnot)
    fun _ jAfter hjAfter => by
      refine emitMemFillLoop_bytes jAfter (n64 := n.setWidth 64) (dstOff := dst.toNat)
        (byteVal := val.setWidth 8) (by rwa [bv32_toNat_setWidth64])
        (by rwa [bv32_toNat_setWidth64]) (by rw [bv32_setWidth64_eq_ofNat]) (sep_ctx_arr.mp hm)
        fun m' hm' => ?_
      rw [bv32_toNat_setWidth64] at hm'
      exact hjAfter _ _ ⟨by rw [bv32_toNat_setWidth64], sep_ctx_arr.mpr hm'⟩

private theorem fnCopy_wp_step {Γ : Env} {X : XPost}
    {vmCtx memBase memLen memCap fuel : BitVec 64} {dst src n : BitVec 32}
    {R' : Mem 64 → Prop} {mem : Mem 64} {LoopPost : BitVec 64 → Mem 64 → Prop}
    {PostQ : Post (wasmRetSig [])} (hnNz : n ≠ 0#32)
    (hm : (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ R') mem)
    (hDone : ∀ fA m', LoopPost fA m' → PostQ (0#32, fA, ()) m')
    (hTrap : ((dst.setWidth 64 + n.setWidth 64).ule memLen &&
        (src.setWidth 64 + n.setWidth 64).ule memLen) = false → PostQ (1#32, fuel, ()) mem)
    (hFwd : ((dst.setWidth 64 + n.setWidth 64).ule memLen &&
        (src.setWidth 64 + n.setWidth 64).ule memLen) = true →
      (dst.setWidth 64).ule (src.setWidth 64) = true →
      ∀ jAfter : Cont [i64], (∀ fA m', LoopPost fA m' → jAfter (fA, ()) m') →
        wp Γ PostQ X (emitMemCopyLoop true [] jAfter (.var fuel) (.var (n.setWidth 64))
          (.var (memBase + dst.setWidth 64)) (.var (memBase + src.setWidth 64))) mem)
    (hBwd : ((dst.setWidth 64 + n.setWidth 64).ule memLen &&
        (src.setWidth 64 + n.setWidth 64).ule memLen) = true →
      (dst.setWidth 64).ule (src.setWidth 64) = false →
      ∀ jAfter : Cont [i64], (∀ fA m', LoopPost fA m' → jAfter (fA, ()) m') →
        wp Γ PostQ X (emitMemCopyLoop false [] jAfter (.var fuel) (.var (n.setWidth 64))
          (.var (memBase + (dst.setWidth 64 + n.setWidth 64)))
          (.var (memBase + (src.setWidth 64 + n.setWidth 64)))) mem) :
    Func.wp Γ (lowerFn bulkMod fnCopy).body (vmCtx, fuel, dst, src, n, ()) mem PostQ X := by
  wasm_bm_void3_head fnCopy LoopPost n jBlk hjBlk hnNz, hm, hDone
  wasm_wp_lets; rw [wp_jnz_]
  refine ⟨fun hok => ?_, fun hnot => by rw [wp_ret_]; exact hTrap (by simpa [Arg.val] using hnot)⟩
  have hokB : ((dst.setWidth 64 + n.setWidth 64).ule memLen &&
      (src.setWidth 64 + n.setWidth 64).ule memLen) = true := by simpa [Arg.val] using hok
  refine wp_join_group (fun xs m' => LoopPost xs.1 m')
    (fun _ ⟨fA, ⟨⟩⟩ m' h => by
      dsimp only [Blocks.get_here, lowerSeq, popArgsAux, varsTup]
      rw [wp_jump_]; exact hjBlk (fA, dst, src, n, ()) m' h)
    fun jAfter hjAfter => ?_
  wasm_wp_let; rw [wp_jnz_]
  refine ⟨fun hdir => ?_, fun hdir => ?_⟩ <;> (wasm_wp_lets; first
    | exact hFwd hokB (by simpa [Arg.val] using hdir) jAfter fun fA m' h => hjAfter (fA, ()) m' h
    | exact hBwd hokB (by simpa [Arg.val] using hdir) jAfter fun fA m' h => hjAfter (fA, ()) m' h)

/-- Concrete `Func.wp` behavioral proof for overlapping forward `memory.copy` (`dst ≤ src`):
matches `listCopyFwdAux` (exact `memmove`), preserves host frame `R`, and deducts `n` fuel. -/
theorem bm_copy_fwd (Γ : Env) (vmCtx memBase memLen memCap fuel : BitVec 64)
    (dst src n : BitVec 32) (bs : List (BitVec 8)) (R : Mem 64 → Prop) (mem : Mem 64)
    (X : XPost) (hnNz : n ≠ 0#32) (hfwd : dst.toNat ≤ src.toNat) (hfn : n.toNat ≤ fuel.toNat)
    (hdLen : dst.toNat + n.toNat ≤ memLen.toNat) (hsLen : src.toNat + n.toNat ≤ memLen.toNat)
    (hdBs : dst.toNat + n.toNat ≤ bs.length) (hsBs : src.toNat + n.toNat ≤ bs.length)
    (hm : (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ array (t := i8) memBase bs ⋆ R) mem) :
    Func.wp Γ (lowerFn bulkMod fnCopy).body (vmCtx, fuel, dst, src, n, ()) mem
      (fun ys m' => ys = (0#32, BitVec.ofNat 64 (fuel.toNat - n.toNat), ()) ∧
        (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆
          cell64 (vmCtx + 16#64) memCap ⋆
          array (t := i8) memBase (listCopyFwdAux dst.toNat src.toNat n.toNat bs) ⋆ R) m') X :=
  fnCopy_wp_step (LoopPost := fun fA m' => fA = BitVec.ofNat 64 (fuel.toNat - n.toNat) ∧
      (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆ cell64 (vmCtx + 16#64) memCap ⋆
        array (t := i8) memBase (listCopyFwdAux dst.toNat src.toNat n.toNat bs) ⋆ R) m')
    (R' := array (t := i8) memBase bs ⋆ R) hnNz (sep_cast hm (by ac_rfl))
    (fun _ _ ⟨hfEq, hm'⟩ => ⟨by rw [hfEq], hm'⟩)
    (fun hnot => by exfalso; rw [u32Add_ule_true hdLen, u32Add_ule_true hsLen] at hnot; cases hnot)
    (fun _ _ jAfter hjAfter => by
      refine emitMemCopyLoop_fwd_bytes jAfter (n64 := n.setWidth 64) (dstOff := dst.toNat)
        (srcOff := src.toNat) (by rwa [bv32_toNat_setWidth64]) (by rwa [bv32_toNat_setWidth64])
        (by rwa [bv32_toNat_setWidth64]) (by rw [bv32_setWidth64_eq_ofNat])
        (by rw [bv32_setWidth64_eq_ofNat]) (sep_ctx_arr.mp hm) fun m' hm' => ?_
      rw [bv32_toNat_setWidth64] at hm'
      exact hjAfter _ _ ⟨by rw [bv32_toNat_setWidth64], sep_ctx_arr.mpr hm'⟩)
    fun _ hdir _ _ => by exfalso; rw [u32_ule_true hfwd] at hdir; cases hdir

/-- Concrete `Func.wp` behavioral proof for overlapping backward `memory.copy` (`src < dst`):
matches `listCopyBwdAux` (exact `memmove`), preserves host frame `R`, and deducts `n` fuel. -/
theorem bm_copy_bwd (Γ : Env) (vmCtx memBase memLen memCap fuel : BitVec 64)
    (dst src n : BitVec 32) (bs : List (BitVec 8)) (R : Mem 64 → Prop) (mem : Mem 64)
    (X : XPost) (hnNz : n ≠ 0#32) (hbwd : src.toNat < dst.toNat) (hfn : n.toNat ≤ fuel.toNat)
    (hdLen : dst.toNat + n.toNat ≤ memLen.toNat) (hsLen : src.toNat + n.toNat ≤ memLen.toNat)
    (hdBs : dst.toNat + n.toNat ≤ bs.length) (hsBs : src.toNat + n.toNat ≤ bs.length)
    (hm : (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆
      cell64 (vmCtx + 16#64) memCap ⋆ array (t := i8) memBase bs ⋆ R) mem) :
    Func.wp Γ (lowerFn bulkMod fnCopy).body (vmCtx, fuel, dst, src, n, ()) mem
      (fun ys m' => ys = (0#32, BitVec.ofNat 64 (fuel.toNat - n.toNat), ()) ∧
        (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆
          cell64 (vmCtx + 16#64) memCap ⋆
          array (t := i8) memBase
            (listCopyBwdAux dst.toNat src.toNat n.toNat n.toNat bs) ⋆ R) m') X :=
  fnCopy_wp_step (LoopPost := fun fA m' => fA = BitVec.ofNat 64 (fuel.toNat - n.toNat) ∧
      (cell64 vmCtx memBase ⋆ cell64 (vmCtx + 8#64) memLen ⋆ cell64 (vmCtx + 16#64) memCap ⋆
        array (t := i8) memBase (listCopyBwdAux dst.toNat src.toNat n.toNat n.toNat bs) ⋆ R) m')
    (R' := array (t := i8) memBase bs ⋆ R) hnNz (sep_cast hm (by ac_rfl))
    (fun _ _ ⟨hfEq, hm'⟩ => ⟨by rw [hfEq], hm'⟩)
    (fun hnot => by exfalso; rw [u32Add_ule_true hdLen, u32Add_ule_true hsLen] at hnot; cases hnot)
    (fun _ hdir _ _ => by exfalso; rw [u32_ule_false hbwd] at hdir; cases hdir)
    fun _ _ jAfter hjAfter => by
      refine emitMemCopyLoop_bwd_bytes jAfter (n64 := n.setWidth 64) (dstOff := dst.toNat)
        (srcOff := src.toNat) (by rwa [bv32_toNat_setWidth64]) (by rwa [bv32_toNat_setWidth64])
        (by rwa [bv32_toNat_setWidth64])
        (by rw [bv32_toNat_setWidth64, bv32_setWidth64_eq_ofNat, bv32_setWidth64_eq_ofNat,
          bv64_ofNat_add_eq])
        (by rw [bv32_toNat_setWidth64, bv32_setWidth64_eq_ofNat, bv32_setWidth64_eq_ofNat,
          bv64_ofNat_add_eq]) (sep_ctx_arr.mp hm) fun m' hm' => ?_
      rw [bv32_toNat_setWidth64] at hm'
      exact hjAfter _ _ ⟨by rw [bv32_toNat_setWidth64], sep_ctx_arr.mpr hm'⟩

-- Concrete 8-byte checks for fill, forward overlap copy, and backward overlap `memmove`
private def exBytes : List (BitVec 8) :=
  [0x10#8, 0x11#8, 0x12#8, 0x13#8, 0x14#8, 0x15#8, 0x16#8, 0x17#8]

#guard listFillAux 0xAB#8 2 4 exBytes ==
  [0x10#8, 0x11#8, 0xAB#8, 0xAB#8, 0xAB#8, 0xAB#8, 0x16#8, 0x17#8] &&
  listCopyFwdAux 1 3 4 exBytes ==
    [0x10#8, 0x13#8, 0x14#8, 0x15#8, 0x16#8, 0x15#8, 0x16#8, 0x17#8] &&
  listCopyBwdAux 3 1 4 4 exBytes ==
    [0x10#8, 0x11#8, 0x12#8, 0x11#8, 0x12#8, 0x13#8, 0x14#8, 0x17#8]

/-- Adversarial `u32` wraparound OOB `memory.fill (dst = 0xFFFFFFF0, n = 32)` on 64 KiB memory:
traps cleanly (`status = 1#32`) with zero memory writes (`mem' = mem`) and `R mem'`. -/
theorem bm_fill_oob (Γ : Env) (vmCtx memBase memCap fuel : BitVec 64)
    (R : Mem 64 → Prop) (mem : Mem 64) (X : XPost)
    (hm : WasmMemInv true vmCtx memBase 65536#64 memCap R mem) :
    Func.wp Γ (lowerFn bulkMod fnFill).body (vmCtx, fuel, 0xFFFFFFF0#32, 0xAB#32, 32#32, ()) mem
      (fun ys m' => ys = (1#32, fuel, ()) ∧ m' = mem ∧
        WasmMemInv true vmCtx memBase 65536#64 memCap R m') X :=
  fnFill_wp_step (LoopPost := fun _ _ => False) (R' := region memBase memCap.toNat ⋆ R) (by decide)
    (sep_cast hm.2 (by ac_rfl)) (fun _ _ h => False.elim h) (fun _ => ⟨rfl, rfl, hm⟩)
    (fun hok _ _ => by exfalso; revert hok; decide)

/-- Adversarial `u32` wraparound OOB `memory.copy (dst = 0xFFFFFFF0, src = 0, n = 32)` on 64 KiB
memory: traps cleanly (`status = 1#32`) with zero memory writes (`mem' = mem`) and `R mem'`. -/
theorem bm_copy_wrap (Γ : Env) (vmCtx memBase memCap fuel : BitVec 64)
    (R : Mem 64 → Prop) (mem : Mem 64) (X : XPost)
    (hm : WasmMemInv true vmCtx memBase 65536#64 memCap R mem) :
    Func.wp Γ (lowerFn bulkMod fnCopy).body (vmCtx, fuel, 0xFFFFFFF0#32, 0#32, 32#32, ()) mem
      (fun ys m' => ys = (1#32, fuel, ()) ∧ m' = mem ∧
        WasmMemInv true vmCtx memBase 65536#64 memCap R m') X :=
  fnCopy_wp_step (LoopPost := fun _ _ => False) (R' := region memBase memCap.toNat ⋆ R) (by decide)
    (sep_cast hm.2 (by ac_rfl)) (fun _ _ h => False.elim h) (fun _ => ⟨rfl, rfl, hm⟩)
    (fun hok _ _ _ => by exfalso; revert hok; decide)
    (fun hok _ _ _ => by exfalso; revert hok; decide)

/-! ## 5. Axiom Audit (Standard Axioms) -/

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
