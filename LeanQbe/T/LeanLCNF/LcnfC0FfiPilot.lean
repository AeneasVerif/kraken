/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
public import LeanQbe.T.LeanLCNF.C0Extern
public import LeanQbe.T.LeanLCNF.LcnfC0Ffi
public import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import Lean
meta import LeanQbe.T.Frontend.C0.Elab
meta import LeanQbe.T.LeanLCNF.C0Extern
meta import LeanQbe.T.LeanLCNF.Lower

/-!
# Shard `F3` Dual-Arch `LeanLCNF ↔ Verified C0 FFI` Pilot (`LcnfC0FfiPilot`)

Defines the end-to-end FFI pilot connecting pure Lean `@[expose, noinline]` FFI stubs with
explicit `@&` borrow annotations to verified C0 wrappers built on `F2`'s `LcnfC0Ffi` runtime
adapters and `Kissat.Plain.kissat_solve_bytes`:

1. Lean `@&`-borrowed FFI stubs (`kissatSolveBA`, `kissatSolveNat`, `xorBytesBA`, `xorBytesNat`)
   and pilot callers (`checkSatBA`, `checkSatNat`, `xorBA`, `xorNat`, `solveXorBA`). Zero
   `@[extern]`, zero C files, zero `axiom`s.
2. Pure C0 XOR byte kernel (`c0_xor_bytes`, `K2a` 6-arg packed return `(status << 56) | out_len`,
   zero `&local`) plus thin non-aborting C0 wrappers (`lcnf_c0_kissat_raw`,
   `lcnf_c0_kissat_solve_ba`, `lcnf_c0_kissat_solve_nat`, `lcnf_c0_xor_ba`, `lcnf_c0_xor_nat`)
   using top-down `s_end` scratch carve/reclaim and returning tagged error scalars on OOM/invalid
   input.
3. Explicit `pilotC0Externs : List C0Extern`, verified `checkC0Externs`, and kernel-lowered Lean
   pilot module (`pilotTfs` / `pilotProgMod`) via `lcnf_of_lean_with_exts!` and
   `splice_lcnf_tflat_with_exts!`.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.LcnfC0FfiPilot

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.LeanLCNF

/-! ## 1. Pure Lean FFI Stubs (`@&` Borrows, Zero `@[extern]`) & Pilot Callers -/

public section

/-- Borrowed-`ByteArray` Kissat SAT solver FFI stub. Returns `20` (UNSAT), `10` (SAT), `0`
(unknown/out-of-fuel), or `3` (non-aborting OOM). -/
@[expose, noinline] def kissatSolveBA (ba : @& ByteArray) (workReq fuel : USize) : USize :=
  ba.size.toUSize ^^^ workReq ^^^ fuel

/-- Borrowed-sentineled-`Nat` (`natOfBytesS`) Kissat SAT solver FFI stub. Returns `20` (UNSAT),
`10` (SAT), `0` (unknown), `1` (invalid sentineled `Nat`), or `3` (OOM). -/
@[expose, noinline] def kissatSolveNat (a : @& Nat) (workReq fuel : USize) : USize :=
  a.toUSize ^^^ workReq ^^^ fuel

/-- Borrowed-`ByteArray` bytewise XOR FFI stub returning `FfiRes ByteArray`. -/
@[expose, noinline] def xorBytesBA (ba : @& ByteArray) (key : UInt8) : FfiRes ByteArray :=
  if ba.size == 0x7fffffff then .oom
  else if ba.size == 0x7ffffffe then .invalidInput
  else if ba.size == 0x7ffffffd then .outOfFuel
  else .ok (ByteArray.mk (ba.data.map fun b => b ^^^ key))

/-- Borrowed-sentineled-`Nat` bytewise XOR FFI stub preserving sentinels, returning `FfiRes Nat`. -/
@[expose, noinline] def xorBytesNat (a : @& Nat) (key : UInt8) : FfiRes Nat :=
  if a == 0xfffffffffffffff1 then .oom
  else if a == 0xfffffffffffffff2 then .outOfFuel
  else
    match bytesOfNatS a with
    | some bs => .ok (natOfBytesS (bs.map fun b => b ^^^ key))
    | none => .invalidInput

/-- Lean pilot caller: solve DIMACS CNF carried in a borrowed `ByteArray`. -/
@[expose, noinline] def checkSatBA (ba : @& ByteArray) (workReq fuel : USize) : USize :=
  kissatSolveBA ba workReq fuel

/-- Lean pilot caller: solve DIMACS CNF carried in a borrowed sentineled `Nat`. -/
@[expose, noinline] def checkSatNat (a : @& Nat) (workReq fuel : USize) : USize :=
  kissatSolveNat a workReq fuel

/-- Lean pilot caller: bytewise XOR a borrowed `ByteArray` without aborting on OOM. -/
@[expose, noinline] def xorBA (ba : @& ByteArray) (key : UInt8) : FfiRes ByteArray :=
  xorBytesBA ba key

/-- Lean pilot caller: bytewise XOR a borrowed sentineled `Nat` without aborting on OOM. -/
@[expose, noinline] def xorNat (a : @& Nat) (key : UInt8) : FfiRes Nat :=
  xorBytesNat a key

/-- Composed Lean pilot caller: XOR-unmask a borrowed DIMACS `ByteArray` into a fresh `ByteArray`,
match `FfiRes`, and feed it directly to `kissatSolveBA` before releasing the temporary buffer. -/
@[expose, noinline] def solveXorBA (ba : @& ByteArray) (key : UInt8)
    (workReq fuel : USize) : USize :=
  match xorBytesBA ba key with
  | .ok masked => kissatSolveBA masked workReq fuel
  | .invalidInput => 1
  | .oom => 3
  | .outOfFuel => 7

/-! ## 2. Pure C0 Kernel (`c0_xor_bytes`) and Verified `LcnfC0Ffi` Wrappers (`pilotC0`) -/

/-- Pure C0 source for the `K2a` `c0_xor_bytes` kernel and thin non-aborting FFI wrappers calling
`Kissat.Plain.kissat_solve_bytes` and `F2`'s `LcnfC0Ffi` runtime adapters. -/
@[expose] def lcnfC0FfiPilotC0Src : String := "
extern u64 kissat_solve_bytes(u64 cnf_ptr, u64 cnf_len, u64 work_ptr, u64 work_cap, u64 fuel);
extern u64 lcnf_ffi_get_end(u64 rt);
extern u64 lcnf_ffi_carve_scratch(u64 rt, u64 req_bytes);
extern void lcnf_ffi_restore_scratch(u64 rt, u64 saved_end);
extern u64 lcnf_ffi_ba_ptr(u64 ba);
extern u64 lcnf_ffi_ba_len(u64 ba);
extern u64 lcnf_ffi_ba_wrap_ok(u64 rt, u64 src_ptr, u64 len);
extern u64 lcnf_ffi_nat_bytes_len(u64 a);
extern u64 lcnf_ffi_nat_bytes_ptr(u64 rt, u64 a);
extern u64 lcnf_ffi_nat_wrap_ok(u64 rt, u64 src_ptr, u64 len);

u64 c0_xor_bytes(u64 in_ptr, u64 in_len, u64 out_ptr, u64 out_cap,
                 u64 key_u8, u64 flags) {
  if (flags != 0ULL) {
    return 2ULL << 56ULL;
  }
  if (in_len > 0x00ffffffffffffffULL) {
    return 1ULL << 56ULL;
  }
  if (in_len > out_cap) {
    return 1ULL << 56ULL;
  }
  if (in_len > 0xffffffffffffffffULL - in_ptr) {
    return 1ULL << 56ULL;
  }
  if (out_cap > 0xffffffffffffffffULL - out_ptr) {
    return 1ULL << 56ULL;
  }
  u64 k = key_u8 & 255ULL;
  u64 i = 0ULL;
  while (i < in_len) {
    u64 b = (u64)(*(u8 *)(in_ptr + i));
    *(u8 *)(out_ptr + i) = (u8)(b ^ k);
    i = i + 1ULL;
  }
  return in_len;
}

u64 lcnf_c0_kissat_raw(u64 rt, u64 cnf_ptr, u64 cnf_len, u64 work_req, u64 fuel) {
  if (work_req == 0ULL || work_req > 0xfffffffffffffff8ULL) {
    return 3ULL;
  }
  u64 saved_end = lcnf_ffi_get_end(rt);
  u64 wptr = lcnf_ffi_carve_scratch(rt, work_req);
  if (wptr == 0ULL) {
    return 3ULL;
  }
  u64 wcap = (work_req + 7ULL) & 0xfffffffffffffff8ULL;
  u64 res = kissat_solve_bytes(cnf_ptr, cnf_len, wptr, wcap, fuel);
  lcnf_ffi_restore_scratch(rt, saved_end);
  return res;
}

u64 lcnf_c0_kissat_solve_ba(u64 rt, u64 ba, u64 work_req, u64 fuel) {
  u64 len = lcnf_ffi_ba_len(ba);
  if (ba > 0xffffffffffffffffULL - 24ULL) {
    return 3ULL;
  }
  u64 ptr = lcnf_ffi_ba_ptr(ba);
  if (len > 0xffffffffffffffffULL - ptr) {
    return 3ULL;
  }
  return lcnf_c0_kissat_raw(rt, ptr, len, work_req, fuel);
}

u64 lcnf_c0_kissat_solve_nat(u64 rt, u64 a, u64 work_req, u64 fuel) {
  u64 len = lcnf_ffi_nat_bytes_len(a);
  if (len == 0xffffffffffffffffULL) {
    return 1ULL;
  }
  u64 ptr = lcnf_ffi_nat_bytes_ptr(rt, a);
  if (ptr == 0ULL) {
    return 3ULL;
  }
  return lcnf_c0_kissat_raw(rt, ptr, len, work_req, fuel);
}

u64 lcnf_c0_xor_ba(u64 rt, u64 ba, u8 key) {
  u64 len = lcnf_ffi_ba_len(ba);
  if (len == 0ULL) {
    return lcnf_ffi_ba_wrap_ok(rt, 0ULL, 0ULL);
  }
  u64 in_ptr = lcnf_ffi_ba_ptr(ba);
  u64 saved_end = lcnf_ffi_get_end(rt);
  u64 out_ptr = lcnf_ffi_carve_scratch(rt, len);
  if (out_ptr == 0ULL) {
    return 5ULL;
  }
  u64 out_cap = (len + 7ULL) & 0xfffffffffffffff8ULL;
  u64 pk = c0_xor_bytes(in_ptr, len, out_ptr, out_cap, (u64)key, 0ULL);
  u64 status = pk >> 56ULL;
  u64 out_len = pk & 0x00ffffffffffffffULL;
  if (status != 0ULL) {
    lcnf_ffi_restore_scratch(rt, saved_end);
    return 3ULL;
  }
  u64 res = lcnf_ffi_ba_wrap_ok(rt, out_ptr, out_len);
  lcnf_ffi_restore_scratch(rt, saved_end);
  return res;
}

u64 lcnf_c0_xor_nat(u64 rt, u64 a, u8 key) {
  u64 len = lcnf_ffi_nat_bytes_len(a);
  if (len == 0xffffffffffffffffULL) {
    return 3ULL;
  }
  if (len == 0ULL) {
    return lcnf_ffi_nat_wrap_ok(rt, 0ULL, 0ULL);
  }
  u64 in_ptr = lcnf_ffi_nat_bytes_ptr(rt, a);
  if (in_ptr == 0ULL) {
    return 5ULL;
  }
  u64 saved_end = lcnf_ffi_get_end(rt);
  u64 out_ptr = lcnf_ffi_carve_scratch(rt, len);
  if (out_ptr == 0ULL) {
    return 5ULL;
  }
  u64 out_cap = (len + 7ULL) & 0xfffffffffffffff8ULL;
  u64 pk = c0_xor_bytes(in_ptr, len, out_ptr, out_cap, (u64)key, 0ULL);
  u64 status = pk >> 56ULL;
  u64 out_len = pk & 0x00ffffffffffffffULL;
  if (status != 0ULL) {
    lcnf_ffi_restore_scratch(rt, saved_end);
    return 3ULL;
  }
  u64 res = lcnf_ffi_nat_wrap_ok(rt, out_ptr, out_len);
  lcnf_ffi_restore_scratch(rt, saved_end);
  return res;
}
"

#eval show Lean.Elab.Command.CommandElabM Unit from
  LeanQbe.T.Frontend.C0.elabC0Module (some `pilotC0) lcnfC0FfiPilotC0Src
    (exits := []) (forceExpose := true)

theorem c0_xor_bytes_wf : Func.Wf c0_xor_bytes_body := by t_wf_reify
theorem lcnf_c0_kissat_raw_wf : Func.Wf lcnf_c0_kissat_raw_body := by t_wf_reify
theorem lcnf_c0_kissat_solve_ba_wf : Func.Wf lcnf_c0_kissat_solve_ba_body := by t_wf_reify
theorem lcnf_c0_kissat_solve_nat_wf : Func.Wf lcnf_c0_kissat_solve_nat_body := by t_wf_reify
theorem lcnf_c0_xor_ba_wf : Func.Wf lcnf_c0_xor_ba_body := by t_wf_reify
theorem lcnf_c0_xor_nat_wf : Func.Wf lcnf_c0_xor_nat_body := by t_wf_reify

/-- Verified `Fn.Wf` for every C0 function in `pilotC0_fns`. -/
theorem pilotC0_fns_wf : ∀ f ∈ pilotC0_fns, f.Wf := by
  intro f hf
  simp only [pilotC0_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact c0_xor_bytes_wf
  · exact lcnf_c0_kissat_raw_wf
  · exact lcnf_c0_kissat_solve_ba_wf
  · exact lcnf_c0_kissat_solve_nat_wf
  · exact lcnf_c0_xor_ba_wf
  · exact lcnf_c0_xor_nat_wf

/-- Static acyclicity of `pilotC0_module`. -/
theorem pilotC0_checkAcyclic : pilotC0_module.checkAcyclic = true := by
  decide

/-! ## 3. Explicit `C0Extern` Registry, Extraction & Lowering -/

/-- Verified `@&`-borrow-checked `C0Extern` descriptor list for the pilot FFI stubs. -/
@[expose] def pilotC0Externs : List C0Extern :=
  [ { leanName := "LeanQbe.T.LeanLCNF.LcnfC0FfiPilot.kissatSolveBA"
      c0Sym := "lcnf_c0_kissat_solve_ba"
      params := [.object, .usize, .usize]
      borrows := [true, false, false]
      retTy := .usize
      passRt := true }
  , { leanName := "LeanQbe.T.LeanLCNF.LcnfC0FfiPilot.kissatSolveNat"
      c0Sym := "lcnf_c0_kissat_solve_nat"
      params := [.tobject, .usize, .usize]
      borrows := [true, false, false]
      retTy := .usize
      passRt := true }
  , { leanName := "LeanQbe.T.LeanLCNF.LcnfC0FfiPilot.xorBytesBA"
      c0Sym := "lcnf_c0_xor_ba"
      params := [.object, .uint8]
      borrows := [true, false]
      retTy := .tobject
      passRt := true }
  , { leanName := "LeanQbe.T.LeanLCNF.LcnfC0FfiPilot.xorBytesNat"
      c0Sym := "lcnf_c0_xor_nat"
      params := [.tobject, .uint8]
      borrows := [true, false]
      retTy := .tobject
      passRt := true }
  ]

/-- Kernel check that every `C0Extern` in `pilotC0Externs` matches `pilotC0_module`. -/
theorem pilotC0Externs_valid : checkC0Externs pilotC0Externs (some pilotC0_module) = true := by
  decide

lcnf_of_lean_with_exts! pilotLcMod pilotC0Externs
  [checkSatBA, checkSatNat, xorBA, xorNat, solveXorBA]

/-- Kernel check that extracted LCNF module matches `pilotC0Externs` (`@&` borrows + C0 sigs). -/
theorem pilotLcMod_externs_valid :
    checkLcModuleExts pilotLcMod pilotC0Externs (some pilotC0_module) = true := by
  decide

splice_lcnf_tflat_with_exts! pilotTfs pilotLcMod pilotC0Externs

/-- Lowered `LeanQbe.T.Module` of the Lean pilot (runtime + `pilotC0Externs` are `externs`). -/
@[expose] def pilotProgMod : LeanQbe.T.Module :=
  lcnfTModuleWithExts pilotTfs pilotC0Externs

/-- Every lowered pilot function satisfies `Fn.Wf`. -/
theorem pilotProgMod_fns_wf : ∀ f ∈ pilotProgMod.fns, f.Wf := by
  intro f hf
  simpa [pilotProgMod, lcnfTModuleWithExts] using
    Frontend.C0.tflatFnsToFns_wf pilotTfs f hf

end

end LeanQbe.T.LeanLCNF.LcnfC0FfiPilot
