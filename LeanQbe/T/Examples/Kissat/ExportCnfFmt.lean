/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.Module
public import LeanQbe.T.Wf
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.Wf

/-!
# Verified C0 ASCII DIMACS CNF Formatter Primitives (`ExportCnfFmt`)

Strictly additive, data-pure (`0` `*Proof*`/`*Lemmas*`/`*Spec*` imports) C0 leaf module
implementing the four iterative, acyclic, bounds-checked ASCII DIMACS serializer primitives
for Kissat simplified-CNF export (`<= 5` `u64` arguments, `0` exits, `0` externs, `0` stack
allocations, legal on both SysV x86-64 and AAPCS64 Arm64):

1. `kissat_emit_byte(out, cap, pos, b)`: writes `(u8)b` at `out + pos` iff `pos < cap`,
   returning saturating `pos + 1` (supporting dry-run length counting with `cap = 0` and
   truncated/insufficient-capacity safety without out-of-bounds writes).
2. `kissat_emit_u64(out, cap, pos, x)`: emits base-10 ASCII decimal digits of `x : u64`
   left-to-right via iterative power-of-10 scaling (`p <= x / 10` then `p > 0`), using zero
   stack buffer and delegating every byte write to `kissat_emit_byte`.
3. `kissat_emit_dimacs_lit(out, cap, pos, lit)`: converts 0-based Kissat internal literal
   `lit` (`2 * (v - 1)` positive, `2 * (v - 1) + 1` negative) to 1-based signed DIMACS ASCII
   with trailing space (`"<v> "` or `"-<v> "`), matching `LratBytes.encodeDimacsLit`.
4. `kissat_emit_dimacs_hdr(out, cap, pos, mv, nc)`: emits `"p cnf <mv> <nc>\n"`.

Separation-logic WP specifications, closed-module `ModuleOk`, and pure `parseDimacs` round-trip
theorems live in `LeanQbe.T.Examples.Kissat.ExportCnfFmtProof`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.ExportCnfFmt

open LeanQbe.T
open LeanQbe.T.Frontend.C0

@[expose] public section

local elab "export_cnf_fmt_c0! " pfx:ident src:str : command => do
  let nm := Lean.mkIdent `exportCnfFmtC0Src
  let defCmd ← `(command| def $nm : String := $src)
  Lean.Elab.Command.elabCommand defCmd
  elabC0Module (some pfx.getId) src.getString (forceExpose := true) (emitModule := false)

export_cnf_fmt_c0! exportCnfFmt "
u64 kissat_emit_byte(u64 out, u64 cap, u64 pos, u64 b) {
  if (pos < cap) {
    *(u8 *)(out + pos) = (u8)b;
  }
  if (pos < 0xFFFFFFFFFFFFFFFFULL) {
    return pos + 1ULL;
  }
  return pos;
}

u64 kissat_emit_u64(u64 out, u64 cap, u64 pos, u64 x) {
  u64 q = x / 10ULL;
  u64 p = 1ULL;
  while (p <= q) {
    p = p * 10ULL;
  }
  while (p > 0ULL) {
    u64 d = x / p;
    pos = kissat_emit_byte(out, cap, pos, 48ULL + d);
    x = x - d * p;
    p = p / 10ULL;
  }
  return pos;
}

u64 kissat_emit_dimacs_lit(u64 out, u64 cap, u64 pos, u64 lit) {
  if ((lit & 1ULL) != 0ULL) {
    pos = kissat_emit_byte(out, cap, pos, 45ULL);
  }
  u64 v = (lit >> 1) + 1ULL;
  pos = kissat_emit_u64(out, cap, pos, v);
  pos = kissat_emit_byte(out, cap, pos, 32ULL);
  return pos;
}

u64 kissat_emit_dimacs_hdr(u64 out, u64 cap, u64 pos, u64 mv, u64 nc) {
  pos = kissat_emit_byte(out, cap, pos, 112ULL);
  pos = kissat_emit_byte(out, cap, pos, 32ULL);
  pos = kissat_emit_byte(out, cap, pos, 99ULL);
  pos = kissat_emit_byte(out, cap, pos, 110ULL);
  pos = kissat_emit_byte(out, cap, pos, 102ULL);
  pos = kissat_emit_byte(out, cap, pos, 32ULL);
  pos = kissat_emit_u64(out, cap, pos, mv);
  pos = kissat_emit_byte(out, cap, pos, 32ULL);
  pos = kissat_emit_u64(out, cap, pos, nc);
  pos = kissat_emit_byte(out, cap, pos, 10ULL);
  return pos;
}
"

/-- Zero-exit, zero-extern acyclic `Module` packaging all four ASCII DIMACS formatter helpers. -/
def exportCnfFmtMod : LeanQbe.T.Module :=
  { fns := exportCnfFmt_fns, externs := [], exits := [] }

end

/-! ## Well-Formedness and Structural Certificates (`Func.Wf`, Acyclicity, Arity) -/

public section

theorem kissat_emit_byte_wf : Func.Wf kissat_emit_byte_body := by
  t_wf_tac

theorem kissat_emit_u64_wf : Func.Wf kissat_emit_u64_body := by
  t_wf_tac

theorem kissat_emit_dimacs_lit_wf : Func.Wf kissat_emit_dimacs_lit_body := by
  t_wf_tac

theorem kissat_emit_dimacs_hdr_wf : Func.Wf kissat_emit_dimacs_hdr_body := by
  t_wf_tac

/-- All four functions in `exportCnfFmt_fns` satisfy `Fn.Wf`. -/
theorem exportCnfFmt_fns_wf : ∀ f ∈ exportCnfFmt_fns, f.Wf := by
  intro f hf
  simp only [exportCnfFmt_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact kissat_emit_byte_wf
  · exact kissat_emit_u64_wf
  · exact kissat_emit_dimacs_lit_wf
  · exact kissat_emit_dimacs_hdr_wf

/-- Acyclicity certificate for `exportCnfFmtMod`. -/
theorem exportCnfFmtMod_checkAcyclic : exportCnfFmtMod.checkAcyclic = true := by
  decide

/-- Unique function-name certificate for `exportCnfFmtMod`. -/
theorem exportCnfFmtMod_namesNodup : exportCnfFmtMod.namesNodup := by
  simp only [Module.namesNodup, Module.names, exportCnfFmtMod, exportCnfFmt_fns]
  decide

/-- Every function in `exportCnfFmt_fns` takes at most 6 scalar arguments (x64 & Arm64 ABI). -/
theorem exportCnfFmt_fns_max6args : ∀ f ∈ exportCnfFmt_fns, f.as.length ≤ 6 := by
  intro f hf
  simp only [exportCnfFmt_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> decide

end

end LeanQbe.T.Examples.Kissat.ExportCnfFmt
