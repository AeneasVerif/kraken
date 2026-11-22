module

public import LeanQbe.T.Examples.Kissat.FullM6SatSound
public import LeanQbe.T.Examples.Kissat.FullM6SatNv
import LeanQbe.T.Examples.Kissat.FullM6Hdr
import LeanQbe.T.Examples.Kissat.FullProof

/-!
# Kissat `D-Full` M6 End-to-End UNSAT+SAT Soundness & Concrete Non-Vacuity Tests

Standalone test suite verifying:
1. Concrete kernel checks (`decide` / `rfl`) on `nvM6Mem`, `M6Hdr`'s `3,456 B` prefix layout
   (`fullM6WorkBase`, `fullM6WorkHdr`, `fullM6ValuesFieldPtr`), `fullM6HdrMagic`, and
   `readModelFromWorkM6`.
2. Direct instantiation of generic `FullM6` combinators (`fullM6_solve_bytes_sound_combinator`,
   `fullM6_solve_bytes_moduleOk_combinator`, `fullM6_respec_tail_moduleOk`,
   `fullM6_host_sound_lift`).
3. Concrete Tier-3b non-vacuity witnesses (`fullM6_unsat_nv`, `fullM6_sat_nv`, `nvM6Mem_sat`,
   `nvM6_unsat_full_m6_mem_init`, `nvM6_sat_full_m6_mem_init`, `nvM6_unsat_init_parse_wp`,
   `nvM6_sat_checkModel_wp`, `nvM6_sat_extend_check_wp`).
4. Single-line `#print axioms` checks strictly within `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.KissatM6SatSoundTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6

example : fullM6ExtBytes = 2304 := by decide
example : fullM6HdrTotalBytes = 3456 := by decide
example : nvM6UnsatBytes.length = 19 := by decide
example : nvM6SatBytes.length = 16 := by decide
example : fullAlignPad nvM6UnsatWorkPtr = 5 := by decide
example : fullAlignPad nvM6SatWorkPtr = 0 := by decide
example : fullM6WorkBase nvM6UnsatWorkPtr = nvM6UnsatWorkPtr + 5#64 := by decide
example : fullM6WorkHdr nvM6UnsatWorkPtr = nvM6UnsatWorkPtr + 2309#64 := by decide
example : fullM6WorkBase nvM6SatWorkPtr = nvM6SatWorkPtr := by decide
example : fullM6WorkHdr nvM6SatWorkPtr = nvM6SatWorkPtr + 2304#64 := by decide
example : fullM6ValuesFieldPtr nvM6SatWorkPtr = nvM6SatWorkPtr + 2368#64 := by decide
example : nvM6SatCfg.hdr = fullM6WorkHdr nvM6SatWorkPtr := rfl
example : nvM6SatCfg.avail = 5888 := rfl
example : nvM6ExtInitWords.length = 288 := nvM6ExtInitWords_len
example : nvM6ExtInitWords[0]? = some fullM6HdrMagic := rfl
example : nvM6SatState.core.vals = [1#8, 0xFF#8, 1#8, 0xFF#8] := rfl
example : parseDimacs nvM6UnsatBytes = some nvM6UnsatCnf := parseDimacs_nvM6UnsatBytes
example : parseDimacs nvM6SatBytes = some nvM6SatCnf := parseDimacs_nvM6SatBytes

theorem t_read_1 : readModelFromWorkM6 nvM6Mem nvM6SatWorkPtr 1 = true :=
  nvM6Mem_readModel_1

theorem t_read_2 : readModelFromWorkM6 nvM6Mem nvM6SatWorkPtr 2 = true :=
  nvM6Mem_readModel_2

theorem t_read_0 : readModelFromWorkM6 nvM6Mem nvM6SatWorkPtr 0 = false :=
  readModelFromWorkM6_zero nvM6Mem nvM6SatWorkPtr

theorem t_read_eq (m' : Mem 64) (w : BitVec 64) (v : Nat) :
    readModelFromWorkM6 m' w v =
      if (v == 0) = true then false
      else
        match loadVal m' i64 (fullM6ValuesFieldPtr w) with
        | none => false
        | some vals_ptr =>
          match loadVal m' i8 (vals_ptr + BitVec.ofNat 64 (2 * (v - 1))) with
          | none => false
          | some b => i8BytePos { toBitVec := b } :=
  readModelFromWorkM6_eq m' w v

theorem t_comb (Γ : Env) (solveBody : Func [i64, i64, i64, i64, i64] [i64])
    (hwp : ∀ a m Q X,
      fullM6SolveBytesSpec a m Q X → Func.wp Γ solveBody a m Q X)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp Γ solveBody
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ())
      m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M : Mem 64),
              (Eq m' ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fullM6_solve_bytes_sound_combinator Γ solveBody hwp hcfit hwfit hm

theorem t_modok (Γ : Env) (m6Mod : Module) (fnName : Sym)
    (fnBody : Func [i64, i64, i64, i64, i64] [i64])
    (hmod : ModuleOk Γ m6Mod)
    (hmem : (⟨fnName, [i64, i64, i64, i64, i64], [i64], fnBody⟩ : Fn) ∈ m6Mod.fns)
    (hspec : ∀ a m Q X,
      fullM6SolveBytesSpec a m Q X →
      Γ fnName [i64, i64, i64, i64, i64] [i64] a m Q X)
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp Γ fnBody
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ())
      m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
            ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
            ∀ (F : Mem 64 → Prop) (M' : Mem 64),
              (Eq m' ⋆ F) M' → cnf.Sat (readModelFromWorkM6 M' work_ptr)) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) :=
  fullM6_solve_bytes_moduleOk_combinator Γ m6Mod fnName fnBody hmod hmem hspec hcfit hwfit hm

theorem t_respec {Γ₀ Γ₁ : Env} {m6Mod : Module} {pfx tail : List Fn}
    (hmod : ModuleOk Γ₀ m6Mod) (hsplit : m6Mod.fns = pfx ++ tail)
    (hpfx : ∀ f as bs, (f, as, bs) ∈ pfx.map Fn.sig ++ m6Mod.externs.map Extern.sig →
      ∀ xs m Q X, Γ₀ f as bs xs m Q X ↔ Γ₁ f as bs xs m Q X)
    (htail : ∀ fn ∈ tail, ∀ xs m Q X,
      Γ₁ fn.name fn.as fn.rs xs m Q X → Func.wp Γ₁ fn.body xs m Q X) :
    ModuleOk Γ₁ m6Mod :=
  fullM6_respec_tail_moduleOk hmod hsplit hpfx htail

theorem t_host {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hq :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        ∀ (F : Mem 64 → Prop) (M : Mem 64),
          (Eq m' ⋆ F) M → cnf.Sat (readModelFromWorkM6 M work_ptr)) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hdmem : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
      ¬ cnf.Unsat ∧ (∃ β, cnf.Sat β) ∧
      cnf.Sat (readModelFromWorkM6 st_dmem work_ptr)) ∧
    ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) ⋆ F_host) st_dmem :=
  fullM6_host_sound_lift hq hdmem

theorem t_ext_chk :
    Func.wp (FullM5.mkM5Env fullSolveBytesSpec) full_extend_body
      (nvM6SatCfg.hdr, ()) nvM6Mem
      (fun _ m1 =>
        Func.wp (FullM5.mkM5Env fullSolveBytesSpec) kissat_check_model_body
          (nvM6CnfPtr, nvM6CnfPtr + BitVec.ofNat 64 nvM6SatBytes.length,
            nvM6SatCfg.hdr, nvM6SatCfg.pVals, BitVec.ofNat 64 nvM6SatCfg.mv, ()) m1
          (fun rs2 m2 =>
            match rs2 with
            | (ok, ()) =>
              ((if ok == 1#64 then 10#64 else 0#64) = 10#64 ∧
                nvM6SatCnf.Sat (readModelFromWorkM6 m2 nvM6SatWorkPtr) ∧
                (bytes nvM6CnfPtr nvM6SatBytes ⋆ region nvM6SatWorkPtr nvM6WorkLen) m2) ∨
              (if ok == 1#64 then 10#64 else 0#64) ≠ 10#64)
          (fun _ _ _ _ => False))
      (fun _ _ _ _ => False) :=
  nvM6_sat_extend_check_wp

theorem t_nv_unsat (Γ : Env) (solveBody : Func [i64, i64, i64, i64, i64] [i64])
    (hwp : ∀ a m Q X,
      fullM6SolveBytesCoreModelSpec a m Q X → Func.wp Γ solveBody a m Q X) :
    Func.wp Γ solveBody
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fullM6_unsat_nv Γ solveBody hwp

theorem t_nv_sat (Γ : Env) (solveBody : Func [i64, i64, i64, i64, i64] [i64])
    (hwp : ∀ a m Q X,
      fullM6SolveBytesSpec a m Q X → Func.wp Γ solveBody a m Q X) :
    Func.wp Γ solveBody
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6SatBytes.length,
        nvM6SatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6SatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64) ∧ r ≠ 20#64 ∧
          (r = 10#64 →
            ¬ nvM6SatCnf.Unsat ∧
            (∀ (F : Mem 64 → Prop) (M : Mem 64),
              (Eq m' ⋆ F) M → nvM6SatCnf.Sat (readModelFromWorkM6 M nvM6SatWorkPtr))) ∧
          (bytes nvM6CnfPtr nvM6SatBytes ⋆ region nvM6SatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  fullM6_sat_nv Γ solveBody hwp

theorem t_init_u :
    nvM6UnsatCnf.Unsat ∧
    (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) nvM6UnsatInitMem :=
  ⟨nvM6UnsatCnf_unsat, nvM6UnsatInitMem_sep⟩

theorem t_init_s :
    nvM6SatCnf.Sat (readModelFromWorkM6 nvM6Mem nvM6SatWorkPtr) ∧
    (bytes nvM6CnfPtr nvM6SatBytes ⋆ region nvM6SatWorkPtr nvM6WorkLen) nvM6Mem :=
  ⟨nvM6Mem_sat, nvM6Mem_region⟩

theorem t_chk_wp :
    Func.wp dimacsExactEnv kissat_check_model_body
      (nvM6CnfPtr, nvM6CnfPtr + BitVec.ofNat 64 nvM6SatBytes.length,
        nvM6SatCfg.hdr, nvM6SatCfg.pVals, BitVec.ofNat 64 nvM6SatCfg.mv, ())
      nvM6Mem
      (fun rs m' =>
        match rs with
        | (ok, ()) =>
          ok = 1#64 ∧
          nvM6SatCnf.Sat (readModelFromWorkM6 m' nvM6SatWorkPtr) ∧
          (bytes nvM6CnfPtr nvM6SatBytes ⋆ region nvM6SatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) :=
  nvM6_sat_checkModel_wp

theorem t_m6_u :
    Func.wp nvM6NvEnv full_m6_mem_init_body
      (nvM6CnfPtr, nvM6CnfPtr + BitVec.ofNat 64 nvM6UnsatBytes.length,
        fullM6WorkBase nvM6UnsatWorkPtr,
        BitVec.ofNat 64 (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr), 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (hdr, ()) =>
          ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState),
            hdr = c.hdr ∧ c.hdr = fullM6WorkHdr nvM6UnsatWorkPtr ∧
            c.avail = nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr - fullM6ExtBytes ∧
            c.mv = 1 ∧ c.nc = 2 ∧
            FullM6HdrCfgOk c ∧ M6HdrExtInitOk ext ∧
            FullM6HdrInv c (shiftDownCnf CNF.empty) ext s ∧
            s.core.cur_vars = c.mv ∧
            s.core.d_cur = nvM6CnfPtr + 9#64 ∧
            s.core.arena_len = 0 ∧ s.core.wlen = 1 ∧ s.core.trail_end = 0 ∧
            s.core.propagated = 0 ∧ s.core.cur_level = 0 ∧ s.core.fuel = 16#64 ∧
            s.core.oom = 0#64 ∧ s.core.inconsistent = 0#64 ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ FullM6HdrMem c ext s ⋆
              region nvM6UnsatWorkPtr (fullAlignPad nvM6UnsatWorkPtr)) m')
      (fun _ _ _ _ => False) :=
  nvM6_unsat_full_m6_mem_init

theorem t_m6_s :
    Func.wp nvM6NvEnv full_m6_mem_init_body
      (nvM6CnfPtr, nvM6CnfPtr + BitVec.ofNat 64 nvM6SatBytes.length,
        fullM6WorkBase nvM6SatWorkPtr,
        BitVec.ofNat 64 (nvM6WorkLen - fullAlignPad nvM6SatWorkPtr), 16#64, ())
      nvM6SatInitMem
      (fun rs m' =>
        match rs with
        | (hdr, ()) =>
          ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState),
            hdr = c.hdr ∧ c.hdr = fullM6WorkHdr nvM6SatWorkPtr ∧
            c.avail = nvM6WorkLen - fullAlignPad nvM6SatWorkPtr - fullM6ExtBytes ∧
            c.mv = 2 ∧ c.nc = 1 ∧
            FullM6HdrCfgOk c ∧ M6HdrExtInitOk ext ∧
            FullM6HdrInv c (shiftDownCnf CNF.empty) ext s ∧
            s.core.cur_vars = c.mv ∧
            s.core.d_cur = nvM6CnfPtr + 9#64 ∧
            s.core.arena_len = 0 ∧ s.core.wlen = 1 ∧ s.core.trail_end = 0 ∧
            s.core.propagated = 0 ∧ s.core.cur_level = 0 ∧ s.core.fuel = 16#64 ∧
            s.core.oom = 0#64 ∧ s.core.inconsistent = 0#64 ∧
            (bytes nvM6CnfPtr nvM6SatBytes ⋆ FullM6HdrMem c ext s ⋆
              region nvM6SatWorkPtr (fullAlignPad nvM6SatWorkPtr)) m')
      (fun _ _ _ _ => False) :=
  nvM6_sat_full_m6_mem_init

theorem t_parse_u :
    Func.wp nvM6NvEnv full_init_state_body
      (nvM6CnfPtr, nvM6CnfPtr + BitVec.ofNat 64 nvM6UnsatBytes.length,
        fullM6WorkHdr nvM6UnsatWorkPtr,
        BitVec.ofNat 64 (nvM6WorkLen - fullAlignPad nvM6UnsatWorkPtr - fullM6ExtBytes),
        16#64, ())
      nvM6UnsatInitMem
      (fun rs m1 =>
        match rs with
        | (ok, ()) =>
          ok = true ∧
          Func.wp (FullM5.mkM5Env fullSolveBytesSpec) full_parse_body_body
            (fullM6WorkHdr nvM6UnsatWorkPtr,
              nvM6CnfPtr + BitVec.ofNat 64 nvM6UnsatBytes.length, ()) m1
            (fun rs2 m2 =>
              match rs2 with
              | (r, ()) =>
                r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
                (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
                  region nvM6UnsatWorkPtr nvM6WorkLen) m2)
            (fun _ _ _ _ => False))
      (fun _ _ _ _ => False) :=
  nvM6_unsat_init_parse_wp

#print axioms t_read_1
#print axioms t_read_2
#print axioms t_read_0
#print axioms t_read_eq
#print axioms t_comb
#print axioms t_modok
#print axioms t_respec
#print axioms t_host
#print axioms t_ext_chk
#print axioms t_nv_unsat
#print axioms t_nv_sat
#print axioms t_init_u
#print axioms t_init_s
#print axioms t_chk_wp
#print axioms t_m6_u
#print axioms t_m6_s
#print axioms t_parse_u

end LeanQbeTest.T.KissatM6SatSoundTest
