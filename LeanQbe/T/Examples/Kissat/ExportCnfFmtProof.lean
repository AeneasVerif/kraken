/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.ExportCnfFmt
public import LeanQbe.T.Examples.Kissat.Ref.Base
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Examples.LratBytesDimacsLemmas
public import LeanQbe.T.Logic.ByteArrayDecimal
public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.Rules
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0HeadStep
meta import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
meta import LeanQbe.T.Logic.ProofKit
import Kraken.Mem
import Kraken.Separation

/-!
# Verification and DIMACS Round-Trip Proofs for `ExportCnfFmt`

Proves:
1. Pure bounded byte-buffer model `writeSlice` and algebraic composition/fit/dry-run/truncation
   lemmas.
2. Exact agreement between `ByteArrayDecimal.digitsPow10`, `LratBytes.natToBytes`, and
   `(Nat.repr n).toUTF8.data.toList`, plus byte-length bounds (`<= 20` / `<= 22` / `<= 48`).
3. Pure DIMACS round-trip theorems connecting emitted Kissat CNF byte streams
   `emitDimacsBytes mv clauses` directly to `LratBytes.parseDimacs`:
   - `emitDimacsBytes_eq_encodeDimacs` & `parseDimacs_emitDimacsBytes_canonical`
     (reusing `LratBytes.parseDimacs_encodeDimacs` directly).
   - `parseDimacs_emitDimacsBytes` (for any declared `mv < dimacsBound` upper-bounding all
     variables in `clauses`, including empty CNFs, empty clauses `"p cnf 0 1\n0\n"`, and
     simplified formulas where `cnfMaxVar < mv`).
4. `XPost`-polymorphic separation-logic WP specifications and proofs for all four C0 helpers
   (`kissat_emit_byte_wp`, `kissat_emit_u64_wp`, `kissat_emit_dimacs_lit_wp`,
   `kissat_emit_dimacs_hdr_wp`), closed-module soundness (`exportCnfFmtEnv_sound`,
   `exportCnfFmtEnv_moduleOk`, `exportCnfFmtFns_sound_in`), and ergonomic full-write, dry-run
   (`cap = 0`, `m' = m`), and insufficient-capacity corollaries.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.ExportCnfFmt

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.ProofKit
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ByteArrayDecimal
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref

/-! ## 1. Pure Bounded Byte-Buffer Model and DIMACS Stream Specification -/

@[expose] public section

/-- Write `emitBs` sequentially into `buf` starting at offset `pos`, silently skipping any byte
whose offset is `≥ buf.length` (modeling bounds-checked buffer writes and dry-run counting). -/
def writeSlice (buf : List UInt8) (pos : Nat) : List UInt8 → List UInt8
  | [] => buf
  | b :: rest =>
    let buf' := if pos < buf.length then buf.set pos b else buf
    writeSlice buf' (pos + 1) rest

/-- Convert a 0-based Kissat literal (`2 * (v - 1)` positive, `2 * (v - 1) + 1` negative)
into a 1-based `Std.Sat.Literal Nat`. -/
@[inline] def kissatLitToDimacs (l : Nat) : Literal Nat :=
  (litVar l + 1, !(litSign l))

/-- Convert a Kissat literal list into a 1-based DIMACS `CNF.Clause Nat`. -/
def kissatClauseToDimacs (cl : List Nat) : CNF.Clause Nat :=
  CNF.Clause.ofLiterals (cl.map kissatLitToDimacs)

/-- Convert a list of Kissat clauses into a 1-based DIMACS `CNF Nat`. -/
def kissatCnfToDimacs (clauses : List (List Nat)) : CNF Nat :=
  ⟨(clauses.map kissatClauseToDimacs).toArray⟩

/-- Pure ASCII byte sequence emitted by `kissat_emit_dimacs_lit` for Kissat literal `lit`
(matches `LratBytes.encodeDimacsLit (kissatLitToDimacs lit)`). -/
def emitDimacsLitBytes (lit : Nat) : List UInt8 :=
  encodeDimacsLit (kissatLitToDimacs lit)

/-- Pure ASCII byte sequence emitted by `kissat_emit_dimacs_hdr` (`"p cnf <mv> <nc>\n"`). -/
def emitDimacsHdrBytes (mv nc : Nat) : List UInt8 :=
  dimacsHeaderPrefix ++ natToBytes mv ++ [asciiSpace] ++ natToBytes nc ++ [asciiNewline]

/-- Pure ASCII byte sequence for one `0\n`-terminated Kissat clause. -/
def emitDimacsClauseBytes (cl : List Nat) : List UInt8 :=
  (cl.flatMap emitDimacsLitBytes) ++ [asciiZero, asciiNewline]

/-- Pure ASCII DIMACS byte stream for header `(mv, clauses.length)` followed by all clauses. -/
def emitDimacsBytes (mv : Nat) (clauses : List (List Nat)) : List UInt8 :=
  emitDimacsHdrBytes mv clauses.length ++ clauses.flatMap emitDimacsClauseBytes

/-! ## 2. Separation-Logic `Spec` Contracts (`XPost`-Polymorphic) -/

/-- `XPost`-polymorphic WP contract for `kissat_emit_byte(out, cap, pos, b)`. -/
def kissatEmitByteSpec : Spec [i64, i64, i64, i64] [i64] := fun args m Q _ =>
  ∃ (out : BitVec 64) (buf : List UInt8) (pos : Nat) (b : BitVec 64) (R : Mem 64 → Prop),
    args = (out, BitVec.ofNat 64 buf.length, BitVec.ofNat 64 pos, b, ()) ∧
    buf.length < 2 ^ 64 ∧
    pos + 1 < 2 ^ 64 ∧
    (bytes out buf ⋆ R) m ∧
    ∀ m', (buf.length ≤ pos → m' = m) →
      (bytes out (writeSlice buf pos [UInt8.ofNat b.toNat]) ⋆ R) m' →
      Q (BitVec.ofNat 64 (pos + 1), ()) m'

/-- `XPost`-polymorphic WP contract for `kissat_emit_u64(out, cap, pos, x)`. -/
def kissatEmitU64Spec : Spec [i64, i64, i64, i64] [i64] := fun args m Q _ =>
  ∃ (out : BitVec 64) (buf : List UInt8) (pos : Nat) (x : BitVec 64) (R : Mem 64 → Prop),
    args = (out, BitVec.ofNat 64 buf.length, BitVec.ofNat 64 pos, x, ()) ∧
    buf.length < 2 ^ 64 ∧
    pos + (natToBytes x.toNat).length < 2 ^ 64 ∧
    (bytes out buf ⋆ R) m ∧
    ∀ m', (buf.length ≤ pos → m' = m) →
      (bytes out (writeSlice buf pos (natToBytes x.toNat)) ⋆ R) m' →
      Q (BitVec.ofNat 64 (pos + (natToBytes x.toNat).length), ()) m'

/-- `XPost`-polymorphic WP contract for `kissat_emit_dimacs_lit(out, cap, pos, lit)`. -/
def kissatEmitDimacsLitSpec : Spec [i64, i64, i64, i64] [i64] := fun args m Q _ =>
  ∃ (out : BitVec 64) (buf : List UInt8) (pos : Nat) (lit : BitVec 64) (R : Mem 64 → Prop),
    args = (out, BitVec.ofNat 64 buf.length, BitVec.ofNat 64 pos, lit, ()) ∧
    buf.length < 2 ^ 64 ∧
    pos + (emitDimacsLitBytes lit.toNat).length < 2 ^ 64 ∧
    (bytes out buf ⋆ R) m ∧
    ∀ m', (buf.length ≤ pos → m' = m) →
      (bytes out (writeSlice buf pos (emitDimacsLitBytes lit.toNat)) ⋆ R) m' →
      Q (BitVec.ofNat 64 (pos + (emitDimacsLitBytes lit.toNat).length), ()) m'

/-- `XPost`-polymorphic WP contract for `kissat_emit_dimacs_hdr(out, cap, pos, mv, nc)`. -/
def kissatEmitDimacsHdrSpec : Spec [i64, i64, i64, i64, i64] [i64] := fun args m Q _ =>
  ∃ (out : BitVec 64) (buf : List UInt8) (pos : Nat) (mv nc : BitVec 64) (R : Mem 64 → Prop),
    args = (out, BitVec.ofNat 64 buf.length, BitVec.ofNat 64 pos, mv, nc, ()) ∧
    buf.length < 2 ^ 64 ∧
    pos + (emitDimacsHdrBytes mv.toNat nc.toNat).length < 2 ^ 64 ∧
    (bytes out buf ⋆ R) m ∧
    ∀ m', (buf.length ≤ pos → m' = m) →
      (bytes out (writeSlice buf pos (emitDimacsHdrBytes mv.toNat nc.toNat)) ⋆ R) m' →
      Q (BitVec.ofNat 64 (pos + (emitDimacsHdrBytes mv.toNat nc.toNat).length), ()) m'

/-- Closed specification environment for `exportCnfFmtMod`. -/
def exportCnfFmtEnv : Env :=
  fun f as rs =>
    if h : f = "kissat_emit_byte" ∧ as = [i64, i64, i64, i64] ∧ rs = [i64] then
      h.2.1 ▸ h.2.2 ▸ kissatEmitByteSpec
    else if h : f = "kissat_emit_u64" ∧ as = [i64, i64, i64, i64] ∧ rs = [i64] then
      h.2.1 ▸ h.2.2 ▸ kissatEmitU64Spec
    else if h : f = "kissat_emit_dimacs_lit" ∧ as = [i64, i64, i64, i64] ∧ rs = [i64] then
      h.2.1 ▸ h.2.2 ▸ kissatEmitDimacsLitSpec
    else if h : f = "kissat_emit_dimacs_hdr" ∧ as = [i64, i64, i64, i64, i64] ∧ rs = [i64] then
      h.2.1 ▸ h.2.2 ▸ kissatEmitDimacsHdrSpec
    else
      fun _ _ _ _ => False

end

/-! ## 3. Pure `writeSlice`, Decimal, and DIMACS Round-Trip Lemmas -/

public section

theorem writeSlice_nil (buf : List UInt8) (pos : Nat) :
    writeSlice buf pos [] = buf := rfl

theorem writeSlice_cons (buf : List UInt8) (pos : Nat) (b : UInt8) (rest : List UInt8) :
    writeSlice buf pos (b :: rest) =
      writeSlice (if pos < buf.length then buf.set pos b else buf) (pos + 1) rest := rfl

theorem writeSlice_length (buf : List UInt8) (pos : Nat) (emitBs : List UInt8) :
    (writeSlice buf pos emitBs).length = buf.length := by
  induction emitBs generalizing buf pos with
  | nil => rfl
  | cons b rest ih =>
    rw [writeSlice_cons, ih]
    split <;> simp

theorem writeSlice_append (buf : List UInt8) (pos : Nat) (bs1 bs2 : List UInt8) :
    writeSlice buf pos (bs1 ++ bs2) =
      writeSlice (writeSlice buf pos bs1) (pos + bs1.length) bs2 := by
  induction bs1 generalizing buf pos with
  | nil => simp [writeSlice_nil]
  | cons b rest ih =>
    simp only [List.cons_append, writeSlice_cons, List.length_cons]
    rw [ih, show pos + 1 + rest.length = pos + (rest.length + 1) by omega]

theorem writeSlice_of_le (buf : List UInt8) {pos : Nat} (hge : buf.length ≤ pos)
    (emitBs : List UInt8) :
    writeSlice buf pos emitBs = buf := by
  induction emitBs generalizing pos with
  | nil => rfl
  | cons b rest ih =>
    rw [writeSlice_cons, ite_eq_right (by omega)]
    exact ih (by omega)

theorem writeSlice_nil_buf (pos : Nat) (emitBs : List UInt8) :
    writeSlice [] pos emitBs = [] :=
  writeSlice_of_le [] (Nat.zero_le pos) emitBs

theorem writeSlice_fit (buf : List UInt8) (pos : Nat) (emitBs : List UInt8)
    (hfit : pos + emitBs.length ≤ buf.length) :
    writeSlice buf pos emitBs = buf.take pos ++ emitBs ++ buf.drop (pos + emitBs.length) := by
  induction emitBs generalizing buf pos with
  | nil =>
    simp only [writeSlice_nil, List.append_nil, List.length_nil, Nat.add_zero]
    exact (List.take_append_drop pos buf).symm
  | cons b rest ih =>
    have hlt : pos < buf.length := by simp at hfit; omega
    have hfit' : (pos + 1) + rest.length ≤ (buf.set pos b).length := by
      simp at hfit ⊢; omega
    rw [writeSlice_cons, ite_eq_left hlt, ih (buf.set pos b) (pos + 1) hfit']
    have htake : (buf.set pos b).take (pos + 1) = buf.take pos ++ [b] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simp [hlt]), List.getElem_set_self,
        List.take_set_of_le (Nat.le_refl pos)]
      simp
    have hdrop : (buf.set pos b).drop (pos + 1 + rest.length) =
        buf.drop (pos + (rest.length + 1)) := by
      rw [show pos + 1 + rest.length = pos + (rest.length + 1) by omega]
      exact List.drop_set_of_lt (by omega)
    rw [htake, hdrop, List.length_cons]
    simp [List.append_assoc]

theorem writeSlice_getElem?_lt (buf : List UInt8) (pos : Nat) (emitBs : List UInt8)
    {i : Nat} (hi : i < pos) :
    (writeSlice buf pos emitBs)[i]? = buf[i]? := by
  induction emitBs generalizing buf pos with
  | nil => rfl
  | cons b rest ih =>
    rw [writeSlice_cons, ih _ _ (by omega)]
    split
    · exact List.getElem?_set_ne (by omega)
    · rfl

private theorem natToBytesAux_succ_eq (fuel n : Nat) (acc : List UInt8) :
    natToBytesAux (fuel + 1) n acc =
      if n < 10 then UInt8.ofNat (48 + n % 10) :: acc
      else natToBytesAux fuel (n / 10) (UInt8.ofNat (48 + n % 10) :: acc) := rfl

private theorem natToBytesAux_acc_eq (fuel n : Nat) (acc : List UInt8) :
    natToBytesAux fuel n acc = natToBytesAux fuel n [] ++ acc := by
  induction fuel generalizing n acc with
  | zero => simp [natToBytesAux]
  | succ fuel ih =>
    rw [natToBytesAux_succ_eq, natToBytesAux_succ_eq]
    by_cases h : n < 10
    · simp [h]
    · simp only [h, ↓reduceIte]
      rw [ih, ih (acc := [UInt8.ofNat (48 + n % 10)]), List.append_assoc]
      rfl

private theorem natToBytesAux_fuel_eq {f1 f2 n : Nat} (acc : List UInt8)
    (h1 : n < f1) (h2 : n < f2) : natToBytesAux f1 n acc = natToBytesAux f2 n acc := by
  induction f1 generalizing f2 n acc with
  | zero => omega
  | succ f1 ih =>
    cases f2 with
    | zero => omega
    | succ f2 =>
      rw [natToBytesAux_succ_eq, natToBytesAux_succ_eq]
      by_cases h : n < 10
      · simp [h]
      · simp only [h, ↓reduceIte]
        exact ih _ (by omega) (by omega)

theorem natToBytes_of_lt_10 {n : Nat} (h : n < 10) :
    natToBytes n = [UInt8.ofNat (48 + n)] := by
  unfold natToBytes
  rw [natToBytesAux_succ_eq]
  simp only [h, ↓reduceIte, Nat.mod_eq_of_lt h]

theorem natToBytes_of_ge_10 {n : Nat} (h : 10 ≤ n) :
    natToBytes n = natToBytes (n / 10) ++ [UInt8.ofNat (48 + n % 10)] := by
  unfold natToBytes
  conv => lhs; rw [natToBytesAux_succ_eq]
  simp only [show ¬ n < 10 by omega, ↓reduceIte]
  rw [natToBytesAux_acc_eq, natToBytesAux_fuel_eq (f2 := n / 10 + 1) [] (by omega) (by omega)]

/-- `ByteArrayDecimal.digitsPow10` agrees identically with `LratBytes.natToBytes`. -/
theorem digitsPow10_eq_natToBytes :
    ∀ (k m : Nat), (k = 0 ∨ 10 ^ k ≤ m) → m < 10 ^ (k + 1) →
      digitsPow10 k m = natToBytes m
  | 0, m, _, hm => by
    have hm10 : m < 10 := by simpa using hm
    rw [natToBytes_of_lt_10 hm10]; rfl
  | k + 1, m, hlow, hm => by
    have hge_pow : 10 ^ (k + 1) ≤ m := hlow.resolve_left (Nat.succ_ne_zero k)
    have h10 : 10 ≤ 10 ^ (k + 1) :=
      Nat.le_trans (by decide : 10 ≤ 10 ^ 1) (Nat.pow_le_pow_right (by omega) (by omega))
    have hge10 : 10 ≤ m := by omega
    have hdiv_lt : m / 10 < 10 ^ (k + 1) := by
      rw [Nat.div_lt_iff_lt_mul (by omega), ← Nat.pow_succ]; exact hm
    have hdiv_low : k = 0 ∨ 10 ^ k ≤ m / 10 :=
      Or.inr ((Nat.le_div_iff_mul_le (by omega)).mpr (by rw [← Nat.pow_succ]; exact hge_pow))
    rw [digitsPow10_succ_right, digitsPow10_eq_natToBytes k (m / 10) hdiv_low hdiv_lt,
      natToBytes_of_ge_10 hge10]

theorem digitsPow10_length (k m : Nat) : (digitsPow10 k m).length = k + 1 := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih => simp [digitsPow10, ih]

private theorem exists_pow10_bounds (n : Nat) :
    ∃ k, (k = 0 ∨ 10 ^ k ≤ n) ∧ n < 10 ^ (k + 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 10
    · exact ⟨0, Or.inl rfl, by simpa using h⟩
    · obtain ⟨k, hlow, hlt⟩ := ih (n / 10) (by omega)
      refine ⟨k + 1, Or.inr ?_, ?_⟩
      · cases hlow with
        | inl hk0 => subst hk0; simp; omega
        | inr hle => rw [Nat.pow_succ]; omega
      · rw [Nat.pow_succ]; omega

/-- `LratBytes.natToBytes n` matches Lean's standard `(Nat.repr n).toUTF8.data.toList`
(bridging `LratBytes` and `ByteArrayDecimal`). -/
theorem natToBytes_eq_natRepr_toUTF8 (n : Nat) :
    natToBytes n = (Nat.repr n).toUTF8.data.toList := by
  obtain ⟨k, hlow, hlt⟩ := exists_pow10_bounds n
  rw [← digitsPow10_eq_natToBytes k n hlow hlt, digitsPow10_eq_natRepr k n hlow hlt]

theorem natToBytes_length_le_of_lt {n k : Nat} (h : n < 10 ^ (k + 1)) :
    (natToBytes n).length ≤ k + 1 := by
  induction k generalizing n with
  | zero =>
    have h10 : n < 10 := by simpa using h
    rw [natToBytes_of_lt_10 h10]; simp
  | succ k ih =>
    by_cases h10 : n < 10
    · rw [natToBytes_of_lt_10 h10]; simp
    · rw [natToBytes_of_ge_10 (by omega), List.length_append, List.length_singleton]
      have hd : n / 10 < 10 ^ (k + 1) := by
        rw [Nat.div_lt_iff_lt_mul (by omega), ← Nat.pow_succ]; exact h
      have := ih hd
      omega

theorem natToBytes_length_le_20 {n : Nat} (hn : n < 2 ^ 64) :
    (natToBytes n).length ≤ 20 :=
  natToBytes_length_le_of_lt (k := 19) (Nat.lt_trans hn (by decide : 2 ^ 64 < 10 ^ 20))

theorem emitDimacsLitBytes_length_le_22 {lit : Nat} (hlit : lit < 2 ^ 64) :
    (emitDimacsLitBytes lit).length ≤ 22 := by
  unfold emitDimacsLitBytes encodeDimacsLit kissatLitToDimacs litVar litSign
  have hv : lit / 2 + 1 < 2 ^ 64 := by omega
  have hl := natToBytes_length_le_20 hv
  cases (lit % 2 == 1) <;> simp <;> omega

theorem emitDimacsHdrBytes_length_le_48 {mv nc : Nat} (hmv : mv < 2 ^ 64) (hnc : nc < 2 ^ 64) :
    (emitDimacsHdrBytes mv nc).length ≤ 48 := by
  unfold emitDimacsHdrBytes dimacsHeaderPrefix
  have h1 := natToBytes_length_le_20 hmv
  have h2 := natToBytes_length_le_20 hnc
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

theorem emitDimacsClauseBytes_eq_encodeDimacsClause (cl : List Nat) :
    emitDimacsClauseBytes cl = encodeDimacsClause (kissatClauseToDimacs cl) := by
  unfold emitDimacsClauseBytes encodeDimacsClause kissatClauseToDimacs emitDimacsLitBytes
  rw [CNF.Clause.literals_ofLiterals, List.flatMap_map]

theorem emitDimacsBytes_eq_encodeDimacs {mv : Nat} {clauses : List (List Nat)}
    (hmv : mv = cnfMaxVar (kissatCnfToDimacs clauses)) :
    emitDimacsBytes mv clauses = encodeDimacs (kissatCnfToDimacs clauses) := by
  rw [hmv]
  unfold emitDimacsBytes emitDimacsHdrBytes encodeDimacs
  have hsz : (kissatCnfToDimacs clauses).clauses.size = clauses.length := by
    simp [kissatCnfToDimacs]
  have htl : (kissatCnfToDimacs clauses).clauses.toList = clauses.map kissatClauseToDimacs := by
    simp [kissatCnfToDimacs]
  rw [hsz, htl, List.flatMap_map]
  simp only [List.append_assoc]
  have hfn : emitDimacsClauseBytes =
      (fun cl => encodeDimacsClause (kissatClauseToDimacs cl)) :=
    funext emitDimacsClauseBytes_eq_encodeDimacsClause
  rw [hfn]

private theorem foldl_max_le_bound {α : Type} {f : α → Nat} {xs : List α} {m0 B : Nat}
    (hm0 : m0 ≤ B) (hxs : ∀ x ∈ xs, f x ≤ B) :
    xs.foldl (fun m x => Nat.max m (f x)) m0 ≤ B := by
  induction xs generalizing m0 with
  | nil => exact hm0
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (Nat.max_le.mpr ⟨hm0, hxs x (by simp)⟩) (fun y hy => hxs y (by simp [hy]))

theorem cnfMaxVar_kissatCnfToDimacs_le {mv : Nat} {clauses : List (List Nat)}
    (hvars : ∀ cl ∈ clauses, ∀ l ∈ cl, litVar l < mv) :
    cnfMaxVar (kissatCnfToDimacs clauses) ≤ mv := by
  unfold cnfMaxVar
  rw [← Array.foldl_toList]
  have htl : (kissatCnfToDimacs clauses).clauses.toList = clauses.map kissatClauseToDimacs := by
    simp [kissatCnfToDimacs]
  rw [htl, List.foldl_map]
  suffices ∀ (cls : List (List Nat)) (m0 : Nat),
      m0 ≤ mv → (∀ cl ∈ cls, ∀ l ∈ cl, litVar l < mv) →
      cls.foldl (fun m cl => (kissatClauseToDimacs cl).literals.foldl
        (fun m' l => Nat.max m' l.1) m) m0 ≤ mv from
    this clauses 0 (Nat.zero_le mv) hvars
  intro cls
  induction cls with
  | nil => intro m0 hm0 _; exact hm0
  | cons cl cls ih =>
    intro m0 hm0 hcl
    simp only [List.foldl_cons]
    refine ih _ ?_ (fun c hc => hcl c (by simp [hc]))
    unfold kissatClauseToDimacs
    rw [CNF.Clause.literals_ofLiterals, List.foldl_map]
    exact foldl_max_le_bound hm0 (fun l hl => by
      have := hcl cl (by simp) l hl
      unfold kissatLitToDimacs; omega)

theorem kissatCnfToDimacs_validDimacs {mv : Nat} {clauses : List (List Nat)}
    (hmv : mv < dimacsBound) (hnc : clauses.length < dimacsBound)
    (hvars : ∀ cl ∈ clauses, ∀ l ∈ cl, litVar l < mv) :
    ValidDimacsCnf (kissatCnfToDimacs clauses) := by
  refine ⟨Nat.lt_of_le_of_lt (cnfMaxVar_kissatCnfToDimacs_le hvars) hmv, ?_, ?_⟩
  · simp [kissatCnfToDimacs, hnc]
  · intro cl hcl l hl
    have htl : (kissatCnfToDimacs clauses).clauses.toList = clauses.map kissatClauseToDimacs := by
      simp [kissatCnfToDimacs]
    rw [htl, List.mem_map] at hcl
    obtain ⟨kcl, _, rfl⟩ := hcl
    unfold kissatClauseToDimacs at hl
    rw [CNF.Clause.literals_ofLiterals, List.mem_map] at hl
    obtain ⟨kl, _, rfl⟩ := hl
    unfold kissatLitToDimacs
    omega

/-- Canonical DIMACS round-trip when header `mv = cnfMaxVar (kissatCnfToDimacs clauses)`,
directly reusing `LratBytes.parseDimacs_encodeDimacs`. -/
theorem parseDimacs_emitDimacsBytes_canonical {clauses : List (List Nat)}
    (hmv : cnfMaxVar (kissatCnfToDimacs clauses) < dimacsBound)
    (hnc : clauses.length < dimacsBound) :
    parseDimacs (emitDimacsBytes (cnfMaxVar (kissatCnfToDimacs clauses)) clauses) =
      some (kissatCnfToDimacs clauses) := by
  rw [emitDimacsBytes_eq_encodeDimacs rfl]
  refine parseDimacs_encodeDimacs ⟨hmv, by simp [kissatCnfToDimacs, hnc], ?_⟩
  intro cl hcl l hl
  have htl : (kissatCnfToDimacs clauses).clauses.toList = clauses.map kissatClauseToDimacs := by
    simp [kissatCnfToDimacs]
  rw [htl, List.mem_map] at hcl
  obtain ⟨kcl, _, rfl⟩ := hcl
  unfold kissatClauseToDimacs at hl
  rw [CNF.Clause.literals_ofLiterals, List.mem_map] at hl
  obtain ⟨kl, _, rfl⟩ := hl
  unfold kissatLitToDimacs
  omega

/-! ### General `mv ≥ cnfMaxVar` Round-Trip (`parseDimacs_emitDimacsBytes`) -/

private theorem digit_u8_toNat {d : Nat} (hd : d < 10) : (UInt8.ofNat (48 + d)).toNat = 48 + d := by
  simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega : 48 + d < 256)]

private theorem isDimacsDigit_u8 {d : Nat} (hd : d < 10) :
    isDimacsDigit (UInt8.ofNat (48 + d)) = true := by
  unfold isDimacsDigit; grind

private theorem isDimacsWs_of_isDigit {b : UInt8} (hd : isDimacsDigit b = true) :
    isDimacsWs b = false := by
  unfold isDimacsDigit at hd; unfold isDimacsWs; grind

private theorem isDimacsDigit_of_isWs {b : UInt8} (hw : isDimacsWs b = true) :
    isDimacsDigit b = false := by
  cases hd : isDimacsDigit b
  · rfl
  · simp [isDimacsWs_of_isDigit hd] at hw

private theorem natToBytes_nonempty_digits (n : Nat) :
    natToBytes n ≠ [] ∧ ∀ b ∈ natToBytes n, isDimacsDigit b = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 10
    · rw [natToBytes_of_lt_10 h]
      exact ⟨by simp, fun b hb => by rw [List.mem_singleton.mp hb]; exact isDimacsDigit_u8 h⟩
    · rw [natToBytes_of_ge_10 (by omega)]
      obtain ⟨_, hdig⟩ := ih (n / 10) (by omega)
      refine ⟨by simp, fun b hb => ?_⟩
      rcases List.mem_append.mp hb with hb | hb
      · exact hdig b hb
      · rw [List.mem_singleton.mp hb]; exact isDimacsDigit_u8 (by omega)

private theorem skipWs_natToBytes (n : Nat) (tail : List UInt8) :
    skipWs (natToBytes n ++ tail) = natToBytes n ++ tail := by
  obtain ⟨hne, hdig⟩ := natToBytes_nonempty_digits n
  rcases h : natToBytes n with _ | ⟨b, bs⟩
  · exact absurd h hne
  · rw [List.cons_append, skipWs, isDimacsWs_of_isDigit (hdig b (by simp [h]))]; rfl

private theorem skipWsComments_natToBytes (n : Nat) (tail : List UInt8) :
    skipWsComments (natToBytes n ++ tail) = natToBytes n ++ tail := by
  obtain ⟨hne, hdig⟩ := natToBytes_nonempty_digits n
  rcases h : natToBytes n with _ | ⟨b, bs⟩
  · exact absurd h hne
  · have hb := hdig b (by simp [h])
    have hne99 : (b == 99) = false := by unfold isDimacsDigit at hb; grind
    rw [List.cons_append, skipWsComments, skipWsCommentsAux,
      isDimacsWs_of_isDigit hb, hne99]
    simp

private theorem parseNat_natToBytes_tail {n : Nat} (hn : n < dimacsBound) (tail : List UInt8) :
    parseNat (natToBytes n ++ tail) = parseDigitsAux n tail := by
  induction n using Nat.strongRecOn generalizing tail with
  | ind n ih =>
    by_cases h : n < 10
    · rw [natToBytes_of_lt_10 h, List.singleton_append, parseNat]
      simp only [isDimacsDigit_u8 h, ↓reduceIte, digit_u8_toNat h]
      congr 1; omega
    · rw [natToBytes_of_ge_10 (by omega), List.append_assoc, List.singleton_append,
        ih (n / 10) (by omega) (by omega)]
      have hd : n % 10 < 10 := by omega
      rw [parseDigitsAux]
      simp only [isDimacsDigit_u8 hd, ↓reduceIte, digit_u8_toNat hd]
      have hacc : n / 10 * 10 + (48 + n % 10 - 48) = n := by omega
      rw [hacc, ite_eq_left hn]

private theorem parseNat_natToBytes_ws_tail {n : Nat} {w : UInt8} {rest : List UInt8}
    (hn : n < dimacsBound) (hw : isDimacsWs w = true) :
    parseNat (natToBytes n ++ w :: rest) = some (n, w :: rest) := by
  rw [parseNat_natToBytes_tail hn, parseDigitsAux]
  simp [isDimacsDigit_of_isWs hw, hw]

private theorem parseHeader_emitDimacsHdrBytes {mv nc : Nat} {body : List UInt8}
    (hmv : mv < dimacsBound) (hnc : nc < dimacsBound) :
    parseHeader (emitDimacsHdrBytes mv nc ++ body) = some (mv, nc, 10 :: body) := by
  unfold emitDimacsHdrBytes parseHeader
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  let tail := natToBytes mv ++ 32 :: (natToBytes nc ++ 10 :: body)
  have hws2 : skipWs1 (32 :: tail) = some tail := by
    simp [tail, skipWs1, show isDimacsWs 32 = true by decide, skipWs_natToBytes]
  have hp1 := parseNat_natToBytes_ws_tail (rest := natToBytes nc ++ 10 :: body)
    hmv (by decide : isDimacsWs 32 = true)
  have hws3 : skipWs1 (32 :: (natToBytes nc ++ 10 :: body)) =
      some (natToBytes nc ++ 10 :: body) := by
    simp [skipWs1, show isDimacsWs 32 = true by decide, skipWs_natToBytes]
  have hp2 := parseNat_natToBytes_ws_tail (rest := body) hnc (by decide : isDimacsWs 10 = true)
  have hsw0 : skipWsComments (112 :: 32 :: 99 :: 110 :: 102 :: 32 :: tail) =
      112 :: 32 :: 99 :: 110 :: 102 :: 32 :: tail := rfl
  have hws1 : skipWs1 (32 :: 99 :: 110 :: 102 :: 32 :: tail) =
      some (99 :: 110 :: 102 :: 32 :: tail) := rfl
  dsimp only [tail] at hsw0 hws1 hws2
  simp [hsw0, hws1, hws2, hp1, hws3, hp2]

private theorem parseClauseAux_ws_step {fuel mv : Nat} {acc : List (Literal Nat)}
    {w : UInt8} {bs : List UInt8} (hw : isDimacsWs w = true) :
    parseClauseAux fuel mv acc (w :: bs) = parseClauseAux fuel mv acc bs := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have hsw : skipWsComments (w :: bs) = skipWsComments bs := by
      rw [skipWsComments, skipWsCommentsAux, hw]; simp; rfl
    unfold parseClauseAux
    rw [hsw]

private theorem parseClause_ws_step {mv : Nat} {w : UInt8} {bs : List UInt8}
    (hw : isDimacsWs w = true) : parseClause mv (w :: bs) = parseClause mv bs := by
  unfold parseClause
  rw [parseClauseAux_ws_step hw]
  exact parseClauseAux_fuel_irrel (by simp; omega) (by omega)

private theorem parseClauseAux_succ_eq_gen (fuel mv : Nat) (acc : List (Literal Nat))
    (bs : List UInt8) :
    parseClauseAux (fuel + 1) mv acc bs =
      match skipWsComments bs with
      | [] => none
      | 45 :: rest => match parseNat rest with
        | some (v, rest') =>
          if 1 ≤ v && v ≤ mv then parseClauseAux fuel mv ((v, false) :: acc) rest' else none
        | none => none
      | b :: rest => match parseNat (b :: rest) with
        | some (0, rest') => some (CNF.Clause.ofLiterals acc.reverse, rest')
        | some (v, rest') =>
          if 1 ≤ v && v ≤ mv then parseClauseAux fuel mv ((v, true) :: acc) rest' else none
        | none => none := rfl

private theorem parseClauseAux_succ_45_gen {fuel mv : Nat} {acc : List (Literal Nat)}
    {bs rest : List UInt8} (h : skipWsComments bs = 45 :: rest) :
    parseClauseAux (fuel + 1) mv acc bs =
      match parseNat rest with
      | some (v, rest') =>
        if 1 ≤ v && v ≤ mv then parseClauseAux fuel mv ((v, false) :: acc) rest' else none
      | none => none := by
  rw [parseClauseAux_succ_eq_gen, h]; rfl

private theorem parseClauseAux_succ_pos_gen {fuel mv : Nat} {acc : List (Literal Nat)}
    {b : UInt8} {bs rest : List UInt8} (h : skipWsComments bs = b :: rest) (hb : b ≠ 45) :
    parseClauseAux (fuel + 1) mv acc bs =
      match parseNat (b :: rest) with
      | some (0, rest') => some (CNF.Clause.ofLiterals acc.reverse, rest')
      | some (v, rest') =>
        if 1 ≤ v && v ≤ mv then parseClauseAux fuel mv ((v, true) :: acc) rest' else none
      | none => none := by
  rw [parseClauseAux_succ_eq_gen, h]; split
  · cases ‹_ = []›
  · exact absurd (List.cons.inj ‹_›).1 hb
  · cases ‹b :: rest = _ :: _›; rfl

private theorem parseClauseAux_encodeLits_gen {ls : List (Literal Nat)} {fuel mv : Nat}
    {acc : List (Literal Nat)} {rest : List UInt8}
    (hmv : mv < dimacsBound) (hls : ∀ l ∈ ls, 1 ≤ l.1 ∧ l.1 ≤ mv)
    (hfuel : (ls.flatMap encodeDimacsLit ++ ([asciiZero, asciiNewline] ++ rest)).length < fuel) :
    parseClauseAux fuel mv acc (ls.flatMap encodeDimacsLit ++ ([asciiZero, asciiNewline] ++ rest)) =
      some (CNF.Clause.ofLiterals (acc.reverse ++ ls), 10 :: rest) := by
  induction ls generalizing fuel acc with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [List.flatMap_nil, List.nil_append, List.cons_append, List.append_nil]
      rw [parseClauseAux_succ_pos_gen (h := rfl) (by decide)]; rfl
  | cons l ls ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨v, pol⟩ := l
      obtain ⟨hv1, hvm⟩ := hls (v, pol) (by simp)
      have hv_lt : v < dimacsBound := Nat.lt_of_le_of_lt hvm hmv
      have hls' : ∀ x ∈ ls, 1 ≤ x.1 ∧ x.1 ≤ mv := fun x hx => hls x (by simp [hx])
      let tail := ls.flatMap encodeDimacsLit ++ ([asciiZero, asciiNewline] ++ rest)
      have hne_v : 1 ≤ (natToBytes v).length := by
        obtain ⟨hne, _⟩ := natToBytes_nonempty_digits v
        cases h : natToBytes v with | nil => exact absurd h hne | cons _ _ => simp
      have hlen_lit : 2 ≤ (encodeDimacsLit (v, pol)).length := by
        unfold encodeDimacsLit; cases pol <;> simp <;> omega
      have hfuel' : tail.length < fuel := by
        simp only [List.flatMap_cons, List.length_append] at hfuel
        dsimp only [tail]; simp only [List.length_append] at hfuel ⊢; omega
      simp only [List.flatMap_cons, List.append_assoc]
      change parseClauseAux (fuel + 1) mv acc (encodeDimacsLit (v, pol) ++ tail) = _
      have hcond : (1 ≤ v && v ≤ mv) = true := by simp [hv1, hvm]
      have hpn := parseNat_natToBytes_ws_tail (rest := tail) hv_lt
        (by decide : isDimacsWs 32 = true)
      cases pol with
      | false =>
        rw [show encodeDimacsLit (v, false) ++ tail = 45 :: (natToBytes v ++ 32 :: tail) by
          simp [encodeDimacsLit], parseClauseAux_succ_45_gen rfl, hpn]
        simp only [hcond, ↓reduceIte]
        rw [parseClauseAux_ws_step (by decide : isDimacsWs 32 = true), ih hls' hfuel']
        simp [List.reverse_cons]
      | true =>
        rw [show encodeDimacsLit (v, true) ++ tail = natToBytes v ++ 32 :: tail by
          simp [encodeDimacsLit]]
        have hsw := skipWsComments_natToBytes v (32 :: tail)
        obtain ⟨hne, hdig⟩ := natToBytes_nonempty_digits v
        rcases hnb : natToBytes v with _ | ⟨b, bs_v⟩
        · exact absurd hnb hne
        · have hb := hdig b (by simp [hnb])
          have hb_ne45 : b ≠ 45 := by unfold isDimacsDigit at hb; grind
          rw [hnb, List.cons_append] at hsw hpn
          rw [List.cons_append, parseClauseAux_succ_pos_gen hsw hb_ne45, hpn]
          cases v with
          | zero => omega
          | succ k =>
            simp only [hcond, ↓reduceIte]
            rw [parseClauseAux_ws_step (by decide : isDimacsWs 32 = true), ih hls' hfuel']
            simp [List.reverse_cons]

private theorem parseClauses_encodeDimacsClauses_gen {mv : Nat} {cls : List (CNF.Clause Nat)}
    (accCnf : CNF Nat) (hmv : mv < dimacsBound)
    (hcls : ∀ cl ∈ cls, ∀ l ∈ cl.literals, 1 ≤ l.1 ∧ l.1 ≤ mv) :
    parseClauses mv cls.length accCnf (10 :: cls.flatMap encodeDimacsClause) =
      some (cls.foldl CNF.add accCnf) := by
  induction cls generalizing accCnf with
  | nil =>
    simp only [List.length_nil, List.flatMap_nil, List.foldl_nil]
    rw [parseClauses]; simp [show skipWsComments [10] = [] from rfl]
  | cons cl cls ih =>
    simp only [List.length_cons, List.flatMap_cons]
    have hpc : parseClause mv (10 :: (encodeDimacsClause cl ++ cls.flatMap encodeDimacsClause)) =
        some (cl, 10 :: cls.flatMap encodeDimacsClause) := by
      rw [parseClause_ws_step (by decide : isDimacsWs 10 = true)]
      unfold parseClause encodeDimacsClause
      rw [List.append_assoc, parseClauseAux_encodeLits_gen hmv (fun l hl => hcls cl (by simp) l hl)
        (by omega)]
      simp
    rw [parseClauses, hpc]
    exact ih (accCnf.add cl) (fun c hc => hcls c (by simp [hc]))

private theorem foldl_cnf_add_toList (cls : List (CNF.Clause Nat)) (init : CNF Nat) :
    (cls.foldl CNF.add init).clauses.toList = init.clauses.toList ++ cls := by
  induction cls generalizing init with
  | nil => simp
  | cons cl cls ih => simp [CNF.add, ih]

/-- General DIMACS round-trip theorem for any declared header variable bound `mv < dimacsBound`
and clause list `clauses` with `clauses.length < dimacsBound` and all literal variables `< mv`:
`parseDimacs (emitDimacsBytes mv clauses) = some (kissatCnfToDimacs clauses)`. -/
theorem parseDimacs_emitDimacsBytes {mv : Nat} {clauses : List (List Nat)}
    (hmv : mv < dimacsBound) (hnc : clauses.length < dimacsBound)
    (hvars : ∀ cl ∈ clauses, ∀ l ∈ cl, litVar l < mv) :
    parseDimacs (emitDimacsBytes mv clauses) = some (kissatCnfToDimacs clauses) := by
  unfold parseDimacs emitDimacsBytes
  rw [parseHeader_emitDimacsHdrBytes hmv hnc]
  have hbody : clauses.flatMap emitDimacsClauseBytes =
      (clauses.map kissatClauseToDimacs).flatMap encodeDimacsClause := by
    rw [List.flatMap_map]
    have hfn : emitDimacsClauseBytes =
        (fun cl => encodeDimacsClause (kissatClauseToDimacs cl)) :=
      funext emitDimacsClauseBytes_eq_encodeDimacsClause
    rw [hfn]
  change parseClauses mv clauses.length CNF.empty (10 :: clauses.flatMap emitDimacsClauseBytes) = _
  rw [hbody, show clauses.length = (clauses.map kissatClauseToDimacs).length by simp]
  rw [parseClauses_encodeDimacsClauses_gen CNF.empty hmv (fun cl hcl l hl => by
    simp only [List.mem_map] at hcl
    obtain ⟨kcl, hkcl, rfl⟩ := hcl
    unfold kissatClauseToDimacs at hl
    rw [CNF.Clause.literals_ofLiterals, List.mem_map] at hl
    obtain ⟨kl, hkl, rfl⟩ := hl
    have := hvars kcl hkcl kl hkl
    unfold kissatLitToDimacs; omega)]
  congr 1
  rcases hfold : (clauses.map kissatClauseToDimacs).foldl CNF.add CNF.empty with ⟨cs⟩
  have hlist := foldl_cnf_add_toList (clauses.map kissatClauseToDimacs) CNF.empty
  rw [hfold] at hlist
  simp only [CNF.empty, Array.toList_empty, List.nil_append] at hlist
  unfold kissatCnfToDimacs
  exact congrArg CNF.mk (Array.ext' (by simpa using hlist))

/-! ## 4. Byte-Store Separation-Logic Helper (`store_bytes_at`) -/

private theorem bytes_append_eq (a : BitVec 64) (b1 b2 : List UInt8)
    (h : b1.length + b2.length ≤ 2 ^ 64) :
    bytes a (b1 ++ b2) = (bytes a b1 ⋆ bytes (a + BitVec.ofNat 64 b1.length) b2) :=
  eq_append_At a b1 b2 h

private theorem bytes_split_at (a : BitVec 64) (bs : List UInt8) (i : Nat)
    (hi : i ≤ bs.length) (hlen : bs.length ≤ 2 ^ 64) :
    bytes a bs = (bytes a (bs.take i) ⋆ bytes (a + BitVec.ofNat 64 i) (bs.drop i)) := by
  conv => lhs; rw [← List.take_append_drop i bs]
  rw [bytes_append_eq a (bs.take i) (bs.drop i) (by simp; omega),
    List.length_take_of_le hi]

private theorem store_bytes_at {a : BitVec 64} {bs : List UInt8} {i : Nat} (v : BitVec 8)
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i < bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes a bs ⋆ R) m) :
    storeOk m i8 (a + BitVec.ofNat 64 i) ∧
      (bytes a (bs.set i (UInt8.ofNat v.toNat)) ⋆ R)
        (storeMem m i8 (a + BitVec.ofNat 64 i) v) := by
  let bOld := bs[i]'hi
  have hsp : bytes a bs =
      (bytes a (bs.take i) ⋆
        (Eq ((Int.toBytes 1 (bOld.toNat : Int)).At (a + BitVec.ofNat 64 i)) ⋆
          bytes (a + BitVec.ofNat 64 i + 1#64) (bs.drop (i + 1)))) := by
    rw [bytes_split_at a bs i (Nat.le_of_lt hi) hlen]
    have hdrop : bs.drop i = [bOld] ++ bs.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hi]; rfl
    rw [hdrop, bytes_append_eq _ [bOld] _ (by simp; omega), toBytes_u8]
    simp only [List.length_singleton, BitVec.add_assoc]; rfl
  rw [hsp] at hm
  have hm' : (Eq ((Int.toBytes (Ty.bits 8).bytes (bOld.toNat : Int)).At (a + BitVec.ofNat 64 i)) ⋆
      (bytes a (bs.take i) ⋆ bytes (a + BitVec.ofNat 64 i + 1#64) (bs.drop (i + 1)) ⋆ R)) m :=
    sep_cast hm (by ac_rfl)
  obtain ⟨hok, hst⟩ := store_toBytes_bits (n := 8) v rfl (by decide) hm'
  refine ⟨hok, ?_⟩
  have hvBytes : Int.toBytes (Ty.bits 8).bytes (v.toNat : Int) = [UInt8.ofNat v.toNat] := by
    have hvEq : (UInt8.ofNat v.toNat).toNat = v.toNat := by
      rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt v.isLt]
    simpa [hvEq, Ty.bytes, Ty.size] using toBytes_u8 (UInt8.ofNat v.toNat)
  rw [hvBytes] at hst
  change (bytes (a + BitVec.ofNat 64 i) [UInt8.ofNat v.toNat] ⋆
      (bytes a (bs.take i) ⋆ bytes (a + BitVec.ofNat 64 i + 1#64) (bs.drop (i + 1)) ⋆ R)) _ at hst
  have hjoin : bytes a (bs.set i (UInt8.ofNat v.toNat)) =
      (bytes a (bs.take i) ⋆
        (bytes (a + BitVec.ofNat 64 i) [UInt8.ofNat v.toNat] ⋆
          bytes (a + BitVec.ofNat 64 i + 1#64) (bs.drop (i + 1)))) := by
    have hlen' : (bs.set i (UInt8.ofNat v.toNat)).length ≤ 2 ^ 64 := by simpa using hlen
    rw [bytes_split_at a _ i (by simp; omega) hlen', List.take_set_of_le (Nat.le_refl i)]
    have hdrop' : (bs.set i (UInt8.ofNat v.toNat)).drop i =
        [UInt8.ofNat v.toNat] ++ bs.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simp [hi]), List.getElem_set_self]
      congr 1
      exact List.drop_set_of_lt (Nat.lt_succ_self i)
    rw [hdrop', bytes_append_eq _ [UInt8.ofNat v.toNat] _ (by simp; omega)]
    simp only [List.length_singleton, BitVec.add_assoc]
  rw [hjoin]
  exact sep_cast hst (by ac_rfl)

/-! ## 5. WP Proofs for All Four C0 Functions -/

private theorem bv64_add_ofNat_eq (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

private theorem bv64_ult_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

private theorem bv64_ule_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = decide (a ≤ b) := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

private theorem pow10_lt_u64 {k : Nat} (hk : k ≤ 19) : 10 ^ k < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hk) (by decide : 10 ^ 19 < 2 ^ 64)

private theorem bv64_pow10_toNat {k : Nat} (hk : k ≤ 19) :
    (BitVec.ofNat 64 (10 ^ k)).toNat = 10 ^ k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (pow10_lt_u64 hk)]

theorem kissat_emit_byte_wp (Γ : Env) :
    ∀ args m Q X, kissatEmitByteSpec args m Q X →
      Func.wp Γ kissat_emit_byte_body args m Q X := by
  rintro _ m Q X ⟨out, buf, pos, b, R, rfl, hcap, hpos, hm, hQ⟩
  unfold Func.wp kissat_emit_byte_body
  c0_hsteps_nogrp
  refine wp_join0 (fun m' => (buf.length ≤ pos → m' = m) ∧
      (bytes out (writeSlice buf pos [UInt8.ofNat b.toNat]) ⋆ R) m')
    (fun _ m' ⟨hmeq, hm'⟩ => by
      c0_hsteps
      rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv64_add_ofNat_eq]
      exact hQ m' hmeq hm') ?_
  intro J hJ
  c0_hsteps
  · have hlt : pos < buf.length := by
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hcap] at hc; exact hc
    dsimp only
    obtain ⟨hok, hst⟩ := store_bytes_at (v := b.setWidth 8) hlt (by omega) hm
    refine ⟨hok, ?_⟩
    c0_hsteps
    apply hJ _ ⟨fun hge => absurd hlt (Nat.not_lt_of_ge hge), ?_⟩
    have hvEq : UInt8.ofNat (b.setWidth 8).toNat = UInt8.ofNat b.toNat := by
      apply UInt8.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
      change (UInt8.ofNat (b.setWidth 8).toNat).toNat = (UInt8.ofNat b.toNat).toNat
      simp [UInt8.toNat_ofNat', BitVec.toNat_setWidth]
    rw [hvEq] at hst
    simpa [writeSlice, hlt] using hst
  · have hnlt : ¬ pos < buf.length := by
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hcap] at hc; omega
    apply hJ m ⟨fun _ => rfl, ?_⟩
    simpa [writeSlice, hnlt] using hm

private structure U64DownSt where
  k : Nat
  done : Bool
  pos : Nat
  x : Nat
  buf : List UInt8

theorem kissat_emit_u64_wp (Γ : Env)
    (hByte : ∀ args m Q X, kissatEmitByteSpec args m Q X →
      Γ "kissat_emit_byte" [i64, i64, i64, i64] [i64] args m Q X) :
    ∀ args m Q X, kissatEmitU64Spec args m Q X →
      Func.wp Γ kissat_emit_u64_body args m Q X := by
  rintro _ m Q X ⟨out, buf, pos0, x, R, rfl, hcap, hpos, hm, hQ⟩
  unfold Func.wp kissat_emit_u64_body
  c0_hsteps_nogrp
  have hq_toNat : (x / 10#64).toNat = x.toNat / 10 := by
    rw [BitVec.toNat_udiv]; rfl
  -- Loop 1: `while (p <= q) { p = p * 10; }` computes `p = 10^k` with `k <= 19`
  refine wp_while_state_pure (α := Nat)
    (fun j => (BitVec.ofNat 64 (10 ^ j), ()))
    (fun j => 19 - j)
    (fun j => j ≤ 19 ∧ (j = 0 ∨ 10 ^ j ≤ x.toNat))
    (fun J1 hJ1 => by
      c0_hsteps
      exact hJ1 0 ⟨by omega, Or.inl rfl⟩)
    (fun J1 j ⟨hj, hlow⟩ ih1 => by
      c0_hsteps_nogrp
      · have hle : 10 ^ j ≤ x.toNat / 10 := by
          rw [Nat.mod_eq_of_lt (pow10_lt_u64 hj)] at hc; exact hc
        have hnext_le : 10 ^ (j + 1) ≤ x.toNat := by rw [Nat.pow_succ]; omega
        have hx20 : x.toNat < 10 ^ 20 := Nat.lt_trans x.isLt (by decide : 2 ^ 64 < 10 ^ 20)
        have hj1 : j + 1 ≤ 19 := by
          by_cases h19 : j + 1 ≤ 19
          · exact h19
          · have hpow : 10 ^ 20 ≤ 10 ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
            omega
        have hmul : BitVec.ofNat 64 (10 ^ j) * (10 : BitVec 64) =
            BitVec.ofNat 64 (10 ^ (j + 1)) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_mul, bv64_pow10_toNat hj, bv64_pow10_toNat hj1]
          change (10 ^ j * 10) % 2 ^ 64 = 10 ^ (j + 1)
          rw [← Nat.pow_succ, Nat.mod_eq_of_lt (pow10_lt_u64 hj1)]
        rw [hmul]
        exact ih1 (j + 1) (by omega) ⟨hj1, Or.inr hnext_le⟩
      · -- Loop 1 exits with `p = 10^j` and `x < 10^(j+1)`
        have hgt : ¬ 10 ^ j ≤ x.toNat / 10 := by
          rw [Nat.mod_eq_of_lt (pow10_lt_u64 hj)] at hc; exact hc
        have hx_lt : x.toNat < 10 ^ (j + 1) := by rw [Nat.pow_succ]; omega
        have hdig_eq : digitsPow10 j x.toNat = natToBytes x.toNat :=
          digitsPow10_eq_natToBytes j x.toNat hlow hx_lt
        have hdig_len : (natToBytes x.toNat).length = j + 1 := by
          rw [← hdig_eq, digitsPow10_length]
        -- Loop 2: `while (p > 0)` emits `digitsPow10 j x.toNat` left-to-right
        refine wp_while_state (α := U64DownSt)
          (fun st => (BitVec.ofNat 64 st.pos, BitVec.ofNat 64 st.x,
            if st.done then 0#64 else BitVec.ofNat 64 (10 ^ st.k), ()))
          (fun st => if st.done then 0 else st.k + 1)
          (fun st m_l =>
            let remBs := if st.done then [] else digitsPow10 st.k st.x
            st.k ≤ 19 ∧
            st.x < 2 ^ 64 ∧
            st.buf.length = buf.length ∧
            (st.done = false → st.x < 10 ^ (st.k + 1)) ∧
            st.pos + remBs.length = pos0 + (natToBytes x.toNat).length ∧
            writeSlice st.buf st.pos remBs = writeSlice buf pos0 (natToBytes x.toNat) ∧
            (buf.length ≤ pos0 → m_l = m) ∧
            pos0 ≤ st.pos ∧
            (bytes out st.buf ⋆ R) m_l)
          (fun J2 hJ2 => by
            c0_hsteps
            have hx_bv : BitVec.ofNat 64 x.toNat = x := by simp
            simpa only [hx_bv, Bool.false_eq_true, ↓reduceIte] using
              hJ2 ⟨j, false, pos0, x.toNat, buf⟩ m
                ⟨hj, x.isLt, rfl, fun _ => hx_lt, by simp [hdig_eq], by simp [hdig_eq],
                  fun _ => rfl, Nat.le_refl _, hm⟩)
          (fun J2 st m_l hinv ih2 => by
            obtain ⟨hk, hx64, hblen, hxlt_f, hpos_sum, hws_inv, hmeq_l, hpos_ge, hm_l⟩ := hinv
            cases hdone : st.done with
            | true =>
              simp only [hdone, ↓reduceIte, List.length_nil, Nat.add_zero, writeSlice_nil]
                at hpos_sum hws_inv ⊢
              c0_hsteps
              rw [hpos_sum]
              rw [hws_inv] at hm_l
              exact hQ m_l hmeq_l hm_l
            | false =>
              simp only [hdone, Bool.false_eq_true, ↓reduceIte] at hpos_sum hws_inv hxlt_f ⊢
              have hx_lt_k : st.x < 10 ^ (st.k + 1) := hxlt_f trivial
              have hp_pos : 0 < 10 ^ st.k := Nat.pow_pos (by omega)
              have hp_lt64 : 10 ^ st.k < 2 ^ 64 := pow10_lt_u64 hk
              have hp_toNat : (BitVec.ofNat 64 (10 ^ st.k)).toNat = 10 ^ st.k :=
                bv64_pow10_toNat hk
              have hp_ne0 : BitVec.ofNat 64 (10 ^ st.k) ≠ 0#64 := fun heq => by
                have h0 := congrArg BitVec.toNat heq
                rw [hp_toNat] at h0; simp at h0
              c0_hsteps_nogrp
              dsimp only
              have hd_toNat : (BitVec.ofNat 64 st.x / BitVec.ofNat 64 (10 ^ st.k)).toNat =
                  st.x / 10 ^ st.k := by
                rw [BitVec.toNat_udiv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx64, hp_toNat]
              have hd_lt10 : st.x / 10 ^ st.k < 10 := by
                rw [Nat.div_lt_iff_lt_mul hp_pos, Nat.mul_comm, ← Nat.pow_succ]; exact hx_lt_k
              have hb_eq : UInt8.ofNat
                  ((48 + BitVec.ofNat 64 st.x / BitVec.ofNat 64 (10 ^ st.k)).toNat) =
                  UInt8.ofNat (48 + st.x / 10 ^ st.k) := by
                congr 1
                rw [BitVec.toNat_add, hd_toNat]
                change (48 + st.x / 10 ^ st.k) % 2 ^ 64 = 48 + st.x / 10 ^ st.k
                exact Nat.mod_eq_of_lt (by omega)
              have hrem_len : (digitsPow10 st.k st.x).length = st.k + 1 :=
                digitsPow10_length st.k st.x
              apply wp_call_of_spec
              apply hByte
              refine ⟨out, st.buf, st.pos,
                48 + BitVec.ofNat 64 st.x / BitVec.ofNat 64 (10 ^ st.k), R,
                by simp [vals, hblen], by omega, by omega, hm_l, fun m1 hmeq1 hm1 => ?_⟩
              c0_hsteps_nogrp
              have hrem_eq : BitVec.ofNat 64 st.x -
                  (BitVec.ofNat 64 st.x / BitVec.ofNat 64 (10 ^ st.k)) *
                    BitVec.ofNat 64 (10 ^ st.k) =
                  BitVec.ofNat 64 (st.x % 10 ^ st.k) := by
                have hdm : st.x / 10 ^ st.k * 10 ^ st.k + st.x % 10 ^ st.k = st.x := by
                  rw [Nat.mul_comm]; exact Nat.div_add_mod st.x (10 ^ st.k)
                have hmul_lt : st.x / 10 ^ st.k * 10 ^ st.k < 2 ^ 64 := by omega
                have hmul_toNat :
                    ((BitVec.ofNat 64 st.x / BitVec.ofNat 64 (10 ^ st.k)) *
                      BitVec.ofNat 64 (10 ^ st.k)).toNat = st.x / 10 ^ st.k * 10 ^ st.k := by
                  rw [BitVec.toNat_mul, hd_toNat, hp_toNat, Nat.mod_eq_of_lt hmul_lt]
                have hmod_lt : st.x % 10 ^ st.k < 2 ^ 64 :=
                  Nat.lt_of_le_of_lt (Nat.mod_le _ _) hx64
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_sub_of_le (by
                    rw [BitVec.le_def, hmul_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx64]
                    omega),
                  BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx64, hmul_toNat,
                  BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmod_lt]
                omega
              rw [hrem_eq]
              let buf1 := writeSlice st.buf st.pos [UInt8.ofNat (48 + st.x / 10 ^ st.k)]
              have hm1' : (bytes out buf1 ⋆ R) m1 := by simpa [buf1, hb_eq] using hm1
              have hblen1 : buf1.length = buf.length := by
                simp only [buf1, writeSlice_length, hblen]
              have hmeq1' : buf.length ≤ pos0 → m1 = m := fun hge =>
                (hmeq1 (by omega)).trans (hmeq_l hge)
              cases hk_eq : st.k with
              | zero =>
                have hp0 : BitVec.ofNat 64 (10 ^ 0) / (10 : BitVec 64) = 0#64 := by decide
                rw [hp0]
                have hws1 : buf1 = writeSlice buf pos0 (natToBytes x.toNat) := by
                  rw [← hws_inv, hk_eq]
                  simp [buf1, digitsPow10, hk_eq]
                simpa only [↓reduceIte] using
                  ih2 ⟨0, true, st.pos + 1, st.x % 1, buf1⟩ m1 (by simp [hk_eq, hdone])
                    ⟨(by dsimp; omega), (by dsimp; omega), hblen1, (fun h => by cases h),
                      (by rw [hk_eq] at hpos_sum; simpa [digitsPow10] using hpos_sum),
                      (by simpa [writeSlice_nil] using hws1), hmeq1', (by dsimp; omega), hm1'⟩
              | succ k' =>
                have hp_div : BitVec.ofNat 64 (10 ^ (k' + 1)) / (10 : BitVec 64) =
                    BitVec.ofNat 64 (10 ^ k') := by
                  apply BitVec.eq_of_toNat_eq
                  rw [BitVec.toNat_udiv, bv64_pow10_toNat (hk_eq ▸ hk),
                    bv64_pow10_toNat (by omega)]
                  change 10 ^ (k' + 1) / 10 = 10 ^ k'
                  rw [Nat.pow_succ, Nat.mul_div_cancel _ (by omega)]
                rw [hp_div]
                have hws_next : writeSlice buf1 (st.pos + 1)
                    (digitsPow10 k' (st.x % 10 ^ (k' + 1))) =
                    writeSlice buf pos0 (natToBytes x.toNat) := by
                  rw [← hws_inv, hk_eq]
                  dsimp only [buf1, digitsPow10]
                  rw [hk_eq, writeSlice_cons, writeSlice_nil, writeSlice_cons]
                have hmod_lt : st.x % 10 ^ (k' + 1) < 10 ^ (k' + 1) :=
                  Nat.mod_lt _ (Nat.pow_pos (by omega))
                simpa only [Bool.false_eq_true, ↓reduceIte] using
                  ih2 ⟨k', false, st.pos + 1, st.x % 10 ^ (k' + 1), buf1⟩ m1
                    (by simp [hk_eq, hdone])
                    ⟨(by dsimp; omega), Nat.lt_trans hmod_lt (pow10_lt_u64 (by omega)), hblen1,
                      (fun _ => hmod_lt),
                      (by rw [hk_eq] at hpos_sum; simp [digitsPow10_length] at hpos_sum ⊢; omega),
                      hws_next, hmeq1', (by dsimp; omega), hm1'⟩))

private theorem bv64_and1_ne_zero_iff (lit : BitVec 64) :
    lit &&& 1#64 ≠ 0#64 ↔ litSign lit.toNat = true := by
  unfold litSign
  have h1 : (lit &&& 1#64).toNat = lit.toNat % 2 := bv_c0_toNat_and_one_64 lit
  constructor
  · intro hne
    by_cases hm : lit.toNat % 2 = 1
    · simp [hm]
    · have hm0 : lit.toNat % 2 = 0 := by omega
      exact absurd (BitVec.eq_of_toNat_eq (by rw [h1, hm0]; rfl)) hne
  · intro h1eq heq
    have h0 := congrArg BitVec.toNat heq
    rw [h1] at h0; simp at h0 h1eq; omega

private theorem bv64_lshr1_add1 (lit : BitVec 64) :
    (lit >>> (1 : Nat)) + (1 : BitVec 64) = BitVec.ofNat 64 (litVar lit.toNat + 1) := by
  apply BitVec.eq_of_toNat_eq
  have hlt : lit.toNat / 2 + 1 < 2 ^ 64 := by have := lit.isLt; omega
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one,
    show (1 : BitVec 64).toNat = 1 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, litVar,
    Nat.mod_eq_of_lt hlt]

private theorem emitDimacsLitBytes_decomp (lit : Nat) :
    emitDimacsLitBytes lit =
      (if litSign lit then [asciiMinus] else []) ++
        natToBytes (litVar lit + 1) ++ [asciiSpace] := by
  unfold emitDimacsLitBytes encodeDimacsLit kissatLitToDimacs
  cases litSign lit <;> simp

theorem kissat_emit_dimacs_lit_wp (Γ : Env)
    (hByte : ∀ args m Q X, kissatEmitByteSpec args m Q X →
      Γ "kissat_emit_byte" [i64, i64, i64, i64] [i64] args m Q X)
    (hU64 : ∀ args m Q X, kissatEmitU64Spec args m Q X →
      Γ "kissat_emit_u64" [i64, i64, i64, i64] [i64] args m Q X) :
    ∀ args m Q X, kissatEmitDimacsLitSpec args m Q X →
      Func.wp Γ kissat_emit_dimacs_lit_body args m Q X := by
  rintro _ m Q X ⟨out, buf, pos0, lit, R, rfl, hcap, hpos, hm, hQ⟩
  unfold Func.wp kissat_emit_dimacs_lit_body
  let pre : List UInt8 := if litSign lit.toNat then [asciiMinus] else []
  have hdecomp := emitDimacsLitBytes_decomp lit.toNat
  have hlen_decomp : (emitDimacsLitBytes lit.toNat).length =
      pre.length + (natToBytes (litVar lit.toNat + 1)).length + 1 := by
    rw [hdecomp]; simp [pre, Nat.add_assoc]
  c0_hsteps_nogrp
  refine wp_join_state1 (α := Unit) (fun _ => BitVec.ofNat 64 (pos0 + pre.length))
    (fun _ m1 => (buf.length ≤ pos0 → m1 = m) ∧
      (bytes out (writeSlice buf pos0 pre) ⋆ R) m1)
    (fun _ _ m1 ⟨hmeq1, hm1⟩ => by
      c0_hsteps_nogrp
      dsimp only
      rw [bv64_lshr1_add1]
      have hv_toNat : (BitVec.ofNat 64 (litVar lit.toNat + 1)).toNat = litVar lit.toNat + 1 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold litVar; have := lit.isLt; omega)]
      apply wp_call_of_spec
      apply hU64
      refine ⟨out, writeSlice buf pos0 pre, pos0 + pre.length,
        BitVec.ofNat 64 (litVar lit.toNat + 1), R,
        by simp [vals, writeSlice_length], by rw [writeSlice_length]; exact hcap,
        by rw [hv_toNat]; omega, hm1, fun m2 hmeq2 hm2 => ?_⟩
      rw [hv_toNat] at hm2 ⊢
      c0_hsteps_nogrp
      dsimp only
      apply wp_call_of_spec
      apply hByte
      refine ⟨out, writeSlice (writeSlice buf pos0 pre) (pos0 + pre.length)
          (natToBytes (litVar lit.toNat + 1)),
        pos0 + pre.length + (natToBytes (litVar lit.toNat + 1)).length,
        32#64, R,
        by simp [vals, writeSlice_length], by simp [writeSlice_length]; exact hcap,
        by omega, hm2, fun m3 hmeq3 hm3 => ?_⟩
      c0_hsteps
      have hws_all : writeSlice
          (writeSlice (writeSlice buf pos0 pre) (pos0 + pre.length)
            (natToBytes (litVar lit.toNat + 1)))
          (pos0 + pre.length + (natToBytes (litVar lit.toNat + 1)).length) [asciiSpace] =
          writeSlice buf pos0 (emitDimacsLitBytes lit.toNat) := by
        rw [hdecomp, writeSlice_append, writeSlice_append]
        simp [pre, List.length_append, Nat.add_assoc]
      have hmeq3' : buf.length ≤ pos0 → m3 = m := fun hge =>
        (hmeq3 (by simp [writeSlice_length]; omega)).trans
          ((hmeq2 (by simp [writeSlice_length]; omega)).trans (hmeq1 hge))
      rw [show (UInt8.ofNat (32#64 : BitVec 64).toNat) = asciiSpace from rfl, hws_all] at hm3
      rw [show pos0 + pre.length + (natToBytes (litVar lit.toNat + 1)).length + 1 =
          pos0 + (emitDimacsLitBytes lit.toNat).length by omega]
      exact hQ m3 hmeq3' hm3)
    (fun J hJ => by
      c0_hsteps_nogrp
      · have hneg : litSign lit.toNat = true := (bv64_and1_ne_zero_iff lit).mp hc
        dsimp only
        apply wp_call_of_spec
        apply hByte
        refine ⟨out, buf, pos0, 45#64, R, rfl, hcap, by
          have : pre.length = 1 := by simp [pre, hneg]
          omega, hm, fun m1 hmeq1 hm1 => ?_⟩
        c0_hsteps
        have hpre : pre = [asciiMinus] := by simp [pre, hneg]
        simpa [hpre, show UInt8.ofNat (45#64 : BitVec 64).toNat = asciiMinus from rfl] using
          hJ () m1 ⟨hmeq1, by simpa [hpre] using hm1⟩
      · have hpos_pol : litSign lit.toNat = false := by
          by_cases hs : litSign lit.toNat = true
          · exact absurd hc ((bv64_and1_ne_zero_iff lit).mpr hs)
          · exact Bool.eq_false_iff.mpr hs
        have hpre : pre = [] := by simp [pre, hpos_pol]
        have hm' : (bytes out (writeSlice buf pos0 pre) ⋆ R) m := by
          rw [hpre, writeSlice_nil]; exact hm
        have hres := hJ () m ⟨fun _ => rfl, hm'⟩
        simpa [hpre] using hres)

private theorem hdr_step_byte {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {out : BitVec 64} {buf0 : List UInt8} (pos0 : Nat) {curPos : Nat} (pre : List UInt8)
    (b : UInt8) {R : Mem 64 → Prop} {m0 m1 : Mem 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hByte : ∀ args m Q X, kissatEmitByteSpec args m Q X →
      Γ "kissat_emit_byte" [i64, i64, i64, i64] [i64] args m Q X)
    (hcur : curPos = pos0 + pre.length)
    (hcap : buf0.length < 2 ^ 64) (hpos : pos0 + pre.length + 1 < 2 ^ 64)
    (hmeq1 : buf0.length ≤ pos0 → m1 = m0)
    (hm1 : (bytes out (writeSlice buf0 pos0 pre) ⋆ R) m1)
    (hk : ∀ m2, (buf0.length ≤ pos0 → m2 = m0) →
      (bytes out (writeSlice buf0 pos0 (pre ++ [b])) ⋆ R) m2 →
      wp Γ Q X (k (BitVec.ofNat 64 (pos0 + (pre ++ [b]).length), ())) m2) :
    wp Γ Q X (.call "kissat_emit_byte" (as := [i64, i64, i64, i64]) (bs := [i64])
      (Arg.var out, Arg.var (BitVec.ofNat 64 buf0.length),
        Arg.var (BitVec.ofNat 64 curPos),
        Arg.imm (BitVec.ofNat 64 b.toNat), ()) k) m1 := by
  subst hcur
  apply wp_call_of_spec
  apply hByte
  refine ⟨out, writeSlice buf0 pos0 pre, pos0 + pre.length, BitVec.ofNat 64 b.toNat, R,
    by simp [vals, writeSlice_length], by rw [writeSlice_length]; exact hcap, hpos, hm1,
    fun m2 hmeq2 hm2 => ?_⟩
  have hb : UInt8.ofNat (BitVec.ofNat 64 b.toNat).toNat = b := by
    apply UInt8.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
    change (UInt8.ofNat (BitVec.ofNat 64 b.toNat).toNat).toNat = b.toNat
    simp [BitVec.toNat_ofNat]
  rw [hb, ← writeSlice_append] at hm2
  rw [show pos0 + pre.length + 1 = pos0 + (pre ++ [b]).length by simp [Nat.add_assoc]]
  exact hk m2 (fun hge => (hmeq2 (by rw [writeSlice_length]; omega)).trans (hmeq1 hge)) hm2

private theorem hdr_step_u64 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {out : BitVec 64} {buf0 : List UInt8} (pos0 : Nat) {curPos : Nat} (pre : List UInt8)
    (x : BitVec 64) {R : Mem 64 → Prop} {m0 m1 : Mem 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hU64 : ∀ args m Q X, kissatEmitU64Spec args m Q X →
      Γ "kissat_emit_u64" [i64, i64, i64, i64] [i64] args m Q X)
    (hcur : curPos = pos0 + pre.length)
    (hcap : buf0.length < 2 ^ 64)
    (hpos : pos0 + pre.length + (natToBytes x.toNat).length < 2 ^ 64)
    (hmeq1 : buf0.length ≤ pos0 → m1 = m0)
    (hm1 : (bytes out (writeSlice buf0 pos0 pre) ⋆ R) m1)
    (hk : ∀ m2, (buf0.length ≤ pos0 → m2 = m0) →
      (bytes out (writeSlice buf0 pos0 (pre ++ natToBytes x.toNat)) ⋆ R) m2 →
      wp Γ Q X (k (BitVec.ofNat 64 (pos0 + (pre ++ natToBytes x.toNat).length), ())) m2) :
    wp Γ Q X (.call "kissat_emit_u64" (as := [i64, i64, i64, i64]) (bs := [i64])
      (Arg.var out, Arg.var (BitVec.ofNat 64 buf0.length),
        Arg.var (BitVec.ofNat 64 curPos), Arg.var x, ()) k) m1 := by
  subst hcur
  apply wp_call_of_spec
  apply hU64
  refine ⟨out, writeSlice buf0 pos0 pre, pos0 + pre.length, x, R,
    by simp [vals, writeSlice_length], by rw [writeSlice_length]; exact hcap, hpos, hm1,
    fun m2 hmeq2 hm2 => ?_⟩
  rw [← writeSlice_append] at hm2
  rw [show pos0 + pre.length + (natToBytes x.toNat).length =
      pos0 + (pre ++ natToBytes x.toNat).length by simp [Nat.add_assoc]]
  exact hk m2 (fun hge => (hmeq2 (by rw [writeSlice_length]; omega)).trans (hmeq1 hge)) hm2

theorem kissat_emit_dimacs_hdr_wp (Γ : Env)
    (hByte : ∀ args m Q X, kissatEmitByteSpec args m Q X →
      Γ "kissat_emit_byte" [i64, i64, i64, i64] [i64] args m Q X)
    (hU64 : ∀ args m Q X, kissatEmitU64Spec args m Q X →
      Γ "kissat_emit_u64" [i64, i64, i64, i64] [i64] args m Q X) :
    ∀ args m Q X, kissatEmitDimacsHdrSpec args m Q X →
      Func.wp Γ kissat_emit_dimacs_hdr_body args m Q X := by
  rintro _ m Q X ⟨out, buf, pos0, mv, nc, R, rfl, hcap, hpos, hm, hQ⟩
  unfold Func.wp kissat_emit_dimacs_hdr_body
  have hlen : (emitDimacsHdrBytes mv.toNat nc.toNat).length =
      6 + (natToBytes mv.toNat).length + 1 + (natToBytes nc.toNat).length + 1 := by
    unfold emitDimacsHdrBytes dimacsHeaderPrefix
    simp only [List.length_append, List.length_cons, List.length_nil]
  c0_hsteps_nogrp; dsimp only
  refine hdr_step_byte pos0 [] asciiP hByte (by simp) hcap (by simp; omega)
    (fun _ => rfl) (by simpa [writeSlice_nil] using hm) fun m1 hm1e hm1 => ?_
  c0_hsteps_nogrp; dsimp only
  refine hdr_step_byte pos0 _ asciiSpace hByte rfl hcap (by simp; omega)
    hm1e hm1 fun m2 hm2e hm2 => ?_
  c0_hsteps_nogrp; dsimp only
  refine hdr_step_byte pos0 _ asciiC hByte rfl hcap (by simp; omega)
    hm2e hm2 fun m3 hm3e hm3 => ?_
  c0_hsteps_nogrp; dsimp only
  refine hdr_step_byte pos0 _ asciiN hByte rfl hcap (by simp; omega)
    hm3e hm3 fun m4 hm4e hm4 => ?_
  c0_hsteps_nogrp; dsimp only
  refine hdr_step_byte pos0 _ asciiF hByte rfl hcap (by simp; omega)
    hm4e hm4 fun m5 hm5e hm5 => ?_
  c0_hsteps_nogrp; dsimp only
  refine hdr_step_byte pos0 _ asciiSpace hByte rfl hcap (by simp; omega)
    hm5e hm5 fun m6 hm6e hm6 => ?_
  c0_hsteps_nogrp; dsimp only
  refine hdr_step_u64 pos0 _ mv hU64 rfl hcap (by simp; omega)
    hm6e hm6 fun m7 hm7e hm7 => ?_
  c0_hsteps_nogrp; dsimp only
  refine hdr_step_byte pos0 _ asciiSpace hByte rfl hcap (by simp; omega)
    hm7e hm7 fun m8 hm8e hm8 => ?_
  c0_hsteps_nogrp; dsimp only
  refine hdr_step_u64 pos0 _ nc hU64 rfl hcap (by simp; omega)
    hm8e hm8 fun m9 hm9e hm9 => ?_
  c0_hsteps_nogrp; dsimp only
  refine hdr_step_byte pos0 _ asciiNewline hByte rfl hcap (by simp; omega)
    hm9e hm9 fun m10 hm10e hm10 => ?_
  c0_hsteps
  have hhdr_eq :
      ([] ++ [asciiP] ++ [asciiSpace] ++ [asciiC] ++ [asciiN] ++ [asciiF] ++ [asciiSpace] ++
        natToBytes mv.toNat ++ [asciiSpace] ++ natToBytes nc.toNat ++ [asciiNewline]) =
      emitDimacsHdrBytes mv.toNat nc.toNat := by
    unfold emitDimacsHdrBytes dimacsHeaderPrefix
    simp [List.append_assoc]
  rw [hhdr_eq] at hm10 ⊢
  exact hQ m10 hm10e hm10

/-! ## 6. Closed-Module Soundness (`ModuleOk`) and Lifting into Larger Environments -/

private theorem exportCnfFmtEnv_byte :
    exportCnfFmtEnv "kissat_emit_byte" [i64, i64, i64, i64] [i64] = kissatEmitByteSpec := by
  simp [exportCnfFmtEnv]

private theorem exportCnfFmtEnv_u64 :
    exportCnfFmtEnv "kissat_emit_u64" [i64, i64, i64, i64] [i64] = kissatEmitU64Spec := by
  simp [exportCnfFmtEnv]

private theorem exportCnfFmtEnv_lit :
    exportCnfFmtEnv "kissat_emit_dimacs_lit" [i64, i64, i64, i64] [i64] =
      kissatEmitDimacsLitSpec := by
  simp [exportCnfFmtEnv]

private theorem exportCnfFmtEnv_hdr :
    exportCnfFmtEnv "kissat_emit_dimacs_hdr" [i64, i64, i64, i64, i64] [i64] =
      kissatEmitDimacsHdrSpec := by
  simp [exportCnfFmtEnv]

/-- Every function in `exportCnfFmt_fns` satisfies its contract in `exportCnfFmtEnv`. -/
theorem exportCnfFmtEnv_sound :
    ∀ f ∈ exportCnfFmt_fns, ∀ args m Q X,
      exportCnfFmtEnv f.name f.as f.rs args m Q X →
      Func.wp exportCnfFmtEnv f.body args m Q X := by
  intro f hf args m Q X hspec
  simp only [exportCnfFmt_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · dsimp only [kissat_emit_byte] at hspec ⊢
    rw [exportCnfFmtEnv_byte] at hspec
    exact kissat_emit_byte_wp exportCnfFmtEnv args m Q X hspec
  · dsimp only [kissat_emit_u64] at hspec ⊢
    rw [exportCnfFmtEnv_u64] at hspec
    exact kissat_emit_u64_wp exportCnfFmtEnv
      (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_byte]) args m Q X hspec
  · dsimp only [kissat_emit_dimacs_lit] at hspec ⊢
    rw [exportCnfFmtEnv_lit] at hspec
    exact kissat_emit_dimacs_lit_wp exportCnfFmtEnv
      (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_byte])
      (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_u64]) args m Q X hspec
  · dsimp only [kissat_emit_dimacs_hdr] at hspec ⊢
    rw [exportCnfFmtEnv_hdr] at hspec
    exact kissat_emit_dimacs_hdr_wp exportCnfFmtEnv
      (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_byte])
      (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_u64]) args m Q X hspec

/-- Closed acyclic `ModuleOk` certificate for `exportCnfFmtMod` under `exportCnfFmtEnv`. -/
theorem exportCnfFmtEnv_moduleOk : ModuleOk exportCnfFmtEnv exportCnfFmtMod :=
  Module.moduleOk_of_checkAcyclic exportCnfFmtMod_checkAcyclic exportCnfFmt_fns_wf
    exportCnfFmtEnv_sound

/-- Restricted closed-module soundness (`Env.ofModule exportCnfFmtMod exportCnfFmtEnv`). -/
theorem exportCnfFmtEnv_ofModule_ok :
    ModuleOk (Env.ofModule exportCnfFmtMod exportCnfFmtEnv) exportCnfFmtMod :=
  exportCnfFmtEnv_moduleOk.ofModule

/-- Lift `exportCnfFmtEnv_sound` into any larger environment `Γ` (such as a full Kissat
exporter environment) that subsumes `exportCnfFmtEnv` on `exportCnfFmt_fns`. -/
theorem exportCnfFmtFns_sound_in (Γ : Env)
    (hSub : ∀ f ∈ exportCnfFmt_fns, ∀ args m Q X,
      exportCnfFmtEnv f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X) :
    ∀ f ∈ exportCnfFmt_fns, ∀ args m Q X,
      exportCnfFmtEnv f.name f.as f.rs args m Q X → Func.wp Γ f.body args m Q X := by
  intro f hf args m Q X hspec
  have hok := exportCnfFmtEnv_moduleOk
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf
  have hwp := hok.wp_restrict (pre := pre) (post := post) hsplit hspec
  refine wp_env_mono (fun g as bs xs m' P E hg => ?_) _ m hwp
  simp only [Env.restrict, exportCnfFmtMod, List.map_nil, List.append_nil, List.mem_map] at hg
  rcases hg with ⟨⟨fn, hfn, hsig⟩, hexp⟩
  have hfn' : fn ∈ exportCnfFmt_fns := by rw [hsplit]; exact List.mem_append_left _ hfn
  cases hsig
  exact hSub fn hfn' xs m' P E hexp

/-! ## 7. Ergonomic Closed-Env, Full-Write, and Dry-Run Corollaries -/

theorem kissat_emit_byte_sound :
    ∀ args m Q X, kissatEmitByteSpec args m Q X →
      Func.wp exportCnfFmtEnv kissat_emit_byte_body args m Q X :=
  kissat_emit_byte_wp exportCnfFmtEnv

theorem kissat_emit_u64_sound :
    ∀ args m Q X, kissatEmitU64Spec args m Q X →
      Func.wp exportCnfFmtEnv kissat_emit_u64_body args m Q X :=
  kissat_emit_u64_wp exportCnfFmtEnv (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_byte])

theorem kissat_emit_dimacs_lit_sound :
    ∀ args m Q X, kissatEmitDimacsLitSpec args m Q X →
      Func.wp exportCnfFmtEnv kissat_emit_dimacs_lit_body args m Q X :=
  kissat_emit_dimacs_lit_wp exportCnfFmtEnv
    (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_byte])
    (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_u64])

theorem kissat_emit_dimacs_hdr_sound :
    ∀ args m Q X, kissatEmitDimacsHdrSpec args m Q X →
      Func.wp exportCnfFmtEnv kissat_emit_dimacs_hdr_body args m Q X :=
  kissat_emit_dimacs_hdr_wp exportCnfFmtEnv
    (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_byte])
    (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_u64])

theorem kissat_emit_byte_write
    {out b : BitVec 64} {buf : List UInt8} {pos : Nat} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hcap : buf.length < 2 ^ 64) (hfit : pos + 1 ≤ buf.length)
    (hm : (bytes out buf ⋆ R) m)
    (hQ : ∀ m',
      (bytes out (buf.take pos ++ [UInt8.ofNat b.toNat] ++ buf.drop (pos + 1)) ⋆ R) m' →
      Q (BitVec.ofNat 64 (pos + 1), ()) m') :
    Func.wp exportCnfFmtEnv kissat_emit_byte_body
      (out, BitVec.ofNat 64 buf.length, BitVec.ofNat 64 pos, b, ()) m Q X := by
  refine kissat_emit_byte_wp exportCnfFmtEnv _ m Q X ?_
  refine ⟨out, buf, pos, b, R, rfl, hcap, by omega, hm, fun m' _ hm' => ?_⟩
  rw [writeSlice_fit buf pos [UInt8.ofNat b.toNat] (by simpa using hfit)] at hm'
  exact hQ m' hm'

theorem kissat_emit_u64_write
    {out x : BitVec 64} {buf : List UInt8} {pos : Nat} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hcap : buf.length < 2 ^ 64) (hfit : pos + (natToBytes x.toNat).length ≤ buf.length)
    (hm : (bytes out buf ⋆ R) m)
    (hQ : ∀ m',
      (bytes out (buf.take pos ++ natToBytes x.toNat ++
        buf.drop (pos + (natToBytes x.toNat).length)) ⋆ R) m' →
      Q (BitVec.ofNat 64 (pos + (natToBytes x.toNat).length), ()) m') :
    Func.wp exportCnfFmtEnv kissat_emit_u64_body
      (out, BitVec.ofNat 64 buf.length, BitVec.ofNat 64 pos, x, ()) m Q X := by
  refine kissat_emit_u64_wp exportCnfFmtEnv
    (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_byte]) _ m Q X ?_
  refine ⟨out, buf, pos, x, R, rfl, hcap, by omega, hm, fun m' _ hm' => ?_⟩
  rw [writeSlice_fit buf pos (natToBytes x.toNat) hfit] at hm'
  exact hQ m' hm'

theorem kissat_emit_dimacs_lit_write
    {out lit : BitVec 64} {buf : List UInt8} {pos : Nat} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hcap : buf.length < 2 ^ 64) (hfit : pos + (emitDimacsLitBytes lit.toNat).length ≤ buf.length)
    (hm : (bytes out buf ⋆ R) m)
    (hQ : ∀ m',
      (bytes out (buf.take pos ++ emitDimacsLitBytes lit.toNat ++
        buf.drop (pos + (emitDimacsLitBytes lit.toNat).length)) ⋆ R) m' →
      Q (BitVec.ofNat 64 (pos + (emitDimacsLitBytes lit.toNat).length), ()) m') :
    Func.wp exportCnfFmtEnv kissat_emit_dimacs_lit_body
      (out, BitVec.ofNat 64 buf.length, BitVec.ofNat 64 pos, lit, ()) m Q X := by
  refine kissat_emit_dimacs_lit_wp exportCnfFmtEnv
    (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_byte])
    (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_u64]) _ m Q X ?_
  refine ⟨out, buf, pos, lit, R, rfl, hcap, by omega, hm, fun m' _ hm' => ?_⟩
  rw [writeSlice_fit buf pos (emitDimacsLitBytes lit.toNat) hfit] at hm'
  exact hQ m' hm'

theorem kissat_emit_dimacs_hdr_write
    {out mv nc : BitVec 64} {buf : List UInt8} {pos : Nat} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hcap : buf.length < 2 ^ 64)
    (hfit : pos + (emitDimacsHdrBytes mv.toNat nc.toNat).length ≤ buf.length)
    (hm : (bytes out buf ⋆ R) m)
    (hQ : ∀ m',
      (bytes out (buf.take pos ++ emitDimacsHdrBytes mv.toNat nc.toNat ++
        buf.drop (pos + (emitDimacsHdrBytes mv.toNat nc.toNat).length)) ⋆ R) m' →
      Q (BitVec.ofNat 64 (pos + (emitDimacsHdrBytes mv.toNat nc.toNat).length), ()) m') :
    Func.wp exportCnfFmtEnv kissat_emit_dimacs_hdr_body
      (out, BitVec.ofNat 64 buf.length, BitVec.ofNat 64 pos, mv, nc, ()) m Q X := by
  refine kissat_emit_dimacs_hdr_wp exportCnfFmtEnv
    (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_byte])
    (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_u64]) _ m Q X ?_
  refine ⟨out, buf, pos, mv, nc, R, rfl, hcap, by omega, hm, fun m' _ hm' => ?_⟩
  rw [writeSlice_fit buf pos (emitDimacsHdrBytes mv.toNat nc.toNat) hfit] at hm'
  exact hQ m' hm'

private theorem bytes_nil_sep_eq (out : BitVec 64) (m : Mem 64) :
    (bytes out [] ⋆ Eq m) m := by
  change (Eq (([] : List UInt8).At out) ⋆ Eq m) m
  rw [← eq_nil_At out, emp_sep]

theorem kissat_emit_byte_dryrun
    {out b : BitVec 64} {pos : Nat} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hpos : pos + 1 < 2 ^ 64)
    (hQ : Q (BitVec.ofNat 64 (pos + 1), ()) m) :
    Func.wp exportCnfFmtEnv kissat_emit_byte_body
      (out, 0#64, BitVec.ofNat 64 pos, b, ()) m Q X :=
  kissat_emit_byte_wp exportCnfFmtEnv _ m Q X
    ⟨out, [], pos, b, Eq m, rfl, by decide, hpos, bytes_nil_sep_eq out m,
      fun m' hmeq _ => (hmeq (Nat.zero_le pos)) ▸ hQ⟩

theorem kissat_emit_u64_dryrun
    {out x : BitVec 64} {pos : Nat} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hpos : pos + (natToBytes x.toNat).length < 2 ^ 64)
    (hQ : Q (BitVec.ofNat 64 (pos + (natToBytes x.toNat).length), ()) m) :
    Func.wp exportCnfFmtEnv kissat_emit_u64_body
      (out, 0#64, BitVec.ofNat 64 pos, x, ()) m Q X :=
  kissat_emit_u64_wp exportCnfFmtEnv
    (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_byte]) _ m Q X
    ⟨out, [], pos, x, Eq m, rfl, by decide, hpos, bytes_nil_sep_eq out m,
      fun m' hmeq _ => (hmeq (Nat.zero_le pos)) ▸ hQ⟩

theorem kissat_emit_dimacs_lit_dryrun
    {out lit : BitVec 64} {pos : Nat} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hpos : pos + (emitDimacsLitBytes lit.toNat).length < 2 ^ 64)
    (hQ : Q (BitVec.ofNat 64 (pos + (emitDimacsLitBytes lit.toNat).length), ()) m) :
    Func.wp exportCnfFmtEnv kissat_emit_dimacs_lit_body
      (out, 0#64, BitVec.ofNat 64 pos, lit, ()) m Q X :=
  kissat_emit_dimacs_lit_wp exportCnfFmtEnv
    (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_byte])
    (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_u64]) _ m Q X
    ⟨out, [], pos, lit, Eq m, rfl, by decide, hpos, bytes_nil_sep_eq out m,
      fun m' hmeq _ => (hmeq (Nat.zero_le pos)) ▸ hQ⟩

theorem kissat_emit_dimacs_hdr_dryrun
    {out mv nc : BitVec 64} {pos : Nat} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hpos : pos + (emitDimacsHdrBytes mv.toNat nc.toNat).length < 2 ^ 64)
    (hQ : Q (BitVec.ofNat 64 (pos + (emitDimacsHdrBytes mv.toNat nc.toNat).length), ()) m) :
    Func.wp exportCnfFmtEnv kissat_emit_dimacs_hdr_body
      (out, 0#64, BitVec.ofNat 64 pos, mv, nc, ()) m Q X :=
  kissat_emit_dimacs_hdr_wp exportCnfFmtEnv
    (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_byte])
    (fun _ _ _ _ h => by rwa [exportCnfFmtEnv_u64]) _ m Q X
    ⟨out, [], pos, mv, nc, Eq m, rfl, by decide, hpos, bytes_nil_sep_eq out m,
      fun m' hmeq _ => (hmeq (Nat.zero_le pos)) ▸ hQ⟩

end

end LeanQbe.T.Examples.Kissat.ExportCnfFmt
