module

public import LeanQbe.Examples.LratBytes
public import LeanQbe.Examples.LratRupLemmas
public import LeanQbe.AbiLemmas
public import Kraken.Bedrock2.Test.LratTrimCheckProof
import all Kraken.Mem
import all Kraken.Separation

/-!
# Shared specifications, pure executable mirror, and `region` lemmas for `LratBytes`

Defines:
1. `lratBytesFns_wf`: well-formedness (`Func.Wf`) of all 6 functions in `lratBytesFns`.
2. `loadub_At` and `region` ↔ `byte1Array` / `int4Array` / `word8Array` / `ZeroTermInts` bridges.
3. The 100% structurally recursive pure mirror `runLratCheckBytes` (`parseBodyPure`,
   `readLeb128Pure`, `readAddLitsPure`, `rupCheckPure`, `checkPrfPure`).
4. `WorkCfg`, `WorkState`, and the exact contracts for all 5 internal callees
   (`lbParseDimacsHeaderSpec`, `lbParseDimacsBodySpec`, `lbReadAddLitsSpec`,
   `lbRupCheckSpec`, `lbCheckPrfSpec`) plus `lratCheckBytesExactSpec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.LratBytes

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT.Internal
open Kraken.Bedrock2.Test
open LeanQbe.LratRup

/-! ## 1. Well-formedness of `lratBytesFns` -/

theorem lbParseDimacsHeader_wf : Func.Wf lbParseDimacsHeader := by
  unfold lbParseDimacsHeader skipWsCommentsQbe skipWs1Qbe readDimacsNat isWsByte; wf_tac

theorem lbParseDimacsBody_wf : Func.Wf lbParseDimacsBody := by
  unfold lbParseDimacsBody skipWsCommentsQbe readDimacsNat isWsByte; wf_tac

theorem lbReadAddLits_wf : Func.Wf lbReadAddLits := by
  unfold lbReadAddLits readLeb128; wf_tac

theorem lbRupCheck_wf : Func.Wf lbRupCheck := by
  unfold lbRupCheck rupPhase1 rupInner readLeb128 assignedLit assignLitChecked backtrack; wf_tac

theorem lbCheckPrf_wf : Func.Wf lbCheckPrf := by
  unfold lbCheckPrf readLeb128; wf_tac

theorem lratCheckBytes_wf : Func.Wf lratCheckBytes := by
  unfold lratCheckBytes; wf_tac

theorem lratBytesFns_wf : ∀ f ∈ lratBytesFns, Func.Wf f.body := by
  intro f hf
  simp only [lratBytesFns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lbParseDimacsHeader_wf
  · exact lbParseDimacsBody_wf
  · exact lbReadAddLits_wf
  · exact lbRupCheck_wf
  · exact lbCheckPrf_wf
  · exact lratCheckBytes_wf

/-! ## 2. Byte-stream `loadub` and `region` ↔ Kraken array bridges -/

theorem toBytes_u8 (b : UInt8) : Int.toBytes 1 (b.toNat : Int) = [b] := by
  have hb := b.toNat_lt
  simp only [Int.toBytes, Int.take]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  simp

theorem loadub_At {base : Val} {bs : List UInt8} {i : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i < bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (Eq (bs.At base) ⋆ R) m) :
    loadVal m .l .b false (base + BitVec.ofNat 64 i) = some (BitVec.ofNat 64 bs[i].toNat) := by
  have hsplit : bs = bs.take i ++ ([bs[i]] ++ bs.drop (i + 1)) := by
    rw [List.singleton_append, ← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have heq : Eq (bs.At base) =
      (Eq ((Int.toBytes 1 (bs[i].toNat : Int)).At (base + BitVec.ofNat 64 i)) ⋆
        (Eq ((bs.take i).At base) ⋆
          Eq ((bs.drop (i + 1)).At (base + BitVec.ofNat 64 i + 1)))) := by
    conv => lhs; rw [hsplit]
    rw [eq_append_At base (bs.take i) ([bs[i]] ++ bs.drop (i + 1))
          (by simp [List.length_take_of_le (Nat.le_of_lt hi)]; omega),
        List.length_take_of_le (Nat.le_of_lt hi),
        eq_append_At (base + BitVec.ofNat 64 i) [bs[i]] (bs.drop (i + 1))
          (by simp; omega),
        toBytes_u8]
    simp only [List.length_singleton]
    ac_rfl
  have hm' : (Eq ((Int.toBytes 1 (bs[i].toNat : Int)).At (base + BitVec.ofNat 64 i)) ⋆
      ((Eq ((bs.take i).At base) ⋆ Eq ((bs.drop (i + 1)).At (base + BitVec.ofNat 64 i + 1))) ⋆ R)) m := by
    rw [heq] at hm; exact sep_cast hm (by ac_rfl)
  rw [loadVal_toBytes (s := .b) hm']
  have hb := bs[i].toNat_lt
  simp only [Sz.bytes, Int.take, Cls.trunc, Sz.extend]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  exact congrArg some (BitVec.eq_of_toNat_eq (by simp))

theorem byte1Array_to_region {a : Val} {xs : List Val} {f : Mem 64}
    (h : xs.length ≤ 2 ^ 64) (hf : byte1Array a xs f) :
    region a xs.length f := by
  rw [byte1Array_eq a xs h] at hf
  exact ⟨bytesN 1 xs, by simp [bytesN_length], hf.symm⟩

theorem int4Array_to_region {a : Val} {xs : List Val} {f : Mem 64}
    (h : 4 * xs.length ≤ 2 ^ 64) (hf : int4Array a xs f) :
    region a (4 * xs.length) f := by
  rw [int4Array_eq a xs h] at hf
  exact ⟨bytesN 4 xs, by simp [bytesN_length], hf.symm⟩

theorem word8Array_to_region {a : Val} {xs : List Val} {f : Mem 64}
    (h : 8 * xs.length ≤ 2 ^ 64) (hf : word8Array a xs f) :
    region a (8 * xs.length) f := by
  rw [word8Array_eq a xs h] at hf
  exact ⟨bytesN 8 xs, by simp [bytesN_length], hf.symm⟩

theorem zeroTermInts_to_region {a : Val} {xs : List Val} {f : Mem 64}
    (h : 4 * (xs.length + 1) ≤ 2 ^ 64) (hf : ZeroTermInts a xs f) :
    region a (4 * (xs.length + 1)) f := by
  unfold ZeroTermInts at hf
  have hr := int4Array_to_region (by simpa using h) hf
  simpa using hr

private theorem toBytes_ofBytes_toNat {n : Nat} {bs : List UInt8}
    (hn : n = 1 ∨ n = 4 ∨ n = 8) (hl : bs.length = n) :
    Int.toBytes n ((BitVec.ofInt 64 (Int.ofBytes bs)).toNat : Int) = bs := by
  rw [← Int.toBytes_emod]
  have hdvd : (2 ^ (8 * n) : Int) ∣ ((2 ^ 64 : Nat) : Int) := by
    rcases hn with rfl | rfl | rfl <;> decide
  have hdvd2 : (2 ^ (8 * n) : Int) ∣ (2 ^ 64 : Int) := by
    rcases hn with rfl | rfl | rfl <;> decide
  have h1 : ((BitVec.ofInt 64 (Int.ofBytes bs)).toNat : Int).take (8 * n) =
      (Int.ofBytes bs).take (8 * n) := by
    simp only [Int.take]
    rw [← BitVec.toInt_emod_two_pow, Int.emod_emod_of_dvd _ hdvd2, BitVec.toInt_ofInt,
        ← Int.emod_emod_of_dvd _ hdvd, Int.bmod_emod, Int.emod_emod_of_dvd _ hdvd]
  rw [h1, Int.toBytes_emod, ← hl]
  exact Int.toBytes_ofBytes_all bs

theorem region_to_byte1Array {a : Val} (k : Nat) (hk : k ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a k f) :
    ∃ xs : List Val, xs.length = k ∧ byte1Array a xs f := by
  induction k generalizing a f with
  | zero =>
    rw [region_zero] at hf
    exact ⟨[], rfl, hf⟩
  | succ k ih =>
    have hsp : region a (1 + k) f := by simpa [Nat.add_comm] using hf
    rw [region_split (by omega)] at hsp
    obtain ⟨f1, f2, hu, hd, ⟨bs1, hl1, rfl⟩, hf2⟩ := hsp
    obtain ⟨xs, hxs, h2⟩ := ih (by omega) hf2
    let v : Val := BitVec.ofInt 64 (Int.ofBytes bs1)
    have hv : byte1 a v (bs1.At a) := by
      show (Int.toBytes 1 v.toNat).At a = bs1.At a
      rw [toBytes_ofBytes_toNat (Or.inl rfl) hl1]
    exact ⟨v :: xs, by simp [hxs], _, _, hu, hd, hv, h2⟩

theorem region_to_int4Array {a : Val} (k : Nat) (hk : 4 * k ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a (4 * k) f) :
    ∃ xs : List Val, xs.length = k ∧ int4Array a xs f := by
  induction k generalizing a f with
  | zero =>
    simp only [Nat.mul_zero, region_zero] at hf
    exact ⟨[], rfl, hf⟩
  | succ k ih =>
    have hsp : region a (4 + 4 * k) f := by
      have : 4 * (k + 1) = 4 + 4 * k := by omega
      rwa [this] at hf
    rw [region_split (by omega)] at hsp
    obtain ⟨f1, f2, hu, hd, ⟨bs1, hl1, rfl⟩, hf2⟩ := hsp
    obtain ⟨xs, hxs, h2⟩ := ih (by omega) hf2
    let v : Val := BitVec.ofInt 64 (Int.ofBytes bs1)
    have hv : int4 a v (bs1.At a) := by
      show (Int.toBytes 4 v.toNat).At a = bs1.At a
      rw [toBytes_ofBytes_toNat (Or.inr (Or.inl rfl)) hl1]
    exact ⟨v :: xs, by simp [hxs], _, _, hu, hd, hv, h2⟩

theorem region_to_word8Array {a : Val} (k : Nat) (hk : 8 * k ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a (8 * k) f) :
    ∃ xs : List Val, xs.length = k ∧ word8Array a xs f := by
  induction k generalizing a f with
  | zero =>
    simp only [Nat.mul_zero, region_zero] at hf
    exact ⟨[], rfl, hf⟩
  | succ k ih =>
    have hsp : region a (8 + 8 * k) f := by
      have : 8 * (k + 1) = 8 + 8 * k := by omega
      rwa [this] at hf
    rw [region_split (by omega)] at hsp
    obtain ⟨f1, f2, hu, hd, ⟨bs1, hl1, rfl⟩, hf2⟩ := hsp
    obtain ⟨xs, hxs, h2⟩ := ih (by omega) hf2
    let v : Val := BitVec.ofInt 64 (Int.ofBytes bs1)
    have hv : word8 a v (bs1.At a) := by
      show (Int.toBytes 8 v.toNat).At a = bs1.At a
      rw [toBytes_ofBytes_toNat (Or.inr (Or.inr rfl)) hl1]
    exact ⟨v :: xs, by simp [hxs], _, _, hu, hd, hv, h2⟩

/-! ## 3. Pure executable mirror (`runLratCheckBytes`) -/

/-- Structural mirror of `@lit_loop` in `lbParseDimacsBody`. -/
def parseClausePure : Nat → Nat → Nat → List Val → List UInt8 →
    Option (List Val × Nat × List UInt8)
  | 0, _, _, _, _ => none
  | fuel + 1, mv, poolRem, acc, bs =>
    match skipWsComments bs with
    | [] => none
    | 45 :: rest =>
      if poolRem == 0 then none
      else match parseNat rest with
      | none => none
      | some (v, rest') =>
        if v == 0 || mv < v then none
        else parseClausePure fuel mv (poolRem - 1) (-BitVec.ofNat 64 v :: acc) rest'
    | b :: rest =>
      if poolRem == 0 then none
      else match parseNat (b :: rest) with
      | none => none
      | some (v, rest') =>
        if v == 0 then some (acc.reverse, poolRem - 1, rest')
        else if mv < v then none
        else parseClausePure fuel mv (poolRem - 1) (BitVec.ofNat 64 v :: acc) rest'

/-- Structural mirror of `@cl_loop` in `lbParseDimacsBody`. -/
def parseBodyPure (mv : Nat) : Nat → Nat → List (List Val) → List UInt8 →
    Option (List (List Val) × Nat)
  | 0, poolRem, revClauses, bs =>
    if (skipWsComments bs).isEmpty then some (revClauses.reverse, poolRem) else none
  | k + 1, poolRem, revClauses, bs => do
    let (clits, poolRem', bs') ← parseClausePure (bs.length + 1) mv poolRem [] bs
    parseBodyPure mv k poolRem' (clits :: revClauses) bs'

/-- Structural mirror of `readLeb128` (1..4 bytes, `< 2^28`). -/
def readLeb128Aux : Nat → Nat → Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | fuel + 1, acc, sh, b :: bs =>
    let acc2 := acc ||| ((b.toNat &&& 127) <<< sh)
    if (b.toNat &&& 128) != 0 then
      let sh2 := sh + 7
      if sh2 < 28 then readLeb128Aux fuel acc2 sh2 bs else none
    else
      some (acc2, bs)

def readLeb128Pure (bs : List UInt8) : Option (Nat × List UInt8) :=
  readLeb128Aux 4 0 0 bs

/-- Decode non-zero zig-zag integer `u` (`v = u / 2`, negative iff `u % 2 == 1`). -/
def decodeZigZag (u : Nat) : Val :=
  let v : Val := BitVec.ofNat 64 (u / 2)
  if u % 2 == 1 then -v else v

/-- Structural mirror of `lbReadAddLits`. -/
def readAddLitsAux : Nat → Nat → Nat → List Val → List UInt8 →
    Option (List Val × Nat × List UInt8)
  | 0, _, _, _, _ => none
  | fuel + 1, mv, poolRem, acc, bs =>
    if poolRem == 0 then none
    else match readLeb128Pure bs with
    | none => none
    | some (0, bs') => some (acc.reverse, poolRem - 1, bs')
    | some (u, bs') =>
      let v := u / 2
      if v == 0 || mv < v then none
      else readAddLitsAux fuel mv (poolRem - 1) (decodeZigZag u :: acc) bs'

def readAddLitsPure (mv poolRem : Nat) (bs : List UInt8) :
    Option (List Val × Nat × List UInt8) :=
  readAddLitsAux (bs.length + 1) mv poolRem [] bs

/-- Outcome of `rupPhase1`. -/
inductive Phase1Res
  | fail
  | taut
  | ok (vals : List Val) (trailLen : Nat)

/-- Structural mirror of `rupPhase1` over `vals : List Val` (`length = mv + 1`). -/
def rupPhase1Pure (mv : Nat) : List Val → List Val → Nat → Phase1Res
  | [], vals, trailLen => .ok vals trailLen
  | lit :: lits, vals, trailLen =>
    let idx := (bvAbs lit).toNat
    let val := evalAssignedLit (vals.getD idx 0) lit
    if val.slt 0 then
      rupPhase1Pure mv lits vals trailLen
    else if (0 : Val).slt val then
      .taut
    else if trailLen == mv + 1 then
      .fail
    else
      let nlit := -lit
      let vals' := vals.set idx (bvSignByte nlit)
      rupPhase1Pure mv lits vals' (trailLen + 1)

/-- Structural mirror of `rupInner` over `vals : List Val`. -/
def rupInnerPure (mv : Nat) : List Val → Val → List Val → Nat →
    Option (Val × List Val × Nat)
  | [], unit, vals, trailLen => some (unit, vals, trailLen)
  | lit :: lits, unit, vals, trailLen =>
    let idx := (bvAbs lit).toNat
    let val := evalAssignedLit (vals.getD idx 0) lit
    if val.slt 0 then
      if unit == -lit then none
      else rupInnerPure mv lits unit vals trailLen
    else
      let stepUnit : Option (Val × List Val × Nat) :=
        if val == 0 then
          if trailLen == mv + 1 then none
          else
            let vals' := vals.set idx (bvSignByte lit)
            rupInnerPure mv lits lit vals' (trailLen + 1)
        else
          rupInnerPure mv lits lit vals trailLen
      if lo32 unit != 0 then
        if unit == lit then stepUnit else none
      else
        stepUnit

/-- Structural mirror of `@consume` in `lbRupCheck`. -/
def consumeHintsAux : Nat → Nat → List (Option (List Val)) → List UInt8 → Option (List UInt8)
  | 0, _, _, _ => none
  | fuel + 1, id, table, bs =>
    match readLeb128Pure bs with
    | none => none
    | some (0, bs') => some bs'
    | some (u, bs') =>
      if u % 2 != 0 then none
      else
        let aid := u / 2
        if aid < id then
          match table[aid]? with
          | some (some _) => consumeHintsAux fuel id table bs'
          | _ => none
        else none

def consumeHintsPure (id : Nat) (table : List (Option (List Val))) (bs : List UInt8) :
    Option (List UInt8) :=
  consumeHintsAux (bs.length + 1) id table bs

/-- Structural mirror of `@ph2` in `lbRupCheck`. -/
def rupPhase2Aux : Nat → Nat → Nat → List (Option (List Val)) → List Val → Nat →
    List UInt8 → Option (List UInt8)
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, mv, id, table, vals, trailLen, bs =>
    match readLeb128Pure bs with
    | none => none
    | some (0, _) => none
    | some (u, bs') =>
      if u % 2 != 0 then none
      else
        let aid := u / 2
        if aid < id then
          match table[aid]? with
          | some (some alits) =>
            match rupInnerPure mv alits 0 vals trailLen with
            | none => none
            | some (unit, vals', trailLen') =>
              if lo32 unit != 0 then
                rupPhase2Aux fuel mv id table vals' trailLen' bs'
              else
                consumeHintsPure id table bs'
          | _ => none
        else none

/-- Structural mirror of `lbRupCheck`. -/
def rupCheckPure (mv id : Nat) (clits : List Val) (table : List (Option (List Val)))
    (bs : List UInt8) : Option (List UInt8) :=
  match rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 with
  | .fail => none
  | .taut => consumeHintsPure id table bs
  | .ok vals trailLen => rupPhase2Aux (bs.length + 1) mv id table vals trailLen bs

/-- Structural mirror of `@del_loop` in `lbCheckPrf`. -/
def delLoopAux : Nat → Nat → List (Option (List Val)) → List UInt8 →
    Option (List (Option (List Val)) × List UInt8)
  | 0, _, _, _ => none
  | fuel + 1, cap, table, bs =>
    match readLeb128Pure bs with
    | none => none
    | some (0, bs') => some (table, bs')
    | some (u, bs') =>
      if u % 2 != 0 then none
      else
        let did := u / 2
        if did == 0 || !(did < cap) then none
        else match table[did]? with
        | some (some _) => delLoopAux fuel cap (table.set did none) bs'
        | _ => none

/-- Structural mirror of `lbCheckPrf`. -/
def checkPrfAux : Nat → Nat → Nat → Nat → List (Option (List Val)) → List UInt8 → Bool
  | 0, _, _, _, _, _ => false
  | _, _, _, _, _, [] => false
  | fuel + 1, mv, nc, poolRem, table, tag :: bs1 =>
    let cap := table.length
    if tag == 97 then
      match readLeb128Pure bs1 with
      | none => false
      | some (uid, bs2) =>
        if uid % 2 != 0 then false
        else
          let id := uid / 2
          if !(nc < id) || !(id < cap) then false
          else match table[id]? with
          | some none =>
            match readAddLitsPure mv poolRem bs2 with
            | none => false
            | some (clits, poolRem', bs3) =>
              match rupCheckPure mv id clits table bs3 with
              | none => false
              | some bs4 =>
                if clits.isEmpty then true
                else checkPrfAux fuel mv nc poolRem' (table.set id (some clits)) bs4
          | _ => false
    else if tag == 100 then
      match delLoopAux (bs1.length + 1) cap table bs1 with
      | none => false
      | some (table', bs2) => checkPrfAux fuel mv nc poolRem table' bs2
    else false

def checkPrfPure (mv nc poolRem : Nat) (table : List (Option (List Val)))
    (bs : List UInt8) : Bool :=
  checkPrfAux (bs.length + 1) mv nc poolRem table bs

/-- Initial `List (Option (List Val))` table of length `cap` (`none` at `0`, `some cl` at `1..nc`,
`none` at `nc + 1 .. cap - 1`). -/
def initClauseTable (cap : Nat) (clauses : List (List Val)) : List (Option (List Val)) :=
  none :: clauses.map some ++ List.replicate (cap - (clauses.length + 1)) none

/-- Total executable mirror of `lrat_check_bytes(cnfBytes, prfBytes, work_len)`. -/
def runLratCheckBytes (cnfBytes prfBytes : List UInt8) (work_len : Nat) : Bool :=
  if work_len < 128 then false
  else match parseHeader cnfBytes with
  | none => false
  | some (mv, nc, bodyRest) =>
    let v_bytes := ((mv + 8) / 8) * 8
    let t_raw := 4 * (mv + 1)
    let t_bytes := ((t_raw + 7) / 8) * 8
    let fixed := 80 + v_bytes + t_bytes
    if work_len < fixed then false
    else
      let rem := work_len - fixed
      let c_half := rem / 16
      let p_cap := prfBytes.length % 268435456
      let want := nc + p_cap + 32
      let cap := if c_half < want then c_half else want
      if cap ≤ nc then false
      else
        let cb_bytes := 8 * cap
        let pool_rem := rem - cb_bytes
        let pool_ints := pool_rem / 4
        match parseBodyPure mv nc pool_ints [] bodyRest with
        | none => false
        | some (clauses, pool_ints') =>
          checkPrfPure mv nc pool_ints' (initClauseTable cap clauses) prfBytes

/-! ## 4. Workspace layout invariant (`WorkCfg`, `WorkState`) and exact contracts -/

/-- Static workspace geometry computed by `lrat_check_bytes` after `lb_parse_dimacs_header`. -/
structure WorkCfg where
  hdr : Val
  mv : Nat
  nc : Nat
  cap : Nat
  poolInts : Nat
  hmv : mv < dimacsBound
  hnc : nc < dimacsBound
  hnc_cap : nc < cap
  hfit : hdr.toNat + (80 + ((mv + 8) / 8) * 8 + ((4 * (mv + 1) + 7) / 8) * 8 +
    8 * cap + 4 * poolInts) < 2 ^ 64

namespace WorkCfg

def vBytes (c : WorkCfg) : Nat := ((c.mv + 8) / 8) * 8
def tRaw (c : WorkCfg) : Nat := 4 * (c.mv + 1)
def tBytes (c : WorkCfg) : Nat := ((c.tRaw + 7) / 8) * 8
def activeBytes (c : WorkCfg) : Nat := 80 + c.vBytes + c.tBytes + 8 * c.cap + 4 * c.poolInts

def vb (c : WorkCfg) : Val := c.hdr + 80
def tb (c : WorkCfg) : Val := c.vb + BitVec.ofNat 64 c.vBytes
def tlim (c : WorkCfg) : Val := c.tb + BitVec.ofNat 64 c.tRaw
def cb (c : WorkCfg) : Val := c.tb + BitVec.ofNat 64 c.tBytes
def pbase (c : WorkCfg) : Val := c.cb + BitVec.ofNat 64 (8 * c.cap)
def plim (c : WorkCfg) : Val := c.pbase + BitVec.ofNat 64 (4 * c.poolInts)

def hdrWords (c : WorkCfg) (pcur cur : Val) : List Val :=
  [BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, BitVec.ofNat 64 c.cap,
   c.vb, c.tb, c.tlim, c.cb, c.plim, pcur, cur]

end WorkCfg

/-- Agreement between physical `ptrs : List Val`, logical `table : List (Option (List Val))`,
and `PoolUsed : Mem 64 → Prop`. -/
def TableRel (mv cap : Nat) (ptrs : List Val) (table : List (Option (List Val)))
    (PoolUsed : Mem 64 → Prop) : Prop :=
  ∃ (hplen : ptrs.length = cap) (htlen : table.length = cap),
    ∀ i (hi : i < cap),
      match table[i]'(htlen ▸ hi) with
      | none => ptrs[i]'(hplen ▸ hi) = 0
      | some lits =>
        ptrs[i]'(hplen ▸ hi) ≠ 0 ∧
        (∀ x ∈ lits, IsValidLit mv x) ∧
        (∃ R, PoolUsed = (ZeroTermInts (ptrs[i]'(hplen ▸ hi)) lits ⋆ R))

/-- Full workspace memory state over `[c.hdr, c.hdr + c.activeBytes)`. -/
def WorkState (c : WorkCfg) (poolUsedInts poolRemInts : Nat) (cur : Val)
    (ptrs : List Val) (table : List (Option (List Val))) (PoolUsed : Mem 64 → Prop) :
    Mem 64 → Prop := fun m =>
  poolUsedInts + poolRemInts = c.poolInts ∧
  TableRel c.mv c.cap ptrs table PoolUsed ∧
  (∀ f, PoolUsed f → region c.pbase (4 * poolUsedInts) f) ∧
  let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsedInts)
  (word8Array c.hdr (c.hdrWords pcur cur) ⋆
    byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
    region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
    region c.tb c.tRaw ⋆
    region c.tlim (c.tBytes - c.tRaw) ⋆
    word8Array c.cb ptrs ⋆
    PoolUsed ⋆
    region pcur (4 * poolRemInts)) m

theorem sep_mono2 {P1 P1' P2 P2' : Mem 64 → Prop}
    (h1 : ∀ f, P1 f → P1' f) (h2 : ∀ f, P2 f → P2' f) :
    ∀ f, (P1 ⋆ P2) f → (P1' ⋆ P2') f :=
  fun _ h => sep_mono h1 (sep_mono_r h2 h)

/-- Any `WorkState` collapses back into `region c.hdr c.activeBytes`. -/
theorem WorkState.to_region {c : WorkCfg} {poolUsedInts poolRemInts : Nat} {cur : Val}
    {ptrs : List Val} {table : List (Option (List Val))} {PoolUsed : Mem 64 → Prop} {m : Mem 64}
    (h : WorkState c poolUsedInts poolRemInts cur ptrs table PoolUsed m) :
    region c.hdr c.activeBytes m := by
  obtain ⟨hsum, ⟨hplen, _, _⟩, hpu, hm⟩ := h
  have hfit := c.hfit
  have hmv := c.hmv
  unfold dimacsBound at hmv
  have hvb : c.mv + 1 ≤ c.vBytes := by unfold WorkCfg.vBytes; omega
  have htb : c.tRaw ≤ c.tBytes := by unfold WorkCfg.tBytes; omega
  dsimp only at hm
  let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsedInts)
  have r_hdr : ∀ f, word8Array c.hdr (c.hdrWords pcur cur) f → region c.hdr 80 f := fun f hf => by
    have := word8Array_to_region (by simp [WorkCfg.hdrWords]) hf
    simpa [WorkCfg.hdrWords] using this
  have r_val : ∀ f, byte1Array c.vb (assignBytes c.mv Assignment.empty) f →
      region c.vb (c.mv + 1) f := fun f hf => by
    have := byte1Array_to_region (by simp; omega) hf
    simpa using this
  have r_cb : ∀ f, word8Array c.cb ptrs f → region c.cb (8 * c.cap) f := fun f hf => by
    have := word8Array_to_region (by rw [hplen]; unfold WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *; omega) hf
    rwa [hplen] at this
  have hm1 : (region c.hdr 80 ⋆
      region c.vb (c.mv + 1) ⋆
      region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
      region c.tb c.tRaw ⋆
      region c.tlim (c.tBytes - c.tRaw) ⋆
      region c.cb (8 * c.cap) ⋆
      region c.pbase (4 * poolUsedInts) ⋆
      region pcur (4 * poolRemInts)) m :=
    sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
      r_hdr r_val) (fun _ h => h)) (fun _ h => h)) (fun _ h => h)) r_cb) hpu) (fun _ h => h) m hm
  have e_pool : (region c.pbase (4 * poolUsedInts) ⋆ region pcur (4 * poolRemInts)) =
      region c.pbase (4 * c.poolInts) := by
    have : 4 * c.poolInts = 4 * poolUsedInts + 4 * poolRemInts := by omega
    rw [this, region_split (by omega)]
  have e_cb : (region c.cb (8 * c.cap) ⋆ region c.pbase (4 * c.poolInts)) =
      region c.cb (8 * c.cap + 4 * c.poolInts) := by
    conv => rhs; rw [region_split (by unfold WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *; omega)]
    rfl
  have e_t : (region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw)) = region c.tb c.tBytes := by
    have : c.tBytes = c.tRaw + (c.tBytes - c.tRaw) := by omega
    conv => rhs; rw [this, region_split (by unfold WorkCfg.tBytes WorkCfg.tRaw at *; omega)]
    rfl
  have e_v : (region c.vb (c.mv + 1) ⋆
      region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1))) =
      region c.vb c.vBytes := by
    have : c.vBytes = (c.mv + 1) + (c.vBytes - (c.mv + 1)) := by omega
    conv => rhs; rw [this, region_split (by unfold WorkCfg.vBytes at *; omega)]
  have hm2 : (region c.hdr 80 ⋆
      ((region c.vb (c.mv + 1) ⋆ region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1))) ⋆
        ((region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw)) ⋆
          (region c.cb (8 * c.cap) ⋆ (region c.pbase (4 * poolUsedInts) ⋆ region pcur (4 * poolRemInts)))))) m :=
    sep_cast hm1 (by ac_rfl)
  rw [e_v, e_t, e_pool, e_cb] at hm2
  have e_tcb : (region c.tb c.tBytes ⋆ region c.cb (8 * c.cap + 4 * c.poolInts)) =
      region c.tb (c.tBytes + (8 * c.cap + 4 * c.poolInts)) := by
    conv => rhs; rw [region_split (by unfold WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *; omega)]
    rfl
  have e_vtcb : (region c.vb c.vBytes ⋆ region c.tb (c.tBytes + (8 * c.cap + 4 * c.poolInts))) =
      region c.vb (c.vBytes + (c.tBytes + (8 * c.cap + 4 * c.poolInts))) := by
    conv => rhs; rw [region_split (by unfold WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *; omega)]
    rfl
  have e_all : (region c.hdr 80 ⋆ region c.vb (c.vBytes + (c.tBytes + (8 * c.cap + 4 * c.poolInts)))) =
      region c.hdr c.activeBytes := by
    have : c.activeBytes = 80 + (c.vBytes + (c.tBytes + (8 * c.cap + 4 * c.poolInts))) := by
      unfold WorkCfg.activeBytes; omega
    conv => rhs; rw [this, region_split (by unfold WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *; omega)]
    rfl
  rwa [e_tcb, e_vtcb, e_all] at hm2

/-! ### Exact callee contracts -/

/-- Exact contract for `lb_parse_dimacs_header(cnf_ptr, cnf_end, hdr)`. -/
def lbParseDimacsHeaderSpec : Spec := fun args m Q _ =>
  ∃ (cnf_ptr hdr : Val) (cnfBytes : List UInt8) (R : Mem 64 → Prop),
    args = [cnf_ptr, cnf_ptr + BitVec.ofNat 64 cnfBytes.length, hdr] ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    hdr.toNat + 80 < 2 ^ 64 ∧
    (Eq (cnfBytes.At cnf_ptr) ⋆ region hdr 80 ⋆ R) m ∧
    ∀ (r : Val) (m' : Mem 64),
      (match parseHeader cnfBytes with
       | none =>
         r = 0 ∧ (Eq (cnfBytes.At cnf_ptr) ⋆ region hdr 80 ⋆ R) m'
       | some (mv, nc, rest) =>
         r = 1 ∧ mv < dimacsBound ∧ nc < dimacsBound ∧
         rest = cnfBytes.drop (cnfBytes.length - rest.length) ∧
         rest.length ≤ cnfBytes.length ∧
         ∃ w2 w3 w4 w5 w6 w7 w8 : Val,
           (Eq (cnfBytes.At cnf_ptr) ⋆
             word8Array hdr
               [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc, w2, w3, w4, w5, w6, w7, w8,
                cnf_ptr + BitVec.ofNat 64 (cnfBytes.length - rest.length)] ⋆ R) m') →
      Q [r] m'

/-- Exact contract for `lb_parse_dimacs_body(cnf_end, hdr)`. -/
def lbParseDimacsBodySpec : Spec := fun args m Q _ =>
  ∃ (c : WorkCfg) (cnf_ptr : Val) (cnfBytes : List UInt8) (idx0 : Nat)
    (R : Mem 64 → Prop),
    args = [cnf_ptr + BitVec.ofNat 64 cnfBytes.length, c.hdr] ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    idx0 ≤ cnfBytes.length ∧
    (Eq (cnfBytes.At cnf_ptr) ⋆
      WorkState c 0 c.poolInts (cnf_ptr + BitVec.ofNat 64 idx0)
        (List.replicate c.cap 0) (List.replicate c.cap none) emp ⋆ R) m ∧
    ∀ (r : Val) (m' : Mem 64),
      (match parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) with
       | none =>
         r = 0 ∧ (Eq (cnfBytes.At cnf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m'
       | some (clauses, poolRem') =>
         r = 1 ∧ clauses.length = c.nc ∧ poolRem' ≤ c.poolInts ∧
         ∃ (ptrs : List Val) (PoolUsed : Mem 64 → Prop),
           (Eq (cnfBytes.At cnf_ptr) ⋆
             WorkState c (c.poolInts - poolRem') poolRem'
               (cnf_ptr + BitVec.ofNat 64 idx0)
               ptrs (initClauseTable c.cap clauses) PoolUsed ⋆ R) m') →
      Q [r] m'

/-- Exact contract for `lb_read_add_lits(hdr, prf_end)`. -/
def lbReadAddLitsSpec : Spec := fun args m Q _ =>
  ∃ (c : WorkCfg) (prf_ptr : Val) (prfBytes : List UInt8) (idx0 poolUsed poolRem : Nat)
    (ptrs : List Val) (table : List (Option (List Val))) (PoolUsed R : Mem 64 → Prop),
    args = [c.hdr, prf_ptr + BitVec.ofNat 64 prfBytes.length] ∧
    prf_ptr.toNat + prfBytes.length < 2 ^ 64 ∧
    idx0 ≤ prfBytes.length ∧
    (Eq (prfBytes.At prf_ptr) ⋆
      WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx0) ptrs table PoolUsed ⋆ R) m ∧
    ∀ (r : Val) (m' : Mem 64),
      (match readAddLitsPure c.mv poolRem (prfBytes.drop idx0) with
       | none =>
         r = 0 ∧ (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m'
       | some (clits, poolRem', bs') =>
         let c_ptr := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
         let idx' := prfBytes.length - bs'.length
         r = (if clits.isEmpty then 2 else 1) ∧
         bs' = prfBytes.drop idx' ∧ idx' ≤ prfBytes.length ∧
         clits.length + 1 + poolRem' = poolRem ∧
         c_ptr ≠ 0 ∧
         (∀ x ∈ clits, IsValidLit c.mv x) ∧
         (Eq (prfBytes.At prf_ptr) ⋆
           WorkState c (poolUsed + (clits.length + 1)) poolRem'
             (prf_ptr + BitVec.ofNat 64 idx')
             ptrs table (PoolUsed ⋆ ZeroTermInts c_ptr clits) ⋆ R) m') →
      Q [r] m'

/-- Exact contract for `lb_rup_check(hdr, id, c_ptr, prf_end)`. -/
def lbRupCheckSpec : Spec := fun args m Q _ =>
  ∃ (c : WorkCfg) (id : Nat) (c_ptr prf_ptr : Val) (prfBytes : List UInt8)
    (idx0 poolUsed poolRem : Nat) (clits ptrs : List Val)
    (table : List (Option (List Val))) (PoolUsed R : Mem 64 → Prop),
    args = [c.hdr, BitVec.ofNat 64 id, c_ptr, prf_ptr + BitVec.ofNat 64 prfBytes.length] ∧
    id < c.cap ∧
    prf_ptr.toNat + prfBytes.length < 2 ^ 64 ∧
    idx0 ≤ prfBytes.length ∧
    (∀ x ∈ clits, IsValidLit c.mv x) ∧
    (∃ R_c, PoolUsed = (ZeroTermInts c_ptr clits ⋆ R_c)) ∧
    (Eq (prfBytes.At prf_ptr) ⋆
      WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx0) ptrs table PoolUsed ⋆ R) m ∧
    ∀ (r : Val) (m' : Mem 64),
      (match rupCheckPure c.mv id clits table (prfBytes.drop idx0) with
       | none =>
         r = 0 ∧ (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m'
       | some bs' =>
         let idx' := prfBytes.length - bs'.length
         r = 1 ∧ bs' = prfBytes.drop idx' ∧ idx' ≤ prfBytes.length ∧
         (Eq (prfBytes.At prf_ptr) ⋆
           WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx')
             ptrs table PoolUsed ⋆ R) m') →
      Q [r] m'

/-- Exact contract for `lb_check_prf(hdr, prf_end)`. -/
def lbCheckPrfSpec : Spec := fun args m Q _ =>
  ∃ (c : WorkCfg) (prf_ptr : Val) (prfBytes : List UInt8) (poolUsed poolRem : Nat)
    (ptrs : List Val) (table : List (Option (List Val))) (PoolUsed R : Mem 64 → Prop),
    args = [c.hdr, prf_ptr + BitVec.ofNat 64 prfBytes.length] ∧
    prf_ptr.toNat + prfBytes.length < 2 ^ 64 ∧
    (Eq (prfBytes.At prf_ptr) ⋆
      WorkState c poolUsed poolRem prf_ptr ptrs table PoolUsed ⋆ R) m ∧
    ∀ (r : Val) (m' : Mem 64),
      r = (if checkPrfPure c.mv c.nc poolRem table prfBytes then 1 else 0) →
      (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m' →
      Q [r] m'

/-- Exact contract for `lrat_check_bytes`. -/
def lratCheckBytesExactSpec : Spec := fun args m Q _ =>
  ∃ (cnf_ptr prf_ptr work_ptr : Val) (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (R_mem : Mem 64 → Prop),
    args = [cnf_ptr, BitVec.ofNat 64 cnfBytes.length,
            prf_ptr, BitVec.ofNat 64 prfBytes.length,
            work_ptr, BitVec.ofNat 64 work_len] ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    prf_ptr.toNat + prfBytes.length < 2 ^ 64 ∧
    work_ptr.toNat + work_len < 2 ^ 64 ∧
    ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆ R_mem) m ∧
    ∀ (r : Val) (m' : Mem 64),
      r = (if runLratCheckBytes cnfBytes prfBytes work_len then 1 else 0) →
      ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆ R_mem) m' →
      Q [r] m'

end LeanQbe.LratBytes
