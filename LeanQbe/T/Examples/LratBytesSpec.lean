module

public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Logic.ZeroTerm
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.FlatLemmas
public import Kraken.Bedrock2.Test.LratTrimCheckProof
import Kraken.Mem
import Kraken.Separation

/-!
# Shared specifications and pure executable mirror for `LeanQbe.T.Examples.LratBytes`

Defines:
1. `lratBytesFns_wf`: well-formedness (`Func.Wf`) of all 6 functions in `lratBytesFns`
   via `t_wf_reify`.
2. Bounds of the DIMACS number parser (`parseNat_lt_bound`) and validity of literals
   (`isValidLit_ofNat`).
3. The 100% structurally recursive pure mirror `runLratCheckBytes` (`parseBodyPure`,
   `readLeb128Pure`, `readAddLitsPure`, `rupCheckPure`, `checkPrfPure`) and `readLeb128_spec`.
4. `WorkCfg`, `WorkState`, and the exact typed contracts for all 5 internal callees plus
   `lratCheckBytesExactSpec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.LratBytes

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT.Internal
open Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.ProofUtil

/-! ## 1. Well-formedness and module structure of `lratBytesModule` -/

theorem lbParseDimacsHeader_wf : Func.Wf lbParseDimacsHeader := by t_wf_reify
theorem lbParseDimacsBody_wf : Func.Wf lbParseDimacsBody := by t_wf_reify
theorem lbReadAddLits_wf : Func.Wf lbReadAddLits := by t_wf_reify
theorem lbRupCheck_wf : Func.Wf lbRupCheck := by t_wf_reify
theorem lbCheckPrf_wf : Func.Wf lbCheckPrf := by t_wf_reify
theorem lratCheckBytes_wf : Func.Wf lratCheckBytes := by t_wf_reify

theorem lratBytesFns_wf : ∀ f ∈ lratBytesFns, Fn.Wf f := by
  intro f hf
  simp only [lratBytesFns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lbParseDimacsHeader_wf
  · exact lbParseDimacsBody_wf
  · exact lbReadAddLits_wf
  · exact lbRupCheck_wf
  · exact lbCheckPrf_wf
  · exact lratCheckBytes_wf

theorem lratBytesModule_namesNodup : lratBytesModule.namesNodup := by
  simp only [Module.namesNodup, Module.names, lratBytesModule, lratBytesFns]
  decide

/-! ## 2. Bounds of the DIMACS number parser and literal validity -/

theorem parseDigitsAux_lt_bound {acc : Nat} {bs : List UInt8} {v : Nat} {rest : List UInt8}
    (hacc : acc < dimacsBound) (h : parseDigitsAux acc bs = some (v, rest)) :
    v < dimacsBound := by
  induction bs generalizing acc with
  | nil => simp [parseDigitsAux] at h; obtain ⟨rfl, _⟩ := h; exact hacc
  | cons b bs ih =>
    simp only [parseDigitsAux] at h
    grind

theorem parseNat_lt_bound {bs : List UInt8} {v : Nat} {rest : List UInt8}
    (h : parseNat bs = some (v, rest)) : v < dimacsBound := by
  cases bs with
  | nil => nomatch h
  | cons b bs =>
    simp only [parseNat] at h
    split at h
    · rename_i hd
      unfold isDimacsDigit at hd
      have := b.toNat_lt
      exact parseDigitsAux_lt_bound (by unfold dimacsBound; omega) h
    · nomatch h

private theorem bv64_ofNat_slt_zero {v : Nat} (hv : v < 2 ^ 28) :
    (BitVec.ofNat 64 v).slt 0#64 = false := by
  unfold BitVec.slt BitVec.toInt
  grind

theorem isValidLit_ofNat {mv v : Nat} (hv1 : 1 ≤ v) (hvm : v ≤ mv) (hmv : mv < dimacsBound) :
    IsValidLit mv (BitVec.ofNat 64 v) := by
  unfold dimacsBound at hmv
  have hslt := bv64_ofNat_slt_zero (v := v) (by omega)
  refine ⟨by unfold IsInt32; grind, ?_, ?_, by omega⟩
  · grind
  · unfold bvAbs
    grind

/-! ## 4. Pure executable mirror (`runLratCheckBytes`) -/

/-- Structural mirror of `@lit_loop` in `lbParseDimacsBody`. -/
def parseClausePure : Nat → Nat → Nat → List (BitVec 64) → List UInt8 →
    Option (List (BitVec 64) × Nat × List UInt8)
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
def parseBodyPure (mv : Nat) : Nat → Nat → List (List (BitVec 64)) → List UInt8 →
    Option (List (List (BitVec 64)) × Nat)
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
def decodeZigZag (u : Nat) : BitVec 64 :=
  let v : BitVec 64 := BitVec.ofNat 64 (u / 2)
  if u % 2 == 1 then -v else v

theorem isValidLit_decodeZigZag {mv u : Nat} (_hu : u < 2 ^ 28)
    (hv1 : 1 ≤ u / 2) (hvm : u / 2 ≤ mv) (hmv : mv < dimacsBound) :
    IsValidLit mv (decodeZigZag u) := by
  unfold decodeZigZag
  have hv := isValidLit_ofNat hv1 hvm hmv
  split
  · exact isValidLit_neg hv
  · exact hv

private theorem lo7_shift_lt {x sh : Nat} (hsh : sh ≤ 21) :
    (x &&& 127) <<< sh < 2 ^ 28 := by
  rw [Nat.shiftLeft_eq]
  have h1 : x &&& 127 < 2 ^ 7 := Nat.and_lt_two_pow x (n := 7) (by decide)
  have h2 : 2 ^ sh ≤ 2 ^ 21 := Nat.pow_le_pow_right (by omega) hsh
  have h3 : (x &&& 127) * 2 ^ sh < 2 ^ 7 * 2 ^ 21 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ h2)
      (Nat.mul_lt_mul_of_pos_right h1 (by decide))
  omega

theorem readLeb128Aux_some {fuel acc sh : Nat} {bs bs' : List UInt8} {u : Nat}
    (hacc : acc < 2 ^ 28) (hsh : sh + 7 * fuel ≤ 28)
    (h : readLeb128Aux fuel acc sh bs = some (u, bs')) :
    u < 2 ^ 28 ∧ ∃ k, 0 < k ∧ k ≤ bs.length ∧ bs' = bs.drop k := by
  induction fuel generalizing acc sh bs with
  | zero => simp [readLeb128Aux] at h
  | succ fuel ih =>
    cases bs with
    | nil => simp [readLeb128Aux] at h
    | cons b rest =>
      have hacc2 : (acc ||| ((b.toNat &&& 127) <<< sh)) < 2 ^ 28 :=
        Nat.or_lt_two_pow hacc (lo7_shift_lt (by omega))
      simp only [readLeb128Aux] at h
      split at h
      · split at h
        · obtain ⟨hu, k, hk0, hkle, rfl⟩ := ih hacc2 (by omega) h
          exact ⟨hu, k + 1, by omega, by simp; omega, by simp⟩
        · simp at h
      · injection h with hp
        injection hp with hu_eq hbs_eq
        subst hu_eq hbs_eq
        exact ⟨hacc2, 1, by omega, by simp, by simp⟩

theorem readLeb128Pure_some {bs bs' : List UInt8} {u : Nat}
    (h : readLeb128Pure bs = some (u, bs')) :
    u < 2 ^ 28 ∧ bs'.length < bs.length ∧
    ∃ k, 0 < k ∧ k ≤ bs.length ∧ bs' = bs.drop k := by
  obtain ⟨hu, k, hk0, hkle, rfl⟩ := readLeb128Aux_some (by decide) (by decide) h
  exact ⟨hu, by simp; omega, k, hk0, hkle, rfl⟩

theorem readLeb128Pure_drop {prfBytes : List UInt8} {idx u : Nat} {bs' : List UInt8}
    (hidx : idx ≤ prfBytes.length)
    (h : readLeb128Pure (prfBytes.drop idx) = some (u, bs')) :
    u < 2 ^ 28 ∧
    bs'.length < (prfBytes.drop idx).length ∧
    prfBytes.length - bs'.length ≤ prfBytes.length ∧
    idx < prfBytes.length - bs'.length ∧
    bs' = prfBytes.drop (prfBytes.length - bs'.length) := by
  obtain ⟨hu, hlt, k, hk0, hkle, hdrop⟩ := readLeb128Pure_some h
  rw [List.length_drop] at hkle hlt
  rw [List.drop_drop] at hdrop
  grind

theorem readLeb128_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {fail : Cont []}
    {cur pend prf_ptr : BitVec 64} {prfBytes : List UInt8} {idx : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {done : BitVec 64 → BitVec 64 → Expr Val Cont rs}
    (hfit : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hidx : idx ≤ prfBytes.length)
    (hcur : cur = prf_ptr + BitVec.ofNat 64 idx)
    (hpend : pend = prf_ptr + BitVec.ofNat 64 prfBytes.length)
    (hm : (Eq (prfBytes.At prf_ptr) ⋆ R) m)
    (hfail : readLeb128Pure (prfBytes.drop idx) = none → fail () m)
    (hdone : ∀ u bs',
      readLeb128Pure (prfBytes.drop idx) = some (u, bs') →
      u < 2 ^ 28 →
      bs'.length < (prfBytes.drop idx).length →
      bs' = prfBytes.drop (prfBytes.length - bs'.length) →
      idx < prfBytes.length - bs'.length →
      wp Γ Q X (done (BitVec.ofNat 64 u)
        (prf_ptr + BitVec.ofNat 64 (prfBytes.length - bs'.length))) m) :
    wp Γ Q X (readLeb128 fail cur pend done) m := by
  subst hcur hpend
  unfold readLeb128
  refine wp_join_group (fun (u_v, cur_v, ()) m' => ∃ u idx',
    u_v = BitVec.ofNat 64 u ∧ cur_v = prf_ptr + BitVec.ofNat 64 idx' ∧
    m' = m ∧ idx' ≤ prfBytes.length ∧
    readLeb128Pure (prfBytes.drop idx) = some (u, prfBytes.drop idx')) ?_ ?_
  · rintro _ ⟨u_v, cur_v, ⟨⟩⟩ _ ⟨u, idx', rfl, rfl, rfl, hidx', hres⟩
    dsimp only [Blocks.get_here]
    obtain ⟨hu, hlt, _, hgt, hdrop⟩ := readLeb128Pure_drop hidx hres
    grind
  · intro Jdone hJdone
    refine wp_loop_group (fun fuel (p_v, acc_v, sh_v, ()) m' => ∃ i acc sh,
      1 ≤ fuel ∧ sh + 7 * fuel = 28 ∧ acc < 2 ^ 28 ∧
      i ≤ prfBytes.length ∧ m' = m ∧
      p_v = prf_ptr + BitVec.ofNat 64 i ∧ acc_v = BitVec.ofNat 64 acc ∧ sh_v = BitVec.ofNat 64 sh ∧
      readLeb128Pure (prfBytes.drop idx) = readLeb128Aux fuel acc sh (prfBytes.drop i)) ?_ ?_
    · rintro Jleb fuel ⟨p_v, acc_v, sh_v, ⟨⟩⟩ _ ih
        ⟨i, acc, sh, hfuel1, hsh_eq, hacc, hi, rfl, rfl, rfl, rfl, hpure⟩
      obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
      dsimp only [Blocks.get_here]
      wp_unfold
      refine cursor_loadu8_branch hfit hi hm
        (fun _ hnil => hfail (by simpa [hnil, readLeb128Aux] using hpure))
        (fun hilt hdrop => ?_)
      rw [setWidth64_ofNat8]
      rw [hdrop] at hpure
      have hlo_lt : prfBytes[i].toNat &&& 127 < 128 :=
        Nat.and_lt_two_pow prfBytes[i].toNat (n := 7) (by decide)
      have hacc2_lt : (acc ||| ((prfBytes[i].toNat &&& 127) <<< sh)) < 2 ^ 28 :=
        Nat.or_lt_two_pow hacc (lo7_shift_lt (by omega))
      have hhi_lt : prfBytes[i].toNat &&& 128 < 256 :=
        Nat.and_lt_two_pow prfBytes[i].toNat (n := 8) (by decide)
      have hlo_bv : BitVec.ofNat 64 prfBytes[i].toNat &&& (127 : BitVec 64) =
          BitVec.ofNat 64 (prfBytes[i].toNat &&& 127) := BitVec.eq_of_toNat_eq (by simp)
      have hhi_bv : BitVec.ofNat 64 prfBytes[i].toNat &&& (128 : BitVec 64) =
          BitVec.ofNat 64 (prfBytes[i].toNat &&& 128) := BitVec.eq_of_toNat_eq (by simp)
      have hsh_mod : (BitVec.ofNat 64 sh).toNat % 64 = sh := by
        simp [Nat.mod_eq_of_lt (by omega : sh < 2 ^ 64), Nat.mod_eq_of_lt (by omega : sh < 64)]
      have hacc2_bv : BitVec.ofNat 64 acc ||| BitVec.ofNat 64 ((prfBytes[i].toNat &&& 127) <<< sh) =
          BitVec.ofNat 64 (acc ||| ((prfBytes[i].toNat &&& 127) <<< sh)) :=
        BitVec.eq_of_toNat_eq (by simp)
      rw [hlo_bv, hsh_mod, bv_shl_ofNat (by omega) (by omega), hacc2_bv, hhi_bv, ptr_step_1]
      have ⟨hmore_b, hnmore_b⟩ := bv_eq_zero_branch (by omega : prfBytes[i].toNat &&& 128 < 2 ^ 64)
        (fun h0 => by
          simp [h0] : prfBytes[i].toNat &&& 128 = 0 → ((prfBytes[i].toNat &&& 128) != 0) = false)
        (fun hnz => by
          simp [hnz] : prfBytes[i].toNat &&& 128 ≠ 0 → ((prfBytes[i].toNat &&& 128) != 0) = true)
      refine ⟨fun hmore => ?_, fun hnmore => ?_⟩
      · simp only [readLeb128Aux, hnmore_b hmore, ↓reduceIte] at hpure
        rw [show (7 : BitVec 64) = BitVec.ofNat 64 7 from rfl,
            show (28 : BitVec 64) = BitVec.ofNat 64 28 from rfl, bv_add_ofNat sh 7]
        refine ult_branch (a := sh + 7) (b := 28) (by omega) (by decide)
          (fun hlt28 => ?_) (fun _ => by grind)
        simp only [hlt28, ↓reduceIte] at hpure
        exact ih fuel' _ _ (by omega)
          ⟨i + 1, _, sh + 7, by omega, by omega, hacc2_lt, hilt, rfl, rfl, rfl, rfl, hpure⟩
      · simp only [readLeb128Aux, hmore_b hnmore, Bool.false_eq_true, ↓reduceIte] at hpure
        exact hJdone _ _ ⟨_, i + 1, rfl, rfl, rfl, hilt, hpure⟩
    · intro Jleb hJleb; wp_unfold
      exact hJleb 4 _ _ ⟨idx, 0, 0, by decide, by decide, by decide, hidx, rfl, rfl, rfl, rfl, rfl⟩

/-- Structural mirror of `lbReadAddLits`. -/
def readAddLitsAux : Nat → Nat → Nat → List (BitVec 64) → List UInt8 →
    Option (List (BitVec 64) × Nat × List UInt8)
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
    Option (List (BitVec 64) × Nat × List UInt8) :=
  readAddLitsAux (bs.length + 1) mv poolRem [] bs

/-- Outcome of `rupPhase1`. -/
inductive Phase1Res
  | fail
  | taut
  | ok (vals : List (BitVec 64)) (trailLen : Nat)

/-- Structural mirror of `rupPhase1` over `vals : List (BitVec 64)` (`length = mv + 1`). -/
def rupPhase1Pure (mv : Nat) : List (BitVec 64) → List (BitVec 64) → Nat → Phase1Res
  | [], vals, trailLen => .ok vals trailLen
  | lit :: lits, vals, trailLen =>
    let idx := (bvAbs lit).toNat
    let val := evalAssignedLit (vals.getD idx 0) lit
    if val.slt 0 then
      rupPhase1Pure mv lits vals trailLen
    else if (0 : BitVec 64).slt val then
      .taut
    else if trailLen == mv + 1 then
      .fail
    else
      let nlit := -lit
      let vals' := vals.set idx (bvSignByte nlit)
      rupPhase1Pure mv lits vals' (trailLen + 1)

/-- Structural mirror of `rupInner` over `vals : List (BitVec 64)`. -/
def rupInnerPure (mv : Nat) : List (BitVec 64) → BitVec 64 → List (BitVec 64) → Nat →
    Option (BitVec 64 × List (BitVec 64) × Nat)
  | [], unit, vals, trailLen => some (unit, vals, trailLen)
  | lit :: lits, unit, vals, trailLen =>
    let idx := (bvAbs lit).toNat
    let val := evalAssignedLit (vals.getD idx 0) lit
    if val.slt 0 then
      if unit == -lit then none
      else rupInnerPure mv lits unit vals trailLen
    else
      let stepUnit : Option (BitVec 64 × List (BitVec 64) × Nat) :=
        if val == 0 then
          if trailLen == mv + 1 then none
          else
            let vals' := vals.set idx (bvSignByte lit)
            rupInnerPure mv lits lit vals' (trailLen + 1)
        else
          rupInnerPure mv lits lit vals trailLen
      if unit != 0 then
        if unit == lit then stepUnit else none
      else
        stepUnit

/-- Structural mirror of `@consume` in `lbRupCheck`. -/
def consumeHintsAux : Nat → Nat → List (Option (List (BitVec 64))) → List UInt8 →
    Option (List UInt8)
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

def consumeHintsPure (id : Nat) (table : List (Option (List (BitVec 64)))) (bs : List UInt8) :
    Option (List UInt8) :=
  consumeHintsAux (bs.length + 1) id table bs

/-- Structural mirror of `@ph2` in `lbRupCheck`. -/
def rupPhase2Aux : Nat → Nat → Nat → List (Option (List (BitVec 64))) → List (BitVec 64) → Nat →
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
              if unit != 0 then
                rupPhase2Aux fuel mv id table vals' trailLen' bs'
              else
                consumeHintsPure id table bs'
          | _ => none
        else none

/-- Structural mirror of `lbRupCheck`. -/
def rupCheckPure (mv id : Nat) (clits : List (BitVec 64))
    (table : List (Option (List (BitVec 64)))) (bs : List UInt8) : Option (List UInt8) :=
  match rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 with
  | .fail => none
  | .taut => consumeHintsPure id table bs
  | .ok vals trailLen => rupPhase2Aux (bs.length + 1) mv id table vals trailLen bs

/-- Structural mirror of `@del_loop` in `lbCheckPrf`. -/
def delLoopAux : Nat → Nat → List (Option (List (BitVec 64))) → List UInt8 →
    Option (List (Option (List (BitVec 64))) × List UInt8)
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
def checkPrfAux : Nat → Nat → Nat → Nat → List (Option (List (BitVec 64))) → List UInt8 → Bool
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

def checkPrfPure (mv nc poolRem : Nat) (table : List (Option (List (BitVec 64))))
    (bs : List UInt8) : Bool :=
  checkPrfAux (bs.length + 1) mv nc poolRem table bs

/-- Initial `List (Option (List (BitVec 64)))` table of length `cap` (`none` at `0`, `some cl` at
`1..nc`, `none` at `nc + 1 .. cap - 1`). -/
def initClauseTable (cap : Nat) (clauses : List (List (BitVec 64))) :
    List (Option (List (BitVec 64))) :=
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

/-! ## 5. Workspace layout invariant (`WorkCfg`, `WorkState`) and exact contracts -/

/-- Static workspace geometry computed by `lrat_check_bytes` after `lb_parse_dimacs_header`. -/
structure WorkCfg where
  hdr : BitVec 64
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

def vb (c : WorkCfg) : BitVec 64 := c.hdr + 80
def tb (c : WorkCfg) : BitVec 64 := c.vb + BitVec.ofNat 64 c.vBytes
def tlim (c : WorkCfg) : BitVec 64 := c.tb + BitVec.ofNat 64 c.tRaw
def cb (c : WorkCfg) : BitVec 64 := c.tb + BitVec.ofNat 64 c.tBytes
def pbase (c : WorkCfg) : BitVec 64 := c.cb + BitVec.ofNat 64 (8 * c.cap)
def plim (c : WorkCfg) : BitVec 64 := c.pbase + BitVec.ofNat 64 (4 * c.poolInts)

def hdrWords (c : WorkCfg) (pcur cur : BitVec 64) : List (BitVec 64) :=
  [BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, BitVec.ofNat 64 c.cap,
   c.vb, c.tb, c.tlim, c.cb, c.plim, pcur, cur]

theorem fit_active (c : WorkCfg) : c.hdr.toNat + c.activeBytes < 2 ^ 64 := by
  have := c.hfit; unfold activeBytes vBytes tBytes tRaw; omega

theorem toNat_vb (c : WorkCfg) : c.vb.toNat = c.hdr.toNat + 80 := by
  have := c.fit_active; unfold activeBytes at this
  exact bv_add_ofNat_toNat (n := 80) (by omega)

theorem toNat_tb (c : WorkCfg) : c.tb.toNat = c.vb.toNat + c.vBytes := by
  have := c.fit_active; have := c.toNat_vb; unfold activeBytes at *
  exact bv_add_ofNat_toNat (n := c.vBytes) (by omega)

theorem toNat_tlim (c : WorkCfg) : c.tlim.toNat = c.tb.toNat + c.tRaw := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
  have htb : c.tRaw ≤ c.tBytes := by unfold tBytes; omega
  unfold activeBytes at *; exact bv_add_ofNat_toNat (n := c.tRaw) (by omega)

theorem toNat_cb (c : WorkCfg) : c.cb.toNat = c.tb.toNat + c.tBytes := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
  unfold activeBytes at *; exact bv_add_ofNat_toNat (n := c.tBytes) (by omega)

theorem toNat_pbase (c : WorkCfg) : c.pbase.toNat = c.cb.toNat + 8 * c.cap := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb; have := c.toNat_cb
  unfold activeBytes at *; exact bv_add_ofNat_toNat (n := 8 * c.cap) (by omega)

theorem toNat_plim (c : WorkCfg) : c.plim.toNat = c.pbase.toNat + 4 * c.poolInts := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
  have := c.toNat_cb; have := c.toNat_pbase
  unfold activeBytes at *; exact bv_add_ofNat_toNat (n := 4 * c.poolInts) (by omega)

theorem pcur_ne_zero (c : WorkCfg) {off : Nat} (hoff : off ≤ 4 * c.poolInts) :
    c.pbase + BitVec.ofNat 64 off ≠ 0 := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
  have := c.toNat_cb; have := c.toNat_pbase; unfold activeBytes at *
  grind

theorem pcur_eq_plim_iff (c : WorkCfg) {rem : Nat} (hrem : rem ≤ c.poolInts) :
    c.pbase + BitVec.ofNat 64 (4 * (c.poolInts - rem)) = c.plim ↔ rem = 0 := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
  have := c.toNat_cb; have := c.toNat_pbase; unfold activeBytes at *; unfold plim
  grind

end WorkCfg

/-- Agreement between physical `ptrs : List (BitVec 64)`, logical `table`, and `PoolUsed`. -/
def TableRel (mv cap : Nat) (ptrs : List (BitVec 64)) (table : List (Option (List (BitVec 64))))
    (PoolUsed : Mem 64 → Prop) : Prop :=
  ∃ (hplen : ptrs.length = cap) (htlen : table.length = cap),
    ∀ i (hi : i < cap),
      match table[i]'(htlen ▸ hi) with
      | none => ptrs[i]'(hplen ▸ hi) = 0
      | some lits =>
        ptrs[i]'(hplen ▸ hi) ≠ 0 ∧
        (∀ x ∈ lits, IsValidLit mv x) ∧
        (∃ R, PoolUsed = (ZeroTermInts (ptrs[i]'(hplen ▸ hi)) lits ⋆ R))

theorem TableRel.frame_right {mv cap : Nat} {ptrs : List (BitVec 64)}
    {table : List (Option (List (BitVec 64)))} {PoolUsed : Mem 64 → Prop} (P : Mem 64 → Prop)
    (h : TableRel mv cap ptrs table PoolUsed) :
    TableRel mv cap ptrs table (PoolUsed ⋆ P) := by
  obtain ⟨hplen, htlen, hrel⟩ := h
  refine ⟨hplen, htlen, fun i hi => ?_⟩
  have hi_spec := hrel i hi
  cases hti : table[i]'(htlen ▸ hi) with
  | none => rw [hti] at hi_spec; exact hi_spec
  | some lits =>
    rw [hti] at hi_spec
    obtain ⟨hne, hv, R_i, hpu⟩ := hi_spec
    exact ⟨hne, hv, R_i ⋆ P, by rw [hpu, sep_assoc]⟩

/-- Full workspace memory state over `[c.hdr, c.hdr + c.activeBytes)`. -/
def WorkState (c : WorkCfg) (poolUsedInts poolRemInts : Nat) (cur : BitVec 64)
    (ptrs : List (BitVec 64)) (table : List (Option (List (BitVec 64))))
    (PoolUsed : Mem 64 → Prop) : Mem 64 → Prop := fun m =>
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

theorem workState_sep {c : WorkCfg} {poolUsedInts poolRemInts : Nat} {cur : BitVec 64}
    {ptrs : List (BitVec 64)} {table : List (Option (List (BitVec 64)))}
    {PoolUsed F : Mem 64 → Prop} {m : Mem 64} :
    (WorkState c poolUsedInts poolRemInts cur ptrs table PoolUsed ⋆ F) m ↔
      poolUsedInts + poolRemInts = c.poolInts ∧
      TableRel c.mv c.cap ptrs table PoolUsed ∧
      (∀ f, PoolUsed f → region c.pbase (4 * poolUsedInts) f) ∧
      ((word8Array c.hdr (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsedInts)) cur) ⋆
        byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
        region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
        region c.tb c.tRaw ⋆
        region c.tlim (c.tBytes - c.tRaw) ⋆
        word8Array c.cb ptrs ⋆
        PoolUsed ⋆
        region (c.pbase + BitVec.ofNat 64 (4 * poolUsedInts)) (4 * poolRemInts)) ⋆ F) m := by
  unfold WorkState; simp only [sep_pure_l]

theorem loadl_hdr {c : WorkCfg} {pcur cur : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (i : Nat) (hi : i < 10)
    (h : (word8Array c.hdr (c.hdrWords pcur cur) ⋆ R) m)
    {a : BitVec 64} (ha : a = c.hdr + BitVec.ofNat 64 (8 * i)) :
    loadVal m i64 a =
      some ((c.hdrWords pcur cur)[i]'(by simpa [WorkCfg.hdrWords] using hi)) := by
  subst ha; exact load_word8Array _ h

/-- Collapse the 8 partitioned workspace regions back into `region c.hdr c.activeBytes`. -/
theorem workCfg_regions_to_activeBytes (c : WorkCfg) {poolUsedInts poolRemInts : Nat}
    (hsum : poolUsedInts + poolRemInts = c.poolInts) {m : Mem 64}
    (hm : (region c.hdr 80 ⋆
      region c.vb (c.mv + 1) ⋆
      region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
      region c.tb c.tRaw ⋆
      region c.tlim (c.tBytes - c.tRaw) ⋆
      region c.cb (8 * c.cap) ⋆
      region c.pbase (4 * poolUsedInts) ⋆
      region (c.pbase + BitVec.ofNat 64 (4 * poolUsedInts)) (4 * poolRemInts)) m) :
    region c.hdr c.activeBytes m := by
  have hfit : c.activeBytes ≤ 2 ^ 64 := by have := c.fit_active; omega
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hvb : c.mv + 1 ≤ c.vBytes := by unfold WorkCfg.vBytes; omega
  have htb : c.tRaw ≤ c.tBytes := by unfold WorkCfg.tBytes WorkCfg.tRaw; omega
  unfold WorkCfg.activeBytes at hfit ⊢
  have hm2 : (region c.hdr 80 ⋆
      ((region c.vb (c.mv + 1) ⋆
          region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1))) ⋆
        ((region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw)) ⋆
          (region c.cb (8 * c.cap) ⋆
            (region c.pbase (4 * poolUsedInts) ⋆
              region (c.pbase + BitVec.ofNat 64 (4 * poolUsedInts)) (4 * poolRemInts)))))) m :=
    sep_ac hm
  rw [
    region_merge_eq (a := c.vb) (n1 := c.mv + 1) (n2 := c.vBytes - (c.mv + 1)) (n := c.vBytes)
      (by omega) (by omega),
    show c.tlim = c.tb + BitVec.ofNat 64 c.tRaw from rfl,
    region_merge_eq (a := c.tb) (n1 := c.tRaw) (n2 := c.tBytes - c.tRaw) (n := c.tBytes)
      (by omega) (by omega),
    region_merge_eq (a := c.pbase) (n1 := 4 * poolUsedInts) (n2 := 4 * poolRemInts)
      (n := 4 * c.poolInts) (by omega) (by omega),
    show c.pbase = c.cb + BitVec.ofNat 64 (8 * c.cap) from rfl,
    region_merge_eq (a := c.cb) (n1 := 8 * c.cap) (n2 := 4 * c.poolInts)
      (n := 8 * c.cap + 4 * c.poolInts) rfl (by omega),
    show c.cb = c.tb + BitVec.ofNat 64 c.tBytes from rfl,
    region_merge_eq (a := c.tb) (n1 := c.tBytes) (n2 := 8 * c.cap + 4 * c.poolInts)
      (n := c.tBytes + (8 * c.cap + 4 * c.poolInts)) rfl (by omega),
    show c.tb = c.vb + BitVec.ofNat 64 c.vBytes from rfl,
    region_merge_eq (a := c.vb) (n1 := c.vBytes) (n2 := c.tBytes + (8 * c.cap + 4 * c.poolInts))
      (n := c.vBytes + (c.tBytes + (8 * c.cap + 4 * c.poolInts))) rfl (by omega),
    show c.vb = c.hdr + BitVec.ofNat 64 80 from rfl,
    region_merge_eq (a := c.hdr) (n1 := 80)
      (n2 := c.vBytes + (c.tBytes + (8 * c.cap + 4 * c.poolInts))) (n := c.activeBytes)
      (by unfold WorkCfg.activeBytes; omega) hfit] at hm2
  exact hm2

def wsFixed (c : WorkCfg) (ptrs : List (BitVec 64)) (PoolUsed : Mem 64 → Prop) : Mem 64 → Prop :=
  byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
  region c.tb c.tRaw ⋆
  region c.tlim (c.tBytes - c.tRaw) ⋆
  word8Array c.cb ptrs ⋆
  PoolUsed

theorem wsFixed_to_region (c : WorkCfg) {pcur0 cur0 : BitVec 64}
    {poolUsed accLen rem : Nat} {ptrs lits : List (BitVec 64)} {PoolUsed : Mem 64 → Prop}
    {m : Mem 64}
    (hplen : ptrs.length = c.cap) (hll : lits.length = accLen)
    (hsum : poolUsed + accLen + rem = c.poolInts)
    (hpu : ∀ f, PoolUsed f → region c.pbase (4 * poolUsed) f)
    (hm : (word8Array c.hdr (c.hdrWords pcur0 cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
      int4Array (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) lits ⋆
      region (c.pbase + BitVec.ofNat 64 (4 * poolUsed) + BitVec.ofNat 64 (4 * accLen))
        (4 * rem)) m) :
    region c.hdr c.activeBytes m := by
  have := c.fit_active; have hmv := c.hmv; unfold dimacsBound at hmv
  unfold WorkCfg.activeBytes WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *
  let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
  have h4 : ∀ f, (int4Array pcur lits ⋆ region (pcur + BitVec.ofNat 64 (4 * accLen)) (4 * rem)) f →
      region pcur (4 * (accLen + rem)) f := fun _ hf => by
    rw [← region_merge_eq (a := pcur) (n1 := 4 * accLen) (n2 := 4 * rem) (by omega) (by omega)]
    exact sep_mono (fun _ g => by simpa [hll] using int4Array_to_region (by rw [hll]; omega) g) hf
  unfold wsFixed at hm
  have hm0 : (word8Array c.hdr (c.hdrWords pcur0 cur0) ⋆
      byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
      region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
      region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw) ⋆
      word8Array c.cb ptrs ⋆ PoolUsed ⋆
      (int4Array pcur lits ⋆ region (pcur + BitVec.ofNat 64 (4 * accLen)) (4 * rem))) m :=
    sep_cast hm (by dsimp only [pcur]; ac_rfl)
  refine workCfg_regions_to_activeBytes c (poolUsedInts := poolUsed) (poolRemInts := accLen + rem)
    (by omega) ?_
  refine sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
    (fun _ hf => by
      simpa [WorkCfg.hdrWords] using word8Array_to_region (by simp [WorkCfg.hdrWords]) hf)
    (fun _ hf => by simpa using byte1Array_to_region (by simp; omega) hf))
    (fun _ h => h)) (fun _ h => h)) (fun _ h => h))
    (fun _ hf => by simpa [hplen] using word8Array_to_region (by rw [hplen]; omega) hf))
    hpu) h4 m hm0

/-- Any `WorkState` collapses back into `region c.hdr c.activeBytes`. -/
theorem WorkState.to_region {c : WorkCfg} {poolUsedInts poolRemInts : Nat} {cur : BitVec 64}
    {ptrs : List (BitVec 64)} {table : List (Option (List (BitVec 64)))}
    {PoolUsed : Mem 64 → Prop} {m : Mem 64}
    (h : WorkState c poolUsedInts poolRemInts cur ptrs table PoolUsed m) :
    region c.hdr c.activeBytes m := by
  obtain ⟨hsum, ⟨hplen, _, _⟩, hpu, hm⟩ := h
  dsimp only at hm
  refine wsFixed_to_region c (pcur0 := c.pbase + BitVec.ofNat 64 (4 * poolUsedInts)) (cur0 := cur)
    (accLen := 0) (lits := []) hplen rfl (by omega) hpu ?_
  simp only [int4Array_nil, Nat.mul_zero, BitVec.add_zero]
  have hemp : (word8Array c.hdr (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsedInts)) cur) ⋆
      wsFixed c ptrs PoolUsed ⋆ emp) =
      (word8Array c.hdr (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsedInts)) cur) ⋆
      wsFixed c ptrs PoolUsed) := by simp [sep_emp]
  rw [hemp]; unfold wsFixed
  exact sep_ac hm

theorem wsFixed_fail_collapse (c : WorkCfg) {base pcur0 cur0 : BitVec 64} {bs : List UInt8}
    {poolUsed rem : Nat} {ptrs acc : List (BitVec 64)} {PoolUsed R : Mem 64 → Prop} {m : Mem 64}
    (hplen : ptrs.length = c.cap)
    (hsum : poolUsed + acc.length + rem = c.poolInts)
    (hpu : ∀ f, PoolUsed f → region c.pbase (4 * poolUsed) f)
    (hm : (Eq (bs.At base) ⋆
      (word8Array c.hdr (c.hdrWords pcur0 cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
        int4Array (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) acc.reverse ⋆
        region (c.pbase + BitVec.ofNat 64 (4 * poolUsed) + BitVec.ofNat 64 (4 * acc.length))
          (4 * rem)) ⋆ R) m) :
    (Eq (bs.At base) ⋆ region c.hdr c.activeBytes ⋆ R) m :=
  sep_mono_mid (B' := region c.hdr c.activeBytes)
    (fun _ hws => wsFixed_to_region c hplen (by simp) hsum hpu hws) hm

theorem wsFixed_push_lit {c : WorkCfg} {base pcur0 cur0 : BitVec 64} {bs : List UInt8}
    {poolUsed rem : Nat} {ptrs acc : List (BitVec 64)} {PoolUsed R : Mem 64 → Prop} {m : Mem 64}
    (lit : BitVec 64) (hrem : 0 < rem) (hfit : 4 * rem ≤ 2 ^ 64)
    (hm : (Eq (bs.At base) ⋆
      (word8Array c.hdr (c.hdrWords pcur0 cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
        int4Array (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) acc.reverse ⋆
        region (c.pbase + BitVec.ofNat 64 (4 * poolUsed) + BitVec.ofNat 64 (4 * acc.length))
          (4 * rem)) ⋆ R) m) :
    let wcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed) + BitVec.ofNat 64 (4 * acc.length)
    storeOk m i32 wcur ∧
    (Eq (bs.At base) ⋆
      (word8Array c.hdr (c.hdrWords pcur0 cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
        int4Array (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) (lit :: acc).reverse ⋆
        region (c.pbase + BitVec.ofNat 64 (4 * poolUsed) +
          BitVec.ofNat 64 (4 * (lit :: acc).length)) (4 * (rem - 1))) ⋆ R)
      (storeMem m i32 wcur (lit.setWidth 32)) := by
  intro wcur
  let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
  obtain ⟨ok_sw, hm1⟩ := region_pop_store_int4_64 lit hrem hfit
    (sep_cast hm (by dsimp only [wcur, pcur]; ac_rfl) : (region wcur (4 * rem) ⋆
      (Eq (bs.At base) ⋆ word8Array c.hdr (c.hdrWords pcur0 cur0) ⋆
        wsFixed c ptrs PoolUsed ⋆ int4Array pcur acc.reverse ⋆ R)) m)
  have harr : int4Array pcur (lit :: acc).reverse =
      (int4Array pcur acc.reverse ⋆ int4 wcur lit) := by
    rw [List.reverse_cons, int4Array_append, List.length_reverse]
    simp [wcur, pcur, sep_emp]
  have hwcur2 : wcur + 4 = pcur + BitVec.ofNat 64 (4 * (lit :: acc).length) := by
    simp only [wcur, pcur, List.length_cons, ptr4]
  rw [hwcur2] at hm1
  refine ⟨ok_sw, ?_⟩
  rw [harr]
  exact sep_cast hm1 (by dsimp only [wcur, pcur]; ac_rfl)

theorem wsFixed_finish_clause {c : WorkCfg} {base pcur0 cur0 : BitVec 64} {bs : List UInt8}
    {poolUsed rem : Nat} {ptrs acc : List (BitVec 64)} {PoolUsed R : Mem 64 → Prop} {m : Mem 64}
    (hrem : 0 < rem) (hsum : poolUsed + (acc.length + 1) + (rem - 1) = c.poolInts)
    (hpu : ∀ f, PoolUsed f → region c.pbase (4 * poolUsed) f)
    (hm : (Eq (bs.At base) ⋆
      (word8Array c.hdr (c.hdrWords pcur0 cur0) ⋆ wsFixed c ptrs PoolUsed ⋆
        int4Array (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) acc.reverse ⋆
        region (c.pbase + BitVec.ofNat 64 (4 * poolUsed) + BitVec.ofNat 64 (4 * acc.length))
          (4 * rem)) ⋆ R) m) :
    let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
    let wcur := pcur + BitVec.ofNat 64 (4 * acc.length)
    let poolUsed' := poolUsed + (acc.length + 1)
    storeOk m i32 wcur ∧
    (∀ f, (PoolUsed ⋆ ZeroTermInts pcur acc.reverse) f → region c.pbase (4 * poolUsed') f) ∧
    (word8Array c.hdr (c.hdrWords pcur0 cur0) ⋆
      (wsFixed c ptrs (PoolUsed ⋆ ZeroTermInts pcur acc.reverse) ⋆
        region (c.pbase + BitVec.ofNat 64 (4 * poolUsed')) (4 * (rem - 1)) ⋆
        Eq (bs.At base) ⋆ R))
      (storeMem m i32 wcur 0#32) := by
  intro pcur wcur poolUsed'
  have hfa := c.fit_active; unfold WorkCfg.activeBytes at hfa
  obtain ⟨ok_z, hm1⟩ := region_pop_store_int4_64 0#64 hrem (by omega)
    (sep_cast hm (by dsimp only [wcur, pcur]; ac_rfl) : (region wcur (4 * rem) ⋆
      (Eq (bs.At base) ⋆ word8Array c.hdr (c.hdrWords pcur0 cur0) ⋆
        wsFixed c ptrs PoolUsed ⋆ int4Array pcur acc.reverse ⋆ R)) m)
  have hzt : ZeroTermInts pcur acc.reverse = (int4Array pcur acc.reverse ⋆ int4 wcur 0) := by
    rw [zeroTermInts_eq_append, List.length_reverse]
  have hwcur2 : wcur + 4 = c.pbase + BitVec.ofNat 64 (4 * poolUsed') := by
    dsimp [wcur, pcur, poolUsed']; grind
  rw [hwcur2] at hm1
  refine ⟨ok_z, fun f hf => ?_, ?_⟩
  · rw [show 4 * poolUsed' = 4 * poolUsed + 4 * (acc.reverse.length + 1) by
      simp [poolUsed']; omega, region_split (by simp; omega)]
    exact sep_mono2 hpu (fun _ hg => zeroTermInts_to_region (by simp; omega) hg) f hf
  · unfold wsFixed at hm1 ⊢
    rw [hzt]
    exact sep_cast hm1 (by dsimp only [wcur, pcur]; ac_rfl)

/-! ### Exact typed callee contracts -/

/-- Exact contract for `lb_parse_dimacs_header(cnf_ptr, cnf_end, hdr)`. -/
def lbParseDimacsHeaderSpec : Spec [i64, i64, i64] [i64] := fun args m Q _ =>
  ∃ (cnf_ptr hdr : BitVec 64) (cnfBytes : List UInt8) (R : Mem 64 → Prop),
    args = (cnf_ptr, cnf_ptr + BitVec.ofNat 64 cnfBytes.length, hdr, ()) ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    hdr.toNat + 80 < 2 ^ 64 ∧
    (Eq (cnfBytes.At cnf_ptr) ⋆ region hdr 80 ⋆ R) m ∧
    ∀ (r : BitVec 64) (m' : Mem 64),
      (match parseHeader cnfBytes with
       | none =>
         r = 0 ∧ (Eq (cnfBytes.At cnf_ptr) ⋆ region hdr 80 ⋆ R) m'
       | some (mv, nc, rest) =>
         r = 1 ∧ mv < dimacsBound ∧ nc < dimacsBound ∧
         rest = cnfBytes.drop (cnfBytes.length - rest.length) ∧
         rest.length ≤ cnfBytes.length ∧
         ∃ w2 w3 w4 w5 w6 w7 w8 : BitVec 64,
           (Eq (cnfBytes.At cnf_ptr) ⋆
             word8Array hdr
               [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc, w2, w3, w4, w5, w6, w7, w8,
                cnf_ptr + BitVec.ofNat 64 (cnfBytes.length - rest.length)] ⋆ R) m') →
      Q (r, ()) m'

/-- Exact contract for `lb_parse_dimacs_body(cnf_end, hdr)`. -/
def lbParseDimacsBodySpec : Spec [i64, i64] [i64] := fun args m Q _ =>
  ∃ (c : WorkCfg) (cnf_ptr : BitVec 64) (cnfBytes : List UInt8) (idx0 : Nat)
    (R : Mem 64 → Prop),
    args = (cnf_ptr + BitVec.ofNat 64 cnfBytes.length, c.hdr, ()) ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    idx0 ≤ cnfBytes.length ∧
    (Eq (cnfBytes.At cnf_ptr) ⋆
      WorkState c 0 c.poolInts (cnf_ptr + BitVec.ofNat 64 idx0)
        (List.replicate c.cap 0) (List.replicate c.cap none) emp ⋆ R) m ∧
    ∀ (r : BitVec 64) (m' : Mem 64),
      (match parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) with
       | none =>
         r = 0 ∧ (Eq (cnfBytes.At cnf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m'
       | some (clauses, poolRem') =>
         r = 1 ∧ clauses.length = c.nc ∧ poolRem' ≤ c.poolInts ∧
         ∃ (ptrs : List (BitVec 64)) (PoolUsed : Mem 64 → Prop),
           (Eq (cnfBytes.At cnf_ptr) ⋆
             WorkState c (c.poolInts - poolRem') poolRem'
               (cnf_ptr + BitVec.ofNat 64 idx0)
               ptrs (initClauseTable c.cap clauses) PoolUsed ⋆ R) m') →
      Q (r, ()) m'

/-- Exact contract for `lb_read_add_lits(hdr, prf_end)`. -/
def lbReadAddLitsSpec : Spec [i64, i64] [i64] := fun args m Q _ =>
  ∃ (c : WorkCfg) (prf_ptr : BitVec 64) (prfBytes : List UInt8) (idx0 poolUsed poolRem : Nat)
    (ptrs : List (BitVec 64)) (table : List (Option (List (BitVec 64))))
    (PoolUsed R : Mem 64 → Prop),
    args = (c.hdr, prf_ptr + BitVec.ofNat 64 prfBytes.length, ()) ∧
    prf_ptr.toNat + prfBytes.length < 2 ^ 64 ∧
    idx0 ≤ prfBytes.length ∧
    (Eq (prfBytes.At prf_ptr) ⋆
      WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx0) ptrs table PoolUsed ⋆ R) m ∧
    ∀ (r : BitVec 64) (m' : Mem 64),
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
      Q (r, ()) m'

/-- Exact contract for `lb_rup_check(hdr, id, c_ptr, prf_end)`. -/
def lbRupCheckSpec : Spec [i64, i64, i64, i64] [i64] := fun args m Q _ =>
  ∃ (c : WorkCfg) (id : Nat) (c_ptr prf_ptr : BitVec 64) (prfBytes : List UInt8)
    (idx0 poolUsed poolRem : Nat) (clits ptrs : List (BitVec 64))
    (table : List (Option (List (BitVec 64)))) (PoolUsed R : Mem 64 → Prop),
    args = (c.hdr, BitVec.ofNat 64 id, c_ptr, prf_ptr + BitVec.ofNat 64 prfBytes.length, ()) ∧
    id < c.cap ∧
    prf_ptr.toNat + prfBytes.length < 2 ^ 64 ∧
    idx0 ≤ prfBytes.length ∧
    (∀ x ∈ clits, IsValidLit c.mv x) ∧
    (∃ R_c, PoolUsed = (ZeroTermInts c_ptr clits ⋆ R_c)) ∧
    (Eq (prfBytes.At prf_ptr) ⋆
      WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx0) ptrs table PoolUsed ⋆ R) m ∧
    ∀ (r : BitVec 64) (m' : Mem 64),
      (match rupCheckPure c.mv id clits table (prfBytes.drop idx0) with
       | none =>
         r = 0 ∧ (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m'
       | some bs' =>
         let idx' := prfBytes.length - bs'.length
         r = 1 ∧ bs' = prfBytes.drop idx' ∧ idx' ≤ prfBytes.length ∧
         (Eq (prfBytes.At prf_ptr) ⋆
           WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx')
             ptrs table PoolUsed ⋆ R) m') →
      Q (r, ()) m'

/-- Exact contract for `lb_check_prf(hdr, prf_end)`. -/
def lbCheckPrfSpec : Spec [i64, i64] [i64] := fun args m Q _ =>
  ∃ (c : WorkCfg) (prf_ptr : BitVec 64) (prfBytes : List UInt8) (poolUsed poolRem : Nat)
    (ptrs : List (BitVec 64)) (table : List (Option (List (BitVec 64))))
    (PoolUsed R : Mem 64 → Prop),
    args = (c.hdr, prf_ptr + BitVec.ofNat 64 prfBytes.length, ()) ∧
    prf_ptr.toNat + prfBytes.length < 2 ^ 64 ∧
    (Eq (prfBytes.At prf_ptr) ⋆
      WorkState c poolUsed poolRem prf_ptr ptrs table PoolUsed ⋆ R) m ∧
    ∀ (r : BitVec 64) (m' : Mem 64),
      r = (if checkPrfPure c.mv c.nc poolRem table prfBytes then 1 else 0) →
      (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m' →
      Q (r, ()) m'

/-- Exact contract for `lrat_check_bytes`. -/
def lratCheckBytesExactSpec : Spec [i64, i64, i64, i64, i64, i64] [i64] := fun args m Q _ =>
  ∃ (cnf_ptr prf_ptr work_ptr : BitVec 64) (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (R_mem : Mem 64 → Prop),
    args = (cnf_ptr, BitVec.ofNat 64 cnfBytes.length,
            prf_ptr, BitVec.ofNat 64 prfBytes.length,
            work_ptr, BitVec.ofNat 64 work_len, ()) ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    prf_ptr.toNat + prfBytes.length < 2 ^ 64 ∧
    work_ptr.toNat + work_len < 2 ^ 64 ∧
    ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆ R_mem) m ∧
    ∀ (r : BitVec 64) (m' : Mem 64),
      r = (if runLratCheckBytes cnfBytes prfBytes work_len then 1 else 0) →
      ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
        region work_ptr work_len) ⋆ R_mem) m' →
      Q (r, ()) m'

end LeanQbe.T.Examples.LratBytes
