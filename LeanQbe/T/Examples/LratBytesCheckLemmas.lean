module

public import LeanQbe.T.Examples.LratBytesSpec
import all Kraken.Separation

/-!
# Verification of `lbCheckPrf`, `lratCheckBytes`, and `checkPrfPure` soundness in `LeanQbe.T`

Proves:
1. Pure LRAT proof soundness (`checkPrfAux_sound_of`, `runLratCheckBytes_sound_of`).
2. `lbCheckPrf_correct_of`: total-correctness `Func.spec` of `lbCheckPrf` against `lbCheckPrfSpec`.
3. `lratCheckBytes_exact_of`: total-correctness `Func.spec` of `lratCheckBytes` against
   `lratCheckBytesExactSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.LratBytes

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT.Internal
open Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.ProofUtil

/-! ## 1. Pure stream-length, fuel-invariance, and literal-validity lemmas -/

private theorem readLeb128Pure_props {bs : List UInt8} {u : Nat} {bs' : List UInt8}
    (h : readLeb128Pure bs = some (u, bs')) :
    u < 2 ^ 28 ∧ bs'.length < bs.length ∧ bs' = bs.drop (bs.length - bs'.length) := by
  obtain ⟨hu, hlt, k, _, hkle, rfl⟩ := readLeb128Pure_some h
  grind

private theorem drop_trans_len {full bs' : List UInt8} {idx : Nat} (hidx : idx ≤ full.length)
    (h : bs' = (full.drop idx).drop ((full.drop idx).length - bs'.length))
    (hlen : bs'.length ≤ (full.drop idx).length) :
    bs' = full.drop (full.length - bs'.length) ∧ full.length - bs'.length ≤ full.length := by
  have hfl : (full.drop idx).length = full.length - idx := List.length_drop
  rw [List.drop_drop] at h
  grind

private theorem readAddLitsAux_zero {mv poolRem : Nat} {acc : List (BitVec 64)}
    {bs : List UInt8} :
    readAddLitsAux 0 mv poolRem acc bs = none := rfl

private theorem readAddLitsAux_succ {fuel mv poolRem : Nat} {acc : List (BitVec 64)}
    {bs : List UInt8} :
    readAddLitsAux (fuel + 1) mv poolRem acc bs =
      if poolRem == 0 then none
      else match readLeb128Pure bs with
      | none => none
      | some (0, bs') => some (acc.reverse, poolRem - 1, bs')
      | some (u, bs') =>
        let v := u / 2
        if v == 0 || mv < v then none
        else readAddLitsAux fuel mv (poolRem - 1) (decodeZigZag u :: acc) bs' := rfl

private theorem readAddLitsAux_succ_none {fuel mv poolRem : Nat} {acc : List (BitVec 64)}
    {bs : List UInt8} (hp : (poolRem == 0) = false) (h : readLeb128Pure bs = none) :
    readAddLitsAux (fuel + 1) mv poolRem acc bs = none := by
  rw [readAddLitsAux_succ, hp, h]; rfl

private theorem readAddLitsAux_succ_zero {fuel mv poolRem : Nat} {acc : List (BitVec 64)}
    {bs bs' : List UInt8} (hp : (poolRem == 0) = false)
    (h : readLeb128Pure bs = some (0, bs')) :
    readAddLitsAux (fuel + 1) mv poolRem acc bs = some (acc.reverse, poolRem - 1, bs') := by
  rw [readAddLitsAux_succ, hp, h]; rfl

private theorem readAddLitsAux_succ_nz {fuel mv poolRem : Nat} {acc : List (BitVec 64)}
    {bs bs' : List UInt8} {u_pred : Nat} (hp : (poolRem == 0) = false)
    (h : readLeb128Pure bs = some (u_pred + 1, bs')) :
    readAddLitsAux (fuel + 1) mv poolRem acc bs =
      (let v := (u_pred + 1) / 2
       if v == 0 || mv < v then none
       else readAddLitsAux fuel mv (poolRem - 1) (decodeZigZag (u_pred + 1) :: acc) bs') := by
  rw [readAddLitsAux_succ, hp, h]; rfl

private theorem consumeHintsAux_zero {id : Nat} {table : List (Option (List (BitVec 64)))}
    {bs : List UInt8} :
    consumeHintsAux 0 id table bs = none := rfl

private theorem consumeHintsAux_succ {fuel id : Nat}
    {table : List (Option (List (BitVec 64)))} {bs : List UInt8} :
    consumeHintsAux (fuel + 1) id table bs =
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
          else none := rfl

private theorem consumeHintsAux_succ_none {fuel id : Nat}
    {table : List (Option (List (BitVec 64)))} {bs : List UInt8}
    (h : readLeb128Pure bs = none) :
    consumeHintsAux (fuel + 1) id table bs = none := by
  rw [consumeHintsAux_succ, h]

private theorem consumeHintsAux_succ_zero {fuel id : Nat}
    {table : List (Option (List (BitVec 64)))} {bs bs' : List UInt8}
    (h : readLeb128Pure bs = some (0, bs')) :
    consumeHintsAux (fuel + 1) id table bs = some bs' := by
  rw [consumeHintsAux_succ, h]; rfl

private theorem consumeHintsAux_succ_nz {fuel id : Nat}
    {table : List (Option (List (BitVec 64)))} {bs bs' : List UInt8} {u_pred : Nat}
    (h : readLeb128Pure bs = some (u_pred + 1, bs')) :
    consumeHintsAux (fuel + 1) id table bs =
      (if (u_pred + 1) % 2 != 0 then none
       else if (u_pred + 1) / 2 < id then
         match table[(u_pred + 1) / 2]? with
         | some (some _) => consumeHintsAux fuel id table bs'
         | _ => none
       else none) := by
  rw [consumeHintsAux_succ, h]; rfl

private theorem rupPhase2Aux_zero {mv id : Nat} {table : List (Option (List (BitVec 64)))}
    {vals : List (BitVec 64)} {tl : Nat} {bs : List UInt8} :
    rupPhase2Aux 0 mv id table vals tl bs = none := rfl

private theorem rupPhase2Aux_succ {fuel mv id : Nat}
    {table : List (Option (List (BitVec 64)))} {vals : List (BitVec 64)} {tl : Nat}
    {bs : List UInt8} :
    rupPhase2Aux (fuel + 1) mv id table vals tl bs =
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
              match rupInnerPure mv alits 0 vals tl with
              | none => none
              | some (unit, vals', trailLen') =>
                if unit != 0 then
                  rupPhase2Aux fuel mv id table vals' trailLen' bs'
                else
                  consumeHintsPure id table bs'
            | _ => none
          else none := rfl

private theorem rupPhase2Aux_succ_none {fuel mv id : Nat}
    {table : List (Option (List (BitVec 64)))} {vals : List (BitVec 64)} {tl : Nat}
    {bs : List UInt8} (h : readLeb128Pure bs = none) :
    rupPhase2Aux (fuel + 1) mv id table vals tl bs = none := by
  rw [rupPhase2Aux_succ, h]

private theorem rupPhase2Aux_succ_zero {fuel mv id : Nat}
    {table : List (Option (List (BitVec 64)))} {vals : List (BitVec 64)} {tl : Nat}
    {bs bs' : List UInt8} (h : readLeb128Pure bs = some (0, bs')) :
    rupPhase2Aux (fuel + 1) mv id table vals tl bs = none := by
  rw [rupPhase2Aux_succ, h]; rfl

private theorem rupPhase2Aux_succ_nz {fuel mv id : Nat}
    {table : List (Option (List (BitVec 64)))} {vals : List (BitVec 64)} {tl : Nat}
    {bs bs' : List UInt8} {u_pred : Nat}
    (h : readLeb128Pure bs = some (u_pred + 1, bs')) :
    rupPhase2Aux (fuel + 1) mv id table vals tl bs =
      (if (u_pred + 1) % 2 != 0 then none
       else if (u_pred + 1) / 2 < id then
         match table[(u_pred + 1) / 2]? with
         | some (some alits) =>
           match rupInnerPure mv alits 0 vals tl with
           | none => none
           | some (unit, vals', trailLen') =>
             if unit != 0 then
               rupPhase2Aux fuel mv id table vals' trailLen' bs'
             else
               consumeHintsPure id table bs'
         | _ => none
       else none) := by
  rw [rupPhase2Aux_succ, h]; rfl

private theorem rupCheckPure_def (mv id : Nat) (clits : List (BitVec 64))
    (table : List (Option (List (BitVec 64)))) (bs : List UInt8) :
    rupCheckPure mv id clits table bs =
      match rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 with
      | .fail => none
      | .taut => consumeHintsPure id table bs
      | .ok vals trailLen =>
        rupPhase2Aux (bs.length + 1) mv id table vals trailLen bs := rfl

private theorem delLoopAux_zero {cap : Nat} {table : List (Option (List (BitVec 64)))}
    {bs : List UInt8} :
    delLoopAux 0 cap table bs = none := rfl

private theorem delLoopAux_succ {fuel cap : Nat}
    {table : List (Option (List (BitVec 64)))} {bs : List UInt8} :
    delLoopAux (fuel + 1) cap table bs =
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
          | _ => none := rfl

private theorem delLoopAux_succ_none {fuel cap : Nat}
    {table : List (Option (List (BitVec 64)))} {bs : List UInt8}
    (h : readLeb128Pure bs = none) :
    delLoopAux (fuel + 1) cap table bs = none := by
  rw [delLoopAux_succ, h]

private theorem delLoopAux_succ_zero {fuel cap : Nat}
    {table : List (Option (List (BitVec 64)))} {bs bs' : List UInt8}
    (h : readLeb128Pure bs = some (0, bs')) :
    delLoopAux (fuel + 1) cap table bs = some (table, bs') := by
  rw [delLoopAux_succ, h]; rfl

private theorem delLoopAux_succ_nz {fuel cap : Nat}
    {table : List (Option (List (BitVec 64)))} {bs bs' : List UInt8} {u_pred : Nat}
    (h : readLeb128Pure bs = some (u_pred + 1, bs')) :
    delLoopAux (fuel + 1) cap table bs =
      (if (u_pred + 1) % 2 != 0 then none
       else if (u_pred + 1) / 2 == 0 || !((u_pred + 1) / 2 < cap) then none
       else match table[(u_pred + 1) / 2]? with
       | some (some _) => delLoopAux fuel cap (table.set ((u_pred + 1) / 2) none) bs'
       | _ => none) := by
  rw [delLoopAux_succ, h]; rfl

private theorem delLoopAux_succ_step {fuel cap : Nat}
    {table : List (Option (List (BitVec 64)))} {bs bs' : List UInt8}
    {u_pred : Nat} {dlits : List (BitVec 64)}
    (hleb : readLeb128Pure bs = some (u_pred + 1, bs'))
    (heven : ((u_pred + 1) % 2 != 0) = false)
    (hnz : (((u_pred + 1) / 2) == 0) = false)
    (hlt : (u_pred + 1) / 2 < cap)
    (hget : table[(u_pred + 1) / 2]? = some (some dlits)) :
    delLoopAux (fuel + 1) cap table bs =
      delLoopAux fuel cap (table.set ((u_pred + 1) / 2) none) bs' := by
  rw [delLoopAux_succ_nz hleb, heven, hnz]
  simp only [hlt, decide_true, Bool.false_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hget]

private theorem checkPrfAux_zero {mv nc poolRem : Nat}
    {table : List (Option (List (BitVec 64)))} {bs : List UInt8} :
    checkPrfAux 0 mv nc poolRem table bs = false := rfl

private theorem checkPrfAux_nil {fuel mv nc poolRem : Nat}
    {table : List (Option (List (BitVec 64)))} :
    checkPrfAux fuel mv nc poolRem table [] = false := by
  cases fuel <;> rfl

private theorem checkPrfAux_succ {fuel mv nc poolRem : Nat}
    {table : List (Option (List (BitVec 64)))} {tag : UInt8} {bs1 : List UInt8} :
    checkPrfAux (fuel + 1) mv nc poolRem table (tag :: bs1) =
      if tag == 97 then
        match readLeb128Pure bs1 with
        | none => false
        | some (uid, bs2) =>
          if uid % 2 != 0 then false
          else
            let id := uid / 2
            if !(nc < id) || !(id < table.length) then false
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
        match delLoopAux (bs1.length + 1) table.length table bs1 with
        | none => false
        | some (table', bs2) => checkPrfAux fuel mv nc poolRem table' bs2
      else false := rfl

private theorem checkPrfAux_succ_97_empty {fuel mv nc poolRem : Nat}
    {table : List (Option (List (BitVec 64)))} {tag : UInt8}
    {bs1 bs2 bs3 bs4 : List UInt8} {uid poolRem' : Nat} {clits : List (BitVec 64)}
    (htag : (tag == 97) = true)
    (hleb : readLeb128Pure bs1 = some (uid, bs2))
    (heven : (uid % 2 != 0) = false)
    (hlo : nc < uid / 2) (hhi : uid / 2 < table.length)
    (hti : table[uid / 2]? = some none)
    (hread : readAddLitsPure mv poolRem bs2 = some (clits, poolRem', bs3))
    (hrup : rupCheckPure mv (uid / 2) clits table bs3 = some bs4)
    (hemp : clits.isEmpty = true) :
    checkPrfAux (fuel + 1) mv nc poolRem table (tag :: bs1) = true := by
  have hbnd : (!(nc < uid / 2) || !(uid / 2 < table.length)) = false := by
    simp only [hlo, hhi, decide_true, Bool.not_true, Bool.false_or]
  rw [checkPrfAux_succ, htag]
  simp only [↓reduceIte, hleb, heven, Bool.false_eq_true, hbnd, hti, hread, hrup, hemp]

private theorem checkPrfAux_succ_97_nonempty {fuel mv nc poolRem : Nat}
    {table : List (Option (List (BitVec 64)))} {tag : UInt8}
    {bs1 bs2 bs3 bs4 : List UInt8} {uid poolRem' : Nat} {clits : List (BitVec 64)}
    (htag : (tag == 97) = true)
    (hleb : readLeb128Pure bs1 = some (uid, bs2))
    (heven : (uid % 2 != 0) = false)
    (hlo : nc < uid / 2) (hhi : uid / 2 < table.length)
    (hti : table[uid / 2]? = some none)
    (hread : readAddLitsPure mv poolRem bs2 = some (clits, poolRem', bs3))
    (hrup : rupCheckPure mv (uid / 2) clits table bs3 = some bs4)
    (hnemp : clits.isEmpty = false) :
    checkPrfAux (fuel + 1) mv nc poolRem table (tag :: bs1) =
      checkPrfAux fuel mv nc poolRem' (table.set (uid / 2) (some clits)) bs4 := by
  have hbnd : (!(nc < uid / 2) || !(uid / 2 < table.length)) = false := by
    simp only [hlo, hhi, decide_true, Bool.not_true, Bool.false_or]
  rw [checkPrfAux_succ, htag]
  simp only [↓reduceIte, hleb, heven, Bool.false_eq_true, hbnd, hti, hread, hrup, hnemp]

private theorem checkPrfAux_succ_100_step {fuel mv nc poolRem : Nat}
    {table table' : List (Option (List (BitVec 64)))} {tag : UInt8}
    {bs1 bs2 : List UInt8}
    (htag_ne : (tag == 97) = false) (htag : (tag == 100) = true)
    (hdel : delLoopAux (bs1.length + 1) table.length table bs1 = some (table', bs2)) :
    checkPrfAux (fuel + 1) mv nc poolRem table (tag :: bs1) =
      checkPrfAux fuel mv nc poolRem table' bs2 := by
  rw [checkPrfAux_succ, htag_ne, htag]
  simp only [Bool.false_eq_true, ↓reduceIte, hdel]

private theorem initClauseTable_def (cap : Nat) (clauses : List (List (BitVec 64))) :
    initClauseTable cap clauses =
      none :: clauses.map some ++ List.replicate (cap - (clauses.length + 1)) none := rfl

private theorem runLratCheckBytes_def (cnfBytes prfBytes : List UInt8) (work_len : Nat) :
    runLratCheckBytes cnfBytes prfBytes work_len =
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
              checkPrfPure mv nc pool_ints' (initClauseTable cap clauses) prfBytes := rfl

private theorem runLratCheckBytes_lt128 {cnfBytes prfBytes : List UInt8} {work_len : Nat}
    (h : work_len < 128) : runLratCheckBytes cnfBytes prfBytes work_len = false := by
  rw [runLratCheckBytes_def]; simp only [h, ↓reduceIte]

private theorem runLratCheckBytes_hdr_none {cnfBytes prfBytes : List UInt8} {work_len : Nat}
    (h128 : ¬ (work_len < 128)) (hhdr : parseHeader cnfBytes = none) :
    runLratCheckBytes cnfBytes prfBytes work_len = false := by
  rw [runLratCheckBytes_def]; simp only [h128, ↓reduceIte]; rw [hhdr]

private theorem readAddLitsAux_lt {fuel mv poolRem : Nat} {acc : List (BitVec 64)}
    {bs : List UInt8} {clits : List (BitVec 64)} {poolRem' : Nat} {bs' : List UInt8}
    (h : readAddLitsAux fuel mv poolRem acc bs = some (clits, poolRem', bs')) :
    bs'.length < bs.length := by
  induction fuel generalizing poolRem acc bs with
  | zero => rw [readAddLitsAux_zero] at h; nomatch h
  | succ fuel ih =>
    cases hpool : (poolRem == 0)
    · rcases heq : readLeb128Pure bs with _ | ⟨_ | u_pred, bs1⟩
      · rw [readAddLitsAux_succ_none hpool heq] at h; nomatch h
      · rw [readAddLitsAux_succ_zero hpool heq] at h
        obtain ⟨_, _, rfl⟩ := Option.some.inj h
        exact (readLeb128Pure_props heq).2.1
      · rw [readAddLitsAux_succ_nz hpool heq] at h; dsimp only at h
        cases hv : ((u_pred + 1) / 2 == 0 || mv < (u_pred + 1) / 2)
        · rw [hv] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
          have hlt1 := (readLeb128Pure_props heq).2.1
          have hlt2 := ih h
          omega
        · rw [hv] at h; nomatch h
    · rw [readAddLitsAux_succ, hpool] at h; nomatch h

private theorem readAddLitsPure_lt {mv poolRem : Nat} {bs : List UInt8}
    {clits : List (BitVec 64)} {poolRem' : Nat} {bs' : List UInt8}
    (h : readAddLitsPure mv poolRem bs = some (clits, poolRem', bs')) :
    bs'.length < bs.length :=
  readAddLitsAux_lt h

private theorem consumeHintsAux_lt {fuel id : Nat} {table : List (Option (List (BitVec 64)))}
    {bs bs' : List UInt8} (h : consumeHintsAux fuel id table bs = some bs') :
    bs'.length < bs.length := by
  induction fuel generalizing bs with
  | zero => rw [consumeHintsAux_zero] at h; nomatch h
  | succ fuel ih =>
    rcases heq : readLeb128Pure bs with _ | ⟨_ | u_pred, bs1⟩
    · rw [consumeHintsAux_succ_none heq] at h; nomatch h
    · rw [consumeHintsAux_succ_zero heq] at h
      obtain rfl := Option.some.inj h
      exact (readLeb128Pure_props heq).2.1
    · rw [consumeHintsAux_succ_nz heq] at h
      have hlt1 := (readLeb128Pure_props heq).2.1
      cases hodd : ((u_pred + 1) % 2 != 0)
      · rw [hodd] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
        by_cases haid : (u_pred + 1) / 2 < id
        · simp only [haid, ↓reduceIte] at h
          rcases htbl : table[(u_pred + 1) / 2]? with _ | _ | alits
          · rw [htbl] at h; nomatch h
          · rw [htbl] at h; nomatch h
          · rw [htbl] at h; dsimp only at h
            have hlt2 := ih h; omega
        · simp only [haid, ↓reduceIte] at h; nomatch h
      · rw [hodd] at h; nomatch h

private theorem rupPhase2Aux_lt {fuel mv id : Nat} {table : List (Option (List (BitVec 64)))}
    {vals : List (BitVec 64)} {tl : Nat} {bs bs' : List UInt8}
    (h : rupPhase2Aux fuel mv id table vals tl bs = some bs') :
    bs'.length < bs.length := by
  induction fuel generalizing vals tl bs with
  | zero => rw [rupPhase2Aux_zero] at h; nomatch h
  | succ fuel ih =>
    rcases heq : readLeb128Pure bs with _ | ⟨_ | u_pred, bs1⟩
    · rw [rupPhase2Aux_succ_none heq] at h; nomatch h
    · rw [rupPhase2Aux_succ_zero heq] at h; nomatch h
    · rw [rupPhase2Aux_succ_nz heq] at h
      have hlt1 := (readLeb128Pure_props heq).2.1
      cases hodd : ((u_pred + 1) % 2 != 0)
      · rw [hodd] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
        by_cases haid : (u_pred + 1) / 2 < id
        · simp only [haid, ↓reduceIte] at h
          rcases htbl : table[(u_pred + 1) / 2]? with _ | _ | alits
          · rw [htbl] at h; nomatch h
          · rw [htbl] at h; nomatch h
          · rw [htbl] at h; dsimp only at h
            rcases hinner : rupInnerPure mv alits 0 vals tl with _ | ⟨unit, vals', tl'⟩
            · rw [hinner] at h; nomatch h
            · rw [hinner] at h; dsimp only at h
              cases hu : (unit != 0)
              · rw [hu] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
                have hlt2 := consumeHintsAux_lt h; omega
              · rw [hu] at h; simp only [↓reduceIte] at h
                have hlt2 := ih h; omega
        · simp only [haid, ↓reduceIte] at h; nomatch h
      · rw [hodd] at h; nomatch h

private theorem rupCheckPure_lt {mv id : Nat} {clits : List (BitVec 64)}
    {table : List (Option (List (BitVec 64)))} {bs bs' : List UInt8}
    (h : rupCheckPure mv id clits table bs = some bs') :
    bs'.length < bs.length := by
  rw [rupCheckPure_def] at h
  cases hp1 : rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 with
  | fail => rw [hp1] at h; nomatch h
  | taut => rw [hp1] at h; dsimp only at h; exact consumeHintsAux_lt h
  | ok vals tl => rw [hp1] at h; dsimp only at h; exact rupPhase2Aux_lt h

private theorem delLoopAux_props {fuel cap : Nat} {table : List (Option (List (BitVec 64)))}
    {bs : List UInt8} {table' : List (Option (List (BitVec 64)))} {bs' : List UInt8}
    (h : delLoopAux fuel cap table bs = some (table', bs')) :
    bs'.length < bs.length ∧ bs' = bs.drop (bs.length - bs'.length) := by
  induction fuel generalizing table bs with
  | zero => rw [delLoopAux_zero] at h; nomatch h
  | succ fuel ih =>
    rcases heq : readLeb128Pure bs with _ | ⟨_ | u_pred, bs1⟩
    · rw [delLoopAux_succ_none heq] at h; nomatch h
    · rw [delLoopAux_succ_zero heq] at h
      obtain ⟨_, rfl⟩ := Option.some.inj h
      exact ⟨(readLeb128Pure_props heq).2.1, (readLeb128Pure_props heq).2.2⟩
    · rw [delLoopAux_succ_nz heq] at h
      obtain ⟨_, hlt1, hdrop1⟩ := readLeb128Pure_props heq
      cases hodd : ((u_pred + 1) % 2 != 0)
      · rw [hodd] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases hbnd : ((u_pred + 1) / 2 == 0 || !((u_pred + 1) / 2 < cap))
        · rw [hbnd] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
          rcases htbl : table[(u_pred + 1) / 2]? with _ | _ | dlits
          · rw [htbl] at h; nomatch h
          · rw [htbl] at h; nomatch h
          · rw [htbl] at h; dsimp only at h
            obtain ⟨hlt2, hdrop2⟩ := ih h
            refine ⟨by omega, ?_⟩
            rw [hdrop1] at hdrop2
            exact (drop_trans_len (by omega) hdrop2 (by rw [← hdrop1]; omega)).1
        · rw [hbnd] at h; nomatch h
      · rw [hodd] at h; nomatch h

private theorem delLoopAux_fuel_irrel {f1 f2 cap : Nat} {table : List (Option (List (BitVec 64)))}
    {bs : List UInt8} (hf1 : bs.length < f1) (hf2 : bs.length < f2) :
    delLoopAux f1 cap table bs = delLoopAux f2 cap table bs := by
  induction f1 generalizing f2 table bs with
  | zero => omega
  | succ f1 ih =>
    cases f2 with
    | zero => omega
    | succ f2 =>
      rcases heq : readLeb128Pure bs with _ | ⟨_ | u_pred, bs1⟩
      · rw [delLoopAux_succ_none heq, delLoopAux_succ_none heq]
      · rw [delLoopAux_succ_zero heq, delLoopAux_succ_zero heq]
      · rw [delLoopAux_succ_nz heq, delLoopAux_succ_nz heq]
        have hlt1 := (readLeb128Pure_props heq).2.1
        cases hodd : ((u_pred + 1) % 2 != 0)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases hbnd : ((u_pred + 1) / 2 == 0 || !((u_pred + 1) / 2 < cap))
          · simp only [Bool.false_eq_true, ↓reduceIte]
            rcases htbl : table[(u_pred + 1) / 2]? with _ | _ | dlits
            · rfl
            · rfl
            · dsimp only
              exact ih (by omega) (by omega)
          · simp only [↓reduceIte]
        · simp only [↓reduceIte]

private theorem checkPrfAux_fuel_irrel {f1 f2 mv nc poolRem : Nat}
    {table : List (Option (List (BitVec 64)))} {bs : List UInt8}
    (hf1 : bs.length < f1) (hf2 : bs.length < f2) :
    checkPrfAux f1 mv nc poolRem table bs = checkPrfAux f2 mv nc poolRem table bs := by
  induction f1 generalizing f2 poolRem table bs with
  | zero => omega
  | succ f1 ih =>
    cases f2 with
    | zero => omega
    | succ f2 =>
      cases bs with
      | nil => rw [checkPrfAux_nil, checkPrfAux_nil]
      | cons tag bs1 =>
        have hbs1 : bs1.length < f1 ∧ bs1.length < f2 := by simp at hf1 hf2; omega
        rw [checkPrfAux_succ, checkPrfAux_succ]
        cases h97 : (tag == 97)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases h100 : (tag == 100)
          · simp only [Bool.false_eq_true, ↓reduceIte]
          · simp only [↓reduceIte]
            rcases heqd : delLoopAux (bs1.length + 1) table.length table bs1 with
              _ | ⟨table', bs2⟩
            · rfl
            · dsimp only
              obtain ⟨hltd, _⟩ := delLoopAux_props heqd
              exact ih (by omega) (by omega)
        · simp only [↓reduceIte]
          rcases heq1 : readLeb128Pure bs1 with _ | ⟨uid, bs2⟩
          · rfl
          · dsimp only
            have hlt1 := (readLeb128Pure_props heq1).2.1
            cases hodd : (uid % 2 != 0)
            · simp only [Bool.false_eq_true, ↓reduceIte]
              cases hbnd : (!(nc < uid / 2) || !(uid / 2 < table.length))
              · simp only [Bool.false_eq_true, ↓reduceIte]
                rcases htbl : table[uid / 2]? with _ | _ | _
                · rfl
                · dsimp only
                  rcases heq2 : readAddLitsPure mv poolRem bs2 with _ | ⟨clits, poolRem', bs3⟩
                  · rfl
                  · dsimp only
                    have hlt2 := readAddLitsPure_lt heq2
                    rcases heq3 : rupCheckPure mv (uid / 2) clits table bs3 with _ | bs4
                    · rfl
                    · dsimp only
                      have hlt3 := rupCheckPure_lt heq3
                      cases hemp : clits.isEmpty
                      · simp only [Bool.false_eq_true, ↓reduceIte]
                        exact ih (by omega) (by omega)
                      · simp only [↓reduceIte]
                · rfl
              · simp only [↓reduceIte]
            · simp only [↓reduceIte]

private theorem readAddLitsAux_valid {fuel mv poolRem : Nat} {acc : List (BitVec 64)}
    {bs : List UInt8} {clits : List (BitVec 64)} {poolRem' : Nat} {bs' : List UInt8}
    (hmv : mv < dimacsBound) (hacc : ∀ x ∈ acc, IsValidLit mv x)
    (h : readAddLitsAux fuel mv poolRem acc bs = some (clits, poolRem', bs')) :
    ∀ x ∈ clits, IsValidLit mv x := by
  induction fuel generalizing poolRem acc bs with
  | zero => rw [readAddLitsAux_zero] at h; nomatch h
  | succ fuel ih =>
    cases hpool : (poolRem == 0)
    · rcases heq : readLeb128Pure bs with _ | ⟨_ | u_pred, bs1⟩
      · rw [readAddLitsAux_succ_none hpool heq] at h; nomatch h
      · rw [readAddLitsAux_succ_zero hpool heq] at h
        obtain ⟨rfl, _, _⟩ := Option.some.inj h
        intro x hx; exact hacc x (List.mem_reverse.mp hx)
      · rw [readAddLitsAux_succ_nz hpool heq] at h; dsimp only at h
        obtain ⟨hu, _, _⟩ := readLeb128Pure_props heq
        cases hbad : ((u_pred + 1) / 2 == 0 || mv < (u_pred + 1) / 2)
        · rw [hbad] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
          simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not] at hbad
          have hv_valid := isValidLit_decodeZigZag hu (by omega) (by omega) hmv
          exact ih (fun x hx => by
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hv_valid
            · exact hacc x hx) h
        · rw [hbad] at h; nomatch h
    · rw [readAddLitsAux_succ, hpool] at h; nomatch h

private theorem readAddLitsPure_valid {mv poolRem : Nat} {bs : List UInt8}
    {clits : List (BitVec 64)} {poolRem' : Nat} {bs' : List UInt8}
    (hmv : mv < dimacsBound)
    (h : readAddLitsPure mv poolRem bs = some (clits, poolRem', bs')) :
    ∀ x ∈ clits, IsValidLit mv x :=
  readAddLitsAux_valid hmv (by simp) h

/-! ## 2. Pure LRAT proof soundness (`checkPrfAux_sound_of`, `runLratCheckBytes_sound_of`) -/

/-- Every active clause in `table` has valid literals in `1..mv` and is entailed by `F`. -/
private abbrev TableSound (mv : Nat) (F : CNF Nat)
    (table : List (Option (List (BitVec 64)))) : Prop :=
  ∀ (i : Nat) (lits : List (BitVec 64)), table[i]? = some (some lits) →
    (∀ x ∈ lits, IsValidLit mv x) ∧ CNF.EntailsClause F (toClause lits)

private theorem entailsClause_add_mono {F : CNF Nat} {c d : CNF.Clause Nat}
    (h : CNF.EntailsClause F d) : CNF.EntailsClause (F.add c) d := by
  rw [CNF.entails_clause_def] at h ⊢
  intro a ha
  rw [CNF.sat_def, CNF.eval_add, Bool.and_eq_true] at ha
  exact h a ((CNF.sat_def a F).mpr ha.2)

private theorem entailsClause_add_self (F : CNF Nat) (c : CNF.Clause Nat) :
    CNF.EntailsClause (F.add c) c := by
  rw [CNF.entails_clause_def]
  intro a ha
  rw [CNF.sat_def, CNF.eval_add, Bool.and_eq_true] at ha
  exact (CNF.Clause.sat_def a c).mpr ha.1

private theorem foldl_add_entails {clauses : List (List (BitVec 64))} {F : CNF Nat}
    {c : CNF.Clause Nat} (hc : CNF.EntailsClause F c) :
    CNF.EntailsClause (clauses.foldl (fun acc lits => acc.add (toClause lits)) F) c := by
  induction clauses generalizing F with
  | nil => exact hc
  | cons hd tl ih => exact ih (entailsClause_add_mono hc)

private theorem foldl_mem_entails {clauses : List (List (BitVec 64))} {F : CNF Nat}
    {lits : List (BitVec 64)} (hmem : lits ∈ clauses) :
    CNF.EntailsClause (clauses.foldl (fun acc ls => acc.add (toClause ls)) F) (toClause lits) := by
  induction clauses generalizing F with
  | nil => nomatch hmem
  | cons hd tl ih =>
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact @foldl_add_entails tl (F.add (toClause lits)) (toClause lits)
        (entailsClause_add_self F (toClause lits))
    · exact ih htl

private theorem tableSound_set_none {mv : Nat} {F : CNF Nat}
    {table : List (Option (List (BitVec 64)))} (ht : TableSound mv F table) (did : Nat) :
    TableSound mv F (table.set did none) := by
  intro i lits hi
  by_cases h : i = did
  · subst h
    by_cases hlt : i < table.length
    · rw [List.getElem?_set_self hlt] at hi; nomatch hi
    · rw [List.getElem?_eq_none (by rw [List.length_set]; omega)] at hi; nomatch hi
  · rw [List.getElem?_set_ne (Ne.symm h)] at hi
    exact ht i lits hi

private theorem tableSound_set_some {mv : Nat} {F : CNF Nat}
    {table : List (Option (List (BitVec 64)))} (ht : TableSound mv F table) (id : Nat)
    {clits : List (BitVec 64)} (hval : ∀ x ∈ clits, IsValidLit mv x)
    (hent : CNF.EntailsClause F (toClause clits)) :
    TableSound mv F (table.set id (some clits)) := by
  intro i lits hi
  by_cases h : i = id
  · subst h
    by_cases hlt : i < table.length
    · rw [List.getElem?_set_self hlt] at hi
      obtain rfl := Option.some.inj (Option.some.inj hi)
      exact ⟨hval, hent⟩
    · rw [List.getElem?_eq_none (by rw [List.length_set]; omega)] at hi; nomatch hi
  · rw [List.getElem?_set_ne (Ne.symm h)] at hi
    exact ht i lits hi

private theorem initClauseTable_sound {mv cap : Nat} {clauses : List (List (BitVec 64))}
    (hvalid : ∀ cl ∈ clauses, ∀ x ∈ cl, IsValidLit mv x) :
    TableSound mv (clauses.foldl (fun acc lits => acc.add (toClause lits)) CNF.empty)
      (initClauseTable cap clauses) := by
  intro i lits hget
  rw [initClauseTable_def] at hget
  cases i with
  | zero => simp at hget
  | succ j =>
    simp only [List.cons_append, List.getElem?_cons_succ] at hget
    by_cases hj : j < (clauses.map some).length
    · rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj, List.getElem_map] at hget
      simp only [Option.some.injEq] at hget
      subst hget
      have hj' : j < clauses.length := by simpa using hj
      have hmem := List.getElem_mem hj'
      exact ⟨hvalid _ hmem, foldl_mem_entails hmem⟩
    · grind

private theorem delLoopAux_sound {fuel cap mv : Nat} {F : CNF Nat}
    {table table' : List (Option (List (BitVec 64)))} {bs bs' : List UInt8}
    (ht : TableSound mv F table)
    (h : delLoopAux fuel cap table bs = some (table', bs')) :
    TableSound mv F table' := by
  induction fuel generalizing table bs with
  | zero => rw [delLoopAux_zero] at h; nomatch h
  | succ fuel ih =>
    rcases heq : readLeb128Pure bs with _ | ⟨_ | u_pred, bs1⟩
    · rw [delLoopAux_succ_none heq] at h; nomatch h
    · rw [delLoopAux_succ_zero heq] at h
      obtain ⟨rfl, _⟩ := Option.some.inj h
      exact ht
    · rw [delLoopAux_succ_nz heq] at h
      cases hodd : ((u_pred + 1) % 2 != 0)
      · rw [hodd] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases hbnd : ((u_pred + 1) / 2 == 0 || !((u_pred + 1) / 2 < cap))
        · rw [hbnd] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
          rcases htbl : table[(u_pred + 1) / 2]? with _ | _ | dlits
          · rw [htbl] at h; nomatch h
          · rw [htbl] at h; nomatch h
          · rw [htbl] at h; dsimp only at h
            exact ih (tableSound_set_none ht ((u_pred + 1) / 2)) h
        · rw [hbnd] at h; nomatch h
      · rw [hodd] at h; nomatch h

private theorem unsat_of_entails_empty {cnf₀ F : CNF Nat}
    (hent : cnf₀.Entails F) (hemp : CNF.EntailsClause F (toClause [])) :
    cnf₀.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro a ha
  have hF : F.Sat a := (CNF.entails_def cnf₀ F).mp hent a ha
  have hc : (toClause []).Sat a := CNF.entails_clause_def.mp hemp a hF
  rw [CNF.Clause.sat_def] at hc
  have hev : CNF.Clause.eval a (toClause []) = false := by
    have hem : toClause [] = CNF.Clause.empty := CNF.Clause.ext (by simp [toClause])
    rw [hem]
    exact CNF.Clause.eval_empty a
  grind

/-- Pure soundness of `checkPrfAux` given RUP step soundness `hrup_sound`. -/
private theorem checkPrfAux_sound_of
    (hrup_sound : ∀ {mv id : Nat} {clits : List (BitVec 64)}
      {table : List (Option (List (BitVec 64)))} {bs bs' : List UInt8} {F : CNF Nat},
      mv < dimacsBound →
      (∀ x ∈ clits, IsValidLit mv x) →
      (∀ aid < id, ∀ alits, table[aid]? = some (some alits) →
        (∀ x ∈ alits, IsValidLit mv x) ∧ CNF.EntailsClause F (toClause alits)) →
      rupCheckPure mv id clits table bs = some bs' →
      CNF.EntailsClause F (toClause clits))
    {fuel mv nc poolRem : Nat} {table : List (Option (List (BitVec 64)))} {bs : List UInt8}
    {cnf₀ F : CNF Nat}
    (hmv : mv < dimacsBound)
    (hent : cnf₀.Entails F)
    (htable : TableSound mv F table)
    (hchk : checkPrfAux fuel mv nc poolRem table bs = true) :
    cnf₀.Unsat := by
  induction fuel generalizing poolRem table bs F with
  | zero => rw [checkPrfAux_zero] at hchk; cases hchk
  | succ fuel ih =>
    cases bs with
    | nil => rw [checkPrfAux_nil] at hchk; cases hchk
    | cons tag bs1 =>
      rw [checkPrfAux_succ] at hchk
      cases h97 : (tag == 97)
      · rw [h97] at hchk; simp only [Bool.false_eq_true, ↓reduceIte] at hchk
        cases h100 : (tag == 100)
        · rw [h100] at hchk; simp only [Bool.false_eq_true, ↓reduceIte] at hchk
        · rw [h100] at hchk; simp only [↓reduceIte] at hchk
          rcases hdel : delLoopAux (bs1.length + 1) table.length table bs1 with _ | ⟨table', bs2⟩
          · rw [hdel] at hchk; cases hchk
          · rw [hdel] at hchk; dsimp only at hchk
            exact ih hent (delLoopAux_sound htable hdel) hchk
      · rw [h97] at hchk; simp only [↓reduceIte] at hchk
        rcases heq_uid : readLeb128Pure bs1 with _ | ⟨uid, bs2⟩
        · rw [heq_uid] at hchk; cases hchk
        · rw [heq_uid] at hchk; dsimp only at hchk
          cases hodd : (uid % 2 != 0)
          · rw [hodd] at hchk; simp only [Bool.false_eq_true, ↓reduceIte] at hchk
            cases hbnd : (!(nc < uid / 2) || !(uid / 2 < table.length))
            · rw [hbnd] at hchk; simp only [Bool.false_eq_true, ↓reduceIte] at hchk
              rcases htbl : table[uid / 2]? with _ | _ | _
              · rw [htbl] at hchk; cases hchk
              · rw [htbl] at hchk; dsimp only at hchk
                rcases hread : readAddLitsPure mv poolRem bs2 with _ | ⟨clits, poolRem', bs3⟩
                · rw [hread] at hchk; cases hchk
                · rw [hread] at hchk; dsimp only at hchk
                  have hclits := readAddLitsPure_valid hmv hread
                  rcases hrup : rupCheckPure mv (uid / 2) clits table bs3 with _ | bs4
                  · rw [hrup] at hchk; cases hchk
                  · rw [hrup] at hchk; dsimp only at hchk
                    have hent_cl : CNF.EntailsClause F (toClause clits) :=
                      hrup_sound hmv hclits (fun aid _ alits hget => htable aid alits hget) hrup
                    cases hemp : clits.isEmpty
                    · rw [hemp] at hchk; simp only [Bool.false_eq_true, ↓reduceIte] at hchk
                      exact ih hent (tableSound_set_some htable (uid / 2) hclits hent_cl) hchk
                    · have hnil : clits = [] := List.isEmpty_iff.mp hemp
                      subst hnil
                      exact unsat_of_entails_empty hent hent_cl
              · rw [htbl] at hchk; cases hchk
            · rw [hbnd] at hchk; cases hchk
          · rw [hodd] at hchk; cases hchk

private theorem parseHeader_bounds {bs : List UInt8} {mv nc : Nat} {rest : List UInt8}
    (h : parseHeader bs = some (mv, nc, rest)) : mv < dimacsBound ∧ nc < dimacsBound := by
  unfold parseHeader at h
  simp only [bind, Option.bind] at h
  split at h
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · rename_i bs3 _
        cases h2 : skipWs1 bs3 with
        | none => simp [h2] at h
        | some bs4 =>
          simp only [h2] at h
          cases hmv : parseNat bs4 with
          | none => simp [hmv] at h
          | some p1 =>
            rcases p1 with ⟨mv', bs5⟩
            simp only [hmv] at h
            cases h3 : skipWs1 bs5 with
            | none => simp [h3] at h
            | some bs6 =>
              simp only [h3] at h
              cases hnc : parseNat bs6 with
              | none => simp [hnc] at h
              | some p2 =>
                rcases p2 with ⟨nc', bs7⟩
                simp only [hnc, Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl, rfl⟩
                exact ⟨parseNat_lt_bound hmv, parseNat_lt_bound hnc⟩
      · cases h
  · cases h

/-- Pure soundness of `runLratCheckBytes` given `parseBodyPure_sound` and `rupCheckPure_sound`. -/
theorem runLratCheckBytes_sound_of
    (hbody_sound : ∀ {cnfBytes bodyRest : List UInt8} {mv nc poolInts poolRem' : Nat}
      {clauses : List (List (BitVec 64))},
      parseHeader cnfBytes = some (mv, nc, bodyRest) →
      mv < dimacsBound →
      parseBodyPure mv nc poolInts [] bodyRest = some (clauses, poolRem') →
      parseDimacs cnfBytes =
        some (clauses.foldl (fun c lits => c.add (toClause lits)) CNF.empty) ∧
      clauses.length = nc ∧
      (∀ cl ∈ clauses, ∀ x ∈ cl, IsValidLit mv x))
    (hrup_sound : ∀ {mv id : Nat} {clits : List (BitVec 64)}
      {table : List (Option (List (BitVec 64)))} {bs bs' : List UInt8} {F : CNF Nat},
      mv < dimacsBound →
      (∀ x ∈ clits, IsValidLit mv x) →
      (∀ aid < id, ∀ alits, table[aid]? = some (some alits) →
        (∀ x ∈ alits, IsValidLit mv x) ∧ CNF.EntailsClause F (toClause alits)) →
      rupCheckPure mv id clits table bs = some bs' →
      CNF.EntailsClause F (toClause clits))
    {cnfBytes prfBytes : List UInt8} {work_len : Nat}
    (hrun : runLratCheckBytes cnfBytes prfBytes work_len = true) :
    ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat := by
  rw [runLratCheckBytes_def] at hrun
  by_cases h128 : work_len < 128
  · simp only [h128, ↓reduceIte] at hrun; cases hrun
  · simp only [h128, ↓reduceIte] at hrun
    rcases hhdr : parseHeader cnfBytes with _ | ⟨mv, nc, bodyRest⟩
    · rw [hhdr] at hrun; cases hrun
    · rw [hhdr] at hrun; dsimp only at hrun
      have hmv := (parseHeader_bounds hhdr).1
      let fixed := 80 + ((mv + 8) / 8) * 8 + ((4 * (mv + 1) + 7) / 8) * 8
      change (if work_len < fixed then false else _) = true at hrun
      by_cases hfix : work_len < fixed
      · simp only [hfix, ↓reduceIte] at hrun; cases hrun
      · simp only [hfix, ↓reduceIte] at hrun
        let rem := work_len - fixed
        let c_half := rem / 16
        let want := nc + prfBytes.length % 268435456 + 32
        let cap := if c_half < want then c_half else want
        change (if cap ≤ nc then false else
          match parseBodyPure mv nc ((rem - 8 * cap) / 4) [] bodyRest with
          | none => false
          | some (clauses, pool_ints') =>
            checkPrfPure mv nc pool_ints' (initClauseTable cap clauses) prfBytes) = true at hrun
        by_cases hcap : cap ≤ nc
        · simp only [hcap, ↓reduceIte] at hrun; cases hrun
        · simp only [hcap, ↓reduceIte] at hrun
          rcases hbody : parseBodyPure mv nc ((rem - 8 * cap) / 4) [] bodyRest with
            _ | ⟨clauses, pool_ints'⟩
          · rw [hbody] at hrun; cases hrun
          · rw [hbody] at hrun; dsimp only at hrun
            obtain ⟨hdimacs, _, hcl_valid⟩ := hbody_sound hhdr hmv hbody
            let cnf₀ := clauses.foldl (fun c lits => c.add (toClause lits)) CNF.empty
            have hunsat : cnf₀.Unsat :=
              checkPrfAux_sound_of hrup_sound hmv (CNF.entails_refl cnf₀)
                (initClauseTable_sound hcl_valid) hrun
            exact ⟨cnf₀, hdimacs, hunsat⟩

/-! ## 3. `WorkState` accessors and verification of `lbCheckPrf` -/

private theorem workState_collapse {B R : Mem 64 → Prop} {c : WorkCfg}
    {poolUsed poolRem : Nat} {cur : BitVec 64} {ptrs : List (BitVec 64)}
    {table : List (Option (List (BitVec 64)))} {PoolUsed : Mem 64 → Prop} {m : Mem 64}
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    (B ⋆ region c.hdr c.activeBytes ⋆ R) m :=
  sep_mono2 (sep_mono2 (fun _ h => h) fun _ => WorkState.to_region) (fun _ h => h) m hm

private abbrev wsCbRest (c : WorkCfg) (poolUsed poolRem : Nat) (cur : BitVec 64)
    (PoolUsed B R : Mem 64 → Prop) : Mem 64 → Prop :=
  word8Array c.hdr (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) cur) ⋆
  byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
  region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
  region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw) ⋆
  PoolUsed ⋆ region (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) (4 * poolRem) ⋆ B ⋆ R

private theorem workState_tableRel {B R : Mem 64 → Prop} {c : WorkCfg}
    {poolUsed poolRem : Nat} {cur : BitVec 64} {ptrs : List (BitVec 64)}
    {table : List (Option (List (BitVec 64)))} {PoolUsed : Mem 64 → Prop} {m : Mem 64}
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    TableRel c.mv c.cap ptrs table PoolUsed :=
  (workState_sep.mp (sep_ac hm :
    (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ (B ⋆ R)) m)).2.1

private theorem workState_ld_hdr {B R : Mem 64 → Prop} {c : WorkCfg}
    {poolUsed poolRem : Nat} {cur p v : BitVec 64} {ptrs : List (BitVec 64)}
    {table : List (Option (List (BitVec 64)))} {PoolUsed : Mem 64 → Prop} {m : Mem 64}
    {Q : BitVec 64 → Prop} (i : Nat)
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m)
    (hp : p = c.hdr + BitVec.ofNat 64 (8 * i))
    (hi : (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) cur)[i]? = some v)
    (hk : Q v) :
    ∃ x, loadVal m i64 p = some x ∧ Q x := by
  obtain ⟨_, _, _, hwm⟩ := workState_sep.mp
    (sep_ac hm : (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ (B ⋆ R)) m)
  simp only [sep_assoc] at hwm
  exact ld_l_step c.hdr i hwm hp hi hk

private theorem workState_store_cur {B R : Mem 64 → Prop} {c : WorkCfg}
    {poolUsed poolRem : Nat} {cur cur' : BitVec 64} {ptrs : List (BitVec 64)}
    {table : List (Option (List (BitVec 64)))} {PoolUsed : Mem 64 → Prop} {m : Mem 64}
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    storeOk m i64 (c.hdr + 72) ∧
      (B ⋆ WorkState c poolUsed poolRem cur' ptrs table PoolUsed ⋆ R)
        (storeMem m i64 (c.hdr + 72) cur') := by
  obtain ⟨hsum, htr, hpu, hwm⟩ := workState_sep.mp
    (sep_ac hm : (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ (B ⋆ R)) m)
  simp only [sep_assoc] at hwm
  rw [show c.hdr + (72 : BitVec 64) = c.hdr + BitVec.ofNat 64 (8 * 9) from rfl]
  obtain ⟨hok, hm1⟩ := store_word8Array (i := 9) cur' (by simp [WorkCfg.hdrWords]) hwm
  have hset : (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) cur).set 9 cur' =
      c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) cur' := rfl
  rw [hset] at hm1
  exact ⟨hok, sep_ac (workState_sep.mpr ⟨hsum, htr, hpu, by simp only [sep_assoc]; exact hm1⟩)⟩

private theorem workState_cb_branch {B R : Mem 64 → Prop} {c : WorkCfg}
    {poolUsed poolRem : Nat} {cur : BitVec 64} {ptrs : List (BitVec 64)}
    {table : List (Option (List (BitVec 64)))} {PoolUsed : Mem 64 → Prop} {m : Mem 64}
    {i : Nat} {P Q : Prop} (hi : i < c.cap)
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m)
    (hsome : ∀ lits, table[i]? = some (some lits) → P)
    (hnone : table[i]? = some none → Q) :
    ∃ v, loadVal m i64 (c.cb + BitVec.ofNat 64 (8 * i)) = some v ∧
      ((v ≠ 0 → P) ∧ (v = 0 → Q)) := by
  obtain ⟨_, ⟨hplen, htlen, hrel⟩, _, hwm⟩ := workState_sep.mp
    (sep_ac hm : (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ (B ⋆ R)) m)
  have hwm_cb : (word8Array c.cb ptrs ⋆ wsCbRest c poolUsed poolRem cur PoolUsed B R) m := by
    dsimp only [wsCbRest]; exact sep_ac hwm
  refine ⟨_, load_word8Array (hplen ▸ hi) hwm_cb, ?_⟩
  have hri := hrel i hi
  have hget : table[i]? = some (table[i]'(htlen ▸ hi)) := List.getElem?_eq_getElem _
  cases hti : table[i]'(htlen ▸ hi) <;> rw [hti] at hri hget
  · exact ⟨fun h => absurd hri h, fun _ => hnone hget⟩
  · exact ⟨fun _ => hsome _ hget, fun h => absurd h hri.1⟩

private theorem workState_store_cb {B R : Mem 64 → Prop} {c : WorkCfg}
    {poolUsed poolRem : Nat} {cur v : BitVec 64} {ptrs : List (BitVec 64)}
    {table table' : List (Option (List (BitVec 64)))} {PoolUsed : Mem 64 → Prop} {m : Mem 64}
    {i : Nat} (hi : i < c.cap)
    (htr' : TableRel c.mv c.cap (ptrs.set i v) table' PoolUsed)
    (hm : (B ⋆ WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ R) m) :
    storeOk m i64 (c.cb + BitVec.ofNat 64 (8 * i)) ∧
      (B ⋆ WorkState c poolUsed poolRem cur (ptrs.set i v) table' PoolUsed ⋆ R)
        (storeMem m i64 (c.cb + BitVec.ofNat 64 (8 * i)) v) := by
  obtain ⟨hsum, ⟨hplen, _, _⟩, hpu, hwm⟩ := workState_sep.mp
    (sep_ac hm : (WorkState c poolUsed poolRem cur ptrs table PoolUsed ⋆ (B ⋆ R)) m)
  have hwm_cb : (word8Array c.cb ptrs ⋆ wsCbRest c poolUsed poolRem cur PoolUsed B R) m := by
    dsimp only [wsCbRest]; exact sep_ac hwm
  obtain ⟨hok, hm1⟩ := store_word8Array v (hplen ▸ hi) hwm_cb
  dsimp only [wsCbRest] at hm1
  have hm1_ws : ((word8Array c.hdr (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) cur) ⋆
      byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
      region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
      region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw) ⋆
      word8Array c.cb (ptrs.set i v) ⋆
      PoolUsed ⋆ region (c.pbase + BitVec.ofNat 64 (4 * poolUsed)) (4 * poolRem)) ⋆
      (B ⋆ R)) (storeMem m i64 (c.cb + BitVec.ofNat 64 (8 * i)) v) := sep_ac hm1
  exact ⟨hok, sep_ac (workState_sep.mpr ⟨hsum, htr', hpu, hm1_ws⟩)⟩

private theorem tableRel_set_none {mv cap : Nat} {ptrs : List (BitVec 64)}
    {table : List (Option (List (BitVec 64)))} {PoolUsed : Mem 64 → Prop} {did : Nat}
    (htr : TableRel mv cap ptrs table PoolUsed) :
    TableRel mv cap (ptrs.set did 0) (table.set did none) PoolUsed := by
  obtain ⟨hplen, htlen, hrel⟩ := htr
  refine ⟨by simp [hplen], by simp [htlen], fun i hi => ?_⟩
  grind

private theorem tableRel_set_some {mv cap : Nat} {ptrs : List (BitVec 64)}
    {table : List (Option (List (BitVec 64)))} {PoolUsed : Mem 64 → Prop}
    {id : Nat} {c_ptr : BitVec 64} {clits : List (BitVec 64)}
    (hc_ptr : c_ptr ≠ 0) (hclits : ∀ x ∈ clits, IsValidLit mv x)
    (hpool : ∃ R_c, PoolUsed = (ZeroTermInts c_ptr clits ⋆ R_c))
    (htr : TableRel mv cap ptrs table PoolUsed) :
    TableRel mv cap (ptrs.set id c_ptr) (table.set id (some clits)) PoolUsed := by
  obtain ⟨hplen, htlen, hrel⟩ := htr
  refine ⟨by simp [hplen], by simp [htlen], fun i hi => ?_⟩
  grind

private theorem apply_jfail {J : Cont []} {P : Tup Val [] → Mem 64 → Prop} {as : Tup Val []}
    {m : Mem 64} (hJ : ∀ as m, P as m → J as m) (hp : P as m) : J as m := hJ as m hp

local macro "fail_leaf" : tactic =>
  `(tactic| ((try refine ⟨fun h => absurd rfl h, fun _ => ?_⟩);
             apply apply_jfail ‹_›;
             refine ⟨
               by simp +zetaDelta [*, -List.getElem_cons_drop, -List.length_drop,
                    -bne_iff_ne, -getElem?_pos, checkPrfAux];
                  try simp +zetaDelta [*, -List.getElem_cons_drop, -List.length_drop,
                    -bne_iff_ne, -getElem?_pos, delLoopAux],
               by first | assumption | exact workState_collapse ‹_›⟩))

/-- Verification of `lbCheckPrf` against `lbCheckPrfSpec`, parameterized by `Γ` providing
`lbReadAddLitsSpec` and `lbRupCheckSpec`. -/
theorem lbCheckPrf_correct_of (Γ : Env)
    (hReadAddLits : ∀ args m Q X,
      lbReadAddLitsSpec args m Q X → Γ "lb_read_add_lits" [i64, i64] [i64] args m Q X)
    (hRupCheck : ∀ args m Q X,
      lbRupCheckSpec args m Q X → Γ "lb_rup_check" [i64, i64, i64, i64] [i64] args m Q X) :
    ∀ args m Q X, lbCheckPrfSpec args m Q X → Func.spec Γ lbCheckPrf args m Q X := by
  rintro _ m0 Q X ⟨c, prf_ptr, prfBytes, poolUsed0, poolRem0, ptrs0, table0, PoolUsed0, R,
    rfl, hprf_fit, hm0, hQ⟩
  unfold lbCheckPrf Func.spec Func.wp
  have hcap_bound : c.cap < 2 ^ 64 := by have := c.hfit; omega
  have hnc_bound : c.nc < 2 ^ 64 := by have := c.hnc; unfold dimacsBound at this; omega
  wp_unfold
  refine workState_ld_hdr 1 hm0 rfl rfl ?_
  refine workState_ld_hdr 2 hm0 rfl rfl ?_
  refine workState_ld_hdr 6 hm0 rfl rfl ?_
  -- `@fail` join point
  refine wp_join_group (fun () m' =>
    checkPrfPure c.mv c.nc poolRem0 table0 prfBytes = false ∧
    (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m') ?_ ?_
  · rintro _ ⟨⟩ m' ⟨hfalse, hm'⟩
    dsimp only [Blocks.get_here]; wp_unfold; exact hQ 0 m' (by simp [hfalse]) hm'
  intro Jfail hJfail
  -- `@rec_loop`
  refine wp_loop_group (fun r () m => ∃ idx poolUsed poolRem ptrs table PoolUsed,
    idx ≤ prfBytes.length ∧
    r = prfBytes.length - idx ∧
    checkPrfPure c.mv c.nc poolRem0 table0 prfBytes =
      checkPrfAux ((prfBytes.drop idx).length + 1) c.mv c.nc poolRem table (prfBytes.drop idx) ∧
    (Eq (prfBytes.At prf_ptr) ⋆
      WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx) ptrs table PoolUsed ⋆ R) m) ?_ ?_
  · rintro Jrec r ⟨⟩ m ih ⟨idx, poolUsed, poolRem, ptrs, table, PoolUsed,
      hidx, rfl, hpure, hm⟩
    have hlen_cap : table.length = c.cap := (workState_tableRel hm).2.1
    dsimp only [Blocks.get_here]; wp_unfold
    refine workState_ld_hdr 9 hm rfl rfl ?_
    refine cursor_eof_branch hidx (by omega)
      (fun hidx_end => by
        subst hidx_end
        refine hJfail () _ ⟨?_, workState_collapse hm⟩
        rw [hpure, List.drop_length]; rfl)
      (fun hidx_lt => by
        have hm_prf : (Eq (prfBytes.At prf_ptr) ⋆
            (WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx) ptrs table PoolUsed ⋆
              R)) m :=
          sep_cast hm (by ac_rfl)
        refine ⟨_, loadu8_At hidx_lt (by omega) hm_prf, ?_⟩
        rw [setWidth64_ofNat8]
        let tag := prfBytes[idx]
        let bs1 := prfBytes.drop (idx + 1)
        have hdrop_idx : prfBytes.drop idx = tag :: bs1 := List.drop_eq_getElem_cons hidx_lt
        rw [ptr_step_1]
        refine u8_eq_branch (fun htag97 => ?_) (fun htag_not97 => ?_)
        · -- `'a'` record
          refine readLeb128_spec hprf_fit (by omega) rfl rfl hm_prf
            (fun hleb_none => by fail_leaf)
            fun uid bs2 hleb_uid huid_lt _ hbs2_drop hidx2_gt => ?_
          rw [eq_comm] at hbs2_drop
          let idx2 := prfBytes.length - bs2.length
          have hidx2_le : idx2 ≤ prfBytes.length := Nat.sub_le _ _
          wp_unfold
          refine bv_odd_branch (by omega : uid < 2 ^ 64)
            (fun ho => by fail_leaf)
            (fun heven' => ?_)
          let id := uid / 2
          rw [bv_shr_one (by omega : uid < 2 ^ 64)]
          refine ult_branch hnc_bound (by omega : id < 2 ^ 64)
            (fun hnc_lt_id => ?_) (fun hid_le_nc => by fail_leaf)
          refine ult_branch (by omega : id < 2 ^ 64) hcap_bound
            (fun hid_lt_cap => ?_) (fun hid_ge_cap => by fail_leaf)
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : id < 2 ^ 64)]
          refine workState_cb_branch hid_lt_cap hm (fun _ hti => by fail_leaf) fun hti_none => ?_
          obtain ⟨hok_cur2, hm_cur2⟩ :=
            workState_store_cur (cur' := prf_ptr + BitVec.ofNat 64 idx2) hm
          refine ⟨hok_cur2, ?_⟩
          refine workState_ld_hdr 8 hm_cur2 rfl rfl ?_
          let c_ptr := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
          refine wp_call_ret1 _ _ _
            (hReadAddLits _ _ _ _ ⟨c, prf_ptr, prfBytes, idx2, poolUsed, poolRem,
              ptrs, table, PoolUsed, R, rfl, hprf_fit, hidx2_le, hm_cur2,
              fun r m1 hr => hr⟩) ?_
          rintro lstat m1 hread_res
          wp_unfold
          rw [hbs2_drop] at hread_res
          cases hread_eq : readAddLitsPure c.mv poolRem bs2 with
          | none =>
            rw [hread_eq] at hread_res; obtain ⟨rfl, hm1_reg⟩ := hread_res; fail_leaf
          | some val3 =>
            rcases val3 with ⟨clits, poolRem', bs3⟩
            rw [hread_eq] at hread_res
            obtain ⟨hlstat, hbs3_drop, hidx3_le, _, hc_ptr_nz, hclits_v, hm1⟩ := hread_res
            rw [eq_comm] at hbs3_drop
            let idx3 := prfBytes.length - bs3.length
            have hlstat_nz : lstat ≠ 0 := by rw [hlstat]; split <;> decide
            refine ⟨fun _ => ?_, fun h0 => absurd h0 hlstat_nz⟩
            let PoolUsed1 := PoolUsed ⋆ ZeroTermInts c_ptr clits
            refine wp_call_ret1 _ _ _
              (hRupCheck _ _ _ _ ⟨c, id, c_ptr, prf_ptr, prfBytes, idx3,
                poolUsed + (clits.length + 1), poolRem', clits, ptrs, table, PoolUsed1, R,
                rfl, hid_lt_cap, hprf_fit, hidx3_le, hclits_v,
                ⟨PoolUsed, sep_comm PoolUsed (ZeroTermInts c_ptr clits)⟩, hm1,
                fun r m2 hr => hr⟩) ?_
            rintro rok m2 hrup_res
            wp_unfold
            rw [hbs3_drop] at hrup_res
            cases hrup_eq : rupCheckPure c.mv id clits table bs3 with
            | none =>
              rw [hrup_eq] at hrup_res; obtain ⟨rfl, hm2_reg⟩ := hrup_res; fail_leaf
            | some bs4 =>
              rw [hrup_eq] at hrup_res
              obtain ⟨rfl, hbs4_drop, hidx4_le, hm2⟩ := hrup_res
              let idx4 := prfBytes.length - bs4.length
              refine ⟨fun _ => ?_, fun h0 => absurd h0 (by decide)⟩
              have hlstat2_iff : (lstat = (2 : BitVec 64)) ↔ clits.isEmpty = true := by
                rw [hlstat]; cases clits.isEmpty <;> decide
              refine ⟨fun hemp => ?_, fun hnemp => ?_⟩
              · have hemp' : clits.isEmpty = true := hlstat2_iff.mp hemp
                refine hQ 1 m2 ?_ (workState_collapse hm2)
                have htrue : checkPrfPure c.mv c.nc poolRem0 table0 prfBytes = true := by
                  rw [hpure, hdrop_idx]
                  exact checkPrfAux_succ_97_empty htag97 hleb_uid heven' hnc_lt_id
                    (hlen_cap ▸ hid_lt_cap) hti_none hread_eq hrup_eq hemp'
                simp [htrue]
              · have hnemp' : clits.isEmpty = false := by
                  cases hb : clits.isEmpty
                  · rfl
                  · exact absurd (hlstat2_iff.mpr hb) hnemp
                have htr_new := tableRel_set_some (id := id) hc_ptr_nz hclits_v
                  ⟨PoolUsed, sep_comm PoolUsed (ZeroTermInts c_ptr clits)⟩
                  (workState_tableRel hm2)
                obtain ⟨hok_cb, hm3⟩ := workState_store_cb hid_lt_cap htr_new hm2
                refine ⟨hok_cb, ?_⟩
                have hlt2 := readAddLitsPure_lt hread_eq
                have hlt3 := rupCheckPure_lt hrup_eq
                have hbs3_lt : bs3.length < bs2.length := by
                  have : (prfBytes.drop idx2).length = bs2.length := by rw [← hbs2_drop]
                  omega
                have hbs4_lt : bs4.length < bs3.length := by
                  have : (prfBytes.drop idx3).length = bs3.length := by rw [← hbs3_drop]
                  omega
                have hidx4_gt : idx < idx4 := by dsimp [idx4, idx2] at hidx2_gt ⊢; omega
                refine ih (prfBytes.length - idx4) () _ (by omega)
                  ⟨idx4, poolUsed + (clits.length + 1), poolRem',
                    ptrs.set id c_ptr, table.set id (some clits), PoolUsed1,
                    hidx4_le, rfl, ?_, hm3⟩
                rw [hpure, hdrop_idx]
                have hstep_aux :
                    checkPrfAux ((tag :: bs1).length + 1) c.mv c.nc poolRem table (tag :: bs1) =
                    checkPrfAux (bs1.length + 1) c.mv c.nc poolRem'
                      (table.set id (some clits)) bs4 :=
                  checkPrfAux_succ_97_nonempty htag97 hleb_uid heven' hnc_lt_id
                    (hlen_cap ▸ hid_lt_cap) hti_none hread_eq hrup_eq hnemp'
                rw [hstep_aux, ← hbs4_drop]
                exact checkPrfAux_fuel_irrel
                  (by have : bs1.length = prfBytes.length - (idx + 1) := List.length_drop; omega)
                  (by omega)
        · -- Not `'a'`: check `'d'` (`100`)
          refine u8_eq_branch (fun htag100 => ?_) (fun htag_not100 => by fail_leaf)
          -- `@del_loop`
          refine wp_loop_group (fun dr (dcur_v, ()) dm => ∃ didx dptrs dtable,
            dcur_v = prf_ptr + BitVec.ofNat 64 didx ∧
            idx + 1 ≤ didx ∧ didx ≤ prfBytes.length ∧
            dr = prfBytes.length - didx ∧
            delLoopAux (bs1.length + 1) c.cap table bs1 =
              delLoopAux ((prfBytes.drop didx).length + 1) c.cap dtable (prfBytes.drop didx) ∧
            (Eq (prfBytes.At prf_ptr) ⋆
              WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx)
                dptrs dtable PoolUsed ⋆ R) dm) ?_ ?_
          · rintro Jdel dr ⟨dcur_v, ⟨⟩⟩ dm ih_del
              ⟨didx, dptrs, dtable, rfl, hdidx_lo, hdidx_hi, rfl, hdel_eq, hdm⟩
            dsimp only [Blocks.get_here]
            have hdm_prf : (Eq (prfBytes.At prf_ptr) ⋆
                (WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx)
                  dptrs dtable PoolUsed ⋆ R)) dm := sep_cast hdm (by ac_rfl)
            refine readLeb128_spec hprf_fit hdidx_hi rfl rfl hdm_prf
              (fun hleb_none => by fail_leaf)
              fun u bs_d hleb_u hu_lt _ hbsd_drop hdidx2_gt => ?_
            rw [eq_comm] at hbsd_drop
            let didx2 := prfBytes.length - bs_d.length
            have hdidx2_le : didx2 ≤ prfBytes.length := Nat.sub_le _ _
            wp_unfold
            refine bv_eq_zero_branch (by omega : u < 2 ^ 64)
              (fun hu0 => by
                subst hu0
                obtain ⟨hok_dcur, hdm_cur⟩ :=
                  workState_store_cur (cur' := prf_ptr + BitVec.ofNat 64 didx2) hdm
                refine ⟨hok_dcur, ?_⟩
                have hdel_done :
                    delLoopAux (bs1.length + 1) c.cap table bs1 = some (dtable, bs_d) := by
                  rw [hdel_eq, delLoopAux_succ_zero hleb_u]
                refine ih (prfBytes.length - didx2) () _ (by omega)
                  ⟨didx2, poolUsed, poolRem, dptrs, dtable, PoolUsed,
                    hdidx2_le, rfl, ?_, hdm_cur⟩
                rw [hpure, hdrop_idx]
                have hstep_d :
                    checkPrfAux ((tag :: bs1).length + 1) c.mv c.nc poolRem table (tag :: bs1) =
                    checkPrfAux (bs1.length + 1) c.mv c.nc poolRem dtable bs_d :=
                  checkPrfAux_succ_100_step htag_not97 htag100 (hlen_cap.symm ▸ hdel_done)
                rw [hstep_d, hbsd_drop]
                exact checkPrfAux_fuel_irrel
                  (by have : bs1.length = prfBytes.length - (idx + 1) := List.length_drop; omega)
                  (by omega))
              (fun hu_ne0 => by
                cases u with
                | zero => exact absurd rfl hu_ne0
                | succ u1 =>
                  let u := u1 + 1
                  refine bv_odd_branch (by omega : u < 2 ^ 64)
                    (fun ho => by fail_leaf)
                    (fun hdeven' => ?_)
                  let did := u / 2
                  rw [bv_shr_one (by omega : u < 2 ^ 64)]
                  refine bv_eq_zero_branch (by omega : did < 2 ^ 64)
                    (fun hdid0 => by fail_leaf)
                    (fun hdid_nz' => ?_)
                  have hdid_nz : (did == 0) = false := beq_false_of_ne hdid_nz'
                  refine ult_branch (by omega : did < 2 ^ 64) hcap_bound
                    (fun hdid_lt_cap => ?_) (fun hdid_ge_cap => by fail_leaf)
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : did < 2 ^ 64)]
                  refine workState_cb_branch hdid_lt_cap hdm (fun dlits hdget_eq => ?_)
                    (fun hdget_none => by fail_leaf)
                  have hdtr_new := tableRel_set_none (did := did) (workState_tableRel hdm)
                  obtain ⟨hok_dcb, hdm2⟩ := workState_store_cb hdid_lt_cap hdtr_new hdm
                  refine ⟨hok_dcb, ih_del (prfBytes.length - didx2) _ _ (by omega)
                    ⟨didx2, dptrs.set did 0, dtable.set did none, rfl,
                      by omega, hdidx2_le, rfl, ?_, hdm2⟩⟩
                  rw [hdel_eq]
                  have hstep_del :
                      delLoopAux ((prfBytes.drop didx).length + 1) c.cap dtable
                        (prfBytes.drop didx) =
                      delLoopAux (prfBytes.drop didx).length c.cap (dtable.set did none) bs_d :=
                    delLoopAux_succ_step hleb_u hdeven' hdid_nz hdid_lt_cap hdget_eq
                  rw [hstep_del, hbsd_drop]
                  exact delLoopAux_fuel_irrel
                    (by have : bs_d.length = prfBytes.length - didx2 := by
                          rw [← hbsd_drop, List.length_drop]
                        have : (prfBytes.drop didx).length = prfBytes.length - didx :=
                          List.length_drop
                        omega)
                    (by omega))
          · intro Jdel hJdel
            wp_unfold
            exact hJdel (prfBytes.length - (idx + 1)) _ _
              ⟨idx + 1, ptrs, table, rfl, Nat.le_refl _, hidx_lt, rfl, rfl, hm⟩)
  · intro Jrec hJrec
    wp_unfold
    refine hJrec prfBytes.length () _
      ⟨0, poolUsed0, poolRem0, ptrs0, table0, PoolUsed0, Nat.zero_le _, by simp, rfl, ?_⟩
    simpa using hm0

/-! ## 4. Verification of `lratCheckBytes` against `lratCheckBytesExactSpec` -/

private theorem replicate_zero_set {xs : List (BitVec 64)} {i : Nat} (hi : i < xs.length) :
    (List.replicate i 0 ++ xs.drop i).set i 0 =
      List.replicate (i + 1) 0 ++ xs.drop (i + 1) := by
  apply List.ext_getElem
  · simp; omega
  · grind

private theorem tableRel_init (mv cap : Nat) :
    TableRel mv cap (List.replicate cap 0) (List.replicate cap none) emp :=
  ⟨by simp, by simp, fun _ _ => by simp⟩

private theorem split_workspace (c : WorkCfg) (work_len : Nat)
    (hlen : c.activeBytes ≤ work_len)
    (hwfit : c.hdr.toNat + work_len < 2 ^ 64)
    {R_rest : Mem 64 → Prop} {hdrInit : List (BitVec 64)} {m : Mem 64}
    (hm : (word8Array c.hdr hdrInit ⋆ region (c.hdr + 80) (work_len - 80) ⋆ R_rest) m) :
    ∃ (vs0 cs0 : List (BitVec 64)),
      vs0.length = c.mv + 1 ∧
      cs0.length = c.cap ∧
      (byte1Array c.vb vs0 ⋆
        word8Array c.cb cs0 ⋆
        word8Array c.hdr hdrInit ⋆
        (region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
          region c.tb c.tRaw ⋆
          region c.tlim (c.tBytes - c.tRaw) ⋆
          region c.pbase (4 * c.poolInts)) ⋆
        region (c.hdr + BitVec.ofNat 64 c.activeBytes) (work_len - c.activeBytes) ⋆ R_rest) m := by
  have hfit := c.fit_active; have hmv := c.hmv
  unfold dimacsBound at hmv; unfold WorkCfg.activeBytes at hfit
  have hact_le : 80 ≤ c.activeBytes := by unfold WorkCfg.activeBytes; omega
  have hvb_le : c.mv + 1 ≤ c.vBytes := by unfold WorkCfg.vBytes; omega
  have htb_le : c.tRaw ≤ c.tBytes := by unfold WorkCfg.tBytes WorkCfg.tRaw; omega
  have hact_fit : c.activeBytes ≤ 2 ^ 64 := by unfold WorkCfg.activeBytes at hlen ⊢; omega
  have hv_fit : c.vBytes ≤ 2 ^ 64 := by omega
  have ht_fit : c.tBytes ≤ 2 ^ 64 := by omega
  have hcb_fit : 8 * c.cap + 4 * c.poolInts ≤ 2 ^ 64 := by omega
  have htc_fit : c.tBytes + (8 * c.cap + 4 * c.poolInts) ≤ 2 ^ 64 := by omega
  have hptr : c.vb + BitVec.ofNat 64 (c.activeBytes - 80) =
      c.hdr + BitVec.ofNat 64 c.activeBytes := by
    apply BitVec.eq_of_toNat_eq
    unfold WorkCfg.vb WorkCfg.activeBytes WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *
    simp [BitVec.toNat_add]; omega
  rw [show c.hdr + (80 : BitVec 64) = c.vb from rfl,
    ← region_merge_eq (a := c.vb) (n1 := c.activeBytes - 80) (n2 := work_len - c.activeBytes)
      (n := work_len - 80) (by omega) (by omega), hptr,
    ← region_merge_eq (a := c.vb) (n1 := c.vBytes) (n2 := c.tBytes + (8 * c.cap + 4 * c.poolInts))
      (n := c.activeBytes - 80) (by unfold WorkCfg.activeBytes; omega) (by omega),
    ← region_merge_eq (a := c.vb) (n1 := c.mv + 1) (n2 := c.vBytes - (c.mv + 1))
      (n := c.vBytes) (by omega) hv_fit,
    show c.vb + BitVec.ofNat 64 c.vBytes = c.tb from rfl,
    ← region_merge_eq (a := c.tb) (n1 := c.tBytes) (n2 := 8 * c.cap + 4 * c.poolInts)
      (n := c.tBytes + (8 * c.cap + 4 * c.poolInts)) rfl htc_fit,
    ← region_merge_eq (a := c.tb) (n1 := c.tRaw) (n2 := c.tBytes - c.tRaw)
      (n := c.tBytes) (by omega) ht_fit,
    show c.tb + BitVec.ofNat 64 c.tRaw = c.tlim from rfl,
    show c.tb + BitVec.ofNat 64 c.tBytes = c.cb from rfl,
    ← region_merge_eq (a := c.cb) (n1 := 8 * c.cap) (n2 := 4 * c.poolInts)
      (n := 8 * c.cap + 4 * c.poolInts) rfl hcb_fit,
    show c.cb + BitVec.ofNat 64 (8 * c.cap) = c.pbase from rfl] at hm
  have hm_ord : (region c.vb (c.mv + 1) ⋆ region c.cb (8 * c.cap) ⋆
      (word8Array c.hdr hdrInit ⋆
        (region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
          region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw) ⋆
          region c.pbase (4 * c.poolInts)) ⋆
        region (c.hdr + BitVec.ofNat 64 c.activeBytes) (work_len - c.activeBytes) ⋆ R_rest)) m :=
    sep_ac hm
  obtain ⟨f_vc, f_rem, hu1, hd1, ⟨f_v, f_c, hu2, hd2, hrv, hrc⟩, hrem⟩ := hm_ord
  obtain ⟨vs0, hvs0, hbv⟩ := region_to_byte1Array (c.mv + 1) (by omega) hrv
  obtain ⟨cs0, hcs0, hbc⟩ := region_to_word8Array c.cap (by omega) hrc
  exact ⟨vs0, cs0, hvs0, hcs0, sep_ac (show (byte1Array c.vb vs0 ⋆ word8Array c.cb cs0 ⋆ _) m from
    ⟨f_vc, f_rem, hu1, hd1, ⟨f_v, f_c, hu2, hd2, hbv, hbc⟩, hrem⟩)⟩

private theorem merge_workspace_tail (c : WorkCfg) (work_len : Nat)
    (hlen : c.activeBytes ≤ work_len)
    (hwfit : c.hdr.toNat + work_len < 2 ^ 64) :
    (region c.hdr c.activeBytes ⋆
      region (c.hdr + BitVec.ofNat 64 c.activeBytes) (work_len - c.activeBytes)) =
    region c.hdr work_len :=
  region_merge_eq (by omega) (by omega)

private theorem runLratCheckBytes_of_header {cnfBytes prfBytes bodyRest : List UInt8}
    {work_len mv nc : Nat}
    (h128 : ¬ (work_len < 128))
    (hhdr : parseHeader cnfBytes = some (mv, nc, bodyRest)) :
    runLratCheckBytes cnfBytes prfBytes work_len =
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
            checkPrfPure mv nc pool_ints' (initClauseTable cap clauses) prfBytes := by
  rw [runLratCheckBytes_def]; simp only [h128, ↓reduceIte]; rw [hhdr]

/-- Verification of `lratCheckBytes` against `lratCheckBytesExactSpec`, parameterized by `Γ`
providing `lbParseDimacsHeaderSpec`, `lbParseDimacsBodySpec`, and `lbCheckPrfSpec`. -/
theorem lratCheckBytes_exact_of (Γ : Env)
    (hParseHeader : ∀ args m Q X,
      lbParseDimacsHeaderSpec args m Q X →
      Γ "lb_parse_dimacs_header" [i64, i64, i64] [i64] args m Q X)
    (hParseBody : ∀ args m Q X,
      lbParseDimacsBodySpec args m Q X →
      Γ "lb_parse_dimacs_body" [i64, i64] [i64] args m Q X)
    (hCheckPrf : ∀ args m Q X,
      lbCheckPrfSpec args m Q X →
      Γ "lb_check_prf" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, lratCheckBytesExactSpec args m Q X → Func.spec Γ lratCheckBytes args m Q X := by
  rintro _ m0 Q X ⟨cnf_ptr, prf_ptr, work_ptr, cnfBytes, prfBytes, work_len, R_mem,
    rfl, hcnf_fit, hprf_fit, hwork_fit, hm0, hQ⟩
  unfold lratCheckBytes Func.spec Func.wp
  wp_unfold
  refine ult_branch (a := work_len) (b := 128) (by omega) (by decide)
    (fun hlt128 => hQ 0 m0 (by simp [runLratCheckBytes_lt128 hlt128]) hm0)
    (fun hnot_lt128 => by
      have hsplit80 : region work_ptr work_len =
          (region work_ptr 80 ⋆ region (work_ptr + 80) (work_len - 80)) := by
        have : work_len = 80 + (work_len - 80) := by omega
        conv => lhs; rw [this, region_split (by omega)]
        rfl
      let R80 := region (work_ptr + 80) (work_len - 80) ⋆ Eq (prfBytes.At prf_ptr) ⋆ R_mem
      have hm0_hdr : (Eq (cnfBytes.At cnf_ptr) ⋆ region work_ptr 80 ⋆ R80) m0 := by
        have hm_tmp := hm0; rw [hsplit80] at hm_tmp
        exact sep_cast hm_tmp (by dsimp [R80]; ac_rfl)
      refine wp_call_ret1 _ _ _
        (hParseHeader _ _ _ _ ⟨cnf_ptr, work_ptr, cnfBytes, R80, rfl, hcnf_fit, by omega, hm0_hdr,
          fun r m1 hr => hr⟩) ?_
      rintro hok m1 hhdr_res
      wp_unfold
      cases hhdr_eq : parseHeader cnfBytes with
      | none =>
        rw [hhdr_eq] at hhdr_res
        obtain ⟨rfl, hm1_reg⟩ := hhdr_res
        refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
        have hm1_full : ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
            region work_ptr work_len) ⋆ R_mem) m1 := by
          have h1 : (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
              (region work_ptr 80 ⋆ region (work_ptr + 80) (work_len - 80)) ⋆ R_mem) m1 :=
            sep_cast hm1_reg (by dsimp [R80]; ac_rfl)
          rw [← hsplit80] at h1
          exact sep_cast h1 (by ac_rfl)
        exact hQ 0 m1 (by simp [runLratCheckBytes_hdr_none hnot_lt128 hhdr_eq]) hm1_full
      | some val_hdr =>
        rcases val_hdr with ⟨mv, nc, bodyRest⟩
        rw [hhdr_eq] at hhdr_res
        obtain ⟨rfl, hmv, hnc, hbody_drop, hbody_le, w2, w3, w4, w5, w6, w7, w8, hm1⟩ := hhdr_res
        refine ⟨fun _ => ?_, fun h0 => absurd h0 (by decide)⟩
        let idx0 := cnfBytes.length - bodyRest.length
        let cur0 := cnf_ptr + BitVec.ofNat 64 idx0
        let hdrInit : List (BitVec 64) :=
          [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc, w2, w3, w4, w5, w6, w7, w8, cur0]
        have hm1_focus : (word8Array work_ptr hdrInit ⋆ (Eq (cnfBytes.At cnf_ptr) ⋆ R80)) m1 :=
          sep_cast hm1 (by dsimp [hdrInit, cur0, idx0]; ac_rfl)
        have hld_mv : loadVal m1 i64 work_ptr = some (BitVec.ofNat 64 mv) := by
          rw [show work_ptr = work_ptr + BitVec.ofNat 64 (8 * 0) by simp]
          exact load_word8Array (i := 0) (by simp [hdrInit]) hm1_focus
        have hld_nc : loadVal m1 i64 (work_ptr + 8) = some (BitVec.ofNat 64 nc) :=
          load_word8Array (i := 1) (by simp [hdrInit]) hm1_focus
        refine ⟨_, hld_mv, _, hld_nc, ?_⟩
        have hcollapse_init : ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
            region work_ptr work_len) ⋆ R_mem) m1 := by
          have hr80 : ∀ f, word8Array work_ptr hdrInit f → region work_ptr 80 f := fun f hf => by
            simpa [hdrInit] using word8Array_to_region (by simp [hdrInit]) hf
          have h2 : (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
              (region work_ptr 80 ⋆ region (work_ptr + 80) (work_len - 80)) ⋆ R_mem) m1 :=
            sep_cast (sep_mono hr80 hm1_focus) (by dsimp [R80]; ac_rfl)
          rw [← hsplit80] at h2
          exact sep_cast h2 (by ac_rfl)
        have hmv_lt : mv < 2 ^ 28 := hmv
        have hnc_lt : nc < 2 ^ 28 := hnc
        let v_bytes := ((mv + 8) / 8) * 8
        let t_raw := 4 * (mv + 1)
        let t_bytes := ((t_raw + 7) / 8) * 8
        let fixed := 80 + v_bytes + t_bytes
        have hbv_traw : (BitVec.ofNat 64 (mv + 1)) <<< (2 : Nat) = BitVec.ofNat 64 t_raw := by
          rw [bv_shl_ofNat (by omega) (by decide),
            show (mv + 1) <<< 2 = t_raw by simp [t_raw, Nat.shiftLeft_eq]; omega]
        rw [show BitVec.ofNat 64 mv + (1 : BitVec 64) = BitVec.ofNat 64 (mv + 1) from
            bv_add_ofNat mv 1,
          show BitVec.ofNat 64 mv + (8 : BitVec 64) = BitVec.ofNat 64 (mv + 8) from
            bv_add_ofNat mv 8,
          show (-8 : BitVec 64) = -(BitVec.ofNat 64 (2 ^ 3)) from rfl,
          bv_align_pow2 (by decide) (by omega),
          hbv_traw,
          show BitVec.ofNat 64 t_raw + (7 : BitVec 64) = BitVec.ofNat 64 (t_raw + 7) from
            bv_add_ofNat t_raw 7,
          bv_align_pow2 (by decide) (by dsimp [t_raw]; omega),
          bv_add_ofNat v_bytes t_bytes,
          show (80 : BitVec 64) + BitVec.ofNat 64 (v_bytes + t_bytes) =
              BitVec.ofNat 64 fixed from by
            rw [show (80 : BitVec 64) = BitVec.ofNat 64 80 from rfl, bv_add_ofNat]
            congr 1; omega]
        refine ult_branch (by omega : work_len < 2 ^ 64)
          (by dsimp [fixed, v_bytes, t_bytes, t_raw]; omega : fixed < 2 ^ 64)
          (fun hlt_fixed => by
            refine hQ 0 m1 ?_ hcollapse_init
            rw [runLratCheckBytes_of_header hnot_lt128 hhdr_eq]
            dsimp only [fixed, v_bytes, t_bytes, t_raw] at hlt_fixed
            simp only [hlt_fixed, ↓reduceIte]; rfl)
          (fun hnot_lt_fixed => by
            let rem := work_len - fixed
            let c_half := rem / 16
            let p_cap := prfBytes.length % 268435456
            let want := nc + p_cap + 32
            let cap := if c_half < want then c_half else want
            have hbv_chalf : (BitVec.ofNat 64 rem) >>> (4 : Nat) = BitVec.ofNat 64 c_half := by
              rw [bv_shr_ofNat (by omega) (by decide), Nat.shiftRight_eq_div_pow]
            rw [bv_sub_ofNat (by omega) (by omega), hbv_chalf,
              show (268435455 : BitVec 64) = BitVec.ofNat 64 (2 ^ 28 - 1) from rfl,
              bv_and_pow2_sub_one (k := 28) (by omega),
              bv_add_ofNat nc p_cap,
              show BitVec.ofNat 64 (nc + p_cap) + (32 : BitVec 64) = BitVec.ofNat 64 want from
                bv_add_ofNat (nc + p_cap) 32]
            refine wp_join_group (fun (cap_v, ()) m' => cap_v = BitVec.ofNat 64 cap ∧ m' = m1) ?_ ?_
            · rintro _ ⟨cap_v, ⟨⟩⟩ m_cap ⟨rfl, hm_cap_eq⟩
              subst m_cap
              dsimp only [Blocks.get_here]; wp_unfold
              have hcap_le_chalf : cap ≤ c_half := by dsimp [cap]; split <;> omega
              have hcap_lt64 : cap < 2 ^ 64 := by dsimp [c_half, rem] at hcap_le_chalf; omega
              refine ule_branch hcap_lt64 (by omega : nc < 2 ^ 64)
                (fun hcap_le_nc => by
                  refine hQ 0 m1 ?_ hcollapse_init
                  rw [runLratCheckBytes_of_header hnot_lt128 hhdr_eq]
                  dsimp only [cap, c_half, want, p_cap, rem, fixed, v_bytes, t_bytes,
                    t_raw] at hnot_lt_fixed hcap_le_nc
                  simp only [hnot_lt_fixed, hcap_le_nc, ↓reduceIte]; rfl)
                (fun hnot_cap_le_nc => by
                  have hnc_cap : nc < cap := by omega
                  let cb_bytes := 8 * cap
                  let pool_rem := rem - cb_bytes
                  let pool_ints := pool_rem / 4
                  have hcb_le_rem : cb_bytes ≤ rem := by dsimp [cb_bytes, c_half] at *; omega
                  have hact_le : 80 + v_bytes + t_bytes + 8 * cap + 4 * pool_ints ≤ work_len := by
                    dsimp [pool_ints, pool_rem, cb_bytes, rem]; omega
                  let c : WorkCfg := {
                    hdr := work_ptr, mv := mv, nc := nc, cap := cap, poolInts := pool_ints,
                    hmv := hmv, hnc := hnc, hnc_cap := hnc_cap,
                    hfit := by dsimp [v_bytes, t_bytes, t_raw] at hact_le; omega
                  }
                  have hc_act_le : c.activeBytes ≤ work_len := hact_le
                  have hbv_pool_bytes : BitVec.ofNat 64 pool_rem &&& (-4 : BitVec 64) =
                      BitVec.ofNat 64 (4 * pool_ints) := by
                    rw [show (-4 : BitVec 64) = -(BitVec.ofNat 64 (2 ^ 2)) from rfl,
                      bv_align_pow2 (by decide) (by omega)]
                    congr 1; dsimp [pool_ints]; omega
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt64,
                    bv_sub_ofNat hcb_le_rem (by omega), hbv_pool_bytes]
                  have hm1_ws_in : (word8Array c.hdr hdrInit ⋆
                      region (c.hdr + 80) (work_len - 80) ⋆
                      (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ R_mem)) m1 :=
                    sep_cast hm1 (by dsimp [c, R80, hdrInit, cur0, idx0]; ac_rfl)
                  obtain ⟨vs0, cs0, hvs0, hcs0, hm1_split⟩ :=
                    split_workspace c work_len hc_act_le hwork_fit hm1_ws_in
                  let WMid :=
                    region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
                    region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw) ⋆
                    region c.pbase (4 * c.poolInts)
                  let RTail :=
                    region (c.hdr + BitVec.ofNat 64 c.activeBytes) (work_len - c.activeBytes)
                  let RRest := Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ R_mem
                  -- `@zv_done()`
                  refine wp_join_group (fun () m_zv =>
                    (word8Array c.cb cs0 ⋆ byte1Array c.vb (List.replicate (c.mv + 1) 0) ⋆
                      word8Array c.hdr hdrInit ⋆ WMid ⋆ RTail ⋆ RRest) m_zv) ?_ ?_
                  · rintro _ ⟨⟩ m_zv hm_zv
                    dsimp only [Blocks.get_here]
                    -- `@zcb_done()`
                    refine wp_join_group (fun () m_zcb =>
                      (word8Array c.hdr hdrInit ⋆
                        byte1Array c.vb (List.replicate (c.mv + 1) 0) ⋆
                        word8Array c.cb (List.replicate c.cap 0) ⋆
                        WMid ⋆ RTail ⋆ RRest) m_zcb) ?_ ?_
                    · rintro _ ⟨⟩ m_zcb hm_zcb
                      dsimp only [Blocks.get_here]; wp_unfold
                      let TailZ := byte1Array c.vb (List.replicate (c.mv + 1) 0) ⋆
                        word8Array c.cb (List.replicate c.cap 0) ⋆ WMid ⋆ RTail ⋆ RRest
                      have hm_s0 : (word8Array c.hdr hdrInit ⋆ TailZ) m_zcb :=
                        sep_cast hm_zcb (by dsimp [TailZ]; ac_rfl)
                      have hp16 :
                          work_ptr + (16 : BitVec 64) = c.hdr + BitVec.ofNat 64 (8 * 2) := rfl
                      have hp24 :
                          work_ptr + (24 : BitVec 64) = c.hdr + BitVec.ofNat 64 (8 * 3) := rfl
                      have hp32 :
                          work_ptr + (32 : BitVec 64) = c.hdr + BitVec.ofNat 64 (8 * 4) := rfl
                      have hp40 :
                          work_ptr + (40 : BitVec 64) = c.hdr + BitVec.ofNat 64 (8 * 5) := rfl
                      have hp48 :
                          work_ptr + (48 : BitVec 64) = c.hdr + BitVec.ofNat 64 (8 * 6) := rfl
                      have hp56 :
                          work_ptr + (56 : BitVec 64) = c.hdr + BitVec.ofNat 64 (8 * 7) := rfl
                      have hp64 :
                          work_ptr + (64 : BitVec 64) = c.hdr + BitVec.ofNat 64 (8 * 8) := rfl
                      rw [hp16, hp24, hp32, hp40, hp48, hp56, hp64]
                      obtain ⟨hok2, hm_s2⟩ :=
                        store_word8Array (i := 2) (BitVec.ofNat 64 c.cap) (by simp [hdrInit]) hm_s0
                      obtain ⟨hok3, hm_s3⟩ :=
                        store_word8Array (i := 3) c.vb (by simp [hdrInit]) hm_s2
                      obtain ⟨hok4, hm_s4⟩ :=
                        store_word8Array (i := 4) c.tb (by simp [hdrInit]) hm_s3
                      obtain ⟨hok5, hm_s5⟩ :=
                        store_word8Array (i := 5) c.tlim (by simp [hdrInit]) hm_s4
                      obtain ⟨hok6, hm_s6⟩ :=
                        store_word8Array (i := 6) c.cb (by simp [hdrInit]) hm_s5
                      obtain ⟨hok7, hm_s7⟩ :=
                        store_word8Array (i := 7) c.plim (by simp [hdrInit]) hm_s6
                      obtain ⟨hok8, hm_s8⟩ :=
                        store_word8Array (i := 8) c.pbase (by simp [hdrInit]) hm_s7
                      refine ⟨hok2, hok3, hok4, hok5, hok6, hok7, hok8, ?_⟩
                      let m_hdr := storeMem (storeMem (storeMem (storeMem (storeMem (storeMem
                        (storeMem m_zcb i64
                          (c.hdr + BitVec.ofNat 64 (8 * 2)) (BitVec.ofNat 64 c.cap))
                        i64 (c.hdr + BitVec.ofNat 64 (8 * 3)) c.vb)
                        i64 (c.hdr + BitVec.ofNat 64 (8 * 4)) c.tb)
                        i64 (c.hdr + BitVec.ofNat 64 (8 * 5)) c.tlim)
                        i64 (c.hdr + BitVec.ofNat 64 (8 * 6)) c.cb)
                        i64 (c.hdr + BitVec.ofNat 64 (8 * 7)) c.plim)
                        i64 (c.hdr + BitVec.ofNat 64 (8 * 8)) c.pbase
                      have hhdr_eq_words :
                          (((((((hdrInit.set 2 (BitVec.ofNat 64 c.cap)).set 3 c.vb).set
                          4 c.tb).set 5 c.tlim).set 6 c.cb).set 7 c.plim).set 8 c.pbase) =
                          c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * 0)) cur0 := by
                        dsimp only [c, hdrInit, WorkCfg.hdrWords]
                        simp only [List.set_cons_zero, List.set_cons_succ, Nat.mul_zero]
                        rw [BitVec.add_zero]
                      rw [hhdr_eq_words] at hm_s8
                      let RBody := RTail ⋆ Eq (prfBytes.At prf_ptr) ⋆ R_mem
                      have hm_ws0 : (Eq (cnfBytes.At cnf_ptr) ⋆
                          WorkState c 0 c.poolInts cur0
                            (List.replicate c.cap 0) (List.replicate c.cap none) emp ⋆
                          RBody) m_hdr := by
                        have hm_tmp : (word8Array c.hdr
                            (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * 0)) cur0) ⋆
                            TailZ) m_hdr := hm_s8
                        dsimp only [TailZ, WMid, RRest] at hm_tmp
                        rw [← assignBytes_empty c.mv,
                          ← sep_emp (region c.pbase (4 * c.poolInts))] at hm_tmp
                        conv at hm_tmp =>
                          pattern (region c.pbase (4 * c.poolInts))
                          rw [show c.pbase = c.pbase + BitVec.ofNat 64 (4 * 0) from
                            (BitVec.add_zero c.pbase).symm]
                        have hm_ws0' : (WorkState c 0 c.poolInts cur0
                            (List.replicate c.cap 0) (List.replicate c.cap none) emp ⋆
                            (Eq (cnfBytes.At cnf_ptr) ⋆ RBody)) m_hdr :=
                          workState_sep.mpr ⟨Nat.zero_add _, tableRel_init c.mv c.cap,
                            fun f hf => by simpa [region_zero] using hf,
                            sep_cast hm_tmp (by dsimp [RBody]; ac_rfl)⟩
                        exact sep_cast hm_ws0' (by ac_rfl)
                      refine wp_call_ret1 _ _ _
                        (hParseBody _ _ _ _ ⟨c, cnf_ptr, cnfBytes, idx0, RBody,
                          rfl, hcnf_fit, by dsimp [idx0]; omega, hm_ws0,
                          fun r m_b hr => hr⟩) ?_
                      rintro bok m_b hbody_res
                      wp_unfold
                      cases hbody_eq :
                          parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) with
                      | none =>
                        rw [hbody_eq] at hbody_res
                        obtain ⟨rfl, hm_b_reg⟩ := hbody_res
                        refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
                        have hm_b_full : ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
                            region work_ptr work_len) ⋆ R_mem) m_b := by
                          have h1 : (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
                              (region c.hdr c.activeBytes ⋆ RTail) ⋆ R_mem) m_b := by
                            dsimp only [RBody] at hm_b_reg; exact sep_ac hm_b_reg
                          dsimp only [RTail] at h1
                          rw [merge_workspace_tail c work_len hc_act_le hwork_fit] at h1
                          exact h1
                        have hbody_eq' : parseBodyPure mv nc pool_ints [] bodyRest = none := by
                          dsimp only [c, idx0] at hbody_eq
                          rwa [← hbody_drop] at hbody_eq
                        refine hQ 0 m_b ?_ hm_b_full
                        rw [runLratCheckBytes_of_header hnot_lt128 hhdr_eq]
                        dsimp only [pool_ints, pool_rem, cb_bytes, cap, c_half, want, p_cap, rem,
                          fixed, v_bytes, t_bytes, t_raw] at hnot_lt_fixed hnot_cap_le_nc hbody_eq'
                        simp only [hnot_lt_fixed, hnot_cap_le_nc, hbody_eq', ↓reduceIte]; rfl
                      | some val_body =>
                        rcases val_body with ⟨clauses, poolRem'⟩
                        rw [hbody_eq] at hbody_res
                        obtain ⟨rfl, _, _, ptrs, PoolUsed, hm_b⟩ := hbody_res
                        refine ⟨fun _ => ?_, fun h0 => absurd h0 (by decide)⟩
                        obtain ⟨hok72, hm_b2⟩ := workState_store_cur (cur' := prf_ptr) hm_b
                        refine ⟨hok72, ?_⟩
                        let RPrf := RTail ⋆ Eq (cnfBytes.At cnf_ptr) ⋆ R_mem
                        have hm_prf_ws : (Eq (prfBytes.At prf_ptr) ⋆
                            WorkState c (c.poolInts - poolRem') poolRem' prf_ptr
                              ptrs (initClauseTable c.cap clauses) PoolUsed ⋆ RPrf)
                            (storeMem m_b i64 (c.hdr + 72) prf_ptr) :=
                          sep_cast hm_b2 (by dsimp [RBody, RPrf]; ac_rfl)
                        refine wp_call_ret1 _ _
                          (fun r m_fin =>
                            r = (if checkPrfPure c.mv c.nc poolRem'
                                  (initClauseTable c.cap clauses) prfBytes = true
                              then 1 else 0) ∧
                            (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ RPrf) m_fin)
                          (hCheckPrf _ _ _ _ ⟨c, prf_ptr, prfBytes, c.poolInts - poolRem', poolRem',
                            ptrs, initClauseTable c.cap clauses, PoolUsed, RPrf,
                            rfl, hprf_fit, hm_prf_ws,
                            fun r m_fin hr hm_fin => ⟨hr, hm_fin⟩⟩) ?_
                        rintro pok m_fin ⟨hpok, hm_fin⟩
                        wp_unfold
                        have hm_fin_full : ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
                            region work_ptr work_len) ⋆ R_mem) m_fin := by
                          have h1 : (Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
                              (region c.hdr c.activeBytes ⋆ RTail) ⋆ R_mem) m_fin := by
                            dsimp only [RPrf] at hm_fin; exact sep_ac hm_fin
                          dsimp only [RTail] at h1
                          rw [merge_workspace_tail c work_len hc_act_le hwork_fit] at h1
                          exact h1
                        have hbody_eq' : parseBodyPure mv nc pool_ints [] bodyRest =
                            some (clauses, poolRem') := by
                          dsimp only [c, idx0] at hbody_eq
                          rwa [← hbody_drop] at hbody_eq
                        refine hQ pok m_fin ?_ hm_fin_full
                        rw [hpok, runLratCheckBytes_of_header hnot_lt128 hhdr_eq]
                        dsimp only [c, pool_ints, pool_rem, cb_bytes, cap, c_half, want, p_cap,
                          rem, fixed, v_bytes, t_bytes, t_raw] at hnot_lt_fixed hnot_cap_le_nc
                        dsimp only [c, pool_ints, pool_rem, cb_bytes, cap, c_half, want, p_cap,
                          rem, fixed, v_bytes, t_bytes, t_raw] at hbody_eq' ⊢
                        simp only [hnot_lt_fixed, hnot_cap_le_nc, hbody_eq', ↓reduceIte]
                    · -- `@zcb(%j)` loop
                      intro Jzcb_done hJzcb_done
                      let RestZcb := byte1Array c.vb (List.replicate (c.mv + 1) 0) ⋆
                        word8Array c.hdr hdrInit ⋆ WMid ⋆ RTail ⋆ RRest
                      refine wp_loop_group (fun r (j_v, ()) m => ∃ j,
                        j_v = BitVec.ofNat 64 j ∧ j ≤ c.cap ∧ r = c.cap - j ∧
                        (word8Array c.cb (List.replicate j 0 ++ cs0.drop j) ⋆ RestZcb) m) ?_ ?_
                      · rintro Jzcb r ⟨j_v, ⟨⟩⟩ m ih_zcb ⟨j, rfl, hj_le, rfl, hm_j⟩
                        dsimp only [Blocks.get_here]; wp_unfold
                        have hc_cap : c.cap = cap := rfl
                        refine ult_branch (by rw [hc_cap] at hj_le; omega : j < 2 ^ 64) hcap_lt64
                          (fun hj_lt => by
                            rw [BitVec.toNat_ofNat,
                              Nat.mod_eq_of_lt (by rw [hc_cap] at hj_le; omega : j < 2 ^ 64)]
                            obtain ⟨hok_j, hm_j'⟩ := store_word8Array (i := j) 0
                              (by simp [hcs0]; dsimp [c]; omega) hm_j
                            rw [replicate_zero_set (hcs0 ▸ (by dsimp [c]; exact hj_lt))] at hm_j'
                            rw [show work_ptr + (80 : BitVec 64) +
                                  BitVec.ofNat 64 ((mv + 8) / 2 ^ 3 * 2 ^ 3) +
                                  BitVec.ofNat 64 ((t_raw + 7) / 2 ^ 3 * 2 ^ 3) = c.cb from rfl,
                              show BitVec.ofNat 64 j + (1 : BitVec 64) =
                                  BitVec.ofNat 64 (j + 1) from bv_add_ofNat j 1]
                            exact ⟨hok_j, ih_zcb (c.cap - (j + 1)) _ _ (by dsimp [c]; omega)
                              ⟨j + 1, rfl, by dsimp [c]; omega, rfl, hm_j'⟩⟩)
                          (fun hj_ge => by
                            obtain rfl : j = c.cap := by dsimp only [c] at hj_le ⊢; omega
                            rw [List.drop_of_length_le (by omega), List.append_nil] at hm_j
                            exact hJzcb_done () _ (sep_cast hm_j (by dsimp [RestZcb]; ac_rfl)))
                      · intro Jzcb hJzcb
                        wp_unfold
                        exact hJzcb c.cap _ _ ⟨0, rfl, Nat.zero_le _, by simp,
                          sep_cast (by simpa using hm_zv) (by dsimp [RestZcb]; ac_rfl)⟩
                  · -- `@zv(%i)` loop
                    intro Jzv_done hJzv_done
                    let RestZv := word8Array c.cb cs0 ⋆ word8Array c.hdr hdrInit ⋆
                      WMid ⋆ RTail ⋆ RRest
                    refine wp_loop_group (fun r (i_v, ()) m => ∃ i,
                      i_v = BitVec.ofNat 64 i ∧ i ≤ c.mv + 1 ∧ r = (c.mv + 1) - i ∧
                      (byte1Array c.vb (List.replicate i 0 ++ vs0.drop i) ⋆ RestZv) m) ?_ ?_
                    · rintro Jzv r ⟨i_v, ⟨⟩⟩ m ih_zv ⟨i, rfl, hi_le, rfl, hm_i⟩
                      dsimp only [Blocks.get_here]; wp_unfold
                      have hc_mv : c.mv = mv := rfl
                      refine ule_branch (by rw [hc_mv] at hi_le; omega : i < 2 ^ 64)
                        (by omega : mv < 2 ^ 64)
                        (fun hi_le_mv => by
                          obtain ⟨hok_i, hm_i'⟩ := store_byte1Array (i := i) 0#8
                            (by simp [hvs0, hc_mv]; omega) hm_i
                          rw [show (0#8).setWidth 64 = (0 : BitVec 64) from rfl,
                            replicate_zero_set
                              (hvs0 ▸ (by rw [hc_mv]; omega : i < c.mv + 1))] at hm_i'
                          rw [show work_ptr + (80 : BitVec 64) = c.vb from rfl,
                            show BitVec.ofNat 64 i + (1 : BitVec 64) =
                                BitVec.ofNat 64 (i + 1) from bv_add_ofNat i 1]
                          exact ⟨hok_i, ih_zv ((c.mv + 1) - (i + 1)) _ _ (by dsimp [c]; omega)
                            ⟨i + 1, rfl, by dsimp [c]; omega, rfl, hm_i'⟩⟩)
                        (fun hi_gt => by
                          obtain rfl : i = c.mv + 1 := by dsimp only [c] at hi_le ⊢; omega
                          rw [List.drop_of_length_le (by omega), List.append_nil] at hm_i
                          exact hJzv_done () _ (sep_cast hm_i (by dsimp [RestZv]; ac_rfl)))
                    · intro Jzv hJzv
                      wp_unfold
                      have hm1_split' : (byte1Array c.vb (List.replicate 0 0 ++ vs0.drop 0) ⋆
                          word8Array c.cb cs0 ⋆ word8Array c.hdr hdrInit ⋆ WMid ⋆
                          RTail ⋆ RRest) m1 := by
                        dsimp only [WMid, RTail, RRest] at hm1_split ⊢
                        rw [List.replicate_zero, List.nil_append, List.drop_zero]
                        exact hm1_split
                      exact hJzv (c.mv + 1) _ _ ⟨0, rfl, Nat.zero_le _, by simp,
                        sep_cast hm1_split' (by dsimp [RestZv]; ac_rfl)⟩)
            · intro Jgot_cap hJgot_cap
              wp_unfold
              refine ult_branch (by dsimp [c_half, rem]; omega : c_half < 2 ^ 64)
                (by dsimp [want, p_cap]; omega : want < 2 ^ 64)
                (fun hlt_w => hJgot_cap _ _ ⟨by simp [cap, hlt_w], rfl⟩)
                (fun hge_w => hJgot_cap _ _ ⟨by simp [cap, hge_w], rfl⟩)))

end LeanQbe.T.Examples.LratBytes
