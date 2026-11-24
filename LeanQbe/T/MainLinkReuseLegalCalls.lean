module

public import LeanQbe.T.Legal
public import LeanQbe.T.Module
import LeanQbe.T.WfLemmas

/-!
# Target Legalization `callsOk` Preservation (`MainLinkReuseLegalCalls`)

Proves that `Func.legal` preserves `Expr.callsOk`, mapping each callee signature
`(g, as, bs)` to `(g, target.legalSig as, target.legalSig bs)` while preserving `exits`:

* `legalOp_callsOk`, `legalLoad_callsOk`, `legalStore_callsOk`
* `legalExpr_callsOk`, `Func.legal_callsOk`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-- Map a pre-legal `SigEntry` through `target.legalSig`. -/
@[expose] def sigEntryLegal (target : LegalTarget) (e : SigEntry) : SigEntry :=
  (e.1, target.legalSig e.2.1, target.legalSig e.2.2)

local macro "solve_calls_cps" h:ident : tactic =>
  `(tactic| (
    try dsimp only [Expr.callsOk] at *;
    repeat' (first
      | exact trivial
      | assumption
      | exact $h _
      | exact $h _ _
      | exact $h _ _ _
      | exact $h _ _ _ _
      | exact $h _ _ _ _ _ _ _ _
      | dsimp only [Expr.callsOk]
      | split)))

section BaseCalls

variable {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}

private theorem emitSextToW_callsOk {n w : Nat} {x : Arg (fun _ => Unit) (.bits w)}
    {k : Arg (fun _ => Unit) (.bits w) → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r, (k r).callsOk allowed exits) :
    (emitSextToW n w x k).callsOk allowed exits := by
  unfold emitSextToW; solve_calls_cps hk

private theorem emitMaskToN_callsOk {n w : Nat} {x : Arg (fun _ => Unit) (.bits w)}
    {k : Arg (fun _ => Unit) (.bits w) → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r, (k r).callsOk allowed exits) :
    (emitMaskToN n w x k).callsOk allowed exits := by
  unfold emitMaskToN; solve_calls_cps hk

private theorem emitCountMod_callsOk {n w : Nat} {c : Arg (fun _ => Unit) (.bits w)}
    {k : Arg (fun _ => Unit) (.bits w) → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r, (k r).callsOk allowed exits) :
    (emitCountMod n w c k).callsOk allowed exits := by
  unfold emitCountMod; solve_calls_cps hk

private theorem emitBoolCmp_callsOk {o : CmpOp} {a b : Arg (fun _ => Unit) .bool}
    {k : Arg (fun _ => Unit) .bool → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r, (k r).callsOk allowed exits) :
    (emitBoolCmp o a b k).callsOk allowed exits := by
  unfold emitBoolCmp; solve_calls_cps hk

private theorem emitBoolSelect_callsOk {c a b : Arg (fun _ => Unit) .bool}
    {k : Arg (fun _ => Unit) .bool → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r, (k r).callsOk allowed exits) :
    (emitBoolSelect c a b k).callsOk allowed exits := by
  unfold emitBoolSelect; solve_calls_cps hk

end BaseCalls

local macro "solve_legal_cps" h:ident : tactic =>
  `(tactic| (
    try dsimp only [Expr.callsOk] at *;
    repeat' (first
      | exact trivial
      | assumption
      | exact $h _
      | exact $h _ _
      | exact $h _ _ _
      | exact $h _ _ _ _
      | exact $h _ _ _ _ _ _ _ _
      | (refine emitSextToW_callsOk fun _ => ?_)
      | (refine emitMaskToN_callsOk fun _ => ?_)
      | (refine emitCountMod_callsOk fun _ => ?_)
      | (refine emitBoolCmp_callsOk fun _ => ?_)
      | (refine emitBoolSelect_callsOk fun _ => ?_)
      | dsimp only [Expr.callsOk]
      | split)))

section BaseCallsMore

variable {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}

private theorem pushLeafWord64_callsOk {w : Nat} {leaf : Arg (fun _ => Unit) i64}
    {ws : List (Arg (fun _ => Unit) i64)} {acc : Arg (fun _ => Unit) i64} {accBits : Nat}
    {k : List (Arg (fun _ => Unit) i64) → Arg (fun _ => Unit) i64 → Nat →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ ws' acc' bits', (k ws' acc' bits').callsOk allowed exits) :
    (pushLeafWord64 w leaf ws acc accBits k).callsOk allowed exits := by
  unfold pushLeafWord64; solve_calls_cps hk

private theorem extractBitsFromWords64_callsOk
    {words : List (Arg (fun _ => Unit) i64)} {off w : Nat}
    {k : Arg (fun _ => Unit) i64 → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r, (k r).callsOk allowed exits) :
    (extractBitsFromWords64 words off w k).callsOk allowed exits := by
  unfold extractBitsFromWords64
  split
  · exact hk _
  · dsimp only
    split <;> (
      try dsimp only [Expr.callsOk]
      split
      · exact emitMaskToN_callsOk hk
      · dsimp only [Expr.callsOk]; exact emitMaskToN_callsOk hk)

private theorem emitTernlog_go_callsOk (t : Ty) (zeroVal : Val t) (imm : BitVec 8)
    (k : Arg (fun _ => Unit) t → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ r, (k r).callsOk allowed exits)
    (a b c na nb nc : Arg (fun _ => Unit) t) :
    ∀ (d idx : Nat), 8 - idx ≤ d → ∀ acc,
      (emitTernlog.go t zeroVal imm k idx acc a b c na nb nc).callsOk allowed exits
  | 0, idx, hd, acc => by
    have hge : idx ≥ 8 := by omega
    rw [emitTernlog.go.eq_def]; simp only [hge, ↓reduceIte]; split <;> exact hk _
  | d + 1, idx, hd, acc => by
    rw [emitTernlog.go.eq_def]
    by_cases hge : idx ≥ 8
    · simp only [hge, ↓reduceIte]; split <;> exact hk _
    · simp only [hge, ↓reduceIte]
      split
      · dsimp only [Expr.callsOk]
        cases acc <;> exact emitTernlog_go_callsOk t zeroVal imm k hk a b c na nb nc d (idx + 1)
          (by omega) _
      · exact emitTernlog_go_callsOk t zeroVal imm k hk a b c na nb nc d (idx + 1) (by omega) _

private theorem emitTernlog_callsOk {t : Ty} {zeroVal onesVal : Val t}
    {a b c : Arg (fun _ => Unit) t} {imm : BitVec 8}
    {k : Arg (fun _ => Unit) t → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r, (k r).callsOk allowed exits) :
    (emitTernlog t zeroVal onesVal a b c imm k).callsOk allowed exits := by
  unfold emitTernlog
  split
  · exact hk _
  · split
    · exact hk _
    · dsimp only [Expr.callsOk]
      exact emitTernlog_go_callsOk t zeroVal imm k hk a b c _ _ _ 8 0 (Nat.le_refl _) none

private theorem emitTernlogBits_callsOk {w : Nat}
    {a b c : Arg (fun _ => Unit) (.bits w)} {imm : BitVec 8}
    {k : Arg (fun _ => Unit) (.bits w) → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r, (k r).callsOk allowed exits) :
    (emitTernlogBits w a b c imm k).callsOk allowed exits :=
  emitTernlog_callsOk hk

private theorem emitTernlogBool_callsOk
    {a b c : Arg (fun _ => Unit) .bool} {imm : BitVec 8}
    {k : Arg (fun _ => Unit) .bool → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r, (k r).callsOk allowed exits) :
    (emitTernlogBool a b c imm k).callsOk allowed exits :=
  emitTernlog_callsOk hk

private theorem unpackToLeaves_callsOk (target : LegalTarget) :
    ∀ (t : Ty) (x : Arg (fun _ => Unit) t)
      (k : Tup (Arg (fun _ => Unit)) (target.leafTys t) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (unpackToLeaves target t x k).callsOk allowed exits
  | .bool, _, k, hk => hk _
  | .bits _, _, k, hk => by dsimp only [unpackToLeaves]; solve_calls_cps hk
  | .float _, _, k, hk => hk _
  | .pair a b, p, k, hk => by
    dsimp only [unpackToLeaves]
    cases p with
    | imm _ => exact hk _
    | var _ =>
      dsimp only [Expr.callsOk]
      exact unpackToLeaves_callsOk target a _ _ fun la =>
        unpackToLeaves_callsOk target b _ _ fun lb => hk _

private theorem unpackToLegal_callsOk (target : LegalTarget) :
    ∀ (t : Ty) (x : Arg (fun _ => Unit) t)
      (k : Tup (Arg (fun _ => Unit)) (target.legalTys t) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (unpackToLegal target t x k).callsOk allowed exits
  | .bool, _, k, hk => hk _
  | .bits _, _, k, hk => by dsimp only [unpackToLegal]; solve_calls_cps hk
  | .float _, _, k, hk => hk _
  | .pair a b, p, k, hk => by
    dsimp only [unpackToLegal]
    split
    · exact hk _
    · cases p with
      | imm _ => exact hk _
      | var _ =>
        dsimp only [Expr.callsOk]
        exact unpackToLegal_callsOk target a _ _ fun la =>
          unpackToLegal_callsOk target b _ _ fun lb => hk _

private theorem packFromLegal_callsOk (target : LegalTarget) :
    ∀ (t : Ty) (xs : Tup (Arg (fun _ => Unit)) (target.legalTys t))
      (k : Arg (fun _ => Unit) t → Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (packFromLegal target t xs k).callsOk allowed exits := by
  intro t
  induction t with
  | bool => intro (_, ()) k hk; exact hk _
  | bits n => intro (_, ()) k hk; dsimp only [packFromLegal]; solve_calls_cps hk
  | float f => intro (_, ()) k hk; exact hk _
  | pair a b iha ihb =>
    intro xs k hk
    dsimp only [packFromLegal]
    split
    · exact hk _
    · exact iha _ _ fun _ => ihb _ _ fun _ => hk _

private theorem splitLegalToLeaves_callsOk (target : LegalTarget) :
    ∀ (t : Ty) (xs : Tup (Arg (fun _ => Unit)) (target.legalTys t))
      (k : Tup (Arg (fun _ => Unit)) (target.leafTys t) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (splitLegalToLeaves target t xs k).callsOk allowed exits
  | .bool, _, k, hk => hk _
  | .bits _, _, k, hk => hk _
  | .float _, _, k, hk => hk _
  | .pair a b, xs, k, hk => by
    dsimp only [splitLegalToLeaves]
    split
    · exact unpackToLeaves_callsOk target (.pair a b) _ k hk
    · exact splitLegalToLeaves_callsOk target a _ _ fun _ =>
        splitLegalToLeaves_callsOk target b _ _ fun _ => hk _

private theorem packLeavesToLegal_callsOk (target : LegalTarget) :
    ∀ (t : Ty) (xs : Tup (Arg (fun _ => Unit)) (target.leafTys t))
      (k : Tup (Arg (fun _ => Unit)) (target.legalTys t) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (packLeavesToLegal target t xs k).callsOk allowed exits
  | .bool, _, k, hk => hk _
  | .bits _, _, k, hk => hk _
  | .float _, _, k, hk => hk _
  | .pair a b, xs, k, hk => by
    dsimp only [packLeavesToLegal]
    split
    · exact packLeavesToLegal_callsOk target a _ _ fun _ =>
        packLeavesToLegal_callsOk target b _ _ fun _ =>
          packFromLegal_callsOk target a _ _ fun _ =>
            packFromLegal_callsOk target b _ _ fun _ => hk _
    · exact packLeavesToLegal_callsOk target a _ _ fun _ =>
        packLeavesToLegal_callsOk target b _ _ fun _ => hk _

private theorem packLeavesToWords64_go_callsOk (target : LegalTarget) :
    ∀ (u : Ty) (xs : Tup (Arg (fun _ => Unit)) (target.leafTys u))
      (ws : List (Arg (fun _ => Unit) i64)) (acc : Arg (fun _ => Unit) i64) (accBits : Nat)
      (k : List (Arg (fun _ => Unit) i64) → Arg (fun _ => Unit) i64 → Nat →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ ws' acc' bits', (k ws' acc' bits').callsOk allowed exits) →
      (packLeavesToWords64.go target u xs ws acc accBits k).callsOk allowed exits := by
  intro u
  induction u with
  | bool =>
    intro (_, ()) ws acc accBits k hk
    dsimp only [packLeavesToWords64.go, Expr.callsOk]
    exact pushLeafWord64_callsOk hk
  | bits n =>
    intro (_, ()) ws acc accBits k hk
    dsimp only [packLeavesToWords64.go]
    repeat' (first
      | exact hk _ _ _
      | exact pushLeafWord64_callsOk hk
      | (dsimp only [Expr.callsOk]; exact pushLeafWord64_callsOk hk)
      | split)
  | float f =>
    intro (_, ()) ws acc accBits k hk
    dsimp only [packLeavesToWords64.go, Expr.callsOk]
    split
    · exact pushLeafWord64_callsOk hk
    · split <;> (dsimp only [Expr.callsOk]; exact pushLeafWord64_callsOk hk)
  | pair a b iha ihb =>
    intro xs ws acc accBits k hk
    dsimp only [packLeavesToWords64.go]
    exact iha _ ws acc accBits _ fun _ _ _ => ihb _ _ _ _ k hk

private theorem packLeavesToWords64_callsOk (target : LegalTarget) (t : Ty)
    (leaves : Tup (Arg (fun _ => Unit)) (target.leafTys t))
    (k : List (Arg (fun _ => Unit) i64) → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ res, (k res).callsOk allowed exits) :
    (packLeavesToWords64 target t leaves k).callsOk allowed exits :=
  packLeavesToWords64_go_callsOk target t leaves [] (.imm 0#64) 0 _ fun _ _ _ => by
    split <;> exact hk _

private theorem unpackWords64ToLeaves_callsOk (target : LegalTarget)
    (words : List (Arg (fun _ => Unit) i64)) :
    ∀ (off : Nat) (u : Ty)
      (k : Tup (Arg (fun _ => Unit)) (target.leafTys u) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (unpackWords64ToLeaves target words off u k).callsOk allowed exits := by
  intro off u
  induction u generalizing off with
  | bool => intro k hk; exact extractBitsFromWords64_callsOk fun _ => hk _
  | bits n =>
    intro k hk
    dsimp only [unpackWords64ToLeaves]
    split
    · exact hk _
    · exact extractBitsFromWords64_callsOk fun _ => by solve_calls_cps hk
  | float f =>
    intro k hk
    exact extractBitsFromWords64_callsOk fun _ => by solve_calls_cps hk
  | pair a b iha ihb =>
    intro k hk
    exact iha off _ fun _ => ihb (off + a.size) _ fun _ => hk _

private theorem loadByteChunksToWords64_callsOk (ptr : Arg (fun _ => Unit) i64) :
    ∀ (byteOff : Nat) (cs : List Nat) (ws : List (Arg (fun _ => Unit) i64))
      (acc : Arg (fun _ => Unit) i64) (accBits : Nat)
      (k : List (Arg (fun _ => Unit) i64) → Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (loadByteChunksToWords64 ptr byteOff cs ws acc accBits k).callsOk allowed exits
  | _, [], ws, acc, accBits, k, hk => by
    dsimp only [loadByteChunksToWords64]; split <;> exact hk _
  | byteOff, c :: cs, ws, acc, accBits, k, hk => by
    dsimp only [loadByteChunksToWords64]
    split <;> (
      dsimp only [Expr.callsOk]
      split
      · exact pushLeafWord64_callsOk fun ws' acc' bits' =>
          loadByteChunksToWords64_callsOk ptr (byteOff + c) cs ws' acc' bits' k hk
      · split <;> (
          try dsimp only [Expr.callsOk]
          exact pushLeafWord64_callsOk fun ws' acc' bits' =>
            loadByteChunksToWords64_callsOk ptr (byteOff + c) cs ws' acc' bits' k hk))

private theorem storeByteChunksFromWords64_callsOk
    (words : List (Arg (fun _ => Unit) i64)) (ptr : Arg (fun _ => Unit) i64) :
    ∀ (byteOff : Nat) (cs : List Nat) (k : Expr (fun _ => Unit) (fun _ => Unit) rs),
      k.callsOk allowed exits →
      (storeByteChunksFromWords64 words ptr byteOff cs k).callsOk allowed exits
  | _, [], _, hk => hk
  | byteOff, c :: cs, k, hk => by
    dsimp only [storeByteChunksFromWords64]
    refine extractBitsFromWords64_callsOk fun _ => ?_
    have ih := storeByteChunksFromWords64_callsOk words ptr (byteOff + c) cs k hk
    repeat' (first | exact ih | (dsimp only [Expr.callsOk]; exact ih) | split)

private theorem emitLoadBits_go_callsOk (n w : Nat)
    (ptr : Arg (fun _ => Unit) i64)
    (k : Arg (fun _ => Unit) (.bits w) → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ r, (k r).callsOk allowed exits) :
    ∀ (byteOff : Nat) (cs : List Nat) (acc : Option (Arg (fun _ => Unit) (.bits w))),
      (emitLoadBits.go n w ptr k byteOff cs acc).callsOk allowed exits
  | _, [], none => hk _
  | _, [], some _ => emitMaskToN_callsOk hk
  | byteOff, c :: rest, acc => by
    unfold emitLoadBits.go
    have hgo : ∀ acc',
        (emitLoadBits.go n w ptr k (byteOff + c) rest acc').callsOk allowed exits :=
      fun acc' => emitLoadBits_go_callsOk n w ptr k hk (byteOff + c) rest acc'
    cases acc <;>
      repeat' (first
        | exact hgo _
        | (dsimp only [Expr.callsOk]; exact hgo _)
        | split
        | dsimp only [Expr.callsOk])

private theorem emitLoadBits_callsOk (bitWidths : List Nat) (n w : Nat)
    (ptr : Arg (fun _ => Unit) i64)
    (k : Arg (fun _ => Unit) (.bits w) → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ r, (k r).callsOk allowed exits) :
    (emitLoadBits bitWidths n w ptr k).callsOk allowed exits := by
  dsimp only [emitLoadBits]
  split
  · exact hk _
  · exact emitLoadBits_go_callsOk n w ptr k hk 0 _ none

private theorem emitStoreBits_go_callsOk (w : Nat)
    (v : Arg (fun _ => Unit) (.bits w)) (ptr : Arg (fun _ => Unit) i64)
    (k : Expr (fun _ => Unit) (fun _ => Unit) rs) (hk : k.callsOk allowed exits) :
    ∀ (byteOff : Nat) (cs : List Nat),
      (emitStoreBits.go w v ptr k byteOff cs).callsOk allowed exits
  | _, [] => hk
  | byteOff, c :: rest => by
    unfold emitStoreBits.go
    have hgo := emitStoreBits_go_callsOk w v ptr k hk (byteOff + c) rest
    repeat' (first
      | exact hgo
      | (dsimp only [Expr.callsOk]; exact hgo)
      | split
      | dsimp only [Expr.callsOk])

private theorem emitStoreBits_callsOk (bitWidths : List Nat) (n w : Nat)
    (v : Arg (fun _ => Unit) (.bits w)) (ptr : Arg (fun _ => Unit) i64)
    (k : Expr (fun _ => Unit) (fun _ => Unit) rs) (hk : k.callsOk allowed exits) :
    (emitStoreBits bitWidths n w v ptr k).callsOk allowed exits := by
  dsimp only [emitStoreBits]
  split
  · exact hk
  · exact emitStoreBits_go_callsOk w v ptr k hk 0 _

private theorem words2ToDwords4_callsOk {w0 w1 : Arg (fun _ => Unit) i64}
    {k : Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
      Arg (fun _ => Unit) i32 → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ d0 d1 d2 d3, (k d0 d1 d2 d3).callsOk allowed exits) :
    (words2ToDwords4 w0 w1 k).callsOk allowed exits := by
  unfold words2ToDwords4; solve_calls_cps hk

private theorem dwords4ToWords2_callsOk {d0 d1 d2 d3 : Arg (fun _ => Unit) i32}
    {k : Arg (fun _ => Unit) i64 → Arg (fun _ => Unit) i64 →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ w0 w1, (k w0 w1).callsOk allowed exits) :
    (dwords4ToWords2 d0 d1 d2 d3 k).callsOk allowed exits := by
  unfold dwords4ToWords2; solve_calls_cps hk

private theorem dwordToBytes4_callsOk {d : Arg (fun _ => Unit) i32}
    {k : Arg (fun _ => Unit) i8 → Arg (fun _ => Unit) i8 → Arg (fun _ => Unit) i8 →
      Arg (fun _ => Unit) i8 → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ b0 b1 b2 b3, (k b0 b1 b2 b3).callsOk allowed exits) :
    (dwordToBytes4 d k).callsOk allowed exits := by
  unfold dwordToBytes4; solve_calls_cps hk

private theorem bytes4ToDword_callsOk {b0 b1 b2 b3 : Arg (fun _ => Unit) i8}
    {k : Arg (fun _ => Unit) i32 → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r, (k r).callsOk allowed exits) :
    (bytes4ToDword b0 b1 b2 b3 k).callsOk allowed exits := by
  unfold bytes4ToDword; solve_calls_cps hk

private theorem dwords4ToBytes16_callsOk {d0 d1 d2 d3 : Arg (fun _ => Unit) i32}
    {k : List (Arg (fun _ => Unit) i8) → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ bs, (k bs).callsOk allowed exits) :
    (dwords4ToBytes16 d0 d1 d2 d3 k).callsOk allowed exits := by
  unfold dwords4ToBytes16
  refine dwordToBytes4_callsOk fun _ _ _ _ => ?_
  refine dwordToBytes4_callsOk fun _ _ _ _ => ?_
  refine dwordToBytes4_callsOk fun _ _ _ _ => ?_
  refine dwordToBytes4_callsOk fun _ _ _ _ => hk _

private theorem bytes16ToDwords4_callsOk {bs : List (Arg (fun _ => Unit) i8)}
    {k : Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
      Arg (fun _ => Unit) i32 → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ d0 d1 d2 d3, (k d0 d1 d2 d3).callsOk allowed exits) :
    (bytes16ToDwords4 bs k).callsOk allowed exits := by
  unfold bytes16ToDwords4
  refine bytes4ToDword_callsOk fun _ => ?_
  refine bytes4ToDword_callsOk fun _ => ?_
  refine bytes4ToDword_callsOk fun _ => ?_
  refine bytes4ToDword_callsOk fun _ => hk _ _ _ _

private theorem scalarBlendwLane_callsOk {imm : BitVec 8} {idx : Nat}
    {ai bi : Arg (fun _ => Unit) i32}
    {k : Arg (fun _ => Unit) i32 → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r, (k r).callsOk allowed exits) :
    (scalarBlendwLane imm idx ai bi k).callsOk allowed exits := by
  unfold scalarBlendwLane; solve_calls_cps hk

private theorem scalarBlendw128_callsOk {imm : BitVec 8}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Arg (fun _ => Unit) i32}
    {k : Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
      Arg (fun _ => Unit) i32 → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r0 r1 r2 r3, (k r0 r1 r2 r3).callsOk allowed exits) :
    (scalarBlendw128 imm a0 a1 a2 a3 b0 b1 b2 b3 k).callsOk allowed exits := by
  unfold scalarBlendw128
  refine scalarBlendwLane_callsOk fun _ => ?_
  refine scalarBlendwLane_callsOk fun _ => ?_
  refine scalarBlendwLane_callsOk fun _ => ?_
  refine scalarBlendwLane_callsOk fun _ => hk _ _ _ _

private theorem scalarAlignr128_callsOk {imm : BitVec 8}
    {h0 h1 h2 h3 l0 l1 l2 l3 : Arg (fun _ => Unit) i32}
    {k : Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
      Arg (fun _ => Unit) i32 → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r0 r1 r2 r3, (k r0 r1 r2 r3).callsOk allowed exits) :
    (scalarAlignr128 imm h0 h1 h2 h3 l0 l1 l2 l3 k).callsOk allowed exits := by
  unfold scalarAlignr128
  refine dwords4ToBytes16_callsOk fun _ => ?_
  refine dwords4ToBytes16_callsOk fun _ => ?_
  exact bytes16ToDwords4_callsOk hk

private theorem scalarShufb128_mux_callsOk (idx : Arg (fun _ => Unit) i8) :
    ∀ (bs : List (Arg (fun _ => Unit) i8)) (j : Nat)
      (k : Arg (fun _ => Unit) i8 → Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ r, (k r).callsOk allowed exits) →
      (scalarShufb128.muxBytes idx bs j k).callsOk allowed exits
  | [], _, k, hk => hk _
  | [_], _, k, hk => hk _
  | _ :: _ :: _, j, k, hk =>
    scalarShufb128_mux_callsOk idx _ (j + 1) _ fun _ => by dsimp only [Expr.callsOk]; exact hk _

private theorem scalarShufb128_doBytes_callsOk
    (k : Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
      Arg (fun _ => Unit) i32 → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ r0 r1 r2 r3, (k r0 r1 r2 r3).callsOk allowed exits)
    (abs mbs : List (Arg (fun _ => Unit) i8)) :
    ∀ (d i : Nat), 16 - i ≤ d → ∀ acc,
      (scalarShufb128.doBytes k abs mbs i acc).callsOk allowed exits
  | 0, i, hd, acc => by
    have hge : i ≥ 16 := by omega
    rw [scalarShufb128.doBytes.eq_def]; simp only [hge, ↓reduceIte]
    exact bytes16ToDwords4_callsOk hk
  | d + 1, i, hd, acc => by
    rw [scalarShufb128.doBytes.eq_def]
    by_cases hge : i ≥ 16
    · simp only [hge, ↓reduceIte]; exact bytes16ToDwords4_callsOk hk
    · simp only [hge, ↓reduceIte, Expr.callsOk]
      exact scalarShufb128_mux_callsOk _ abs 0 _ fun _ => by
        dsimp only [Expr.callsOk]
        exact scalarShufb128_doBytes_callsOk k hk abs mbs d (i + 1) (by omega) _

private theorem scalarShufb128_callsOk
    {a0 a1 a2 a3 m0 m1 m2 m3 : Arg (fun _ => Unit) i32}
    {k : Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
      Arg (fun _ => Unit) i32 → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r0 r1 r2 r3, (k r0 r1 r2 r3).callsOk allowed exits) :
    (scalarShufb128 a0 a1 a2 a3 m0 m1 m2 m3 k).callsOk allowed exits := by
  unfold scalarShufb128
  refine dwords4ToBytes16_callsOk fun abs => ?_
  refine dwords4ToBytes16_callsOk fun mbs => ?_
  exact scalarShufb128_doBytes_callsOk k hk abs mbs 16 0 (Nat.le_refl _) []

private theorem emitShaMix3_callsOk {thirdLshr : Bool} {n1 n2 n3 : Nat}
    {x : Arg (fun _ => Unit) i32}
    {k : Arg (fun _ => Unit) i32 → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r, (k r).callsOk allowed exits) :
    (emitShaMix3 thirdLshr n1 n2 n3 x k).callsOk allowed exits := by
  unfold emitShaMix3 emitRotr32 emitLshr32 emitXor32; solve_calls_cps hk

private theorem emitShaCh_callsOk {x y z : Arg (fun _ => Unit) i32}
    {k : Arg (fun _ => Unit) i32 → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r, (k r).callsOk allowed exits) :
    (emitShaCh x y z k).callsOk allowed exits := by
  unfold emitShaCh emitAnd32 emitNot32 emitXor32; solve_calls_cps hk

private theorem emitShaMaj_callsOk {x y z : Arg (fun _ => Unit) i32}
    {k : Arg (fun _ => Unit) i32 → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r, (k r).callsOk allowed exits) :
    (emitShaMaj x y z k).callsOk allowed exits := by
  unfold emitShaMaj emitAnd32 emitXor32; solve_calls_cps hk

private theorem emitShaRound_callsOk {a b c d e f g h wk : Arg (fun _ => Unit) i32}
    {k : Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
      Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
      Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ a' b' c' d' e' f' g' h', (k a' b' c' d' e' f' g' h').callsOk allowed exits) :
    (emitShaRound a b c d e f g h wk k).callsOk allowed exits := by
  unfold emitShaRound emitShaSigma0 emitShaSigma1 emitAdd32
  refine emitShaCh_callsOk fun _ => ?_
  refine emitShaMix3_callsOk fun _ => ?_
  dsimp only [Expr.callsOk]
  refine emitShaMaj_callsOk fun _ => ?_
  refine emitShaMix3_callsOk fun _ => ?_
  dsimp only [Expr.callsOk]; exact hk _ _ _ _ _ _ _ _

private theorem scalarSha256rnds2_callsOk
    {cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 wk2 wk3 : Arg (fun _ => Unit) i32}
    {k : Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
      Arg (fun _ => Unit) i32 → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r0 r1 r2 r3, (k r0 r1 r2 r3).callsOk allowed exits) :
    (scalarSha256rnds2 cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 wk2 wk3 k).callsOk
      allowed exits := by
  unfold scalarSha256rnds2
  refine emitShaRound_callsOk fun _ _ _ _ _ _ _ _ => ?_
  exact emitShaRound_callsOk fun _ _ _ _ _ _ _ _ => hk _ _ _ _

private theorem scalarSha256msg1_callsOk
    {a0 a1 a2 a3 b0 b1 b2 b3 : Arg (fun _ => Unit) i32}
    {k : Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
      Arg (fun _ => Unit) i32 → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r0 r1 r2 r3, (k r0 r1 r2 r3).callsOk allowed exits) :
    (scalarSha256msg1 a0 a1 a2 a3 b0 b1 b2 b3 k).callsOk allowed exits := by
  unfold scalarSha256msg1 emitShaSig0 emitAdd32
  refine emitShaMix3_callsOk fun _ => ?_
  dsimp only [Expr.callsOk]
  refine emitShaMix3_callsOk fun _ => ?_
  dsimp only [Expr.callsOk]
  refine emitShaMix3_callsOk fun _ => ?_
  dsimp only [Expr.callsOk]
  refine emitShaMix3_callsOk fun _ => ?_
  dsimp only [Expr.callsOk]; exact hk _ _ _ _

private theorem scalarSha256msg2_callsOk
    {s0 s1 s2 s3 w0 w1 w2 w3 : Arg (fun _ => Unit) i32}
    {k : Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
      Arg (fun _ => Unit) i32 → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hk : ∀ r0 r1 r2 r3, (k r0 r1 r2 r3).callsOk allowed exits) :
    (scalarSha256msg2 s0 s1 s2 s3 w0 w1 w2 w3 k).callsOk allowed exits := by
  unfold scalarSha256msg2 emitShaSig1 emitAdd32
  refine emitShaMix3_callsOk fun _ => ?_
  dsimp only [Expr.callsOk]
  refine emitShaMix3_callsOk fun _ => ?_
  dsimp only [Expr.callsOk]
  refine emitShaMix3_callsOk fun _ => ?_
  dsimp only [Expr.callsOk]
  refine emitShaMix3_callsOk fun _ => ?_
  dsimp only [Expr.callsOk]; exact hk _ _ _ _

end BaseCallsMore

section TreeCalls

variable (target : LegalTarget) {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}

private theorem legalUnaryTree_goS_callsOk
    {onBool : Arg (fun _ => Unit) .bool →
      (Arg (fun _ => Unit) .bool → Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    {onBits : (n : Nat) → Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
      (Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
        Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    {onFloat : (f : Fmt) → Arg (fun _ => Unit) (.float f) →
      (Arg (fun _ => Unit) (.float f) → Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hb : ∀ x cont, (∀ r, (cont r).callsOk allowed exits) → (onBool x cont).callsOk allowed exits)
    (hn : ∀ n x cont, (∀ r, (cont r).callsOk allowed exits) →
      (onBits n x cont).callsOk allowed exits)
    (hf : ∀ f x cont, (∀ r, (cont r).callsOk allowed exits) →
      (onFloat f x cont).callsOk allowed exits) :
    ∀ (u : Ty) (fx : Tup (Arg (fun _ => Unit)) (target.leafTys u))
      (c : Tup (Arg (fun _ => Unit)) (target.leafTys u) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (c res).callsOk allowed exits) →
      (legalUnaryTree.goS target onBool onBits onFloat u fx c).callsOk allowed exits
  | .bool, (x, ()), _, hc => hb x _ fun _ => hc _
  | .bits n, (x, ()), _, hc => hn n x _ fun _ => hc _
  | .float f, (x, ()), _, hc => hf f x _ fun _ => hc _
  | .pair u1 u2, _, _, hc =>
    legalUnaryTree_goS_callsOk hb hn hf u1 _ _ fun _ =>
      legalUnaryTree_goS_callsOk hb hn hf u2 _ _ fun _ => hc _

private theorem legalUnaryTree_callsOk
    (mkCode : (u : Ty) → OpCode [u] [u]) (vecSupported : (u : Ty) → Bool)
    {onBool : Arg (fun _ => Unit) .bool →
      (Arg (fun _ => Unit) .bool → Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    {onBits : (n : Nat) → Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
      (Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
        Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    {onFloat : (f : Fmt) → Arg (fun _ => Unit) (.float f) →
      (Arg (fun _ => Unit) (.float f) → Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hb : ∀ x cont, (∀ r, (cont r).callsOk allowed exits) → (onBool x cont).callsOk allowed exits)
    (hn : ∀ n x cont, (∀ r, (cont r).callsOk allowed exits) →
      (onBits n x cont).callsOk allowed exits)
    (hf : ∀ f x cont, (∀ r, (cont r).callsOk allowed exits) →
      (onFloat f x cont).callsOk allowed exits) :
    ∀ (t : Ty) (xs : Tup (Arg (fun _ => Unit)) (target.legalTys t))
      (k : Tup (Arg (fun _ => Unit)) (target.legalTys t) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (legalUnaryTree target mkCode vecSupported onBool onBits onFloat t xs k).callsOk allowed exits
  | .bool, (x, ()), _, hk => hb x _ fun _ => hk _
  | .bits n, (x, ()), _, hk => hn n x _ fun _ => hk _
  | .float f, (x, ()), _, hk => hf f x _ fun _ => hk _
  | .pair t1 t2, xs, k, hk => by
    dsimp only [legalUnaryTree]
    split
    · split
      · exact hk _
      · exact splitLegalToLeaves_callsOk target (.pair t1 t2) xs _ fun _ =>
          legalUnaryTree_goS_callsOk target hb hn hf (.pair t1 t2) _ _ fun _ =>
            packLeavesToLegal_callsOk target (.pair t1 t2) _ k hk
    · exact legalUnaryTree_callsOk mkCode vecSupported hb hn hf t1 _ _ fun _ =>
        legalUnaryTree_callsOk mkCode vecSupported hb hn hf t2 _ _ fun _ => hk _

private theorem legalBswapTree_callsOk (t : Ty)
    (xs : Tup (Arg (fun _ => Unit)) (target.legalTys t))
    (k : Tup (Arg (fun _ => Unit)) (target.legalTys t) →
      Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ res, (k res).callsOk allowed exits) :
    (legalBswapTree target t xs k).callsOk allowed exits := by
  dsimp only [legalBswapTree]
  split
  · trivial
  · refine legalUnaryTree_callsOk target _ _ ?_ ?_ ?_ t xs k hk
    · intro _ _ _; trivial
    · intro _ _ _ h; solve_calls_cps h
    · intro _ _ _ _; trivial

private theorem legalTernaryTree_goS_callsOk
    {onBool : Arg (fun _ => Unit) .bool → Arg (fun _ => Unit) .bool →
      Arg (fun _ => Unit) .bool →
      (Arg (fun _ => Unit) .bool → Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    {onBits : (n : Nat) → Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
      Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
      Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
      (Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
        Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    {onFloat : (f : Fmt) → Arg (fun _ => Unit) (.float f) →
      Arg (fun _ => Unit) (.float f) → Arg (fun _ => Unit) (.float f) →
      (Arg (fun _ => Unit) (.float f) → Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hb : ∀ a b c cont, (∀ r, (cont r).callsOk allowed exits) →
      (onBool a b c cont).callsOk allowed exits)
    (hn : ∀ n a b c cont, (∀ r, (cont r).callsOk allowed exits) →
      (onBits n a b c cont).callsOk allowed exits)
    (hf : ∀ f a b c cont, (∀ r, (cont r).callsOk allowed exits) →
      (onFloat f a b c cont).callsOk allowed exits) :
    ∀ (u : Ty) (fx fy fz : Tup (Arg (fun _ => Unit)) (target.leafTys u))
      (c : Tup (Arg (fun _ => Unit)) (target.leafTys u) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (c res).callsOk allowed exits) →
      (legalTernaryTree.goS target onBool onBits onFloat u fx fy fz c).callsOk allowed exits
  | .bool, (_, ()), (_, ()), (_, ()), _, hc => hb _ _ _ _ fun _ => hc _
  | .bits n, (_, ()), (_, ()), (_, ()), _, hc => hn n _ _ _ _ fun _ => hc _
  | .float f, (_, ()), (_, ()), (_, ()), _, hc => hf f _ _ _ _ fun _ => hc _
  | .pair u1 u2, _, _, _, _, hc =>
    legalTernaryTree_goS_callsOk hb hn hf u1 _ _ _ _ fun _ =>
      legalTernaryTree_goS_callsOk hb hn hf u2 _ _ _ _ fun _ => hc _

private theorem legalTernaryTree_callsOk
    (mkCode : (u : Ty) → OpCode [u, u, u] [u]) (vecSupported : (u : Ty) → Bool)
    {onBool : Arg (fun _ => Unit) .bool → Arg (fun _ => Unit) .bool →
      Arg (fun _ => Unit) .bool →
      (Arg (fun _ => Unit) .bool → Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    {onBits : (n : Nat) → Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
      Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
      Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
      (Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
        Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    {onFloat : (f : Fmt) → Arg (fun _ => Unit) (.float f) →
      Arg (fun _ => Unit) (.float f) → Arg (fun _ => Unit) (.float f) →
      (Arg (fun _ => Unit) (.float f) → Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hb : ∀ a b c cont, (∀ r, (cont r).callsOk allowed exits) →
      (onBool a b c cont).callsOk allowed exits)
    (hn : ∀ n a b c cont, (∀ r, (cont r).callsOk allowed exits) →
      (onBits n a b c cont).callsOk allowed exits)
    (hf : ∀ f a b c cont, (∀ r, (cont r).callsOk allowed exits) →
      (onFloat f a b c cont).callsOk allowed exits) :
    ∀ (t : Ty) (xs ys zs : Tup (Arg (fun _ => Unit)) (target.legalTys t))
      (k : Tup (Arg (fun _ => Unit)) (target.legalTys t) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (legalTernaryTree target mkCode vecSupported onBool onBits onFloat t xs ys zs k).callsOk
        allowed exits
  | .bool, (_, ()), (_, ()), (_, ()), _, hk => hb _ _ _ _ fun _ => hk _
  | .bits n, (_, ()), (_, ()), (_, ()), _, hk => hn n _ _ _ _ fun _ => hk _
  | .float f, (_, ()), (_, ()), (_, ()), _, hk => hf f _ _ _ _ fun _ => hk _
  | .pair t1 t2, xs, ys, zs, k, hk => by
    dsimp only [legalTernaryTree]
    split
    · split
      · exact hk _
      · exact splitLegalToLeaves_callsOk target (.pair t1 t2) xs _ fun _ =>
          splitLegalToLeaves_callsOk target (.pair t1 t2) ys _ fun _ =>
            splitLegalToLeaves_callsOk target (.pair t1 t2) zs _ fun _ =>
              legalTernaryTree_goS_callsOk target hb hn hf (.pair t1 t2) _ _ _ _ fun _ =>
                packLeavesToLegal_callsOk target (.pair t1 t2) _ k hk
    · exact legalTernaryTree_callsOk mkCode vecSupported hb hn hf t1 _ _ _ _ fun _ =>
        legalTernaryTree_callsOk mkCode vecSupported hb hn hf t2 _ _ _ _ fun _ => hk _

private theorem legalBinTree_goS_callsOk
    {onBool : Arg (fun _ => Unit) .bool → Arg (fun _ => Unit) .bool →
      (Arg (fun _ => Unit) .bool → Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    {onBits : (n : Nat) → Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
      Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
      (Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
        Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    {onFloat : (f : Fmt) → Arg (fun _ => Unit) (.float f) →
      Arg (fun _ => Unit) (.float f) →
      (Arg (fun _ => Unit) (.float f) → Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hb : ∀ a b cont, (∀ r, (cont r).callsOk allowed exits) →
      (onBool a b cont).callsOk allowed exits)
    (hn : ∀ n a b cont, (∀ r, (cont r).callsOk allowed exits) →
      (onBits n a b cont).callsOk allowed exits)
    (hf : ∀ f a b cont, (∀ r, (cont r).callsOk allowed exits) →
      (onFloat f a b cont).callsOk allowed exits) :
    ∀ (u : Ty) (fx fy : Tup (Arg (fun _ => Unit)) (target.leafTys u))
      (c : Tup (Arg (fun _ => Unit)) (target.leafTys u) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (c res).callsOk allowed exits) →
      (legalBinTree.goS target onBool onBits onFloat u fx fy c).callsOk allowed exits
  | .bool, (_, ()), (_, ()), _, hc => hb _ _ _ fun _ => hc _
  | .bits n, (_, ()), (_, ()), _, hc => hn n _ _ _ fun _ => hc _
  | .float f, (_, ()), (_, ()), _, hc => hf f _ _ _ fun _ => hc _
  | .pair u1 u2, _, _, _, hc =>
    legalBinTree_goS_callsOk hb hn hf u1 _ _ _ fun _ =>
      legalBinTree_goS_callsOk hb hn hf u2 _ _ _ fun _ => hc _

private theorem legalBinTree_callsOk
    (mkCode : (u : Ty) → OpCode [u, u] [u]) (vecSupported : (u : Ty) → Bool → Bool)
    {onBool : Arg (fun _ => Unit) .bool → Arg (fun _ => Unit) .bool →
      (Arg (fun _ => Unit) .bool → Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    {onBits : (n : Nat) → Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
      Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
      (Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
        Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    {onFloat : (f : Fmt) → Arg (fun _ => Unit) (.float f) →
      Arg (fun _ => Unit) (.float f) →
      (Arg (fun _ => Unit) (.float f) → Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    (unifRhs : (u : Ty) → Arg (LVar target (fun _ => Unit)) u → Bool)
    (hb : ∀ a b cont, (∀ r, (cont r).callsOk allowed exits) →
      (onBool a b cont).callsOk allowed exits)
    (hn : ∀ n a b cont, (∀ r, (cont r).callsOk allowed exits) →
      (onBits n a b cont).callsOk allowed exits)
    (hf : ∀ f a b cont, (∀ r, (cont r).callsOk allowed exits) →
      (onFloat f a b cont).callsOk allowed exits) :
    ∀ (t : Ty) (xs ys : Tup (Arg (fun _ => Unit)) (target.legalTys t))
      (rawRhs : Option (Arg (LVar target (fun _ => Unit)) t))
      (k : Tup (Arg (fun _ => Unit)) (target.legalTys t) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (legalBinTree target mkCode vecSupported onBool onBits onFloat unifRhs t xs ys rawRhs
        k).callsOk allowed exits
  | .bool, (_, ()), (_, ()), _, _, hk => hb _ _ _ fun _ => hk _
  | .bits n, (_, ()), (_, ()), _, _, hk => hn n _ _ _ fun _ => hk _
  | .float f, (_, ()), (_, ()), _, _, hk => hf f _ _ _ fun _ => hk _
  | .pair t1 t2, xs, ys, rawRhs, k, hk => by
    dsimp only [legalBinTree]
    split
    · split
      · exact hk _
      · have hnone : (splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
            splitLegalToLeaves target (.pair t1 t2) ys fun fy =>
              legalBinTree.goS target onBool onBits onFloat (.pair t1 t2) fx fy fun fres =>
                packLeavesToLegal target (.pair t1 t2) fres k).callsOk allowed exits :=
          splitLegalToLeaves_callsOk target (.pair t1 t2) xs _ fun _ =>
            splitLegalToLeaves_callsOk target (.pair t1 t2) ys _ fun _ =>
              legalBinTree_goS_callsOk target hb hn hf (.pair t1 t2) _ _ _ fun _ =>
                packLeavesToLegal_callsOk target (.pair t1 t2) _ k hk
        cases rawRhs with
        | none =>
          cases opShiftKind (mkCode (.pair t1 t2)) with
          | none => exact hnone
          | some sb => cases sb <;> exact hnone
        | some rhs =>
          cases opShiftKind (mkCode (.pair t1 t2)) with
          | none => exact hnone
          | some sb =>
            cases sb <;> cases rhs <;> try exact hnone
            · dsimp only
              cases uniformShiftLeaf? (.pair t1 t2) _ with
              | none => exact hnone
              | some val =>
                rcases val with ⟨w, s⟩
                split
                · rename_i heq
                  dsimp only at heq
                  split at heq
                  · cases heq; exact hk _
                  · split at heq
                    · cases heq; try dsimp only [Expr.callsOk]; exact hk _
                    · cases heq
                · exact hnone
            · dsimp only
              cases uniformShiftLeaf? (.pair t1 t2) _ with
              | none => exact hnone
              | some val =>
                rcases val with ⟨w, s⟩
                split
                · rename_i heq
                  dsimp only at heq
                  split at heq
                  · cases heq; exact hk _
                  · split at heq
                    · cases heq; try dsimp only [Expr.callsOk]; exact hk _
                    · cases heq
                · exact hnone
    · exact legalBinTree_callsOk mkCode vecSupported unifRhs hb hn hf t1 _ _ none _ fun _ =>
        legalBinTree_callsOk mkCode vecSupported unifRhs hb hn hf t2 _ _ none _ fun _ => hk _

private theorem legalBitsArith_callsOk (n : Nat) (code : OpCode [.bits n, .bits n] [.bits n])
    (a b : Arg (fun _ => Unit) (.bits (target.widenWidth n)))
    (k : Arg (fun _ => Unit) (.bits (target.widenWidth n)) →
      Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ r, (k r).callsOk allowed exits) :
    (legalBitsArith target n code a b k).callsOk allowed exits := by
  unfold legalBitsArith
  solve_legal_cps hk

private theorem legalCmpTree_goMask_callsOk (o : CmpOp) :
    ∀ (u : Ty) (fx fy : Tup (Arg (fun _ => Unit)) (target.leafTys u))
      (c : Tup (Arg (fun _ => Unit)) (target.leafTys u.mask) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (c res).callsOk allowed exits) →
      (legalCmpTree.goMask target o u fx fy c).callsOk allowed exits := by
  intro u
  induction u with
  | bool =>
    intro (_, ()) (_, ()) k hc
    dsimp only [legalCmpTree.goMask]; solve_legal_cps hc
  | bits n =>
    intro (_, ()) (_, ()) k hc
    dsimp only [legalCmpTree.goMask]
    split
    · exact hc _
    · split
      · exact hc _
      · cases o <;> solve_legal_cps hc
  | float f => intro _ _ _ _; trivial
  | pair u1 u2 ih1 ih2 =>
    intro fx fy k hc
    exact ih1 _ _ _ fun _ => ih2 _ _ _ fun _ => hc _

private theorem legalCmpTree_callsOk (o : CmpOp) :
    ∀ (t : Ty) (xs ys : Tup (Arg (fun _ => Unit)) (target.legalTys t))
      (k : Tup (Arg (fun _ => Unit)) (target.legalTys t.mask) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (legalCmpTree target o t xs ys k).callsOk allowed exits := by
  intro t
  induction t with
  | bool =>
    intro (_, ()) (_, ()) k hk
    dsimp only [legalCmpTree]; solve_legal_cps hk
  | bits n =>
    intro (_, ()) (_, ()) k hk
    dsimp only [legalCmpTree]
    split
    · exact hk _
    · split
      · exact hk _
      · cases o <;> solve_legal_cps hk
  | float f => intro _ _ _ _; trivial
  | pair t1 t2 _ _ =>
    intro xs ys k hk
    exact splitLegalToLeaves_callsOk target (.pair t1 t2) xs _ fun _ =>
      splitLegalToLeaves_callsOk target (.pair t1 t2) ys _ fun _ =>
        legalCmpTree_goMask_callsOk target o (.pair t1 t2) _ _ _ fun _ =>
          packLeavesToLegal_callsOk target (Ty.mask (.pair t1 t2)) _ k hk

private theorem legalSelectTree_goSel_callsOk (c : Arg (fun _ => Unit) .bool) :
    ∀ (u : Ty) (fx fy : Tup (Arg (fun _ => Unit)) (target.leafTys u))
      (k : Tup (Arg (fun _ => Unit)) (target.leafTys u) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (legalSelectTree.goSel target c u fx fy k).callsOk allowed exits
  | .bool, (_, ()), (_, ()), _, hk => by
    dsimp only [legalSelectTree.goSel]; split
    · exact hk _
    · exact emitBoolSelect_callsOk fun _ => hk _
  | .bits n, (_, ()), (_, ()), _, hk => hk _
  | .float _f, (_, ()), (_, ()), _, hk => hk _
  | .pair u1 u2, _, _, _, hk =>
    legalSelectTree_goSel_callsOk c u1 _ _ _ fun _ =>
      legalSelectTree_goSel_callsOk c u2 _ _ _ fun _ => hk _

private theorem legalSelectTree_callsOk (c : Arg (fun _ => Unit) .bool) :
    ∀ (t : Ty) (xs ys : Tup (Arg (fun _ => Unit)) (target.legalTys t))
      (k : Tup (Arg (fun _ => Unit)) (target.legalTys t) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (legalSelectTree target c t xs ys k).callsOk allowed exits
  | .bool, (_, ()), (_, ()), _, hk => by
    dsimp only [legalSelectTree]; split
    · exact hk _
    · exact emitBoolSelect_callsOk fun _ => hk _
  | .bits n, (_, ()), (_, ()), _, hk => hk _
  | .float _f, (_, ()), (_, ()), _, hk => hk _
  | .pair t1 t2, xs, ys, k, hk =>
    splitLegalToLeaves_callsOk target (.pair t1 t2) xs _ fun _ =>
      splitLegalToLeaves_callsOk target (.pair t1 t2) ys _ fun _ =>
        legalSelectTree_goSel_callsOk target c (.pair t1 t2) _ _ _ fun _ =>
          packLeavesToLegal_callsOk target (.pair t1 t2) _ k hk

private theorem legalBlendTree_goBlend_callsOk :
    ∀ (u : Ty) (fm : Tup (Arg (fun _ => Unit)) (target.leafTys u.mask))
      (fx fy : Tup (Arg (fun _ => Unit)) (target.leafTys u))
      (k : Tup (Arg (fun _ => Unit)) (target.leafTys u) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (legalBlendTree.goBlend target u fm fx fy k).callsOk allowed exits
  | .bool, (_, ()), (_, ()), (_, ()), _, hk => by
    dsimp only [legalBlendTree.goBlend]; split
    · exact hk _
    · exact emitBoolSelect_callsOk fun _ => hk _
  | .bits n, (_, ()), (_, ()), (_, ()), _, hk => hk _
  | .float _f, (_, ()), (_, ()), (_, ()), _, hk => hk _
  | .pair u1 u2, _, _, _, _, hk =>
    legalBlendTree_goBlend_callsOk u1 _ _ _ _ fun _ =>
      legalBlendTree_goBlend_callsOk u2 _ _ _ _ fun _ => hk _

private theorem legalBlendTree_callsOk :
    ∀ (t : Ty) (ms : Tup (Arg (fun _ => Unit)) (target.legalTys t.mask))
      (xs ys : Tup (Arg (fun _ => Unit)) (target.legalTys t))
      (k : Tup (Arg (fun _ => Unit)) (target.legalTys t) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (legalBlendTree target t ms xs ys k).callsOk allowed exits
  | .bool, (_, ()), (_, ()), (_, ()), _, hk => by
    dsimp only [legalBlendTree]; split
    · exact hk _
    · exact emitBoolSelect_callsOk fun _ => hk _
  | .bits n, (_, ()), (_, ()), (_, ()), _, hk => hk _
  | .float _f, (_, ()), (_, ()), (_, ()), _, hk => hk _
  | .pair t1 t2, ms, xs, ys, k, hk =>
    splitLegalToLeaves_callsOk target (Ty.mask (.pair t1 t2)) ms _ fun _ =>
      splitLegalToLeaves_callsOk target (.pair t1 t2) xs _ fun _ =>
        splitLegalToLeaves_callsOk target (.pair t1 t2) ys _ fun _ =>
          legalBlendTree_goBlend_callsOk target (.pair t1 t2) _ _ _ _ fun _ =>
            packLeavesToLegal_callsOk target (.pair t1 t2) _ k hk

private theorem legalFCmpTree_goFCmp_callsOk (o : FCmpOp) :
    ∀ (u : Ty) (fx fy : Tup (Arg (fun _ => Unit)) (target.leafTys u))
      (k : Tup (Arg (fun _ => Unit)) (target.leafTys u.mask) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (legalFCmpTree.goFCmp target o u fx fy k).callsOk allowed exits
  | .bool, _, _, _, _ => trivial
  | .bits _, _, _, _, _ => trivial
  | .float _f, (_, ()), (_, ()), _, hk => hk _
  | .pair u1 u2, _, _, _, hk =>
    legalFCmpTree_goFCmp_callsOk o u1 _ _ _ fun _ =>
      legalFCmpTree_goFCmp_callsOk o u2 _ _ _ fun _ => hk _

private theorem legalFCmpTree_callsOk (o : FCmpOp) :
    ∀ (t : Ty) (xs ys : Tup (Arg (fun _ => Unit)) (target.legalTys t))
      (k : Tup (Arg (fun _ => Unit)) (target.legalTys t.mask) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (legalFCmpTree target o t xs ys k).callsOk allowed exits
  | .bool, _, _, _, _ => trivial
  | .bits _, _, _, _, _ => trivial
  | .float _f, (_, ()), (_, ()), _, hk => hk _
  | .pair t1 t2, xs, ys, k, hk =>
    splitLegalToLeaves_callsOk target (.pair t1 t2) xs _ fun _ =>
      splitLegalToLeaves_callsOk target (.pair t1 t2) ys _ fun _ =>
        legalFCmpTree_goFCmp_callsOk target o (.pair t1 t2) _ _ _ fun _ =>
          packLeavesToLegal_callsOk target (Ty.mask (.pair t1 t2)) _ k hk

private theorem legalSimdScalar128_goWords_callsOk
    (on128 : Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
      Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
      Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
      (Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
        Arg (fun _ => Unit) i32 → Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hon : ∀ a0 a1 a2 a3 b0 b1 b2 b3 cont,
      (∀ r0 r1 r2 r3, (cont r0 r1 r2 r3).callsOk allowed exits) →
      (on128 a0 a1 a2 a3 b0 b1 b2 b3 cont).callsOk allowed exits)
    (t : Ty)
    (k : Tup (Arg (fun _ => Unit)) (target.legalTys t) →
      Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ res, (k res).callsOk allowed exits) :
    ∀ (wx wy acc : List (Arg (fun _ => Unit) i64)),
      (legalSimdScalar128.goWords target on128 t k wx wy acc).callsOk allowed exits
  | _ :: _ :: _, _ :: _ :: _, _ =>
    words2ToDwords4_callsOk fun _ _ _ _ =>
      words2ToDwords4_callsOk fun _ _ _ _ =>
        hon _ _ _ _ _ _ _ _ _ fun _ _ _ _ =>
          dwords4ToWords2_callsOk fun w0 w1 =>
            legalSimdScalar128_goWords_callsOk on128 hon t k hk _ _ (_ ++ [w0, w1])
  | [], _, acc | [_], _, acc | _ :: _ :: _, [], acc | _ :: _ :: _, [_], acc =>
    unpackWords64ToLeaves_callsOk target acc 0 t _ fun _ =>
      packLeavesToLegal_callsOk target t _ k hk

private theorem legalSimdScalar128_callsOk
    (on128 : Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
      Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
      Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
      (Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 → Arg (fun _ => Unit) i32 →
        Arg (fun _ => Unit) i32 → Expr (fun _ => Unit) (fun _ => Unit) rs) →
      Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hon : ∀ a0 a1 a2 a3 b0 b1 b2 b3 cont,
      (∀ r0 r1 r2 r3, (cont r0 r1 r2 r3).callsOk allowed exits) →
      (on128 a0 a1 a2 a3 b0 b1 b2 b3 cont).callsOk allowed exits)
    (t : Ty) (xs ys : Tup (Arg (fun _ => Unit)) (target.legalTys t))
    (k : Tup (Arg (fun _ => Unit)) (target.legalTys t) →
      Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ res, (k res).callsOk allowed exits) :
    (legalSimdScalar128 target on128 t xs ys k).callsOk allowed exits :=
  splitLegalToLeaves_callsOk target t xs _ fun _ =>
    splitLegalToLeaves_callsOk target t ys _ fun _ =>
      packLeavesToWords64_callsOk target t _ _ fun _ =>
        packLeavesToWords64_callsOk target t _ _ fun _ =>
          legalSimdScalar128_goWords_callsOk target on128 hon t k hk _ _ []

private theorem legalShufd_callsOk (imm : BitVec 8) :
    ∀ (t : Ty) (xs : Tup (Arg (fun _ => Unit)) (target.legalTys t))
      (k : Tup (Arg (fun _ => Unit)) (target.legalTys t) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (legalShufd target imm t xs k).callsOk allowed exits
  | t, xs, k, hk => by
    unfold legalShufd
    split
    · trivial
    · cases t with
      | bool | bits _ | float _ =>
        exact legalSimdScalar128_callsOk target _ (fun _ _ _ _ _ _ _ _ _ hc => hc _ _ _ _)
          _ xs xs k hk
      | pair a b =>
        dsimp only; split
        · split
          · exact hk _
          · exact legalSimdScalar128_callsOk target _ (fun _ _ _ _ _ _ _ _ _ hc => hc _ _ _ _)
              (.pair a b) xs xs k hk
        · split
          · exact legalShufd_callsOk imm a _ _ fun _ =>
              legalShufd_callsOk imm b _ _ fun _ => hk _
          · exact legalSimdScalar128_callsOk target _ (fun _ _ _ _ _ _ _ _ _ hc => hc _ _ _ _)
              (.pair a b) xs xs k hk

private theorem legalBlendw_callsOk (imm : BitVec 8) :
    ∀ (t : Ty) (xs ys : Tup (Arg (fun _ => Unit)) (target.legalTys t))
      (k : Tup (Arg (fun _ => Unit)) (target.legalTys t) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (legalBlendw target imm t xs ys k).callsOk allowed exits
  | t, xs, ys, k, hk => by
    unfold legalBlendw
    split
    · trivial
    · cases t with
      | bool | bits _ | float _ =>
        exact legalSimdScalar128_callsOk target _
          (fun _ _ _ _ _ _ _ _ _ hc => scalarBlendw128_callsOk hc) _ xs ys k hk
      | pair a b =>
        dsimp only; split
        · split
          · exact hk _
          · exact legalSimdScalar128_callsOk target _
              (fun _ _ _ _ _ _ _ _ _ hc => scalarBlendw128_callsOk hc) (.pair a b) xs ys k hk
        · split
          · exact legalBlendw_callsOk imm a _ _ _ fun _ =>
              legalBlendw_callsOk imm b _ _ _ fun _ => hk _
          · exact legalSimdScalar128_callsOk target _
              (fun _ _ _ _ _ _ _ _ _ hc => scalarBlendw128_callsOk hc) (.pair a b) xs ys k hk

private theorem legalAlignr_callsOk (imm : BitVec 8) :
    ∀ (t : Ty) (xs ys : Tup (Arg (fun _ => Unit)) (target.legalTys t))
      (k : Tup (Arg (fun _ => Unit)) (target.legalTys t) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (legalAlignr target imm t xs ys k).callsOk allowed exits
  | t, xs, ys, k, hk => by
    unfold legalAlignr
    split
    · trivial
    · cases t with
      | bool | bits _ | float _ =>
        exact legalSimdScalar128_callsOk target _
          (fun _ _ _ _ _ _ _ _ _ hc => scalarAlignr128_callsOk hc) _ xs ys k hk
      | pair a b =>
        dsimp only; split
        · split
          · exact hk _
          · exact legalSimdScalar128_callsOk target _
              (fun _ _ _ _ _ _ _ _ _ hc => scalarAlignr128_callsOk hc) (.pair a b) xs ys k hk
        · split
          · exact legalAlignr_callsOk imm a _ _ _ fun _ =>
              legalAlignr_callsOk imm b _ _ _ fun _ => hk _
          · exact legalSimdScalar128_callsOk target _
              (fun _ _ _ _ _ _ _ _ _ hc => scalarAlignr128_callsOk hc) (.pair a b) xs ys k hk

private theorem legalShufb_callsOk :
    ∀ (t : Ty) (xs ys : Tup (Arg (fun _ => Unit)) (target.legalTys t))
      (k : Tup (Arg (fun _ => Unit)) (target.legalTys t) →
        Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (legalShufb target t xs ys k).callsOk allowed exits
  | t, xs, ys, k, hk => by
    unfold legalShufb
    split
    · trivial
    · cases t with
      | bool | bits _ | float _ =>
        exact legalSimdScalar128_callsOk target _
          (fun _ _ _ _ _ _ _ _ _ hc => scalarShufb128_callsOk hc) _ xs ys k hk
      | pair a b =>
        dsimp only; split
        · split
          · exact hk _
          · exact legalSimdScalar128_callsOk target _
              (fun _ _ _ _ _ _ _ _ _ hc => scalarShufb128_callsOk hc) (.pair a b) xs ys k hk
        · split
          · exact legalShufb_callsOk a _ _ _ fun _ =>
              legalShufb_callsOk b _ _ _ fun _ => hk _
          · exact legalSimdScalar128_callsOk target _
              (fun _ _ _ _ _ _ _ _ _ hc => scalarShufb128_callsOk hc) (.pair a b) xs ys k hk

private theorem legalFloatBit2_callsOk
    (mkOp : (w : Nat) → OpCode [.bits w, .bits w] [.bits w])
    (mkFOp : (f : Fmt) → OpCode [.float f, .float f] [.float f])
    (f : Fmt) (x y : Arg (fun _ => Unit) (.float f))
    (k : Arg (fun _ => Unit) (.float f) → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ r, (k r).callsOk allowed exits) :
    (legalFloatBit2 target mkOp mkFOp f x y k).callsOk allowed exits := by
  unfold legalFloatBit2; solve_calls_cps hk

end TreeCalls

/-- `legalOp` introduces no `.call` or `.exit` instructions outside continuation `k`. -/
theorem legalOp_callsOk (target : LegalTarget) {allowed : List SigEntry} {exits : List Sym}
    {outRs rs' : List Ty} (op : Op (LVar target (fun _ => Unit)) rs')
    (k : Tup (LVar target (fun _ => Unit)) rs' → Expr (fun _ => Unit) (fun _ => Unit) outRs)
    (hk : ∀ res, (k res).callsOk allowed exits) :
    (legalOp target op k).callsOk allowed exits := by
  rcases op with ⟨code, args⟩
  cases code with
  | copy => exact hk _
  | add t | sub t | mul t =>
    dsimp only [legalOp]
    split
    · trivial
    · refine legalBinTree_callsOk target _ _ _ ?_ ?_ ?_ t _ _ none _ fun _ => hk _
      · intro _ _ _ h; dsimp only [Expr.callsOk]; exact h _
      · intro n _ _ _ h; exact legalBitsArith_callsOk target n _ _ _ _ h
      · intro _ _ _ _ _; trivial
  | neg t =>
    dsimp only [legalOp]
    split
    · trivial
    · refine legalUnaryTree_callsOk target _ _ ?_ ?_ ?_ t _ _ fun _ => hk _
      · intro _ _ h; exact h _
      · intro n _ _ h; split
        · exact h _
        · try dsimp only [Expr.callsOk]
          exact emitMaskToN_callsOk h
      · intro _ _ _ _; trivial
  | and t | or t | xor t =>
    dsimp only [legalOp]
    refine legalBinTree_callsOk target _ _ _ ?_ ?_ ?_ t _ _ none _ fun _ => hk _
    · intro _ _ _ h; dsimp only [Expr.callsOk]; exact h _
    · intro n _ _ _ h; exact legalBitsArith_callsOk target n _ _ _ _ h
    · intro f _ _ _ h; exact legalFloatBit2_callsOk target _ _ f _ _ _ h
  | not t =>
    dsimp only [legalOp]
    refine legalUnaryTree_callsOk target _ _ ?_ ?_ ?_ t _ _ fun _ => hk _
    · intro _ _ h; dsimp only [Expr.callsOk]; exact h _
    · intro n _ _ h; split
      · exact h _
      · split
        · try dsimp only [Expr.callsOk]
          exact h _
        · try dsimp only [Expr.callsOk]
          exact emitMaskToN_callsOk h
    · intro f _ _ h; split
      · dsimp only [Expr.callsOk]; exact h _
      · try dsimp only [Expr.callsOk]
        exact h _
  | ternlog t imm =>
    dsimp only [legalOp]
    refine legalTernaryTree_callsOk target _ _ ?_ ?_ ?_ t _ _ _ _ fun _ => hk _
    · intro _ _ _ _ h; exact emitTernlogBool_callsOk h
    · intro n _ _ _ _ h; split
      · exact h _
      · split
        · try dsimp only [Expr.callsOk]
          exact emitMaskToN_callsOk h
        · exact emitTernlogBits_callsOk fun _ => emitMaskToN_callsOk h
    · intro f _ _ _ _ h; split
      · dsimp only [Expr.callsOk]; exact h _
      · try dsimp only [Expr.callsOk]; split
        · try dsimp only [Expr.callsOk]
          exact h _
        · exact emitTernlogBits_callsOk fun _ => by dsimp only [Expr.callsOk]; exact h _
  | shl t | lshr t | ashr t | rotl t | rotr t =>
    dsimp only [legalOp]
    split
    · trivial
    · refine legalBinTree_callsOk target _ _ _ ?_ ?_ ?_ t _ _ (some _) _ fun _ => hk _
      · intro _ _ _ h; exact h _
      · intro n _ _ _ h; exact legalBitsArith_callsOk target n _ _ _ _ h
      · intro _ _ _ _ _; trivial
  | fshl n | fshr n =>
    dsimp only [legalOp]; solve_legal_cps hk
  | bswap t =>
    dsimp only [legalOp]
    exact legalBswapTree_callsOk target t _ _ fun _ => hk _
  | clz n | cls n | rbit n | ctz n | popcnt n =>
    dsimp only [legalOp]; solve_legal_cps hk
  | udiv n | urem n | sdiv n | srem n | udiv0 n | sdiv0 n =>
    dsimp only [legalOp]; solve_legal_cps hk
  | addc n | subb n | umulw n | smulw n =>
    dsimp only [legalOp]; solve_legal_cps hk
  | fneg _ | fabs _ | fsqrt _ =>
    dsimp only [legalOp]; split
    · trivial
    · refine legalUnaryTree_callsOk target _ _ ?_ ?_ ?_ _ _ _ fun _ => hk _
      · intro _ _ _; trivial
      · intro _ _ _ _; trivial
      · intro _ _ _ h; try dsimp only [Expr.callsOk]; exact h _
  | fadd _ | fsub _ | fmul _ | fdiv _ =>
    dsimp only [legalOp]; split
    · trivial
    · refine legalBinTree_callsOk target _ _ _ ?_ ?_ ?_ _ _ _ none _ fun _ => hk _
      · intro _ _ _ _; trivial
      · intro _ _ _ _ _; trivial
      · intro _ _ _ _ h; try dsimp only [Expr.callsOk]; exact h _
  | ffma _ =>
    dsimp only [legalOp]; split
    · trivial
    · refine legalTernaryTree_callsOk target _ _ ?_ ?_ ?_ _ _ _ _ _ fun _ => hk _
      · intro _ _ _ _ _; trivial
      · intro _ _ _ _ _ _; trivial
      · intro _ _ _ _ _ h; try dsimp only [Expr.callsOk]; exact h _
  | cmp o t =>
    dsimp only [legalOp]; split
    · trivial
    · exact legalCmpTree_callsOk target o t _ _ _ fun _ => hk _
  | fcmp o t =>
    dsimp only [legalOp]; split
    · trivial
    · exact legalFCmpTree_callsOk target o t _ _ _ fun _ => hk _
  | select t =>
    dsimp only [legalOp]
    exact legalSelectTree_callsOk target _ t _ _ _ fun _ => hk _
  | blend t =>
    dsimp only [legalOp]
    exact legalBlendTree_callsOk target t _ _ _ _ fun _ => hk _
  | sext n m | zext n m | trunc n m | ofBool n =>
    dsimp only [legalOp]; solve_legal_cps hk
  | fptoui _ _ | fptosi _ _ | uitofp _ _ | sitofp _ _ | fcvt _ _ =>
    dsimp only [legalOp]; solve_legal_cps hk
  | bitcast s d _ =>
    dsimp only [legalOp]
    have hslow : ∀ la,
        (splitLegalToLeaves target s la fun fx =>
          packLeavesToWords64 target s fx fun words =>
            unpackWords64ToLeaves target words 0 d fun fu =>
              packLeavesToLegal target d fu fun res => k (res, ())).callsOk allowed exits :=
      fun _ =>
        splitLegalToLeaves_callsOk target s _ _ fun _ =>
          packLeavesToWords64_callsOk target s _ _ fun _ =>
            unpackWords64ToLeaves_callsOk target _ 0 d _ fun _ =>
              packLeavesToLegal_callsOk target d _ _ fun _ => hk _
    repeat' (first
      | exact hslow _
      | exact hk _
      | (dsimp only [Expr.callsOk]; exact hk _)
      | split)
  | mkpair a b =>
    dsimp only [legalOp]; split
    · exact packFromLegal_callsOk target a _ _ fun _ =>
        packFromLegal_callsOk target b _ _ fun _ => by dsimp only [Expr.callsOk]; exact hk _
    · exact hk _
  | unpair a b =>
    dsimp only [legalOp]; split
    · split
      · exact hk _
      · dsimp only [Expr.callsOk]
        exact unpackToLegal_callsOk target a _ _ fun _ =>
          unpackToLegal_callsOk target b _ _ fun _ => hk _
    · exact hk _
  | shufd t imm =>
    dsimp only [legalOp]
    exact legalShufd_callsOk target imm t _ _ fun _ => hk _
  | blendw t imm =>
    dsimp only [legalOp]
    exact legalBlendw_callsOk target imm t _ _ _ fun _ => hk _
  | alignr t imm =>
    dsimp only [legalOp]
    exact legalAlignr_callsOk target imm t _ _ _ fun _ => hk _
  | shufb t =>
    dsimp only [legalOp]
    exact legalShufb_callsOk target t _ _ _ fun _ => hk _
  | sha256rnds2 =>
    dsimp only [legalOp]; split
    · dsimp only [Expr.callsOk]; exact hk _
    · exact splitLegalToLeaves_callsOk target _ _ _ fun _ =>
        splitLegalToLeaves_callsOk target _ _ _ fun _ =>
          splitLegalToLeaves_callsOk target _ _ _ fun _ =>
            packLeavesToWords64_callsOk target _ _ _ fun _ =>
              packLeavesToWords64_callsOk target _ _ _ fun _ =>
                packLeavesToWords64_callsOk target _ _ _ fun _ =>
                  words2ToDwords4_callsOk fun _ _ _ _ =>
                    words2ToDwords4_callsOk fun _ _ _ _ =>
                      words2ToDwords4_callsOk fun _ _ _ _ =>
                        scalarSha256rnds2_callsOk fun _ _ _ _ =>
                          dwords4ToWords2_callsOk fun _ _ =>
                            unpackWords64ToLeaves_callsOk target _ 0 _ _ fun _ =>
                              packLeavesToLegal_callsOk target _ _ _ fun _ => hk _
  | sha256msg1 =>
    dsimp only [legalOp]; split
    · dsimp only [Expr.callsOk]; exact hk _
    · exact splitLegalToLeaves_callsOk target _ _ _ fun _ =>
        splitLegalToLeaves_callsOk target _ _ _ fun _ =>
          packLeavesToWords64_callsOk target _ _ _ fun _ =>
            packLeavesToWords64_callsOk target _ _ _ fun _ =>
              words2ToDwords4_callsOk fun _ _ _ _ =>
                words2ToDwords4_callsOk fun _ _ _ _ =>
                  scalarSha256msg1_callsOk fun _ _ _ _ =>
                    dwords4ToWords2_callsOk fun _ _ =>
                      unpackWords64ToLeaves_callsOk target _ 0 _ _ fun _ =>
                        packLeavesToLegal_callsOk target _ _ _ fun _ => hk _
  | sha256msg2 =>
    dsimp only [legalOp]; split
    · dsimp only [Expr.callsOk]; exact hk _
    · exact splitLegalToLeaves_callsOk target _ _ _ fun _ =>
        splitLegalToLeaves_callsOk target _ _ _ fun _ =>
          packLeavesToWords64_callsOk target _ _ _ fun _ =>
            packLeavesToWords64_callsOk target _ _ _ fun _ =>
              words2ToDwords4_callsOk fun _ _ _ _ =>
                words2ToDwords4_callsOk fun _ _ _ _ =>
                  scalarSha256msg2_callsOk fun _ _ _ _ =>
                    dwords4ToWords2_callsOk fun _ _ =>
                      unpackWords64ToLeaves_callsOk target _ 0 _ _ fun _ =>
                        packLeavesToLegal_callsOk target _ _ _ fun _ => hk _

/-- `legalLoad` introduces no `.call` or `.exit` instructions outside continuation `k`. -/
theorem legalLoad_callsOk (target : LegalTarget) {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} :
    ∀ (t : Ty) (ptr : Arg (fun _ => Unit) i64)
      (k : LVar target (fun _ => Unit) t → Expr (fun _ => Unit) (fun _ => Unit) rs),
      (∀ res, (k res).callsOk allowed exits) →
      (legalLoad target t ptr k).callsOk allowed exits
  | .bool, _, k, hk => hk _
  | .bits n, ptr, k, hk => by
    dsimp only [legalLoad]; split
    · exact hk _
    · exact emitLoadBits_callsOk target.bitWidths n _ ptr _ fun r => hk (r, ())
  | .float _, _, k, hk => hk _
  | .pair a b, ptr, k, hk => by
    dsimp only [legalLoad]
    split
    · exact hk _
    · split
      · refine legalLoad_callsOk target a ptr _ fun _ => ?_
        try dsimp only
        split
        · exact legalLoad_callsOk target b ptr _ fun _ => hk _
        · dsimp only [Expr.callsOk]
          exact legalLoad_callsOk target b _ _ fun _ => hk _
      · split
        · exact unpackWords64ToLeaves_callsOk target [] 0 (.pair a b) _ fun _ =>
            packLeavesToLegal_callsOk target (.pair a b) _ k hk
        · exact loadByteChunksToWords64_callsOk ptr 0 _ [] (.imm 0#64) 0 _ fun _ =>
            unpackWords64ToLeaves_callsOk target _ 0 (.pair a b) _ fun _ =>
              packLeavesToLegal_callsOk target (.pair a b) _ k hk

/-- `legalStore` introduces no `.call` or `.exit` instructions outside continuation `k`. -/
theorem legalStore_callsOk (target : LegalTarget) {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} :
    ∀ (t : Ty) (v : LVar target (fun _ => Unit) t) (ptr : Arg (fun _ => Unit) i64)
      (k : Expr (fun _ => Unit) (fun _ => Unit) rs),
      k.callsOk allowed exits →
      (legalStore target t v ptr k).callsOk allowed exits
  | .bool, (_, ()), _, k, hk => hk
  | .bits n, (_, ()), ptr, k, hk => by
    dsimp only [legalStore]; split
    · exact hk
    · exact emitStoreBits_callsOk target.bitWidths n _ _ ptr k hk
  | .float _, (_, ()), _, k, hk => hk
  | .pair a b, xs, ptr, k, hk => by
    dsimp only [legalStore]
    split
    · exact hk
    · split
      · refine legalStore_callsOk target a _ ptr _ ?_
        split
        · exact legalStore_callsOk target b _ ptr k hk
        · exact legalStore_callsOk target b _ _ k hk
      · split
        · exact hk
        · exact splitLegalToLeaves_callsOk target (.pair a b) xs _ fun _ =>
            packLeavesToWords64_callsOk target (.pair a b) _ _ fun _ =>
              storeByteChunksFromWords64_callsOk _ ptr 0 _ k hk

private theorem tup_units_gen_eq {α : Type} :
    ∀ {ts : List α} (xs : Tup (fun _ => Unit) ts), xs = Tup.units ts
  | [], () => rfl
  | _ :: _, ((), rest) => congrArg ((), ·) (tup_units_gen_eq rest)

private theorem legalBlocks_callsOk_aux (target : LegalTarget) {allowed : List SigEntry}
    {exits : List Sym} {rs : List Ty} :
    ∀ {sig : List (List Ty)}
      (b : Blocks (LVar target (fun _ => Unit)) (LLab target (fun _ => Unit)) rs sig),
      (∀ {ts} (i : Member ts sig) (ys : Tup (fun _ => Unit) (target.legalSig ts)),
        (legalExpr target (b.get i (splitParams target ts ys))).callsOk
          (allowed.map (sigEntryLegal target)) exits) →
      (legalBlocks target b).callsOk (allowed.map (sigEntryLegal target)) exits
  | [], .nil, _ => trivial
  | _ :: _, .cons _ _, h => by
    dsimp only [legalBlocks, Blocks.callsOk]
    exact ⟨h .here (Tup.units _), legalBlocks_callsOk_aux target _ fun i => h (.there i)⟩

/-- `legalExpr` maps every callee signature in `e` through `sigEntryLegal target` and preserves
`exits`. -/
theorem legalExpr_callsOk (target : LegalTarget) {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty}
    {G : Ctx (LVar target (fun _ => Unit)) (fun _ => Unit)}
    {D : Ctx (LLab target (fun _ => Unit)) (fun _ => Unit)}
    {e₁ : Expr (LVar target (fun _ => Unit)) (LLab target (fun _ => Unit)) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    e₂.callsOk allowed exits →
    (legalExpr target e₁).callsOk (allowed.map (sigEntryLegal target)) exits := by
  induction hwf using Wf.induct with
  | let_ _ _ ih =>
    intro hc
    dsimp only [legalExpr]
    exact legalOp_callsOk target _ _ fun res => ih res (Tup.units _) hc
  | load t _ _ ih =>
    intro hc
    dsimp only [legalExpr]
    split
    · exact legalLoad_callsOk target t _ _ fun res => ih res () hc
    · trivial
  | store _ _ _ ih =>
    intro hc
    dsimp only [legalExpr]
    split
    · exact legalStore_callsOk target _ _ _ _ (ih hc)
    · trivial
  | call f _ _ ih =>
    intro ⟨hmem, hc⟩
    dsimp only [legalExpr, Expr.callsOk]
    exact ⟨List.mem_map.mpr ⟨(f, _, _), hmem, rfl⟩, ih _ (Tup.units _) hc⟩
  | jnz _ _ _ iht ihe =>
    intro ⟨ht, he⟩
    dsimp only [legalExpr, Expr.callsOk]
    exact ⟨iht ht, ihe he⟩
  | jump _ _ => intro _; trivial
  | ret _ => intro _; trivial
  | exit f _ =>
    intro hf
    dsimp only [legalExpr, Expr.callsOk]
    exact hf
  | hlt => intro _; trivial
  | @group _ _ sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro ⟨hb, hk⟩
    dsimp only [legalExpr, Expr.callsOk]
    refine ⟨legalBlocks_callsOk_aux target _ fun i ys => ?_,
      ihk (tupLiftMap target.legalSig _ (Tup.units _)) (Tup.units _) ?_⟩
    · exact ihb (tupLiftMap target.legalSig _ (Tup.units _)) (Tup.units _) i _ (Tup.units _)
        (by rw [tup_units_gen_eq (Tup.units _)]; exact Blocks.callsOk_get hb i)
    · rw [tup_units_gen_eq (Tup.units _)] at hk
      exact hk

/-- Closed-function `callsOk` preservation for `Func.legal`. -/
theorem Func.legal_callsOk (target : LegalTarget) {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.legal target f) (fun _ => Unit) (fun _ => Unit)
      (Tup.units (target.legalSig as))).callsOk
      (allowed.map (sigEntryLegal target)) exits := by
  exact legalExpr_callsOk target
    (hf (LVar target (fun _ => Unit)) (fun _ => Unit) (LLab target (fun _ => Unit))
      (fun _ => Unit) (splitParams target as (Tup.units _)) (Tup.units as))
    hc

end LeanQbe.T
