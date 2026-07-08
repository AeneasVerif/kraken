import KrakenStdlibCandidates

def val130 (low mid high : UInt64) : Int :=
  low.toBitVec.unsigned + (mid.toBitVec.unsigned <<< 64) + ((high.toBitVec.unsigned &&& 7) <<< 128)

/--
Representative standalone test isolating the exact 3-word (130-bit) add-with-carry chain
from `poly_add` in `poly1305_x86_64.lean`.
Note on automation: because `c1` contains a compound `∨` (`Or`) conditional inside an `if` (`ite`),
`grind` cannot automatically case-split `c1` even when passed `grind (config := { lax := true, splits := 20 })`
due to E-graph `instDecidableOr` canonicalization checks (`failed to canonicalize instance instDecidableOr`).
Therefore, manual boolean splitting on the carry flags (`by_cases hc0` and `by_cases hc1`) right before `grind`
is currently required to bridge the equational overflow wraps.
-/
example (r8 r9 r10 mem0 mem1 : UInt64)
    (h_r10 : r10.toBitVec.unsigned ≤ 4) :
    let s_r8  := r8 + mem0
    let c0    := if s_r8 < r8 then 1#64 else 0#64
    let s_r9  := r9 + mem1 + UInt64.ofBitVec c0
    let c1    := if (s_r9 < r9) ∨ (s_r9 == r9 ∧ c0 == 1#64) then 1#64 else 0#64
    let s_r10 := r10 + 1 + UInt64.ofBitVec c1
    val130 s_r8 s_r9 s_r10 =
    val130 r8 r9 r10 + mem0.toBitVec.unsigned + (mem1.toBitVec.unsigned * 2^64) + 2^128 := by
  intro s_r8 c0 s_r9 c1 s_r10
  dsimp only [val130, s_r8, s_r9, s_r10]
  -- Manual carry bit splits are required because grind.cases cannot split compound DecidableOr conditionals:
  by_cases hc0 : c0 = 1#64 <;> by_cases hc1 : c1 = 1#64 <;> grind
