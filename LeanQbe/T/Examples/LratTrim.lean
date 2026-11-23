module

public import LeanQbe.T.Notation
public import LeanQbe.T.Module
public import LeanQbe.T.Examples.LratTrimProg

/-!
# The `lrat-trim` Kernel in Typed `LeanQbe.T` (`tqbe`) Notation

Non-proof typed-IR transliteration of the `lrat-trim` kernel into
`LeanQbe.T.Func` / `LeanQbe.T.Module`:

* `checkRup` (`br_check_clause_non_strictly_by_propagation`)
* `strictCheck` (`br_check_clause_strictly_by_resolution`)
* `checkClause` (`br_check_clause`)
* `checkProof` (`br_check_proof`)
* `trimProof` (`br_trim_proof`)

Low-32 `jnz` tests are translated explicitly into `.bool` (`:b`) conditions via
`cnew` / `cnel` against `0`, and boolean loop flags (`%first`, `%used`, `%wu`, `%io`, `%orig`)
are typed natively as `.bool`.

Kernel state layout at `%st` (64-bit pointer / integer fields unless noted):
* `+0`: `used_begin` (`int32_t*`)
* `+8`: `antecedents_begin` (`int32_t**`)
* `+16`: `literals_begin` (`int32_t**`)
* `+24`: `values_begin` (`int8_t*`)
* `+32`: `marks_begin` (`int8_t*`)
* `+40`: `trail_begin` (`int32_t*`)
* `+48`: `trail_end` (`int32_t*`)
* `+56`: `worklist_begin` (`int32_t*`)
* `+64`: `empty_clause` (`int32_t` in low 32 bits)
* `+72`: `first_proof_id` (`int32_t` in low 32 bits)
* `+80`: `strict` (`uint64_t`)
* `+88`: `trimming` (`uint64_t`)
* `+96`: `checking` (`uint64_t`)
* `+104`: `forward` (`uint64_t`)
* `+112`: `stat_trivial_cnf` (`uint64_t`)
* `+120`: `stat_trivial_proof` (`uint64_t`)
* `+128`: `stat_total` (`uint64_t`)
* `+136`: `stat_complete` (`uint64_t`)
* `+144`: `stat_resolved` (`uint64_t`)
* `+152`: `stat_lit_assigned` (`uint64_t`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.LratTrim

open LeanQbe.T

/-- Typed module for the `lrat-trim` kernel with abnormal exit `lrat_fail`. -/
def lratTrimModule : LeanQbe.T.Module :=
  { fns := lratTrimFns, externs := [], exits := ["lrat_fail"] }

end LeanQbe.T.Examples.LratTrim

end
