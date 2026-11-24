module

import Kraken.X64.Parser
import Kraken.X64.Semantics

/-!
Definitional-equality tests for `Layout.offset`: for concrete programs and an arbitrary layout, the
addresses of a prefix laid out with `l` and of a suffix laid out with `l.offset p₁` are
definitionally the addresses of the same directives in the whole program. Each test must be closed
by `rfl` within the default heartbeat budget.
-/

open Kraken (Layout)

private def ev : Program := ⸨prog|
even:
  test %rdi, %rdi
  jz even_zero
  dec %rdi
  call odd
  ret
even_zero:
  mov $1, %rax
  ret
⸩

private def od : Program := ⸨prog|
odd:
  test %rdi, %rdi
  jz odd_zero
  dec %rdi
  call even
  ret
odd_zero:
  mov $0, %rax
  ret
⸩

variable (l : Layout)

/-- Prefix: an address inside `ev`. -/
example : (l.apply (ev ++ od)).addrOf 3 = (l.apply ev).addrOf 3 := rfl

/-- Prefix: the end of `ev`. -/
example : (l.apply (ev ++ od)).addrOf 9 = (l.apply ev).addrOf ev.length := rfl

/-- Suffix: the start of `od`. -/
example : (l.apply (ev ++ od)).addrOf 9 = ((l.offset ev).apply od).addrOf 0 := rfl

/-- Suffix: an address inside `od`. -/
example : (l.apply (ev ++ od)).addrOf (9 + 3) = ((l.offset ev).apply od).addrOf 3 := rfl

/-- Suffix: the end of `od`. -/
example : (l.apply (ev ++ od)).addrOf 18 = ((l.offset ev).apply od).addrOf od.length := rfl

/-- Offsets compose. -/
example : (l.offset ev).offset od = l.offset (ev ++ od) := rfl

/-- The empty offset is the identity. -/
example : l.offset ([] : Program) = l := rfl
