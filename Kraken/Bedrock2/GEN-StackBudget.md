# Stack budget for `Exec` (prototype)

`Exec ext e B c t m l post` carries a stack budget `B : Nat`. `stackalloc x n body` requires
`n ≤ B` and runs `body` with budget `B - n`; all other rules pass `B` unchanged, and `call` hands
the caller's current budget to the callee. Stack addresses are still universally quantified.

Without the budget, a `stackalloc` for which no disjoint `(a, mStack)` exists (address-space
exhaustion) has a vacuous premise, so `Exec … (fun _ _ _ => False)` was derivable. With the
budget, `NonVacuity.lean` proves that a derivation is never vacuous when `B` free bytes are
available:

- `Exec.exists_post_of_freeBlock` / `Exec.nonvacuous`: given `ExtSpec.Responsive ext` and a free
  block of `B` bytes, some final state satisfies `post`.
- `Exec.nonvacuous_of_empty`: `m = ∅` and `B < 2 ^ w` suffice.
- `Exec.nonvacuous_of_size`: `(m.size + 1) * (B + 1) ≤ 2 ^ w` suffices (pigeonhole).
- `Exec.exists_run_of_block`: given a `Handler` that is `Ok` and `Complete` for `ext`, the
  interpreter `run` succeeds on an oracle whose addresses are non-null and lie inside the block
  (a downward-growing packed stack), and its result satisfies `post`.

The budget counts only `stackalloc` bytes, not call frames, spills or alignment padding; a
compiler has to reserve those separately.
