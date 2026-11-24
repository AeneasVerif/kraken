# Guidelines

## Code

- **No dead code.** All features, semantics, theorems, and definitions should be
  used either directly or by an example or test.
- **No defensive code.** If something is wrong (e.g. semantics added without
  extending the parsers, or malformed semantics that break fuzzing), it should
  fail loudly rather than be silently caught.

## Definitions, theorems, and proofs

- **Encapsulate complexity.** Unless necessary for automation, all definitions
  and theorems should encapsulate some data or proof complexity; do not add
  theorems with one-line rewrite proofs or similar.
- **Write resilient proofs.** Avoid scattering `have` statements across proofs,
  since they are brittle to changes in the theorem statement. In general, prefer
  backwards reasoning over forwards reasoning when it avoids spelling out
  intermediate steps. More generally, keep proofs resilient to change as long as
  this does not overly hurt performance (e.g. using non-terminal `simp only`,
  terminal `simp`, or `grind`).

## Tests, examples, and CI

- **Follow unit-test format.** Most tests and example proofs should test one
  thing, make clear what they test, and, if they fail, make clear why. This
  applies both to tests and to examples showing how to prove a particular kind
  of program (e.g. proving a jump), which themselves act as tests.
- **Keep CI deterministic.** Everything that runs in CI must either clearly pass
  or clearly fail. Do not add random functions, flaky tests, or tests or
  examples that can change due to unrelated changes.

## Pull requests

- **Keep PRs small.** Write small PRs when possible and split large changes into
  chains. This makes reviews faster and more reliable, and gets code merged
  faster.
