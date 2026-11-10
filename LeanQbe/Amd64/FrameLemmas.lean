module

public import LeanQbe.Amd64.TargLemmas

/-!
# x64 step lemmas for the frame directives

The lemmas (written by memframe) now live in `TargLemmas.lean`, because the `Target` instance needs
them. This module re-exports `TargLemmas` so that existing imports keep working.
-/
