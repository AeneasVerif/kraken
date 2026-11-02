# Notes on developing in Kraken

## Helper lemmas

Developers will oftentimes want to state helper lemmas (e.g. about common data
structures like sets or maps), in the course of authoring a main lemma. The
guidelines are as follows:
- to begin with, the helper lemma ought to be marked as `private`, and live in the same
  file as the main lemma
- should the need for this helper lemma arise in multiple places in the
  codebase, rather than have a large amount of copies of this lemma, a PR should
  move the lemma to StdLibCandidates with a review, to ensure the lemma is
  stated in a way that is general enough
- we should then try to upstream the lemmas we have in StdLibCandidates on a
  regular basis.

## Main lemmas

Main lemmas are *not* marked private and are assigned to the file that makes the
most sense: `Mem.lean` (memory), `SeparationMem.lean` (separation view of the
memory), `Separation.lean` (separating star and other connectives).
