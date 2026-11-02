# Contributing

## Reviewing semantics

All changes to semantics should be thoroughly checked against the [Intel SDM](https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-2b-manual.pdf)
by two maintainers.
As a maintainer proposing a change,
please review your own edits
and flag TODOs for anything not corroborated by an authoritative reference.

Here are some common but easy-to-forget considerations to look out for:

- Some operations have multiple outputs.
  All effects observable through modeled state need to be captured correctly.
- Outputs may be implicit (not apparent from the syntax),
  for example to flag registers or for the high half of a wide output.
- Multiple destinations of the same kind (e.g. registers or memory),
  if one or more of these is selectable,
  we need a decision about which write wins if the same destination is selected
- For operations that write to registers and memory,
  do the writes to registers affect the calculation of the destination address?
- When accessing memory, what width is used for address computations?
- For control instructions, what width is used for code-address computations?
- When computing an operation on different-width inputs,
  is the shorter one sign-extended or zero-extended?
- When computing immediates during assembly,
  is there overflow, at what width, and is it signed or unsigned?
- Can the instruction trap, or raise an exception, or fault?

Please also flag any aspects of a change or issue that you are not confident about.

## Automatically generated content

Use of automated tooling to generate code or text must be disclosed fully and specifically:
describe the workflow used and which parts of the change it produced (briefly if possible).
Generated prose must be explicitly marked, so no reader has to guess whether text is human or machine.

- In **GitHub text** (PR descriptions, review/issue comments),
  wrap generated text in a `<details>` block:

      <details>
      <summary>generated explanation</summary>
      This test used to fail because foo ate the bar.
      </details>

- Generated **source-code comments** can be added by exception only.
  Prefer a human summary of the context and references needed to regenerate the longer comment.
  Any exception must be specifically requested during code review.

Authors must review, understand, and be ready to defend every change themselves before opening a PR.
A human reply must get a human reply; automated review/issue conversation is not allowed.

Be especially wary of machine-generated abstractions and definition factoring.
Prefer to check in a more pedestrian, concrete approach first,
and introduce the abstraction only once the right interface is clear to humans.

For informative context, see [Chromium AI Coding Policy](https://chromium.googlesource.com/chromium/src/+/main/agents/ai_policy.md), [Contributing to mathlib](https://leanprover-community.github.io/contribute/index.html), [Kaashoek & Zeldovich xv6-AI § 9](https://arxiv.org/abs/2609.04043)
