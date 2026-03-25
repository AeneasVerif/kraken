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
