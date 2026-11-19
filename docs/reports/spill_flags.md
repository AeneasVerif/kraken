# Spill Flag & Variant Allocator Upgrade (`Spill.lean`)

Forked from `main @ 2a28b05` (non-proof heuristic track — 0 proof files modified).

## 1. Summary of Changes

Upgraded the untrusted flag/variant allocator in `LeanQbe/T/Spill.lean` (`800` LOC, `≤ 800` cap) and removed `Patch` / `patchHints` / `patchAdcxAdox` / `patchCfLoop` from `LeanQbeTest/T/RegaLitmusProgs.lean` so all 13 `G12` litmus programs lower via unpatched `Spill.hints`:

1. **Multi-op & multi-consumer flag webs (`scanDefs`, `scanRanges`, `tryColorWeb`)**:
   - Replaced the single-instruction `localOnly` check with exact live-range tracking over `Tree` (`liveIn`, `liveAfter`, `varLiveIps`, `usesOf`), supporting `.cmp`, `.addc`, and `.subb` `.bool` outputs across multi-op gaps (e.g., `mul4x4`'s `umulw`s, `addMod25519`'s 4 `select`s) and dead final carry-outs (`_c2` in `fnAdcChain`, final carries in `Bignum.mulRow0K`/`mulRowAccK`).
   - Rejects flag allocation when a `.bool` variable crosses a `.call` or has any incompatible consumer (e.g. `.store .bool`, `.xor .bool`, or an intervening clobber that cannot be avoided).
2. **Interleaved dual-chain coloring & hoisted `clearFlags` (`probeIntervening`, `placeOrHoistClear`)**:
   - Models interference among concurrent flag webs via `FlagMask.disjoint (I.gpr.condReads c₁) (I.gpr.condReads c₂)` and checks every instruction strictly inside each web's live range against `clob`.
   - When concurrent `cin = .imm false` chains or overlapping webs share a region (`hoistBlocked`), prefers clobber-minimal variants (`.adcx`, `.adox`) over `.default` and hoists `PreStep.clearFlags` to the latest flag-free anchor (`anchorOf`) whose path preserves the target flag, allowing a single `clearFlags` to seed both `CF` and `OF` without clobbering an already-live chain.
3. **Clobber-avoiding `VariantHint` promotion (`altVariantsFor`, `probeIntervening`)**:
   - Probes `.mulxFast` on `.umulw`, `.disp off` / `.disp (-off)` and `.decInc` on `.add`/`.sub`, and `.decInc` (`tstz`) on `.cmp` whenever `.default` clobbers a concurrently live flag or a hoisted `clearFlags` value.
4. **Loop-carried `.flag` block parameters (`ufFind`, `immFalseJumps`, `emitAlloc`)**:
   - Unions `.bool` block parameters with incoming `.var` jump arguments and colors block-parameter webs first, verifying `clearFlags` placement on incoming `.imm false` jump edges and propagating `clrAt` in `emitAlloc` for all `Tree` nodes (including `.jump`).

## 2. Before / After Metrics

### `G12d` Litmus Programs (`RegaLitmus.isa`, unpatched `Spill.hints`)

| Program | Before (instrs / `setcc` / `bt0`) | After (instrs / `setcc` / `bt0`) | Notes |
|---|---:|---:|---|
| `cmpJcc` | 11 / 0 / 0 | 11 / 0 / 0 | `cmp` → `jcc .cf` |
| `adcChain` | 10 / 1 / 0 | 9 / 0 / 0 | Dead final carry `_c2` stays in `CF` (`0` `setcc`) |
| `adcxAdox` | 14 / 4 / 2 | 10 / 0 / 0 | Unpatched; single hoisted `xorz 11`, interleaved `adcx`/`adox` |
| `cfLoop` | 22 / 1 / 1 | 21 / 1 / 0 | Unpatched; loop-carried `CF` with `lea`/`dec`/`tstz`, `setcc` on exit only |

### `Bignum` (`LegalTarget.x64SSE`, standalone `/tmp/` check against extended `bigIsa`)

Extended `RegaLitmus.isa` in a standalone `/tmp/` Lean check with `umulw` (`.default` → `mul`, `.mulxFast` → `mulx`), `subb` (`sub`/`sbb`), and `select` (`cmovcc` on `.flag`, `test;cmovnz` on `.gpr`):

| Function | Before (`2a28b05`) | After (instrs & breakdown) |
|---|---|---|
| `mul4x4` | failed `Rega.lowerFn` (`let: op`) | **148 instrs**: `mul=5`, `mulx=11`, `adc=7`, `adcx=12`, `adox=12`, **`setcc=0`**, **`bt0=0`**, `xorz=4`, `slots=7`, `saved=4` |
| `addMod25519` | failed `Rega.lowerFn` (`let: op`) | **55 instrs**: `adc=4`, `sbb=4`, `cmov=4`, **`setcc=0`**, **`bt0=0`**, `xorz=2`, `slots=4`, `saved=0` |
| `subMod25519` | failed `Rega.lowerFn` (`let: op`) | **55 instrs**: `sbb=4`, `adcx=4`, `testCmov=4`, `setcc=1`, **`bt0=0`**, `xorz=2`, `slots=4`, `saved=1` |

## 3. Verification

- `timeout 300 lake build --wfail LeanQbe.T.Spill LeanQbeTest.T.RegaLitmusTest LeanQbeTest.T.RegaScaleTest LeanQbeTest.T.MainTest`: exited 0 (`126` jobs), all theorems `0 sorry` using only `[propext, Classical.choice, Quot.sound]`.
- `LeanQbe/T/Spill.lean`: `800` LOC (zero proof files touched).
- `LeanQbeTest/T/RegaLitmusProgs.lean`: `patchAdcxAdox`, `patchCfLoop`, `patchHints`, and `Patch` deleted; all 13 `G12` litmus programs lower via unpatched `Spill.hints isa fn`; `cmpJcc_code`, `adcChain_code`, `adcxAdox_code`, `cfLoop_code`, `cfLoop_cf_writers`, `g12a_code_highlights`, `*_nonvacuous`, and `*_correct` all green.
