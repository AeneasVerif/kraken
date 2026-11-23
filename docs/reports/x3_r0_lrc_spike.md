> **[Historical design note]** Written during the initial `LeanLRC` prototype; `LeanQbe.T.LeanLRC.*` and `test/lrc/run.sh` have since been wired into the main build and cyclic/SCC linking (`LinkRec`, `LinkScc`) has since landed. See `LeanQbe-README.md` for current paths and status.

# Lean `λRC` / `Lean.IR.Decl` → `LeanQbe.T` Prototype & Tier-0a Runtime

## 1. Architecture & Deliverables Summary

| Artifact | Purpose | LOC | Verification |
|---|---|---:|---|
| `LeanQbe/T/LeanLRC/Basic.lean` | Typed `λRC`/`Lean.IR` AST (`LrcVal`, `LrcExpr`, `LrcFn`, `LrcModule`), Kosaraju SCC & closure collector, `meta` `Lean.IR.Decl` reader (`lrc_of_lean!`) | 607 | `lake build --wfail`, `-DwarningAsError=true` |
| `LeanQbe/T/LeanLRC/Runtime.lean` | Tier-0a C0 runtime (`rtBase_fns`: 28 helpers), 64-bit LE header, tagged scalars `2n+1`, `genLeanApplyC0` balanced `jnz` dispatch generator | 506 | `28 × t_wf_reify` (`Func.Wf`), `-DwarningAsError=true` |
| `LeanQbe/T/LeanLRC/ToT.lean` | `LrcModule → TFlatFn` lowering (`rt` threading, `loop1` tail calls, `jdecl`/`jmp`, `reset`/`reuse` ctor fallback, `pap`/`ap`), 4 bench modules + `realLeanIrMod` | 992 | `TFlat.wfCheck`, `tflatFnsToFns_wf`, x64/Arm64 compile |
| `LeanQbeTest/T/LeanLRCTest.lean` | Kernel `Func.Wf` proofs, `#guard` suites, `scalarStructMod` coverage, single-line `#print axioms`, C++20/QBE codegen | 403 | 0 sorry, 0 native tactics, `[propext, Classical.choice, Quot.sound]` |
| `test/lrc/run.sh` | 7-way differential suite (`leanc`, `g++`, `clang++` ASan+UBSan, native x64, Arm64/QEMU, stock QBE x64 & Arm64) + exit traps | 86 | Bit-identical outputs & traps pass |

## 2. Tier-0a ABI, Layout, and Lowering Design

- **Explicit runtime state (`LeanRt *rt` at arg `0`):** `{base, cur, end, fuel, depth, env}` (48 B).
  Threaded through every user function and allocating/arithmetic runtime call (`lean_alloc_*`,
  `lean_box_u64`, `lean_nat_{add,sub,mul,div,mod}`). Non-tail user calls enter via
  `lean_rt_enter(rt)` (`fuel--`, `depth--`) and balance via `lean_rt_leave(rt)` (`depth++`) on
  every `.ret`. Tail self-calls (`.vdecl z _ (.fap fn args) (.ret (.var z))`) lower to `loop1` and
  use `lean_rt_tick(rt)` (`fuel--` without touching `depth`), keeping stack usage `O(1)`
  (validated by `lrc_sumTo(500) = 125250` leaving `rt.depth == 1024`).
- **SysV x64 6-GPR register cap:** `x64Frame.argRegs` exposes 6 GPRs (`rdi..r9`); reserving
  `rdi` for `rt` caps direct `LrcFn` arities at `≤ 5` (`ap` arities at `≤ 4` plus `clo`).
- **`lean_object` 64-bit LE header:** `rc` bits `0..31`, `cs_sz` bits `32..47`, `other` (field
  count) bits `48..55`, `tag` bits `56..63`; tagged immediate scalars use `(2*n + 1)` with `x >>> 1`
  unboxing, while scalar enum types (`Bool` at `IRType.uint8`) remain unboxed (`0`/`1`).
- **Conservative fallbacks:** `reset` decrements `x` and yields `lean_box(0)`; `reuse` lowers to
  fresh `lean_alloc_ctor` allocation; Tier-0a bump allocation does not reclaim `m_rc == 0` storage
  (`lean_is_shared` remains accurate via `m_rc == 1` vs `> 1`).

## 3. Empirical Measurements

### 3.1 Static C0 Runtime IR & Machine Code Sizes (`rtBase_fns`)

Total across all `28` C0-elaborated runtime helpers (`657` x64 / `662` Arm64 machine directives):

| Helper | TFlat Ops | x64 Dirs | Helper | TFlat Ops | x64 Dirs | Helper | TFlat Ops | x64 Dirs |
|---|---:|---:|---|---:|---:|---|---:|---:|
| `lean_is_scalar` | 2 | 10 | `lean_ctor_get` | 4 | 10 | `lean_box_u64` | 5 | 13 |
| `lean_box` | 3 | 7 | `lean_ctor_set` | 4 | 10 | `lean_unbox_u64` | 5 | 7 |
| `lean_unbox` | 2 | 6 | `lean_ctor_set_tag` | 2 | 7 | `lean_nat_add` | 14 | 36 |
| `lean_obj_tag` | 8 | 19 | `lean_inc` | 7 | 32 | `lean_nat_sub` | 13 | 34 |
| `lean_rt_enter` | 16 | 32 | `lean_dec` | 7 | 32 | `lean_nat_mul` | 15 | 49 |
| `lean_rt_tick` | 8 | 18 | `lean_is_shared` | 8 | 34 | `lean_nat_div` | 13 | 43 |
| `lean_rt_leave` | 5 | 9 | `lean_alloc_closure` | 20 | 37 | `lean_nat_mod` | 13 | 41 |
| `lean_alloc_small` | 12 | 21 | `lean_closure_get` | 4 | 10 | `lean_nat_dec_eq` | 11 | 34 |
| `lean_alloc_ctor` | 19 | 30 | `lean_closure_set` | 4 | 10 | `lean_nat_dec_le` | 15 | 33 |
| — | — | — | — | — | — | `lean_nat_dec_lt` | 15 | 33 |

### 3.2 Benchmark & Real `Lean.IR` Module Metrics

| Module | User Fns | Lowered Fns | `pap` Targets | SCCs | `checkAcyclic` | TFlat Ops | `jnz` | Calls | x64 Dirs | Arm64 Dirs |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `sumToMod` | 2 | 2 | 0 | 2 | `true` | 5 | 1 | 9 | 61 | 63 |
| `mapAddMod` | 5 | 6 | 1 | 5 | `false` | 42 | 7 | 52 | 344 | 348 |
| `tree2Mod` | 3 | 3 | 0 | 3 | `false` | 18 | 2 | 27 | 151 | 153 |
| `foldMapMod` | 6 | 8 | 3 | 6 | `false` | 78 | 17 | 88 | 651 | 669 |
| `realLeanIrMod` | 15 | 17 | 2 | 15 | `false` | 104 | 22 | 174 | 1072 | 1091 |
| `allBenchLrcMod` | 31 | 33 | 6 | 31 | `false` | 205 | 44 | 325 | 2052 | 2097 |

Note: Tail-recursive functions (`lrc_sumToAcc`, `lrc_mapAdd_build`, `lrc_foldMap_build`,
`leanSumToAcc`, `leanListBuild`, `leanListFoldl`) eliminate self-call cycles via `loop1`; thus
`sumToMod` linked with `rtBase_fns` already satisfies `Module.checkAcyclic = true`. Non-tail
recursive modules (`mapAddMod`, `tree2Mod`, `foldMapMod`, `realLeanIrMod`) have self/indirect
calls rejected by `Module.checkAcyclic`. Across our test corpus all static SCCs are size 1 because
user `ap` callers invoke `lean_apply_k` rather than direct mutual cycles; once cyclic linking links
`ap -> lean_apply_k -> papTarget`, higher-order mutual cycles (`f -> lean_apply_k -> g -> f`)
form non-trivial SCCs including `lean_apply_k` itself.

### 3.3 Defunctionalized `lean_apply_k` Dispatch Scaling & Overhead

`genLeanApplyC0` emits a balanced binary `jnz` tree over `fun_id` (`O(N)` static code size,
`O(log2 N)` dynamic branch depth per call), plus under-application allocation (`rem > k`) and
over-application chaining (`rem < k`). Measured scaling across `N` eligible arity-2 targets:

| Targets `N` | `apply_1` Ops | `apply_1` `jnz` | `apply_1` Calls | `apply_1` x64 | `apply_2` Ops | `apply_2` `jnz` | `apply_2` Calls | `apply_2` x64 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 16 | 4 | 13 | 119 | 18 | 5 | 15 | 145 |
| 2 | 18 | 6 | 18 | 161 | 20 | 7 | 18 | 181 |
| 3 | 20 | 8 | 23 | 203 | 22 | 9 | 21 | 217 |
| 4 | 22 | 10 | 28 | 245 | 24 | 11 | 24 | 253 |
| 8 | 30 | 18 | 48 | 413 | 32 | 19 | 36 | 397 |
| 16 | 46 | 34 | 88 | 753 | 48 | 35 | 60 | 685 |
| 32 | 78 | 66 | 168 | 1425 | 80 | 67 | 108 | 1266 |

Static growth is exact linear `2*N + 2` `jnz` nodes (`apply_1`: `+42` x64 dirs / target; `apply_2`:
`+36` x64 dirs / target). For `allBenchLrcMod` (`N = 6` targets: arities `[2, 2, 1, 3, 3, 2]`),
`lean_apply_1` compiles to `26` ops, `14` `jnz`s, `40` calls (`336` x64 dirs); `lean_apply_2` filters
to the `5` targets with `arity ≥ 2` and adds the `rem == 1` over-application path (`26` ops, `13`
`jnz`s, `31` calls, `303` x64 dirs).

### 3.4 Depth & Fuel Guard Overhead

- **Static code size:** `lean_rt_enter` (`16` ops, `32` x64 / `30` Arm64 dirs) + `lean_rt_tick`
  (`8` ops, `18` x64 / `20` Arm64 dirs) + `lean_rt_leave` (`5` ops, `9` x64 / `10` Arm64 dirs).
- **Dynamic per-call overhead:** Every non-tail function pays 2 extra calls (`enter` on entry,
  `leave` before `ret`) checking `rt->fuel` and `rt->depth` in memory. Each tail `loop1` iteration
  pays 1 `lean_rt_tick` call checking/decrementing `rt->fuel` only.
- **Follow-up optimization path:** With cyclic linking and inlining, inlining
  `lean_rt_{enter,tick,leave}` (keeping `rt` or its `fuel`/`depth` fields in registers across
  `loop1`) eliminates per-iteration call overhead (~2 instructions: `decq`/`cbz`).

## 4. Differential Validation Results

`test/lrc/run.sh` asserts byte-for-byte identity across:
1. Native Lean 4 (`lean -c` + `leanc -O2`),
2. `PrintCpp` + `g++ -std=c++20 -O2` (`-DTQBE_CATCH_UB`),
3. `PrintCpp` + `clang++ -std=c++20 -O2 -fsanitize=undefined,address` (`ASan + UBSan`),
4. Native x64 ELF (`LeanQbe.T.compile x64Target` + `gcc`),
5. Native AArch64 ELF (`LeanQbe.T.compile armTarget` + `aarch64-linux-gnu-gcc` + `qemu-aarch64`),
6. Stock QBE (`amd64_sysv` & `arm64` via `qemu-aarch64`).

Observed identical vectors:
- `n ∈ {0, 1, 5, 10, 12}`: `(sumTo, mapAdd(+3), foldMap(+4))` = `(0,0,0)`, `(1,4,6)`,
  `(15,30,40)`, `(55,85,105)`, `(78,114,138)`.
- `d ∈ {0..6}`: `tree2(d)` = `1, 3, 8, 20, 48, 112, 256`.
- Tail stress: `lrc_sumTo(500) == 125250` with `rt.depth == 1024` preserved.
- Exhaustive scalar/struct test (`scalarStructMod` under ASan+UBSan): `lrc_struct_roundtrip == 1058`.
- Abnormal traps (`g++` `ExitException`, native x64 & Arm64 `setjmp`/`longjmp`):
  `lean_out_of_fuel`, `lean_stack_overflow`, `lean_oom` all trap as expected.

## 5. Readiness Analysis for Cyclic Recursion Linking (`LinkRec`)

The Tier-0a `λRC` pipeline exposes three concrete requirements for cyclic/mutually recursive linking
(`LinkRec`/`LinkScc` supporting arbitrary mutually recursive modules and closures):

1. **Coinductive / Fixed-Point `ModuleOk` (`Env` Least-Fixed-Point / Fuel-Indexed `wp`):**
   - Acyclic `LeanQbe/T/Module.lean` requires `M.fns = pre ++ fn :: post`
     with `fn.callsOk (pre.map Fn.sig ++ ext.map Extern.sig)`. This handles `sumToMod` (`loop1`),
     but rejects non-tail recursion (`lrc_treeSum`, `lrc_mapAdd_map`) and `lean_apply_k`
     ↔ user closure SCCs (`realLeanIrMod`, `foldMapMod`).
   - **Design requirement:** Replace the linear `pre ++ fn :: post` prefix restriction with a cyclic
     `M.callsOk (allSigs := M.sigs)` predicate plus a mutual/fuel-indexed or coinductive `Env`
     hypothesis: assuming every `g ∈ M.sigs` meets `Γ g` at strictly smaller recursion measure `(fuel,
     depth)` (matching explicit `rt->fuel` and `rt->depth`), every SCC in `M` discharges `ModuleOk`
     by induction on `rt->fuel`. Both `rt->fuel` and `rt->depth` in `LeanRt` provide the semantic
     termination witness needed for total correctness (`Func.wp` with `exits`) over recursive Lean
     programs.

2. **Sound Whole-Module Stack Bounds (`stackBound_rec`):**
   - Acyclic `LeanQbe/T/Main.lean` `calleesBound` computes
     `max(F + ra + bound(callee))` assuming an acyclic DAG (`Option Nat` fails or diverges on cycles).
   - **Design options:** Two approaches compose directly with `LeanLRC`:
     - *Dynamic `depth` guard (already live in Tier-0a):* `rt->depth` caps call chain length at `D0`,
       so peak stack usage of any cyclic SCC `S` is statically bounded by `D0 * (max_{f ∈ S} (F_f + ra))`
       (plus acyclic prefix/suffix bounds). In the stack-frame invariant, lowering passes `rt->depth` as
       an explicit ghost/state invariant tying machine `%rsp`/`sp` headroom to `(rt->depth + 1) * F_max`.
     - *SCC contraction:* Contract cyclic SCCs via Tarjan/Kosaraju before computing acyclic `calleesBound`
       on the condensation DAG. Note `lrc_sumToAcc` avoids recursion via `loop1` (frame bound = 1x).

3. **Defunctionalized Higher-Order Call Specification (`ap -> lean_apply_k`):**
   - Because `lean_apply_k` branches on `cl->m_fun_id` and saturates/chains all `N` `pap` targets,
     `lean_apply_k` connects caller SCCs to every closure target in the module, inflating the worst-case
     callees-set of `lean_apply_k`.
   - **Design requirement:** Separate *type-safe indirect specification* (`closureSpec cl` indexing a
     relational closure table by `(fun_id, nfix, args)`) from *monolithic inlined SCCs*: `lean_apply_k`'s
     `wp` postcondition can dispatch to `(targets[fid].spec)` at `fuel' = fuel - 1`, letting
     callers (`listMap`, `listFoldl`) stay modular without knowing unrelated closure targets' frames,
     while per-target ABI conformance (`params.all (·.toTTy == i64)`) is already enforced in
     `lowerLrcProgram`.
