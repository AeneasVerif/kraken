> **[Historical design note]** Written during an earlier milestone; several `LeanQbe/*.lean` (E1) paths referenced below have since moved to `LeanQbe/T/`. See `README.md` for current paths.

# rega: verified lowering, pipeline, litmus tests

Owner: `rega`. Files: `LeanQbe/{Rega,RegaLemmas,Main,MainLemmas}.lean`, `LeanQbe/{Live,Spill}.lean`,
`Main.lean` (CLI), `LeanQbe/Examples/Litmus*.lean`, `test/`, `spike/e3/`.

## Status

| Milestone | State |
|---|---|
| Proof skeleton against a mock target (E1) | done, scratch only (not in the repo), no sorry |
| R1: `lower` for param/let/store/ret, generic proof, x64 tracer | done: generic-host Kraken-only theorem plus non-vacuity |
| R2, E1 half: control-flow litmus, oracle, pipeline | done: five programs checked by kernel `rfl`, with FnSpec instances and native runs; `sumto` end to end with a loop proof |
| R2, E3 half: the same skeleton in E3, the D8 comparison | done (`spike/e3/`, written by helper `e3`; see below) |
| R3: calls, exits, stack spills, prologue/epilogue, oracle, module linking, 4-way litmus | done: `lower_correct`, `lowerFn_correct`, `compileFn_correct`, `compile_correct`, `callinc` / `twice` / `spill10` / `sumcall` checked 4 ways |
| Step 5 (x64): linked `[find, union]` Union-Find end to end on Kraken x64 | done: `uf_module_fnspec`, `find_x64_correct`, `union_x64_correct`, `find_x64_nonvacuous`, `union_x64_nonvacuous`, `test/uf_main.c` |
| Step 7 (x64): linked `lratCheckFns` LRAT-trim checker end to end on Kraken x64 | done: `lrat_module_compile`, `lrat_module_fnspec`, `checkProof_x64_correct`, `checkProof_x64_nonvacuous`, `checkProof_x64_accepts`, `test/lrat_trim_main.c` |
| Untrusted-bytes LRAT checker (x64): linked 6-fn `lratBytesFns` (`Amd64.fastTarget`) end to end on Kraken x64 | done: `lrat_bytes_module_compile`, `lrat_bytes_module_fnspec`, `lrat_check_bytes_x64_correct`, `lrat_check_bytes_x64_unsat`, `lrat_check_bytes_x64_accepts`, `lrat_check_bytes_x64_rejects`, `test/lrat_bytes_main.c` (26/26 PASS in `test/run.sh`) |

## What exists

### `LeanQbe/Rega.lean` (executable, imports no lemmas)

`lower (h : Hints I) (E : Ext) (fn : String) : Expr Nat Nat → St I → Res I`, one structural
recursion over the PHOAS term at `V := Nat, L := Nat`.

- **Locations (`Loc I`)**: `.reg r` (an allocatable or scratch register) or `.slot i` (spill slot
  `i < h.nslots` of the current stack frame).
- **Symbolic location file (`R : List (Arg Nat × Loc I)`)**: a relation between values/constants and
  locations. `clob d R` removes `d` and all scratch registers while keeping spill slots; `slotsOnly R`
  (used after `call`) drops all register entries and keeps only `.slot i` entries.
- **Moves (`Move I`)**: `.mov d s`, `.movi d c`, `.ld d i` (`slotLd`), `.st i s` (`slotSt`), checked
  by `Move.ok h.nslots` and executed symbolically by `execMoves`.
- **Hints (`Hints I`)**: `dest : Nat → Option Reg`, `entry : Nat → Entry I` (`live : SymRegs I`
  allowing both registers and slots, `ploc : List Reg`), `pre : Nat → List (Move I)` (spills,
  reloads and copies emitted before instruction number `ip`), and `nslots : Nat`.
- **Untrusted parallel moves (`pmove`, `shuffle`)**: handles register-to-register, slot-to-register
  (`.ld`), register-to-slot (`.st`), and constant-to-register (`.movi`) moves at `call`, `jump`,
  `ret`, and `exit`, breaking register cycles via a scratch register and checking that every target
  entry holds in the resulting `SymRegs`.
- **Frame & calls/exits**: `lowerFn` emits `label f.name :: (prologue h.nslots ++ c)`. `ret` emits
  `epilogue h.nslots ++ ret`; `exit g as` shuffles arguments into `argRegs` and emits
  `epilogue h.nslots ++ tailJmp g`; `call g as k` shuffles arguments into `argRegs`, emits
  `call g`, filters `R` with `slotsOnly`, and binds continuation parameters from `retRegs`.

### `LeanQbe/RegaLemmas.lean`

- `lower_correct`: one induction on `Wf G D e₁ e₂` against `Target` v1 (`Abi.lean`, `AbiLemmas.lean`).
  - `Agree G R s σ`: every `(a, .reg r) ∈ R` holds `a`'s value in `T.get s r`, and every
    `(a, .slot i) ∈ R` holds `a`'s value in `σ[i]?`.
  - `Inv hints s₀ ra n Rf m s σ`: `σ.length = hints.nslots`, `T.get s T.sp = base hints s₀`
    (`sp₀ - frameSize nslots`), callee-saved registers equal to `s₀`, and
    `T.mem s =⋆ Eq m ⋆ (slots (base hints s₀) σ ⋆ T.Saved (T.get s₀ T.sp) ra hints.nslots ⋆ region (sp₀ - n) (n - frame hints) ⋆ Rf)`.
  - `call` uses `callee_split` to split off `region (base - raBytes - bound g) (bound g + raBytes)`
    from the stack reserve below the frame, applies `T.call_fnspec` with the caller's `slots`,
    `Saved`, and remaining stack reserve framed into `G`, restores `Inv` on normal return using
    `Agree.slotsOnly`, and propagates callee exits by absorbing the caller's frame into the
    existential `F` of `FnPost`'s exit disjunct.
  - `ret` and `exit` run `epilogue_ok` (`frame_close` converts `slots` back to `region` via
    `slots_region` and merges the frame and reserve back into `T.Entry sp₀ ra n`) followed by
    `T.ret_spec` or `T.tailJmp_spec`.
- `lowerFn_correct`: steps past `label f.name` and `prologue hints.nslots`, splits `T.Entry sp₀ ra n`
  into the frame and callee reserve, converts the raw frame region into initial spill slots `σ` via
  `region_slots`, and applies `lower_correct` to conclude `T.FnSpec h f.name (Func.spec Γ f.body) n nX`.

### Oracle: `LeanQbe/Live.lean`, `LeanQbe/Spill.lean` (untrusted, no lemmas)

- `Live.toTree` replays `lower`'s exact `(nv, nl, ip)` numbering and traversal order. `liveLabels`
  computes join-point live-in sets by fixpoint; `liveIn` computes live sets at each node; `acrossCalls`
  collects names live across any `call` (live into the continuation other than its result `param`s).
- `Spill.hints I f` assigns each live name a permanent home (`.reg r` or `.slot i`):
  - A name gets a spill slot if it is in `acrossCalls`, if `≥ allocatable.length - 2` live-out names
    already have register homes (keeping 2 allocatable registers free as reload/destination
    temporaries), or if it is live into a block whose live-in register homes plus block parameters
    would exhaust `allocatable`.
  - Spilled definitions (`let_`, `load`, and function/call-result/block `param`s) are stored to their
    slots in the `pre` moves of the following instruction (stores first), and reloaded into free
    allocatable registers in the `pre` moves of instructions that read them.
  - Compiles all 12 litmus functions, `UnionFind` (`find`, `union`, `unionInline`), `LratRup`, and
    all 5 functions of `LratTrim` (`strictCheck` 35 slots, `checkClause` 4 slots, `checkProof` 7
    slots, `trimProof` 33 slots).

### Pipeline & linking: `LeanQbe/Main.lean`, `LeanQbe/MainLemmas.lean`

- `Fn.ext` extracts `callees` and `exits` from `f.body`; `compileFn I f` runs `Func.opt`,
  `Spill.hints`, and `Rega.lowerFn`.
- `compileFn_correct` and `compileFn_leaf_correct` lift `lowerFn_correct` through `Func.opt_wf` and
  `Func.opt_spec`.
- `compile_correct` proves module-level linking for `compile T.toIsa fs = .ok code` over an acyclic
  list of functions `fs` (callees first).
- `compileModule` and `compile_sound`: `compileModule I raBytes extCallees exits nX fs` compiles an
  acyclic module and computes and checks all per-function stack bounds `(f.name, b)` automatically
  inside the compiler. `compile_sound` proves that when `compileModule` returns `.ok (code, bounds)`
  (checked by `kernel_rfl`), the user only discharges `Func.Wf`, source contracts
  `Γ f.name → Func.spec Γ f.body`, external callee `FnSpec`s, and exit `Defined`ness to obtain
  `T.Defined h p.1 ∧ T.FnSpec h p.1 (Γ p.1) p.2 nX` for every `p ∈ bounds`.

### Litmus, Step 5 Union-Find, Step 7 LRAT-trim, and Untrusted-Bytes LRAT (`LeanQbe/Examples/Litmus*.lean`, `test/`)

All 13 litmus suites (`tracer`, `ifelse`, `sumto`, `evenodd`, `nested`, `swap`, `callinc`, `twice`,
`spill10`, `sumcall`, `uf`, `lrat_trim`, `lrat_bytes`) pass all four checks:
1. Kernel evaluation (`*_compile` and `*_module_compile` by `kernel_rfl` against Kraken-parsed
   assembly literals and computed stack bounds).
2. Native execution (`test/run.sh`: `leanqbe <name>` → `cc` with `test/<name>_main.c` → run).
3. Stock QBE differential run (`test/run.sh`: `leanqbe --il <name>` → stock `qbe` → `cc` → run):
   26/26 PASS (including `PROT_NONE` guard-paged + `0xAA`-poisoned `test/lrat_bytes_main.c`).
4. `scripts/check.sh` (zero warnings, zero `sorry`, standard 3 axioms on all headline theorems).

Closed Kraken-x64-only end-to-end theorems + concrete non-vacuity instances:
- `tracer_correct`, `tracer_nonvacuous` (`LeanQbe/Examples/Litmus.lean`)
- `sumto_correct`, `sumto_nonvacuous` (`LeanQbe/Examples/LitmusCfLemmas.lean`)
- `callinc_module_fnspec`, `callinc_correct`, `callinc_nonvacuous` (2-function module with spill across call)
- `twice_module_fnspec`, `twice_correct`, `twice_nonvacuous_exit` (2-function module with exit propagation through call)
- `spill10_fnspec`, `spill10_correct`, `spill10_nonvacuous` (6 stack spill slots, 56-byte frame)
- `uf_module_fnspec`, `find_x64_correct`, `union_x64_correct`, `find_x64_nonvacuous`, `union_x64_nonvacuous` (`LeanQbe/Examples/LitmusUf.lean`: linked `[find, union]` module via `compile_sound`, entering at `Labels.label "find"` and `Labels.label "union"`, where `union` calls `find` twice and spills `p`, `y`, `rx` across the calls)
- `lrat_module_compile`, `lrat_module_fnspec`, `checkProof_x64_correct`, `checkProof_x64_nonvacuous`, `checkProof_x64_accepts` (`LeanQbe/Examples/LitmusLrat.lean`: linked 4-function LRAT checker module `[checkRup, strictCheck, checkClause, checkProof]` via `compile_sound`, with computed bounds `[472, 296, 520, 584]`, entering at `Labels.label "br_check_proof"` and concluding `cnf₀.Unsat` on normal return or exit to `Labels.label "lrat_fail"`, plus concrete accepting execution `checkProof_x64_accepts` on `nvAcceptBytes` concluding `st.pc = 0x1234 ∧ nvAcceptCnf.Unsat` with exit postcondition `False`)
- `lrat_bytes_module_compile`, `lrat_bytes_module_fnspec`, `lrat_check_bytes_x64_correct`, `lrat_check_bytes_x64_unsat`, `lrat_check_bytes_x64_accepts`, `lrat_check_bytes_x64_rejects` (`LeanQbe/Examples/LitmusLratBytesCode.lean` + `LeanQbe/Examples/LitmusLratBytes.lean`: linked 6-function untrusted-bytes ASCII DIMACS + Binary LRAT checker module `lratBytesFns` on `Amd64.fastTarget` via `compile_sound`, 2,268 Kraken-parsed x64 directives, computed bounds `[136, 664, 168, 632, 728, 968]`, `exits = []`, proving both full ABI preservation on arbitrary byte buffers (`rax = 1 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`), the parser-free trivial-postcondition corollary `lrat_check_bytes_x64_unsat` on `(encodeDimacs cnf)` (`st.pc = ra ∧ (rax = 0 ∨ rax = 1) ∧ (rax = 1 → cnf.Unsat)`), and concrete machine-level accepting (`rax = 1 ∧ nvBytesCnf.Unsat`) and rejecting (`rax = 0`) executions in `lratBytesHost`)

## D8 and D9 evidence (R2)

**D9 (direct lowering from PHOAS) holds** through calls, exits, and stack spills (`RegaLemmas.lean`,
1250 lines total). The `toFlat` fallback is not needed.

**D8 (E1 against E3)** compares the same lowering proof against the same mock target (`spike/e3/`,
full table in `spike/e3/README.md`):

| | E1 | E3 |
|---|---|---|
| main lemma | 215 lines, one `induction hwf` | 214 + 16 lines, three mutual lemmas, no hand-written induction principle needed |
| junk cases | 3 constructs (`args = []` in 7 cases, block without a pending label, the `acc`/`pend` invariant everywhere), about 14 lines | none |
| `Wf` | 19 lines | 36 lines |
| elaboration / kernel of the main lemma | 1.04 s / 28 ms | 1.28 s / about 61 ms |
| even/odd `lower … = .ok` by `rfl` | works (62 ms; kernel only 24 ms) | works (65 ms; kernel only 25 ms) |
