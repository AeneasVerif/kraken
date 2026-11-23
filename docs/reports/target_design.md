> **[Historical design note]** Written during the initial design of `LeanQbe/T/Target.lean` and `LeanQbe/T/Rega.lean`; several deferred items (such as `LinkRec`/`LinkScc`) have since been implemented. See `LeanQbe-README.md` for current architecture and file paths.

# Target Interface Design Note: PHOAS-First Checked Lowering, Flag-Frame Snippets, and ABI Contract

Companion artifacts (early design prototypes, verified with `0 sorry`, `-DwarningAsError=true`, standard axioms only):
- Target/ISA interface: `LeanQbe/T/Target.lean` & cross-module `t_kernel_rfl` test `LeanQbeTest/T/TargetConsumerTest.lean`
- Flag-frame preservation prototypes (historical scratch checks for x86-64 and AArch64 flag clobbering)

---

## 1. PHOAS-First Lowering Architecture & Bounded Symbolic State

`Rega` lowers `Fn` directly by structural mutual recursion `lowerExpr` / `lowerBlocks` over `Expr K KL rs` and `Blocks K KL rs sig` instantiated at `K := fun _ => Nat` and `KL := fun _ => Nat`, gated by `fn.Wf`, `fn.isLegal`, and `Fn.backendOk I fn = true` (without `TFlat` or `denote` at `lower` time). Correctness (`lowerFn_correct : ... → T.FnSpec h fn.name ...`) is proved directly by `Wf.induct` relating `(K := Nat, KL := Nat)` in lockstep with `(V := Val, L := Cont)`.

* **Bounded `SymState` & kernel-reduction (`t_kernel_rfl`) guardrails:**
  1. `R_reg : List (SymArg × RegLoc Reg VReg Cond)` — active bindings (`SymArg`: `var | immBool | immBits | immVec`) in `.gpr r`, `.vec vr`, or `.flag c` **only**. Since each physical register/condition holds at most one live `SymArg`, `R_reg.length ≤ |GPR| + |VReg| + |Cond|` (`O(1)` scan for lookup, clobber, and flag kill).
  2. `R_slot : Trie (SymArg × SlotWidth)` — active stack slots indexed by 8-byte granule `i < h.nslots` (`O(log N)` structural `find?`/`erase` on `Trie` + `insertAux (n + 1)` on `Nat` fuel with zero `WellFounded.fix`, proved via `Trie.find?_insert_{self,ne}` & `Trie.find?_erase_{self,ne}` in `LeanQbe/T/Target.lean`). Memory predicates reuse `region`, `cell64`, and `array64` directly from `LeanQbe.T.Logic.Mem` (avoiding duplicate `word`/`slots` aliases).
  3. `defs : Trie DefFact` — pure SSA definitions `x = op(args)` for total `OpCode`s, passed **lexically** (never threaded sequentially across `.jnz` branches or sibling `Blocks`). By lexical SSA freshness (`nv` strictly increasing), entries hold monotonically with zero kill maintenance, enabling checked `[base + disp]` folding (`AddrArg.baseDisp`) and constant/copy rematerialization without a `.remat` `Loc` constructor.
  4. `nv nl ip : Nat` — fresh variable IDs, structural `Nat` block labels, and instruction index into `Hints.{dest, pre, variant}`. All computable `module` checks use pure `Bool` (`Nat.ble`, `List.contains`, `==`, `&&`, `||` — never `Prop` `if a < b` / `∈` `Decidable` witnesses that block cross-module `t_kernel_rfl`, verified in `TargetConsumerTest.lean`), `OpCode` matchers match flatly (`match sig, rs, code with`), and `LabelsUnique` is proved structurally from monotone `[nl, nl')` bounds in `Rega` rather than `O(L²)` `List.Nodup` `decide`.
* **Literal `Hints` splicing path (`MainLemmas`):** `SlotWidth`, `Loc`, `VariantHint`, `Move`, `PreStep`, `SymArg`, `Entry`, `Trie`, and `Hints` all derive `Lean.ToExpr` in `Target.lean` (matching `Kraken/{X64,AArch64}/Syntax.lean`), so the MetaM compile wrapper runs untrusted `Spill.hints` outside the kernel and splices literal `Hints` expressions directly via `Lean.toExpr` (verified in `TargetConsumerTest.sampleHintsExpr`) without `Repr` round-tripping.
* **Simulation invariant (`Agree`), `entryScopeOk`, & `.group` (`Blocks`):** `Agree s st ρ m G` asserts: (i) every `(sa, rl) ∈ st.R_reg` satisfies `GprHolds` / `VecHolds` / `evalCond = b` under `ρ`; (ii) `s.mem =⋆ Eq m ⋆ Saved sp₀ ra h.totalSlots ⋆ SlotMem sp h.nslots st.R_slot ρ ⋆ CsMem sp h.nslots h.saved s₀ ⋆ G`; (iii) `s.sp = sp₀ - frameSize h.totalSlots` with `spOk s.sp` and `frameSize h.totalSlots + raBytes ≤ 2^64` (zero mid-body `push`/`pop`); (iv) every pure fact in `st.defs` evaluates to `ρ x`. At `.group bodies k`, `Rega` checks `entryScopeOk nv` (`Nat.ble (x + 1) nv` for every `.var x` in `Entry.live`, blocking future-`nv` slot injection on unreachable blocks), packages label existence + continuation into `LabJ`, proves `Closed Γ Q X (bodies Js) Js` over `Blocks`, and steps into `k Js` (eliding `jmp` on fallthrough `ft = some ℓ`).

---

## 2. Snippet Lemma Signatures & Flag-Frame Clauses (6 Representative Op Kinds)

Every snippet spec in `LeanQbe/T/Target.lean` uses `M.FallsTo condReads h k code gClob vClob fClob s Q post`, whose `M.Frame` packages `M.KeepsGpr`, `M.KeepsVec`, and `M.UpdFlags`:
```lean
def UpdFlags (condReads : C → FlagMask) (s s' : M.MData) (mask : FlagMask) : Prop :=
  ∀ c, FlagMask.disjoint (condReads c) mask = true → M.evalCond s' c = M.evalCond s c
```
Snippet proofs keep `@[step_simp]` separate from Kraken `@[kstep]` so `get64`/`set64`/`getXReg`/`setXReg` stay unexpanded for `grind`/rewrite lemmas. Scratch-using specs require `rd ∉ scratch` / `vd ∉ vecScratch`, while pure 1-reg `mov_spec` (`[rd]`) and `vmov_spec` (`[vd]`) allow `tmp ∈ scratch` / `vtmp ∈ vecScratch` so `pmove` breaks GPR/VReg cycles in registers. Generic flag-kill rule: retain `(sa, .flag c) ∈ R_reg` iff `FlagMask.disjoint (condReads c) fClob = true`.

### (1) Move (`mov` / `movi 0` / `setcc` — `GprTarget.{mov_spec, movi_spec, setcc_spec}`)
```lean
mov_spec   : ∀ {h k rd rs s post}, M.FallsTo g.condReads h k (g.mov rd rs) [rd] [] FlagMask.none s
               (fun s' => M.getGpr s' rd = M.getGpr s rs ∧ M.mem s' = M.mem s) post
movi_spec  : ∀ {h k rd c s post},  M.FallsTo g.condReads h k (g.movi rd c) (rd :: scratch) [] FlagMask.none s
               (fun s' => M.getGpr s' rd = c ∧ M.mem s' = M.mem s) post
setcc_spec : ∀ {h k rd c s post}, rd ∉ scratch → M.FallsTo g.condReads h k (g.setcc rd c) (rd :: scratch) [] FlagMask.none s
               (fun s' => GprHolds (M.getGpr s' rd) .bool (M.evalCond s c) ∧ M.mem s' = M.mem s) post
```
* **Flag-frame & invariants:** All 9 `Move` constructors (`mov`, `movi`, `ld`, `st`, `setcc`, `vmov`, `vmovi`, `vld`, `vst`) have `fClob = FlagMask.none` (`0x00#8`), preserving **every** live `.flag c` across `PreStep.moves` and parallel-move shuffles. On x64, `movi rd 0` emits `mov $0, %rd` (preserving `CF`, unlike `xor %edx, %edx` which clears `CF`). `Move.setcc` (`setcc %dl; movzbl %dl, %edx` / Arm64 `CSINC rd, xzr, xzr, c.invert`) is the **sole** flag-bank move (`flag → GPR`, writing `0`/`1` in low 8 bits).

### (2) Scalar ALU (`add` / `lea` / `udiv` — `GprTarget.op_spec`)
```lean
op_spec : ∀ {h k sig rs} {code : OpCode sig rs} {pas dsts vh c clob vs P s post},
  g.op code pas dsts vh = some (c, clob) → (∀ r ∈ tupArgGprs pas, r ∉ scratch) → (∀ r ∈ tupDstGprs dsts, r ∉ scratch) →
  TRel (M.PArgHolds s) pas vs → code.wp vs P →
  M.FallsTo g.condReads h k c (tupDstGprs dsts ++ scratch) [] clob s
    (fun s' => (∃ rvs, P rvs ∧ TRel (M.PDstHolds s') dsts rvs) ∧ M.mem s' = M.mem s) post
```
* **Flag-frame & sub-word discipline:** Narrow writers need not clear upper bits `(n..64)`. On x64, `lea (%r1,%r2), %rd` returns `clob = 0x00#8`, whereas `add %r2, %rd` returns `0xFF#8`; Arm64 non-`S` `ADD` returns `0x00#8`. Partial ops (`udiv`/`sdiv`) extract `b ≠ 0` / `¬sdivOv` directly from `code.wp vs P`; demonic undefined flags (e.g., x64 `rol` `OF`) set their bits in `clob`.

### (3) Flag Writer (`cmp` & `addc`/`subb` chains — `GprTarget.op_spec` + `clearFlags_spec`)
* **Instantiation:** `OpCode.cmp` with `dsts = (.flag c, ())` sets `M.evalCond s' c = b` (`clob = 0xFF#8`). For `OpCode.addc 64` with `dsts = (.gpr rd, .flag .c, ())` and `vh = .adcx`, x64 emits `adcx` with `clob = 0x01#8` (`CF` only; `OF` preserved); `vh = .adox` emits `adox` (`clob = 0x20#8`, `CF` preserved); loop-latch `sub 1` with `vh = .decInc` emits `dec` (`clob = 0x3E#8`, `CF` preserved across backedge); `clearFlags_spec` (`xor %eax, %eax`) seeds `(.immBool false, .flag .c)` / `.flag .o`. On AArch64, `OpCode.subb 64` caches logical borrow in `.flag .cc` (`!status.c`), matching `SBCS` with 0 inversions.

### (4) Flag Reader (`select → cmovcc`/`csel` via `op_spec`, and `jcc_spec` / `jnzGpr_spec`)
```lean
jcc_spec : ∀ {h k j c l s post}, (g.jcc c l).IsInfixAt (M.prog h) k → M.labelAddr h l = M.addrOf h j →
  (∀ s', M.Frame g.condReads s s' scratch [] FlagMask.none → M.mem s' = M.mem s →
    (M.evalCond s c = true → M.Run h j s' post) ∧ (M.evalCond s c = false → M.Run h (k + (g.jcc c l).length) s' post)) → M.Run h k s post
```
* **Flag-frame & GPR fallback:** Reading `.flag c` in `OpCode.select` emits branchless `cmovcc`/`csel` (`clob = 0x00#8`, non-destructive); `.jnz` emits `jcc c` / `jcc (negCond c)` (`fClob = 0x00#8`). On AArch64, `Cond` is the 14-case `ArmCond` excluding `AL`/`NV` (since Kraken treats `NV` as always true). When the bool is in `.gpr r`, `select` uses `testb`+`cmovnz` and `.jnz` uses `jnzGpr_spec` (`testb`+`jnz` / `tbnz`) — **never** reloading GPR → flag.

### (5) Vector Moves, Vector Immediates, & Multi-Granule Spills (`VecTarget.{vmov_spec, vmovi_spec, vslotSt_spec, vslotLd_spec}`)
```lean
vmov_spec    : ∀ {h k w vd vs s post}, M.FallsTo condReads h k (v.vmov w vd vs) [] [vd] FlagMask.none s
                 (fun s' => (M.getVec s' vd).setWidth w.bits = (M.getVec s vs).setWidth w.bits ∧ M.mem s' = M.mem s) post
vmovi_spec   : ∀ {h k w vd c code s post}, v.vmovi w vd c = some code → vd ∉ v.vecScratch →
                 M.FallsTo condReads h k code scratch (vd :: v.vecScratch) FlagMask.none s
                   (fun s' => (M.getVec s' vd).setWidth w.bits = c.setWidth w.bits ∧ M.mem s' = M.mem s) post
vslotSt_spec : ∀ {h k w i vr s G post}, vr ∉ v.vecScratch → spOk (M.getGpr s sp) →
                 (M.mem s =⋆ region (M.getGpr s sp + BitVec.ofNat 64 (8 * i)) (8 * w.slots) ⋆ G) →
                 M.FallsTo condReads h k (v.vslotSt w i vr) scratch v.vecScratch FlagMask.none s
                   (fun s' => M.mem s' =⋆ array64 (M.getGpr s sp + BitVec.ofNat 64 (8 * i)) (unpackSlotWords w (M.getVec s vr)) ⋆ G) post
vslotLd_spec : ∀ {h k w i vd bv s G post}, vd ∉ v.vecScratch → spOk (M.getGpr s sp) →
                 (M.mem s =⋆ array64 (M.getGpr s sp + BitVec.ofNat 64 (8 * i)) (unpackSlotWords w bv) ⋆ G) →
                 M.FallsTo condReads h k (v.vslotLd w vd i) scratch (vd :: v.vecScratch) FlagMask.none s
                   (fun s' => (M.getVec s' vd).setWidth w.bits = bv.setWidth w.bits ∧ M.mem s' = M.mem s) post
```
* **Flag-frame, vector immediates, & granule invariants:** All four specs have `fClob = 0x00#8`. `Move.vmovi` materializes `SymArg.immVec` (`v.vmovi` returns `Option` since Kraken `d2b7a5e` loads 64/128-bit constants via `movabs`+`vmovq`+`palignr` and `0`/`allOnes` at 256/512 via `vpternlogd`). Low-`t.size` `VecHolds` covers both SSE `replaceLow` and VEX/EVEX zero-extension; unaligned spills map directly onto `array64` via `unpackSlotWords`. `VecIsa`/`VecTarget` (`Amd64/IselVec`) own `vslotSt`/`vslotLd`, keeping `FrameIsa`/`FrameTarget` `VReg`-free (`VecTarget.empty` on AArch64).

### (6) Call (`FrameTarget.{canonAbi_spec, call_spec}` + `Target.FnSpec`)
```lean
call_spec : ∀ {h k sym s G post}, (f.call sym).IsInfixAt (M.prog h) k →
  (M.mem s =⋆ region (M.getGpr s f.sp - BitVec.ofNat 64 f.raBytes) f.raBytes ⋆ G) →
  (∀ s', M.getGpr s' f.sp = M.getGpr s f.sp - BitVec.ofNat 64 f.raBytes →
    M.Frame condReads s s' (f.sp :: f.raRegs ++ f.scratch) [] FlagMask.all →
    raReg s' (M.addrOf h (k + (f.call sym).length)) →
    (M.mem s' =⋆ RetAddr (M.getGpr s' f.sp) (M.addrOf h (k + (f.call sym).length)) ⋆ G) →
    Eventually (M.step h) post (M.mkState s' (M.labelAddr h sym))) → M.Run h k s post
```
* **Flag-frame, `AbiGprHolds` scope, & `FnSpec`:** At `.call sym args k`, `Rega` shuffles `args` into distinct `Isa.assignArgs as` (`argRegs_nodup`/`vecArgRegs_nodup`), zero-extends sub-64-bit GPRs via unified `canonAbi_spec` (shared with `.ret`), and calls `sym` (`fClob = FlagMask.all`). The flag-kill rule drops all `.flag` and caller-saved `.gpr`/`.vec` entries from `R_reg`; `saved` GPRs (`Target.Restored`, GPRs + `sp` only), `R_slot`, and `defs` survive; `RetsIn` (`retRegs_nodup`/`vecRetRegs_nodup`) weakens via `AbiGprHolds.toGprHolds`; exits compose via `nX ≤ n' ∧ n' + raBytes ≤ 2^64`. **C ABI scope note:** `AbiGprHolds` requires 64-bit zero-extension in both `ArgsIn` and `RetsIn`; compiled functions tolerate unextended narrow C inputs internally, but `FnSpec` directly covers external C callers/callees at narrow `bool`/`i8`/`i16`/`i32` only when zero-extended (or wrapped in an `i64` C shim; `Bignum`/`ChaCha`/`LratBytes` pass only `i64` pointers/scalars and vectors).

---

## 3. Design Decisions & Deferred Items (At Snapshot Time)

* **Read-only flag cache:** Keeping flags read-only (`setcc` as the sole move, no flag slots or GPR→flag reloads) avoids flag-slot/`pmove` complexity while `adcx`/`adox` touch only `cf`/`of`.
* **Backend entry gate (`Fn.backendOk`):** Separates `VecIsa.isAbiVec` (`assignSig`/`isLegalTy`) from `vecSlotWidth` (`hasBank` `.w64` `mkpair`/`unpair` bridges); passes `op.args` to `supportsScalarOp`/`supportsVecOp`/`supportsOp` (admitting `ChaCha` uniform-`.imm` `rotr v4i32`); splits `hasBitCounts` from `hasPopcnt` (`core_bitcount_and_fp_gates`); enforces arity bounds (`Fn.assign_of_backendOk`). `.hlt` emits `[]`.
* **Items out of scope in the initial design:** (1) `.remat` `Loc` kind (replaced by lexical `defs`); (2) pressure-oracle export; (3) tail calls (general `call + ret` deferred; `exitJmp` is solely for `Expr.exit` after `epilogue`); (4) `Fn.frameBytes`; (5) `link_rec` / SCC recursion bounds (later implemented in `LinkRec`/`LinkScc`); (6) `Env.Local`; (7) `OpCode.intrinsic`.
