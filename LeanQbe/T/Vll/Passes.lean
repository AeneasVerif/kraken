module

public import LeanQbe.T.Vll.Syntax

/-!
# Target-Neutral Verified VLLIR Machine Peephole Passes (`Vll.Passes`)

Pure, computable, architecture-free machine peephole optimization passes over `BedrockMach` L1
(`Instr A`, `Block A`, `VllCodeMap A`) for any `A : Arch`, with zero `Arm64`, `Amd64`,
`Kraken.X64`, `Kraken.AArch64`, or `*Lemmas*` imports:

* **No-op elimination (`elimFilter`, `elimSelfMov`, `elimZeroFrame`, `elimCanonAbi64`,
  `elimNoop`, `elimNoopBody`):** drops 64-bit self-moves (`.mov .w64 rd rd`, strictly preserving
  sub-word zero-extension semantics), zero-frame `.prologue 0` / `.epilogue 0` when `A` has a
  stack no-op zero frame (`isZeroPrologueNoop` / `isZeroEpilogueNoop`), and redundant 64-bit
  `.canonAbi (.bits 64) r` when `isCanonAbi64Noop`.
* **Two-instruction straight-line peephole window (`elimWindow`, `elimRedundantWindowCore`,
  `elimRedundantWindow`):** drops redundant `.clearFlags` before `.clearFlags`/`.cmp`/`.test`,
  duplicate/move-back `.mov .w64` pairs, and dead pure GPR writes immediately overwritten by
  `.movi`, non-self `.mov .w64`, or `.symAddr`.
* **Jump / trampoline / duplicate-label threading (`threadJmp`):** threads `.jmp`/`.jcc`/`.jnzGpr`
  through empty `.label l; .label l'` aliases and `.label l; .jmp l'` trampolines, and inlines
  `.jmp l` to `.ret` when `.label l` immediately precedes `.ret`.
* **Branch inversion over label (`invertJccJmp`):** rewrites `[.jcc c l₁, .jmp l₂, .label l₁]`
  into `[.jcc (A.negCond c) l₂, .label l₁]` via `A.negCond`.
* **Fall-through branch elision (`elimFallthroughJmp`, `elimFallthrough`):** drops
  `[.jmp l, .label l]` and `[.jcc c l, .label l]` into `[.label l]`.
* **Composed pipelines & structured `Block`/`VllCodeMap` passes:** `optBody`, `passPipeWf`,
  `passPipeCore`, `passPipe`, `optBlockBody`, `optBlocks`, `optCodeMapBody`, `threadCodeMap`,
  `optCodeMap`, and `PassMetrics`.

Every pass preserves the exact ordered list of defined `.label` directives (`definedLabels`),
`NoVllLab`, `LabelsUnique`, and call-site return anchors. Soundness proofs live in
`LeanQbe.T.Vll.PassesLemmas`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open LeanQbe.T

/-! ## 1. Architecture No-Op Queries & Structural Classifiers -/

/-- True iff `.prologue 0` is an architectural stack/flag no-op on `A` (`.stack` return
convention with `frameSize 0 = 0` and zero flag clobbers). -/
@[expose] def Arch.isZeroPrologueNoop (A : Arch) : Bool :=
  match A.abi.raKind with
  | .stack => A.abi.frameSize 0 == 0 && A.abi.prologueClob == FlagMask.none
  | .linkReg _ => false

/-- True iff `.epilogue 0` is an architectural stack/flag no-op on `A` (`.stack` return
convention with `frameSize 0 = 0` and zero flag clobbers). -/
@[expose] def Arch.isZeroEpilogueNoop (A : Arch) : Bool :=
  match A.abi.raKind with
  | .stack => A.abi.frameSize 0 == 0 && A.abi.epilogueClob == FlagMask.none
  | .linkReg _ => false

/-- True iff `.canonAbi (.bits 64) r` clobbers no status flags (making it a full no-op since
`canonAbiVal (.bits 64) v = v`). -/
@[expose] def Arch.isCanonAbi64Noop (A : Arch) : Bool :=
  A.abi.canonAbiClob (.bits 64) == FlagMask.none

/-- True iff `i` is a hardware call instruction (`.call` or `.icall`) whose immediate successor
serves as its return-site anchor. -/
@[expose] def Instr.isCall {A : Arch} : Instr A → Bool
  | .call _ | .icall _ => true
  | _ => false

/-- True iff `i` is a full-width 64-bit self-move (`.mov .w64 rd rd`). Sub-word moves
(`.w8`/`.w16`/`.w32`) are deliberately excluded because `A.writeSub` may zero-extend upper bits. -/
@[expose] def Instr.isSelfMov64 {A : Arch} : Instr A → Bool
  | .mov .w64 rd rs => rd == rs
  | _ => false

/-- True iff `i` is a redundant 0-slot `.prologue 0` or `.epilogue 0` on architecture `A`. -/
@[expose] def Instr.isZeroFrameNoop (A : Arch) : Instr A → Bool
  | .prologue 0 => A.isZeroPrologueNoop
  | .epilogue 0 => A.isZeroEpilogueNoop
  | _ => false

/-- True iff `i` is a no-op 64-bit `.canonAbi (.bits 64) r` on architecture `A`. -/
@[expose] def Instr.isCanonAbi64Noop (A : Arch) : Instr A → Bool
  | .canonAbi (.bits 64) _ => A.isCanonAbi64Noop
  | _ => false

/-- True iff `i` is a single-instruction semantic no-op on architecture `A` (excluding landing
pads `.pad k`, which are preserved for CET/BTI `padsOk` invariants). -/
@[expose] def Instr.isNoop (A : Arch) (i : Instr A) : Bool :=
  i.isSelfMov64 || i.isZeroFrameNoop A || i.isCanonAbi64Noop A

/-- Extract the sole destination GPR of a total, flag- and memory-preserving, straight-line
GPR write instruction. -/
@[expose] def Instr.pureGprWriteDst? {A : Arch} : Instr A → Option A.Reg
  | .mov _ rd _ => some rd
  | .movi rd _ => some rd
  | .setcc rd _ => some rd
  | .symAddr _ rd => some rd
  | _ => none

/-- True iff `i` unconditionally overwrites all 64 bits of `r` without reading `r`, while
preserving all other GPRs, vector registers, flags, and memory. -/
@[expose] def Instr.overwritesFullGpr {A : Arch} (r : A.Reg) : Instr A → Bool
  | .movi rd _ => rd == r
  | .mov .w64 rd rs => rd == r && rs != r
  | .symAddr _ rd => rd == r
  | _ => false

/-- True iff `i` unconditionally overwrites architectural status flags independently of prior
`.clearFlags`. -/
@[expose] def Instr.overwritesClearFlags {A : Arch} : Instr A → Bool
  | .clearFlags | .cmp _ _ _ | .test _ _ _ => true
  | _ => false

/-- Ordered list of all `.label l` symbols defined in a flat instruction stream. -/
@[expose] def definedLabels {A : Arch} : List (Instr A) → List Sym
  | [] => []
  | .label l :: rest => l :: definedLabels rest
  | _ :: rest => definedLabels rest

/-! ## 2. Pass 1: Single-Instruction No-Op Elimination (`elimFilter` / `elimNoop`) -/

/-- Generic straight-line filter dropping every instruction matching `p` (used inside
`Block.body`, which contains no hardware calls). -/
@[expose] def elimFilterBody {A : Arch} (p : Instr A → Bool) : List (Instr A) → List (Instr A)
  | [] => []
  | i :: rest => if p i then elimFilterBody p rest else i :: elimFilterBody p rest

/-- Worker for `elimFilter` tracking whether the immediately preceding instruction was a hardware
call (`.call` / `.icall`) so return-site anchors are never deleted. -/
@[expose] def elimFilterAux {A : Arch} (p : Instr A → Bool) :
    Bool → List (Instr A) → List (Instr A)
  | _, [] => []
  | afterCall, i :: rest =>
    if !afterCall && p i then
      elimFilterAux p false rest
    else
      i :: elimFilterAux p i.isCall rest

/-- Generic call-anchor-preserving flat filter dropping instructions satisfying `p`. -/
@[expose] def elimFilter {A : Arch} (p : Instr A → Bool) (is : List (Instr A)) :
    List (Instr A) :=
  elimFilterAux p false is

/-- Drop full-width 64-bit self-moves (`.mov .w64 rd rd`) from a flat stream (`A.Wf`-only). -/
@[expose] def elimSelfMov (A : Arch) (is : List (Instr A)) : List (Instr A) :=
  elimFilter (Instr.isSelfMov64 (A := A)) is

/-- Drop redundant zero-frame `.prologue 0`/`.epilogue 0` when `A` has a stack no-op zero frame. -/
@[expose] def elimZeroFrame (A : Arch) (is : List (Instr A)) : List (Instr A) :=
  elimFilter (Instr.isZeroFrameNoop A) is

/-- Drop redundant 64-bit `.canonAbi (.bits 64) r` when `A.isCanonAbi64Noop` holds. -/
@[expose] def elimCanonAbi64 (A : Arch) (is : List (Instr A)) : List (Instr A) :=
  elimFilter (Instr.isCanonAbi64Noop A) is

/-- Drop all single-instruction no-ops (`Instr.isNoop A`) from a straight-line body. -/
@[expose] def elimNoopBody (A : Arch) (is : List (Instr A)) : List (Instr A) :=
  elimFilterBody (Instr.isNoop A) is

/-- Flat pass dropping `.mov .w64 rd rd`, no-op `.prologue 0`/`.epilogue 0`, and no-op
`.canonAbi (.bits 64) r` while preserving every `.label` and call return-site anchor. -/
@[expose] def elimNoop (A : Arch) (is : List (Instr A)) : List (Instr A) :=
  elimFilter (Instr.isNoop A) is

/-! ## 3. Pass 2: Two-Instruction Straight-Line Peephole Window (`elimWindow`) -/

/-- Pure `A.Wf`-only 2-to-1 straight-line rewrite rule (`clearFlags; clearFlags`, duplicate or
move-back `.mov .w64`, and dead pure GPR writes overwritten by `.movi`/`.mov .w64`/`.symAddr`). -/
@[expose] def peepholePairCore? (A : Arch) (i₁ i₂ : Instr A) : Option (Instr A) :=
  match i₁, i₂ with
  | .clearFlags, .clearFlags => some .clearFlags
  | .mov .w64 rd rs, .mov .w64 rd' rs' =>
    if (rd == rs' && rs == rd') || (rd == rd' && rs == rs') then
      some (.mov .w64 rd rs)
    else if rd == rd' && rs' != rd then
      some (.mov .w64 rd' rs')
    else
      none
  | i₁, i₂ =>
    match i₁.pureGprWriteDst? with
    | some r => if i₂.overwritesFullGpr r then some i₂ else none
    | none => none

/-- Full 2-to-1 straight-line rewrite rule extending `peepholePairCore?` with redundant
`.clearFlags` elimination immediately before `.cmp` / `.test`. -/
@[expose] def peepholePair? (A : Arch) (i₁ i₂ : Instr A) : Option (Instr A) :=
  match i₁, i₂ with
  | .clearFlags, i₂ =>
    if i₂.overwritesClearFlags then some i₂ else none
  | i₁, i₂ => peepholePairCore? A i₁ i₂

/-- Generic linear-time 2-instruction straight-line peephole pass driven by `rule`. -/
@[expose] def elimWindow {A : Arch} (rule : Instr A → Instr A → Option (Instr A)) :
    List (Instr A) → List (Instr A)
  | [] => []
  | [i] => [i]
  | i₁ :: i₂ :: rest =>
    match rule i₁ i₂ with
    | some i' => i' :: elimWindow rule rest
    | none => i₁ :: elimWindow rule (i₂ :: rest)

/-- `A.Wf`-only 2-instruction straight-line peephole pass. -/
@[expose] def elimRedundantWindowCore (A : Arch) (is : List (Instr A)) : List (Instr A) :=
  elimWindow (peepholePairCore? A) is

/-- Full 2-instruction straight-line peephole pass (including `clearFlags; cmp/test`). -/
@[expose] def elimRedundantWindow (A : Arch) (is : List (Instr A)) : List (Instr A) :=
  elimWindow (peepholePair? A) is

/-! ## 4. Pass 3: Jump / Duplicate-Label / `jmp`-to-`ret` Threading (`threadJmp`) -/

/-- Single-step trampoline summary for a label `l`. -/
inductive JmpAction where
  /-- Label `l` immediately aliases or jumps unconditionally to `l'`. -/
  | toLabel (l' : Sym)
  /-- Label `l` immediately precedes `.ret`. -/
  | toRet
  deriving DecidableEq, Repr

/-- Collect immediate trampoline actions (`label l; label l'`, `label l; jmp l'`, `label l; ret`)
from a flat instruction stream without modifying any label definitions. -/
@[expose] def buildJmpTable (A : Arch) : List (Instr A) → List (Sym × JmpAction)
  | [] => []
  | .label l :: .label l' :: rest =>
    let tail := buildJmpTable A (.label l' :: rest)
    if l != l' then (l, .toLabel l') :: tail else tail
  | .label l :: .jmp l' :: rest =>
    let tail := buildJmpTable A (.jmp l' :: rest)
    if l != l' then (l, .toLabel l') :: tail else tail
  | .label l :: .ret :: rest =>
    (l, .toRet) :: buildJmpTable A (.ret :: rest)
  | _ :: rest => buildJmpTable A rest

/-- Look up the first recorded `JmpAction` for label `l`. -/
@[expose] def lookupJmpTable (tbl : List (Sym × JmpAction)) (l : Sym) : Option JmpAction :=
  (tbl.find? fun p => p.1 == l).map Prod.snd

/-- Thread a single instruction using trampoline table `tbl` (length-preserving 1:1 rewrite). -/
@[expose] def threadInstr (A : Arch) (tbl : List (Sym × JmpAction)) : Instr A → Instr A
  | .jmp l =>
    match lookupJmpTable tbl l with
    | some (.toLabel l') => .jmp l'
    | some .toRet => .ret
    | none => .jmp l
  | .jcc c l =>
    match lookupJmpTable tbl l with
    | some (.toLabel l') => .jcc c l'
    | _ => .jcc c l
  | .jnzGpr r l =>
    match lookupJmpTable tbl l with
    | some (.toLabel l') => .jnzGpr r l'
    | _ => .jnzGpr r l
  | i => i

/-- Length-preserving jump / alias / `jmp`-to-`ret` threading pass over `List (Instr A)`. -/
@[expose] def threadJmp (A : Arch) (is : List (Instr A)) : List (Instr A) :=
  let tbl := buildJmpTable A is
  is.map (threadInstr A tbl)

/-- Labels that `threadJmp A is` may bypass as trampoline entries. -/
@[expose] def threadedLabels (A : Arch) (is : List (Instr A)) : List Sym :=
  (buildJmpTable A is).map Prod.fst

/-! ## 5. Pass 4: `jcc` + `jmp` Branch Inversion over Label (`invertJccJmp`) -/

/-- Rewrite `[.jcc c l₁, .jmp l₂, .label l₁, ...]` into `[.jcc (A.negCond c) l₂, .label l₁, ...]`
using `A.negCond`, keeping `.label l₁` intact. -/
@[expose] def invertJccJmp (A : Arch) : List (Instr A) → List (Instr A)
  | [] => []
  | .jcc c l₁ :: .jmp l₂ :: .label l₃ :: rest =>
    if l₁ == l₃ then
      .jcc (A.negCond c) l₂ :: invertJccJmp A (.label l₃ :: rest)
    else
      .jcc c l₁ :: invertJccJmp A (.jmp l₂ :: .label l₃ :: rest)
  | i :: rest => i :: invertJccJmp A rest

/-! ## 6. Pass 5: Fall-Through `jmp` & `jcc` Elision (`elimFallthrough`) -/

/-- Worker for `elimFallthrough` tracking whether the immediately preceding instruction was a
hardware call so return-site anchors are never deleted. When `includeJcc = true`, redundant
conditional branches to the immediately following label (`[.jcc c l, .label l]`) are also
elided. -/
@[expose] def elimFallthroughAux (A : Arch) (includeJcc : Bool) :
    Bool → List (Instr A) → List (Instr A)
  | _, [] => []
  | afterCall, .jmp l₁ :: .label l₂ :: rest =>
    if !afterCall && l₁ == l₂ then
      elimFallthroughAux A includeJcc false (.label l₂ :: rest)
    else
      .jmp l₁ :: elimFallthroughAux A includeJcc false (.label l₂ :: rest)
  | afterCall, .jcc c l₁ :: .label l₂ :: rest =>
    if includeJcc && !afterCall && l₁ == l₂ then
      elimFallthroughAux A includeJcc false (.label l₂ :: rest)
    else
      .jcc c l₁ :: elimFallthroughAux A includeJcc false (.label l₂ :: rest)
  | _, i :: rest => i :: elimFallthroughAux A includeJcc i.isCall rest

/-- Flat pass eliding redundant fall-through `.jmp l` immediately preceding `.label l`. -/
@[expose] def elimFallthroughJmp (A : Arch) (is : List (Instr A)) : List (Instr A) :=
  elimFallthroughAux A false false is

/-- Flat pass eliding redundant fall-through `.jmp l` and `.jcc c l` immediately preceding
`.label l`, preserving every `.label` and call return-site anchor. -/
@[expose] def elimFallthrough (A : Arch) (is : List (Instr A)) : List (Instr A) :=
  elimFallthroughAux A true false is

/-! ## 7. Composed Flat Pipelines & Metrics -/

/-- Composed straight-line body optimizer (`elimRedundantWindow ∘ elimNoopBody`). -/
@[expose] def optBody (A : Arch) (is : List (Instr A)) : List (Instr A) :=
  elimRedundantWindow A (elimNoopBody A is)

/-- Pure `A.Wf`-only straight-line body optimizer (`elimRedundantWindowCore ∘ elimSelfMov`). -/
@[expose] def optBodyWf (A : Arch) (is : List (Instr A)) : List (Instr A) :=
  elimRedundantWindowCore A (elimFilterBody (Instr.isSelfMov64 (A := A)) is)

/-- Pure `A.Wf`-only four-pass flat pipeline
(`elimFallthrough ∘ invertJccJmp ∘ elimRedundantWindowCore ∘ elimSelfMov`), transferring
`FnSpec` under bare `A.Wf` with zero extra flag assumptions or `ra` restrictions. -/
@[expose] def passPipeWf (A : Arch) (is : List (Instr A)) : List (Instr A) :=
  elimFallthrough A (invertJccJmp A (elimRedundantWindowCore A (elimSelfMov A is)))

/-- Four-pass flat peephole pipeline without trampoline label skipping
(`elimFallthrough ∘ invertJccJmp ∘ elimRedundantWindow ∘ elimNoop`), transferring `FnSpec` under
`A.PassWf` with zero restrictions on caller return addresses. -/
@[expose] def passPipeCore (A : Arch) (is : List (Instr A)) : List (Instr A) :=
  elimFallthrough A (invertJccJmp A (elimRedundantWindow A (elimNoop A is)))

/-- Full five-pass verified target-neutral VLLIR peephole pipeline
(`elimFallthrough ∘ invertJccJmp ∘ threadJmp ∘ elimRedundantWindow ∘ elimNoop`). -/
@[expose] def passPipe (A : Arch) (is : List (Instr A)) : List (Instr A) :=
  elimFallthrough A (invertJccJmp A (threadJmp A (elimRedundantWindow A (elimNoop A is))))

/-- Instruction-count reduction metrics for a peephole pass run. -/
structure PassMetrics where
  before : Nat
  after : Nat
  removed : Nat
  deriving DecidableEq, Repr

/-- Compute `PassMetrics` for running `passPipe A` on `is`. -/
@[expose] def passPipeMetrics (A : Arch) (is : List (Instr A)) : PassMetrics :=
  let opt := passPipe A is
  { before := is.length, after := opt.length, removed := is.length - opt.length }

/-! ## 8. Structured Basic-Block & `VllCodeMap` Passes -/

/-- Optimize the straight-line body of a single `Block A`, preserving its label, landing pad,
and terminator. -/
@[expose] def optBlockBody (A : Arch) (b : Block A) : Block A :=
  { b with body := optBody A b.body }

/-- Optimize straight-line bodies across a list of basic blocks. -/
@[expose] def optBlocks (A : Arch) (bs : List (Block A)) : List (Block A) :=
  bs.map (optBlockBody A)

/-- Optimize every block body in a `VllCodeMap A`, preserving `symAddr`, `addrTaken`, landing
pads, labels, and open-module `Xcap.ModOk`. -/
@[expose] def optCodeMapBody (A : Arch) (cm : VllCodeMap A) : VllCodeMap A :=
  { cm with blocks := optBlocks A cm.blocks }

/-- Inspect label `l` in `cm` for an empty-body forwarding trampoline
(`.jmp l'` / `.fall l'` / `.ret`). -/
@[expose] def blockJmpAction (A : Arch) (cm : VllCodeMap A) (l : Sym) : Option JmpAction :=
  match cm.lookupLabel l with
  | some b =>
    if b.body.isEmpty then
      match b.term with
      | .jmp l' => if l != l' then some (.toLabel l') else none
      | .fall l' => if l != l' then some (.toLabel l') else none
      | .ret => some .toRet
      | _ => none
    else none
  | none => none

/-- Thread a block terminator through empty forwarding blocks in `cm`. -/
@[expose] def threadTerm (A : Arch) (cm : VllCodeMap A) : Term A → Term A
  | .fall l =>
    match blockJmpAction A cm l with
    | some (.toLabel l') => .jmp l'
    | some .toRet => .ret
    | none => .fall l
  | .jmp l =>
    match blockJmpAction A cm l with
    | some (.toLabel l') => .jmp l'
    | some .toRet => .ret
    | none => .jmp l
  | .jcc c t f =>
    let t' := match blockJmpAction A cm t with | some (.toLabel lt) => lt | _ => t
    let f' := match blockJmpAction A cm f with | some (.toLabel lf) => lf | _ => f
    .jcc c t' f'
  | .jnzGpr r t f =>
    let t' := match blockJmpAction A cm t with | some (.toLabel lt) => lt | _ => t
    let f' := match blockJmpAction A cm f with | some (.toLabel lf) => lf | _ => f
    .jnzGpr r t' f'
  | t => t

/-- Thread terminators across all blocks of a `VllCodeMap A`, keeping block labels, addresses,
and landing pads unchanged. -/
@[expose] def threadCodeMap (A : Arch) (cm : VllCodeMap A) : VllCodeMap A :=
  { cm with blocks := cm.blocks.map fun b => { b with term := threadTerm A cm b.term } }

/-- Full structured `VllCodeMap A` optimization pipeline (`threadCodeMap ∘ optCodeMapBody`). -/
@[expose] def optCodeMap (A : Arch) (cm : VllCodeMap A) : VllCodeMap A :=
  threadCodeMap A (optCodeMapBody A cm)

/-- Flatten and optimize a `VllCodeMap A` into a flat `List (Instr A)` stream. -/
@[expose] def optCodeMapFlat (A : Arch) (cm : VllCodeMap A) : List (Instr A) :=
  passPipe A (optCodeMap A cm).flatten

end LeanQbe.T.Vll
