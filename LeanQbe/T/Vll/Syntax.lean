module

public import LeanQbe.T.Vll.Arch

/-!
# Target-Neutral `BedrockMach` L1 Syntax (`Vll.Syntax`)

Defines the post-Rega target-neutral machine IR syntax parameterized by `A : Arch`:

* `Src A`: register or 64-bit immediate RHS operand.
* `Instr A`: flat directive/instruction set (`label`, `mov`, `movi`, `alu`, `cmp`, `test`,
  `clearFlags`, `setcc`, `load`, `store`, `slotSt`, `slotLd`, `prologue`, `epilogue`, `canonAbi`,
  `jmp`, `jcc`, `jnzGpr`, `call`, `icall`, `ret`, `exitJmp`, `tailJmpR`, `symAddr`, `ijmp`, `pad`,
  `native`), directly usable as `Isa.Directive` and `Machine.Directive`.
* `Term A`, `Block A`, `VllCodeMap A`: structured basic-block / code-map representation with
  layout-order fall-through elision, `addrTaken` CET/BTI landing-pad checks, and symbol-indexed
  lookup.
* Pure structural analyses (`uses`, `defs`, `clobGpr`, `clobVec`, `clobFlags`, `syms`,
  `isStraightLine`, `Block.toInstrs`, `VllCodeMap.flatten`, `VllCodeMap.padsOk`).

Zero `Kraken.X64`, `Kraken.AArch64`, `Amd64`, `Arm64`, or `*Lemmas*` imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open LeanQbe.T

/-! ## 1. Source Operands (`Src A`) -/

/-- Right-hand source operand for `alu`, `cmp`, and `test`. -/
inductive Src (A : Arch) : Type where
  | reg (r : A.Reg)
  | imm (v : BitVec 64)

/-- Evaluate `Src A` to a 64-bit word under register file `gpr`. -/
@[expose] def Src.eval {A : Arch} (gpr : A.Reg → BitVec 64) : Src A → BitVec 64
  | .reg r => gpr r
  | .imm v => v

/-- Evaluate `Src A` truncated to width `w`. -/
@[expose] def Src.evalW {A : Arch} (w : Width) (gpr : A.Reg → BitVec 64) (s : Src A) :
    BitVec w.bits :=
  (s.eval gpr).setWidth w.bits

/-- Registers read by a `Src A`. -/
@[expose] def Src.regs {A : Arch} : Src A → List A.Reg
  | .reg r => [r]
  | .imm _ => []

/-! ## 2. Flat Target-Neutral Machine Instructions (`Instr A`) -/

/-- Target-neutral `BedrockMach` L1 instruction / directive type, parameterized by `A : Arch`.
First-class constructors cover all core GPR, memory, frame, ABI, and control-flow operations;
`.native d` is the escape hatch for target-specific fused / SIMD / exotic directives. -/
inductive Instr (A : Arch) : Type where
  /-- Code label anchor (no operational effect; establishes `labelAddr`). -/
  | label (s : Sym)
  /-- Register-to-register move at width `w` (writes via `A.writeSub w`). -/
  | mov (w : Width) (rd rs : A.Reg)
  /-- 64-bit immediate load into `rd` (preserving flags). -/
  | movi (rd : A.Reg) (imm : BitVec 64)
  /-- Core integer ALU operation (`rd := op w lhs rhs`), optionally updating flags. -/
  | alu (op : CoreAlu) (w : Width) (rd lhs : A.Reg) (rhs : Src A) (setFlags : Bool := false)
  /-- Compare `lhs` and `rhs` at width `w`, updating architectural flags. -/
  | cmp (w : Width) (lhs : A.Reg) (rhs : Src A)
  /-- Bitwise AND test `lhs &&& rhs` at width `w`, updating architectural flags. -/
  | test (w : Width) (lhs : A.Reg) (rhs : Src A)
  /-- Clear architectural status flags so every `c ∈ A.zeroFlags` evaluates to `false`. -/
  | clearFlags
  /-- Materialize condition code `c` (`0`/`1`) into `rd` (via `A.writeSub .w8`). -/
  | setcc (rd : A.Reg) (c : A.Cond)
  /-- Memory load at width `w` with extension policy `ext` (`zx` / `sx` / `sub`). -/
  | load (w : Width) (ext : LoadExt) (rd : A.Reg) (addr : AddrArg A.Reg)
  /-- Memory store of low `w.bits` bits of `rs` to `addr`. -/
  | store (w : Width) (rs : A.Reg) (addr : AddrArg A.Reg)
  /-- Store 64-bit register `rs` to stack slot `i` (`[sp + 8 * i]`). -/
  | slotSt (i : Nat) (rs : A.Reg)
  /-- Load 64-bit stack slot `i` (`[sp + 8 * i]`) into `rd`. -/
  | slotLd (rd : A.Reg) (i : Nat)
  /-- Allocate stack frame for `ns` 8-byte slots (and spill `lr` when `raKind = .linkReg`). -/
  | prologue (ns : Nat)
  /-- Restore `lr` (when `raKind = .linkReg`) and deallocate stack frame for `ns` slots. -/
  | epilogue (ns : Nat)
  /-- Canonicalize sub-word register `r` to ABI zero-extended 64-bit form for type `t`. -/
  | canonAbi (t : Ty) (r : A.Reg)
  /-- Direct unconditional branch to label `l`. -/
  | jmp (l : Sym)
  /-- Conditional branch to label `l` when `A.evalCond flags c = true`. -/
  | jcc (c : A.Cond) (l : Sym)
  /-- Branch to label `l` when low byte of `r` is nonzero. -/
  | jnzGpr (r : A.Reg) (l : Sym)
  /-- Direct hardware call to `sym` (RAS/CET-safe: pushes return PC or writes `lr`). -/
  | call (sym : Sym)
  /-- Indirect hardware call to code address in `r` (RAS/CET-safe). -/
  | icall (r : A.Reg)
  /-- Hardware return (pops return PC from `[sp]` or branches to `lr`). -/
  | ret
  /-- Direct tail jump to exit symbol `sym`. -/
  | exitJmp (sym : Sym)
  /-- Indirect tail jump to code address in `r`. -/
  | tailJmpR (r : A.Reg)
  /-- Materialize 64-bit address of symbol `sym` into `rd`. -/
  | symAddr (sym : Sym) (rd : A.Reg)
  /-- Open word-level indirect jump to address in `r` (L0/VM dispatch/coroutines). -/
  | ijmp (r : A.Reg)
  /-- Hardware indirect-branch landing pad (`endbr64` / `bti`; semantically a nop). -/
  | pad (k : PadKind)
  /-- Target-specific native directive escape hatch (1:1 lowered by `asm_A`). -/
  | native (d : A.Native)

/-! ## 3. Structural Queries on `Instr A` -/

/-- Extract label name if `i` is `.label s`. -/
@[expose] def Instr.label? {A : Arch} : Instr A → Option Sym
  | .label s => some s
  | _ => none

/-- True iff `i` is a `.native` escape-hatch directive. -/
@[expose] def Instr.isNative {A : Arch} : Instr A → Bool
  | .native _ => true
  | _ => false

/-- True iff `i` is a control-transfer instruction (or a control-transfer `.native`). -/
@[expose] def Instr.isControl {A : Arch} : Instr A → Bool
  | .jmp _ | .jcc _ _ | .jnzGpr _ _ | .call _ | .icall _
  | .ret | .exitJmp _ | .tailJmpR _ | .ijmp _ => true
  | .native d => (A.nativeEffect d).isControl
  | _ => false

/-- True iff `i` always falls through (not a control transfer). -/
@[expose] def Instr.isStraightLine {A : Arch} (i : Instr A) : Bool :=
  !i.isControl

/-- GPRs read by instruction `i`. -/
@[expose] def Instr.uses {A : Arch} : Instr A → List A.Reg
  | .label _ | .movi _ _ | .clearFlags | .setcc _ _
  | .jmp _ | .jcc _ _ | .call _ | .exitJmp _ | .symAddr _ _ | .pad _ => []
  | .mov _ _ rs => [rs]
  | .alu _ _ _ lhs rhs _ => lhs :: rhs.regs
  | .cmp _ lhs rhs | .test _ lhs rhs => lhs :: rhs.regs
  | .load _ _ _ a => a.regs
  | .store _ rs a => rs :: a.regs
  | .slotSt _ rs => [A.abi.sp, rs]
  | .slotLd _ _ => [A.abi.sp]
  | .prologue _ => A.abi.sp :: A.abi.raRegs
  | .epilogue _ => [A.abi.sp]
  | .canonAbi _ r => [r]
  | .jnzGpr r _ | .icall r | .tailJmpR r | .ijmp r => [r]
  | .ret => A.abi.sp :: A.abi.raRegs
  | .native d => (A.nativeEffect d).gUses

/-- GPRs explicitly defined (written) by instruction `i`. -/
@[expose] def Instr.defs {A : Arch} : Instr A → List A.Reg
  | .label _ | .cmp _ _ _ | .test _ _ _ | .clearFlags | .store _ _ _
  | .slotSt _ _ | .jmp _ | .jcc _ _ | .jnzGpr _ _ | .exitJmp _
  | .tailJmpR _ | .ijmp _ | .pad _ => []
  | .mov _ rd _ | .movi rd _ | .alu _ _ rd _ _ _ | .setcc rd _
  | .load _ _ rd _ | .slotLd rd _ | .canonAbi _ rd | .symAddr _ rd => [rd]
  | .prologue _ => [A.abi.sp]
  | .epilogue _ => A.abi.sp :: A.abi.raRegs
  | .call _ | .icall _ => A.abi.sp :: A.abi.raRegs
  | .ret => match A.abi.raKind with | .stack => [A.abi.sp] | .linkReg _ => []
  | .native d => (A.nativeEffect d).gClob

/-- Upper bound on GPRs potentially modified by `i`. -/
@[expose] def Instr.clobGpr {A : Arch} (i : Instr A) : List A.Reg :=
  i.defs

/-- Upper bound on vector registers potentially modified by `i`. -/
@[expose] def Instr.clobVec {A : Arch} : Instr A → List A.VReg
  | .native d => (A.nativeEffect d).vClob
  | _ => []

/-- Flag clobber mask of instruction `i`. -/
@[expose] def Instr.clobFlags {A : Arch} : Instr A → FlagMask
  | .alu op _ _ _ _ sf => A.aluClob op sf
  | .cmp _ _ _ => A.cmpClob
  | .test _ _ _ => A.testClob
  | .clearFlags => FlagMask.all
  | .prologue _ => A.abi.prologueClob
  | .epilogue _ => A.abi.epilogueClob
  | .canonAbi t _ => A.abi.canonAbiClob t
  | .jnzGpr _ _ => A.jnzGprClob
  | .native d => (A.nativeEffect d).fClob
  | _ => FlagMask.none

/-- Symbols referenced by instruction `i`. -/
@[expose] def Instr.syms {A : Arch} : Instr A → List Sym
  | .label s | .jmp s | .jcc _ s | .jnzGpr _ s
  | .call s | .exitJmp s | .symAddr s _ => [s]
  | _ => []

/-! ## 4. Structured Basic Blocks (`Term A`, `Block A`) & Code Maps (`VllCodeMap A`) -/

/-- Basic-block terminator for `BedrockMach` L1 XCAP code maps. -/
inductive Term (A : Arch) : Type where
  /-- Fall through to the statically next block `next`. -/
  | fall (next : Sym)
  /-- Direct unconditional jump to label `l`. -/
  | jmp (l : Sym)
  /-- Conditional branch: jump to `taken` if `evalCond flags c = true`, else `fall`. -/
  | jcc (c : A.Cond) (taken fall : Sym)
  /-- Branch to `taken` if low byte of `r` is nonzero, else `fall`. -/
  | jnzGpr (r : A.Reg) (taken fall : Sym)
  /-- Hardware direct call to `sym`, returning to continuation label `retLabel` (RAS/CET-safe). -/
  | call (sym retLabel : Sym)
  /-- Hardware indirect call to address in `r`, returning to `retLabel` (RAS/CET-safe). -/
  | icall (r : A.Reg) (retLabel : Sym)
  /-- Hardware return (pops `[sp]` or jumps to `lr`). -/
  | ret
  /-- Direct tail jump to exit symbol `sym`. -/
  | exitJmp (sym : Sym)
  /-- Indirect tail jump to address in `r`. -/
  | tailJmpR (r : A.Reg)
  /-- Open word-level indirect jump to address in `r`. -/
  | ijmp (r : A.Reg)
  /-- Halt execution with exit word `gpr r` (XCAP termination). -/
  | halt (r : A.Reg)
  /-- Native escape-hatch terminator (must jump or halt under `A.nativeStep`). -/
  | nativeTerm (d : A.Native)

/-- Static successor labels of a block terminator. -/
@[expose] def Term.succs {A : Arch} : Term A → List Sym
  | .fall n | .jmp n | .exitJmp n => [n]
  | .jcc _ t f | .jnzGpr _ t f => [t, f]
  | .call sym retL => [sym, retL]
  | .icall _ retL => [retL]
  | .ret | .tailJmpR _ | .ijmp _ | .halt _ | .nativeTerm _ => []

/-- Symbols referenced by a block terminator. -/
@[expose] def Term.syms {A : Arch} (t : Term A) : List Sym :=
  t.succs

/-- True iff `t` performs an open indirect control transfer. -/
@[expose] def Term.isOpenIndirect {A : Arch} : Term A → Bool
  | .icall _ _ | .tailJmpR _ | .ijmp _ => true
  | _ => false

/-- GPRs read by a block terminator. -/
@[expose] def Term.uses {A : Arch} : Term A → List A.Reg
  | .jnzGpr r _ _ | .icall r _ | .tailJmpR r | .ijmp r | .halt r => [r]
  | .ret => A.abi.sp :: A.abi.raRegs
  | .nativeTerm d => (A.nativeEffect d).gUses
  | _ => []

/-- Lower a terminator to flat `Instr A` instructions, eliding unconditional jumps to
`nextLabel?` when the target is laid out immediately after this block. -/
@[expose] def Term.toInstrs {A : Arch} (nextLabel? : Option Sym) : Term A → List (Instr A)
  | .fall n => if nextLabel? == some n then [] else [.jmp n]
  | .jmp l => if nextLabel? == some l then [] else [.jmp l]
  | .jcc c t f =>
    .jcc c t :: (if nextLabel? == some f then [] else [.jmp f])
  | .jnzGpr r t f =>
    .jnzGpr r t :: (if nextLabel? == some f then [] else [.jmp f])
  | .call sym retL =>
    .call sym :: (if nextLabel? == some retL then [] else [.jmp retL])
  | .icall r retL =>
    .icall r :: (if nextLabel? == some retL then [] else [.jmp retL])
  | .ret => [.ret]
  | .exitJmp sym => [.exitJmp sym]
  | .tailJmpR r => [.tailJmpR r]
  | .ijmp r => [.ijmp r]
  | .halt _ => []
  | .nativeTerm d => [.native d]

/-- A first-order basic block at label `label` with optional CET/BTI landing pad `pad?`,
straight-line instruction body `body`, and terminator `term`. -/
structure Block (A : Arch) : Type where
  label : Sym
  pad? : Option PadKind := none
  body : List (Instr A) := []
  term : Term A

/-- True iff `b` starts with a hardware landing pad (`endbr64` / `bti`). -/
@[expose] def Block.hasLandingPad {A : Arch} (b : Block A) : Bool :=
  b.pad?.isSome

/-- True iff every instruction in `b.body` is straight-line. -/
@[expose] def Block.isBodyStraightLine {A : Arch} (b : Block A) : Bool :=
  b.body.all Instr.isStraightLine

/-- Symbols referenced inside `b` (including its own label, body, and terminator). -/
@[expose] def Block.syms {A : Arch} (b : Block A) : List Sym :=
  b.label :: (b.body.flatMap Instr.syms ++ b.term.syms)

/-- Flatten a block into `Instr A` directives, eliding fall-through jumps to `nextLabel?`. -/
@[expose] def Block.toInstrs {A : Arch} (nextLabel? : Option Sym) (b : Block A) :
    List (Instr A) :=
  .label b.label ::
    (match b.pad? with | some k => [.pad k] | none => []) ++
    b.body ++ b.term.toInstrs nextLabel?

/-- Ordered `BedrockMach` L1 code map pairing basic blocks with a symbol-address layout `symAddr`
and the `addrTaken` set of escaped jump targets (for static CET/BTI landing-pad checks). -/
structure VllCodeMap (A : Arch) : Type where
  blocks : List (Block A)
  symAddr : Sym → BitVec 64
  addrTaken : List Sym := []

/-- Labels of all blocks in layout order. -/
@[expose] def VllCodeMap.labels {A : Arch} (cm : VllCodeMap A) : List Sym :=
  cm.blocks.map Block.label

/-- Look up the first block with label `l`. -/
@[expose] def VllCodeMap.lookupLabel {A : Arch} (cm : VllCodeMap A) (l : Sym) :
    Option (Block A) :=
  cm.blocks.find? (fun b => b.label == l)

/-- Look up the first block mapped to code address `pc`. -/
@[expose] def VllCodeMap.lookupPc {A : Arch} (cm : VllCodeMap A) (pc : BitVec 64) :
    Option (Block A) :=
  cm.blocks.find? (fun b => cm.symAddr b.label == pc)

/-- Flatten ordered blocks into a flat instruction stream, passing each block the label of the
immediately following block to enable fall-through jump elision. -/
@[expose] def flattenBlocks {A : Arch} : List (Block A) → List (Instr A)
  | [] => []
  | [b] => b.toInstrs none
  | b :: bNext :: rest => b.toInstrs (some bNext.label) ++ flattenBlocks (bNext :: rest)

/-- Flatten a `VllCodeMap A` into a flat `List (Instr A)` stream. -/
@[expose] def VllCodeMap.flatten {A : Arch} (cm : VllCodeMap A) : List (Instr A) :=
  flattenBlocks cm.blocks

/-- Check whether all block labels in `cm` are pairwise distinct. -/
@[expose] def VllCodeMap.labelsUnique {A : Arch} (cm : VllCodeMap A) : Bool :=
  let rec go : List Sym → Bool
    | [] => true
    | l :: ls => !ls.contains l && go ls
  go cm.labels

/-- Check whether all block addresses in `cm` are pairwise distinct. -/
@[expose] def VllCodeMap.addrsUnique {A : Arch} (cm : VllCodeMap A) : Bool :=
  let rec go : List (BitVec 64) → Bool
    | [] => true
    | p :: ps => !ps.contains p && go ps
  go (cm.blocks.map fun b => cm.symAddr b.label)

/-- Static CET/BTI landing-pad check: every `l ∈ cm.addrTaken` present in `cm` starts with a
landing pad (`pad? = some _`). -/
@[expose] def VllCodeMap.padsOk {A : Arch} (cm : VllCodeMap A) : Bool :=
  cm.addrTaken.all fun l =>
    match cm.lookupLabel l with
    | some b => b.hasLandingPad
    | none => true

/-- Check whether every block in `cm` has a straight-line body. -/
@[expose] def VllCodeMap.bodiesStraightLine {A : Arch} (cm : VllCodeMap A) : Bool :=
  cm.blocks.all Block.isBodyStraightLine

/-- Well-formedness predicate for a `VllCodeMap A`: distinct block addresses, distinct labels,
and valid landing pads on all escaped `addrTaken` labels. -/
structure VllCodeMap.Wf {A : Arch} (cm : VllCodeMap A) : Prop where
  labels_nodup : cm.labels.Nodup
  addrs_inj : ∀ b₁ ∈ cm.blocks, ∀ b₂ ∈ cm.blocks,
    cm.symAddr b₁.label = cm.symAddr b₂.label → b₁ = b₂
  pads_ok : ∀ l ∈ cm.addrTaken, ∀ b, cm.lookupLabel l = some b → b.hasLandingPad = true

/-! ## 5. Basic Structural Lemmas -/

theorem Block.toInstrs_head_label {A : Arch} (nextLabel? : Option Sym) (b : Block A) :
    (b.toInstrs nextLabel?)[0]? = some (.label b.label) := by
  simp [Block.toInstrs]

theorem VllCodeMap.lookupPc_mem {A : Arch} {cm : VllCodeMap A} {pc : BitVec 64} {b : Block A}
    (h : cm.lookupPc pc = some b) :
    b ∈ cm.blocks ∧ cm.symAddr b.label = pc := by
  have hmem := List.mem_of_find?_eq_some h
  have hpred := List.find?_some h
  exact ⟨hmem, beq_iff_eq.mp hpred⟩

theorem VllCodeMap.lookupLabel_mem {A : Arch} {cm : VllCodeMap A} {l : Sym} {b : Block A}
    (h : cm.lookupLabel l = some b) :
    b ∈ cm.blocks ∧ b.label = l := by
  have hmem := List.mem_of_find?_eq_some h
  have hpred := List.find?_some h
  exact ⟨hmem, beq_iff_eq.mp hpred⟩

private theorem find?_eq_some_of_unique {α : Type} (p : α → Bool) :
    ∀ {xs : List α} {x : α}, x ∈ xs → p x = true →
      (∀ y ∈ xs, p y = true → y = x) → xs.find? p = some x
  | [], _, hx, _, _ => nomatch hx
  | y :: ys, x, hx, hpx, huniq => by
    simp only [List.find?]
    cases hpy : p y with
    | true =>
      have hyx : y = x := huniq y List.mem_cons_self hpy
      subst hyx; rfl
    | false =>
      rcases List.mem_cons.mp hx with rfl | hmem
      · rw [hpx] at hpy; cases hpy
      · exact find?_eq_some_of_unique p hmem hpx
          (fun z hz hpz => huniq z (List.mem_cons_of_mem _ hz) hpz)

theorem VllCodeMap.lookupPc_of_wf {A : Arch} {cm : VllCodeMap A} (hwf : cm.Wf)
    {b : Block A} (hb : b ∈ cm.blocks) :
    cm.lookupPc (cm.symAddr b.label) = some b := by
  refine find?_eq_some_of_unique _ hb (by simp) ?_
  intro b' hb' heq
  exact hwf.addrs_inj b' hb' b hb (beq_iff_eq.mp heq)

theorem VllCodeMap.padsOk_spec {A : Arch} {cm : VllCodeMap A} (h : cm.padsOk = true)
    {l : Sym} (hl : l ∈ cm.addrTaken) {b : Block A} (hb : cm.lookupLabel l = some b) :
    b.hasLandingPad = true := by
  have hall := List.all_eq_true.mp h l hl
  rw [hb] at hall
  exact hall

theorem Term.toInstrs_fall_elided {A : Arch} (l : Sym) :
    (Term.fall (A := A) l).toInstrs (some l) = [] := by
  simp [Term.toInstrs]

theorem Term.toInstrs_jmp_elided {A : Arch} (l : Sym) :
    (Term.jmp (A := A) l).toInstrs (some l) = [] := by
  simp [Term.toInstrs]

end LeanQbe.T.Vll
