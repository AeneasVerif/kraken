module

public import Kraken.OmniSemantics
public import Kraken.SeparationMem
public import Kraken.Data.List.Infix
public import LeanQbe.WP

/-!
# Target signature and function contract (version 0)

The counterpart of QBE's `Target` struct (plan section 2.3) and the function contract `FnSpec`
(plan section 2.4). Generic: this module imports neither `Kraken.X64` nor `Kraken.AArch64`.
Instances live in `LeanQbe/Amd64/` and `LeanQbe/Arm64/`.

An architecture is abstracted as

* `Isa`: executable data only. Registers, register sets, and *snippets*: for each thing the
  lowering emits (move, constant, one per IL operation, store, jumps, return, label) a function
  producing a short list of directives. `Rega.lower` only needs an `Isa`.
* `Target`: an `Isa` plus the machine semantics, abstracted as "from index `k` of the host
  program, eventually `post`", and one step lemma per snippet in continuation form.

Three rules keep the signature small:

1. Flags and other non-register state are dead between snippets. A snippet lemma only speaks about
   the general-purpose registers (`get`) and the data memory (`mem`).
2. A snippet clobbers only its destination and the scratch registers (`Keeps`).
3. Two-address form, immediate ranges and similar encoding details stay inside the snippet.

Every snippet lemma has the shape

```
code at index k of the host  →  side conditions  →
  (∀ s', relation between s and s' → from k + code.length (or a label), eventually post) →
  from k, eventually post
```

so that the generic lowering proof chains them without knowing any instruction.

Version 0.1 covers what the step-1 tracer function (`x = add a b; storel x p; ret x`) and simple
control flow need: one generic snippet for pure operations, loads and stores (each may return `none`
for an unsupported case, and the lowering then fails), jumps on `Truthy` as the IL's `jnz`.
Version 1 (plan step 2b) adds frames, calls and exits.
-/

@[expose] public section

namespace LeanQbe

/-- `n` bytes starting at `a` (wrapping around), with arbitrary contents. -/
def region (a : BitVec 64) (n : Nat) : Mem 64 → Prop :=
  fun f => ∃ bs : List UInt8, bs.length = n ∧ f = bs.At a

/-- The executable part of a target: registers, register sets and snippets. -/
structure Isa where
  /-- General-purpose registers. -/
  Reg : Type
  [decEq : DecidableEq Reg]
  /-- One directive (label or instruction) of the architecture's assembly. -/
  Directive : Type
  /-- The label directive. -/
  label : String → Directive
  /-- The stack pointer. -/
  sp : Reg
  /-- Registers every snippet may clobber. Never allocated. -/
  scratch : List Reg
  /-- Registers the allocator may assign to values (version 0: caller-saved only). -/
  allocatable : List Reg
  /-- Argument registers, in order. -/
  argRegs : List Reg
  /-- Result registers, in order. -/
  retRegs : List Reg
  /-- Registers a function must restore before returning (the stack pointer is separate). -/
  calleeSaved : List Reg
  /-- `mov rd rs`: `rd := rs`. -/
  mov : Reg → Reg → List Directive
  /-- `movi rd c`: `rd := c`. -/
  movi : Reg → Val → List Directive
  /-- `rd := o` for a pure operation `o` on registers and immediates; `none` if unsupported. -/
  op : Op Reg → Reg → Option (List Directive)
  /-- `rd := load{s}{sg} a` at class `k`; `none` if unsupported. -/
  load : Cls → Sz → Bool → Reg → Arg Reg → Option (List Directive)
  /-- `store{s} v, a`; `none` if unsupported. -/
  store : Sz → Arg Reg → Arg Reg → Option (List Directive)
  /-- `jmp l`: jump to label `l`. -/
  jmp : String → List Directive
  /-- `jnz r l`: jump to label `l` if `Truthy r` (low 32 bits nonzero), else fall through. -/
  jnz : Reg → String → List Directive
  /-- `ret`: return to the caller. -/
  ret : List Directive

attribute [instance] Isa.decEq

/-- The variables an operand mentions. -/
def Arg.vars {V : Type} : Arg V → List V
  | .var v => [v]
  | .imm _ => []

/-- The variables an operation mentions. -/
def Op.vars {V : Type} : Op V → List V
  | .bin _ _ a b => a.vars ++ b.vars
  | .cmp _ _ a b => a.vars ++ b.vars
  | .ext _ _ _ a => a.vars
  | .copy _ a => a.vars

/--
A target: an `Isa`, a machine semantics, and one step lemma per snippet.

The semantics is abstracted as a one-step relation `step h` on machine states of a host `h`, in
the omnisemantics style of `Kraken.OmniSemantics` (`step h st P`: one step from `st` ends in `P`).
Runs are `Eventually (step h)`. A state is machine data (`MData`: registers, flags, memory) plus a
program counter (`Addr`). `prog h` is the host program and `addrOf h k` the address of its `k`-th
directive, as in Kraken's `Host`.
-/
structure Target extends Isa where
  /-- Machine data: registers, flags, memory; no program counter. -/
  MData : Type
  /-- Code addresses. -/
  Addr : Type
  /-- Machine states: machine data and a program counter. -/
  State : Type
  /-- A host: a program with a layout. -/
  Host : Type
  get : MData → Reg → Val
  mem : MData → Mem 64
  mkState : MData → Addr → State
  pc : State → Addr
  data : State → MData
  pc_mk : ∀ s a, pc (mkState s a) = a
  data_mk : ∀ s a, data (mkState s a) = s
  mk_eta : ∀ st, mkState (data st) (pc st) = st
  prog : Host → List Directive
  addrOf : Host → Nat → Addr
  /-- The address a label resolves to (in Kraken: the first definition, or `-1`). -/
  labelAddr : Host → String → Addr
  step : Host → State → (State → Prop) → Prop
  /-- Bytes the return address occupies at the stack pointer on entry (x64: 8, AArch64: 0). -/
  raBytes : Nat
  /-- Memory holding return address `ra` for stack pointer `sp` (x64: `ra` at `sp`; AArch64: empty). -/
  RetAddr : Val → Addr → Mem 64 → Prop
  /-- Register part of the return address convention (x64: `True`; AArch64: `x30 = ra`). -/
  raReg : MData → Addr → Prop
  /-- Stack pointer condition on entry to a function (x64: `sp + 8 ≡ 0 mod 16`). -/
  spEntry : Val → Prop

  /- Register-set facts the generic proofs rely on. -/
  sp_not_scratch : sp ∉ scratch
  sp_not_allocatable : sp ∉ allocatable
  scratch_not_allocatable : ∀ r, r ∈ scratch → r ∉ allocatable
  calleeSaved_not_scratch : ∀ r, r ∈ calleeSaved → r ∉ scratch
  calleeSaved_not_allocatable : ∀ r, r ∈ calleeSaved → r ∉ allocatable
  sp_not_calleeSaved : sp ∉ calleeSaved
  argRegs_not_scratch : ∀ r, r ∈ argRegs → r ∉ scratch
  retRegs_not_scratch : ∀ r, r ∈ retRegs → r ∉ scratch
  /-- The return address occupies exactly `raBytes` bytes at the stack pointer. -/
  retAddr_region : ∀ a ra f, RetAddr a ra f → region a raBytes f
  /-- The register part of the return address lives outside allocatable and scratch registers. -/
  raReg_congr : ∀ s s' ra, (∀ r, r ∉ allocatable → r ∉ scratch → get s' r = get s r) →
    raReg s ra → raReg s' ra

  /- Labels. -/
  /-- A label resolves to its first definition. -/
  labelAddr_eq : ∀ {h : Host} {k : Nat} {l : String}, (prog h)[k]? = some (label l) →
    (∀ j, j < k → (prog h)[j]? ≠ some (label l)) → labelAddr h l = addrOf h k
  /-- A label is skipped. -/
  label_spec : ∀ {h : Host} {k : Nat} {l : String} {s : MData} {post : State → Prop},
    (prog h)[k]? = some (label l) →
    Eventually (step h) post (mkState s (addrOf h (k + 1))) →
    Eventually (step h) post (mkState s (addrOf h k))

  /- Snippets. `∀ r, r ∉ clob → get s' r = get s r` is spelled out because `Keeps` is defined
     after the structure. -/
  mov_spec : ∀ {h : Host} {k : Nat} {rd rs : Reg} {s : MData} {post : State → Prop},
    (mov rd rs).IsInfixAt (prog h) k →
    (∀ s', get s' rd = get s rs → (∀ r, r ∉ [rd] → get s' r = get s r) →
      mem s' = mem s → Eventually (step h) post (mkState s' (addrOf h (k + (mov rd rs).length)))) →
    Eventually (step h) post (mkState s (addrOf h k))
  movi_spec : ∀ {h : Host} {k : Nat} {rd : Reg} {c : Val} {s : MData} {post : State → Prop},
    (movi rd c).IsInfixAt (prog h) k →
    (∀ s', get s' rd = c → (∀ r, r ∉ rd :: scratch → get s' r = get s r) →
      mem s' = mem s → Eventually (step h) post (mkState s' (addrOf h (k + (movi rd c).length)))) →
    Eventually (step h) post (mkState s (addrOf h k))
  op_spec : ∀ {h : Host} {k : Nat} {o : Op Reg} {rd : Reg} {c : List Directive} {v : Val}
      {s : MData} {post : State → Prop},
    op o rd = some c → c.IsInfixAt (prog h) k → (∀ r, r ∈ o.vars → r ∉ scratch) →
    (o.map (get s)).eval = some v →
    (∀ s', get s' rd = v → (∀ r, r ∉ rd :: scratch → get s' r = get s r) →
      mem s' = mem s → Eventually (step h) post (mkState s' (addrOf h (k + c.length)))) →
    Eventually (step h) post (mkState s (addrOf h k))
  load_spec : ∀ {h : Host} {k : Nat} {cl : Cls} {sz : Sz} {sg : Bool} {rd : Reg} {a : Arg Reg}
      {c : List Directive} {v : Val} {s : MData} {post : State → Prop},
    load cl sz sg rd a = some c → c.IsInfixAt (prog h) k → (∀ r, r ∈ a.vars → r ∉ scratch) →
    loadVal (mem s) cl sz sg (a.map (get s)).val = some v →
    (∀ s', get s' rd = v → (∀ r, r ∉ rd :: scratch → get s' r = get s r) →
      mem s' = mem s → Eventually (step h) post (mkState s' (addrOf h (k + c.length)))) →
    Eventually (step h) post (mkState s (addrOf h k))
  store_spec : ∀ {h : Host} {k : Nat} {sz : Sz} {x a : Arg Reg} {c : List Directive}
      {s : MData} {post : State → Prop},
    store sz x a = some c → c.IsInfixAt (prog h) k → (∀ r, r ∈ x.vars ++ a.vars → r ∉ scratch) →
    storeOk (mem s) sz (a.map (get s)).val →
    (∀ s', (∀ r, r ∉ scratch → get s' r = get s r) →
      mem s' = storeMem (mem s) sz (a.map (get s)).val (x.map (get s)).val →
      Eventually (step h) post (mkState s' (addrOf h (k + c.length)))) →
    Eventually (step h) post (mkState s (addrOf h k))
  jmp_spec : ∀ {h : Host} {k j : Nat} {l : String} {s : MData} {post : State → Prop},
    (jmp l).IsInfixAt (prog h) k → labelAddr h l = addrOf h j →
    (∀ s', (∀ r, r ∉ scratch → get s' r = get s r) → mem s' = mem s →
      Eventually (step h) post (mkState s' (addrOf h j))) →
    Eventually (step h) post (mkState s (addrOf h k))
  jnz_spec : ∀ {h : Host} {k j : Nat} {r : Reg} {l : String} {s : MData} {post : State → Prop},
    (jnz r l).IsInfixAt (prog h) k → labelAddr h l = addrOf h j → r ∉ scratch →
    (∀ s', (∀ r, r ∉ scratch → get s' r = get s r) → mem s' = mem s →
      (Truthy (get s r) → Eventually (step h) post (mkState s' (addrOf h j))) ∧
      (¬ Truthy (get s r) →
        Eventually (step h) post (mkState s' (addrOf h (k + (jnz r l).length))))) →
    Eventually (step h) post (mkState s (addrOf h k))
  /-- `ret` with the return address `ra` where the convention keeps it (`RetAddr`, `raReg`). -/
  ret_spec : ∀ {h : Host} {k : Nat} {s : MData} {ra : Addr} {R : Mem 64 → Prop}
      {post : State → Prop},
    ret.IsInfixAt (prog h) k → raReg s ra → (mem s =⋆ RetAddr (get s sp) ra ⋆ R) →
    (∀ s', (∀ r, r ∉ sp :: scratch → get s' r = get s r) →
      get s' sp = get s sp + BitVec.ofNat 64 raBytes → mem s' = mem s →
      Eventually (step h) post (mkState s' ra)) →
    Eventually (step h) post (mkState s (addrOf h k))

namespace Target

variable (T : Target)

/-- From index `k` of the host program with machine data `s`, eventually `post`. -/
def Run (h : T.Host) (k : Nat) (s : T.MData) (post : T.State → Prop) : Prop :=
  Eventually (T.step h) post (T.mkState s (T.addrOf h k))

/-- `s'` agrees with `s` on every register outside `clob`. -/
def Keeps (s s' : T.MData) (clob : List T.Reg) : Prop :=
  ∀ r, r ∉ clob → T.get s' r = T.get s r

/-- No label is defined twice in the host program (Spike K: required for jumps to be correct). -/
def LabelsUnique (h : T.Host) : Prop :=
  ∀ (i j : Nat) (l : String),
    (T.prog h)[i]? = some (T.label l) → (T.prog h)[j]? = some (T.label l) → i = j

/-- Label `l` is defined in the host program. (Kraken resolves undefined labels to `-1`.) -/
def Defined (h : T.Host) (l : String) : Prop :=
  ∃ k : Nat, (T.prog h)[k]? = some (T.label l)

/-- The values `vs` are in the first `vs.length` registers of `regs`
(so there are at least that many). -/
def ValsIn (regs : List T.Reg) (vs : List Val) (s : T.MData) : Prop :=
  (regs.take vs.length).map (T.get s) = vs

/-- Arguments in the argument registers. -/
def ArgsIn (args : List Val) (s : T.MData) : Prop := T.ValsIn T.argRegs args s

/-- Results in the result registers. -/
def RetsIn (rets : List Val) (s : T.MData) : Prop := T.ValsIn T.retRegs rets s

/-- The memory a caller hands to a callee on entry, for stack pointer `sp`, return address `ra`
and stack bound `n`: `n` free bytes below `sp`, and the return address. -/
def Entry (sp : Val) (ra : T.Addr) (n : Nat) : Mem 64 → Prop :=
  region (sp - BitVec.ofNat 64 n) n ⋆ T.RetAddr sp ra

/-- The same footprint as `Entry sp ra n`, with arbitrary contents: what the caller gets back. -/
def Exit (sp : Val) (n : Nat) : Mem 64 → Prop :=
  region (sp - BitVec.ofNat 64 n) (n + T.raBytes)

/-- What a function guarantees about registers on return, relative to its entry data `s`. -/
def Restored (s s' : T.MData) : Prop :=
  (∀ r, r ∈ T.calleeSaved → T.get s' r = T.get s r) ∧
  T.get s' T.sp = T.get s T.sp + BitVec.ofNat 64 T.raBytes

end Target

namespace Target

variable (T : Target)

/--
Function contract, version 0 (plan section 2.4).

In host `h`, the code at label `sym` implements `spec` using at most `n` bytes of stack below the
entry stack pointer: for every call satisfying `spec`, from any machine data `s` with

* the arguments in the argument registers,
* the return address `ra` where the convention keeps it,
* an entry stack pointer satisfying the ABI's condition,
* memory split into the source memory `m`, the callee's stack region `Entry`, and a frame `R`,

execution starting at `sym` eventually either

* reaches `ra` with results in the result registers, callee-saved registers and the stack pointer
  restored, and memory split into the new source memory `m'`, the same stack footprint (contents
  arbitrary), and the untouched frame `R`; or
* reaches the label of an exit symbol `sym'` with its arguments in the argument registers, the
  same memory split.

Open in version 0 (settled in step 2b): the stack pointer and alignment at an exit, more results
than result registers, and how stack bounds of callees add up (`FnSpec` of a non-leaf function).
-/
def FnSpec (h : T.Host) (sym : String) (spec : Spec) (n : Nat) : Prop :=
  ∀ args m Q X, spec args m Q X →
  ∀ (s : T.MData) (ra : T.Addr) (R : Mem 64 → Prop),
    T.ArgsIn args s → T.raReg s ra → T.spEntry (T.get s T.sp) →
    (T.mem s =⋆ Eq m ⋆ T.Entry (T.get s T.sp) ra n ⋆ R) →
    Eventually (T.step h)
      (fun st =>
        (T.pc st = ra ∧ ∃ rets m', Q rets m' ∧ T.RetsIn rets (T.data st) ∧
          T.Restored s (T.data st) ∧
          (T.mem (T.data st) =⋆ Eq m' ⋆ T.Exit (T.get s T.sp) n ⋆ R)) ∨
        (∃ sym' as m', X sym' as m' ∧ T.Defined h sym' ∧ T.pc st = T.labelAddr h sym' ∧
          T.ArgsIn as (T.data st) ∧
          (T.mem (T.data st) =⋆ Eq m' ⋆ T.Exit (T.get s T.sp) n ⋆ R)))
      (T.mkState s (T.labelAddr h sym))

end Target

end LeanQbe
