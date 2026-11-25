module

public import LeanQbe.T.IL
public import LeanQbe.T.WP
public import LeanQbe.T.Wf
public import LeanQbe.T.Flat

/-!
# Unityped-Word Bedrock L0 Core (`BedrockWord.Core`)

Target-neutral L0 IR where code pointers are plain 64-bit machine words (`i64` / `BitVec 64`):

* Machine state: 6 uniform 64-bit registers `Regs := {sp, rp, rv, r1, r2, r3}` + `Mem 64`.
* Dual PHOAS + de Bruijn `BlockFlat` IR (`let_`, `load`, `store`, `codeAddr`, `jnz`, `ijmp`,
  `halt`, `hlt`), `BlockFlat.wfCheck`, `BlockFlat.wp`, `BlockB.wp`, `BlockB.Wf`.
* Concrete 8-byte-aligned `CodeMap`, computable `evalOpCode` and `BlockFlat.exec`, `runFuel`,
  `runCode`, `TraceEv`, `runTrace`, and ICFP'13 structured macros (`atomicM`, `seqM`, `ifM`,
  `whileM`, `callM`, `retM`, `tailCallM`, `haltM`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.BedrockWord

open LeanQbe.T

/-! ## §1. Machine State, Registers, and Alignment -/

/-- Six uniform 64-bit word registers at basic-block boundaries. -/
structure Regs : Type where
  sp : BitVec 64 := 0#64
  rp : BitVec 64 := 0#64
  rv : BitVec 64 := 0#64
  r1 : BitVec 64 := 0#64
  r2 : BitVec 64 := 0#64
  r3 : BitVec 64 := 0#64
  deriving DecidableEq, Repr, Inhabited

/-- Machine state at a basic-block boundary: uniform 64-bit registers + `Mem 64`. -/
structure State : Type where
  regs : Regs
  mem  : Mem 64

/-- The uniform register boundary signature (six `i64` words). -/
abbrev regSig : List Ty := [i64, i64, i64, i64, i64, i64]

/-- PHOAS register binders at the entry of a basic block. -/
structure RegsV (V : Ty → Type) : Type where
  sp : V i64
  rp : V i64
  rv : V i64
  r1 : V i64
  r2 : V i64
  r3 : V i64

/-- PHOAS register operand expressions transferred at an `ijmp` boundary. -/
structure RegsExpr (V : Ty → Type) : Type where
  sp : Arg V i64
  rp : Arg V i64
  rv : Arg V i64
  r1 : Arg V i64
  r2 : Arg V i64
  r3 : Arg V i64

/-- Preserve all six registers unchanged across an `ijmp`. -/
@[expose] def RegsV.keep {V : Ty → Type} (r : RegsV V) : RegsExpr V :=
  ⟨.var r.sp, .var r.rp, .var r.rv, .var r.r1, .var r.r2, .var r.r3⟩

@[expose] def Regs.toRegsV (r : Regs) : RegsV Val :=
  ⟨r.sp, r.rp, r.rv, r.r1, r.r2, r.r3⟩

@[expose] def RegsExpr.eval (e : RegsExpr Val) : Regs :=
  ⟨e.sp.val, e.rp.val, e.rv.val, e.r1.val, e.r2.val, e.r3.val⟩

@[expose] def RegsV.toTup {V : Ty → Type} (r : RegsV V) : Tup V regSig :=
  (r.sp, r.rp, r.rv, r.r1, r.r2, r.r3, ())

@[expose] def RegsExpr.toTup {V : Ty → Type} (e : RegsExpr V) : Tup (Arg V) regSig :=
  (e.sp, e.rp, e.rv, e.r1, e.r2, e.r3, ())

@[expose] def RegsV.levels0 : RegsV K := ⟨0, 1, 2, 3, 4, 5⟩

@[expose] def RegsV.units : RegsV (fun _ => Unit) := ⟨(), (), (), (), (), ()⟩

/-- Push the six boundary registers onto an empty de Bruijn context (`r3` at index `0`,
`sp` at index `5`). -/
@[expose] def pushRegsV {V : Ty → Type} (r : RegsV V) : List ((t : Ty) × V t) :=
  pushTup r.toTup []

/-- Type context corresponding to `pushRegsV`. -/
abbrev regCtx : List Ty := pushTypes regSig []

@[expose] def RegsExpr.idxArgs (nv : Nat) (e : RegsExpr K) : RegsExpr K :=
  ⟨idxArg nv e.sp, idxArg nv e.rp, idxArg nv e.rv,
   idxArg nv e.r1, idxArg nv e.r2, idxArg nv e.r3⟩

@[expose] def denoteRegsExpr {V : Ty → Type} (vs : List ((t : Ty) × V t)) (e : RegsExpr K) :
    Option (RegsExpr V) :=
  match denoteArg vs e.sp, denoteArg vs e.rp, denoteArg vs e.rv,
        denoteArg vs e.r1, denoteArg vs e.r2, denoteArg vs e.r3 with
  | some sp', some rp', some rv', some r1', some r2', some r3' =>
      some ⟨sp', rp', rv', r1', r2', r3'⟩
  | _, _, _, _, _, _ => none

@[expose] def checkRegsExpr (Γ : List Ty) (e : RegsExpr K) : Bool :=
  checkArg Γ i64 e.sp && checkArg Γ i64 e.rp && checkArg Γ i64 e.rv &&
  checkArg Γ i64 e.r1 && checkArg Γ i64 e.r2 && checkArg Γ i64 e.r3

/-- Relational equivalence on `RegsExpr` reusing `LeanQbe.T.ArgRel`. -/
structure RegsExprRel {V₁ V₂ : Ty → Type} (G : Ctx V₁ V₂)
    (e₁ : RegsExpr V₁) (e₂ : RegsExpr V₂) : Prop where
  sp : ArgRel G i64 e₁.sp e₂.sp
  rp : ArgRel G i64 e₁.rp e₂.rp
  rv : ArgRel G i64 e₁.rv e₂.rv
  r1 : ArgRel G i64 e₁.r1 e₂.r1
  r2 : ArgRel G i64 e₁.r2 e₂.r2
  r3 : ArgRel G i64 e₁.r3 e₂.r3

/-- Pure proposition lifted into `Mem 64` separation logic (`[φ]`). -/
@[expose] def pure (φ : Prop) : Mem 64 → Prop := fun m => φ ∧ m = ∅

/-- 8-byte alignment predicate on 64-bit code addresses. -/
abbrev AlignedAddr (a : BitVec 64) : Prop := a &&& 7#64 = 0#64

/-! ## §2. Unityped-Word PHOAS & First-Order `BlockFlat` IR -/

/-- Unityped-word Bedrock basic block in `LeanQbe.T` PHOAS style. -/
inductive BlockB (V : Ty → Type) : Type
  | let_ {ts : List Ty} (op : Op V ts) (k : Tup V ts → BlockB V) : BlockB V
  | load (t : Ty) (a : Arg V i64) (k : V t → BlockB V) : BlockB V
  | store {t : Ty} (v : Arg V t) (a : Arg V i64) (k : BlockB V) : BlockB V
  | codeAddr (sym : Sym) (k : V i64 → BlockB V) : BlockB V
  | jnz (c : Arg V .bool) (t e : BlockB V) : BlockB V
  | ijmp (target : Arg V i64) (nextRegs : RegsExpr V) : BlockB V
  | halt (code : Arg V i64) : BlockB V
  | hlt : BlockB V

/-- A closed PHOAS basic block parameterized over `V` and the six boundary registers. -/
abbrev BlockP : Type 1 := ∀ (V : Ty → Type), RegsV V → BlockB V

/-- A named, explicitly 8-byte-aligned PHOAS basic block entry. -/
structure CodeEntryP : Type 1 where
  name : Sym
  addr : BitVec 64
  body : BlockP

/-- A PHOAS unityped-word Bedrock module with explicit block layout. -/
structure ModuleP : Type 1 where
  entries : List CodeEntryP

abbrev BlockB.let1 {V : Ty → Type} {t : Ty} (op : Op V [t]) (k : V t → BlockB V) : BlockB V :=
  .let_ op fun (x, ()) => k x

abbrev BlockB.letOp1 {V : Ty → Type} {a t : Ty} (c : OpCode [a] [t])
    (x : Arg V a) (k : V t → BlockB V) : BlockB V :=
  .let1 (op1 c x) k

abbrev BlockB.letOp2 {V : Ty → Type} {a b t : Ty} (c : OpCode [a, b] [t])
    (x : Arg V a) (y : Arg V b) (k : V t → BlockB V) : BlockB V :=
  .let1 (op2 c x y) k

abbrev BlockB.letOp3 {V : Ty → Type} {a b d t : Ty} (c : OpCode [a, b, d] [t])
    (x : Arg V a) (y : Arg V b) (z : Arg V d) (k : V t → BlockB V) : BlockB V :=
  .let1 (op3 c x y z) k

abbrev BlockB.load64 {V : Ty → Type} (a : Arg V i64) (k : V i64 → BlockB V) : BlockB V :=
  .load i64 a k

abbrev BlockB.store64 {V : Ty → Type} (v a : Arg V i64) (k : BlockB V) : BlockB V :=
  .store (t := i64) v a k

abbrev BlockB.jmpSym {V : Ty → Type} (sym : Sym) (nextRegs : RegsExpr V) : BlockB V :=
  .codeAddr sym fun p => .ijmp (.var p) nextRegs

/-- Symbol-to-address environment mapping block names to 64-bit code addresses. -/
abbrev SymEnv : Type := Sym → Option (BitVec 64)

/-- Code specification environment. -/
abbrev CodeSpec : Type := BitVec 64 → State → Prop

/-- Whole-program halt postcondition over exit code and final `Mem 64`. -/
abbrev HaltPost : Type := BitVec 64 → Mem 64 → Prop

/-- Extension ordering on symbol environments. -/
@[expose] def SymEnv.Ext (ρ₁ ρ₂ : SymEnv) : Prop :=
  ∀ s a, ρ₁ s = some a → ρ₂ s = some a

/-- Weakest precondition of a single basic block `b : BlockB Val`. -/
@[expose] def BlockB.wp (ρ : SymEnv) (Ψ : CodeSpec) (H : HaltPost) :
    BlockB Val → Mem 64 → Prop
  | .let_ op k, m => op.wp (fun r => BlockB.wp ρ Ψ H (k r) m)
  | .load t a k, m => ∃ v, loadVal m t a.val = some v ∧ BlockB.wp ρ Ψ H (k v) m
  | .store (t := t) v a k, m =>
      storeOk m t a.val ∧ BlockB.wp ρ Ψ H k (storeMem m t a.val v.val)
  | .codeAddr sym k, m => ∃ a, ρ sym = some a ∧ BlockB.wp ρ Ψ H (k a) m
  | .jnz c t e, m =>
      (c.val = true → BlockB.wp ρ Ψ H t m) ∧ (c.val = false → BlockB.wp ρ Ψ H e m)
  | .ijmp target nextRegs, m => Ψ target.val ⟨nextRegs.eval, m⟩
  | .halt code, m => H code.val m
  | .hlt, _ => False

/-- Weakest precondition of a closed PHOAS block `b : BlockP` at machine state `st`. -/
@[expose] def BlockP.wp (ρ : SymEnv) (Ψ : CodeSpec) (H : HaltPost)
    (b : BlockP) (st : State) : Prop :=
  BlockB.wp ρ Ψ H (b Val st.regs.toRegsV) st.mem

/-- Relational parametricity between two instantiations of a PHOAS `BlockB`. -/
inductive BlockB.Wf {V₁ V₂ : Ty → Type} : Ctx V₁ V₂ → BlockB V₁ → BlockB V₂ → Prop
  | let_ {G ts op₁ op₂ k₁ k₂} :
      OpRel G op₁ op₂ →
      (∀ (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts),
        BlockB.Wf (Tup.zip xs₁ xs₂ ++ G) (k₁ xs₁) (k₂ xs₂)) →
      BlockB.Wf G (.let_ (ts := ts) op₁ k₁) (.let_ op₂ k₂)
  | load {G} (t : Ty) {a₁ a₂ k₁ k₂} :
      ArgRel G i64 a₁ a₂ →
      (∀ (v₁ : V₁ t) (v₂ : V₂ t), BlockB.Wf (⟨t, v₁, v₂⟩ :: G) (k₁ v₁) (k₂ v₂)) →
      BlockB.Wf G (.load t a₁ k₁) (.load t a₂ k₂)
  | store {G t v₁ v₂ a₁ a₂ k₁ k₂} :
      ArgRel G t v₁ v₂ → ArgRel G i64 a₁ a₂ → BlockB.Wf G k₁ k₂ →
      BlockB.Wf G (.store (t := t) v₁ a₁ k₁) (.store v₂ a₂ k₂)
  | codeAddr {G} (sym : Sym) {k₁ k₂} :
      (∀ (a₁ : V₁ i64) (a₂ : V₂ i64), BlockB.Wf (⟨i64, a₁, a₂⟩ :: G) (k₁ a₁) (k₂ a₂)) →
      BlockB.Wf G (.codeAddr sym k₁) (.codeAddr sym k₂)
  | jnz {G c₁ c₂ t₁ t₂ e₁ e₂} :
      ArgRel G .bool c₁ c₂ → BlockB.Wf G t₁ t₂ → BlockB.Wf G e₁ e₂ →
      BlockB.Wf G (.jnz c₁ t₁ e₁) (.jnz c₂ t₂ e₂)
  | ijmp {G t₁ t₂ n₁ n₂} :
      ArgRel G i64 t₁ t₂ → RegsExprRel G n₁ n₂ →
      BlockB.Wf G (.ijmp t₁ n₁) (.ijmp t₂ n₂)
  | halt {G c₁ c₂} :
      ArgRel G i64 c₁ c₂ → BlockB.Wf G (.halt c₁) (.halt c₂)
  | hlt {G} : BlockB.Wf G .hlt .hlt

/-- Every two instantiations of a closed PHOAS block at related registers are `BlockB.Wf`. -/
@[expose] def BlockP.Wf (b : BlockP) : Prop :=
  ∀ (V₁ V₂ : Ty → Type) (r₁ : RegsV V₁) (r₂ : RegsV V₂),
    BlockB.Wf (Tup.zip r₁.toTup r₂.toTup) (b V₁ r₁) (b V₂ r₂)

/-- First-order de Bruijn mirror of `BlockB` over `LeanQbe.T.K` (`0` = newest binder). -/
inductive BlockFlat : Type
  | let_ {ts : List Ty} (op : Op K ts) (k : BlockFlat) : BlockFlat
  | load (t : Ty) (a : Arg K i64) (k : BlockFlat) : BlockFlat
  | store {t : Ty} (v : Arg K t) (a : Arg K i64) (k : BlockFlat) : BlockFlat
  | codeAddr (sym : Sym) (k : BlockFlat) : BlockFlat
  | jnz (c : Arg K .bool) (t e : BlockFlat) : BlockFlat
  | ijmp (target : Arg K i64) (nextRegs : RegsExpr K) : BlockFlat
  | halt (code : Arg K i64) : BlockFlat
  | hlt : BlockFlat

/-- Total reification of `BlockB K` into first-order de Bruijn `BlockFlat` at depth `nv`. -/
@[expose] def toFlat : BlockB K → Nat → BlockFlat
  | .let_ (ts := ts) op k, nv =>
      .let_ ⟨op.code, idxArgs nv op.args⟩ (toFlat (k (Tup.levels ts nv)) (nv + ts.length))
  | .load t a k, nv => .load t (idxArg nv a) (toFlat (k nv) (nv + 1))
  | .store v a k, nv => .store (idxArg nv v) (idxArg nv a) (toFlat k nv)
  | .codeAddr sym k, nv => .codeAddr sym (toFlat (k nv) (nv + 1))
  | .jnz c t e, nv => .jnz (idxArg nv c) (toFlat t nv) (toFlat e nv)
  | .ijmp tgt nxt, nv => .ijmp (idxArg nv tgt) (nxt.idxArgs nv)
  | .halt c, nv => .halt (idxArg nv c)
  | .hlt, _ => .hlt

/-- Reify a closed PHOAS `BlockP` into its first-order `BlockFlat` representation. -/
@[expose] def reifyBlock (b : BlockP) : BlockFlat :=
  toFlat (b K RegsV.levels0) 6

/-- Denote a first-order `BlockFlat` back into PHOAS `BlockB V`. -/
@[expose] def BlockFlat.denote (V : Ty → Type) :
    BlockFlat → List ((t : Ty) × V t) → BlockB V
  | .let_ op k, vs =>
      match denoteArgs vs op.args with
      | some args' => .let_ ⟨op.code, args'⟩ fun xs => k.denote V (pushTup xs vs)
      | none => .hlt
  | .load t a k, vs =>
      match denoteArg vs a with
      | some a' => .load t a' fun v => k.denote V (⟨t, v⟩ :: vs)
      | none => .hlt
  | .store v a k, vs =>
      match denoteArg vs v, denoteArg vs a with
      | some v', some a' => .store v' a' (k.denote V vs)
      | _, _ => .hlt
  | .codeAddr sym k, vs =>
      .codeAddr sym fun a => k.denote V (⟨i64, a⟩ :: vs)
  | .jnz c t e, vs =>
      match denoteArg vs c with
      | some c' => .jnz c' (t.denote V vs) (e.denote V vs)
      | none => .hlt
  | .ijmp tgt nxt, vs =>
      match denoteArg vs tgt, denoteRegsExpr vs nxt with
      | some tgt', some nxt' => .ijmp tgt' nxt'
      | _, _ => .hlt
  | .halt c, vs =>
      match denoteArg vs c with
      | some c' => .halt c'
      | none => .hlt
  | .hlt, _ => .hlt

/-- Denote a `BlockFlat` back into a closed PHOAS `BlockP`. -/
@[expose] def denoteBlock (bf : BlockFlat) : BlockP :=
  fun V r => bf.denote V (pushRegsV r)

/-- Total computable scope/type checker for `BlockFlat` under value type context `Γ`. -/
@[expose] def BlockFlat.wfCheck : BlockFlat → List Ty → Bool
  | .let_ (ts := ts) op k, Γ => checkArgs Γ op.args && k.wfCheck (pushTypes ts Γ)
  | .load t a k, Γ => checkArg Γ i64 a && k.wfCheck (t :: Γ)
  | .store (t := t) v a k, Γ => checkArg Γ t v && checkArg Γ i64 a && k.wfCheck Γ
  | .codeAddr _ k, Γ => k.wfCheck (i64 :: Γ)
  | .jnz c t e, Γ => checkArg Γ .bool c && t.wfCheck Γ && e.wfCheck Γ
  | .ijmp tgt nxt, Γ => checkArg Γ i64 tgt && checkRegsExpr Γ nxt
  | .halt c, Γ => checkArg Γ i64 c
  | .hlt, _ => true

/-- A closed `BlockFlat` is well-formed iff it passes `wfCheck` under `regCtx`. -/
@[expose] def BlockFlat.Wf (bf : BlockFlat) : Prop :=
  bf.wfCheck regCtx = true

/-- True iff `BlockFlat` contains no explicit `.hlt` node. -/
@[expose] def BlockFlat.noHlt : BlockFlat → Bool
  | .let_ _ k => k.noHlt
  | .load _ _ k => k.noHlt
  | .store _ _ k => k.noHlt
  | .codeAddr _ k => k.noHlt
  | .jnz _ t e => t.noHlt && e.noHlt
  | .ijmp _ _ => true
  | .halt _ => true
  | .hlt => false

/-- Direct first-order weakest precondition on `BlockFlat` over de Bruijn environment `vs`. -/
@[expose] def BlockFlat.wp (ρ : SymEnv) (Ψ : CodeSpec) (H : HaltPost) :
    BlockFlat → List ((t : Ty) × Val t) → Mem 64 → Prop
  | .let_ op k, vs, m =>
      match denoteArgs vs op.args with
      | some args' => (⟨op.code, args'⟩ : Op Val _).wp (fun r => k.wp ρ Ψ H (pushTup r vs) m)
      | none => False
  | .load ty a k, vs, m =>
      match denoteArg vs a with
      | some a' => ∃ v, loadVal m ty a'.val = some v ∧ k.wp ρ Ψ H (⟨ty, v⟩ :: vs) m
      | none => False
  | .store (t := ty) v a k, vs, m =>
      match denoteArg vs v, denoteArg vs a with
      | some v', some a' =>
          storeOk m ty a'.val ∧ k.wp ρ Ψ H vs (storeMem m ty a'.val v'.val)
      | _, _ => False
  | .codeAddr sym k, vs, m =>
      ∃ a, ρ sym = some a ∧ k.wp ρ Ψ H (⟨i64, a⟩ :: vs) m
  | .jnz c t e, vs, m =>
      match denoteArg vs c with
      | some c' => (c'.val = true → t.wp ρ Ψ H vs m) ∧ (c'.val = false → e.wp ρ Ψ H vs m)
      | none => False
  | .ijmp tgt nxt, vs, m =>
      match denoteArg vs tgt, denoteRegsExpr vs nxt with
      | some tgt', some nxt' => Ψ tgt'.val ⟨nxt'.eval, m⟩
      | _, _ => False
  | .halt c, vs, m =>
      match denoteArg vs c with
      | some c' => H c'.val m
      | none => False
  | .hlt, _, _ => False

/-! ## §3. Concrete `CodeMap`, Evaluators, and Operational Execution -/

/-- A concrete first-order code-map entry pairing symbol name, aligned address, and block. -/
structure CodeEntry : Type where
  name  : Sym
  addr  : BitVec 64
  block : BlockFlat

/-- A concrete layout mapping 8-byte-aligned 64-bit addresses and symbol names to blocks. -/
abbrev CodeMap : Type := List CodeEntry

/-- Compile a list of PHOAS `CodeEntryP`s into a concrete `CodeMap`. -/
@[expose] def compileEntries (es : List CodeEntryP) : CodeMap :=
  es.map fun e => ⟨e.name, e.addr, reifyBlock e.body⟩

/-- Compile a PHOAS `ModuleP` into a concrete `CodeMap`. -/
@[expose] def ModuleP.toCodeMap (M : ModuleP) : CodeMap :=
  compileEntries M.entries

/-- Address lookup in `CodeMap` (first matching entry). -/
@[expose] def CodeMap.lookupAddr : CodeMap → BitVec 64 → Option BlockFlat
  | [], _ => none
  | e :: es, pc => if e.addr == pc then some e.block else CodeMap.lookupAddr es pc

/-- Symbol-name-to-address resolution in `CodeMap`. -/
@[expose] def CodeMap.addrOf? : CodeMap → Sym → Option (BitVec 64)
  | [], _ => none
  | e :: es, s => if e.name == s then some e.addr else CodeMap.addrOf? es s

/-- The symbol environment defined by `cm`. -/
@[expose] def CodeMap.symEnv (cm : CodeMap) : SymEnv :=
  fun s => cm.addrOf? s

/-- All addresses in `cm` are 8-byte aligned (`addr &&& 7 = 0`). -/
@[expose] def CodeMap.Aligned (cm : CodeMap) : Prop :=
  ∀ e ∈ cm, AlignedAddr e.addr

/-- All block addresses in `cm` are distinct. -/
@[expose] def CodeMap.AddrsNodup (cm : CodeMap) : Prop :=
  (cm.map (·.addr)).Nodup

/-- All block symbol names in `cm` are distinct. -/
@[expose] def CodeMap.NamesNodup (cm : CodeMap) : Prop :=
  (cm.map (·.name)).Nodup

/-- Full well-formedness of a concrete `CodeMap`. -/
structure CodeMap.Wf (cm : CodeMap) : Prop where
  aligned : cm.Aligned
  addrsNodup : cm.AddrsNodup
  namesNodup : cm.NamesNodup
  blocksWf : ∀ e ∈ cm, e.block.Wf

/-- Computable boolean checker for `CodeMap.Wf`, kernel-reducible via `rfl`. -/
@[expose] def CodeMap.checkWf (cm : CodeMap) : Bool :=
  cm.all (fun e => (e.addr &&& 7#64) == 0#64) &&
  listNodup (cm.map (·.addr)) &&
  listNodup (cm.map (·.name)) &&
  cm.all (fun e => e.block.wfCheck regCtx)

/-- Address-disjointness of two `CodeMap`s. -/
@[expose] def CodeMap.AddrDisjoint (cm₁ cm₂ : CodeMap) : Prop :=
  ∀ e₁ ∈ cm₁, ∀ e₂ ∈ cm₂, e₁.addr ≠ e₂.addr

/-- Symbol-name disjointness of two `CodeMap`s. -/
@[expose] def CodeMap.NameDisjoint (cm₁ cm₂ : CodeMap) : Prop :=
  ∀ e₁ ∈ cm₁, ∀ e₂ ∈ cm₂, e₁.name ≠ e₂.name

/-- Full disjointness of two `CodeMap`s for horizontal linking (`cm₁ ++ cm₂`). -/
structure CodeMap.Disjoint (cm₁ cm₂ : CodeMap) : Prop where
  addrDisj : cm₁.AddrDisjoint cm₂
  nameDisj : cm₁.NameDisjoint cm₂

/-- Computable boolean disjointness checker for concrete `CodeMap` linking. -/
@[expose] def CodeMap.checkDisjoint (cm₁ cm₂ : CodeMap) : Bool :=
  cm₁.all (fun e₁ => cm₂.all (fun e₂ => (e₁.addr != e₂.addr) && (e₁.name != e₂.name)))

/-- Sub-code-map relation: every mapped address in `cm₁` maps identically in `cm₂`. -/
@[expose] def CodeMap.Sub (cm₁ cm₂ : CodeMap) : Prop :=
  ∀ pc b, cm₁.lookupAddr pc = some b → cm₂.lookupAddr pc = some b

/-- Canonical packed NaN bit-pattern for IEEE format `f`. -/
@[expose] def packedNaNBv (f : Fmt) : BitVec f.width :=
  (Float.Model.UnpackedFloat.packedNaN f.format).cast (Fmt.format_numBits f)

@[expose] def evalFloatResult (f : Fmt) (res : Float.Model.UnpackedFloat) : BitVec f.width :=
  if res.isNaN then packedNaNBv f else packFloat f res

@[expose] def evalFloat1
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    (t : Ty) → Val t → Option (Val t)
  | .float f, a => some (evalFloatResult f (op f.format (unpackFloat f a)))
  | .pair s u, a => do
      let r1 ← evalFloat1 op s a.1
      let r2 ← evalFloat1 op u a.2
      some (r1, r2)
  | _, _ => none

@[expose] def evalFloat2
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    (t : Ty) → Val t → Val t → Option (Val t)
  | .float f, a, b => some (evalFloatResult f (op f.format (unpackFloat f a) (unpackFloat f b)))
  | .pair s u, a, b => do
      let r1 ← evalFloat2 op s a.1 b.1
      let r2 ← evalFloat2 op u a.2 b.2
      some (r1, r2)
  | _, _, _ => none

@[expose] def evalFloat3
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    (t : Ty) → Val t → Val t → Val t → Option (Val t)
  | .float f, a, b, c =>
      some (evalFloatResult f (op f.format (unpackFloat f a) (unpackFloat f b) (unpackFloat f c)))
  | .pair s u, a, b, c => do
      let r1 ← evalFloat3 op s a.1 b.1 c.1
      let r2 ← evalFloat3 op u a.2 b.2 c.2
      some (r1, r2)
  | _, _, _, _ => none

@[expose] def evalConvertFloat (src dst : Fmt) (b : BitVec src.width) : BitVec dst.width :=
  match unpackFloat src b with
  | .notANumber => packedNaNBv dst
  | .finite s m e _ => packFloat dst (Float.Model.UnpackedFloat.round dst.format s m e)
  | u => packFloat dst u

/-- Deterministic computable evaluator for every `LeanQbe.T.OpCode`. -/
@[expose] def evalOpCode : {as rs : List Ty} → OpCode as rs → Tup Val as → Option (Tup Val rs)
  | _, _, .copy _, (a, ()) => some (a, ())
  | _, _, .add t, (a, b, ()) =>
      if t.hasFloat then none else some (lift2 (· + ·) (· ^^ ·) t a b, ())
  | _, _, .sub t, (a, b, ()) =>
      if t.hasFloat then none else some (lift2 (· - ·) (· ^^ ·) t a b, ())
  | _, _, .mul t, (a, b, ()) =>
      if t.hasFloat then none else some (lift2 (· * ·) (· && ·) t a b, ())
  | _, _, .neg t, (a, ()) =>
      if t.hasFloat then none else some (lift1 (- ·) id t a, ())
  | _, _, .and t, (a, b, ()) => some (lift2 (· &&& ·) (· && ·) t a b, ())
  | _, _, .or t, (a, b, ()) => some (lift2 (· ||| ·) (· || ·) t a b, ())
  | _, _, .xor t, (a, b, ()) => some (lift2 (· ^^^ ·) (· ^^ ·) t a b, ())
  | _, _, .not t, (a, ()) => some (lift1 (~~~ ·) (! ·) t a, ())
  | _, _, .ternlog t imm, (a, b, c, ()) =>
      some (lift3 (fun x y z => ternaryLogic x y z imm)
        (fun x y z => ternaryLogicBool x y z imm) t a b c, ())
  | _, _, .shl t, (a, b, ()) =>
      if t.hasFloat then none
      else some (lift2 (fun {n} x y => x <<< (y.toNat % n)) (fun x _ => x) t a b, ())
  | _, _, .lshr t, (a, b, ()) =>
      if t.hasFloat then none
      else some (lift2 (fun {n} x y => x >>> (y.toNat % n)) (fun x _ => x) t a b, ())
  | _, _, .ashr t, (a, b, ()) =>
      if t.hasFloat then none
      else some (lift2 (fun {n} x y => x.sshiftRight (y.toNat % n)) (fun x _ => x) t a b, ())
  | _, _, .rotl t, (a, b, ()) =>
      if t.hasFloat then none
      else some (lift2 (fun {n} x y => x.rotateLeft (y.toNat % n)) (fun x _ => x) t a b, ())
  | _, _, .rotr t, (a, b, ()) =>
      if t.hasFloat then none
      else some (lift2 (fun {n} x y => x.rotateRight (y.toNat % n)) (fun x _ => x) t a b, ())
  | _, _, .fshl n, (a, b, c, ()) =>
      some ((((a ++ b) <<< (c.toNat % n)).extractLsb' n n), ())
  | _, _, .fshr n, (a, b, c, ()) =>
      some ((((a ++ b) >>> (c.toNat % n)).extractLsb' 0 n), ())
  | _, _, .bswap t, (a, ()) =>
      if !t.bswapOk then none else some (lift1 bswapBits id t a, ())
  | _, _, .clz _, (a, ()) => some (a.clz, ())
  | _, _, .cls n, (a, ()) => some ((if a.msb then (~~~a).clz else a.clz) - 1#n, ())
  | _, _, .rbit _, (a, ()) => some (a.reverse, ())
  | _, _, .ctz _, (a, ()) => some (a.reverse.clz, ())
  | _, _, .popcnt _, (a, ()) => some (a.cpop, ())
  | _, _, .cmp o t _ rfl, (a, b, ()) =>
      if t.hasFloat then none else some (liftCmp o.evalBits o.evalBool t a b, ())
  | _, _, .select _, (c, a, b, ()) => some (if c then a else b, ())
  | _, _, .blend t _ rfl, (c, a, b, ()) => some (blendV t c a b, ())
  | _, _, .zext m n, (a, ()) => if m ≤ n then some (a.setWidth n, ()) else none
  | _, _, .sext m n, (a, ()) => if m ≤ n then some (a.signExtend n, ()) else none
  | _, _, .trunc m n, (a, ()) => if n ≤ m then some (a.setWidth n, ()) else none
  | _, _, .ofBool n, (c, ()) => some (BitVec.ofNat n c.toNat, ())
  | _, _, .addc n, (a, b, c, ()) =>
      some (a + b + BitVec.ofNat n c.toNat, decide (2 ^ n ≤ a.toNat + b.toNat + c.toNat), ())
  | _, _, .subb n, (a, b, c, ()) =>
      some (a - b - BitVec.ofNat n c.toNat, decide (a.toNat < b.toNat + c.toNat), ())
  | _, _, .umulw n, (a, b, ()) =>
      some (a * b, BitVec.ofNat n (a.toNat * b.toNat / 2 ^ n), ())
  | _, _, .smulw n, (a, b, ()) =>
      some (a * b, (BitVec.ofInt (n + n) (a.toInt * b.toInt)).extractLsb' n n, ())
  | _, _, .udiv _, (a, b, ()) => if b ≠ 0 then some (a / b, ()) else none
  | _, _, .sdiv _, (a, b, ()) => if sdivDefined a b then some (a.sdiv b, ()) else none
  | _, _, .urem _, (a, b, ()) => if b ≠ 0 then some (a % b, ()) else none
  | _, _, .srem _, (a, b, ()) => if sdivDefined a b then some (a.srem b, ()) else none
  | _, _, .udiv0 _, (a, b, ()) => some (if b = 0 then 0 else a / b, ())
  | _, _, .sdiv0 _, (a, b, ()) => some (if b = 0 then 0 else a.sdiv b, ())
  | _, _, .mkpair _ _, (a, b, ()) => some ((a, b), ())
  | _, _, .unpair _ _, (p, ()) => some (p.1, p.2, ())
  | _, _, .bitcast t u h, (a, ()) => some (ofBits u ((toBits t a).cast h), ())
  | _, _, .shufd t imm, (a, ()) =>
      if t.size ≠ 0 ∧ t.size % 128 = 0 then
        some (ofBits t (shuffleDwords (toBits t a) imm), ())
      else none
  | _, _, .shufb t, (a, m, ()) =>
      if t.size ≠ 0 ∧ t.size % 128 = 0 then
        some (ofBits t (shuffleBytes (toBits t a) (toBits t m)), ())
      else none
  | _, _, .alignr t imm, (hi, lo, ()) =>
      if t.size ≠ 0 ∧ t.size % 128 = 0 then
        some (ofBits t (alignBytes (toBits t hi) (toBits t lo) imm), ())
      else none
  | _, _, .blendw t imm, (a, b, ()) =>
      if t.size ≠ 0 ∧ t.size % 128 = 0 then
        some (ofBits t (blendWords (toBits t a) (toBits t b) imm), ())
      else none
  | _, _, .sha256rnds2, (cdgh, abef, wk, ()) =>
      some (ofBits v4i32
        (Sha256.rounds2 (toBits v4i32 cdgh) (toBits v4i32 abef) (toBits v4i32 wk)), ())
  | _, _, .sha256msg1, (w0123, w4, ()) =>
      some (ofBits v4i32 (Sha256.msg1 (toBits v4i32 w0123) (toBits v4i32 w4)), ())
  | _, _, .sha256msg2, (sums, w, ()) =>
      some (ofBits v4i32 (Sha256.msg2 (toBits v4i32 sums) (toBits v4i32 w)), ())
  | _, _, .fadd t, (a, b, ()) =>
      if !t.isFloatTree then none
      else (evalFloat2 Float.Model.UnpackedFloat.add t a b).map (·, ())
  | _, _, .fsub t, (a, b, ()) =>
      if !t.isFloatTree then none
      else (evalFloat2 Float.Model.UnpackedFloat.sub t a b).map (·, ())
  | _, _, .fmul t, (a, b, ()) =>
      if !t.isFloatTree then none
      else (evalFloat2 Float.Model.UnpackedFloat.mul t a b).map (·, ())
  | _, _, .fdiv t, (a, b, ()) =>
      if !t.isFloatTree then none
      else (evalFloat2 Float.Model.UnpackedFloat.div t a b).map (·, ())
  | _, _, .ffma t, (a, b, c, ()) =>
      if !t.isFloatTree then none
      else (evalFloat3 Float.Model.UnpackedFloat.fma t a b c).map (·, ())
  | _, _, .fsqrt t, (a, ()) =>
      if !t.isFloatTree then none
      else (evalFloat1 Float.Model.UnpackedFloat.sqrt t a).map (·, ())
  | _, _, .fneg t, (a, ()) =>
      if !t.isFloatTree then none
      else some (lift1 (fun {n} x => x ^^^ (1#n <<< (n - 1))) id t a, ())
  | _, _, .fabs t, (a, ()) =>
      if !t.isFloatTree then none
      else some (lift1 (fun {n} x => x &&& ~~~(1#n <<< (n - 1))) id t a, ())
  | _, _, .fcmp o t _ rfl, (a, b, ()) =>
      if !t.isFloatTree then none else some (liftFCmp o t a b, ())
  | _, _, .fptoui f n, (a, ()) =>
      match truncToInt (unpackFloat f a) with
      | some z => if 0 ≤ z ∧ z < 2 ^ n then some (BitVec.ofInt n z, ()) else none
      | none => none
  | _, _, .fptosi f n, (a, ()) =>
      if n ≠ 0 then
        match truncToInt (unpackFloat f a) with
        | some z =>
            if -(2 ^ (n - 1) : Int) ≤ z ∧ z < 2 ^ (n - 1) then some (BitVec.ofInt n z, ())
            else none
        | none => none
      else none
  | _, _, .uitofp _ f, (a, ()) =>
      some (packFloat f (Float.Model.UnpackedFloat.ofInt f.format a.toNat), ())
  | _, _, .sitofp _ f, (a, ()) =>
      some (packFloat f (Float.Model.UnpackedFloat.ofInt f.format a.toInt), ())
  | _, _, .fcvt f g, (a, ()) => some (evalConvertFloat f g a, ())

/-- Outcome of executing one basic block to its terminator. -/
inductive BlockOutcome : Type
  | jump (pc : BitVec 64) (st : State)
  | halt (code : BitVec 64) (mem : Mem 64)

/-- Direct deterministic operational execution of a first-order `BlockFlat`. -/
@[expose] def BlockFlat.exec (ρ : SymEnv) :
    BlockFlat → List ((t : Ty) × Val t) → Mem 64 → Option BlockOutcome
  | .let_ op k, vs, m =>
      match denoteArgs vs op.args with
      | some args' =>
          match evalOpCode op.code (vals args') with
          | some r => k.exec ρ (pushTup r vs) m
          | none => none
      | none => none
  | .load ty a k, vs, m =>
      match denoteArg vs a with
      | some a' =>
          match loadVal m ty a'.val with
          | some v => k.exec ρ (⟨ty, v⟩ :: vs) m
          | none => none
      | none => none
  | .store (t := ty) v a k, vs, m =>
      match denoteArg vs v, denoteArg vs a with
      | some v', some a' =>
          if (m.loadInt a'.val ty.bytes).isSome then
            k.exec ρ vs (storeMem m ty a'.val v'.val)
          else none
      | _, _ => none
  | .codeAddr sym k, vs, m =>
      match ρ sym with
      | some a => k.exec ρ (⟨i64, a⟩ :: vs) m
      | none => none
  | .jnz c t e, vs, m =>
      match denoteArg vs c with
      | some c' => if c'.val then t.exec ρ vs m else e.exec ρ vs m
      | none => none
  | .ijmp tgt nxt, vs, m =>
      match denoteArg vs tgt, denoteRegsExpr vs nxt with
      | some tgt', some nxt' => some (.jump tgt'.val ⟨nxt'.eval, m⟩)
      | _, _ => none
  | .halt c, vs, m =>
      match denoteArg vs c with
      | some c' => some (.halt c'.val m)
      | none => none
  | .hlt, _, _ => none

/-- Single basic-block transition in `cm` starting at concrete address `pc`. -/
@[expose] def Step (cm : CodeMap) (pc : BitVec 64) (st : State) (out : BlockOutcome) : Prop :=
  ∃ b, cm.lookupAddr pc = some b ∧
    b.exec cm.symEnv (pushRegsV st.regs.toRegsV) st.mem = some out

/-- Multi-block big-step termination relation for `CodeMap`. -/
inductive Halts (cm : CodeMap) : BitVec 64 → State → BitVec 64 → Mem 64 → Prop
  | halt {pc st code m'} :
      Step cm pc st (.halt code m') →
      Halts cm pc st code m'
  | jump {pc st pc' st' code m'} :
      Step cm pc st (.jump pc' st') →
      Halts cm pc' st' code m' →
      Halts cm pc st code m'

/-- Deterministic fuel-bounded interpreter executing `BlockFlat` directly from `cm`. -/
@[expose] def runFuel (cm : CodeMap) : Nat → BitVec 64 → State → Option (BitVec 64 × Mem 64)
  | 0, _, _ => none
  | fuel + 1, pc, st =>
      match cm.lookupAddr pc with
      | none => none
      | some b =>
          match b.exec cm.symEnv (pushRegsV st.regs.toRegsV) st.mem with
          | some (.halt code m') => some (code, m')
          | some (.jump pc' st') => runFuel cm fuel pc' st'
          | none => none

/-- Convenience runner returning only the exit code. -/
@[expose] def runCode (cm : CodeMap) (fuel : Nat) (pc : BitVec 64) (st : State) :
    Option (BitVec 64) :=
  (runFuel cm fuel pc st).map Prod.fst

/-- Trace event emitted by `runTrace`. -/
inductive TraceEv : Type
  | jump (fromPc toPc : BitVec 64) (rv r1 r2 r3 sp rp : BitVec 64)
  | halt (atPc code : BitVec 64)
  | stuck (atPc : BitVec 64)
  | outOfFuel (atPc : BitVec 64)
  deriving DecidableEq, Repr

/-- Traced interpreter recording every indirect jump and halt. -/
@[expose] def runTrace (cm : CodeMap) :
    Nat → BitVec 64 → State → List TraceEv × Option (BitVec 64)
  | 0, pc, _ => ([.outOfFuel pc], none)
  | fuel + 1, pc, st =>
      match cm.lookupAddr pc with
      | none => ([.stuck pc], none)
      | some b =>
          match b.exec cm.symEnv (pushRegsV st.regs.toRegsV) st.mem with
          | some (.halt code _) => ([.halt pc code], some code)
          | some (.jump pc' st') =>
              let ev := TraceEv.jump pc pc' st'.regs.rv st'.regs.r1 st'.regs.r2
                st'.regs.r3 st'.regs.sp st'.regs.rp
              let res := runTrace cm fuel pc' st'
              (ev :: res.1, res.2)
          | none => ([.stuck pc], none)

/-! ## §4. ICFP'13 Generative Structured Macros -/

/-- Half-open 8-byte-aligned address range `[base, base + 8 * n)`. -/
@[expose] def InRange (base : BitVec 64) (n : Nat) (a : BitVec 64) : Prop :=
  ∃ i : Nat, i < n ∧ a = base + BitVec.ofNat 64 (8 * i)

/-- An ICFP'13-style generative structured macro. -/
structure Macro : Type 1 where
  size : Nat
  emit : (pfx : String) → (base cont : BitVec 64) → List CodeEntryP

/-- Compiled concrete `CodeMap` of a macro placed at `(pfx, base, cont)`. -/
@[expose] def Macro.compile (m : Macro) (pfx : String) (base cont : BitVec 64) : CodeMap :=
  compileEntries (m.emit pfx base cont)

/-- Structural layout well-formedness of a macro. -/
@[expose] def Macro.WellLaidOut (m : Macro) : Prop :=
  ∀ (pfx : String) (base cont : BitVec 64),
    ∀ e ∈ m.emit pfx base cont, InRange base m.size e.addr ∧ e.body.Wf

/-- Single straight-line atomic macro ending in a fallthrough jump to `cont`. -/
@[expose] def atomicM
    (step : ∀ (V : Ty → Type), RegsV V → (RegsExpr V → BlockB V) → BlockB V) : Macro where
  size := 1
  emit pfx base cont :=
    [⟨pfx, base, fun V r => step V r (fun nxt => .ijmp (.imm cont) nxt)⟩]

/-- Structured sequencing: `m₁` falls through to `m₂`'s entry at `base + 8 * m₁.size`. -/
@[expose] def seqM (m₁ m₂ : Macro) : Macro where
  size := m₁.size + m₂.size
  emit pfx base cont :=
    let mid := base + BitVec.ofNat 64 (8 * m₁.size)
    m₁.emit (pfx ++ "_1") base mid ++ m₂.emit (pfx ++ "_2") mid cont

/-- Structured conditional branch. -/
@[expose] def ifM (cond : ∀ (V : Ty → Type), RegsV V → (V .bool → BlockB V) → BlockB V)
    (mT mE : Macro) : Macro where
  size := 1 + mT.size + mE.size
  emit pfx base cont :=
    let tAddr := base + 8#64
    let eAddr := base + BitVec.ofNat 64 (8 * (1 + mT.size))
    ⟨pfx ++ "_if", base, fun V r =>
      cond V r (fun b =>
        .jnz (.var b) (.ijmp (.imm tAddr) r.keep) (.ijmp (.imm eAddr) r.keep))⟩ ::
    (mT.emit (pfx ++ "_t") tAddr cont ++ mE.emit (pfx ++ "_e") eAddr cont)

/-- Structured `while` loop. -/
@[expose] def whileM (cond : ∀ (V : Ty → Type), RegsV V → (V .bool → BlockB V) → BlockB V)
    (body : Macro) : Macro where
  size := 1 + body.size
  emit pfx base cont :=
    let bodyAddr := base + 8#64
    ⟨pfx ++ "_hdr", base, fun V r =>
      cond V r (fun b =>
        .jnz (.var b) (.ijmp (.imm bodyAddr) r.keep) (.ijmp (.imm cont) r.keep))⟩ ::
    body.emit (pfx ++ "_b") bodyAddr base

/-- Structured non-tail call macro saving `rp` and `r3` on `[sp - 8..-16]`. -/
@[expose] def callM (callee : Sym) : Macro where
  size := 2
  emit pfx base cont :=
    [ ⟨pfx ++ "_call", base, fun _ r =>
        .letOp2 (.sub i64) (.var r.sp) (.imm 8#64) fun sp1 =>
        .store64 (.var r.rp) (.var sp1) <|
        .letOp2 (.sub i64) (.var sp1) (.imm 8#64) fun sp2 =>
        .store64 (.var r.r3) (.var sp2) <|
        .codeAddr (pfx ++ "_ret") fun retPc =>
        .codeAddr callee fun fnPc =>
        .ijmp (.var fnPc) { r.keep with sp := .var sp2, rp := .var retPc }⟩,
      ⟨pfx ++ "_ret", base + 8#64, fun _ r =>
        .load64 (.var r.sp) fun savedR3 =>
        .letOp2 (.add i64) (.var r.sp) (.imm 8#64) fun sp1 =>
        .load64 (.var sp1) fun savedRp =>
        .letOp2 (.add i64) (.var sp1) (.imm 8#64) fun sp0 =>
        .ijmp (.imm cont)
          { r.keep with sp := .var sp0, rp := .var savedRp, r3 := .var savedR3 }⟩ ]

/-- Structured return macro: indirect jump through `rp`. -/
@[expose] def retM : Macro where
  size := 1
  emit pfx base _ :=
    [⟨pfx ++ "_ret", base, fun _ r => .ijmp (.var r.rp) r.keep⟩]

/-- Structured tail-call macro. -/
@[expose] def tailCallM (callee : Sym) : Macro where
  size := 1
  emit pfx base _ :=
    [⟨pfx ++ "_tail", base, fun _ r => .jmpSym callee r.keep⟩]

/-- Structured halt macro returning `rv`. -/
@[expose] def haltM : Macro where
  size := 1
  emit pfx base _ :=
    [⟨pfx ++ "_halt", base, fun _ r => .halt (.var r.rv)⟩]

end LeanQbe.T.BedrockWord
