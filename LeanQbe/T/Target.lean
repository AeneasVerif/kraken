module

public import Lean.ToExpr
public import Kraken.OmniSemantics
public import Kraken.Data.List.Infix
public import LeanQbe.T.Trie
public import LeanQbe.T.Logic.Mem

/-!
# Typed Target Interface, Disjoint Sub-Records, `Hints`, `FnSpec`, and `backendOk` (`H3`/`T11a`, `H4`)

Target-generic contract for `T7` (`Rega`), `T8`/`T9` (`Gpr*`), `T10` (`Vec*`), `T11b` (`Frame*`), and
`T12` (`Main`). Representation-agnostic (`PHOAS`-first; zero `Kraken.X64`/`AArch64`/`TFlat` imports).
Locks `L2`–`L8`, `L10`, `R5`, `R11`, `R13`–`R14`, and E1 `Abi`/code-health invariants (#153–#169).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## 1. 8-Byte Stack-Slot Granules (`L10`, reusing `region`/`cell64`/`array64` from `Logic.Mem`) -/

inductive SlotWidth where
  | w64 | w128 | w256 | w512
  deriving DecidableEq, Repr, Inhabited, Hashable, Lean.ToExpr

@[reducible] def SlotWidth.slots : SlotWidth → Nat
  | .w64 => 1 | .w128 => 2 | .w256 => 4 | .w512 => 8

@[reducible] def SlotWidth.bits : SlotWidth → Nat
  | .w64 => 64 | .w128 => 128 | .w256 => 256 | .w512 => 512

def unpackSlotWords : SlotWidth → BitVec 512 → List (BitVec 64)
  | .w64, v => [v.extractLsb' 0 64]
  | .w128, v => [v.extractLsb' 0 64, v.extractLsb' 64 64]
  | .w256, v =>
    [v.extractLsb' 0 64, v.extractLsb' 64 64, v.extractLsb' 128 64, v.extractLsb' 192 64]
  | .w512, v =>
    [v.extractLsb' 0 64, v.extractLsb' 64 64, v.extractLsb' 128 64, v.extractLsb' 192 64,
     v.extractLsb' 256 64, v.extractLsb' 320 64, v.extractLsb' 384 64, v.extractLsb' 448 64]

/-! ## 2. Flat `Loc`, Clobber Masks, Moves, and Logarithmic Trie `Hints` (`L2`–`L7`, `G9`) -/

abbrev FlagMask : Type := BitVec 8
def FlagMask.none : FlagMask := 0x00#8
def FlagMask.all  : FlagMask := 0xFF#8

@[reducible] def FlagMask.disjoint (reads clob : FlagMask) : Bool :=
  (reads &&& clob) == 0#8

inductive Loc (Reg VReg Cond : Type) where
  | gpr (r : Reg)
  | vec (v : VReg)
  | flag (c : Cond)
  | slot (i : Nat) (w : SlotWidth)
  deriving DecidableEq, Repr, Lean.ToExpr

inductive VariantHint where
  | default | adcx | adox | mulxFast | decInc | disp (off : Int64)
  deriving DecidableEq, Repr, Inhabited, Hashable, Lean.ToExpr

/-- Checked moves (`L3`, `L4`, `L10`): all preserve flags (`clob = 0#8`).
`setcc` is the sole flag move. -/
inductive Move (Reg VReg Cond : Type) where
  | mov (d s : Reg)
  | movi (d : Reg) (c : BitVec 64)
  | ld (d : Reg) (i : Nat)
  | st (i : Nat) (s : Reg)
  | setcc (d : Reg) (c : Cond)
  | vmov (w : SlotWidth) (d s : VReg)
  | vmovi (w : SlotWidth) (d : VReg) (c : BitVec 512)
  | vld (w : SlotWidth) (d : VReg) (i : Nat)
  | vst (w : SlotWidth) (i : Nat) (s : VReg)
  deriving DecidableEq, Repr, Lean.ToExpr

structure PreStep (Reg VReg Cond : Type) where
  clearFlags : Bool := false
  moves : List (Move Reg VReg Cond) := []
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

inductive SymArg where
  | var (x : Nat)
  | immBool (b : Bool)
  | immBits (w : Nat) (c : BitVec 64)
  | immVec (w : SlotWidth) (c : BitVec 512)
  deriving DecidableEq, Repr, Lean.ToExpr

structure Entry (Reg VReg Cond : Type) where
  live : List (SymArg × Loc Reg VReg Cond) := []
  ploc : List (Loc Reg VReg Cond) := []
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

structure Hints (Reg VReg Cond : Type) where
  dest : Trie (Loc Reg VReg Cond) := .empty
  entry : Trie (Entry Reg VReg Cond) := .empty
  pre : Trie (PreStep Reg VReg Cond) := .empty
  variant : Trie VariantHint := .empty
  elide : Trie Bool := .empty
  nslots : Nat := 0
  saved : List Reg := []
  deriving Repr, Lean.ToExpr

def Hints.totalSlots {R V C : Type} (h : Hints R V C) : Nat :=
  h.nslots + h.saved.length

/-! ## 3. Physical Snippet Operands and Disjoint `Isa` Sub-Records (`R5`) -/

inductive AddrArg (Reg : Type) where
  | baseDisp (base : Reg) (disp : Int64 := 0)
  | imm (addr : BitVec 64)
  deriving DecidableEq, Repr

def AddrArg.eval {Reg : Type} (get : Reg → BitVec 64) : AddrArg Reg → BitVec 64
  | .baseDisp r d => get r + d.toBitVec
  | .imm a => a

def AddrArg.regs {Reg : Type} : AddrArg Reg → List Reg
  | .baseDisp r _ => [r]
  | .imm _ => []

inductive PArg (Reg VReg Cond : Type) : Ty → Type where
  | gpr {t : Ty} (r : Reg) : PArg Reg VReg Cond t
  | vec {t : Ty} (v : VReg) : PArg Reg VReg Cond t
  | flag (c : Cond) : PArg Reg VReg Cond .bool
  | imm {t : Ty} (c : Val t) : PArg Reg VReg Cond t

inductive PDst (Reg VReg Cond : Type) : Ty → Type where
  | gpr {t : Ty} (r : Reg) : PDst Reg VReg Cond t
  | vec {t : Ty} (v : VReg) : PDst Reg VReg Cond t
  | flag (c : Cond) : PDst Reg VReg Cond .bool

@[simp] def PArg.gprs {R V C : Type} {t : Ty} : PArg R V C t → List R
  | .gpr r => [r] | _ => []

@[simp] def PArg.vecs {R V C : Type} {t : Ty} : PArg R V C t → List V
  | .vec v => [v] | _ => []

@[simp] def PDst.gprs {R V C : Type} {t : Ty} : PDst R V C t → List R
  | .gpr r => [r] | _ => []

@[simp] def PDst.vecs {R V C : Type} {t : Ty} : PDst R V C t → List V
  | .vec v => [v] | _ => []

def tupFlatMap {F : Ty → Type} {α : Type} (f : {t : Ty} → F t → List α) :
    {ts : List Ty} → Tup F ts → List α
  | [], () => []
  | _ :: _, (x, xs) => f x ++ tupFlatMap f xs

@[simp] theorem tupFlatMap_nil {F : Ty → Type} {α : Type} (f : {t : Ty} → F t → List α)
    (xs : Tup F []) :
    tupFlatMap (F := F) f (ts := []) xs = [] := rfl

@[simp] theorem tupFlatMap_cons {F : Ty → Type} {α : Type} (f : {t : Ty} → F t → List α)
    {t : Ty} {ts : List Ty} (xs : Tup F (t :: ts)) :
    tupFlatMap (F := F) f (ts := t :: ts) xs = f xs.1 ++ tupFlatMap (F := F) f xs.2 := rfl

def tupArgGprs {R V C : Type} {ts : List Ty} (xs : Tup (PArg R V C) ts) : List R :=
  tupFlatMap PArg.gprs xs

def tupArgVecs {R V C : Type} {ts : List Ty} (xs : Tup (PArg R V C) ts) : List V :=
  tupFlatMap PArg.vecs xs

def tupDstGprs {R V C : Type} {ts : List Ty} (xs : Tup (PDst R V C) ts) : List R :=
  tupFlatMap PDst.gprs xs

def tupDstVecs {R V C : Type} {ts : List Ty} (xs : Tup (PDst R V C) ts) : List V :=
  tupFlatMap PDst.vecs xs

theorem tupArgGprs_nil {R V C : Type} (xs : Tup (PArg R V C) []) :
    tupArgGprs (R := R) (V := V) (C := C) (ts := []) xs = [] := rfl

theorem tupArgGprs_cons {R V C : Type} {t : Ty} {ts : List Ty}
    (xs : Tup (PArg R V C) (t :: ts)) :
    tupArgGprs (ts := t :: ts) xs = xs.1.gprs ++ tupArgGprs xs.2 := rfl

theorem tupArgVecs_nil {R V C : Type} (xs : Tup (PArg R V C) []) :
    tupArgVecs (R := R) (V := V) (C := C) (ts := []) xs = [] := rfl

theorem tupArgVecs_cons {R V C : Type} {t : Ty} {ts : List Ty}
    (xs : Tup (PArg R V C) (t :: ts)) :
    tupArgVecs (ts := t :: ts) xs = xs.1.vecs ++ tupArgVecs xs.2 := rfl

theorem tupDstGprs_nil {R V C : Type} (xs : Tup (PDst R V C) []) :
    tupDstGprs (R := R) (V := V) (C := C) (ts := []) xs = [] := rfl

theorem tupDstGprs_cons {R V C : Type} {t : Ty} {ts : List Ty}
    (xs : Tup (PDst R V C) (t :: ts)) :
    tupDstGprs (ts := t :: ts) xs = xs.1.gprs ++ tupDstGprs xs.2 := rfl

theorem tupDstVecs_nil {R V C : Type} (xs : Tup (PDst R V C) []) :
    tupDstVecs (R := R) (V := V) (C := C) (ts := []) xs = [] := rfl

theorem tupDstVecs_cons {R V C : Type} {t : Ty} {ts : List Ty}
    (xs : Tup (PDst R V C) (t :: ts)) :
    tupDstVecs (ts := t :: ts) xs = xs.1.vecs ++ tupDstVecs xs.2 := rfl

/-- Scalar opcode gate (`H4`, `module` `rfl`-safe via `contains`/`Nat.ble` per `#165`):
splits `hasBitCounts` from `hasPopcnt` (#156). -/
def defaultSupportsScalarOp (ws : List Nat) (hasBitCounts hasPopcnt hasDiv0 : Bool)
    {sig rs : List Ty} (code : OpCode sig rs)
    (_args : Tup (Arg (fun _ => Unit)) sig) : Bool :=
  match sig, rs, code with
  | _, _, .copy (.bits n) | _, _, .add (.bits n) | _, _, .sub (.bits n) | _, _, .mul (.bits n)
  | _, _, .neg (.bits n) | _, _, .and (.bits n) | _, _, .or (.bits n) | _, _, .xor (.bits n)
  | _, _, .not (.bits n) | _, _, .shl (.bits n) | _, _, .lshr (.bits n) | _, _, .ashr (.bits n)
  | _, _, .rotl (.bits n) | _, _, .rotr (.bits n) | _, _, .fshl n | _, _, .fshr n | _, _, .ofBool n
  | _, _, .addc n | _, _, .subb n | _, _, .umulw n | _, _, .smulw n | _, _, .udiv n | _, _, .sdiv n
  | _, _, .urem n | _, _, .srem n | _, _, .cmp _ (.bits n) _ _
  | _, _, .select (.bits n) => ws.contains n
  | _, _, .copy .bool | _, _, .and .bool | _, _, .or .bool
  | _, _, .xor .bool | _, _, .not .bool => true
  | _, _, .clz n | _, _, .cls n | _, _, .rbit n | _, _, .ctz n => hasBitCounts && ws.contains n
  | _, _, .popcnt n => hasPopcnt && ws.contains n
  | _, _, .udiv0 n | _, _, .sdiv0 n => hasDiv0 && ws.contains n
  | _, _, .bswap (.bits n) => ws.contains n && (n % 8 == 0) && Nat.ble 9 n
  | _, _, .zext m n | _, _, .sext m n => ws.contains m && ws.contains n && Nat.ble (m + 1) n
  | _, _, .trunc m n => ws.contains m && ws.contains n && Nat.ble (n + 1) m
  | _, _, .bitcast (.bits m) (.bits n) _ => ws.contains m && ws.contains n
  | _, _, _ => false

structure GprIsa (Reg VReg Cond Directive : Type) where
  condReads : Cond → FlagMask
  negCond : Cond → Cond
  zeroFlags : List Cond
  clearFlags : List Directive
  mov : Reg → Reg → List Directive
  movi : Reg → BitVec 64 → List Directive
  setcc : Reg → Cond → List Directive
  jmp : Sym → List Directive
  jcc : Cond → Sym → List Directive
  jnzGpr : Reg → Sym → List Directive × FlagMask
  op : {sig rs : List Ty} → OpCode sig rs → Tup (PArg Reg VReg Cond) sig →
    Tup (PDst Reg VReg Cond) rs → VariantHint → Option (List Directive × FlagMask)
  load : Ty → Reg → AddrArg Reg → Option (List Directive × FlagMask)
  store : (t : Ty) → PArg Reg VReg Cond t → AddrArg Reg → Option (List Directive × FlagMask)
  supportsScalarOp : {sig rs : List Ty} → (c : OpCode sig rs) →
    Tup (Arg (fun _ => Unit)) sig → Bool
  /-- Comparison condition codes `Spill` may keep a `cmp` result in (untrusted hint input). -/
  cmpFlags : List Cond := []

structure VecIsa (Reg VReg Cond Directive : Type) where
  vecScratch : List VReg
  vecAllocatable : List VReg
  vecArgRegs : List VReg
  vecRetRegs : List VReg
  isAbiVec : Ty → Bool
  vecSlotWidth : Ty → Option SlotWidth
  vmov : SlotWidth → VReg → VReg → List Directive
  vmovi : SlotWidth → VReg → BitVec 512 → Option (List Directive)
  vslotSt : SlotWidth → Nat → VReg → List Directive
  vslotLd : SlotWidth → VReg → Nat → List Directive
  vop : {sig rs : List Ty} → OpCode sig rs → Tup (PArg Reg VReg Cond) sig →
    Tup (PDst Reg VReg Cond) rs → VariantHint → Option (List Directive × FlagMask)
  vload : Ty → VReg → AddrArg Reg → Option (List Directive × FlagMask)
  vstore : Ty → VReg → AddrArg Reg → Option (List Directive × FlagMask)
  supportsVecOp : {sig rs : List Ty} → (c : OpCode sig rs) →
    Tup (Arg (fun _ => Unit)) sig → Bool

def VecIsa.empty (Reg Cond Directive : Type) : VecIsa Reg Empty Cond Directive :=
  ⟨[], [], [], [], fun _ => false, fun _ => none, fun _ r => r.elim, fun _ r _ => r.elim,
   fun _ _ r => r.elim, fun _ r => r.elim, fun _ _ _ _ => none, fun _ r _ => r.elim,
   fun _ r _ => r.elim, fun _ _ => false⟩

structure FrameIsa (Reg Directive : Type) where
  label : Sym → Directive
  sp : Reg
  scratch : List Reg
  allocatable : List Reg
  calleeSaved : List Reg
  raRegs : List Reg
  argRegs : List Reg
  retRegs : List Reg
  bitWidths : List Nat := [8, 16, 32, 64]
  raBytes : Nat
  frameSize : Nat → Nat
  prologue : Nat → List Directive × FlagMask
  epilogue : Nat → List Directive × FlagMask
  slotSt : Nat → Reg → List Directive
  slotLd : Reg → Nat → List Directive
  canonAbi : Ty → Reg → List Directive × FlagMask
  call : Sym → List Directive
  exitJmp : Sym → List Directive
  ret : List Directive

structure Isa where
  Reg : Type
  VReg : Type
  Cond : Type
  Directive : Type
  [decEqReg : DecidableEq Reg]
  [decEqVReg : DecidableEq VReg]
  [decEqCond : DecidableEq Cond]
  gpr : GprIsa Reg VReg Cond Directive
  vec : VecIsa Reg VReg Cond Directive
  frame : FrameIsa Reg Directive
  /-- Untrusted displacement legality predicate (`base + disp`) for address-op elision. -/
  supportsAddrDisp : Ty → BitVec 64 → Bool := fun _ _ => false

attribute [instance] Isa.decEqReg Isa.decEqVReg Isa.decEqCond
abbrev Isa.Loc (I : Isa) : Type := _root_.LeanQbe.T.Loc I.Reg I.VReg I.Cond
abbrev Isa.Move (I : Isa) : Type := _root_.LeanQbe.T.Move I.Reg I.VReg I.Cond
abbrev Isa.Hints (I : Isa) : Type := _root_.LeanQbe.T.Hints I.Reg I.VReg I.Cond

/-! ## 4. ABI Register Assignment and PHOAS-First `backendOk` (`H4`, `R11`, `R13`, `#153`, `#156`) -/

inductive AbiReg (Reg VReg : Type) : Ty → Type where
  | gpr {t : Ty} (r : Reg) : AbiReg Reg VReg t
  | vec {t : Ty} (v : VReg) : AbiReg Reg VReg t

def Isa.isLegalTy (I : Isa) : Ty → Bool
  | .bool => true
  | .bits n => I.frame.bitWidths.contains n
  | .float _ => false
  | .pair a b => I.vec.isAbiVec (.pair a b)

def Isa.hasBank (I : Isa) : Ty → Bool
  | .bool => true
  | .bits n => I.frame.bitWidths.contains n
  | .float _ => false
  | .pair a b => (I.vec.vecSlotWidth (.pair a b)).isSome

def Isa.assignSig (I : Isa) :
    (ts : List Ty) → List I.Reg → List I.VReg → Option (Tup (AbiReg I.Reg I.VReg) ts)
  | [], _, _ => some ()
  | .bool :: ts, r :: gs, vs => (I.assignSig ts gs vs).map (.gpr r, ·)
  | .bits n :: ts, r :: gs, vs =>
    if I.frame.bitWidths.contains n then (I.assignSig ts gs vs).map (.gpr r, ·) else none
  | .pair a b :: ts, gs, v :: vs =>
    if I.vec.isAbiVec (.pair a b) then (I.assignSig ts gs vs).map (.vec v, ·) else none
  | _, _, _ => none

def Isa.assignArgs (I : Isa) (as : List Ty) :=
  I.assignSig as I.frame.argRegs I.vec.vecArgRegs

def Isa.assignRets (I : Isa) (rs : List Ty) :=
  I.assignSig rs I.frame.retRegs I.vec.vecRetRegs

def Isa.supportsOp (I : Isa) {sig rs : List Ty} (code : OpCode sig rs)
    (args : Tup (Arg (fun _ => Unit)) sig) : Bool :=
  sig.all I.hasBank && rs.all I.hasBank &&
    (I.gpr.supportsScalarOp code args || I.vec.supportsVecOp code args)

mutual
def Expr.backendOk (I : Isa) {rs : List Ty} : Expr (fun _ => Unit) (fun _ => Unit) rs → Bool
  | .let_ (ts := ts) op k =>
    I.supportsOp op.code op.args && (k (Tup.units ts)).backendOk I
  | .load t _ k => I.isLegalTy i64 && I.isLegalTy t && (k ()).backendOk I
  | .store (t := t) _ _ k => I.isLegalTy i64 && I.isLegalTy t && k.backendOk I
  | .call _ (as := as) (bs := bs) _ k =>
    (I.assignArgs as).isSome && (I.assignRets bs).isSome && (k (Tup.units bs)).backendOk I
  | .jnz _ t e => I.isLegalTy .bool && t.backendOk I && e.backendOk I
  | .jump (ts := ts) _ _ => ts.all I.isLegalTy
  | .ret _ => (I.assignRets rs).isSome
  | .exit _ (as := as) _ => (I.assignArgs as).isSome
  | .hlt => true
  | .group (sig := sig) bodies k =>
    sig.all (·.all I.isLegalTy) &&
      (bodies (Tup.units sig)).backendOk I && (k (Tup.units sig)).backendOk I

def Blocks.backendOk (I : Isa) {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig → Bool
  | _, .nil => true
  | _, .cons (ts := ts) b bs => (b (Tup.units ts)).backendOk I && bs.backendOk I
end

def Fn.backendOk (I : Isa) (fn : Fn) : Bool :=
  (I.assignArgs fn.as).isSome && (I.assignRets fn.rs).isSome &&
    (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as)).backendOk I

theorem Fn.assign_of_backendOk {I : Isa} {fn : Fn} (h : fn.backendOk I = true) :
    (I.assignArgs fn.as).isSome = true ∧ (I.assignRets fn.rs).isSome = true := by
  simp only [Fn.backendOk, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2⟩

/-! ## 5. Machine Semantics, Value Invariants (`L8`, `L10`, `R14`), `Target`, and `FnSpec` -/

def GprHolds (regVal : BitVec 64) : (t : Ty) → Val t → Prop
  | .bool, b => regVal.setWidth 8 = BitVec.ofNat 8 b.toNat
  | .bits n, v => n ≤ 64 ∧ regVal.setWidth n = v
  | _, _ => False

def AbiGprHolds (regVal : BitVec 64) : (t : Ty) → Val t → Prop
  | .bool, b => regVal = BitVec.ofNat 64 b.toNat
  | .bits n, v => n ≤ 64 ∧ regVal = v.setWidth 64
  | _, _ => False

theorem AbiGprHolds.toGprHolds {w : BitVec 64} {t : Ty} {v : Val t}
    (h : AbiGprHolds w t v) : GprHolds w t v := by
  cases t with
  | bool => subst h; cases v <;> rfl
  | bits n =>
    have ⟨hn, hw⟩ := h
    refine ⟨hn, ?_⟩
    rw [hw]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [show (i : Nat) < n from hi, show (i : Nat) < 64 by omega]
  | float _ | pair _ _ => exact h

def VecHolds (vecVal : BitVec 512) (t : Ty) (v : Val t) : Prop :=
  t.size ≤ 512 ∧ vecVal.setWidth t.size = toBits t v

structure Machine (Reg VReg Cond Directive : Type) where
  MData : Type
  Addr : Type
  State : Type
  Host : Type
  getGpr : MData → Reg → BitVec 64
  getVec : MData → VReg → BitVec 512
  evalCond : MData → Cond → Bool
  mem : MData → Mem 64
  mkState : MData → Addr → State
  pc : State → Addr
  data : State → MData
  pc_mk : ∀ s a, pc (mkState s a) = a
  data_mk : ∀ s a, data (mkState s a) = s
  mk_eta : ∀ st, mkState (data st) (pc st) = st
  prog : Host → List Directive
  addrOf : Host → Nat → Addr
  labelAddr : Host → Sym → Addr
  step : Host → State → (State → Prop) → Prop

namespace Machine
variable {R V C D : Type} (M : Machine R V C D)

def Run (h : M.Host) (k : Nat) (s : M.MData) (post : M.State → Prop) : Prop :=
  Eventually (M.step h) post (M.mkState s (M.addrOf h k))

def KeepsGpr (s s' : M.MData) (clob : List R) : Prop :=
  ∀ r, r ∉ clob → M.getGpr s' r = M.getGpr s r

def KeepsVec (s s' : M.MData) (clob : List V) : Prop :=
  ∀ v, v ∉ clob → M.getVec s' v = M.getVec s v

def UpdFlags (condReads : C → FlagMask) (s s' : M.MData) (mask : FlagMask) : Prop :=
  ∀ c, FlagMask.disjoint (condReads c) mask = true → M.evalCond s' c = M.evalCond s c

abbrev KeepsFlags := @UpdFlags R V C D M

def Frame (condReads : C → FlagMask) (s s' : M.MData)
    (gClob : List R) (vClob : List V) (fClob : FlagMask) : Prop :=
  M.KeepsGpr s s' gClob ∧ M.KeepsVec s s' vClob ∧ M.UpdFlags condReads s s' fClob

def FallsTo (condReads : C → FlagMask) (h : M.Host) (k : Nat) (c : List D)
    (gClob : List R) (vClob : List V) (fClob : FlagMask)
    (s : M.MData) (Q : M.MData → Prop) (post : M.State → Prop) : Prop :=
  c.IsInfixAt (M.prog h) k →
    (∀ s', Q s' → M.Frame condReads s s' gClob vClob fClob → M.Run h (k + c.length) s' post) →
    M.Run h k s post

def PArgHolds (s : M.MData) : (t : Ty) → PArg R V C t → Val t → Prop
  | t, .gpr r, v => GprHolds (M.getGpr s r) t v
  | t, .vec vr, v => VecHolds (M.getVec s vr) t v
  | .bool, .flag c, b => M.evalCond s c = b
  | _, .imm c, v => c = v

def PDstHolds (s : M.MData) : (t : Ty) → PDst R V C t → Val t → Prop
  | t, .gpr r, v => GprHolds (M.getGpr s r) t v
  | t, .vec vr, v => VecHolds (M.getVec s vr) t v
  | .bool, .flag c, b => M.evalCond s c = b

def AbiHolds (s : M.MData) : (t : Ty) → AbiReg R V t → Val t → Prop
  | t, .gpr r, v => AbiGprHolds (M.getGpr s r) t v
  | t, .vec vr, v => VecHolds (M.getVec s vr) t v
end Machine

structure GprTarget {R V C D : Type} (M : Machine R V C D) (g : GprIsa R V C D)
    (scratch : List R) : Prop where
  negCond_reads : ∀ c, g.condReads (g.negCond c) = g.condReads c
  negCond_eval : ∀ s c, M.evalCond s (g.negCond c) = !M.evalCond s c
  clearFlags_spec : ∀ {h k s post},
    M.FallsTo g.condReads h k g.clearFlags scratch [] FlagMask.all s
      (fun s' => (∀ c ∈ g.zeroFlags, M.evalCond s' c = false) ∧ M.mem s' = M.mem s) post
  mov_spec : ∀ {h k rd rs s post},
    M.FallsTo g.condReads h k (g.mov rd rs) [rd] [] FlagMask.none s
      (fun s' => M.getGpr s' rd = M.getGpr s rs ∧ M.mem s' = M.mem s) post
  movi_spec : ∀ {h k rd c s post},
    M.FallsTo g.condReads h k (g.movi rd c) (rd :: scratch) [] FlagMask.none s
      (fun s' => M.getGpr s' rd = c ∧ M.mem s' = M.mem s) post
  setcc_spec : ∀ {h k rd c s post}, rd ∉ scratch →
    M.FallsTo g.condReads h k (g.setcc rd c) (rd :: scratch) [] FlagMask.none s
      (fun s' => GprHolds (M.getGpr s' rd) .bool (M.evalCond s c) ∧ M.mem s' = M.mem s) post
  jmp_spec : ∀ {h k j l s post},
    (g.jmp l).IsInfixAt (M.prog h) k → M.labelAddr h l = M.addrOf h j →
    (∀ s', M.Frame g.condReads s s' scratch [] FlagMask.none →
      M.mem s' = M.mem s → M.Run h j s' post) →
    M.Run h k s post
  jcc_spec : ∀ {h k j c l s post},
    (g.jcc c l).IsInfixAt (M.prog h) k → M.labelAddr h l = M.addrOf h j →
    (∀ s', M.Frame g.condReads s s' scratch [] FlagMask.none → M.mem s' = M.mem s →
      (M.evalCond s c = true → M.Run h j s' post) ∧
      (M.evalCond s c = false → M.Run h (k + (g.jcc c l).length) s' post)) →
    M.Run h k s post
  jnzGpr_spec : ∀ {h k j r l b s post},
    (g.jnzGpr r l).1.IsInfixAt (M.prog h) k → M.labelAddr h l = M.addrOf h j →
    r ∉ scratch → GprHolds (M.getGpr s r) .bool b →
    (∀ s', M.Frame g.condReads s s' scratch [] (g.jnzGpr r l).2 → M.mem s' = M.mem s →
      (b = true → M.Run h j s' post) ∧
      (b = false → M.Run h (k + (g.jnzGpr r l).1.length) s' post)) →
    M.Run h k s post
  op_spec : ∀ {h k sig rs} {code : OpCode sig rs} {pas dsts vh c clob vs P s post},
    g.op code pas dsts vh = some (c, clob) →
    (∀ r ∈ tupArgGprs pas, r ∉ scratch) → (∀ r ∈ tupDstGprs dsts, r ∉ scratch) →
    TRel (M.PArgHolds s) pas vs → code.wp vs P →
    M.FallsTo g.condReads h k c (tupDstGprs dsts ++ scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (M.PDstHolds s') dsts rvs) ∧ M.mem s' = M.mem s) post
  load_spec : ∀ {h k t rd a c clob v s post},
    g.load t rd a = some (c, clob) → rd ∉ scratch → (∀ r ∈ a.regs, r ∉ scratch) →
    loadVal (M.mem s) t (a.eval (M.getGpr s)) = some v →
    M.FallsTo g.condReads h k c (rd :: scratch) [] clob s
      (fun s' => GprHolds (M.getGpr s' rd) t v ∧ M.mem s' = M.mem s) post
  store_spec : ∀ {h k t pa a c clob v s post},
    g.store t pa a = some (c, clob) → (∀ r ∈ pa.gprs ++ a.regs, r ∉ scratch) →
    M.PArgHolds s t pa v → storeOk (M.mem s) t (a.eval (M.getGpr s)) →
    M.FallsTo g.condReads h k c scratch [] clob s
      (fun s' => M.mem s' = storeMem (M.mem s) t (a.eval (M.getGpr s)) v) post

structure FrameTarget {R V C D : Type} (M : Machine R V C D) (f : FrameIsa R D)
    (condReads : C → FlagMask) : Type where
  RetAddr : BitVec 64 → M.Addr → Mem 64 → Prop
  raReg : M.MData → M.Addr → Prop
  spEntry : BitVec 64 → Prop
  spOk : BitVec 64 → Prop
  Saved : BitVec 64 → M.Addr → Nat → Mem 64 → Prop
  sp_disj : f.sp ∉ f.scratch ∧ f.sp ∉ f.allocatable ∧ f.sp ∉ f.calleeSaved ∧
    f.sp ∉ f.argRegs ∧ f.sp ∉ f.retRegs ∧ f.sp ∉ f.raRegs
  scratch_disj : ∀ r ∈ f.scratch,
    r ∉ f.allocatable ∧ r ∉ f.calleeSaved ∧ r ∉ f.argRegs ∧ r ∉ f.retRegs
  cs_disj : ∀ r ∈ f.calleeSaved, r ∉ f.allocatable ∧ r ∉ f.argRegs ∧ r ∉ f.retRegs
  ra_disj : ∀ r ∈ f.raRegs,
    r ∉ f.allocatable ∧ r ∉ f.scratch ∧ r ∉ f.calleeSaved ∧ r ∉ f.argRegs ∧ r ∉ f.retRegs
  argRegs_nodup : f.argRegs.Nodup
  retRegs_nodup : f.retRegs.Nodup
  retAddr_region : ∀ a ra m, RetAddr a ra m → region a f.raBytes m
  raReg_of_raRegs : ∀ s s' ra,
    (∀ r ∈ f.raRegs, M.getGpr s' r = M.getGpr s r) → raReg s ra → raReg s' ra
  slots_le_frameSize : ∀ ns, 8 * ns ≤ f.frameSize ns
  spOk_frame : ∀ sp ns, spEntry sp → spOk (sp - BitVec.ofNat 64 (f.frameSize ns))
  spEntry_call : ∀ sp ns, spEntry sp →
    spEntry (sp - BitVec.ofNat 64 (f.frameSize ns) - BitVec.ofNat 64 f.raBytes)
  labelAddr_eq : ∀ {h} {k : Nat} {l},
    (M.prog h)[k]? = some (f.label l) →
    (∀ j < k, (M.prog h)[j]? ≠ some (f.label l)) → M.labelAddr h l = M.addrOf h k
  label_spec : ∀ {h} {k : Nat} {l s post},
    (M.prog h)[k]? = some (f.label l) → M.Run h (k + 1) s post → M.Run h k s post
  prologue_spec : ∀ {h k ns s ra G post},
    raReg s ra → spEntry (M.getGpr s f.sp) → f.frameSize ns + f.raBytes ≤ 2 ^ 64 →
    (M.mem s =⋆ RetAddr (M.getGpr s f.sp) ra ⋆
      region (M.getGpr s f.sp - BitVec.ofNat 64 (f.frameSize ns)) (f.frameSize ns) ⋆ G) →
    M.FallsTo condReads h k (f.prologue ns).1 (f.sp :: f.raRegs ++ f.scratch) [] (f.prologue ns).2 s
      (fun s' => M.getGpr s' f.sp = M.getGpr s f.sp - BitVec.ofNat 64 (f.frameSize ns) ∧
        (M.mem s' =⋆ Saved (M.getGpr s f.sp) ra ns ⋆
          region (M.getGpr s f.sp - BitVec.ofNat 64 (f.frameSize ns)) (8 * ns) ⋆ G)) post
  epilogue_spec : ∀ {h k ns s ra G post},
    spOk (M.getGpr s f.sp) → f.frameSize ns + f.raBytes ≤ 2 ^ 64 →
    (M.mem s =⋆ Saved (M.getGpr s f.sp + BitVec.ofNat 64 (f.frameSize ns)) ra ns ⋆ G) →
    M.FallsTo condReads h k (f.epilogue ns).1 (f.sp :: f.raRegs ++ f.scratch) [] (f.epilogue ns).2 s
      (fun s' => M.getGpr s' f.sp = M.getGpr s f.sp + BitVec.ofNat 64 (f.frameSize ns) ∧
        raReg s' ra ∧
        (M.mem s' =⋆ RetAddr (M.getGpr s f.sp + BitVec.ofNat 64 (f.frameSize ns)) ra ⋆
          region (M.getGpr s f.sp + BitVec.ofNat 64 (8 * ns))
            (f.frameSize ns - 8 * ns) ⋆ G)) post
  slotSt_spec : ∀ {h k i r s G post},
    r ∉ f.scratch → spOk (M.getGpr s f.sp) →
    (M.mem s =⋆ region (M.getGpr s f.sp + BitVec.ofNat 64 (8 * i)) 8 ⋆ G) →
    M.FallsTo condReads h k (f.slotSt i r) f.scratch [] FlagMask.none s
      (fun s' => M.mem s' =⋆
        cell64 (M.getGpr s f.sp + BitVec.ofNat 64 (8 * i)) (M.getGpr s r) ⋆ G) post
  slotLd_spec : ∀ {h k i rd v s G post},
    rd ∉ f.scratch → spOk (M.getGpr s f.sp) →
    (M.mem s =⋆ cell64 (M.getGpr s f.sp + BitVec.ofNat 64 (8 * i)) v ⋆ G) →
    M.FallsTo condReads h k (f.slotLd rd i) (rd :: f.scratch) [] FlagMask.none s
      (fun s' => M.getGpr s' rd = v ∧ M.mem s' = M.mem s) post
  canonAbi_spec : ∀ {h k t r v s post},
    (t = .bool ∨ ∃ n ∈ f.bitWidths, t = .bits n) → r ∉ f.scratch →
    GprHolds (M.getGpr s r) t v →
    M.FallsTo condReads h k (f.canonAbi t r).1 (r :: f.scratch) [] (f.canonAbi t r).2 s
      (fun s' => AbiGprHolds (M.getGpr s' r) t v ∧ M.mem s' = M.mem s) post
  call_spec : ∀ {h k sym s G post},
    (f.call sym).IsInfixAt (M.prog h) k →
    (M.mem s =⋆ region (M.getGpr s f.sp - BitVec.ofNat 64 f.raBytes) f.raBytes ⋆ G) →
    (∀ s', M.getGpr s' f.sp = M.getGpr s f.sp - BitVec.ofNat 64 f.raBytes →
      M.Frame condReads s s' (f.sp :: f.raRegs ++ f.scratch) [] FlagMask.all →
      raReg s' (M.addrOf h (k + (f.call sym).length)) →
      (M.mem s' =⋆
        RetAddr (M.getGpr s' f.sp) (M.addrOf h (k + (f.call sym).length)) ⋆ G) →
      Eventually (M.step h) post (M.mkState s' (M.labelAddr h sym))) →
    M.Run h k s post
  exitJmp_spec : ∀ {h k sym s post},
    (f.exitJmp sym).IsInfixAt (M.prog h) k →
    (∀ s', M.Frame condReads s s' f.scratch [] FlagMask.none → M.mem s' = M.mem s →
      Eventually (M.step h) post (M.mkState s' (M.labelAddr h sym))) →
    M.Run h k s post
  ret_spec : ∀ {h k s ra R post},
    f.ret.IsInfixAt (M.prog h) k → raReg s ra →
    (M.mem s =⋆ RetAddr (M.getGpr s f.sp) ra ⋆ R) →
    (∀ s', M.KeepsGpr s s' (f.sp :: f.scratch) → M.KeepsVec s s' [] →
      M.getGpr s' f.sp = M.getGpr s f.sp + BitVec.ofNat 64 f.raBytes →
      M.mem s' = M.mem s → Eventually (M.step h) post (M.mkState s' ra)) →
    M.Run h k s post

structure VecTarget {R V C D : Type} (M : Machine R V C D) (v : VecIsa R V C D)
    (condReads : C → FlagMask) (sp : R) (scratch : List R) (spOk : BitVec 64 → Prop) : Prop where
  vecScratch_disj : ∀ r ∈ v.vecScratch,
    r ∉ v.vecAllocatable ∧ r ∉ v.vecArgRegs ∧ r ∉ v.vecRetRegs
  vecArgRegs_nodup : v.vecArgRegs.Nodup
  vecRetRegs_nodup : v.vecRetRegs.Nodup
  abiVec_slot : ∀ t, v.isAbiVec t = true → (v.vecSlotWidth t).isSome = true
  vmov_spec : ∀ {h k w vd vs s post},
    M.FallsTo condReads h k (v.vmov w vd vs) [] [vd] FlagMask.none s
      (fun s' => (M.getVec s' vd).setWidth w.bits = (M.getVec s vs).setWidth w.bits ∧
        M.mem s' = M.mem s) post
  vmovi_spec : ∀ {h k w vd c code s post},
    v.vmovi w vd c = some code → vd ∉ v.vecScratch →
    M.FallsTo condReads h k code scratch (vd :: v.vecScratch) FlagMask.none s
      (fun s' => (M.getVec s' vd).setWidth w.bits = c.setWidth w.bits ∧ M.mem s' = M.mem s) post
  vslotSt_spec : ∀ {h k w i vr s G post},
    vr ∉ v.vecScratch → spOk (M.getGpr s sp) →
    (M.mem s =⋆ region (M.getGpr s sp + BitVec.ofNat 64 (8 * i)) (8 * w.slots) ⋆ G) →
    M.FallsTo condReads h k (v.vslotSt w i vr) scratch v.vecScratch FlagMask.none s
      (fun s' => M.mem s' =⋆
        array64 (M.getGpr s sp + BitVec.ofNat 64 (8 * i))
          (unpackSlotWords w (M.getVec s vr)) ⋆ G) post
  vslotLd_spec : ∀ {h k w i vd bv s G post},
    vd ∉ v.vecScratch → spOk (M.getGpr s sp) →
    (M.mem s =⋆
      array64 (M.getGpr s sp + BitVec.ofNat 64 (8 * i)) (unpackSlotWords w bv) ⋆ G) →
    M.FallsTo condReads h k (v.vslotLd w vd i) scratch (vd :: v.vecScratch) FlagMask.none s
      (fun s' => (M.getVec s' vd).setWidth w.bits = bv.setWidth w.bits ∧ M.mem s' = M.mem s) post
  vop_spec : ∀ {h k sig rs} {code : OpCode sig rs} {pas dsts vh c clob vs P s post},
    v.vop code pas dsts vh = some (c, clob) →
    (∀ r ∈ tupArgGprs pas, r ∉ scratch) → (∀ vr ∈ tupArgVecs pas, vr ∉ v.vecScratch) →
    (∀ r ∈ tupDstGprs dsts, r ∉ scratch) → (∀ vr ∈ tupDstVecs dsts, vr ∉ v.vecScratch) →
    TRel (M.PArgHolds s) pas vs → code.wp vs P →
    M.FallsTo condReads h k c (tupDstGprs dsts ++ scratch) (tupDstVecs dsts ++ v.vecScratch) clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (M.PDstHolds s') dsts rvs) ∧ M.mem s' = M.mem s) post
  vload_spec : ∀ {h k t vd a c clob val s post},
    v.vload t vd a = some (c, clob) → vd ∉ v.vecScratch → (∀ r ∈ a.regs, r ∉ scratch) →
    loadVal (M.mem s) t (a.eval (M.getGpr s)) = some val →
    M.FallsTo condReads h k c scratch (vd :: v.vecScratch) clob s
      (fun s' => VecHolds (M.getVec s' vd) t val ∧ M.mem s' = M.mem s) post
  vstore_spec : ∀ {h k t vs a c clob val s post},
    v.vstore t vs a = some (c, clob) → (∀ r ∈ a.regs, r ∉ scratch) →
    vs ∉ v.vecScratch → VecHolds (M.getVec s vs) t val →
    storeOk (M.mem s) t (a.eval (M.getGpr s)) →
    M.FallsTo condReads h k c scratch v.vecScratch clob s
      (fun s' => M.mem s' = storeMem (M.mem s) t (a.eval (M.getGpr s)) val) post

theorem VecTarget.empty {R C D : Type} (M : Machine R Empty C D) (condReads : C → FlagMask)
    (sp : R) (scratch : List R) (spOk : BitVec 64 → Prop) :
    VecTarget M (VecIsa.empty R C D) condReads sp scratch spOk where
  vecScratch_disj r := r.elim
  vecArgRegs_nodup := List.nodup_nil
  vecRetRegs_nodup := List.nodup_nil
  abiVec_slot _ h := nomatch h
  vmov_spec {_ _ _ vd} := vd.elim
  vmovi_spec {_ _ _ vd} := vd.elim
  vslotSt_spec {_ _ _ _ vr} := vr.elim
  vslotLd_spec {_ _ _ _ vd} := vd.elim
  vop_spec h := nomatch h
  vload_spec {_ _ _ vd} := vd.elim
  vstore_spec {_ _ _ vs} := vs.elim

structure Target extends Isa where
  mach : Machine Reg VReg Cond Directive
  gprSpec : GprTarget mach gpr frame.scratch
  frameSpec : FrameTarget mach frame gpr.condReads
  vecSpec : VecTarget mach vec gpr.condReads frame.sp frame.scratch frameSpec.spOk

namespace Target
variable (T : Target)

def LabelsUnique (h : T.mach.Host) : Prop :=
  ∀ (i j : Nat) l,
    (T.mach.prog h)[i]? = some (T.frame.label l) →
    (T.mach.prog h)[j]? = some (T.frame.label l) → i = j

def Defined (h : T.mach.Host) (l : Sym) : Prop :=
  ∃ k : Nat, (T.mach.prog h)[k]? = some (T.frame.label l)

def ArgsIn {as : List Ty} (args : Tup Val as) (s : T.mach.MData) : Prop :=
  ∃ locs, T.toIsa.assignArgs as = some locs ∧ TRel (T.mach.AbiHolds s) locs args

def RetsIn {bs : List Ty} (rets : Tup Val bs) (s : T.mach.MData) : Prop :=
  ∃ locs, T.toIsa.assignRets bs = some locs ∧ TRel (T.mach.AbiHolds s) locs rets

def Entry (sp : BitVec 64) (ra : T.mach.Addr) (n : Nat) : Mem 64 → Prop :=
  region (sp - BitVec.ofNat 64 n) n ⋆ T.frameSpec.RetAddr sp ra

def Exit (sp : BitVec 64) (n : Nat) : Mem 64 → Prop :=
  region (sp - BitVec.ofNat 64 n) (n + T.frame.raBytes)

def Restored (s s' : T.mach.MData) : Prop :=
  (∀ r ∈ T.frame.calleeSaved, T.mach.getGpr s' r = T.mach.getGpr s r) ∧
    T.mach.getGpr s' T.frame.sp = T.mach.getGpr s T.frame.sp + BitVec.ofNat 64 T.frame.raBytes

def FnSpec (h : T.mach.Host) (sym : Sym) {as bs : List Ty} (spec : Spec as bs) (n nX : Nat) :
    Prop :=
  ∀ (args : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost), spec args m Q X →
  ∀ (s : T.mach.MData) (ra : T.mach.Addr) (R : Mem 64 → Prop),
    T.ArgsIn args s → T.frameSpec.raReg s ra → T.frameSpec.spEntry (T.mach.getGpr s T.frame.sp) →
    (T.mach.mem s =⋆ Eq m ⋆ T.Entry (T.mach.getGpr s T.frame.sp) ra n ⋆ R) →
    Eventually (T.mach.step h)
      (fun st =>
        (T.mach.pc st = ra ∧
          ∃ (rets : Tup Val bs) (m' : Mem 64),
            Q rets m' ∧ T.RetsIn rets (T.mach.data st) ∧ T.Restored s (T.mach.data st) ∧
            (T.mach.mem (T.mach.data st) =⋆
              Eq m' ⋆ T.Exit (T.mach.getGpr s T.frame.sp) n ⋆ R)) ∨
        (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64),
          X sym' cs xs m' ∧ T.Defined h sym' ∧ T.mach.pc st = T.mach.labelAddr h sym' ∧
          T.ArgsIn xs (T.mach.data st) ∧
          T.frameSpec.spEntry (T.mach.getGpr (T.mach.data st) T.frame.sp) ∧
          ∃ (ra' : T.mach.Addr) (n' : Nat) (F : Mem 64 → Prop),
            nX ≤ n' ∧ n' + T.frame.raBytes ≤ 2 ^ 64 ∧ T.frameSpec.raReg (T.mach.data st) ra' ∧
            (T.mach.mem (T.mach.data st) =⋆
              Eq m' ⋆ T.Entry (T.mach.getGpr (T.mach.data st) T.frame.sp) ra' n' ⋆ F ⋆ R)))
      (T.mach.mkState s (T.mach.labelAddr h sym))
end Target

theorem core_bitcount_and_fp_gates (n : Nat) (f : Fmt)
    (u1 : Tup (Arg (fun _ => Unit)) [.bits n])
    (uf : Tup (Arg (fun _ => Unit)) [.float f, .float f]) :
    defaultSupportsScalarOp [8, 16, 32, 64] false false false (.clz n) u1 = false ∧
    defaultSupportsScalarOp [8, 16, 32, 64] false false false (.ctz n) u1 = false ∧
    defaultSupportsScalarOp [8, 16, 32, 64] false false false (.popcnt n) u1 = false ∧
    defaultSupportsScalarOp [32, 64] true false false (.clz 64) (.var (), ()) = true ∧
    defaultSupportsScalarOp [32, 64] true false false (.popcnt n) u1 = false ∧
    defaultSupportsScalarOp [8, 16, 32, 64] false false false (.fadd (.float f)) uf = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end LeanQbe.T
