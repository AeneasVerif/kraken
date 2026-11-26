module

public import LeanQbe.T.Target
public import LeanQbe.T.Vll.Arch
public import LeanQbe.T.Vll.Syntax
public import LeanQbe.T.Vll.Sem
import LeanQbe.T.TargetLemmas
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Logic.MemLemmas

/-!
# Pure First-Class `Instr A` Core Lowering & Soundness (`Vll.RegaInst0`)

Target-neutral core scalar lowering over `BedrockMach` L1 (`Instr A` / `vllMach A`), factored out
of `Vll.RegaInst` to keep both modules under `2,500` LOC and L4-firewall clean:

* `withWidth`, `vllSrcOfPArg`, `vllRegOfPArg`, `vllBoolRegOfPArg`.
* `vllCoreOp`, `vllCoreSupportsScalarOp`, `vllCoreLoad`, `vllCoreStore`.
* Soundness theorems (`vllCoreOp_spec`, `vllCoreLoad_spec`, `vllCoreLoad_zx_zext`,
  `vllCoreLoad_zx_zero32`, `vllCoreStore_spec`).
* Structural label-freedom (`NoVllLab`, `vllCoreOp_noLab`, `vllCoreLoad_noLab`,
  `vllCoreStore_noLab`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open LeanQbe.T

/-! ## 1. Pure First-Class `Instr A` Core Scalar Lowering -/

/-- Dispatch a natural bit width `n ∈ {8, 16, 32, 64}` to its architectural `Width`. -/
@[expose] def withWidth {α : Type} (n : Nat)
    (f : (w : Width) → n = w.bits → Option α) : Option α :=
  match n with
  | 8  => f .w8  rfl
  | 16 => f .w16 rfl
  | 32 => f .w32 rfl
  | 64 => f .w64 rfl
  | _  => none

/-- Convert a scalar bitvector `PArg` to a `Src A` right-hand operand. -/
@[expose] def vllSrcOfPArg {A : Arch} (w : Width) :
    PArg A.Reg A.VReg A.Cond (.bits w.bits) → Option (Src A)
  | .gpr r => some (.reg r)
  | .imm c => some (.imm (c.setWidth 64))
  | _ => none

/-- Materialize a scalar bitvector `PArg` into a GPR (using scratch `s0` for immediates). -/
@[expose] def vllRegOfPArg {A : Arch} (s0? : Option A.Reg) (w : Width) :
    PArg A.Reg A.VReg A.Cond (.bits w.bits) → Option (List (Instr A) × A.Reg)
  | .gpr r => some ([], r)
  | .imm c => s0?.map fun s0 => ([.movi s0 (c.setWidth 64)], s0)
  | _ => none

/-- Materialize a boolean `PArg` into a GPR (using scratch `s0` for immediates/flags). -/
@[expose] def vllBoolRegOfPArg {A : Arch} (s0? : Option A.Reg) :
    PArg A.Reg A.VReg A.Cond .bool → Option (List (Instr A) × A.Reg)
  | .gpr r => some ([], r)
  | .imm b => s0?.map fun s0 => ([.movi s0 (BitVec.ofNat 64 b.toNat)], s0)
  | .flag c => s0?.map fun s0 => ([.setcc s0 c], s0)
  | _ => none

/-- Lower a binary `CoreAlu` operation at concrete `Width` `w` into first-class `Instr A`. -/
@[expose] def vllCoreAlu (A : Arch) (op : CoreAlu) (w : Width)
    (pa pb : PArg A.Reg A.VReg A.Cond (.bits w.bits)) (rd : A.Reg) :
    Option (List (Instr A) × FlagMask) :=
  match vllRegOfPArg A.abi.scratch.head? w pa, vllSrcOfPArg w pb with
  | some (c1, ra), some sb => some (c1 ++ [.alu op w rd ra sb false], A.aluClob op false)
  | _, _ => none

/-- Lower a binary `CoreAlu` operation at bit width `n ∈ A.abi.bitWidths ∩ {8,16,32,64}`. -/
@[expose] def vllCoreBinBits (A : Arch) (op : CoreAlu) (n : Nat)
    (pa pb : PArg A.Reg A.VReg A.Cond (.bits n)) (rd : A.Reg) :
    Option (List (Instr A) × FlagMask) :=
  if A.abi.bitWidths.contains n then
    withWidth n fun w hw => vllCoreAlu A op w (hw ▸ pa) (hw ▸ pb) rd
  else none

/-- Lower a binary `CoreAlu` operation on `.bits n` into `.gpr rd`. -/
@[expose] def vllCoreBinTy (A : Arch) (op : CoreAlu) (t : Ty)
    (pa pb : PArg A.Reg A.VReg A.Cond t) (pd : PDst A.Reg A.VReg A.Cond t) :
    Option (List (Instr A) × FlagMask) :=
  match t, pd, pa, pb with
  | .bits n, .gpr rd, pa, pb => vllCoreBinBits A op n pa pb rd
  | _, _, _, _ => none

/-- Lower a commutative binary boolean logic operation (`.and`/`.or`/`.xor`) on `.bool`. -/
@[expose] def vllCoreBoolBin (A : Arch) (op : CoreAlu)
    (pa pb : PArg A.Reg A.VReg A.Cond .bool) (rd : A.Reg) :
    Option (List (Instr A) × FlagMask) :=
  let s0? := A.abi.scratch.head?
  match pb with
  | .gpr rb =>
    (vllBoolRegOfPArg s0? pa).map fun (c1, ra) =>
      (c1 ++ [.alu op .w8 rd ra (.reg rb) false], A.aluClob op false)
  | .imm b =>
    (vllBoolRegOfPArg s0? pa).map fun (c1, ra) =>
      (c1 ++ [.alu op .w8 rd ra (.imm (BitVec.ofNat 64 b.toNat)) false], A.aluClob op false)
  | .flag cb =>
    match pa, s0? with
    | .gpr ra, some s0 =>
      some ([.setcc s0 cb, .alu op .w8 rd ra (.reg s0) false], A.aluClob op false)
    | .imm a, some s0 =>
      some ([.setcc s0 cb, .alu op .w8 rd s0 (.imm (BitVec.ofNat 64 a.toNat)) false],
        A.aluClob op false)
    | .flag ca, some s0 =>
      some ([.setcc rd ca, .setcc s0 cb, .alu op .w8 rd rd (.reg s0) false], A.aluClob op false)
    | _, _ => none
  | .vec _ => none

/-- Lower `.and`/`.or`/`.xor` on either `.bool` or `.bits n`. -/
@[expose] def vllCoreBoolOrBits (A : Arch) (op : CoreAlu) (t : Ty)
    (pa pb : PArg A.Reg A.VReg A.Cond t) (pd : PDst A.Reg A.VReg A.Cond t) :
    Option (List (Instr A) × FlagMask) :=
  match t, pd, pa, pb with
  | .bool, .gpr rd, pa, pb => vllCoreBoolBin A op pa pb rd
  | .bits n, .gpr rd, pa, pb => vllCoreBinBits A op n pa pb rd
  | _, _, _, _ => none

/-- Lower `.copy (.bits w.bits)` into `.gpr rd`. -/
@[expose] def vllCoreCopyW (A : Arch) (w : Width)
    (pa : PArg A.Reg A.VReg A.Cond (.bits w.bits)) (rd : A.Reg) :
    Option (List (Instr A) × FlagMask) :=
  match pa with
  | .gpr r => some ([.mov w rd r], FlagMask.none)
  | .imm c => some ([.movi rd (c.setWidth 64)], FlagMask.none)
  | _ => none

/-- Lower `.copy t` into `.gpr rd`. -/
@[expose] def vllCoreCopy (A : Arch) (t : Ty)
    (pa : PArg A.Reg A.VReg A.Cond t) (pd : PDst A.Reg A.VReg A.Cond t) :
    Option (List (Instr A) × FlagMask) :=
  match t, pd, pa with
  | .bool, .gpr rd, .gpr r => some ([.mov .w8 rd r], FlagMask.none)
  | .bool, .gpr rd, .imm b => some ([.movi rd (BitVec.ofNat 64 b.toNat)], FlagMask.none)
  | .bool, .gpr rd, .flag c => some ([.setcc rd c], FlagMask.none)
  | .bits n, .gpr rd, pa =>
    if A.abi.bitWidths.contains n then withWidth n fun w hw => vllCoreCopyW A w (hw ▸ pa) rd
    else none
  | _, _, _ => none

/-- Lower `.neg (.bits w.bits)` as `0 - pa` into `.gpr rd`. -/
@[expose] def vllCoreNegW (A : Arch) (w : Width)
    (pa : PArg A.Reg A.VReg A.Cond (.bits w.bits)) (rd : A.Reg) :
    Option (List (Instr A) × FlagMask) :=
  match A.abi.scratch.head?, vllSrcOfPArg w pa with
  | some s0, some sb =>
    some ([.movi s0 0#64, .alu .sub w rd s0 sb false], A.aluClob .sub false)
  | _, _ => none

/-- Lower `.neg t` into `.gpr rd`. -/
@[expose] def vllCoreNeg (A : Arch) (t : Ty)
    (pa : PArg A.Reg A.VReg A.Cond t) (pd : PDst A.Reg A.VReg A.Cond t) :
    Option (List (Instr A) × FlagMask) :=
  match t, pd, pa with
  | .bits n, .gpr rd, pa =>
    if A.abi.bitWidths.contains n then withWidth n fun w hw => vllCoreNegW A w (hw ▸ pa) rd
    else none
  | _, _, _ => none

/-- Lower `.not (.bits w.bits)` as `pa ^^^ allOnes` into `.gpr rd`. -/
@[expose] def vllCoreNotW (A : Arch) (w : Width)
    (pa : PArg A.Reg A.VReg A.Cond (.bits w.bits)) (rd : A.Reg) :
    Option (List (Instr A) × FlagMask) :=
  (vllRegOfPArg A.abi.scratch.head? w pa).map fun (c1, ra) =>
    (c1 ++ [.alu .xor w rd ra (.imm (~~~0#64)) false], A.aluClob .xor false)

/-- Lower `.not t` on `.bool` or `.bits n` into `.gpr rd`. -/
@[expose] def vllCoreNot (A : Arch) (t : Ty)
    (pa : PArg A.Reg A.VReg A.Cond t) (pd : PDst A.Reg A.VReg A.Cond t) :
    Option (List (Instr A) × FlagMask) :=
  match t, pd, pa with
  | .bool, .gpr rd, pa =>
    (vllBoolRegOfPArg A.abi.scratch.head? pa).map fun (c1, ra) =>
      (c1 ++ [.alu .xor .w8 rd ra (.imm 1#64) false], A.aluClob .xor false)
  | .bits n, .gpr rd, pa =>
    if A.abi.bitWidths.contains n then withWidth n fun w hw => vllCoreNotW A w (hw ▸ pa) rd
    else none
  | _, _, _ => none

/-- Lower a scalar comparison `.cmp co (.bits w.bits)` to `.gpr rd` or `.flag cc`. -/
@[expose] def vllCoreCmpW (A : Arch) (condOfCmp? : CmpOp → Option A.Cond)
    (co : CmpOp) (w : Width) (pa pb : PArg A.Reg A.VReg A.Cond (.bits w.bits))
    (pd : PDst A.Reg A.VReg A.Cond .bool) : Option (List (Instr A) × FlagMask) :=
  match condOfCmp? co with
  | none => none
  | some cc =>
    match vllRegOfPArg A.abi.scratch.head? w pa, vllSrcOfPArg w pb with
    | some (c1, ra), some sb =>
      match pd with
      | .gpr rd => some (c1 ++ [.cmp w ra sb, .setcc rd cc], A.cmpClob)
      | .flag cf => if cf == cc then some (c1 ++ [.cmp w ra sb], A.cmpClob) else none
      | _ => none
    | _, _ => none

/-- Lower `.cmp co t m hm` for scalar `.bits n`. -/
@[expose] def vllCoreCmp (A : Arch) (condOfCmp? : CmpOp → Option A.Cond)
    (co : CmpOp) (t m : Ty) (hm : m = t.mask)
    (pa pb : PArg A.Reg A.VReg A.Cond t) (pd : PDst A.Reg A.VReg A.Cond m) :
    Option (List (Instr A) × FlagMask) :=
  match t, m, hm, pa, pb, pd with
  | .bits n, .bool, rfl, pa, pb, pd =>
    if A.abi.bitWidths.contains n then
      withWidth n fun w hw => vllCoreCmpW A condOfCmp? co w (hw ▸ pa) (hw ▸ pb) pd
    else none
  | _, _, _, _, _, _ => none

/-- Lower `.zext m n` (`m ≤ n`) into `.gpr rd`. -/
@[expose] def vllCoreZext (A : Arch) (m n : Nat)
    (pa : PArg A.Reg A.VReg A.Cond (.bits m)) (pd : PDst A.Reg A.VReg A.Cond (.bits n)) :
    Option (List (Instr A) × FlagMask) :=
  match pd with
  | .gpr rd =>
    if A.abi.bitWidths.contains m && A.abi.bitWidths.contains n &&
        (Width.ofBits? m).isSome && (Width.ofBits? n).isSome && Nat.ble m n then
      match pa with
      | .imm c => some ([.movi rd ((c.setWidth n).setWidth 64)], FlagMask.none)
      | .gpr r => some ([.mov .w64 rd r, .canonAbi (.bits m) rd], A.abi.canonAbiClob (.bits m))
      | _ => none
    else none
  | _ => none

/-- Lower `.sext m n` (`m ≤ n`) via `shl (n - m)` followed by `ashr (n - m)` at width `wn`. -/
@[expose] def vllCoreSextW (A : Arch) (m : Nat) (wn : Width)
    (pa : PArg A.Reg A.VReg A.Cond (.bits m)) (rd : A.Reg) :
    Option (List (Instr A) × FlagMask) :=
  if A.abi.bitWidths.contains m && A.abi.bitWidths.contains wn.bits &&
      Nat.ble 1 m && Nat.ble m wn.bits then
    match pa with
    | .imm c => some ([.movi rd ((c.signExtend wn.bits).setWidth 64)], FlagMask.none)
    | .gpr r =>
      let sh : BitVec 64 := BitVec.ofNat 64 (wn.bits - m)
      some ([.alu .shl wn rd r (.imm sh) false, .alu .ashr wn rd rd (.imm sh) false],
        A.aluClob .shl false ||| A.aluClob .ashr false)
    | _ => none
  else none

/-- Lower `.sext m n` into `.gpr rd`. -/
@[expose] def vllCoreSext (A : Arch) (m n : Nat)
    (pa : PArg A.Reg A.VReg A.Cond (.bits m)) (pd : PDst A.Reg A.VReg A.Cond (.bits n)) :
    Option (List (Instr A) × FlagMask) :=
  match pd with
  | .gpr rd =>
    if (Width.ofBits? m).isSome then withWidth n fun wn _ => vllCoreSextW A m wn pa rd
    else none
  | _ => none

/-- Lower `.trunc m n` (`n ≤ m`) into `.gpr rd` at destination width `wn`. -/
@[expose] def vllCoreTruncW (A : Arch) (m : Nat) (wn : Width)
    (pa : PArg A.Reg A.VReg A.Cond (.bits m)) (rd : A.Reg) :
    Option (List (Instr A) × FlagMask) :=
  if A.abi.bitWidths.contains m && A.abi.bitWidths.contains wn.bits && Nat.ble wn.bits m then
    match pa with
    | .imm c => some ([.movi rd ((c.setWidth wn.bits).setWidth 64)], FlagMask.none)
    | .gpr r => some ([.mov wn rd r], FlagMask.none)
    | _ => none
  else none

/-- Lower `.trunc m n` into `.gpr rd`. -/
@[expose] def vllCoreTrunc (A : Arch) (m n : Nat)
    (pa : PArg A.Reg A.VReg A.Cond (.bits m)) (pd : PDst A.Reg A.VReg A.Cond (.bits n)) :
    Option (List (Instr A) × FlagMask) :=
  match pd with
  | .gpr rd =>
    if (Width.ofBits? m).isSome then withWidth n fun wn _ => vllCoreTruncW A m wn pa rd
    else none
  | _ => none

/-- Lower `.ofBool n` into `.gpr rd`. -/
@[expose] def vllCoreOfBool (A : Arch) (n : Nat)
    (pa : PArg A.Reg A.VReg A.Cond .bool) (pd : PDst A.Reg A.VReg A.Cond (.bits n)) :
    Option (List (Instr A) × FlagMask) :=
  match pd with
  | .gpr rd =>
    if A.abi.bitWidths.contains n && (Width.ofBits? n).isSome then
      match pa with
      | .imm b => some ([.movi rd (BitVec.ofNat 64 b.toNat)], FlagMask.none)
      | .gpr r => some ([.mov .w64 rd r, .canonAbi .bool rd], A.abi.canonAbiClob .bool)
      | .flag c => some ([.setcc rd c, .canonAbi .bool rd], A.abi.canonAbiClob .bool)
      | _ => none
    else none
  | _ => none

/-- Lower `.bitcast (.bits m) (.bits n) h` into `.gpr rd`. -/
@[expose] def vllCoreBitcast (A : Arch) (t u : Ty) (h : t.size = u.size)
    (pa : PArg A.Reg A.VReg A.Cond t) (pd : PDst A.Reg A.VReg A.Cond u) :
    Option (List (Instr A) × FlagMask) :=
  match t, u, h, pd, pa with
  | .bits m, .bits _, _, .gpr rd, pa =>
    if A.abi.bitWidths.contains m then withWidth m fun w hw => vllCoreCopyW A w (hw ▸ pa) rd
    else none
  | _, _, _, _, _ => none

/-- Pure first-class `Instr A` lowering for core scalar `OpCode`s (flat single-level dispatch). -/
@[expose] def vllCoreOp (A : Arch) (condOfCmp? : CmpOp → Option A.Cond)
    {sig rs : List Ty} : (code : OpCode sig rs) →
    Tup (PArg A.Reg A.VReg A.Cond) sig →
    Tup (PDst A.Reg A.VReg A.Cond) rs → VariantHint →
    Option (List (Instr A) × FlagMask)
  | .copy t, (pa, ()), (pd, ()), _ => vllCoreCopy A t pa pd
  | .add t, (pa, pb, ()), (pd, ()), _ => vllCoreBinTy A .add t pa pb pd
  | .sub t, (pa, pb, ()), (pd, ()), _ => vllCoreBinTy A .sub t pa pb pd
  | .mul t, (pa, pb, ()), (pd, ()), _ => vllCoreBinTy A .mul t pa pb pd
  | .neg t, (pa, ()), (pd, ()), _ => vllCoreNeg A t pa pd
  | .and t, (pa, pb, ()), (pd, ()), _ => vllCoreBoolOrBits A .and t pa pb pd
  | .or t, (pa, pb, ()), (pd, ()), _ => vllCoreBoolOrBits A .or t pa pb pd
  | .xor t, (pa, pb, ()), (pd, ()), _ => vllCoreBoolOrBits A .xor t pa pb pd
  | .not t, (pa, ()), (pd, ()), _ => vllCoreNot A t pa pd
  | .shl t, (pa, pb, ()), (pd, ()), _ => vllCoreBinTy A .shl t pa pb pd
  | .lshr t, (pa, pb, ()), (pd, ()), _ => vllCoreBinTy A .lshr t pa pb pd
  | .ashr t, (pa, pb, ()), (pd, ()), _ => vllCoreBinTy A .ashr t pa pb pd
  | .cmp co t m hm, (pa, pb, ()), (pd, ()), _ => vllCoreCmp A condOfCmp? co t m hm pa pb pd
  | .zext m n, (pa, ()), (pd, ()), _ => vllCoreZext A m n pa pd
  | .sext m n, (pa, ()), (pd, ()), _ => vllCoreSext A m n pa pd
  | .trunc m n, (pa, ()), (pd, ()), _ => vllCoreTrunc A m n pa pd
  | .ofBool n, (pa, ()), (pd, ()), _ => vllCoreOfBool A n pa pd
  | .bitcast t u h, (pa, ()), (pd, ()), _ => vllCoreBitcast A t u h pa pd
  | _, _, _, _ => none

/-- Decidable opcode gate matching `vllCoreOp`. -/
@[expose] def vllCoreSupportsScalarOp (A : Arch) (condOfCmp? : CmpOp → Option A.Cond)
    {sig rs : List Ty} (code : OpCode sig rs)
    (_args : Tup (Arg (fun _ => Unit)) sig) : Bool :=
  let okW (n : Nat) : Bool := A.abi.bitWidths.contains n && (Width.ofBits? n).isSome
  let okTy : Ty → Bool | .bits n => okW n | _ => false
  let okBoolOrBits : Ty → Bool | .bool => true | .bits n => okW n | _ => false
  match code with
  | .copy t | .and t | .or t | .xor t | .not t => okBoolOrBits t
  | .add t | .sub t | .mul t | .neg t | .shl t | .lshr t | .ashr t => okTy t
  | .ofBool n => okW n
  | .cmp co t _ _ => okTy t && (condOfCmp? co).isSome
  | .zext m n | .sext m n => okW m && okW n && Nat.ble m n
  | .trunc m n => okW m && okW n && Nat.ble n m
  | .bitcast t u _ => okTy t && okTy u
  | _ => false

/-- Pure first-class `Instr A` scalar memory load (`LoadExt` defaults to `.zx`). -/
@[expose] def vllCoreLoad (A : Arch) (ext : LoadExt := .zx) (t : Ty) (rd : A.Reg)
    (a : AddrArg A.Reg) : Option (List (Instr A) × FlagMask) :=
  match t with
  | .bool => some ([.load .w8 ext rd a], FlagMask.none)
  | .bits n =>
    if A.abi.bitWidths.contains n then
      (Width.ofBits? n).map fun w => ([.load w ext rd a], FlagMask.none)
    else none
  | _ => none

/-- Lower a scalar memory store at concrete `Width` `w`. -/
@[expose] def vllCoreStoreW (A : Arch) (w : Width)
    (pa : PArg A.Reg A.VReg A.Cond (.bits w.bits)) (a : AddrArg A.Reg) :
    Option (List (Instr A) × FlagMask) :=
  match pa with
  | .gpr r => some ([.store w r a], FlagMask.none)
  | .imm c => A.abi.scratch.head?.map fun s0 => ([.movi s0 (c.setWidth 64), .store w s0 a],
      FlagMask.none)
  | _ => none

/-- Pure first-class `Instr A` scalar memory store. -/
@[expose] def vllCoreStore (A : Arch) (t : Ty) (pa : PArg A.Reg A.VReg A.Cond t)
    (a : AddrArg A.Reg) : Option (List (Instr A) × FlagMask) :=
  let s0? := A.abi.scratch.head?
  match t, pa with
  | .bool, .gpr r => some ([.store .w8 r a], FlagMask.none)
  | .bool, .imm b =>
    s0?.map fun s0 => ([.movi s0 (BitVec.ofNat 64 b.toNat), .store .w8 s0 a], FlagMask.none)
  | .bool, .flag c =>
    s0?.map fun s0 => ([.setcc s0 c, .store .w8 s0 a], FlagMask.none)
  | .bits n, pa =>
    if A.abi.bitWidths.contains n then withWidth n fun w hw => vllCoreStoreW A w (hw ▸ pa) a
    else none
  | _, _ => none

/-! ## 2. Correctness Proofs for Pure First-Class Core Lowering -/

private theorem keepsGpr_gpr {A : Arch} {s s' : MachSt A} {clob : List A.Reg}
    (h : (vllMach A).KeepsGpr s s' clob) {r : A.Reg} (hr : r ∉ clob) :
    s'.gpr r = s.gpr r := h r hr

private theorem mem_tupArgGprs_1 {R V C : Type} {t : Ty} {pa : PArg R V C t} {r : R}
    (h : r ∈ pa.gprs) : r ∈ tupArgGprs (ts := [t]) (pa, ()) :=
  List.mem_append_left _ h

private theorem mem_tupArgGprs_2l {R V C : Type} {t u : Ty} {pa : PArg R V C t}
    {pb : PArg R V C u} {r : R} (h : r ∈ pa.gprs) :
    r ∈ tupArgGprs (ts := [t, u]) (pa, pb, ()) :=
  List.mem_append_left _ h

private theorem mem_tupArgGprs_2r {R V C : Type} {t u : Ty} {pa : PArg R V C t}
    {pb : PArg R V C u} {r : R} (h : r ∈ pb.gprs) :
    r ∈ tupArgGprs (ts := [t, u]) (pa, pb, ()) :=
  List.mem_append_right _ (List.mem_append_left _ h)

private theorem mem_tupDstGprs_1 {R V C : Type} {t : Ty} {pd : PDst R V C t} {r : R}
    (h : r ∈ pd.gprs) : r ∈ tupDstGprs (ts := [t]) (pd, ()) :=
  List.mem_append_left _ h

private theorem withWidth_eq_some {α : Type} {n : Nat}
    {f : (w : Width) → n = w.bits → Option α} {x : α}
    (h : withWidth n f = some x) : ∃ (w : Width) (hw : n = w.bits), f w hw = some x := by
  unfold withWidth at h
  split at h
  · exact ⟨.w8, rfl, h⟩
  · exact ⟨.w16, rfl, h⟩
  · exact ⟨.w32, rfl, h⟩
  · exact ⟨.w64, rfl, h⟩
  · cases h

private theorem width_ofBits?_eq {n : Nat} {w : Width} (h : Width.ofBits? n = some w) :
    n = w.bits := by
  unfold Width.ofBits? at h; split at h <;> cases h <;> rfl

private theorem width_ofBits?_isSome_le_64 {n : Nat} (h : (Width.ofBits? n).isSome = true) :
    n ≤ 64 := by
  cases hw : Width.ofBits? n with
  | none => simp [hw] at h
  | some w => rw [width_ofBits?_eq hw]; exact w.bits_le_64

theorem flagMask_sub_refl (m : FlagMask) : m &&& ~~~m = 0#8 := BitVec.and_not_self m

theorem flagMask_none_sub (m : FlagMask) : FlagMask.none &&& ~~~m = 0#8 := by
  simp [FlagMask.none]

private theorem setWidth_setWidth_self {n : Nat} (hn : n ≤ 64) (v : BitVec n) :
    (v.setWidth 64).setWidth n = v := by
  rw [BitVec.setWidth_setWidth_of_le _ hn, BitVec.setWidth_eq]

private theorem ofNat64_setWidth_eq (n : Nat) (b : Bool) :
    (BitVec.ofNat 64 b.toNat).setWidth n = BitVec.ofNat n b.toNat := by
  apply BitVec.eq_of_toNat_eq
  have hb : b.toNat < 2 := by cases b <;> decide
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64)]

private theorem ofNat64_setWidth8_bool (b : Bool) :
    (BitVec.ofNat 64 b.toNat).setWidth 8 = BitVec.ofNat 8 b.toNat := by
  cases b <;> rfl

private theorem head?_mem {α : Type} {xs : List α} {x : α} (h : xs.head? = some x) : x ∈ xs := by
  cases xs with
  | nil => cases h
  | cons _ _ => cases h; exact List.mem_cons_self

theorem fallsTo_weaken_rd {A : Arch} {h : VllHost A} {k : Nat} {c : List (Instr A)}
    {rd : A.Reg} {clob : FlagMask} {s : MachSt A} {Q : MachSt A → Prop} {post : Config A → Prop}
    (ft : (vllMach A).FallsTo A.condReads h k c [rd] [] FlagMask.none s Q post) :
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s Q post :=
  Machine.FallsTo.weaken ft
    (fun _ hr => by simp only [List.mem_singleton] at hr; exact hr ▸ List.mem_cons_self)
    (fun _ h => nomatch h) (flagMask_none_sub _)

private theorem fallsTo_weaken_s0 {A : Arch} {h : VllHost A} {k : Nat} {c : List (Instr A)}
    {s0 : A.Reg} (hs0 : s0 ∈ A.abi.scratch) {s : MachSt A} {Q : MachSt A → Prop}
    {post : Config A → Prop}
    (ft : (vllMach A).FallsTo A.condReads h k c [s0] [] FlagMask.none s Q post) :
    (vllMach A).FallsTo A.condReads h k c A.abi.scratch [] FlagMask.none s Q post :=
  Machine.FallsTo.weaken ft
    (fun _ hr => by simp only [List.mem_singleton] at hr; exact hr ▸ hs0)
    (fun _ h => nomatch h) (flagMask_none_sub _)

private theorem fallsTo_weaken_app_rd {A : Arch} {h : VllHost A} {k : Nat} {c : List (Instr A)}
    {rd : A.Reg} {clob : FlagMask} {s : MachSt A} {Q : MachSt A → Prop} {post : Config A → Prop}
    (ft : (vllMach A).FallsTo A.condReads h k c (A.abi.scratch ++ [rd]) []
      (FlagMask.none ||| clob) s Q post) :
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s Q post :=
  Machine.FallsTo.weaken ft
    (fun _ hr => by
      rcases List.mem_append.mp hr with h1 | h2
      · exact List.mem_cons_of_mem rd h1
      · simp only [List.mem_singleton] at h2; subst h2; exact List.mem_cons_self)
    (fun _ h => nomatch h) (by simp [FlagMask.none])

private theorem fallsTo_weaken_rd_canon {A : Arch} {h : VllHost A} {k : Nat} {c : List (Instr A)}
    {rd : A.Reg} {clob : FlagMask} {s : MachSt A} {Q : MachSt A → Prop} {post : Config A → Prop}
    (ft : (vllMach A).FallsTo A.condReads h k c ([rd] ++ (rd :: A.abi.scratch)) []
      (FlagMask.none ||| clob) s Q post) :
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s Q post :=
  Machine.FallsTo.weaken ft
    (fun _ hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | hr'
      · exact List.mem_cons_self
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem rd hr')
    (fun _ h => nomatch h) (by simp [FlagMask.none])

private theorem wrap1 {A : Arch} {h : VllHost A} {k : Nat} {c : List (Instr A)} {clob : FlagMask}
    {s : MachSt A} {post : Config A → Prop} {t : Ty} {rd : A.Reg} {v : Val t}
    {P : Tup Val [t] → Prop} (hP : P (v, ()))
    (ft : (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => GprHolds (s'.gpr rd) t v ∧ s'.mem = s.mem) post) :
    (vllMach A).FallsTo A.condReads h k c
      (@tupDstGprs A.Reg A.VReg A.Cond [t] (.gpr rd, ()) ++ A.abi.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧
        TRel ((vllMach A).PDstHolds s') (as := [t]) (.gpr rd, ()) rvs) ∧
        s'.mem = s.mem) post :=
  Machine.FallsTo.conseq ft fun _ ⟨hg, hm⟩ _ => ⟨⟨(_, ()), hP, .cons hg .nil⟩, hm⟩

private theorem loadVal_bool_to_bits8 {m : Mem 64} {a : BitVec 64} {b : Bool}
    (h : loadVal m .bool a = some b) :
    loadVal m (.bits 8) a = some (BitVec.ofNat 8 b.toNat) := by
  unfold loadVal at h ⊢
  change (m.loadInt a 1).bind _ = some b at h
  change (m.loadInt a 1).bind _ = some (BitVec.ofNat 8 b.toNat)
  cases hl : m.loadInt a 1 with
  | none => simp [hl] at h
  | some i =>
    rw [hl] at h
    simp only [Option.bind_some] at h ⊢
    by_cases h01 : (i == 0 || i == 1) = true
    · simp only [h01, ↓reduceIte, Option.some.injEq] at h; subst h
      simp only [Bool.or_eq_true, beq_iff_eq] at h01
      rcases h01 with rfl | rfl <;> rfl
    · simp [h01] at h

private theorem storeMem_bool_eq_bits8 (m : Mem 64) (a : BitVec 64) (b : Bool) :
    storeMem m (.bits 8) a (BitVec.ofNat 8 b.toNat) = storeMem m .bool a b := by
  cases b <;> rfl

private theorem srcOfPArg_spec {A : Arch} {w : Width}
    {pa : PArg A.Reg A.VReg A.Cond (.bits w.bits)} {sb : Src A} {s : MachSt A} {v : BitVec w.bits}
    (hsrc : vllSrcOfPArg w pa = some sb)
    (hh : (vllMach A).PArgHolds s (.bits w.bits) pa v) : sb.evalW w s.gpr = v := by
  cases pa with
  | gpr _ => cases hsrc; exact hh.2
  | imm c =>
    cases hsrc
    have hEq : c = v := hh
    subst hEq
    exact setWidth_setWidth_self w.bits_le_64 c
  | vec _ => cases hsrc

private theorem srcOfPArg_regs_sub {A : Arch} {w : Width}
    {pb : PArg A.Reg A.VReg A.Cond (.bits w.bits)} {sb : Src A}
    (hsrc : vllSrcOfPArg w pb = some sb) : ∀ r ∈ sb.regs, r ∈ pb.gprs := by
  cases pb with
  | gpr _ => cases hsrc; intro _ hr; exact hr
  | imm _ => cases hsrc; intro _ hr; cases hr
  | vec _ => cases hsrc

private theorem src_evalW_frame {A : Arch} {w : Width} {sb : Src A} {s s' : MachSt A}
    {clob : List A.Reg} (hkeep : (vllMach A).KeepsGpr s s' clob)
    (hdisj : ∀ r ∈ sb.regs, r ∉ clob) : sb.evalW w s'.gpr = sb.evalW w s.gpr := by
  cases sb with
  | imm _ => rfl
  | reg r => dsimp only [Src.evalW, Src.eval]; rw [keepsGpr_gpr hkeep (hdisj r List.mem_cons_self)]

private theorem addrArg_eval_frame {A : Arch} {a : AddrArg A.Reg} {s s' : MachSt A}
    {clob : List A.Reg} (hkeep : (vllMach A).KeepsGpr s s' clob)
    (hdisj : ∀ r ∈ a.regs, r ∉ clob) : a.eval s'.gpr = a.eval s.gpr := by
  cases a with
  | imm _ => rfl
  | baseDisp b _ =>
    dsimp only [AddrArg.eval]; rw [keepsGpr_gpr hkeep (hdisj b List.mem_cons_self)]
  | baseIdxDisp b idx _ _ =>
    dsimp only [AddrArg.eval]
    rw [keepsGpr_gpr hkeep (hdisj b List.mem_cons_self),
      keepsGpr_gpr hkeep (hdisj idx (List.mem_cons_of_mem _ List.mem_cons_self))]

private theorem regOfPArg_spec {A : Arch} {w : Width}
    {pa : PArg A.Reg A.VReg A.Cond (.bits w.bits)} {c : List (Instr A)} {ra : A.Reg}
    {h : VllHost A} {k : Nat} {s : MachSt A} {v : BitVec w.bits} {post : Config A → Prop}
    (hreg : vllRegOfPArg A.abi.scratch.head? w pa = some (c, ra))
    (hh : (vllMach A).PArgHolds s (.bits w.bits) pa v) :
    (vllMach A).FallsTo A.condReads h k c A.abi.scratch [] FlagMask.none s
      (fun s' => (s'.gpr ra).setWidth w.bits = v ∧ s'.mem = s.mem) post := by
  cases pa with
  | gpr _ => cases hreg; exact Machine.FallsTo.nil ⟨hh.2, rfl⟩
  | imm cv =>
    cases hs0 : A.abi.scratch.head? with
    | none => simp [vllRegOfPArg, hs0] at hreg
    | some s0 =>
      simp only [vllRegOfPArg, hs0, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hreg
      rcases hreg with ⟨rfl, rfl⟩
      have hEq : cv = v := hh; subst hEq
      refine Machine.FallsTo.conseq (fallsTo_weaken_s0 (head?_mem hs0)
        (vllMach_movi_spec (A := A) (rd := s0) (imm := cv.setWidth 64))) ?_
      intro s' ⟨hg, hm⟩ _
      have hg' : s'.gpr s0 = cv.setWidth 64 := hg
      exact ⟨by rw [hg']; exact setWidth_setWidth_self w.bits_le_64 cv, hm⟩
  | vec _ => cases hreg

private theorem boolRegOfPArg_spec {A : Arch} (hwf : A.Wf)
    {pa : PArg A.Reg A.VReg A.Cond .bool} {c : List (Instr A)} {ra : A.Reg}
    {h : VllHost A} {k : Nat} {s : MachSt A} {b : Bool} {post : Config A → Prop}
    (hreg : vllBoolRegOfPArg A.abi.scratch.head? pa = some (c, ra))
    (hh : (vllMach A).PArgHolds s .bool pa b) :
    (vllMach A).FallsTo A.condReads h k c A.abi.scratch [] FlagMask.none s
      (fun s' => (s'.gpr ra).setWidth 8 = BitVec.ofNat 8 b.toNat ∧ s'.mem = s.mem) post := by
  cases pa with
  | gpr _ => cases hreg; exact Machine.FallsTo.nil ⟨hh, rfl⟩
  | imm bv =>
    cases hs0 : A.abi.scratch.head? with
    | none => simp [vllBoolRegOfPArg, hs0] at hreg
    | some s0 =>
      simp only [vllBoolRegOfPArg, hs0, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hreg
      rcases hreg with ⟨rfl, rfl⟩
      have hEq : bv = b := hh; subst hEq
      refine Machine.FallsTo.conseq (fallsTo_weaken_s0 (head?_mem hs0)
        (vllMach_movi_spec (A := A) (rd := s0) (imm := BitVec.ofNat 64 bv.toNat))) ?_
      intro s' ⟨hg, hm⟩ _
      have hg' : s'.gpr s0 = BitVec.ofNat 64 bv.toNat := hg
      exact ⟨by rw [hg']; exact ofNat64_setWidth8_bool bv, hm⟩
  | flag cf =>
    cases hs0 : A.abi.scratch.head? with
    | none => simp [vllBoolRegOfPArg, hs0] at hreg
    | some s0 =>
      simp only [vllBoolRegOfPArg, hs0, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hreg
      rcases hreg with ⟨rfl, rfl⟩
      refine Machine.FallsTo.conseq
        (fallsTo_weaken_s0 (head?_mem hs0) (vllMach_setcc_spec hwf (rd := s0) (c := cf))) ?_
      intro s' ⟨hg, hm⟩ _
      have hEq : (vllMach A).evalCond s cf = b := hh
      rw [hEq] at hg
      exact ⟨hg, hm⟩
  | vec _ => cases hreg

private theorem vllCoreAlu_spec {A : Arch} (hwf : A.Wf) {op : CoreAlu} {w : Width}
    {pa pb : PArg A.Reg A.VReg A.Cond (.bits w.bits)} {rd : A.Reg}
    {c : List (Instr A)} {clob : FlagMask} {va vb : BitVec w.bits}
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (halu : vllCoreAlu A op w pa pb rd = some (c, clob))
    (hpb_ns : ∀ r ∈ pb.gprs, r ∉ A.abi.scratch)
    (hha : (vllMach A).PArgHolds s (.bits w.bits) pa va)
    (hhb : (vllMach A).PArgHolds s (.bits w.bits) pb vb) :
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => GprHolds (s'.gpr rd) (.bits w.bits) (op.eval w va vb) ∧ s'.mem = s.mem) post := by
  unfold vllCoreAlu at halu
  cases hreg : vllRegOfPArg A.abi.scratch.head? w pa with
  | none => simp [hreg] at halu
  | some p1 =>
    rcases p1 with ⟨c1, ra⟩
    cases hsrc : vllSrcOfPArg w pb with
    | none => simp [hreg, hsrc] at halu
    | some sb =>
      simp only [hreg, hsrc, Option.some.injEq, Prod.mk.injEq] at halu
      rcases halu with ⟨rfl, rfl⟩
      refine fallsTo_weaken_app_rd
        (Machine.FallsTo.comp (regOfPArg_spec hreg hha) fun s1 ⟨hra, hm1⟩ hfr1 => ?_)
      have hsb1 : sb.evalW w s1.gpr = vb := by
        rw [src_evalW_frame hfr1.1 (fun r hr => hpb_ns r (srcOfPArg_regs_sub hsrc r hr))]
        exact srcOfPArg_spec hsrc hhb
      refine Machine.FallsTo.conseq
        (vllMach_alu_spec hwf (op := op) (w := w) (rd := rd) (lhs := ra) (rhs := sb)
          (sf := false)) ?_
      intro s2 ⟨_, hg2, _, hm2⟩ _
      rw [hra, hsb1] at hg2
      exact ⟨hg2, hm2.trans hm1⟩

private theorem vllCoreBinBits_spec {A : Arch} (hwf : A.Wf) {op : CoreAlu} {n : Nat}
    {pa pb : PArg A.Reg A.VReg A.Cond (.bits n)} {rd : A.Reg}
    {c : List (Instr A)} {clob : FlagMask} {va vb : BitVec n}
    {f : {k : Nat} → BitVec k → BitVec k → BitVec k}
    (hf : ∀ (w : Width) (x y : BitVec w.bits), op.eval w x y = f x y)
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (hbin : vllCoreBinBits A op n pa pb rd = some (c, clob))
    (hpb_ns : ∀ r ∈ pb.gprs, r ∉ A.abi.scratch)
    (hha : (vllMach A).PArgHolds s (.bits n) pa va)
    (hhb : (vllMach A).PArgHolds s (.bits n) pb vb) :
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => GprHolds (s'.gpr rd) (.bits n) (f va vb) ∧ s'.mem = s.mem) post := by
  unfold vllCoreBinBits at hbin
  split at hbin
  · obtain ⟨w, rfl, hw⟩ := withWidth_eq_some hbin
    simpa only [hf w] using vllCoreAlu_spec hwf hw hpb_ns hha hhb
  · cases hbin

private theorem vllCoreBinTy_spec {A : Arch} (hwf : A.Wf) {op : CoreAlu} {t : Ty}
    {pa pb : PArg A.Reg A.VReg A.Cond t} {pd : PDst A.Reg A.VReg A.Cond t}
    {c : List (Instr A)} {clob : FlagMask} {va vb : Val t} {P : Tup Val [t] → Prop}
    {f : {k : Nat} → BitVec k → BitVec k → BitVec k}
    (hf : ∀ (w : Width) (x y : BitVec w.bits), op.eval w x y = f x y)
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (hbin : vllCoreBinTy A op t pa pb pd = some (c, clob))
    (hpb_ns : ∀ r ∈ pb.gprs, r ∉ A.abi.scratch)
    (hha : (vllMach A).PArgHolds s t pa va) (hhb : (vllMach A).PArgHolds s t pb vb)
    (hP : match t, va, vb, P with | .bits _, va, vb, P => P (f va vb, ()) | _, _, _, _ => True) :
    (vllMach A).FallsTo A.condReads h k c
      (tupDstGprs (ts := [t]) (pd, ()) ++ A.abi.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧
        TRel ((vllMach A).PDstHolds s') (as := [t]) (pd, ()) rvs) ∧ s'.mem = s.mem) post := by
  cases t with
  | bits n =>
    cases pd with
    | gpr rd => exact wrap1 hP (vllCoreBinBits_spec hwf hf hbin hpb_ns hha hhb)
    | vec _ => cases hbin
  | bool | float _ | pair _ _ => cases hbin

private theorem vllCoreCopyW_spec {A : Arch} (hwf : A.Wf) {w : Width}
    {pa : PArg A.Reg A.VReg A.Cond (.bits w.bits)} {rd : A.Reg}
    {c : List (Instr A)} {clob : FlagMask} {va : BitVec w.bits}
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (hcp : vllCoreCopyW A w pa rd = some (c, clob))
    (hha : (vllMach A).PArgHolds s (.bits w.bits) pa va) :
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => GprHolds (s'.gpr rd) (.bits w.bits) va ∧ s'.mem = s.mem) post := by
  cases pa with
  | gpr r =>
    cases hcp
    refine Machine.FallsTo.conseq (fallsTo_weaken_rd (vllMach_movW_spec hwf (w := w) (rd := rd)
      (rs := r))) ?_
    intro s' ⟨_, hg, hm⟩ _
    have hha2 : (s.gpr r).setWidth w.bits = va := hha.2
    rw [hha2] at hg
    exact ⟨hg, hm⟩
  | imm cv =>
    cases hcp
    have hEq : cv = va := hha; subst hEq
    refine Machine.FallsTo.conseq
      (fallsTo_weaken_rd (vllMach_movi_spec (A := A) (rd := rd) (imm := cv.setWidth 64))) ?_
    intro s' ⟨hg, hm⟩ _
    have hg' : s'.gpr rd = cv.setWidth 64 := hg
    exact ⟨⟨w.bits_le_64, by rw [hg']; exact setWidth_setWidth_self w.bits_le_64 cv⟩, hm⟩
  | vec _ => cases hcp

private theorem vllCoreCopy_spec {A : Arch} (hwf : A.Wf) {t : Ty}
    {pa : PArg A.Reg A.VReg A.Cond t} {pd : PDst A.Reg A.VReg A.Cond t}
    {c : List (Instr A)} {clob : FlagMask} {va : Val t} {P : Tup Val [t] → Prop}
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (hcp : vllCoreCopy A t pa pd = some (c, clob))
    (hha : (vllMach A).PArgHolds s t pa va) (hP : P (va, ())) :
    (vllMach A).FallsTo A.condReads h k c
      (tupDstGprs (ts := [t]) (pd, ()) ++ A.abi.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧
        TRel ((vllMach A).PDstHolds s') (as := [t]) (pd, ()) rvs) ∧ s'.mem = s.mem) post := by
  cases t with
  | bool =>
    cases pd with
    | gpr rd =>
      cases pa with
      | gpr r =>
        cases hcp
        refine wrap1 hP (Machine.FallsTo.conseq
          (fallsTo_weaken_rd (vllMach_movW_spec hwf (w := .w8) (rd := rd) (rs := r))) ?_)
        intro s' ⟨_, hg, hm⟩ _
        have hha8 : (s.gpr r).setWidth 8 = BitVec.ofNat 8 va.toNat := hha
        have hg2 : (s'.gpr rd).setWidth 8 = (s.gpr r).setWidth 8 := hg.2
        exact ⟨hg2.trans hha8, hm⟩
      | imm bv =>
        cases hcp
        have hEq : bv = va := hha; subst hEq
        refine wrap1 hP (Machine.FallsTo.conseq (fallsTo_weaken_rd
          (vllMach_movi_spec (A := A) (rd := rd) (imm := BitVec.ofNat 64 bv.toNat))) ?_)
        intro s' ⟨hg, hm⟩ _
        have hg' : s'.gpr rd = BitVec.ofNat 64 bv.toNat := hg
        exact ⟨by rw [hg']; exact ofNat64_setWidth8_bool bv, hm⟩
      | flag cf =>
        cases hcp
        refine wrap1 hP (Machine.FallsTo.conseq
          (fallsTo_weaken_rd (vllMach_setcc_spec hwf (rd := rd) (c := cf))) ?_)
        intro s' ⟨hg, hm⟩ _
        have hEq : (vllMach A).evalCond s cf = va := hha
        rw [hEq] at hg
        exact ⟨hg, hm⟩
      | vec _ => cases hcp
    | vec _ | flag _ => cases hcp
  | bits n =>
    cases pd with
    | gpr rd =>
      dsimp only [vllCoreCopy] at hcp; split at hcp
      · obtain ⟨w, rfl, hw⟩ := withWidth_eq_some hcp
        exact wrap1 hP (vllCoreCopyW_spec hwf hw hha)
      · cases hcp
    | vec _ => cases hcp
  | float _ | pair _ _ => cases hcp

private theorem vllCoreNegW_spec {A : Arch} (hwf : A.Wf) {w : Width}
    {pa : PArg A.Reg A.VReg A.Cond (.bits w.bits)} {rd : A.Reg}
    {c : List (Instr A)} {clob : FlagMask} {va : BitVec w.bits}
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (hneg : vllCoreNegW A w pa rd = some (c, clob))
    (hpa_ns : ∀ r ∈ pa.gprs, r ∉ A.abi.scratch)
    (hha : (vllMach A).PArgHolds s (.bits w.bits) pa va) :
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => GprHolds (s'.gpr rd) (.bits w.bits) (-va) ∧ s'.mem = s.mem) post := by
  unfold vllCoreNegW at hneg
  cases hs0 : A.abi.scratch.head? with
  | none => simp [hs0] at hneg
  | some s0 =>
    cases hsrc : vllSrcOfPArg w pa with
    | none => simp [hs0, hsrc] at hneg
    | some sb =>
      simp only [hs0, hsrc, Option.some.injEq, Prod.mk.injEq] at hneg
      rcases hneg with ⟨rfl, rfl⟩
      refine fallsTo_weaken_app_rd (Machine.FallsTo.comp
        (fallsTo_weaken_s0 (head?_mem hs0) (vllMach_movi_spec (A := A) (rd := s0) (imm := 0#64)))
        fun s1 ⟨hs0_0, hm1⟩ hfr1 => ?_)
      have hsb1 : sb.evalW w s1.gpr = va := by
        rw [src_evalW_frame hfr1.1 (fun r hr => hpa_ns r (srcOfPArg_regs_sub hsrc r hr))]
        exact srcOfPArg_spec hsrc hha
      refine Machine.FallsTo.conseq
        (vllMach_alu_spec hwf (op := .sub) (w := w) (rd := rd) (lhs := s0) (rhs := sb)
          (sf := false)) ?_
      intro s2 ⟨_, hg2, _, hm2⟩ _
      have hs0_0' : s1.gpr s0 = 0#64 := hs0_0
      have hz : (s1.gpr s0).setWidth w.bits = 0#w.bits := by rw [hs0_0']; cases w <;> rfl
      have hev : CoreAlu.sub.eval w 0#w.bits va = -va := BitVec.zero_sub va
      rw [hz, hsb1, hev] at hg2
      exact ⟨hg2, hm2.trans hm1⟩

private theorem vllCoreNeg_spec {A : Arch} (hwf : A.Wf) {t : Ty}
    {pa : PArg A.Reg A.VReg A.Cond t} {pd : PDst A.Reg A.VReg A.Cond t}
    {c : List (Instr A)} {clob : FlagMask} {va : Val t} {P : Tup Val [t] → Prop}
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (hneg : vllCoreNeg A t pa pd = some (c, clob))
    (hpa_ns : ∀ r ∈ pa.gprs, r ∉ A.abi.scratch)
    (hha : (vllMach A).PArgHolds s t pa va)
    (hP : match t, va, P with | .bits _, va, P => P (-va, ()) | _, _, _ => True) :
    (vllMach A).FallsTo A.condReads h k c
      (tupDstGprs (ts := [t]) (pd, ()) ++ A.abi.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧
        TRel ((vllMach A).PDstHolds s') (as := [t]) (pd, ()) rvs) ∧ s'.mem = s.mem) post := by
  cases t with
  | bits n =>
    cases pd with
    | gpr rd =>
      dsimp only [vllCoreNeg] at hneg; split at hneg
      · obtain ⟨w, rfl, hw⟩ := withWidth_eq_some hneg
        exact wrap1 hP (vllCoreNegW_spec hwf hw hpa_ns hha)
      · cases hneg
    | vec _ => cases hneg
  | bool | float _ | pair _ _ => cases hneg

private theorem vllCoreNotW_spec {A : Arch} (hwf : A.Wf) {w : Width}
    {pa : PArg A.Reg A.VReg A.Cond (.bits w.bits)} {rd : A.Reg}
    {c : List (Instr A)} {clob : FlagMask} {va : BitVec w.bits}
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (hnot : vllCoreNotW A w pa rd = some (c, clob))
    (hha : (vllMach A).PArgHolds s (.bits w.bits) pa va) :
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => GprHolds (s'.gpr rd) (.bits w.bits) (~~~va) ∧ s'.mem = s.mem) post := by
  unfold vllCoreNotW at hnot
  cases hreg : vllRegOfPArg A.abi.scratch.head? w pa with
  | none => simp [hreg] at hnot
  | some p1 =>
    rcases p1 with ⟨c1, ra⟩
    simp only [hreg, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hnot
    rcases hnot with ⟨rfl, rfl⟩
    refine fallsTo_weaken_app_rd
      (Machine.FallsTo.comp (regOfPArg_spec hreg hha) fun s1 ⟨hra, hm1⟩ _ => ?_)
    refine Machine.FallsTo.conseq (vllMach_alu_spec hwf (op := .xor) (w := w) (rd := rd)
      (lhs := ra) (rhs := .imm (~~~0#64)) (sf := false)) ?_
    intro s2 ⟨_, hg2, _, hm2⟩ _
    have hall : (Src.imm (A := A) (~~~0#64)).evalW w s1.gpr = ~~~0#w.bits := by
      dsimp only [Src.evalW, Src.eval]; cases w <;> rfl
    have hxor : CoreAlu.xor.eval w va (~~~0#w.bits) = ~~~va := by
      dsimp only [CoreAlu.eval]; apply BitVec.eq_of_getElem_eq; intro i _; simp
    rw [hra, hall, hxor] at hg2
    exact ⟨hg2, hm2.trans hm1⟩

private theorem vllCoreNot_spec {A : Arch} (hwf : A.Wf) {t : Ty}
    {pa : PArg A.Reg A.VReg A.Cond t} {pd : PDst A.Reg A.VReg A.Cond t}
    {c : List (Instr A)} {clob : FlagMask} {va : Val t} {P : Tup Val [t] → Prop}
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (hnot : vllCoreNot A t pa pd = some (c, clob))
    (hha : (vllMach A).PArgHolds s t pa va)
    (hP : P (lift1 (~~~ ·) (! ·) t va, ())) :
    (vllMach A).FallsTo A.condReads h k c
      (tupDstGprs (ts := [t]) (pd, ()) ++ A.abi.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧
        TRel ((vllMach A).PDstHolds s') (as := [t]) (pd, ()) rvs) ∧ s'.mem = s.mem) post := by
  cases t with
  | bool =>
    cases pd with
    | gpr rd =>
      dsimp only [vllCoreNot] at hnot
      cases hreg : vllBoolRegOfPArg A.abi.scratch.head? pa with
      | none => simp [hreg] at hnot
      | some p1 =>
        rcases p1 with ⟨c1, ra⟩
        simp only [hreg, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hnot
        rcases hnot with ⟨rfl, rfl⟩
        refine wrap1 hP (fallsTo_weaken_app_rd
          (Machine.FallsTo.comp (boolRegOfPArg_spec hwf hreg hha) fun s1 ⟨hra, hm1⟩ _ => ?_))
        refine Machine.FallsTo.conseq (vllMach_alu_spec hwf (op := .xor) (w := .w8) (rd := rd)
          (lhs := ra) (rhs := .imm 1#64) (sf := false)) ?_
        intro s2 ⟨_, hg2, _, hm2⟩ _
        have hnotb : CoreAlu.xor.eval .w8 (BitVec.ofNat 8 va.toNat) 1#8 =
            BitVec.ofNat 8 (!va).toNat := by cases va <;> rfl
        have hrhs : (Src.imm (A := A) 1#64).evalW .w8 s1.gpr = 1#8 := rfl
        have hg2' : (s2.gpr rd).setWidth 8 = BitVec.ofNat 8 (!va).toNat := by
          have h2 := hg2.2
          rw [hra, hrhs, hnotb] at h2
          exact h2
        exact ⟨hg2', hm2.trans hm1⟩
    | vec _ | flag _ => cases hnot
  | bits n =>
    cases pd with
    | gpr rd =>
      dsimp only [vllCoreNot] at hnot; split at hnot
      · obtain ⟨w, rfl, hw⟩ := withWidth_eq_some hnot
        exact wrap1 hP (vllCoreNotW_spec hwf hw hha)
      · cases hnot
    | vec _ => cases hnot
  | float _ | pair _ _ => cases hnot

private theorem boolAlu_eval_eq (a b : Bool) :
    (CoreAlu.eval .and .w8 (BitVec.ofNat 8 a.toNat) (BitVec.ofNat 8 b.toNat) =
      BitVec.ofNat 8 (a && b).toNat) ∧
    (CoreAlu.eval .or .w8 (BitVec.ofNat 8 a.toNat) (BitVec.ofNat 8 b.toNat) =
      BitVec.ofNat 8 (a || b).toNat) ∧
    (CoreAlu.eval .xor .w8 (BitVec.ofNat 8 a.toNat) (BitVec.ofNat 8 b.toNat) =
      BitVec.ofNat 8 (a ^^ b).toNat) := by
  cases a <;> cases b <;> decide

private theorem vllCoreBoolBin_spec {A : Arch} (hwf : A.Wf) {op : CoreAlu}
    {f : Bool → Bool → Bool}
    (hop : ∀ a b : Bool,
      op.eval .w8 (BitVec.ofNat 8 a.toNat) (BitVec.ofNat 8 b.toNat) =
        BitVec.ofNat 8 (f a b).toNat)
    (hcomm : ∀ a b : Bool, f a b = f b a)
    {pa pb : PArg A.Reg A.VReg A.Cond .bool} {rd : A.Reg}
    {c : List (Instr A)} {clob : FlagMask} {a b : Bool}
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (hbin : vllCoreBoolBin A op pa pb rd = some (c, clob))
    (hpa_ns : ∀ r ∈ pa.gprs, r ∉ A.abi.scratch)
    (hpb_ns : ∀ r ∈ pb.gprs, r ∉ A.abi.scratch) (hrd_ns : rd ∉ A.abi.scratch)
    (hha : (vllMach A).PArgHolds s .bool pa a) (hhb : (vllMach A).PArgHolds s .bool pb b) :
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => GprHolds (s'.gpr rd) .bool (f a b) ∧ s'.mem = s.mem) post := by
  unfold vllCoreBoolBin at hbin
  cases pb with
  | vec _ => cases hbin
  | gpr rb =>
    cases hreg : vllBoolRegOfPArg A.abi.scratch.head? pa with
    | none => simp [hreg] at hbin
    | some p1 =>
      rcases p1 with ⟨c1, ra⟩
      simp only [hreg, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hbin
      rcases hbin with ⟨rfl, rfl⟩
      refine fallsTo_weaken_app_rd
        (Machine.FallsTo.comp (boolRegOfPArg_spec hwf hreg hha) fun s1 ⟨hra, hm1⟩ hfr1 => ?_)
      have hrb : (s1.gpr rb).setWidth 8 = BitVec.ofNat 8 b.toNat := by
        rw [keepsGpr_gpr hfr1.1 (hpb_ns rb List.mem_cons_self)]; exact hhb
      refine Machine.FallsTo.conseq (vllMach_alu_spec hwf (op := op) (w := .w8) (rd := rd)
        (lhs := ra) (rhs := .reg rb) (sf := false)) ?_
      intro s2 ⟨_, hg2, _, hm2⟩ _
      have h2 : (s2.gpr rd).setWidth 8 = BitVec.ofNat 8 (f a b).toNat := by
        have h' := hg2.2
        dsimp only [Src.evalW, Src.eval] at h'
        rw [hra, hrb, hop a b] at h'; exact h'
      exact ⟨h2, hm2.trans hm1⟩
  | imm bv =>
    have hEq : bv = b := hhb; subst hEq
    cases hreg : vllBoolRegOfPArg A.abi.scratch.head? pa with
    | none => simp [hreg] at hbin
    | some p1 =>
      rcases p1 with ⟨c1, ra⟩
      simp only [hreg, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hbin
      rcases hbin with ⟨rfl, rfl⟩
      refine fallsTo_weaken_app_rd
        (Machine.FallsTo.comp (boolRegOfPArg_spec hwf hreg hha) fun s1 ⟨hra, hm1⟩ _ => ?_)
      refine Machine.FallsTo.conseq (vllMach_alu_spec hwf (op := op) (w := .w8) (rd := rd)
        (lhs := ra) (rhs := .imm (BitVec.ofNat 64 bv.toNat)) (sf := false)) ?_
      intro s2 ⟨_, hg2, _, hm2⟩ _
      have h2 : (s2.gpr rd).setWidth 8 = BitVec.ofNat 8 (f a bv).toNat := by
        have h' := hg2.2
        dsimp only [Src.evalW, Src.eval] at h'
        rw [hra, ofNat64_setWidth8_bool bv, hop a bv] at h'; exact h'
      exact ⟨h2, hm2.trans hm1⟩
  | flag cb =>
    have hcb : A.evalCond s.flags cb = b := hhb
    cases hs0 : A.abi.scratch.head? with
    | none => cases pa <;> simp [hs0] at hbin
    | some s0 =>
      have hs0_mem : s0 ∈ A.abi.scratch := head?_mem hs0
      cases pa with
      | vec _ => simp at hbin
      | gpr ra =>
        simp only [hs0, Option.some.injEq, Prod.mk.injEq] at hbin; rcases hbin with ⟨rfl, rfl⟩
        refine fallsTo_weaken_app_rd (Machine.FallsTo.comp
          (fallsTo_weaken_s0 hs0_mem (vllMach_setcc_spec hwf (rd := s0) (c := cb)))
          fun s1 ⟨hs0_b, hm1⟩ hfr1 => ?_)
        have hra : (s1.gpr ra).setWidth 8 = BitVec.ofNat 8 a.toNat := by
          rw [keepsGpr_gpr hfr1.1 (hpa_ns ra List.mem_cons_self)]; exact hha
        have hs0' : (s1.gpr s0).setWidth 8 = BitVec.ofNat 8 b.toNat := by
          have h' : (s1.gpr s0).setWidth 8 = BitVec.ofNat 8 (A.evalCond s.flags cb).toNat := hs0_b
          rwa [hcb] at h'
        refine Machine.FallsTo.conseq (vllMach_alu_spec hwf (op := op) (w := .w8) (rd := rd)
          (lhs := ra) (rhs := .reg s0) (sf := false)) ?_
        intro s2 ⟨_, hg2, _, hm2⟩ _
        have h2 : (s2.gpr rd).setWidth 8 = BitVec.ofNat 8 (f a b).toNat := by
          have h' := hg2.2
          dsimp only [Src.evalW, Src.eval] at h'
          rw [hra, hs0', hop a b] at h'; exact h'
        exact ⟨h2, hm2.trans hm1⟩
      | imm av =>
        have hEq : av = a := hha; subst hEq
        simp only [hs0, Option.some.injEq, Prod.mk.injEq] at hbin; rcases hbin with ⟨rfl, rfl⟩
        refine fallsTo_weaken_app_rd (Machine.FallsTo.comp
          (fallsTo_weaken_s0 hs0_mem (vllMach_setcc_spec hwf (rd := s0) (c := cb)))
          fun s1 ⟨hs0_b, hm1⟩ _ => ?_)
        have hs0' : (s1.gpr s0).setWidth 8 = BitVec.ofNat 8 b.toNat := by
          have h' : (s1.gpr s0).setWidth 8 = BitVec.ofNat 8 (A.evalCond s.flags cb).toNat := hs0_b
          rwa [hcb] at h'
        refine Machine.FallsTo.conseq (vllMach_alu_spec hwf (op := op) (w := .w8) (rd := rd)
          (lhs := s0) (rhs := .imm (BitVec.ofNat 64 av.toNat)) (sf := false)) ?_
        intro s2 ⟨_, hg2, _, hm2⟩ _
        have heq' : op.eval .w8 (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 av.toNat) =
            BitVec.ofNat 8 (f av b).toNat := by rw [hop b av, hcomm b av]
        have h2 : (s2.gpr rd).setWidth 8 = BitVec.ofNat 8 (f av b).toNat := by
          have h' := hg2.2
          dsimp only [Src.evalW, Src.eval] at h'
          rw [hs0', ofNat64_setWidth8_bool av, heq'] at h'; exact h'
        exact ⟨h2, hm2.trans hm1⟩
      | flag ca =>
        have hca : A.evalCond s.flags ca = a := hha
        simp only [hs0, Option.some.injEq, Prod.mk.injEq] at hbin; rcases hbin with ⟨rfl, rfl⟩
        have hrd_ne_s0 : rd ≠ s0 := fun e => hrd_ns (e ▸ hs0_mem)
        have h1 := vllMach_setcc_spec hwf (rd := rd) (c := ca)
          (h := h) (k := k) (s := s) (post := post)
        have h23 :
            (vllMach A).FallsTo A.condReads h k
              ([.setcc rd ca] ++ ([.setcc s0 cb] ++ [.alu op .w8 rd rd (.reg s0) false]))
              ([rd] ++ ([s0] ++ [rd])) ([] ++ ([] ++ []))
              (FlagMask.none ||| (FlagMask.none ||| A.aluClob op false)) s
              (fun s' => GprHolds (s'.gpr rd) .bool (f a b) ∧ s'.mem = s.mem) post := by
          refine Machine.FallsTo.comp h1 fun s1 ⟨hrd1, hm1⟩ hfr1 => ?_
          have hcb1 : A.evalCond s1.flags cb = b :=
            (hfr1.2.2 cb (FlagMask.disjoint_none _)).trans hcb
          have h2 := vllMach_setcc_spec hwf (rd := s0) (c := cb)
            (h := h) (k := k + 1) (s := s1) (post := post)
          refine Machine.FallsTo.comp h2 fun s2 ⟨hs0_2, hm2⟩ hfr2 => ?_
          have hrd1' : (s1.gpr rd).setWidth 8 = BitVec.ofNat 8 a.toNat := by
            have h' : (s1.gpr rd).setWidth 8 = BitVec.ofNat 8 (A.evalCond s.flags ca).toNat := hrd1
            rwa [hca] at h'
          have hrd2 : (s2.gpr rd).setWidth 8 = BitVec.ofNat 8 a.toNat := by
            rw [keepsGpr_gpr hfr2.1 (by simp [hrd_ne_s0])]; exact hrd1'
          have hs0' : (s2.gpr s0).setWidth 8 = BitVec.ofNat 8 b.toNat := by
            have h' : (s2.gpr s0).setWidth 8 =
                BitVec.ofNat 8 (A.evalCond s1.flags cb).toNat := hs0_2
            rwa [hcb1] at h'
          refine Machine.FallsTo.conseq (vllMach_alu_spec hwf (op := op) (w := .w8) (rd := rd)
            (lhs := rd) (rhs := .reg s0) (sf := false)) ?_
          intro s3 ⟨_, hg3, _, hm3⟩ _
          have h3 : (s3.gpr rd).setWidth 8 = BitVec.ofNat 8 (f a b).toNat := by
            have h' := hg3.2
            dsimp only [Src.evalW, Src.eval] at h'
            rw [hrd2, hs0', hop a b] at h'; exact h'
          exact ⟨h3, hm3.trans (hm2.trans hm1)⟩
        refine Machine.FallsTo.weaken h23 ?_ (fun _ h => nomatch h) (by simp [FlagMask.none])
        intro r hr; simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem rd hs0_mem
        · exact List.mem_cons_self

private theorem vllCoreBoolOrBits_spec {A : Arch} (hwf : A.Wf) {op : CoreAlu} {t : Ty}
    {fb : {k : Nat} → BitVec k → BitVec k → BitVec k} {fg : Bool → Bool → Bool}
    (hfb : ∀ (w : Width) (x y : BitVec w.bits), op.eval w x y = fb x y)
    (hfg : ∀ a b : Bool,
      op.eval .w8 (BitVec.ofNat 8 a.toNat) (BitVec.ofNat 8 b.toNat) =
        BitVec.ofNat 8 (fg a b).toNat)
    (hcomm : ∀ a b : Bool, fg a b = fg b a)
    {pa pb : PArg A.Reg A.VReg A.Cond t} {pd : PDst A.Reg A.VReg A.Cond t}
    {c : List (Instr A)} {clob : FlagMask} {va vb : Val t} {P : Tup Val [t] → Prop}
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (hbin : vllCoreBoolOrBits A op t pa pb pd = some (c, clob))
    (hpa_ns : ∀ r ∈ pa.gprs, r ∉ A.abi.scratch) (hpb_ns : ∀ r ∈ pb.gprs, r ∉ A.abi.scratch)
    (hpd_ns : ∀ r ∈ pd.gprs, r ∉ A.abi.scratch)
    (hha : (vllMach A).PArgHolds s t pa va) (hhb : (vllMach A).PArgHolds s t pb vb)
    (hP : P (lift2 fb fg t va vb, ())) :
    (vllMach A).FallsTo A.condReads h k c
      (tupDstGprs (ts := [t]) (pd, ()) ++ A.abi.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧
        TRel ((vllMach A).PDstHolds s') (as := [t]) (pd, ()) rvs) ∧ s'.mem = s.mem) post := by
  cases t with
  | bool =>
    cases pd with
    | gpr rd =>
      exact wrap1 hP (vllCoreBoolBin_spec hwf hfg hcomm hbin hpa_ns hpb_ns
        (hpd_ns rd List.mem_cons_self) hha hhb)
    | vec _ | flag _ => cases hbin
  | bits n =>
    cases pd with
    | gpr rd => exact wrap1 hP (vllCoreBinBits_spec hwf hfb hbin hpb_ns hha hhb)
    | vec _ => cases hbin
  | float _ | pair _ _ => cases hbin

private theorem vllCoreCmpW_spec {A : Arch} (hwf : A.Wf) (condOfCmp? : CmpOp → Option A.Cond)
    (hcmp : ∀ co cc (w : Width) (a b : BitVec w.bits) f,
      condOfCmp? co = some cc → A.evalCond (A.cmpFlags w a b f) cc = co.evalBits a b)
    {co : CmpOp} {w : Width} {pa pb : PArg A.Reg A.VReg A.Cond (.bits w.bits)}
    {pd : PDst A.Reg A.VReg A.Cond .bool} {c : List (Instr A)} {clob : FlagMask}
    {va vb : BitVec w.bits} {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (hc : vllCoreCmpW A condOfCmp? co w pa pb pd = some (c, clob))
    (hpb_ns : ∀ r ∈ pb.gprs, r ∉ A.abi.scratch)
    (hha : (vllMach A).PArgHolds s (.bits w.bits) pa va)
    (hhb : (vllMach A).PArgHolds s (.bits w.bits) pb vb) :
    (vllMach A).FallsTo A.condReads h k c (pd.gprs ++ A.abi.scratch) [] clob s
      (fun s' => (vllMach A).PDstHolds s' .bool pd (co.evalBits va vb) ∧ s'.mem = s.mem) post := by
  unfold vllCoreCmpW at hc
  cases hcc : condOfCmp? co with
  | none => simp [hcc] at hc
  | some cc =>
    simp only [hcc] at hc
    cases hreg : vllRegOfPArg A.abi.scratch.head? w pa with
    | none => simp [hreg] at hc
    | some p1 =>
      rcases p1 with ⟨c1, ra⟩
      cases hsrc : vllSrcOfPArg w pb with
      | none => simp [hreg, hsrc] at hc
      | some sb =>
        simp only [hreg, hsrc] at hc
        cases pd with
        | vec _ => cases hc
        | gpr rd =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
          refine fallsTo_weaken_app_rd
            (Machine.FallsTo.comp (regOfPArg_spec hreg hha) fun s1 ⟨hra, hm1⟩ hfr1 => ?_)
          have hsb1 : sb.evalW w s1.gpr = vb := by
            rw [src_evalW_frame hfr1.1 (fun r hr => hpb_ns r (srcOfPArg_regs_sub hsrc r hr))]
            exact srcOfPArg_spec hsrc hhb
          have h23 :
              (vllMach A).FallsTo A.condReads h (k + c1.length)
                ([.cmp w ra sb] ++ [.setcc rd cc]) ([] ++ [rd]) ([] ++ [])
                (A.cmpClob ||| FlagMask.none) s1
                (fun s' => (vllMach A).PDstHolds s' .bool (.gpr rd) (co.evalBits va vb) ∧
                  s'.mem = s.mem) post := by
            refine Machine.FallsTo.comp
              (vllMach_cmp_spec hwf (w := w) (lhs := ra) (rhs := sb)) fun s2 ⟨hf2, hm2⟩ _ => ?_
            refine Machine.FallsTo.conseq (vllMach_setcc_spec hwf (rd := rd) (c := cc)) ?_
            intro s3 ⟨hg3, hm3⟩ _
            have hev : (vllMach A).evalCond s2 cc = co.evalBits va vb := by
              show A.evalCond s2.flags cc = co.evalBits va vb
              rw [hf2, hra, hsb1]; exact hcmp co cc w va vb s1.flags hcc
            rw [hev] at hg3
            exact ⟨hg3, hm3.trans (hm2.trans hm1)⟩
          exact Machine.FallsTo.weaken h23 (fun _ hr => by simpa using hr)
            (fun _ h => nomatch h) (by simp [FlagMask.none])
        | flag cf =>
          by_cases hcf : (cf == cc) = true
          · simp only [hcf, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
            rcases hc with ⟨rfl, rfl⟩; obtain rfl := beq_iff_eq.mp hcf
            have hcomp :
                (vllMach A).FallsTo A.condReads h k (c1 ++ [.cmp w ra sb])
                  (A.abi.scratch ++ []) ([] ++ []) (FlagMask.none ||| A.cmpClob) s
                  (fun s' => (vllMach A).PDstHolds s' .bool (.flag cf) (co.evalBits va vb) ∧
                    s'.mem = s.mem) post := by
              refine Machine.FallsTo.comp (regOfPArg_spec hreg hha) fun s1 ⟨hra, hm1⟩ hfr1 => ?_
              have hsb1 : sb.evalW w s1.gpr = vb := by
                rw [src_evalW_frame hfr1.1 (fun r hr => hpb_ns r (srcOfPArg_regs_sub hsrc r hr))]
                exact srcOfPArg_spec hsrc hhb
              refine Machine.FallsTo.conseq
                (vllMach_cmp_spec hwf (w := w) (lhs := ra) (rhs := sb)) ?_
              intro s2 ⟨hf2, hm2⟩ _
              exact ⟨by show A.evalCond s2.flags cf = co.evalBits va vb
                        rw [hf2, hra, hsb1]; exact hcmp co cf w va vb s1.flags hcc,
                hm2.trans hm1⟩
            exact Machine.FallsTo.weaken hcomp
              (fun _ hr => by simpa [PDst.gprs] using hr) (fun _ h => nomatch h)
              (by simp [FlagMask.none])
          · simp [hcf] at hc

private theorem vllCoreCmp_spec {A : Arch} (hwf : A.Wf) (condOfCmp? : CmpOp → Option A.Cond)
    (hcmp : ∀ co cc (w : Width) (a b : BitVec w.bits) f,
      condOfCmp? co = some cc → A.evalCond (A.cmpFlags w a b f) cc = co.evalBits a b)
    {co : CmpOp} {t m : Ty} {hm : m = t.mask}
    {pa pb : PArg A.Reg A.VReg A.Cond t} {pd : PDst A.Reg A.VReg A.Cond m}
    {c : List (Instr A)} {clob : FlagMask} {va vb : Val t} {P : Tup Val [m] → Prop}
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (hc : vllCoreCmp A condOfCmp? co t m hm pa pb pd = some (c, clob))
    (hpb_ns : ∀ r ∈ pb.gprs, r ∉ A.abi.scratch)
    (hha : (vllMach A).PArgHolds s t pa va) (hhb : (vllMach A).PArgHolds s t pb vb)
    (hwp : (OpCode.cmp co t m hm).wp (va, vb, ()) P) :
    (vllMach A).FallsTo A.condReads h k c
      (tupDstGprs (ts := [m]) (pd, ()) ++ A.abi.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧
        TRel ((vllMach A).PDstHolds s') (as := [m]) (pd, ()) rvs) ∧ s'.mem = s.mem) post := by
  subst hm
  cases t with
  | bits n =>
    dsimp only [vllCoreCmp] at hc; split at hc
    · obtain ⟨w, rfl, hw⟩ := withWidth_eq_some hc
      simp only [tupDstGprs, tupFlatMap, List.append_nil]
      refine Machine.FallsTo.conseq
        (vllCoreCmpW_spec hwf condOfCmp? hcmp hw hpb_ns hha hhb) ?_
      intro _ ⟨hg, hm'⟩ _; exact ⟨⟨(_, ()), hwp, .cons hg .nil⟩, hm'⟩
    · cases hc
  | bool | float _ | pair _ _ => cases hc

private theorem sext_shl_ashr {m n : Nat} (hm : 1 ≤ m) (hmn : m ≤ n) (hn : n ≤ 64)
    (x : BitVec 64) (v : BitVec m) (hv : x.setWidth m = v) :
    ((x.setWidth n) <<< (n - m)).sshiftRight (n - m) = v.signExtend n := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  rw [BitVec.getElem_sshiftRight, BitVec.getElem_signExtend]
  by_cases him : i < m
  · have hlt : n - m + i < n := by omega
    have hge : ¬(n - m + i < n - m) := by omega
    have hsub : n - m + i - (n - m) = i := by omega
    have hi64 : i < 64 := by omega
    have hvi : x[i] = v[i] := by
      have := congrArg (fun bv : BitVec m => bv[i]) hv
      simpa [BitVec.getElem_setWidth, hi64] using this
    simp [hlt, him, BitVec.getElem_shiftLeft, hge, hsub, BitVec.getElem_setWidth, hi64, hvi]
  · have hnlt : ¬(n - m + i < n) := by omega
    have hmsb : ((x.setWidth n) <<< (n - m)).msb = v.msb := by
      rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last]
      have hge : ¬(n - 1 < n - m) := by omega
      have hsub : n - 1 - (n - m) = m - 1 := by omega
      have hm_lt : m - 1 < m := by omega
      have hxm : x.getLsbD (m - 1) = v.getLsbD (m - 1) := by
        have := congrArg (fun bv : BitVec m => bv.getLsbD (m - 1)) hv
        simpa [BitVec.getLsbD_setWidth, hm_lt] using this
      simp [hge, hsub, hxm, show n - 1 < n by omega]
    simp [hnlt, him, hmsb]

private theorem vllCoreZext_spec {A : Arch} (hwf : A.Wf) {m n : Nat}
    {pa : PArg A.Reg A.VReg A.Cond (.bits m)} {pd : PDst A.Reg A.VReg A.Cond (.bits n)}
    {c : List (Instr A)} {clob : FlagMask} {va : BitVec m} {P : Tup Val [.bits n] → Prop}
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (hz : vllCoreZext A m n pa pd = some (c, clob))
    (hha : (vllMach A).PArgHolds s (.bits m) pa va) (hP : P (va.setWidth n, ())) :
    (vllMach A).FallsTo A.condReads h k c
      (tupDstGprs (ts := [.bits n]) (pd, ()) ++ A.abi.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧
        TRel ((vllMach A).PDstHolds s') (as := [.bits n]) (pd, ()) rvs) ∧ s'.mem = s.mem) post := by
  cases pd with
  | vec _ => cases hz
  | gpr rd =>
    dsimp only [vllCoreZext] at hz; split at hz
    · rename_i hcond
      simp only [Bool.and_eq_true, Nat.ble_eq] at hcond
      have hm_in : m ∈ A.abi.bitWidths := List.contains_iff_mem.mp hcond.1.1.1.1
      have hn64 : n ≤ 64 := width_ofBits?_isSome_le_64 hcond.1.2
      cases pa with
      | vec _ => cases hz
      | imm cv =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hz; rcases hz with ⟨rfl, rfl⟩
        have hEq : cv = va := hha; subst hEq
        refine wrap1 hP (Machine.FallsTo.conseq (fallsTo_weaken_rd
          (vllMach_movi_spec (A := A) (rd := rd) (imm := (cv.setWidth n).setWidth 64))) ?_)
        intro s' ⟨hg, hm⟩ _
        have hg' : s'.gpr rd = (cv.setWidth n).setWidth 64 := hg
        exact ⟨⟨hn64, by rw [hg']; exact setWidth_setWidth_self hn64 _⟩, hm⟩
      | gpr r =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hz; rcases hz with ⟨rfl, rfl⟩
        refine wrap1 hP (fallsTo_weaken_rd_canon (Machine.FallsTo.comp
          (vllMach_mov_spec hwf (rd := rd) (rs := r)) fun s1 ⟨hg1, hm1⟩ _ => ?_))
        have hh1 : GprHolds (s1.gpr rd) (.bits m) va := by
          show GprHolds ((vllMach A).getGpr s1 rd) (.bits m) va; rw [hg1]; exact hha
        refine Machine.FallsTo.conseq
          (vllMach_canonAbi_spec hwf (t := .bits m) (r := rd) (v := va)
            (Or.inr ⟨m, hm_in, rfl⟩) hh1) ?_
        intro s2 ⟨habi, hm2⟩ _
        exact ⟨⟨hn64, by rw [habi.2, BitVec.setWidth_setWidth_of_le _ hn64]⟩, hm2.trans hm1⟩
    · cases hz

private theorem vllCoreSextW_spec {A : Arch} (hwf : A.Wf) {m : Nat} {wn : Width}
    {pa : PArg A.Reg A.VReg A.Cond (.bits m)} {rd : A.Reg}
    {c : List (Instr A)} {clob : FlagMask} {va : BitVec m}
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (hsext : vllCoreSextW A m wn pa rd = some (c, clob))
    (hha : (vllMach A).PArgHolds s (.bits m) pa va) :
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => GprHolds (s'.gpr rd) (.bits wn.bits) (va.signExtend wn.bits) ∧
        s'.mem = s.mem) post := by
  unfold vllCoreSextW at hsext; split at hsext
  · rename_i hcond
    simp only [Bool.and_eq_true, Nat.ble_eq] at hcond
    have hm1 : 1 ≤ m := hcond.1.2; have hmn : m ≤ wn.bits := hcond.2
    cases pa with
    | vec _ => cases hsext
    | imm cv =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsext; rcases hsext with ⟨rfl, rfl⟩
      have hEq : cv = va := hha; subst hEq
      refine Machine.FallsTo.conseq (fallsTo_weaken_rd
        (vllMach_movi_spec (A := A) (rd := rd) (imm := (cv.signExtend wn.bits).setWidth 64))) ?_
      intro s' ⟨hg, hm⟩ _
      have hg' : s'.gpr rd = (cv.signExtend wn.bits).setWidth 64 := hg
      exact ⟨⟨wn.bits_le_64, by rw [hg']; exact setWidth_setWidth_self wn.bits_le_64 _⟩, hm⟩
    | gpr r =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsext; rcases hsext with ⟨rfl, rfl⟩
      have hsh_mod : ∀ g,
          ((Src.imm (A := A) (BitVec.ofNat 64 (wn.bits - m))).evalW wn g).toNat % wn.bits =
            wn.bits - m := fun _ => by
        dsimp only [Src.evalW, Src.eval]
        have hlt1 : wn.bits - m < wn.bits := by omega
        have hlt2 : wn.bits - m < 2 ^ wn.bits := Nat.lt_trans hlt1 Nat.lt_two_pow_self
        have hlt64 : wn.bits - m < 2 ^ 64 :=
          Nat.lt_of_lt_of_le hlt2 (Nat.pow_le_pow_right (by decide) wn.bits_le_64)
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64,
          Nat.mod_eq_of_lt hlt2, Nat.mod_eq_of_lt hlt1]
      have hcomp :
          (vllMach A).FallsTo A.condReads h k
            ([.alu .shl wn rd r (.imm (BitVec.ofNat 64 (wn.bits - m))) false] ++
              [.alu .ashr wn rd rd (.imm (BitVec.ofNat 64 (wn.bits - m))) false])
            ([rd] ++ [rd]) ([] ++ [])
            (A.aluClob .shl false ||| A.aluClob .ashr false) s
            (fun s' => GprHolds (s'.gpr rd) (.bits wn.bits) (va.signExtend wn.bits) ∧
              s'.mem = s.mem) post := by
        refine Machine.FallsTo.comp (vllMach_alu_spec hwf (op := .shl) (w := wn) (rd := rd)
          (lhs := r) (rhs := .imm (BitVec.ofNat 64 (wn.bits - m))) (sf := false))
          fun s1 ⟨_, hg1, _, hm1'⟩ _ => ?_
        refine Machine.FallsTo.conseq (vllMach_alu_spec hwf (op := .ashr) (w := wn) (rd := rd)
          (lhs := rd) (rhs := .imm (BitVec.ofNat 64 (wn.bits - m))) (sf := false)) ?_
        intro s2 ⟨_, hg2, _, hm2'⟩ _
        have hstep1 : (s1.gpr rd).setWidth wn.bits =
            ((s.gpr r).setWidth wn.bits) <<< (wn.bits - m) := by
          have h1 := hg1.2
          dsimp only [CoreAlu.eval] at h1
          rw [hsh_mod] at h1; exact h1
        have hres : CoreAlu.ashr.eval wn ((s1.gpr rd).setWidth wn.bits)
            ((Src.imm (A := A) (BitVec.ofNat 64 (wn.bits - m))).evalW wn s1.gpr) =
            va.signExtend wn.bits := by
          dsimp only [CoreAlu.eval]; rw [hstep1, hsh_mod]
          exact sext_shl_ashr hm1 hmn wn.bits_le_64 (s.gpr r) va hha.2
        rw [hres] at hg2
        exact ⟨hg2, hm2'.trans hm1'⟩
      refine Machine.FallsTo.weaken hcomp ?_ (fun _ h => nomatch h) (flagMask_sub_refl _)
      intro _ hq; simp only [List.mem_append, List.mem_singleton] at hq
      rcases hq with rfl | rfl <;> exact List.mem_cons_self
  · cases hsext

private theorem vllCoreSext_spec {A : Arch} (hwf : A.Wf) {m n : Nat}
    {pa : PArg A.Reg A.VReg A.Cond (.bits m)} {pd : PDst A.Reg A.VReg A.Cond (.bits n)}
    {c : List (Instr A)} {clob : FlagMask} {va : BitVec m} {P : Tup Val [.bits n] → Prop}
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (hsext : vllCoreSext A m n pa pd = some (c, clob))
    (hha : (vllMach A).PArgHolds s (.bits m) pa va) (hP : P (va.signExtend n, ())) :
    (vllMach A).FallsTo A.condReads h k c
      (tupDstGprs (ts := [.bits n]) (pd, ()) ++ A.abi.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧
        TRel ((vllMach A).PDstHolds s') (as := [.bits n]) (pd, ()) rvs) ∧ s'.mem = s.mem) post := by
  cases pd with
  | vec _ => cases hsext
  | gpr rd =>
    dsimp only [vllCoreSext] at hsext; split at hsext
    · obtain ⟨wn, rfl, hw⟩ := withWidth_eq_some hsext
      exact wrap1 hP (vllCoreSextW_spec hwf hw hha)
    · cases hsext

private theorem vllCoreTruncW_spec {A : Arch} (hwf : A.Wf) {m : Nat} {wn : Width}
    {pa : PArg A.Reg A.VReg A.Cond (.bits m)} {rd : A.Reg}
    {c : List (Instr A)} {clob : FlagMask} {va : BitVec m}
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (htrunc : vllCoreTruncW A m wn pa rd = some (c, clob))
    (hha : (vllMach A).PArgHolds s (.bits m) pa va) :
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => GprHolds (s'.gpr rd) (.bits wn.bits) (va.setWidth wn.bits) ∧
        s'.mem = s.mem) post := by
  unfold vllCoreTruncW at htrunc; split at htrunc
  · rename_i hcond
    simp only [Bool.and_eq_true, Nat.ble_eq] at hcond
    have hnm : wn.bits ≤ m := hcond.2
    cases pa with
    | vec _ => cases htrunc
    | imm cv =>
      simp only [Option.some.injEq, Prod.mk.injEq] at htrunc; rcases htrunc with ⟨rfl, rfl⟩
      have hEq : cv = va := hha; subst hEq
      refine Machine.FallsTo.conseq (fallsTo_weaken_rd
        (vllMach_movi_spec (A := A) (rd := rd) (imm := (cv.setWidth wn.bits).setWidth 64))) ?_
      intro s' ⟨hg, hm⟩ _
      have hg' : s'.gpr rd = (cv.setWidth wn.bits).setWidth 64 := hg
      exact ⟨⟨wn.bits_le_64, by rw [hg']; exact setWidth_setWidth_self wn.bits_le_64 _⟩, hm⟩
    | gpr r =>
      simp only [Option.some.injEq, Prod.mk.injEq] at htrunc; rcases htrunc with ⟨rfl, rfl⟩
      refine Machine.FallsTo.conseq
        (fallsTo_weaken_rd (vllMach_movW_spec hwf (w := wn) (rd := rd) (rs := r))) ?_
      intro s' ⟨_, hg, hm⟩ _
      have hha2 : (s.gpr r).setWidth m = va := hha.2
      have heq : (s.gpr r).setWidth wn.bits = va.setWidth wn.bits := by
        rw [← hha2, BitVec.setWidth_setWidth_of_le _ hnm]
      rw [heq] at hg
      exact ⟨hg, hm⟩
  · cases htrunc

private theorem vllCoreTrunc_spec {A : Arch} (hwf : A.Wf) {m n : Nat}
    {pa : PArg A.Reg A.VReg A.Cond (.bits m)} {pd : PDst A.Reg A.VReg A.Cond (.bits n)}
    {c : List (Instr A)} {clob : FlagMask} {va : BitVec m} {P : Tup Val [.bits n] → Prop}
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (htrunc : vllCoreTrunc A m n pa pd = some (c, clob))
    (hha : (vllMach A).PArgHolds s (.bits m) pa va) (hP : P (va.setWidth n, ())) :
    (vllMach A).FallsTo A.condReads h k c
      (tupDstGprs (ts := [.bits n]) (pd, ()) ++ A.abi.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧
        TRel ((vllMach A).PDstHolds s') (as := [.bits n]) (pd, ()) rvs) ∧ s'.mem = s.mem) post := by
  cases pd with
  | vec _ => cases htrunc
  | gpr rd =>
    dsimp only [vllCoreTrunc] at htrunc; split at htrunc
    · obtain ⟨wn, rfl, hw⟩ := withWidth_eq_some htrunc
      exact wrap1 hP (vllCoreTruncW_spec hwf hw hha)
    · cases htrunc

private theorem vllCoreOfBool_spec {A : Arch} (hwf : A.Wf) {n : Nat}
    {pa : PArg A.Reg A.VReg A.Cond .bool} {pd : PDst A.Reg A.VReg A.Cond (.bits n)}
    {c : List (Instr A)} {clob : FlagMask} {va : Bool} {P : Tup Val [.bits n] → Prop}
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (hob : vllCoreOfBool A n pa pd = some (c, clob))
    (hha : (vllMach A).PArgHolds s .bool pa va) (hP : P (BitVec.ofNat n va.toNat, ())) :
    (vllMach A).FallsTo A.condReads h k c
      (tupDstGprs (ts := [.bits n]) (pd, ()) ++ A.abi.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧
        TRel ((vllMach A).PDstHolds s') (as := [.bits n]) (pd, ()) rvs) ∧ s'.mem = s.mem) post := by
  cases pd with
  | vec _ => cases hob
  | gpr rd =>
    dsimp only [vllCoreOfBool] at hob; split at hob
    · rename_i hcond
      simp only [Bool.and_eq_true] at hcond
      have hn64 : n ≤ 64 := width_ofBits?_isSome_le_64 hcond.2
      cases pa with
      | vec _ => cases hob
      | imm bv =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hob; rcases hob with ⟨rfl, rfl⟩
        have hEq : bv = va := hha; subst hEq
        refine wrap1 hP (Machine.FallsTo.conseq (fallsTo_weaken_rd
          (vllMach_movi_spec (A := A) (rd := rd) (imm := BitVec.ofNat 64 bv.toNat))) ?_)
        intro s' ⟨hg, hm⟩ _
        have hg' : s'.gpr rd = BitVec.ofNat 64 bv.toNat := hg
        exact ⟨⟨hn64, by rw [hg']; exact ofNat64_setWidth_eq n bv⟩, hm⟩
      | gpr r =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hob; rcases hob with ⟨rfl, rfl⟩
        refine wrap1 hP (fallsTo_weaken_rd_canon (Machine.FallsTo.comp
          (vllMach_mov_spec hwf (rd := rd) (rs := r)) fun s1 ⟨hg1, hm1⟩ _ => ?_))
        have hh1 : GprHolds (s1.gpr rd) .bool va := by
          show GprHolds ((vllMach A).getGpr s1 rd) .bool va; rw [hg1]; exact hha
        refine Machine.FallsTo.conseq
          (vllMach_canonAbi_spec hwf (t := .bool) (r := rd) (v := va) (Or.inl rfl) hh1) ?_
        intro s2 ⟨habi, hm2⟩ _
        exact ⟨⟨hn64, by rw [habi]; exact ofNat64_setWidth_eq n va⟩, hm2.trans hm1⟩
      | flag cf =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hob; rcases hob with ⟨rfl, rfl⟩
        refine wrap1 hP (fallsTo_weaken_rd_canon (Machine.FallsTo.comp
          (vllMach_setcc_spec hwf (rd := rd) (c := cf)) fun s1 ⟨hg1, hm1⟩ _ => ?_))
        have hEq : (vllMach A).evalCond s cf = va := hha
        have hh1 : GprHolds (s1.gpr rd) .bool va := by rw [hEq] at hg1; exact hg1
        refine Machine.FallsTo.conseq
          (vllMach_canonAbi_spec hwf (t := .bool) (r := rd) (v := va) (Or.inl rfl) hh1) ?_
        intro s2 ⟨habi, hm2⟩ _
        exact ⟨⟨hn64, by rw [habi]; exact ofNat64_setWidth_eq n va⟩, hm2.trans hm1⟩
    · cases hob

private theorem vllCoreBitcast_spec {A : Arch} (hwf : A.Wf) {t u : Ty} {htu : t.size = u.size}
    {pa : PArg A.Reg A.VReg A.Cond t} {pd : PDst A.Reg A.VReg A.Cond u}
    {c : List (Instr A)} {clob : FlagMask} {va : Val t} {P : Tup Val [u] → Prop}
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (hbc : vllCoreBitcast A t u htu pa pd = some (c, clob))
    (hha : (vllMach A).PArgHolds s t pa va)
    (hwp : (OpCode.bitcast t u htu).wp (va, ()) P) :
    (vllMach A).FallsTo A.condReads h k c
      (tupDstGprs (ts := [u]) (pd, ()) ++ A.abi.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧
        TRel ((vllMach A).PDstHolds s') (as := [u]) (pd, ()) rvs) ∧ s'.mem = s.mem) post := by
  cases t with
  | bits m =>
    cases u with
    | bits n =>
      cases pd with
      | gpr rd =>
        have hmn : m = n := htu
        subst hmn
        have hP : P (va, ()) := by simpa [OpCode.wp, toBits, ofBits] using hwp
        dsimp only [vllCoreBitcast] at hbc; split at hbc
        · obtain ⟨w, rfl, hw⟩ := withWidth_eq_some hbc
          exact wrap1 hP (vllCoreCopyW_spec hwf hw hha)
        · cases hbc
      | vec _ => cases hbc
    | bool | float _ | pair _ _ => cases hbc
  | bool | float _ | pair _ _ => cases hbc

/-- Soundness of pure first-class `vllCoreOp` against `OpCode.wp` on `vllMach A`. -/
theorem vllCoreOp_spec (A : Arch) (hwf : A.Wf) (condOfCmp? : CmpOp → Option A.Cond)
    (hcmp : ∀ co cc (w : Width) (a b : BitVec w.bits) f,
      condOfCmp? co = some cc → A.evalCond (A.cmpFlags w a b f) cc = co.evalBits a b)
    {h : VllHost A} {k : Nat} {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg A.Reg A.VReg A.Cond) sig} {dsts : Tup (PDst A.Reg A.VReg A.Cond) rs}
    {vh : VariantHint} {c : List (Instr A)} {clob : FlagMask}
    {vs : Tup Val sig} {P : Tup Val rs → Prop} {s : MachSt A} {post : Config A → Prop}
    (hop : vllCoreOp A condOfCmp? code pas dsts vh = some (c, clob))
    (hargs_ns : ∀ r ∈ tupArgGprs pas, r ∉ A.abi.scratch)
    (hdsts_ns : ∀ r ∈ tupDstGprs dsts, r ∉ A.abi.scratch)
    (hrel : TRel ((vllMach A).PArgHolds s) pas vs) (hwp : code.wp vs P) :
    (vllMach A).FallsTo A.condReads h k c (tupDstGprs dsts ++ A.abi.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel ((vllMach A).PDstHolds s') dsts rvs) ∧
        s'.mem = s.mem) post := by
  cases code with
  | copy t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    rcases hrel with _ | ⟨hha, _⟩
    exact vllCoreCopy_spec hwf hop hha hwp
  | add t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    rcases hrel with _ | ⟨hha, _ | ⟨hhb, _⟩⟩
    exact vllCoreBinTy_spec hwf (f := (· + ·)) (fun _ _ _ => rfl) hop
      (fun _ hr => hargs_ns _ (mem_tupArgGprs_2r hr)) hha hhb
      (by cases t <;> first | exact hwp | trivial)
  | sub t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    rcases hrel with _ | ⟨hha, _ | ⟨hhb, _⟩⟩
    exact vllCoreBinTy_spec hwf (f := (· - ·)) (fun _ _ _ => rfl) hop
      (fun _ hr => hargs_ns _ (mem_tupArgGprs_2r hr)) hha hhb
      (by cases t <;> first | exact hwp | trivial)
  | mul t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    rcases hrel with _ | ⟨hha, _ | ⟨hhb, _⟩⟩
    exact vllCoreBinTy_spec hwf (f := (· * ·)) (fun _ _ _ => rfl) hop
      (fun _ hr => hargs_ns _ (mem_tupArgGprs_2r hr)) hha hhb
      (by cases t <;> first | exact hwp | trivial)
  | neg t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    rcases hrel with _ | ⟨hha, _⟩
    exact vllCoreNeg_spec hwf hop (fun _ hr => hargs_ns _ (mem_tupArgGprs_1 hr)) hha
      (by cases t <;> first | exact hwp | trivial)
  | and t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    rcases hrel with _ | ⟨hha, _ | ⟨hhb, _⟩⟩
    exact vllCoreBoolOrBits_spec hwf (fun _ _ _ => rfl) (fun a b => (boolAlu_eval_eq a b).1)
      Bool.and_comm hop (fun _ hr => hargs_ns _ (mem_tupArgGprs_2l hr))
      (fun _ hr => hargs_ns _ (mem_tupArgGprs_2r hr))
      (fun _ hr => hdsts_ns _ (mem_tupDstGprs_1 hr)) hha hhb hwp
  | or t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    rcases hrel with _ | ⟨hha, _ | ⟨hhb, _⟩⟩
    exact vllCoreBoolOrBits_spec hwf (fun _ _ _ => rfl) (fun a b => (boolAlu_eval_eq a b).2.1)
      Bool.or_comm hop (fun _ hr => hargs_ns _ (mem_tupArgGprs_2l hr))
      (fun _ hr => hargs_ns _ (mem_tupArgGprs_2r hr))
      (fun _ hr => hdsts_ns _ (mem_tupDstGprs_1 hr)) hha hhb hwp
  | xor t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    rcases hrel with _ | ⟨hha, _ | ⟨hhb, _⟩⟩
    exact vllCoreBoolOrBits_spec hwf (fun _ _ _ => rfl) (fun a b => (boolAlu_eval_eq a b).2.2)
      Bool.xor_comm hop (fun _ hr => hargs_ns _ (mem_tupArgGprs_2l hr))
      (fun _ hr => hargs_ns _ (mem_tupArgGprs_2r hr))
      (fun _ hr => hdsts_ns _ (mem_tupDstGprs_1 hr)) hha hhb hwp
  | not t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    rcases hrel with _ | ⟨hha, _⟩
    exact vllCoreNot_spec hwf hop hha hwp
  | shl t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    rcases hrel with _ | ⟨hha, _ | ⟨hhb, _⟩⟩
    exact vllCoreBinTy_spec hwf (f := fun {k} x y => x <<< (y.toNat % k)) (fun _ _ _ => rfl) hop
      (fun _ hr => hargs_ns _ (mem_tupArgGprs_2r hr)) hha hhb
      (by cases t <;> first | exact hwp | trivial)
  | lshr t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    rcases hrel with _ | ⟨hha, _ | ⟨hhb, _⟩⟩
    exact vllCoreBinTy_spec hwf (f := fun {k} x y => x >>> (y.toNat % k)) (fun _ _ _ => rfl) hop
      (fun _ hr => hargs_ns _ (mem_tupArgGprs_2r hr)) hha hhb
      (by cases t <;> first | exact hwp | trivial)
  | ashr t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    rcases hrel with _ | ⟨hha, _ | ⟨hhb, _⟩⟩
    exact vllCoreBinTy_spec hwf (f := fun {k} x y => x.sshiftRight (y.toNat % k))
      (fun _ _ _ => rfl) hop (fun _ hr => hargs_ns _ (mem_tupArgGprs_2r hr)) hha hhb
      (by cases t <;> first | exact hwp | trivial)
  | cmp co t m hm =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    rcases hrel with _ | ⟨hha, _ | ⟨hhb, _⟩⟩
    exact vllCoreCmp_spec hwf condOfCmp? hcmp hop
      (fun _ hr => hargs_ns _ (mem_tupArgGprs_2r hr)) hha hhb hwp
  | zext m n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    rcases hrel with _ | ⟨hha, _⟩
    exact vllCoreZext_spec hwf hop hha hwp.2
  | sext m n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    rcases hrel with _ | ⟨hha, _⟩
    exact vllCoreSext_spec hwf hop hha hwp.2
  | trunc m n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    rcases hrel with _ | ⟨hha, _⟩
    exact vllCoreTrunc_spec hwf hop hha hwp.2
  | ofBool n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    rcases hrel with _ | ⟨hha, _⟩
    exact vllCoreOfBool_spec hwf hop hha hwp
  | bitcast t u htu =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    rcases hrel with _ | ⟨hha, _⟩
    exact vllCoreBitcast_spec hwf hop hha hwp
  | _ => cases hop

/-- Soundness of pure first-class `vllCoreLoad` on `vllMach A`. -/
theorem vllCoreLoad_spec (A : Arch) (hwf : A.Wf) (ext : LoadExt)
    {h : VllHost A} {k : Nat} {t : Ty} {rd : A.Reg} {a : AddrArg A.Reg}
    {c : List (Instr A)} {clob : FlagMask} {v : Val t} {s : MachSt A} {post : Config A → Prop}
    (hld : vllCoreLoad A ext t rd a = some (c, clob))
    (hval : loadVal s.mem t (a.eval s.gpr) = some v) :
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => GprHolds (s'.gpr rd) t v ∧ s'.mem = s.mem) post := by
  cases t with
  | bool =>
    cases hld
    refine Machine.FallsTo.conseq
      (fallsTo_weaken_rd (vllMach_load_spec hwf (loadVal_bool_to_bits8 hval) (ext := ext)
        (rd := rd))) ?_
    intro s' ⟨_, hg, hm⟩ _; exact ⟨hg.2, hm⟩
  | bits n =>
    dsimp only [vllCoreLoad] at hld; split at hld
    · cases hw : Width.ofBits? n with
      | none => simp [hw] at hld
      | some w =>
        simp only [hw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hld
        rcases hld with ⟨rfl, rfl⟩; obtain rfl := width_ofBits?_eq hw
        refine Machine.FallsTo.conseq
          (fallsTo_weaken_rd (vllMach_load_spec hwf hval (ext := ext) (rd := rd))) ?_
        intro s' ⟨_, hg, hm⟩ _; exact ⟨hg, hm⟩
    · cases hld
  | float _ | pair _ _ => cases hld

/-- When `ext = .zx`, `vllCoreLoad` leaves `rd` in canonical zero-extended ABI form. -/
theorem vllCoreLoad_zx_zext (A : Arch) (hwf : A.Wf)
    {h : VllHost A} {k : Nat} {t : Ty} {rd : A.Reg} {a : AddrArg A.Reg}
    {c : List (Instr A)} {clob : FlagMask} {v : Val t} {s : MachSt A} {post : Config A → Prop}
    (hld : vllCoreLoad A .zx t rd a = some (c, clob))
    (hval : loadVal s.mem t (a.eval s.gpr) = some v) :
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => AbiGprHolds (s'.gpr rd) t v ∧ s'.mem = s.mem) post := by
  cases t with
  | bool =>
    cases hld
    refine Machine.FallsTo.conseq
      (fallsTo_weaken_rd (vllMach_load_spec hwf (loadVal_bool_to_bits8 hval) (ext := .zx)
        (rd := rd))) ?_
    intro s' ⟨hg, _, hm⟩ _; refine ⟨?_, hm⟩
    show s'.gpr rd = BitVec.ofNat 64 v.toNat; rw [hg]; cases v <;> rfl
  | bits n =>
    dsimp only [vllCoreLoad] at hld; split at hld
    · cases hw : Width.ofBits? n with
      | none => simp [hw] at hld
      | some w =>
        simp only [hw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hld
        rcases hld with ⟨rfl, rfl⟩; obtain rfl := width_ofBits?_eq hw
        refine Machine.FallsTo.conseq
          (fallsTo_weaken_rd (vllMach_load_spec hwf hval (ext := .zx) (rd := rd))) ?_
        intro s' ⟨hg, _, hm⟩ _; exact ⟨⟨w.bits_le_64, hg⟩, hm⟩
    · cases hld
  | float _ | pair _ _ => cases hld

/-- When `ext = .zx`, `vllCoreLoad` at `i32` zeroes bits `32..63` of `rd`. -/
theorem vllCoreLoad_zx_zero32 (A : Arch) (hwf : A.Wf)
    {h : VllHost A} {k : Nat} {rd : A.Reg} {a : AddrArg A.Reg}
    {c : List (Instr A)} {clob : FlagMask} {v : BitVec 32} {s : MachSt A} {post : Config A → Prop}
    (hld : vllCoreLoad A .zx (.bits 32) rd a = some (c, clob))
    (hval : loadVal s.mem (.bits 32) (a.eval s.gpr) = some v) :
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => s'.gpr rd = v.setWidth 64 ∧ s'.mem = s.mem) post :=
  Machine.FallsTo.conseq (vllCoreLoad_zx_zext A hwf hld hval) fun _ ⟨habi, hm⟩ _ => ⟨habi.2, hm⟩

private theorem vllCoreStoreW_spec {A : Arch} {w : Width}
    {pa : PArg A.Reg A.VReg A.Cond (.bits w.bits)} {a : AddrArg A.Reg}
    {c : List (Instr A)} {clob : FlagMask} {v : BitVec w.bits}
    {h : VllHost A} {k : Nat} {s : MachSt A} {post : Config A → Prop}
    (hst : vllCoreStoreW A w pa a = some (c, clob))
    (ha_ns : ∀ r ∈ a.regs, r ∉ A.abi.scratch)
    (hh : (vllMach A).PArgHolds s (.bits w.bits) pa v)
    (hok : storeOk s.mem (.bits w.bits) (a.eval s.gpr)) :
    (vllMach A).FallsTo A.condReads h k c A.abi.scratch [] clob s
      (fun s' => s'.mem = storeMem s.mem (.bits w.bits) (a.eval s.gpr) v) post := by
  cases pa with
  | vec _ => cases hst
  | gpr r =>
    cases hst
    refine Machine.FallsTo.conseq (Machine.FallsTo.weaken
      (vllMach_store_spec (A := A) (w := w) (rs := r) (addr := a) hok)
      (fun _ h => nomatch h) (fun _ h => nomatch h) (flagMask_none_sub _)) ?_
    intro s' hm' _
    have hh2 : (s.gpr r).setWidth w.bits = v := hh.2
    rw [hh2] at hm'; exact hm'
  | imm cv =>
    have hEq : cv = v := hh; subst hEq
    cases hs0 : A.abi.scratch.head? with
    | none => simp [vllCoreStoreW, hs0] at hst
    | some s0 =>
      simp only [vllCoreStoreW, hs0, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
      rcases hst with ⟨rfl, rfl⟩
      have hcomp :
          (vllMach A).FallsTo A.condReads h k ([.movi s0 (cv.setWidth 64)] ++ [.store w s0 a])
            (A.abi.scratch ++ []) ([] ++ []) (FlagMask.none ||| FlagMask.none) s
            (fun s' => s'.mem = storeMem s.mem (.bits w.bits) (a.eval s.gpr) cv) post := by
        refine Machine.FallsTo.comp
          (fallsTo_weaken_s0 (head?_mem hs0) (vllMach_movi_spec (A := A) (rd := s0)
            (imm := cv.setWidth 64))) fun s1 ⟨hg1, hm1⟩ hfr1 => ?_
        have ha1 : a.eval s1.gpr = a.eval s.gpr := addrArg_eval_frame hfr1.1 ha_ns
        have hm1' : s1.mem = s.mem := hm1
        have hg1' : s1.gpr s0 = cv.setWidth 64 := hg1
        have hok1 : storeOk s1.mem w.toTy (a.eval s1.gpr) := by rw [hm1', ha1]; exact hok
        refine Machine.FallsTo.conseq
          (vllMach_store_spec (A := A) (w := w) (rs := s0) (addr := a) hok1) ?_
        intro s2 hm2 _
        rw [hm2, hm1', ha1, hg1', setWidth_setWidth_self w.bits_le_64]
      exact Machine.FallsTo.weaken hcomp (fun _ hr => by simpa using hr)
        (fun _ h => nomatch h) (by simp [FlagMask.none])

/-- Soundness of pure first-class `vllCoreStore` on `vllMach A`. -/
theorem vllCoreStore_spec (A : Arch) (hwf : A.Wf)
    {h : VllHost A} {k : Nat} {t : Ty} {pa : PArg A.Reg A.VReg A.Cond t} {a : AddrArg A.Reg}
    {c : List (Instr A)} {clob : FlagMask} {v : Val t} {s : MachSt A} {post : Config A → Prop}
    (hst : vllCoreStore A t pa a = some (c, clob))
    (hns : ∀ r ∈ pa.gprs ++ a.regs, r ∉ A.abi.scratch)
    (hh : (vllMach A).PArgHolds s t pa v) (hok : storeOk s.mem t (a.eval s.gpr)) :
    (vllMach A).FallsTo A.condReads h k c A.abi.scratch [] clob s
      (fun s' => s'.mem = storeMem s.mem t (a.eval s.gpr) v) post := by
  have ha_ns : ∀ r ∈ a.regs, r ∉ A.abi.scratch := fun r hr => hns r (List.mem_append_right _ hr)
  cases t with
  | float _ | pair _ _ => cases hst
  | bool =>
    have hok8 : storeOk s.mem (.bits 8) (a.eval s.gpr) := hok
    cases pa with
    | vec _ => cases hst
    | gpr r =>
      cases hst
      refine Machine.FallsTo.conseq (Machine.FallsTo.weaken
        (vllMach_store_spec (A := A) (w := .w8) (rs := r) (addr := a) hok8)
        (fun _ h => nomatch h) (fun _ h => nomatch h) (flagMask_none_sub _)) ?_
      intro s' hm' _
      have hh8 : (s.gpr r).setWidth 8 = BitVec.ofNat 8 v.toNat := hh
      rw [hm', hh8, storeMem_bool_eq_bits8]
    | imm bv =>
      have hEq : bv = v := hh; subst hEq
      cases hs0 : A.abi.scratch.head? with
      | none => simp [vllCoreStore, hs0] at hst
      | some s0 =>
        simp only [vllCoreStore, hs0, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
        rcases hst with ⟨rfl, rfl⟩
        have hcomp :
            (vllMach A).FallsTo A.condReads h k
              ([.movi s0 (BitVec.ofNat 64 bv.toNat)] ++ [.store .w8 s0 a])
              (A.abi.scratch ++ []) ([] ++ []) (FlagMask.none ||| FlagMask.none) s
              (fun s' => s'.mem = storeMem s.mem .bool (a.eval s.gpr) bv) post := by
          refine Machine.FallsTo.comp
            (fallsTo_weaken_s0 (head?_mem hs0) (vllMach_movi_spec (A := A) (rd := s0)
              (imm := BitVec.ofNat 64 bv.toNat))) fun s1 ⟨hg1, hm1⟩ hfr1 => ?_
          have ha1 : a.eval s1.gpr = a.eval s.gpr := addrArg_eval_frame hfr1.1 ha_ns
          have hm1' : s1.mem = s.mem := hm1
          have hg1' : s1.gpr s0 = BitVec.ofNat 64 bv.toNat := hg1
          have hok1 : storeOk s1.mem Width.w8.toTy (a.eval s1.gpr) := by rw [hm1', ha1]; exact hok8
          refine Machine.FallsTo.conseq
            (vllMach_store_spec (A := A) (w := .w8) (rs := s0) (addr := a) hok1) ?_
          intro s2 hm2 _
          rw [hm2, hm1', ha1, hg1', ofNat64_setWidth8_bool, storeMem_bool_eq_bits8]
        exact Machine.FallsTo.weaken hcomp (fun _ hr => by simpa using hr)
          (fun _ h => nomatch h) (by simp [FlagMask.none])
    | flag cf =>
      have hEq : (vllMach A).evalCond s cf = v := hh
      cases hs0 : A.abi.scratch.head? with
      | none => simp [vllCoreStore, hs0] at hst
      | some s0 =>
        simp only [vllCoreStore, hs0, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
        rcases hst with ⟨rfl, rfl⟩
        have hcomp :
            (vllMach A).FallsTo A.condReads h k ([.setcc s0 cf] ++ [.store .w8 s0 a])
              (A.abi.scratch ++ []) ([] ++ []) (FlagMask.none ||| FlagMask.none) s
              (fun s' => s'.mem = storeMem s.mem .bool (a.eval s.gpr) v) post := by
          refine Machine.FallsTo.comp
            (fallsTo_weaken_s0 (head?_mem hs0) (vllMach_setcc_spec hwf (rd := s0) (c := cf)))
            fun s1 ⟨hg1, hm1⟩ hfr1 => ?_
          have ha1 : a.eval s1.gpr = a.eval s.gpr := addrArg_eval_frame hfr1.1 ha_ns
          have hm1' : s1.mem = s.mem := hm1
          have hok1 : storeOk s1.mem Width.w8.toTy (a.eval s1.gpr) := by rw [hm1', ha1]; exact hok8
          have hg1' : (s1.gpr s0).setWidth 8 = BitVec.ofNat 8 v.toNat := by
            rw [hEq] at hg1; exact hg1
          refine Machine.FallsTo.conseq
            (vllMach_store_spec (A := A) (w := .w8) (rs := s0) (addr := a) hok1) ?_
          intro s2 hm2 _
          rw [hm2, hm1', ha1, hg1', storeMem_bool_eq_bits8]
        exact Machine.FallsTo.weaken hcomp (fun _ hr => by simpa using hr)
          (fun _ h => nomatch h) (by simp [FlagMask.none])
  | bits n =>
    dsimp only [vllCoreStore] at hst; split at hst
    · obtain ⟨w, rfl, hw⟩ := withWidth_eq_some hst
      exact vllCoreStoreW_spec hw ha_ns hh hok
    · cases hst

/-! ## 3. Structural Label-Freedom (`NoVllLab`) for Core Lowering -/

/-- No instruction in `cs` is `.label l`. -/
@[expose] def NoVllLab {A : Arch} (cs : List (Instr A)) : Prop :=
  ∀ l : Sym, Instr.label l ∉ cs

theorem noVllLab_nil {A : Arch} : NoVllLab ([] : List (Instr A)) := fun _ h => nomatch h

theorem noVllLab_cons {A : Arch} {i : Instr A} {cs : List (Instr A)}
    (hi : ∀ l, i ≠ .label l) (hcs : NoVllLab cs) : NoVllLab (i :: cs) := fun l hm => by
  rcases List.mem_cons.mp hm with h | h
  · exact hi l h.symm
  · exact hcs l h

theorem noVllLab_one {A : Arch} {i : Instr A} (hi : ∀ l, i ≠ .label l) : NoVllLab [i] :=
  noVllLab_cons hi noVllLab_nil

theorem noVllLab_two {A : Arch} {i j : Instr A}
    (hi : ∀ l, i ≠ .label l) (hj : ∀ l, j ≠ .label l) : NoVllLab [i, j] :=
  noVllLab_cons hi (noVllLab_one hj)

theorem noVllLab_append {A : Arch} {c1 c2 : List (Instr A)}
    (h1 : NoVllLab c1) (h2 : NoVllLab c2) : NoVllLab (c1 ++ c2) := fun l hm => by
  rcases List.mem_append.mp hm with h | h
  · exact h1 l h
  · exact h2 l h

private theorem regOfPArg_noLab {A : Arch} {s0? : Option A.Reg} {w : Width}
    {pa : PArg A.Reg A.VReg A.Cond (.bits w.bits)} {c : List (Instr A)} {r : A.Reg}
    (h : vllRegOfPArg s0? w pa = some (c, r)) : NoVllLab c := by
  cases pa with
  | gpr _ => cases h; exact noVllLab_nil
  | imm _ =>
    cases s0? with
    | none => simp [vllRegOfPArg] at h
    | some _ =>
      simp only [vllRegOfPArg, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩; exact noVllLab_one (fun _ e => by cases e)
  | vec _ => cases h

private theorem boolRegOfPArg_noLab {A : Arch} {s0? : Option A.Reg}
    {pa : PArg A.Reg A.VReg A.Cond .bool} {c : List (Instr A)} {r : A.Reg}
    (h : vllBoolRegOfPArg s0? pa = some (c, r)) : NoVllLab c := by
  cases pa with
  | gpr _ => cases h; exact noVllLab_nil
  | imm _ | flag _ =>
    cases s0? with
    | none => simp [vllBoolRegOfPArg] at h
    | some _ =>
      simp only [vllBoolRegOfPArg, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩; exact noVllLab_one (fun _ e => by cases e)
  | vec _ => cases h

private theorem vllCoreAlu_noLab {A : Arch} {op : CoreAlu} {w : Width}
    {pa pb : PArg A.Reg A.VReg A.Cond (.bits w.bits)} {rd : A.Reg}
    {c : List (Instr A)} {cl : FlagMask}
    (h : vllCoreAlu A op w pa pb rd = some (c, cl)) : NoVllLab c := by
  unfold vllCoreAlu at h
  cases hr : vllRegOfPArg A.abi.scratch.head? w pa with
  | none => simp [hr] at h
  | some p1 =>
    rcases p1 with ⟨c1, ra⟩
    cases hs : vllSrcOfPArg w pb with
    | none => simp [hr, hs] at h
    | some _ =>
      simp only [hr, hs, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩
      exact noVllLab_append (regOfPArg_noLab hr) (noVllLab_one (fun _ e => by cases e))

private theorem vllCoreBinBits_noLab {A : Arch} {op : CoreAlu} {n : Nat}
    {pa pb : PArg A.Reg A.VReg A.Cond (.bits n)} {rd : A.Reg}
    {c : List (Instr A)} {cl : FlagMask}
    (h : vllCoreBinBits A op n pa pb rd = some (c, cl)) : NoVllLab c := by
  unfold vllCoreBinBits at h; split at h
  · obtain ⟨_, rfl, hw⟩ := withWidth_eq_some h; exact vllCoreAlu_noLab hw
  · cases h

private theorem vllCoreBinTy_noLab {A : Arch} {op : CoreAlu} {t : Ty}
    {pa pb : PArg A.Reg A.VReg A.Cond t} {pd : PDst A.Reg A.VReg A.Cond t}
    {c : List (Instr A)} {cl : FlagMask}
    (h : vllCoreBinTy A op t pa pb pd = some (c, cl)) : NoVllLab c := by
  cases t with
  | bits _ => cases pd with | gpr _ => exact vllCoreBinBits_noLab h | vec _ => cases h
  | bool | float _ | pair _ _ => cases h

private theorem vllCoreCopyW_noLab {A : Arch} {w : Width}
    {pa : PArg A.Reg A.VReg A.Cond (.bits w.bits)} {rd : A.Reg}
    {c : List (Instr A)} {cl : FlagMask}
    (h : vllCoreCopyW A w pa rd = some (c, cl)) : NoVllLab c := by
  cases pa with
  | gpr _ | imm _ => cases h; exact noVllLab_one (fun _ e => by cases e)
  | vec _ => cases h

private theorem vllCoreCopy_noLab {A : Arch} {t : Ty}
    {pa : PArg A.Reg A.VReg A.Cond t} {pd : PDst A.Reg A.VReg A.Cond t}
    {c : List (Instr A)} {cl : FlagMask}
    (h : vllCoreCopy A t pa pd = some (c, cl)) : NoVllLab c := by
  cases t with
  | bool =>
    cases pd with
    | gpr _ =>
      cases pa with
      | gpr _ | imm _ | flag _ => cases h; exact noVllLab_one (fun _ e => by cases e)
      | vec _ => cases h
    | vec _ | flag _ => cases h
  | bits _ =>
    cases pd with
    | gpr _ =>
      dsimp only [vllCoreCopy] at h; split at h
      · obtain ⟨_, rfl, hw⟩ := withWidth_eq_some h; exact vllCoreCopyW_noLab hw
      · cases h
    | vec _ => cases h
  | float _ | pair _ _ => cases h

private theorem vllCoreNeg_noLab {A : Arch} {t : Ty}
    {pa : PArg A.Reg A.VReg A.Cond t} {pd : PDst A.Reg A.VReg A.Cond t}
    {c : List (Instr A)} {cl : FlagMask}
    (h : vllCoreNeg A t pa pd = some (c, cl)) : NoVllLab c := by
  cases t with
  | bits _ =>
    cases pd with
    | gpr _ =>
      dsimp only [vllCoreNeg] at h; split at h
      · obtain ⟨w, rfl, hw⟩ := withWidth_eq_some h
        unfold vllCoreNegW at hw
        cases hs0 : A.abi.scratch.head? <;> cases hs : vllSrcOfPArg w pa <;> simp [hs0, hs] at hw
        rcases hw with ⟨rfl, rfl⟩
        exact noVllLab_two (fun _ e => by cases e) (fun _ e => by cases e)
      · cases h
    | vec _ => cases h
  | bool | float _ | pair _ _ => cases h

private theorem vllCoreBoolBin_noLab {A : Arch} {op : CoreAlu}
    {pa pb : PArg A.Reg A.VReg A.Cond .bool} {rd : A.Reg}
    {c : List (Instr A)} {cl : FlagMask}
    (h : vllCoreBoolBin A op pa pb rd = some (c, cl)) : NoVllLab c := by
  unfold vllCoreBoolBin at h
  cases pb with
  | vec _ => cases h
  | gpr _ | imm _ =>
    cases hr : vllBoolRegOfPArg A.abi.scratch.head? pa with
    | none => simp [hr] at h
    | some p1 =>
      rcases p1 with ⟨c1, ra⟩
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact noVllLab_append (boolRegOfPArg_noLab hr) (noVllLab_one (fun _ e => by cases e))
  | flag _ =>
    cases pa <;> cases hs0 : A.abi.scratch.head? <;> simp [hs0] at h
    all_goals
      rcases h with ⟨rfl, rfl⟩
      repeat (apply noVllLab_cons (fun _ e => by cases e))
      exact noVllLab_nil

private theorem vllCoreBoolOrBits_noLab {A : Arch} {op : CoreAlu} {t : Ty}
    {pa pb : PArg A.Reg A.VReg A.Cond t} {pd : PDst A.Reg A.VReg A.Cond t}
    {c : List (Instr A)} {cl : FlagMask}
    (h : vllCoreBoolOrBits A op t pa pb pd = some (c, cl)) : NoVllLab c := by
  cases t with
  | bool => cases pd with | gpr _ => exact vllCoreBoolBin_noLab h | vec _ | flag _ => cases h
  | bits _ => cases pd with | gpr _ => exact vllCoreBinBits_noLab h | vec _ => cases h
  | float _ | pair _ _ => cases h

private theorem vllCoreNot_noLab {A : Arch} {t : Ty}
    {pa : PArg A.Reg A.VReg A.Cond t} {pd : PDst A.Reg A.VReg A.Cond t}
    {c : List (Instr A)} {cl : FlagMask}
    (h : vllCoreNot A t pa pd = some (c, cl)) : NoVllLab c := by
  cases t with
  | bool =>
    cases pd with
    | gpr _ =>
      dsimp only [vllCoreNot] at h
      cases hr : vllBoolRegOfPArg A.abi.scratch.head? pa with
      | none => simp [hr] at h
      | some p1 =>
        rcases p1 with ⟨c1, ra⟩
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact noVllLab_append (boolRegOfPArg_noLab hr) (noVllLab_one (fun _ e => by cases e))
    | vec _ | flag _ => cases h
  | bits _ =>
    cases pd with
    | gpr _ =>
      dsimp only [vllCoreNot] at h; split at h
      · obtain ⟨w, rfl, hw⟩ := withWidth_eq_some h
        unfold vllCoreNotW at hw
        cases hr : vllRegOfPArg A.abi.scratch.head? w pa with
        | none => simp [hr] at hw
        | some p1 =>
          rcases p1 with ⟨c1, ra⟩
          simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hw
          rcases hw with ⟨rfl, rfl⟩
          exact noVllLab_append (regOfPArg_noLab hr) (noVllLab_one (fun _ e => by cases e))
      · cases h
    | vec _ => cases h
  | float _ | pair _ _ => cases h

private theorem vllCoreCmp_noLab {A : Arch} {condOfCmp? : CmpOp → Option A.Cond}
    {co : CmpOp} {t m : Ty} {hm : m = t.mask}
    {pa pb : PArg A.Reg A.VReg A.Cond t} {pd : PDst A.Reg A.VReg A.Cond m}
    {c : List (Instr A)} {cl : FlagMask}
    (h : vllCoreCmp A condOfCmp? co t m hm pa pb pd = some (c, cl)) : NoVllLab c := by
  subst hm
  cases t with
  | bits _ =>
    dsimp only [vllCoreCmp] at h; split at h
    · obtain ⟨w, rfl, hw⟩ := withWidth_eq_some h
      dsimp only [vllCoreCmpW] at hw
      cases hcc : condOfCmp? co with
      | none => simp [hcc] at hw
      | some _ =>
        simp only [hcc] at hw
        cases hr : vllRegOfPArg A.abi.scratch.head? w pa with
        | none => simp [hr] at hw
        | some p1 =>
          rcases p1 with ⟨c1, ra⟩
          cases hs : vllSrcOfPArg w pb with
          | none => simp [hr, hs] at hw
          | some _ =>
            simp only [hr, hs] at hw
            cases pd with
            | vec _ => cases hw
            | gpr _ =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hw; rcases hw with ⟨rfl, rfl⟩
              exact noVllLab_append (regOfPArg_noLab hr)
                (noVllLab_two (fun _ e => by cases e) (fun _ e => by cases e))
            | flag _ =>
              dsimp only at hw; split at hw
              · simp only [Option.some.injEq, Prod.mk.injEq] at hw; rcases hw with ⟨rfl, rfl⟩
                exact noVllLab_append (regOfPArg_noLab hr) (noVllLab_one (fun _ e => by cases e))
              · cases hw
    · cases h
  | bool | float _ | pair _ _ => cases h

/-- Pure first-class `vllCoreOp` never emits `.label`. -/
theorem vllCoreOp_noLab {A : Arch} {condOfCmp? : CmpOp → Option A.Cond}
    {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg A.Reg A.VReg A.Cond) sig} {dsts : Tup (PDst A.Reg A.VReg A.Cond) rs}
    {vh : VariantHint} {c : List (Instr A)} {cl : FlagMask}
    (h : vllCoreOp A condOfCmp? code pas dsts vh = some (c, cl)) : NoVllLab c := by
  cases code with
  | copy _ => rcases pas with ⟨_, ⟨⟩⟩; rcases dsts with ⟨_, ⟨⟩⟩; exact vllCoreCopy_noLab h
  | add _ | sub _ | mul _ | shl _ | lshr _ | ashr _ =>
    rcases pas with ⟨_, _, ⟨⟩⟩; rcases dsts with ⟨_, ⟨⟩⟩; exact vllCoreBinTy_noLab h
  | neg _ => rcases pas with ⟨_, ⟨⟩⟩; rcases dsts with ⟨_, ⟨⟩⟩; exact vllCoreNeg_noLab h
  | and _ | or _ | xor _ =>
    rcases pas with ⟨_, _, ⟨⟩⟩; rcases dsts with ⟨_, ⟨⟩⟩; exact vllCoreBoolOrBits_noLab h
  | not _ => rcases pas with ⟨_, ⟨⟩⟩; rcases dsts with ⟨_, ⟨⟩⟩; exact vllCoreNot_noLab h
  | cmp _ _ _ _ => rcases pas with ⟨_, _, ⟨⟩⟩; rcases dsts with ⟨_, ⟨⟩⟩; exact vllCoreCmp_noLab h
  | zext _ _ =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with
    | vec _ => cases h
    | gpr _ =>
      dsimp only [vllCoreOp, vllCoreZext] at h; split at h
      · cases pa with
        | gpr _ => cases h; exact noVllLab_two (fun _ e => by cases e) (fun _ e => by cases e)
        | imm _ => cases h; exact noVllLab_one (fun _ e => by cases e)
        | vec _ => cases h
      · cases h
  | sext _ _ =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with
    | vec _ => cases h
    | gpr _ =>
      dsimp only [vllCoreOp, vllCoreSext] at h; split at h
      · obtain ⟨_, rfl, hw⟩ := withWidth_eq_some h
        unfold vllCoreSextW at hw; split at hw
        · cases pa with
          | gpr _ => cases hw; exact noVllLab_two (fun _ e => by cases e) (fun _ e => by cases e)
          | imm _ => cases hw; exact noVllLab_one (fun _ e => by cases e)
          | vec _ => cases hw
        · cases hw
      · cases h
  | trunc _ _ =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with
    | vec _ => cases h
    | gpr _ =>
      dsimp only [vllCoreOp, vllCoreTrunc] at h; split at h
      · obtain ⟨_, rfl, hw⟩ := withWidth_eq_some h
        unfold vllCoreTruncW at hw; split at hw
        · cases pa with
          | gpr _ | imm _ => cases hw; exact noVllLab_one (fun _ e => by cases e)
          | vec _ => cases hw
        · cases hw
      · cases h
  | ofBool _ =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with
    | vec _ => cases h
    | gpr _ =>
      dsimp only [vllCoreOp, vllCoreOfBool] at h; split at h
      · cases pa with
        | gpr _ | flag _ =>
          cases h; exact noVllLab_two (fun _ e => by cases e) (fun _ e => by cases e)
        | imm _ => cases h; exact noVllLab_one (fun _ e => by cases e)
        | vec _ => cases h
      · cases h
  | bitcast t u _ =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with
    | bits _ =>
      cases u with
      | bits _ =>
        cases pd with
        | gpr _ =>
          dsimp only [vllCoreOp, vllCoreBitcast] at h; split at h
          · obtain ⟨_, rfl, hw⟩ := withWidth_eq_some h; exact vllCoreCopyW_noLab hw
          · cases h
        | vec _ => cases h
      | bool | float _ | pair _ _ => cases h
    | bool | float _ | pair _ _ => cases h
  | _ => cases h

/-- Pure first-class `vllCoreLoad` never emits `.label`. -/
theorem vllCoreLoad_noLab {A : Arch} {ext : LoadExt} {t : Ty} {rd : A.Reg}
    {a : AddrArg A.Reg} {c : List (Instr A)} {cl : FlagMask}
    (h : vllCoreLoad A ext t rd a = some (c, cl)) : NoVllLab c := by
  cases t with
  | bool => cases h; exact noVllLab_one (fun _ e => by cases e)
  | bits n =>
    dsimp only [vllCoreLoad] at h; split at h
    · cases hw : Width.ofBits? n with
      | none => simp [hw] at h
      | some _ =>
        simp only [hw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩; exact noVllLab_one (fun _ e => by cases e)
    · cases h
  | float _ | pair _ _ => cases h

/-- Pure first-class `vllCoreStore` never emits `.label`. -/
theorem vllCoreStore_noLab {A : Arch} {t : Ty} {pa : PArg A.Reg A.VReg A.Cond t}
    {a : AddrArg A.Reg} {c : List (Instr A)} {cl : FlagMask}
    (h : vllCoreStore A t pa a = some (c, cl)) : NoVllLab c := by
  cases t with
  | float _ | pair _ _ => cases h
  | bool =>
    cases pa with
    | vec _ => cases h
    | gpr _ => cases h; exact noVllLab_one (fun _ e => by cases e)
    | imm _ | flag _ =>
      cases hs0 : A.abi.scratch.head? <;> simp [vllCoreStore, hs0] at h
      rcases h with ⟨rfl, rfl⟩; exact noVllLab_two (fun _ e => by cases e) (fun _ e => by cases e)
  | bits _ =>
    dsimp only [vllCoreStore] at h; split at h
    · obtain ⟨_, rfl, hw⟩ := withWidth_eq_some h
      cases pa with
      | vec _ => cases hw
      | gpr _ => cases hw; exact noVllLab_one (fun _ e => by cases e)
      | imm _ =>
        cases hs0 : A.abi.scratch.head? <;> simp [vllCoreStoreW, hs0] at hw
        rcases hw with ⟨rfl, rfl⟩
        exact noVllLab_two (fun _ e => by cases e) (fun _ e => by cases e)
    · cases h

end LeanQbe.T.Vll
