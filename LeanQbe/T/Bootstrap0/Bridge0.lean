module

public import LeanQbe.T.Bootstrap0.Types0
public import LeanQbe.T.Frontend.C0.Elab
public import LeanQbe.T.LeanLCNF.Lower1
public import LeanQbe.T.Amd64.Isel
public import LeanQbe.T.Amd64.Frame

/-!
# Bridge Adapters Between `LeanQbe.T` / `Kraken.X64` and `leanqbe0`

Reuses existing codebase IR and x64 assembly infrastructure outside `Compiler0.lean`:
* `ofTFlatModule`: translates real `Frontend.C0.TFlatFn` modules (including `LeanLCNF` output)
  into `TFlatModule0` plus the numeric symbol table.
* `toAmd64Program`: translates `List Dir0` emitted by `leanqbe0Compile` into `List Amd64.Directive`
  printable by `Kraken.X64.toATT` (using `Amd64.Base`/`Amd64.Isel`/`Amd64.Frame` primitives).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T
open LeanQbe.T.Amd64

/-- Convert a supported scalar `Ty` into `Ty0`. -/
def tyToTy0 : Ty → Except String Ty0
  | .bool => .ok .bool
  | .bits 8 => .ok .b8
  | .bits 16 => .ok .b16
  | .bits 32 => .ok .b32
  | .bits 64 => .ok .b64
  | t => .error s!"ofTFlatModule: unsupported type {repr t}"

/-- Convert a `List Ty` into `List Ty0`. -/
def tyListToTy0 : List Ty → Except String (List Ty0)
  | [] => .ok []
  | t :: rest => do .ok ((← tyToTy0 t) :: (← tyListToTy0 rest))

/-- Convert a bit width `{8, 16, 32, 64}` into `Width`. -/
def bitsToWidth0 : Nat → Except String Width
  | 8 => .ok .W8
  | 16 => .ok .W16
  | 32 => .ok .W32
  | 64 => .ok .W64
  | n => .error s!"ofTFlatModule: unsupported bit width {n}"

/-- Translate a typed `Arg K t` into first-order `Arg0`. -/
def argToArg0 : (t : Ty) → Arg K t → Except String Arg0
  | _, .var i => .ok (.var (UInt32.ofNat i))
  | .bool, .imm b => .ok (.immBool b)
  | .bits n, .imm c => do
    let w ← bitsToWidth0 n
    .ok (.immBits w (UInt64.ofNat c.toNat))
  | t, .imm _ => .error s!"ofTFlatModule: unsupported immediate type {repr t}"

/-- Translate a typed operand tuple `Tup (Arg K) ts` into `List Arg0`. -/
def tupArgsToList0 : (ts : List Ty) → Tup (Arg K) ts → Except String (List Arg0)
  | [], () => .ok []
  | t :: ts, (a, rest) => do
    let a0 ← argToArg0 t a
    let rest0 ← tupArgsToList0 ts rest
    .ok (a0 :: rest0)

/-- Translate `OpCode sig rs` + already-converted `args0` into `.let1` or `.let2Umulw64`. -/
def opCodeToTFlat0 : {sig rs : List Ty} → OpCode sig rs → List Arg0 → TFlat0 →
    Except String TFlat0
  | _, _, .copy t, args0, k => do .ok (.let1 (.un .copy (← tyToTy0 t)) args0 k)
  | _, _, .neg t, args0, k => do .ok (.let1 (.un .neg (← tyToTy0 t)) args0 k)
  | _, _, .not t, args0, k => do .ok (.let1 (.un .not (← tyToTy0 t)) args0 k)
  | _, _, .add t, args0, k => do .ok (.let1 (.bin .add (← tyToTy0 t)) args0 k)
  | _, _, .sub t, args0, k => do .ok (.let1 (.bin .sub (← tyToTy0 t)) args0 k)
  | _, _, .mul t, args0, k => do .ok (.let1 (.bin .mul (← tyToTy0 t)) args0 k)
  | _, _, .and t, args0, k => do .ok (.let1 (.bin .and (← tyToTy0 t)) args0 k)
  | _, _, .or t, args0, k => do .ok (.let1 (.bin .or (← tyToTy0 t)) args0 k)
  | _, _, .xor t, args0, k => do .ok (.let1 (.bin .xor (← tyToTy0 t)) args0 k)
  | _, _, .shl t, args0, k => do .ok (.let1 (.bin .shl (← tyToTy0 t)) args0 k)
  | _, _, .lshr t, args0, k => do .ok (.let1 (.bin .lshr (← tyToTy0 t)) args0 k)
  | _, _, .ashr t, args0, k => do .ok (.let1 (.bin .ashr (← tyToTy0 t)) args0 k)
  | _, _, .rotl t, args0, k => do .ok (.let1 (.bin .rotl (← tyToTy0 t)) args0 k)
  | _, _, .rotr t, args0, k => do .ok (.let1 (.bin .rotr (← tyToTy0 t)) args0 k)
  | _, _, .cmp co t _ _, args0, k => do .ok (.let1 (.cmp co (← tyToTy0 t)) args0 k)
  | _, _, .select t, args0, k => do .ok (.let1 (.select (← tyToTy0 t)) args0 k)
  | _, _, .ofBool n, args0, k => do
    .ok (.let1 (.conv .ofBool .W8 (← bitsToWidth0 n)) args0 k)
  | _, _, .zext m n, args0, k => do
    .ok (.let1 (.conv .zext (← bitsToWidth0 m) (← bitsToWidth0 n)) args0 k)
  | _, _, .sext m n, args0, k => do
    .ok (.let1 (.conv .sext (← bitsToWidth0 m) (← bitsToWidth0 n)) args0 k)
  | _, _, .trunc m n, args0, k => do
    .ok (.let1 (.conv .trunc (← bitsToWidth0 m) (← bitsToWidth0 n)) args0 k)
  | _, _, .udiv n, args0, k => do .ok (.let1 (.div .udiv (← bitsToWidth0 n)) args0 k)
  | _, _, .urem n, args0, k => do .ok (.let1 (.div .urem (← bitsToWidth0 n)) args0 k)
  | _, _, .sdiv n, args0, k => do .ok (.let1 (.div .sdiv (← bitsToWidth0 n)) args0 k)
  | _, _, .srem n, args0, k => do .ok (.let1 (.div .srem (← bitsToWidth0 n)) args0 k)
  | _, _, .umulw 64, [a, b], k => .ok (.let2Umulw64 a b k)
  | _, _, .bitcast (.bits m) (.bits n) _, args0, k => do
    if m == n then
      let t ← tyToTy0 (.bits m)
      .ok (.let1 (.un .copy t) args0 k)
    else .error s!"ofTFlatModule: unsupported bitcast {m} -> {n}"
  | _, _, _, _, _ => .error "ofTFlatModule: unsupported opcode for Stage A leanqbe0"

/-- Translate `OpCode sig rs` + `args` into `.let1` or `.let2Umulw64`. -/
def opToTFlat0 {sig rs : List Ty} (code : OpCode sig rs)
    (args : Tup (Arg K) sig) (k : TFlat0) : Except String TFlat0 := do
  let args0 ← tupArgsToList0 sig args
  opCodeToTFlat0 code args0 k

/-- Look up symbol ID in association table. -/
def lookupSymId? (tbl : List (Sym × Sym0)) (s : Sym) : Option Sym0 :=
  match tbl with
  | [] => none
  | (n, id) :: rest => if n == s then some id else lookupSymId? rest s

/-- Resolve symbol name by ID (falling back to numeric name). -/
def symNameOf (tbl : List (Sym × Sym0)) (id : Sym0) : Sym :=
  match tbl.find? fun p => p.2 == id with
  | some (s, _) => s
  | none => s!"sym_{id.toNat}"

mutual
/-- Translate `TFlat rs` into first-order `TFlat0`. -/
def tflatToTFlat0 (tbl : List (Sym × Sym0)) {rs : List Ty} :
    TFlat rs → Except String TFlat0
  | .let_ op k => do
    let k0 ← tflatToTFlat0 tbl k
    opToTFlat0 op.code op.args k0
  | .load t a k => do
    let t0 ← tyToTy0 t
    let a0 ← argToArg0 i64 a
    let k0 ← tflatToTFlat0 tbl k
    .ok (.load t0 a0 k0)
  | .store (t := t) v a k => do
    let t0 ← tyToTy0 t
    let v0 ← argToArg0 t v
    let a0 ← argToArg0 i64 a
    let k0 ← tflatToTFlat0 tbl k
    .ok (.store t0 v0 a0 k0)
  | .call f (as := as) bs args k => do
    let some fid := lookupSymId? tbl f
      | .error s!"ofTFlatModule: unknown call symbol '{f}'"
    let as0 ← tyListToTy0 as
    let bs0 ← tyListToTy0 bs
    let args0 ← tupArgsToList0 as args
    let k0 ← tflatToTFlat0 tbl k
    .ok (.call fid as0 bs0 args0 k0)
  | .jnz c t e => do
    let c0 ← argToArg0 .bool c
    let t0 ← tflatToTFlat0 tbl t
    let e0 ← tflatToTFlat0 tbl e
    .ok (.jnz c0 t0 e0)
  | .jump (ts := ts) j args => do
    let args0 ← tupArgsToList0 ts args
    .ok (.jump (UInt32.ofNat j) args0)
  | .ret vs => do
    let vs0 ← tupArgsToList0 rs vs
    .ok (.ret vs0)
  | .exit f (as := as) args => do
    let some fid := lookupSymId? tbl f
      | .error s!"ofTFlatModule: unknown exit symbol '{f}'"
    let as0 ← tyListToTy0 as
    let args0 ← tupArgsToList0 as args
    .ok (.exit fid as0 args0)
  | .hlt => .ok .hlt
  | .group bodies k => do
    let bs0 ← tblocksToList0 tbl bodies
    let k0 ← tflatToTFlat0 tbl k
    .ok (.group bs0 k0)

/-- Translate `TBlocks rs sig` into `List (List Ty0 × TFlat0)`. -/
def tblocksToList0 (tbl : List (Sym × Sym0)) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Except String (List (List Ty0 × TFlat0))
  | _, .nil => .ok []
  | _, .cons (ts := ts) b bs => do
    let ts0 ← tyListToTy0 ts
    let b0 ← tflatToTFlat0 tbl b
    let rest0 ← tblocksToList0 tbl bs
    .ok ((ts0, b0) :: rest0)
end

/-- Translate a list of `Frontend.C0.TFlatFn`s + externs/exits to `TFlatModule0` + sym table. -/
def ofTFlatModule (tfs : List Frontend.C0.TFlatFn)
    (externs : List Extern := LeanLCNF.rtExterns)
    (exits : List Sym := LeanLCNF.rtExitSyms) :
    Except String (TFlatModule0 × List (Sym × Sym0)) := do
  let fnNames := tfs.map (·.name)
  let extNames := externs.map (·.name)
  let allNames := (fnNames ++ extNames ++ exits).eraseDups
  let tbl := allNames.zip ((List.range allNames.length).map UInt32.ofNat)
  let fns0 ← tfs.mapM fun tf => do
    let some fid := lookupSymId? tbl tf.name
      | .error s!"ofTFlatModule: missing fn '{tf.name}'"
    let as0 ← tyListToTy0 tf.as
    let rs0 ← tyListToTy0 tf.rs
    let body0 ← tflatToTFlat0 tbl tf.flat
    .ok { name := fid, as := as0, rs := rs0, body := body0 : TFlatFn0 }
  let exts0 ← externs.mapM fun ex => do
    let some eid := lookupSymId? tbl ex.name
      | .error s!"ofTFlatModule: missing extern '{ex.name}'"
    let as0 ← tyListToTy0 ex.as
    let rs0 ← tyListToTy0 ex.rs
    .ok { name := eid, as := as0, rs := rs0 : ExtSig0 }
  let exits0 ← exits.mapM fun ex => do
    let some eid := lookupSymId? tbl ex
      | .error s!"ofTFlatModule: missing exit '{ex}'"
    .ok eid
  .ok ({ fns := fns0, externs := exts0, exits := exits0 }, tbl)

/-- Render `Label0` as an AT&T assembly label string. -/
def label0ToSym (symName : Sym0 → Sym) : Label0 → Sym
  | .sym id => symName id
  | .loc fnId lblId => s!".L_{fnId.toNat}_{lblId.toNat}"

/-- Map `AluKind0` + `Width` to Kraken `Operation`. -/
def alu0ToOp (w : Width) (k : AluKind0) (rd rs : Reg64) : Operation w :=
  match k with
  | .add => .add (.reg (regW w rd)) (.reg (regW w rs))
  | .sub => .sub (.reg (regW w rd)) (.reg (regW w rs))
  | .mul => .imul none (.reg (regW w rd)) (.reg (regW w rs))
  | .and => .and (.reg (regW w rd)) (.reg (regW w rs))
  | .or => .or (.reg (regW w rd)) (.reg (regW w rs))
  | .xor => .xor (.reg (regW w rd)) (.reg (regW w rs))

/-- Map `ShiftKind0` + `Width` to Kraken `%cl` `Operation`. -/
def shift0ToOp (w : Width) (k : ShiftKind0) (rd : Reg64) : Operation w :=
  match k with
  | .shl => .shl (.reg (regW w rd)) .cl
  | .lshr => .shr (.reg (regW w rd)) .cl
  | .ashr => .sar (.reg (regW w rd)) .cl
  | .rotl => .rol (.reg (regW w rd)) .cl
  | .rotr => .ror (.reg (regW w rd)) .cl

/-- Lower one `Dir0` into concrete `Directive`s reusing `Amd64.Isel`/`Frame`. -/
def dir0ToAmd64 (symName : Sym0 → Sym) : Dir0 → List _root_.Directive
  | .label l => [.label (label0ToSym symName l)]
  | .movRR w rd rs => [insW w (.mov (.reg (regW w rd)) (.reg (regW w rs)))]
  | .movRI rd imm => [moviD rd (BitVec.ofNat 64 imm.toNat)]
  | .movzx32 .W8 rd rs => [ins32 (.movzx (.reg (d rd)) (.reg (b8 rs)))]
  | .movzx32 .W16 rd rs => [ins32 (.movzx (.reg (d rd)) (.reg (h16 rs)))]
  | .movzx32 .W32 rd rs => [ins32 (.mov (.reg (d rd)) (.reg (d rs)))]
  | .movzx32 .W64 rd rs => [ins (.mov (.reg (q rd)) (.reg (q rs)))]
  | .movsx .W64 rd .W8 rs => [ins (.movsx (.reg (q rd)) (.reg (b8 rs)))]
  | .movsx .W64 rd .W16 rs => [ins (.movsx (.reg (q rd)) (.reg (h16 rs)))]
  | .movsx .W64 rd .W32 rs => [ins (.movsx (.reg (q rd)) (.reg (d rs)))]
  | .movsx .W64 rd .W64 rs => [ins (.mov (.reg (q rd)) (.reg (q rs)))]
  | .movsx .W32 rd .W8 rs => [ins32 (.movsx (.reg (d rd)) (.reg (b8 rs)))]
  | .movsx .W32 rd .W16 rs => [ins32 (.movsx (.reg (d rd)) (.reg (h16 rs)))]
  | .movsx wDst rd _ rs => [insW wDst (.mov (.reg (regW wDst rd)) (.reg (regW wDst rs)))]
  | .ldMem .W8 rd base =>
    [ins32 (.movzx (.reg (d rd)) (.mem (atReg base) : RegOrMem .W8))]
  | .ldMem .W16 rd base =>
    [ins32 (.movzx (.reg (d rd)) (.mem (atReg base) : RegOrMem .W16))]
  | .ldMem .W32 rd base => [ins32 (.mov (.reg (d rd)) (.mem (atReg base)))]
  | .ldMem .W64 rd base => [ins (.mov (.reg (q rd)) (.mem (atReg base)))]
  | .stMem w base val => [insW w (.mov (.mem (atReg base)) (.reg (regW w val)))]
  | .ldSlot rd disp =>
    [ins (.mov (.reg (q rd)) (.mem (x64AtSp (Int64.ofNat disp.toNat))))]
  | .stSlot disp rs =>
    [ins (.mov (.mem (x64AtSp (Int64.ofNat disp.toNat))) (.reg (q rs)))]
  | .ldSlotIdx rd idx =>
    [ins (.mov (.reg (q rd)) (.mem { base := some (.reg .rsp), idx := some ⟨idx, .W8⟩ }))]
  | .stSlotIdx idx rs =>
    [ins (.mov (.mem { base := some (.reg .rsp), idx := some ⟨idx, .W8⟩ }) (.reg (q rs)))]
  | .spAdd true imm32 => [x64SubSpD (Int64.ofNat imm32.toNat)]
  | .spAdd false imm32 => [x64AddSpD (Int64.ofNat imm32.toNat)]
  | .spAddReg true r => [ins (.sub (.reg (q .rsp)) (.reg (q r)))]
  | .spAddReg false r => [ins (.add (.reg (q .rsp)) (.reg (q r)))]
  | .aluRR w k rd rs => [insW w (alu0ToOp w k rd rs)]
  | .unary w true rd => [insW w (.neg (.reg (regW w rd)))]
  | .unary w false rd => [insW w (.not (.reg (regW w rd)))]
  | .shiftCl w k rd => [insW w (shift0ToOp w k rd)]
  | .shMaskCl imm => [ins32 (.and (.reg (d .rcx)) (.imm (.int64 (Int64.ofNat imm.toNat))))]
  | .cmpRR w ra rb => [insW w (.cmp (.reg (regW w ra)) (.reg (regW w rb)))]
  | .testbRR ra rb => [ins8 (.test (.reg (b8 ra)) (.reg (b8 rb)))]
  | .setcc cc rd => [ins8 (.setcc cc (.reg (b8 rd)))]
  | .cmovcc w cc rd rs => [insW w (.cmovcc cc (regW w rd) (.reg (regW w rs)))]
  | .divCore .W64 true rhs =>
    [ ins (.mov (.reg (q .rdx)) (.reg (q .rax))),
      ins (.sar (.reg (q .rdx)) (.imm8 (.int64 63))),
      ins (.idiv (.reg (q rhs))) ]
  | .divCore .W64 false rhs =>
    [ moviD .rdx 0,
      ins (.div (.reg (q rhs))) ]
  | .divCore w true rhs =>
    [ ins32 (.mov (.reg (d .rdx)) (.reg (d .rax))),
      ins32 (.sar (.reg (d .rdx)) (.imm8 (.int64 31))),
      insW w (.idiv (.reg (regW w rhs))) ]
  | .divCore w false rhs =>
    [ moviD .rdx 0,
      insW w (.div (.reg (regW w rhs))) ]
  | .mulq rhs => [ins (.mul (.reg (q rhs)))]
  | .jmp l => [x64JmpD (label0ToSym symName l)]
  | .jcc cc l => [ins (.jcc cc (label0ToSym symName l))]
  | .callSym sym => [x64CallD (symName sym)]
  | .ret => [x64RetD]

/-- Convert a full `List Dir0` program into `List Directive`. -/
def toAmd64Program (symName : Sym0 → Sym) (dirs : List Dir0) : List _root_.Directive :=
  dirs.flatMap (dir0ToAmd64 symName)

end LeanQbe.T.Bootstrap0
