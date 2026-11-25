module

public import LeanQbe.T.Wasm.BulkLower

/-!
# Verified WebAssembly to `LeanQbe.T` IR Lowering (`LeanQbe.T.Wasm.Lower`)

Direct, zero-cast, target-independent structured lowering from `WModule` (`LeanQbe.T.Wasm.Ast`)
into `LeanQbe.T.Module` using:
* VM-context SFI ABI (`LeanQbe.T.Wasm.BulkLower`): `(vmCtx, fuel, ...wasmParams)` returning
  `(status, remFuel, ...wasmResults)` with `status = 0` (ok), `1` (trap), `2` (out-of-fuel), and
  `vmCtx` pointing to `[memBase, memLen, memCap]`.
* 64-bit SFI linear memory access checking `zext32(idx) + off + width ≤ᵤ memLen` and verified
  bulk-memory / memory-growth instructions (`memory.size`, `memory.grow`, `memory.fill`,
  `memory.copy`).
* 1:1 `Expr.group` structured control (`block`, `loop`, `if_`, `br`, `br_if`, `br_table`,
  `return_`), with explicit `fuel` checks/decrements on every `loop`, `call`, `memory.grow`,
  `memory.fill`, and `memory.copy`.
* Branchless SWAR `popcnt` and explicit trap/edge-case guards on integer division/remainder
  for compatibility with both `x64Target` (`x64LegalTarget`) and `armTarget`
  (`armLegalTarget`).
* Universal `lowerModule_wf`, `lowerModule_supportsSource`, and `lowerModule_legalSig` theorems.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Wasm

/-! ## Scalar and Control Emitters -/

/-- Width-parametric SWAR population count kernel (`n = 32` or `64`). -/
@[expose] def emitPopcntCore {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (n : Nat) (m1 m2 m4 mul sh : BitVec n) (x : Arg V (.bits n))
    (k : Arg V (.bits n) → Expr V L rs) : Expr V L rs :=
  .let_ (.mk (.lshr (.bits n)) (x, .imm 1#n, ())) fun s1 =>
  .let_ (.mk (.and (.bits n)) (.var s1.1, .imm m1, ())) fun s1m =>
  .let_ (.mk (.sub (.bits n)) (x, .var s1m.1, ())) fun t1 =>
  .let_ (.mk (.and (.bits n)) (.var t1.1, .imm m2, ())) fun t1a =>
  .let_ (.mk (.lshr (.bits n)) (.var t1.1, .imm 2#n, ())) fun t1s =>
  .let_ (.mk (.and (.bits n)) (.var t1s.1, .imm m2, ())) fun t1b =>
  .let_ (.mk (.add (.bits n)) (.var t1a.1, .var t1b.1, ())) fun t2 =>
  .let_ (.mk (.lshr (.bits n)) (.var t2.1, .imm 4#n, ())) fun t2s =>
  .let_ (.mk (.add (.bits n)) (.var t2.1, .var t2s.1, ())) fun t2a =>
  .let_ (.mk (.and (.bits n)) (.var t2a.1, .imm m4, ())) fun t3 =>
  .let_ (.mk (.mul (.bits n)) (.var t3.1, .imm mul, ())) fun prod =>
  .let_ (.mk (.lshr (.bits n)) (.var prod.1, .imm sh, ())) fun res =>
    k (.var res.1)

/-- Branchless SWAR population count for `i32` / `i64`, supported on both x64 and Arm64. -/
@[expose] def emitPopcnt {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (w : WValTy)
    (x : Arg V w.toTy) (k : Arg V w.toTy → Expr V L rs) : Expr V L rs :=
  match w with
  | .i32 => emitPopcntCore 32
      0x55555555#32 0x33333333#32 0x0F0F0F0F#32 0x01010101#32 24#32 x k
  | .i64 => emitPopcntCore 64
      0x5555555555555555#64 0x3333333333333333#64 0x0F0F0F0F0F0F0F0F#64
      0x0101010101010101#64 56#64 x k

/-- Emit unary operation `op` on `x : Arg V w.toTy`. -/
@[expose] def emitUnOp {V : Ty → Type} {L : List Ty → Type} (retTys : List WValTy)
    (fuel : Arg V T.i64) (w : WValTy) (op : WUnOp) (x : Arg V w.toTy)
    (k : Arg V w.toTy → Expr V L (wasmRetSig retTys)) : Expr V L (wasmRetSig retTys) :=
  match w, op with
  | .i32, .clz => .let_ (.mk (.clz 32) (x, ())) fun r => k (.var r.1)
  | .i64, .clz => .let_ (.mk (.clz 64) (x, ())) fun r => k (.var r.1)
  | .i32, .ctz => .let_ (.mk (.ctz 32) (x, ())) fun r => k (.var r.1)
  | .i64, .ctz => .let_ (.mk (.ctz 64) (x, ())) fun r => k (.var r.1)
  | .i32, .popcnt => emitPopcnt .i32 x k
  | .i64, .popcnt => emitPopcnt .i64 x k
  | .i32, .extend8_s =>
    .let_ (.mk (.trunc 32 8) (x, ())) fun b =>
    .let_ (.mk (.sext 8 32) (.var b.1, ())) fun r => k (.var r.1)
  | .i64, .extend8_s =>
    .let_ (.mk (.trunc 64 8) (x, ())) fun b =>
    .let_ (.mk (.sext 8 64) (.var b.1, ())) fun r => k (.var r.1)
  | .i32, .extend16_s =>
    .let_ (.mk (.trunc 32 16) (x, ())) fun b =>
    .let_ (.mk (.sext 16 32) (.var b.1, ())) fun r => k (.var r.1)
  | .i64, .extend16_s =>
    .let_ (.mk (.trunc 64 16) (x, ())) fun b =>
    .let_ (.mk (.sext 16 64) (.var b.1, ())) fun r => k (.var r.1)
  | .i64, .extend32_s =>
    .let_ (.mk (.trunc 64 32) (x, ())) fun b =>
    .let_ (.mk (.sext 32 64) (.var b.1, ())) fun r => k (.var r.1)
  | .i32, .extend32_s => mkTrapExpr retTys 1#32 fuel

/-- Map WebAssembly relational operator to `LeanQbe.T.CmpOp`. -/
@[expose, reducible] def lowerRelOp : WRelOp → CmpOp
  | .eq => .eq
  | .ne => .ne
  | .lt_s => .slt
  | .lt_u => .ult
  | .gt_s => .sgt
  | .gt_u => .ugt
  | .le_s => .sle
  | .le_u => .ule
  | .ge_s => .sge
  | .ge_u => .uge

/-- Guarded WebAssembly integer division/remainder emitter (`div_u`, `rem_u`, `div_s`, `rem_s`). -/
@[expose] def emitDivRemCore {V : Ty → Type} {L : List Ty → Type} (retTys : List WValTy)
    (fuel : Arg V T.i64) (n : Nat) (minC neg1C : BitVec n) (signed trapOvf : Bool)
    (code : OpCode [.bits n, .bits n] [.bits n])
    (a b : Arg V (.bits n)) (k : Arg V (.bits n) → Expr V L (wasmRetSig retTys)) :
    Expr V L (wasmRetSig retTys) :=
  .let_ (.mk (.cmp .eq (.bits n)) (b, .imm 0#n, ())) fun isZ =>
  .jnz (.var isZ.1) (mkTrapExpr retTys 1#32 fuel)
    (if signed then
      .let_ (.mk (.cmp .eq (.bits n)) (a, .imm minC, ())) fun isMin =>
      .let_ (.mk (.cmp .eq (.bits n)) (b, .imm neg1C, ())) fun isNeg1 =>
      .let_ (.mk (.and .bool) (.var isMin.1, .var isNeg1.1, ())) fun isOvf =>
      .jnz (.var isOvf.1) (if trapOvf then mkTrapExpr retTys 1#32 fuel else k (.imm 0#n))
        (.let_ (.mk code (a, b, ())) fun r => k (.var r.1))
    else
      .let_ (.mk code (a, b, ())) fun r => k (.var r.1))

/-- Emit safe WebAssembly binary operation on `a, b : Arg V w.toTy`, with explicit division/
remainder trap & `INT_MIN ÷ -1` guards. -/
@[expose] def emitBinOp {V : Ty → Type} {L : List Ty → Type} (retTys : List WValTy)
    (fuel : Arg V T.i64) (w : WValTy) (op : WBinOp) (a b : Arg V w.toTy)
    (k : Arg V w.toTy → Expr V L (wasmRetSig retTys)) : Expr V L (wasmRetSig retTys) :=
  let emitPure (mkCode : (t : Ty) → OpCode [t, t] [t]) : Expr V L (wasmRetSig retTys) :=
    match w with
    | .i32 => Expr.let_ (.mk (mkCode T.i32) (a, b, ())) fun r => k (.var r.1)
    | .i64 => Expr.let_ (.mk (mkCode T.i64) (a, b, ())) fun r => k (.var r.1)
  let emitDiv (signed trapOvf : Bool) (mkCode : (n : Nat) → OpCode [.bits n, .bits n] [.bits n]) :=
    match w with
    | .i32 =>
      emitDivRemCore retTys fuel 32 0x80000000#32 0xFFFFFFFF#32 signed trapOvf (mkCode 32) a b k
    | .i64 => emitDivRemCore retTys fuel 64 0x8000000000000000#64 0xFFFFFFFFFFFFFFFF#64
        signed trapOvf (mkCode 64) a b k
  match op with
  | .add => emitPure OpCode.add
  | .sub => emitPure OpCode.sub
  | .mul => emitPure OpCode.mul
  | .and => emitPure OpCode.and
  | .or => emitPure OpCode.or
  | .xor => emitPure OpCode.xor
  | .shl => emitPure OpCode.shl
  | .shr_u => emitPure OpCode.lshr
  | .shr_s => emitPure OpCode.ashr
  | .rotl => emitPure OpCode.rotl
  | .rotr => emitPure OpCode.rotr
  | .div_u => emitDiv false false OpCode.udiv
  | .rem_u => emitDiv false false OpCode.urem
  | .div_s => emitDiv true true OpCode.sdiv
  | .rem_s => emitDiv true false OpCode.srem

/-- Extend/convert raw loaded memory cell `raw` into `resTy.toTy` (returns `trap` if invalid). -/
@[expose] def emitLoadCast {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (trap : Expr V L rs) (resTy : WValTy) (width : WMemWidth) (signed : Bool)
    (raw : V width.memTy) (k : Arg V resTy.toTy → Expr V L rs) : Expr V L rs :=
  match resTy, width, signed with
  | .i32, .w32, false => k (.var raw)
  | .i32, .w32, true => trap
  | .i64, .w64, false => k (.var raw)
  | .i64, .w64, true => trap
  | .i32, .w8, false => .let_ (.mk (.zext 8 32) (.var raw, ())) fun r => k (.var r.1)
  | .i32, .w8, true => .let_ (.mk (.sext 8 32) (.var raw, ())) fun r => k (.var r.1)
  | .i32, .w16, false => .let_ (.mk (.zext 16 32) (.var raw, ())) fun r => k (.var r.1)
  | .i32, .w16, true => .let_ (.mk (.sext 16 32) (.var raw, ())) fun r => k (.var r.1)
  | .i64, .w8, false => .let_ (.mk (.zext 8 64) (.var raw, ())) fun r => k (.var r.1)
  | .i64, .w8, true => .let_ (.mk (.sext 8 64) (.var raw, ())) fun r => k (.var r.1)
  | .i64, .w16, false => .let_ (.mk (.zext 16 64) (.var raw, ())) fun r => k (.var r.1)
  | .i64, .w16, true => .let_ (.mk (.sext 16 64) (.var raw, ())) fun r => k (.var r.1)
  | .i64, .w32, false => .let_ (.mk (.zext 32 64) (.var raw, ())) fun r => k (.var r.1)
  | .i64, .w32, true => .let_ (.mk (.sext 32 64) (.var raw, ())) fun r => k (.var r.1)
  | .i32, .w64, _ => trap

/-- Narrow `val : Arg V srcTy.toTy` to `Arg V width.memTy` for memory store. -/
@[expose] def emitStoreCast {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (trap : Expr V L rs) (srcTy : WValTy) (width : WMemWidth) (val : Arg V srcTy.toTy)
    (k : Arg V width.memTy → Expr V L rs) : Expr V L rs :=
  match srcTy, width with
  | .i32, .w32 => k val
  | .i64, .w64 => k val
  | .i32, .w8 => .let_ (.mk (.trunc 32 8) (val, ())) fun r => k (.var r.1)
  | .i32, .w16 => .let_ (.mk (.trunc 32 16) (val, ())) fun r => k (.var r.1)
  | .i64, .w8 => .let_ (.mk (.trunc 64 8) (val, ())) fun r => k (.var r.1)
  | .i64, .w16 => .let_ (.mk (.trunc 64 16) (val, ())) fun r => k (.var r.1)
  | .i64, .w32 => .let_ (.mk (.trunc 64 32) (val, ())) fun r => k (.var r.1)
  | .i32, .w64 => trap

/-- Emit switch chain for `br_table` matching `targets` against `0, 1, ...` and falling back
to `defaultTarget`. -/
@[expose] def emitBrTable {V : Ty → Type} {L : List Ty → Type} (locTys retTys : List WValTy)
    (labs : List (WLabel V L locTys)) (locs : Tup (Arg V) (locTys.map WValTy.toTy))
    (fuel : Arg V T.i64) (idx32 : Arg V T.i32) (defLbl : WLabel V L locTys)
    (brArgs : Tup (Arg V) (defLbl.argTys.map WValTy.toTy)) :
    Nat → List Nat → Expr V L (wasmRetSig retTys)
  | _, [] => .jump defLbl.lbl (fuel, tupAppend locs brArgs)
  | i, t :: ts =>
    match labs[t]? with
    | none => mkTrapExpr retTys 1#32 fuel
    | some lbl =>
      if h : lbl.argTys = defLbl.argTys then
        .let_ (.mk (.cmp .eq T.i32) (idx32, .imm (BitVec.ofNat 32 i), ())) fun isEq =>
        .jnz (.var isEq.1)
          (.jump (h ▸ lbl.lbl) (fuel, tupAppend locs brArgs))
          (emitBrTable locTys retTys labs locs fuel idx32 defLbl brArgs (i + 1) ts)
      else
        mkTrapExpr retTys 1#32 fuel

/-- Select between two identically typed stack values (`v1` if `c ≠ 0`, else `v2`). -/
@[expose, reducible] def emitSelect {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (trap : Expr V L rs) (c : Arg V T.i32) (v1 v2 : SVal V) (k : SVal V → Expr V L rs) :
    Expr V L rs :=
  match v1, v2 with
  | .i32 a, .i32 b =>
    .let_ (.mk (.cmp .ne T.i32) (c, .imm 0#32, ())) fun selB =>
    .let_ (.mk (.select T.i32) (.var selB.1, a, b, ())) fun res => k (.i32 (.var res.1))
  | .i64 a, .i64 b =>
    .let_ (.mk (.cmp .ne T.i32) (c, .imm 0#32, ())) fun selB =>
    .let_ (.mk (.select T.i64) (.var selB.1, a, b, ())) fun res => k (.i64 (.var res.1))
  | _, _ => trap

/-- Emit zero comparison `x == 0` returning `Arg V T.i32` (`0` or `1`). -/
@[expose, reducible] def emitEqz {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (w : WValTy) (x : Arg V w.toTy) (k : Arg V T.i32 → Expr V L rs) : Expr V L rs :=
  match w with
  | .i32 =>
    .let_ (.mk (.cmp .eq T.i32) (x, .imm 0#32, ())) fun b =>
    .let_ (.mk (.ofBool 32) (.var b.1, ())) fun r => k (.var r.1)
  | .i64 =>
    .let_ (.mk (.cmp .eq T.i64) (x, .imm 0#64, ())) fun b =>
    .let_ (.mk (.ofBool 32) (.var b.1, ())) fun r => k (.var r.1)

/-- Emit relational comparison `a op b` returning `Arg V T.i32` (`0` or `1`). -/
@[expose, reducible] def emitRelOp {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (w : WValTy) (op : WRelOp) (a b : Arg V w.toTy) (k : Arg V T.i32 → Expr V L rs) :
    Expr V L rs :=
  let cmp := lowerRelOp op
  match w with
  | .i32 =>
    .let_ (.mk (.cmp cmp T.i32) (a, b, ())) fun cb =>
    .let_ (.mk (.ofBool 32) (.var cb.1, ())) fun r => k (.var r.1)
  | .i64 =>
    .let_ (.mk (.cmp cmp T.i64) (a, b, ())) fun cb =>
    .let_ (.mk (.ofBool 32) (.var cb.1, ())) fun r => k (.var r.1)

/-! ## Non-Branching Instruction Emitter & Full `lowerSeq` -/

/-- Lower any single non-nested WebAssembly instruction (all instructions except `block`/`loop`/
`if_` and unconditional terminators). -/
@[expose] def lowerSimpleInstr {V : Ty → Type} {L : List Ty → Type} (ctx : WLowerCtx)
    (vmCtx fuel : Arg V T.i64) (locs : Tup (Arg V) (ctx.locTys.map WValTy.toTy))
    (stk : List (SVal V)) (labs : List (WLabel V L ctx.locTys)) (instr : WInstr)
    (k : WCont V L ctx.locTys ctx.retTys) : Expr V L (wasmRetSig ctx.retTys) :=
  let trap := mkTrapExpr ctx.retTys 1#32 fuel
  match instr with
  | .nop => k fuel locs stk
  | .br_if depth =>
    match pop32 stk, labs[depth]? with
    | some (cond, stk1), some lbl =>
      match popArgsAux lbl.argTys stk1 with
      | some (brArgs, _) =>
        .let_ (.mk (.cmp .ne T.i32) (cond, .imm 0#32, ())) fun taken =>
        .jnz (.var taken.1)
          (.jump lbl.lbl (fuel, tupAppend locs brArgs))
          (k fuel locs stk1)
      | none => trap
    | _, _ => trap
  | .call fnIdx =>
    match ctx.funcs[fnIdx]? with
    | none => trap
    | some callee =>
      match ctx.types[callee.typeIdx]? with
      | none => trap
      | some ft =>
        match popArgsAux ft.params stk with
        | none => trap
        | some (callArgs, stk1) =>
          .let_ (.mk (.cmp .eq T.i64) (fuel, .imm 0#64, ())) fun outFuel =>
          .jnz (.var outFuel.1) (mkTrapExpr ctx.retTys 2#32 fuel)
            (.let_ (.mk (.sub T.i64) (fuel, .imm 1#64, ())) fun fuel' =>
            .call callee.name (as := wasmAbiParams ft) (bs := wasmAbiResults ft)
              (vmCtx, Arg.var fuel'.1, callArgs) fun res =>
              let status : Arg V T.i32 := .var res.1
              let remFuel : Arg V T.i64 := .var res.2.1
              let retArgs := varsTup res.2.2
              .let_ (.mk (.cmp .eq T.i32) (status, .imm 0#32, ())) fun isOk =>
              .jnz (.var isOk.1)
                (k remFuel locs (pushArgsAux ft.results retArgs stk1))
                (mkStatusTrapExpr ctx.retTys status remFuel))
  | .drop =>
    match stk with
    | _ :: stk1 => k fuel locs stk1
    | [] => trap
  | .select =>
    match pop32 stk with
    | some (cond, v2 :: v1 :: stk3) =>
      emitSelect trap cond v1 v2 fun res => k fuel locs (res :: stk3)
    | _ => trap
  | .local_get idx =>
    match getLocal ctx.locTys locs idx with
    | some v => k fuel locs (v :: stk)
    | none => trap
  | .local_set idx =>
    match stk with
    | v :: stk1 =>
      match setLocal ctx.locTys locs idx v with
      | some locs' => k fuel locs' stk1
      | none => trap
    | [] => trap
  | .local_tee idx =>
    match stk with
    | v :: _ =>
      match setLocal ctx.locTys locs idx v with
      | some locs' => k fuel locs' stk
      | none => trap
    | [] => trap
  | .global_get idx =>
    match ctx.globals[idx]? with
    | some g =>
      let gv := match g.ty with
        | .i32 => SVal.i32 (.imm (BitVec.ofNat 32 g.init.toNat))
        | .i64 => SVal.i64 (.imm g.init)
      k fuel locs (gv :: stk)
    | none => trap
  | .load resTy width signed arg =>
    if ctx.hasMem && validateLoad resTy width signed then
      match pop32 stk with
      | some (idx32, stk1) =>
        emitMemBounds ctx.retTys vmCtx fuel idx32 arg width.bytes fun ptr =>
          .load width.memTy ptr fun raw =>
            emitLoadCast trap resTy width signed raw fun v =>
              k fuel locs (SVal.ofArg resTy v :: stk1)
      | none => trap
    else
      trap
  | .store srcTy width arg =>
    if ctx.hasMem && validateStore srcTy width then
      match popExpectS srcTy stk with
      | some (val, stk1) =>
        match pop32 stk1 with
        | some (idx32, stk2) =>
          emitMemBounds ctx.retTys vmCtx fuel idx32 arg width.bytes fun ptr =>
            emitStoreCast trap srcTy width val fun memVal =>
              .store memVal ptr (k fuel locs stk2)
        | none => trap
      | none => trap
    else
      trap
  | .memory_size =>
    if ctx.hasMem then
      emitMemSize vmCtx fun pages32 =>
        k fuel locs (.i32 pages32 :: stk)
    else
      trap
  | .memory_grow =>
    if ctx.hasMem then
      match pop32 stk with
      | some (delta, stk1) =>
        emitMemGrow ctx.retTys ctx.memMaxBytes vmCtx fuel delta fun fuel' res =>
          k fuel' locs (.i32 res :: stk1)
      | none => trap
    else
      trap
  | .memory_fill =>
    if ctx.hasMem then
      match pop32 stk with
      | some (n32, stk1) =>
        match pop32 stk1 with
        | some (val32, stk2) =>
          match pop32 stk2 with
          | some (dst32, stk3) =>
            emitMemFill ctx.retTys vmCtx fuel dst32 val32 n32 fun fuel' =>
              k fuel' locs stk3
          | none => trap
        | none => trap
      | none => trap
    else
      trap
  | .memory_copy =>
    if ctx.hasMem then
      match pop32 stk with
      | some (n32, stk1) =>
        match pop32 stk1 with
        | some (src32, stk2) =>
          match pop32 stk2 with
          | some (dst32, stk3) =>
            emitMemCopy ctx.retTys vmCtx fuel dst32 src32 n32 fun fuel' =>
              k fuel' locs stk3
          | none => trap
        | none => trap
      | none => trap
    else
      trap
  | .i32_const v => k fuel locs (.i32 (.imm v) :: stk)
  | .i64_const v => k fuel locs (.i64 (.imm v) :: stk)
  | .eqz w =>
    match w, stk with
    | .i32, .i32 x :: stk1 => emitEqz .i32 x fun r => k fuel locs (.i32 r :: stk1)
    | .i64, .i64 x :: stk1 => emitEqz .i64 x fun r => k fuel locs (.i32 r :: stk1)
    | _, _ => trap
  | .unop w op =>
    match popExpectS w stk with
    | some (x, stk1) =>
      emitUnOp ctx.retTys fuel w op x fun r =>
        k fuel locs (SVal.ofArg w r :: stk1)
    | none => trap
  | .binop w op =>
    match popExpectS w stk with
    | some (b, stk1) =>
      match popExpectS w stk1 with
      | some (a, stk2) =>
        emitBinOp ctx.retTys fuel w op a b fun r =>
          k fuel locs (SVal.ofArg w r :: stk2)
      | none => trap
    | none => trap
  | .relop w op =>
    match popExpectS w stk with
    | some (b, stk1) =>
      match popExpectS w stk1 with
      | some (a, stk2) =>
        emitRelOp w op a b fun r => k fuel locs (.i32 r :: stk2)
      | none => trap
    | none => trap
  | .wrap_i64 =>
    match pop64 stk with
    | some (x, stk1) =>
      .let_ (.mk (.trunc 64 32) (x, ())) fun r =>
        k fuel locs (.i32 (.var r.1) :: stk1)
    | none => trap
  | .extend_i32_s =>
    match pop32 stk with
    | some (x, stk1) =>
      .let_ (.mk (.sext 32 64) (x, ())) fun r =>
        k fuel locs (.i64 (.var r.1) :: stk1)
    | none => trap
  | .extend_i32_u =>
    match pop32 stk with
    | some (x, stk1) =>
      .let_ (.mk (.zext 32 64) (x, ())) fun r =>
        k fuel locs (.i64 (.var r.1) :: stk1)
    | none => trap
  | _ => trap

/-- Join wrapper for `block`/`loop`/`if_` structured control flow. -/
@[expose, reducible] def lowerGroupJoin {V : Ty → Type} {L : List Ty → Type} (ctx : WLowerCtx)
    (ft : WFuncTy) (stkAfter : List (SVal V))
    (body : WLabel V L ctx.locTys → WCont V L ctx.locTys ctx.retTys →
      Expr V L (wasmRetSig ctx.retTys))
    (after : WCont V L ctx.locTys ctx.retTys) : Expr V L (wasmRetSig ctx.retTys) :=
  .group (sig := [labelSig ctx.locTys ft.results])
    (fun _ =>
      .cons (fun xs =>
        let (locs', resArgs) := tupSplit (varsTup xs.2)
        after (.var xs.1) locs' (pushArgsAux ft.results resArgs stkAfter)) .nil)
    (fun (jLbl, ()) =>
      let lbl' : WLabel V L ctx.locTys := ⟨ft.results, jLbl⟩
      body lbl' fun fuelEnd locsEnd stkEnd =>
        match popArgsAux ft.results stkEnd with
        | some (resArgs, _) => .jump jLbl (fuelEnd, tupAppend locsEnd resArgs)
        | none => mkTrapExpr ctx.retTys 1#32 fuelEnd)

/-- Lower a WebAssembly instruction sequence using `Expr.group` for structured control flow
(`block`, `loop`, `if_`), trapping on invalid/out-of-bounds operations without ever emitting `.hlt`.
-/
@[expose] def lowerSeq {V : Ty → Type} {L : List Ty → Type} (ctx : WLowerCtx)
    (vmCtx fuel : Arg V T.i64) (locs : Tup (Arg V) (ctx.locTys.map WValTy.toTy))
    (stk : List (SVal V)) (labs : List (WLabel V L ctx.locTys)) :
    (instrs : List WInstr) → WCont V L ctx.locTys ctx.retTys → Expr V L (wasmRetSig ctx.retTys)
  | [], k => k fuel locs stk
  | .unreachable :: _, _ => mkTrapExpr ctx.retTys 1#32 fuel
  | .br depth :: _, _ =>
    match labs[depth]? with
    | some lbl =>
      match popArgsAux lbl.argTys stk with
      | some (brArgs, _) => .jump lbl.lbl (fuel, tupAppend locs brArgs)
      | none => mkTrapExpr ctx.retTys 1#32 fuel
    | none => mkTrapExpr ctx.retTys 1#32 fuel
  | .br_table targets defTarget :: _, _ =>
    match pop32 stk, labs[defTarget]? with
    | some (idx32, stk1), some defLbl =>
      match popArgsAux defLbl.argTys stk1 with
      | some (brArgs, _) =>
        emitBrTable ctx.locTys ctx.retTys labs locs fuel idx32 defLbl brArgs 0 targets
      | none => mkTrapExpr ctx.retTys 1#32 fuel
    | _, _ => mkTrapExpr ctx.retTys 1#32 fuel
  | .return_ :: _, _ =>
    match popArgsAux ctx.retTys stk with
    | some (retArgs, _) => .ret (.imm 0#32, fuel, retArgs)
    | none => mkTrapExpr ctx.retTys 1#32 fuel
  | .block bt body :: rest, k =>
    match bt.resolve ctx.types with
    | none => mkTrapExpr ctx.retTys 1#32 fuel
    | some ft =>
      match popArgsAux ft.params stk with
      | none => mkTrapExpr ctx.retTys 1#32 fuel
      | some (initArgs, stkAfter) =>
        lowerGroupJoin ctx ft stkAfter
          (fun lbl' fall =>
            lowerSeq ctx vmCtx fuel locs (pushArgsAux ft.params initArgs [])
              (lbl' :: labs) body fall)
          (fun fuel' locs' stk' => lowerSeq ctx vmCtx fuel' locs' stk' labs rest k)
  | .loop bt body :: rest, k =>
    match bt.resolve ctx.types with
    | none => mkTrapExpr ctx.retTys 1#32 fuel
    | some ft =>
      match popArgsAux ft.params stk with
      | none => mkTrapExpr ctx.retTys 1#32 fuel
      | some (initArgs, stkAfter) =>
        lowerGroupJoin ctx ft stkAfter
          (fun _ fall =>
            .group (sig := [labelSig ctx.locTys ft.params])
              (fun (lHdr, ()) =>
                .cons (fun xs =>
                  let fHdr : Arg V T.i64 := .var xs.1
                  let (locsHdr, loopArgs) := tupSplit (varsTup xs.2)
                  .let_ (.mk (.cmp .eq T.i64) (fHdr, .imm 0#64, ())) fun isZ =>
                  .jnz (.var isZ.1) (mkTrapExpr ctx.retTys 2#32 fHdr)
                    (.let_ (.mk (.sub T.i64) (fHdr, .imm 1#64, ())) fun fNext =>
                      let lbl' : WLabel V L ctx.locTys := ⟨ft.params, lHdr⟩
                      lowerSeq ctx vmCtx (.var fNext.1) locsHdr
                        (pushArgsAux ft.params loopArgs []) (lbl' :: labs) body fall)) .nil)
              (fun (lHdr, ()) => .jump lHdr (fuel, tupAppend locs initArgs)))
          (fun fuel' locs' stk' => lowerSeq ctx vmCtx fuel' locs' stk' labs rest k)
  | .if_ bt thenBody elseBody :: rest, k =>
    match bt.resolve ctx.types with
    | none => mkTrapExpr ctx.retTys 1#32 fuel
    | some ft =>
      match pop32 stk with
      | none => mkTrapExpr ctx.retTys 1#32 fuel
      | some (condArg, stk1) =>
        match popArgsAux ft.params stk1 with
        | none => mkTrapExpr ctx.retTys 1#32 fuel
        | some (initArgs, stkAfter) =>
          lowerGroupJoin ctx ft stkAfter
            (fun lbl' fall =>
              let brThen := lowerSeq ctx vmCtx fuel locs
                (pushArgsAux ft.params initArgs []) (lbl' :: labs) thenBody fall
              let brElse := lowerSeq ctx vmCtx fuel locs
                (pushArgsAux ft.params initArgs []) (lbl' :: labs) elseBody fall
              .let_ (.mk (.cmp .ne T.i32) (condArg, .imm 0#32, ())) fun isTrue =>
              .jnz (.var isTrue.1) brThen brElse)
            (fun fuel' locs' stk' => lowerSeq ctx vmCtx fuel' locs' stk' labs rest k)
  | i :: rest, k =>
    lowerSimpleInstr ctx vmCtx fuel locs stk labs i fun fuel' locs' stk' =>
      lowerSeq ctx vmCtx fuel' locs' stk' labs rest k
termination_by instrs _ => sizeOf instrs

/-! ## Module & Function Lowering Entry Points -/

/-- Lower a single WebAssembly function `f` in module `m` into a closed `Func`. -/
@[expose] def lowerFuncBody (m : WModule) (f : WFunc) (ft : WFuncTy) :
    Func (wasmAbiParams ft) (wasmAbiResults ft) :=
  fun V L xs =>
    let vmCtx : Arg V T.i64 := .var xs.1
    let fuel : Arg V T.i64 := .var xs.2.1
    let locs := appendZeroLocals ft.params f.locals (varsTup xs.2.2)
    let ctx : WLowerCtx :=
      { types := m.types, funcs := m.funcs, hasMem := m.memory.isSome,
        memMaxBytes := (m.memory.map WMemSpec.maxBytes).getD 0#64,
        globals := m.globals, locTys := ft.params ++ f.locals, retTys := ft.results }
    .group (sig := [labelSig ctx.locTys ft.results])
      (fun _ =>
        .cons (fun rxs =>
          let (_, resArgs) := tupSplit (varsTup rxs.2)
          .ret (.imm 0#32, .var rxs.1, resArgs)) .nil)
      (fun (jRet, ()) =>
        let retLbl : WLabel V L ctx.locTys := ⟨ft.results, jRet⟩
        lowerSeq ctx vmCtx fuel locs [] [retLbl] f.body fun fuelEnd _ stkEnd =>
          match popArgsAux ft.results stkEnd with
          | some (resArgs, _) => .ret (.imm 0#32, fuelEnd, resArgs)
          | none => mkTrapExpr ft.results 1#32 fuelEnd)

/-- Lower a `WFunc` to a named `LeanQbe.T.Fn`. -/
@[expose] def lowerFn (m : WModule) (f : WFunc) : Fn :=
  let ft := (m.types[f.typeIdx]?).getD {}
  { name := f.name
    as := wasmAbiParams ft
    rs := wasmAbiResults ft
    body := lowerFuncBody m f ft }

/-- Lower a `WModule` into a `LeanQbe.T.Module` (with zero external symbols). -/
@[expose] def lowerModule (m : WModule) : Module :=
  { fns := m.funcs.map (lowerFn m), externs := [] }

/-! ## Well-Formedness (`Wf`) Preservation -/

section WfProofs

local macro "wf_mem_if" b:term : tactic => `(tactic| (
  by_cases hm : $b; rotate_left
  · simp [hm] <;> assumption
  simp only [hm, ↓reduceIte]))

local macro "wf_pop" h:Lean.Parser.Tactic.elimTarget ","
    x:Lean.binderIdent r:Lean.binderIdent : tactic => `(tactic| (
  cases $h; · rename_i _hn; simp [_hn.1, _hn.2] <;> assumption
  rename_i _p; cases _p; rename_i _ _p; cases _p; rename_i _ _p
  cases _p; rename_i _ _p; cases _p; rename_i _ _p; cases _p; rename_i _hp1 _p
  cases _p; rename_i _hp2 _p; cases _p; rename_i $x $r; simp only [_hp1, _hp2]; (try dsimp only)))

local macro "wf_hk0" hk:ident hf:ident hlocs:ident s:term : tactic =>
  `(tactic| exact $hk (fun _ h => h) (fun _ h => h) $hf $hlocs $s)

local macro "wf_hk1" hk:ident h1:term "," hf:ident hlocs:ident s:term : tactic =>
  `(tactic| exact $hk $h1 (fun _ h => h) (ArgRel.mono $h1 $hf) (TRel_ArgRel_mono $h1 $hlocs) $s)

local macro "wasm_ret" hk:ident : tactic => `(tactic| (
  (try dsimp only [WValTy.toTy, WMemWidth.memTy, SValRel]); apply $hk
  · wasm_sub
  · wasm_arg))

theorem emitPopcntCore_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (n : Nat) (m1 m2 m4 mul sh : BitVec n)
    {x₁ : Arg V₁ (.bits n)} {x₂ : Arg V₂ (.bits n)} (hx : ArgRel G (.bits n) x₁ x₂)
    {k₁ : Arg V₁ (.bits n) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.bits n) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂,
      ArgRel G' (.bits n) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitPopcntCore n m1 m2 m4 mul sh x₁ k₁) (emitPopcntCore n m1 m2 m4 mul sh x₂ k₂) := by
  dsimp only [emitPopcntCore]; wasm_wf!; wasm_ret hk

theorem emitPopcnt_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (w : WValTy) {x₁ : Arg V₁ w.toTy} {x₂ : Arg V₂ w.toTy}
    (hx : ArgRel G w.toTy x₁ x₂)
    {k₁ : Arg V₁ w.toTy → Expr V₁ L₁ rs} {k₂ : Arg V₂ w.toTy → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' w.toTy y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitPopcnt w x₁ k₁) (emitPopcnt w x₂ k₂) := by
  cases w <;> exact emitPopcntCore_wf _ _ _ _ _ _ hx hk

theorem emitUnOp_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    (retTys : List WValTy) {f₁ : Arg V₁ T.i64} {f₂ : Arg V₂ T.i64} (hf : ArgRel G T.i64 f₁ f₂)
    (w : WValTy) (op : WUnOp) {x₁ : Arg V₁ w.toTy} {x₂ : Arg V₂ w.toTy} (hx : ArgRel G w.toTy x₁ x₂)
    {k₁ : Arg V₁ w.toTy → Expr V₁ L₁ (wasmRetSig retTys)}
    {k₂ : Arg V₂ w.toTy → Expr V₂ L₂ (wasmRetSig retTys)}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' w.toTy y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitUnOp retTys f₁ w op x₁ k₁) (emitUnOp retTys f₂ w op x₂ k₂) := by
  cases w <;> cases op <;> simp only [emitUnOp] <;>
    first | exact emitPopcnt_wf _ hx hk | (wasm_wf!; try wasm_ret hk)

theorem emitDivRemCore_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {G : Ctx V₁ V₂}
    {D : Ctx L₁ L₂} (retTys : List WValTy) {f₁ : Arg V₁ T.i64} {f₂ : Arg V₂ T.i64}
    (hf : ArgRel G T.i64 f₁ f₂) (n : Nat) (minC neg1C : BitVec n) (signed trapOvf : Bool)
    (code : OpCode [.bits n, .bits n] [.bits n]) {a₁ b₁ : Arg V₁ (.bits n)}
    {a₂ b₂ : Arg V₂ (.bits n)} (ha : ArgRel G (.bits n) a₁ a₂) (hb : ArgRel G (.bits n) b₁ b₂)
    {k₁ : Arg V₁ (.bits n) → Expr V₁ L₁ (wasmRetSig retTys)}
    {k₂ : Arg V₂ (.bits n) → Expr V₂ L₂ (wasmRetSig retTys)}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂,
      ArgRel G' (.bits n) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitDivRemCore retTys f₁ n minC neg1C signed trapOvf code a₁ b₁ k₁)
           (emitDivRemCore retTys f₂ n minC neg1C signed trapOvf code a₂ b₂ k₂) := by
  cases signed <;> cases trapOvf <;>
    simp only [emitDivRemCore, ↓reduceIte, Bool.false_eq_true] <;> wasm_wf! <;> try wasm_ret hk

theorem emitBinOp_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    (retTys : List WValTy) {f₁ : Arg V₁ T.i64} {f₂ : Arg V₂ T.i64} (hf : ArgRel G T.i64 f₁ f₂)
    (w : WValTy) (op : WBinOp) {a₁ b₁ : Arg V₁ w.toTy} {a₂ b₂ : Arg V₂ w.toTy}
    (ha : ArgRel G w.toTy a₁ a₂) (hb : ArgRel G w.toTy b₁ b₂)
    {k₁ : Arg V₁ w.toTy → Expr V₁ L₁ (wasmRetSig retTys)}
    {k₂ : Arg V₂ w.toTy → Expr V₂ L₂ (wasmRetSig retTys)}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' w.toTy y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitBinOp retTys f₁ w op a₁ b₁ k₁) (emitBinOp retTys f₂ w op a₂ b₂ k₂) := by
  cases op <;> cases w <;> simp only [emitBinOp] <;>
    first | exact emitDivRemCore_wf retTys hf _ _ _ _ _ _ ha hb hk | (wasm_wf!; wasm_ret hk)

theorem emitLoadCast_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} {G : Ctx V₁ V₂}
    {D : Ctx L₁ L₂} {t₁ : Expr V₁ L₁ rs} {t₂ : Expr V₂ L₂ rs} (ht : Wf G D t₁ t₂) (resTy : WValTy)
    (width : WMemWidth) (signed : Bool) (r₁ : V₁ width.memTy) (r₂ : V₂ width.memTy)
    (hr : ⟨width.memTy, r₁, r₂⟩ ∈ G) {k₁ : Arg V₁ resTy.toTy → Expr V₁ L₁ rs}
    {k₂ : Arg V₂ resTy.toTy → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂,
      ArgRel G' resTy.toTy y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitLoadCast t₁ resTy width signed r₁ k₁)
           (emitLoadCast t₂ resTy width signed r₂ k₂) := by
  cases resTy <;> cases width <;> cases signed <;> simp only [emitLoadCast] <;>
    first | exact ht | (wasm_wf!; wasm_ret hk)

theorem emitStoreCast_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} {G : Ctx V₁ V₂}
    {D : Ctx L₁ L₂} {t₁ : Expr V₁ L₁ rs} {t₂ : Expr V₂ L₂ rs} (ht : Wf G D t₁ t₂)
    (srcTy : WValTy) (width : WMemWidth) {v₁ : Arg V₁ srcTy.toTy} {v₂ : Arg V₂ srcTy.toTy}
    (hv : ArgRel G srcTy.toTy v₁ v₂) {k₁ : Arg V₁ width.memTy → Expr V₁ L₁ rs}
    {k₂ : Arg V₂ width.memTy → Expr V₂ L₂ rs} (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') →
      ∀ y₁ y₂, ArgRel G' width.memTy y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitStoreCast t₁ srcTy width v₁ k₁) (emitStoreCast t₂ srcTy width v₂ k₂) := by
  cases srcTy <;> cases width <;> simp only [emitStoreCast] <;>
    first | exact ht | (wasm_wf!; wasm_ret hk)

theorem emitBrTable_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {D : Ctx L₁ L₂}
    (locTys retTys : List WValTy) {labs₁ : List (WLabel V₁ L₁ locTys)}
    {labs₂ : List (WLabel V₂ L₂ locTys)} (hlabs : LabsRel D locTys labs₁ labs₂)
    {def₁ : WLabel V₁ L₁ locTys} {def₂ : WLabel V₂ L₂ locTys} (hdef : LabRel D locTys def₁ def₂)
    (har : def₁.argTys = def₂.argTys) :
    ∀ {G : Ctx V₁ V₂} {locs₁ : Tup (Arg V₁) (locTys.map WValTy.toTy)}
      {locs₂ : Tup (Arg V₂) (locTys.map WValTy.toTy)} {f₁ : Arg V₁ T.i64} {f₂ : Arg V₂ T.i64}
      {idx₁ : Arg V₁ T.i32} {idx₂ : Arg V₂ T.i32}
      {ba₁ : Tup (Arg V₁) (def₁.argTys.map WValTy.toTy)}
      {ba₂ : Tup (Arg V₂) (def₂.argTys.map WValTy.toTy)},
      TRel (ArgRel G) locs₁ locs₂ → ArgRel G T.i64 f₁ f₂ → ArgRel G T.i32 idx₁ idx₂ →
      TRel (ArgRel G) ba₁ (har ▸ ba₂) → ∀ (i : Nat) (ts : List Nat),
        Wf G D (emitBrTable locTys retTys labs₁ locs₁ f₁ idx₁ def₁ ba₁ i ts)
               (emitBrTable locTys retTys labs₂ locs₂ f₂ idx₂ def₂ ba₂ i ts) := by
  obtain ⟨hdeq, hdm⟩ := hdef; rcases def₁ with ⟨dt, dl₁⟩; rcases def₂ with ⟨dt2, dl₂⟩
  dsimp only at hdeq har hdm; subst har
  intro G locs₁ locs₂ f₁ f₂ idx₁ idx₂ ba₁ ba₂ hlocs hf hidx hba i ts
  induction ts generalizing G i with
  | nil => exact .jump hdm (.cons hf (tupAppend_rel hlocs hba))
  | cons t rest ih =>
    simp only [emitBrTable]
    rcases LabsRel_getElem?_rel hlabs t with ⟨hn1, hn2⟩ | ⟨⟨lt₁, ll₁⟩, ⟨lt₂, ll₂⟩, hs1, hs2, hl⟩
    · simp [hn1, hn2, mkTrapExpr_wf _ _ hf]
    · simp only [hs1, hs2]; rcases hl with ⟨hl_eq, hl_m⟩; dsimp only at hl_eq hl_m; subst hl_eq
      by_cases hlt : lt₁ = dt
      · simp only [hlt, ↓reduceDIte]; subst hlt
        refine wf_let2 (.cmp .eq T.i32) hidx (.imm _) fun h1 _ _ heq =>
          .jnz heq (.jump hl_m (.cons (ArgRel.mono h1 hf)
            (tupAppend_rel (TRel_ArgRel_mono h1 hlocs) (TRel_ArgRel_mono h1 hba))))
            (ih (TRel_ArgRel_mono h1 hlocs) (ArgRel.mono h1 hf) (ArgRel.mono h1 hidx)
              (TRel_ArgRel_mono h1 hba) (i + 1))
      · simp only [hlt, ↓reduceDIte]; exact mkTrapExpr_wf _ _ hf

theorem emitSelect_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} {G : Ctx V₁ V₂}
    {D : Ctx L₁ L₂} {t₁ : Expr V₁ L₁ rs} {t₂ : Expr V₂ L₂ rs} (ht : Wf G D t₁ t₂)
    {c₁ : Arg V₁ T.i32} {c₂ : Arg V₂ T.i32} (hc : ArgRel G T.i32 c₁ c₂)
    {v₁₁ v₂₁ : SVal V₁} {v₁₂ v₂₂ : SVal V₂} (hv₁ : SValRel G v₁₁ v₁₂) (hv₂ : SValRel G v₂₁ v₂₂)
    {k₁ : SVal V₁ → Expr V₁ L₁ rs} {k₂ : SVal V₂ → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, SValRel G' y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitSelect t₁ c₁ v₁₁ v₂₁ k₁) (emitSelect t₂ c₂ v₁₂ v₂₂ k₂) := by
  cases v₁₁ <;> cases v₁₂ <;> cases v₂₁ <;> cases v₂₂ <;>
    simp only [SValRel, emitSelect] at hv₁ hv₂ ⊢ <;>
    first | contradiction | exact ht | (wasm_wf!; wasm_ret hk)

theorem emitEqz_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} {G : Ctx V₁ V₂}
    {D : Ctx L₁ L₂} (w : WValTy) {x₁ : Arg V₁ w.toTy} {x₂ : Arg V₂ w.toTy}
    (hx : ArgRel G w.toTy x₁ x₂) {k₁ : Arg V₁ T.i32 → Expr V₁ L₁ rs}
    {k₂ : Arg V₂ T.i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' T.i32 y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitEqz w x₁ k₁) (emitEqz w x₂ k₂) := by
  cases w <;> dsimp only [emitEqz] <;> wasm_wf! <;> wasm_ret hk

theorem emitRelOp_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} {G : Ctx V₁ V₂}
    {D : Ctx L₁ L₂} (w : WValTy) (op : WRelOp) {a₁ b₁ : Arg V₁ w.toTy} {a₂ b₂ : Arg V₂ w.toTy}
    (ha : ArgRel G w.toTy a₁ a₂) (hb : ArgRel G w.toTy b₁ b₂)
    {k₁ : Arg V₁ T.i32 → Expr V₁ L₁ rs} {k₂ : Arg V₂ T.i32 → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' T.i32 y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitRelOp w op a₁ b₁ k₁) (emitRelOp w op a₂ b₂ k₂) := by
  cases w <;> dsimp only [emitRelOp] <;> wasm_wf! <;> wasm_ret hk

local macro "wf_ofArg" hk:ident h:ident "," w:term "," y:ident "," r:ident "," hf:ident
    hlocs:ident : tactic =>
  `(tactic| wf_hk1 $hk $h, $hf $hlocs (.cons (SValRel.ofArg $w $y) (StkRel.mono $h $r)))

theorem lowerSimpleInstr_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} (ctx : WLowerCtx)
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {vc₁ f₁ : Arg V₁ T.i64} {vc₂ f₂ : Arg V₂ T.i64}
    {locs₁ : Tup (Arg V₁) (ctx.locTys.map WValTy.toTy)}
    {locs₂ : Tup (Arg V₂) (ctx.locTys.map WValTy.toTy)}
    {stk₁ : List (SVal V₁)} {stk₂ : List (SVal V₂)}
    {labs₁ : List (WLabel V₁ L₁ ctx.locTys)} {labs₂ : List (WLabel V₂ L₂ ctx.locTys)}
    (instr : WInstr) {k₁ : WCont V₁ L₁ ctx.locTys ctx.retTys}
    {k₂ : WCont V₂ L₂ ctx.locTys ctx.retTys}
    (hvc : ArgRel G T.i64 vc₁ vc₂) (hf : ArgRel G T.i64 f₁ f₂)
    (hlocs : TRel (ArgRel G) locs₁ locs₂) (hstk : StkRel G stk₁ stk₂)
    (hlabs : LabsRel D ctx.locTys labs₁ labs₂) (hk : ContWf ctx.locTys ctx.retTys G D k₁ k₂) :
    Wf G D (lowerSimpleInstr ctx vc₁ f₁ locs₁ stk₁ labs₁ instr k₁)
           (lowerSimpleInstr ctx vc₂ f₂ locs₂ stk₂ labs₂ instr k₂) := by
  have htrap : Wf G D (mkTrapExpr (L := L₁) ctx.retTys 1#32 f₁)
      (mkTrapExpr (L := L₂) ctx.retTys 1#32 f₂) := mkTrapExpr_wf ctx.retTys 1#32 hf
  cases instr <;> simp only [lowerSimpleInstr] <;> try exact htrap
  case nop => wf_hk0 hk hf hlocs hstk
  case br_if depth =>
    rcases pop32_rel hstk with ⟨hn1, hn2⟩ | ⟨c₁, c₂, r₁, r₂, hp1, hp2, hc, hr⟩
    · simp [hn1, hn2, htrap]
    · simp only [hp1, hp2]; rcases LabsRel_getElem?_rel hlabs depth with
        ⟨hn1, hn2⟩ | ⟨⟨lt₁, ll₁⟩, ⟨lt₂, ll₂⟩, hs1, hs2, hl⟩
      · simp [hn1, hn2, htrap]
      · simp only [hs1, hs2]; rcases hl with ⟨har, hm⟩; dsimp only at har hm; subst har
        wf_pop (popArgsAux_rel lt₁ hr), hb s_
        exact wf_let2 (.cmp .ne T.i32) hc (.imm _) fun h1 _ _ htk =>
          .jnz htk (.jump hm (.cons (ArgRel.mono h1 hf)
            (tupAppend_rel (TRel_ArgRel_mono h1 hlocs) (TRel_ArgRel_mono h1 hb))))
            (by wf_hk1 hk h1, hf hlocs (StkRel.mono h1 hr))
  case call fnIdx =>
    cases hcal : ctx.funcs[fnIdx]? with | none => exact htrap | some callee =>
    dsimp only; cases hft : ctx.types[callee.typeIdx]? with | none => exact htrap | some ft =>
    dsimp only; wf_pop (popArgsAux_rel ft.params hstk), ha hs; wasm_wf!
    refine .call callee.name (.cons (by wasm_arg) (.cons (by wasm_arg)
      (TRel_ArgRel_mono (by wasm_sub) ha))) fun ⟨st₁, rf₁, rets₁⟩ ⟨st₂, rf₂, rets₂⟩ => ?_
    wasm_wf!
    · exact hk (by wasm_sub) (fun _ h => h) (by wasm_arg) (TRel_ArgRel_mono (by wasm_sub) hlocs)
        (pushArgsAux_rel ft.results (TRel_ArgRel_mono (fun _ hp => by
          try dsimp only [wasmAbiResults, Tup.zip] at hp ⊢
          wasm_mem) varsTup_rel_nil) (StkRel.mono (by wasm_sub) hs))
    · exact .ret (.cons (by wasm_arg) (.cons (by wasm_arg) (zeroArgs_rel _ ctx.retTys)))
  case drop => cases hstk with | nil => exact htrap | cons _ hr => wf_hk0 hk hf hlocs hr
  case select =>
    rcases pop32_rel hstk with ⟨hn1, hn2⟩ | ⟨c₁, c₂, r₁, r₂, hp1, hp2, hc, hr⟩
    · simp [hn1, hn2, htrap]
    · simp only [hp1, hp2]
      rcases popAny_rel hr with ⟨rfl, rfl⟩ | ⟨v₂₁, v₂₂, _, _, rfl, rfl, hv₂, hr₂⟩
      · exact htrap
      · rcases popAny_rel hr₂ with ⟨rfl, rfl⟩ | ⟨v₁₁, v₁₂, _, _, rfl, rfl, hv₁, hr₃⟩
        · cases v₂₁ <;> cases v₂₂ <;> exact htrap
        · exact emitSelect_wf htrap hc hv₁ hv₂ fun h _ _ y => by
            wf_hk1 hk h, hf hlocs (.cons y (StkRel.mono h hr₃))
  case local_get idx =>
    rcases getLocal_rel ctx.locTys idx hlocs with ⟨hn1, hn2⟩ | ⟨_, _, hs1, hs2, hv⟩
    · simp [hn1, hn2, htrap]
    · simp only [hs1, hs2]; wf_hk0 hk hf hlocs (.cons hv hstk)
  case local_set idx =>
    cases hstk with | nil => exact htrap | cons hv hrest =>
    rcases setLocal_rel ctx.locTys idx hlocs hv with ⟨hn1, hn2⟩ | ⟨_, _, hs1, hs2, hl'⟩
    · simp [hn1, hn2, htrap]
    · simp only [hs1, hs2]; wf_hk0 hk hf hl' hrest
  case local_tee idx =>
    cases hstk with | nil => exact htrap | cons hv hrest =>
    rcases setLocal_rel ctx.locTys idx hlocs hv with ⟨hn1, hn2⟩ | ⟨_, _, hs1, hs2, hl'⟩
    · simp [hn1, hn2, htrap]
    · simp only [hs1, hs2]; wf_hk0 hk hf hl' (.cons hv hrest)
  case global_get idx =>
    cases ctx.globals[idx]? with | none => exact htrap | some g =>
      wf_hk0 hk hf hlocs (.cons (by cases g.ty <;> exact .imm _) hstk)
  case load resTy width signed arg =>
    wf_mem_if (ctx.hasMem && validateLoad resTy width signed) = true; wf_pop (pop32_rel hstk), hi hr
    refine emitMemBounds_wf ctx.retTys hvc hf hi arg width.bytes fun h1 _ _ hp =>
      .load width.memTy hp fun raw₁ raw₂ =>
        emitLoadCast_wf (mkTrapExpr_wf _ 1#32 (ArgRel.mono (fun _ h => .tail _ (h1 _ h)) hf))
          resTy width signed raw₁ raw₂ List.mem_cons_self fun h2 _ _ hy => by
          have h12 := fun q hq => h2 q (.tail _ (h1 q hq)); wf_ofArg hk h12, resTy, hy, hr, hf hlocs
  case store srcTy width arg =>
    wf_mem_if (ctx.hasMem && validateStore srcTy width) = true
    wf_pop (popExpectS_rel srcTy hstk), hv hs; wf_pop (pop32_rel hs), hi hr
    refine emitMemBounds_wf ctx.retTys hvc hf hi arg width.bytes fun h1 _ _ hp =>
      emitStoreCast_wf (mkTrapExpr_wf _ 1#32 (ArgRel.mono h1 hf)) srcTy width (ArgRel.mono h1 hv)
        fun h2 _ _ hmv =>
          have h12 := fun q hq => h2 q (h1 q hq)
          .store hmv (ArgRel.mono h2 hp) (by wf_hk1 hk h12, hf hlocs (StkRel.mono h12 hr))
  case memory_size =>
    wf_mem_if ctx.hasMem = true
    exact emitMemSize_wf hvc fun h _ _ y => by wf_ofArg hk h, .i32, y, hstk, hf hlocs
  case memory_grow =>
    wf_mem_if ctx.hasMem = true; wf_pop (pop32_rel hstk), hd hr
    exact emitMemGrow_wf ctx.retTys ctx.memMaxBytes hvc hf hd fun h1 hD1 _ _ _ _ hf' hrs =>
      hk h1 hD1 hf' (TRel_ArgRel_mono h1 hlocs) (.cons (SValRel.ofArg .i32 hrs) (StkRel.mono h1 hr))
  case memory_fill =>
    wf_mem_if ctx.hasMem = true
    wf_pop (pop32_rel hstk), hn hs1; wf_pop (pop32_rel hs1), hv hs2; wf_pop (pop32_rel hs2), hd hr
    exact emitMemFill_wf ctx.retTys hvc hf hd hv hn fun h1 hD1 _ _ hf' =>
      hk h1 hD1 hf' (TRel_ArgRel_mono h1 hlocs) (StkRel.mono h1 hr)
  case memory_copy =>
    wf_mem_if ctx.hasMem = true
    wf_pop (pop32_rel hstk), hn hs1; wf_pop (pop32_rel hs1), hs hs2; wf_pop (pop32_rel hs2), hd hr
    exact emitMemCopy_wf ctx.retTys hvc hf hd hs hn fun h1 hD1 _ _ hf' =>
      hk h1 hD1 hf' (TRel_ArgRel_mono h1 hlocs) (StkRel.mono h1 hr)
  case i32_const _ | i64_const _ => wf_hk0 hk hf hlocs (.cons (.imm _) hstk)
  case eqz w =>
    rcases popAny_rel hstk with ⟨rfl, rfl⟩ | ⟨x₁, x₂, _, _, rfl, rfl, hv, hrest⟩
    · cases w <;> exact htrap
    · cases w <;> cases x₁ <;> cases x₂ <;> simp only [SValRel] at hv <;> first
      | exact htrap
      | exact emitEqz_wf _ hv fun h _ _ y => by wf_ofArg hk h, .i32, y, hrest, hf hlocs
  case unop w op =>
    wf_pop (popExpectS_rel w hstk), hx hr
    exact emitUnOp_wf ctx.retTys hf w op hx fun h _ _ y => by wf_ofArg hk h, w, y, hr, hf hlocs
  case binop w op =>
    wf_pop (popExpectS_rel w hstk), hb hs; wf_pop (popExpectS_rel w hs), ha hr
    exact emitBinOp_wf ctx.retTys hf w op ha hb fun h _ _ y => by wf_ofArg hk h, w, y, hr, hf hlocs
  case relop w op =>
    wf_pop (popExpectS_rel w hstk), hb hs; wf_pop (popExpectS_rel w hs), ha hr
    exact emitRelOp_wf w op ha hb fun h _ _ y => by wf_ofArg hk h, .i32, y, hr, hf hlocs
  case wrap_i64 =>
    wf_pop (pop64_rel hstk), hx hr
    exact wf_let1 (.trunc 64 32) hx fun h _ _ y => by wf_ofArg hk h, .i32, y, hr, hf hlocs
  case extend_i32_s | extend_i32_u =>
    wf_pop (pop32_rel hstk), hx hr
    exact wf_let1 _ hx fun h _ _ y => by wf_ofArg hk h, .i64, y, hr, hf hlocs

theorem lowerGroupJoin_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} (ctx : WLowerCtx)
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (ft : WFuncTy) {sa₁ : List (SVal V₁)} {sa₂ : List (SVal V₂)}
    (hsa : StkRel G sa₁ sa₂)
    {body₁ : WLabel V₁ L₁ ctx.locTys → WCont V₁ L₁ ctx.locTys ctx.retTys →
      Expr V₁ L₁ (wasmRetSig ctx.retTys)}
    {body₂ : WLabel V₂ L₂ ctx.locTys → WCont V₂ L₂ ctx.locTys ctx.retTys →
      Expr V₂ L₂ (wasmRetSig ctx.retTys)}
    {after₁ : WCont V₁ L₁ ctx.locTys ctx.retTys} {after₂ : WCont V₂ L₂ ctx.locTys ctx.retTys}
    (hafter : ContWf ctx.locTys ctx.retTys G D after₁ after₂)
    (hbody : ∀ (j₁ : L₁ (labelSig ctx.locTys ft.results)) (j₂ : L₂ (labelSig ctx.locTys ft.results))
      (fall₁ : WCont V₁ L₁ ctx.locTys ctx.retTys) (fall₂ : WCont V₂ L₂ ctx.locTys ctx.retTys),
      let D' := Tup.zip (as := [labelSig ctx.locTys ft.results]) (j₁, ()) (j₂, ()) ++ D
      (∀ p ∈ D, p ∈ D') → (⟨labelSig ctx.locTys ft.results, j₁, j₂⟩ ∈ D') →
      ContWf ctx.locTys ctx.retTys G D' fall₁ fall₂ →
      Wf G D' (body₁ ⟨ft.results, j₁⟩ fall₁) (body₂ ⟨ft.results, j₂⟩ fall₂)) :
    Wf G D (lowerGroupJoin ctx ft sa₁ body₁ after₁) (lowerGroupJoin ctx ft sa₂ body₂ after₂) :=
  .group (sig := [labelSig ctx.locTys ft.results])
    (fun ⟨j₁, ()⟩ ⟨j₂, ()⟩ => .cons (fun ⟨fx₁, xlocs₁⟩ ⟨fx₂, xlocs₂⟩ => by
      let Gb := Tup.zip (as := labelSig ctx.locTys ft.results) (fx₁, xlocs₁) (fx₂, xlocs₂) ++ G
      have hsp := tupSplit_rel (G := Gb) (TRel_ArgRel_mono (by wasm_sub) varsTup_rel_nil)
      exact hafter (by wasm_sub) (by wasm_sub) (.var (by wasm_mem)) hsp.1
        (pushArgsAux_rel ft.results hsp.2 (StkRel.mono (by wasm_sub) hsa))) .nil)
    fun ⟨j₁, ()⟩ ⟨j₂, ()⟩ => hbody j₁ j₂ _ _ (by wasm_sub) (by wasm_mem)
      fun {_ D''} _ hDD'' {_ _ _ _ _ _} hfe hle hse => by
        have htrap := mkTrapExpr_wf (L₁ := L₁) (L₂ := L₂) (D := D'') ctx.retTys 1#32 hfe
        wf_pop (popArgsAux_rel ft.results hse), hra s_
        exact .jump (hDD'' _ (by wasm_mem)) (.cons hfe (tupAppend_rel hle hra))

theorem lowerSeq_wf_aux (ctx : WLowerCtx) :
    ∀ (sz : Nat) {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {vc₁ f₁ : Arg V₁ T.i64} {vc₂ f₂ : Arg V₂ T.i64}
      {locs₁ : Tup (Arg V₁) (ctx.locTys.map WValTy.toTy)}
      {locs₂ : Tup (Arg V₂) (ctx.locTys.map WValTy.toTy)}
      {stk₁ : List (SVal V₁)} {stk₂ : List (SVal V₂)}
      {labs₁ : List (WLabel V₁ L₁ ctx.locTys)} {labs₂ : List (WLabel V₂ L₂ ctx.locTys)}
      (instrs : List WInstr) (_hsz : sizeOf instrs ≤ sz)
      {k₁ : WCont V₁ L₁ ctx.locTys ctx.retTys} {k₂ : WCont V₂ L₂ ctx.locTys ctx.retTys},
      ArgRel G T.i64 vc₁ vc₂ → ArgRel G T.i64 f₁ f₂ → TRel (ArgRel G) locs₁ locs₂ →
      StkRel G stk₁ stk₂ → LabsRel D ctx.locTys labs₁ labs₂ →
      ContWf ctx.locTys ctx.retTys G D k₁ k₂ →
      Wf G D (lowerSeq ctx vc₁ f₁ locs₁ stk₁ labs₁ instrs k₁)
             (lowerSeq ctx vc₂ f₂ locs₂ stk₂ labs₂ instrs k₂) := by
  intro sz; induction sz using Nat.strongRecOn with | _ sz ih =>
  intro V₁ V₂ L₁ L₂ G D vc₁ f₁ vc₂ f₂ locs₁ locs₂ stk₁ stk₂ labs₁ labs₂
    instrs hsz k₁ k₂ hvc hf hlocs hstk hlabs hk
  cases instrs with
  | nil => simp only [lowerSeq]; wf_hk0 hk hf hlocs hstk
  | cons i rest =>
    have hlt {b : List WInstr} (h : sizeOf b < sizeOf (i :: rest)) : sizeOf b < sz :=
      Nat.lt_of_lt_of_le h hsz
    have htrap := mkTrapExpr_wf (L₁ := L₁) (L₂ := L₂) (D := D) ctx.retTys 1#32 hf
    let hafter : ContWf ctx.locTys ctx.retTys G D
        (fun f' l' s' => lowerSeq ctx vc₁ f' l' s' labs₁ rest k₁)
        (fun f' l' s' => lowerSeq ctx vc₂ f' l' s' labs₂ rest k₂) :=
      fun {_ _} hGG' hDD' {_ _ _ _ _ _} hf' hl' hs' =>
        ih _ (hlt (by simp +arith)) rest (Nat.le_refl _) (ArgRel.mono hGG' hvc)
          hf' hl' hs' (LabsRel.mono hDD' hlabs) (hk.mono hGG' hDD')
    cases i with
    | unreachable => simp only [lowerSeq]; exact htrap
    | br depth =>
      simp only [lowerSeq]
      rcases LabsRel_getElem?_rel hlabs depth with
        ⟨hn1, hn2⟩ | ⟨⟨lt₁, ll₁⟩, ⟨lt₂, ll₂⟩, hs1, hs2, hl⟩
      · simp [hn1, hn2, htrap]
      · simp only [hs1, hs2]; rcases hl with ⟨har, hm⟩; dsimp only at har hm; subst har
        wf_pop (popArgsAux_rel lt₁ hstk), hb s_; exact .jump hm (.cons hf (tupAppend_rel hlocs hb))
    | br_table targets defTarget =>
      simp only [lowerSeq]; wf_pop (pop32_rel hstk), hi hr
      rcases LabsRel_getElem?_rel hlabs defTarget with
        ⟨hn1, hn2⟩ | ⟨⟨dt₁, dl₁⟩, ⟨dt₂, dl₂⟩, hs1, hs2, hdef⟩
      · simp [hn1, hn2, htrap]
      · simp only [hs1, hs2]; have hdeq : dt₁ = dt₂ := hdef.1; subst hdeq
        wf_pop (popArgsAux_rel dt₁ hr), hb s_
        exact emitBrTable_wf ctx.locTys ctx.retTys hlabs hdef rfl hlocs hf hi hb 0 targets
    | return_ =>
      simp only [lowerSeq]; wf_pop (popArgsAux_rel ctx.retTys hstk), hr s_
      exact .ret (.cons (.imm _) (.cons hf hr))
    | block bt body =>
      simp only [lowerSeq]; cases bt.resolve ctx.types with | none => exact htrap | some ft =>
      dsimp only; wf_pop (popArgsAux_rel ft.params hstk), hia hsa
      exact lowerGroupJoin_wf ctx ft hsa hafter fun j₁ j₂ _ _ hDD' hj hfall =>
        ih _ (hlt (by simp +arith)) body (Nat.le_refl _) hvc hf hlocs
          (pushArgsAux_rel ft.params hia .nil) (.cons ⟨rfl, hj⟩ (LabsRel.mono hDD' hlabs)) hfall
    | loop bt body =>
      simp only [lowerSeq]; cases bt.resolve ctx.types with | none => exact htrap | some ft =>
      dsimp only; wf_pop (popArgsAux_rel ft.params hstk), hia hsa
      refine lowerGroupJoin_wf ctx ft hsa hafter fun j₁ j₂ _ _ hDD₁ _ hfall =>
        .group (sig := [labelSig ctx.locTys ft.params])
          (fun ⟨lh₁, ()⟩ ⟨lh₂, ()⟩ => .cons (fun ⟨fh₁, xlocs₁⟩ ⟨fh₂, xlocs₂⟩ => by
            let G₁ :=
              Tup.zip (as := labelSig ctx.locTys ft.params) (fh₁, xlocs₁) (fh₂, xlocs₂) ++ G
            have hsp := tupSplit_rel (G := G₁) (TRel_ArgRel_mono (by wasm_sub) varsTup_rel_nil)
            wasm_wf!
            exact ih _ (hlt (by simp +arith)) body (Nat.le_refl _) (by wasm_arg) (by wasm_arg)
              (TRel_ArgRel_mono (by wasm_sub) hsp.1)
              (pushArgsAux_rel ft.params (TRel_ArgRel_mono (by wasm_sub) hsp.2) .nil)
              (.cons ⟨rfl, List.mem_append_left _ List.mem_cons_self⟩
                (LabsRel.mono (fun _ hp => List.mem_append_right _ (hDD₁ _ hp)) hlabs))
              (hfall.mono (by wasm_sub) (by wasm_sub))) .nil)
          fun _ _ => .jump (by wasm_mem) (.cons hf (tupAppend_rel hlocs hia))
    | if_ bt thenBody elseBody =>
      simp only [lowerSeq]; cases bt.resolve ctx.types with | none => exact htrap | some ft =>
      dsimp only; wf_pop (pop32_rel hstk), hc hr; wf_pop (popArgsAux_rel ft.params hr), hia hsa
      refine lowerGroupJoin_wf ctx ft hsa hafter fun j₁ j₂ _ _ hDD' hj hfall => by
        have hlabs' : LabsRel _ ctx.locTys (⟨ft.results, j₁⟩ :: labs₁)
            (⟨ft.results, j₂⟩ :: labs₂) := .cons ⟨rfl, hj⟩ (LabsRel.mono hDD' hlabs)
        wasm_wf! <;> exact ih _ (hlt (by simp +arith)) _ (Nat.le_refl _) (by wasm_arg)
          (by wasm_arg) (TRel_ArgRel_mono (by wasm_sub) hlocs)
          (pushArgsAux_rel ft.params (TRel_ArgRel_mono (by wasm_sub) hia) .nil) hlabs'
          (hfall.mono (by wasm_sub) fun _ hp => hp)
    | _ => simp only [lowerSeq]; exact lowerSimpleInstr_wf ctx _ hvc hf hlocs hstk hlabs hafter

theorem lowerFuncBody_wf (m : WModule) (f : WFunc) (ft : WFuncTy) :
    (lowerFuncBody m f ft).Wf := fun _ _ _ _ ⟨vc₁, f₁, ps₁⟩ ⟨vc₂, f₂, ps₂⟩ => by
  simp only [lowerFuncBody]
  let ctx : WLowerCtx :=
    { types := m.types, funcs := m.funcs, hasMem := m.memory.isSome,
      memMaxBytes := (m.memory.map WMemSpec.maxBytes).getD 0#64,
      globals := m.globals, locTys := ft.params ++ f.locals, retTys := ft.results }
  let G₀ := Tup.zip (as := wasmAbiParams ft) (vc₁, f₁, ps₁) (vc₂, f₂, ps₂)
  refine .group (sig := [labelSig ctx.locTys ft.results])
    (fun ⟨j₁, ()⟩ ⟨j₂, ()⟩ => .cons (fun ⟨rf₁, rlocs₁⟩ ⟨rf₂, rlocs₂⟩ => by
      let Gr := Tup.zip (as := labelSig ctx.locTys ft.results) (rf₁, rlocs₁) (rf₂, rlocs₂) ++ G₀
      have hsp := tupSplit_rel (G := Gr) (as := ctx.locTys.map WValTy.toTy)
        (bs := ft.results.map WValTy.toTy) (TRel_ArgRel_mono (by wasm_sub) varsTup_rel_nil)
      exact .ret (.cons (.imm _) (.cons (.var (by wasm_mem)) hsp.2))) .nil)
    fun ⟨j₁, ()⟩ ⟨j₂, ()⟩ => lowerSeq_wf_aux ctx (sizeOf f.body) f.body (Nat.le_refl _)
      (.var (by wasm_mem)) (.var (by wasm_mem))
      (appendZeroLocals_rel ft.params f.locals (TRel_ArgRel_mono (by wasm_sub) varsTup_rel_nil))
      .nil (.cons ⟨rfl, List.mem_cons_self⟩ .nil) fun {_ D'} _ _ {_ _ _ _ _ _} hfe _ hse => by
        have htrap := mkTrapExpr_wf (L₁ := _) (L₂ := _) (D := D') ft.results 1#32 hfe
        wf_pop (popArgsAux_rel ft.results hse), hra s_; exact .ret (.cons (.imm _) (.cons hfe hra))

/-- Universal well-formedness: every lowered function in `lowerModule m` satisfies `Fn.Wf`. -/
theorem lowerModule_wf (m : WModule) : ∀ fn ∈ (lowerModule m).fns, fn.Wf := fun _ hmem => by
  rcases List.mem_map.mp hmem with ⟨f, _, rfl⟩; exact lowerFuncBody_wf m f _

/-- Lowered function names are pairwise distinct whenever `validateModule m = true`. -/
theorem lowerModule_namesNodup {m : WModule} (hv : validateModule m = true) :
    (lowerModule m).namesNodup := by
  simpa [Module.namesNodup, Module.names, lowerModule, Function.comp_def, lowerFn] using
    (validateModule_elim hv).1

end WfProofs

/-! ## Target-Independent Supportability (`supportsSource`) & Signature Legality -/

section SupportsSourceProofs

local macro "ss_mem_if" b:term : tactic => `(tactic| (
  by_cases hm : $b
  rotate_left
  · simp only [hm, Bool.false_eq_true, ↓reduceIte]
    exact mkTrapExpr_ss (by assumption) _ _ _ _ _
  simp only [hm, ↓reduceIte]))

local macro "ss_pop" e:Lean.Parser.Tactic.elimTarget ","
    x:Lean.binderIdent r:Lean.binderIdent : tactic => `(tactic| (
  cases $e
  · exact mkTrapExpr_ss (by assumption) _ _ _ _ _
  rename_i _p; cases _p; rename_i $x $r; try dsimp only))

theorem emitPopcntCore_ss {lt : LegalTarget} (hv : lt.valid = true) {rs : List Ty} (n : Nat)
    (hn : n ≤ 64) (m1 m2 m4 mul sh : BitVec n) (x : Arg K (.bits n))
    (k : Arg K (.bits n) → Expr K KL rs)
    (hk : ∀ y nv' nl', (toTFlat (k y) nv' nl').supportsSource lt = true) (nv nl : Nat) :
    (toTFlat (emitPopcntCore n m1 m2 m4 mul sh x k) nv nl).supportsSource lt = true := by
  simp only [emitPopcntCore]; tflat_builder_ss! hv

theorem emitPopcnt_ss {lt : LegalTarget} (hv : lt.valid = true) {rs : List Ty} (w : WValTy)
    (x : Arg K w.toTy) (k : Arg K w.toTy → Expr K KL rs)
    (hk : ∀ y nv' nl', (toTFlat (k y) nv' nl').supportsSource lt = true) :
    ∀ nv nl, (toTFlat (emitPopcnt w x k) nv nl).supportsSource lt = true := by
  cases w <;> exact emitPopcntCore_ss hv _ (by omega) _ _ _ _ _ x k hk

theorem emitUnOp_ss {lt : LegalTarget} (hv : lt.valid = true) (retTys : List WValTy)
    (f : Arg K T.i64) (w : WValTy) (op : WUnOp) (x : Arg K w.toTy)
    (k : Arg K w.toTy → Expr K KL (wasmRetSig retTys))
    (hk : ∀ y nv' nl', (toTFlat (k y) nv' nl').supportsSource lt = true) (nv nl : Nat) :
    (toTFlat (emitUnOp retTys f w op x k) nv nl).supportsSource lt = true := by
  cases w <;> cases op <;> simp only [emitUnOp] <;>
    first | exact emitPopcnt_ss hv _ x k hk nv nl | tflat_builder_ss! hv

theorem emitDivRemCore_ss {lt : LegalTarget} (hv : lt.valid = true) (retTys : List WValTy)
    (f : Arg K T.i64) (n : Nat) (hn : n ≤ 64) (minC neg1C : BitVec n) (signed trapOvf : Bool)
    (code : OpCode [.bits n, .bits n] [.bits n]) (hop : lt.supportsOpCode code = true)
    (a b : Arg K (.bits n)) (k : Arg K (.bits n) → Expr K KL (wasmRetSig retTys))
    (hk : ∀ y nv' nl', (toTFlat (k y) nv' nl').supportsSource lt = true) (nv nl : Nat) :
    (toTFlat (emitDivRemCore retTys f n minC neg1C signed trapOvf code a b k)
      nv nl).supportsSource lt = true := by
  cases signed <;> cases trapOvf <;> simp only [emitDivRemCore, ↓reduceIte, Bool.false_eq_true] <;>
    repeat (first
      | exact hk _ _ _ | exact mkTrapExpr_ss hv retTys 1#32 f _ _
      | refine tflat_let2_ss lt _ _ _ (by first | exact hop | tflat_op_ss hv) ?_
      | refine tflat_jnz_ss lt _ ?_ ?_)

theorem emitBinOp_ss {lt : LegalTarget} (hv : lt.valid = true) (retTys : List WValTy)
    (f : Arg K T.i64) (w : WValTy) (op : WBinOp) (a b : Arg K w.toTy)
    (k : Arg K w.toTy → Expr K KL (wasmRetSig retTys))
    (hk : ∀ y nv' nl', (toTFlat (k y) nv' nl').supportsSource lt = true) (nv nl : Nat) :
    (toTFlat (emitBinOp retTys f w op a b k) nv nl).supportsSource lt = true := by
  cases op <;> cases w <;> simp only [emitBinOp] <;> first
  | (refine emitDivRemCore_ss hv retTys f _ (by omega) _ _ _ _ _ ?_ a b k hk nv nl; tflat_op_ss hv)
  | tflat_builder_ss! hv

theorem emitLoadCast_ss {lt : LegalTarget} (hv : lt.valid = true) {rs : List Ty}
    {trap : Expr K KL rs} (htrap : ∀ nv nl, (toTFlat trap nv nl).supportsSource lt = true)
    (resTy : WValTy) (width : WMemWidth) (signed : Bool) (raw : K width.memTy)
    (k : Arg K resTy.toTy → Expr K KL rs)
    (hk : ∀ y nv' nl', (toTFlat (k y) nv' nl').supportsSource lt = true) (nv nl : Nat) :
    (toTFlat (emitLoadCast trap resTy width signed raw k) nv nl).supportsSource lt = true := by
  cases resTy <;> cases width <;> cases signed <;>
    first | exact htrap nv nl | exact hk _ nv nl | tflat_builder_ss! hv

theorem emitStoreCast_ss {lt : LegalTarget} (hv : lt.valid = true) {rs : List Ty}
    {trap : Expr K KL rs} (htrap : ∀ nv nl, (toTFlat trap nv nl).supportsSource lt = true)
    (srcTy : WValTy) (width : WMemWidth) (v : Arg K srcTy.toTy)
    (k : Arg K width.memTy → Expr K KL rs)
    (hk : ∀ y nv' nl', (toTFlat (k y) nv' nl').supportsSource lt = true) (nv nl : Nat) :
    (toTFlat (emitStoreCast trap srcTy width v k) nv nl).supportsSource lt = true := by
  cases srcTy <;> cases width <;>
    first | exact htrap nv nl | exact hk _ nv nl | tflat_builder_ss! hv

theorem emitBrTable_ss {lt : LegalTarget} (hv : lt.valid = true) (locTys retTys : List WValTy)
    (labs : List (WLabel K KL locTys)) (locs : Tup (Arg K) (locTys.map WValTy.toTy))
    (f : Arg K T.i64) (idx : Arg K T.i32) (defLbl : WLabel K KL locTys)
    (ba : Tup (Arg K) (defLbl.argTys.map WValTy.toTy)) (i : Nat) (ts : List Nat) (nv nl : Nat) :
    (toTFlat (emitBrTable locTys retTys labs locs f idx defLbl ba i ts) nv nl).supportsSource lt =
      true := by
  induction ts generalizing i nv nl with
  | nil =>
    simpa [emitBrTable, toTFlat, TFlat.supportsSource] using
      labelSig_supportsTy hv locTys defLbl.argTys
  | cons t _ ih =>
    simp only [emitBrTable]
    cases labs[t]? with | none => exact mkTrapExpr_ss hv retTys 1#32 f nv nl | some l =>
    by_cases hlt : l.argTys = defLbl.argTys
    · simp only [hlt, ↓reduceDIte]
      tflat_builder_ss! hv <;>
        first | simpa [hlt] using labelSig_supportsTy hv locTys defLbl.argTys | exact ih (i + 1) _ _
    · simp only [hlt, ↓reduceDIte]; exact mkTrapExpr_ss hv retTys 1#32 f nv nl

theorem emitSelect_ss {lt : LegalTarget} (hv : lt.valid = true) {rs : List Ty}
    {trap : Expr K KL rs} (htrap : ∀ nv nl, (toTFlat trap nv nl).supportsSource lt = true)
    (c : Arg K T.i32) (v1 v2 : SVal K) (k : SVal K → Expr K KL rs)
    (hk : ∀ y nv' nl', (toTFlat (k y) nv' nl').supportsSource lt = true) (nv nl : Nat) :
    (toTFlat (emitSelect trap c v1 v2 k) nv nl).supportsSource lt = true := by
  cases v1 <;> cases v2 <;> simp only [emitSelect] <;>
    first | exact htrap nv nl | tflat_builder_ss! hv

theorem emitEqz_ss {lt : LegalTarget} (hv : lt.valid = true) {rs : List Ty} (w : WValTy)
    (x : Arg K w.toTy) (k : Arg K T.i32 → Expr K KL rs)
    (hk : ∀ y nv' nl', (toTFlat (k y) nv' nl').supportsSource lt = true) (nv nl : Nat) :
    (toTFlat (emitEqz w x k) nv nl).supportsSource lt = true := by
  cases w <;> simp only [emitEqz] <;> tflat_builder_ss! hv

theorem emitRelOp_ss {lt : LegalTarget} (hv : lt.valid = true) {rs : List Ty} (w : WValTy)
    (op : WRelOp) (a b : Arg K w.toTy) (k : Arg K T.i32 → Expr K KL rs)
    (hk : ∀ y nv' nl', (toTFlat (k y) nv' nl').supportsSource lt = true) (nv nl : Nat) :
    (toTFlat (emitRelOp w op a b k) nv nl).supportsSource lt = true := by
  cases w <;> simp only [emitRelOp] <;> tflat_builder_ss! hv

theorem lowerSimpleInstr_ss {lt : LegalTarget} (hv : lt.valid = true) (ctx : WLowerCtx)
    (vc f : Arg K T.i64) (locs : Tup (Arg K) (ctx.locTys.map WValTy.toTy)) (stk : List (SVal K))
    (labs : List (WLabel K KL ctx.locTys)) (instr : WInstr)
    (k : WCont K KL ctx.locTys ctx.retTys)
    (hk : ∀ f' l' s' nv' nl', (toTFlat (k f' l' s') nv' nl').supportsSource lt = true)
    (nv nl : Nat) :
    (toTFlat (lowerSimpleInstr ctx vc f locs stk labs instr k) nv nl).supportsSource lt = true := by
  have htrap : ∀ nv' nl',
      (toTFlat (mkTrapExpr (L := KL) ctx.retTys 1#32 f) nv' nl').supportsSource lt = true :=
    fun nv' nl' => mkTrapExpr_ss hv ctx.retTys 1#32 f nv' nl'
  cases instr <;> simp only [lowerSimpleInstr] <;> try exact htrap nv nl
  case nop => exact hk f locs stk nv nl
  case br_if depth =>
    ss_pop (pop32 stk), c s1; cases labs[depth]? with | none => exact htrap nv nl | some l =>
    dsimp only; ss_pop (popArgsAux l.argTys s1), ba s2
    tflat_builder_ss! hv <;> exact hk f locs s1 _ _
  case call fnIdx =>
    cases ctx.funcs[fnIdx]? with | none => exact htrap nv nl | some callee =>
    dsimp only; cases ctx.types[callee.typeIdx]? with | none => exact htrap nv nl | some ft =>
    dsimp only; ss_pop (popArgsAux ft.params stk), ca s1; tflat_builder_ss! hv <;> first
      | apply hk | simpa [mkStatusTrapExpr, toTFlat, TFlat.supportsSource] using
        wasmRetSig_supportsTy hv ctx.retTys
  case drop => cases stk with | nil => exact htrap nv nl | cons _ r => exact hk f locs r nv nl
  case select =>
    ss_pop (pop32 stk), cond s1
    cases s1 with | nil => exact htrap nv nl | cons v₂ r2 =>
    cases r2 with | nil => exact htrap nv nl | cons v₁ r3 =>
    exact emitSelect_ss hv htrap cond v₁ v₂ _ (fun _ => hk f locs _) nv nl
  case local_get idx =>
    cases getLocal ctx.locTys locs idx with
    | none => exact htrap nv nl | some v => exact hk f locs _ nv nl
  case local_set idx | local_tee idx =>
    cases stk with | nil => exact htrap nv nl | cons v r =>
    dsimp only; cases setLocal ctx.locTys locs idx v with
    | none => exact htrap nv nl | some locs' => exact hk f locs' _ nv nl
  case global_get idx =>
    cases ctx.globals[idx]? with | none => exact htrap nv nl | some _ => exact hk f locs _ nv nl
  case load resTy width signed arg =>
    ss_mem_if (ctx.hasMem && validateLoad resTy width signed); ss_pop (pop32 stk), i r
    refine emitMemBounds_ss hv ctx.retTys vc f i arg width.bytes _ (fun _ _ _ =>
      tflat_load_ss lt width.memTy _ (by cases width <;> exact supportsTy_le64 hv (by omega))
        (by cases width <;> decide)
        (emitLoadCast_ss hv htrap resTy width signed _ _ (fun _ => hk f locs _) _ _)) nv nl
  case store srcTy width arg =>
    ss_mem_if (ctx.hasMem && validateStore srcTy width)
    ss_pop (popExpectS srcTy stk), v r; ss_pop (pop32 r), i r2
    refine emitMemBounds_ss hv ctx.retTys vc f i arg width.bytes _ (fun _ nv' nl' =>
      emitStoreCast_ss hv htrap srcTy width v _ (fun _ _ _ =>
        tflat_store_ss lt (t := width.memTy) _ _
          (by cases width <;> exact supportsTy_le64 hv (by omega))
          (by cases width <;> decide) (hk f locs r2 _ _)) nv' nl') nv nl
  case memory_size =>
    ss_mem_if ctx.hasMem; exact emitMemSize_ss hv vc _ (fun _ => hk f locs _) nv nl
  case memory_grow =>
    ss_mem_if ctx.hasMem; ss_pop (pop32 stk), d r
    exact emitMemGrow_ss hv ctx.retTys ctx.memMaxBytes vc f d _ (fun f' _ => hk f' locs _) nv nl
  case memory_fill =>
    ss_mem_if ctx.hasMem; ss_pop (pop32 stk), n r1; ss_pop (pop32 r1), v r2; ss_pop (pop32 r2), d r3
    exact emitMemFill_ss hv ctx.retTys vc f d v n _ (fun f' => hk f' locs r3) nv nl
  case memory_copy =>
    ss_mem_if ctx.hasMem; ss_pop (pop32 stk), n r1; ss_pop (pop32 r1), s r2; ss_pop (pop32 r2), d r3
    exact emitMemCopy_ss hv ctx.retTys vc f d s n _ (fun f' => hk f' locs r3) nv nl
  case i32_const _ | i64_const _ => exact hk f locs _ nv nl
  case eqz w =>
    cases w <;> cases stk with | nil => exact htrap nv nl | cons x _ =>
    cases x <;> first | exact htrap nv nl | exact emitEqz_ss hv _ _ _ (fun _ => hk f locs _) nv nl
  case unop w op =>
    ss_pop (popExpectS w stk), x r
    exact emitUnOp_ss hv ctx.retTys f w op x _ (fun _ => hk f locs _) nv nl
  case binop w op =>
    ss_pop (popExpectS w stk), b r1; ss_pop (popExpectS w r1), a r2
    exact emitBinOp_ss hv ctx.retTys f w op a b _ (fun _ => hk f locs _) nv nl
  case relop w op =>
    ss_pop (popExpectS w stk), b r1; ss_pop (popExpectS w r1), a r2
    exact emitRelOp_ss hv w op a b _ (fun _ => hk f locs _) nv nl
  case wrap_i64 => ss_pop (pop64 stk), x r; tflat_builder_ss! hv <;> exact hk f locs _ _ _
  case extend_i32_s | extend_i32_u =>
    ss_pop (pop32 stk), x r; tflat_builder_ss! hv <;> exact hk f locs _ _ _

theorem lowerGroupJoin_ss {lt : LegalTarget} (hv : lt.valid = true) (ctx : WLowerCtx)
    (ft : WFuncTy) (sa : List (SVal K)) (body : WLabel K KL ctx.locTys →
      WCont K KL ctx.locTys ctx.retTys → Expr K KL (wasmRetSig ctx.retTys))
    (after : WCont K KL ctx.locTys ctx.retTys) (hbody : ∀ lbl fall,
      (∀ f' l' s' nv' nl', (toTFlat (fall f' l' s') nv' nl').supportsSource lt = true) →
      ∀ nv' nl', (toTFlat (body lbl fall) nv' nl').supportsSource lt = true)
    (hafter : ∀ f' l' s' nv' nl', (toTFlat (after f' l' s') nv' nl').supportsSource lt = true)
    (nv nl : Nat) :
    (toTFlat (lowerGroupJoin ctx ft sa body after) nv nl).supportsSource lt = true := by
  refine tflat_group1_ss lt (labelSig ctx.locTys ft.results) _ _
    (labelSig_supportsTy hv ctx.locTys ft.results) (by dsimp only; exact hafter _ _ _ _ _) ?_
  refine hbody _ _ (fun _ _ s' _ _ => ?_) _ _
  ss_pop (popArgsAux ft.results s'), ra s1
  exact tflat_jump_ss lt _ _ (labelSig_supportsTy hv ctx.locTys ft.results)

theorem lowerSeq_ss_aux {lt : LegalTarget} (hv : lt.valid = true) (ctx : WLowerCtx) :
    ∀ (sz : Nat) (vc f : Arg K T.i64) (locs : Tup (Arg K) (ctx.locTys.map WValTy.toTy))
      (stk : List (SVal K)) (labs : List (WLabel K KL ctx.locTys)) (instrs : List WInstr)
      (_hsz : sizeOf instrs ≤ sz) (k : WCont K KL ctx.locTys ctx.retTys),
      (∀ f' l' s' nv' nl', (toTFlat (k f' l' s') nv' nl').supportsSource lt = true) →
      ∀ nv nl,
        (toTFlat (lowerSeq ctx vc f locs stk labs instrs k) nv nl).supportsSource lt = true := by
  intro sz; induction sz using Nat.strongRecOn with | _ sz ih =>
  intro vc f locs stk labs instrs hsz k hk nv nl
  have htrap : ∀ nv' nl',
      (toTFlat (mkTrapExpr (L := KL) ctx.retTys 1#32 f) nv' nl').supportsSource lt = true :=
    fun nv' nl' => mkTrapExpr_ss hv ctx.retTys 1#32 f nv' nl'
  cases instrs with
  | nil => simp only [lowerSeq]; exact hk f locs stk nv nl
  | cons i rest =>
    have hlt {b : List WInstr} (h : sizeOf b < sizeOf (i :: rest)) : sizeOf b < sz :=
      Nat.lt_of_lt_of_le h hsz
    let hafter := fun (f' : Arg K T.i64) l' s' nv' nl' =>
      ih _ (hlt (by simp +arith)) vc f' l' s' labs rest (Nat.le_refl _) k hk nv' nl'
    cases i with
    | unreachable => simp only [lowerSeq]; exact htrap nv nl
    | br depth =>
      simp only [lowerSeq]; cases labs[depth]? with | none => exact htrap nv nl | some lbl =>
      dsimp only; ss_pop (popArgsAux lbl.argTys stk), ba s1
      simpa [toTFlat, TFlat.supportsSource, labelSig, List.all_cons] using
        labelSig_supportsTy_pair hv ctx.locTys lbl.argTys
    | br_table targets defTarget =>
      simp only [lowerSeq]; ss_pop (pop32 stk), idx32 stk1
      cases labs[defTarget]? with | none => exact htrap nv nl | some defLbl =>
      dsimp only; ss_pop (popArgsAux defLbl.argTys stk1), ba s2
      exact emitBrTable_ss hv ctx.locTys ctx.retTys labs locs f idx32 defLbl ba 0 targets nv nl
    | return_ =>
      simp only [lowerSeq]; ss_pop (popArgsAux ctx.retTys stk), ra s1
      simpa [toTFlat, TFlat.supportsSource] using wasmRetSig_supportsTy hv ctx.retTys
    | block bt body =>
      simp only [lowerSeq]; cases bt.resolve ctx.types with | none => exact htrap nv nl | some ft =>
      dsimp only; ss_pop (popArgsAux ft.params stk), ia sa
      exact lowerGroupJoin_ss hv ctx ft sa _ _ (fun _ _ hfall =>
        ih _ (hlt (by simp +arith)) vc f locs _ _ body (Nat.le_refl _) _ hfall) hafter nv nl
    | loop bt body =>
      simp only [lowerSeq]; cases bt.resolve ctx.types with | none => exact htrap nv nl | some ft =>
      dsimp only; ss_pop (popArgsAux ft.params stk), ia sa
      refine lowerGroupJoin_ss hv ctx ft sa _ _ (fun _ _ hfall _ _ => ?_) hafter nv nl
      refine tflat_group1_ss lt (labelSig ctx.locTys ft.params) _ _
        (labelSig_supportsTy hv ctx.locTys ft.params) ?_
        (tflat_jump_ss lt _ _ (labelSig_supportsTy hv ctx.locTys ft.params))
      tflat_builder_ss! hv
      exact ih _ (hlt (by simp +arith)) vc _ _ _ _ body (Nat.le_refl _) _ hfall _ _
    | if_ bt thenBody elseBody =>
      simp only [lowerSeq]; cases bt.resolve ctx.types with | none => exact htrap nv nl | some ft =>
      dsimp only; ss_pop (pop32 stk), cond stk1; ss_pop (popArgsAux ft.params stk1), ia sa
      refine lowerGroupJoin_ss hv ctx ft sa _ _ (fun _ _ hfall _ _ => by
        tflat_builder_ss! hv <;>
          exact ih _ (hlt (by simp +arith)) vc f locs _ _ _ (Nat.le_refl _) _ hfall _ _)
        hafter nv nl
    | _ =>
      simp only [lowerSeq]
      exact lowerSimpleInstr_ss hv ctx vc f locs stk labs _ _
        (fun _ l' s' nv' nl' => hafter _ l' s' nv' nl') nv nl

theorem lowerFuncBody_supportsSource (m : WModule) (f : WFunc) (ft : WFuncTy)
    {lt : LegalTarget} (hv : lt.valid = true) :
    (lowerFuncBody m f ft).supportsSource lt = true := by
  simp only [Func.supportsSource, Bool.and_eq_true, lowerFuncBody]
  refine ⟨⟨⟨hv, wasmAbiParams_supportsTy hv ft⟩, wasmRetSig_supportsTy hv ft.results⟩, ?_⟩
  let ctx : WLowerCtx :=
    { types := m.types, funcs := m.funcs, hasMem := m.memory.isSome,
      memMaxBytes := (m.memory.map WMemSpec.maxBytes).getD 0#64,
      globals := m.globals, locTys := ft.params ++ f.locals, retTys := ft.results }
  have hsig := labelSig_supportsTy_pair hv ctx.locTys ft.results
  have hret := wasmRetSig_supportsTy hv ft.results
  simp only [toTFlat, toTBlocks, TFlat.supportsSource, TBlocks.supportsSource,
    labelSig, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨⟨hsig, hsig, by simpa [toTFlat, TFlat.supportsSource] using hret⟩, ?_⟩
  refine lowerSeq_ss_aux hv ctx (sizeOf f.body) _ _ _ [] _ f.body (Nat.le_refl _) _
    (fun _ _ s' _ _ => ?_) _ _
  ss_pop (popArgsAux ft.results s'), ra s1; simpa [toTFlat, TFlat.supportsSource] using hret

/-- Universal supportability: every lowered function in `lowerModule m` satisfies
`fn.body.supportsSource lt` for every valid `LegalTarget` (including both `x64LegalTarget`
and `armLegalTarget`). -/
theorem lowerModule_supportsSource (m : WModule) {lt : LegalTarget} (hv : lt.valid = true) :
    ∀ fn ∈ (lowerModule m).fns, fn.body.supportsSource lt = true := fun _ hmem => by
  rcases List.mem_map.mp hmem with ⟨f, _, rfl⟩; exact lowerFuncBody_supportsSource m f _ hv

theorem legalSig_map_toTy {lt : LegalTarget}
    (h32 : lt.legalTys T.i32 = [T.i32]) (h64 : lt.legalTys T.i64 = [T.i64]) :
    ∀ ts : List WValTy, lt.legalSig (ts.map WValTy.toTy) = ts.map WValTy.toTy
  | [] => rfl
  | .i32 :: ts => by
    simp only [List.map_cons, WValTy.toTy, LegalTarget.legalSig, h32, List.singleton_append]
    exact congrArg (T.i32 :: ·) (legalSig_map_toTy h32 h64 ts)
  | .i64 :: ts => by
    simp only [List.map_cons, WValTy.toTy, LegalTarget.legalSig, h64, List.singleton_append]
    exact congrArg (T.i64 :: ·) (legalSig_map_toTy h32 h64 ts)

/-- Every lowered function's parameter and result signatures are already legal on any target whose
`legalTys` preserves scalar `i32` and `i64` (including both `x64LegalTarget` and
`armLegalTarget`). -/
theorem lowerModule_legalSig (m : WModule) {lt : LegalTarget}
    (h32 : lt.legalTys T.i32 = [T.i32]) (h64 : lt.legalTys T.i64 = [T.i64]) :
    ∀ fn ∈ (lowerModule m).fns, lt.legalSig fn.as = fn.as ∧ lt.legalSig fn.rs = fn.rs :=
  fun _ hmem => by
    rcases List.mem_map.mp hmem with ⟨f, _, rfl⟩
    simp only [lowerFn, wasmAbiResults, wasmRetSig, LegalTarget.legalSig, h32, h64,
      List.cons_append, List.nil_append]
    exact ⟨congrArg (T.i64 :: T.i64 :: ·) (legalSig_map_toTy h32 h64 _),
      congrArg (T.i32 :: T.i64 :: ·) (legalSig_map_toTy h32 h64 _)⟩

end SupportsSourceProofs

end LeanQbe.T.Wasm
