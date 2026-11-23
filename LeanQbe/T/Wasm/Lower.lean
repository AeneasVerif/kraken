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

/-- Branchless SWAR population count for `i32` / `i64`, supported on both x64 and Arm64. -/
@[expose] def emitPopcnt {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (w : WValTy)
    (x : Arg V w.toTy) (k : Arg V w.toTy → Expr V L rs) : Expr V L rs :=
  match w with
  | .i32 =>
    .let_ (.mk (.lshr T.i32) (x, .imm 1#32, ())) fun s1 =>
    .let_ (.mk (.and T.i32) (.var s1.1, .imm 0x55555555#32, ())) fun s1m =>
    .let_ (.mk (.sub T.i32) (x, .var s1m.1, ())) fun t1 =>
    .let_ (.mk (.and T.i32) (.var t1.1, .imm 0x33333333#32, ())) fun t1a =>
    .let_ (.mk (.lshr T.i32) (.var t1.1, .imm 2#32, ())) fun t1s =>
    .let_ (.mk (.and T.i32) (.var t1s.1, .imm 0x33333333#32, ())) fun t1b =>
    .let_ (.mk (.add T.i32) (.var t1a.1, .var t1b.1, ())) fun t2 =>
    .let_ (.mk (.lshr T.i32) (.var t2.1, .imm 4#32, ())) fun t2s =>
    .let_ (.mk (.add T.i32) (.var t2.1, .var t2s.1, ())) fun t2a =>
    .let_ (.mk (.and T.i32) (.var t2a.1, .imm 0x0F0F0F0F#32, ())) fun t3 =>
    .let_ (.mk (.mul T.i32) (.var t3.1, .imm 0x01010101#32, ())) fun prod =>
    .let_ (.mk (.lshr T.i32) (.var prod.1, .imm 24#32, ())) fun res =>
      k (.var res.1)
  | .i64 =>
    .let_ (.mk (.lshr T.i64) (x, .imm 1#64, ())) fun s1 =>
    .let_ (.mk (.and T.i64) (.var s1.1, .imm 0x5555555555555555#64, ())) fun s1m =>
    .let_ (.mk (.sub T.i64) (x, .var s1m.1, ())) fun t1 =>
    .let_ (.mk (.and T.i64) (.var t1.1, .imm 0x3333333333333333#64, ())) fun t1a =>
    .let_ (.mk (.lshr T.i64) (.var t1.1, .imm 2#64, ())) fun t1s =>
    .let_ (.mk (.and T.i64) (.var t1s.1, .imm 0x3333333333333333#64, ())) fun t1b =>
    .let_ (.mk (.add T.i64) (.var t1a.1, .var t1b.1, ())) fun t2 =>
    .let_ (.mk (.lshr T.i64) (.var t2.1, .imm 4#64, ())) fun t2s =>
    .let_ (.mk (.add T.i64) (.var t2.1, .var t2s.1, ())) fun t2a =>
    .let_ (.mk (.and T.i64) (.var t2a.1, .imm 0x0F0F0F0F0F0F0F0F#64, ())) fun t3 =>
    .let_ (.mk (.mul T.i64) (.var t3.1, .imm 0x0101010101010101#64, ())) fun prod =>
    .let_ (.mk (.lshr T.i64) (.var prod.1, .imm 56#64, ())) fun res =>
      k (.var res.1)

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

/-- Emit safe WebAssembly binary operation on `a, b : Arg V w.toTy`, with explicit division/
remainder trap & `INT_MIN ÷ -1` guards. -/
@[expose] def emitBinOp {V : Ty → Type} {L : List Ty → Type} (retTys : List WValTy)
    (fuel : Arg V T.i64) (w : WValTy) (op : WBinOp) (a b : Arg V w.toTy)
    (k : Arg V w.toTy → Expr V L (wasmRetSig retTys)) : Expr V L (wasmRetSig retTys) :=
  let emitPure (mkCode : (t : Ty) → OpCode [t, t] [t]) : Expr V L (wasmRetSig retTys) :=
    match w with
    | .i32 => Expr.let_ (.mk (mkCode T.i32) (a, b, ())) fun r => k (.var r.1)
    | .i64 => Expr.let_ (.mk (mkCode T.i64) (a, b, ())) fun r => k (.var r.1)
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
  | .div_u =>
    match w with
    | .i32 =>
      .let_ (.mk (.cmp .eq T.i32) (b, .imm 0#32, ())) fun isZ =>
      .jnz (.var isZ.1) (mkTrapExpr retTys 1#32 fuel)
        (.let_ (.mk (.udiv 32) (a, b, ())) fun r => k (.var r.1))
    | .i64 =>
      .let_ (.mk (.cmp .eq T.i64) (b, .imm 0#64, ())) fun isZ =>
      .jnz (.var isZ.1) (mkTrapExpr retTys 1#32 fuel)
        (.let_ (.mk (.udiv 64) (a, b, ())) fun r => k (.var r.1))
  | .rem_u =>
    match w with
    | .i32 =>
      .let_ (.mk (.cmp .eq T.i32) (b, .imm 0#32, ())) fun isZ =>
      .jnz (.var isZ.1) (mkTrapExpr retTys 1#32 fuel)
        (.let_ (.mk (.urem 32) (a, b, ())) fun r => k (.var r.1))
    | .i64 =>
      .let_ (.mk (.cmp .eq T.i64) (b, .imm 0#64, ())) fun isZ =>
      .jnz (.var isZ.1) (mkTrapExpr retTys 1#32 fuel)
        (.let_ (.mk (.urem 64) (a, b, ())) fun r => k (.var r.1))
  | .div_s =>
    match w with
    | .i32 =>
      .let_ (.mk (.cmp .eq T.i32) (b, .imm 0#32, ())) fun isZ =>
      .jnz (.var isZ.1) (mkTrapExpr retTys 1#32 fuel)
        (.let_ (.mk (.cmp .eq T.i32) (a, .imm 0x80000000#32, ())) fun isMin =>
        .let_ (.mk (.cmp .eq T.i32) (b, .imm 0xFFFFFFFF#32, ())) fun isNeg1 =>
        .let_ (.mk (.and .bool) (.var isMin.1, .var isNeg1.1, ())) fun isOvf =>
        .jnz (.var isOvf.1) (mkTrapExpr retTys 1#32 fuel)
          (.let_ (.mk (.sdiv 32) (a, b, ())) fun r => k (.var r.1)))
    | .i64 =>
      .let_ (.mk (.cmp .eq T.i64) (b, .imm 0#64, ())) fun isZ =>
      .jnz (.var isZ.1) (mkTrapExpr retTys 1#32 fuel)
        (.let_ (.mk (.cmp .eq T.i64) (a, .imm 0x8000000000000000#64, ())) fun isMin =>
        .let_ (.mk (.cmp .eq T.i64) (b, .imm 0xFFFFFFFFFFFFFFFF#64, ())) fun isNeg1 =>
        .let_ (.mk (.and .bool) (.var isMin.1, .var isNeg1.1, ())) fun isOvf =>
        .jnz (.var isOvf.1) (mkTrapExpr retTys 1#32 fuel)
          (.let_ (.mk (.sdiv 64) (a, b, ())) fun r => k (.var r.1)))
  | .rem_s =>
    match w with
    | .i32 =>
      .let_ (.mk (.cmp .eq T.i32) (b, .imm 0#32, ())) fun isZ =>
      .jnz (.var isZ.1) (mkTrapExpr retTys 1#32 fuel)
        (.let_ (.mk (.cmp .eq T.i32) (a, .imm 0x80000000#32, ())) fun isMin =>
        .let_ (.mk (.cmp .eq T.i32) (b, .imm 0xFFFFFFFF#32, ())) fun isNeg1 =>
        .let_ (.mk (.and .bool) (.var isMin.1, .var isNeg1.1, ())) fun isOvf =>
        .jnz (.var isOvf.1) (k (.imm 0#32))
          (.let_ (.mk (.srem 32) (a, b, ())) fun r => k (.var r.1)))
    | .i64 =>
      .let_ (.mk (.cmp .eq T.i64) (b, .imm 0#64, ())) fun isZ =>
      .jnz (.var isZ.1) (mkTrapExpr retTys 1#32 fuel)
        (.let_ (.mk (.cmp .eq T.i64) (a, .imm 0x8000000000000000#64, ())) fun isMin =>
        .let_ (.mk (.cmp .eq T.i64) (b, .imm 0xFFFFFFFFFFFFFFFF#64, ())) fun isNeg1 =>
        .let_ (.mk (.and .bool) (.var isMin.1, .var isNeg1.1, ())) fun isOvf =>
        .jnz (.var isOvf.1) (k (.imm 0#64))
          (.let_ (.mk (.srem 64) (a, b, ())) fun r => k (.var r.1)))

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
    | some (cond, .i32 v2 :: .i32 v1 :: stk3) =>
      .let_ (.mk (.cmp .ne T.i32) (cond, .imm 0#32, ())) fun selB =>
      .let_ (.mk (.select T.i32) (.var selB.1, v1, v2, ())) fun res =>
        k fuel locs (.i32 (.var res.1) :: stk3)
    | some (cond, .i64 v2 :: .i64 v1 :: stk3) =>
      .let_ (.mk (.cmp .ne T.i32) (cond, .imm 0#32, ())) fun selB =>
      .let_ (.mk (.select T.i64) (.var selB.1, v1, v2, ())) fun res =>
        k fuel locs (.i64 (.var res.1) :: stk3)
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
    | .i32, .i32 x :: stk1 =>
      .let_ (.mk (.cmp .eq T.i32) (x, .imm 0#32, ())) fun b =>
      .let_ (.mk (.ofBool 32) (.var b.1, ())) fun r =>
        k fuel locs (.i32 (.var r.1) :: stk1)
    | .i64, .i64 x :: stk1 =>
      .let_ (.mk (.cmp .eq T.i64) (x, .imm 0#64, ())) fun b =>
      .let_ (.mk (.ofBool 32) (.var b.1, ())) fun r =>
        k fuel locs (.i32 (.var r.1) :: stk1)
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
        let cmp := lowerRelOp op
        match w with
        | .i32 =>
          .let_ (.mk (.cmp cmp T.i32) (a, b, ())) fun cb =>
          .let_ (.mk (.ofBool 32) (.var cb.1, ())) fun r =>
            k fuel locs (.i32 (.var r.1) :: stk2)
        | .i64 =>
          .let_ (.mk (.cmp cmp T.i64) (a, b, ())) fun cb =>
          .let_ (.mk (.ofBool 32) (.var cb.1, ())) fun r =>
            k fuel locs (.i32 (.var r.1) :: stk2)
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
        .group (sig := [labelSig ctx.locTys ft.results])
          (fun _ =>
            .cons (fun xs =>
              let (locs', resArgs) := tupSplit (varsTup xs.2)
              lowerSeq ctx vmCtx (.var xs.1) locs'
                (pushArgsAux ft.results resArgs stkAfter) labs rest k) .nil)
          (fun (jLbl, ()) =>
            let lbl' : WLabel V L ctx.locTys := ⟨ft.results, jLbl⟩
            lowerSeq ctx vmCtx fuel locs (pushArgsAux ft.params initArgs [])
              (lbl' :: labs) body fun fuelEnd locsEnd stkEnd =>
                match popArgsAux ft.results stkEnd with
                | some (resArgs, _) => .jump jLbl (fuelEnd, tupAppend locsEnd resArgs)
                | none => mkTrapExpr ctx.retTys 1#32 fuelEnd)
  | .loop bt body :: rest, k =>
    match bt.resolve ctx.types with
    | none => mkTrapExpr ctx.retTys 1#32 fuel
    | some ft =>
      match popArgsAux ft.params stk with
      | none => mkTrapExpr ctx.retTys 1#32 fuel
      | some (initArgs, stkAfter) =>
        .group (sig := [labelSig ctx.locTys ft.results])
          (fun _ =>
            .cons (fun xs =>
              let (locs', resArgs) := tupSplit (varsTup xs.2)
              lowerSeq ctx vmCtx (.var xs.1) locs'
                (pushArgsAux ft.results resArgs stkAfter) labs rest k) .nil)
          (fun (jAfter, ()) =>
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
                        (pushArgsAux ft.params loopArgs []) (lbl' :: labs) body
                        fun fuelEnd locsEnd stkEnd =>
                          match popArgsAux ft.results stkEnd with
                          | some (resArgs, _) => .jump jAfter (fuelEnd, tupAppend locsEnd resArgs)
                          | none => mkTrapExpr ctx.retTys 1#32 fuelEnd)) .nil)
              (fun (lHdr, ()) => .jump lHdr (fuel, tupAppend locs initArgs)))
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
          .group (sig := [labelSig ctx.locTys ft.results])
            (fun _ =>
              .cons (fun xs =>
                let (locs', resArgs) := tupSplit (varsTup xs.2)
                lowerSeq ctx vmCtx (.var xs.1) locs'
                  (pushArgsAux ft.results resArgs stkAfter) labs rest k) .nil)
            (fun (jLbl, ()) =>
              let lbl' : WLabel V L ctx.locTys := ⟨ft.results, jLbl⟩
              let fall : WCont V L ctx.locTys ctx.retTys := fun fuelEnd locsEnd stkEnd =>
                match popArgsAux ft.results stkEnd with
                | some (resArgs, _) => .jump jLbl (fuelEnd, tupAppend locsEnd resArgs)
                | none => mkTrapExpr ctx.retTys 1#32 fuelEnd
              let brThen := lowerSeq ctx vmCtx fuel locs
                (pushArgsAux ft.params initArgs []) (lbl' :: labs) thenBody fall
              let brElse := lowerSeq ctx vmCtx fuel locs
                (pushArgsAux ft.params initArgs []) (lbl' :: labs) elseBody fall
              .let_ (.mk (.cmp .ne T.i32) (condArg, .imm 0#32, ())) fun isTrue =>
              .jnz (.var isTrue.1) brThen brElse)
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

theorem emitPopcnt_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (w : WValTy)
    {x₁ : Arg V₁ w.toTy} {x₂ : Arg V₂ w.toTy} (hx : ArgRel G w.toTy x₁ x₂)
    {k₁ : Arg V₁ w.toTy → Expr V₁ L₁ rs} {k₂ : Arg V₂ w.toTy → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' w.toTy y₁ y₂ →
      Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitPopcnt w x₁ k₁) (emitPopcnt w x₂ k₂) := by
  cases w
  · refine wf_let2 (.lshr T.i32) hx (.imm _) fun h1 _ _ hs1 =>
      wf_let2 (.and T.i32) hs1 (.imm _) fun h2 _ _ hs1m =>
      wf_let2 (.sub T.i32) (ArgRel.mono (fun p hp => h2 p (h1 p hp)) hx) hs1m fun h3 _ _ ht1 =>
      wf_let2 (.and T.i32) ht1 (.imm _) fun h4 _ _ ht1a =>
      wf_let2 (.lshr T.i32) (ArgRel.mono h4 ht1) (.imm _) fun h5 _ _ ht1s =>
      wf_let2 (.and T.i32) ht1s (.imm _) fun h6 _ _ ht1b =>
      wf_let2 (.add T.i32) (ArgRel.mono (fun p hp => h6 p (h5 p hp)) ht1a) ht1b fun h7 _ _ ht2 =>
      wf_let2 (.lshr T.i32) ht2 (.imm _) fun h8 _ _ ht2s =>
      wf_let2 (.add T.i32) (ArgRel.mono h8 ht2) ht2s fun h9 _ _ ht2a =>
      wf_let2 (.and T.i32) ht2a (.imm _) fun h10 _ _ ht3 =>
      wf_let2 (.mul T.i32) ht3 (.imm _) fun h11 _ _ hpr =>
      wf_let2 (.lshr T.i32) hpr (.imm _) fun h12 _ _ hres =>
        hk (fun p hp => h12 p (h11 p (h10 p (h9 p (h8 p (h7 p (h6 p
          (h5 p (h4 p (h3 p (h2 p (h1 p hp)))))))))))) _ _ hres
  · refine wf_let2 (.lshr T.i64) hx (.imm _) fun h1 _ _ hs1 =>
      wf_let2 (.and T.i64) hs1 (.imm _) fun h2 _ _ hs1m =>
      wf_let2 (.sub T.i64) (ArgRel.mono (fun p hp => h2 p (h1 p hp)) hx) hs1m fun h3 _ _ ht1 =>
      wf_let2 (.and T.i64) ht1 (.imm _) fun h4 _ _ ht1a =>
      wf_let2 (.lshr T.i64) (ArgRel.mono h4 ht1) (.imm _) fun h5 _ _ ht1s =>
      wf_let2 (.and T.i64) ht1s (.imm _) fun h6 _ _ ht1b =>
      wf_let2 (.add T.i64) (ArgRel.mono (fun p hp => h6 p (h5 p hp)) ht1a) ht1b fun h7 _ _ ht2 =>
      wf_let2 (.lshr T.i64) ht2 (.imm _) fun h8 _ _ ht2s =>
      wf_let2 (.add T.i64) (ArgRel.mono h8 ht2) ht2s fun h9 _ _ ht2a =>
      wf_let2 (.and T.i64) ht2a (.imm _) fun h10 _ _ ht3 =>
      wf_let2 (.mul T.i64) ht3 (.imm _) fun h11 _ _ hpr =>
      wf_let2 (.lshr T.i64) hpr (.imm _) fun h12 _ _ hres =>
        hk (fun p hp => h12 p (h11 p (h10 p (h9 p (h8 p (h7 p (h6 p
          (h5 p (h4 p (h3 p (h2 p (h1 p hp)))))))))))) _ _ hres

theorem emitUnOp_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (retTys : List WValTy)
    {f₁ : Arg V₁ T.i64} {f₂ : Arg V₂ T.i64} (hf : ArgRel G T.i64 f₁ f₂)
    (w : WValTy) (op : WUnOp) {x₁ : Arg V₁ w.toTy} {x₂ : Arg V₂ w.toTy}
    (hx : ArgRel G w.toTy x₁ x₂)
    {k₁ : Arg V₁ w.toTy → Expr V₁ L₁ (wasmRetSig retTys)}
    {k₂ : Arg V₂ w.toTy → Expr V₂ L₂ (wasmRetSig retTys)}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' w.toTy y₁ y₂ →
      Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitUnOp retTys f₁ w op x₁ k₁) (emitUnOp retTys f₂ w op x₂ k₂) := by
  cases w <;> cases op
  · exact wf_let1 (.clz 32) hx fun h1 _ _ hr => hk h1 _ _ hr
  · exact wf_let1 (.ctz 32) hx fun h1 _ _ hr => hk h1 _ _ hr
  · exact emitPopcnt_wf .i32 hx hk
  · exact wf_let1 (.trunc 32 8) hx fun h1 _ _ hb =>
      wf_let1 (.sext 8 32) hb fun h2 _ _ hr => hk (fun p hp => h2 p (h1 p hp)) _ _ hr
  · exact wf_let1 (.trunc 32 16) hx fun h1 _ _ hb =>
      wf_let1 (.sext 16 32) hb fun h2 _ _ hr => hk (fun p hp => h2 p (h1 p hp)) _ _ hr
  · exact mkTrapExpr_wf retTys 1#32 hf
  · exact wf_let1 (.clz 64) hx fun h1 _ _ hr => hk h1 _ _ hr
  · exact wf_let1 (.ctz 64) hx fun h1 _ _ hr => hk h1 _ _ hr
  · exact emitPopcnt_wf .i64 hx hk
  · exact wf_let1 (.trunc 64 8) hx fun h1 _ _ hb =>
      wf_let1 (.sext 8 64) hb fun h2 _ _ hr => hk (fun p hp => h2 p (h1 p hp)) _ _ hr
  · exact wf_let1 (.trunc 64 16) hx fun h1 _ _ hb =>
      wf_let1 (.sext 16 64) hb fun h2 _ _ hr => hk (fun p hp => h2 p (h1 p hp)) _ _ hr
  · exact wf_let1 (.trunc 64 32) hx fun h1 _ _ hb =>
      wf_let1 (.sext 32 64) hb fun h2 _ _ hr => hk (fun p hp => h2 p (h1 p hp)) _ _ hr

theorem emitBinOp_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (retTys : List WValTy)
    {f₁ : Arg V₁ T.i64} {f₂ : Arg V₂ T.i64} (hf : ArgRel G T.i64 f₁ f₂)
    (w : WValTy) (op : WBinOp) {a₁ b₁ : Arg V₁ w.toTy} {a₂ b₂ : Arg V₂ w.toTy}
    (ha : ArgRel G w.toTy a₁ a₂) (hb : ArgRel G w.toTy b₁ b₂)
    {k₁ : Arg V₁ w.toTy → Expr V₁ L₁ (wasmRetSig retTys)}
    {k₂ : Arg V₂ w.toTy → Expr V₂ L₂ (wasmRetSig retTys)}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' w.toTy y₁ y₂ →
      Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitBinOp retTys f₁ w op a₁ b₁ k₁) (emitBinOp retTys f₂ w op a₂ b₂ k₂) := by
  cases op <;> cases w <;>
  first
  | exact wf_let2 _ ha hb fun h1 _ _ hr => hk h1 _ _ hr
  | exact wf_let2 (.cmp .eq _) hb (.imm _) fun h1 _ _ hz =>
      .jnz hz (mkTrapExpr_wf retTys 1#32 (ArgRel.mono h1 hf))
        (wf_let2 _ (ArgRel.mono h1 ha) (ArgRel.mono h1 hb) fun h2 _ _ hr =>
          hk (fun p hp => h2 p (h1 p hp)) _ _ hr)
  | exact wf_let2 (.cmp .eq _) hb (.imm _) fun h1 _ _ hz =>
      .jnz hz (mkTrapExpr_wf retTys 1#32 (ArgRel.mono h1 hf))
        (wf_let2 (.cmp .eq _) (ArgRel.mono h1 ha) (.imm _) fun h2 _ _ hm =>
          wf_let2 (.cmp .eq _) (ArgRel.mono (fun p hp => h2 p (h1 p hp)) hb) (.imm _)
            fun h3 _ _ hn =>
            wf_let2 (.and .bool) (ArgRel.mono h3 hm) hn fun h4 _ _ ho =>
              .jnz ho
                (mkTrapExpr_wf retTys 1#32
                  (ArgRel.mono (fun p hp => h4 p (h3 p (h2 p (h1 p hp)))) hf))
                (wf_let2 (.sdiv _)
                  (ArgRel.mono (fun p hp => h4 p (h3 p (h2 p (h1 p hp)))) ha)
                  (ArgRel.mono (fun p hp => h4 p (h3 p (h2 p (h1 p hp)))) hb)
                  fun h5 _ _ hr =>
                    hk (fun p hp => h5 p (h4 p (h3 p (h2 p (h1 p hp))))) _ _ hr))
  | exact wf_let2 (.cmp .eq _) hb (.imm _) fun h1 _ _ hz =>
      .jnz hz (mkTrapExpr_wf retTys 1#32 (ArgRel.mono h1 hf))
        (wf_let2 (.cmp .eq _) (ArgRel.mono h1 ha) (.imm _) fun h2 _ _ hm =>
          wf_let2 (.cmp .eq _) (ArgRel.mono (fun p hp => h2 p (h1 p hp)) hb) (.imm _)
            fun h3 _ _ hn =>
            wf_let2 (.and .bool) (ArgRel.mono h3 hm) hn fun h4 _ _ ho =>
              .jnz ho
                (hk (fun p hp => h4 p (h3 p (h2 p (h1 p hp)))) _ _ (.imm _))
                (wf_let2 (.srem _)
                  (ArgRel.mono (fun p hp => h4 p (h3 p (h2 p (h1 p hp)))) ha)
                  (ArgRel.mono (fun p hp => h4 p (h3 p (h2 p (h1 p hp)))) hb)
                  fun h5 _ _ hr =>
                    hk (fun p hp => h5 p (h4 p (h3 p (h2 p (h1 p hp))))) _ _ hr))

theorem emitLoadCast_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {t₁ : Expr V₁ L₁ rs} {t₂ : Expr V₂ L₂ rs} (ht : Wf G D t₁ t₂)
    (resTy : WValTy) (width : WMemWidth) (signed : Bool)
    (r₁ : V₁ width.memTy) (r₂ : V₂ width.memTy) (hr : ⟨width.memTy, r₁, r₂⟩ ∈ G)
    {k₁ : Arg V₁ resTy.toTy → Expr V₁ L₁ rs} {k₂ : Arg V₂ resTy.toTy → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' resTy.toTy y₁ y₂ →
      Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitLoadCast t₁ resTy width signed r₁ k₁)
           (emitLoadCast t₂ resTy width signed r₂ k₂) := by
  cases resTy <;> cases width <;> cases signed <;>
  first
  | exact ht
  | exact hk (fun _ hp => hp) _ _ (.var hr)
  | exact wf_let1 _ (.var hr) fun h1 _ _ hy => hk h1 _ _ hy

theorem emitStoreCast_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {t₁ : Expr V₁ L₁ rs} {t₂ : Expr V₂ L₂ rs} (ht : Wf G D t₁ t₂)
    (srcTy : WValTy) (width : WMemWidth)
    {v₁ : Arg V₁ srcTy.toTy} {v₂ : Arg V₂ srcTy.toTy} (hv : ArgRel G srcTy.toTy v₁ v₂)
    {k₁ : Arg V₁ width.memTy → Expr V₁ L₁ rs} {k₂ : Arg V₂ width.memTy → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' width.memTy y₁ y₂ →
      Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitStoreCast t₁ srcTy width v₁ k₁)
           (emitStoreCast t₂ srcTy width v₂ k₂) := by
  cases srcTy <;> cases width <;>
  first
  | exact ht
  | exact hk (fun _ hp => hp) _ _ hv
  | exact wf_let1 _ hv fun h1 _ _ hy => hk h1 _ _ hy

theorem emitBrTable_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {D : Ctx L₁ L₂} (locTys retTys : List WValTy)
    {labs₁ : List (WLabel V₁ L₁ locTys)} {labs₂ : List (WLabel V₂ L₂ locTys)}
    (hlabs : LabsRel D locTys labs₁ labs₂)
    {def₁ : WLabel V₁ L₁ locTys} {def₂ : WLabel V₂ L₂ locTys}
    (hdef : LabRel D locTys def₁ def₂) (har : def₁.argTys = def₂.argTys) :
    ∀ {G : Ctx V₁ V₂}
      {locs₁ : Tup (Arg V₁) (locTys.map WValTy.toTy)}
      {locs₂ : Tup (Arg V₂) (locTys.map WValTy.toTy)}
      {f₁ : Arg V₁ T.i64} {f₂ : Arg V₂ T.i64}
      {idx₁ : Arg V₁ T.i32} {idx₂ : Arg V₂ T.i32}
      {ba₁ : Tup (Arg V₁) (def₁.argTys.map WValTy.toTy)}
      {ba₂ : Tup (Arg V₂) (def₂.argTys.map WValTy.toTy)},
      TRel (ArgRel G) locs₁ locs₂ → ArgRel G T.i64 f₁ f₂ → ArgRel G T.i32 idx₁ idx₂ →
      TRel (ArgRel G) ba₁ (har ▸ ba₂) →
      ∀ (i : Nat) (ts : List Nat),
        Wf G D (emitBrTable locTys retTys labs₁ locs₁ f₁ idx₁ def₁ ba₁ i ts)
               (emitBrTable locTys retTys labs₂ locs₂ f₂ idx₂ def₂ ba₂ i ts) := by
  obtain ⟨hdeq, hdm⟩ := hdef
  cases def₁ with
  | mk dt dl₁ =>
    cases def₂ with
    | mk dt2 dl₂ =>
      dsimp only at hdeq har hdm
      subst har
      intro G locs₁ locs₂ f₁ f₂ idx₁ idx₂ ba₁ ba₂ hlocs hf hidx hba i ts
      induction ts generalizing G i with
      | nil =>
        exact .jump hdm (.cons hf (tupAppend_rel hlocs hba))
      | cons t rest ih =>
        simp only [emitBrTable]
        rcases LabsRel_getElem?_rel hlabs t with ⟨hn1, hn2⟩ | ⟨l₁, l₂, hs1, hs2, hl⟩
        · simp only [hn1, hn2]
          exact mkTrapExpr_wf retTys 1#32 hf
        · simp only [hs1, hs2]
          rcases hl with ⟨hl_eq, hl_m⟩
          cases l₁ with
          | mk lt₁ ll₁ =>
            cases l₂ with
            | mk lt₂ ll₂ =>
              dsimp only at hl_eq hl_m
              subst hl_eq
              by_cases hlt : lt₁ = dt
              · simp only [hlt, ↓reduceDIte]
                subst hlt
                refine wf_let2 (.cmp .eq T.i32) hidx (.imm _) fun h1 _ _ heq =>
                  .jnz heq (.jump hl_m (.cons (ArgRel.mono h1 hf)
                    (tupAppend_rel (TRel_ArgRel_mono h1 hlocs) (TRel_ArgRel_mono h1 hba))))
                    (ih (TRel_ArgRel_mono h1 hlocs) (ArgRel.mono h1 hf) (ArgRel.mono h1 hidx)
                      (TRel_ArgRel_mono h1 hba) (i + 1))
              · simp only [hlt, ↓reduceDIte]
                exact mkTrapExpr_wf retTys 1#32 hf

theorem lowerSimpleInstr_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} (ctx : WLowerCtx)
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {vc₁ f₁ : Arg V₁ T.i64} {vc₂ f₂ : Arg V₂ T.i64}
    {locs₁ : Tup (Arg V₁) (ctx.locTys.map WValTy.toTy)}
    {locs₂ : Tup (Arg V₂) (ctx.locTys.map WValTy.toTy)}
    {stk₁ : List (SVal V₁)} {stk₂ : List (SVal V₂)}
    {labs₁ : List (WLabel V₁ L₁ ctx.locTys)} {labs₂ : List (WLabel V₂ L₂ ctx.locTys)}
    (instr : WInstr)
    {k₁ : WCont V₁ L₁ ctx.locTys ctx.retTys} {k₂ : WCont V₂ L₂ ctx.locTys ctx.retTys}
    (hvc : ArgRel G T.i64 vc₁ vc₂) (hf : ArgRel G T.i64 f₁ f₂)
    (hlocs : TRel (ArgRel G) locs₁ locs₂) (hstk : StkRel G stk₁ stk₂)
    (hlabs : LabsRel D ctx.locTys labs₁ labs₂) (hk : ContWf ctx.locTys ctx.retTys G D k₁ k₂) :
    Wf G D (lowerSimpleInstr ctx vc₁ f₁ locs₁ stk₁ labs₁ instr k₁)
           (lowerSimpleInstr ctx vc₂ f₂ locs₂ stk₂ labs₂ instr k₂) := by
  have htrap : Wf G D (mkTrapExpr (L := L₁) ctx.retTys 1#32 f₁)
      (mkTrapExpr (L := L₂) ctx.retTys 1#32 f₂) := mkTrapExpr_wf ctx.retTys 1#32 hf
  cases instr with
  | nop => exact hk (fun _ h => h) (fun _ h => h) hf hlocs hstk
  | br_if depth =>
    simp only [lowerSimpleInstr]
    rcases pop32_rel hstk with ⟨hn1, hn2⟩ | ⟨c₁, c₂, r₁, r₂, hp1, hp2, hc, hr⟩
    · simp [hn1, hn2, htrap]
    · simp only [hp1, hp2]
      rcases LabsRel_getElem?_rel hlabs depth with ⟨hn1, hn2⟩ | ⟨l₁, l₂, hs1, hs2, hl⟩
      · simp [hn1, hn2, htrap]
      · simp only [hs1, hs2]
        rcases hl with ⟨har, hm⟩
        cases l₁ with
        | mk lt₁ ll₁ =>
          cases l₂ with
          | mk lt₂ ll₂ =>
            dsimp only at har hm
            subst har
            rcases popArgsAux_rel lt₁ hr with ⟨ha1, ha2⟩ | ⟨b₁, b₂, s₁, s₂, hp1', hp2', hb, _⟩
            · simp [ha1, ha2, htrap]
            · simp only [hp1', hp2']
              exact wf_let2 (.cmp .ne T.i32) hc (.imm _) fun h1 _ _ htk =>
                .jnz htk (.jump hm (.cons (ArgRel.mono h1 hf)
                  (tupAppend_rel (TRel_ArgRel_mono h1 hlocs) (TRel_ArgRel_mono h1 hb))))
                  (hk h1 (fun _ h => h) (ArgRel.mono h1 hf)
                    (TRel_ArgRel_mono h1 hlocs) (StkRel.mono h1 hr))
  | call fnIdx =>
    simp only [lowerSimpleInstr]
    cases hcal : ctx.funcs[fnIdx]? with
    | none => exact htrap
    | some callee =>
      dsimp only
      cases hft : ctx.types[callee.typeIdx]? with
      | none => exact htrap
      | some ft =>
        dsimp only
        rcases popArgsAux_rel ft.params hstk with
          ⟨hn1, hn2⟩ | ⟨a₁, a₂, s₁, s₂, hp1, hp2, ha, hs⟩
        · simp [hn1, hn2, htrap]
        · simp only [hp1, hp2]
          refine wf_let2 (.cmp .eq T.i64) hf (.imm _) fun h1 _ _ ho =>
            .jnz ho (mkTrapExpr_wf ctx.retTys 2#32 (ArgRel.mono h1 hf))
              (wf_let2 (.sub T.i64) (ArgRel.mono h1 hf) (.imm _) fun {G₂} h2 _ _ hfn => ?_)
          have h12 : ∀ p ∈ G, p ∈ G₂ := fun p hp => h2 p (h1 p hp)
          refine .call callee.name (.cons (ArgRel.mono h12 hvc)
            (.cons hfn (TRel_ArgRel_mono h12 ha))) fun res₁ res₂ => ?_
          rcases res₁ with ⟨st₁, rf₁, rets₁⟩
          rcases res₂ with ⟨st₂, rf₂, rets₂⟩
          let Gc := Tup.zip (as := wasmRetSig ft.results) (st₁, rf₁, rets₁) (st₂, rf₂, rets₂) ++
            G₂
          have hG2c : ∀ p ∈ G₂, p ∈ Gc := fun _ hp => List.mem_append_right _ hp
          have hGc : ∀ p ∈ G, p ∈ Gc := fun p hp => hG2c p (h12 p hp)
          have hst : ArgRel Gc T.i32 (.var st₁) (.var st₂) :=
            .var (List.mem_append_left _ List.mem_cons_self)
          have hrf : ArgRel Gc T.i64 (.var rf₁) (.var rf₂) :=
            .var (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
          have hrets : TRel (ArgRel Gc) (varsTup rets₁) (varsTup rets₂) :=
            TRel_ArgRel_mono (fun _ hp => by
              simp only [Gc, Tup.zip] at hp ⊢
              exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp)))
              varsTup_rel_nil
          refine wf_let2 (.cmp .eq T.i32) hst (.imm _) fun h3 _ _ hok =>
            .jnz hok ?_ ?_
          · exact hk (fun p hp => h3 p (hGc p hp)) (fun _ h => h) (ArgRel.mono h3 hrf)
              (TRel_ArgRel_mono (fun p hp => h3 p (hGc p hp)) hlocs)
              (pushArgsAux_rel ft.results (TRel_ArgRel_mono h3 hrets)
                (StkRel.mono (fun p hp => h3 p (hGc p hp)) hs))
          · exact .ret (.cons (ArgRel.mono h3 hst)
              (.cons (ArgRel.mono h3 hrf) (zeroArgs_rel _ ctx.retTys)))
  | drop =>
    simp only [lowerSimpleInstr]
    cases hstk with
    | nil => exact htrap
    | cons _ hrest => exact hk (fun _ h => h) (fun _ h => h) hf hlocs hrest
  | select =>
    simp only [lowerSimpleInstr]
    rcases pop32_rel hstk with ⟨hn1, hn2⟩ | ⟨c₁, c₂, r₁, r₂, hp1, hp2, hc, hr⟩
    · simp [hn1, hn2, htrap]
    · simp only [hp1, hp2]
      rcases popAny_rel hr with ⟨rfl, rfl⟩ | ⟨v₂₁, v₂₂, u₁, u₂, rfl, rfl, hv₂, hr₂⟩
      · exact htrap
      · rcases popAny_rel hr₂ with ⟨rfl, rfl⟩ | ⟨v₁₁, v₁₂, r₃₁, r₃₂, rfl, rfl, hv₁, hr₃⟩
        · cases v₂₁ <;> cases v₂₂ <;> exact htrap
        · cases v₂₁ <;> cases v₂₂ <;> cases v₁₁ <;> cases v₁₂ <;>
            simp only [SValRel] at hv₁ hv₂ <;>
            try exact htrap
          · exact wf_let2 (.cmp .ne T.i32) hc (.imm _) fun h1 _ _ hsb =>
              wf_let3 (.select T.i32) hsb (ArgRel.mono h1 hv₁) (ArgRel.mono h1 hv₂)
                fun h2 _ _ hres =>
                  have h12 : ∀ p ∈ G, p ∈ _ := fun p hp => h2 p (h1 p hp)
                  hk h12 (fun _ h => h) (ArgRel.mono h12 hf) (TRel_ArgRel_mono h12 hlocs)
                    (.cons hres (StkRel.mono h12 hr₃))
          · exact wf_let2 (.cmp .ne T.i32) hc (.imm _) fun h1 _ _ hsb =>
              wf_let3 (.select T.i64) hsb (ArgRel.mono h1 hv₁) (ArgRel.mono h1 hv₂)
                fun h2 _ _ hres =>
                  have h12 : ∀ p ∈ G, p ∈ _ := fun p hp => h2 p (h1 p hp)
                  hk h12 (fun _ h => h) (ArgRel.mono h12 hf) (TRel_ArgRel_mono h12 hlocs)
                    (.cons hres (StkRel.mono h12 hr₃))
  | local_get idx =>
    simp only [lowerSimpleInstr]
    rcases getLocal_rel ctx.locTys idx hlocs with ⟨hn1, hn2⟩ | ⟨v₁, v₂, hs1, hs2, hv⟩
    · simp [hn1, hn2, htrap]
    · simp only [hs1, hs2]
      exact hk (fun _ h => h) (fun _ h => h) hf hlocs (.cons hv hstk)
  | local_set idx =>
    simp only [lowerSimpleInstr]
    cases hstk with
    | nil => exact htrap
    | cons hv hrest =>
      rcases setLocal_rel ctx.locTys idx hlocs hv with ⟨hn1, hn2⟩ | ⟨l₁', l₂', hs1, hs2, hl'⟩
      · simp [hn1, hn2, htrap]
      · simp only [hs1, hs2]
        exact hk (fun _ h => h) (fun _ h => h) hf hl' hrest
  | local_tee idx =>
    simp only [lowerSimpleInstr]
    cases hstk with
    | nil => exact htrap
    | cons hv hrest =>
      rcases setLocal_rel ctx.locTys idx hlocs hv with ⟨hn1, hn2⟩ | ⟨l₁', l₂', hs1, hs2, hl'⟩
      · simp [hn1, hn2, htrap]
      · simp only [hs1, hs2]
        exact hk (fun _ h => h) (fun _ h => h) hf hl' (.cons hv hrest)
  | global_get idx =>
    simp only [lowerSimpleInstr]
    cases hgl : ctx.globals[idx]? with
    | none => exact htrap
    | some g =>
      refine hk (fun _ h => h) (fun _ h => h) hf hlocs (.cons ?_ hstk)
      cases g.ty <;> exact .imm _
  | load resTy width signed arg =>
    simp only [lowerSimpleInstr]
    by_cases hok : (ctx.hasMem && validateLoad resTy width signed) = true
    · simp only [hok, ↓reduceIte]
      rcases pop32_rel hstk with ⟨hn1, hn2⟩ | ⟨i₁, i₂, r₁, r₂, hp1, hp2, hi, hr⟩
      · simp [hn1, hn2, htrap]
      · simp only [hp1, hp2]
        refine emitMemBounds_wf ctx.retTys hvc hf hi arg width.bytes fun h1 p₁ p₂ hp => ?_
        refine .load width.memTy hp fun raw₁ raw₂ => ?_
        have h1' : ∀ q ∈ G, q ∈ (⟨width.memTy, raw₁, raw₂⟩ :: _) :=
          fun q hq => List.mem_cons_of_mem _ (h1 q hq)
        exact emitLoadCast_wf (mkTrapExpr_wf ctx.retTys 1#32 (ArgRel.mono h1' hf))
          resTy width signed raw₁ raw₂ List.mem_cons_self fun h2 y₁ y₂ hy =>
            have h12 : ∀ q ∈ G, q ∈ _ := fun q hq => h2 q (h1' q hq)
            hk h12 (fun _ h => h) (ArgRel.mono h12 hf) (TRel_ArgRel_mono h12 hlocs)
              (.cons (SValRel.ofArg resTy hy) (StkRel.mono h12 hr))
    · simp [hok, htrap]
  | store srcTy width arg =>
    simp only [lowerSimpleInstr]
    by_cases hok : (ctx.hasMem && validateStore srcTy width) = true
    · simp only [hok, ↓reduceIte]
      rcases popExpectS_rel srcTy hstk with ⟨hn1, hn2⟩ | ⟨v₁, v₂, s₁, s₂, hp1, hp2, hv, hs⟩
      · simp [hn1, hn2, htrap]
      · simp only [hp1, hp2]
        rcases pop32_rel hs with ⟨hn1', hn2'⟩ | ⟨i₁, i₂, r₁, r₂, hp1', hp2', hi, hr⟩
        · simp [hn1', hn2', htrap]
        · simp only [hp1', hp2']
          refine emitMemBounds_wf ctx.retTys hvc hf hi arg width.bytes fun h1 p₁ p₂ hp => ?_
          refine emitStoreCast_wf (mkTrapExpr_wf ctx.retTys 1#32 (ArgRel.mono h1 hf))
            srcTy width (ArgRel.mono h1 hv) fun h2 mv₁ mv₂ hmv => ?_
          have h12 : ∀ q ∈ G, q ∈ _ := fun q hq => h2 q (h1 q hq)
          exact .store hmv (ArgRel.mono h2 hp)
            (hk h12 (fun _ h => h) (ArgRel.mono h12 hf) (TRel_ArgRel_mono h12 hlocs)
              (StkRel.mono h12 hr))
    · simp [hok, htrap]
  | memory_size =>
    simp only [lowerSimpleInstr]
    by_cases hm : ctx.hasMem = true
    · simp only [hm, ↓reduceIte]
      exact emitMemSize_wf hvc fun h1 p₁ p₂ hp =>
        hk h1 (fun _ h => h) (ArgRel.mono h1 hf) (TRel_ArgRel_mono h1 hlocs)
          (.cons hp (StkRel.mono h1 hstk))
    · simp [hm, htrap]
  | memory_grow =>
    simp only [lowerSimpleInstr]
    by_cases hm : ctx.hasMem = true
    · simp only [hm, ↓reduceIte]
      rcases pop32_rel hstk with ⟨hn1, hn2⟩ | ⟨d₁, d₂, r₁, r₂, hp1, hp2, hd, hr⟩
      · simp [hn1, hn2, htrap]
      · simp only [hp1, hp2]
        exact emitMemGrow_wf ctx.retTys ctx.memMaxBytes hvc hf hd fun h1 hD1 f₁' f₂' rs₁ rs₂ hf'
          hrs =>
          hk h1 hD1 hf' (TRel_ArgRel_mono h1 hlocs) (.cons hrs (StkRel.mono h1 hr))
    · simp [hm, htrap]
  | memory_fill =>
    simp only [lowerSimpleInstr]
    by_cases hm : ctx.hasMem = true
    · simp only [hm, ↓reduceIte]
      rcases pop32_rel hstk with ⟨hn1, hn2⟩ | ⟨n₁, n₂, s₁, s₂, hp1, hp2, hn, hs1⟩
      · simp [hn1, hn2, htrap]
      · simp only [hp1, hp2]
        rcases pop32_rel hs1 with ⟨hn1', hn2'⟩ | ⟨v₁, v₂, s₁', s₂', hp1', hp2', hv, hs2⟩
        · simp [hn1', hn2', htrap]
        · simp only [hp1', hp2']
          rcases pop32_rel hs2 with ⟨hn1'', hn2''⟩ | ⟨d₁, d₂, r₁, r₂, hp1'', hp2'', hd, hr⟩
          · simp [hn1'', hn2'', htrap]
          · simp only [hp1'', hp2'']
            exact emitMemFill_wf ctx.retTys hvc hf hd hv hn fun h1 hD1 f₁' f₂' hf' =>
              hk h1 hD1 hf' (TRel_ArgRel_mono h1 hlocs) (StkRel.mono h1 hr)
    · simp [hm, htrap]
  | memory_copy =>
    simp only [lowerSimpleInstr]
    by_cases hm : ctx.hasMem = true
    · simp only [hm, ↓reduceIte]
      rcases pop32_rel hstk with ⟨hn1, hn2⟩ | ⟨n₁, n₂, s₁, s₂, hp1, hp2, hn, hs1⟩
      · simp [hn1, hn2, htrap]
      · simp only [hp1, hp2]
        rcases pop32_rel hs1 with ⟨hn1', hn2'⟩ | ⟨s₁', s₂', s₁'', s₂'', hp1', hp2', hs, hs2⟩
        · simp [hn1', hn2', htrap]
        · simp only [hp1', hp2']
          rcases pop32_rel hs2 with ⟨hn1'', hn2''⟩ | ⟨d₁, d₂, r₁, r₂, hp1'', hp2'', hd, hr⟩
          · simp [hn1'', hn2'', htrap]
          · simp only [hp1'', hp2'']
            exact emitMemCopy_wf ctx.retTys hvc hf hd hs hn fun h1 hD1 f₁' f₂' hf' =>
              hk h1 hD1 hf' (TRel_ArgRel_mono h1 hlocs) (StkRel.mono h1 hr)
    · simp [hm, htrap]
  | i32_const _ => exact hk (fun _ h => h) (fun _ h => h) hf hlocs (.cons (.imm _) hstk)
  | i64_const _ => exact hk (fun _ h => h) (fun _ h => h) hf hlocs (.cons (.imm _) hstk)
  | eqz w =>
    simp only [lowerSimpleInstr]
    rcases popAny_rel hstk with ⟨rfl, rfl⟩ | ⟨x₁, x₂, t₁, t₂, rfl, rfl, hv, hrest⟩
    · cases w <;> exact htrap
    · cases w <;> cases x₁ <;> cases x₂ <;> simp only [SValRel] at hv <;> try exact htrap
      · exact wf_let2 (.cmp .eq T.i32) hv (.imm _) fun h1 _ _ hb =>
          wf_let1 (.ofBool 32) hb fun h2 _ _ hr =>
            have h12 : ∀ p ∈ G, p ∈ _ := fun p hp => h2 p (h1 p hp)
            hk h12 (fun _ h => h) (ArgRel.mono h12 hf) (TRel_ArgRel_mono h12 hlocs)
              (.cons hr (StkRel.mono h12 hrest))
      · exact wf_let2 (.cmp .eq T.i64) hv (.imm _) fun h1 _ _ hb =>
          wf_let1 (.ofBool 32) hb fun h2 _ _ hr =>
            have h12 : ∀ p ∈ G, p ∈ _ := fun p hp => h2 p (h1 p hp)
            hk h12 (fun _ h => h) (ArgRel.mono h12 hf) (TRel_ArgRel_mono h12 hlocs)
              (.cons hr (StkRel.mono h12 hrest))
  | unop w op =>
    simp only [lowerSimpleInstr]
    rcases popExpectS_rel w hstk with ⟨hn1, hn2⟩ | ⟨x₁, x₂, r₁, r₂, hp1, hp2, hx, hr⟩
    · simp [hn1, hn2, htrap]
    · simp only [hp1, hp2]
      exact emitUnOp_wf ctx.retTys hf w op hx fun h1 y₁ y₂ hy =>
        hk h1 (fun _ h => h) (ArgRel.mono h1 hf) (TRel_ArgRel_mono h1 hlocs)
          (.cons (SValRel.ofArg w hy) (StkRel.mono h1 hr))
  | binop w op =>
    simp only [lowerSimpleInstr]
    rcases popExpectS_rel w hstk with ⟨hn1, hn2⟩ | ⟨b₁, b₂, s₁, s₂, hp1, hp2, hb, hs⟩
    · simp [hn1, hn2, htrap]
    · simp only [hp1, hp2]
      rcases popExpectS_rel w hs with ⟨hn1', hn2'⟩ | ⟨a₁, a₂, r₁, r₂, hp1', hp2', ha, hr⟩
      · simp [hn1', hn2', htrap]
      · simp only [hp1', hp2']
        exact emitBinOp_wf ctx.retTys hf w op ha hb fun h1 y₁ y₂ hy =>
          hk h1 (fun _ h => h) (ArgRel.mono h1 hf) (TRel_ArgRel_mono h1 hlocs)
            (.cons (SValRel.ofArg w hy) (StkRel.mono h1 hr))
  | relop w op =>
    simp only [lowerSimpleInstr]
    rcases popExpectS_rel w hstk with ⟨hn1, hn2⟩ | ⟨b₁, b₂, s₁, s₂, hp1, hp2, hb, hs⟩
    · simp [hn1, hn2, htrap]
    · simp only [hp1, hp2]
      rcases popExpectS_rel w hs with ⟨hn1', hn2'⟩ | ⟨a₁, a₂, r₁, r₂, hp1', hp2', ha, hr⟩
      · simp [hn1', hn2', htrap]
      · simp only [hp1', hp2']
        cases w
        · exact wf_let2 (.cmp (lowerRelOp op) T.i32) ha hb fun h1 _ _ hcb =>
            wf_let1 (.ofBool 32) hcb fun h2 _ _ hres =>
              have h12 : ∀ p ∈ G, p ∈ _ := fun p hp => h2 p (h1 p hp)
              hk h12 (fun _ h => h) (ArgRel.mono h12 hf) (TRel_ArgRel_mono h12 hlocs)
                (.cons hres (StkRel.mono h12 hr))
        · exact wf_let2 (.cmp (lowerRelOp op) T.i64) ha hb fun h1 _ _ hcb =>
            wf_let1 (.ofBool 32) hcb fun h2 _ _ hres =>
              have h12 : ∀ p ∈ G, p ∈ _ := fun p hp => h2 p (h1 p hp)
              hk h12 (fun _ h => h) (ArgRel.mono h12 hf) (TRel_ArgRel_mono h12 hlocs)
                (.cons hres (StkRel.mono h12 hr))
  | wrap_i64 =>
    simp only [lowerSimpleInstr]
    rcases pop64_rel hstk with ⟨hn1, hn2⟩ | ⟨x₁, x₂, r₁, r₂, hp1, hp2, hx, hr⟩
    · simp [hn1, hn2, htrap]
    · simp only [hp1, hp2]
      exact wf_let1 (.trunc 64 32) hx fun h1 _ _ hres =>
        hk h1 (fun _ h => h) (ArgRel.mono h1 hf) (TRel_ArgRel_mono h1 hlocs)
          (.cons hres (StkRel.mono h1 hr))
  | extend_i32_s =>
    simp only [lowerSimpleInstr]
    rcases pop32_rel hstk with ⟨hn1, hn2⟩ | ⟨x₁, x₂, r₁, r₂, hp1, hp2, hx, hr⟩
    · simp [hn1, hn2, htrap]
    · simp only [hp1, hp2]
      exact wf_let1 (.sext 32 64) hx fun h1 _ _ hres =>
        hk h1 (fun _ h => h) (ArgRel.mono h1 hf) (TRel_ArgRel_mono h1 hlocs)
          (.cons hres (StkRel.mono h1 hr))
  | extend_i32_u =>
    simp only [lowerSimpleInstr]
    rcases pop32_rel hstk with ⟨hn1, hn2⟩ | ⟨x₁, x₂, r₁, r₂, hp1, hp2, hx, hr⟩
    · simp [hn1, hn2, htrap]
    · simp only [hp1, hp2]
      exact wf_let1 (.zext 32 64) hx fun h1 _ _ hres =>
        hk h1 (fun _ h => h) (ArgRel.mono h1 hf) (TRel_ArgRel_mono h1 hlocs)
          (.cons hres (StkRel.mono h1 hr))
  | unreachable => exact htrap
  | block _ _ => exact htrap
  | loop _ _ => exact htrap
  | if_ _ _ _ => exact htrap
  | br _ => exact htrap
  | br_table _ _ => exact htrap
  | return_ => exact htrap

theorem lowerSeq_wf_aux (ctx : WLowerCtx) :
    ∀ (sz : Nat) {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
      {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {vc₁ f₁ : Arg V₁ T.i64} {vc₂ f₂ : Arg V₂ T.i64}
      {locs₁ : Tup (Arg V₁) (ctx.locTys.map WValTy.toTy)}
      {locs₂ : Tup (Arg V₂) (ctx.locTys.map WValTy.toTy)}
      {stk₁ : List (SVal V₁)} {stk₂ : List (SVal V₂)}
      {labs₁ : List (WLabel V₁ L₁ ctx.locTys)} {labs₂ : List (WLabel V₂ L₂ ctx.locTys)}
      (instrs : List WInstr) (_hsz : sizeOf instrs ≤ sz)
      {k₁ : WCont V₁ L₁ ctx.locTys ctx.retTys} {k₂ : WCont V₂ L₂ ctx.locTys ctx.retTys},
      ArgRel G T.i64 vc₁ vc₂ → ArgRel G T.i64 f₁ f₂ →
      TRel (ArgRel G) locs₁ locs₂ → StkRel G stk₁ stk₂ → LabsRel D ctx.locTys labs₁ labs₂ →
      ContWf ctx.locTys ctx.retTys G D k₁ k₂ →
      Wf G D (lowerSeq ctx vc₁ f₁ locs₁ stk₁ labs₁ instrs k₁)
             (lowerSeq ctx vc₂ f₂ locs₂ stk₂ labs₂ instrs k₂) := by
  intro sz
  induction sz using Nat.strongRecOn with
  | _ sz ih =>
    intro V₁ V₂ L₁ L₂ G D vc₁ f₁ vc₂ f₂ locs₁ locs₂ stk₁ stk₂ labs₁ labs₂
      instrs hsz k₁ k₂ hvc hf hlocs hstk hlabs hk
    cases instrs with
    | nil =>
      simp only [lowerSeq]
      exact hk (fun _ h => h) (fun _ h => h) hf hlocs hstk
    | cons i rest =>
      have hszRest : sizeOf rest < sizeOf (i :: rest) := by simp +arith
      cases i with
      | unreachable =>
        simp only [lowerSeq]
        exact mkTrapExpr_wf ctx.retTys 1#32 hf
      | br depth =>
        simp only [lowerSeq]
        rcases LabsRel_getElem?_rel hlabs depth with ⟨hn1, hn2⟩ | ⟨l₁, l₂, hs1, hs2, hl⟩
        · simp [hn1, hn2, mkTrapExpr_wf ctx.retTys 1#32 hf]
        · simp only [hs1, hs2]
          rcases hl with ⟨har, hm⟩
          cases l₁ with
          | mk lt₁ ll₁ =>
            cases l₂ with
            | mk lt₂ ll₂ =>
              dsimp only at har hm
              subst har
              rcases popArgsAux_rel lt₁ hstk with ⟨ha1, ha2⟩ | ⟨b₁, b₂, _, _, hp1, hp2, hb, _⟩
              · simp [ha1, ha2, mkTrapExpr_wf ctx.retTys 1#32 hf]
              · simp only [hp1, hp2]
                exact .jump hm (.cons hf (tupAppend_rel hlocs hb))
      | br_table targets defTarget =>
        simp only [lowerSeq]
        rcases pop32_rel hstk with ⟨hn1, hn2⟩ | ⟨i₁, i₂, r₁, r₂, hp1, hp2, hi, hr⟩
        · simp [hn1, hn2, mkTrapExpr_wf ctx.retTys 1#32 hf]
        · simp only [hp1, hp2]
          rcases LabsRel_getElem?_rel hlabs defTarget with
            ⟨hn1, hn2⟩ | ⟨d₁, d₂, hs1, hs2, hdef⟩
          · simp [hn1, hn2, mkTrapExpr_wf ctx.retTys 1#32 hf]
          · simp only [hs1, hs2]
            have hdeq : d₁.argTys = d₂.argTys := hdef.1
            rcases popArgsAux_rel d₁.argTys hr with
              ⟨ha1, ha2⟩ | ⟨b₁, b₂, _, _, hp1', hp2', hb, _⟩
            · have ha2' : popArgsAux d₂.argTys r₂ = none := by rw [← hdeq]; exact ha2
              simp [ha1, ha2', mkTrapExpr_wf ctx.retTys 1#32 hf]
            · simp only [hp1']
              cases d₁ with
              | mk dt₁ dl₁ =>
                cases d₂ with
                | mk dt₂ dl₂ =>
                  dsimp only at hdeq
                  subst hdeq
                  simp only [hp2']
                  exact emitBrTable_wf ctx.locTys ctx.retTys hlabs hdef rfl hlocs hf hi hb 0
                    targets
      | return_ =>
        simp only [lowerSeq]
        rcases popArgsAux_rel ctx.retTys hstk with
          ⟨ha1, ha2⟩ | ⟨r₁, r₂, _, _, hp1, hp2, hr, _⟩
        · simp [ha1, ha2, mkTrapExpr_wf ctx.retTys 1#32 hf]
        · simp only [hp1, hp2]
          exact .ret (.cons (.imm _) (.cons hf hr))
      | block bt body =>
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => exact mkTrapExpr_wf ctx.retTys 1#32 hf
        | some ft =>
          dsimp only
          rcases popArgsAux_rel ft.params hstk with
            ⟨ha1, ha2⟩ | ⟨ia₁, ia₂, sa₁, sa₂, hp1, hp2, hia, hsa⟩
          · simp [ha1, ha2, mkTrapExpr_wf ctx.retTys 1#32 hf]
          · simp only [hp1, hp2]
            have hszBody : sizeOf body < sz :=
              Nat.lt_of_lt_of_le (by simp +arith) hsz
            have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
            refine .group (sig := [labelSig ctx.locTys ft.results]) ?_ ?_
            · intro ⟨j₁, ()⟩ ⟨j₂, ()⟩
              refine .cons (fun xs₁ xs₂ => ?_) .nil
              rcases xs₁ with ⟨fx₁, xlocs₁⟩
              rcases xs₂ with ⟨fx₂, xlocs₂⟩
              let Gb := Tup.zip (as := labelSig ctx.locTys ft.results)
                (fx₁, xlocs₁) (fx₂, xlocs₂) ++ G
              let Db := Tup.zip (as := [labelSig ctx.locTys ft.results]) (j₁, ()) (j₂, ()) ++ D
              have hGGb : ∀ p ∈ G, p ∈ Gb := fun _ hp => List.mem_append_right _ hp
              have hDDb : ∀ p ∈ D, p ∈ Db := fun _ hp => List.mem_append_right _ hp
              have hfx : ArgRel Gb T.i64 (.var fx₁) (.var fx₂) :=
                .var (List.mem_append_left _ List.mem_cons_self)
              have hvxs : TRel (ArgRel Gb) (varsTup xlocs₁) (varsTup xlocs₂) :=
                TRel_ArgRel_mono (fun _ hp => List.mem_append_left _ (List.mem_cons_of_mem _ hp))
                  varsTup_rel_nil
              have hsp := tupSplit_rel hvxs
              exact ih _ hszRest' rest (Nat.le_refl _)
                (ArgRel.mono hGGb hvc) hfx hsp.1
                (pushArgsAux_rel ft.results hsp.2 (StkRel.mono hGGb hsa))
                (LabsRel.mono hDDb hlabs) (hk.mono hGGb hDDb)
            · intro ⟨j₁, ()⟩ ⟨j₂, ()⟩
              let D' := Tup.zip (as := [labelSig ctx.locTys ft.results]) (j₁, ()) (j₂, ()) ++ D
              have hDD' : ∀ p ∈ D, p ∈ D' := fun _ hp => List.mem_append_right _ hp
              have hj : ⟨labelSig ctx.locTys ft.results, j₁, j₂⟩ ∈ D' :=
                List.mem_append_left _ List.mem_cons_self
              have hlabs' : LabsRel D' ctx.locTys
                  (⟨ft.results, j₁⟩ :: labs₁) (⟨ft.results, j₂⟩ :: labs₂) :=
                .cons ⟨rfl, hj⟩ (LabsRel.mono hDD' hlabs)
              refine ih _ hszBody body (Nat.le_refl _) hvc hf hlocs
                (pushArgsAux_rel ft.params hia .nil) hlabs' ?_
              intro G' D'' hGG' hDD'' fe₁ fe₂ le₁ le₂ se₁ se₂ hfe hle hse
              rcases popArgsAux_rel ft.results hse with
                ⟨hb1, hb2⟩ | ⟨ra₁, ra₂, _, _, hbp1, hbp2, hra, _⟩
              · simp [hb1, hb2, mkTrapExpr_wf ctx.retTys 1#32 hfe]
              · simp only [hbp1, hbp2]
                exact .jump (hDD'' _ hj) (.cons hfe (tupAppend_rel hle hra))
      | loop bt body =>
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => exact mkTrapExpr_wf ctx.retTys 1#32 hf
        | some ft =>
          dsimp only
          rcases popArgsAux_rel ft.params hstk with
            ⟨ha1, ha2⟩ | ⟨ia₁, ia₂, sa₁, sa₂, hp1, hp2, hia, hsa⟩
          · simp [ha1, ha2, mkTrapExpr_wf ctx.retTys 1#32 hf]
          · simp only [hp1, hp2]
            have hszBody : sizeOf body < sz :=
              Nat.lt_of_lt_of_le (by simp +arith) hsz
            have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
            refine .group (sig := [labelSig ctx.locTys ft.results]) ?_ ?_
            · intro ⟨j₁, ()⟩ ⟨j₂, ()⟩
              refine .cons (fun xs₁ xs₂ => ?_) .nil
              rcases xs₁ with ⟨fx₁, xlocs₁⟩
              rcases xs₂ with ⟨fx₂, xlocs₂⟩
              let Gb := Tup.zip (as := labelSig ctx.locTys ft.results)
                (fx₁, xlocs₁) (fx₂, xlocs₂) ++ G
              let Db := Tup.zip (as := [labelSig ctx.locTys ft.results]) (j₁, ()) (j₂, ()) ++ D
              have hGGb : ∀ p ∈ G, p ∈ Gb := fun _ hp => List.mem_append_right _ hp
              have hDDb : ∀ p ∈ D, p ∈ Db := fun _ hp => List.mem_append_right _ hp
              have hfx : ArgRel Gb T.i64 (.var fx₁) (.var fx₂) :=
                .var (List.mem_append_left _ List.mem_cons_self)
              have hvxs : TRel (ArgRel Gb) (varsTup xlocs₁) (varsTup xlocs₂) :=
                TRel_ArgRel_mono (fun _ hp => List.mem_append_left _ (List.mem_cons_of_mem _ hp))
                  varsTup_rel_nil
              have hsp := tupSplit_rel hvxs
              exact ih _ hszRest' rest (Nat.le_refl _)
                (ArgRel.mono hGGb hvc) hfx hsp.1
                (pushArgsAux_rel ft.results hsp.2 (StkRel.mono hGGb hsa))
                (LabsRel.mono hDDb hlabs) (hk.mono hGGb hDDb)
            · intro ⟨ja₁, ()⟩ ⟨ja₂, ()⟩
              let D₁ := Tup.zip (as := [labelSig ctx.locTys ft.results])
                (ja₁, ()) (ja₂, ()) ++ D
              have hDD₁ : ∀ p ∈ D, p ∈ D₁ := fun _ hp => List.mem_append_right _ hp
              have hja : ⟨labelSig ctx.locTys ft.results, ja₁, ja₂⟩ ∈ D₁ :=
                List.mem_append_left _ List.mem_cons_self
              refine .group (sig := [labelSig ctx.locTys ft.params]) ?_ ?_
              · intro ⟨lh₁, ()⟩ ⟨lh₂, ()⟩
                refine .cons (fun xs₁ xs₂ => ?_) .nil
                rcases xs₁ with ⟨fh₁, xlocs₁⟩
                rcases xs₂ with ⟨fh₂, xlocs₂⟩
                let G₁ := Tup.zip (as := labelSig ctx.locTys ft.params)
                  (fh₁, xlocs₁) (fh₂, xlocs₂) ++ G
                let D₂ := Tup.zip (as := [labelSig ctx.locTys ft.params])
                  (lh₁, ()) (lh₂, ()) ++ D₁
                have hGG₁ : ∀ p ∈ G, p ∈ G₁ := fun _ hp => List.mem_append_right _ hp
                have hD₁D₂ : ∀ p ∈ D₁, p ∈ D₂ := fun _ hp => List.mem_append_right _ hp
                have hlh : ⟨labelSig ctx.locTys ft.params, lh₁, lh₂⟩ ∈ D₂ :=
                  List.mem_append_left _ List.mem_cons_self
                have hfh : ArgRel G₁ T.i64 (.var fh₁) (.var fh₂) :=
                  .var (List.mem_append_left _ List.mem_cons_self)
                have hvxs : TRel (ArgRel G₁) (varsTup xlocs₁) (varsTup xlocs₂) :=
                  TRel_ArgRel_mono (fun _ hp =>
                    List.mem_append_left _ (List.mem_cons_of_mem _ hp)) varsTup_rel_nil
                have hsp := tupSplit_rel hvxs
                refine wf_let2 (.cmp .eq T.i64) hfh (.imm _) fun h1 _ _ hiz =>
                  .jnz hiz (mkTrapExpr_wf ctx.retTys 2#32 (ArgRel.mono h1 hfh))
                    (wf_let2 (.sub T.i64) (ArgRel.mono h1 hfh) (.imm _) fun h2 _ _ hfn => ?_)
                have hG₁₂ : ∀ p ∈ G₁, p ∈ _ := fun p hp => h2 p (h1 p hp)
                have hG₂ : ∀ p ∈ G, p ∈ _ := fun p hp => hG₁₂ p (hGG₁ p hp)
                have hlabs₂ : LabsRel D₂ ctx.locTys
                    (⟨ft.params, lh₁⟩ :: labs₁) (⟨ft.params, lh₂⟩ :: labs₂) :=
                  .cons ⟨rfl, hlh⟩ (LabsRel.mono (fun p hp => hD₁D₂ p (hDD₁ p hp)) hlabs)
                refine ih _ hszBody body (Nat.le_refl _)
                  (ArgRel.mono hG₂ hvc) hfn
                  (TRel_ArgRel_mono hG₁₂ hsp.1)
                  (pushArgsAux_rel ft.params (TRel_ArgRel_mono hG₁₂ hsp.2) .nil) hlabs₂ ?_
                intro G' D'' _ hDD'' fe₁ fe₂ le₁ le₂ se₁ se₂ hfe hle hse
                rcases popArgsAux_rel ft.results hse with
                  ⟨hb1, hb2⟩ | ⟨ra₁, ra₂, _, _, hbp1, hbp2, hra, _⟩
                · simp [hb1, hb2, mkTrapExpr_wf ctx.retTys 1#32 hfe]
                · simp only [hbp1, hbp2]
                  exact .jump (hDD'' _ (hD₁D₂ _ hja)) (.cons hfe (tupAppend_rel hle hra))
              · intro ⟨lh₁, ()⟩ ⟨lh₂, ()⟩
                exact .jump (List.mem_append_left _ List.mem_cons_self)
                  (.cons hf (tupAppend_rel hlocs hia))
      | if_ bt thenBody elseBody =>
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => exact mkTrapExpr_wf ctx.retTys 1#32 hf
        | some ft =>
          dsimp only
          rcases pop32_rel hstk with ⟨hc1, hc2⟩ | ⟨c₁, c₂, r₁, r₂, hcp1, hcp2, hc, hr⟩
          · simp [hc1, hc2, mkTrapExpr_wf ctx.retTys 1#32 hf]
          · simp only [hcp1, hcp2]
            rcases popArgsAux_rel ft.params hr with
              ⟨ha1, ha2⟩ | ⟨ia₁, ia₂, sa₁, sa₂, hp1, hp2, hia, hsa⟩
            · simp [ha1, ha2, mkTrapExpr_wf ctx.retTys 1#32 hf]
            · simp only [hp1, hp2]
              have hszT : sizeOf thenBody < sz :=
                Nat.lt_of_lt_of_le (by simp +arith) hsz
              have hszE : sizeOf elseBody < sz :=
                Nat.lt_of_lt_of_le (by simp +arith) hsz
              have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
              refine .group (sig := [labelSig ctx.locTys ft.results]) ?_ ?_
              · intro ⟨j₁, ()⟩ ⟨j₂, ()⟩
                refine .cons (fun xs₁ xs₂ => ?_) .nil
                rcases xs₁ with ⟨fx₁, xlocs₁⟩
                rcases xs₂ with ⟨fx₂, xlocs₂⟩
                let Gb := Tup.zip (as := labelSig ctx.locTys ft.results)
                  (fx₁, xlocs₁) (fx₂, xlocs₂) ++ G
                let Db := Tup.zip (as := [labelSig ctx.locTys ft.results]) (j₁, ()) (j₂, ()) ++ D
                have hGGb : ∀ p ∈ G, p ∈ Gb := fun _ hp => List.mem_append_right _ hp
                have hDDb : ∀ p ∈ D, p ∈ Db := fun _ hp => List.mem_append_right _ hp
                have hfx : ArgRel Gb T.i64 (.var fx₁) (.var fx₂) :=
                  .var (List.mem_append_left _ List.mem_cons_self)
                have hvxs : TRel (ArgRel Gb) (varsTup xlocs₁) (varsTup xlocs₂) :=
                  TRel_ArgRel_mono (fun _ hp =>
                    List.mem_append_left _ (List.mem_cons_of_mem _ hp)) varsTup_rel_nil
                have hsp := tupSplit_rel hvxs
                exact ih _ hszRest' rest (Nat.le_refl _)
                  (ArgRel.mono hGGb hvc) hfx hsp.1
                  (pushArgsAux_rel ft.results hsp.2 (StkRel.mono hGGb hsa))
                  (LabsRel.mono hDDb hlabs) (hk.mono hGGb hDDb)
              · intro ⟨j₁, ()⟩ ⟨j₂, ()⟩
                let D' := Tup.zip (as := [labelSig ctx.locTys ft.results]) (j₁, ()) (j₂, ()) ++ D
                have hDD' : ∀ p ∈ D, p ∈ D' := fun _ hp => List.mem_append_right _ hp
                have hj : ⟨labelSig ctx.locTys ft.results, j₁, j₂⟩ ∈ D' :=
                  List.mem_append_left _ List.mem_cons_self
                have hlabs' : LabsRel D' ctx.locTys
                    (⟨ft.results, j₁⟩ :: labs₁) (⟨ft.results, j₂⟩ :: labs₂) :=
                  .cons ⟨rfl, hj⟩ (LabsRel.mono hDD' hlabs)
                refine wf_let2 (.cmp .ne T.i32) hc (.imm _) fun h1 _ _ hbt => .jnz hbt ?_ ?_
                · refine ih _ hszT thenBody (Nat.le_refl _) (ArgRel.mono h1 hvc)
                    (ArgRel.mono h1 hf) (TRel_ArgRel_mono h1 hlocs)
                    (pushArgsAux_rel ft.params (TRel_ArgRel_mono h1 hia) .nil) hlabs' ?_
                  intro G' D'' _ hDD'' fe₁ fe₂ le₁ le₂ se₁ se₂ hfe hle hse
                  rcases popArgsAux_rel ft.results hse with
                    ⟨hb1, hb2⟩ | ⟨ra₁, ra₂, _, _, hbp1, hbp2, hra, _⟩
                  · simp [hb1, hb2, mkTrapExpr_wf ctx.retTys 1#32 hfe]
                  · simp only [hbp1, hbp2]
                    exact .jump (hDD'' _ hj) (.cons hfe (tupAppend_rel hle hra))
                · refine ih _ hszE elseBody (Nat.le_refl _) (ArgRel.mono h1 hvc)
                    (ArgRel.mono h1 hf) (TRel_ArgRel_mono h1 hlocs)
                    (pushArgsAux_rel ft.params (TRel_ArgRel_mono h1 hia) .nil) hlabs' ?_
                  intro G' D'' _ hDD'' fe₁ fe₂ le₁ le₂ se₁ se₂ hfe hle hse
                  rcases popArgsAux_rel ft.results hse with
                    ⟨hb1, hb2⟩ | ⟨ra₁, ra₂, _, _, hbp1, hbp2, hra, _⟩
                  · simp [hb1, hb2, mkTrapExpr_wf ctx.retTys 1#32 hfe]
                  · simp only [hbp1, hbp2]
                    exact .jump (hDD'' _ hj) (.cons hfe (tupAppend_rel hle hra))
      | _ =>
        -- All remaining constructors go through `lowerSimpleInstr`
        simp only [lowerSeq]
        have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
        refine lowerSimpleInstr_wf ctx _ hvc hf hlocs hstk hlabs ?_
        intro G' D' hGG' hDD' f₁' f₂' l₁' l₂' s₁' s₂' hf' hl' hs'
        exact ih _ hszRest' rest (Nat.le_refl _) (ArgRel.mono hGG' hvc)
          hf' hl' hs' (LabsRel.mono hDD' hlabs) (hk.mono hGG' hDD')

theorem lowerFuncBody_wf (m : WModule) (f : WFunc) (ft : WFuncTy) :
    (lowerFuncBody m f ft).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  rcases xs₁ with ⟨vc₁, f₁, ps₁⟩
  rcases xs₂ with ⟨vc₂, f₂, ps₂⟩
  simp only [lowerFuncBody]
  let ctx : WLowerCtx :=
    { types := m.types, funcs := m.funcs, hasMem := m.memory.isSome,
      memMaxBytes := (m.memory.map WMemSpec.maxBytes).getD 0#64,
      globals := m.globals, locTys := ft.params ++ f.locals, retTys := ft.results }
  refine .group (sig := [labelSig ctx.locTys ft.results]) ?_ ?_
  · intro ⟨j₁, ()⟩ ⟨j₂, ()⟩
    refine .cons (fun rxs₁ rxs₂ => ?_) .nil
    rcases rxs₁ with ⟨rf₁, rlocs₁⟩
    rcases rxs₂ with ⟨rf₂, rlocs₂⟩
    let G₀ := Tup.zip (as := wasmAbiParams ft) (vc₁, f₁, ps₁) (vc₂, f₂, ps₂)
    let Gr := Tup.zip (as := labelSig ctx.locTys ft.results) (rf₁, rlocs₁) (rf₂, rlocs₂) ++ G₀
    have hsp := tupSplit_rel (G := Gr) (as := ctx.locTys.map WValTy.toTy)
      (bs := ft.results.map WValTy.toTy)
      (TRel_ArgRel_mono (fun _ hp => List.mem_append_left _ (List.mem_cons_of_mem _ hp))
        varsTup_rel_nil)
    exact .ret (.cons (.imm _) (.cons (.var (List.mem_append_left _ List.mem_cons_self)) hsp.2))
  · intro ⟨j₁, ()⟩ ⟨j₂, ()⟩
    let G₀ := Tup.zip (as := wasmAbiParams ft) (vc₁, f₁, ps₁) (vc₂, f₂, ps₂)
    let D₀ := Tup.zip (as := [labelSig ctx.locTys ft.results]) (j₁, ()) (j₂, ())
    have hvc : ArgRel G₀ T.i64 (.var vc₁) (.var vc₂) := .var List.mem_cons_self
    have hf : ArgRel G₀ T.i64 (.var f₁) (.var f₂) :=
      .var (List.mem_cons_of_mem _ List.mem_cons_self)
    have hps : TRel (ArgRel G₀) (varsTup ps₁) (varsTup ps₂) :=
      TRel_ArgRel_mono (fun _ hp => by
        simp only [G₀, Tup.zip] at hp ⊢
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
        varsTup_rel_nil
    have hlocs := appendZeroLocals_rel ft.params f.locals hps
    have hj : ⟨labelSig ctx.locTys ft.results, j₁, j₂⟩ ∈ D₀ := List.mem_cons_self
    refine lowerSeq_wf_aux ctx (sizeOf f.body) f.body (Nat.le_refl _) hvc hf hlocs .nil
      (.cons ⟨rfl, hj⟩ .nil) ?_
    intro G' D' _ _ fe₁ fe₂ _ _ se₁ se₂ hfe _ hse
    rcases popArgsAux_rel ft.results hse with
      ⟨hn1, hn2⟩ | ⟨ra₁, ra₂, _, _, hp1, hp2, hra, _⟩
    · simp [hn1, hn2, mkTrapExpr_wf ft.results 1#32 hfe]
    · simp only [hp1, hp2]
      exact .ret (.cons (.imm _) (.cons hfe hra))

/-- Universal well-formedness: every lowered function in `lowerModule m` satisfies `Fn.Wf`. -/
theorem lowerModule_wf (m : WModule) : ∀ fn ∈ (lowerModule m).fns, fn.Wf := by
  intro fn hmem
  simp only [lowerModule, List.mem_map] at hmem
  rcases hmem with ⟨f, _, rfl⟩
  exact lowerFuncBody_wf m f _

/-- Lowered function names are pairwise distinct whenever `validateModule m = true`. -/
theorem lowerModule_namesNodup {m : WModule} (hv : validateModule m = true) :
    (lowerModule m).namesNodup := by
  have hnd := (validateModule_elim hv).1
  simpa [Module.namesNodup, Module.names, lowerModule, Function.comp_def, lowerFn] using hnd

end WfProofs

/-! ## Target-Independent Supportability (`supportsSource`) & Signature Legality -/

section SupportsSourceProofs

theorem emitPopcnt_ss {lt : LegalTarget} (hv : lt.valid = true) {rs : List Ty}
    (w : WValTy) (x : Arg K w.toTy) (k : Arg K w.toTy → Expr K KL rs)
    (hk : ∀ y nv' nl', (toTFlat (k y) nv' nl').supportsSource lt = true) :
    ∀ nv nl, (toTFlat (emitPopcnt w x k) nv nl).supportsSource lt = true := by
  intro nv nl
  have h32 : lt.supportsTy (.bits 32) = true := supportsTy_le64 hv (by omega)
  have h64 : lt.supportsTy (.bits 64) = true := supportsTy_le64 hv (by omega)
  cases w <;> simp only [emitPopcnt]
  · repeat first
      | exact hk _ _ _
      | refine tflat_let2_ss lt _ _ _
          (by simp [LegalTarget.supportsOpCode]; repeat first | exact h32 | constructor) ?_
  · repeat first
      | exact hk _ _ _
      | refine tflat_let2_ss lt _ _ _
          (by simp [LegalTarget.supportsOpCode]; repeat first | exact h64 | constructor) ?_

theorem emitUnOp_ss {lt : LegalTarget} (hv : lt.valid = true) (retTys : List WValTy)
    (f : Arg K T.i64) (w : WValTy) (op : WUnOp) (x : Arg K w.toTy)
    (k : Arg K w.toTy → Expr K KL (wasmRetSig retTys))
    (hk : ∀ y nv' nl', (toTFlat (k y) nv' nl').supportsSource lt = true) :
    ∀ nv nl, (toTFlat (emitUnOp retTys f w op x k) nv nl).supportsSource lt = true := by
  intro nv nl
  have h8 : lt.supportsTy (.bits 8) = true := supportsTy_le64 hv (by omega)
  have h16 : lt.supportsTy (.bits 16) = true := supportsTy_le64 hv (by omega)
  have h32 : lt.supportsTy (.bits 32) = true := supportsTy_le64 hv (by omega)
  have h64 : lt.supportsTy (.bits 64) = true := supportsTy_le64 hv (by omega)
  cases w <;> cases op
  · exact tflat_let1_ss lt (.clz 32) x (by simp [LegalTarget.supportsOpCode, h32]) (hk _ _ _)
  · exact tflat_let1_ss lt (.ctz 32) x (by simp [LegalTarget.supportsOpCode, h32]) (hk _ _ _)
  · exact emitPopcnt_ss hv .i32 x k hk nv nl
  · refine tflat_let1_ss lt (.trunc 32 8) x
      (by simp [LegalTarget.supportsOpCode, h32, h8]) ?_
    exact tflat_let1_ss lt (.sext 8 32) _
      (by simp [LegalTarget.supportsOpCode, h32, h8]) (hk _ _ _)
  · refine tflat_let1_ss lt (.trunc 32 16) x
      (by simp [LegalTarget.supportsOpCode, h32, h16]) ?_
    exact tflat_let1_ss lt (.sext 16 32) _
      (by simp [LegalTarget.supportsOpCode, h32, h16]) (hk _ _ _)
  · exact mkTrapExpr_ss hv retTys 1#32 f nv nl
  · exact tflat_let1_ss lt (.clz 64) x (by simp [LegalTarget.supportsOpCode, h64]) (hk _ _ _)
  · exact tflat_let1_ss lt (.ctz 64) x (by simp [LegalTarget.supportsOpCode, h64]) (hk _ _ _)
  · exact emitPopcnt_ss hv .i64 x k hk nv nl
  · refine tflat_let1_ss lt (.trunc 64 8) x
      (by simp [LegalTarget.supportsOpCode, h64, h8]) ?_
    exact tflat_let1_ss lt (.sext 8 64) _
      (by simp [LegalTarget.supportsOpCode, h64, h8]) (hk _ _ _)
  · refine tflat_let1_ss lt (.trunc 64 16) x
      (by simp [LegalTarget.supportsOpCode, h64, h16]) ?_
    exact tflat_let1_ss lt (.sext 16 64) _
      (by simp [LegalTarget.supportsOpCode, h64, h16]) (hk _ _ _)
  · refine tflat_let1_ss lt (.trunc 64 32) x
      (by simp [LegalTarget.supportsOpCode, h64, h32]) ?_
    exact tflat_let1_ss lt (.sext 32 64) _
      (by simp [LegalTarget.supportsOpCode, h64, h32]) (hk _ _ _)

theorem emitBinOp_ss {lt : LegalTarget} (hv : lt.valid = true) (retTys : List WValTy)
    (f : Arg K T.i64) (w : WValTy) (op : WBinOp) (a b : Arg K w.toTy)
    (k : Arg K w.toTy → Expr K KL (wasmRetSig retTys))
    (hk : ∀ y nv' nl', (toTFlat (k y) nv' nl').supportsSource lt = true) :
    ∀ nv nl,
      (toTFlat (emitBinOp retTys f w op a b k) nv nl).supportsSource lt = true := by
  intro nv nl
  have h32 : lt.supportsTy (.bits 32) = true := supportsTy_le64 hv (by omega)
  have h64 : lt.supportsTy (.bits 64) = true := supportsTy_le64 hv (by omega)
  cases op <;> cases w <;>
  first
  | exact tflat_let2_ss lt _ a b
      (by simp [LegalTarget.supportsOpCode]; repeat first | exact h32 | exact h64 | constructor)
      (hk _ _ _)
  | (refine tflat_let2_ss lt _ _ _ ?_ ?_
     · simp [LegalTarget.supportsOpCode]; first | exact h32 | exact h64
     simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true]
     refine ⟨wasmRetSig_supportsTy hv retTys,
       by simp [LegalTarget.supportsOpCode]; first | exact h32 | exact h64, ?_⟩
     apply hk)
  | (refine tflat_let2_ss lt _ _ _ ?_ ?_
     · simp [LegalTarget.supportsOpCode]; first | exact h32 | exact h64
     simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true]
     refine ⟨wasmRetSig_supportsTy hv retTys,
       by simp [LegalTarget.supportsOpCode]; first | exact h32 | exact h64,
       by simp [LegalTarget.supportsOpCode]; first | exact h32 | exact h64,
       by simp [LegalTarget.supportsOpCode, LegalTarget.supportsTy],
       wasmRetSig_supportsTy hv retTys,
       by simp [LegalTarget.supportsOpCode]; first | exact h32 | exact h64, ?_⟩
     apply hk)
  | (refine tflat_let2_ss lt _ _ _ ?_ ?_
     · simp [LegalTarget.supportsOpCode]; first | exact h32 | exact h64
     simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true]
     refine ⟨wasmRetSig_supportsTy hv retTys,
       by simp [LegalTarget.supportsOpCode]; first | exact h32 | exact h64,
       by simp [LegalTarget.supportsOpCode]; first | exact h32 | exact h64,
       by simp [LegalTarget.supportsOpCode, LegalTarget.supportsTy],
       ?_, by simp [LegalTarget.supportsOpCode]; first | exact h32 | exact h64, ?_⟩
     · apply hk
     · apply hk)

theorem emitLoadCast_ss {lt : LegalTarget} (hv : lt.valid = true) {rs : List Ty}
    {trap : Expr K KL rs} (htrap : ∀ nv nl, (toTFlat trap nv nl).supportsSource lt = true)
    (resTy : WValTy) (width : WMemWidth) (signed : Bool) (raw : K width.memTy)
    (k : Arg K resTy.toTy → Expr K KL rs)
    (hk : ∀ y nv' nl', (toTFlat (k y) nv' nl').supportsSource lt = true) :
    ∀ nv nl,
      (toTFlat (emitLoadCast trap resTy width signed raw k) nv nl).supportsSource lt =
        true := by
  intro nv nl
  have h8 : lt.supportsTy (.bits 8) = true := supportsTy_le64 hv (by omega)
  have h16 : lt.supportsTy (.bits 16) = true := supportsTy_le64 hv (by omega)
  have h32 : lt.supportsTy (.bits 32) = true := supportsTy_le64 hv (by omega)
  have h64 : lt.supportsTy (.bits 64) = true := supportsTy_le64 hv (by omega)
  cases resTy <;> cases width <;> cases signed <;>
  first
  | exact htrap nv nl
  | exact hk _ nv nl
  | exact tflat_let1_ss lt _ _
      (by simp [LegalTarget.supportsOpCode];
          repeat first | exact h8 | exact h16 | exact h32 | exact h64 | constructor)
      (hk _ _ _)

theorem emitStoreCast_ss {lt : LegalTarget} (hv : lt.valid = true) {rs : List Ty}
    {trap : Expr K KL rs} (htrap : ∀ nv nl, (toTFlat trap nv nl).supportsSource lt = true)
    (srcTy : WValTy) (width : WMemWidth) (v : Arg K srcTy.toTy)
    (k : Arg K width.memTy → Expr K KL rs)
    (hk : ∀ y nv' nl', (toTFlat (k y) nv' nl').supportsSource lt = true) :
    ∀ nv nl,
      (toTFlat (emitStoreCast trap srcTy width v k) nv nl).supportsSource lt = true := by
  intro nv nl
  have h8 : lt.supportsTy (.bits 8) = true := supportsTy_le64 hv (by omega)
  have h16 : lt.supportsTy (.bits 16) = true := supportsTy_le64 hv (by omega)
  have h32 : lt.supportsTy (.bits 32) = true := supportsTy_le64 hv (by omega)
  have h64 : lt.supportsTy (.bits 64) = true := supportsTy_le64 hv (by omega)
  cases srcTy <;> cases width <;>
  first
  | exact htrap nv nl
  | exact hk _ nv nl
  | exact tflat_let1_ss lt _ _
      (by simp [LegalTarget.supportsOpCode];
          repeat first | exact h8 | exact h16 | exact h32 | exact h64 | constructor)
      (hk _ _ _)

theorem emitBrTable_ss {lt : LegalTarget} (hv : lt.valid = true) (locTys retTys : List WValTy)
    (labs : List (WLabel K KL locTys)) (locs : Tup (Arg K) (locTys.map WValTy.toTy))
    (f : Arg K T.i64) (idx : Arg K T.i32) (defLbl : WLabel K KL locTys)
    (ba : Tup (Arg K) (defLbl.argTys.map WValTy.toTy)) :
    ∀ (i : Nat) (ts : List Nat) (nv nl : Nat),
      (toTFlat (emitBrTable locTys retTys labs locs f idx defLbl ba i ts) nv nl).supportsSource lt =
        true := by
  intro i ts
  induction ts generalizing i with
  | nil =>
    intro nv nl
    simpa [emitBrTable, toTFlat, TFlat.supportsSource] using
      labelSig_supportsTy hv locTys defLbl.argTys
  | cons t rest ih =>
    intro nv nl
    simp only [emitBrTable]
    cases labs[t]? with
    | none => exact mkTrapExpr_ss hv retTys 1#32 f nv nl
    | some l =>
      by_cases hlt : l.argTys = defLbl.argTys
      · simp only [hlt, ↓reduceDIte]
        have h32 : lt.supportsTy (.bits 32) = true := supportsTy_le64 hv (by omega)
        refine tflat_let2_ss lt (.cmp .eq T.i32) idx (.imm _)
          (by simp [LegalTarget.supportsOpCode, h32]) ?_
        simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true]
        refine ⟨?_, ih (i + 1) _ _⟩
        simpa [TFlat.supportsSource, hlt] using labelSig_supportsTy hv locTys defLbl.argTys
      · simp only [hlt, ↓reduceDIte]
        exact mkTrapExpr_ss hv retTys 1#32 f nv nl

theorem lowerSimpleInstr_ss {lt : LegalTarget} (hv : lt.valid = true) (ctx : WLowerCtx)
    (vc f : Arg K T.i64) (locs : Tup (Arg K) (ctx.locTys.map WValTy.toTy))
    (stk : List (SVal K)) (labs : List (WLabel K KL ctx.locTys)) (instr : WInstr)
    (k : WCont K KL ctx.locTys ctx.retTys)
    (hk : ∀ f' l' s' nv' nl', (toTFlat (k f' l' s') nv' nl').supportsSource lt = true) :
    ∀ nv nl,
      (toTFlat (lowerSimpleInstr ctx vc f locs stk labs instr k) nv nl).supportsSource lt =
        true := by
  intro nv nl
  have h8 : lt.supportsTy (.bits 8) = true := supportsTy_le64 hv (by omega)
  have h16 : lt.supportsTy (.bits 16) = true := supportsTy_le64 hv (by omega)
  have h32 : lt.supportsTy (.bits 32) = true := supportsTy_le64 hv (by omega)
  have h64 : lt.supportsTy (.bits 64) = true := supportsTy_le64 hv (by omega)
  have htrap : ∀ nv' nl',
      (toTFlat (mkTrapExpr (L := KL) ctx.retTys 1#32 f) nv' nl').supportsSource lt = true :=
    fun nv' nl' => mkTrapExpr_ss hv ctx.retTys 1#32 f nv' nl'
  cases instr with
  | nop => exact hk f locs stk nv nl
  | br_if depth =>
    simp only [lowerSimpleInstr]
    cases pop32 stk with
    | none => exact htrap nv nl
    | some p =>
      rcases p with ⟨c, r⟩
      cases labs[depth]? with
      | none => exact htrap nv nl
      | some l =>
        dsimp only
        cases popArgsAux l.argTys r with
        | none => exact htrap nv nl
        | some p' =>
          rcases p' with ⟨ba, _⟩
          dsimp only
          refine tflat_let2_ss lt (.cmp .ne T.i32) c (.imm _)
            (by simp [LegalTarget.supportsOpCode, h32]) ?_
          simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true]
          refine ⟨?_, hk f locs r _ _⟩
          simpa [TFlat.supportsSource] using labelSig_supportsTy hv ctx.locTys l.argTys
  | call fnIdx =>
    simp only [lowerSimpleInstr]
    cases hcal : ctx.funcs[fnIdx]? with
    | none => exact htrap nv nl
    | some callee =>
      dsimp only
      cases hft : ctx.types[callee.typeIdx]? with
      | none => exact htrap nv nl
      | some ft =>
        dsimp only
        cases popArgsAux ft.params stk with
        | none => exact htrap nv nl
        | some p =>
          rcases p with ⟨ca, s1⟩
          dsimp only
          refine tflat_let2_ss lt (.cmp .eq T.i64) f (.imm _)
            (by simp [LegalTarget.supportsOpCode, h64]) ?_
          simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true]
          refine ⟨wasmRetSig_supportsTy hv ctx.retTys,
            by simp [LegalTarget.supportsOpCode, h64],
            ⟨wasmAbiParams_supportsTy hv ft, wasmRetSig_supportsTy hv ft.results⟩,
            by simp [LegalTarget.supportsOpCode, h32],
            by apply hk,
            wasmRetSig_supportsTy hv ctx.retTys⟩
  | drop =>
    simp only [lowerSimpleInstr]
    cases stk with
    | nil => exact htrap nv nl
    | cons _ r => exact hk f locs r nv nl
  | select =>
    simp only [lowerSimpleInstr]
    cases pop32 stk with
    | none => exact htrap nv nl
    | some p =>
      rcases p with ⟨c, r⟩
      cases r with
      | nil => exact htrap nv nl
      | cons v₂ r2 =>
        cases r2 with
        | nil => cases v₂ <;> exact htrap nv nl
        | cons v₁ r3 =>
          cases v₂ <;> cases v₁
          · refine tflat_let2_ss lt (.cmp .ne T.i32) c (.imm _)
              (by simp [LegalTarget.supportsOpCode, h32]) ?_
            exact tflat_let3_ss lt (.select T.i32) _ _ _
              (by simp [LegalTarget.supportsOpCode, h32]) (hk f locs _ _ _)
          · exact htrap nv nl
          · exact htrap nv nl
          · refine tflat_let2_ss lt (.cmp .ne T.i32) c (.imm _)
              (by simp [LegalTarget.supportsOpCode, h32]) ?_
            exact tflat_let3_ss lt (.select T.i64) _ _ _
              (by simp [LegalTarget.supportsOpCode, h64]) (hk f locs _ _ _)
  | local_get idx =>
    simp only [lowerSimpleInstr]
    cases getLocal ctx.locTys locs idx with
    | none => exact htrap nv nl
    | some v => exact hk f locs (v :: stk) nv nl
  | local_set idx =>
    simp only [lowerSimpleInstr]
    cases stk with
    | nil => exact htrap nv nl
    | cons v r =>
      dsimp only
      cases setLocal ctx.locTys locs idx v with
      | none => exact htrap nv nl
      | some locs' => exact hk f locs' r nv nl
  | local_tee idx =>
    simp only [lowerSimpleInstr]
    cases stk with
    | nil => exact htrap nv nl
    | cons v r =>
      dsimp only
      cases setLocal ctx.locTys locs idx v with
      | none => exact htrap nv nl
      | some locs' => exact hk f locs' (v :: r) nv nl
  | global_get idx =>
    simp only [lowerSimpleInstr]
    cases ctx.globals[idx]? with
    | none => exact htrap nv nl
    | some g => exact hk f locs _ nv nl
  | load resTy width signed arg =>
    simp only [lowerSimpleInstr]
    by_cases hok : (ctx.hasMem && validateLoad resTy width signed) = true
    · simp only [hok, ↓reduceIte]
      cases pop32 stk with
      | none => exact htrap nv nl
      | some p =>
        rcases p with ⟨i, r⟩
        dsimp only
        refine emitMemBounds_ss hv ctx.retTys vc f i arg width.bytes _
          (fun ptr nv' nl' => ?_) nv nl
        simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true]
        have hwm : lt.supportsTy width.memTy = true := by
          cases width <;> simp [WMemWidth.memTy, h8, h16, h32, h64]
        have hwb : decide (width.memTy.bytes ≤ 2 ^ 64) = true := by cases width <;> rfl
        refine ⟨⟨hwm, hwb⟩, ?_⟩
        exact emitLoadCast_ss hv htrap resTy width signed _ _
          (fun v nv'' nl'' => hk f locs _ nv'' nl'') _ _
    · simp only [hok, Bool.false_eq_true, ↓reduceIte]; exact htrap nv nl
  | store srcTy width arg =>
    simp only [lowerSimpleInstr]
    by_cases hok : (ctx.hasMem && validateStore srcTy width) = true
    · simp only [hok, ↓reduceIte]
      cases popExpectS srcTy stk with
      | none => exact htrap nv nl
      | some p =>
        rcases p with ⟨v, r⟩
        dsimp only
        cases pop32 r with
        | none => exact htrap nv nl
        | some p' =>
          rcases p' with ⟨i, r2⟩
          dsimp only
          refine emitMemBounds_ss hv ctx.retTys vc f i arg width.bytes _
            (fun ptr nv' nl' => ?_) nv nl
          refine emitStoreCast_ss hv htrap srcTy width v _ (fun mv nv'' nl'' => ?_) nv' nl'
          simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true]
          have hwm : lt.supportsTy width.memTy = true := by
            cases width <;> simp [WMemWidth.memTy, h8, h16, h32, h64]
          have hwb : decide (width.memTy.bytes ≤ 2 ^ 64) = true := by cases width <;> rfl
          exact ⟨⟨hwm, hwb⟩, hk f locs r2 nv'' nl''⟩
    · simp only [hok, Bool.false_eq_true, ↓reduceIte]; exact htrap nv nl
  | memory_size =>
    simp only [lowerSimpleInstr]
    by_cases hm : ctx.hasMem = true
    · simp only [hm, ↓reduceIte]
      exact emitMemSize_ss hv vc _ (fun _ nv' nl' => hk f locs _ nv' nl') nv nl
    · simp only [hm, Bool.false_eq_true, ↓reduceIte]; exact htrap nv nl
  | memory_grow =>
    simp only [lowerSimpleInstr]
    by_cases hm : ctx.hasMem = true
    · simp only [hm, ↓reduceIte]
      cases pop32 stk with
      | none => exact htrap nv nl
      | some p =>
        rcases p with ⟨d, r⟩
        dsimp only
        exact emitMemGrow_ss hv ctx.retTys ctx.memMaxBytes vc f d _
          (fun f' _ nv' nl' => hk f' locs _ nv' nl') nv nl
    · simp only [hm, Bool.false_eq_true, ↓reduceIte]; exact htrap nv nl
  | memory_fill =>
    simp only [lowerSimpleInstr]
    by_cases hm : ctx.hasMem = true
    · simp only [hm, ↓reduceIte]
      cases pop32 stk with
      | none => exact htrap nv nl
      | some p1 =>
        rcases p1 with ⟨n, r1⟩
        dsimp only
        cases pop32 r1 with
        | none => exact htrap nv nl
        | some p2 =>
          rcases p2 with ⟨v, r2⟩
          dsimp only
          cases pop32 r2 with
          | none => exact htrap nv nl
          | some p3 =>
            rcases p3 with ⟨d, r3⟩
            dsimp only
            exact emitMemFill_ss hv ctx.retTys vc f d v n _
              (fun f' nv' nl' => hk f' locs r3 nv' nl') nv nl
    · simp only [hm, Bool.false_eq_true, ↓reduceIte]; exact htrap nv nl
  | memory_copy =>
    simp only [lowerSimpleInstr]
    by_cases hm : ctx.hasMem = true
    · simp only [hm, ↓reduceIte]
      cases pop32 stk with
      | none => exact htrap nv nl
      | some p1 =>
        rcases p1 with ⟨n, r1⟩
        dsimp only
        cases pop32 r1 with
        | none => exact htrap nv nl
        | some p2 =>
          rcases p2 with ⟨s, r2⟩
          dsimp only
          cases pop32 r2 with
          | none => exact htrap nv nl
          | some p3 =>
            rcases p3 with ⟨d, r3⟩
            dsimp only
            exact emitMemCopy_ss hv ctx.retTys vc f d s n _
              (fun f' nv' nl' => hk f' locs r3 nv' nl') nv nl
    · simp only [hm, Bool.false_eq_true, ↓reduceIte]; exact htrap nv nl
  | i32_const _ => exact hk f locs _ nv nl
  | i64_const _ => exact hk f locs _ nv nl
  | eqz w =>
    simp only [lowerSimpleInstr]
    cases w with
    | i32 =>
      cases stk with
      | nil => exact htrap nv nl
      | cons x r =>
        cases x with
        | i32 v =>
          refine tflat_let2_ss lt (.cmp .eq T.i32) v (.imm _)
            (by simp [LegalTarget.supportsOpCode, h32]) ?_
          exact tflat_let1_ss lt (.ofBool 32) _
            (by simp [LegalTarget.supportsOpCode, h32]) (hk f locs _ _ _)
        | i64 _ => exact htrap nv nl
    | i64 =>
      cases stk with
      | nil => exact htrap nv nl
      | cons x r =>
        cases x with
        | i32 _ => exact htrap nv nl
        | i64 v =>
          refine tflat_let2_ss lt (.cmp .eq T.i64) v (.imm _)
            (by simp [LegalTarget.supportsOpCode, h64]) ?_
          exact tflat_let1_ss lt (.ofBool 32) _
            (by simp [LegalTarget.supportsOpCode, h32]) (hk f locs _ _ _)
  | unop w op =>
    simp only [lowerSimpleInstr]
    cases popExpectS w stk with
    | none => exact htrap nv nl
    | some p =>
      rcases p with ⟨x, r⟩
      dsimp only
      exact emitUnOp_ss hv ctx.retTys f w op x _ (fun _ nv' nl' => hk f locs _ nv' nl') nv nl
  | binop w op =>
    simp only [lowerSimpleInstr]
    cases popExpectS w stk with
    | none => exact htrap nv nl
    | some p =>
      rcases p with ⟨b, r1⟩
      dsimp only
      cases popExpectS w r1 with
      | none => exact htrap nv nl
      | some p' =>
        rcases p' with ⟨a, r2⟩
        dsimp only
        exact emitBinOp_ss hv ctx.retTys f w op a b _
          (fun _ nv' nl' => hk f locs _ nv' nl') nv nl
  | relop w op =>
    simp only [lowerSimpleInstr]
    cases popExpectS w stk with
    | none => exact htrap nv nl
    | some p =>
      rcases p with ⟨b, r1⟩
      dsimp only
      cases popExpectS w r1 with
      | none => exact htrap nv nl
      | some p' =>
        rcases p' with ⟨a, r2⟩
        dsimp only
        cases w
        · refine tflat_let2_ss lt (.cmp (lowerRelOp op) T.i32) a b
            (by simp [LegalTarget.supportsOpCode, h32]) ?_
          exact tflat_let1_ss lt (.ofBool 32) _
            (by simp [LegalTarget.supportsOpCode, h32]) (hk f locs _ _ _)
        · refine tflat_let2_ss lt (.cmp (lowerRelOp op) T.i64) a b
            (by simp [LegalTarget.supportsOpCode, h64]) ?_
          exact tflat_let1_ss lt (.ofBool 32) _
            (by simp [LegalTarget.supportsOpCode, h32]) (hk f locs _ _ _)
  | wrap_i64 =>
    simp only [lowerSimpleInstr]
    cases pop64 stk with
    | none => exact htrap nv nl
    | some p =>
      rcases p with ⟨x, r⟩
      dsimp only
      exact tflat_let1_ss lt (.trunc 64 32) x
        (by simp [LegalTarget.supportsOpCode, h64, h32]) (hk f locs _ _ _)
  | extend_i32_s =>
    simp only [lowerSimpleInstr]
    cases pop32 stk with
    | none => exact htrap nv nl
    | some p =>
      rcases p with ⟨x, r⟩
      dsimp only
      exact tflat_let1_ss lt (.sext 32 64) x
        (by simp [LegalTarget.supportsOpCode, h32, h64]) (hk f locs _ _ _)
  | extend_i32_u =>
    simp only [lowerSimpleInstr]
    cases pop32 stk with
    | none => exact htrap nv nl
    | some p =>
      rcases p with ⟨x, r⟩
      dsimp only
      exact tflat_let1_ss lt (.zext 32 64) x
        (by simp [LegalTarget.supportsOpCode, h32, h64]) (hk f locs _ _ _)
  | unreachable => exact htrap nv nl
  | block _ _ => exact htrap nv nl
  | loop _ _ => exact htrap nv nl
  | if_ _ _ _ => exact htrap nv nl
  | br _ => exact htrap nv nl
  | br_table _ _ => exact htrap nv nl
  | return_ => exact htrap nv nl

theorem lowerSeq_ss_aux {lt : LegalTarget} (hv : lt.valid = true) (ctx : WLowerCtx) :
    ∀ (sz : Nat) (vc f : Arg K T.i64) (locs : Tup (Arg K) (ctx.locTys.map WValTy.toTy))
      (stk : List (SVal K)) (labs : List (WLabel K KL ctx.locTys))
      (instrs : List WInstr) (_hsz : sizeOf instrs ≤ sz)
      (k : WCont K KL ctx.locTys ctx.retTys),
      (∀ f' l' s' nv' nl', (toTFlat (k f' l' s') nv' nl').supportsSource lt = true) →
      ∀ nv nl,
        (toTFlat (lowerSeq ctx vc f locs stk labs instrs k) nv nl).supportsSource lt = true := by
  intro sz
  induction sz using Nat.strongRecOn with
  | _ sz ih =>
    intro vc f locs stk labs instrs hsz k hk nv nl
    have htrap : ∀ nv' nl',
        (toTFlat (mkTrapExpr (L := KL) ctx.retTys 1#32 f) nv' nl').supportsSource lt = true :=
      fun nv' nl' => mkTrapExpr_ss hv ctx.retTys 1#32 f nv' nl'
    have h64 : lt.supportsTy (.bits 64) = true := supportsTy_le64 hv (by omega)
    have h32 : lt.supportsTy (.bits 32) = true := supportsTy_le64 hv (by omega)
    cases instrs with
    | nil => simp only [lowerSeq]; exact hk f locs stk nv nl
    | cons i rest =>
      have hszRest : sizeOf rest < sizeOf (i :: rest) := by simp +arith
      cases i with
      | unreachable => simp only [lowerSeq]; exact htrap nv nl
      | br depth =>
        simp only [lowerSeq]
        cases labs[depth]? with
        | none => exact htrap nv nl
        | some lbl =>
          dsimp only
          cases popArgsAux lbl.argTys stk with
          | none => exact htrap nv nl
          | some p =>
            rcases p with ⟨ba, _⟩
            dsimp only
            simp only [toTFlat, TFlat.supportsSource, labelSig, List.all_cons, Bool.and_eq_true]
            exact labelSig_supportsTy_pair hv ctx.locTys lbl.argTys
      | br_table targets defTarget =>
        simp only [lowerSeq]
        cases pop32 stk with
        | none => exact htrap nv nl
        | some p =>
          rcases p with ⟨idx32, stk1⟩
          cases labs[defTarget]? with
          | none => exact htrap nv nl
          | some defLbl =>
            dsimp only
            cases popArgsAux defLbl.argTys stk1 with
            | none => exact htrap nv nl
            | some p' =>
              rcases p' with ⟨ba, _⟩
              dsimp only
              exact emitBrTable_ss hv ctx.locTys ctx.retTys labs locs f idx32 defLbl ba
                0 targets nv nl
      | return_ =>
        simp only [lowerSeq]
        cases popArgsAux ctx.retTys stk with
        | none => exact htrap nv nl
        | some p =>
          rcases p with ⟨ra, _⟩
          dsimp only
          simpa [toTFlat, TFlat.supportsSource] using wasmRetSig_supportsTy hv ctx.retTys
      | block bt body =>
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => exact htrap nv nl
        | some ft =>
          dsimp only
          cases popArgsAux ft.params stk with
          | none => exact htrap nv nl
          | some p =>
            rcases p with ⟨ia, sa⟩
            dsimp only
            have hszBody : sizeOf body < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
            have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
            have hsig := labelSig_supportsTy_pair hv ctx.locTys ft.results
            simp only [toTFlat, toTBlocks, TFlat.supportsSource, TBlocks.supportsSource,
              labelSig, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
            refine ⟨⟨hsig, hsig, ?_⟩, ?_⟩
            · exact ih _ hszRest' vc _ _ _ labs rest (Nat.le_refl _) k hk _ _
            · refine ih _ hszBody vc f locs _ _ body (Nat.le_refl _) _
                (fun f' l' s' nv' nl' => ?_) _ _
              cases popArgsAux ft.results s' with
              | none => exact mkTrapExpr_ss hv ctx.retTys 1#32 f' nv' nl'
              | some p' =>
                rcases p' with ⟨ra, _⟩
                dsimp only
                simp only [toTFlat, TFlat.supportsSource, List.all_cons, Bool.and_eq_true]
                exact hsig
      | loop bt body =>
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => exact htrap nv nl
        | some ft =>
          dsimp only
          cases popArgsAux ft.params stk with
          | none => exact htrap nv nl
          | some p =>
            rcases p with ⟨ia, sa⟩
            dsimp only
            have hszBody : sizeOf body < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
            have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
            have hsigR := labelSig_supportsTy_pair hv ctx.locTys ft.results
            have hsigP := labelSig_supportsTy_pair hv ctx.locTys ft.params
            simp only [toTFlat, toTBlocks, TFlat.supportsSource, TBlocks.supportsSource,
              labelSig, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
            refine ⟨⟨hsigR, hsigR, ?_⟩, ?_⟩
            · exact ih _ hszRest' vc _ _ _ labs rest (Nat.le_refl _) k hk _ _
            · refine ⟨⟨hsigP, hsigP, ?_⟩, hsigP⟩
              refine ⟨by simp [LegalTarget.supportsOpCode, h64],
                ⟨h32, h64, list_map_toTy_supportsTy hv ctx.retTys⟩,
                by simp [LegalTarget.supportsOpCode, h64], ?_⟩
              refine ih _ hszBody vc _ _ _ _ body (Nat.le_refl _) _
                (fun f' l' s' nv' nl' => ?_) _ _
              cases popArgsAux ft.results s' with
              | none => exact mkTrapExpr_ss hv ctx.retTys 1#32 f' nv' nl'
              | some p' =>
                rcases p' with ⟨ra, _⟩
                dsimp only
                simp only [toTFlat, TFlat.supportsSource, List.all_cons, Bool.and_eq_true]
                exact hsigR
      | if_ bt thenBody elseBody =>
        simp only [lowerSeq]
        cases bt.resolve ctx.types with
        | none => exact htrap nv nl
        | some ft =>
          dsimp only
          cases pop32 stk with
          | none => exact htrap nv nl
          | some p =>
            rcases p with ⟨cond, stk1⟩
            dsimp only
            cases popArgsAux ft.params stk1 with
            | none => exact htrap nv nl
            | some p' =>
              rcases p' with ⟨ia, sa⟩
              dsimp only
              have hszT : sizeOf thenBody < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
              have hszE : sizeOf elseBody < sz := Nat.lt_of_lt_of_le (by simp +arith) hsz
              have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
              have hsig := labelSig_supportsTy_pair hv ctx.locTys ft.results
              simp only [toTFlat, toTBlocks, TFlat.supportsSource, TBlocks.supportsSource,
                labelSig, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
              refine ⟨⟨hsig, hsig, ?_⟩, by simp [LegalTarget.supportsOpCode, h32], ?_, ?_⟩
              · exact ih _ hszRest' vc _ _ _ labs rest (Nat.le_refl _) k hk _ _
              · refine ih _ hszT vc f locs _ _ thenBody (Nat.le_refl _) _
                  (fun f' l' s' nv' nl' => ?_) _ _
                cases popArgsAux ft.results s' with
                | none => exact mkTrapExpr_ss hv ctx.retTys 1#32 f' nv' nl'
                | some p'' =>
                  rcases p'' with ⟨ra, _⟩
                  dsimp only
                  simp only [toTFlat, TFlat.supportsSource, List.all_cons, Bool.and_eq_true]
                  exact hsig
              · refine ih _ hszE vc f locs _ _ elseBody (Nat.le_refl _) _
                  (fun f' l' s' nv' nl' => ?_) _ _
                cases popArgsAux ft.results s' with
                | none => exact mkTrapExpr_ss hv ctx.retTys 1#32 f' nv' nl'
                | some p'' =>
                  rcases p'' with ⟨ra, _⟩
                  dsimp only
                  simp only [toTFlat, TFlat.supportsSource, List.all_cons, Bool.and_eq_true]
                  exact hsig
      | _ =>
        simp only [lowerSeq]
        have hszRest' : sizeOf rest < sz := Nat.lt_of_lt_of_le hszRest hsz
        exact lowerSimpleInstr_ss hv ctx vc f locs stk labs _ _
          (fun f' l' s' nv' nl' => ih _ hszRest' vc f' l' s' labs rest (Nat.le_refl _)
            k hk nv' nl') nv nl

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
    (fun f' _ s' nv' nl' => ?_) _ _
  cases popArgsAux ft.results s' with
  | none => exact mkTrapExpr_ss hv ft.results 1#32 f' nv' nl'
  | some p =>
    rcases p with ⟨ra, _⟩
    dsimp only
    simpa [toTFlat, TFlat.supportsSource] using hret

/-- Universal supportability: every lowered function in `lowerModule m` satisfies
`fn.body.supportsSource lt` for every valid `LegalTarget` (including both `x64LegalTarget`
and `armLegalTarget`). -/
theorem lowerModule_supportsSource (m : WModule) {lt : LegalTarget} (hv : lt.valid = true) :
    ∀ fn ∈ (lowerModule m).fns, fn.body.supportsSource lt = true := by
  intro fn hmem
  simp only [lowerModule, List.mem_map] at hmem
  rcases hmem with ⟨f, _, rfl⟩
  exact lowerFuncBody_supportsSource m f _ hv

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
    ∀ fn ∈ (lowerModule m).fns, lt.legalSig fn.as = fn.as ∧ lt.legalSig fn.rs = fn.rs := by
  intro fn hmem
  simp only [lowerModule, List.mem_map] at hmem
  rcases hmem with ⟨f, _, rfl⟩
  simp only [lowerFn, wasmAbiResults, wasmRetSig,
    LegalTarget.legalSig, h32, h64, List.cons_append, List.nil_append]
  exact ⟨congrArg (T.i64 :: T.i64 :: ·) (legalSig_map_toTy h32 h64 _),
    congrArg (T.i32 :: T.i64 :: ·) (legalSig_map_toTy h32 h64 _)⟩

end SupportsSourceProofs

end LeanQbe.T.Wasm
