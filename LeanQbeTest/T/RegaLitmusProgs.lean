module

public import LeanQbeTest.T.RegaLitmusTarget
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Spill
public meta import Lean
public meta import LeanQbe.T.Spill
public meta import LeanQbeTest.T.RegaLitmusTarget

/-!
# `G12a`/`G12d` Litmus Programs, Untrusted `Spill` Hints, and Kernel-Checked Lowering

Programs over the typed PHOAS IL lowered by `Rega.lowerFn RegaLitmus.isa` with untrusted hints
computed directly by `Spill.hints`, spliced as literals, and checked by a single kernel `rfl` per
program (`t_kernel_rfl`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.RegaLitmus
open LeanQbe.T

abbrev v2i32 : Ty := Ty.vec 1 i32

/-! ## 1. `G12a` Programs -/

/-- `|a - b| + 1` through a diamond joining at a block with a parameter. -/
def fnBranches : Fn := ⟨"branches", [i64, i64], [i64], fun _ _ (a, b, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (fun (r, ()) =>
      .let_ (op2 (.add i64) (.var r) (.imm 1)) fun (r1, ()) => .ret (.var r1, ())) .nil)
    (fun (join, ()) =>
      .let_ (op2 (.ult i64) (.var a) (.var b)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.sub i64) (.var b) (.var a)) fun (d, ()) => .jump join (.var d, ()))
        (.let_ (op2 (.sub i64) (.var a) (.var b)) fun (d, ()) => .jump join (.var d, ())))⟩

/-- `n + (n - 1) + … + 1` (`n ≥ 1`). -/
def fnLoop : Fn := ⟨"loop", [i64], [i64], fun _ _ (n, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
      .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
      .let_ (op2 (.ne i64) (.var i') (.imm 0)) fun (c, ()) =>
      .jnz (.var c) (.jump loop (.var i', .var acc', ())) (.ret (.var acc', ())))
    (fun loop => .jump loop (.var n, .imm 0, ()))⟩

/-- Irreducible parity: the entry jumps into either block of the `even`/`odd` cycle. -/
def fnEvenOdd : Fn := ⟨"evenOdd", [i64, i64], [i64], fun _ _ (n, st, ()) =>
  .group (sig := [[i64], [i64]])
    (fun (ev, od, ()) =>
      .cons (fun (k, ()) =>
        .let_ (op2 (.eq i64) (.var k) (.imm 0)) fun (z, ()) =>
        .jnz (.var z) (.ret (.imm 1, ()))
          (.let_ (op2 (.sub i64) (.var k) (.imm 1)) fun (k', ()) => .jump od (.var k', ())))
      (.cons (fun (k, ()) =>
        .let_ (op2 (.eq i64) (.var k) (.imm 0)) fun (z, ()) =>
        .jnz (.var z) (.ret (.imm 0, ()))
          (.let_ (op2 (.sub i64) (.var k) (.imm 1)) fun (k', ()) => .jump ev (.var k', ()))) .nil))
    (fun (ev, od, ()) =>
      .let_ (op2 (.eq i64) (.var st) (.imm 0)) fun (s, ()) =>
      .jnz (.var s) (.jump ev (.var n, ())) (.jump od (.var n, ())))⟩

/-- `n * m` by nested counting loops (`n, m ≥ 1`). -/
def fnNested : Fn := ⟨"nested", [i64, i64], [i64], fun _ _ (n, m, ()) =>
  loop1 (ts := [i64, i64])
    (fun outer (i, acc, ()) =>
      loop1 (ts := [i64, i64])
        (fun inner (j, acc2, ()) =>
          .let_ (op2 (.add i64) (.var acc2) (.imm 1)) fun (acc3, ()) =>
          .let_ (op2 (.sub i64) (.var j) (.imm 1)) fun (j', ()) =>
          .let_ (op2 (.ne i64) (.var j') (.imm 0)) fun (cj, ()) =>
          .jnz (.var cj) (.jump inner (.var j', .var acc3, ()))
            (.let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
             .let_ (op2 (.ne i64) (.var i') (.imm 0)) fun (ci, ()) =>
             .jnz (.var ci) (.jump outer (.var i', .var acc3, ())) (.ret (.var acc3, ()))))
        (fun inner => .jump inner (.var m, .var acc, ())))
    (fun outer => .jump outer (.var n, .imm 0, ()))⟩

/-- A loop carrying an `(i64, bool)` state: sum and parity of the trip count. -/
def fnPairLoop : Fn := ⟨"pairLoop", [i64], [i64, .bool], fun _ _ (n, ()) =>
  loop1 (ts := [i64, i64, .bool])
    (fun loop (i, acc, b, ()) =>
      .let_ (op2 (.add i64) (.var acc) (.var i)) fun (acc', ()) =>
      .let_ (op2 (.xor .bool) (.var b) (.imm true)) fun (b', ()) =>
      .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
      .let_ (op2 (.ne i64) (.var i') (.imm 0)) fun (c, ()) =>
      .jnz (.var c) (.jump loop (.var i', .var acc', .var b', ())) (.ret (.var acc', .var b', ())))
    (fun loop => .jump loop (.var n, .imm 0, .imm false, ()))⟩

/-- A `vec 2 i32` loop: the vector state is initialised by `vmovi` and doubled each trip. -/
def fnVecLoop : Fn := ⟨"vecLoop", [i64], [v2i32], fun _ _ (n, ()) =>
  loop1 (ts := [i64, v2i32])
    (fun loop (i, acc, ()) =>
      .let_ (op2 (.add v2i32) (.var acc) (.var acc)) fun (acc', ()) =>
      .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
      .let_ (op2 (.ne i64) (.var i') (.imm 0)) fun (c, ()) =>
      .jnz (.var c) (.jump loop (.var i', .var acc', ())) (.ret (.var acc', ())))
    (fun loop => .jump loop (.var n, .imm ((1#32, 2#32) : Val v2i32), ()))⟩

/-- Callee for `fnCarryCall`. -/
def fnInc : Fn := ⟨"inc", [i64], [i64], fun _ _ (y, ()) =>
  .let_ (op2 (.add i64) (.var y) (.imm 1)) fun (r, ()) => .ret (.var r, ())⟩

/-- A carry produced before a `call` and consumed after it (flags die at the call). -/
def fnCarryCall : Fn := ⟨"carryCall", [i64, i64, i64], [i64, .bool], fun _ _ (a, b, x, ()) =>
  .let_ (op3 (.addc 64) (.var a) (.var b) (.imm false)) fun (s0, c0, ()) =>
  .call "inc" (as := [i64]) (bs := [i64]) (.var s0, ()) fun (r, ()) =>
  .let_ (op3 (.addc 64) (.var r) (.var x) (.var c0)) fun (s1, c1, ()) =>
  .ret (.var s1, .var c1, ())⟩

/-- `lshr` and `cmp ult` at `bits 8`, through an `i8` load and store. -/
def fnBits8 : Fn := ⟨"bits8", [i64, i8], [i8], fun _ _ (p, b, ()) =>
  .load i8 (.var p) fun a =>
  .let_ (op2 (.lshr i8) (.var a) (.imm 1)) fun (x, ()) =>
  .store (.var x) (.var p) (
  .let_ (op2 (.ult i8) (.var x) (.var b)) fun (c, ()) =>
  .jnz (.var c) (.ret (.var x, ())) (.ret (.var b, ())))⟩

/-! ## 2. `G12d` Programs -/

/-- `cmp → jcc`: unsigned minimum through a branch on `CF`. -/
def fnCmpJcc : Fn := ⟨"cmpJcc", [i64, i64], [i64], fun _ _ (a, b, ()) =>
  .let_ (op2 (.ult i64) (.var a) (.var b)) fun (c, ()) =>
  .jnz (.var c) (.ret (.var a, ())) (.ret (.var b, ()))⟩

/-- An `adc` chain: `(a1:a0) + (b1:b0)`, returning the high limb and the carry-out limb. -/
def fnAdcChain : Fn := ⟨"adcChain", [i64, i64, i64, i64], [i64, i64], fun _ _ (a0, a1, b0, b1, ()) =>
  .let_ (op3 (.addc 64) (.var a0) (.var b0) (.imm false)) fun (_s0, c0, ()) =>
  .let_ (op3 (.addc 64) (.var a1) (.var b1) (.var c0)) fun (s1, c1, ()) =>
  .let_ (op3 (.addc 64) (.imm 0) (.imm 0) (.var c1)) fun (s2, _c2, ()) =>
  .ret (.var s1, .var s2, ())⟩

/-- Two interleaved carry chains: `(a1:a0) + b` on `CF` (`adcx`), `(c1:c0) + d` on `OF` (`adox`). -/
def fnAdcxAdox : Fn := ⟨"adcxAdox", [i64, i64, i64, i64, i64, i64], [i64, i64],
  fun _ _ (a0, a1, b, c0, c1, d, ()) =>
  .let_ (op3 (.addc 64) (.var a0) (.var b) (.imm false)) fun (_x0, cx, ()) =>
  .let_ (op3 (.addc 64) (.var c0) (.var d) (.imm false)) fun (_y0, oy, ()) =>
  .let_ (op3 (.addc 64) (.var a1) (.imm 0) (.var cx)) fun (x1, _cx', ()) =>
  .let_ (op3 (.addc 64) (.var c1) (.imm 0) (.var oy)) fun (y1, _oy', ()) =>
  .ret (.var x1, .var y1, ())⟩

/-- Loop-carried `CF`: `acc += y` with carry each trip, `y += 8` by `lea`, counter by `dec`. -/
def fnCfLoop : Fn := ⟨"cfLoop", [i64, i64], [i64, .bool], fun _ _ (n, x, ()) =>
  loop1 (ts := [i64, i64, i64, .bool])
    (fun loop (i, acc, y, cf, ()) =>
      .let_ (op3 (.addc 64) (.var acc) (.var y) (.var cf)) fun (acc', cf', ()) =>
      .let_ (op2 (.add i64) (.var y) (.imm 8)) fun (y', ()) =>
      .let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) =>
      .let_ (op2 (.ne i64) (.var i') (.imm 0)) fun (c, ()) =>
      .jnz (.var c) (.jump loop (.var i', .var acc', .var y', .var cf', ()))
        (.ret (.var acc', .var cf', ())))
    (fun loop => .jump loop (.var n, .imm 0, .var x, .imm false, ()))⟩


def extCarryCall : Rega.Ext := { callees := [("inc", [i64], [i64])] }

/-! ## 4. External Untrusted Hint & Code Splicing (`ToExpr`, zero kernel oracle execution) -/

meta section
open Lean Elab Command Term Meta

/-- `splice_lower h c (hintsTerm) (extTerm) fn` evaluates `hintsTerm` (e.g. `Spill.hints isa fn`)
and `Rega.lowerFn isa hints ext fn` in the interpreter and adds the results as literal
definitions `h` and `c`. -/
elab "splice_lower " hName:ident cName:ident "(" hT:term ")" "(" eT:term ")" fnId:ident : command => do
  let hDeclNm := (← getCurrNamespace) ++ hName.getId
  let cDeclNm := (← getCurrNamespace) ++ cName.getId
  let hTy := mkApp3 (mkConst ``Hints) (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Cond)
  let cTy := mkApp (mkConst ``List [0]) (mkConst ``Instr)
  let (hExpr, cExpr) ← liftTermElabM do
    let hTerm ← elabTerm hT (some hTy)
    let hVal ← unsafe evalExpr (Hints Nat Nat Cond) hTy hTerm
    let hLit := toExpr hVal
    let resTy := mkApp2 (mkConst ``Except [0, 0]) (mkConst ``String) cTy
    let isaE ← elabTerm (← `(isa)) none
    let fnE ← elabTerm fnId none
    let extE ← elabTerm eT (some (mkConst ``Rega.Ext))
    let lowerTerm := mkApp4 (mkConst ``Rega.lowerFn) isaE hLit extE fnE
    let resVal ← unsafe evalExpr (Except String (List Instr)) resTy lowerTerm
    match resVal with
    | .error err => throwError "splice_lower: Rega.lowerFn failed: {err}"
    | .ok code => return (hLit, toExpr code)
  liftCoreM do
    let hDecl := Declaration.defnDecl {
      name := hDeclNm, levelParams := [], type := hTy, value := hExpr,
      hints := .abbrev, safety := .safe }
    let cDecl := Declaration.defnDecl {
      name := cDeclNm, levelParams := [], type := cTy, value := cExpr,
      hints := .abbrev, safety := .safe }
    -- exported with their bodies (kernel-unfoldable from importing modules) and compiled
    addDecl hDecl (forceExpose := true)
    addDecl cDecl (forceExpose := true)
    compileDecl hDecl
    compileDecl cDecl

end

splice_lower hintsBranches codeBranches (Spill.hints isa fnBranches) ({}) fnBranches
splice_lower hintsLoop codeLoop (Spill.hints isa fnLoop) ({}) fnLoop
splice_lower hintsEvenOdd codeEvenOdd (Spill.hints isa fnEvenOdd) ({}) fnEvenOdd
splice_lower hintsNested codeNested (Spill.hints isa fnNested) ({}) fnNested
splice_lower hintsPairLoop codePairLoop (Spill.hints isa fnPairLoop) ({}) fnPairLoop
splice_lower hintsVecLoop codeVecLoop (Spill.hints isa fnVecLoop) ({}) fnVecLoop
splice_lower hintsInc codeInc (Spill.hints isa fnInc) ({}) fnInc
splice_lower hintsCarryCall codeCarryCall (Spill.hints isa fnCarryCall) (extCarryCall) fnCarryCall
splice_lower hintsBits8 codeBits8 (Spill.hints isa fnBits8) ({}) fnBits8
splice_lower hintsCmpJcc codeCmpJcc (Spill.hints isa fnCmpJcc) ({}) fnCmpJcc
splice_lower hintsAdcChain codeAdcChain (Spill.hints isa fnAdcChain) ({}) fnAdcChain
splice_lower hintsAdcxAdox codeAdcxAdox (Spill.hints isa fnAdcxAdox) ({}) fnAdcxAdox
splice_lower hintsCfLoop codeCfLoop (Spill.hints isa fnCfLoop) ({}) fnCfLoop

/-! ## 5. Well-Formedness and Kernel-Checked Lowering -/

theorem branches_wf : fnBranches.Wf := by unfold Fn.Wf; t_wf_reify
theorem loop_wf : fnLoop.Wf := by unfold Fn.Wf; t_wf_reify
theorem evenOdd_wf : fnEvenOdd.Wf := by unfold Fn.Wf; t_wf_reify
theorem nested_wf : fnNested.Wf := by unfold Fn.Wf; t_wf_reify
theorem pairLoop_wf : fnPairLoop.Wf := by unfold Fn.Wf; t_wf_reify
theorem vecLoop_wf : fnVecLoop.Wf := by unfold Fn.Wf; t_wf_reify
theorem inc_wf : fnInc.Wf := by unfold Fn.Wf; t_wf_reify
theorem carryCall_wf : fnCarryCall.Wf := by unfold Fn.Wf; t_wf_reify
theorem bits8_wf : fnBits8.Wf := by unfold Fn.Wf; t_wf_reify
theorem cmpJcc_wf : fnCmpJcc.Wf := by unfold Fn.Wf; t_wf_reify
theorem adcChain_wf : fnAdcChain.Wf := by unfold Fn.Wf; t_wf_reify
theorem adcxAdox_wf : fnAdcxAdox.Wf := by unfold Fn.Wf; t_wf_reify
theorem cfLoop_wf : fnCfLoop.Wf := by unfold Fn.Wf; t_wf_reify

theorem branches_lower : Rega.lowerFn isa hintsBranches {} fnBranches = .ok codeBranches := by
  t_kernel_rfl
theorem loop_lower : Rega.lowerFn isa hintsLoop {} fnLoop = .ok codeLoop := by t_kernel_rfl
theorem evenOdd_lower : Rega.lowerFn isa hintsEvenOdd {} fnEvenOdd = .ok codeEvenOdd := by
  t_kernel_rfl
theorem nested_lower : Rega.lowerFn isa hintsNested {} fnNested = .ok codeNested := by t_kernel_rfl
theorem pairLoop_lower : Rega.lowerFn isa hintsPairLoop {} fnPairLoop = .ok codePairLoop := by
  t_kernel_rfl
theorem vecLoop_lower : Rega.lowerFn isa hintsVecLoop {} fnVecLoop = .ok codeVecLoop := by
  t_kernel_rfl
theorem inc_lower : Rega.lowerFn isa hintsInc {} fnInc = .ok codeInc := by t_kernel_rfl
theorem carryCall_lower :
    Rega.lowerFn isa hintsCarryCall extCarryCall fnCarryCall = .ok codeCarryCall := by t_kernel_rfl
theorem bits8_lower : Rega.lowerFn isa hintsBits8 {} fnBits8 = .ok codeBits8 := by t_kernel_rfl
theorem cmpJcc_lower : Rega.lowerFn isa hintsCmpJcc {} fnCmpJcc = .ok codeCmpJcc := by t_kernel_rfl
theorem adcChain_lower : Rega.lowerFn isa hintsAdcChain {} fnAdcChain = .ok codeAdcChain := by
  t_kernel_rfl
theorem adcxAdox_lower : Rega.lowerFn isa hintsAdcxAdox {} fnAdcxAdox = .ok codeAdcxAdox := by
  t_kernel_rfl
theorem cfLoop_lower : Rega.lowerFn isa hintsCfLoop {} fnCfLoop = .ok codeCfLoop := by t_kernel_rfl

/-! ## 6. Emitted-Code Highlights (the flag paths are really taken) -/

/-- Instructions that may change `CF` (per `execI`). -/
def Instr.writesCF : Instr → Bool
  | .xorz _ | .test8 _ | .bin .. | .cmp .. | .adc .. | .adcx .. | .bt0 _ => true
  | _ => false

/-- Instructions that move a flag into a GPR or a GPR into a flag. -/
def Instr.flagMove : Instr → Bool
  | .setcc .. | .bt0 _ => true
  | _ => false

/-- `cmp → jcc`: the comparison result never leaves `CF` (no `setcc`). -/
theorem cmpJcc_code : codeCmpJcc =
    [.label "cmpJcc", .spAdd 0#64, .mov 0 7, .cmp 64 (.reg 0) (.reg 6), .jcc .cf "cmpJcc.L0",
     .mov 0 6, .spAdd 0#64, .ret, .label "cmpJcc.L0", .spAdd 0#64, .ret] := by t_kernel_rfl

/-- `adc` chain: one `xor` clears `CF`, then three `adc`s ripple the carry through `CF`; the dead
final carry stays in `CF` (zero `setcc`). -/
theorem adcChain_code : codeAdcChain =
    [.label "adcChain", .spAdd 0#64, .mov 0 6, .xorz 11, .adc 64 7 (.reg 7) (.reg 2),
     .adc 64 0 (.reg 0) (.reg 1), .adc 64 2 (.imm 0#64) (.imm 0#64), .spAdd 0#64,
     .ret] := by t_kernel_rfl

/-- Interleaved `adcx`/`adox`: the `CF` chain survives the `adox`es and the `OF` chain survives the
`adcx`es; no flag ever moves through a GPR. -/
theorem adcxAdox_code : codeAdcxAdox =
    [.label "adcxAdox", .spAdd 0#64, .mov 0 6, .xorz 11, .adcx 64 7 (.reg 7) (.reg 2),
     .adox 64 1 (.reg 1) (.reg 9), .adcx 64 0 (.reg 0) (.imm 0#64), .adox 64 2 (.reg 8) (.imm 0#64),
     .spAdd 0#64, .ret] := by t_kernel_rfl

/-- Loop-carried `CF`: `adc` produces it, `lea`/`dec`/`tstz`/`jcc`/`mov`/`jmp` preserve it around
the back-edge into the next `adc`; it is materialised (`setc`) only on exit. -/
theorem cfLoop_code : codeCfLoop =
    [.label "cfLoop", .spAdd 0#64, .mov 0 6, .mov 2 7, .xorz 11, .movi 1 0#64,
     .label "cfLoop.L0", .adc 64 1 (.reg 1) (.reg 0), .lea 6 0 8#64, .dec 64 0 (.reg 2),
     .tstz 64 (.reg 0), .jcc .nzf "cfLoop.L1", .mov 0 1, .setcc 2 .cf, .zext 8 2, .spAdd 0#64, .ret,
     .label "cfLoop.L1", .mov 2 0, .mov 0 6, .jmp "cfLoop.L0"] := by t_kernel_rfl

theorem cfLoop_cf_writers :
    codeCfLoop.filter Instr.writesCF = [.xorz 11, .adc 64 1 (.reg 1) (.reg 0)] ∧
    codeCfLoop.filter Instr.flagMove = [.setcc 2 .cf] := ⟨by t_kernel_rfl, by t_kernel_rfl⟩

/-- `G12a` highlights: `jcc` on flags for every branch, `vmovi` + 2×i32 `vbin`, a carry spilled
across `call` via `setc`/slot/`bt`, and 8-bit `lshr`/`cmp`/`jcc`. -/
theorem g12a_code_highlights :
    codeBranches.contains (.jcc .cf "branches.L1") = true ∧
    codeLoop.contains (.jcc .nzf "loop.L0") = true ∧
    codeEvenOdd.contains (.jcc .nzf "evenOdd.L1") = true ∧
    codeNested.contains (.jcc .nzf "nested.L1") = true ∧
    codePairLoop.contains (.bin .xor 8 2 (.reg 2) (.imm 1#64)) = true ∧
    codeVecLoop.contains (.vmovi 0 0x200000001#512) = true ∧
    codeVecLoop.contains (.vbin .add v2i32 0 0 0) = true ∧
    codeCarryCall.filter Instr.flagMove = [.setcc 0 .cf, .bt0 2, .setcc 2 .cf] ∧
    codeCarryCall.contains (.call "inc") = true ∧
    codeBits8.contains (.bin .lshr 8 0 (.reg 0) (.imm 1#64)) = true ∧
    codeBits8.contains (.cmp 8 (.reg 0) (.reg 6)) = true ∧
    codeBits8.contains (.jcc .cf "bits8.L0") = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> t_kernel_rfl

#print axioms branches_lower
#print axioms loop_lower
#print axioms evenOdd_lower
#print axioms nested_lower
#print axioms pairLoop_lower
#print axioms vecLoop_lower
#print axioms inc_lower
#print axioms carryCall_lower
#print axioms bits8_lower
#print axioms cmpJcc_lower
#print axioms adcChain_lower
#print axioms adcxAdox_lower
#print axioms cfLoop_lower
#print axioms cfLoop_wf
#print axioms cfLoop_code
#print axioms g12a_code_highlights

end LeanQbe.T.RegaLitmus
