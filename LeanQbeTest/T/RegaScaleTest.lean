module

public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Spill
public meta import Lean
public meta import LeanQbe.T.Target
public meta import LeanQbe.T.Spill

/-!
# Gate `G12c` Kernel `rfl` Scaling Benchmarks (`T7a`)

Measures `Rega.lowerFn` in the Lean kernel (`t_kernel_rfl`) consuming untrusted literal `Hints`
computed externally by `Spill.hints` (spliced as pure literal expressions via `Lean.ToExpr`):
- `sl250`, `sl1000`, `sl2000`: straight-line 250 / 1000 / 2000 `add i64` chains
- `bl50`, `bl250`, `bl250_cross`: 50- and 250-block `.group` benchmarks
- `spill20`: 20 live variables under 4 allocatable GPRs exercising full `Spill` spill/reload traffic
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.RegaScaleTest
open LeanQbe.T

abbrev MockDir := Nat × Nat × Nat × Sym

def mkScaleIsa (nAlloc : Nat) : Isa where
  Reg := Nat
  VReg := Nat
  Cond := Nat
  Directive := MockDir
  gpr := {
    condReads := fun _ => 1#8
    negCond := fun c => if Nat.beq c 0 then 1 else 0
    zeroFlags := [0]
    clearFlags := []
    mov := fun d s => [(1, d, s, "")]
    movi := fun d c => [(2, d, c.toNat, "")]
    setcc := fun d c => [(3, d, c, "")]
    jmp := fun l => [(4, 0, 0, l)]
    jcc := fun c l => [(5, c, 0, l)]
    jnzGpr := fun r l => ([(6, r, 0, l)], 1#8)
    op := fun {sig rs} code pas dsts _ =>
      match sig, rs, code, pas, dsts with
      | _, _, .add (.bits 64), (.gpr a, .gpr b, ()), (.gpr d, ()) =>
        some ([(10, d, a * 32 + b, "")], 1#8)
      | _, _, .add (.bits 64), (.gpr a, .imm c, ()), (.gpr d, ()) =>
        some ([(11, d, a * 32 + c.toNat, "")], 1#8)
      | _, _, _, _, _ => none
    load := fun _ _ _ => none
    store := fun _ _ _ => none
    supportsScalarOp := defaultSupportsScalarOp [8, 16, 32, 64] false false false
  }
  vec := {
    vecScratch := [4], vecAllocatable := [0, 1, 2, 3], vecArgRegs := [0, 1], vecRetRegs := [0]
    isAbiVec := fun _ => false, vecSlotWidth := fun _ => none
    vmov := fun _ _ _ => [], vmovi := fun _ _ _ => none
    vslotSt := fun _ _ _ => [], vslotLd := fun _ _ _ => []
    vop := fun _ _ _ _ => none, vload := fun _ _ _ => none, vstore := fun _ _ _ => none
    supportsVecOp := fun _ _ => false
  }
  frame := {
    label := fun s => (0, 0, 0, s)
    sp := 0
    scratch := [1]
    allocatable := (List.range nAlloc).map (· + 2)
    calleeSaved := [nAlloc + 2, nAlloc + 3]
    raRegs := []
    argRegs := (List.range (min nAlloc 6)).map (· + 2)
    retRegs := [2]
    raBytes := 8
    frameSize := (8 * ·)
    prologue := fun n => ([(20, n, 0, "")], 0#8)
    epilogue := fun n => ([(21, n, 0, "")], 0#8)
    slotSt := fun i s => [(7, i, s, "")]
    slotLd := fun d i => [(8, d, i, "")]
    canonAbi := fun _ _ => ([], 0#8)
    call := fun _ => []
    exitJmp := fun l => [(4, 0, 0, l)]
    ret := [(22, 0, 0, "")]
  }

def scaleIsa : Isa := mkScaleIsa 14
def smallIsa : Isa := mkScaleIsa 4

/-! ## Benchmark Functions (`sl250`, `sl1000`, `sl2000`, `bl50`, `bl250`, `bl250_cross`, `spill20`) -/

def mkSL {V : Ty → Type} {L : List Ty → Type} : Nat → V i64 → V i64 → Expr V L [i64]
  | 0, _, x => .ret (.var x, ())
  | n + 1, a, x => .let_ (op2 (.add i64) (.var x) (.var a)) fun (y, ()) => mkSL n a y

def fn_sl250 : Fn := ⟨"sl250", [i64], [i64], fun _ _ (a, ()) => mkSL 250 a a⟩
def fn_sl1000 : Fn := ⟨"sl1000", [i64], [i64], fun _ _ (a, ()) => mkSL 1000 a a⟩
def fn_sl2000 : Fn := ⟨"sl2000", [i64], [i64], fun _ _ (a, ()) => mkSL 2000 a a⟩

def mkBlocks {V : Ty → Type} {L : List Ty → Type} :
    (k : Nat) → V i64 → Tup L (List.replicate k [i64]) → Blocks V L [i64] (List.replicate k [i64])
  | 0, _, () => .nil
  | _ + 1, a, (l, ls) =>
    .cons (fun (x, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm 1)) fun (y1, ()) =>
      .let_ (op2 (.add i64) (.var y1) (.var a)) fun (y2, ()) =>
      .let_ (op2 (.add i64) (.var y2) (.imm 2)) fun (y3, ()) =>
      .jump l (.var y3, ()))
      (mkBlocks _ a ls)

def fn_bl50 : Fn := ⟨"bl50", [i64], [i64], fun _ _ (a, ()) =>
  .group (sig := List.replicate 50 [i64]) (fun Js => mkBlocks 50 a Js) (fun Js => .jump Js.1 (.var a, ()))⟩

def fn_bl250 : Fn := ⟨"bl250", [i64], [i64], fun _ _ (a, ()) =>
  .group (sig := List.replicate 250 [i64]) (fun Js => mkBlocks 250 a Js) (fun Js => .jump Js.1 (.var a, ()))⟩

def mkBlocksCross {V : Ty → Type} {L : List Ty → Type} (l0 : L [i64]) (a : V i64) :
    (k : Nat) → Tup L (List.replicate k [i64]) → Blocks V L [i64] (List.replicate k [i64])
  | 0, () => .nil
  | 1, (_, ()) =>
    .cons (fun (x, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm 1)) fun (y1, ()) =>
      .let_ (op2 (.add i64) (.var y1) (.var a)) fun (y2, ()) =>
      .let_ (op2 (.add i64) (.var y2) (.imm 2)) fun (y3, ()) =>
      .jump l0 (.var y3, ()))
      .nil
  | k + 2, (_, ls) =>
    .cons (fun (x, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm 1)) fun (y1, ()) =>
      .let_ (op2 (.add i64) (.var y1) (.var a)) fun (y2, ()) =>
      .let_ (op2 (.add i64) (.var y2) (.imm 2)) fun (y3, ()) =>
      .jump ls.1 (.var y3, ()))
      (mkBlocksCross l0 a (k + 1) ls)

def fn_bl250_cross : Fn := ⟨"bl250_cross", [i64], [i64], fun _ _ (a, ()) =>
  .group (sig := List.replicate 250 [i64]) (fun Js => mkBlocksCross Js.1 a 250 Js) (fun Js => .jump Js.1 (.var a, ()))⟩

def mkSpillSum {V : Ty → Type} {L : List Ty → Type} : List (V i64) → V i64 → Expr V L [i64]
  | [], acc => .ret (.var acc, ())
  | x :: xs, acc =>
    .let_ (op2 (.add i64) (.var acc) (.var x)) fun (y1, ()) =>
    .let_ (op2 (.add i64) (.var y1) (.var x)) fun (y2, ()) => mkSpillSum xs y2

def mkSpill {V : Ty → Type} {L : List Ty → Type} : Nat → V i64 → List (V i64) → Expr V L [i64]
  | 0, a, xs => mkSpillSum xs a
  | n + 1, a, xs =>
    .let_ (op2 (.add i64) (.var a) (.imm (BitVec.ofNat 64 (n + 1)))) fun (y, ()) =>
    mkSpill n a (y :: xs)

def fn_spill20 : Fn := ⟨"spill20", [i64], [i64], fun _ _ (a, ()) => mkSpill 20 a []⟩

/-! ## External Untrusted Hint & Code Splicing (`ToExpr`, Zero Kernel Oracle Execution) -/

meta section
open Lean Elab Command Term Meta

elab "splice_lower " hName:ident cName:ident isaId:ident fnId:ident : command => do
  let hDeclNm := (← getCurrNamespace) ++ hName.getId
  let cDeclNm := (← getCurrNamespace) ++ cName.getId
  let (hExpr, cExpr) ← liftTermElabM do
    let hTerm ← elabTerm (← `(Spill.hints $isaId $fnId)) none
    let hTy := mkApp3 (mkConst ``Hints) (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat)
    let hVal ← unsafe evalExpr (Hints Nat Nat Nat) hTy hTerm
    let hLit := toExpr hVal
    let dirTy := toTypeExpr (Nat × Nat × Nat × String)
    let resTy := mkApp2 (mkConst ``Except [0, 0]) (mkConst ``String) (mkApp (mkConst ``List [0]) dirTy)
    let isaE ← elabTerm isaId none
    let fnE ← elabTerm fnId none
    let extE ← elabTerm (← `(({} : Rega.Ext))) none
    let lowerTerm := mkApp4 (mkConst ``Rega.lowerFn) isaE hLit extE fnE
    let resVal ← unsafe evalExpr (Except String (List (Nat × Nat × Nat × String))) resTy lowerTerm
    match resVal with
    | .error err => throwError "splice_lower: Rega.lowerFn failed: {err}"
    | .ok code => return (hLit, toExpr code)
  let hTy := mkApp3 (mkConst ``Hints) (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat)
  let cTy := mkApp (mkConst ``List [0]) (toTypeExpr (Nat × Nat × Nat × String))
  liftCoreM do
    addDecl <| .defnDecl {
      name := hDeclNm, levelParams := [], type := hTy, value := hExpr,
      hints := .abbrev, safety := .safe }
    addDecl <| .defnDecl {
      name := cDeclNm, levelParams := [], type := cTy, value := cExpr,
      hints := .abbrev, safety := .safe }

end

splice_lower hints_sl250 code_sl250 scaleIsa fn_sl250
splice_lower hints_sl1000 code_sl1000 scaleIsa fn_sl1000
splice_lower hints_sl2000 code_sl2000 scaleIsa fn_sl2000
splice_lower hints_bl50 code_bl50 scaleIsa fn_bl50
splice_lower hints_bl250 code_bl250 scaleIsa fn_bl250
splice_lower hints_bl250_cross code_bl250_cross scaleIsa fn_bl250_cross
splice_lower hints_spill20 code_spill20 smallIsa fn_spill20

theorem sl250_lower : Rega.lowerFn scaleIsa hints_sl250 {} fn_sl250 = .ok code_sl250 := by t_kernel_rfl
theorem sl1000_lower : Rega.lowerFn scaleIsa hints_sl1000 {} fn_sl1000 = .ok code_sl1000 := by t_kernel_rfl
theorem sl2000_lower : Rega.lowerFn scaleIsa hints_sl2000 {} fn_sl2000 = .ok code_sl2000 := by t_kernel_rfl
theorem bl50_lower : Rega.lowerFn scaleIsa hints_bl50 {} fn_bl50 = .ok code_bl50 := by t_kernel_rfl
theorem bl250_lower : Rega.lowerFn scaleIsa hints_bl250 {} fn_bl250 = .ok code_bl250 := by t_kernel_rfl
theorem bl250_cross_lower : Rega.lowerFn scaleIsa hints_bl250_cross {} fn_bl250_cross = .ok code_bl250_cross := by t_kernel_rfl
theorem spill20_lower : Rega.lowerFn smallIsa hints_spill20 {} fn_spill20 = .ok code_spill20 := by t_kernel_rfl
theorem spill20_spills : hints_spill20.nslots > 0 := by decide

#print axioms sl1000_lower
#print axioms sl2000_lower
#print axioms bl250_lower
#print axioms spill20_lower

end LeanQbe.T.RegaScaleTest
