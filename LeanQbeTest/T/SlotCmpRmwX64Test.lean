module

import LeanQbe.T.Amd64.TargLemmas
import LeanQbe.T.Amd64.IselLemmas5
import LeanQbe.T.Main
meta import LeanQbe.T.Amd64.TargLemmas
meta import LeanQbe.T.Amd64.Isel
meta import LeanQbe.T.Main

/-!
# Stack-Slot `cmp`/`test`/`alu`/`jnz` & `[mem]` RMW Codegen Tests (SysV x64)

Self-contained x86-64 test module (`Kraken.X64` only, never Arm64):
1. `x64Gpr.aluMem`, `x64Gpr.jnzMem`, and `x64Gpr.rmwMem` instruction selection (`inc`/`dec`/ALU,
   width 8/16/32/64, >32-bit imm64 fallback via `.r11`, `mul` at 8-bit excluded, zero32 flag).
2. Closed Kraken machine specs `x64Gpr_aluMem_spec`, `x64Gpr_aluMem_zero32`,
   `x64Gpr_jnzMem_spec`, and `x64Gpr_rmwMem_spec` on concrete x64 instruction sequences.
3. End-to-end `Spill.hints` + verified `Rega.lowerFn` (`checkCompile`) positive and negative checks:
   - `[%rsp+off]` stack-slot `cmp`, `test`, `sext`/`zext` `cmp`, `alu` (`add`/`sub`/`and`/`or`/
     `xor`), and `jnzMem` on spilled values under high register pressure;
   - `[mem]` RMW folding (`incq`/`decq`/`addq`/`subq`/`andl`/`orl`/`xorq` imm & reg, shared and
     CSE-duplicate `[base+disp]` pointers, negative different-addr, negative `z - x` non-comm `sub`,
     negative intervening store).
4. `#print axioms` audit (`[propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.SlotCmpRmwX64Test

open LeanQbe.T LeanQbe.T.Amd64 Kraken

/-! ## 1. Direct x64 Instruction Selection & Negative Encodings -/

theorem rmw_encodings_rfl :
    x64Gpr.zeroUpper32AluMem = true ∧
    x64Gpr.aluMem 32 (.add i32) true (.baseDisp .rsp 8) (.gpr .rax) .rax =
      some ([ins32 (.add (.reg (d .rax)) (.regOrMem (.mem (atDisp .rsp 8))))], maskAll) ∧
    x64Gpr.aluMem 64 (.sub i64) true (.baseDisp .rsp 16) (.gpr .rax) .rax =
      some ([ins (.sub (.reg (q .rax)) (.regOrMem (.mem (atDisp .rsp 16))))], maskAll) ∧
    x64Gpr.aluMem 8 (.mul i8) true (.baseDisp .rsp 8) (.gpr .rax) .rax = none ∧
    x64Gpr.aluMem 64 (.sub i64) false (.baseDisp .rsp 8) (.gpr .rax) .rax = none ∧
    x64Gpr.jnzMem (.baseDisp .rsp 24) false "L1" =
      some ([ins8 (.cmp (.mem (atDisp .rsp 24)) (immBitsOp .W8 0#8)),
             ins (.jcc .nz "L1")], maskAll) ∧
    x64Gpr.rmwMem 64 (.add i64) (.baseDisp .rdi 0) (.imm 1#64) =
      some ([ins (.inc (.mem (atReg .rdi)))], maskDecInc) ∧
    x64Gpr.rmwMem 64 (.sub i64) (.baseDisp .rdi 0) (.imm 1#64) =
      some ([ins (.dec (.mem (atReg .rdi)))], maskDecInc) ∧
    x64Gpr.rmwMem 32 (.xor i32) (.baseDisp .rdi 4) (.gpr .rcx) =
      some ([ins32 (.xor (.mem (atDisp .rdi 4)) (.reg (d .rcx)))], maskAll) ∧
    x64Gpr.rmwMem 64 (.add i64) (.baseDisp .rdi 0) (.imm (BitVec.ofNat 64 (2 ^ 33))) =
      some ([moviD .r11 (BitVec.ofNat 64 (2 ^ 33)),
             ins (.add (.mem (atReg .rdi)) (.reg (q .r11)))], maskAll) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. Closed Concrete Semantics Theorems (`aluMem` & `rmwMem`) -/

theorem slot_sub64_spec {h : x64Mach.Host} {k : Nat} {s : MachineData}
    {va vb : BitVec 64} {post : MachineState → Prop}
    (hlv : loadVal s.dmem i64 (s.regs.get64 .rsp + 16#64) = some va)
    (hr : s.regs.get64 .rax = vb)
    {c : List Directive} {clob : FlagMask}
    (hc : x64Gpr.aluMem 64 (.sub i64) true (.baseDisp .rsp 16) (.gpr .rax) .rax =
      some (c, clob)) :
    x64Mach.FallsTo x64Gpr.condReads h k c (.rax :: x64Scratch) [] clob s
      (fun s' => s'.regs.get64 .rax = vb - va ∧ s'.dmem = s.dmem) post := by
  have hpb : x64Mach.PArgHolds s i64 (.gpr .rax) vb := by
    dsimp [Machine.PArgHolds, x64Mach, Machine.getGpr, GprHolds]
    exact ⟨Nat.le_refl _, by rw [hr, BitVec.setWidth_eq]⟩
  have hwp : (OpCode.sub i64).wp (vb, va, ()) (fun r => r = (vb - va, ())) := by
    simp [OpCode.wp, lift2, Ty.hasFloat]
  refine fun hinf kont =>
    x64Gpr_aluMem_spec hc (by simp [AddrArg.regs, PArg.gprs, x64Scratch])
      (by simp [x64Scratch]) hlv hpb hwp hinf fun s' ⟨⟨rv, hrv, hg⟩, hm⟩ hfr => ?_
  cases hrv
  exact kont s' ⟨by simpa [GprHolds, BitVec.setWidth_eq] using hg.2, hm⟩ hfr

theorem slot_add32_zero32 {h : x64Mach.Host} {k : Nat} {s : MachineData}
    {va vb : BitVec 32} {post : MachineState → Prop}
    (hlv : loadVal s.dmem i32 (s.regs.get64 .rsp + 8#64) = some va)
    (hr : (s.regs.get64 .rcx).setWidth 32 = vb)
    {c : List Directive} {clob : FlagMask}
    (hc : x64Gpr.aluMem 32 (.add i32) true (.baseDisp .rsp 8) (.gpr .rcx) .rcx =
      some (c, clob)) :
    x64Mach.FallsTo x64Gpr.condReads h k c (.rcx :: x64Scratch) [] clob s
      (fun s' => s'.regs.get64 .rcx = (vb + va).setWidth 64 ∧ s'.dmem = s.dmem) post := by
  have hpb : x64Mach.PArgHolds s i32 (.gpr .rcx) vb :=
    ⟨by decide, hr⟩
  have hwp : (OpCode.add i32).wp (vb, va, ()) (fun r => r = (vb + va, ())) := by
    simp [OpCode.wp, lift2, Ty.hasFloat]
  refine fun hinf kont =>
    x64Gpr_aluMem_zero32 rfl hc (by simp [AddrArg.regs, PArg.gprs, x64Scratch])
      (by simp [x64Scratch]) hlv hpb hwp hinf fun s' ⟨⟨rv, hrv, hz⟩, hm⟩ hfr => ?_
  cases hrv
  exact kont s' ⟨hz, hm⟩ hfr

theorem heap_inc64_spec {h : x64Mach.Host} {k : Nat} {s : MachineData}
    {va : BitVec 64} {post : MachineState → Prop}
    (hlv : loadVal s.dmem i64 (s.regs.get64 .rdi) = some va)
    (hsok : storeOk s.dmem i64 (s.regs.get64 .rdi))
    {c : List Directive} {clob : FlagMask}
    (hc : x64Gpr.rmwMem 64 (.add i64) (.baseDisp .rdi 0) (.imm 1#64) = some (c, clob)) :
    x64Mach.FallsTo x64Gpr.condReads h k c x64Scratch [] clob s
      (fun s' => s'.dmem = storeMem s.dmem i64 (s.regs.get64 .rdi) (va + 1#64)) post := by
  have hwp : (OpCode.add i64).wp (va, 1#64, ()) (fun r => r = (va + 1#64, ())) := by
    simp [OpCode.wp, lift2, Ty.hasFloat]
  have hlv' : loadVal (x64Mach.mem s) (.bits 64)
      ((AddrArg.baseDisp .rdi 0).eval (x64Mach.getGpr s)) = some va := by
    simpa [AddrArg.eval] using hlv
  have hsok' : storeOk (x64Mach.mem s) (.bits 64)
      ((AddrArg.baseDisp .rdi 0).eval (x64Mach.getGpr s)) := by
    simpa [AddrArg.eval] using hsok
  refine fun hinf kont =>
    x64Gpr_rmwMem_spec hc (by simp [AddrArg.regs, PArg.gprs, x64Scratch]) hlv' hsok'
      (by simp [Machine.PArgHolds]) hwp hinf fun s' ⟨rv, hrv, hm⟩ hfr => ?_
  cases hrv
  exact kont s' (by simpa [AddrArg.eval] using hm) hfr

/-! ## 3. End-to-End `Spill.hints` + Verified `Rega.lowerFn` Tests -/

meta def hintsOf (fs : List Fn) : List x64Target.toIsa.Hints :=
  fs.map (Fn.computeHints x64Target.toIsa x64LegalTarget)

meta def chk (fs : List Fn) : Bool :=
  checkCompile x64Target x64Layout x64LegalTarget [] [] 0 fs (hintsOf fs) 2048

meta def codeOf (fs : List Fn) : List Directive :=
  extractCode (compileModule x64Target.toIsa x64LegalTarget x64Target.frame.raBytes [] [] 0 fs
    (hintsOf fs))

meta def isRspSlotMem {w : Width} : RegOrMem w → Bool
  | .mem { base := some (.reg .rsp), idx := none, .. } => true
  | _ => false

meta def isRspMemAlu : Directive → Bool
  | .instr (.regular _ _ (.add _ (.regOrMem m@(.mem _)))) => isRspSlotMem m
  | .instr (.regular _ _ (.sub _ (.regOrMem m@(.mem _)))) => isRspSlotMem m
  | .instr (.regular _ _ (.and _ (.regOrMem m@(.mem _)))) => isRspSlotMem m
  | .instr (.regular _ _ (.or  _ (.regOrMem m@(.mem _)))) => isRspSlotMem m
  | .instr (.regular _ _ (.xor _ (.regOrMem m@(.mem _)))) => isRspSlotMem m
  | _ => false

meta def isRspMemCmpOrTest : Directive → Bool
  | .instr (.regular _ _ (.cmp m@(.mem _) _)) => isRspSlotMem m
  | .instr (.regular _ _ (.cmp _ (.regOrMem m@(.mem _)))) => isRspSlotMem m
  | .instr (.regular _ _ (.test m@(.mem _) _)) => isRspSlotMem m
  | _ => false

meta def isRmwIncDecOrMemOp : Directive → Bool
  | .instr (.regular _ _ (.inc (.mem _))) => true
  | .instr (.regular _ _ (.dec (.mem _))) => true
  | .instr (.regular _ _ (.add (.mem _) _)) => true
  | .instr (.regular _ _ (.sub (.mem _) _)) => true
  | .instr (.regular _ _ (.and (.mem _) _)) => true
  | .instr (.regular _ _ (.or  (.mem _) _)) => true
  | .instr (.regular _ _ (.xor (.mem _) _)) => true
  | _ => false

meta def isHeapLoadDir : Directive → Bool
  | .instr (.regular _ _ (.mov _ (.regOrMem (.mem { base := some (.reg r), .. })))) => r != .rsp
  | _ => false

meta def pingFn : Fn :=
  ⟨"ping", [i64], [i64], fun _ _ (x, ()) => .ret (.var x, ())⟩

/-- Function with >16 live variables across an external `ping` call (forcing slot spills) whose
cold/warm post-call uses exercise stack-slot `cmp`, `test`, `add`, non-comm `sub`, and `jnz`. -/
meta def slotPressureFn : Fn :=
  ⟨"slot_pressure", [i64, i64, i64, i64], [i64], fun V L (p0, p1, p2, p3, ()) =>
    let mkSum (a b : V i64) (k : V i64 → Expr V L [i64]) : Expr V L [i64] :=
      .let_ (op2 (.add i64) (.var a) (.var b)) fun (r, ()) => k r
    mkSum p0 p1 fun s0 => mkSum p1 p2 fun s1 => mkSum p2 p3 fun s2 => mkSum p3 p0 fun s3 =>
    mkSum s0 s1 fun s4 => mkSum s1 s2 fun s5 => mkSum s2 s3 fun s6 => mkSum s3 s0 fun s7 =>
    mkSum s4 s5 fun s8 => mkSum s5 s6 fun s9 => mkSum s6 s7 fun s10 => mkSum s7 s4 fun s11 =>
    mkSum s8 s9 fun s12 => mkSum s9 s10 fun s13 => mkSum s10 s11 fun s14 => mkSum s11 s8 fun s15 =>
    mkSum s12 s13 fun s16 => mkSum s14 s15 fun s17 =>
    .let_ (op2 (.cmp .ult i64) (.var s16) (.imm 5#64)) fun (bPre, ()) =>
    .call "ping" (as := [i64]) (bs := [i64]) (.var p0, ()) fun (c0, ()) =>
    .let_ (op2 (.add i64) (.var c0) (.var s0)) fun (w0, ()) =>
    .let_ (op2 (.add i64) (.var w0) (.var s1)) fun (w1, ()) =>
    .let_ (op2 (.add i64) (.var w1) (.var s2)) fun (w2, ()) =>
    .let_ (op2 (.add i64) (.var w2) (.var s3)) fun (w3, ()) =>
    .let_ (op2 (.add i64) (.var w3) (.var s4)) fun (w4, ()) =>
    .let_ (op2 (.add i64) (.var w4) (.var s5)) fun (w5, ()) =>
    .let_ (op2 (.sub i64) (.var w5) (.var s6)) fun (w6, ()) =>
    .let_ (op2 (.xor i64) (.var w6) (.var s7)) fun (w7, ()) =>
    .let_ (op2 (.or  i64) (.var w7) (.var s8)) fun (w8, ()) =>
    .let_ (op2 (.and i64) (.var w8) (.var s9)) fun (w9, ()) =>
    .let_ (op2 (.add i64) (.var w9) (.var s10)) fun (w10, ()) =>
    .let_ (op2 (.add i64) (.var w10) (.var s11)) fun (w11, ()) =>
    .let_ (op2 (.add i64) (.var w11) (.var s12)) fun (w12, ()) =>
    .let_ (op2 (.add i64) (.var w12) (.var s13)) fun (w13, ()) =>
    .let_ (op2 (.cmp .ult i64) (.var s16) (.imm 9#64)) fun (b0, ()) =>
    .let_ (op2 (.and i64) (.var s17) (.imm 7#64)) fun (m1, ()) =>
    .let_ (op2 (.cmp .ne i64) (.var m1) (.imm 0#64)) fun (b1, ()) =>
    .jnz (.var b0)
      (.jnz (.var b1)
        (.jnz (.var bPre) (.ret (.var w13, ())) (.ret (.var s16, ())))
        (.ret (.var s17, ())))
      (.ret (.var s14, ()))⟩

#guard chk [pingFn, slotPressureFn] = true

#guard
  let ds := codeOf [pingFn, slotPressureFn]
  (ds.filter isRspMemAlu).length > 0 && (ds.filter isRspMemCmpOrTest).length > 0

/-- Straight-line `[mem]` RMW positive suite covering `incq`, `decq`, `addq r`, `subq $c`,
`andl $c`, `orl r`, `xorq $c`, and two CSE-duplicate `[base+disp]` pointers. -/
meta def rmwPosFn : Fn :=
  ⟨"rmw_pos", [i64, i64, i32], [i64], fun _ _ (p, v64, v32, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 8#64)) fun (p8a, ()) =>
    .load i64 (.var p8a) fun x0 =>
    .let_ (op2 (.add i64) (.var x0) (.imm 1#64)) fun (y0, ()) =>
    .let_ (op2 (.add i64) (.var p) (.imm 8#64)) fun (p8b, ()) =>
    .store (.var y0) (.var p8b) <|
    .load i64 (.var p) fun x1 =>
    .let_ (op2 (.sub i64) (.var x1) (.imm 1#64)) fun (y1, ()) =>
    .store (.var y1) (.var p) <|
    .let_ (op2 (.add i64) (.var p) (.imm 16#64)) fun (p16, ()) =>
    .load i64 (.var p16) fun x2 =>
    .let_ (op2 (.add i64) (.var v64) (.var x2)) fun (y2, ()) =>
    .store (.var y2) (.var p16) <|
    .let_ (op2 (.add i64) (.var p) (.imm 24#64)) fun (p24, ()) =>
    .load i32 (.var p24) fun x3 =>
    .let_ (op2 (.and i32) (.var x3) (.imm 0xff#32)) fun (y3, ()) =>
    .store (.var y3) (.var p24) <|
    .let_ (op2 (.add i64) (.var p) (.imm 32#64)) fun (p32, ()) =>
    .load i32 (.var p32) fun x4 =>
    .let_ (op2 (.or i32) (.var x4) (.var v32)) fun (y4, ()) =>
    .store (.var y4) (.var p32) <|
    .let_ (op2 (.add i64) (.var p) (.imm 40#64)) fun (p40, ()) =>
    .load i64 (.var p40) fun x5 =>
    .let_ (op2 (.xor i64) (.var x5) (.imm 3#64)) fun (y5, ()) =>
    .store (.var y5) (.var p40) <|
    .ret (.var p, ())⟩

#guard chk [rmwPosFn] = true
#guard
  let ds := codeOf [rmwPosFn]
  (ds.filter isRmwIncDecOrMemOp).length == 6 && (ds.filter isHeapLoadDir).length == 0

/-- Negative RMW suite: different address (`q != p`), non-commutative RHS `v - x`, and
intervening store must NOT fold into a memory RMW instruction. -/
meta def rmwNegFn : Fn :=
  ⟨"rmw_neg", [i64, i64, i64], [i64], fun _ _ (p, q, z, ()) =>
    .load i64 (.var p) fun x0 =>
    .let_ (op2 (.add i64) (.var x0) (.imm 1#64)) fun (y0, ()) =>
    .store (.var y0) (.var q) <|
    .load i64 (.var p) fun x1 =>
    .let_ (op2 (.sub i64) (.var z) (.var x1)) fun (y1, ()) =>
    .store (.var y1) (.var p) <|
    .load i64 (.var q) fun x2 =>
    .store (t := i64) (.imm 7#64) (.var q) <|
    .let_ (op2 (.add i64) (.var x2) (.imm 1#64)) fun (y2, ()) =>
    .store (.var y2) (.var q) <|
    .ret (.var p, ())⟩

#guard chk [rmwNegFn] = true
#guard
  let ds := codeOf [rmwNegFn]
  (ds.filter isRmwIncDecOrMemOp).length == 0

#print axioms rmw_encodings_rfl
#print axioms slot_sub64_spec
#print axioms slot_add32_zero32
#print axioms heap_inc64_spec

end LeanQbeTest.T.SlotCmpRmwX64Test
