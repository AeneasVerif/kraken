module

/-
KrakenRunnerX64 - Run assembly instructions through Kraken Semantics and obtain results as json.

At this point this expects a file only containing a list of assembly instructions, no data block or similar.

Usage: krakenrunner_x64 <assembly.S>
       krakenrunner_x64 --generate <seed> <count> <length>  (random sequences that Kraken deems deterministic)
       krakenrunner_x64 --batch < sequences.json              (predict final states for a JSON array of sequences)

Arguments:
- assembly.S: Assembly source file

Output:
- Json formatted Machine state of Kraken after running the assembly.
  See StateSummary for format.
-/

import Kraken.Fuzzer
meta import Kraken.Fuzzer
import Kraken.X64.Parser
import Kraken.X64.PrintATT
import Kraken.X64.Semantics

open Lean Kraken.Fuzzer

-- TODO Add memory, for now we only track and compare registers and flags.
structure StateSummary where
  regs : List (String × UInt64)
  zmms : List (String × ZmmValue)
  flags : List (String × Bool)

-- Custom json serialization for the state summary. Registers with zero values
-- are not included.
instance : ToJson StateSummary where
  toJson s :=
    let regs := s.regs.filterMap (fun (k, v) => if v == 0 then none else some (k, Json.num v.toNat))
    let zmms := s.zmms.filterMap (fun (k, v) => if v == 0#512 then none else some (k, Json.str (String.ofList (Nat.toDigits 16 v.toNat))))
    let flags := s.flags.map (fun (k, v) => (k, toJson v))
    Json.mkObj [
      ("regs", Json.mkObj regs),
      ("zmms", Json.mkObj zmms),
      ("flags", Json.mkObj flags)
    ]

def summarize (s : MachineData) : StateSummary :=
  let r := s.regs
  let z := s.zmms
  let f := s.status
  { regs := [("rax", r.rax), ("rbx", r.rbx), ("rcx", r.rcx), ("rdx", r.rdx),
             ("rsi", r.rsi), ("rdi", r.rdi), ("rsp", r.rsp), ("rbp", r.rbp), ("r8", r.r8),
             ("r9", r.r9), ("r10", r.r10), ("r11", r.r11), ("r12", r.r12),
             ("r13", r.r13), ("r14", r.r14), ("r15", r.r15)],
    zmms := [("zmm0", z.zmm0), ("zmm1", z.zmm1), ("zmm2", z.zmm2), ("zmm3", z.zmm3),
             ("zmm4", z.zmm4), ("zmm5", z.zmm5), ("zmm6", z.zmm6), ("zmm7", z.zmm7),
             ("zmm8", z.zmm8), ("zmm9", z.zmm9), ("zmm10", z.zmm10), ("zmm11", z.zmm11),
             ("zmm12", z.zmm12), ("zmm13", z.zmm13), ("zmm14", z.zmm14), ("zmm15", z.zmm15),
             ("zmm16", z.zmm16), ("zmm17", z.zmm17), ("zmm18", z.zmm18), ("zmm19", z.zmm19),
             ("zmm20", z.zmm20), ("zmm21", z.zmm21), ("zmm22", z.zmm22), ("zmm23", z.zmm23),
             ("zmm24", z.zmm24), ("zmm25", z.zmm25), ("zmm26", z.zmm26), ("zmm27", z.zmm27),
             ("zmm28", z.zmm28), ("zmm29", z.zmm29), ("zmm30", z.zmm30), ("zmm31", z.zmm31)],
    flags := [("cf", f.cf), ("pf", f.pf), ("af", f.af),
              ("zf", f.zf), ("sf", f.sf), ("of", f.of)] }

-- Place the stack somewhere high in memory, aligned to 256 bytes. This will
-- help us avoid disagreements with the actual machine: we will avoid over/underflow
-- when we allocate stack memory using arithmetic instructions (which would happen
-- if the stack were at 0), and fixing the last byte of the address at 0 means that
-- we will match PF for these operations. The hardware harness (`reset_state` in
-- Kraken/X64/Test/asm_tests.py) runs with exactly this rsp and stack mapping.
def stackLocation : UInt64 := 0x7ffecafee200
def initData : MachineData := {regs := {rsp := stackLocation}, dmem := initStack stackLocation}

def finishCriterion (p : Program) (s : MachineState) : Bool :=
  s.2 = p.fakeLayout.labels.label _end

def runKraken (asmCode : String)
    : Except String MachineState := do
  let prog ← Kraken.X64.Parser.parse (_start ++ ":" ++ asmCode ++ "\n" ++ _end ++ ":")
  let initState : MachineState := (initData, prog.fakeLayout.labels.label _start)
  prog.fakeLayout.eval initState (finishCriterion prog)

/-! ## Fuzzer instantiation -/

/-- The six status flag values as bits, in the layout of `NondetSupportingType.from_hash`
(cf, pf, af, zf, sf, of = bits 0..5). -/
instance : StatusFlagBits StatusFlags where
  numBits := 6
  toBits f := f.cf.toNat ||| f.pf.toNat <<< 1 ||| f.af.toNat <<< 2 ||| f.zf.toNat <<< 3 ||| f.sf.toNat <<< 4 ||| f.of.toNat <<< 5
  ofBits := NondetSupportingType.from_hash

-- Runs `Effects` to completion, resolving every `undefined` choice with `h`. Also returns
-- whether any `undefined` choice was made.
partial def evalEffects (h : UInt64) (sawUndef : Bool) : Effects → Option (MachineData × Bool)
  | .done (s, _) => some (s, sawUndef)
  | .require_read_access _ _ ok | .require_write_access _ _ ok | .require_exec_access _ ok => evalEffects h sawUndef (ok ())
  | @Effects.undefined _ t cont => evalEffects h true (cont (t.from_hash h))
  | _ => none

instance : Gen Width := ⟨gen_ctors% Width⟩
instance : Gen AvxWidth := ⟨gen_ctors% AvxWidth⟩
instance : Gen RegMm := ⟨gen_ctors% RegMm⟩
instance : Gen Reg64 := ⟨gen_ctors% Reg64⟩
instance : Gen CondCode := ⟨gen_ctors% CondCode⟩
instance : Gen AddrIndex := ⟨gen_ctors% AddrIndex⟩

-- No nop lengths or alignments; other control flow is rejected by `stepDeterministic`.
instance : Gen Nat := ⟨failure⟩
instance : Gen Int64 := ⟨genInt64 #[3, 8, 16, 32, 64]⟩
-- Code addresses differ between Kraken's layout and the hardware binary, so no labels, nor
-- `before/after_current_instruction`, nor rip-relative addressing.
instance : Gen ConstExpr := ⟨.int64 <$> gen⟩
instance : Gen RegOrRip := ⟨.reg <$> gen⟩
-- Indexed families, which `gen_ctors%` can't handle.
instance {w} : Gen (Reg w) where gen := match w with
  | .W8 => oneOf #[(.low · .W8) <$> gen, pick #[.ah, .bh, .ch, .dh]] | w => (.low · w) <$> gen
instance {w} : Gen (AvxReg w) where gen := match w with
  | .W128 => .xmm <$> gen | .W256 => .ymm <$> gen | .W512 => .zmm <$> gen
-- Half of all addresses are slots in Kraken's stack mapping [rsp - 800, rsp) (usable when the
-- instruction's address size is 64 bits).
instance : Gen AddrExpr := ⟨oneOf #[gen_ctors% AddrExpr,
  return { base := some (.reg .rsp), idx := none, disp := .int64 (.ofInt (-1 - (← nextNat stackSize))) }]⟩

instance : Gen ShiftCountExpr := ⟨gen_ctors% ShiftCountExpr⟩
instance : Gen RelRegOrMem := ⟨gen_ctors% RelRegOrMem⟩
instance {w} : Gen (RegOrMem w) := ⟨gen_ctors% RegOrMem⟩
instance {w} : Gen (Operand w) := ⟨gen_ctors% Operand⟩
instance {w} : Gen (AvxRegOrMem w) := ⟨gen_ctors% AvxRegOrMem⟩
instance {w} : Gen (Operation w) := ⟨gen_ctors% Operation⟩
instance {w} : Gen (AvxOperation w) := ⟨gen_ctors% AvxOperation⟩
instance : Gen Instr := ⟨gen_ctors% Instr⟩

-- Loads a random 64-bit value into a register other than rsp.
def genSeed : GenM String := do
  let r ← gen; guard (r != Reg64.rsp)
  let r := Kraken.X64.ATT.reg (.low r .W64)
  let movabs := s!"movabsq ${← nextNat (2 ^ 64)}, {r}"
  if ← pick #[true, false] then return movabs
  -- Also copy it into one of xmm0-15 via the stack; they start zeroed, so SSE ops would
  -- otherwise see only zeros.
  return s!"{movabs}\nmovq {r}, -16(%rsp)\nmovq {r}, -8(%rsp)\nmovups -16(%rsp), %xmm{← nextNat 16}"

-- APX is excluded because the hardware lacks it (e.g. `imul %edx, %r12d, %edi`), AVX-512 because
-- the harness only observes ymm0-15.
def fuzzConfig : FuzzConfig MachineData StatusFlags StateSummary where
  initData := initData
  getStatus := (·.status)
  setStatus s status := { s with status }
  parseSteps asmCode := do
    let exe := (← (Kraken.X64.Parser.parse asmCode).toOption).fakeLayout
    let := exe.labels
    return exe.withAddresses.map fun (pc, dir, sz) =>
      (pc, (fun s p h => evalEffects h false (dir.interp s p (fun s => .done (s, p.upper)) (fun _ _ => .unimplemented "jump"))), sz)
  summarize := summarize
  genInstr := Kraken.X64.ATT.instr <$> gen
  runAssembler path := IO.Process.output { cmd := "as", args := #["-march=+noapx_f+noavx512f", "-o", "/dev/null", path.toString] }
  genSeed := genSeed
  defineAllFlagsInstr := "addq %rax, %rax"

public def main (args : List String) : IO UInt32 := do
  if let some code ← fuzzConfig.handleCli? args then return code

  if args.isEmpty then return 1

  let asmCode ← IO.FS.readFile args[0]!

  match runKraken asmCode with
  | .ok (state, _) =>
      IO.println (toJson (summarize state)).compress
      return 0
  | .error e =>
      IO.eprintln s!"Kraken Semantic Error: {e}"
      return 1
