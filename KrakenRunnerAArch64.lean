module

/-
KrakenRunnerAArch64 - Run AArch64 assembly instructions through Kraken Semantics and obtain results as json.

Usage: krakenrunner_aarch64 <assembly.S> [init_regs.json]
       krakenrunner_aarch64 --generate <seed> <count> <length>  (random sequences that Kraken deems deterministic)
       krakenrunner_aarch64 --batch < sequences.json            (predict final states for a JSON array of sequences)

Arguments:
- assembly.S: Assembly source file
- init_regs.json: Optional JSON file providing initial register values

Output:
- Json formatted Machine state of Kraken after running the assembly.
-/

import Kraken.AArch64.Parser
import Kraken.AArch64.Print
import Kraken.AArch64.Semantics
import Kraken.Fuzzer
meta import Kraken.Fuzzer

open Lean Kraken.Fuzzer

structure StateSummary where
  regs : List (String × UInt64)
  flags : List (String × Bool)

instance : ToJson StateSummary where
  toJson s :=
    let regs := s.regs.map (fun (k, v) => (k, Json.num v.toNat))
    let flags := s.flags.map (fun (k, v) => (k, toJson v))
    Json.mkObj [
      ("regs", Json.mkObj regs),
      ("flags", Json.mkObj flags)
    ]

def summarize (s : MachineData) : StateSummary :=
  let r := s.regs
  let f := s.status
  { regs := [("x0", r.X0), ("x1", r.X1), ("x2", r.X2), ("x3", r.X3),
             ("x4", r.X4), ("x5", r.X5), ("x6", r.X6), ("x7", r.X7),
             ("x8", r.X8), ("x9", r.X9), ("x10", r.X10), ("x11", r.X11),
             ("x12", r.X12), ("x13", r.X13), ("x14", r.X14), ("x15", r.X15),
             ("x16", r.X16), ("x17", r.X17), ("x18", r.X18), ("x19", r.X19),
             ("x20", r.X20), ("x21", r.X21), ("x22", r.X22), ("x23", r.X23),
             ("x24", r.X24), ("x25", r.X25), ("x26", r.X26), ("x27", r.X27),
             ("x28", r.X28), ("x29", r.X29), ("x30", r.X30), ("sp", r.SP)],
    flags := [("n", f.n), ("z", f.z), ("c", f.c), ("v", f.v)] }

-- Map the stack at a 16B/256B-aligned address that fits within qemu-aarch64's guest
-- address space when linked with `--section-start=.stack=...`.
def stackLocation : UInt64 := 0xcafe200
def initData : MachineData := {regs := {SP := stackLocation}, dmem := initStack stackLocation}

def parseInitRegs (jsonStr : String) : Except String Reg64s := do
  let json ← Json.parse jsonStr
  let getVal (k : String) (d : UInt64 := 0) : UInt64 :=
    match json.getObjValAs? Nat k with
    | .ok v => v.toUInt64
    | .error _ => d

  return {
    X0 := getVal "x0",   X1 := getVal "x1",   X2 := getVal "x2",   X3 := getVal "x3",
    X4 := getVal "x4",   X5 := getVal "x5",   X6 := getVal "x6",   X7 := getVal "x7",
    X8 := getVal "x8",   X9 := getVal "x9",   X10 := getVal "x10", X11 := getVal "x11",
    X12 := getVal "x12", X13 := getVal "x13", X14 := getVal "x14", X15 := getVal "x15",
    X16 := getVal "x16", X17 := getVal "x17", X18 := getVal "x18", X19 := getVal "x19",
    X20 := getVal "x20", X21 := getVal "x21", X22 := getVal "x22", X23 := getVal "x23",
    X24 := getVal "x24", X25 := getVal "x25", X26 := getVal "x26", X27 := getVal "x27",
    X28 := getVal "x28", X29 := getVal "x29", X30 := getVal "x30", SP := getVal "sp" stackLocation
  }

def finishCriterion (prog : Program) (s : MachineState) : Bool :=
  let layout := Program.fakeLayout prog
  s.2 = layout.labels.label _end

def runKraken (asmCode : String) (initRegs : Reg64s := initData.regs)
    : Except String MachineState := do
  let stripped := Kraken.AArch64.Parser.stripDirectives (_start ++ ":\n" ++ asmCode ++ "\n" ++ _end ++ ":\n")
  let prog ← Kraken.AArch64.Parser.parse stripped
  let layout := Program.fakeLayout prog
  let initState : MachineState := ({regs := initRegs, dmem := initStack stackLocation}, layout.labels.label _start)
  layout.eval initState (finishCriterion prog)

/-! ## Fuzzer instantiation -/

/-- The four status flag values as bits, in the layout of `NondetSupportingType.from_hash`
(n, z, c, v = bits 0..3). -/
instance : StatusFlagBits StatusFlags where
  numBits := 4
  toBits f := f.n.toNat ||| f.z.toNat <<< 1 ||| f.c.toNat <<< 2 ||| f.v.toNat <<< 3
  ofBits := NondetSupportingType.from_hash

-- Runs `Effects` to completion, resolving every `undefined` choice with `h`. Also returns
-- whether any `undefined` choice was made.
partial def evalEffects (h : UInt64) (sawUndef : Bool) : Effects → Option (MachineData × Bool)
  | .done (s, _) => some (s, sawUndef)
  | .require_read_access _ _ ok | .require_write_access _ _ ok | .require_exec_access _ ok => evalEffects h sawUndef (ok ())
  | @Effects.undefined _ t cont => evalEffects h true (cont (t.from_hash h))
  | _ => none

instance {w} : CoeOut (Operation w) Instr := ⟨(⟨w, ·⟩)⟩

instance : Gen RegWidth := ⟨gen_ctors% RegWidth⟩
instance : Gen XReg := ⟨gen_ctors% XReg⟩
instance : Gen XRegOrSp := ⟨gen_ctors% XRegOrSp⟩
instance : Gen XRegOrXzr := ⟨gen_ctors% XRegOrXzr⟩
instance {w} : Gen (RegOrSp w) := ⟨(.low · w) <$> gen⟩
instance {w} : Gen (RegOrZr w) := ⟨(.low · w) <$> gen⟩
instance : Gen RegOrSpW := ⟨gen_ctors% RegOrSpW⟩
instance : Gen RegOrZrW := ⟨gen_ctors% RegOrZrW⟩
instance : Gen ExtendType := ⟨gen_ctors% ExtendType⟩
instance : Gen MemExtendType := ⟨gen_ctors% MemExtendType⟩
instance : Gen ExtendAmount := ⟨gen_ctors% ExtendAmount⟩
instance : Gen MemExtendAmount := ⟨gen_ctors% MemExtendAmount⟩
instance : Gen ShiftType := ⟨gen_ctors% ShiftType⟩
instance : Gen ImmShift := ⟨gen_ctors% ImmShift⟩
instance {w} : Gen (MovShift w) where gen := match w with
  | .W32 => pick #[.LSL0, .LSL16] | .W64 => pick #[.LSL0, .LSL16, .LSL32, .LSL48]
instance : Gen Index := ⟨gen_ctors% Index⟩
instance : Gen Extend := ⟨gen_ctors% Extend⟩
instance : Gen MemExtend := ⟨gen_ctors% MemExtend⟩
instance : Gen ExtRegExpr := ⟨gen_ctors% ExtRegExpr⟩
instance : Gen MemExtRegExpr := ⟨gen_ctors% MemExtRegExpr⟩
instance : Gen CondCode := ⟨gen_ctors% CondCode⟩

-- Bit positions, bitfield bounds and condition flags are in 0..63.
instance : Gen Nat := ⟨oneOf #[nextNat 16, nextNat 32, nextNat 64]⟩
instance : Gen Int64 := ⟨genInt64 #[3, 6, 8, 12, 16, 32, 64]⟩
instance : Gen ConstExpr := ⟨.int64 <$> gen⟩

instance : Gen ImmExpr := ⟨gen_ctors% ImmExpr⟩
instance {w} : Gen (ShiftRegExpr w) := ⟨gen_ctors% ShiftRegExpr⟩
instance : Gen ImmAddrExpr := ⟨gen_ctors% ImmAddrExpr⟩
instance : Gen AddrOff := ⟨gen_ctors% AddrOff⟩
-- Half of all addresses are slots near sp in Kraken's stack mapping [sp - 800, sp).
instance : Gen AddrExpr := ⟨oneOf #[gen_ctors% AddrExpr, do
  let off : Int := (← pick #[-16, -8, -4, -2, -1, 4, 8, 16]) * (← nextNat 16)
  return { base := .SP, off := .imm { imm := .int64 (.ofInt off), index := ← gen } }]⟩
instance : Gen UnscaledAddrExpr := ⟨oneOf #[gen_ctors% UnscaledAddrExpr,
  return { base := .SP, imm := .int64 (.ofInt ((← nextNat 512) - 256)) }]⟩
instance : Gen LitAddrExpr := ⟨gen_ctors% LitAddrExpr⟩
instance : Gen LitPoolExpr := ⟨gen_ctors% LitPoolExpr⟩
instance : Gen _root_.Literal := ⟨gen_ctors% _root_.Literal⟩
instance : Gen AddrOrLit := ⟨gen_ctors% AddrOrLit⟩
instance : Gen ExtOrImmReg := ⟨gen_ctors% ExtOrImmReg⟩
instance : Gen Instr := ⟨gen_ctors% Operation⟩

def runAssembler (path : System.FilePath) : IO IO.Process.Output := do
  let searchPath := ((← IO.getEnv "PATH").getD "").splitOn ":"
  for (cmd, args) in #[
    ("aarch64-linux-gnu-as", #[]),
    ("aarch64-none-elf-as", #[]),
    ("clang", #["--target=aarch64-linux-gnu", "-c", "-x", "assembler", "-ferror-limit=0"]),
    ("clang-19", #["--target=aarch64-linux-gnu", "-c", "-x", "assembler", "-ferror-limit=0"]),
    ("clang-18", #["--target=aarch64-linux-gnu", "-c", "-x", "assembler", "-ferror-limit=0"]),
    ("clang-17", #["--target=aarch64-linux-gnu", "-c", "-x", "assembler", "-ferror-limit=0"]),
    ("clang-16", #["--target=aarch64-linux-gnu", "-c", "-x", "assembler", "-ferror-limit=0"])
  ] do
    if ← searchPath.anyM fun dir => (System.FilePath.mk dir / cmd).pathExists then
      return ← IO.Process.output { cmd, args := args ++ #["-o", "/dev/null", path.toString] }
  throw (.userError "no AArch64 assembler found")

-- Loads a random 64-bit value into a general-purpose register.
def genSeed : GenM String := do
  let r := Kraken.AArch64.Print.xreg .W64 (← gen)
  let ldr := s!"ldr {r}, ={← nextNat (2 ^ 64)}"
  if ← pick #[true, false] then return ldr
  -- Also push it onto the stack, moving sp into the mapped stack region so positive-offset
  -- and post-indexed [sp, ...] accesses are in bounds and see non-0xff data.
  return s!"{ldr}\nstr {r}, [sp, #-16]!"

def fuzzConfig : FuzzConfig MachineData StatusFlags StateSummary where
  initData := initData
  getStatus := (·.status)
  setStatus s status := { s with status }
  parseSteps asmCode := do
    let exe := Program.fakeLayout (← (Kraken.AArch64.Parser.parse asmCode).toOption)
    let := exe.labels
    return exe.withAddresses.map fun (pc, dir, sz) =>
      (pc, (fun s p h => evalEffects h false (dir.interp s p (fun s => .done (s, p.upper)) (fun _ _ => .unimplemented "jump"))), sz)
  summarize := summarize
  genInstr := Kraken.AArch64.Print.instr <$> gen
  runAssembler := runAssembler
  genSeed := genSeed
  defineAllFlagsInstr := "adds x0, x0, x0"

public def main (args : List String) : IO UInt32 := do
  if let some code ← fuzzConfig.handleCli? args then return code

  if args.isEmpty then return (1 : UInt32)

  let asmCode ← IO.FS.readFile args[0]!
  let mut initRegs : Reg64s := initData.regs
  if args.length > 1 then
    let jsonStr ← IO.FS.readFile args[1]!
    match parseInitRegs jsonStr with
    | .ok regs => initRegs := regs
    | .error e =>
        IO.eprintln s!"Failed to parse init json: {e}"
        return (1 : UInt32)

  match runKraken asmCode initRegs with
  | .ok (state, _) =>
      IO.println (toJson (summarize state)).compress
      return (0 : UInt32)
  | .error e =>
      IO.eprintln s!"Kraken Semantic Error: {e}"
      return (1 : UInt32)
