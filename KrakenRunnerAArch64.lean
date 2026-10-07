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
import Kraken.Mem
import Lean.Data.Json
public meta import Lean.Elab.Term

open Lean

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

def _start: String := "_start"
def _end: String := "_end"

-- Give the program a stack of 800B initially, mapped at a 16B/256B-aligned address that
-- fits within qemu-aarch64's guest address space when linked with `--section-start=.stack=...`.
def stackSize := 800
def stackLocation : UInt64 := 0xcafe200
def initStack : DataMem := (List.replicate stackSize 0xff).At (stackLocation - stackSize)
def initData : MachineData := {regs := {SP := stackLocation}, dmem := initStack}

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

def finishCriterion (prog: Program) (s: MachineState): Bool :=
  let layout := Program.fakeLayout prog
  s.2 = layout.labels.label _end

def runKraken (asmCode : String) (initRegs : Reg64s := initData.regs)
    : Except String MachineState := do
  let stripped := Kraken.AArch64.Parser.stripDirectives (_start ++ ":\n" ++ asmCode ++ "\n" ++ _end ++ ":\n")
  let prog ← Kraken.AArch64.Parser.parse stripped
  let layout := Program.fakeLayout prog
  let initState: MachineState := ({regs := initRegs, dmem := initStack}, layout.labels.label _start)
  layout.eval initState (finishCriterion prog)

/-! ## Determinism checking, with Semantics.lean in the loop

`Executable.eval` produces *one* possible behavior, resolving each `undefined` choice to an
arbitrary value (a hash of the registers). The fuzzer instead needs to know whether the hardware's
result is predictable at all, i.e. whether it is the same for *every* resolution of the `undefined`
choices; it discards sequences for which it isn't. -/

/-- The four status flag values as bits, in the layout of `NondetSupportingType.from_hash`
(n, z, c, v = bits 0..3). -/
def StatusFlags.toBits (f : StatusFlags) : Nat :=
  f.n.toNat ||| f.z.toNat <<< 1 ||| f.c.toNat <<< 2 ||| f.v.toNat <<< 3

/-- Which status flags are currently undefined, i.e. may hold either value, as a mask in the
`StatusFlags.toBits` layout. -/
structure UndefFlags where
  mask : Nat
  deriving BEq

def UndefFlags.none : UndefFlags := ⟨0⟩

/-- Every assignment of the status flags that agrees with `f` on the defined flags. -/
def UndefFlags.completions (u : UndefFlags) (f : StatusFlags) : List StatusFlags :=
  (List.range 16).filter (fun m => m &&& u.mask == m) |>.map fun m =>
    NondetSupportingType.from_hash (f.toBits &&& (15 ^^^ u.mask) ||| m).toUInt64

/-- The flags on which any of `fs` differs from `f`. -/
def UndefFlags.disagreeing (f : StatusFlags) (fs : Array StatusFlags) : UndefFlags :=
  ⟨fs.foldl (fun acc g => acc ||| (g.toBits ^^^ f.toBits)) 0⟩

-- Runs `Effects` to completion, resolving every `undefined` choice with `h`. Also returns
-- whether any `undefined` choice was made.
partial def evalEffects (h : UInt64) (sawUndef : Bool) : Effects → Option (MachineData × Bool)
  | .done (s, _) => some (s, sawUndef)
  | .require_read_access _ _ ok | .require_write_access _ _ ok | .require_exec_access _ ok => evalEffects h sawUndef (ok ())
  | @Effects.undefined _ t cont => evalEffects h true (cont (t.from_hash h))
  | _ => none

/-- Executes `asmCode` (straight-line, no jumps) from `d`, where the flags in `u` are currently
undefined. Each instruction is run under every assignment of the undefined flags, at two different
code addresses (to reject PC-relative `adr`/`adrp`), and, if it makes `undefined` choices, with
those resolved once to all-zeros and once to all-ones. Fails unless registers and memory agree
across all runs; returns the resulting state and the flags that disagree. -/
def stepDeterministic (d : MachineData) (u : UndefFlags) (asmCode : String) : Option (MachineData × UndefFlags) := do
  let exe := Program.fakeLayout (← (Kraken.AArch64.Parser.parse asmCode).toOption)
  let := exe.labels
  let mut (d, u) := (d, u)
  for (pc, dir, sz) in exe.withAddresses do
    let run (status : StatusFlags) (pc : Int64) (h : UInt64) : Option (MachineData × Bool) :=
      let p : Std.Rco Int64 := .mk pc (pc + .ofNat sz)
      evalEffects h false (dir.interp { d with status } p (fun s => .done (s, p.upper)) (fun _ _ => .unimplemented "jump"))
    let mut outs : Array MachineData := #[(← run d.status (pc + 0x1000) 0).1]
    for status in u.completions d.status do
      let (s, sawUndef) ← run status pc 0
      outs := outs.push s
      if sawUndef then outs := outs.push (← run status pc (-1)).1
    let s0 ← outs[0]?
    if outs.any ({ · with status := s0.status } != s0) then failure
    (d, u) := (s0, .disagreeing s0.status (outs.map (·.status)))
  return (d, u)

def predict (asmCode : String) : Json :=
  match stepDeterministic initData .none asmCode with
  | some (s, ⟨0⟩) => Json.mkObj [("ok", toJson true), ("state", toJson (summarize s))]
  | _ => Json.mkObj [("ok", toJson false), ("error", toJson "unparseable, faulting, jumping, or non-deterministic")]

/-! ## Random instruction sequence generation

Candidate instructions are random `Instr`s: `gen_ctors%` derives generators from the constructors
in Syntax.lean, so every instruction form is covered without being listed here; the hand-written
instances only choose operand values. Each `--generate` prints 5000 of them with `Print.instr` and keeps
those the assembler accepts (`genPool`, `assemblable`); every slot of a sequence then draws from that pool
until Semantics.lean deems the candidate deterministic in the current state (`stepDeterministic`). -/

abbrev GenM := OptionT (StateM StdGen)
def nextNat (n : Nat) : GenM Nat := modifyGet (randNat · 0 (n - 1))
def oneOf {α : Type} (xs : Array (GenM α)) : GenM α := do xs.getD (← nextNat xs.size) failure
def pick {α : Type} (xs : Array α) : GenM α := oneOf (xs.map pure)

class Gen (α : Type) where gen : GenM α
export Gen (gen)

open Elab Term in
/-- Picks a constructor of inductive type `T` uniformly (inferring `T`'s parameters) and draws each
of its fields from `gen`. -/
elab "gen_ctors% " t:ident : term <= ty => do
  let alts ← (← getConstInfoInduct (← realizeGlobalConstNoOverload t)).ctors.toArray.mapM fun c => do
    let info ← getConstInfoCtor c
    let hole ← `(_)
    let field ← `((← gen))
    `(do return @$(mkIdent c) $(.replicate info.numParams hole)* $(.replicate info.numFields field)*)
  elabTerm (← `(oneOf #[$alts,*])) ty

instance {w} : CoeOut (Operation w) Instr := ⟨(⟨w, ·⟩)⟩

instance {α : Type} [Gen α] : Gen (Option α) := ⟨gen_ctors% Option⟩
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

-- No labels; bit positions, bitfield bounds and condition flags are in 0..63.
instance : Gen String := ⟨failure⟩
instance : Gen Nat := ⟨oneOf #[nextNat 16, nextNat 32, nextNat 64]⟩
-- Small values, the boundaries of each width, and uniformly random values of each width.
instance : Gen Int64 where gen := do
  let n : Int := 2 ^ (← pick #[3, 6, 8, 12, 16, 32, 64])
  return .ofInt (← pick #[0, 1, -1, n / 2 - 1, -(n / 2), n - 1, (← nextNat n.toNat)])
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

/-- The candidates that the AArch64 assembler accepts without errors or warnings. -/
def assemblable (cands : Array String) : IO (Array String) := IO.FS.withTempFile fun h path => do
  h.putStr ("\n".intercalate cands.toList ++ "\n"); h.flush
  let out ← runAssembler path
  let pfx := path.toString ++ ":"
  let bad := out.stderr.splitOn "\n" |>.filterMap fun l =>
    (l.dropPrefix? pfx).bind (·.takeWhile Char.isDigit |>.toString.toNat?)
  if out.exitCode != 0 && bad.isEmpty then throw (.userError out.stderr)
  return cands.zipIdx.filterMap fun (c, i) => if bad.contains (i + 1) then none else some c

def genPool (n : Nat) : StateM StdGen (Array String) :=
  (Array.range n).filterMapM fun _ => (Kraken.AArch64.Print.instr <$> gen).run

-- Loads a random 64-bit value into a general-purpose register.
def genSeed : GenM String := do
  let r := Kraken.AArch64.Print.xreg .W64 (← gen)
  let ldr := s!"ldr {r}, ={← nextNat (2 ^ 64)}"
  if ← pick #[true, false] then return ldr
  -- Also push it onto the stack, moving sp into the mapped stack region so positive-offset
  -- and post-indexed [sp, ...] accesses are in bounds and see non-0xff data.
  return s!"{ldr}\nstr {r}, [sp, #-16]!"

-- Four random register initializations (`genSeed`) followed by `length` instructions from `pool`, each drawn
-- until `stepDeterministic` accepts one. A final `adds` makes all flags defined.
def genSequence (pool : Array String) (length : Nat) : StateM StdGen String := do
  let mut (d, undef, lines) := (initData, UndefFlags.none, #[])
  for i in [0 : 4 + length] do
    for _ in [0 : 200] do
      let some cand ← (if i < 4 then genSeed else pick pool).run | continue
      if let some (d', undef') := stepDeterministic d undef cand then
        (d, undef, lines) := (d', undef', lines.push cand)
        break
  if undef != .none then lines := lines.push "adds x0, x0, x0"
  return "\n".intercalate lines.toList

public def main (args : List String) : IO UInt32 := do
  match args with
  | ["--generate", seed, count, length] =>
    let (pool, g) := (genPool 5000).run (mkStdGen seed.toNat!)
    let pool ← assemblable pool
    let gen := (List.range count.toNat!).mapM fun _ => genSequence pool length.toNat!
    IO.println (toJson (gen.run' g).run).compress
    return 0
  | ["--batch"] =>
    let raw ← (← IO.getStdin).readToEnd
    let seqs ← IO.ofExcept (Json.parse raw >>= fromJson? (α := Array String))
    IO.println (toJson (seqs.map predict)).compress
    return 0
  | _ => pure ()

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
