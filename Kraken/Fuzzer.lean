module

/-
Common infrastructure for Kraken's differential instruction fuzzers:
- Status flag bitmasks (`StatusFlagBits`, `UndefFlags`) and determinism checking (`stepDeterministic`)
- Random instruction and operand generation (`GenM`, `Gen`, `gen_ctors%`, `genInt64`)
- Assembler filtering (`filterAssemblable`), sequence generation (`genSequence`), and CLI (`handleCli?`)
-/

public import Kraken.Mem
public import Lean.Data.Json
public meta import Lean.Elab.Term

public section

open Lean

namespace Kraken.Fuzzer

def _start : String := "_start"
def _end : String := "_end"

-- Give the program a stack of 800B initially, mapped at a plausible place.
def stackSize : Nat := 800

def initStack (stackLocation : UInt64) : Mem 64 :=
  (List.replicate stackSize 0xff).At (stackLocation - stackSize)

/-! ## Determinism checking -/

/-- Mapping between an architecture's `StatusFlags` structure and a compact `numBits`-bit integer. -/
class StatusFlagBits (Flags : Type) where
  numBits : Nat
  toBits : Flags → Nat
  ofBits : UInt64 → Flags

/-- Which status flags are currently undefined, i.e. may hold either value, as a bitmask in the
`StatusFlagBits.toBits` layout. -/
structure UndefFlags where
  mask : Nat
  deriving BEq

def UndefFlags.none : UndefFlags := ⟨0⟩

/-- Every assignment of the status flags that agrees with `f` on the defined flags. -/
def UndefFlags.completions {Flags : Type} [inst : StatusFlagBits Flags] (u : UndefFlags) (f : Flags) : List Flags :=
  let n := 1 <<< inst.numBits
  (List.range n).filter (fun m => m &&& u.mask == m) |>.map fun m =>
    inst.ofBits (inst.toBits f &&& ((n - 1) ^^^ u.mask) ||| m).toUInt64

/-- The flags on which any of `fs` differs from `f`. -/
def UndefFlags.disagreeing {Flags : Type} [inst : StatusFlagBits Flags] (f : Flags) (fs : Array Flags) : UndefFlags :=
  ⟨fs.foldl (fun acc g => acc ||| (inst.toBits g ^^^ inst.toBits f)) 0⟩

/-! ## Random instruction sequence generation -/

abbrev GenM := OptionT (StateM StdGen)
def nextNat (n : Nat) : GenM Nat := modifyGet (randNat · 0 (n - 1))
def oneOf {α : Type} (xs : Array (GenM α)) : GenM α := do xs.getD (← nextNat xs.size) failure
def pick {α : Type} (xs : Array α) : GenM α := oneOf (xs.map pure)

class Gen (α : Type) where gen : GenM α
export Gen (gen)

public meta section

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

end

instance {α : Type} [Gen α] : Gen (Option α) := ⟨gen_ctors% Option⟩
instance : Gen String := ⟨failure⟩

/-- Small values (below 2^3), the boundaries of each width in `widths`, and uniformly random values
of each width. -/
def genInt64 (widths : Array Nat) : GenM Int64 := do
  let n : Int := 2 ^ (← pick widths)
  return .ofInt (← pick #[0, 1, -1, n / 2 - 1, -(n / 2), n - 1, (← nextNat n.toNat)])

/-- Filters `cands` to those that `runAssembler` assembles without errors or warnings. -/
def filterAssemblable (runAssembler : System.FilePath → IO IO.Process.Output) (cands : Array String) : IO (Array String) :=
  IO.FS.withTempFile fun h path => do
    h.putStr ("\n".intercalate cands.toList ++ "\n"); h.flush
    let out ← runAssembler path
    let pfx := path.toString ++ ":"
    let bad := out.stderr.splitOn "\n" |>.filterMap fun l =>
      (l.dropPrefix? pfx).bind (·.takeWhile Char.isDigit |>.toString.toNat?)
    if out.exitCode != 0 && bad.isEmpty then throw (.userError out.stderr)
    return cands.zipIdx.filterMap fun (c, i) => if bad.contains (i + 1) then none else some c

/-- Architecture-specific hooks for the differential fuzzer. -/
structure FuzzConfig (MachineData StatusFlags StateSummary : Type) where
  initData : MachineData
  getStatus : MachineData → StatusFlags
  setStatus : MachineData → StatusFlags → MachineData
  /-- Parses `asmCode` into `(pc, step, size)` triples where `step s p h` runs the directive at
  address range `p` from state `s`, resolving `undefined` choices with `h`. -/
  parseSteps : String → Option (List (Int64 × (MachineData → Std.Rco Int64 → UInt64 → Option (MachineData × Bool)) × Nat))
  summarize : MachineData → StateSummary
  genInstr : GenM String
  runAssembler : System.FilePath → IO IO.Process.Output
  genSeed : GenM String
  defineAllFlagsInstr : String

variable {MachineData StatusFlags StateSummary : Type}
  [BEq MachineData] [StatusFlagBits StatusFlags] [ToJson StateSummary]

/-- Executes `asmCode` (straight-line, no jumps) from `d`, where the flags in `u` are currently
undefined. Each instruction is run under every assignment of the undefined flags, at two different
code addresses (to reject PC-relative instructions), and, if it makes `undefined` choices, with
those resolved once to all-zeros and once to all-ones. Fails unless registers and memory agree
across all runs; returns the resulting state and the flags that disagree.

Resolving to all-zeros and all-ones makes every bit of an `undefined` value differ between the two
runs. That suffices to expose any dependence on it because `Semantics.lean` only ever stores an
undefined choice directly into a flag, all flags, or a register, never computes with it. -/
def FuzzConfig.stepDeterministic (cfg : FuzzConfig MachineData StatusFlags StateSummary)
    (d : MachineData) (u : UndefFlags) (asmCode : String) : Option (MachineData × UndefFlags) := do
  let steps ← cfg.parseSteps asmCode
  let mut (d, u) := (d, u)
  for (pc, step, sz) in steps do
    let run (status : StatusFlags) (pc : Int64) (h : UInt64) : Option (MachineData × Bool) :=
      step (cfg.setStatus d status) (.mk pc (pc + .ofNat sz)) h
    let dStatus := cfg.getStatus d
    let mut outs : Array MachineData := #[]
    for status in u.completions dStatus do
      let (s, sawUndef) ← run status pc 0
      outs := outs.push s
      if sawUndef then outs := outs.push (← run status pc (-1)).1
    outs := outs.push (← run dStatus (pc + 0x1000) 0).1
    let s0 ← outs[0]?
    let s0Status := cfg.getStatus s0
    if outs.any (cfg.setStatus · s0Status != s0) then failure
    (d, u) := (s0, .disagreeing s0Status (outs.map cfg.getStatus))
  return (d, u)

def FuzzConfig.predict (cfg : FuzzConfig MachineData StatusFlags StateSummary) (asmCode : String) : Json :=
  match cfg.stepDeterministic cfg.initData .none asmCode with
  | some (s, ⟨0⟩) => Json.mkObj [("ok", toJson true), ("state", toJson (cfg.summarize s))]
  | _ => Json.mkObj [("ok", toJson false), ("error", toJson "unparseable, faulting, jumping, or non-deterministic")]

def FuzzConfig.genPool (cfg : FuzzConfig MachineData StatusFlags StateSummary) (n : Nat) : StateM StdGen (Array String) :=
  (Array.range n).filterMapM fun _ => cfg.genInstr.run

def FuzzConfig.assemblable (cfg : FuzzConfig MachineData StatusFlags StateSummary) (cands : Array String) : IO (Array String) :=
  filterAssemblable cfg.runAssembler cands

/-- Four random register initializations (`genSeed`) followed by `length` instructions from `pool`,
each drawn until `stepDeterministic` accepts one. A final `defineAllFlagsInstr` makes all flags defined. -/
def FuzzConfig.genSequence (cfg : FuzzConfig MachineData StatusFlags StateSummary)
    (pool : Array String) (length : Nat) : StateM StdGen String := do
  let mut (d, undef, lines) := (cfg.initData, UndefFlags.none, #[])
  for i in [0 : 4 + length] do
    for _ in [0 : 200] do
      let some cand ← (if i < 4 then cfg.genSeed else pick pool).run | continue
      if let some (d', undef') := cfg.stepDeterministic d undef cand then
        (d, undef, lines) := (d', undef', lines.push cand)
        break
  if undef != .none then lines := lines.push cfg.defineAllFlagsInstr
  return "\n".intercalate lines.toList

/-- Handles `--generate <seed> <count> <length>` and `--batch` CLI invocations, returning `none`
when `args` is a normal single-file runner invocation. -/
def FuzzConfig.handleCli? (cfg : FuzzConfig MachineData StatusFlags StateSummary)
    (args : List String) : IO (Option UInt32) := do
  match args with
  | ["--generate", seed, count, length] =>
    let (pool, g) := (cfg.genPool 5000).run (mkStdGen seed.toNat!)
    let pool ← cfg.assemblable pool
    let gen := (List.range count.toNat!).mapM fun _ => cfg.genSequence pool length.toNat!
    IO.println (toJson (gen.run' g).run).compress
    return some 0
  | ["--batch"] =>
    let raw ← (← IO.getStdin).readToEnd
    let seqs ← IO.ofExcept (Json.parse raw >>= fromJson? (α := Array String))
    IO.println (toJson (seqs.map cfg.predict)).compress
    return some 0
  | _ => return none

end Kraken.Fuzzer
