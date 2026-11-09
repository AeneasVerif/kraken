module

/-
Common infrastructure for Kraken's differential instruction fuzzers:
- Status flag bitmasks (`StatusFlagBits`, `UndefFlags`) and determinism checking (`stepDeterministic`)
- Random instruction and operand generation (`GenM`, `Gen`, `gen_ctors%`, `genInt64`)
- Assembler filtering (`filterAssemblable`), sequence generation (`genSequence`), and CLI (`handleCli?`)
-/

public import Kraken.Layout
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
  /-- Parses `asmCode` into positioned steps where `directive s p h` runs the directive at
  address range `p` from state `s`, resolving `undefined` choices with `h`. -/
  parseSteps : String → Option (List (Addressable (MachineData → Std.Rco Int64 → UInt64 → Option (MachineData × Bool))))
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
  for {addr := pc, directive := step, size := sz} in steps do
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

/-- The mnemonic of an assembly line: its first word. -/
def mnemonic (line : String) : String :=
  (line.trimAscii.toString.takeWhile (!·.isWhitespace)).toString

/-- The assemblable instructions a run draws from, grouped by mnemonic. Sequences pick a mnemonic
uniformly and then one of its forms, so that an instruction with few syntactic forms is run as
often as one with many, and so that one the generator rarely produces is not drowned out.

The unit of fairness is the printed mnemonic, so in AT&T syntax each width (`addb`, `addw`, …) and
each condition code (`seta`, `setb`, …) is its own group; a condition-code instruction thus gets
sixteen shares, a vector instruction one. -/
structure Pool where
  groups : Array (String × Array String)

/-- How many assemblable forms of each mnemonic `buildPool` aims for, so that every mnemonic
is run with a varied set of operands. -/
def poolTarget : Nat := 64

/-- The rounds of generation `buildPool` runs: each draws 5000 random instructions. A focused pool
(`only` set) runs more, since it discards most of each round before the assembler sees it and the
mnemonics of interest may be ones the generator rarely produces. -/
def poolRounds (focused : Bool) : Nat := if focused then 64 else 8

/-- Rounds of random generation and assembler filtering, grouped by mnemonic, stopping early once
every mnemonic seen has `poolTarget` forms. A mnemonic the generator rarely produces ends up with
fewer forms, but is still drawn as often as any other. With `only` set, keeps the mnemonics that
start with one of its entries. -/
def FuzzConfig.buildPool (cfg : FuzzConfig MachineData StatusFlags StateSummary) (g : StdGen)
    (only : Array String := #[]) : IO (Pool × StdGen) := do
  let keep (m : String) := only.isEmpty || only.any (m.startsWith ·)
  let mut forms : Std.HashMap String (Array String) := {}
  let mut g := g
  for _ in [0 : poolRounds !only.isEmpty] do
    let (cands, g') := (cfg.genPool 5000).run g
    g := g'
    for c in ← cfg.assemblable (cands.filter (keep <| mnemonic ·)) do
      let m := mnemonic c
      let seen := forms.getD m #[]
      if seen.size < poolTarget && !seen.contains c then
        forms := forms.insert m (seen.push c)
    if !forms.isEmpty && forms.toArray.all (·.2.size ≥ poolTarget) then break
  return (⟨forms.toArray.qsort (·.1 < ·.1)⟩, g)

/-- The first of `cands` that `stepDeterministic` accepts from `(d, undef)`, with the resulting
state, drawing up to `tries` candidates. -/
def FuzzConfig.firstAccepted (cfg : FuzzConfig MachineData StatusFlags StateSummary)
    (d : MachineData) (undef : UndefFlags) (cands : GenM String) (tries : Nat) :
    StateM StdGen (Option (String × MachineData × UndefFlags)) := do
  for _ in [0 : tries] do
    let some cand ← cands.run | continue
    if let some (d', undef') := cfg.stepDeterministic d undef cand then
      return some (cand, d', undef')
  return none

/-- Four random register initializations (`genSeed`) followed by `length` instructions from `pool`:
a mnemonic drawn uniformly, then its forms drawn until `stepDeterministic` accepts one, so that a
mnemonic most of whose forms fault (say, on a random address) is run no less often than the others.
A final `defineAllFlagsInstr` makes all flags defined. -/
def FuzzConfig.genSequence (cfg : FuzzConfig MachineData StatusFlags StateSummary)
    (pool : Pool) (length : Nat) : StateM StdGen String := do
  let mut (d, undef, lines) := (cfg.initData, UndefFlags.none, #[])
  for _ in [0 : 4] do
    if let some (cand, d', undef') ← cfg.firstAccepted d undef cfg.genSeed 200 then
      (d, undef, lines) := (d', undef', lines.push cand)
  for _ in [0 : length] do
    for _ in [0 : 10] do
      let some (_, forms) ← (pick pool.groups).run | continue
      if let some (cand, d', undef') ← cfg.firstAccepted d undef (pick forms) 20 then
        (d, undef, lines) := (d', undef', lines.push cand)
        break
  if undef != .none then lines := lines.push cfg.defineAllFlagsInstr
  return "\n".intercalate lines.toList

/-- Handles `--generate <seed> <count> <length> [<mnemonic-prefixes>]`, `--mnemonics [<prefixes>]`
and `--batch` CLI invocations, returning `none` when `args` is a normal single-file runner
invocation. The prefixes are comma-separated and restrict the pool to the mnemonics starting with
one of them; `--mnemonics` prints the pool's mnemonics with the number of forms of each. -/
def FuzzConfig.handleCli? (cfg : FuzzConfig MachineData StatusFlags StateSummary)
    (args : List String) : IO (Option UInt32) := do
  let prefixes (s : String) : Array String :=
    (s.splitOn ",").toArray.map (·.trimAscii.toString) |>.filter (· ≠ "")
  match args with
  | "--generate" :: seed :: count :: length :: rest =>
    let only := prefixes (" ".intercalate rest)
    let (pool, g) ← cfg.buildPool (mkStdGen seed.toNat!) only
    if pool.groups.isEmpty then
      IO.eprintln s!"no assemblable instruction has a mnemonic starting with {", ".intercalate only.toList}"
      return some 1
    let gen := (List.range count.toNat!).mapM fun _ => cfg.genSequence pool length.toNat!
    IO.println (toJson (gen.run' g).run).compress
    return some 0
  | "--mnemonics" :: rest =>
    let (pool, _) ← cfg.buildPool (mkStdGen 0) (prefixes (" ".intercalate rest))
    for (m, forms) in pool.groups do
      IO.println s!"{m} {forms.size}"
    return some 0
  | ["--batch"] =>
    let raw ← (← IO.getStdin).readToEnd
    let seqs ← IO.ofExcept (Json.parse raw >>= fromJson? (α := Array String))
    IO.println (toJson (seqs.map cfg.predict)).compress
    return some 0
  | _ => return none

end Kraken.Fuzzer
