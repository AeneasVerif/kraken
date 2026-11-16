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

/-- Which mnemonic to group an instruction under. We special case `rep` prefixes and drop `addr32`.
This means that `rep movsb` is distinct from `movsb`, but `addr32 rep movsb` is not distinct from
`rep movsb`. -/
private def mnemonic (line : String) : String :=
  match (line.splitOn " ").filter (· ≠ "") with
  | "addr32" :: "rep" :: w :: _ | "rep" :: w :: _ => s!"rep {w}"
  | "addr32" :: w :: _ | w :: _ => w
  | [] => ""

#guard mnemonic "addq $1, %rax" == "addq"
#guard mnemonic "movsb" == "movsb"
#guard mnemonic "addr32 movsb" == "movsb"
#guard mnemonic "rep movsb" == "rep movsb"
#guard mnemonic "addr32 rep movsb" == "rep movsb"
#guard mnemonic "ldr x0, [x1, #8]" == "ldr"

private def poolTarget : Nat := 64

/-- Builds a pool of instructions grouped by mnemonic, keeping up to `poolTarget` forms for each
mnemonic. `only` restricts the set of mnemonics in the pool. -/
private def FuzzConfig.buildPool (cfg : FuzzConfig MachineData StatusFlags StateSummary) (g : StdGen)
    (only : Array String := #[]) : IO (Array (String × Array String) × StdGen) := do
  let mut forms : Std.HashMap String (Array String) := {}
  let mut g := g
  for _ in [0 : if only.isEmpty then 8 else 64] do
    let (cands, g') := (cfg.genPool 5000).run g
    g := g'
    let fresh := cands.filter fun c =>
      let m := mnemonic c
      let seen := forms.getD m #[]
      (only.isEmpty || only.any (m.startsWith ·)) && seen.size < poolTarget && !seen.contains c
    if fresh.isEmpty then continue
    for c in ← cfg.assemblable fresh do
      let m := mnemonic c
      let seen := forms.getD m #[]
      if seen.size < poolTarget && !seen.contains c then
        forms := forms.insert m (seen.push c)
  return (forms.toArray.qsort (·.1 < ·.1), g)

/-- The first result of `cands` that `stepDeterministic` accepts, trying `tries` times. -/
private def FuzzConfig.firstAccepted (cfg : FuzzConfig MachineData StatusFlags StateSummary)
    (d : MachineData) (undef : UndefFlags) (cands : GenM String) (tries : Nat) :
    StateM StdGen (Option (String × MachineData × UndefFlags)) := do
  for _ in [0 : tries] do
    let some cand ← cands.run | continue
    if let some (d', undef') := cfg.stepDeterministic d undef cand then
      return some (cand, d', undef')
  return none

/-- Generates a sequence of instructions: first four random initializations from `genSeed`, then up
to `length` instructions from `pool`, and finally `defineAllFlagsInstr` to fix flags (if necessary).
Returns the instruction sequence and the mnemonics of the instructions drawn from the pool.

We attempt (i.e., run up to a bound) to keep an equal distribution of mnemonics by trying
multiple variants until we find one that doesn't take a branch, fault, or depend on nondeterministic
state. -/
def FuzzConfig.genSequence (cfg : FuzzConfig MachineData StatusFlags StateSummary)
    (pool : Array (String × Array String)) (length : Nat) : StateM StdGen (String × Array String) := do
  let mut (d, undef, lines, drawn) := (cfg.initData, UndefFlags.none, #[], (#[] : Array String))
  for _ in [0 : 4] do
    if let some (cand, d', undef') ← cfg.firstAccepted d undef cfg.genSeed 200 then
      (d, undef, lines) := (d', undef', lines.push cand)
  for _ in [0 : length] do
    for _ in [0 : 10] do
      let some (m, forms) ← (pick pool).run | continue
      if let some (cand, d', undef') ← cfg.firstAccepted d undef (pick forms) 20 then
        (d, undef, lines, drawn) := (d', undef', lines.push cand, drawn.push m)
        break
  if undef != .none then lines := lines.push cfg.defineAllFlagsInstr
  return ("\n".intercalate lines.toList, drawn)

/-- `--generate` reads `{"seed": n, "count": n, "length": n, "only": [prefixes]}` from stdin
to produce test sequences. `--batch` reads a JSON string array of instruction sequences from
stdin and runs them. -/
def FuzzConfig.handleCli? (cfg : FuzzConfig MachineData StatusFlags StateSummary)
    (args : List String) : IO (Option UInt32) := do
  match args with
  | ["--generate"] =>
    let req ← IO.ofExcept (Json.parse (← (← IO.getStdin).readToEnd))
    let seed ← IO.ofExcept (req.getObjValAs? Nat "seed")
    let count ← IO.ofExcept (req.getObjValAs? Nat "count")
    let length ← IO.ofExcept (req.getObjValAs? Nat "length")
    let only ← IO.ofExcept (req.getObjValAs? (Array String) "only")
    let (pool, g) ← cfg.buildPool (mkStdGen seed) only
    let gen := (List.range count).mapM fun _ => cfg.genSequence pool length
    let results := (gen.run' g).run
    let runs := (results.toArray.flatMap (·.2)).foldl (init := ({} : Std.HashMap String Nat))
      fun acc m => acc.insert m (acc.getD m 0 + 1)
    IO.println (Json.mkObj [
      ("pool", toJson (pool.map (·.1))),
      ("seqs", toJson (results.map (·.1))),
      ("runs", Json.mkObj (runs.toList.map fun (m, n) => (m, toJson n)))]).compress
    return some 0
  | ["--batch"] =>
    let raw ← (← IO.getStdin).readToEnd
    let seqs ← IO.ofExcept (Json.parse raw >>= fromJson? (α := Array String))
    IO.println (toJson (seqs.map cfg.predict)).compress
    return some 0
  | _ => return none

end Kraken.Fuzzer
