module

/-
KrakenRunnerX64 - Run assembly instructions through Kraken Semantics and obtain results as json.

At this point this expects a file only containing a list of assembly instructions, no data block or similar.

Usage: krakenrunner_x64 <assembly.S>
       krakenrunner_x64 --generate <seed> <count> <length>  (random sequences that Kraken deems deterministic)
       krakenrunner_x64 --batch < sequences.json              (predict final states for a JSON array of sequences;
                                                               they must not depend on rsp's value)

Arguments:
- assembly.S: Assembly source file

Output:
- Json formatted Machine state of Kraken after running the assembly.
  See StateSummary for format.
-/

import Kraken.Mem
import Kraken.X64.Parser
import Kraken.X64.Semantics
import Lean.Data.Json

open Lean

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
             ("rsi", r.rsi), ("rdi", r.rdi), ("rbp", r.rbp), ("r8", r.r8),
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

def _start: String := "_start"
def _end: String := "_end"

-- Give the program a stack of 800B initially, mapped at a plausible place.
def stackSize := 800
-- Place the stack somewhere high in memory, aligned to 256 bytes. This will
-- help us avoid disagreements with the actual machine: we will avoid over/underflow
-- when we allocate stack memory using arithmetic instructions (which would happen
-- if the stack were at 0), and fixing the last byte of the address at 0 means that
-- we will match PF for these operations (providing that we also align rsp on
-- hardware).
def stackLocation: UInt64 := 0x7ffecafee200
def initStack : DataMem := (List.replicate stackSize 0xff).At (stackLocation - stackSize)
def initData : MachineData := {regs := {rsp := stackLocation}, dmem := initStack}

def finishCriterion (p: Program) (s: MachineState): Bool :=
  s.2 = p.fakeLayout.labels.label _end

def runKraken (asmCode : String)
    : Except String MachineState := do
  let prog ← Kraken.X64.Parser.parse (_start ++ ":" ++ asmCode ++ "\n" ++ _end ++ ":")
  let initState: MachineState := (initData, prog.fakeLayout.labels.label _start)
  prog.fakeLayout.eval initState (finishCriterion prog)

/-! ## Determinism checking, with Semantics.lean in the loop

We track which of the six status flags are currently undefined as a bitmask using the
bit layout of `NondetSupportingType.from_hash` (cf, pf, af, zf, sf, of = bits 0..5). -/

def StatusFlags.toMask (f : StatusFlags) : Nat :=
  f.cf.toNat ||| f.pf.toNat <<< 1 ||| f.af.toNat <<< 2 ||| f.zf.toNat <<< 3 ||| f.sf.toNat <<< 4 ||| f.of.toNat <<< 5

-- Runs `Effects` to completion, resolving every `undefined` choice with `h`. Also returns
-- whether any `undefined` choice was made.
partial def evalEffects (h : UInt64) (sawUndef : Bool) : Effects → Option (MachineData × Bool)
  | .done (s, _) => some (s, sawUndef)
  | .require_read_access _ _ ok | .require_write_access _ _ ok | .require_exec_access _ ok => evalEffects h sawUndef (ok ())
  | @Effects.undefined _ t cont => evalEffects h true (cont (t.from_hash h))
  | _ => none

/-- Executes `asmCode` (straight-line, no jumps) from `d`, where `mask` are the flags currently
undefined. Each instruction is run under every assignment of the undefined flags, and (if it makes
`undefined` choices) with those resolved to all-zeros and to all-ones. Fails unless registers and
memory agree across all runs; returns the resulting state and the new mask of flags that disagree.

The two-sample resolution of `undefined` is sound because Semantics.lean only ever stores an
undefined choice directly into a flag, all flags, or a register, never computes with it. -/
def stepDeterministic (d : MachineData) (mask : Nat) (asmCode : String) : Option (MachineData × Nat) := do
  let exe := (← (Kraken.X64.Parser.parse asmCode).toOption).fakeLayout
  let := exe.labels
  let mut (d, mask) := (d, mask)
  for (pc, dir, sz) in exe.withAddresses do
    let p : Std.Rco Int64 := .mk pc (pc + .ofNat sz)
    let fixed := d.status.toMask &&& (63 ^^^ mask)
    let run (m : Nat) (h : UInt64) : Option (MachineData × Bool) :=
      let status : StatusFlags := NondetSupportingType.from_hash (fixed ||| m).toUInt64
      evalEffects h false (dir.interp { d with status } p (fun s => .done (s, p.upper)) (fun _ _ => .unimplemented "jump"))
    let mut outs : Array MachineData := #[]
    for m in (List.range 64).filter (fun m => m &&& mask == m) do
      let (s, sawUndef) ← run m 0
      outs := outs.push s
      if sawUndef then outs := outs.push (← run m (-1)).1
    let s0 ← outs[0]?
    if outs.any ({ · with status := s0.status } != s0) then failure
    (d, mask) := (s0, outs.foldl (fun acc s => acc ||| (s.status.toMask ^^^ s0.status.toMask)) 0)
  if d.regs.rsp != stackLocation then failure
  return (d, mask)

def predict (asmCode : String) : Json :=
  match stepDeterministic initData 0 asmCode with
  | some (s, 0) => Json.mkObj [("ok", toJson true), ("state", toJson (summarize s))]
  | _ => Json.mkObj [("ok", toJson false), ("error", toJson "unparseable, faulting, jumping, or non-deterministic")]

/-! ## Random instruction sequence generation -/

abbrev GenM := StateM StdGen
def nextNat (n : Nat) : GenM Nat := modifyGet (randNat · 0 (n - 1))
def pick {α : Type} [Inhabited α] (xs : Array α) : GenM α := do return xs[← nextNat xs.size]!

def regsQ := #["rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]
def regsByWidth : String → Array String
  | "b" => #["al", "bl", "cl", "dl", "sil", "dil", "bpl", "r8b", "r9b", "r10b", "r11b", "r12b", "r13b", "r14b", "r15b"]
  | "w" => #["ax", "bx", "cx", "dx", "si", "di", "bp", "r8w", "r9w", "r10w", "r11w", "r12w", "r13w", "r14w", "r15w"]
  | "l" => #["eax", "ebx", "ecx", "edx", "esi", "edi", "ebp", "r8d", "r9d", "r10d", "r11d", "r12d", "r13d", "r14d", "r15d"]
  | _ => regsQ

def randImm (w : String) : GenM Int := do
  let bits := if w == "b" then 8 else if w == "w" then 16 else 32
  let interesting := #[0, 1, -1, 2, -2, 7, 8, 15, 16, 31, 32, 63, 64, 127, -128, 255, 32767, -32768,
    65535, 2147483647, -2147483648, 0x55555555].filter fun (i : Int) => -2 ^ (bits - 1) ≤ i && i < 2 ^ bits
  if (← nextNat 10) < 7 then pick interesting else return (← nextNat (2 ^ bits)) - 2 ^ (bits - 1)

def genMovabs : GenM String := do return s!"movabsq ${← nextNat (2 ^ 64)}, %{← pick regsQ}"

def genCandidate : GenM String := do
  let cat ← nextNat 100
  let w ← pick #["b", "w", "l", "q"]
  let dst ← pick (regsByWidth w)
  let src ← pick (regsByWidth w)
  if cat < 24 then
    let op ← pick #["add", "sub", "adc", "sbb", "and", "or", "xor", "cmp", "test"]
    if (← nextNat 10) < 4 then return s!"{op}{w} ${← randImm w}, %{dst}"
    else return s!"{op}{w} %{src}, %{dst}"
  else if cat < 32 then
    return s!"{← pick #["inc", "dec", "neg", "not"]}{w} %{dst}"
  else if cat < 42 then
    if w == "q" && (← nextNat 2) == 0 then genMovabs
    else return s!"mov{w} ${← randImm w}, %{dst}"
  else if cat < 50 then
    let (ws, wd) ← pick #[("b", "w"), ("b", "l"), ("b", "q"), ("w", "l"), ("w", "q")]
    return s!"{← pick #["movs", "movz"]}{ws}{wd} %{← pick (regsByWidth ws)}, %{← pick (regsByWidth wd)}"
  else if cat < 58 then
    let cc ← pick #["z", "nz", "b", "ae", "a", "be", "l", "le"]
    if (← nextNat 2) == 0 then return s!"set{cc} %{← pick (regsByWidth "b")}"
    else
      let wc ← pick #["w", "l", "q"]
      return s!"cmov{cc} %{← pick (regsByWidth wc)}, %{← pick (regsByWidth wc)}"
  else if cat < 72 then
    let op ← pick #["shl", "shr", "sar", "rol", "ror"]
    match ← nextNat 3 with
    | 0 => return s!"{op}{w} %{dst}"
    | 1 => return s!"{op}{w} %cl, %{dst}"
    | _ => return s!"{op}{w} ${← pick #[1, 2, 3, 4, 7, 8, 15, 16, 31]}, %{dst}"
  else if cat < 76 then
    let ws ← pick #["w", "l", "q"]
    let cnt ← pick (if ws == "w" then #[1, 2, 7, 15] else #[1, 2, 7, 15, 31])
    return s!"{← pick #["shld", "shrd"]}{ws} ${cnt}, %{← pick (regsByWidth ws)}, %{← pick (regsByWidth ws)}"
  else if cat < 82 then
    match w, ← nextNat 4 with
    | _, 0 => return s!"mul{w} %{src}"
    | "b", _ | _, 1 => return s!"imul{w} %{src}"
    | _, 2 => return s!"imul{w} %{src}, %{dst}"
    | _, _ => return s!"imul{w} ${← randImm w}, %{src}, %{dst}"
  else if cat < 86 then
    let wm ← pick #["l", "q"]
    let (r1, r2, r3) := (← pick (regsByWidth wm), ← pick (regsByWidth wm), ← pick (regsByWidth wm))
    if (← nextNat 3) == 0 then return s!"mulx{wm} %{r1}, %{r2}, %{r3}"
    else return s!"{← pick #["adcx", "adox"]}{wm} %{r1}, %{r2}"
  else if cat < 90 then
    let wl ← pick #["w", "l", "q"]
    let idx ← if (← nextNat 2) == 0 then pure "" else pure s!", %{← pick regsQ}, {← pick #[1, 2, 4, 8]}"
    return s!"lea{wl} {(← nextNat 256 : Int) - 128}(%{← pick regsQ}{idx}), %{← pick (regsByWidth wl)}"
  else if cat < 92 then
    let wb ← pick #["l", "q"]
    return s!"bswap{wb} %{← pick (regsByWidth wb)}"
  else if cat < 96 then
    -- Stay within Kraken's stack mapping [rsp - 800, rsp).
    let mem := s!"{-512 + 8 * (← nextNat 56 : Int)}(%rsp)"
    match ← nextNat 3 with
    | 0 => return s!"mov{w} %{dst}, {mem}"
    | 1 => return s!"mov{w} {mem}, %{dst}"
    | _ => return s!"{← pick #["add", "sub", "xor", "and", "or"]}{w} %{dst}, {mem}"
  else if cat < 98 then
    return s!"pushq %{← pick regsQ}\n    popq %{← pick regsQ}"
  else
    -- Store two finite floats to an aligned stack slot, then load/compute with them.
    let disp := -512 + 32 * (← nextNat 14 : Int)
    let rTmp ← pick regsQ
    let fBits : Array Nat := #[0x00000000, 0x80000000, 0x3F800000, 0xBF800000, 0x40000000, 0x40400000, 0x3F000000, 0x42280000]
    let (i1, i2) := (← nextNat 16, ← nextNat 16)
    let setup := s!"movabsq ${(← pick fBits) <<< 32 ||| (← pick fBits)}, %{rTmp}\n    movq %{rTmp}, {disp}(%rsp)\n    movq %{rTmp}, {disp + 8}(%rsp)"
    match ← nextNat 5 with
    | 0 => return s!"{setup}\n    movups {disp}(%rsp), %xmm{i1}"
    | 1 => return s!"{setup}\n    vmovups {disp}(%rsp), %xmm{i1}"
    | 2 => return s!"{setup}\n    movq %{rTmp}, {disp + 16}(%rsp)\n    movq %{rTmp}, {disp + 24}(%rsp)\n    vmovups {disp}(%rsp), %ymm{i1}"
    | 3 => return s!"{setup}\n    movaps {disp}(%rsp), %xmm{i1}\n    addps %xmm{i1}, %xmm{i2}"
    | _ => return s!"{setup}\n    movaps {disp}(%rsp), %xmm{i1}\n    subps %xmm{i1}, %xmm{i2}"

-- Four random register initializations followed by `length` instructions, each drawn until
-- `stepDeterministic` accepts one. A final `add` makes all flags defined.
def genSequence (length : Nat) : GenM String := do
  let mut (d, mask, lines) := (initData, 0, #[])
  for i in [0 : 4 + length] do
    for _ in [0 : 200] do
      let cand ← if i < 4 then genMovabs else genCandidate
      if let some (d', mask') := stepDeterministic d mask cand then
        (d, mask, lines) := (d', mask', lines.push cand)
        break
  if mask != 0 then lines := lines.push "addq %rax, %rax"
  return "\n".intercalate lines.toList

public def main (args : List String) : IO UInt32 := do
  match args with
  | ["--generate", seed, count, length] =>
    let gen := (List.range count.toNat!).mapM fun _ => genSequence length.toNat!
    IO.println (toJson (gen.run' (mkStdGen seed.toNat!)).run).compress
    return 0
  | ["--batch"] =>
    let raw ← (← IO.getStdin).readToEnd
    let seqs ← IO.ofExcept (Json.parse raw >>= fromJson? (α := Array String))
    IO.println (toJson (seqs.map predict)).compress
    return 0
  | _ => pure ()

  if args.isEmpty then return 1

  let asmCode ← IO.FS.readFile args[0]!

  match runKraken asmCode with
  | .ok (state, _) =>
      IO.println (toJson (summarize state)).compress
      return 0
  | .error e =>
      IO.eprintln s!"Kraken Semantic Error: {e}"
      return 1
