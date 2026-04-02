/-
Kraken TestHarness - Compare Kraken semantics with real x86 execution

This module provides a test harness that:
1. Takes raw assembly code (AT&T syntax) as input
2. Parses it through Kraken and runs the semantics
3. Appends a capture epilogue to read final state
4. Compares the final machine states (registers, flags, and memory)

The input assembly should set up its own initial state - the harness only
adds the epilogue to capture and output final state.

Compatible with Lean 4.22.0+.
-/

import Kraken.Semantics
import Kraken.Parser

namespace Kraken.TestHarness

-- ============================================================================
-- Memory Region Definition
-- ============================================================================

/-- A memory region to track during test execution.
    base must be 8-byte aligned; size is number of 8-byte words. -/
structure MemRegion where
  base : UInt64   -- Starting address (must be 8-byte aligned)
  size : Nat      -- Number of 8-byte words to track
  deriving Repr, BEq

-- ============================================================================
-- Capture Epilogue Generation
-- ============================================================================

/-- Generate .data section for storing final register state. -/
def genCaptureDataRegs : String :=
  ".data\n" ++
  ".align 8\n" ++
  "# Final register state (filled by capture epilogue)\n" ++
  "_kraken_final_rax: .quad 0\n" ++
  "_kraken_final_rbx: .quad 0\n" ++
  "_kraken_final_rcx: .quad 0\n" ++
  "_kraken_final_rdx: .quad 0\n" ++
  "_kraken_final_rsi: .quad 0\n" ++
  "_kraken_final_rdi: .quad 0\n" ++
  "_kraken_final_rsp: .quad 0\n" ++
  "_kraken_final_rbp: .quad 0\n" ++
  "_kraken_final_r8: .quad 0\n" ++
  "_kraken_final_r9: .quad 0\n" ++
  "_kraken_final_r10: .quad 0\n" ++
  "_kraken_final_r11: .quad 0\n" ++
  "_kraken_final_r12: .quad 0\n" ++
  "_kraken_final_r13: .quad 0\n" ++
  "_kraken_final_r14: .quad 0\n" ++
  "_kraken_final_r15: .quad 0\n" ++
  "_kraken_final_flags: .quad 0\n"

/-- Generate .data section for memory region tracking. -/
def genCaptureDataMem (regions : List MemRegion) : String :=
  if regions.isEmpty then ""
  else
    let regionData := regions.mapIdx fun i r =>
      s!"# Memory region {i}: base={r.base}, size={r.size} words\n" ++
      s!"_kraken_mem_region_{i}_base: .quad {r.base.toNat}\n" ++
      s!"_kraken_mem_region_{i}_size: .quad {r.size}\n" ++
      s!"_kraken_mem_region_{i}_data: .space {r.size * 8}\n"
    "\n# Memory regions to track\n" ++
    s!"_kraken_mem_region_count: .quad {regions.length}\n" ++
    String.intercalate "\n" regionData

/-- Generate full .data section for capture (registers + optional memory). -/
def genCaptureData (memRegions : List MemRegion := []) : String :=
  genCaptureDataRegs ++ genCaptureDataMem memRegions

/-- Generate assembly to save registers to .data section. -/
def genSaveRegisters : String :=
  "    # Save all registers to .data section\n" ++
  "    movq %rax, _kraken_final_rax(%rip)\n" ++
  "    movq %rbx, _kraken_final_rbx(%rip)\n" ++
  "    movq %rcx, _kraken_final_rcx(%rip)\n" ++
  "    movq %rdx, _kraken_final_rdx(%rip)\n" ++
  "    movq %rsi, _kraken_final_rsi(%rip)\n" ++
  "    movq %rdi, _kraken_final_rdi(%rip)\n" ++
  "    movq %rsp, _kraken_final_rsp(%rip)\n" ++
  "    movq %rbp, _kraken_final_rbp(%rip)\n" ++
  "    movq %r8,  _kraken_final_r8(%rip)\n" ++
  "    movq %r9,  _kraken_final_r9(%rip)\n" ++
  "    movq %r10, _kraken_final_r10(%rip)\n" ++
  "    movq %r11, _kraken_final_r11(%rip)\n" ++
  "    movq %r12, _kraken_final_r12(%rip)\n" ++
  "    movq %r13, _kraken_final_r13(%rip)\n" ++
  "    movq %r14, _kraken_final_r14(%rip)\n" ++
  "    movq %r15, _kraken_final_r15(%rip)\n" ++
  "    # Save flags\n" ++
  "    pushfq\n" ++
  "    popq %rax\n" ++
  "    movq %rax, _kraken_final_flags(%rip)\n"

/-- Generate assembly to copy memory regions to dump buffers. -/
def genCopyMemoryRegions (regions : List MemRegion) : String :=
  if regions.isEmpty then ""
  else
    let copies := regions.mapIdx fun i r =>
      s!"    # Copy memory region {i}\n" ++
      s!"    movq _kraken_mem_region_{i}_base(%rip), %rsi  # source = base\n" ++
      s!"    leaq _kraken_mem_region_{i}_data(%rip), %rdi  # dest = buffer\n" ++
      s!"    movq ${r.size}, %rcx                  # count = size words\n" ++
      s!"    rep movsq                             # copy\n"
    "\n    # Copy memory regions to dump buffers\n" ++
    String.intercalate "\n" copies

/-- Calculate total output size: registers (136) + memory regions. -/
def calcOutputSize (regions : List MemRegion) : Nat :=
  136 + -- 16 regs + 1 flags = 17 * 8 = 136 bytes
  (if regions.isEmpty then 0
   else 8 + -- mem_region_count
        regions.foldl (fun acc r => acc + 8 + 8 + r.size * 8) 0) -- base + size + data per region

/-- Generate assembly to write output to stdout and exit. -/
def genWriteAndExit (regions : List MemRegion) : String :=
  let regBytes := 136
  let memHeaderSize := if regions.isEmpty then 0 else 8 -- _kraken_mem_region_count
  let memDataSize := regions.foldl (fun acc r => acc + 16 + r.size * 8) 0 -- base + size + data per region
  let totalBytes := regBytes + memHeaderSize + memDataSize

  -- Write registers first
  "    # Write register state to stdout (136 bytes)\n" ++
  "    movq $1, %rax         # sys_write\n" ++
  "    movq $1, %rdi         # stdout\n" ++
  "    leaq _kraken_final_rax(%rip), %rsi  # buffer start\n" ++
  "    movq $136, %rdx       # 17 quads = 136 bytes\n" ++
  "    syscall\n" ++
  (if regions.isEmpty then ""
   else
    "\n    # Write memory region data to stdout\n" ++
    "    movq $1, %rax\n" ++
    "    movq $1, %rdi\n" ++
    "    leaq _kraken_mem_region_count(%rip), %rsi\n" ++
    s!"    movq ${memHeaderSize + memDataSize}, %rdx\n" ++
    "    syscall\n") ++
  "\n    # Exit with code 0\n" ++
  "    movq $60, %rax\n" ++
  "    xorq %rdi, %rdi\n" ++
  "    syscall\n"

/-- Generate the full capture epilogue with optional memory tracking. -/
def genCaptureEpilogue (memRegions : List MemRegion := []) : String :=
  "\n" ++
  "# ====== KRAKEN CAPTURE EPILOGUE ======\n" ++
  "_kraken_capture:\n" ++
  genSaveRegisters ++
  genCopyMemoryRegions memRegions ++
  "\n" ++
  genWriteAndExit memRegions

-- ============================================================================
-- Assembly Modification
-- ============================================================================

/-- Wrap user's assembly code with capture infrastructure.

    The user's code should be a complete program (with .text, .globl _start, etc.)
    that ends by jumping/falling through to _kraken_capture.

    Optional: specify memory regions to track. -/
def wrapAssembly (userAsm : String) (memRegions : List MemRegion := []) : String :=
  genCaptureData memRegions ++ "\n" ++ userAsm ++ genCaptureEpilogue memRegions

/-- Generate a minimal test program from just the instructions to test.
    Creates a complete program with _start that runs the instructions
    and then captures state.

    Example: makeTestProgram "addq $1, %rax" -/
def makeTestProgram (instructions : String) (memRegions : List MemRegion := []) : String :=
  genCaptureData memRegions ++ "\n" ++
  ".text\n" ++
  ".globl _start\n" ++
  "_start:\n" ++
  instructions ++ "\n" ++
  genCaptureEpilogue memRegions

-- ============================================================================
-- Result Parsing
-- ============================================================================

/-- Extract a 64-bit value from binary data at given offset (little-endian). -/
def extractUInt64 (data : ByteArray) (offset : Nat) : UInt64 :=
  if offset + 7 >= data.size then 0
  else
    -- TODO: foldl?
    let b0 := data.get! offset
    let b1 := data.get! (offset + 1)
    let b2 := data.get! (offset + 2)
    let b3 := data.get! (offset + 3)
    let b4 := data.get! (offset + 4)
    let b5 := data.get! (offset + 5)
    let b6 := data.get! (offset + 6)
    let b7 := data.get! (offset + 7)
    b0.toUInt64 + (b1.toUInt64 <<< 8) + (b2.toUInt64 <<< 16) + (b3.toUInt64 <<< 24) +
    (b4.toUInt64 <<< 32) + (b5.toUInt64 <<< 40) + (b6.toUInt64 <<< 48) + (b7.toUInt64 <<< 56)

/-- Parse final register/flag state from binary output (first 136 bytes). -/
def parseRegisterState (data : ByteArray) : Option (Reg64s × StatusFlags) :=
  if data.size < 136 then none
  else
    let regs : Reg64s := {
      rax := extractUInt64 data 0,
      rbx := extractUInt64 data 8,
      rcx := extractUInt64 data 16,
      rdx := extractUInt64 data 24,
      rsi := extractUInt64 data 32,
      rdi := extractUInt64 data 40,
      rsp := extractUInt64 data 48,
      rbp := extractUInt64 data 56,
      r8  := extractUInt64 data 64,
      r9  := extractUInt64 data 72,
      r10 := extractUInt64 data 80,
      r11 := extractUInt64 data 88,
      r12 := extractUInt64 data 96,
      r13 := extractUInt64 data 104,
      r14 := extractUInt64 data 112,
      r15 := extractUInt64 data 120
    }
    let flagsVal := extractUInt64 data 128
    let flags : StatusFlags := {
      -- https://en.wikipedia.org/wiki/FLAGS_register
      cf := (flagsVal &&& 0x01) != 0,
      pf := (flagsVal &&& 0x04) != 0,
      af := (flagsVal &&& 0x10) != 0,
      zf := (flagsVal &&& 0x40) != 0,
      sf := (flagsVal &&& 0x80) != 0,
      of := (flagsVal &&& 0x800) != 0,
    }
    some (regs, flags)

/-- Parse memory region data from binary output (after register state).
    Returns list of (base, values) pairs. -/
def parseMemoryRegions (data : ByteArray) : List (UInt64 × Array UInt64) :=
  if data.size <= 136 then []
  else
    let regionCount := extractUInt64 data 136
    parseRegionsAux data 144 regionCount.toNat []
where
  parseRegionsAux (data : ByteArray) (offset : Nat) (remaining : Nat)
      (acc : List (UInt64 × Array UInt64)) : List (UInt64 × Array UInt64) :=
    match remaining with
    | 0 => acc
    | n + 1 =>
      if offset + 16 > data.size then acc
      else
        let base := extractUInt64 data offset
        let size := extractUInt64 data (offset + 8)
        let valuesOffset := offset + 16
        let values := Array.range size.toNat |>.map fun i =>
          if valuesOffset + i * 8 + 8 > data.size then 0
          else extractUInt64 data (valuesOffset + i * 8)
        let newOffset := valuesOffset + size.toNat * 8
        parseRegionsAux data newOffset n (acc ++ [(base, values)])

-- ============================================================================
-- State Comparison
-- ============================================================================

/-- Compare two register states, returning list of differences.
    Skips rsp since Kraken initializes it to 0 but real execution has a stack. -/
def compareRegisters (expected actual : Reg64s) : List String :=
  let checks := [
    ("rax", expected.rax, actual.rax), ("rbx", expected.rbx, actual.rbx),
    ("rcx", expected.rcx, actual.rcx), ("rdx", expected.rdx, actual.rdx),
    ("rsi", expected.rsi, actual.rsi), ("rdi", expected.rdi, actual.rdi),
    -- Skip rsp: Kraken initializes to 0, real execution has stack pointer
    -- ("rsp", expected.rsp, actual.rsp),
    ("rbp", expected.rbp, actual.rbp),
    ("r8",  expected.r8,  actual.r8),  ("r9",  expected.r9,  actual.r9),
    ("r10", expected.r10, actual.r10), ("r11", expected.r11, actual.r11),
    ("r12", expected.r12, actual.r12), ("r13", expected.r13, actual.r13),
    ("r14", expected.r14, actual.r14), ("r15", expected.r15, actual.r15)
  ]
  checks.filterMap fun (name, exp, act) =>
    if exp != act then some s!"{name}: expected {exp}, got {act}"
    else none

/-- Compare two flag states, returning list of differences. -/
def compareFlags (expected actual : StatusFlags) : List String :=
  let checks := [
    ("CF", expected.cf, actual.cf),
    ("PF", expected.zf, actual.pf),
    ("AF", expected.zf, actual.af),
    ("ZF", expected.zf, actual.zf),
    ("SF", expected.zf, actual.sf),
    ("OF", expected.of, actual.of)
  ]
  checks.filterMap fun (name, exp, act) =>
    if exp != act then some s!"{name}: expected {exp}, got {act}"
    else none

/-- Extract memory values from Kraken's sparse heap for comparison. -/
def extractKrakenMemory (heap : DataMem) (regions : List MemRegion)
    : List (UInt64 × Array UInt64) :=
  regions.map fun r =>
    let values := Array.range r.size |>.map fun i =>
      match heap[(r.base + i.toUInt64 * 8)]? with
      | some v => v
      | none => 0  -- Uninitialized = 0
    (r.base, values)

/-- Compare memory regions, returning list of differences. -/
def compareMemory (expected actual : List (UInt64 × Array UInt64)) : List String :=
  let pairs := expected.zip actual
  pairs.foldl (fun acc ((expBase, expVals), (actBase, actVals)) =>
    if expBase != actBase then
      -- TODO: computational complexity?
      acc ++ [s!"memory base mismatch: expected {expBase}, got {actBase}"]
    else
      let valDiffs := (List.zip expVals.toList actVals.toList).mapIdx fun i (e, a) =>
        if e != a then some s!"mem[{expBase}+{i*8}]: expected {e}, got {a}"
        else none
      let valDiffs := valDiffs.filterMap id
      acc ++ valDiffs
  ) []

-- ============================================================================
-- Kraken Execution
-- ============================================================================

abbrev MachineState := MachineData × Int64

def startGadget: String := "
__start:
"

-- A gadget for testcases that fall-through the end: does nothing at run-time
-- but allows stopping execution when it hits the __end label.
def endGadget: String := "
  jmp __end
__end:
  nop
"

def finishCriterion (p: Program) (s: MachineState): Bool :=
  let end_idx := defaultLayout p ("__end", 0)
  let current_idx := s.2
  current_idx = end_idx

/-- Run assembly through Kraken's semantics.
    Returns the final machine state after execution. -/
def runKraken (asmCode : String) 
    : Except String MachineState := do
  let prog ← Parser.parse (startGadget ++ asmCode ++ endGadget)
  let initState: MachineState := ({}, defaultLayout prog ("__start", 0))
  eval prog initState (finishCriterion prog)

def test1 := "
__start:
start:
start1:
  movq $0, %rax
loop:
  addq $1, %rax
  cmpq $10, %rax
  jne loop
  jmp end
end:
  nop
"

#eval Parser.parse test1

#eval match (Parser.parse test1) with
  | .ok test1 =>
    -- defaultLayout test1 ("loop", 3)
    let : Layout := { layout := defaultLayout test1 }
    ConstExpr.interp (.sub (.Label "end") .after_current_instruction) (.mk 0 0)
  | .error _ => -1

#eval runKraken test1

-- ============================================================================
-- Test Result Type
-- ============================================================================

inductive TestResult
  | success : TestResult
  | mismatch : List String → TestResult  -- List of differences
  | krakenError : String → TestResult
  | execError : String → TestResult
  deriving Repr

/-- Compare Kraken's expected final state with actual execution result (registers only). -/
def compareStates (krakenState : MachineState) (actualRegs : Reg64s) (actualFlags : StatusFlags)
    : TestResult :=
  let regDiffs := compareRegisters krakenState.1.regs actualRegs
  let flagDiffs := compareFlags krakenState.1.status actualFlags
  let allDiffs := regDiffs ++ flagDiffs
  if allDiffs.isEmpty then .success
  else .mismatch allDiffs

/-- Compare Kraken's expected final state with actual execution (including memory). -/
def compareStatesWithMem (krakenState : MachineState)
    (actualRegs : Reg64s) (actualFlags : StatusFlags)
    (actualMem : List (UInt64 × Array UInt64))
    (memRegions : List MemRegion)
    : TestResult :=
  let regDiffs := compareRegisters krakenState.1.regs actualRegs
  let flagDiffs := compareFlags krakenState.1.status actualFlags
  let expectedMem := extractKrakenMemory krakenState.1.dmem memRegions
  let memDiffs := compareMemory expectedMem actualMem
  let allDiffs := regDiffs ++ flagDiffs ++ memDiffs
  if allDiffs.isEmpty then .success
  else .mismatch allDiffs

-- ============================================================================
-- High-Level Test API
-- ============================================================================

/-- Extract testable instructions from assembly code.
    Looks for code between _start: and jmp _kraken_capture,
    filtering out directives and comments. -/
def extractTestableCode (asmCode : String) : String :=
  let lines := asmCode.splitOn "\n"
  let inTest := lines.foldl (fun (acc, inBlock) line =>
    let trimmed := line.trim
    if trimmed.startsWith "_start:" then (acc, true)
    else if inBlock && trimmed.startsWith "jmp" && trimmed.endsWith "_kraken_capture" then
      (acc, false)
    else if inBlock then
      -- Skip directives, empty lines, and comment-only lines
      let isDirective := trimmed.startsWith "." || trimmed.isEmpty || trimmed.startsWith "#"
      if isDirective then (acc, inBlock)
      else (acc ++ [line], inBlock)
    else (acc, inBlock)
  ) ([], false)
  String.intercalate "\n" inTest.1

/-- Run a complete test: parse AS output, run Kraken eval, compare results.

    Arguments:
    - asmCode: Full assembly code (will extract testable portion)
    - asOutput: Binary output from running AS (136+ bytes)

    Returns TestResult indicating pass/fail with details. -/
def runTest (asmCode : String) (asOutput : ByteArray) : TestResult :=
  -- Parse AS output
  match parseRegisterState asOutput with
  | none => .execError "Failed to parse AS output (need 136 bytes)"
  | some (actualRegs, actualFlags) =>
    -- Extract testable code
    let testCode := extractTestableCode asmCode
    if testCode.isEmpty then
      -- If no markers found, try using the whole file
      match runKraken asmCode with
      | .error e => .krakenError e
      | .ok krakenState => compareStates krakenState actualRegs actualFlags
    else
      -- Run extracted code through Kraken
      match runKraken testCode with
      | .error e => .krakenError s!"Error running extracted code: {e}"
      | .ok krakenState => compareStates krakenState actualRegs actualFlags

/-- Format a TestResult for display. -/
def TestResult.toString : TestResult → String
  | .success => "PASS"
  | .mismatch diffs => "FAIL:\n" ++ String.intercalate "\n  " ("" :: diffs)
  | .krakenError e => s!"KRAKEN ERROR: {e}"
  | .execError e => s!"EXEC ERROR: {e}"

end Kraken.TestHarness

-- ============================================================================
-- Example Usage
-- ============================================================================

/-
WORKFLOW FOR MEMORY TESTING:

1. Define memory regions to track:

   def myRegions : List MemRegion := [
     { base := 0x600000, size := 8 },  -- Track 8 words starting at 0x600000
     { base := 0x601000, size := 4 }   -- Track 4 words starting at 0x601000
   ]

2. Generate test program with memory tracking:

   let prog := Kraken.TestHarness.makeTestProgram
     "movq $42, 0x600000\nmovq $99, 0x600008" myRegions

3. Run and capture output:

   $ as -o test.o test.S && ld -o test test.o && ./test > output.bin

4. Parse output and compare:

   let (regs, flags) := parseRegisterState outputBytes
   let memData := parseMemoryRegions outputBytes
   let result := compareStatesWithMem krakenState regs flags memData myRegions
-/
