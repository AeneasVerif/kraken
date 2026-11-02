module

/-
  Round-trip tests for the AArch64 printer: `parse (print p) = .ok p` for programs
  `p` produced by `parse`.
-/

import Kraken.AArch64.Parser
meta import Kraken.AArch64.Parser
import Kraken.AArch64.Print
meta import Kraken.AArch64.Print

open Kraken.AArch64 Kraken.AArch64.Parser

/-- `s` parses, and printing the result then re-parsing gives the same program. -/
def roundtrips (s : String) : Bool :=
  match parse s with
  | .ok p => match parse (print p) with
    | .ok p' => p' == p
    | .error _ => false
  | .error _ => false

/-- One line per `Operation` constructor and operand form. -/
def corpus : List String := [
  -- loads and stores, all widths and addressing modes
  "ldr x0, [sp]", "ldr w1, [x2, #12]", "ldr x3, [sp, #-16]!", "ldr x4, [x5], #8",
  "ldr x0, [x1, x2, lsl #3]", "ldr x0, [x1, x2, sxtx #0]", "ldr w0, [x1, w2, uxtw #2]",
  "ldr x0, [x1, w2, sxtw #3]", "ldr x0, [x1, #:lo12:sym]", "ldr x0, sym", "ldr x0, =42",
  "str x0, [sp, #16]", "str w1, [x2, #-8]!", "str x3, [x4], #16",
  "ldur x0, [x1, #-8]", "stur w2, [x3, #13]",
  "ldp x0, x1, [sp, #16]", "ldp w2, w3, [x4, #-16]!", "stp x5, x6, [sp], #32",
  "ldrb w0, [x1, #5]", "ldurb w0, [x1, #-5]", "strb w0, [x1, #10]", "sturb w0, [x1, #-10]",
  "ldrsb w0, [x1, #5]", "ldrsb x0, [x1, #5]", "ldursb x0, [x1, #-5]",
  "ldrh w0, [x1, #6]", "ldurh w0, [x1, #-6]", "strh w0, [x1, #8]", "sturh w0, [x1, #-8]",
  "ldrsh w0, [x1, #6]", "ldrsh x0, [x1, #6]", "ldursh x0, [x1, #-6]",
  "ldrsw x0, [x1, #8]", "ldrsw x0, sym", "ldursw x0, [x1, #-8]", "ldpsw x0, x1, [sp, #8]",
  -- arithmetic (extended, immediate, shifted)
  "add x0, x1, #42", "add x0, x1, #42, lsl #12", "add sp, sp, #16", "add x0, x0, :lo12:sym",
  "add x0, x1, w2, uxtw #2", "add sp, x1, x2", "add x0, x1, x2, sxtx #3",
  "add x0, x1, x2", "add x0, x1, x2, lsl #2", "add w0, w1, w2, lsr #3", "add x0, x1, x2, asr #4",
  "adds x0, x1, #42", "adds x0, sp, w2, sxtw #1", "adds x0, x1, x2, lsl #2", "cmn x1, #10",
  "sub x0, x1, #5", "sub sp, sp, w2, uxtb #1", "sub x0, x1, x2, lsr #1",
  "subs x0, x1, #5", "subs x0, sp, w2, sxth #2", "subs x0, x1, x2, asr #3",
  "cmp x1, x2", "neg x0, x1", "negs w0, w1",
  -- carry arithmetic, division, multiply
  "adc x0, x1, x2", "adcs w3, w4, w5", "sbc x6, x7, x8", "sbcs w9, w10, w11",
  "sdiv x0, x1, x2", "udiv w0, w1, w2",
  "madd x0, x1, x2, x3", "msub w0, w1, w2, w3", "mul x0, x1, x2", "mneg w0, w1, w2",
  "smulh x0, x1, x2", "umulh x0, x1, x2",
  "smaddl x0, w1, w2, x3", "umaddl x0, w1, w2, x3", "smsubl x0, w1, w2, x3", "umsubl x0, w1, w2, x3",
  -- logical
  "and x0, x1, #255", "and sp, x1, #15", "and x0, x1, x2, lsr #4",
  "ands w5, w6, #255", "ands x0, x1, x2", "tst x1, #255", "tst x1, x2",
  "orr w2, w3, #255", "orr x0, x1, x2, ror #4", "orn x0, x1, x2",
  "eor sp, x4, #255", "eor x0, x1, x2", "eon x0, x1, x2",
  "bic x0, x1, x2", "bics x0, x1, x2", "mov x0, x1", "mov sp, x0", "mvn x2, x3",
  -- bitfield, bit manipulation, move wide, variable shifts
  "bfm w0, w1, #4, #11", "sbfm x0, x1, #0, #15", "ubfm w0, w1, #4, #11",
  "ubfx w0, w1, #4, #8", "sbfx x0, x1, #0, #16", "bfi w0, w1, #8, #8", "sxtw x0, w1",
  "clz w0, w1", "cls x0, x1", "rbit w0, w1", "rev x0, x1", "rev16 w0, w1", "rev32 x0, x1",
  "extr w0, w1, w2, #8", "lsl x0, x1, #4", "ror w0, w1, #4",
  "movz x0, #1234, lsl #16", "movk w1, #5678, lsl #0", "movn x2, #65535, lsl #48",
  "lslv w0, w1, w2", "lsrv x0, x1, x2", "asrv x0, x1, x2", "rorv x0, x1, x2",
  -- conditional select & compare
  "csel x0, x1, x2, eq", "csinc x0, x1, x2, cs", "csinv x0, x1, x2, mi", "csneg w0, w1, w2, le",
  "ccmp x0, x1, #4, eq", "ccmp x0, #10, #2, ne", "ccmn w0, w1, #0, hs", "ccmn w0, #1, #0, lo",
  -- addressing, control flow, misc
  "adr x0, main", "adr x1, #4096", "adrp x0, main", "adrp x0, :pg_hi21:main",
  "b main", "b #16", "b.eq loop", "b.nv exit", "bl foo", "blr x16", "br x30", "ret", "ret x19",
  "cbz x0, target", "cbnz w1, loop", "tbz x2, #5, label", "tbnz w3, #31, exit",
  "nop", "foo:\nbar: ret\n\nbaz:"
]

/-- info: [] -/
#guard_msgs in
#eval corpus.filter (!roundtrips ·)

-- Printed form is canonical AArch64.
#guard match parse "ldr x0, [sp, #0]\nfoo: cmp x1, x2\nbne foo\nret lr" with
  | .ok p => print p == "ldr x0, [sp]\nfoo:\nsubs xzr, x1, x2\nb.ne foo\nret"
  | .error _ => false

-- Every program in the hardware test corpus round-trips.
#eval show IO Unit from do
  for f in ← System.FilePath.readDir "Kraken/AArch64/Test/asm" do
    if f.path.extension == some "S" then
      unless roundtrips (stripDirectives (← IO.FS.readFile f.path)) do
        throw <| .userError s!"{f.path} does not round-trip"
