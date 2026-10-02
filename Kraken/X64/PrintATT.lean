module

public import Kraken.X64.PrintIntel

public section
/-!
# AT&T printer
Prints Kraken x64 syntax in the AT&T dialect accepted by `Kraken.X64.Parser.parse`.
The intended property is `parse (toATT p) = .ok p` for every program `p` that `parse`
can produce (see `PrintATTTests.lean`). Values outside the parser's image (e.g. memory
operands without a base register, or `ConstExpr` arithmetic) are still printed, but
won't round-trip.

Mnemonics carry a width suffix whenever the operands may not determine the width
(immediates, memory), and are unsuffixed when a register operand always does.
-/
namespace Kraken.X64.ATT

def suffix : Width → String | .W8 => "b" | .W16 => "w" | .W32 => "l" | .W64 => "q"

def reg {w} (r : Reg w) : String := "%" ++ r.toStr

def avxReg {w} (r : AvxReg w) : String := "%" ++ toString r

def const : ConstExpr → String
  | .label l => l
  | .int64 i => toString i
  | .add a b => s!"{const a}+{const b}"
  | .sub a b => s!"{const a}-{const b}"
  | e => toString e

def addr (aw : Width) (a : AddrExpr) : String :=
  let disp := match a.base, a.disp with
    | some .rip, .sub e .after_current_instruction => const e
    | _, .int64 0 => ""
    | _, d => const d
  let base := match a.base with
    | some (.reg r) => reg (.low r aw)
    | some .rip => "%rip"
    | none => ""
  let idx := match a.idx with
    | some ⟨r, s⟩ => s!",{reg (.low r aw)},{s.bytes}"
    | none => ""
  -- Without registers, the displacement alone is an absolute address.
  if a.base.isNone && a.idx.isNone then const a.disp else s!"{disp}({base}{idx})"

def rm {w} (aw : Width) : RegOrMem w → String
  | .reg r => reg r
  | .mem a => addr aw a

def avxRm {w} (aw : Width) : AvxRegOrMem w → String
  | .avx r => avxReg r
  | .mem a => addr aw a

def operand {w} (aw : Width) : Operand w → String
  | .regOrMem x => rm aw x
  | .imm e => "$" ++ const e

def count : ShiftCountExpr → String
  | .cl => "%cl"
  | .imm8 e => "$" ++ const e

def target (aw : Width) : RelRegOrMem → String
  | .rel (.sub e .after_current_instruction) => const e
  | .rel e => const e
  | .reg r => reg r
  | .mem a => addr aw a

def operation {w} (aw : Width) (op : Operation w) : String :=
  let s := suffix w
  let one (mn a : String) := s!"{mn}{s} {a}"
  let two (mn a b : String) := s!"{mn}{s} {a}, {b}"
  match op with
  | .mov d x => two "mov" (operand aw x) (rm aw d)
  | .movsx d x => s!"movsx {rm aw x}, {rm aw d}"
  | .movzx d x => s!"movzx {rm aw x}, {rm aw d}"
  | .push x => one "push" (operand aw x)
  | .pop d => one "pop" (rm aw d)
  | .setcc cc d => s!"set{cc} {rm aw d}"
  | .cmovcc cc d x => s!"cmov{cc} {rm aw x}, {reg d}"
  | .lea d a => s!"lea {addr aw a}, {reg d}"
  | .add d x => two "add" (operand aw x) (rm aw d)
  | .adc d x => two "adc" (operand aw x) (rm aw d)
  | .adcx d x => s!"adcx {rm aw x}, {reg d}"
  | .adox d x => s!"adox {rm aw x}, {reg d}"
  | .inc d => one "inc" (rm aw d)
  | .dec d => one "dec" (rm aw d)
  | .neg d => one "neg" (rm aw d)
  | .sub d x => two "sub" (operand aw x) (rm aw d)
  | .sbb d x => two "sbb" (operand aw x) (rm aw d)
  | .cmp a b => two "cmp" (operand aw b) (rm aw a)
  | .mul x => one "mul" (rm aw x)
  | .mulx hi lo x => s!"mulx {rm aw x}, {reg lo}, {reg hi}"
  | .imul1 x => one "imul" (rm aw x)
  | .imul none a b => two "imul" (operand aw b) (rm aw a)
  | .imul (some d) a b => s!"imul{s} {operand aw b}, {rm aw a}, {rm aw d}"
  | .test a b => two "test" (operand aw b) (rm aw a)
  | .and d x => two "and" (operand aw x) (rm aw d)
  | .not d => one "not" (rm aw d)
  | .or d x => two "or" (operand aw x) (rm aw d)
  | .xor d x => two "xor" (operand aw x) (rm aw d)
  | .shl d c => two "shl" (count c) (rm aw d)
  | .shr d c => two "shr" (count c) (rm aw d)
  | .sar d c => two "sar" (count c) (rm aw d)
  | .shld d x c => s!"shld {count c}, {reg x}, {rm aw d}"
  | .shrd d x c => s!"shrd {count c}, {reg x}, {rm aw d}"
  | .rol d c => two "rol" (count c) (rm aw d)
  | .ror d c => two "ror" (count c) (rm aw d)
  | .rcl d c => two "rcl" (count c) (rm aw d)
  | .rcr d c => two "rcr" (count c) (rm aw d)
  | .bswap d => s!"bswap {reg d}"
  | .jcc cc l => s!"j{cc} {l}"
  | .jmp t => s!"jmp {target aw t}"
  | .call t => s!"call {target aw t}"
  | .ret => "ret"
  | .nop 1 => "nop"
  | .nop n => s!"nop {n}"
  | .nopalign a none => s!".align {a}"
  | .nopalign a (some p) => s!".align {a}, {p}"

def avxOperation {w} (aw : Width) (op : AvxOperation w) : String :=
  let two (mn : String) {w} (d x : AvxRegOrMem w) := s!"{mn} {avxRm aw x}, {avxRm aw d}"
  match op with
  | .movups d x => two "movups" d x
  | .vmovups d x => two "vmovups" d x
  | .movaps d x => two "movaps" d x
  | .subps d x => two "subps" d x
  | .addps d x => two "addps" d x

def instr : Instr → String
  | .regular aw _ op => operation aw op
  | .avx aw _ op => avxOperation aw op

def directive : Directive → String
  | .instr i => instr i
  | .label l => s!"{l}:"
  | d@(.byteArray _) => toString d

end Kraken.X64.ATT

/-- Print a program in AT&T syntax, one directive per line. -/
def Kraken.X64.toATT (p : Program) : String :=
  "\n".intercalate (p.map ATT.directive)
