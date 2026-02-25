/-
Kraken - Code Generation

Generates executable x86_64 assembly from Kraken programs.
-/

import AsmInterp.Core

namespace Kraken

-- Register to assembly string
def regToAsm : Reg → String
  | .rax => "%rax" | .rbx => "%rbx" | .rcx => "%rcx" | .rdx => "%rdx"
  | .rsi => "%rsi" | .rdi => "%rdi" | .rsp => "%rsp" | .rbp => "%rbp"
  | .r8  => "%r8"  | .r9  => "%r9"  | .r10 => "%r10" | .r11 => "%r11"
  | .r12 => "%r12" | .r13 => "%r13" | .r14 => "%r14" | .r15 => "%r15"

-- Operand to assembly string (word offsets converted to bytes)
def opToAsm : Operand → String
  | .reg r => regToAsm r
  | .imm v => s!"${v}"
  | .mem base 0 => s!"({regToAsm base})"
  | .mem base wordOffset =>
    let byteOffset := wordOffset * 8
    s!"{byteOffset}({regToAsm base})"
  | .memIdx base idx 0 => s!"({regToAsm base},{regToAsm idx},8)"
  | .memIdx base idx wordOffset =>
    let byteOffset := wordOffset * 8
    s!"{byteOffset}({regToAsm base},{regToAsm idx},8)"
  | .memByte base 0 => s!"({regToAsm base})"
  | .memByte base byteOffset => s!"{byteOffset}({regToAsm base})"

-- Single instruction to assembly string
def instrToAsm : Instr → String
  -- Arithmetic
  | .add dst src  => s!"\taddq\t{opToAsm src}, {opToAsm dst}"
  | .adc dst src  => s!"\tadcq\t{opToAsm src}, {opToAsm dst}"
  | .adcx dst src => s!"\tadcxq\t{opToAsm src}, {opToAsm dst}"
  | .adox dst src => s!"\tadoxq\t{opToAsm src}, {opToAsm dst}"
  | .sub dst src  => s!"\tsubq\t{opToAsm src}, {opToAsm dst}"
  | .sbb dst src  => s!"\tsbbq\t{opToAsm src}, {opToAsm dst}"
  | .mul src      => s!"\tmulq\t{opToAsm src}"
  | .mulx hi lo src =>
    match hi, lo with
    | .reg hi_r, .reg lo_r => s!"\tmulxq\t{opToAsm src}, {regToAsm lo_r}, {regToAsm hi_r}"
    | _, _ => "# ERROR: mulx requires register destinations"
  | .imul dst src => s!"\timulq\t{opToAsm src}, {opToAsm dst}"
  | .neg dst      => s!"\tnegq\t{opToAsm dst}"
  | .dec dst      => s!"\tdecq\t{opToAsm dst}"

  -- Move/Load
  | .mov dst src  => s!"\tmovq\t{opToAsm src}, {opToAsm dst}"
  | .lea dst src  => s!"\tleaq\t{opToAsm src}, {regToAsm dst}"

  -- Bitwise
  | .xor dst src  => s!"\txorq\t{opToAsm src}, {opToAsm dst}"
  | .and dst src  => s!"\tandq\t{opToAsm src}, {opToAsm dst}"
  | .or dst src   => s!"\torq\t{opToAsm src}, {opToAsm dst}"

  -- Compare
  | .cmp a b      => s!"\tcmpq\t{opToAsm b}, {opToAsm a}"

  -- Control flow
  | .jmp target   => s!"\tjmp\t{target}"
  | .jz target    => s!"\tjz\t{target}"
  | .jnz target   => s!"\tjnz\t{target}"
  | .jb target    => s!"\tjb\t{target}"
  | .jae target   => s!"\tjae\t{target}"
  | .jne target   => s!"\tjne\t{target}"
  | .ja target    => s!"\tja\t{target}"

-- Label to assembly string
def labelToAsm : Option Label → String
  | .none => ""
  | .some l => s!"{l}:\n"

-- Convert a program to assembly
def programToAsm (p : Program) : String :=
  let lines := p.map fun (lbl, instr) =>
    labelToAsm lbl ++ instrToAsm instr
  "\n".intercalate lines

-- Assembly configuration for complete .S files
structure AsmConfig where
  funcName : String
  prologue : String
  epilogue : String
  body     : Program

-- Generate complete .S file
def genFullAsm (config : AsmConfig) : String :=
  config.prologue ++ "\n" ++ programToAsm config.body ++ "\n" ++ config.epilogue

end Kraken
