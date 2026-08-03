import Kraken.X64.Syntax
/-!
# IntelPrinter
This file prints Kraken-supported x64 assembly in Intel syntax.
This is different from Parser.lean which expects AT&T syntax.
-/

instance : ToString Reg64 where
  toString r := match r with
  | .rax => "rax" | .rbx => "rbx" | .rcx => "rcx" | .rdx => "rdx"
  | .rsi => "rsi" | .rdi => "rdi" | .rsp => "rsp" | .rbp => "rbp"
  | .r8  => "r8"  | .r9  => "r9"  | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

instance : ToString RegMm where
  toString r := match r with
  | .mm0  => "mm0"  | .mm1  => "mm1"  | .mm2  => "mm2"  | .mm3  => "mm3"
  | .mm4  => "mm4"  | .mm5  => "mm5"  | .mm6  => "mm6"  | .mm7  => "mm7"
  | .mm8  => "mm8"  | .mm9  => "mm9"  | .mm10 => "mm10" | .mm11 => "mm11"
  | .mm12 => "mm12" | .mm13 => "mm13" | .mm14 => "mm14" | .mm15 => "mm15"
  | .mm16 => "mm16" | .mm17 => "mm17" | .mm18 => "mm18" | .mm19 => "mm19"
  | .mm20 => "mm20" | .mm21 => "mm21" | .mm22 => "mm22" | .mm23 => "mm23"
  | .mm24 => "mm24" | .mm25 => "mm25" | .mm26 => "mm26" | .mm27 => "mm27"
  | .mm28 => "mm28" | .mm29 => "mm29" | .mm30 => "mm30" | .mm31 => "mm31"

def Reg.toStr {w} (r : Reg w) : String := match w, r with
  | .W64, .low r _ => toString r
  | .W32, .low r _ => match r with
    | .rax => "eax" | .rbx => "ebx" | .rcx => "ecx" | .rdx => "edx"
    | .rsi => "esi" | .rdi => "edi" | .rsp => "esp" | .rbp => "ebp"
    | .r8  => "r8d" | .r9  => "r9d" | .r10 => "r10d" | .r11 => "r11d"
    | .r12 => "r12d"| .r13 => "r13d"| .r14 => "r14d"| .r15 => "r15d"
  | .W16, .low r _ => match r with
    | .rax => "ax" | .rbx => "bx" | .rcx => "cx" | .rdx => "dx"
    | .rsi => "si" | .rdi => "di" | .rsp => "sp" | .rbp => "bp"
    | .r8  => "r8w" | .r9  => "r9w" | .r10 => "r10w" | .r11 => "r11w"
    | .r12 => "r12w"| .r13 => "r13w"| .r14 => "r14w"| .r15 => "r15w"
  | .W8, .low r _ => match r with
    | .rax => "al" | .rbx => "bl" | .rcx => "cl" | .rdx => "dl"
    | .rsi => "sil" | .rdi => "dil" | .rsp => "spl" | .rbp => "bpl"
    | .r8  => "r8b" | .r9  => "r9b" | .r10 => "r10b" | .r11 => "r11b"
    | .r12 => "r12b"| .r13 => "r13b"| .r14 => "r14b"| .r15 => "r15b"
  | .W8, .ah => "ah" | .W8, .bh => "bh" | .W8, .ch => "ch" | .W8, .dh => "dh"

instance {w} : ToString (Reg w) where toString := Reg.toStr

instance {w} : ToString (AvxReg w) where
  toString r := match r with
  | .xmm r => "x" ++ toString r
  | .ymm r => "y" ++ toString r
  | .zmm r => "z" ++ toString r

def RegOrRip.toStr (b : RegOrRip) (addr_w : Width := .W64) : String := match b with
  | .reg r => toString (Reg.low r addr_w)
  | .rip => "rip"
instance : ToString RegOrRip where toString b := b.toStr

def ConstExpr.toStr : ConstExpr → String
  | .label l => l
  | .int64 i => s!"{i}"
  | .before_current_instruction => "."
  | .after_current_instruction => "."
  | .add e1 e2 => s!"({e1.toStr} + {e2.toStr})"
  | .sub e1 e2 => s!"({e1.toStr} - {e2.toStr})"
instance : ToString ConstExpr where toString := ConstExpr.toStr

def AddrExpr.toStr (a : AddrExpr) (addr_w : Width := .W64) : String :=
  let dispStr := match a.base, a.disp with
    -- Unwrap RIP-relative displacements back to just the label for printing
    -- (like RelRegOrMem.toStr below)
    | .some .rip, .sub e .after_current_instruction => toString e
    | _, _ => toString a.disp
  "[" ++ "+".intercalate (
    (match a.base with | .some b => [b.toStr addr_w] | _ => [])
    ++ (match a.idx with | .some ⟨r, s⟩ => [s!"{Reg.low r addr_w}*{s.bytes}"] | _ => [])
    ++ [dispStr]
  ) ++ "]"

def RegOrMem.toStr {w} (rm : RegOrMem w) (addr_w : Width := .W64) : String := match rm with
  | .reg r => ToString.toString r
  | .mem a => match w with
    | .W64 => "QWORD PTR " ++ a.toStr addr_w
    | .W32 => "DWORD PTR " ++ a.toStr addr_w
    | .W16 => "WORD PTR " ++ a.toStr addr_w
    | .W8 => "BYTE PTR " ++ a.toStr addr_w
instance {w} : ToString (RegOrMem w) where toString rm := rm.toStr

def AvxRegOrMem.toStr {w} (rm : AvxRegOrMem w) (addr_w : Width := .W64) : String := match rm with
  | .avx r => ToString.toString r
  | .mem a => match w with
    | .W512 => "ZMMWORD PTR " ++ a.toStr addr_w
    | .W256 => "YMMWORD PTR " ++ a.toStr addr_w
    | .W128 => "XMMWORD PTR " ++ a.toStr addr_w
instance {w} : ToString (AvxRegOrMem w) where toString rm := rm.toStr

def Operand.toStr {w} (op : Operand w) (addr_w : Width := .W64) : String := match op with
  | .regOrMem rm => rm.toStr addr_w
  | .imm v => toString v
instance {w} : ToString (Operand w) where toString op := op.toStr

def AvxOperand.toStr {w} (op : AvxOperand w) (addr_w : Width := .W64) : String := match op with
  | .regOrMem rm => rm.toStr addr_w
instance {w} : ToString (AvxOperand w) where toString op := op.toStr

def RelRegOrMem.toStr (rel : RelRegOrMem) (addr_w : Width := .W64) : String := match rel with
  | .rel (.sub e .after_current_instruction) => toString e
  | .rel c => toString c
  | .reg r => toString r
  | .mem a => "QWORD PTR " ++ a.toStr addr_w
instance : ToString RelRegOrMem where toString rel := rel.toStr

instance : ToString CondCode where toString
  | .z => "e" | .nz => "ne" | .c => "b" | .nc => "ae" | .a => "a" | .be => "be"

instance : ToString ShiftCountExpr where toString
  | .cl => "cl"
  | .imm8 v => ToString.toString v

def Operation.toStr {w} (op : Operation w) (addr_w : Width := .W64) : String := match op with
  | .mov dst src => s!"mov {dst.toStr addr_w}, {src.toStr addr_w}"
  | .movsx dst src => s!"movsx {dst.toStr addr_w}, {src.toStr addr_w}"
  | .movzx dst src => s!"movzx {dst.toStr addr_w}, {src.toStr addr_w}"
  | .push src => s!"push {src.toStr addr_w}"
  | .pop dst => s!"pop {dst.toStr addr_w}"
  | .setcc cc dst => s!"set{cc} {dst.toStr addr_w}"
  | .cmovcc cc dst src => s!"cmov{cc} {dst}, {src.toStr addr_w}"
  | .lea dst src => s!"lea {dst}, {src.toStr addr_w}"
  | .add dst src => s!"add {dst.toStr addr_w}, {src.toStr addr_w}"
  | .adc dst src => s!"adc {dst.toStr addr_w}, {src.toStr addr_w}"
  | .adcx dst src => s!"adcx {dst}, {src.toStr addr_w}"
  | .adox dst src => s!"adox {dst}, {src.toStr addr_w}"
  | .inc dst => s!"inc {dst.toStr addr_w}"
  | .dec dst => s!"dec {dst.toStr addr_w}"
  | .neg dst => s!"neg {dst.toStr addr_w}"
  | .sub dst src => s!"sub {dst.toStr addr_w}, {src.toStr addr_w}"
  | .sbb dst src => s!"sbb {dst.toStr addr_w}, {src.toStr addr_w}"
  | .cmp a b => s!"cmp {a.toStr addr_w}, {b.toStr addr_w}"
  | .mul src => s!"mul {src.toStr addr_w}"
  | .mulx hi lo src => s!"mulx {hi}, {lo}, {src.toStr addr_w}"
  | .imul none src1 src2 => s!"imul {src1.toStr addr_w}, {src2.toStr addr_w}"
  | .imul (some dst) src1 src2 => s!"imul {dst.toStr addr_w}, {src1.toStr addr_w}, {src2.toStr addr_w}"
  | .imul1 src => s!"imul {src.toStr addr_w}"
  | .test a b => s!"test {a.toStr addr_w}, {b.toStr addr_w}"
  | .and dst src => s!"and {dst.toStr addr_w}, {src.toStr addr_w}"
  | .not dst => s!"not {dst.toStr addr_w}"
  | .or dst src => s!"or {dst.toStr addr_w}, {src.toStr addr_w}"
  | .xor dst src => s!"xor {dst.toStr addr_w}, {src.toStr addr_w}"
  | .shl dst cnt => s!"shl {dst.toStr addr_w}, {cnt}"
  | .shr dst cnt => s!"shr {dst.toStr addr_w}, {cnt}"
  | .sar dst cnt => s!"sar {dst.toStr addr_w}, {cnt}"
  | .shld dst src cnt => s!"shld {dst.toStr addr_w}, {src}, {cnt}"
  | .shrd dst src cnt => s!"shrd {dst.toStr addr_w}, {src}, {cnt}"
  | .rol dst cnt => s!"rol {dst.toStr addr_w}, {cnt}"
  | .ror dst cnt => s!"ror {dst.toStr addr_w}, {cnt}"
  | .rcl dst cnt => s!"rcl {dst.toStr addr_w}, {cnt}"
  | .rcr dst cnt => s!"rcr {dst.toStr addr_w}, {cnt}"
  | .bswap dst => s!"bswap {dst}"
  | .jcc cc l => s!"j{cc} {l}"
  | .jmp tgt => s!"jmp {tgt.toStr addr_w}"
  | .call tgt => s!"call {tgt.toStr addr_w}"
  | .ret => "ret"
  | .nop n => s!".nops {n}"
  | .nopalign a none => s!".align {a}"
  | .nopalign a (some p) => s!".align {a}, {p}"
instance {w} : ToString (Operation w) where toString op := op.toStr

def AvxOperation.toStr {w} (op : AvxOperation w) (addr_w : Width := .W64) : String := match op with
  | .movups dst src => s!"movups {dst.toStr addr_w}, {src.toStr addr_w}"
  | .vmovups dst src => s!"vmovups {dst.toStr addr_w}, {src.toStr addr_w}"
  | .movaps dst src => s!"movaps {dst.toStr addr_w}, {src.toStr addr_w}"
  | .subps dst src => s!"subps {dst.toStr addr_w}, {src.toStr addr_w}"
  | .addps dst src => s!"addps {dst.toStr addr_w}, {src.toStr addr_w}"
instance {w} : ToString (Operation w) where toString op := op.toStr

instance : ToString Instr where
  toString i := match i with
  | .regular a _ o => o.toStr a
  | .avx a _ o => o.toStr a

instance : ToString Directive where
  toString
  | .instr i => ToString.toString i
  | .label l => s!"{l}:"
  | .byteArray bs => ".byte "++", ".intercalate (bs.toList.map (fun b => s!"{b}"))
