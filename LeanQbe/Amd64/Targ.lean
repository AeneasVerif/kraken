module

public import LeanQbe.Amd64.Isel

/-!
# x64 snippets (QBE `amd64/targ.c`, `amd64/emit.c` in spirit)

The executable part of the x64 target: register sets of the System V ABI and one snippet per
thing the lowering emits, as Kraken x64 directives. The step lemmas and the `Target` instance are
in `TargLemmas.lean`.

Register roles:

* scratch: `r10`, `r11` (caller-saved, not used for arguments or results);
* allocatable: the remaining caller-saved registers `rax rcx rdx rsi rdi r8 r9` (leaf functions do
  not save callee-saved registers yet);
* arguments `rdi rsi rdx rcx r8 r9`, results `rax rdx`;
* callee-saved `rbx rbp r12 r13 r14 r15`; stack pointer `rsp`.

The snippets for IL operations (`op`, `load`, `store`) are in `Isel.lean`.
-/

@[expose] public section

namespace LeanQbe.Amd64

/-- `jmp l` (the encoding the parser produces). -/
def jmp (l : String) : List Directive :=
  [ins (.jmp (.rel (.sub (.label l) .after_current_instruction)))]

/-- `test %r32, %r32; jnz l` (the IL's `jnz` tests the low 32 bits). -/
def jnz (r : Reg64) (l : String) : List Directive :=
  [ins32 (.test (.reg (d r)) (.reg (d r))), ins (.jcc .nz l)]

/-- `ret` -/
def ret : List Directive := [ins .ret]

/-! ## Frame instructions (plan step 2b) -/

/-- `push %r` -/
def pushD (r : Reg64) : Directive := ins (.push (.reg (q r)))

/-- `pop %r` -/
def popD (r : Reg64) : Directive := ins (.pop (.reg (q r)))

/-- `sub $c, %rsp` -/
def subSpD (c : Int64) : Directive := ins (.sub (.reg (q .rsp)) (.imm (.int64 c)))

/-- `add $c, %rsp` -/
def addSpD (c : Int64) : Directive := ins (.add (.reg (q .rsp)) (.imm (.int64 c)))

/-- `[rsp + off]` -/
abbrev atSp (off : Int64) : AddrExpr := { base := some (.reg .rsp), idx := none, disp := .int64 off }

/-- `movq %rv, off(%rsp)` -/
def stSpD (rv : Reg64) (off : Int64) : Directive := ins (.mov (.mem (atSp off)) (.reg (q rv)))

/-- `movq off(%rsp), %rd` -/
def ldSpD (rd : Reg64) (off : Int64) : Directive := ins (.mov (.reg (q rd)) (.mem (atSp off)))

/-- `call l` (the encoding the parser produces). -/
def callD (l : String) : Directive :=
  ins (.call (.rel (.sub (.label l) .after_current_instruction)))

/-- `jmp l` -/
def jmpD (l : String) : Directive :=
  ins (.jmp (.rel (.sub (.label l) .after_current_instruction)))

/-- Frame size for `ns` slots: `8 ns` rounded to `≡ 8 mod 16`, so that `rsp ≡ 0 mod 16` at calls
(the return address makes up the other 8). -/
def frameSize (ns : Nat) : Nat := 8 * ns + (if ns % 2 = 0 then 8 else 0)

/-- The x64 instruction set as seen by the lowering. -/
@[reducible] def isa : Isa where
  Reg := Reg64
  Directive := Directive
  label := .label
  sp := .rsp
  scratch := [.r10, .r11]
  allocatable := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9]
  argRegs := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]
  retRegs := [.rax, .rdx]
  calleeSaved := [.rbx, .rbp, .r12, .r13, .r14, .r15]
  mov := mov
  movi := movi
  op := op
  load := load
  store := store
  jmp := jmp
  jnzCmp := jnzCmp
  ret := ret
  raRegs := []
  frameSize := frameSize
  prologue ns := [subSpD (Int64.ofNat (frameSize ns))]
  epilogue ns := [addSpD (Int64.ofNat (frameSize ns))]
  slotSt i r := [stSpD r (Int64.ofNat (8 * i))]
  slotLd rd i := [ldSpD rd (Int64.ofNat (8 * i))]
  call sym := [callD sym]
  tailJmp sym := [jmpD sym]

end LeanQbe.Amd64
