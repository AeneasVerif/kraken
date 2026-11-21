module

public import LeanQbe.T.TargetLemmas
public import LeanQbe.T.Logic.MemLemmas
public import LeanQbe.T.Logic.Bytes
import all Kraken.Mem
import all Kraken.Separation

/-!
# A Small Executable x64-Flavoured `Target` for the `T7b` Litmus Suite (`G12a`/`G12d`)

A toy machine (`Instr`, `MData`, `exec`; x64 register numbers `rax=0 … rsp=4 … rdi=7 r8..r15`),
512-bit vector registers, flags `CF`/`ZF`/`OF` (mask bits 0/3/5), byte memory `Mem 64`, `call`/`ret`
pushing/popping an 8-byte return address at `rsp`, and the flag-aware `VariantHint` variants:
* default `add/sub/and/or/xor/shl/lshr/cmp/adc` clobber all flags;
* `adcx` reads/writes `CF` only, `adox` reads/writes `OF` only (interleaved carry chains);
* `.decInc`: `sub x 1` is `dec` and `cmp ne x 0` is `tstz` (x86 `inc;dec`), both keep `CF`;
* `.disp`: `add x c` is `lea` (flags kept).

The `Target` instance (all `GprTarget`/`FrameTarget`/`VecTarget` obligations) is `litmusTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.RegaLitmus
open LeanQbe.T

deriving instance Lean.ToExpr for Fmt
deriving instance Lean.ToExpr for Ty

/-! ## 1. Conditions, Flag Masks, Operands, and Instructions -/

inductive Cond where
  | cf | ncf | zf | nzf | of | nof
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

def maskCF : FlagMask := 0x01#8
def maskZF : FlagMask := 0x08#8
def maskOF : FlagMask := 0x20#8
/-- `dec`/`inc` clobber `PF, AF, ZF, SF, OF` and keep `CF`. -/
def maskDecInc : FlagMask := 0x3E#8

def Cond.reads : Cond → FlagMask
  | .cf | .ncf => maskCF
  | .zf | .nzf => maskZF
  | .of | .nof => maskOF
def Cond.neg : Cond → Cond
  | .cf => .ncf | .ncf => .cf | .zf => .nzf | .nzf => .zf | .of => .nof | .nof => .of

inductive Src where
  | reg (r : Nat)
  | imm (c : BitVec 64)
  deriving DecidableEq, Repr, Lean.ToExpr

inductive Addr where
  | bd (base : Nat) (disp : BitVec 64)
  | bid (base idx : Nat) (scale : Nat) (disp : BitVec 64)
  | abs (a : BitVec 64)
  deriving DecidableEq, Repr, Lean.ToExpr

inductive BinK where
  | add | sub | and | or | xor | shl | lshr
  deriving DecidableEq, Repr, Lean.ToExpr

inductive Instr where
  | label (l : String)
  | mov (d s : Nat)
  | movi (d : Nat) (c : BitVec 64)
  | setcc (d : Nat) (c : Cond)
  /-- `xor %d, %d`: `d := 0`, `CF := OF := 0`, `ZF := 1`. -/
  | xorz (d : Nat)
  /-- `test %r8b, %r8b`: `ZF := (low byte = 0)`, `CF := OF := 0`. -/
  | test8 (r : Nat)
  | jmp (l : String)
  | jcc (c : Cond) (l : String)
  /-- `n`-bit ALU op, result zero-extended into `d`; writes `CF`, `ZF`, `OF`. -/
  | bin (k : BinK) (n : Nat) (d : Nat) (a b : Src)
  /-- `lea c(%a), %d` (flags kept). -/
  | lea (d a : Nat) (c : BitVec 64)
  /-- `dec`: `d := a - 1` (`n` bits); writes `ZF`, `OF`; keeps `CF`. -/
  | dec (n : Nat) (d : Nat) (a : Src)
  /-- `inc %a; dec %a` fused: `ZF := (a = 0)` (`n` bits), `OF := 0`; keeps `CF`. -/
  | tstz (n : Nat) (a : Src)
  /-- `cmp`: `ZF := a = b`, `CF := a <u b`, `OF := signed overflow of a - b`. -/
  | cmp (n : Nat) (a b : Src)
  /-- `adc`: `d := a + b + CF`, `CF := carry`, `ZF`, `OF` written. -/
  | adc (n : Nat) (d : Nat) (a b : Src)
  /-- `adcx`: `d := a + b + CF`, `CF := carry`; other flags kept. -/
  | adcx (n : Nat) (d : Nat) (a b : Src)
  /-- `adox`: `d := a + b + OF`, `OF := carry`; other flags kept. -/
  | adox (n : Nat) (d : Nat) (a b : Src)
  /-- `bt $0, %r`: `CF := bit 0 of r`; other flags kept. -/
  | bt0 (r : Nat)
  /-- `movz{b,w,l}`: `r := zext (r mod 2^n)`. -/
  | zext (n r : Nat)
  | ld (t : Ty) (d : Nat) (a : Addr)
  | st (t : Ty) (s : Src) (a : Addr)
  /-- `lea c(%rsp), %rsp` (flags kept). -/
  | spAdd (c : BitVec 64)
  | call (l : String)
  | ret
  | vmov (d s : Nat)
  | vmovi (d : Nat) (c : BitVec 512)
  /-- Lane-wise vector op on type `t` (low `t.size` bits; flags kept). -/
  | vbin (k : BinK) (t : Ty) (d a b : Nat)
  /-- Store the `w.slots` words of `v` at `8 i(%rsp)`. -/
  | vst (w : SlotWidth) (i : Nat) (v : Nat)
  /-- Load `w.slots` words from `8 i(%rsp)` into `d`. -/
  | vld (w : SlotWidth) (d : Nat) (i : Nat)
  deriving DecidableEq, Repr, Lean.ToExpr

/-! ## 2. Machine State and Semantics (generic in the memory representation) -/

/-- Byte-memory interface: the real machine uses `Mem 64`; concrete witnesses use the
kernel-reducible `FMem` (see `RegaLitmusTest.lean`). -/
structure MemOps (M : Type) where
  get : M → BitVec 64 → Option UInt8
  put : M → BitVec 64 → List UInt8 → M

def memOps : MemOps (Mem 64) := ⟨fun m k => m.get? k, Mem.storeBytes⟩

/-- `loadVal`, generic in the memory (definitionally `loadVal` for `memOps`). -/
def loadValG {M : Type} (ops : MemOps M) (m : M) (t : Ty) (a : BitVec 64) : Option (Val t) :=
  ((((List.range t.bytes).map fun i => ops.get m (a + BitVec.ofNat 64 i)).mapM id).map
      Int.ofBytes).bind fun i =>
    match t with
    | .bool => if i == 0 || i == 1 then some (i == 1) else none
    | .bits n => some (ofBits (.bits n) (BitVec.ofInt n i))
    | .float f => some (ofBits (.float f) (BitVec.ofInt f.width i))
    | .pair x y => some (ofBits (.pair x y) (BitVec.ofInt (x.size + y.size) i))

/-- `storeMem`, generic in the memory (definitionally `storeMem` for `memOps`). -/
def storeMemG {M : Type} (ops : MemOps M) (m : M) (t : Ty) (a : BitVec 64) (v : Val t) : M :=
  ops.put m a (Int.toBytes t.bytes ((toBits t v).setWidth (8 * t.bytes)).toInt)

structure MDataG (M : Type) where
  gpr : Nat → BitVec 64
  vec : Nat → BitVec 512
  cf : Bool
  zf : Bool
  of : Bool
  mem : M
abbrev MData := MDataG (Mem 64)

structure LHost where
  prog : List Instr
  len_lt : prog.length < 2 ^ 64

section Sem
variable {M : Type}

def MDataG.evalCond (s : MDataG M) : Cond → Bool
  | .cf => s.cf | .ncf => !s.cf | .zf => s.zf | .nzf => !s.zf | .of => s.of | .nof => !s.of
def MDataG.setGpr (s : MDataG M) (r : Nat) (v : BitVec 64) : MDataG M :=
  { s with gpr := fun x => if x = r then v else s.gpr x }
def MDataG.setVec (s : MDataG M) (r : Nat) (v : BitVec 512) : MDataG M :=
  { s with vec := fun x => if x = r then v else s.vec x }
def MDataG.src (s : MDataG M) : Src → BitVec 64
  | .reg r => s.gpr r
  | .imm c => c
def MDataG.addr (s : MDataG M) : Addr → BitVec 64
  | .bd r d => s.gpr r + d
  | .bid b i sc d => s.gpr b + (s.gpr i <<< sc) + d
  | .abs a => a

end Sem

def binEval {n : Nat} : BinK → BitVec n → BitVec n → BitVec n
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y
  | .shl, x, y => x <<< (y.toNat % n)
  | .lshr, x, y => x >>> (y.toNat % n)
def binCF {n : Nat} : BinK → BitVec n → BitVec n → Bool
  | .add, x, y => decide (2 ^ n ≤ x.toNat + y.toNat)
  | .sub, x, y => x.ult y
  | _, _, _ => false
def addOF {n : Nat} (x y r : BitVec n) : Bool := x.msb == y.msb && r.msb != x.msb

/-- GPR encoding of a value of a GPR type (zero-extended). -/
def valToGpr : (t : Ty) → Val t → BitVec 64
  | .bool, b => BitVec.ofNat 64 b.toNat
  | .bits _, v => v.setWidth 64
  | _, _ => 0

/-- Value of type `t` held in the low bits of a GPR. -/
def gprToVal : (t : Ty) → BitVec 64 → Val t
  | .bool, x => x.getLsbD 0
  | .bits n, x => x.setWidth n
  | .float f, _ => (0 : BitVec f.width)
  | .pair a b, _ => (default : Val (.pair a b))

/-- Store the words `ws` at consecutive 8-byte addresses from `a`. -/
def storeWords {M : Type} (ops : MemOps M) (m : M) (a : BitVec 64) : List (BitVec 64) → M
  | [] => m
  | w :: ws => storeWords ops (storeMemG ops m i64 a w) (a + 8) ws

/-- Load `k` consecutive 8-byte words from `a`. -/
def loadWords {M : Type} (ops : MemOps M) (m : M) (a : BitVec 64) : Nat → Option (List (BitVec 64))
  | 0 => some []
  | k + 1 => (loadValG ops m i64 a).bind fun w => (loadWords ops m (a + 8) k).map (w :: ·)

/-- Inverse of `unpackSlotWords`: word `j` goes to bits `[64 j, 64 j + 64)`. -/
def packWords : List (BitVec 64) → BitVec 512
  | [] => 0
  | w :: ws => (packWords ws <<< 64) ||| w.setWidth 512

def labelAddr (h : LHost) (l : String) : Nat :=
  (h.prog.findIdx? (· == Instr.label l)).getD h.prog.length

def vbinVal (k : BinK) (t : Ty) (a b : BitVec 512) : BitVec 512 :=
  let x := ofBits t (a.setWidth t.size)
  let y := ofBits t (b.setWidth t.size)
  let r : Val t := match k with
    | .add => lift2 (· + ·) (· ^^ ·) t x y
    | .sub => lift2 (· - ·) (· ^^ ·) t x y
    | .and => lift2 (· &&& ·) (· && ·) t x y
    | .or => lift2 (· ||| ·) (· || ·) t x y
    | .xor => lift2 (· ^^^ ·) (· ^^ ·) t x y
    | .shl | .lshr => x
  (toBits t r).setWidth 512

/-- Execute instruction `i` at `pc`. -/
def execI {M : Type} (ops : MemOps M) (h : LHost) (s : MDataG M) (pc : Nat) :
    Instr → Option (MDataG M × Nat)
  | .label _ => some (s, pc + 1)
  | .mov d r => some (s.setGpr d (s.gpr r), pc + 1)
  | .movi d c => some (s.setGpr d c, pc + 1)
  | .setcc d c => some (s.setGpr d (BitVec.ofNat 64 (s.evalCond c).toNat), pc + 1)
  | .xorz d => some ({ s.setGpr d 0 with cf := false, zf := true, of := false }, pc + 1)
  | .test8 r => some ({ s with cf := false, zf := (s.gpr r).setWidth 8 == 0, of := false }, pc + 1)
  | .jmp l => some (s, labelAddr h l)
  | .jcc c l => some (s, if s.evalCond c then labelAddr h l else pc + 1)
  | .bin k n d a b =>
    let x := (s.src a).setWidth n
    let y := (s.src b).setWidth n
    let r := binEval k x y
    some ({ s.setGpr d (r.setWidth 64) with cf := binCF k x y, zf := r == 0, of := addOF x y r },
      pc + 1)
  | .lea d a c => some (s.setGpr d (s.gpr a + c), pc + 1)
  | .dec n d a =>
    let r := (s.src a).setWidth n - 1
    some ({ s.setGpr d (r.setWidth 64) with zf := r == 0, of := r == BitVec.intMax n }, pc + 1)
  | .tstz n a => some ({ s with zf := (s.src a).setWidth n == 0, of := false }, pc + 1)
  | .cmp n a b =>
    let x := (s.src a).setWidth n
    let y := (s.src b).setWidth n
    some ({ s with cf := x.ult y, zf := x == y, of := addOF x (-y) (x - y) }, pc + 1)
  | .adc n d a b =>
    let x := (s.src a).setWidth n
    let y := (s.src b).setWidth n
    let r := x + y + BitVec.ofNat n s.cf.toNat
    some ({ s.setGpr d (r.setWidth 64) with
      cf := decide (2 ^ n ≤ x.toNat + y.toNat + s.cf.toNat), zf := r == 0, of := addOF x y r },
      pc + 1)
  | .adcx n d a b =>
    let x := (s.src a).setWidth n
    let y := (s.src b).setWidth n
    some ({ s.setGpr d ((x + y + BitVec.ofNat n s.cf.toNat).setWidth 64) with
      cf := decide (2 ^ n ≤ x.toNat + y.toNat + s.cf.toNat) }, pc + 1)
  | .adox n d a b =>
    let x := (s.src a).setWidth n
    let y := (s.src b).setWidth n
    some ({ s.setGpr d ((x + y + BitVec.ofNat n s.of.toNat).setWidth 64) with
      of := decide (2 ^ n ≤ x.toNat + y.toNat + s.of.toNat) }, pc + 1)
  | .bt0 r => some ({ s with cf := (s.gpr r).getLsbD 0 }, pc + 1)
  | .zext n r => some (s.setGpr r (((s.gpr r).setWidth n).setWidth 64), pc + 1)
  | .ld t d a => (loadValG ops s.mem t (s.addr a)).map fun v => (s.setGpr d (valToGpr t v), pc + 1)
  | .st t v a =>
    let m := storeMemG ops s.mem t (s.addr a) (gprToVal t (s.src v))
    some ({ s with mem := m }, pc + 1)
  | .spAdd c => some (s.setGpr 4 (s.gpr 4 + c), pc + 1)
  | .call l =>
    let sp' := s.gpr 4 - 8
    let m := storeMemG ops s.mem i64 sp' (BitVec.ofNat 64 (pc + 1))
    some ({ s.setGpr 4 sp' with mem := m }, labelAddr h l)
  | .ret => (loadValG ops s.mem i64 (s.gpr 4)).map fun ra => (s.setGpr 4 (s.gpr 4 + 8), ra.toNat)
  | .vmov d r => some (s.setVec d (s.vec r), pc + 1)
  | .vmovi d c => some (s.setVec d c, pc + 1)
  | .vbin k t d a b => some (s.setVec d (vbinVal k t (s.vec a) (s.vec b)), pc + 1)
  | .vst w i v =>
    let m := storeWords ops s.mem (s.gpr 4 + BitVec.ofNat 64 (8 * i)) (unpackSlotWords w (s.vec v))
    some ({ s with mem := m }, pc + 1)
  | .vld w d i =>
    (loadWords ops s.mem (s.gpr 4 + BitVec.ofNat 64 (8 * i)) w.slots).map fun ws =>
      (s.setVec d (packWords ws), pc + 1)

def execG {M : Type} (ops : MemOps M) (h : LHost) (st : MDataG M × Nat) : Option (MDataG M × Nat) :=
  match h.prog[st.2]? with
  | some i => execI ops h st.1 st.2 i
  | none => none
abbrev exec (h : LHost) (st : MData × Nat) : Option (MData × Nat) := execG memOps h st

def mach : Machine Nat Nat Cond Instr where
  MData := MData
  Addr := Nat
  State := MData × Nat
  Host := LHost
  getGpr s r := s.gpr r
  getVec s v := s.vec v
  evalCond s c := s.evalCond c
  mem s := s.mem
  mkState s a := (s, a)
  pc st := st.2
  data st := st.1
  pc_mk _ _ := rfl
  data_mk _ _ := rfl
  mk_eta _ := rfl
  prog h := h.prog
  addrOf _ k := k
  labelAddr := labelAddr
  step h st P := ∃ st', exec h st = some st' ∧ P st'

/-! ## 3. Snippets: `GprIsa`, `VecIsa`, `FrameIsa` -/

def srcOf : {t : Ty} → PArg Nat Nat Cond t → Option Src
  | .bits _, .gpr r => some (.reg r)
  | .bits _, .imm c => some (.imm (c.setWidth 64))
  | _, _ => none
def addrOf : AddrArg Nat → Addr
  | .baseDisp r d => .bd r d.toBitVec
  | .baseIdxDisp b i sc d => .bid b i sc.shift d.toBitVec
  | .imm a => .abs a
def isGprTy : Ty → Bool
  | .bool => true
  | .bits n => [8, 16, 32, 64].contains n
  | _ => false

def binArm (k : BinK) (n d : Nat) (a b : PArg Nat Nat Cond (.bits n)) :
    Option (List Instr × FlagMask) :=
  if Nat.ble n 64 then
    (srcOf a).bind fun sa => (srcOf b).map fun sb => ([.bin k n d sa sb], FlagMask.all)
  else none

def srcOfBool : PArg Nat Nat Cond .bool → Option Src
  | .gpr r => some (.reg r)
  | .imm b => some (.imm (BitVec.ofNat 64 b.toNat))
  | _ => none

/-- `and/or/xor` on `bool`s held in GPRs (`0`/`1` in the low byte). -/
def boolArm (k : BinK) (d : Nat) (a b : PArg Nat Nat Cond .bool) : Option (List Instr × FlagMask) :=
  (srcOfBool a).bind fun sa => (srcOfBool b).map fun sb => ([.bin k 8 d sa sb], FlagMask.all)

def addArm (n d : Nat) (a b : PArg Nat Nat Cond (.bits n)) (vh : VariantHint) :
    Option (List Instr × FlagMask) :=
  match vh, a, b with
  | .disp _, .gpr ra, .imm c => if Nat.beq n 64 then some ([.lea d ra (c.setWidth 64)], 0#8) else none
  | _, _, _ => binArm .add n d a b

def subArm (n d : Nat) (a b : PArg Nat Nat Cond (.bits n)) (vh : VariantHint) :
    Option (List Instr × FlagMask) :=
  match vh, b with
  | .decInc, .imm c =>
    if Nat.ble n 64 && c == 1#n then (srcOf a).map fun sa => ([.dec n d sa], maskDecInc) else none
  | _, _ => binArm .sub n d a b

def cmpCond : CmpOp → Option Cond
  | .eq => some .zf
  | .ne => some .nzf
  | .ult => some .cf
  | _ => none

def cmpArm (o : CmpOp) (n : Nat) (a b : PArg Nat Nat Cond (.bits n)) (dst : PDst Nat Nat Cond .bool)
    (vh : VariantHint) : Option (List Instr × FlagMask) :=
  if !Nat.ble n 64 then none
  else match vh, o, b, dst with
    | .decInc, .ne, .imm c, .flag .nzf =>
      if c == 0#n then (srcOf a).map fun sa => ([.tstz n sa], maskDecInc) else none
    | _, _, _, _ =>
      (cmpCond o).bind fun cc => (srcOf a).bind fun sa => (srcOf b).bind fun sb =>
        match dst with
        | .flag c' => if c' == cc then some ([.cmp n sa sb], FlagMask.all) else none
        | .gpr d => some ([.cmp n sa sb, .setcc d cc], FlagMask.all)
        | .vec _ => none

/-- `addc`: `cin` in `CF` (`adc`), `false` (`add`), or a GPR (`bt $0; adc`); `cout` in `CF` or
a GPR (`setc`); `adcx`/`adox` variants for interleaved `CF`/`OF` chains. -/
def addcArm (n d : Nat) (a b : PArg Nat Nat Cond (.bits n)) (cin : PArg Nat Nat Cond .bool)
    (cout : PDst Nat Nat Cond .bool) (vh : VariantHint) : Option (List Instr × FlagMask) :=
  if !Nat.ble n 64 then none
  else (srcOf a).bind fun sa => (srcOf b).bind fun sb =>
    match vh, cin, cout with
    | .adcx, .flag .cf, .flag .cf => some ([.adcx n d sa sb], maskCF)
    | .adox, .flag .of, .flag .of => some ([.adox n d sa sb], maskOF)
    | .default, cin, cout =>
      let main : Option (List Instr) := match cin with
        | .flag .cf => some [.adc n d sa sb]
        | .imm false => some [.bin .add n d sa sb]
        | .gpr r => some [.bt0 r, .adc n d sa sb]
        | _ => none
      let post : Option (List Instr) := match cout with
        | .flag .cf => some []
        | .gpr r => if r == d then none else some [.setcc r .cf]
        | _ => none
      main.bind fun m => post.map fun p => (m ++ p, FlagMask.all)
    | _, _, _ => none

def gop : {sig rs : List Ty} → OpCode sig rs → Tup (PArg Nat Nat Cond) sig →
    Tup (PDst Nat Nat Cond) rs → VariantHint → Option (List Instr × FlagMask)
  | _, _, .add (.bits n), (a, b, ()), (.gpr d, ()), vh => addArm n d a b vh
  | _, _, .sub (.bits n), (a, b, ()), (.gpr d, ()), vh => subArm n d a b vh
  | _, _, .and (.bits n), (a, b, ()), (.gpr d, ()), _ => binArm .and n d a b
  | _, _, .or (.bits n), (a, b, ()), (.gpr d, ()), _ => binArm .or n d a b
  | _, _, .xor (.bits n), (a, b, ()), (.gpr d, ()), _ => binArm .xor n d a b
  | _, _, .and .bool, (a, b, ()), (.gpr d, ()), _ => boolArm .and d a b
  | _, _, .or .bool, (a, b, ()), (.gpr d, ()), _ => boolArm .or d a b
  | _, _, .xor .bool, (a, b, ()), (.gpr d, ()), _ => boolArm .xor d a b
  | _, _, .shl (.bits n), (a, b, ()), (.gpr d, ()), _ => binArm .shl n d a b
  | _, _, .lshr (.bits n), (a, b, ()), (.gpr d, ()), _ => binArm .lshr n d a b
  | _, _, .cmp o (.bits n) _ rfl, (a, b, ()), (dst, ()), vh => cmpArm o n a b dst vh
  | _, _, .addc n, (a, b, cin, ()), (.gpr d, cout, ()), vh => addcArm n d a b cin cout vh
  | _, _, _, _, _, _ => none

def gprLoad (t : Ty) (rd : Nat) (a : AddrArg Nat) : Option (List Instr × FlagMask) :=
  if isGprTy t then some ([.ld t rd (addrOf a)], 0#8) else none
def gprStore (t : Ty) (pa : PArg Nat Nat Cond t) (a : AddrArg Nat) : Option (List Instr × FlagMask) :=
  if !isGprTy t then none
  else match pa with
    | .gpr r => some ([.st t (.reg r) (addrOf a)], 0#8)
    | .imm c => some ([.st t (.imm (valToGpr t c)) (addrOf a)], 0#8)
    | _ => none

def gprIsa : GprIsa Nat Nat Cond Instr where
  condReads := Cond.reads
  negCond := Cond.neg
  zeroFlags := [.cf, .of, .nzf]
  clearFlags := [.xorz 11]
  mov d s := [.mov d s]
  movi d c := [.movi d c]
  setcc d c := [.setcc d c]
  jmp l := [.jmp l]
  jcc c l := [.jcc c l]
  jnzGpr r l := ([.test8 r, .jcc .nzf l], FlagMask.all)
  op := gop
  load := gprLoad
  store := gprStore
  supportsScalarOp := defaultSupportsScalarOp [8, 16, 32, 64] false false false

/-- Slot width of an integer vector (`pair`) type: the smallest of `w64 … w512` that fits. -/
def vecSlotWidth : Ty → Option SlotWidth
  | .pair a b =>
    if (Ty.pair a b).hasFloat then none
    else if Nat.ble (Ty.pair a b).size 64 then some .w64
    else if Nat.ble (Ty.pair a b).size 128 then some .w128
    else if Nat.ble (Ty.pair a b).size 256 then some .w256
    else if Nat.ble (Ty.pair a b).size 512 then some .w512
    else none
  | _ => none

def vbinArm (k : BinK) (t : Ty) (d a b : Nat) : Option (List Instr × FlagMask) :=
  if (vecSlotWidth t).isSome then some ([.vbin k t d a b], 0#8) else none

def vop : {sig rs : List Ty} → OpCode sig rs → Tup (PArg Nat Nat Cond) sig →
    Tup (PDst Nat Nat Cond) rs → VariantHint → Option (List Instr × FlagMask)
  | _, _, .add t, (.vec a, .vec b, ()), (.vec d, ()), _ => vbinArm .add t d a b
  | _, _, .sub t, (.vec a, .vec b, ()), (.vec d, ()), _ => vbinArm .sub t d a b
  | _, _, .and t, (.vec a, .vec b, ()), (.vec d, ()), _ => vbinArm .and t d a b
  | _, _, .or t, (.vec a, .vec b, ()), (.vec d, ()), _ => vbinArm .or t d a b
  | _, _, .xor t, (.vec a, .vec b, ()), (.vec d, ()), _ => vbinArm .xor t d a b
  | _, _, _, _, _, _ => none

def supportsVecOp : {sig rs : List Ty} → OpCode sig rs → Tup (Arg (fun _ => Unit)) sig → Bool
  | _, _, .add t, _ | _, _, .sub t, _ | _, _, .and t, _ | _, _, .or t, _ | _, _, .xor t, _ =>
    (vecSlotWidth t).isSome
  | _, _, _, _ => false

def vecIsa : VecIsa Nat Nat Cond Instr where
  vecScratch := [15]
  vecAllocatable := [0, 1, 2, 3, 4, 5, 6, 7]
  vecArgRegs := [0, 1, 2, 3]
  vecRetRegs := [0]
  isAbiVec t := (vecSlotWidth t).isSome
  vecSlotWidth := vecSlotWidth
  vmov _ d s := [.vmov d s]
  vmovi _ d c := some [.vmovi d c]
  vslotSt w i v := [.vst w i v]
  vslotLd w d i := [.vld w d i]
  vop := vop
  vload _ _ _ := none
  vstore _ _ _ := none
  supportsVecOp := supportsVecOp

def canonAbi : Ty → Nat → List Instr × FlagMask
  | .bool, r => ([.zext 8 r], 0#8)
  | .bits n, r => if Nat.beq n 64 then ([], 0#8) else ([.zext n r], 0#8)
  | _, _ => ([], 0#8)

def frameIsa : FrameIsa Nat Instr where
  label := .label
  sp := 4
  scratch := [11]
  allocatable := [0, 1, 2, 6, 7, 8, 9, 10]
  calleeSaved := [3, 5, 12, 13, 14, 15]
  raRegs := []
  argRegs := [7, 6, 2, 1, 8, 9]
  retRegs := [0, 2]
  raBytes := 8
  frameSize ns := 8 * ns
  prologue ns := ([.spAdd (-BitVec.ofNat 64 (8 * ns))], 0#8)
  epilogue ns := ([.spAdd (BitVec.ofNat 64 (8 * ns))], 0#8)
  slotSt i r := [.st i64 (.reg r) (.bd 4 (BitVec.ofNat 64 (8 * i)))]
  slotLd r i := [.ld i64 r (.bd 4 (BitVec.ofNat 64 (8 * i)))]
  canonAbi := canonAbi
  call l := [.call l]
  exitJmp l := [.jmp l]
  ret := [.ret]

@[reducible] def isa : Isa where
  Reg := Nat
  VReg := Nat
  Cond := Cond
  Directive := Instr
  gpr := gprIsa
  vec := vecIsa
  frame := frameIsa


/-! ## 4. Basic Stepping Lemmas -/

@[simp] theorem loadValG_memOps (m : Mem 64) (t : Ty) (a : BitVec 64) :
    loadValG memOps m t a = loadVal m t a := by
  simp only [loadValG, loadVal, Mem.loadInt, Mem.loadBytes, memOps]
  cases t <;> rfl
@[simp] theorem storeMemG_memOps (m : Mem 64) (t : Ty) (a : BitVec 64) (v : Val t) :
    storeMemG memOps m t a v = storeMem m t a v := by
  simp only [storeMemG, storeMem, Mem.storeInt, memOps]

theorem exec_fetch {h : LHost} {k : Nat} {i : Instr} (s : MData) (hi : h.prog[k]? = some i) :
    exec h (s, k) = execI memOps h s k i := by
  simp [exec, execG, hi]

theorem run_exec {h : LHost} {k k' : Nat} {s s' : MData} {post : mach.State → Prop}
    (he : exec h (s, k) = some (s', k')) (hk : mach.Run h k' s' post) : mach.Run h k s post :=
  step_cps _ _ _ ⟨_, he, hk⟩

theorem run_instr {h : LHost} {k k' : Nat} {i : Instr} {s s' : MData} {post : mach.State → Prop}
    (hi : h.prog[k]? = some i) (he : execI memOps h s k i = some (s', k'))
    (hk : mach.Run h k' s' post) : mach.Run h k s post :=
  run_exec (by rw [exec_fetch s hi]; exact he) hk

/-- A one-instruction snippet that falls through. -/
theorem fallsTo_one {cr : Cond → FlagMask} {h : LHost} {k : Nat} {i : Instr} {g : List Nat}
    {v : List Nat} {f : FlagMask} {s s' : MData} {Q : MData → Prop} {post : mach.State → Prop}
    (he : execI memOps h s k i = some (s', k + 1)) (hq : Q s') (hfr : mach.Frame cr s s' g v f) :
    mach.FallsTo cr h k [i] g v f s Q post := fun hc hk =>
  run_instr (List.isInfixAt_singleton.mp hc) he (hk s' hq hfr)

/-! ## 5. `FrameTarget` and `VecTarget` -/

section FrameVec
open Std Std.ExtHashMap

theorem frame_setGpr (cr : Cond → FlagMask) (s : MData) (d : Nat) (v : BitVec 64) (g : List Nat)
    (hd : d ∈ g) (vc : List Nat) (f : FlagMask) : mach.Frame cr s (s.setGpr d v) g vc f :=
  ⟨fun r hr => by
      show (if r = d then v else s.gpr r) = s.gpr r
      simp only [show ¬ r = d from fun (e : r = d) => hr (e ▸ hd), ite_false],
    fun _ _ => rfl, fun _ _ => rfl⟩

theorem frame_setVec (cr : Cond → FlagMask) (s : MData) (d : Nat) (v : BitVec 512) (g : List Nat)
    (vc : List Nat) (hd : d ∈ vc) (f : FlagMask) : mach.Frame cr s (s.setVec d v) g vc f :=
  ⟨fun _ _ => rfl, fun r hr => by
      show (if r = d then v else s.vec r) = s.vec r
      simp only [show ¬ r = d from fun (e : r = d) => hr (e ▸ hd), ite_false],
    fun _ _ => rfl⟩

theorem frame_mem (cr : Cond → FlagMask) (s : MData) (m : Mem 64) (g : List Nat)
    (vc : List Nat) (f : FlagMask) : mach.Frame cr s { s with mem := m } g vc f :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

private theorem toBytes_ofInt_ofBytes {bs : List UInt8} (hl : bs.length = 8) :
    Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes bs)).toInt = bs := by
  rw [← Int.toBytes_emod]
  have h1 : ((BitVec.ofInt 64 (Int.ofBytes bs)).toInt).take (8 * 8) =
      (Int.ofBytes bs).take (8 * 8) := by
    grind
  rw [h1, Int.toBytes_emod, ← hl]
  exact Int.toBytes_ofBytes_all bs

theorem region8_cell64 {a : BitVec 64} {f : Mem 64} (h : region a 8 f) : ∃ v, cell64 a v f := by
  obtain ⟨bs, hl, hf⟩ := h
  exact ⟨BitVec.ofInt 64 (Int.ofBytes bs), by
    show (Int.toBytes 8 _).At a = f
    rw [toBytes_ofInt_ofBytes hl]; exact hf.symm⟩

theorem cell64_region8 {a v : BitVec 64} {f : Mem 64} (h : cell64 a v f) : region a 8 f :=
  ⟨Int.toBytes 8 v.toInt, Int.toBytes_length _ _, h.symm⟩

theorem store_region8 {a : BitVec 64} (v : BitVec 64) {G : Mem 64 → Prop} {m : Mem 64}
    (h : (region a 8 ⋆ G) m) : (cell64 a v ⋆ G) (storeMem m i64 a v) := by
  obtain ⟨f1, f2, hu, hd, h1, h2⟩ := h
  obtain ⟨v0, hv0⟩ := region8_cell64 h1
  exact (store_cell64 v ⟨f1, f2, hu, hd, hv0, h2⟩).2

def framePreds : FramePreds mach where
  RetAddr a (ra : Nat) m := ra < 2 ^ 64 ∧ cell64 a (BitVec.ofNat 64 ra) m
  raReg _ _ := True
  spEntry _ := True
  spOk _ := True
  Saved sp (ra : Nat) _ m := ra < 2 ^ 64 ∧ cell64 sp (BitVec.ofNat 64 ra) m

theorem frameSpec_spec : FrameSpec mach frameIsa Cond.reads framePreds where
  sp_disj := by decide
  scratch_disj := by decide
  cs_disj := by decide
  ra_disj := by decide
  argRegs_nodup := by decide
  retRegs_nodup := by decide
  retAddr_region _ _ _ h := cell64_region8 h.2
  raReg_of_raRegs _ _ _ _ _ := trivial
  slots_le_frameSize _ := Nat.le_refl _
  spOk_frame _ _ _ := trivial
  spEntry_call _ _ _ := trivial
  labelAddr_eq {h k l} hk hlt := by
    change h.prog[k]? = some (Instr.label l) at hk
    change ∀ j < k, h.prog[j]? ≠ some (Instr.label l) at hlt
    show (h.prog.findIdx? (· == Instr.label l)).getD h.prog.length = k
    have hk' : k < h.prog.length := by
      rcases Nat.lt_or_ge k h.prog.length with hh | hh
      · exact hh
      · rw [List.getElem?_eq_none hh] at hk; cases hk
    rw [(List.findIdx?_eq_some_iff_getElem (xs := h.prog)).mpr ⟨hk', ?_, ?_⟩]
    · rfl
    · rw [List.getElem?_eq_getElem hk'] at hk
      simp only [Option.some.injEq] at hk
      simp [hk]
    · intro j hj
      have := hlt j hj
      rw [List.getElem?_eq_getElem (Nat.lt_trans hj hk')] at this
      simp only [ne_eq, Option.some.injEq] at this
      simpa using this
  label_spec hi hk := run_instr hi rfl hk
  prologue_spec {h k ns s ra G post} _ _ _ hm :=
    fallsTo_one rfl
      ⟨by
        show s.gpr 4 + -BitVec.ofNat 64 (8 * ns) = s.gpr 4 - BitVec.ofNat 64 (8 * ns)
        rw [BitVec.sub_eq_add_neg], hm⟩
      (frame_setGpr _ _ _ _ _ (by simp [frameIsa]) _ _)
  epilogue_spec {h k ns s ra G post} _ _ hm :=
    fallsTo_one rfl
      ⟨rfl, trivial, by
        show ((_ ⋆ region _ (8 * ns - 8 * ns)) ⋆ G) s.mem
        rw [Nat.sub_self, region_zero, sep_emp]; exact hm⟩
      (frame_setGpr _ _ _ _ _ (by simp [frameIsa]) _ _)
  slotSt_spec {h k i r s G post} _ _ hm :=
    fallsTo_one rfl
      (by
        show (cell64 _ (s.gpr r) ⋆ G)
          (storeMemG memOps s.mem i64 (s.gpr 4 + BitVec.ofNat 64 (8 * i)) ((s.gpr r).setWidth 64))
        rw [storeMemG_memOps, BitVec.setWidth_eq]
        exact store_region8 _ hm)
      (frame_mem _ _ _ _ _ _)
  slotLd_spec {h k i rd v s G post} _ _ hm := by
    have hl : loadVal s.mem i64 (s.gpr 4 + BitVec.ofNat 64 (8 * i)) = some v := loadVal_cell64 hm
    refine fallsTo_one (s' := s.setGpr rd v) ?_ ⟨?_, rfl⟩ (frame_setGpr _ _ _ _ _ (by simp [frameIsa]) _ _)
    · show (loadValG memOps s.mem i64 (s.gpr 4 + BitVec.ofNat 64 (8 * i))).map _ = _
      rw [loadValG_memOps, hl]
      simp [valToGpr]
    · show (if rd = rd then v else s.gpr rd) = v
      simp
  canonAbi_spec {h k t r v s post} ht _ hg := by
    rcases ht with rfl | ⟨n, hn, rfl⟩
    · refine fallsTo_one rfl ?_ (frame_setGpr _ _ _ _ _ (by simp [frameIsa]) _ _)
      refine ⟨?_, rfl⟩
      show (if r = r then _ else _) = _
      simp only [ite_true]
      change (s.gpr r).setWidth 8 = BitVec.ofNat 8 v.toNat at hg
      rw [hg]; cases v <;> rfl
    · have hn' : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 := by simpa [frameIsa] using hn
      obtain ⟨hle, hv⟩ := hg
      change (s.gpr r).setWidth n = v at hv
      rcases hn' with rfl | rfl | rfl | rfl
      all_goals first
        | (refine fallsTo_one rfl ⟨⟨by decide, ?_⟩, rfl⟩ (frame_setGpr _ _ _ _ _ (by simp [frameIsa]) _ _)
           show (if r = r then _ else _) = _
           simp only [ite_true, ← hv])
        | (refine Machine.FallsTo.nil ⟨⟨by decide, ?_⟩, rfl⟩
           show s.gpr r = _
           rw [← hv, BitVec.setWidth_eq, BitVec.setWidth_eq])
  call_spec {h k sym s G post} hc hm hk := by
    have hi : h.prog[k]? = some (Instr.call sym) := List.isInfixAt_singleton.mp hc
    have hk' : k < h.prog.length := by
      rcases Nat.lt_or_ge k h.prog.length with hh | hh
      · exact hh
      · rw [List.getElem?_eq_none hh] at hi; cases hi
    have hlt : k + 1 < 2 ^ 64 := Nat.lt_of_le_of_lt hk' h.len_lt
    refine step_cps _ _ _ ⟨_, exec_fetch s hi, ?_⟩
    refine hk _ rfl (frame_setGpr _ _ _ _ _ (by simp [frameIsa]) _ _) trivial ?_
    show ((fun m => k + 1 < 2 ^ 64 ∧ cell64 (s.gpr 4 - 8) (BitVec.ofNat 64 (k + 1)) m) ⋆ G)
      (storeMemG memOps s.mem i64 (s.gpr 4 - 8) (BitVec.ofNat 64 (k + 1)))
    rw [sep_pure_l, storeMemG_memOps]
    exact ⟨hlt, store_region8 _ hm⟩
  exitJmp_spec {h k sym s post} hc hk := by
    have hi : h.prog[k]? = some (Instr.jmp sym) := List.isInfixAt_singleton.mp hc
    exact step_cps _ _ _ ⟨_, exec_fetch s hi, hk s (Machine.Frame.refl _ _ _ _ _) rfl⟩
  ret_spec {h k s ra R post} hc _ hm hk := by
    have hi : h.prog[k]? = some Instr.ret := List.isInfixAt_singleton.mp hc
    obtain ⟨hlt, hm⟩ := sep_pure_l.mp hm
    have hl : loadVal s.mem i64 (s.gpr 4) = some (BitVec.ofNat 64 ra) := loadVal_cell64 hm
    refine step_cps _ _ _ ⟨(s.setGpr 4 (s.gpr 4 + 8), ra), ?_, ?_⟩
    · refine (exec_fetch s hi).trans ?_
      show (loadValG memOps s.mem i64 (s.gpr 4)).map _ = _
      have e : (BitVec.ofNat 64 ra).toNat = ra :=
        (BitVec.toNat_ofNat (w := 64) (x := (ra : Nat))).trans (Nat.mod_eq_of_lt hlt)
      rw [loadValG_memOps, hl, Option.map_some, e]
    · exact hk _ (frame_setGpr Cond.reads _ _ _ _ (by simp [frameIsa]) [] 0).1 (fun _ _ => rfl) rfl rfl

def frameSpec : FrameTarget mach frameIsa Cond.reads where
  toFramePreds := framePreds
  spec := frameSpec_spec

open ProofUtil in
theorem storeWords_region (ws : List (BitVec 64)) :
    ∀ (a : BitVec 64) (m : Mem 64) (G : Mem 64 → Prop), 8 * ws.length ≤ 2 ^ 64 →
      (region a (8 * ws.length) ⋆ G) m → (array64 a ws ⋆ G) (storeWords memOps m a ws) := by
  induction ws with
  | nil =>
    intro a m G _ h
    simp only [List.length_nil, Nat.mul_zero, region_zero] at h
    exact h
  | cons w ws ih =>
    intro a m G hl h
    have e : 8 * (w :: ws).length = 8 + 8 * ws.length := by simp; omega
    rw [e, region_split (by omega), sep_assoc] at h
    have h2 := store_region8 w h
    have h3 : (region (a + BitVec.ofNat 64 8) (8 * ws.length) ⋆ (cell64 a w ⋆ G))
        (storeMem m i64 a w) := sep_ac h2
    have h4 := ih _ _ _ (by simp at hl; omega) h3
    show ((cell64 a w ⋆ array64 (a + BitVec.ofNat 64 8) ws) ⋆ G)
      (storeWords memOps (storeMemG memOps m i64 a w) (a + BitVec.ofNat 64 8) ws)
    rw [storeMemG_memOps]
    exact sep_ac h4

open ProofUtil in
theorem loadWords_array64 (ws : List (BitVec 64)) :
    ∀ (a : BitVec 64) (m : Mem 64) (G : Mem 64 → Prop),
      (array64 a ws ⋆ G) m → loadWords memOps m a ws.length = some ws := by
  induction ws with
  | nil => intro _ _ _ _; rfl
  | cons w ws ih =>
    intro a m G h
    have h1 : (cell64 a w ⋆ (array64 (a + 8) ws ⋆ G)) m := by
      rw [array64_cons, sep_assoc] at h; exact h
    have hl := loadVal_cell64 h1
    have h2 : (array64 (a + 8) ws ⋆ (cell64 a w ⋆ G)) m := sep_ac h1
    show (loadValG memOps m i64 a).bind
      (fun w => (loadWords memOps m (a + 8) ws.length).map (w :: ·)) = some (w :: ws)
    rw [loadValG_memOps, hl, Option.bind_some, ih _ _ _ h2, Option.map_some]

theorem getLsbD_packWords (ws : List (BitVec 64)) :
    ∀ i, i < 512 → (packWords ws).getLsbD i = (ws.getD (i / 64) 0).getLsbD (i % 64) := by
  induction ws with
  | nil => intro i _; simp [packWords]
  | cons w ws ih =>
    intro i hi
    simp only [packWords, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    rcases Nat.lt_or_ge i 64 with h | h
    · rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, List.getD_cons_zero]
      simp [h, hi]
    · have e1 : i / 64 = (i - 64) / 64 + 1 := by omega
      have e2 : i % 64 = (i - 64) % 64 := by omega
      rw [e1, e2, List.getD_cons_succ, ← ih (i - 64) (by omega)]
      simp [hi, show ¬ i < 64 by omega, BitVec.getLsbD_of_ge w i (by omega)]

theorem unpackSlotWords_getD (w : SlotWidth) (bv : BitVec 512) (j : Nat) (hj : j < w.slots) :
    (unpackSlotWords w bv).getD j 0 = bv.extractLsb' (64 * j) 64 := by
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by
    have := w.slots_le_eight; omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases w <;> first | rfl | exact absurd hj (by decide)

theorem packWords_unpackSlotWords (w : SlotWidth) (bv : BitVec 512) :
    (packWords (unpackSlotWords w bv)).setWidth w.bits = bv.setWidth w.bits := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb := SlotWidth.bits_eq_64_mul_slots w
  have := w.slots_le_eight
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth, getLsbD_packWords _ _ (by omega),
    unpackSlotWords_getD w bv (i / 64) (by omega), BitVec.getLsbD_extractLsb',
    Nat.div_add_mod]
  simp [Nat.mod_lt]

theorem vbin_spec (kk : BinK) (f : ∀ {n}, BitVec n → BitVec n → BitVec n) (g : Bool → Bool → Bool)
    (hk : ∀ t x y, vbinVal kk t x y =
      (toBits t (lift2 f g t (ofBits t (x.setWidth t.size)) (ofBits t (y.setWidth t.size)))).setWidth 512)
    {t : Ty} {a b d : Nat} {h : LHost} {k : Nat} {c : List Instr} {clob : FlagMask}
    {va vb : Val t} {P : Tup Val [t] → Prop} {s : MData} {post : mach.State → Prop}
    (hop : vbinArm kk t d a b = some (c, clob))
    (ha : VecHolds (s.vec a) t va) (hb : VecHolds (s.vec b) t vb) (hP : P (lift2 f g t va vb, ())) :
    mach.FallsTo Cond.reads h k c ([] ++ [11]) ([d] ++ [15]) clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (mach.PDstHolds s') (PDst.vec d, ()) rvs) ∧
        mach.mem s' = mach.mem s) post := by
  unfold vbinArm at hop
  split at hop
  · cases hop
    refine fallsTo_one rfl ⟨⟨_, hP, .cons ?_ .nil⟩, rfl⟩ (frame_setVec _ _ _ _ _ _ (by simp) _)
    show VecHolds (if d = d then _ else _) t _
    simp only [ite_true, hk, ha.2, hb.2, ofBits_toBits]
    exact ⟨ha.1, by rw [BitVec.setWidth_setWidth_of_le _ ha.1, BitVec.setWidth_eq]⟩
  · cases hop

theorem wp_bin {t : Ty} {P : Prop} (hw : (if t.hasFloat then False else P)) : P := by
  split at hw
  · exact hw.elim
  · exact hw

theorem vecSpec : VecTarget mach vecIsa Cond.reads frameIsa.sp frameIsa.scratch (fun _ => True) where
  vecScratch_disj := by decide
  vecArgRegs_nodup := by decide
  vecRetRegs_nodup := by decide
  abiVec_slot _ h := h
  vmov_spec {h k w vd vs s post} :=
    fallsTo_one rfl
      ⟨by show BitVec.setWidth _ (if vd = vd then s.vec vs else s.vec vd) = _; simp; rfl, rfl⟩
      (frame_setVec _ _ _ _ _ _ (by simp) _)
  vmovi_spec {h k w vd c code s post} hc _ := by
    cases hc
    exact fallsTo_one rfl
      ⟨by show BitVec.setWidth _ (if vd = vd then c else s.vec vd) = _; simp, rfl⟩
      (frame_setVec _ _ _ _ _ _ (by simp) _)
  vslotSt_spec {h k w i vr s G post} _ _ hm := by
    have hl := unpackSlotWords_length w (mach.getVec s vr)
    have hm' : (region (mach.getGpr s frameIsa.sp + BitVec.ofNat 64 (8 * i))
        (8 * (unpackSlotWords w (mach.getVec s vr)).length) ⋆ G) (mach.mem s) := by
      rw [hl]; exact hm
    exact fallsTo_one rfl
      (storeWords_region _ _ _ _ (by rw [hl]; have := w.slots_le_eight; omega) hm')
      (frame_mem _ _ _ _ _ _)
  vslotLd_spec {h k w i vd bv s G post} _ _ hm := by
    have hl := unpackSlotWords_length w bv
    have hw : loadWords memOps s.mem (s.gpr 4 + BitVec.ofNat 64 (8 * i)) w.slots =
        some (unpackSlotWords w bv) := hl ▸ loadWords_array64 _ _ _ _ hm
    refine fallsTo_one (s' := s.setVec vd (packWords (unpackSlotWords w bv))) ?_ ⟨?_, rfl⟩
      (frame_setVec _ _ _ _ _ _ (by simp) _)
    · show Option.map _ (loadWords memOps s.mem (s.gpr 4 + BitVec.ofNat 64 (8 * i)) w.slots) = _
      rw [hw]; rfl
    · show BitVec.setWidth _ (if vd = vd then packWords (unpackSlotWords w bv) else s.vec vd) = _
      simp only [ite_true]
      exact packWords_unpackSlotWords w bv
  vop_spec {h k sig rs code pas dsts vh c clob vs P s post} hop _ _ _ _ hargs hwp := by
    unfold vecIsa at hop
    simp only at hop
    unfold vop at hop
    split at hop
    all_goals first
      | (cases hop; done)
      | (obtain ⟨_, _, ⟨⟩⟩ := vs
         cases hargs with
         | cons ha hr =>
           cases hr with
           | cons hb _ =>
             first
               | exact vbin_spec .add (· + ·) (· ^^ ·) (fun _ _ _ => rfl) hop ha hb (wp_bin hwp)
               | exact vbin_spec .sub (· - ·) (· ^^ ·) (fun _ _ _ => rfl) hop ha hb (wp_bin hwp)
               | exact vbin_spec .and (· &&& ·) (· && ·) (fun _ _ _ => rfl) hop ha hb hwp
               | exact vbin_spec .or (· ||| ·) (· || ·) (fun _ _ _ => rfl) hop ha hb hwp
               | exact vbin_spec .xor (· ^^^ ·) (· ^^ ·) (fun _ _ _ => rfl) hop ha hb hwp)
  vload_spec h := by cases h
  vstore_spec h := by cases h


end FrameVec

/-! ## 6. `GprTarget` -/

namespace GprPf

theorem disj_all (c : Cond) : FlagMask.disjoint c.reads FlagMask.all = false := by
  cases c <;> decide

theorem upd_all (s s' : MData) : mach.UpdFlags Cond.reads s s' FlagMask.all := fun c hc => by
  rw [disj_all] at hc; cases hc

/-- Flag-frame from explicit flag equalities (any mask). -/
theorem upd_eq {s s' : MData} {f : FlagMask} (hc : s'.cf = s.cf) (hz : s'.zf = s.zf)
    (ho : s'.of = s.of) : mach.UpdFlags Cond.reads s s' f := fun c _ => by
  show s'.evalCond c = s.evalCond c
  cases c <;> simp [MDataG.evalCond, hc, hz, ho]

theorem upd_decInc {s s' : MData} (hc : s'.cf = s.cf) :
    mach.UpdFlags Cond.reads s s' maskDecInc := fun c h => by
  show s'.evalCond c = s.evalCond c
  cases c <;> first | exact absurd h (by decide) | simp [MDataG.evalCond, hc]

theorem upd_cf {s s' : MData} (hz : s'.zf = s.zf) (ho : s'.of = s.of) :
    mach.UpdFlags Cond.reads s s' maskCF := fun c h => by
  show s'.evalCond c = s.evalCond c
  cases c <;> first | exact absurd h (by decide) | simp [MDataG.evalCond, hz, ho]

theorem upd_of {s s' : MData} (hc : s'.cf = s.cf) (hz : s'.zf = s.zf) :
    mach.UpdFlags Cond.reads s s' maskOF := fun c h => by
  show s'.evalCond c = s.evalCond c
  cases c <;> first | exact absurd h (by decide) | simp [MDataG.evalCond, hc, hz]

theorem frame_mk {s s' : MData} {g : List Nat} {f : FlagMask}
    (hg : ∀ r, r ∉ g → s'.gpr r = s.gpr r) (hv : s'.vec = s.vec)
    (hf : mach.UpdFlags Cond.reads s s' f) : mach.Frame Cond.reads s s' g [] f :=
  ⟨hg, fun v _ => congrFun hv v, hf⟩

@[simp] theorem mach_getGpr (s : MData) (r : Nat) : mach.getGpr s r = s.gpr r := rfl
@[simp] theorem mach_evalCond (s : MData) (c : Cond) : mach.evalCond s c = s.evalCond c := rfl
@[simp] theorem mach_mem (s : MData) : mach.mem s = s.mem := rfl
@[simp] theorem setGpr_gpr {M : Type} (s : MDataG M) (r x : Nat) (v : BitVec 64) :
    (s.setGpr r v).gpr x = if x = r then v else s.gpr x := rfl
@[simp] theorem setGpr_vec {M : Type} (s : MDataG M) (r : Nat) (v : BitVec 64) :
    (s.setGpr r v).vec = s.vec := rfl
@[simp] theorem setGpr_mem {M : Type} (s : MDataG M) (r : Nat) (v : BitVec 64) :
    (s.setGpr r v).mem = s.mem := rfl
@[simp] theorem setGpr_cf {M : Type} (s : MDataG M) (r : Nat) (v : BitVec 64) :
    (s.setGpr r v).cf = s.cf := rfl
@[simp] theorem setGpr_zf {M : Type} (s : MDataG M) (r : Nat) (v : BitVec 64) :
    (s.setGpr r v).zf = s.zf := rfl
@[simp] theorem setGpr_of {M : Type} (s : MDataG M) (r : Nat) (v : BitVec 64) :
    (s.setGpr r v).of = s.of := rfl

theorem keeps_setGpr {s : MData} {d : Nat} {v : BitVec 64} {g : List Nat} (hd : d ∈ g) :
    ∀ r, r ∉ g → (s.setGpr d v).gpr r = s.gpr r := by
  intro r hr; have : r ≠ d := fun h => hr (h ▸ hd); simp [this]

theorem setWidth_64_setWidth {n : Nat} (r : BitVec n) (hn : n ≤ 64) :
    (r.setWidth 64).setWidth n = r := by
  rw [BitVec.setWidth_setWidth_of_le _ hn, BitVec.setWidth_eq]

theorem gprHolds_setWidth {n : Nat} (r : BitVec n) (hn : n ≤ 64) :
    GprHolds (r.setWidth 64) (.bits n) r := ⟨hn, setWidth_64_setWidth r hn⟩

theorem gprHolds_bool (b : Bool) : GprHolds (BitVec.ofNat 64 b.toNat) .bool b := by
  cases b <;> rfl

theorem srcOf_spec {n : Nat} {pa : PArg Nat Nat Cond (.bits n)} {sa : Src} {v : BitVec n}
    {s : MData} (h : srcOf pa = some sa) (hv : mach.PArgHolds s (.bits n) pa v) (hn : n ≤ 64) :
    (s.src sa).setWidth n = v := by
  cases pa with
  | gpr r => simp only [srcOf, Option.some.injEq] at h; subst h; exact hv.2
  | imm c =>
    simp only [srcOf, Option.some.injEq] at h; subst h
    have hv' : c = v := hv
    subst hv'; exact setWidth_64_setWidth c hn
  | vec _ => simp [srcOf] at h

theorem negCond_reads (c : Cond) : Cond.reads (Cond.neg c) = Cond.reads c := by cases c <;> rfl
theorem negCond_eval (s : MData) (c : Cond) : s.evalCond c.neg = !s.evalCond c := by
  cases c <;> simp [Cond.neg, MDataG.evalCond]

theorem bool_of_setWidth8 {x : BitVec 64} {b : Bool} (h : x.setWidth 8 = BitVec.ofNat 8 b.toNat) :
    x.getLsbD 0 = b := by
  have := congrArg (fun y : BitVec 8 => y.getLsbD 0) h
  cases b <;> simpa using this

theorem ne0_of_setWidth8 {x : BitVec 64} {b : Bool} (h : x.setWidth 8 = BitVec.ofNat 8 b.toNat) :
    (!(x.setWidth 8 == 0#8)) = b := by
  rw [h]; cases b <;> decide

theorem isGprTy_bits {n : Nat} (h : isGprTy (.bits n) = true) : n ≤ 64 := by
  simp [isGprTy] at h; omega

theorem addr_eval (s : MData) (a : AddrArg Nat) : s.addr (addrOf a) = a.eval s.gpr := by
  cases a <;> rfl

theorem gprHolds_valToGpr {t : Ty} (ht : isGprTy t = true) (v : Val t) :
    GprHolds (valToGpr t v) t v := by
  cases t with
  | bool => exact gprHolds_bool v
  | bits n => exact gprHolds_setWidth v (isGprTy_bits ht)
  | float _ => cases ht
  | pair _ _ => cases ht

theorem gprToVal_of_holds {t : Ty} (ht : isGprTy t = true) {x : BitVec 64} {v : Val t}
    (h : GprHolds x t v) : gprToVal t x = v := by
  cases t with
  | bool => exact bool_of_setWidth8 h
  | bits n => exact h.2
  | float _ => cases ht
  | pair _ _ => cases ht

theorem jmp_spec {h : LHost} {k j : Nat} {l : String} {s : MData} {post : mach.State → Prop}
    (hc : (gprIsa.jmp l).IsInfixAt (mach.prog h) k) (hl : mach.labelAddr h l = mach.addrOf h j)
    (hk : ∀ s', mach.Frame gprIsa.condReads s s' frameIsa.scratch [] FlagMask.none →
      mach.mem s' = mach.mem s → mach.Run h j s' post) : mach.Run h k s post := by
  have hl' : labelAddr h l = j := hl
  refine run_instr (List.isInfixAt_singleton.mp hc) (k' := j) (s' := s) (by simp [execI, hl']) ?_
  exact hk s (Machine.Frame.refl _ _ _ _ _) rfl

theorem jcc_spec {h : LHost} {k j : Nat} {c : Cond} {l : String} {s : MData}
    {post : mach.State → Prop}
    (hc : (gprIsa.jcc c l).IsInfixAt (mach.prog h) k) (hl : mach.labelAddr h l = mach.addrOf h j)
    (hk : ∀ s', mach.Frame gprIsa.condReads s s' frameIsa.scratch [] FlagMask.none →
      mach.mem s' = mach.mem s →
      (mach.evalCond s c = true → mach.Run h j s' post) ∧
      (mach.evalCond s c = false → mach.Run h (k + (gprIsa.jcc c l).length) s' post)) :
    mach.Run h k s post := by
  have hl' : labelAddr h l = j := hl
  have hk' := hk s (Machine.Frame.refl _ _ _ _ _) rfl
  cases he : s.evalCond c
  · exact run_instr (List.isInfixAt_singleton.mp hc) (k' := k + 1) (s' := s)
      (by simp [execI, he]) (hk'.2 he)
  · exact run_instr (List.isInfixAt_singleton.mp hc) (k' := j) (s' := s)
      (by simp [execI, he, hl']) (hk'.1 he)

theorem jnzGpr_spec {h : LHost} {k j r : Nat} {l : String} {b : Bool} {s : MData}
    {post : mach.State → Prop}
    (hc : (gprIsa.jnzGpr r l).1.IsInfixAt (mach.prog h) k) (hl : mach.labelAddr h l = mach.addrOf h j)
    (hb : GprHolds (mach.getGpr s r) .bool b)
    (hk : ∀ s', mach.Frame gprIsa.condReads s s' frameIsa.scratch [] (gprIsa.jnzGpr r l).2 →
      mach.mem s' = mach.mem s →
      (b = true → mach.Run h j s' post) ∧
      (b = false → mach.Run h (k + (gprIsa.jnzGpr r l).1.length) s' post)) :
    mach.Run h k s post := by
  have hl' : labelAddr h l = j := hl
  obtain ⟨h1, hc2⟩ := hc.cons
  obtain ⟨h2, -⟩ := hc2.cons
  let s₁ : MData := { s with cf := false, zf := (s.gpr r).setWidth 8 == 0, of := false }
  have hk' := hk s₁ (frame_mk (fun _ _ => rfl) rfl (upd_all _ _)) rfl
  have hz : s₁.evalCond .nzf = b := ne0_of_setWidth8 hb
  refine run_instr h1 (k' := k + 1) (s' := s₁) rfl ?_
  cases b
  · exact run_instr h2 (k' := k + 1 + 1) (s' := s₁) (by simp [execI, hz]) (hk'.2 rfl)
  · exact run_instr h2 (k' := j) (s' := s₁) (by simp [execI, hz, hl']) (hk'.1 rfl)

theorem load_spec {h : LHost} {k : Nat} {t : Ty} {rd : Nat} {a : AddrArg Nat} {c : List Instr}
    {clob : FlagMask} {v : Val t} {s : MData} {post : mach.State → Prop}
    (hop : gprIsa.load t rd a = some (c, clob))
    (hl : loadVal (mach.mem s) t (a.eval (mach.getGpr s)) = some v) :
    mach.FallsTo gprIsa.condReads h k c (rd :: frameIsa.scratch) [] clob s
      (fun s' => GprHolds (mach.getGpr s' rd) t v ∧ mach.mem s' = mach.mem s) post := by
  simp only [gprIsa, gprLoad] at hop
  split at hop
  · next ht =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    have hl' : loadVal s.mem t (s.addr (addrOf a)) = some v := by rw [addr_eval]; exact hl
    refine fallsTo_one (s' := s.setGpr rd (valToGpr t v)) (by simp [execI, hl']) ⟨?_, rfl⟩
      (frame_mk (keeps_setGpr (by simp)) rfl (upd_eq rfl rfl rfl))
    show GprHolds ((s.setGpr rd _).gpr rd) t v
    simpa using gprHolds_valToGpr ht v
  · cases hop

theorem store_spec {h : LHost} {k : Nat} {t : Ty} {pa : PArg Nat Nat Cond t} {a : AddrArg Nat}
    {c : List Instr} {clob : FlagMask} {v : Val t} {s : MData} {post : mach.State → Prop}
    (hop : gprIsa.store t pa a = some (c, clob)) (hv : mach.PArgHolds s t pa v) :
    mach.FallsTo gprIsa.condReads h k c frameIsa.scratch [] clob s
      (fun s' => mach.mem s' = storeMem (mach.mem s) t (a.eval (mach.getGpr s)) v) post := by
  simp only [gprIsa, gprStore] at hop
  split at hop
  · cases hop
  · next ht =>
    simp only [Bool.not_eq_true', Bool.not_eq_false] at ht
    have key : ∀ sv : Src, gprToVal t (s.src sv) = v →
        [Instr.st t sv (addrOf a)] = c → (0#8 : FlagMask) = clob →
        mach.FallsTo gprIsa.condReads h k c frameIsa.scratch [] clob s
          (fun s' => mach.mem s' = storeMem (mach.mem s) t (a.eval (mach.getGpr s)) v) post := by
      rintro sv hsv rfl rfl
      refine fallsTo_one (s' := { s with mem := storeMem s.mem t (s.addr (addrOf a)) v })
        (by simp [execI, hsv]) ?_ (frame_mk (fun _ _ => rfl) rfl (upd_eq rfl rfl rfl))
      show storeMem s.mem t (s.addr (addrOf a)) v = _
      rw [addr_eval]; rfl
    split at hop <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hop
    · exact key (.reg _) (gprToVal_of_holds ht hv) hop.1 hop.2
    · next c0 =>
      refine key _ ?_ hop.1 hop.2
      have hv' : c0 = v := hv
      subst hv'
      cases t with
      | bool => cases c0 <;> first | decide | simp [gprToVal, valToGpr, MDataG.src]
      | bits n => exact setWidth_64_setWidth c0 (isGprTy_bits ht)
      | float _ => cases ht
      | pair _ _ => cases ht

/-- `c` runs from `(s, k)` to `s'`, each instruction falling through. -/
def Steps (h : LHost) : List Instr → Nat → MData → MData → Prop
  | [], _, s, s' => s' = s
  | i :: is, k, s, s' => ∃ s₁, execI memOps h s k i = some (s₁, k + 1) ∧ Steps h is (k + 1) s₁ s'

theorem run_steps {h : LHost} {c : List Instr} {k : Nat} {s s' : MData} {post : mach.State → Prop}
    (hs : Steps h c k s s') (hc : c.IsInfixAt (mach.prog h) k)
    (hr : mach.Run h (k + c.length) s' post) : mach.Run h k s post := by
  induction c generalizing k s with
  | nil => cases hs; simpa using hr
  | cons i is ih =>
    obtain ⟨s₁, he, hs⟩ := hs
    obtain ⟨hi, hc'⟩ := hc.cons
    exact run_instr hi he (ih hs hc' (by simpa [Nat.add_assoc, Nat.add_comm 1] using hr))

theorem fallsTo_steps {cr : Cond → FlagMask} {h : LHost} {c : List Instr} {k : Nat} {g : List Nat}
    {f : FlagMask} {s s' : MData} {Q : MData → Prop} {post : mach.State → Prop}
    (hs : Steps h c k s s') (hq : Q s') (hfr : mach.Frame cr s s' g [] f) :
    mach.FallsTo cr h k c g [] f s Q post := fun hc hk => run_steps hs hc (hk s' hq hfr)

theorem steps_append {h : LHost} {c₁ c₂ : List Instr} {k : Nat} {s s₁ s₂ : MData}
    (h₁ : Steps h c₁ k s s₁) (h₂ : Steps h c₂ (k + c₁.length) s₁ s₂) :
    Steps h (c₁ ++ c₂) k s s₂ := by
  induction c₁ generalizing k s with
  | nil => cases h₁; simpa using h₂
  | cons i is ih =>
    obtain ⟨s', he, hs⟩ := h₁
    exact ⟨s', he, ih hs (by simpa [Nat.add_assoc, Nat.add_comm 1] using h₂)⟩

abbrev OpQ {rs : List Ty} (s : MData) (dsts : Tup (PDst Nat Nat Cond) rs) (P : Tup Val rs → Prop)
    (s' : MData) : Prop :=
  (∃ rvs, P rvs ∧ TRel (mach.PDstHolds s') dsts rvs) ∧ mach.mem s' = mach.mem s

theorem mem_hd {d : Nat} {l g : List Nat} : d ∈ (d :: l) ++ g := by simp

theorem keeps_one {s s' : MData} {d : Nat} {g : List Nat} (hd : d ∈ g)
    (h : ∀ r, r ≠ d → s'.gpr r = s.gpr r) : ∀ r, r ∉ g → s'.gpr r = s.gpr r :=
  fun r hr => h r fun e => hr (e ▸ hd)

theorem dst_bits {s' : MData} {n d : Nat} {r : BitVec n} (hn : n ≤ 64)
    (hd : s'.gpr d = r.setWidth 64) : mach.PDstHolds s' (.bits n) (.gpr d) r := by
  show GprHolds (s'.gpr d) (.bits n) r
  rw [hd]; exact gprHolds_setWidth r hn

theorem dst_bool_setcc {s' : MData} {d : Nat} {b : Bool}
    (hd : s'.gpr d = BitVec.ofNat 64 b.toNat) : mach.PDstHolds s' .bool (.gpr d) b := by
  show GprHolds (s'.gpr d) .bool b
  rw [hd]; exact gprHolds_bool b

theorem dst_bool_gpr {s' : MData} {d : Nat} {x : BitVec 8} {b : Bool}
    (hd : s'.gpr d = x.setWidth 64) (hx : x = BitVec.ofNat 8 b.toNat) :
    mach.PDstHolds s' .bool (.gpr d) b := by
  show (s'.gpr d).setWidth 8 = _
  rw [hd, setWidth_64_setWidth _ (by decide), hx]

theorem dst_flag {s' : MData} {c : Cond} {b : Bool} (h : s'.evalCond c = b) :
    mach.PDstHolds s' .bool (.flag c) b := h

theorem srcOfBool_spec {pa : PArg Nat Nat Cond .bool} {sa : Src} {b : Bool} {s : MData}
    (h : srcOfBool pa = some sa) (hv : mach.PArgHolds s .bool pa b) :
    (s.src sa).setWidth 8 = BitVec.ofNat 8 b.toNat := by
  cases pa with
  | gpr r => simp only [srcOfBool, Option.some.injEq] at h; subst h; exact hv
  | imm b0 =>
    simp only [srcOfBool, Option.some.injEq] at h; subst h
    have hv' : b0 = b := hv
    subst hv'; cases b0 <;> rfl
  | vec _ => simp [srcOfBool] at h
  | flag _ => simp [srcOfBool] at h

theorem trel2 {R : ∀ t, PArg Nat Nat Cond t → Val t → Prop} {t u : Ty} {a : PArg Nat Nat Cond t}
    {b : PArg Nat Nat Cond u} {x : Val t} {y : Val u}
    (h : TRel R (as := [t, u]) (a, b, ()) (x, y, ())) : R t a x ∧ R u b y := by
  cases h with | cons h1 h2 => cases h2 with | cons h3 _ => exact ⟨h1, h3⟩

theorem trel3 {R : ∀ t, PArg Nat Nat Cond t → Val t → Prop} {t u w : Ty} {a : PArg Nat Nat Cond t}
    {b : PArg Nat Nat Cond u} {c : PArg Nat Nat Cond w} {x : Val t} {y : Val u} {z : Val w}
    (h : TRel R (as := [t, u, w]) (a, b, c, ()) (x, y, z, ())) : R t a x ∧ R u b y ∧ R w c z := by
  cases h with
  | cons h1 h2 => cases h2 with | cons h3 h4 => cases h4 with | cons h5 _ => exact ⟨h1, h3, h5⟩

theorem binArm_spec {h : LHost} {k : Nat} {kk : BinK} {n d : Nat} {a b : PArg Nat Nat Cond (.bits n)}
    {c : List Instr} {clob : FlagMask} {va vb : BitVec n} {s : MData}
    {P : Tup Val [.bits n] → Prop} {post : mach.State → Prop}
    (hop : binArm kk n d a b = some (c, clob)) (ha : mach.PArgHolds s (.bits n) a va)
    (hb : mach.PArgHolds s (.bits n) b vb) (hP : P (binEval kk va vb, ())) :
    mach.FallsTo Cond.reads h k c ([d] ++ frameIsa.scratch) [] clob s
      (OpQ s (PDst.gpr d, ()) P) post := by
  unfold binArm at hop
  split at hop
  · next hn' =>
    have hn := Nat.le_of_ble_eq_true hn'
    obtain ⟨sa, hsa, hop⟩ := Option.bind_eq_some_iff.mp hop
    obtain ⟨sb, hsb, hop⟩ := Option.map_eq_some_iff.mp hop
    cases hop
    have ea := srcOf_spec hsa ha hn
    have eb := srcOf_spec hsb hb hn
    subst ea eb
    refine fallsTo_steps ⟨_, rfl, rfl⟩ ⟨⟨(_, ()), hP, .cons (dst_bits hn ?_) .nil⟩, rfl⟩
      (frame_mk (keeps_one (d := d) mem_hd (by intro r hr; simp [hr])) rfl (upd_all _ _))
    simp
  · cases hop

theorem addArm_spec {h : LHost} {k : Nat} {n d : Nat} {a b : PArg Nat Nat Cond (.bits n)}
    {vh : VariantHint} {c : List Instr} {clob : FlagMask} {va vb : BitVec n} {s : MData}
    {P : Tup Val [.bits n] → Prop} {post : mach.State → Prop}
    (hop : addArm n d a b vh = some (c, clob)) (ha : mach.PArgHolds s (.bits n) a va)
    (hb : mach.PArgHolds s (.bits n) b vb) (hP : P (va + vb, ())) :
    mach.FallsTo Cond.reads h k c ([d] ++ frameIsa.scratch) [] clob s
      (OpQ s (PDst.gpr d, ()) P) post := by
  unfold addArm at hop
  split at hop
  · next ra c0 =>
    split at hop
    · next hn =>
      have hn := Nat.eq_of_beq_eq_true hn
      subst hn
      cases hop
      have ea : s.gpr ra = va := (BitVec.setWidth_eq _).symm.trans ha.2
      have eb : c0 = vb := hb
      subst ea eb
      refine fallsTo_steps ⟨_, rfl, rfl⟩ ⟨⟨(_, ()), hP, .cons (dst_bits (Nat.le_refl _) ?_) .nil⟩, rfl⟩
        (frame_mk (keeps_one (d := d) mem_hd (by intro r hr; simp [hr])) rfl (upd_eq rfl rfl rfl))
      simp
    · cases hop
  · exact binArm_spec hop ha hb hP

theorem subArm_spec {h : LHost} {k : Nat} {n d : Nat} {a b : PArg Nat Nat Cond (.bits n)}
    {vh : VariantHint} {c : List Instr} {clob : FlagMask} {va vb : BitVec n} {s : MData}
    {P : Tup Val [.bits n] → Prop} {post : mach.State → Prop}
    (hop : subArm n d a b vh = some (c, clob)) (ha : mach.PArgHolds s (.bits n) a va)
    (hb : mach.PArgHolds s (.bits n) b vb) (hP : P (va - vb, ())) :
    mach.FallsTo Cond.reads h k c ([d] ++ frameIsa.scratch) [] clob s
      (OpQ s (PDst.gpr d, ()) P) post := by
  unfold subArm at hop
  split at hop
  · next c0 =>
    split at hop
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hn', rfl⟩ := hc
      have hn := Nat.le_of_ble_eq_true hn'
      obtain ⟨sa, hsa, hop⟩ := Option.map_eq_some_iff.mp hop
      cases hop
      have ea := srcOf_spec hsa ha hn
      have eb : 1#n = vb := hb
      subst ea eb
      refine fallsTo_steps ⟨_, rfl, rfl⟩ ⟨⟨(_, ()), hP, .cons (dst_bits hn ?_) .nil⟩, rfl⟩
        (frame_mk (keeps_one (d := d) mem_hd (by intro r hr; simp [hr])) rfl (upd_decInc rfl))
      simp
    · cases hop
  · exact binArm_spec hop ha hb hP

theorem boolArm_spec {h : LHost} {k : Nat} {kk : BinK} {gb : Bool → Bool → Bool} {d : Nat}
    {a b : PArg Nat Nat Cond .bool} {c : List Instr} {clob : FlagMask} {va vb : Bool} {s : MData}
    {P : Tup Val [.bool] → Prop} {post : mach.State → Prop}
    (hk : ∀ x y : Bool, binEval kk (BitVec.ofNat 8 x.toNat) (BitVec.ofNat 8 y.toNat) =
      BitVec.ofNat 8 (gb x y).toNat)
    (hop : boolArm kk d a b = some (c, clob)) (ha : mach.PArgHolds s .bool a va)
    (hb : mach.PArgHolds s .bool b vb) (hP : P (gb va vb, ())) :
    mach.FallsTo Cond.reads h k c ([d] ++ frameIsa.scratch) [] clob s
      (OpQ s (PDst.gpr d, ()) P) post := by
  unfold boolArm at hop
  obtain ⟨sa, hsa, hop⟩ := Option.bind_eq_some_iff.mp hop
  obtain ⟨sb, hsb, hop⟩ := Option.map_eq_some_iff.mp hop
  cases hop
  have ea := srcOfBool_spec hsa ha
  have eb := srcOfBool_spec hsb hb
  refine fallsTo_steps ⟨_, rfl, rfl⟩ ⟨⟨(_, ()), hP, .cons (dst_bool_gpr
    (x := binEval kk ((s.src sa).setWidth 8) ((s.src sb).setWidth 8)) ?_ ?_) .nil⟩, rfl⟩
    (frame_mk (keeps_one (d := d) mem_hd (by intro r hr; simp [hr])) rfl (upd_all _ _))
  · simp
  · rw [ea, eb, hk]

theorem beq_dec {n : Nat} (x y : BitVec n) : (x == y) = decide (x = y) :=
  Bool.eq_iff_iff.mpr (by simp)

@[simp] theorem src_mk_gpr {M : Type} (s : MDataG M) (v : Nat → BitVec 512) (c z o : Bool) (m : M)
    (sa : Src) : (MDataG.mk s.gpr v c z o m).src sa = s.src sa := by cases sa <;> rfl

theorem keeps_setGpr_of {s s₁ : MData} {d : Nat} {v : BitVec 64} {g : List Nat} (hd : d ∈ g)
    (h1 : ∀ r, r ∉ g → s₁.gpr r = s.gpr r) : ∀ r, r ∉ g → (s₁.setGpr d v).gpr r = s.gpr r := by
  intro r hr; have : r ≠ d := fun h => hr (h ▸ hd); simp [this, h1 r hr]

@[simp] theorem cmp_eval {o : CmpOp} {cc : Cond} (hcc : cmpCond o = some cc) (s : MData) {n : Nat}
    (x y : BitVec n) (o' : Bool) :
    ({ s with cf := x.ult y, zf := x == y, of := o' } : MData).evalCond cc = o.evalBits x y := by
  cases o <;> simp [cmpCond] at hcc <;> subst hcc <;> simp [MDataG.evalCond, CmpOp.evalBits, beq_dec]

theorem cmpArm_spec {h : LHost} {k : Nat} {o : CmpOp} {n : Nat} {a b : PArg Nat Nat Cond (.bits n)}
    {dst : PDst Nat Nat Cond .bool} {vh : VariantHint} {c : List Instr} {clob : FlagMask}
    {va vb : BitVec n} {s : MData} {P : Tup Val [.bool] → Prop} {post : mach.State → Prop}
    (hop : cmpArm o n a b dst vh = some (c, clob)) (ha : mach.PArgHolds s (.bits n) a va)
    (hb : mach.PArgHolds s (.bits n) b vb) (hP : P (o.evalBits va vb, ())) :
    mach.FallsTo Cond.reads h k c (tupDstGprs (ts := [.bool]) (dst, ()) ++ frameIsa.scratch) [] clob s
      (OpQ s (dst, ()) P) post := by
  unfold cmpArm at hop
  split at hop
  · cases hop
  next hn' =>
  have hn : n ≤ 64 := by simpa using hn'
  split at hop
  · next c0 =>
    split at hop
    · next hc0 =>
      have hc0 : c0 = 0#n := by simpa using hc0
      subst hc0
      obtain ⟨sa, hsa, hop⟩ := Option.map_eq_some_iff.mp hop
      cases hop
      have ea := srcOf_spec hsa ha hn
      have eb : 0#n = vb := hb
      subst ea eb
      refine fallsTo_steps ⟨_, rfl, rfl⟩ ⟨⟨(_, ()), hP, .cons (dst_flag ?_) .nil⟩, rfl⟩
        (frame_mk (fun _ _ => rfl) rfl (upd_decInc rfl))
      simp [MDataG.evalCond, CmpOp.evalBits, beq_dec]
    · cases hop
  · simp only [Option.bind_eq_some_iff] at hop
    obtain ⟨cc, hcc, sa, hsa, sb, hsb, hop⟩ := hop
    have ea := srcOf_spec hsa ha hn
    have eb := srcOf_spec hsb hb hn
    subst ea eb
    split at hop
    · split at hop
      · rename_i hc'
        simp only [beq_iff_eq] at hc'
        subst hc'
        cases hop
        refine fallsTo_steps ⟨_, rfl, rfl⟩ ⟨⟨(_, ()), hP, .cons (dst_flag ?_) .nil⟩, rfl⟩
          (frame_mk (fun _ _ => rfl) rfl (upd_all _ _))
        exact cmp_eval hcc _ _ _ _
      · cases hop
    · cases hop
      refine fallsTo_steps ⟨_, rfl, _, rfl, rfl⟩
        ⟨⟨(_, ()), hP, .cons (dst_bool_setcc ?_) .nil⟩, rfl⟩
        (frame_mk (keeps_setGpr_of mem_hd (fun _ _ => rfl)) rfl (upd_all _ _))
      simp [cmp_eval hcc]
    · cases hop

theorem addcArm_spec {h : LHost} {k : Nat} {n d : Nat} {a b : PArg Nat Nat Cond (.bits n)}
    {cin : PArg Nat Nat Cond .bool} {cout : PDst Nat Nat Cond .bool} {vh : VariantHint}
    {c : List Instr} {clob : FlagMask} {va vb : BitVec n} {vc : Bool} {s : MData}
    {P : Tup Val [.bits n, .bool] → Prop} {post : mach.State → Prop}
    (hop : addcArm n d a b cin cout vh = some (c, clob)) (ha : mach.PArgHolds s (.bits n) a va)
    (hb : mach.PArgHolds s (.bits n) b vb) (hc : mach.PArgHolds s .bool cin vc)
    (hP : P (va + vb + BitVec.ofNat n vc.toNat,
      decide (2 ^ n ≤ va.toNat + vb.toNat + vc.toNat), ())) :
    mach.FallsTo Cond.reads h k c
      (tupDstGprs (ts := [.bits n, .bool]) (PDst.gpr d, cout, ()) ++ frameIsa.scratch) [] clob s
      (OpQ s (PDst.gpr d, cout, ()) P) post := by
  unfold addcArm at hop
  split at hop
  · cases hop
  next hn' =>
  have hn : n ≤ 64 := by simpa using hn'
  obtain ⟨sa, hsa, hop⟩ := Option.bind_eq_some_iff.mp hop
  obtain ⟨sb, hsb, hop⟩ := Option.bind_eq_some_iff.mp hop
  have ea := srcOf_spec hsa ha hn
  have eb := srcOf_spec hsb hb hn
  subst ea eb
  split at hop
  · cases hop
    have ec : s.cf = vc := hc
    subst ec
    refine fallsTo_steps ⟨_, rfl, rfl⟩
      ⟨⟨(_, _, ()), hP, .cons (dst_bits hn ?_) (.cons (dst_flag rfl) .nil)⟩, rfl⟩
      (frame_mk (keeps_one (d := d) mem_hd (by intro r hr; simp [hr])) rfl (upd_cf rfl rfl))
    simp
  · cases hop
    have ec : s.of = vc := hc
    subst ec
    refine fallsTo_steps ⟨_, rfl, rfl⟩
      ⟨⟨(_, _, ()), hP, .cons (dst_bits hn ?_) (.cons (dst_flag rfl) .nil)⟩, rfl⟩
      (frame_mk (keeps_one (d := d) mem_hd (by intro r hr; simp [hr])) rfl (upd_of rfl rfl))
    simp
  · obtain ⟨m, hm, hop⟩ := Option.bind_eq_some_iff.mp hop
    obtain ⟨p, hp, hop⟩ := Option.map_eq_some_iff.mp hop
    cases hop
    have hmain : ∃ s₁, Steps h m k s s₁ ∧
        s₁.gpr d = ((s.src sa).setWidth n + (s.src sb).setWidth n +
          BitVec.ofNat n vc.toNat).setWidth 64 ∧
        s₁.cf = decide (2 ^ n ≤ ((s.src sa).setWidth n).toNat + ((s.src sb).setWidth n).toNat +
          vc.toNat) ∧
        (∀ r, r ≠ d → s₁.gpr r = s.gpr r) ∧ s₁.vec = s.vec ∧ s₁.mem = s.mem := by
      split at hm <;> simp only [Option.some.injEq, reduceCtorEq] at hm <;> subst hm
      · have ec : s.cf = vc := hc
        subst ec
        exact ⟨_, ⟨_, rfl, rfl⟩, by simp, rfl, by intro r hr; simp [hr], rfl, rfl⟩
      · have ec : false = vc := hc
        subst ec
        exact ⟨_, ⟨_, rfl, rfl⟩, by simp [binEval], by simp [binCF], by intro r hr; simp [hr], rfl, rfl⟩
      · have ec := bool_of_setWidth8 hc
        subst ec
        exact ⟨_, ⟨_, rfl, _, rfl, rfl⟩, by simp, by simp, by intro r hr; simp [hr], rfl, rfl⟩
    obtain ⟨s₁, hs₁, h1d, h1c, h1g, h1v, h1m⟩ := hmain
    split at hp
    · simp only [Option.some.injEq] at hp
      subst hp
      refine fallsTo_steps (steps_append hs₁ rfl)
        ⟨⟨(_, _, ()), hP, .cons (dst_bits hn h1d) (.cons (dst_flag (c := .cf) h1c) .nil)⟩, h1m⟩
        (frame_mk ?_ h1v (upd_all _ _))
      intro r hr; exact h1g r (by rintro rfl; simp [tupDstGprs] at hr)
    · split at hp
      · cases hp
      · rename_i hrd
        simp only [Option.some.injEq] at hp
        subst hp
        simp only [beq_iff_eq] at hrd
        refine fallsTo_steps (steps_append hs₁ ⟨_, rfl, rfl⟩)
          ⟨⟨(_, _, ()), hP, .cons (dst_bits hn ?_) (.cons (dst_bool_setcc ?_) .nil)⟩, h1m⟩
          (frame_mk ?_ (by simpa using h1v) (upd_all _ _))
        · simp [Ne.symm hrd, h1d]
        · simp [MDataG.evalCond, h1c]
        · intro r hr
          simp only [tupDstGprs_cons, tupDstGprs_nil, PDst.gprs, frameIsa, List.nil_append,
            List.cons_append, List.mem_cons, not_or] at hr
          simp [hr.2.1, h1g r hr.1]
    · cases hp
  · cases hop

theorem op_spec {h : LHost} {k : Nat} {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg Nat Nat Cond) sig} {dsts : Tup (PDst Nat Nat Cond) rs} {vh : VariantHint}
    {c : List Instr} {clob : FlagMask} {vs : Tup Val sig} {P : Tup Val rs → Prop} {s : MData}
    {post : mach.State → Prop}
    (hop : gprIsa.op code pas dsts vh = some (c, clob))
    (hrel : TRel (mach.PArgHolds s) pas vs) (hwp : code.wp vs P) :
    mach.FallsTo gprIsa.condReads h k c (tupDstGprs dsts ++ frameIsa.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (mach.PDstHolds s') dsts rvs) ∧ mach.mem s' = mach.mem s)
      post := by
  simp only [gprIsa] at hop
  unfold gop at hop
  split at hop
  case h_1 =>
    obtain ⟨va, vb, ⟨⟩⟩ := vs; obtain ⟨ha, hb⟩ := trel2 hrel
    exact addArm_spec hop ha hb hwp
  case h_2 =>
    obtain ⟨va, vb, ⟨⟩⟩ := vs; obtain ⟨ha, hb⟩ := trel2 hrel
    exact subArm_spec hop ha hb hwp
  case h_3 =>
    obtain ⟨va, vb, ⟨⟩⟩ := vs; obtain ⟨ha, hb⟩ := trel2 hrel
    exact binArm_spec hop ha hb hwp
  case h_4 =>
    obtain ⟨va, vb, ⟨⟩⟩ := vs; obtain ⟨ha, hb⟩ := trel2 hrel
    exact binArm_spec hop ha hb hwp
  case h_5 =>
    obtain ⟨va, vb, ⟨⟩⟩ := vs; obtain ⟨ha, hb⟩ := trel2 hrel
    exact binArm_spec hop ha hb hwp
  case h_6 =>
    obtain ⟨va, vb, ⟨⟩⟩ := vs; obtain ⟨ha, hb⟩ := trel2 hrel
    exact boolArm_spec (gb := (· && ·)) (by decide) hop ha hb hwp
  case h_7 =>
    obtain ⟨va, vb, ⟨⟩⟩ := vs; obtain ⟨ha, hb⟩ := trel2 hrel
    exact boolArm_spec (gb := (· || ·)) (by decide) hop ha hb hwp
  case h_8 =>
    obtain ⟨va, vb, ⟨⟩⟩ := vs; obtain ⟨ha, hb⟩ := trel2 hrel
    exact boolArm_spec (gb := (· ^^ ·)) (by decide) hop ha hb hwp
  case h_9 =>
    obtain ⟨va, vb, ⟨⟩⟩ := vs; obtain ⟨ha, hb⟩ := trel2 hrel
    exact binArm_spec hop ha hb hwp
  case h_10 =>
    obtain ⟨va, vb, ⟨⟩⟩ := vs; obtain ⟨ha, hb⟩ := trel2 hrel
    exact binArm_spec hop ha hb hwp
  case h_11 =>
    obtain ⟨va, vb, ⟨⟩⟩ := vs; obtain ⟨ha, hb⟩ := trel2 hrel
    exact cmpArm_spec hop ha hb hwp
  case h_12 =>
    obtain ⟨va, vb, vc, ⟨⟩⟩ := vs; obtain ⟨ha, hb, hc⟩ := trel3 hrel
    exact addcArm_spec hop ha hb hc hwp
  case h_13 => cases hop

theorem clearFlags_spec {h : LHost} {k : Nat} {s : MData} {post : mach.State → Prop} :
    mach.FallsTo gprIsa.condReads h k gprIsa.clearFlags frameIsa.scratch [] FlagMask.all s
      (fun s' => (∀ c ∈ gprIsa.zeroFlags, mach.evalCond s' c = false) ∧ mach.mem s' = mach.mem s)
      post := by
  refine fallsTo_steps ⟨_, rfl, rfl⟩ ⟨?_, rfl⟩
    (frame_mk (keeps_one (d := 11) (by simp [frameIsa]) (by intro r hr; simp [hr])) rfl
      (upd_all _ _))
  intro c hc
  simp only [gprIsa, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> rfl

theorem mov_spec {h : LHost} {k rd rs : Nat} {s : MData} {post : mach.State → Prop} :
    mach.FallsTo gprIsa.condReads h k (gprIsa.mov rd rs) [rd] [] FlagMask.none s
      (fun s' => mach.getGpr s' rd = mach.getGpr s rs ∧ mach.mem s' = mach.mem s) post :=
  fallsTo_steps ⟨_, rfl, rfl⟩ ⟨by simp, rfl⟩
    (frame_mk (keeps_one (d := rd) (by simp) (by intro r hr; simp [hr])) rfl (upd_eq rfl rfl rfl))

theorem movi_spec {h : LHost} {k rd : Nat} {c : BitVec 64} {s : MData} {post : mach.State → Prop} :
    mach.FallsTo gprIsa.condReads h k (gprIsa.movi rd c) (rd :: frameIsa.scratch) [] FlagMask.none s
      (fun s' => mach.getGpr s' rd = c ∧ mach.mem s' = mach.mem s) post :=
  fallsTo_steps ⟨_, rfl, rfl⟩ ⟨by simp, rfl⟩
    (frame_mk (keeps_one (d := rd) (by simp) (by intro r hr; simp [hr])) rfl (upd_eq rfl rfl rfl))

theorem setcc_spec {h : LHost} {k rd : Nat} {c : Cond} {s : MData} {post : mach.State → Prop} :
    mach.FallsTo gprIsa.condReads h k (gprIsa.setcc rd c) (rd :: frameIsa.scratch) [] FlagMask.none s
      (fun s' => GprHolds (mach.getGpr s' rd) .bool (mach.evalCond s c) ∧ mach.mem s' = mach.mem s)
      post :=
  fallsTo_steps ⟨_, rfl, rfl⟩ ⟨by simpa using gprHolds_bool (s.evalCond c), rfl⟩
    (frame_mk (keeps_one (d := rd) (by simp) (by intro r hr; simp [hr])) rfl (upd_eq rfl rfl rfl))

end GprPf

open GprPf in
theorem gprSpec : GprTarget mach gprIsa frameIsa.scratch where
  negCond_reads := negCond_reads
  negCond_eval := negCond_eval
  clearFlags_spec := clearFlags_spec
  mov_spec := mov_spec
  movi_spec := movi_spec
  setcc_spec := fun _ => setcc_spec
  jmp_spec := jmp_spec
  jcc_spec := jcc_spec
  jnzGpr_spec := fun hc hl _ hb hk => jnzGpr_spec hc hl hb hk
  op_spec := fun hop _ _ hrel hwp => op_spec hop hrel hwp
  load_spec := fun hop _ _ hl => load_spec hop hl
  store_spec := fun hop _ hv _ => store_spec hop hv


/-! ## 7. The `Target` Instance -/

@[reducible] def litmusTarget : Target where
  toIsa := isa
  mach := mach
  gprSpec := gprSpec
  frameSpec := frameSpec
  vecSpec := vecSpec

/-- Litmus `Isa` with `[base + disp]` displacement elision enabled for GPR memory types. -/
def addrIsa : Isa :=
  { isa with
    supportsAddrDisp := fun t _ => isGprTy t
    supportsAddrIdx := fun t _ _ => isGprTy t }

/-- `Target` wrapper over `addrIsa`, sharing verified `gprSpec`/`frameSpec`/`vecSpec`. -/
@[reducible] def litmusAddrTarget : Target where
  toIsa := addrIsa
  mach := mach
  gprSpec := gprSpec
  frameSpec := frameSpec
  vecSpec := vecSpec

#print axioms frameSpec
#print axioms vecSpec
#print axioms gprSpec
#print axioms litmusTarget
#print axioms litmusAddrTarget

end LeanQbe.T.RegaLitmus
