import LeanQbe
import spike.il.Smoke

/-!
Differential test of `LeanQbe.Op.eval` and `LeanQbe.Print` against stock QBE (driven by
`scripts/qbe_difftest.sh`). For every operation, class, width and test vector where `Op.eval` is
defined, a one-instruction function is printed to QBE IL and called from a C harness; the expected
output is computed by `Op.eval` in Lean. Also prints the smoke-test functions of `spike/il/Smoke.lean`.

Usage: `lake env lean --run scripts/QbeDiff.lean <outdir>` writes test.ssa, harness.c, expected.txt.
-/

open LeanQbe

def vecs : List Val := [0, 1, 2, 5, 31, 32, 33, 63, 64, 65, 0x7fffffff, 0x80000000, 0xffffffff,
  0x100000000, 0x7fffffffffffffff, 0x8000000000000000, 0xffffffffffffffff, 0xfffffffffffffffb,
  0x123456789abcdef0, 0xfedcba9876543210, 0x80, 0xff, 0x8000, 0xffff, 0x17f]

def bins : List BinOp := [.add, .sub, .mul, .div, .rem, .udiv, .urem, .and, .or, .xor, .sar, .shr, .shl]
def cmps : List CmpOp := [.eq, .ne, .sle, .slt, .sge, .sgt, .ule, .ult, .uge, .ugt]
def szs : List Sz := [.b, .h, .w, .l]
def clss : List Cls := [.w, .l]

structure T where
  name : String
  arity : Nat           -- 1 or 2 value args
  fn : Fn
  eval : Val → Val → Option Val

def mkBin2 (name : String) (op : ∀ {V : Type}, Arg V → Arg V → Op V) : T :=
  { name, arity := 2,
    fn := { name, body := fun _ _ => .param fun a => .param fun b => .let_ (op (.var a) (.var b)) fun x => .ret [.var x] },
    eval := fun a b => (op (.imm a) (.imm b) : Op Val).eval }

def mkImm (name : String) (c : Val) (op : ∀ {V : Type}, Arg V → Arg V → Op V) : T :=
  { name, arity := 1,
    fn := { name, body := fun _ _ => .param fun a => .let_ (op (.var a) (.imm c)) fun x => .ret [.var x] },
    eval := fun a _ => (op (.imm a) (.imm c) : Op Val).eval }

def mkUn (name : String) (op : ∀ {V : Type}, Arg V → Op V) : T :=
  { name, arity := 1,
    fn := { name, body := fun _ _ => .param fun a => .let_ (op (.var a)) fun x => .ret [.var x] },
    eval := fun a _ => (op (.imm a) : Op Val).eval }

/-- store v to the buffer p, load it back: `f(p, v)`. Expected: trunc (extend v). -/
def mkMem (c : Cls) (s : Sz) (sg : Bool) : T :=
  let name := s!"mem_{c.name}_{s.name}_{sg}"
  { name, arity := 2,
    fn := { name, body := fun _ _ => .param fun p => .param fun v =>
      .store s (.var v) (.var p) <| .load c s sg (.var p) fun x => .ret [.var x] },
    eval := fun _ v => some (c.trunc (s.extend sg v)) }

def tests : List T :=
  (clss.flatMap fun k => bins.map fun o => mkBin2 s!"{o.name}_{k.name}" (fun a b => .bin k o a b)) ++
  (clss.flatMap fun k => cmps.map fun o => mkBin2 s!"c{o.name}_{k.name}" (fun a b => .cmp k o a b)) ++
  (clss.flatMap fun k => szs.flatMap fun s => [true, false].map fun sg =>
      mkUn s!"ext_{k.name}_{s.name}_{sg}" (fun a => .ext k s sg a)) ++
  (clss.map fun k => mkUn s!"copy_{k.name}" (fun a => .copy k a)) ++
  [mkImm "addimm_l" 0xffffffffffffffff (fun a b => .bin .l .add a b),
   mkImm "addimm_w" 0xffffffffffffffff (fun a b => .bin .w .add a b),
   mkImm "shlimm_l" 65 (fun a b => .bin .l .shl a b),
   mkImm "sarimm_w" 33 (fun a b => .bin .w .sar a b),
   mkImm "big_l" 0x8000000000000000 (fun a b => .bin .l .xor a b),
   mkImm "cult_imm" 0xfffffffffffffffe (fun a b => .cmp .l .ult a b)] ++
  (clss.flatMap fun c => szs.flatMap fun s => [true, false].map fun sg => mkMem c s sg)

def main (argv : List String) : IO Unit := do
  let dir : System.FilePath := argv.headD "."
  IO.FS.createDirAll dir
  let fns := tests.map (·.fn) ++ [⟨"tracer", Smoke.tracer⟩, ⟨"evenOdd", Smoke.evenOdd⟩, ⟨"caller", Smoke.caller⟩]
  match Print.module fns with
  | .error e => throw (IO.userError e)
  | .ok s => IO.FS.writeFile (dir / "test.ssa") s
  let mut c := "#include <stdio.h>\n#include <stdint.h>\n#include <stdlib.h>\n"
  c := c ++ "uint64_t g(uint64_t a) { return a + 1; }\nvoid abort_(void);\n"
  c := c ++ "uint64_t tracer(uint64_t, uint64_t, uint64_t*);\nuint64_t evenOdd(uint64_t);\nuint64_t caller(uint64_t);\n"
  for t in tests do
    if t.arity = 2 then c := c ++ s!"uint64_t {t.name}(uint64_t, uint64_t);\n"
    else c := c ++ s!"uint64_t {t.name}(uint64_t);\n"
  c := c ++ "int main(void) {\n  uint64_t buf[2];\n"
  let mut exp := ""
  for t in tests do
    for a in vecs do
      for b in (if t.arity = 2 then vecs else [0]) do
        match t.eval a b with
        | none => pure ()
        | some r =>
          let call := if t.name.startsWith "mem_" then s!"{t.name}((uint64_t)buf, {b.toNat}ull)"
            else if t.arity = 2 then s!"{t.name}({a.toNat}ull, {b.toNat}ull)" else s!"{t.name}({a.toNat}ull)"
          c := c ++ s!"  printf(\"{t.name} {a.toNat} {b.toNat} %llu\\n\", (unsigned long long){call});\n"
          exp := exp ++ s!"{t.name} {a.toNat} {b.toNat} {r.toNat}\n"
  -- smoke functions
  for n in [0, 1, 2, 7, 10, 11] do
    c := c ++ s!"  printf(\"evenOdd {n} %llu\\n\", (unsigned long long)evenOdd({n}));\n"
    exp := exp ++ s!"evenOdd {n} {if n % 2 = 0 then 1 else 0}\n"
  c := c ++ "  printf(\"tracer %llu %llu\\n\", (unsigned long long)tracer(40, 2, buf), (unsigned long long)buf[0]);\n"
  exp := exp ++ "tracer 42 42\n"
  c := c ++ "  printf(\"caller %llu\\n\", (unsigned long long)caller(41));\n"
  exp := exp ++ "caller 42\n"
  c := c ++ "  return 0;\n}\n"
  IO.FS.writeFile (dir / "harness.c") c
  IO.FS.writeFile (dir / "expected.txt") exp
  IO.println s!"{tests.length} test functions"
