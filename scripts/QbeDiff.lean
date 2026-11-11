import LeanQbe
import LeanQbeTest.Smoke

/-!
Differential test of `LeanQbe`'s semantics and `LeanQbe.Print` against stock QBE (driven by
`scripts/qbe_difftest.sh`).

Every test is a function in our IL. It is printed to QBE IL and called from a C harness; the expected
result is computed in Lean by `interp` below, a small fuel-bounded interpreter whose every step is
`Op.eval`, `loadVal`, `storeOk`/`storeMem` (Kraken's `Mem.loadInt`/`Mem.storeInt` on a concrete
`Mem 64`) or `Truthy`, i.e. the definitions `wp` is built from. Tests:

* every operation, class, width, on 25 test vectors (pairs for binary operations), where defined;
* store/load round trips at every width, signedness and class, through a real buffer;
* `jnz` on the result of a 64-bit `add` (the condition is the low 32 bits);
* the smoke functions of `LeanQbeTest/Smoke.lean`, and an `exit` path (run as a separate process).

Usage: `lake env lean --run scripts/QbeDiff.lean <outdir>` writes test.ssa, harness.c, expected.txt,
expected_exit.txt. The pointer argument of memory tests is `bufAddr` in Lean and a real buffer in C;
results do not depend on it.
-/

open LeanQbe

/-! ## Interpreter (test oracle; untrusted, not used by any proof) -/

inductive Outcome
  | ret (vs : List Val) (m : Mem 64)
  | exit (f : Sym) (as : List Val) (m : Mem 64)

instance : Inhabited Outcome := ⟨.ret [] ∅⟩

/-- External functions of the harness. -/
def extern : Sym → List Val → Mem 64 → Option (List Val × Mem 64)
  | "g", [a], m => some ([a + 1], m)
  | _, _, _ => none

structure Ctx where
  blocks : List (Nat × Expr Val Nat) := []
  acc : List Nat := []
  nl : Nat := 0

/-- Run `e` with pending arguments `args`. `none`: undefined behaviour, junk, or out of fuel. -/
partial def interp (fuel : Nat) (ctx : Ctx) (e : Expr Val Nat) (args : List Val) (m : Mem 64) :
    Option Outcome :=
  let noArgs : Option Unit := if args.isEmpty then some () else none
  match e with
  | .param f =>
    match args with
    | a :: as => interp fuel { ctx with acc := [] } (f a) as m
    | [] => none
  | .let_ op k => do noArgs; let v ← op.eval; interp fuel { ctx with acc := [] } (k v) [] m
  | .load c s sg a k => do
    noArgs; let v ← loadVal m c s sg a.val; interp fuel { ctx with acc := [] } (k v) [] m
  | .store s v a k => do
    noArgs; let _ ← m.loadInt a.val s.bytes
    interp fuel { ctx with acc := [] } k [] (storeMem m s a.val v.val)
  | .call f as k => do
    noArgs; let (rs, m') ← extern f (as.map Arg.val) m
    interp fuel { ctx with acc := [] } k rs m'
  | .jnz c t e => do
    noArgs
    interp fuel { ctx with acc := [] } (if lo32 c.val ≠ 0 then t else e) [] m
  | .jump j as => do
    noArgs
    match fuel with
    | 0 => none
    | fuel + 1 =>
      let b ← ctx.blocks.lookup j
      interp fuel { ctx with acc := [] } b (as.map Arg.val) m
  | .ret vs => do noArgs; pure (.ret (vs.map Arg.val) m)
  | .exit f as => do noArgs; pure (.exit f (as.map Arg.val) m)
  | .hlt => none
  | .label f => do
    noArgs
    interp fuel { ctx with acc := ctx.acc ++ [ctx.nl], nl := ctx.nl + 1 } (f ctx.nl) [] m
  | .block b rest => do
    noArgs
    match ctx.acc with
    | [] => none
    | l :: acc' => interp fuel { ctx with blocks := (l, b) :: ctx.blocks, acc := acc' } rest [] m

def bufAddr : Val := 0x10000
/-- 16 mapped bytes at `bufAddr`. -/
def mem0 : Mem 64 := (List.replicate 16 (0 : UInt8)).At bufAddr

def runFn (f : Func) (args : List Val) : Option Outcome := interp 100000 {} (f Val Nat) args mem0

def retVal (f : Func) (args : List Val) : Option Val :=
  match runFn f args with
  | some (.ret [v] _) => some v
  | _ => none

/-! ## Tests -/

def vecs : List Val := [0, 1, 2, 5, 31, 32, 33, 63, 64, 65, 0x7fffffff, 0x80000000, 0xffffffff,
  0x100000000, 0x7fffffffffffffff, 0x8000000000000000, 0xffffffffffffffff, 0xfffffffffffffffb,
  0x123456789abcdef0, 0xfedcba9876543210, 0x80, 0xff, 0x8000, 0xffff, 0x17f,
  0xffffffff00000000, 0x100000001]

def bins : List BinOp := [.add, .sub, .mul, .div, .rem, .udiv, .urem, .and, .or, .xor, .sar, .shr, .shl]
def cmps : List CmpOp := [.eq, .ne, .sle, .slt, .sge, .sgt, .ule, .ult, .uge, .ugt]
def szs : List Sz := [.b, .h, .w, .l]
def clss : List Cls := [.w, .l]

structure T where
  name : String
  /-- 1 or 2 value arguments -/
  arity : Nat
  /-- the first argument is the buffer pointer -/
  ptr : Bool := false
  fn : Func

def mkBin2 (name : String) (op : ∀ {V : Type}, Arg V → Arg V → Op V) : T :=
  { name, arity := 2,
    fn := fun _ _ => .param fun a => .param fun b => .let_ (op (.var a) (.var b)) fun x => .ret [.var x] }

def mkImm (name : String) (c : Val) (op : ∀ {V : Type}, Arg V → Arg V → Op V) : T :=
  { name, arity := 1, fn := fun _ _ => .param fun a => .let_ (op (.var a) (.imm c)) fun x => .ret [.var x] }

def mkUn (name : String) (op : ∀ {V : Type}, Arg V → Op V) : T :=
  { name, arity := 1, fn := fun _ _ => .param fun a => .let_ (op (.var a)) fun x => .ret [.var x] }

/-- `f(p, v)`: store `v` to the buffer `p`, load it back. -/
def mkMem (c : Cls) (s : Sz) (sg : Bool) : T :=
  { name := s!"mem_{c.name}_{s.name}_{sg}", arity := 2, ptr := true,
    fn := fun _ _ => .param fun p => .param fun v =>
      .store s (.var v) (.var p) <| .load c s sg (.var p) fun x => .ret [.var x] }

/-- `jnz` on a 64-bit `add` defined in the same block (stock QBE amd64 used to test all 64 bits). -/
def jnzAdd : T :=
  { name := "jnz_add_l", arity := 2,
    fn := fun _ _ => .param fun a => .param fun b =>
      .let_ (.bin .l .add (.var a) (.var b)) fun c => .jnz (.var c) (.ret [.imm 1]) (.ret [.imm 0]) }

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
   mkImm "cult_imm" 0xfffffffffffffffe (fun a b => .cmp .l .ult a b),
   jnzAdd] ++
  (clss.flatMap fun c => szs.flatMap fun s => [true, false].map fun sg => mkMem c s sg) ++
  [{ name := "evenOdd", arity := 1, fn := Smoke.evenOdd },
   { name := "caller", arity := 1, fn := Smoke.caller }]

/-- Exit path: `exiter(a) = jnz a, ret a, exit $leanqbe_exit(a, 7)`; run with `a = 0x100000000`. -/
def exiter : Func := fun _ _ =>
  .param fun a => .jnz (.var a) (.ret [.var a]) (.exit "leanqbe_exit" [.var a, .imm 7])

def lit (v : Val) : String := s!"{v.toNat}ull"

def main (argv : List String) : IO Unit := do
  let dir : System.FilePath := argv.headD "."
  IO.FS.createDirAll dir
  let fns : List Fn := tests.map (fun t => ⟨t.name, t.fn⟩) ++ [⟨"tracer", Smoke.tracer⟩, ⟨"exiter", exiter⟩]
  match Print.module fns with
  | .error e => throw (IO.userError e)
  | .ok s => IO.FS.writeFile (dir / "test.ssa") s
  let mut c := "#include <stdio.h>\n#include <stdint.h>\n#include <stdlib.h>\n"
  c := c ++ "uint64_t g(uint64_t a) { return a + 1; }\n"
  c := c ++ "void leanqbe_exit(uint64_t a, uint64_t b) { printf(\"exit %llu %llu\\n\", (unsigned long long)a, (unsigned long long)b); exit(0); }\n"
  c := c ++ "uint64_t tracer(uint64_t, uint64_t, uint64_t*);\nuint64_t exiter(uint64_t);\n"
  for t in tests do
    if t.arity = 2 then c := c ++ s!"uint64_t {t.name}(uint64_t, uint64_t);\n"
    else c := c ++ s!"uint64_t {t.name}(uint64_t);\n"
  c := c ++ "int main(int argc, char **argv) {\n  uint64_t buf[2];\n"
  -- the exit path, alone
  let ea : Val := 0x100000000
  c := c ++ s!"  if (argc > 1) \{ exiter({lit ea}); return 1; }\n"
  let expExit := match runFn exiter [ea] with
    | some (.exit f [a, b] _) => if f = "leanqbe_exit" then s!"exit {a.toNat} {b.toNat}\n" else "?\n"
    | _ => "?\n"
  let mut exp := ""
  let mut n := 0
  for t in tests do
    for a in vecs do
      for b in (if t.arity = 2 then vecs else [0]) do
        let args := if t.arity = 2 then [(if t.ptr then bufAddr else a), b] else [a]
        match retVal t.fn args with
        | none => pure ()
        | some r =>
          let callS := if t.ptr then s!"{t.name}((uint64_t)buf, {lit b})"
            else if t.arity = 2 then s!"{t.name}({lit a}, {lit b})" else s!"{t.name}({lit a})"
          c := c ++ s!"  printf(\"{t.name} {a.toNat} {b.toNat} %llu\\n\", (unsigned long long){callS});\n"
          exp := exp ++ s!"{t.name} {a.toNat} {b.toNat} {r.toNat}\n"
          n := n + 1
  -- tracer: returns a + b and stores it to the buffer
  let tr := match runFn Smoke.tracer [40, 2, bufAddr] with
    | some (.ret [v] m) => s!"tracer {v.toNat} {((loadVal m .l .l false bufAddr).getD 0).toNat}\n"
    | _ => "?\n"
  c := c ++ "  printf(\"tracer %llu %llu\\n\", (unsigned long long)tracer(40, 2, buf), (unsigned long long)buf[0]);\n"
  exp := exp ++ tr
  c := c ++ "  return 0;\n}\n"
  IO.FS.writeFile (dir / "harness.c") c
  IO.FS.writeFile (dir / "expected.txt") exp
  IO.FS.writeFile (dir / "expected_exit.txt") expExit
  IO.println s!"{tests.length + 2} test functions, {n + 2} expected results"
