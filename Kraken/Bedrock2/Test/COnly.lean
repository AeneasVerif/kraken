module

public import Kraken.Bedrock2.CPrinter
import Kraken.Bedrock2.Notation
meta import Kraken.Bedrock2.Notation

@[expose] public section

namespace Kraken.Bedrock2.Test

def typecheckLits : List Int :=
  [0, 1, 5, 31, 32, 63, 64, 255, 256, 2 ^ 31, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 63, 2 ^ 64 - 1, 2 ^ 64 + 5, -1]

def allBinOps : List BinOp :=
  [.add, .sub, .mul, .mulhuu, .divu, .remu, .and, .or, .xor, .sru, .slu, .srs, .lts, .ltu, .eq]

def allAccessSizes : List AccessSize := [.one, .two, .four, .eight]

def typecheckExprs : List Expr :=
  let a : Expr := .var "a"
  let b : Expr := .var "b"
  let lits := typecheckLits.map Expr.literal
  let cmp : List Expr := [.op .eq a b, .op .ltu a b, .op .lts a b]
  [a] ++ lits ++
  allBinOps.flatMap (fun o =>
    [.op o a b] ++ lits.flatMap (fun l => [.op o a l, .op o l a]) ++
    cmp.flatMap (fun c => [.op o c a, .op o a c, .op o c (.literal 3)])) ++
  [Op1.not, Op1.opp].flatMap (fun o => (a :: lits ++ cmp).map (.op1 o)) ++
  lits.flatMap (fun l => [.ite a b l, .ite l a b, .ite (.op .eq a b) l a]) ++
  cmp.map (fun c => .ite c c c) ++
  allAccessSizes.flatMap (fun sz =>
    [.load sz a, .load sz (.op .add a (.literal 8)), .inlinetable sz (List.range 16 |>.map (·.toUInt8)) a])

def typecheckC : String :=
  cPrelude ++ "\nint main(void) {\n  br_word_t a = 0, b = 0;\n  (void)a;\n  (void)b;\n" ++
  String.join (typecheckExprs.zipIdx.map fun (e, i) =>
    s!"  static_assert(_Generic(({cExpr e}), br_word_t: 1, default: 0), \"expr {i}\");\n") ++
  "  return 0;\n}\n"

def stackallocLoop := bedrock2:(fn stackalloc_loop() -> (r) {
  i = 0;
  while i < 0x100000 {
    stackalloc 1024 as t { store1(t + (i >> 10), i) };
    i = i + 1
  };
  r = 0
})

def stackallocLoopC : Except String String := do
  let m ← cModule [stackallocLoop] []
  return m ++ "\nint main(void) {\n  return (int)stackalloc_loop();\n}\n"

def cOnlyPrograms : List (String × Bool × Except String String) :=
  [("typecheck", false, pure typecheckC), ("stackalloc_loop", true, stackallocLoopC)]

end Kraken.Bedrock2.Test
