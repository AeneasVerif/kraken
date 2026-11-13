module

public import Kraken.Bedrock2.Test.Cases

@[expose] public section

namespace Kraken.Bedrock2.Test

def boundaryValues : List Int :=
  [0, 1, 2, 31, 32, 33, 63, 64, 65, 2 ^ 31 - 1, 2 ^ 31, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 63 - 1, 2 ^ 63,
   2 ^ 64 - 1]

def binops : List (BinOp × String) :=
  [(.add, "add"), (.sub, "sub"), (.mul, "mul"), (.mulhuu, "mulhuu"), (.divu, "divu"),
   (.remu, "remu"), (.and, "and"), (.or, "or"), (.xor, "xor"), (.sru, "sru"), (.slu, "slu"),
   (.srs, "srs"), (.lts, "lts"), (.ltu, "ltu"), (.eq, "eq")]

def seqAll : List Cmd → Cmd
  | [] => .skip
  | [c] => c
  | c :: cs => .seq c (seqAll cs)

def offset (p : String) (k : Nat) : Expr :=
  if k == 0 then .var p else .op .add (.var p) (.literal k)

def storeAll (p : String) (es : List Expr) : Cmd :=
  seqAll (es.zipIdx.map fun (e, k) => .store .eight (offset p (8 * k)) e)

def boundaryVar (i : Nat) : Expr := .var s!"v{i}"

def boundaryCase (name : String) (es : List Expr) : Case :=
  let fname := s!"matrix_{name}"
  let params := "out" :: (List.range boundaryValues.length).map (s!"v{·}")
  { name := fname, funcs := [(fname, ⟨params, [], storeAll "out" es⟩)], entry := fname,
    args := .buf (List.replicate (8 * es.length) 0) :: boundaryValues.map .word }

def binopCase (op : BinOp) (name : String) : Case :=
  let idx := List.range boundaryValues.length
  boundaryCase name <|
    (idx.flatMap fun i => idx.map fun j => .op op (boundaryVar i) (boundaryVar j)) ++
    (idx.flatMap fun i => boundaryValues.map fun c => .op op (boundaryVar i) (.literal c))

def op1Case : Case :=
  let idx := List.range boundaryValues.length
  boundaryCase "op1" <| [Op1.not, Op1.opp].flatMap fun op =>
    idx.map (fun i => .op1 op (boundaryVar i)) ++ boundaryValues.map (fun c => .op1 op (.literal c))

def accessSizes : List AccessSize := [.one, .two, .four, .eight]

def accessOffsets : List Nat := List.range 9

def accessCase : Case :=
  let loads := accessSizes.flatMap fun sz => accessOffsets.map fun o => Expr.load sz (offset "src" o)
  let slots := accessSizes.flatMap fun sz => accessOffsets.map fun o => (sz, o)
  let stores := seqAll (slots.zipIdx.map fun ((sz, o), k) => .store sz (offset "dst" (16 * k + o)) (.var "v"))
  { name := "matrix_access",
    funcs := [("matrix_access", ⟨["src", "dst", "out", "v"], [], .seq (storeAll "out" loads) stores⟩)],
    entry := "matrix_access",
    args := [.buf (bytesOf 24 (· * 37 + 0x83)), .buf (List.replicate (16 * slots.length) 0),
      .buf (List.replicate (8 * loads.length) 0), .word 0xfedcba9876543210] }

def matrixCases : List Case :=
  binops.map (fun (op, name) => binopCase op name) ++ [op1Case, accessCase]

end Kraken.Bedrock2.Test
