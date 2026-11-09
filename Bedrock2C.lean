module

import Kraken.Bedrock2.Test.Cases
import Kraken.Bedrock2.CPrinter
import Kraken.Bedrock2.Interp
import Lean.Data.Json

open Lean Kraken.Bedrock2 Kraken.Bedrock2.Test

def findCase (name : String) : Except String Case :=
  match cases.find? (·.name == name) with
  | some c => pure c
  | none => throw s!"unknown case '{name}'"

def cArgs : List Arg → Nat → List String
  | [], _ => []
  | .word v :: as, k => ("(br_word_t)" ++ cLit v) :: cArgs as k
  | .buf _ :: as, k => s!"(br_word_t)_br_buf{k}" :: cArgs as (k + 1)

def cModuleAt (c : Case) (w : Nat) : Except String (String × Func) := do
  let fs := c.funcsAt w
  let some f := fs.lookup c.entry | throw s!"entry function '{c.entry}' not found"
  if f.params.length != c.args.length then throw s!"case '{c.name}' has wrong number of arguments"
  return (← cModule (fs.filter (·.1 == c.entry)) (fs.filter (·.1 != c.entry)) true, f)

def cDriver (c : Case) : Except String String := do
  let (mod32, f32) ← cModuleAt c 32
  let (mod64, f) ← cModuleAt c 64
  if f32.rets.length != f.rets.length then
    throw s!"case '{c.name}' has width-dependent number of return values"
  let mod := if mod32 == mod64 then mod64 else String.join [
    "#include <stdint.h>\n",
    "#if UINTPTR_MAX == 0xFFFFFFFFu\n", mod32, "\n",
    "#elif UINTPTR_MAX == 0xFFFFFFFFFFFFFFFFu\n", mod64, "\n",
    "#else\n",
    "#error \"word size is neither 32 nor 64 bits\"\n",
    "#endif"]
  let bufs := c.buffers.zipIdx
  let nrets := f.rets.length
  let retNames := (List.range nrets).map (s!"_br_ret{·}")
  let call := c.entry ++ "(" ++ ", ".intercalate (cArgs c.args 0 ++ retNames.dropLast.map ("&" ++ ·)) ++ ");"
  let sep (i : Nat) := if i == 0 then "" else "printf(\", \"); "
  return mod ++ "\n" ++ String.join [
    "#include <stdio.h>\n",
    "#include <stdlib.h>\n\n",
    "static br_word_t _br_log_addr[4096];\n",
    "static br_word_t _br_log_n[4096];\n",
    "static size_t _br_log_len;\n\n",
    "void _br_test_stackalloc(br_word_t addr, br_word_t n) {\n",
    "  if (_br_log_len == 4096) abort();\n",
    "  _br_log_addr[_br_log_len] = addr;\n",
    "  _br_log_n[_br_log_len] = n;\n",
    "  _br_log_len++;\n",
    "}\n\n",
    "static void _br_print_bytes(const uint8_t *p, size_t n) {\n",
    "  printf(\"[\");\n",
    "  for (size_t i = 0; i < n; i++) printf(\"%s%u\", i ? \", \" : \"\", (unsigned)p[i]);\n",
    "  printf(\"]\");\n",
    "}\n\n",
    String.join (bufs.map fun (bs, k) =>
      s!"_Alignas(16) static uint8_t _br_buf{k}[{max bs.length 1}] = \{" ++
        (if bs.isEmpty then "0" else ", ".intercalate (bs.map (toString ·.toNat))) ++ "};\n"),
    "\nint main(void) {\n",
    String.join (retNames.map fun r => s!"  br_word_t {r} = 0;\n"),
    (match retNames.getLast? with
      | none => "  " ++ call ++ "\n"
      | some r => "  " ++ r ++ " = " ++ call ++ "\n"),
    "  printf(\"{\\\"wordsize\\\": %u, \\\"buffers\\\": [\", (unsigned)sizeof(br_word_t));\n",
    String.join (bufs.map fun (_, k) =>
      s!"  {sep k}printf(\"%llu\", (unsigned long long)(br_word_t)_br_buf{k});\n"),
    "  printf(\"], \\\"stackalloc\\\": [\");\n",
    "  for (size_t i = 0; i < _br_log_len; i++)\n",
    "    printf(\"%s[%llu, %llu]\", i ? \", \" : \"\", (unsigned long long)_br_log_addr[i],\n",
    "      (unsigned long long)_br_log_n[i]);\n",
    "  printf(\"], \\\"rets\\\": [\");\n",
    String.join (retNames.zipIdx.map fun (r, i) =>
      s!"  {sep i}printf(\"%llu\", (unsigned long long){r});\n"),
    "  printf(\"], \\\"final\\\": [\");\n",
    String.join (bufs.map fun (bs, k) => s!"  {sep k}_br_print_bytes(_br_buf{k}, {bs.length});\n"),
    "  printf(\"]}\\n\");\n",
    "  return 0;\n",
    "}\n"]

structure Obs where
  rets : List Nat
  final : List (List UInt8)
  deriving BEq

def Obs.toJson (o : Obs) : List (String × Json) :=
  [("rets", Lean.toJson o.rets), ("final", Lean.toJson (o.final.map (·.map (·.toNat))))]

def argVals (w : Nat) : List Arg → List Nat → Option (List (BitVec w))
  | [], _ => some []
  | .word v :: as, ad => (BitVec.ofInt w v :: ·) <$> argVals w as ad
  | .buf _ :: as, a :: ad => (BitVec.ofNat w a :: ·) <$> argVals w as ad
  | .buf _ :: _, [] => none

def runCase (w : Nat) (c : Case) (addrs : List Nat) (o : List Nat) (fill : UInt8) :
    Except String Obs := do
  let some f := c.funcs.lookup c.entry | throw s!"entry function '{c.entry}' not found"
  let bufs := c.buffers.zip addrs
  if bufs.length != addrs.length || bufs.length != c.buffers.length then
    throw "buffer count mismatch"
  let m0 : Mem w := bufs.foldl (fun m (bs, a) => m.union (bs.At (BitVec.ofNat w a))) ∅
  let some args := argVals w c.args addrs | throw "buffer count mismatch"
  let some lf := putManyZip f.params args ∅ | throw "wrong number of arguments"
  let some (_, m, l, rest) := run c.funcs fill c.fuel f.body [] m0 lf (o.map (BitVec.ofNat w))
    | throw "interpreter got stuck"
  if !rest.isEmpty then throw s!"{rest.length} logged stackallocs were not used"
  let some rets := getMany l f.rets | throw "return variable unset"
  let some final := bufs.mapM (fun (bs, a) => m.loadBytes (BitVec.ofNat w a) bs.length)
    | throw "buffer missing from final memory"
  return ⟨rets.map (·.toNat), final⟩

def alignDown (a : Nat) : Nat := a / 0x1000 * 0x1000
def alignUp (a : Nat) : Nat := (a + 0xfff) / 0x1000 * 0x1000

def perturb (w : Nat) (bufs stk : List (Nat × Nat)) : Option (List Nat) :=
  match stk.map (·.1) with
  | [] => some []
  | s :: ss =>
    let sLo := alignDown (ss.foldl min s)
    let sHi := alignUp (stk.foldl (fun h (a, n) => max h (a + max n 1)) 0)
    let all := bufs ++ stk
    let allLo := alignDown (all.foldl (fun l (a, _) => min l a) s)
    let allHi := alignUp (all.foldl (fun h (a, n) => max h (a + max n 1)) 0)
    let span := sHi - sLo
    let move (base : Nat) := stk.map fun (a, _) => a - sLo + base
    if allHi + 0x10000 + span ≤ 2 ^ w then some (move (allHi + 0x10000))
    else if span + 0x20000 ≤ allLo then some (move (allLo - 0x10000 - span))
    else none

def replay (c : Case) (j : Json) : Except String Json := do
  let ws ← j.getObjValAs? Nat "wordsize"
  let addrs := (← j.getObjValAs? (Array Nat) "buffers").toList
  let log := (← j.getObjValAs? (Array (Array Nat)) "stackalloc").toList
  let stk ← log.mapM fun | #[a, n] => pure (a, n) | _ => throw "malformed stackalloc log"
  let w ← match ws with | 4 => pure 32 | 8 => pure 64 | _ => throw s!"unsupported word size {ws}"
  let fail (msg : String) : Json := Json.mkObj [("status", Json.str "stuck"), ("error", Json.str msg)]
  let c := { c with funcs := c.funcsAt w }
  match runCase w c addrs (stk.map (·.1)) 0 with
  | .error e => return fail e
  | .ok obs =>
    let some o' := perturb w (addrs.zip (c.buffers.map (·.length))) stk
      | throw "no room for perturbed stack addresses"
    let alt := runCase w c addrs o' 0xa5
    match alt with
    | .ok obs' =>
      if obs' == obs then return Json.mkObj ([("status", Json.str "ok")] ++ obs.toJson)
      else return Json.mkObj ([("status", Json.str "invalid")] ++ obs.toJson ++ [("perturbed", Json.mkObj obs'.toJson)])
    | .error e =>
      return Json.mkObj ([("status", Json.str "invalid")] ++ obs.toJson ++ [("perturbed_error", Json.str e)])

partial def readAll (s : IO.FS.Stream) (acc : String := "") : IO String := do
  let line ← s.getLine
  if line.isEmpty then return acc else readAll s (acc ++ line)

def usage : String :=
  "usage: bedrock2c list | emit <case> [--out file.c] | replay <case> < c_output.json"

def orFail {α} (r : Except String α) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

public def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["list"] =>
      for c in cases do IO.println c.name
      return 0
    | ["emit", name] =>
      IO.print (← orFail (findCase name >>= cDriver))
      return 0
    | ["emit", name, "--out", file] =>
      IO.FS.writeFile file (← orFail (findCase name >>= cDriver))
      return 0
    | ["replay", name] =>
      let c ← orFail (findCase name)
      let j ← orFail (Json.parse (← readAll (← IO.getStdin)))
      IO.println (← orFail (replay c j)).compress
      return 0
    | _ =>
      IO.eprintln usage
      return 2
  catch e =>
    IO.eprintln s!"bedrock2c: {e}"
    return 1
