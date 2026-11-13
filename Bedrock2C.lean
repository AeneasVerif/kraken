module

import Kraken.Bedrock2.Test.Cases
import Kraken.Bedrock2.Test.Matrix
import Kraken.Bedrock2.CPrinter
import Kraken.Bedrock2.Test.Run
import Kraken.Bedrock2.Test.Gen
import Kraken.Bedrock2.Test.COnly
import Lean.Data.Json

open Lean Kraken.Bedrock2 Kraken.Bedrock2.Test

def corpus : List Case := cases ++ matrixCases

def findCase (name : String) : Except String Case :=
  match corpus.find? (·.name == name), name.splitOn "_" with
  | some c, _ => pure c
  | none, ["gen", seed, i] =>
    match seed.toNat?, i.toNat? with
    | some seed, some i => Gen.genCase seed i
    | _, _ => throw s!"unknown case '{name}'"
  | none, _ => throw s!"unknown case '{name}'"

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

def obsJson (o : Obs) : List (String × Json) :=
  [("rets", Lean.toJson o.rets), ("final", Lean.toJson (o.final.map (·.map (·.toNat))))]

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
      if obs' == obs then return Json.mkObj ([("status", Json.str "ok")] ++ obsJson obs)
      else return Json.mkObj ([("status", Json.str "invalid")] ++ obsJson obs ++ [("perturbed", Json.mkObj (obsJson obs'))])
    | .error e =>
      return Json.mkObj ([("status", Json.str "invalid")] ++ obsJson obs ++ [("perturbed_error", Json.str e)])

partial def readAll (s : IO.FS.Stream) (acc : String := "") : IO String := do
  let line ← s.getLine
  if line.isEmpty then return acc else readAll s (acc ++ line)

def usage : String :=
  "usage: bedrock2c list | gen <seed> <count> | show <case> | emit <case> [--out file.c] | " ++
    "replay <case> < c_output.json | conly-list | conly <name> --out file.c"

def orFail {α} (r : Except String α) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

public def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["list"] =>
      for c in corpus do IO.println c.name
      return 0
    | ["gen", seed, count] =>
      let some seed := seed.toNat? | throw (IO.userError "bad seed")
      let some count := count.toNat? | throw (IO.userError "bad count")
      for i in List.range count do
        IO.println (← orFail (Gen.genCase seed i)).name
      return 0
    | ["show", name] =>
      let c ← orFail (findCase name)
      IO.println s!"entry := {repr c.entry}"
      IO.println s!"args := {repr c.args}"
      IO.println s!"funcs := {repr c.funcs}"
      if c.funcsAt 32 != c.funcs then IO.println s!"funcsAt 32 := {repr (c.funcsAt 32)}"
      if c.funcsAt 64 != c.funcs then IO.println s!"funcsAt 64 := {repr (c.funcsAt 64)}"
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
    | ["conly-list"] =>
      for (name, run, _) in cOnlyPrograms do
        IO.println s!"{name} {if run then "run" else "compile"}"
      return 0
    | ["conly", name, "--out", file] =>
      let some (_, _, src) := cOnlyPrograms.find? (·.1 == name)
        | throw (IO.userError s!"unknown C-only program '{name}'")
      IO.FS.writeFile file (← orFail src)
      return 0
    | _ =>
      IO.eprintln usage
      return 2
  catch e =>
    IO.eprintln s!"bedrock2c: {e}"
    return 1
