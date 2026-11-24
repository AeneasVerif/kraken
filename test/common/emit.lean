import Lean

/-!
# Unified Target-Parameterized Assembly Emitter CLI (`test/common/emit.lean`)

Replaces the 18 duplicate `test/*/emit_*.lean` CLI wrappers with a single entrypoint
supporting both SysV x86-64 and AAPCS64 AArch64 targets across all test and benchmark suites:
`kissat` (`dmin`), `coreplus`, `plain`, `m3`, `m4`, `lcnf`, `lrc`, `bignum`, and `chacha`.

Usage:
  lake env lean --run test/common/emit.lean --arch <x64|arm64> --suite <suite> [args...]
-/

def getLeanCmd : IO (String × Array String) := do
  match (← IO.getEnv "STAGE_LEAN_PATH") with
  | some _ => pure ("lean", #[])
  | none =>
    match (← IO.getEnv "LEAN_PATH") with
    | some lp => if !lp.isEmpty then pure ("lean", #[]) else pure ("lake", #["env", "lean"])
    | none => pure ("lake", #["env", "lean"])

def renderCode (arch suite : String) : Except String String :=
  match (arch, suite) with
  | ("x64", "kissat") | ("x64", "solver") | ("x64", "dmin") => .ok "import LeanQbe.T.Examples.Kissat.Solver
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Amd64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => \"/tmp/kissat_x64.s\"
  let hints := kissatFns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← match LeanQbe.T.compile x64Target.toIsa x64LegalTarget kissatFns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let asm := Driver.emitAsm (fun c => toATTAligned c ++ \"\\n\") kissatFns dirs
  IO.FS.writeFile outPath asm
"
  | ("arm64", "kissat") | ("arm64", "solver") | ("arm64", "dmin") => .ok "import LeanQbe.T.Examples.Kissat.Solver
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print

open LeanQbe.T LeanQbe.T.Examples.Kissat LeanQbe.T.Arm64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => \"/tmp/kissat_arm64.s\"
  let hints := kissatFns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← match LeanQbe.T.compile armTarget.toIsa armLegalTarget kissatFns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let pp := fun c =>
    \".p2align 2\\n\" ++ String.intercalate \"\\n\" (c.map Kraken.AArch64.Print.directive)
  IO.FS.writeFile outPath (Driver.emitAsm (fun c => pp c ++ \"\\n\") kissatFns dirs)
"
  | ("x64", "coreplus") => .ok "import LeanQbe.T.Examples.Kissat.CorePlus
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.Examples.Kissat.CorePlus LeanQbe.T.Amd64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => \"/tmp/coreplus_x64.s\"
  let hints := coreplusFns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← match LeanQbe.T.compile x64Target.toIsa x64LegalTarget coreplusFns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let asm := Driver.emitAsm (fun c => toATTAligned c ++ \"\\n\") coreplusFns dirs
  IO.FS.writeFile outPath asm
"
  | ("arm64", "coreplus") => .ok "import LeanQbe.T.Examples.Kissat.CorePlus
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print

open LeanQbe.T LeanQbe.T.Examples.Kissat.CorePlus LeanQbe.T.Arm64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => \"/tmp/coreplus_arm64.s\"
  let hints := coreplusFns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← match LeanQbe.T.compile armTarget.toIsa armLegalTarget coreplusFns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let pp := fun c =>
    \".p2align 2\\n\" ++ String.intercalate \"\\n\" (c.map Kraken.AArch64.Print.directive)
  IO.FS.writeFile outPath (Driver.emitAsm (fun c => pp c ++ \"\\n\") coreplusFns dirs)
"
  | ("x64", "plain") => .ok "import LeanQbe.T.Examples.Kissat.Plain
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.Examples.Kissat.Plain LeanQbe.T.Amd64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => \"/tmp/plain_x64.s\"
  let hints := plainFns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← match LeanQbe.T.compile x64Target.toIsa x64LegalTarget plainFns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let asm := Driver.emitAsm (fun c => toATTAligned c ++ \"\\n\") plainFns dirs
  IO.FS.writeFile outPath asm
"
  | ("arm64", "plain") => .ok "import LeanQbe.T.Examples.Kissat.Plain
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print

open LeanQbe.T LeanQbe.T.Examples.Kissat.Plain LeanQbe.T.Arm64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => \"/tmp/plain_arm64.s\"
  let hints := plainFns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← match LeanQbe.T.compile armTarget.toIsa armLegalTarget plainFns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let pp := fun c =>
    \".p2align 2\\n\" ++ String.intercalate \"\\n\" (c.map Kraken.AArch64.Print.directive)
  IO.FS.writeFile outPath (Driver.emitAsm (fun c => pp c ++ \"\\n\") plainFns dirs)
"
  | ("x64", "m3") | ("x64", "fullm3") => .ok "import LeanQbe.T.Examples.Kissat.FullM3
import LeanQbe.T.PrintCpp
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.PrintCpp LeanQbe.T.Examples.Kissat.FullM3 LeanQbe.T.Amd64

public def main (args : List String) : IO Unit := do
  let (outPath, cppPath?) : System.FilePath × Option System.FilePath := match args with
    | p :: c :: _ => (p, some c)
    | [p] => (p, none)
    | [] => (\"/tmp/kissat_m3_x64.s\", none)
  let fns := m3Module.fns
  let hints := fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← match LeanQbe.T.compile x64Target.toIsa x64LegalTarget fns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let asm := Driver.emitAsm (fun c => toATTAligned c ++ \"\\n\") fns dirs
  IO.FS.writeFile outPath asm
  if let some cppPath := cppPath? then
    let cpp ← match ppTModule m3Module with
      | .ok s => pure s
      | .error e => throw (IO.userError e)
    IO.FS.writeFile cppPath cpp
"
  | ("arm64", "m3") | ("arm64", "fullm3") => .ok "import LeanQbe.T.Examples.Kissat.FullM3
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM3 LeanQbe.T.Arm64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => \"/tmp/kissat_m3_arm64.s\"
  let fns := m3Module.fns
  let hints := fns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← match LeanQbe.T.compile armTarget.toIsa armLegalTarget fns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let pp := fun c =>
    \".p2align 2\\n\" ++ String.intercalate \"\\n\" (c.map Kraken.AArch64.Print.directive)
  IO.FS.writeFile outPath (Driver.emitAsm (fun c => pp c ++ \"\\n\") fns dirs)
"
  | ("x64", "m4") | ("x64", "fullm4") => .ok "import LeanQbe.T.Examples.Kissat.FullM4
import LeanQbe.T.PrintCpp
import LeanQbe.T.Opt
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.PrintCpp LeanQbe.T.Examples.Kissat.FullM4 LeanQbe.T.Amd64

public def main (args : List String) : IO Unit := do
  let (outPath, cppPath?) : System.FilePath × Option System.FilePath := match args with
    | p :: c :: _ => (p, some c)
    | [p] => (p, none)
    | [] => (\"/tmp/kissat_m4_x64.s\", none)
  let fns := (m4Module.optInline 40).fns
  let hints := fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← match LeanQbe.T.compile x64Target.toIsa x64LegalTarget fns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let asm := Driver.emitAsm (fun c => toATTAligned c ++ \"\\n\") fns dirs
  IO.FS.writeFile outPath asm
  if let some cppPath := cppPath? then
    let cpp ← match ppTModule m4Module with
      | .ok s => pure s
      | .error e => throw (IO.userError e)
    IO.FS.writeFile cppPath cpp
"
  | ("arm64", "m4") | ("arm64", "fullm4") => .ok "import LeanQbe.T.Examples.Kissat.FullM4
import LeanQbe.T.Opt
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM4 LeanQbe.T.Arm64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => \"/tmp/kissat_m4_arm64.s\"
  let fns := (m4Module.optInline 40).fns
  let hints := fns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← match LeanQbe.T.compile armTarget.toIsa armLegalTarget fns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let pp := fun c =>
    \".p2align 2\\n\" ++ String.intercalate \"\\n\" (c.map Kraken.AArch64.Print.directive)
  IO.FS.writeFile outPath (Driver.emitAsm (fun c => pp c ++ \"\\n\") fns dirs)
"
  | ("x64", "lcnf") => .ok "import LeanQbe.T.LeanLCNF.Lower1
import LeanQbe.T.LeanLCNF.Demo
import LeanQbe.T.LeanLCNF.Coverage
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

private def emitOne (tag : String) (m : LcModule) (out : System.FilePath) : IO Unit := do
  let t0 ← IO.monoMsNow
  let tfs ← IO.ofExcept (lowerModule m)
  let fns := LeanLRC.tflatFnsToFns tfs
  let hints := fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← IO.ofExcept (LeanQbe.T.compile x64Target.toIsa x64LegalTarget fns hints)
  IO.FS.writeFile out (Driver.emitAsm (fun c => toATTAligned c ++ \"\\n\") fns dirs)
  IO.eprintln s!\"emit_x64 ({tag}): {fns.length} functions in {(← IO.monoMsNow) - t0} ms\"

def main (args : List String) : IO Unit := do
  let out : System.FilePath := args.headD \"lcnf_x64.s\"
  emitOne \"demo\" Demo.lcnfProgram out
  match args with
  | _ :: covOut :: _ => emitOne \"cov\" Coverage.covProgram covOut
  | _ => pure ()
"
  | ("arm64", "lcnf") => .ok "import LeanQbe.T.LeanLCNF.Lower1
import LeanQbe.T.LeanLCNF.Demo
import LeanQbe.T.LeanLCNF.Coverage
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Arm64

private def emitOne (tag : String) (m : LcModule) (out : System.FilePath) : IO Unit := do
  let t0 ← IO.monoMsNow
  let tfs ← IO.ofExcept (lowerModule m)
  let fns := LeanLRC.tflatFnsToFns tfs
  let hints := fns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← IO.ofExcept (LeanQbe.T.compile armTarget.toIsa armLegalTarget fns hints)
  let pp := fun c =>
    \".p2align 2\\n\" ++ String.intercalate \"\\n\" (c.map Kraken.AArch64.Print.directive)
  IO.FS.writeFile out (Driver.emitAsm (fun c => pp c ++ \"\\n\") fns dirs)
  IO.eprintln s!\"emit_arm64 ({tag}): {fns.length} functions in {(← IO.monoMsNow) - t0} ms\"

def main (args : List String) : IO Unit := do
  let out : System.FilePath := args.headD \"lcnf_arm64.s\"
  emitOne \"demo\" Demo.lcnfProgram out
  match args with
  | _ :: covOut :: _ => emitOne \"cov\" Coverage.covProgram covOut
  | _ => pure ()
"
  | ("x64", "lrc") => .ok "import LeanQbe.T.LeanLRC.ToT
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.LeanLRC LeanQbe.T.Amd64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => \"/tmp/lrc_x64.s\"
  let tfs ← match lowerLrcProgram allBenchLrcMod with
    | .ok x => pure x | .error e => throw (IO.userError e)
  let allFns := rtBase_fns ++ tflatFnsToFns tfs
  let hints := allFns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← match LeanQbe.T.compile x64Target.toIsa x64LegalTarget allFns hints with
    | .ok d => pure d | .error e => throw (IO.userError e)
  let asm := Driver.emitAsm (fun c => toATTAligned c ++ \"\\n\") allFns dirs
  IO.FS.writeFile outPath asm
"
  | ("arm64", "lrc") => .ok "import LeanQbe.T.LeanLRC.ToT
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print

open LeanQbe.T LeanQbe.T.LeanLRC LeanQbe.T.Arm64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => \"/tmp/lrc_arm64.s\"
  let tfs ← match lowerLrcProgram allBenchLrcMod with
    | .ok x => pure x | .error e => throw (IO.userError e)
  let allFns := rtBase_fns ++ tflatFnsToFns tfs
  let hints := allFns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← match LeanQbe.T.compile armTarget.toIsa armLegalTarget allFns hints with
    | .ok d => pure d | .error e => throw (IO.userError e)
  let pp := fun c =>
    \".p2align 2\\n\" ++ String.intercalate \"\\n\" (c.map Kraken.AArch64.Print.directive)
  IO.FS.writeFile outPath (Driver.emitAsm (fun c => pp c ++ \"\\n\") allFns dirs)
"
  | ("x64", "bignum") | ("x64", "t_bignum") => .ok "import LeanQbe.T.Amd64.Bignum
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T.Amd64.Bignum

private def emitFn (name body : String) : String :=
  \".text\\n.globl \" ++ name ++ \"\\n\" ++ body ++ \"\\n\"

def main (args : List String) : IO UInt32 := do
  let outDir := args.headD \"/tmp/leanqbe-tbignum\"
  IO.FS.writeFile s!\"{outDir}/mul4x4_x64.s\"
    (emitFn \"mul4x4\" (LeanQbe.T.Amd64.toATTAligned mul4x4Compiled.code))
  IO.FS.writeFile s!\"{outDir}/addMod25519_x64.s\"
    (emitFn \"addMod25519\" (LeanQbe.T.Amd64.toATTAligned addMod25519Compiled.code))
  IO.FS.writeFile s!\"{outDir}/subMod25519_x64.s\"
    (emitFn \"subMod25519\" (LeanQbe.T.Amd64.toATTAligned subMod25519Compiled.code))
  return 0
"
  | ("arm64", "bignum") | ("arm64", "t_bignum") => .ok "import LeanQbe.T.Arm64.Bignum
import Kraken.AArch64.Print

open LeanQbe.T.Arm64.Bignum

private def emitFn (name : String) (body : List String) : String :=
  \".text\\n.globl \" ++ name ++ \"\\n.p2align 2\\n\" ++
    String.intercalate \"\\n\" body ++ \"\\n\"

def main (args : List String) : IO UInt32 := do
  let outDir := args.headD \"/tmp/leanqbe-tbignum\"
  IO.FS.writeFile s!\"{outDir}/mul4x4_arm64.s\"
    (emitFn \"mul4x4\" (mul4x4Compiled.code.map Kraken.AArch64.Print.directive))
  IO.FS.writeFile s!\"{outDir}/addMod25519_arm64.s\"
    (emitFn \"addMod25519\" (addMod25519Compiled.code.map Kraken.AArch64.Print.directive))
  IO.FS.writeFile s!\"{outDir}/subMod25519_arm64.s\"
    (emitFn \"subMod25519\" (subMod25519Compiled.code.map Kraken.AArch64.Print.directive))
  return 0
"
  | ("x64", "chacha") | ("x64", "t_chacha") => .ok "import LeanQbe.T.Amd64.ChaCha
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T.Amd64.ChaCha

def main (args : List String) : IO UInt32 := do
  let outDir := args.headD \"/tmp/leanqbe-tchacha\"
  let asm := \".text\\n.globl chacha20Block\\n\" ++
    LeanQbe.T.Amd64.toATTAligned compiled.code ++ \"\\n\"
  IO.FS.writeFile s!\"{outDir}/chacha_x64.s\" asm
  return 0
"
  | ("arm64", "chacha") | ("arm64", "t_chacha") => .ok "import LeanQbe.T.Arm64.ChaCha
import Kraken.AArch64.Print

open LeanQbe.T.Arm64.ChaCha

def main (args : List String) : IO UInt32 := do
  let outDir := args.headD \"/tmp/leanqbe-tchacha\"
  let asm :=
    \".text\\n.globl chacha20Block\\n.p2align 2\\n\" ++
      String.intercalate \"\\n\" (compiled.code.map Kraken.AArch64.Print.directive) ++ \"\\n\"
  IO.FS.writeFile s!\"{outDir}/chacha_arm64.s\" asm
  return 0
"
  | _ => .error s!"unknown (arch, suite) combination: ({arch}, {suite})"

def normalizeArch (a : String) : Option String :=
  match a.toLower with
  | "x64" | "x86_64" | "x86-64" | "amd64" => some "x64"
  | "arm64" | "aarch64" | "arm" => some "arm64"
  | _ => none

partial def parseArgs (args : List String) : Except String (String × String × List String) := do
  let mut arch? : Option String := none
  let mut suite? : Option String := none
  let mut rest : List String := []
  let mut cur := args
  while true do
    match cur with
    | "--arch" :: a :: tl =>
      arch? := normalizeArch a
      cur := tl
    | "--suite" :: s :: tl =>
      suite? := some s.toLower
      cur := tl
    | hd :: tl =>
      rest := rest ++ [hd]
      cur := tl
    | [] =>
      break
  let arch ← match arch? with
    | some a => pure a
    | none => .error "missing or invalid --arch <x64|arm64>"
  let suite ← match suite? with
    | some s => pure s
    | none => .error "missing --suite <kissat|coreplus|plain|m3|m4|lcnf|lrc|bignum|chacha>"
  return (arch, suite, rest)

def main (args : List String) : IO UInt32 := do
  let (arch, suite, restArgs) ← match parseArgs args with
    | .ok res => pure res
    | .error err =>
      IO.eprintln s!"ERROR: {err}"
      IO.eprintln "usage: lake env lean --run test/common/emit.lean --arch <x64|arm64> --suite <suite> [args...]"
      return 2
  let code ← match renderCode arch suite with
    | .ok c => pure c
    | .error err =>
      IO.eprintln s!"ERROR: {err}"
      return 2
  let (cmd, cmdPrefix) ← getLeanCmd
  let tmpPath := s!"/tmp/leanqbe_emit_{arch}_{suite}_{← IO.monoMsNow}.lean"
  IO.FS.writeFile tmpPath code
  let child ← IO.Process.spawn {
    cmd := cmd
    args := cmdPrefix ++ #["--run", tmpPath] ++ restArgs.toArray
  }
  let rc ← child.wait
  try IO.FS.removeFile tmpPath catch _ => pure ()
  return rc
