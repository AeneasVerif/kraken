set_option autoImplicit false

private def detectHostArch : IO String := do
  let out ← IO.Process.output { cmd := "uname", args := #["-m"] }
  let m := out.stdout.trimAscii.toString
  if m == "aarch64" || m == "arm64" then pure "arm64"
  else if m == "x86_64" || m == "amd64" then pure "x64"
  else throw (IO.userError s!"unsupported host arch: {m}")

private def findScript (dir? : Option String) (name : String) : IO System.FilePath := do
  if let some d := dir? then
    let p : System.FilePath := System.FilePath.mk d / name
    if ← p.pathExists then return p
  for cand in #[System.FilePath.mk "c" / name, System.FilePath.mk "bv_decide_qbe" / "c" / name] do
    if ← cand.pathExists then return cand
  throw (IO.userError s!"cannot locate {name}")

private partial def parseArgs (arch? : Option String) (dir? : Option String)
    (out? : Option String) : List String → IO (Option String × Option String × String)
  | [] =>
    match out? with
    | some o => pure (arch?, dir?, o)
    | none => throw (IO.userError "usage: emit_asm.lean [--arch x64|arm64] [--dir <c_dir>] [-o] <out.s>")
  | "--arch" :: a :: rest => parseArgs (some a) dir? out? rest
  | "--dir" :: d :: rest => parseArgs arch? (some d) out? rest
  | "-o" :: o :: rest => parseArgs arch? dir? (some o) rest
  | o :: rest =>
    if o.startsWith "-" then throw (IO.userError s!"unknown flag: {o}")
    else parseArgs arch? dir? (some o) rest

def main (args : List String) : IO Unit := do
  let (arch?, dir?, outPath) ← parseArgs none none none args
  let arch ← match arch? with
    | some a =>
      let al := a.toLower
      if al == "x64" || al == "amd64" || al == "x86_64" then pure "x64"
      else if al == "arm64" || al == "aarch64" then pure "arm64"
      else throw (IO.userError s!"unknown --arch '{a}' (expected x64 | arm64)")
    | none => detectHostArch
  let scriptName := if arch == "arm64" then "emit_asm_arm64.lean" else "emit_asm_x64.lean"
  let scriptPath ← findScript dir? scriptName
  let child ← IO.Process.output {
    cmd := "lean"
    args := #["--run", scriptPath.toString, outPath]
  }
  if child.exitCode != 0 then
    throw (IO.userError s!"emit_asm ({arch}) failed (exit {child.exitCode}):\n{child.stderr}{child.stdout}")
