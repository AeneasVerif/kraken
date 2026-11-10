import LeanQbe.Parse
import LeanQbe.Print
import LeanQbe.Main
import LeanQbe.Amd64.Targ
import Kraken.X64.PrintATT

/-!
Feeds QBE's own test programs through our front end and compiler:
1. parse each `.ssa` file with `LeanQbe.Parse`;
2. print the resulting PHOAS functions back with `LeanQbe.Print` (for stock QBE);
3. compile the resulting PHOAS functions with our verified pipeline `LeanQbe.compile Amd64.isa`
   (`Func.opt` + `Spill.hints` + `Rega.lowerFn`) and print x64 assembly via `Kraken.X64.toATT`;
4. write the C driver embedded in the file (between `# >>> driver` and `# <<<`).
Driven by `scripts/qbe_tests.sh`.

Usage: `lake env lean --run scripts/QbeTests.lean <outdir> <file.ssa>…`; prints one status line per file.
-/

open LeanQbe

def emitAsm (fs : List Fn) (code : List Amd64.isa.Directive) : String :=
  let globls := fs.map (fun f => s!".globl {f.name}\n") |>.foldl (· ++ ·) ""
  ".text\n" ++ globls ++ Kraken.X64.toATT code ++ "\n"

def driver (src : String) : Option String := do
  let lines := src.splitOn "\n"
  let start ← lines.findIdx? (·.startsWith "# >>> driver")
  let rest := lines.drop (start + 1)
  let stop := (rest.findIdx? (·.startsWith "# <<<")).getD rest.length
  let body := (rest.take stop).map fun l => if l.startsWith "# " then l.drop 2 |>.toString
    else if l.startsWith "#" then l.drop 1 |>.toString else l
  return "\n".intercalate body ++ "\n"

def main (argv : List String) : IO UInt32 := do
  let dir : System.FilePath := argv.headD "."
  IO.FS.createDirAll dir
  for path in argv.drop 1 do
    let src ← IO.FS.readFile path
    let base := (System.FilePath.mk path).fileStem.getD path
    match Parse.parseFlat src with
    | .error e => IO.println s!"SKIP {base}: {e}"
    | .ok fs =>
      let fns := fs.map Parse.toFn
      match Print.module fns with
      | .error e => IO.println s!"SKIP {base}: print: {e}"
      | .ok il =>
        -- globals used as operands: their addresses come from C getters (`Parse.addrFn`)
        let globals := ((il.splitOn "call $leanqbe_addr_").drop 1).map (fun s => (s.takeWhile (· != '(')).toString)
          |>.eraseDups
        let own := globals.filter fun g => (src.splitOn s!"data ${g} ").length > 1
        match driver src with
        | none => IO.println s!"SKIP {base}: no driver"
        | some d =>
          if !own.isEmpty then IO.println s!"SKIP {base}: uses its own data {own}" else
          IO.FS.writeFile (dir / s!"{base}.ssa") il
          IO.FS.writeFile (dir / s!"{base}_driver.c") d
          IO.FS.writeFile (dir / s!"{base}_addr.c") <| String.join <| globals.map fun g =>
            s!"extern char {g};\nvoid *leanqbe_addr_{g}(void) \{ return &{g}; }\n"
          match compile Amd64.isa fns with
          | .ok code =>
            IO.FS.writeFile (dir / s!"{base}_leanqbe.s") (emitAsm fns code)
            IO.println s!"OK {base}: {fs.length} function(s) (leanqbe: {code.length} directives)"
          | .error e =>
            IO.println s!"OK {base}: {fs.length} function(s) (leanqbe skip: {e})"
  return 0
