module

public import Lean

/-!
Single-session compiled `.olean` axiom and `isUnsafe` auditor (`audit_axioms`).

Reads a manifest with `GROUP <name>` headers followed by `<Module> <Const>` lines,
loads each group's public `.olean` closure via
`importModules (loadExts := true) (level := .exported) (trustLevel := 0)`, and verifies
every headline constant in a single pass:
1. Constant exists in the loaded environment (`env.find?`).
2. `Lean.collectAxioms` (using Lean's kernel-exported `exportedAxiomsExt`, which
   records transitive axioms across both public and private proof bodies) returns
   exclusively standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
3. Single-pass O(V + E) iterative DFS with a shared `Std.HashSet Name` verifies
   `!ci.isUnsafe` / `!v.isUnsafe` across all reachable exported constants.

When a manifest contains multiple groups, `audit_axioms` dispatches bounded-parallel
per-group child workers (`--group <name>`) so each `importModules` runs in a clean
environment without accumulating compacted `.olean` regions across groups.
-/

set_option autoImplicit false

open Lean

private def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def parseName (s : String) : Name :=
  (s.splitOn ".").foldl (fun acc part => Name.str acc part) Name.anonymous

/-- Read-only `MonadEnv` wrapper over an imported `Environment` for `Lean.collectAxioms`. -/
private abbrev AuditReadM := ReaderT Environment Id

private instance : MonadEnv AuditReadM where
  getEnv := read
  modifyEnv _ := pure ()

/-- Iterative O(V + E) `isUnsafe` check across reachable exported constants.
    (Under `level := .exported`, non-`@[expose]` definitions and theorems appear as
    `.axiomInfo` stubs whose true transitive axioms are audited by `Lean.collectAxioms`
    via `exportedAxiomsExt`; their `isUnsafe` flag is preserved on the stub.) -/
private def checkUnsafeRec (env : Environment) (root : Name)
    (visited : Std.HashSet Name) (errors : Array String) :
    Std.HashSet Name × Array String := Id.run do
  let mut vis := visited
  let mut errs := errors
  let mut stack : Array Name := #[root]
  while !stack.isEmpty do
    let some c := stack.back? | break
    stack := stack.pop
    if vis.contains c then
      continue
    vis := vis.insert c
    match env.find? c with
    | none => pure ()
    | some (.axiomInfo v) =>
      if v.isUnsafe then
        errs := errs.push s!"unsafe decl {c} (from {root})"
      for d in v.type.getUsedConstants do
        if !vis.contains d then
          stack := stack.push d
    | some ci =>
      if ci.isUnsafe then
        errs := errs.push s!"unsafe decl {c} (from {root})"
      for d in ci.type.getUsedConstants do
        if !vis.contains d then
          stack := stack.push d
      match ci.value? (allowOpaque := true) with
      | some val =>
        for d in val.getUsedConstants do
          if !vis.contains d then
            stack := stack.push d
      | none =>
        match ci with
        | .inductInfo v =>
          for d in v.ctors do
            if !vis.contains d then
              stack := stack.push d
        | .ctorInfo v =>
          if !vis.contains v.induct then
            stack := stack.push v.induct
        | .recInfo v =>
          for d in v.all do
            if !vis.contains d then
              stack := stack.push d
        | _ => pure ()
  return (vis, errs)

private def auditEnv (grp : String) (mods : Array Name) (consts : Array Name) :
    IO (Nat × Bool) := do
  let imps : Array Import := mods.map fun m => { module := m }
  unsafe enableInitializersExecution
  let env ← importModules imps {} (trustLevel := 0) (loadExts := true) (level := .exported)
  let mut vis : Std.HashSet Name := {}
  let mut errs : Array String := #[]
  let mut checked := 0
  let mut failed := false
  for nm in consts do
    match env.find? nm with
    | none =>
      IO.eprintln s!"FAIL [{grp}] missing constant: {nm}"
      failed := true
    | some _ =>
      let axs : Array Name := (Lean.collectAxioms nm : AuditReadM (Array Name)).run env
      for ax in axs do
        if !allowedAxioms.contains ax then
          errs := errs.push s!"disallowed axiom {ax} (from {nm})"
      let (vis', errs') := checkUnsafeRec env nm vis errs
      vis := vis'
      errs := errs'
      checked := checked + 1
  for e in errs do
    IO.eprintln s!"FAIL [{grp}] {e}"
    failed := true
  let msg := s!"audit_axioms [{grp}]: {checked} theorems checked"
  IO.println s!"{msg} (visited={vis.size}, bad={errs.size})"
  return (checked, failed)

private def parseTotalFromOutput (out : String) : Nat :=
  let prefix_ := "audit_axioms: TOTAL "
  (out.splitOn "\n").foldl (init := 0) fun acc ln =>
    if ln.startsWith prefix_ then
      let rest := (ln.drop prefix_.length).toString
      match (rest.splitOn " ").head? >>= String.toNat? with
      | some n => n
      | none => acc
    else
      acc

private def auditGroup (manifestPath : String) (grp : String)
    (entries : Array (Name × Name)) : IO (Nat × Bool) := do
  if entries.isEmpty then
    return (0, false)
  let mut modSeen : Std.HashSet Name := {}
  let mut mods : Array Name := #[]
  let mut consts : Array Name := #[]
  for (m, c) in entries do
    if !modSeen.contains m then
      modSeen := modSeen.insert m
      mods := mods.push m
    consts := consts.push c
  try
    auditEnv grp mods consts
  catch e =>
    if mods.size <= 1 then
      IO.eprintln s!"FAIL [{grp}] importModules failed: {e}"
      return (0, true)
    IO.println s!"NOTE [{grp}]: batch import failed ({e}); retrying per-module"
    let exe ← IO.appPath
    let mut total := 0
    let mut anyFail := false
    for m in mods do
      let res ← IO.Process.output {
        cmd := exe.toString
        args := #["--module", grp, m.toString, manifestPath]
      }
      if !res.stdout.isEmpty then IO.print res.stdout
      if !res.stderr.isEmpty then IO.eprint res.stderr
      total := total + parseTotalFromOutput res.stdout
      if res.exitCode != 0 then
        anyFail := true
    return (total, anyFail)

private def parseManifest (content : String) :
    Except String (Array (String × Array (Name × Name))) := Id.run do
  let mut groups : Array (String × Array (Name × Name)) := #[]
  let mut curName : Option String := none
  let mut curEntries : Array (Name × Name) := #[]
  let mut lineNo := 0
  for raw in content.splitOn "\n" do
    lineNo := lineNo + 1
    let line := raw.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then
      continue
    let parts := (line.splitOn " ").filter (!·.isEmpty)
    if parts[0]? == some "GROUP" then
      if let some g := curName then
        groups := groups.push (g, curEntries)
      match parts[1]? with
      | some g =>
        curName := some g
        curEntries := #[]
      | none =>
        return .error s!"line {lineNo}: GROUP missing name"
    else
      match curName, parts[0]?, parts[1]? with
      | some _, some modStr, some constStr =>
        curEntries := curEntries.push (parseName modStr, parseName constStr)
      | none, _, _ =>
        return .error s!"line {lineNo}: entry before GROUP header"
      | _, _, _ =>
        return .error s!"line {lineNo}: malformed entry `{line}`"
  if let some g := curName then
    groups := groups.push (g, curEntries)
  return .ok groups

private def childStdio : IO.Process.StdioConfig :=
  { stdin := .null, stdout := .piped, stderr := .piped }

private def runGroupsParallel (manifestPath : String)
    (groups : Array (String × Array (Name × Name))) : IO (Nat × Bool) := do
  let exe ← IO.appPath
  let maxJobs : Nat := 6
  let mut total := 0
  let mut failed := false
  let mut idx := 0
  while idx < groups.size do
    let endIdx := min groups.size (idx + maxJobs)
    let mut children : Array (IO.Process.Child childStdio) := #[]
    for j in [idx:endIdx] do
      let (grp, _) := groups[j]!
      let child ← IO.Process.spawn {
        toStdioConfig := childStdio
        cmd := exe.toString
        args := #["--group", grp, manifestPath]
      }
      children := children.push child
    for child in children do
      let errTask ← IO.asTask child.stderr.readToEnd
      let stdout ← child.stdout.readToEnd
      let stderr ← IO.ofExcept errTask.get
      let rc ← child.wait
      if !stdout.isEmpty then
        for ln in stdout.splitOn "\n" do
          if !ln.isEmpty && !ln.startsWith "audit_axioms: TOTAL " then
            IO.println ln
      if !stderr.isEmpty then
        IO.eprint stderr
      total := total + parseTotalFromOutput stdout
      if rc != 0 then
        failed := true
    idx := endIdx
  return (total, failed)

public def main (args : List String) : IO UInt32 := do
  match args with
  | ["--group", targetGrp, manifestPath] =>
    initSearchPath (← findSysroot)
    let content ← IO.FS.readFile manifestPath
    match parseManifest content with
    | .error err =>
      IO.eprintln s!"FAIL: invalid manifest {manifestPath}: {err}"
      return 2
    | .ok groups =>
      let some (_, entries) := groups.find? (fun p => p.1 == targetGrp)
        | IO.eprintln s!"FAIL: group not found in manifest: {targetGrp}"
          return 2
      let (cnt, failed) ← auditGroup manifestPath targetGrp entries
      if failed then
        return 1
      IO.println s!"audit_axioms: TOTAL {cnt} theorems verified (0 unsafe, <= std3)"
      return 0
  | ["--module", targetGrp, targetMod, manifestPath] =>
    initSearchPath (← findSysroot)
    let content ← IO.FS.readFile manifestPath
    match parseManifest content with
    | .error err =>
      IO.eprintln s!"FAIL: invalid manifest {manifestPath}: {err}"
      return 2
    | .ok groups =>
      let some (_, entries) := groups.find? (fun p => p.1 == targetGrp)
        | IO.eprintln s!"FAIL: group not found in manifest: {targetGrp}"
          return 2
      let modName := parseName targetMod
      let consts := (entries.filter (fun p => p.1 == modName)).map (·.2)
      let (cnt, failed) ← auditEnv s!"{targetGrp}:{targetMod}" #[modName] consts
      if failed then
        return 1
      IO.println s!"audit_axioms: TOTAL {cnt} theorems verified (0 unsafe, <= std3)"
      return 0
  | [manifestPath] =>
    let content ← IO.FS.readFile manifestPath
    match parseManifest content with
    | .error err =>
      IO.eprintln s!"FAIL: invalid manifest {manifestPath}: {err}"
      return 2
    | .ok groups =>
      let (total, failed) ←
        if groups.size <= 1 then
          initSearchPath (← findSysroot)
          match groups[0]? with
          | none => pure (0, false)
          | some (grp, entries) => auditGroup manifestPath grp entries
        else
          runGroupsParallel manifestPath groups
      if failed then
        IO.eprintln s!"audit_axioms: FAILED (checked {total} theorems)"
        return 1
      IO.println s!"audit_axioms: TOTAL {total} theorems verified (0 unsafe, <= std3)"
      return 0
  | _ =>
    IO.eprintln "Usage: audit_axioms <manifest_path>"
    return 2
