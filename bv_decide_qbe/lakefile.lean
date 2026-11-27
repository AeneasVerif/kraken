import Lake
open Lake DSL System

package bv_decide_qbe where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
  enableArtifactCache := true
  restoreAllArtifacts := true

require LeanQbe from ".."

private def hostArch : String :=
  if System.Platform.target.startsWith "aarch64" || System.Platform.target.startsWith "arm64" then
    "arm64"
  else
    "x64"

target kissat_asm (pkg : NPackage __name__) : FilePath := do
  let arch := hostArch
  let needMods : Array Lean.Name :=
    #[ `LeanQbeTest.T.BitblastCertCommon
     , `LeanQbe.T.Examples.Kissat.Plain
     , `LeanQbe.T.Examples.Bitblast.Src.Full
     , `LeanQbe.T.Driver
     ] ++ if arch == "arm64" then
       #[`LeanQbeTest.T.BitblastCertArm64, `LeanQbe.T.Arm64.Isa, `Kraken.AArch64.Print]
     else
       #[`LeanQbeTest.T.BitblastCertX64, `LeanQbe.T.Amd64.Isa, `LeanQbe.T.Amd64.PrintATTAlign]
  let modJobs ← needMods.mapM fun modName => do
    let some mod ← findModule? modName
      | error s!"kissat_asm: module '{modName}' not found in workspace"
    mod.olean.fetch
  let scriptJob ← inputTextFile (pkg.dir / "c" / "emit_asm.lean")
  let archScriptJob ← inputTextFile (pkg.dir / "c" / s!"emit_asm_{arch}.lean")
  let depJob := Job.collectArray (modJobs ++ #[scriptJob, archScriptJob])
  let outFile := pkg.buildDir / "c" / "kissat_solver.s"
  depJob.mapM fun _ => do
    addPlatformTrace
    addPureTrace arch "arch"
    let art ← buildArtifactUnlessUpToDate outFile (build := do
      let lean ← getLeanInstall
      let leanPath ← getAugmentedLeanPath
      createParentDirs outFile
      proc {
        cmd := lean.lean.toString
        args := #[ "--run"
                 , (pkg.dir / "c" / "emit_asm.lean").toString
                 , "--arch", arch
                 , "--dir", (pkg.dir / "c").toString
                 , outFile.toString ]
        env := #[("LEAN_PATH", leanPath.toString)]
      }) (text := true) (ext := "s") (restore := true)
    return art.path

target kissat_asm_o (pkg : NPackage __name__) : FilePath := do
  let srcJob ← kissat_asm.fetch
  let oFile := pkg.buildDir / "c" / "kissat_solver.o"
  buildO oFile srcJob #[] #["-fPIC"] "cc"

target kissat_ffi_o (pkg : NPackage __name__) : FilePath := do
  let srcJob ← inputTextFile (pkg.dir / "c" / "kissat_ffi.c")
  let oFile := pkg.buildDir / "c" / "kissat_ffi.o"
  let lean ← getLeanInstall
  buildO oFile srcJob #[]
    #["-O2", "-fPIC", "-Wall", "-Wextra", "-Werror", "-I", lean.includeDir.toString] "cc"

target libkissat_qbe_static (pkg : NPackage __name__) : FilePath := do
  let asmO ← kissat_asm_o.fetch
  let ffiO ← kissat_ffi_o.fetch
  let libFile := pkg.sharedLibDir / nameToStaticLib "kissat_qbe"
  buildStaticLib libFile #[asmO, ffiO]

target libkissat_qbe : Dynlib := do
  let staticJob ← libkissat_qbe_static.fetch
  let dynJob ← buildLeanSharedLibOfStatic staticJob
  dynJob.mapM fun path => return { path, name := "kissat_qbe" }

lean_lib BvDecideQbeNative where
  roots := #[]
  globs := #[`BvDecideQbe.FFI, `BvDecideQbe.Encode, `BvDecideQbe.Counterexample]
  precompileModules := true
  moreLinkLibs := #[libkissat_qbe]

@[default_target]
lean_lib BvDecideQbe where
  roots := #[]
  globs := #[`BvDecideQbe.Prover, `BvDecideQbe.Cegar, `BvDecideQbe.Tactic]

lean_lib BvDecideQbeTest where
  roots := #[]
  globs := #[Glob.submodules `BvDecideQbeTest]
