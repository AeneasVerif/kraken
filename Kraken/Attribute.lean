import Lean

open Lean

initialize kstepExtension : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    name := `kstepExtension
    addEntry := fun s n => s.insert n
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `kstep
  descr := "mark declarations for kstep tactic"
  add := fun declName _stx _kind => do
    modifyEnv fun env => kstepExtension.addEntry env declName
}
