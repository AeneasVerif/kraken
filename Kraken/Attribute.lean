module

public meta import Lean

public meta section

open Lean

initialize kstepExtension : TagDeclarationExtension ← mkTagDeclarationExtension

initialize registerBuiltinAttribute {
  name := `kstep
  descr := "declarations to be reduced in the goal as part of the kstep tactic"
  add := fun declName _stx _kind => do
    modifyEnv fun env => kstepExtension.addEntry env declName
}

initialize kspecExtension : TagDeclarationExtension ← mkTagDeclarationExtension

initialize registerBuiltinAttribute {
  name := `kspec
  descr := "specification lemmas for built-in, in separation logic, to be leveraged by the kstep tactic"
  add := fun declName _stx _kind => do
    modifyEnv fun env => kspecExtension.addEntry env declName
}

open Lean.Meta

initialize ksimpExt : Sym.Simp.SymSimpExtension ←
  Sym.Simp.registerSymSimpAttr `ksimp "simp theorems used by kstep"
