module

public meta import Lean

public meta section

open Lean Meta

initialize kstepExtension : TagDeclarationExtension ← mkTagDeclarationExtension

initialize registerBuiltinAttribute {
  name := `kstep
  descr := "declarations to be reduced in the goal as part of the kstep tactic"
  add := fun declName _stx _kind => do
    modifyEnv fun env => kstepExtension.tag env declName
}

initialize kspecExtension : SimpleScopedEnvExtension (Sym.Pattern × Name) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun tree (pat, declName) => Sym.insertPattern tree pat declName
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `kspec
  descr := "specification lemmas for built-in, in separation logic, to be leveraged by the kstep tactic"
  add := fun declName _stx kind => do
    let (pat, _) ← (Sym.mkEqPatternFromDecl declName).run'
    kspecExtension.add (pat, declName) kind
}

initialize ksimpExt : Sym.Simp.SymSimpExtension ←
  Sym.Simp.registerSymSimpAttr `ksimp "simp theorems used by kstep"
