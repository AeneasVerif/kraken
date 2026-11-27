module

public meta import Lean

public meta section

open Lean Meta

initialize kreduceExtension : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s n => s.insert n
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `kreduce
  descr := "declarations to be reduced in the goal as part of the kstep tactic"
  add := fun declName _stx _kind => do
    modifyEnv fun env => kreduceExtension.addEntry env declName
}

initialize kmemExtension : SimpleScopedEnvExtension (Sym.Pattern × Name) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun tree (pat, declName) => Sym.insertPattern tree pat declName
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `kmem
  descr := "memory specification lemmas in separation logic, to be leveraged by the kstep tactic"
  add := fun declName _stx kind => do
    let (pat, _) ← (Sym.mkEqPatternFromDecl declName).run'
    kmemExtension.add (pat, declName) kind
}

initialize ksimpExt : Sym.Simp.SymSimpExtension ←
  Sym.Simp.registerSymSimpAttr `ksimp "simp theorems used by kstep"
