import LeanQbe.Print
import LeanQbe.Main
import LeanQbe.Amd64.Targ
import LeanQbe.Examples.UnionFind
import LeanQbe.Examples.LratRup
import LeanQbe.Examples.LratTrim
import Kraken.X64.PrintATT

open LeanQbe

def emitAsm (fs : List Fn) (code : List Amd64.isa.Directive) : String :=
  let globls := fs.map (fun f => s!".globl {f.name}\n") |>.foldl (· ++ ·) ""
  ".text\n" ++ globls ++ Kraken.X64.toATT code ++ "\n"

def main (args : List String) : IO UInt32 := do
  let outDir := args.headD "/tmp"
  let ufFns : List Fn := [⟨"find", UnionFind.find⟩, ⟨"union", UnionFind.union⟩, ⟨"unionInline", UnionFind.unionInline⟩]
  let ufLeafFns : List Fn := [⟨"find", UnionFind.find⟩, ⟨"unionInline", UnionFind.unionInline⟩]
  match Print.module ufFns with
  | .ok s => IO.FS.writeFile s!"{outDir}/uf.ssa" s
  | .error e => IO.eprintln s!"uf.ssa error: {e}"; return 1
  match Print.module LratTrim.lratTrimFns with
  | .ok s => IO.FS.writeFile s!"{outDir}/lrat_trim.ssa" s
  | .error e => IO.eprintln s!"lrat_trim.ssa error: {e}"; return 1
  match compile Amd64.isa ufLeafFns with
  | .ok c => IO.FS.writeFile s!"{outDir}/uf_leaf.s" (emitAsm ufLeafFns c)
  | .error e => IO.eprintln s!"uf_leaf.s note: {e}"
  match compile Amd64.isa ufFns with
  | .ok c => IO.FS.writeFile s!"{outDir}/uf.s" (emitAsm ufFns c)
  | .error e => IO.eprintln s!"uf.s (awaiting R3 calls): {e}"
  match compile Amd64.isa LratTrim.lratTrimFns with
  | .ok c => IO.FS.writeFile s!"{outDir}/lrat_trim.s" (emitAsm LratTrim.lratTrimFns c)
  | .error e => IO.eprintln s!"lrat_trim.s (awaiting R3 calls/exits/spills): {e}"
  return 0
