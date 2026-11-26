module

/-!
# Pure FFI Bindings for `libkissat_qbe` (`S1`)

Provides `SolveResult`, `private @[extern]` bindings for `leanqbe_alloc_work_buf` and
`leanqbe_solve_dimacs_bytes`, and a deterministic doubling-retry helper `solveDimacs`.
-/

set_option autoImplicit false

public section

namespace BvDecideQbe

inductive SolveResult where
  | unsat
  | sat (model : ByteArray)
  | unknown
  | workTooSmall
  deriving BEq, Inhabited

instance : Repr SolveResult where
  reprPrec r _ :=
    match r with
    | .unsat => "SolveResult.unsat"
    | .sat m => s!"SolveResult.sat (ByteArray.size={m.size})"
    | .unknown => "SolveResult.unknown"
    | .workTooSmall => "SolveResult.workTooSmall"

@[extern "leanqbe_alloc_work_buf"]
private opaque allocWorkBuf (n : UInt64) : ByteArray

@[extern "leanqbe_solve_dimacs_bytes"]
private opaque solveDimacsRaw (cnf : @& ByteArray) (work : ByteArray) (fuel : UInt64) : SolveResult

/-- Default initial scratch workspace size (`256 KiB`). -/
def defaultInitWorkBytes : UInt64 := 256 * 1024

/-- Default maximum scratch workspace size (`512 MiB`). -/
def defaultMaxWorkBytes : UInt64 := 512 * 1024 * 1024

/-- Default Kissat fuel budget. -/
def defaultFuel : UInt64 := 100000000

/-- Solve ASCII DIMACS CNF bytes with deterministic `2x` workspace retry on `.workTooSmall`. -/
def solveDimacsWith (cnf : ByteArray) (initWorkBytes maxWorkBytes fuel : UInt64) : SolveResult :=
  go 32 initWorkBytes
where
  go : Nat → UInt64 → SolveResult
    | 0, _ => .workTooSmall
    | steps + 1, curWork =>
      let work := allocWorkBuf curWork
      match solveDimacsRaw cnf work fuel with
      | .workTooSmall =>
        if curWork < maxWorkBytes then
          let nextWork :=
            if curWork > maxWorkBytes / 2 then maxWorkBytes else curWork * 2
          if nextWork <= curWork then .workTooSmall else go steps nextWork
        else
          .workTooSmall
      | res => res

/-- Solve ASCII DIMACS CNF bytes using deterministic default workspace sizing (`256 KiB .. 512 MiB`). -/
def solveDimacs (cnf : ByteArray) (fuel : UInt64 := defaultFuel) : SolveResult :=
  solveDimacsWith cnf defaultInitWorkBytes defaultMaxWorkBytes fuel

end BvDecideQbe
