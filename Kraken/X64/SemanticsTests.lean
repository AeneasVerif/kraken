module

import Kraken.X64.Semantics
meta import Kraken.X64.Semantics

/-! Concrete-evaluation tests of semantics that the native asm tests can't observe. -/

/-- The read and the write access checks, as `(address, width)` lists, that `e` requests before
it is `done`, granting each one; `none` if it isn't `done` then. -/
private partial def accessChecks :
    Effects → Option (List (BitVec 64 × Width) × List (BitVec 64 × Width))
  | .done _ => some ([], [])
  | .require_read_access addr w ok => (accessChecks (ok ())).map fun (rs, ws) => ((addr, w) :: rs, ws)
  | .require_write_access addr w ok => (accessChecks (ok ())).map fun (rs, ws) => (rs, (addr, w) :: ws)
  | _ => none

/-- 64 bytes of data memory at `0x1000`. -/
private def s : MachineData := { dmem := (List.replicate 64 0).At 0x1000 }

-- The asm tests' runner grants every access check. A vector load or store requests access to
-- every byte it touches, 8 bytes at a time.
#guard accessChecks (s.loadAvx 0x1000 .W128 fun _ s => .done (s, 0)) ==
  some ([(0x1000, .W64), (0x1008, .W64)], [])
#guard accessChecks (s.loadAvx 0x1000 .W256 fun _ s => .done (s, 0)) ==
  some ([(0x1000, .W64), (0x1008, .W64), (0x1010, .W64), (0x1018, .W64)], [])
#guard accessChecks (s.loadAvx 0x1000 .W512 fun _ s => .done (s, 0)) ==
  some ([(0x1000, .W64), (0x1008, .W64), (0x1010, .W64), (0x1018, .W64),
         (0x1020, .W64), (0x1028, .W64), (0x1030, .W64), (0x1038, .W64)], [])
#guard accessChecks (s.storeAvx (w := .W128) 0x1000 0 fun s => .done (s, 0)) ==
  some ([], [(0x1000, .W64), (0x1008, .W64)])
#guard accessChecks (s.storeAvx (w := .W256) 0x1000 0 fun s => .done (s, 0)) ==
  some ([], [(0x1000, .W64), (0x1008, .W64), (0x1010, .W64), (0x1018, .W64)])
#guard accessChecks (s.storeAvx (w := .W512) 0x1000 0 fun s => .done (s, 0)) ==
  some ([], [(0x1000, .W64), (0x1008, .W64), (0x1010, .W64), (0x1018, .W64),
             (0x1020, .W64), (0x1028, .W64), (0x1030, .W64), (0x1038, .W64)])
