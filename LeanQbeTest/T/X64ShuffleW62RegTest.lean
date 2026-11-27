/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Amd64.Isa
public import LeanQbe.T.Driver
public import LeanQbe.T.RegaW62
public import LeanQbe.T.Spill
meta import LeanQbe.T.Amd64.Isa
meta import LeanQbe.T.Driver
meta import LeanQbe.T.RegaW62
meta import LeanQbe.T.Spill

/-!
# x86-64 Wave 6.2-A `jump: shuffle` Regression Tests (`addSlotEntry` + `.gprZ`)

Guards against the Wave 6.2-A `OPT-10a` regression where `Rega.addSlotEntry` overwrote an existing
`.gprZ` slot entry (`SlotEntry.gprZ`) with a fresh `.gpr [sa]` entry when a non-`liveZ` variable
(such as a coalesced `zext 32 64` `i64` copy) shared a 64-bit stack slot with a preceding `liveZ`
`i32` variable in `Entry.live` / `Entry.ploc`, causing subsequent jumps requiring both variables
to fail with `jump: shuffle`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.X64ShuffleW62RegTest

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Rega

/-! ## 1. Unit Guards on `addSlotEntry`, `buildEntryBaseZ`, `bindBlockParamsZ`, `shuffle` -/

private meta def emptySt : SymState x64Isa :=
  { regs := [], slots := .empty, defs := .empty, vecWidths := .empty }

private meta def sharedLive : List (SymArg × x64Isa.Loc) :=
  [(.var 0, .slot 0 .w64), (.var 1, .slot 0 .w64)]

private meta def sharedEntry : Entry x64Isa.Reg x64Isa.VReg x64Isa.Cond :=
  { live := sharedLive, ploc := [], liveZ := [true, false], plocZ := [] }

-- `addSlotEntry` preserves an existing `.gprZ` entry on the same 64-bit slot.
#guard match addSlotZEntry .empty (.var 0) true 0 .w64 .empty with
  | some sl1 =>
    match addSlotEntry .empty (.var 1) 0 .w64 sl1 with
    | some sl2 =>
      let st : SymState x64Isa := { emptySt with slots := sl2 }
      holdsLoc x64Isa st (.var 0) (.slot 0 .w64) &&
        holdsLoc x64Isa st (.var 1) (.slot 0 .w64) &&
        holdsZLoc x64Isa st (.var 0) (.slot 0 .w64) &&
        !holdsZLoc x64Isa st (.var 1) (.slot 0 .w64)
    | none => false
  | none => false

-- `buildEntryBaseZ` with `liveZ = [true, false]` on the same slot preserves both vars and `shuffle`.
#guard match buildEntryBaseZ x64Isa 2 .empty sharedLive [true, false] emptySt with
  | some st =>
    holdsLoc x64Isa st (.var 0) (.slot 0 .w64) &&
      holdsLoc x64Isa st (.var 1) (.slot 0 .w64) &&
      holdsZLoc x64Isa st (.var 0) (.slot 0 .w64) &&
      match shuffle x64Isa 2 [] st sharedLive true with
      | some (code, st2) => code.isEmpty && entryZOk x64Isa st2 sharedEntry []
      | none => false
  | none => false

-- Reverse ordering (`liveZ = [false, true]`) also preserves both vars and canonical `.gprZ`.
#guard match buildEntryBaseZ x64Isa 2 .empty sharedLive [false, true] emptySt with
  | some st =>
    holdsLoc x64Isa st (.var 0) (.slot 0 .w64) &&
      holdsLoc x64Isa st (.var 1) (.slot 0 .w64) &&
      holdsZLoc x64Isa st (.var 1) (.slot 0 .w64) &&
      !holdsZLoc x64Isa st (.var 0) (.slot 0 .w64)
  | none => false

-- `bindBlockParamsZ` adding a non-`plocZ` `i64` param to a `.gprZ` slot preserves the live var.
#guard match buildEntryBaseZ x64Isa 2 .empty [(.var 0, .slot 0 .w64)] [true] emptySt with
  | some baseSt =>
    match bindBlockParamsZ x64Isa 2 [i64] [.slot 0 .w64] [false] 1 baseSt with
    | some st =>
      holdsLoc x64Isa st (.var 0) (.slot 0 .w64) &&
        holdsLoc x64Isa st (.var 1) (.slot 0 .w64) &&
        holdsZLoc x64Isa st (.var 0) (.slot 0 .w64)
    | none => false
  | none => false

/-! ## 2. End-to-End x86-64 Spill + Rega Regression (Coalesced `i32`/`zext 32 64` in Shared Slot) -/

private meta def makeLivePress {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (base : V i64) : Nat → (List (V i64) → Expr V L rs) → Expr V L rs
  | 0, k => k []
  | n + 1, k =>
    .let_ (op2 (.add i64) (.var base) (.imm (BitVec.ofNat 64 (8 * (n + 1))))) fun (a, ()) =>
      .load i64 (.var a) fun v =>
        makeLivePress base n fun vs => k (v :: vs)

private meta def sumVars {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    List (V i64) → V i64 → (V i64 → Expr V L rs) → Expr V L rs
  | [], acc, k => k acc
  | v :: vs, acc, k =>
    .let_ (op2 (.xor i64) (.var acc) (.var v)) fun (a1, ()) =>
      .let_ (op2 (.add i64) (.var a1) (.var v)) fun (a2, ()) =>
        sumVars vs a2 k

/-- High-pressure multi-block loop where a canonical `i32` load `x32` (`liveZ = true`) and its
`zext 32 64` `x64` (`liveZ = false`) coalesce into the same stack slot in `(true, false)` order
and stay live across a two-block loop backedge (`body -> hdr`). -/
meta def coalescedZextSlotLoopFn : Fn :=
  ⟨"coalesced_zext_slot_loop", [i64, i64, i64], [i64], fun _ _ (p, q, n, ()) =>
    .load i32 (.var q) fun x32 =>
    .let_ (op1 (.zext 32 64) (.var x32)) fun (x64, ()) =>
    makeLivePress p 16 fun ps =>
    .group (sig := [[i64, i64], [i64, i64]])
      (fun (hdr, body, ()) =>
        .cons (ts := [i64, i64])
          (fun (i, acc, ()) =>
            .let_ (op2 (.cmp .ult i64) (.var i) (.var n)) fun (c, ()) =>
            .jnz (.var c)
              (.jump body (.var i, .var acc, ()))
              (.let_ (op2 (.add i64) (.var acc) (.var x64)) fun (s1, ()) =>
               .let_ (op2 (.add i32) (.var x32) (.imm 7)) fun (y32, ()) =>
               .let_ (op1 (.zext 32 64) (.var y32)) fun (y64, ()) =>
               .let_ (op2 (.xor i64) (.var s1) (.var y64)) fun (res, ()) =>
               .ret (.var res, ())))
        (.cons (ts := [i64, i64])
          (fun (i, acc, ()) =>
            sumVars ps acc fun a1 =>
            .let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
            .jump hdr (.var i', .var a1, ()))
          .nil))
      (fun (hdr, _body, ()) => .jump hdr (.imm 0, .imm 0, ()))⟩

private meta def hasOrderedMixedZSlot :
    List ((SymArg × x64Isa.Loc) × Bool) → Bool
  | [] => false
  | ((_, .slot s1 .w64), true) :: rest =>
    (rest.any fun ((_, loc2), z2) =>
      match loc2 with
      | .slot s2 .w64 => Nat.beq s1 s2 && !z2
      | _ => false) || hasOrderedMixedZSlot rest
  | _ :: rest => hasOrderedMixedZSlot rest

private meta def hasMixedZSlotEntry (f : Fn) : Bool :=
  let ff := Driver.toFlatFn f
  let mf := midStageFlat x64LegalTarget (earlyOptFlat ff)
  let h := Spill.hints x64Isa mf.toFn
  (List.range 8).any fun lid =>
    match h.entry.find? lid with
    | some en => hasOrderedMixedZSlot (en.live.zip en.liveZ)
    | none => false

#guard hasMixedZSlotEntry coalescedZextSlotLoopFn
#guard (Driver.compileFnFlat x64Isa x64LegalTarget coalescedZextSlotLoopFn).isOk
#guard
  let ff := Driver.toFlatFn coalescedZextSlotLoopFn
  let mf := midStageFlat x64LegalTarget (earlyOptFlat ff)
  let fn := mf.toFn
  let h := Spill.hints x64Isa fn
  (Rega.lowerFn x64Isa h fn.ext fn).isOk

end LeanQbeTest.T.X64ShuffleW62RegTest
