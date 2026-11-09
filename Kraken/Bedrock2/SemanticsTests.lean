module

import Kraken.Bedrock2.Semantics
import Kraken.Bedrock2.NonVacuity
meta import Kraken.Bedrock2.Semantics

open Std Kraken.Bedrock2

private def ev32 (e : Expr) (m : Mem 32 := ∅) : Option (BitVec 32) := e.eval m ∅
private def ev64 (e : Expr) (m : Mem 64 := ∅) : Option (BitVec 64) := e.eval m ∅
private def lit (v : Int) : Expr := .literal v

#guard ev32 (.op .slu (lit 1) (lit 33)) = some 2
#guard ev64 (.op .slu (lit 1) (lit 65)) = some 2
#guard ev64 (.op .slu (lit 1) (lit 33)) = some (1 <<< 33)
#guard ev32 (.op .sru (lit 0x80000000) (lit 63)) = some 1
#guard ev32 (.op .srs (lit 0x80000000) (lit 63)) = some 0xffffffff
#guard ev32 (.op .divu (lit 7) (lit 0)) = some 0xffffffff
#guard ev32 (.op .remu (lit 7) (lit 0)) = some 7
#guard ev32 (.op .mulhuu (lit 0xffffffff) (lit 0xffffffff)) = some 0xfffffffe
#guard ev64 (.op .mulhuu (lit (2 ^ 63)) (lit 4)) = some 2
#guard ev32 (.op .lts (lit (-1)) (lit 0)) = some 1
#guard ev32 (.op .ltu (lit (-1)) (lit 0)) = some 0
#guard ev32 (.op .eq (lit (-1)) (lit 0xffffffff)) = some 1
#guard ev32 (.op1 .opp (lit 1)) = some 0xffffffff
#guard ev32 (.op1 .not (lit 0)) = some 0xffffffff
#guard ev32 (.ite (lit 0) (lit 1) (lit 2)) = some 2
#guard ev32 (.ite (lit 3) (lit 1) (.var "unbound")) = some 1
#guard ev32 (.var "unbound") = none
#guard ev32 (.inlinetable .two [1, 2, 3, 4] (lit 1)) = some 0x0302
#guard ev32 (.inlinetable .two [1, 2, 3, 4] (lit 3)) = none

private def m8 : Mem 32 := [1, 2, 3, 4, 5, 6, 7, 8].At 0x100

#guard ev32 (.load .eight (lit 0x100)) m8 = some 0x04030201
#guard ev32 (.load .four (lit 0x104)) m8 = some 0x08070605
#guard ev32 (.load .four (lit 0x105)) m8 = none

#guard ((store? .eight m8 0x100 0xffffffff).map (·.loadBytes 0x100 8)) =
  some (some [0xff, 0xff, 0xff, 0xff, 0, 0, 0, 0])
#guard (store? .two m8 0x107 0).isNone
#guard ((store? .one m8 0x107 0x1ff).map (·.loadBytes 0x100 8)) =
  some (some [1, 2, 3, 4, 5, 6, 7, 0xff])

example {ext : ExtSpec 32} {e : Env} {t : Trace 32} {m : Mem 32} {l : Locals 32}
    {post : Trace 32 → Mem 32 → Locals 32 → Prop} :
    ¬ Exec ext e 3 (.stackalloc "x" 4 .skip) t m l post := by
  intro h
  cases h
  omega

example {ext : ExtSpec 64} (hext : ext.Responsive) {e : Env} {B : Nat} {c : Cmd} {t : Trace 64}
    {l : Locals 64} (hB : B < 2 ^ 64) : ¬ Exec ext e B c t ∅ l fun _ _ _ => False :=
  fun h => let ⟨_, _, _, h⟩ := h.nonvacuous_of_empty hext hB; h

example : ExtSpec.Responsive (w := 64) fun _ _ _ _ _ => False := fun _ _ _ _ _ h => h.elim

example : Handler.Complete (w := 64) (fun _ _ _ _ _ => False) fun _ _ _ _ => none :=
  fun _ _ _ _ _ _ _ _ h => h.elim
