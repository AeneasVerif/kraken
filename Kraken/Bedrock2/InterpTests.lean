module

import Kraken.Bedrock2.Interp
meta import Kraken.Bedrock2.Interp

open Std Kraken.Bedrock2

private def lit (v : Int) : Expr := .literal v
private def var (x : String) : Expr := .var x

private def run32 (c : Cmd) (fuel : Nat := 100) (m : Mem 32 := ∅) (o : List (BitVec 32) := [])
    (fill : UInt8 := 0) (e : Env := []) : Option (RunResult 32) :=
  run e fill fuel c [] m ∅ o

private def get (r : Option (RunResult 32)) (x : String) : Option (BitVec 32) :=
  r.bind (·.2.2.1.get? x)

private def straight : Cmd :=
  .seq (.set "x" (lit 0x01020304))
    (.seq (.store .four (lit 0x100) (var "x"))
      (.seq (.store .one (lit 0x101) (lit 0xff))
        (.set "y" (.load .four (lit 0x100)))))

#guard get (run32 straight (m := [0, 0, 0, 0].At 0x100)) "y" = some 0x0102ff04
#guard (run32 straight (m := [0, 0, 0, 0].At 0x100)).map (·.2.1.loadBytes 0x100 4) =
  some (some [4, 0xff, 2, 1])
#guard (run32 straight).isNone

private def sumLoop : Cmd :=
  .seq (.set "s" (lit 0))
    (.seq (.set "i" (lit 0))
      (.while (.op .ltu (var "i") (lit 10))
        (.seq (.set "s" (.op .add (var "s") (var "i")))
          (.set "i" (.op .add (var "i") (lit 1))))))

#guard get (run32 sumLoop) "s" = some 45
#guard get (run32 sumLoop) "i" = some 10

private def divmodBody : Cmd :=
  .seq (.set "q" (.op .divu (var "a") (var "b"))) (.set "r" (.op .remu (var "a") (var "b")))

private def divmodEnv : Env := [("divmod", ⟨["a", "b"], ["q", "r"], divmodBody⟩)]

private def callDivmod : Cmd := .call ["x", "y"] "divmod" [lit 17, lit 5]

#guard get (run32 callDivmod (e := divmodEnv)) "x" = some 3
#guard get (run32 callDivmod (e := divmodEnv)) "y" = some 2
#guard get (run32 callDivmod (e := divmodEnv)) "a" = none
#guard (run32 callDivmod).isNone
#guard (run32 (.call ["x"] "divmod" [lit 17, lit 5]) (e := divmodEnv)).isNone

private theorem divmod_call {ext : ExtSpec 32} {B : Nat} (t : Trace 32) (m : Mem 32) (a b : BitVec 32) :
    call ext divmodEnv B "divmod" t m [a, b] fun t' m' rets =>
      t' = t ∧ m' = m ∧ rets = [interpBinop .divu a b, a % b] := by
  refine call.of_body rfl (by simp; rfl) (.seq_cps (.set_cps (v := interpBinop .divu a b) ?_
    (.set_cps (v := interpBinop .remu a b) ?_ ?_))) <;>
    simp [Expr.eval, var, getMany, interpBinop]

private theorem callDivmod_run {fill : UInt8} {fuel : Nat} {o : List (BitVec 32)} {r : RunResult 32}
    (hr : run divmodEnv fill fuel callDivmod [] ∅ ∅ o = some r) :
    r.2.2.1.get? "x" = some 3 ∧ r.2.2.1.get? "y" = some 2 := by
  obtain ⟨t', m', l', o'⟩ := r
  obtain ⟨rets, hl, -, -, rfl⟩ := run_of_call (Handler.ok_none fun _ _ _ _ _ => False)
    (divmod_call (B := 0) [] ∅ 17 5) (by rfl) hr
  simp [interpBinop] at hl
  simp [← hl]

private def allocLoad : Cmd := .stackalloc "p" 4 (.set "v" (.load .four (var "p")))

#guard get (run32 allocLoad (o := [0x200]) (fill := 0xab)) "v" = some 0xabababab
#guard get (run32 allocLoad (o := [0x200]) (fill := 0xab)) "p" = some 0x200
#guard (run32 allocLoad (o := [0x200]) (fill := 0xab)).map (·.2.1.contains 0x200) = some false
#guard (run32 allocLoad (o := [0x200]) (m := [7].At 0x100)).map (·.2.1.get? 0x100) = some (some 7)
#guard (run32 allocLoad (o := [0x200]) (m := [1].At 0x203)).isNone
#guard (run32 allocLoad (o := [0x200]) (m := [1].At 0x204)).isSome
#guard (run32 allocLoad).isNone

#guard (run32 (.while (lit 1) .skip) (fuel := 50)).isNone
#guard (run32 sumLoop (fuel := 10)).isNone
#guard (run32 sumLoop (fuel := 11)).isSome
#guard (run32 callDivmod (fuel := 0) (e := divmodEnv)).isNone
#guard (run32 callDivmod (fuel := 1) (e := divmodEnv)).isSome

private def twoAllocs : Cmd :=
  .seq (.stackalloc "p" 4 .skip) (.stackalloc "q" 2 (.stackalloc "r" 1 .skip))

#guard get (run32 twoAllocs (o := [0x300, 0x200, 0x100, 0x50])) "p" = some 0x300
#guard get (run32 twoAllocs (o := [0x300, 0x200, 0x100, 0x50])) "q" = some 0x200
#guard get (run32 twoAllocs (o := [0x300, 0x200, 0x100, 0x50])) "r" = some 0x100
#guard (run32 twoAllocs (o := [0x300, 0x200, 0x100, 0x50])).map (·.2.2.2) = some [0x50]
#guard (run32 twoAllocs (o := [0x300, 0x200])).isNone
#guard (run32 (.stackalloc "p" 4 (.stackalloc "q" 4 .skip)) (o := [0x200, 0x202])).isNone

private def echo : Handler 32 := fun _ _ a args =>
  if a = "echo" then some (∅, ∅, args) else none

#guard ((run [] 0 10 (.interact ["z"] "echo" [lit 9]) [] (∅ : Mem 32) ∅ [] echo).bind
  (·.2.2.1.get? "z")) = some 9
