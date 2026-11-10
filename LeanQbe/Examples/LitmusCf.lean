module

public import LeanQbe.Spill
public import LeanQbe.Amd64.Targ

/-!
# Control-flow litmus programs (plan step 2a)

if/else, a counting loop, an even/odd group of two mutually recursive join points, nested loops
with values live across both loops, and a loop that swaps its parameters (a parallel-move cycle).
Hints come from the untrusted first-fit oracle `Spill.hints`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Litmus

/-- `a ≠ 0 ? a + b : b - a` (`jnz` tests the low 32 bits). -/
def ifelse : Fn where
  name := "ifelse"
  body := fun _ _ => .param fun a => .param fun b =>
    .jnz (.var a)
      (.let_ (.bin .l .add (.var a) (.var b)) fun x => .ret [.var x])
      (.let_ (.bin .l .sub (.var b) (.var a)) fun x => .ret [.var x])

/-- `1 + 2 + … + n` (for `n < 2^32`). -/
def sumto : Fn where
  name := "sumto"
  body := fun _ _ => .param fun n =>
    .label fun loop =>
    .block (.param fun i => .param fun s =>
        .jnz (.var i)
          (.let_ (.bin .l .add (.var s) (.var i)) fun s' =>
           .let_ (.bin .l .sub (.var i) (.imm 1)) fun i' =>
           .jump loop [.var i', .var s'])
          (.ret [.var s]))
      (.jump loop [.var n, .imm 0])

/-- `1` if `n` is even, else `0` (for `n < 2^32`): two mutually recursive join points. -/
def evenodd : Fn where
  name := "evenodd"
  body := fun _ _ => .param fun n =>
    .label fun even => .label fun odd =>
    .block (.param fun x =>
        .jnz (.var x) (.let_ (.bin .l .sub (.var x) (.imm 1)) fun x' => .jump odd [.var x'])
          (.ret [.imm 1])) <|
    .block (.param fun x =>
        .jnz (.var x) (.let_ (.bin .l .sub (.var x) (.imm 1)) fun x' => .jump even [.var x'])
          (.ret [.imm 0])) <|
    .jump even [.var n]

/-- `Σ_{i=1..n} Σ_{j=1..m} (k + i)`: `m` and `k` live across both loops, `i` across the inner one. -/
def nested : Fn where
  name := "nested"
  body := fun _ _ => .param fun n => .param fun m => .param fun k =>
    .label fun outer =>
    .block (.param fun i => .param fun t =>
        .jnz (.var i)
          (.label fun inner =>
           .block (.param fun j => .param fun u =>
               .jnz (.var j)
                 (.let_ (.bin .l .add (.var u) (.var k)) fun u1 =>
                  .let_ (.bin .l .add (.var u1) (.var i)) fun u2 =>
                  .let_ (.bin .l .sub (.var j) (.imm 1)) fun j' =>
                  .jump inner [.var j', .var u2])
                 (.let_ (.bin .l .sub (.var i) (.imm 1)) fun i' =>
                  .jump outer [.var i', .var u]))
             (.jump inner [.var m, .var t]))
          (.ret [.var t]))
      (.jump outer [.var n, .imm 0])

/-- `a` if `n` is even, else `b`: the loop swaps its two parameters (a move cycle). -/
def swap : Fn where
  name := "swap"
  body := fun _ _ => .param fun n => .param fun a => .param fun b =>
    .label fun loop =>
    .block (.param fun i => .param fun x => .param fun y =>
        .jnz (.var i)
          (.let_ (.bin .l .sub (.var i) (.imm 1)) fun i' => .jump loop [.var i', .var y, .var x])
          (.ret [.var x]))
      (.jump loop [.var n, .var a, .var b])

end LeanQbe.Litmus
