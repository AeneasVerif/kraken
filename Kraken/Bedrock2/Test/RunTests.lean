module

import Kraken.Bedrock2.Test.Run
meta import Kraken.Bedrock2.Test.Run

open Kraken.Bedrock2 Kraken.Bedrock2.Test

private def stable (w : Nat) (c : Case) (addrs : List Nat) (stk : List (Nat × Nat)) : Bool :=
  match runCase w c addrs (stk.map (·.1)) 0, perturb w (addrs.zip (c.buffers.map (·.length))) stk with
  | .ok obs, some o' =>
    match runCase w c addrs o' 0xa5 with
    | .ok obs' => obs' == obs
    | .error _ => false
  | _, _ => false

private def oneAlloc (ret : Expr) : Case :=
  { name := "one_alloc", entry := "f", args := [],
    funcs := [("f", ⟨[], ["r"], .stackalloc "a" 8 (.set "r" ret)⟩)] }

private def twoAllocs (ret : Expr) : Case :=
  { name := "two_allocs", entry := "f", args := [],
    funcs := [("f", ⟨[], ["r"], .stackalloc "a" 8 (.stackalloc "b" 8 (.set "r" ret))⟩)] }

private def seqAllocs : Case :=
  { name := "seq_allocs", entry := "f", args := [],
    funcs := [("f", ⟨[], ["r"],
      .seq (.stackalloc "a" 8 (.set "x" (.var "a")))
        (.stackalloc "b" 8 (.set "r" (.op .sub (.var "b") (.var "x"))))⟩)] }

private def bufAndAllocs : Case :=
  { name := "buf_and_allocs", entry := "f", args := [.buf (List.replicate 16 7)],
    funcs := [("f", ⟨["p"], ["r"],
      .stackalloc "a" 8 (.seq (.store .eight (.var "a") (.load .eight (.var "p")))
        (.stackalloc "b" 8 (.seq (.store .eight (.var "b") (.literal 1))
          (.seq (.store .eight (.op .add (.var "p") (.literal 8))
              (.op .add (.load .eight (.var "a")) (.load .eight (.var "b"))))
            (.set "r" (.load .one (.op .add (.var "a") (.literal 3))))))))⟩)] }

private def low12 : Expr := .op .and (.var "a") (.literal 0xfff)
private def diff : Expr := .op .sub (.var "b") (.var "a")

private def stk64 : List (Nat × Nat) := [(0x7ffd12345670, 8), (0x7ffd12345660, 8)]
private def stk32 : List (Nat × Nat) := [(0xffffd670, 8), (0xffffd660, 8)]

#guard !stable 64 (oneAlloc low12) [] [(0x7ffd12345670, 8)]
#guard !stable 32 (oneAlloc low12) [] [(0xffffd670, 8)]
#guard !stable 64 (twoAllocs diff) [] stk64
#guard !stable 32 (twoAllocs diff) [] stk32
#guard !stable 64 (twoAllocs (.op .and (.var "b") (.literal 0xfff))) [] stk64
#guard !stable 64 seqAllocs [] [(0x7ffd12345670, 8), (0x7ffd12345670, 8)]
#guard !stable 64 seqAllocs [] [(0x7ffd12345670, 8), (0x7ffd12345660, 8)]

#guard !stable 64 (oneAlloc (.load .eight (.var "a"))) [] [(0x7ffd12345670, 8)]
#guard stable 64 (twoAllocs (.literal 5)) [] stk64
#guard stable 32 (twoAllocs (.literal 5)) [] stk32
#guard stable 64 bufAndAllocs [0x555555558000] stk64
#guard stable 32 bufAndAllocs [0x56558000] stk32
private def nested : Case :=
  { name := "stack_nested", funcs := [stackNested], entry := "stack_nested",
    args := [.word 0x1122334455667788] }

#guard stable 64 nested [] stk64
#guard stable 32 nested [] stk32

#guard perturb 64 [] [] = some []
#guard perturb 32 [(0x1000, 0x10)] [(0xfffff000, 0x1000)] = none
#guard match perturb 64 [(0x555555558000, 16)] stk64 with
  | some [b0, b1] =>
    b0 + 8 < b1 && b0 % 0x1000 != 0x670 && b1 % 0x1000 != 0x660 &&
    [b0, b1].all (fun b => b ≥ 0x555555558010 || b + 8 ≤ 0x555555558000) &&
    [b0, b1].all (fun b => b ≥ 0x7ffd12345678 || b + 8 ≤ 0x7ffd12345660)
  | _ => false
