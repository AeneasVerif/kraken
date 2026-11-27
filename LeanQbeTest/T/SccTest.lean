module

public import LeanQbe.T.SccLemmas
public import LeanQbe.T.Notation
public import LeanQbe.T.FlatLemmas
meta import LeanQbe.T.Scc
meta import LeanQbe.T.SccLemmas
meta import LeanQbe.T.Module
meta import LeanQbe.T.Notation

/-!
# Tests for Call Graph Extraction, Tarjan Condensation, and `checkSccOrder`

Exercises `LeanQbe.T.Scc` and `LeanQbe.T.SccLemmas`:
1. Multi-SCC call graph extraction (`callGraph`), Tarjan condensation (`sccOrder`), and
   `checkSccOrder` / `checkModuleSccOrder` on a 4-SCC DAG with mutual recursion, externals, and
   exits.
2. Extraction of `Fn.callsOk` and disjointness via `checkSccOrder_sound` and
   `checkSccOrder_of_acyclic`.
3. Negative tests rejecting broken SCC splits, wrong topological order, duplicates, empty SCCs,
   missing external signatures, undeclared exits, and external name collisions.
4. Single-line `#print axioms` audit for every new public theorem in `SccLemmas.lean` and this file.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.SccTest

open LeanQbe.T LeanQbe.T.Notation

/-! ## 1. Test Functions & Multi-SCC Module -/

def leafFn : Fn := tqbe $leaf(%x:l) -> l {
  %y =l call $extInc(%x)
  ret %y
}

def pingFn : Fn := tqbe $ping(%n:l) -> l {
  %c =b ceql %n, 0
  jnz %c, {
    %b =l call $leaf(1:l)
    ret %b
  }, {
    %n1 =l sub %n, 1
    %r =l call $pong(%n1)
    ret %r
  }
}

def pongFn : Fn := tqbe $pong(%n:l) -> l {
  %c =b ceql %n, 0
  jnz %c, {
    exit $halt(%n)
  }, {
    %n1 =l sub %n, 1
    %r =l call $ping(%n1)
    ret %r
  }
}

def midFn : Fn := tqbe $mid(%n:l) -> l {
  %a =l call $leaf(%n)
  %b =l call $ping(%a)
  ret %b
}

def topFn : Fn := tqbe $top(%n:l) -> l {
  %a =l call $mid(%n)
  %b =l call $pong(%a)
  ret %b
}

def testExts : List Extern := [⟨"extInc", [i64], [i64]⟩]
def testExtSigs : List SigEntry := testExts.map Extern.sig
def testExits : List Sym := ["halt"]

def multiSccFns : List Fn := [topFn, midFn, pongFn, pingFn, leafFn]
def multiSccMod : Module := ⟨multiSccFns, testExts, testExits⟩

/-! ## 2. Positive `#guard`s & `checkSccOrder_sound` -/

#guard (callGraph [leafFn, midFn]).map Prod.fst == ["leaf", "mid"]
#guard (callGraph [leafFn]).head!.2 == [("extInc", [i64], [i64])]
#guard (sccOrder multiSccFns).map (List.map Fn.name) ==
  [["leaf"], ["ping", "pong"], ["mid"], ["top"]]
#guard checkSccOrder (sccOrder multiSccFns) testExtSigs testExits == true
#guard checkModuleSccOrder multiSccMod (sccOrder multiSccFns) == true

def acycMod : Module := ⟨[leafFn], testExts, []⟩

#guard acycMod.checkAcyclic == true
#guard checkSccOrder (acycMod.fns.map fun f => [f]) (acycMod.externs.map Extern.sig)
  acycMod.exits == true

theorem multiScc_order_ok :
    checkSccOrder (sccOrder multiSccFns) testExtSigs testExits = true := by
  t_kernel_rfl

theorem multiScc_order_shape :
    sccOrder multiSccFns = [[leafFn], [pingFn, pongFn], [midFn], [topFn]] := by
  t_kernel_rfl

theorem multiScc_ping_callsOk :
    pingFn.callsOk
      ([leafFn].map Fn.sig ++ [pingFn, pongFn].map Fn.sig ++ testExtSigs) testExits := by
  have hsplit : sccOrder multiSccFns =
      [[leafFn]] ++ [pingFn, pongFn] :: [[midFn], [topFn]] :=
    multiScc_order_shape
  exact checkSccOrder_scc_callsOk multiScc_order_ok hsplit List.mem_cons_self

theorem acycMod_sccOrder_ok :
    checkSccOrder (acycMod.fns.map fun f => [f]) (acycMod.externs.map Extern.sig)
      acycMod.exits = true :=
  checkSccOrder_of_acyclic (by t_kernel_rfl)

/-! ## 3. Negative `#guard`s (Rejected Splits, Order, Duplicates, Missing Exts/Exits) -/

-- Splitting mutual cycle `ping`/`pong` must fail in either order.
#guard checkSccOrder [[leafFn], [pingFn], [pongFn]] testExtSigs testExits == false
#guard checkSccOrder [[leafFn], [pongFn], [pingFn]] testExtSigs testExits == false

-- Wrong topological order (`mid` before `leaf`) must fail.
#guard checkSccOrder [[midFn], [leafFn], [pingFn, pongFn]] testExtSigs testExits == false
#guard checkSccOrder [[topFn], [midFn], [pingFn, pongFn], [leafFn]] testExtSigs testExits == false

-- Duplicate function across SCCs or within an SCC must fail.
#guard checkSccOrder [[leafFn], [leafFn]] testExtSigs testExits == false
#guard checkSccOrder [[leafFn, leafFn]] testExtSigs testExits == false

-- Empty SCC must fail.
#guard checkSccOrder [[]] testExtSigs testExits == false
#guard checkSccOrder [[leafFn], []] testExtSigs testExits == false

-- Missing external signature or undeclared exit must fail.
#guard checkSccOrder (sccOrder multiSccFns) [] testExits == false
#guard checkSccOrder (sccOrder multiSccFns) testExtSigs [] == false

-- Function name colliding with an external signature name must fail.
#guard checkSccOrder [[leafFn]] (testExtSigs ++ [("leaf", [i64], [i64])]) testExits == false

/-! ## 4. Single-Line Axiom Audit -/

#print axioms LeanQbe.T.checkSccCalls_ok
#print axioms LeanQbe.T.checkSccOrder_sound
#print axioms LeanQbe.T.checkSccOrder_nodup
#print axioms LeanQbe.T.checkSccOrder_scc_callsOk
#print axioms LeanQbe.T.checkSccOrder_scc_namesNodup
#print axioms LeanQbe.T.checkSccOrder_of_acyclic
#print axioms multiScc_order_ok
#print axioms multiScc_order_shape
#print axioms multiScc_ping_callsOk
#print axioms acycMod_sccOrder_ok

end LeanQbeTest.T.SccTest
