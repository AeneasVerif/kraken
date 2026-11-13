module

public import Kraken.Bedrock2.Test.Run
public import Kraken.Bedrock2.Test.Matrix
public import Kraken.Bedrock2.CPrinter

@[expose] public section

namespace Kraken.Bedrock2.Test.Gen

structure GenState where
  seed : UInt64
  fresh : Nat := 0
  deriving Inhabited

abbrev GenM := StateM GenState

def next : GenM UInt64 := modifyGet fun st =>
  let s : UInt64 := st.seed + 0x9e3779b97f4a7c15
  let z : UInt64 := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z : UInt64 := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (z ^^^ (z >>> 31), { st with seed := s })

def below (n : Nat) : GenM Nat := return (← next).toNat % max n 1

def pick {α} [Inhabited α] (xs : List α) : GenM α := return xs[← below xs.length]!

def pickDistinct : Nat → List String → GenM (List String)
  | 0, _ => return []
  | n + 1, xs => do
    let x ← pick xs
    return x :: (← pickDistinct n (xs.erase x))

def freshName (pre : String) : GenM String :=
  modifyGet fun st => (s!"{pre}{st.fresh}", { st with fresh := st.fresh + 1 })

def genLit : GenM Int := do
  match ← below 4 with
  | 0 => pick boundaryValues
  | 1 => return (← below 256)
  | 2 => return (← next).toNat
  | _ => return (← below 17 : Int) - 8

structure Ctx where
  scalars : List String
  targets : List String
  ptrs : List (String × Nat)
  callees : List (String × Nat × Nat)

def masked (p : String) (mask : Nat) (e : Expr) : Expr :=
  .op .add (.var p) (.op .and e (.literal mask))

def leaf (c : Ctx) : GenM Expr := do
  if c.scalars.isEmpty || (← below 3) == 0 then return .literal (← genLit)
  else return .var (← pick c.scalars)

def genExpr (c : Ctx) : Nat → GenM Expr
  | 0 => leaf c
  | d + 1 => do
    match ← below 12 with
    | 0 | 1 => leaf c
    | 2 => return .op1 (← pick [.not, .opp]) (← genExpr c d)
    | 3 | 4 | 5 | 6 => return .op (← pick (binops.map (·.1))) (← genExpr c d) (← genExpr c d)
    | 7 => return .ite (← genExpr c d) (← genExpr c d) (← genExpr c d)
    | 8 | 9 =>
      let (p, mask) ← pick c.ptrs
      return .load (← pick accessSizes) (masked p mask (← genExpr c d))
    | _ =>
      let j ← pick [0, 1, 2, 3, 4]
      let table ← (List.range (2 ^ j + 8)).mapM fun _ => return (← below 256).toUInt8
      return .inlinetable (← pick accessSizes) table (.op .and (← genExpr c d) (.literal (2 ^ j - 1)))

def genSet (c : Ctx) : GenM Cmd := do
  let t ← pick c.targets
  let e ← genExpr c 3
  return .set t (if e == .var t then .op .add e (.literal 1) else e)

def genStore (c : Ctx) : GenM Cmd := do
  let (p, mask) ← pick c.ptrs
  return .store (← pick accessSizes) (masked p mask (← genExpr c 2)) (← genExpr c 3)

mutual

partial def genCmd (c : Ctx) : Nat → GenM Cmd
  | 0 => do if (← below 3) == 0 then genStore c else genSet c
  | d + 1 => do
    match ← below 14 with
    | 0 | 1 | 2 | 3 => genSet c
    | 4 | 5 => genStore c
    | 6 | 7 => return .cond (← genExpr c 3) (← genBlock c d) (← genBlock c d)
    | 8 | 9 =>
      let i ← freshName "c"
      let bound ← if (← below 2) == 0 then pure (Expr.literal (← below 4))
        else pure (.op .and (← genExpr c 2) (.literal 3))
      let body ← genBlock { c with scalars := i :: c.scalars } d
      return .seq (.set i (.literal 0))
        (.while (.op .ltu (.var i) bound) (.seq body (.set i (.op .add (.var i) (.literal 1)))))
    | 10 | 11 =>
      let q ← freshName "q"
      let k ← pick [3, 4, 5, 6]
      let n := 2 ^ k + 8
      let inits ← (List.range (n / 8)).mapM fun o =>
        return Cmd.store .eight (offset q (8 * o)) (← genExpr c 2)
      let body ← genBlock { c with ptrs := (q, 2 ^ k - 1) :: c.ptrs } d
      return .stackalloc q n (.seq (seqAll inits) body)
    | _ =>
      match c.callees with
      | [] => genSet c
      | _ =>
        let (g, np, nr) ← pick c.callees
        let (p, _) ← pick (c.ptrs.filter (·.2 == 63))
        let args ← (List.range np).mapM fun _ => genExpr c 2
        return .call (← pickDistinct nr c.targets) g (.var p :: args)

partial def genBlock (c : Ctx) (d : Nat) : GenM Cmd := do
  let n ← below 3
  return seqAll (← (List.range (n + 1)).mapM fun _ => genCmd c d)

end

def genFunc (k : Nat) (callees : List (String × Nat × Nat)) (np nr : Nat) :
    GenM (String × Func) := do
  let params := (List.range np).map (s!"a{·}")
  let rets := (List.range nr).map (s!"r{·}")
  let locals := (List.range (3 + (← below 3))).map (s!"x{·}")
  let ptrs := [("p", 63)]
  let mut scalars := params
  let mut inits := #[]
  for t in locals ++ rets do
    inits := inits.push (Cmd.set t (← genExpr ⟨scalars, [], ptrs, []⟩ 2))
    scalars := scalars ++ [t]
  let ctx : Ctx := ⟨scalars, locals ++ rets, ptrs, callees⟩
  let body ← (List.range (2 + (← below 5))).mapM fun _ => genCmd ctx 3
  let fold ← scalars.foldlM (fun acc x => return Expr.op (← pick [.add, .xor, .sub]) acc (.var x))
    (Expr.load .eight (.var "p"))
  let final := match rets with
    | r :: _ => Cmd.set r fold
    | [] => Cmd.store .eight (.var "p") fold
  return (s!"f{k}", ⟨"p" :: params, rets, seqAll (inits.toList ++ body ++ [final])⟩)

def genCandidate (seed i attempt : Nat) : Case :=
  let st : GenState := { seed := ((seed * 1000003 + i) * 1000003 + attempt).toUInt64 }
  Prod.fst <| StateT.run (m := Id) (s := st) do
    let nf := 1 + (← below 4)
    let mut funcs : List (String × Func) := []
    let mut sigs : List (String × Nat × Nat) := []
    for k in (List.range nf).reverse do
      let np ← below 4
      let nr ← if k == 0 then pure (1 + (← below 3)) else below 4
      let f ← genFunc k sigs np nr
      funcs := f :: funcs
      sigs := (f.1, np, nr) :: sigs
    let np := match sigs with | (_, np, _) :: _ => np | [] => 0
    let buf ← (List.range 72).mapM fun _ => return (← below 256).toUInt8
    let words ← (List.range np).mapM fun _ => return Arg.word (← genLit)
    return { name := s!"gen_{seed}_{i}", funcs, entry := "f0", args := .buf buf :: words }

def oracleA : List Nat := (List.range 4096).map (0x100000 + · * 0x100)
def oracleB : List Nat := (List.range 4096).map fun i => 0x800000 + (4095 - i) * 0x100

def accept (c : Case) : Bool :=
  (match cModule (c.funcs.filter (·.1 == c.entry)) (c.funcs.filter (·.1 != c.entry)) true with
    | .ok _ => true
    | .error _ => false) &&
  [32, 64].all fun w =>
    match runCase w c [0x10000] oracleA 0 false, runCase w c [0x10000] oracleB 0xa5 false with
    | .ok a, .ok b => a == b
    | _, _ => false

def genCase (seed i : Nat) : Except String Case :=
  match (List.range 100).find? (fun a => accept (genCandidate seed i a)) with
  | some a => pure (genCandidate seed i a)
  | none => throw s!"no acceptable program for seed {seed} index {i}"

end Kraken.Bedrock2.Test.Gen
