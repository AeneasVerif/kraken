module

public import Kraken.Bedrock2.Test.Cases
public import Kraken.Bedrock2.Interp

@[expose] public section

namespace Kraken.Bedrock2.Test

structure Obs where
  rets : List Nat
  final : List (List UInt8)
  deriving BEq

def argVals (w : Nat) : List Arg → List Nat → Option (List (BitVec w))
  | [], _ => some []
  | .word v :: as, ad => (BitVec.ofInt w v :: ·) <$> argVals w as ad
  | .buf _ :: as, a :: ad => (BitVec.ofNat w a :: ·) <$> argVals w as ad
  | .buf _ :: _, [] => none

def runCase (w : Nat) (c : Case) (addrs : List Nat) (o : List Nat) (fill : UInt8)
    (exact : Bool := true) : Except String Obs := do
  let some f := c.funcs.lookup c.entry | throw s!"entry function '{c.entry}' not found"
  let bufs := c.buffers.zip addrs
  if bufs.length != addrs.length || bufs.length != c.buffers.length then
    throw "buffer count mismatch"
  let m0 : Mem w := bufs.foldl (fun m (bs, a) => m.union (bs.At (BitVec.ofNat w a))) ∅
  let some args := argVals w c.args addrs | throw "buffer count mismatch"
  let some lf := putManyZip f.params args ∅ | throw "wrong number of arguments"
  let some (_, m, l, rest) := run c.funcs fill c.fuel f.body [] m0 lf (o.map (BitVec.ofNat w))
    | throw "interpreter got stuck"
  if exact && !rest.isEmpty then throw s!"{rest.length} logged stackallocs were not used"
  let some rets := getMany l f.rets | throw "return variable unset"
  let some final := bufs.mapM (fun (bs, a) => m.loadBytes (BitVec.ofNat w a) bs.length)
    | throw "buffer missing from final memory"
  return ⟨rets.map (·.toNat), final⟩

def alignDown (a : Nat) : Nat := a / 0x1000 * 0x1000
def alignUp (a : Nat) : Nat := (a + 0xfff) / 0x1000 * 0x1000

def perturb (w : Nat) (bufs stk : List (Nat × Nat)) : Option (List Nat) :=
  let all := bufs ++ stk
  let allLo := alignDown (all.foldl (fun l (a, _) => min l a) (2 ^ w))
  let allHi := alignUp (all.foldl (fun h (a, n) => max h (a + max n 1)) 0)
  let order := stk.zipIdx.mergeSort fun (x, i) (y, j) => y.1 < x.1 || (y.1 == x.1 && j ≤ i)
  let off := 0x5a3
  let (slots, size) := order.foldl (init := ([], 0)) fun (acc, cur) ((a, n), i) =>
    let p := if (off + cur) % 0x1000 == a % 0x1000 then cur + 1 else cur
    ((i, p) :: acc, p + max n 1 + 0x11 + 0x8 * (acc.length % 32))
  let rel := (slots.mergeSort fun x y => x.1 ≤ y.1).map (·.2)
  if allHi + 0x10000 + off + size ≤ 2 ^ w then some (rel.map (allHi + 0x10000 + off + ·))
  else if 0x20000 + off + size ≤ allLo then
    some (rel.map (alignDown (allLo - 0x10000 - off - size) + off + ·))
  else none

end Kraken.Bedrock2.Test
