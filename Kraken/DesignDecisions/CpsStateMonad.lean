import Kraken.Semantics

def CpsState (σ α : Type) : Type 1 :=
  σ → (α → σ → Effects) → Effects

instance {σ} : Monad (CpsState σ) where
  pure x := fun s k => k x s
  bind m f := fun s k => m s (fun a s' => f a s' k)

-- primed definitions to change argument order:

def RegOrMem.interp' {w} [Labels] [AddressSize]
  (o : RegOrMem w) (p : Std.Rco Int64) : CpsState MachineData w.type :=
  fun s (ret : w.type → MachineData → Effects) => RegOrMem.interp o s p ret

def Operand.interp' {w} [Labels] [AddressSize]
  (o : Operand w) (p : Std.Rco Int64) : CpsState MachineData w.type :=
  fun s (ret : w.type → MachineData → Effects) => Operand.interp o s p ret

def StatusFlags.set' (status : StatusFlags) : CpsState MachineData Unit :=
  fun s ret => ret () { s with status }

def RegOrMem.set' {w} [Labels] [AddressSize]
  (d : Dst w) (v : w.type) (p : Std.Rco Int64) : CpsState MachineData Unit :=
  fun s (ret : Unit → MachineData → Effects) => MachineData.set s d v p (ret ())

-- Operation.interp for the .add case rewritten in monadic style:
def add.interp' [Labels] [address_size : AddressSize] {w : Width}
  (dst : Dst w) (src : Operand w) (p : Std.Rco Int64)
  : CpsState MachineData Unit := do
    let a ← src.interp' p
    let b ← dst.interp' p
    let v := a + b
    let status := .from_result v {
      cf := v.unsigned != a.unsigned + b.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
      of := v.signed != a.signed + b.signed }
    StatusFlags.set' status
    dst.set' v p

example [Labels] [address_size : AddressSize] {w : Width}
  (dst : Dst w) (src : Operand w) p s next ignored_jmp :
  add.interp' dst src p s next = (Operation.add dst src).interp p s (next ()) ignored_jmp
:= by rfl

-- use different arguments so that equality doesn't hold and we can inspect the
-- result of unfolding without dsimp overeagerly applying rfl
example [Labels] [address_size : AddressSize] {w : Width}
  (dst1 dst2 : Dst w) (src1 src2 : Operand w) p s next ignored_jmp
  (e1: dst1 = dst2) (e2: src1 = src2) :
  add.interp' dst1 src1 p s next = (Operation.add dst2 src2).interp p s (next ()) ignored_jmp
:= by
  dsimp only [add.interp', Operation.interp]
  dsimp only [bind, pure]
  dsimp only [RegOrMem.interp', Operand.interp', StatusFlags.set', RegOrMem.set']
  rewrite [e1, e2]
  -- same, except that LHS uses a_1 instead of b
  rfl

-- This is how to tell Lean that it's a state monad, but we did not even
-- use state-monad `get` and `set` above, but preferred `fun s ret => ...` style
-- for the state-modifying primitives
instance {σ} : MonadStateOf σ (CpsState σ) where
  get := fun s k => k s s
  set s'  := fun _ k => k () s'
  modifyGet f := fun s k => let (a, s') := f s; k a s'
