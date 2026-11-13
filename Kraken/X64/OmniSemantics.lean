module

/-
Omnisemantics for x64.
-/

import Kraken.Attribute
public import Kraken.OmniSemantics
public import Kraken.X64.Semantics

@[expose] public section

@[kstep] def Effects.All (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).All post
  | .require_read_access _ cont => (cont ()).All post
  | .require_write_access _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

@[ksimp] theorem Effects.All_require_read_access (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → Prop) :
    (require_access require_read_access addr bytes ok).All post = (ok ()).All post := by
  dsimp only [require_access]
  split <;> rfl

@[ksimp] theorem Effects.All_require_write_access (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → Prop) :
    (require_access require_write_access addr bytes ok).All post = (ok ()).All post := by
  dsimp only [require_access]
  split <;> rfl

/-! ### Memory accesses at a mapped address

Backward rules for stepping a load or store by hand (`refine Effects.All_load h ?_`). They are
implications, not equations, so they are not `ksimp` lemmas: under `kstep`, the same steps are taken
by the `kspec` equations `store_sep`/`load_sep` (`Kraken.X64.Sep`), whose side conditions are
separation-logic facts. The AVX rules have no `kspec` counterpart yet. -/

/-- A store to a mapped address: the access check passes and the run continues with the stored
bytes. -/
theorem Effects.All_store {s : MachineData} {addr : BitVec 64} {w : Width} {v : w.type}
    {ret : MachineData → Effects} {post : MachineState → Prop}
    (h : (Mem.loadInt s.dmem addr w.bytes).isSome)
    (hk : (ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }).All post) :
    (s.store addr v ret).All post := by
  unfold MachineData.store
  rw [Effects.All_require_write_access]
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
  simp only [hi]
  exact hk

/-- A load from a mapped address holding `i`: the run continues with the value read. -/
theorem Effects.All_load {s : MachineData} {addr : BitVec 64} {w : Width} {i : Int}
    {ret : w.type → MachineData → Effects} {post : MachineState → Prop}
    (h : Mem.loadInt s.dmem addr w.bytes = some i)
    (hk : (ret (.ofInt _ i) s).All post) :
    (s.load addr w ret).All post := by
  unfold MachineData.load
  rw [Effects.All_require_read_access]
  simp only [h]
  exact hk

/-- An aligned vector store to a mapped address. With `checkAlign := true` (`movaps`), the
alignment is a side condition: an unaligned access raises `#GP`, which `Effects.All` rejects. -/
theorem Effects.All_storeAvx {s : MachineData} {addr : BitVec 64} {w : AvxWidth} {v : w.type}
    {ret : MachineData → Effects} {post : MachineState → Prop} {checkAlign : Bool}
    (ha : checkAlign → isAligned w.bytes addr)
    (h : (Mem.loadInt s.dmem addr w.bytes).isSome)
    (hk : (ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }).All post) :
    (s.storeAvx addr v ret checkAlign).All post := by
  unfold MachineData.storeAvx
  split
  · cases checkAlign <;> simp_all
  rw [Effects.All_require_write_access]
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
  simp only [hi]
  exact hk

/-- An aligned vector load from a mapped address holding `i`. -/
theorem Effects.All_loadAvx {s : MachineData} {addr : BitVec 64} {w : AvxWidth} {i : Int}
    {ret : w.type → MachineData → Effects} {post : MachineState → Prop} {checkAlign : Bool}
    (ha : checkAlign → isAligned w.bytes addr)
    (h : Mem.loadInt s.dmem addr w.bytes = some i)
    (hk : (ret (.ofInt _ i) s).All post) :
    (s.loadAvx addr w ret checkAlign).All post := by
  unfold MachineData.loadAvx
  split
  · cases checkAlign <;> simp_all
  rw [Effects.All_require_read_access]
  simp only [h]
  exact hk

def step1 [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.step e s .done).All post

def straightlineStep [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.straightline e s .done).All post
