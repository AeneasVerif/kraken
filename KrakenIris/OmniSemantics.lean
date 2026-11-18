module

public import Kraken.X64.Semantics
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Instances.Lib.FUpd
public import Iris.Instances.Lib.GhostMap
public import Iris.Instances.Lib.Invariants
public import Iris.Std.HeapInstances

/-!
# Omnisemantics for x64, in Iris

`Effects.All` (`Kraken/X64/OmniSemantics.lean`) is a handler into `Prop`, and
`Effects.AllI` below is an extension of it to `IProp`.
That is enough to let a program touch memory shared with other threads:

* a load or store outside the data memory needs the points-to assertion for the bytes it touches;
* at a `yield`, where other threads may run, every invariant must be closed.
-/

@[expose] public section

open Iris BI

/-- The ghost state of the shared memory. -/
class krakenGS (GF : BundledGFunctors) where
  memG : GhostMapG GF (BitVec 64) UInt8 (Std.ExtTreeMap (BitVec 64) · compare)
  memName : GName

attribute [reducible, instance] krakenGS.memG

section pointsto

variable {GF : BundledGFunctors} [G : krakenGS GF]

/-- `l ↦ b`: the shared memory holds the byte `b` at address `l`. -/
def pointsto (a : BitVec 64) (b : UInt8) : IProp GF :=
  ghost_map_elem G.memName (DFrac.own 1) a b

@[inherit_doc] notation:50 a:50 " ↦ " b:50 => pointsto a b

instance pointsto_timeless (a : BitVec 64) (b : UInt8) : Timeless (a ↦ b : IProp GF) := by
  unfold pointsto
  infer_instance

/-- `l ↦∗ bs`: the shared memory holds the bytes `bs` starting at address `l`. -/
def pointstoBytes (a : BitVec 64) : List UInt8 → IProp GF
  | [] => iprop(emp)
  | b :: bs => iprop(a ↦ b ∗ pointstoBytes (a + 1) bs)

@[inherit_doc] notation:50 a:50 " ↦∗ " bs:50 => pointstoBytes a bs

@[simp] theorem pointstoBytes_nil (a : BitVec 64) : (a ↦∗ [] : IProp GF) = iprop(emp) := rfl
@[simp] theorem pointstoBytes_cons (a : BitVec 64) (b : UInt8) (bs : List UInt8) :
    (a ↦∗ (b :: bs) : IProp GF) = iprop(a ↦ b ∗ (a + 1) ↦∗ bs) := rfl

end pointsto

section handler

variable {GF : BundledGFunctors} [InvGS GF] [G : krakenGS GF]

def Effects.AllI₀ (post : MachineState → IProp GF) : Effects → IProp GF
  | .done s => iprop(|={∅, ⊤}=> post s)
  | .unimplemented _ => iprop(False)
  | .gp_unaligned _ _ => iprop(False)
  | @Effects.undefined α _ k => iprop(∀ v : α, |={∅}=> (k v).AllI₀ post)
  | .require_read_access _ k => (k ()).AllI₀ post
  | .require_write_access _ k => (k ()).AllI₀ post
  | .require_exec_access _ k => (k ()).AllI₀ post
  -- KrakenIris
  -- loading data from the shared memory.
  | .nonmem_load dmem a w k =>
    iprop(∃ bs : List UInt8, ⌜bs.length = w.bytes⌝ ∗ a ↦∗ bs ∗
      ▷ (a ↦∗ bs ={∅}=∗ (k (.ofInt _ (Int.ofBytes bs)) dmem).AllI₀ post))
  -- storing data to the shared memory.
  | @Effects.nonmem_store dmem a w v k =>
    iprop(∃ old : List UInt8, ⌜old.length = w.bytes⌝ ∗ a ↦∗ old ∗
      ▷ (a ↦∗ Int.toBytes w.bytes v.toInt ={∅}=∗ (k dmem).AllI₀ post))
  -- yield point: other threads may run here, so every invariant must be closed.
  -- read `|={∅, ⊤}=>` as: close every invariant that is open
  -- read `|={⊤, ∅}=>` as: from here on, invariants may be opened again
  | .yield k => iprop(|={∅, ⊤}=> |={⊤, ∅}=> (k ()).AllI₀ post)

/-- The mask `M` is the set of invariants that are still closed. -/
def Effects.AllI (M : CoPset) (post : MachineState → IProp GF) (e : Effects) : IProp GF :=
  iprop(|={M, ∅}=> e.AllI₀ post)

theorem Effects.fupd_AllI (M M' : CoPset) (post : MachineState → IProp GF) (e : Effects) :
    (|={M, M'}=> e.AllI M' post) ⊢ e.AllI M post := by
  unfold Effects.AllI
  iintro H
  imod H
  iexact H

instance elimModal_fupd_AllI {io : ProofMode.InOut} (p : Bool) (E1 E2 : CoPset) (P : IProp GF)
    (post : MachineState → IProp GF) (e : Effects) :
    ProofMode.ElimModal True p io false iprop(|={E1,E2}=> P) P (e.AllI E1 post)
      (e.AllI E2 post) where
  elim_modal _ := by
    cases p <;> simp
    · iintro ⟨HP, Hwand⟩
      iapply Effects.fupd_AllI E1 E2
      imod HP
      iapply Hwand $$ HP
    · iintro ⟨#HP, Hwand⟩
      iapply Effects.fupd_AllI E1 E2
      imod HP
      iapply Hwand $$ HP

instance isExcept0_AllI (M : CoPset) (post : MachineState → IProp GF) (e : Effects) :
    ProofMode.IsExcept0 (e.AllI M post) := by
  unfold Effects.AllI
  infer_instance

/-! ## One rule per node -/

theorem Effects.AllI_done (M : CoPset) (s : MachineState) (post : MachineState → IProp GF) :
    (|={M, ⊤}=> post s) ⊢ (Effects.done s).AllI M post := by
  unfold Effects.AllI Effects.AllI₀
  iintro H
  imod H
  iapply fupd_mask_intro_subseteq (by simp) $$ H

/-- A `yield` can only be passed with every invariant closed: the mask must be `⊤`. -/
theorem Effects.AllI_yield (k : Unit → Effects) (post : MachineState → IProp GF) :
    (k ()).AllI ⊤ post ⊢ (Effects.yield k).AllI ⊤ post := by
  unfold Effects.AllI
  rw [Effects.AllI₀]
  iintro H
  iapply fupd_mask_intro (by simp)
  iintro Hclose
  imod Hclose
  imodintro
  iexact H

/-- An `undefined` value: the rest of the tree must be correct for every choice. -/
theorem Effects.AllI_undefined (M : CoPset) {α : Type} [NondetSupportingType α] (k : α → Effects)
    (post : MachineState → IProp GF) :
    (∀ v, (k v).AllI M post) ⊢ (Effects.undefined k).AllI M post := by
  unfold Effects.AllI
  rw [Effects.AllI₀]
  iintro H
  iapply fupd_mask_intro (by simp)
  iintro Hclose %v
  imod Hclose
  iapply H

theorem Effects.AllI_nonmem_load (M : CoPset) (dmem : DataMem) (a : BitVec 64) (w : Width)
    (k : w.type → DataMem → Effects) (bs : List UInt8) (post : MachineState → IProp GF)
    (hlen : bs.length = w.bytes) :
    a ↦∗ bs -∗
    ▷ (a ↦∗ bs -∗ (k (.ofInt _ (Int.ofBytes bs)) dmem).AllI M post) -∗
    (Effects.nonmem_load dmem a w k).AllI M post := by
  unfold Effects.AllI
  rw [Effects.AllI₀]
  iintro Hpt Hpost
  iapply fupd_mask_intro (by simp)
  iintro Hclose
  iexists bs
  iframe Hpt
  isplitr
  · ipureintro; exact hlen
  inext
  iintro Hpt
  imod Hclose
  iapply Hpost $$ Hpt

theorem Effects.AllI_nonmem_store (M : CoPset) (dmem : DataMem) (a : BitVec 64) {w : Width}
    (v : w.type) (k : DataMem → Effects) (old : List UInt8) (post : MachineState → IProp GF)
    (hlen : old.length = w.bytes) :
    a ↦∗ old -∗
    ▷ (a ↦∗ Int.toBytes w.bytes v.toInt -∗ (k dmem).AllI M post) -∗
    (Effects.nonmem_store dmem a v k).AllI M post := by
  unfold Effects.AllI
  rw [Effects.AllI₀]
  iintro Hpt Hpost
  iapply fupd_mask_intro (by simp)
  iintro Hclose
  iexists old
  iframe Hpt
  isplitr
  · ipureintro; exact hlen
  inext
  iintro Hpt
  imod Hclose
  iapply Hpost $$ Hpt

/-! ## The postcondition can be weakened -/

theorem Effects.AllI₀_weaken (e : Effects) (post post' : MachineState → IProp GF) :
    e.AllI₀ post -∗ (∀ s, post s -∗ post' s) -∗ e.AllI₀ post' := by
  induction e with
  | done s =>
    rw [Effects.AllI₀, Effects.AllI₀]
    iintro H Hw
    imod H
    imodintro
    iapply Hw $$ H
  | unimplemented msg =>
    rw [Effects.AllI₀]
    iintro ⟨⟩
  | gp_unaligned addr w =>
    rw [Effects.AllI₀]
    iintro ⟨⟩
  | nonmem_load dmem a w k ih =>
    rw [Effects.AllI₀, Effects.AllI₀]
    iintro ⟨%bs, %hlen, Hpt, Hk⟩ Hw
    iexists bs
    iframe Hpt
    isplitr
    · ipureintro; exact hlen
    inext
    iintro Hpt
    imod Hk $$ Hpt with Hk
    imodintro
    iapply ih $$ Hk Hw
  | nonmem_store dmem a v k ih =>
    rw [Effects.AllI₀, Effects.AllI₀]
    iintro ⟨%old, %hlen, Hpt, Hk⟩ Hw
    iexists old
    iframe Hpt
    isplitr
    · ipureintro; exact hlen
    inext
    iintro Hpt
    imod Hk $$ Hpt with Hk
    imodintro
    iapply ih $$ Hk Hw
  | undefined k ih =>
    rw [Effects.AllI₀, Effects.AllI₀]
    iintro H Hw %v
    imod H $$ %v with H
    imodintro
    iapply ih $$ H Hw
  | require_read_access span k ih =>
    rw [Effects.AllI₀, Effects.AllI₀]
    exact ih ()
  | require_write_access span k ih =>
    rw [Effects.AllI₀, Effects.AllI₀]
    exact ih ()
  | require_exec_access p k ih =>
    rw [Effects.AllI₀, Effects.AllI₀]
    exact ih ()
  | yield k ih =>
    rw [Effects.AllI₀, Effects.AllI₀]
    iintro H Hw
    imod H
    imodintro
    imod H
    imodintro
    iapply ih $$ H Hw

theorem Effects.AllI_weaken (M : CoPset) (e : Effects) (post post' : MachineState → IProp GF) :
    e.AllI M post -∗ (∀ s, post s -∗ post' s) -∗ e.AllI M post' := by
  unfold Effects.AllI
  iintro H Hw
  imod H
  imodintro
  iapply Effects.AllI₀_weaken $$ H Hw

@[simp] theorem Effects.AllI_require_exec_access (M : CoPset) (p : Std.Rco Int64)
    (ok : Unit → Effects) (post : MachineState → IProp GF) :
    (Effects.require_exec_access p ok).AllI M post = (ok ()).AllI M post := by
  simp only [Effects.AllI, Effects.AllI₀]

@[simp] theorem Effects.AllI_require_read_access (M : CoPset) (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → IProp GF) :
    (require_access require_read_access addr bytes ok).AllI M post = (ok ()).AllI M post := by
  dsimp only [require_access]
  split <;> simp only [Effects.AllI, Effects.AllI₀]

@[simp] theorem Effects.AllI_require_write_access (M : CoPset) (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → IProp GF) :
    (require_access require_write_access addr bytes ok).AllI M post = (ok ()).AllI M post := by
  dsimp only [require_access]
  split <;> simp only [Effects.AllI, Effects.AllI₀]

end handler
