module

public import LeanQbe.T.LeanLCNF.Basic
public import LeanQbe.T.LeanLCNF.Lower
public import LeanQbe.T.LeanLCNF.Lower1
public import LeanQbe.T.LeanLCNF.Sem.SpecNorm
public import LeanQbe.T.LinkLfp
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.Logic.MemLemmas

/-!
# Tier-H Core Types, State, Invariants, and Reference-Counting Helpers (`HBase`)

Foundational types shared by `Sem/HPrim` and `Sem/H`:
- `Word`, typed constructors/extractors, little-endian scalar byte helpers.
- `HValEnv`, `paramsMatch`, `HState`, `HState.mem`, `HInv`.
- `HPost`, `HXPost`, `HSpec`, `HEnv`, `HJEnv`, refinement orders (`HSpec.le`, `HEnv.le`,
  `HJEnv.le`), and `HSpec.Mono`.
- `HDec1Pre`, `HDec1Rel`, `HDecN`, `HResetRelease`, `HState.casesTag`, and their monotonicity
  lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open Std.ExtHashMap

/-! ## 1. Words, Byte Helpers, and Environments -/

/-- A typed machine word carried in Tier-H variables and function boundaries. -/
abbrev Word : Type := (t : Ty) × Val t

/-- Construct a `Word` from an arbitrary `BitVec w`. -/
@[expose] def Word.bits {w : Nat} (v : BitVec w) : Word := ⟨.bits w, v⟩

/-- Construct a 64-bit `Word`. -/
@[expose] def Word.i64 (v : BitVec 64) : Word := ⟨.bits 64, v⟩

/-- Construct a 32-bit `Word`. -/
@[expose] def Word.i32 (v : BitVec 32) : Word := ⟨.bits 32, v⟩

/-- Construct a 16-bit `Word`. -/
@[expose] def Word.i16 (v : BitVec 16) : Word := ⟨.bits 16, v⟩

/-- Construct an 8-bit `Word`. -/
@[expose] def Word.i8 (v : BitVec 8) : Word := ⟨.bits 8, v⟩

/-- Extract a 64-bit bitvector from a `Word`. -/
@[expose] def Word.toBV64? : Word → Option (BitVec 64)
  | ⟨.bits 64, v⟩ => some v
  | _ => none

/-- Extract a `w`-bit bitvector from a `Word` (exact width match). -/
@[expose] def Word.toBits? (w : Nat) : Word → Option (BitVec w)
  | ⟨.bits m, v⟩ => if h : m = w then some (h ▸ v) else none
  | _ => none

/-- Extract the underlying `Nat` value of any bitvector `Word`. -/
@[expose] def Word.toNat? : Word → Option Nat
  | ⟨.bits _, v⟩ => some v.toNat
  | _ => none

/-- Zero-extend or truncate any bitvector `Word` to width `w` (matches `Lower.convW`). -/
@[expose] def Word.toWidth (w : Nat) : Word → Option Word
  | ⟨.bits _, v⟩ => some ⟨.bits w, v.setWidth w⟩
  | _ => none

/-- Convert a `LeanQbe.T.Tup Val ts` into a list of `Word`s. -/
@[expose] def wordsOfTup : {ts : List Ty} → Tup Val ts → List Word
  | [], () => []
  | t :: _, (v, vs) => ⟨t, v⟩ :: wordsOfTup vs

/-- Read `k` little-endian bytes from `bs` starting at `off` into a `Nat`. -/
@[expose] def readNatLE (bs : List UInt8) (off : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (bs.getD off 0).toNat + 256 * readNatLE bs (off + 1) k

/-- Read a `w`-bit little-endian value from `bs` starting at byte offset `off`. -/
@[expose] def readBitsLE (w : Nat) (bs : List UInt8) (off : Nat) : BitVec w :=
  BitVec.ofNat w (readNatLE bs off ((w + 7) / 8))

/-- Encode `n : Nat` into `k` little-endian bytes. -/
@[expose] def writeNatLE (n : Nat) : Nat → List UInt8
  | 0 => []
  | k + 1 => UInt8.ofNat (n % 256) :: writeNatLE (n / 256) k

/-- Overwrite `patch.length` bytes in `bs` starting at `off`. -/
@[expose] def writeBytesAt (bs : List UInt8) (off : Nat) (patch : List UInt8) : List UInt8 :=
  bs.take off ++ patch ++ bs.drop (off + patch.length)

/-- Named Tier-H local environment: variable id ↦ `(LcTy, Word)`. -/
abbrev HValEnv : Type := Nat → Option (LcTy × Word)

@[expose] def HValEnv.empty : HValEnv := fun _ => none

@[expose] def HValEnv.set (ρ : HValEnv) (x : Nat) (ty : LcTy) (w : Word) : HValEnv :=
  fun i => if i = x then some (ty, w) else ρ i

/-- Bind parameters left-to-right (matching `LCtx.bindAll`). -/
@[expose] def HValEnv.bindAll (ρ : HValEnv) : List LcParam → List Word → HValEnv
  | p :: ps, w :: ws => (ρ.set p.id p.ty w).bindAll ps ws
  | _, _ => ρ

/-- Evaluate an `LcArg` at expected type `t` (matching `Lower1.argAt`). -/
@[expose] def HValEnv.evalArgAt (ρ : HValEnv) (a : LcArg) (t : LcTy) : Option Word :=
  match a with
  | .erased => some ⟨t.toTTy, BitVec.ofNat t.width (if t.isScalar then 0 else 1)⟩
  | .var x =>
    match ρ x with
    | some (_, w) => if w.1 = t.toTTy then some w else none
    | none => none

/-- Evaluate an `LcArg` at its own type (matching `Lower1.argOwn`). -/
@[expose] def HValEnv.evalArgOwn (ρ : HValEnv) : LcArg → Option Word
  | .erased => some (Word.i64 1#64)
  | .var x => (ρ x).map Prod.snd

/-- Look up a 64-bit word for variable `x`. -/
@[expose] def HValEnv.getBV64? (ρ : HValEnv) (x : Nat) : Option (BitVec 64) :=
  (ρ.evalArgOwn (.var x)).bind Word.toBV64?

/-- Look up `(ty, addr64)` for variable `x`. -/
@[expose] def HValEnv.getTypedBV64? (ρ : HValEnv) (x : Nat) : Option (LcTy × BitVec 64) :=
  match ρ x with
  | some (ty, w) => (w.toBV64?).map (ty, ·)
  | none => none

/-- Evaluate an argument list at its own types. -/
@[expose] def HValEnv.evalArgsOwn (ρ : HValEnv) : List LcArg → Option (List Word)
  | [] => some []
  | a :: as =>
    match ρ.evalArgOwn a, ρ.evalArgsOwn as with
    | some w, some ws => some (w :: ws)
    | _, _ => none

/-- Evaluate an argument list as 64-bit object words (`.tobject`). -/
@[expose] def HValEnv.evalObjArgs (ρ : HValEnv) : List LcArg → Option (List (BitVec 64))
  | [] => some []
  | a :: as =>
    match (ρ.evalArgAt a .tobject).bind Word.toBV64?, ρ.evalObjArgs as with
    | some v, some ws => some (v :: ws)
    | _, _ => none

/-- Whether a list of `Word`s matches the parameter types of `ps`. -/
@[expose] def paramsMatch : List LcParam → List Word → Prop
  | [], [] => True
  | p :: ps, w :: ws => w.1 = p.ty.toTTy ∧ paramsMatch ps ws
  | _, _ => False

/-! ## 2. Tier-H State, Invariant, Contracts, and Environments -/

/-- Concrete heap/runtime state of the Tier-H operational semantics. -/
structure HState where
  st : RtC0State
  objs : List LcnfObj
  scr : BitVec 64
  scrLimbs : List (BitVec 64)

/-- Separation-logic memory footprint of an `HState` rooted at runtime pointer `rt`. -/
@[expose] def HState.mem (rt : BitVec 64) (σ : HState) : Mem 64 → Prop :=
  bigNumRtInv rt σ.st σ.scr σ.scrLimbs ⋆ lcnfHeap σ.objs

/-- Global well-formedness invariant of an `HState` rooted at `rt`:
`BigNumRtWf` (48-bit arena bound, non-overflowing header and scratch array).
Object-level `LcnfObj.Wf` and `lcnfHeapClosed` invariants live on the individual
`H*Wp` / `HDec1Pre` preconditions that actually require them. -/
@[expose] def HInv (rt : BitVec 64) (σ : HState) : Prop :=
  BigNumRtWf rt σ.st σ.scr σ.scrLimbs

/-- Return postcondition at Tier H. -/
abbrev HPost : Type := Word → HState → Prop

/-- Abnormal-exit postcondition at Tier H (panic code passed to `lcnf_panic`). -/
abbrev HXPost : Type := BitVec 64 → HState → Prop

/-- Tier-H function contract: args → state → normal post → panic post → Prop. -/
abbrev HSpec : Type := List Word → HState → HPost → HXPost → Prop

/-- Tier-H call environment for module declarations. -/
abbrev HEnv : Type := String → HSpec

/-- Tier-H join-point continuation environment. -/
abbrev HJEnv : Type := Nat → List Word → HState → Prop

@[expose] def HEnv.bot : HEnv := fun _ _ _ _ _ => False

@[expose] def HJEnv.empty : HJEnv := fun _ _ _ => False

@[expose] def HJEnv.set (J : HJEnv) (j : Nat) (Jj : List Word → HState → Prop) : HJEnv :=
  fun i => if i = j then Jj else J i

/-- Pointwise refinement order on Tier-H specs, call environments, and join environments. -/
@[expose] def HSpec.le (S₁ S₂ : HSpec) : Prop :=
  ∀ as σ Q X, S₁ as σ Q X → S₂ as σ Q X

@[expose] def HEnv.le (Δ₁ Δ₂ : HEnv) : Prop :=
  ∀ f, HSpec.le (Δ₁ f) (Δ₂ f)

@[expose] def HJEnv.le (J₁ J₂ : HJEnv) : Prop :=
  ∀ j as σ, J₁ j as σ → J₂ j as σ

@[expose] def HSpec.Mono (S : HSpec) : Prop :=
  ∀ as σ (Q₁ Q₂ : HPost) (X₁ X₂ : HXPost),
    (∀ r σ', Q₁ r σ' → Q₂ r σ') → (∀ c σ', X₁ c σ' → X₂ c σ') →
    S as σ Q₁ X₁ → S as σ Q₂ X₂

/-! ## 3. Reference-Counting, Reset-Release, & Case-Tag Helpers -/

/-- Precondition for a single `dec` step (`Lower.emitDec1`). -/
@[expose] def HDec1Pre (x : BitVec 64) (ty : LcTy) (chk : Bool) (σ : HState) : Prop :=
  if !ty.needsRc then True
  else if (x &&& 1#64) ≠ 0#64 then chk = true ∧ ty = .tobject
  else
    ∃ o ∈ σ.objs, o.addr = x ∧ o.Wf ∧
      (o.rc = 1#32 → σ.objs.length ≤ σ.st.workCap ∧
        (∀ obj ∈ σ.objs, obj.Wf) ∧ lcnfHeapClosed σ.objs ∧ RcSound x σ.objs)

/-- Relational post-state for a single `dec` step (`Lower.emitDec1`). -/
@[expose] def HDec1Rel (x : BitVec 64) (ty : LcTy) (σ σ' : HState) : Prop :=
  if !ty.needsRc then σ' = σ
  else if (x &&& 1#64) ≠ 0#64 then σ' = σ
  else
    (∃ o ∈ σ.objs, o.addr = x ∧ o.rc = 0#32 ∧ σ' = σ) ∨
    (∃ (idx : Nat) (hidx : idx < σ.objs.length),
      σ.objs[idx].addr = x ∧ 1 < σ.objs[idx].rc.toInt ∧
      σ' = { σ with objs := σ.objs.set idx (σ.objs[idx].withRc (σ.objs[idx].rc - 1#32)) }) ∨
    (σ'.st.PreservesMeta σ.st ∧ σ'.st.rem = σ.st.rem ∧
      σ'.scr = σ.scr ∧ σ'.scrLimbs = σ.scrLimbs ∧ DecColdRel x σ.objs σ'.objs)

/-- Weakest precondition of `n` consecutive `dec` steps (`Lower.emitDec`). -/
@[expose] def HDecN (x : BitVec 64) (ty : LcTy) (chk : Bool) :
    Nat → (HState → Prop) → HState → Prop
  | 0, K, σ => K σ
  | n + 1, K, σ =>
    HDec1Pre x ty chk σ ∧ ∀ σ', HDec1Rel x ty σ σ' → HDecN x ty chk n K σ'

/-- Exclusive-field release loop for `LcVal.reset` (`Lower1.lowerReset`). -/
@[expose] def HResetRelease (addr : BitVec 64) (n : Nat) (K : HPost) : Nat → HState → Prop
  | 0, σ => K (Word.i64 addr) σ
  | i + 1, σ =>
    let fi := n - 1 - i
    ∃ (idx : Nat) (hidx : idx < σ.objs.length),
      let o := σ.objs[idx]'hidx
      o.addr = addr ∧ fi < o.fields.length ∧
      HDecN (o.fields.getD fi 1#64) .tobject true 1
        (fun σ' =>
          ∃ (idx2 : Nat) (hidx2 : idx2 < σ'.objs.length),
            let o2 := σ'.objs[idx2]'hidx2
            let o2' : LcnfObj := { o2 with fields := o2.fields.set fi 1#64 }
            o2.addr = addr ∧
            HResetRelease addr n K i { σ' with objs := σ'.objs.set idx2 o2' }) σ

/-- Tag extraction for `LcCode.cases x alts`, aligned with `Lower1.lowerCases`. -/
@[expose] def HState.casesTag (ρ : HValEnv) (σ : HState) (x : Nat) (tag : Nat) : Prop :=
  match ρ x with
  | some (ty, ⟨.bits w, v⟩) =>
    w = ty.width ∧
    if ty.isScalar then tag = v.toNat
    else
      let v64 : BitVec 64 := v.setWidth 64
      if ty = .object then
        w = 64 ∧ ∃ o ∈ σ.objs, o.addr = v64 ∧ o.Wf ∧ tag = o.tag
      else if ty = .tagged then
        w = 64 ∧ tag = (v64 >>> 1).toNat
      else
        w = 64 ∧
        if (v64 &&& 1#64) ≠ 0#64 then tag = (v64 >>> 1).toNat
        else ∃ o ∈ σ.objs, o.addr = v64 ∧ o.Wf ∧ tag = o.tag
  | _ => False

/-! ## 4. Order and RC Monotonicity Lemmas -/

theorem HSpec.le_refl (S : HSpec) : HSpec.le S S := fun _ _ _ _ h => h

theorem HSpec.le_trans {S₁ S₂ S₃ : HSpec} (h12 : HSpec.le S₁ S₂) (h23 : HSpec.le S₂ S₃) :
    HSpec.le S₁ S₃ := fun as σ Q X h => h23 as σ Q X (h12 as σ Q X h)

theorem HEnv.le_refl (Δ : HEnv) : HEnv.le Δ Δ := fun _ => HSpec.le_refl _

theorem HEnv.le_trans {Δ₁ Δ₂ Δ₃ : HEnv} (h12 : HEnv.le Δ₁ Δ₂) (h23 : HEnv.le Δ₂ Δ₃) :
    HEnv.le Δ₁ Δ₃ := fun f => HSpec.le_trans (h12 f) (h23 f)

theorem HJEnv.le_refl (J : HJEnv) : HJEnv.le J J := fun _ _ _ h => h

theorem HJEnv.le_set {J₁ J₂ : HJEnv} (hJ : HJEnv.le J₁ J₂) (j : Nat)
    (Jj : List Word → HState → Prop) : HJEnv.le (J₁.set j Jj) (J₂.set j Jj) := by
  intro i as σ h
  dsimp only [HJEnv.set] at h ⊢
  by_cases heq : i = j
  · simp [heq] at h ⊢; exact h
  · simp [heq] at h ⊢; exact hJ i as σ h

theorem HDecN_mono {x : BitVec 64} {ty : LcTy} {chk : Bool} {K₁ K₂ : HState → Prop}
    (hK : ∀ σ, K₁ σ → K₂ σ) :
    ∀ n σ, HDecN x ty chk n K₁ σ → HDecN x ty chk n K₂ σ
  | 0, _, h => hK _ h
  | n + 1, _, ⟨hpre, hcont⟩ =>
    ⟨hpre, fun σ' hrel => HDecN_mono hK n σ' (hcont σ' hrel)⟩

theorem HResetRelease_mono {addr : BitVec 64} {n : Nat} {K₁ K₂ : HPost}
    (hK : ∀ r σ, K₁ r σ → K₂ r σ) :
    ∀ k σ, HResetRelease addr n K₁ k σ → HResetRelease addr n K₂ k σ
  | 0, _, h => hK _ _ h
  | k + 1, _, ⟨idx, hidx, ha, hlt, hdec⟩ =>
    ⟨idx, hidx, ha, hlt, HDecN_mono (fun _ ⟨idx2, hidx2, ha2, hrec⟩ =>
      ⟨idx2, hidx2, ha2, HResetRelease_mono hK k _ hrec⟩) 1 _ hdec⟩

end LeanQbe.T.LeanLCNF.Sem
