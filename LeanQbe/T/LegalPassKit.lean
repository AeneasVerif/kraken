module

public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Legal

/-!
# Shared Legal `supportsSource` Structural Helpers (`LegalPassKit`)

Factorizes `TFlat.supportsSource` / `TBlocks.supportsSource` block access, reconstruction, and
`toTFlat` constructor simplifications used across `LicmRoLemmas` and `LicmLemmas`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

namespace LegalPassKit

theorem toTBlocks_supportsSource_get_full (target : LegalTarget) {rs : List Ty} (nv nl : Nat) :
    ∀ {sig : List (List Ty)} (bs : Blocks K KL rs sig),
      (toTBlocks bs nv nl).supportsSource target = true →
      ∀ {ts} (i : Member ts sig),
        ts.all target.supportsTy = true ∧
        (toTFlat (bs.get i (Tup.levels ts nv)) (nv + ts.length) nl).supportsSource target = true
  | _, .nil, _, _, i => nomatch i
  | _, .cons _ bs, hs, _, .here => by
    dsimp only [toTBlocks, TBlocks.supportsSource] at hs
    simp only [Bool.and_eq_true] at hs
    exact ⟨hs.1.1, hs.1.2⟩
  | _, .cons _ bs, hs, _, .there i => by
    dsimp only [toTBlocks, TBlocks.supportsSource] at hs
    simp only [Bool.and_eq_true] at hs
    exact toTBlocks_supportsSource_get_full target nv nl bs hs.2 i

theorem toTBlocks_supportsSource_get (target : LegalTarget) {rs : List Ty} (nv nl : Nat)
    {sig : List (List Ty)} (bs : Blocks K KL rs sig)
    (hs : (toTBlocks bs nv nl).supportsSource target = true)
    {ts} (i : Member ts sig) :
    (toTFlat (bs.get i (Tup.levels ts nv)) (nv + ts.length) nl).supportsSource target = true :=
  (toTBlocks_supportsSource_get_full target nv nl bs hs i).2

theorem toTBlocks_supportsSource_of_get (target : LegalTarget) {rs : List Ty} (nv nl : Nat) :
    ∀ {sig : List (List Ty)} (bs : Blocks K KL rs sig),
      sig.all (·.all target.supportsTy) = true →
      (∀ {ts} (i : Member ts sig),
        (toTFlat (bs.get i (Tup.levels ts nv)) (nv + ts.length) nl).supportsSource target = true) →
      (toTBlocks bs nv nl).supportsSource target = true
  | [], .nil, _, _ => rfl
  | _ :: _, .cons _ bs, hsig, hget => by
    dsimp only [List.all_cons] at hsig
    simp only [Bool.and_eq_true] at hsig
    dsimp only [toTBlocks, TBlocks.supportsSource]
    simp only [Bool.and_eq_true]
    exact ⟨⟨hsig.1, hget .here⟩, toTBlocks_supportsSource_of_get target nv nl bs hsig.2
      (fun i => hget (.there i))⟩

theorem TFlat.supportsSource_let {target : LegalTarget} {rs ts : List Ty}
    {op : Op K ts} {k : TFlat rs} :
    (TFlat.let_ op k).supportsSource target = true ↔
      target.supportsOpCode op.code = true ∧ k.supportsSource target = true := by
  simp [TFlat.supportsSource]

theorem TFlat.supportsSource_load {target : LegalTarget} {rs : List Ty}
    {t : Ty} {a : Arg K i64} {k : TFlat rs} :
    (TFlat.load t a k).supportsSource target = true ↔
      (target.supportsTy t = true ∧ t.bytes ≤ 2 ^ 64) ∧ k.supportsSource target = true := by
  simp [TFlat.supportsSource, Bool.and_assoc, and_assoc]

theorem TFlat.supportsSource_store {target : LegalTarget} {rs : List Ty}
    {t : Ty} {v : Arg K t} {a : Arg K i64} {k : TFlat rs} :
    (TFlat.store v a k).supportsSource target = true ↔
      (target.supportsTy t = true ∧ t.bytes ≤ 2 ^ 64) ∧ k.supportsSource target = true := by
  simp [TFlat.supportsSource, Bool.and_assoc, and_assoc]

theorem TFlat.supportsSource_call {target : LegalTarget} {rs : List Ty}
    {f : Sym} {as bs : List Ty} {args : Tup (Arg K) as} {k : TFlat rs} :
    (TFlat.call f bs args k).supportsSource target = true ↔
      (as.all target.supportsTy = true ∧ bs.all target.supportsTy = true) ∧
        k.supportsSource target = true := by
  simp [TFlat.supportsSource, Bool.and_assoc, and_assoc]

theorem TFlat.supportsSource_jnz {target : LegalTarget} {rs : List Ty}
    {c : Arg K .bool} {t e : TFlat rs} :
    (TFlat.jnz c t e).supportsSource target = true ↔
      t.supportsSource target = true ∧ e.supportsSource target = true := by
  simp [TFlat.supportsSource]

theorem TFlat.supportsSource_group {target : LegalTarget} {rs : List Ty}
    {sig : List (List Ty)} {bs : TBlocks rs sig} {k : TFlat rs} :
    (TFlat.group bs k).supportsSource target = true ↔
      sig.all (·.all target.supportsTy) = true ∧
        bs.supportsSource target = true ∧ k.supportsSource target = true := by
  simp [TFlat.supportsSource, Bool.and_assoc]

theorem toTFlat_supportsSource_let {target : LegalTarget} {rs ts : List Ty}
    {op : Op K ts} {k : Tup K ts → Expr K KL rs} {nv nl : Nat} :
    (toTFlat (.let_ op k) nv nl).supportsSource target = true ↔
      target.supportsOpCode op.code = true ∧
        (toTFlat (k (Tup.levels ts nv)) (nv + ts.length) nl).supportsSource target = true :=
  TFlat.supportsSource_let

theorem toTFlat_supportsSource_load {target : LegalTarget} {rs : List Ty}
    {t : Ty} {a : Arg K i64} {k : K t → Expr K KL rs} {nv nl : Nat} :
    (toTFlat (.load t a k) nv nl).supportsSource target = true ↔
      (target.supportsTy t = true ∧ t.bytes ≤ 2 ^ 64) ∧
        (toTFlat (k nv) (nv + 1) nl).supportsSource target = true :=
  TFlat.supportsSource_load

theorem toTFlat_supportsSource_store {target : LegalTarget} {rs : List Ty}
    {t : Ty} {v : Arg K t} {a : Arg K i64} {k : Expr K KL rs} {nv nl : Nat} :
    (toTFlat (.store v a k) nv nl).supportsSource target = true ↔
      (target.supportsTy t = true ∧ t.bytes ≤ 2 ^ 64) ∧
        (toTFlat k nv nl).supportsSource target = true :=
  TFlat.supportsSource_store

theorem toTFlat_supportsSource_call {target : LegalTarget} {rs : List Ty}
    {f : Sym} {as bs : List Ty} {args : Tup (Arg K) as}
    {k : Tup K bs → Expr K KL rs} {nv nl : Nat} :
    (toTFlat (.call f (bs := bs) args k) nv nl).supportsSource target = true ↔
      (as.all target.supportsTy = true ∧ bs.all target.supportsTy = true) ∧
        (toTFlat (k (Tup.levels bs nv)) (nv + bs.length) nl).supportsSource target = true :=
  TFlat.supportsSource_call

theorem toTFlat_supportsSource_jnz {target : LegalTarget} {rs : List Ty}
    {c : Arg K .bool} {t e : Expr K KL rs} {nv nl : Nat} :
    (toTFlat (.jnz c t e) nv nl).supportsSource target = true ↔
      (toTFlat t nv nl).supportsSource target = true ∧
        (toTFlat e nv nl).supportsSource target = true :=
  TFlat.supportsSource_jnz

theorem toTFlat_supportsSource_group {target : LegalTarget} {rs : List Ty}
    {sig : List (List Ty)} {bs : Tup KL sig → Blocks K KL rs sig}
    {k : Tup KL sig → Expr K KL rs} {nv nl : Nat} :
    (toTFlat (.group bs k) nv nl).supportsSource target = true ↔
      sig.all (·.all target.supportsTy) = true ∧
        (toTBlocks (bs (Tup.levels sig nl)) nv (nl + sig.length)).supportsSource target = true ∧
        (toTFlat (k (Tup.levels sig nl)) nv (nl + sig.length)).supportsSource target = true :=
  TFlat.supportsSource_group

end LegalPassKit

end LeanQbe.T
