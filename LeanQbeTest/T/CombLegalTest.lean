module

public import LeanQbe.T.Logic.ControlComb
public import LeanQbe.T.LegalEmit
public import LeanQbe.T.LegalCheck1
public import LeanQbe.T.LegalWfBaseLemmas1
public import LeanQbe.T.LegalWpBaseLemmas1
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Examples.LratBytesDimacsLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification and Axiom Audit for `ControlComb` and `LegalEmit`

Exercises:
1. All 5 `LegalBase` builders (`emitBoolCmp`, `emitBoolSelect`, `emitMaskToN`, `emitSextToW`,
   `emitTernlogBool`) via `Emit` `rfl`-compatible compilation and single-pass `LegalEmitSpec`
   bundles (`isLegal`, `Wf`, `wp`), plus a composed `Emit` pipeline.
2. State-indexed PHOAS combinators (`wp_join_state`, `wp_join_state1`, `wp_while_state`,
   `wp_while_state1`, `wp_jnz_decide`) on real `LratBytes` code (`skipWs1Qbe` and `readLeb128`).
3. Single-line `#print axioms` checks (`≤ 100` cols) strictly `⊆ [propext, Classical.choice,
   Quot.sound]`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.CombLegalTest

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test

/-! ## 1. Definitional (`rfl`) compatibility with all 5 `LegalBase` builders -/

section RflBridges

example {V L rs} (a b : Arg V .bool) (k : Arg V .bool → Expr V L rs) :
    (boolCmpEmit .eq).run (a, b, ()) k = emitBoolCmp .eq a b k := rfl
example {V L rs} (a b : Arg V .bool) (k : Arg V .bool → Expr V L rs) :
    (boolCmpEmit .ult).run (a, b, ()) k = emitBoolCmp .ult a b k := rfl
example {V L rs} (a b : Arg V .bool) (k : Arg V .bool → Expr V L rs) :
    (boolCmpEmit .sge).run (a, b, ()) k = emitBoolCmp .sge a b k := rfl
example {V L rs} (c a b : Arg V .bool) (k : Arg V .bool → Expr V L rs) :
    boolSelectEmit.run (c, a, b, ()) k = emitBoolSelect c a b k := rfl
example {V L rs} (x : Arg V (.bits 32)) (k : Arg V (.bits 32) → Expr V L rs) :
    (maskToNEmit 0 32).run (x, ()) k = emitMaskToN 0 32 x k := rfl
example {V L rs} (x : Arg V (.bits 32)) (k : Arg V (.bits 32) → Expr V L rs) :
    (maskToNEmit 13 32).run (x, ()) k = emitMaskToN 13 32 x k := rfl
example {V L rs} (x : Arg V (.bits 32)) (k : Arg V (.bits 32) → Expr V L rs) :
    (maskToNEmit 32 32).run (x, ()) k = emitMaskToN 32 32 x k := rfl
example {V L rs} (x : Arg V (.bits 32)) (k : Arg V (.bits 32) → Expr V L rs) :
    (sextToWEmit 32 32).run (x, ()) k = emitSextToW 32 32 x k := rfl
example {V L rs} (x : Arg V (.bits 32)) (k : Arg V (.bits 32) → Expr V L rs) :
    (sextToWEmit 7 32).run (x, ()) k = emitSextToW 7 32 x k := rfl
example {V L rs} (a b c : Arg V .bool) (k : Arg V .bool → Expr V L rs) :
    (ternlogBoolEmit 0#8).run (a, b, c, ()) k = emitTernlogBool a b c 0#8 k := rfl
example {V L rs} (a b c : Arg V .bool) (k : Arg V .bool → Expr V L rs) :
    (ternlogBoolEmit 0xff#8).run (a, b, c, ()) k = emitTernlogBool a b c 0xff#8 k := rfl

end RflBridges

/-! ## 2. Exact `isLegal` + `Wf` + `wp` reconstruction for all 5 `LegalBase` builders -/

theorem test_emitBoolCmp_isLegal (target : LegalTarget) {Γ Δ rs} (o : CmpOp)
    (a b : Arg K .bool) (ha : ArgNormal target Γ .bool a) (hb : ArgNormal target Γ .bool b)
    {k : Arg K .bool → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' .bool r) k) :
    (toTFlat (emitBoolCmp o a b k) Γ.length Δ.length).isLegal target Γ Δ = true :=
  (boolCmpEmit_bundle target o).isLegal_eq (a, b, ()) ⟨ha, hb, trivial⟩ hk
    (boolCmpEmit_eq_emitBoolCmp o a b k)

theorem test_emitBoolCmp_wf {V₁ V₂ L₁ L₂ rs} {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (o : CmpOp)
    {a₁ b₁ : Arg V₁ .bool} {a₂ b₂ : Arg V₂ .bool}
    (ha : ArgRel G .bool a₁ a₂) (hb : ArgRel G .bool b₁ b₂)
    {k₁ : Arg V₁ .bool → Expr V₁ L₁ rs} {k₂ : Arg V₂ .bool → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' .bool y₁ y₂ →
      Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitBoolCmp o a₁ b₁ k₁) (emitBoolCmp o a₂ b₂ k₂) :=
  (boolCmpEmit_bundle .aarch64 o).wf_eq (.cons ha (.cons hb .nil)) hk
    (boolCmpEmit_eq_emitBoolCmp o a₁ b₁ k₁) (boolCmpEmit_eq_emitBoolCmp o a₂ b₂ k₂)

theorem test_emitBoolCmp_wp {Γ rs Q X m} (o : CmpOp) (a b : Arg Val .bool)
    {k : Arg Val .bool → Expr Val Cont rs}
    (hk : ∀ r, r.val = o.evalBool a.val b.val → wp Γ Q X (k r) m) :
    wp Γ Q X (emitBoolCmp o a b k) m :=
  (boolCmpEmit_bundle .aarch64 o).wp_eq (a, b, ()) hk (boolCmpEmit_eq_emitBoolCmp o a b k)

theorem test_emitBoolSelect_all (target : LegalTarget) :
    (∀ {Γ Δ rs} (c a b : Arg K .bool),
      ArgNormal target Γ .bool c → ArgNormal target Γ .bool a → ArgNormal target Γ .bool b →
      ∀ {k : Arg K .bool → Expr K KL rs},
        IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' .bool r) k →
        (toTFlat (emitBoolSelect c a b k) Γ.length Δ.length).isLegal target Γ Δ = true) ∧
    (∀ {V₁ V₂ L₁ L₂ rs} {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {c₁ a₁ b₁ : Arg V₁ .bool} {c₂ a₂ b₂ : Arg V₂ .bool},
      ArgRel G .bool c₁ c₂ → ArgRel G .bool a₁ a₂ → ArgRel G .bool b₁ b₂ →
      ∀ {k₁ : Arg V₁ .bool → Expr V₁ L₁ rs} {k₂ : Arg V₂ .bool → Expr V₂ L₂ rs},
        (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' .bool y₁ y₂ →
          Wf G' D (k₁ y₁) (k₂ y₂)) →
        Wf G D (emitBoolSelect c₁ a₁ b₁ k₁) (emitBoolSelect c₂ a₂ b₂ k₂)) ∧
    (∀ {Γ rs Q X m} (c a b : Arg Val .bool) {k : Arg Val .bool → Expr Val Cont rs},
      (∀ r, r.val = (if c.val then a.val else b.val) → wp Γ Q X (k r) m) →
      wp Γ Q X (emitBoolSelect c a b k) m) :=
  ⟨fun c a b hc ha hb _ hk =>
    (boolSelectEmit_bundle target).isLegal_eq (c, a, b, ()) ⟨hc, ha, hb, trivial⟩ hk rfl,
   fun hc ha hb _ _ hk =>
    (boolSelectEmit_bundle target).wf_eq (.cons hc (.cons ha (.cons hb .nil))) hk rfl rfl,
   fun c a b _ hk =>
    (boolSelectEmit_bundle target).wp_eq (c, a, b, ()) hk rfl⟩

theorem test_emitMaskToN_all (target : LegalTarget) {n w : Nat}
    (hw : w ∈ target.bitWidths) (hnw : n ≤ w) :
    (∀ {Γ Δ rs} (x : Arg K (.bits w)), ArgNormal target Γ (.bits w) x →
      ∀ {k : Arg K (.bits w) → Expr K KL rs},
        IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits w) r) k →
        (toTFlat (emitMaskToN n w x k) Γ.length Δ.length).isLegal target Γ Δ = true) ∧
    (∀ {V₁ V₂ L₁ L₂ rs} {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {x₁ : Arg V₁ (.bits w)} {x₂ : Arg V₂ (.bits w)},
      ArgRel G (.bits w) x₁ x₂ →
      ∀ {k₁ : Arg V₁ (.bits w) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.bits w) → Expr V₂ L₂ rs},
        (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits w) y₁ y₂ →
          Wf G' D (k₁ y₁) (k₂ y₂)) →
        Wf G D (emitMaskToN n w x₁ k₁) (emitMaskToN n w x₂ k₂)) ∧
    (∀ {Γ rs Q X m} {x : Arg Val (.bits w)} {v : BitVec w},
      x.val = v → ∀ {k : Arg Val (.bits w) → Expr Val Cont rs},
      (∀ r, r.val = (v.setWidth n).setWidth w → wp Γ Q X (k r) m) →
      wp Γ Q X (emitMaskToN n w x k) m) :=
  ⟨fun x hx _ hk =>
    (maskToNEmit_bundle target hw hnw).isLegal_eq (x, ()) ⟨hx, trivial⟩ hk
      (maskToNEmit_eq_emitMaskToN n w x _),
   fun hx k₁ k₂ hk =>
    (maskToNEmit_bundle target hw hnw).wf_eq (.cons hx .nil) hk
      (maskToNEmit_eq_emitMaskToN n w _ k₁) (maskToNEmit_eq_emitMaskToN n w _ k₂),
   fun {_ _ _ _ _ x _} hx _ hk =>
    (maskToNEmit_bundle target hw hnw).wp_eq (x, ()) (fun r hr => hk r (hx ▸ hr))
      (maskToNEmit_eq_emitMaskToN n w x _)⟩

theorem test_emitSextToW_all (target : LegalTarget) {n w : Nat}
    (hw : w ∈ target.bitWidths) (hn0 : 0 < n) (hnw : n ≤ w) :
    (∀ {Γ Δ rs} (x : Arg K (.bits w)), ArgNormal target Γ (.bits w) x →
      ∀ {k : Arg K (.bits w) → Expr K KL rs},
        IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' (.bits w) r) k →
        (toTFlat (emitSextToW n w x k) Γ.length Δ.length).isLegal target Γ Δ = true) ∧
    (∀ {V₁ V₂ L₁ L₂ rs} {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {x₁ : Arg V₁ (.bits w)} {x₂ : Arg V₂ (.bits w)},
      ArgRel G (.bits w) x₁ x₂ →
      ∀ {k₁ : Arg V₁ (.bits w) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.bits w) → Expr V₂ L₂ rs},
        (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits w) y₁ y₂ →
          Wf G' D (k₁ y₁) (k₂ y₂)) →
        Wf G D (emitSextToW n w x₁ k₁) (emitSextToW n w x₂ k₂)) ∧
    (∀ {Γ rs Q X m} {x : Arg Val (.bits w)} {a : BitVec n},
      x.val = a.setWidth w → ∀ {k : Arg Val (.bits w) → Expr Val Cont rs},
      (∀ r, r.val = a.signExtend w → wp Γ Q X (k r) m) →
      wp Γ Q X (emitSextToW n w x k) m) :=
  ⟨fun x hx _ hk =>
    (sextToWEmit_bundle target hw hn0 hnw).isLegal_eq (x, ()) ⟨hx, trivial⟩ hk
      (sextToWEmit_eq_emitSextToW n w x _),
   fun hx k₁ k₂ hk =>
    (sextToWEmit_bundle target hw hn0 hnw).wf_eq (.cons hx .nil) hk
      (sextToWEmit_eq_emitSextToW n w _ k₁) (sextToWEmit_eq_emitSextToW n w _ k₂),
   fun {_ _ _ _ _ x a} hx _ hk =>
    (sextToWEmit_bundle target hw hn0 hnw).wp_eq (x, ()) ⟨a, hx, hk⟩
      (sextToWEmit_eq_emitSextToW n w x _)⟩

theorem test_emitTernlogBool_all (target : LegalTarget) (imm : BitVec 8) :
    (∀ {Γ Δ rs} (a b c : Arg K .bool),
      ArgNormal target Γ .bool a → ArgNormal target Γ .bool b → ArgNormal target Γ .bool c →
      ∀ {k : Arg K .bool → Expr K KL rs},
        IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' .bool r) k →
        (toTFlat (emitTernlogBool a b c imm k) Γ.length Δ.length).isLegal target Γ Δ = true) ∧
    (∀ {V₁ V₂ L₁ L₂ rs} {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {a₁ b₁ c₁ : Arg V₁ .bool} {a₂ b₂ c₂ : Arg V₂ .bool},
      ArgRel G .bool a₁ a₂ → ArgRel G .bool b₁ b₂ → ArgRel G .bool c₁ c₂ →
      ∀ {k₁ : Arg V₁ .bool → Expr V₁ L₁ rs} {k₂ : Arg V₂ .bool → Expr V₂ L₂ rs},
        (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' .bool y₁ y₂ →
          Wf G' D (k₁ y₁) (k₂ y₂)) →
        Wf G D (emitTernlogBool a₁ b₁ c₁ imm k₁) (emitTernlogBool a₂ b₂ c₂ imm k₂)) ∧
    (∀ {Γ rs Q X m} (a b c : Arg Val .bool) {k : Arg Val .bool → Expr Val Cont rs},
      (∀ r, r.val = ternaryLogicBool a.val b.val c.val imm → wp Γ Q X (k r) m) →
      wp Γ Q X (emitTernlogBool a b c imm k) m) :=
  ⟨fun a b c ha hb hc _ hk =>
    (ternlogBoolEmit_bundle target imm).isLegal_eq (a, b, c, ()) ⟨ha, hb, hc, trivial⟩ hk
      (ternlogBoolEmit_eq_emitTernlogBool imm a b c _),
   fun ha hb hc k₁ k₂ hk =>
    (ternlogBoolEmit_bundle target imm).wf_eq (.cons ha (.cons hb (.cons hc .nil))) hk
      (ternlogBoolEmit_eq_emitTernlogBool imm _ _ _ k₁)
      (ternlogBoolEmit_eq_emitTernlogBool imm _ _ _ k₂),
   fun a b c _ hk =>
    (ternlogBoolEmit_bundle target imm).wp_eq (a, b, c, ()) hk
      (ternlogBoolEmit_eq_emitTernlogBool imm a b c _)⟩

/-- Composed custom `Emit` builder (`boolEqXorEmit`) verified with `Emit.bundlePure`. -/
def boolIffXorEmit : Emit [.bool, .bool] .bool :=
  .letE (.op2 (.xor .bool) (.arg .here) (.arg (.there .here)))
    (.op1 (.not .bool) (.arg .here))

theorem boolIffXorEmit_bundle (target : LegalTarget) :
    LegalEmitSpec target boolIffXorEmit (fun (a, b, ()) p => p (a == b)) :=
  boolIffXorEmit.bundlePure target (fun (a, b, ()) => a == b)
    (by simp [boolIffXorEmit, Emit.IsLegal, OpCode.isPackBridge,
      LegalTarget.isLegalOp, LegalTarget.isLegalTy])
    (fun (a, b, ()) => by
      cases a <;> cases b <;> simp [boolIffXorEmit, Emit.wp, Tup.get, OpCode.wp, lift1, lift2])

/-! ## 3. Real `LratBytes` examples using `wp_join_state`, `wp_while_state`, `wp_jnz_decide` -/

/-- `LratBytes.skipWs1Qbe` verified via `wp_join_state1`, `wp_while_state1`, and `wp_jnz_decide`
(zero existential tuple repacking). -/
theorem skipWs1Qbe_spec_comb {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {fail : Cont []}
    {base : BitVec 64} {bs : List UInt8} {i0 : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {done : BitVec 64 → Expr Val Cont rs}
    (hbase : base.toNat + bs.length < 2 ^ 64)
    (hi0 : i0 ≤ bs.length)
    (hm : (Eq (bs.At base) ⋆ R) m)
    (hfail : skipWs1 (bs.drop i0) = none → fail () m)
    (hdone : ∀ j rest, skipWs1 (bs.drop i0) = some rest →
      i0 < j → j ≤ bs.length → bs.drop j = rest →
      wp Γ Q X (done (base + BitVec.ofNat 64 j)) m) :
    wp Γ Q X (skipWs1Qbe fail (base + BitVec.ofNat 64 i0)
      (base + BitVec.ofNat 64 bs.length) done) m := by
  unfold skipWs1Qbe; wp_unfold
  refine cursor_loadu8_branch hbase hi0 hm (fun _ hnil => hfail (by simp [hnil, skipWs1]))
    (fun _ hdrop0 => ?_)
  rw [setWidth64_ofNat8]; refine isWsByte_spec ?_
  refine wp_jnz_decide (isDimacsWs bs[i0] = true) ?_ ?_ ?_
  · simp
  · intro hws0
    have hsw1 : skipWs1 (bs.drop i0) = some (skipWs (bs.drop (i0 + 1))) := by
      rw [hdrop0]; simp [skipWs1, hws0]
    refine wp_join_state1 (α := Nat) (fun j => base + BitVec.ofNat 64 j)
      (fun j m' =>
        i0 < j ∧ j ≤ bs.length ∧ bs.drop j = skipWs (bs.drop (i0 + 1)) ∧ m' = m)
      (fun _ j m' ⟨hj1, hj2, hdrop, hmEq⟩ => hmEq ▸ hdone j _ hsw1 hj1 hj2 hdrop)
      (fun Jdone hJdone => ?_)
    refine wp_while_state1 (α := Nat) (fun i => base + BitVec.ofNat 64 i) (fun i => bs.length - i)
      (fun i m' =>
        i0 < i ∧ i ≤ bs.length ∧ skipWs (bs.drop i) = skipWs (bs.drop (i0 + 1)) ∧ m' = m)
      (fun _ hJsw => by
        wp_unfold; rw [ptr_step_1]; exact hJsw (i0 + 1) m ⟨by omega, by omega, rfl, rfl⟩)
      (fun _ i m' ⟨hi1, hi2, hinv, hmEq⟩ ih => ?_)
    subst m'
    dsimp only [Blocks.get_here]; wp_unfold
    refine cursor_loadu8_branch hbase hi2 hm
      (fun heq hnil => by
        subst heq
        exact hJdone bs.length m
          ⟨hi1, Nat.le_refl _, by simpa [hnil, skipWs] using hinv, rfl⟩)
      (fun _ hdrop_i => ?_)
    rw [setWidth64_ofNat8]; refine isWsByte_spec ?_
    refine wp_jnz_decide (isDimacsWs bs[i] = true) ?_ ?_ ?_
    · simp
    · intro hws
      wp_unfold; rw [ptr_step_1]
      exact ih (i + 1) m (by omega)
        ⟨by omega, by omega,
          by rw [hdrop_i, skipWs] at hinv; simpa [hws] using hinv, rfl⟩
    · intro hnws
      wp_unfold
      exact hJdone i m
        ⟨hi1, hi2, by rw [hdrop_i, skipWs] at hinv; simpa [hnws, ← hdrop_i] using hinv,
          rfl⟩
  · intro hnws0; wp_unfold; exact hfail (by rw [hdrop0]; simp [skipWs1, hnws0])

private theorem lo7_shift_lt_test {x sh : Nat} (hsh : sh ≤ 21) :
    (x &&& 127) <<< sh < 2 ^ 28 := by
  rw [Nat.shiftLeft_eq]
  have h1 : x &&& 127 < 2 ^ 7 := Nat.and_lt_two_pow x (n := 7) (by decide)
  have h2 : 2 ^ sh ≤ 2 ^ 21 := Nat.pow_le_pow_right (by omega) hsh
  have h3 : (x &&& 127) * 2 ^ sh < 2 ^ 7 * 2 ^ 21 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ h2) (Nat.mul_lt_mul_of_pos_right h1 (by decide))
  omega

/-- Logical state for `readLeb128` loop: `(fuel, idx, acc, shift)`. -/
private structure LebState where
  fuel : Nat
  idx : Nat
  acc : Nat
  sh : Nat

/-- `LratBytes.readLeb128` verified via `wp_join_state`, `wp_while_state`, and `wp_jnz_decide`
(both equality-zero and `BitVec.ult` branch elimination). -/
theorem readLeb128_spec_comb {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {fail : Cont []}
    {cur pend prf_ptr : BitVec 64} {prfBytes : List UInt8} {idx : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {done : BitVec 64 → BitVec 64 → Expr Val Cont rs}
    (hfit : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hidx : idx ≤ prfBytes.length)
    (hcur : cur = prf_ptr + BitVec.ofNat 64 idx)
    (hpend : pend = prf_ptr + BitVec.ofNat 64 prfBytes.length)
    (hm : (Eq (prfBytes.At prf_ptr) ⋆ R) m)
    (hfail : readLeb128Pure (prfBytes.drop idx) = none → fail () m)
    (hdone : ∀ u bs',
      readLeb128Pure (prfBytes.drop idx) = some (u, bs') →
      u < 2 ^ 28 → bs'.length < (prfBytes.drop idx).length →
      bs' = prfBytes.drop (prfBytes.length - bs'.length) →
      idx < prfBytes.length - bs'.length →
      wp Γ Q X (done (BitVec.ofNat 64 u)
        (prf_ptr + BitVec.ofNat 64 (prfBytes.length - bs'.length))) m) :
    wp Γ Q X (readLeb128 fail cur pend done) m := by
  subst hcur hpend; unfold readLeb128
  refine wp_join_state (α := Nat × Nat)
    (fun (u, idx') => (BitVec.ofNat 64 u, prf_ptr + BitVec.ofNat 64 idx', ()))
    (fun (u, idx') m' => m' = m ∧ idx' ≤ prfBytes.length ∧
      readLeb128Pure (prfBytes.drop idx) = some (u, prfBytes.drop idx'))
    (fun _ (u, idx') m' ⟨hmEq, hidx', hres⟩ => by
      subst hmEq; dsimp only [Blocks.get_here]
      obtain ⟨hu, hlt, _, hgt, hdrop⟩ := readLeb128Pure_drop hidx hres
      grind)
    (fun Jdone hJdone => ?_)
  refine wp_while_state (α := LebState)
    (fun st =>
      (prf_ptr + BitVec.ofNat 64 st.idx, BitVec.ofNat 64 st.acc, BitVec.ofNat 64 st.sh, ()))
    (fun st => st.fuel)
    (fun st m' => 1 ≤ st.fuel ∧ st.sh + 7 * st.fuel = 28 ∧ st.acc < 2 ^ 28 ∧
      st.idx ≤ prfBytes.length ∧ m' = m ∧
      readLeb128Pure (prfBytes.drop idx) =
        readLeb128Aux st.fuel st.acc st.sh (prfBytes.drop st.idx))
    (fun _ hJleb => by
      wp_unfold
      exact hJleb ⟨4, idx, 0, 0⟩ m ⟨by simp, by simp, by simp, hidx, rfl, rfl⟩)
    (fun _ st m' ⟨hfuel1, hsh_eq, hacc, hi, hmEq, hpure⟩ ih => ?_)
  subst m'
  obtain ⟨fuel', hfuelEq⟩ : ∃ fuel', st.fuel = fuel' + 1 := ⟨st.fuel - 1, by omega⟩
  dsimp only [Blocks.get_here]; wp_unfold
  refine cursor_loadu8_branch hfit hi hm
    (fun _ hnil => hfail (by simpa [hfuelEq, hnil, readLeb128Aux] using hpure))
    (fun hilt hdrop => ?_)
  rw [setWidth64_ofNat8]
  rw [hdrop, hfuelEq] at hpure
  have hlo_lt : prfBytes[st.idx].toNat &&& 127 < 128 :=
    Nat.and_lt_two_pow prfBytes[st.idx].toNat (n := 7) (by decide)
  have hacc2_lt : (st.acc ||| ((prfBytes[st.idx].toNat &&& 127) <<< st.sh)) < 2 ^ 28 :=
    Nat.or_lt_two_pow hacc (lo7_shift_lt_test (by omega))
  have hhi_lt : prfBytes[st.idx].toNat &&& 128 < 2 ^ 64 :=
    Nat.lt_trans (Nat.and_lt_two_pow prfBytes[st.idx].toNat (n := 8) (by decide)) (by decide)
  have hlo_bv : BitVec.ofNat 64 prfBytes[st.idx].toNat &&& (127 : BitVec 64) =
      BitVec.ofNat 64 (prfBytes[st.idx].toNat &&& 127) := BitVec.eq_of_toNat_eq (by simp)
  have hhi_bv : BitVec.ofNat 64 prfBytes[st.idx].toNat &&& (128 : BitVec 64) =
      BitVec.ofNat 64 (prfBytes[st.idx].toNat &&& 128) := BitVec.eq_of_toNat_eq (by simp)
  have hsh_mod : (BitVec.ofNat 64 st.sh).toNat % 64 = st.sh := by
    simp [Nat.mod_eq_of_lt (by omega : st.sh < 2 ^ 64), Nat.mod_eq_of_lt (by omega : st.sh < 64)]
  have hacc2_bv :
      BitVec.ofNat 64 st.acc ||| BitVec.ofNat 64 ((prfBytes[st.idx].toNat &&& 127) <<< st.sh) =
      BitVec.ofNat 64 (st.acc ||| ((prfBytes[st.idx].toNat &&& 127) <<< st.sh)) :=
    BitVec.eq_of_toNat_eq (by simp)
  rw [hlo_bv, hsh_mod, bv_shl_ofNat (by omega) (by omega), hacc2_bv, hhi_bv, ptr_step_1]
  refine ⟨fun hmore => ?_, fun hnmore => ?_⟩
  · have hm_t : ((prfBytes[st.idx].toNat &&& 128) != 0) = true :=
      bne_iff_ne.mpr (fun hz => hmore (by simp [hz]))
    simp only [readLeb128Aux, hm_t, ↓reduceIte] at hpure
    rw [show (7 : BitVec 64) = BitVec.ofNat 64 7 from rfl,
      show (28 : BitVec 64) = BitVec.ofNat 64 28 from rfl, bv_add_ofNat st.sh 7]
    refine jnz_decide (st.sh + 7 < 28) ?_ ?_ ?_
    · simp [BitVec.ult, Nat.mod_eq_of_lt (by omega : st.sh + 7 < 2 ^ 64)]
    · intro hlt28
      simp only [hlt28, ↓reduceIte] at hpure
      exact ih ⟨fuel', st.idx + 1, _, st.sh + 7⟩ m (by dsimp; omega)
        ⟨by dsimp; omega, by dsimp; omega, hacc2_lt, hilt, rfl, hpure⟩
    · intro hnlt28
      simp only [hnlt28, ↓reduceIte] at hpure
      exact hfail hpure
  · have hhi0 : prfBytes[st.idx].toNat &&& 128 = 0 := by
      simpa [Nat.mod_eq_of_lt hhi_lt] using congrArg BitVec.toNat hnmore
    have hm_f : ((prfBytes[st.idx].toNat &&& 128) != 0) = false :=
      bne_eq_false_iff_eq.mpr hhi0
    simp only [readLeb128Aux, hm_f, Bool.false_eq_true, ↓reduceIte] at hpure
    exact hJdone (_, st.idx + 1) m ⟨rfl, hilt, hpure⟩

/-! ## 4. Single-line `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.jnz_decide
#print axioms LeanQbe.T.wp_jnz_decide
#print axioms LeanQbe.T.jnz_not_decide
#print axioms LeanQbe.T.wp_jnz_not_decide
#print axioms LeanQbe.T.jnz_iff
#print axioms LeanQbe.T.wp_jnz_iff
#print axioms LeanQbe.T.jnz_bool
#print axioms LeanQbe.T.wp_jnz_bool
#print axioms LeanQbe.T.jnz_true
#print axioms LeanQbe.T.wp_jnz_true
#print axioms LeanQbe.T.jnz_false
#print axioms LeanQbe.T.wp_jnz_false
#print axioms LeanQbe.T.wp_join_state
#print axioms LeanQbe.T.wp_join_state0
#print axioms LeanQbe.T.wp_join_state1
#print axioms LeanQbe.T.wp_join_state_pure
#print axioms LeanQbe.T.wp_join0
#print axioms LeanQbe.T.wp_while_state
#print axioms LeanQbe.T.wp_while_state0
#print axioms LeanQbe.T.wp_while_state1
#print axioms LeanQbe.T.wp_while_state_pure
#print axioms LeanQbe.T.wp_while_break_state
#print axioms LeanQbe.T.Emit.run_isLegal
#print axioms LeanQbe.T.Emit.run_wf
#print axioms LeanQbe.T.Emit.run_wp
#print axioms LeanQbe.T.Emit.bundle
#print axioms LeanQbe.T.Emit.bundlePure
#print axioms LeanQbe.T.boolCmpEmit_eq_emitBoolCmp
#print axioms LeanQbe.T.boolCmpEmit_bundle
#print axioms LeanQbe.T.boolSelectEmit_eq_emitBoolSelect
#print axioms LeanQbe.T.boolSelectEmit_bundle
#print axioms LeanQbe.T.maskToNEmit_eq_emitMaskToN
#print axioms LeanQbe.T.maskToNEmit_bundle
#print axioms LeanQbe.T.sextToWEmit_eq_emitSextToW
#print axioms LeanQbe.T.sextToWEmit_bundle
#print axioms LeanQbe.T.ternlogBoolEmit_eq_emitTernlogBool
#print axioms LeanQbe.T.ternlogBoolEmit_bundle
#print axioms test_emitBoolCmp_isLegal
#print axioms test_emitBoolCmp_wf
#print axioms test_emitBoolCmp_wp
#print axioms test_emitBoolSelect_all
#print axioms test_emitMaskToN_all
#print axioms test_emitSextToW_all
#print axioms test_emitTernlogBool_all
#print axioms boolIffXorEmit_bundle
#print axioms skipWs1Qbe_spec_comb
#print axioms readLeb128_spec_comb

end LeanQbeTest.T.CombLegalTest
