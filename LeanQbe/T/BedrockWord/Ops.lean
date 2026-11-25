module

public import LeanQbe.T.BedrockWord.Core
import LeanQbe.T.OpsLemmas
import LeanQbe.T.WfLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.FlatLemmas
import LeanQbe.T.Logic.MemLemmas

/-!
# Bit-Level, Reification, Evaluator, and Operational Lemmas (`BedrockWord.Ops`)

Proof module companion to `LeanQbe.T.BedrockWord.Core` (all `*Lemmas` imports stay private):

* 64-bit alignment and pointer untagging (`alignedAddr_iff_mod8`, `bv64_untag_aligned`,
  `bv64_shl3_eq_mul8`, `bv64_mul8_eq_ofNat`).
* Reification / `Wf` triad (`BlockFlat.denote_wf`, `BlockP.wf_of_denote`, `BlockP.wf_of_reify`,
  `BlockFlat.wp_iff_denote_wp`, `BlockFlat.denote_wp_iff`, `BlockP.wp_toFlat`).
* Evaluator bridge `OpCode.wp_imp_eval` and `BlockFlat.wp_imp_exec`.
* Operational determinism, `runFuel_sound` / `runFuel_complete`, and stuck lemmas.
* `CodeMap` lookup, sub-map, disjointness, and `Macro.WellLaidOut` lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.BedrockWord

open LeanQbe.T

/-! ## §1. Alignment and Bit-Level Helpers -/

theorem alignedAddr_iff_mod8 (a : BitVec 64) : AlignedAddr a ↔ a.toNat % 8 = 0 := by
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat] at ht
    have h7 : (7 : Nat) % 2 ^ 64 = 7 := by decide
    have h0 : (0 : Nat) % 2 ^ 64 = 0 := by decide
    rw [h7, h0, show (7 : Nat) = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod] at ht
    exact ht
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    have h7 : (7 : Nat) % 2 ^ 64 = 7 := by decide
    have h0 : (0 : Nat) % 2 ^ 64 = 0 := by decide
    rw [h7, h0, show (7 : Nat) = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
    exact h

theorem alignedAddr_add_mul8 {a : BitVec 64} (ha : AlignedAddr a) (k : Nat) :
    AlignedAddr (a + BitVec.ofNat 64 (8 * k)) := by
  rw [alignedAddr_iff_mod8] at ha ⊢
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hpow : (2 ^ 64 : Nat) = 8 * 2 ^ 61 := by decide
  omega

private theorem getLsbD_lt3_of_aligned {a : BitVec 64} (ha : AlignedAddr a) {i : Nat}
    (hi : i < 3) : a.getLsbD i = false := by
  have h := congrArg (fun x => x.getLsbD i) ha
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at h
  have h7 : (7#64).getLsbD i = true := by
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl <;> decide
  rw [h7, Bool.and_true] at h
  exact h

private theorem getLsbD_ge3_of_lt8 {tag : BitVec 64} (ht : tag.toNat < 8) {i : Nat}
    (hi : 3 ≤ i) : tag.getLsbD i = false := by
  rw [BitVec.getLsbD_eq_getElem?_getD]
  by_cases hlt : i < 64
  · rw [BitVec.getElem?_eq_some_iff.mpr ⟨hlt, rfl⟩]
    simp only [Option.getD_some, BitVec.getElem_eq_testBit_toNat, Nat.testBit,
      Nat.shiftRight_eq_div_pow]
    have hlt2 : tag.toNat < 2 ^ i :=
      Nat.lt_of_lt_of_le ht (Nat.pow_le_pow_right (n := 2) (by decide) hi)
    rw [Nat.div_eq_of_lt hlt2]
    rfl
  · simp [BitVec.getElem?_eq_none (Nat.le_of_not_lt hlt)]

private theorem getLsbD_seven (i : Nat) : (7#64).getLsbD i = decide (i < 3) := by
  by_cases h : i < 3
  · have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl <;> decide
  · simp only [h, decide_false]
    exact getLsbD_ge3_of_lt8 (by decide) (by omega)

/-- Clearing the low 3 tag bits of an aligned address OR'd with a 3-bit tag recovers `a`. -/
theorem bv64_untag_aligned {a tag : BitVec 64} (ha : AlignedAddr a) (ht : tag.toNat < 8) :
    (a ||| tag) &&& ~~~7#64 = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true,
    Bool.true_and, getLsbD_seven]
  by_cases h3 : i < 3
  · rw [getLsbD_lt3_of_aligned ha h3]; simp [h3]
  · rw [getLsbD_ge3_of_lt8 ht (by omega)]; simp [h3]

/-- Extracting the low 3 tag bits of an aligned address OR'd with a 3-bit tag recovers `tag`. -/
theorem bv64_extract_tag {a tag : BitVec 64} (ha : AlignedAddr a) (ht : tag.toNat < 8) :
    (a ||| tag) &&& 7#64 = tag := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, getLsbD_seven]
  by_cases h3 : i < 3
  · rw [getLsbD_lt3_of_aligned ha h3]; simp [h3]
  · rw [getLsbD_ge3_of_lt8 ht (by omega)]; simp [h3]

/-- OR'ing a nonzero 3-bit tag into an aligned address yields an unaligned address. -/
theorem bv64_tagged_unaligned {a tag : BitVec 64} (ha : AlignedAddr a)
    (ht0 : tag ≠ 0#64) (ht8 : tag.toNat < 8) : ¬ AlignedAddr (a ||| tag) := by
  intro hun
  have heq : (a ||| tag) &&& 7#64 = tag := bv64_extract_tag ha ht8
  rw [hun] at heq
  exact ht0 heq.symm

/-- Shifting a 64-bit index left by `3` equals multiplying by `8`. -/
theorem bv64_shl3_eq_mul8 (idx : BitVec 64) :
    idx <<< ((3#64 : BitVec 64).toNat % 64) = BitVec.ofNat 64 (8 * idx.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h3 : (3#64 : BitVec 64).toNat % 64 = 3 := by decide
  rw [h3, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  simp [Nat.shiftLeft_eq, Nat.mul_comm]

theorem bv64_mul8_eq_ofNat (idx : BitVec 64) :
    idx * 8#64 = BitVec.ofNat 64 (8 * idx.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_comm]

/-! ## §2. Reification, `Wf`, and `BlockB.wp` Lemmas -/

theorem SymEnv.Ext.refl (ρ : SymEnv) : SymEnv.Ext ρ ρ := fun _ _ h => h

theorem SymEnv.Ext.trans {ρ₁ ρ₂ ρ₃ : SymEnv}
    (h₁ : SymEnv.Ext ρ₁ ρ₂) (h₂ : SymEnv.Ext ρ₂ ρ₃) : SymEnv.Ext ρ₁ ρ₃ :=
  fun s a h => h₂ s a (h₁ s a h)

theorem RegsExprRel.weaken {V₁ V₂ : Ty → Type} {G G' : Ctx V₁ V₂}
    {e₁ : RegsExpr V₁} {e₂ : RegsExpr V₂} (hG : ∀ p ∈ G, p ∈ G')
    (h : RegsExprRel G e₁ e₂) : RegsExprRel G' e₁ e₂ :=
  ⟨h.sp.weaken hG, h.rp.weaken hG, h.rv.weaken hG,
   h.r1.weaken hG, h.r2.weaken hG, h.r3.weaken hG⟩

theorem BlockB.wp_mono {ρ₁ ρ₂ : SymEnv} {Ψ₁ Ψ₂ : CodeSpec} {H₁ H₂ : HaltPost}
    (hρ : SymEnv.Ext ρ₁ ρ₂)
    (hΨ : ∀ pc st, Ψ₁ pc st → Ψ₂ pc st)
    (hH : ∀ c m, H₁ c m → H₂ c m) :
    (b : BlockB Val) → ∀ m, b.wp ρ₁ Ψ₁ H₁ m → b.wp ρ₂ Ψ₂ H₂ m
  | .let_ _ k, m, h => Op.wp_mono (fun r hr => BlockB.wp_mono hρ hΨ hH (k r) m hr) h
  | .load _ _ k, m, ⟨v, hv, hk⟩ => ⟨v, hv, BlockB.wp_mono hρ hΨ hH (k v) m hk⟩
  | .store _ _ k, _, ⟨hok, hk⟩ => ⟨hok, BlockB.wp_mono hρ hΨ hH k _ hk⟩
  | .codeAddr s k, m, ⟨a, ha, hk⟩ => ⟨a, hρ s a ha, BlockB.wp_mono hρ hΨ hH (k a) m hk⟩
  | .jnz _ t e, m, ⟨ht, he⟩ =>
      ⟨fun hc => BlockB.wp_mono hρ hΨ hH t m (ht hc),
       fun hc => BlockB.wp_mono hρ hΨ hH e m (he hc)⟩
  | .ijmp _ _, _, h => hΨ _ _ h
  | .halt _, _, h => hH _ _ h
  | .hlt, _, h => h

theorem BlockB.Wf.weaken {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {b₁ : BlockB V₁} {b₂ : BlockB V₂}
    (h : BlockB.Wf G b₁ b₂) : ∀ {G'}, (∀ p ∈ G, p ∈ G') → BlockB.Wf G' b₁ b₂ := by
  induction h with
  | let_ hop _ ih =>
      intro _ hG; exact .let_ (hop.weaken hG) fun x₁ x₂ => ih x₁ x₂ (append_sub_left _ hG)
  | load t ha _ ih =>
      intro _ hG; exact .load t (ha.weaken hG) fun v₁ v₂ => ih v₁ v₂ (cons_sub hG)
  | store hv ha _ ih => intro _ hG; exact .store (hv.weaken hG) (ha.weaken hG) (ih hG)
  | codeAddr s _ ih =>
      intro _ hG; exact .codeAddr s fun a₁ a₂ => ih a₁ a₂ (cons_sub hG)
  | jnz hc _ _ iht ihe => intro _ hG; exact .jnz (hc.weaken hG) (iht hG) (ihe hG)
  | ijmp ht hn => intro _ hG; exact .ijmp (ht.weaken hG) (hn.weaken hG)
  | halt hc => intro _ hG; exact .halt (hc.weaken hG)
  | hlt => intro _ _; exact .hlt

private theorem denoteArg_idxArg_rel_local {V : Ty → Type}
    (G : Ctx K V) (vs : List ((t : Ty) × V t))
    (hvs : ∀ p ∈ G, p.2.1 < vs.length ∧ lookupV vs p.1 (vs.length - 1 - p.2.1) = some p.2.2)
    {t : Ty} {a₁ : Arg K t} {a₂ : Arg V t} (ha : ArgRel G t a₁ a₂) :
    denoteArg vs (idxArg vs.length a₁) = some a₂ := by
  cases ha with
  | @var lvl v hm =>
    obtain ⟨hlt, hl⟩ := hvs _ hm
    dsimp only [idxArg]; simp only [hlt, ↓reduceIte]; dsimp only [denoteArg]; rw [hl]
  | imm c => rfl

private theorem denoteArgs_idxArgs_local {V : Ty → Type}
    (G : Ctx K V) (vs : List ((t : Ty) × V t))
    (hvs : ∀ p ∈ G, p.2.1 < vs.length ∧ lookupV vs p.1 (vs.length - 1 - p.2.1) = some p.2.2) :
    {ts : List Ty} → {as₁ : Tup (Arg K) ts} → {as₂ : Tup (Arg V) ts} →
    TRel (ArgRel G) as₁ as₂ →
    denoteArgs vs (idxArgs vs.length as₁) = some as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons h hs => by
    dsimp only [idxArgs, denoteArgs]
    rw [denoteArg_idxArg_rel_local G vs hvs h, denoteArgs_idxArgs_local G vs hvs hs]

private theorem denoteRegsExpr_idxArgs_local {V : Ty → Type}
    (G : Ctx K V) (vs : List ((t : Ty) × V t))
    (hvs : ∀ p ∈ G, p.2.1 < vs.length ∧ lookupV vs p.1 (vs.length - 1 - p.2.1) = some p.2.2)
    {e₁ : RegsExpr K} {e₂ : RegsExpr V} (hr : RegsExprRel G e₁ e₂) :
    denoteRegsExpr vs (e₁.idxArgs vs.length) = some e₂ := by
  dsimp only [RegsExpr.idxArgs, denoteRegsExpr]
  rw [denoteArg_idxArg_rel_local G vs hvs hr.sp, denoteArg_idxArg_rel_local G vs hvs hr.rp,
      denoteArg_idxArg_rel_local G vs hvs hr.rv, denoteArg_idxArg_rel_local G vs hvs hr.r1,
      denoteArg_idxArg_rel_local G vs hvs hr.r2, denoteArg_idxArg_rel_local G vs hvs hr.r3]

private theorem lookupV_head_local {V : Ty → Type} (t : Ty) (v : V t)
    (vs : List ((t' : Ty) × V t')) : lookupV (⟨t, v⟩ :: vs) t 0 = some v := by
  dsimp only [lookupV, listGet?, castTy]
  induction t with
  | bool => rfl
  | bits n => simp
  | float f => simp
  | pair a b _ _ =>
    dsimp only
    cases ha : tyDecEq a a with
    | isFalse h => exact absurd rfl h
    | isTrue _ =>
      cases hb : tyDecEq b b with
      | isFalse h => exact absurd rfl h
      | isTrue _ => rfl

private theorem ctxMatch_cons_local {V : Ty → Type} {G : Ctx K V} {vs : List ((t : Ty) × V t)}
    (hvs : ∀ p ∈ G, p.2.1 < vs.length ∧ lookupV vs p.1 (vs.length - 1 - p.2.1) = some p.2.2)
    (t : Ty) (v : V t) :
    ∀ p ∈ (⟨t, vs.length, v⟩ :: G),
      p.2.1 < (⟨t, v⟩ :: vs).length ∧
      lookupV (⟨t, v⟩ :: vs) p.1 ((⟨t, v⟩ :: vs).length - 1 - p.2.1) = some p.2.2 := by
  rintro ⟨pt, pidx, pv⟩ hp
  rcases List.mem_cons.1 hp with h1 | hp
  · cases h1
    refine ⟨Nat.lt_succ_self _, ?_⟩
    simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_self]
    exact lookupV_head_local t v vs
  · obtain ⟨hlt, hl⟩ := hvs ⟨pt, pidx, pv⟩ hp
    have hlt' : pidx < vs.length := hlt
    refine ⟨Nat.lt_succ_of_lt hlt', ?_⟩
    have hidx : (⟨t, v⟩ :: vs).length - 1 - pidx = (vs.length - 1 - pidx) + 1 := by
      have aux : ∀ m n : Nat, n < m → (m + 1) - 1 - n = (m - 1 - n) + 1 := fun m n hn => by omega
      exact aux vs.length pidx hlt'
    rw [hidx]; exact hl

private theorem ctxMatch_pushTup_local {V : Ty → Type} :
    {as : List Ty} → (xs : Tup V as) → {G : Ctx K V} → {vs : List ((t : Ty) × V t)} →
    (∀ p ∈ G, p.2.1 < vs.length ∧ lookupV vs p.1 (vs.length - 1 - p.2.1) = some p.2.2) →
    ∀ p ∈ (Tup.zip (Tup.levels as vs.length) xs ++ G),
      p.2.1 < (pushTup xs vs).length ∧
      lookupV (pushTup xs vs) p.1 ((pushTup xs vs).length - 1 - p.2.1) = some p.2.2
  | [], (), _, _, hvs, p, hp => by simpa [Tup.zip, pushTup] using hvs p hp
  | a :: as, (x, xs), G, vs, hvs, p, hp => by
    have h1 := ctxMatch_cons_local hvs a x
    have h2 := ctxMatch_pushTup_local xs h1
    simp only [List.length_cons] at h2
    refine h2 p ?_
    dsimp only [Tup.levels, Tup.zip] at hp ⊢
    simp only [List.cons_append, List.mem_append, List.mem_cons] at hp ⊢
    rcases hp with rfl | hp | hp
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl hp
    · exact Or.inr (Or.inr hp)

private theorem denoteRegsExpr_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {vs₁ : List ((t : Ty) × V₁ t)} {vs₂ : List ((t : Ty) × V₂ t)}
    (hvs : CtxRel G vs₁ vs₂) (e : RegsExpr K) :
    ORel (RegsExprRel G) (denoteRegsExpr vs₁ e) (denoteRegsExpr vs₂ e) := by
  have hsp := denoteArg_rel hvs e.sp
  have hrp := denoteArg_rel hvs e.rp
  have hrv := denoteArg_rel hvs e.rv
  have hr1 := denoteArg_rel hvs e.r1
  have hr2 := denoteArg_rel hvs e.r2
  have hr3 := denoteArg_rel hvs e.r3
  dsimp only [denoteRegsExpr]
  cases e1 : denoteArg vs₁ e.sp <;> cases e2 : denoteArg vs₂ e.sp <;>
    rw [e1, e2] at hsp <;> dsimp only [ORel] at hsp ⊢ <;>
  cases f1 : denoteArg vs₁ e.rp <;> cases f2 : denoteArg vs₂ e.rp <;>
    rw [f1, f2] at hrp <;> dsimp only [ORel] at hrp ⊢ <;>
  cases g1 : denoteArg vs₁ e.rv <;> cases g2 : denoteArg vs₂ e.rv <;>
    rw [g1, g2] at hrv <;> dsimp only [ORel] at hrv ⊢ <;>
  cases i1 : denoteArg vs₁ e.r1 <;> cases i2 : denoteArg vs₂ e.r1 <;>
    rw [i1, i2] at hr1 <;> dsimp only [ORel] at hr1 ⊢ <;>
  cases j1 : denoteArg vs₁ e.r2 <;> cases j2 : denoteArg vs₂ e.r2 <;>
    rw [j1, j2] at hr2 <;> dsimp only [ORel] at hr2 ⊢ <;>
  cases k1 : denoteArg vs₁ e.r3 <;> cases k2 : denoteArg vs₂ e.r3 <;>
    rw [k1, k2] at hr3 <;> dsimp only [ORel] at hr3 ⊢ <;>
  first | trivial | exact ⟨hsp, hrp, hrv, hr1, hr2, hr3⟩

private theorem BlockFlat.denote_wf {V₁ V₂ : Ty → Type} :
    (bf : BlockFlat) → {G : Ctx V₁ V₂} →
    {vs₁ : List ((t : Ty) × V₁ t)} → {vs₂ : List ((t : Ty) × V₂ t)} →
    CtxRel G vs₁ vs₂ → BlockB.Wf G (bf.denote V₁ vs₁) (bf.denote V₂ vs₂)
  | .let_ op k, _, vs₁, vs₂, hvs => by
      have hr := denoteArgs_rel hvs op.args
      dsimp only [BlockFlat.denote]
      cases e₁ : denoteArgs vs₁ op.args <;> cases e₂ : denoteArgs vs₂ op.args <;>
        rw [e₁, e₂] at hr <;> dsimp only [ORel] at hr ⊢
      · exact .hlt
      · exact .let_ (.mk op.code hr) fun xs₁ xs₂ =>
          BlockFlat.denote_wf k (ctxRel_pushTup xs₁ xs₂ hvs)
  | .load t a k, _, vs₁, vs₂, hvs => by
      have hr := denoteArg_rel hvs a
      dsimp only [BlockFlat.denote]
      cases e₁ : denoteArg vs₁ a <;> cases e₂ : denoteArg vs₂ a <;>
        rw [e₁, e₂] at hr <;> dsimp only [ORel] at hr ⊢
      · exact .hlt
      · exact .load t hr fun v₁ v₂ =>
          BlockFlat.denote_wf k
            (.cons List.mem_cons_self (hvs.mono fun _ hp => List.mem_cons_of_mem _ hp))
  | .store v a k, _, vs₁, vs₂, hvs => by
      have hv := denoteArg_rel hvs v
      have ha := denoteArg_rel hvs a
      dsimp only [BlockFlat.denote]
      cases e₁ : denoteArg vs₁ v <;> cases e₂ : denoteArg vs₂ v <;> rw [e₁, e₂] at hv <;>
        dsimp only [ORel] at hv ⊢ <;>
        cases f₁ : denoteArg vs₁ a <;> cases f₂ : denoteArg vs₂ a <;> rw [f₁, f₂] at ha <;>
        dsimp only [ORel] at ha ⊢ <;>
        first | exact .hlt | exact .store hv ha (BlockFlat.denote_wf k hvs)
  | .codeAddr sym k, _, _, _, hvs =>
      .codeAddr sym fun a₁ a₂ =>
        BlockFlat.denote_wf k
          (.cons List.mem_cons_self (hvs.mono fun _ hp => List.mem_cons_of_mem _ hp))
  | .jnz c t e, _, vs₁, vs₂, hvs => by
      have hr := denoteArg_rel hvs c
      dsimp only [BlockFlat.denote]
      cases e₁ : denoteArg vs₁ c <;> cases e₂ : denoteArg vs₂ c <;>
        rw [e₁, e₂] at hr <;> dsimp only [ORel] at hr ⊢
      · exact .hlt
      · exact .jnz hr (BlockFlat.denote_wf t hvs) (BlockFlat.denote_wf e hvs)
  | .ijmp tgt nxt, _, vs₁, vs₂, hvs => by
      have ht := denoteArg_rel hvs tgt
      have hn := denoteRegsExpr_rel hvs nxt
      dsimp only [BlockFlat.denote]
      cases e₁ : denoteArg vs₁ tgt <;> cases e₂ : denoteArg vs₂ tgt <;> rw [e₁, e₂] at ht <;>
        dsimp only [ORel] at ht ⊢ <;>
        cases f₁ : denoteRegsExpr vs₁ nxt <;> cases f₂ : denoteRegsExpr vs₂ nxt <;>
        rw [f₁, f₂] at hn <;> dsimp only [ORel] at hn ⊢ <;>
        first | exact .hlt | exact .ijmp ht hn
  | .halt c, _, vs₁, vs₂, hvs => by
      have hc := denoteArg_rel hvs c
      dsimp only [BlockFlat.denote]
      cases e₁ : denoteArg vs₁ c <;> cases e₂ : denoteArg vs₂ c <;>
        rw [e₁, e₂] at hc <;> dsimp only [ORel] at hc ⊢
      · exact .hlt
      · exact .halt hc
  | .hlt, _, _, _, _ => .hlt

theorem BlockP.wf_of_denote {b : BlockP} (bf : BlockFlat)
    (h : b = fun V r => bf.denote V (pushRegsV r)) : b.Wf := by
  intro V₁ V₂ r₁ r₂
  have h₁ : b V₁ r₁ = bf.denote V₁ (pushRegsV r₁) := congrFun (congrFun h V₁) r₁
  have h₂ : b V₂ r₂ = bf.denote V₂ (pushRegsV r₂) := congrFun (congrFun h V₂) r₂
  rw [h₁, h₂]
  exact BlockFlat.denote_wf bf
    ((ctxRel_pushTup r₁.toTup r₂.toTup (.nil (G := []))).mono fun _ hp => by simpa using hp)

theorem BlockP.wf_of_reify {b : BlockP}
    (h : b = fun V r => (reifyBlock b).denote V (pushRegsV r)) : b.Wf :=
  BlockP.wf_of_denote (reifyBlock b) h

theorem BlockFlat.wp_iff_denote_wp {ρ : SymEnv} {Ψ : CodeSpec} {H : HaltPost} :
    (bf : BlockFlat) → ∀ vs m,
    bf.wp ρ Ψ H vs m ↔ BlockB.wp ρ Ψ H (bf.denote Val vs) m
  | .let_ op k, vs, m => by
      dsimp only [BlockFlat.wp, BlockFlat.denote]
      cases denoteArgs vs op.args with
      | none => rfl
      | some args' =>
          dsimp only [BlockB.wp]
          exact ⟨Op.wp_mono fun r hr => (BlockFlat.wp_iff_denote_wp k (pushTup r vs) m).1 hr,
                 Op.wp_mono fun r hr => (BlockFlat.wp_iff_denote_wp k (pushTup r vs) m).2 hr⟩
  | .load ty a k, vs, m => by
      dsimp only [BlockFlat.wp, BlockFlat.denote]
      cases denoteArg vs a with
      | none => rfl
      | some a' =>
          dsimp only [BlockB.wp]
          exact exists_congr fun v =>
            and_congr_right fun _ => BlockFlat.wp_iff_denote_wp k (⟨ty, v⟩ :: vs) m
  | .store v a k, vs, m => by
      dsimp only [BlockFlat.wp, BlockFlat.denote]
      cases denoteArg vs v <;> cases denoteArg vs a <;> dsimp only [BlockB.wp]
      · rfl
      · rfl
      · rfl
      · exact and_congr_right fun _ => BlockFlat.wp_iff_denote_wp k vs _
  | .codeAddr _ k, vs, m => by
      dsimp only [BlockFlat.wp, BlockFlat.denote, BlockB.wp]
      exact exists_congr fun a =>
        and_congr_right fun _ => BlockFlat.wp_iff_denote_wp k (⟨i64, a⟩ :: vs) m
  | .jnz c t e, vs, m => by
      dsimp only [BlockFlat.wp, BlockFlat.denote]
      cases denoteArg vs c with
      | none => rfl
      | some c' =>
          dsimp only [BlockB.wp]
          exact and_congr
            (imp_congr_right fun _ => BlockFlat.wp_iff_denote_wp t vs m)
            (imp_congr_right fun _ => BlockFlat.wp_iff_denote_wp e vs m)
  | .ijmp tgt nxt, vs, m => by
      dsimp only [BlockFlat.wp, BlockFlat.denote]
      cases denoteArg vs tgt <;> cases denoteRegsExpr vs nxt <;> rfl
  | .halt c, vs, m => by
      dsimp only [BlockFlat.wp, BlockFlat.denote]
      cases denoteArg vs c <;> rfl
  | .hlt, _, _ => Iff.rfl

private theorem BlockFlat.denote_wp_iff {ρ : SymEnv} {Ψ : CodeSpec} {H : HaltPost}
    {G : Ctx K Val} {b₁ : BlockB K} {b₂ : BlockB Val} (hwf : BlockB.Wf G b₁ b₂) :
    ∀ (vs : List ((t : Ty) × Val t)),
    (∀ p ∈ G, p.2.1 < vs.length ∧ lookupV vs p.1 (vs.length - 1 - p.2.1) = some p.2.2) →
    ∀ m, BlockB.wp ρ Ψ H ((toFlat b₁ vs.length).denote Val vs) m ↔ BlockB.wp ρ Ψ H b₂ m := by
  induction hwf with
  | let_ hop _ ih =>
      intro vs hvs m
      cases hop with | mk code hargs =>
      have hda := denoteArgs_idxArgs_local _ vs hvs hargs
      dsimp only [toFlat, BlockFlat.denote]; rw [hda]; dsimp only [BlockB.wp]
      refine ⟨Op.wp_mono fun r hr => ?_, Op.wp_mono fun r hr => ?_⟩
      · have hk := (ih (Tup.levels _ vs.length) r (pushTup r vs)
          (ctxMatch_pushTup_local r hvs) m).1
        rw [pushTup_length r vs] at hk; exact hk hr
      · have hk := (ih (Tup.levels _ vs.length) r (pushTup r vs)
          (ctxMatch_pushTup_local r hvs) m).2
        rw [pushTup_length r vs] at hk; exact hk hr
  | load ty ha _ ih =>
      intro vs hvs m
      have hda := denoteArg_idxArg_rel_local _ vs hvs ha
      dsimp only [toFlat, BlockFlat.denote]; rw [hda]; dsimp only [BlockB.wp]
      exact exists_congr fun v => and_congr_right fun _ =>
        ih vs.length v (⟨ty, v⟩ :: vs) (ctxMatch_cons_local hvs ty v) m
  | store hv ha _ ih =>
      intro vs hvs _
      have hdv := denoteArg_idxArg_rel_local _ vs hvs hv
      have hda := denoteArg_idxArg_rel_local _ vs hvs ha
      dsimp only [toFlat, BlockFlat.denote]; rw [hdv, hda]; dsimp only [BlockB.wp]
      exact and_congr_right fun _ => ih vs hvs _
  | codeAddr _ _ ih =>
      intro vs hvs m
      dsimp only [toFlat, BlockFlat.denote, BlockB.wp]
      exact exists_congr fun a => and_congr_right fun _ =>
        ih vs.length a (⟨i64, a⟩ :: vs) (ctxMatch_cons_local hvs i64 a) m
  | jnz hc _ _ iht ihe =>
      intro vs hvs m
      have hdc := denoteArg_idxArg_rel_local _ vs hvs hc
      dsimp only [toFlat, BlockFlat.denote]; rw [hdc]; dsimp only [BlockB.wp]
      exact and_congr
        (imp_congr_right fun _ => iht vs hvs m)
        (imp_congr_right fun _ => ihe vs hvs m)
  | ijmp ht hn =>
      intro vs hvs m
      have hdt := denoteArg_idxArg_rel_local _ vs hvs ht
      have hdn := denoteRegsExpr_idxArgs_local _ vs hvs hn
      dsimp only [toFlat, BlockFlat.denote]; rw [hdt, hdn]
  | halt hc =>
      intro vs hvs m
      have hdc := denoteArg_idxArg_rel_local _ vs hvs hc
      dsimp only [toFlat, BlockFlat.denote]; rw [hdc]
  | hlt => intro _ _ _; rfl

theorem BlockP.wp_toFlat {ρ : SymEnv} {Ψ : CodeSpec} {H : HaltPost}
    {b : BlockP} (hwf : b.Wf) (st : State) :
    (reifyBlock b).wp ρ Ψ H (pushRegsV st.regs.toRegsV) st.mem ↔ b.wp ρ Ψ H st := by
  rw [BlockFlat.wp_iff_denote_wp]
  have hrel := hwf K Val RegsV.levels0 st.regs.toRegsV
  have hvs := ctxMatch_pushTup_local (G := ([] : Ctx K Val)) (vs := [])
    st.regs.toRegsV.toTup (fun _ hp => nomatch hp)
  have hvs' : ∀ p ∈ Tup.zip RegsV.levels0.toTup st.regs.toRegsV.toTup,
      p.2.1 < (pushRegsV st.regs.toRegsV).length ∧
      lookupV (pushRegsV st.regs.toRegsV) p.1
        ((pushRegsV st.regs.toRegsV).length - 1 - p.2.1) = some p.2.2 := by
    simpa [List.append_nil, RegsV.levels0, RegsV.toTup, Tup.levels, pushRegsV] using hvs
  have hd := BlockFlat.denote_wp_iff (ρ := ρ) (Ψ := Ψ) (H := H) hrel
    (pushRegsV st.regs.toRegsV) hvs' st.mem
  simpa [reifyBlock, BlockP.wp, pushRegsV, pushTup_length] using hd

/-! ## §3. `CodeMap` Lemmas -/

theorem CodeMap.wf_of_checkWf {cm : CodeMap} (h : cm.checkWf = true) : cm.Wf := by
  simp only [CodeMap.checkWf, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact ⟨fun e he => h.1.1.1 e he,
         listNodup_nodup h.1.1.2,
         listNodup_nodup h.1.2,
         fun e he => h.2 e he⟩

theorem CodeMap.disjoint_of_checkDisjoint {cm₁ cm₂ : CodeMap}
    (h : cm₁.checkDisjoint cm₂ = true) : cm₁.Disjoint cm₂ := by
  simp only [CodeMap.checkDisjoint, List.all_eq_true, Bool.and_eq_true, bne_iff_ne] at h
  exact ⟨fun e₁ h₁ e₂ h₂ => (h e₁ h₁ e₂ h₂).1, fun e₁ h₁ e₂ h₂ => (h e₁ h₁ e₂ h₂).2⟩

theorem CodeMap.Sub.refl (cm : CodeMap) : cm.Sub cm := fun _ _ h => h

theorem CodeMap.Sub.trans {cm₁ cm₂ cm₃ : CodeMap}
    (h₁ : cm₁.Sub cm₂) (h₂ : cm₂.Sub cm₃) : cm₁.Sub cm₃ :=
  fun pc b h => h₂ pc b (h₁ pc b h)

theorem CodeMap.lookupAddr_mem : {cm : CodeMap} → {pc : BitVec 64} → {b : BlockFlat} →
    cm.lookupAddr pc = some b → ∃ e ∈ cm, e.addr = pc ∧ e.block = b
  | [], _, _, h => by simp [CodeMap.lookupAddr] at h
  | e :: es, pc, b, h => by
      dsimp only [CodeMap.lookupAddr] at h
      split at h
      · rename_i heq
        simp only [beq_iff_eq] at heq
        cases h
        exact ⟨e, List.mem_cons_self, heq, rfl⟩
      · obtain ⟨e', hm, ha, hb⟩ := CodeMap.lookupAddr_mem h
        exact ⟨e', List.mem_cons_of_mem _ hm, ha, hb⟩

theorem CodeMap.lookupAddr_none_of_not_mem : {cm : CodeMap} → {pc : BitVec 64} →
    (∀ e ∈ cm, e.addr ≠ pc) → cm.lookupAddr pc = none
  | [], _, _ => rfl
  | e :: es, pc, h => by
      have hne : (e.addr == pc) = false := beq_false_of_ne (h e List.mem_cons_self)
      dsimp only [CodeMap.lookupAddr]
      rw [hne]
      exact CodeMap.lookupAddr_none_of_not_mem (fun e' he' => h e' (List.mem_cons_of_mem _ he'))

theorem CodeMap.lookupAddr_append : {cm₁ cm₂ : CodeMap} → (pc : BitVec 64) →
    (cm₁ ++ cm₂).lookupAddr pc =
      match cm₁.lookupAddr pc with
      | some b => some b
      | none => cm₂.lookupAddr pc
  | [], _, _ => rfl
  | e :: es, cm₂, pc => by
      dsimp only [List.cons_append, CodeMap.lookupAddr]
      cases e.addr == pc
      · exact CodeMap.lookupAddr_append pc
      · rfl

theorem CodeMap.addrOf?_mem : {cm : CodeMap} → {s : Sym} → {a : BitVec 64} →
    cm.addrOf? s = some a → ∃ e ∈ cm, e.name = s ∧ e.addr = a
  | [], _, _, h => by simp [CodeMap.addrOf?] at h
  | e :: es, s, a, h => by
      dsimp only [CodeMap.addrOf?] at h
      split at h
      · rename_i heq
        simp only [beq_iff_eq] at heq
        cases h
        exact ⟨e, List.mem_cons_self, heq, rfl⟩
      · obtain ⟨e', hm, hn, ha⟩ := CodeMap.addrOf?_mem h
        exact ⟨e', List.mem_cons_of_mem _ hm, hn, ha⟩

theorem CodeMap.addrOf?_none_of_not_mem : {cm : CodeMap} → {s : Sym} →
    (∀ e ∈ cm, e.name ≠ s) → cm.addrOf? s = none
  | [], _, _ => rfl
  | e :: es, s, h => by
      have hne : (e.name == s) = false := beq_false_of_ne (h e List.mem_cons_self)
      dsimp only [CodeMap.addrOf?]
      rw [hne]
      exact CodeMap.addrOf?_none_of_not_mem (fun e' he' => h e' (List.mem_cons_of_mem _ he'))

theorem CodeMap.addrOf?_append : {cm₁ cm₂ : CodeMap} → (s : Sym) →
    (cm₁ ++ cm₂).addrOf? s =
      match cm₁.addrOf? s with
      | some a => some a
      | none => cm₂.addrOf? s
  | [], _, _ => rfl
  | e :: es, cm₂, s => by
      dsimp only [List.cons_append, CodeMap.addrOf?]
      cases e.name == s
      · exact CodeMap.addrOf?_append s
      · rfl

theorem CodeMap.sub_append_left (cm₁ cm₂ : CodeMap) : cm₁.Sub (cm₁ ++ cm₂) := by
  intro pc b h
  rw [CodeMap.lookupAddr_append, h]

theorem CodeMap.sub_append_right {cm₁ cm₂ : CodeMap} (hd : cm₁.AddrDisjoint cm₂) :
    cm₂.Sub (cm₁ ++ cm₂) := by
  intro pc b h
  obtain ⟨e₂, he₂, rfl, -⟩ := CodeMap.lookupAddr_mem h
  rw [CodeMap.lookupAddr_append,
      CodeMap.lookupAddr_none_of_not_mem (fun e₁ he₁ => hd e₁ he₁ e₂ he₂)]
  exact h

theorem CodeMap.symEnv_ext_append_left (cm₁ cm₂ : CodeMap) :
    SymEnv.Ext cm₁.symEnv (cm₁ ++ cm₂).symEnv := by
  intro s a h
  dsimp only [CodeMap.symEnv] at h ⊢
  rw [CodeMap.addrOf?_append, h]

theorem CodeMap.symEnv_ext_append_right {cm₁ cm₂ : CodeMap} (hd : cm₁.NameDisjoint cm₂) :
    SymEnv.Ext cm₂.symEnv (cm₁ ++ cm₂).symEnv := by
  intro s a h
  dsimp only [CodeMap.symEnv] at h ⊢
  obtain ⟨e₂, he₂, rfl, -⟩ := CodeMap.addrOf?_mem h
  rw [CodeMap.addrOf?_append,
      CodeMap.addrOf?_none_of_not_mem (fun e₁ he₁ => hd e₁ he₁ e₂ he₂)]
  exact h

theorem CodeMap.lookupAddr_none_of_unaligned {cm : CodeMap} (hal : cm.Aligned)
    {pc : BitVec 64} (hun : ¬ AlignedAddr pc) : cm.lookupAddr pc = none :=
  CodeMap.lookupAddr_none_of_not_mem fun e he hEq => hun (hEq ▸ hal e he)

/-! ## §4. Evaluator Bridge and Operational Lemmas -/

private theorem floatResultWp_eval (f : Fmt) (res : Float.Model.UnpackedFloat)
    {k : BitVec f.width → Prop} (h : floatResultWp f res k) :
    k (evalFloatResult f res) := by
  unfold floatResultWp at h
  unfold evalFloatResult
  split at h
  · rename_i hnan; rw [ite_eq_left hnan]; exact h (packedNaNBv f) (isFloatNaN_packedNaN f)
  · rename_i hnan; rw [ite_eq_right hnan]; exact h

private theorem liftFloatRel1_eval
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (a : Val t) (k : Val t → Prop),
    liftFloatRel1 op t a k → ∃ r, evalFloat1 op t a = some r ∧ k r
  | .float f, a, _, h => ⟨_, rfl, floatResultWp_eval f _ h⟩
  | .pair s u, a, _, h => by
      obtain ⟨r1, h1, hk1⟩ := liftFloatRel1_eval op s a.1 _ h
      obtain ⟨r2, h2, hk2⟩ := liftFloatRel1_eval op u a.2 _ hk1
      exact ⟨(r1, r2), by simp [evalFloat1, h1, h2], hk2⟩
  | .bool, _, _, h => False.elim h
  | .bits _, _, _, h => False.elim h

private theorem liftFloatRel2_eval
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (a b : Val t) (k : Val t → Prop),
    liftFloatRel2 op t a b k → ∃ r, evalFloat2 op t a b = some r ∧ k r
  | .float f, a, b, _, h => ⟨_, rfl, floatResultWp_eval f _ h⟩
  | .pair s u, a, b, _, h => by
      obtain ⟨r1, h1, hk1⟩ := liftFloatRel2_eval op s a.1 b.1 _ h
      obtain ⟨r2, h2, hk2⟩ := liftFloatRel2_eval op u a.2 b.2 _ hk1
      exact ⟨(r1, r2), by simp [evalFloat2, h1, h2], hk2⟩
  | .bool, _, _, _, h => False.elim h
  | .bits _, _, _, _, h => False.elim h

private theorem liftFloatRel3_eval
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (a b c : Val t) (k : Val t → Prop),
    liftFloatRel3 op t a b c k → ∃ r, evalFloat3 op t a b c = some r ∧ k r
  | .float f, a, b, c, _, h => ⟨_, rfl, floatResultWp_eval f _ h⟩
  | .pair s u, a, b, c, _, h => by
      obtain ⟨r1, h1, hk1⟩ := liftFloatRel3_eval op s a.1 b.1 c.1 _ h
      obtain ⟨r2, h2, hk2⟩ := liftFloatRel3_eval op u a.2 b.2 c.2 _ hk1
      exact ⟨(r1, r2), by simp [evalFloat3, h1, h2], hk2⟩
  | .bool, _, _, _, _, h => False.elim h
  | .bits _, _, _, _, _, h => False.elim h

private theorem convertFloat_eval (src dst : Fmt) (b : BitVec src.width)
    {k : BitVec dst.width → Prop} (h : convertFloat src dst b k) :
    k (evalConvertFloat src dst b) := by
  unfold convertFloat at h
  unfold evalConvertFloat
  cases hu : unpackFloat src b with
  | notANumber => rw [hu] at h; exact h (packedNaNBv dst) (isFloatNaN_packedNaN dst)
  | finite _ _ _ _ => rw [hu] at h; exact h
  | zero _ => rw [hu] at h; exact h
  | infinity _ => rw [hu] at h; exact h

/-- Bridge from relational `OpCode.wp` to deterministic `evalOpCode`. -/
theorem OpCode.wp_imp_eval {as rs : List Ty} (c : OpCode as rs) (args : Tup Val as)
    {post : Tup Val rs → Prop} (h : c.wp args post) :
    ∃ r, evalOpCode c args = some r ∧ post r := by
  cases c with
  | fadd t =>
      obtain ⟨a, b, ⟨⟩⟩ := args
      dsimp only [OpCode.wp, evalOpCode] at h ⊢
      by_cases hf : (!t.isFloatTree) = true
      · rw [ite_eq_left hf] at h; exact False.elim h
      · rw [ite_eq_right hf] at h ⊢
        obtain ⟨r, hr, hp⟩ := liftFloatRel2_eval _ t a b _ h
        exact ⟨(r, ()), by simp [hr], hp⟩
  | fsub t =>
      obtain ⟨a, b, ⟨⟩⟩ := args
      dsimp only [OpCode.wp, evalOpCode] at h ⊢
      by_cases hf : (!t.isFloatTree) = true
      · rw [ite_eq_left hf] at h; exact False.elim h
      · rw [ite_eq_right hf] at h ⊢
        obtain ⟨r, hr, hp⟩ := liftFloatRel2_eval _ t a b _ h
        exact ⟨(r, ()), by simp [hr], hp⟩
  | fmul t =>
      obtain ⟨a, b, ⟨⟩⟩ := args
      dsimp only [OpCode.wp, evalOpCode] at h ⊢
      by_cases hf : (!t.isFloatTree) = true
      · rw [ite_eq_left hf] at h; exact False.elim h
      · rw [ite_eq_right hf] at h ⊢
        obtain ⟨r, hr, hp⟩ := liftFloatRel2_eval _ t a b _ h
        exact ⟨(r, ()), by simp [hr], hp⟩
  | fdiv t =>
      obtain ⟨a, b, ⟨⟩⟩ := args
      dsimp only [OpCode.wp, evalOpCode] at h ⊢
      by_cases hf : (!t.isFloatTree) = true
      · rw [ite_eq_left hf] at h; exact False.elim h
      · rw [ite_eq_right hf] at h ⊢
        obtain ⟨r, hr, hp⟩ := liftFloatRel2_eval _ t a b _ h
        exact ⟨(r, ()), by simp [hr], hp⟩
  | ffma t =>
      obtain ⟨a, b, c, ⟨⟩⟩ := args
      dsimp only [OpCode.wp, evalOpCode] at h ⊢
      by_cases hf : (!t.isFloatTree) = true
      · rw [ite_eq_left hf] at h; exact False.elim h
      · rw [ite_eq_right hf] at h ⊢
        obtain ⟨r, hr, hp⟩ := liftFloatRel3_eval _ t a b c _ h
        exact ⟨(r, ()), by simp [hr], hp⟩
  | fsqrt t =>
      obtain ⟨a, ⟨⟩⟩ := args
      dsimp only [OpCode.wp, evalOpCode] at h ⊢
      by_cases hf : (!t.isFloatTree) = true
      · rw [ite_eq_left hf] at h; exact False.elim h
      · rw [ite_eq_right hf] at h ⊢
        obtain ⟨r, hr, hp⟩ := liftFloatRel1_eval _ t a _ h
        exact ⟨(r, ()), by simp [hr], hp⟩
  | fcvt f g =>
      obtain ⟨a, ⟨⟩⟩ := args
      exact ⟨(evalConvertFloat f g a, ()), rfl, convertFloat_eval f g a h⟩
  | fptoui f n =>
      obtain ⟨a, ⟨⟩⟩ := args
      dsimp only [OpCode.wp, evalOpCode] at h ⊢
      cases htr : truncToInt (unpackFloat f a) with
      | none => rw [htr] at h; exact False.elim h
      | some z =>
          rw [htr] at h
          exact ⟨(BitVec.ofInt n z, ()), by simp [h.1, h.2.1], h.2.2⟩
  | fptosi f n =>
      obtain ⟨a, ⟨⟩⟩ := args
      dsimp only [OpCode.wp, evalOpCode] at h ⊢
      obtain ⟨hn, h2⟩ := h
      rw [ite_eq_left hn]
      cases htr : truncToInt (unpackFloat f a) with
      | none => rw [htr] at h2; exact False.elim h2
      | some z =>
          rw [htr] at h2
          exact ⟨(BitVec.ofInt n z, ()), by simp [h2.1, h2.2.1], h2.2.2⟩
  | _ =>
      try cases ‹_ = Ty.mask _›
      try obtain ⟨_, _, _, ⟨⟩⟩ := args
      try obtain ⟨_, _, ⟨⟩⟩ := args
      try obtain ⟨_, ⟨⟩⟩ := args
      dsimp only [OpCode.wp, evalOpCode] at h ⊢
      first
        | exact ⟨_, rfl, h⟩
        | (split at h
           · exact False.elim h
           · rename_i hf; rw [ite_eq_right hf]; exact ⟨_, rfl, h⟩)
        | (obtain ⟨h1, h2⟩ := h; rw [ite_eq_left h1]; exact ⟨_, rfl, h2⟩)
        | (obtain ⟨h1, h2, h3⟩ := h; rw [ite_eq_left ⟨h1, h2⟩]; exact ⟨_, rfl, h3⟩)

/-- `BlockFlat.wp` implies concrete deterministic execution of `BlockFlat.exec`. -/
theorem BlockFlat.wp_imp_exec {ρ : SymEnv} {Ψ : CodeSpec} {H : HaltPost} :
    (b : BlockFlat) → ∀ vs m,
    b.wp ρ Ψ H vs m →
    ∃ out, b.exec ρ vs m = some out ∧
      match out with
      | .halt code m' => H code m'
      | .jump pc' st' => Ψ pc' st'
  | .let_ op k, vs, m, h => by
      dsimp only [BlockFlat.wp, BlockFlat.exec] at h ⊢
      cases hargs : denoteArgs vs op.args with
      | none => rw [hargs] at h; exact False.elim h
      | some args' =>
          rw [hargs] at h; dsimp only at h ⊢
          obtain ⟨r, hev, hk⟩ := OpCode.wp_imp_eval op.code (vals args') h
          rw [hev]
          exact BlockFlat.wp_imp_exec k (pushTup r vs) m hk
  | .load ty a k, vs, m, h => by
      dsimp only [BlockFlat.wp, BlockFlat.exec] at h ⊢
      cases ha : denoteArg vs a with
      | none => rw [ha] at h; exact False.elim h
      | some a' =>
          rw [ha] at h; dsimp only at h ⊢
          rcases h with ⟨v, hv, hk⟩
          rw [hv]
          exact BlockFlat.wp_imp_exec k (⟨ty, v⟩ :: vs) m hk
  | .store (t := ty) v a k, vs, m, h => by
      dsimp only [BlockFlat.wp, BlockFlat.exec] at h ⊢
      cases hv : denoteArg vs v with
      | none => rw [hv] at h; exact False.elim h
      | some v' =>
          cases ha : denoteArg vs a with
          | none => rw [hv, ha] at h; exact False.elim h
          | some a' =>
              rw [hv, ha] at h; dsimp only at h ⊢
              rcases h with ⟨⟨i, hi⟩, hk⟩
              have his : (m.loadInt a'.val ty.bytes).isSome = true := by rw [hi]; rfl
              rw [ite_eq_left his]
              exact BlockFlat.wp_imp_exec k vs (storeMem m ty a'.val v'.val) hk
  | .codeAddr sym k, vs, m, h => by
      dsimp only [BlockFlat.wp, BlockFlat.exec] at h ⊢
      rcases h with ⟨a, ha, hk⟩
      rw [ha]
      exact BlockFlat.wp_imp_exec k (⟨i64, a⟩ :: vs) m hk
  | .jnz c t e, vs, m, h => by
      dsimp only [BlockFlat.wp, BlockFlat.exec] at h ⊢
      cases hc : denoteArg vs c with
      | none => rw [hc] at h; exact False.elim h
      | some c' =>
          rw [hc] at h; dsimp only at h ⊢
          cases hv : c'.val
          · rw [ite_eq_right (by simp)]
            exact BlockFlat.wp_imp_exec e vs m (h.2 hv)
          · rw [ite_eq_left rfl]
            exact BlockFlat.wp_imp_exec t vs m (h.1 hv)
  | .ijmp tgt nxt, vs, m, h => by
      dsimp only [BlockFlat.wp, BlockFlat.exec] at h ⊢
      cases ht : denoteArg vs tgt with
      | none => rw [ht] at h; exact False.elim h
      | some tgt' =>
          cases hn : denoteRegsExpr vs nxt with
          | none => rw [ht, hn] at h; exact False.elim h
          | some nxt' =>
              rw [ht, hn] at h; dsimp only at h ⊢
              exact ⟨.jump tgt'.val ⟨nxt'.eval, m⟩, rfl, h⟩
  | .halt c, vs, m, h => by
      dsimp only [BlockFlat.wp, BlockFlat.exec] at h ⊢
      cases hc : denoteArg vs c with
      | none => rw [hc] at h; exact False.elim h
      | some c' =>
          rw [hc] at h; dsimp only at h ⊢
          exact ⟨.halt c'.val m, rfl, h⟩
  | .hlt, _, _, h => False.elim h

theorem Step_det {cm : CodeMap} {pc : BitVec 64} {st : State} {o₁ o₂ : BlockOutcome}
    (h₁ : Step cm pc st o₁) (h₂ : Step cm pc st o₂) : o₁ = o₂ := by
  rcases h₁ with ⟨b₁, hl₁, he₁⟩
  rcases h₂ with ⟨b₂, hl₂, he₂⟩
  rw [hl₁] at hl₂; cases hl₂
  rw [he₁] at he₂; cases he₂
  rfl

theorem Halts_det {cm : CodeMap} {pc : BitVec 64} {st : State} {c₁ c₂ : BitVec 64}
    {m₁ m₂ : Mem 64} (h₁ : Halts cm pc st c₁ m₁) (h₂ : Halts cm pc st c₂ m₂) :
    c₁ = c₂ ∧ m₁ = m₂ := by
  induction h₁ with
  | halt hs₁ =>
      cases h₂ with
      | halt hs₂ =>
          have heq := Step_det hs₁ hs₂; cases heq; exact ⟨rfl, rfl⟩
      | jump hs₂ _ =>
          have heq := Step_det hs₁ hs₂; cases heq
  | jump hs₁ _ ih =>
      cases h₂ with
      | halt hs₂ =>
          have heq := Step_det hs₁ hs₂; cases heq
      | jump hs₂ hh₂ =>
          have heq := Step_det hs₁ hs₂; cases heq; exact ih hh₂

theorem runFuel_sound {cm : CodeMap} :
    ∀ {fuel : Nat} {pc : BitVec 64} {st : State} {code : BitVec 64} {m' : Mem 64},
    runFuel cm fuel pc st = some (code, m') → Halts cm pc st code m'
  | 0, _, _, _, _, h => by simp [runFuel] at h
  | fuel + 1, pc, st, code, m', h => by
      dsimp only [runFuel] at h
      cases hlu : cm.lookupAddr pc with
      | none => rw [hlu] at h; cases h
      | some b =>
          rw [hlu] at h; dsimp only at h
          cases hex : b.exec cm.symEnv (pushRegsV st.regs.toRegsV) st.mem with
          | none => rw [hex] at h; cases h
          | some out =>
              rw [hex] at h
              cases out with
              | halt c m'' =>
                  cases h; exact .halt ⟨b, hlu, hex⟩
              | jump pc' st' =>
                  exact .jump ⟨b, hlu, hex⟩ (runFuel_sound h)

theorem runFuel_complete {cm : CodeMap} {pc : BitVec 64} {st : State} {code : BitVec 64}
    {m' : Mem 64} (h : Halts cm pc st code m') :
    ∃ fuel, runFuel cm fuel pc st = some (code, m') := by
  induction h with
  | halt hs =>
      rcases hs with ⟨b, hlu, hex⟩
      exact ⟨1, by simp [runFuel, hlu, hex]⟩
  | jump hs _ ih =>
      rcases hs with ⟨b, hlu, hex⟩
      obtain ⟨fuel, hf⟩ := ih
      exact ⟨fuel + 1, by simp [runFuel, hlu, hex, hf]⟩

theorem unmapped_stuck {cm : CodeMap} {pc : BitVec 64} (hnone : cm.lookupAddr pc = none)
    (st : State) (code : BitVec 64) (m' : Mem 64) :
    ¬ Halts cm pc st code m' := by
  intro h
  cases h with
  | halt hs | jump hs _ =>
      rcases hs with ⟨_, hlu, _⟩
      rw [hnone] at hlu; cases hlu

theorem unaligned_stuck {cm : CodeMap} (hal : cm.Aligned) {pc : BitVec 64}
    (hun : ¬ AlignedAddr pc) (st : State) (code : BitVec 64) (m' : Mem 64) :
    ¬ Halts cm pc st code m' :=
  unmapped_stuck (CodeMap.lookupAddr_none_of_unaligned hal hun) st code m'

/-! ## §5. Macro Layout Lemmas -/

theorem inRange_mono_left {base : BitVec 64} {n₁ n₂ : Nat} {a : BitVec 64}
    (h : InRange base n₁ a) : InRange base (n₁ + n₂) a := by
  rcases h with ⟨i, hi, rfl⟩
  exact ⟨i, by omega, rfl⟩

theorem inRange_shift {base : BitVec 64} {n₁ n₂ : Nat} {a : BitVec 64}
    (h : InRange (base + BitVec.ofNat 64 (8 * n₁)) n₂ a) :
    InRange base (n₁ + n₂) a := by
  rcases h with ⟨j, hj, rfl⟩
  refine ⟨n₁ + j, by omega, ?_⟩
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add]

theorem atomicM_wellLaidOut
    {step : ∀ (V : Ty → Type), RegsV V → (RegsExpr V → BlockB V) → BlockB V}
    (hwf : ∀ cont, BlockP.Wf (fun V r => step V r (fun nxt => .ijmp (.imm cont) nxt))) :
    (atomicM step).WellLaidOut := by
  intro pfx base cont e he
  simp only [atomicM, List.mem_singleton] at he; subst he
  exact ⟨⟨0, by simp [atomicM], by simp⟩, hwf cont⟩

theorem seqM_wellLaidOut {m₁ m₂ : Macro} (h₁ : m₁.WellLaidOut) (h₂ : m₂.WellLaidOut) :
    (seqM m₁ m₂).WellLaidOut := by
  intro pfx base cont e he
  simp only [seqM, List.mem_append] at he
  rcases he with he₁ | he₂
  · obtain ⟨hr, hw⟩ := h₁ _ _ _ e he₁
    exact ⟨inRange_mono_left hr, hw⟩
  · obtain ⟨hr, hw⟩ := h₂ _ _ _ e he₂
    exact ⟨inRange_shift hr, hw⟩

theorem ifM_wellLaidOut
    {cond : ∀ (V : Ty → Type), RegsV V → (V .bool → BlockB V) → BlockB V}
    {mT mE : Macro}
    (hc : ∀ tAddr eAddr, BlockP.Wf (fun V r =>
      cond V r (fun b =>
        .jnz (.var b) (.ijmp (.imm tAddr) r.keep) (.ijmp (.imm eAddr) r.keep))))
    (hT : mT.WellLaidOut) (hE : mE.WellLaidOut) :
    (ifM cond mT mE).WellLaidOut := by
  intro pfx base cont e he
  simp only [ifM, List.mem_cons, List.mem_append] at he
  rcases he with rfl | heT | heE
  · exact ⟨⟨0, by simp [ifM]; omega, by simp⟩, hc _ _⟩
  · obtain ⟨hr, hw⟩ := hT _ _ _ e heT
    have hr1 : InRange base (1 + mT.size) e.addr :=
      inRange_shift (n₁ := 1) (n₂ := mT.size) hr
    exact ⟨inRange_mono_left hr1, hw⟩
  · obtain ⟨hr, hw⟩ := hE _ _ _ e heE
    exact ⟨inRange_shift (n₁ := 1 + mT.size) (n₂ := mE.size) hr, hw⟩

theorem whileM_wellLaidOut
    {cond : ∀ (V : Ty → Type), RegsV V → (V .bool → BlockB V) → BlockB V}
    {body : Macro}
    (hc : ∀ bAddr cont, BlockP.Wf (fun V r =>
      cond V r (fun b =>
        .jnz (.var b) (.ijmp (.imm bAddr) r.keep) (.ijmp (.imm cont) r.keep))))
    (hb : body.WellLaidOut) :
    (whileM cond body).WellLaidOut := by
  intro pfx base cont e he
  simp only [whileM, List.mem_cons] at he
  rcases he with rfl | heB
  · exact ⟨⟨0, by simp [whileM]; omega, by simp⟩, hc _ _⟩
  · obtain ⟨hr, hw⟩ := hb _ _ _ e heB
    exact ⟨inRange_shift (n₁ := 1) (n₂ := body.size) hr, hw⟩

end LeanQbe.T.BedrockWord
