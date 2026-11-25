module

public import LeanQbe.T.LinkParamEnv
import LeanQbe.T.WPLemmas

/-!
# Depth-Indexed `DepthEnv.lfp` Order-Theoretic Core (`LinkDepthLfp`)

Purely target-independent order-theoretic fixed-point core over `DepthEnv := ParamEnv Nat`,
backed by `LeanQbe.T.LinkParamEnv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

open LeanQbe.T.LinkRec
open LeanQbe.T.LinkScc

/-! ## 1. Depth-Indexed Environments and Knaster–Tarski `DepthEnv.lfp` -/

abbrev DepthEnv : Type := ParamEnv Nat
abbrev DepthEnv.le (A B : DepthEnv) : Prop := ParamEnv.le A B
theorem DepthEnv.le_refl (A : DepthEnv) : DepthEnv.le A A := ParamEnv.le_refl A
theorem DepthEnv.le_trans {A B C : DepthEnv} (h₁ : DepthEnv.le A B) (h₂ : DepthEnv.le B C) :
    DepthEnv.le A C := ParamEnv.le_trans h₁ h₂
abbrev DepthEnv.bot : DepthEnv := ParamEnv.bot
theorem DepthEnv.bot_le (A : DepthEnv) : DepthEnv.le DepthEnv.bot A := ParamEnv.bot_le A
abbrev DepthEnv.mono (Φ : DepthEnv → DepthEnv) : Prop := ParamEnv.mono Φ
abbrev DepthEnv.lfp (Φ : DepthEnv → DepthEnv) : DepthEnv := ParamEnv.lfp Φ

theorem DepthEnv.lfp_le {Φ : DepthEnv → DepthEnv} {G : DepthEnv} (h : DepthEnv.le (Φ G) G) :
    DepthEnv.le (DepthEnv.lfp Φ) G := ParamEnv.lfp_le h
theorem DepthEnv.lfp_closed {Φ : DepthEnv → DepthEnv} (hm : DepthEnv.mono Φ) :
    DepthEnv.le (Φ (DepthEnv.lfp Φ)) (DepthEnv.lfp Φ) := ParamEnv.lfp_closed hm
theorem DepthEnv.lfp_pre {Φ : DepthEnv → DepthEnv} (hm : DepthEnv.mono Φ) :
    DepthEnv.le (Φ (DepthEnv.lfp Φ)) (DepthEnv.lfp Φ) := ParamEnv.lfp_closed hm
theorem DepthEnv.lfp_post {Φ : DepthEnv → DepthEnv} (hm : DepthEnv.mono Φ) :
    DepthEnv.le (DepthEnv.lfp Φ) (Φ (DepthEnv.lfp Φ)) := ParamEnv.lfp_post hm
theorem DepthEnv.lfp_fix {Φ : DepthEnv → DepthEnv} (hm : DepthEnv.mono Φ) :
    DepthEnv.lfp Φ = Φ (DepthEnv.lfp Φ) := ParamEnv.lfp_fix hm
theorem DepthEnv.lfp_mono {Φ₁ Φ₂ : DepthEnv → DepthEnv} (hm₂ : DepthEnv.mono Φ₂)
    (hle : ∀ G, DepthEnv.le (Φ₁ G) (Φ₂ G)) : DepthEnv.le (DepthEnv.lfp Φ₁) (DepthEnv.lfp Φ₂) :=
  ParamEnv.lfp_mono hm₂ hle

/-! ## 2. Depth Monotonicity and Well-Founded Introduction (`DepthEnv.lfp_wf`) -/

abbrev DepthEnv.IsDepthMono (G : DepthEnv) : Prop := ParamEnv.IsRelMono (· ≤ ·) G
abbrev DepthEnv.PreservesDepthMono (Φ : DepthEnv → DepthEnv) : Prop :=
  ParamEnv.PreservesRelMono (· ≤ ·) Φ

theorem DepthEnv.lfp_depth_mono {Φ : DepthEnv → DepthEnv}
    (hm : DepthEnv.mono Φ) (hdm : DepthEnv.PreservesDepthMono Φ) :
    DepthEnv.IsDepthMono (DepthEnv.lfp Φ) :=
  ParamEnv.lfp_rel_mono (· ≤ ·) Nat.le_refl (fun _ _ _ => Nat.le_trans) hm hdm

theorem DepthEnv.lfp_depth_mono_of_shift {Φ : DepthEnv → DepthEnv} (hm : DepthEnv.mono Φ)
    (hshift : ∀ (G : DepthEnv) (d : Nat), Env.le (Φ (fun k => G (k + 1)) d) (Φ G (d + 1))) :
    DepthEnv.IsDepthMono (DepthEnv.lfp Φ) := by
  have step : ∀ d, Env.le (DepthEnv.lfp Φ d) (DepthEnv.lfp Φ (d + 1)) :=
    DepthEnv.lfp_le (G := fun k => DepthEnv.lfp Φ (k + 1)) fun d =>
      Env.le_trans (hshift (DepthEnv.lfp Φ) d) (DepthEnv.lfp_closed hm (d + 1))
  intro d₁ d₂ hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  induction k with
  | zero => exact Env.le_refl _
  | succ k ih => exact Env.le_trans (ih (Nat.le_add_right d₁ k)) (step (d₁ + k))

abbrev DepthEnv.supBelow {ι : Type} (lt : ι → ι → Prop) (depth : ι → Nat)
    (S : ι → Env) (i : ι) : DepthEnv := ParamEnv.supBelow (· ≤ ·) lt depth S i

theorem DepthEnv.supBelow_call {ι : Type} {lt : ι → ι → Prop} {depth : ι → Nat}
    {S : ι → Env} {i j : ι} (hlt : lt j i) (hdep : depth j < depth i) :
    Env.le (S j) (DepthEnv.supBelow lt depth S i (depth i - 1)) :=
  fun _ _ _ _ _ _ _ hS => ⟨j, hlt, Nat.le_pred_of_lt hdep, hS⟩

theorem DepthEnv.supBelow_tail {ι : Type} {lt : ι → ι → Prop} {depth : ι → Nat}
    {S : ι → Env} {i j : ι} (hlt : lt j i) (hdep : depth j ≤ depth i) :
    Env.le (S j) (DepthEnv.supBelow lt depth S i (depth i)) :=
  fun _ _ _ _ _ _ _ hS => ⟨j, hlt, hdep, hS⟩

theorem DepthEnv.lfp_wf {ι : Type} {lt : ι → ι → Prop} (hwf : WellFounded lt)
    (depth : ι → Nat) {Φ : DepthEnv → DepthEnv}
    (hm : DepthEnv.mono Φ) (hdm : DepthEnv.PreservesDepthMono Φ) (S : ι → Env)
    (hstep : ∀ i, Env.le (S i) (Φ (DepthEnv.supBelow lt depth S i) (depth i))) :
    ∀ i, Env.le (S i) (DepthEnv.lfp Φ (depth i)) :=
  ParamEnv.lfp_wf_mono (· ≤ ·) hwf Nat.le_refl (fun _ _ _ => Nat.le_trans) depth hm hdm S hstep

theorem DepthEnv.lfp_wf_recIdx {ι : Type} (idx : RecIdx ι) {Φ : DepthEnv → DepthEnv}
    (hm : DepthEnv.mono Φ) (hdm : DepthEnv.PreservesDepthMono Φ) (S : ι → Env)
    (hstep : ∀ i, Env.le (S i) (Φ (DepthEnv.supBelow idx.lt idx.depth S i) (idx.depth i))) :
    ∀ i, Env.le (S i) (DepthEnv.lfp Φ (idx.depth i)) :=
  DepthEnv.lfp_wf idx.wf idx.depth hm hdm S hstep

/-! ## 3. Split-Slot Module Operators (`DepthEnv.mkSccOp`, `DepthEnv.sccOp`, `DepthEnv.semScc`) -/

@[expose] def DepthEnv.callSlot (M : Module) (Γext : Env) (G : DepthEnv) : Nat → Env
  | 0 => Env.extStep M Γext
  | d + 1 => Env.sccStep M (G d) Γext

@[expose] def DepthEnv.tailSlot (M : Module) (Γext : Env) (G : DepthEnv) (d : Nat) : Env :=
  Env.sccStep M (G d) Γext

theorem DepthEnv.extStep_le_sccStep (M : Module) (Γ Γext : Env) :
    Env.le (Env.extStep M Γext) (Env.sccStep M Γ Γext) :=
  fun _ _ _ _ _ _ _ h => Or.inr h

theorem DepthEnv.callSlot_le_tailSlot {M : Module} {Γext : Env} {G : DepthEnv}
    (hdm : DepthEnv.IsDepthMono G) (d : Nat) :
    Env.le (DepthEnv.callSlot M Γext G d) (DepthEnv.tailSlot M Γext G d) := by
  cases d with
  | zero => exact DepthEnv.extStep_le_sccStep M (G 0) Γext
  | succ d =>
      rintro f as bs xs m Q X (⟨hfns, hG⟩ | ⟨hext, hG⟩)
      · exact Or.inl ⟨hfns, hdm (Nat.le_succ d) f as bs xs m Q X hG⟩
      · exact Or.inr ⟨hext, hG⟩

theorem DepthEnv.callSlot_mono {M : Module} {Γext : Env} {A B : DepthEnv}
    (hle : DepthEnv.le A B) : ∀ d, Env.le (DepthEnv.callSlot M Γext A d)
      (DepthEnv.callSlot M Γext B d)
  | 0 => Env.le_refl _
  | d + 1 => by
      rintro f as bs xs m Q X (⟨hfns, hA⟩ | ⟨hext, hA⟩)
      · exact Or.inl ⟨hfns, hle d f as bs xs m Q X hA⟩
      · exact Or.inr ⟨hext, hA⟩

theorem DepthEnv.tailSlot_mono {M : Module} {Γext : Env} {A B : DepthEnv}
    (hle : DepthEnv.le A B) (d : Nat) :
    Env.le (DepthEnv.tailSlot M Γext A d) (DepthEnv.tailSlot M Γext B d) := by
  rintro f as bs xs m Q X (⟨hfns, hA⟩ | ⟨hext, hA⟩)
  · exact Or.inl ⟨hfns, hle d f as bs xs m Q X hA⟩
  · exact Or.inr ⟨hext, hA⟩

theorem DepthEnv.callSlot_depth_mono {M : Module} {Γext : Env} {G : DepthEnv}
    (hdm : DepthEnv.IsDepthMono G) : DepthEnv.IsDepthMono (DepthEnv.callSlot M Γext G) := by
  intro d₁ d₂ hd
  cases d₁ with
  | zero => cases d₂ with
      | zero => exact Env.le_refl _
      | succ d₂ => exact DepthEnv.extStep_le_sccStep M (G d₂) Γext
  | succ d₁ =>
      obtain ⟨d₂, rfl⟩ : ∃ k, d₂ = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
      rintro f as bs xs m Q X (⟨hfns, hG⟩ | ⟨hext, hG⟩)
      · exact Or.inl ⟨hfns, hdm (Nat.succ_le_succ_iff.mp hd) f as bs xs m Q X hG⟩
      · exact Or.inr ⟨hext, hG⟩

theorem DepthEnv.tailSlot_depth_mono {M : Module} {Γext : Env} {G : DepthEnv}
    (hdm : DepthEnv.IsDepthMono G) : DepthEnv.IsDepthMono (DepthEnv.tailSlot M Γext G) := by
  rintro d₁ d₂ hd f as bs xs m Q X (⟨hfns, hG⟩ | ⟨hext, hG⟩)
  · exact Or.inl ⟨hfns, hdm hd f as bs xs m Q X hG⟩
  · exact Or.inr ⟨hext, hG⟩

@[expose] def DepthEnv.mkSccOp (M : Module) (Γext : Env) (op₂ : Env → Env → Env)
    (G : DepthEnv) (d : Nat) : Env :=
  op₂ (DepthEnv.callSlot M Γext G d) (DepthEnv.tailSlot M Γext G d)

theorem DepthEnv.mkSccOp_mono {M : Module} {Γext : Env} {op₂ : Env → Env → Env}
    (hbi : Env.BiMono op₂) : DepthEnv.mono (DepthEnv.mkSccOp M Γext op₂) :=
  fun _ _ hle d => hbi (DepthEnv.callSlot_mono hle d) (DepthEnv.tailSlot_mono hle d)

theorem DepthEnv.mkSccOp_preservesDepthMono {M : Module} {Γext : Env} {op₂ : Env → Env → Env}
    (hbi : Env.BiMono op₂) : DepthEnv.PreservesDepthMono (DepthEnv.mkSccOp M Γext op₂) :=
  fun _ hdm _ _ hd =>
    hbi (DepthEnv.callSlot_depth_mono hdm hd) (DepthEnv.tailSlot_depth_mono hdm hd)

theorem DepthEnv.lfp_wf_mkSccOp {ι : Type} {lt : ι → ι → Prop} (hwf : WellFounded lt)
    (depth : ι → Nat) (M : Module) (Γext : Env) {op₂ : Env → Env → Env} (hbi : Env.BiMono op₂)
    (S : ι → Env)
    (hstep : ∀ (i : ι) (Γcall Γtail : Env),
      (∀ j, lt j i → depth j < depth i → Env.le (Env.restrict (S j) (M.fns.map Fn.sig)) Γcall) →
      Env.le (Env.extStep M Γext) Γcall →
      (∀ j, lt j i → depth j ≤ depth i → Env.le (Env.restrict (S j) (M.fns.map Fn.sig)) Γtail) →
      Env.le (Env.extStep M Γext) Γtail →
      Env.le (Env.restrict (S i) (M.fns.map Fn.sig)) (op₂ Γcall Γtail)) :
    ∀ i, Env.le (Env.restrict (S i) (M.fns.map Fn.sig))
      (DepthEnv.lfp (DepthEnv.mkSccOp M Γext op₂) (depth i)) := by
  let S' : ι → Env := fun i => Env.restrict (S i) (M.fns.map Fn.sig)
  refine DepthEnv.lfp_wf hwf depth (DepthEnv.mkSccOp_mono hbi)
    (DepthEnv.mkSccOp_preservesDepthMono hbi) S' fun i => ?_
  refine hstep i _ _ (fun j hlt hdep => ?_) ?_ (fun j hlt hdep => ?_) ?_
  · cases hd : depth i with
    | zero => omega
    | succ d' =>
        intro f as bs xs m Q X hSj
        exact Or.inl ⟨hSj.1, j, hlt, by rw [hd] at hdep; exact Nat.lt_succ_iff.mp hdep, hSj⟩
  · cases depth i with
    | zero => exact Env.le_refl _
    | succ _ => exact DepthEnv.extStep_le_sccStep M _ Γext
  · intro f as bs xs m Q X hSj; exact Or.inl ⟨hSj.1, j, hlt, hdep, hSj⟩
  · exact DepthEnv.extStep_le_sccStep M _ Γext

@[expose] def DepthEnv.sccOp (M : Module) (Γext : Env) : DepthEnv → DepthEnv :=
  DepthEnv.mkSccOp M Γext fun Γcall _ f as bs xs m Q X =>
    (f, as, bs) ∈ M.fns.map Fn.sig ∧ ∃ fn ∈ M.fns, fn.name = f ∧
      ∃ (ha : fn.as = as) (hr : fn.rs = bs), Func.wp Γcall fn.body (ha ▸ xs) m (hr ▸ Q) X

private theorem wp_sccOp_biMono (M : Module) :
    Env.BiMono fun Γcall _ f as bs xs m Q X =>
      (f, as, bs) ∈ M.fns.map Fn.sig ∧ ∃ fn ∈ M.fns, fn.name = f ∧
        ∃ (ha : fn.as = as) (hr : fn.rs = bs), Func.wp Γcall fn.body (ha ▸ xs) m (hr ▸ Q) X := by
  rintro _ _ _ _ hC _ f as bs xs m Q X ⟨hsig, fn, hfn, hnm, ha, hr, hwp⟩
  exact ⟨hsig, fn, hfn, hnm, ha, hr, wp_env_mono hC _ m hwp⟩

theorem DepthEnv.sccOp_mono (M : Module) (Γext : Env) : DepthEnv.mono (DepthEnv.sccOp M Γext) :=
  DepthEnv.mkSccOp_mono (wp_sccOp_biMono M)

theorem DepthEnv.sccOp_preservesDepthMono (M : Module) (Γext : Env) :
    DepthEnv.PreservesDepthMono (DepthEnv.sccOp M Γext) :=
  DepthEnv.mkSccOp_preservesDepthMono (wp_sccOp_biMono M)

@[expose] def DepthEnv.semScc (M : Module) (Γext : Env) : DepthEnv :=
  DepthEnv.lfp (DepthEnv.sccOp M Γext)

theorem DepthEnv.semScc_depth_mono (M : Module) (Γext : Env) :
    DepthEnv.IsDepthMono (DepthEnv.semScc M Γext) :=
  DepthEnv.lfp_depth_mono (DepthEnv.sccOp_mono M Γext) (DepthEnv.sccOp_preservesDepthMono M Γext)

theorem DepthEnv.semScc_fix (M : Module) (Γext : Env) :
    DepthEnv.semScc M Γext = DepthEnv.sccOp M Γext (DepthEnv.semScc M Γext) :=
  DepthEnv.lfp_fix (DepthEnv.sccOp_mono M Γext)

/-! ## 4. Bridges Between `DepthEnv.lfp` and `LinkLfp` (`Env.lfp`, `Env.semScc`, `unfoldRecAt`) -/

@[expose] def DepthEnv.liftOp (Φ : Env → Env) (G : DepthEnv) (d : Nat) : Env := Φ (G d)

theorem DepthEnv.liftOp_mono {Φ : Env → Env} (hm : Env.mono Φ) :
    DepthEnv.mono (DepthEnv.liftOp Φ) := fun _ _ hle d => hm (hle d)

theorem DepthEnv.lfp_liftOp_eq {Φ : Env → Env} (hm : Env.mono Φ) (d : Nat) :
    DepthEnv.lfp (DepthEnv.liftOp Φ) d = Env.lfp Φ := by
  funext f as bs xs m Q X
  exact propext ⟨fun h => h (fun _ => Env.lfp Φ) (fun _ => Env.lfp_pre hm),
    fun h G hG => h (G d) (hG d)⟩

theorem DepthEnv.lfp_tailOnly_zero_eq (M : Module) (Γext : Env) {op₂ : Env → Env → Env}
    (hbi : Env.BiMono op₂) (htail : ∀ C₁ C₂ T, op₂ C₁ T = op₂ C₂ T) :
    DepthEnv.lfp (DepthEnv.mkSccOp M Γext op₂) 0 =
      Env.lfp (fun Γ => op₂ (Env.extStep M Γext) (Env.sccStep M Γ Γext)) := by
  have hm1 : Env.mono (fun Γ => op₂ (Env.extStep M Γext) (Env.sccStep M Γ Γext)) := fun _ _ h =>
    hbi (Env.le_refl _) (DepthEnv.tailSlot_mono (A := fun _ => _) (B := fun _ => _) (fun _ => h) 0)
  funext f as bs xs m Q X
  refine propext ⟨fun h => ?_, fun h G hG => h (G 0) (hG 0)⟩
  refine h (fun _ => Env.lfp (fun Γ => op₂ (Env.extStep M Γext) (Env.sccStep M Γ Γext))) fun d => ?_
  dsimp only [DepthEnv.mkSccOp]; rw [htail (DepthEnv.callSlot M Γext _ d) (Env.extStep M Γext)]
  exact Env.lfp_pre hm1

theorem DepthEnv.semScc_le_envSemScc (M : Module) (Γext : Env) (d : Nat) :
    Env.le (DepthEnv.semScc M Γext d) (Env.semScc M Γext) := by
  let G : DepthEnv := fun _ => Env.semScc M Γext
  refine DepthEnv.lfp_le (G := G) (fun k => ?_) d
  have hle : Env.le (DepthEnv.callSlot M Γext G k) (Env.sccStep M (Env.semScc M Γext) Γext) := by
    cases k with
    | zero => exact DepthEnv.extStep_le_sccStep M _ Γext
    | succ _ => exact Env.le_refl _
  exact Env.le_trans (wp_sccOp_biMono M hle (Env.le_refl (DepthEnv.tailSlot M Γext G k)))
    (Env.lfp_pre (LeanQbe.T.sccOp_mono M Γext))

private theorem unfoldRecBelow_mono_depth {M : Module} {Γext : Env} :
    ∀ {j k : Nat}, j ≤ k → Env.le (Env.unfoldRecBelow M Γext j) (Env.unfoldRecBelow M Γext k)
  | _, 0, hjk, _, _, _, _, _, _, _, h => by obtain rfl : _ = 0 := Nat.le_zero.mp hjk; exact h
  | _, k + 1, hjk, f, as, bs, xs, m, Q, X, h => by
      rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
      · exact h
      · exact Or.inl (unfoldRecBelow_mono_depth (Nat.lt_succ_iff.mp hlt) f as bs xs m Q X h)

private theorem sccStep_unfoldRecAt_le (M : Module) (Γext : Env) (d : Nat) :
    Env.le (Env.sccStep M (Env.unfoldRecAt M Γext d) Γext) (Env.unfoldRecAt M Γext d) := by
  rintro f as bs xs m Q X (⟨_, hU⟩ | ⟨hext, hΓ⟩)
  · exact hU
  · exact unfoldRecBelow_mono_depth (Nat.zero_le (d + 1)) f as bs xs m Q X ⟨hext, hΓ⟩

theorem DepthEnv.semScc_le_unfoldRecAt (M : Module) (Γext : Env) (d : Nat) :
    Env.le (DepthEnv.semScc M Γext d) (Env.unfoldRecAt M Γext d) := by
  refine DepthEnv.lfp_le (G := fun k => Env.unfoldRecAt M Γext k) (fun k => ?_) d
  cases k with
  | zero => exact fun _ _ _ _ _ _ _ ⟨hsig, fn, hfn, hnm, ha, hr, hwp⟩ =>
      Or.inr ⟨hsig, fn, hfn, hnm, ha, hr, hwp⟩
  | succ k =>
      rintro _ _ _ _ m _ _ ⟨hsig, fn, hfn, hnm, ha, hr, hwp⟩
      exact Or.inr ⟨hsig, fn, hfn, hnm, ha, hr,
        wp_env_mono (sccStep_unfoldRecAt_le M Γext k) _ m hwp⟩

theorem DepthEnv.moduleSccOk_strict_le_semScc {ι : Type} {idx : RecIdx ι} {Γrec : ι → Env}
    {Γext : Env} {M : Module} (hM : ModuleSccOk idx Γrec Γext true M) :
    ∀ i, Env.le (Env.restrict (Γrec i) (M.fns.map Fn.sig))
      (DepthEnv.semScc M Γext (idx.depth i)) := by
  refine DepthEnv.lfp_wf_mkSccOp idx.wf idx.depth M Γext (wp_sccOp_biMono M) Γrec ?_
  intro i Γcall _ hrec hext _ _ f as bs xs m Q X ⟨hsig, hΓ⟩
  obtain ⟨fn, hfn, hfeq⟩ := List.mem_map.mp hsig
  rcases Prod.mk.inj hfeq with ⟨rfl, hsig_ab⟩; rcases Prod.mk.inj hsig_ab with ⟨rfl, rfl⟩
  refine ⟨hsig, fn, hfn, rfl, rfl, rfl,
    wp_env_mono (fun g as' bs' xs' m' Q' X' hg => ?_) _ m ((hM.fnsOk fn hfn).2.2 i xs m Q X hΓ)⟩
  rcases hg with ⟨hfns, j, hlt, hst, hΓ'⟩ | ⟨hex, hΓ'⟩
  · rcases hst with hfalse | hdep
    · cases hfalse
    · exact hrec j hlt hdep g as' bs' xs' m' Q' X' ⟨hfns, hΓ'⟩
  · exact hext g as' bs' xs' m' Q' X' ⟨hex, hΓ'⟩

end LeanQbe.T
