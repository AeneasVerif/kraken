module

public import LeanQbe.T.BedrockWord.Ops
public import LeanQbe.T.Xcap.Link

/-!
# BedrockWord L0 Instantiation onto `LeanQbe.T.Xcap` (`BedrockWord.Exec`)

Connects `LeanQbe.T.BedrockWord` directly to the generic XCAP core (`LeanQbe.T.Xcap`):

* `bwMach`, `bwHalt`: `Xcap.Mach State BlockFlat` and `Xcap.Halt State` instance.
* `SpecsClosed`, `CodeMap.wp`: connected to `Xcap.Closed` / `Xcap.wp` via `xcap_wp_of_wp`.
* `CodeMap.adequacy`, `CodeMap.adequacy_runFuel`, `CodeMap.not_wp_of_stuck`.
* `CodeMap.wp_of_ranked`, `CodeMap.wp_of_ranked_nat` (via `Xcap.wp_of_ranked`).
* `SpecsClosed.split`, `SpecsClosed.link`, `OpenModOk`, `OpenModOk.link`, `OpenModOk.close`,
  and `xcapModOk_of_openModOk`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.BedrockWord

open LeanQbe.T

/-! ## §1. `Xcap.Mach` Instantiation for BedrockWord L0 -/

/-- Generic `Xcap.Mach` executing `BlockFlat` over `(State, SymEnv)`. -/
@[expose] def bwMach (ρ : SymEnv) : Xcap.Mach State BlockFlat where
  exec b st o := match b.exec ρ (pushRegsV st.regs.toRegsV) st.mem with
    | some (.jump pc' st') => o = .jump pc' st'
    | some (.halt c m') => o = .halt c { st with mem := m' }
    | none => False

/-- `Xcap.Halt State` lifted from `HaltPost`. -/
@[expose] def bwHalt (H : HaltPost) : Xcap.Halt State :=
  fun c st => H c st.mem

/-- Impredicative XCAP code-pointer assertion matching `Xcap.cptr`. -/
@[expose] def cptr (Ψ : CodeSpec) (p : BitVec 64) (P : State → Prop) : Prop :=
  Xcap.cptr Ψ p P

theorem cptr_refl (Ψ : CodeSpec) (p : BitVec 64) : cptr Ψ p (Ψ p) :=
  fun _ h => h

theorem cptr_weaken {Ψ : CodeSpec} {p : BitVec 64} {P P' : State → Prop}
    (h : cptr Ψ p P) (himp : ∀ st, P' st → P st) : cptr Ψ p P' :=
  fun st hst => h st (himp st hst)

theorem cptr_mono_spec {Ψ₁ Ψ₂ : CodeSpec} {p : BitVec 64} {P : State → Prop}
    (hΨ : ∀ st, Ψ₁ p st → Ψ₂ p st) (h : cptr Ψ₁ p P) : cptr Ψ₂ p P :=
  fun st hst => hΨ st (h st hst)

/-- Prefixpoint closure of a `CodeSpec` `Ψ` with respect to every block in `cm`. -/
@[expose] def SpecsClosed (cm : CodeMap) (ρ : SymEnv) (Ψ : CodeSpec) (H : HaltPost) : Prop :=
  ∀ (pc : BitVec 64) (b : BlockFlat), cm.lookupAddr pc = some b →
    ∀ st : State, b.wp ρ Ψ H (pushRegsV st.regs.toRegsV) st.mem → Ψ pc st

theorem SpecsClosed.applyP {cm : CodeMap} {ρ : SymEnv} {Ψ : CodeSpec} {H : HaltPost}
    (hΨ : SpecsClosed cm ρ Ψ H) {pc : BitVec 64} {b : BlockP}
    (hlu : cm.lookupAddr pc = some (reifyBlock b)) (hwf : b.Wf)
    {st : State} (hwp : b.wp ρ Ψ H st) : Ψ pc st :=
  hΨ pc (reifyBlock b) hlu st ((BlockP.wp_toFlat hwf st).2 hwp)

/-- Total-correctness weakest precondition of a concrete `CodeMap` (Knaster–Tarski LFP). -/
@[expose] def CodeMap.wp (cm : CodeMap) (H : HaltPost) (pc : BitVec 64) (st : State) : Prop :=
  ∀ Ψ : CodeSpec, SpecsClosed cm cm.symEnv Ψ H → Ψ pc st

/-- Every `BlockFlat.wp` implies `Xcap.bwp (bwMach ρ)`. -/
theorem bwp_of_blockFlat_wp {ρ : SymEnv} {Ψ : CodeSpec} {H : HaltPost}
    {b : BlockFlat} {st : State} (h : b.wp ρ Ψ H (pushRegsV st.regs.toRegsV) st.mem) :
    Xcap.bwp (bwMach ρ) b Ψ (bwHalt H) st := by
  obtain ⟨out, hex, hout⟩ := BlockFlat.wp_imp_exec b _ _ h
  cases out with
  | jump pc' st' =>
      refine ⟨⟨.jump pc' st', ?_⟩, ?_, ?_⟩
      · simp [bwMach, hex]
      · intro p s hx; simp [bwMach, hex] at hx; rcases hx with ⟨rfl, rfl⟩; exact hout
      · intro c s hx; simp [bwMach, hex] at hx
  | halt c m' =>
      refine ⟨⟨.halt c { st with mem := m' }, ?_⟩, ?_, ?_⟩
      · simp [bwMach, hex]
      · intro p s hx; simp [bwMach, hex] at hx
      · intro c' s hx; simp [bwMach, hex] at hx; rcases hx with ⟨rfl, rfl⟩; exact hout

/-- Any `Xcap.Closed` invariant for `bwMach ρ` is `SpecsClosed`. -/
theorem specsClosed_of_xcap_closed {cm : CodeMap} {ρ : SymEnv} {Ψ : CodeSpec} {H : HaltPost}
    (hcl : Xcap.Closed (bwMach ρ) cm.lookupAddr Ψ (bwHalt H)) :
    SpecsClosed cm ρ Ψ H :=
  fun pc b hlu st hwp => hcl pc b hlu st (bwp_of_blockFlat_wp hwp)

/-- `CodeMap.wp` embeds directly into generic `Xcap.wp (bwMach cm.symEnv)`. -/
theorem CodeMap.wp_imp_xcap_wp {cm : CodeMap} {H : HaltPost} {pc : BitVec 64} {st : State}
    (h : cm.wp H pc st) : Xcap.wp (bwMach cm.symEnv) cm.lookupAddr (bwHalt H) pc st :=
  fun Ψ hcl => h Ψ (specsClosed_of_xcap_closed hcl)

/-- Operational `Xcap.Halts` over `bwMach cm.symEnv` implies `BedrockWord.Halts`. -/
theorem halts_of_xcap_halts {cm : CodeMap} {pc : BitVec 64} {st : State}
    {c : BitVec 64} {st' : State}
    (h : Xcap.Halts (bwMach cm.symEnv) cm.lookupAddr pc st c st') :
    ∃ m', Halts cm pc st c m' ∧ st'.mem = m' := by
  induction h with
  | @halt pc b s c s' hb hex =>
      dsimp [bwMach] at hex
      cases hbe : b.exec cm.symEnv (pushRegsV s.regs.toRegsV) s.mem with
      | none => simp [hbe] at hex
      | some out =>
          cases out with
          | jump _ _ => simp [hbe] at hex
          | halt c0 m0 =>
              simp [hbe] at hex
              rcases hex with ⟨rfl, rfl⟩
              exact ⟨m0, .halt ⟨b, hb, hbe⟩, rfl⟩
  | @jump pc b s pc' s' c s'' hb hex _ ih =>
      dsimp [bwMach] at hex
      cases hbe : b.exec cm.symEnv (pushRegsV s.regs.toRegsV) s.mem with
      | none => simp [hbe] at hex
      | some out =>
          cases out with
          | halt _ _ => simp [hbe] at hex
          | jump p0 st0 =>
              simp [hbe] at hex
              rcases hex with ⟨rfl, rfl⟩
              obtain ⟨m', hm', hmem⟩ := ih
              exact ⟨m', .jump ⟨b, hb, hbe⟩ hm', hmem⟩

/-- Total-correctness adequacy discharged via generic `Xcap.adequacy`. -/
theorem CodeMap.adequacy {cm : CodeMap} {H : HaltPost} {pc : BitVec 64} {st : State}
    (hwp : cm.wp H pc st) :
    ∃ code m', Halts cm pc st code m' ∧ H code m' := by
  obtain ⟨c, st', hx, hH⟩ := Xcap.adequacy (CodeMap.wp_imp_xcap_wp hwp)
  obtain ⟨m', hm', heq⟩ := halts_of_xcap_halts hx
  dsimp only [bwHalt] at hH
  rw [heq] at hH
  exact ⟨c, m', hm', hH⟩

/-- Fuel-interpreter adequacy corollary. -/
theorem CodeMap.adequacy_runFuel {cm : CodeMap} {H : HaltPost} {pc : BitVec 64} {st : State}
    (hwp : cm.wp H pc st) :
    ∃ fuel code m', runFuel cm fuel pc st = some (code, m') ∧ H code m' := by
  obtain ⟨code, m', hh, hH⟩ := cm.adequacy hwp
  obtain ⟨fuel, hf⟩ := runFuel_complete hh
  exact ⟨fuel, code, m', hf, hH⟩

/-- Non-vacuity bridge: if `(pc, st)` is stuck, then `¬ cm.wp H pc st`. -/
theorem CodeMap.not_wp_of_stuck {cm : CodeMap} {H : HaltPost} {pc : BitVec 64} {st : State}
    (hstuck : ∀ code m', ¬ Halts cm pc st code m') :
    ¬ cm.wp H pc st := by
  intro hwp
  obtain ⟨code, m', hh, _⟩ := cm.adequacy hwp
  exact hstuck code m' hh

/-! ## §2. Ranked Rules and Open-World Module Linking (via `Xcap`) -/

/-- General well-founded ranked LFP proof rule for `CodeMap.wp`. -/
theorem CodeMap.wp_of_ranked {cm : CodeMap} {H : HaltPost}
    {Measure : Type} {lt : Measure → Measure → Prop} (hwf : WellFounded lt)
    (Φ : Measure → CodeSpec)
    (hblks : ∀ (Ψ : CodeSpec) (r : Measure),
      (∀ r', lt r' r → ∀ pc st, Φ r' pc st → Ψ pc st) →
      ∀ pc st, Φ r pc st →
        ∃ b, cm.lookupAddr pc = some b ∧
          b.wp cm.symEnv Ψ H (pushRegsV st.regs.toRegsV) st.mem)
    {pc₀ : BitVec 64} {st₀ : State} {r₀ : Measure}
    (hinit : Φ r₀ pc₀ st₀) :
    cm.wp H pc₀ st₀ := by
  intro Ψ hΨ
  suffices h : ∀ r pc st, Φ r pc st → Ψ pc st from h r₀ pc₀ st₀ hinit
  intro r
  induction r using hwf.induction with
  | _ r ih =>
      intro pc st hΦ
      obtain ⟨b, hlu, hwp⟩ := hblks Ψ r ih pc st hΦ
      exact hΨ pc b hlu st hwp

/-- `Nat`-ranked LFP proof rule for `CodeMap.wp`, with a direct `Xcap.wp` companion
discharged via `Xcap.wp_of_ranked`. -/
theorem CodeMap.wp_of_ranked_nat {cm : CodeMap} {H : HaltPost}
    (Φ : Nat → CodeSpec)
    (hblks : ∀ (Ψ : CodeSpec) (n : Nat),
      (∀ n' < n, ∀ pc st, Φ n' pc st → Ψ pc st) →
      ∀ pc st, Φ n pc st →
        ∃ b, cm.lookupAddr pc = some b ∧
          b.wp cm.symEnv Ψ H (pushRegsV st.regs.toRegsV) st.mem)
    {pc₀ : BitVec 64} {st₀ : State} {n₀ : Nat}
    (hinit : Φ n₀ pc₀ st₀) :
    cm.wp H pc₀ st₀ :=
  CodeMap.wp_of_ranked Nat.lt_wfRel.wf Φ hblks hinit

/-- Direct `Xcap.wp_of_ranked` bridge for `BlockFlat` invariants. -/
theorem CodeMap.xcap_wp_of_ranked {cm : CodeMap} {H : HaltPost}
    (Φ : Nat → CodeSpec)
    (hblks : ∀ n pc st, Φ n pc st →
      ∃ b, cm.lookupAddr pc = some b ∧
        b.wp cm.symEnv (fun pc' st' => ∃ k, k < n ∧ Φ k pc' st') H
          (pushRegsV st.regs.toRegsV) st.mem)
    {pc₀ : BitVec 64} {st₀ : State} {n₀ : Nat} (hinit : Φ n₀ pc₀ st₀) :
    Xcap.wp (bwMach cm.symEnv) cm.lookupAddr (bwHalt H) pc₀ st₀ :=
  Xcap.wp_of_ranked Φ (fun n pc st h => by
    obtain ⟨b, hlu, hwp⟩ := hblks n pc st h
    exact ⟨b, hlu, bwp_of_blockFlat_wp hwp⟩) n₀ pc₀ st₀ hinit

theorem SpecsClosed.of_sub {cm₁ cm₂ : CodeMap} {ρ : SymEnv} {Ψ : CodeSpec} {H : HaltPost}
    (hsub : cm₁.Sub cm₂) (h : SpecsClosed cm₂ ρ Ψ H) : SpecsClosed cm₁ ρ Ψ H :=
  fun pc b hlu st hwp => h pc b (hsub pc b hlu) st hwp

theorem SpecsClosed.split {cm₁ cm₂ : CodeMap} {ρ : SymEnv} {Ψ : CodeSpec} {H : HaltPost}
    (hd : cm₁.AddrDisjoint cm₂) (h : SpecsClosed (cm₁ ++ cm₂) ρ Ψ H) :
    SpecsClosed cm₁ ρ Ψ H ∧ SpecsClosed cm₂ ρ Ψ H :=
  ⟨SpecsClosed.of_sub (CodeMap.sub_append_left cm₁ cm₂) h,
   SpecsClosed.of_sub (CodeMap.sub_append_right hd) h⟩

theorem SpecsClosed.link {cm₁ cm₂ : CodeMap} {ρ : SymEnv} {Ψ : CodeSpec} {H : HaltPost}
    (h₁ : SpecsClosed cm₁ ρ Ψ H) (h₂ : SpecsClosed cm₂ ρ Ψ H) :
    SpecsClosed (cm₁ ++ cm₂) ρ Ψ H := by
  intro pc b hlu st hwp
  rw [CodeMap.lookupAddr_append] at hlu
  cases hl₁ : cm₁.lookupAddr pc with
  | some b₁ =>
      rw [hl₁] at hlu; cases hlu
      exact h₁ pc b hl₁ st hwp
  | none =>
      rw [hl₁] at hlu
      exact h₂ pc b hlu st hwp

/-- Open-world ranked module verification judgment. -/
@[expose] def OpenModOk (cm : CodeMap) (H : HaltPost) (SymReq : SymEnv → Prop)
    (Imp Exp : Nat → CodeSpec) : Prop :=
  ∀ (ρ : SymEnv) (Ψ : CodeSpec) (r : Nat),
    SymEnv.Ext cm.symEnv ρ →
    SymReq ρ →
    (∀ r' < r, ∀ pc st, (Imp r' pc st ∨ Exp r' pc st) → Ψ pc st) →
    ∀ pc st, Exp r pc st →
      ∃ b, cm.lookupAddr pc = some b ∧
        b.wp ρ Ψ H (pushRegsV st.regs.toRegsV) st.mem

theorem OpenModOk.link {cm₁ cm₂ : CodeMap} {H : HaltPost}
    {SymReq₁ SymReq₂ SymReqExt : SymEnv → Prop}
    {Imp₁ Exp₁ Imp₂ Exp₂ ImpExt : Nat → CodeSpec}
    (hdisj : cm₁.Disjoint cm₂)
    (hMod₁ : OpenModOk cm₁ H SymReq₁ Imp₁ Exp₁)
    (hMod₂ : OpenModOk cm₂ H SymReq₂ Imp₂ Exp₂)
    (hSym₁ : ∀ ρ, SymEnv.Ext (cm₁ ++ cm₂).symEnv ρ → SymReqExt ρ → SymReq₁ ρ)
    (hSym₂ : ∀ ρ, SymEnv.Ext (cm₁ ++ cm₂).symEnv ρ → SymReqExt ρ → SymReq₂ ρ)
    (hImp₁ : ∀ r pc st, Imp₁ r pc st → Exp₂ r pc st ∨ ImpExt r pc st)
    (hImp₂ : ∀ r pc st, Imp₂ r pc st → Exp₁ r pc st ∨ ImpExt r pc st) :
    OpenModOk (cm₁ ++ cm₂) H SymReqExt ImpExt (fun r pc st => Exp₁ r pc st ∨ Exp₂ r pc st) := by
  intro ρ Ψ r hρ hSymE hIH pc st hExp
  have hρ₁ : SymEnv.Ext cm₁.symEnv ρ := (CodeMap.symEnv_ext_append_left cm₁ cm₂).trans hρ
  have hρ₂ : SymEnv.Ext cm₂.symEnv ρ :=
    (CodeMap.symEnv_ext_append_right hdisj.nameDisj).trans hρ
  rcases hExp with hE₁ | hE₂
  · have hIH₁ : ∀ r' < r, ∀ pc' st', (Imp₁ r' pc' st' ∨ Exp₁ r' pc' st') → Ψ pc' st' := by
      intro r' hr' pc' st' h
      rcases h with hi | he
      · rcases hImp₁ r' pc' st' hi with he₂ | hix
        · exact hIH r' hr' pc' st' (Or.inr (Or.inr he₂))
        · exact hIH r' hr' pc' st' (Or.inl hix)
      · exact hIH r' hr' pc' st' (Or.inr (Or.inl he))
    obtain ⟨b, hlu, hwp⟩ := hMod₁ ρ Ψ r hρ₁ (hSym₁ ρ hρ hSymE) hIH₁ pc st hE₁
    exact ⟨b, CodeMap.sub_append_left cm₁ cm₂ pc b hlu, hwp⟩
  · have hIH₂ : ∀ r' < r, ∀ pc' st', (Imp₂ r' pc' st' ∨ Exp₂ r' pc' st') → Ψ pc' st' := by
      intro r' hr' pc' st' h
      rcases h with hi | he
      · rcases hImp₂ r' pc' st' hi with he₁ | hix
        · exact hIH r' hr' pc' st' (Or.inr (Or.inl he₁))
        · exact hIH r' hr' pc' st' (Or.inl hix)
      · exact hIH r' hr' pc' st' (Or.inr (Or.inr he))
    obtain ⟨b, hlu, hwp⟩ := hMod₂ ρ Ψ r hρ₂ (hSym₂ ρ hρ hSymE) hIH₂ pc st hE₂
    exact ⟨b, CodeMap.sub_append_right hdisj.addrDisj pc b hlu, hwp⟩

theorem OpenModOk.close {cm : CodeMap} {H : HaltPost} {Exp : Nat → CodeSpec}
    (hMod : OpenModOk cm H (fun _ => True) (fun _ _ _ => False) Exp)
    {r₀ : Nat} {pc₀ : BitVec 64} {st₀ : State} (hinit : Exp r₀ pc₀ st₀) :
    cm.wp H pc₀ st₀ := by
  refine CodeMap.wp_of_ranked_nat Exp (fun Ψ r ih pc st hE => ?_) hinit
  exact hMod cm.symEnv Ψ r (SymEnv.Ext.refl _) trivial
    (fun r' hr' pc' st' h => h.elim False.elim (ih r' hr' pc' st')) pc st hE

/-- Embed a DAG `SpecsClosed` module into generic `Xcap.ModOk`. -/
theorem xcapModOk_of_specsClosed {cm : CodeMap} {H : HaltPost} {imps exps : Xcap.Iface State}
    (hClosed : ∀ (big : Xcap.Code BlockFlat) (Ψ : Xcap.CodeSpec State),
      Xcap.Sub cm.lookupAddr big → Xcap.Closed (bwMach cm.symEnv) big Ψ (bwHalt H) →
      (∀ e ∈ imps, Xcap.cptr Ψ e.1 (e.2 Ψ)) → ∀ e ∈ exps, Xcap.cptr Ψ e.1 (e.2 Ψ)) :
    Xcap.ModOk (bwMach cm.symEnv) cm.lookupAddr (bwHalt H) imps exps :=
  hClosed

end LeanQbe.T.BedrockWord
