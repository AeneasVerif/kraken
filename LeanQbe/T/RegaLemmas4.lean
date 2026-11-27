module

public import LeanQbe.T.RegaLemmas4Ccmp

/-!
# `RegaLemmas` Part 4: `Wf.induct` Correctness of `lowerExpr`, `lowerBlocks`, and `lowerFn`

* `LabJ`/`makeLabJs`/`DOk`/`CcmpMotive`/`CcmpJnzMotive` live in
  `RegaLemmas4Base` / `RegaLemmas4Ccmp` and are re-exported here.
* `lowerExpr_correct` by `Wf.induct`, `lowerFn_correct : ... → T.FnSpec ...`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace Rega

section Main
variable {T : Target} {host : T.mach.Host} {hints : T.toIsa.Hints} {E : Ext} {Γ : Env} {fn : Sym}
  {s₀ : T.mach.MData} {ra : T.mach.Addr} {n nX : Nat} {Rf : Mem 64 → Prop} {bound : Sym → Nat}
  {rs : List Ty} {Q : Post rs} {X : XPost}

private def defaultValTup : (ts : List Ty) → Tup Val ts
  | [] => ()
  | _ :: ts => (default, defaultValTup ts)

private def RawJumpOk (D : Ctx Cont LNat) (lo hi : Nat) (raw : Trie Nat) : Prop :=
  ∀ x y, raw.find? x = some y → lo ≤ x ∧ x < hi ∧ ∃ ts', ∃ (J' : Cont ts'), ⟨ts', J', y⟩ ∈ D

private theorem wf_jump_mem_D {G : VCtx} {D : Ctx Cont LNat} {e₁ : Expr Val Cont rs}
    {ts : List Ty} {j : Nat} {args : Tup (Arg VNat) ts}
    (h : Wf G D e₁ (.jump j args)) : ∃ ts', ∃ (J' : Cont ts'), ⟨ts', J', j⟩ ∈ D := by
  cases h with
  | jump hj _ => exact ⟨ts, _, hj⟩

private theorem blockTrampoline_target {G : VCtx} {D : Ctx Cont LNat}
    {defs : Trie DefFact} {vw : Trie SlotWidth} {lid nv ip : Nat}
    {ts : List Ty} {b₁ : Tup Val ts → Expr Val Cont rs} {b₂ : Tup VNat ts → Expr VNat LNat rs}
    (hb : ∀ xs₁ xs₂, Wf (Tup.zip xs₁ xs₂ ++ G) D (b₁ xs₁) (b₂ xs₂))
    {j' : Nat} (hbt : blockTrampoline? T.toIsa hints defs vw lid nv ip b₂ = some j') :
    ∃ ts', ∃ (J' : Cont ts'), ⟨ts', J', j'⟩ ∈ D := by
  unfold blockTrampoline? at hbt
  cases hen : hints.entry.find? lid with
  | none => simp [hen] at hbt
  | some en =>
    rw [hen] at hbt; dsimp only at hbt
    by_cases hsc : entryScopeOk nv en = true
    · simp only [hsc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hbt
      cases hbe : buildEntryBaseZ T.toIsa hints.nslots vw en.live en.liveZ
          { regs := [], slots := .empty, defs := defs, vecWidths := vw } with
      | none => simp [hbe] at hbt
      | some baseSt =>
        rw [hbe] at hbt; dsimp only at hbt
        cases hbp : bindBlockParamsZ T.toIsa hints.nslots ts en.ploc en.plocZ nv baseSt with
        | none => simp [hbp] at hbt
        | some initSt =>
          rw [hbp] at hbt; dsimp only at hbt
          cases heqb : b₂ (Tup.levels ts nv) with
          | jump j'' args' =>
            rw [heqb] at hbt
            cases hpre : stepPre T.toIsa hints ip initSt with
            | none => simp [hpre] at hbt
            | some p1 =>
              rcases p1 with ⟨mc, st1⟩
              cases mc with
              | cons _ _ => simp [hpre] at hbt
              | nil =>
                cases hen' : hints.entry.find? j'' with
                | none => simp [hpre, hen'] at hbt
                | some en' =>
                  simp only [hpre, hen'] at hbt
                  cases hjt : jumpTargets T.toIsa args' en'.ploc with
                  | none => simp [hjt] at hbt
                  | some argTgts =>
                    rw [hjt] at hbt; dsimp only at hbt
                    split at hbt; · simp at hbt
                    cases hsh : shuffle T.toIsa hints.nslots hints.saved st1
                        (en'.live ++ argTgts) with
                    | none => simp [hsh] at hbt
                    | some p2 =>
                      rcases p2 with ⟨sc, st2⟩
                      cases sc with
                      | cons _ _ => simp [hsh] at hbt
                      | nil =>
                        rw [hsh] at hbt; dsimp only at hbt
                        split at hbt
                        · simp only [Option.some.injEq] at hbt; subst hbt
                          have hwf := hb (defaultValTup ts) (Tup.levels ts nv)
                          rw [heqb] at hwf
                          exact wf_jump_mem_D hwf
                        · simp at hbt
          | _ => rw [heqb] at hbt; simp at hbt
    · simp [hsc] at hbt

private theorem collectRawFwds_aux {G : VCtx} {D : Ctx Cont LNat}
    {defs : Trie DefFact} {vw : Trie SlotWidth} {fwd : Trie Nat} {fwdTgts : Trie Bool} :
    ∀ {sig : List (List Ty)} {bs₁ : Blocks Val Cont rs sig} {bs₂ : Blocks VNat LNat rs sig}
      (_hbs : WfB G D bs₁ bs₂) (lo lid nv nl ip : Nat) (_hle : lo ≤ lid)
      (raw0 : Trie Nat) (lids0 : List Nat),
    RawJumpOk D lo lid raw0 →
    (∀ x ∈ lids0, lo ≤ x ∧ x < lid ∧ (raw0.find? x).isSome = true ∧
      (fwd.find? x).isNone = true ∧ fwdTgts.find? x ≠ some true) →
    (∀ x, (raw0.find? x).isSome = true → x ∈ lids0) →
    lids0.Nodup →
    let res := collectRawFwds T.toIsa hints defs vw fwd fwdTgts bs₂ lid nv nl ip raw0 lids0
    RawJumpOk D lo (lid + sig.length) res.1 ∧
    (∀ x ∈ res.2, lo ≤ x ∧ x < lid + sig.length ∧ (res.1.find? x).isSome = true ∧
      (fwd.find? x).isNone = true ∧ fwdTgts.find? x ≠ some true) ∧
    (∀ x, (res.1.find? x).isSome = true → x ∈ res.2) ∧
    res.2.Nodup
  | _, .nil, .nil, _, lo, lid, _, _, _, _, raw0, lids0, hR0, hL0, hM0, hNd => by
    refine ⟨?_, ?_, ?_, hNd⟩ <;> simp only [collectRawFwds, List.length_nil, Nat.add_zero]
    · exact hR0
    · exact hL0
    · exact hM0
  | ts0 :: sig, .cons b₁ bs₁, .cons b₂ bs₂, .cons hb0 hbs', lo, lid, nv, nl, ip, hle,
      raw0, lids0, hR0, hL0, hM0, hNd => by
    dsimp only [collectRawFwds]
    have hnotin : lid ∉ lids0 := fun hm => absurd (hL0 lid hm).2.1 (Nat.lt_irrefl _)
    let p1 : Trie Nat × List Nat :=
      if (fwd.find? lid).isNone && !(fwdTgts.getD lid false) then
        match blockTrampoline? T.toIsa hints defs vw lid nv ip b₂ with
        | some j' => (raw0.insert lid j', lid :: lids0)
        | none => (raw0, lids0)
      else (raw0, lids0)
    have hR1 : RawJumpOk D lo (lid + 1) p1.1 ∧
        (∀ x ∈ p1.2, lo ≤ x ∧ x < lid + 1 ∧ (p1.1.find? x).isSome = true ∧
          (fwd.find? x).isNone = true ∧ fwdTgts.find? x ≠ some true) ∧
        (∀ x, (p1.1.find? x).isSome = true → x ∈ p1.2) ∧ p1.2.Nodup := by
      dsimp only [p1]
      split
      · rename_i hgd
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hgd
        have hft : fwdTgts.find? lid ≠ some true := fun h => by
          simp [Trie.getD, h] at hgd
        cases hbt : blockTrampoline? T.toIsa hints defs vw lid nv ip b₂ with
        | none =>
          refine ⟨fun x y hx => have ⟨h1, h2, h3⟩ := hR0 x y hx; ⟨h1, by omega, h3⟩,
            fun x hx => have ⟨h1, h2, h3⟩ := hL0 x hx; ⟨h1, by omega, h3⟩, hM0, hNd⟩
        | some j' =>
          refine ⟨?_, ?_, ?_, List.nodup_cons.mpr ⟨hnotin, hNd⟩⟩
          · intro x y hx
            by_cases hxl : x = lid
            · subst hxl; rw [Trie.find?_insert_self] at hx; cases hx
              exact ⟨hle, Nat.lt_succ_self _, blockTrampoline_target (T := T) hb0 hbt⟩
            · rw [Trie.find?_insert_ne _ _ hxl] at hx
              have ⟨h1, h2, h3⟩ := hR0 x y hx; exact ⟨h1, by omega, h3⟩
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx'
            · exact ⟨hle, Nat.lt_succ_self _, by simp [Trie.find?_insert_self], hgd.1, hft⟩
            · have ⟨h1, h2, h3, h4, h5⟩ := hL0 x hx'
              have hne : x ≠ lid := Nat.ne_of_lt h2
              exact ⟨h1, by omega, by simpa [Trie.find?_insert_ne _ _ hne] using h3, h4, h5⟩
          · intro x hx
            by_cases hxl : x = lid
            · subst hxl; exact List.mem_cons_self
            · rw [Trie.find?_insert_ne _ _ hxl] at hx
              exact List.mem_cons_of_mem _ (hM0 x hx)
      · exact ⟨fun x y hx => have ⟨h1, h2, h3⟩ := hR0 x y hx; ⟨h1, by omega, h3⟩,
          fun x hx => have ⟨h1, h2, h3⟩ := hL0 x hx; ⟨h1, by omega, h3⟩, hM0, hNd⟩
    rcases hcnt : exprIpCount (b₂ (Tup.levels ts0 nv)) (nv + ts0.length) nl with ⟨nv1, nl1, d⟩
    have ih := collectRawFwds_aux (defs := defs) (vw := vw) (fwd := fwd) (fwdTgts := fwdTgts)
      hbs' lo (lid + 1) nv1 nl1 (ip + d) (by omega) p1.1 p1.2
      hR1.1 hR1.2.1 hR1.2.2.1 hR1.2.2.2
    have hlen : lid + 1 + sig.length = lid + (ts0 :: sig).length := by
      simp [List.length_cons]; omega
    rw [← hlen]
    exact ih

private theorem foldGroupFwds_inv {lo hi : Nat} {raw fwd : Trie Nat} {fwdTgts : Trie Bool}
    (hFb0 : FwdBound lo fwd fwdTgts) :
    ∀ (xs : List Nat) (f : Trie Nat) (ft : Trie Bool),
    FwdBound hi f ft →
    (∀ x < lo, f.find? x = fwd.find? x) →
    (∀ x, lo ≤ x → (f.find? x).isSome = true → x < hi ∧ (raw.find? x).isSome = true) →
    (∀ x y, lo ≤ x → f.find? x = some y →
      ∃ fuel, resolveTrampoline raw fwd fuel x = some y ∧ raw.find? y = none ∧
        fwd.find? y = none ∧ y ≠ x) →
    (∀ x ∈ xs, lo ≤ x ∧ x < hi ∧ (raw.find? x).isSome = true ∧
      f.find? x = none ∧ ft.find? x ≠ some true) →
    xs.Nodup →
    let res := xs.foldl
      (fun (p : Trie Nat × Trie Bool) lid =>
        match resolveTrampoline raw fwd (hi - lo + 1) lid with
        | some m =>
          if (raw.find? m).isNone && (fwd.find? m).isNone && m != lid then
            (p.1.insert lid m, p.2.insert m true)
          else p
        | none => p)
      (f, ft)
    FwdBound hi res.1 res.2 ∧
    (∀ x < lo, res.1.find? x = fwd.find? x) ∧
    (∀ x, lo ≤ x → (res.1.find? x).isSome = true → x < hi ∧ (raw.find? x).isSome = true) ∧
    (∀ x y, lo ≤ x → res.1.find? x = some y →
      ∃ fuel, resolveTrampoline raw fwd fuel x = some y ∧ raw.find? y = none ∧
        fwd.find? y = none ∧ y ≠ x)
  | [], f, ft, hFb, hEq, hRaw, hRes, _, _ => ⟨hFb, hEq, hRaw, hRes⟩
  | lid :: xs, f, ft, hFb, hEq, hRaw, hRes, hXs, hNd => by
    have ⟨hlo, hhi, hrawL, hfL, hftL⟩ := hXs lid List.mem_cons_self
    have hNd' := (List.nodup_cons.mp hNd)
    dsimp only [List.foldl]
    cases hres : resolveTrampoline raw fwd (hi - lo + 1) lid with
    | none =>
      exact foldGroupFwds_inv hFb0 xs f ft hFb hEq hRaw hRes
        (fun x hx => hXs x (List.mem_cons_of_mem _ hx)) hNd'.2
    | some m =>
      dsimp only
      by_cases hgd : ((raw.find? m).isNone && (fwd.find? m).isNone && m != lid) = true
      · simp only [hgd, ↓reduceIte]
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, bne_iff_ne] at hgd
        obtain ⟨⟨hrm, hfm⟩, hml⟩ := hgd
        have hf_m : f.find? m = none := by
          cases hcm : f.find? m with
          | none => rfl
          | some _ =>
            by_cases hmlo : m < lo
            · rw [hEq m hmlo, hfm] at hcm; cases hcm
            · have := (hRaw m (by omega) (by simp [hcm])).2
              rw [hrm] at this; cases this
        have hFb' : FwdBound hi (f.insert lid m) (ft.insert m true) := by
          refine ⟨fun x y hx => ?_, fun x hx => ?_⟩
          · by_cases hxl : x = lid
            · subst hxl; rw [Trie.find?_insert_self] at hx; cases hx
              exact ⟨hhi, by rw [Trie.find?_insert_ne _ _ hml]; exact hf_m,
                Trie.find?_insert_self _ _ _⟩
            · rw [Trie.find?_insert_ne _ _ hxl] at hx
              have ⟨hxhi, hfy, hfty⟩ := hFb.1 x y hx
              have hyl : y ≠ lid := fun he => hftL (he ▸ hfty)
              refine ⟨hxhi, by rw [Trie.find?_insert_ne _ _ hyl]; exact hfy, ?_⟩
              by_cases hym : y = m
              · subst hym; exact Trie.find?_insert_self _ _ _
              · rw [Trie.find?_insert_ne _ _ hym]; exact hfty
          · by_cases hxm : x = m
            · subst hxm; rw [Trie.find?_insert_ne _ _ hml]; exact hf_m
            · rw [Trie.find?_insert_ne _ _ hxm] at hx
              have hfx := hFb.2 x hx
              have hxl : x ≠ lid := fun he => hftL (he ▸ hx)
              rw [Trie.find?_insert_ne _ _ hxl]; exact hfx
        have hEq' : ∀ x < lo, (f.insert lid m).find? x = fwd.find? x := fun x hx => by
          rw [Trie.find?_insert_ne _ _ (by omega), hEq x hx]
        have hRaw' : ∀ x, lo ≤ x → ((f.insert lid m).find? x).isSome = true →
            x < hi ∧ (raw.find? x).isSome = true := fun x hx hsm => by
          by_cases hxl : x = lid
          · subst hxl; exact ⟨hhi, hrawL⟩
          · rw [Trie.find?_insert_ne _ _ hxl] at hsm; exact hRaw x hx hsm
        have hRes' : ∀ x y, lo ≤ x → (f.insert lid m).find? x = some y →
            ∃ fuel, resolveTrampoline raw fwd fuel x = some y ∧ raw.find? y = none ∧
              fwd.find? y = none ∧ y ≠ x := fun x y hx hxy => by
          by_cases hxl : x = lid
          · subst hxl; rw [Trie.find?_insert_self] at hxy; cases hxy
            exact ⟨hi - lo + 1, hres, hrm, hfm, hml⟩
          · rw [Trie.find?_insert_ne _ _ hxl] at hxy; exact hRes x y hx hxy
        have hXs' : ∀ x ∈ xs, lo ≤ x ∧ x < hi ∧ (raw.find? x).isSome = true ∧
            (f.insert lid m).find? x = none ∧ (ft.insert m true).find? x ≠ some true :=
          fun x hx => by
          have ⟨h1, h2, h3, h4, h5⟩ := hXs x (List.mem_cons_of_mem _ hx)
          have hxl : x ≠ lid := fun he => hNd'.1 (he ▸ hx)
          have hxm : x ≠ m := fun he => by subst he; rw [hrm] at h3; cases h3
          exact ⟨h1, h2, h3, by rw [Trie.find?_insert_ne _ _ hxl]; exact h4,
            by rw [Trie.find?_insert_ne _ _ hxm]; exact h5⟩
        exact foldGroupFwds_inv hFb0 xs _ _ hFb' hEq' hRaw' hRes' hXs' hNd'.2
      · have hngd : ((raw.find? m).isNone && (fwd.find? m).isNone && m != lid) = false :=
          Bool.eq_false_iff.mpr hgd
        simp only [hngd, Bool.false_eq_true, ↓reduceIte]
        exact foldGroupFwds_inv hFb0 xs f ft hFb hEq hRaw hRes
          (fun x hx => hXs x (List.mem_cons_of_mem _ hx)) hNd'.2

private theorem resolveTrampoline_step_mem {G : VCtx} {D D' : Ctx Cont LNat}
    {raw fwd fwd' : Trie Nat}
    {lo hi : Nat} (hRaw : RawJumpOk D' lo hi raw)
    (hMem : ∀ ts' (J' : Cont ts') y, ⟨ts', J', y⟩ ∈ D' → y < lo →
      ∃ ts'', ∃ (J'' : Cont ts''), ⟨ts'', J'', y⟩ ∈ D)
    (hSc' : DScope hi D') (hD : DOk T host hints E fn s₀ ra n nX Rf Q X fwd G D)
    (hnl : ∀ i, i < hi - lo → fwd'.find? (lo + i) = none →
      ∃ k : Nat, (T.mach.prog host)[k]? = some (T.frame.label (lname fn (lo + i))))
    (hNoNew : ∀ x, lo ≤ x → raw.find? x = none → fwd'.find? x = none)
    (hNoFwd : ∀ x, lo ≤ x → fwd.find? x = none) :
    ∀ (fuel : Nat) (cur m : Nat),
      (∃ ts', ∃ (J' : Cont ts'), ⟨ts', J', cur⟩ ∈ D') →
      resolveTrampoline raw fwd fuel cur = some m →
      ∃ k : Nat, (T.mach.prog host)[k]? = some (T.frame.label (lname fn m))
  | 0, _, _, _, hres => by simp [resolveTrampoline] at hres
  | fuel + 1, cur, m, hcur, hres => by
    simp only [resolveTrampoline] at hres
    cases hrc : raw.find? cur with
    | some nxt =>
      rw [hrc] at hres
      obtain ⟨_, _, ts', J', hnxt⟩ := hRaw cur nxt hrc
      exact resolveTrampoline_step_mem hRaw hMem hSc' hD hnl hNoNew hNoFwd fuel nxt m
        ⟨ts', J', hnxt⟩ hres
    | none =>
      rw [hrc] at hres; simp only [Option.some.injEq] at hres
      by_cases hclo : cur < lo
      · obtain ⟨ts', J', hcd⟩ := hcur
        obtain ⟨ts'', J'', hcD⟩ := hMem ts' J' cur hcd hclo
        have hk := (hD ts'' J'' cur hcD).1
        rwa [show tgtLab fwd cur = m from by simpa [tgtLab] using hres] at hk
      · have hfc := hNoFwd cur (by omega)
        have hmc : cur = m := by simpa [Trie.getD, hfc] using hres
        subst hmc
        obtain ⟨ts', J', hcd⟩ := hcur
        have hhi := hSc' ts' J' cur hcd
        have hf'c := hNoNew cur (by omega) hrc
        obtain ⟨k, hk⟩ := hnl (cur - lo) (by omega)
          (by simpa [show lo + (cur - lo) = cur by omega] using hf'c)
        exact ⟨k, by simpa [show lo + (cur - lo) = cur by omega] using hk⟩


private theorem lowerExpr_group_ok (hy : Hyps T host hints E Γ s₀ n nX bound) {G : VCtx}
    {D : Ctx Cont LNat} {sig : List (List Ty)}
    {b₁ : Tup Cont sig → Blocks Val Cont rs sig}
    {b₂ : Tup LNat sig → Blocks VNat LNat rs sig}
    {k₁ : Tup Cont sig → Expr Val Cont rs}
    {k₂ : Tup LNat sig → Expr VNat LNat rs}
    (hb : ∀ (ls₁ : Tup Cont sig) (ls₂ : Tup LNat sig),
      WfB G (Tup.zip ls₁ ls₂ ++ D) (b₁ ls₁) (b₂ ls₂))
    (ihb : ∀ (ls₁ : Tup Cont sig) (ls₂ : Tup LNat sig) {ts} (i : Member ts sig)
      (xs₁ : Tup Val ts) (xs₂ : Tup VNat ts),
      Motive T host hints E Γ fn s₀ ra n nX Rf Q X (Tup.zip xs₁ xs₂ ++ G) (Tup.zip ls₁ ls₂ ++ D)
        ((b₁ ls₁).get i xs₁) ((b₂ ls₂).get i xs₂))
    (ihk : ∀ (ls₁ : Tup Cont sig) (ls₂ : Tup LNat sig),
      Motive T host hints E Γ fn s₀ ra n nX Rf Q X G (Tup.zip ls₁ ls₂ ++ D)
        (k₁ ls₁) (k₂ ls₂)) :
    Motive T host hints E Γ fn s₀ ra n nX Rf Q X G D (.group (sig := sig) b₁ k₁)
      (.group b₂ k₂) := by
  intro nv nl ip st ft fwd fwdTgts c nv' nl' ip' k s σ m hl hc hft hFb hSc hD hA hM hI hwp
  simp only [lowerExpr] at hl
  split at hl; · simp at hl
  rename_i ck nv1 nl1 ip1 hlk
  obtain ⟨cb, hpb, rfl⟩ := prepend_ok hl
  obtain ⟨hck, hcb⟩ := List.IsInfixAt.append hc
  let fwdRes := findGroupFwds T.toIsa hints st (b₂ (Tup.levels sig nl)) (k₂ (Tup.levels sig nl))
    nv nl ip fwd fwdTgts
  let fwd' := fwdRes.1
  let tgts' := fwdRes.2
  have hnl1 : nl + sig.length ≤ nl1 := (lowerExpr_nv_le hlk).2
  have hlabs := lowerBlocks_labelPos (prog := T.mach.prog host) (b₂ (Tup.levels sig nl))
    nl nv1 nl1 ip1 st.defs st.vecWidths ft fwd' tgts' cb nv' nl' ip' _ hpb hcb
  let D_pre :=
    Tup.zip (makeLabJs T host hints E fn s₀ ra n nX Rf Q X fwd' G sig nl) (Tup.levels sig nl) ++ D
  have hSc' : DScope (nl + sig.length) D_pre := DScope_makeLabJs sig nl hSc
  let hcnt := exprIpCount (k₂ (Tup.levels sig nl)) nv (nl + sig.length)
  have hRawLids := collectRawFwds_aux (T := T) (hints := hints) (defs := st.defs)
    (vw := st.vecWidths) (fwd := fwd) (fwdTgts := fwdTgts)
    (hb (makeLabJs T host hints E fn s₀ ra n nX Rf Q X fwd' G sig nl) (Tup.levels sig nl))
    nl nl hcnt.1 hcnt.2.1 (ip + hcnt.2.2) (Nat.le_refl _) .empty []
    (fun _ _ h => by simp at h) (fun _ h => by cases h) (fun _ h => by simp at h) List.nodup_nil
  let rawLids := collectRawFwds T.toIsa hints st.defs st.vecWidths fwd fwdTgts
    (b₂ (Tup.levels sig nl)) nl hcnt.1 hcnt.2.1 (ip + hcnt.2.2) .empty []
  have hFold := foldGroupFwds_inv (raw := rawLids.1) hFb rawLids.2 fwd fwdTgts
    (hFb.mono (Nat.le_add_right _ _)) (fun _ _ => rfl)
    (fun x hx hsm => by
      cases hfx : fwd.find? x with
      | none => simp [hfx] at hsm
      | some _ => exact absurd (hFb.1 x _ hfx).1 (Nat.not_lt.mpr hx))
    (fun x y hx hxy => absurd (hFb.1 x y hxy).1 (Nat.not_lt.mpr hx))
    (fun x hx => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hRawLids.2.1 x hx
      exact ⟨h1, by simpa [Nat.add_sub_cancel_left] using h2, h3,
        by cases hfx : fwd.find? x with
           | none => rfl
           | some _ => exact absurd (hFb.1 x _ hfx).1 (Nat.not_lt.mpr h1), h5⟩)
    hRawLids.2.2.2
  have hFold' : FwdBound (nl + sig.length) fwd' tgts' ∧
      (∀ x < nl, fwd'.find? x = fwd.find? x) ∧
      (∀ x, nl ≤ x → (fwd'.find? x).isSome = true →
        x < nl + sig.length ∧ (rawLids.1.find? x).isSome = true) ∧
      (∀ x y, nl ≤ x → fwd'.find? x = some y →
        ∃ fuel, resolveTrampoline rawLids.1 fwd fuel x = some y ∧ rawLids.1.find? y = none ∧
          fwd.find? y = none ∧ y ≠ x) := by
    have hSub : nl + sig.length - nl = sig.length := Nat.add_sub_cancel_left _ _
    rw [hSub] at hFold
    exact hFold
  have hFb' : FwdBound (nl + sig.length) fwd' tgts' := hFold'.1
  have hEq' : ∀ x < nl, fwd'.find? x = fwd.find? x := hFold'.2.1
  have hRaw' : ∀ x, nl ≤ x → (fwd'.find? x).isSome = true →
      x < nl + sig.length ∧ (rawLids.1.find? x).isSome = true := hFold'.2.2.1
  have hRes' : ∀ x y, nl ≤ x → fwd'.find? x = some y →
      ∃ fuel, resolveTrampoline rawLids.1 fwd fuel x = some y ∧ rawLids.1.find? y = none ∧
        fwd.find? y = none ∧ y ≠ x := hFold'.2.2.2
  have hNoNew : ∀ x, nl ≤ x → rawLids.1.find? x = none → fwd'.find? x = none := fun x hx hrx => by
    cases hfx : fwd'.find? x with
    | none => rfl
    | some _ => have hsm := (hRaw' x hx (by simp [hfx])).2; rw [hrx] at hsm; cases hsm
  have hD_orig_upd : DOk T host hints E fn s₀ ra n nX Rf Q X fwd' G D := DOk_fwd_mono hSc hEq' hD
  have hMem_pre : ∀ ts' (J' : Cont ts') y, ⟨ts', J', y⟩ ∈ D_pre → y < nl →
      ∃ ts'', ∃ (J'' : Cont ts''), ⟨ts'', J'', y⟩ ∈ D := fun ts' J' y hy hylo => by
    rcases List.mem_append.mp hy with h1 | h2
    · have hge : ∀ (sig0 : List (List Ty)) (nl0 : Nat),
          ⟨ts', J', y⟩ ∈ Tup.zip (makeLabJs T host hints E fn s₀ ra n nX Rf Q X fwd' G sig0 nl0)
            (Tup.levels sig0 nl0) → nl0 ≤ y := by
        intro sig0
        induction sig0 with
        | nil => intro nl0 h0; simp [Tup.zip] at h0
        | cons _ sig0 ih =>
          intro nl0 h0
          simp only [makeLabJs, Tup.levels, Tup.zip, List.mem_cons] at h0
          rcases h0 with hhd | htl
          · cases hhd; exact Nat.le_refl _
          · exact Nat.le_trans (Nat.le_succ _) (ih (nl0 + 1) htl)
      exact absurd (hge sig nl h1) (Nat.not_le.mpr hylo)
    · exact ⟨ts', J', h2⟩
  have hLabSig : ∀ i, i < sig.length →
      ∃ k : Nat, (T.mach.prog host)[k]? =
        some (T.frame.label (lname fn (tgtLab fwd' (nl + i)))) := by
    intro i hi
    cases hfx : fwd'.find? (nl + i) with
    | none => simpa [tgtLab, Trie.getD, hfx] using hlabs.1 i hi hfx
    | some m =>
      obtain ⟨fuel, hres, -, -, hne⟩ := hRes' (nl + i) m (Nat.le_add_right _ _) hfx
      have hNoFwd' : ∀ x, nl ≤ x → fwd.find? x = none := fun x hx => by
        cases h : fwd.find? x with
        | none => rfl
        | some _ => exact absurd (hFb.1 x _ h).1 (Nat.not_lt.mpr hx)
      cases fuel with
      | zero => simp [resolveTrampoline] at hres
      | succ fuel' =>
        simp only [resolveTrampoline] at hres
        cases hrc : rawLids.1.find? (nl + i) with
        | none =>
          rw [hrc] at hres
          have hf0 : fwd.find? (nl + i) = none := hNoFwd' (nl + i) (Nat.le_add_right _ _)
          have heqm : nl + i = m := by simpa [Trie.getD, hf0] using hres
          exact absurd heqm.symm hne
        | some nxt =>
          rw [hrc] at hres
          obtain ⟨_, _, ts', J', hnxt⟩ := hRawLids.1 (nl + i) nxt hrc
          have hstep := resolveTrampoline_step_mem (T := T) (host := host) (hints := hints)
            (E := E) (fn := fn) (s₀ := s₀) (ra := ra) (n := n) (nX := nX) (Rf := Rf)
            (Q := Q) (X := X) (G := G) hRawLids.1 hMem_pre hSc' hD
            (fun j hj hfj => hlabs.1 j (by omega) hfj)
            hNoNew hNoFwd' fuel' nxt m ⟨ts', J', hnxt⟩ hres
          simpa [tgtLab, Trie.getD, hfx] using hstep
  have hD' : DOk T host hints E fn s₀ ra n nX Rf Q X fwd' G D_pre :=
    makeLabJs_dok sig nl hLabSig hD_orig_upd
  have hnv1 : nv ≤ nv1 := (lowerExpr_nv_le hlk).1
  have hClosed := lowerBlocks_closed hy hD' hA (hb _ (Tup.levels sig nl))
    (fun i xs₁ xs₂ => ihb _ (Tup.levels sig nl) i xs₁ xs₂) nl nv1 nl1 ip1 ft
    cb nv' nl' ip' (k + ck.length) hnv1 (hFb'.mono hnl1) (hSc'.mono hnl1) hpb hcb
    (FT_congr (by simp [Nat.add_assoc]) hft)
  simp only [wp] at hwp
  refine ihk _ (Tup.levels sig nl) nv (nl + sig.length) ip st
    (firstNonFwd fwd' (b₂ (Tup.levels sig nl)) nl ft) fwd' tgts' ck nv1 nl1 ip1 k s σ m
    hlk hck ?_ hFb' hSc' hD' hA hM hI (hwp _ hClosed)
  exact hlabs.2 (fun j hj => by simpa [Nat.add_assoc] using hft j hj)

private theorem ccmpChain_none {G : VCtx} {D : Ctx Cont LNat}
    {e₁ : Expr Val Cont rs} {e₂ : Expr VNat LNat rs}
    (h : ∀ nv nl ip st br targetJ ipEx ft fwd tgts res,
      lowerCcmpChain T.toIsa hints E fn e₂ nv nl ip st br targetJ ipEx ft fwd tgts ≠ .ok res) :
    CcmpMotive T host hints E Γ fn s₀ ra n nX Rf Q X G D e₁ e₂ :=
  fun nv nl ip st br targetJ ipEx ft fwd tgts c nv' nl' ip' _ _ _ _ _ hl =>
    absurd hl (h nv nl ip st br targetJ ipEx ft fwd tgts (c, nv', nl', ip'))

private theorem ccmpJnz_none {G : VCtx} {D : Ctx Cont LNat}
    {e₁ : Expr Val Cont rs} {e₂ : Expr VNat LNat rs}
    (h : ∀ nv nl ipJnz st br targetJ ipEx ft fwd tgts reqCx co {w} (a b : Arg VNat (.bits w)) res,
      lowerCcmpJnz T.toIsa hints E fn e₂ nv nl ipJnz st br targetJ ipEx ft fwd tgts reqCx co a b ≠
        .ok res) :
    CcmpJnzMotive T host hints E Γ fn s₀ ra n nX Rf Q X G D e₁ e₂ :=
  fun nv nl ipJnz st br targetJ ipEx ft fwd tgts reqCx co _ _ _ a b c nv' nl' ip'
      _ _ _ _ _ hl =>
    absurd hl (h nv nl ipJnz st br targetJ ipEx ft fwd tgts reqCx co a b (c, nv', nl', ip'))

/-- Main theorem: `Wf.induct` correctness of `lowerExpr` (all ten `Expr` forms). -/
theorem lowerExpr_correct (hy : Hyps T host hints E Γ s₀ n nX bound) {G : VCtx} {D : Ctx Cont LNat}
    {e₁ : Expr Val Cont rs} {e₂ : Expr VNat LNat rs} (hwf : Wf G D e₁ e₂) :
    Motive T host hints E Γ fn s₀ ra n nX Rf Q X G D e₁ e₂ := by
  refine (Wf.induct
    (motive := fun G D e₁ e₂ _ =>
      Motive T host hints E Γ fn s₀ ra n nX Rf Q X G D e₁ e₂ ∧
      CcmpMotive T host hints E Γ fn s₀ ra n nX Rf Q X G D e₁ e₂ ∧
      CcmpJnzMotive T host hints E Γ fn s₀ ra n nX Rf Q X G D e₁ e₂)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hwf).1
  · -- let_
    intro G D ts op₁ op₂ k₁ k₂ hop _ ih
    refine ⟨?_, ccmpMotive_let hy hop (fun xs₁ xs₂ => (ih xs₁ xs₂).2.2),
      ccmpJnz_none (by simp [lowerCcmpJnz])⟩
    intro nv nl ip st ft fwd fwdTgts c nv' nl' ip' k s σ m hl hc hft hFb hSc hD hA hM hI hwp
    simp only [lowerExpr] at hl
    cases hp : stepPre T.toIsa hints ip st with
    | none => simp [hp] at hl
    | some p1 =>
      obtain ⟨mc, st1⟩ := p1
      cases hlop : lowerOp T.toIsa hints nv ip st1 op₂
          (deferJnzNext T.toIsa hints fn nv nl ip st1 op₂ (k₂ (Tup.levels ts nv)) ||
            deferLeaNext T.toIsa hints nv ip st1 op₂ (k₂ (Tup.levels ts nv)))
          (hints.mulHiIps.getD ip false) with
      | none => simp [hp, hlop] at hl
      | some p2 =>
        obtain ⟨co, st2⟩ := p2
        simp only [hp, hlop] at hl
        obtain ⟨ck, hlk, rfl⟩ := prepend_ok hl
        obtain ⟨hc1, hck⟩ := List.IsInfixAt.append hc
        obtain ⟨hmc, hco⟩ := List.IsInfixAt.append hc1
        simp only [wp] at hwp
        have hM1 : MemDefsOk G m nv st1.memDefs := stepPre_memDefs hp ▸ hM
        refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
        refine lowerOp_ok hy.spE hy.saved_cs hop hlop hco hA1 hM1 hI1 hwp
          fun rvs s2 hP hA2 hM2 hI2 => ?_
        refine run_congr (by simp [Nat.add_assoc])
          ((ih rvs (Tup.levels ts nv)).1 (nv + ts.length) nl
          (ip + 1) st2 ft fwd fwdTgts ck nv' nl' ip' _ s2 σ1 m hlk hck
          (FT_congr (by simp [Nat.add_assoc]) hft) hFb hSc
          (hD.weaken fun _ hp => List.mem_append_right _ hp) hA2 hM2 hI2 hP)
  · -- load
    intro G D t a₁ a₂ k₁ k₂ ha _ ih
    refine ⟨?_,
      ccmpChain_none (by simp [lowerCcmpChain]),
      ccmpJnz_none (by simp [lowerCcmpJnz])⟩
    intro nv nl ip st ft fwd fwdTgts c nv' nl' ip' k s σ m hl hc hft hFb hSc hD hA hM hI hwp
    simp only [lowerExpr] at hl
    cases hp : stepPre T.toIsa hints ip st with
    | none => simp [hp] at hl
    | some p1 =>
      obtain ⟨mc, st1⟩ := p1
      cases hll : lowerLoad T.toIsa hints nv ip st1 t a₂
          (loadSextNext T.toIsa hints nv ip st1 t a₂ (k₂ nv)) with
      | none => simp [hp, hll] at hl
      | some p2 =>
        obtain ⟨co, st2⟩ := p2
        simp only [hp, hll] at hl
        obtain ⟨ck, hlk, rfl⟩ := prepend_ok hl
        obtain ⟨hc1, hck⟩ := List.IsInfixAt.append hc
        obtain ⟨hmc, hco⟩ := List.IsInfixAt.append hc1
        simp only [wp] at hwp
        obtain ⟨v, hv, hwk⟩ := hwp
        have hM1 : MemDefsOk G m nv st1.memDefs := stepPre_memDefs hp ▸ hM
        refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
        refine lowerLoad_ok hy.spE hy.saved_cs ha hll hco hA1 hM1 hI1 hv fun s2 hA2 hM2 hI2 => ?_
        refine run_congr (by simp [Nat.add_assoc]) ((ih v nv).1 (nv + 1) nl (ip + 1) st2 ft
          fwd fwdTgts ck nv' nl' ip' _ s2 σ1 m hlk hck (FT_congr (by simp [Nat.add_assoc]) hft)
          hFb hSc (hD.weaken fun _ hp => List.mem_cons_of_mem _ hp) hA2 hM2 hI2 hwk)
  · -- store
    intro G D t v₁ v₂ a₁ a₂ k₁ k₂ hv ha _ ih
    refine ⟨?_,
      ccmpChain_none (by simp [lowerCcmpChain]),
      ccmpJnz_none (by simp [lowerCcmpJnz])⟩
    intro nv nl ip st ft fwd fwdTgts c nv' nl' ip' k s σ m hl hc hft hFb hSc hD hA hM hI hwp
    simp only [lowerExpr] at hl
    cases hp : stepPre T.toIsa hints ip st with
    | none => simp [hp] at hl
    | some p1 =>
      obtain ⟨mc, st1⟩ := p1
      cases hls : lowerStore T.toIsa st1 (hints.variant.getD ip .default) t v₂ a₂ with
      | none => simp [hp, hls] at hl
      | some p2 =>
        obtain ⟨co, st2⟩ := p2
        simp only [hp, hls] at hl
        obtain ⟨ck, hlk, rfl⟩ := prepend_ok hl
        obtain ⟨hc1, hck⟩ := List.IsInfixAt.append hc
        obtain ⟨hmc, hco⟩ := List.IsInfixAt.append hc1
        simp only [wp] at hwp
        have hM1 : MemDefsOk G m nv st1.memDefs := stepPre_memDefs hp ▸ hM
        refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
        refine lowerStore_ok hy.spE hv ha hls hco hA1 hM1 hI1 hwp.1 fun s2 hA2 hM2 hI2 => ?_
        refine run_congr (by simp [Nat.add_assoc]) (ih.1 nv nl (ip + 1) st2 ft fwd fwdTgts ck
          nv' nl' ip' _ s2 σ1 _ hlk hck (FT_congr (by simp [Nat.add_assoc]) hft)
          hFb hSc hD hA2 hM2 hI2 hwp.2)
  · -- call
    intro G D f as bs args₁ args₂ k₁ k₂ hargs _ ih
    refine ⟨?_,
      ccmpChain_none (by simp [lowerCcmpChain]),
      ccmpJnz_none (by simp [lowerCcmpJnz])⟩
    intro nv nl ip st ft fwd fwdTgts c nv' nl' ip' k s σ m hl hc hft hFb hSc hD hA _hM hI hwp
    simp only [lowerExpr] at hl
    cases hp : stepPre T.toIsa hints ip st with
    | none => simp [hp] at hl
    | some p1 =>
      obtain ⟨mc, st1⟩ := p1
      simp only [hp] at hl
      split at hl; · simp at hl
      rename_i hcal
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hcal
      cases hal : T.toIsa.assignArgs as with
      | none => simp [hal] at hl
      | some argLocs =>
        cases hrl : T.toIsa.assignRets bs with
        | none => simp [hal, hrl] at hl
        | some retLocs =>
          simp only [hal, hrl] at hl
          cases htg : abiTargets T.toIsa args₂ argLocs with
          | none => simp [htg] at hl
          | some tgts =>
            cases hsh : shuffle T.toIsa hints.nslots hints.saved st1 tgts
                (hints.deadFlags.getD ip false) with
            | none => simp [htg, hsh] at hl
            | some p2 =>
              obtain ⟨sc, st2⟩ := p2
              cases hb :
                  bindAbiParams T.toIsa retLocs nv (afterCallState T.toIsa hints.saved st2) with
              | none => simp [htg, hsh, hb] at hl
              | some st4 =>
                simp only [htg, hsh, hb] at hl
                obtain ⟨ck, hlk, rfl⟩ := prepend_ok hl
                obtain ⟨hc1, hck⟩ := List.IsInfixAt.append hc
                simp only [List.append_assoc] at hc1
                obtain ⟨hmc, hc2⟩ := List.IsInfixAt.append hc1
                obtain ⟨hsc, hcc⟩ := List.IsInfixAt.append hc2
                simp only [wp] at hwp
                obtain ⟨P, X', hspec, hk, hX⟩ := hwp
                have hmd4 : st4.memDefs = .empty := bindAbiParams_memDefs hb
                refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
                refine shuffle_ok hy.spE hsh hsc hA1 hI1 fun s2 σ2 hok hA2 hI2 => ?_
                refine call_ok hy hargs hcal hal hrl htg hb hcc hok hA2 hI2 hspec hX
                  fun rets m' s3 σ3 hP hA3 hI3 => ?_
                refine run_congr (by simp; omega) ((ih rets (Tup.levels bs nv)).1 (nv + bs.length)
                  nl (ip + 1) st4 ft fwd fwdTgts ck nv' nl' ip' _ s3 σ3 m' hlk hck
                  (FT_congr (by simp; omega) hft) hFb hSc
                  (hD.weaken fun _ hp => List.mem_append_right _ hp) hA3
                  (hmd4 ▸ MemDefsOk.empty _ _ _) hI3 (hk rets m' hP))
  · -- jnz
    intro G D c₁ c₂ t₁ t₂ e₁ e₂ hcr ht he iht ihe
    refine ⟨?_,
      ccmpMotive_jnz hy hcr ht he ⟨iht.1, iht.2.1⟩ ⟨ihe.1, ihe.2.1⟩,
      ccmpJnzMotive_jnz hy hcr ht he ⟨iht.1, iht.2.1⟩ ⟨ihe.1, ihe.2.1⟩⟩
    intro nv nl ip st ft fwd fwdTgts c nv' nl' ip' k s σ m hl hc hft hFb hSc hD hA hM hI hwp
    cases hcr with
    | imm b =>
      simp only [lowerExpr] at hl
      cases hp : stepPre T.toIsa hints ip st with
      | none => simp [hp] at hl
      | some p1 =>
        obtain ⟨mc, st1⟩ := p1
        simp only [hp] at hl
        obtain ⟨cb, hlb, rfl⟩ := prepend_ok hl
        obtain ⟨hmc, hcb⟩ := List.IsInfixAt.append hc
        simp only [wp, Arg.val] at hwp
        have hM1 : MemDefsOk G m nv st1.memDefs := stepPre_memDefs hp ▸ hM
        refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
        have hft' : FT T host fn ft (k + mc.length + cb.length) :=
          FT_congr (by simp [Nat.add_assoc]) hft
        cases b
        · simp only [Bool.false_eq_true, ite_false] at hlb
          exact ihe.1 nv nl (ip + 1) st1 ft fwd fwdTgts cb nv' nl' ip' _ s1 σ1 m
            hlb hcb hft' hFb hSc hD hA1 hM1 hI1 (hwp.2 rfl)
        · simp only [ite_true] at hlb
          exact iht.1 nv nl (ip + 1) st1 ft fwd fwdTgts cb nv' nl' ip' _ s1 σ1 m
            hlb hcb hft' hFb hSc hD hA1 hM1 hI1 (hwp.1 rfl)
    | @var cv cx hmem =>
      simp only [lowerExpr] at hl
      cases hp : stepPre T.toIsa hints ip st with
      | none => simp [hp] at hl
      | some p1 =>
        obtain ⟨mc, st1⟩ := p1
        cases hfc : findJnzCond T.toIsa hints.nslots st1 cx with
        | none => simp [hp, hfc] at hl
        | some cond =>
          cases hstC : ccmpStart? T.toIsa hints nv nl ip st1 cond t₂ e₂ with
          | some q =>
            rcases q with ⟨c0, st0, br0, targetJ, wantTrue, ipRest, ipEx0⟩
            simp only [hp, hfc, hstC] at hl
            obtain ⟨cR, hr, rfl⟩ := prepend_ok hl
            rw [List.append_assoc] at hc hft
            obtain ⟨hmc, hcR⟩ := List.IsInfixAt.append hc
            simp only [wp, Arg.val] at hwp
            have hM1 : MemDefsOk G m nv st1.memDefs := stepPre_memDefs hp ▸ hM
            refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
            exact ccmpStart_ok hy ht he iht.2.1 ihe.2.1 hmem hfc hstC hr hcR
              (FT_congr (by simp [List.length_append, Nat.add_assoc]) hft) hFb hSc hD hA1 hM1 hI1
              hwp
          | none =>
            cases hs : jnzSetup T.toIsa hints fn nl
                (jnzIpT nv nl ip t₂ e₂) (ip + 1) st1 t₂ e₂ ft cond fwd with
            | none => simp [hp, hfc, hstC, hs] at hl
            | some q =>
              rcases q with ⟨inv, tgt, br, stBr⟩
              simp only [hp, hfc, hstC, hs] at hl
              split at hl; · simp at hl
              rename_i ce nv1 nl1 ip1 hle
              split at hl; · simp at hl
              rename_i ct nv2 nl2 ip2 hlt
              obtain ⟨cf, hfin, rfl⟩ := prepend_ok hl
              obtain ⟨hmc, hcf⟩ := List.IsInfixAt.append hc
              simp only [wp, Arg.val] at hwp
              have hleE := lowerExpr_nv_le hle
              have hnv1 : nv ≤ nv1 := hleE.1
              have hnl1 : nl + 1 ≤ nl1 := hleE.2
              have hFb1 : FwdBound (nl + 1) fwd fwdTgts := hFb.mono (Nat.le_succ _)
              have hSc1 : DScope (nl + 1) D := hSc.mono (Nat.le_succ _)
              have hFb2 : FwdBound nl1 fwd fwdTgts := hFb.mono (by omega)
              have hSc2 : DScope nl1 D := hSc.mono (by omega)
              have hMBr : MemDefsOk G m nv stBr.memDefs :=
                ((jnzSetup_memDefs hs).trans (stepPre_memDefs hp)) ▸ hM
              have hMBr1 : MemDefsOk G m nv1 stBr.memDefs :=
                hMBr.grow hnv1 (fun _ h => Or.inl h) (fun _ h => h)
              have hM1 : MemDefsOk G m nv st1.memDefs := stepPre_memDefs hp ▸ hM
              refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
              cases tgt with
              | none =>
                have hcf' := hcf
                cases inv with
                | false =>
                  simp only [Bool.false_eq_true, ite_false] at hle hlt hfin
                  obtain ⟨hcfe, rfl, rfl, rfl⟩ := finishJnzBranch_none hfin
                  rw [hcfe] at hcf' hft
                  obtain ⟨hbr, h2⟩ := List.IsInfixAt.append hcf'
                  obtain ⟨hce, h3⟩ := List.IsInfixAt.append h2
                  obtain ⟨hlab, hct⟩ := List.IsInfixAt.cons h3
                  refine branch_ok hy hmem hA1 hI1 hM1 hfc hbr hlab hs
                    fun s' hA' hI' => ⟨fun htk => ?_, fun hnt => ?_⟩
                  · refine T.frameSpec.label_spec hlab ?_
                    exact iht.1 nv1 nl1 ip1 stBr ft fwd fwdTgts ct _ _ _ _ s' σ1 m hlt hct
                      (FT_congr (by simp; omega) hft) hFb2 hSc2 hD (hA'.mono_nv hnv1) hMBr1 hI'
                      (hwp.1 (by simpa using htk))
                  · exact ihe.1 nv (nl + 1) (ip + 1) stBr none fwd fwdTgts ce nv1 nl1 ip1 _ s'
                      σ1 m hle hce (FT_none _) hFb1 hSc1 hD hA' hMBr hI'
                        (hwp.2 (by simpa using hnt))
                | true =>
                  simp only [ite_true] at hle hlt hfin
                  obtain ⟨hcfe, rfl, rfl, rfl⟩ := finishJnzBranch_none hfin
                  rw [hcfe] at hcf' hft
                  obtain ⟨hbr, h2⟩ := List.IsInfixAt.append hcf'
                  obtain ⟨hct, h3⟩ := List.IsInfixAt.append h2
                  obtain ⟨hlab, hce⟩ := List.IsInfixAt.cons h3
                  refine branch_ok hy hmem hA1 hI1 hM1 hfc hbr hlab hs
                    fun s' hA' hI' => ⟨fun htk => ?_, fun hnt => ?_⟩
                  · refine T.frameSpec.label_spec hlab ?_
                    exact ihe.1 nv (nl + 1) (ip + 1) stBr ft fwd fwdTgts ce nv1 nl1 ip1 _ s'
                      σ1 m hle hce (FT_congr (by simp; omega) hft) hFb1 hSc1 hD hA' hMBr hI'
                      (hwp.2 (by simpa using htk))
                  · exact iht.1 nv1 nl1 ip1 stBr none fwd fwdTgts ct _ _ _ _ s' σ1 m hlt hct
                      (FT_none _) hFb2 hSc2 hD (hA'.mono_nv hnv1) hMBr1 hI'
                      (hwp.1 (by simpa using hnt))
              | some j =>
                have hth := jnzSetup_thread hs
                cases inv with
                | false =>
                  simp only [Bool.false_eq_true, ite_false] at hle hlt hfin
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := finishJnzBranch_some hfin
                  obtain ⟨hbr, hce⟩ := List.IsInfixAt.append hcf
                  obtain ⟨kj, hlab, hrun⟩ := thread_ok hy ht hD (hth.1 rfl)
                  refine branch_ok hy hmem hA1 hI1 hM1 hfc hbr hlab hs
                    fun s' hA' hI' => ⟨fun htk => ?_, fun hnt => ?_⟩
                  · exact hrun (hwp.1 (by simpa using htk)) nv s' σ1 hA' hI'
                  · exact ihe.1 nv (nl + 1) (ip + 1) stBr ft fwd fwdTgts ce nv1 nl1 ip1 _ s'
                      σ1 m hle hce (FT_congr (by simp [Nat.add_assoc]) hft) hFb1 hSc1 hD hA'
                      hMBr hI' (hwp.2 (by simpa using hnt))
                | true =>
                  simp only [ite_true] at hle hlt hfin
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := finishJnzBranch_some hfin
                  obtain ⟨hbr, hct⟩ := List.IsInfixAt.append hcf
                  obtain ⟨kj, hlab, hrun⟩ := thread_ok hy he hD (hth.2 rfl)
                  refine branch_ok hy hmem hA1 hI1 hM1 hfc hbr hlab hs
                    fun s' hA' hI' => ⟨fun htk => ?_, fun hnt => ?_⟩
                  · exact hrun (hwp.2 (by simpa using htk)) nv s' σ1 hA' hI'
                  · exact iht.1 nv1 nl1 ip1 stBr ft fwd fwdTgts ct _ _ _ _ s' σ1 m hlt hct
                      (FT_congr (by simp [Nat.add_assoc]) hft) hFb2 hSc2 hD (hA'.mono_nv hnv1)
                      hMBr1 hI' (hwp.1 (by simpa using hnt))
  · -- jump
    intro G D ts j₁ j₂ args₁ args₂ hj hargs
    refine ⟨?_,
      ccmpChain_none (by simp [lowerCcmpChain]),
      ccmpJnz_none (by simp [lowerCcmpJnz])⟩
    intro nv nl ip st ft fwd fwdTgts c nv' nl' ip' k s σ m hl hc hft hFb hSc hD hA _hM hI hwp
    simp only [lowerExpr] at hl
    cases hp : stepPre T.toIsa hints ip st with
    | none => simp [hp] at hl
    | some p1 =>
      obtain ⟨mc, st1⟩ := p1
      cases hen : hints.entry.find? j₂ with
      | none => simp [hp, hen] at hl
      | some en =>
        cases hjt : jumpTargets T.toIsa args₂ en.ploc with
        | none => simp [hp, hen, hjt] at hl
        | some argTgts =>
          simp only [hp, hen, hjt] at hl
          split at hl; · simp at hl
          rename_i hlocs
          cases hsh : shuffle T.toIsa hints.nslots hints.saved st1 (en.live ++ argTgts)
              (hints.deadFlags.getD ip false) with
          | none => simp [hsh] at hl
          | some p2 =>
            obtain ⟨sc, st2⟩ := p2
            rw [hsh] at hl; dsimp only at hl
            split at hl; · simp at hl
            rename_i hez
            have hez' : entryZOk T.toIsa st2 en argTgts = true := by simpa using hez
            simp only [Except.ok.injEq, Prod.mk.injEq] at hl
            obtain ⟨rfl, -, -, -⟩ := hl
            obtain ⟨⟨kℓ, hlabℓ⟩, G', hGs, hJeq⟩ := hD ts j₁ j₂ hj
            subst hJeq
            simp only [wp] at hwp
            simp only [List.append_assoc] at hc hft
            obtain ⟨hmc, hc2⟩ := List.IsInfixAt.append hc
            obtain ⟨hsc, hc3⟩ := List.IsInfixAt.append hc2
            simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at hlocs
            refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
            refine shuffle_ok hy.spE hsh hsc hA1 hI1 fun s2 σ2 hok hA2 hI2 => ?_
            obtain ⟨hlZ, hpZ⟩ := entryZOk_ok hA2 hargs hjt hez'
            by_cases hfj : (ft == some (tgtLab fwd j₂)) = true
            · simp only [hfj, ite_true, List.append_nil] at hft hc3
              have hl0 := hft (tgtLab fwd j₂) (by simpa using hfj)
              exact enter_labJ hy hGs hargs hen hjt hok hlZ hpZ hI2
                (by simpa [Nat.add_assoc] using hl0) hwp
            · simp only [hfj, Bool.false_eq_true, ite_false] at hc3
              refine T.gprSpec.jmp_spec hc3 (labelAddr_of_unique hy.unique hlabℓ)
                fun s3 hfr hm => ?_
              have hjlLive : ∀ p ∈ en.live, ∀ r, p.2 = .gpr r → r ∉ T.frame.scratch :=
                fun p hp r hr => (jumpLocOk_spec (hlocs p (List.mem_append_left _ hp))).1 r hr
              have hjlArg : ∀ p ∈ argTgts, ∀ r, p.2 = .gpr r → r ∉ T.frame.scratch :=
                fun p hp r hr => (jumpLocOk_spec (hlocs p (List.mem_append_right _ hp))).1 r hr
              refine enter_labJ hy hGs hargs hen hjt (fun p hp => ?_)
                (LiveZOk.frame hfr (fun _ => Or.inr trivial) hjlLive hlZ)
                (paramsZOk_frame_jump hfr hjt hjlArg hpZ)
                (hI2.keep hm (keep_of_frame_scratch hfr))
                hlabℓ hwp
              have hjl := jumpLocOk_spec (hlocs p hp)
              exact LocOk.frame hfr (hok p hp) hjl.1 (fun _ _ => List.not_mem_nil)
                (fun _ _ => FlagMask.disjoint_none _)
  · -- ret
    intro G D vs₁ vs₂ hvs
    refine ⟨?_,
      ccmpChain_none (by simp [lowerCcmpChain]),
      ccmpJnz_none (by simp [lowerCcmpJnz])⟩
    intro nv nl ip st ft fwd fwdTgts c nv' nl' ip' k s σ m hl hc hft hFb hSc hD hA _hM hI hwp
    simp only [lowerExpr] at hl
    cases hp : stepPre T.toIsa hints ip st with
    | none => simp [hp] at hl
    | some p1 =>
      obtain ⟨mc, st1⟩ := p1
      cases hrl : T.toIsa.assignRets rs with
      | none => simp [hp, hrl] at hl
      | some retLocs =>
        simp only [hp, hrl, lowerTail] at hl
        cases htg : abiTargets T.toIsa vs₂ retLocs with
        | none => simp [htg] at hl
        | some tgts =>
          cases hsh : shuffle T.toIsa hints.nslots hints.saved st1 tgts
              (hints.deadFlags.getD ip false) with
          | none => simp [htg, hsh] at hl
          | some p2 =>
            obtain ⟨sc, st2⟩ := p2
            simp only [htg, hsh, Except.ok.injEq, Prod.mk.injEq] at hl
            obtain ⟨rfl, -, -, -⟩ := hl
            simp only [List.append_assoc] at hc
            obtain ⟨hmc, hc2⟩ := List.IsInfixAt.append hc
            obtain ⟨hsc, hc3⟩ := List.IsInfixAt.append hc2
            simp only [wp] at hwp
            refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
            refine shuffle_ok hy.spE hsh hsc hA1 hI1 fun s2 σ2 hok hA2 hI2 => ?_
            exact ret_ok hy hvs hrl htg (by simpa only [List.append_assoc] using hc3) hok hA2 hI2
              hwp
  · -- exit
    intro G D f as args₁ args₂ hargs
    refine ⟨?_,
      ccmpChain_none (by simp [lowerCcmpChain]),
      ccmpJnz_none (by simp [lowerCcmpJnz])⟩
    intro nv nl ip st ft fwd fwdTgts c nv' nl' ip' k s σ m hl hc hft hFb hSc hD hA _hM hI hwp
    simp only [lowerExpr] at hl
    cases hp : stepPre T.toIsa hints ip st with
    | none => simp [hp] at hl
    | some p1 =>
      obtain ⟨mc, st1⟩ := p1
      cases hal : T.toIsa.assignArgs as with
      | none => simp [hp, hal] at hl
      | some argLocs =>
        simp only [hp, hal] at hl
        split at hl; · simp at hl
        rename_i hex
        simp only [Bool.not_eq_true', Bool.not_eq_false] at hex
        simp only [lowerTail] at hl
        cases htg : abiTargets T.toIsa args₂ argLocs with
        | none => simp [htg] at hl
        | some tgts =>
          cases hsh : shuffle T.toIsa hints.nslots hints.saved st1 tgts
              (hints.deadFlags.getD ip false) with
          | none => simp [htg, hsh] at hl
          | some p2 =>
            obtain ⟨sc, st2⟩ := p2
            simp only [htg, hsh, Except.ok.injEq, Prod.mk.injEq] at hl
            obtain ⟨rfl, -, -, -⟩ := hl
            simp only [List.append_assoc] at hc
            obtain ⟨hmc, hc2⟩ := List.IsInfixAt.append hc
            obtain ⟨hsc, hc3⟩ := List.IsInfixAt.append hc2
            simp only [wp] at hwp
            refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
            refine shuffle_ok hy.spE hsh hsc hA1 hI1 fun s2 σ2 hok hA2 hI2 => ?_
            exact exit_ok hy hargs hex hal htg (by simpa only [List.append_assoc] using hc3) hok hA2
              hI2 hwp
  · -- hlt
    intro G D
    refine ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hwp => absurd hwp (by simp [wp]),
      ccmpChain_none (by simp [lowerCcmpChain]),
      ccmpJnz_none (by simp [lowerCcmpJnz])⟩
  · -- group
    intro G D sig b₁ b₂ k₁ k₂ hb _ ihb ihk
    exact ⟨lowerExpr_group_ok hy hb (fun ls₁ ls₂ {ts} i xs₁ xs₂ => (ihb ls₁ ls₂ i xs₁ xs₂).1)
        (fun ls₁ ls₂ => (ihk ls₁ ls₂).1),
      ccmpChain_none (by simp [lowerCcmpChain]),
      ccmpJnz_none (by simp [lowerCcmpJnz])⟩

end Main

/-! ## Function-level correctness -/

/-- **Main theorem:** a successfully lowered well-formed function satisfies `Target.FnSpec`. -/
theorem lowerFn_correct (T : Target) (host : T.mach.Host) (hints : T.toIsa.Hints) (E : Ext) (f : Fn)
    (Γ : Env) (n nX : Nat) (bound : Sym → Nat) {code : List T.Directive} {k₀ : Nat}
    (hwf : f.Wf) (hl : lowerFn T.toIsa hints E f = .ok code)
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hfr : effFrame T.toIsa hints E ≤ n) (hn : n + T.frame.raBytes ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ E.callees →
      T.FnSpec host g (Γ g as bs) (bound g) nX ∧
        effFrame T.toIsa hints E + T.frame.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ E.exits → T.Defined host g ∧ nX ≤ n) :
    T.FnSpec host f.name (Func.spec Γ f.body) n nX := by
  unfold lowerFn at hl
  split at hl; · simp at hl
  rename_i hsv
  simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, List.all_eq_true] at hsv
  cases hal : T.toIsa.assignArgs f.as with
  | none => simp [hal] at hl
  | some argLocs =>
    cases hrl : T.toIsa.assignRets f.rs with
    | none => simp [hal, hrl] at hl
    | some retLocs =>
      simp only [hal, hrl] at hl
      cases hb : bindAbiParams T.toIsa argLocs 0
          { regs := [], slots := .empty, defs := .empty, vecWidths := .empty } with
      | none => simp [hb] at hl
      | some st0 =>
        simp only [hb] at hl
        split at hl
        · rename_i c nv' nl' ip' hle
          simp only [Except.ok.injEq] at hl
          subst hl
          intro args m Q X hspec s ra R hargs hra hspE hmem
          have hy : Hyps T host hints E Γ s n nX bound :=
            { unique := hu, spE := hspE, frame_le := hfr, frame_bound := by omega,
              stack_bound := hn,
              saved_cs := fun r hr => by simpa using hsv.2 r hr,
              saved_nodup := listNodup_nodup hsv.1,
              callees := hcal, exits := hex }
          have hmd0 : st0.memDefs = .empty := bindAbiParams_memDefs hb
          obtain ⟨hlab, hrest⟩ := List.IsInfixAt.cons hc
          rw [labelAddr_of_unique hu hlab]
          refine T.frameSpec.label_spec hlab ?_
          obtain ⟨hpro, hbody⟩ := List.IsInfixAt.append hrest
          refine fn_entry_ok hy hargs hra hmem hal hb hpro fun s' σ hA hI => ?_
          exact lowerExpr_correct (fn := f.name) (Q := Q) (X := X) (Rf := R) (ra := ra) hy
            (hwf Val VNat Cont LNat args (Tup.levels f.as 0)) f.as.length 0 0 st0 none
            .empty .empty c nv' nl' ip' _ s' σ m hle hbody (FT_none _)
            ⟨fun _ _ h => by simp [Trie.find?] at h, fun _ h => by simp [Trie.find?] at h⟩
            (fun _ _ _ h => nomatch h) (fun _ _ _ h => nomatch h) hA
            (hmd0 ▸ MemDefsOk.empty _ _ _) hI hspec
        · simp at hl

end Rega
end LeanQbe.T
