module

public import LeanQbe.T.SimplifyGroupLemmas1
public import LeanQbe.T.WPLemmas

/-!
# Correctness Proofs for `SimplifyGroup` (`O-M2`, Part 2)

Builds on `LeanQbe.T.SimplifyGroupLemmas1` to prove:
* `simplifyGroup_outerWf` / `simplifyGroup_wf` / `Func.simplifyGroup_wf`
* `untagWith`, `substLabels_wp`, `spliceBlock_wp`, `outerWf_wp_congr_rhs`
* `simplifyGroup_wp` / `Func.simplifyGroup_spec`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

namespace SgImpl

private theorem outerWf_ite_bool {chk : Bool} {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} {G : Ctx (OptV V₁) (OptV V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {c₁ c₂ : Bool} {t₁ e₁ : Expr (OptV V₁) (JLabel L₁) rs}
    {t₂ e₂ : Expr (OptV V₂) (JLabel L₂) rs}
    (hc : c₁ = c₂)
    (ht : c₁ = true → c₂ = true → OuterWf chk G D t₁ t₂)
    (he : c₁ = false → c₂ = false → OuterWf chk G D e₁ e₂) :
    OuterWf chk G D (if c₁ then t₁ else e₁) (if c₂ then t₂ else e₂) := by
  cases h1 : c₁ with
  | true =>
    have h2 : c₂ = true := (h1.symm.trans hc).symm
    simp only [h2, ↓reduceIte]; exact ht h1 h2
  | false =>
    have h2 : c₂ = false := (h1.symm.trans hc).symm
    simp only [h2, Bool.false_eq_true, ↓reduceIte]; exact he h1 h2

private theorem spliceCov_cons_bounded {L₁ L₂ : List Ty → Type} (depth targetId : Nat)
    (targetTs : List Ty) {D : Ctx (JLabel L₁) (JLabel L₂)}
    (hD : BoundedD depth D) (hle : depth ≤ targetId) :
    SpliceCov targetId targetTs (⟨targetTs, .loc targetId, .loc targetId⟩ :: D) D := by
  intro p hp
  cases hp with
  | head => exact ⟨rfl, by simp⟩
  | tail _ hp =>
    have hd := hD p hp; rcases p with ⟨pts, j₁, j₂⟩
    cases j₁ <;> cases j₂ <;> simp only [isLocLbl] at hd ⊢
    all_goals first
      | exact ⟨trivial, trivial, hp⟩
      | (have hf : true = false := hd.1; cases hf)
      | (have hf : true = false := hd.2; cases hf)
      | (rcases hd with ⟨rfl, hlt⟩
         have hne : ∀ x < depth, (x == targetId) = false := fun x hx => by
           simp only [beq_eq_false_iff_ne]; omega
         exact ⟨rfl, by simp [hne _ hlt]; exact hp⟩)

/-! ## `SgRel`, `handleGroup_kept_outerWf`, and `simplifyGroup_outerWf` -/

def SgRel {V₁ V₂ : Ty → Type} (G' : Ctx (OptV V₁) (OptV V₂))
    (G : Ctx (Arg (OptV V₁)) (Arg (OptV V₂))) : Prop :=
  ∀ p ∈ G, ArgRel G' p.1 p.2.1 p.2.2

theorem SgRel.weaken {V₁ V₂ : Ty → Type} {G₁ G₂ : Ctx (OptV V₁) (OptV V₂)}
    {G : Ctx (Arg (OptV V₁)) (Arg (OptV V₂))} (hG : SgRel G₁ G) (hsub : ∀ p ∈ G₁, p ∈ G₂) :
    SgRel G₂ G := fun p hp => (hG p hp).weaken hsub

theorem SgRel.flattenArg {V₁ V₂ : Ty → Type} {G' : Ctx (OptV V₁) (OptV V₂)}
    {G : Ctx (Arg (OptV V₁)) (Arg (OptV V₂))} (hG : SgRel G' G)
    {t : Ty} {a₁ : Arg (Arg (OptV V₁)) t} {a₂ : Arg (Arg (OptV V₂)) t} :
    ArgRel G t a₁ a₂ → ArgRel G' t (flattenArg a₁) (flattenArg a₂)
  | .var hm => hG _ hm
  | .imm c => .imm c

theorem SgRel.flattenArgs {V₁ V₂ : Ty → Type} {G' : Ctx (OptV V₁) (OptV V₂)}
    {G : Ctx (Arg (OptV V₁)) (Arg (OptV V₂))} (hG : SgRel G' G)
    {ts : List Ty} {as₁ : Tup (Arg (Arg (OptV V₁))) ts} {as₂ : Tup (Arg (Arg (OptV V₂))) ts}
    (h : TRel (ArgRel G) as₁ as₂) : TRel (ArgRel G') (flattenArgs as₁) (flattenArgs as₂) :=
  TRel.tupMapArg_rel (fun _ => LeanQbe.T.flattenArg) (fun _ => LeanQbe.T.flattenArg)
    (fun ha => hG.flattenArg ha) h

theorem SgRel.append_toArgTup {V₁ V₂ : Ty → Type} {G' : Ctx (OptV V₁) (OptV V₂)}
    {G : Ctx (Arg (OptV V₁)) (Arg (OptV V₂))} (hG : SgRel G' G) :
    {ts : List Ty} → (xs₁ : Tup (OptV V₁) ts) → (xs₂ : Tup (OptV V₂) ts) →
    SgRel (Tup.zip xs₁ xs₂ ++ G') (Tup.zip (toArgTup xs₁) (toArgTup xs₂) ++ G)
  | [], (), () => hG
  | _ :: _, (x₁, xs₁), (x₂, xs₂) => fun p hp => by
    simp only [toArgTup, Tup.zip, List.cons_append] at hp ⊢
    cases hp with
    | head => exact .var List.mem_cons_self
    | tail _ hp => exact (SgRel.append_toArgTup hG xs₁ xs₂ p hp).weaken fun _ h => .tail _ h

theorem SgRel.cons_var {V₁ V₂ : Ty → Type} {G' : Ctx (OptV V₁) (OptV V₂)}
    {G : Ctx (Arg (OptV V₁)) (Arg (OptV V₂))} (hG : SgRel G' G) {t : Ty}
    (v₁ : OptV V₁ t) (v₂ : OptV V₂ t) :
    SgRel (⟨t, v₁, v₂⟩ :: G') (⟨t, .var v₁, .var v₂⟩ :: G) := fun p hp => by
  cases hp with
  | head => exact .var List.mem_cons_self
  | tail _ hp => exact (hG p hp).weaken fun _ h => .tail _ h

theorem SgRel.append_args {V₁ V₂ : Ty → Type} {G' : Ctx (OptV V₁) (OptV V₂)}
    {G : Ctx (Arg (OptV V₁)) (Arg (OptV V₂))} (hG : SgRel G' G) :
    {ts : List Ty} → {a₁ : Tup (Arg (OptV V₁)) ts} → {a₂ : Tup (Arg (OptV V₂)) ts} →
    TRel (ArgRel G') a₁ a₂ → SgRel G' (Tup.zip a₁ a₂ ++ G)
  | [], (), (), .nil, p, hp => hG p hp
  | _ :: _, (_, _), (_, _), .cons ha has, p, hp => by
    cases hp with | head => exact ha | tail _ hp => exact SgRel.append_args hG has p hp

theorem handleGroup_kept_outerWf {chk : Bool} {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} (depth : Nat) {sig : List (List Ty)}
    {G : Ctx (OptV V₁) (OptV V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)} (hD : BoundedD depth D)
    {bs₁' : SBlocks (OptV V₁) (JLabel L₁) rs sig}
    {bs₂' : SBlocks (OptV V₂) (JLabel L₂) rs sig}
    {k₁' : Expr (OptV V₁) (JLabel L₁) rs} {k₂' : Expr (OptV V₂) (JLabel L₂) rs}
    (hb0 : OuterWfS false G (Tup.zip (locLabels sig depth) (locLabels sig depth) ++ D) bs₁' bs₂')
    (hb : OuterWfS chk G (Tup.zip (locLabels sig depth) (locLabels sig depth) ++ D) bs₁' bs₂')
    (hk0 : OuterWf false G (Tup.zip (locLabels sig depth) (locLabels sig depth) ++ D) k₁' k₂')
    (hk : OuterWf chk G (Tup.zip (locLabels sig depth) (locLabels sig depth) ++ D) k₁' k₂')
    {reach : List Nat}
    (hreach_k : ∀ x ∈ collectJumps depth (depth + sig.length) k₁' [], x ∈ reach)
    (hsbc : SBlocksClosed reach depth (depth + sig.length) depth bs₁')
    {sig' : List (List Ty)} {ids' : List Nat}
    {bs₁'' : SBlocks (OptV V₁) (JLabel L₁) rs sig'}
    {bs₂'' : SBlocks (OptV V₂) (JLabel L₂) rs sig'}
    {mkEnv₁ : Tup (JLabel L₁) sig' → List (Nat × ((ts : List Ty) × JLabel L₁ ts))}
    {mkEnv₂ : Tup (JLabel L₂) sig' → List (Nat × ((ts : List Ty) × JLabel L₂ ts))}
    (hr₁ : filterSBlocks (fun x => reach.contains x) sig bs₁' depth = ⟨sig', ids', bs₁'', mkEnv₁⟩)
    (hr₂ : filterSBlocks (fun x => reach.contains x) sig bs₂' depth = ⟨sig', ids', bs₂'', mkEnv₂⟩) :
    OuterWf chk G D
      (.group (sig := sig') (fun Js => substLabelsB (mkEnv₁ Js) (sblocksToBlocks bs₁''))
        (fun Js => substLabels (mkEnv₁ Js) k₁'))
      (.group (sig := sig') (fun Js => substLabelsB (mkEnv₂ Js) (sblocksToBlocks bs₂''))
        (fun Js => substLabels (mkEnv₂ Js) k₂')) := by
  let d' := depth + sig.length
  let keep : Nat → Bool := fun x => reach.contains x
  have hD_loc := boundedD_append_loc sig depth depth (Nat.le_refl _) hD
  have hD_c := boundedD_lblCompat hD_loc
  let D_keep : Ctx (JLabel L₁) (JLabel L₂) :=
    (Tup.zip (locLabels sig depth) (locLabels sig depth)).filter
      (fun p => match p.2.1 with | .loc d => reach.contains d | _ => true) ++ D
  have hrest : RestSub depth d' (Tup.zip (locLabels (L := L₁) sig depth)
      (locLabels (L := L₂) sig depth) ++ D) D_keep :=
    restSub_loc_drop sig depth hD fun _ hp => List.mem_append_right _ hp
  have hmem_keep : ∀ x ∈ reach, ∀ {ts},
      ⟨ts, JLabel.loc x, JLabel.loc x⟩ ∈
        Tup.zip (locLabels (L := L₁) sig depth) (locLabels (L := L₂) sig depth) ++ D →
      ⟨ts, JLabel.loc x, JLabel.loc x⟩ ∈ D_keep := fun x hxr {ts} hmem => by
    rcases List.mem_append.1 hmem with hmem | hmem
    · exact List.mem_append_left _ (List.mem_filter.2 ⟨hmem, by simp [hxr]⟩)
    · exact List.mem_append_right _ hmem
  have hk_keep := outerWf_restrict_of_collect depth d' hD_c hrest hk0 hk
    fun x hx => hmem_keep x (hreach_k x hx)
  have hb_keep : OuterWfB chk G D_keep (sblocksToBlocks bs₁'') (sblocksToBlocks bs₂'') := by
    have hsig_eq := (filterSBlocks_sig_eq keep sig bs₁' bs₂' depth).1
    have hfl0 := outerWfS_cast rfl _ _ hsig_eq hr₁ hr₂
      (filterSBlocks_outerWfS keep sig bs₁' bs₂' depth G _ hb0 hsig_eq)
    have hflc := outerWfS_cast rfl _ _ hsig_eq hr₁ hr₂
      (filterSBlocks_outerWfS keep sig bs₁' bs₂' depth G _ hb hsig_eq)
    refine outerWfB_restrict_of_collect depth d' hD_c hrest hfl0.to_blocks hflc.to_blocks
      fun x hx {ts'} hmem => ?_
    rcases collectJumpsB_mem_exists depth d' x (sblocksToBlocks bs₁'') hx with ⟨tsB, iB, hiB⟩
    have hcl : ∀ r : FilterRes (OptV V₁) L₁ rs,
        r = filterSBlocks (fun x => reach.contains x) sig bs₁' depth →
        ∀ (j : Member tsB r.sig),
          x ∈ collectJumps depth d' ((sblocksToBlocks r.blocks).get j (noneTup tsB)) [] →
          x ∈ reach := by
      rintro _ rfl j hj; exact filterSBlocks_kept_closed reach depth d' sig bs₁' depth hsbc j x hj
    exact hmem_keep x (hcl ⟨sig', ids', bs₁'', mkEnv₁⟩ hr₁.symm iB hiB) hmem
  have hcov : ∀ (Js₁ : Tup (JLabel L₁) sig') (Js₂ : Tup (JLabel L₂) sig'),
      SubstCov (mkEnv₁ Js₁) (mkEnv₂ Js₂) D_keep (Tup.zip Js₁ Js₂ ++ D) := by
    intro Js₁ Js₂ p hp
    rcases List.mem_append.1 hp with hp | hp
    · rcases List.mem_filter.1 hp with ⟨hp_loc, hp_rch⟩
      rcases mem_locLabels_zip sig depth hp_loc with ⟨id, h1, h2, hge, hhi⟩
      rcases p with ⟨ts', j₁, j₂⟩; simp only at h1 h2 hp_rch; subst h1 h2
      have hfl := filterSBlocks_mkEnv_lookup_eq keep sig bs₁' bs₂' depth hge hhi hp_loc hp_rch
        Js₁ Js₂ hr₁ hr₂
      rcases hfl with ⟨l₁, l₂, hl₁, hl₂, hmem_j⟩
      exact ⟨rfl, by rw [hl₁, hl₂]; exact List.mem_append_left _ hmem_j⟩
    · have h := hD p hp
      rcases p with ⟨ts', j₁, j₂⟩; cases j₁ <;> cases j₂ <;> simp only [isLocLbl] at h ⊢
      all_goals first
        | (have hf : true = false := h.1; cases hf)
        | (have hf : true = false := h.2; cases hf)
        | exact ⟨trivial, trivial, List.mem_append_right _ hp⟩
        | (rcases h with ⟨rfl, hlt⟩
           have hn1 := filterSBlocks_mkEnv_lt_none_eq keep sig bs₁' depth _ ts' hlt Js₁ hr₁
           have hn2 := filterSBlocks_mkEnv_lt_none_eq keep sig bs₂' depth _ ts' hlt Js₂ hr₂
           exact ⟨rfl, by rw [hn1, hn2]; exact List.mem_append_right _ hp⟩)
  exact .group
    (fun Js₁ Js₂ _ => outerWfB_substLabels (mkEnv₁ Js₁) (mkEnv₂ Js₂) (hcov Js₁ Js₂) hb_keep)
    (fun Js₁ Js₂ _ => outerWf_substLabels (mkEnv₁ Js₁) (mkEnv₂ Js₂) (hcov Js₁ Js₂) hk_keep)

theorem simplifyGroup_outerWf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (Arg (OptV V₁)) (Arg (OptV V₂))} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {e₁ : Expr (Arg (OptV V₁)) (JLabel L₁) rs} {e₂ : Expr (Arg (OptV V₂)) (JLabel L₂) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx (OptV V₁) (OptV V₂)} (chk : Bool) (depth : Nat),
      (chk = true → SgRel G' G) → BoundedD depth D →
      OuterWf chk G' D (simplifyGroup depth e₁) (simplifyGroup depth e₂) := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro G' chk depth hG hD
    cases hop with
    | mk code hargs =>
      exact .let_ (fun h => .mk code ((hG h).flattenArgs hargs)) fun xs₁ xs₂ _ =>
        ih (toArgTup xs₁) (toArgTup xs₂) chk depth
          (fun h => (hG h).append_toArgTup xs₁ xs₂) hD
  | load t ha _ ih =>
    intro G' chk depth hG hD
    exact .load t (fun h => (hG h).flattenArg ha) fun v₁ v₂ _ =>
      ih (.var v₁) (.var v₂) chk depth (fun h => (hG h).cons_var v₁ v₂) hD
  | store hv ha _ ih =>
    intro G' chk depth hG hD
    exact .store (fun h => (hG h).flattenArg hv) (fun h => (hG h).flattenArg ha)
      (ih chk depth hG hD)
  | call f hargs _ ih =>
    intro G' chk depth hG hD
    exact .call f (fun h => (hG h).flattenArgs hargs) fun xs₁ xs₂ _ =>
      ih (toArgTup xs₁) (toArgTup xs₂) chk depth
        (fun h => (hG h).append_toArgTup xs₁ xs₂) hD
  | jnz hc _ _ iht ihe =>
    intro G' chk depth hG hD
    exact .jnz (fun h => (hG h).flattenArg hc) (iht chk depth hG hD) (ihe chk depth hG hD)
  | jump hj hargs => intro G' chk _ hG _; exact .jump hj (fun h => (hG h).flattenArgs hargs)
  | ret hvs => intro G' chk _ hG _; exact .ret (fun h => (hG h).flattenArgs hvs)
  | exit f hargs => intro G' chk _ hG _; exact .exit f (fun h => (hG h).flattenArgs hargs)
  | hlt => intro _ _ _ _ _; exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro G' chk depth hG hD
    let d' := depth + sig.length
    have hD_loc := boundedD_append_loc sig depth depth (Nat.le_refl _) hD
    have hD_c := boundedD_lblCompat hD_loc
    have mk_bs : ∀ (c : Bool), (c = true → SgRel G' G) →
        OuterWfS c G' (Tup.zip (locLabels sig depth) (locLabels sig depth) ++ D)
          (simplifyGroupB d' (b₁ (locLabels sig depth)))
          (simplifyGroupB d' (b₂ (locLabels sig depth))) := fun c hGc => by
      clear ihk
      let rec go : ∀ (s : List (List Ty))
          (bs₁ : Blocks (Arg (OptV V₁)) (JLabel L₁) rs s)
          (bs₂ : Blocks (Arg (OptV V₂)) (JLabel L₂) rs s),
          (∀ {ts} (i : Member ts s) xs₁ xs₂, ∀ {G''}, (∀ p ∈ G', p ∈ G'') →
            (c = true → SgRel G'' (Tup.zip xs₁ xs₂ ++ G)) →
            OuterWf c G'' (Tup.zip (locLabels sig depth) (locLabels sig depth) ++ D)
              (simplifyGroup d' (bs₁.get i xs₁)) (simplifyGroup d' (bs₂.get i xs₂))) →
          OuterWfS c G' (Tup.zip (locLabels sig depth) (locLabels sig depth) ++ D)
            (simplifyGroupB d' bs₁) (simplifyGroupB d' bs₂)
        | [], .nil, .nil, _ => .nil
        | _ :: _, .cons _ bs₁, .cons _ bs₂, hbs =>
          .cons (fun a₁ a₂ hsub ha => hbs .here a₁ a₂ hsub
              fun hc => ((hGc hc).weaken hsub).append_args (ha hc))
            (go _ bs₁ bs₂ fun i => hbs (.there i))
      exact go sig _ _ fun i xs₁ xs₂ _ _ hG'' =>
        ihb (locLabels sig depth) (locLabels sig depth) i xs₁ xs₂ c d' hG'' hD_loc
    have hb0 := mk_bs false (fun h => by cases h)
    have hbc := mk_bs chk hG
    have hk0 := ihk (locLabels sig depth) (locLabels sig depth) (G' := G') false d'
      (fun h => by cases h) hD_loc
    have hkc := ihk (locLabels sig depth) (locLabels sig depth) chk d' hG hD_loc
    simp only [simplifyGroup]; unfold handleGroup; dsimp only
    let k₁' := simplifyGroup d' (k₁ (locLabels sig depth))
    let k₂' := simplifyGroup d' (k₂ (locLabels sig depth))
    let bs₁' := simplifyGroupB d' (b₁ (locLabels sig depth))
    let bs₂' := simplifyGroupB d' (b₂ (locLabels sig depth))
    have heq_init : collectJumps depth d' k₁' [] = collectJumps depth d' k₂' [] :=
      outerWf_collectJumps depth d' hD_c hk0 []
    have heq_adj : blockAdj depth d' depth bs₁' = blockAdj depth d' depth bs₂' :=
      outerWfS_blockAdj depth d' hD_c depth hb0
    rw [heq_init, heq_adj]
    let reach := reachLoop (blockAdj depth d' depth bs₂') (sig.length + 1)
      (collectJumps depth d' k₂' [])
    let keep : Nat → Bool := fun x => reach.contains x
    rcases filterSBlocks_sig_eq keep sig bs₁' bs₂' depth with ⟨hsig, hids⟩
    have hlen1 := filterSBlocks_ids_len keep sig bs₁' depth
    have hadj_bd := blockAdj_bounds depth d' depth bs₁'
    have hinit_bd := collectJumps_bounds depth d' k₁' (acc := []) (fun _ h => (by cases h))
    have hinit_nd := collectJumps_nodup depth d' k₁' List.nodup_nil
    have hreach := reachLoop_spec (blockAdj depth d' depth bs₁') depth sig.length
      (by simpa [d'] using hadj_bd) (sig.length + 1) (collectJumps depth d' k₁' [])
      (by simpa [d'] using hinit_bd) hinit_nd (by omega)
    rw [heq_init, heq_adj] at hreach
    have hsbc := sblocksClosed_of_adj reach depth d' depth bs₁'
      (by simpa only [heq_adj] using hreach.2)
    rcases hr₁ : filterSBlocks keep sig bs₁' depth with ⟨sig₁', ids₁', bs₁'', mkEnv₁⟩
    rcases hr₂ : filterSBlocks keep sig bs₂' depth with ⟨sig₂', ids₂', bs₂'', mkEnv₂⟩
    rw [hr₁] at hsig hids hlen1; rw [hr₂] at hsig hids
    subst hsig; subst hids
    have hfl0 := outerWfS_cast rfl _ _
      (filterSBlocks_sig_eq keep sig bs₁' bs₂' depth).1 hr₁ hr₂
      (filterSBlocks_outerWfS keep sig bs₁' bs₂' depth G' _ hb0
        (filterSBlocks_sig_eq keep sig bs₁' bs₂' depth).1)
    have hflc := outerWfS_cast rfl _ _
      (filterSBlocks_sig_eq keep sig bs₁' bs₂' depth).1 hr₁ hr₂
      (filterSBlocks_outerWfS keep sig bs₁' bs₂' depth G' _ hbc
        (filterSBlocks_sig_eq keep sig bs₁' bs₂' depth).1)
    have hrest_sub := restSub_loc_drop sig depth hD fun _ hp => hp
    cases sig₁' with
    | nil =>
      cases bs₁''; cases bs₂''; dsimp only
      refine outerWf_restrict_of_collect depth d' hD_c hrest_sub hk0 hkc fun x hx {ts'} _ => ?_
      have hnil := (filterSBlocks_ids_spec keep sig bs₁' depth).2.1 (by simp [hr₁])
      have hxr := hreach.1 x (heq_init ▸ hx)
      have hbdx := hinit_bd x hx
      have hf := hnil x hbdx.1 hbdx.2
      simp only [keep, List.contains_eq_mem, decide_eq_false_iff_not] at hf
      exact False.elim (hf hxr)
    | cons jTs sig_rest =>
      cases sig_rest with
      | nil =>
        cases bs₁'' with | cons b₁' bt₁ => cases bt₁ with | nil =>
        cases bs₂'' with | cons b₂' bt₂ => cases bt₂ with | nil =>
        cases ids₁' with
        | nil => simp at hlen1
        | cons jId id_rest =>
          cases id_rest with
          | cons _ _ => simp at hlen1
          | nil =>
            change OuterWf chk G' D
              (if !hasJumpTo jId (b₁' (dummyArgOptTup jTs)) &&
                  (isJumpTo jId jTs k₁' ||
                    (exprSizeJ (b₁' (dummyArgOptTup jTs)) ≤ 16 && countJumps jId k₁' == 1))
                then spliceBlock jId jTs b₁' k₁'
                else .group (sig := [jTs])
                  (fun Js => substLabelsB (mkEnv₁ Js) (sblocksToBlocks (.cons b₁' .nil)))
                  (fun Js => substLabels (mkEnv₁ Js) k₁'))
              (if !hasJumpTo jId (b₂' (dummyArgOptTup jTs)) &&
                  (isJumpTo jId jTs k₂' ||
                    (exprSizeJ (b₂' (dummyArgOptTup jTs)) ≤ 16 && countJumps jId k₂' == 1))
                then spliceBlock jId jTs b₂' k₂'
                else .group (sig := [jTs])
                  (fun Js => substLabelsB (mkEnv₂ Js) (sblocksToBlocks (.cons b₂' .nil)))
                  (fun Js => substLabels (mkEnv₂ Js) k₂'))
            have hbc0 : ∀ {G''} a₁ a₂, (∀ p ∈ G', p ∈ G'') →
                OuterWf false G'' (Tup.zip (locLabels sig depth) (locLabels sig depth) ++ D)
                  (b₁' a₁) (b₂' a₂) := by
              cases hfl0 with
              | cons hb _ => exact fun a₁ a₂ hsub => hb a₁ a₂ hsub fun h => by cases h
            have hbcc : ∀ {G''} a₁ a₂, (∀ p ∈ G', p ∈ G'') →
                (chk = true → TRel (ArgRel G'') a₁ a₂) →
                OuterWf chk G'' (Tup.zip (locLabels sig depth) (locLabels sig depth) ++ D)
                  (b₁' a₁) (b₂' a₂) := by cases hflc with | cons hb _ => exact hb
            have hb_dum := hbc0 (dummyArgOptTup jTs) (dummyArgOptTup jTs) (fun _ h => h)
            have hbd_eq := outerWf_countJumps jId hD_c hb_dum
            have hsz_eq := outerWf_exprSizeJ hb_dum
            refine outerWf_ite_bool ?_ (fun hcond _ => ?_) (fun _ _ => ?_)
            · dsimp only [k₁', k₂']
              simp only [hasJumpTo, hbd_eq, hsz_eq, outerWf_isJumpTo hD_c hk0 jId jTs,
                outerWf_countJumps jId hD_c hk0]
            · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
              have hbc_cl := filterSBlocks_head_closed_eq reach depth d' sig bs₁' depth hsbc hr₁
              have hone := (filterSBlocks_ids_spec keep sig bs₁' depth).2.2 jTs jId
                (by simp [hr₁]) (by simp [hr₁])
              have hbk_D : ∀ {G''} a₁ a₂, (∀ p ∈ G', p ∈ G'') →
                  (chk = true → TRel (ArgRel G'') a₁ a₂) →
                  OuterWf chk G'' D (b₁' a₁) (b₂' a₂) := fun a₁ a₂ hsub ha => by
                refine outerWf_restrict_of_collect depth d' hD_c hrest_sub
                  (hbc0 a₁ a₂ hsub) (hbcc a₁ a₂ hsub ha) fun x hx {ts'} _ => ?_
                have heqc : collectJumps depth d' (b₁' a₁) [] =
                    collectJumps depth d' (b₁' (dummyArgOptTup jTs)) [] :=
                  (outerWf_collectJumps depth d' hD_c
                    (hbc0 a₁ (dummyArgOptTup jTs) hsub) []).trans
                  (outerWf_collectJumps depth d' hD_c hb_dum []).symm
                rw [heqc] at hx
                have hxr := hbc_cl.2 x hx
                have hbdx := collectJumps_bounds depth d' _ (fun _ h => (by cases h)) x hx
                have hxeq := hone.2.2.2 x hbdx.1 hbdx.2 (List.contains_iff_mem.2 hxr)
                subst hxeq
                have hcz := collectJumps_count_pos depth d' x _ hx
                have h0 : countJumps x (b₁' (dummyArgOptTup jTs)) = 0 := by
                  simpa [hasJumpTo] using hcond.1
                exact absurd h0 hcz
              have hsp_sub : RestSub depth d' (Tup.zip (locLabels (L := L₁) sig depth)
                  (locLabels (L := L₂) sig depth) ++ D) (⟨jTs, .loc jId, .loc jId⟩ :: D) :=
                restSub_loc_drop sig depth hD fun _ hp => .tail _ hp
              have hk_sub : OuterWf chk G' (⟨jTs, .loc jId, .loc jId⟩ :: D) k₁' k₂' := by
                refine outerWf_restrict_of_collect depth d' hD_c hsp_sub hk0 hkc
                  fun x hx {ts'} hmem => ?_
                have hxr := hreach.1 x (heq_init ▸ hx)
                have hbdx := hinit_bd x hx
                have hxeq := hone.2.2.2 x hbdx.1 hbdx.2 (List.contains_iff_mem.2 hxr)
                subst hxeq
                have hts' : ts' = jTs := by
                  rcases List.mem_append.1 hmem with hmem | hmem
                  · exact filterSBlocks_single_ts_eq keep sig bs₁' depth hr₁ hmem
                  · exfalso; have := hD _ hmem; simp at this; omega
                subst hts'; exact List.mem_cons_self
              exact outerWf_spliceBlock jId jTs b₁' b₂' hbk_D (fun _ h => h)
                (spliceCov_cons_bounded depth jId jTs hD hone.1) hk_sub
            · exact handleGroup_kept_outerWf depth hD hb0 hbc hk0 hkc
                (fun x hx => hreach.1 x (heq_init ▸ hx)) hsbc hr₁ hr₂
      | cons _ _ =>
        change OuterWf chk G' D
          (.group (sig := _ :: _ :: _)
            (fun Js => substLabelsB (mkEnv₁ Js) (sblocksToBlocks bs₁''))
            (fun Js => substLabels (mkEnv₁ Js) k₁'))
          (.group (sig := _ :: _ :: _)
            (fun Js => substLabelsB (mkEnv₂ Js) (sblocksToBlocks bs₂''))
            (fun Js => substLabels (mkEnv₂ Js) k₂'))
        exact handleGroup_kept_outerWf depth hD hb0 hbc hk0 hkc
          (fun x hx => hreach.1 x (heq_init ▸ hx)) hsbc hr₁ hr₂

/-! ## `outerWf_to_untag_wf` -/

def SomeRelG {V₁ V₂ : Ty → Type} (G' : Ctx V₁ V₂) (G : Ctx (OptV V₁) (OptV V₂)) : Prop :=
  ∀ p ∈ G, ∃ v₁ v₂, p.2.1 = some v₁ ∧ p.2.2 = some v₂ ∧ ⟨p.1, v₁, v₂⟩ ∈ G'

theorem SomeRelG.append_some {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {G : Ctx (OptV V₁) (OptV V₂)}
    (hG : SomeRelG G' G) : {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    SomeRelG (Tup.zip xs₁ xs₂ ++ G') (Tup.zip (someTup ts xs₁) (someTup ts xs₂) ++ G)
  | [], (), () => hG
  | _ :: _, (x₁, xs₁), (x₂, xs₂) => fun p hp => by
    simp only [someTup, Tup.zip, List.cons_append] at hp ⊢
    cases hp with
    | head => exact ⟨x₁, x₂, rfl, rfl, List.mem_cons_self⟩
    | tail _ hp =>
      rcases SomeRelG.append_some hG xs₁ xs₂ p hp with ⟨v₁, v₂, h1, h2, hm⟩
      exact ⟨v₁, v₂, h1, h2, .tail _ hm⟩

theorem SomeRelG.cons_some {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {G : Ctx (OptV V₁) (OptV V₂)}
    (hG : SomeRelG G' G) {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) :
    SomeRelG (⟨t, v₁, v₂⟩ :: G') (⟨t, some v₁, some v₂⟩ :: G) :=
  SomeRelG.append_some hG (ts := [t]) (v₁, ()) (v₂, ())

theorem argSweep_rel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {G : Ctx (OptV V₁) (OptV V₂)}
    (hG : SomeRelG G' G) {t : Ty} {a₁ : Arg (OptV V₁) t} {a₂ : Arg (OptV V₂) t} :
    ArgRel G t a₁ a₂ → ArgRel G' t (argSweep a₁) (argSweep a₂)
  | .var hm => by
    rcases hG _ hm with ⟨v₁, v₂, h1, h2, hv⟩
    dsimp only at h1 h2 hv; rw [h1, h2]; exact .var hv
  | .imm c => .imm c

theorem trel_argSweep {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {G : Ctx (OptV V₁) (OptV V₂)}
    (hG : SomeRelG G' G) {ts : List Ty} {as₁ : Tup (Arg (OptV V₁)) ts}
    {as₂ : Tup (Arg (OptV V₂)) ts} (h : TRel (ArgRel G) as₁ as₂) :
    TRel (ArgRel G') (argsSweep as₁) (argsSweep as₂) :=
  TRel.tupMapArg_rel (fun _ => argSweep) (fun _ => argSweep) (fun ha => argSweep_rel hG ha) h

def OuterD {L₁ L₂ : List Ty → Type} (D : Ctx (JLabel L₁) (JLabel L₂)) (D' : Ctx L₁ L₂) : Prop :=
  ∀ p ∈ D, match p.2.1, p.2.2 with | .outer l₁, .outer l₂ => ⟨p.1, l₁, l₂⟩ ∈ D' | _, _ => False

theorem OuterD.append_outer {L₁ L₂ : List Ty → Type} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {D' : Ctx L₁ L₂} (hD : OuterD D D') :
    {sig : List (List Ty)} → (Js₁ : Tup L₁ sig) → (Js₂ : Tup L₂ sig) →
    OuterD (Tup.zip (Js₁.map fun _ l => .outer l) (Js₂.map fun _ l => .outer l) ++ D)
      (Tup.zip Js₁ Js₂ ++ D')
  | [], (), (), p, hp => by
    have := hD p hp; cases h1 : p.2.1 <;> cases h2 : p.2.2 <;> simp_all
  | _ :: _, (_, Js₁), (_, Js₂), p, hp => by
    simp only [Tup.map, Tup.zip, List.cons_append] at hp ⊢
    cases hp with
    | head => exact List.mem_cons_self
    | tail _ hp =>
      have := OuterD.append_outer hD Js₁ Js₂ p hp
      cases h1 : p.2.1 <;> cases h2 : p.2.2 <;> simp_all

mutual
theorem outerWf_to_untag_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    {G : Ctx (OptV V₁) (OptV V₂)} → {G' : Ctx V₁ V₂} →
    {D : Ctx (JLabel L₁) (JLabel L₂)} → {D' : Ctx L₁ L₂} →
    SomeRelG G' G → OuterD D D' →
    {e₁ : Expr (OptV V₁) (JLabel L₁) rs} → {e₂ : Expr (OptV V₂) (JLabel L₂) rs} →
    OuterWf true G D e₁ e₂ → Wf G' D' (untagExpr e₁) (untagExpr e₂)
  | _, _, _, _, hG, hD, _, _, .let_ hop hk => by
    rcases hop rfl with ⟨code, hargs⟩
    exact .let_ (.mk code (trel_argSweep hG hargs)) fun xs₁ xs₂ =>
      outerWf_to_untag_wf (hG.append_some xs₁ xs₂) hD
        (hk (someTup _ xs₁) (someTup _ xs₂) (fun _ => ⟨xs₁, xs₂, rfl, rfl⟩))
  | _, _, _, _, hG, hD, _, _, .load t ha hk =>
    .load t (argSweep_rel hG (ha rfl)) fun v₁ v₂ =>
      outerWf_to_untag_wf (hG.cons_some v₁ v₂) hD
        (hk (some v₁) (some v₂) (fun _ => ⟨v₁, v₂, rfl, rfl⟩))
  | _, _, _, _, hG, hD, _, _, .store hv ha hk =>
    .store (argSweep_rel hG (hv rfl)) (argSweep_rel hG (ha rfl)) (outerWf_to_untag_wf hG hD hk)
  | _, _, _, _, hG, hD, _, _, .call f hargs hk =>
    .call f (trel_argSweep hG (hargs rfl)) fun xs₁ xs₂ =>
      outerWf_to_untag_wf (hG.append_some xs₁ xs₂) hD
        (hk (someTup _ xs₁) (someTup _ xs₂) (fun _ => ⟨xs₁, xs₂, rfl, rfl⟩))
  | _, _, _, _, hG, hD, _, _, .jnz hc ht he =>
    .jnz (argSweep_rel hG (hc rfl)) (outerWf_to_untag_wf hG hD ht) (outerWf_to_untag_wf hG hD he)
  | _, _, _, _, hG, hD, _, _, .jump (j₁ := j₁) (j₂ := j₂) hj hargs => by
    have hj' := hD _ hj
    cases j₁ <;> cases j₂ <;> simp only [untagExpr] at hj' ⊢
    · exact .jump hj' (trel_argSweep hG (hargs rfl))
    all_goals exact False.elim hj'
  | _, _, _, _, hG, _, _, _, .ret hvs => .ret (trel_argSweep hG (hvs rfl))
  | _, _, _, _, hG, _, _, _, .exit f hargs => .exit f (trel_argSweep hG (hargs rfl))
  | _, _, _, _, _, _, _, _, .hlt => .hlt
  | _, _, _, _, hG, hD, _, _, .group hb hk =>
    .group
      (fun Js₁ Js₂ => outerWfB_to_untag_wf hG (OuterD.append_outer hD Js₁ Js₂)
        (hb (Js₁.map fun _ l => .outer l) (Js₂.map fun _ l => .outer l) (isLocLbl_outer Js₁ Js₂)))
      (fun Js₁ Js₂ => outerWf_to_untag_wf hG (OuterD.append_outer hD Js₁ Js₂)
        (hk (Js₁.map fun _ l => .outer l) (Js₂.map fun _ l => .outer l) (isLocLbl_outer Js₁ Js₂)))

theorem outerWfB_to_untag_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    {G : Ctx (OptV V₁) (OptV V₂)} → {G' : Ctx V₁ V₂} →
    {D : Ctx (JLabel L₁) (JLabel L₂)} → {D' : Ctx L₁ L₂} →
    SomeRelG G' G → OuterD D D' → {sig : List (List Ty)} →
    {bs₁ : Blocks (OptV V₁) (JLabel L₁) rs sig} → {bs₂ : Blocks (OptV V₂) (JLabel L₂) rs sig} →
    OuterWfB true G D bs₁ bs₂ → WfB G' D' (untagBlocks bs₁) (untagBlocks bs₂)
  | _, _, _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, hG, hD, _, _, _, .cons hb hbs =>
    .cons (fun xs₁ xs₂ => outerWf_to_untag_wf (hG.append_some xs₁ xs₂) hD
        (hb (someTup _ xs₁) (someTup _ xs₂) (fun _ => ⟨xs₁, xs₂, rfl, rfl⟩)))
      (outerWfB_to_untag_wf hG hD hbs)
end

/-! ## `wp` refinement via `untagWith`, `substLabels_wp`, and `spliceBlock_wp` -/

abbrev JEnv : Type := ∀ {ts : List Ty}, Nat → Cont ts

def evalJLbl (interp : JEnv) {ts : List Ty} : JLabel Cont ts → Cont ts
  | .outer l => l
  | .loc id => interp id
  | .probe => fun _ _ => False

def SBlocks.get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → SBlocks V L rs sig → {ts : List Ty} → Member ts sig →
    Tup (Arg V) ts → Expr V L rs
  | _, .cons b _, _, .here => b
  | _, .cons _ bs, _, .there i => bs.get i

theorem sblocksToBlocks_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → (bs : SBlocks V L rs sig) →
    {ts : List Ty} → (i : Member ts sig) → (xs : Tup V ts) →
    (sblocksToBlocks bs).get i xs = bs.get i (toArgTup xs)
  | _, .cons _ _, _, .here, _ => rfl
  | _, .cons _ bs, _, .there i, xs => sblocksToBlocks_get bs i xs

theorem simplifyGroupB_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (d : Nat) :
    {sig : List (List Ty)} → (bs : Blocks (Arg (OptV V)) (JLabel L) rs sig) →
    {ts : List Ty} → (i : Member ts sig) → (a : Tup (Arg (OptV V)) ts) →
    (simplifyGroupB d bs).get i a = simplifyGroup d (bs.get i a)
  | _, .cons _ _, _, .here, _ => rfl
  | _, .cons _ bs, _, .there i, a => simplifyGroupB_get d bs i a

mutual
/-- `untagExpr` generalized over a local-label interpretation `interp : JEnv`. -/
def untagWith (interp : JEnv) {rs : List Ty} :
    Expr (OptV Val) (JLabel Cont) rs → Expr Val Cont rs
  | .let_ (ts := ts) op k =>
    .let_ ⟨op.code, argsSweep op.args⟩ fun xs => untagWith interp (k (someTup ts xs))
  | .load t a k => .load t (argSweep a) fun v => untagWith interp (k (some v))
  | .store v a k => .store (argSweep v) (argSweep a) (untagWith interp k)
  | .call f (bs := bs) args k =>
    .call f (argsSweep args) fun xs => untagWith interp (k (someTup bs xs))
  | .jnz c t e => .jnz (argSweep c) (untagWith interp t) (untagWith interp e)
  | .jump (.outer l) args => .jump l (argsSweep args)
  | .jump (.loc id) args => .jump (interp id) (argsSweep args)
  | .jump .probe _ => .hlt
  | .ret vs => .ret (argsSweep vs)
  | .exit f args => .exit f (argsSweep args)
  | .hlt => .hlt
  | .group bodies k =>
    .group
      (fun Js => untagBlocksWith interp (bodies (Js.map fun _ l => .outer l)))
      (fun Js => untagWith interp (k (Js.map fun _ l => .outer l)))

def untagBlocksWith (interp : JEnv) {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (OptV Val) (JLabel Cont) rs sig → Blocks Val Cont rs sig
  | _, .nil => .nil
  | _, .cons (ts := ts) b bs =>
    .cons (fun xs => untagWith interp (b (someTup ts xs))) (untagBlocksWith interp bs)
end

theorem untagBlocksWith_get (interp : JEnv) {rs : List Ty} :
    {sig : List (List Ty)} → (bs : Blocks (OptV Val) (JLabel Cont) rs sig) →
    {ts : List Ty} → (i : Member ts sig) → (xs : Tup Val ts) →
    (untagBlocksWith interp bs).get i xs = untagWith interp (bs.get i (someTup ts xs))
  | _, .cons _ _, _, .here, _ => rfl
  | _, .cons _ bs, _, .there i, xs => untagBlocksWith_get interp bs i xs

theorem untagBlocks_get {rs : List Ty} :
    {sig : List (List Ty)} → (bs : Blocks (OptV Val) (JLabel Cont) rs sig) →
    {ts : List Ty} → (i : Member ts sig) → (xs : Tup Val ts) →
    (untagBlocks bs).get i xs = untagExpr (bs.get i (someTup ts xs))
  | _, .cons _ _, _, .here, _ => rfl
  | _, .cons _ bs, _, .there i, xs => untagBlocks_get bs i xs

theorem substLabelsB_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (env : List (Nat × ((ts : List Ty) × JLabel L ts))) :
    {sig : List (List Ty)} → (bs : Blocks V (JLabel L) rs sig) →
    {ts : List Ty} → (i : Member ts sig) → (xs : Tup V ts) →
    (substLabelsB env bs).get i xs = substLabels env (bs.get i xs)
  | _, .cons _ _, _, .here, _ => rfl
  | _, .cons _ bs, _, .there i, xs => substLabelsB_get env bs i xs

theorem untagWith_false_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (e : Expr (OptV Val) (JLabel Cont) rs) :
    ∀ m, wp Γ Q X (untagWith (fun _ _ _ => False) e) m → wp Γ Q X (untagExpr e) m := by
  induction e using Expr.induct with
  | let_ _ _ ih => exact fun m h => Op.wp_mono (fun r => ih (someTup _ r) m) h
  | load _ _ _ ih => exact fun m ⟨v, hv, h⟩ => ⟨v, hv, ih (some v) m h⟩
  | store _ _ _ ih => exact fun m ⟨hok, h⟩ => ⟨hok, ih _ h⟩
  | call _ _ _ ih =>
    exact fun m ⟨P, E, hG, hP, hE⟩ =>
      ⟨P, E, hG, fun r m' hp => ih (someTup _ r) m' (hP r m' hp), hE⟩
  | jnz _ _ _ iht ihe => exact fun m h => ⟨fun hc => iht m (h.1 hc), fun hc => ihe m (h.2 hc)⟩
  | jump j _ => cases j <;> exact fun _ h => h
  | ret _ | exit _ _ | hlt => exact fun _ h => h
  | group bodies k ihb ihk =>
    intro m h Js hcl
    refine ihk (Js.map fun _ l => .outer l) m (h Js ?_)
    rw [closed_iff] at hcl ⊢
    intro ts i xs m' hb
    rw [untagBlocksWith_get] at hb
    exact hcl i xs m' (by rw [untagBlocks_get]; exact ihb _ i (someTup ts xs) m' hb)

def mkKeepInterp (env : List (Nat × ((ts : List Ty) × JLabel Cont ts))) (base : JEnv) : JEnv :=
  fun {ts} id => match lookupLblEnv env id ts with | some j => evalJLbl base j | none => base id

theorem substLabels_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (env : List (Nat × ((ts : List Ty) × JLabel Cont ts))) (base : JEnv)
    (e : Expr (OptV Val) (JLabel Cont) rs) :
    ∀ m, wp Γ Q X (untagWith (mkKeepInterp env base) e) m →
      wp Γ Q X (untagWith base (substLabels env e)) m := by
  induction e using Expr.induct with
  | let_ _ _ ih => exact fun m h => Op.wp_mono (fun r => ih (someTup _ r) m) h
  | load _ _ _ ih => exact fun m ⟨v, hv, h⟩ => ⟨v, hv, ih (some v) m h⟩
  | store _ _ _ ih => exact fun m ⟨hok, h⟩ => ⟨hok, ih _ h⟩
  | call _ _ _ ih =>
    exact fun m ⟨P, E, hG, hP, hE⟩ =>
      ⟨P, E, hG, fun r m' hp => ih (someTup _ r) m' (hP r m' hp), hE⟩
  | jnz _ _ _ iht ihe => exact fun m h => ⟨fun hc => iht m (h.1 hc), fun hc => ihe m (h.2 hc)⟩
  | @jump ts j _ =>
    intro m h
    cases j with
    | outer _ | probe => exact h
    | loc id =>
      simp only [untagWith, mkKeepInterp, wp, substLabels] at h ⊢
      cases hlk : lookupLblEnv env id ts with
      | none => simp [hlk] at h ⊢; exact h
      | some j' => simp [hlk] at h ⊢; cases j' <;> exact h
  | ret _ | exit _ _ | hlt => exact fun _ h => h
  | group bodies k ihb ihk =>
    intro m h Js hcl
    refine ihk (Js.map fun _ l => .outer l) m (h Js ?_)
    rw [closed_iff] at hcl ⊢
    intro ts i xs m' hb
    rw [untagBlocksWith_get] at hb
    exact hcl i xs m' (by
      rw [untagBlocksWith_get, substLabelsB_get]; exact ihb _ i (someTup ts xs) m' hb)

def mkSpliceInterp (targetId : Nat) (targetTs : List Ty) (P : Cont targetTs) (base : JEnv) :
    JEnv :=
  fun {ts} id =>
    if id == targetId then
      match listTyDecEq ts targetTs with | isTrue h => h ▸ P | isFalse _ => base id
    else base id

theorem spliceBlock_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (targetId : Nat) (targetTs : List Ty)
    (b : Tup (Arg (OptV Val)) targetTs → Expr (OptV Val) (JLabel Cont) rs)
    (P : Cont targetTs) (base : JEnv)
    (hP : ∀ args m, P (vals (argsSweep args)) m → wp Γ Q X (untagWith base (b args)) m)
    (e : Expr (OptV Val) (JLabel Cont) rs) :
    ∀ m, wp Γ Q X (untagWith (mkSpliceInterp targetId targetTs P base) e) m →
      wp Γ Q X (untagWith base (spliceBlock targetId targetTs b e)) m := by
  induction e using Expr.induct with
  | let_ _ _ ih => exact fun m h => Op.wp_mono (fun r => ih (someTup _ r) m) h
  | load _ _ _ ih => exact fun m ⟨v, hv, h⟩ => ⟨v, hv, ih (some v) m h⟩
  | store _ _ _ ih => exact fun m ⟨hok, h⟩ => ⟨hok, ih _ h⟩
  | call _ _ _ ih =>
    exact fun m ⟨P, E, hG, hP, hE⟩ =>
      ⟨P, E, hG, fun r m' hp => ih (someTup _ r) m' (hP r m' hp), hE⟩
  | jnz _ _ _ iht ihe => exact fun m h => ⟨fun hc => iht m (h.1 hc), fun hc => ihe m (h.2 hc)⟩
  | @jump ts j args =>
    intro m h
    cases j with
    | outer _ | probe => exact h
    | loc id =>
      simp only [untagWith, mkSpliceInterp, wp, spliceBlock] at h ⊢
      cases hid : (id == targetId)
      · rw [hid] at h; exact h
      · rw [hid] at h
        cases hd : listTyDecEq ts targetTs with
        | isFalse _ => rw [hd] at h; exact h
        | isTrue hts => rw [hd] at h; subst hts; exact hP args m h
  | ret _ | exit _ _ | hlt => exact fun _ h => h
  | group bodies k ihb ihk =>
    intro m h Js hcl
    refine ihk (Js.map fun _ l => .outer l) m (h Js ?_)
    rw [closed_iff] at hcl ⊢
    intro ts i xs m' hb
    rw [untagBlocksWith_get] at hb
    let rec spliceGet : ∀ {s} (bs : Blocks (OptV Val) (JLabel Cont) rs s)
        {ts} (i : Member ts s) xs,
        (spliceBlockB targetId targetTs b bs).get i xs =
          spliceBlock targetId targetTs b (bs.get i xs)
      | _, .cons _ _, _, .here, _ => rfl
      | _, .cons _ bs, _, .there i, xs => spliceGet bs i xs
    exact hcl i xs m' (by
      rw [untagBlocksWith_get, spliceGet]; exact ihb _ i (someTup ts xs) m' hb)

mutual
theorem outerWf_wp_congr_rhs {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {K : Ty → Type} {KL : List Ty → Type}
    {interp₁ interp₂ : JEnv} {Gk : Ctx (OptV K) (OptV Val)} {Dk : Ctx (JLabel KL) (JLabel Cont)}
    (hagree : ∀ p ∈ Dk, match p.2.2 with
      | .loc id => interp₁ (ts := p.1) id = interp₂ (ts := p.1) id | _ => True) :
    {ek : Expr (OptV K) (JLabel KL) rs} → {e₁ : Expr (OptV Val) (JLabel Cont) rs} →
    OuterWf false Gk Dk ek e₁ → ∀ m,
    wp Γ Q X (untagWith interp₁ e₁) m → wp Γ Q X (untagWith interp₂ e₁) m
  | _, _, .let_ _ hk, m, h => Op.wp_mono (fun r => outerWf_wp_congr_rhs hagree
      (hk (noneTup _) (someTup _ r) (fun c => by cases c)) m) h
  | _, _, .load _ _ hk, m, ⟨v, hv, h⟩ =>
    ⟨v, hv, outerWf_wp_congr_rhs hagree (hk none (some v) (fun c => by cases c)) m h⟩
  | _, _, .store _ _ hk, m, ⟨hok, h⟩ => ⟨hok, outerWf_wp_congr_rhs hagree hk _ h⟩
  | _, _, .call _ _ hk, m, ⟨P, E, hG, hP, hE⟩ =>
    ⟨P, E, hG, fun r m' hp => outerWf_wp_congr_rhs hagree
      (hk (noneTup _) (someTup _ r) (fun c => by cases c)) m' (hP r m' hp), hE⟩
  | _, _, .jnz _ ht he, m, h =>
    ⟨fun hc => outerWf_wp_congr_rhs hagree ht m (h.1 hc),
     fun hc => outerWf_wp_congr_rhs hagree he m (h.2 hc)⟩
  | _, _, .jump (j₂ := j₂) hj _, m, h => by
    have ha := hagree _ hj
    cases j₂ with
    | outer _ | probe => exact h
    | loc _ => simp only [untagWith, wp] at h ⊢; rw [← ha]; exact h
  | _, _, .ret _, _, h | _, _, .exit _ _, _, h | _, _, .hlt, _, h => h
  | _, _, .group (sig := sig) hb hk, m, h => by
    intro Js hcl
    have hagree' : ∀ p ∈ Tup.zip (probeLabels (L := KL) sig) (Js.map fun _ l => .outer l) ++ Dk,
        match p.2.2 with | .loc id => interp₁ (ts := p.1) id = interp₂ (ts := p.1) id | _ => True :=
      fun p hp => by
        rcases List.mem_append.1 hp with hp | hp
        · have h := isLocLbl_probe_outer Js p hp; cases h2 : p.2.2 <;> simp_all [isLocLbl]
        · exact hagree p hp
    have hagree_sym :
        ∀ p ∈ Tup.zip (probeLabels (L := KL) sig) (Js.map fun _ l => .outer l) ++ Dk,
        match p.2.2 with | .loc id => interp₂ (ts := p.1) id = interp₁ (ts := p.1) id | _ => True :=
      fun p hp => by
        have := hagree' p hp; cases h2 : p.2.2 <;> simp_all
    refine outerWf_wp_congr_rhs hagree' (hk (probeLabels sig) (Js.map fun _ l => .outer l)
      (isLocLbl_probe_outer Js)) m (h Js ?_)
    exact outerWfB_wp_congr_rhs hagree_sym (hb (probeLabels sig) (Js.map fun _ l => .outer l)
      (isLocLbl_probe_outer Js)) Js hcl

theorem outerWfB_wp_congr_rhs {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {K : Ty → Type} {KL : List Ty → Type}
    {interp₁ interp₂ : JEnv} {Gk : Ctx (OptV K) (OptV Val)} {Dk : Ctx (JLabel KL) (JLabel Cont)}
    (hagree : ∀ p ∈ Dk, match p.2.2 with
      | .loc id => interp₁ (ts := p.1) id = interp₂ (ts := p.1) id | _ => True) :
    {sig : List (List Ty)} →
    {bsk : Blocks (OptV K) (JLabel KL) rs sig} → {bs₁ : Blocks (OptV Val) (JLabel Cont) rs sig} →
    OuterWfB false Gk Dk bsk bs₁ → ∀ Js,
    Closed Γ Q X (untagBlocksWith interp₁ bs₁) Js → Closed Γ Q X (untagBlocksWith interp₂ bs₁) Js
  | _, _, _, .nil, (), _ => trivial
  | _, _, _, .cons hb hbs, (J, Js), hcl => by
    simp only [Closed, untagBlocksWith] at hcl ⊢
    exact ⟨fun xs m h => hcl.1 xs m (outerWf_wp_congr_rhs (fun p hp => by
        have := hagree p hp; cases h2 : p.2.2 <;> simp_all)
        (hb (noneTup _) (someTup _ xs) (fun c => by cases c)) m h),
      outerWfB_wp_congr_rhs hagree hbs Js hcl.2⟩
end

def WpG (G : Ctx (Arg (OptV Val)) Val) : Prop :=
  ∀ p ∈ G, (argSweep p.2.1).val = p.2.2

theorem WpG.append_some {G : Ctx (Arg (OptV Val)) Val} (hG : WpG G) :
    {ts : List Ty} → (xs : Tup Val ts) → WpG (Tup.zip (toArgTup (someTup ts xs)) xs ++ G)
  | [], () => hG
  | _ :: _, (x, xs) => fun p hp => by
    simp only [someTup, toArgTup, Tup.zip, List.cons_append] at hp
    cases hp with
    | head => rfl
    | tail _ hp => exact WpG.append_some hG xs p hp

theorem WpG.cons_some {G : Ctx (Arg (OptV Val)) Val} (hG : WpG G) {t : Ty} (v : Val t) :
    WpG (⟨t, .var (some v), v⟩ :: G) :=
  WpG.append_some hG (ts := [t]) (v, ())

theorem argSweep_flatten_val {G : Ctx (Arg (OptV Val)) Val} (hG : WpG G) {t : Ty}
    {a₁ : Arg (Arg (OptV Val)) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → (argSweep (flattenArg a₁)).val = a₂.val
  | .var hm => hG _ hm
  | .imm _ => rfl

theorem trel_argsSweep_flatten_vals {G : Ctx (Arg (OptV Val)) Val} (hG : WpG G) :
    {ts : List Ty} → {a₁ : Tup (Arg (Arg (OptV Val))) ts} → {a₂ : Tup (Arg Val) ts} →
    TRel (ArgRel G) a₁ a₂ → vals (argsSweep (flattenArgs a₁)) = vals a₂
  | [], (), (), .nil => rfl
  | _ :: _, (x₁, xs₁), (x₂, xs₂), .cons h hs => by
    simp only [tupMapArg, vals]
    rw [argSweep_flatten_val hG h, trel_argsSweep_flatten_vals hG hs]

theorem WpG.append_args {G₁ G₂ : Ctx (Arg (OptV Val)) Val} (hG₁ : WpG G₁) (hG₂ : WpG G₂) :
    {ts : List Ty} → {a₁ : Tup (Arg (Arg (OptV Val))) ts} → {a₂ : Tup (Arg Val) ts} →
    TRel (ArgRel G₁) a₁ a₂ → WpG (Tup.zip (flattenArgs a₁) (vals a₂) ++ G₂)
  | [], (), (), .nil => hG₂
  | _ :: _, (x₁, xs₁), (x₂, xs₂), .cons h hs => fun p hp => by
    simp only [flattenArgs, tupMapArg, vals, Tup.zip, List.cons_append] at hp
    cases hp with
    | head => exact argSweep_flatten_val hG₁ h
    | tail _ hp => exact WpG.append_args hG₁ hG₂ hs p hp

theorem WpG.append_val_eq {G : Ctx (Arg (OptV Val)) Val} (hG : WpG G) :
    {ts : List Ty} → (a : Tup (Arg (OptV Val)) ts) → (xs : Tup Val ts) →
    vals (argsSweep a) = xs → WpG (Tup.zip a xs ++ G)
  | [], (), (), _ => hG
  | _ :: _, (a, as), (x, xs), heq => fun p hp => by
    simp only [Tup.zip, List.cons_append] at hp
    simp only [tupMapArg, vals, Prod.mk.injEq] at heq
    cases hp with
    | head => exact heq.1
    | tail _ hp => exact WpG.append_val_eq hG as xs heq.2 p hp

def WpD (depth : Nat) (interp : JEnv) (D : Ctx (JLabel Cont) Cont) : Prop :=
  ∀ p ∈ D, match p.2.1 with
    | .outer l => l = p.2.2
    | .loc id => id < depth ∧ interp id = p.2.2
    | .probe => False

theorem wpD_extend (depth : Nat) {sig : List (List Ty)} {interp interp' : JEnv}
    {D : Ctx (JLabel Cont) Cont} (hD : WpD depth interp D)
    (Js₂ : Tup Cont sig) (heq_lt : ∀ {ts} id, id < depth → interp' (ts := ts) id = interp id)
    (heq_in : ∀ {ts} {id : Nat} {j₂ : Cont ts},
      ⟨ts, .loc id, j₂⟩ ∈ Tup.zip (locLabels (L := Cont) sig depth) Js₂ → interp' id = j₂) :
    WpD (depth + sig.length) interp' (Tup.zip (locLabels (L := Cont) sig depth) Js₂ ++ D) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · have hmem : ∀ (s : List (List Ty)) (d : Nat) (js : Tup Cont s) q,
        q ∈ Tup.zip (locLabels (L := Cont) s d) js →
        ∃ id, q.2.1 = .loc id ∧ d ≤ id ∧ id < d + s.length := fun s d js q hq => by
      induction s generalizing d with
      | nil => cases hq
      | cons _ s ih =>
        cases hq with
        | head => exact ⟨d, rfl, Nat.le_refl _, by simp⟩
        | tail _ hq =>
          rcases ih (d + 1) js.2 hq with ⟨i, hi, h1, h2⟩
          exact ⟨i, hi, by omega, by simp only [List.length_cons] at h2 ⊢; omega⟩
    rcases hmem sig depth Js₂ p hp with ⟨id, hloc, _, hhi⟩
    rcases p with ⟨ts', j₁, j₂⟩; simp only at hloc ⊢; subst hloc
    exact ⟨hhi, heq_in hp⟩
  · have h := hD p hp
    cases h1 : p.2.1 with
    | outer l => rw [h1] at h; exact h
    | loc id => rw [h1] at h; exact ⟨by omega, (heq_lt _ h.1).trans h.2⟩
    | probe => rw [h1] at h; exact False.elim h

def memberIdx {α : Type} : {a : α} → {as : List α} → Member a as → Nat
  | _, _, .here => 0
  | _, _, .there i => memberIdx i + 1

def tupTrue : (sig : List (List Ty)) → Tup Cont sig
  | [] => ()
  | _ :: sig => (fun _ _ => True, tupTrue sig)

theorem tupTrue_mem : ∀ (sig : List (List Ty)) (d : Nat) {ts} {id : Nat} {j₂ : Cont ts},
    ⟨ts, .loc id, j₂⟩ ∈ Tup.zip (locLabels (L := Cont) sig d) (tupTrue sig) →
    d ≤ id ∧ id < d + sig.length ∧ j₂ = fun _ _ => True
  | _ :: _, _, _, _, _, .head _ => ⟨Nat.le_refl _, by simp, rfl⟩
  | _ :: sig, d, _, _, _, .tail _ h => by
    rcases tupTrue_mem sig (d + 1) h with ⟨hle, hhi, rfl⟩
    exact ⟨by omega, by simp only [List.length_cons]; omega, rfl⟩

theorem pureTrue_closed (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    {sig : List (List Ty)} → (bs : Blocks Val Cont rs sig) →
    Closed Γ Q X bs (tupTrue sig)
  | [], .nil => trivial
  | _ :: _, .cons _ bs => ⟨fun _ _ _ => trivial, pureTrue_closed Γ Q X bs⟩

def spliceTup (jId : Nat) (jTs : List Ty) (P : Cont jTs) :
    (sig : List (List Ty)) → Nat → Tup Cont sig
  | [], _ => ()
  | ts :: sig, id =>
    let hd : Cont ts :=
      if id == jId then
        match listTyDecEq ts jTs with | isTrue h => h ▸ P | isFalse _ => fun _ _ => True
      else fun _ _ => True
    (hd, spliceTup jId jTs P sig (id + 1))

theorem spliceTup_mem_eq {jId : Nat} {jTs : List Ty} {P : Cont jTs} :
    ∀ (sig : List (List Ty)) (d : Nat) {ts} {id : Nat} {j₂ : Cont ts},
      ⟨ts, .loc id, j₂⟩ ∈ Tup.zip (locLabels (L := Cont) sig d) (spliceTup jId jTs P sig d) →
      j₂ = mkSpliceInterp jId jTs P (fun _ _ _ => True) id
  | _ :: _, _, _, _, _, .head _ => rfl
  | _ :: sig, d, _, _, _, .tail _ h => spliceTup_mem_eq sig (d + 1) h

theorem spliceTup_closed (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost)
    (jId : Nat) (jTs : List Ty) (P : Cont jTs) :
    {sig : List (List Ty)} → (bs : Blocks Val Cont rs sig) → (d : Nat) →
    (∀ {ts} (i : Member ts sig), d + memberIdx i = jId →
      ∃ (heq : ts = jTs), ∀ xs m, wp Γ Q X (bs.get i xs) m → P (heq ▸ xs) m) →
    Closed Γ Q X bs (spliceTup jId jTs P sig d)
  | [], .nil, _, _ => trivial
  | ts :: _, .cons _ bs, d, hb => by
    refine ⟨fun xs m hw => ?_, spliceTup_closed Γ Q X jId jTs P bs (d + 1) fun i hi =>
      hb (.there i) (by simp only [memberIdx] at hi ⊢; omega)⟩
    simp only [spliceTup]
    cases hid : (d == jId)
    · trivial
    · rcases hb .here (by simp [memberIdx, beq_iff_eq.1 hid]) with ⟨rfl, hp⟩
      cases hd : listTyDecEq ts ts with
      | isFalse hne => exact absurd rfl hne
      | isTrue _ => exact hp xs m hw

def contFromEnv (env : List (Nat × ((ts : List Ty) × JLabel Cont ts))) (id : Nat)
    (ts : List Ty) : Cont ts :=
  match lookupLblEnv env id ts with
  | some j => evalJLbl (fun _ _ _ => False) j
  | none => fun _ _ => True

def tupFromEnv (env : List (Nat × ((ts : List Ty) × JLabel Cont ts))) :
    (sig : List (List Ty)) → Nat → Tup Cont sig
  | [], _ => ()
  | ts :: sig, id => (contFromEnv env id ts, tupFromEnv env sig (id + 1))

theorem tupFromEnv_mem (env : List (Nat × ((ts : List Ty) × JLabel Cont ts))) :
    ∀ (sig : List (List Ty)) (d : Nat) {ts} {id : Nat} {j₂ : Cont ts},
      ⟨ts, .loc id, j₂⟩ ∈ Tup.zip (locLabels (L := Cont) sig d) (tupFromEnv env sig d) →
      d ≤ id ∧ j₂ = contFromEnv env id ts
  | _ :: _, _, _, _, _, .head _ => ⟨Nat.le_refl _, rfl⟩
  | _ :: sig, d, _, _, _, .tail _ h =>
    have ih := tupFromEnv_mem env sig (d + 1) h
    ⟨Nat.le_trans (Nat.le_succ _) ih.1, ih.2⟩

theorem tupFromEnv_get (env : List (Nat × ((ts : List Ty) × JLabel Cont ts))) :
    ∀ (sig : List (List Ty)) (d : Nat) {ts} (i : Member ts sig),
      (tupFromEnv env sig d).get i = contFromEnv env (d + memberIdx i) ts
  | _ :: _, d, _, .here => by simp [tupFromEnv, Tup.get, memberIdx]
  | _ :: sig, d, _, .there i => by
    simp only [tupFromEnv, Tup.get, memberIdx]
    rw [tupFromEnv_get env sig (d + 1) i, show d + 1 + memberIdx i = d + (memberIdx i + 1) by omega]

theorem lookupLblEnv_mkEnv_outer {V : Ty → Type} {rs : List Ty} (keep : Nat → Bool) :
    (sig : List (List Ty)) → (bs : SBlocks V (JLabel Cont) rs sig) → (id : Nat) →
    (Js : Tup Cont (filterSBlocks keep sig bs id).sig) →
    ∀ q ts {j : JLabel Cont ts},
      lookupLblEnv ((filterSBlocks keep sig bs id).mkEnv (Js.map fun _ l => .outer l)) q ts =
        some j →
      ∃ J : Cont ts, j = .outer J
  | [], .nil, _, (), _, _, _, h => by cases h
  | ts₀ :: sig, .cons _ bs, id, Js, q, ts, j, h => by
    cases hk : keep id
    · revert Js h; rw [filterSBlocks_cons_false hk]; intro Js h
      exact lookupLblEnv_mkEnv_outer keep sig bs (id + 1) Js q ts h
    · revert Js h; rw [filterSBlocks_cons_true hk]; intro Js h
      simp only [Tup.map, lookupLblEnv] at h
      by_cases hq : q = id
      · subst hq; simp only [beq_self_eq_true, ↓reduceIte] at h
        cases hdec : listTyDecEq ts₀ ts with
        | isTrue heq => rw [hdec] at h; cases h; subst heq; exact ⟨Js.1, rfl⟩
        | isFalse _ =>
          rw [hdec] at h
          exact lookupLblEnv_mkEnv_outer keep sig bs (q + 1) Js.2 q ts h
      · have hne : (q == id) = false := beq_false_of_ne hq
        simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
        exact lookupLblEnv_mkEnv_outer keep sig bs (id + 1) Js.2 q ts h

theorem filterSBlocks_member {V : Ty → Type} {rs : List Ty} (keep : Nat → Bool) :
    (sig : List (List Ty)) → (bs : SBlocks V (JLabel Cont) rs sig) → (d : Nat) →
    {ts : List Ty} → (i : Member ts sig) → keep (d + memberIdx i) = true →
    ∃ i' : Member ts (filterSBlocks keep sig bs d).sig,
      (∀ a, (filterSBlocks keep sig bs d).blocks.get i' a = bs.get i a) ∧
      ∀ Js : Tup Cont (filterSBlocks keep sig bs d).sig,
        lookupLblEnv ((filterSBlocks keep sig bs d).mkEnv (Js.map fun _ l => .outer l))
          (d + memberIdx i) ts = some (.outer (Js.get i'))
  | ts :: sig, .cons b bs, d, _, .here, hk => by
    simp only [memberIdx, Nat.add_zero] at hk ⊢
    rw [filterSBlocks_cons_true hk]
    refine ⟨.here, fun _ => rfl, fun Js => ?_⟩
    simp only [Tup.map, lookupLblEnv, beq_self_eq_true, ↓reduceIte]
    cases listTyDecEq ts ts with | isFalse h => exact absurd rfl h | isTrue _ => rfl
  | ts₀ :: sig, .cons b bs, d, ts, .there i, hk => by
    simp only [memberIdx] at hk ⊢
    have hk' : keep ((d + 1) + memberIdx i) = true := by
      rwa [show d + 1 + memberIdx i = d + (memberIdx i + 1) by omega]
    rcases filterSBlocks_member keep sig bs (d + 1) i hk' with ⟨i', hblk, hlkp⟩
    cases hkd : keep d
    · rw [filterSBlocks_cons_false hkd]
      refine ⟨i', hblk, fun Js => ?_⟩
      rw [show d + (memberIdx i + 1) = d + 1 + memberIdx i by omega]
      exact hlkp Js
    · rw [filterSBlocks_cons_true hkd]
      refine ⟨.there i', hblk, fun Js => ?_⟩
      have hne : (d + (memberIdx i + 1) == d) = false := by simp [beq_eq_false_iff_ne]
      simp only [Tup.map, lookupLblEnv, hne, Bool.false_eq_true, ↓reduceIte]
      rw [show d + (memberIdx i + 1) = d + 1 + memberIdx i by omega]
      exact hlkp Js.2

theorem lookupLblEnv_mkEnv_false {V : Ty → Type} {rs : List Ty} (keep : Nat → Bool) :
    (sig : List (List Ty)) → (bs : SBlocks V (JLabel Cont) rs sig) → (d : Nat) →
    (Js : Tup Cont (filterSBlocks keep sig bs d).sig) →
    ∀ q ts, keep q = false →
    lookupLblEnv ((filterSBlocks keep sig bs d).mkEnv (Js.map fun _ l => .outer l)) q ts = none
  | [], .nil, _, (), _, _, _ => rfl
  | _ :: sig, .cons _ bs, d, Js, q, ts, hq => by
    cases hk : keep d
    · revert Js; rw [filterSBlocks_cons_false hk]; intro Js
      exact lookupLblEnv_mkEnv_false keep sig bs (d + 1) Js q ts hq
    · revert Js; rw [filterSBlocks_cons_true hk]; intro Js
      have hne : (q == d) = false := by
        simp only [beq_eq_false_iff_ne]; intro heq; subst heq; cases hq.symm.trans hk
      simp only [Tup.map, lookupLblEnv, hne, Bool.false_eq_true, ↓reduceIte]
      exact lookupLblEnv_mkEnv_false keep sig bs (d + 1) Js.2 q ts hq

theorem filterRes_kept_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} (interp : JEnv)
    {sig₁ : List (List Ty)} {ids₁ : List Nat}
    {bs₁ : SBlocks (OptV Val) (JLabel Cont) rs sig₁}
    {mkEnv₁ : Tup (JLabel Cont) sig₁ → List (Nat × ((ts : List Ty) × JLabel Cont ts))}
    (k₁ : Expr (OptV Val) (JLabel Cont) rs) (m : Mem 64) :
    ∀ (r : FilterRes (OptV Val) Cont rs), r = ⟨sig₁, ids₁, bs₁, mkEnv₁⟩ →
      wp Γ Q X (untagWith interp (.group (sig := r.sig)
        (fun Js => substLabelsB (r.mkEnv Js) (sblocksToBlocks r.blocks))
        (fun Js => substLabels (r.mkEnv Js) k₁))) m →
      wp Γ Q X (untagWith interp (.group (sig := sig₁)
        (fun Js => substLabelsB (mkEnv₁ Js) (sblocksToBlocks bs₁))
        (fun Js => substLabels (mkEnv₁ Js) k₁))) m
  | _, rfl, h => h

theorem sblocksClosed_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (reach : List Nat) (lo hi : Nat) :
    {sig : List (List Ty)} → (bs : SBlocks (OptV V) (JLabel L) rs sig) → (d : Nat) →
    SBlocksClosed reach lo hi d bs →
    ∀ {ts} (i : Member ts sig), d + memberIdx i ∈ reach →
    ∀ x ∈ collectJumps lo hi (bs.get i (dummyArgOptTup ts)) [], x ∈ reach
  | _ :: _, .cons _ _, _, h, _, .here, hin => h.1 hin
  | _ :: _, .cons _ bs, d, h, ts, .there i, hin =>
    sblocksClosed_get reach lo hi bs (d + 1) h.2 i
      (by rwa [show d + 1 + memberIdx i = d + (memberIdx i + 1) by omega])

theorem locLabels_zip_swap {L₁ L₂ : List Ty → Type} :
    ∀ (sig : List (List Ty)) (d : Nat) {ts} {q : Nat},
      ⟨ts, .loc q, .loc q⟩ ∈ Tup.zip (locLabels (L := L₁) sig d) (locLabels (L := L₂) sig d) →
      ⟨ts, .loc q, .loc q⟩ ∈ Tup.zip (locLabels (L := L₂) sig d) (locLabels (L := L₂) sig d)
  | _ :: _, _, _, _, .head _ => .head _
  | _ :: sig, d, _, _, .tail _ h => .tail _ (locLabels_zip_swap sig (d + 1) h)

theorem boundedD_loc_lt {L₁ L₂ : List Ty → Type} {depth : Nat} {Dk : Ctx (JLabel L₁) (JLabel L₂)}
    (hBD : BoundedD depth Dk) {ts : List Ty} {j₁ : JLabel L₁ ts} {id : Nat}
    (hp : ⟨ts, j₁, .loc id⟩ ∈ Dk) : id < depth := by
  have h := hBD _ hp; cases j₁ <;> simp only [isLocLbl] at h
  · cases h.2
  · exact h.1 ▸ h.2
  · cases h.2

theorem simplifyGroup_wp_aux {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {K : Ty → Type} {KL : List Ty → Type}
    {G : Ctx (Arg (OptV Val)) Val} {D : Ctx (JLabel Cont) Cont}
    {e₁ : Expr (Arg (OptV Val)) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
    (hw : Wf G D e₁ e₂) :
    ∀ {Gk : Ctx (Arg (OptV K)) (Arg (OptV Val))} {Dk : Ctx (JLabel KL) (JLabel Cont)}
      {ek : Expr (Arg (OptV K)) (JLabel KL) rs} (_hwk : Wf Gk Dk ek e₁)
      (depth : Nat) (interp : JEnv),
      WpG G → WpD depth interp D → BoundedD depth Dk →
      ∀ m, wp Γ Q X e₂ m → wp Γ Q X (untagWith interp (simplifyGroup depth e₁)) m := by
  induction hw using Wf.induct with
  | let_ hop _ ih =>
    intro Gk Dk ek hwk depth interp hG hD hBD m hw2
    rcases hwk.rhs_let with ⟨opk, kk, rfl, _, hkk⟩
    cases hop with
    | mk code hargs =>
      simp only [simplifyGroup, flattenOp, untagWith, wp, Op.wp] at hw2 ⊢
      rw [trel_argsSweep_flatten_vals hG hargs]
      exact OpCode.wp_mono code _ (fun r => ih (toArgTup (someTup _ r)) r
        (hkk (toArgTup (noneTup _)) (toArgTup (someTup _ r))) depth interp
        (hG.append_some r) hD hBD m) hw2
  | load t ha _ ih =>
    intro Gk Dk ek hwk depth interp hG hD hBD m ⟨v, hv, hw2⟩
    rcases hwk.rhs_load with ⟨ak, kk, rfl, _, hkk⟩
    simp only [simplifyGroup, untagWith, wp]
    rw [argSweep_flatten_val hG ha]
    exact ⟨v, hv, ih (.var (some v)) v (hkk (.var none) (.var (some v))) depth interp
      (hG.cons_some v) hD hBD m hw2⟩
  | store hv ha _ ih =>
    intro Gk Dk ek hwk depth interp hG hD hBD m ⟨hok, hw2⟩
    rcases hwk.rhs_store with ⟨vk, ak, kk, rfl, _, _, hkk⟩
    simp only [simplifyGroup, untagWith, wp]
    rw [argSweep_flatten_val hG hv, argSweep_flatten_val hG ha]
    exact ⟨hok, ih hkk depth interp hG hD hBD _ hw2⟩
  | call f hargs _ ih =>
    intro Gk Dk ek hwk depth interp hG hD hBD m ⟨P, E, hΓ, hP, hE⟩
    rcases hwk.rhs_call with ⟨argsk, kk, rfl, _, hkk⟩
    simp only [simplifyGroup, untagWith, wp]
    rw [trel_argsSweep_flatten_vals hG hargs]
    exact ⟨P, E, hΓ, fun r m' hp => ih (toArgTup (someTup _ r)) r
      (hkk (toArgTup (noneTup _)) (toArgTup (someTup _ r))) depth interp
      (hG.append_some r) hD hBD m' (hP r m' hp), hE⟩
  | jnz hc _ _ iht ihe =>
    intro Gk Dk ek hwk depth interp hG hD hBD m hw2
    rcases hwk.rhs_jnz with ⟨ck, tk, ek', rfl, _, htk, hek⟩
    simp only [simplifyGroup, untagWith, wp] at hw2 ⊢
    rw [argSweep_flatten_val hG hc]
    exact ⟨fun h => iht htk depth interp hG hD hBD m (hw2.1 h),
           fun h => ihe hek depth interp hG hD hBD m (hw2.2 h)⟩
  | @jump _ _ _ j₁ _ _ _ hj hargs =>
    intro Gk Dk ek hwk depth interp hG hD _ m hw2
    have hd := hD _ hj
    cases j₁ with
    | outer l =>
      simp only [simplifyGroup, untagWith, wp] at hw2 ⊢
      rw [trel_argsSweep_flatten_vals hG hargs]; dsimp only at hd; rwa [hd]
    | loc id =>
      simp only [simplifyGroup, untagWith, wp] at hw2 ⊢
      rw [trel_argsSweep_flatten_vals hG hargs]; dsimp only at hd; rwa [hd.2]
    | probe => exact False.elim hd
  | ret hvs =>
    intro _ _ _ _ _ _ hG _ _ m hw2
    simp only [simplifyGroup, untagWith, wp] at hw2 ⊢
    rwa [trel_argsSweep_flatten_vals hG hvs]
  | exit f hargs =>
    intro _ _ _ _ _ _ hG _ _ m hw2
    simp only [simplifyGroup, untagWith, wp] at hw2 ⊢
    rwa [trel_argsSweep_flatten_vals hG hargs]
  | hlt =>
    intro _ _ _ _ _ _ _ _ _ _ hw2; exact hw2
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro Gk Dk ek hwk depth interp hG hD hBD m hw2
    rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩
    let d' := depth + sig.length
    let locK := locLabels (L := KL) sig depth
    let loc₁ := locLabels (L := Cont) sig depth
    have hD_loc := boundedD_append_loc sig depth depth (Nat.le_refl _) hBD
    have hD_c := boundedD_lblCompat hD_loc
    have hb0 : OuterWfS false [] (Tup.zip locK loc₁ ++ Dk)
        (simplifyGroupB d' (bk locK)) (simplifyGroupB d' (b₁ loc₁)) := by
      let rec go : ∀ (s : List (List Ty)) (bsK : Blocks (Arg (OptV K)) (JLabel KL) rs s)
          (bs₁ : Blocks (Arg (OptV Val)) (JLabel Cont) rs s),
          (∀ {ts} (i : Member ts s) xsK xs₁,
            Wf (Tup.zip xsK xs₁ ++ Gk) (Tup.zip locK loc₁ ++ Dk)
              (bsK.get i xsK) (bs₁.get i xs₁)) →
          OuterWfS false [] (Tup.zip locK loc₁ ++ Dk)
            (simplifyGroupB d' bsK) (simplifyGroupB d' bs₁)
        | [], .nil, .nil, _ => .nil
        | _ :: _, .cons _ bsK, .cons _ bs₁, hbs =>
          .cons (fun a₁ a₂ _ _ => simplifyGroup_outerWf (hbs .here a₁ a₂) false d'
              (fun h => by cases h) hD_loc)
            (go _ bsK bs₁ fun i => hbs (.there i))
      exact go sig (bk locK) (b₁ loc₁) fun i xsK xs₁ => WfB.get (hbk locK loc₁) i xsK xs₁
    have hk0 : OuterWf false [] (Tup.zip locK loc₁ ++ Dk)
        (simplifyGroup d' (kk locK)) (simplifyGroup d' (k₁ loc₁)) :=
      simplifyGroup_outerWf (hkk locK loc₁) false d' (fun h => by cases h) hD_loc
    let kK' := simplifyGroup d' (kk locK)
    let k₁' := simplifyGroup d' (k₁ loc₁)
    let bsK' := simplifyGroupB d' (bk locK)
    let bs₁' := simplifyGroupB d' (b₁ loc₁)
    have heq_init : collectJumps depth d' kK' [] = collectJumps depth d' k₁' [] :=
      outerWf_collectJumps depth d' hD_c hk0 []
    have heq_adj : blockAdj depth d' depth bsK' = blockAdj depth d' depth bs₁' :=
      outerWfS_blockAdj depth d' hD_c depth hb0
    let reach := reachLoop (blockAdj depth d' depth bs₁') (sig.length + 1)
      (collectJumps depth d' k₁' [])
    let keep : Nat → Bool := fun x => reach.contains x
    have hadj_bd := blockAdj_bounds depth d' depth bsK'
    have hinit_bd := collectJumps_bounds depth d' kK' (acc := []) (fun _ h => (by cases h))
    have hinit_nd := collectJumps_nodup depth d' kK' List.nodup_nil
    have hreach := reachLoop_spec (blockAdj depth d' depth bsK') depth sig.length
      (by simpa [d'] using hadj_bd) (sig.length + 1) (collectJumps depth d' kK' [])
      (by simpa [d'] using hinit_bd) hinit_nd (by omega)
    rw [heq_init, heq_adj] at hreach
    have hsbcK := sblocksClosed_of_adj reach depth d' depth bsK'
      (by simpa only [heq_adj] using hreach.2)
    have hrest_sub := restSub_loc_drop sig depth hBD fun _ hp => hp
    have hkept : wp Γ Q X (untagWith interp (.group
        (sig := (filterSBlocks keep sig bs₁' depth).sig)
        (fun Js => substLabelsB ((filterSBlocks keep sig bs₁' depth).mkEnv Js)
          (sblocksToBlocks (filterSBlocks keep sig bs₁' depth).blocks))
        (fun Js => substLabels ((filterSBlocks keep sig bs₁' depth).mkEnv Js) k₁'))) m := by
      simp only [untagWith, wp]
      intro Js_out hclosed_out
      let res₁ := filterSBlocks keep sig bs₁' depth
      let Js_lbl : Tup (JLabel Cont) res₁.sig := Js_out.map fun _ l => .outer l
      let env₁ := res₁.mkEnv Js_lbl
      let Js₂ : Tup Cont sig := tupFromEnv env₁ sig depth
      let interp' : JEnv := fun {ts} id => if id < depth then interp id else contFromEnv env₁ id ts
      have hD' : WpD d' interp' (Tup.zip loc₁ Js₂ ++ D) :=
        wpD_extend depth hD Js₂ (fun id hlt => by simp [interp', hlt]) fun hmem => by
          rcases tupFromEnv_mem env₁ sig depth hmem with ⟨hle, rfl⟩
          simp [interp', Nat.not_lt_of_ge hle]
      let D_keep : Ctx (JLabel KL) (JLabel Cont) :=
        (Tup.zip locK loc₁).filter
          (fun p => match p.2.1 with | .loc d => reach.contains d | _ => true) ++ Dk
      have hrest_keep : RestSub depth d' (Tup.zip locK loc₁ ++ Dk) D_keep :=
        restSub_loc_drop sig depth hBD fun _ hp => List.mem_append_right _ hp
      have hmem_keep : ∀ x ∈ reach, ∀ {ts},
          ⟨ts, JLabel.loc x, JLabel.loc x⟩ ∈ Tup.zip locK loc₁ ++ Dk →
          ⟨ts, JLabel.loc x, JLabel.loc x⟩ ∈ D_keep := fun x hxr {ts} hmem => by
        rcases List.mem_append.1 hmem with hmem | hmem
        · exact List.mem_append_left _ (List.mem_filter.2 ⟨hmem, by simp [hxr]⟩)
        · exact List.mem_append_right _ hmem
      have hagree : ∀ p ∈ D_keep, match p.2.2 with
          | .loc id => interp' (ts := p.1) id = mkKeepInterp env₁ interp (ts := p.1) id
          | _ => True := fun p hp => by
        rcases List.mem_append.1 hp with hp | hp
        · rcases List.mem_filter.1 hp with ⟨hp_loc, hp_rch⟩
          rcases mem_locLabels_zip sig depth hp_loc with ⟨id, h1, h2, hge, hhi⟩
          rcases p with ⟨ts', j₁, j₂⟩; simp only at h1 h2 hp_rch; subst h1 h2
          have hlt_d := Nat.not_lt_of_ge hge
          have hfl := filterSBlocks_mkEnv_lookup keep sig bs₁' bs₁' depth hge hhi
            (locLabels_zip_swap sig depth hp_loc) hp_rch Js_lbl Js_lbl rfl
          rcases hfl with ⟨l₁, _, hl₁, _, _⟩
          rcases lookupLblEnv_mkEnv_outer keep sig bs₁' depth Js_out _ ts' hl₁ with ⟨J, rfl⟩
          simp only [interp', hlt_d, ↓reduceIte, contFromEnv, mkKeepInterp, env₁, res₁]
          rw [hl₁]; rfl
        · rcases p with ⟨ts', j₁, j₂⟩; cases j₂ with
          | outer _ | probe => trivial
          | loc _ =>
            have hbd := boundedD_loc_lt hBD hp
            have hn := filterSBlocks_mkEnv_lt_none keep sig bs₁' depth Js_lbl _ ts' hbd
            simp only [interp', hbd, ↓reduceIte, mkKeepInterp, env₁, res₁, hn]
      have hclosed₂ : Closed Γ Q X (b₂ Js₂) Js₂ := by
        rw [closed_iff]
        intro ts i xs m' hb'
        rw [tupFromEnv_get]
        cases hkid : keep (depth + memberIdx i)
        · have hn := lookupLblEnv_mkEnv_false keep sig bs₁' depth Js_out
            (depth + memberIdx i) ts hkid
          simp only [contFromEnv, env₁, Js_lbl, res₁]; rw [hn]; trivial
        · rcases filterSBlocks_member keep sig bs₁' depth i hkid with ⟨i', hblk, hlkp⟩
          simp only [contFromEnv, env₁, Js_lbl, res₁]; rw [hlkp Js_out]; simp only [evalJLbl]
          have hw_i := ihb loc₁ Js₂ i (toArgTup (someTup ts xs)) xs
            (WfB.get (hbk locK loc₁) i (dummyArgOptTup ts) (toArgTup (someTup ts xs)))
            d' interp' (hG.append_some xs) hD' hD_loc m' hb'
          have hblk_ow0 : OuterWf false [] (Tup.zip locK loc₁ ++ Dk)
              (bsK'.get i (dummyArgOptTup ts)) (bs₁'.get i (toArgTup (someTup ts xs))) := by
            simpa only [bsK', bs₁', simplifyGroupB_get] using simplifyGroup_outerWf
              (WfB.get (hbk locK loc₁) i (dummyArgOptTup ts) (toArgTup (someTup ts xs)))
              false d' (fun h => by cases h) hD_loc
          have hblk_keep : OuterWf false [] D_keep
              (bsK'.get i (dummyArgOptTup ts)) (bs₁'.get i (toArgTup (someTup ts xs))) :=
            outerWf_restrict_of_collect depth d' hD_c hrest_keep hblk_ow0 hblk_ow0 fun x hx =>
              hmem_keep x (sblocksClosed_get reach depth d' bsK' depth hsbcK i
                (List.contains_iff_mem.1 hkid) x hx)
          have hcongr := outerWf_wp_congr_rhs (Γ := Γ) (Q := Q) (X := X) hagree hblk_keep m'
            (by simpa only [bs₁', simplifyGroupB_get] using hw_i)
          have hsub := substLabels_wp (Γ := Γ) (Q := Q) (X := X) env₁ interp
            (bs₁'.get i (toArgTup (someTup ts xs))) m' hcongr
          dsimp only [res₁, env₁] at hsub
          rw [← hblk (toArgTup (someTup ts xs)), ← sblocksToBlocks_get,
            ← substLabelsB_get, ← untagBlocksWith_get] at hsub
          rw [closed_iff] at hclosed_out
          exact hclosed_out i' xs m' hsub
      have hw1' := ihk loc₁ Js₂ (hkk locK loc₁) d' interp' hG hD' hD_loc m (hw2 Js₂ hclosed₂)
      have hk_keep : OuterWf false [] D_keep kK' k₁' :=
        outerWf_restrict_of_collect depth d' hD_c hrest_keep hk0 hk0 fun x hx =>
          hmem_keep x (hreach.1 x (heq_init ▸ hx))
      exact substLabels_wp env₁ interp k₁' m (outerWf_wp_congr_rhs hagree hk_keep m hw1')
    simp only [simplifyGroup]; unfold handleGroup; dsimp only
    have hlen1 := filterSBlocks_ids_len keep sig bs₁' depth
    rcases hr₁ : filterSBlocks keep sig bs₁' depth with ⟨sig₁', ids₁', bs₁'', mkEnv₁⟩
    rw [hr₁] at hlen1
    cases sig₁' with
    | nil =>
      cases bs₁''; dsimp only
      let Js₂ := tupTrue sig
      let interp' : JEnv := fun {ts} id =>
        if depth ≤ id && id < d' then (fun _ _ => True) else interp id
      have hD' : WpD d' interp' (Tup.zip loc₁ Js₂ ++ D) :=
        wpD_extend depth hD Js₂
          (fun id hlt => by simp [interp', show ¬ depth ≤ id by omega])
          (fun {ts} {id} {j₂} hmem => by
            rcases tupTrue_mem sig depth hmem with ⟨hge, hhi, rfl⟩
            simp [interp', hge, d', hhi])
      have hw1' := ihk loc₁ Js₂ (hkk locK loc₁) d' interp' hG hD' hD_loc m
        (hw2 Js₂ (pureTrue_closed Γ Q X (b₂ Js₂)))
      have hk_D : OuterWf false [] Dk kK' k₁' := by
        refine outerWf_restrict_of_collect depth d' hD_c hrest_sub hk0 hk0 fun x hx {ts'} _ => ?_
        have hnil := (filterSBlocks_ids_spec keep sig bs₁' depth).2.1 (by simp [hr₁])
        have hxr := hreach.1 x (heq_init ▸ hx)
        have hbdx := hinit_bd x hx
        have hf := hnil x hbdx.1 hbdx.2
        simp only [keep, List.contains_eq_mem, decide_eq_false_iff_not] at hf
        exact False.elim (hf hxr)
      have hagree : ∀ p ∈ Dk, match p.2.2 with
          | .loc id => interp' (ts := p.1) id = interp (ts := p.1) id
          | _ => True := fun p hp => by
        rcases p with ⟨ts', j₁, j₂⟩; cases j₂ with
        | outer _ | probe => trivial
        | loc _ =>
          have hlt : ¬ depth ≤ _ := Nat.not_le_of_lt (boundedD_loc_lt hBD hp)
          simp [interp', hlt]
      exact outerWf_wp_congr_rhs hagree hk_D m hw1'
    | cons jTs sig_rest =>
      cases sig_rest with
      | nil =>
        cases bs₁'' with | cons b₁' bt₁ => cases bt₁ with | nil =>
        cases ids₁' with
        | nil => simp at hlen1
        | cons jId id_rest =>
          cases id_rest with
          | cons _ _ => simp at hlen1
          | nil =>
            change wp Γ Q X (untagWith interp
              (if !hasJumpTo jId (b₁' (dummyArgOptTup jTs)) &&
                  (isJumpTo jId jTs k₁' ||
                    (exprSizeJ (b₁' (dummyArgOptTup jTs)) ≤ 16 && countJumps jId k₁' == 1))
                then spliceBlock jId jTs b₁' k₁'
                else .group (sig := [jTs])
                  (fun Js => substLabelsB (mkEnv₁ Js) (sblocksToBlocks (.cons b₁' .nil)))
                  (fun Js => substLabels (mkEnv₁ Js) k₁'))) m
            split
            · rename_i hcond
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
              have hone := (filterSBlocks_ids_spec keep sig bs₁' depth).2.2 jTs jId
                (by simp [hr₁]) (by simp [hr₁])
              let J_splice : Cont jTs := fun vs m' =>
                ∀ (a₁ : Tup (Arg (OptV Val)) jTs), vals (argsSweep a₁) = vs →
                  wp Γ Q X (untagWith interp (b₁' a₁)) m'
              let Js₂ := spliceTup jId jTs J_splice sig depth
              let interp' : JEnv := fun {ts} id =>
                if id < depth then interp id
                else mkSpliceInterp jId jTs J_splice (fun _ _ _ => True) id
              have hD' : WpD d' interp' (Tup.zip loc₁ Js₂ ++ D) :=
                wpD_extend depth hD Js₂ (fun id hlt => by simp [interp', hlt]) fun hmem => by
                  have hge := locLabels_zip_ge sig depth Js₂ hmem
                  rw [spliceTup_mem_eq sig depth hmem]
                  simp [interp', Nat.not_lt_of_ge hge]
              have hclosed₂ : Closed Γ Q X (b₂ Js₂) Js₂ := by
                refine spliceTup_closed Γ Q X jId jTs J_splice (b₂ Js₂) depth fun {ts} i hi => ?_
                have hkd : keep (depth + memberIdx i) = true := by rw [hi]; exact hone.2.2.1
                rcases filterSBlocks_member keep sig bs₁' depth i hkd with ⟨i', hblk, _⟩
                have hi'_eq : (filterSBlocks keep sig bs₁' depth).sig = [jTs] := by simp [hr₁]
                have hts : ts = jTs := by
                  have hi'' := hi'_eq ▸ i'
                  cases hi'' with | here => rfl | there k => exact nomatch k
                subst hts
                refine ⟨rfl, fun xs m' hb' a₁ ha₁ => ?_⟩
                have hres_fn : ∀ a, bs₁'.get i a = b₁' a := fun a => by
                  have hb_eq : ∀ r : FilterRes (OptV Val) Cont rs,
                      r = ⟨[ts], [jId], .cons b₁' .nil, mkEnv₁⟩ →
                      ∀ (j : Member ts r.sig), r.blocks.get j a = bs₁'.get i a →
                        b₁' a = bs₁'.get i a := by
                    rintro r rfl j hj; cases j with | here => exact hj | there k => exact nomatch k
                  exact (hb_eq _ hr₁ i' (hblk a)).symm
                have hres_i : bs₁'.get i a₁ = b₁' a₁ := hres_fn a₁
                have hw_i := ihb loc₁ Js₂ i a₁ xs
                  (WfB.get (hbk locK loc₁) i (dummyArgOptTup ts) a₁)
                  d' interp' (hG.append_val_eq a₁ xs ha₁) hD' hD_loc m' hb'
                have hbx_ow : OuterWf false [] (Tup.zip locK loc₁ ++ Dk)
                    (bsK'.get i (dummyArgOptTup ts)) (b₁' a₁) := by
                  rw [← hres_i]
                  simpa only [bsK', bs₁', simplifyGroupB_get] using simplifyGroup_outerWf
                    (WfB.get (hbk locK loc₁) i (dummyArgOptTup ts) a₁)
                    false d' (fun h => by cases h) hD_loc
                have hbx_dum : OuterWf false [] (Tup.zip locK loc₁ ++ Dk)
                    (bsK'.get i (dummyArgOptTup ts)) (b₁' (dummyArgOptTup ts)) := by
                  rw [← hres_fn (dummyArgOptTup ts)]
                  simpa only [bsK', bs₁', simplifyGroupB_get] using simplifyGroup_outerWf
                    (WfB.get (hbk locK loc₁) i (dummyArgOptTup ts) (dummyArgOptTup ts))
                    false d' (fun h => by cases h) hD_loc
                have hbc_1 := filterSBlocks_head_closed_eq reach depth d' sig bs₁' depth
                  (sblocksClosed_of_adj reach depth d' depth bs₁' hreach.2) hr₁
                have hbx_D : OuterWf false [] Dk (bsK'.get i (dummyArgOptTup ts)) (b₁' a₁) := by
                  refine outerWf_restrict_of_collect depth d' hD_c hrest_sub hbx_ow hbx_ow
                    fun x hx {ts'} _ => ?_
                  rw [outerWf_collectJumps depth d' hD_c hbx_dum []] at hx
                  have hxr := hbc_1.2 x hx
                  have hbdx := collectJumps_bounds depth d' _ (acc := [])
                    (fun _ h => (by cases h)) x hx
                  have hxeq := hone.2.2.2 x hbdx.1 hbdx.2 (List.contains_iff_mem.2 hxr)
                  subst hxeq
                  exact absurd (collectJumps_count_pos depth d' x _ hx)
                    (by simp [hasJumpTo] at hcond; simp [hcond.1])
                have hagree : ∀ p ∈ Dk, match p.2.2 with
                    | .loc id => interp' (ts := p.1) id = interp (ts := p.1) id
                    | _ => True := fun p hp => by
                  rcases p with ⟨ts', j₁, j₂⟩; cases j₂ with
                  | outer _ | probe => trivial
                  | loc _ => simp [interp', boundedD_loc_lt hBD hp]
                refine outerWf_wp_congr_rhs hagree hbx_D m' ?_
                rwa [← hres_i, show bs₁'.get i a₁ = simplifyGroup d' ((b₁ loc₁).get i a₁) from
                  simplifyGroupB_get d' (b₁ loc₁) i a₁]
              have hw1' :=
                ihk loc₁ Js₂ (hkk locK loc₁) d' interp' hG hD' hD_loc m (hw2 Js₂ hclosed₂)
              have hk_sp_sub : RestSub depth d' (Tup.zip locK loc₁ ++ Dk)
                  (⟨jTs, .loc jId, .loc jId⟩ :: Dk) :=
                restSub_loc_drop sig depth hBD fun _ hp => .tail _ hp
              have hk_sp : OuterWf false [] (⟨jTs, .loc jId, .loc jId⟩ :: Dk) kK' k₁' := by
                refine outerWf_restrict_of_collect depth d' hD_c hk_sp_sub hk0 hk0
                  fun x hx {ts'} hmem => ?_
                have hxr := hreach.1 x (heq_init ▸ hx)
                have hbdx := hinit_bd x hx
                have hxeq := hone.2.2.2 x hbdx.1 hbdx.2 (List.contains_iff_mem.2 hxr)
                subst hxeq
                have hts' : ts' = jTs := by
                  rcases List.mem_append.1 hmem with hmem | hmem
                  · exact filterSBlocks_single_ts_eq keep sig bs₁' depth hr₁ hmem
                  · exfalso; have := boundedD_loc_lt hBD hmem; have := hone.1; omega
                subst hts'; exact List.mem_cons_self
              have hagree_sp : ∀ p ∈ (⟨jTs, .loc jId, .loc jId⟩ :: Dk), match p.2.2 with
                  | .loc id =>
                    interp' (ts := p.1) id = mkSpliceInterp jId jTs J_splice interp (ts := p.1) id
                  | _ => True := fun p hp => by
                cases hp with
                | head =>
                  have hge : depth ≤ jId := hone.1
                  simp only [interp', Nat.not_lt_of_ge hge, ↓reduceIte, mkSpliceInterp,
                    beq_self_eq_true]
                  cases listTyDecEq jTs jTs with
                  | isFalse h => exact absurd rfl h | isTrue _ => rfl
                | tail _ hp =>
                  rcases p with ⟨ts', j₁, j₂⟩; cases j₂ with
                  | outer _ | probe => trivial
                  | loc id =>
                    have hbd := boundedD_loc_lt hBD hp
                    have hne : (id == jId) = false := by
                      simp only [beq_eq_false_iff_ne]; have := hone.1; omega
                    simp [interp', hbd, mkSpliceInterp, hne]
              have hw1'' := outerWf_wp_congr_rhs hagree_sp hk_sp m hw1'
              exact spliceBlock_wp jId jTs b₁' J_splice interp
                (fun args m' hp => hp args rfl) k₁' m hw1''
            · exact filterRes_kept_wp interp k₁' m _ hr₁ hkept
      | cons _ _ =>
        change wp Γ Q X (untagWith interp (.group (sig := _ :: _ :: _)
          (fun Js => substLabelsB (mkEnv₁ Js) (sblocksToBlocks bs₁''))
          (fun Js => substLabels (mkEnv₁ Js) k₁'))) m
        exact filterRes_kept_wp interp k₁' m _ hr₁ hkept

end SgImpl

open SgImpl

/-- Well-formedness preservation for `simplifyGroup` + `untagExpr`. -/
theorem simplifyGroup_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (Arg (OptV V₁)) (Arg (OptV V₂))} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {e₁ : Expr (Arg (OptV V₁)) (JLabel L₁) rs} {e₂ : Expr (Arg (OptV V₂)) (JLabel L₂) rs}
    (hwf : Wf G D e₁ e₂) {G' : Ctx (OptV V₁) (OptV V₂)} {G'' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
    (hG : SgRel G' G) (hS : SomeRelG G'' G') (hD : OuterD D D') (depth : Nat) :
    Wf G'' D' (untagExpr (simplifyGroup depth e₁)) (untagExpr (simplifyGroup depth e₂)) :=
  have hBD : BoundedD depth D := fun p hp => by
    have := hD p hp; cases h1 : p.2.1 <;> cases h2 : p.2.2 <;> simp_all [isLocLbl]
  outerWf_to_untag_wf hS hD (simplifyGroup_outerWf hwf true depth (fun _ => hG) hBD)

/-- `Func.simplifyGroup` preserves relational well-formedness `Func.Wf`. -/
theorem Func.simplifyGroup_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.simplifyGroup f).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hwf := hf (Arg (OptV V₁)) (Arg (OptV V₂)) (JLabel L₁) (JLabel L₂)
    (toArgTup (someTup as xs₁)) (toArgTup (someTup as xs₂))
  have hG : SgRel (Tup.zip (someTup as xs₁) (someTup as xs₂))
      (Tup.zip (toArgTup (someTup as xs₁)) (toArgTup (someTup as xs₂))) := by
    simpa using SgRel.append_toArgTup (G' := []) (G := []) (fun _ h => (by cases h))
      (someTup as xs₁) (someTup as xs₂)
  have hS : SomeRelG (Tup.zip xs₁ xs₂) (Tup.zip (someTup as xs₁) (someTup as xs₂)) := by
    simpa using SomeRelG.append_some (G' := []) (G := []) (fun _ h => (by cases h)) xs₁ xs₂
  exact LeanQbe.T.simplifyGroup_wf hwf hG hS (fun _ h => (by cases h)) 0

/-- Weakest-precondition refinement for `simplifyGroup` + `untagExpr`. -/
theorem simplifyGroup_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {K : Ty → Type} {KL : List Ty → Type}
    {G : Ctx (Arg (OptV Val)) Val} {D : Ctx (JLabel Cont) Cont}
    {e₁ : Expr (Arg (OptV Val)) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
    (hw : Wf G D e₁ e₂)
    {Gk : Ctx (Arg (OptV K)) (Arg (OptV Val))} {Dk : Ctx (JLabel KL) (JLabel Cont)}
    {ek : Expr (Arg (OptV K)) (JLabel KL) rs} (hwk : Wf Gk Dk ek e₁)
    (depth : Nat) (hG : WpG G)
    (hD : ∀ p ∈ D, match p.2.1 with | .outer l => l = p.2.2 | _ => False)
    (hDk : BoundedD depth Dk) (m : Mem 64) (hw2 : wp Γ Q X e₂ m) :
    wp Γ Q X (untagExpr (simplifyGroup depth e₁)) m :=
  untagWith_false_wp (simplifyGroup depth e₁) m
    (simplifyGroup_wp_aux hw hwk depth (fun _ _ _ => False) hG
      (fun p hp => by have h := hD p hp; cases h1 : p.2.1 <;> simp_all) hDk m hw2)

/-- `Func.simplifyGroup` refines function contracts: any source contract holds on
`Func.simplifyGroup f`. -/
theorem Func.simplifyGroup_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.simplifyGroup f) xs m Q X := by
  have hwf := hf (Arg (OptV Val)) Val (JLabel Cont) Cont (toArgTup (someTup as xs)) xs
  have hwk := hf (Arg (OptV K)) (Arg (OptV Val)) (JLabel KL) (JLabel Cont)
    (toArgTup (noneTup as)) (toArgTup (someTup as xs))
  have hG : WpG (Tup.zip (toArgTup (someTup as xs)) xs) := by
    simpa using WpG.append_some (G := []) (fun _ h => (by cases h)) xs
  exact LeanQbe.T.simplifyGroup_wp hwf hwk 0 hG
    (fun _ h => (by cases h)) (fun _ h => (by cases h)) m h

end LeanQbe.T
