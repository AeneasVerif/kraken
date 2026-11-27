module

public import LeanQbe.T.LeanLCNF.Sem.PLemmas
public import LeanQbe.T.LeanLCNF.Sem.PerceusSim

/-!
# Top-Level Perceus Soundness Theorems (`perceus_sound`, `perceus_sound_idx`)

Top-level Tier-P → Tier-H Perceus soundness theorems:
- `hOfPR`, `hOfPRIdx`, `hOfPRIdx_le` (resource-level Tier-H interpretation of `PResEnv`);
- `perceus_decl_ok_res`, `perceus_sound_res`, `perceus_sound_res_idx`;
- `combinedPRes`, `PWp_PRWp_combine`;
- **`perceus_sound`**: `RcCheck m = true → perceusModWf m = true →
  PModuleOk Δp m → HModuleOk (hOfP m Δp) m`;
- **`perceus_sound_idx`**: measure-indexed version supporting self-tail / recursive modules.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

/-! ## 1. Per-Declaration Soundness at `PRWp` -/

private theorem handlesRcSound_shrink {h1 h2 : List (BitVec 64)} {objs : List LcnfObj}
    (hle : ∀ a, h2.count a ≤ h1.count a) (hs : HandlesRcSound h1 objs) :
    HandlesRcSound h2 objs :=
  ⟨hs.1, fun q hq hrc => Nat.le_trans (Nat.add_le_add_left (hle q.addr) _) (hs.2 q hq hrc)⟩

/-- Prove Tier-H `HWp` for a single declaration `d ∈ m.decls` from `PRWp` and entry `RcInv`. -/
public theorem perceus_decl_ok_res {m : LcModule} {Δr : PResEnv} {Δh : HEnv}
    (hrc : RcCheck m = true) (hmwf : perceusModWf m = true) (hcompat : PRCallCompat m Δr Δh)
    {d : LcDecl} (hd : d ∈ m.decls) {rt0 rt : BitVec 64} {pvs : List PVal} {as : List Word}
    {extH ghostH : List (BitVec 64)} {σ : HState} {rem wr rcr : Nat}
    {Pr : PResPost} {Er : PResXPost} {Q : HPost} {X : HXPost}
    (h_len : pvs.length = d.params.length) (h_match : paramsMatch d.params as)
    (h_rc : RcInv rt0 (entryRcFrame d pvs as extH ghostH) σ)
    (h_hih : HandlesInHeap (extH ++ ghostH) σ.objs)
    (h_res : ResStateInv σ rem wr rcr) (h_inv : HInv rt σ)
    (h_pr : PRWp m (mkRcModEnv m) d.retTy Δr [] (RcCtx.mk [] [] |>.bindParams d.params)
      PResJEnv.empty (PValEnv.empty.bindAll d.params pvs) rem wr rcr Pr Er d.body)
    (hq : ∀ r rw σ' rem' wr' rcr',
      Pr r rem' wr' rcr' → HeapClean rt0 σ' → ResStateInv σ' rem' wr' rcr' →
      ValRep d.retTy r rw σ'.objs →
      (¬d.retTy.isScalar = true → ¬d.retTy.needsRc = true →
        ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) →
      HandlesRcSound (retHandles d.retTy rw ++ extH ++ ghostH) σ'.objs →
      CallPreserve (nonScalarWords d.params as) (extH ++ ghostH) σ σ' → Q rw σ')
    (hx : ∀ c rem' wr' rcr' σ', Er c rem' wr' rcr' → X (BitVec.ofNat 64 c) σ') :
    HWp Δh rt d.retTy HJEnv.empty (HValEnv.empty.bindAll d.params as) Q X d.body σ := by
  have _ := h_len
  obtain ⟨_, hmod⟩ := perceusModWf_facts hmwf
  have hd_f := hmod d hd
  have hmwf' : ∀ d0 ∈ m.decls,
      !isPrimName d0.name = true ∧ (d0.params.map LcParam.id).Nodup :=
    fun d0 hd0 => ⟨(hmod d0 hd0).1, (hmod d0 hd0).2.1⟩
  obtain ⟨jumps, hcc⟩ := rcCheck_decl_checkCode hrc hd
  let rf0 := entryRcFrame d pvs as extH ghostH
  have hrc' : RcInv rt rf0 σ := rcInv_swap_rt h_rc h_inv
  have hclean0 := entryRcFrame_clean d
  have hsbv0 : SharedBoolVars rf0.ctx := fun p hp => by
    simp only [rf0, entryRcFrame, bindParams_sharedPreds] at hp; cases hp
  exact perceus_code_sim hmwf' hcompat d.body (rf0 := rf0) (rf := rf0) (σ0 := σ) (σ := σ)
    (sm := []) (jpsOk := []) hcc hd_f.2.2 h_pr hrc' hclean0.1
    (parentsOwned_entry d.params hd_f.2.1) (noRcCorrect_init d.params)
    (parentChildBacked_init d pvs as extH ghostH)
    (sharedTargetsHeap_init d.params rf0.envP rf0.envH extH ghostH) h_hih
    (entryPres_refl rf0 σ hrc'.1.1.2.1 hrc'.1.2) hsbv0 (sharedBoolPreds_init d.params)
    (exclCtorHeap_init d.params rf0.envP rf0.envH extH ghostH) List.nodup_nil
    (fun _ _ _ => rfl) h_res ⟨List.nodup_nil, fun _ h => nomatch h⟩
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun hPr hc' hres' hvr hno hsnd hep' =>
      hq _ _ _ _ _ _ hPr (heapClean_swap_rt hc' h_rc.1.1.1.2.1) hres' hvr hno
        (handlesRcSound_shrink (fun a => by
          simp only [List.count_append, hep'.2.2.1]
          exact Nat.add_le_add_left (hep'.2.2.2.2 a) _) hsnd)
        (entryPres_to_callPreserve hd_f.2.1 h_match hep'))
    (fun hEr => hx _ _ _ _ _ hEr)

/-! ## 2. Resource-Level Perceus Soundness (`hOfPR`, `perceus_sound_res{,_idx}`) -/

/-- Tier-H specification induced by resource-aware Tier-P contract `Δr` on module `m`. -/
@[expose] public def hOfPR (m : LcModule) (Δr : PResEnv) : HEnv :=
  fun fn as σ Q X =>
    ∃ rt d pvs extH ghostH rem₀ wr₀ rcr₀ Pr Er,
      d ∈ m.decls ∧
      d.name = fn ∧
      RcInv rt (entryRcFrame d pvs as extH ghostH) σ ∧
      HandlesInHeap (extH ++ ghostH) σ.objs ∧
      ResStateInv σ rem₀ wr₀ rcr₀ ∧
      pvs.length = d.params.length ∧
      Δr fn pvs rem₀ wr₀ rcr₀ Pr Er ∧
      (∀ r rw σ' rem' wr' rcr',
        Pr r rem' wr' rcr' → HeapClean rt σ' → ResStateInv σ' rem' wr' rcr' →
        ValRep d.retTy r rw σ'.objs →
        (¬d.retTy.isScalar = true → ¬d.retTy.needsRc = true →
          ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) →
        HandlesRcSound (retHandles d.retTy rw ++ extH ++ ghostH) σ'.objs →
        CallPreserve (nonScalarWords d.params as) (extH ++ ghostH) σ σ' → Q rw σ') ∧
      (∀ c rem' wr' rcr' σ', Er c rem' wr' rcr' → X (BitVec.ofNat 64 c) σ')

/-- Measure-indexed resource-aware Tier-H environment induced by `Δr : Nat → PResEnv`. -/
@[expose] public def hOfPRIdx (m : LcModule) (Δr : Nat → PResEnv) (k : Nat) : HEnv :=
  fun fn as σ Q X =>
    ∃ rt d pvs extH ghostH rem₀ wr₀ rcr₀ Pr Er,
      d ∈ m.decls ∧
      d.name = fn ∧
      RcInv rt (entryRcFrame d pvs as extH ghostH) σ ∧
      HandlesInHeap (extH ++ ghostH) σ.objs ∧
      ResStateInv σ rem₀ wr₀ rcr₀ ∧
      pvs.length = d.params.length ∧
      Δr k fn pvs rem₀ wr₀ rcr₀ Pr Er ∧
      (∀ r rw σ' rem' wr' rcr',
        Pr r rem' wr' rcr' → HeapClean rt σ' → ResStateInv σ' rem' wr' rcr' →
        ValRep d.retTy r rw σ'.objs →
        (¬d.retTy.isScalar = true → ¬d.retTy.needsRc = true →
          ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) →
        HandlesRcSound (retHandles d.retTy rw ++ extH ++ ghostH) σ'.objs →
        CallPreserve (nonScalarWords d.params as) (extH ++ ghostH) σ σ' → Q rw σ') ∧
      (∀ c rem' wr' rcr' σ', Er c rem' wr' rcr' → X (BitVec.ofNat 64 c) σ')

/-- Monotonicity of `hOfPRIdx` along a monotone `PResEnv` family. -/
public theorem hOfPRIdx_le {m : LcModule} {Δr : Nat → PResEnv}
    (hmono : ∀ k, (Δr k).le (Δr (k + 1))) :
    ∀ k, (hOfPRIdx m Δr k).le (hOfPRIdx m Δr (k + 1)) := by
  intro k fn as σ Q X
    ⟨rt, d, pvs, extH, ghostH, rem₀, wr₀, rcr₀, Pr, Er,
      hd, hnm, hrc, hhih, hres, hlen, hdr, hq, hx⟩
  exact ⟨rt, d, pvs, extH, ghostH, rem₀, wr₀, rcr₀, Pr, Er,
    hd, hnm, hrc, hhih, hres, hlen, hmono k _ _ _ _ _ _ _ hdr, hq, hx⟩

private theorem prCallCompat_of_hOfPR {m : LcModule} {Δr : PResEnv} :
    PRCallCompat m Δr (hOfPR m Δr) := by
  unfold PRCallCompat
  intro rt d calleeRf σ pvs ws rem wr rcr P E hd hrf hpvs hws hrc _ _ hhih hres hΔr
  have _ := hws
  let Ph : HPost := fun rw σ' =>
    CallPostOk rt d (calleeRf.extH ++ calleeRf.ghostH) (nonScalarWords d.params ws) σ σ' rw P
  let Eh : HXPost := fun c σ' => CallExcOk rt σ' c E
  refine ⟨Ph, Eh, ?_, fun _ _ h => h, fun _ _ h => h⟩
  exact ⟨rt, d, pvs, calleeRf.extH, calleeRf.ghostH, rem, wr, rcr, P, E,
    hd, rfl, hrf ▸ hrc, hhih, hres, hpvs, hΔr,
    fun r rw σ' rem' wr' rcr' hP hc' hres' hvr hno hsnd hcpres =>
      ⟨r, rem', wr', rcr', hP, hc', hvr, hno,
        List.append_assoc _ _ _ ▸ hsnd, hcpres, hres'⟩,
    fun c rem' wr' rcr' σ' hE => ⟨c, rem', wr', rcr', hE, rfl⟩⟩

private theorem prCallCompat_of_hOfPRIdx {m : LcModule} {Δr : Nat → PResEnv} (k : Nat) :
    PRCallCompat m (match k with | 0 => PResEnv.bot | k' + 1 => Δr k')
      (match k with | 0 => HEnv.bot | k' + 1 => hOfPRIdx m Δr k') := by
  unfold PRCallCompat
  intro rt d calleeRf σ pvs ws rem wr rcr P E hd hrf hpvs hws hrc _ _ hhih hres hΔr
  have _ := hws
  cases k with
  | zero => exact False.elim hΔr
  | succ k' =>
    let Ph : HPost := fun rw σ' =>
      CallPostOk rt d (calleeRf.extH ++ calleeRf.ghostH) (nonScalarWords d.params ws) σ σ' rw P
    let Eh : HXPost := fun c σ' => CallExcOk rt σ' c E
    refine ⟨Ph, Eh, ?_, fun _ _ h => h, fun _ _ h => h⟩
    exact ⟨rt, d, pvs, calleeRf.extH, calleeRf.ghostH, rem, wr, rcr, P, E,
      hd, rfl, hrf ▸ hrc, hhih, hres, hpvs, hΔr,
      fun r rw σ' rem' wr' rcr' hP hc' hres' hvr hno hsnd hcpres =>
        ⟨r, rem', wr', rcr', hP, hc', hvr, hno,
          List.append_assoc _ _ _ ▸ hsnd, hcpres, hres'⟩,
      fun c rem' wr' rcr' σ' hE => ⟨c, rem', wr', rcr', hE, rfl⟩⟩

/-- Resource-aware Perceus soundness for acyclic / fixed-contract modules. -/
public theorem perceus_sound_res {m : LcModule} {Δr : PResEnv}
    (hrc : RcCheck m = true) (hmwf : perceusModWf m = true) (hpres : PResOk Δr m) :
    HModuleOk (hOfPR m Δr) m := by
  unfold HModuleOk
  intro d hd rt as σ Q X hinv hmatch hspec
  obtain ⟨rt0, d', pvs, extH, ghostH, rem₀, wr₀, rcr₀, Pr, Er,
    hd', hnm, hrc0, hhih, hres, hlen, hdr, hq, hx⟩ := hspec
  obtain ⟨hnd, _⟩ := perceusModWf_facts hmwf
  obtain rfl : d = d' := (mod_decl_unique hnd hd hd' hnm).symm
  have hpr := hpres d hd pvs rem₀ wr₀ rcr₀ Pr Er hlen hdr
  exact perceus_decl_ok_res hrc hmwf prCallCompat_of_hOfPR hd hlen hmatch hrc0 hhih hres hinv hpr
    hq hx

/-- Resource-aware Perceus soundness for measure-indexed / self-tail / recursive modules. -/
public theorem perceus_sound_res_idx {m : LcModule} {Δr : Nat → PResEnv}
    (hrc : RcCheck m = true) (hmwf : perceusModWf m = true) (hpres : PResOkIdx Δr m) :
    HModuleOkIdx (hOfPRIdx m Δr) m := by
  unfold HModuleOkIdx
  refine ⟨hOfPRIdx_le hpres.1, fun k d hd rt as σ Q X hinv hmatch hspec => ?_⟩
  obtain ⟨rt0, d', pvs, extH, ghostH, rem₀, wr₀, rcr₀, Pr, Er,
    hd', hnm, hrc0, hhih, hres, hlen, hdr, hq, hx⟩ := hspec
  obtain ⟨hnd, _⟩ := perceusModWf_facts hmwf
  obtain rfl : d = d' := (mod_decl_unique hnd hd hd' hnm).symm
  have hpr := hpres.2 k d hd pvs rem₀ wr₀ rcr₀ Pr Er hlen hdr
  exact perceus_decl_ok_res hrc hmwf (prCallCompat_of_hOfPRIdx k) hd hlen hmatch
    hrc0 hhih hres hinv hpr hq hx

/-! ## 3. Combining `PWp` and `PRWp` (`perceus_sound`, `perceus_sound_idx`) -/

/-- Conjunction of pure Tier-P contract `Δp` and resource contract `Δr`. -/
@[expose] public def combinedPRes (Δp : PEnv) (Δr : PResEnv) : PResEnv :=
  fun fn as rem wr rcr Q X =>
    ∃ Qp Xp Pr Er,
      Δp fn as Qp Xp ∧ Δr fn as rem wr rcr Pr Er ∧
      (∀ r rem' wr' rcr', Qp r → Pr r rem' wr' rcr' → Q r rem' wr' rcr') ∧
      (∀ c rem' wr' rcr', Xp c → Er c rem' wr' rcr' → X c rem' wr' rcr')

private theorem ne_of_all_bne {jps : List RcJpInfo} {j : Nat}
    (hall : jps.all (·.id != j) = true) {info : RcJpInfo} (hinfo : info ∈ jps) :
    info.id ≠ j :=
  bne_iff_ne.mp (List.all_eq_true.mp hall info hinfo)

private theorem jpBaseCtx_branches {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {j : Nat} {ps : List LcParam} {body k : LcCode} {jumps : List (Nat × RcCtx)}
    (hcc : checkCode env retTy jps ctx (.jp j ps body k) = .ok jumps) :
    let jInfo : RcJpInfo := { id := j, params := ps, scopeIds := ctx.vars.map (·.id) }
    (∃ jumpsK, checkCode env retTy (jInfo :: jps) ctx k = .ok jumpsK) ∧
    (∃ jumpsB, checkCode env retTy jps ((jpBaseCtx env retTy jps ctx j ps k).bindParams ps)
      body = .ok jumpsB) := by
  intro jInfo
  have hcc' := hcc
  rw [checkCode.eq_2] at hcc'
  dsimp only at hcc'
  cases hck : checkCode env retTy (jInfo :: jps) ctx k with
  | error e => rw [hck] at hcc'; simp [Bind.bind, Except.bind] at hcc'
  | ok jumpsK =>
    rw [hck] at hcc'
    simp only [Bind.bind, Except.bind, pure, Except.pure] at hcc'
    cases hmj : mergeJpList ((jumpsK.filter (·.1 == j)).map Prod.snd) with
    | error e => rw [hmj] at hcc'; cases hcc'
    | ok base? =>
      have hbc : jpBaseCtx env retTy jps ctx j ps k =
          match base? with | some c => c | none => ctx := by
        simp only [jpBaseCtx, jInfo, hck, hmj]
        cases base? <;> rfl
      rw [hmj] at hcc'
      cases base? with
      | none =>
        dsimp only at hcc'
        cases hcb : checkCode env retTy jps (ctx.bindParams ps) body with
        | error e => rw [hcb] at hcc'; cases hcc'
        | ok jumpsB => exact ⟨⟨jumpsK, rfl⟩, ⟨jumpsB, by simpa [hbc] using hcb⟩⟩
      | some base =>
        dsimp only at hcc'
        cases hcb : checkCode env retTy jps (base.bindParams ps) body with
        | error e => rw [hcb] at hcc'; cases hcc'
        | ok jumpsB => exact ⟨⟨jumpsK, rfl⟩, ⟨jumpsB, by simpa [hbc] using hcb⟩⟩

private theorem checkAlts_step_cons {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {x : Nat} {target? : Option Nat} {pat : LcPat} {b : LcCode}
    {rest : List (LcPat × LcCode)} {jumps : List (Nat × RcCtx)}
    (hca : checkAlts env retTy jps ctx x target? ((pat, b) :: rest) = .ok jumps) :
    let ctxB := match pat with
      | .dflt => ctx
      | .ctor ci cname =>
        let ctx1 := if env.scalarCtors.contains cname then ctx.markScalarBranch x else ctx
        match target?, ci with
        | some tgt, 0 => ctx1.markExcl tgt
        | _, _ => ctx1
    (∃ j1, checkCode env retTy jps ctxB b = .ok j1) ∧
    (∃ j2, checkAlts env retTy jps ctx x target? rest = .ok j2) := by
  intro ctxB
  have heq : checkAlts env retTy jps ctx x target? ((pat, b) :: rest) =
      (do
        let j1 ← checkCode env retTy jps ctxB b
        let j2 ← checkAlts env retTy jps ctx x target? rest
        pure (j1 ++ j2)) := by
    cases pat with
    | dflt => cases target? <;> rfl
    | ctor ci _ => cases ci <;> cases target? <;> rfl
  rw [heq] at hca
  cases h1 : checkCode env retTy jps ctxB b with
  | error _ => simp [h1, Bind.bind, Except.bind] at hca
  | ok j1 =>
    simp only [h1, Bind.bind, Except.bind] at hca
    cases h2 : checkAlts env retTy jps ctx x target? rest with
    | error _ => simp [h2] at hca
    | ok j2 => exact ⟨⟨j1, rfl⟩, ⟨j2, rfl⟩⟩

private theorem checkCode_cases_unwrap {env : RcModEnv} {retTy : LcTy} {jps : List RcJpInfo}
    {ctx : RcCtx} {x : Nat} {alts : List (LcPat × LcCode)} {jumps : List (Nat × RcCtx)}
    (hcc : checkCode env retTy jps ctx (.cases x alts) = .ok jumps) :
    checkAlts env retTy jps ctx x
      ((ctx.sharedPreds.find? (·.1 == x)).map Prod.snd) alts = .ok jumps := by
  rw [checkCode.eq_4] at hcc
  cases hlv : ctx.checkLive x with
  | error _ => simp [hlv, Bind.bind, Except.bind] at hcc
  | ok _ => simpa [hlv, Bind.bind, Except.bind] using hcc

private theorem PWp_jp_congr_of_check {ar : PArity} {Δ : PEnv} {env : RcModEnv} {retTy : LcTy} :
    ∀ (c : LcCode) {jps : List RcJpInfo} {ctx : RcCtx} {jumps : List (Nat × RcCtx)}
      {J₁ J₂ : PJEnv} {ρ : PValEnv} {Q : PPost} {X : PXPost},
      checkCode env retTy jps ctx c = .ok jumps →
      (∀ info ∈ jps, ∀ vs, J₁ info.id vs → J₂ info.id vs) →
      PWp ar Δ J₁ ρ Q X c → PWp ar Δ J₂ ρ Q X c
  | .let_ x ty v k, jps, ctx, jumps, J₁, J₂, ρ, Q, X, hcc, hJ, h => by
    rw [checkCode.eq_1] at hcc
    cases hcv : checkVal env ctx x ty v with
    | error _ => simp [hcv, Bind.bind, Except.bind] at hcc
    | ok ctx' =>
      simp only [hcv, Bind.bind, Except.bind] at hcc
      rw [PWp.eq_1] at h ⊢
      exact PVal.wp_conseq (PEnv.le_refl Δ)
        (fun r hk => PWp_jp_congr_of_check k hcc hJ hk) (fun _ hx => hx) h
  | .jp j ps body k, jps, ctx, jumps, J₁, J₂, ρ, Q, X, hcc, hJ, h => by
    obtain ⟨⟨jK, hccK⟩, ⟨jB, hccB⟩⟩ := jpBaseCtx_branches hcc
    rw [PWp.eq_2] at h ⊢
    intro Jj hbody
    have hset : ∀ info ∈ ({ id := j, params := ps, scopeIds := ctx.vars.map (·.id) } :: jps),
        ∀ vs, (J₁.set j Jj) info.id vs → (J₂.set j Jj) info.id vs := by
      intro info hinfo vs
      dsimp only [PJEnv.set]
      rcases List.mem_cons.mp hinfo with rfl | hmem
      · simp
      · by_cases heq : info.id = j
        · simp [heq]
        · simp [heq]; exact hJ info hmem vs
    have hbody1 : ∀ as, as.length = ps.length →
        PWp ar Δ (J₁.set j Jj) (ρ.bindAll ps as) Q X body → Jj as := by
      intro as hlen hb1
      have hsetB : ∀ info ∈ jps, ∀ vs, (J₁.set j Jj) info.id vs → (J₂.set j Jj) info.id vs :=
        fun info hinfo => hset info (List.mem_cons_of_mem _ hinfo)
      exact hbody as hlen (PWp_jp_congr_of_check body hccB hsetB hb1)
    exact PWp_jp_congr_of_check k hccK hset (h Jj hbody1)
  | .jmp j as, jps, ctx, jumps, J₁, J₂, ρ, Q, X, hcc, hJ, h => by
    rw [checkCode.eq_3] at hcc
    cases hfj : jps.find? (·.id == j) with
    | none => simp [hfj] at hcc
    | some info =>
      have hmem := List.mem_of_find?_eq_some hfj
      have hid : info.id = j :=
        beq_iff_eq.mp (List.find?_some (p := fun x : RcJpInfo => x.id == j) hfj)
      rw [PWp.eq_3] at h ⊢
      cases hev : ρ.evalArgs as with
      | none => simp [hev] at h
      | some vs =>
        simp only [hev] at h ⊢
        exact by simpa [hid] using hJ info hmem vs (by simpa [hid] using h)
  | .cases x alts, jps, ctx, jumps, J₁, J₂, ρ, Q, X, hcc, hJ, h => by
    have hca := checkCode_cases_unwrap hcc
    rw [PWp.eq_4] at h ⊢
    cases htg : (ρ x).bind PVal.tag? with
    | none => simp [htg] at h
    | some tag =>
      simp only [htg] at h ⊢
      let tgt? := (ctx.sharedPreds.find? (·.1 == x)).map Prod.snd
      have hdflt : ∀ alts1, (∀ a ∈ alts1, a ∈ alts) →
          (∃ j, checkAlts env retTy jps ctx x tgt? alts1 = .ok j) →
          PWpDfltAlts ar Δ J₁ ρ Q X alts1 → PWpDfltAlts ar Δ J₂ ρ Q X alts1 := by
        intro alts1 hsub hca1 hd
        induction alts1 with
        | nil => rw [PWpDfltAlts.eq_1] at hd; exact hd
        | cons a rest ih =>
          rcases a with ⟨pat, b⟩
          obtain ⟨j0, hj0⟩ := hca1
          obtain ⟨⟨jb, hccb⟩, hcar⟩ := checkAlts_step_cons hj0
          have hlt_b : sizeOf b < 1 + x + sizeOf alts := by
            have := List.sizeOf_lt_of_mem (hsub (pat, b) List.mem_cons_self); simp_all; omega
          cases pat with
          | dflt =>
            rw [PWpDfltAlts.eq_2] at hd ⊢
            exact PWp_jp_congr_of_check b hccb hJ hd
          | ctor ci cname =>
            rw [PWpDfltAlts.eq_3] at hd ⊢
            exact ih (fun e he => hsub e (List.mem_cons_of_mem _ he)) hcar hd
      have hctor : ∀ alts1, (∀ a ∈ alts1, a ∈ alts) →
          (∃ j, checkAlts env retTy jps ctx x tgt? alts1 = .ok j) →
          ∀ d₁ d₂, (d₁ → d₂) →
          PWpCtorAlts ar Δ J₁ ρ Q X tag alts1 d₁ → PWpCtorAlts ar Δ J₂ ρ Q X tag alts1 d₂ := by
        intro alts1 hsub hca1 d₁ d₂ hd hct
        induction alts1 with
        | nil => rw [PWpCtorAlts.eq_1] at hct ⊢; exact hd hct
        | cons a rest ih =>
          rcases a with ⟨pat, b⟩
          obtain ⟨j0, hj0⟩ := hca1
          obtain ⟨⟨jb, hccb⟩, hcar⟩ := checkAlts_step_cons hj0
          have hlt_b : sizeOf b < 1 + x + sizeOf alts := by
            have := List.sizeOf_lt_of_mem (hsub (pat, b) List.mem_cons_self); simp_all; omega
          cases pat with
          | dflt =>
            rw [PWpCtorAlts.eq_3] at hct ⊢
            exact ih (fun e he => hsub e (List.mem_cons_of_mem _ he)) hcar hct
          | ctor ci cname =>
            rw [PWpCtorAlts.eq_2] at hct ⊢
            by_cases htg_eq : ci = tag
            · simp only [htg_eq, ↓reduceIte] at hct ⊢
              exact PWp_jp_congr_of_check b hccb hJ hct
            · simp only [htg_eq, ↓reduceIte] at hct ⊢
              exact ih (fun e he => hsub e (List.mem_cons_of_mem _ he)) hcar hct
      exact hctor alts (fun _ h => h) ⟨jumps, hca⟩ _ _
        (hdflt alts (fun _ h => h) ⟨jumps, hca⟩) h
  | .ret a, _, _, _, _, _, _, _, _, _, _, h => by
    rw [PWp.eq_5] at h ⊢; exact h
  | .unreach, _, _, _, _, _, _, _, _, _, _, h => by
    rw [PWp.eq_6] at h ⊢; exact h
  | .oset x i y k, jps, ctx, jumps, J₁, J₂, ρ, Q, X, hcc, hJ, h => by
    rw [checkCode.eq_7] at hcc
    cases h1 : ctx.checkExcl x "oset" with
    | error _ => simp [h1, Bind.bind, Except.bind] at hcc
    | ok _ =>
      simp only [h1, Bind.bind, Except.bind] at hcc
      cases h2 : ctx.consumeArg y with
      | error _ => simp [h2] at hcc
      | ok ctx1 =>
        simp only [h2] at hcc
        rw [PWp.eq_7] at h ⊢
        cases hx : ρ x <;> cases hy : ρ.evalArg y <;> simp [hx, hy] at h ⊢
        rename_i xv yv
        cases hs : xv.setObj i yv with
        | none => simp [hs] at h
        | some xv' => simp only [hs] at h ⊢; exact PWp_jp_congr_of_check k hcc hJ h
  | .uset x i y k, jps, ctx, jumps, J₁, J₂, ρ, Q, X, hcc, hJ, h => by
    rw [checkCode.eq_8] at hcc
    cases h1 : ctx.checkExcl x "uset" with
    | error _ => simp [h1, Bind.bind, Except.bind] at hcc
    | ok _ =>
      simp only [h1, Bind.bind, Except.bind] at hcc
      cases h2 : ctx.checkLive y with
      | error _ => simp [h2] at hcc
      | ok _ =>
        simp only [h2] at hcc
        rw [PWp.eq_8] at h ⊢
        cases hx : ρ x <;> cases hy : ρ y <;> simp [hx, hy] at h ⊢
        rename_i xv yv
        cases hs : xv.setUsize i yv with
        | none => simp [hs] at h
        | some xv' => simp only [hs] at h ⊢; exact PWp_jp_congr_of_check k hcc hJ h
  | .sset x n off y ty k, jps, ctx, jumps, J₁, J₂, ρ, Q, X, hcc, hJ, h => by
    rw [checkCode.eq_9] at hcc
    cases h1 : ctx.checkExcl x "sset" with
    | error _ => simp [h1, Bind.bind, Except.bind] at hcc
    | ok _ =>
      simp only [h1, Bind.bind, Except.bind] at hcc
      cases h2 : ctx.checkLive y with
      | error _ => simp [h2] at hcc
      | ok _ =>
        simp only [h2] at hcc
        rw [PWp.eq_9] at h ⊢
        cases hx : ρ x <;> cases hy : ρ y <;> simp [hx, hy] at h ⊢
        rename_i xv yv
        cases hs : xv.setScalar n off ty yv with
        | none => simp [hs] at h
        | some xv' => simp only [hs] at h ⊢; exact PWp_jp_congr_of_check k hcc hJ h
  | .setTag x cidx k, jps, ctx, jumps, J₁, J₂, ρ, Q, X, hcc, hJ, h => by
    rw [checkCode.eq_10] at hcc
    cases h1 : ctx.checkExcl x "setTag" with
    | error _ => simp [h1, Bind.bind, Except.bind] at hcc
    | ok _ =>
      simp only [h1, Bind.bind, Except.bind] at hcc
      rw [PWp.eq_10] at h ⊢
      cases hs : (ρ x).bind (·.setTag cidx) with
      | none => simp [hs] at h
      | some xv' => simp only [hs] at h ⊢; exact PWp_jp_congr_of_check k hcc hJ h
  | .inc x n chk k, jps, ctx, jumps, J₁, J₂, ρ, Q, X, hcc, hJ, h => by
    rw [checkCode.eq_11] at hcc
    cases hgx : ctx.get? x with
    | none => simp [hgx] at hcc
    | some v =>
      simp only [hgx] at hcc
      cases hlv : !v.isLive with
      | true => simp [hlv, Bind.bind, Except.bind] at hcc
      | false =>
        simp only [hlv, Bool.false_eq_true, ↓reduceIte] at hcc
        rw [PWp.eq_11] at h ⊢
        by_cases hskip : (v.noRc || v.persistent || n == 0) = true
        · simp only [hskip, ↓reduceIte] at hcc; exact PWp_jp_congr_of_check k hcc hJ h
        · simp only [hskip, Bool.false_eq_true, ↓reduceIte] at hcc
          exact PWp_jp_congr_of_check k hcc hJ h
  | .dec x n chk k, jps, ctx, jumps, J₁, J₂, ρ, Q, X, hcc, hJ, h => by
    rw [checkCode.eq_12] at hcc
    cases h1 : ctx.consumeVar x n with
    | error _ => simp [h1, Bind.bind, Except.bind] at hcc
    | ok ctx1 =>
      simp only [h1, Bind.bind, Except.bind] at hcc
      rw [PWp.eq_12] at h ⊢; exact PWp_jp_congr_of_check k hcc hJ h
  | .del x k, jps, ctx, jumps, J₁, J₂, ρ, Q, X, hcc, hJ, h => by
    rw [checkCode.eq_13] at hcc
    cases h1 : ctx.checkExcl x "del" with
    | error _ => simp [h1, Bind.bind, Except.bind] at hcc
    | ok _ =>
      simp only [h1, Bind.bind, Except.bind] at hcc
      cases h2 : ctx.consumeVar x with
      | error _ => simp [h2] at hcc
      | ok ctx1 =>
        simp only [h2] at hcc
        rw [PWp.eq_13] at h ⊢; exact PWp_jp_congr_of_check k hcc hJ h
termination_by c => sizeOf c
decreasing_by all_goals (simp; try (first | exact hlt_b | omega))

private theorem combine_val_wp {m : LcModule} {Δp : PEnv} {Δr : PResEnv}
    (hmwf : ∀ d ∈ m.decls, !isPrimName d.name = true ∧ (d.params.map LcParam.id).Nodup)
    {ρ : PValEnv} {ty : LcTy} {v : LcVal} {rem wr rcr : Nat}
    {Kp : PPost} {Xp : PXPost} {Kr : PResPost} {Xr : PResXPost}
    {Kc : PResPost} {Xc : PResXPost}
    (hK : ∀ r rem' wr' rcr', Kp r → Kr r rem' wr' rcr' → Kc r rem' wr' rcr')
    (hX : ∀ c rem' wr' rcr', Xp c → Xr c rem' wr' rcr' → Xc c rem' wr' rcr')
    (hp : PVal.wp (modArityOf m) Δp ρ ty v Kp Xp)
    (hr : PRValWp (mkRcModEnv m) Δr ρ ty v rem wr rcr Kr Xr) :
    PRValWp (mkRcModEnv m) (combinedPRes Δp Δr) ρ ty v rem wr rcr Kc Xc := by
  cases v with
  | lit l =>
    cases l with
    | nat n => exact ⟨hr.1, hK _ _ _ _ hp hr.2⟩
    | str _ => exact False.elim hr
    | scalar _ => exact hK _ _ _ _ hp hr
  | erased => exact hK _ _ _ _ hp hr
  | ctor ci as =>
    dsimp only [PVal.wp] at hp; dsimp only [PRValWp] at hr ⊢
    cases has : ρ.evalArgs as with
    | none => simp [has] at hr
    | some vs =>
      simp only [has] at hp hr ⊢
      cases hmk : PVal.mkCtor ty ci vs with
      | none => simp [hmk] at hr
      | some r =>
        simp only [hmk] at hp hr ⊢
        by_cases hsc : ci.isScalar = true
        · simp only [hsc, ↓reduceIte] at hr ⊢; exact hK _ _ _ _ hp hr
        · simp only [hsc, Bool.false_eq_true, ↓reduceIte] at hr ⊢
          exact ⟨hr.1, hr.2.1, hK _ _ _ _ hp hr.2.2⟩
  | oproj i x =>
    dsimp only [PVal.wp] at hp; dsimp only [PRValWp] at hr ⊢
    cases h : (ρ x).bind (·.getObj? i) with
    | none => simp [h] at hr
    | some r => simp only [h] at hp hr ⊢; exact hK _ _ _ _ hp hr
  | uproj i x =>
    dsimp only [PVal.wp] at hp; dsimp only [PRValWp] at hr ⊢
    cases h : (ρ x).bind (·.getUsize? i) with
    | none => simp [h] at hr
    | some r => simp only [h] at hp hr ⊢; exact hK _ _ _ _ hp hr
  | sproj n off x =>
    dsimp only [PVal.wp] at hp; dsimp only [PRValWp] at hr ⊢
    cases h : (ρ x).bind (·.getScalar? n off ty) with
    | none => simp [h] at hr
    | some r => simp only [h] at hp hr ⊢; exact hK _ _ _ _ hp hr
  | box t x =>
    dsimp only [PVal.wp] at hp; dsimp only [PRValWp] at hr ⊢
    cases h : (ρ x).bind (PVal.box t) with
    | none => simp [h] at hr
    | some r =>
      simp only [h] at hp hr ⊢
      by_cases hbx : (t == .uint64 || t == .usize || t == .float) = true
      · simp only [hbx, ↓reduceIte] at hr ⊢; exact ⟨hr.1, hr.2.1, hK _ _ _ _ hp hr.2.2⟩
      · simp only [hbx, Bool.false_eq_true, ↓reduceIte] at hr ⊢; exact hK _ _ _ _ hp hr
  | unbox x =>
    dsimp only [PVal.wp] at hp; dsimp only [PRValWp] at hr ⊢
    cases hx : ρ x with
    | none => simp [hx] at hr
    | some pv =>
      simp only [hx, Option.bind_some] at hp hr ⊢
      cases hb : PVal.unbox ty pv with
      | none => simp [hb] at hr
      | some r => simp only [hb] at hp hr ⊢; exact ⟨hr.1, hK _ _ _ _ hp hr.2⟩
  | isShared x =>
    dsimp only [PVal.wp] at hp; dsimp only [PRValWp] at hr ⊢
    cases hx : ρ x with
    | none => simp [hx] at hr
    | some pv =>
      simp only [hx] at hr ⊢
      exact ⟨hr.1, fun b => hK _ _ _ _ (hp.2 b) (hr.2 b)⟩
  | fap f as =>
    dsimp only [PVal.wp] at hp; dsimp only [PRValWp] at hr ⊢
    cases has : ρ.evalArgs as with
    | none => simp [has] at hr
    | some vs =>
      simp only [has] at hp hr ⊢
      by_cases hoob : (f == "outOfBounds._redArg") = true
      · simp only [hoob, ↓reduceIte] at hp hr ⊢
        simp only [hr.1, ↓reduceIte] at hp
        exact ⟨hr.1, hX _ _ _ _ hp hr.2⟩
      · simp only [hoob, Bool.false_eq_true, ↓reduceIte] at hp hr ⊢
        by_cases hfd : ((mkRcModEnv m).decls.find? (·.1 == f)).isSome = true
        · have hnp := mkRcModEnv_decl_not_prim hmwf hfd
          simp only [hnp, Bool.false_eq_true, ↓reduceIte] at hp
          simp only [hfd, ↓reduceIte] at hr ⊢
          rcases hp with ⟨Qp', Xp', hΔp, hQp', hXp'⟩
          rcases hr with ⟨Pr', Er', hΔr, hPr', hEr'⟩
          refine ⟨fun r rem' wr' rcr' => Qp' r ∧ Pr' r rem' wr' rcr',
            fun c rem' wr' rcr' => Xp' c ∧ Er' c rem' wr' rcr',
            ⟨Qp', Xp', Pr', Er', hΔp, hΔr, fun _ _ _ _ => And.intro, fun _ _ _ _ => And.intro⟩,
            fun r rem' wr' rcr' ⟨hq', hr'⟩ => hK _ _ _ _ (hQp' r hq') (hPr' r rem' wr' rcr' hr'),
            fun c rem' wr' rcr' ⟨hx', he'⟩ => hX _ _ _ _ (hXp' c hx') (hEr' c rem' wr' rcr' he')⟩
        · have hfdf : ((mkRcModEnv m).decls.find? (·.1 == f)).isSome = false :=
            Bool.eq_false_iff.mpr hfd
          simp only [hfdf, Bool.false_eq_true, ↓reduceIte] at hr ⊢
          rcases hr with ⟨hpprim, hprim⟩
          simp only [hpprim, ↓reduceIte] at hp
          refine ⟨hpprim, ?_⟩
          cases hpf : primP f vs with
          | none => simp [hpf] at hprim
          | some r => simp only [hpf] at hp hprim ⊢; exact ⟨hprim.1, hK _ _ _ _ hp hprim.2⟩
  | ap _ _ | pap _ _ | reset _ _ | reuse _ _ _ _ => exact False.elim hr

private theorem PWp_PRWp_combine {m : LcModule} {Δp : PEnv} {Δr : PResEnv}
    (hmwf : ∀ d ∈ m.decls, !isPrimName d.name = true ∧ (d.params.map LcParam.id).Nodup) :
    ∀ (c : LcCode) {retTy : LcTy} {jps : List RcJpInfo} {ctx : RcCtx}
      {sm : List (Nat × Nat × List Bool)} {jumps : List (Nat × RcCtx)}
      {Jw : PJEnv} {Jp Jc : PResJEnv} {ρ : PValEnv} {rem wr rcr : Nat}
      {Qp : PPost} {Xp : PXPost} {Qr : PResPost} {Xr : PResXPost},
      checkCode (mkRcModEnv m) retTy jps ctx c = .ok jumps →
      perceusCodeWf (mkRcModEnv m) retTy jps ctx sm c = true →
      (∀ info ∈ jps, ∀ vs rem' wr' rcr',
        Jw info.id vs → Jp info.id vs rem' wr' rcr' → Jc info.id vs rem' wr' rcr') →
      PWp (modArityOf m) Δp Jw ρ Qp Xp c →
      PRWp m (mkRcModEnv m) retTy Δr jps ctx Jp ρ rem wr rcr Qr Xr c →
      PRWp m (mkRcModEnv m) retTy (combinedPRes Δp Δr) jps ctx Jc ρ rem wr rcr
        (fun r rem' wr' rcr' => Qp r ∧ Qr r rem' wr' rcr')
        (fun code rem' wr' rcr' => Xp code ∧ Xr code rem' wr' rcr') c
  | .let_ x ty v k, retTy, jps, ctx, sm, jumps, Jw, Jp, Jc, ρ, rem, wr, rcr, Qp, Xp, Qr, Xr,
      hcc, hwf, hJ, hp, hr => by
    rw [checkCode.eq_1] at hcc
    cases hcv : checkVal (mkRcModEnv m) ctx x ty v with
    | error _ => simp [hcv, Bind.bind, Except.bind] at hcc
    | ok ctx' =>
      simp only [hcv, Bind.bind, Except.bind] at hcc
      have hwf_k : ∃ sm', perceusCodeWf (mkRcModEnv m) retTy jps ctx' sm' k = true := by
        by_cases hctor : ∃ ci args, v = .ctor ci args
        · rcases hctor with ⟨ci, args, rfl⟩
          rw [perceusCodeWf.eq_1] at hwf
          simp only [Bool.and_eq_true, hcv] at hwf
          exact ⟨ctorBindMask x ci sm, hwf.2⟩
        · rw [perceusCodeWf.eq_2 _ _ _ _ _ _ _ _ _ (fun ci args h => hctor ⟨ci, args, h⟩)] at hwf
          simp only [Bool.and_eq_true, hcv] at hwf
          exact ⟨sm.filter (·.1 != x), hwf.2⟩
      obtain ⟨sm', hwfK⟩ := hwf_k
      rw [PWp.eq_1] at hp
      rw [PRWp.eq_1] at hr ⊢
      simp only [hcv] at hr ⊢
      exact combine_val_wp hmwf
        (fun r rem' wr' rcr' hpk hrk =>
          PWp_PRWp_combine hmwf k hcc hwfK hJ hpk hrk)
        (fun _ _ _ _ => And.intro) hp hr
  | .jp j ps body k, retTy, jps, ctx, sm, jumps, Jw, Jp, Jc, ρ, rem, wr, rcr, Qp, Xp, Qr, Xr,
      hcc, hwf, hJ, hp, hr => by
    obtain ⟨⟨jK, hccK⟩, ⟨jB, hccB⟩⟩ := jpBaseCtx_branches hcc
    have hwf' := hwf
    rw [perceusCodeWf.eq_3] at hwf'
    dsimp only at hwf'
    simp only [Bool.and_eq_true] at hwf'
    obtain ⟨⟨⟨⟨⟨⟨hjps_no, _⟩, _⟩, _⟩, _⟩, hwfK⟩, hwfB⟩ := hwf'
    rw [PWp.eq_2] at hp
    rw [PRWp.eq_2] at hr ⊢
    dsimp only at hr ⊢
    intro Jc_new hJc_body
    let baseCtx := jpBaseCtx (mkRcModEnv m) retTy jps ctx j ps k
    let Jj_w : List PVal → Prop := fun as =>
      as.length = ps.length ∧ PWp (modArityOf m) Δp Jw (ρ.bindAll ps as) Qp Xp body
    let Jj_p : List PVal → Nat → Nat → Nat → Prop := fun as rem' wr' rcr' =>
      Jj_w as → Jc_new as rem' wr' rcr'
    have hJw_body : ∀ as, as.length = ps.length →
        PWp (modArityOf m) Δp (Jw.set j Jj_w) (ρ.bindAll ps as) Qp Xp body → Jj_w as := by
      intro as hlen hb
      refine ⟨hlen, PWp_jp_congr_of_check body hccB ?_ hb⟩
      intro info hinfo vs
      have hne := ne_of_all_bne hjps_no hinfo
      simp [PJEnv.set, hne]
    have hJp_body : ∀ as rem' wr' rcr', as.length = ps.length →
        PRWp m (mkRcModEnv m) retTy Δr jps (baseCtx.bindParams ps) (Jp.set j Jj_p)
          (ρ.bindAll ps as) rem' wr' rcr' Qr Xr body → Jj_p as rem' wr' rcr' := by
      intro as rem' wr' rcr' hlen hrb hwb
      refine hJc_body as rem' wr' rcr' hlen
        (PWp_PRWp_combine hmwf body hccB hwfB ?_ hwb.2 hrb)
      intro info hinfo vs rem1 wr1 rcr1 hw_i hp_i
      have hne := ne_of_all_bne hjps_no hinfo
      simp only [PResJEnv.set, hne, ↓reduceIte] at hp_i ⊢
      exact hJ info hinfo vs rem1 wr1 rcr1 hw_i hp_i
    let jInfo : RcJpInfo := { id := j, params := ps, scopeIds := ctx.vars.map (·.id) }
    refine PWp_PRWp_combine hmwf k hccK hwfK ?_ (hp Jj_w hJw_body) (hr Jj_p hJp_body)
    intro info hinfo vs rem1 wr1 rcr1 hw_i hp_i
    rcases List.mem_cons.mp hinfo with rfl | hmem
    · simp only [PJEnv.set, PResJEnv.set, ↓reduceIte] at hw_i hp_i ⊢
      exact hp_i hw_i
    · have hne := ne_of_all_bne hjps_no hmem
      simp only [PJEnv.set, PResJEnv.set, hne, ↓reduceIte] at hw_i hp_i ⊢
      exact hJ info hmem vs rem1 wr1 rcr1 hw_i hp_i
  | .jmp j as, retTy, jps, ctx, _, jumps, Jw, Jp, Jc, ρ, rem, wr, rcr, Qp, Xp, Qr, Xr,
      hcc, _, hJ, hp, hr => by
    rw [checkCode.eq_3] at hcc
    cases hfj : jps.find? (·.id == j) with
    | none => simp [hfj] at hcc
    | some info =>
      have hmem := List.mem_of_find?_eq_some hfj
      have hid : info.id = j :=
        beq_iff_eq.mp (List.find?_some (p := fun x : RcJpInfo => x.id == j) hfj)
      rw [PWp.eq_3] at hp
      rw [PRWp.eq_3] at hr ⊢
      cases hev : ρ.evalArgs as with
      | none => simp [hev] at hr
      | some vs =>
        simp only [hev] at hp hr ⊢
        exact by
          simpa [hid] using hJ info hmem vs rem wr rcr
            (by simpa [hid] using hp) (by simpa [hid] using hr)
  | .cases x alts, retTy, jps, ctx, sm, jumps, Jw, Jp, Jc, ρ, rem, wr, rcr, Qp, Xp, Qr, Xr,
      hcc, hwf, hJ, hp, hr => by
    have hca := checkCode_cases_unwrap hcc
    rw [perceusCodeWf.eq_5] at hwf
    rw [PWp.eq_4] at hp
    rw [PRWp.eq_4] at hr ⊢
    cases hgx : ctx.get? x with
    | none => simp [hgx] at hwf hr
    | some vx =>
      cases hpx : ρ x with
      | none => simp [hpx] at hp hr
      | some pv =>
        cases htg : pv.tag? with
        | none => simp [hpx, htg] at hp hr
        | some tag =>
          simp only [hgx, hpx, Option.bind_some, htg] at hwf hp hr ⊢
          refine ⟨hr.1, ?_⟩
          let tgt? := (ctx.sharedPreds.find? (·.1 == x)).map Prod.snd
          have hdflt : ∀ alts1, (∀ a ∈ alts1, a ∈ alts) →
              (∃ j, checkAlts (mkRcModEnv m) retTy jps ctx x tgt? alts1 = .ok j) →
              perceusAltsWf (mkRcModEnv m) retTy jps ctx sm x vx.ty tgt? alts1 = true →
              PWpDfltAlts (modArityOf m) Δp Jw ρ Qp Xp alts1 →
              PRWpDfltAlts m (mkRcModEnv m) retTy Δr jps ctx Jp ρ rem wr rcr Qr Xr alts1 →
              PRWpDfltAlts m (mkRcModEnv m) retTy (combinedPRes Δp Δr) jps ctx Jc ρ
                rem wr rcr (fun r rem' wr' rcr' => Qp r ∧ Qr r rem' wr' rcr')
                (fun code rem' wr' rcr' => Xp code ∧ Xr code rem' wr' rcr') alts1 := by
            intro alts1 hsub hca1 hwf1 hp1 hr1
            induction alts1 with
            | nil => rw [PRWpDfltAlts.eq_1] at hr1; exact hr1
            | cons a rest ih =>
              rcases a with ⟨pat, b⟩
              obtain ⟨j0, hj0⟩ := hca1
              obtain ⟨⟨jb, hccb⟩, hcar⟩ := checkAlts_step_cons hj0
              have hlt_b : sizeOf b < 1 + x + sizeOf alts := by
                have := List.sizeOf_lt_of_mem (hsub (pat, b) List.mem_cons_self); simp_all; omega
              cases pat with
              | dflt =>
                rw [perceusAltsWf.eq_4 _ _ _ _ _ _ _ _ _ tgt?
                  (fun _ _ _ h => nomatch h)] at hwf1
                simp only [Bool.and_eq_true] at hwf1
                rw [PWpDfltAlts.eq_2] at hp1
                rw [PRWpDfltAlts.eq_2] at hr1 ⊢
                exact PWp_PRWp_combine hmwf b hccb hwf1.1.2 hJ hp1 hr1
              | ctor ci cname =>
                have hwfR : perceusAltsWf (mkRcModEnv m) retTy jps ctx sm x vx.ty tgt? rest =
                    true := by
                  cases ht : tgt? with
                  | none =>
                    rw [ht] at hwf1
                    rw [perceusAltsWf.eq_3 _ _ _ _ _ _ _ _ _ _ _ none
                      (fun _ _ h => nomatch h)] at hwf1
                    simp only [Bool.and_eq_true] at hwf1; exact hwf1.2
                  | some tgt =>
                    rw [ht] at hwf1
                    cases ci with
                    | zero =>
                      rw [perceusAltsWf.eq_2 _ _ _ _ _ _ _ _ _ _ _ _ cname rfl] at hwf1
                      simp only [Bool.and_eq_true] at hwf1; exact hwf1.2
                    | succ m0 =>
                      rw [perceusAltsWf.eq_3 _ _ _ _ _ _ _ _ _ _ _ (some tgt)
                        (fun _ _ _ h => by cases h)] at hwf1
                      simp only [Bool.and_eq_true] at hwf1; exact hwf1.2
                rw [PWpDfltAlts.eq_3] at hp1
                rw [PRWpDfltAlts.eq_3] at hr1 ⊢
                exact ih (fun e he => hsub e (List.mem_cons_of_mem _ he)) hcar hwfR hp1 hr1
          have hctor : ∀ alts1, (∀ a ∈ alts1, a ∈ alts) →
              (∃ j, checkAlts (mkRcModEnv m) retTy jps ctx x tgt? alts1 = .ok j) →
              perceusAltsWf (mkRcModEnv m) retTy jps ctx sm x vx.ty tgt? alts1 = true →
              ∀ dc dp dr : Prop, (dp → dr → dc) →
              PWpCtorAlts (modArityOf m) Δp Jw ρ Qp Xp tag alts1 dp →
              PRWpCtorAlts m (mkRcModEnv m) retTy Δr jps ctx x tgt? pv Jp ρ tag rem wr rcr
                Qr Xr alts1 dr →
              PRWpCtorAlts m (mkRcModEnv m) retTy (combinedPRes Δp Δr) jps ctx x tgt? pv Jc ρ tag
                rem wr rcr (fun r rem' wr' rcr' => Qp r ∧ Qr r rem' wr' rcr')
                (fun code rem' wr' rcr' => Xp code ∧ Xr code rem' wr' rcr') alts1 dc := by
            intro alts1 hsub hca1 hwf1 dc dp dr hdc hcp hcr
            induction alts1 with
            | nil =>
              rw [PWpCtorAlts.eq_1] at hcp
              rw [PRWpCtorAlts.eq_1] at hcr ⊢
              exact hdc hcp hcr
            | cons a rest ih =>
              rcases a with ⟨pat, b⟩
              have hlt_b : sizeOf b < 1 + x + sizeOf alts := by
                have := List.sizeOf_lt_of_mem (hsub (pat, b) List.mem_cons_self); simp_all; omega
              cases pat with
              | dflt =>
                obtain ⟨j0, hj0⟩ := hca1
                obtain ⟨⟨_, _⟩, hcar⟩ := checkAlts_step_cons hj0
                rw [perceusAltsWf.eq_4 _ _ _ _ _ _ _ _ _ tgt?
                  (fun _ _ _ h => nomatch h)] at hwf1
                simp only [Bool.and_eq_true] at hwf1
                rw [PWpCtorAlts.eq_3] at hcp
                rw [PRWpCtorAlts.eq_4] at hcr ⊢
                exact ih (fun e he => hsub e (List.mem_cons_of_mem _ he)) hcar hwf1.2 hcp hcr
              | ctor ci cname =>
                rw [PWpCtorAlts.eq_2] at hcp
                cases ht : tgt? with
                | some tgt =>
                  rw [ht] at hca1 hwf1 hcr
                  cases ci with
                  | zero =>
                    obtain ⟨j0', hj0'⟩ := hca1
                    obtain ⟨⟨jb', hccb'⟩, hcar'⟩ := checkAlts_step_cons hj0'
                    rw [perceusAltsWf.eq_2 _ _ _ _ _ _ _ _ _ _ _ _ cname rfl] at hwf1
                    simp only [Bool.and_eq_true] at hwf1
                    rw [PRWpCtorAlts.eq_2] at hcr ⊢
                    by_cases htg_eq : 0 = tag
                    · simp only [htg_eq, ↓reduceIte] at hcp hcr ⊢
                      exact ⟨hcr.1, PWp_PRWp_combine hmwf b hccb' hwf1.1.2 hJ hcp hcr.2⟩
                    · simp only [htg_eq, ↓reduceIte] at hcp hcr ⊢
                      exact by
                        simpa [ht] using ih (fun e he => hsub e (List.mem_cons_of_mem _ he))
                          (by simpa [ht] using hcar') (by simpa [ht] using hwf1.2) hcp
                          (by simpa [ht] using hcr)
                  | succ m0 =>
                    obtain ⟨j0', hj0'⟩ := hca1
                    obtain ⟨⟨jb', hccb'⟩, hcar'⟩ := checkAlts_step_cons hj0'
                    rw [perceusAltsWf.eq_3 _ _ _ _ _ _ _ _ _ _ _ (some tgt)
                      (fun _ _ _ h => by cases h)] at hwf1
                    simp only [Bool.and_eq_true] at hwf1
                    rw [PRWpCtorAlts.eq_3 _ _ _ _ _ _ _ (some tgt) _ _ _ _ _ _ _ _ _ _
                      (m0 + 1) _ _ _ (fun _ _ h => by cases h)] at hcr ⊢
                    by_cases htg_eq : m0 + 1 = tag
                    · simp only [htg_eq, ↓reduceIte] at hcp hcr ⊢
                      exact ⟨hcr.1, PWp_PRWp_combine hmwf b hccb' hwf1.1.2 hJ hcp hcr.2⟩
                    · simp only [htg_eq, ↓reduceIte] at hcp hcr ⊢
                      exact by
                        simpa [ht] using ih (fun e he => hsub e (List.mem_cons_of_mem _ he))
                          (by simpa [ht] using hcar') (by simpa [ht] using hwf1.2) hcp
                          (by simpa [ht] using hcr)
                | none =>
                  rw [ht] at hca1 hwf1 hcr
                  obtain ⟨j0', hj0'⟩ := hca1
                  obtain ⟨⟨jb', hccb'⟩, hcar'⟩ := checkAlts_step_cons hj0'
                  rw [perceusAltsWf.eq_3 _ _ _ _ _ _ _ _ _ _ _ none
                    (fun _ _ h => nomatch h)] at hwf1
                  simp only [Bool.and_eq_true] at hwf1
                  rw [PRWpCtorAlts.eq_3 _ _ _ _ _ _ _ none _ _ _ _ _ _ _ _ _ _
                    ci _ _ _ (fun _ h => nomatch h)] at hcr ⊢
                  by_cases htg_eq : ci = tag
                  · simp only [htg_eq, ↓reduceIte] at hcp hcr ⊢
                    exact ⟨hcr.1, PWp_PRWp_combine hmwf b hccb' hwf1.1.2 hJ hcp hcr.2⟩
                  · simp only [htg_eq, ↓reduceIte] at hcp hcr ⊢
                    exact by
                      simpa [ht] using ih (fun e he => hsub e (List.mem_cons_of_mem _ he))
                        (by simpa [ht] using hcar') (by simpa [ht] using hwf1.2) hcp
                        (by simpa [ht] using hcr)
          exact hctor alts (fun _ h => h) ⟨jumps, hca⟩ hwf _ _ _
            (fun h1 h2 => hdflt alts (fun _ h => h) ⟨jumps, hca⟩ hwf h1 h2) hp hr.2
  | .ret a, _, _, _, _, _, _, _, _, ρ, _, _, _, _, _, _, _, _, _, _, hp, hr => by
    rw [PWp.eq_5] at hp; rw [PRWp.eq_5] at hr ⊢
    cases ha : ρ.evalArg a <;> simp [ha] at hp hr ⊢; exact ⟨hp, hr⟩
  | .unreach, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp, hr => by
    rw [PWp.eq_6] at hp; rw [PRWp.eq_6] at hr ⊢; exact ⟨hp, hr⟩
  | .oset x i y k, retTy, jps, ctx, sm, jumps, Jw, Jp, Jc, ρ, rem, wr, rcr, Qp, Xp, Qr, Xr,
      hcc, hwf, hJ, hp, hr => by
    rw [checkCode.eq_7] at hcc
    cases h1 : ctx.checkExcl x "oset" with
    | error _ => simp [h1, Bind.bind, Except.bind] at hcc
    | ok _ =>
      simp only [h1, Bind.bind, Except.bind] at hcc
      cases h2 : ctx.consumeArg y with
      | error _ => simp [h2] at hcc
      | ok ctx1 =>
        simp only [h2] at hcc
        obtain ⟨vx, hgx, _⟩ := checkExcl_facts h1
        have hwfK : perceusCodeWf (mkRcModEnv m) retTy jps ctx1 sm k = true := by
          cases hy : y with
          | erased =>
            rw [hy] at h2 hwf
            rw [perceusCodeWf.eq_10 _ _ _ _ _ _ _ _ vx hgx] at hwf
            simp only [Bool.and_eq_true, h2] at hwf; exact hwf.2
          | var yid =>
            rw [hy] at h2 hwf
            rw [perceusCodeWf.eq_9 _ _ _ _ _ _ _ _ vx yid hgx] at hwf
            simp only [Bool.and_eq_true, h2] at hwf; exact hwf.2
        rw [PWp.eq_7] at hp; rw [PRWp.eq_7] at hr ⊢
        simp only [h2] at hr ⊢
        cases hx : ρ x <;> cases hy : ρ.evalArg y <;> simp [hx, hy] at hp hr ⊢
        rename_i xv yv
        cases hs : xv.setObj i yv with
        | none => simp [hs] at hr
        | some xv' => simp only [hs] at hp hr ⊢; exact PWp_PRWp_combine hmwf k hcc hwfK hJ hp hr
  | .uset x i y k, retTy, jps, ctx, sm, jumps, Jw, Jp, Jc, ρ, rem, wr, rcr, Qp, Xp, Qr, Xr,
      hcc, hwf, hJ, hp, hr => by
    rw [checkCode.eq_8] at hcc
    cases h1 : ctx.checkExcl x "uset" with
    | error _ => simp [h1, Bind.bind, Except.bind] at hcc
    | ok _ =>
      simp only [h1, Bind.bind, Except.bind] at hcc
      cases h2 : ctx.checkLive y with
      | error _ => simp [h2] at hcc
      | ok _ =>
        simp only [h2] at hcc
        have hwfK : perceusCodeWf (mkRcModEnv m) retTy jps ctx (initScalarBytes sm x i 0 8) k =
            true := by
          rw [perceusCodeWf.eq_12] at hwf; simp only [Bool.and_eq_true] at hwf; exact hwf.2
        rw [PWp.eq_8] at hp; rw [PRWp.eq_8] at hr ⊢
        cases hx : ρ x <;> cases hy : ρ y <;> simp [hx, hy] at hp hr ⊢
        rename_i xv yv
        cases hs : xv.setUsize i yv with
        | none => simp [hs] at hr
        | some xv' => simp only [hs] at hp hr ⊢; exact PWp_PRWp_combine hmwf k hcc hwfK hJ hp hr
  | .sset x n off y ty k, retTy, jps, ctx, sm, jumps, Jw, Jp, Jc, ρ, rem, wr, rcr,
      Qp, Xp, Qr, Xr, hcc, hwf, hJ, hp, hr => by
    rw [checkCode.eq_9] at hcc
    cases h1 : ctx.checkExcl x "sset" with
    | error _ => simp [h1, Bind.bind, Except.bind] at hcc
    | ok _ =>
      simp only [h1, Bind.bind, Except.bind] at hcc
      cases h2 : ctx.checkLive y with
      | error _ => simp [h2] at hcc
      | ok _ =>
        simp only [h2] at hcc
        have hwfK : perceusCodeWf (mkRcModEnv m) retTy jps ctx
            (initScalarBytes sm x n off ty.toTTy.bytes) k = true := by
          rw [perceusCodeWf.eq_13] at hwf; simp only [Bool.and_eq_true] at hwf; exact hwf.2
        rw [PWp.eq_9] at hp; rw [PRWp.eq_9] at hr ⊢
        cases hx : ρ x <;> cases hy : ρ y <;> simp [hx, hy] at hp hr ⊢
        rename_i xv yv
        cases hs : xv.setScalar n off ty yv with
        | none => simp [hs] at hr
        | some xv' => simp only [hs] at hp hr ⊢; exact PWp_PRWp_combine hmwf k hcc hwfK hJ hp hr
  | .setTag x cidx k, retTy, jps, ctx, sm, jumps, Jw, Jp, Jc, ρ, rem, wr, rcr,
      Qp, Xp, Qr, Xr, hcc, hwf, hJ, hp, hr => by
    rw [checkCode.eq_10] at hcc
    cases h1 : ctx.checkExcl x "setTag" with
    | error _ => simp [h1, Bind.bind, Except.bind] at hcc
    | ok _ =>
      simp only [h1, Bind.bind, Except.bind] at hcc
      have hwfK : perceusCodeWf (mkRcModEnv m) retTy jps ctx sm k = true := by
        rw [perceusCodeWf.eq_14] at hwf; simp only [Bool.and_eq_true] at hwf; exact hwf.2
      rw [PWp.eq_10] at hp; rw [PRWp.eq_10] at hr ⊢
      cases hs : (ρ x).bind (·.setTag cidx) with
      | none => simp [hs] at hr
      | some xv' => simp only [hs] at hp hr ⊢; exact PWp_PRWp_combine hmwf k hcc hwfK hJ hp hr
  | .inc x n chk k, retTy, jps, ctx, sm, jumps, Jw, Jp, Jc, ρ, rem, wr, rcr,
      Qp, Xp, Qr, Xr, hcc, hwf, hJ, hp, hr => by
    rw [checkCode.eq_11] at hcc
    cases hgx : ctx.get? x with
    | none => simp [hgx] at hcc
    | some v =>
      simp only [hgx] at hcc
      cases hlv : !v.isLive with
      | true => simp [hlv, Bind.bind, Except.bind] at hcc
      | false =>
        simp only [hlv, Bool.false_eq_true, ↓reduceIte] at hcc
        rw [PWp.eq_11] at hp; rw [PRWp.eq_11] at hr ⊢
        simp only [hgx] at hr ⊢
        rw [perceusCodeWf.eq_15] at hwf
        simp only [hgx, Bool.and_eq_true] at hwf
        by_cases hskip : (v.noRc || v.persistent || n == 0) = true
        · simp only [hskip, ↓reduceIte] at hcc hwf hr ⊢
          exact PWp_PRWp_combine hmwf k hcc hwf.2.2 hJ hp hr
        · simp only [hskip, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hcc hwf hr ⊢
          exact ⟨hr.1, PWp_PRWp_combine hmwf k hcc hwf.2.2.2 hJ hp hr.2⟩
  | .dec x n chk k, retTy, jps, ctx, sm, jumps, Jw, Jp, Jc, ρ, rem, wr, rcr,
      Qp, Xp, Qr, Xr, hcc, hwf, hJ, hp, hr => by
    rw [checkCode.eq_12] at hcc
    cases h1 : ctx.consumeVar x n with
    | error _ => simp [h1, Bind.bind, Except.bind] at hcc
    | ok ctx1 =>
      simp only [h1, Bind.bind, Except.bind] at hcc
      have hwfK : perceusCodeWf (mkRcModEnv m) retTy jps ctx1 sm k = true := by
        rw [perceusCodeWf.eq_16] at hwf
        cases hgx : ctx.get? x with
        | none => simp [hgx] at hwf
        | some v => simp only [hgx, h1, Bool.and_eq_true] at hwf; exact hwf.2
      rw [PWp.eq_12] at hp; rw [PRWp.eq_12] at hr ⊢
      simp only [h1] at hr ⊢
      exact ⟨hr.1, PWp_PRWp_combine hmwf k hcc hwfK hJ hp hr.2⟩
  | .del x k, retTy, jps, ctx, sm, jumps, Jw, Jp, Jc, ρ, rem, wr, rcr,
      Qp, Xp, Qr, Xr, hcc, hwf, hJ, hp, hr => by
    rw [checkCode.eq_13] at hcc
    cases h1 : ctx.checkExcl x "del" with
    | error _ => simp [h1, Bind.bind, Except.bind] at hcc
    | ok _ =>
      simp only [h1, Bind.bind, Except.bind] at hcc
      cases h2 : ctx.consumeVar x with
      | error _ => simp [h2] at hcc
      | ok ctx1 =>
        simp only [h2] at hcc
        have hwfK : perceusCodeWf (mkRcModEnv m) retTy jps ctx1 (sm.filter (·.1 != x)) k =
            true := by
          rw [perceusCodeWf.eq_17] at hwf; simp only [h2] at hwf; exact hwf
        rw [PWp.eq_13] at hp; rw [PRWp.eq_13] at hr ⊢
        simp only [h2] at hr ⊢
        exact PWp_PRWp_combine hmwf k hcc hwfK hJ hp hr
termination_by c => sizeOf c
decreasing_by all_goals (simp; try (first | exact hlt_b | omega))

private theorem prCallCompat_of_hOfP {m : LcModule} {Δp : PEnv} {Δr : PResEnv}
    (hpres : PResOk Δr m) :
    PRCallCompat m (combinedPRes Δp Δr) (hOfP m Δp) := by
  unfold PRCallCompat
  intro rt d calleeRf σ pvs ws rem wr rcr P E hd hrf hpvs hws hrc _ _ hhih hres hcomb
  have _ := hws
  rcases hcomb with ⟨Qp, Xp, Pr, Er, hdp, hdr, hP, hE⟩
  let Ph : HPost := fun rw σ' =>
    CallPostOk rt d (calleeRf.extH ++ calleeRf.ghostH) (nonScalarWords d.params ws) σ σ' rw P
  let Eh : HXPost := fun c σ' => CallExcOk rt σ' c E
  refine ⟨Ph, Eh, ?_, fun _ _ h => h, fun _ _ h => h⟩
  exact ⟨rt, d, Δr, pvs, calleeRf.extH, calleeRf.ghostH, rem, wr, rcr, Qp, Xp, Pr, Er,
    hd, rfl, hpres, hrf ▸ hrc, hhih, hres, hpvs, hdp, hdr,
    fun r rw σ' rem' wr' rcr' hqp hpr hc' hres' hvr hno hsnd hcpres =>
      ⟨r, rem', wr', rcr', hP r rem' wr' rcr' hqp hpr, hc', hvr, hno,
        List.append_assoc _ _ _ ▸ hsnd, hcpres, hres'⟩,
    fun c rem' wr' rcr' σ' hxp her => ⟨c, rem', wr', rcr', hE c rem' wr' rcr' hxp her, rfl⟩⟩

private theorem prCallCompat_of_hOfPIdx {m : LcModule} {Δp : Nat → PEnv} {Δr : Nat → PResEnv}
    (hpres : PResOkIdx Δr m) (k : Nat) :
    PRCallCompat m
      (combinedPRes (match k with | 0 => PEnv.bot | k' + 1 => Δp k')
        (match k with | 0 => PResEnv.bot | k' + 1 => Δr k'))
      (match k with | 0 => HEnv.bot | k' + 1 => hOfPIdx m Δp k') := by
  unfold PRCallCompat
  intro rt d calleeRf σ pvs ws rem wr rcr P E hd hrf hpvs hws hrc _ _ hhih hres hcomb
  have _ := hws
  rcases hcomb with ⟨Qp, Xp, Pr, Er, hdp, hdr, hP, hE⟩
  cases k with
  | zero => exact False.elim hdp
  | succ k' =>
    let Ph : HPost := fun rw σ' =>
      CallPostOk rt d (calleeRf.extH ++ calleeRf.ghostH) (nonScalarWords d.params ws) σ σ' rw P
    let Eh : HXPost := fun c σ' => CallExcOk rt σ' c E
    refine ⟨Ph, Eh, ?_, fun _ _ h => h, fun _ _ h => h⟩
    exact ⟨rt, d, Δr, pvs, calleeRf.extH, calleeRf.ghostH, rem, wr, rcr, Qp, Xp, Pr, Er,
      hd, rfl, hpres, hrf ▸ hrc, hhih, hres, hpvs, hdp, hdr,
      fun r rw σ' rem' wr' rcr' hqp hpr hc' hres' hvr hno hsnd hcpres =>
        ⟨r, rem', wr', rcr', hP r rem' wr' rcr' hqp hpr, hc', hvr, hno,
          List.append_assoc _ _ _ ▸ hsnd, hcpres, hres'⟩,
      fun c rem' wr' rcr' σ' hxp her => ⟨c, rem', wr', rcr', hE c rem' wr' rcr' hxp her, rfl⟩⟩

/-- **Top-level Perceus Soundness (`perceus_sound`)**:
if `m` passes `RcCheck`, `perceusModWf`, and pure `PModuleOk Δp m`,
then `m` satisfies Tier-H `HModuleOk (hOfP m Δp) m`. -/
public theorem perceus_sound {m : LcModule} {Δp : PEnv}
    (hrc : RcCheck m = true) (hmwf : perceusModWf m = true) (hpure : PModuleOk Δp m) :
    HModuleOk (hOfP m Δp) m := by
  unfold HModuleOk
  intro d hd rt as σ Q X hinv hmatch hspec
  obtain ⟨rt0, d', Δr', pvs, extH, ghostH, rem₀, wr₀, rcr₀, Qp, Xp, Pr, Er,
    hd', hnm, hres', hrc0, hhih, hres_s, hlen, hdp, hdr, hq, hx⟩ := hspec
  obtain ⟨hnd, hmod⟩ := perceusModWf_facts hmwf
  obtain rfl : d = d' := (mod_decl_unique hnd hd hd' hnm).symm
  have hmwf' : ∀ d0 ∈ m.decls,
      !isPrimName d0.name = true ∧ (d0.params.map LcParam.id).Nodup :=
    fun d0 hd0 => ⟨(hmod d0 hd0).1, (hmod d0 hd0).2.1⟩
  obtain ⟨jumps, hcc⟩ := rcCheck_decl_checkCode hrc hd
  have hw := hpure d hd pvs Qp Xp hlen hdp
  have hr := hres' d hd pvs rem₀ wr₀ rcr₀ Pr Er hlen hdr
  have hpr := PWp_PRWp_combine hmwf' d.body (Jc := PResJEnv.empty) hcc (hmod d hd).2.2
    (fun _ h => nomatch h) hw hr
  exact perceus_decl_ok_res hrc hmwf (prCallCompat_of_hOfP hres') hd hlen hmatch hrc0 hhih hres_s
    hinv hpr
    (fun r rw σ' rem' wr' rcr' ⟨hqp, hpr_ok⟩ =>
      hq r rw σ' rem' wr' rcr' hqp hpr_ok)
    (fun c rem' wr' rcr' σ' ⟨hxp, her⟩ => hx c rem' wr' rcr' σ' hxp her)

/-- **Top-level Indexed Perceus Soundness (`perceus_sound_idx`)**:
measure-indexed soundness for recursive / self-tail modules `PModuleOkIdx Δp m`. -/
public theorem perceus_sound_idx {m : LcModule} {Δp : Nat → PEnv}
    (hrc : RcCheck m = true) (hmwf : perceusModWf m = true) (hpure : PModuleOkIdx Δp m) :
    HModuleOkIdx (hOfPIdx m Δp) m := by
  unfold HModuleOkIdx
  refine ⟨hOfPIdx_le hpure.1, fun k d hd rt as σ Q X hinv hmatch hspec => ?_⟩
  obtain ⟨rt0, d', Δr', pvs, extH, ghostH, rem₀, wr₀, rcr₀, Qp, Xp, Pr, Er,
    hd', hnm, hres', hrc0, hhih, hres_s, hlen, hdp, hdr, hq, hx⟩ := hspec
  obtain ⟨hnd, hmod⟩ := perceusModWf_facts hmwf
  obtain rfl : d = d' := (mod_decl_unique hnd hd hd' hnm).symm
  have hmwf' : ∀ d0 ∈ m.decls,
      !isPrimName d0.name = true ∧ (d0.params.map LcParam.id).Nodup :=
    fun d0 hd0 => ⟨(hmod d0 hd0).1, (hmod d0 hd0).2.1⟩
  obtain ⟨jumps, hcc⟩ := rcCheck_decl_checkCode hrc hd
  have hw := hpure.2 k d hd pvs Qp Xp hlen hdp
  have hr := hres'.2 k d hd pvs rem₀ wr₀ rcr₀ Pr Er hlen hdr
  have hpr := PWp_PRWp_combine hmwf' d.body (Jc := PResJEnv.empty) hcc (hmod d hd).2.2
    (fun _ h => nomatch h) hw hr
  exact perceus_decl_ok_res hrc hmwf
    (prCallCompat_of_hOfPIdx hres' k) hd hlen hmatch hrc0 hhih hres_s hinv hpr
    (fun r rw σ' rem' wr' rcr' ⟨hqp, hpr_ok⟩ =>
      hq r rw σ' rem' wr' rcr' hqp hpr_ok)
    (fun c rem' wr' rcr' σ' ⟨hxp, her⟩ => hx c rem' wr' rcr' σ' hxp her)

end LeanQbe.T.LeanLCNF.Sem
