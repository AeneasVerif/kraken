module

public import LeanQbe.T.LeanLCNF.Sem.PerceusLetPrim

/-!
# Perceus `let_` Simulation Dispatcher (`PerceusLet`)

Simulates pure, allocation, projection, `box`, `unbox`, `isShared`, and `.fap` `let_`
expressions using `PerceusLet2`, `PerceusLet3`, and `PerceusLetPrim`, exposing `letVal_step`
and `let_step`.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

public section

/-! ### Step helpers -/

private theorem checkLive_bind_ok {α : Type} {ctx : RcCtx} {y : Nat} {vy : RcVar}
    {f : α} {r : α} (hgety : ctx.get? y = some vy)
    (heq : (do ctx.checkLive y; pure f) = Except.ok r) :
    r = f ∧ vy.isLive = true := by
  unfold RcCtx.checkLive at heq
  simp only [hgety] at heq
  cases hlv : vy.isLive
  · simp only [hlv, ↓reduceIte, Bool.false_eq_true, Bind.bind, Except.bind] at heq
    cases heq
  · simp only [hlv, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure] at heq
    cases heq; exact ⟨rfl, rfl⟩

private theorem readNatLE_p_eq (bs : List UInt8) (k off : Nat) :
    PVal.readNatLE bs off k = readNatLE bs off k := by
  induction k generalizing off with
  | zero => rfl
  | succ k ih =>
    change (bs.getD off 0).toNat + 256 * PVal.readNatLE bs (off + 1) k =
      (bs.getD off 0).toNat + 256 * readNatLE bs (off + 1) k
    rw [ih]

private theorem readBitsLE_p_eq (w : Nat) (bs : List UInt8) (off : Nat) :
    PVal.readBitsLE w bs off = readBitsLE w bs off := by
  unfold PVal.readBitsLE readBitsLE; rw [readNatLE_p_eq]

private theorem let_nonPtr_wrap {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {x : Nat} {ty : LcTy}
    {pv : PVal} {w : Word} {jpsOk : List JpEntry} {Jp : PResJEnv} {Jh : HJEnv}
    {jumps : List (Nat × RcCtx)} {K : PResPost} {rem wr rcr : Nat} {Kh : HPost}
    (hjok : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps)
    (hrc : RcInv rt rf σ) (hcl : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbp : SharedBoolPreds rf.ctx) (hex : ExclCtorHeap rf)
    (hsh : ShadowOk sm rf.ctx ρP rf.envP) (hsmwf : ShadowSmWf sm)
    (hres : ResStateInv σ rem wr rcr) (hjsc : JpsScopeIn (jpsOk.map JpEntry.info) rf.ctx)
    (hfr : binderFreshOwned rf.ctx x = true)
    (hvr : ValRep ty pv w σ.objs)
    (hodd : ¬ty.isScalar = true → ∃ bv, w = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64)
    (hK : K pv rem wr rcr)
    (hcont : ∀ {rf' : RcFrame} {σ' : HState} {sm' : List (Nat × Nat × List Bool)}
      {ρP' : PValEnv} {rem' wr' rcr' : Nat} {jpsOk' : List JpEntry} {pv' : PVal} {rw : Word},
      K pv' rem' wr' rcr' →
      rf'.ctx = rf.ctx.bindOwned x ty → rf'.envH = rf.envH.set x ty rw → ρP' = ρP.set x pv' →
      sm' = sm.filter (·.1 != x) →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → SharedBoolPreds rf'.ctx → ExclCtorHeap rf' →
      ShadowSmWf sm' → ShadowOk sm' rf'.ctx ρP' rf'.envP →
      ResStateInv σ' rem' wr' rcr' →
      JpsScopeIn (jpsOk'.map JpEntry.info) rf'.ctx →
      JpsOk rt rf0 σ0 Jp Jh jpsOk' rf' ρP' jumps →
      jpsOk' = jpsOk.map (fun e => { e with mutVars := x :: e.mutVars }) →
      Kh rw σ') :
    Kh w σ := by
  have hsteps := bind_nonPtr_step_invs hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh hfr hvr hodd
  rcases hsteps with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  let ctx' := rf.ctx.bindOwned x ty
  let rf' : RcFrame :=
    ⟨ctx', rf.envP.set x pv, rf.envH.set x ty w, rf.extH, rf.ghostH⟩
  have hjsc' : JpsScopeIn ((jpsOk.map fun e => { e with mutVars := x :: e.mutVars }).map
      JpEntry.info) ctx' := by
    simp; exact jpsScopeIn_put hrc.2.1 hjsc
  have hjok' := jpsOk_let_step (rf' := rf') (ρP' := ρP.set x pv) hjok
    (ctx_step_props_bindOwned hrc.2.1 hfr ty)
    (fun z hz => by simp [rf', PValEnv.set, HValEnv.set, hz]) rfl
  exact hcont (rf' := rf') (ρP' := ρP.set x pv) (pv' := pv) (rw := w)
    hK rfl rfl rfl rfl h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    (shadowSmWf_filter_ne hsmwf) h12 hres hjsc' hjok' rfl

private theorem uproj_step {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {x i y : Nat} {ty : LcTy}
    {env : RcModEnv} {Δr : PResEnv} {jpsOk : List JpEntry} {Jp : PResJEnv} {Jh : HJEnv}
    {jumps : List (Nat × RcCtx)} {rem wr rcr : Nat} {K : PResPost} {Xp : PResXPost}
    {Δh : HEnv} {Kh : HPost} {Xh : HXPost} {ctx' : RcCtx}
    (hpvwf : perceusValWf env rf.ctx x ty (.uproj i y) = true)
    (hsv : valScalarWf sm ty (.uproj i y) = true)
    (hcv : checkVal env rf.ctx x ty (.uproj i y) = .ok ctx')
    (hpr : PRValWp env Δr ρP ty (.uproj i y) rem wr rcr K Xp)
    (hjok : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps)
    (hrc : RcInv rt rf σ) (hcl : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbp : SharedBoolPreds rf.ctx) (hex : ExclCtorHeap rf)
    (hsh : ShadowOk sm rf.ctx ρP rf.envP) (hsmwf : ShadowSmWf sm)
    (hres : ResStateInv σ rem wr rcr) (hjsc : JpsScopeIn (jpsOk.map JpEntry.info) rf.ctx)
    (hcont : ∀ {rf' : RcFrame} {σ' : HState} {sm' : List (Nat × Nat × List Bool)}
      {ρP' : PValEnv} {rem' wr' rcr' : Nat} {jpsOk' : List JpEntry} {pv : PVal} {rw : Word},
      K pv rem' wr' rcr' →
      rf'.ctx = ctx' → rf'.envH = rf.envH.set x ty rw → ρP' = ρP.set x pv →
      sm' = sm.filter (·.1 != x) →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → SharedBoolPreds rf'.ctx → ExclCtorHeap rf' →
      ShadowSmWf sm' → ShadowOk sm' rf'.ctx ρP' rf'.envP →
      ResStateInv σ' rem' wr' rcr' →
      JpsScopeIn (jpsOk'.map JpEntry.info) rf'.ctx →
      JpsOk rt rf0 σ0 Jp Jh jpsOk' rf' ρP' jumps →
      jpsOk' = jpsOk.map (fun e => { e with mutVars := x :: e.mutVars }) →
      Kh rw σ') :
    HVal.wp Δh rt rf.envH ty (.uproj i y) Kh Xh σ := by
  unfold perceusValWf at hpvwf
  simp only [Bool.and_eq_true, beq_iff_eq] at hpvwf
  rcases hpvwf with ⟨hfr, ⟨⟨hsc, hw64⟩, hvy_m⟩⟩
  cases hgety : rf.ctx.get? y with
  | none => simp [hgety] at hvy_m
  | some vy =>
    simp only [hgety, Bool.and_eq_true] at hvy_m
    rcases hvy_m with ⟨hns_y, _⟩
    have hns_y' : vy.ty.isScalar = false := by simpa using hns_y
    have hctx'_eq : ctx' = rf.ctx.bindOwned x ty ∧ vy.isLive = true := by
      unfold checkVal at hcv
      exact checkLive_bind_ok hgety hcv
    rcases hctx'_eq with ⟨rfl, hlive_y⟩
    unfold valScalarWf at hsv
    unfold PRValWp at hpr
    cases hrho : ρP y with
    | none => simp [hrho] at hpr
    | some pv_y =>
      cases pv_y with
      | ctor cidx fs pscal =>
        simp only [hrho, Option.bind_some] at hpr
        cases hgu : PVal.getUsize? (.ctor cidx fs pscal) i with
        | none => rw [hgu] at hpr; cases hpr
        | some r =>
          rw [hgu] at hpr
          dsimp only at hpr
          dsimp only [PVal.getUsize?] at hgu
          by_cases hfl : fs.length ≤ i
          · simp only [hfl, ↓reduceIte] at hgu
            have hgu' : (if 8 * (i - fs.length) + 8 ≤ pscal.length then
                some (PVal.bits 64 (PVal.readBitsLE 64 pscal (8 * (i - fs.length)))) else none) =
                some r := hgu
            by_cases hbb : 8 * (i - fs.length) + 8 ≤ pscal.length
            · simp only [hbb, ↓reduceIte] at hgu'
              cases hgu'
              obtain ⟨hscal, henv_y, hlen_eq, hbytes⟩ :=
                shadowOk_ctor_bytes hsh hgety hlive_y hsv hrho hfl
                  (by simpa [Nat.add_zero] using hbb)
              obtain ⟨_, w_y, hev_py, hev_hy, hvr_y, _⟩ :=
                hrc.2.2.2.1 vy (RcCtx.get?_mem hgety).1 hlive_y
              rw [(RcCtx.get?_mem hgety).2] at hev_py hev_hy
              rw [henv_y] at hev_py; cases hev_py
              unfold ValRep at hvr_y
              simp only [hns_y', Bool.false_eq_true, ↓reduceIte] at hvr_y
              rcases hvr_y with ⟨bv_y, rfl, hobj_y, _⟩
              unfold ObjRep at hobj_y
              rcases hobj_y with
                ⟨rfl, rfl, _, _⟩ | ⟨_, o_y, ho_y, ha_y, _, _, hle244, hsc_eq, hfrep⟩
              · rw [← hlen_eq] at hbb; simp at hbb
              · have hfl_eq : o_y.fields.length = fs.length := (objFieldsRep_length hfrep).symm
                have hi_o : o_y.fields.length ≤ i := by rw [hfl_eq]; omega
                have hb_o : 8 * (i - o_y.fields.length) + 8 ≤ o_y.scalarData.length := by
                  rw [hfl_eq, hsc_eq, hlen_eq]; exact hbb
                have hr_eq : PVal.readBitsLE 64 pscal (8 * (i - fs.length)) =
                    readBitsLE 64 o_y.scalarData (8 * (i - o_y.fields.length)) := by
                  rw [readBitsLE_p_eq, hfl_eq, hsc_eq]
                  exact readBitsLE_congr fun d hd =>
                    hbytes d (by
                      rw [show (64 + 7) / 8 = 8 by decide] at hd
                      simpa [Nat.add_zero] using hd)
                have hvr_res : ValRep ty
                    (PVal.bits 64 (PVal.readBitsLE 64 pscal (8 * (i - fs.length))))
                    (Word.i64 (readBitsLE 64 o_y.scalarData (8 * (i - o_y.fields.length))))
                    σ.objs := by
                  cases ty <;>
                    first
                    | (cases hsc; done)
                    | (cases hw64; done)
                    | (simp only [ValRep, LcTy.isScalar, ↓reduceIte, ScalarRep, LcTy.width];
                       exact Or.inl ⟨PVal.readBitsLE 64 pscal (8 * (i - fs.length)), rfl, by
                         rw [hr_eq, Word.i64]⟩)
                simp only [HVal.wp, getBV64_of_envH hev_hy]
                refine ⟨o_y, ho_y, ha_y, hrc.1.1.2.1 o_y ho_y, hle244, hi_o, hb_o, ?_⟩
                exact let_nonPtr_wrap hjok hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh
                  hsmwf hres hjsc hfr hvr_res (fun h => absurd hsc (by simp [h])) hpr hcont
            · simp only [hbb, ↓reduceIte] at hgu'
              cases hgu'
          · simp only [hfl, ↓reduceIte] at hgu
            cases hgu
      | _ => simp [hrho, PVal.getUsize?] at hpr

private theorem sproj_step {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {x n off y : Nat} {ty : LcTy}
    {env : RcModEnv} {Δr : PResEnv} {jpsOk : List JpEntry} {Jp : PResJEnv} {Jh : HJEnv}
    {jumps : List (Nat × RcCtx)} {rem wr rcr : Nat} {K : PResPost} {Xp : PResXPost}
    {Δh : HEnv} {Kh : HPost} {Xh : HXPost} {ctx' : RcCtx}
    (hpvwf : perceusValWf env rf.ctx x ty (.sproj n off y) = true)
    (hsv : valScalarWf sm ty (.sproj n off y) = true)
    (hcv : checkVal env rf.ctx x ty (.sproj n off y) = .ok ctx')
    (hpr : PRValWp env Δr ρP ty (.sproj n off y) rem wr rcr K Xp)
    (hjok : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps)
    (hrc : RcInv rt rf σ) (hcl : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbp : SharedBoolPreds rf.ctx) (hex : ExclCtorHeap rf)
    (hsh : ShadowOk sm rf.ctx ρP rf.envP) (hsmwf : ShadowSmWf sm)
    (hres : ResStateInv σ rem wr rcr) (hjsc : JpsScopeIn (jpsOk.map JpEntry.info) rf.ctx)
    (hcont : ∀ {rf' : RcFrame} {σ' : HState} {sm' : List (Nat × Nat × List Bool)}
      {ρP' : PValEnv} {rem' wr' rcr' : Nat} {jpsOk' : List JpEntry} {pv : PVal} {rw : Word},
      K pv rem' wr' rcr' →
      rf'.ctx = ctx' → rf'.envH = rf.envH.set x ty rw → ρP' = ρP.set x pv →
      sm' = sm.filter (·.1 != x) →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → SharedBoolPreds rf'.ctx → ExclCtorHeap rf' →
      ShadowSmWf sm' → ShadowOk sm' rf'.ctx ρP' rf'.envP →
      ResStateInv σ' rem' wr' rcr' →
      JpsScopeIn (jpsOk'.map JpEntry.info) rf'.ctx →
      JpsOk rt rf0 σ0 Jp Jh jpsOk' rf' ρP' jumps →
      jpsOk' = jpsOk.map (fun e => { e with mutVars := x :: e.mutVars }) →
      Kh rw σ') :
    HVal.wp Δh rt rf.envH ty (.sproj n off y) Kh Xh σ := by
  unfold perceusValWf at hpvwf
  simp only [Bool.and_eq_true] at hpvwf
  rcases hpvwf with ⟨hfr, ⟨hsc, hvy_m⟩⟩
  cases hgety : rf.ctx.get? y with
  | none => simp [hgety] at hvy_m
  | some vy =>
    simp only [hgety, Bool.and_eq_true] at hvy_m
    rcases hvy_m with ⟨hns_y, _⟩
    have hns_y' : vy.ty.isScalar = false := by simpa using hns_y
    have hctx'_eq : ctx' = rf.ctx.bindOwned x ty ∧ vy.isLive = true := by
      unfold checkVal at hcv
      exact checkLive_bind_ok hgety hcv
    rcases hctx'_eq with ⟨rfl, hlive_y⟩
    unfold valScalarWf at hsv
    unfold PRValWp at hpr
    cases hrho : ρP y with
    | none => simp [hrho] at hpr
    | some pv_y =>
      cases pv_y with
      | ctor cidx fs pscal =>
        simp only [hrho, Option.bind_some] at hpr
        cases hgs : PVal.getScalar? (.ctor cidx fs pscal) n off ty with
        | none => rw [hgs] at hpr; cases hpr
        | some r =>
          rw [hgs] at hpr
          dsimp only at hpr
          dsimp only [PVal.getScalar?] at hgs
          by_cases hfl : fs.length ≤ n
          · simp only [hfl, ↓reduceIte] at hgs
            have hgs' : (if 8 * (n - fs.length) + off + ty.toTTy.bytes ≤ pscal.length then
                some (PVal.bits ty.width
                  (PVal.readBitsLE ty.width pscal (8 * (n - fs.length) + off)))
                else none) = some r := hgs
            by_cases hbb : 8 * (n - fs.length) + off + ty.toTTy.bytes ≤ pscal.length
            · simp only [hbb, ↓reduceIte] at hgs'
              cases hgs'
              obtain ⟨hscal, henv_y, hlen_eq, hbytes⟩ :=
                shadowOk_ctor_bytes hsh hgety hlive_y hsv hrho hfl hbb
              obtain ⟨_, w_y, hev_py, hev_hy, hvr_y, _⟩ :=
                hrc.2.2.2.1 vy (RcCtx.get?_mem hgety).1 hlive_y
              rw [(RcCtx.get?_mem hgety).2] at hev_py hev_hy
              rw [henv_y] at hev_py; cases hev_py
              unfold ValRep at hvr_y
              simp only [hns_y', Bool.false_eq_true, ↓reduceIte] at hvr_y
              rcases hvr_y with ⟨bv_y, rfl, hobj_y, _⟩
              unfold ObjRep at hobj_y
              rcases hobj_y with
                ⟨rfl, rfl, _, _⟩ | ⟨_, o_y, ho_y, ha_y, _, _, hle244, hsc_eq, hfrep⟩
              · rw [← hlen_eq, List.length_nil] at hbb
                have : 0 < ty.toTTy.bytes := by cases ty <;> simp [LcTy.toTTy, Ty.bytes, LcTy.width]
                omega
              · have hfl_eq : o_y.fields.length = fs.length := (objFieldsRep_length hfrep).symm
                have hi_o : o_y.fields.length ≤ n := by rw [hfl_eq]; exact hfl
                have hb_o : 8 * (n - o_y.fields.length) + off + ty.toTTy.bytes ≤
                    o_y.scalarData.length := by
                  rw [hfl_eq, hsc_eq, hlen_eq]; exact hbb
                have hr_eq : PVal.readBitsLE ty.width pscal (8 * (n - fs.length) + off) =
                    readBitsLE ty.width o_y.scalarData (8 * (n - o_y.fields.length) + off) := by
                  rw [readBitsLE_p_eq, hfl_eq, hsc_eq]
                  exact readBitsLE_congr fun d hd =>
                    hbytes d (by simpa [LcTy.toTTy, Ty.bytes, Ty.size] using hd)
                have hvr_res : ValRep ty
                    (PVal.bits ty.width
                      (PVal.readBitsLE ty.width pscal (8 * (n - fs.length) + off)))
                    ⟨ty.toTTy,
                      readBitsLE ty.width o_y.scalarData (8 * (n - o_y.fields.length) + off)⟩
                    σ.objs := by
                  simp only [ValRep, hsc, ↓reduceIte, ScalarRep, LcTy.toTTy]
                  left
                  exact ⟨PVal.readBitsLE ty.width pscal (8 * (n - fs.length) + off), rfl,
                    by rw [hr_eq]⟩
                simp only [HVal.wp, getBV64_of_envH hev_hy]
                refine ⟨o_y, ho_y, ha_y, hrc.1.1.2.1 o_y ho_y, hle244, hi_o, hb_o, ?_⟩
                exact let_nonPtr_wrap hjok hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh
                  hsmwf hres hjsc hfr hvr_res (fun h => absurd hsc (by simp [h])) hpr hcont
            · simp only [hbb, ↓reduceIte] at hgs'
              cases hgs'
          · simp only [hfl, ↓reduceIte] at hgs
            cases hgs
      | _ => simp [hrho, PVal.getScalar?] at hpr

private theorem oproj_step {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {x i y : Nat} {ty : LcTy}
    {env : RcModEnv} {Δr : PResEnv} {jpsOk : List JpEntry} {Jp : PResJEnv} {Jh : HJEnv}
    {jumps : List (Nat × RcCtx)} {rem wr rcr : Nat} {K : PResPost} {Xp : PResXPost}
    {Δh : HEnv} {Kh : HPost} {Xh : HXPost} {ctx' : RcCtx}
    (hpvwf : perceusValWf env rf.ctx x ty (.oproj i y) = true)
    (hcv : checkVal env rf.ctx x ty (.oproj i y) = .ok ctx')
    (hpr : PRValWp env Δr ρP ty (.oproj i y) rem wr rcr K Xp)
    (hjok : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps)
    (hrc : RcInv rt rf σ) (hcl : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbp : SharedBoolPreds rf.ctx) (hex : ExclCtorHeap rf)
    (hsh : ShadowOk sm rf.ctx ρP rf.envP) (hsmwf : ShadowSmWf sm)
    (hres : ResStateInv σ rem wr rcr) (hjsc : JpsScopeIn (jpsOk.map JpEntry.info) rf.ctx)
    (hcont : ∀ {rf' : RcFrame} {σ' : HState} {sm' : List (Nat × Nat × List Bool)}
      {ρP' : PValEnv} {rem' wr' rcr' : Nat} {jpsOk' : List JpEntry} {pv : PVal} {rw : Word},
      K pv rem' wr' rcr' →
      rf'.ctx = ctx' → rf'.envH = rf.envH.set x ty rw → ρP' = ρP.set x pv →
      sm' = sm.filter (·.1 != x) →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → SharedBoolPreds rf'.ctx → ExclCtorHeap rf' →
      ShadowSmWf sm' → ShadowOk sm' rf'.ctx ρP' rf'.envP →
      ResStateInv σ' rem' wr' rcr' →
      JpsScopeIn (jpsOk'.map JpEntry.info) rf'.ctx →
      JpsOk rt rf0 σ0 Jp Jh jpsOk' rf' ρP' jumps →
      jpsOk' = jpsOk.map (fun e => { e with mutVars := x :: e.mutVars }) →
      Kh rw σ') :
    HVal.wp Δh rt rf.envH ty (.oproj i y) Kh Xh σ := by
  unfold perceusValWf at hpvwf
  simp only [Bool.and_eq_true] at hpvwf
  rcases hpvwf with ⟨hfr, ⟨hty_o, hvy_m⟩⟩
  have hty_eq : ty = .tobject := (lcTy_beq_iff ty .tobject).mp hty_o
  subst hty_eq
  cases hgety : rf.ctx.get? y with
  | none => simp [hgety] at hvy_m
  | some vy =>
    simp only [hgety, Bool.and_eq_true] at hvy_m
    rcases hvy_m with ⟨hns_y, _⟩
    have hns_y' : vy.ty.isScalar = false := by simpa using hns_y
    cases hpb : rf.ctx.projBacking y with
    | error e =>
      unfold checkVal at hcv
      simp only [hpb, Bind.bind, Except.bind] at hcv
      cases hcv
    | ok bp =>
      rcases bp with ⟨p?, pers⟩
      have hctx'_eq : ctx' = rf.ctx.bindBorrowed x .tobject p? pers := by
        unfold checkVal at hcv
        simp only [hpb, Bind.bind, Except.bind, Pure.pure, Except.pure] at hcv
        cases hcv; rfl
      subst hctx'_eq
      have hlive_y : vy.isLive = true := by
        unfold RcCtx.projBacking at hpb
        simp only [hgety] at hpb
        split at hpb
        · simp at hpb
        · simp_all
      unfold PRValWp at hpr
      have hpr_env := hpr
      have hobj_eq := shadowOk_getObj?_eq (i := i) hsh hgety hlive_y
      change match (ρP y).bind fun x => x.getObj? i with
        | some r => K r rem wr rcr
        | none => False at hpr_env
      rw [hobj_eq] at hpr_env
      obtain ⟨pv_y, w_y, hev_py, hev_hy, hvr_y, _⟩ :=
        hrc.2.2.2.1 vy (RcCtx.get?_mem hgety).1 hlive_y
      rw [(RcCtx.get?_mem hgety).2] at hev_py hev_hy
      rw [hev_py] at hpr_env
      cases pv_y with
      | ctor cidx fs hscal =>
        simp only [Option.bind_some, PVal.getObj?] at hpr_env
        cases hget_fs : fs[i]? with
        | none => simp [hget_fs] at hpr_env
        | some pv_res =>
          simp only [hget_fs] at hpr_env
          have hi_fs : i < fs.length := (List.getElem?_eq_some_iff.mp hget_fs).1
          unfold ValRep at hvr_y
          simp only [hns_y', Bool.false_eq_true, ↓reduceIte] at hvr_y
          rcases hvr_y with ⟨bv_y, rfl, hobj_y, _⟩
          unfold ObjRep at hobj_y
          rcases hobj_y with ⟨rfl, rfl, _, _⟩ | ⟨_, o_y, ho_y, ha_y, _, _, hle244, _, hfrep⟩
          · simp at hget_fs
          · have hfl_eq : o_y.fields.length = fs.length := (objFieldsRep_length hfrep).symm
            have hi_o : i < o_y.fields.length := by rw [hfl_eq]; exact hi_fs
            have hmem_res : fs[i] = pv_res := (List.getElem?_eq_some_iff.mp hget_fs).2
            have hobj_res : ObjRep pv_res o_y.fields[i] σ.objs :=
              hmem_res ▸ objFieldsRep_getElem hfrep hi_fs hi_o
            have hvr_res : ValRep .tobject pv_res (Word.i64 o_y.fields[i]) σ.objs := by
              simp only [ValRep, LcTy.isScalar, Bool.false_eq_true, ↓reduceIte]
              exact ⟨o_y.fields[i], rfl, hobj_res, (fun h => by cases h), (fun h => by cases h)⟩
            have hchild : o_y.fields[i] &&& 1#64 = 0#64 → o_y.fields[i] ∈ o_y.childFields := by
              intro _; simp [LcnfObj.childFields, hle244, List.getElem_mem]
            have hsteps := bind_borrowed_step_invs hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh
              hfr rfl hpb hgety (by simp [hns_y']) hev_hy ho_y ha_y hvr_res hchild
            rcases hsteps with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
            let ctx' := rf.ctx.bindBorrowed x .tobject p? pers
            let rf' : RcFrame :=
              ⟨ctx', rf.envP.set x pv_res, rf.envH.set x .tobject (Word.i64 o_y.fields[i]),
                rf.extH, rf.ghostH⟩
            have hjsc' : JpsScopeIn ((jpsOk.map fun e => { e with mutVars := x :: e.mutVars }).map
                JpEntry.info) ctx' := by
              simp; exact jpsScopeIn_put hrc.2.1 hjsc
            have hjok' := jpsOk_let_step (x := x) (rf' := rf') (ρP' := ρP.set x pv_res) hjok
              ⟨fun z hz => by
                dsimp only [rf', ctx', RcCtx.bindBorrowed]
                rw [get?_put_ne rf.ctx hrc.2.1 hz]
                exact ⟨rfl, fun h => h⟩,
                fun p hp _ => by
                  refine ⟨hp, ?_⟩
                  unfold binderFreshOwned at hfr
                  simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hfr
                  exact (hfr.1.2 p hp).2⟩
              (fun z hz => by simp [rf', PValEnv.set, HValEnv.set, hz]) rfl
            simp only [HVal.wp, getBV64_of_envH hev_hy]
            refine ⟨o_y, ho_y, ha_y, hle244, hi_o, ?_⟩
            exact hcont (rf' := rf') (ρP' := ρP.set x pv_res) (pv := pv_res)
              (rw := Word.i64 o_y.fields[i]) hpr_env rfl rfl rfl rfl
              h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 (shadowSmWf_filter_ne hsmwf) h12 hres
              hjsc' hjok' rfl
      | _ => simp [PVal.getObj?] at hpr_env

private theorem isShared_step {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {x y : Nat} {ty : LcTy}
    {env : RcModEnv} {Δr : PResEnv} {jpsOk : List JpEntry} {Jp : PResJEnv} {Jh : HJEnv}
    {jumps : List (Nat × RcCtx)} {rem wr rcr : Nat} {K : PResPost} {Xp : PResXPost}
    {Δh : HEnv} {Kh : HPost} {Xh : HXPost} {ctx' : RcCtx}
    (hpvwf : perceusValWf env rf.ctx x ty (.isShared y) = true)
    (hcv : checkVal env rf.ctx x ty (.isShared y) = .ok ctx')
    (hpr : PRValWp env Δr ρP ty (.isShared y) rem wr rcr K Xp)
    (hjok : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps)
    (hrc : RcInv rt rf σ) (hcl : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbp : SharedBoolPreds rf.ctx) (hex : ExclCtorHeap rf)
    (hsh : ShadowOk sm rf.ctx ρP rf.envP) (hsmwf : ShadowSmWf sm)
    (hres : ResStateInv σ rem wr rcr) (hjsc : JpsScopeIn (jpsOk.map JpEntry.info) rf.ctx)
    (hcont : ∀ {rf' : RcFrame} {σ' : HState} {sm' : List (Nat × Nat × List Bool)}
      {ρP' : PValEnv} {rem' wr' rcr' : Nat} {jpsOk' : List JpEntry} {pv : PVal} {rw : Word},
      K pv rem' wr' rcr' →
      rf'.ctx = ctx' → rf'.envH = rf.envH.set x ty rw → ρP' = ρP.set x pv →
      sm' = sm.filter (·.1 != x) →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → SharedBoolPreds rf'.ctx → ExclCtorHeap rf' →
      ShadowSmWf sm' → ShadowOk sm' rf'.ctx ρP' rf'.envP →
      ResStateInv σ' rem' wr' rcr' →
      JpsScopeIn (jpsOk'.map JpEntry.info) rf'.ctx →
      JpsOk rt rf0 σ0 Jp Jh jpsOk' rf' ρP' jumps →
      jpsOk' = jpsOk.map (fun e => { e with mutVars := x :: e.mutVars }) →
      Kh rw σ') :
    HVal.wp Δh rt rf.envH ty (.isShared y) Kh Xh σ := by
  unfold perceusValWf at hpvwf
  simp only [Bool.and_eq_true] at hpvwf
  rcases hpvwf with ⟨hfr, ⟨hty_u, hvy_m⟩⟩
  have hty_eq : ty = .uint8 := (lcTy_beq_iff ty .uint8).mp hty_u
  subst hty_eq
  cases hgety : rf.ctx.get? y with
  | none => simp [hgety] at hvy_m
  | some vy =>
    simp only [hgety, Bool.and_eq_true, decide_eq_true_eq] at hvy_m
    rcases hvy_m with ⟨⟨hns_y, _⟩, hoy⟩
    have hns_y' : vy.ty.isScalar = false := by simpa using hns_y
    have hctx'_eq : ctx' =
        { vars := (rf.ctx.bindOwned x .uint8).vars,
          sharedPreds := (x, y) :: (rf.ctx.bindOwned x .uint8).sharedPreds } ∧
        vy.isLive = true := by
      unfold checkVal at hcv
      exact checkLive_bind_ok hgety hcv
    rcases hctx'_eq with ⟨rfl, hlive_y⟩
    unfold PRValWp at hpr
    cases hrho : ρP y with
    | none => simp [hrho] at hpr
    | some pv_y =>
      simp only [hrho] at hpr
      rcases hpr with ⟨hnt, hK⟩
      obtain ⟨pvH, hev_py, hnt_H⟩ := shadowOk_isTaggedPVal_false hsh hgety hlive_y hrho hnt
      obtain ⟨pvH', w_y, hev_py', hev_hy, hvr_y, _⟩ :=
        hrc.2.2.2.1 vy (RcCtx.get?_mem hgety).1 hlive_y
      rw [(RcCtx.get?_mem hgety).2] at hev_py' hev_hy
      rw [hev_py] at hev_py'; cases hev_py'
      unfold ValRep at hvr_y
      simp only [hns_y', Bool.false_eq_true, ↓reduceIte] at hvr_y
      rcases hvr_y with ⟨bv_y, rfl, hobj_y, _⟩
      obtain ⟨o_y, ho_y, ha_y⟩ := objRep_not_tagged_mem hobj_y hnt_H
      have hsteps := bind_isShared_step_invs hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh hfr
        hgety hlive_y hoy hev_hy ho_y ha_y
      rcases hsteps with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
      let ctx1 := rf.ctx.bindOwned x .uint8
      let ctx' : RcCtx := { vars := ctx1.vars, sharedPreds := (x, y) :: ctx1.sharedPreds }
      let b := decide (o_y.rc ≠ 1#32)
      let rw := Word.i8 (if o_y.rc ≠ 1#32 then 1#8 else 0#8)
      let rf' : RcFrame :=
        ⟨ctx', rf.envP.set x (.bool b), rf.envH.set x .uint8 rw, rf.extH, rf.ghostH⟩
      have hjsc' : JpsScopeIn ((jpsOk.map fun e => { e with mutVars := x :: e.mutVars }).map
          JpEntry.info) ctx' := by
        simp only [List.map_map, Function.comp_def]
        have heq_j := jpsScopeIn_put hrc.2.1
          (v := ⟨x, .uint8, true, false, 0, false, none, false, false⟩) hjsc
        simpa [ctx', ctx1, RcCtx.bindOwned, LcTy.needsRc, JpsScopeIn, RcCtx.get?] using heq_j
      have hjok' := jpsOk_let_step (x := x) (rf' := rf') (ρP' := ρP.set x (.bool b)) hjok
        ⟨fun z hz => by
          change Option.map RcVar.ty (ctx1.get? z) = Option.map RcVar.ty (rf.ctx.get? z) ∧
            (Option.map RcVar.isLive (ctx1.get? z) = some true →
              Option.map RcVar.isLive (rf.ctx.get? z) = some true)
          dsimp only [ctx1, RcCtx.bindOwned]
          rw [get?_put_ne rf.ctx hrc.2.1 hz]
          exact ⟨rfl, fun h => h⟩,
        fun p hp hne => by
          rcases List.mem_cons.mp hp with hpeq | hp1
          · simp [hpeq] at hne
          · refine ⟨hp1, ?_⟩
            unfold binderFreshOwned at hfr
            simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hfr
            exact (hfr.1.2 p hp1).2⟩
        (fun z hz => by simp [rf', PValEnv.set, HValEnv.set, hz]) rfl
      simp only [HVal.wp, getBV64_of_envH hev_hy]
      refine ⟨o_y, ho_y, ha_y, ?_⟩
      exact hcont (rf' := rf') (ρP' := ρP.set x (.bool b)) (pv := .bool b) (rw := rw)
        (hK b) rfl rfl rfl rfl h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
        (shadowSmWf_filter_ne hsmwf) h12 hres hjsc' hjok' rfl

private theorem unbox_step {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {x y : Nat} {ty : LcTy}
    {env : RcModEnv} {Δr : PResEnv} {jpsOk : List JpEntry} {Jp : PResJEnv} {Jh : HJEnv}
    {jumps : List (Nat × RcCtx)} {rem wr rcr : Nat} {K : PResPost} {Xp : PResXPost}
    {Δh : HEnv} {Kh : HPost} {Xh : HXPost} {ctx' : RcCtx}
    (hpvwf : perceusValWf env rf.ctx x ty (.unbox y) = true)
    (hsv : valScalarWf sm ty (.unbox y) = true)
    (hcv : checkVal env rf.ctx x ty (.unbox y) = .ok ctx')
    (hpr : PRValWp env Δr ρP ty (.unbox y) rem wr rcr K Xp)
    (hjok : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps)
    (hrc : RcInv rt rf σ) (hcl : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbp : SharedBoolPreds rf.ctx) (hex : ExclCtorHeap rf)
    (hsh : ShadowOk sm rf.ctx ρP rf.envP) (hsmwf : ShadowSmWf sm)
    (hres : ResStateInv σ rem wr rcr) (hjsc : JpsScopeIn (jpsOk.map JpEntry.info) rf.ctx)
    (hcont : ∀ {rf' : RcFrame} {σ' : HState} {sm' : List (Nat × Nat × List Bool)}
      {ρP' : PValEnv} {rem' wr' rcr' : Nat} {jpsOk' : List JpEntry} {pv : PVal} {rw : Word},
      K pv rem' wr' rcr' →
      rf'.ctx = ctx' → rf'.envH = rf.envH.set x ty rw → ρP' = ρP.set x pv →
      sm' = sm.filter (·.1 != x) →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → SharedBoolPreds rf'.ctx → ExclCtorHeap rf' →
      ShadowSmWf sm' → ShadowOk sm' rf'.ctx ρP' rf'.envP →
      ResStateInv σ' rem' wr' rcr' →
      JpsScopeIn (jpsOk'.map JpEntry.info) rf'.ctx →
      JpsOk rt rf0 σ0 Jp Jh jpsOk' rf' ρP' jumps →
      jpsOk' = jpsOk.map (fun e => { e with mutVars := x :: e.mutVars }) →
      Kh rw σ') :
    HVal.wp Δh rt rf.envH ty (.unbox y) Kh Xh σ := by
  unfold perceusValWf at hpvwf
  simp only [Bool.and_eq_true] at hpvwf
  rcases hpvwf with ⟨hfr, ⟨hsc, hvy_m⟩⟩
  cases hgety : rf.ctx.get? y with
  | none => simp [hgety] at hvy_m
  | some vy =>
    simp only [hgety] at hvy_m
    have hns_y : vy.ty.isScalar = false := by simpa using hvy_m
    have hctx'_eq : ctx' = rf.ctx.bindOwned x ty ∧ vy.isLive = true := by
      unfold checkVal at hcv
      exact checkLive_bind_ok hgety hcv
    rcases hctx'_eq with ⟨rfl, hlive_y⟩
    unfold valScalarWf at hsv
    unfold PRValWp at hpr
    cases hrho : ρP y with
    | none => simp [hrho] at hpr
    | some pv_y =>
      cases hub : pv_y.unbox ty with
      | none => simp [hrho, hub] at hpr
      | some pv_res =>
        simp only [hrho, Option.bind_some, hub] at hpr
        rcases hpr with ⟨hsafe, hK⟩
        have hpeq := shadowOk_isVarInit hsh hgety hlive_y hsv
        obtain ⟨pv_y', w_y, hev_py, hev_hy, hvr_y, _⟩ :=
          hrc.2.2.2.1 vy (RcCtx.get?_mem hgety).1 hlive_y
        rw [(RcCtx.get?_mem hgety).2] at hev_py hev_hy
        rw [← hpeq, hrho] at hev_py; cases hev_py
        unfold ValRep at hvr_y
        simp only [hns_y, Bool.false_eq_true, ↓reduceIte] at hvr_y
        rcases hvr_y with ⟨bv_y, rfl, hobj_y, _⟩
        simp only [HVal.wp, getBV64_of_envH hev_hy]
        by_cases hbig : ty = .uint64 ∨ ty = .usize ∨ ty = .float
        · have hbig' : ∃ v : BitVec 64, pv_y = .bits 64 v := by
            rcases hbig with rfl | rfl | rfl <;> exact hsafe
          rcases hbig' with ⟨v, rfl⟩
          have hpv : pv_res = .bits 64 v := by
            rcases hbig with rfl | rfl | rfl <;>
              simpa [PVal.unbox, LcTy.width, BitVec.setWidth_eq] using hub.symm
          subst hpv
          unfold ObjRep at hobj_y
          rcases hobj_y with ⟨hw64, _⟩ | ⟨_, o_y, ho_y, ha_y, _, htag0, hf0, hsc_y⟩
          · omega
          · have hlen8 : 8 ≤ o_y.scalarData.length := by rw [hsc_y]; exact Nat.le_refl 8
            have hrd : readBitsLE 64 o_y.scalarData 0 = v := by
              rw [hsc_y]; exact readBitsLE_writeNatLE_64 v
            have hvr64 : ∀ (t0 : LcTy), t0.isScalar = true → t0.width = 64 →
                ValRep t0 (.bits 64 v) (Word.i64 (readBitsLE 64 o_y.scalarData 0)) σ.objs := by
              intro t0 hts htw
              cases t0 <;>
                first
                | (cases hts; done)
                | (cases htw; done)
                | (simp only [ValRep, LcTy.isScalar, ↓reduceIte, ScalarRep, LcTy.width];
                   exact Or.inl ⟨v, rfl, by rw [hrd, Word.i64]⟩)
            have hvr_res := hvr64 ty hsc (by rcases hbig with rfl | rfl | rfl <;> rfl)
            have hwrap := let_nonPtr_wrap hjok hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh
              hsmwf hres hjsc hfr hvr_res (fun h => absurd hsc (by simp [h])) hK hcont
            rcases hbig with rfl | rfl | rfl <;>
              exact ⟨o_y, ho_y, ha_y, hrc.1.1.2.1 o_y ho_y, htag0, hf0, hlen8, hwrap⟩
        · have hne64 : ty ≠ .uint64 ∧ ty ≠ .usize ∧ ty ≠ .float :=
            ⟨fun h => hbig (Or.inl h), fun h => hbig (Or.inr (Or.inl h)),
              fun h => hbig (Or.inr (Or.inr h))⟩
          have hsm : ty = .uint8 ∨ ty = .uint16 ∨ ty = .uint32 := by
            cases ty <;> simp only [LcTy.isScalar] at hsc
            all_goals first
              | (cases hsc; done)
              | exact absurd rfl hne64.1
              | exact absurd rfl hne64.2.1
              | exact absurd rfl hne64.2.2
              | exact Or.inl rfl
              | exact Or.inr (Or.inl rfl)
              | exact Or.inr (Or.inr rfl)
          have hw32 := ty_width_le_32_of_not_64 hsc hne64.1 hne64.2.1 hne64.2.2
          have hw64 : ty.width < 64 := by omega
          let resBV := BitVec.setWidth ty.width (bv_y >>> 1)
          have hvr_res : ValRep ty pv_res ⟨ty.toTTy, resBV⟩ σ.objs := by
            simp only [ValRep, hsc, ↓reduceIte, ScalarRep, LcTy.toTTy]
            left
            cases pv_y with
            | bits w v =>
              have hwv : w < 64 := by
                rcases hsm with rfl | rfl | rfl <;> exact hsafe
              unfold ObjRep at hobj_y
              rcases hobj_y with ⟨_, rfl⟩ | ⟨_, _⟩
              · have hpv : pv_res = .bits ty.width (BitVec.setWidth ty.width v) := by
                  simpa [PVal.unbox] using hub.symm
                have hres_eq : resBV = BitVec.setWidth ty.width v := by
                  dsimp [resBV]
                  rw [bv_setWidth_shift1_or1_ushift1 hw64]
                  ext i hi
                  have hi64 : i < 64 := Nat.lt_of_lt_of_le hi (Nat.le_of_lt hw64)
                  simp [hi64]
                exact ⟨BitVec.setWidth ty.width v, hpv, by simp [resBV, hres_eq]⟩
              · omega
            | nat n =>
              have hn : n < 2 ^ 63 := by
                rcases hsm with rfl | rfl | rfl <;> exact hsafe
              unfold ObjRep natRepR0 at hobj_y
              simp only [hn, ↓reduceIte] at hobj_y
              subst hobj_y
              have hpv : pv_res = .bits ty.width (BitVec.ofNat ty.width n) := by
                simpa [PVal.unbox] using hub.symm
              exact ⟨BitVec.ofNat ty.width n, hpv, by
                simp only [resBV, bv_setWidth_ofNat_2n1_ushift1 (Nat.le_of_lt hw64) hn]⟩
            | ctor c fs sc =>
              have hc : fs = [] ∧ sc = [] ∧ c < 2 ^ 63 := by
                cases fs with
                | cons _ _ => rcases hsm with rfl | rfl | rfl <;> exact False.elim hsafe
                | nil =>
                  cases sc with
                  | cons _ _ => rcases hsm with rfl | rfl | rfl <;> exact False.elim hsafe
                  | nil =>
                    refine ⟨rfl, rfl, ?_⟩
                    rcases hsm with rfl | rfl | rfl <;> exact hsafe
              rcases hc with ⟨rfl, rfl, hc⟩
              unfold ObjRep at hobj_y
              rcases hobj_y with ⟨_, _, _, rfl⟩ | ⟨hneg, _⟩
              · have hpv : pv_res = .bits ty.width (BitVec.ofNat ty.width c) := by
                  simpa [PVal.unbox] using hub.symm
                exact ⟨BitVec.ofNat ty.width c, hpv, by
                  simp only [resBV, bv_setWidth_ofNat_2n1_ushift1 (Nat.le_of_lt hw64) hc]⟩
              · exact absurd ⟨rfl, rfl⟩ hneg
            | erased =>
              unfold ObjRep at hobj_y
              subst hobj_y
              have hpv : pv_res = .bits ty.width 0#ty.width := by
                simpa [PVal.unbox] using hub.symm
              have hz : BitVec.setWidth ty.width (1#64 >>> 1) = 0#ty.width := by
                ext i; simp
              exact ⟨0#ty.width, hpv, by simp only [resBV, hz]⟩
            | str _ | arr _ | barr _ | int _ | clo _ _ _ =>
              simp [PVal.unbox] at hub
          have hwrap := let_nonPtr_wrap hjok hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh hsmwf
            hres hjsc hfr hvr_res (fun h => absurd hsc (by simp [h])) hK hcont
          rcases hsm with rfl | rfl | rfl <;> exact hwrap

private theorem scalarRep_extract_box {t : LcTy} (ht : t.isScalar = true)
    {pv_y : PVal} {w_y : Word} (hsr : ScalarRep t.width pv_y w_y) :
    ∃ bv : BitVec t.width, w_y = ⟨t.toTTy, bv⟩ ∧ PVal.box t pv_y = some (.bits t.width bv) := by
  rcases hsr with ⟨bv, rfl, rfl⟩ | ⟨c, rfl, _, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨bv, rfl, ?_⟩
    cases t <;> simp_all [PVal.box, LcTy.width, LcTy.isScalar] <;>
      exact congrArg (PVal.bits _) (BitVec.setWidth_eq _)
  · refine ⟨BitVec.ofNat t.width c, rfl, ?_⟩
    cases t <;> simp_all [PVal.box, LcTy.width, LcTy.isScalar]
  · refine ⟨0#t.width, rfl, ?_⟩
    cases t <;> simp_all [PVal.box, LcTy.width, LcTy.isScalar]

private theorem box_step {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {x : Nat} {t : LcTy} {y : Nat} {ty : LcTy}
    {env : RcModEnv} {Δr : PResEnv} {jpsOk : List JpEntry} {Jp : PResJEnv} {Jh : HJEnv}
    {jumps : List (Nat × RcCtx)} {rem wr rcr : Nat} {K : PResPost} {Xp : PResXPost}
    {Δh : HEnv} {Kh : HPost} {Xh : HXPost} {ctx' : RcCtx}
    (hpvwf : perceusValWf env rf.ctx x ty (.box t y) = true)
    (hsv : valScalarWf sm ty (.box t y) = true)
    (hcv : checkVal env rf.ctx x ty (.box t y) = .ok ctx')
    (hpr : PRValWp env Δr ρP ty (.box t y) rem wr rcr K Xp)
    (hjok : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps)
    (hrc : RcInv rt rf σ) (hcl : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx) (hsbp : SharedBoolPreds rf.ctx)
    (hex : ExclCtorHeap rf) (hsh : ShadowOk sm rf.ctx ρP rf.envP) (hsmwf : ShadowSmWf sm)
    (hres : ResStateInv σ rem wr rcr) (hjsc : JpsScopeIn (jpsOk.map JpEntry.info) rf.ctx)
    (hcont : ∀ {rf' : RcFrame} {σ' : HState} {sm' : List (Nat × Nat × List Bool)}
      {ρP' : PValEnv} {rem' wr' rcr' : Nat} {jpsOk' : List JpEntry} {pv : PVal} {rw : Word},
      K pv rem' wr' rcr' →
      rf'.ctx = ctx' → rf'.envH = rf.envH.set x ty rw → ρP' = ρP.set x pv →
      sm' = sm.filter (·.1 != x) →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → SharedBoolPreds rf'.ctx → ExclCtorHeap rf' →
      ShadowSmWf sm' → ShadowOk sm' rf'.ctx ρP' rf'.envP →
      ResStateInv σ' rem' wr' rcr' →
      JpsScopeIn (jpsOk'.map JpEntry.info) rf'.ctx →
      JpsOk rt rf0 σ0 Jp Jh jpsOk' rf' ρP' jumps →
      jpsOk' = jpsOk.map (fun e => { e with mutVars := x :: e.mutVars }) →
      Kh rw σ') :
    HVal.wp Δh rt rf.envH ty (.box t y) Kh Xh σ := by
  unfold perceusValWf at hpvwf
  simp only [Bool.and_eq_true] at hpvwf
  rcases hpvwf with ⟨hfr, ⟨htsc, hvy_m⟩⟩
  cases hgety : rf.ctx.get? y with
  | none => simp [hgety] at hvy_m
  | some vy =>
    simp only [hgety, Bool.and_eq_true, beq_iff_eq] at hvy_m
    rcases hvy_m with ⟨⟨⟨hysc, hyw⟩, htyns⟩, hty_chk⟩
    have hns_ty : ty.isScalar = false := by simpa using htyns
    have hctx'_eq : ctx' = rf.ctx.bindOwned x ty true ∧ vy.isLive = true := by
      unfold checkVal at hcv
      exact checkLive_bind_ok hgety hcv
    rcases hctx'_eq with ⟨rfl, hlive_y⟩
    unfold valScalarWf at hsv
    unfold PRValWp at hpr
    have hpeq := shadowOk_isVarInit hsh hgety hlive_y hsv
    obtain ⟨pv_y, w_y, hev_py, hev_hy, hvr_y, _⟩ :=
      hrc.2.2.2.1 vy (RcCtx.get?_mem hgety).1 hlive_y
    rw [(RcCtx.get?_mem hgety).2] at hev_py hev_hy
    rw [← hpeq] at hev_py
    unfold ValRep at hvr_y
    simp only [hysc, ↓reduceIte, hyw] at hvr_y
    obtain ⟨bv_y, rfl, hbox_eq⟩ := scalarRep_extract_box htsc hvr_y
    have hev_at : rf.envH.evalArgAt (.var y) t = some ⟨t.toTTy, bv_y⟩ := by
      simp [HValEnv.evalArgAt, hev_hy]
    simp only [hev_py, Option.bind_some, hbox_eq] at hpr
    simp only [HVal.wp, hev_at]
    by_cases hbig : (t == .uint64 || t == .usize || t == .float) = true
    · simp only [hbig, ↓reduceIte] at hpr hty_chk
      rcases hpr with ⟨h16, h1, hK⟩
      have hcan : canAllocBytesR0 σ.st 16 := Or.inr (Nat.le_trans h16 hres.1)
      have hty_tag : ty ≠ .tagged := (ty_needsRc_ne_tagged hty_chk).1
      have hsub : ∀ (bv64 : BitVec 64) {p : BitVec 64} {st' : RtC0State},
          K (.bits 64 bv64) (rem - 16) (wr - 1) rcr →
          p ≠ 0#64 → p.toNat % 8 = 0 → (∀ o ∈ σ.objs, o.addr ≠ p) →
          st'.PreservesMeta σ.st → σ.st.rem - 16 ≤ st'.rem →
          let newObj : LcnfObj := {
            addr := p, rc := 1#32, csSz := 16, other := 0, tag := 0,
            scalarData := writeNatLE bv64.toNat 8 }
          let σ' : HState :=
            ⟨st', newObj :: σ.objs, σ.scr, σ.scrLimbs⟩
          Kh (Word.i64 p) σ' := by
        intro bv64 p st' hK64 hpne hpmod hpfresh hpmeta hprem newObj σ'
        have hsteps := box_fresh_alloc_step_invs hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh
          hres h16 h1 hfr hty_chk hty_tag hpne hpmod hpfresh hpmeta hprem (bv := bv64)
        rcases hsteps with ⟨h1', h2', h3', h4', h5', h6', h7', h8', h9', h10', h11', h12', h13'⟩
        let ctx' := rf.ctx.bindOwned x ty true
        let rf' : RcFrame :=
          ⟨ctx', rf.envP.set x (.bits 64 bv64), rf.envH.set x ty (Word.i64 p), rf.extH, rf.ghostH⟩
        have hjsc' : JpsScopeIn ((jpsOk.map fun e => { e with mutVars := x :: e.mutVars }).map
            JpEntry.info) ctx' := by
          simp; exact jpsScopeIn_put hrc.2.1 hjsc
        have hjok' := jpsOk_let_step (rf' := rf') (ρP' := ρP.set x (.bits 64 bv64)) hjok
          (ctx_step_props_bindOwned hrc.2.1 hfr ty true)
          (fun z hz => by simp [rf', PValEnv.set, HValEnv.set, hz]) rfl
        exact hcont (rf' := rf') (σ' := σ') (ρP' := ρP.set x (.bits 64 bv64))
          (pv := .bits 64 bv64) (rw := Word.i64 p) hK64 rfl rfl rfl rfl
          h1' h2' h3' h4' h5' h6' h7' h8' h9' h10' h11' (shadowSmWf_filter_ne hsmwf) h12' h13'
          hjsc' hjok' rfl
      simp only [Bool.or_eq_true, lcTy_beq_iff] at hbig
      rcases hbig with (rfl | rfl) | rfl
      · exact ⟨hcan, fun p st' hpne hpmod hpfresh hpmeta _ hprem =>
          hsub bv_y hK hpne hpmod hpfresh hpmeta hprem⟩
      · exact ⟨hcan, fun p st' hpne hpmod hpfresh hpmeta _ hprem =>
          hsub bv_y hK hpne hpmod hpfresh hpmeta hprem⟩
      · exact ⟨hcan, fun p st' hpne hpmod hpfresh hpmeta _ hprem =>
          hsub bv_y hK hpne hpmod hpfresh hpmeta hprem⟩
    · have hne64 : t ≠ .uint64 ∧ t ≠ .usize ∧ t ≠ .float := by
        simp only [Bool.or_eq_true, lcTy_beq_iff, not_or] at hbig
        exact ⟨hbig.1.1, hbig.1.2, hbig.2⟩
      simp only [hbig, Bool.false_eq_true, ↓reduceIte] at hpr hty_chk ⊢
      have hne_obj : ty ≠ .object := fun h => by subst h; cases hty_chk
      have ht_small : t = .uint8 ∨ t = .uint16 ∨ t = .uint32 := by
        cases t <;>
          first
          | (cases htsc; done)
          | exact absurd rfl hne64.1
          | exact absurd rfl hne64.2.1
          | exact absurd rfl hne64.2.2
          | exact Or.inl rfl
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr rfl)
      have ht_lt64 : t.width < 64 := by
        rcases ht_small with rfl | rfl | rfl <;> decide
      let x64 := BitVec.setWidth 64 bv_y
      let bv_res := x64 <<< 1 ||| 1#64
      have hvr_res : ValRep ty (.bits t.width bv_y) (Word.i64 bv_res) σ.objs := by
        simp only [ValRep, hns_ty, Bool.false_eq_true, ↓reduceIte]
        refine ⟨bv_res, rfl, ?_, fun h => absurd h hne_obj, fun _ => bv_shift1_or1_and_one x64⟩
        exact Or.inl ⟨ht_lt64, rfl⟩
      have hrc' := rcInv_bind_nonPtr hrc hcl hfr ty true hvr_res
        (fun _ => ⟨bv_res, rfl, bv_shift1_or1_and_one x64⟩)
      have hnd' : ((rf.ctx.bindOwned x ty true).vars.map RcVar.id).Nodup :=
        RcCtx.put_nodup hrc.2.1 _
      have hpo' := parentsOwned_bindOwned hrc.2.1 hpo hfr ty true false false
      have hno' := noRcCorrect_bindOwned hrc.2.1 hno x ty true false false
      let ctx' := rf.ctx.bindOwned x ty true
      let rf' : RcFrame :=
        ⟨ctx', rf.envP.set x (.bits t.width bv_y), rf.envH.set x ty (Word.i64 bv_res),
          rf.extH, rf.ghostH⟩
      have hfr_preds : ∀ p ∈ rf.ctx.sharedPreds, p.1 ≠ x := fun p hp => by
        unfold binderFreshOwned at hfr
        simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hfr
        exact (hfr.1.2 p hp).1
      have hsbv' : SharedBoolVars ctx' := by
        dsimp only [ctx', RcCtx.bindOwned]
        exact sharedBoolVars_put_fresh hrc.2.1 hsbv (by simpa using hfr_preds)
      have hsbp' : SharedBoolPreds ctx' := by
        dsimp only [ctx', RcCtx.bindOwned]
        exact sharedBoolPreds_put_fresh hrc.2.1 hsbp (by simpa using hfr_preds)
      have hpcb' : ParentChildBacked rf' σ.objs := by
        intro u hu hl hnr hpr' hbr p hp bv0 hb0 hev0
        have hgetu := get?_of_mem_nodup hnd' hu
        have hne : u.id ≠ x := fun he => by
          subst he
          dsimp only [RcCtx.bindOwned] at hgetu
          rw [get?_put_self rf.ctx hrc.2.1 _] at hgetu
          have hbr_f := congrArg RcVar.borrowed (Option.some.inj hgetu)
          simp [hbr] at hbr_f
        dsimp only [RcCtx.bindOwned] at hgetu
        rw [get?_put_ne rf.ctx hrc.2.1 hne] at hgetu
        have hnep : p ≠ x := fun he => by
          subst he; unfold binderFreshOwned at hfr
          simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hfr
          exact absurd hp (hfr.1.1 u (RcCtx.get?_mem hgetu).1)
        simp only [rf', HValEnv.set, hne, ↓reduceIte] at hb0
        simpa [rf', HValEnv.set, hnep] using
          hpcb u (RcCtx.get?_mem hgetu).1 hl hnr hpr' hbr p hp bv0 hb0 hev0
      have hsth' : SharedTargetsHeap rf' := by
        intro p hp vx hg hnr
        have hnep : p.2 ≠ x := by
          unfold binderFreshOwned at hfr
          simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hfr
          exact (hfr.1.2 p hp).2
        dsimp only [rf', ctx', RcCtx.bindOwned] at hg
        rw [get?_put_ne rf.ctx hrc.2.1 hnep] at hg
        obtain ⟨bv0, hh0, hev0⟩ := hsth p hp vx hg hnr
        exact ⟨bv0, by simp only [rf', HValEnv.set, hnep, ↓reduceIte]; exact hh0, hev0⟩
      have hex' : ExclCtorHeap rf' := by
        intro u hu hl huex hnr hpr' c fs sc hp_e
        have hgetu := get?_of_mem_nodup hnd' hu
        by_cases heq : u.id = x
        · simp only [rf', PValEnv.set, heq, ↓reduceIte] at hp_e; cases hp_e
        · dsimp only [RcCtx.bindOwned] at hgetu
          rw [get?_put_ne rf.ctx hrc.2.1 heq] at hgetu
          simp only [rf', PValEnv.set, heq, ↓reduceIte] at hp_e
          obtain ⟨bv0, hh0, hev0⟩ := hex u (RcCtx.get?_mem hgetu).1 hl huex hnr hpr' c fs sc hp_e
          exact ⟨bv0, by simp only [rf', HValEnv.set, heq, ↓reduceIte]; exact hh0, hev0⟩
      have hsh' : ShadowOk (sm.filter (·.1 != x)) ctx' (ρP.set x (.bits t.width bv_y))
          rf'.envP := by
        intro u hu hl
        have hgetu := get?_of_mem_nodup hnd' hu
        by_cases heq : u.id = x
        · have his : isVarScalarInit (sm.filter (·.1 != x)) x = true := by simp [isVarScalarInit]
          rw [heq, his]; simp [rf', PValEnv.set]
        · dsimp only [RcCtx.bindOwned] at hgetu
          rw [get?_put_ne rf.ctx hrc.2.1 heq] at hgetu
          have h0 := hsh u (RcCtx.get?_mem hgetu).1 hl
          have his : isVarScalarInit (sm.filter (·.1 != x)) u.id = isVarScalarInit sm u.id := by
            simp only [isVarScalarInit, List.all_filter]
            congr 1; ext e
            by_cases hfx : e.1 = x
            · simp [hfx, show x ≠ u.id from Ne.symm heq]
            · simp [hfx]
          rw [his]
          simp only [rf', PValEnv.set, heq, ↓reduceIte]
          by_cases hisu : isVarScalarInit sm u.id = true
          · simp only [hisu, ↓reduceIte] at h0 ⊢; exact h0
          · simp only [hisu, Bool.false_eq_true, ↓reduceIte] at h0 ⊢
            rw [find?_filter_ne sm heq]; exact h0
      have hep' : EntryPres rf0 σ0 rf' σ := by
        refine ⟨hep.1, fun a ha hiso => ?_, hep.2.2.1, hep.2.2.2⟩
        obtain ⟨hiso1, hobj1⟩ := hep.2.1 a ha hiso
        refine ⟨⟨fun u hu hl hns w hw => ?_, hiso1.2.1, hiso1.2.2⟩, hobj1⟩
        by_cases heq : u.id = x
        · simp only [rf', HValEnv.set, heq, ↓reduceIte] at hw; cases hw
          intro heq_bv
          have h0 : bv_res &&& 1#64 = a &&& 1#64 := congrArg (· &&& 1#64) (Option.some.inj heq_bv)
          have ha_ev : a &&& 1#64 = 0#64 := by
            rcases hiso.2.2 with ⟨o, _, hwf, hao, _⟩
            rw [← hao]
            exact bv_and_one_eq_zero_of_wf hwf
          rw [ha_ev] at h0
          exact bv_shift1_or1_and_one x64 h0
        · have hgetu := get?_of_mem_nodup hnd' hu
          dsimp only [RcCtx.bindOwned] at hgetu
          rw [get?_put_ne rf.ctx hrc.2.1 heq] at hgetu
          simp only [rf', HValEnv.set, heq, ↓reduceIte] at hw
          exact hiso1.1 u (RcCtx.get?_mem hgetu).1 hl hns w hw
      have hjsc' : JpsScopeIn ((jpsOk.map fun e => { e with mutVars := x :: e.mutVars }).map
          JpEntry.info) ctx' := by
        simp; exact jpsScopeIn_put hrc.2.1 hjsc
      have hjok' := jpsOk_let_step (rf' := rf') (ρP' := ρP.set x (.bits t.width bv_y)) hjok
        (ctx_step_props_bindOwned hrc.2.1 hfr ty true)
        (fun z hz => by simp [rf', PValEnv.set, HValEnv.set, hz]) rfl
      have hsub_sm : Kh (Word.i64 bv_res) σ := hcont (rf' := rf')
        (ρP' := ρP.set x (.bits t.width bv_y)) (pv := .bits t.width bv_y) (rw := Word.i64 bv_res)
        hpr rfl rfl rfl rfl hrc'.1 hrc'.2 hpo' hno' hpcb' hsth' hhih hep' hsbv' hsbp' hex'
        (shadowSmWf_filter_ne hsmwf) hsh' hres hjsc' hjok' rfl
      rcases ht_small with rfl | rfl | rfl <;>
        exact hsub_sm

private theorem ctor_step {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {x : Nat} {ty : LcTy}
    {ci : LcCtor} {as : List LcArg}
    {env : RcModEnv} {Δr : PResEnv} {jpsOk : List JpEntry} {Jp : PResJEnv} {Jh : HJEnv}
    {jumps : List (Nat × RcCtx)} {rem wr rcr : Nat} {K : PResPost} {Xp : PResXPost}
    {Δh : HEnv} {Kh : HPost} {Xh : HXPost} {ctx' : RcCtx}
    (hpvwf : perceusValWf env rf.ctx x ty (.ctor ci as) = true)
    (hsv : valScalarWf sm ty (.ctor ci as) = true)
    (hcv : checkVal env rf.ctx x ty (.ctor ci as) = .ok ctx')
    (hpr : PRValWp env Δr ρP ty (.ctor ci as) rem wr rcr K Xp)
    (hjok : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps)
    (hrc : RcInv rt rf σ) (hcl : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbp : SharedBoolPreds rf.ctx) (hex : ExclCtorHeap rf)
    (hsh : ShadowOk sm rf.ctx ρP rf.envP) (hsmwf : ShadowSmWf sm)
    (hres : ResStateInv σ rem wr rcr) (hjsc : JpsScopeIn (jpsOk.map JpEntry.info) rf.ctx)
    (hcont : ∀ {rf' : RcFrame} {σ' : HState} {sm' : List (Nat × Nat × List Bool)}
      {ρP' : PValEnv} {rem' wr' rcr' : Nat} {jpsOk' : List JpEntry} {pv : PVal} {rw : Word},
      K pv rem' wr' rcr' →
      rf'.ctx = ctx' → rf'.envH = rf.envH.set x ty rw → ρP' = ρP.set x pv →
      sm' = ctorBindMask x ci sm →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → SharedBoolPreds rf'.ctx → ExclCtorHeap rf' →
      ShadowSmWf sm' → ShadowOk sm' rf'.ctx ρP' rf'.envP →
      ResStateInv σ' rem' wr' rcr' →
      JpsScopeIn (jpsOk'.map JpEntry.info) rf'.ctx →
      JpsOk rt rf0 σ0 Jp Jh jpsOk' rf' ρP' jumps →
      jpsOk' = jpsOk.map (fun e => { e with mutVars := x :: e.mutVars }) →
      Kh rw σ') :
    HVal.wp Δh rt rf.envH ty (.ctor ci as) Kh Xh σ := by
  unfold PRValWp at hpr
  cases hevp : ρP.evalArgs as with
  | none => simp [hevp] at hpr
  | some pvs =>
    simp only [hevp] at hpr
    by_cases hsc_ci : ci.isScalar = true
    · unfold perceusValWf at hpvwf
      simp only [Bool.and_eq_true, hsc_ci, ↓reduceIte] at hpvwf
      rcases hpvwf with ⟨hfr, hty_m⟩
      have hctx'_eq : ctx' = rf.ctx.bindOwned x ty := by
        unfold checkVal at hcv
        simp only [hsc_ci, ↓reduceIte] at hcv
        cases hcv; rfl
      subst hctx'_eq
      have hmask : ctorBindMask x ci sm = sm.filter (·.1 != x) := by
        simp [ctorBindMask, hsc_ci]
      simp only [PVal.mkCtor, hsc_ci, ↓reduceIte] at hpr
      simp only [HVal.wp, hsc_ci, ↓reduceIte]
      by_cases hty_sc : ty.isScalar = true
      · simp only [hty_sc, ↓reduceIte] at hpr hty_m ⊢
        have hvr : ValRep ty (.bits ty.width (.ofNat ty.width ci.cidx))
            ⟨ty.toTTy, .ofNat ty.width ci.cidx⟩ σ.objs := by
          simp only [ValRep, hty_sc, ↓reduceIte, ScalarRep]
          exact Or.inl ⟨.ofNat ty.width ci.cidx, rfl, rfl⟩
        exact let_nonPtr_wrap hjok hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh hsmwf hres
          hjsc hfr hvr (fun h => absurd hty_sc (by simp [h])) hpr
          (fun hk1 hctx1 henv1 hrho1 hsm1 => hcont hk1 hctx1 henv1 hrho1 (hsm1.trans hmask.symm))
      · have hty_f : ty.isScalar = false := Bool.eq_false_iff.mpr hty_sc
        have hw64 : ty.width = 64 := ty_width_of_not_scalar hty_f
        simp only [hty_f, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
          at hpr hty_m ⊢
        rcases hty_m with ⟨hlt, hne_obj⟩
        have hvr : ValRep ty (.ctor ci.cidx [] [])
            (Word.i64 (BitVec.ofNat 64 (2 * ci.cidx + 1))) σ.objs := by
          simp only [ValRep, hty_f, Bool.false_eq_true, ↓reduceIte]
          refine ⟨BitVec.ofNat 64 (2 * ci.cidx + 1), rfl, ?_,
            (fun h => by rw [h] at hne_obj; cases hne_obj),
            (fun _ => bv_odd_of_mul2_add1 ci.cidx)⟩
          exact Or.inl ⟨rfl, rfl, hlt, rfl⟩
        have hw_eq : (⟨ty.toTTy, BitVec.ofNat ty.width (2 * ci.cidx + 1)⟩ : Word) =
            Word.i64 (BitVec.ofNat 64 (2 * ci.cidx + 1)) := by
          simp only [LcTy.toTTy, Word.i64]; rw [hw64]
        rw [hw_eq]
        exact let_nonPtr_wrap hjok hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh hsmwf hres
          hjsc hfr hvr (fun _ => ⟨_, rfl, bv_odd_of_mul2_add1 ci.cidx⟩) hpr
          (fun hk1 hctx1 henv1 hrho1 hsm1 => hcont hk1 hctx1 henv1 hrho1 (hsm1.trans hmask.symm))
    · have hns_ci : ci.isScalar = false := Bool.eq_false_iff.mpr hsc_ci
      unfold perceusValWf at hpvwf
      simp only [Bool.and_eq_true, hsc_ci, Bool.false_eq_true, ↓reduceIte,
        decide_eq_true_eq] at hpvwf
      rcases hpvwf with ⟨hfr, ⟨⟨⟨⟨⟨⟨htynrc, hcidx⟩, hsize⟩, hmin⟩, hmax⟩, hans⟩, hnost⟩⟩
      cases happ : rf.ctx.applyArgs as (List.replicate as.length false) with
      | error e =>
        unfold checkVal at hcv
        simp only [hsc_ci, Bool.false_eq_true, ↓reduceIte, happ, Bind.bind, Except.bind] at hcv
        cases hcv
      | ok ctx1 =>
        have hctx'_eq : ctx' = ctx1.bindOwned x ty true := by
          unfold checkVal at hcv
          simp only [hsc_ci, Bool.false_eq_true, ↓reduceIte, happ, Bind.bind, Except.bind,
            Pure.pure, Except.pure] at hcv
          cases hcv; rfl
        subst hctx'_eq
        cases hsz_eq : (pvs.length == ci.size) with
        | false => simp [PVal.mkCtor, hsc_ci, hsz_eq] at hpr
        | true =>
          simp only [PVal.mkCtor, hsc_ci, hsz_eq, Bool.false_eq_true, ↓reduceIte] at hpr
          rcases hpr with ⟨hbytes, h1wr, hK⟩
          have hpvs_len : pvs.length = ci.size := by simpa using hsz_eq
          have hlive := applyArgs_var_live hrc.2.1 hcl happ
          have hl_eval : ∀ a ∈ as, match a with
              | .erased => True
              | .var z => ∃ v, rf.ctx.get? z = some v ∧ v.isLive = true := by
            intro a ha
            rcases hlive a ha with rfl | ⟨z, v, rfl, hgz, hlv⟩
            · trivial
            · exact ⟨v, hgz, hlv⟩
          have hevp_rf : rf.envP.evalArgs as = some pvs := by
            rw [← shadowOk_evalArgs_init hsh (List.all_eq_true.mp hsv) hl_eval]; exact hevp
          obtain ⟨bvs, hev_obj, hfrep⟩ := evalObjArgs_sim hrc.2.2.2.1 hans hl_eval hevp_rf
          have hbvs_len : bvs.length = ci.size := (objFieldsRep_length hfrep).symm.trans hpvs_len
          have hcan : canAllocBytesR0 σ.st ci.byteSize := Or.inr (Nat.le_trans hbytes hres.1)
          have hty_tag : ty ≠ .tagged := (ty_needsRc_ne_tagged htynrc).1
          simp only [HVal.wp, hsc_ci, Bool.false_eq_true, ↓reduceIte, hev_obj]
          refine ⟨hbvs_len, hcidx, hsize, hmin, hmax, hcan, fun p st' scal hpne hpmod hpfresh
              hpmeta _ hprem hscal => ?_⟩
          have hsteps := ctor_fresh_alloc_step_invs hrc hcl hpo hno hpcb hsth hhih hep hsbp hex
            hsh hres hbytes h1wr hfr htynrc hty_tag (by simp [hns_ci]) hcidx hsize hmin hmax hans
            hnost happ hpvs_len hev_obj hfrep hpne hpmod hpfresh hpmeta hprem hscal
          rcases hsteps with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
          let ctx' := ctx1.bindOwned x ty true
          let pv_res := PVal.ctor ci.cidx pvs (List.replicate (8 * ci.usize + ci.ssize) 0)
          let newObj : LcnfObj := {
            addr := p, rc := 1#32, csSz := ci.byteSize, other := ci.size, tag := ci.cidx,
            fields := bvs, scalarData := scal }
          let σ' : HState :=
            ⟨st', newObj :: σ.objs, σ.scr, σ.scrLimbs⟩
          let rf' : RcFrame :=
            ⟨ctx', rf.envP.set x (PVal.ctor ci.cidx pvs scal), rf.envH.set x ty (Word.i64 p),
              rf.extH, rf.ghostH⟩
          have hjsc' : JpsScopeIn ((jpsOk.map fun e => { e with mutVars := x :: e.mutVars }).map
              JpEntry.info) ctx' := by
            simp; exact jpsScopeIn_put (applyArgs_nodup hrc.2.1 happ)
              (jpsScopeIn_applyArgs hrc.2.1 happ hjsc)
          have hjok' := jpsOk_let_step (rf' := rf') (ρP' := ρP.set x pv_res) hjok
            (ctx_step_props_applyArgs_bindOwned hrc.2.1 happ hfr ty true)
            (fun z hz => by simp [rf', PValEnv.set, HValEnv.set, hz]) rfl
          exact hcont (rf' := rf') (σ' := σ') (ρP' := ρP.set x pv_res) (pv := pv_res)
            (rw := Word.i64 p) hK rfl rfl rfl rfl h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
            (shadowSmWf_ctorBindMask hsmwf x ci) h12 h13 hjsc' hjok' rfl

/-- Compute the updated scalar-initialization shadow mask after binding `x` to `v`. -/
def letNextMask (x : Nat) (v : LcVal)
    (sm : List (Nat × Nat × List Bool)) : List (Nat × Nat × List Bool) :=
  match v with
  | .ctor ci _ => ctorBindMask x ci sm
  | _ => sm.filter (·.1 != x)

theorem letVal_step {m : LcModule} {Δr : PResEnv} {Δh : HEnv}
    {rt : BitVec 64} {rf0 rf : RcFrame} {σ0 σ : HState} {sm : List (Nat × Nat × List Bool)}
    {ρP : PValEnv} {rem wr rcr x : Nat} {ty : LcTy} {v : LcVal}
    {jpsOk : List JpEntry} {Jp : PResJEnv} {Jh : HJEnv} {jumps : List (Nat × RcCtx)}
    {ctx' : RcCtx} {K : PResPost} {Xp : PResXPost} {Kh : HPost} {Xh : HXPost}
    (hmwf : ∀ d ∈ m.decls, !isPrimName d.name = true ∧ (d.params.map LcParam.id).Nodup)
    (hcompat : PRCallCompat m Δr Δh)
    (hpvwf : perceusValWf (mkRcModEnv m) rf.ctx x ty v = true)
    (hsv : valScalarWf sm ty v = true)
    (hcv : checkVal (mkRcModEnv m) rf.ctx x ty v = .ok ctx')
    (hpr : PRValWp (mkRcModEnv m) Δr ρP ty v rem wr rcr K Xp)
    (hjok : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps)
    (hrc : RcInv rt rf σ) (hcl : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx) (hsbp : SharedBoolPreds rf.ctx)
    (hex : ExclCtorHeap rf) (hsh : ShadowOk sm rf.ctx ρP rf.envP) (hsmwf : ShadowSmWf sm)
    (hres : ResStateInv σ rem wr rcr) (hjsc : JpsScopeIn (jpsOk.map JpEntry.info) rf.ctx)
    (hcont : ∀ {rf' : RcFrame} {σ' : HState} {sm' : List (Nat × Nat × List Bool)}
      {ρP' : PValEnv} {rem' wr' rcr' : Nat} {jpsOk' : List JpEntry} {pv : PVal} {rw : Word},
      K pv rem' wr' rcr' →
      rf'.ctx = ctx' → rf'.envH = rf.envH.set x ty rw → ρP' = ρP.set x pv →
      sm' = letNextMask x v sm →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → SharedBoolPreds rf'.ctx → ExclCtorHeap rf' →
      ShadowSmWf sm' → ShadowOk sm' rf'.ctx ρP' rf'.envP →
      ResStateInv σ' rem' wr' rcr' →
      JpsScopeIn (jpsOk'.map JpEntry.info) rf'.ctx →
      JpsOk rt rf0 σ0 Jp Jh jpsOk' rf' ρP' jumps →
      jpsOk' = jpsOk.map (fun e => { e with mutVars := x :: e.mutVars }) →
      Kh rw σ')
    (hx : ∀ {c rem' wr' rcr' : Nat} {σ' : HState},
      Xp c rem' wr' rcr' → Xh (BitVec.ofNat 64 c) σ') :
    HVal.wp Δh rt rf.envH ty v Kh Xh σ := by
  cases v with
  | lit l =>
    cases l with
    | nat n =>
      unfold perceusValWf at hpvwf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hpvwf
      rcases hpvwf with ⟨hfr, ⟨⟨hn, hns⟩, hnoobj⟩⟩
      have hns_f : ty.isScalar = false := by simpa using hns
      have hctx'_eq : ctx' = rf.ctx.bindOwned x ty := by
        unfold checkVal at hcv
        by_cases hnrc : (!ty.needsRc) = true
        · simp only [hnrc, ↓reduceIte] at hcv; cases hcv; rfl
        · have hnrc_f : (!ty.needsRc) = false := Bool.eq_false_iff.mpr hnrc
          simp only [hnrc_f, Bool.false_eq_true, ↓reduceIte, hn] at hcv; cases hcv; rfl
      subst hctx'_eq
      unfold PRValWp at hpr
      have hvr : ValRep ty (PVal.nat n) (Word.i64 (BitVec.ofNat 64 (2 * n + 1))) σ.objs := by
        simp only [ValRep, hns_f, Bool.false_eq_true, ↓reduceIte]
        refine ⟨BitVec.ofNat 64 (2 * n + 1), rfl, ?_,
          (fun h => by rw [h] at hnoobj; cases hnoobj),
          (fun _ => bv_odd_of_mul2_add1 n)⟩
        simp [ObjRep, natRepR0, hn]
      simp only [HVal.wp, hn, ↓reduceIte]
      exact let_nonPtr_wrap hjok hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh hsmwf hres
        hjsc hfr hvr (fun _ => ⟨_, rfl, bv_odd_of_mul2_add1 n⟩) hpr.2 hcont
    | scalar n =>
      unfold perceusValWf at hpvwf
      simp only [Bool.and_eq_true] at hpvwf
      rcases hpvwf with ⟨hfr, hsc⟩
      have hctx'_eq : ctx' = rf.ctx.bindOwned x ty := by
        unfold checkVal at hcv; cases hcv; rfl
      subst hctx'_eq
      unfold PRValWp at hpr
      have hvr : ValRep ty (.bits ty.width (.ofNat ty.width n))
          ⟨ty.toTTy, .ofNat ty.width n⟩ σ.objs := by
        simp only [ValRep, hsc, ↓reduceIte, ScalarRep]
        exact Or.inl ⟨.ofNat ty.width n, rfl, rfl⟩
      simp only [HVal.wp]
      exact let_nonPtr_wrap hjok hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh hsmwf hres
        hjsc hfr hvr (fun h => absurd hsc (by simp [h])) hpr hcont
    | str _ => simp [perceusValWf] at hpvwf
  | erased =>
    unfold perceusValWf at hpvwf
    simp only [Bool.and_eq_true] at hpvwf
    rcases hpvwf with ⟨hfr, ⟨hns, hnoobj⟩⟩
    have hns_f : ty.isScalar = false := by simpa using hns
    have hw64 : ty.width = 64 := ty_width_of_not_scalar hns_f
    have hctx'_eq : ctx' = rf.ctx.bindOwned x ty := by
      unfold checkVal at hcv; cases hcv; rfl
    subst hctx'_eq
    unfold PRValWp at hpr
    have hvr : ValRep ty .erased (Word.i64 1#64) σ.objs := by
      simp only [ValRep, hns_f, Bool.false_eq_true, ↓reduceIte]
      exact ⟨1#64, rfl, by simp [ObjRep], (fun h => by rw [h] at hnoobj; cases hnoobj),
        (fun _ => by decide)⟩
    have hw_eq : (⟨ty.toTTy, BitVec.ofNat ty.width (if ty.isScalar = true then 0 else 1)⟩ : Word) =
        Word.i64 1#64 := by
      simp only [LcTy.toTTy, Word.i64, hns_f, Bool.false_eq_true, ↓reduceIte]
      rw [hw64]
    simp only [HVal.wp, hw_eq]
    exact let_nonPtr_wrap hjok hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh hsmwf hres
      hjsc hfr hvr (fun _ => ⟨1#64, rfl, by decide⟩) hpr hcont
  | oproj i y =>
    exact oproj_step hpvwf hcv hpr hjok hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh hsmwf
      hres hjsc hcont
  | uproj i y =>
    exact uproj_step hpvwf hsv hcv hpr hjok hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh hsmwf
      hres hjsc hcont
  | sproj n off y =>
    exact sproj_step hpvwf hsv hcv hpr hjok hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh hsmwf
      hres hjsc hcont
  | isShared y =>
    exact isShared_step hpvwf hcv hpr hjok hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh hsmwf
      hres hjsc hcont
  | unbox y =>
    exact unbox_step hpvwf hsv hcv hpr hjok hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh hsmwf
      hres hjsc hcont
  | box t y =>
    exact box_step hpvwf hsv hcv hpr hjok hrc hcl hpo hno hpcb hsth hhih hep hsbv hsbp hex hsh hsmwf
      hres hjsc hcont
  | ctor ci as =>
    exact ctor_step hpvwf hsv hcv hpr hjok hrc hcl hpo hno hpcb hsth hhih hep hsbp hex hsh hsmwf
      hres hjsc hcont
  | fap f as =>
    have hinit : ∀ a ∈ as, argScalarInit sm a = true := by
      unfold valScalarWf at hsv
      exact List.all_eq_true.mp hsv
    cases hfind : (mkRcModEnv m).decls.find? (·.1 == f) with
    | some entry =>
      rcases entry with ⟨nm, borrows, pts, rty, isConst⟩
      exact fap_decl_step hmwf hcompat hfind hpvwf hinit hcv hpr hrc hcl hpo hno hpcb hsth hhih
        hep hsbv hsbp hex hsh hres
        (fun hK hctx1 hext1 henv1 hrho1 hother1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 => by
          have hfr : binderFreshOwned rf.ctx x = true := by
            unfold perceusValWf at hpvwf; exact (Bool.and_eq_true _ _ |>.mp hpvwf).1
          have hhapp : ∃ ctx1, rf.ctx.applyArgs as borrows = .ok ctx1 ∧
              ctx' = ctx1.bindOwned x ty := by
            unfold checkVal at hcv
            have hncst : (isConst && as.isEmpty) = false := by
              unfold perceusValWf at hpvwf; simp [hfind] at hpvwf
              cases h : isConst && as.isEmpty <;> simp_all
            simp only [hfind, hncst, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind,
              Pure.pure, Except.pure] at hcv
            cases happ : rf.ctx.applyArgs as borrows with
            | error e => rw [happ] at hcv; cases hcv
            | ok ctx1 => rw [happ] at hcv; cases hcv; exact ⟨ctx1, rfl, rfl⟩
          rcases hhapp with ⟨ctx1, happ, hce⟩
          have hjsc' : JpsScopeIn ((jpsOk.map fun e => { e with mutVars := x :: e.mutVars }).map
              JpEntry.info) ctx' := by
            simp; rw [hce]
            exact jpsScopeIn_put (applyArgs_nodup hrc.2.1 happ)
              (jpsScopeIn_applyArgs hrc.2.1 happ hjsc)
          have hjok' := jpsOk_let_step hjok (by
            rw [hctx1, hce]
            exact ctx_step_props_applyArgs_bindOwned hrc.2.1 happ hfr ty) hother1 hext1
          exact hcont hK hctx1 henv1 hrho1 rfl h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
            (shadowSmWf_filter_ne hsmwf) h12 h13 (by rw [hctx1]; exact hjsc') hjok' rfl) hx
    | none =>
      exact prim_step hfind hpvwf hinit hcv hpr hjok hrc hcl hpo hno hpcb hsth hhih hep hsbv hsbp
        hex hsh hsmwf hres hjsc hcont hx
  | pap _ _ => simp [perceusValWf] at hpvwf
  | ap _ _ => simp [perceusValWf] at hpvwf
  | reset _ _ => simp [perceusValWf] at hpvwf
  | reuse _ _ _ _ => simp [perceusValWf] at hpvwf

theorem let_step {m : LcModule} {retTy : LcTy} {Δr : PResEnv} {Δh : HEnv}
    {rt : BitVec 64} {Jh : HJEnv} {Jp : PResJEnv} {Qp : PResPost} {Xp : PResXPost}
    {Qh : HPost} {Xh : HXPost} {jpsOk : List JpEntry} {rf0 rf : RcFrame} {σ0 σ : HState}
    {sm : List (Nat × Nat × List Bool)} {ρP : PValEnv} {rem wr rcr x : Nat}
    {ty : LcTy} {v : LcVal} {k : LcCode} {jumps : List (Nat × RcCtx)}
    (hmwf : ∀ d ∈ m.decls, !isPrimName d.name = true ∧ (d.params.map LcParam.id).Nodup)
    (hcompat : PRCallCompat m Δr Δh)
    (hcc : checkCode (mkRcModEnv m) retTy (jpsOk.map JpEntry.info) rf.ctx (.let_ x ty v k) =
      .ok jumps)
    (hpw : perceusCodeWf (mkRcModEnv m) retTy (jpsOk.map JpEntry.info) rf.ctx sm
      (.let_ x ty v k) = true)
    (hpr : PRWp m (mkRcModEnv m) retTy Δr (jpsOk.map JpEntry.info) rf.ctx Jp ρP rem wr rcr
      Qp Xp (.let_ x ty v k))
    (hrc : RcInv rt rf σ) (hcl : CleanVars rf.ctx) (hpo : ParentsOwned rf.ctx)
    (hno : NoRcCorrect rf.ctx) (hpcb : ParentChildBacked rf σ.objs)
    (hsth : SharedTargetsHeap rf) (hhih : HandlesInHeap (rf.extH ++ rf.ghostH) σ.objs)
    (hep : EntryPres rf0 σ0 rf σ) (hsbv : SharedBoolVars rf.ctx) (hsbp : SharedBoolPreds rf.ctx)
    (hex : ExclCtorHeap rf) (hsmwf : ShadowSmWf sm) (hsh : ShadowOk sm rf.ctx ρP rf.envP)
    (hres : ResStateInv σ rem wr rcr) (hjsc : JpsScopeIn (jpsOk.map JpEntry.info) rf.ctx)
    (hjok : JpsOk rt rf0 σ0 Jp Jh jpsOk rf ρP jumps)
    (hjmut : ∀ e ∈ jpsOk, jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars
      (.let_ x ty v k) = true)
    (hpb : ∀ e ∈ jpsOk, ∀ pvs, e.PBody pvs)
    (hx : ∀ {c rem' wr' rcr' : Nat} {σ' : HState},
      Xp c rem' wr' rcr' → Xh (BitVec.ofNat 64 c) σ')
    (hk : ∀ {jpsOk' : List JpEntry} {rf' : RcFrame} {σ' : HState}
      {sm' : List (Nat × Nat × List Bool)} {ρP' : PValEnv} {rem' wr' rcr' : Nat},
      checkCode (mkRcModEnv m) retTy (jpsOk'.map JpEntry.info) rf'.ctx k = .ok jumps →
      perceusCodeWf (mkRcModEnv m) retTy (jpsOk'.map JpEntry.info) rf'.ctx sm' k = true →
      PRWp m (mkRcModEnv m) retTy Δr (jpsOk'.map JpEntry.info) rf'.ctx Jp ρP' rem' wr' rcr'
        Qp Xp k →
      RcInv rt rf' σ' → CleanVars rf'.ctx → ParentsOwned rf'.ctx → NoRcCorrect rf'.ctx →
      ParentChildBacked rf' σ'.objs → SharedTargetsHeap rf' →
      HandlesInHeap (rf'.extH ++ rf'.ghostH) σ'.objs → EntryPres rf0 σ0 rf' σ' →
      SharedBoolVars rf'.ctx → SharedBoolPreds rf'.ctx → ExclCtorHeap rf' →
      ShadowSmWf sm' → ShadowOk sm' rf'.ctx ρP' rf'.envP →
      ResStateInv σ' rem' wr' rcr' → JpsScopeIn (jpsOk'.map JpEntry.info) rf'.ctx →
      JpsOk rt rf0 σ0 Jp Jh jpsOk' rf' ρP' jumps →
      (∀ e ∈ jpsOk', jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars k = true) →
      (∀ e ∈ jpsOk', ∀ pvs, e.PBody pvs) →
      HWp Δh rt retTy Jh rf'.envH Qh Xh k σ') :
    HWp Δh rt retTy Jh rf.envH Qh Xh (.let_ x ty v k) σ := by
  have hcc_eq : checkCode (mkRcModEnv m) retTy (jpsOk.map JpEntry.info) rf.ctx (.let_ x ty v k) =
      (checkVal (mkRcModEnv m) rf.ctx x ty v).bind
        (fun ctx' => checkCode (mkRcModEnv m) retTy (jpsOk.map JpEntry.info) ctx' k) := rfl
  rw [hcc_eq] at hcc
  cases hcv : checkVal (mkRcModEnv m) rf.ctx x ty v with
  | error e =>
    simp only [hcv, Except.bind] at hcc
    cases hcc
  | ok ctx' =>
    simp only [hcv, Except.bind] at hcc
    have hpw_eq : perceusCodeWf (mkRcModEnv m) retTy (jpsOk.map JpEntry.info) rf.ctx sm
        (.let_ x ty v k) =
        (perceusValWf (mkRcModEnv m) rf.ctx x ty v && valScalarWf sm ty v &&
          match checkVal (mkRcModEnv m) rf.ctx x ty v with
          | .ok ctx1 => perceusCodeWf (mkRcModEnv m) retTy (jpsOk.map JpEntry.info) ctx1
              (letNextMask x v sm) k
          | .error _ => false) := by
      cases v <;> rfl
    rw [hpw_eq, hcv, Bool.and_eq_true, Bool.and_eq_true] at hpw
    rcases hpw with ⟨⟨hpvwf, hsv⟩, hpw_k⟩
    have hpr_eq : PRWp m (mkRcModEnv m) retTy Δr (jpsOk.map JpEntry.info) rf.ctx Jp ρP rem wr rcr
        Qp Xp (.let_ x ty v k) =
        match checkVal (mkRcModEnv m) rf.ctx x ty v with
        | .ok ctx1 => PRValWp (mkRcModEnv m) Δr ρP ty v rem wr rcr
            (fun r rem' wr' rcr' =>
              PRWp m (mkRcModEnv m) retTy Δr (jpsOk.map JpEntry.info) ctx1 Jp (ρP.set x r)
                rem' wr' rcr' Qp Xp k) Xp
        | .error _ => False := rfl
    rw [hpr_eq, hcv] at hpr
    change HVal.wp Δh rt rf.envH ty v
      (fun r σ' => HWp Δh rt retTy Jh (rf.envH.set x ty r) Qh Xh k σ') Xh σ
    refine letVal_step hmwf hcompat hpvwf hsv hcv hpr hjok hrc hcl hpo hno hpcb hsth hhih hep
      hsbv hsbp hex hsh hsmwf hres hjsc (fun hK hctx1 henv1 hrho1 hsm1 h1 h2 h3 h4 h5 h6 h7 h8 h9
        h10 h11 h12 h13 h14 hjsc' hjok' hjmap => ?_) hx
    rw [← henv1]
    rw [← hsm1] at hpw_k
    have hjmut' : ∀ e ∈ jpsOk.map (fun e => { e with mutVars := x :: e.mutVars }),
        jpLiveNoMut e.info.id (baseCtxLiveIds e.baseCtx) e.mutVars k = true := by
      intro e he
      rcases List.mem_map.mp he with ⟨e0, he0, rfl⟩
      simpa [jpLiveNoMut, jpLiveNoMut._f] using hjmut e0 he0
    have hjmp : (jpsOk.map fun e => { e with mutVars := x :: e.mutVars }).map JpEntry.info =
        jpsOk.map JpEntry.info := by simp
    have hpb' : ∀ e ∈ jpsOk.map (fun e => { e with mutVars := x :: e.mutVars }),
        ∀ pvs, e.PBody pvs := by
      intro e he pvs
      rcases List.mem_map.mp he with ⟨e0, he0, rfl⟩
      exact hpb e0 he0 pvs
    rw [← hjmp] at hcc hpw_k hK
    subst hctx1; subst hrho1; subst hjmap
    exact hk hcc hpw_k hK h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hjsc' hjok' hjmut' hpb'
