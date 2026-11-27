module

public import LeanQbe.T.LeanLCNF.Sem.LowerSound3
public import LeanQbe.T.LeanLCNF.Sem.LowerSound1b

/-!
# Case Dispatch & Monotonicity Helpers for `lowerCode` (`Lower1.lean`)

Provides `LMMono` preservation for Phase-1 `lowerCode`/`lowerVal`/`lowerCases`,
invariant transfer across fresh-id allocation (`HSimInv.transfer`, `VarRel.bindAll_of_pushJp`),
and case-dispatch soundness (`lowerCases_sound`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.LeanLCNF

/-! ## §1. Monotonicity & Structural Utilities -/

/-- Loads the tag byte at `addr + 7#64` for a heap object in `HState`. -/
theorem mem_load_lcnfObj_tag {rt addr : BitVec 64} {σ : HState}
    {mem_f : Mem 64 → Prop} {mem : Mem 64} {o : LcnfObj}
    (ho : o ∈ σ.objs) (hwf : o.Wf) (haddr : o.addr = addr)
    (hm : (HState.mem rt σ ⋆ mem_f) mem) :
    loadVal mem i8 (addr + 7#64) = some (BitVec.ofNat 8 o.tag) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ho
  rw [← haddr]
  dsimp only [HState.mem] at hm
  rw [lcnfHeap_focus σ.objs hi, Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_assoc,
    Std.ExtHashMap.sep_comm_l] at hm
  exact lcnfObjMem_load_i8_tag hwf hm

theorem fresh_mono : LMMono fresh := by
  intro n a n' h
  simp only [fresh, modifyGet, StateT.run, MonadStateOf.modifyGet, StateT.modifyGet,
    Except.pure, Pure.pure, Except.ok.injEq, Prod.mk.injEq] at h
  omega

theorem freshVar_mono (t : Ty) : LMMono (freshVar t) :=
  bind_mono fresh_mono (fun _ => pure_mono _)

theorem var_mono (c : LCtx) (x : Nat) : LMMono (c.var x) := by
  intro n p n' h
  dsimp only [LCtx.var] at h
  cases hlu : List.lookup x c.vars with
  | none =>
    simp [hlu, lfail, StateT.run, throw, throwThe, MonadExceptOf.throw,
      StateT.lift, Functor.map, Except.map] at h
  | some r =>
    simp [hlu, pure, Pure.pure, StateT.run, StateT.pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ Nat.le_refl n

theorem argAt_mono (c : LCtx) (a : LcArg) (t : LcTy) : LMMono (argAt c a t) := by
  cases a with
  | erased => exact pure_mono _
  | var x =>
    dsimp only [argAt]
    refine bind_mono (var_mono c x) (fun ⟨_, _⟩ => ?_)
    split
    · exact pure_mono _
    · exact lfail_mono

theorem argOwn_mono (c : LCtx) (a : LcArg) : LMMono (argOwn c a) := by
  cases a with
  | erased => exact pure_mono _
  | var x => exact bind_mono (var_mono c x) (fun _ => pure_mono _)

theorem mapM_mono {α β : Type} {f : α → LM β} :
    ∀ (xs : List α), (∀ x ∈ xs, LMMono (f x)) → LMMono (xs.mapM f)
  | [], _ => by
    intro n ys n' h
    simp [List.mapM, List.mapM.loop, StateT.run, Pure.pure, StateT.pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ Nat.le_refl n
  | x :: xs, hf => by
    have hfx : LMMono (f x) := hf x (by simp)
    have hfxs : LMMono (xs.mapM f) := mapM_mono xs (fun y hy => hf y (by simp [hy]))
    rw [List.mapM_cons]
    exact bind_mono hfx (fun _ => bind_mono hfxs (fun _ => pure_mono _))

theorem spillExtras_mono (rt : LArg) :
    ∀ (extras : List (LArg × Ty)) (off : Nat) (k : LM LExpr),
      LMMono k → LMMono (spillExtras rt off extras k)
  | [], _, _, hk => hk
  | (_, _) :: rest, off, k, hk =>
    storeAt_mono (spillExtras_mono rt rest (off + 1) k hk)

theorem callFn_mono (rt : LArg) (sym : Sym) (args : List (LArg × Ty)) (ret : Ty)
    {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) :
    LMMono (callFn rt sym args ret k) := by
  dsimp only [callFn]
  split
  · exact bind_mono lfail_mono (fun _ => spillExtras_mono rt _ 0 _ (call1_mono hk))
  · exact spillExtras_mono rt _ 0 _ (call1_mono hk)

theorem m_decl_inFirstOrder {m : LcModule} (hfrag : m.inFirstOrderFragment = true)
    {d : LcDecl} (hd : d ∈ m.decls) : d.inFirstOrder m.decls = true := by
  simp only [LcModule.inFirstOrderFragment, Bool.and_eq_true] at hfrag
  exact List.all_eq_true.mp hfrag.2 d hd

theorem lowerFap_mono_of_fo {m : LcModule} {env : LEnv}
    (hfrag : m.inFirstOrderFragment = true) (henv : LEnvOk m env)
    (c : LCtx) (f : String) (as : List LcArg) (ty : LcTy)
    {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) :
    LMMono (lowerFap env c f as ty k) := by
  dsimp only [lowerFap]
  cases hlu : List.lookup f env.decls with
  | none =>
    exact bind_mono (mapM_mono as (fun a _ => argOwn_mono c a)) (fun _ => externPrim_mono hk)
  | some d =>
    obtain ⟨hd, _⟩ := (henv f d).mp hlu
    have hdFo := m_decl_inFirstOrder hfrag hd
    simp only [LcDecl.inFirstOrder, Bool.and_eq_true] at hdFo
    have hnoConst : (d.params.isEmpty && !d.retTy.isScalar) = false := by
      cases hc : d.params.isEmpty && !d.retTy.isScalar with
      | false => rfl
      | true => simp [hc] at hdFo
    simp only [hnoConst, Bool.false_eq_true, ↓reduceIte]
    have hbodyMono : LMMono (do
        let args ← List.mapM (fun x : LcArg × LcParam => do
          let la ← argAt c x.1 x.2.ty
          pure (la, x.2.ty.toTTy)) (as.zip d.params)
        callFn c.rt (mangleLc f) args d.retTy.toTTy fun r =>
          convW d.retTy.width ty.width r k) := by
      refine bind_mono (mapM_mono _ (fun p _ => bind_mono (argAt_mono c p.1 p.2.ty)
        (fun _ => pure_mono _))) (fun _ => callFn_mono _ _ _ _ (fun _ => convW_mono hk))
    split
    · exact bind_mono lfail_mono (fun _ => hbodyMono)
    · exact hbodyMono

theorem lowerVal_mono_of_fo {m : LcModule} {env : LEnv}
    (hfrag : m.inFirstOrderFragment = true) (henv : LEnvOk m env)
    (c : LCtx) (ty : LcTy) (v : LcVal)
    (hval : LcVal.inFirstOrder m.decls ty v = true)
    {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) :
    LMMono (lowerVal env c ty v k) := by
  cases v with
  | lit l =>
    cases l with
    | nat natN =>
      simp only [LcVal.inFirstOrder, Bool.and_eq_true, decide_eq_true_eq] at hval
      dsimp only [lowerVal]
      simp only [hval.1, ↓reduceIte]
      exact hk _
    | scalar _ => exact hk _
    | str _ => simp [LcVal.inFirstOrder] at hval
  | erased => exact hk _
  | ap _ _ => simp [LcVal.inFirstOrder] at hval
  | pap _ _ => simp [LcVal.inFirstOrder] at hval
  | reset _ _ => simp [LcVal.inFirstOrder] at hval
  | reuse _ _ _ _ => simp [LcVal.inFirstOrder] at hval
  | isShared _ => simp [LcVal.inFirstOrder] at hval
  | ctor ci as =>
    dsimp only [lowerVal]
    by_cases hsc : ci.isScalar = true
    · simp [hsc, hk]
    · simp only [hsc, Bool.false_eq_true, ↓reduceIte]
      exact bind_mono (mapM_mono as (fun a _ => argAt_mono c a LcTy.tobject))
        (fun _ => allocObj_mono (fun p => storeFields_mono 8 _ (k p) (hk p)))
  | oproj _ x => exact bind_mono (var_mono c x) (fun _ => loadAt_mono hk)
  | uproj _ x => exact bind_mono (var_mono c x) (fun _ => loadAt_mono hk)
  | sproj _ _ x => exact bind_mono (var_mono c x) (fun _ => loadAt_mono hk)
  | fap f as => exact lowerFap_mono_of_fo hfrag henv c f as ty hk
  | box t x =>
    dsimp only [lowerVal]
    refine bind_mono (var_mono c x) (fun ⟨xa, _⟩ => ?_)
    cases t <;> first
      | exact boxU64_mono hk
      | exact convW_mono (fun _ => boxSmall_mono hk)
      | exact hk xa
  | unbox x =>
    dsimp only [lowerVal]
    refine bind_mono (var_mono c x) (fun ⟨_, _⟩ => ?_)
    cases ty <;> first
      | exact loadAt_mono hk
      | exact lshr64_mono (fun _ => convW_mono hk)

theorem dispatchAlts_mono (tag : LArg) (w : Nat) :
    ∀ (alts : List (LcPat × LM LExpr)), (∀ p ∈ alts, LMMono p.2) → LMMono (dispatchAlts tag w alts)
  | [], _ => by rw [dispatchAlts.eq_1]; exact pure_mono _
  | [(fst, b)], halts => by rw [dispatchAlts.eq_2]; exact halts (fst, b) (by simp)
  | (.dflt, b) :: d :: tl, halts => by
    rw [dispatchAlts.eq_3 tag w b (d :: tl) (by simp)]
    exact halts (.dflt, b) (by simp)
  | (.ctor ci nm, b) :: d :: tl, halts => by
    rw [dispatchAlts.eq_4 tag w ci nm b (d :: tl) (by simp)]
    refine cmpOp_mono (fun _ => ?_)
    refine bind_mono (halts (.ctor ci nm, b) (by simp)) (fun _ => ?_)
    refine bind_mono (dispatchAlts_mono tag w (d :: tl) (fun q hq => halts q (by simp [hq])))
      (fun _ => pure_mono _)

theorem lowerCases_mono (c : LCtx) (x : Nat) (alts : List (LcPat × LM LExpr))
    (halts : ∀ p ∈ alts, LMMono p.2) :
    LMMono (lowerCases c x alts) := by
  dsimp only [lowerCases]
  refine bind_mono (var_mono c x) (fun ⟨xa, xt⟩ => ?_)
  have hmem : ∀ (f1 f2 : LcPat × LM LExpr → Bool) p,
      p ∈ alts.filter f1 ++ alts.filter f2 → LMMono p.2 := by
    intro f1 f2 p hp
    simp only [List.mem_append, List.mem_filter] at hp
    rcases hp with ⟨hp, _⟩ | ⟨hp, _⟩ <;> exact halts p hp
  dsimp only
  split
  · exact pure_mono _
  · next fst b heq => exact hmem _ _ (fst, b) (by rw [heq]; exact List.mem_cons_self)
  · split
    · exact dispatchAlts_mono xa xt.width _ (hmem _ _)
    · split
      · exact loadAt_mono (fun t => dispatchAlts_mono t 8 _ (hmem _ _))
      · split
        · exact lshr64_mono (fun t => dispatchAlts_mono t 64 _ (hmem _ _))
        · refine isScalarObj_mono (fun _ => withJoin1_mono
            (fun t => dispatchAlts_mono t 64 _ (hmem _ _)) (fun _ => ?_))
          refine bind_mono (loadAt_mono (fun _ => convW_mono (fun _ => pure_mono _)))
            (fun _ => bind_mono (lshr64_mono (fun _ => pure_mono _)) (fun _ => pure_mono _))

theorem sizeOf_snd_lt_of_mem_cases {x : Nat} :
    ∀ {alts : List (LcPat × LcCode)} {p : LcPat × LcCode},
      p ∈ alts → sizeOf p.2 < sizeOf (LcCode.cases x alts) := by
  intro alts p hp
  have h1 : sizeOf p.2 < sizeOf p := by
    cases p; simp only [Prod.mk.sizeOf_spec]; omega
  have h2 : sizeOf p < sizeOf alts := List.sizeOf_lt_of_mem hp
  have h3 : sizeOf alts < sizeOf (LcCode.cases x alts) := by
    simp only [LcCode.cases.sizeOf_spec]; omega
  omega

theorem lowerAlts_eq_map (env : LEnv) (c : LCtx) :
    ∀ (alts : List (LcPat × LcCode)),
      lowerAlts env c alts = alts.map (fun p => (p.1, lowerCode env c p.2))
  | [] => by rw [lowerAlts.eq_1, List.map_nil]
  | (_, _) :: rest => by
    rw [lowerAlts.eq_2, List.map_cons, lowerAlts_eq_map env c rest]

theorem inFirstOrder_of_mem_alts {decls : List LcDecl}
    {jps : List (Nat × List LcTy)} :
    ∀ {alts : List (LcPat × LcCode)},
      LcAlts.inFirstOrder decls jps alts = true →
      ∀ p ∈ alts, (∀ ci nm, p.1 = .ctor ci nm → ci < 256) ∧
        LcCode.inFirstOrder decls jps p.2 = true
  | [], _, _, hp => by cases hp
  | (.ctor ci nm, b) :: rest, hfo, p, hp => by
    rw [LcAlts.inFirstOrder.eq_2] at hfo
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfo
    rw [List.mem_cons] at hp
    rcases hp with hpEq | hrest
    · rw [hpEq]
      exact ⟨fun _ _ heq => (LcPat.ctor.inj heq).1 ▸ hfo.1.1, hfo.1.2⟩
    · exact inFirstOrder_of_mem_alts hfo.2 p hrest
  | (.dflt, b) :: rest, hfo, p, hp => by
    rw [LcAlts.inFirstOrder.eq_3] at hfo
    simp only [Bool.and_eq_true] at hfo
    rw [List.mem_cons] at hp
    rcases hp with hpEq | hrest
    · rw [hpEq]
      exact ⟨(fun _ _ heq => by cases heq), hfo.1.2⟩
    · exact inFirstOrder_of_mem_alts hfo.2 p hrest

theorem foldl_bind_jps : ∀ (l : List (LcParam × LArg)) (c : LCtx),
    (l.foldl (fun cc x => cc.bind x.1.id x.2 x.1.ty) c).jps = c.jps
  | [], _ => rfl
  | pa :: rest, c => by
    simp only [List.foldl_cons]
    exact (foldl_bind_jps rest (c.bind pa.1.id pa.2 pa.1.ty)).trans rfl

theorem bindAll_jps (ps : List LcParam) (as : List LArg) (c : LCtx) :
    (c.bindAll ps as).jps = c.jps :=
  foldl_bind_jps (ps.zip as) c

theorem lowerCode_mono_of_fo {m : LcModule} {env : LEnv}
    (hfrag : m.inFirstOrderFragment = true) (henv : LEnvOk m env) :
    ∀ (code : LcCode) (c : LCtx),
      code.inFirstOrder m.decls (c.jps.map fun p => (p.1, p.2.2)) = true →
      LMMono (lowerCode env c code)
  | .let_ x ty v k, c, hc => by
    rw [lowerCode.eq_1]
    rw [LcCode.inFirstOrder.eq_1, Bool.and_eq_true] at hc
    cases hst : selfTailJump? c (.let_ x ty v k) with
    | some jump =>
      dsimp only [selfTailJump?] at hst
      cases hl : c.loop? with
      | none => simp [hl] at hst
      | some lbl =>
        simp only [hl] at hst
        cases hv : v with
        | fap f as =>
          subst hv
          simp only at hst
          by_cases hself : isSelfTail c.fn c.params.length (.let_ x ty (.fap f as) k) = true
          · simp only [hself, ↓reduceIte] at hst
            injection hst with hj
            subst hj
            exact bind_mono (mapM_mono _ (fun p _ => argAt_mono c p.1 p.2)) (fun _ => pure_mono _)
          · simp [hself] at hst
        | _ => simp [hv] at hst
    | none =>
      exact lowerVal_mono_of_fo hfrag henv c ty v hc.1
        (fun r => lowerCode_mono_of_fo hfrag henv k (c.bind x r ty) hc.2)
  | .jp j ps body k, c, hc => by
    rw [lowerCode.eq_2]
    rw [LcCode.inFirstOrder.eq_2, Bool.and_eq_true] at hc
    refine bind_mono fresh_mono (fun lbl =>
      bind_mono (mapM_mono ps (fun p _ => freshVar_mono p.ty.toTTy)) (fun pvs => ?_))
    let c' : LCtx := { c with jps := (j, lbl, ps.map (·.ty)) :: c.jps }
    have hcBody : body.inFirstOrder m.decls
        (((c'.bindAll ps (pvs.map vArg)).jps.map fun p => (p.1, p.2.2))) = true := by
      rw [bindAll_jps]; exact hc.1
    have hbodyMono := lowerCode_mono_of_fo hfrag henv body (c'.bindAll ps (pvs.map vArg)) hcBody
    have hkMono := lowerCode_mono_of_fo hfrag henv k c' hc.2
    exact bind_mono hbodyMono (fun _ => bind_mono hkMono (fun _ => pure_mono _))
  | .jmp j as, c, _ => by
    rw [lowerCode.eq_3]
    cases List.lookup j c.jps with
    | none => exact lfail_mono
    | some p =>
      dsimp only
      have hmap : LMMono (List.mapM (fun x : LcArg × LcTy => argAt c x.1 x.2) (as.zip p.2)) :=
        mapM_mono _ (fun q _ => argAt_mono c q.1 q.2)
      split
      · exact bind_mono lfail_mono (fun _ => bind_mono hmap (fun _ => pure_mono _))
      · exact bind_mono hmap (fun _ => pure_mono _)
  | .cases x alts, c, hc => by
    rw [lowerCode.eq_4]
    rw [LcCode.inFirstOrder.eq_4] at hc
    refine lowerCases_mono c x (lowerAlts env c alts) (fun q hq => ?_)
    rw [lowerAlts_eq_map, List.mem_map] at hq
    obtain ⟨p, hpMem, rfl⟩ := hq
    have hpFo := (inFirstOrder_of_mem_alts hc p hpMem).2
    have hlt : sizeOf p.2 < sizeOf (LcCode.cases x alts) := sizeOf_snd_lt_of_mem_cases hpMem
    exact lowerCode_mono_of_fo hfrag henv p.2 c hpFo
  | .ret a, c, _ => by
    rw [lowerCode.eq_5]
    exact bind_mono (argAt_mono c a c.retTy) (fun _ => pure_mono _)
  | .unreach, _, _ => by
    rw [lowerCode.eq_6]
    exact pure_mono _
  | .inc x n chk k, c, hc => by
    rw [lowerCode.eq_11]
    rw [LcCode.inFirstOrder.eq_7] at hc
    exact bind_mono (var_mono c x) (fun ⟨_, _⟩ =>
      emitInc_mono (lowerCode_mono_of_fo hfrag henv k c hc))
  | .dec x n chk k, c, hc => by
    rw [lowerCode.eq_12]
    rw [LcCode.inFirstOrder.eq_8] at hc
    exact bind_mono (var_mono c x) (fun ⟨_, _⟩ =>
      emitDec_mono (lowerCode_mono_of_fo hfrag henv k c hc) n)
  | .oset _ _ _ _, _, hc => by simp [LcCode.inFirstOrder.eq_9] at hc
  | .uset _ _ _ _, _, hc => by simp [LcCode.inFirstOrder.eq_10] at hc
  | .sset _ _ _ _ _ _, _, hc => by simp [LcCode.inFirstOrder.eq_11] at hc
  | .setTag _ _ _, _, hc => by simp [LcCode.inFirstOrder] at hc
  | .del _ _, _, hc => by simp [LcCode.inFirstOrder] at hc
termination_by code _ _ => sizeOf code
decreasing_by
  all_goals first
    | (simp only [LcCode.let_.sizeOf_spec]; omega)
    | (simp only [LcCode.jp.sizeOf_spec]; omega)
    | (simp only [LcCode.inc.sizeOf_spec]; omega)
    | (simp only [LcCode.dec.sizeOf_spec]; omega)
    | exact hlt

theorem ctxVar_run_eq {c : LCtx} {x n n' : Nat} {p : LArg × LcTy}
    (h : (c.var x).run n = .ok (p, n')) :
    n' = n ∧ List.lookup x c.vars = some p := by
  dsimp only [LCtx.var] at h
  cases hlu : List.lookup x c.vars with
  | none =>
    simp [hlu, lfail, StateT.run, throw, throwThe, MonadExceptOf.throw,
      StateT.lift, Functor.map, Except.map] at h
  | some q =>
    simp [hlu, pure, Pure.pure, StateT.run, StateT.pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨h.2.symm, h.1 ▸ rfl⟩

/-! ## §2. Simulation Invariant Transfer & Join Helpers -/

/-- Transfers `HSimInv` across fresh variable/label allocations that preserve ids below `n`. -/
theorem HSimInv.transfer {Δ : HEnv} {rt : BitVec 64} {R : Mem 64 → Prop} {c : LCtx}
    {n m : Nat} {QH : HPost} {XH : HXPost} {QT : Post [c.retTy.toTTy]} {XT : XPost}
    {JH : HJEnv} {ρH : HValEnv} {ρL ρL' : Frontend.C0.VEnv} {JL JL' : Frontend.C0.JEnv}
    (hsim : HSimInv Δ rt R c n QH XH QT XT JH ρH ρL JL)
    (hn : n ≤ m)
    (hρ : VEnvAgreeBelow n ρL' ρL)
    (hJ : JEnvAgreeBelow n JL' JL) :
    HSimInv Δ rt R c m QH XH QT XT JH ρH ρL' JL' := by
  refine HSimInv.mk (ctxIdsBelow_mono hn hsim.idsOk) ?_ ?_ ?_ ?_ hsim.postRel hsim.xpostRel
  · exact (hρ.eval hsim.idsOk.1).trans hsim.rtOk
  · intro x ty w hx
    obtain ⟨a, h, hlu, hev⟩ := hsim.varRel x ty w hx
    exact ⟨a, h, hlu, (hρ.eval (ctxIdsBelow_lookup_var hsim.idsOk hlu)).trans hev⟩
  · intro j lbl ts hlu
    obtain ⟨k, hget, hk⟩ := hsim.jpRel j lbl ts hlu
    exact ⟨k, (hJ lbl (ts.map (·.toTTy)) (ctxIdsBelow_lookup_jp hsim.idsOk hlu)).trans hget, hk⟩
  · intro lbl heq
    obtain ⟨k, hget, hk⟩ := hsim.loopRel lbl heq
    exact ⟨k, (hJ lbl (c.params.map (·.toTTy)) (hsim.idsOk.2.2.2 lbl heq)).trans hget, hk⟩

theorem VEnv.bind_cast_tys (ρ : Frontend.C0.VEnv) (bs : List Frontend.C0.LVar)
    {ts₁ ts₂ : List Ty} (h : ts₁ = ts₂) (xs : Tup Val ts₁) :
    ρ.bind bs ts₂ (h ▸ xs) = ρ.bind bs ts₁ xs := by
  cases h; rfl

theorem evalArgs_getElem_of_wordsOfTup {ρ : Frontend.C0.VEnv} :
    ∀ (ts : List Ty) (as : List LArg) (xs : Tup Val ts) (ws : List Word),
      evalArgs ρ ts as = some xs →
      wordsOfTup xs = ws →
      ∀ (i : Nat) (hi : i < ts.length) (hia : i < as.length) (hiw : i < ws.length),
        ∃ (h : ws[i].fst = ts[i]), LArg.eval ρ ts[i] as[i] = some (h ▸ ws[i].snd)
  | [], _, _, _, _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | t :: ts', [], _, _, hev, _, _, _, _, _ => by
    have hnone : evalArgs ρ (t :: ts') [] = none :=
      evalArgs.eq_3 ρ (t :: ts') [] (fun h _ => by cases h)
        (fun _ _ _ _ _ h => by cases h)
    rw [hnone] at hev
    cases hev
  | t :: ts', a :: as', (v, vs), ws, hev, hws, i, hi, hia, hiw => by
    rw [evalArgs.eq_2] at hev
    cases heva : LArg.eval ρ t a with
    | none => simp [heva] at hev
    | some va =>
      cases hevs : evalArgs ρ ts' as' with
      | none => simp [heva, hevs] at hev
      | some vvs =>
        simp only [heva, hevs, Option.some.injEq, Prod.mk.injEq] at hev
        rcases hev with ⟨rfl, rfl⟩
        rw [wordsOfTup.eq_2] at hws
        cases hws
        cases i with
        | zero => exact ⟨rfl, heva⟩
        | succ j =>
          exact evalArgs_getElem_of_wordsOfTup ts' as' vvs (wordsOfTup vvs) hevs rfl j
            (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hia) (Nat.lt_of_succ_lt_succ hiw)

private theorem larg_eval_cast_ty {ρ : Frontend.C0.VEnv} {a : LArg} {t₁ t₂ : Ty}
    (ht : t₁ = t₂) {wt : Ty} (hw : wt = t₁) (wv : Val wt)
    (hev : LArg.eval ρ t₁ a = some (hw ▸ wv)) :
    LArg.eval ρ t₂ a = some ((hw.trans ht) ▸ wv) := by
  cases ht; exact hev

theorem VarRel.bindAll_of_pushJp {c' : LCtx} {ρH : HValEnv} {ρL : Frontend.C0.VEnv}
    {n : Nat} {ps : List LcParam} {as : List Word}
    (hc : ctxIdsBelow c' (n + 1)) (hvar : VarRel c' ρH ρL) (hpm : paramsMatch ps as)
    {xs : Tup Val (ps.map (·.ty.toTTy))} (hws : wordsOfTup xs = as) :
    let pvs := mkFreshVars (ps.map (·.ty.toTTy)) (n + 1)
    let hpvTy : pvs.map (·.ty) = ps.map (·.ty.toTTy) := mkFreshVars_map_ty _ (n + 1)
    VarRel (c'.bindAll ps (pvs.map vArg)) (ρH.bindAll ps as)
      (ρL.bind pvs (pvs.map (·.ty)) (hpvTy ▸ xs)) := by
  intro pvs hpvTy
  have hevVars : evalArgs (ρL.bind pvs (pvs.map (·.ty)) (hpvTy ▸ xs))
      (ps.map (·.ty.toTTy)) (pvs.map vArg) = some xs := by
    rw [VEnv.bind_cast_tys ρL pvs hpvTy.symm xs]
    exact evalArgs_bind_mkFreshVars (ps.map (·.ty.toTTy)) (n + 1) ρL xs
  have hbound : ∀ b ∈ pvs, n + 1 ≤ b.id := by
    intro b hb
    clear hevVars hvar hpm hws hc
    suffices ∀ (ts : List Ty) (m : Nat) (x : Frontend.C0.LVar),
        x ∈ mkFreshVars ts m → m ≤ x.id from
      this (ps.map (·.ty.toTTy)) (n + 1) b hb
    intro ts
    induction ts with
    | nil => intro m x hx; simp [mkFreshVars] at hx
    | cons _ _ ih =>
      intro m x hx
      simp only [mkFreshVars, List.mem_cons] at hx
      rcases hx with rfl | hx'
      · exact Nat.le_refl _
      · exact Nat.le_trans (Nat.le_succ _) (ih (m + 1) x hx')
  have hvarFresh : VarRel c' ρH (ρL.bind pvs (pvs.map (·.ty)) (hpvTy ▸ xs)) :=
    VarRel.bind_fresh _ hc hvar hbound
  have hlen : (pvs.map vArg).length = ps.length := by
    simp [pvs, mkFreshVars_length]
  refine VarRel.bindAll hvarFresh hlen hpm (fun i hi hia hiw => ?_)
  have hget := evalArgs_getElem_of_wordsOfTup (ps.map (·.ty.toTTy)) (pvs.map vArg) xs as
    hevVars hws i (by simp [hi]) hia hiw
  obtain ⟨hw, hev⟩ := hget
  have htyEq : (List.map (fun x => x.ty.toTTy) ps)[i]'(by simp [hi]) = ps[i].ty.toTTy := by simp
  exact ⟨hw.trans htyEq, larg_eval_cast_ty htyEq hw as[i].snd hev⟩

/-! ## §3. Case Dispatch Soundness (`dispatchAlts_wp`, `lowerCases_sound`) -/

private theorem width_ge_8_of_isScalar {ty : LcTy} (h : ty.isScalar = true) : 8 ≤ ty.width := by
  cases ty <;> simp [LcTy.isScalar, LcTy.width] at h ⊢

private theorem lcty_beq_object {x : LcTy} : (x == .object) = true ↔ x = .object := by
  cases x <;> decide

private theorem lcty_beq_tagged {x : LcTy} : (x == .tagged) = true ↔ x = .tagged := by
  cases x <;> decide

private theorem setWidth_64_of_eq {w : Nat} (hw : w = 64) (v : BitVec w) :
    BitVec.setWidth 64 v = hw ▸ v := by
  cases hw; simp

private theorem larg_eval_width64 {ρ : Frontend.C0.VEnv} {a : LArg} {w : Nat}
    (hw : w = 64) (v : BitVec w) (v64 : BitVec 64) (hv : v64 = hw ▸ v)
    (hev : LArg.eval ρ (Ty.bits w) a = some v) :
    LArg.eval ρ i64 a = some v64 := by
  cases hw; subst hv; exact hev

theorem pure_run_eq {α : Type} {a b : α} {n n' : Nat}
    (h : (pure a : LM α).run n = .ok (b, n')) : a = b ∧ n = n' := by
  simp only [pure, Pure.pure, StateT.run, StateT.pure, Except.pure] at h
  injection h with hpair
  injection hpair with h1 h2
  exact ⟨h1, h2⟩

private theorem eq_of_bitVec_ofNat_eq {w tag ci : Nat}
    (h8 : 8 ≤ w) (ht : tag < 2 ^ w) (hc : ci < 256)
    (heq : BitVec.ofNat w tag = BitVec.ofNat w ci) :
    ci = tag := by
  have hpow : 256 ≤ 2 ^ w := by
    have : 2 ^ 8 ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) h8
    omega
  have hcLt : ci < 2 ^ w := Nat.lt_of_lt_of_le hc hpow
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hcLt] at hnat
  exact hnat.symm

private def isCtorPat (p : LcPat × LcCode) : Bool :=
  match p.1 with | .ctor _ _ => true | _ => false

private def isDfltPat (p : LcPat × LcCode) : Bool :=
  match p.1 with | .dflt => true | _ => false

private theorem HWpCtorAlts_iff_filter {Δ : HEnv} {rt : BitVec 64} {retTy : LcTy}
    {J : HJEnv} {ρ : HValEnv} {Q : HPost} {X : HXPost} {tag : Nat} {kD : HState → Prop}
    {σ : HState} :
    ∀ (alts : List (LcPat × LcCode)),
      HWpCtorAlts Δ rt retTy J ρ Q X tag alts kD σ ↔
      HWpCtorAlts Δ rt retTy J ρ Q X tag (alts.filter isCtorPat) kD σ
  | [] => Iff.rfl
  | (.ctor _ _, _) :: rest => by
    simp only [List.filter_cons, isCtorPat, ↓reduceIte]
    rw [HWpCtorAlts.eq_2, HWpCtorAlts.eq_2]
    split <;> first | exact Iff.rfl | exact HWpCtorAlts_iff_filter rest
  | (.dflt, _) :: rest => by
    simp only [List.filter_cons, isCtorPat, Bool.false_eq_true, ↓reduceIte]
    rw [HWpCtorAlts.eq_3]
    exact HWpCtorAlts_iff_filter rest

private theorem HWpDfltAlts_iff_filter {Δ : HEnv} {rt : BitVec 64} {retTy : LcTy}
    {J : HJEnv} {ρ : HValEnv} {Q : HPost} {X : HXPost} {σ : HState} :
    ∀ (alts : List (LcPat × LcCode)),
      HWpDfltAlts Δ rt retTy J ρ Q X alts σ ↔
      HWpDfltAlts Δ rt retTy J ρ Q X (alts.filter isDfltPat) σ
  | [] => Iff.rfl
  | (.dflt, _) :: _ => by
    simp only [List.filter_cons, isDfltPat, ↓reduceIte]
    rw [HWpDfltAlts.eq_2, HWpDfltAlts.eq_2]
  | (.ctor _ _, _) :: rest => by
    simp only [List.filter_cons, isDfltPat, Bool.false_eq_true, ↓reduceIte]
    rw [HWpDfltAlts.eq_3]
    exact HWpDfltAlts_iff_filter rest

private theorem filter_ctor_map {f : LcCode → LM LExpr}
    (p : LcPat × LM LExpr → Bool)
    (hc : ∀ c n b, p (.ctor c n, b) = true) (hd : ∀ b, p (.dflt, b) = false) :
    ∀ (alts : List (LcPat × LcCode)),
      (alts.map (fun q => (q.1, f q.2))).filter p =
        (alts.filter isCtorPat).map (fun q => (q.1, f q.2))
  | [] => rfl
  | (.ctor c n, b) :: rest => by
    simp only [List.map_cons, List.filter_cons, isCtorPat, hc c n (f b), ↓reduceIte,
      filter_ctor_map p hc hd rest]
  | (.dflt, b) :: rest => by
    simp only [List.map_cons, List.filter_cons, isCtorPat, hd (f b), Bool.false_eq_true,
      ↓reduceIte, filter_ctor_map p hc hd rest]

private theorem filter_dflt_map {f : LcCode → LM LExpr}
    (p : LcPat × LM LExpr → Bool)
    (hc : ∀ c n b, p (.ctor c n, b) = false) (hd : ∀ b, p (.dflt, b) = true) :
    ∀ (alts : List (LcPat × LcCode)),
      (alts.map (fun q => (q.1, f q.2))).filter p =
        (alts.filter isDfltPat).map (fun q => (q.1, f q.2))
  | [] => rfl
  | (.ctor c n, b) :: rest => by
    simp only [List.map_cons, List.filter_cons, isDfltPat, hc c n (f b), Bool.false_eq_true,
      ↓reduceIte, filter_dflt_map p hc hd rest]
  | (.dflt, b) :: rest => by
    simp only [List.map_cons, List.filter_cons, isDfltPat, hd (f b), ↓reduceIte,
      filter_dflt_map p hc hd rest]

private theorem dispatchAlts_wp {Γ : Env} {Δ : HEnv} {rt : BitVec 64} {c : LCtx} {env : LEnv}
    {QH : HPost} {XH : HXPost} {QT : Post [c.retTy.toTTy]} {XT : XPost}
    {JH : HJEnv} {ρH : HValEnv} {σ : HState} {mem : Mem 64}
    {w tag : Nat} (hw8 : 8 ≤ w) (htag : tag < 2 ^ w) :
    ∀ (cs ds : List (LcPat × LcCode)) (n n' : Nat) (e : LExpr)
      (ρL : Frontend.C0.VEnv) (JL : Frontend.C0.JEnv) (tagArg : LArg),
      cs ++ ds ≠ [] →
      (∀ p ∈ cs, ∃ ci nm, p.1 = .ctor ci nm ∧ ci < 256) →
      (∀ p ∈ ds, p.1 = .dflt) →
      (∀ p ∈ cs ++ ds, LMMono (lowerCode env c p.2)) →
      HWpCtorAlts Δ rt c.retTy JH ρH QH XH tag cs (HWpDfltAlts Δ rt c.retTy JH ρH QH XH ds) σ →
      StateT.run (dispatchAlts tagArg w ((cs ++ ds).map (fun p => (p.1, lowerCode env c p.2)))) n =
        .ok (e, n') →
      LArg.eval ρL (Ty.bits w) tagArg = some (BitVec.ofNat w tag) →
      argIdsBelow tagArg n →
      (∀ p ∈ cs ++ ds, ∀ nr nr' ek ρ' J',
        n ≤ nr → VEnvAgreeBelow n ρ' ρL → JEnvAgreeBelow n J' JL →
        StateT.run (lowerCode env c p.2) nr = .ok (ek, nr') →
        HWp Δ rt c.retTy JH ρH QH XH p.2 σ →
        LExpr.wp Γ QT XT ek ρ' J' mem) →
      LExpr.wp Γ QT XT e ρL JL mem
  | [], [], _, _, _, _, _, _, hne, _, _, _, _, _, _, _, _ => by simp at hne
  | [], (.dflt, b) :: [], n, n', e, ρL, JL, _, _, _, _, _, hhw, hrun, _, _, hBr => by
    simp only [List.nil_append, List.map_cons, List.map_nil] at hrun
    rw [dispatchAlts.eq_2] at hrun
    rw [HWpCtorAlts.eq_1, HWpDfltAlts.eq_2] at hhw
    exact hBr (.dflt, b) (by simp) n n' e ρL JL (Nat.le_refl n)
      (VEnvAgreeBelow.refl n ρL) (JEnvAgreeBelow.refl n JL) hrun hhw
  | [], (.dflt, b) :: d2 :: ds', n, n', e, ρL, JL, tagArg, _, _, _, _, hhw, hrun, _, _, hBr => by
    simp only [List.nil_append, List.map_cons] at hrun
    rw [dispatchAlts.eq_3 tagArg w (lowerCode env c b) _ (by simp)] at hrun
    rw [HWpCtorAlts.eq_1, HWpDfltAlts.eq_2] at hhw
    exact hBr (.dflt, b) (by simp) n n' e ρL JL (Nat.le_refl n)
      (VEnvAgreeBelow.refl n ρL) (JEnvAgreeBelow.refl n JL) hrun hhw
  | [], (.ctor ci nm, b) :: _, _, _, _, _, _, _, _, _, hdsPat, _, _, _, _, _, _ => by
    exfalso; have h := hdsPat (.ctor ci nm, b) (by simp); cases h
  | (.dflt, b) :: _, _, _, _, _, _, _, _, _, hcsPat, _, _, _, _, _, _, _ => by
    exfalso; obtain ⟨_, _, hcon, _⟩ := hcsPat (.dflt, b) (by simp); injection hcon
  | (.ctor ci nm, b) :: cs', ds, n, n', e, ρL, JL, tagArg, _, hcsPat, hdsPat,
      hmono, hhw, hrun, hEv, hId, hBr => by
    cases hrest : cs' ++ ds with
    | nil =>
      have hcs0 : cs' = [] := (List.append_eq_nil_iff.mp hrest).1
      have hds0 : ds = [] := (List.append_eq_nil_iff.mp hrest).2
      subst hcs0; subst hds0
      simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil] at hrun
      rw [dispatchAlts.eq_2] at hrun
      rw [HWpCtorAlts.eq_2, HWpCtorAlts.eq_1, HWpDfltAlts.eq_1] at hhw
      split at hhw
      · exact hBr (.ctor ci nm, b) (by simp) n n' e ρL JL (Nat.le_refl n)
          (VEnvAgreeBelow.refl n ρL) (JEnvAgreeBelow.refl n JL) hrun hhw
      · cases hhw
    | cons p2 rest2 =>
      have hneRest : cs' ++ ds ≠ [] := by rw [hrest]; simp
      have hmap : (((.ctor ci nm, b) :: cs') ++ ds).map (fun p => (p.1, lowerCode env c p.2)) =
          (.ctor ci nm, lowerCode env c b) ::
            ((cs' ++ ds).map (fun p => (p.1, lowerCode env c p.2))) := by simp
      have hmapNe : ((cs' ++ ds).map (fun p => (p.1, lowerCode env c p.2))) ≠ [] :=
        fun hnil => hneRest (List.map_eq_nil_iff.mp hnil)
      rw [hmap, dispatchAlts.eq_4 tagArg w ci nm (lowerCode env c b) _ (fun h => hmapNe h)] at hrun
      refine cmpOp_wp hrun hEv (LArg.eval_imm_self ρL (Ty.bits w) (BitVec.ofNat w ci))
        (fun r ek ρ' hrunK hrId hagr hEvEq => ?_)
      simp only [lm_bind_run] at hrunK
      rcases hrunK with ⟨tb, n2, htb, eb, n3, heb, hpure⟩
      simp only [pure, Pure.pure, StateT.run, StateT.pure] at hpure
      rcases hpure with ⟨rfl, rfl⟩
      have hciLt : ci < 256 := by
        obtain ⟨ci', _, heq, hlt⟩ := hcsPat (.ctor ci nm, b) (by simp)
        injection heq with hci; exact hci ▸ hlt
      have hn2 : n + 1 ≤ n2 := hmono (.ctor ci nm, b) (by simp) _ _ _ htb
      have hn'2 : n ≤ n2 := Nat.le_trans (Nat.le_succ n) hn2
      rw [HWpCtorAlts.eq_2] at hhw
      simp only [CmpOp.evalBits] at hEvEq
      refine wp_jnz hEvEq (fun htrue => ?_) (fun hfalse => ?_)
      · have hbv : BitVec.ofNat w tag = BitVec.ofNat w ci := by
          simpa [decide_eq_true_iff] using htrue
        have hEqTag : ci = tag := eq_of_bitVec_ofNat_eq hw8 htag hciLt hbv
        simp only [hEqTag, ↓reduceIte] at hhw
        exact hBr (.ctor ci nm, b) (by simp) (n + 1) n2 tb ρ' JL (Nat.le_succ n)
          hagr (JEnvAgreeBelow.refl n JL) htb hhw
      · have hbv : BitVec.ofNat w tag ≠ BitVec.ofNat w ci := by
          simpa [decide_eq_true_iff] using hfalse
        have hNeTag : ci ≠ tag := fun heq => hbv (heq ▸ rfl)
        simp only [hNeTag, ↓reduceIte] at hhw
        have hEv' : LArg.eval ρ' (Ty.bits w) tagArg = some (BitVec.ofNat w tag) :=
          (hagr.eval hId).trans hEv
        have hId' : argIdsBelow tagArg n2 := argIdsBelow_mono hn'2 hId
        exact dispatchAlts_wp hw8 htag cs' ds n2 n' eb ρ' JL tagArg hneRest
          (fun p hp => hcsPat p (by simp [hp])) hdsPat
          (fun p hp => hmono p (by simp [hp])) hhw heb hEv' hId'
          (fun p hp nr nr' ek' ρ'' J'' hnr hagr2 hJ2 hek' hwpP =>
            hBr p (by simp [hp]) nr nr' ek' ρ'' J'' (Nat.le_trans hn'2 hnr)
              ((hagr2.mono hn'2).trans hagr) (hJ2.mono hn'2) hek' hwpP)

/-- Soundness of `lowerCases` (`LcCode.cases`). -/
theorem lowerCases_sound {m : LcModule} {env : LEnv} {Δ : HEnv} {Γ : Env}
    {rt : BitVec 64} {R : Mem 64 → Prop} {c : LCtx} {x n n' : Nat}
    {alts : List (LcPat × LcCode)} {e : LExpr}
    {QH : HPost} {XH : HXPost} {QT : Post [c.retTy.toTTy]} {XT : XPost}
    {JH : HJEnv} {ρH : HValEnv} {ρL : Frontend.C0.VEnv} {JL : Frontend.C0.JEnv}
    {σ : HState} {mem : Mem 64}
    (hfrag : m.inFirstOrderFragment = true) (henv : LEnvOk m env)
    (hAlts : LcAlts.inFirstOrder m.decls (c.jps.map fun p => (p.1, p.2.2)) alts = true)
    (hrun : (lowerCases c x (lowerAlts env c alts)).run n = .ok (e, n'))
    (hsim : HSimInv Δ rt R c n QH XH QT XT JH ρH ρL JL)
    (hm : (HState.mem rt σ ⋆ R) mem)
    (hwp : HWp Δ rt c.retTy JH ρH QH XH (.cases x alts) σ)
    (hBr : ∀ p ∈ alts, ∀ nr nr' ek ρ' J',
      n ≤ nr → VEnvAgreeBelow n ρ' ρL → JEnvAgreeBelow n J' JL →
      (lowerCode env c p.2).run nr = .ok (ek, nr') →
      HSimInv Δ rt R c nr QH XH QT XT JH ρH ρ' J' →
      HWp Δ rt c.retTy JH ρH QH XH p.2 σ →
      LExpr.wp Γ QT XT ek ρ' J' mem) :
    LExpr.wp Γ QT XT e ρL JL mem := by
  dsimp only [lowerCases] at hrun
  rw [lm_bind_run] at hrun
  rcases hrun with ⟨⟨xa, xt⟩, n1, hvar, hrunCases⟩
  obtain ⟨hn1, hlu⟩ := ctxVar_run_eq hvar
  subst n1
  have hxaId : argIdsBelow xa n := ctxIdsBelow_lookup_var hsim.idsOk hlu
  rw [HWp.eq_4] at hwp
  rcases hwp with ⟨tag, hcasesTag, hhwAlts⟩
  dsimp only [HState.casesTag] at hcasesTag
  cases hρ : ρH x with
  | none => simp [hρ] at hcasesTag
  | some p =>
    rcases p with ⟨ty, ⟨tWord, v⟩⟩
    cases tWord with
    | bool | float _ | pair _ _ => simp [hρ] at hcasesTag
    | bits w =>
      simp only [hρ] at hcasesTag
      obtain ⟨hwEq, hcasesBody⟩ := hcasesTag
      obtain ⟨la, _, hlaLu, hEvLa⟩ := hsim.varRel x ty ⟨Ty.bits w, v⟩ hρ
      rw [hlu] at hlaLu
      injection hlaLu with hlap
      have rfl_la : la = xa := (congrArg Prod.fst hlap).symm
      have rfl_ty : ty = xt := (congrArg Prod.snd hlap).symm
      subst la; subst ty
      have hw : w = xt.width := hwEq
      subst hw
      dsimp only [Val] at v
      have hEvXa : LArg.eval ρL (Ty.bits xt.width) xa = some v := by
        dsimp only [LcTy.toTTy] at hEvLa
        exact hEvLa
      let cs := alts.filter isCtorPat
      let ds := alts.filter isDfltPat
      have hmapEq : ∀ (f1 f2 : LcPat × LM LExpr → Bool),
          (∀ c n b, f1 (.ctor c n, b) = true) → (∀ b, f1 (.dflt, b) = false) →
          (∀ c n b, f2 (.ctor c n, b) = false) → (∀ b, f2 (.dflt, b) = true) →
          (lowerAlts env c alts).filter f1 ++ (lowerAlts env c alts).filter f2 =
            (cs ++ ds).map (fun p => (p.1, lowerCode env c p.2)) := by
        intro f1 f2 h1c h1d h2c h2d
        rw [lowerAlts_eq_map, filter_ctor_map f1 h1c h1d, filter_dflt_map f2 h2c h2d,
          ← List.map_append]
      have hhw : HWpCtorAlts Δ rt c.retTy JH ρH QH XH tag cs
          (HWpDfltAlts Δ rt c.retTy JH ρH QH XH ds) σ := by
        have hc := (HWpCtorAlts_iff_filter alts).mp hhwAlts
        exact HWpCtorAlts_conseq (HEnv.le_refl Δ) (fun _ _ h => h) (fun _ _ h => h) tag cs
          (fun _ h => (HWpDfltAlts_iff_filter alts).mp h) (HJEnv.le_refl JH) ρH σ hc
      have hmemAlts : ∀ p ∈ cs ++ ds, p ∈ alts := by
        intro p hp
        simp only [List.mem_append, cs, ds, List.mem_filter] at hp
        rcases hp with ⟨hp, _⟩ | ⟨hp, _⟩ <;> exact hp
      have hcsPat : ∀ p ∈ cs, ∃ ci nm, p.1 = .ctor ci nm ∧ ci < 256 := by
        intro p hp
        have hpMem : p ∈ alts := hmemAlts p (List.mem_append_left _ hp)
        have hfo := (inFirstOrder_of_mem_alts hAlts p hpMem).1
        have hpF := (List.mem_filter.mp hp).2
        cases hp1 : p.1 with
        | ctor ci nm => exact ⟨ci, nm, rfl, hfo ci nm hp1⟩
        | dflt => simp [isCtorPat, hp1] at hpF
      have hdsPat : ∀ p ∈ ds, p.1 = .dflt := by
        intro p hp
        have hpF := (List.mem_filter.mp hp).2
        cases hp1 : p.1 with
        | dflt => rfl
        | ctor _ _ => simp [isDfltPat, hp1] at hpF
      have hmonoCD : ∀ p ∈ cs ++ ds, LMMono (lowerCode env c p.2) := by
        intro p hp
        have hpFo := (inFirstOrder_of_mem_alts hAlts p (hmemAlts p hp)).2
        exact lowerCode_mono_of_fo hfrag henv p.2 c hpFo
      have hBrCD : ∀ p ∈ cs ++ ds, ∀ nr nr' ek ρ' J',
          n ≤ nr → VEnvAgreeBelow n ρ' ρL → JEnvAgreeBelow n J' JL →
          (lowerCode env c p.2).run nr = .ok (ek, nr') →
          HWp Δ rt c.retTy JH ρH QH XH p.2 σ →
          LExpr.wp Γ QT XT ek ρ' J' mem := by
        intro p hp nr nr' ek ρ' J' hnr hagr hJ hek hwpP
        exact hBr p (hmemAlts p hp) nr nr' ek ρ' J' hnr hagr hJ hek
          (HSimInv.transfer hsim hnr hagr hJ) hwpP
      dsimp only at hrunCases
      rw [hmapEq _ _ (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)]
        at hrunCases
      cases hcd : cs ++ ds with
      | nil =>
        have hcs0 : cs = [] := (List.append_eq_nil_iff.mp hcd).1
        have hds0 : ds = [] := (List.append_eq_nil_iff.mp hcd).2
        rw [hcs0, hds0, HWpCtorAlts.eq_1, HWpDfltAlts.eq_1] at hhw
        cases hhw
      | cons p1 rest =>
        cases rest with
        | nil =>
          simp only [hcd, List.map_cons, List.map_nil] at hrunCases
          have hp1Mem : p1 ∈ cs ++ ds := by rw [hcd]; simp
          rcases List.mem_append.mp hp1Mem with hpCs | hpDs
          · obtain ⟨ci, nm, hpPat, _⟩ := hcsPat p1 hpCs
            have hcsEq : cs = [p1] := by
              have hle : cs.length ≤ 1 := by
                have := congrArg List.length hcd
                simp only [List.length_append, List.length_cons, List.length_nil] at this
                omega
              cases hcsVal : cs with
              | nil => rw [hcsVal] at hpCs; cases hpCs
              | cons a tl =>
                cases htlVal : tl with
                | nil =>
                  rw [hcsVal, htlVal, List.cons_append, List.nil_append] at hcd
                  injection hcd with h1 _
                  exact congrArg (· :: []) h1
                | cons _ _ => rw [hcsVal, htlVal] at hle; simp at hle
            have hdsEq : ds = [] := by
              have hlen := congrArg List.length hcd
              simp only [hcsEq, List.length_append, List.length_cons, List.length_nil] at hlen
              exact List.eq_nil_of_length_eq_zero (by omega)
            rw [hcsEq, hdsEq] at hhw
            rcases p1 with ⟨pat1, b1⟩
            dsimp only at hpPat; subst hpPat
            rw [HWpCtorAlts.eq_2, HWpCtorAlts.eq_1, HWpDfltAlts.eq_1] at hhw
            split at hhw
            · exact hBrCD (.ctor ci nm, b1) hp1Mem n n' e ρL JL (Nat.le_refl n)
                (VEnvAgreeBelow.refl n ρL) (JEnvAgreeBelow.refl n JL) hrunCases hhw
            · cases hhw
          · have hpPat := hdsPat p1 hpDs
            have hcs0 : cs = [] := by
              cases hcsVal : cs with
              | nil => rfl
              | cons a tl =>
                rw [hcsVal, List.cons_append] at hcd
                injection hcd with _ htl
                have hdsNil := (List.append_eq_nil_iff.mp htl).2
                rw [hdsNil] at hpDs; cases hpDs
            have hdsEq : ds = [p1] := by rw [hcs0, List.nil_append] at hcd; exact hcd
            rw [hcs0, hdsEq] at hhw
            rcases p1 with ⟨pat1, b1⟩
            dsimp only at hpPat; subst hpPat
            rw [HWpCtorAlts.eq_1, HWpDfltAlts.eq_2] at hhw
            exact hBrCD (.dflt, b1) hp1Mem n n' e ρL JL (Nat.le_refl n)
              (VEnvAgreeBelow.refl n ρL) (JEnvAgreeBelow.refl n JL) hrunCases hhw
        | cons p2 rest2 =>
          have hneCD : cs ++ ds ≠ [] := by rw [hcd]; simp
          have hmapCons : List.map (fun p => (p.1, lowerCode env c p.2)) (cs ++ ds) =
              (p1.1, lowerCode env c p1.2) :: (p2.1, lowerCode env c p2.2) ::
                List.map (fun p => (p.1, lowerCode env c p.2)) rest2 := by
            rw [hcd]; rfl
          rw [hmapCons] at hrunCases
          dsimp only at hrunCases
          rw [← hmapCons] at hrunCases
          by_cases hsc : xt.isScalar = true
          · simp only [hsc, ↓reduceIte] at hrunCases hcasesBody
            have h8 := width_ge_8_of_isScalar hsc
            have htagLt : tag < 2 ^ xt.width := hcasesBody ▸ v.isLt
            have hEvOfNat :
                LArg.eval ρL (Ty.bits xt.width) xa = some (BitVec.ofNat xt.width tag) := by
              have hvEq : BitVec.ofNat xt.width tag = v := by
                rw [hcasesBody]
                apply BitVec.eq_of_toNat_eq
                simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt v.isLt]
              rw [hvEq]
              exact hEvXa
            exact dispatchAlts_wp h8 htagLt cs ds n n' e ρL JL xa hneCD hcsPat hdsPat
              hmonoCD hhw hrunCases hEvOfNat hxaId hBrCD
          · simp only [hsc, Bool.false_eq_true, ↓reduceIte] at hrunCases hcasesBody
            by_cases hobjB : (xt == .object) = true
            · have hobj := lcty_beq_object.mp hobjB
              subst hobj
              dsimp only [LcTy.width] at v
              simp only [hobjB, ↓reduceIte] at hrunCases
              simp only [↓reduceIte] at hcasesBody
              obtain ⟨_, o, hoMem, hoAddr, hoWf, hoTag⟩ := hcasesBody
              have hload := mem_load_lcnfObj_tag hoMem hoWf hoAddr hm
              have h8 : 8 ≤ 8 := Nat.le_refl 8
              have htagLt : tag < 2 ^ 8 := by rw [hoTag]; exact hoWf.2.2.2.2.2.1
              refine lm_loadAt_wp hrunCases hEvXa hxaId hload
                (fun r ek ρ' nr hnr hek hrId hagr hrEv => ?_)
              have hrEv' : LArg.eval ρ' (Ty.bits 8) r = some (BitVec.ofNat 8 tag) := by
                rw [hoTag]; exact hrEv
              exact dispatchAlts_wp h8 htagLt cs ds nr n' ek ρ' JL r hneCD hcsPat hdsPat
                hmonoCD hhw hek hrEv' hrId
                (fun p hp nr2 nr2' ek2 ρ2 J2 hnr2 hagr2 hJ2 hek2 hwpP =>
                  hBrCD p hp nr2 nr2' ek2 ρ2 J2 (Nat.le_trans (by omega) hnr2)
                    ((hagr2.mono (by omega)).trans hagr) (hJ2.mono (by omega)) hek2 hwpP)
            · have hobjNe : xt ≠ .object := fun heq => hobjB (lcty_beq_object.mpr heq)
              have hobjF : (xt == .object) = false := Bool.eq_false_iff.mpr hobjB
              simp only [hobjF, Bool.false_eq_true, ↓reduceIte] at hrunCases
              simp only [hobjNe, ↓reduceIte] at hcasesBody
              by_cases htagB : (xt == .tagged) = true
              · have htagTy := lcty_beq_tagged.mp htagB
                subst htagTy
                dsimp only [LcTy.width] at v
                simp only [htagB, ↓reduceIte] at hrunCases
                simp only [↓reduceIte] at hcasesBody
                have htagEq : tag = (BitVec.setWidth 64 v >>> 1).toNat := hcasesBody.2
                have htagLt : tag < 2 ^ 64 := by
                  rw [htagEq]; exact (BitVec.setWidth 64 v >>> 1).isLt
                refine lshr64_wp hrunCases hEvXa (LArg.eval_imm_self ρL i64 1#64)
                  (fun r ek ρ' hek hrId hagr hrEv => ?_)
                have h1Mod : (1#64 : BitVec 64).toNat % 64 = 1 := rfl
                rw [h1Mod] at hrEv
                have hrEv' : LArg.eval ρ' (Ty.bits 64) r = some (BitVec.ofNat 64 tag) := by
                  have hvSelf : BitVec.setWidth 64 v = v := by
                    apply BitVec.eq_of_toNat_eq
                    simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt v.isLt]
                  have hvEq : BitVec.ofNat 64 tag = v >>> 1 := by
                    rw [htagEq, hvSelf]
                    apply BitVec.eq_of_toNat_eq
                    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (v >>> 1).isLt]
                  rw [hvEq]; exact hrEv
                exact dispatchAlts_wp (by omega) htagLt cs ds (n + 1) n' ek ρ' JL r
                  hneCD hcsPat hdsPat hmonoCD hhw hek hrEv' hrId
                  (fun p hp nr2 nr2' ek2 ρ2 J2 hnr2 hagr2 hJ2 hek2 hwpP =>
                    hBrCD p hp nr2 nr2' ek2 ρ2 J2 (Nat.le_trans (Nat.le_succ n) hnr2)
                      ((hagr2.mono (Nat.le_succ n)).trans hagr)
                      (hJ2.mono (Nat.le_succ n)) hek2 hwpP)
              · have htagNe : xt ≠ .tagged := fun heq => htagB (lcty_beq_tagged.mpr heq)
                have htagF : (xt == .tagged) = false := Bool.eq_false_iff.mpr htagB
                simp only [htagF, Bool.false_eq_true, ↓reduceIte] at hrunCases
                simp only [htagNe, ↓reduceIte] at hcasesBody
                have hwid64 : xt.width = 64 := hcasesBody.1
                let v64 : BitVec 64 := hwid64 ▸ v
                have hv64 : BitVec.setWidth 64 v = v64 := setWidth_64_of_eq hwid64 v
                have hEv64 : LArg.eval ρL i64 xa = some v64 :=
                  larg_eval_width64 hwid64 v v64 rfl hEvXa
                rw [hv64] at hcasesBody
                have htagLt : tag < 2 ^ 64 := by
                  have hb := hcasesBody.2
                  split at hb
                  · rw [hb]; exact (v64 >>> 1).isLt
                  · obtain ⟨o, _, _, hwf, htagO⟩ := hb
                    rw [htagO]; exact Nat.lt_trans hwf.2.2.2.2.2.1 (by decide)
                refine isScalarObj_wp hrunCases hEv64 (fun s ekJ ρ1 hrunJ hsId hagr1 hsEv => ?_)
                let Inv : Val i64 → Mem 64 → Prop := fun vJ m1 =>
                  vJ = BitVec.ofNat 64 tag ∧ m1 = mem
                have hdispMono : LMMono
                    (dispatchAlts (vArg { id := n + 2 + 1, name := "", ty := i64 }) 64
                    ((cs ++ ds).map (fun p => (p.1, lowerCode env c p.2)))) :=
                  dispatchAlts_mono _ 64 _ (fun q hq => by
                    rw [List.mem_map] at hq
                    obtain ⟨p, hpMem, rfl⟩ := hq
                    exact hmonoCD p hpMem)
                refine withJoin1_wp Inv hrunJ hdispMono
                  (fun r blk n2 J' hblk hrId hJ1 vJ m1 hInvJ hagr2 hrEv => ?_)
                  (fun j body n2 J' hn2 hpre hJ1 hj => ?_)
                · obtain ⟨hvJ, rfl⟩ := hInvJ
                  subst hvJ
                  exact dispatchAlts_wp (by omega) htagLt cs ds (n + 2 + 2) n2 blk
                    (ρ1.set (n + 2 + 1) i64 (BitVec.ofNat 64 tag)) J' r
                    hneCD hcsPat hdsPat hmonoCD hhw hblk hrEv hrId
                    (fun p hp nr2 nr2' ek2 ρ2 J2 hnr2 hagr3 hJ3 hek2 hwpP =>
                      have hagr0 : VEnvAgreeBelow n ρ2 ρL :=
                        ((hagr3.mono (by omega)).trans (hagr2.mono (by omega))).trans hagr1
                      have hJ0 : JEnvAgreeBelow n J2 JL :=
                        (hJ3.mono (by omega)).trans (hJ1.mono (by omega))
                      hBrCD p hp nr2 nr2' ek2 ρ2 J2 (Nat.le_trans (by omega) hnr2)
                        hagr0 hJ0 hek2 hwpP)
                · rw [lm_bind_run] at hpre
                  obtain ⟨ptr, n3, hptr, hrest⟩ := hpre
                  rw [lm_bind_run] at hrest
                  obtain ⟨sc, n4, hscPre, hpure⟩ := hrest
                  obtain ⟨hbodyEq, hn4Eq⟩ := pure_run_eq hpure
                  subst hbodyEq; subst hn4Eq
                  have hxaEv1 : LArg.eval ρ1 i64 xa = some v64 := (hagr1.eval hxaId).trans hEv64
                  have hxaId2 : argIdsBelow xa n2 := argIdsBelow_mono (by omega) hxaId
                  refine wp_jnz hsEv (fun htrue => ?_) (fun hfalse => ?_)
                  · have hvBit : v64 &&& 1#64 ≠ 0#64 := of_decide_eq_true htrue
                    have hb := hcasesBody.2
                    split at hb
                    · refine lshr64_wp hscPre hxaEv1 (LArg.eval_imm_self ρ1 i64 1#64)
                        (fun rS ekS ρS hekS _ _ hrEvS => ?_)
                      obtain ⟨hekEq, _⟩ := pure_run_eq hekS
                      subst hekEq
                      have h1Mod : (1#64 : BitVec 64).toNat % 64 = 1 := rfl
                      rw [h1Mod] at hrEvS
                      have hvEq : v64 >>> 1 = BitVec.ofNat 64 tag := by
                        rw [hb]
                        apply BitVec.eq_of_toNat_eq
                        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (v64 >>> 1).isLt]
                      exact hj J' rS ρS mem (BitVec.ofNat 64 tag)
                        (JEnvAgreeBelow.refl _ J') (hvEq ▸ hrEvS) ⟨rfl, rfl⟩
                    · exact absurd hvBit ‹_›
                  · have hvBit : ¬(v64 &&& 1#64 ≠ 0#64) := of_decide_eq_false hfalse
                    have hb := hcasesBody.2
                    split at hb
                    · exact absurd ‹_› hvBit
                    · obtain ⟨o, hoMem, hoAddr, hoWf, hoTag⟩ := hb
                      have hload := mem_load_lcnfObj_tag hoMem hoWf hoAddr hm
                      refine lm_loadAt_wp hptr hxaEv1 hxaId2 hload
                        (fun t8 ek8 ρ8 nr8 hnr8 hek8 ht8Id hagr8 ht8Ev => ?_)
                      refine convW_wp hek8 ht8Ev ht8Id
                        (fun t64 ek64 ρ64 _ _ hek64 _ _ ht64Ev => ?_)
                      obtain ⟨hekEq, _⟩ := pure_run_eq hek64
                      subst hekEq
                      have hsetW :
                          BitVec.setWidth 64 (BitVec.ofNat 8 o.tag) = BitVec.ofNat 64 tag := by
                        rw [hoTag]
                        apply BitVec.eq_of_toNat_eq
                        have hlt8 : o.tag < 2 ^ 8 := hoWf.2.2.2.2.2.1
                        have hlt64 : o.tag < 2 ^ 64 := Nat.lt_trans hlt8 (by decide)
                        simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt8, Nat.mod_eq_of_lt hlt64]
                      exact hj J' t64 ρ64 mem (BitVec.ofNat 64 tag)
                        (JEnvAgreeBelow.refl _ J') (hsetW ▸ ht64Ev) ⟨rfl, rfl⟩

end LeanQbe.T.LeanLCNF.Sem
