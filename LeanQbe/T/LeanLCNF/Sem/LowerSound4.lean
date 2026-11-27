module

public import LeanQbe.T.LeanLCNF.Sem.LowerSound3b

/-!
# Module & Recursive-SCC Lowering Soundness (`LowerSound4.lean`)

Lifts body-level simulation (`lowerCode_sound`) through declarations (`lowerDecl_sound`,
`lowerDecl_sound_loop`), acyclic linked modules (`lowerModule_moduleOk`,
`lowerModule_moduleOk_idx`), and mutually-recursive fixed-point semantics
(`lowerModule_moduleSccOk`, `lowerModule_semScc`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.LeanLCNF

private theorem rtCoreCallSigs_subset_rtC0CoreMod_sigs :
    rtCoreCallSigs.all (fun s => decide (s ∈ rtC0CoreMod.fns.map Fn.sig)) = true := by
  decide

private theorem mem_mapM_ok {α β : Type} {f : α → Except String β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys →
      (∀ x ∈ xs, ∃ y ∈ ys, f x = .ok y) ∧ (∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y)
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨(fun _ hx => by cases hx), (fun _ hy => by cases hy)⟩
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases hx : f x with
    | error err => simp [hx] at h
    | ok y =>
      simp only [hx] at h
      cases hxs : xs.mapM f with
      | error err => simp [hxs] at h
      | ok ys' =>
        simp only [hxs, pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨ihL, ihR⟩ := mem_mapM_ok hxs
        refine ⟨fun a ha => ?_, fun b hb => ?_⟩
        · rcases List.mem_cons.mp ha with rfl | ha'
          · exact ⟨y, List.mem_cons_self, hx⟩
          · obtain ⟨b, hbMem, hbOk⟩ := ihL a ha'
            exact ⟨b, List.mem_cons_of_mem _ hbMem, hbOk⟩
        · rcases List.mem_cons.mp hb with rfl | hb'
          · exact ⟨x, List.mem_cons_self, hx⟩
          · obtain ⟨a, haMem, haOk⟩ := ihR b hb'
            exact ⟨a, List.mem_cons_of_mem _ haMem, haOk⟩

private theorem eq_of_map_eq_of_mem_nodup {α β : Type} (f : α → β) :
    ∀ {xs : List α}, (xs.map f).Nodup → ∀ {x y : α}, x ∈ xs → y ∈ xs → f x = f y → x = y
  | [], hn, _, _, hx, _, _ => by cases hx
  | a :: rest, hn, x, y, hx, hy, heq => by
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd (heq ▸ List.mem_map_of_mem hy') hn.1
    · exact absurd (heq.symm ▸ List.mem_map_of_mem hx') hn.1
    · exact eq_of_map_eq_of_mem_nodup f hn.2 hx' hy' heq

private theorem find_name_eq_some_of_mem_nodup :
    ∀ {xs : List LcDecl}, (xs.map (·.name)).Nodup → ∀ {d : LcDecl},
      d ∈ xs → xs.find? (·.name == d.name) = some d
  | [], _, _, hd => by cases hd
  | a :: rest, hn, d, hd => by
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hd with rfl | hd'
    · simp [List.find?]
    · have hne : a.name ≠ d.name := fun heq => hn.1 (heq ▸ List.mem_map_of_mem hd')
      have hbeq : (a.name == d.name) = false := beq_false_of_ne hne
      simp only [List.find?, hbeq]
      exact find_name_eq_some_of_mem_nodup hn.2 hd'

private theorem HEnv.le_of_step {Δ : Nat → HEnv} (hstep : ∀ k, (Δ k).le (Δ (k + 1))) :
    ∀ {a b : Nat}, a ≤ b → (Δ a).le (Δ b)
  | a, b, hab => by
    induction b with
    | zero =>
      have : a = 0 := Nat.le_zero.mp hab
      subst this
      exact HEnv.le_refl _
    | succ b ih =>
      rcases Nat.lt_or_eq_of_le hab with hlt | rfl
      · exact HEnv.le_trans (ih (Nat.lt_succ_iff.mp hlt)) (hstep b)
      · exact HEnv.le_refl _

private theorem func_wp_cast_roundtrip {Γ : Env} {as1 as2 rs1 rs2 : List Ty}
    (ha : as1 = as2) (hr : rs1 = rs2) {body : Func as1 rs1}
    {xs : Tup Val as1} {mem : Mem 64} {Q : Post rs1} {X : XPost}
    (hwp : Func.wp Γ body (ha.symm ▸ (ha ▸ xs)) mem (hr.symm ▸ (hr ▸ Q)) X) :
    Func.wp Γ body xs mem Q X := by
  subst ha; subst hr; exact hwp

private theorem inFirstOrderFragment_decl_mem {m : LcModule}
    (hfrag : m.inFirstOrderFragment = true) {d : LcDecl} (hd : d ∈ m.decls) :
    d.inFirstOrder m.decls = true := by
  simp only [LcModule.inFirstOrderFragment, Bool.and_eq_true, List.all_eq_true] at hfrag
  exact hfrag.2 d hd

private theorem inFirstOrderFragment_nodup_mangle {m : LcModule}
    (hfrag : m.inFirstOrderFragment = true) :
    (m.decls.map (fun d => mangleLc d.name)).Nodup := by
  simp only [LcModule.inFirstOrderFragment, Bool.and_eq_true] at hfrag
  exact nodup_of_symsNodup hfrag.1.2

private theorem inFirstOrderFragment_nodup_name {m : LcModule}
    (hfrag : m.inFirstOrderFragment = true) :
    (m.decls.map (·.name)).Nodup := by
  simp only [LcModule.inFirstOrderFragment, Bool.and_eq_true] at hfrag
  exact nodup_of_symsNodup hfrag.1.1

private theorem decl_body_fo_of_decl_fo {decls : List LcDecl} {d : LcDecl}
    (hd : d.inFirstOrder decls = true) :
    d.body.inFirstOrder decls [] = true := by
  simp only [LcDecl.inFirstOrder, Bool.and_eq_true] at hd
  exact hd.2

private def posFn (xs : List Fn) (fn : Fn) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => if x.name == fn.name then 0 else 1 + posFn rest fn

private theorem posFn_lt_length :
    ∀ {xs : List Fn} {fn : Fn}, fn ∈ xs → posFn xs fn < xs.length
  | [], _, hfn => by cases hfn
  | x :: rest, fn, hfn => by
    simp only [posFn, List.length_cons]
    by_cases hbeq : (x.name == fn.name) = true
    · simp only [hbeq, ↓reduceIte]; omega
    · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      rcases List.mem_cons.mp hfn with rfl | hrest
      · simp at hbeq
      · have hlt := posFn_lt_length hrest; omega

private theorem mem_take_succ_posFn :
    ∀ {xs : List Fn}, (xs.map Fn.name).Nodup → ∀ {fn : Fn},
      fn ∈ xs → fn ∈ xs.take (posFn xs fn + 1)
  | [], _, _, hfn => by cases hfn
  | x :: rest, hn, fn, hfn => by
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [posFn]
    by_cases hbeq : (x.name == fn.name) = true
    · simp only [hbeq, ↓reduceIte, List.take_succ_cons]
      have hnm : x.name = fn.name := beq_iff_eq.mp hbeq
      rcases List.mem_cons.mp hfn with rfl | hrest
      · exact List.mem_cons_self
      · exact absurd (hnm ▸ List.mem_map_of_mem hrest) hn.1
    · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      rcases List.mem_cons.mp hfn with rfl | hrest
      · simp at hbeq
      · rw [Nat.add_comm 1 (posFn rest fn), Nat.add_assoc, List.take_succ_cons]
        exact List.mem_cons_of_mem _ (mem_take_succ_posFn hn.2 hrest)

private theorem split_at_posFn :
    ∀ {xs : List Fn}, (xs.map Fn.name).Nodup → ∀ {fn : Fn},
      fn ∈ xs → xs = xs.take (posFn xs fn) ++ fn :: xs.drop (posFn xs fn + 1)
  | [], _, _, hfn => by cases hfn
  | x :: rest, hn, fn, hfn => by
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [posFn]
    by_cases hbeq : (x.name == fn.name) = true
    · simp only [hbeq, ↓reduceIte, List.take_zero, List.drop_succ_cons, List.drop_zero,
        List.nil_append]
      have hnm : x.name = fn.name := beq_iff_eq.mp hbeq
      rcases List.mem_cons.mp hfn with rfl | hrest
      · rfl
      · exact absurd (hnm ▸ List.mem_map_of_mem hrest) hn.1
    · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      rcases List.mem_cons.mp hfn with rfl | hrest
      · simp at hbeq
      · rw [Nat.add_comm 1 (posFn rest fn), List.take_succ_cons, List.cons_append,
          List.drop_succ_cons]
        exact congrArg (x :: ·) (split_at_posFn hn.2 hrest)

private theorem not_mem_take_of_lt_posFn :
    ∀ {xs : List Fn} {fn : Fn}, fn ∈ xs → ∀ {i : Nat},
      i < posFn xs fn → fn.name ∉ (xs.take (i + 1)).map Fn.name
  | [], _, hfn, _, _ => by cases hfn
  | x :: rest, fn, hfn, i, hi => by
    simp only [posFn] at hi
    by_cases hbeq : (x.name == fn.name) = true
    · simp only [hbeq, ↓reduceIte] at hi; omega
    · simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hi
      rcases List.mem_cons.mp hfn with rfl | hrest
      · simp at hbeq
      · have hne : fn.name ≠ x.name := fun heq => hbeq (beq_iff_eq.mpr heq.symm)
        cases i with
        | zero =>
          simp only [Nat.zero_add, List.take_succ_cons, List.take_zero, List.map_cons,
            List.map_nil, List.mem_singleton]
          exact hne
        | succ j =>
          simp only [List.take_succ_cons, List.map_cons, List.mem_cons, not_or]
          exact ⟨hne, not_mem_take_of_lt_posFn hrest (by omega)⟩

private theorem mem_take_posFn_lt :
    ∀ {xs : List Fn}, (xs.map Fn.name).Nodup → ∀ {fn g : Fn},
      g ∈ xs.take (posFn xs fn) → g ∈ xs ∧ posFn xs g < posFn xs fn
  | [], _, _, _, hg => by simp at hg
  | x :: rest, hn, fn, g, hg => by
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [posFn] at hg ⊢
    by_cases hbeq : (x.name == fn.name) = true
    · simp only [hbeq, ↓reduceIte, List.take_zero] at hg
      cases hg
    · simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hg ⊢
      rw [Nat.add_comm 1 (posFn rest fn), List.take_succ_cons] at hg
      rcases List.mem_cons.mp hg with rfl | hgRest
      · simp; omega
      · obtain ⟨hgMem, hlt⟩ := mem_take_posFn_lt hn.2 hgRest
        have hne : x.name ≠ g.name := fun heq => hn.1 (heq ▸ List.mem_map_of_mem hgMem)
        have hbg : (x.name == g.name) = false := beq_false_of_ne hne
        simp only [hbg, Bool.false_eq_true, ↓reduceIte]
        exact ⟨List.mem_cons_of_mem _ hgMem, by omega⟩

private theorem not_rtCoreFnNames_of_decl {m : LcModule}
    {progTfs : List Frontend.C0.TFlatFn}
    (hfrag : m.inFirstOrderFragment = true)
    (hlow : lowerModule m = .ok progTfs)
    (hnodup : (linkLcnfWithRtC0 progTfs).namesNodup)
    {d : LcDecl} (hd : d ∈ m.decls) :
    ¬mangleLc d.name ∈ rtCoreFnNames := by
  have hmapM := lowerModule_firstOrder_decls hfrag hlow
  obtain ⟨tf, htfMem, htfOk⟩ := (mem_mapM_ok hmapM).1 d hd
  have hsig := lowerDecl_sig htfOk
  have hprogMem := tflatFn_toFn_mem_progMod htfMem
  have hdisj := lcnfProgMod_disjoint_rt_of_nodup hnodup tf.toFn hprogMem
  change ¬tf.name ∈ rtCoreFnNames at hdisj
  rw [hsig.1] at hdisj
  exact hdisj

/-- Spec-parametric declaration lowering soundness for non-self-tail Phase-1 functions. -/
theorem lowerDecl_sound_spec {m : LcModule} {d : LcDecl} {fn : Frontend.C0.TFlatFn}
    {Δ : HEnv} {Γ : Env} {S : HSpec}
    (hfrag : m.inFirstOrderFragment = true)
    (hΓ : HCallEnvOk m Δ Γ)
    (hret : HEnv.RetTyped m Δ)
    (hd : d.inFirstOrder m.decls = true)
    (hnoLoop : hasSelfTail d.name d.params.length d.body = false)
    (hlow : lowerDecl (firstOrderLEnv m) d = .ok fn)
    (hbody : ∀ rt as σ Q' X', HInv rt σ → paramsMatch d.params as → S as σ Q' X' →
      HWp Δ rt d.retTy HJEnv.empty (HValEnv.empty.bindAll d.params as) Q' X' d.body σ)
    {xs : Tup Val (i64 :: (d.params.map (·.ty.toTTy) |>.take regArgs))}
    {mem : Mem 64} {Q : Post [d.retTy.toTTy]} {X : XPost}
    (hs : liftDeclSpec S d.params d.retTy xs mem Q X)
    (ha : fn.toFn.as = i64 :: (d.params.map (·.ty.toTTy) |>.take regArgs) := by
      exact (lowerDecl_sig hlow).2.1)
    (hr : fn.toFn.rs = [d.retTy.toTTy] := by
      exact (lowerDecl_sig hlow).2.2) :
    Func.wp Γ fn.toFn.body (ha ▸ xs) mem (hr ▸ Q) X :=
  lowerDecl_of_body_sim (lowerCode_sound hfrag) hΓ hret
    (decl_body_fo_of_decl_fo hd) hnoLoop hlow hbody hs ha hr

/-- Per-declaration lowering soundness for non-self-tail Phase-1 first-order functions,
parametric in any `Γ` satisfying `HCallEnvOk m Δ Γ`. -/
theorem lowerDecl_sound {m : LcModule} {d : LcDecl} {fn : Frontend.C0.TFlatFn}
    {Δ : HEnv} {Γ : Env}
    (hfrag : m.inFirstOrderFragment = true)
    (hΓ : HCallEnvOk m Δ Γ)
    (hret : HEnv.RetTyped m Δ)
    (hd : d.inFirstOrder m.decls = true)
    (hnoLoop : hasSelfTail d.name d.params.length d.body = false)
    (hlow : lowerDecl (firstOrderLEnv m) d = .ok fn)
    (hbody : ∀ rt as σ Q' X', HInv rt σ → paramsMatch d.params as → Δ d.name as σ Q' X' →
      HWp Δ rt d.retTy HJEnv.empty (HValEnv.empty.bindAll d.params as) Q' X' d.body σ)
    {xs : Tup Val (i64 :: (d.params.map (·.ty.toTTy) |>.take regArgs))}
    {mem : Mem 64} {Q : Post [d.retTy.toTTy]} {X : XPost}
    (hs : liftDeclSpec (Δ d.name) d.params d.retTy xs mem Q X)
    (ha : fn.toFn.as = i64 :: (d.params.map (·.ty.toTTy) |>.take regArgs) := by
      exact (lowerDecl_sig hlow).2.1)
    (hr : fn.toFn.rs = [d.retTy.toTTy] := by
      exact (lowerDecl_sig hlow).2.2) :
    Func.wp Γ fn.toFn.body (ha ▸ xs) mem (hr ▸ Q) X :=
  lowerDecl_sound_spec hfrag hΓ hret hd hnoLoop hlow hbody hs ha hr

/-- Per-declaration lowering soundness for self-tail Phase-1 first-order loop functions,
parametric in any indexed chain `Δ : Nat → HEnv` and target env `Γ`. -/
theorem lowerDecl_sound_loop {m : LcModule} {d : LcDecl} {fn : Frontend.C0.TFlatFn}
    {Δ : Nat → HEnv} {Γ : Env} {k : Nat}
    (hfrag : m.inFirstOrderFragment = true)
    (hrt : rtCoreCallEnv.le Γ)
    (hΓ : ∀ j, j < k → HCallEnvOk m (Δ j) Γ)
    (hret : ∀ j, j < k → HEnv.RetTyped m (Δ j))
    (hd : d.inFirstOrder m.decls = true)
    (hfind : m.decls.find? (·.name == d.name) = some d)
    (hloop : hasSelfTail d.name d.params.length d.body = true)
    (hlow : lowerDecl (firstOrderLEnv m) d = .ok fn)
    (hbody : ∀ j, j ≤ k → ∀ rt as σ Q' X', HInv rt σ → paramsMatch d.params as →
      Δ j d.name as σ Q' X' →
      HWp (match j with | 0 => HEnv.bot | j' + 1 => Δ j')
        rt d.retTy HJEnv.empty (HValEnv.empty.bindAll d.params as) Q' X' d.body σ)
    {xs : Tup Val (i64 :: (d.params.map (·.ty.toTTy) |>.take regArgs))}
    {mem : Mem 64} {Q : Post [d.retTy.toTTy]} {X : XPost}
    (hs : liftDeclSpec (Δ k d.name) d.params d.retTy xs mem Q X)
    (ha : fn.toFn.as = i64 :: (d.params.map (·.ty.toTTy) |>.take regArgs) := by
      exact (lowerDecl_sig hlow).2.1)
    (hr : fn.toFn.rs = [d.retTy.toTTy] := by
      exact (lowerDecl_sig hlow).2.2) :
    Func.wp Γ fn.toFn.body (ha ▸ xs) mem (hr ▸ Q) X :=
  lowerDecl_loop_of_body_sim (lowerCode_sound hfrag) hrt hΓ hret
    (decl_body_fo_of_decl_fo hd) hfind hloop hlow hbody hs ha hr

private theorem progFn_wp_from_decl {m : LcModule}
    {progTfs : List Frontend.C0.TFlatFn} {fn : Fn}
    (hfrag : m.inFirstOrderFragment = true)
    (hlow : lowerModule m = .ok progTfs)
    (hfnMem : fn ∈ (lcnfProgMod progTfs).fns)
    {xs : Tup Val fn.as} {mem : Mem 64} {Q : Post fn.rs} {X : XPost}
    {Δs : HEnv}
    (hspec : liftEnv m Δs fn.name fn.as fn.rs xs mem Q X) :
    ∃ (d : LcDecl) (tf : Frontend.C0.TFlatFn),
      d ∈ m.decls ∧ tf ∈ progTfs ∧ tf.toFn = fn ∧
        lowerDecl (firstOrderLEnv m) d = .ok tf ∧
        d.inFirstOrder m.decls = true ∧
        m.decls.find? (·.name == d.name) = some d ∧
        ∃ (ha : fn.as = i64 :: (d.params.map (·.ty.toTTy) |>.take regArgs))
          (hr : fn.rs = [d.retTy.toTTy]),
          liftDeclSpec (Δs d.name) d.params d.retTy (ha ▸ xs) mem (hr ▸ Q) X := by
  dsimp only [lcnfProgMod, Frontend.C0.tflatFnsToFns] at hfnMem
  rw [List.mem_map] at hfnMem
  obtain ⟨tf, htfMem, htfEq⟩ := hfnMem
  have hmapM := lowerModule_firstOrder_decls hfrag hlow
  obtain ⟨d0, hd0Mem, hd0Low⟩ := (mem_mapM_ok hmapM).2 tf htfMem
  rcases hspec with ⟨d, hdMem, hnm, ha, hr, hdl⟩
  have hsig0 := lowerDecl_sig hd0Low
  have heqName : mangleLc d0.name = mangleLc d.name := by
    calc mangleLc d0.name = tf.name := hsig0.1.symm
      _ = tf.toFn.name := rfl
      _ = fn.name := congrArg Fn.name htfEq
      _ = mangleLc d.name := hnm.symm
  have hdEq : d0 = d :=
    eq_of_map_eq_of_mem_nodup (fun x => mangleLc x.name)
      (inFirstOrderFragment_nodup_mangle hfrag) hd0Mem hdMem heqName
  subst hdEq
  exact ⟨d0, tf, hd0Mem, htfMem, htfEq, hd0Low,
    inFirstOrderFragment_decl_mem hfrag hd0Mem,
    find_name_eq_some_of_mem_nodup (inFirstOrderFragment_nodup_name hfrag) hd0Mem,
    ha.symm, hr.symm, hdl⟩

/-- Whole-module `ModuleOk` soundness for loop-free acyclic Phase-1 first-order modules
linked against `rtC0CoreMod`. -/
theorem lowerModule_moduleOk {m : LcModule} {progTfs : List Frontend.C0.TFlatFn}
    {Δ : HEnv}
    (hfrag : m.inFirstOrderFragment = true)
    (hlow : lowerModule m = .ok progTfs)
    (hacyc : (linkLcnfWithRtC0 progTfs).checkAcyclic = true)
    (hret : HEnv.RetTyped m Δ)
    (hmOk : HModuleOk Δ m)
    (hnoLoop : ∀ d ∈ m.decls, hasSelfTail d.name d.params.length d.body = false) :
    ModuleOk (linkRtC0Env (liftEnv m Δ)) (linkLcnfWithRtC0 progTfs) := by
  have hnodup := linkLcnfWithRtC0_nodup_of_checkAcyclic hacyc
  have hnotRt : ∀ d ∈ m.decls, ¬mangleLc d.name ∈ rtCoreFnNames :=
    fun d hd => not_rtCoreFnNames_of_decl hfrag hlow hnodup hd
  have hΓ : HCallEnvOk m Δ (linkRtC0Env (liftEnv m Δ)) := HCallEnvOk_linkRtC0Env hnotRt
  refine linkLcnfWithRtC0_moduleOk (liftEnv m Δ) hacyc (fun fn hfnMem xs mem Q X hspec => ?_)
  obtain ⟨d, tf, hdMem, _, rfl, hlowD, hdFo, _, ha, hr, hdl⟩ :=
    progFn_wp_from_decl hfrag hlow hfnMem hspec
  have hsig := lowerDecl_sig hlowD
  have hwp := lowerDecl_sound hfrag hΓ hret hdFo (hnoLoop d hdMem) hlowD
    (fun rt as σ Q' X' hinv hpm hs => hmOk d hdMem rt as σ Q' X' hinv hpm hs)
    hdl hsig.2.1 hsig.2.2
  exact func_wp_cast_roundtrip ha hr hwp

/-- Whole-module `ModuleOk` soundness for acyclic Phase-1 first-order modules including
self-tail loop declarations, proved via an indexed specification chain `HModuleOkIdx Δ m`. -/
theorem lowerModule_moduleOk_idx {m : LcModule} {progTfs : List Frontend.C0.TFlatFn}
    {Δ : Nat → HEnv}
    (hfrag : m.inFirstOrderFragment = true)
    (hlow : lowerModule m = .ok progTfs)
    (hacyc : (linkLcnfWithRtC0 progTfs).checkAcyclic = true)
    (hret : ∀ j, HEnv.RetTyped m (Δ j))
    (hmOk : HModuleOkIdx Δ m)
    (k : Nat) :
    ModuleOk (linkRtC0Env (liftEnv m (Δ k))) (linkLcnfWithRtC0 progTfs) := by
  have hnodup := linkLcnfWithRtC0_nodup_of_checkAcyclic hacyc
  have hnotRt : ∀ d ∈ m.decls, ¬mangleLc d.name ∈ rtCoreFnNames :=
    fun d hd => not_rtCoreFnNames_of_decl hfrag hlow hnodup hd
  have hΓk : HCallEnvOk m (Δ k) (linkRtC0Env (liftEnv m (Δ k))) := HCallEnvOk_linkRtC0Env hnotRt
  have hΓlt : ∀ j, j < k → HCallEnvOk m (Δ j) (linkRtC0Env (liftEnv m (Δ k))) := fun j hj =>
    HCallEnvOk_env_mono (HEnv.le_of_step hmOk.1 (Nat.le_of_lt hj)) hΓk
  refine linkLcnfWithRtC0_moduleOk (liftEnv m (Δ k)) hacyc
    (fun fn hfnMem xs mem Q X hspec => ?_)
  obtain ⟨d, tf, hdMem, _, rfl, hlowD, hdFo, hfind, ha, hr, hdl⟩ :=
    progFn_wp_from_decl hfrag hlow hfnMem hspec
  have hsig := lowerDecl_sig hlowD
  cases hself : hasSelfTail d.name d.params.length d.body with
  | false =>
    cases k with
    | zero =>
      have hΓ0 : HCallEnvOk m HEnv.bot (linkRtC0Env (liftEnv m (Δ 0))) :=
        HCallEnvOk_bot hΓk.2
      have hwp := lowerDecl_sound_spec hfrag hΓ0 (HEnv.RetTyped_bot m) hdFo hself hlowD
        (fun rt as σ Q' X' hinv hpm hs => hmOk.2 0 d hdMem rt as σ Q' X' hinv hpm hs)
        hdl hsig.2.1 hsig.2.2
      exact func_wp_cast_roundtrip ha hr hwp
    | succ k' =>
      have hΓ' := hΓlt k' (Nat.lt_succ_self k')
      have hwp := lowerDecl_sound_spec hfrag hΓ' (hret k') hdFo hself hlowD
        (fun rt as σ Q' X' hinv hpm hs => hmOk.2 (k' + 1) d hdMem rt as σ Q' X' hinv hpm hs)
        hdl hsig.2.1 hsig.2.2
      exact func_wp_cast_roundtrip ha hr hwp
  | true =>
    have hwp := lowerDecl_sound_loop hfrag hΓk.2 hΓlt (fun j _ => hret j)
      hdFo hfind hself hlowD
      (fun j _ rt as σ Q' X' hinv hpm hs => hmOk.2 j d hdMem rt as σ Q' X' hinv hpm hs)
      hdl hsig.2.1 hsig.2.2
    exact func_wp_cast_roundtrip ha hr hwp

/-- Indexed environment family used by `lowerModule_moduleSccOk`: indices `0 .. rtLen - 1`
expose the acyclic `rtC0CoreMod` prefix and indices `rtLen + k` expose `Δ k` alongside
the runtime. -/
@[expose] def lowerSccRecEnv (m : LcModule) (Δ : Nat → HEnv) (i : Nat) : Env :=
  if i < rtC0CoreMod.fns.length then
    rtC0CoreEnv.restrict ((rtC0CoreMod.fns.take (i + 1)).map Fn.sig)
  else
    linkRtC0Env (liftEnv m (Δ (i - rtC0CoreMod.fns.length)))

private theorem rtCoreCallEnv_le_sccStep {m : LcModule}
    {progTfs : List Frontend.C0.TFlatFn} {Δ : Nat → HEnv} {Γ : Env} {k : Nat}
    (hRec : ∀ g ∈ (linkLcnfWithRtC0 progTfs).fns, ∀ i' < rtC0CoreMod.fns.length + k,
      ∀ {xs : Tup Val g.as} {mem : Mem 64} {Q : Post g.rs} {X : XPost},
        lowerSccRecEnv m Δ i' g.name g.as g.rs xs mem Q X → Γ g.name g.as g.rs xs mem Q X) :
    rtCoreCallEnv.le Γ := by
  intro f as rs xs mem Q X ⟨hsig, hcore⟩
  have hall := (List.all_eq_true.mp rtCoreCallSigs_subset_rtC0CoreMod_sigs) (f, as, rs) hsig
  have hmemSig : (f, as, rs) ∈ rtC0CoreMod.fns.map Fn.sig := decide_eq_true_iff.mp hall
  rw [List.mem_map] at hmemSig
  obtain ⟨g, hgMem, hgSig⟩ := hmemSig
  have hgPosLt : posFn rtC0CoreMod.fns g < rtC0CoreMod.fns.length := posFn_lt_length hgMem
  have hgInTake : g ∈ rtC0CoreMod.fns.take (posFn rtC0CoreMod.fns g + 1) :=
    mem_take_succ_posFn rtC0CoreMod_fns_names_nodup hgMem
  have hgRec : lowerSccRecEnv m Δ (posFn rtC0CoreMod.fns g) g.name g.as g.rs
      (by cases hgSig; exact xs) mem (by cases hgSig; exact Q) X := by
    simp only [lowerSccRecEnv, hgPosLt, ↓reduceIte, Env.restrict]
    refine ⟨List.mem_map_of_mem hgInTake, ?_⟩
    cases hgSig; exact hcore
  have hgLinked : g ∈ (linkLcnfWithRtC0 progTfs).fns := by
    rw [linkLcnfWithRtC0_fns_eq]; exact List.mem_append_left _ hgMem
  have hres := hRec g hgLinked (posFn rtC0CoreMod.fns g) (by omega) hgRec
  cases hgSig; exact hres

private theorem liftEnv_le_sccStep {m : LcModule}
    {progTfs : List Frontend.C0.TFlatFn} {Δ : Nat → HEnv} {Γ : Env} {j k : Nat}
    (hfrag : m.inFirstOrderFragment = true)
    (hlow : lowerModule m = .ok progTfs)
    (hnodup : (linkLcnfWithRtC0 progTfs).namesNodup)
    (hjk : j < k)
    (hRec : ∀ g ∈ (linkLcnfWithRtC0 progTfs).fns, ∀ i' < rtC0CoreMod.fns.length + k,
      ∀ {xs : Tup Val g.as} {mem : Mem 64} {Q : Post g.rs} {X : XPost},
        lowerSccRecEnv m Δ i' g.name g.as g.rs xs mem Q X → Γ g.name g.as g.rs xs mem Q X) :
    (liftEnv m (Δ j)).le Γ := by
  intro sym as rs xs mem Q X hspec
  rcases hspec with ⟨d, hdMem, hnm, ha, hr, hdl⟩
  have hmapM := lowerModule_firstOrder_decls hfrag hlow
  obtain ⟨tf, htfMem, htfOk⟩ := (mem_mapM_ok hmapM).1 d hdMem
  have hsig := lowerDecl_sig htfOk
  have hfnMem : tf.toFn ∈ (linkLcnfWithRtC0 progTfs).fns := tflatFn_toFn_mem_linked htfMem
  have hnotRt : ¬tf.toFn.name ∈ rtCoreFnNames := by
    change ¬tf.name ∈ rtCoreFnNames
    rw [hsig.1]; exact not_rtCoreFnNames_of_decl hfrag hlow hnodup hdMem
  have hasEq : tf.toFn.as = as := Eq.trans hsig.2.1 ha
  have hrsEq : tf.toFn.rs = rs := Eq.trans hsig.2.2 hr
  have hnmEq : tf.toFn.name = sym := hsig.1.trans hnm
  have hrecSpec : lowerSccRecEnv m Δ (rtC0CoreMod.fns.length + j)
      tf.toFn.name tf.toFn.as tf.toFn.rs (hasEq ▸ xs) mem (hrsEq ▸ Q) X := by
    have hnotLt : ¬(rtC0CoreMod.fns.length + j < rtC0CoreMod.fns.length) := by omega
    simp only [lowerSccRecEnv, hnotLt, ↓reduceIte, Nat.add_sub_cancel_left]
    rw [linkRtC0Env_prog _ hnotRt]
    have hspecSub : liftEnv m (Δ j) tf.toFn.name tf.toFn.as tf.toFn.rs
        (hasEq ▸ xs) mem (hrsEq ▸ Q) X := by
      refine ⟨d, hdMem, hsig.1.symm, hsig.2.1.symm, hsig.2.2.symm, ?_⟩
      subst hasEq; subst hrsEq; exact hdl
    exact hspecSub
  have hres := hRec tf.toFn hfnMem (rtC0CoreMod.fns.length + j) (by omega) hrecSpec
  subst hnmEq; subst hasEq; subst hrsEq
  exact hres

/-- Whole-module `LinkScc.ModuleSccOk` soundness for arbitrary cyclic/mutually-recursive
Phase-1 first-order modules linked against `rtC0CoreMod`. -/
theorem lowerModule_moduleSccOk {m : LcModule}
    {progTfs : List Frontend.C0.TFlatFn} {Δ : Nat → HEnv}
    (hfrag : m.inFirstOrderFragment = true)
    (hlow : lowerModule m = .ok progTfs)
    (hcyc : LinkRec.checkCyclic (linkLcnfWithRtC0 progTfs) = true)
    (hret : ∀ k, HEnv.RetTyped m (Δ k))
    (hmOk : HModuleOkIdx Δ m)
    (Γext : Env := fun _ _ _ _ _ _ _ => False) :
    LinkScc.ModuleSccOk LinkScc.natRecIdx (lowerSccRecEnv m Δ) Γext false
      (linkLcnfWithRtC0 progTfs) := by
  have hnodup : (linkLcnfWithRtC0 progTfs).namesNodup := by
    simp only [LinkRec.checkCyclic, Bool.and_eq_true] at hcyc
    exact Module.namesNodup_of_checkNamesNodup hcyc.1
  refine LinkScc.moduleSccOk_of_step LinkScc.natRecIdx hcyc
    (linkLcnfWithRtC0_fns_wf progTfs) (fun i fn hfnMem Γ hRec _ xs mem Q X hspec => ?_)
  have hRec' : ∀ g ∈ (linkLcnfWithRtC0 progTfs).fns, ∀ i' < i,
      ∀ {xs' : Tup Val g.as} {m' : Mem 64} {Q' : Post g.rs} {X' : XPost},
        lowerSccRecEnv m Δ i' g.name g.as g.rs xs' m' Q' X' →
          Γ g.name g.as g.rs xs' m' Q' X' :=
    fun g hgMem i' hlt _ _ _ _ hs => hRec g hgMem i' hlt (Or.inl rfl) _ _ _ _ hs
  rw [linkLcnfWithRtC0_fns_eq] at hfnMem
  rcases List.mem_append.mp hfnMem with hrtMem | hprogMem
  · have hpLt : posFn rtC0CoreMod.fns fn < rtC0CoreMod.fns.length := posFn_lt_length hrtMem
    by_cases hip : i < posFn rtC0CoreMod.fns fn
    · have hiRt : i < rtC0CoreMod.fns.length := Nat.lt_trans hip hpLt
      simp only [lowerSccRecEnv, hiRt, ↓reduceIte, Env.restrict] at hspec
      obtain ⟨hsigMem, _⟩ := hspec
      rw [List.mem_map] at hsigMem
      obtain ⟨g, hgTake, hgSig⟩ := hsigMem
      have hnmTake : fn.name ∈ (rtC0CoreMod.fns.take (i + 1)).map Fn.name := by
        rw [List.mem_map]
        exact ⟨g, hgTake, congrArg Prod.fst hgSig⟩
      exact absurd hnmTake (not_mem_take_of_lt_posFn hrtMem hip)
    · have hpi : posFn rtC0CoreMod.fns fn ≤ i := Nat.le_of_not_lt hip
      have hspecCore : rtC0CoreEnv fn.name fn.as fn.rs xs mem Q X := by
        by_cases hiRt : i < rtC0CoreMod.fns.length
        · simp only [lowerSccRecEnv, hiRt, ↓reduceIte, Env.restrict] at hspec
          exact hspec.2
        · simp only [lowerSccRecEnv, hiRt, ↓reduceIte] at hspec
          have hnmRt : fn.name ∈ rtCoreFnNames := List.mem_map_of_mem hrtMem
          exact (linkRtC0Env_rt _ hnmRt).mp hspec
      have hsplit := split_at_posFn rtC0CoreMod_fns_names_nodup hrtMem
      have hwpRestr := rtC0CoreMod_moduleOk.wp_restrict hsplit hspecCore
      dsimp only [Func.wp] at hwpRestr ⊢
      refine wp_env_mono (fun g as bs xs' m' P E hrestr => ?_) (fn.body Val Cont xs) mem hwpRestr
      dsimp only [Env.restrict] at hrestr
      obtain ⟨hsigMem, hcore⟩ := hrestr
      have hsigEmpty : (rtC0CoreMod.externs.map Extern.sig) = [] := rfl
      rw [hsigEmpty, List.append_nil, List.mem_map] at hsigMem
      obtain ⟨gfn, hgPre, hgSig⟩ := hsigMem
      obtain ⟨hgRt, hgPosLt⟩ := mem_take_posFn_lt rtC0CoreMod_fns_names_nodup hgPre
      have hgPosLen : posFn rtC0CoreMod.fns gfn < rtC0CoreMod.fns.length :=
        posFn_lt_length hgRt
      have hgInTake : gfn ∈ rtC0CoreMod.fns.take (posFn rtC0CoreMod.fns gfn + 1) :=
        mem_take_succ_posFn rtC0CoreMod_fns_names_nodup hgRt
      have hrecSpec : lowerSccRecEnv m Δ (posFn rtC0CoreMod.fns gfn)
          gfn.name gfn.as gfn.rs
          (by cases hgSig; exact xs') m' (by cases hgSig; exact P) E := by
        simp only [lowerSccRecEnv, hgPosLen, ↓reduceIte, Env.restrict]
        refine ⟨List.mem_map_of_mem hgInTake, ?_⟩
        cases hgSig; exact hcore
      have hgLinked : gfn ∈ (linkLcnfWithRtC0 progTfs).fns := by
        rw [linkLcnfWithRtC0_fns_eq]; exact List.mem_append_left _ hgRt
      have hres := hRec' gfn hgLinked (posFn rtC0CoreMod.fns gfn)
        (Nat.lt_of_lt_of_le hgPosLt hpi) hrecSpec
      cases hgSig; exact hres
  · by_cases hiRt : i < rtC0CoreMod.fns.length
    · simp only [lowerSccRecEnv, hiRt, ↓reduceIte, Env.restrict] at hspec
      obtain ⟨hsigMem, _⟩ := hspec
      rw [List.mem_map] at hsigMem
      obtain ⟨g, hgTake, hgSig⟩ := hsigMem
      have hgRt : g ∈ rtC0CoreMod.fns := List.mem_of_mem_take hgTake
      have hnmEq : g.name = fn.name := congrArg Prod.fst hgSig
      have hnmRt : fn.name ∈ rtCoreFnNames := by
        change fn.name ∈ rtC0CoreMod.fns.map Fn.name
        rw [← hnmEq]
        exact List.mem_map_of_mem hgRt
      exact absurd hnmRt (lcnfProgMod_disjoint_rt_of_nodup hnodup fn hprogMem)
    · let k := i - rtC0CoreMod.fns.length
      simp only [lowerSccRecEnv, hiRt, ↓reduceIte] at hspec
      have hdisj : ¬fn.name ∈ rtCoreFnNames := lcnfProgMod_disjoint_rt_of_nodup hnodup fn hprogMem
      have hspecLift : liftEnv m (Δ k) fn.name fn.as fn.rs xs mem Q X :=
        (linkRtC0Env_prog _ hdisj).mp hspec
      have hRecK : ∀ g ∈ (linkLcnfWithRtC0 progTfs).fns, ∀ i' < rtC0CoreMod.fns.length + k,
          ∀ {xs' : Tup Val g.as} {m' : Mem 64} {Q' : Post g.rs} {X' : XPost},
            lowerSccRecEnv m Δ i' g.name g.as g.rs xs' m' Q' X' →
              Γ g.name g.as g.rs xs' m' Q' X' := by
        intro g hgMem i' hlt _ _ _ _ hs
        exact hRec' g hgMem i' (by omega) hs
      have hrtΓ : rtCoreCallEnv.le Γ := rtCoreCallEnv_le_sccStep hRecK
      have hΓlt : ∀ j, j < k → HCallEnvOk m (Δ j) Γ := fun j hj =>
        ⟨liftEnv_le_sccStep hfrag hlow hnodup hj hRecK, hrtΓ⟩
      obtain ⟨d, tf, hdMem, _, rfl, hlowD, hdFo, hfind, ha, hr, hdl⟩ :=
        progFn_wp_from_decl hfrag hlow hprogMem hspecLift
      have hsig := lowerDecl_sig hlowD
      cases hself : hasSelfTail d.name d.params.length d.body with
      | false =>
        cases hk : k with
        | zero =>
          have hdl0 : liftDeclSpec (Δ 0 d.name) d.params d.retTy (ha ▸ xs) mem (hr ▸ Q) X := by
            rw [← hk]; exact hdl
          have hΓ0 : HCallEnvOk m HEnv.bot Γ := HCallEnvOk_bot hrtΓ
          have hwp := lowerDecl_sound_spec hfrag hΓ0 (HEnv.RetTyped_bot m) hdFo hself hlowD
            (fun rt as σ Q' X' hinv hpm hs => hmOk.2 0 d hdMem rt as σ Q' X' hinv hpm hs)
            hdl0 hsig.2.1 hsig.2.2
          exact func_wp_cast_roundtrip ha hr hwp
        | succ k' =>
          have hΓ' := hΓlt k' (by omega)
          have hdlSucc : liftDeclSpec (Δ (k' + 1) d.name) d.params d.retTy
              (ha ▸ xs) mem (hr ▸ Q) X := by
            rw [← hk]; exact hdl
          have hwp := lowerDecl_sound_spec hfrag hΓ' (hret k') hdFo hself hlowD
            (fun rt as σ Q' X' hinv hpm hs =>
              hmOk.2 (k' + 1) d hdMem rt as σ Q' X' hinv hpm hs)
            hdlSucc hsig.2.1 hsig.2.2
          exact func_wp_cast_roundtrip ha hr hwp
      | true =>
        have hwp := lowerDecl_sound_loop hfrag hrtΓ hΓlt (fun j _ => hret j)
          hdFo hfind hself hlowD
          (fun j _ rt as σ Q' X' hinv hpm hs => hmOk.2 j d hdMem rt as σ Q' X' hinv hpm hs)
          hdl hsig.2.1 hsig.2.2
        exact func_wp_cast_roundtrip ha hr hwp

/-- Fixed-point `Env.semScc` soundness for arbitrary cyclic/mutually-recursive Phase-1
first-order modules linked against `rtC0CoreMod`. -/
theorem lowerModule_semScc {m : LcModule}
    {progTfs : List Frontend.C0.TFlatFn} {Δ : Nat → HEnv}
    (hfrag : m.inFirstOrderFragment = true)
    (hlow : lowerModule m = .ok progTfs)
    (hcyc : LinkRec.checkCyclic (linkLcnfWithRtC0 progTfs) = true)
    (hret : ∀ k, HEnv.RetTyped m (Δ k))
    (hmOk : HModuleOkIdx Δ m)
    (Γext : Env := fun _ _ _ _ _ _ _ => False) :
    (∀ k, HCallEnvOk m (Δ k) (Env.semScc (linkLcnfWithRtC0 progTfs) Γext)) ∧
      (∀ d ∈ m.decls, ∀ tf ∈ progTfs, lowerDecl (firstOrderLEnv m) d = .ok tf →
        ∀ k xs mem Q X,
          liftDeclSpec (Δ k d.name) d.params d.retTy xs mem Q X →
          ∀ (ha : tf.toFn.as = i64 :: (d.params.map (·.ty.toTTy) |>.take regArgs))
            (hr : tf.toFn.rs = [d.retTy.toTTy]),
            Func.wp (Env.semScc (linkLcnfWithRtC0 progTfs) Γext) tf.toFn.body
              (ha ▸ xs) mem (hr ▸ Q) X) := by
  have hsccOk := lowerModule_moduleSccOk hfrag hlow hcyc hret hmOk Γext
  have hle := moduleSccOk_le_semScc hsccOk
  have hnodup : (linkLcnfWithRtC0 progTfs).namesNodup := by
    simp only [LinkRec.checkCyclic, Bool.and_eq_true] at hcyc
    exact Module.namesNodup_of_checkNamesNodup hcyc.1
  have hmapM := lowerModule_firstOrder_decls hfrag hlow
  have hΓ : ∀ k, HCallEnvOk m (Δ k) (Env.semScc (linkLcnfWithRtC0 progTfs) Γext) := by
    intro k
    refine ⟨?_, ?_⟩
    · intro sym as rs xs mem Q X hspec
      rcases hspec with ⟨d, hdMem, hnm, ha, hr, hdl⟩
      obtain ⟨tf, htfMem, htfOk⟩ := (mem_mapM_ok hmapM).1 d hdMem
      have hsig := lowerDecl_sig htfOk
      have hnotRt : ¬mangleLc d.name ∈ rtCoreFnNames :=
        not_rtCoreFnNames_of_decl hfrag hlow hnodup hdMem
      have hfnMem : tf.toFn ∈ (linkLcnfWithRtC0 progTfs).fns := tflatFn_toFn_mem_linked htfMem
      have hasEq : tf.toFn.as = as := hsig.2.1.trans ha
      have hrsEq : tf.toFn.rs = rs := hsig.2.2.trans hr
      have hsigMem : (sym, as, rs) ∈ (linkLcnfWithRtC0 progTfs).fns.map Fn.sig := by
        rw [List.mem_map]
        refine ⟨tf.toFn, hfnMem, ?_⟩
        change (tf.toFn.name, tf.toFn.as, tf.toFn.rs) = (sym, as, rs)
        rw [hasEq, hrsEq]
        change (tf.name, as, rs) = (sym, as, rs)
        rw [hsig.1, hnm]
      refine hle (rtC0CoreMod.fns.length + k) sym as rs xs mem Q X ⟨hsigMem, ?_⟩
      have hnotLt : ¬(rtC0CoreMod.fns.length + k < rtC0CoreMod.fns.length) := by omega
      simp only [lowerSccRecEnv, hnotLt, ↓reduceIte, Nat.add_sub_cancel_left]
      rw [← hnm]
      exact (linkRtC0Env_prog _ hnotRt).mpr ⟨d, hdMem, rfl, ha, hr, hdl⟩
    · intro f as rs xs mem Q X ⟨hsig, hcore⟩
      have hall := (List.all_eq_true.mp rtCoreCallSigs_subset_rtC0CoreMod_sigs) (f, as, rs) hsig
      have hmemSig : (f, as, rs) ∈ rtC0CoreMod.fns.map Fn.sig := decide_eq_true_iff.mp hall
      rw [List.mem_map] at hmemSig
      obtain ⟨g, hgMem, hgSig⟩ := hmemSig
      have hgPosLt : posFn rtC0CoreMod.fns g < rtC0CoreMod.fns.length := posFn_lt_length hgMem
      have hgInTake : g ∈ rtC0CoreMod.fns.take (posFn rtC0CoreMod.fns g + 1) :=
        mem_take_succ_posFn rtC0CoreMod_fns_names_nodup hgMem
      have hgLinked : g ∈ (linkLcnfWithRtC0 progTfs).fns := by
        rw [linkLcnfWithRtC0_fns_eq]; exact List.mem_append_left _ hgMem
      have hsigM : (f, as, rs) ∈ (linkLcnfWithRtC0 progTfs).fns.map Fn.sig := by
        rw [List.mem_map]
        exact ⟨g, hgLinked, hgSig⟩
      refine hle (posFn rtC0CoreMod.fns g) f as rs xs mem Q X ⟨hsigM, ?_⟩
      simp only [lowerSccRecEnv, hgPosLt, ↓reduceIte, Env.restrict]
      rw [← hgSig]
      exact ⟨List.mem_map_of_mem hgInTake, by cases hgSig; exact hcore⟩
  refine ⟨hΓ, fun d hdMem tf _ hlowD k xs mem Q X hspec ha hr => ?_⟩
  have hdFo := inFirstOrderFragment_decl_mem hfrag hdMem
  have hfind := find_name_eq_some_of_mem_nodup (inFirstOrderFragment_nodup_name hfrag) hdMem
  cases hself : hasSelfTail d.name d.params.length d.body with
  | false =>
    cases k with
    | zero =>
      have hΓ0 : HCallEnvOk m HEnv.bot (Env.semScc (linkLcnfWithRtC0 progTfs) Γext) :=
        HCallEnvOk_bot (hΓ 0).2
      exact lowerDecl_sound_spec hfrag hΓ0 (HEnv.RetTyped_bot m) hdFo hself hlowD
        (fun rt as σ Q' X' hinv hpm hs => hmOk.2 0 d hdMem rt as σ Q' X' hinv hpm hs)
        hspec ha hr
    | succ k' =>
      exact lowerDecl_sound_spec hfrag (hΓ k') (hret k') hdFo hself hlowD
        (fun rt as σ Q' X' hinv hpm hs => hmOk.2 (k' + 1) d hdMem rt as σ Q' X' hinv hpm hs)
        hspec ha hr
  | true =>
    exact lowerDecl_sound_loop hfrag (hΓ k).2 (fun j _ => hΓ j) (fun j _ => hret j)
      hdFo hfind hself hlowD
      (fun j _ rt as σ Q' X' hinv hpm hs => hmOk.2 j d hdMem rt as σ Q' X' hinv hpm hs)
      hspec ha hr

end LeanQbe.T.LeanLCNF.Sem
