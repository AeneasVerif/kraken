module

public import LeanQbe.T.MainLemmas
import LeanQbe.T.RegaLemmas

/-!
# Shared Linking, Label-Uniqueness, Loop, & TargetInit Utilities (`LinkUtil`)

Pure, non-`MainLemmas`-modifying utilities shared across `MainLinkScc`, `MainCertProof`,
and `MainCertScc`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## 1. List, Boolean, Infix, & Signature Helpers -/

theorem nodup_getElem?_inj {α : Type _} : ∀ {xs : List α} {i j : Nat} {x : α},
    xs.Nodup → xs[i]? = some x → xs[j]? = some x → i = j
  | [], _, _, _, _, hi, _ => by simp at hi
  | _ :: _, 0, 0, _, _, _, _ => rfl
  | _ :: _, 0, _ + 1, _, hnd, hi, hj => by
      simp only [List.nodup_cons, List.getElem?_cons_zero, Option.some.injEq] at hnd hi
      exact absurd (hi ▸ List.mem_of_getElem? hj) hnd.1
  | _ :: _, _ + 1, 0, _, hnd, hi, hj => by
      simp only [List.nodup_cons, List.getElem?_cons_zero, Option.some.injEq] at hnd hj
      exact absurd (hj ▸ List.mem_of_getElem? hi) hnd.1
  | _ :: _, i + 1, j + 1, _, hnd, hi, hj =>
      congrArg Nat.succ (nodup_getElem?_inj (List.nodup_cons.mp hnd).2 hi hj)

theorem list_isInfixAt_trans {α : Type _} {a b c : List α} {k₁ k₂ : Nat}
    (hk1 : k₁ ≤ b.length) (h1 : a.IsInfixAt b k₁) (h2 : b.IsInfixAt c k₂) :
    a.IsInfixAt c (k₂ + k₁) := by
  obtain ⟨t1, ht1⟩ := h1; obtain ⟨t2, ht2⟩ := h2
  refine ⟨t1 ++ t2, ?_⟩
  have hd : (b ++ t2).drop k₁ = b.drop k₁ ++ t2 := by
    rw [List.drop_append, show k₁ - b.length = 0 by omega, List.drop_zero]
  rw [← List.drop_drop, ← ht2, hd, ← ht1, List.append_assoc]

theorem list_find?_pred {α : Type _} {p : α → Bool} :
    ∀ {xs : List α} {x : α}, xs.find? p = some x → p x = true
  | [], _, h => by simp at h
  | y :: _, _, h => by
      simp only [List.find?] at h
      cases hp : p y with
      | true => simp [hp] at h; subst h; exact hp
      | false => simp [hp] at h; exact list_find?_pred h

theorem bool_not_eq_false {p : Bool} (h : (!p) = true) : p = false := by
  cases p <;> simp at h ⊢

theorem mem_unique_fst_sig : ∀ {xs : List SigEntry}, (xs.map Prod.fst).Nodup →
    ∀ {f as₁ bs₁ as₂ bs₂}, (f, as₁, bs₁) ∈ xs → (f, as₂, bs₂) ∈ xs → as₁ = as₂ ∧ bs₁ = bs₂
  | [], _, _, _, _, _, _, h, _ => nomatch h
  | (_, _, _) :: _, hnd, _, _, _, _, _, h1, h2 => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
      rcases List.mem_cons.mp h1 with e1 | h1 <;> rcases List.mem_cons.mp h2 with e2 | h2
      · cases e1; cases e2; exact ⟨rfl, rfl⟩
      · cases e1; exact absurd rfl (hnd.1 _ h2)
      · cases e2; exact absurd rfl (hnd.1 _ h1)
      · exact mem_unique_fst_sig hnd.2 h1 h2

theorem fn_name_not_mem_externs_mod {M : Module} (hnd : M.namesNodup)
    {fn : Fn} (hfn : fn ∈ M.fns) {as bs : List Ty} :
    (fn.name, as, bs) ∉ M.externs.map Extern.sig := by
  intro hex
  obtain ⟨ex, hexm, heq⟩ := List.mem_map.mp hex
  exact (List.nodup_append.mp hnd).2.2 fn.name (List.mem_map_of_mem hfn) ex.name
    (List.mem_map_of_mem hexm) (congrArg Prod.fst heq).symm

/-! ## 2. Shared Label-Uniqueness Proofs -/

theorem compile_code_labels {T : Target} (hcl : Rega.LabelClean T.toIsa) (lt : LegalTarget) :
    ∀ {fs : List Fn} {hints : List T.toIsa.Hints} {code : List T.Directive},
      compile T.toIsa lt fs hints = .ok code →
      (fs.map Fn.name).Nodup → fs.all (fun f => fnNameOk f.name) = true →
      (∀ (i : Nat) (l : Sym), code[i]? = some (T.frame.label l) →
        ∃ f ∈ fs, l = f.name ∨ ∃ a, l = Rega.lname f.name a) ∧
      (∀ (i j : Nat) (l : Sym), code[i]? = some (T.frame.label l) →
        code[j]? = some (T.frame.label l) → i = j)
  | [], [], _, hcm, _, _ => by
      dsimp only [compile] at hcm; simp only [Except.ok.injEq] at hcm; subst hcm
      exact ⟨fun _ _ hi => by simp at hi, fun _ _ _ hi => by simp at hi⟩
  | [], _ :: _, _, hcm, _, _ | _ :: _, [], _, hcm, _, _ => by
      dsimp only [compile] at hcm; cases hcm
  | f :: fs, h :: hs, code, hcm, hnd, hok => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
      simp only [List.all_cons, Bool.and_eq_true] at hok; dsimp only [compile] at hcm
      split at hcm
      · rename_i c cs hl hrest
        simp only [Except.ok.injEq] at hcm; subst hcm
        obtain ⟨ih_mem, ih_uniq⟩ := compile_code_labels hcl lt hrest hnd.2 hok.2
        have hc_mem : ∀ (i : Nat) (l : Sym), c[i]? = some (T.frame.label l) →
            l = f.name ∨ ∃ a, l = Rega.lname f.name a :=
          fun i l hi => Rega.lowerFn_label_mem hcl hl hi
        have hc_uniq := Rega.lowerFn_labelsUnique hcl hl
        constructor
        · intro i l hi
          by_cases hlt : i < c.length
          · rw [List.getElem?_append_left hlt] at hi; exact ⟨f, List.mem_cons_self, hc_mem i l hi⟩
          · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hi
            obtain ⟨g, hg, hl'⟩ := ih_mem (i - c.length) l hi
            exact ⟨g, List.mem_cons_of_mem f hg, hl'⟩
        · intro i j l hi hj
          have disj : ∀ {i₁ j₁ : Nat}, c[i₁]? = some (T.frame.label l) →
              cs[j₁]? = some (T.frame.label l) → False := by
            intro i₁ j₁ hi₁ hj₁; obtain ⟨g, hg, hlg⟩ := ih_mem j₁ l hj₁
            have hgok := List.all_eq_true.mp hok.2 g hg
            rcases hc_mem i₁ l hi₁ with rfl | ⟨a, rfl⟩ <;> rcases hlg with hgl | ⟨b, hgl⟩
            · exact hnd.1 g hg hgl.symm
            · exact lname_ne_cross hok.1 hgl.symm
            · exact lname_ne_cross hgok hgl
            · exact hnd.1 g hg (lname_inj_cross hok.1 hgok hgl).1.symm
          by_cases hic : i < c.length <;> by_cases hjc : j < c.length
          · rw [List.getElem?_append_left hic] at hi; rw [List.getElem?_append_left hjc] at hj
            exact hc_uniq i j l hi hj
          · rw [List.getElem?_append_left hic] at hi
            rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
            exact absurd hi (fun h' => disj h' hj)
          · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
            rw [List.getElem?_append_left hjc] at hj; exact absurd hj (fun h' => disj h' hi)
          · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
            rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
            have heq := ih_uniq (i - c.length) (j - c.length) l hi hj; omega
      · simp at hcm
      · simp at hcm

theorem append_exits_labelsUnique {T : Target} (hcl : Rega.LabelClean T.toIsa)
    {fs : List Fn} {exits : List Sym} {code : List T.Directive}
    (hmem : ∀ (i : Nat) (l : Sym), code[i]? = some (T.frame.label l) →
      ∃ f ∈ fs, l = f.name ∨ ∃ a, l = Rega.lname f.name a)
    (huniq : ∀ (i j : Nat) (l : Sym), code[i]? = some (T.frame.label l) →
      code[j]? = some (T.frame.label l) → i = j)
    (hnd : (fs.map Fn.name ++ exits).Nodup)
    (hok : (fs.map Fn.name ++ exits).all fnNameOk = true) :
    ∀ (i j : Nat) (l : Sym),
      (code ++ exits.map T.frame.label)[i]? = some (T.frame.label l) →
      (code ++ exits.map T.frame.label)[j]? = some (T.frame.label l) → i = j := by
  have hnd_split := List.nodup_append.mp hnd
  simp only [List.all_append, Bool.and_eq_true, List.all_map] at hok
  have hEx : ∀ (k : Nat) (l : Sym),
      (exits.map T.frame.label)[k]? = some (T.frame.label l) → exits[k]? = some l := by
    intro k l hk; rw [List.getElem?_map] at hk
    cases hx : exits[k]? with
    | none => simp [hx] at hk
    | some e => simp only [hx, Option.map_some, Option.some.injEq] at hk; rw [hcl.label_inj e l hk]
  have hdisj : ∀ (i₁ k₂ : Nat) (l : Sym), code[i₁]? = some (T.frame.label l) →
      (exits.map T.frame.label)[k₂]? = some (T.frame.label l) → False := by
    intro i₁ k₂ l hi₁ hk₂
    have hmemE := List.mem_of_getElem? (hEx k₂ l hk₂)
    obtain ⟨f, hf, hlf⟩ := hmem i₁ l hi₁
    rcases hlf with rfl | ⟨_, rfl⟩
    · exact hnd_split.2.2 f.name (List.mem_map_of_mem hf) f.name hmemE rfl
    · exact lname_ne_cross (List.all_eq_true.mp hok.2 _ hmemE) rfl
  intro i j l hi hj
  by_cases hic : i < code.length <;> by_cases hjc : j < code.length
  · rw [List.getElem?_append_left hic] at hi; rw [List.getElem?_append_left hjc] at hj
    exact huniq i j l hi hj
  · rw [List.getElem?_append_left hic] at hi
    rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
    exact absurd hi (fun h' => hdisj i (j - code.length) l h' hj)
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
    rw [List.getElem?_append_left hjc] at hj
    exact absurd hj (fun h' => hdisj j (i - code.length) l h' hi)
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
    rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
    have heq := nodup_getElem?_inj hnd_split.2.1 (hEx _ _ hi) (hEx _ _ hj); omega

theorem compile_labelsUnique {T : Target} (hcl : Rega.LabelClean T.toIsa) {lt : LegalTarget}
    {fs : List Fn} {hints : List T.toIsa.Hints} {exits : List Sym} {code : List T.Directive}
    (hcm : compile T.toIsa lt fs hints = .ok code) (hnd : (fs.map Fn.name ++ exits).Nodup)
    (hok : (fs.map Fn.name ++ exits).all fnNameOk = true) :
    ∀ (i j : Nat) (l : Sym),
      (code ++ exits.map T.frame.label)[i]? = some (T.frame.label l) →
      (code ++ exits.map T.frame.label)[j]? = some (T.frame.label l) → i = j := by
  have hok_fns : fs.all (fun f => fnNameOk f.name) = true := by
    simp only [List.all_append, Bool.and_eq_true, List.all_map] at hok; exact hok.1
  obtain ⟨hmem, huniq⟩ := compile_code_labels hcl lt hcm (List.nodup_append.mp hnd).1 hok_fns
  exact append_exits_labelsUnique hcl hmem huniq hnd hok

/-! ## 3. Monoidal Sequential Compiler-Loop Engine (`compileSeqLoop`) -/

@[expose] def compileSeqLoop {α β : Type _} {I : Isa} (unit : β) (combine : β → β → β)
    (step : α → I.Hints → Except String (List I.Directive × β)) (errMismatch : String) :
    List α → List I.Hints → Except String (List I.Directive × β)
  | [], [] => .ok ([], unit)
  | x :: xs, h :: hs =>
      match step x h with
      | .ok (c, v) =>
          match compileSeqLoop unit combine step errMismatch xs hs with
          | .ok (cs, vrest) => .ok (c ++ cs, combine v vrest)
          | .error e => .error e
      | .error e => .error e
  | _, _ => .error errMismatch

theorem compileSeqLoop_append {α β : Type _} {I : Isa} {unit : β} {combine : β → β → β}
    (hunit : ∀ b, combine unit b = b)
    (hassoc : ∀ a b c, combine (combine a b) c = combine a (combine b c))
    {step : α → I.Hints → Except String (List I.Directive × β)} {err : String} :
    ∀ {xs₁ xs₂ : List α} {hs₁ hs₂ : List I.Hints} {c₁ c₂ : List I.Directive} {v₁ v₂ : β},
      compileSeqLoop unit combine step err xs₁ hs₁ = .ok (c₁, v₁) →
      compileSeqLoop unit combine step err xs₂ hs₂ = .ok (c₂, v₂) →
      compileSeqLoop unit combine step err (xs₁ ++ xs₂) (hs₁ ++ hs₂) =
        .ok (c₁ ++ c₂, combine v₁ v₂)
  | [], _, [], _, _, _, _, _, h₁, h₂ => by
      dsimp only [compileSeqLoop] at h₁; simp only [Except.ok.injEq, Prod.mk.injEq] at h₁
      rcases h₁ with ⟨rfl, rfl⟩; simpa [hunit] using h₂
  | [], _, _ :: _, _, _, _, _, _, h₁, _ | _ :: _, _, [], _, _, _, _, _, h₁, _ => by
      dsimp only [compileSeqLoop] at h₁; cases h₁
  | x :: xs₁, xs₂, h :: hs₁, hs₂, _, _, _, _, h₁, h₂ => by
      rw [List.cons_append, List.cons_append]; dsimp only [compileSeqLoop] at h₁ ⊢
      cases hst : step x h with
      | error _ => simp [hst] at h₁
      | ok p =>
          simp only [hst] at h₁ ⊢
          cases hrest : compileSeqLoop unit combine step err xs₁ hs₁ with
          | error _ => simp [hrest] at h₁
          | ok _ =>
              simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h₁
              rcases h₁ with ⟨rfl, rfl⟩
              rw [compileSeqLoop_append hunit hassoc hrest h₂]
              simp only [List.append_assoc, hassoc]

theorem compileSeqLoop_mono {α β : Type _} {I : Isa} {unit : β} {combine : β → β → β}
    {step₁ step₂ : α → I.Hints → Except String (List I.Directive × β)} {err : String}
    (hmono : ∀ x h c v, step₁ x h = .ok (c, v) → step₂ x h = .ok (c, v)) :
    ∀ {xs : List α} {hs : List I.Hints} {res : List I.Directive × β},
      compileSeqLoop unit combine step₁ err xs hs = .ok res →
      compileSeqLoop unit combine step₂ err xs hs = .ok res
  | [], [], _, h => h
  | [], _ :: _, _, h | _ :: _, [], _, h => by dsimp only [compileSeqLoop] at h; cases h
  | x :: xs, hint :: hs, _, h => by
      dsimp only [compileSeqLoop] at h ⊢
      cases hst : step₁ x hint with
      | error _ => simp [hst] at h
      | ok p =>
          rw [hst] at h; rw [hmono x hint p.1 p.2 hst]; dsimp only
          cases hrest : compileSeqLoop unit combine step₁ err xs hs with
          | error _ => simp [hrest] at h
          | ok _ => rw [hrest] at h; rw [compileSeqLoop_mono hmono hrest]; exact h

theorem compileSeqLoop_mem {α β : Type _} {I : Isa} {unit : β} {combine : β → β → β}
    {step : α → I.Hints → Except String (List I.Directive × β)} {err : String} :
    ∀ {xs : List α} {hs : List I.Hints} {code : List I.Directive} {v : β},
      compileSeqLoop unit combine step err xs hs = .ok (code, v) →
      ∀ x ∈ xs, ∃ hint c k_f vx,
        step x hint = .ok (c, vx) ∧ c.IsInfixAt code k_f ∧ k_f ≤ code.length
  | [], _, _, _, _, _, hx => nomatch hx
  | _ :: _, [], _, _, h, _, _ => by dsimp only [compileSeqLoop] at h; cases h
  | x0 :: xs, hint :: hs, _, _, h, x, hx => by
      dsimp only [compileSeqLoop] at h
      cases hst : step x0 hint with
      | error _ => simp [hst] at h
      | ok p =>
          rw [hst] at h
          cases hrest : compileSeqLoop unit combine step err xs hs with
          | error _ => simp [hrest] at h
          | ok res =>
              simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, _⟩
              rcases List.mem_cons.mp hx with rfl | hx'
              · exact ⟨hint, p.1, 0, p.2, hst, ⟨res.1, rfl⟩, Nat.zero_le _⟩
              · obtain ⟨hint', c', k', vx', hst', hinf', hklen'⟩ := compileSeqLoop_mem hrest x hx'
                obtain ⟨tail, htail⟩ := hinf'
                refine ⟨hint', c', p.1.length + k', vx', hst', ⟨tail, ?_⟩, by simp; exact hklen'⟩
                have hd : (p.1 ++ res.1).drop p.1.length = res.1 := List.drop_left' rfl
                rw [← List.drop_drop, hd, htail]

theorem compileSeqLoop_compile {α β : Type _} {I : Isa} {lt : LegalTarget} (toFn : α → Fn)
    {unit : β} {combine : β → β → β}
    {step : α → I.Hints → Except String (List I.Directive × β)} {err : String}
    (hstep : ∀ x h c v, step x h = .ok (c, v) → compileFn I lt h (toFn x) = .ok c) :
    ∀ {xs : List α} {hs : List I.Hints} {code : List I.Directive} {v : β},
      compileSeqLoop unit combine step err xs hs = .ok (code, v) →
      compile I lt (xs.map toFn) hs = .ok code
  | [], [], _, _, h => by
      dsimp only [compileSeqLoop] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩; rfl
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by dsimp only [compileSeqLoop] at h; cases h
  | x :: xs, hint :: hs, _, _, h => by
      dsimp only [compileSeqLoop] at h
      cases hst : step x hint with
      | error _ => simp [hst] at h
      | ok p =>
          rw [hst] at h
          cases hrest : compileSeqLoop unit combine step err xs hs with
          | error _ => simp [hrest] at h
          | ok _ =>
              simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, _⟩
              simp only [List.map_cons, compile]
              rw [hstep x hint p.1 p.2 hst, compileSeqLoop_compile toFn hstep hrest]

theorem compileSeqLoop_supp_of {α β : Type _} {I : Isa} {lt : LegalTarget} (toFn : α → Fn)
    {unit : β} {combine : β → β → β}
    {stepSupp stepMid : α → I.Hints → Except String (List I.Directive × β)} {err : String}
    (hsupp_gate : ∀ x h res, stepSupp x h = .ok res →
      ((toFn x).earlyOpt).body.supportsSource lt = true ∧ stepMid x h = .ok res) :
    ∀ {xs : List α} {hs : List I.Hints} {res : List I.Directive × β},
      compileSeqLoop unit combine stepSupp err xs hs = .ok res →
      compileSeqLoop unit combine stepMid err xs hs = .ok res ∧
        ∀ x ∈ xs, ((toFn x).earlyOpt).body.supportsSource lt = true
  | [], [], _, h => ⟨h, fun _ hx => nomatch hx⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => by dsimp only [compileSeqLoop] at h; cases h
  | x :: xs, hint :: hs, _, h => by
      dsimp only [compileSeqLoop] at h ⊢
      cases hst : stepSupp x hint with
      | error _ => simp [hst] at h
      | ok p =>
          rw [hst] at h; obtain ⟨hs_x, hm_x⟩ := hsupp_gate x hint p hst; rw [hm_x]; dsimp only
          cases hrest : compileSeqLoop unit combine stepSupp err xs hs with
          | error _ => simp [hrest] at h
          | ok _ =>
              rw [hrest] at h
              obtain ⟨ih_mid, ih_supp⟩ := compileSeqLoop_supp_of toFn hsupp_gate hrest
              rw [ih_mid]; refine ⟨h, fun y hy => ?_⟩
              rcases List.mem_cons.mp hy with rfl | hy'; exact hs_x; exact ih_supp y hy'

/-! ## 4. Generic `TargetInit` Execution Runners -/

section TargetInitOf

variable {T : Target} {maxStack maxMem : Nat} (I : TargetInit T maxStack maxMem)

theorem TargetInit.run_fnSpec_of (host : T.mach.Host) (bound : Sym → Nat) (maxBound : Nat)
    (hbound_le : ∀ nm, bound nm ≤ maxBound) {nm : Sym} {as bs : List Ty} {spec : Spec as bs}
    {nX : Nat} (hf : T.FnSpec host nm spec (bound nm) nX) (bsMem : List UInt8) (args : Tup Val as)
    (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs as).isSome = true)
    {Q : Post bs} {X : XPost} (hspec : spec args (bsMem.At 0x1000#64) Q X)
    {post : T.mach.State → Prop}
    (hpost : ∀ st,
      (T.mach.pc st = I.ra0 ∧ ∃ rets m', Q rets m' ∧ T.RetsIn rets (T.mach.data st) ∧
        (T.mach.mem (T.mach.data st) =⋆ Eq m' ⋆ T.Exit I.sp0 (bound nm) ⋆ Std.ExtHashMap.emp)) ∨
      (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64), X sym' cs xs m' ∧
        T.mach.pc st = T.mach.labelAddr host sym' ∧ T.ArgsIn xs (T.mach.data st)) → post st)
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step host) post
      (T.mach.mkState (I.initState (bound nm) bsMem args) (T.mach.labelAddr host nm)) := by
  have hmem := I.mem_entry (bound nm) bsMem args (Nat.le_trans (hbound_le nm) hbound) hbs
  rw [← I.get_sp (bound nm) bsMem args] at hmem
  refine eventually_weaken _ _ _ _ ?_ (hf args (bsMem.At 0x1000#64) Q X hspec
    (I.initState (bound nm) bsMem args) I.ra0 Std.ExtHashMap.emp (I.argsIn _ _ _ hargs)
    (I.raReg _ _ _) (by rw [I.get_sp]; exact I.spEntry) hmem)
  rintro st (⟨hpc, rets, m', hQ, hrets, _, hm'⟩ | ⟨sym', cs, xs, m', hX, _, hpc, has, _⟩)
  · rw [I.get_sp] at hm'; exact hpost st (Or.inl ⟨hpc, rets, m', hQ, hrets, hm'⟩)
  · exact hpost st (Or.inr ⟨sym', cs, xs, m', hX, hpc, has⟩)

theorem TargetInit.run_ret1_of (host : T.mach.Host) (bound : Sym → Nat) (maxBound : Nat)
    (hbound_le : ∀ nm, bound nm ≤ maxBound) {nm : Sym} {as : List Ty} {t : Ty}
    {spec : Spec as [t]} {nX : Nat} (hf : T.FnSpec host nm spec (bound nm) nX)
    (bsMem : List UInt8) (args : Tup Val as) (v : Val t) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs as).isSome = true) {Q : Post [t]}
    (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ())) (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.RetsIn (bs := [t]) (v, ()) (T.mach.data st))
      (T.mach.mkState (I.initState (bound nm) bsMem args) (T.mach.labelAddr host nm)) := by
  refine I.run_fnSpec_of host bound maxBound hbound_le hf bsMem args hbs hargs hspec ?_ hbound
  rintro st (⟨hpc, rets, m', hq, hrets, _⟩ | ⟨_, _, _, _, hx, _⟩)
  · have hr := hQ rets m' hq; subst hr; exact ⟨hpc, hrets⟩
  · exact hx.elim

theorem TargetInit.run_ret1_i64_of (host : T.mach.Host) (bound : Sym → Nat) (maxBound : Nat)
    (hbound_le : ∀ nm, bound nm ≤ maxBound) {nm : Sym} {as : List Ty} {spec : Spec as [i64]}
    {nX : Nat} (hf : T.FnSpec host nm spec (bound nm) nX) (bsMem : List UInt8) (args : Tup Val as)
    (v : Val i64) (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs as).isSome = true)
    {Q : Post [i64]} (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ())) (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v)
      (T.mach.mkState (I.initState (bound nm) bsMem args) (T.mach.labelAddr host nm)) :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, I.retsIn_singleton v _ h.2⟩)
    (I.run_ret1_of host bound maxBound hbound_le hf bsMem args v hbs hargs hspec hQ hbound)

end TargetInitOf

end LeanQbe.T
