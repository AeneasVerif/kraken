module

public import LeanQbe.T.Main
public import LeanQbe.T.OptLemmas
public import LeanQbe.T.LegalLemmas
public import LeanQbe.T.RegaLemmas
public import LeanQbe.T.TargetLemmas
public import LeanQbe.T.Logic.MemLemmas

/-!
# Soundness of `LeanQbe.T.Main` & `Compiled` Harness (`T12g`)

* **Signature & contract transfer**: `fnSpec_of_spec`, `encodeTup_eq_cast_of_legalSig_eq`,
  `legal_xpost_of_legalSig_eq`, `legal_xpost_i64`, and `fnSpec_of_legalEnv_legalSig_eq`
  (`noExit` and general `legalXPost` variants).
* **Cross-function label uniqueness**: `lname_inj_cross`, `lname_ne_cross`, `stringsNodup_nodup`,
  and `compileModule_labelsUnique` bridging `Rega.LabelClean T.toIsa` + `fnNameOk` +
  distinct function/exit names directly to `T.LabelsUnique host` without scanning internal `.L`
  block labels.
* **End-to-end compilation soundness**: `compileFn_correct` (composing `Func.earlyOpt_spec` →
  `Fn.legal_spec` → `Func.lateOpt_spec` → `Rega.lowerFn_correct` with `legalEnv` & `Env.ofModule`
  signature isolation) and `compile_sound` over acyclic modules checked by `Module.checkAcyclic`.
* **Kernel-certificate harness**: `TargetLayout` (+ `TargetLayout.ofClean`), `Compiled`,
  `checkCompile`, `compileChecked` (+ `WithLabels` variant), `Compiled.fnSpec`,
  `Compiled.fnSpec_host`, and `TargetInit` (`run_fnSpec`, `run_ret1`, `run_ret1_sep`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

open Std Std.ExtHashMap

/-! ## `Target.FnSpec` variance and cast helpers -/

/-- `Target.FnSpec` is antitone in its source/IR contract `spec` (local helper; public
`Target.FnSpec.of_spec` is provided by `LeanQbe.T.AbiLemmas`). -/
private theorem fnSpec_of_spec {T : Target} {h : T.mach.Host} {sym : Sym} {as bs : List Ty}
    {spec₁ spec₂ : Spec as bs} {n nX : Nat}
    (him : ∀ args m Q X, spec₂ args m Q X → spec₁ args m Q X)
    (hf : T.FnSpec h sym spec₁ n nX) : T.FnSpec h sym spec₂ n nX :=
  fun args m Q X hs => hf args m Q X (him args m Q X hs)

theorem Target.argsIn_cast {T : Target} {as as' : List Ty} (h : as = as') (xs : Tup Val as)
    (s : T.mach.MData) : T.ArgsIn (cast (congrArg (Tup Val) h) xs) s ↔ T.ArgsIn xs s := by
  subst h; rfl

theorem Target.retsIn_cast {T : Target} {bs bs' : List Ty} (h : bs = bs') (ys : Tup Val bs)
    (s : T.mach.MData) : T.RetsIn (cast (congrArg (Tup Val) h) ys) s ↔ T.RetsIn ys s := by
  subst h; rfl

/-! ## Identity-signature transfer across `legalEnv` -/

theorem legalTys_length_ge_one (lt : LegalTarget) : ∀ t : Ty, 1 ≤ (lt.legalTys t).length
  | .bool | .bits _ | .float _ => Nat.le_refl 1
  | .pair a b => by
    unfold LegalTarget.legalTys; split
    · exact Nat.le_refl 1
    · rw [List.length_append]
      have ha := legalTys_length_ge_one lt a; have hb := legalTys_length_ge_one lt b; omega

theorem legalSig_length_ge (lt : LegalTarget) : ∀ ts : List Ty, ts.length ≤ (lt.legalSig ts).length
  | [] => Nat.le_refl 0
  | t :: ts => by
    simp only [LegalTarget.legalSig, List.length_append, List.length_cons]
    have ht := legalTys_length_ge_one lt t; have hts := legalSig_length_ge lt ts; omega

theorem legalSig_eq_cons_iff {lt : LegalTarget} {t : Ty} {ts : List Ty}
    (h : lt.legalSig (t :: ts) = t :: ts) : lt.legalTys t = [t] ∧ lt.legalSig ts = ts := by
  have hlen := congrArg List.length h
  simp only [LegalTarget.legalSig, List.length_append, List.length_cons] at hlen
  have h1 := legalTys_length_ge_one lt t; have h2 := legalSig_length_ge lt ts
  have hl1 : (lt.legalTys t).length = 1 := by omega
  exact List.append_inj (show lt.legalTys t ++ lt.legalSig ts = [t] ++ ts from h)
    (by simpa using hl1)

private theorem encodeVal_heq_of_legalTys_eq (lt : LegalTarget) :
    ∀ {t : Ty}, lt.legalTys t = [t] → (v : Val t) →
      HEq (encodeVal lt t v) (show Tup Val [t] from (v, ()))
  | .bool, _, _ | .float _, _, _ => HEq.rfl
  | .bits _, h, v => by
    simp only [LegalTarget.legalTys, List.cons.injEq, Ty.bits.injEq, and_true] at h
    dsimp only [encodeVal]
    rw [setWidth_eq_cast h.symm v]
    exact cast_heq _ _
  | .pair a b, h, p => by
    by_cases hp : lt.keepsPacked (.pair a b) = true
    · rw [encodeVal_pair_packed lt hp p]; exact cast_heq _ _
    · exfalso
      have hf := Bool.eq_false_iff.mpr hp
      have hlen := congrArg List.length h
      simp only [LegalTarget.legalTys, hf, Bool.false_eq_true, ↓reduceIte,
        List.length_append, List.length_singleton] at hlen
      have ha := legalTys_length_ge_one lt a
      have hb := legalTys_length_ge_one lt b
      omega

private theorem tupAppend_heq {α : Type} {f : α → Type} {a a' b b' : List α}
    (ha : a = a') (hb : b = b') {x : Tup f a} {x' : Tup f a'} {y : Tup f b} {y' : Tup f b'}
    (hx : HEq x x') (hy : HEq y y') : HEq (tupAppend x y) (tupAppend x' y') := by
  subst ha; subst hb; cases eq_of_heq hx; cases eq_of_heq hy; exact HEq.rfl

theorem encodeTup_heq_of_legalSig_eq (lt : LegalTarget) :
    ∀ {ts : List Ty}, lt.legalSig ts = ts → (xs : Tup Val ts) → HEq (encodeTup lt ts xs) xs
  | [], _, () => HEq.rfl
  | _ :: _, h, (x, xs) => by
    obtain ⟨ht, hts⟩ := legalSig_eq_cons_iff h
    dsimp only [encodeTup]
    exact tupAppend_heq ht hts (encodeVal_heq_of_legalTys_eq lt ht x)
      (encodeTup_heq_of_legalSig_eq lt hts xs)

theorem encodeTup_eq_cast_of_legalSig_eq {lt : LegalTarget} {ts : List Ty}
    (h : lt.legalSig ts = ts) (xs : Tup Val ts) :
    encodeTup lt ts xs = cast (congrArg (Tup Val) h.symm) xs :=
  eq_of_heq ((encodeTup_heq_of_legalSig_eq lt h xs).trans (cast_heq _ _).symm)

theorem legal_xpost_aux (X : XPost) (g : Sym) (m : Mem 64) {cs ts : List Ty}
    {xs : Tup Val ts} {ys : Tup Val cs} (h1 : ts = cs) (h2 : HEq xs ys)
    (hx : X g cs ys m) : X g ts xs m := by
  subst h1; cases eq_of_heq h2; exact hx

/-- Transfer an exit postcondition `X g cs xs m` across `lt.legalSig` when `lt.legalSig cs = cs`. -/
theorem legal_xpost_of_legalSig_eq {lt : LegalTarget} {cs : List Ty}
    (h : lt.legalSig cs = cs) {X : XPost} {g : Sym} {xs : Tup Val cs} {m : Mem 64}
    (hx : X g cs xs m) : X g (lt.legalSig cs) (encodeTup lt cs xs) m :=
  legal_xpost_aux X g m h (encodeTup_heq_of_legalSig_eq lt h xs) hx

/-- Single-`i64` specialization of `legal_xpost_of_legalSig_eq`. -/
theorem legal_xpost_i64 {lt : LegalTarget} (h : lt.legalSig [i64] = [i64])
    {X : XPost} {g : Sym} {v : BitVec 64} {m : Mem 64}
    (hx : X g [i64] (v, ()) m) :
    X g (lt.legalSig [i64]) (encodeTup lt [i64] (v, ())) m :=
  legal_xpost_of_legalSig_eq h hx

private theorem legalXPost_cast {lt : LegalTarget} {X : XPost} {g : Sym}
    {cs cs' : List Ty} (hcs : lt.legalSig cs = cs') {xs : Tup Val cs}
    {ys : Tup Val cs'} {m : Mem 64}
    (hy : cast (congrArg (Tup Val) hcs) (encodeTup lt cs xs) = ys)
    (hx : X g (lt.legalSig cs) (encodeTup lt cs xs) m) : X g cs' ys m := by
  subst hcs; subst hy; exact hx

/-- Transfer `T.FnSpec` from `legalEnv lt (Env.ofModule M Γ)` directly back to source `Γ` when
`lt.legalSig` fixes `(as, bs)`. -/
theorem fnSpec_of_legalEnv_legalSig_eq {T : Target} {host : T.mach.Host} {lt : LegalTarget}
    {M : Module} {Γ : Env} {sym : Sym} {as bs : List Ty} {n nX : Nat}
    (has : lt.legalSig as = as) (hbs : lt.legalSig bs = bs)
    (hmem : (sym, as, bs) ∈ M.sigs)
    (hf : T.FnSpec host sym
      (legalEnv lt (Env.ofModule M Γ) sym (lt.legalSig as) (lt.legalSig bs)) n nX) :
    T.FnSpec host sym
      (fun args m Q X => Γ sym as bs args m Q
        (fun g cs xs m' => X g (lt.legalSig cs) (encodeTup lt cs xs) m')) n nX := by
  intro args m Q X hΓ s ra R hargs hra hspE hmemS
  let args' : Tup Val (lt.legalSig as) := cast (congrArg (Tup Val) has.symm) args
  let Q' : Post (lt.legalSig bs) := fun ys m' => Q (cast (congrArg (Tup Val) hbs) ys) m'
  have hleg : legalEnv lt (Env.ofModule M Γ) sym (lt.legalSig as) (lt.legalSig bs)
      args' m Q' X := by
    refine ⟨as, bs, rfl, rfl, args, Q,
      (fun g cs xs m' => X g (lt.legalSig cs) (encodeTup lt cs xs) m'),
      ?_, ?_, ?_, ⟨hmem, hΓ⟩⟩
    · rw [cast_eq]; exact encodeTup_eq_cast_of_legalSig_eq has args
    · rintro r m₁ ⟨xs, rfl, hq⟩
      dsimp only [Q']; rw [cast_eq, encodeTup_eq_cast_of_legalSig_eq hbs xs, cast_cast_eq]; exact hq
    · rintro g cs' ys m₁ ⟨cs, hcs, xs, hy, hx⟩; exact legalXPost_cast hcs hy hx
  have hargs' : T.ArgsIn args' s := (T.argsIn_cast has.symm args s).mpr hargs
  refine eventually_weaken _ _ _ _ ?_ (hf args' m Q' X hleg s ra R hargs' hra hspE hmemS)
  rintro st (⟨hpc, rets', m', hQ', hrets', hrest, hm'⟩ | hEx)
  · exact Or.inl ⟨hpc, cast (congrArg (Tup Val) hbs) rets', m', hQ',
      (T.retsIn_cast hbs rets' (T.mach.data st)).mpr hrets', hrest, hm'⟩
  · exact Or.inr hEx

/-- Crisp source-level transfer when `lt.legalSig` fixes `(as, bs)` and `Γ` is independent of
exit continuations. -/
theorem fnSpec_of_legalEnv_legalSig_eq_noExit {T : Target} {host : T.mach.Host}
    {lt : LegalTarget} {M : Module} {Γ : Env} {sym : Sym} {as bs : List Ty} {n nX : Nat}
    (has : lt.legalSig as = as) (hbs : lt.legalSig bs = bs)
    (hmem : (sym, as, bs) ∈ M.sigs)
    (hnoex : ∀ args m Q X X', Γ sym as bs args m Q X → Γ sym as bs args m Q X')
    (hf : T.FnSpec host sym
      (legalEnv lt (Env.ofModule M Γ) sym (lt.legalSig as) (lt.legalSig bs)) n nX) :
    T.FnSpec host sym (Γ sym as bs) n nX :=
  fnSpec_of_spec (fun args m Q X h => hnoex args m Q X _ h)
    (fnSpec_of_legalEnv_legalSig_eq has hbs hmem hf)

/-! ## Cross-function label uniqueness and fast `Nodup` lemmas -/

private theorem hasDotLChars_cons_ne {x y : Char} {zs : List Char}
    (h : ¬(x = '.' ∧ y = 'L')) :
    hasDotLChars (x :: y :: zs) = hasDotLChars (y :: zs) := by
  by_cases hx : x = '.' <;> by_cases hy : y = 'L'
  · exact absurd ⟨hx, hy⟩ h
  · subst hx; simp [hasDotLChars, hy]
  · simp [hasDotLChars, hx]
  · simp [hasDotLChars, hx]

theorem hasDotLChars_append_dotL : ∀ (xs ds : List Char),
    hasDotLChars (xs ++ '.' :: 'L' :: ds) = true
  | [], _ => rfl
  | x :: [], ds => by
    have hne : ¬(x = '.' ∧ '.' = 'L') := fun h => by cases h.2
    rw [List.cons_append, List.nil_append, hasDotLChars_cons_ne hne]; rfl
  | x :: y :: zs, ds => by
    have ih := hasDotLChars_append_dotL (y :: zs) ds
    by_cases h : x = '.' ∧ y = 'L'
    · rcases h with ⟨rfl, rfl⟩; rfl
    · rw [List.cons_append, List.cons_append, hasDotLChars_cons_ne h]
      exact ih

private theorem hasDotLChars_tail {x : Char} {xs : List Char}
    (h : hasDotLChars (x :: xs) = false) : hasDotLChars xs = false := by
  cases xs with
  | nil => rfl
  | cons y zs =>
    by_cases hxy : x = '.' ∧ y = 'L'
    · rcases hxy with ⟨rfl, rfl⟩; simp [hasDotLChars] at h
    · simpa [hasDotLChars_cons_ne hxy] using h

private theorem dotL_nil_absurd {y : Char} {ys ds₁ ds₂ : List Char}
    (hy : hasDotLChars (y :: ys) = false)
    (h : '.' :: 'L' :: ds₁ = (y :: ys) ++ '.' :: 'L' :: ds₂) : False := by
  simp only [List.cons_append, List.cons.injEq] at h
  rcases ys with _ | ⟨z, zs⟩
  · cases h.2
  · simp only [List.cons_append, List.cons.injEq] at h
    rcases h with ⟨rfl, rfl, _⟩; simp [hasDotLChars] at hy

private theorem dotL_prefix_eq :
    ∀ {xs ys ds₁ ds₂ : List Char},
      hasDotLChars xs = false → hasDotLChars ys = false →
      xs ++ '.' :: 'L' :: ds₁ = ys ++ '.' :: 'L' :: ds₂ → xs = ys
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, hy, h => absurd h (dotL_nil_absurd hy)
  | _ :: _, [], _, _, hx, _, h => absurd h.symm (dotL_nil_absurd hx)
  | x :: xs, y :: ys, _, _, hx, hy, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    rcases h with ⟨rfl, htail⟩
    exact congrArg (x :: ·) (dotL_prefix_eq (hasDotLChars_tail hx) (hasDotLChars_tail hy) htail)

private theorem lname_toList (fn : Sym) (a : Nat) :
    (Rega.lname fn a).toList =
      fn.toList ++ '.' :: 'L' :: (String.ofList (Rega.natDigits (a + 1) a [])).toList := by
  simp only [Rega.lname, String.toList_append, List.append_assoc]; rfl

/-- Generated local label `Rega.lname f a` can never equal any valid symbol `g` (`fnNameOk g`). -/
theorem lname_ne_cross {f g : Sym} {a : Nat} (hg : fnNameOk g = true) :
    Rega.lname f a ≠ g := fun h => by
  have h1 := congrArg (fun s => hasDotLChars s.toList) h
  rw [lname_toList, hasDotLChars_append_dotL] at h1
  simp only [fnNameOk, Bool.not_eq_true'] at hg
  rw [hg] at h1; cases h1

/-- Cross-function injectivity of `Rega.lname` whenever both function names satisfy `fnNameOk`. -/
theorem lname_inj_cross {f g : Sym} {a b : Nat}
    (hf : fnNameOk f = true) (hg : fnNameOk g = true)
    (h : Rega.lname f a = Rega.lname g b) : f = g ∧ a = b := by
  simp only [fnNameOk, Bool.not_eq_true'] at hf hg
  have hl := congrArg String.toList h
  rw [lname_toList, lname_toList] at hl
  have heq : f = g := String.ext (dotL_prefix_eq hf hg hl)
  subst heq; exact ⟨rfl, Rega.lname_inj h⟩

theorem stringsNodup_nodup {ss : List String} (h : stringsNodup ss = true) : ss.Nodup :=
  List.Pairwise.of_map (fun (s : String) => s.toList.reverse) (fun _ _ hne e => hne (e ▸ rfl))
    (listNodup_nodup h)

theorem labelsNodupBy_nodup {D : Type} (labelOf? : D → Option Sym) {prog : List D}
    (h : labelsNodupBy labelOf? prog = true) : (prog.filterMap labelOf?).Nodup :=
  stringsNodup_nodup h

private theorem nodup_getElem?_inj : ∀ {xs : List Sym} {i j : Nat} {x : Sym},
    xs.Nodup → xs[i]? = some x → xs[j]? = some x → i = j
  | [], _, _, _, _, hi, _ => by simp at hi
  | y :: ys, 0, 0, _, _, _, _ => rfl
  | y :: ys, 0, j + 1, x, hnd, hi, hj => by
    simp only [List.nodup_cons] at hnd
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    exact absurd (hi ▸ List.mem_of_getElem? hj) hnd.1
  | y :: ys, i + 1, 0, x, hnd, hi, hj => by
    simp only [List.nodup_cons] at hnd
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    exact absurd (hj ▸ List.mem_of_getElem? hi) hnd.1
  | _ :: ys, i + 1, j + 1, x, hnd, hi, hj =>
    congrArg Nat.succ (nodup_getElem?_inj (List.nodup_cons.mp hnd).2 hi hj)

theorem compileModule_code_labels {T : Target} (hcl : Rega.LabelClean T.toIsa)
    (lt : LegalTarget) (raBytes : Nat) (exits : List Sym) (nX : Nat) :
    ∀ {extCallees : List (SigEntry × Nat)} {fs : List Fn} {hints : List T.toIsa.Hints}
      {code : List T.Directive} {bounds : List (Sym × Nat)},
      compileModule T.toIsa lt raBytes extCallees exits nX fs hints = .ok (code, bounds) →
      (fs.map Fn.name).Nodup → fs.all (fun f => fnNameOk f.name) = true →
      (∀ (i : Nat) (l : Sym), code[i]? = some (T.frame.label l) →
        ∃ f ∈ fs, l = f.name ∨ ∃ a, l = Rega.lname f.name a) ∧
      (∀ (i j : Nat) (l : Sym), code[i]? = some (T.frame.label l) →
        code[j]? = some (T.frame.label l) → i = j)
  | _, [], [], _, _, hcm, _, _ => by
    simp only [compileModule, Except.ok.injEq, Prod.mk.injEq] at hcm
    rcases hcm with ⟨rfl, rfl⟩
    exact ⟨fun _ _ hi => by simp at hi, fun _ _ _ hi => by simp at hi⟩
  | _, [], _ :: _, _, _, hcm, _, _ => by simp [compileModule] at hcm
  | _, _ :: _, [], _, _, hcm, _, _ => by simp [compileModule] at hcm
  | extCallees, f :: fs, h :: hs, code, bounds, hcm, hnd, hok => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    simp only [List.all_cons, Bool.and_eq_true] at hok
    dsimp only [compileModule] at hcm
    split at hcm
    · rename_i c b hl hcnd
      split at hcm
      · rename_i cs bs hrest
        simp only [Except.ok.injEq, Prod.mk.injEq] at hcm
        rcases hcm with ⟨rfl, rfl⟩
        obtain ⟨ih_mem, ih_uniq⟩ := compileModule_code_labels hcl lt raBytes exits nX
          hrest hnd.2 hok.2
        have hc_mem : ∀ (i : Nat) (l : Sym), c[i]? = some (T.frame.label l) →
            l = f.name ∨ ∃ a, l = Rega.lname f.name a := fun i l hi =>
          Rega.lowerFn_label_mem hcl hl hi
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
            intro i₁ j₁ hi₁ hj₁
            obtain ⟨g, hg, hlg⟩ := ih_mem j₁ l hj₁
            have hgok := List.all_eq_true.mp hok.2 g hg
            rcases hc_mem i₁ l hi₁ with rfl | ⟨a, rfl⟩ <;> rcases hlg with hgl | ⟨b, hgl⟩
            · exact hnd.1 g hg hgl.symm
            · exact lname_ne_cross hok.1 hgl.symm
            · exact lname_ne_cross hgok hgl
            · exact hnd.1 g hg (lname_inj_cross hok.1 hgok hgl).1.symm
          by_cases hic : i < c.length <;> by_cases hjc : j < c.length
          · rw [List.getElem?_append_left hic] at hi
            rw [List.getElem?_append_left hjc] at hj
            exact hc_uniq i j l hi hj
          · rw [List.getElem?_append_left hic] at hi
            rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
            exact absurd hi (fun h' => disj h' hj)
          · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
            rw [List.getElem?_append_left hjc] at hj
            exact absurd hj (fun h' => disj h' hi)
          · have hi' : c.length ≤ i := Nat.le_of_not_lt hic
            have hj' : c.length ≤ j := Nat.le_of_not_lt hjc
            rw [List.getElem?_append_right hi'] at hi
            rw [List.getElem?_append_right hj'] at hj
            have heq := ih_uniq (i - c.length) (j - c.length) l hi hj
            omega
      · simp at hcm
    · simp at hcm
    · simp at hcm

/-- Bridge `Rega.LabelClean T.toIsa` + distinct `fnNameOk` names + distinct `exits` directly to
position uniqueness of `T.frame.label` in `code ++ exits.map T.frame.label`. -/
theorem compileModule_labelsUnique {T : Target} (hcl : Rega.LabelClean T.toIsa)
    {lt : LegalTarget} {raBytes : Nat} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} {fs : List Fn} {hints : List T.toIsa.Hints}
    {code : List T.Directive} {bounds : List (Sym × Nat)}
    (hcm : compileModule T.toIsa lt raBytes extCallees exits nX fs hints = .ok (code, bounds))
    (hnd : (fs.map Fn.name ++ exits).Nodup)
    (hok : (fs.map Fn.name ++ exits).all fnNameOk = true) :
    ∀ (i j : Nat) (l : Sym),
      (code ++ exits.map T.frame.label)[i]? = some (T.frame.label l) →
      (code ++ exits.map T.frame.label)[j]? = some (T.frame.label l) → i = j := by
  have hnd_split := List.nodup_append.mp hnd
  simp only [List.all_append, Bool.and_eq_true, List.all_map] at hok
  obtain ⟨hmem, huniq⟩ := compileModule_code_labels hcl lt raBytes exits nX hcm hnd_split.1 hok.1
  have hEx : ∀ (k : Nat) (l : Sym),
      (exits.map T.frame.label)[k]? = some (T.frame.label l) → exits[k]? = some l := by
    intro k l hk
    rw [List.getElem?_map] at hk
    cases hx : exits[k]? with
    | none => simp [hx] at hk
    | some e =>
      simp only [hx, Option.map_some, Option.some.injEq] at hk
      rw [hcl.label_inj e l hk]
  have hdisj : ∀ (i₁ k₂ : Nat) (l : Sym), code[i₁]? = some (T.frame.label l) →
      (exits.map T.frame.label)[k₂]? = some (T.frame.label l) → False := by
    intro i₁ k₂ l hi₁ hk₂
    have hmemE : l ∈ exits := List.mem_of_getElem? (hEx k₂ l hk₂)
    have hlok : fnNameOk l = true := List.all_eq_true.mp hok.2 l hmemE
    obtain ⟨f, hf, hlf⟩ := hmem i₁ l hi₁
    rcases hlf with hl_eq | ⟨a, hl_eq⟩
    · exact hnd_split.2.2 l (hl_eq ▸ List.mem_map_of_mem hf) l hmemE rfl
    · exact lname_ne_cross hlok hl_eq.symm
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
  · have hi' : code.length ≤ i := Nat.le_of_not_lt hic
    have hj' : code.length ≤ j := Nat.le_of_not_lt hjc
    rw [List.getElem?_append_right hi'] at hi
    rw [List.getElem?_append_right hj'] at hj
    have heq := nodup_getElem?_inj hnd_split.2.1 (hEx _ _ hi) (hEx _ _ hj)
    omega

/-- `M.checkNamesNodup`-backed corollary proving `T.LabelsUnique host` directly from
`Rega.LabelClean T.toIsa`, `(M.fns.all (fnNameOk ·.name))`, and valid disjoint `exits`. -/
theorem compileModule_labelsUnique_of_module {T : Target} (hcl : Rega.LabelClean T.toIsa)
    (host : T.mach.Host) {lt : LegalTarget} {M : Module}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {hints : List T.toIsa.Hints} {code : List T.Directive} {bounds : List (Sym × Nat)}
    (hprog : T.mach.prog host = code ++ exits.map T.frame.label)
    (hcm : compileModule T.toIsa lt T.frame.raBytes extCallees exits nX M.fns hints =
      .ok (code, bounds))
    (hnd : M.checkNamesNodup = true) (hex_nd : exits.Nodup)
    (hex_disj : ∀ e ∈ exits, e ∉ M.fns.map Fn.name)
    (hfok : M.fns.all (fun f => fnNameOk f.name) = true) (heok : exits.all fnNameOk = true) :
    T.LabelsUnique host := by
  have hMnd := (List.nodup_append.mp (M.namesNodup_of_checkNamesNodup hnd)).1
  have hnd' : (M.fns.map Fn.name ++ exits).Nodup :=
    List.nodup_append.mpr ⟨hMnd, hex_nd, fun _ hm _ hn he => hex_disj _ hn (he ▸ hm)⟩
  have hok' : (M.fns.map Fn.name ++ exits).all fnNameOk = true := by
    simp only [List.all_append, Bool.and_eq_true, List.all_map]; exact ⟨hfok, heok⟩
  intro i j l hi hj; rw [hprog] at hi hj
  exact compileModule_labelsUnique hcl hcm hnd' hok' i j l hi hj

/-- Concatenate two separately compiled modules whose function names are pairwise distinct and
`fnNameOk`, yielding `T.LabelsUnique` for any host whose program is `code₁ ++ code₂`. -/
theorem compileModule_append_labelsUnique {T : Target} (hcl : Rega.LabelClean T.toIsa)
    (host : T.mach.Host)
    {lt₁ lt₂ : LegalTarget} {raBytes₁ raBytes₂ : Nat}
    {ext₁ ext₂ : List (SigEntry × Nat)} {exits₁ exits₂ : List Sym} {nX₁ nX₂ : Nat}
    {fs₁ fs₂ : List Fn} {hints₁ hints₂ : List T.toIsa.Hints}
    {code₁ code₂ : List T.Directive} {bounds₁ bounds₂ : List (Sym × Nat)}
    (hprog : T.mach.prog host = code₁ ++ code₂)
    (hcm₁ : compileModule T.toIsa lt₁ raBytes₁ ext₁ exits₁ nX₁ fs₁ hints₁ = .ok (code₁, bounds₁))
    (hcm₂ : compileModule T.toIsa lt₂ raBytes₂ ext₂ exits₂ nX₂ fs₂ hints₂ = .ok (code₂, bounds₂))
    (hnd : (fs₁.map Fn.name ++ fs₂.map Fn.name).Nodup)
    (hok : (fs₁.map Fn.name ++ fs₂.map Fn.name).all fnNameOk = true) :
    T.LabelsUnique host := by
  have hnd_split := List.nodup_append.mp hnd
  simp only [List.all_append, Bool.and_eq_true, List.all_map] at hok
  obtain ⟨hmem₁, huniq₁⟩ := compileModule_code_labels hcl lt₁ raBytes₁ exits₁ nX₁ hcm₁
    hnd_split.1 hok.1
  obtain ⟨hmem₂, huniq₂⟩ := compileModule_code_labels hcl lt₂ raBytes₂ exits₂ nX₂ hcm₂
    hnd_split.2.1 hok.2
  have hdisj : ∀ (i₁ j₂ : Nat) (l : Sym), code₁[i₁]? = some (T.frame.label l) →
      code₂[j₂]? = some (T.frame.label l) → False := by
    intro i₁ j₂ l hi₁ hj₂
    obtain ⟨f₁, hf₁, h₁⟩ := hmem₁ i₁ l hi₁
    obtain ⟨f₂, hf₂, h₂⟩ := hmem₂ j₂ l hj₂
    have hok₁ := List.all_eq_true.mp hok.1 f₁ hf₁
    have hok₂ := List.all_eq_true.mp hok.2 f₂ hf₂
    rcases h₁ with rfl | ⟨a, rfl⟩ <;> rcases h₂ with hnm | ⟨b, hnm⟩
    · exact hnd_split.2.2 f₁.name (List.mem_map_of_mem hf₁) f₂.name
        (List.mem_map_of_mem hf₂) hnm
    · exact lname_ne_cross hok₁ hnm.symm
    · exact lname_ne_cross hok₂ hnm
    · exact hnd_split.2.2 f₁.name (List.mem_map_of_mem hf₁) f₂.name
        (List.mem_map_of_mem hf₂) (lname_inj_cross hok₁ hok₂ hnm).1
  intro i j l hi hj
  rw [hprog] at hi hj
  rcases Nat.lt_or_ge i code₁.length with hiL | hiR <;>
    rcases Nat.lt_or_ge j code₁.length with hjL | hjR
  · rw [List.getElem?_append_left hiL] at hi
    rw [List.getElem?_append_left hjL] at hj
    exact huniq₁ i j l hi hj
  · rw [List.getElem?_append_left hiL] at hi
    rw [List.getElem?_append_right hjR] at hj
    exact absurd hj (fun h' => hdisj i (j - code₁.length) l hi h')
  · rw [List.getElem?_append_right hiR] at hi
    rw [List.getElem?_append_left hjL] at hj
    exact absurd hi (fun h' => hdisj j (i - code₁.length) l hj h')
  · rw [List.getElem?_append_right hiR] at hi
    rw [List.getElem?_append_right hjR] at hj
    have heq := huniq₂ (i - code₁.length) (j - code₁.length) l hi hj
    omega

/-! ## Stack bound and `compile` helper lemmas -/

theorem lookupBound_mem : ∀ {bounds : List (SigEntry × Nat)} {g : SigEntry} {v : Nat},
    lookupBound bounds g = some v → (g, v) ∈ bounds
  | [], _, _, h => by simp [lookupBound] at h
  | p :: ps, g, v, h => by
    simp only [lookupBound, List.find?] at h
    split at h
    · next heq =>
      simp only [Option.map_some, Option.some.injEq] at h
      rw [← SigEntry.beq_iff_eq.mp heq, ← h]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem p (lookupBound_mem h)

theorem lookupFnBound_mem : ∀ {bounds : List (Sym × Nat)} {g : Sym} {v : Nat},
    lookupFnBound bounds g = some v → (g, v) ∈ bounds
  | [], _, _, h => by simp [lookupFnBound] at h
  | p :: ps, g, v, h => by
    simp only [lookupFnBound, List.find?] at h
    split at h
    · next heq =>
      simp only [Option.map_some, Option.some.injEq] at h
      rw [← beq_iff_eq.mp heq, ← h]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem p (lookupFnBound_mem h)

theorem calleesBound_ge {F raBytes : Nat} {bounds : List (SigEntry × Nat)} :
    ∀ {gs : List SigEntry} {n : Nat}, calleesBound F raBytes bounds gs = some n → F ≤ n
  | [], _, h => by cases h; exact Nat.le_refl _
  | g :: gs, n, h => by
    simp only [calleesBound] at h
    split at h
    · next bg rest _ _ =>
      cases h
      exact Nat.le_trans (by omega) (Nat.le_max_left (F + raBytes + bg) rest)
    · cases h

theorem calleesBound_mem {F raBytes : Nat} {bounds : List (SigEntry × Nat)} :
    ∀ {gs : List SigEntry} {n : Nat}, calleesBound F raBytes bounds gs = some n →
      ∀ g ∈ gs, ∃ bg, lookupBound bounds g = some bg ∧ F + raBytes + bg ≤ n
  | [], _, _, _, h => nomatch h
  | _ :: _, _, h, g, hmem => by
    simp only [calleesBound] at h
    split at h
    · next bg rest h1 h2 =>
      cases h
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact ⟨bg, h1, Nat.le_max_left _ _⟩
      · obtain ⟨bg', hbg', hle⟩ := calleesBound_mem h2 g hmem'
        exact ⟨bg', hbg', Nat.le_trans hle (Nat.le_max_right _ _)⟩
    · cases h

theorem checkAndBoundExt_spec {I : Isa} {raBytes : Nat} {exits : List Sym} {nX : Nat}
    {bounds : List (SigEntry × Nat)} {h : I.Hints} {ext : Rega.Ext} {n : Nat}
    (hc : checkAndBoundExt I raBytes exits nX bounds h ext = some n) :
    I.frame.frameSize h.totalSlots ≤ n ∧ n + raBytes ≤ 2 ^ 64 ∧
      (∀ g ∈ ext.callees, ∃ bg, lookupBound bounds g = some bg ∧
        I.frame.frameSize h.totalSlots + raBytes + bg ≤ n) ∧
      (∀ g ∈ ext.exits, g ∈ exits ∧ nX ≤ n) := by
  simp only [checkAndBoundExt] at hc
  cases hcb : calleesBound (I.frame.frameSize h.totalSlots) raBytes bounds ext.callees with
  | none => rw [hcb] at hc; cases hc
  | some n₁ =>
    rw [hcb] at hc
    cases hex : ext.exits.all (fun g => exits.contains g) with
    | false => rw [hex] at hc; cases hc
    | true =>
      rw [hex] at hc; simp only [↓reduceIte] at hc
      let n₁' := if ext.exits.isEmpty then n₁ else Nat.max n₁ nX
      change (if Nat.ble (n₁' + raBytes) (2 ^ 64) = true then some n₁' else none) = some n at hc
      cases hble : Nat.ble (n₁' + raBytes) (2 ^ 64) with
      | false => rw [hble] at hc; cases hc
      | true =>
        rw [hble] at hc; simp only [↓reduceIte, Option.some.injEq] at hc
        subst hc
        have hle := calleesBound_ge hcb
        have hex' : ∀ g ∈ ext.exits, g ∈ exits := fun g hg =>
          by simpa using List.all_eq_true.mp hex g hg
        have hle_n : n₁ ≤ n₁' := by
          dsimp only [n₁']; cases ext.exits.isEmpty <;> simp [Nat.le_max_left]
        refine ⟨Nat.le_trans hle hle_n, Nat.le_of_ble_eq_true hble, fun g hg => ?_, fun g hg => ?_⟩
        · obtain ⟨bg, hbg, hbd⟩ := calleesBound_mem hcb g hg
          exact ⟨bg, hbg, Nat.le_trans hbd hle_n⟩
        · refine ⟨hex' g hg, ?_⟩
          have hne : ext.exits.isEmpty = false := by
            cases he : ext.exits with | nil => simp [he] at hg | cons _ _ => rfl
          dsimp only [n₁']; simp [hne, Nat.le_max_right]

theorem compile_of_compileModule {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {exits : List Sym} {nX : Nat} :
    ∀ {extCallees : List (SigEntry × Nat)} {fs : List Fn} {hints : List I.Hints}
      {code : List I.Directive} {bounds : List (Sym × Nat)},
      compileModule I lt raBytes extCallees exits nX fs hints = .ok (code, bounds) →
      compile I lt fs hints = .ok code
  | _, [], [], _, _, h => by simp [compileModule] at h; cases h.1; rfl
  | _, [], _ :: _, _, _, h => by simp [compileModule] at h
  | _, _ :: _, [], _, _, h => by simp [compileModule] at h
  | _, _ :: _, _ :: _, _, _, h => by
    dsimp only [compileModule] at h
    split at h
    · rename_i c b hl _
      split at h
      · rename_i cs bs hrest
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have h1 : compileFn I lt _ _ = .ok c := hl
        have h2 := compile_of_compileModule hrest
        simp [compile, h1, h2]
      · simp at h
    · simp at h
    · simp at h

/-! ## `compileFn_correct` and `compile_sound` -/

theorem fn_mid_wf {lt : LegalTarget} {f : Fn} (hwf : f.Wf) : (f.mid lt).Wf := by
  have _ := hwf
  exact Func.renorm_wf _

private theorem mid_pipeline_spec {lt : LegalTarget} {as rs : List Ty} (g : Func as rs)
    (hg : g.Wf) (hsupp : (Func.earlyOpt g).supportsSource lt = true) (Γ : Env)
    (xs : Tup Val as) (xs' : Tup Val (lt.legalSig as)) (hxs : encodeTup lt as xs = xs')
    (m : Mem 64) (P : Post rs) (E : XPost)
    (Q' : Post (lt.legalSig rs)) (X' : XPost)
    (hQ : ∀ r m₁, legalPost lt P r m₁ → Q' r m₁)
    (hX : ∀ f cs ys m₁, legalXPost lt E f cs ys m₁ → X' f cs ys m₁)
    (hs : Func.spec Γ g xs m P E) :
    Func.spec (legalEnv lt Γ) (Func.lateOpt (Func.legal lt (Func.earlyOpt g))) xs' m Q' X' := by
  subst hxs
  have hwf₁ : (Func.earlyOpt g).Wf := Func.earlyOpt_wf hg
  have hopt : Func.spec Γ (Func.earlyOpt g) xs m P E := Func.earlyOpt_spec hg hs
  have hleg := Func.legal_spec lt (Func.earlyOpt g) hwf₁ hsupp Γ xs m P E hopt
  have hmono := Func.spec_mono (legalEnv lt Γ) (Func.legal lt (Func.earlyOpt g))
    (encodeTup lt as xs) m (legalPost lt P) Q' (legalXPost lt E) X' hQ hX hleg
  exact Func.lateOpt_spec (Func.legal_wf lt hwf₁) hmono

private theorem legalEnv_elim_mid {lt : LegalTarget} {f : Fn} {Γ_src : Env}
    (hiso : ∀ as bs xs m P E, Γ_src f.name as bs xs m P E → as = f.as ∧ bs = f.rs)
    {xs' : Tup Val (lt.legalSig f.as)} {m : Mem 64} {Q' : Post (lt.legalSig f.rs)} {X' : XPost}
    (h : legalEnv lt Γ_src f.name (lt.legalSig f.as) (lt.legalSig f.rs) xs' m Q' X') :
    ∃ (xs : Tup Val f.as) (P : Post f.rs) (E : XPost),
      encodeTup lt f.as xs = xs' ∧ (∀ r m₁, legalPost lt P r m₁ → Q' r m₁) ∧
      (∀ g cs ys m₁, legalXPost lt E g cs ys m₁ → X' g cs ys m₁) ∧
      Γ_src f.name f.as f.rs xs m P E := by
  rcases h with ⟨as, bs, has, hbs, xs, P, E, hxs, hQ, hX, hΓ⟩
  obtain ⟨rfl, rfl⟩ := hiso as bs xs m P E hΓ
  refine ⟨xs, P, E, ?_, ?_, hX, hΓ⟩
  · simpa only [cast_eq] using hxs
  · intro r m₁ hp; have := hQ r m₁ hp; rwa [cast_eq] at this

/-- Reified body of `f.mid lt` equals `Func.renorm` of the staged `earlyOpt → legal → lateOpt`
pipeline. -/
theorem fn_mid_body_eq (lt : LegalTarget) (f : Fn) :
    (f.mid lt).body = Func.renorm (Func.lateOpt (Func.legal lt (Func.earlyOpt f.body))) := by
  delta Fn.mid Fn.lateOpt Fn.legal Fn.earlyOpt Func.renorm
  rfl

/-- Lift a WP contract on the un-materialized `Func.lateOpt` body to `(f.mid lt).body`. -/
theorem fn_mid_spec_of_lateOpt {lt : LegalTarget} {f : Fn} (hwf : f.Wf) (Γ : Env)
    {xs : Tup Val (lt.legalSig f.as)} {m : Mem 64} {Q : Post (lt.legalSig f.rs)} {X : XPost}
    (h : Func.spec Γ (Func.lateOpt (Func.legal lt (Func.earlyOpt f.body))) xs m Q X) :
    Func.spec Γ (f.mid lt).body xs m Q X :=
  (congrArg (fun b => Func.spec Γ b xs m Q X) (fn_mid_body_eq lt f)).mpr
    (Func.renorm_spec (Func.lateOpt_wf (Func.legal_wf lt (Func.earlyOpt_wf hwf))) h)

private theorem compileFn_mid_spec {lt : LegalTarget} {f : Fn} (hwf : f.Wf)
    (hsupp : (Func.earlyOpt f.body).supportsSource lt = true) (Γ_src : Env)
    (hiso : ∀ as bs xs m P E, Γ_src f.name as bs xs m P E → as = f.as ∧ bs = f.rs)
    (hsound : ∀ xs m P E, Γ_src f.name f.as f.rs xs m P E → Func.spec Γ_src f.body xs m P E) :
    ∀ xs' m Q' X',
      legalEnv lt Γ_src f.name (lt.legalSig f.as) (lt.legalSig f.rs) xs' m Q' X' →
      Func.spec (legalEnv lt Γ_src)
        (Func.lateOpt (Func.legal lt (Func.earlyOpt f.body))) xs' m Q' X' := by
  intro xs' m Q' X' h
  obtain ⟨xs, P, E, hxs', hQ', hX, hΓ⟩ := legalEnv_elim_mid hiso h
  exact mid_pipeline_spec f.body hwf hsupp Γ_src xs xs' hxs' m P E Q' X' hQ' hX
    (hsound xs m P E hΓ)

/-- Generalized `compileFn_correct` for any signature-isolated source environment `Γ_src`. -/
theorem compileFn_correct_iso (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (hints : T.toIsa.Hints) (E : Rega.Ext) (f : Fn) (Γ_src : Env)
    (n nX : Nat) (bound : Sym → Nat) {code : List T.Directive} {k₀ : Nat}
    (hwf : f.Wf) (hsupp : (f.earlyOpt).body.supportsSource lt = true)
    (hl : Rega.lowerFn T.toIsa hints E (f.mid lt) = .ok code)
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hfr : Rega.frame T hints ≤ n) (hn : n + T.frame.raBytes ≤ 2 ^ 64)
    (hiso : ∀ as bs xs m P E', Γ_src f.name as bs xs m P E' → as = f.as ∧ bs = f.rs)
    (hsound : ∀ xs m P E', Γ_src f.name f.as f.rs xs m P E' → Func.spec Γ_src f.body xs m P E')
    (hcal : ∀ g as bs, (g, as, bs) ∈ E.callees →
      T.FnSpec host g (legalEnv lt Γ_src g as bs) (bound g) nX ∧
      Rega.frame T hints + T.frame.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ E.exits → T.Defined host g ∧ nX ≤ n) :
    T.FnSpec host f.name
      (legalEnv lt Γ_src f.name (lt.legalSig f.as) (lt.legalSig f.rs)) n nX :=
  fnSpec_of_spec
    (fun args m Q X h =>
      fn_mid_spec_of_lateOpt hwf (legalEnv lt Γ_src)
        (compileFn_mid_spec hwf hsupp Γ_src hiso hsound args m Q X h))
    (Rega.lowerFn_correct T host hints E (f.mid lt) (legalEnv lt Γ_src) n nX bound
      (fn_mid_wf hwf) hl hc hu hfr hn hcal hex)

/-- Single-function `compileFn` correctness specialized to a module `M` via `Env.ofModule M Γ`
for signature isolation. -/
theorem compileFn_correct (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (M : Module) (hnd : M.namesNodup) {f : Fn} (hf : f ∈ M.fns)
    (hints : T.toIsa.Hints) (Γ : Env) (n nX : Nat) (bound : Sym → Nat)
    {code : List T.Directive} {k₀ : Nat}
    (hwf : f.Wf) (hsupp : (f.earlyOpt).body.supportsSource lt = true)
    (hl : compileFn T.toIsa lt hints f = .ok code)
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hfr : Rega.frame T hints ≤ n) (hn : n + T.frame.raBytes ≤ 2 ^ 64)
    (hsound : ∀ xs m P E',
      Env.ofModule M Γ f.name f.as f.rs xs m P E' → Func.wp (Env.ofModule M Γ) f.body xs m P E')
    (hcal : ∀ g as bs, (g, as, bs) ∈ (f.mid lt).ext.callees →
      T.FnSpec host g (legalEnv lt (Env.ofModule M Γ) g as bs) (bound g) nX ∧
      Rega.frame T hints + T.frame.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ (f.mid lt).ext.exits → T.Defined host g ∧ nX ≤ n) :
    T.FnSpec host f.name
      (legalEnv lt (Env.ofModule M Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs)) n nX :=
  compileFn_correct_iso T host lt hints (f.mid lt).ext f (Env.ofModule M Γ) n nX bound
    hwf hsupp hl hc hu hfr hn
    (fun as bs xs m P E' h => by
      by_cases he : (as, bs) = (f.as, f.rs)
      · exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
      · exact absurd h (Env.ofModule_empty_off_sig hnd Γ hf he xs m P E'))
    hsound hcal hex

private theorem find?_pred {α : Type} {p : α → Bool} :
    ∀ {xs : List α} {x : α}, xs.find? p = some x → p x = true
  | [], _, h => by simp at h
  | y :: ys, x, h => by
    simp only [List.find?] at h
    cases hp : p y with
    | true => simp [hp] at h; subst h; exact hp
    | false => simp [hp] at h; exact find?_pred h

private theorem defined_of_lowerFn {T : Target} {host : T.mach.Host}
    {hints : T.toIsa.Hints} {E : Rega.Ext} {f : Fn} {code : List T.Directive} {k₀ : Nat}
    (hl : Rega.lowerFn T.toIsa hints E f = .ok code)
    (hc : code.IsInfixAt (T.mach.prog host) k₀) : T.Defined host f.name := by
  unfold Rega.lowerFn at hl
  split at hl
  · cases hl
  · cases hal : T.toIsa.assignArgs f.as with
    | none => simp [hal] at hl
    | some argLocs =>
      cases hrl : T.toIsa.assignRets f.rs with
      | none => simp [hal, hrl] at hl
      | some _ =>
        simp only [hal, hrl] at hl
        cases hb : Rega.bindAbiParams T.toIsa argLocs 0 ⟨[], .empty, .empty, .empty⟩ with
        | none => simp [hb] at hl
        | some st0 =>
          simp only [hb] at hl
          cases hle : Rega.lowerExpr T.toIsa hints E f.name
              (f.body Rega.VNat Rega.LNat (Tup.levels f.as 0)) f.as.length 0 0 st0 none with
          | error _ => simp [hle] at hl
          | ok _ =>
            simp only [hle, Except.ok.injEq] at hl
            subst hl
            exact ⟨k₀, (List.IsInfixAt.cons hc).1⟩

private theorem compile_sound_aux (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (M : Module) (Γ : Env) (hnd : M.namesNodup)
    (exits : List Sym) (nX : Nat) (hexits : ∀ g ∈ exits, T.Defined host g) :
    ∀ {fs : List Fn} {hints : List T.toIsa.Hints} {extCallees : List (SigEntry × Nat)}
      {code : List T.Directive} {bounds : List (Sym × Nat)} {k₀ : Nat},
      compileModule T.toIsa lt T.frame.raBytes extCallees exits nX fs hints = .ok (code, bounds) →
      code.IsInfixAt (T.mach.prog host) k₀ → T.LabelsUnique host → (fs.map Fn.name).Nodup →
      (∀ f ∈ fs, f ∈ M.fns ∧ f.Wf ∧ (f.earlyOpt).body.supportsSource lt = true ∧
        ∀ xs m P E, Env.ofModule M Γ f.name f.as f.rs xs m P E →
          Func.wp (Env.ofModule M Γ) f.body xs m P E) →
      (∀ p ∈ extCallees,
        T.FnSpec host p.1.1 (legalEnv lt (Env.ofModule M Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX) →
      (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) →
      (∀ p ∈ extCallees, p.1.1 ∉ fs.map Fn.name) →
      ∀ p ∈ bounds, ∃ f ∈ fs, p.1 = f.name ∧ T.Defined host p.1 ∧
        T.FnSpec host p.1
          (legalEnv lt (Env.ofModule M Γ) p.1 (lt.legalSig f.as) (lt.legalSig f.rs)) p.2 nX
  | [], [], _, _, _, _, hcm, _, _, _, _, _, _, _, p, hp => by
    simp [compileModule] at hcm; rcases hcm with ⟨_, rfl⟩; cases hp
  | [], _ :: _, _, _, _, _, hcm, _, _, _, _, _, _, _, _, _ => by simp [compileModule] at hcm
  | _ :: _, [], _, _, _, _, hcm, _, _, _, _, _, _, _, _, _ => by simp [compileModule] at hcm
  | f :: fs, hint :: hints, extCallees, code, bounds, k₀, hcm, hc, hu, hfsnd, hfns,
      hext, hext_eq, hext_disj, p, hp => by
    simp only [List.map_cons, List.nodup_cons] at hfsnd
    dsimp only [compileModule] at hcm
    cases hl : Rega.lowerFn T.toIsa hint (f.mid lt).ext (f.mid lt) with
    | error e => simp [hl] at hcm
    | ok c =>
      cases hchk : checkAndBoundExt T.toIsa T.frame.raBytes exits nX extCallees hint
          (f.mid lt).ext with
      | none => simp [hl, hchk] at hcm
      | some b =>
        simp only [hl, hchk] at hcm
        cases hrest : compileModule T.toIsa lt T.frame.raBytes (((f.mid lt).sig, b) :: extCallees)
            exits nX fs hints with
        | error e => simp [hrest] at hcm
        | ok res =>
          rcases res with ⟨cs, bs⟩
          simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at hcm
          rcases hcm with ⟨rfl, rfl⟩
          obtain ⟨hc_inf, hcs_inf⟩ := List.IsInfixAt.append hc
          obtain ⟨hfM, hfwf, hfsupp, hfwp⟩ := hfns f List.mem_cons_self
          have hfns' : ∀ g ∈ fs, g ∈ M.fns ∧ g.Wf ∧ (g.earlyOpt).body.supportsSource lt = true ∧
              ∀ xs m P E, Env.ofModule M Γ g.name g.as g.rs xs m P E →
                Func.wp (Env.ofModule M Γ) g.body xs m P E :=
            fun g hg => hfns g (List.mem_cons_of_mem f hg)
          obtain ⟨hfr, hn, hcal_b, hex_b⟩ := checkAndBoundExt_spec hchk
          let bound : Sym → Nat := fun g =>
            match extCallees.find? (fun q => q.1.1 == g) with
            | some q => q.2
            | none => 0
          have hcal : ∀ g as bs', (g, as, bs') ∈ (f.mid lt).ext.callees →
              T.FnSpec host g (legalEnv lt (Env.ofModule M Γ) g as bs') (bound g) nX ∧
              Rega.frame T hint + T.frame.raBytes + bound g ≤ b := by
            intro g as bs' hg
            obtain ⟨bg, hlk, hle⟩ := hcal_b (g, as, bs') hg
            have hmem : ((g, as, bs'), bg) ∈ extCallees := lookupBound_mem hlk
            have hbd_eq : bound g = bg := by
              dsimp only [bound]
              cases hfnd : extCallees.find? (fun q => q.1.1 == g) with
              | none =>
                exfalso
                have hnot := List.find?_eq_none.mp hfnd ((g, as, bs'), bg) hmem
                simp at hnot
              | some q =>
                have hqmem : q ∈ extCallees := List.mem_of_find?_eq_some hfnd
                have hpred : q.1.1 = g :=
                  beq_iff_eq.mp (find?_pred (p := fun q : SigEntry × Nat => q.1.1 == g) hfnd)
                exact hext_eq q hqmem ((g, as, bs'), bg) hmem hpred
            rw [hbd_eq]; exact ⟨hext ((g, as, bs'), bg) hmem, hle⟩
          have hex : ∀ g, g ∈ (f.mid lt).ext.exits → T.Defined host g ∧ nX ≤ b := fun g hg =>
            ⟨hexits g (hex_b g hg).1, (hex_b g hg).2⟩
          have hfdef : T.Defined host f.name := defined_of_lowerFn (f := f.mid lt) hl hc_inf
          have hfspec : T.FnSpec host f.name
              (legalEnv lt (Env.ofModule M Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs)) b nX :=
            compileFn_correct T host lt M hnd hfM hint Γ b nX bound
              hfwf hfsupp hl hc_inf hu hfr hn hfwp hcal hex
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact ⟨f, List.mem_cons_self, rfl, hfdef, hfspec⟩
          · have hext' : ∀ q ∈ ((f.mid lt).sig, b) :: extCallees,
                T.FnSpec host q.1.1
                  (legalEnv lt (Env.ofModule M Γ) q.1.1 q.1.2.1 q.1.2.2) q.2 nX := by
              intro q hq
              rcases List.mem_cons.mp hq with rfl | hq'
              · exact hfspec
              · exact hext q hq'
            have hext_disj' : ∀ q ∈ ((f.mid lt).sig, b) :: extCallees, q.1.1 ∉ fs.map Fn.name := by
              intro q hq hmem
              rcases List.mem_cons.mp hq with rfl | hq'
              · exact hfsnd.1 hmem
              · exact hext_disj q hq' (List.mem_cons_of_mem f.name hmem)
            have hext_eq' : ∀ q₁ ∈ ((f.mid lt).sig, b) :: extCallees,
                ∀ q₂ ∈ ((f.mid lt).sig, b) :: extCallees, q₁.1.1 = q₂.1.1 → q₁.2 = q₂.2 := by
              intro q₁ hq₁ q₂ hq₂ hsym
              rcases List.mem_cons.mp hq₁ with rfl | hq₁' <;>
                rcases List.mem_cons.mp hq₂ with rfl | hq₂'
              · rfl
              · exact absurd (hsym.symm ▸ List.mem_cons_self) (hext_disj q₂ hq₂')
              · exact absurd (hsym ▸ List.mem_cons_self) (hext_disj q₁ hq₁')
              · exact hext_eq q₁ hq₁' q₂ hq₂' hsym
            obtain ⟨g, hg, heqn, hgdef, hgspec⟩ := compile_sound_aux T host lt M Γ hnd exits nX
              hexits hrest hcs_inf hu hfsnd.2 hfns' hext' hext_eq' hext_disj' p hp'
            exact ⟨g, List.mem_cons_of_mem f hg, heqn, hgdef, hgspec⟩

/-- Top-level acyclic module linking theorem over `M : Module` checked by `M.checkAcyclic = true`
(`Module.moduleOk_of_checkAcyclic`), establishing `T.Defined` and `T.FnSpec` at `legalEnv lt
(Env.ofModule M Γ)` for every compiled function entry in `bounds`. -/
theorem compile_sound (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (M : Module) (Γ : Env) (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (hints : List T.toIsa.Hints) (code : List T.Directive) (bounds : List (Sym × Nat)) (k₀ : Nat)
    (hcm : compileModule T.toIsa lt T.frame.raBytes extCallees exits nX M.fns hints =
      .ok (code, bounds))
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hacyc : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf)
    (hsupp : ∀ f ∈ M.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ M.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec host p.1.1 (legalEnv lt (Env.ofModule M Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ M.fns.map Fn.name))
    (hexits : ∀ g ∈ exits, T.Defined host g) :
    ∀ p ∈ bounds, ∃ f ∈ M.fns, p.1 = f.name ∧ T.Defined host p.1 ∧
      T.FnSpec host p.1
        (legalEnv lt (Env.ofModule M Γ) p.1 (lt.legalSig f.as) (lt.legalSig f.rs)) p.2 nX := by
  have hMod := (Module.moduleOk_of_checkAcyclic hacyc hwf hwp).ofModule
  have hfnsNd : (M.fns.map Fn.name).Nodup := (List.nodup_append.mp hMod.nodup).1
  have hfnsOk : ∀ f ∈ M.fns, f ∈ M.fns ∧ f.Wf ∧ (f.earlyOpt).body.supportsSource lt = true ∧
      ∀ xs m P E, Env.ofModule M Γ f.name f.as f.rs xs m P E →
        Func.wp (Env.ofModule M Γ) f.body xs m P E := by
    intro f hf
    obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hf
    exact ⟨hf, hwf f hf, hsupp f hf, (hMod.fnsOk pre f post hsplit).2.2⟩
  exact compile_sound_aux T host lt M Γ hMod.nodup exits nX hexits hcm hc hu
    hfnsNd hfnsOk hext hext_uniq.1 hext_uniq.2

/-- Unique identification of `f ∈ M.fns` from `f.name` under `M.namesNodup`. -/
theorem fn_eq_of_mem_fns : ∀ {fns : List Fn}, (fns.map Fn.name).Nodup →
    ∀ {f g : Fn}, f ∈ fns → g ∈ fns → f.name = g.name → f = g
  | [], _, _, _, hf, _, _ => nomatch hf
  | _ :: _, hnd, f, g, hf, hg, hnm => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    rcases List.mem_cons.mp hf with rfl | hf' <;> rcases List.mem_cons.mp hg with rfl | hg'
    · rfl
    · exact absurd hnm.symm (hnd.1 g hg')
    · exact absurd hnm (hnd.1 f hf')
    · exact fn_eq_of_mem_fns hnd.2 hf' hg' hnm

/-! ## Check-result extractors, `TargetLayout`, `Compiled`, and `compileChecked` -/

theorem bound_le_of_all {D : Type} {res : Except String (List D × List (Sym × Nat))}
    {c : List D} {b : List (Sym × Nat)} {maxBound : Nat}
    (hres : res = .ok (c, b)) (hle : b.all (fun p => Nat.ble p.2 maxBound) = true) (nm : Sym) :
    (lookupFnBound (extractBounds res) nm).getD 0 ≤ maxBound := by
  subst hres; unfold extractBounds
  cases hlk : lookupFnBound b nm with
  | none => simp
  | some v =>
    simpa using Nat.le_of_ble_eq_true (List.all_eq_true.mp hle (nm, v) (lookupFnBound_mem hlk))

theorem bound_mem_of_all {D : Type} {res : Except String (List D × List (Sym × Nat))}
    {c : List D} {b : List (Sym × Nat)} {fnNames : List Sym}
    (hres : res = .ok (c, b)) (hmem : fnNames.all (fun nm => (lookupFnBound b nm).isSome) = true)
    {nm : Sym} (hnm : nm ∈ fnNames) :
    (nm, (lookupFnBound (extractBounds res) nm).getD 0) ∈ extractBounds res := by
  subst hres; unfold extractBounds
  have hall := List.all_eq_true.mp hmem nm hnm
  cases hlk : lookupFnBound b nm with
  | none => simp [hlk] at hall
  | some _ => exact lookupFnBound_mem hlk

theorem checkCompileResult_parts {D : Type} {label : Sym → D} {progSmall : List D → Bool}
    {res : Except String (List D × List (Sym × Nat))} {fnNames exits : List Sym} {maxBound : Nat}
    (h : checkCompileResult label progSmall res fnNames exits maxBound = true) :
    res = .ok (extractCode res, extractBounds res) ∧ fnNames.all fnNameOk = true ∧
      exits.all fnNameOk = true ∧ (fnNames ++ exits).Nodup ∧
      progSmall (extractCode res ++ exits.map label) = true ∧
      (extractBounds res).all (fun p => Nat.ble p.2 maxBound) = true ∧
      fnNames.all (fun nm => (lookupFnBound (extractBounds res) nm).isSome) = true := by
  cases res with
  | error _ => simp [checkCompileResult] at h
  | ok cb =>
    rcases cb with ⟨c, b⟩; simp only [checkCompileResult, Bool.and_eq_true] at h
    unfold extractCode extractBounds
    exact ⟨rfl, h.1.1.1.1.1, h.1.1.1.1.2, stringsNodup_nodup h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem extractResult_eq {D : Type} {label : Sym → D} {progSmall : List D → Bool}
    {res : Except String (List D × List (Sym × Nat))} {fnNames exits : List Sym} {maxBound : Nat}
    (h : checkCompileResult label progSmall res fnNames exits maxBound = true) :
    res = .ok (extractCode res, extractBounds res) := (checkCompileResult_parts h).1

theorem checkWithLabels_parts {D : Type} {label : Sym → D} {labelsNodup progSmall : List D → Bool}
    {res : Except String (List D × List (Sym × Nat))} {fnNames exits : List Sym} {maxBound : Nat}
    (h : checkCompileResultWithLabels label labelsNodup progSmall res
      fnNames exits maxBound = true) :
    res = .ok (extractCode res, extractBounds res) ∧
      labelsNodup (extractCode res ++ exits.map label) = true ∧
      progSmall (extractCode res ++ exits.map label) = true ∧
      (extractBounds res).all (fun p => Nat.ble p.2 maxBound) = true ∧
      fnNames.all (fun nm => (lookupFnBound (extractBounds res) nm).isSome) = true := by
  cases res with
  | error _ => simp [checkCompileResultWithLabels] at h
  | ok cb =>
    rcases cb with ⟨c, b⟩; simp only [checkCompileResultWithLabels, Bool.and_eq_true] at h
    unfold extractCode extractBounds
    exact ⟨rfl, h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- Target-specific host layout constructor supporting both structural `Rega.LabelClean`
uniqueness (`TargetLayout.ofClean`) and explicit `stringsNodup` directive checks. -/
structure TargetLayout (T : Target) where
  progSmall : List T.Directive → Bool
  layoutOf : (prog : List T.Directive) → progSmall prog = true → T.mach.Host
  prog_layoutOf : ∀ (prog : List T.Directive) (h : progSmall prog = true),
    T.mach.prog (layoutOf prog h) = prog
  labelsNodup : List T.Directive → Bool
  labelsUnique_layoutOf : ∀ {prog : List T.Directive} (h : progSmall prog = true),
    labelsNodup prog = true → T.LabelsUnique (layoutOf prog h)

/-- Construct a `TargetLayout` when label uniqueness is discharged structurally via
`Rega.LabelClean` (`compileChecked`), without scanning directives with `labelsNodup`. -/
def TargetLayout.ofClean {T : Target} (progSmall : List T.Directive → Bool)
    (layoutOf : (prog : List T.Directive) → progSmall prog = true → T.mach.Host)
    (prog_layoutOf : ∀ (prog : List T.Directive) (h : progSmall prog = true),
      T.mach.prog (layoutOf prog h) = prog) : TargetLayout T :=
  ⟨progSmall, layoutOf, prog_layoutOf, fun _ => false, fun _ h => nomatch h⟩

/-- Bundle of a compiled typed module on target `T`, constructed from a single kernel evaluation
of `checkCompile` (or `checkCompileWithLabels`) so downstream proofs never re-evaluate the
compiler. -/
structure Compiled (T : Target) (lt : LegalTarget) (extCallees : List (SigEntry × Nat))
    (exits : List Sym) (nX : Nat) (fs : List Fn) (hints : List T.toIsa.Hints)
    (maxBound : Nat := 2048) where
  code : List T.Directive
  bounds : List (Sym × Nat)
  compileModule_eq :
    compileModule T.toIsa lt T.frame.raBytes extCallees exits nX fs hints = .ok (code, bounds)
  compile_eq : compile T.toIsa lt fs hints = .ok code
  bound_mem : ∀ {nm : Sym}, nm ∈ fs.map Fn.name → (nm, (lookupFnBound bounds nm).getD 0) ∈ bounds
  bound_le : ∀ (nm : Sym), (lookupFnBound bounds nm).getD 0 ≤ maxBound
  host : T.mach.Host
  prog_host : T.mach.prog host = code ++ exits.map T.frame.label
  labelsUnique : T.LabelsUnique host

namespace Compiled

variable {T : Target} {lt : LegalTarget} {extCallees : List (SigEntry × Nat)}
  {exits : List Sym} {nX : Nat} {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}

/-- Stack bound computed for function `nm` in `M`. -/
def bound (M : Compiled T lt extCallees exits nX fs hints maxBound) (nm : Sym) : Nat :=
  (lookupFnBound M.bounds nm).getD 0

theorem bound_mem_of_mem (M : Compiled T lt extCallees exits nX fs hints maxBound)
    {nm : Sym} (hnm : nm ∈ fs.map Fn.name) : (nm, M.bound nm) ∈ M.bounds := M.bound_mem hnm

theorem bound_le_max (M : Compiled T lt extCallees exits nX fs hints maxBound) (nm : Sym) :
    M.bound nm ≤ maxBound := M.bound_le nm

theorem code_infix_host (M : Compiled T lt extCallees exits nX fs hints maxBound) :
    M.code.IsInfixAt (T.mach.prog M.host) 0 := by
  rw [M.prog_host]; exact ⟨exits.map T.frame.label, rfl⟩

theorem defined_exit_host (M : Compiled T lt extCallees exits nX fs hints maxBound)
    {g : Sym} (hg : g ∈ exits) : T.Defined M.host g := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
  refine ⟨M.code.length + i, ?_⟩
  rw [M.prog_host, List.getElem?_append_right (by omega), List.getElem?_map]; simp [hi]

/-- Module linking theorem over any host `h` containing `M.code` at `k₀` with unique labels. -/
theorem fnSpec (M : Compiled T lt extCallees exits nX fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1 (legalEnv lt (Env.ofModule mod Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ mod.fns.map Fn.name))
    (hexits : ∀ g ∈ exits, T.Defined h g) {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined h f.name ∧ T.FnSpec h f.name
      (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      (M.bound f.name) nX := by
  have hmemB : (f.name, M.bound f.name) ∈ M.bounds := M.bound_mem (hfs ▸ List.mem_map_of_mem hf)
  obtain ⟨f', hf', hnm, hdef, hspec⟩ :=
    compile_sound T h lt mod Γ extCallees exits nX hints M.code M.bounds k₀
      (hfs ▸ M.compileModule_eq) hc hu hacyc hwf hsupp hwp hext hext_uniq hexits
      (f.name, M.bound f.name) hmemB
  have hMnd : (mod.fns.map Fn.name).Nodup := by
    simp only [Module.checkAcyclic, Bool.and_eq_true] at hacyc
    exact (List.nodup_append.mp (mod.namesNodup_of_checkNamesNodup hacyc.1)).1
  have heqf : f = f' := fn_eq_of_mem_fns hMnd hf hf' hnm
  subst heqf; exact ⟨hdef, hspec⟩

/-- Module linking theorem specialized to `M.host` when `extCallees = []`. -/
theorem fnSpec_host (M : Compiled T lt [] exits nX fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (Γ : Env)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined M.host f.name ∧ T.FnSpec M.host f.name
      (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      (M.bound f.name) nX :=
  M.fnSpec mod hfs M.host Γ 0 M.code_infix_host M.labelsUnique hacyc hwf hsupp hwp
    (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    (fun _ hg => M.defined_exit_host hg) hf

/-- Source-level specialization of `fnSpec_host` when `lt.legalSig` fixes `(f.as, f.rs)` and `Γ`
is independent of exit continuations. -/
theorem fnSpec_host_src (M : Compiled T lt [] exits nX fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (Γ : Env)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns) (has : lt.legalSig f.as = f.as) (hbs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X') :
    T.Defined M.host f.name ∧ T.FnSpec M.host f.name (Γ f.name f.as f.rs) (M.bound f.name) nX := by
  obtain ⟨hdef, hspec⟩ := M.fnSpec_host mod hfs Γ hacyc hwf hsupp hwp hf
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq_noExit has hbs
    (List.mem_append_left _ (List.mem_map_of_mem hf)) hnoex hspec⟩

/-- Generic `FnSpec` wrapper for empty-extern, empty-exit modules over any host `h` when
`lt.legalSig` fixes `(f.as, f.rs)` and `Γ` ignores exit continuations. -/
theorem fnSpec_noExit_id (M : Compiled T lt [] [] nX fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    {f : Fn} (hf : f ∈ mod.fns) (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X') :
    T.Defined h f.name ∧ T.FnSpec h f.name (Γ f.name f.as f.rs) (M.bound f.name) nX := by
  obtain ⟨hdef, hspec⟩ := M.fnSpec mod hfs h Γ k₀ hc hu hacyc hwf hsupp hwp
    (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    (fun _ h => nomatch h) hf
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq_noExit has hrs
    (List.mem_append_left _ (List.mem_map_of_mem hf)) hnoex hspec⟩

end Compiled

/-- Lift a kernel `List.all` `supportsSource` check to a universal quantifier over `fs`. -/
theorem supportsAll_to_forall {lt : LegalTarget} {fs : List Fn}
    (h : fs.all (fun f => (f.earlyOpt).body.supportsSource lt) = true) :
    ∀ f ∈ fs, (f.earlyOpt).body.supportsSource lt = true :=
  fun f hf => List.all_eq_true.mp h f hf

/-- Single boolean predicate checked once by `t_kernel_rfl`, using structural `fnNameOk` +
`stringsNodup (fnNames ++ exits)` (no O(L²) scan over internal `.L` block labels). -/
def checkCompile (T : Target) (L : TargetLayout T) (lt : LegalTarget)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (fs : List Fn) (hints : List T.toIsa.Hints) (maxBound : Nat := 2048) : Bool :=
  checkCompileResult T.frame.label L.progSmall
    (compileModule T.toIsa lt T.frame.raBytes extCallees exits nX fs hints)
    (fs.map Fn.name) exits maxBound

/-- Construct `Compiled` from `checkCompile = true` and `hcl : Rega.LabelClean T.toIsa`. -/
def compileChecked (T : Target) (L : TargetLayout T) (lt : LegalTarget)
    (hcl : Rega.LabelClean T.toIsa) (extCallees : List (SigEntry × Nat)) (exits : List Sym)
    (nX : Nat) (fs : List Fn) (hints : List T.toIsa.Hints) (maxBound : Nat := 2048)
    (h : checkCompile T L lt extCallees exits nX fs hints maxBound = true) :
    Compiled T lt extCallees exits nX fs hints maxBound where
  code := extractCode (compileModule T.toIsa lt T.frame.raBytes extCallees exits nX fs hints)
  bounds := extractBounds (compileModule T.toIsa lt T.frame.raBytes extCallees exits nX fs hints)
  compileModule_eq := (checkCompileResult_parts h).1
  compile_eq := compile_of_compileModule (checkCompileResult_parts h).1
  bound_mem := fun hnm =>
    bound_mem_of_all (checkCompileResult_parts h).1 (checkCompileResult_parts h).2.2.2.2.2.2 hnm
  bound_le :=
    bound_le_of_all (checkCompileResult_parts h).1 (checkCompileResult_parts h).2.2.2.2.2.1
  host := L.layoutOf
    (extractCode (compileModule T.toIsa lt T.frame.raBytes extCallees exits nX fs hints) ++
      exits.map T.frame.label)
    (checkCompileResult_parts h).2.2.2.2.1
  prog_host := L.prog_layoutOf _ _
  labelsUnique := by
    have hp := checkCompileResult_parts h
    intro i j l hi hj; rw [L.prog_layoutOf _ hp.2.2.2.2.1] at hi hj
    exact compileModule_labelsUnique hcl hp.1 hp.2.2.2.1
      (by simp only [List.all_append, Bool.and_eq_true]; exact ⟨hp.2.1, hp.2.2.1⟩) i j l hi hj

/-- Variant boolean predicate checking label uniqueness via `L.labelsNodup`. -/
def checkCompileWithLabels (T : Target) (L : TargetLayout T) (lt : LegalTarget)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (fs : List Fn) (hints : List T.toIsa.Hints) (maxBound : Nat := 2048) : Bool :=
  checkCompileResultWithLabels T.frame.label L.labelsNodup L.progSmall
    (compileModule T.toIsa lt T.frame.raBytes extCallees exits nX fs hints)
    (fs.map Fn.name) exits maxBound

/-- Construct `Compiled` via `L.labelsNodup` and `L.labelsUnique_layoutOf` (for targets that
supply `stringsNodup` without `Rega.LabelClean`). -/
def compileCheckedWithLabels (T : Target) (L : TargetLayout T) (lt : LegalTarget)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (fs : List Fn) (hints : List T.toIsa.Hints) (maxBound : Nat := 2048)
    (h : checkCompileWithLabels T L lt extCallees exits nX fs hints maxBound = true) :
    Compiled T lt extCallees exits nX fs hints maxBound where
  code := extractCode (compileModule T.toIsa lt T.frame.raBytes extCallees exits nX fs hints)
  bounds := extractBounds (compileModule T.toIsa lt T.frame.raBytes extCallees exits nX fs hints)
  compileModule_eq := (checkWithLabels_parts h).1
  compile_eq := compile_of_compileModule (checkWithLabels_parts h).1
  bound_mem := fun hnm =>
    bound_mem_of_all (checkWithLabels_parts h).1 (checkWithLabels_parts h).2.2.2.2 hnm
  bound_le := bound_le_of_all (checkWithLabels_parts h).1 (checkWithLabels_parts h).2.2.2.1
  host := L.layoutOf
    (extractCode (compileModule T.toIsa lt T.frame.raBytes extCallees exits nX fs hints) ++
      exits.map T.frame.label)
    (checkWithLabels_parts h).2.2.1
  prog_host := L.prog_layoutOf _ _
  labelsUnique :=
    L.labelsUnique_layoutOf (checkWithLabels_parts h).2.2.1 (checkWithLabels_parts h).2.1

/-! ## Stack zeros and concrete execution harness (`TargetInit`) -/

/-- `n` zero bytes for concrete initial stack frames (irreducible so tactics do not unfold `n`). -/
def stackZeros (n : Nat) : List UInt8 := List.replicate n 0

theorem stackZeros_length (n : Nat) : (stackZeros n).length = n := List.length_replicate

attribute [irreducible] stackZeros

/-- Concrete initial-state parameters for closed execution witnesses over typed `Tup Val as` /
`Tup Val [t]` contracts on target `T`. -/
structure TargetInit (T : Target) (maxStack : Nat := 2048) (maxMem : Nat := 8192) where
  sp0 : BitVec 64
  ra0 : T.mach.Addr
  ret0 : T.Reg
  arg0 : T.Reg
  initState : Nat → List UInt8 → {as : List Ty} → Tup Val as → T.mach.MData
  get_sp : ∀ n bs {as : List Ty} (args : Tup Val as),
    T.mach.getGpr (initState n bs args) T.frame.sp = sp0
  argsIn : ∀ n bs {as : List Ty} (args : Tup Val as),
    (T.toIsa.assignArgs as).isSome = true → T.ArgsIn args (initState n bs args)
  raReg : ∀ n bs {as : List Ty} (args : Tup Val as), T.frameSpec.raReg (initState n bs args) ra0
  spEntry : T.frameSpec.spEntry sp0
  mem_entry : ∀ n bs {as : List Ty} (args : Tup Val as), n ≤ maxStack → bs.length ≤ maxMem →
    (T.mach.mem (initState n bs args) =⋆
      Eq (bs.At 0x1000#64) ⋆ T.Entry sp0 ra0 n ⋆ Std.ExtHashMap.emp)
  retsIn_singleton : ∀ (v : Val i64) (s : T.mach.MData),
    T.RetsIn (bs := [i64]) (v, ()) s → T.mach.getGpr s ret0 = v
  argsIn_singleton : ∀ (v : Val i64) (s : T.mach.MData),
    T.ArgsIn (as := [i64]) (v, ()) s → T.mach.getGpr s arg0 = v

section TargetInitHelpers

variable {T : Target} {maxStack maxMem : Nat} (I : TargetInit T maxStack maxMem)
  {lt : LegalTarget} {extCallees : List (SigEntry × Nat)} {exits : List Sym}
  {nX : Nat} {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}

/-- Run a function `nm` in `M.host` from `I.initState (M.bound nm) bsMem args` using `hf`. -/
theorem TargetInit.run_fnSpec (M : Compiled T lt extCallees exits nX fs hints maxBound)
    {nm : Sym} {as bs : List Ty} {spec : Spec as bs} (hf : T.FnSpec M.host nm spec (M.bound nm) nX)
    (bsMem : List UInt8) (args : Tup Val as) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs as).isSome = true) {Q : Post bs} {X : XPost}
    (hspec : spec args (bsMem.At 0x1000#64) Q X) {post : T.mach.State → Prop}
    (hpost : ∀ st, (T.mach.pc st = I.ra0 ∧ ∃ rets m', Q rets m' ∧ T.RetsIn rets (T.mach.data st) ∧
        (T.mach.mem (T.mach.data st) =⋆ Eq m' ⋆ T.Exit I.sp0 (M.bound nm) ⋆ Std.ExtHashMap.emp)) ∨
      (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64), X sym' cs xs m' ∧
        T.mach.pc st = T.mach.labelAddr M.host sym' ∧ T.ArgsIn xs (T.mach.data st)) → post st)
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step M.host) post
      (T.mach.mkState (I.initState (M.bound nm) bsMem args) (T.mach.labelAddr M.host nm)) := by
  have hmem := I.mem_entry (M.bound nm) bsMem args (Nat.le_trans (M.bound_le_max nm) hbound) hbs
  rw [← I.get_sp (M.bound nm) bsMem args] at hmem
  refine eventually_weaken _ _ _ _ ?_ (hf args (bsMem.At 0x1000#64) Q X hspec
    (I.initState (M.bound nm) bsMem args) I.ra0 Std.ExtHashMap.emp (I.argsIn _ _ _ hargs)
    (I.raReg _ _ _) (by rw [I.get_sp]; exact I.spEntry) hmem)
  rintro st (⟨hpc, rets, m', hQ, hrets, _, hm'⟩ | ⟨sym', cs, xs, m', hX, _, hpc, has, _⟩)
  · rw [I.get_sp] at hm'; exact hpost st (Or.inl ⟨hpc, rets, m', hQ, hrets, hm'⟩)
  · exact hpost st (Or.inr ⟨sym', cs, xs, m', hX, hpc, has⟩)

/-- Run a non-exiting function returning a typed singleton `(v, ()) : Tup Val [t]`. -/
theorem TargetInit.run_ret1 (M : Compiled T lt extCallees exits nX fs hints maxBound)
    {nm : Sym} {as : List Ty} {t : Ty} {spec : Spec as [t]}
    (hf : T.FnSpec M.host nm spec (M.bound nm) nX) (bsMem : List UInt8) (args : Tup Val as)
    (v : Val t) (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs as).isSome = true)
    {Q : Post [t]} (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step M.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.RetsIn (bs := [t]) (v, ()) (T.mach.data st))
      (T.mach.mkState (I.initState (M.bound nm) bsMem args) (T.mach.labelAddr M.host nm)) := by
  refine I.run_fnSpec M hf bsMem args hbs hargs hspec ?_ hbound
  rintro st (⟨hpc, rets, m', hq, hrets, _⟩ | ⟨_, _, _, _, hx, _⟩)
  · have hr := hQ rets m' hq; subst hr; exact ⟨hpc, hrets⟩
  · exact hx.elim

/-- Specialization of `run_ret1` to `i64`, projecting the return value directly to `I.ret0`. -/
theorem TargetInit.run_ret1_i64 (M : Compiled T lt extCallees exits nX fs hints maxBound)
    {nm : Sym} {as : List Ty} {spec : Spec as [i64]}
    (hf : T.FnSpec M.host nm spec (M.bound nm) nX) (bsMem : List UInt8) (args : Tup Val as)
    (v : Val i64) (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs as).isSome = true)
    {Q : Post [i64]} (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step M.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v)
      (T.mach.mkState (I.initState (M.bound nm) bsMem args) (T.mach.labelAddr M.host nm)) :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, I.retsIn_singleton v _ h.2⟩)
    (I.run_ret1 M hf bsMem args v hbs hargs hspec hQ hbound)

/-- Run a non-exiting function returning `(v, ()) : Tup Val [t]` and establishing `P`. -/
theorem TargetInit.run_ret1_sep (M : Compiled T lt extCallees exits nX fs hints maxBound)
    {nm : Sym} {as : List Ty} {t : Ty} {spec : Spec as [t]}
    (hf : T.FnSpec M.host nm spec (M.bound nm) nX) (bsMem : List UInt8) (args : Tup Val as)
    (v : Val t) (P : Mem 64 → Prop) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs as).isSome = true) {Q : Post [t]}
    (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()) ∧ P m')
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step M.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.RetsIn (bs := [t]) (v, ()) (T.mach.data st) ∧
        (T.mach.mem (T.mach.data st) =⋆ P ⋆ T.Exit I.sp0 (M.bound nm) ⋆ Std.ExtHashMap.emp))
      (T.mach.mkState (I.initState (M.bound nm) bsMem args) (T.mach.labelAddr M.host nm)) := by
  refine I.run_fnSpec M hf bsMem args hbs hargs hspec ?_ hbound
  rintro st (⟨hpc, rets, m', hq, hrets, hm'⟩ | ⟨_, _, _, _, hx, _⟩)
  · obtain ⟨rfl, hP⟩ := hQ rets m' hq
    exact ⟨hpc, hrets, sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP)) hm'⟩
  · exact hx.elim

/-- Specialization of `run_ret1_sep` to `i64`, projecting the return value directly to `I.ret0`. -/
theorem TargetInit.run_ret1_sep_i64 (M : Compiled T lt extCallees exits nX fs hints maxBound)
    {nm : Sym} {as : List Ty} {spec : Spec as [i64]}
    (hf : T.FnSpec M.host nm spec (M.bound nm) nX) (bsMem : List UInt8) (args : Tup Val as)
    (v : Val i64) (P : Mem 64 → Prop) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs as).isSome = true) {Q : Post [i64]}
    (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()) ∧ P m')
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step M.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v ∧
        (T.mach.mem (T.mach.data st) =⋆ P ⋆ T.Exit I.sp0 (M.bound nm) ⋆ Std.ExtHashMap.emp))
      (T.mach.mkState (I.initState (M.bound nm) bsMem args) (T.mach.labelAddr M.host nm)) :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, I.retsIn_singleton v _ h.2.1, h.2.2⟩)
    (I.run_ret1_sep M hf bsMem args v P hbs hargs hspec hQ hbound)

end TargetInitHelpers

end LeanQbe.T
