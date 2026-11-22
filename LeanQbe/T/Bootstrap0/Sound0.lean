module

public import LeanQbe.T.Bootstrap0.Sound0Part12
import LeanQbe.T.TargetLemmas
import LeanQbe.T.AbiLemmas
import LeanQbe.T.FlatLemmas

/-!
# Bootstrap Stage B (`Sound0`): End-to-End `leanqbe0Compile` Semantic Soundness

Composes Stage-B per-function soundness (`Sound0Part12.compileFn0_fnSpec` and `compileFn0_defined`)
with module-level loop decomposition (`compileModuleLoop0`), cross-function label uniqueness
(`label0ToSym` / `compileModuleLoop0_host_labelsUnique`), call-acyclic `NodeContracts0` lifting,
`PrintAsm0` assembly equivalence (`toAmd64Program_printAsm0` / `toAmd64Program_printModule0`), and
the `Bridge0.ofTFlatModule` frontend pipeline (`bridge_leanqbe0Compile_fnSpec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T
open LeanQbe.T.Amd64
open Std Std.ExtHashMap

/-! ## 1. `UInt32` Arithmetic & `compileModuleLoop0` Decomposition -/

private theorem u32_ext0 {a b : UInt32} (h : a.toNat = b.toNat) : a = b :=
  UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

private theorem u32_toNat_ofNat0 (n : Nat) : (UInt32.ofNat n).toNat = n % 2 ^ 32 := by
  rw [← UInt32.toNat_toBitVec]
  exact BitVec.toNat_ofNat n 32

private theorem u32_add_assoc_one0 (a : UInt32) (k : Nat) :
    a + UInt32.ofNat (k + 1) = (a + 1) + UInt32.ofNat k := by
  apply u32_ext0
  rw [UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_one,
    u32_toNat_ofNat0, u32_toNat_ofNat0, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_mod_mod,
    Nat.add_assoc, Nat.add_comm k 1]

private theorem u32_add_zero0 (a : UInt32) : a + UInt32.ofNat 0 = a := by
  apply u32_ext0
  rw [UInt32.toNat_add, u32_toNat_ofNat0, Nat.zero_mod, Nat.add_zero,
    Nat.mod_eq_of_lt (UInt32.toNat_lt a)]

private theorem u32_add_ofNat_lt0 {a : UInt32} {k : Nat} (h : a.toNat + k < 2 ^ 32) :
    (a + UInt32.ofNat k).toNat = a.toNat + k := by
  rw [UInt32.toNat_add, u32_toNat_ofNat0,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h), Nat.mod_eq_of_lt h]

private theorem u32Max0_ge (a b : UInt32) :
    a.toNat ≤ (u32Max0 a b).toNat ∧ b.toNat ≤ (u32Max0 a b).toNat := by
  dsimp only [u32Max0]
  split
  · rename_i h
    exact ⟨Nat.le_of_lt (by simpa [UInt32.lt_iff_toNat_lt] using h), Nat.le_refl _⟩
  · rename_i h
    have hge : b.toNat ≤ a.toNat := Nat.le_of_not_lt (by
      simpa [UInt32.lt_iff_toNat_lt] using h)
    exact ⟨Nat.le_refl _, hge⟩

/-- `compileModuleLoop0` preserves `revAcc.reverse` as a prefix and its directives do not depend on
`maxSl`. -/
theorem compileModuleLoop0_fst_acc (fns : List TFlatFn0) (idx maxSl : UInt32)
    (revAcc : List Dir0) :
    (compileModuleLoop0 fns idx maxSl revAcc).1 =
      revAcc.reverse ++ (compileModuleLoop0 fns idx 0 []).1 := by
  induction fns generalizing idx maxSl revAcc with
  | nil =>
    dsimp only [compileModuleLoop0]
    rw [revDirAux0_eq, revDirAux0_eq]
    simp only [List.reverse_nil, List.append_nil]
  | cons fn rest ih =>
    dsimp only [compileModuleLoop0]
    rw [ih (idx + 1) (u32Max0 maxSl (compileFn0 idx fn).2)
        (revDirAux0 (compileFn0 idx fn).1 revAcc)]
    rw [ih (idx + 1) (u32Max0 0 (compileFn0 idx fn).2)
        (revDirAux0 (compileFn0 idx fn).1 [])]
    simp only [revDirAux0_eq, List.append_nil, List.reverse_append, List.reverse_reverse,
      List.append_assoc]

/-- The emitted directive list `(compileModuleLoop0 fns idx maxSl []).1` is independent of
`maxSl`. -/
theorem compileModuleLoop0_fst_maxSl (fns : List TFlatFn0) (idx maxSl : UInt32) :
    (compileModuleLoop0 fns idx maxSl []).1 = (compileModuleLoop0 fns idx 0 []).1 := by
  simpa only [List.reverse_nil, List.nil_append] using
    compileModuleLoop0_fst_acc fns idx maxSl []

/-- Single-step unfolding of `(compileModuleLoop0 (fn :: rest) idx maxSl []).1`. -/
theorem compileModuleLoop0_cons (fn : TFlatFn0) (rest : List TFlatFn0) (idx maxSl : UInt32) :
    (compileModuleLoop0 (fn :: rest) idx maxSl []).1 =
      (compileFn0 idx fn).1 ++ (compileModuleLoop0 rest (idx + 1) 0 []).1 := by
  dsimp only [compileModuleLoop0]
  rw [compileModuleLoop0_fst_acc, revDirAux0_eq, List.append_nil, List.reverse_reverse]

/-- Splitting `compileModuleLoop0` directives across `xs ++ ys`. -/
theorem compileModuleLoop0_append (xs ys : List TFlatFn0) (idx maxSl : UInt32) :
    (compileModuleLoop0 (xs ++ ys) idx maxSl []).1 =
      (compileModuleLoop0 xs idx 0 []).1 ++
        (compileModuleLoop0 ys (idx + UInt32.ofNat xs.length) 0 []).1 := by
  induction xs generalizing idx maxSl with
  | nil =>
    dsimp only [List.nil_append, List.length_nil]
    rw [u32_add_zero0, compileModuleLoop0_fst_maxSl]
    rfl
  | cons fn rest ih =>
    dsimp only [List.cons_append, List.length_cons]
    rw [compileModuleLoop0_cons, ih (idx + 1) 0, compileModuleLoop0_cons (idx := idx),
      u32_add_assoc_one0, List.append_assoc]

/-- Prefix/infix embedding for a single compiled function inside `compileModuleLoop0`. -/
theorem compileModuleLoop0_fn_infix {pre : List TFlatFn0} {fn : TFlatFn0} {post : List TFlatFn0}
    {symName : Sym0 → Sym} {h : Host} {k₀ : Nat} (idx maxSl : UInt32)
    (hinf : (toAmd64Program symName
      (compileModuleLoop0 (pre ++ fn :: post) idx maxSl []).1).IsInfixAt
      (x64ScalarMach.prog h) k₀) :
    (toAmd64Program symName (compileFn0 (idx + UInt32.ofNat pre.length) fn).1).IsInfixAt
      (x64ScalarMach.prog h)
      (k₀ + (toAmd64Program symName (compileModuleLoop0 pre idx 0 []).1).length) := by
  rw [compileModuleLoop0_append, compileModuleLoop0_cons, toAmd64Program_append,
    toAmd64Program_append] at hinf
  exact hinf.append.2.append.1

/-- `compileModuleLoop0`'s final `maxSl` bounds both the initial accumulator and every compiled
function's peak slot count. -/
theorem compileModuleLoop0_maxSl_ge (fns : List TFlatFn0) (idx maxSl : UInt32)
    (revAcc : List Dir0) :
    maxSl.toNat ≤ (compileModuleLoop0 fns idx maxSl revAcc).2.toNat ∧
    ∀ pre fn post, fns = pre ++ fn :: post →
      (compileFn0 (idx + UInt32.ofNat pre.length) fn).2.toNat ≤
        (compileModuleLoop0 fns idx maxSl revAcc).2.toNat := by
  induction fns generalizing idx maxSl revAcc with
  | nil =>
    dsimp only [compileModuleLoop0]
    refine ⟨Nat.le_refl _, fun pre _ _ hsp => ?_⟩
    cases pre <;> simp at hsp
  | cons g rest ih =>
    dsimp only [compileModuleLoop0]
    have hmx := u32Max0_ge maxSl (compileFn0 idx g).2
    have hih := ih (idx + 1) (u32Max0 maxSl (compileFn0 idx g).2)
      (revDirAux0 (compileFn0 idx g).1 revAcc)
    refine ⟨Nat.le_trans hmx.1 hih.1, fun pre fn post hsp => ?_⟩
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hsp
      rcases hsp with ⟨rfl, rfl⟩
      rw [List.length_nil, u32_add_zero0]
      exact Nat.le_trans hmx.2 hih.1
    | cons p pre' =>
      simp only [List.cons_append, List.cons.injEq] at hsp
      rcases hsp with ⟨rfl, hrest⟩
      simp only [List.length_cons]
      rw [u32_add_assoc_one0]
      exact hih.2 pre' fn post hrest

/-! ## 2. Cross-Function Label Injectivity & `x64ScalarTarget.LabelsUnique` -/

/-- Structural check rejecting `".L_*"` internal label prefixes on symbol names. -/
@[expose] def symNoLocPrefix0 (s : Sym) : Bool :=
  match s.toList with
  | '.' :: 'L' :: '_' :: _ => false
  | _ => true

theorem symNoLocPrefix0_of_fnNameOk {s : Sym} (h : fnNameOk s = true) :
    symNoLocPrefix0 s = true := by
  dsimp only [fnNameOk, Bool.not_eq_true'] at h
  dsimp only [symNoLocPrefix0]
  cases hcs : s.toList with
  | nil => rfl
  | cons a r1 =>
    by_cases ha : a = '.'
    · subst ha; cases r1 with
      | nil => rfl
      | cons b r2 =>
        by_cases hb : b = 'L'
        · subst hb; cases r2 with
          | nil => rfl
          | cons c r3 =>
            by_cases hc : c = '_'
            · subst hc; rw [hcs] at h; cases h
            · split <;> simp_all
        · split <;> simp_all
    · split <;> simp_all

private theorem nat_repr_inj {m n : Nat} (h : Nat.repr m = Nat.repr n) : m = n := by
  have hl : (Nat.repr m).toList = (Nat.repr n).toList := congrArg String.toList h
  rw [Nat.toList_repr, Nat.toList_repr] at hl
  have hp := congrArg (fun ds => Nat.ofDigitChars 10 ds 0) hl
  rwa [Nat.ofDigitChars_ten_toDigits, Nat.ofDigitChars_ten_toDigits] at hp

private theorem nat_repr_no_underscore (n : Nat) :
    ∀ c ∈ (Nat.repr n).toList, c ≠ '_' := by
  rw [Nat.toList_repr]
  intro c hc he
  subst he
  exact Nat.underscore_not_in_toDigits hc

private theorem split_at_underscore :
    ∀ {xs₁ ys₁ xs₂ ys₂ : List Char},
      (∀ c ∈ xs₁, c ≠ '_') → (∀ c ∈ xs₂, c ≠ '_') →
      xs₁ ++ '_' :: ys₁ = xs₂ ++ '_' :: ys₂ → xs₁ = xs₂ ∧ ys₁ = ys₂
  | [], ys₁, [], ys₂, _, _, h => by cases h; exact ⟨rfl, rfl⟩
  | [], _, x :: _, _, _, hx2, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd h.1.symm (hx2 x List.mem_cons_self)
  | x :: _, _, [], _, hx1, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd h.1 (hx1 x List.mem_cons_self)
  | x :: xs₁, ys₁, y :: xs₂, ys₂, hx1, hx2, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    rcases h with ⟨rfl, htail⟩
    have ih := split_at_underscore (fun c hc => hx1 c (List.mem_cons_of_mem _ hc))
      (fun c hc => hx2 c (List.mem_cons_of_mem _ hc)) htail
    exact ⟨congrArg (x :: ·) ih.1, ih.2⟩

/-- `.L_{fn}_{lbl}` label strings have prefix `".L_"` (`symNoLocPrefix0 = false`). -/
theorem symNoLocPrefix0_loc {symName : Sym0 → Sym} (fnId lblId : UInt32) :
    symNoLocPrefix0 (label0ToSym symName (.loc fnId lblId)) = false := by
  change symNoLocPrefix0 (".L_" ++ Nat.repr fnId.toNat ++ "_" ++ Nat.repr lblId.toNat) = false
  dsimp only [symNoLocPrefix0]
  rw [String.toList_append, String.toList_append, String.toList_append]
  simp only [List.append_assoc]
  rfl

/-- `.L_{fn₁}_{lbl₁} = .L_{fn₂}_{lbl₂}` implies `fn₁ = fn₂ ∧ lbl₁ = lbl₂`. -/
theorem label0ToSym_loc_inj {symName : Sym0 → Sym} {fn₁ lbl₁ fn₂ lbl₂ : UInt32}
    (h : label0ToSym symName (.loc fn₁ lbl₁) = label0ToSym symName (.loc fn₂ lbl₂)) :
    fn₁ = fn₂ ∧ lbl₁ = lbl₂ := by
  have hl := congrArg String.toList h
  change (".L_" ++ Nat.repr fn₁.toNat ++ "_" ++ Nat.repr lbl₁.toNat).toList =
    (".L_" ++ Nat.repr fn₂.toNat ++ "_" ++ Nat.repr lbl₂.toNat).toList at hl
  rw [String.toList_append, String.toList_append, String.toList_append,
    String.toList_append, String.toList_append, String.toList_append] at hl
  simp only [List.append_assoc] at hl
  change '.' :: 'L' :: '_' :: ((Nat.repr fn₁.toNat).toList ++
      '_' :: (Nat.repr lbl₁.toNat).toList) =
    '.' :: 'L' :: '_' :: ((Nat.repr fn₂.toNat).toList ++
      '_' :: (Nat.repr lbl₂.toNat).toList) at hl
  injection hl with _ hl1
  injection hl1 with _ hl2
  injection hl2 with _ hl3
  obtain ⟨hf, hl'⟩ := split_at_underscore (nat_repr_no_underscore fn₁.toNat)
    (nat_repr_no_underscore fn₂.toNat) hl3
  have hf_nat := nat_repr_inj (String.ext hf)
  have hl_nat := nat_repr_inj (String.ext hl')
  exact ⟨u32_ext0 hf_nat, u32_ext0 hl_nat⟩

theorem label0ToSym_loc_ne_sym {symName : Sym0 → Sym} {fnId lblId : UInt32} {s : Sym}
    (hs : symNoLocPrefix0 s = true) :
    label0ToSym symName (.loc fnId lblId) ≠ s := fun he => by
  have h1 := congrArg symNoLocPrefix0 he
  rw [symNoLocPrefix0_loc, hs] at h1
  cases h1

private theorem dir0ToAmd64_label_iff (symName : Sym0 → Sym) (d0 : Dir0) (l : Sym) :
    x64Frame.label l ∈ dir0ToAmd64 symName d0 ↔
      ∃ l0, d0 = .label l0 ∧ l = label0ToSym symName l0 := by
  cases d0 with
  | label l0 => simp [dir0ToAmd64]
  | jmp _ => simp [dir0ToAmd64, x64JmpD]
  | callSym _ => simp [dir0ToAmd64, x64CallD]
  | ret => simp [dir0ToAmd64, x64RetD]
  | jcc _ _ | setcc _ _ | shMaskCl _ | testbRR _ _ | mulq _
  | ldSlot _ _ | stSlot _ _ | ldSlotIdx _ _ | stSlotIdx _ _ =>
    simp [dir0ToAmd64]
  | movRI _ _ => simp [dir0ToAmd64, moviD]
  | spAdd isSub _ =>
    cases isSub <;> simp [dir0ToAmd64, x64SubSpD, x64AddSpD]
  | spAddReg isSub _ =>
    cases isSub <;> simp [dir0ToAmd64]
  | movRR w _ _ | cmpRR w _ _ | cmovcc w _ _ _ =>
    cases w <;> simp [dir0ToAmd64, insW]
  | unary w isNeg _ =>
    cases w <;> cases isNeg <;> simp [dir0ToAmd64, insW]
  | movzx32 w _ _ | ldMem w _ _ =>
    cases w <;> simp [dir0ToAmd64]
  | stMem w _ _ =>
    cases w <;> simp [dir0ToAmd64, insW]
  | movsx wd _ ws _ =>
    cases wd <;> cases ws
    all_goals first | (simp [dir0ToAmd64]; done) | (simp [dir0ToAmd64, insW]; done)
  | aluRR w k _ _ =>
    cases w <;> cases k <;> simp [dir0ToAmd64, insW]
  | shiftCl w k _ =>
    cases w <;> cases k <;> simp [dir0ToAmd64, insW]
  | divCore w isS _ =>
    cases w <;> cases isS
    all_goals first
      | (simp [dir0ToAmd64]; done)
      | (simp [dir0ToAmd64, insW]; done)
      | (simp [dir0ToAmd64, moviD]; done)
      | (simp [dir0ToAmd64, insW, moviD]; done)

private theorem toAmd64Program_labOk0 (symName : Sym0 → Sym) (S : Label0 → Prop)
    (dirs : List Dir0) (hlab : LabOk0 S dirs)
    (hinj : ∀ l₁ l₂, S l₁ → S l₂ → label0ToSym symName l₁ = label0ToSym symName l₂ → l₁ = l₂) :
    (∀ (i : Nat) (l : Sym), (toAmd64Program symName dirs)[i]? = some (x64Frame.label l) →
      ∃ l0, S l0 ∧ l = label0ToSym symName l0) ∧
    (∀ (i j : Nat) (l : Sym),
      (toAmd64Program symName dirs)[i]? = some (x64Frame.label l) →
      (toAmd64Program symName dirs)[j]? = some (x64Frame.label l) → i = j) := by
  induction dirs with
  | nil =>
    exact ⟨fun _ _ h => by simp [toAmd64Program] at h,
           fun _ _ _ h => by simp [toAmd64Program] at h⟩
  | cons d0 rest ih =>
    have hrest : LabOk0 S rest :=
      ⟨fun i j l hi hj => by
          have := hlab.1 (i + 1) (j + 1) l (by simpa using hi) (by simpa using hj)
          omega,
        fun l hl => hlab.2 l (List.mem_cons_of_mem _ hl)⟩
    obtain ⟨ih_mem, ih_uniq⟩ := ih hrest
    have hprog_cons : toAmd64Program symName (d0 :: rest) =
        dir0ToAmd64 symName d0 ++ toAmd64Program symName rest := by
      dsimp only [toAmd64Program]; exact List.flatMap_cons
    by_cases hdl : ∃ l0, d0 = .label l0
    · obtain ⟨l0, rfl⟩ := hdl
      have hS0 : S l0 := hlab.2 l0 List.mem_cons_self
      have hnin_rest : .label l0 ∉ rest := fun hm => by
        obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hm
        have hget : (Dir0.label l0 :: rest)[k + 1]? = some (.label l0) := by
          simp only [List.getElem?_cons_succ]; rw [List.getElem?_eq_getElem hk, he]
        have := hlab.1 0 (k + 1) l0 rfl hget
        omega
      have hnin_prog : x64Frame.label (label0ToSym symName l0) ∉
          toAmd64Program symName rest := fun hm => by
        dsimp only [toAmd64Program] at hm
        rw [List.mem_flatMap] at hm
        obtain ⟨d', hd', hdl'⟩ := hm
        obtain ⟨l2, rfl, hl2⟩ := (dir0ToAmd64_label_iff symName d' _).mp hdl'
        have heq2 := hinj l0 l2 hS0 (hlab.2 l2 (List.mem_cons_of_mem _ hd')) hl2
        subst heq2; exact hnin_rest hd'
      have hhead : dir0ToAmd64 symName (.label l0) = [x64Frame.label (label0ToSym symName l0)] :=
        rfl
      rw [hprog_cons, hhead, List.singleton_append]
      constructor
      · intro i l hi
        cases i with
        | zero => simp at hi; subst hi; exact ⟨l0, hS0, rfl⟩
        | succ k => exact ih_mem k l hi
      · intro i j l hi hj
        cases i with
        | zero =>
          simp at hi; subst hi
          cases j with
          | zero => rfl
          | succ j' =>
            simp only [List.getElem?_cons_succ] at hj
            exact absurd (List.mem_of_getElem? hj) hnin_prog
        | succ i' =>
          cases j with
          | zero =>
            simp at hj; subst hj
            simp only [List.getElem?_cons_succ] at hi
            exact absurd (List.mem_of_getElem? hi) hnin_prog
          | succ j' => exact congrArg Nat.succ (ih_uniq i' j' l hi hj)
    · have hnol : ∀ (x : Sym), x64Frame.label x ∉ dir0ToAmd64 symName d0 := fun x hx => by
        obtain ⟨l0, he, _⟩ := (dir0ToAmd64_label_iff symName d0 x).mp hx
        exact hdl ⟨l0, he⟩
      let m := (dir0ToAmd64 symName d0).length
      constructor
      · intro i l hi
        rw [hprog_cons] at hi
        by_cases hlt : i < m
        · rw [List.getElem?_append_left hlt] at hi
          exact absurd (List.mem_of_getElem? hi) (hnol l)
        · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hi
          exact ih_mem (i - m) l hi
      · intro i j l hi hj
        rw [hprog_cons] at hi hj
        by_cases hilt : i < m <;> by_cases hjlt : j < m
        · rw [List.getElem?_append_left hilt] at hi
          exact absurd (List.mem_of_getElem? hi) (hnol l)
        · rw [List.getElem?_append_left hilt] at hi
          exact absurd (List.mem_of_getElem? hi) (hnol l)
        · rw [List.getElem?_append_left hjlt] at hj
          exact absurd (List.mem_of_getElem? hj) (hnol l)
        · rw [List.getElem?_append_right (Nat.le_of_not_lt hilt)] at hi
          rw [List.getElem?_append_right (Nat.le_of_not_lt hjlt)] at hj
          have heq := ih_uniq (i - m) (j - m) l hi hj
          omega

/-- Characterization of all AT&T label directives emitted across `fns` by `compileModuleLoop0`. -/
@[expose] def modCodeLabelsPred0 (symName : Sym0 → Sym) (fns : List TFlatFn0) (idx0 : UInt32)
    (l : Sym) : Prop :=
  (∃ fn ∈ fns, l = symName fn.name) ∨
  ∃ (k : Nat) (_hk : k < fns.length) (j : UInt32),
    1 ≤ j.toNat ∧ j.toNat < 2 ^ 31 ∧
    l = label0ToSym symName (.loc (idx0 + UInt32.ofNat k) j)

/-- Structural label-membership & cross-function uniqueness for `compileModuleLoop0`. -/
theorem compileModuleLoop0_code_labels (symName : Sym0 → Sym) :
    ∀ (fns : List TFlatFn0) (idx0 maxSl : UInt32),
      idx0.toNat + fns.length < 2 ^ 32 →
      (∀ fn ∈ fns, fn.okGuardsFull = true) →
      (fns.map (fun fn => symName fn.name)).Nodup →
      (∀ fn ∈ fns, symNoLocPrefix0 (symName fn.name) = true) →
      let code := toAmd64Program symName (compileModuleLoop0 fns idx0 maxSl []).1
      (∀ (i : Nat) (l : Sym), code[i]? = some (x64Frame.label l) →
        modCodeLabelsPred0 symName fns idx0 l) ∧
      (∀ (i j : Nat) (l : Sym), code[i]? = some (x64Frame.label l) →
        code[j]? = some (x64Frame.label l) → i = j)
  | [], _, _, _, _, _, _ => by
    dsimp only [compileModuleLoop0, revDirAux0, toAmd64Program, List.flatMap_nil]
    exact ⟨fun _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩
  | fn :: rest, idx0, maxSl, hidx_bd, hg_all, hnd, hnoloc => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    have hg_fn : fn.okGuardsFull = true := hg_all fn List.mem_cons_self
    have hg_rest : ∀ g ∈ rest, g.okGuardsFull = true := fun g hg =>
      hg_all g (List.mem_cons_of_mem _ hg)
    have hnoloc_fn : symNoLocPrefix0 (symName fn.name) = true := hnoloc fn List.mem_cons_self
    have hnoloc_rest : ∀ g ∈ rest, symNoLocPrefix0 (symName g.name) = true := fun g hg =>
      hnoloc g (List.mem_cons_of_mem _ hg)
    have hidx1 : (idx0 + 1).toNat = idx0.toNat + 1 := by
      rw [UInt32.toNat_add, UInt32.toNat_one,
        Nat.mod_eq_of_lt (by simp only [List.length_cons] at hidx_bd; omega)]
    have hbd_rest : (idx0 + 1).toNat + rest.length < 2 ^ 32 := by
      rw [hidx1]; simp only [List.length_cons] at hidx_bd; omega
    obtain ⟨ih_mem, ih_uniq⟩ :=
      compileModuleLoop0_code_labels symName rest (idx0 + 1) 0 hbd_rest hg_rest hnd.2 hnoloc_rest
    let Sfn : Label0 → Prop := fun l =>
      l = .sym fn.name ∨ ∃ j : UInt32, 1 ≤ j.toNat ∧ j.toNat < 2 ^ 31 ∧ l = .loc idx0 j
    have hlab_fn := (compileFn0_labOk0 idx0 fn hg_fn).2
    have hinj_fn : ∀ l₁ l₂, Sfn l₁ → Sfn l₂ →
        label0ToSym symName l₁ = label0ToSym symName l₂ → l₁ = l₂ := by
      rintro l₁ l₂ (rfl | ⟨j₁, _, _, rfl⟩) (rfl | ⟨j₂, _, _, rfl⟩) he
      · rfl
      · exact absurd he.symm (label0ToSym_loc_ne_sym hnoloc_fn)
      · exact absurd he (label0ToSym_loc_ne_sym hnoloc_fn)
      · obtain ⟨_, hj⟩ := label0ToSym_loc_inj he; subst hj; rfl
    obtain ⟨hc_mem, hc_uniq⟩ := toAmd64Program_labOk0 symName Sfn _ hlab_fn hinj_fn
    let c := toAmd64Program symName (compileFn0 idx0 fn).1
    let cs := toAmd64Program symName (compileModuleLoop0 rest (idx0 + 1) 0 []).1
    have hcode_eq : toAmd64Program symName (compileModuleLoop0 (fn :: rest) idx0 maxSl []).1 =
        c ++ cs := by
      rw [compileModuleLoop0_cons, toAmd64Program_append]
    have hfn_pred : ∀ (i : Nat) l, c[i]? = some (x64Frame.label l) →
        modCodeLabelsPred0 symName (fn :: rest) idx0 l := by
      intro i l hi
      obtain ⟨l0, (rfl | ⟨j, hj1, hj2, rfl⟩), rfl⟩ := hc_mem i l hi
      · exact Or.inl ⟨fn, List.mem_cons_self, rfl⟩
      · refine Or.inr ⟨0, by simp, j, hj1, hj2, ?_⟩
        rw [u32_add_zero0]
    have hrest_pred : ∀ (i : Nat) l, cs[i]? = some (x64Frame.label l) →
        modCodeLabelsPred0 symName (fn :: rest) idx0 l := by
      intro i l hi
      rcases ih_mem i l hi with ⟨g, hg, rfl⟩ | ⟨k, hk, j, hj1, hj2, rfl⟩
      · exact Or.inl ⟨g, List.mem_cons_of_mem _ hg, rfl⟩
      · refine Or.inr ⟨k + 1, by simp only [List.length_cons]; omega, j, hj1, hj2, ?_⟩
        rw [u32_add_assoc_one0]
    have hdisj : ∀ (i₁ j₁ : Nat) l, c[i₁]? = some (x64Frame.label l) →
        cs[j₁]? = some (x64Frame.label l) → False := by
      intro i₁ j₁ l hi₁ hj₁
      obtain ⟨l0, hl0, rfl⟩ := hc_mem i₁ l hi₁
      rcases ih_mem j₁ _ hj₁ with ⟨g, hg, hl_eq⟩ | ⟨k, hk, j₂, _, _, hl_eq⟩
      · rcases hl0 with rfl | ⟨j, _, _, rfl⟩
        · exact hnd.1 g hg hl_eq.symm
        · exact label0ToSym_loc_ne_sym (hnoloc_rest g hg) hl_eq
      · rcases hl0 with rfl | ⟨j₁, _, _, rfl⟩
        · exact label0ToSym_loc_ne_sym hnoloc_fn hl_eq.symm
        · obtain ⟨hidx_eq, _⟩ := label0ToSym_loc_inj hl_eq
          have h1 : idx0.toNat = ((idx0 + 1) + UInt32.ofNat k).toNat :=
            congrArg UInt32.toNat hidx_eq
          rw [u32_add_ofNat_lt0 (by omega), hidx1] at h1
          omega
    dsimp only
    rw [hcode_eq]
    constructor
    · intro i l hi
      by_cases hilt : i < c.length
      · rw [List.getElem?_append_left hilt] at hi; exact hfn_pred i l hi
      · rw [List.getElem?_append_right (Nat.le_of_not_lt hilt)] at hi
        exact hrest_pred (i - c.length) l hi
    · intro i j l hi hj
      by_cases hilt : i < c.length <;> by_cases hjlt : j < c.length
      · rw [List.getElem?_append_left hilt] at hi
        rw [List.getElem?_append_left hjlt] at hj
        exact hc_uniq i j l hi hj
      · rw [List.getElem?_append_left hilt] at hi
        rw [List.getElem?_append_right (Nat.le_of_not_lt hjlt)] at hj
        exact absurd hj (fun h' => hdisj i (j - c.length) l hi h')
      · rw [List.getElem?_append_right (Nat.le_of_not_lt hilt)] at hi
        rw [List.getElem?_append_left hjlt] at hj
        exact absurd hi (fun h' => hdisj j (i - c.length) l hj h')
      · rw [List.getElem?_append_right (Nat.le_of_not_lt hilt)] at hi
        rw [List.getElem?_append_right (Nat.le_of_not_lt hjlt)] at hj
        have heq := ih_uniq (i - c.length) (j - c.length) l hi hj
        omega

private theorem getElem?_map_label_inj : ∀ {xs : List Sym} {i j : Nat} {l : Sym},
    xs.Nodup → (xs.map x64Frame.label)[i]? = some (x64Frame.label l) →
    (xs.map x64Frame.label)[j]? = some (x64Frame.label l) → i = j
  | [], _, _, _, _, hi, _ => by simp at hi
  | y :: ys, 0, 0, _, _, _, _ => rfl
  | y :: ys, 0, j + 1, l, hnd, hi, hj => by
    simp only [List.nodup_cons] at hnd
    simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hi
    injection hi with hy_l
    simp only [List.map_cons, List.getElem?_cons_succ] at hj
    have hmem : x64Frame.label l ∈ ys.map x64Frame.label := List.mem_of_getElem? hj
    rw [List.mem_map] at hmem
    obtain ⟨y', hy', heq⟩ := hmem
    injection heq with hy_eq
    subst hy_l; subst hy_eq
    exact absurd hy' hnd.1
  | y :: ys, i + 1, 0, l, hnd, hi, hj => by
    simp only [List.nodup_cons] at hnd
    simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hj
    injection hj with hy_l
    simp only [List.map_cons, List.getElem?_cons_succ] at hi
    have hmem : x64Frame.label l ∈ ys.map x64Frame.label := List.mem_of_getElem? hi
    rw [List.mem_map] at hmem
    obtain ⟨y', hy', heq⟩ := hmem
    injection heq with hy_eq
    subst hy_l; subst hy_eq
    exact absurd hy' hnd.1
  | _ :: ys, i + 1, j + 1, l, hnd, hi, hj =>
    congrArg Nat.succ (getElem?_map_label_inj (List.nodup_cons.mp hnd).2 hi hj)

/-- `x64ScalarTarget.LabelsUnique` and exit `Defined` for any host whose program is
`code ++ exitSyms.map x64Frame.label`. -/
theorem compileModuleLoop0_host_labelsUnique {symName : Sym0 → Sym} {fns : List TFlatFn0}
    {idx0 maxSl : UInt32} {exitSyms : List Sym} {h : Host}
    (hprog : x64ScalarMach.prog h =
      toAmd64Program symName (compileModuleLoop0 fns idx0 maxSl []).1 ++
        exitSyms.map x64Frame.label)
    (hbd : idx0.toNat + fns.length < 2 ^ 32)
    (hg : ∀ fn ∈ fns, fn.okGuardsFull = true)
    (hnd : (fns.map (fun fn => symName fn.name) ++ exitSyms).Nodup)
    (hnoloc_fns : ∀ fn ∈ fns, symNoLocPrefix0 (symName fn.name) = true)
    (hnoloc_ex : ∀ g ∈ exitSyms, symNoLocPrefix0 g = true) :
    x64ScalarTarget.LabelsUnique h ∧
    ∀ g ∈ exitSyms, x64ScalarTarget.Defined h g := by
  have hnd_split := List.nodup_append.mp hnd
  obtain ⟨hmem, huniq⟩ := compileModuleLoop0_code_labels symName fns idx0 maxSl hbd hg
    hnd_split.1 hnoloc_fns
  let code := toAmd64Program symName (compileModuleLoop0 fns idx0 maxSl []).1
  let exCode := exitSyms.map x64Frame.label
  have hdisj : ∀ (i₁ j₁ : Nat) (l : Sym), code[i₁]? = some (x64Frame.label l) →
      exCode[j₁]? = some (x64Frame.label l) → False := by
    intro i₁ j₁ l hi₁ hj₁
    have hex_mem : x64Frame.label l ∈ exCode := List.mem_of_getElem? hj₁
    rw [List.mem_map] at hex_mem
    obtain ⟨g, hg_mem, hg_eq⟩ := hex_mem
    injection hg_eq with hl_eq
    subst hl_eq
    rcases hmem i₁ g hi₁ with ⟨fn, hfn, heq⟩ | ⟨_, _, j, _, _, heq⟩
    · exact hnd_split.2.2 _ (List.mem_map_of_mem hfn) _ hg_mem heq.symm
    · exact label0ToSym_loc_ne_sym (hnoloc_ex g hg_mem) heq.symm
  refine ⟨fun i j l hi hj => ?_, fun g hg_mem => ?_⟩
  · rw [hprog] at hi hj
    change (code ++ exCode)[i]? = some (x64Frame.label l) at hi
    change (code ++ exCode)[j]? = some (x64Frame.label l) at hj
    by_cases hilt : i < code.length <;> by_cases hjlt : j < code.length
    · rw [List.getElem?_append_left hilt] at hi
      rw [List.getElem?_append_left hjlt] at hj
      exact huniq i j l hi hj
    · rw [List.getElem?_append_left hilt] at hi
      rw [List.getElem?_append_right (Nat.le_of_not_lt hjlt)] at hj
      exact absurd hj (fun h' => hdisj i (j - code.length) l hi h')
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hilt)] at hi
      rw [List.getElem?_append_left hjlt] at hj
      exact absurd hi (fun h' => hdisj j (i - code.length) l hj h')
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hilt)] at hi
      rw [List.getElem?_append_right (Nat.le_of_not_lt hjlt)] at hj
      have heq := getElem?_map_label_inj hnd_split.2.1 hi hj
      omega
  · obtain ⟨k, hk, hgk⟩ := List.mem_iff_getElem.mp hg_mem
    refine ⟨code.length + k, ?_⟩
    rw [hprog]
    change (code ++ exCode)[code.length + k]? = some (x64Frame.label g)
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    simp [exCode, hk, hgk]

/-! ## 3. Acyclic Call Graph, Stack Bounds, & `NodeContracts0` Lifting -/

/-- `(name, as, rs)` signature tuple for `TFlatFn0`. -/
@[expose] def TFlatFn0.sig0 (fn : TFlatFn0) : Sym0 × List Ty0 × List Ty0 :=
  (fn.name, fn.as, fn.rs)

/-- `(name, as, rs)` signature tuple for `ExtSig0`. -/
@[expose] def ExtSig0.sig0 (ex : ExtSig0) : Sym0 × List Ty0 × List Ty0 :=
  (ex.name, ex.as, ex.rs)

/-- Structural boolean equality on `Ty0`. -/
@[expose] def ty0Eq0 : Ty0 → Ty0 → Bool
  | .bool, .bool | .b8, .b8 | .b16, .b16 | .b32, .b32 | .b64, .b64 => true
  | _, _ => false

/-- Structural boolean equality on `List Ty0`. -/
@[expose] def ty0ListEq0 : List Ty0 → List Ty0 → Bool
  | [], [] => true
  | a :: as, b :: bs => ty0Eq0 a b && ty0ListEq0 as bs
  | _, _ => false

private theorem ty0Eq0_iff_eq {a b : Ty0} : ty0Eq0 a b = true ↔ a = b := by
  cases a <;> cases b <;> first
    | exact ⟨fun _ => rfl, fun _ => rfl⟩
    | exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

private theorem ty0ListEq0_iff_eq : ∀ {a b : List Ty0}, ty0ListEq0 a b = true ↔ a = b
  | [], [] => ⟨fun _ => rfl, fun _ => rfl⟩
  | [], _ :: _ => ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | _ :: _, [] => ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | a :: as, b :: bs => by
    dsimp only [ty0ListEq0]
    simp only [Bool.and_eq_true, ty0Eq0_iff_eq, ty0ListEq0_iff_eq, List.cons.injEq]

/-- Decidable equality on `(Sym0 × List Ty0 × List Ty0)`. -/
@[expose] def sigEq0 (a b : Sym0 × List Ty0 × List Ty0) : Bool :=
  (a.1 == b.1) && (ty0ListEq0 a.2.1 b.2.1 && ty0ListEq0 a.2.2 b.2.2)

private theorem sigEq0_iff_eq {a b : Sym0 × List Ty0 × List Ty0} :
    sigEq0 a b = true ↔ a = b := by
  rcases a with ⟨fa, asa, bsa⟩
  rcases b with ⟨fb, asb, bsb⟩
  simp only [sigEq0, Bool.and_eq_true, beq_iff_eq, ty0ListEq0_iff_eq, Prod.mk.injEq]

mutual
/-- Computable check that all `.call`/`.tailCall` targets stay in `allowed` and `.exit` targets in
`exits`. -/
@[expose] def TFlat0.checkCallsOk0 (allowed : List (Sym0 × List Ty0 × List Ty0))
    (curRs : List Ty0) (exits : List Sym0) : TFlat0 → Bool
  | .let1 _ _ k | .let2Umulw64 _ _ k | .load _ _ k | .store _ _ _ k =>
    k.checkCallsOk0 allowed curRs exits
  | .call f as bs _ k =>
    allowed.any (sigEq0 (f, as, bs)) && k.checkCallsOk0 allowed curRs exits
  | .tailCall f as _ => allowed.any (sigEq0 (f, as, curRs))
  | .exit f _ _ => exits.any (fun e => f == e)
  | .jnz _ t e => t.checkCallsOk0 allowed curRs exits && e.checkCallsOk0 allowed curRs exits
  | .group bodies k =>
    blocksCheckCallsOk0 allowed curRs exits bodies && k.checkCallsOk0 allowed curRs exits
  | .jump _ _ | .ret _ | .hlt => true

@[expose] def blocksCheckCallsOk0 (allowed : List (Sym0 × List Ty0 × List Ty0))
    (curRs : List Ty0) (exits : List Sym0) : List (List Ty0 × TFlat0) → Bool
  | [] => true
  | (_, b) :: rest => b.checkCallsOk0 allowed curRs exits &&
      blocksCheckCallsOk0 allowed curRs exits rest
end

/-- Computable callees-first acyclicity checker across `mod.fns`. -/
@[expose] def TFlatModule0.checkFnsCallsOk0 (exits : List Sym0)
    (extSigs : List (Sym0 × List Ty0 × List Ty0)) :
    List (Sym0 × List Ty0 × List Ty0) → List TFlatFn0 → Bool
  | _, [] => true
  | allowed, fn :: rest =>
    fn.body.checkCallsOk0 (allowed ++ extSigs) fn.rs exits &&
    TFlatModule0.checkFnsCallsOk0 exits extSigs (allowed ++ [fn.sig0]) rest

/-- Whole-module `TFlatModule0` acyclicity + symbol-disjointness checker. -/
@[expose] def TFlatModule0.checkAcyclic0 (mod : TFlatModule0) : Bool :=
  listNodup (mod.fns.map TFlatFn0.name ++ mod.externs.map ExtSig0.name) &&
  TFlatModule0.checkFnsCallsOk0 mod.exits (mod.externs.map ExtSig0.sig0) [] mod.fns

/-- Look up a stack bound by `Sym0` in `List (Sym0 × Nat)`. -/
@[expose] def lookupBound0 (bounds : List (Sym0 × Nat)) (f : Sym0) : Option Nat :=
  (bounds.find? (fun p => p.1 == f)).map Prod.snd

private theorem lookupBound0_mem {bounds : List (Sym0 × Nat)} {f : Sym0} {v : Nat}
    (h : lookupBound0 bounds f = some v) : (f, v) ∈ bounds := by
  induction bounds with
  | nil => simp [lookupBound0] at h
  | cons p ps ih =>
    dsimp only [lookupBound0, List.find?] at h
    split at h
    · rename_i heq
      simp only [Option.map_some, Option.some.injEq] at h
      have hp1 : p.1 = f := beq_iff_eq.mp heq
      rw [← hp1, ← h]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem p (ih h)

mutual
/-- Compute minimum required caller stack bound `n` satisfying `NodeContracts0` bounds. -/
@[expose] def TFlat0.computeBound0 (curFrame nX : Nat) (bounds : List (Sym0 × Nat)) :
    TFlat0 → Option Nat
  | .let1 _ _ k | .let2Umulw64 _ _ k | .load _ _ k | .store _ _ _ k =>
    k.computeBound0 curFrame nX bounds
  | .call f _ _ _ k =>
    match lookupBound0 bounds f, k.computeBound0 curFrame nX bounds with
    | some bf, some r => some (Nat.max (curFrame + 8 + bf) r)
    | _, _ => none
  | .tailCall f _ _ => lookupBound0 bounds f
  | .exit _ _ _ => some nX
  | .jnz _ t e =>
    match t.computeBound0 curFrame nX bounds, e.computeBound0 curFrame nX bounds with
    | some nt, some ne => some (Nat.max nt ne)
    | _, _ => none
  | .group bodies k =>
    match blocksComputeBound0 curFrame nX bounds bodies, k.computeBound0 curFrame nX bounds with
    | some nb, some nk => some (Nat.max nb nk)
    | _, _ => none
  | .jump _ _ | .ret _ | .hlt => some 0

@[expose] def blocksComputeBound0 (curFrame nX : Nat) (bounds : List (Sym0 × Nat)) :
    List (List Ty0 × TFlat0) → Option Nat
  | [] => some 0
  | (_, b) :: rest =>
    match b.computeBound0 curFrame nX bounds, blocksComputeBound0 curFrame nX bounds rest with
    | some nb, some nr => some (Nat.max nb nr)
    | _, _ => none
end

/-- Incremental callees-first bound calculator mirroring `compileModuleLoop0` indices. -/
@[expose] def compileModuleBoundsLoop0 (nX : Nat) :
    List TFlatFn0 → UInt32 → List (Sym0 × Nat) → Option (List (Sym0 × Nat))
  | [], _, acc => some acc
  | fn :: rest, idx, acc =>
    let curFrame := x64FrameSize (compileFn0 idx fn).2.toNat
    match fn.body.computeBound0 curFrame nX acc with
    | some req =>
      let b := Nat.max curFrame req
      if Nat.ble (b + 8) (2 ^ 64) then
        compileModuleBoundsLoop0 nX rest (idx + 1) ((fn.name, b) :: acc)
      else none
    | none => none

/-- Compute valid stack bounds for `mod.fns` given extern bounds and `nX`. -/
@[expose] def TFlatModule0.computeBounds0 (mod : TFlatModule0) (extBounds : List (Sym0 × Nat))
    (nX : Nat) : Option (List (Sym0 × Nat)) :=
  if mod.externs.all (fun ex => match lookupBound0 extBounds ex.name with
      | some b => Nat.ble (b + 8) (2 ^ 64)
      | none => false) then
    compileModuleBoundsLoop0 nX mod.fns 0 extBounds
  else none

mutual
/-- Combined call-acyclicity & stack-frame bound predicate on `TFlat0` subtrees. -/
@[expose] def CallsAcyclic0 (curRs : List Ty0) (bound : Sym0 → Nat)
    (allowed : List (Sym0 × List Ty0 × List Ty0)) (exits : List Sym0)
    (curFrame n nX : Nat) : TFlat0 → Prop
  | .let1 _ _ k | .let2Umulw64 _ _ k | .load _ _ k | .store _ _ _ k =>
    CallsAcyclic0 curRs bound allowed exits curFrame n nX k
  | .call f as bs _ k =>
    (f, as, bs) ∈ allowed ∧ curFrame + 8 + bound f ≤ n ∧
    CallsAcyclic0 curRs bound allowed exits curFrame n nX k
  | .tailCall f as _ => (f, as, curRs) ∈ allowed ∧ bound f ≤ n
  | .exit f _ _ => f ∈ exits ∧ nX ≤ n
  | .jnz _ t e =>
    CallsAcyclic0 curRs bound allowed exits curFrame n nX t ∧
    CallsAcyclic0 curRs bound allowed exits curFrame n nX e
  | .group bodies k =>
    BlocksCallsAcyclic0 curRs bound allowed exits curFrame n nX bodies ∧
    CallsAcyclic0 curRs bound allowed exits curFrame n nX k
  | .jump _ _ | .ret _ | .hlt => True

@[expose] def BlocksCallsAcyclic0 (curRs : List Ty0) (bound : Sym0 → Nat)
    (allowed : List (Sym0 × List Ty0 × List Ty0)) (exits : List Sym0)
    (curFrame n nX : Nat) : List (List Ty0 × TFlat0) → Prop
  | [] => True
  | (_, b) :: rest =>
    CallsAcyclic0 curRs bound allowed exits curFrame n nX b ∧
    BlocksCallsAcyclic0 curRs bound allowed exits curFrame n nX rest
end

/-- Whole-module acyclic call & stack-bound contract for `mod` at `nX`. -/
@[expose] def ModBoundsOk0 (mod : TFlatModule0) (nX : Nat) (bound : Sym0 → Nat) : Prop :=
  (∀ ex ∈ mod.externs, bound ex.name + 8 ≤ 2 ^ 64) ∧
  ∀ pre fn post, mod.fns = pre ++ fn :: post →
    let fnIdx := UInt32.ofNat pre.length
    x64FrameSize (compileFn0 fnIdx fn).2.toNat ≤ bound fn.name ∧
    bound fn.name + 8 ≤ 2 ^ 64 ∧
    CallsAcyclic0 fn.rs bound (pre.map TFlatFn0.sig0 ++ mod.externs.map ExtSig0.sig0)
      mod.exits (x64FrameSize (compileFn0 fnIdx fn).2.toNat) (bound fn.name) nX fn.body

mutual
private theorem nodeContracts0_of_callsAcyclic0_aux {h : Host} {symName : Sym0 → Sym} {Γ : Env}
    {ctx : LegalCtx0} {ns : UInt32} {n nX : Nat} {bound : Sym0 → Nat}
    {allowed : List (Sym0 × List Ty0 × List Ty0)} {exits : List Sym0} {rs : List Ty0}
    (hctx_rs : ctx.curRs = rs)
    (hallowed : ∀ f as bs, (f, as, bs) ∈ allowed →
      x64ScalarTarget.Defined h (symName f) ∧
      x64ScalarTarget.FnSpec h (symName f)
        (Γ (symName f) (ty0ListToTy as) (ty0ListToTy bs)) (bound f) nX)
    (hexits : ∀ f ∈ exits, x64ScalarTarget.Defined h (symName f)) :
    ∀ (node : TFlat0),
      CallsAcyclic0 rs bound allowed exits (x64FrameSize ns.toNat) n nX node →
      NodeContracts0 h symName Γ ctx ns n nX node
  | .let1 _ _ k, hc | .let2Umulw64 _ _ k, hc | .load _ _ k, hc | .store _ _ _ k, hc => by
    dsimp only [CallsAcyclic0] at hc; dsimp only [NodeContracts0]
    exact nodeContracts0_of_callsAcyclic0_aux hctx_rs hallowed hexits k hc
  | .call f as bs _ k, hc => by
    dsimp only [CallsAcyclic0] at hc; dsimp only [NodeContracts0]
    obtain ⟨hd, hs⟩ := hallowed f as bs hc.1
    exact ⟨⟨bound f, hc.2.1, hd, hs⟩,
      nodeContracts0_of_callsAcyclic0_aux hctx_rs hallowed hexits k hc.2.2⟩
  | .tailCall f as _, hc => by
    dsimp only [CallsAcyclic0] at hc; dsimp only [NodeContracts0]
    obtain ⟨hd, hs⟩ := hallowed f as rs hc.1
    refine ⟨bound f, hc.2, hd, ?_⟩
    rw [hctx_rs]; exact hs
  | .exit f _ _, hc => by
    dsimp only [CallsAcyclic0] at hc; dsimp only [NodeContracts0]
    exact ⟨hc.2, hexits f hc.1⟩
  | .jnz _ t e, hc => by
    dsimp only [CallsAcyclic0] at hc; dsimp only [NodeContracts0]
    exact ⟨nodeContracts0_of_callsAcyclic0_aux hctx_rs hallowed hexits t hc.1,
           nodeContracts0_of_callsAcyclic0_aux hctx_rs hallowed hexits e hc.2⟩
  | .group bodies k, hc => by
    dsimp only [CallsAcyclic0] at hc; dsimp only [NodeContracts0]
    exact ⟨blocksContracts0_of_callsAcyclic0 hctx_rs hallowed hexits bodies hc.1,
           nodeContracts0_of_callsAcyclic0_aux hctx_rs hallowed hexits k hc.2⟩
  | .jump _ _, _ | .ret _, _ | .hlt, _ => trivial
termination_by node => sizeOf node

private theorem blocksContracts0_of_callsAcyclic0 {h : Host} {symName : Sym0 → Sym} {Γ : Env}
    {ctx : LegalCtx0} {ns : UInt32} {n nX : Nat} {bound : Sym0 → Nat}
    {allowed : List (Sym0 × List Ty0 × List Ty0)} {exits : List Sym0} {rs : List Ty0}
    (hctx_rs : ctx.curRs = rs)
    (hallowed : ∀ f as bs, (f, as, bs) ∈ allowed →
      x64ScalarTarget.Defined h (symName f) ∧
      x64ScalarTarget.FnSpec h (symName f)
        (Γ (symName f) (ty0ListToTy as) (ty0ListToTy bs)) (bound f) nX)
    (hexits : ∀ f ∈ exits, x64ScalarTarget.Defined h (symName f)) :
    ∀ (bodies : List (List Ty0 × TFlat0)),
      BlocksCallsAcyclic0 rs bound allowed exits (x64FrameSize ns.toNat) n nX bodies →
      BlocksContracts0 h symName Γ ctx ns n nX bodies
  | [], _ => trivial
  | (_, b) :: rest, hc => by
    dsimp only [BlocksCallsAcyclic0] at hc; dsimp only [BlocksContracts0]
    exact ⟨nodeContracts0_of_callsAcyclic0_aux hctx_rs hallowed hexits b hc.1,
           blocksContracts0_of_callsAcyclic0 hctx_rs hallowed hexits rest hc.2⟩
termination_by bs => sizeOf bs
end

/-- Bridge `CallsAcyclic0` directly to `NodeContracts0`. -/
theorem nodeContracts0_of_callsAcyclic0 {h : Host} {symName : Sym0 → Sym} {Γ : Env}
    {ctx : LegalCtx0} {ns : UInt32} {n nX : Nat} {bound : Sym0 → Nat}
    {allowed : List (Sym0 × List Ty0 × List Ty0)} {exits : List Sym0} {node : TFlat0}
    (hc : CallsAcyclic0 ctx.curRs bound allowed exits (x64FrameSize ns.toNat) n nX node)
    (hallowed : ∀ f as bs, (f, as, bs) ∈ allowed →
      x64ScalarTarget.Defined h (symName f) ∧
      x64ScalarTarget.FnSpec h (symName f)
        (Γ (symName f) (ty0ListToTy as) (ty0ListToTy bs)) (bound f) nX)
    (hexits : ∀ f ∈ exits, x64ScalarTarget.Defined h (symName f)) :
    NodeContracts0 h symName Γ ctx ns n nX node :=
  nodeContracts0_of_callsAcyclic0_aux rfl hallowed hexits node hc

private theorem checkFnsCallsOk0_split (exits : List Sym0)
    (extSigs : List (Sym0 × List Ty0 × List Ty0)) :
    ∀ (seen rest pre : List TFlatFn0) (fn : TFlatFn0) (post : List TFlatFn0),
      TFlatModule0.checkFnsCallsOk0 exits extSigs (seen.map TFlatFn0.sig0) rest = true →
      rest = pre ++ fn :: post →
      fn.body.checkCallsOk0 ((seen ++ pre).map TFlatFn0.sig0 ++ extSigs) fn.rs exits = true
  | _, [], pre, _, _, _, hsp => by cases pre <;> simp at hsp
  | seen, f :: rest, [], fn, post, hchk, hsp => by
    simp only [List.nil_append, List.cons.injEq] at hsp
    rcases hsp with ⟨rfl, _⟩
    dsimp only [TFlatModule0.checkFnsCallsOk0] at hchk
    rw [Bool.and_eq_true] at hchk
    simpa [List.append_nil] using hchk.1
  | seen, f :: rest, f' :: pre', fn, post, hchk, hsp => by
    simp only [List.cons_append, List.cons.injEq] at hsp
    rcases hsp with ⟨rfl, hrest⟩
    dsimp only [TFlatModule0.checkFnsCallsOk0] at hchk
    rw [Bool.and_eq_true] at hchk
    have hnext := hchk.2
    rw [show seen.map TFlatFn0.sig0 ++ [f.sig0] = (seen ++ [f]).map TFlatFn0.sig0 by simp] at hnext
    have ih := checkFnsCallsOk0_split exits extSigs (seen ++ [f]) rest pre' fn post hnext hrest
    simpa [List.append_assoc] using ih

mutual
private theorem callsAcyclic0_of_checks (curRs : List Ty0) (bound : Sym0 → Nat)
    (allowed : List (Sym0 × List Ty0 × List Ty0)) (exits : List Sym0)
    (curFrame nX : Nat) (boundsList : List (Sym0 × Nat))
    (hagree : ∀ p ∈ allowed, lookupBound0 boundsList p.1 = some (bound p.1)) :
    ∀ (node : TFlat0) (n req : Nat),
      node.checkCallsOk0 allowed curRs exits = true →
      node.computeBound0 curFrame nX boundsList = some req →
      req ≤ n →
      CallsAcyclic0 curRs bound allowed exits curFrame n nX node
  | .let1 _ _ k, n, req, hc, hb, hle | .let2Umulw64 _ _ k, n, req, hc, hb, hle
  | .load _ _ k, n, req, hc, hb, hle | .store _ _ _ k, n, req, hc, hb, hle => by
    dsimp only [TFlat0.checkCallsOk0] at hc
    dsimp only [TFlat0.computeBound0] at hb
    dsimp only [CallsAcyclic0]
    exact callsAcyclic0_of_checks curRs bound allowed exits curFrame nX boundsList hagree
      k n req hc hb hle
  | .call f as bs _ k, n, req, hc, hb, hle => by
    dsimp only [TFlat0.checkCallsOk0] at hc
    rw [Bool.and_eq_true, List.any_eq_true] at hc
    obtain ⟨⟨p, hp, hpe⟩, hck⟩ := hc
    rw [sigEq0_iff_eq] at hpe; subst hpe
    dsimp only [TFlat0.computeBound0] at hb
    cases hbf : lookupBound0 boundsList f with
    | none => simp [hbf] at hb
    | some bf =>
      cases hk : k.computeBound0 curFrame nX boundsList with
      | none => simp [hbf, hk] at hb
      | some rk =>
        simp only [hbf, hk, Option.some.injEq] at hb
        subst hb
        have hbf_eq : bf = bound f := by
          have := hagree (f, as, bs) hp
          rw [hbf, Option.some.injEq] at this
          exact this
        rw [hbf_eq] at hle
        dsimp only [CallsAcyclic0]
        exact ⟨hp, Nat.le_trans (Nat.le_max_left _ _) hle,
          callsAcyclic0_of_checks curRs bound allowed exits curFrame nX boundsList hagree
            k n rk hck hk (Nat.le_trans (Nat.le_max_right _ _) hle)⟩
  | .tailCall f as _, n, req, hc, hb, hle => by
    dsimp only [TFlat0.checkCallsOk0] at hc; rw [List.any_eq_true] at hc
    obtain ⟨p, hp, hpe⟩ := hc
    rw [sigEq0_iff_eq] at hpe; subst hpe
    dsimp only [TFlat0.computeBound0] at hb
    have hag := hagree (f, as, curRs) hp
    dsimp only at hag
    rw [hb, Option.some.injEq] at hag
    dsimp only [CallsAcyclic0]
    exact ⟨hp, Nat.le_trans (le_of_eq hag.symm) hle⟩
  | .exit f _ _, n, req, hc, hb, hle => by
    dsimp only [TFlat0.checkCallsOk0] at hc; rw [List.any_eq_true] at hc
    obtain ⟨g, hg, hge⟩ := hc
    have : f = g := beq_iff_eq.mp hge
    subst this
    dsimp only [TFlat0.computeBound0] at hb; rw [Option.some.injEq] at hb
    subst hb
    dsimp only [CallsAcyclic0]
    exact ⟨hg, hle⟩
  | .jnz _ t e, n, req, hc, hb, hle => by
    dsimp only [TFlat0.checkCallsOk0] at hc; rw [Bool.and_eq_true] at hc
    dsimp only [TFlat0.computeBound0] at hb
    cases ht : t.computeBound0 curFrame nX boundsList with
    | none => simp [ht] at hb
    | some nt =>
      cases he : e.computeBound0 curFrame nX boundsList with
      | none => simp [ht, he] at hb
      | some ne =>
        simp only [ht, he, Option.some.injEq] at hb
        subst hb
        dsimp only [CallsAcyclic0]
        exact ⟨callsAcyclic0_of_checks curRs bound allowed exits curFrame nX boundsList hagree
            t n nt hc.1 ht (Nat.le_trans (Nat.le_max_left _ _) hle),
          callsAcyclic0_of_checks curRs bound allowed exits curFrame nX boundsList hagree
            e n ne hc.2 he (Nat.le_trans (Nat.le_max_right _ _) hle)⟩
  | .group bodies k, n, req, hc, hb, hle => by
    dsimp only [TFlat0.checkCallsOk0] at hc; rw [Bool.and_eq_true] at hc
    dsimp only [TFlat0.computeBound0] at hb
    cases hbs : blocksComputeBound0 curFrame nX boundsList bodies with
    | none => simp [hbs] at hb
    | some nb =>
      cases hk : k.computeBound0 curFrame nX boundsList with
      | none => simp [hbs, hk] at hb
      | some nk =>
        simp only [hbs, hk, Option.some.injEq] at hb
        subst hb
        dsimp only [CallsAcyclic0]
        exact ⟨blocksCallsAcyclic0_of_checks curRs bound allowed exits curFrame nX boundsList hagree
            bodies n nb hc.1 hbs (Nat.le_trans (Nat.le_max_left _ _) hle),
          callsAcyclic0_of_checks curRs bound allowed exits curFrame nX boundsList hagree
            k n nk hc.2 hk (Nat.le_trans (Nat.le_max_right _ _) hle)⟩
  | .jump _ _, _, _, _, _, _ | .ret _, _, _, _, _, _ | .hlt, _, _, _, _, _ => trivial
termination_by node => sizeOf node

private theorem blocksCallsAcyclic0_of_checks (curRs : List Ty0) (bound : Sym0 → Nat)
    (allowed : List (Sym0 × List Ty0 × List Ty0)) (exits : List Sym0)
    (curFrame nX : Nat) (boundsList : List (Sym0 × Nat))
    (hagree : ∀ p ∈ allowed, lookupBound0 boundsList p.1 = some (bound p.1)) :
    ∀ (bodies : List (List Ty0 × TFlat0)) (n req : Nat),
      blocksCheckCallsOk0 allowed curRs exits bodies = true →
      blocksComputeBound0 curFrame nX boundsList bodies = some req →
      req ≤ n →
      BlocksCallsAcyclic0 curRs bound allowed exits curFrame n nX bodies
  | [], _, _, _, _, _ => trivial
  | (_, b) :: rest, n, req, hc, hb, hle => by
    dsimp only [blocksCheckCallsOk0] at hc; rw [Bool.and_eq_true] at hc
    dsimp only [blocksComputeBound0] at hb
    cases hbb : b.computeBound0 curFrame nX boundsList with
    | none => simp [hbb] at hb
    | some nb =>
      cases hbr : blocksComputeBound0 curFrame nX boundsList rest with
      | none => simp [hbb, hbr] at hb
      | some nr =>
        simp only [hbb, hbr, Option.some.injEq] at hb
        subst hb
        dsimp only [BlocksCallsAcyclic0]
        exact ⟨callsAcyclic0_of_checks curRs bound allowed exits curFrame nX boundsList hagree
            b n nb hc.1 hbb (Nat.le_trans (Nat.le_max_left _ _) hle),
          blocksCallsAcyclic0_of_checks curRs bound allowed exits curFrame nX boundsList hagree
            rest n nr hc.2 hbr (Nat.le_trans (Nat.le_max_right _ _) hle)⟩
termination_by bs => sizeOf bs
end

private theorem compileModuleBoundsLoop0_acc_mono (nX : Nat) :
    ∀ (fns : List TFlatFn0) (idx : UInt32) (acc out : List (Sym0 × Nat)),
      compileModuleBoundsLoop0 nX fns idx acc = some out →
      ∀ f, f ∉ fns.map TFlatFn0.name → lookupBound0 out f = lookupBound0 acc f
  | [], _, acc, out, h, f, _ => by
    dsimp only [compileModuleBoundsLoop0] at h
    injection h with he; subst he; rfl
  | fn :: rest, idx, acc, out, h, f, hnf => by
    simp only [List.map_cons, List.mem_cons, not_or] at hnf
    dsimp only [compileModuleBoundsLoop0] at h
    split at h
    · rename_i req hreq
      split at h
      · have ih := compileModuleBoundsLoop0_acc_mono nX rest (idx + 1)
          ((fn.name, Nat.max (x64FrameSize (compileFn0 idx fn).2.toNat) req) :: acc) out h
          f hnf.2
        rw [ih]
        have hbeq : (fn.name == f) = false :=
          Bool.eq_false_iff.mpr fun hb => hnf.1 (beq_iff_eq.mp hb).symm
        dsimp only [lookupBound0, List.find?]
        simp [hbeq]
      · cases h
    · cases h

private theorem compileModuleBoundsLoop0_spec (nX : Nat) :
    ∀ (seen rest : List TFlatFn0) (acc out : List (Sym0 × Nat)),
      (seen.map TFlatFn0.name ++ rest.map TFlatFn0.name).Nodup →
      compileModuleBoundsLoop0 nX rest (UInt32.ofNat seen.length) acc = some out →
      (∀ exName ∈ acc.map Prod.fst, exName ∉ rest.map TFlatFn0.name) →
      ∀ (exits : List Sym0) (extSigs : List (Sym0 × List Ty0 × List Ty0)),
        (∀ p ∈ extSigs, p.1 ∉ (seen ++ rest).map TFlatFn0.name ∧
          lookupBound0 acc p.1 ≠ none) →
        TFlatModule0.checkFnsCallsOk0 exits extSigs (seen.map TFlatFn0.sig0) rest = true →
        (∀ g ∈ seen, lookupBound0 acc g.name ≠ none) →
        ∀ pre fn post, rest = pre ++ fn :: post →
          let fnIdx := UInt32.ofNat (seen.length + pre.length)
          let bound := fun sym => (lookupBound0 out sym).getD 0
          x64FrameSize (compileFn0 fnIdx fn).2.toNat ≤ bound fn.name ∧
          bound fn.name + 8 ≤ 2 ^ 64 ∧
          CallsAcyclic0 fn.rs bound
            ((seen ++ pre).map TFlatFn0.sig0 ++ extSigs)
            exits (x64FrameSize (compileFn0 fnIdx fn).2.toNat) (bound fn.name) nX fn.body
  | _, [], _, _, _, _, _, _, _, _, _, _, pre, _, _, hsp => by cases pre <;> simp at hsp
  | seen, g :: rest, acc, out, hnd, hloop, hacc_disj, exits, extSigs, hext, hchk, hseen,
      pre, fn, post, hsp => by
    have hnd' := List.nodup_append.mp hnd
    have hg_nd := List.nodup_cons.mp hnd'.2.1
    dsimp only [compileModuleBoundsLoop0] at hloop
    cases hreq : g.body.computeBound0
        (x64FrameSize (compileFn0 (UInt32.ofNat seen.length) g).2.toNat) nX acc with
    | none => simp [hreq] at hloop
    | some req =>
      rw [hreq] at hloop
      dsimp only at hloop
      split at hloop
      · rename_i hble
        let b := Nat.max (x64FrameSize (compileFn0 (UInt32.ofNat seen.length) g).2.toNat) req
        change Nat.ble (b + 8) (2 ^ 64) = true at hble
        change compileModuleBoundsLoop0 nX rest (UInt32.ofNat seen.length + 1)
          ((g.name, b) :: acc) = some out at hloop
        have hb8 : b + 8 ≤ 2 ^ 64 := Nat.le_of_ble_eq_true hble
        have hgnin_rest : g.name ∉ rest.map TFlatFn0.name := hg_nd.1
        have hout_g : lookupBound0 out g.name = some b := by
          rw [compileModuleBoundsLoop0_acc_mono nX rest (UInt32.ofNat seen.length + 1)
            ((g.name, b) :: acc) out hloop g.name hgnin_rest]
          simp [lookupBound0]
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hsp
          rcases hsp with ⟨rfl, rfl⟩
          simp only [List.length_nil, Nat.add_zero, List.append_nil]
          have hc_g : g.body.checkCallsOk0 (seen.map TFlatFn0.sig0 ++ extSigs) g.rs exits =
              true := by
            dsimp only [TFlatModule0.checkFnsCallsOk0] at hchk
            rw [Bool.and_eq_true] at hchk; exact hchk.1
          have hagree : ∀ p ∈ seen.map TFlatFn0.sig0 ++ extSigs,
              lookupBound0 acc p.1 = some ((lookupBound0 out p.1).getD 0) := by
            intro p hp
            have hpn : p.1 ∉ (g :: rest).map TFlatFn0.name := by
              rcases List.mem_append.mp hp with hp1 | hp2
              · rw [List.mem_map] at hp1
                obtain ⟨q, hq, rfl⟩ := hp1
                exact fun hm => hnd'.2.2 _ (List.mem_map_of_mem hq) _ hm rfl
              · intro hm
                have : p.1 ∈ (seen ++ g :: rest).map TFlatFn0.name := by
                  rw [List.map_append]; exact List.mem_append_right _ hm
                exact (hext p hp2).1 this
            have hlk_out := compileModuleBoundsLoop0_acc_mono nX rest (UInt32.ofNat seen.length + 1)
              ((g.name, b) :: acc) out hloop p.1 (fun hm => hpn (List.mem_cons_of_mem _ hm))
            have hne_g : g.name ≠ p.1 := fun he => hpn (he ▸ List.mem_cons_self)
            have hbeq : (g.name == p.1) = false := Bool.eq_false_iff.mpr fun hb =>
              hne_g (beq_iff_eq.mp hb)
            have hlk_acc : lookupBound0 ((g.name, b) :: acc) p.1 = lookupBound0 acc p.1 := by
              dsimp only [lookupBound0, List.find?]; simp [hbeq]
            rw [hlk_out, hlk_acc]
            have hne : lookupBound0 acc p.1 ≠ none := by
              rcases List.mem_append.mp hp with hp1 | hp2
              · rw [List.mem_map] at hp1
                obtain ⟨q, hq, rfl⟩ := hp1
                exact hseen q hq
              · exact (hext p hp2).2
            cases hlk : lookupBound0 acc p.1 with
            | none => exact absurd hlk hne
            | some v => simp
          refine ⟨by
              change x64FrameSize (compileFn0 (UInt32.ofNat seen.length) g).2.toNat ≤
                (lookupBound0 out g.name).getD 0
              rw [hout_g]; exact Nat.le_max_left _ _,
            by change (lookupBound0 out g.name).getD 0 + 8 ≤ 2 ^ 64
               rw [hout_g]; exact hb8,
            callsAcyclic0_of_checks g.rs (fun sym => (lookupBound0 out sym).getD 0)
              (seen.map TFlatFn0.sig0 ++ extSigs) exits
              (x64FrameSize (compileFn0 (UInt32.ofNat seen.length) g).2.toNat) nX acc
              hagree g.body ((lookupBound0 out g.name).getD 0) req hc_g hreq
              (by rw [hout_g]; exact Nat.le_max_right _ _)⟩
        | cons p pre' =>
          simp only [List.cons_append, List.cons.injEq] at hsp
          rcases hsp with ⟨rfl, hrest⟩
          have hnd_next : ((seen ++ [g]).map TFlatFn0.name ++ rest.map TFlatFn0.name).Nodup := by
            simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
              List.singleton_append] using hnd
          have hlen_succ : (UInt32.ofNat (seen ++ [g]).length : UInt32) =
              UInt32.ofNat seen.length + 1 := by
            apply u32_ext0
            rw [List.length_append, List.length_singleton, UInt32.toNat_add, UInt32.toNat_one,
              u32_toNat_ofNat0, u32_toNat_ofNat0, Nat.mod_add_mod]
          rw [← hlen_succ] at hloop
          have hchk_next : TFlatModule0.checkFnsCallsOk0 exits extSigs
              ((seen ++ [g]).map TFlatFn0.sig0) rest = true := by
            dsimp only [TFlatModule0.checkFnsCallsOk0] at hchk
            rw [Bool.and_eq_true] at hchk; simpa [List.map_append] using hchk.2
          have hacc_disj' : ∀ exName ∈ ((g.name, b) :: acc).map Prod.fst,
              exName ∉ rest.map TFlatFn0.name := by
            intro exName hm
            rcases List.mem_cons.mp hm with rfl | hm'
            · exact hgnin_rest
            · exact fun hf => hacc_disj exName hm' (List.mem_cons_of_mem _ hf)
          have hext' : ∀ q ∈ extSigs, q.1 ∉ ((seen ++ [g]) ++ rest).map TFlatFn0.name ∧
              lookupBound0 ((g.name, b) :: acc) q.1 ≠ none := by
            intro q hq
            have hq1 := hext q hq
            refine ⟨by simpa [List.map_append, List.append_assoc] using hq1.1, ?_⟩
            have hne : g.name ≠ q.1 := fun he =>
              hq1.1 (by
                rw [List.map_append]; exact List.mem_append_right _ (he ▸ List.mem_cons_self))
            have hbeq : (g.name == q.1) = false := Bool.eq_false_iff.mpr fun hb =>
              hne (beq_iff_eq.mp hb)
            have hlk_eq : lookupBound0 ((g.name, b) :: acc) q.1 = lookupBound0 acc q.1 := by
              dsimp only [lookupBound0, List.find?]; rw [hbeq]
            rw [hlk_eq]; exact hq1.2
          have hseen' : ∀ q ∈ seen ++ [g], lookupBound0 ((g.name, b) :: acc) q.name ≠ none := by
            intro q hq
            rcases List.mem_append.mp hq with hqs | hqg
            · by_cases he : g.name = q.name
              · rw [he]; simp [lookupBound0]
              · have hbeq : (g.name == q.name) = false := Bool.eq_false_iff.mpr fun hb =>
                  he (beq_iff_eq.mp hb)
                have hlk_eq : lookupBound0 ((g.name, b) :: acc) q.name =
                    lookupBound0 acc q.name := by
                  dsimp only [lookupBound0, List.find?]; rw [hbeq]
                rw [hlk_eq]; exact hseen q hqs
            · simp only [List.mem_singleton] at hqg; subst hqg; simp [lookupBound0]
          have ih := compileModuleBoundsLoop0_spec nX (seen ++ [g]) rest ((g.name, b) :: acc) out
            hnd_next hloop hacc_disj' exits extSigs hext' hchk_next hseen' pre' fn post hrest
          simpa only [List.length_append, List.length_cons, List.length_singleton,
            List.length_nil, List.append_assoc, List.singleton_append, Nat.zero_add,
            Nat.add_assoc, Nat.add_comm 1 pre'.length] using ih
      · simp at hloop

private theorem ty0ToTy_inj_loc {a b : Ty0} (h : ty0ToTy a = ty0ToTy b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by simp [ty0ToTy])

private theorem ty0ListToTy_inj_loc :
    ∀ {as bs : List Ty0}, ty0ListToTy as = ty0ListToTy bs → as = bs
  | [], [], _ => rfl
  | [], _ :: _, h => by dsimp only [ty0ListToTy, List.map] at h; cases h
  | _ :: _, [], h => by dsimp only [ty0ListToTy, List.map] at h; cases h
  | _ :: _, _ :: _, h => by
    dsimp only [ty0ListToTy] at h
    simp only [List.map_cons, List.cons.injEq] at h
    exact congr (congrArg List.cons (ty0ToTy_inj_loc h.1)) (ty0ListToTy_inj_loc h.2)

private theorem checkAcyclic0_parts {mod : TFlatModule0} (h : mod.checkAcyclic0 = true) :
    (mod.fns.map TFlatFn0.name ++ mod.externs.map ExtSig0.name).Nodup ∧
    TFlatModule0.checkFnsCallsOk0 mod.exits (mod.externs.map ExtSig0.sig0) [] mod.fns = true := by
  dsimp only [TFlatModule0.checkAcyclic0] at h
  rw [Bool.and_eq_true] at h
  exact ⟨listNodup_nodup h.1, h.2⟩

/-- Any success of `mod.computeBounds0` + `(namesNodup, checkFnsCallsOk0)` constructs
`ModBoundsOk0`. -/
theorem modBoundsOk0_of_parts {mod : TFlatModule0} {extBounds modBounds : List (Sym0 × Nat)}
    {nX : Nat} (hnd : (mod.fns.map TFlatFn0.name ++ mod.externs.map ExtSig0.name).Nodup)
    (hchk : TFlatModule0.checkFnsCallsOk0 mod.exits (mod.externs.map ExtSig0.sig0) [] mod.fns =
      true)
    (hb : mod.computeBounds0 extBounds nX = some modBounds)
    (hext_disj : ∀ exName ∈ extBounds.map Prod.fst, exName ∉ mod.fns.map TFlatFn0.name) :
    ModBoundsOk0 mod nX (fun sym => (lookupBound0 modBounds sym).getD 0) := by
  rw [List.nodup_append] at hnd
  dsimp only [TFlatModule0.computeBounds0] at hb
  split at hb
  · rename_i hall_exts
    rw [List.all_eq_true] at hall_exts
    have hdisj_fns : ∀ p ∈ mod.externs.map ExtSig0.sig0,
        p.1 ∉ ([] ++ mod.fns).map TFlatFn0.name ∧ lookupBound0 extBounds p.1 ≠ none := by
      intro p hp
      rw [List.mem_map] at hp
      obtain ⟨ex, hex, rfl⟩ := hp
      refine ⟨fun hm => hnd.2.2 _ hm _ (List.mem_map_of_mem hex) rfl, ?_⟩
      have he := hall_exts ex hex
      dsimp only [ExtSig0.sig0]
      cases hlk : lookupBound0 extBounds ex.name with
      | none => rw [hlk] at he; cases he
      | some _ => simp
    have hloop := compileModuleBoundsLoop0_spec nX [] mod.fns extBounds modBounds
      (by simpa using hnd.1) (by simpa using hb) hext_disj mod.exits
      (mod.externs.map ExtSig0.sig0) hdisj_fns hchk (fun _ hm => nomatch hm)
    refine ⟨fun ex hex => ?_, fun pre fn post hsp => ?_⟩
    · have hlk_ext := hall_exts ex hex
      cases hlk : lookupBound0 extBounds ex.name with
      | none => rw [hlk] at hlk_ext; cases hlk_ext
      | some v =>
        rw [hlk] at hlk_ext
        have hnin : ex.name ∉ mod.fns.map TFlatFn0.name := fun hm =>
          hnd.2.2 _ hm _ (List.mem_map_of_mem hex) rfl
        have hout := compileModuleBoundsLoop0_acc_mono nX mod.fns 0 extBounds modBounds hb
          ex.name hnin
        change (lookupBound0 modBounds ex.name).getD 0 + 8 ≤ 2 ^ 64
        rw [hout, hlk]
        exact Nat.le_of_ble_eq_true hlk_ext
    · simpa using hloop pre fn post hsp
  · cases hb

/-- Any success of `mod.computeBounds0` + `mod.checkAcyclic0` constructs `ModBoundsOk0`. -/
theorem modBoundsOk0_of_computeBounds0 {mod : TFlatModule0}
    {extBounds modBounds : List (Sym0 × Nat)} {nX : Nat} (hacyc : mod.checkAcyclic0 = true)
    (hb : mod.computeBounds0 extBounds nX = some modBounds)
    (hext_disj : ∀ exName ∈ extBounds.map Prod.fst, exName ∉ mod.fns.map TFlatFn0.name) :
    ModBoundsOk0 mod nX (fun sym => (lookupBound0 modBounds sym).getD 0) :=
  let hp := checkAcyclic0_parts hacyc
  modBoundsOk0_of_parts hp.1 hp.2 hb hext_disj

/-! ## 4. Module Soundness (`compileModuleLoop0_sound` & `leanqbe0Compile_fnSpec`) -/

private theorem compileModuleLoop0_sound_prefix {h : Host} {symName : Sym0 → Sym} {Γ : Env}
    {mod : TFlatModule0} {nX k₀ : Nat} {bound : Sym0 → Nat}
    (hfit : mod.sigLensFitU32 = true) (hl : legalMod0 mod = 0)
    (hg : mod.okGuardsFull = true)
    (hinf : (toAmd64Program symName (compileModuleLoop0 mod.fns 0 0 []).1).IsInfixAt
      (x64ScalarMach.prog h) k₀)
    (hu : x64ScalarTarget.LabelsUnique h)
    (hmod_bd : ModBoundsOk0 mod nX bound)
    (hext : ∀ ex ∈ mod.externs,
      x64ScalarTarget.Defined h (symName ex.name) ∧
      x64ScalarTarget.FnSpec h (symName ex.name)
        (Γ (symName ex.name) (ty0ListToTy ex.as) (ty0ListToTy ex.rs)) (bound ex.name) nX)
    (hexits : ∀ g ∈ mod.exits, x64ScalarTarget.Defined h (symName g))
    (hwp : ∀ fn ∈ mod.fns, ∀ (args : Tup Val (ty0ListToTy fn.as)) m Q X,
      Γ (symName fn.name) (ty0ListToTy fn.as) (ty0ListToTy fn.rs) args m Q X →
      wp0 Γ symName fn.rs (pushTup args []) [] Q X fn.body m) :
    ∀ (seen rest : List TFlatFn0), mod.fns = seen ++ rest →
      (∀ g ∈ seen,
        x64ScalarTarget.Defined h (symName g.name) ∧
        x64ScalarTarget.FnSpec h (symName g.name)
          (Γ (symName g.name) (ty0ListToTy g.as) (ty0ListToTy g.rs)) (bound g.name) nX) →
      ∀ fn ∈ rest,
        x64ScalarTarget.Defined h (symName fn.name) ∧
        x64ScalarTarget.FnSpec h (symName fn.name)
          (Γ (symName fn.name) (ty0ListToTy fn.as) (ty0ListToTy fn.rs)) (bound fn.name) nX := by
  have hl_snd := legalMod0_sound mod hl hfit
  have hfns_ok : mod.fns.all TFlatFn0.okGuardsFull = true := by
    simp only [TFlatModule0.okGuardsFull, Bool.and_eq_true] at hg; exact hg.1.2
  have hfns_lt32 : mod.fns.length < 2 ^ 32 := TFlatModule0.okGuardsFull_fns_length hg
  intro seen rest
  induction rest generalizing seen with
  | nil => intro _ _ _ hmem; nomatch hmem
  | cons cur tail ih =>
    intro hsp hseen fn hmem
    have hsplit_cur : mod.fns = seen ++ cur :: tail := hsp
    have hcur_mem : cur ∈ mod.fns := hsp ▸ by simp
    have hcur_legal := hl_snd.2.2 cur hcur_mem
    have hcur_guard : cur.okGuardsFull = true := List.all_eq_true.mp hfns_ok cur hcur_mem
    have hcur_inf := compileModuleLoop0_fn_infix (pre := seen) (fn := cur) (post := tail)
      (symName := symName) 0 0 (hsplit_cur ▸ hinf)
    rw [UInt32.zero_add] at hcur_inf
    have hdef_cur : x64ScalarTarget.Defined h (symName cur.name) :=
      compileFn0_defined (UInt32.ofNat seen.length) cur hcur_guard hcur_inf
    have hpre_len_lt : seen.length < 2 ^ 32 := by
      have := congrArg List.length hsplit_cur
      simp only [List.length_append, List.length_cons] at this
      omega
    have hcur_bds := hmod_bd.2 seen cur tail hsplit_cur
    dsimp only at hcur_bds
    let sigs := prepSigsFns0 mod.fns (prepSigsExts0 mod.externs [])
    let ctx : LegalCtx0 := LegalCtx0.mk sigs mod.exits cur.rs
    have hallowed : ∀ f as bs,
        (f, as, bs) ∈ seen.map TFlatFn0.sig0 ++ mod.externs.map ExtSig0.sig0 →
        x64ScalarTarget.Defined h (symName f) ∧
        x64ScalarTarget.FnSpec h (symName f)
          (Γ (symName f) (ty0ListToTy as) (ty0ListToTy bs)) (bound f) nX := by
      intro f as bs hmem_a
      rcases List.mem_append.mp hmem_a with hs | he
      · rw [List.mem_map] at hs
        obtain ⟨g, hg_mem, hsig⟩ := hs
        injection hsig with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact hseen g hg_mem
      · rw [List.mem_map] at he
        obtain ⟨ex, hex_mem, hsig⟩ := he
        injection hsig with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact hext ex hex_mem
    have hc_node : NodeContracts0 h symName Γ ctx
        (compileFn0 (UInt32.ofNat seen.length) cur).2 (bound cur.name) nX cur.body :=
      nodeContracts0_of_callsAcyclic0 (ctx := ctx) hcur_bds.2.2 hallowed hexits
    have hspec_wp := compileFn0_fnSpec (h := h) (symName := symName) (Γ := Γ) (ctx := ctx)
      (UInt32.ofNat seen.length) cur (n := bound cur.name) (nX := nX)
      hcur_legal.1 hcur_legal.2.1 rfl hcur_legal.2.2.1 hcur_guard
      hcur_bds.1 hcur_bds.2.1 hcur_inf hu hc_node
    have hspec_cur : x64ScalarTarget.FnSpec h (symName cur.name)
        (Γ (symName cur.name) (ty0ListToTy cur.as) (ty0ListToTy cur.rs)) (bound cur.name) nX :=
      fun args m Q X hΓ => hspec_wp args m Q X (hwp cur hcur_mem args m Q X hΓ)
    rcases List.mem_cons.mp hmem with rfl | htail
    · exact ⟨hdef_cur, hspec_cur⟩
    · refine ih (seen ++ [cur]) (by simpa [List.append_assoc] using hsplit_cur) ?_ fn htail
      intro q hq
      rcases List.mem_append.mp hq with hq_s | hq_c
      · exact hseen q hq_s
      · simp only [List.mem_singleton] at hq_c; subst hq_c; exact ⟨hdef_cur, hspec_cur⟩

/-- General module soundness for `compileModuleLoop0` on any well-formed host `h`. -/
theorem compileModuleLoop0_sound {h : Host} {symName : Sym0 → Sym} {Γ : Env}
    {mod : TFlatModule0} {nX k₀ : Nat} {bound : Sym0 → Nat}
    (hl : legalMod0 mod = 0) (hg : mod.okGuardsFull = true)
    (hinf : (toAmd64Program symName (compileModuleLoop0 mod.fns 0 0 []).1).IsInfixAt
      (x64ScalarMach.prog h) k₀)
    (hu : x64ScalarTarget.LabelsUnique h)
    (hmod_bd : ModBoundsOk0 mod nX bound)
    (hext : ∀ ex ∈ mod.externs,
      x64ScalarTarget.Defined h (symName ex.name) ∧
      x64ScalarTarget.FnSpec h (symName ex.name)
        (Γ (symName ex.name) (ty0ListToTy ex.as) (ty0ListToTy ex.rs)) (bound ex.name) nX)
    (hexits : ∀ g ∈ mod.exits, x64ScalarTarget.Defined h (symName g))
    (hwp : ∀ fn ∈ mod.fns, ∀ (args : Tup Val (ty0ListToTy fn.as)) m Q X,
      Γ (symName fn.name) (ty0ListToTy fn.as) (ty0ListToTy fn.rs) args m Q X →
      wp0 Γ symName fn.rs (pushTup args []) [] Q X fn.body m) :
    ∀ fn ∈ mod.fns,
      x64ScalarTarget.Defined h (symName fn.name) ∧
      x64ScalarTarget.FnSpec h (symName fn.name)
        (Γ (symName fn.name) (ty0ListToTy fn.as) (ty0ListToTy fn.rs)) (bound fn.name) nX :=
  fun fn hmem =>
    compileModuleLoop0_sound_prefix (TFlatModule0.okGuardsFull_sigLensFitU32 hg) hl hg hinf hu
      hmod_bd hext hexits hwp [] mod.fns rfl (fun _ h => nomatch h) fn hmem

private theorem legalMod0_eq_zero_of_leanqbe0Compile {mod : TFlatModule0} {dirs : List Dir0}
    {maxSl : UInt32} (hc : leanqbe0Compile mod = .ok dirs maxSl) :
    legalMod0 mod = 0 ∧ dirs = (compileModuleLoop0 mod.fns 0 0 []).1 ∧
    maxSl = (compileModuleLoop0 mod.fns 0 0 []).2 := by
  dsimp only [leanqbe0Compile] at hc
  split at hc
  · rename_i hl
    injection hc with hd hm
    exact ⟨hl, hd.symm, hm.symm⟩
  · cases hc

/-- Headline end-to-end semantic soundness for `leanqbe0Compile`: whenever `leanqbe0Compile mod =
.ok dirs maxSl`, `mod.okGuardsFull = true`, `h` hosts `toAmd64Program symName dirs` with unique
labels, and callees/exits satisfy acyclic contracts `ModBoundsOk0`, every function in `mod.fns`
satisfies `x64ScalarTarget.Defined` and `x64ScalarTarget.FnSpec`. -/
theorem leanqbe0Compile_fnSpec {h : Host} {symName : Sym0 → Sym} {Γ : Env}
    {mod : TFlatModule0} {dirs : List Dir0} {maxSl : UInt32} {nX k₀ : Nat} {bound : Sym0 → Nat}
    (hc : leanqbe0Compile mod = .ok dirs maxSl) (hg : mod.okGuardsFull = true)
    (hinf : (toAmd64Program symName dirs).IsInfixAt (x64ScalarMach.prog h) k₀)
    (hu : x64ScalarTarget.LabelsUnique h)
    (hmod_bd : ModBoundsOk0 mod nX bound)
    (hext : ∀ ex ∈ mod.externs,
      x64ScalarTarget.Defined h (symName ex.name) ∧
      x64ScalarTarget.FnSpec h (symName ex.name)
        (Γ (symName ex.name) (ty0ListToTy ex.as) (ty0ListToTy ex.rs)) (bound ex.name) nX)
    (hexits : ∀ g ∈ mod.exits, x64ScalarTarget.Defined h (symName g))
    (hwp : ∀ fn ∈ mod.fns, ∀ (args : Tup Val (ty0ListToTy fn.as)) m Q X,
      Γ (symName fn.name) (ty0ListToTy fn.as) (ty0ListToTy fn.rs) args m Q X →
      wp0 Γ symName fn.rs (pushTup args []) [] Q X fn.body m) :
    ∀ fn ∈ mod.fns,
      x64ScalarTarget.Defined h (symName fn.name) ∧
      x64ScalarTarget.FnSpec h (symName fn.name)
        (Γ (symName fn.name) (ty0ListToTy fn.as) (ty0ListToTy fn.rs)) (bound fn.name) nX := by
  obtain ⟨hl, rfl, _⟩ := legalMod0_eq_zero_of_leanqbe0Compile hc
  exact compileModuleLoop0_sound hl hg hinf hu hmod_bd hext hexits hwp

/-- Standalone concrete-host soundness theorem constructing `h := x64ScalarLayout.layoutOf prog`
and proving `x64ScalarTarget.LabelsUnique h` and exit `Defined` automatically. -/
theorem leanqbe0Compile_sound_layout {symName : Sym0 → Sym} {Γ : Env} {mod : TFlatModule0}
    {dirs : List Dir0} {maxSl : UInt32} {nX : Nat} {bound : Sym0 → Nat}
    (hc : leanqbe0Compile mod = .ok dirs maxSl) (hg : mod.okGuardsFull = true)
    (hnd : (mod.fns.map (fun fn => symName fn.name) ++ mod.exits.map symName).Nodup)
    (hnoloc_fns : ∀ fn ∈ mod.fns, symNoLocPrefix0 (symName fn.name) = true)
    (hnoloc_ex : ∀ g ∈ mod.exits, symNoLocPrefix0 (symName g) = true)
    (hsmall : x64ScalarProgSmall
      (toAmd64Program symName dirs ++ mod.exits.map (fun g => x64Frame.label (symName g))) = true)
    (hmod_bd : ModBoundsOk0 mod nX bound)
    (hext : ∀ ex ∈ mod.externs,
      let h := x64ScalarLayout.layoutOf
        (toAmd64Program symName dirs ++ mod.exits.map (fun g => x64Frame.label (symName g)))
        hsmall
      x64ScalarTarget.Defined h (symName ex.name) ∧
      x64ScalarTarget.FnSpec h (symName ex.name)
        (Γ (symName ex.name) (ty0ListToTy ex.as) (ty0ListToTy ex.rs)) (bound ex.name) nX)
    (hwp : ∀ fn ∈ mod.fns, ∀ (args : Tup Val (ty0ListToTy fn.as)) m Q X,
      Γ (symName fn.name) (ty0ListToTy fn.as) (ty0ListToTy fn.rs) args m Q X →
      wp0 Γ symName fn.rs (pushTup args []) [] Q X fn.body m) :
    let h := x64ScalarLayout.layoutOf
      (toAmd64Program symName dirs ++ mod.exits.map (fun g => x64Frame.label (symName g)))
      hsmall
    x64ScalarTarget.LabelsUnique h ∧
    ∀ fn ∈ mod.fns,
      x64ScalarTarget.Defined h (symName fn.name) ∧
      x64ScalarTarget.FnSpec h (symName fn.name)
        (Γ (symName fn.name) (ty0ListToTy fn.as) (ty0ListToTy fn.rs)) (bound fn.name) nX := by
  obtain ⟨hl, hd_eq, _⟩ := legalMod0_eq_zero_of_leanqbe0Compile hc
  let prog := toAmd64Program symName dirs ++ mod.exits.map (fun g => x64Frame.label (symName g))
  let h := x64ScalarLayout.layoutOf prog hsmall
  have hl_prog := x64ScalarLayout.prog_layoutOf prog hsmall
  change x64ScalarMach.prog h = prog at hl_prog
  have hprog : x64ScalarMach.prog h =
      toAmd64Program symName (compileModuleLoop0 mod.fns 0 0 []).1 ++
        (mod.exits.map symName).map x64Frame.label := by
    rw [hl_prog]; dsimp only [prog]; rw [hd_eq, List.map_map]; try rfl
  have hfns_g : ∀ fn ∈ mod.fns, fn.okGuardsFull = true := by
    simp only [TFlatModule0.okGuardsFull, Bool.and_eq_true, List.all_eq_true] at hg
    exact hg.1.2
  have hfns_bd : (0 : UInt32).toNat + mod.fns.length < 2 ^ 32 := by
    have := TFlatModule0.okGuardsFull_fns_length hg
    rw [UInt32.toNat_zero, Nat.zero_add]
    omega
  obtain ⟨hu, hexits⟩ := compileModuleLoop0_host_labelsUnique (symName := symName)
    (fns := mod.fns) (idx0 := 0) (maxSl := 0) (exitSyms := mod.exits.map symName)
    hprog hfns_bd hfns_g hnd hnoloc_fns (fun _ hm => by
      rw [List.mem_map] at hm
      obtain ⟨g, hg_mem, rfl⟩ := hm
      exact hnoloc_ex g hg_mem)
  have hinf : (toAmd64Program symName dirs).IsInfixAt (x64ScalarMach.prog h) 0 := by
    rw [hl_prog]
    exact ⟨mod.exits.map (fun g => x64Frame.label (symName g)), rfl⟩
  have hexits' : ∀ g ∈ mod.exits, x64ScalarTarget.Defined h (symName g) := fun g hg_mem =>
    hexits (symName g) (List.mem_map_of_mem hg_mem)
  exact ⟨hu, leanqbe0Compile_fnSpec hc hg hinf hu hmod_bd hext hexits' hwp⟩

/-- Direct single-function specialization of `leanqbe0Compile` returning raw `wp0` soundness without
requiring a fixed caller-supplied `Γ` wrapper on `fn` itself. -/
theorem leanqbe0Compile_singleFn_fnSpec {h : Host} {symName : Sym0 → Sym} {Γ : Env}
    {fn : TFlatFn0} {externs : List ExtSig0} {exits : List Sym0} {dirs : List Dir0}
    {maxSl : UInt32} {n nX k₀ : Nat} {bound : Sym0 → Nat}
    (hc : leanqbe0Compile { fns := [fn], externs := externs, exits := exits } = .ok dirs maxSl)
    (hg : fn.okGuardsFull = true)
    (hext_fit : externs.all (fun ex => listLenFitsU32 ex.as && listLenFitsU32 ex.rs) = true)
    (hinf : (toAmd64Program symName dirs).IsInfixAt (x64ScalarMach.prog h) k₀)
    (hu : x64ScalarTarget.LabelsUnique h)
    (hframe_le : x64FrameSize (compileFn0 0 fn).2.toNat ≤ n) (hn_bd : n + 8 ≤ 2 ^ 64)
    (hcalls : CallsAcyclic0 fn.rs bound (externs.map ExtSig0.sig0) exits
      (x64FrameSize (compileFn0 0 fn).2.toNat) n nX fn.body)
    (hext : ∀ ex ∈ externs,
      x64ScalarTarget.Defined h (symName ex.name) ∧
      x64ScalarTarget.FnSpec h (symName ex.name)
        (Γ (symName ex.name) (ty0ListToTy ex.as) (ty0ListToTy ex.rs)) (bound ex.name) nX)
    (hexits : ∀ g ∈ exits, x64ScalarTarget.Defined h (symName g)) :
    x64ScalarTarget.Defined h (symName fn.name) ∧
    x64ScalarTarget.FnSpec h (symName fn.name)
      (fun (args : Tup Val (ty0ListToTy fn.as)) m Q X =>
        wp0 Γ symName fn.rs (pushTup args []) [] Q X fn.body m) n nX := by
  let mod : TFlatModule0 := { fns := [fn], externs := externs, exits := exits }
  have hg_mod : mod.okGuardsFull = true := by
    simp [mod, TFlatModule0.okGuardsFull, hg, hext_fit]
  obtain ⟨hl, rfl, _⟩ := legalMod0_eq_zero_of_leanqbe0Compile hc
  have hl_snd := legalMod0_sound mod hl (TFlatModule0.okGuardsFull_sigLensFitU32 hg_mod)
  have hfn_l := hl_snd.2.2 fn List.mem_cons_self
  have hfn_inf : (toAmd64Program symName (compileFn0 0 fn).1).IsInfixAt
      (x64ScalarMach.prog h) k₀ := by
    rw [compileModuleLoop0_cons, show (compileModuleLoop0 [] (0 + 1) 0 []).1 = [] from rfl,
      List.append_nil] at hinf
    exact hinf
  have hallowed : ∀ f as bs, (f, as, bs) ∈ externs.map ExtSig0.sig0 →
      x64ScalarTarget.Defined h (symName f) ∧
      x64ScalarTarget.FnSpec h (symName f)
        (Γ (symName f) (ty0ListToTy as) (ty0ListToTy bs)) (bound f) nX := by
    intro f as bs hm
    rw [List.mem_map] at hm
    obtain ⟨ex, hex, hsig⟩ := hm
    injection hsig with h1 h2
    injection h2 with h2 h3
    subst h1; subst h2; subst h3
    exact hext ex hex
  let sigs := prepSigsFns0 mod.fns (prepSigsExts0 mod.externs [])
  let ctx := LegalCtx0.mk sigs exits fn.rs
  have hc_node : NodeContracts0 h symName Γ ctx (compileFn0 0 fn).2 n nX fn.body :=
    nodeContracts0_of_callsAcyclic0 (ctx := ctx) hcalls hallowed hexits
  exact ⟨compileFn0_defined 0 fn hg hfn_inf,
    compileFn0_fnSpec 0 fn hfn_l.1 hfn_l.2.1 rfl hfn_l.2.2.1 hg hframe_le hn_bd
      hfn_inf hu hc_node⟩

/-- Composition of `leanqbe0Compile` with `PrintAsm0.printAsm0`: exact emitted AT&T assembly text
agreement with `Kraken.X64.toATT`. -/
theorem leanqbe0Compile_printAsm0 {symName : Sym0 → Sym} {mod : TFlatModule0}
    {dirs : List Dir0} {maxSl : UInt32} (_hc : leanqbe0Compile mod = .ok dirs maxSl) :
    printAsm0 (toAmd64Program symName dirs) =
      Kraken.X64.toATT (toAmd64Program symName dirs) :=
  toAmd64Program_printAsm0 symName dirs

/-- Composition of `leanqbe0Compile` with `PrintAsm0.printModule0`: exact full-module `.text` +
`.globl` + `Kraken.X64.toATT` output. -/
theorem leanqbe0Compile_printModule0 {fnNames : List String} {symName : Sym0 → Sym}
    {mod : TFlatModule0} {dirs : List Dir0} {maxSl : UInt32}
    (_hc : leanqbe0Compile mod = .ok dirs maxSl) :
    printModule0 fnNames (toAmd64Program symName dirs) =
      ".text\n" ++
        String.join (fnNames.map fun n => s!".globl {n}\n") ++
        if (toAmd64Program symName dirs).isEmpty then ""
        else Kraken.X64.toATT (toAmd64Program symName dirs) ++ "\n" :=
  toAmd64Program_printModule0 fnNames symName dirs

/-! ## 5. End-to-End `Bridge0.ofTFlatModule` + `Module.checkAcyclic` + `ModuleOk` Pipeline -/

private theorem except_bind_eq_ok {α β ε : Type} (x : Except ε α) (f : α → Except ε β)
    (y : β) (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => simp [bind, Except.bind] at h; exact ⟨a, rfl, h⟩

private theorem ty0ToTy_tyToTy0_loc {t : Ty} {t0 : Ty0} (h : tyToTy0 t = .ok t0) :
    ty0ToTy t0 = t := by
  cases t with
  | bool => cases h; rfl
  | bits n =>
    by_cases h8 : n = 8
    · subst h8; cases h; rfl
    · by_cases h16 : n = 16
      · subst h16; cases h; rfl
      · by_cases h32 : n = 32
        · subst h32; cases h; rfl
        · by_cases h64 : n = 64
          · subst h64; cases h; rfl
          · simp [tyToTy0, h8, h16, h32, h64] at h
  | float _ | pair _ _ => cases h

private theorem ty0ListToTy_tyListToTy0_loc :
    ∀ {ts : List Ty} {ts0 : List Ty0}, tyListToTy0 ts = .ok ts0 → ty0ListToTy ts0 = ts
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | t :: ts, ts0, h => by
    dsimp only [tyListToTy0] at h
    obtain ⟨t0, ht, h⟩ := except_bind_eq_ok _ _ _ h
    obtain ⟨rest0, hts, h⟩ := except_bind_eq_ok _ _ _ h
    simp only [Except.ok.injEq] at h
    subst h
    dsimp only [ty0ListToTy]
    rw [List.map_cons, ty0ToTy_tyToTy0_loc ht]
    exact congrArg (t :: ·) (ty0ListToTy_tyListToTy0_loc hts)

private inductive Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall2 R [] []
  | cons : ∀ {a b as bs}, R a b → Forall2 R as bs → Forall2 R (a :: as) (b :: bs)

private theorem Forall2.imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → Forall2 S xs ys
  | _, _, .nil => .nil
  | _, _, .cons r hr => .cons (h _ _ r) (hr.imp h)

private theorem Forall2.append {α β : Type} {R : α → β → Prop} :
    ∀ {xs₁ xs₂ : List α} {ys₁ ys₂ : List β},
      Forall2 R xs₁ ys₁ → Forall2 R xs₂ ys₂ → Forall2 R (xs₁ ++ xs₂) (ys₁ ++ ys₂)
  | _, _, _, _, .nil, h₂ => h₂
  | _, _, _, _, .cons r h₁, h₂ => .cons r (Forall2.append h₁ h₂)

private theorem Forall2.map {α β γ δ : Type} {R : γ → δ → Prop} (f : α → γ) (g : β → δ) :
    ∀ {xs : List α} {ys : List β},
      Forall2 (fun x y => R (f x) (g y)) xs ys → Forall2 R (xs.map f) (ys.map g)
  | _, _, .nil => .nil
  | _, _, .cons r hr => .cons r (hr.map f g)

private theorem Forall2.exists_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → ∀ {a : α}, a ∈ xs → ∃ b ∈ ys, R a b
  | _, _, .cons h hr, _, ha => by
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨b, hb, hrel⟩ := hr.exists_mem_left ha'
      exact ⟨b, List.mem_cons_of_mem _ hb, hrel⟩

private theorem Forall2.exists_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → ∀ {b : β}, b ∈ ys → ∃ a ∈ xs, R a b
  | _, _, .cons h hr, _, hb => by
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨a, ha, hrel⟩ := hr.exists_mem_right hb'
      exact ⟨a, List.mem_cons_of_mem _ ha, hrel⟩

private theorem list_mapM_loop_except {α β ε : Type} (f : α → Except ε β) :
    ∀ (xs : List α) (acc ys : List β),
      List.mapM.loop f xs acc = .ok ys →
      ∃ zs, ys = acc.reverse ++ zs ∧ Forall2 (fun x y => f x = .ok y) xs zs
  | [], acc, ys, h => by
    simp only [List.mapM.loop, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨[], by simpa using h.symm, .nil⟩
  | x :: xs, acc, ys, h => by
    dsimp only [List.mapM.loop] at h
    cases hx : f x with
    | error e => rw [hx] at h; cases h
    | ok y =>
      rw [hx] at h; dsimp only [bind, Except.bind] at h
      obtain ⟨zs, hys, hrel⟩ := list_mapM_loop_except f xs (y :: acc) ys h
      refine ⟨y :: zs, ?_, .cons hx hrel⟩
      simpa [List.reverse_cons, List.append_assoc] using hys

private theorem list_mapM_except_forall₂ {α β ε : Type} (f : α → Except ε β)
    {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys) :
    Forall2 (fun x y => f x = .ok y) xs ys := by
  obtain ⟨zs, hys, hrel⟩ := list_mapM_loop_except f xs [] ys h
  simpa using hys ▸ hrel

private theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ xs : List α, xs.eraseDups.Nodup
  | [] => by rw [List.eraseDups_nil]; exact List.nodup_nil
  | a :: as => by
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, ?_⟩
    · rw [List.mem_eraseDups, List.mem_filter] at hm
      simp at hm
    · have : (List.filter (fun b => !b == a) as).length ≤ as.length :=
        List.length_filter_le _ _
      exact eraseDups_nodup (List.filter (fun b => !b == a) as)
termination_by xs => xs.length

private theorem ofTFlatModule_symTable_props (tfs : List Frontend.C0.TFlatFn)
    (externs : List Extern) (exits : List Sym) {mod : TFlatModule0} {tbl : List (Sym × Sym0)}
    (hof : ofTFlatModule tfs externs exits = .ok (mod, tbl))
    (hlt : tbl.length < 2 ^ 32) :
    (∀ s fid, lookupSymId? tbl s = some fid → symNameOf tbl fid = s) ∧
    Forall2 (fun tf fn0 =>
      lookupSymId? tbl tf.name = some fn0.name ∧
      ty0ListToTy fn0.as = tf.as ∧
      ty0ListToTy fn0.rs = tf.rs ∧
      tflatToTFlat0 tbl tf.flat = .ok fn0.body) tfs mod.fns ∧
    Forall2 (fun ex ex0 =>
      lookupSymId? tbl ex.name = some ex0.name ∧
      ty0ListToTy ex0.as = ex.as ∧
      ty0ListToTy ex0.rs = ex.rs) externs mod.externs ∧
    Forall2 (fun g g0 => lookupSymId? tbl g = some g0) exits mod.exits := by
  dsimp only [ofTFlatModule] at hof
  let allNames := (tfs.map (·.name) ++ externs.map (·.name) ++ exits).eraseDups
  let tbl' := allNames.zip ((List.range allNames.length).map UInt32.ofNat)
  have hof' :
      (do
        let fns0 ← tfs.mapM fun (tf : Frontend.C0.TFlatFn) => do
          let some fid := lookupSymId? tbl' tf.name
            | .error s!"ofTFlatModule: missing fn '{tf.name}'"
          let as0 ← tyListToTy0 tf.as
          let rs0 ← tyListToTy0 tf.rs
          let body0 ← tflatToTFlat0 tbl' tf.flat
          .ok { name := fid, as := as0, rs := rs0, body := body0 : TFlatFn0 }
        let exts0 ← externs.mapM fun (ex : Extern) => do
          let some eid := lookupSymId? tbl' ex.name
            | .error s!"ofTFlatModule: missing extern '{ex.name}'"
          let as0 ← tyListToTy0 ex.as
          let rs0 ← tyListToTy0 ex.rs
          .ok { name := eid, as := as0, rs := rs0 : ExtSig0 }
        let exits0 ← exits.mapM fun (ex : Sym) => do
          let some eid := lookupSymId? tbl' ex
            | .error s!"ofTFlatModule: missing exit '{ex}'"
          .ok eid
        .ok (({ fns := fns0, externs := exts0, exits := exits0 } : TFlatModule0), tbl')) =
      .ok (mod, tbl) := hof
  obtain ⟨fns0, hf0, hof1⟩ := except_bind_eq_ok _ _ _ hof'
  obtain ⟨exts0, he0, hof2⟩ := except_bind_eq_ok _ _ _ hof1
  obtain ⟨exits0, hx0, hof3⟩ := except_bind_eq_ok _ _ _ hof2
  simp only [Except.ok.injEq, Prod.mk.injEq] at hof3
  rcases hof3 with ⟨rfl, rfl⟩
  have hlen_tbl : tbl'.length = allNames.length := by
    dsimp only [tbl']
    simp only [List.length_zip, List.length_map, List.length_range, Nat.min_self]
  have hall_lt : allNames.length < 2 ^ 32 := hlen_tbl ▸ hlt
  have hnd1 : (tbl'.map Prod.fst).Nodup := by
    dsimp only [tbl']
    rw [List.map_fst_zip (by simp only [List.length_map, List.length_range, le_refl])]
    exact eraseDups_nodup _
  have hnd2 : (tbl'.map Prod.snd).Nodup := by
    dsimp only [tbl']
    rw [List.map_snd_zip (by simp only [List.length_map, List.length_range, le_refl])]
    have map_nodup_of_injOn : ∀ {xs : List Nat}, xs.Nodup →
        (∀ a ∈ xs, ∀ b ∈ xs, UInt32.ofNat a = UInt32.ofNat b → a = b) →
        (xs.map UInt32.ofNat).Nodup := by
      intro xs
      induction xs with
      | nil => intro _ _; exact List.nodup_nil
      | cons x xs ih =>
        intro hnd hinj
        simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
        simp only [List.nodup_cons] at hnd
        refine ⟨fun a ha he => hnd.1 ((hinj _ (List.mem_cons_of_mem _ ha) _
          List.mem_cons_self he) ▸ ha), ih hnd.2 fun a ha b hb =>
            hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)⟩
    refine map_nodup_of_injOn List.nodup_range fun x hx y hy he => ?_
    rw [List.mem_range] at hx hy
    have hxn : (UInt32.ofNat x).toNat = x := by
      rw [u32_toNat_ofNat0, Nat.mod_eq_of_lt (by omega)]
    have hyn : (UInt32.ofNat y).toNat = y := by
      rw [u32_toNat_ofNat0, Nat.mod_eq_of_lt (by omega)]
    rw [← hxn, ← hyn, he]
  refine ⟨fun _ _ => lookupSymId?_symNameOf tbl' hnd1 hnd2, ?_, ?_, ?_⟩
  · refine (list_mapM_except_forall₂ _ hf0).imp fun tf fn0 h => ?_
    cases hfid : lookupSymId? tbl' tf.name with
    | none => rw [hfid] at h; cases h
    | some fid =>
      rw [hfid] at h; dsimp only at h
      obtain ⟨as0, has, h⟩ := except_bind_eq_ok _ _ _ h
      obtain ⟨rs0, hrs, h⟩ := except_bind_eq_ok _ _ _ h
      obtain ⟨body0, hbd, h⟩ := except_bind_eq_ok _ _ _ h
      simp only [Except.ok.injEq] at h
      subst h
      exact ⟨rfl, ty0ListToTy_tyListToTy0_loc has,
        ty0ListToTy_tyListToTy0_loc hrs, hbd⟩
  · refine (list_mapM_except_forall₂ _ he0).imp fun ex ex0 h => ?_
    cases hfid : lookupSymId? tbl' ex.name with
    | none => rw [hfid] at h; cases h
    | some fid =>
      rw [hfid] at h; dsimp only at h
      obtain ⟨as0, has, h⟩ := except_bind_eq_ok _ _ _ h
      obtain ⟨rs0, hrs, h⟩ := except_bind_eq_ok _ _ _ h
      simp only [Except.ok.injEq] at h
      subst h
      exact ⟨rfl, ty0ListToTy_tyListToTy0_loc has,
        ty0ListToTy_tyListToTy0_loc hrs⟩
  · refine (list_mapM_except_forall₂ _ hx0).imp fun g g0 h => ?_
    cases hfid : lookupSymId? tbl' g with
    | none => rw [hfid] at h; cases h
    | some eid =>
      rw [hfid] at h; simp only [Except.ok.injEq] at h
      subst h; rfl

private theorem list_get?_map_fst {α : Type} {f : α → Type} :
    ∀ {xs : List ((a : α) × f a)} {vT : List α} {i : Nat} {a : α},
      xs.map Sigma.fst = vT → listGet? vT i = some a →
      ∃ x : f a, listGet? xs i = some ⟨a, x⟩
  | [], [], i, _, _, hg => by cases i <;> (dsimp only [listGet?] at hg; cases hg)
  | _ :: _, [], _, _, hm, _ => by simp at hm
  | [], _ :: _, _, _, hm, _ => by simp at hm
  | ⟨a', x⟩ :: xs, t :: vT, 0, a, hm, hg => by
    simp only [List.map_cons, List.cons.injEq] at hm
    dsimp only [listGet?] at hg ⊢
    injection hg with hta; subst hta; cases hm.1
    exact ⟨x, rfl⟩
  | _ :: xs, _ :: vT, i + 1, a, hm, hg => by
    simp only [List.map_cons, List.cons.injEq] at hm
    dsimp only [listGet?] at hg ⊢
    exact list_get?_map_fst hm.2 hg

private theorem castTy_unit_refl (t : Ty) :
    @castTy (fun _ => Unit) t t () = some () := by
  cases t with
  | bool => rfl
  | bits n => simp [castTy]
  | float f => simp [castTy]
  | pair a b =>
    dsimp only [castTy]
    have hd : ∀ x : Ty, tyDecEq x x = isTrue rfl := by
      intro x
      induction x with
      | bool => rfl
      | bits _ | float _ => dsimp only [tyDecEq]; split <;> first | rfl | contradiction
      | pair x y ix iy => dsimp only [tyDecEq]; rw [ix, iy]
    rw [hd a, hd b]

private theorem castListTy_unit_refl (ts : List Ty) :
    @castListTy (fun _ => Unit) ts ts () = some () := by
  dsimp only [castListTy]
  have hd : ∀ xs : List Ty, listTyDecEq xs xs = isTrue rfl := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      have htx : tyDecEq x x = isTrue rfl := by
        induction x with
        | bool => rfl
        | bits _ | float _ => dsimp only [tyDecEq]; split <;> first | rfl | contradiction
        | pair a b ia ib => dsimp only [tyDecEq]; rw [ia, ib]
      dsimp only [listTyDecEq]; rw [htx, ih]
  rw [hd ts]

private theorem denoteArg_unit_isSome {vT : List Ty} {vs : List ((_ : Ty) × Unit)}
    (hvs : vs.map Sigma.fst = vT) {t : Ty} {a : Arg K t} (ha : checkArg vT t a = true) :
    denoteArg vs a = some (match a with | .var _ => .var () | .imm c => .imm c) := by
  cases a with
  | imm c => rfl
  | var i =>
    dsimp only [checkArg] at ha
    cases hl : listGet? vT i with
    | none => rw [hl] at ha; cases ha
    | some t' =>
      rw [hl] at ha; dsimp only at ha
      cases hd : tyDecEq t' t with
      | isTrue heq =>
        subst heq
        obtain ⟨u, hxs⟩ := list_get?_map_fst hvs hl
        cases u
        dsimp only [denoteArg, lookupV]
        rw [hxs]; dsimp only; rw [castTy_unit_refl t']
      | isFalse _ => rw [hd] at ha; cases ha

private theorem denoteArgs_unit_isSome {vT : List Ty} {vs : List ((_ : Ty) × Unit)}
    (hvs : vs.map Sigma.fst = vT) :
    ∀ {ts : List Ty} {args : Tup (Arg K) ts},
      checkArgs vT args = true → ∃ args', denoteArgs vs args = some args'
  | [], (), _ => ⟨(), rfl⟩
  | _ :: ts, (a, rest), h => by
    dsimp only [checkArgs] at h; rw [Bool.and_eq_true] at h
    obtain ⟨r', hr'⟩ := denoteArgs_unit_isSome hvs h.2
    exact ⟨_, by dsimp only [denoteArgs]; rw [denoteArg_unit_isSome hvs h.1, hr']⟩

private theorem lookupL_unit_isSome {lT : List (List Ty)} {ls : List ((_ : List Ty) × Unit)}
    (hls : ls.map Sigma.fst = lT) {ts : List Ty} {j : Nat}
    (hj : (match listGet? lT j with
      | some ts' => match listTyDecEq ts' ts with | isTrue _ => true | isFalse _ => false
      | none => false) = true) :
    lookupL ls ts j = some () := by
  cases hl : listGet? lT j with
  | none => rw [hl] at hj; cases hj
  | some ts' =>
    rw [hl] at hj; dsimp only at hj
    cases hd : listTyDecEq ts' ts with
    | isTrue heq =>
      subst heq
      obtain ⟨u, hls'⟩ := list_get?_map_fst hls hl
      cases u
      dsimp only [lookupL]
      rw [hls']; dsimp only; rw [castListTy_unit_refl ts']
    | isFalse _ => rw [hd] at hj; cases hj

private theorem pushTup_map_fst {α : Type} {f : α → Type} :
    ∀ {ts : List α} (xs : Tup f ts) (acc : List ((a : α) × f a)),
      (pushTup xs acc).map Sigma.fst = pushTypes ts (acc.map Sigma.fst)
  | [], (), acc => rfl
  | a :: ts, (x, xs), acc => by
    dsimp only [pushTup, pushTypes]
    exact pushTup_map_fst xs (⟨a, x⟩ :: acc)

mutual
private theorem tflatToTFlat0_checkCallsOk0 {tbl : List (Sym × Sym0)}
    (hsym : ∀ s fid, lookupSymId? tbl s = some fid → symNameOf tbl fid = s)
    {allowed0 : List (Sym0 × List Ty0 × List Ty0)} {allowed : List SigEntry}
    {exits0 : List Sym0} {exits : List Sym} {rs0 : List Ty0}
    (hal : ∀ s (fid : Sym0) as0 bs0, lookupSymId? tbl s = some fid →
      (s, ty0ListToTy as0, ty0ListToTy bs0) ∈ allowed → (fid, as0, bs0) ∈ allowed0)
    (hex : ∀ s (fid : Sym0), lookupSymId? tbl s = some fid → s ∈ exits → fid ∈ exits0) :
    ∀ {rs : List Ty} (tf : TFlat rs) (tf0 : TFlat0)
      (vT : List Ty) (lT : List (List Ty))
      (vs : List ((_ : Ty) × Unit)) (ls : List ((_ : List Ty) × Unit)),
      tflatToTFlat0 tbl tf = .ok tf0 →
      tf.wfCheck vT lT = true →
      vs.map Sigma.fst = vT →
      ls.map Sigma.fst = lT →
      (denote (fun _ => Unit) (fun _ => Unit) tf vs ls).callsOk allowed exits →
      tf0.checkCallsOk0 allowed0 rs0 exits0 = true
  | _, .let_ op k, tf0, vT, lT, vs, ls, htf, hwf, hvs, hls, hco => by
    dsimp only [tflatToTFlat0] at htf
    dsimp only [TFlat.wfCheck] at hwf; rw [Bool.and_eq_true] at hwf
    obtain ⟨k0, hk0, htf⟩ := except_bind_eq_ok _ _ _ htf
    dsimp only [opToTFlat0] at htf
    obtain ⟨args0, _, htf⟩ := except_bind_eq_ok _ _ _ htf
    obtain ⟨args', hda⟩ := denoteArgs_unit_isSome hvs hwf.1
    dsimp only [denote] at hco; rw [hda] at hco; dsimp only [Expr.callsOk] at hco
    have hk := tflatToTFlat0_checkCallsOk0 (rs0 := rs0) hsym hal hex k k0 (pushTypes _ vT) lT
      (pushTup (Tup.units _) vs) ls hk0 hwf.2 (by rw [pushTup_map_fst, hvs]) hls hco
    rcases opCodeToTFlat0_cases op.code args0 k0 tf0 htf with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
      exact hk
  | _, .load t a k, tf0, vT, lT, vs, ls, htf, hwf, hvs, hls, hco => by
    dsimp only [tflatToTFlat0] at htf
    dsimp only [TFlat.wfCheck] at hwf; rw [Bool.and_eq_true] at hwf
    obtain ⟨t0, _, htf⟩ := except_bind_eq_ok _ _ _ htf
    obtain ⟨a0, _, htf⟩ := except_bind_eq_ok _ _ _ htf
    obtain ⟨k0, hk0, htf⟩ := except_bind_eq_ok _ _ _ htf
    simp only [Except.ok.injEq] at htf; subst htf
    dsimp only [denote] at hco; rw [denoteArg_unit_isSome hvs hwf.1] at hco
    dsimp only [Expr.callsOk] at hco
    dsimp only [TFlat0.checkCallsOk0]
    exact tflatToTFlat0_checkCallsOk0 hsym hal hex k k0 (t :: vT) lT (⟨t, ()⟩ :: vs) ls
      hk0 hwf.2 (by simp [hvs]) hls hco
  | _, .store (t := t) v a k, tf0, vT, lT, vs, ls, htf, hwf, hvs, hls, hco => by
    dsimp only [tflatToTFlat0] at htf
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨t0, _, htf⟩ := except_bind_eq_ok _ _ _ htf
    obtain ⟨v0, _, htf⟩ := except_bind_eq_ok _ _ _ htf
    obtain ⟨a0, _, htf⟩ := except_bind_eq_ok _ _ _ htf
    obtain ⟨k0, hk0, htf⟩ := except_bind_eq_ok _ _ _ htf
    simp only [Except.ok.injEq] at htf; subst htf
    dsimp only [denote] at hco
    rw [denoteArg_unit_isSome hvs hwf.1.1, denoteArg_unit_isSome hvs hwf.1.2] at hco
    dsimp only [Expr.callsOk] at hco
    dsimp only [TFlat0.checkCallsOk0]
    exact tflatToTFlat0_checkCallsOk0 hsym hal hex k k0 vT lT vs ls hk0 hwf.2 hvs hls hco
  | _, .call f (as := as) bs args k, tf0, vT, lT, vs, ls, htf, hwf, hvs, hls, hco => by
    dsimp only [tflatToTFlat0] at htf
    dsimp only [TFlat.wfCheck] at hwf; rw [Bool.and_eq_true] at hwf
    cases hfid : lookupSymId? tbl f with
    | none => rw [hfid] at htf; cases htf
    | some fid =>
      rw [hfid] at htf; dsimp only at htf
      obtain ⟨as0, has0, htf⟩ := except_bind_eq_ok _ _ _ htf
      obtain ⟨bs0, hbs0, htf⟩ := except_bind_eq_ok _ _ _ htf
      obtain ⟨args0, _, htf⟩ := except_bind_eq_ok _ _ _ htf
      obtain ⟨k0, hk0, htf⟩ := except_bind_eq_ok _ _ _ htf
      simp only [Except.ok.injEq] at htf; subst htf
      obtain ⟨args', hda⟩ := denoteArgs_unit_isSome hvs hwf.1
      dsimp only [denote] at hco; rw [hda] at hco; dsimp only [Expr.callsOk] at hco
      have has_eq := ty0ListToTy_tyListToTy0_loc has0
      have hbs_eq := ty0ListToTy_tyListToTy0_loc hbs0
      have hmem0 := hal f _ _ _ hfid (has_eq ▸ hbs_eq ▸ hco.1)
      have hk := tflatToTFlat0_checkCallsOk0 (rs0 := rs0) hsym hal hex k k0 (pushTypes bs vT) lT
        (pushTup (Tup.units bs) vs) ls hk0 hwf.2 (by rw [pushTup_map_fst, hvs]) hls hco.2
      dsimp only [TFlat0.checkCallsOk0]; rw [Bool.and_eq_true, List.any_eq_true]
      exact ⟨⟨(_, _, _), hmem0, sigEq0_iff_eq.mpr rfl⟩, hk⟩
  | _, .jnz c t e, tf0, vT, lT, vs, ls, htf, hwf, hvs, hls, hco => by
    dsimp only [tflatToTFlat0] at htf
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨c0, _, htf⟩ := except_bind_eq_ok _ _ _ htf
    obtain ⟨t0, ht0, htf⟩ := except_bind_eq_ok _ _ _ htf
    obtain ⟨e0, he0, htf⟩ := except_bind_eq_ok _ _ _ htf
    simp only [Except.ok.injEq] at htf; subst htf
    dsimp only [denote] at hco; rw [denoteArg_unit_isSome hvs hwf.1.1] at hco
    dsimp only [Expr.callsOk] at hco
    dsimp only [TFlat0.checkCallsOk0]; rw [Bool.and_eq_true]
    exact ⟨tflatToTFlat0_checkCallsOk0 hsym hal hex t t0 vT lT vs ls ht0 hwf.1.2 hvs hls hco.1,
           tflatToTFlat0_checkCallsOk0 hsym hal hex e e0 vT lT vs ls he0 hwf.2 hvs hls hco.2⟩
  | _, .jump (ts := ts) j args, tf0, vT, lT, vs, ls, htf, hwf, hvs, hls, _ => by
    dsimp only [tflatToTFlat0] at htf
    obtain ⟨args0, _, htf⟩ := except_bind_eq_ok _ _ _ htf
    simp only [Except.ok.injEq] at htf; subst htf; rfl
  | _, .ret _, tf0, vT, _, _, _, htf, _, _, _, _ => by
    dsimp only [tflatToTFlat0] at htf
    obtain ⟨vs0, _, htf⟩ := except_bind_eq_ok _ _ _ htf
    simp only [Except.ok.injEq] at htf; subst htf; rfl
  | _, .exit f (as := as) args, tf0, vT, _, vs, ls, htf, hwf, hvs, _, hco => by
    dsimp only [tflatToTFlat0] at htf
    dsimp only [TFlat.wfCheck] at hwf
    cases hfid : lookupSymId? tbl f with
    | none => rw [hfid] at htf; cases htf
    | some fid =>
      rw [hfid] at htf; dsimp only at htf
      obtain ⟨as0, _, htf⟩ := except_bind_eq_ok _ _ _ htf
      obtain ⟨args0, _, htf⟩ := except_bind_eq_ok _ _ _ htf
      simp only [Except.ok.injEq] at htf; subst htf
      obtain ⟨args', hda⟩ := denoteArgs_unit_isSome hvs hwf
      dsimp only [denote] at hco; rw [hda] at hco; dsimp only [Expr.callsOk] at hco
      dsimp only [TFlat0.checkCallsOk0]; rw [List.any_eq_true]
      exact ⟨_, hex f _ hfid hco, beq_iff_eq.mpr rfl⟩
  | _, .hlt, tf0, _, _, _, _, htf, _, _, _, _ => by
    dsimp only [tflatToTFlat0] at htf; simp only [Except.ok.injEq] at htf; subst htf; rfl
  | _, .group (sig := sig) bodies k, tf0, vT, lT, vs, ls, htf, hwf, hvs, hls, hco => by
    dsimp only [tflatToTFlat0] at htf
    dsimp only [TFlat.wfCheck] at hwf; rw [Bool.and_eq_true] at hwf
    obtain ⟨bs0, hbs0, htf⟩ := except_bind_eq_ok _ _ _ htf
    obtain ⟨k0, hk0, htf⟩ := except_bind_eq_ok _ _ _ htf
    simp only [Except.ok.injEq] at htf; subst htf
    dsimp only [denote, Expr.callsOk] at hco
    dsimp only [TFlat0.checkCallsOk0]; rw [Bool.and_eq_true]
    exact ⟨tblocksToList0_checkCallsOk0 hsym hal hex bodies bs0 vT (pushTypes sig lT)
        vs (pushTup (Tup.units sig) ls) hbs0 hwf.1 hvs (by rw [pushTup_map_fst, hls]) hco.1,
      tflatToTFlat0_checkCallsOk0 hsym hal hex k k0 vT (pushTypes sig lT)
        vs (pushTup (Tup.units sig) ls) hk0 hwf.2 hvs (by rw [pushTup_map_fst, hls]) hco.2⟩

private theorem tblocksToList0_checkCallsOk0 {tbl : List (Sym × Sym0)}
    (hsym : ∀ s fid, lookupSymId? tbl s = some fid → symNameOf tbl fid = s)
    {allowed0 : List (Sym0 × List Ty0 × List Ty0)} {allowed : List SigEntry}
    {exits0 : List Sym0} {exits : List Sym} {rs0 : List Ty0}
    (hal : ∀ s (fid : Sym0) as0 bs0, lookupSymId? tbl s = some fid →
      (s, ty0ListToTy as0, ty0ListToTy bs0) ∈ allowed → (fid, as0, bs0) ∈ allowed0)
    (hex : ∀ s (fid : Sym0), lookupSymId? tbl s = some fid → s ∈ exits → fid ∈ exits0) :
    ∀ {rs : List Ty} {sig : List (List Ty)}
      (bodies : TBlocks rs sig) (bs0 : List (List Ty0 × TFlat0))
      (vT : List Ty) (lT : List (List Ty))
      (vs : List ((_ : Ty) × Unit)) (ls : List ((_ : List Ty) × Unit)),
      tblocksToList0 tbl bodies = .ok bs0 →
      bodies.wfCheck vT lT = true →
      vs.map Sigma.fst = vT →
      ls.map Sigma.fst = lT →
      (denoteB (fun _ => Unit) (fun _ => Unit) bodies vs ls).callsOk allowed exits →
      blocksCheckCallsOk0 allowed0 rs0 exits0 bs0 = true
  | _, _, .nil, bs0, _, _, _, _, hbs, _, _, _, _ => by cases hbs; rfl
  | _, _, .cons (ts := ts) b bs, bs0, vT, lT, vs, ls, hbs, hwf, hvs, hls, hco => by
    dsimp only [tblocksToList0] at hbs
    dsimp only [TBlocks.wfCheck] at hwf; rw [Bool.and_eq_true] at hwf
    obtain ⟨ts0, _, hbs⟩ := except_bind_eq_ok _ _ _ hbs
    obtain ⟨b0, hb, hbs⟩ := except_bind_eq_ok _ _ _ hbs
    obtain ⟨rest0, hr, hbs⟩ := except_bind_eq_ok _ _ _ hbs
    simp only [Except.ok.injEq] at hbs; subst hbs
    dsimp only [denoteB, Blocks.callsOk] at hco
    dsimp only [blocksCheckCallsOk0]; rw [Bool.and_eq_true]
    exact ⟨tflatToTFlat0_checkCallsOk0 hsym hal hex b b0 (pushTypes ts vT) lT
        (pushTup (Tup.units ts) vs) ls hb hwf.1 (by rw [pushTup_map_fst, hvs]) hls hco.1,
      tblocksToList0_checkCallsOk0 hsym hal hex bs rest0 vT lT vs ls hr hwf.2 hvs hls hco.2⟩
end

private theorem forall2_symId_nodup {tbl : List (Sym × Sym0)}
    (hsym : ∀ s fid, lookupSymId? tbl s = some fid → symNameOf tbl fid = s) :
    ∀ {xs : List Sym} {ys : List Sym0},
      Forall2 (fun s s0 => lookupSymId? tbl s = some s0) xs ys → xs.Nodup → ys.Nodup
  | _, _, .nil, _ => List.nodup_nil
  | _, _, .cons hx hr, hnd => by
    simp only [List.nodup_cons] at hnd ⊢
    refine ⟨fun hm => ?_, forall2_symId_nodup hsym hr hnd.2⟩
    obtain ⟨s', hs', hsx⟩ := hr.exists_mem_right hm
    exact hnd.1 ((hsym _ _ hx).symm.trans (hsym _ _ hsx) ▸ hs')

private theorem forall2_map_sym {α β : Type} (tbl : List (Sym × Sym0))
    (hsym : ∀ s fid, lookupSymId? tbl s = some fid → symNameOf tbl fid = s)
    (fnA : α → Sym) (fnB : β → Sym0) {R : α → β → Prop}
    (hrel : ∀ a b, R a b → lookupSymId? tbl (fnA a) = some (fnB b)) :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys →
      ys.map (fun b => symNameOf tbl (fnB b)) = xs.map fnA
  | _, _, .nil => rfl
  | _, _, .cons h hr => by
    simp only [List.map_cons, hsym _ _ (hrel _ _ h),
      forall2_map_sym tbl hsym fnA fnB hrel hr]

/-- Bridge a `Module.checkAcyclic = true` + `TFlat.wfCheck = true` `Frontend.C0.TFlatFn` pipeline
into `mod.namesNodup` + `checkFnsCallsOk0 = true` cleanly. -/
theorem bridge_checkCallsOk0 (tfs : List Frontend.C0.TFlatFn)
    (externs : List Extern) (exits : List Sym) {mod : TFlatModule0} {tbl : List (Sym × Sym0)}
    (hof : ofTFlatModule tfs externs exits = .ok (mod, tbl))
    (hlt : tbl.length < 2 ^ 32)
    (hwf_chk : ∀ tf ∈ tfs, tf.flat.wfCheck (pushTypes tf.as []) [] = true)
    (hacyc : (Module.mk (tfs.map Frontend.C0.TFlatFn.toFn) externs exits).checkAcyclic = true) :
    (mod.fns.map TFlatFn0.name ++ mod.externs.map ExtSig0.name).Nodup ∧
    TFlatModule0.checkFnsCallsOk0 mod.exits (mod.externs.map ExtSig0.sig0) [] mod.fns =
      true := by
  let M : Module := { fns := tfs.map Frontend.C0.TFlatFn.toFn, externs := externs, exits := exits }
  obtain ⟨hsym, hf2, he2, hx2⟩ := ofTFlatModule_symTable_props tfs externs exits hof hlt
  simp only [Module.checkAcyclic, Bool.and_eq_true] at hacyc
  have hMnd : M.namesNodup := M.namesNodup_of_checkNamesNodup hacyc.1
  have hmod_nd : (mod.fns.map TFlatFn0.name ++ mod.externs.map ExtSig0.name).Nodup := by
    have h1 : Forall2 (fun s s0 => lookupSymId? tbl s = some s0)
        (tfs.map (·.name) ++ externs.map (·.name))
        (mod.fns.map TFlatFn0.name ++ mod.externs.map ExtSig0.name) :=
      Forall2.append
        (Forall2.map (fun x => x.name) (fun x => x.name) (hf2.imp fun _ _ h => h.1))
        (Forall2.map (fun x => x.name) (fun x => x.name) (he2.imp fun _ _ h => h.1))
    have hnd_src : (tfs.map (·.name) ++ externs.map (·.name)).Nodup := by
      simpa [M, Module.namesNodup, Module.names, List.map_map, Function.comp_def,
        Frontend.C0.TFlatFn.toFn] using hMnd
    exact forall2_symId_nodup hsym h1 hnd_src
  have hex_mem : ∀ s (fid : Sym0), lookupSymId? tbl s = some fid → s ∈ exits → fid ∈ mod.exits := by
    intro s fid hlk hs
    obtain ⟨g0, hg0_mem, hg0⟩ := hx2.exists_mem_left hs
    have heq : fid = g0 := Option.some.inj (hlk.symm.trans hg0)
    exact heq ▸ hg0_mem
  have hal_fns_exts : ∀ (preTf : List Frontend.C0.TFlatFn) (pre0 : List TFlatFn0),
      Forall2 (fun tf fn0 =>
        lookupSymId? tbl tf.name = some fn0.name ∧ ty0ListToTy fn0.as = tf.as ∧
        ty0ListToTy fn0.rs = tf.rs ∧ tflatToTFlat0 tbl tf.flat = .ok fn0.body) preTf pre0 →
      ∀ s (fid : Sym0) as0 bs0, lookupSymId? tbl s = some fid →
        (s, ty0ListToTy as0, ty0ListToTy bs0) ∈
          (preTf.map Frontend.C0.TFlatFn.toFn).map Fn.sig ++ externs.map Extern.sig →
        (fid, as0, bs0) ∈ pre0.map TFlatFn0.sig0 ++ mod.externs.map ExtSig0.sig0 := by
    intro preTf pre0 hpre s fid as0 bs0 hlk hmem
    rcases List.mem_append.mp hmem with hfn | hex
    · rw [List.mem_map] at hfn
      obtain ⟨f, hf, hsig⟩ := hfn
      rw [List.mem_map] at hf
      obtain ⟨tf, htf_mem, rfl⟩ := hf
      obtain ⟨fn0, hfn0_mem, hfn0⟩ := hpre.exists_mem_left htf_mem
      simp only [Frontend.C0.TFlatFn.toFn, Fn.sig, Prod.mk.injEq] at hsig
      rcases hsig with ⟨hs_eq, has_eq, hbs_eq⟩
      subst hs_eq
      have hfid_eq : fid = fn0.name := Option.some.inj (hlk.symm.trans hfn0.1)
      have has0_eq : as0 = fn0.as := (ty0ListToTy_inj_loc (hfn0.2.1.trans has_eq)).symm
      have hbs0_eq : bs0 = fn0.rs := (ty0ListToTy_inj_loc (hfn0.2.2.1.trans hbs_eq)).symm
      subst hfid_eq; subst has0_eq; subst hbs0_eq
      exact List.mem_append_left _ (List.mem_map.mpr ⟨fn0, hfn0_mem, rfl⟩)
    · rw [List.mem_map] at hex
      obtain ⟨ex, hex_mem', hsig⟩ := hex
      obtain ⟨ex0, hex0_mem, hex0⟩ := he2.exists_mem_left hex_mem'
      simp only [Extern.sig, Prod.mk.injEq] at hsig
      rcases hsig with ⟨hs_eq, has_eq, hbs_eq⟩
      subst hs_eq
      have hfid_eq : fid = ex0.name := Option.some.inj (hlk.symm.trans hex0.1)
      have has0_eq : as0 = ex0.as := (ty0ListToTy_inj_loc (hex0.2.1.trans has_eq)).symm
      have hbs0_eq : bs0 = ex0.rs := (ty0ListToTy_inj_loc (hex0.2.2.trans hbs_eq)).symm
      subst hfid_eq; subst has0_eq; subst hbs0_eq
      exact List.mem_append_right _ (List.mem_map.mpr ⟨ex0, hex0_mem, rfl⟩)
  have hwalk : ∀ (seenTf restTf : List Frontend.C0.TFlatFn) (seen0 rest0 : List TFlatFn0),
      Forall2 (fun tf fn0 =>
        lookupSymId? tbl tf.name = some fn0.name ∧ ty0ListToTy fn0.as = tf.as ∧
        ty0ListToTy fn0.rs = tf.rs ∧ tflatToTFlat0 tbl tf.flat = .ok fn0.body) seenTf seen0 →
      Forall2 (fun tf fn0 =>
        lookupSymId? tbl tf.name = some fn0.name ∧ ty0ListToTy fn0.as = tf.as ∧
        ty0ListToTy fn0.rs = tf.rs ∧ tflatToTFlat0 tbl tf.flat = .ok fn0.body) restTf rest0 →
      (∀ tf ∈ restTf, tf.flat.wfCheck (pushTypes tf.as []) [] = true) →
      Module.checkFnsCallsOk exits (externs.map Extern.sig)
        ((seenTf.map Frontend.C0.TFlatFn.toFn).map Fn.sig)
        (restTf.map Frontend.C0.TFlatFn.toFn) = true →
      TFlatModule0.checkFnsCallsOk0 mod.exits (mod.externs.map ExtSig0.sig0)
        (seen0.map TFlatFn0.sig0) rest0 = true := by
    intro seenTf restTf
    induction restTf generalizing seenTf with
    | nil =>
      intro seen0 rest0 _ hr _ _
      cases hr
      rfl
    | cons tf rtf ih =>
      intro seen0 rest0 hseen hr hwf_r hchk
      cases hr with
      | cons hcur hrest =>
        rename_i fn0 r0
        simp only [List.map_cons, Module.checkFnsCallsOk, Bool.and_eq_true] at hchk
        have hco : (denote (fun _ => Unit) (fun _ => Unit) tf.flat
            (pushTup (Tup.units tf.as) []) []).callsOk
            ((seenTf.map Frontend.C0.TFlatFn.toFn).map Fn.sig ++ externs.map Extern.sig) exits :=
          Fn.callsOk_of_checkCallsOk hchk.1
        have hwf_tf : tf.flat.wfCheck (pushTypes tf.as []) [] = true :=
          hwf_r tf List.mem_cons_self
        have hcalls_cur : fn0.body.checkCallsOk0
            (seen0.map TFlatFn0.sig0 ++ mod.externs.map ExtSig0.sig0) fn0.rs mod.exits = true :=
          tflatToTFlat0_checkCallsOk0 hsym (hal_fns_exts seenTf seen0 hseen) hex_mem
            tf.flat fn0.body (pushTypes tf.as []) [] (pushTup (Tup.units tf.as) []) []
            hcur.2.2.2 hwf_tf (by rw [pushTup_map_fst]; rfl) rfl hco
        have ih_res := ih (seenTf ++ [tf]) (seen0 ++ [fn0]) r0
          (Forall2.append hseen (.cons hcur .nil)) hrest
          (fun q hq => hwf_r q (List.mem_cons_of_mem _ hq))
          (by simpa [List.map_append, Frontend.C0.TFlatFn.toFn, Fn.sig] using hchk.2)
        dsimp only [TFlatModule0.checkFnsCallsOk0]; rw [Bool.and_eq_true]
        exact ⟨hcalls_cur,
          by simpa only [List.map_append, List.map_cons, List.map_nil] using ih_res⟩
  exact ⟨hmod_nd, hwalk [] tfs [] mod.fns .nil hf2 hwf_chk (by simpa [M] using hacyc.2)⟩

private theorem fnSpec_congr_env {h : Host} (Γ : Env) {s₁ s₂ : Sym} {as₁ as₂ bs₁ bs₂ : List Ty}
    {n nX : Nat} (hs : s₁ = s₂) (ha : as₁ = as₂) (hb : bs₁ = bs₂)
    (hf : x64ScalarTarget.FnSpec h s₁ (Γ s₁ as₁ bs₁) n nX) :
    x64ScalarTarget.FnSpec h s₂ (Γ s₂ as₂ bs₂) n nX := by
  subst hs; subst ha; subst hb; exact hf

private theorem bridge_fn_wp0 {Γ : Env} {M : Module} {tbl : List (Sym × Sym0)}
    (hsym : ∀ s fid, lookupSymId? tbl s = some fid → symNameOf tbl fid = s)
    (hM : ModuleOk Γ M)
    {tf : Frontend.C0.TFlatFn} (htf_mem : tf.toFn ∈ M.fns) {fn0 : TFlatFn0}
    (hlk : lookupSymId? tbl tf.name = some fn0.name)
    (has : ty0ListToTy fn0.as = tf.as) (hrs : ty0ListToTy fn0.rs = tf.rs)
    (hbd : tflatToTFlat0 tbl tf.flat = .ok fn0.body)
    (hu32 : tflatIdxLtU32 tf.flat = true) :
    ∀ (args : Tup Val (ty0ListToTy fn0.as)) m Q X,
      Env.ofModule M Γ (symNameOf tbl fn0.name) (ty0ListToTy fn0.as) (ty0ListToTy fn0.rs)
        args m Q X →
      wp0 (Env.ofModule M Γ) (symNameOf tbl) fn0.rs (pushTup args []) [] Q X fn0.body m := by
  have hM' := ModuleOk.ofModule hM
  obtain ⟨pre, post, hsp⟩ := List.append_of_mem htf_mem
  have hwp_tf := (hM'.fnsOk pre tf.toFn post hsp).2.2
  dsimp only [Frontend.C0.TFlatFn.toFn, Func.wp, denoteFunc] at hwp_tf
  have hname : symNameOf tbl fn0.name = tf.name := hsym _ _ hlk
  rw [hname]
  intro args m Q X hΓ
  have hpush_id : ∀ {as₁ as₂ : List Ty} (ha : as₁ = as₂) (a : Tup Val as₁),
      pushTup (ha ▸ a) [] = pushTup a [] := by
    intro _ _ ha _; subst ha; rfl
  have hq_id : ∀ {rs₁ rs₂ : List Ty} (hb : rs₁ = rs₂) (q : Post rs₁),
      (hb ▸ (hb ▸ q : Post rs₂) : Post rs₁) = q := by
    intro _ _ hb _; subst hb; rfl
  have hcast_env : ∀ {as₁ as₂ rs₁ rs₂ : List Ty} (ha : as₁ = as₂) (hb : rs₁ = rs₂)
      (a : Tup Val as₁) (q : Post rs₁),
      Env.ofModule M Γ tf.name as₁ rs₁ a m q X →
      Env.ofModule M Γ tf.name as₂ rs₂ (ha ▸ a) m (hb ▸ q : Post rs₂) X := by
    intro _ _ _ _ ha hb a q h
    subst ha; subst hb; exact h
  have hw := hwp_tf (has ▸ args : Tup Val tf.as) m (hrs ▸ Q : Post tf.rs) X
    (hcast_env has hrs args Q hΓ)
  have hw0 := bridge_tflatToTFlat0_wp hsym hrs tf.flat fn0.body hbd hu32
    (pushTup (has ▸ args : Tup Val tf.as) []) [] (hrs ▸ Q : Post tf.rs) X m hw
  rwa [hpush_id has args, hq_id hrs Q] at hw0

/-- End-to-end semantic soundness for `Bridge0.ofTFlatModule` + `leanqbe0Compile` on any host `h`
containing `toAmd64Program (symNameOf tbl) dirs` with unique labels. -/
theorem bridge_leanqbe0Compile_fnSpec {h : Host} {Γ : Env}
    (tfs : List Frontend.C0.TFlatFn) (externs : List Extern) (exits : List Sym)
    {mod : TFlatModule0} {tbl : List (Sym × Sym0)} {dirs : List Dir0} {maxSl : UInt32}
    {nX k₀ : Nat} {bound : Sym → Nat}
    (hof : ofTFlatModule tfs externs exits = .ok (mod, tbl))
    (hc : leanqbe0Compile mod = .ok dirs maxSl)
    (hg : mod.okGuardsFull = true)
    (hlt : tbl.length < 2 ^ 32)
    (hu32 : ∀ tf ∈ tfs, tflatIdxLtU32 tf.flat = true)
    (_hacyc : (Module.mk (tfs.map Frontend.C0.TFlatFn.toFn) externs exits).checkAcyclic = true)
    (hM : ModuleOk Γ
      { fns := tfs.map Frontend.C0.TFlatFn.toFn, externs := externs, exits := exits })
    (hinf : (toAmd64Program (symNameOf tbl) dirs).IsInfixAt (x64ScalarMach.prog h) k₀)
    (hu : x64ScalarTarget.LabelsUnique h)
    (hmod_bd : ModBoundsOk0 mod nX (fun id => bound (symNameOf tbl id)))
    (hext : ∀ ex ∈ externs,
      x64ScalarTarget.Defined h ex.name ∧
      x64ScalarTarget.FnSpec h ex.name
        (Env.ofModule
          { fns := tfs.map Frontend.C0.TFlatFn.toFn, externs := externs, exits := exits }
          Γ ex.name ex.as ex.rs)
        (bound ex.name) nX)
    (hexits : ∀ g ∈ exits, x64ScalarTarget.Defined h g) :
    ∀ tf ∈ tfs,
      x64ScalarTarget.Defined h tf.name ∧
      x64ScalarTarget.FnSpec h tf.name
        (Env.ofModule
          { fns := tfs.map Frontend.C0.TFlatFn.toFn, externs := externs, exits := exits }
          Γ tf.name tf.as tf.rs)
        (bound tf.name) nX := by
  let M : Module := { fns := tfs.map Frontend.C0.TFlatFn.toFn, externs := externs, exits := exits }
  let Γ' := Env.ofModule M Γ
  obtain ⟨hsym, hf2, he2, hx2⟩ := ofTFlatModule_symTable_props tfs externs exits hof hlt
  have hext0 : ∀ ex0 ∈ mod.externs,
      x64ScalarTarget.Defined h (symNameOf tbl ex0.name) ∧
      x64ScalarTarget.FnSpec h (symNameOf tbl ex0.name)
        (Γ' (symNameOf tbl ex0.name) (ty0ListToTy ex0.as) (ty0ListToTy ex0.rs))
        (bound (symNameOf tbl ex0.name)) nX := by
    intro ex0 hex0_mem
    obtain ⟨ex, hex_mem, hlk, has, hrs⟩ := he2.exists_mem_right hex0_mem
    have hnm : symNameOf tbl ex0.name = ex.name := hsym _ _ hlk
    obtain ⟨hd, hs⟩ := hext ex hex_mem
    have hs' := fnSpec_congr_env Γ' rfl has.symm hrs.symm hs
    rw [hnm]; exact ⟨hd, hs'⟩
  have hexits0 : ∀ g0 ∈ mod.exits, x64ScalarTarget.Defined h (symNameOf tbl g0) := by
    intro g0 hg0_mem
    obtain ⟨g, hg_mem, hlk⟩ := hx2.exists_mem_right hg0_mem
    rw [hsym _ _ hlk]; exact hexits g hg_mem
  have hwp0 : ∀ fn0 ∈ mod.fns, ∀ (args : Tup Val (ty0ListToTy fn0.as)) m Q X,
      Γ' (symNameOf tbl fn0.name) (ty0ListToTy fn0.as) (ty0ListToTy fn0.rs) args m Q X →
      wp0 Γ' (symNameOf tbl) fn0.rs (pushTup args []) [] Q X fn0.body m := by
    intro fn0 hfn0_mem args m Q X hΓ'
    obtain ⟨tf, htf_mem, hlk, has, hrs, hbd⟩ := hf2.exists_mem_right hfn0_mem
    exact bridge_fn_wp0 hsym hM (List.mem_map_of_mem htf_mem) hlk has hrs hbd
      (hu32 tf htf_mem) args m Q X hΓ'
  have hres := leanqbe0Compile_fnSpec hc hg hinf hu hmod_bd hext0 hexits0 hwp0
  intro tf htf_mem
  obtain ⟨fn0, hfn0_mem, hlk, has, hrs, _⟩ := hf2.exists_mem_left htf_mem
  have hnm : symNameOf tbl fn0.name = tf.name := hsym _ _ hlk
  obtain ⟨hd, hs⟩ := hres fn0 hfn0_mem
  rw [← hnm]; exact ⟨hd, fnSpec_congr_env Γ' rfl has hrs hs⟩

/-- Standalone concrete-host `Bridge0.ofTFlatModule` + `leanqbe0Compile` + `PrintAsm0` soundness
theorem building `h := x64ScalarLayout.layoutOf` and computing stack bounds via `computeBounds0`. -/
theorem bridge_leanqbe0Compile_layout {Γ : Env}
    (tfs : List Frontend.C0.TFlatFn) (externs : List Extern) (exits : List Sym)
    {mod : TFlatModule0} {tbl : List (Sym × Sym0)} {dirs : List Dir0} {maxSl : UInt32}
    {extBounds modBounds : List (Sym0 × Nat)} {nX : Nat}
    (hof : ofTFlatModule tfs externs exits = .ok (mod, tbl))
    (hc : leanqbe0Compile mod = .ok dirs maxSl)
    (hg : mod.okGuardsFull = true)
    (hlt : tbl.length < 2 ^ 32)
    (hwf_chk : ∀ tf ∈ tfs, tf.flat.wfCheck (pushTypes tf.as []) [] = true)
    (hu32 : ∀ tf ∈ tfs, tflatIdxLtU32 tf.flat = true)
    (hacyc : (Module.mk (tfs.map Frontend.C0.TFlatFn.toFn) externs exits).checkAcyclic = true)
    (hex_nd : exits.Nodup)
    (hex_disj : ∀ g ∈ exits, ∀ fn ∈ tfs, fn.name ≠ g)
    (hfn_noloc : ∀ tf ∈ tfs, symNoLocPrefix0 tf.name = true)
    (hex_noloc : ∀ g ∈ exits, symNoLocPrefix0 g = true)
    (hb : mod.computeBounds0 extBounds nX = some modBounds)
    (hext_disj : ∀ exName ∈ extBounds.map Prod.fst, exName ∉ mod.fns.map TFlatFn0.name)
    (hsmall : x64ScalarProgSmall
      (toAmd64Program (symNameOf tbl) dirs ++ exits.map x64Frame.label) = true)
    (hM : ModuleOk Γ
      { fns := tfs.map Frontend.C0.TFlatFn.toFn, externs := externs, exits := exits })
    (hext : ∀ ex ∈ externs, ∀ ex0 ∈ mod.externs, symNameOf tbl ex0.name = ex.name →
      let h := x64ScalarLayout.layoutOf
        (toAmd64Program (symNameOf tbl) dirs ++ exits.map x64Frame.label) hsmall
      x64ScalarTarget.Defined h ex.name ∧
      x64ScalarTarget.FnSpec h ex.name
        (Env.ofModule
          { fns := tfs.map Frontend.C0.TFlatFn.toFn, externs := externs, exits := exits }
          Γ ex.name ex.as ex.rs)
        ((lookupBound0 modBounds ex0.name).getD 0) nX) :
    let h := x64ScalarLayout.layoutOf
      (toAmd64Program (symNameOf tbl) dirs ++ exits.map x64Frame.label) hsmall
    x64ScalarTarget.LabelsUnique h ∧
    printAsm0 (toAmd64Program (symNameOf tbl) dirs) =
      Kraken.X64.toATT (toAmd64Program (symNameOf tbl) dirs) ∧
    ∀ tf ∈ tfs,
      x64ScalarTarget.Defined h tf.name ∧
      x64ScalarTarget.FnSpec h tf.name
        (Env.ofModule
          { fns := tfs.map Frontend.C0.TFlatFn.toFn, externs := externs, exits := exits }
          Γ tf.name tf.as tf.rs)
        ((lookupBound0 modBounds (lookupSymId? tbl tf.name).get!).getD 0) nX := by
  let M : Module := { fns := tfs.map Frontend.C0.TFlatFn.toFn, externs := externs, exits := exits }
  let Γ' := Env.ofModule M Γ
  obtain ⟨hl, hd_eq, _⟩ := legalMod0_eq_zero_of_leanqbe0Compile hc
  obtain ⟨hsym, hf2, he2, hx2⟩ := ofTFlatModule_symTable_props tfs externs exits hof hlt
  obtain ⟨hmod_nd, hmod_calls⟩ := bridge_checkCallsOk0 tfs externs exits hof hlt hwf_chk hacyc
  have hmod_bd := modBoundsOk0_of_parts hmod_nd hmod_calls hb hext_disj
  have hfn_names_nd : (tfs.map Frontend.C0.TFlatFn.name).Nodup := by
    have h1 := M.namesNodup_of_checkNamesNodup
      (by simp only [Module.checkAcyclic, Bool.and_eq_true] at hacyc; exact hacyc.1)
    simp only [M, Module.namesNodup, Module.names, List.map_map, Function.comp_def,
      Frontend.C0.TFlatFn.toFn] at h1
    exact (List.nodup_append.mp h1).1
  have hmap_names := forall2_map_sym tbl hsym Frontend.C0.TFlatFn.name TFlatFn0.name
    (fun _ _ h => h.1) hf2
  have hex_names : mod.exits.map (symNameOf tbl) = exits := by
    have h := forall2_map_sym tbl hsym id id (fun _ _ h => h) hx2
    simp only [id_eq, List.map_id] at h
    exact h
  have hnd_all : (mod.fns.map (fun fn => symNameOf tbl fn.name) ++
      mod.exits.map (symNameOf tbl)).Nodup := by
    rw [hmap_names, hex_names, List.nodup_append]
    refine ⟨hfn_names_nd, hex_nd, fun x hx y hy he => ?_⟩
    rw [List.mem_map] at hx
    obtain ⟨fn, hfn_mem, rfl⟩ := hx
    exact hex_disj y hy fn hfn_mem he
  have hnoloc_fns : ∀ fn0 ∈ mod.fns, symNoLocPrefix0 (symNameOf tbl fn0.name) = true := by
    intro fn0 hfn0_mem
    obtain ⟨tf, htf_mem, hlk, _⟩ := hf2.exists_mem_right hfn0_mem
    rw [hsym _ _ hlk]; exact hfn_noloc tf htf_mem
  have hnoloc_ex : ∀ g0 ∈ mod.exits, symNoLocPrefix0 (symNameOf tbl g0) = true := by
    intro g0 hg0_mem
    obtain ⟨g, hg_mem, hlk⟩ := hx2.exists_mem_right hg0_mem
    rw [hsym _ _ hlk]; exact hex_noloc g hg_mem
  let prog := toAmd64Program (symNameOf tbl) dirs ++ exits.map x64Frame.label
  let h := x64ScalarLayout.layoutOf prog hsmall
  have hl_prog := x64ScalarLayout.prog_layoutOf prog hsmall
  change x64ScalarMach.prog h = prog at hl_prog
  have hprog : x64ScalarMach.prog h =
      toAmd64Program (symNameOf tbl) (compileModuleLoop0 mod.fns 0 0 []).1 ++
        (mod.exits.map (symNameOf tbl)).map x64Frame.label := by
    rw [hl_prog]; dsimp only [prog]; rw [hd_eq, hex_names]; try rfl
  have hfns_g : ∀ fn ∈ mod.fns, fn.okGuardsFull = true := by
    simp only [TFlatModule0.okGuardsFull, Bool.and_eq_true, List.all_eq_true] at hg
    exact hg.1.2
  have hfns_bd : (0 : UInt32).toNat + mod.fns.length < 2 ^ 32 := by
    have := TFlatModule0.okGuardsFull_fns_length hg
    rw [UInt32.toNat_zero, Nat.zero_add]; omega
  obtain ⟨hu, hexits⟩ := compileModuleLoop0_host_labelsUnique (symName := symNameOf tbl)
    (fns := mod.fns) (idx0 := 0) (maxSl := 0) (exitSyms := mod.exits.map (symNameOf tbl))
    hprog hfns_bd hfns_g hnd_all hnoloc_fns (fun _ hm => by
      rw [List.mem_map] at hm; obtain ⟨g, hg_mem, rfl⟩ := hm; exact hnoloc_ex g hg_mem)
  have hinf : (toAmd64Program (symNameOf tbl) dirs).IsInfixAt (x64ScalarMach.prog h) 0 := by
    rw [hl_prog]; exact ⟨exits.map x64Frame.label, rfl⟩
  have hext0 : ∀ ex0 ∈ mod.externs,
      x64ScalarTarget.Defined h (symNameOf tbl ex0.name) ∧
      x64ScalarTarget.FnSpec h (symNameOf tbl ex0.name)
        (Γ' (symNameOf tbl ex0.name) (ty0ListToTy ex0.as) (ty0ListToTy ex0.rs))
        ((lookupBound0 modBounds ex0.name).getD 0) nX := by
    intro ex0 hex0_mem
    obtain ⟨ex, hex_mem, hlk, has, hrs⟩ := he2.exists_mem_right hex0_mem
    have hnm : symNameOf tbl ex0.name = ex.name := hsym _ _ hlk
    obtain ⟨hd, hs⟩ := hext ex hex_mem ex0 hex0_mem hnm
    exact ⟨hnm ▸ hd, fnSpec_congr_env Γ' hnm.symm has.symm hrs.symm hs⟩
  have hexits0 : ∀ g0 ∈ mod.exits, x64ScalarTarget.Defined h (symNameOf tbl g0) := by
    intro g0 hg0_mem; exact hexits _ (List.mem_map_of_mem hg0_mem)
  have hwp0 : ∀ fn0 ∈ mod.fns, ∀ (args : Tup Val (ty0ListToTy fn0.as)) m Q X,
      Γ' (symNameOf tbl fn0.name) (ty0ListToTy fn0.as) (ty0ListToTy fn0.rs) args m Q X →
      wp0 Γ' (symNameOf tbl) fn0.rs (pushTup args []) [] Q X fn0.body m := by
    intro fn0 hfn0_mem args m Q X hΓ'
    obtain ⟨tf, htf_mem, hlk, has, hrs, hbd⟩ := hf2.exists_mem_right hfn0_mem
    exact bridge_fn_wp0 hsym hM (List.mem_map_of_mem htf_mem) hlk has hrs hbd
      (hu32 tf htf_mem) args m Q X hΓ'
  have hres := leanqbe0Compile_fnSpec hc hg hinf hu hmod_bd hext0 hexits0 hwp0
  refine ⟨hu, leanqbe0Compile_printAsm0 hc, fun tf htf_mem => ?_⟩
  obtain ⟨fn0, hfn0_mem, hlk, has, hrs, _⟩ := hf2.exists_mem_left htf_mem
  have hnm : symNameOf tbl fn0.name = tf.name := hsym _ _ hlk
  have hget_id : (lookupSymId? tbl tf.name).get! = fn0.name := by rw [hlk]; rfl
  rw [hget_id]
  obtain ⟨hd, hs⟩ := hres fn0 hfn0_mem
  rw [← hnm]; exact ⟨hd, fnSpec_congr_env Γ' rfl has hrs hs⟩

/-! ## 6. Closed Machine Execution Helper (`TargetInit.run_ret1_i64_of_fnSpec`) -/

/-- Run a non-exiting `x64ScalarTarget.FnSpec` returning `i64` directly via `TargetInit`, without
requiring a legacy `Compiled` bundle. -/
theorem TargetInit.run_ret1_i64_of_fnSpec {T : Target} {maxStack maxMem : Nat}
    (I : TargetInit T maxStack maxMem) (h : T.mach.Host) {nm : Sym} {as : List Ty}
    {spec : Spec as [i64]} {b nX : Nat} (hf : T.FnSpec h nm spec b nX)
    (bsMem : List UInt8) (args : Tup Val as) (v : Val i64)
    (hb : b ≤ maxStack) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs as).isSome = true)
    {Q : Post [i64]} (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ())) :
    Eventually (T.mach.step h)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v)
      (T.mach.mkState (I.initState b bsMem args) (T.mach.labelAddr h nm)) := by
  have hmem := I.mem_entry b bsMem args hb hbs
  rw [← I.get_sp b bsMem args] at hmem
  refine eventually_weaken _ _ _ _ ?_ (hf args (bsMem.At 0x1000#64) Q
    (fun _ _ _ _ => False) hspec (I.initState b bsMem args) I.ra0 Std.ExtHashMap.emp
    (I.argsIn b bsMem args hargs) (I.raReg b bsMem args)
    (by rw [I.get_sp]; exact I.spEntry) hmem)
  rintro st (⟨hpc, rets, m', hq, hrets, _⟩ | ⟨_, _, _, _, hx, _⟩)
  · have hr := hQ rets m' hq; subst hr
    exact ⟨hpc, I.retsIn_singleton v (T.mach.data st) hrets⟩
  · exact hx.elim

end LeanQbe.T.Bootstrap0
