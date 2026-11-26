module

public import LeanQbe.T.Logic.C0Step

/-!
# Canonical per-function specification environments (`CanonicalEnv`)

Light-weight combinators built directly on `LeanQbe.T.Env.ofTable` and `TableImpl` so multi-file
C0 proofs can use **one canonical `SpecEntry` per function** without patch layers, slot-agreement
glue, or re-exported lookup lemmas:

1. **Spec order & multi-mode combinators**: `Spec.Le`, `Spec.or`, `Spec.iUnion`, `Spec.XFree`,
   and the `xfree` tactic.
2. **Environment capabilities**: `Env.Has` (definitionally identical to existing per-function `Γ`
   callee hypotheses), `Env.Sat`, `Env.Sat.has`, `Env.Sat.ofTable` (`List.Mem` + one shared
   `Nodup` proof, zero string comparisons), and `Env.override`.
3. **Segment certificates & module assembly**: `SpecEntry.sig`, `SegCert`, `TableImpl.append`,
   `AllFns.of_forall`, and `ModuleOk.ofCanonical`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## 1. Spec order, multi-mode combinators, and exit-insensitivity -/

/-- `S.Le T`: every caller obligation for `S` discharges `T` (a `T`-callee satisfies `S`). -/
@[expose] def Spec.Le {as bs : List Ty} (S T : Spec as bs) : Prop :=
  ∀ xs m Q X, S xs m Q X → T xs m Q X

theorem Spec.Le.refl {as bs : List Ty} (S : Spec as bs) : S.Le S :=
  fun _ _ _ _ h => h

theorem Spec.Le.trans {as bs : List Ty} {S T U : Spec as bs}
    (h₁ : S.Le T) (h₂ : T.Le U) : S.Le U :=
  fun xs m Q X h => h₂ xs m Q X (h₁ xs m Q X h)

/-- Multi-mode contract (`{P₁}f{Q₁} ∧ {P₂}f{Q₂}`): the caller chooses the mode. -/
@[expose] def Spec.or {as bs : List Ty} (S T : Spec as bs) : Spec as bs :=
  fun xs m Q X => S xs m Q X ∨ T xs m Q X

/-- Indexed multi-mode contract: the caller supplies mode index `i : ι`. -/
@[expose] def Spec.iUnion {ι : Type} {as bs : List Ty} (S : ι → Spec as bs) : Spec as bs :=
  fun xs m Q X => ∃ i, S i xs m Q X

theorem Spec.le_or_left {as bs : List Ty} {S T : Spec as bs} : S.Le (S.or T) :=
  fun _ _ _ _ => Or.inl

theorem Spec.le_or_right {as bs : List Ty} {S T : Spec as bs} : T.Le (S.or T) :=
  fun _ _ _ _ => Or.inr

theorem Spec.or_le {as bs : List Ty} {S₁ S₂ T : Spec as bs}
    (h₁ : S₁.Le T) (h₂ : S₂.Le T) : (S₁.or S₂).Le T :=
  fun xs m Q X h => h.elim (h₁ xs m Q X) (h₂ xs m Q X)

theorem Spec.le_iUnion {ι : Type} {as bs : List Ty}
    (S : ι → Spec as bs) (i : ι) : (S i).Le (Spec.iUnion S) :=
  fun _ _ _ _ h => ⟨i, h⟩

theorem Spec.iUnion_le {ι : Type} {as bs : List Ty}
    {S : ι → Spec as bs} {T : Spec as bs}
    (h : ∀ i, (S i).Le T) : (Spec.iUnion S).Le T :=
  fun xs m Q X ⟨i, hi⟩ => h i xs m Q X hi

theorem Spec.impl_or {Γ : Env} {as rs : List Ty} {f : Func as rs} {S T : Spec as rs}
    (h₁ : ∀ xs m Q X, S xs m Q X → Func.wp Γ f xs m Q X)
    (h₂ : ∀ xs m Q X, T xs m Q X → Func.wp Γ f xs m Q X) :
    ∀ xs m Q X, S.or T xs m Q X → Func.wp Γ f xs m Q X :=
  fun xs m Q X h => h.elim (h₁ xs m Q X) (h₂ xs m Q X)

theorem Spec.impl_iUnion {ι : Type} {Γ : Env} {as rs : List Ty} {f : Func as rs}
    {S : ι → Spec as rs}
    (h : ∀ i xs m Q X, S i xs m Q X → Func.wp Γ f xs m Q X) :
    ∀ xs m Q X, (Spec.iUnion S) xs m Q X → Func.wp Γ f xs m Q X :=
  fun xs m Q X ⟨i, hi⟩ => h i xs m Q X hi

/-- Exit-insensitive contract (`fun … m Q _ => …`); eliminates per-callee `_noExit` lemmas. -/
@[expose] def Spec.XFree {as bs : List Ty} (S : Spec as bs) : Prop :=
  ∀ xs m Q X X', S xs m Q X → S xs m Q X'

/-- Close `Spec.XFree S` by definitional equality when `S` ignores its `XPost` argument. -/
macro "xfree" : tactic => `(tactic| exact fun _ _ _ _ _ h => h)

theorem Spec.XFree.or {as bs : List Ty} {S T : Spec as bs}
    (hS : S.XFree) (hT : T.XFree) : (S.or T).XFree :=
  fun xs m Q X X' h => h.elim (fun hs => .inl (hS xs m Q X X' hs))
    (fun ht => .inr (hT xs m Q X X' ht))

theorem Spec.XFree.iUnion {ι : Type} {as bs : List Ty} {S : ι → Spec as bs}
    (hS : ∀ i, (S i).XFree) : (Spec.iUnion S).XFree :=
  fun xs m Q X X' ⟨i, hi⟩ => ⟨i, hS i xs m Q X X' hi⟩

/-! ## 2. Environment capabilities (`Env.Has`, `Env.Sat`, `Env.override`) -/

/-- `Γ` honours `S` at `f`: *definitionally* the standard callee hypothesis shape. -/
abbrev Env.Has (Γ : Env) (f : Sym) {as bs : List Ty} (S : Spec as bs) : Prop :=
  ∀ xs m Q X, S xs m Q X → Γ f as bs xs m Q X

theorem Env.Has.of_le {Γ : Env} {f : Sym} {as bs : List Ty} {S T : Spec as bs}
    (h : Γ.Has f T) (hle : S.Le T) : Γ.Has f S :=
  fun xs m Q X hs => h xs m Q X (hle xs m Q X hs)

/-- `Γ` honours every effective row contract in `tbl`. -/
@[expose] def Env.Sat (Γ : Env) (tbl : List SpecEntry) : Prop :=
  ∀ e ∈ tbl, Γ.Has e.name e.eff

theorem Env.Sat.nil (Γ : Env) : Γ.Sat [] :=
  fun _ h => nomatch h

theorem Env.Sat.cons_iff {Γ : Env} {e : SpecEntry} {es : List SpecEntry} :
    Γ.Sat (e :: es) ↔ Γ.Has e.name e.eff ∧ Γ.Sat es := by
  simp only [Env.Sat, List.mem_cons]
  exact ⟨fun h => ⟨h e (.inl rfl), fun e' he' => h e' (.inr he')⟩,
    fun ⟨he, hes⟩ e' h => h.elim (fun eq => eq ▸ he) (hes e')⟩

theorem Env.Sat.append_iff {Γ : Env} {a b : List SpecEntry} :
    Γ.Sat (a ++ b) ↔ Γ.Sat a ∧ Γ.Sat b := by
  simp only [Env.Sat, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (.inl he), fun e he => h e (.inr he)⟩,
    fun ⟨ha, hb⟩ e he => he.elim (ha e) (hb e)⟩

theorem Env.Sat.append {Γ : Env} {a b : List SpecEntry}
    (ha : Γ.Sat a) (hb : Γ.Sat b) : Γ.Sat (a ++ b) :=
  Env.Sat.append_iff.mpr ⟨ha, hb⟩

theorem Env.Sat.left {Γ : Env} {a b : List SpecEntry} (h : Γ.Sat (a ++ b)) : Γ.Sat a :=
  fun e he => h e (List.mem_append_left b he)

theorem Env.Sat.right {Γ : Env} {a b : List SpecEntry} (h : Γ.Sat (a ++ b)) : Γ.Sat b :=
  fun e he => h e (List.mem_append_right a he)

theorem Env.Sat.sub {Γ : Env} {s t : List SpecEntry}
    (h : Γ.Sat t) (hst : ∀ e ∈ s, e ∈ t) : Γ.Sat s :=
  fun e he => h e (hst e he)

theorem Env.Sat.has_eff {Γ : Env} {tbl : List SpecEntry}
    (h : Γ.Sat tbl) {e : SpecEntry} (he : e ∈ tbl) : Γ.Has e.name e.eff :=
  h e he

/-- Project a single `XFree` capability from `Γ.Sat tbl` using an explicit `List.Mem` proof. -/
theorem Env.Sat.has {Γ : Env} {tbl : List SpecEntry} (h : Γ.Sat tbl) {e : SpecEntry}
    (he : e ∈ tbl) (hX : Spec.XFree e.spec) : Γ.Has e.name e.spec :=
  fun xs m Q X hs => h e he xs m Q X <| by
    unfold SpecEntry.eff
    split
    · exact hX _ _ _ _ _ hs
    · exact hs

theorem Env.Sat.has_of_noExit_false {Γ : Env} {tbl : List SpecEntry} (h : Γ.Sat tbl)
    {e : SpecEntry} (he : e ∈ tbl) (hn : e.noExit = false) : Γ.Has e.name e.spec :=
  fun xs m Q X hs =>
    h e he xs m Q X (by simp only [SpecEntry.eff, hn, Bool.false_eq_true, ↓reduceIte]; exact hs)

/-- `Env.ofTable tbl` satisfies any sub-table via `List.Mem` + one shared `Nodup` proof. -/
theorem Env.Sat.ofTable {tbl sub : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup)
    (hsub : ∀ e ∈ sub, e ∈ tbl) : (Env.ofTable tbl).Sat sub :=
  fun e he _ _ _ _ h => Env.ofTable_of_mem (hsub e he) hnd h

theorem Env.Sat.ofTable_self {tbl : List SpecEntry} (hnd : (tbl.map SpecEntry.name).Nodup) :
    (Env.ofTable tbl).Sat tbl :=
  Env.Sat.ofTable hnd fun _ h => h

/-- Disjoint environment override (`Γnew` on `names`, `Γ` elsewhere). -/
@[expose] def Env.override (names : List Sym) (Γnew Γ : Env) : Env :=
  fun f as bs xs m Q X => if f ∈ names then Γnew f as bs xs m Q X else Γ f as bs xs m Q X

theorem Env.override_pos {names : List Sym} {Γnew Γ : Env} {f : Sym} (hin : f ∈ names)
    {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost} :
    Env.override names Γnew Γ f as bs xs m Q X ↔ Γnew f as bs xs m Q X := by
  simp only [Env.override, ite_eq_left hin]

theorem Env.override_neg {names : List Sym} {Γnew Γ : Env} {f : Sym} (hout : f ∉ names)
    {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost} :
    Env.override names Γnew Γ f as bs xs m Q X ↔ Γ f as bs xs m Q X := by
  simp only [Env.override, ite_eq_right hout]

theorem Env.Has.override_new {names : List Sym} {Γnew Γ : Env} {f : Sym} {as bs : List Ty}
    {S : Spec as bs} (h : Γnew.Has f S) (hin : f ∈ names) :
    (Env.override names Γnew Γ).Has f S :=
  fun xs m Q X hs => (Env.override_pos hin).mpr (h xs m Q X hs)

theorem Env.Has.override_old {names : List Sym} {Γnew Γ : Env} {f : Sym} {as bs : List Ty}
    {S : Spec as bs} (h : Γ.Has f S) (hout : f ∉ names) :
    (Env.override names Γnew Γ).Has f S :=
  fun xs m Q X hs => (Env.override_neg hout).mpr (h xs m Q X hs)

theorem Env.Sat.override_new {names : List Sym} {Γnew Γ : Env} {tbl : List SpecEntry}
    (h : Γnew.Sat tbl) (hin : ∀ e ∈ tbl, e.name ∈ names) :
    (Env.override names Γnew Γ).Sat tbl :=
  fun e he => (h e he).override_new (hin e he)

theorem Env.Sat.override_old {names : List Sym} {Γnew Γ : Env} {tbl : List SpecEntry}
    (h : Γ.Sat tbl) (hout : ∀ e ∈ tbl, e.name ∉ names) :
    (Env.override names Γnew Γ).Sat tbl :=
  fun e he => (h e he).override_old (hout e he)

/-! ## 3. Segment certificates & `ModuleOk.ofCanonical` -/

/-- Signature triple `(name, as, rs)` of a specification row, matching `Fn.sig`. -/
@[expose] def SpecEntry.sig (e : SpecEntry) : SigEntry :=
  (e.name, e.as, e.rs)

theorem names_eq_of_sigs_eq {tbl : List SpecEntry} {fs : List Fn}
    (h : tbl.map SpecEntry.sig = fs.map Fn.sig) :
    tbl.map SpecEntry.name = fs.map Fn.name := by
  have h1 := congrArg (List.map Prod.fst) h
  simpa [List.map_map, Function.comp_def, SpecEntry.sig, Fn.sig] using h1

/-- Per-segment implementation certificate under arbitrary `Γ` satisfying `deps` and `rows`. -/
@[expose] def SegCert (deps : List SpecEntry) (fns : List Fn) (rows : List SpecEntry) : Prop :=
  ∀ Γ : Env, Γ.Sat deps → Γ.Sat rows → TableImpl Γ fns rows

theorem SegCert.nil (deps : List SpecEntry) : SegCert deps [] [] :=
  fun _ _ _ => trivial

theorem TableImpl.append {Γ : Env} : ∀ {f₁ f₂ : List Fn} {r₁ r₂ : List SpecEntry},
    TableImpl Γ f₁ r₁ → f₁.length = r₁.length → TableImpl Γ f₂ r₂ →
    TableImpl Γ (f₁ ++ f₂) (r₁ ++ r₂)
  | [], _, [], _, _, _, h₂ => h₂
  | _ :: _, _, _ :: _, _, ⟨h, t⟩, hl, h₂ => ⟨h, TableImpl.append t (Nat.succ.inj hl) h₂⟩
  | [], _, _ :: _, _, _, hl, _ => nomatch hl
  | _ :: _, _, [], _, h, _, _ => h.elim

theorem TableImpl.append_sigs {Γ : Env} {f₁ f₂ : List Fn} {r₁ r₂ : List SpecEntry}
    (h₁ : TableImpl Γ f₁ r₁) (hsig : r₁.map SpecEntry.sig = f₁.map Fn.sig)
    (h₂ : TableImpl Γ f₂ r₂) : TableImpl Γ (f₁ ++ f₂) (r₁ ++ r₂) :=
  TableImpl.append h₁ (by
    have hlen := congrArg List.length hsig
    simp only [List.length_map] at hlen
    exact hlen.symm) h₂

theorem AllFns.of_forall {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h => ⟨h _ (.head _), AllFns.of_forall fun f hf => h f (.tail _ hf)⟩

theorem AllFns.append {P : Fn → Prop} :
    ∀ {f₁ f₂ : List Fn}, AllFns P f₁ → AllFns P f₂ → AllFns P (f₁ ++ f₂)
  | [], _, _, h₂ => h₂
  | _ :: _, _, ⟨h, t⟩, h₂ => ⟨h, AllFns.append t h₂⟩

theorem Module.fns_namesNodup_of_checkAcyclic {M : Module}
    (hchk : M.checkAcyclic = true) : (M.fns.map Fn.name).Nodup := by
  simp only [Module.checkAcyclic, Bool.and_eq_true] at hchk
  exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1

theorem nodup_of_checkAcyclic {M : Module} {tbl : List SpecEntry}
    (hchk : M.checkAcyclic = true)
    (hnames : tbl.map SpecEntry.name = M.fns.map Fn.name) :
    (tbl.map SpecEntry.name).Nodup :=
  hnames ▸ Module.fns_namesNodup_of_checkAcyclic hchk

/-- Flat acyclic module + aligned canonical table + `Γ`-parametric certificate ⇒ `ModuleOk`. -/
theorem ModuleOk.ofCanonical {M : Module} {tbl : List SpecEntry}
    (hchk : M.checkAcyclic = true) (hwf : AllFns Fn.Wf M.fns)
    (hnames : tbl.map SpecEntry.name = M.fns.map Fn.name)
    (hcert : ∀ Γ : Env, Γ.Sat tbl → TableImpl Γ M.fns tbl) :
    ModuleOk (Env.ofTable tbl) M :=
  Env.ofTable_moduleOk hchk hwf
    (hcert _ (Env.Sat.ofTable (nodup_of_checkAcyclic hchk hnames) fun _ h => h))

/-- `ModuleOk.ofCanonical` variant taking full signature-list alignment (`SpecEntry.sig`). -/
theorem ModuleOk.ofCanonicalSigs {M : Module} {tbl : List SpecEntry}
    (hchk : M.checkAcyclic = true) (hwf : AllFns Fn.Wf M.fns)
    (hsigs : tbl.map SpecEntry.sig = M.fns.map Fn.sig)
    (hcert : ∀ Γ : Env, Γ.Sat tbl → TableImpl Γ M.fns tbl) :
    ModuleOk (Env.ofTable tbl) M :=
  ModuleOk.ofCanonical hchk hwf (names_eq_of_sigs_eq hsigs) hcert

/-! ## 4. `O(N)` byte-trie acyclicity & `Nodup` check (`Module.checkAcyclicTrie`) -/

/- Byte-indexed signature trie (`Option (List Ty × List Ty)` payload at terminal bytes). -/
mutual
inductive SigTrie where
  | node (sig : Option (List Ty × List Ty)) (children : SigTrieList)

inductive SigTrieList where
  | nil
  | cons (k : UInt8) (v : SigTrie) (rest : SigTrieList)
end

@[expose] def SigTrie.empty : SigTrie :=
  .node none .nil

@[expose] def SigTrieList.modify (k : UInt8) (f : SigTrie → Option SigTrie) :
    SigTrieList → Option SigTrieList
  | .nil => (f .empty).map fun sub => .cons k sub .nil
  | .cons c v rest =>
    if c.toBitVec.toNat == k.toBitVec.toNat then
      (f v).map fun sub => .cons c sub rest
    else
      (SigTrieList.modify k f rest).map fun rest' => .cons c v rest'

@[expose] def SigTrie.insertBytes (s : List Ty × List Ty) :
    List UInt8 → SigTrie → Option SigTrie
  | [], .node (some _) _ => none
  | [], .node none cs => some (.node (some s) cs)
  | b :: bs, .node p cs =>
    (SigTrieList.modify b (SigTrie.insertBytes s bs) cs).map fun cs' => .node p cs'

@[expose] def SigTrieList.find (k : UInt8) : SigTrieList → Option SigTrie
  | .nil => none
  | .cons c v rest =>
    if c.toBitVec.toNat == k.toBitVec.toNat then some v else SigTrieList.find k rest

@[expose] def SigTrie.findBytes : List UInt8 → SigTrie → Option (List Ty × List Ty)
  | [], .node p _ => p
  | b :: bs, .node _ cs =>
    match SigTrieList.find b cs with
    | some sub => SigTrie.findBytes bs sub
    | none => none

@[expose] def SigTrie.hasSig (t : SigTrie) (f : Sym) (as bs : List Ty) : Bool :=
  match t.findBytes f.toByteArray.data.toList with
  | some (as', bs') => Ty.listBeq as' as && Ty.listBeq bs' bs
  | none => false

mutual
@[expose] def Expr.checkCallsTrie (t : SigTrie) (exits : List Sym) {rs : List Ty} :
    Expr (fun _ => Unit) (fun _ => Unit) rs → Bool
  | .let_ _ k => Expr.checkCallsTrie t exits (k (Tup.units _))
  | .load _ _ k => Expr.checkCallsTrie t exits (k ())
  | .store _ _ k => Expr.checkCallsTrie t exits k
  | .call f (as := as) (bs := bs) _ k =>
      t.hasSig f as bs && Expr.checkCallsTrie t exits (k (Tup.units bs))
  | .jnz _ t' e' => Expr.checkCallsTrie t exits t' && Expr.checkCallsTrie t exits e'
  | .jump _ _ | .ret _ | .hlt => true
  | .exit f _ => exits.any (fun e => f == e)
  | .group (sig := sig) bodies k =>
      Blocks.checkCallsTrie t exits (bodies (Tup.units sig)) &&
        Expr.checkCallsTrie t exits (k (Tup.units sig))

@[expose] def Blocks.checkCallsTrie (t : SigTrie) (exits : List Sym) {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig → Bool
  | _, .nil => true
  | _, .cons b bs =>
      Expr.checkCallsTrie t exits (b (Tup.units _)) && Blocks.checkCallsTrie t exits bs
end

@[expose] def Fn.checkCallsTrie (t : SigTrie) (exits : List Sym) (fn : Fn) : Bool :=
  Expr.checkCallsTrie t exits (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as))

@[expose] def SigTrie.insertExterns (t : SigTrie) : List Extern → Option SigTrie
  | [] => some t
  | ex :: exs =>
    match t.insertBytes (ex.as, ex.rs) ex.name.toByteArray.data.toList with
    | some t' => SigTrie.insertExterns t' exs
    | none => none

@[expose] def Module.checkFnsCallsTrie (exits : List Sym) (t : SigTrie) : List Fn → Bool
  | [] => true
  | fn :: fns =>
    fn.checkCallsTrie t exits &&
    match t.insertBytes (fn.as, fn.rs) fn.name.toByteArray.data.toList with
    | some t' => Module.checkFnsCallsTrie exits t' fns
    | none => false

/-- Linear-time byte-trie acyclicity and `namesNodup` check for `M : Module`,
reducible by `t_kernel_rfl` without `O(N^2)` prefix scans. -/
@[expose] def Module.checkAcyclicTrie (M : Module) : Bool :=
  match SigTrie.insertExterns .empty M.externs with
  | some t => Module.checkFnsCallsTrie M.exits t M.fns
  | none => false

private theorem toBytes_inj {s₁ s₂ : Sym}
    (h : s₁.toByteArray.data.toList = s₂.toByteArray.data.toList) : s₁ = s₂ := by
  cases s₁ with | ofByteArray b₁ _ =>
  cases s₂ with | ofByteArray b₂ _ =>
  cases b₁ with | mk a₁ =>
  cases b₂ with | mk a₂ =>
  cases a₁ with | mk l₁ =>
  cases a₂ with | mk l₂ =>
  cases h; rfl

private theorem u8_beq_eq {a b : UInt8}
    (h : (a.toBitVec.toNat == b.toBitVec.toNat) = true) : a = b := by
  have h1 : a.toBitVec = b.toBitVec := BitVec.eq_of_toNat_eq (beq_iff_eq.mp h)
  exact UInt8.ofBitVec_toBitVec a ▸ UInt8.ofBitVec_toBitVec b ▸ congrArg UInt8.ofBitVec h1

private theorem SigTrie.findBytes_empty (k : List UInt8) : SigTrie.empty.findBytes k = none := by
  cases k <;> rfl

private theorem SigTrieList.find_modify_self (k : UInt8) (f : SigTrie → Option SigTrie) :
    ∀ {cs cs' : SigTrieList}, SigTrieList.modify k f cs = some cs' →
      ∃ sub, f ((SigTrieList.find k cs).getD .empty) = some sub ∧
        SigTrieList.find k cs' = some sub
  | .nil, cs', h => by
    simp only [SigTrieList.modify, Option.map_eq_some_iff] at h
    rcases h with ⟨sub, hf, rfl⟩
    exact ⟨sub, hf, by simp only [SigTrieList.find, beq_self_eq_true, ↓reduceIte]⟩
  | .cons c v rest, cs', h => by
    simp only [SigTrieList.modify] at h
    split at h
    · rename_i hck
      simp only [Option.map_eq_some_iff] at h
      rcases h with ⟨sub, hf, rfl⟩
      refine ⟨sub, ?_, ?_⟩ <;>
        simp only [SigTrieList.find, hck, ↓reduceIte, Option.getD_some, hf]
    · rename_i hck
      simp only [Option.map_eq_some_iff] at h
      rcases h with ⟨rest', hmod, rfl⟩
      obtain ⟨sub, hf, hfind⟩ := SigTrieList.find_modify_self k f hmod
      refine ⟨sub, ?_, ?_⟩ <;>
        simp only [SigTrieList.find, hck, Bool.false_eq_true, ↓reduceIte, hf, hfind]

private theorem SigTrieList.find_modify_ne {k k' : UInt8} (hne : k' ≠ k)
    (f : SigTrie → Option SigTrie) :
    ∀ {cs cs' : SigTrieList}, SigTrieList.modify k f cs = some cs' →
      SigTrieList.find k' cs' = SigTrieList.find k' cs
  | .nil, cs', h => by
    simp only [SigTrieList.modify, Option.map_eq_some_iff] at h
    rcases h with ⟨sub, _, rfl⟩
    simp only [SigTrieList.find]
    split
    · rename_i heq; exact absurd (u8_beq_eq heq) hne.symm
    · rfl
  | .cons c v rest, cs', h => by
    simp only [SigTrieList.modify] at h
    split at h
    · rename_i hck
      simp only [Option.map_eq_some_iff] at h
      rcases h with ⟨sub, _, rfl⟩
      simp only [SigTrieList.find]
      split
      · rename_i hck'
        have e1 := u8_beq_eq hck
        have e2 := u8_beq_eq hck'
        exact absurd (e2.symm.trans e1) hne
      · rfl
    · rename_i hck
      simp only [Option.map_eq_some_iff] at h
      rcases h with ⟨rest', hmod, rfl⟩
      simp only [SigTrieList.find]
      split
      · rfl
      · exact SigTrieList.find_modify_ne hne f hmod

private theorem SigTrie.insertBytes_self (s : List Ty × List Ty) :
    ∀ (k : List UInt8) {t t' : SigTrie},
      t.insertBytes s k = some t' → t.findBytes k = none ∧ t'.findBytes k = some s
  | [], .node (some _) _, _, h => by simp [SigTrie.insertBytes] at h
  | [], .node none cs, t', h => by
    simp only [SigTrie.insertBytes, Option.some.injEq] at h
    cases h
    exact ⟨rfl, rfl⟩
  | b :: bs, .node p cs, t', h => by
    simp only [SigTrie.insertBytes, Option.map_eq_some_iff] at h
    rcases h with ⟨cs', hmod, rfl⟩
    obtain ⟨sub, hsub, hfind⟩ := SigTrieList.find_modify_self b (SigTrie.insertBytes s bs) hmod
    have ih := SigTrie.insertBytes_self s bs hsub
    simp only [SigTrie.findBytes, hfind, ih.2, and_true]
    cases hfb : SigTrieList.find b cs with
    | none => rfl
    | some v =>
      rw [hfb, Option.getD_some] at ih
      exact ih.1

private theorem SigTrie.insertBytes_ne (s : List Ty × List Ty) :
    ∀ {k k' : List UInt8} (_hne : k' ≠ k) {t t' : SigTrie},
      t.insertBytes s k = some t' → t'.findBytes k' = t.findBytes k'
  | [], [], hne, _, _, _ => absurd rfl hne
  | [], b' :: bs', _, .node none _, t', h => by
    simp only [SigTrie.insertBytes, Option.some.injEq] at h
    cases h
    rfl
  | [], b' :: bs', _, .node (some _) _, _, h => by simp [SigTrie.insertBytes] at h
  | b :: bs, [], _, .node p cs, t', h => by
    simp only [SigTrie.insertBytes, Option.map_eq_some_iff] at h
    rcases h with ⟨_, _, rfl⟩
    rfl
  | b :: bs, b' :: bs', hne, .node p cs, t', h => by
    simp only [SigTrie.insertBytes, Option.map_eq_some_iff] at h
    rcases h with ⟨cs', hmod, rfl⟩
    by_cases hb : b' = b
    · subst hb
      have hne' : bs' ≠ bs := fun h => hne (congrArg (b' :: ·) h)
      obtain ⟨sub, hsub, hfind⟩ :=
        SigTrieList.find_modify_self b' (SigTrie.insertBytes s bs) hmod
      have ih := SigTrie.insertBytes_ne s hne' hsub
      simp only [SigTrie.findBytes, hfind, ih]
      cases hfb : SigTrieList.find b' cs with
      | none => simp only [Option.getD_none, SigTrie.findBytes_empty]
      | some v => rfl
    · have hne_cs := SigTrieList.find_modify_ne hb (SigTrie.insertBytes s bs) hmod
      simp only [SigTrie.findBytes, hne_cs]

private def SigTrie.Matches (t : SigTrie) (sigs : List SigEntry) : Prop :=
  (∀ f as bs, (f, as, bs) ∈ sigs → t.findBytes f.toByteArray.data.toList = some (as, bs)) ∧
  (∀ k v, t.findBytes k = some v → ∃ f, f.toByteArray.data.toList = k ∧ (f, v.1, v.2) ∈ sigs)

private theorem SigTrie.matches_empty : SigTrie.empty.Matches [] :=
  ⟨(fun _ _ _ h => nomatch h),
   (fun k _ h => by rw [SigTrie.findBytes_empty] at h; cases h)⟩

private theorem SigTrie.matches_insert {t t' : SigTrie} {sigs : List SigEntry}
    {nm : Sym} {as bs : List Ty} (hm : t.Matches sigs)
    (hi : t.insertBytes (as, bs) nm.toByteArray.data.toList = some t') :
    nm ∉ sigs.map Prod.fst ∧ t'.Matches ((nm, as, bs) :: sigs) := by
  have hself := SigTrie.insertBytes_self (as, bs) nm.toByteArray.data.toList hi
  have hnin : nm ∉ sigs.map Prod.fst := by
    rintro hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨⟨f, a, b⟩, hfs, rfl⟩
    have hf := hm.1 f a b hfs
    rw [hself.1] at hf
    cases hf
  refine ⟨hnin, ⟨?_, ?_⟩⟩
  · intro f a b hf
    rcases List.mem_cons.mp hf with h1 | h2
    · cases h1; exact hself.2
    · have hne_nm : f ≠ nm := fun h => hnin (h ▸ List.mem_map.mpr ⟨(f, a, b), h2, rfl⟩)
      have hne_bytes : f.toByteArray.data.toList ≠ nm.toByteArray.data.toList :=
        fun h => hne_nm (toBytes_inj h)
      rw [SigTrie.insertBytes_ne (as, bs) hne_bytes hi]
      exact hm.1 f a b h2
  · intro k v hk
    by_cases heq : k = nm.toByteArray.data.toList
    · subst heq
      rw [hself.2, Option.some.injEq] at hk
      subst hk
      exact ⟨nm, rfl, .head _⟩
    · rw [SigTrie.insertBytes_ne (as, bs) heq hi] at hk
      obtain ⟨f, hfb, hfm⟩ := hm.2 k v hk
      exact ⟨f, hfb, .tail _ hfm⟩

private theorem SigTrie.hasSig_mem {t : SigTrie} {sigs : List SigEntry}
    (hm : t.Matches sigs) {f : Sym} {as bs : List Ty}
    (h : t.hasSig f as bs = true) : (f, as, bs) ∈ sigs := by
  simp only [SigTrie.hasSig] at h
  cases hfb : t.findBytes f.toByteArray.data.toList with
  | none => simp [hfb] at h
  | some p =>
    rcases p with ⟨as', bs'⟩
    rw [hfb] at h
    simp only [Bool.and_eq_true, Ty.listBeq_iff_eq] at h
    rcases h with ⟨rfl, rfl⟩
    obtain ⟨f', hf', hmem⟩ := hm.2 _ _ hfb
    cases toBytes_inj hf'
    exact hmem

mutual
private theorem Expr.callsOk_of_checkCallsTrie {t : SigTrie} {sigs : List SigEntry}
    {exits : List Sym} {rs : List Ty} (hm : t.Matches sigs) :
    (e : Expr (fun _ => Unit) (fun _ => Unit) rs) →
    Expr.checkCallsTrie t exits e = true → e.callsOk sigs exits
  | .let_ _ k, h => Expr.callsOk_of_checkCallsTrie hm (k (Tup.units _)) h
  | .load _ _ k, h => Expr.callsOk_of_checkCallsTrie hm (k ()) h
  | .store _ _ k, h => Expr.callsOk_of_checkCallsTrie hm k h
  | .call f (as := as) (bs := bs) _ k, h => by
    simp only [Expr.checkCallsTrie, Bool.and_eq_true] at h
    exact ⟨SigTrie.hasSig_mem hm h.1, Expr.callsOk_of_checkCallsTrie hm (k (Tup.units bs)) h.2⟩
  | .jnz _ t' e', h => by
    simp only [Expr.checkCallsTrie, Bool.and_eq_true] at h
    exact ⟨Expr.callsOk_of_checkCallsTrie hm t' h.1,
      Expr.callsOk_of_checkCallsTrie hm e' h.2⟩
  | .jump _ _, _ | .ret _, _ | .hlt, _ => trivial
  | .exit f _, h => by
    simp only [Expr.checkCallsTrie, List.any_eq_true, beq_iff_eq] at h
    rcases h with ⟨s, hs, rfl⟩
    exact hs
  | .group (sig := sig) bodies k, h => by
    simp only [Expr.checkCallsTrie, Bool.and_eq_true] at h
    exact ⟨Blocks.callsOk_of_checkCallsTrie hm (bodies (Tup.units sig)) h.1,
      Expr.callsOk_of_checkCallsTrie hm (k (Tup.units sig)) h.2⟩

private theorem Blocks.callsOk_of_checkCallsTrie {t : SigTrie} {sigs : List SigEntry}
    {exits : List Sym} {rs : List Ty} (hm : t.Matches sigs) :
    {sig : List (List Ty)} → (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) →
    Blocks.checkCallsTrie t exits bs = true → bs.callsOk sigs exits
  | _, .nil, _ => trivial
  | _, .cons b bs, h => by
    simp only [Blocks.checkCallsTrie, Bool.and_eq_true] at h
    exact ⟨Expr.callsOk_of_checkCallsTrie hm (b (Tup.units _)) h.1,
      Blocks.callsOk_of_checkCallsTrie hm bs h.2⟩
end

private theorem SigTrie.matches_iff {t : SigTrie} {s₁ s₂ : List SigEntry}
    (hm : t.Matches s₁) (h : ∀ e, e ∈ s₁ ↔ e ∈ s₂) : t.Matches s₂ :=
  ⟨fun f as bs hf => hm.1 f as bs ((h _).mpr hf),
   fun k v hk => let ⟨f, hfb, hfm⟩ := hm.2 k v hk; ⟨f, hfb, (h _).mp hfm⟩⟩

private theorem insertExterns_ok :
    ∀ (exts : List Extern) {t t' : SigTrie} {sigs : List SigEntry},
      t.Matches sigs →
      SigTrie.insertExterns t exts = some t' →
      (exts.map Extern.name).Nodup ∧
        (∀ x ∈ exts.map Extern.name, x ∉ sigs.map Prod.fst) ∧
        t'.Matches (exts.map Extern.sig ++ sigs)
  | [], t, t', sigs, hm, h => by
    simp only [SigTrie.insertExterns, Option.some.injEq] at h
    cases h
    exact ⟨.nil, fun _ hx => by simp at hx, hm⟩
  | ex :: exs, t, t', sigs, hm, h => by
    simp only [SigTrie.insertExterns] at h
    cases hi : t.insertBytes (ex.as, ex.rs) ex.name.toByteArray.data.toList with
    | none => simp [hi] at h
    | some t₁ =>
      rw [hi] at h
      obtain ⟨hnin, hm₁⟩ := SigTrie.matches_insert hm hi
      obtain ⟨hnd, hdisj, hm'⟩ := insertExterns_ok exs hm₁ h
      have hne_ex : ex.name ∉ exs.map Extern.name := fun hmem =>
        hdisj ex.name hmem (by simp)
      have hdisj' : ∀ x ∈ (ex :: exs).map Extern.name, x ∉ sigs.map Prod.fst := by
        intro x hx hxs
        simp only [List.map_cons, List.mem_cons] at hx
        rcases hx with rfl | hx'
        · exact hnin hxs
        · exact hdisj x hx' (List.mem_cons_of_mem _ hxs)
      have hm'' : t'.Matches ((ex :: exs).map Extern.sig ++ sigs) :=
        SigTrie.matches_iff hm' fun e => by
          simp only [List.map_cons, List.cons_append, List.mem_append, List.mem_cons]
          constructor <;> rintro (h1 | h1 | h1)
          · exact .inr (.inl h1)
          · exact .inl h1
          · exact .inr (.inr h1)
          · exact .inr (.inl h1)
          · exact .inl h1
          · exact .inr (.inr h1)
      exact ⟨List.nodup_cons.mpr ⟨hne_ex, hnd⟩, hdisj', hm''⟩

private theorem checkFnsCallsTrie_ok (exits : List Sym) (extSigs : List SigEntry) :
    ∀ (seen rest : List Fn) {t : SigTrie},
      t.Matches (seen.map Fn.sig ++ extSigs) →
      Module.checkFnsCallsTrie exits t rest = true →
      (rest.map Fn.name).Nodup ∧
        (∀ nm ∈ rest.map Fn.name, nm ∉ (seen.map Fn.sig ++ extSigs).map Prod.fst) ∧
        ∀ pre fn post, rest = pre ++ fn :: post →
          fn.callsOk ((seen ++ pre).map Fn.sig ++ extSigs) exits
  | seen, [], _, _, _ =>
    ⟨.nil, (fun _ h => nomatch h), (fun pre _ _ h => by cases pre <;> simp at h)⟩
  | seen, f :: fs, t, hm, h => by
    simp only [Module.checkFnsCallsTrie, Bool.and_eq_true] at h
    rcases h with ⟨hcall, hrest⟩
    cases hi : t.insertBytes (f.as, f.rs) f.name.toByteArray.data.toList with
    | none => simp [hi] at hrest
    | some t₁ =>
      rw [hi] at hrest
      obtain ⟨hnin, hm₁⟩ := SigTrie.matches_insert hm hi
      have hm₁' : t₁.Matches ((seen ++ [f]).map Fn.sig ++ extSigs) :=
        SigTrie.matches_iff hm₁ fun e => by
          simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
            List.cons_append, List.nil_append, List.mem_cons, List.mem_append, Fn.sig]
          constructor <;> rintro (h1 | h1 | h1)
          · exact .inr (.inl h1)
          · exact .inl h1
          · exact .inr (.inr h1)
          · exact .inr (.inl h1)
          · exact .inl h1
          · exact .inr (.inr h1)
      obtain ⟨hnd, hdisj, hcalls⟩ := checkFnsCallsTrie_ok exits extSigs (seen ++ [f]) fs hm₁' hrest
      have hf_nin_fs : f.name ∉ fs.map Fn.name := fun hmem =>
        hdisj f.name hmem (by simp [Fn.sig])
      have hdisj' : ∀ nm ∈ (f :: fs).map Fn.name,
          nm ∉ (seen.map Fn.sig ++ extSigs).map Prod.fst := by
        intro nm hnm hprev
        simp only [List.map_cons, List.mem_cons] at hnm
        rcases hnm with rfl | hnm'
        · exact hnin hprev
        · refine hdisj nm hnm' ?_
          simp only [List.map_append, List.map_cons, List.map_nil, List.mem_map,
            List.mem_append, List.mem_cons] at hprev ⊢
          rcases hprev with h1 | h1
          · exact .inl (.inl h1)
          · exact .inr h1
      refine ⟨List.nodup_cons.mpr ⟨hf_nin_fs, hnd⟩, hdisj', fun pre fn post hsplit => ?_⟩
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hsplit
        rcases hsplit with ⟨rfl, _⟩
        simpa [Fn.callsOk, List.append_nil] using
          Expr.callsOk_of_checkCallsTrie hm _ hcall
      | cons f' pre' =>
        simp only [List.cons_append, List.cons.injEq] at hsplit
        rcases hsplit with ⟨rfl, hfs⟩
        simpa [List.append_assoc] using hcalls pre' fn post hfs

private theorem checkAcyclicTrie_sound {M : Module} (hchk : M.checkAcyclicTrie = true) :
    M.namesNodup ∧
      ∀ pre fn post, M.fns = pre ++ fn :: post →
        fn.callsOk (pre.map Fn.sig ++ M.externs.map Extern.sig) M.exits := by
  simp only [Module.checkAcyclicTrie] at hchk
  cases he : SigTrie.insertExterns .empty M.externs with
  | none => simp [he] at hchk
  | some t₀ =>
    rw [he] at hchk
    obtain ⟨hnd_ext, _, hm₀⟩ := insertExterns_ok M.externs SigTrie.matches_empty he
    have hm₀' : t₀.Matches ([].map Fn.sig ++ M.externs.map Extern.sig) := by
      simpa using hm₀
    obtain ⟨hnd_fns, hdisj, hcalls⟩ :=
      checkFnsCallsTrie_ok M.exits (M.externs.map Extern.sig) [] M.fns hm₀' hchk
    have hdisj' : ∀ nm ∈ M.fns.map Fn.name, nm ∉ M.externs.map Extern.name := by
      intro nm hnm hex
      apply hdisj nm hnm
      simp only [List.map_nil, List.nil_append, List.mem_map, Extern.sig] at hex ⊢
      rcases hex with ⟨ex, hex, rfl⟩
      exact ⟨(ex.name, ex.as, ex.rs), ⟨ex, hex, rfl⟩, rfl⟩
    have hnd : M.namesNodup := by
      rw [Module.namesNodup, Module.names, List.nodup_append]
      exact ⟨hnd_fns, hnd_ext, fun a ha b hb hab => hdisj' a ha (hab ▸ hb)⟩
    exact ⟨hnd, fun pre fn post hsplit => by simpa using hcalls pre fn post hsplit⟩

theorem Module.fns_namesNodup_of_checkAcyclicTrie {M : Module}
    (hchk : M.checkAcyclicTrie = true) : (M.fns.map Fn.name).Nodup :=
  (List.nodup_append.mp (checkAcyclicTrie_sound hchk).1).1

theorem nodup_of_checkAcyclicTrie {M : Module} {tbl : List SpecEntry}
    (hchk : M.checkAcyclicTrie = true)
    (hnames : tbl.map SpecEntry.name = M.fns.map Fn.name) :
    (tbl.map SpecEntry.name).Nodup :=
  hnames ▸ Module.fns_namesNodup_of_checkAcyclicTrie hchk

/-- `O(N)` byte-trie analogue of `ModuleOk.ofCanonical` avoiding `O(N^2)` prefix scans. -/
theorem ModuleOk.ofCanonicalTrie {M : Module} {tbl : List SpecEntry}
    (hchk : M.checkAcyclicTrie = true) (hwf : AllFns Fn.Wf M.fns)
    (hnames : tbl.map SpecEntry.name = M.fns.map Fn.name)
    (hcert : ∀ Γ : Env, Γ.Sat tbl → TableImpl Γ M.fns tbl) :
    ModuleOk (Env.ofTable tbl) M := by
  obtain ⟨hndM, hcalls⟩ := checkAcyclicTrie_sound hchk
  have hndFns : (M.fns.map Fn.name).Nodup := (List.nodup_append.mp hndM).1
  have hndTbl : (tbl.map SpecEntry.name).Nodup := hnames ▸ hndFns
  have hsound := Env.ofTable_sound hndFns (hcert _ (Env.Sat.ofTable hndTbl fun _ h => h))
  refine ⟨hndM, fun pre fn post hsplit => ?_⟩
  have hmem : fn ∈ M.fns := hsplit ▸ by simp
  exact ⟨hwf.mem fn hmem, hcalls pre fn post hsplit, hsound fn hmem⟩

/-- `ModuleOk.ofCanonicalTrie` variant taking full signature-list alignment (`SpecEntry.sig`). -/
theorem ModuleOk.ofCanonicalTrieSigs {M : Module} {tbl : List SpecEntry}
    (hchk : M.checkAcyclicTrie = true) (hwf : AllFns Fn.Wf M.fns)
    (hsigs : tbl.map SpecEntry.sig = M.fns.map Fn.sig)
    (hcert : ∀ Γ : Env, Γ.Sat tbl → TableImpl Γ M.fns tbl) :
    ModuleOk (Env.ofTable tbl) M :=
  ModuleOk.ofCanonicalTrie hchk hwf (names_eq_of_sigs_eq hsigs) hcert

end LeanQbe.T
