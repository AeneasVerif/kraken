module

public import LeanQbe.T.MainLinkScc
public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertProof
public import LeanQbe.T.MainCertElab
public import LeanQbe.T.Scc
public meta import Lean
public meta import LeanQbe.T.MainLinkScc
public meta import LeanQbe.T.MainCertCore
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.MainLinkSplice
public meta import LeanQbe.T.MainSplice
public meta import LeanQbe.T.Scc

/-!
# Mixed Acyclic + Cyclic-SCC Compilation Certificates (`MainCertScc`)

Noncomputable-by-default certificate layer over `MainLinkScc`, `MainCertCore`, `MainCertProof`,
and `MainCertElab`:
* `LinkedCertScc`: closed whole-module certificate mixing `.acyc`, `.recSCC`, and `.recBudgetSCC`.
* `compile_linked_scc!` / `compile_linked_budget_scc!`: parallel sub-chunked kernel checking.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

open Std Std.ExtHashMap
open LeanQbe.T.LinkRec

/-! ## 1. O(#subchunks) Slice, `supportsSource`, and `checkChunksCalls` Helpers -/

theorem slice_sub_last_mod_eq {α : Type _} (l : List α) (s : Nat) :
    l.drop s = (l.drop s ++ []) ++ [] := by simp
theorem slice_sub_last_eq {α : Type _} {l rest : List α} {s k : Nat}
    (h : l.drop (s + k) = rest) : l.drop s = ((l.drop s).take k ++ []) ++ rest := by
  simpa using slice_cons_eq h
theorem slice_sub_cons_eq {α : Type _} {l : List α} {scs tail : List α} {s k : Nat}
    (h : l.drop (s + k) = scs ++ tail) : l.drop s = ((l.drop s).take k ++ scs) ++ tail := by
  rw [List.append_assoc]; exact slice_cons_eq h
theorem budgetFns_last_mod_eq (l : List BudgetFn) (s : Nat) :
    (l.map BudgetFn.toFn).drop s = (l.drop s ++ []).map BudgetFn.toFn ++ [] := by
  rw [List.append_nil, List.append_nil, List.map_drop]
theorem budgetFns_last_eq {l : List BudgetFn} {tail : List Fn} {s k : Nat}
    (h : (l.map BudgetFn.toFn).drop (s + k) = tail) :
    (l.map BudgetFn.toFn).drop s = ((l.drop s).take k ++ []).map BudgetFn.toFn ++ tail := by
  rw [List.append_nil, List.map_take, List.map_drop]; exact slice_cons_eq h
theorem budgetFns_cons_eq {l : List BudgetFn} {curBfs : List BudgetFn} {tail : List Fn}
    {s k : Nat} (h : (l.map BudgetFn.toFn).drop (s + k) = curBfs.map BudgetFn.toFn ++ tail) :
    (l.map BudgetFn.toFn).drop s = ((l.drop s).take k ++ curBfs).map BudgetFn.toFn ++ tail := by
  rw [List.map_append, List.map_take, List.map_drop, List.append_assoc]; exact slice_cons_eq h
theorem supportsAll_budget_nil (lt : LegalTarget) :
    ∀ b ∈ ([] : List BudgetFn), (b.toFn.earlyOpt).body.supportsSource lt = true :=
  fun _ hb => nomatch hb
theorem supportsAll_budget_append (lt : LegalTarget) {bs₁ bs₂ : List BudgetFn}
    (h₁ : ∀ b ∈ bs₁, (b.toFn.earlyOpt).body.supportsSource lt = true)
    (h₂ : ∀ b ∈ bs₂, (b.toFn.earlyOpt).body.supportsSource lt = true) :
    ∀ b ∈ bs₁ ++ bs₂, (b.toFn.earlyOpt).body.supportsSource lt = true := fun b hb =>
  (List.mem_append.mp hb).elim (h₁ b) (h₂ b)
theorem supportsAll_budget_leaf (lt : LegalTarget) (bfs : List BudgetFn)
    (h : ∀ b ∈ bfs, (b.toFn.earlyOpt).body.supportsSource lt = true) :
    ∀ f ∈ bfs.map BudgetFn.toFn, (f.earlyOpt).body.supportsSource lt = true := fun f hf => by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hf; exact h b hb
theorem supportsAll_leaf {lt : LegalTarget} {fs : List Fn}
    (h : checkSupportsChunk lt fs = true) :
    ∀ f ∈ fs, (f.earlyOpt).body.supportsSource lt = true := fun f hf => List.all_eq_true.mp h f hf

/-- Variant of `LinkRec.compileModuleRecAux` gating `supportsSource lt` once on `f.earlyOpt`. -/
@[expose] def compileModuleRecAuxSupp (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (recSigs : List SigEntry) (extCallees : List (SigEntry × Nat))
    (exits : List Sym) (nX : Nat) :
    List Fn → List I.Hints → Except String (List I.Directive × Nat × Nat)
  | [], [] => .ok ([], 0, 0)
  | f :: fs, h :: hs =>
    let ef := f.earlyOpt
    if ef.body.supportsSource lt then
      let mf := Fn.midFromEarly lt ef
      match Rega.lowerFn I h mf.ext mf,
            checkAndBoundRecExt I raBytes recSigs extCallees exits nX h mf.ext with
      | .ok c, some (bf, sf) =>
        match compileModuleRecAuxSupp I lt raBytes recSigs extCallees exits nX fs hs with
        | .ok (cs, brest, srest) => .ok (c ++ cs, Nat.max bf brest, Nat.max sf srest)
        | .error e => .error e
      | .error e, _ => .error s!"{f.name}: {e}"
      | _, none => .error s!"{f.name}: unknown callee or undeclared exit"
    else .error s!"{f.name}: unsupported source op for target"
  | _, _ => .error "compileModuleRec: fn/hints length mismatch"

private theorem recAuxSupp_spec {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat} :
    ∀ {fs : List Fn} {hints : List I.Hints} {res : List I.Directive × Nat × Nat},
      compileModuleRecAuxSupp I lt raBytes recSigs extCallees exits nX fs hints = .ok res →
      compileModuleRecAux I lt raBytes recSigs extCallees exits nX fs hints = .ok res ∧
        ∀ f ∈ fs, (f.earlyOpt).body.supportsSource lt = true
  | [], [], _, h => ⟨h, fun _ hf => nomatch hf⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => by dsimp only [compileModuleRecAuxSupp] at h; cases h
  | f :: fs, hint :: hints, _, h => by
    dsimp only [compileModuleRecAuxSupp] at h; dsimp only [compileModuleRecAux, Fn.mid]
    cases hs' : (f.earlyOpt).body.supportsSource lt <;> simp only [hs'] at h
    · cases h
    · cases hl : Rega.lowerFn I hint _ _ <;> simp only [hl] at h
      · cases h
      · cases hchk : checkAndBoundRecExt _ _ _ _ _ _ _ _ <;> simp only [hchk] at h ⊢
        · cases h
        · cases hrest : compileModuleRecAuxSupp I lt raBytes recSigs extCallees exits nX
              fs hints <;> simp only [hrest] at h
          · cases h
          · obtain ⟨ihc, ihs⟩ := recAuxSupp_spec hrest; rw [ihc]
            exact ⟨h, fun g hg => by
              rcases List.mem_cons.mp hg with rfl | hg'; exact hs'; exact ihs g hg'⟩

theorem compileModuleRecAux_of_supp {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs : List Fn} {hints : List I.Hints} {res : List I.Directive × Nat × Nat}
    (h : compileModuleRecAuxSupp I lt raBytes recSigs extCallees exits nX fs hints = .ok res) :
    compileModuleRecAux I lt raBytes recSigs extCallees exits nX fs hints = .ok res :=
  (recAuxSupp_spec h).1

theorem supportsAll_of_compileModuleRecAuxSupp {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs : List Fn} {hints : List I.Hints} {res : List I.Directive × Nat × Nat}
    (h : compileModuleRecAuxSupp I lt raBytes recSigs extCallees exits nX fs hints = .ok res) :
    ∀ f ∈ fs, (f.earlyOpt).body.supportsSource lt = true :=
  (recAuxSupp_spec h).2

/-- Variant of `compileModuleBudgetRecAux` gating `supportsSource lt` on `bfn.toFn.earlyOpt`. -/
@[expose] def compileModuleBudgetRecAuxSupp (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (recSigs : List SigEntry) (extCallees : List (SigEntry × Nat))
    (exits : List Sym) (nX : Nat) :
    List BudgetFn → List I.Hints → Except String (List I.Directive)
  | [], [] => .ok []
  | bfn :: bfs, h :: hs =>
    let f := bfn.toFn; let ef := f.earlyOpt
    if ef.body.supportsSource lt then
      let mf := Fn.midFromEarly lt ef
      match Rega.lowerFn I h mf.ext mf,
            checkAndBoundBudgetRecExt I raBytes recSigs extCallees exits nX h mf.ext bfn with
      | .ok c, true =>
        match compileModuleBudgetRecAuxSupp I lt raBytes recSigs extCallees exits nX bfs hs with
        | .ok cs => .ok (c ++ cs) | .error e => .error e
      | .error e, _ => .error s!"{f.name}: {e}"
      | _, false => .error s!"{f.name}: budget check failed"
    else .error s!"{f.name}: unsupported source op for target"
  | _, _ => .error "compileModuleBudgetRec: fn/hints length mismatch"

private theorem budgetRecAuxSupp_spec {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat} :
    ∀ {bfs : List BudgetFn} {hints : List I.Hints} {code : List I.Directive},
      compileModuleBudgetRecAuxSupp I lt raBytes recSigs extCallees exits nX bfs hints = .ok code →
      compileModuleBudgetRecAux I lt raBytes recSigs extCallees exits nX bfs hints = .ok code ∧
        ∀ bfn ∈ bfs, (bfn.toFn.earlyOpt).body.supportsSource lt = true
  | [], [], _, h => ⟨h, fun _ hb => nomatch hb⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => by
      dsimp only [compileModuleBudgetRecAuxSupp] at h; cases h
  | bfn :: bfs, hint :: hints, _, h => by
    dsimp only [compileModuleBudgetRecAuxSupp] at h; dsimp only [compileModuleBudgetRecAux, Fn.mid]
    cases hs' : (bfn.toFn.earlyOpt).body.supportsSource lt <;> simp only [hs'] at h
    · cases h
    · cases hl : Rega.lowerFn I hint _ _ <;> simp only [hl] at h
      · cases h
      · cases hchk : checkAndBoundBudgetRecExt _ _ _ _ _ _ _ _ _ <;> simp only [hchk] at h ⊢
        · cases h
        · cases hrest : compileModuleBudgetRecAuxSupp I lt raBytes recSigs extCallees exits nX
              bfs hints <;> simp only [hrest] at h
          · cases h
          · obtain ⟨ihc, ihs⟩ := budgetRecAuxSupp_spec hrest; rw [ihc]
            exact ⟨h, fun b hb => by
              rcases List.mem_cons.mp hb with rfl | hb'; exact hs'; exact ihs b hb'⟩

theorem compileModuleBudgetRecAux_of_supp {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {bfs : List BudgetFn} {hints : List I.Hints} {code : List I.Directive}
    (h : compileModuleBudgetRecAuxSupp I lt raBytes recSigs extCallees exits nX bfs hints =
      .ok code) :
    compileModuleBudgetRecAux I lt raBytes recSigs extCallees exits nX bfs hints = .ok code :=
  (budgetRecAuxSupp_spec h).1

theorem supportsAll_of_compileModuleBudgetRecAuxSupp {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {bfs : List BudgetFn} {hints : List I.Hints} {code : List I.Directive}
    (h : compileModuleBudgetRecAuxSupp I lt raBytes recSigs extCallees exits nX bfs hints =
      .ok code) :
    ∀ bfn ∈ bfs, (bfn.toFn.earlyOpt).body.supportsSource lt = true :=
  (budgetRecAuxSupp_spec h).2

/-- Accumulated signature list produced by threading `checkChunksCalls` across `chunks`. -/
@[expose] def sccChunksSigAcc {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    List SigEntry → List (Chunk T lt exits nX) → List SigEntry
  | extSigs, [] => extSigs
  | extSigs, c :: cs => sccChunksSigAcc (c.fns.map Fn.sig ++ extSigs) cs

theorem checkChunksCalls_append {T : Target} {lt : LegalTarget} {nX : Nat}
    (exits : List Sym) :
    ∀ (cs₁ cs₂ : List (Chunk T lt exits nX)) (extSigs : List SigEntry),
      checkChunksCalls exits extSigs (cs₁ ++ cs₂) =
        (checkChunksCalls exits extSigs cs₁ &&
          checkChunksCalls exits (sccChunksSigAcc extSigs cs₁) cs₂)
  | [], _, _ => by simp [checkChunksCalls, sccChunksSigAcc]
  | c :: rest, cs₂, extSigs => by
      dsimp only [List.cons_append, checkChunksCalls, sccChunksSigAcc]
      rw [checkChunksCalls_append exits rest cs₂ (c.fns.map Fn.sig ++ extSigs), Bool.and_assoc]

private theorem chunksFns_map_acyc {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (cs : List (CompiledChunk T lt exits nX)), sccChunksFns (cs.map Chunk.acyc) = chunksFns cs
  | [] => rfl | c :: cs => by simp [sccChunksFns, chunksFns, Chunk.fns, chunksFns_map_acyc cs]

private theorem chunksCode_map_acyc {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (cs : List (CompiledChunk T lt exits nX)), sccChunksCode (cs.map Chunk.acyc) = chunksCode cs
  | [] => rfl | c :: cs => by simp [sccChunksCode, chunksCode, Chunk.code, chunksCode_map_acyc cs]

private theorem chunksMaxBound_map_acyc {T : Target} {lt : LegalTarget} {exits : List Sym}
    {nX : Nat} :
    ∀ (cs : List (CompiledChunk T lt exits nX)),
      sccChunksMaxBound (cs.map Chunk.acyc) = chunksMaxBound cs
  | [] => rfl
  | c :: cs => by
      simp [sccChunksMaxBound, chunksMaxBound, Chunk.maxBound, chunksMaxBound_map_acyc cs]

private theorem checkChunksExt_map_acyc {T : Target} {lt : LegalTarget} {exits : List Sym}
    {nX : Nat} :
    ∀ (acc : List (SigEntry × Nat)) (cs : List (CompiledChunk T lt exits nX)),
      checkSccChunksExt acc (cs.map Chunk.acyc) = checkChunksExt acc cs
  | _, [] => rfl
  | _, _ :: cs => by
      simp [checkSccChunksExt, checkChunksExt, Chunk.extCallees, Chunk.sigBounds,
        checkChunksExt_map_acyc _ cs]

theorem checkLinkSccList_map_acyc {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (ext₀ : List (SigEntry × Nat))
    (cs : List (CompiledChunk T lt exits nX)) (h : checkLinkList L ext₀ cs = true)
    (hdisj : !(ext₀.any (fun p => ((chunksFns cs).map Fn.name).any
      (fun nm => nm == p.1.1))) = true) :
    checkLinkSccList L ext₀ (cs.map Chunk.acyc) = true := by
  dsimp only [checkLinkList] at h; dsimp only [checkLinkSccList, checkHostNamesOk]
  rw [chunksFns_map_acyc, chunksCode_map_acyc, checkChunksExt_map_acyc]
  simp only [Bool.and_eq_true, and_assoc] at h ⊢
  exact ⟨h.1, hdisj, h.2⟩

/-! ## 2. `LinkedCertScc` Certificate Structure & Proof API -/

/-- Closed whole-module native compilation and linking certificate over mixed `.acyc`, `.recSCC`,
and `.recBudgetSCC` chunks (`MainLinkScc`), emitting `noncomputable` certificates by default. -/
structure LinkedCertScc (T : Target) (L : TargetLayout T) (lt : LegalTarget)
    (hcl : Rega.LabelClean T.toIsa) (mod : Module)
    (ext₀ : List (SigEntry × Nat) := []) (exits : List Sym := []) (nX : Nat := 0)
    (maxBound : Nat := 2048) (extSigs : List SigEntry := mod.externs.map Extern.sig) :
    Type 1 where
  chunks : List (Chunk T lt exits nX)
  linkCheck : checkLinkSccList L ext₀ chunks = true
  callsCheck : checkChunksCalls exits extSigs chunks = true
  fns_eq : mod.fns = sccChunksFns chunks
  supportsAll : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true
  maxBound_le : sccChunksMaxBound chunks ≤ maxBound

namespace LinkedCertScc

variable {T : Target} {L : TargetLayout T} {lt : LegalTarget}
  {hcl : Rega.LabelClean T.toIsa} {mod : Module}
  {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat} {extSigs : List SigEntry}

@[expose] noncomputable def host
    (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs) : T.mach.Host :=
  sccHost L ext₀ cert.chunks cert.linkCheck
@[expose] noncomputable def code
    (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs) : List T.Directive :=
  sccChunksCode cert.chunks
@[expose] noncomputable def bound
    (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs) (nm : Sym) : Nat :=
  sccBound cert.chunks nm
@[expose] noncomputable def sem
    (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs)
    (Γ₀ : Env := fun _ _ _ _ _ _ _ => False) : Env :=
  semChunks extSigs Γ₀ cert.chunks
@[expose] def numChunks
    (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs) : Nat :=
  cert.chunks.length

/-- Lift an acyclic `LinkedCert` into `LinkedCertScc` given `checkChunksCalls`. -/
@[expose] noncomputable def ofLinkedCert
    (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxBound)
    (hdisj : !(ext₀.any (fun p => (mod.fns.map Fn.name).any
      (fun nm => nm == p.1.1))) = true)
    (hcalls : checkChunksCalls exits (mod.externs.map Extern.sig)
      (cert.chunks.map Chunk.acyc) = true) :
    LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound where
  chunks := cert.chunks.map Chunk.acyc
  linkCheck := checkLinkSccList_map_acyc L ext₀ cert.chunks cert.linkCheck
    (by simpa [← cert.fns_eq] using hdisj)
  callsCheck := hcalls
  fns_eq := by rw [chunksFns_map_acyc]; exact cert.fns_eq
  supportsAll := cert.supportsAll
  maxBound_le := by rw [chunksMaxBound_map_acyc]; exact cert.maxBound_le

/-- Compositionally link two pre-verified `LinkedCertScc`s using metadata-only checking. -/
@[expose] noncomputable def append {mod₁ mod₂ mod : Module} {ext₂ : List (SigEntry × Nat)}
    {maxB₁ maxB₂ : Nat} {extSigs₁ extSigs₂ extSigs : List SigEntry}
    (c₁ : LinkedCertScc T L lt hcl mod₁ ext₀ exits nX maxB₁ extSigs₁)
    (c₂ : LinkedCertScc T L lt hcl mod₂ ext₂ exits nX maxB₂ extSigs₂)
    (hmod : mod.fns = mod₁.fns ++ mod₂.fns)
    (hchk : checkLinkSccList L ext₀ (c₁.chunks ++ c₂.chunks) = true)
    (hcalls : checkChunksCalls exits extSigs (c₁.chunks ++ c₂.chunks) = true) :
    LinkedCertScc T L lt hcl mod ext₀ exits nX (Nat.max maxB₁ maxB₂) extSigs where
  chunks := c₁.chunks ++ c₂.chunks
  linkCheck := hchk; callsCheck := hcalls
  fns_eq := by rw [hmod, c₁.fns_eq, c₂.fns_eq, sccChunksFns_append]
  supportsAll := fun f hf => by
    rw [hmod, List.mem_append] at hf
    rcases hf with h1 | h2; exact c₁.supportsAll f h1; exact c₂.supportsAll f h2
  maxBound_le := by
    rw [sccChunksMaxBound_append]
    exact Nat.max_le.mpr
      ⟨Nat.le_trans c₁.maxBound_le (Nat.le_max_left _ _),
       Nat.le_trans c₂.maxBound_le (Nat.le_max_right _ _)⟩

theorem bound_le_max
    (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs) (nm : Sym) :
    cert.bound nm ≤ maxBound :=
  Nat.le_trans (sccBound_le_max cert.chunks nm) cert.maxBound_le
theorem bound_eq_chunk
    (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs)
    {c : Chunk T lt exits nX} (hc : c ∈ cert.chunks) {nm : Sym} (hnm : nm ∈ c.fns.map Fn.name) :
    cert.bound nm = c.bound nm :=
  sccBound_eq_chunk cert.chunks
    (List.nodup_append.mp (checkLinkSccList_parts cert.linkCheck).2.2.2.2.1).1 c hc hnm
theorem prog_host (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs) :
    T.mach.prog cert.host = cert.code ++ exits.map T.frame.label :=
  sccProg_host L ext₀ cert.chunks cert.linkCheck
theorem code_infix_host (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs) :
    cert.code.IsInfixAt (T.mach.prog cert.host) 0 :=
  sccCode_infix_host L ext₀ cert.chunks cert.linkCheck
theorem labelsUnique (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs) :
    T.LabelsUnique cert.host :=
  sccLabelsUnique L hcl ext₀ cert.chunks cert.linkCheck
theorem defined_exit_host (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs)
    {g : Sym} (hg : g ∈ exits) : T.Defined cert.host g :=
  sccDefined_exit_host L ext₀ cert.chunks cert.linkCheck hg

private theorem mem_chunk_of_mem_sccChunksFns {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} {f : Fn} :
    ∀ {chunks : List (Chunk T lt exits nX)},
      f ∈ sccChunksFns chunks → ∃ c ∈ chunks, f ∈ c.fns
  | [], h => by simp [sccChunksFns] at h
  | c₀ :: cs, h => by
      dsimp only [sccChunksFns] at h
      rcases List.mem_append.mp h with h0 | hcs
      · exact ⟨c₀, List.mem_cons_self, h0⟩
      · obtain ⟨c', hc', hfc'⟩ := mem_chunk_of_mem_sccChunksFns hcs
        exact ⟨c', List.mem_cons_of_mem _ hc', hfc'⟩

/-- General linked-host `FnSpec` over `cert.sem Γ₀`. -/
theorem fnSpec_linked (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs)
    (Γ₀ : Env) (hnd_ext : (extSigs.map Prod.fst).Nodup)
    (hdisj_ext : ∀ nm ∈ mod.fns.map Fn.name, nm ∉ extSigs.map Prod.fst)
    (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hext : ∀ p ∈ ext₀,
      T.FnSpec cert.host p.1.1
        (legalEnv lt (Env.restrict Γ₀ extSigs) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : ∀ p ∈ ext₀, ∀ q ∈ ext₀, p.1.1 = q.1.1 → p.2 = q.2)
    {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined cert.host f.name ∧
      T.FnSpec cert.host f.name
        (legalEnv lt (Env.onlyFn f (cert.sem Γ₀)) f.name
          (lt.legalSig f.as) (lt.legalSig f.rs))
        (cert.bound f.name) nX := by
  obtain ⟨c, hc, hfc⟩ := mem_chunk_of_mem_sccChunksFns (cert.fns_eq ▸ hf)
  exact linkChunks_fnSpec_linked L hcl ext₀ extSigs Γ₀ cert.chunks cert.linkCheck
    cert.callsCheck hnd_ext (fun nm hm => hdisj_ext nm (cert.fns_eq ▸ hm))
    (fun g hg => hwf g (cert.fns_eq ▸ hg)) (fun g hg => cert.supportsAll g (cert.fns_eq ▸ hg))
    hext hext_uniq c hc f hfc

/-- Self-contained (`ext₀ = []`, `extSigs = []`) whole-module `Defined` + `FnSpec` on
`cert.host` against canonical `cert.sem`. -/
theorem fnSpec_host (cert : LinkedCertScc T L lt hcl mod [] exits nX maxBound [])
    (hwf : ∀ f ∈ mod.fns, f.Wf) {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined cert.host f.name ∧
      T.FnSpec cert.host f.name
        (legalEnv lt (Env.onlyFn f (cert.sem (fun _ _ _ _ _ _ _ => False))) f.name
          (lt.legalSig f.as) (lt.legalSig f.rs))
        (cert.bound f.name) nX :=
  cert.fnSpec_linked (fun _ _ _ _ _ _ _ => False) List.nodup_nil
    (fun _ _ hm => nomatch hm) hwf (fun _ h => nomatch h) (fun _ h => nomatch h) hf

/-- Source-level `Defined` + `FnSpec` on `cert.host` (`ext₀ = []`, `extSigs = []`) for any user
specification `spec` lying below `cert.sem`. -/
theorem fnSpec_host_src_of_le (cert : LinkedCertScc T L lt hcl mod [] exits nX maxBound [])
    (hwf : ∀ f ∈ mod.fns, f.Wf) {f : Fn} (hf : f ∈ mod.fns) (spec : Spec f.as f.rs)
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', spec args m Q X → spec args m Q X')
    (hle : ∀ args m Q X, spec args m Q X →
      cert.sem (fun _ _ _ _ _ _ _ => False) f.name f.as f.rs args m Q X) :
    T.Defined cert.host f.name ∧ T.FnSpec cert.host f.name spec (cert.bound f.name) nX := by
  obtain ⟨hdef, hspec⟩ := cert.fnSpec_host hwf hf
  exact ⟨hdef, Target.FnSpec.of_spec T (fnSpec_of_legalEnv_onlyFn has hrs hspec)
    fun args m Q X hs => hle args m Q _ (hnoex args m Q X _ hs)⟩

/-- Project the head chunk's `Chunk.sem` into `semChunks extSigs Γ₀ (c :: cs)` when `f.name` does
not appear in any trailing chunk `cs`. -/
theorem semChunks_of_head {c : Chunk T lt exits nX} {cs : List (Chunk T lt exits nX)}
    {extSigs : List SigEntry} {Γ₀ : Env} {f : Fn}
    (hnot : f.name ∉ (sccChunksFns cs).map Fn.name) (xs : Tup Val f.as) (m : Mem 64)
    (Q : Post f.rs) (X : XPost) (h : c.sem extSigs Γ₀ f.name f.as f.rs xs m Q X) :
    semChunks extSigs Γ₀ (c :: cs) f.name f.as f.rs xs m Q X := by
  dsimp only [semChunks]
  rcases c.sem_elim h with hsig | ⟨hex, _⟩
  · exact (semChunks_agree_earlier cs (c.fns.map Fn.sig ++ extSigs) (c.sem extSigs Γ₀)
      hnot (List.mem_append_left _ hsig) xs m Q X).mpr h
  · exact (semChunks_agree_earlier cs (c.fns.map Fn.sig ++ extSigs) (c.sem extSigs Γ₀)
      hnot (List.mem_append_right _ hex) xs m Q X).mpr h

theorem recChunk_sem_of_depth {extCallees : List (SigEntry × Nat)} {fuel : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxB : Nat}
    (cr : CompiledRec T lt extCallees exits nX fuel fs hints maxB)
    {extSigs : List SigEntry} {Γ₀ : Env} {f : Fn} (hf : f ∈ fs) {d : Nat} (hd : d ≤ fuel)
    {xs : Tup Val f.as} {m : Mem 64} {Q : Post f.rs} {X : XPost}
    (hsem : DepthEnv.semScc ⟨fs, externsOfSigs extSigs, exits⟩ Γ₀ d f.name f.as f.rs xs m Q X) :
    (Chunk.recSCC extCallees fuel fs hints maxB cr).sem extSigs Γ₀ f.name f.as f.rs xs m Q X :=
  Or.inl ⟨List.mem_map_of_mem hf,
    DepthEnv.semScc_depth_mono ⟨fs, externsOfSigs extSigs, exits⟩ Γ₀ hd _ _ _ _ _ _ _ hsem⟩

theorem recBudgetChunk_sem_of_budgetSemScc {extCallees : List (SigEntry × Nat)}
    {bfs : List BudgetFn} {hints : List T.toIsa.Hints} {maxB : Nat}
    {exportBounds : List (Sym × Nat)}
    (cbr : CompiledBudgetRec T lt extCallees exits nX bfs hints maxB exportBounds)
    {extSigs : List SigEntry} {Γ₀ : Env} {bfn : BudgetFn} (hbfn : bfn ∈ bfs) {sb : Nat}
    (hsb : sb ≤ budgetBound exportBounds maxB bfn.toFn.name)
    {xs : Tup Val bfn.toFn.as} {m : Mem 64} {Q : Post bfn.toFn.rs} {X : XPost}
    (hsem : BudgetEnv.semScc ⟨bfs, externsOfSigs extSigs, exits⟩ Γ₀ sb
      bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs m Q X) :
    (Chunk.recBudgetSCC extCallees bfs hints maxB exportBounds cbr).sem extSigs Γ₀
      bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs m Q X :=
  Or.inl ⟨List.mem_map_of_mem hbfn,
    BudgetEnv.semScc_budget_mono ⟨bfs, externsOfSigs extSigs, exits⟩ Γ₀ hsb _ _ _ _ _ _ _ hsem⟩

theorem acycChunk_sem_of_semScc (cc : CompiledChunk T lt exits nX)
    {extSigs : List SigEntry} {Γ₀ : Env} {f : Fn} (hf : f ∈ cc.fs)
    {xs : Tup Val f.as} {m : Mem 64} {Q : Post f.rs} {X : XPost}
    (hsem : Env.semScc ⟨cc.fs, externsOfSigs extSigs, exits⟩ Γ₀ f.name f.as f.rs xs m Q X) :
    (Chunk.acyc cc).sem extSigs Γ₀ f.name f.as f.rs xs m Q X :=
  Or.inl ⟨List.mem_map_of_mem hf, hsem⟩

/-! ### Concrete `TargetInit` `Eventually` lifts -/

section ConcreteInit

variable {maxStack maxMem : Nat}

theorem run_fnSpec (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs)
    (I : TargetInit T maxStack maxMem) {nm : Sym} {as bs : List Ty} {spec : Spec as bs}
    (hf : T.FnSpec cert.host nm spec (cert.bound nm) nX)
    (bsMem : List UInt8) (args : Tup Val as) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs as).isSome = true) {Q : Post bs} {X : XPost}
    (hspec : spec args (bsMem.At 0x1000#64) Q X) {post : T.mach.State → Prop}
    (hpost : ∀ st,
      (T.mach.pc st = I.ra0 ∧ ∃ rets m', Q rets m' ∧ T.RetsIn rets (T.mach.data st) ∧
        (T.mach.mem (T.mach.data st) =⋆ Eq m' ⋆ T.Exit I.sp0 (cert.bound nm) ⋆
          Std.ExtHashMap.emp)) ∨
      (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64), X sym' cs xs m' ∧
        T.mach.pc st = T.mach.labelAddr cert.host sym' ∧ T.ArgsIn xs (T.mach.data st)) → post st)
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host) post
      (T.mach.mkState (I.initState (cert.bound nm) bsMem args) (T.mach.labelAddr cert.host nm)) :=
  I.run_fnSpec_of cert.host cert.bound maxBound cert.bound_le_max hf bsMem args hbs hargs hspec
    hpost hbound
theorem run_ret1 (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs)
    (I : TargetInit T maxStack maxMem) {nm : Sym} {as : List Ty} {t : Ty} {spec : Spec as [t]}
    (hf : T.FnSpec cert.host nm spec (cert.bound nm) nX) (bsMem : List UInt8) (args : Tup Val as)
    (v : Val t) (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs as).isSome = true)
    {Q : Post [t]} (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.RetsIn (bs := [t]) (v, ()) (T.mach.data st))
      (T.mach.mkState (I.initState (cert.bound nm) bsMem args) (T.mach.labelAddr cert.host nm)) :=
  I.run_ret1_of cert.host cert.bound maxBound cert.bound_le_max hf bsMem args v hbs hargs hspec hQ
    hbound
theorem run_ret1_i64 (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs)
    (I : TargetInit T maxStack maxMem) {nm : Sym} {as : List Ty} {spec : Spec as [i64]}
    (hf : T.FnSpec cert.host nm spec (cert.bound nm) nX) (bsMem : List UInt8) (args : Tup Val as)
    (v : Val i64) (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs as).isSome = true)
    {Q : Post [i64]} (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v)
      (T.mach.mkState (I.initState (cert.bound nm) bsMem args) (T.mach.labelAddr cert.host nm)) :=
  I.run_ret1_i64_of cert.host cert.bound maxBound cert.bound_le_max hf bsMem args v hbs hargs hspec
    hQ hbound
/-- Closed end-to-end `Eventually` theorem from `cert.sem` to `cert.host` execution for any
non-exiting `i64`-returning function `f ∈ mod.fns` (`ext₀ = []`, `extSigs = []`). -/
theorem eventually_ret1_i64_of_le
    (cert : LinkedCertScc T L lt hcl mod [] exits nX maxBound [])
    (I : TargetInit T maxStack maxMem) (hwf : ∀ f ∈ mod.fns, f.Wf)
    {f : Fn} (hf : f ∈ mod.fns) (hret : f.rs = [i64])
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs) (spec : Spec f.as [i64])
    (hnoex : ∀ args m Q X X', spec args m Q X → spec args m Q X')
    (hle : ∀ args m Q X, spec args m Q X →
      cert.sem (fun _ _ _ _ _ _ _ => False) f.name f.as [i64] args m Q X)
    (bsMem : List UInt8) (args : Tup Val f.as) (v : Val i64)
    (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs f.as).isSome = true)
    {Q : Post [i64]} (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ())) (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v)
      (T.mach.mkState (I.initState (cert.bound f.name) bsMem args)
        (T.mach.labelAddr cert.host f.name)) := by
  have hsrc := fnSpec_of_legalEnv_onlyFn has hrs (cert.fnSpec_host hwf hf).2; rw [hret] at hsrc
  exact cert.run_ret1_i64 I
    (Target.FnSpec.of_spec T hsrc fun args m Q X hs => hle args m Q _ (hnoex args m Q X _ hs))
    bsMem args v hbs hargs hspec hQ hbound

end ConcreteInit

end LinkedCertScc

/-! ## 3. Mixed Acyclic + Cyclic-SCC Meta Evaluator & `compile_linked_scc!` -/

meta section

open Lean Elab Command Meta

/-- Per-leaf slice data inside either `.recSCC` or `.recBudgetSCC`. -/
structure EvalSccLeaf where
  startIdx : Nat
  fnCount : Nat
  isModuleLast : Bool
  hintsLit : Lean.Expr
  codeLit : Lean.Expr
  baseLit : Lean.Expr
  stepLit : Lean.Expr
  deriving Inhabited

/-- Evaluated chunk data for `compile_linked_scc!` and `compile_linked_budget_scc!`. -/
inductive EvalSccChunk where
  | acyc (startIdx fnCount : Nat) (isModuleLast : Bool)
      (extLit hintsLit codeLit boundsLit : Lean.Expr)
  | recSCC (extLit recSigsLit : Lean.Expr) (fuel : Nat) (subchunks : List EvalSccLeaf)
  | recBudgetSCC (extLit recSigsLit : Lean.Expr) (subchunks : List EvalSccLeaf)
  deriving Inhabited

/-- Complete meta evaluation output for `compile_linked_scc!` / `compile_linked_budget_scc!`. -/
structure EvalSccModuleData where
  chunks : List EvalSccChunk
  finalExtLit : Lean.Expr
  deriving Inhabited

private structure SccItem (I : Isa) where
  name : Sym
  srcSig : SigEntry
  legalSig : SigEntry
  hint : I.Hints
  code : List I.Directive
  ext : Rega.Ext
  callees : List SigEntry
  exitsOk : Bool
  budgetBounds? : Option (Nat × Nat) := none

private def SccItem.callsOk {I : Isa} (it : SccItem I) (allowed : List SigEntry) : Bool :=
  it.exitsOk && it.callees.all (fun s => allowed.any (SigEntry.beq s))

private def lookupFuelOpt {I : Isa} (fuels : List (Sym × Nat)) (defaultFuel : Nat)
    (items : List (SccItem I)) : Nat :=
  (items.findSome? fun it =>
    fuels.findSome? fun p => if p.1 == it.name then some p.2 else none).getD defaultFuel

private def closedPrefixLen {I : Isa} (availSigs : List SigEntry)
    (rest : List (SccItem I)) : Nat :=
  let rec lastCalleeIdx (cals : List SigEntry) : Nat → List (SccItem I) → Nat → Nat
    | _, [], best => best
    | idx, it :: ys, best =>
        lastCalleeIdx cals (idx + 1) ys
          (if cals.any (SigEntry.beq it.srcSig) then idx + 1 else best)
  let rec expand : Nat → Nat → Nat
    | 0, k => k
    | fuel + 1, k =>
        let pref := rest.take k
        let allowed := availSigs ++ pref.map (·.srcSig)
        let missing := pref.foldr (fun it acc =>
          (it.callees.filter fun c => !allowed.any (SigEntry.beq c)) ++ acc) []
        if missing.isEmpty then k
        else
          let need := lastCalleeIdx missing 0 rest k
          if need <= k then k else expand fuel need
  expand (rest.length + 1) 1

private def evalRecItems (I : Isa) (raBytes : Nat) (recSigs : List SigEntry)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat) (isBudget : Bool) :
    List (SccItem I) → Except String (List (SccItem I × Nat × Nat))
  | [] => .ok []
  | it :: rest => do
    let bsf ←
      if !isBudget then
        match LinkRec.checkAndBoundRecExt I raBytes recSigs extCallees exits nX it.hint it.ext with
        | some p => .ok p
        | none => .error s!"{it.name}: unknown callee or undeclared exit"
      else
        match it.budgetBounds? with
        | none => .error s!"{it.name}: missing BudgetFn metadata"
        | some (maxFrame, minEntry) =>
          let bfn : BudgetFn :=
            { toFn := ⟨it.name, [], [], fun _ _ _ => .hlt⟩, maxFrame, minEntry }
          if checkAndBoundBudgetRecExt I raBytes recSigs extCallees exits nX it.hint it.ext bfn then
            .ok (0, 0)
          else
            let fb := Rega.effFrame I it.hint it.ext + raBytes
            if !Nat.ble fb maxFrame then
              .error s!"{it.name}: compiled effFrame+raBytes ({fb}) > maxFrame ({maxFrame})"
            else .error s!"{it.name}: callee/exit budget exceeds minEntry ({minEntry}) or unknown"
    .ok ((it, bsf) :: (← evalRecItems I raBytes recSigs extCallees exits nX isBudget rest))

private def splitRecSubchunks {I : Isa} (k maxDirs startIdx : Nat) (isEndAfter : Bool)
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)]
    (xs : List (SccItem I × Nat × Nat)) : List EvalSccLeaf × Nat × Nat :=
  let rec go : Nat → Nat → Nat → Nat → List (SccItem I × Nat × Nat) →
      List EvalSccLeaf → List EvalSccLeaf × Nat × Nat
    | 0, _, maxB, maxS, _, out | _, _, maxB, maxS, [], out => (out.reverse, maxB, maxS)
    | fuel + 1, idx, maxB, maxS, first :: rest, out =>
        let (grp, rest') := takeDirBounded k maxDirs (·.1.code.length) first rest
        let bf := grp.foldr (fun x m => Nat.max x.2.1 m) 0
        let sf := grp.foldr (fun x m => Nat.max x.2.2 m) 0
        let leaf : EvalSccLeaf := {
          startIdx := idx, fnCount := grp.length, isModuleLast := isEndAfter && rest'.isEmpty
          hintsLit := Lean.toExpr (grp.map (·.1.hint))
          codeLit := Lean.toExpr (grp.foldr (fun x cs => x.1.code ++ cs) [])
          baseLit := Lean.toExpr bf, stepLit := Lean.toExpr sf }
        go fuel (idx + grp.length) (Nat.max maxB bf) (Nat.max maxS sf) rest' (leaf :: out)
  go (xs.length + 1) startIdx 0 0 xs []

private def evalSccItemsCore (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (extSigs0 : List SigEntry) (exits : List Sym) (nX : Nat)
    (entries : List (Fn × Option (Nat × Nat))) (chunkSize defaultFuel maxBound maxDirs : Nat)
    (fuels : List (Sym × Nat)) (budgetExports? : Option (List (Sym × Nat)))
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] :
    Except String EvalSccModuleData := do
  let k := Nat.max chunkSize 1
  if entries.isEmpty then
    let (code, bounds) ← compileModule I lt raBytes ext0 exits nX [] []
    let extLit := Lean.toExpr ext0
    pure {
      chunks := [.acyc 0 0 true extLit (Lean.toExpr ([] : List I.Hints))
        (Lean.toExpr code) (Lean.toExpr bounds)]
      finalExtLit := extLit }
  else
    let allItems ← spawnLowerItems I lt entries Prod.fst fun nm h c mf ext (f, bb?) =>
      let cals := f.callees
      SccItem.mk nm f.sig mf.sig h c ext cals (f.checkCallsOk cals exits) bb?
    let emitAcyc (isLast : Bool) (startIdx : Nat) (chunkExt0 : List (SigEntry × Nat))
        (revGrp : List (SccItem I × Nat)) : EvalSccChunk :=
      let grp := revGrp.reverse
      .acyc startIdx grp.length isLast (Lean.toExpr chunkExt0) (Lean.toExpr (grp.map (·.1.hint)))
        (Lean.toExpr (grp.foldr (fun x cs => x.1.code ++ cs) []))
        (Lean.toExpr (grp.map fun x => (x.1.name, x.2)))
    let rec walk (fuel idx : Nat) (availSigs : List SigEntry)
        (chunkExt0 acc : List (SigEntry × Nat)) (acycStart acycDirs : Nat)
        (acycAcc : List (SccItem I × Nat)) (rest : List (SccItem I))
        (out : List EvalSccChunk) : Except String EvalSccModuleData :=
      let flush (isLast : Bool) :=
        if acycAcc.isEmpty then out else emitAcyc isLast acycStart chunkExt0 acycAcc :: out
      match fuel, rest with
      | 0, _ | _, [] => .ok { chunks := (flush true).reverse, finalExtLit := Lean.toExpr acc }
      | fuel' + 1, it :: tl =>
        if it.callsOk availSigs then
          let nextDirs := acycDirs + it.code.length
          if !acycAcc.isEmpty && (acycAcc.length >= k || (maxDirs > 0 && nextDirs > maxDirs)) then
            walk fuel' idx availSigs acc acc idx 0 [] rest (flush false)
          else do
            let b ← evalOneFnBoundCheck I raBytes exits nX maxBound acc it.name it.hint it.ext
            let acycAcc' := (it, b) :: acycAcc; let acc' := (it.legalSig, b) :: acc
            let avail' := it.srcSig :: availSigs
            if tl.isEmpty then
              .ok {
                chunks := (emitAcyc true acycStart chunkExt0 acycAcc' :: out).reverse
                finalExtLit := Lean.toExpr acc' }
            else walk fuel' (idx + 1) avail' chunkExt0 acc' acycStart nextDirs acycAcc' tl out
        else
          let out1 := flush false; let len := closedPrefixLen availSigs rest
          let sccItems := rest.take len; let tl' := rest.drop len
          let sccSrcSigs := sccItems.map (·.srcSig)
          if let some bad := sccItems.find? fun x => !x.callsOk (availSigs ++ sccSrcSigs) then
            .error s!"{bad.name}: unknown callee or undeclared exit"
          else if let some hit := sccItems.find? fun x => acc.any (·.1.1 == x.name) then
            .error s!"{hit.name}: function name collides with external callee"
          else do
            let recSigs := sccItems.map (·.legalSig)
            let bounded ← evalRecItems I raBytes recSigs acc exits nX budgetExports?.isSome sccItems
            let (leaves, baseB, stepB) := splitRecSubchunks k maxDirs idx tl'.isEmpty bounded
            let (sccCh, sccSigs) ← match budgetExports? with
              | none =>
                let sccFuel := lookupFuelOpt fuels defaultFuel sccItems
                let totB := baseB + sccFuel * stepB
                if !Nat.ble totB maxBound || !Nat.ble maxBound (2 ^ 64) ||
                    !Nat.ble (totB + raBytes) (2 ^ 64) then
                  .error s!"recSCC({it.name}): bound {totB} > {maxBound}"
                else .ok (.recSCC (Lean.toExpr acc) (Lean.toExpr recSigs) sccFuel leaves,
                    recSigs.map (·, totB))
              | some expB =>
                if !Nat.ble maxBound (2 ^ 64) || !Nat.ble (maxBound + raBytes) (2 ^ 64) ||
                    !expB.all (fun p => Nat.ble p.2 maxBound) then
                  .error s!"recBudgetSCC({it.name}): exportBounds/maxBound overflow"
                else .ok (.recBudgetSCC (Lean.toExpr acc) (Lean.toExpr recSigs) leaves,
                    recSigs.map fun s => (s, budgetBound expB maxBound s.1))
            let acc2 := sccSigs.reverse ++ acc
            walk fuel' (idx + len) (sccSrcSigs ++ availSigs) acc2 acc2 (idx + len) 0 [] tl'
              (sccCh :: out1)
    walk (allItems.length * 2 + 4) 0 extSigs0 ext0 ext0 0 0 [] allItems []

def evalLinkedSccChunks (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (extSigs0 : List SigEntry) (exits : List Sym) (nX : Nat)
    (fs : List Fn) (chunkSize defaultFuel maxBound maxDirs : Nat) (fuels : List (Sym × Nat))
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] :
    Except String EvalSccModuleData :=
  evalSccItemsCore I lt raBytes ext0 extSigs0 exits nX
    (fs.map (·, none)) chunkSize defaultFuel maxBound maxDirs fuels none

def evalLinkedBudgetSccChunks (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (extSigs0 : List SigEntry) (exits : List Sym) (nX : Nat)
    (bfs : List BudgetFn) (chunkSize maxBound maxDirs : Nat) (exportBounds : List (Sym × Nat) := [])
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] :
    Except String EvalSccModuleData :=
  evalSccItemsCore I lt raBytes ext0 extSigs0 exits nX
    (bfs.map fun b => (b.toFn, some (b.maxFrame, b.minEntry))) chunkSize 0 maxBound maxDirs []
    (some exportBounds)

structure CertSccOptions where
  maxBT? : Option Term := none
  exportBoundsT? : Option Term := none
  extT? : Option Term := none
  extSigsT? : Option Term := none
  exitsT? : Option Term := none
  nXT? : Option Term := none
  fuelT? : Option Term := none
  fuelsT? : Option Term := none
  maxDirsT? : Option Term := none
  compileT? : Option Term := none
  compileExtT? : Option Term := none
  deriving Inhabited

structure CertSccInputs where
  base : CertBaseEnv
  modE : Lean.Expr
  bfsBaseE? : Option Lean.Expr
  extSigsE : Lean.Expr
  exportBoundsE : Lean.Expr
  chunks : List EvalSccChunk
  finalExtLit : Lean.Expr

def parseCertSccOptions (optKeys : TSyntaxArray `ident) (optVals : TSyntaxArray `term) :
    CommandElabM CertSccOptions :=
  parseKvOptions "compile_linked_scc!"
    "maxBound, exportBounds, ext, extSigs, exits, nX, fuel, fuels, maxDirs, compile, compileExt" {}
    (fun opts k v => pure <| match k with
      | `maxBound => some { opts with maxBT? := some v }
      | `exportBounds => some { opts with exportBoundsT? := some v }
      | `ext => some { opts with extT? := some v }
      | `extSigs => some { opts with extSigsT? := some v }
      | `exits => some { opts with exitsT? := some v }
      | `nX => some { opts with nXT? := some v }
      | `fuel => some { opts with fuelT? := some v }
      | `fuels => some { opts with fuelsT? := some v }
      | `maxDirs => some { opts with maxDirsT? := some v }
      | `compile => some { opts with compileT? := some v }
      | `compileExt => some { opts with compileExtT? := some v }
      | _ => none) optKeys optVals

def elabAndEvalSccChunks (targT layoutT ltT clT modT : Term) (chunkSize : Nat)
    (opts : CertSccOptions) (isBudget : Bool := false) : TermElabM CertSccInputs := do
  if !isBudget && opts.exportBoundsT?.isSome then
    throwError "compile_linked_scc!: exportBounds only valid in compile_linked_budget_scc!"
  let b ← elabCertBase targT layoutT ltT clT {
    maxBT? := opts.maxBT?, extT? := opts.extT?, exitsT? := opts.exitsT?, nXT? := opts.nXT?,
    maxDirsT? := opts.maxDirsT?, compileT? := opts.compileT?, compileExtT? := opts.compileExtT? }
  let tys := mkCertTypes
  let (modE, bfsBaseE?) ←
    if isBudget then
      let bModE ← Term.elabTerm modT (some (Lean.mkConst ``LeanQbe.T.BudgetModule))
      pure (mkApp (Lean.mkConst ``LeanQbe.T.BudgetModule.toModule) bModE,
        some (mkApp (Lean.mkConst ``LeanQbe.T.BudgetModule.fns) bModE))
    else pure (← Term.elabTerm modT (some (Lean.mkConst ``LeanQbe.T.Module)), none)
  let extSigsE ← elabOptTerm opts.extSigsT? tys.listSigTy
    (mkApp4 (Lean.mkConst ``List.map [.zero, .zero]) (Lean.mkConst ``LeanQbe.T.Extern) tys.sigTy
      (Lean.mkConst ``LeanQbe.T.Extern.sig) (mkApp (Lean.mkConst ``LeanQbe.T.Module.externs) modE))
  let nilSymNat := mkApp (Lean.mkConst ``List.nil [.zero]) tys.symNatTy
  let fuelE ← elabOptTerm opts.fuelT? tys.natTy (mkNatLit 16)
  let fuelsE ← elabOptTerm opts.fuelsT? tys.listBoundsTy nilSymNat
  let exportBoundsE ← elabOptTerm opts.exportBoundsT? tys.listBoundsTy nilSymNat
  Term.synthesizeSyntheticMVarsNoPostponing
  let modE ← instantiateMVars modE; let bfsBaseE? ← bfsBaseE?.mapM instantiateMVars
  let extSigsE ← instantiateMVars extSigsE; let fuelE ← instantiateMVars fuelE
  let fuelsE ← instantiateMVars fuelsE; let exportBoundsE ← instantiateMVars exportBoundsE
  let callE ← instantiateMVars <| match bfsBaseE? with
    | some bfsE => mkAppN (Lean.mkConst ``LeanQbe.T.evalLinkedBudgetSccChunks)
        #[b.isaE, b.ltE, b.raE, b.ext0E, extSigsE, b.exitsE, b.nXE, bfsE, mkNatLit chunkSize,
          b.maxBE, b.maxDirsE, exportBoundsE, b.toExprHintsInst, b.toExprDirInst]
    | none => mkAppN (Lean.mkConst ``LeanQbe.T.evalLinkedSccChunks)
        #[b.isaE, b.ltE, b.raE, b.ext0E, extSigsE, b.exitsE, b.nXE,
          mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) modE, mkNatLit chunkSize,
          fuelE, b.maxBE, b.maxDirsE, fuelsE, b.toExprHintsInst, b.toExprDirInst]
  let outTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String)
    (Lean.mkConst ``LeanQbe.T.EvalSccModuleData)
  let cmdNm := if isBudget then "compile_linked_budget_scc!" else "compile_linked_scc!"
  match (← unsafe evalExpr (Except String EvalSccModuleData) outTy callE) with
  | .error e => throwError "{cmdNm}: {e}"
  | .ok md => return {
      base := b, modE, bfsBaseE?, extSigsE, exportBoundsE,
      chunks := md.chunks, finalExtLit := md.finalExtLit }

private structure EmittedLeafNames where
  leaf : EvalSccLeaf
  fnsNm : Name
  hintsNm : Name
  codeNm : Name
  baseNm : Name
  stepNm : Name
  cmAuxNm : Name
  subNm : Name
  resPair : Lean.Expr
  deriving Inhabited

private inductive EmittedChunkMeta where
  | acyc (ac : AcycChunkNames)
  | recAny (isBudget : Bool) (extNm recSigsNm scsNm chkNm chunkNm : Name)
      (fuel? : Option Nat) (leaves : Array EmittedLeafNames)
  deriving Inhabited

private def elabCompileLinkedScc (isBudget : Bool) (certId : Ident)
    (targT layoutT ltT clT modT : Term) (chunkSize : Nat)
    (optKeys : TSyntaxArray `ident) (optVals : TSyntaxArray `term) : CommandElabM Unit := do
  let ns ← getCurrNamespace; let certNm := ns ++ certId.getId; let auxNs := certNm ++ `aux
  let opts ← parseCertSccOptions optKeys optVals
  let inp ← liftTermElabM <|
    elabAndEvalSccChunks targT layoutT ltT clT modT chunkSize opts isBudget
  let b := inp.base; let tys := mkCertTypes; let bfnTy := Lean.mkConst ``LeanQbe.T.BudgetFn
  let recTripleTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) b.listDirTy tys.pairNatTy
  let recExcTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String) recTripleTy
  let budgetExcTy :=
    mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String) b.listDirTy
  let fnsBaseE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) inp.modE
  let emitLeaves (pfx : String) (hasBounds : Bool) (leaves : List EvalSccLeaf) :
      CommandElabM (Array EmittedLeafNames) := do
    let (elemTy, baseListE) :=
      if hasBounds then (tys.fnTy, fnsBaseE) else (bfnTy, inp.bfsBaseE?.get!)
    let listElemTy := mkApp (Lean.mkConst ``List [1]) elemTy
    let mut leafArr : Array EmittedLeafNames := #[]; let mut sj : Nat := 0
    for lf in leaves do
      let nm := fun s => auxNs ++ Name.mkSimple s!"{pfx}_s{sj}_{s}"
      let fnsNm := nm "fns"; let hintsNm := nm "hints"; let codeNm := nm "code"
      let baseNm := nm "base"; let stepNm := nm "step"
      let sliceE := mkSliceExpr elemTy baseListE lf.startIdx lf.fnCount lf.isModuleLast
      liftCoreM do
        addCertDef fnsNm listElemTy sliceE b.compileCert
        addCertDef hintsNm b.listHintsTy lf.hintsLit b.compileCert
        addCertDef codeNm b.listDirTy lf.codeLit b.compileCert
        if hasBounds then
          addCertDef baseNm tys.natTy lf.baseLit b.compileCert
          addCertDef stepNm tys.natTy lf.stepLit b.compileCert
      let resPair := if hasBounds then
        mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) b.listDirTy tys.pairNatTy
          (Lean.mkConst codeNm) (mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) tys.natTy
            tys.natTy (Lean.mkConst baseNm) (Lean.mkConst stepNm))
        else Lean.mkConst codeNm
      leafArr := leafArr.push {
        leaf := lf, fnsNm, hintsNm, codeNm, baseNm, stepNm,
        cmAuxNm := nm "cm", subNm := nm "sub", resPair }
      sj := sj + 1
    return leafArr
  let emitRec (pfx : String) (isB : Bool) (extLit recSigsLit : Lean.Expr) (fuel? : Option Nat)
      (leaves : List EvalSccLeaf) : CommandElabM EmittedChunkMeta := do
    let nm := fun s => auxNs ++ Name.mkSimple s!"{pfx}_{s}"
    let extNm := nm "ext"; let recSigsNm := nm "recsigs"
    liftCoreM do
      addCertDef extNm tys.listExtTy extLit b.compileCert
      addCertDef recSigsNm tys.listSigTy recSigsLit b.compileCert
    return .recAny isB extNm recSigsNm (nm "scs") (nm "chk") (nm "chunk")
      fuel? (← emitLeaves pfx (!isB) leaves)
  -- Pass 1: emit pure literal definitions for all chunks and sub-chunks.
  let mut emitted : Array EmittedChunkMeta := #[]; let mut ci : Nat := 0
  for ch in inp.chunks do
    let pfx := s!"c{ci}"
    emitted := emitted.push <| ← match ch with
      | .acyc startIdx fnCount isLast extLit hintsLit codeLit boundsLit =>
        .acyc <$> emitAcycChunkDefs auxNs pfx b.compileCert fnsBaseE b.listHintsTy b.listDirTy
          ⟨startIdx, fnCount, isLast, extLit, hintsLit, codeLit, boundsLit⟩
      | .recSCC extLit recSigsLit fuel leaves =>
        emitRec pfx false extLit recSigsLit (some fuel) leaves
      | .recBudgetSCC extLit recSigsLit leaves =>
        emitRec pfx true extLit recSigsLit none leaves
    ci := ci + 1
  -- Pass 2: queue all per-chunk and per-subchunk kernel theorems in parallel.
  let addBoolEq (nm : Name) (lhs : Lean.Expr) :=
    liftCoreM <| addKernelEqThm nm (Lean.mkConst ``Bool) lhs (Lean.mkConst ``Bool.true) .zero
  for em in emitted do
    match em with
    | .acyc ac => liftCoreM <| emitAcycChunkThms b ac
    | .recAny isB extNm recSigsNm _ _ _ _ leaves =>
      let (fnConst, resTy, excTy) := if isB
        then (``LeanQbe.T.compileModuleBudgetRecAuxSupp, b.listDirTy, budgetExcTy)
        else (``LeanQbe.T.compileModuleRecAuxSupp, recTripleTy, recExcTy)
      for lfn in leaves do
        let cmLhs := mkAppN (Lean.mkConst fnConst) #[b.isaE, b.ltE, b.raE, Lean.mkConst recSigsNm,
          Lean.mkConst extNm, b.exitsE, b.nXE, Lean.mkConst lfn.fnsNm, Lean.mkConst lfn.hintsNm]
        let cmRhs := mkApp3 (Lean.mkConst ``Except.ok [.zero, .zero])
          (Lean.mkConst ``String) resTy lfn.resPair
        liftCoreM <| addKernelEqThm lfn.cmAuxNm excTy cmLhs cmRhs .zero
  -- Pass 3: assemble `.acyc`, `.recSCC`, and `.recBudgetSCC` `Chunk` entries & checks.
  let chunkTy := mkAppN (Lean.mkConst ``LeanQbe.T.Chunk) #[b.targE, b.ltE, b.exitsE, b.nXE]
  let mut chunkEntries : Array Lean.Expr := #[]
  for em in emitted do
    match em with
    | .acyc ac =>
      let ccVal ← liftCoreM <| emitAcycCompiledChunk b ac
      chunkEntries := chunkEntries.push
        (mkAppN (Lean.mkConst ``LeanQbe.T.Chunk.acyc) #[b.targE, b.ltE, b.exitsE, b.nXE, ccVal])
    | .recAny isB extNm recSigsNm scsNm chkNm chunkNm fuel? leaves =>
      let (subC, auxEqC, subMkC, chkC, ofSubC, extraArg) := if isB then
        (``LeanQbe.T.RecBudgetSubChunk, ``LeanQbe.T.compileModuleBudgetRecAux_of_supp,
         ``LeanQbe.T.RecBudgetSubChunk.mk, ``LeanQbe.T.checkRecBudgetSubchunks,
         ``LeanQbe.T.Chunk.ofBudgetRecSubchunks, inp.exportBoundsE)
      else (``LeanQbe.T.RecSubChunk, ``LeanQbe.T.compileModuleRecAux_of_supp,
         ``LeanQbe.T.RecSubChunk.mk, ``LeanQbe.T.checkRecSubchunks,
         ``LeanQbe.T.Chunk.ofRecSubchunks, mkNatLit fuel?.get!)
      let subTy := mkAppN (Lean.mkConst subC)
        #[b.targE, b.ltE, Lean.mkConst recSigsNm, Lean.mkConst extNm, b.exitsE, b.nXE]
      let mut subConsts : List Lean.Expr := []
      for lfn in leaves do
        let auxEq := mkAppN (Lean.mkConst auxEqC)
          #[b.isaE, b.ltE, b.raE, Lean.mkConst recSigsNm, Lean.mkConst extNm, b.exitsE, b.nXE,
            Lean.mkConst lfn.fnsNm, Lean.mkConst lfn.hintsNm, lfn.resPair, Lean.mkConst lfn.cmAuxNm]
        let baseArgs := #[b.targE, b.ltE, Lean.mkConst recSigsNm, Lean.mkConst extNm, b.exitsE,
          b.nXE, Lean.mkConst lfn.fnsNm, Lean.mkConst lfn.hintsNm, Lean.mkConst lfn.codeNm]
        let subVal := mkAppN (Lean.mkConst subMkC) (if isB then baseArgs.push auxEq
          else baseArgs ++ #[Lean.mkConst lfn.baseNm, Lean.mkConst lfn.stepNm, auxEq])
        liftCoreM <| addCertDef lfn.subNm subTy subVal b.compileCert
        subConsts := subConsts ++ [Lean.mkConst lfn.subNm]
      let tailPair := if isB then #[b.maxBE, extraArg] else #[extraArg, b.maxBE]
      liftCoreM <| addCertDef scsNm (mkApp (Lean.mkConst ``List [1]) subTy)
        (mkExprList 1 subTy subConsts) b.compileCert
      addBoolEq chkNm (mkAppN (Lean.mkConst chkC) (#[b.targE, b.layoutE, b.ltE,
        Lean.mkConst recSigsNm, Lean.mkConst extNm, b.exitsE, b.nXE] ++ tailPair ++
        #[Lean.mkConst scsNm]))
      liftCoreM <| addCertDef chunkNm chunkTy (mkAppN (Lean.mkConst ofSubC)
        (#[b.targE, b.ltE, b.exitsE, b.nXE, b.layoutE, b.clE, Lean.mkConst recSigsNm,
          Lean.mkConst extNm] ++ tailPair ++ #[Lean.mkConst scsNm, Lean.mkConst chkNm]))
        b.compileCert
      chunkEntries := chunkEntries.push (Lean.mkConst chunkNm)
  let chunksNm := auxNs ++ `chunks
  let linkCheckNm := auxNs ++ `link_check; let callsCheckNm := auxNs ++ `calls_check
  liftCoreM <| addCertDef chunksNm (mkApp (Lean.mkConst ``List [1]) chunkTy)
    (mkExprList 1 chunkTy chunkEntries.toList) b.compileCert
  addBoolEq linkCheckNm (mkAppN (Lean.mkConst ``LeanQbe.T.checkLinkSccList)
    #[b.targE, b.layoutE, b.ltE, b.exitsE, b.nXE, b.ext0E, Lean.mkConst chunksNm])
  addBoolEq callsCheckNm (mkAppN (Lean.mkConst ``LeanQbe.T.checkChunksCalls)
    #[b.targE, b.ltE, b.nXE, b.exitsE, inp.extSigsE, Lean.mkConst chunksNm])
  -- Pass 4: build O(#subchunks) proofs of `fns_eq`, `supportsAll`, and `maxBound_le`.
  let fnsEqNm := auxNs ++ `fns_eq; let suppAllNm := auxNs ++ `supportsAll
  let maxBLeNm := auxNs ++ `maxBound_le
  let sccChunksFnsE := mkAppN (Lean.mkConst ``LeanQbe.T.sccChunksFns)
    #[b.targE, b.ltE, b.exitsE, b.nXE, Lean.mkConst chunksNm]
  let mut fnsEqProof : Lean.Expr := default
  let mut restFnsE := mkApp (Lean.mkConst ``List.nil [1]) tys.fnTy
  let mut suppProof := mkApp (Lean.mkConst ``LeanQbe.T.supportsAll_nil) b.ltE
  let mut maxBProof := mkAppN (Lean.mkConst ``LeanQbe.T.sccChunksMaxBound_nil)
    #[b.targE, b.ltE, b.exitsE, b.nXE, b.maxBE]
  let mut restChunksE := mkApp (Lean.mkConst ``List.nil [1]) chunkTy
  let nChunks := emitted.size
  for revIdx in [:nChunks] do
    let i := nChunks - 1 - revIdx
    let em := emitted[i]!; let chunkVal := chunkEntries[i]!
    match em with
    | .acyc ac =>
      let curFnsE := Lean.mkConst ac.fnsNm
      fnsEqProof := if revIdx == 0 then
        mkApp3 (Lean.mkConst ``LeanQbe.T.slice_last_eq [1]) tys.fnTy fnsBaseE (mkNatLit ac.startIdx)
      else mkApp6 (Lean.mkConst ``LeanQbe.T.slice_cons_eq [1])
        tys.fnTy fnsBaseE restFnsE (mkNatLit ac.startIdx) (mkNatLit ac.fnCount) fnsEqProof
      let acycSupp := mkAppN (Lean.mkConst ``LeanQbe.T.Compiled.supportsSource)
        #[b.targE, b.ltE, Lean.mkConst ac.extNm, b.exitsE, b.nXE,
          curFnsE, Lean.mkConst ac.hintsNm, b.maxBE, Lean.mkConst ac.compNm]
      suppProof := mkApp5 (Lean.mkConst ``LeanQbe.T.supportsAll_append_pred)
        b.ltE curFnsE restFnsE acycSupp suppProof
      restFnsE := mkApp3 (Lean.mkConst ``List.append [1]) tys.fnTy curFnsE restFnsE
    | .recAny isB extNm recSigsNm _ _ chunkNm _ leaves =>
      let tailFnsE := restFnsE; let elemTy := if isB then bfnTy else tys.fnTy
      let (baseE, nilSuppC, appSuppC, leafSuppC) := if isB then
        (inp.bfsBaseE?.get!, ``LeanQbe.T.supportsAll_budget_nil,
         ``LeanQbe.T.supportsAll_budget_append,
         ``LeanQbe.T.supportsAll_of_compileModuleBudgetRecAuxSupp)
      else (fnsBaseE, ``LeanQbe.T.supportsAll_nil,
         ``LeanQbe.T.supportsAll_append_pred, ``LeanQbe.T.supportsAll_of_compileModuleRecAuxSupp)
      let mut curItemsE := mkApp (Lean.mkConst ``List.nil [1]) elemTy
      let mut curSupp := mkApp (Lean.mkConst nilSuppC) b.ltE
      let nLeaves := leaves.size
      for sRevIdx in [:nLeaves] do
        let lfn := leaves[nLeaves - 1 - sRevIdx]!
        let leafItemsE := Lean.mkConst lfn.fnsNm
        let sE := mkNatLit lfn.leaf.startIdx; let kE := mkNatLit lfn.leaf.fnCount
        fnsEqProof := if sRevIdx == 0 then
          if revIdx == 0 then
            if isB then mkApp2 (Lean.mkConst ``LeanQbe.T.budgetFns_last_mod_eq) baseE sE
            else mkApp3 (Lean.mkConst ``LeanQbe.T.slice_sub_last_mod_eq [1]) tys.fnTy baseE sE
          else
            if isB then mkApp5 (Lean.mkConst ``LeanQbe.T.budgetFns_last_eq)
              baseE tailFnsE sE kE fnsEqProof
            else mkAppN (Lean.mkConst ``LeanQbe.T.slice_sub_last_eq [1])
              #[tys.fnTy, baseE, tailFnsE, sE, kE, fnsEqProof]
        else
          if isB then mkApp6 (Lean.mkConst ``LeanQbe.T.budgetFns_cons_eq)
            baseE curItemsE tailFnsE sE kE fnsEqProof
          else mkAppN (Lean.mkConst ``LeanQbe.T.slice_sub_cons_eq [1])
            #[tys.fnTy, baseE, curItemsE, tailFnsE, sE, kE, fnsEqProof]
        let leafSuppVal := mkAppN (Lean.mkConst leafSuppC)
          #[b.isaE, b.ltE, b.raE, Lean.mkConst recSigsNm, Lean.mkConst extNm,
            b.exitsE, b.nXE, leafItemsE, Lean.mkConst lfn.hintsNm,
            lfn.resPair, Lean.mkConst lfn.cmAuxNm]
        curSupp := mkApp5 (Lean.mkConst appSuppC) b.ltE leafItemsE curItemsE leafSuppVal curSupp
        curItemsE := mkApp3 (Lean.mkConst ``List.append [1]) elemTy leafItemsE curItemsE
      let scsSupp := if isB then
        mkApp3 (Lean.mkConst ``LeanQbe.T.supportsAll_budget_leaf) b.ltE curItemsE curSupp
      else curSupp
      let chunkFnsE := mkAppN (Lean.mkConst ``LeanQbe.T.Chunk.fns)
        #[b.targE, b.ltE, b.exitsE, b.nXE, Lean.mkConst chunkNm]
      suppProof := mkApp5 (Lean.mkConst ``LeanQbe.T.supportsAll_append_pred)
        b.ltE chunkFnsE tailFnsE scsSupp suppProof
      restFnsE := mkApp3 (Lean.mkConst ``List.append [1]) tys.fnTy chunkFnsE tailFnsE
    maxBProof := mkAppN (Lean.mkConst ``LeanQbe.T.sccChunksMaxBound_cons)
      #[b.targE, b.ltE, b.exitsE, b.nXE, b.maxBE, chunkVal, restChunksE,
        mkApp (Lean.mkConst ``Nat.le_refl) b.maxBE, maxBProof]
    restChunksE := mkApp3 (Lean.mkConst ``List.cons [1]) chunkTy chunkVal restChunksE
  liftCoreM <| addCertThm fnsEqNm
    (mkApp3 (Lean.mkConst ``Eq [2]) tys.listFnTy fnsBaseE sccChunksFnsE) fnsEqProof
  let (suppAllTy, suppAllVal, maxBLeProp) ← liftTermElabM do
    let sVal ← mkAppM ``LeanQbe.T.supportsAll_of_eq #[Lean.mkConst fnsEqNm, suppProof]
    let lhs := mkAppN (Lean.mkConst ``LeanQbe.T.sccChunksMaxBound)
      #[b.targE, b.ltE, b.exitsE, b.nXE, Lean.mkConst chunksNm]
    return (← instantiateMVars (← inferType sVal), ← instantiateMVars sVal,
      ← instantiateMVars (← mkAppM ``LE.le #[lhs, b.maxBE]))
  liftCoreM do
    addCertThm suppAllNm suppAllTy suppAllVal
    addCertThm maxBLeNm maxBLeProp maxBProof
    addCertDef certNm
      (mkAppN (Lean.mkConst ``LeanQbe.T.LinkedCertScc) #[b.targE, b.layoutE, b.ltE, b.clE,
        inp.modE, b.ext0E, b.exitsE, b.nXE, b.maxBE, inp.extSigsE])
      (mkAppN (Lean.mkConst ``LeanQbe.T.LinkedCertScc.mk)
        #[b.targE, b.layoutE, b.ltE, b.clE, inp.modE, b.ext0E, b.exitsE, b.nXE, b.maxBE,
          inp.extSigsE, Lean.mkConst chunksNm, Lean.mkConst linkCheckNm,
          Lean.mkConst callsCheckNm, Lean.mkConst fnsEqNm, Lean.mkConst suppAllNm,
          Lean.mkConst maxBLeNm]) b.compileCert
    addCertDef (certNm ++ `exportedExt) tys.listExtTy inp.finalExtLit b.compileExt

/-- `compile_linked_scc! certName target layout legalTarget labelClean mod chunkSize ...`
partitions `mod.fns` into `.acyc` spans and closed `.recSCC` SCC chunks. -/
scoped syntax "compile_linked_scc! " ident
    term:arg term:arg term:arg term:arg term:arg num
    ("(" ident " := " term ")")* : command

/-- `compile_linked_budget_scc! certName target layout legalTarget labelClean budgetMod chunkSize
...` partitions `budgetMod.fns` into `.acyc` spans and closed `.recBudgetSCC` SCC chunks. -/
scoped syntax "compile_linked_budget_scc! " ident
    term:arg term:arg term:arg term:arg term:arg num
    ("(" ident " := " term ")")* : command

scoped elab_rules : command
  | `(compile_linked_scc! $certId $targT $layoutT $ltT $clT $modT $chunkSizeLit
      $[($optKeys := $optVals)]*) =>
    elabCompileLinkedScc false certId targT layoutT ltT clT modT chunkSizeLit.getNat optKeys optVals
  | `(compile_linked_budget_scc! $certId $targT $layoutT $ltT $clT $modT $chunkSizeLit
      $[($optKeys := $optVals)]*) =>
    elabCompileLinkedScc true certId targT layoutT ltT clT modT chunkSizeLit.getNat optKeys optVals

end

end LeanQbe.T
