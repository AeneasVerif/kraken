module

public import LeanQbe.T.MainLinkScc
public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertProof
public import LeanQbe.T.MainCertElab
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Scc
import LeanQbe.T.MainFlatLemmas
import LeanQbe.T.RegaFlatLemmas
public meta import Lean
public meta import LeanQbe.T.MainLinkScc
public meta import LeanQbe.T.MainCertCore
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.MainCertFlatElab
public meta import LeanQbe.T.MainLinkSplice
public meta import LeanQbe.T.MainSplice
public meta import LeanQbe.T.Scc

/-!
# Mixed Acyclic + Cyclic Budget-SCC Compilation Certificates (`MainCertScc`)

Noncomputable-by-default certificate layer over `MainLinkScc`, `MainCertCore`, `MainCertProof`,
and `MainCertElab`:
* `LinkedCertScc`: closed whole-module certificate mixing `.acyc` and `.recBudgetSCC`.
* `compile_linked_budget_scc!`: parallel sub-chunked kernel checking.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

open Std Std.ExtHashMap
open LeanQbe.T.LinkRec

/-! ## 1. O(#subchunks) Slice, `supportsSource`, and `checkChunksCalls` Helpers -/

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

/-- First-order `TFlatFn` bundle mirroring `BudgetFn` without PHOAS closures. -/
structure FlatBudgetFn where
  toFlat : TFlatFn
  maxFrame : Nat
  minEntry : Nat := maxFrame

/-- Denotes a `FlatBudgetFn` back to a PHOAS `BudgetFn` (`toFlat.toFn`). -/
@[expose] def FlatBudgetFn.toBudgetFn (b : FlatBudgetFn) : BudgetFn :=
  ⟨b.toFlat.toFn, b.maxFrame, b.minEntry⟩

/-- First-order mirror of `compileModuleBudgetRecAuxSupp` executing `MainFlat` passes. -/
@[expose] def compileModuleBudgetRecAuxFlat (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (recSigs : List SigEntry) (extCallees : List (SigEntry × Nat))
    (exits : List Sym) (nX : Nat) :
    List FlatBudgetFn → List I.Hints → Except String (List I.Directive)
  | [], [] => .ok []
  | bf :: bfs, h :: hs =>
    let f := bf.toFlat
    if !f.wfCheck then .error s!"{f.name}: wfCheck failed"
    else
      let ef := earlyOptFlat f
      if ef.supportsSource lt then
        let mf := midStageFlat lt ef
        let ext := TFlat.ext mf.body
        let fakeBfn : BudgetFn :=
          { toFn := ⟨f.name, [], [], fun _ _ _ => .hlt⟩
            maxFrame := bf.maxFrame
            minEntry := bf.minEntry }
        match Rega.lowerFlatFn I h ext mf,
              checkAndBoundBudgetRecExt I raBytes recSigs extCallees exits nX h ext fakeBfn with
        | .ok c, true =>
          match compileModuleBudgetRecAuxFlat I lt raBytes recSigs extCallees exits nX bfs hs with
          | .ok cs => .ok (c ++ cs) | .error e => .error e
        | .error e, _ => .error s!"{f.name}: {e}"
        | _, false => .error s!"{f.name}: budget check failed"
      else .error s!"{f.name}: unsupported source op for target"
  | _, _ => .error "compileModuleBudgetRec: fn/hints length mismatch"

section FlatBridge
attribute [local irreducible] earlyOptFlat midStageFlat

private theorem compileModuleBudgetRecAuxSupp_of_flat (I : Isa) (lt : LegalTarget)
    (raBytes : Nat) (recSigs : List SigEntry) (extCallees : List (SigEntry × Nat))
    (exits : List Sym) (nX : Nat) :
    ∀ (fbfs : List FlatBudgetFn) (hs : List I.Hints) (code : List I.Directive),
      compileModuleBudgetRecAuxFlat I lt raBytes recSigs extCallees exits nX fbfs hs =
        .ok code →
      compileModuleBudgetRecAuxSupp I lt raBytes recSigs extCallees exits nX
        (fbfs.map FlatBudgetFn.toBudgetFn) hs = .ok code
  | [], [], _, h => h
  | [], _ :: _, _, h | _ :: _, [], _, h => by
      dsimp only [compileModuleBudgetRecAuxFlat] at h; cases h
  | bf :: fbfs, h :: hs, code, hok => by
      dsimp only [compileModuleBudgetRecAuxFlat] at hok
      cases hwf : bf.toFlat.wfCheck
      · simp only [hwf, Bool.not_false, ↓reduceIte] at hok; cases hok
      · simp only [hwf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        have heowf := earlyOptFlat_wfCheck bf.toFlat hwf
        have heoto := earlyOptFlat_toFn bf.toFlat hwf
        have hsupp_eq : (bf.toFlat.toFn.earlyOpt).body.supportsSource lt =
            (earlyOptFlat bf.toFlat).supportsSource lt := by
          rw [← heoto]; exact TFlatFn.supportsSource_eq lt (earlyOptFlat bf.toFlat) heowf
        cases hsup : (earlyOptFlat bf.toFlat).supportsSource lt
        · simp only [hsup, Bool.false_eq_true, ↓reduceIte] at hok; cases hok
        · simp only [hsup, ↓reduceIte] at hok
          have hmwf := midStageFlat_wfCheck lt (earlyOptFlat bf.toFlat) heowf
          have hmto := midStageFlat_toFn lt (earlyOptFlat bf.toFlat) heowf
          let ef := earlyOptFlat bf.toFlat
          let mf := midStageFlat lt ef
          have hext : TFlat.ext mf.body = Fn.ext (Fn.midFromEarly lt bf.toFlat.toFn.earlyOpt) := by
            rw [TFlat.ext_eq_fn_ext mf hmwf, hmto, heoto]
          have hlow : Rega.lowerFlatFn I h (TFlat.ext mf.body) mf =
              Rega.lowerFn I h (Fn.ext (Fn.midFromEarly lt bf.toFlat.toFn.earlyOpt))
                (Fn.midFromEarly lt bf.toFlat.toFn.earlyOpt) := by
            rw [hext]
            have h1 := Rega.lowerFlatFn_eq_lowerFn I h
              (Fn.ext (Fn.midFromEarly lt bf.toFlat.toFn.earlyOpt)) mf hmwf
            rwa [hmto, heoto] at h1
          have hchk : checkAndBoundBudgetRecExt I raBytes recSigs extCallees exits nX h
                (TFlat.ext mf.body) ⟨⟨bf.toFlat.name, [], [], fun _ _ _ => .hlt⟩,
                  bf.maxFrame, bf.minEntry⟩ =
              checkAndBoundBudgetRecExt I raBytes recSigs extCallees exits nX h
                (Fn.ext (Fn.midFromEarly lt bf.toFlat.toFn.earlyOpt))
                { toFn := bf.toFlat.toFn, maxFrame := bf.maxFrame, minEntry := bf.minEntry } := by
            rw [← hext]; rfl
          dsimp only [List.map, compileModuleBudgetRecAuxSupp]
          simp only [FlatBudgetFn.toBudgetFn, hsupp_eq, hsup, ↓reduceIte]
          rw [← hlow, ← hchk]
          split at hok
          · rename_i c _ hlowOk hcbOk
            split at hok
            · rename_i cs hrest
              rw [hlowOk, hcbOk]
              dsimp only
              have ih := compileModuleBudgetRecAuxSupp_of_flat I lt raBytes recSigs extCallees
                exits nX fbfs hs cs hrest
              rw [ih]; exact hok
            · simp at hok
          · cases hok
          · cases hok

theorem compileModuleBudgetRecAuxSupp_of_flat_eq {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {bfs : List BudgetFn} {fbfs : List FlatBudgetFn} {hs : List I.Hints}
    {code : List I.Directive}
    (hbfs : bfs = fbfs.map FlatBudgetFn.toBudgetFn)
    (hok : compileModuleBudgetRecAuxFlat I lt raBytes recSigs extCallees exits nX fbfs hs =
      .ok code) :
    compileModuleBudgetRecAuxSupp I lt raBytes recSigs extCallees exits nX bfs hs = .ok code := by
  subst hbfs
  exact compileModuleBudgetRecAuxSupp_of_flat I lt raBytes recSigs extCallees exits nX
    fbfs hs code hok

end FlatBridge

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

/-! ## 3. Mixed Acyclic + Cyclic Budget-SCC Meta Evaluator & `compile_linked_budget_scc!` -/

meta section

open Lean Elab Command Meta

/-- Per-leaf slice data inside `.recBudgetSCC`. -/
structure EvalSccLeaf where
  startIdx : Nat
  fnCount : Nat
  isModuleLast : Bool
  hintsLit : Lean.Expr
  codeLit : Lean.Expr
  deriving Inhabited

/-- Evaluated chunk data for `compile_linked_budget_scc!`. -/
inductive EvalSccChunk where
  | acyc (startIdx fnCount : Nat) (isModuleLast : Bool)
      (extLit hintsLit codeLit boundsLit : Lean.Expr)
  | recBudgetSCC (extLit recSigsLit : Lean.Expr) (subchunks : List EvalSccLeaf)
  deriving Inhabited

/-- Complete meta evaluation output for `compile_linked_budget_scc!`. -/
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
  budgetBounds : Nat × Nat

private def SccItem.callsOk {I : Isa} (it : SccItem I) (allowed : List SigEntry) : Bool :=
  it.exitsOk && it.callees.all (fun s => allowed.any (SigEntry.beq s))

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
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat) :
    List (SccItem I) → Except String Unit
  | [] => .ok ()
  | it :: rest => do
    let (maxFrame, minEntry) := it.budgetBounds
    let bfn : BudgetFn :=
      { toFn := ⟨it.name, [], [], fun _ _ _ => .hlt⟩, maxFrame, minEntry }
    if checkAndBoundBudgetRecExt I raBytes recSigs extCallees exits nX it.hint it.ext bfn then
      evalRecItems I raBytes recSigs extCallees exits nX rest
    else
      let fb := Rega.effFrame I it.hint it.ext + raBytes
      if !Nat.ble fb maxFrame then
        .error s!"{it.name}: compiled effFrame+raBytes ({fb}) > maxFrame ({maxFrame})"
      else .error s!"{it.name}: callee/exit budget exceeds minEntry ({minEntry}) or unknown"

private def splitRecSubchunks {I : Isa} (k maxDirs startIdx : Nat) (isEndAfter : Bool)
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)]
    (xs : List (SccItem I)) : List EvalSccLeaf :=
  let rec go : Nat → Nat → List (SccItem I) → List EvalSccLeaf → List EvalSccLeaf
    | 0, _, _, out | _, _, [], out => out.reverse
    | fuel + 1, idx, first :: rest, out =>
        let (grp, rest') := takeDirBounded k maxDirs (·.code.length) first rest
        let leaf : EvalSccLeaf := {
          startIdx := idx, fnCount := grp.length, isModuleLast := isEndAfter && rest'.isEmpty
          hintsLit := Lean.toExpr (grp.map (·.hint))
          codeLit := Lean.toExpr (grp.foldr (fun x cs => x.code ++ cs) []) }
        go fuel (idx + grp.length) rest' (leaf :: out)
  go (xs.length + 1) startIdx xs []

mutual
private def tflatCalleesAux {rs : List Ty} : TFlat rs → List SigEntry → List SigEntry
  | .let_ _ k, cs | .load _ _ k, cs | .store _ _ k, cs => tflatCalleesAux k cs
  | .call f (as := as) bs _ k, cs =>
      tflatCalleesAux k (addCalleeEntry (f, as, bs) cs)
  | .jnz _ t e, cs => tflatCalleesAux e (tflatCalleesAux t cs)
  | .jump _ _, cs | .ret _, cs | .exit _ _, cs | .hlt, cs => cs
  | .group bodies k, cs => tblocksCalleesAux bodies (tflatCalleesAux k cs)

private def tblocksCalleesAux {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → List SigEntry → List SigEntry
  | _, .nil, cs => cs
  | _, .cons b bs, cs => tblocksCalleesAux bs (tflatCalleesAux b cs)
end

mutual
private def tflatExitsOk (exits : List Sym) {rs : List Ty} : TFlat rs → Bool
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => tflatExitsOk exits k
  | .jnz _ t e => tflatExitsOk exits t && tflatExitsOk exits e
  | .jump _ _ | .ret _ | .hlt => true
  | .exit f _ => exits.any (· == f)
  | .group bodies k => tblocksExitsOk exits bodies && tflatExitsOk exits k

private def tblocksExitsOk (exits : List Sym) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => true
  | _, .cons b bs => tflatExitsOk exits b && tblocksExitsOk exits bs
end

private def evalSccEmpty (I : Isa) (ext0 : List (SigEntry × Nat))
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] : EvalSccModuleData :=
  let extLit := Lean.toExpr ext0
  { chunks := [.acyc 0 0 true extLit (Lean.toExpr ([] : List I.Hints))
      (Lean.toExpr ([] : List I.Directive)) (Lean.toExpr ([] : List (Sym × Nat)))]
    finalExtLit := extLit }

private def evalSccItemsFromList (I : Isa) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (extSigs0 : List SigEntry) (exits : List Sym) (nX : Nat)
    (chunkSize maxBound maxDirs : Nat) (exportBounds : List (Sym × Nat))
    (allItems : List (SccItem I))
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] :
    Except String EvalSccModuleData := do
  let k := Nat.max chunkSize 1
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
          let _ ← evalRecItems I raBytes recSigs acc exits nX sccItems
          let leaves := splitRecSubchunks k maxDirs idx tl'.isEmpty sccItems
          if !Nat.ble maxBound (2 ^ 64) || !Nat.ble (maxBound + raBytes) (2 ^ 64) ||
              !exportBounds.all (fun p => Nat.ble p.2 maxBound) then
            .error s!"recBudgetSCC({it.name}): exportBounds/maxBound overflow"
          else
            let sccCh : EvalSccChunk :=
              .recBudgetSCC (Lean.toExpr acc) (Lean.toExpr recSigs) leaves
            let sccSigs := recSigs.map fun s => (s, budgetBound exportBounds maxBound s.1)
            let acc2 := sccSigs.reverse ++ acc
            walk fuel' (idx + len) (sccSrcSigs ++ availSigs) acc2 acc2 (idx + len) 0 [] tl'
              (sccCh :: out1)
  walk (allItems.length * 2 + 4) 0 extSigs0 ext0 ext0 0 0 [] allItems []

private def evalSccItemsCore (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (extSigs0 : List SigEntry) (exits : List Sym) (nX : Nat)
    (bfs : List BudgetFn) (chunkSize maxBound maxDirs : Nat) (exportBounds : List (Sym × Nat))
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] :
    Except String EvalSccModuleData := do
  if bfs.isEmpty then
    pure (evalSccEmpty I ext0)
  else
    let allItems ← spawnLowerItems I lt bfs (fun b => b.toFn)
        fun nm h c mf ext b =>
      let cals := b.toFn.callees
      SccItem.mk nm b.toFn.sig mf.sig h c ext cals (b.toFn.checkCallsOk cals exits)
        (b.maxFrame, b.minEntry)
    evalSccItemsFromList I raBytes ext0 extSigs0 exits nX chunkSize maxBound maxDirs
      exportBounds allItems

def evalLinkedBudgetSccChunks (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (extSigs0 : List SigEntry) (exits : List Sym) (nX : Nat)
    (bfs : List BudgetFn) (chunkSize maxBound maxDirs : Nat) (exportBounds : List (Sym × Nat) := [])
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] :
    Except String EvalSccModuleData :=
  evalSccItemsCore I lt raBytes ext0 extSigs0 exits nX bfs chunkSize maxBound maxDirs exportBounds

/-- Flat `TFlatFn` meta evaluator mirroring `evalLinkedBudgetSccChunks` via `MainFlat`. -/
def evalLinkedBudgetSccChunksFlat (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (extSigs0 : List SigEntry) (exits : List Sym) (nX : Nat)
    (chunkSize maxBound maxDirs : Nat) (exportBounds : List (Sym × Nat))
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)]
    (items : List (TFlatFn × Nat × Nat)) :
    Except String EvalSccModuleData := do
  if items.isEmpty then
    pure (evalSccEmpty I ext0)
  else
    let allItems ← spawnLowerFlatItems I lt items (·.1)
        fun nm h c mf ext it =>
      let (tf, maxFrame, minEntry) := it
      let cals := (tflatCalleesAux tf.body []).reverse
      SccItem.mk nm (tf.name, tf.as, tf.rs) (mf.name, mf.as, mf.rs) h c ext cals
        (tflatExitsOk exits tf.body) (maxFrame, minEntry)
    evalSccItemsFromList I raBytes ext0 extSigs0 exits nX chunkSize maxBound maxDirs
      exportBounds allItems

structure CertSccOptions where
  maxBT? : Option Term := none
  exportBoundsT? : Option Term := none
  extT? : Option Term := none
  extSigsT? : Option Term := none
  exitsT? : Option Term := none
  nXT? : Option Term := none
  maxDirsT? : Option Term := none
  compileT? : Option Term := none
  compileExtT? : Option Term := none
  flatT? : Option Term := none
  deriving Inhabited

structure CertSccInputs where
  base : CertBaseEnv
  modE : Lean.Expr
  bfsBaseE : Lean.Expr
  extSigsE : Lean.Expr
  exportBoundsE : Lean.Expr
  chunks : List EvalSccChunk
  finalExtLit : Lean.Expr
  flatBfsCtx? : Option (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := none

def parseCertSccOptions (optKeys : TSyntaxArray `ident) (optVals : TSyntaxArray `term) :
    CommandElabM CertSccOptions :=
  parseKvOptions "compile_linked_budget_scc!"
    "maxBound, exportBounds, ext, extSigs, exits, nX, maxDirs, compile, compileExt, flat" {}
    (fun opts k v => pure <| match k with
      | `maxBound => some { opts with maxBT? := some v }
      | `exportBounds => some { opts with exportBoundsT? := some v }
      | `ext => some { opts with extT? := some v }
      | `extSigs => some { opts with extSigsT? := some v }
      | `exits => some { opts with exitsT? := some v }
      | `nX => some { opts with nXT? := some v }
      | `maxDirs => some { opts with maxDirsT? := some v }
      | `compile => some { opts with compileT? := some v }
      | `compileExt => some { opts with compileExtT? := some v }
      | `flat => some { opts with flatT? := some v }
      | _ => none) optKeys optVals

def elabAndEvalSccChunks (targT layoutT ltT clT modT : Term) (chunkSize : Nat)
    (opts : CertSccOptions) : TermElabM CertSccInputs := do
  let b ← elabCertBase targT layoutT ltT clT {
    maxBT? := opts.maxBT?, extT? := opts.extT?, exitsT? := opts.exitsT?, nXT? := opts.nXT?,
    maxDirsT? := opts.maxDirsT?, compileT? := opts.compileT?, compileExtT? := opts.compileExtT? }
  let tys := mkCertTypes
  let bModE ← Term.elabTerm modT (some (Lean.mkConst ``LeanQbe.T.BudgetModule))
  let modE := mkApp (Lean.mkConst ``LeanQbe.T.BudgetModule.toModule) bModE
  let bfsBaseE := mkApp (Lean.mkConst ``LeanQbe.T.BudgetModule.fns) bModE
  let extSigsE ← elabOptTerm opts.extSigsT? tys.listSigTy
    (mkApp4 (Lean.mkConst ``List.map [.zero, .zero]) (Lean.mkConst ``LeanQbe.T.Extern) tys.sigTy
      (Lean.mkConst ``LeanQbe.T.Extern.sig) (mkApp (Lean.mkConst ``LeanQbe.T.Module.externs) modE))
  let nilSymNat := mkApp (Lean.mkConst ``List.nil [.zero]) tys.symNatTy
  let exportBoundsE ← elabOptTerm opts.exportBoundsT? tys.listBoundsTy nilSymNat
  let flat ← evalBoolOpt opts.flatT? false
  Term.synthesizeSyntheticMVarsNoPostponing
  let modE ← instantiateMVars modE; let bfsBaseE ← instantiateMVars bfsBaseE
  let extSigsE ← instantiateMVars extSigsE; let exportBoundsE ← instantiateMVars exportBoundsE
  let outTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String)
    (Lean.mkConst ``LeanQbe.T.EvalSccModuleData)
  let (evalRes, flatBfsCtx?) ←
    if flat then
      match (← decodeFlatBudgetSliceExpr bfsBaseE) with
      | some (flatItems, flatBfsListE, bfsEqProof, flatFnsListE, fnsEqProof) =>
        let flatTy := Lean.mkConst ``LeanQbe.T.TFlatFn
        let natPairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) tys.natTy tys.natTy
        let flatItemTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) flatTy natPairTy
        let listFlatItemTy := mkApp (Lean.mkConst ``List [.zero]) flatItemTy
        let runnerTy := Lean.mkForall `_ .default listFlatItemTy outTy
        let callE ← instantiateMVars <|
          mkAppN (Lean.mkConst ``LeanQbe.T.evalLinkedBudgetSccChunksFlat)
            #[b.isaE, b.ltE, b.raE, b.ext0E, extSigsE, b.exitsE, b.nXE, mkNatLit chunkSize,
              b.maxBE, b.maxDirsE, exportBoundsE, b.toExprHintsInst, b.toExprDirInst]
        let runner ← unsafe evalExpr
          (List (TFlatFn × Nat × Nat) → Except String EvalSccModuleData) runnerTy callE
        pure (runner flatItems, some (flatBfsListE, bfsEqProof, flatFnsListE, fnsEqProof))
      | none =>
        throwError "compile_linked_budget_scc!: (flat := true) requires a materialized \
          TFlatFn/denoteFunc BudgetModule slice (decodeFlatBudgetSliceExpr returned none)"
    else
      let callE ← instantiateMVars <| mkAppN (Lean.mkConst ``LeanQbe.T.evalLinkedBudgetSccChunks)
        #[b.isaE, b.ltE, b.raE, b.ext0E, extSigsE, b.exitsE, b.nXE, bfsBaseE, mkNatLit chunkSize,
          b.maxBE, b.maxDirsE, exportBoundsE, b.toExprHintsInst, b.toExprDirInst]
      pure (← unsafe evalExpr (Except String EvalSccModuleData) outTy callE, none)
  match evalRes with
  | .error e => throwError "compile_linked_budget_scc!: {e}"
  | .ok md => return {
      base := b, modE, bfsBaseE, extSigsE, exportBoundsE,
      chunks := md.chunks, finalExtLit := md.finalExtLit, flatBfsCtx? }

private structure EmittedLeafNames where
  leaf : EvalSccLeaf
  fnsNm : Name
  hintsNm : Name
  codeNm : Name
  cmAuxNm : Name
  subNm : Name
  flatNm? : Option Name := none
  cmFlatNm? : Option Name := none
  deriving Inhabited

private inductive EmittedChunkMeta where
  | acyc (ac : AcycChunkNames)
  | recBudget (extNm recSigsNm scsNm chkNm chunkNm : Name) (leaves : Array EmittedLeafNames)
  deriving Inhabited

private def elabCompileLinkedBudgetScc (certId : Ident)
    (targT layoutT ltT clT modT : Term) (chunkSize : Nat)
    (optKeys : TSyntaxArray `ident) (optVals : TSyntaxArray `term) : CommandElabM Unit := do
  let ns ← getCurrNamespace; let certNm := ns ++ certId.getId; let auxNs := certNm ++ `aux
  let opts ← parseCertSccOptions optKeys optVals
  let inp ← liftTermElabM <|
    elabAndEvalSccChunks targT layoutT ltT clT modT chunkSize opts
  let b := inp.base; let tys := mkCertTypes; let bfnTy := Lean.mkConst ``LeanQbe.T.BudgetFn
  let listBfnTy := mkApp (Lean.mkConst ``List [1]) bfnTy
  let budgetExcTy :=
    mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String) b.listDirTy
  let fnsBaseE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) inp.modE
  let (flatBfsCtx?, flatFnsCtx?) ← match inp.flatBfsCtx? with
    | some (flatBfsListE, bfsEqProof, flatFnsListE, fnsEqProof) =>
      let flatTy := Lean.mkConst ``LeanQbe.T.TFlatFn
      let listFlatTy := mkApp (Lean.mkConst ``List [.zero]) flatTy
      let flatBfnTy := Lean.mkConst ``LeanQbe.T.FlatBudgetFn
      let listFlatBfnTy := mkApp (Lean.mkConst ``List [.zero]) flatBfnTy
      let flatBfsNm := auxNs ++ `flatBfs; let bfsFlatEqNm := auxNs ++ `bfs_flat_eq
      let flatBfsConstE := Lean.mkConst flatBfsNm
      let bfsRhsE := mkApp4 (Lean.mkConst ``List.map [.zero, .one])
        flatBfnTy bfnTy (Lean.mkConst ``LeanQbe.T.FlatBudgetFn.toBudgetFn) flatBfsConstE
      let bfsEqTy := mkApp3 (Lean.mkConst ``Eq [2]) listBfnTy inp.bfsBaseE bfsRhsE
      let flatFnsNm := auxNs ++ `flatFns; let fnsFlatEqNm := auxNs ++ `fns_flat_eq
      let flatFnsConstE := Lean.mkConst flatFnsNm
      let fnsRhsE := mkApp4 (Lean.mkConst ``List.map [.zero, .one])
        flatTy tys.fnTy (Lean.mkConst ``LeanQbe.T.TFlatFn.toFn) flatFnsConstE
      let fnsEqTy := mkApp3 (Lean.mkConst ``Eq [2]) tys.listFnTy fnsBaseE fnsRhsE
      liftCoreM do
        addCertDef flatBfsNm listFlatBfnTy flatBfsListE false
        addCertThm bfsFlatEqNm bfsEqTy bfsEqProof
        addCertDef flatFnsNm listFlatTy flatFnsListE false
        addCertThm fnsFlatEqNm fnsEqTy fnsEqProof
      pure (some (flatBfnTy, flatBfsConstE, bfsFlatEqNm),
        some (fnsBaseE, flatFnsConstE, fnsFlatEqNm))
    | none => pure (none, none)
  let flatFnsBaseE? := flatFnsCtx?.map (·.2.1)
  let emitLeaves (pfx : String) (leaves : List EvalSccLeaf) :
      CommandElabM (Array EmittedLeafNames) := do
    let mut leafArr : Array EmittedLeafNames := #[]; let mut sj : Nat := 0
    for lf in leaves do
      let nm := fun s => auxNs ++ Name.mkSimple s!"{pfx}_s{sj}_{s}"
      let fnsNm := nm "fns"; let hintsNm := nm "hints"; let codeNm := nm "code"
      let sliceE := mkSliceExpr bfnTy inp.bfsBaseE lf.startIdx lf.fnCount lf.isModuleLast
      let flatNm? := flatBfsCtx?.map fun _ => nm "flat"
      let cmFlatNm? := flatBfsCtx?.map fun _ => nm "cm_flat"
      liftCoreM do
        addCertDef fnsNm listBfnTy sliceE b.compileCert
        addCertDef hintsNm b.listHintsTy lf.hintsLit b.compileCert
        addCertDef codeNm b.listDirTy lf.codeLit b.compileCert
        if let (some (flatBfnTy, flatBfsConstE, _), some flatNm) := (flatBfsCtx?, flatNm?) then
          let listFlatBfnTy := mkApp (Lean.mkConst ``List [.zero]) flatBfnTy
          let flatSliceE :=
            mkSliceExpr flatBfnTy flatBfsConstE lf.startIdx lf.fnCount lf.isModuleLast .zero
          addCertDef flatNm listFlatBfnTy flatSliceE false
      leafArr := leafArr.push {
        leaf := lf, fnsNm, hintsNm, codeNm, cmAuxNm := nm "cm", subNm := nm "sub",
        flatNm?, cmFlatNm? }
      sj := sj + 1
    return leafArr
  let emitRec (pfx : String) (extLit recSigsLit : Lean.Expr)
      (leaves : List EvalSccLeaf) : CommandElabM EmittedChunkMeta := do
    let nm := fun s => auxNs ++ Name.mkSimple s!"{pfx}_{s}"
    let extNm := nm "ext"; let recSigsNm := nm "recsigs"
    liftCoreM do
      addCertDef extNm tys.listExtTy extLit b.compileCert
      addCertDef recSigsNm tys.listSigTy recSigsLit b.compileCert
    return .recBudget extNm recSigsNm (nm "scs") (nm "chk") (nm "chunk")
      (← emitLeaves pfx leaves)
  -- Pass 1: emit pure literal definitions for all chunks and sub-chunks.
  let mut emitted : Array EmittedChunkMeta := #[]; let mut ci : Nat := 0
  for ch in inp.chunks do
    let pfx := s!"c{ci}"
    emitted := emitted.push <| ← match ch with
      | .acyc startIdx fnCount isLast extLit hintsLit codeLit boundsLit =>
        .acyc <$> emitAcycChunkDefs auxNs pfx b.compileCert fnsBaseE b.listHintsTy b.listDirTy
          ⟨startIdx, fnCount, isLast, extLit, hintsLit, codeLit, boundsLit⟩ flatFnsBaseE?
      | .recBudgetSCC extLit recSigsLit leaves =>
        emitRec pfx extLit recSigsLit leaves
    ci := ci + 1
  -- Pass 2: queue all per-chunk and per-subchunk kernel theorems in parallel.
  let addBoolEq (nm : Name) (lhs : Lean.Expr) :=
    liftCoreM <| addKernelEqThm nm (Lean.mkConst ``Bool) lhs (Lean.mkConst ``Bool.true) .zero
  for em in emitted do
    match em with
    | .acyc ac => liftCoreM <| emitAcycChunkThms b ac flatFnsCtx?
    | .recBudget extNm recSigsNm _ _ _ leaves =>
      for lfn in leaves do
        let cmLhs := mkAppN (Lean.mkConst ``LeanQbe.T.compileModuleBudgetRecAuxSupp)
          #[b.isaE, b.ltE, b.raE, Lean.mkConst recSigsNm, Lean.mkConst extNm, b.exitsE, b.nXE,
            Lean.mkConst lfn.fnsNm, Lean.mkConst lfn.hintsNm]
        let cmRhs := mkApp3 (Lean.mkConst ``Except.ok [.zero, .zero])
          (Lean.mkConst ``String) b.listDirTy (Lean.mkConst lfn.codeNm)
        match flatBfsCtx?, lfn.flatNm?, lfn.cmFlatNm? with
        | some (flatBfnTy, flatBfsConstE, bfsFlatEqNm), some flatNm, some cmFlatNm =>
          let cmFlatLhs := mkAppN (Lean.mkConst ``LeanQbe.T.compileModuleBudgetRecAuxFlat)
            #[b.isaE, b.ltE, b.raE, Lean.mkConst recSigsNm, Lean.mkConst extNm, b.exitsE, b.nXE,
              Lean.mkConst flatNm, Lean.mkConst lfn.hintsNm]
          liftCoreM do
            addKernelEqThm cmFlatNm budgetExcTy cmFlatLhs cmRhs .zero
            let sliceEqPf := if lfn.leaf.isModuleLast then
              mkAppN (Lean.mkConst ``LeanQbe.T.map_drop_eq [.zero, .one])
                #[flatBfnTy, bfnTy, Lean.mkConst ``LeanQbe.T.FlatBudgetFn.toBudgetFn,
                  inp.bfsBaseE, flatBfsConstE, Lean.mkConst bfsFlatEqNm,
                  mkNatLit lfn.leaf.startIdx]
            else
              mkAppN (Lean.mkConst ``LeanQbe.T.map_slice_eq [.zero, .one])
                #[flatBfnTy, bfnTy, Lean.mkConst ``LeanQbe.T.FlatBudgetFn.toBudgetFn,
                  inp.bfsBaseE, flatBfsConstE, Lean.mkConst bfsFlatEqNm,
                  mkNatLit lfn.leaf.startIdx, mkNatLit lfn.leaf.fnCount]
            let cmTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) budgetExcTy cmLhs cmRhs
            let cmVal := mkAppN (Lean.mkConst ``LeanQbe.T.compileModuleBudgetRecAuxSupp_of_flat_eq)
              #[b.isaE, b.ltE, b.raE, Lean.mkConst recSigsNm, Lean.mkConst extNm, b.exitsE,
                b.nXE, Lean.mkConst lfn.fnsNm, Lean.mkConst flatNm, Lean.mkConst lfn.hintsNm,
                Lean.mkConst lfn.codeNm, sliceEqPf, Lean.mkConst cmFlatNm]
            addCertThm lfn.cmAuxNm cmTy cmVal
        | _, _, _ =>
          liftCoreM <| addKernelEqThm lfn.cmAuxNm budgetExcTy cmLhs cmRhs .zero
  -- Pass 3: assemble `.acyc` and `.recBudgetSCC` `Chunk` entries & checks.
  let chunkTy := mkAppN (Lean.mkConst ``LeanQbe.T.Chunk) #[b.targE, b.ltE, b.exitsE, b.nXE]
  let mut chunkEntries : Array Lean.Expr := #[]
  for em in emitted do
    match em with
    | .acyc ac =>
      let ccVal ← liftCoreM <| emitAcycCompiledChunk b ac
      chunkEntries := chunkEntries.push
        (mkAppN (Lean.mkConst ``LeanQbe.T.Chunk.acyc) #[b.targE, b.ltE, b.exitsE, b.nXE, ccVal])
    | .recBudget extNm recSigsNm scsNm chkNm chunkNm leaves =>
      let subTy := mkAppN (Lean.mkConst ``LeanQbe.T.RecBudgetSubChunk)
        #[b.targE, b.ltE, Lean.mkConst recSigsNm, Lean.mkConst extNm, b.exitsE, b.nXE]
      let mut subConsts : List Lean.Expr := []
      for lfn in leaves do
        let auxEq := mkAppN (Lean.mkConst ``LeanQbe.T.compileModuleBudgetRecAux_of_supp)
          #[b.isaE, b.ltE, b.raE, Lean.mkConst recSigsNm, Lean.mkConst extNm, b.exitsE, b.nXE,
            Lean.mkConst lfn.fnsNm, Lean.mkConst lfn.hintsNm, Lean.mkConst lfn.codeNm,
            Lean.mkConst lfn.cmAuxNm]
        let subVal := mkAppN (Lean.mkConst ``LeanQbe.T.RecBudgetSubChunk.mk)
          #[b.targE, b.ltE, Lean.mkConst recSigsNm, Lean.mkConst extNm, b.exitsE, b.nXE,
            Lean.mkConst lfn.fnsNm, Lean.mkConst lfn.hintsNm, Lean.mkConst lfn.codeNm, auxEq]
        liftCoreM <| addCertDef lfn.subNm subTy subVal b.compileCert
        subConsts := subConsts ++ [Lean.mkConst lfn.subNm]
      liftCoreM <| addCertDef scsNm (mkApp (Lean.mkConst ``List [1]) subTy)
        (mkExprList 1 subTy subConsts) b.compileCert
      addBoolEq chkNm (mkAppN (Lean.mkConst ``LeanQbe.T.checkRecBudgetSubchunks)
        #[b.targE, b.layoutE, b.ltE, Lean.mkConst recSigsNm, Lean.mkConst extNm, b.exitsE, b.nXE,
          b.maxBE, inp.exportBoundsE, Lean.mkConst scsNm])
      liftCoreM <| addCertDef chunkNm chunkTy
        (mkAppN (Lean.mkConst ``LeanQbe.T.Chunk.ofBudgetRecSubchunks)
          #[b.targE, b.ltE, b.exitsE, b.nXE, b.layoutE, b.clE, Lean.mkConst recSigsNm,
            Lean.mkConst extNm, b.maxBE, inp.exportBoundsE, Lean.mkConst scsNm, Lean.mkConst chkNm])
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
    | .recBudget extNm recSigsNm _ _ chunkNm leaves =>
      let tailFnsE := restFnsE
      let mut curItemsE := mkApp (Lean.mkConst ``List.nil [1]) bfnTy
      let mut curSupp := mkApp (Lean.mkConst ``LeanQbe.T.supportsAll_budget_nil) b.ltE
      let nLeaves := leaves.size
      for sRevIdx in [:nLeaves] do
        let lfn := leaves[nLeaves - 1 - sRevIdx]!
        let leafItemsE := Lean.mkConst lfn.fnsNm
        let sE := mkNatLit lfn.leaf.startIdx; let kE := mkNatLit lfn.leaf.fnCount
        fnsEqProof := if sRevIdx == 0 then
          if revIdx == 0 then
            mkApp2 (Lean.mkConst ``LeanQbe.T.budgetFns_last_mod_eq) inp.bfsBaseE sE
          else mkApp5 (Lean.mkConst ``LeanQbe.T.budgetFns_last_eq)
            inp.bfsBaseE tailFnsE sE kE fnsEqProof
        else mkApp6 (Lean.mkConst ``LeanQbe.T.budgetFns_cons_eq)
          inp.bfsBaseE curItemsE tailFnsE sE kE fnsEqProof
        let leafSuppVal :=
          mkAppN (Lean.mkConst ``LeanQbe.T.supportsAll_of_compileModuleBudgetRecAuxSupp)
            #[b.isaE, b.ltE, b.raE, Lean.mkConst recSigsNm, Lean.mkConst extNm,
              b.exitsE, b.nXE, leafItemsE, Lean.mkConst lfn.hintsNm,
              Lean.mkConst lfn.codeNm, Lean.mkConst lfn.cmAuxNm]
        curSupp := mkApp5 (Lean.mkConst ``LeanQbe.T.supportsAll_budget_append)
          b.ltE leafItemsE curItemsE leafSuppVal curSupp
        curItemsE := mkApp3 (Lean.mkConst ``List.append [1]) bfnTy leafItemsE curItemsE
      let scsSupp :=
        mkApp3 (Lean.mkConst ``LeanQbe.T.supportsAll_budget_leaf) b.ltE curItemsE curSupp
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

/-- `compile_linked_budget_scc! certName target layout legalTarget labelClean budgetMod chunkSize
[(maxBound := ...)] [(exportBounds := ...)] [(ext := ...)] [(extSigs := ...)] [(exits := ...)]
[(nX := ...)] [(maxDirs := ...)] [(compile := ...)] [(compileExt := ...)] [(flat := ...)]`
partitions `budgetMod.fns` into `.acyc` spans and closed `.recBudgetSCC` SCC chunks. -/
scoped syntax "compile_linked_budget_scc! " ident
    term:arg term:arg term:arg term:arg term:arg num
    ("(" ident " := " term ")")* : command

scoped elab_rules : command
  | `(compile_linked_budget_scc! $certId $targT $layoutT $ltT $clT $modT $chunkSizeLit
      $[($optKeys := $optVals)]*) =>
    elabCompileLinkedBudgetScc certId targT layoutT ltT clT modT chunkSizeLit.getNat optKeys optVals

end

end LeanQbe.T
