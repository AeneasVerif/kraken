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

S1(a)-compliant certificate layer (`addNoncomputable` / `compile := false` defaults) over
`MainLinkScc`, `MainCertCore`, `MainCertProof`, and `MainCertElab`:
* `LinkedCertScc`: closed whole-module certificate mixing `.acyc` (`CompiledChunk`) and
  `.recSCC` (`CompiledRec` assembled from parallel-checked `RecSubChunk`s) against canonical
  `semChunks`, plus `ofLinkedCert`, `append`, and `TargetInit` `Eventually` lifts.
* `compile_linked_scc!`: partitions `mod.fns` in source list order into minimal acyclic spans
  and closed SCC chunks, evaluates all functions once in parallel worker tasks, verifies
  per-subchunk kernel theorems in parallel, links chunks in O(#subchunks), and emits a
  `std3`-clean `LinkedCertScc` with tiny `.c`/`.ir`/`.olean.private` footprints.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

open Std Std.ExtHashMap
open LeanQbe.T.LinkRec

/-! ## 1. O(#subchunks) Slice, `supportsSource`, and `checkChunksCalls` Helpers -/

theorem slice_sub_last_mod_eq {α : Type _} (l : List α) (s : Nat) :
    l.drop s = (l.drop s ++ []) ++ [] := by
  simp

theorem slice_sub_last_eq {α : Type _} {l rest : List α} {s k : Nat}
    (h : l.drop (s + k) = rest) :
    l.drop s = ((l.drop s).take k ++ []) ++ rest := by
  simpa using slice_cons_eq h

theorem slice_sub_cons_eq {α : Type _} {l : List α} {scs tail : List α} {s k : Nat}
    (h : l.drop (s + k) = scs ++ tail) :
    l.drop s = ((l.drop s).take k ++ scs) ++ tail := by
  rw [List.append_assoc]
  exact slice_cons_eq h

theorem supportsAll_append_pred {lt : LegalTarget} {fs₁ fs₂ : List Fn}
    (h₁ : ∀ f ∈ fs₁, (f.earlyOpt).body.supportsSource lt = true)
    (h₂ : ∀ f ∈ fs₂, (f.earlyOpt).body.supportsSource lt = true) :
    ∀ f ∈ fs₁ ++ fs₂, (f.earlyOpt).body.supportsSource lt = true := by
  intro f hf
  rcases List.mem_append.mp hf with h | h
  · exact h₁ f h
  · exact h₂ f h

theorem supportsAll_leaf {lt : LegalTarget} {fs : List Fn}
    (h : checkSupportsChunk lt fs = true) :
    ∀ f ∈ fs, (f.earlyOpt).body.supportsSource lt = true :=
  fun f hf => List.all_eq_true.mp h f hf

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
  | [], cs₂, extSigs => by simp [checkChunksCalls, sccChunksSigAcc]
  | .acyc c :: rest, cs₂, extSigs => by
      dsimp only [List.cons_append, checkChunksCalls, sccChunksSigAcc, Chunk.fns]
      rw [checkChunksCalls_append exits rest cs₂ (c.fs.map Fn.sig ++ extSigs), Bool.and_assoc]
  | .recSCC _ _ fs _ _ _ :: rest, cs₂, extSigs => by
      dsimp only [List.cons_append, checkChunksCalls, sccChunksSigAcc, Chunk.fns]
      rw [checkChunksCalls_append exits rest cs₂ (fs.map Fn.sig ++ extSigs), Bool.and_assoc]

private theorem chunksFns_map_acyc {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (cs : List (CompiledChunk T lt exits nX)),
      sccChunksFns (cs.map Chunk.acyc) = chunksFns cs
  | [] => rfl
  | c :: cs => by simp [sccChunksFns, chunksFns, Chunk.fns, chunksFns_map_acyc cs]

private theorem chunksCode_map_acyc {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (cs : List (CompiledChunk T lt exits nX)),
      sccChunksCode (cs.map Chunk.acyc) = chunksCode cs
  | [] => rfl
  | c :: cs => by simp [sccChunksCode, chunksCode, Chunk.code, chunksCode_map_acyc cs]

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
  | acc, c :: cs => by
      simp [checkSccChunksExt, checkChunksExt, Chunk.extCallees, Chunk.sigBounds,
        checkChunksExt_map_acyc _ cs]

theorem checkLinkSccList_map_acyc {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (ext₀ : List (SigEntry × Nat))
    (cs : List (CompiledChunk T lt exits nX))
    (h : checkLinkList L ext₀ cs = true)
    (hdisj : !(ext₀.any (fun p => ((chunksFns cs).map Fn.name).any
      (fun nm => nm == p.1.1))) = true) :
    checkLinkSccList L ext₀ (cs.map Chunk.acyc) = true := by
  dsimp only [checkLinkList] at h
  dsimp only [checkLinkSccList]
  rw [chunksFns_map_acyc, chunksCode_map_acyc, checkChunksExt_map_acyc]
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨⟨⟨h.1.1.1.1, hdisj⟩, h.1.1.1.2⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩

/-! ## 2. `LinkedCertScc` Certificate Structure & Proof API -/

/-- Closed whole-module native compilation and linking certificate over mixed `.acyc` and
`.recSCC` chunks (`MainLinkScc`), following S1(a) `noncomputable` cert hygiene. -/
structure LinkedCertScc (T : Target) (L : TargetLayout T) (lt : LegalTarget)
    (hcl : Rega.LabelClean T.toIsa) (mod : Module)
    (ext₀ : List (SigEntry × Nat) := []) (exits : List Sym := []) (nX : Nat := 0)
    (maxBound : Nat := 2048)
    (extSigs : List SigEntry := mod.externs.map Extern.sig) : Type 1 where
  chunks : List (Chunk T lt exits nX)
  linkCheck : checkLinkSccList L ext₀ chunks = true
  callsCheck : checkChunksCalls exits extSigs chunks = true
  fns_eq : mod.fns = sccChunksFns chunks
  supportsAll : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true
  maxBound_le : sccChunksMaxBound chunks ≤ maxBound

namespace LinkedCertScc

variable {T : Target} {L : TargetLayout T} {lt : LegalTarget}
  {hcl : Rega.LabelClean T.toIsa} {mod : Module}
  {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
  {extSigs : List SigEntry}

/-- Linked machine-code host for the full mixed module. -/
@[expose] noncomputable def host
    (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs) :
    T.mach.Host :=
  sccHost L ext₀ cert.chunks cert.linkCheck

/-- Concatenated directive stream of all linked chunks. -/
@[expose] noncomputable def code
    (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs) :
    List T.Directive :=
  sccChunksCode cert.chunks

/-- Stack bound linked for symbol `nm` across `cert.chunks`. -/
@[expose] noncomputable def bound
    (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs) (nm : Sym) : Nat :=
  sccBound cert.chunks nm

/-- Canonical closed semantic environment accumulated across `cert.chunks`. -/
@[expose] noncomputable def sem
    (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs)
    (Γ₀ : Env := fun _ _ _ _ _ _ _ => False) : Env :=
  semChunks extSigs Γ₀ cert.chunks

/-- Number of compiled chunks linked in `cert`. -/
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
  linkCheck := hchk
  callsCheck := hcalls
  fns_eq := by rw [hmod, c₁.fns_eq, c₂.fns_eq, sccChunksFns_append]
  supportsAll := by
    intro f hf
    rw [hmod, List.mem_append] at hf
    rcases hf with h1 | h2
    · exact c₁.supportsAll f h1
    · exact c₂.supportsAll f h2
  maxBound_le := by
    rw [sccChunksMaxBound_append]
    exact Nat.max_le.mpr
      ⟨Nat.le_trans c₁.maxBound_le (Nat.le_max_left _ _),
       Nat.le_trans c₂.maxBound_le (Nat.le_max_right _ _)⟩

/-! ### Metadata, host, and semantic theorems (opaque proofs in `.olean.private`) -/

theorem bound_le_max
    (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs) (nm : Sym) :
    cert.bound nm ≤ maxBound :=
  Nat.le_trans (sccBound_le_max cert.chunks nm) cert.maxBound_le

theorem bound_eq_chunk
    (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs)
    {c : Chunk T lt exits nX} (hc : c ∈ cert.chunks) {nm : Sym} (hnm : nm ∈ c.fns.map Fn.name) :
    cert.bound nm = c.bound nm := by
  have hp := checkLinkSccList_parts cert.linkCheck
  have hnd := (List.nodup_append.mp hp.2.2.2.2.1).1
  exact sccBound_eq_chunk cert.chunks hnd c hc hnm

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
  have hdisj' : ∀ nm ∈ (sccChunksFns cert.chunks).map Fn.name, nm ∉ extSigs.map Prod.fst := by
    rw [← cert.fns_eq]; exact hdisj_ext
  have hwf' : ∀ g ∈ sccChunksFns cert.chunks, g.Wf := by rw [← cert.fns_eq]; exact hwf
  have hsupp' : ∀ g ∈ sccChunksFns cert.chunks, (g.earlyOpt).body.supportsSource lt = true := by
    rw [← cert.fns_eq]; exact cert.supportsAll
  have hmem : f ∈ sccChunksFns cert.chunks := by rw [← cert.fns_eq]; exact hf
  obtain ⟨c, hc, hfc⟩ := mem_chunk_of_mem_sccChunksFns hmem
  exact linkChunks_fnSpec_linked L hcl ext₀ extSigs Γ₀ cert.chunks cert.linkCheck
    cert.callsCheck hnd_ext hdisj' hwf' hsupp' hext hext_uniq c hc f hfc

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
  refine ⟨hdef, Target.FnSpec.of_spec T (fnSpec_of_legalEnv_onlyFn has hrs hspec)
    fun args m Q X hs => hle args m Q _ (hnoex args m Q X _ hs)⟩

private theorem mem_sccChunksFns_tail_of_not_mem {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} {f : Fn} :
    ∀ {cs : List (Chunk T lt exits nX)},
      f.name ∉ (sccChunksFns cs).map Fn.name → ∀ c ∈ cs, f.sig ∉ c.fns.map Fn.sig
  | [], _, _, hc => nomatch hc
  | c₀ :: cs, hnot, c, hc => by
      dsimp only [sccChunksFns] at hnot
      rw [List.map_append] at hnot
      rcases List.mem_cons.mp hc with rfl | hcs
      · intro hmem
        obtain ⟨g, hg, heq⟩ := List.mem_map.mp hmem
        have hnm : g.name = f.name := congrArg Prod.fst heq
        exact hnot (List.mem_append_left _ (hnm ▸ List.mem_map_of_mem hg))
      · exact mem_sccChunksFns_tail_of_not_mem
          (fun hm => hnot (List.mem_append_right _ hm)) c hcs

private theorem externsOfSigs_map_sig' (sigs : List SigEntry) :
    (externsOfSigs sigs).map Extern.sig = sigs := by
  induction sigs with
  | nil => rfl
  | cons s ss ih => rcases s with ⟨nm, as, bs⟩; simpa [externsOfSigs, Extern.sig] using ih

/-- Project the head chunk's `Chunk.sem` into `semChunks extSigs Γ₀ (c :: cs)` when `f.name` does
not appear in any trailing chunk `cs`. -/
theorem semChunks_of_head {c : Chunk T lt exits nX} {cs : List (Chunk T lt exits nX)}
    {extSigs : List SigEntry} {Γ₀ : Env} {f : Fn}
    (hnot : f.name ∉ (sccChunksFns cs).map Fn.name) (xs : Tup Val f.as) (m : Mem 64)
    (Q : Post f.rs) (X : XPost)
    (h : c.sem extSigs Γ₀ f.name f.as f.rs xs m Q X) :
    semChunks extSigs Γ₀ (c :: cs) f.name f.as f.rs xs m Q X := by
  have hstep : ∀ (cs : List (Chunk T lt exits nX)) (es : List SigEntry) (Γ : Env),
      f.name ∉ (sccChunksFns cs).map Fn.name → f.sig ∈ es →
      Γ f.name f.as f.rs xs m Q X →
      semChunks es Γ cs f.name f.as f.rs xs m Q X := by
    intro cs
    induction cs with
    | nil => intro _ _ _ _ hΓ; exact hΓ
    | cons d ds ih =>
        intro es Γ hnotd hmemd hΓ
        dsimp only [sccChunksFns] at hnotd
        rw [List.map_append, List.mem_append, not_or] at hnotd
        dsimp only [semChunks]
        refine ih (d.fns.map Fn.sig ++ es) (d.sem es Γ) hnotd.2
          (List.mem_append_right _ hmemd) ?_
        cases d with
        | acyc _ =>
            dsimp only [Chunk.sem, Env.sccStep]; rw [externsOfSigs_map_sig']
            exact Or.inr ⟨hmemd, hΓ⟩
        | recSCC _ _ _ _ _ _ =>
            dsimp only [Chunk.sem, Env.sccStep]; rw [externsOfSigs_map_sig']
            exact Or.inr ⟨hmemd, hΓ⟩
  rcases Classical.em (f ∈ c.fns) with hfc | hnotc
  · exact hstep cs (c.fns.map Fn.sig ++ extSigs) (c.sem extSigs Γ₀) hnot
      (List.mem_append_left _ (List.mem_map_of_mem hfc)) h
  · dsimp only [semChunks]
    cases c with
    | acyc m' =>
        have horig := h
        dsimp only [Chunk.sem, Env.sccStep] at h
        rw [externsOfSigs_map_sig'] at h
        rcases h with ⟨hsig, _⟩ | ⟨hex, _⟩
        · obtain ⟨g, hg, heq⟩ := List.mem_map.mp hsig
          have hsig_eq : f.sig = g.sig := heq.symm
          exact hstep cs (m'.fs.map Fn.sig ++ extSigs)
            (Chunk.sem extSigs (.acyc m') Γ₀) hnot
            (List.mem_append_left _ (hsig_eq ▸ List.mem_map_of_mem hg)) horig
        · exact hstep cs (m'.fs.map Fn.sig ++ extSigs)
            (Chunk.sem extSigs (.acyc m') Γ₀) hnot
            (List.mem_append_right _ hex) horig
    | recSCC ext fuel fs hints maxB cr =>
        have horig := h
        dsimp only [Chunk.sem, Env.sccStep] at h
        rw [externsOfSigs_map_sig'] at h
        rcases h with ⟨hsig, _⟩ | ⟨hex, _⟩
        · obtain ⟨g, hg, heq⟩ := List.mem_map.mp hsig
          have hsig_eq : f.sig = g.sig := heq.symm
          exact hstep cs (fs.map Fn.sig ++ extSigs)
            (Chunk.sem extSigs (.recSCC ext fuel fs hints maxB cr) Γ₀) hnot
            (List.mem_append_left _ (hsig_eq ▸ List.mem_map_of_mem hg)) horig
        · exact hstep cs (fs.map Fn.sig ++ extSigs)
            (Chunk.sem extSigs (.recSCC ext fuel fs hints maxB cr) Γ₀) hnot
            (List.mem_append_right _ hex) horig

/-- Introduce `Chunk.sem` for a `.recSCC` chunk from `DepthEnv.semScc` at any depth `d ≤ fuel`. -/
theorem recChunk_sem_of_depth {extCallees : List (SigEntry × Nat)} {fuel : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxB : Nat}
    (cr : CompiledRec T lt extCallees exits nX fuel fs hints maxB)
    {extSigs : List SigEntry} {Γ₀ : Env} {f : Fn} (hf : f ∈ fs) {d : Nat} (hd : d ≤ fuel)
    {xs : Tup Val f.as} {m : Mem 64} {Q : Post f.rs} {X : XPost}
    (hsem : DepthEnv.semScc ⟨fs, externsOfSigs extSigs, exits⟩ Γ₀ d
      f.name f.as f.rs xs m Q X) :
    (Chunk.recSCC extCallees fuel fs hints maxB cr).sem extSigs Γ₀
      f.name f.as f.rs xs m Q X :=
  Or.inl ⟨List.mem_map_of_mem hf,
    DepthEnv.semScc_depth_mono ⟨fs, externsOfSigs extSigs, exits⟩ Γ₀ hd
      f.name f.as f.rs xs m Q X hsem⟩

/-- Introduce `Chunk.sem` for an `.acyc` chunk from `Env.semScc`. -/
theorem acycChunk_sem_of_semScc (cc : CompiledChunk T lt exits nX)
    {extSigs : List SigEntry} {Γ₀ : Env} {f : Fn} (hf : f ∈ cc.fs)
    {xs : Tup Val f.as} {m : Mem 64} {Q : Post f.rs} {X : XPost}
    (hsem : Env.semScc ⟨cc.fs, externsOfSigs extSigs, exits⟩ Γ₀
      f.name f.as f.rs xs m Q X) :
    (Chunk.acyc cc).sem extSigs Γ₀ f.name f.as f.rs xs m Q X :=
  Or.inl ⟨List.mem_map_of_mem hf, hsem⟩

/-! ### Concrete `TargetInit` `Eventually` lifts -/

section ConcreteInit

variable {maxStack maxMem : Nat}

/-- Run `nm` in `cert.host` from `I.initState (cert.bound nm) bsMem args` using `hf`. -/
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
      (T.mach.mkState (I.initState (cert.bound nm) bsMem args)
        (T.mach.labelAddr cert.host nm)) := by
  have hmem := I.mem_entry (cert.bound nm) bsMem args
    (Nat.le_trans (cert.bound_le_max nm) hbound) hbs
  rw [← I.get_sp (cert.bound nm) bsMem args] at hmem
  refine eventually_weaken _ _ _ _ ?_ (hf args (bsMem.At 0x1000#64) Q X hspec
    (I.initState (cert.bound nm) bsMem args) I.ra0 Std.ExtHashMap.emp (I.argsIn _ _ _ hargs)
    (I.raReg _ _ _) (by rw [I.get_sp]; exact I.spEntry) hmem)
  rintro st (⟨hpc, rets, m', hQ, hrets, _, hm'⟩ | ⟨sym', cs, xs, m', hX, _, hpc, has, _⟩)
  · rw [I.get_sp] at hm'; exact hpost st (Or.inl ⟨hpc, rets, m', hQ, hrets, hm'⟩)
  · exact hpost st (Or.inr ⟨sym', cs, xs, m', hX, hpc, has⟩)

/-- Run a non-exiting function returning `(v, ()) : Tup Val [t]` in `cert.host`. -/
theorem run_ret1 (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs)
    (I : TargetInit T maxStack maxMem) {nm : Sym} {as : List Ty} {t : Ty} {spec : Spec as [t]}
    (hf : T.FnSpec cert.host nm spec (cert.bound nm) nX) (bsMem : List UInt8) (args : Tup Val as)
    (v : Val t) (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs as).isSome = true)
    {Q : Post [t]} (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.RetsIn (bs := [t]) (v, ()) (T.mach.data st))
      (T.mach.mkState (I.initState (cert.bound nm) bsMem args)
        (T.mach.labelAddr cert.host nm)) := by
  refine cert.run_fnSpec I hf bsMem args hbs hargs hspec ?_ hbound
  rintro st (⟨hpc, rets, m', hq, hrets, _⟩ | ⟨_, _, _, _, hx, _⟩)
  · have hr := hQ rets m' hq; subst hr; exact ⟨hpc, hrets⟩
  · exact hx.elim

/-- `i64` specialization of `run_ret1` projecting directly to `I.ret0`. -/
theorem run_ret1_i64 (cert : LinkedCertScc T L lt hcl mod ext₀ exits nX maxBound extSigs)
    (I : TargetInit T maxStack maxMem) {nm : Sym} {as : List Ty} {spec : Spec as [i64]}
    (hf : T.FnSpec cert.host nm spec (cert.bound nm) nX) (bsMem : List UInt8) (args : Tup Val as)
    (v : Val i64) (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs as).isSome = true)
    {Q : Post [i64]} (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v)
      (T.mach.mkState (I.initState (cert.bound nm) bsMem args)
        (T.mach.labelAddr cert.host nm)) :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, I.retsIn_singleton v _ h.2⟩)
    (cert.run_ret1 I hf bsMem args v hbs hargs hspec hQ hbound)

/-- Closed end-to-end `Eventually` theorem from `cert.sem` to `cert.host` execution for any
non-exiting `i64`-returning function `f ∈ mod.fns` (`ext₀ = []`, `extSigs = []`). -/
theorem eventually_ret1_i64_of_le
    (cert : LinkedCertScc T L lt hcl mod [] exits nX maxBound [])
    (I : TargetInit T maxStack maxMem) (hwf : ∀ f ∈ mod.fns, f.Wf)
    {f : Fn} (hf : f ∈ mod.fns) (hret : f.rs = [i64])
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (spec : Spec f.as [i64])
    (hnoex : ∀ args m Q X X', spec args m Q X → spec args m Q X')
    (hle : ∀ args m Q X, spec args m Q X →
      cert.sem (fun _ _ _ _ _ _ _ => False) f.name f.as [i64] args m Q X)
    (bsMem : List UInt8) (args : Tup Val f.as) (v : Val i64)
    (hbs : bsMem.length ≤ maxMem) (hargs : (T.toIsa.assignArgs f.as).isSome = true)
    {Q : Post [i64]}
    (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()))
    (hbound : maxBound ≤ maxStack := by omega) :
    Eventually (T.mach.step cert.host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v)
      (T.mach.mkState (I.initState (cert.bound f.name) bsMem args)
        (T.mach.labelAddr cert.host f.name)) := by
  have hfn := (cert.fnSpec_host hwf hf).2
  have hsrc := fnSpec_of_legalEnv_onlyFn has hrs hfn
  rw [hret] at hsrc
  exact cert.run_ret1_i64 I
    (Target.FnSpec.of_spec T hsrc fun args m Q X hs => hle args m Q _ (hnoex args m Q X _ hs))
    bsMem args v hbs hargs hspec hQ hbound

end ConcreteInit

end LinkedCertScc

/-! ## 3. Mixed Acyclic + Cyclic-SCC Meta Evaluator & `compile_linked_scc!` -/

meta section

open Lean Elab Command Meta

/-- Per-leaf slice data inside either an `.acyc` chunk or one `RecSubChunk` of `.recSCC`. -/
structure EvalSccLeaf where
  startIdx : Nat
  fnCount : Nat
  isModuleLast : Bool
  hintsLit : Lean.Expr
  codeLit : Lean.Expr
  baseLit : Lean.Expr
  stepLit : Lean.Expr
  deriving Inhabited

/-- Evaluated chunk data for `compile_linked_scc!`. -/
inductive EvalSccChunk where
  | acyc (startIdx fnCount : Nat) (isModuleLast : Bool)
      (extLit hintsLit codeLit boundsLit : Lean.Expr)
  | recSCC (extLit recSigsLit : Lean.Expr) (fuel : Nat) (subchunks : List EvalSccLeaf)
  deriving Inhabited

/-- Complete meta evaluation output for `compile_linked_scc!`. -/
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

private def SccItem.callsOk {I : Isa} (it : SccItem I) (allowed : List SigEntry) : Bool :=
  it.exitsOk && it.callees.all (fun s => allowed.any (SigEntry.beq s))

private def lookupFuelOpt {I : Isa} (fuels : List (Sym × Nat)) (defaultFuel : Nat)
    (items : List (SccItem I)) : Nat :=
  match items.findSome? fun it => fuels.findSome? fun p =>
      if p.1 == it.name then some p.2 else none with
  | some f => f
  | none => defaultFuel

private def closedPrefixLen {I : Isa} (availSigs : List SigEntry)
    (rest : List (SccItem I)) : Nat :=
  let rec lastCalleeIdx (cals : List SigEntry) : Nat → List (SccItem I) → Nat → Nat
    | _, [], best => best
    | idx, it :: ys, best =>
        let best' := if cals.any (SigEntry.beq it.srcSig) then idx + 1 else best
        lastCalleeIdx cals (idx + 1) ys best'
  let rec expand : Nat → Nat → Nat
    | 0, k => k
    | fuel + 1, k =>
        let pref := rest.take k
        let ownSigs := pref.map (·.srcSig)
        let allowed := availSigs ++ ownSigs
        let missing := pref.foldr (fun it acc =>
          (it.callees.filter fun c => !allowed.any (SigEntry.beq c)) ++ acc) []
        if missing.isEmpty then k
        else
          let need := lastCalleeIdx missing 0 rest k
          if need <= k then k else expand fuel need
  expand (rest.length + 1) 1

private def checkNoNameCollision {I : Isa} (acc : List (SigEntry × Nat))
    (items : List (SccItem I)) : Except String Unit :=
  match items.find? fun it => acc.any (fun p => p.1.1 == it.name) with
  | some it => .error s!"{it.name}: function name collides with external callee"
  | none => .ok ()

private def evalRecItemsBounds (I : Isa) (raBytes : Nat) (recSigs : List SigEntry)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat) :
    List (SccItem I) → Except String (List (SccItem I × Nat × Nat))
  | [] => .ok []
  | it :: rest =>
      match LinkRec.checkAndBoundRecExt I raBytes recSigs extCallees exits nX it.hint it.ext with
      | none => .error s!"{it.name}: unknown callee or undeclared exit"
      | some (bf, sf) => do
          let tail ← evalRecItemsBounds I raBytes recSigs extCallees exits nX rest
          pure ((it, bf, sf) :: tail)

private def splitRecSubchunks {I : Isa} (k maxDirs startIdx : Nat) (isEndAfter : Bool)
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)]
    (xs : List (SccItem I × Nat × Nat)) : List EvalSccLeaf × Nat × Nat :=
  let rec takeSub (cnt dirSum : Nat) (rev : List (SccItem I × Nat × Nat)) :
      List (SccItem I × Nat × Nat) →
      List (SccItem I × Nat × Nat) × List (SccItem I × Nat × Nat)
    | [] => (rev.reverse, [])
    | x :: rest =>
        let nextDirs := dirSum + x.1.code.length
        if cnt < k && (maxDirs == 0 || nextDirs <= maxDirs) then
          takeSub (cnt + 1) nextDirs (x :: rev) rest
        else
          (rev.reverse, x :: rest)
  let rec go : Nat → Nat → Nat → Nat → List (SccItem I × Nat × Nat) →
      List EvalSccLeaf → List EvalSccLeaf × Nat × Nat
    | 0, _, maxB, maxS, _, out => (out.reverse, maxB, maxS)
    | _, _, maxB, maxS, [], out => (out.reverse, maxB, maxS)
    | fuel + 1, idx, maxB, maxS, first :: rest, out =>
        let (grp, rest') := takeSub 1 first.1.code.length [first] rest
        let isLast := isEndAfter && rest'.isEmpty
        let hints := grp.map (·.1.hint)
        let code := grp.foldr (fun x cs => x.1.code ++ cs) []
        let bf := grp.foldr (fun x m => Nat.max x.2.1 m) 0
        let sf := grp.foldr (fun x m => Nat.max x.2.2 m) 0
        let leaf : EvalSccLeaf := {
          startIdx := idx
          fnCount := grp.length
          isModuleLast := isLast
          hintsLit := Lean.toExpr hints
          codeLit := Lean.toExpr code
          baseLit := Lean.toExpr bf
          stepLit := Lean.toExpr sf
        }
        go fuel (idx + grp.length) (Nat.max maxB bf) (Nat.max maxS sf) rest' (leaf :: out)
  go (xs.length + 1) startIdx 0 0 xs []

/-- Parallel meta evaluator partitioning `fs` in order into `.acyc` and `.recSCC` chunks
(with sub-chunks inside `.recSCC`), checking both `Fn.checkCallsOk` closure and stack bounds. -/
def evalLinkedSccChunks (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (extSigs0 : List SigEntry)
    (exits : List Sym) (nX : Nat) (fs : List Fn)
    (chunkSize defaultFuel maxBound maxDirs : Nat) (fuels : List (Sym × Nat))
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] :
    Except String EvalSccModuleData := do
  let k := Nat.max chunkSize 1
  if fs.isEmpty then
    let (code, bounds) ← compileModule I lt raBytes ext0 exits nX [] []
    let extLit := Lean.toExpr ext0
    pure {
      chunks := [.acyc 0 0 true extLit (Lean.toExpr ([] : List I.Hints))
        (Lean.toExpr code) (Lean.toExpr bounds)]
      finalExtLit := extLit
    }
  else
    let tasks := fs.map fun f => Task.spawn fun () =>
      match evalOneFnStage1 I lt f with
      | .error e => .error e
      | .ok (nm, h, mf, ext) =>
        match Rega.lowerFn I h ext mf with
        | .ok c =>
          let cals := f.callees
          let exOk := f.checkCallsOk cals exits
          .ok (SccItem.mk nm f.sig mf.sig h c ext cals exOk)
        | .error e => .error s!"{nm}: {e}"
    let rec collect : List (Task (Except String (SccItem I))) → Except String (List (SccItem I))
      | [] => .ok []
      | t :: ts => do
          let it ← t.get
          let rest ← collect ts
          pure (it :: rest)
    let allItems ← collect tasks
    let emitAcyc (isModLast : Bool) (startIdx : Nat) (chunkExt0 : List (SigEntry × Nat))
        (revGrp : List (SccItem I × Nat)) : EvalSccChunk :=
      let grp := revGrp.reverse
      let hints := grp.map (·.1.hint)
      let code := grp.foldr (fun x cs => x.1.code ++ cs) []
      let bounds := grp.map (fun x => (x.1.name, x.2))
      EvalSccChunk.acyc startIdx grp.length isModLast
        (Lean.toExpr chunkExt0) (Lean.toExpr hints) (Lean.toExpr code) (Lean.toExpr bounds)
    let rec walk (fuel : Nat) (idx : Nat) (availSigs : List SigEntry)
        (chunkExt0 acc : List (SigEntry × Nat)) (acycStart acycDirs : Nat)
        (acycAcc : List (SccItem I × Nat)) (rest : List (SccItem I))
        (out : List EvalSccChunk) : Except String EvalSccModuleData :=
      match fuel with
      | 0 => .ok { chunks := out.reverse, finalExtLit := Lean.toExpr acc }
      | fuel' + 1 =>
          match rest with
          | [] =>
              if acycAcc.isEmpty then
                .ok { chunks := out.reverse, finalExtLit := Lean.toExpr acc }
              else
                let ch := emitAcyc true acycStart chunkExt0 acycAcc
                .ok { chunks := (ch :: out).reverse, finalExtLit := Lean.toExpr acc }
          | it :: tl =>
              if it.callsOk availSigs then
                let curCount := acycAcc.length
                let nextDirs := acycDirs + it.code.length
                if curCount > 0 &&
                    (curCount >= k || (maxDirs > 0 && nextDirs > maxDirs)) then
                  let ch := emitAcyc false acycStart chunkExt0 acycAcc
                  walk fuel' idx availSigs acc acc idx 0 [] rest (ch :: out)
                else do
                  let b ← evalOneFnBoundCheck I raBytes exits nX maxBound acc
                    it.name it.hint it.ext
                  let acycAcc' := (it, b) :: acycAcc
                  let acc' := (it.legalSig, b) :: acc
                  let avail' := it.srcSig :: availSigs
                  if tl.isEmpty then
                    let ch := emitAcyc true acycStart chunkExt0 acycAcc'
                    .ok { chunks := (ch :: out).reverse, finalExtLit := Lean.toExpr acc' }
                  else
                    walk fuel' (idx + 1) avail' chunkExt0 acc' acycStart nextDirs acycAcc' tl out
              else
                let out1 :=
                  if acycAcc.isEmpty then out
                  else emitAcyc false acycStart chunkExt0 acycAcc :: out
                let len := closedPrefixLen availSigs rest
                let sccItems := rest.take len
                let tl' := rest.drop len
                let sccSrcSigs := sccItems.map (·.srcSig)
                let rec? := sccItems.find? fun x =>
                  !x.callsOk (availSigs ++ sccSrcSigs)
                match rec? with
                | some bad => .error s!"{bad.name}: unknown callee or undeclared exit"
                | none => do
                    checkNoNameCollision acc sccItems
                    let recSigs := sccItems.map (·.legalSig)
                    let bounded ← evalRecItemsBounds I raBytes recSigs acc exits nX sccItems
                    let sccFuel := lookupFuelOpt fuels defaultFuel sccItems
                    let (leaves, baseB, stepB) :=
                      splitRecSubchunks k maxDirs idx tl'.isEmpty bounded
                    let totB := baseB + sccFuel * stepB
                    if !Nat.ble totB maxBound || !Nat.ble maxBound (2 ^ 64) ||
                        !Nat.ble (totB + raBytes) (2 ^ 64) then
                      .error s!"recSCC({it.name}): bound {totB} > {maxBound}"
                    else
                      let sccCh := EvalSccChunk.recSCC
                        (Lean.toExpr acc) (Lean.toExpr recSigs) sccFuel leaves
                      let sccSigs := recSigs.map (fun s => (s, totB))
                      let acc2 := sccSigs ++ acc
                      let avail2 := sccSrcSigs ++ availSigs
                      let idx2 := idx + len
                      walk fuel' idx2 avail2 acc2 acc2 idx2 0 [] tl' (sccCh :: out1)
    walk (allItems.length * 2 + 4) 0 extSigs0 ext0 ext0 0 0 [] allItems []

structure CertSccOptions where
  maxBT? : Option Term := none
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
  targE : Lean.Expr
  layoutE : Lean.Expr
  ltE : Lean.Expr
  clE : Lean.Expr
  modE : Lean.Expr
  isaE : Lean.Expr
  raE : Lean.Expr
  labelE : Lean.Expr
  progSmallE : Lean.Expr
  dirTy : Lean.Expr
  listDirTy : Lean.Expr
  listHintsTy : Lean.Expr
  ext0E : Lean.Expr
  extSigsE : Lean.Expr
  exitsE : Lean.Expr
  nXE : Lean.Expr
  maxBE : Lean.Expr
  compileCert : Bool
  compileExt : Bool
  chunks : List EvalSccChunk
  finalExtLit : Lean.Expr

def parseCertSccOptions (optKeys : TSyntaxArray `ident) (optVals : TSyntaxArray `term) :
    CommandElabM CertSccOptions := do
  let mut opts : CertSccOptions := {}
  for i in [:optKeys.size] do
    let k := optKeys[i]!.getId
    let v := optVals[i]!
    match k with
    | `maxBound => opts := { opts with maxBT? := some v }
    | `ext => opts := { opts with extT? := some v }
    | `extSigs => opts := { opts with extSigsT? := some v }
    | `exits => opts := { opts with exitsT? := some v }
    | `nX => opts := { opts with nXT? := some v }
    | `fuel => opts := { opts with fuelT? := some v }
    | `fuels => opts := { opts with fuelsT? := some v }
    | `maxDirs => opts := { opts with maxDirsT? := some v }
    | `compile => opts := { opts with compileT? := some v }
    | `compileExt => opts := { opts with compileExtT? := some v }
    | _ =>
      throwErrorAt optKeys[i]!
        ("compile_linked_scc!: unknown option '{k}'; expected maxBound, ext, extSigs, " ++
          "exits, nX, fuel, fuels, maxDirs, compile, compileExt")
  return opts

def elabAndEvalSccChunks (targT layoutT ltT clT modT : Term) (chunkSize : Nat)
    (opts : CertSccOptions) : TermElabM CertSccInputs := do
  let targE ← Term.elabTerm targT (some (Lean.mkConst ``LeanQbe.T.Target))
  let layoutTy := mkApp (Lean.mkConst ``LeanQbe.T.TargetLayout) targE
  let layoutE ← Term.elabTerm layoutT (some layoutTy)
  let ltE ← Term.elabTerm ltT (some (Lean.mkConst ``LeanQbe.T.LegalTarget))
  let isaE := mkApp (Lean.mkConst ``LeanQbe.T.Target.toIsa) targE
  let clTy := mkApp (Lean.mkConst ``LeanQbe.T.Rega.LabelClean) isaE
  let clE ← Term.elabTerm clT (some clTy)
  let modE ← Term.elabTerm modT (some (Lean.mkConst ``LeanQbe.T.Module))
  let sigTy := Lean.mkConst ``LeanQbe.T.SigEntry
  let listSigTy := mkApp (Lean.mkConst ``List [.zero]) sigTy
  let sigEntryNatTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) sigTy (Lean.mkConst ``Nat)
  let listExtTy := mkApp (Lean.mkConst ``List [.zero]) sigEntryNatTy
  let symTy := Lean.mkConst ``LeanQbe.T.Sym
  let listSymTy := mkApp (Lean.mkConst ``List [.zero]) symTy
  let symNatTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) symTy (Lean.mkConst ``Nat)
  let listSymNatTy := mkApp (Lean.mkConst ``List [.zero]) symNatTy
  let ext0E ← match opts.extT? with
    | some t => Term.elabTerm t (some listExtTy)
    | none => pure (mkApp (Lean.mkConst ``List.nil [.zero]) sigEntryNatTy)
  let extSigsE ← match opts.extSigsT? with
    | some t => Term.elabTerm t (some listSigTy)
    | none => pure (mkApp4 (Lean.mkConst ``List.map [.zero, .zero])
        (Lean.mkConst ``LeanQbe.T.Extern) sigTy (Lean.mkConst ``LeanQbe.T.Extern.sig)
        (mkApp (Lean.mkConst ``LeanQbe.T.Module.externs) modE))
  let exitsE ← match opts.exitsT? with
    | some t => Term.elabTerm t (some listSymTy)
    | none => pure (mkApp (Lean.mkConst ``List.nil [.zero]) symTy)
  let nXE ← match opts.nXT? with
    | some t => Term.elabTerm t (some (Lean.mkConst ``Nat))
    | none => pure (mkNatLit 0)
  let fuelE ← match opts.fuelT? with
    | some t => Term.elabTerm t (some (Lean.mkConst ``Nat))
    | none => pure (mkNatLit 16)
  let fuelsE ← match opts.fuelsT? with
    | some t => Term.elabTerm t (some listSymNatTy)
    | none => pure (mkApp (Lean.mkConst ``List.nil [.zero]) symNatTy)
  let maxBE ← match opts.maxBT? with
    | some t => Term.elabTerm t (some (Lean.mkConst ``Nat))
    | none => pure (mkNatLit 2048)
  let maxDirsE ← match opts.maxDirsT? with
    | some t => Term.elabTerm t (some (Lean.mkConst ``Nat))
    | none => pure (mkNatLit 0)
  let compileCert ← evalBoolOpt opts.compileT? false
  let compileExt ← evalBoolOpt opts.compileExtT? false
  Term.synthesizeSyntheticMVarsNoPostponing
  let targE ← instantiateMVars targE
  let layoutE ← instantiateMVars layoutE
  let ltE ← instantiateMVars ltE
  let clE ← instantiateMVars clE
  let modE ← instantiateMVars modE
  let isaE ← instantiateMVars isaE
  let ext0E ← instantiateMVars ext0E
  let extSigsE ← instantiateMVars extSigsE
  let exitsE ← instantiateMVars exitsE
  let nXE ← instantiateMVars nXE
  let fuelE ← instantiateMVars fuelE
  let fuelsE ← instantiateMVars fuelsE
  let maxBE ← instantiateMVars maxBE
  let maxDirsE ← instantiateMVars maxDirsE
  let regTy ← whnf (mkApp (Lean.mkConst ``LeanQbe.T.Isa.Reg) isaE)
  let vregTy ← whnf (mkApp (Lean.mkConst ``LeanQbe.T.Isa.VReg) isaE)
  let condTy ← whnf (mkApp (Lean.mkConst ``LeanQbe.T.Isa.Cond) isaE)
  let hintTy := mkApp3 (Lean.mkConst ``LeanQbe.T.Hints) regTy vregTy condTy
  let listHintsConcreteTy := mkApp (Lean.mkConst ``List [.zero]) hintTy
  let dirConcreteTy ← whnf (mkApp (Lean.mkConst ``LeanQbe.T.Isa.Directive) isaE)
  let listDirConcreteTy := mkApp (Lean.mkConst ``List [.zero]) dirConcreteTy
  let toExprHintsInst ← synthInstance
    (mkApp (Lean.mkConst ``Lean.ToExpr [.zero]) listHintsConcreteTy)
  let toExprDirInst ← synthInstance
    (mkApp (Lean.mkConst ``Lean.ToExpr [.zero]) listDirConcreteTy)
  let frameE ← mkAppM ``LeanQbe.T.Isa.frame #[isaE]
  let raE ← mkAppM ``LeanQbe.T.FrameIsa.raBytes #[frameE]
  let labelE ← mkAppM ``LeanQbe.T.FrameIsa.label #[frameE]
  let progSmallE ← mkAppM ``LeanQbe.T.TargetLayout.progSmall #[layoutE]
  let fnsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) modE
  let callE ← instantiateMVars (mkAppN (Lean.mkConst ``LeanQbe.T.evalLinkedSccChunks)
    #[isaE, ltE, raE, ext0E, extSigsE, exitsE, nXE, fnsE, mkNatLit chunkSize,
      fuelE, maxBE, maxDirsE, fuelsE, toExprHintsInst, toExprDirInst])
  let outTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero]) (Lean.mkConst ``String)
    (Lean.mkConst ``LeanQbe.T.EvalSccModuleData)
  let evalRes ← unsafe evalExpr (Except String EvalSccModuleData) outTy callE
  let modData ← match evalRes with
    | .error e => throwError "compile_linked_scc!: {e}"
    | .ok md => pure md
  let dirTy := mkApp (Lean.mkConst ``LeanQbe.T.Isa.Directive) isaE
  let listDirTy := mkApp (Lean.mkConst ``List [.zero]) dirTy
  let listHintsTy := mkApp (Lean.mkConst ``List [.zero])
    (mkApp (Lean.mkConst ``LeanQbe.T.Isa.Hints) isaE)
  return {
    targE, layoutE, ltE, clE, modE, isaE, raE, labelE, progSmallE,
    dirTy, listDirTy, listHintsTy, ext0E, extSigsE, exitsE, nXE, maxBE,
    compileCert, compileExt,
    chunks := modData.chunks, finalExtLit := modData.finalExtLit
  }

private structure EmittedLeafNames where
  leaf : EvalSccLeaf
  fnsNm : Name
  hintsNm : Name
  codeNm : Name
  baseNm : Name
  stepNm : Name
  cmAuxNm : Name
  suppNm : Name
  subNm : Name
  deriving Inhabited

private inductive EmittedChunkMeta where
  | acyc (startIdx fnCount : Nat) (fnsNm hintsNm extNm codeNm boundsNm : Name)
      (cmNm metaNm suppNm compNm : Name)
  | recSCC (extNm recSigsNm scsNm chkNm chunkNm : Name) (fuel : Nat)
      (leaves : Array EmittedLeafNames)
  deriving Inhabited

/-- `compile_linked_scc! certName target layout legalTarget labelClean mod chunkSize
[(maxBound := ...)] [(ext := ...)] [(extSigs := ...)] [(exits := ...)] [(nX := ...)]
[(fuel := ...)] [(fuels := ...)] [(maxDirs := ...)] [(compile := ...)] [(compileExt := ...)]`
partitions `mod.fns` in list order into `.acyc` spans and closed `.recSCC` SCC chunks, splits
large SCCs into `RecSubChunk`s capped at `chunkSize` / `maxDirs`, checks per-leaf theorems in
parallel via the kernel, links all chunks via `checkLinkSccList` + `checkChunksCalls`, and
defines `certName : LinkedCertScc ...` with `std3` axioms only. -/
scoped syntax "compile_linked_scc! " ident
    term:arg term:arg term:arg term:arg term:arg num
    ("(" ident " := " term ")")* : command

scoped elab_rules : command
  | `(compile_linked_scc! $certId $targT $layoutT $ltT $clT $modT $chunkSizeLit
      $[($optKeys := $optVals)]*) => do
    let ns ← getCurrNamespace
    let certNm := ns ++ certId.getId
    let auxNs := certNm ++ `aux
    let opts ← parseCertSccOptions optKeys optVals
    let inp ← liftTermElabM <|
      elabAndEvalSccChunks targT layoutT ltT clT modT chunkSizeLit.getNat opts
    let fnTy := Lean.mkConst ``LeanQbe.T.Fn
    let listFnTy := mkApp (Lean.mkConst ``List [1]) fnTy
    let symTy := Lean.mkConst ``LeanQbe.T.Sym
    let sigTy := Lean.mkConst ``LeanQbe.T.SigEntry
    let listSigTy := mkApp (Lean.mkConst ``List [.zero]) sigTy
    let natTy := Lean.mkConst ``Nat
    let sigEntryNatTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) sigTy natTy
    let listExtTy := mkApp (Lean.mkConst ``List [.zero]) sigEntryNatTy
    let symNatTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) symTy natTy
    let listBoundsTy := mkApp (Lean.mkConst ``List [.zero]) symNatTy
    let acycPairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) inp.listDirTy listBoundsTy
    let acycExcTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero])
      (Lean.mkConst ``String) acycPairTy
    let recTripleTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) inp.listDirTy
      (mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) natTy natTy)
    let recExcTy := mkApp2 (Lean.mkConst ``Except [.zero, .zero])
      (Lean.mkConst ``String) recTripleTy
    let fnsBaseE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) inp.modE
    -- Pass 1: emit pure literal definitions for all `.acyc` chunks and `.recSCC` sub-chunks.
    let mut emitted : Array EmittedChunkMeta := #[]
    let mut ci : Nat := 0
    for ch in inp.chunks do
      let pfx := s!"c{ci}"
      match ch with
      | .acyc startIdx fnCount isLast extLit hintsLit codeLit boundsLit =>
          let fnsNm := auxNs ++ Name.mkSimple s!"{pfx}_fns"
          let hintsNm := auxNs ++ Name.mkSimple s!"{pfx}_hints"
          let extNm := auxNs ++ Name.mkSimple s!"{pfx}_ext"
          let codeNm := auxNs ++ Name.mkSimple s!"{pfx}_code"
          let boundsNm := auxNs ++ Name.mkSimple s!"{pfx}_bounds"
          let dropE := mkApp3 (Lean.mkConst ``List.drop [1]) fnTy (mkNatLit startIdx) fnsBaseE
          let sliceE :=
            if isLast then dropE
            else mkApp3 (Lean.mkConst ``List.take [1]) fnTy (mkNatLit fnCount) dropE
          liftCoreM do
            addCertDef fnsNm listFnTy sliceE inp.compileCert
            addCertDef hintsNm inp.listHintsTy hintsLit inp.compileCert
            addCertDef extNm listExtTy extLit inp.compileCert
            addCertDef codeNm inp.listDirTy codeLit inp.compileCert
            addCertDef boundsNm listBoundsTy boundsLit inp.compileCert
          emitted := emitted.push (.acyc startIdx fnCount fnsNm hintsNm extNm codeNm boundsNm
            (auxNs ++ Name.mkSimple s!"{pfx}_cm") (auxNs ++ Name.mkSimple s!"{pfx}_meta")
            (auxNs ++ Name.mkSimple s!"{pfx}_supp") (auxNs ++ Name.mkSimple s!"{pfx}_compiled"))
      | .recSCC extLit recSigsLit fuel leaves =>
          let extNm := auxNs ++ Name.mkSimple s!"{pfx}_ext"
          let recSigsNm := auxNs ++ Name.mkSimple s!"{pfx}_recsigs"
          liftCoreM do
            addCertDef extNm listExtTy extLit inp.compileCert
            addCertDef recSigsNm listSigTy recSigsLit inp.compileCert
          let mut leafArr : Array EmittedLeafNames := #[]
          let mut sj : Nat := 0
          for lf in leaves do
            let spfx := s!"{pfx}_s{sj}"
            let fnsNm := auxNs ++ Name.mkSimple s!"{spfx}_fns"
            let hintsNm := auxNs ++ Name.mkSimple s!"{spfx}_hints"
            let codeNm := auxNs ++ Name.mkSimple s!"{spfx}_code"
            let baseNm := auxNs ++ Name.mkSimple s!"{spfx}_base"
            let stepNm := auxNs ++ Name.mkSimple s!"{spfx}_step"
            let dropE := mkApp3 (Lean.mkConst ``List.drop [1])
              fnTy (mkNatLit lf.startIdx) fnsBaseE
            let sliceE :=
              if lf.isModuleLast then dropE
              else mkApp3 (Lean.mkConst ``List.take [1]) fnTy (mkNatLit lf.fnCount) dropE
            liftCoreM do
              addCertDef fnsNm listFnTy sliceE inp.compileCert
              addCertDef hintsNm inp.listHintsTy lf.hintsLit inp.compileCert
              addCertDef codeNm inp.listDirTy lf.codeLit inp.compileCert
              addCertDef baseNm natTy lf.baseLit inp.compileCert
              addCertDef stepNm natTy lf.stepLit inp.compileCert
            leafArr := leafArr.push {
              leaf := lf, fnsNm, hintsNm, codeNm, baseNm, stepNm
              cmAuxNm := auxNs ++ Name.mkSimple s!"{spfx}_cm"
              suppNm := auxNs ++ Name.mkSimple s!"{spfx}_supp"
              subNm := auxNs ++ Name.mkSimple s!"{spfx}_sub"
            }
            sj := sj + 1
          emitted := emitted.push (.recSCC extNm recSigsNm
            (auxNs ++ Name.mkSimple s!"{pfx}_scs") (auxNs ++ Name.mkSimple s!"{pfx}_chk")
            (auxNs ++ Name.mkSimple s!"{pfx}_chunk") fuel leafArr)
      ci := ci + 1
    -- Pass 2: queue all per-chunk and per-subchunk kernel theorems in parallel.
    for em in emitted do
      match em with
      | .acyc _ _ fnsNm hintsNm extNm codeNm boundsNm cmNm metaNm suppNm _ =>
          let cmLhs := mkAppN (Lean.mkConst ``LeanQbe.T.compileModule)
            #[inp.isaE, inp.ltE, inp.raE, Lean.mkConst extNm, inp.exitsE, inp.nXE,
              Lean.mkConst fnsNm, Lean.mkConst hintsNm]
          let cmRhs := mkApp3 (Lean.mkConst ``Except.ok [.zero, .zero])
            (Lean.mkConst ``String) acycPairTy
            (mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) inp.listDirTy listBoundsTy
              (Lean.mkConst codeNm) (Lean.mkConst boundsNm))
          liftCoreM <| addKernelEqThm cmNm acycExcTy cmLhs cmRhs .zero
          let fnNamesE := mkApp4 (Lean.mkConst ``List.map [1, .zero])
            fnTy symTy (Lean.mkConst ``LeanQbe.T.Fn.name) (Lean.mkConst fnsNm)
          let metaLhs := mkAppN (Lean.mkConst ``LeanQbe.T.checkCompileLit)
            #[inp.dirTy, inp.labelE, inp.progSmallE, Lean.mkConst codeNm, Lean.mkConst boundsNm,
              fnNamesE, inp.exitsE, inp.maxBE]
          liftCoreM <| addKernelEqThm metaNm (Lean.mkConst ``Bool)
            metaLhs (Lean.mkConst ``Bool.true) .zero
          let suppLhs := mkApp2 (Lean.mkConst ``LeanQbe.T.checkSupportsChunk)
            inp.ltE (Lean.mkConst fnsNm)
          liftCoreM <| addKernelEqThm suppNm (Lean.mkConst ``Bool)
            suppLhs (Lean.mkConst ``Bool.true) .zero
      | .recSCC extNm recSigsNm _ _ _ _ leaves =>
          for lfn in leaves do
            let cmLhs := mkAppN (Lean.mkConst ``LeanQbe.T.LinkRec.compileModuleRecAux)
              #[inp.isaE, inp.ltE, inp.raE, Lean.mkConst recSigsNm, Lean.mkConst extNm,
                inp.exitsE, inp.nXE, Lean.mkConst lfn.fnsNm, Lean.mkConst lfn.hintsNm]
            let stepPair := mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero])
              natTy natTy (Lean.mkConst lfn.baseNm) (Lean.mkConst lfn.stepNm)
            let pairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) natTy natTy
            let cmRhs := mkApp3 (Lean.mkConst ``Except.ok [.zero, .zero])
              (Lean.mkConst ``String) recTripleTy
              (mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) inp.listDirTy pairTy
                (Lean.mkConst lfn.codeNm) stepPair)
            liftCoreM <| addKernelEqThm lfn.cmAuxNm recExcTy cmLhs cmRhs .zero
            let suppLhs := mkApp2 (Lean.mkConst ``LeanQbe.T.checkSupportsChunk)
              inp.ltE (Lean.mkConst lfn.fnsNm)
            liftCoreM <| addKernelEqThm lfn.suppNm (Lean.mkConst ``Bool)
              suppLhs (Lean.mkConst ``Bool.true) .zero
    -- Pass 3: assemble `.acyc` and `.recSCC` `Chunk` entries and validate link/call checks.
    let chunkTy := mkAppN (Lean.mkConst ``LeanQbe.T.Chunk)
      #[inp.targE, inp.ltE, inp.exitsE, inp.nXE]
    let mut chunkEntries : Array Lean.Expr := #[]
    for em in emitted do
      match em with
      | .acyc _ _ fnsNm hintsNm extNm codeNm boundsNm cmNm metaNm _ compNm =>
          let compTy := mkAppN (Lean.mkConst ``LeanQbe.T.Compiled)
            #[inp.targE, inp.ltE, Lean.mkConst extNm, inp.exitsE, inp.nXE,
              Lean.mkConst fnsNm, Lean.mkConst hintsNm, inp.maxBE]
          let compVal := mkAppN (Lean.mkConst ``LeanQbe.T.compileCheckedLit)
            #[inp.targE, inp.layoutE, inp.ltE, inp.clE, Lean.mkConst extNm, inp.exitsE, inp.nXE,
              Lean.mkConst fnsNm, Lean.mkConst hintsNm, inp.maxBE,
              Lean.mkConst codeNm, Lean.mkConst boundsNm, Lean.mkConst cmNm, Lean.mkConst metaNm]
          liftCoreM <| addCertDef compNm compTy compVal inp.compileCert
          let ccVal := mkAppN (Lean.mkConst ``LeanQbe.T.CompiledChunk.mk)
            #[inp.targE, inp.ltE, inp.exitsE, inp.nXE, Lean.mkConst extNm, Lean.mkConst fnsNm,
              Lean.mkConst hintsNm, inp.maxBE, Lean.mkConst compNm]
          let chunkVal := mkAppN (Lean.mkConst ``LeanQbe.T.Chunk.acyc)
            #[inp.targE, inp.ltE, inp.exitsE, inp.nXE, ccVal]
          chunkEntries := chunkEntries.push chunkVal
      | .recSCC extNm recSigsNm scsNm chkNm chunkNm fuel leaves =>
          let subTy := mkAppN (Lean.mkConst ``LeanQbe.T.RecSubChunk)
            #[inp.targE, inp.ltE, Lean.mkConst recSigsNm, Lean.mkConst extNm, inp.exitsE, inp.nXE]
          let listSubTy := mkApp (Lean.mkConst ``List [1]) subTy
          let mut subConsts : List Lean.Expr := []
          for lfn in leaves do
            let subVal := mkAppN (Lean.mkConst ``LeanQbe.T.RecSubChunk.mk)
              #[inp.targE, inp.ltE, Lean.mkConst recSigsNm, Lean.mkConst extNm, inp.exitsE, inp.nXE,
                Lean.mkConst lfn.fnsNm, Lean.mkConst lfn.hintsNm, Lean.mkConst lfn.codeNm,
                Lean.mkConst lfn.baseNm, Lean.mkConst lfn.stepNm, Lean.mkConst lfn.cmAuxNm]
            liftCoreM <| addCertDef lfn.subNm subTy subVal inp.compileCert
            subConsts := subConsts ++ [Lean.mkConst lfn.subNm]
          let scsVal := subConsts.foldr
            (fun sc acc => mkApp3 (Lean.mkConst ``List.cons [1]) subTy sc acc)
            (mkApp (Lean.mkConst ``List.nil [1]) subTy)
          liftCoreM <| addCertDef scsNm listSubTy scsVal inp.compileCert
          let fuelE := mkNatLit fuel
          let chkLhs := mkAppN (Lean.mkConst ``LeanQbe.T.checkRecSubchunks)
            #[inp.targE, inp.layoutE, inp.ltE, Lean.mkConst recSigsNm, Lean.mkConst extNm,
              inp.exitsE, inp.nXE, fuelE, inp.maxBE, Lean.mkConst scsNm]
          liftCoreM <| addKernelEqThm chkNm (Lean.mkConst ``Bool)
            chkLhs (Lean.mkConst ``Bool.true) .zero
          let chunkVal := mkAppN (Lean.mkConst ``LeanQbe.T.Chunk.ofRecSubchunks)
            #[inp.targE, inp.ltE, inp.exitsE, inp.nXE, inp.layoutE, inp.clE,
              Lean.mkConst recSigsNm, Lean.mkConst extNm, fuelE, inp.maxBE,
              Lean.mkConst scsNm, Lean.mkConst chkNm]
          liftCoreM <| addCertDef chunkNm chunkTy chunkVal inp.compileCert
          chunkEntries := chunkEntries.push (Lean.mkConst chunkNm)
    let listChunkTy := mkApp (Lean.mkConst ``List [1]) chunkTy
    let chunksVal := chunkEntries.toList.foldr
      (fun c acc => mkApp3 (Lean.mkConst ``List.cons [1]) chunkTy c acc)
      (mkApp (Lean.mkConst ``List.nil [1]) chunkTy)
    let chunksNm := auxNs ++ `chunks
    liftCoreM <| addCertDef chunksNm listChunkTy chunksVal inp.compileCert
    let linkCheckNm := auxNs ++ `link_check
    let linkLhs := mkAppN (Lean.mkConst ``LeanQbe.T.checkLinkSccList)
      #[inp.targE, inp.layoutE, inp.ltE, inp.exitsE, inp.nXE, inp.ext0E, Lean.mkConst chunksNm]
    liftCoreM <| addKernelEqThm linkCheckNm (Lean.mkConst ``Bool)
      linkLhs (Lean.mkConst ``Bool.true) .zero
    let callsCheckNm := auxNs ++ `calls_check
    let callsLhs := mkAppN (Lean.mkConst ``LeanQbe.T.checkChunksCalls)
      #[inp.targE, inp.ltE, inp.nXE, inp.exitsE, inp.extSigsE, Lean.mkConst chunksNm]
    liftCoreM <| addKernelEqThm callsCheckNm (Lean.mkConst ``Bool)
      callsLhs (Lean.mkConst ``Bool.true) .zero
    -- Pass 4: build O(#subchunks) proofs of `fns_eq`, `supportsAll`, and `maxBound_le`.
    let fnsEqNm := auxNs ++ `fns_eq
    let suppAllNm := auxNs ++ `supportsAll
    let maxBLeNm := auxNs ++ `maxBound_le
    let sccChunksFnsE := mkAppN (Lean.mkConst ``LeanQbe.T.sccChunksFns)
      #[inp.targE, inp.ltE, inp.exitsE, inp.nXE, Lean.mkConst chunksNm]
    let fnsEqTy := mkApp3 (Lean.mkConst ``Eq [2]) listFnTy fnsBaseE sccChunksFnsE
    let mut fnsEqProof : Lean.Expr := default
    let mut restFnsE : Lean.Expr := mkApp (Lean.mkConst ``List.nil [1]) fnTy
    let mut suppProof : Lean.Expr := mkApp (Lean.mkConst ``LeanQbe.T.supportsAll_nil) inp.ltE
    let mut maxBProof : Lean.Expr := mkAppN (Lean.mkConst ``LeanQbe.T.sccChunksMaxBound_nil)
      #[inp.targE, inp.ltE, inp.exitsE, inp.nXE, inp.maxBE]
    let mut restChunksE : Lean.Expr := mkApp (Lean.mkConst ``List.nil [1]) chunkTy
    let nChunks := emitted.size
    for revIdx in [:nChunks] do
      let i := nChunks - 1 - revIdx
      let em := emitted[i]!
      let chunkVal := chunkEntries[i]!
      match em with
      | .acyc startIdx fnCount fnsNm _ _ _ _ _ _ suppNm _ =>
          let curFnsE := Lean.mkConst fnsNm
          if revIdx == 0 then
            fnsEqProof := mkApp3 (Lean.mkConst ``LeanQbe.T.slice_last_eq [1])
              fnTy fnsBaseE (mkNatLit startIdx)
          else
            fnsEqProof := mkApp6 (Lean.mkConst ``LeanQbe.T.slice_cons_eq [1])
              fnTy fnsBaseE restFnsE (mkNatLit startIdx) (mkNatLit fnCount) fnsEqProof
          suppProof := mkApp5 (Lean.mkConst ``LeanQbe.T.supportsAll_append)
            inp.ltE curFnsE restFnsE (Lean.mkConst suppNm) suppProof
          restFnsE := mkApp3 (Lean.mkConst ``List.append [1]) fnTy curFnsE restFnsE
      | .recSCC _ _ _ _ chunkNm _ leaves =>
          let tailFnsE := restFnsE
          let mut curScsFnsE : Lean.Expr := mkApp (Lean.mkConst ``List.nil [1]) fnTy
          let mut curScsSupp : Lean.Expr := mkApp (Lean.mkConst ``LeanQbe.T.supportsAll_nil) inp.ltE
          let nLeaves := leaves.size
          for sRevIdx in [:nLeaves] do
            let j := nLeaves - 1 - sRevIdx
            let lfn := leaves[j]!
            let leafFnsE := Lean.mkConst lfn.fnsNm
            if sRevIdx == 0 then
              if revIdx == 0 then
                fnsEqProof := mkApp3 (Lean.mkConst ``LeanQbe.T.slice_sub_last_mod_eq [1])
                  fnTy fnsBaseE (mkNatLit lfn.leaf.startIdx)
              else
                fnsEqProof := mkAppN (Lean.mkConst ``LeanQbe.T.slice_sub_last_eq [1])
                  #[fnTy, fnsBaseE, tailFnsE, mkNatLit lfn.leaf.startIdx,
                    mkNatLit lfn.leaf.fnCount, fnsEqProof]
            else
              fnsEqProof := mkAppN (Lean.mkConst ``LeanQbe.T.slice_sub_cons_eq [1])
                #[fnTy, fnsBaseE, curScsFnsE, tailFnsE, mkNatLit lfn.leaf.startIdx,
                  mkNatLit lfn.leaf.fnCount, fnsEqProof]
            let leafSuppVal := mkApp3 (Lean.mkConst ``LeanQbe.T.supportsAll_leaf)
              inp.ltE leafFnsE (Lean.mkConst lfn.suppNm)
            curScsSupp := mkApp5 (Lean.mkConst ``LeanQbe.T.supportsAll_append_pred)
              inp.ltE leafFnsE curScsFnsE leafSuppVal curScsSupp
            curScsFnsE := mkApp3 (Lean.mkConst ``List.append [1]) fnTy leafFnsE curScsFnsE
          let chunkFnsE := mkAppN (Lean.mkConst ``LeanQbe.T.Chunk.fns)
            #[inp.targE, inp.ltE, inp.exitsE, inp.nXE, Lean.mkConst chunkNm]
          suppProof := mkApp5 (Lean.mkConst ``LeanQbe.T.supportsAll_append_pred)
            inp.ltE chunkFnsE tailFnsE curScsSupp suppProof
          restFnsE := mkApp3 (Lean.mkConst ``List.append [1]) fnTy chunkFnsE tailFnsE
      maxBProof := mkAppN (Lean.mkConst ``LeanQbe.T.sccChunksMaxBound_cons)
        #[inp.targE, inp.ltE, inp.exitsE, inp.nXE, inp.maxBE, chunkVal, restChunksE,
          mkApp (Lean.mkConst ``Nat.le_refl) inp.maxBE, maxBProof]
      restChunksE := mkApp3 (Lean.mkConst ``List.cons [1]) chunkTy chunkVal restChunksE
    liftCoreM <| addCertThm fnsEqNm fnsEqTy fnsEqProof
    let (suppAllTy, suppAllVal, maxBLeProp) ← liftTermElabM do
      let sVal ← mkAppM ``LeanQbe.T.supportsAll_of_eq #[Lean.mkConst fnsEqNm, suppProof]
      let sTy ← inferType sVal
      let lhs := mkAppN (Lean.mkConst ``LeanQbe.T.sccChunksMaxBound)
        #[inp.targE, inp.ltE, inp.exitsE, inp.nXE, Lean.mkConst chunksNm]
      let mProp ← mkAppM ``LE.le #[lhs, inp.maxBE]
      return (← instantiateMVars sTy, ← instantiateMVars sVal, ← instantiateMVars mProp)
    liftCoreM do
      addCertThm suppAllNm suppAllTy suppAllVal
      addCertThm maxBLeNm maxBLeProp maxBProof
    let certTy := mkAppN (Lean.mkConst ``LeanQbe.T.LinkedCertScc)
      #[inp.targE, inp.layoutE, inp.ltE, inp.clE, inp.modE,
        inp.ext0E, inp.exitsE, inp.nXE, inp.maxBE, inp.extSigsE]
    let certVal := mkAppN (Lean.mkConst ``LeanQbe.T.LinkedCertScc.mk)
      #[inp.targE, inp.layoutE, inp.ltE, inp.clE, inp.modE,
        inp.ext0E, inp.exitsE, inp.nXE, inp.maxBE, inp.extSigsE,
        Lean.mkConst chunksNm, Lean.mkConst linkCheckNm, Lean.mkConst callsCheckNm,
        Lean.mkConst fnsEqNm, Lean.mkConst suppAllNm, Lean.mkConst maxBLeNm]
    liftCoreM do
      addCertDef certNm certTy certVal inp.compileCert
      addCertDef (certNm ++ `exportedExt) listExtTy inp.finalExtLit inp.compileExt

end

end LeanQbe.T
