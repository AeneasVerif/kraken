module

public import LeanQbe.T.MainLink
public import LeanQbe.T.LinkDepthLfp
public import LeanQbe.T.LinkBudgetLfp
import LeanQbe.T.OptLemmas
import LeanQbe.T.LegalLemmas
import LeanQbe.T.RegaLemmas

/-!
# Target-Parameterized SCC Linking & `Chunk.recSCC` Sub-Chunking (`MainLinkScc`)

Target-independent (zero `Kraken.{X64,AArch64}` imports) compositional compilation and linking
over `MainLink`, `LinkLfp`, and `LinkDepthLfp`:
* **Machine/source Galois bridge (`machEnv`, `pullEnv`, `machDepthEnv`):** connects `Target.FnSpec`
  with `DepthEnv.lfp` / `Env.lfp`, yielding `link_scc_depth_lfp` and `link_scc_lfp_zero` via
  one-shot
  `DepthEnv.lfp_le` / `Env.lfp_le` elimination (zero induction over compiler internals).
* **Literal-backed `CompiledRec` (`compileCheckedRecLit`) & SCC sub-chunking (`RecSubChunk`):**
  splits large cyclic SCCs into parallel-checked `compileModuleRecAux` sub-chunks and links them
  into a `CompiledRec` in O(#subchunks) metadata-only time (`linkRecSubchunks`).
* **Mixed acyclic + cyclic `Chunk` / `Chunk.recSCC` linking (`semChunks`, `linkChunks_fnSpec`):**
  validates and links mixed lists of `.acyc` (`CompiledChunk`) and `.recSCC` (`CompiledRec`)
  chunks against a closed canonical semantic environment `semChunks` with zero user `Γ` or `ι`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

open Std Std.ExtHashMap
open LeanQbe.T.LinkRec
open LeanQbe.T.LinkScc

/-! ## 1. `machEnv`, `pullEnv`, `machDepthEnv`, and `DepthEnv.lfp` SCC Linking -/

/-- Target-level machine contract environment at stack bound `n` and exit headroom `nX`.
`T.FnSpec h sym spec n nX` holds iff `spec` implies `machEnv T h n nX sym`. -/
@[expose] def machEnv (T : Target) (h : T.mach.Host) (n nX : Nat) : Env :=
  fun sym _as bs args m Q X =>
    ∀ (s : T.mach.MData) (ra : T.mach.Addr) (R : Mem 64 → Prop),
      T.ArgsIn args s → T.frameSpec.raReg s ra →
      T.frameSpec.spEntry (T.mach.getGpr s T.frame.sp) →
      (T.mach.mem s =⋆ Eq m ⋆ T.Entry (T.mach.getGpr s T.frame.sp) ra n ⋆ R) →
      Eventually (T.mach.step h)
        (fun st =>
          (T.mach.pc st = ra ∧
            ∃ (rets : Tup Val bs) (m' : Mem 64),
              Q rets m' ∧ T.RetsIn rets (T.mach.data st) ∧ T.Restored s (T.mach.data st) ∧
              (T.mach.mem (T.mach.data st) =⋆
                Eq m' ⋆ T.Exit (T.mach.getGpr s T.frame.sp) n ⋆ R)) ∨
          (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64),
            X sym' cs xs m' ∧ T.Defined h sym' ∧ T.mach.pc st = T.mach.labelAddr h sym' ∧
            T.ArgsIn xs (T.mach.data st) ∧
            T.frameSpec.spEntry (T.mach.getGpr (T.mach.data st) T.frame.sp) ∧
            ∃ (ra' : T.mach.Addr) (n' : Nat) (F : Mem 64 → Prop),
              nX ≤ n' ∧ n' + T.frame.raBytes ≤ 2 ^ 64 ∧ T.frameSpec.raReg (T.mach.data st) ra' ∧
              (T.mach.mem (T.mach.data st) =⋆
                Eq m' ⋆ T.Entry (T.mach.getGpr (T.mach.data st) T.frame.sp) ra' n' ⋆ F ⋆ R)))
        (T.mach.mkState s (T.mach.labelAddr h sym))

/-- Pull back a target-typed environment `G` to source signatures via `encodeTup` / `legalPost` /
`legalXPost`. Forms a Galois connection with `legalEnv lt`. -/
@[expose] def pullEnv (lt : LegalTarget) (G : Env) : Env :=
  fun f as bs xs m P E =>
    G f (lt.legalSig as) (lt.legalSig bs) (encodeTup lt as xs) m
      (legalPost lt P) (legalXPost lt E)

/-- Depth-indexed pre-fixpoint candidate `d ↦ pullEnv lt (machEnv T h (base + d * step) nX)`. -/
@[expose] def machDepthEnv (T : Target) (lt : LegalTarget) (h : T.mach.Host)
    (base step nX : Nat) : DepthEnv :=
  fun d => pullEnv lt (machEnv T h (base + d * step) nX)

theorem fnSpec_iff_machEnv {T : Target} {h : T.mach.Host} {sym : Sym} {as bs : List Ty}
    {spec : Spec as bs} {n nX : Nat} :
    T.FnSpec h sym spec n nX ↔
      ∀ args m Q X, spec args m Q X → machEnv T h n nX sym as bs args m Q X :=
  Iff.rfl

theorem machEnv_conseq (T : Target) (h : T.mach.Host) (n nX : Nat) :
    ∀ f as bs xs m (Q Q' : Post bs) (X X' : XPost),
      (∀ r m', Q r m' → Q' r m') → (∀ g cs ys m', X g cs ys m' → X' g cs ys m') →
      machEnv T h n nX f as bs xs m Q X → machEnv T h n nX f as bs xs m Q' X' := by
  intro f as bs xs m Q Q' X X' hQ hX hm s ra R ha hra hsp hmem
  refine eventually_weaken _ _ _ _ ?_ (hm s ra R ha hra hsp hmem)
  rintro st (⟨hpc, rets, m', hq, hrets, hrest, hmem'⟩ |
    ⟨sym', cs, xs', m', hx, hd, hpc, has, hsp', ra', n', F, hn', hb', hra', hmem'⟩)
  · exact Or.inl ⟨hpc, rets, m', hQ rets m' hq, hrets, hrest, hmem'⟩
  · exact Or.inr ⟨sym', cs, xs', m', hX sym' cs xs' m' hx, hd, hpc, has, hsp',
      ra', n', F, hn', hb', hra', hmem'⟩

theorem legalEnv_pullEnv_le (lt : LegalTarget) {G : Env}
    (hconseq : ∀ f as bs xs m (Q Q' : Post bs) (X X' : XPost),
      (∀ r m', Q r m' → Q' r m') → (∀ g cs ys m', X g cs ys m' → X' g cs ys m') →
      G f as bs xs m Q X → G f as bs xs m Q' X') :
    Env.le (legalEnv lt (pullEnv lt G)) G := by
  rintro f as' bs' xs' m Q' X' ⟨as, bs, has, hbs, xs, P, E, hxs, hQ, hX, hpull⟩
  subst has; subst hbs
  have hxs' : encodeTup lt as xs = xs' := by simpa only [cast_eq] using hxs
  have hQ' : ∀ r m₁, legalPost lt P r m₁ → Q' r m₁ := fun r m₁ hp => by
    have := hQ r m₁ hp; rwa [cast_eq] at this
  subst hxs'
  exact hconseq f (lt.legalSig as) (lt.legalSig bs) (encodeTup lt as xs) m
    (legalPost lt P) Q' (legalXPost lt E) X' hQ' hX hpull

private theorem compileFn_body_correct (T : Target) (host : T.mach.Host) (lt : LegalTarget)
    (hints : T.toIsa.Hints) (E : Rega.Ext) (f : Fn) (Γcall : Env)
    (n nX : Nat) (bound : Sym → Nat) {code : List T.Directive} {k₀ : Nat}
    (hwf : f.Wf) (hsupp : (f.earlyOpt).body.supportsSource lt = true)
    (hl : Rega.lowerFn T.toIsa hints E (f.mid lt) = .ok code)
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hfr : Rega.effFrame T.toIsa hints E ≤ n) (hn : n + T.frame.raBytes ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ E.callees →
      T.FnSpec host g (legalEnv lt Γcall g as bs) (bound g) nX ∧
      Rega.effFrame T.toIsa hints E + T.frame.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ E.exits → T.Defined host g ∧ nX ≤ n) :
    ∀ xs m P E', Func.wp Γcall f.body xs m P E' →
      machEnv T host n nX f.name (lt.legalSig f.as) (lt.legalSig f.rs)
        (encodeTup lt f.as xs) m (legalPost lt P) (legalXPost lt E') := by
  intro xs m P E' hwp
  have hspec : T.FnSpec host f.name
      (fun args' m' Q' X' => args' = encodeTup lt f.as xs ∧ m' = m ∧
        Q' = legalPost lt P ∧ X' = legalXPost lt E') n nX := by
    refine Target.FnSpec.of_spec T
      (Rega.lowerFn_correct T host hints E (f.mid lt) (legalEnv lt Γcall) n nX bound
        (fn_mid_wf hwf) hl hc hu hfr hn hcal hex) ?_
    rintro args' m' Q' X' ⟨rfl, hm, rfl, rfl⟩
    subst m'
    exact @fn_mid_spec lt f hwf hsupp Γcall xs (encodeTup lt f.as xs) rfl m P E'
      (legalPost lt P) (legalXPost lt E') (fun _ _ h => h) (fun _ _ _ _ h => h) hwp
  exact hspec (encodeTup lt f.as xs) m (legalPost lt P) (legalXPost lt E') ⟨rfl, rfl, rfl, rfl⟩

private theorem defined_of_lowerFn' {T : Target} {host : T.mach.Host}
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
        cases hb : Rega.bindAbiParams T.toIsa argLocs 0
            { regs := [], slots := .empty, defs := .empty, vecWidths := .empty } with
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

private theorem infix_trans' {α : Type} {a b c : List α} {k₁ k₂ : Nat}
    (hk1 : k₁ ≤ b.length) (h1 : a.IsInfixAt b k₁) (h2 : b.IsInfixAt c k₂) :
    a.IsInfixAt c (k₂ + k₁) := by
  obtain ⟨t1, ht1⟩ := h1
  obtain ⟨t2, ht2⟩ := h2
  refine ⟨t1 ++ t2, ?_⟩
  have hd : (b ++ t2).drop k₁ = b.drop k₁ ++ t2 := by
    rw [List.drop_append, show k₁ - b.length = 0 by omega, List.drop_zero]
  rw [← List.drop_drop, ← ht2, hd, ← ht1, List.append_assoc]

private theorem find?_pred' {α : Type} {p : α → Bool} :
    ∀ {xs : List α} {x : α}, xs.find? p = some x → p x = true
  | [], _, h => by simp at h
  | y :: ys, x, h => by
    simp only [List.find?] at h
    cases hp : p y with
    | true => simp [hp] at h; subst h; exact hp
    | false => simp [hp] at h; exact find?_pred' h

private theorem compileModuleRec_disjoint' {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel maxBound : Nat}
    {fs : List Fn} {hints : List I.Hints} {code : List I.Directive} {base step : Nat}
    (h : compileModuleRec I lt raBytes extCallees exits nX fuel maxBound fs hints =
      .ok (code, base, step)) :
    (∀ p ∈ extCallees, p.1.1 ∉ fs.map Fn.name) ∧
      compileModuleRecAux I lt raBytes
        (fs.map (fun f => (f.name, lt.legalSig f.as, lt.legalSig f.rs)))
        extCallees exits nX fs hints = .ok (code, base, step) := by
  dsimp only [compileModuleRec] at h
  split at h
  · simp at h
  · rename_i hno
    split at h
    · simp at h
    · rename_i code' b' s' haux
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        refine ⟨fun p hp hmem => ?_, haux⟩
        obtain ⟨f, hf, hnm⟩ := List.mem_map.mp hmem
        exact hno (List.any_eq_true.mpr ⟨p, hp, List.any_eq_true.mpr ⟨f, hf, beq_iff_eq.mpr hnm⟩⟩)
      · simp at h

private theorem fn_name_not_mem_externs' {M : Module} (hnd : M.namesNodup)
    {fn : Fn} (hfn : fn ∈ M.fns) {as bs : List Ty} :
    (fn.name, as, bs) ∉ M.externs.map Extern.sig := by
  intro hex
  have hdisj := (List.nodup_append.mp hnd).2.2
  have h1 : fn.name ∈ M.fns.map Fn.name := List.mem_map_of_mem hfn
  obtain ⟨ex, hexm, heq⟩ := List.mem_map.mp hex
  have h2 : ex.name ∈ M.externs.map Extern.name := List.mem_map_of_mem hexm
  exact hdisj fn.name h1 ex.name h2 (congrArg Prod.fst heq).symm

private theorem legalEnv_sccStep_ext {mod : Module} {lt : LegalTarget} {Γrec Γext : Env}
    {g : Sym} (hg : g ∉ mod.fns.map Fn.name)
    {as bs : List Ty} {xs' : Tup Val as} {m0 : Mem 64} {Q' : Post bs} {X' : XPost}
    (h : legalEnv lt (Env.sccStep mod Γrec Γext) g as bs xs' m0 Q' X') :
    legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) g as bs xs' m0 Q' X' := by
  rcases h with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hstep⟩
  rcases hstep with ⟨hsig, _⟩ | ⟨hsig, hΓ⟩
  · obtain ⟨fn, hfn, hfeq⟩ := List.mem_map.mp hsig
    have hnm : fn.name = g := congrArg Prod.fst hfeq
    exact absurd (hnm ▸ List.mem_map_of_mem hfn) hg
  · exact ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hsig, hΓ⟩

private theorem legalEnv_callSlot_ext {mod : Module} {lt : LegalTarget} {Γext : Env}
    {G : DepthEnv} {d : Nat} {g : Sym} (hg : g ∉ mod.fns.map Fn.name)
    {as bs : List Ty} {xs' : Tup Val as} {m0 : Mem 64} {Q' : Post bs} {X' : XPost}
    (h : legalEnv lt (DepthEnv.callSlot mod Γext G d) g as bs xs' m0 Q' X') :
    legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) g as bs xs' m0 Q' X' := by
  cases d with
  | zero => exact h
  | succ _ => exact legalEnv_sccStep_ext hg h

/-- **One-shot `DepthEnv.lfp_le` SCC linking theorem (`link_scc_depth_lfp`):**
proves `T.Defined` and `T.FnSpec` for `DepthEnv.semScc mod Γext d` at stack bound
`M.baseBound + d * M.stepBound` for every `d ≤ fuel`, with zero induction over compiler
internals (ready for Stage 3's `.tailCall` arm). -/
theorem link_scc_depth_lfp {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (h : T.mach.Host)
    (Γext : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hcyc : checkCyclic mod = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1
        (legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hexits : ∀ g ∈ exits, T.Defined h g) :
    ∀ d ≤ fuel, ∀ f ∈ mod.fns, T.Defined h f.name ∧
      T.FnSpec h f.name
        (legalEnv lt (Env.onlyFn f (DepthEnv.semScc mod Γext d)) f.name
          (lt.legalSig f.as) (lt.legalSig f.rs))
        (M.baseBound + d * M.stepBound) nX := by
  have hnd := Module.namesNodup_of_checkNamesNodup ((Bool.and_eq_true _ _).mp hcyc).1
  obtain ⟨hdisj, haux⟩ :=
    compileModuleRec_disjoint' (show compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits
      nX fuel maxBound mod.fns hints = .ok (M.code, M.baseBound, M.stepBound) from
      by rw [hfs]; exact M.compileModuleRec_eq)
  let G : DepthEnv := fun d =>
    if d ≤ fuel then pullEnv lt (machEnv T h (M.baseBound + d * M.stepBound) nX)
    else fun _ _ _ _ _ _ _ => True
  have hpre : DepthEnv.le (DepthEnv.sccOp mod Γext G) G := by
    intro d f as bs xs m P E hΦ
    by_cases hd : d ≤ fuel
    · simp only [G, hd, ↓reduceIte]
      rcases hΦ with ⟨_, fn, hfn, rfl, rfl, rfl, hwp⟩
      obtain ⟨hint, c, k_f, bf, sf, hl, hinf, hklen, hchk, hbf, hsf⟩ :=
        compileModuleRecAux_mem haux fn hfn
      have hc_f : c.IsInfixAt (T.mach.prog h) (k₀ + k_f) := infix_trans' hklen hinf hc
      obtain ⟨hsf_eq, hfr_b, hcal_b, hex_b⟩ := checkAndBoundRecExt_spec hchk
      have hfr_eff : Rega.effFrame T.toIsa hint (fn.mid lt).ext ≤
          M.baseBound + d * M.stepBound :=
        Nat.le_trans (Rega.effFrame_le T.toIsa hint (fn.mid lt).ext)
          (Nat.le_trans hfr_b (Nat.le_trans hbf (Nat.le_add_right _ _)))
      have hn_d : M.baseBound + d * M.stepBound + T.frame.raBytes ≤ 2 ^ 64 :=
        M.total_ra_le_at hd
      let bound : Sym → Nat := fun g =>
        if (mod.fns.map Fn.name).contains g then
          match d with
          | 0 => 0
          | d' + 1 => M.baseBound + d' * M.stepBound
        else
          match extCallees.find? (fun q => q.1.1 == g) with
          | some q => q.2
          | none => 0
      have hcal : ∀ g as' bs', (g, as', bs') ∈ (fn.mid lt).ext.callees →
          T.FnSpec h g (legalEnv lt (DepthEnv.callSlot mod Γext G d) g as' bs') (bound g) nX ∧
          Rega.effFrame T.toIsa hint (fn.mid lt).ext + T.frame.raBytes + bound g ≤
            M.baseBound + d * M.stepBound := by
        intro g as' bs' hg
        rcases hcal_b (g, as', bs') hg with ⟨hrec_sig, hstep_b⟩ | ⟨_, bg, hlk, hbg_b⟩
        · obtain ⟨gfn, hgfn, hgeq⟩ := List.mem_map.mp hrec_sig
          rcases Prod.mk.inj hgeq with ⟨rfl, hsig_ab⟩
          rcases Prod.mk.inj hsig_ab with ⟨rfl, rfl⟩
          have hmem_nm : gfn.name ∈ mod.fns.map Fn.name := List.mem_map_of_mem hgfn
          have hcon : (mod.fns.map Fn.name).contains gfn.name = true := by simpa using hmem_nm
          cases d with
          | zero =>
              have hbd0 : bound gfn.name = 0 := by
                dsimp only [bound]; simp only [hcon, ↓reduceIte]
              rw [hbd0]
              refine ⟨?_, ?_⟩
              · intro args' m0 Q' X' hleg
                rcases hleg with ⟨_, _, _, _, _, _, _, _, _, _, hmemE, _⟩
                exact absurd hmemE (fn_name_not_mem_externs' hnd hgfn)
              · have hle_f := Rega.effFrame_le T.toIsa hint (fn.mid lt).ext
                have := Nat.le_trans (Nat.add_le_add_right hle_f _) hstep_b
                exact Nat.le_trans this (Nat.le_trans hbf (Nat.le_add_right _ _))
          | succ d' =>
              have hd' : d' ≤ fuel := Nat.le_trans (Nat.le_succ d') hd
              have hbd' : bound gfn.name = M.baseBound + d' * M.stepBound := by
                dsimp only [bound]; simp only [hcon, ↓reduceIte]
              rw [hbd']
              refine ⟨?_, ?_⟩
              · intro args' m0 Q' X' hleg
                have hpull : legalEnv lt
                    (pullEnv lt (machEnv T h (M.baseBound + d' * M.stepBound) nX))
                    gfn.name (lt.legalSig gfn.as) (lt.legalSig gfn.rs) args' m0 Q' X' := by
                  rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hst⟩
                  rcases hst with ⟨_, hG⟩ | ⟨hmemE, _⟩
                  · simp only [G, hd', ↓reduceIte] at hG
                    exact ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hG⟩
                  · exact absurd hmemE (fn_name_not_mem_externs' hnd hgfn)
                exact legalEnv_pullEnv_le lt (machEnv_conseq T h _ nX)
                  gfn.name _ _ args' m0 Q' X' hpull
              · have hfr_sf : Rega.effFrame T.toIsa hint (fn.mid lt).ext + T.frame.raBytes ≤
                    M.stepBound := by
                  have htmp := Nat.add_le_add_right (Rega.effFrame_le T.toIsa hint (fn.mid lt).ext)
                    T.frame.raBytes
                  rw [← hsf_eq] at htmp; exact Nat.le_trans htmp hsf
                rw [Nat.succ_mul]
                omega
        · have hmem_ext : ((g, as', bs'), bg) ∈ extCallees := lookupBound_mem hlk
          have hnot_nm : g ∉ mod.fns.map Fn.name := hdisj ((g, as', bs'), bg) hmem_ext
          have hcon : (mod.fns.map Fn.name).contains g = false := by
            simpa [List.contains_eq_mem] using hnot_nm
          have hbd : bound g = bg := by
            dsimp only [bound]; rw [hcon]
            simp only [Bool.false_eq_true, ↓reduceIte]
            cases hfnd : extCallees.find? (fun q => q.1.1 == g) with
            | none =>
                exfalso
                have hnot := List.find?_eq_none.mp hfnd ((g, as', bs'), bg) hmem_ext
                simp at hnot
            | some q =>
                have hqmem : q ∈ extCallees := List.mem_of_find?_eq_some hfnd
                have hpred : q.1.1 = g :=
                  beq_iff_eq.mp (find?_pred' (p := fun q : SigEntry × Nat => q.1.1 == g) hfnd)
                exact hext_uniq q hqmem ((g, as', bs'), bg) hmem_ext hpred
          rw [hbd]
          refine ⟨?_, ?_⟩
          · exact Target.FnSpec.of_spec T (hext ((g, as', bs'), bg) hmem_ext)
              fun _ _ _ _ hleg => legalEnv_callSlot_ext hnot_nm hleg
          · have hle_f := Rega.effFrame_le T.toIsa hint (fn.mid lt).ext
            have := Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right hle_f _) _) hbg_b
            exact Nat.le_trans this (Nat.le_trans hbf (Nat.le_add_right _ _))
      have hex : ∀ g, g ∈ (fn.mid lt).ext.exits →
          T.Defined h g ∧ nX ≤ M.baseBound + d * M.stepBound :=
        fun g hg => ⟨hexits g (hex_b g hg).1,
          Nat.le_trans (hex_b g hg).2 (Nat.le_trans hbf (Nat.le_add_right _ _))⟩
      exact compileFn_body_correct T h lt hint (fn.mid lt).ext fn
        (DepthEnv.callSlot mod Γext G d) (M.baseBound + d * M.stepBound) nX bound
        (hwf fn hfn) (hsupp fn hfn) hl hc_f hu hfr_eff hn_d hcal hex xs m P E hwp
    · simp only [G, hd, ↓reduceIte]
  have hlfp := DepthEnv.lfp_le hpre
  intro d hd f hf
  obtain ⟨hint, c, k_f, _, _, hl, hinf, hklen, _⟩ := compileModuleRecAux_mem haux f hf
  refine ⟨defined_of_lowerFn' (f := f.mid lt) hl (infix_trans' hklen hinf hc), ?_⟩
  intro args m Q X hleg
  rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀,
    _, ha, hb, hsem⟩
  subst ha; subst hb
  have hG := hlfp d f.name f.as f.rs xs₀ m P₀ E₀ hsem
  simp only [G, hd, ↓reduceIte] at hG
  exact legalEnv_pullEnv_le lt (machEnv_conseq T h (M.baseBound + d * M.stepBound) nX)
    f.name (lt.legalSig f.as) (lt.legalSig f.rs) args m Q X
    ⟨f.as, f.rs, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hG⟩

/-- Host specialization of `link_scc_depth_lfp` with `extCallees = []`. -/
theorem link_scc_depth_lfp_host {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX fuel : Nat} {fs : List Fn} {hints : List T.toIsa.Hints}
    {maxBound : Nat}
    (M : CompiledRec T lt [] exits nX fuel fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (Γext : Env)
    (hcyc : checkCyclic mod = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true) :
    ∀ d ≤ fuel, ∀ f ∈ mod.fns, T.Defined M.host f.name ∧
      T.FnSpec M.host f.name
        (legalEnv lt (Env.onlyFn f (DepthEnv.semScc mod Γext d)) f.name
          (lt.legalSig f.as) (lt.legalSig f.rs))
        (M.baseBound + d * M.stepBound) nX :=
  link_scc_depth_lfp M mod hfs M.host Γext 0 M.code_infix_host M.labelsUnique hcyc hwf hsupp
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ hg => M.defined_exit_host hg)

/-- One-shot `Env.lfp_le` linking theorem for `M.stepBound = 0` against flat `Env.semScc`. -/
theorem link_scc_lfp_zero {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound)
    (hstep0 : M.stepBound = 0)
    (mod : Module) (hfs : mod.fns = fs) (h : T.mach.Host)
    (Γext : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hcyc : checkCyclic mod = true) (hwf : ∀ f ∈ mod.fns, f.Wf)
    (hsupp : ∀ f ∈ mod.fns, (f.earlyOpt).body.supportsSource lt = true)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1
        (legalEnv lt (Env.restrict Γext (mod.externs.map Extern.sig)) p.1.1 p.1.2.1 p.1.2.2)
        p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hexits : ∀ g ∈ exits, T.Defined h g) :
    ∀ f ∈ mod.fns, T.Defined h f.name ∧
      T.FnSpec h f.name
        (legalEnv lt (Env.onlyFn f (Env.semScc mod Γext)) f.name
          (lt.legalSig f.as) (lt.legalSig f.rs))
        M.baseBound nX := by
  have hnd := Module.namesNodup_of_checkNamesNodup ((Bool.and_eq_true _ _).mp hcyc).1
  obtain ⟨hdisj, haux⟩ :=
    compileModuleRec_disjoint' (show compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits
      nX fuel maxBound mod.fns hints = .ok (M.code, M.baseBound, M.stepBound) from
      by rw [hfs]; exact M.compileModuleRec_eq)
  let G : Env := pullEnv lt (machEnv T h M.baseBound nX)
  have hpre : Env.le (Env.sccOp mod Γext G) G := by
    intro f as bs xs m P E hΦ
    rcases hΦ with ⟨_, fn, hfn, rfl, rfl, rfl, hwp⟩
    obtain ⟨hint, c, k_f, bf, sf, hl, hinf, hklen, hchk, hbf, hsf⟩ :=
      compileModuleRecAux_mem haux fn hfn
    have hc_f : c.IsInfixAt (T.mach.prog h) (k₀ + k_f) := infix_trans' hklen hinf hc
    obtain ⟨hsf_eq, hfr_b, hcal_b, hex_b⟩ := checkAndBoundRecExt_spec hchk
    have hfr_eff : Rega.effFrame T.toIsa hint (fn.mid lt).ext ≤ M.baseBound :=
      Nat.le_trans (Rega.effFrame_le T.toIsa hint (fn.mid lt).ext)
        (Nat.le_trans hfr_b hbf)
    have hn0 : M.baseBound + T.frame.raBytes ≤ 2 ^ 64 := by
      have h0 := M.total_ra_le_at (Nat.zero_le fuel)
      simpa [CompiledRec.boundAt] using h0
    let bound : Sym → Nat := fun g =>
      if (mod.fns.map Fn.name).contains g then M.baseBound
      else match extCallees.find? (fun q => q.1.1 == g) with
        | some q => q.2
        | none => 0
    have hcal : ∀ g as' bs', (g, as', bs') ∈ (fn.mid lt).ext.callees →
        T.FnSpec h g (legalEnv lt (Env.sccStep mod G Γext) g as' bs') (bound g) nX ∧
        Rega.effFrame T.toIsa hint (fn.mid lt).ext + T.frame.raBytes + bound g ≤ M.baseBound := by
      intro g as' bs' hg
      rcases hcal_b (g, as', bs') hg with ⟨hrec_sig, _⟩ | ⟨_, bg, hlk, hbg_b⟩
      · obtain ⟨gfn, hgfn, hgeq⟩ := List.mem_map.mp hrec_sig
        rcases Prod.mk.inj hgeq with ⟨rfl, hsig_ab⟩
        rcases Prod.mk.inj hsig_ab with ⟨rfl, rfl⟩
        have hmem_nm : gfn.name ∈ mod.fns.map Fn.name := List.mem_map_of_mem hgfn
        have hcon : (mod.fns.map Fn.name).contains gfn.name = true := by simpa using hmem_nm
        have hbd : bound gfn.name = M.baseBound := by
          dsimp only [bound]; simp only [hcon, ↓reduceIte]
        rw [hbd]
        refine ⟨?_, ?_⟩
        · intro args' m0 Q' X' hleg
          have hpull : legalEnv lt G gfn.name (lt.legalSig gfn.as) (lt.legalSig gfn.rs)
              args' m0 Q' X' := by
            rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hst⟩
            rcases hst with ⟨_, hG⟩ | ⟨hmemE, _⟩
            · exact ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hG⟩
            · exact absurd hmemE (fn_name_not_mem_externs' hnd hgfn)
          exact legalEnv_pullEnv_le lt (machEnv_conseq T h M.baseBound nX)
            gfn.name _ _ args' m0 Q' X' hpull
        · have hfr_sf : Rega.effFrame T.toIsa hint (fn.mid lt).ext + T.frame.raBytes ≤ 0 := by
            have htmp := Nat.add_le_add_right (Rega.effFrame_le T.toIsa hint (fn.mid lt).ext)
              T.frame.raBytes
            rw [← hsf_eq] at htmp; exact Nat.le_trans htmp (hstep0 ▸ hsf)
          omega
      · have hmem_ext : ((g, as', bs'), bg) ∈ extCallees := lookupBound_mem hlk
        have hnot_nm : g ∉ mod.fns.map Fn.name := hdisj ((g, as', bs'), bg) hmem_ext
        have hcon : (mod.fns.map Fn.name).contains g = false := by
          simpa [List.contains_eq_mem] using hnot_nm
        have hbd : bound g = bg := by
          dsimp only [bound]; rw [hcon]
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases hfnd : extCallees.find? (fun q => q.1.1 == g) with
          | none =>
              exfalso
              have hnot := List.find?_eq_none.mp hfnd ((g, as', bs'), bg) hmem_ext
              simp at hnot
          | some q =>
              have hqmem : q ∈ extCallees := List.mem_of_find?_eq_some hfnd
              have hpred : q.1.1 = g :=
                beq_iff_eq.mp (find?_pred' (p := fun q : SigEntry × Nat => q.1.1 == g) hfnd)
              exact hext_uniq q hqmem ((g, as', bs'), bg) hmem_ext hpred
        rw [hbd]
        refine ⟨?_, ?_⟩
        · exact Target.FnSpec.of_spec T (hext ((g, as', bs'), bg) hmem_ext)
            fun _ _ _ _ hleg => legalEnv_sccStep_ext hnot_nm hleg
        · have hle_f := Rega.effFrame_le T.toIsa hint (fn.mid lt).ext
          exact Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right hle_f _) _)
            (Nat.le_trans hbg_b hbf)
    have hex : ∀ g, g ∈ (fn.mid lt).ext.exits → T.Defined h g ∧ nX ≤ M.baseBound :=
      fun g hg => ⟨hexits g (hex_b g hg).1, Nat.le_trans (hex_b g hg).2 hbf⟩
    exact compileFn_body_correct T h lt hint (fn.mid lt).ext fn
      (Env.sccStep mod G Γext) M.baseBound nX bound
      (hwf fn hfn) (hsupp fn hfn) hl hc_f hu hfr_eff hn0 hcal hex xs m P E hwp
  have hlfp := Env.lfp_le hpre
  intro f hf
  obtain ⟨hint, c, k_f, _, _, hl, hinf, hklen, _⟩ := compileModuleRecAux_mem haux f hf
  refine ⟨defined_of_lowerFn' (f := f.mid lt) hl (infix_trans' hklen hinf hc), ?_⟩
  intro args m Q X hleg
  rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, _, ha, hb, hsem⟩
  subst ha; subst hb
  exact legalEnv_pullEnv_le lt (machEnv_conseq T h M.baseBound nX)
    f.name (lt.legalSig f.as) (lt.legalSig f.rs) args m Q X
    ⟨f.as, f.rs, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀,
      hlfp f.name f.as f.rs xs₀ m P₀ E₀ hsem⟩

/-! ## 2. Literal-Backed `CompiledRec` and `RecSubChunk` SCC Sub-Chunking -/

/-- Legalized `(fnSig, stackBound)` entries exported by a `CompiledRec` SCC at `fuel`. -/
@[expose] def LinkRec.CompiledRec.sigBounds {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound) :
    List (SigEntry × Nat) :=
  fs.map fun f => ((f.name, lt.legalSig f.as, lt.legalSig f.rs), M.boundAt fuel)

/-- Legalized `(fnSig, bound)` table for a uniform SCC stack bound `b`. -/
@[expose] def sigBoundsRecOf (lt : LegalTarget) (fs : List Fn) (b : Nat) :
    List (SigEntry × Nat) :=
  fs.map fun f => ((f.name, lt.legalSig f.as, lt.legalSig f.rs), b)

theorem LinkRec.CompiledRec.sigBounds_eq {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX fuel : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : CompiledRec T lt extCallees exits nX fuel fs hints maxBound) :
    M.sigBounds = sigBoundsRecOf lt fs (M.boundAt fuel) :=
  rfl

/-- Metadata-only validity check over pre-evaluated literal `(code, baseBound, stepBound)` for a
`CompiledRec` SCC (does not re-run `compileModuleRec`). -/
@[expose] def checkCompileRecLit {D : Type} (label : Sym → D) (progSmall : List D → Bool)
    (code : List D) (baseBound stepBound : Nat) (fnNames exits : List Sym) : Bool :=
  checkCompileRecResult label progSmall (.ok (code, baseBound, stepBound)) fnNames exits

/-- Variant of `checkCompileRecLit` checking label uniqueness via `labelsNodup`. -/
@[expose] def checkCompileRecLitWithLabels {D : Type} (label : Sym → D)
    (labelsNodup progSmall : List D → Bool)
    (code : List D) (baseBound stepBound : Nat) (exits : List Sym) : Bool :=
  checkCompileRecResultWithLabels label labelsNodup progSmall
    (.ok (code, baseBound, stepBound)) exits

/-- Construct a literal-backed `CompiledRec` from pre-evaluated `(code, baseBound, stepBound)`
literals, a one-shot `compileModuleRec` proof `hcm`, and a fast metadata check `hchk`. -/
@[expose] def compileCheckedRecLit (T : Target) (L : TargetLayout T) (lt : LegalTarget)
    (hcl : Rega.LabelClean T.toIsa) (extCallees : List (SigEntry × Nat)) (exits : List Sym)
    (nX fuel : Nat) (fs : List Fn) (hints : List T.toIsa.Hints) (maxBound : Nat := 2048)
    (code : List T.Directive) (baseBound stepBound : Nat)
    (hcm : compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits nX fuel maxBound
      fs hints = .ok (code, baseBound, stepBound))
    (hchk : checkCompileRecLit T.frame.label L.progSmall code baseBound stepBound
      (fs.map Fn.name) exits = true) :
    CompiledRec T lt extCallees exits nX fuel fs hints maxBound where
  code := code
  baseBound := baseBound
  stepBound := stepBound
  compileModuleRec_eq := hcm
  compile_eq := compileRec_of_compileModuleRec hcm
  bound_le := (compileModuleRec_bounds_le hcm).1
  maxBound_le := (compileModuleRec_bounds_le hcm).2.1
  total_ra_le := (compileModuleRec_bounds_le hcm).2.2
  host := L.layoutOf (code ++ exits.map T.frame.label) (by
    have hp := checkCompileRecResult_parts hchk
    simpa [extractRecCode] using hp.2.2.2.2)
  prog_host := L.prog_layoutOf _ _
  labelsUnique := by
    have hp := checkCompileRecResult_parts hchk
    intro i j l hi hj
    rw [L.prog_layoutOf _ (by simpa [extractRecCode] using hp.2.2.2.2)] at hi hj
    exact compileModuleRec_labelsUnique hcl hcm hp.2.2.2.1
      (by simp only [List.all_append, Bool.and_eq_true]; exact ⟨hp.2.1, hp.2.2.1⟩) i j l hi hj

/-- Variant of `compileCheckedRecLit` using `checkCompileRecLitWithLabels` and
`L.labelsUnique_layoutOf`. -/
@[expose] def compileCheckedRecLitWithLabels (T : Target) (L : TargetLayout T) (lt : LegalTarget)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym)
    (nX fuel : Nat) (fs : List Fn) (hints : List T.toIsa.Hints) (maxBound : Nat := 2048)
    (code : List T.Directive) (baseBound stepBound : Nat)
    (hcm : compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits nX fuel maxBound
      fs hints = .ok (code, baseBound, stepBound))
    (hchk : checkCompileRecLitWithLabels T.frame.label L.labelsNodup L.progSmall code
      baseBound stepBound exits = true) :
    CompiledRec T lt extCallees exits nX fuel fs hints maxBound where
  code := code
  baseBound := baseBound
  stepBound := stepBound
  compileModuleRec_eq := hcm
  compile_eq := compileRec_of_compileModuleRec hcm
  bound_le := (compileModuleRec_bounds_le hcm).1
  maxBound_le := (compileModuleRec_bounds_le hcm).2.1
  total_ra_le := (compileModuleRec_bounds_le hcm).2.2
  host := L.layoutOf (code ++ exits.map T.frame.label) (by
    have hp := checkCompileRecWithLabels_parts hchk
    simpa [extractRecCode] using hp.2.2)
  prog_host := L.prog_layoutOf _ _
  labelsUnique := L.labelsUnique_layoutOf
    (by simpa [extractRecCode] using (checkCompileRecWithLabels_parts hchk).2.2)
    (by simpa [extractRecCode] using (checkCompileRecWithLabels_parts hchk).2.1)

private theorem calleesBoundRec_mono_lookupBound {F raBytes : Nat} {recSigs : List SigEntry}
    {ext₁ ext₂ : List (SigEntry × Nat)}
    (hmono : ∀ g bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg) :
    ∀ {gs : List SigEntry} {n : Nat},
      calleesBoundRec F raBytes recSigs ext₁ gs = some n →
      calleesBoundRec F raBytes recSigs ext₂ gs = some n
  | [], _, h => h
  | g :: gs, n, h => by
      dsimp only [calleesBoundRec] at h ⊢
      split at h
      · rename_i hrec
        simp only [hrec, ↓reduceIte]
        cases hcb : calleesBoundRec F raBytes recSigs ext₁ gs with
        | none => simp [hcb] at h
        | some rest =>
            simp only [hcb, Option.map_some, Option.some.injEq] at h
            rw [calleesBoundRec_mono_lookupBound hmono hcb]
            simp [h]
      · rename_i hnot
        simp only [hnot, Bool.false_eq_true, ↓reduceIte]
        cases h1 : lookupBound ext₁ g with
        | none => simp [h1] at h
        | some bg =>
            cases h2 : calleesBoundRec F raBytes recSigs ext₁ gs with
            | none => simp [h1, h2] at h
            | some rest =>
                simp only [h1, h2, Option.some.injEq] at h
                rw [hmono g bg h1, calleesBoundRec_mono_lookupBound hmono h2]
                dsimp only; rw [h]

private theorem checkAndBoundRecExt_mono_lookupBound {I : Isa} {raBytes : Nat}
    {recSigs : List SigEntry} {exits : List Sym} {nX : Nat} {ext₁ ext₂ : List (SigEntry × Nat)}
    (hmono : ∀ g bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg)
    {h : I.Hints} {ext : Rega.Ext} {res : Nat × Nat}
    (hc : checkAndBoundRecExt I raBytes recSigs ext₁ exits nX h ext = some res) :
    checkAndBoundRecExt I raBytes recSigs ext₂ exits nX h ext = some res := by
  dsimp only [checkAndBoundRecExt] at hc ⊢
  cases hcb : calleesBoundRec (I.frame.frameSize h.totalSlots) raBytes recSigs ext₁ ext.callees with
  | none => simp [hcb] at hc
  | some n₁ =>
      rw [hcb] at hc
      rw [calleesBoundRec_mono_lookupBound hmono hcb]
      exact hc

theorem compileModuleRecAux_mono_lookupBound {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {recSigs : List SigEntry} {exits : List Sym} {nX : Nat} :
    ∀ {ext₁ ext₂ : List (SigEntry × Nat)} {fs : List Fn} {hints : List I.Hints}
      {code : List I.Directive} {base step : Nat},
      (∀ g bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg) →
      compileModuleRecAux I lt raBytes recSigs ext₁ exits nX fs hints =
        .ok (code, base, step) →
      compileModuleRecAux I lt raBytes recSigs ext₂ exits nX fs hints =
        .ok (code, base, step)
  | _, _, [], [], _, _, _, _, h => h
  | _, _, [], _ :: _, _, _, _, _, h => by dsimp only [compileModuleRecAux] at h; cases h
  | _, _, _ :: _, [], _, _, _, _, h => by dsimp only [compileModuleRecAux] at h; cases h
  | ext₁, ext₂, f :: fs, hint :: hints, code, base, step, hmono, h => by
      dsimp only [compileModuleRecAux] at h ⊢
      cases hl : Rega.lowerFn I hint (f.mid lt).ext (f.mid lt) with
      | error e => simp [hl] at h
      | ok c =>
          cases hchk : checkAndBoundRecExt I raBytes recSigs ext₁ exits nX hint
              (f.mid lt).ext with
          | none => simp [hl, hchk] at h
          | some p =>
              simp only [hl, hchk] at h ⊢
              rw [checkAndBoundRecExt_mono_lookupBound hmono hchk]
              dsimp only
              cases hrest : compileModuleRecAux I lt raBytes recSigs ext₁ exits nX fs hints with
              | error e => simp [hrest] at h
              | ok res =>
                  simp only [hrest] at h
                  rw [compileModuleRecAux_mono_lookupBound hmono hrest]
                  exact h

theorem compileModuleRec_mono_lookupBound {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {ext₁ ext₂ : List (SigEntry × Nat)} {exits : List Sym} {nX fuel maxBound : Nat}
    {fs : List Fn} {hints : List I.Hints} {code : List I.Directive} {base step : Nat}
    (hmono : ∀ g bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg)
    (hdisj : ∀ p ∈ ext₂, p.1.1 ∉ fs.map Fn.name)
    (h : compileModuleRec I lt raBytes ext₁ exits nX fuel maxBound fs hints =
      .ok (code, base, step)) :
    compileModuleRec I lt raBytes ext₂ exits nX fuel maxBound fs hints =
      .ok (code, base, step) := by
  dsimp only [compileModuleRec] at h ⊢
  split at h
  · simp at h
  · have hno₂ : ext₂.any (fun p => fs.any (fun f => f.name == p.1.1)) = false := by
      cases hne : ext₂.any (fun p => fs.any (fun f => f.name == p.1.1)) with
      | false => rfl
      | true =>
          obtain ⟨p, hp, hf⟩ := List.any_eq_true.mp hne
          obtain ⟨f, hfm, hnm⟩ := List.any_eq_true.mp hf
          exact absurd ((beq_iff_eq.mp hnm) ▸ List.mem_map_of_mem hfm) (hdisj p hp)
    simp only [hno₂, Bool.false_eq_true, ↓reduceIte]
    split at h
    · simp at h
    · rename_i code' b' s' haux
      rw [compileModuleRecAux_mono_lookupBound hmono haux]
      exact h

/-- Legalized signature list for `fs` as passed to `compileModuleRecAux`. -/
@[expose] def recSigsOf (lt : LegalTarget) (fs : List Fn) : List SigEntry :=
  fs.map fun f => (f.name, lt.legalSig f.as, lt.legalSig f.rs)

/-- Kernel-reducible boolean equality over lists of `SigEntry` via `SigEntry.beq`. -/
@[expose] def sigListBeq : List SigEntry → List SigEntry → Bool
  | [], [] => true
  | a :: as, b :: bs => SigEntry.beq a b && sigListBeq as bs
  | _, _ => false

theorem sigListBeq_eq : ∀ {xs ys : List SigEntry}, sigListBeq xs ys = true → xs = ys
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
      dsimp only [sigListBeq] at h
      simp only [Bool.and_eq_true, SigEntry.beq_iff_eq] at h
      rw [h.1, sigListBeq_eq h.2]

/-- Literal-backed compiled sub-chunk of a single cyclic SCC sharing fixed `recSigs` and
`extCallees` across all sibling sub-chunks. -/
structure RecSubChunk (T : Target) (lt : LegalTarget) (recSigs : List SigEntry)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat) : Type 1 where
  fs : List Fn
  hints : List T.toIsa.Hints
  code : List T.Directive
  baseBound : Nat
  stepBound : Nat
  compileAux_eq :
    compileModuleRecAux T.toIsa lt T.frame.raBytes recSigs extCallees exits nX fs hints =
      .ok (code, baseBound, stepBound)

@[expose] def recSubchunksFns {T : Target} {lt : LegalTarget} {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat} :
    List (RecSubChunk T lt recSigs extCallees exits nX) → List Fn
  | [] => []
  | sc :: scs => sc.fs ++ recSubchunksFns scs

@[expose] def recSubchunksHints {T : Target} {lt : LegalTarget} {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat} :
    List (RecSubChunk T lt recSigs extCallees exits nX) → List T.toIsa.Hints
  | [] => []
  | sc :: scs => sc.hints ++ recSubchunksHints scs

@[expose] def recSubchunksCode {T : Target} {lt : LegalTarget} {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat} :
    List (RecSubChunk T lt recSigs extCallees exits nX) → List T.Directive
  | [] => []
  | sc :: scs => sc.code ++ recSubchunksCode scs

@[expose] def recSubchunksBase {T : Target} {lt : LegalTarget} {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat} :
    List (RecSubChunk T lt recSigs extCallees exits nX) → Nat
  | [] => 0
  | sc :: scs => Nat.max sc.baseBound (recSubchunksBase scs)

@[expose] def recSubchunksStep {T : Target} {lt : LegalTarget} {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat} :
    List (RecSubChunk T lt recSigs extCallees exits nX) → Nat
  | [] => 0
  | sc :: scs => Nat.max sc.stepBound (recSubchunksStep scs)

theorem compileModuleRecAux_append {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} :
    ∀ {fs₁ fs₂ : List Fn} {hints₁ hints₂ : List I.Hints}
      {c₁ c₂ : List I.Directive} {b₁ s₁ b₂ s₂ : Nat},
      compileModuleRecAux I lt raBytes recSigs extCallees exits nX fs₁ hints₁ =
        .ok (c₁, b₁, s₁) →
      compileModuleRecAux I lt raBytes recSigs extCallees exits nX fs₂ hints₂ =
        .ok (c₂, b₂, s₂) →
      compileModuleRecAux I lt raBytes recSigs extCallees exits nX
        (fs₁ ++ fs₂) (hints₁ ++ hints₂) =
        .ok (c₁ ++ c₂, Nat.max b₁ b₂, Nat.max s₁ s₂) := by
  intro fs₁
  induction fs₁ with
  | nil =>
      intro fs₂ hints₁ hints₂ c₁ c₂ b₁ s₁ b₂ s₂ h₁ h₂
      cases hints₁ with
      | nil =>
          change Except.ok ([], 0, 0) = Except.ok (c₁, b₁, s₁) at h₁
          simp only [Except.ok.injEq, Prod.mk.injEq] at h₁
          rcases h₁ with ⟨rfl, rfl, rfl⟩
          simpa [Nat.zero_max] using h₂
      | cons _ _ =>
          change Except.error "compileModuleRec: fn/hints length mismatch" = _ at h₁
          cases h₁
  | cons f fs₁ ih =>
      intro fs₂ hints₁ hints₂ c₁ c₂ b₁ s₁ b₂ s₂ h₁ h₂
      cases hints₁ with
      | nil =>
          change Except.error "compileModuleRec: fn/hints length mismatch" = _ at h₁
          cases h₁
      | cons hint hints₁ =>
          rw [List.cons_append, List.cons_append]
          dsimp only [compileModuleRecAux] at h₁ ⊢
          cases hl : Rega.lowerFn I hint (f.mid lt).ext (f.mid lt) with
          | error e => simp [hl] at h₁
          | ok c =>
              cases hchk : checkAndBoundRecExt I raBytes recSigs extCallees exits nX hint
                  (f.mid lt).ext with
              | none => simp [hl, hchk] at h₁
              | some p =>
                  simp only [hl, hchk] at h₁ ⊢
                  cases hrest : compileModuleRecAux I lt raBytes recSigs extCallees exits nX
                      fs₁ hints₁ with
                  | error e => simp [hrest] at h₁
                  | ok res =>
                      simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h₁
                      rcases h₁ with ⟨rfl, rfl, rfl⟩
                      rw [ih hrest h₂]
                      simp only [List.append_assoc, Nat.max_assoc]

theorem compileModuleRecAux_subchunks_eq {T : Target} {lt : LegalTarget}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} :
    ∀ scs : List (RecSubChunk T lt recSigs extCallees exits nX),
      compileModuleRecAux T.toIsa lt T.frame.raBytes recSigs extCallees exits nX
        (recSubchunksFns scs) (recSubchunksHints scs) =
        .ok (recSubchunksCode scs, recSubchunksBase scs, recSubchunksStep scs)
  | [] => rfl
  | sc :: scs =>
      compileModuleRecAux_append sc.compileAux_eq (compileModuleRecAux_subchunks_eq scs)

/-- Metadata-only validator assembling a list of `RecSubChunk`s into a single cyclic SCC
`CompiledRec` at recursion budget `fuel` and stack bound `maxBound`. -/
@[expose] def checkRecSubchunks {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} (fuel maxBound : Nat)
    (scs : List (RecSubChunk T lt recSigs extCallees exits nX)) : Bool :=
  let fs := recSubchunksFns scs
  let fnNames := fs.map Fn.name
  let code := recSubchunksCode scs
  let baseBound := recSubchunksBase scs
  let stepBound := recSubchunksStep scs
  let totalBound := baseBound + fuel * stepBound
  sigListBeq recSigs (recSigsOf lt fs) &&
  !(extCallees.any (fun p => fnNames.any (fun nm => nm == p.1.1))) &&
  Nat.ble totalBound maxBound &&
  Nat.ble maxBound (2 ^ 64) &&
  Nat.ble (totalBound + T.frame.raBytes) (2 ^ 64) &&
  fnNames.all fnNameOk &&
  exits.all fnNameOk &&
  stringsNodup (fnNames ++ exits) &&
  L.progSmall (code ++ exits.map T.frame.label)

/-- Variant of `checkRecSubchunks` using `L.labelsNodup`. -/
@[expose] def checkRecSubchunksWithLabels {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} (fuel maxBound : Nat)
    (scs : List (RecSubChunk T lt recSigs extCallees exits nX)) : Bool :=
  let fs := recSubchunksFns scs
  let fnNames := fs.map Fn.name
  let code := recSubchunksCode scs
  let baseBound := recSubchunksBase scs
  let stepBound := recSubchunksStep scs
  let totalBound := baseBound + fuel * stepBound
  sigListBeq recSigs (recSigsOf lt fs) &&
  !(extCallees.any (fun p => fnNames.any (fun nm => nm == p.1.1))) &&
  Nat.ble totalBound maxBound &&
  Nat.ble maxBound (2 ^ 64) &&
  Nat.ble (totalBound + T.frame.raBytes) (2 ^ 64) &&
  stringsNodup (fnNames ++ exits) &&
  L.labelsNodup (code ++ exits.map T.frame.label) &&
  L.progSmall (code ++ exits.map T.frame.label)

private theorem bool_not_any_eq_false {p : Bool} (h : (!p) = true) : p = false := by
  cases p <;> simp at h ⊢

private theorem eq_rec_compileModuleRecAux {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {r₁ r₂ : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs : List Fn} {hints : List I.Hints} {code : List I.Directive} {base step : Nat}
    (h : r₁ = r₂)
    (haux : compileModuleRecAux I lt raBytes r₁ extCallees exits nX fs hints =
      .ok (code, base, step)) :
    compileModuleRecAux I lt raBytes r₂ extCallees exits nX fs hints =
      .ok (code, base, step) :=
  h ▸ haux

private theorem compileModuleRec_of_subchunks {T : Target} {lt : LegalTarget}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX fuel maxBound : Nat}
    (scs : List (RecSubChunk T lt recSigs extCallees exits nX))
    (hsig : sigListBeq recSigs (recSigsOf lt (recSubchunksFns scs)) = true)
    (hdisj : !(extCallees.any (fun p => (recSubchunksFns scs).any (fun f => f.name == p.1.1))) =
      true)
    (hb1 : Nat.ble (recSubchunksBase scs + fuel * recSubchunksStep scs) maxBound = true)
    (hb2 : Nat.ble maxBound (2 ^ 64) = true)
    (hb3 : Nat.ble (recSubchunksBase scs + fuel * recSubchunksStep scs + T.frame.raBytes)
      (2 ^ 64) = true) :
    compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits nX fuel maxBound
      (recSubchunksFns scs) (recSubchunksHints scs) =
      .ok (recSubchunksCode scs, recSubchunksBase scs, recSubchunksStep scs) := by
  have haux := eq_rec_compileModuleRecAux (sigListBeq_eq hsig)
    (compileModuleRecAux_subchunks_eq scs)
  dsimp only [recSigsOf] at haux
  have hno : (extCallees.any (fun p => (recSubchunksFns scs).any (fun f => f.name == p.1.1))) =
      false :=
    bool_not_any_eq_false hdisj
  dsimp only [compileModuleRec]
  simp only [hno, Bool.false_eq_true, ↓reduceIte]
  rw [haux]
  simp only [hb1, hb2, hb3, Bool.and_self, ↓reduceIte]

private theorem ext_disj_fnNames_to_fns {extCallees : List (SigEntry × Nat)} {fs : List Fn}
    (h : !(extCallees.any (fun p => (fs.map Fn.name).any (fun nm => nm == p.1.1))) = true) :
    !(extCallees.any (fun p => fs.any (fun f => f.name == p.1.1))) = true := by
  simpa [List.any_map, Function.comp_def] using h

theorem linkRecSubchunks_cm {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    (fuel maxBound : Nat)
    (scs : List (RecSubChunk T lt recSigs extCallees exits nX))
    (h : checkRecSubchunks L fuel maxBound scs = true) :
    compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits nX fuel maxBound
      (recSubchunksFns scs) (recSubchunksHints scs) =
      .ok (recSubchunksCode scs, recSubchunksBase scs, recSubchunksStep scs) := by
  dsimp only [checkRecSubchunks] at h
  simp only [Bool.and_eq_true] at h
  exact compileModuleRec_of_subchunks scs
    h.1.1.1.1.1.1.1.1 (ext_disj_fnNames_to_fns h.1.1.1.1.1.1.1.2)
    h.1.1.1.1.1.1.2 h.1.1.1.1.1.2 h.1.1.1.1.2

theorem linkRecSubchunks_chk {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    (fuel maxBound : Nat)
    (scs : List (RecSubChunk T lt recSigs extCallees exits nX))
    (h : checkRecSubchunks L fuel maxBound scs = true) :
    checkCompileRecLit T.frame.label L.progSmall (recSubchunksCode scs)
      (recSubchunksBase scs) (recSubchunksStep scs) ((recSubchunksFns scs).map Fn.name)
      exits = true := by
  dsimp only [checkRecSubchunks] at h
  simp only [Bool.and_eq_true] at h
  dsimp only [checkCompileRecLit, checkCompileRecResult]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨h.1.1.1.2, h.1.1.2⟩, h.1.2⟩, h.2⟩

/-- Link a list of cyclic SCC `RecSubChunk`s into a single `CompiledRec` in O(#subchunks)
metadata-only time (zero re-evaluation of `Rega.lowerFn` or `compileModuleRecAux`). -/
@[expose] def linkRecSubchunks {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    (hcl : Rega.LabelClean T.toIsa) {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    (fuel maxBound : Nat)
    (scs : List (RecSubChunk T lt recSigs extCallees exits nX))
    (h : checkRecSubchunks L fuel maxBound scs = true) :
    CompiledRec T lt extCallees exits nX fuel (recSubchunksFns scs) (recSubchunksHints scs)
      maxBound :=
  compileCheckedRecLit T L lt hcl extCallees exits nX fuel
    (recSubchunksFns scs) (recSubchunksHints scs) maxBound
    (recSubchunksCode scs) (recSubchunksBase scs) (recSubchunksStep scs)
    (linkRecSubchunks_cm L fuel maxBound scs h)
    (linkRecSubchunks_chk L fuel maxBound scs h)

theorem linkRecSubchunksWithLabels_cm {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    (fuel maxBound : Nat)
    (scs : List (RecSubChunk T lt recSigs extCallees exits nX))
    (h : checkRecSubchunksWithLabels L fuel maxBound scs = true) :
    compileModuleRec T.toIsa lt T.frame.raBytes extCallees exits nX fuel maxBound
      (recSubchunksFns scs) (recSubchunksHints scs) =
      .ok (recSubchunksCode scs, recSubchunksBase scs, recSubchunksStep scs) := by
  dsimp only [checkRecSubchunksWithLabels] at h
  simp only [Bool.and_eq_true] at h
  exact compileModuleRec_of_subchunks scs
    h.1.1.1.1.1.1.1 (ext_disj_fnNames_to_fns h.1.1.1.1.1.1.2)
    h.1.1.1.1.1.2 h.1.1.1.1.2 h.1.1.1.2

theorem linkRecSubchunksWithLabels_chk {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    (fuel maxBound : Nat)
    (scs : List (RecSubChunk T lt recSigs extCallees exits nX))
    (h : checkRecSubchunksWithLabels L fuel maxBound scs = true) :
    checkCompileRecLitWithLabels T.frame.label L.labelsNodup L.progSmall
      (recSubchunksCode scs) (recSubchunksBase scs) (recSubchunksStep scs) exits = true := by
  dsimp only [checkRecSubchunksWithLabels] at h
  simp only [Bool.and_eq_true] at h
  dsimp only [checkCompileRecLitWithLabels, checkCompileRecResultWithLabels]
  simp only [Bool.and_eq_true]
  exact ⟨h.1.2, h.2⟩

/-- Variant of `linkRecSubchunks` using `checkRecSubchunksWithLabels` and
`L.labelsUnique_layoutOf`. -/
@[expose] def linkRecSubchunksWithLabels {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} (fuel maxBound : Nat)
    (scs : List (RecSubChunk T lt recSigs extCallees exits nX))
    (h : checkRecSubchunksWithLabels L fuel maxBound scs = true) :
    CompiledRec T lt extCallees exits nX fuel (recSubchunksFns scs) (recSubchunksHints scs)
      maxBound :=
  compileCheckedRecLitWithLabels T L lt extCallees exits nX fuel
    (recSubchunksFns scs) (recSubchunksHints scs) maxBound
    (recSubchunksCode scs) (recSubchunksBase scs) (recSubchunksStep scs)
    (linkRecSubchunksWithLabels_cm L fuel maxBound scs h)
    (linkRecSubchunksWithLabels_chk L fuel maxBound scs h)

/-! ## 2b. `BudgetModule` Compilation, `CompiledBudgetRec`, and `link_scc_budget_lfp` -/

/-- Check that every callee in `gs` is either a cyclic signature in `recSigs` or an external
callee in `extCallees` with `F + raBytes + bg ≤ minEntry`. -/
@[expose] def checkBudgetCallees (F raBytes minEntry : Nat) (recSigs : List SigEntry)
    (extCallees : List (SigEntry × Nat)) (gs : List SigEntry) : Bool :=
  gs.all fun g =>
    if recSigs.any (SigEntry.beq g) then true
    else match lookupBound extCallees g with
      | some bg => Nat.ble (F + raBytes + bg) minEntry
      | none => false

/-- Check per-function `BudgetFn` frame budget (`effFrame + raBytes ≤ bfn.maxFrame`) and
per-function entry headroom (`bfn.minEntry`) over pre-extracted `ext : Rega.Ext`. -/
@[expose] def checkAndBoundBudgetRecExt (I : Isa) (raBytes : Nat) (recSigs : List SigEntry)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (h : I.Hints) (ext : Rega.Ext) (bfn : BudgetFn) : Bool :=
  let F := Rega.effFrame I h ext
  Nat.ble (F + raBytes) bfn.maxFrame &&
  checkBudgetCallees F raBytes bfn.minEntry recSigs extCallees ext.callees &&
  ext.exits.all (fun g => exits.contains g) &&
  (ext.exits.isEmpty || Nat.ble nX bfn.minEntry)

/-- Check `BudgetFn` frame/callee/exit budgets for pre-lowered `mf = bfn.toFn.mid lt`. -/
@[expose] def checkAndBoundBudgetRecMid (I : Isa) (raBytes : Nat) (recSigs : List SigEntry)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (h : I.Hints) (mf : Fn) (bfn : BudgetFn) : Bool :=
  checkAndBoundBudgetRecExt I raBytes recSigs extCallees exits nX h mf.ext bfn

/-- Check `BudgetFn` frame/callee/exit budgets under `lt` and hints `h`. -/
@[expose] def checkAndBoundBudgetRec (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (recSigs : List SigEntry) (extCallees : List (SigEntry × Nat)) (exits : List Sym)
    (nX : Nat) (bfn : BudgetFn) (h : I.Hints) : Bool :=
  checkAndBoundBudgetRecMid I raBytes recSigs extCallees exits nX h (bfn.toFn.mid lt) bfn

/-- Compile a potentially cyclic list of `BudgetFn`s against `recSigs` and `extCallees`,
checking `effFrame + raBytes ≤ bfn.maxFrame` and per-function `bfn.minEntry`. -/
@[expose] def compileModuleBudgetRecAux (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (recSigs : List SigEntry) (extCallees : List (SigEntry × Nat))
    (exits : List Sym) (nX : Nat) :
    List BudgetFn → List I.Hints → Except String (List I.Directive)
  | [], [] => .ok []
  | bfn :: bfs, h :: hs =>
    let f := bfn.toFn
    let mf := f.mid lt
    let ext := mf.ext
    match Rega.lowerFn I h ext mf,
          checkAndBoundBudgetRecExt I raBytes recSigs extCallees exits nX h ext bfn with
    | .ok c, true =>
      match compileModuleBudgetRecAux I lt raBytes recSigs extCallees exits nX bfs hs with
      | .ok cs => .ok (c ++ cs)
      | .error e => .error e
    | .error e, _ => .error s!"{f.name}: {e}"
    | _, false => .error s!"{f.name}: frame/callee budget exceeded or unknown callee/exit"
  | _, _ => .error "compileModuleBudgetRec: fn/hints length mismatch"

/-- Compile and validate a cyclic/mutually-recursive `List BudgetFn`, failing closed if any
`effFrame + raBytes > bfn.maxFrame`, any external callee exceeds `bfn.minEntry`, any exit
exceeds `bfn.minEntry`, or `exportBounds`/`maxBound` overflow `2^64`. -/
@[expose] def compileModuleBudgetRec (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX maxBound : Nat)
    (bfs : List BudgetFn) (hints : List I.Hints)
    (exportBounds : List (Sym × Nat) := []) :
    Except String (List I.Directive) :=
  let recSigs := bfs.map (fun b => (b.toFn.name, lt.legalSig b.toFn.as, lt.legalSig b.toFn.rs))
  if extCallees.any (fun p => bfs.any (fun b => b.toFn.name == p.1.1)) then
    .error "compileModuleBudgetRec: external callee collides with module function"
  else if !(Nat.ble maxBound (2 ^ 64) &&
      Nat.ble (maxBound + raBytes) (2 ^ 64) &&
      exportBounds.all (fun p => Nat.ble p.2 maxBound)) then
    .error s!"compileModuleBudgetRec: stack bound overflow (maxBound={maxBound})"
  else
    compileModuleBudgetRecAux I lt raBytes recSigs extCallees exits nX bfs hints

/-- Exported stack bound for symbol `nm` from a `.recBudgetSCC` chunk, defaulting to `maxBound`. -/
@[expose] def budgetBound (exportBounds : List (Sym × Nat)) (maxBound : Nat) (nm : Sym) : Nat :=
  (lookupFnBound exportBounds nm).getD maxBound

/-- Legalized signature list for `bfs : List BudgetFn`. -/
@[expose] def budgetRecSigsOf (lt : LegalTarget) (bfs : List BudgetFn) : List SigEntry :=
  bfs.map fun b => (b.toFn.name, lt.legalSig b.toFn.as, lt.legalSig b.toFn.rs)

/-- Legalized `(fnSig, stackBound)` entries exported by a `BudgetFn` SCC. -/
@[expose] def sigBoundsBudgetRecOf (lt : LegalTarget) (bfs : List BudgetFn)
    (exportBounds : List (Sym × Nat)) (maxBound : Nat) : List (SigEntry × Nat) :=
  bfs.map fun b =>
    ((b.toFn.name, lt.legalSig b.toFn.as, lt.legalSig b.toFn.rs),
      budgetBound exportBounds maxBound b.toFn.name)

/-- Kernel-reducible check over `compileModuleBudgetRec` result using `fnNameOk` +
`stringsNodup`. -/
@[expose] def checkCompileBudgetRecResult {D : Type} (label : Sym → D)
    (progSmall : List D → Bool) (res : Except String (List D))
    (fnNames exits : List Sym) : Bool :=
  match res with
  | .error _ => false
  | .ok code =>
    let prog := code ++ exits.map label
    fnNames.all fnNameOk &&
    exits.all fnNameOk &&
    stringsNodup (fnNames ++ exits) &&
    progSmall prog

/-- Extract the directive stream from a `compileModuleBudgetRec` result. -/
@[expose] def extractBudgetRecCode {D : Type} : Except String (List D) → List D
  | .ok c => c
  | .error _ => []

attribute [irreducible] extractBudgetRecCode

private theorem checkBudgetCallees_spec {F raBytes minEntry : Nat} {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} {gs : List SigEntry}
    (h : checkBudgetCallees F raBytes minEntry recSigs extCallees gs = true) :
    ∀ g ∈ gs,
      g ∈ recSigs ∨
      (g ∉ recSigs ∧ ∃ bg, lookupBound extCallees g = some bg ∧
        F + raBytes + bg ≤ minEntry) := by
  intro g hg
  dsimp only [checkBudgetCallees] at h
  have hall := List.all_eq_true.mp h g hg
  by_cases hrec : recSigs.any (SigEntry.beq g) = true
  · simp only [List.any_eq_true, SigEntry.beq_iff_eq] at hrec
    obtain ⟨s, hs, rfl⟩ := hrec
    exact Or.inl hs
  · have hrec_f : recSigs.any (SigEntry.beq g) = false := by
      cases hc : recSigs.any (SigEntry.beq g) with | false => rfl | true => exact absurd hc hrec
    rw [hrec_f] at hall
    simp only [Bool.false_eq_true, ↓reduceIte] at hall
    have hnr : g ∉ recSigs := fun hm =>
      hrec (List.any_eq_true.mpr ⟨g, hm, SigEntry.beq_iff_eq.mpr rfl⟩)
    cases hlk : lookupBound extCallees g with
    | none => rw [hlk] at hall; simp at hall
    | some bg =>
      rw [hlk] at hall
      exact Or.inr ⟨hnr, bg, rfl, Nat.le_of_ble_eq_true hall⟩

private theorem checkAndBoundBudgetRecExt_spec {I : Isa} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} {h : I.Hints} {ext : Rega.Ext} {bfn : BudgetFn}
    (hc : checkAndBoundBudgetRecExt I raBytes recSigs extCallees exits nX h ext bfn = true) :
    Rega.effFrame I h ext + raBytes ≤ bfn.maxFrame ∧
      (∀ g ∈ ext.callees,
        g ∈ recSigs ∨
        (g ∉ recSigs ∧ ∃ bg, lookupBound extCallees g = some bg ∧
          Rega.effFrame I h ext + raBytes + bg ≤ bfn.minEntry)) ∧
      (∀ g ∈ ext.exits, g ∈ exits ∧ nX ≤ bfn.minEntry) := by
  dsimp only [checkAndBoundBudgetRecExt] at hc
  simp only [Bool.and_eq_true] at hc
  refine ⟨Nat.le_of_ble_eq_true hc.1.1.1, checkBudgetCallees_spec hc.1.1.2, fun g hg => ?_⟩
  refine ⟨by simpa using List.all_eq_true.mp hc.1.2 g hg, ?_⟩
  have hne : ext.exits.isEmpty = false := by
    cases he : ext.exits with | nil => simp [he] at hg | cons _ _ => rfl
  have hor := hc.2
  rw [hne] at hor
  simp only [Bool.false_or] at hor
  exact Nat.le_of_ble_eq_true hor

private theorem checkBudgetCallees_mono_lookupBound {F raBytes minEntry : Nat}
    {recSigs : List SigEntry} {ext₁ ext₂ : List (SigEntry × Nat)}
    (hmono : ∀ g bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg)
    {gs : List SigEntry}
    (hc : checkBudgetCallees F raBytes minEntry recSigs ext₁ gs = true) :
    checkBudgetCallees F raBytes minEntry recSigs ext₂ gs = true := by
  dsimp only [checkBudgetCallees] at hc ⊢
  rw [List.all_eq_true] at hc ⊢
  intro g hg
  have h1 := hc g hg
  by_cases hrec : recSigs.any (SigEntry.beq g) = true
  · simp only [hrec, ↓reduceIte]
  · have hrec_f : recSigs.any (SigEntry.beq g) = false := by
      cases hq : recSigs.any (SigEntry.beq g) with | false => rfl | true => exact absurd hq hrec
    simp only [hrec_f, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
    cases hlk : lookupBound ext₁ g with
    | none => rw [hlk] at h1; simp at h1
    | some bg =>
      rw [hlk] at h1
      rw [hmono g bg hlk]
      exact h1

private theorem checkAndBoundBudgetRecExt_mono_lookupBound {I : Isa} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees₁ extCallees₂ : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} {h : I.Hints} {ext : Rega.Ext} {bfn : BudgetFn}
    (hmono : ∀ g bg, lookupBound extCallees₁ g = some bg →
      lookupBound extCallees₂ g = some bg)
    (hc : checkAndBoundBudgetRecExt I raBytes recSigs extCallees₁ exits nX h ext bfn = true) :
    checkAndBoundBudgetRecExt I raBytes recSigs extCallees₂ exits nX h ext bfn = true := by
  dsimp only [checkAndBoundBudgetRecExt] at hc ⊢
  simp only [Bool.and_eq_true] at hc ⊢
  exact ⟨⟨⟨hc.1.1.1, checkBudgetCallees_mono_lookupBound hmono hc.1.1.2⟩, hc.1.2⟩, hc.2⟩

theorem compileModuleBudgetRecAux_mono_lookupBound {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {recSigs : List SigEntry} {exits : List Sym} {nX : Nat} :
    ∀ {ext₁ ext₂ : List (SigEntry × Nat)} {bfs : List BudgetFn} {hints : List I.Hints}
      {code : List I.Directive},
      (∀ g bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg) →
      compileModuleBudgetRecAux I lt raBytes recSigs ext₁ exits nX bfs hints = .ok code →
      compileModuleBudgetRecAux I lt raBytes recSigs ext₂ exits nX bfs hints = .ok code
  | _, _, [], [], _, _, h => h
  | _, _, [], _ :: _, _, _, h => by dsimp only [compileModuleBudgetRecAux] at h; cases h
  | _, _, _ :: _, [], _, _, h => by dsimp only [compileModuleBudgetRecAux] at h; cases h
  | ext₁, ext₂, bfn :: bfs, hint :: hints, code, hmono, h => by
    dsimp only [compileModuleBudgetRecAux] at h ⊢
    cases hl : Rega.lowerFn I hint (bfn.toFn.mid lt).ext (bfn.toFn.mid lt) with
    | error e => simp [hl] at h
    | ok c =>
      cases hchk : checkAndBoundBudgetRecExt I raBytes recSigs ext₁ exits nX hint
          (bfn.toFn.mid lt).ext bfn with
      | false => simp [hl, hchk] at h
      | true =>
        simp only [hl, hchk] at h ⊢
        rw [checkAndBoundBudgetRecExt_mono_lookupBound hmono hchk]
        dsimp only
        cases hrest : compileModuleBudgetRecAux I lt raBytes recSigs ext₁ exits nX bfs hints with
        | error e => simp [hrest] at h
        | ok cs =>
          simp only [hrest] at h
          rw [compileModuleBudgetRecAux_mono_lookupBound hmono hrest]
          exact h

theorem compileModuleBudgetRec_mono_lookupBound {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {ext₁ ext₂ : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    {bfs : List BudgetFn} {hints : List I.Hints} {exportBounds : List (Sym × Nat)}
    {code : List I.Directive}
    (hmono : ∀ g bg, lookupBound ext₁ g = some bg → lookupBound ext₂ g = some bg)
    (hdisj : ∀ p ∈ ext₂, p.1.1 ∉ bfs.map (fun b => b.toFn.name))
    (h : compileModuleBudgetRec I lt raBytes ext₁ exits nX maxBound bfs hints exportBounds =
      .ok code) :
    compileModuleBudgetRec I lt raBytes ext₂ exits nX maxBound bfs hints exportBounds =
      .ok code := by
  dsimp only [compileModuleBudgetRec] at h ⊢
  split at h
  · simp at h
  · have hno₂ : ext₂.any (fun p => bfs.any (fun b => b.toFn.name == p.1.1)) = false := by
      cases hne : ext₂.any (fun p => bfs.any (fun b => b.toFn.name == p.1.1)) with
      | false => rfl
      | true =>
        obtain ⟨p, hp, hf⟩ := List.any_eq_true.mp hne
        obtain ⟨b, hbm, hnm⟩ := List.any_eq_true.mp hf
        exact absurd ((beq_iff_eq.mp hnm) ▸ List.mem_map_of_mem hbm) (hdisj p hp)
    simp only [hno₂, Bool.false_eq_true, ↓reduceIte]
    by_cases hov : (!(Nat.ble maxBound (2 ^ 64) && Nat.ble (maxBound + raBytes) (2 ^ 64) &&
        exportBounds.all (fun p => Nat.ble p.2 maxBound))) = true
    · simp [hov] at h
    · simp only [hov] at h ⊢
      exact compileModuleBudgetRecAux_mono_lookupBound hmono h

private theorem compileOfBudgetAux {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym}
    {nX : Nat} :
    ∀ {bfs : List BudgetFn} {hints : List I.Hints} {code : List I.Directive},
      compileModuleBudgetRecAux I lt raBytes recSigs extCallees exits nX bfs hints = .ok code →
      compile I lt (bfs.map BudgetFn.toFn) hints = .ok code
  | [], [], _, h => by
    dsimp only [compileModuleBudgetRecAux] at h
    simp only [Except.ok.injEq] at h
    subst h; rfl
  | [], _ :: _, _, h => by dsimp only [compileModuleBudgetRecAux] at h; cases h
  | _ :: _, [], _, h => by dsimp only [compileModuleBudgetRecAux] at h; cases h
  | bfn :: bfs, hint :: hints, code, h => by
    dsimp only [compileModuleBudgetRecAux] at h
    split at h
    · rename_i c hl _
      split at h
      · rename_i cs hrest
        simp only [Except.ok.injEq] at h
        subst h
        have h1 : compileFn I lt hint bfn.toFn = .ok c := hl
        have h2 := compileOfBudgetAux hrest
        simp [compile, h1, h2]
      · simp at h
    · simp at h
    · simp at h

theorem compile_of_compileModuleBudgetRec {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    {bfs : List BudgetFn} {hints : List I.Hints} {exportBounds : List (Sym × Nat)}
    {code : List I.Directive}
    (h : compileModuleBudgetRec I lt raBytes extCallees exits nX maxBound bfs hints exportBounds =
      .ok code) :
    compile I lt (bfs.map BudgetFn.toFn) hints = .ok code := by
  dsimp only [compileModuleBudgetRec] at h
  split at h; · simp at h
  split at h; · simp at h
  exact compileOfBudgetAux h

theorem compileModuleBudgetRec_bounds_le {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    {bfs : List BudgetFn} {hints : List I.Hints} {exportBounds : List (Sym × Nat)}
    {code : List I.Directive}
    (h : compileModuleBudgetRec I lt raBytes extCallees exits nX maxBound bfs hints exportBounds =
      .ok code) :
    maxBound ≤ 2 ^ 64 ∧ maxBound + raBytes ≤ 2 ^ 64 ∧
      exportBounds.all (fun p => Nat.ble p.2 maxBound) = true := by
  dsimp only [compileModuleBudgetRec] at h
  split at h; · simp at h
  split at h
  · simp at h
  · rename_i hok
    simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at hok
    exact ⟨Nat.le_of_ble_eq_true hok.1.1, Nat.le_of_ble_eq_true hok.1.2, hok.2⟩

private theorem compileModuleBudgetRecAux_mem {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} :
    ∀ {bfs : List BudgetFn} {hints : List I.Hints} {code : List I.Directive},
      compileModuleBudgetRecAux I lt raBytes recSigs extCallees exits nX bfs hints = .ok code →
      ∀ bfn ∈ bfs, ∃ hint c k_f,
        Rega.lowerFn I hint (bfn.toFn.mid lt).ext (bfn.toFn.mid lt) = .ok c ∧
        c.IsInfixAt code k_f ∧ k_f ≤ code.length ∧
        checkAndBoundBudgetRecExt I raBytes recSigs extCallees exits nX hint
          (bfn.toFn.mid lt).ext bfn = true
  | [], _, _, _, _, hf => nomatch hf
  | _ :: _, [], _, h, _, _ => by dsimp only [compileModuleBudgetRecAux] at h; cases h
  | b0 :: bfs, hint :: hints, code, h, bfn, hf => by
    dsimp only [compileModuleBudgetRecAux] at h
    split at h
    · rename_i c hl hchk
      split at h
      · rename_i cs hrest
        simp only [Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.mp hf with rfl | hf'
        · exact ⟨hint, c, 0, hl, ⟨cs, rfl⟩, Nat.zero_le _, hchk⟩
        · obtain ⟨hint', c', k', hl', hinf', hklen', hchk'⟩ :=
            compileModuleBudgetRecAux_mem hrest bfn hf'
          refine ⟨hint', c', c.length + k', hl', ?_, by simp; exact hklen', hchk'⟩
          obtain ⟨tail, htail⟩ := hinf'
          exact ⟨tail, by
            have e : (c ++ cs).drop (c.length + k') = cs.drop k' := by
              rw [← List.drop_drop, List.drop_left' rfl]
            rw [e, htail]⟩
      · simp at h
    · simp at h
    · simp at h

private theorem compileModuleBudgetRecAux_code_labels {T : Target} (hcl : Rega.LabelClean T.toIsa)
    (lt : LegalTarget) (raBytes : Nat) (recSigs : List SigEntry)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat) :
    ∀ {bfs : List BudgetFn} {hints : List T.toIsa.Hints} {code : List T.Directive},
      compileModuleBudgetRecAux T.toIsa lt raBytes recSigs extCallees exits nX bfs hints =
        .ok code →
      (bfs.map (fun b => b.toFn.name)).Nodup →
      bfs.all (fun b => fnNameOk b.toFn.name) = true →
      (∀ (i : Nat) (l : Sym), code[i]? = some (T.frame.label l) →
        ∃ b ∈ bfs, l = b.toFn.name ∨ ∃ a, l = Rega.lname b.toFn.name a) ∧
      (∀ (i j : Nat) (l : Sym), code[i]? = some (T.frame.label l) →
        code[j]? = some (T.frame.label l) → i = j)
  | [], [], _, hcm, _, _ => by
    dsimp only [compileModuleBudgetRecAux] at hcm
    simp only [Except.ok.injEq] at hcm
    subst hcm
    exact ⟨fun _ _ hi => by simp at hi, fun _ _ _ hi => by simp at hi⟩
  | [], _ :: _, _, hcm, _, _ => by dsimp only [compileModuleBudgetRecAux] at hcm; cases hcm
  | _ :: _, [], _, hcm, _, _ => by dsimp only [compileModuleBudgetRecAux] at hcm; cases hcm
  | b0 :: bfs, h :: hs, code, hcm, hnd, hok => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    simp only [List.all_cons, Bool.and_eq_true] at hok
    dsimp only [compileModuleBudgetRecAux] at hcm
    split at hcm
    · rename_i c hl _
      split at hcm
      · rename_i cs hrest
        simp only [Except.ok.injEq] at hcm
        subst hcm
        obtain ⟨ih_mem, ih_uniq⟩ := compileModuleBudgetRecAux_code_labels hcl lt raBytes recSigs
          extCallees exits nX hrest hnd.2 hok.2
        have hc_mem : ∀ (i : Nat) (l : Sym), c[i]? = some (T.frame.label l) →
            l = b0.toFn.name ∨ ∃ a, l = Rega.lname b0.toFn.name a :=
          fun i l hi => Rega.lowerFn_label_mem hcl hl hi
        have hc_uniq := Rega.lowerFn_labelsUnique hcl hl
        constructor
        · intro i l hi
          by_cases hlt : i < c.length
          · rw [List.getElem?_append_left hlt] at hi
            exact ⟨b0, List.mem_cons_self, hc_mem i l hi⟩
          · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hi
            obtain ⟨g, hg, hl'⟩ := ih_mem (i - c.length) l hi
            exact ⟨g, List.mem_cons_of_mem b0 hg, hl'⟩
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
          · rw [List.getElem?_append_left hic] at hi; rw [List.getElem?_append_left hjc] at hj
            exact hc_uniq i j l hi hj
          · rw [List.getElem?_append_left hic] at hi
            rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
            exact absurd hi (fun h' => disj h' hj)
          · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
            rw [List.getElem?_append_left hjc] at hj
            exact absurd hj (fun h' => disj h' hi)
          · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
            rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
            have heq := ih_uniq (i - c.length) (j - c.length) l hi hj
            omega
      · simp at hcm
    · simp at hcm
    · simp at hcm

private theorem nodup_getElem?_inj_b : ∀ {xs : List Sym} {i j : Nat} {x : Sym},
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
    congrArg Nat.succ (nodup_getElem?_inj_b (List.nodup_cons.mp hnd).2 hi hj)

theorem compileModuleBudgetRec_labelsUnique {T : Target} (hcl : Rega.LabelClean T.toIsa)
    {lt : LegalTarget} {raBytes : Nat} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX maxBound : Nat} {bfs : List BudgetFn} {hints : List T.toIsa.Hints}
    {exportBounds : List (Sym × Nat)} {code : List T.Directive}
    (hcm : compileModuleBudgetRec T.toIsa lt raBytes extCallees exits nX maxBound bfs hints
      exportBounds = .ok code)
    (hnd : (bfs.map (fun b => b.toFn.name) ++ exits).Nodup)
    (hok : (bfs.map (fun b => b.toFn.name) ++ exits).all fnNameOk = true) :
    ∀ (i j : Nat) (l : Sym),
      (code ++ exits.map T.frame.label)[i]? = some (T.frame.label l) →
      (code ++ exits.map T.frame.label)[j]? = some (T.frame.label l) → i = j := by
  dsimp only [compileModuleBudgetRec] at hcm
  split at hcm; · simp at hcm
  split at hcm; · simp at hcm
  have hnd_split := List.nodup_append.mp hnd
  simp only [List.all_append, Bool.and_eq_true, List.all_map] at hok
  obtain ⟨hmem, huniq⟩ := compileModuleBudgetRecAux_code_labels hcl lt raBytes _ extCallees
    exits nX hcm hnd_split.1 hok.1
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
    obtain ⟨b, hb, hlf⟩ := hmem i₁ l hi₁
    rcases hlf with hl_eq | ⟨a, hl_eq⟩
    · exact hnd_split.2.2 l (hl_eq ▸ List.mem_map_of_mem hb) l hmemE rfl
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
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
    rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
    have heq := nodup_getElem?_inj_b hnd_split.2.1 (hEx _ _ hi) (hEx _ _ hj)
    omega

private theorem compileModuleBudgetRec_disjoint {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    {bfs : List BudgetFn} {hints : List I.Hints} {exportBounds : List (Sym × Nat)}
    {code : List I.Directive}
    (h : compileModuleBudgetRec I lt raBytes extCallees exits nX maxBound bfs hints exportBounds =
      .ok code) :
    (∀ p ∈ extCallees, p.1.1 ∉ bfs.map (fun b => b.toFn.name)) ∧
      compileModuleBudgetRecAux I lt raBytes
        (bfs.map (fun b => (b.toFn.name, lt.legalSig b.toFn.as, lt.legalSig b.toFn.rs)))
        extCallees exits nX bfs hints = .ok code := by
  dsimp only [compileModuleBudgetRec] at h
  split at h
  · simp at h
  · rename_i hno
    split at h
    · simp at h
    · refine ⟨fun p hp hmem => ?_, h⟩
      obtain ⟨b, hb, hnm⟩ := List.mem_map.mp hmem
      exact hno (List.any_eq_true.mpr ⟨p, hp, List.any_eq_true.mpr ⟨b, hb, beq_iff_eq.mpr hnm⟩⟩)

/-- Bundle of a compiled cyclic/mutually-recursive `BudgetFn` SCC on target `T`. -/
structure CompiledBudgetRec (T : Target) (lt : LegalTarget) (extCallees : List (SigEntry × Nat))
    (exits : List Sym) (nX : Nat) (bfs : List BudgetFn) (hints : List T.toIsa.Hints)
    (maxBound : Nat := 2048) (exportBounds : List (Sym × Nat) := []) where
  code : List T.Directive
  compileModuleBudgetRec_eq :
    compileModuleBudgetRec T.toIsa lt T.frame.raBytes extCallees exits nX maxBound
      bfs hints exportBounds = .ok code
  compile_eq : compile T.toIsa lt (bfs.map BudgetFn.toFn) hints = .ok code
  maxBound_le : maxBound ≤ 2 ^ 64
  total_ra_le : maxBound + T.frame.raBytes ≤ 2 ^ 64
  exportBounds_le : exportBounds.all (fun p => Nat.ble p.2 maxBound) = true
  host : T.mach.Host
  prog_host : T.mach.prog host = code ++ exits.map T.frame.label
  labelsUnique : T.LabelsUnique host

namespace CompiledBudgetRec

variable {T : Target} {lt : LegalTarget} {extCallees : List (SigEntry × Nat)}
  {exits : List Sym} {nX : Nat} {bfs : List BudgetFn} {hints : List T.toIsa.Hints}
  {maxBound : Nat} {exportBounds : List (Sym × Nat)}

/-- Exported stack bound for `nm` from `M`. -/
@[expose] def bound
    (_M : CompiledBudgetRec T lt extCallees exits nX bfs hints maxBound exportBounds)
    (nm : Sym) : Nat :=
  budgetBound exportBounds maxBound nm

/-- Legalized `(fnSig, stackBound)` entries exported by `M`. -/
@[expose] def sigBounds
    (_M : CompiledBudgetRec T lt extCallees exits nX bfs hints maxBound exportBounds) :
    List (SigEntry × Nat) :=
  sigBoundsBudgetRecOf lt bfs exportBounds maxBound

theorem bound_le_max
    (M : CompiledBudgetRec T lt extCallees exits nX bfs hints maxBound exportBounds)
    (nm : Sym) : M.bound nm ≤ maxBound := by
  dsimp only [bound, budgetBound]
  cases hlk : lookupFnBound exportBounds nm with
  | none => exact Nat.le_refl _
  | some b =>
    have hmem := lookupFnBound_mem hlk
    have hble := List.all_eq_true.mp M.exportBounds_le (nm, b) hmem
    exact Nat.le_of_ble_eq_true hble

theorem bound_ra_le
    (M : CompiledBudgetRec T lt extCallees exits nX bfs hints maxBound exportBounds)
    (nm : Sym) : M.bound nm + T.frame.raBytes ≤ 2 ^ 64 :=
  Nat.le_trans (Nat.add_le_add_right (M.bound_le_max nm) _) M.total_ra_le

theorem code_infix_host
    (M : CompiledBudgetRec T lt extCallees exits nX bfs hints maxBound exportBounds) :
    M.code.IsInfixAt (T.mach.prog M.host) 0 := by
  rw [M.prog_host]; exact ⟨exits.map T.frame.label, rfl⟩

theorem defined_exit_host
    (M : CompiledBudgetRec T lt extCallees exits nX bfs hints maxBound exportBounds)
    {g : Sym} (hg : g ∈ exits) : T.Defined M.host g := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
  refine ⟨M.code.length + i, ?_⟩
  rw [M.prog_host, List.getElem?_append_right (by omega), List.getElem?_map]; simp [hi]

end CompiledBudgetRec

/-- Metadata-only check over pre-evaluated `code` literal for a `CompiledBudgetRec`. -/
@[expose] def checkCompileBudgetRecLit {D : Type} (label : Sym → D) (progSmall : List D → Bool)
    (code : List D) (fnNames exits : List Sym) : Bool :=
  checkCompileBudgetRecResult label progSmall (.ok code) fnNames exits

theorem checkCompileBudgetRecLit_parts {D : Type} {label : Sym → D}
    {progSmall : List D → Bool} {code : List D} {fnNames exits : List Sym}
    (h : checkCompileBudgetRecLit label progSmall code fnNames exits = true) :
    fnNames.all fnNameOk = true ∧ exits.all fnNameOk = true ∧
      (fnNames ++ exits).Nodup ∧
      progSmall (code ++ exits.map label) = true := by
  dsimp only [checkCompileBudgetRecLit, checkCompileBudgetRecResult] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, stringsNodup_nodup h.1.2, h.2⟩

/-- Construct a literal-backed `CompiledBudgetRec` from pre-evaluated `code` and kernel proofs. -/
@[expose] def compileCheckedBudgetRecLit (T : Target) (L : TargetLayout T) (lt : LegalTarget)
    (hcl : Rega.LabelClean T.toIsa) (extCallees : List (SigEntry × Nat)) (exits : List Sym)
    (nX : Nat) (bfs : List BudgetFn) (hints : List T.toIsa.Hints) (maxBound : Nat := 2048)
    (exportBounds : List (Sym × Nat) := []) (code : List T.Directive)
    (hcm : compileModuleBudgetRec T.toIsa lt T.frame.raBytes extCallees exits nX maxBound
      bfs hints exportBounds = .ok code)
    (hchk : checkCompileBudgetRecLit T.frame.label L.progSmall code
      (bfs.map (fun b => b.toFn.name)) exits = true) :
    CompiledBudgetRec T lt extCallees exits nX bfs hints maxBound exportBounds where
  code := code
  compileModuleBudgetRec_eq := hcm
  compile_eq := compile_of_compileModuleBudgetRec hcm
  maxBound_le := (compileModuleBudgetRec_bounds_le hcm).1
  total_ra_le := (compileModuleBudgetRec_bounds_le hcm).2.1
  exportBounds_le := (compileModuleBudgetRec_bounds_le hcm).2.2
  host := L.layoutOf (code ++ exits.map T.frame.label)
    (checkCompileBudgetRecLit_parts hchk).2.2.2
  prog_host := L.prog_layoutOf _ _
  labelsUnique := by
    have hp := checkCompileBudgetRecLit_parts hchk
    intro i j l hi hj
    rw [L.prog_layoutOf _ hp.2.2.2] at hi hj
    exact compileModuleBudgetRec_labelsUnique hcl hcm hp.2.2.1
      (by simp only [List.all_append, Bool.and_eq_true]; exact ⟨hp.1, hp.2.1⟩) i j l hi hj

/-- Literal-backed compiled sub-chunk of a single cyclic `BudgetFn` SCC. -/
structure RecBudgetSubChunk (T : Target) (lt : LegalTarget) (recSigs : List SigEntry)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat) : Type 1 where
  bfs : List BudgetFn
  hints : List T.toIsa.Hints
  code : List T.Directive
  compileAux_eq :
    compileModuleBudgetRecAux T.toIsa lt T.frame.raBytes recSigs extCallees exits nX bfs hints =
      .ok code

@[expose] def recBudgetSubchunksBfs {T : Target} {lt : LegalTarget} {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    (scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX)) : List BudgetFn :=
  scs.foldr (fun sc acc => sc.bfs ++ acc) []

@[expose] def recBudgetSubchunksFns {T : Target} {lt : LegalTarget} {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    (scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX)) : List Fn :=
  (recBudgetSubchunksBfs scs).map BudgetFn.toFn

@[expose] def recBudgetSubchunksHints {T : Target} {lt : LegalTarget} {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    (scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX)) : List T.toIsa.Hints :=
  scs.foldr (fun sc acc => sc.hints ++ acc) []

@[expose] def recBudgetSubchunksCode {T : Target} {lt : LegalTarget} {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    (scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX)) : List T.Directive :=
  scs.foldr (fun sc acc => sc.code ++ acc) []

theorem compileModuleBudgetRecAux_append {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} :
    ∀ {bfs₁ bfs₂ : List BudgetFn} {hints₁ hints₂ : List I.Hints} {c₁ c₂ : List I.Directive},
      compileModuleBudgetRecAux I lt raBytes recSigs extCallees exits nX bfs₁ hints₁ = .ok c₁ →
      compileModuleBudgetRecAux I lt raBytes recSigs extCallees exits nX bfs₂ hints₂ = .ok c₂ →
      compileModuleBudgetRecAux I lt raBytes recSigs extCallees exits nX
        (bfs₁ ++ bfs₂) (hints₁ ++ hints₂) = .ok (c₁ ++ c₂) := by
  intro bfs₁
  induction bfs₁ with
  | nil =>
    intro bfs₂ hints₁ hints₂ c₁ c₂ h₁ h₂
    cases hints₁ with
    | nil =>
      change Except.ok [] = Except.ok c₁ at h₁
      simp only [Except.ok.injEq] at h₁
      subst h₁; exact h₂
    | cons _ _ =>
      change Except.error "compileModuleBudgetRec: fn/hints length mismatch" = _ at h₁
      cases h₁
  | cons bfn bfs₁ ih =>
    intro bfs₂ hints₁ hints₂ c₁ c₂ h₁ h₂
    cases hints₁ with
    | nil =>
      change Except.error "compileModuleBudgetRec: fn/hints length mismatch" = _ at h₁
      cases h₁
    | cons hint hints₁ =>
      rw [List.cons_append, List.cons_append]
      dsimp only [compileModuleBudgetRecAux] at h₁ ⊢
      cases hl : Rega.lowerFn I hint (bfn.toFn.mid lt).ext (bfn.toFn.mid lt) with
      | error e => simp [hl] at h₁
      | ok c =>
        cases hchk : checkAndBoundBudgetRecExt I raBytes recSigs extCallees exits nX hint
            (bfn.toFn.mid lt).ext bfn with
        | false => simp [hl, hchk] at h₁
        | true =>
          simp only [hl, hchk] at h₁ ⊢
          cases hrest : compileModuleBudgetRecAux I lt raBytes recSigs extCallees exits nX
              bfs₁ hints₁ with
          | error e => simp [hrest] at h₁
          | ok cs =>
            simp only [hrest, Except.ok.injEq] at h₁
            subst h₁
            rw [ih hrest h₂, List.append_assoc]

theorem compileModuleBudgetRecAux_subchunks_eq {T : Target} {lt : LegalTarget}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} :
    ∀ scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX),
      compileModuleBudgetRecAux T.toIsa lt T.frame.raBytes recSigs extCallees exits nX
        (recBudgetSubchunksBfs scs) (recBudgetSubchunksHints scs) =
        .ok (recBudgetSubchunksCode scs)
  | [] => rfl
  | sc :: scs => by
    dsimp only [recBudgetSubchunksBfs, recBudgetSubchunksHints, recBudgetSubchunksCode,
      List.foldr_cons]
    exact compileModuleBudgetRecAux_append sc.compileAux_eq
      (compileModuleBudgetRecAux_subchunks_eq scs)

/-- Metadata-only validator assembling `RecBudgetSubChunk`s into a single `CompiledBudgetRec`. -/
@[expose] def checkRecBudgetSubchunks {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)}
    {exits : List Sym} {nX : Nat} (maxBound : Nat) (exportBounds : List (Sym × Nat))
    (scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX)) : Bool :=
  let bfs := recBudgetSubchunksBfs scs
  let fnNames := bfs.map (fun b => b.toFn.name)
  let code := recBudgetSubchunksCode scs
  sigListBeq recSigs (budgetRecSigsOf lt bfs) &&
  !(extCallees.any (fun p => fnNames.any (fun nm => nm == p.1.1))) &&
  Nat.ble maxBound (2 ^ 64) &&
  Nat.ble (maxBound + T.frame.raBytes) (2 ^ 64) &&
  exportBounds.all (fun p => Nat.ble p.2 maxBound) &&
  fnNames.all fnNameOk &&
  exits.all fnNameOk &&
  stringsNodup (fnNames ++ exits) &&
  L.progSmall (code ++ exits.map T.frame.label)

private theorem eq_rec_compileModuleBudgetRecAux {I : Isa} {lt : LegalTarget} {raBytes : Nat}
    {r₁ r₂ : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {bfs : List BudgetFn} {hints : List I.Hints} {code : List I.Directive}
    (h : r₁ = r₂)
    (haux : compileModuleBudgetRecAux I lt raBytes r₁ extCallees exits nX bfs hints = .ok code) :
    compileModuleBudgetRecAux I lt raBytes r₂ extCallees exits nX bfs hints = .ok code :=
  h ▸ haux

private theorem ext_disj_budgetNames_to_bfs {extCallees : List (SigEntry × Nat)}
    {bfs : List BudgetFn}
    (h : !(extCallees.any (fun p => (bfs.map (fun b => b.toFn.name)).any
      (fun nm => nm == p.1.1))) = true) :
    !(extCallees.any (fun p => bfs.any (fun b => b.toFn.name == p.1.1))) = true := by
  simpa [List.any_map, Function.comp_def] using h

theorem linkBudgetRecSubchunks_cm {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    (maxBound : Nat) (exportBounds : List (Sym × Nat))
    (scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX))
    (h : checkRecBudgetSubchunks L maxBound exportBounds scs = true) :
    compileModuleBudgetRec T.toIsa lt T.frame.raBytes extCallees exits nX maxBound
      (recBudgetSubchunksBfs scs) (recBudgetSubchunksHints scs) exportBounds =
      .ok (recBudgetSubchunksCode scs) := by
  dsimp only [checkRecBudgetSubchunks] at h
  simp only [Bool.and_eq_true] at h
  have haux := eq_rec_compileModuleBudgetRecAux (sigListBeq_eq h.1.1.1.1.1.1.1.1)
    (compileModuleBudgetRecAux_subchunks_eq scs)
  dsimp only [budgetRecSigsOf] at haux
  have hno : (extCallees.any (fun p =>
      (recBudgetSubchunksBfs scs).any (fun b => b.toFn.name == p.1.1))) = false := by
    have h0 := ext_disj_budgetNames_to_bfs h.1.1.1.1.1.1.1.2
    cases hq : extCallees.any (fun p =>
        (recBudgetSubchunksBfs scs).any (fun b => b.toFn.name == p.1.1))
    · rfl
    · simp [hq] at h0
  dsimp only [compileModuleBudgetRec]
  simp only [hno, Bool.false_eq_true, ↓reduceIte,
    h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, Bool.and_self, Bool.not_true]
  exact haux

theorem linkBudgetRecSubchunks_chk {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    (maxBound : Nat) (exportBounds : List (Sym × Nat))
    (scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX))
    (h : checkRecBudgetSubchunks L maxBound exportBounds scs = true) :
    checkCompileBudgetRecLit T.frame.label L.progSmall (recBudgetSubchunksCode scs)
      ((recBudgetSubchunksBfs scs).map (fun b => b.toFn.name)) exits = true := by
  dsimp only [checkRecBudgetSubchunks] at h
  simp only [Bool.and_eq_true] at h
  dsimp only [checkCompileBudgetRecLit, checkCompileBudgetRecResult]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨h.1.1.1.2, h.1.1.2⟩, h.1.2⟩, h.2⟩

/-- Link `RecBudgetSubChunk`s into a single `CompiledBudgetRec` in O(#subchunks) time. -/
@[expose] def linkBudgetRecSubchunks {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    (hcl : Rega.LabelClean T.toIsa) {recSigs : List SigEntry}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    (maxBound : Nat) (exportBounds : List (Sym × Nat))
    (scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX))
    (h : checkRecBudgetSubchunks L maxBound exportBounds scs = true) :
    CompiledBudgetRec T lt extCallees exits nX (recBudgetSubchunksBfs scs)
      (recBudgetSubchunksHints scs) maxBound exportBounds :=
  compileCheckedBudgetRecLit T L lt hcl extCallees exits nX
    (recBudgetSubchunksBfs scs) (recBudgetSubchunksHints scs) maxBound exportBounds
    (recBudgetSubchunksCode scs)
    (linkBudgetRecSubchunks_cm L maxBound exportBounds scs h)
    (linkBudgetRecSubchunks_chk L maxBound exportBounds scs h)

private theorem wp_evalMono :
    BudgetFn.EvalMono (fun Γcall _ bfn => Func.wp Γcall bfn.toFn.body) :=
  fun bfn _ _ _ _ hC _ xs m _ _ hwp => wp_env_mono hC (bfn.toFn.body Val Cont xs) m hwp

private theorem bfn_name_not_mem_externs {BM : BudgetModule} (hnd : BM.toModule.namesNodup)
    {bfn : BudgetFn} (hbfn : bfn ∈ BM.fns) {as bs : List Ty} :
    (bfn.toFn.name, as, bs) ∉ BM.extSigs :=
  fn_name_not_mem_externs' (M := BM.toModule) hnd (List.mem_map_of_mem hbfn)

private theorem legalEnv_budgetCallSlot_ext {BM : BudgetModule} {lt : LegalTarget}
    {bfn : BudgetFn} {Γext : BudgetEnv} {G : BudgetEnv} {sb : Nat}
    {g : Sym} (hg : g ∉ BM.fns.map (fun b => b.toFn.name))
    {as bs : List Ty} {xs' : Tup Val as} {m0 : Mem 64} {Q' : Post bs} {X' : XPost}
    (h : legalEnv lt (BudgetEnv.callSlot BM bfn Γext G sb) g as bs xs' m0 Q' X') :
    legalEnv lt (Env.restrict (Γext (sb - bfn.maxFrame)) BM.extSigs) g as bs xs' m0 Q' X' := by
  rcases h with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hstep⟩
  rcases hstep with ⟨hsig, _⟩ | ⟨hsig, hΓ⟩
  · obtain ⟨b, hb, hbeq⟩ := List.mem_map.mp hsig
    have hnm : b.toFn.name = g := congrArg Prod.fst hbeq
    exact absurd (hnm ▸ List.mem_map_of_mem hb) hg
  · exact ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hsig, hΓ⟩

/-- **Single-shot `BudgetEnv.lfp` SCC linking theorem (`link_scc_budget_lfp`):**
proves `T.Defined` and `T.FnSpec` for `BudgetEnv.semScc BM Γext sb` at stack bound `sb` for
every `sb` with `sb + T.frame.raBytes ≤ 2^64`, honoring per-function `bfn.maxFrame` and
`bfn.minEntry` with zero SCC-wide `baseBound` bleed onto sibling functions. -/
theorem link_scc_budget_lfp {T : Target} {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {bfs : List BudgetFn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    {exportBounds : List (Sym × Nat)}
    (M : CompiledBudgetRec T lt extCallees exits nX bfs hints maxBound exportBounds)
    (BM : BudgetModule) (hbfs : BM.fns = bfs) (h : T.mach.Host)
    (Γext : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hcyc : checkCyclic BM.toModule = true)
    (hwf : ∀ bfn ∈ BM.fns, bfn.toFn.Wf)
    (hsupp : ∀ bfn ∈ BM.fns, (bfn.toFn.earlyOpt).body.supportsSource lt = true)
    (hext : ∀ p ∈ extCallees,
      T.FnSpec h p.1.1
        (legalEnv lt (Env.restrict Γext BM.extSigs) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : ∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2)
    (hexits : ∀ g ∈ exits, T.Defined h g) :
    ∀ sb, sb + T.frame.raBytes ≤ 2 ^ 64 → ∀ bfn ∈ BM.fns,
      T.Defined h bfn.toFn.name ∧
      T.FnSpec h bfn.toFn.name
        (legalEnv lt (Env.onlyFn bfn.toFn (BudgetEnv.semScc BM Γext sb))
          bfn.toFn.name (lt.legalSig bfn.toFn.as) (lt.legalSig bfn.toFn.rs))
        sb nX := by
  have hnd := Module.namesNodup_of_checkNamesNodup ((Bool.and_eq_true _ _).mp hcyc).1
  obtain ⟨hdisj, haux⟩ :=
    compileModuleBudgetRec_disjoint (show compileModuleBudgetRec T.toIsa lt T.frame.raBytes
      extCallees exits nX maxBound BM.fns hints exportBounds = .ok M.code from
      by rw [hbfs]; exact M.compileModuleBudgetRec_eq)
  have htot_ra := M.total_ra_le
  let cap : Nat := 2 ^ 64 - T.frame.raBytes
  let G : BudgetEnv := fun sb => pullEnv lt (machEnv T h sb nX)
  have hpre : ∀ sb, sb ≤ cap → Env.le (BudgetEnv.sccOp BM Γext G sb) (G sb) := by
    intro sb hsb_cap f as bs xs m P E hΦ
    have hn_sb : sb + T.frame.raBytes ≤ 2 ^ 64 := by dsimp only [cap] at hsb_cap; omega
    rcases hΦ with ⟨bfn, hbfn, rfl, rfl, rfl, hmax, hmin, hwp⟩
    obtain ⟨hint, c, k_f, hl, hinf, hklen, hchk⟩ :=
      compileModuleBudgetRecAux_mem haux bfn hbfn
    have hc_f : c.IsInfixAt (T.mach.prog h) (k₀ + k_f) := infix_trans' hklen hinf hc
    obtain ⟨hfr_max, hcal_b, hex_b⟩ := checkAndBoundBudgetRecExt_spec hchk
    have hfr_eff : Rega.effFrame T.toIsa hint (bfn.toFn.mid lt).ext ≤ sb := by omega
    let bound : Sym → Nat := fun g =>
      if (BM.fns.map (fun b => b.toFn.name)).contains g then sb - bfn.maxFrame
      else match extCallees.find? (fun q => q.1.1 == g) with
        | some q => q.2
        | none => 0
    have hcal : ∀ g as' bs', (g, as', bs') ∈ (bfn.toFn.mid lt).ext.callees →
        T.FnSpec h g (legalEnv lt (BudgetEnv.callSlot BM bfn (BudgetEnv.const Γext) G sb)
          g as' bs') (bound g) nX ∧
        Rega.effFrame T.toIsa hint (bfn.toFn.mid lt).ext + T.frame.raBytes + bound g ≤ sb := by
      intro g as' bs' hg
      rcases hcal_b (g, as', bs') hg with hrec_sig | ⟨_, bg, hlk, hbg_b⟩
      · obtain ⟨gbfn, hgbfn, hgeq⟩ := List.mem_map.mp hrec_sig
        rcases Prod.mk.inj hgeq with ⟨rfl, hsig_ab⟩
        rcases Prod.mk.inj hsig_ab with ⟨rfl, rfl⟩
        have hmem_nm : gbfn.toFn.name ∈ BM.fns.map (fun b => b.toFn.name) :=
          List.mem_map_of_mem hgbfn
        have hcon : (BM.fns.map (fun b => b.toFn.name)).contains gbfn.toFn.name = true := by
          simpa using hmem_nm
        have hbd : bound gbfn.toFn.name = sb - bfn.maxFrame := by
          dsimp only [bound]; simp only [hcon, ↓reduceIte]
        rw [hbd]
        refine ⟨?_, by omega⟩
        intro args' m0 Q' X' hleg
        have hpull : legalEnv lt (pullEnv lt (machEnv T h (sb - bfn.maxFrame) nX))
            gbfn.toFn.name (lt.legalSig gbfn.toFn.as) (lt.legalSig gbfn.toFn.rs)
            args' m0 Q' X' := by
          rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hst⟩
          rcases hst with ⟨_, hG⟩ | ⟨hmemE, _⟩
          · exact ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hG⟩
          · exact absurd hmemE (bfn_name_not_mem_externs hnd hgbfn)
        exact legalEnv_pullEnv_le lt (machEnv_conseq T h (sb - bfn.maxFrame) nX)
          gbfn.toFn.name _ _ args' m0 Q' X' hpull
      · have hmem_ext : ((g, as', bs'), bg) ∈ extCallees := lookupBound_mem hlk
        have hnot_nm : g ∉ BM.fns.map (fun b => b.toFn.name) :=
          hdisj ((g, as', bs'), bg) hmem_ext
        have hcon : (BM.fns.map (fun b => b.toFn.name)).contains g = false := by
          simpa [List.contains_eq_mem] using hnot_nm
        have hbd : bound g = bg := by
          dsimp only [bound]; rw [hcon]
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases hfnd : extCallees.find? (fun q => q.1.1 == g) with
          | none =>
            exfalso
            have hnot := List.find?_eq_none.mp hfnd ((g, as', bs'), bg) hmem_ext
            simp at hnot
          | some q =>
            have hqmem : q ∈ extCallees := List.mem_of_find?_eq_some hfnd
            have hpred : q.1.1 = g :=
              beq_iff_eq.mp (find?_pred' (p := fun q : SigEntry × Nat => q.1.1 == g) hfnd)
            exact hext_uniq q hqmem ((g, as', bs'), bg) hmem_ext hpred
        rw [hbd]
        refine ⟨?_, by omega⟩
        exact Target.FnSpec.of_spec T (hext ((g, as', bs'), bg) hmem_ext)
          fun _ _ _ _ hleg => legalEnv_budgetCallSlot_ext hnot_nm hleg
    have hex : ∀ g, g ∈ (bfn.toFn.mid lt).ext.exits → T.Defined h g ∧ nX ≤ sb :=
      fun g hg => ⟨hexits g (hex_b g hg).1, Nat.le_trans (hex_b g hg).2 hmin⟩
    exact compileFn_body_correct T h lt hint (bfn.toFn.mid lt).ext bfn.toFn
      (BudgetEnv.callSlot BM bfn (BudgetEnv.const Γext) G sb) sb nX bound
      (hwf bfn hbfn) (hsupp bfn hbfn) hl hc_f hu hfr_eff hn_sb hcal hex xs m P E hwp
  have hlfp := BudgetEnv.lfp_le_of_prefix_below
    (BudgetEnv.mkSccOp_budgetLocal BM (BudgetEnv.const Γext) wp_evalMono) cap G hpre
  intro sb hsb bfn hbfn
  have hsb_cap : sb ≤ cap := by dsimp only [cap]; omega
  obtain ⟨hint, c, k_f, hl, hinf, hklen, _⟩ := compileModuleBudgetRecAux_mem haux bfn hbfn
  refine ⟨defined_of_lowerFn' (f := bfn.toFn.mid lt) hl (infix_trans' hklen hinf hc), ?_⟩
  intro args m Q X hleg
  rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, _, ha, hb, hsem⟩
  subst ha; subst hb
  have hG := hlfp sb hsb_cap bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs₀ m P₀ E₀ hsem
  exact legalEnv_pullEnv_le lt (machEnv_conseq T h sb nX)
    bfn.toFn.name (lt.legalSig bfn.toFn.as) (lt.legalSig bfn.toFn.rs) args m Q X
    ⟨bfn.toFn.as, bfn.toFn.rs, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hG⟩

/-- Host specialization of `link_scc_budget_lfp` with `extCallees = []`. -/
theorem link_scc_budget_lfp_host {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} {bfs : List BudgetFn} {hints : List T.toIsa.Hints}
    {maxBound : Nat} {exportBounds : List (Sym × Nat)}
    (M : CompiledBudgetRec T lt [] exits nX bfs hints maxBound exportBounds)
    (BM : BudgetModule) (hbfs : BM.fns = bfs) (Γext : Env)
    (hcyc : checkCyclic BM.toModule = true)
    (hwf : ∀ bfn ∈ BM.fns, bfn.toFn.Wf)
    (hsupp : ∀ bfn ∈ BM.fns, (bfn.toFn.earlyOpt).body.supportsSource lt = true) :
    ∀ sb, sb + T.frame.raBytes ≤ 2 ^ 64 → ∀ bfn ∈ BM.fns,
      T.Defined M.host bfn.toFn.name ∧
      T.FnSpec M.host bfn.toFn.name
        (legalEnv lt (Env.onlyFn bfn.toFn (BudgetEnv.semScc BM Γext sb))
          bfn.toFn.name (lt.legalSig bfn.toFn.as) (lt.legalSig bfn.toFn.rs))
        sb nX :=
  link_scc_budget_lfp M BM hbfs M.host Γext 0 M.code_infix_host M.labelsUnique hcyc hwf hsupp
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ hg => M.defined_exit_host hg)

/-! ## 3. Mixed Acyclic + Cyclic SCC `Chunk` / `Chunk.recSCC` Linking -/

/-- A compiled program unit in a mixed acyclic + recursive-SCC module: an acyclic `CompiledChunk`,
a fuel-indexed `CompiledRec` SCC, or a stack-budgeted `CompiledBudgetRec` SCC. -/
inductive Chunk (T : Target) (lt : LegalTarget) (exits : List Sym) (nX : Nat) : Type 1 where
  | acyc (c : CompiledChunk T lt exits nX) : Chunk T lt exits nX
  | recSCC (extCallees : List (SigEntry × Nat)) (fuel : Nat) (fs : List Fn)
      (hints : List T.toIsa.Hints) (maxBound : Nat)
      (compiled : CompiledRec T lt extCallees exits nX fuel fs hints maxBound) :
      Chunk T lt exits nX
  | recBudgetSCC (extCallees : List (SigEntry × Nat)) (bfs : List BudgetFn)
      (hints : List T.toIsa.Hints) (maxBound : Nat) (exportBounds : List (Sym × Nat))
      (compiled : CompiledBudgetRec T lt extCallees exits nX bfs hints maxBound exportBounds) :
      Chunk T lt exits nX

namespace Chunk

variable {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}

/-- Build a `.recSCC` chunk from a list of `RecSubChunk`s via `linkRecSubchunks`. -/
@[expose] def ofRecSubchunks (L : TargetLayout T) (hcl : Rega.LabelClean T.toIsa)
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)}
    (fuel maxBound : Nat)
    (scs : List (RecSubChunk T lt recSigs extCallees exits nX))
    (h : checkRecSubchunks L fuel maxBound scs = true) : Chunk T lt exits nX :=
  .recSCC extCallees fuel (recSubchunksFns scs) (recSubchunksHints scs) maxBound
    (linkRecSubchunks L hcl fuel maxBound scs h)

/-- Build a `.recBudgetSCC` chunk from `RecBudgetSubChunk`s via `linkBudgetRecSubchunks`. -/
@[expose] def ofBudgetRecSubchunks (L : TargetLayout T) (hcl : Rega.LabelClean T.toIsa)
    {recSigs : List SigEntry} {extCallees : List (SigEntry × Nat)}
    (maxBound : Nat) (exportBounds : List (Sym × Nat))
    (scs : List (RecBudgetSubChunk T lt recSigs extCallees exits nX))
    (h : checkRecBudgetSubchunks L maxBound exportBounds scs = true) : Chunk T lt exits nX :=
  .recBudgetSCC extCallees (recBudgetSubchunksBfs scs) (recBudgetSubchunksHints scs)
    maxBound exportBounds (linkBudgetRecSubchunks L hcl maxBound exportBounds scs h)

/-- Typed IR functions belonging to chunk `c`. -/
@[expose] def fns (c : Chunk T lt exits nX) : List Fn :=
  Chunk.casesOn c (fun c => c.fs) (fun _ _ fs _ _ _ => fs)
    (fun _ bfs _ _ _ _ => bfs.map BudgetFn.toFn)

/-- Register-allocation hints belonging to chunk `c`. -/
@[expose] def hints (c : Chunk T lt exits nX) : List T.toIsa.Hints :=
  Chunk.casesOn c (fun c => c.hints) (fun _ _ _ h _ _ => h) (fun _ _ h _ _ _ => h)

/-- Compiled directive stream of chunk `c`. -/
@[expose] def code (c : Chunk T lt exits nX) : List T.Directive :=
  Chunk.casesOn c (fun c => c.compiled.code) (fun _ _ _ _ _ m => m.code)
    (fun _ _ _ _ _ m => m.code)

/-- Declared stack-bound cap of chunk `c`. -/
@[expose] def maxBound (c : Chunk T lt exits nX) : Nat :=
  Chunk.casesOn c (fun c => c.maxBound) (fun _ _ _ _ mb _ => mb)
    (fun _ _ _ mb _ _ => mb)

/-- External callee stack bounds assumed by chunk `c`. -/
@[expose] def extCallees (c : Chunk T lt exits nX) : List (SigEntry × Nat) :=
  Chunk.casesOn c (fun c => c.extCallees) (fun ext _ _ _ _ _ => ext)
    (fun ext _ _ _ _ _ => ext)

/-- Exported `(SigEntry, stackBound)` entries of chunk `c` for downstream chunks. -/
@[expose] def sigBounds (c : Chunk T lt exits nX) : List (SigEntry × Nat) :=
  Chunk.casesOn c (fun c => c.compiled.sigBounds) (fun _ _ _ _ _ m => m.sigBounds)
    (fun _ _ _ _ _ m => m.sigBounds)

/-- Stack bound exported by chunk `c` for symbol `nm`. -/
@[expose] def bound (c : Chunk T lt exits nX) (nm : Sym) : Nat :=
  Chunk.casesOn c (fun m => m.compiled.bound nm) (fun _ fuel _ _ _ m => m.boundAt fuel)
    (fun _ _ _ _ _ m => m.bound nm)

end Chunk

/-- Concatenated typed functions across a mixed chunk list. -/
@[expose] def sccChunksFns {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    List (Chunk T lt exits nX) → List Fn
  | [] => []
  | c :: cs => c.fns ++ sccChunksFns cs

/-- Concatenated hints across a mixed chunk list. -/
@[expose] def sccChunksHints {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    List (Chunk T lt exits nX) → List T.toIsa.Hints
  | [] => []
  | c :: cs => c.hints ++ sccChunksHints cs

/-- Concatenated directive stream across a mixed chunk list. -/
@[expose] def sccChunksCode {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    List (Chunk T lt exits nX) → List T.Directive
  | [] => []
  | c :: cs => c.code ++ sccChunksCode cs

/-- Maximum stack bound across a mixed chunk list. -/
@[expose] def sccChunksMaxBound {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    List (Chunk T lt exits nX) → Nat
  | [] => 0
  | c :: cs => Nat.max c.maxBound (sccChunksMaxBound cs)

theorem sccChunksFns_append {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (cs₁ cs₂ : List (Chunk T lt exits nX)),
      sccChunksFns (cs₁ ++ cs₂) = sccChunksFns cs₁ ++ sccChunksFns cs₂
  | [], _ => rfl
  | c :: cs₁, cs₂ => by
      simp only [List.cons_append, sccChunksFns, sccChunksFns_append cs₁ cs₂, List.append_assoc]

theorem sccChunksCode_append {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (cs₁ cs₂ : List (Chunk T lt exits nX)),
      sccChunksCode (cs₁ ++ cs₂) = sccChunksCode cs₁ ++ sccChunksCode cs₂
  | [], _ => rfl
  | c :: cs₁, cs₂ => by
      simp only [List.cons_append, sccChunksCode, sccChunksCode_append cs₁ cs₂, List.append_assoc]

theorem sccChunksMaxBound_nil {T : Target} {lt : LegalTarget} {exits : List Sym} {nX B : Nat} :
    sccChunksMaxBound ([] : List (Chunk T lt exits nX)) ≤ B :=
  Nat.zero_le B

theorem sccChunksMaxBound_cons {T : Target} {lt : LegalTarget} {exits : List Sym} {nX B : Nat}
    {c : Chunk T lt exits nX} {cs : List (Chunk T lt exits nX)}
    (hc : c.maxBound ≤ B) (hcs : sccChunksMaxBound cs ≤ B) :
    sccChunksMaxBound (c :: cs) ≤ B :=
  Nat.max_le.mpr ⟨hc, hcs⟩

theorem sccChunksMaxBound_append {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (cs₁ cs₂ : List (Chunk T lt exits nX)),
      sccChunksMaxBound (cs₁ ++ cs₂) = Nat.max (sccChunksMaxBound cs₁) (sccChunksMaxBound cs₂)
  | [], cs₂ => by simp [sccChunksMaxBound]
  | c :: cs₁, cs₂ => by
      simp only [List.cons_append, sccChunksMaxBound, sccChunksMaxBound_append cs₁ cs₂,
        Nat.max_assoc]

/-- Check that every chunk's `extCallees` is compatible with the accumulated `sigBounds` of
preceding chunks plus `ext₀`. -/
@[expose] def checkSccChunksExt {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (acc : List (SigEntry × Nat)) : List (Chunk T lt exits nX) → Bool
  | [] => true
  | c :: cs =>
      checkExtCompat acc c.extCallees &&
      checkSccChunksExt (c.sigBounds ++ acc) cs

/-- O(N) metadata-only linker validator for a mixed list of `.acyc` and `.recSCC` chunks. -/
@[expose] def checkLinkSccList {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (ext₀ : List (SigEntry × Nat))
    (chunks : List (Chunk T lt exits nX)) : Bool :=
  let fnNames := (sccChunksFns chunks).map Fn.name
  let prog := sccChunksCode chunks ++ exits.map T.frame.label
  checkSccChunksExt ext₀ chunks &&
  !(ext₀.any (fun p => fnNames.any (fun nm => nm == p.1.1))) &&
  fnNames.all fnNameOk &&
  exits.all fnNameOk &&
  stringsNodup (fnNames ++ exits) &&
  L.progSmall prog

/-- Variant of `checkLinkSccList` checking label uniqueness via `L.labelsNodup`. -/
@[expose] def checkLinkSccListWithLabels {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (ext₀ : List (SigEntry × Nat))
    (chunks : List (Chunk T lt exits nX)) : Bool :=
  let fnNames := (sccChunksFns chunks).map Fn.name
  let prog := sccChunksCode chunks ++ exits.map T.frame.label
  checkSccChunksExt ext₀ chunks &&
  !(ext₀.any (fun p => fnNames.any (fun nm => nm == p.1.1))) &&
  stringsNodup (fnNames ++ exits) &&
  L.labelsNodup prog &&
  L.progSmall prog

/-- Convert source external signature entries into `Extern` declarations. -/
@[expose] def externsOfSigs (sigs : List SigEntry) : List Extern :=
  sigs.map fun s => ⟨s.1, s.2.1, s.2.2⟩

/-- Kernel-reducible single-chunk call-graph check (`Module.checkAcyclic` for `.acyc`,
`LinkRec.checkCyclic` for `.recSCC` / `.recBudgetSCC`). -/
@[expose] def Chunk.callsOk {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (extSigs : List SigEntry) (c : Chunk T lt exits nX) : Bool :=
  Chunk.casesOn c
    (fun m => Module.checkAcyclic ⟨m.fs, externsOfSigs extSigs, exits⟩)
    (fun _ _ fs _ _ _ => LinkRec.checkCyclic ⟨fs, externsOfSigs extSigs, exits⟩)
    (fun _ bfs _ _ _ _ =>
      LinkRec.checkCyclic ⟨bfs.map BudgetFn.toFn, externsOfSigs extSigs, exits⟩)

/-- Kernel-reducible call-graph checker validating `Module.checkAcyclic` on every `.acyc` chunk
and `LinkRec.checkCyclic` on every `.recSCC`/`.recBudgetSCC` chunk, threading signatures. -/
@[expose] def checkChunksCalls {T : Target} {lt : LegalTarget} {nX : Nat}
    (exits : List Sym) : List SigEntry → List (Chunk T lt exits nX) → Bool
  | _, [] => true
  | extSigs, c :: rest =>
      c.callsOk extSigs && checkChunksCalls exits (c.fns.map Fn.sig ++ extSigs) rest

theorem checkLinkSccList_parts {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} {ext₀ : List (SigEntry × Nat)}
    {chunks : List (Chunk T lt exits nX)}
    (h : checkLinkSccList L ext₀ chunks = true) :
    checkSccChunksExt ext₀ chunks = true ∧
      (∀ p ∈ ext₀, p.1.1 ∉ (sccChunksFns chunks).map Fn.name) ∧
      ((sccChunksFns chunks).map Fn.name).all fnNameOk = true ∧
      exits.all fnNameOk = true ∧
      ((sccChunksFns chunks).map Fn.name ++ exits).Nodup ∧
      L.progSmall (sccChunksCode chunks ++ exits.map T.frame.label) = true := by
  dsimp only [checkLinkSccList] at h
  simp only [Bool.and_eq_true] at h
  refine ⟨h.1.1.1.1.1, fun p hp hmem => ?_, h.1.1.1.2, h.1.1.2,
    stringsNodup_nodup h.1.2, h.2⟩
  have hfalse := bool_not_any_eq_false h.1.1.1.1.2
  have hmem' : ((sccChunksFns chunks).map Fn.name).any (fun nm => nm == p.1.1) = true :=
    List.any_eq_true.mpr ⟨p.1.1, hmem, beq_iff_eq.mpr rfl⟩
  have hany : ext₀.any (fun p => ((sccChunksFns chunks).map Fn.name).any
      (fun nm => nm == p.1.1)) = true :=
    List.any_eq_true.mpr ⟨p, hp, hmem'⟩
  rw [hany] at hfalse
  cases hfalse

/-- Linked machine-code host for a validated mixed `Chunk` list. -/
@[expose] def sccHost {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (ext₀ : List (SigEntry × Nat))
    (chunks : List (Chunk T lt exits nX))
    (h : checkLinkSccList L ext₀ chunks = true) : T.mach.Host :=
  L.layoutOf (sccChunksCode chunks ++ exits.map T.frame.label)
    (checkLinkSccList_parts h).2.2.2.2.2

theorem sccProg_host {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (ext₀ : List (SigEntry × Nat))
    (chunks : List (Chunk T lt exits nX))
    (h : checkLinkSccList L ext₀ chunks = true) :
    T.mach.prog (sccHost L ext₀ chunks h) = sccChunksCode chunks ++ exits.map T.frame.label :=
  L.prog_layoutOf _ _

theorem sccCode_infix_host {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (ext₀ : List (SigEntry × Nat))
    (chunks : List (Chunk T lt exits nX))
    (h : checkLinkSccList L ext₀ chunks = true) :
    (sccChunksCode chunks).IsInfixAt (T.mach.prog (sccHost L ext₀ chunks h)) 0 := by
  rw [sccProg_host]; exact ⟨exits.map T.frame.label, rfl⟩

theorem sccDefined_exit_host {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (ext₀ : List (SigEntry × Nat))
    (chunks : List (Chunk T lt exits nX))
    (h : checkLinkSccList L ext₀ chunks = true) {g : Sym} (hg : g ∈ exits) :
    T.Defined (sccHost L ext₀ chunks h) g := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
  refine ⟨(sccChunksCode chunks).length + i, ?_⟩
  rw [sccProg_host, List.getElem?_append_right (by omega), List.getElem?_map]; simp [hi]

private theorem nodup_getElem?_inj' : ∀ {xs : List Sym} {i j : Nat} {x : Sym},
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
      congrArg Nat.succ (nodup_getElem?_inj' (List.nodup_cons.mp hnd).2 hi hj)

private theorem chunk_code_labels {T : Target} (hcl : Rega.LabelClean T.toIsa)
    {lt : LegalTarget} {exits : List Sym} {nX : Nat} (c : Chunk T lt exits nX)
    (hnd : (c.fns.map Fn.name).Nodup) (hok : c.fns.all (fun f => fnNameOk f.name) = true) :
    (∀ (i : Nat) (l : Sym), c.code[i]? = some (T.frame.label l) →
      ∃ f ∈ c.fns, l = f.name ∨ ∃ a, l = Rega.lname f.name a) ∧
    (∀ (i j : Nat) (l : Sym), c.code[i]? = some (T.frame.label l) →
      c.code[j]? = some (T.frame.label l) → i = j) := by
  cases c with
  | acyc cc =>
      exact compileModule_code_labels hcl lt T.frame.raBytes exits nX
        cc.compiled.compileModule_eq hnd hok
  | recSCC ext fuel fs hints maxB cr =>
      obtain ⟨_, haux⟩ := compileModuleRec_disjoint' cr.compileModuleRec_eq
      exact compileModuleRecAux_code_labels hcl lt T.frame.raBytes _ ext exits nX haux hnd hok
  | recBudgetSCC ext bfs hints maxB expB cbr =>
      obtain ⟨_, haux⟩ := compileModuleBudgetRec_disjoint cbr.compileModuleBudgetRec_eq
      have hnd' : (bfs.map (fun b => b.toFn.name)).Nodup := by
        dsimp only [Chunk.fns] at hnd
        rwa [List.map_map] at hnd
      have hok' : bfs.all (fun b => fnNameOk b.toFn.name) = true := by
        dsimp only [Chunk.fns] at hok
        rwa [List.all_map] at hok
      obtain ⟨hm, hu⟩ := compileModuleBudgetRecAux_code_labels hcl lt T.frame.raBytes _ ext
        exits nX haux hnd' hok'
      refine ⟨fun i l hi => ?_, hu⟩
      obtain ⟨b, hb, hl⟩ := hm i l hi
      exact ⟨b.toFn, List.mem_map_of_mem hb, hl⟩

private theorem sccChunks_code_labels {T : Target} (hcl : Rega.LabelClean T.toIsa)
    {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (chunks : List (Chunk T lt exits nX)),
      ((sccChunksFns chunks).map Fn.name).Nodup →
      (sccChunksFns chunks).all (fun f => fnNameOk f.name) = true →
      (∀ (i : Nat) (l : Sym), (sccChunksCode chunks)[i]? = some (T.frame.label l) →
        ∃ f ∈ sccChunksFns chunks, l = f.name ∨ ∃ a, l = Rega.lname f.name a) ∧
      (∀ (i j : Nat) (l : Sym), (sccChunksCode chunks)[i]? = some (T.frame.label l) →
        (sccChunksCode chunks)[j]? = some (T.frame.label l) → i = j)
  | [], _, _ => ⟨fun _ _ hi => by simp [sccChunksCode] at hi,
      fun _ _ _ hi => by simp [sccChunksCode] at hi⟩
  | c :: cs, hnd, hok => by
      dsimp only [sccChunksFns] at hnd hok
      simp only [List.map_append, List.all_append, Bool.and_eq_true] at hnd hok
      have hnd_s := List.nodup_append.mp hnd
      obtain ⟨hc_mem, hc_uniq⟩ := chunk_code_labels hcl c hnd_s.1 hok.1
      obtain ⟨ih_mem, ih_uniq⟩ := sccChunks_code_labels hcl cs hnd_s.2.1 hok.2
      have hdisj : ∀ {i₁ j₁ : Nat} {l : Sym}, c.code[i₁]? = some (T.frame.label l) →
          (sccChunksCode cs)[j₁]? = some (T.frame.label l) → False := by
        intro i₁ j₁ l hi₁ hj₁
        obtain ⟨f₁, hf₁, h₁⟩ := hc_mem i₁ l hi₁
        obtain ⟨f₂, hf₂, h₂⟩ := ih_mem j₁ l hj₁
        have hok₁ := List.all_eq_true.mp hok.1 f₁ hf₁
        have hok₂ := List.all_eq_true.mp hok.2 f₂ hf₂
        rcases h₁ with rfl | ⟨a, rfl⟩ <;> rcases h₂ with hnm | ⟨b, hnm⟩
        · exact hnd_s.2.2 f₁.name (List.mem_map_of_mem hf₁) f₂.name
            (List.mem_map_of_mem hf₂) hnm
        · exact lname_ne_cross hok₁ hnm.symm
        · exact lname_ne_cross hok₂ hnm
        · exact hnd_s.2.2 f₁.name (List.mem_map_of_mem hf₁) f₂.name
            (List.mem_map_of_mem hf₂) (lname_inj_cross hok₁ hok₂ hnm).1
      constructor
      · intro i l hi
        dsimp only [sccChunksCode, sccChunksFns] at hi ⊢
        by_cases hlt : i < c.code.length
        · rw [List.getElem?_append_left hlt] at hi
          obtain ⟨f, hf, hl⟩ := hc_mem i l hi
          exact ⟨f, List.mem_append_left _ hf, hl⟩
        · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hi
          obtain ⟨f, hf, hl⟩ := ih_mem (i - c.code.length) l hi
          exact ⟨f, List.mem_append_right _ hf, hl⟩
      · intro i j l hi hj
        dsimp only [sccChunksCode] at hi hj
        by_cases hic : i < c.code.length <;> by_cases hjc : j < c.code.length
        · rw [List.getElem?_append_left hic] at hi; rw [List.getElem?_append_left hjc] at hj
          exact hc_uniq i j l hi hj
        · rw [List.getElem?_append_left hic] at hi
          rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
          exact absurd hi (fun h' => hdisj h' hj)
        · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
          rw [List.getElem?_append_left hjc] at hj
          exact absurd hj (fun h' => hdisj h' hi)
        · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
          rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
          have heq := ih_uniq (i - c.code.length) (j - c.code.length) l hi hj
          omega

theorem sccLabelsUnique {T : Target} (L : TargetLayout T) (hcl : Rega.LabelClean T.toIsa)
    {lt : LegalTarget} {exits : List Sym} {nX : Nat} (ext₀ : List (SigEntry × Nat))
    (chunks : List (Chunk T lt exits nX))
    (h : checkLinkSccList L ext₀ chunks = true) :
    T.LabelsUnique (sccHost L ext₀ chunks h) := by
  have hp := checkLinkSccList_parts h
  have hnd_s := List.nodup_append.mp hp.2.2.2.2.1
  have hok_fns : (sccChunksFns chunks).all (fun f => fnNameOk f.name) = true := by
    simpa [List.all_map, Function.comp_def] using hp.2.2.1
  obtain ⟨hmem, huniq⟩ := sccChunks_code_labels hcl chunks hnd_s.1 hok_fns
  have hEx : ∀ (k : Nat) (l : Sym),
      (exits.map T.frame.label)[k]? = some (T.frame.label l) → exits[k]? = some l := by
    intro k l hk
    rw [List.getElem?_map] at hk
    cases hx : exits[k]? with
    | none => simp [hx] at hk
    | some e =>
        simp only [hx, Option.map_some, Option.some.injEq] at hk
        rw [hcl.label_inj e l hk]
  have hdisj : ∀ (i₁ k₂ : Nat) (l : Sym),
      (sccChunksCode chunks)[i₁]? = some (T.frame.label l) →
      (exits.map T.frame.label)[k₂]? = some (T.frame.label l) → False := by
    intro i₁ k₂ l hi₁ hk₂
    have hmemE : l ∈ exits := List.mem_of_getElem? (hEx k₂ l hk₂)
    have hlok : fnNameOk l = true := List.all_eq_true.mp hp.2.2.2.1 l hmemE
    obtain ⟨f, hf, hlf⟩ := hmem i₁ l hi₁
    rcases hlf with hl_eq | ⟨a, hl_eq⟩
    · exact hnd_s.2.2 l (hl_eq ▸ List.mem_map_of_mem hf) l hmemE rfl
    · exact lname_ne_cross hlok hl_eq.symm
  intro i j l hi hj
  rw [sccProg_host] at hi hj
  by_cases hic : i < (sccChunksCode chunks).length <;>
    by_cases hjc : j < (sccChunksCode chunks).length
  · rw [List.getElem?_append_left hic] at hi; rw [List.getElem?_append_left hjc] at hj
    exact huniq i j l hi hj
  · rw [List.getElem?_append_left hic] at hi
    rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
    exact absurd hi (fun h' => hdisj i (j - (sccChunksCode chunks).length) l h' hj)
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
    rw [List.getElem?_append_left hjc] at hj
    exact absurd hj (fun h' => hdisj j (i - (sccChunksCode chunks).length) l h' hi)
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hic)] at hi
    rw [List.getElem?_append_right (Nat.le_of_not_lt hjc)] at hj
    have heq := nodup_getElem?_inj' hnd_s.2.1 (hEx _ _ hi) (hEx _ _ hj)
    omega

/-- Look up the linked stack bound of symbol `nm` across a mixed `Chunk` list. -/
@[expose] def sccBound {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    List (Chunk T lt exits nX) → Sym → Nat
  | [], _ => 0
  | c :: cs, nm =>
      if (c.fns.map Fn.name).contains nm then c.bound nm else sccBound cs nm

theorem sccBound_le_max {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (chunks : List (Chunk T lt exits nX)) (nm : Sym),
      sccBound chunks nm ≤ sccChunksMaxBound chunks
  | [], _ => Nat.le_refl 0
  | c :: cs, nm => by
      dsimp only [sccBound, sccChunksMaxBound]
      split
      · refine Nat.le_trans ?_ (Nat.le_max_left _ _)
        cases c with
        | acyc m => exact m.compiled.bound_le_max nm
        | recSCC _ fuel _ _ _ m => exact m.boundAt_le_max (Nat.le_refl fuel)
        | recBudgetSCC _ _ _ _ _ m => exact m.bound_le_max nm
      · exact Nat.le_trans (sccBound_le_max cs nm) (Nat.le_max_right _ _)

private theorem mem_sccChunksFns_of_mem_chunk {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} {c : Chunk T lt exits nX} :
    ∀ {cs : List (Chunk T lt exits nX)}, c ∈ cs → ∀ {g : Fn}, g ∈ c.fns →
      g ∈ sccChunksFns cs
  | [], hc, _, _ => nomatch hc
  | d :: ds, hc, _, hg => by
      rcases List.mem_cons.mp hc with rfl | hds
      · exact List.mem_append_left _ hg
      · exact List.mem_append_right _ (mem_sccChunksFns_of_mem_chunk hds hg)

theorem sccBound_eq_chunk {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat} :
    ∀ (chunks : List (Chunk T lt exits nX)),
      ((sccChunksFns chunks).map Fn.name).Nodup →
      ∀ c ∈ chunks, ∀ {nm : Sym}, nm ∈ c.fns.map Fn.name →
        sccBound chunks nm = c.bound nm
  | [], _, _, hc, _, _ => nomatch hc
  | c₀ :: cs, hnd, c, hc, nm, hnm => by
      dsimp only [sccChunksFns] at hnd; simp only [List.map_append] at hnd
      have hnd_s := List.nodup_append.mp hnd
      rcases List.mem_cons.mp hc with rfl | hcs
      · have hcon : (c.fns.map Fn.name).contains nm = true := by
          simpa [List.contains_eq_mem] using hnm
        dsimp only [sccBound]; simp only [hcon, ↓reduceIte]
      · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hnm
        have hnm_cs : f.name ∈ (sccChunksFns cs).map Fn.name :=
          List.mem_map_of_mem (mem_sccChunksFns_of_mem_chunk hcs hf)
        have hnot0 : f.name ∉ c₀.fns.map Fn.name := fun h0 =>
          hnd_s.2.2 f.name h0 f.name hnm_cs rfl
        have hcon : (c₀.fns.map Fn.name).contains f.name = false := by
          simpa [List.contains_eq_mem] using hnot0
        dsimp only [sccBound]; simp only [hcon, Bool.false_eq_true, ↓reduceIte]
        exact sccBound_eq_chunk cs hnd_s.2.1 c hcs (List.mem_map_of_mem hf)

/-! ## 4. Closed Canonical `semChunks` Environment and `linkChunks_fnSpec` -/

/-- Canonical closed semantic transformer for a single chunk `c` over preceding environment `Γprev`
and earlier signatures `extSigs`. -/
@[expose] def Chunk.sem {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (extSigs : List SigEntry) : Chunk T lt exits nX → Env → Env
  | .acyc c, Γprev =>
      let M : Module := ⟨c.fs, externsOfSigs extSigs, exits⟩
      Env.sccStep M (Env.semScc M Γprev) Γprev
  | .recSCC _ fuel fs _ _ _, Γprev =>
      let M : Module := ⟨fs, externsOfSigs extSigs, exits⟩
      Env.sccStep M (DepthEnv.semScc M Γprev fuel) Γprev
  | .recBudgetSCC _ bfs _ maxB exportBounds _, Γprev =>
      let BM : BudgetModule := ⟨bfs, externsOfSigs extSigs, exits⟩
      BudgetEnv.sccStep BM (fun f as bs xs m Q X =>
        BudgetEnv.semScc BM Γprev (budgetBound exportBounds maxB f) f as bs xs m Q X) Γprev

/-- Closed canonical semantic environment for a mixed `Chunk` list, threading `extSigs` and
accumulating each chunk's `Env.semScc` (`.acyc`) or `DepthEnv.semScc ... fuel` (`.recSCC`). -/
@[expose] def semChunks {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (extSigs : List SigEntry) (Γ₀ : Env) : List (Chunk T lt exits nX) → Env
  | [] => Γ₀
  | c :: cs =>
      semChunks (c.fns.map Fn.sig ++ extSigs) (c.sem extSigs Γ₀) cs

private theorem externsOfSigs_map_sig (sigs : List SigEntry) :
    (externsOfSigs sigs).map Extern.sig = sigs := by
  induction sigs with
  | nil => rfl
  | cons s ss ih =>
      rcases s with ⟨nm, as, bs⟩
      simpa [externsOfSigs, Extern.sig] using ih

private theorem mem_unique_fst_sig : ∀ {xs : List SigEntry}, (xs.map Prod.fst).Nodup →
    ∀ {f as₁ bs₁ as₂ bs₂}, (f, as₁, bs₁) ∈ xs → (f, as₂, bs₂) ∈ xs → as₁ = as₂ ∧ bs₁ = bs₂
  | [], _, _, _, _, _, _, h, _ => nomatch h
  | (_, _, _) :: _, hnd, _, _, _, _, _, h1, h2 => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
      rcases List.mem_cons.mp h1 with e1 | h1 <;> rcases List.mem_cons.mp h2 with e2 | h2
      · cases e1; cases e2; exact ⟨rfl, rfl⟩
      · cases e1; exact absurd rfl (hnd.1 _ h2)
      · cases e2; exact absurd rfl (hnd.1 _ h1)
      · exact mem_unique_fst_sig hnd.2 h1 h2

private theorem sccChunks_fn_not_mem_rest {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} {c : Chunk T lt exits nX}
    {cs : List (Chunk T lt exits nX)} {f : Fn} (hf : f ∈ c.fns)
    (hnd : ((c.fns ++ sccChunksFns cs).map Fn.name).Nodup) :
    f.name ∉ (sccChunksFns cs).map Fn.name := by
  simp only [List.map_append] at hnd
  have hs := List.nodup_append.mp hnd
  intro hmem
  exact hs.2.2 f.name (List.mem_map_of_mem hf) f.name hmem rfl

private theorem semChunks_agree_earlier {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} :
    ∀ (cs : List (Chunk T lt exits nX)) (extSigs : List SigEntry) (Γ₀ : Env)
      {f : Fn}, f.name ∉ (sccChunksFns cs).map Fn.name → f.sig ∈ extSigs →
      ∀ xs m Q X,
        semChunks extSigs Γ₀ cs f.name f.as f.rs xs m Q X ↔
          Γ₀ f.name f.as f.rs xs m Q X := by
  intro cs
  induction cs with
  | nil => intro extSigs Γ₀ f _ _ xs m Q X; exact Iff.rfl
  | cons c cs ih =>
      intro extSigs Γ₀ f hnot hmem xs m Q X
      dsimp only [sccChunksFns] at hnot
      simp only [List.map_append, List.mem_append, not_or] at hnot
      dsimp only [semChunks]
      rw [ih (c.fns.map Fn.sig ++ extSigs) (c.sem extSigs Γ₀)
        hnot.2 (List.mem_append_right _ hmem) xs m Q X]
      have hnot_sig : f.sig ∉ c.fns.map Fn.sig := by
        intro hs
        obtain ⟨g, hg, hgeq⟩ := List.mem_map.mp hs
        have hnm : g.name = f.name := congrArg Prod.fst hgeq
        exact hnot.1 (hnm ▸ List.mem_map_of_mem hg)
      cases c with
      | acyc m' =>
          dsimp only [Chunk.sem, Env.sccStep]
          rw [externsOfSigs_map_sig]
          constructor
          · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
            · exact absurd h1 hnot_sig
            · exact h2
          · intro h0; exact Or.inr ⟨hmem, h0⟩
      | recSCC _ _ fs _ _ _ =>
          dsimp only [Chunk.sem, Env.sccStep]
          rw [externsOfSigs_map_sig]
          constructor
          · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
            · exact absurd h1 hnot_sig
            · exact h2
          · intro h0; exact Or.inr ⟨hmem, h0⟩
      | recBudgetSCC _ bfs _ _ _ _ =>
          dsimp only [Chunk.sem, BudgetEnv.sccStep, BudgetModule.fnSigs, BudgetModule.extSigs]
          rw [externsOfSigs_map_sig]
          constructor
          · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
            · have h1' : f.sig ∈ (bfs.map BudgetFn.toFn).map Fn.sig := by
                rw [List.map_map]; exact h1
              exact absurd h1' hnot_sig
            · exact h2
          · intro h0; exact Or.inr ⟨hmem, h0⟩

private theorem linkChunks_aux {T : Target} {lt : LegalTarget}
    {exits : List Sym} {nX : Nat} (h : T.mach.Host) :
    ∀ (chunks : List (Chunk T lt exits nX)) (k₀ : Nat)
      (acc : List (SigEntry × Nat)) (extSigs : List SigEntry) (Γcur : Env),
      (sccChunksCode chunks).IsInfixAt (T.mach.prog h) k₀ →
      T.LabelsUnique h →
      checkSccChunksExt acc chunks = true →
      checkChunksCalls exits extSigs chunks = true →
      ((sccChunksFns chunks).map Fn.name ++ extSigs.map Prod.fst).Nodup →
      (∀ f ∈ sccChunksFns chunks, f.Wf) →
      (∀ f ∈ sccChunksFns chunks, (f.earlyOpt).body.supportsSource lt = true) →
      (∀ p ∈ acc,
        T.FnSpec h p.1.1
          (legalEnv lt (Env.restrict Γcur extSigs) p.1.1 p.1.2.1 p.1.2.2) p.2 nX) →
      (∀ p ∈ acc, ∀ q ∈ acc, p.1.1 = q.1.1 → p.2 = q.2) →
      (∀ p ∈ acc, p.1.1 ∉ (sccChunksFns chunks).map Fn.name) →
      (∀ g ∈ exits, T.Defined h g) →
      ∀ c ∈ chunks, ∀ f ∈ c.fns,
        T.Defined h f.name ∧
          T.FnSpec h f.name
            (legalEnv lt (Env.onlyFn f (semChunks extSigs Γcur chunks)) f.name
              (lt.legalSig f.as) (lt.legalSig f.rs))
            (c.bound f.name) nX
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _ => nomatch hc
  | c :: cs, k₀, acc, extSigs, Γcur, hinf, hu, hchkExt, hcalls, hnd, hwf, hsupp,
      hacc, hacc_uniq, hacc_disj, hexits, c', hc', f, hf => by
      dsimp only [checkSccChunksExt] at hchkExt
      simp only [Bool.and_eq_true] at hchkExt
      obtain ⟨hinf_c, hinf_cs⟩ := List.IsInfixAt.append hinf
      have hnd_top : ((c.fns.map Fn.name ++ (sccChunksFns cs).map Fn.name) ++
          extSigs.map Prod.fst).Nodup := by
        simpa [sccChunksFns, List.map_append] using hnd
      have hnd_1 := List.nodup_append.mp hnd_top
      have hnd_fns := List.nodup_append.mp hnd_1.1
      have hdisj_c_ext : ∀ p ∈ acc, p.1.1 ∉ c.fns.map Fn.name := fun p hp hm => by
        refine hacc_disj p hp ?_
        dsimp only [sccChunksFns]; rw [List.map_append]; exact List.mem_append_left _ hm
      have hcompat := checkExtCompat_lookupBound hchkExt.1
      have hchunk_spec : ∀ g ∈ c.fns, T.Defined h g.name ∧
          T.FnSpec h g.name
            (legalEnv lt (Env.onlyFn g (c.sem extSigs Γcur)) g.name
              (lt.legalSig g.as) (lt.legalSig g.rs))
            (c.bound g.name) nX := by
        cases c with
        | acyc cc =>
            dsimp only [checkChunksCalls, Chunk.callsOk] at hcalls
            simp only [Bool.and_eq_true] at hcalls
            let M : Module := ⟨cc.fs, externsOfSigs extSigs, exits⟩
            let Γnext : Env := Env.sccStep M (Env.semScc M Γcur) Γcur
            have hMnd : M.namesNodup := by
              rw [Module.namesNodup, Module.names]
              have hex_map : M.externs.map Extern.name = extSigs.map Prod.fst := by
                simp [M, externsOfSigs, List.map_map, Function.comp_def]
              rw [hex_map]
              exact List.nodup_append.mpr ⟨hnd_fns.1, hnd_1.2.1,
                fun a ha b hb he => hnd_1.2.2 a (List.mem_append_left _ ha) b hb he⟩
            have hcm_acc := compileModule_mono_lookupBound hcompat cc.compiled.compileModule_eq
            have hwp_step : ∀ g ∈ M.fns, ∀ xs m Q X,
                Γnext g.name g.as g.rs xs m Q X → Func.wp Γnext g.body xs m Q X := by
              intro g hg xs m Q X hΓ
              rcases hΓ with ⟨_, hg_sem⟩ | ⟨hex_mem, _⟩
              · have hpost := Env.lfp_post (sccOp_mono M Γcur) g.name g.as g.rs xs m Q X hg_sem
                rcases hpost with ⟨_, fn, hfn, hnm, ha, hr, hwp⟩
                have hfnsNd : (M.fns.map Fn.name).Nodup := (List.nodup_append.mp hMnd).1
                obtain rfl := fn_eq_of_mem_fns hfnsNd hfn hg hnm
                exact hwp
              · exact absurd hex_mem (fn_name_not_mem_externs' hMnd hg)
            have hext_M : ∀ p ∈ acc,
                T.FnSpec h p.1.1
                  (legalEnv lt (Env.ofModule M Γnext) p.1.1 p.1.2.1 p.1.2.2) p.2 nX := by
              intro p hp
              refine Target.FnSpec.of_spec T (hacc p hp) fun args m0 Q X hleg => ?_
              rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hsig, hΓ⟩
              have hnot_fn : p.1.1 ∉ M.fns.map Fn.name := hdisj_c_ext p hp
              have hnot_fnsig : (p.1.1, as₀, bs₀) ∉ M.fns.map Fn.sig := by
                intro hm
                obtain ⟨fn, hfn, heq⟩ := List.mem_map.mp hm
                exact hnot_fn ((congrArg Prod.fst heq) ▸ List.mem_map_of_mem hfn)
              rcases List.mem_append.mp hsig with hm_fn | hm_ex
              · exact absurd hm_fn hnot_fnsig
              · rw [externsOfSigs_map_sig] at hm_ex
                rcases hΓ with ⟨_, _⟩ | ⟨_, hΓcur⟩
                · exact absurd (by assumption) hnot_fnsig
                · exact ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hm_ex, hΓcur⟩
            have hsound := compile_sound T h lt M Γnext acc exits nX cc.hints cc.compiled.code
              cc.compiled.bounds k₀ hcm_acc hinf_c hu hcalls.1
              (fun g hg => hwf g (List.mem_append_left _ hg))
              (fun g hg => hsupp g (List.mem_append_left _ hg))
              hwp_step hext_M ⟨hacc_uniq, hdisj_c_ext⟩ hexits
            intro g hg
            have hmemB := cc.compiled.bound_mem (List.mem_map_of_mem hg)
            obtain ⟨g', hg', hnm, hdef, hspec⟩ := hsound (g.name, cc.compiled.bound g.name) hmemB
            obtain rfl := fn_eq_of_mem_fns hnd_fns.1 hg hg' hnm
            refine ⟨hdef, Target.FnSpec.of_spec T hspec fun args m0 Q X hleg => ?_⟩
            rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀,
              _, ha, hb, hΓn⟩
            subst ha; subst hb
            exact ⟨g.as, g.rs, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀,
              List.mem_append_left _ (List.mem_map_of_mem hg), hΓn⟩
        | recSCC ext fuel fs hints maxB cr =>
            dsimp only [checkChunksCalls, Chunk.callsOk] at hcalls
            simp only [Bool.and_eq_true] at hcalls
            let M : Module := ⟨fs, externsOfSigs extSigs, exits⟩
            have hcm_acc := compileModuleRec_mono_lookupBound hcompat hdisj_c_ext
              cr.compileModuleRec_eq
            let M_acc : CompiledRec T lt acc exits nX fuel fs hints maxB :=
              { cr with compileModuleRec_eq := hcm_acc }
            have hext_M : ∀ p ∈ acc,
                T.FnSpec h p.1.1
                  (legalEnv lt (Env.restrict Γcur (M.externs.map Extern.sig))
                    p.1.1 p.1.2.1 p.1.2.2)
                  p.2 nX := by
              intro p hp
              rw [externsOfSigs_map_sig]
              exact hacc p hp
            have hres := link_scc_depth_lfp M_acc M rfl h Γcur k₀ hinf_c hu hcalls.1
              (fun g hg => hwf g (List.mem_append_left _ hg))
              (fun g hg => hsupp g (List.mem_append_left _ hg))
              hext_M hacc_uniq hexits fuel (Nat.le_refl fuel)
            intro g hg
            obtain ⟨hdef, hspec⟩ := hres g hg
            refine ⟨hdef, Target.FnSpec.of_spec T hspec fun args m0 Q X hleg => ?_⟩
            rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀,
              _, ha, hb, hstep⟩
            subst ha; subst hb
            have hMnd : M.namesNodup :=
              Module.namesNodup_of_checkNamesNodup ((Bool.and_eq_true _ _).mp hcalls.1).1
            rcases hstep with ⟨_, hsem⟩ | ⟨hmemE, _⟩
            · exact ⟨g.as, g.rs, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, rfl, rfl, rfl, hsem⟩
            · exact absurd hmemE (fn_name_not_mem_externs' hMnd hg)
        | recBudgetSCC ext bfs hints maxB expB cbr =>
            dsimp only [checkChunksCalls, Chunk.callsOk] at hcalls
            simp only [Bool.and_eq_true] at hcalls
            let BM : BudgetModule := ⟨bfs, externsOfSigs extSigs, exits⟩
            have hdisj_b : ∀ p ∈ acc, p.1.1 ∉ bfs.map (fun b => b.toFn.name) := by
              intro p hp hm
              refine hdisj_c_ext p hp ?_
              dsimp only [Chunk.fns]
              rwa [List.map_map]
            have hcm_acc := compileModuleBudgetRec_mono_lookupBound hcompat hdisj_b
              cbr.compileModuleBudgetRec_eq
            let M_acc : CompiledBudgetRec T lt acc exits nX bfs hints maxB expB :=
              { cbr with compileModuleBudgetRec_eq := hcm_acc }
            have hext_M : ∀ p ∈ acc,
                T.FnSpec h p.1.1
                  (legalEnv lt (Env.restrict Γcur BM.extSigs) p.1.1 p.1.2.1 p.1.2.2) p.2 nX := by
              intro p hp
              dsimp only [BM, BudgetModule.extSigs]
              rw [externsOfSigs_map_sig]
              exact hacc p hp
            have hres := link_scc_budget_lfp M_acc BM rfl h Γcur k₀ hinf_c hu hcalls.1
              (fun b hb => hwf b.toFn (List.mem_append_left _ (List.mem_map_of_mem hb)))
              (fun b hb => hsupp b.toFn (List.mem_append_left _ (List.mem_map_of_mem hb)))
              hext_M hacc_uniq hexits
            intro g hg
            obtain ⟨bg, hbg, rfl⟩ := List.mem_map.mp hg
            have hsb_ra : cbr.bound bg.toFn.name + T.frame.raBytes ≤ 2 ^ 64 :=
              cbr.bound_ra_le bg.toFn.name
            obtain ⟨hdef, hspec⟩ := hres (cbr.bound bg.toFn.name) hsb_ra bg hbg
            refine ⟨hdef, Target.FnSpec.of_spec T hspec fun args m0 Q X hleg => ?_⟩
            rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀,
              _, ha, hb, hstep⟩
            subst ha; subst hb
            have hMnd : BM.toModule.namesNodup :=
              Module.namesNodup_of_checkNamesNodup ((Bool.and_eq_true _ _).mp hcalls.1).1
            rcases hstep with ⟨_, hsem⟩ | ⟨hmemE, _⟩
            · exact ⟨bg.toFn.as, bg.toFn.rs, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀,
                rfl, rfl, rfl, hsem⟩
            · exact absurd hmemE (bfn_name_not_mem_externs hMnd hbg)
      rcases List.mem_cons.mp hc' with rfl | hcs
      · refine ⟨(hchunk_spec f hf).1, Target.FnSpec.of_spec T (hchunk_spec f hf).2 ?_⟩
        intro args m0 Q X hleg
        rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀,
          _, ha, hb, hsem⟩
        subst ha; subst hb
        have hnot_rest := sccChunks_fn_not_mem_rest hf
          (by simpa only [List.map_append] using hnd_1.1)
        have hsig_in : f.sig ∈ c'.fns.map Fn.sig ++ extSigs :=
          List.mem_append_left _ (List.mem_map_of_mem hf)
        have hagree := (semChunks_agree_earlier cs (c'.fns.map Fn.sig ++ extSigs)
          (c'.sem extSigs Γcur) hnot_rest hsig_in xs₀ m0 P₀ E₀).mp hsem
        exact ⟨f.as, f.rs, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, rfl, rfl, rfl, hagree⟩
      · have hcalls_cs : checkChunksCalls exits (c.fns.map Fn.sig ++ extSigs) cs = true :=
          (Bool.and_eq_true _ _).mp hcalls |>.2
        have hnd_cs : ((sccChunksFns cs).map Fn.name ++
            (c.fns.map Fn.sig ++ extSigs).map Prod.fst).Nodup := by
          have hex_eq : (c.fns.map Fn.sig ++ extSigs).map Prod.fst =
              c.fns.map Fn.name ++ extSigs.map Prod.fst := by
            simp [List.map_append, List.map_map, Function.comp_def, Fn.sig]
          rw [hex_eq]
          refine List.nodup_append.mpr ⟨hnd_fns.2.1,
            List.nodup_append.mpr ⟨hnd_fns.1, (List.nodup_append.mp hnd).2.1,
              fun a ha b hb he => hnd_1.2.2 a (List.mem_append_left _ ha) b hb he⟩,
            fun a ha b hb he => ?_⟩
          rcases List.mem_append.mp hb with hbc | hbe
          · exact hnd_fns.2.2 b hbc a ha he.symm
          · exact hnd_1.2.2 a (List.mem_append_right _ ha) b hbe he
        have hsigB_names : ∀ p ∈ c.sigBounds, ∃ g ∈ c.fns,
            p = ((g.name, lt.legalSig g.as, lt.legalSig g.rs), c.bound g.name) := by
          intro p hp
          cases c with
          | acyc cc =>
              simp only [Chunk.sigBounds, Compiled.sigBounds, List.mem_map] at hp
              obtain ⟨g, hg, rfl⟩ := hp
              exact ⟨g, hg, rfl⟩
          | recSCC _ fuel _ _ _ cr =>
              simp only [Chunk.sigBounds, CompiledRec.sigBounds, List.mem_map] at hp
              obtain ⟨g, hg, rfl⟩ := hp
              exact ⟨g, hg, rfl⟩
          | recBudgetSCC _ _ _ _ _ cbr =>
              simp only [Chunk.sigBounds, CompiledBudgetRec.sigBounds,
                sigBoundsBudgetRecOf, List.mem_map] at hp
              obtain ⟨b, hb, rfl⟩ := hp
              exact ⟨b.toFn, List.mem_map_of_mem hb, rfl⟩
        have hacc' : ∀ p ∈ c.sigBounds ++ acc,
            T.FnSpec h p.1.1
              (legalEnv lt (Env.restrict (c.sem extSigs Γcur) (c.fns.map Fn.sig ++ extSigs))
                p.1.1 p.1.2.1 p.1.2.2) p.2 nX := by
          intro p hp
          rcases List.mem_append.mp hp with hp_c | hp_acc
          · obtain ⟨g, hg, rfl⟩ := hsigB_names p hp_c
            refine Target.FnSpec.of_spec T (hchunk_spec g hg).2 fun args m0 Q X hleg => ?_
            rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hmemS, hΓ⟩
            have hmapFst : (c.fns.map Fn.sig ++ extSigs).map Prod.fst =
                c.fns.map Fn.name ++ extSigs.map Prod.fst := by
              simp [List.map_append, List.map_map, Function.comp_def, Fn.sig]
            have hndS : ((c.fns.map Fn.sig ++ extSigs).map Prod.fst).Nodup := by
              rw [hmapFst]
              exact List.nodup_append.mpr ⟨hnd_fns.1, (List.nodup_append.mp hnd).2.1,
                fun a ha b hb he => hnd_1.2.2 a (List.mem_append_left _ ha) b hb he⟩
            obtain ⟨rfl, rfl⟩ := mem_unique_fst_sig hndS hmemS
              (List.mem_append_left _ (List.mem_map_of_mem hg))
            exact ⟨g.as, g.rs, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, rfl, rfl, rfl, hΓ⟩
          · refine Target.FnSpec.of_spec T (hacc p hp_acc) fun args m0 Q X hleg => ?_
            rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hmemS, hΓ⟩
            have hnot_fn := hdisj_c_ext p hp_acc
            have hnot_sig : (p.1.1, as₀, bs₀) ∉ c.fns.map Fn.sig := by
              intro hm
              obtain ⟨fn, hfn, heq⟩ := List.mem_map.mp hm
              exact hnot_fn ((congrArg Prod.fst heq) ▸ List.mem_map_of_mem hfn)
            rcases List.mem_append.mp hmemS with hm_c | hm_e
            · exact absurd hm_c hnot_sig
            · have hΓ0 : Γcur p.1.1 as₀ bs₀ xs₀ m0 P₀ E₀ := by
                cases c with
                | acyc cc =>
                    dsimp only [Chunk.sem, Env.sccStep] at hΓ
                    rw [externsOfSigs_map_sig] at hΓ
                    rcases hΓ with ⟨h1, _⟩ | ⟨_, h2⟩
                    · exact absurd h1 hnot_sig
                    · exact h2
                | recSCC _ _ fs _ _ _ =>
                    dsimp only [Chunk.sem, Env.sccStep] at hΓ
                    rw [externsOfSigs_map_sig] at hΓ
                    rcases hΓ with ⟨h1, _⟩ | ⟨_, h2⟩
                    · exact absurd h1 hnot_sig
                    · exact h2
                | recBudgetSCC _ bfs _ _ _ _ =>
                    dsimp only [Chunk.sem, BudgetEnv.sccStep, BudgetModule.fnSigs,
                      BudgetModule.extSigs] at hΓ
                    rw [externsOfSigs_map_sig] at hΓ
                    rcases hΓ with ⟨h1, _⟩ | ⟨_, h2⟩
                    · have h1' : (p.1.1, as₀, bs₀) ∈ (bfs.map BudgetFn.toFn).map Fn.sig := by
                        rw [List.map_map]; exact h1
                      exact absurd h1' hnot_sig
                    · exact h2
              exact ⟨as₀, bs₀, has₀, hbs₀, xs₀, P₀, E₀, hxs₀, hQ₀, hX₀, hm_e, hΓ0⟩
        have hacc_uniq' : ∀ p ∈ c.sigBounds ++ acc, ∀ q ∈ c.sigBounds ++ acc,
            p.1.1 = q.1.1 → p.2 = q.2 := by
          intro p hp q hq hnm
          rcases List.mem_append.mp hp with hp_c | hp_acc <;>
            rcases List.mem_append.mp hq with hq_c | hq_acc
          · obtain ⟨g₁, hg₁, rfl⟩ := hsigB_names p hp_c
            obtain ⟨g₂, hg₂, rfl⟩ := hsigB_names q hq_c
            obtain rfl := fn_eq_of_mem_fns hnd_fns.1 hg₁ hg₂ hnm
            rfl
          · obtain ⟨g₁, hg₁, rfl⟩ := hsigB_names p hp_c
            exact absurd (hnm ▸ List.mem_map_of_mem hg₁) (hdisj_c_ext q hq_acc)
          · obtain ⟨g₂, hg₂, rfl⟩ := hsigB_names q hq_c
            exact absurd (hnm.symm ▸ List.mem_map_of_mem hg₂) (hdisj_c_ext p hp_acc)
          · exact hacc_uniq p hp_acc q hq_acc hnm
        have hacc_disj' : ∀ p ∈ c.sigBounds ++ acc, p.1.1 ∉ (sccChunksFns cs).map Fn.name := by
          intro p hp hm
          rcases List.mem_append.mp hp with hp_c | hp_acc
          · obtain ⟨g, hg, rfl⟩ := hsigB_names p hp_c
            exact hnd_fns.2.2 g.name (List.mem_map_of_mem hg) g.name hm rfl
          · refine hacc_disj p hp_acc ?_
            dsimp only [sccChunksFns]; rw [List.map_append]; exact List.mem_append_right _ hm
        exact linkChunks_aux h cs (k₀ + c.code.length) (c.sigBounds ++ acc)
          (c.fns.map Fn.sig ++ extSigs) (c.sem extSigs Γcur) hinf_cs hu hchkExt.2 hcalls_cs
          hnd_cs (fun g hg => hwf g (List.mem_append_right _ hg))
          (fun g hg => hsupp g (List.mem_append_right _ hg))
          hacc' hacc_uniq' hacc_disj' hexits c' hcs f hf

/-- **Closed whole-module linking theorem over mixed `.acyc` + `.recSCC` chunks:**
proves `T.Defined` and `T.FnSpec` against the canonical closed `semChunks extSigs Γ₀ chunks`
environment for every function `f ∈ c.fns` across every chunk `c ∈ chunks`. -/
theorem linkChunks_fnSpec {T : Target} {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (h : T.mach.Host) (ext₀ : List (SigEntry × Nat)) (extSigs : List SigEntry) (Γ₀ : Env)
    (chunks : List (Chunk T lt exits nX)) (k₀ : Nat)
    (hc : (sccChunksCode chunks).IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hchkExt : checkSccChunksExt ext₀ chunks = true)
    (hcalls : checkChunksCalls exits extSigs chunks = true)
    (hnd : ((sccChunksFns chunks).map Fn.name ++ extSigs.map Prod.fst).Nodup)
    (hwf : ∀ f ∈ sccChunksFns chunks, f.Wf)
    (hsupp : ∀ f ∈ sccChunksFns chunks, (f.earlyOpt).body.supportsSource lt = true)
    (hext : ∀ p ∈ ext₀,
      T.FnSpec h p.1.1 (legalEnv lt (Env.restrict Γ₀ extSigs) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : ∀ p ∈ ext₀, ∀ q ∈ ext₀, p.1.1 = q.1.1 → p.2 = q.2)
    (hext_disj : ∀ p ∈ ext₀, p.1.1 ∉ (sccChunksFns chunks).map Fn.name)
    (hexits : ∀ g ∈ exits, T.Defined h g) :
    ∀ c ∈ chunks, ∀ f ∈ c.fns,
      T.Defined h f.name ∧
        T.FnSpec h f.name
          (legalEnv lt (Env.onlyFn f (semChunks extSigs Γ₀ chunks)) f.name
            (lt.legalSig f.as) (lt.legalSig f.rs))
          (c.bound f.name) nX :=
  linkChunks_aux h chunks k₀ ext₀ extSigs Γ₀ hc hu hchkExt hcalls hnd hwf hsupp
    hext hext_uniq hext_disj hexits

/-- Linked-host specialization using `sccHost` and `sccBound`. -/
theorem linkChunks_fnSpec_linked {T : Target} (L : TargetLayout T)
    (hcl : Rega.LabelClean T.toIsa) {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (ext₀ : List (SigEntry × Nat)) (extSigs : List SigEntry) (Γ₀ : Env)
    (chunks : List (Chunk T lt exits nX))
    (hchk : checkLinkSccList L ext₀ chunks = true)
    (hcalls : checkChunksCalls exits extSigs chunks = true)
    (hnd_ext : (extSigs.map Prod.fst).Nodup)
    (hdisj_ext : ∀ nm ∈ (sccChunksFns chunks).map Fn.name, nm ∉ extSigs.map Prod.fst)
    (hwf : ∀ f ∈ sccChunksFns chunks, f.Wf)
    (hsupp : ∀ f ∈ sccChunksFns chunks, (f.earlyOpt).body.supportsSource lt = true)
    (hext : ∀ p ∈ ext₀,
      T.FnSpec (sccHost L ext₀ chunks hchk) p.1.1
        (legalEnv lt (Env.restrict Γ₀ extSigs) p.1.1 p.1.2.1 p.1.2.2) p.2 nX)
    (hext_uniq : ∀ p ∈ ext₀, ∀ q ∈ ext₀, p.1.1 = q.1.1 → p.2 = q.2) :
    ∀ c ∈ chunks, ∀ f ∈ c.fns,
      T.Defined (sccHost L ext₀ chunks hchk) f.name ∧
        T.FnSpec (sccHost L ext₀ chunks hchk) f.name
          (legalEnv lt (Env.onlyFn f (semChunks extSigs Γ₀ chunks)) f.name
            (lt.legalSig f.as) (lt.legalSig f.rs))
          (sccBound chunks f.name) nX := by
  have hp := checkLinkSccList_parts hchk
  have hnd_fns := (List.nodup_append.mp hp.2.2.2.2.1).1
  have hnd : ((sccChunksFns chunks).map Fn.name ++ extSigs.map Prod.fst).Nodup :=
    List.nodup_append.mpr ⟨hnd_fns, hnd_ext, fun a ha b hb he => hdisj_ext a ha (he ▸ hb)⟩
  intro c hc f hf
  have hres := linkChunks_fnSpec (sccHost L ext₀ chunks hchk) ext₀ extSigs Γ₀ chunks 0
    (sccCode_infix_host L ext₀ chunks hchk) (sccLabelsUnique L hcl ext₀ chunks hchk)
    hp.1 hcalls hnd hwf hsupp hext hext_uniq hp.2.1
    (fun _ hg => sccDefined_exit_host L ext₀ chunks hchk hg) c hc f hf
  rw [sccBound_eq_chunk chunks hnd_fns c hc (List.mem_map_of_mem hf)]
  exact hres

/-- Self-contained (`ext₀ = []`, `extSigs = []`) linked-host specialization of
`linkChunks_fnSpec`. -/
theorem linkChunks_fnSpec_host {T : Target} (L : TargetLayout T)
    (hcl : Rega.LabelClean T.toIsa) {lt : LegalTarget} {exits : List Sym} {nX : Nat}
    (chunks : List (Chunk T lt exits nX))
    (hchk : checkLinkSccList L [] chunks = true)
    (hcalls : checkChunksCalls exits [] chunks = true)
    (hwf : ∀ f ∈ sccChunksFns chunks, f.Wf)
    (hsupp : ∀ f ∈ sccChunksFns chunks, (f.earlyOpt).body.supportsSource lt = true) :
    ∀ c ∈ chunks, ∀ f ∈ c.fns,
      T.Defined (sccHost L [] chunks hchk) f.name ∧
        T.FnSpec (sccHost L [] chunks hchk) f.name
          (legalEnv lt (Env.onlyFn f (semChunks [] (fun _ _ _ _ _ _ _ => False) chunks))
            f.name (lt.legalSig f.as) (lt.legalSig f.rs))
          (sccBound chunks f.name) nX :=
  linkChunks_fnSpec_linked L hcl [] [] (fun _ _ _ _ _ _ _ => False) chunks hchk hcalls
    List.nodup_nil (fun _ _ hm => nomatch hm) hwf hsupp
    (fun _ h => nomatch h) (fun _ h => nomatch h)

end LeanQbe.T
