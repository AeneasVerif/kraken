module

public import LeanQbe.T.Xcap.Link
public import LeanQbe.T.Target
public import LeanQbe.T.Main
public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Logic.C0Step
import LeanQbe.T.MainCertProof
import LeanQbe.T.AbiLemmas

/-!
# Generic `Target.FnSpec` ↔ `Xcap.cptr` Bridge (`Xcap.Bridge`)

100% target-generic bidirectional seam between LeanQbe's `Target.FnSpec` machine-code contracts
and `Xcap.cptr` impredicative code-pointer specifications (zero `Kraken.X64`, `Kraken.AArch64`,
`Amd64`, or `Arm64` imports; works uniformly for SysV x86-64 stack return addresses and AAPCS64
link-register return addresses):

* `AddrCodec`, `TargetSafe`, `TargetClosed`, `targetCallPre`, `targetIfaceEntry`.
* **Seam 1 (`Target.FnSpec` → `Xcap.cptr`):** `fnSpec_to_cptr` and `fnSpec_to_targetSafe_cptr`.
* **Seam 2 (`Xcap.cptr` → `Target.FnSpec`):** `cptr_to_Γ`, `cptr_of_targetClosed_to_Γ`, and exact
  bi-directional equivalences `fnSpec_iff_forall_targetSafe_cptr` /
  `fnSpec_iff_forall_targetClosed_cptr`.
* **External-callee & `Env.ofTable` / `ModuleOk` / `Compiled` / `LinkedCert` adapters:**
  `extCalleesOfTable`, `cptr_table_to_extCallees`, `cptr_specTable_to_extCallees`,
  `compiled_fnSpec_of_cptr_ext`, `compiled_to_cptr`, `compiled_ofTable_fnSpec_src`,
  `compiled_ofTable_cptr_src`, `linkedCert_fnSpec_of_cptr_ext`, `linkedCert_to_cptr`,
  `linkedCert_host_to_cptr_src`, `linkedCert_ofTable_fnSpec_src`, and
  `linkedCert_ofTable_cptr_src`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Xcap

open Std Std.ExtHashMap
open LeanQbe.T

/-! ## 1. `AddrCodec`, `TargetSafe`, `TargetClosed`, and `targetCallPre` -/

/-- Injective encoding between `T.mach.Addr` and `BitVec 64`
(after U2, canonically `⟨T.mach.addrBits, T.mach.ofBits, T.mach.ofBits_addrBits⟩`). -/
structure AddrCodec (T : Target) where
  toBits : T.mach.Addr → BitVec 64
  ofBits : BitVec 64 → T.mach.Addr
  of_to : ∀ a, ofBits (toBits a) = a

theorem AddrCodec.toBits_inj {T : Target} (C : AddrCodec T) {a b : T.mach.Addr}
    (h : C.toBits a = C.toBits b) : a = b := by
  rw [← C.of_to a, ← C.of_to b, h]

theorem AddrCodec.mkState_ofBits_toBits {T : Target} (C : AddrCodec T)
    (s : T.mach.MData) (a : T.mach.Addr) :
    T.mach.mkState s (C.ofBits (C.toBits a)) = T.mach.mkState s a := by
  rw [C.of_to]

/-- Target machine safety predicate lifted to `Xcap.CodeSpec T.mach.MData`:
executing `T.mach.step host` from `(s, C.ofBits pc)` eventually satisfies `H`. -/
@[expose] def TargetSafe (T : Target) (C : AddrCodec T) (host : T.mach.Host)
    (H : T.mach.State → Prop) : CodeSpec T.mach.MData :=
  fun pc s => Eventually (T.mach.step host) H (T.mach.mkState s (C.ofBits pc))

theorem TargetSafe.done {T : Target} {C : AddrCodec T} {host : T.mach.Host}
    {H : T.mach.State → Prop} {pc : BitVec 64} {s : T.mach.MData}
    (h : H (T.mach.mkState s (C.ofBits pc))) : TargetSafe T C host H pc s :=
  Eventually.done _ h

theorem TargetSafe.done_toBits {T : Target} {C : AddrCodec T} {host : T.mach.Host}
    {H : T.mach.State → Prop} {a : T.mach.Addr} {s : T.mach.MData}
    (h : H (T.mach.mkState s a)) : TargetSafe T C host H (C.toBits a) s := by
  dsimp only [TargetSafe]
  rw [C.of_to]
  exact Eventually.done _ h

theorem TargetSafe.weaken {T : Target} {C : AddrCodec T} {host : T.mach.Host}
    {H₁ H₂ : T.mach.State → Prop} (h : ∀ st, H₁ st → H₂ st) {pc : BitVec 64} {s : T.mach.MData}
    (hs : TargetSafe T C host H₁ pc s) : TargetSafe T C host H₂ pc s :=
  eventually_weaken _ _ _ _ h hs

theorem TargetSafe.bind {T : Target} {C : AddrCodec T} {host : T.mach.Host}
    {H : T.mach.State → Prop} {st₀ : T.mach.State}
    (h : Eventually (T.mach.step host)
      (fun st => TargetSafe T C host H (C.toBits (T.mach.pc st)) (T.mach.data st)) st₀) :
    Eventually (T.mach.step host) H st₀ :=
  eventually_trans (T.mach.step host) _ H st₀ h fun st hst => by
    dsimp only [TargetSafe] at hst
    rw [C.of_to, T.mach.mk_eta] at hst
    exact hst

/-- Step-closure of a `CodeSpec` under `Eventually (T.mach.step host)` (the concrete machine
analogue of `Xcap.Closed`; canonically inhabited by `TargetSafe T C host H`). -/
@[expose] def TargetClosed (T : Target) (C : AddrCodec T) (host : T.mach.Host)
    (Ψ : CodeSpec T.mach.MData) (H : T.mach.State → Prop) : Prop :=
  ∀ pc s, Eventually (T.mach.step host)
      (fun st => Ψ (C.toBits (T.mach.pc st)) (T.mach.data st) ∨ H st)
      (T.mach.mkState s (C.ofBits pc)) →
    Ψ pc s

/-- `TargetSafe T C host H` is canonically `TargetClosed` for `H`. -/
theorem TargetSafe.closed (T : Target) (C : AddrCodec T) (host : T.mach.Host)
    (H : T.mach.State → Prop) :
    TargetClosed T C host (TargetSafe T C host H) H := by
  intro pc s hev
  refine eventually_trans (T.mach.step host) _ H _ hev ?_
  rintro st (hsafe | hH)
  · dsimp only [TargetSafe] at hsafe
    rw [C.of_to, T.mach.mk_eta] at hsafe
    exact hsafe
  · exact .done st hH

theorem TargetClosed.of_eventually {T : Target} {C : AddrCodec T} {host : T.mach.Host}
    {Ψ : CodeSpec T.mach.MData} {H : T.mach.State → Prop}
    (hcl : TargetClosed T C host Ψ H) {pc : BitVec 64} {s : T.mach.MData}
    (hev : Eventually (T.mach.step host)
      (fun st => Ψ (C.toBits (T.mach.pc st)) (T.mach.data st))
      (T.mach.mkState s (C.ofBits pc))) :
    Ψ pc s :=
  hcl pc s (eventually_weaken _ _ _ _ (fun _ h => Or.inl h) hev)

theorem TargetClosed.of_H {T : Target} {C : AddrCodec T} {host : T.mach.Host}
    {Ψ : CodeSpec T.mach.MData} {H : T.mach.State → Prop}
    (hcl : TargetClosed T C host Ψ H) {pc : BitVec 64} {s : T.mach.MData}
    (h : H (T.mach.mkState s (C.ofBits pc))) : Ψ pc s :=
  hcl pc s (.done _ (Or.inr h))

theorem TargetClosed.weaken_H {T : Target} {C : AddrCodec T} {host : T.mach.Host}
    {Ψ : CodeSpec T.mach.MData} {H₁ H₂ : T.mach.State → Prop}
    (hcl : TargetClosed T C host Ψ H₂) (h : ∀ st, H₁ st → H₂ st) :
    TargetClosed T C host Ψ H₁ :=
  fun pc s hev => hcl pc s (eventually_weaken _ _ _ _ (fun st => Or.imp_right (h st)) hev)

/-- Knaster–Tarski characterization: `TargetSafe` is the least `TargetClosed` code spec. -/
theorem targetSafe_iff_forall_closed (T : Target) (C : AddrCodec T) (host : T.mach.Host)
    (H : T.mach.State → Prop) (pc : BitVec 64) (s : T.mach.MData) :
    TargetSafe T C host H pc s ↔ ∀ Ψ, TargetClosed T C host Ψ H → Ψ pc s :=
  ⟨fun hs _ hcl => hcl pc s (eventually_weaken _ _ _ _ (fun _ h => Or.inr h) hs),
   fun hall => hall _ (TargetSafe.closed T C host H)⟩

/-- Generic XCAP call precondition matching `Target.FnSpec` (`callPre` generalized to
stack-frame `T.Entry` + callee-saved `T.Restored` + abnormal exit `X` continuations). -/
@[expose] def targetCallPre (T : Target) (C : AddrCodec T) (host : T.mach.Host)
    {as bs : List Ty} (spec : Spec as bs) (n nX : Nat) :
    CodeSpec T.mach.MData → T.mach.MData → Prop :=
  fun Ψ s =>
    ∃ (args : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost)
      (ra : T.mach.Addr) (R : Mem 64 → Prop),
      spec args m Q X ∧
      T.ArgsIn args s ∧ T.frameSpec.raReg s ra ∧
      T.frameSpec.spEntry (T.mach.getGpr s T.frame.sp) ∧
      (T.mach.mem s =⋆ Eq m ⋆ T.Entry (T.mach.getGpr s T.frame.sp) ra n ⋆ R) ∧
      cptr Ψ (C.toBits ra) (fun s' =>
        ∃ rets m', Q rets m' ∧ T.RetsIn rets s' ∧ T.Restored s s' ∧
          (T.mach.mem s' =⋆ Eq m' ⋆ T.Exit (T.mach.getGpr s T.frame.sp) n ⋆ R)) ∧
      (∀ sym' cs xs m', X sym' cs xs m' →
        cptr Ψ (C.toBits (T.mach.labelAddr host sym')) (fun s' =>
          T.Defined host sym' ∧ T.ArgsIn xs s' ∧
          T.frameSpec.spEntry (T.mach.getGpr s' T.frame.sp) ∧
          ∃ ra' n' F, nX ≤ n' ∧ n' + T.frame.raBytes ≤ 2 ^ 64 ∧
            T.frameSpec.raReg s' ra' ∧
            (T.mach.mem s' =⋆ Eq m' ⋆ T.Entry (T.mach.getGpr s' T.frame.sp) ra' n' ⋆ F ⋆ R)))

/-- Single `Xcap.Iface` entry corresponding to a target function symbol `sym`. -/
@[expose] def targetIfaceEntry (T : Target) (C : AddrCodec T) (host : T.mach.Host) (sym : Sym)
    {as bs : List Ty} (spec : Spec as bs) (n nX : Nat) :
    BitVec 64 × (CodeSpec T.mach.MData → T.mach.MData → Prop) :=
  (C.toBits (T.mach.labelAddr host sym), targetCallPre T C host spec n nX)

theorem cptr_weaken {σ : Type _} {Ψ : CodeSpec σ} {p : BitVec 64} {P Q : σ → Prop}
    (hc : cptr Ψ p P) (h : ∀ s, Q s → P s) : cptr Ψ p Q :=
  fun s hs => hc s (h s hs)

theorem targetCallPre_mono_Ψ {T : Target} {C : AddrCodec T} {host : T.mach.Host}
    {as bs : List Ty} {spec : Spec as bs} {n nX : Nat} {Ψ₁ Ψ₂ : CodeSpec T.mach.MData}
    (hΨ : ∀ pc s, Ψ₁ pc s → Ψ₂ pc s) {s : T.mach.MData}
    (h : targetCallPre T C host spec n nX Ψ₁ s) :
    targetCallPre T C host spec n nX Ψ₂ s := by
  rcases h with ⟨args, m, Q, X, ra, R, hspec, hargs, hra, hspE, hmem, hret, hexit⟩
  exact ⟨args, m, Q, X, ra, R, hspec, hargs, hra, hspE, hmem,
    fun s' hs' => hΨ _ s' (hret s' hs'),
    fun sym' cs xs m' hX s' hs' => hΨ _ s' (hexit sym' cs xs m' hX s' hs')⟩

theorem targetCallPre_mono_spec {T : Target} {C : AddrCodec T} {host : T.mach.Host}
    {as bs : List Ty} {spec₁ spec₂ : Spec as bs} {n nX : Nat}
    (him : ∀ args m Q X, spec₁ args m Q X → spec₂ args m Q X)
    {Ψ : CodeSpec T.mach.MData} {s : T.mach.MData}
    (h : targetCallPre T C host spec₁ n nX Ψ s) :
    targetCallPre T C host spec₂ n nX Ψ s := by
  rcases h with ⟨args, m, Q, X, ra, R, hspec, hargs, hra, hspE, hmem, hret, hexit⟩
  exact ⟨args, m, Q, X, ra, R, him args m Q X hspec, hargs, hra, hspE, hmem, hret, hexit⟩

/-- Build a `targetCallPre` witness for a non-exiting call (`X := fun _ _ _ _ => False`). -/
theorem targetCallPre_of_noExit {T : Target} {C : AddrCodec T} {host : T.mach.Host}
    {as bs : List Ty} {spec : Spec as bs} {n nX : Nat} {Ψ : CodeSpec T.mach.MData}
    {s : T.mach.MData} (args : Tup Val as) (m : Mem 64) (Q : Post bs)
    (ra : T.mach.Addr) (R : Mem 64 → Prop)
    (hspec : spec args m Q (fun _ _ _ _ => False))
    (hargs : T.ArgsIn args s) (hra : T.frameSpec.raReg s ra)
    (hspE : T.frameSpec.spEntry (T.mach.getGpr s T.frame.sp))
    (hmem : T.mach.mem s =⋆ Eq m ⋆ T.Entry (T.mach.getGpr s T.frame.sp) ra n ⋆ R)
    (hret : cptr Ψ (C.toBits ra) (fun s' =>
      ∃ rets m', Q rets m' ∧ T.RetsIn rets s' ∧ T.Restored s s' ∧
        (T.mach.mem s' =⋆ Eq m' ⋆ T.Exit (T.mach.getGpr s T.frame.sp) n ⋆ R))) :
    targetCallPre T C host spec n nX Ψ s :=
  ⟨args, m, Q, (fun _ _ _ _ => False), ra, R, hspec, hargs, hra, hspE, hmem, hret,
    fun _ _ _ _ hX => hX.elim⟩

/-! ## 2. Seam 1 (`fnSpec_to_cptr`) & Seam 2 (`cptr_to_Γ`) -/

/-- Seam 1 (Tier S → XCAP): ANY certified `Target.FnSpec` becomes a standard XCAP `cptr` entry
for every `TargetClosed` machine spec `Ψ` (in particular `TargetSafe T C host H`). -/
theorem fnSpec_to_cptr {T : Target} (C : AddrCodec T) {host : T.mach.Host} {sym : Sym}
    {as bs : List Ty} {spec : Spec as bs} {n nX : Nat}
    (hfn : T.FnSpec host sym spec n nX)
    {Ψ : CodeSpec T.mach.MData} {H : T.mach.State → Prop}
    (hcl : TargetClosed T C host Ψ H) :
    cptr Ψ (C.toBits (T.mach.labelAddr host sym)) (targetCallPre T C host spec n nX Ψ) := by
  rintro s ⟨args, m, Q, X, ra, R, hspec, hargs, hra, hspE, hmem, hret, hexit⟩
  apply hcl (C.toBits (T.mach.labelAddr host sym)) s
  rw [C.of_to]
  refine eventually_weaken _ _ _ _ ?_ (hfn args m Q X hspec s ra R hargs hra hspE hmem)
  rintro st (⟨hpc, rets, m', hQ, hrets, hrest, hm'⟩ |
    ⟨sym', cs, xs, m', hX, hdef, hpc, hxs, hsp', ra', n', F, hnX, hbd, hra', hm'⟩)
  · left
    rw [hpc]
    exact hret (T.mach.data st) ⟨rets, m', hQ, hrets, hrest, hm'⟩
  · left
    rw [hpc]
    exact hexit sym' cs xs m' hX (T.mach.data st)
      ⟨hdef, hxs, hsp', ra', n', F, hnX, hbd, hra', hm'⟩

/-- Convenience specialization of `fnSpec_to_cptr` to `TargetSafe T C host H`. -/
theorem fnSpec_to_targetSafe_cptr {T : Target} (C : AddrCodec T) {host : T.mach.Host} {sym : Sym}
    {as bs : List Ty} {spec : Spec as bs} {n nX : Nat}
    (hfn : T.FnSpec host sym spec n nX) (H : T.mach.State → Prop) :
    cptr (TargetSafe T C host H) (C.toBits (T.mach.labelAddr host sym))
      (targetCallPre T C host spec n nX (TargetSafe T C host H)) :=
  fnSpec_to_cptr C hfn (TargetSafe.closed T C host H)

/-- Seam 2 (XCAP → Tier S): ANY opaque XCAP `cptr` entry (e.g. from `BedrockMach` `ModOk.link`
or hand-verified `W_res` blocks) yields a `Target.FnSpec` usable as an external `Γ` callee in
`Compiled`, `LinkedCert`, or `Env.ofTable_moduleOk` callers. -/
theorem cptr_to_Γ {T : Target} (C : AddrCodec T) {host : T.mach.Host} {sym : Sym}
    {as bs : List Ty} {spec : Spec as bs} {n nX : Nat}
    (hcptr : ∀ (H : T.mach.State → Prop),
      cptr (TargetSafe T C host H) (C.toBits (T.mach.labelAddr host sym))
        (targetCallPre T C host spec n nX (TargetSafe T C host H))) :
    T.FnSpec host sym spec n nX := by
  intro args m Q X hspec s ra R hargs hra hspE hmem
  let H : T.mach.State → Prop := fun st =>
    (T.mach.pc st = ra ∧
      ∃ (rets : Tup Val bs) (m' : Mem 64),
        Q rets m' ∧ T.RetsIn rets (T.mach.data st) ∧ T.Restored s (T.mach.data st) ∧
        (T.mach.mem (T.mach.data st) =⋆
          Eq m' ⋆ T.Exit (T.mach.getGpr s T.frame.sp) n ⋆ R)) ∨
    (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64),
      X sym' cs xs m' ∧ T.Defined host sym' ∧ T.mach.pc st = T.mach.labelAddr host sym' ∧
      T.ArgsIn xs (T.mach.data st) ∧
      T.frameSpec.spEntry (T.mach.getGpr (T.mach.data st) T.frame.sp) ∧
      ∃ (ra' : T.mach.Addr) (n' : Nat) (F : Mem 64 → Prop),
        nX ≤ n' ∧ n' + T.frame.raBytes ≤ 2 ^ 64 ∧ T.frameSpec.raReg (T.mach.data st) ra' ∧
        (T.mach.mem (T.mach.data st) =⋆
          Eq m' ⋆ T.Entry (T.mach.getGpr (T.mach.data st) T.frame.sp) ra' n' ⋆ F ⋆ R))
  have hsafe := hcptr H s ⟨args, m, Q, X, ra, R, hspec, hargs, hra, hspE, hmem, ?_, ?_⟩
  · dsimp only [TargetSafe] at hsafe
    rwa [C.of_to] at hsafe
  · intro s' hs'
    dsimp only [TargetSafe]
    rw [C.of_to]
    refine .done _ (Or.inl ⟨T.mach.pc_mk s' ra, ?_⟩)
    simpa only [T.mach.data_mk] using hs'
  · intro sym' cs xs m' hX s' hs'
    dsimp only [TargetSafe]
    rw [C.of_to]
    rcases hs' with ⟨hdef, hxs, hsp', ra', n', F, hnX, hbd, hra', hm'⟩
    refine .done _ (Or.inr ⟨sym', cs, xs, m', hX, hdef, T.mach.pc_mk s' _, ?_⟩)
    simpa only [T.mach.data_mk] using ⟨hxs, hsp', ra', n', F, hnX, hbd, hra', hm'⟩

/-- Seam 2 variant taking a `TargetClosed`-polymorphic `cptr` proof directly. -/
theorem cptr_of_targetClosed_to_Γ {T : Target} (C : AddrCodec T) {host : T.mach.Host} {sym : Sym}
    {as bs : List Ty} {spec : Spec as bs} {n nX : Nat}
    (hcptr : ∀ (Ψ : CodeSpec T.mach.MData) (H : T.mach.State → Prop),
      TargetClosed T C host Ψ H →
      cptr Ψ (C.toBits (T.mach.labelAddr host sym)) (targetCallPre T C host spec n nX Ψ)) :
    T.FnSpec host sym spec n nX :=
  cptr_to_Γ C (fun H => hcptr _ H (TargetSafe.closed T C host H))

/-- Exact bi-directional characterization of `Target.FnSpec` via `TargetSafe` XCAP `cptr`. -/
theorem fnSpec_iff_forall_targetSafe_cptr {T : Target} (C : AddrCodec T) {host : T.mach.Host}
    {sym : Sym} {as bs : List Ty} {spec : Spec as bs} {n nX : Nat} :
    T.FnSpec host sym spec n nX ↔
      ∀ (H : T.mach.State → Prop),
        cptr (TargetSafe T C host H) (C.toBits (T.mach.labelAddr host sym))
          (targetCallPre T C host spec n nX (TargetSafe T C host H)) :=
  ⟨fnSpec_to_targetSafe_cptr C, cptr_to_Γ C⟩

/-- Exact bi-directional characterization of `Target.FnSpec` via `TargetClosed` XCAP `cptr`. -/
theorem fnSpec_iff_forall_targetClosed_cptr {T : Target} (C : AddrCodec T) {host : T.mach.Host}
    {sym : Sym} {as bs : List Ty} {spec : Spec as bs} {n nX : Nat} :
    T.FnSpec host sym spec n nX ↔
      ∀ (Ψ : CodeSpec T.mach.MData) (H : T.mach.State → Prop),
        TargetClosed T C host Ψ H →
        cptr Ψ (C.toBits (T.mach.labelAddr host sym)) (targetCallPre T C host spec n nX Ψ) :=
  ⟨fun hfn _ _ hcl => fnSpec_to_cptr C hfn hcl, cptr_of_targetClosed_to_Γ C⟩

/-! ## 3. External-Callee Tables, Legalization, and `Env.ofTable` Bridges -/

private theorem sig_unique_of_nodup :
    ∀ {xs : List SigEntry}, (xs.map Prod.fst).Nodup →
      ∀ {sym as₁ bs₁ as₂ bs₂}, (sym, as₁, bs₁) ∈ xs → (sym, as₂, bs₂) ∈ xs →
        as₁ = as₂ ∧ bs₁ = bs₂
  | [], _, _, _, _, _, _, h, _ => nomatch h
  | (_, _, _) :: _, hnd, _, _, _, _, _, h1, h2 => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    rcases List.mem_cons.mp h1 with e1 | h1 <;> rcases List.mem_cons.mp h2 with e2 | h2
    · cases e1; cases e2; exact ⟨rfl, rfl⟩
    · cases e1; exact absurd rfl (hnd.1 _ h2)
    · cases e2; exact absurd rfl (hnd.1 _ h1)
    · exact sig_unique_of_nodup hnd.2 h1 h2

private theorem module_sigs_map_fst (M : Module) : M.sigs.map Prod.fst = M.names := by
  simp [Module.sigs, Module.names, List.map_append, List.map_map, Function.comp_def,
    Fn.sig, Extern.sig]

private theorem cast_encodeTup_eq_self {lt : LegalTarget} {ts : List Ty}
    (h : lt.legalSig ts = ts) (xs : Tup Val ts) :
    cast (congrArg (Tup Val) h) (encodeTup lt ts xs) = xs :=
  eq_of_heq ((cast_heq _ _).trans (encodeTup_heq_of_legalSig_eq lt h xs))

/-- Lift a source-signature `Target.FnSpec` into the legalized external-callee `legalEnv` contract
required by `compile_sound` / `Compiled.fnSpec` / `LinkedCert.fnSpec`. -/
theorem fnSpec_to_legalEnv {T : Target} {host : T.mach.Host} {lt : LegalTarget}
    {mod : Module} {Γ : Env} {sym : Sym} {as bs : List Ty} {n nX : Nat}
    (hnd : mod.namesNodup) (hsig : (sym, as, bs) ∈ mod.sigs)
    (has : lt.legalSig as = as) (hbs : lt.legalSig bs = bs)
    (hex_leg : ∀ args m P E, Γ sym as bs args m P E →
      ∀ g cs ys m₁, E g cs ys m₁ → lt.legalSig cs = cs)
    (hfn : T.FnSpec host sym (Γ sym as bs) n nX) :
    T.FnSpec host sym (legalEnv lt (Env.ofModule mod Γ) sym (lt.legalSig as) (lt.legalSig bs))
      n nX := by
  rw [has, hbs]
  intro xs' m Q' X' hleg s ra R hargs' hra hspE hmem
  rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs, P, E, hxs, hQ, hX, hmem₀, hΓ⟩
  obtain ⟨rfl, rfl⟩ := sig_unique_of_nodup (module_sigs_map_fst mod ▸ hnd) hsig hmem₀
  have hxs_eq : xs = xs' := (cast_encodeTup_eq_self has₀ xs).symm.trans hxs
  subst hxs_eq
  refine eventually_weaken _ _ _ _ ?_ (hfn xs m P E hΓ s ra R hargs' hra hspE hmem)
  rintro st (⟨hpc, rets, m', hP, hrets, hrest, hm'⟩ |
    ⟨sym', cs, ys, m', hE, hdef, hpc, hys, hsp', ra', n', F, hnX, hbd, hra', hm'⟩)
  · refine Or.inl ⟨hpc, rets, m', ?_, hrets, hrest, hm'⟩
    have hq := hQ (encodeTup lt bs rets) m' ⟨rets, rfl, hP⟩
    rwa [cast_encodeTup_eq_self hbs₀ rets] at hq
  · refine Or.inr ⟨sym', cs, ys, m', ?_, hdef, hpc, hys, hsp', ra', n', F, hnX, hbd, hra', hm'⟩
    have hcs : lt.legalSig cs = cs := hex_leg xs m P E hΓ sym' cs ys m' hE
    exact hX sym' cs ys m' ⟨cs, hcs, ys, cast_encodeTup_eq_self hcs ys, hE⟩

/-- Non-exiting specialization of `fnSpec_to_legalEnv` requiring no exit-signature check. -/
theorem fnSpec_to_legalEnv_noExit {T : Target} {host : T.mach.Host} {lt : LegalTarget}
    {mod : Module} {Γ : Env} {sym : Sym} {as bs : List Ty} {n nX : Nat}
    (hnd : mod.namesNodup) (hsig : (sym, as, bs) ∈ mod.sigs)
    (has : lt.legalSig as = as) (hbs : lt.legalSig bs = bs)
    (hnoex : ∀ args m P E, Γ sym as bs args m P E →
      Γ sym as bs args m P (fun _ _ _ _ => False))
    (hfn : T.FnSpec host sym (Γ sym as bs) n nX) :
    T.FnSpec host sym (legalEnv lt (Env.ofModule mod Γ) sym (lt.legalSig as) (lt.legalSig bs))
      n nX := by
  rw [has, hbs]
  intro xs' m Q' X' hleg s ra R hargs' hra hspE hmem
  rcases hleg with ⟨as₀, bs₀, has₀, hbs₀, xs, P, E, hxs, hQ, _, hmem₀, hΓ⟩
  obtain ⟨rfl, rfl⟩ := sig_unique_of_nodup (module_sigs_map_fst mod ▸ hnd) hsig hmem₀
  have hxs_eq : xs = xs' := (cast_encodeTup_eq_self has₀ xs).symm.trans hxs
  subst hxs_eq
  have hΓ0 := hnoex xs m P E hΓ
  refine eventually_weaken _ _ _ _ ?_ (hfn xs m P _ hΓ0 s ra R hargs' hra hspE hmem)
  rintro st (⟨hpc, rets, m', hP, hrets, hrest, hm'⟩ | ⟨_, _, _, _, hE, _⟩)
  · refine Or.inl ⟨hpc, rets, m', ?_, hrets, hrest, hm'⟩
    have hq := hQ (encodeTup lt bs rets) m' ⟨rets, rfl, hP⟩
    rwa [cast_encodeTup_eq_self hbs₀ rets] at hq
  · exact hE.elim

/-- Combine Seam 2 (`cptr_to_Γ`) with `fnSpec_to_legalEnv`. -/
theorem cptr_to_legalEnv_fnSpec {T : Target} (C : AddrCodec T) {host : T.mach.Host}
    {lt : LegalTarget} {mod : Module} {Γ : Env} {sym : Sym} {as bs : List Ty} {n nX : Nat}
    (hnd : mod.namesNodup) (hsig : (sym, as, bs) ∈ mod.sigs)
    (has : lt.legalSig as = as) (hbs : lt.legalSig bs = bs)
    (hex_leg : ∀ args m P E, Γ sym as bs args m P E →
      ∀ g cs ys m₁, E g cs ys m₁ → lt.legalSig cs = cs)
    (hcptr : ∀ (H : T.mach.State → Prop),
      cptr (TargetSafe T C host H) (C.toBits (T.mach.labelAddr host sym))
        (targetCallPre T C host (Γ sym as bs) n nX (TargetSafe T C host H))) :
    T.FnSpec host sym (legalEnv lt (Env.ofModule mod Γ) sym (lt.legalSig as) (lt.legalSig bs))
      n nX :=
  fnSpec_to_legalEnv hnd hsig has hbs hex_leg (cptr_to_Γ C hcptr)

/-- Combine Seam 2 (`cptr_to_Γ`) with `fnSpec_to_legalEnv_noExit`. -/
theorem cptr_to_legalEnv_fnSpec_noExit {T : Target} (C : AddrCodec T) {host : T.mach.Host}
    {lt : LegalTarget} {mod : Module} {Γ : Env} {sym : Sym} {as bs : List Ty} {n nX : Nat}
    (hnd : mod.namesNodup) (hsig : (sym, as, bs) ∈ mod.sigs)
    (has : lt.legalSig as = as) (hbs : lt.legalSig bs = bs)
    (hnoex : ∀ args m P E, Γ sym as bs args m P E →
      Γ sym as bs args m P (fun _ _ _ _ => False))
    (hcptr : ∀ (H : T.mach.State → Prop),
      cptr (TargetSafe T C host H) (C.toBits (T.mach.labelAddr host sym))
        (targetCallPre T C host (Γ sym as bs) n nX (TargetSafe T C host H))) :
    T.FnSpec host sym (legalEnv lt (Env.ofModule mod Γ) sym (lt.legalSig as) (lt.legalSig bs))
      n nX :=
  fnSpec_to_legalEnv_noExit hnd hsig has hbs hnoex (cptr_to_Γ C hcptr)

/-- Extract the row contract `e.eff` from `Env.ofTable tbl` when `tbl` has unique row names. -/
theorem env_ofTable_to_eff {tbl : List SpecEntry} {e : SpecEntry} (he : e ∈ tbl)
    (hnd : (tbl.map SpecEntry.name).Nodup) {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs}
    {X : XPost} (h : Env.ofTable tbl e.name e.as e.rs xs m Q X) : e.eff xs m Q X := by
  induction tbl with
  | nil => nomatch he
  | cons e' es ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | hmem
    · exact (Env.ofTable_cons_self _ _ _ _ _ _).1 h
    · have hne : e'.name ≠ e.name := fun h' => hnd.1 (h' ▸ List.mem_map_of_mem hmem)
      exact ih hmem hnd.2 ((Env.ofTable_cons_ne hne _ _ _ _).1 h)

/-- Legalized `(SigEntry, stackBound)` external-callee list derived from a table of
`(SpecEntry, stackBound)` XCAP external entries. -/
@[expose] def extCalleesOfTable (lt : LegalTarget)
    (extRows : List (SpecEntry × Nat)) : List (SigEntry × Nat) :=
  extRows.map fun r => ((r.1.name, lt.legalSig r.1.as, lt.legalSig r.1.rs), r.2)

/-- Lift a table of XCAP `cptr` proofs over `extCallees` directly into the `hext` external-callee
hypothesis expected by `compile_sound`, `Compiled.fnSpec`, and `LinkedCert.fnSpec`. -/
theorem cptr_table_to_extCallees {T : Target} (C : AddrCodec T) {lt : LegalTarget}
    {host : T.mach.Host} {mod : Module} {Γ : Env} {nX : Nat}
    {extCallees : List (SigEntry × Nat)}
    (hcptrs : ∀ p ∈ extCallees, ∀ (H : T.mach.State → Prop),
      cptr (TargetSafe T C host H) (C.toBits (T.mach.labelAddr host p.1.1))
        (targetCallPre T C host
          (legalEnv lt (Env.ofModule mod Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX
          (TargetSafe T C host H))) :
    ∀ p ∈ extCallees,
      T.FnSpec host p.1.1
        (legalEnv lt (Env.ofModule mod Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX :=
  fun p hp => cptr_to_Γ C (hcptrs p hp)

/-- Lift source-level `SpecEntry` XCAP `cptr` proofs (under `Env.ofTable tbl`) directly into the
legalized `hext` external-callee hypothesis for `extCalleesOfTable lt extRows`. -/
theorem cptr_specTable_to_extCallees {T : Target} (C : AddrCodec T) {lt : LegalTarget}
    {host : T.mach.Host} {mod : Module} {tbl : List SpecEntry} {nX : Nat}
    {extRows : List (SpecEntry × Nat)}
    (hmod_nd : mod.namesNodup)
    (htbl_nd : (tbl.map SpecEntry.name).Nodup)
    (hsub : ∀ r ∈ extRows, r.1 ∈ tbl)
    (hsigs : ∀ r ∈ extRows, (r.1.name, r.1.as, r.1.rs) ∈ mod.sigs)
    (hleg : ∀ r ∈ extRows, lt.legalSig r.1.as = r.1.as ∧ lt.legalSig r.1.rs = r.1.rs)
    (hnoex : ∀ r ∈ extRows, r.1.noExit = true)
    (hcptrs : ∀ r ∈ extRows, ∀ (H : T.mach.State → Prop),
      cptr (TargetSafe T C host H) (C.toBits (T.mach.labelAddr host r.1.name))
        (targetCallPre T C host r.1.eff r.2 nX (TargetSafe T C host H))) :
    ∀ p ∈ extCalleesOfTable lt extRows,
      T.FnSpec host p.1.1
        (legalEnv lt (Env.ofModule mod (Env.ofTable tbl)) p.1.1 p.1.2.1 p.1.2.2) p.2 nX := by
  intro p hp
  rcases List.mem_map.mp hp with ⟨r, hr, rfl⟩
  have hfn_eff : T.FnSpec host r.1.name r.1.eff r.2 nX := cptr_to_Γ C (hcptrs r hr)
  have hfn_tbl : T.FnSpec host r.1.name (Env.ofTable tbl r.1.name r.1.as r.1.rs) r.2 nX :=
    Target.FnSpec.of_spec T hfn_eff fun xs m Q X h =>
      env_ofTable_to_eff (hsub r hr) htbl_nd h
  have hnoex_r : ∀ xs m P E,
      Env.ofTable tbl r.1.name r.1.as r.1.rs xs m P E →
      Env.ofTable tbl r.1.name r.1.as r.1.rs xs m P (fun _ _ _ _ => False) := by
    intro xs m P E h
    have heff := env_ofTable_to_eff (hsub r hr) htbl_nd h
    apply Env.ofTable_of_mem (hsub r hr) htbl_nd
    simpa only [SpecEntry.eff, hnoex r hr, ↓reduceIte] using heff
  exact fnSpec_to_legalEnv_noExit hmod_nd (hsigs r hr) (hleg r hr).1 (hleg r hr).2 hnoex_r hfn_tbl

private theorem nodup_name_eq_bound :
    ∀ {rs : List (SpecEntry × Nat)}, (rs.map (fun r => r.1.name)).Nodup →
      ∀ {r₁ r₂ : SpecEntry × Nat}, r₁ ∈ rs → r₂ ∈ rs → r₁.1.name = r₂.1.name → r₁.2 = r₂.2
  | [], _, _, _, h, _, _ => nomatch h
  | _ :: _, hnd, _, _, h1, h2, hnm => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    rcases List.mem_cons.mp h1 with rfl | h1'
    · rcases List.mem_cons.mp h2 with rfl | h2'
      · rfl
      · exact absurd hnm.symm (hnd.1 _ h2')
    · rcases List.mem_cons.mp h2 with rfl | h2'
      · exact absurd hnm (hnd.1 _ h1')
      · exact nodup_name_eq_bound hnd.2 h1' h2' hnm

/-- Discharge the `hext_uniq` side condition of `Compiled.fnSpec` / `LinkedCert.fnSpec` for
`extCalleesOfTable lt extRows` from distinct external names disjoint from `mod.fns`. -/
theorem extCalleesOfTable_uniq (lt : LegalTarget) {mod : Module}
    {extRows : List (SpecEntry × Nat)}
    (hext_nd : (extRows.map (fun r => r.1.name)).Nodup)
    (hext_disj : ∀ r ∈ extRows, r.1.name ∉ mod.fns.map Fn.name) :
    (∀ p ∈ extCalleesOfTable lt extRows, ∀ q ∈ extCalleesOfTable lt extRows,
      p.1.1 = q.1.1 → p.2 = q.2) ∧
    (∀ p ∈ extCalleesOfTable lt extRows, p.1.1 ∉ mod.fns.map Fn.name) := by
  refine ⟨?_, ?_⟩
  · intro p hp q hq hnm
    rcases List.mem_map.mp hp with ⟨r₁, hr₁, rfl⟩
    rcases List.mem_map.mp hq with ⟨r₂, hr₂, rfl⟩
    exact nodup_name_eq_bound hext_nd hr₁ hr₂ hnm
  · intro p hp
    rcases List.mem_map.mp hp with ⟨r, hr, rfl⟩
    exact hext_disj r hr

/-! ## 4. `ModuleOk`, `Compiled`, and `LinkedCert` End-to-End XCAP Bridges -/

/-- Project per-function `Fn.Wf` and `Func.wp` obligations directly from `ModuleOk Γ mod`. -/
theorem moduleOk_wf_hwp {Γ : Env} {mod : Module} (hM : ModuleOk Γ mod) :
    (∀ f ∈ mod.fns, f.Wf) ∧
    (∀ f ∈ mod.fns, ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X) := by
  refine ⟨fun f hf => ?_, fun f hf => ?_⟩
  · obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hf
    exact (hM.fnsOk pre f post hsplit).1
  · obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hf
    exact (hM.fnsOk pre f post hsplit).2.2

/-- Link XCAP external `cptr` callees into `Compiled.fnSpec` via `ModuleOk`. -/
theorem compiled_fnSpec_of_cptr_ext {T : Target} (C : AddrCodec T) {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : Compiled T lt extCallees exits nX fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hM : ModuleOk Γ mod)
    (hcptrs : ∀ p ∈ extCallees, ∀ (H : T.mach.State → Prop),
      cptr (TargetSafe T C h H) (C.toBits (T.mach.labelAddr h p.1.1))
        (targetCallPre T C h
          (legalEnv lt (Env.ofModule mod Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX
          (TargetSafe T C h H)))
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ mod.fns.map Fn.name))
    (hexits : ∀ g ∈ exits, T.Defined h g) {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined h f.name ∧ T.FnSpec h f.name
      (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      (M.bound f.name) nX :=
  have ⟨hwf, hwp⟩ := moduleOk_wf_hwp hM
  M.fnSpec mod hfs h Γ k₀ hc hu hacyc hwf (hfs ▸ M.supportsSource) hwp
    (cptr_table_to_extCallees C hcptrs) hext_uniq hexits hf

/-- Bidirectional `Compiled` bridge: consume XCAP external `cptr` callees and export any compiled
function `f ∈ mod.fns` back as an XCAP `cptr` for every `TargetClosed` `Ψ`. -/
theorem compiled_to_cptr {T : Target} (C : AddrCodec T) {lt : LegalTarget}
    {extCallees : List (SigEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : Compiled T lt extCallees exits nX fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hM : ModuleOk Γ mod)
    (hcptrs : ∀ p ∈ extCallees, ∀ (H : T.mach.State → Prop),
      cptr (TargetSafe T C h H) (C.toBits (T.mach.labelAddr h p.1.1))
        (targetCallPre T C h
          (legalEnv lt (Env.ofModule mod Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX
          (TargetSafe T C h H)))
    (hext_uniq : (∀ p ∈ extCallees, ∀ q ∈ extCallees, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ extCallees, p.1.1 ∉ mod.fns.map Fn.name))
    (hexits : ∀ g ∈ exits, T.Defined h g) {f : Fn} (hf : f ∈ mod.fns)
    {Ψ : CodeSpec T.mach.MData} {H : T.mach.State → Prop} (hcl : TargetClosed T C h Ψ H) :
    T.Defined h f.name ∧
      cptr Ψ (C.toBits (T.mach.labelAddr h f.name))
        (targetCallPre T C h
          (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
          (M.bound f.name) nX Ψ) :=
  let ⟨hdef, hfn⟩ := compiled_fnSpec_of_cptr_ext C M mod hfs h Γ k₀ hc hu hacyc hM hcptrs
    hext_uniq hexits hf
  ⟨hdef, fnSpec_to_cptr C hfn hcl⟩

/-- Bundled proof obligations for a table of non-exiting XCAP external callees `extRows`
backing `Env.ofTable tbl` in `Compiled` / `LinkedCert` callers. -/
structure XcapExtTableOk {T : Target} (C : AddrCodec T) (lt : LegalTarget)
    (host : T.mach.Host) (mod : Module) (tbl : List SpecEntry) (nX : Nat)
    (extRows : List (SpecEntry × Nat)) : Prop where
  tbl_nodup : (tbl.map SpecEntry.name).Nodup
  tbl_noExit : ∀ e ∈ tbl, e.noExit = true
  sub : ∀ r ∈ extRows, r.1 ∈ tbl
  sigs : ∀ r ∈ extRows, (r.1.name, r.1.as, r.1.rs) ∈ mod.sigs
  legal : ∀ r ∈ extRows, lt.legalSig r.1.as = r.1.as ∧ lt.legalSig r.1.rs = r.1.rs
  ext_nodup : (extRows.map (fun r => r.1.name)).Nodup
  ext_disj : ∀ r ∈ extRows, r.1.name ∉ mod.fns.map Fn.name
  cptrs : ∀ r ∈ extRows, ∀ (H : T.mach.State → Prop),
    cptr (TargetSafe T C host H) (C.toBits (T.mach.labelAddr host r.1.name))
      (targetCallPre T C host r.1.eff r.2 nX (TargetSafe T C host H))

/-- End-to-end `Compiled` + `Env.ofTable_moduleOk` bridge taking source-level XCAP `cptr` proofs
for external rows `extRows` and yielding source-level `T.FnSpec` for `f ∈ mod.fns`. -/
theorem compiled_ofTable_fnSpec_src {T : Target} (C : AddrCodec T) {lt : LegalTarget}
    {extRows : List (SpecEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : Compiled T lt (extCalleesOfTable lt extRows) exits nX fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (tbl : List SpecEntry) (h : T.mach.Host) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hwf : AllFns Fn.Wf mod.fns)
    (hok : TableImpl (Env.ofTable tbl) mod.fns tbl)
    (hExt : XcapExtTableOk C lt h mod tbl nX extRows)
    (hexits : ∀ g ∈ exits, T.Defined h g)
    {f : Fn} (hf : f ∈ mod.fns) (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs) :
    T.Defined h f.name ∧
      T.FnSpec h f.name (Env.ofTable tbl f.name f.as f.rs) (M.bound f.name) nX := by
  have hMod : ModuleOk (Env.ofTable tbl) mod := Env.ofTable_moduleOk hacyc hwf hok
  have ⟨hwf', hwp'⟩ := moduleOk_wf_hwp hMod
  have hext := cptr_specTable_to_extCallees C hMod.nodup hExt.tbl_nodup hExt.sub hExt.sigs
    hExt.legal (fun r hr => hExt.tbl_noExit r.1 (hExt.sub r hr)) hExt.cptrs
  have ⟨hdef, hfn⟩ := M.fnSpec mod hfs h (Env.ofTable tbl) k₀ hc hu hacyc hwf'
    (hfs ▸ M.supportsSource) hwp' hext (extCalleesOfTable_uniq lt hExt.ext_nodup hExt.ext_disj)
    hexits hf
  exact ⟨hdef, fnSpec_of_legalEnv_legalSig_eq_noExit has hrs
    (List.mem_append_left _ (List.mem_map_of_mem hf))
    (Env.ofTable_noExit hExt.tbl_noExit f.name f.as f.rs) hfn⟩

/-- Lift `compiled_ofTable_fnSpec_src` directly back into an XCAP `cptr` for any `TargetClosed`
`Ψ` (full XCAP → `Compiled` (`Env.ofTable`) → XCAP round-trip). -/
theorem compiled_ofTable_cptr_src {T : Target} (C : AddrCodec T) {lt : LegalTarget}
    {extRows : List (SpecEntry × Nat)} {exits : List Sym} {nX : Nat}
    {fs : List Fn} {hints : List T.toIsa.Hints} {maxBound : Nat}
    (M : Compiled T lt (extCalleesOfTable lt extRows) exits nX fs hints maxBound)
    (mod : Module) (hfs : mod.fns = fs) (tbl : List SpecEntry) (h : T.mach.Host) (k₀ : Nat)
    (hc : M.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hwf : AllFns Fn.Wf mod.fns)
    (hok : TableImpl (Env.ofTable tbl) mod.fns tbl)
    (hExt : XcapExtTableOk C lt h mod tbl nX extRows)
    (hexits : ∀ g ∈ exits, T.Defined h g)
    {f : Fn} (hf : f ∈ mod.fns) (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    {Ψ : CodeSpec T.mach.MData} {H : T.mach.State → Prop} (hcl : TargetClosed T C h Ψ H) :
    T.Defined h f.name ∧
      cptr Ψ (C.toBits (T.mach.labelAddr h f.name))
        (targetCallPre T C h (Env.ofTable tbl f.name f.as f.rs) (M.bound f.name) nX Ψ) :=
  let ⟨hdef, hfn⟩ := compiled_ofTable_fnSpec_src C M mod hfs tbl h k₀ hc hu hacyc hwf hok hExt
    hexits hf has hrs
  ⟨hdef, fnSpec_to_cptr C hfn hcl⟩

/-- Link XCAP external `cptr` callees into `LinkedCert.fnSpec` via `ModuleOk`. -/
theorem linkedCert_fnSpec_of_cptr_ext {T : Target} (C : AddrCodec T) {L : TargetLayout T}
    {lt : LegalTarget} {hcl_lab : Rega.LabelClean T.toIsa} {mod : Module}
    {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    (cert : LinkedCert T L lt hcl_lab mod ext₀ exits nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hM : ModuleOk Γ mod)
    (hcptrs : ∀ p ∈ ext₀, ∀ (H : T.mach.State → Prop),
      cptr (TargetSafe T C h H) (C.toBits (T.mach.labelAddr h p.1.1))
        (targetCallPre T C h
          (legalEnv lt (Env.ofModule mod Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX
          (TargetSafe T C h H)))
    (hext_uniq : (∀ p ∈ ext₀, ∀ q ∈ ext₀, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ ext₀, p.1.1 ∉ mod.fns.map Fn.name))
    (hexits : ∀ g ∈ exits, T.Defined h g) {f : Fn} (hf : f ∈ mod.fns) :
    T.Defined h f.name ∧ T.FnSpec h f.name
      (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
      (cert.bound f.name) nX :=
  have ⟨hwf, hwp⟩ := moduleOk_wf_hwp hM
  cert.fnSpec h Γ k₀ hc hu hacyc hwf hwp (cptr_table_to_extCallees C hcptrs) hext_uniq hexits hf

/-- Lift any `LinkedCert.fnSpec` with XCAP external `cptr` callees directly into an XCAP `cptr`
for every `TargetClosed` `Ψ`. -/
theorem linkedCert_to_cptr {T : Target} (C : AddrCodec T) {L : TargetLayout T}
    {lt : LegalTarget} {hcl_lab : Rega.LabelClean T.toIsa} {mod : Module}
    {ext₀ : List (SigEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    (cert : LinkedCert T L lt hcl_lab mod ext₀ exits nX maxBound)
    (h : T.mach.Host) (Γ : Env) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hM : ModuleOk Γ mod)
    (hcptrs : ∀ p ∈ ext₀, ∀ (H : T.mach.State → Prop),
      cptr (TargetSafe T C h H) (C.toBits (T.mach.labelAddr h p.1.1))
        (targetCallPre T C h
          (legalEnv lt (Env.ofModule mod Γ) p.1.1 p.1.2.1 p.1.2.2) p.2 nX
          (TargetSafe T C h H)))
    (hext_uniq : (∀ p ∈ ext₀, ∀ q ∈ ext₀, p.1.1 = q.1.1 → p.2 = q.2) ∧
      (∀ p ∈ ext₀, p.1.1 ∉ mod.fns.map Fn.name))
    (hexits : ∀ g ∈ exits, T.Defined h g) {f : Fn} (hf : f ∈ mod.fns)
    {Ψ : CodeSpec T.mach.MData} {H : T.mach.State → Prop} (hcl : TargetClosed T C h Ψ H) :
    T.Defined h f.name ∧
      cptr Ψ (C.toBits (T.mach.labelAddr h f.name))
        (targetCallPre T C h
          (legalEnv lt (Env.ofModule mod Γ) f.name (lt.legalSig f.as) (lt.legalSig f.rs))
          (cert.bound f.name) nX Ψ) :=
  let ⟨hdef, hfn⟩ := linkedCert_fnSpec_of_cptr_ext C cert h Γ k₀ hc hu hacyc hM hcptrs
    hext_uniq hexits hf
  ⟨hdef, fnSpec_to_cptr C hfn hcl⟩

/-- Self-contained `LinkedCert` (`ext₀ = []`) export on `cert.host` to a source-level XCAP
`cptr` for every `TargetClosed` `Ψ`. -/
theorem linkedCert_host_to_cptr_src {T : Target} (C : AddrCodec T) {L : TargetLayout T}
    {lt : LegalTarget} {hcl_lab : Rega.LabelClean T.toIsa} {mod : Module}
    {exits : List Sym} {nX maxBound : Nat}
    (cert : LinkedCert T L lt hcl_lab mod [] exits nX maxBound)
    (Γ : Env) (hacyc : mod.checkAcyclic = true) (hM : ModuleOk Γ mod)
    {f : Fn} (hf : f ∈ mod.fns) (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X', Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X')
    {Ψ : CodeSpec T.mach.MData} {H : T.mach.State → Prop}
    (hcl : TargetClosed T C cert.host Ψ H) :
    T.Defined cert.host f.name ∧
      cptr Ψ (C.toBits (T.mach.labelAddr cert.host f.name))
        (targetCallPre T C cert.host (Γ f.name f.as f.rs) (cert.bound f.name) nX Ψ) := by
  have ⟨hwf, hwp⟩ := moduleOk_wf_hwp hM
  obtain ⟨hdef, hfn⟩ := cert.fnSpec_host_src Γ hacyc hwf hwp hf has hrs hnoex
  exact ⟨hdef, fnSpec_to_cptr C hfn hcl⟩

/-- End-to-end `LinkedCert` + `Env.ofTable_moduleOk` bridge consuming source-level XCAP `cptr`
proofs for external rows `extRows` and yielding source-level `T.FnSpec` for `f ∈ mod.fns`. -/
theorem linkedCert_ofTable_fnSpec_src {T : Target} (C : AddrCodec T) {L : TargetLayout T}
    {lt : LegalTarget} {hcl_lab : Rega.LabelClean T.toIsa} {mod : Module}
    {extRows : List (SpecEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    (cert : LinkedCert T L lt hcl_lab mod (extCalleesOfTable lt extRows) exits nX maxBound)
    (tbl : List SpecEntry) (h : T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hwf : AllFns Fn.Wf mod.fns)
    (hok : TableImpl (Env.ofTable tbl) mod.fns tbl)
    (hExt : XcapExtTableOk C lt h mod tbl nX extRows)
    (hexits : ∀ g ∈ exits, T.Defined h g)
    {f : Fn} (hf : f ∈ mod.fns) (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs) :
    T.Defined h f.name ∧
      T.FnSpec h f.name (Env.ofTable tbl f.name f.as f.rs) (cert.bound f.name) nX :=
  compiled_ofTable_fnSpec_src C cert.compiled mod cert.fns_eq tbl h k₀ hc hu hacyc hwf hok hExt
    hexits hf has hrs

/-- Full `LinkedCert` + `Env.ofTable_moduleOk` round-trip: XCAP external `cptr` callees →
`LinkedCert` compiled functions → XCAP `cptr` exports for every `TargetClosed` `Ψ`. -/
theorem linkedCert_ofTable_cptr_src {T : Target} (C : AddrCodec T) {L : TargetLayout T}
    {lt : LegalTarget} {hcl_lab : Rega.LabelClean T.toIsa} {mod : Module}
    {extRows : List (SpecEntry × Nat)} {exits : List Sym} {nX maxBound : Nat}
    (cert : LinkedCert T L lt hcl_lab mod (extCalleesOfTable lt extRows) exits nX maxBound)
    (tbl : List SpecEntry) (h : T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (T.mach.prog h) k₀) (hu : T.LabelsUnique h)
    (hacyc : mod.checkAcyclic = true) (hwf : AllFns Fn.Wf mod.fns)
    (hok : TableImpl (Env.ofTable tbl) mod.fns tbl)
    (hExt : XcapExtTableOk C lt h mod tbl nX extRows)
    (hexits : ∀ g ∈ exits, T.Defined h g)
    {f : Fn} (hf : f ∈ mod.fns) (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    {Ψ : CodeSpec T.mach.MData} {H : T.mach.State → Prop} (hcl : TargetClosed T C h Ψ H) :
    T.Defined h f.name ∧
      cptr Ψ (C.toBits (T.mach.labelAddr h f.name))
        (targetCallPre T C h (Env.ofTable tbl f.name f.as f.rs) (cert.bound f.name) nX Ψ) :=
  let ⟨hdef, hfn⟩ := linkedCert_ofTable_fnSpec_src C cert tbl h k₀ hc hu hacyc hwf hok hExt
    hexits hf has hrs
  ⟨hdef, fnSpec_to_cptr C hfn hcl⟩

end LeanQbe.T.Xcap
