module

public import LeanQbe.T.Xcap.Bridge
public import LeanQbe.T.MainCertProof
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.AbiLemmas
import LeanQbe.T.FlatLemmas
meta import Lean

/-!
# Generic Tests & Shared Dual-Arch Fixtures for `Xcap.Bridge` (`XcapBridgeTest`)

Arch-free test suite and shared fixtures for `LeanQbe.T.Xcap.Bridge` (paired with
`XcapBridgeX64Test` and `XcapBridgeArm64Test`, since `Kraken.X64` and `Kraken.AArch64` live in
isolated closures):

1. Shared IR functions (`fnAddTen`, `fnDoubleAddTen`, `fnCallOpaque`), `Module`s (`selfMod`,
   `callerMod`), `SpecEntry` tables (`selfTbl`, `callerTbl`), and `TableImpl` / `ModuleOk` proofs.
2. Generic hand-assembled opaque XCAP block (`opaqueIncCode` / `opaqueInc_xcap_cptr`) verified
   purely via `TargetClosed` / `Xcap.cptr` (`label_spec` → `op_spec` → `ret_spec`), plus a generic
   concrete `TargetInit` runner (`run_i64_of_cptr`) executing any `Xcap.cptr`.
3. Generic round-trip checks (`fnSpec_to_cptr` ↔ `cptr_to_Γ`, including non-trivial abnormal
   exits `XPost` and `Target.Restored` callee-saved preservation).
4. `check_std_axioms!` audit and MetaM import-closure isolation check confirming
   `LeanQbe.T.Xcap.Bridge` has `0` `Kraken.X64`, `Kraken.AArch64`, `Amd64`, or `Arm64` imports.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.XcapBridgeTest

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Xcap LeanQbe.T.ProofKit Kraken

/-! ## 1. Shared IR Modules, `SpecEntry` Tables, and `TableImpl` Proofs -/

/-- Leaf compiled function: `add_ten(x) = x + 10`. -/
@[expose] def fnAddTen : Fn :=
  ⟨"add_ten", [i64], [i64], fun _ _ (x, ()) =>
    .let_ ⟨.add i64, (.var x, .imm 10#64, ())⟩ fun (s, ()) =>
    .ret (.var s, ())⟩

/-- Calling compiled function: `double_add_ten(x) = add_ten(x) + add_ten(x)`. -/
@[expose] def fnDoubleAddTen : Fn :=
  ⟨"double_add_ten", [i64], [i64], fun _ _ (x, ()) =>
    .call "add_ten" (as := [i64]) (bs := [i64]) (.var x, ()) fun (r1, ()) =>
    .call "add_ten" (as := [i64]) (bs := [i64]) (.var x, ()) fun (r2, ()) =>
    .let_ ⟨.add i64, (.var r1, .var r2, ())⟩ fun (s, ()) =>
    .ret (.var s, ())⟩

/-- Compiled caller invoking external opaque XCAP block `"opaque_inc"`:
`call_opaque(x) = opaque_inc(x) + x`. -/
@[expose] def fnCallOpaque : Fn :=
  ⟨"call_opaque", [i64], [i64], fun _ _ (x, ()) =>
    .call "opaque_inc" (as := [i64]) (bs := [i64]) (.var x, ()) fun (y, ()) =>
    .let_ ⟨.add i64, (.var y, .var x, ())⟩ fun (s, ()) =>
    .ret (.var s, ())⟩

@[expose] def selfMod : Module :=
  { fns := [fnAddTen, fnDoubleAddTen] }

@[expose] def callerFns : List Fn :=
  [fnCallOpaque]

@[expose] def callerMod : Module :=
  { fns := callerFns
    externs := [⟨"opaque_inc", [i64], [i64]⟩] }

@[expose] def addTenSpec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ => Q (x + 10#64, ()) m

@[expose] def doubleAddTenSpec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ => Q ((x + 10#64) + (x + 10#64), ()) m

@[expose] def opaqueIncSpec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ => Q (x + 1#64, ()) m

@[expose] def callOpaqueSpec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ => Q ((x + 1#64) + x, ()) m

@[expose] def selfTbl : List SpecEntry :=
  [ .ofFn fnAddTen addTenSpec true
  , .ofFn fnDoubleAddTen doubleAddTenSpec true ]

@[expose] def opaqueIncRow : SpecEntry :=
  ⟨"opaque_inc", [i64], [i64], opaqueIncSpec, true⟩

@[expose] def callerTbl : List SpecEntry :=
  [ .ofFn fnCallOpaque callOpaqueSpec true
  , opaqueIncRow ]

@[expose] def opaqueExtRows : List (SpecEntry × Nat) :=
  [(opaqueIncRow, 0)]

@[expose] def opaqueExtCallees : List (SigEntry × Nat) :=
  [(("opaque_inc", [i64], [i64]), 0)]

theorem selfMod_acyclic : selfMod.checkAcyclic = true := by t_kernel_rfl
theorem callerMod_acyclic : callerMod.checkAcyclic = true := by t_kernel_rfl

theorem fnAddTen_wf : fnAddTen.Wf := by t_wf_reify
theorem fnDoubleAddTen_wf : fnDoubleAddTen.Wf := by t_wf_reify
theorem fnCallOpaque_wf : fnCallOpaque.Wf := by t_wf_reify

theorem selfMod_allWf : AllFns Fn.Wf selfMod.fns :=
  ⟨fnAddTen_wf, fnDoubleAddTen_wf, trivial⟩

theorem callerMod_allWf : AllFns Fn.Wf callerMod.fns :=
  ⟨fnCallOpaque_wf, trivial⟩

theorem selfTbl_impl : TableImpl (Env.ofTable selfTbl) selfMod.fns selfTbl := by
  refine ⟨SpecEntry.Impl.of ?_, SpecEntry.Impl.of ?_, trivial⟩
  · rintro ⟨x, ⟨⟩⟩ m Q _ hQ
    exact hQ
  · rintro ⟨x, ⟨⟩⟩ m Q X hQ
    dsimp only [Func.wp, fnDoubleAddTen, LeanQbe.T.wp, Op.wp, op2, OpCode.wp, lift2,
      Ty.hasFloat, Arg.val, vals]
    refine ⟨fun (r, _) m₁ => r = x + 10#64 ∧ m₁ = m, X, ?_, ?_, fun _ _ _ _ hx => hx⟩
    · exact Or.inl ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    · rintro ⟨r₁, ⟨⟩⟩ m₁ ⟨rfl, rfl⟩
      refine ⟨fun (r, _) m₂ => r = x + 10#64 ∧ m₂ = m₁, X, ?_, ?_, fun _ _ _ _ hx => hx⟩
      · exact Or.inl ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩⟩
      · rintro ⟨r₂, ⟨⟩⟩ m₂ ⟨rfl, rfl⟩
        exact hQ

theorem selfMod_moduleOk : ModuleOk (Env.ofTable selfTbl) selfMod :=
  Env.ofTable_moduleOk selfMod_acyclic selfMod_allWf selfTbl_impl

theorem callerTbl_impl : TableImpl (Env.ofTable callerTbl) callerMod.fns callerTbl := by
  refine ⟨SpecEntry.Impl.of ?_, trivial⟩
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  dsimp only [Func.wp, fnCallOpaque, LeanQbe.T.wp, Op.wp, op2, OpCode.wp, lift2,
    Ty.hasFloat, Arg.val, vals]
  refine ⟨fun (y, _) m₁ => y = x + 1#64 ∧ m₁ = m, X, ?_, ?_, fun _ _ _ _ hx => hx⟩
  · exact Or.inr ⟨(fun h => absurd h.1 (by decide)), Or.inl ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩⟩⟩
  · rintro ⟨y, ⟨⟩⟩ m₁ ⟨rfl, rfl⟩
    exact hQ

theorem callerMod_moduleOk : ModuleOk (Env.ofTable callerTbl) callerMod :=
  Env.ofTable_moduleOk callerMod_acyclic callerMod_allWf callerTbl_impl

theorem selfTbl_noExit : ∀ e ∈ selfTbl, e.noExit = true := by
  intro e he
  simp only [selfTbl, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> rfl

theorem callerTbl_noExit : ∀ e ∈ callerTbl, e.noExit = true := by
  intro e he
  simp only [callerTbl, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> rfl

theorem callerTbl_nodup : (callerTbl.map SpecEntry.name).Nodup := by
  decide

/-! ## 2. Generic Opaque XCAP Assembly Block (`opaqueInc_xcap_cptr`) & `TargetInit` Runner -/

/-- Hand-assembled opaque XCAP block `[label "opaque_inc"] ++ body ++ ret` for any `Target`. -/
@[expose] def opaqueIncCode (T : Target) (body : List T.Directive) : List T.Directive :=
  [T.frame.label "opaque_inc"] ++ body ++ T.frame.ret

private theorem abiGprHolds_i64_of_argsIn {T : Target} {arg0 : T.Reg} {x : BitVec 64}
    {s : T.mach.MData} (hassign : T.toIsa.assignArgs [i64] = some (.gpr arg0, ()))
    (hargs : T.ArgsIn (as := [i64]) (x, ()) s) :
    GprHolds (T.mach.getGpr s arg0) i64 x := by
  obtain ⟨locs, hlocs, hrel⟩ := hargs
  rw [hassign] at hlocs
  injection hlocs with hlocs
  subst hlocs
  cases hrel with
  | cons h1 _ =>
    dsimp only [Machine.AbiHolds] at h1
    exact h1.toGprHolds

private theorem retsIn_i64_of_gprHolds {T : Target} {ret0 : T.Reg} {v : BitVec 64}
    {s : T.mach.MData} (hassign : T.toIsa.assignRets [i64] = some (.gpr ret0, ()))
    (hval : GprHolds (T.mach.getGpr s ret0) i64 v) :
    T.RetsIn (bs := [i64]) (v, ()) s := by
  refine ⟨(.gpr ret0, ()), hassign, .cons ?_ .nil⟩
  exact abiGprHolds_bits64_of_gprHolds hval

/-- Pure XCAP verification of the opaque hand-assembled block `opaqueIncCode T body` on ANY
`Target`: given a single `.add i64` snippet `body` + `T.frame.ret` at offset `k₀`, proves
`Xcap.cptr Ψ (C.toBits (labelAddr host "opaque_inc")) (targetCallPre ... opaqueIncRow.eff 0 nX Ψ)`
for every `TargetClosed` `Ψ` (never constructing a `T.FnSpec` directly). -/
theorem opaqueInc_xcap_cptr {T : Target} (C : AddrCodec T) {host : T.mach.Host}
    {arg0 ret0 : T.Reg} {vh : VariantHint} {body : List T.Directive} {clob : FlagMask}
    {k₀ nX : Nat}
    (hassignA : T.toIsa.assignArgs [i64] = some (.gpr arg0, ()))
    (hassignR : T.toIsa.assignRets [i64] = some (.gpr ret0, ()))
    (harg_ns : arg0 ∉ T.frame.scratch)
    (hret_ns : ret0 ∉ T.frame.scratch)
    (hret_sp : ret0 ≠ T.frame.sp)
    (hret_cs : ret0 ∉ T.frame.calleeSaved)
    (hret_ra : ret0 ∉ T.frame.raRegs)
    (hra_bd : 0 + T.frame.raBytes ≤ 2 ^ 64)
    (hop : T.gpr.op (.add i64) (.gpr arg0, .imm 1#64, ()) (.gpr ret0, ()) vh = some (body, clob))
    (hinf : (opaqueIncCode T body).IsInfixAt (T.mach.prog host) k₀)
    (hu : T.LabelsUnique host)
    {Ψ : CodeSpec T.mach.MData} {H : T.mach.State → Prop}
    (hcl : TargetClosed T C host Ψ H) :
    cptr Ψ (C.toBits (T.mach.labelAddr host "opaque_inc"))
      (targetCallPre T C host opaqueIncRow.eff 0 nX Ψ) := by
  rintro s ⟨⟨x, ⟨⟩⟩, m, Q, X, ra, R, hspec, hargs, hra, _, hmem, hret, _⟩
  apply hcl (C.toBits (T.mach.labelAddr host "opaque_inc")) s
  rw [C.of_to]
  have hcons : (T.frame.label "opaque_inc" :: (body ++ T.frame.ret)).IsInfixAt
      (T.mach.prog host) k₀ := by
    simpa [opaqueIncCode, List.append_assoc] using hinf
  obtain ⟨hlab, hrest_inf⟩ := List.IsInfixAt.cons hcons
  obtain ⟨hbody_inf, hret_inf⟩ := List.IsInfixAt.append hrest_inf
  have haddr : T.mach.labelAddr host "opaque_inc" = T.mach.addrOf host k₀ :=
    T.frameSpec.labelAddr_eq hlab fun j hj heq => Nat.ne_of_lt hj (hu j k₀ "opaque_inc" heq hlab)
  rw [haddr]
  apply T.frameSpec.label_spec hlab
  have harg_holds : GprHolds (T.mach.getGpr s arg0) i64 x :=
    abiGprHolds_i64_of_argsIn hassignA hargs
  have hpa : TRel (T.mach.PArgHolds s) (as := [i64, i64])
      (.gpr arg0, .imm 1#64, ()) (x, 1#64, ()) :=
    .cons harg_holds (.cons rfl .nil)
  have hwp : (OpCode.add i64).wp (x, 1#64, ()) (fun r => r = (x + 1#64, ())) := rfl
  refine T.gprSpec.op_spec hop ?_ ?_ hpa hwp hbody_inf ?_
  · intro r hr
    simp only [tupArgGprs, tupFlatMap, PArg.gprs, List.append_nil, List.mem_singleton] at hr
    exact hr ▸ harg_ns
  · intro r hr
    simp only [tupDstGprs, tupFlatMap, PDst.gprs, List.append_nil, List.mem_singleton] at hr
    exact hr ▸ hret_ns
  · intro s₁ ⟨⟨rvs, hrvs, hdst⟩, hmem₁⟩ hfr₁
    subst hrvs
    cases hdst with
    | cons hret_val _ =>
      have hsp₁ : T.mach.getGpr s₁ T.frame.sp = T.mach.getGpr s T.frame.sp :=
        hfr₁.1 T.frame.sp fun hm => by
          rcases List.mem_append.mp hm with h1 | h2
          · simp only [tupDstGprs, tupFlatMap, PDst.gprs, List.append_nil,
              List.mem_singleton] at h1
            exact hret_sp h1.symm
          · exact T.frameSpec.sp_disj.1 h2
      have hra₁ : T.frameSpec.raReg s₁ ra :=
        T.frameSpec.raReg_of_raRegs s s₁ ra (fun r hr => hfr₁.1 r fun hm => by
          rcases List.mem_append.mp hm with h1 | h2
          · simp only [tupDstGprs, tupFlatMap, PDst.gprs, List.append_nil,
              List.mem_singleton] at h1
            exact hret_ra (h1 ▸ hr)
          · exact (T.frameSpec.ra_disj r hr).2.1 h2) hra
      have hmem₁_ra : T.mach.mem s₁ =⋆
          T.frameSpec.RetAddr (T.mach.getGpr s₁ T.frame.sp) ra ⋆
            (Eq m ⋆ region (T.mach.getGpr s T.frame.sp - BitVec.ofNat 64 0) 0 ⋆ R) := by
        rw [hmem₁, hsp₁]
        exact T.retAddr_of_entry' hmem
      refine T.frameSpec.ret_spec hret_inf hra₁ hmem₁_ra ?_
      intro s₂ hkg₂ _ hsp₂ hmem₂
      have hret₂ : T.mach.getGpr s₂ ret0 = T.mach.getGpr s₁ ret0 :=
        hkg₂ ret0 fun hm => by
          rcases List.mem_cons.mp hm with h1 | h2
          · exact hret_sp h1
          · exact hret_ns h2
      have hrest : T.Restored s s₂ := by
        refine ⟨fun r hr => ?_, ?_⟩
        · have h2 : T.mach.getGpr s₂ r = T.mach.getGpr s₁ r :=
            hkg₂ r fun hm => by
              rcases List.mem_cons.mp hm with rfl | hscr
              · exact T.frameSpec.sp_disj.2.2.1 hr
              · exact (T.frameSpec.scratch_disj r hscr).2.1 hr
          have h1 : T.mach.getGpr s₁ r = T.mach.getGpr s r :=
            hfr₁.1 r fun hm => by
              rcases List.mem_append.mp hm with hd | hscr
              · simp only [tupDstGprs, tupFlatMap, PDst.gprs, List.append_nil,
                  List.mem_singleton] at hd
                exact hret_cs (hd ▸ hr)
              · exact (T.frameSpec.scratch_disj r hscr).2.1 hr
          exact h2.trans h1
        · rw [hsp₂, hsp₁]
      have hrets₂ : T.RetsIn (bs := [i64]) (x + 1#64, ()) s₂ := by
        dsimp only [Machine.PDstHolds] at hret_val
        exact retsIn_i64_of_gprHolds hassignR (by simpa only [hret₂] using hret_val)
      have hmem₂_exit : T.mach.mem s₂ =⋆ Eq m ⋆ T.Exit (T.mach.getGpr s T.frame.sp) 0 ⋆ R := by
        rw [hmem₂, hmem₁]
        exact T.exit_of_entry hra_bd hmem
      refine .done _ (Or.inl ?_)
      rw [T.mach.pc_mk, T.mach.data_mk]
      exact hret s₂ ⟨(x + 1#64, ()), m, hspec, hrets₂, hrest, hmem₂_exit⟩

/-- Execute ANY `Xcap.cptr` at `TargetSafe` on a concrete `TargetInit` initial state, returning
an `i64` result in `I.ret0` at `pc = I.ra0` (demonstrating non-vacuous usability of Seam 1). -/
theorem run_i64_of_cptr {T : Target} (C : AddrCodec T) {maxStack maxMem : Nat}
    (I : TargetInit T maxStack maxMem) {host : T.mach.Host} {sym : Sym}
    {as : List Ty} {spec : Spec as [i64]} {n nX : Nat} {v : BitVec 64}
    (hcptr : cptr
      (TargetSafe T C host (fun st =>
        T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v))
      (C.toBits (T.mach.labelAddr host sym))
      (targetCallPre T C host spec n nX
        (TargetSafe T C host (fun st =>
          T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v))))
    (bsMem : List UInt8) (args : Tup Val as) (hn : n ≤ maxStack) (hbs : bsMem.length ≤ maxMem)
    (hargs : (T.toIsa.assignArgs as).isSome = true) {Q : Post [i64]}
    (hspec : spec args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ())) :
    Eventually (T.mach.step host)
      (fun st => T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v)
      (T.mach.mkState (I.initState n bsMem args) (T.mach.labelAddr host sym)) := by
  have hmem := I.mem_entry n bsMem args hn hbs
  rw [← I.get_sp n bsMem args] at hmem
  have hpre : targetCallPre T C host spec n nX
      (TargetSafe T C host (fun st =>
        T.mach.pc st = I.ra0 ∧ T.mach.getGpr (T.mach.data st) I.ret0 = v))
      (I.initState n bsMem args) :=
    targetCallPre_of_noExit args (bsMem.At 0x1000#64) Q I.ra0 Std.ExtHashMap.emp hspec
      (I.argsIn n bsMem args hargs) (I.raReg n bsMem args)
      (by rw [I.get_sp]; exact I.spEntry) hmem
      (fun s' ⟨rets, m', hq, hrets, _, _⟩ => by
        have hr := hQ rets m' hq
        subst hr
        refine TargetSafe.done_toBits ?_
        rw [T.mach.pc_mk, T.mach.data_mk]
        exact ⟨rfl, I.retsIn_singleton v s' hrets⟩)
  have hsafe := hcptr (I.initState n bsMem args) hpre
  dsimp only [TargetSafe] at hsafe
  rwa [C.of_to] at hsafe

/-! ## 3. Generic Round-Trip & Abnormal-Exit Preservation Checks -/

/-- Round-tripping `FnSpec → Xcap.cptr → FnSpec` preserves arbitrary abnormal exits `XPost` and
callee-saved restoration `T.Restored` losslessly on every `Target`. -/
theorem roundtrip_fnSpec_preserves_exits {T : Target} (C : AddrCodec T) {host : T.mach.Host}
    {sym : Sym} {as bs : List Ty} {spec : Spec as bs} {n nX : Nat}
    (hfn : T.FnSpec host sym spec n nX) :
    T.FnSpec host sym spec n nX :=
  cptr_to_Γ C (fun H => fnSpec_to_cptr C hfn (TargetSafe.closed T C host H))

/-- Bidirectional `TargetClosed` characterization check. -/
theorem roundtrip_targetClosed_cptr {T : Target} (C : AddrCodec T) {host : T.mach.Host}
    {sym : Sym} {as bs : List Ty} {spec : Spec as bs} {n nX : Nat}
    (hc : ∀ Ψ H, TargetClosed T C host Ψ H →
      cptr Ψ (C.toBits (T.mach.labelAddr host sym)) (targetCallPre T C host spec n nX Ψ))
    {Ψ : CodeSpec T.mach.MData} {H : T.mach.State → Prop}
    (hcl : TargetClosed T C host Ψ H) :
    cptr Ψ (C.toBits (T.mach.labelAddr host sym)) (targetCallPre T C host spec n nX Ψ) :=
  fnSpec_to_cptr C (cptr_of_targetClosed_to_Γ C hc) hcl

/-! ## 4. `std3` Axiom Audit & Arch-Isolation Check on `LeanQbe.T.Xcap.Bridge` -/

check_std_axioms!
  LeanQbe.T.Xcap.AddrCodec.toBits_inj
  LeanQbe.T.Xcap.AddrCodec.mkState_ofBits_toBits
  LeanQbe.T.Xcap.TargetSafe.done
  LeanQbe.T.Xcap.TargetSafe.done_toBits
  LeanQbe.T.Xcap.TargetSafe.weaken
  LeanQbe.T.Xcap.TargetSafe.bind
  LeanQbe.T.Xcap.TargetSafe.closed
  LeanQbe.T.Xcap.TargetClosed.of_eventually
  LeanQbe.T.Xcap.TargetClosed.of_H
  LeanQbe.T.Xcap.TargetClosed.weaken_H
  LeanQbe.T.Xcap.targetSafe_iff_forall_closed
  LeanQbe.T.Xcap.cptr_weaken
  LeanQbe.T.Xcap.targetCallPre_mono_Ψ
  LeanQbe.T.Xcap.targetCallPre_mono_spec
  LeanQbe.T.Xcap.targetCallPre_of_noExit
  LeanQbe.T.Xcap.fnSpec_to_cptr
  LeanQbe.T.Xcap.fnSpec_to_targetSafe_cptr
  LeanQbe.T.Xcap.cptr_to_Γ
  LeanQbe.T.Xcap.cptr_of_targetClosed_to_Γ
  LeanQbe.T.Xcap.fnSpec_iff_forall_targetSafe_cptr
  LeanQbe.T.Xcap.fnSpec_iff_forall_targetClosed_cptr
  LeanQbe.T.Xcap.fnSpec_to_legalEnv
  LeanQbe.T.Xcap.fnSpec_to_legalEnv_noExit
  LeanQbe.T.Xcap.cptr_to_legalEnv_fnSpec
  LeanQbe.T.Xcap.cptr_to_legalEnv_fnSpec_noExit
  LeanQbe.T.Xcap.env_ofTable_to_eff
  LeanQbe.T.Xcap.cptr_table_to_extCallees
  LeanQbe.T.Xcap.cptr_specTable_to_extCallees
  LeanQbe.T.Xcap.extCalleesOfTable_uniq
  LeanQbe.T.Xcap.moduleOk_wf_hwp
  LeanQbe.T.Xcap.compiled_fnSpec_of_cptr_ext
  LeanQbe.T.Xcap.compiled_to_cptr
  LeanQbe.T.Xcap.compiled_ofTable_fnSpec_src
  LeanQbe.T.Xcap.compiled_ofTable_cptr_src
  LeanQbe.T.Xcap.linkedCert_fnSpec_of_cptr_ext
  LeanQbe.T.Xcap.linkedCert_to_cptr
  LeanQbe.T.Xcap.linkedCert_host_to_cptr_src
  LeanQbe.T.Xcap.linkedCert_ofTable_fnSpec_src
  LeanQbe.T.Xcap.linkedCert_ofTable_cptr_src
  LeanQbeTest.T.XcapBridgeTest.opaqueInc_xcap_cptr
  LeanQbeTest.T.XcapBridgeTest.run_i64_of_cptr
  LeanQbeTest.T.XcapBridgeTest.roundtrip_fnSpec_preserves_exits
  LeanQbeTest.T.XcapBridgeTest.roundtrip_targetClosed_cptr

meta section

open Lean

private def isArchMod (m : Name) : Bool :=
  let s := m.toString
  s.startsWith "Kraken.X64" || s.startsWith "Kraken.AArch64" ||
  s.startsWith "LeanQbe.T.Amd64" || s.startsWith "LeanQbe.T.Arm64"

#eval show MetaM Unit from do
  let env ← importModules #[{ module := `LeanQbe.T.Xcap.Bridge }] {}
  let bad := env.header.moduleNames.filter isArchMod
  if !bad.isEmpty then
    throwError "Xcap.Bridge import closure leaks arch module(s): {bad.toList}"

end

end LeanQbeTest.T.XcapBridgeTest
