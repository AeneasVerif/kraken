module

public import LeanQbe.T.Unified.DriverLemmas
public import LeanQbe.T.Xcap.Link
import LeanQbe.T.FlatLemmas

/-!
# Tests for Unified Pipeline Core & Generic XCAP Core (`UnifiedPipelineTest`)

Exercises:
1. Generic `Tier`/`Stage`/`Pass` combinators (`Pass.gate_off`, `Stage.mapM_sound`, `midEndFine`).
2. Toy C0-lite frontend compiled through the **real** `Fn.mid` (`midEnd`), `unified_eq_legacy`,
   `unified_direct`, and `unified_refBackend_sound`.
3. Generic XCAP core (`Xcap.wp_block`, `Xcap.wp_of_ranked`, `Xcap.adequacy`, `Xcap.ModOk.link`,
   `Xcap.ModOk.close`) instantiated on both L0 (`WordSt`) and L1 (`MachSt (Fin 16)`).
4. `#print axioms` checks confirming all top-level theorems depend only on
   `⊆ [propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.UnifiedPipelineTest

open LeanQbe.T
open LeanQbe.T.Unified

/-! ## 1. Toy C0-lite frontend through real `midEnd` -/

inductive CStmt : Type
  | ret (v : BitVec 64)
  | ite (c : Bool) (t e : CStmt)

def CStmt.eval : CStmt → BitVec 64
  | .ret v => v
  | .ite c t e => if c then t.eval else e.eval

def CStmt.toExpr {V : Ty → Type} {L : List Ty → Type} : CStmt → Expr V L [i64]
  | .ret v => .ret (.imm v, ())
  | .ite c t e => .jnz (.imm c) t.toExpr e.toExpr

def CStmt.toFn (s : CStmt) : Fn := ⟨"main", [], [i64], fun _ _ _ => s.toExpr⟩

theorem CStmt.toExpr_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} (G : Ctx V₁ V₂)
    (D : Ctx L₁ L₂) : ∀ s : CStmt, Wf G D (s.toExpr (V := V₁) (L := L₁)) s.toExpr
  | .ret v => .ret (.cons (.imm (t := i64) v) .nil)
  | .ite c t e => .jnz (.imm (t := .bool) c) (toExpr_wf G D t) (toExpr_wf G D e)

theorem CStmt.toExpr_wp (Γ : Env) (Q : Post [i64]) (X : XPost) (m : Mem 64) :
    ∀ s : CStmt, Q (s.eval, ()) m → wp Γ Q X s.toExpr m
  | .ret v, h => h
  | .ite c t e, h => by
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · have hc' : c = true := hc
      subst hc'; exact toExpr_wp Γ Q X m t h
    · have hc' : c = false := hc
      subst hc'; exact toExpr_wp Γ Q X m e h

def c0Lite : Tier.{0, 0} where
  Prog := CStmt
  Ok _ := True
  Spec := BitVec 64 → Mem 64 → Prop
  top _ _ := False
  Sat s P := ∀ m, P s.eval m

def c0LiteLower : Stage c0Lite ssa where
  run s := .ok s.toFn
  tr _ P := {
    Γ := fun _ _ _ _ _ _ _ => False
    C := fun _ rs _ m Q _ => ∃ h : [i64] = rs, ∀ v, P v m →
      Q (cast (congrArg (Tup Val) h) (v, ())) m }
  ok s _ _ h := by
    cases h; intro V₁ V₂ L₁ L₂ _ _; exact CStmt.toExpr_wf _ _ s
  sound s _ P _ h hs := by
    cases h
    rintro xs m Q X ⟨hrs, hQ⟩
    cases hrs
    exact CStmt.toExpr_wp _ Q X m s (hQ _ (hs m))

def c0LiteFrontend : Frontend.{0, 0} := ⟨c0Lite, fun _ => {}, c0LiteLower⟩

theorem c0Lite_direct (s : CStmt) : route (c0LiteFrontend.caps s) = .direct := rfl

theorem c0Lite_end_to_end (t : LegalTarget) (src : CStmt) (P : BitVec 64 → Mem 64 → Prop)
    (ds : List Fn) (hrun : (unified c0LiteFrontend t refBackend).run src = .ok ds)
    (hP : ∀ m, P src.eval m) :
    ∃ fn, ds = [fn] ∧ ssa.Sat fn ((unified c0LiteFrontend t refBackend).tr src P) :=
  unified_refBackend_sound c0LiteFrontend t src P ds trivial hrun hP

theorem c0Lite_sample_ok :
    ∃ fn, (unified c0LiteFrontend LegalTarget.scalar64 refBackend).run
        (.ite true (.ret 7#64) (.ret 9#64)) = .ok [fn] ∧
      ssa.Sat fn ((unified c0LiteFrontend LegalTarget.scalar64 refBackend).tr
        (.ite true (.ret 7#64) (.ret 9#64)) (fun v _ => v = 7#64)) := by
  let src := CStmt.ite true (.ret 7#64) (.ret 9#64)
  have hsupp : (src.toFn.earlyOpt).body.supportsSource LegalTarget.scalar64 = true := by
    t_kernel_rfl
  have hrun :
      (unified c0LiteFrontend LegalTarget.scalar64 refBackend).run src =
        .ok [src.toFn.mid LegalTarget.scalar64] := by
    rw [unified_eq_legacy]
    simp only [c0LiteFrontend, c0LiteLower, refBackend, bindE, legacyMid, src, hsupp, ↓reduceIte]
    rfl
  obtain ⟨fn', hfn, hsat⟩ := unified_refBackend_sound c0LiteFrontend LegalTarget.scalar64 src
    (fun v _ => v = 7#64) [src.toFn.mid LegalTarget.scalar64] trivial hrun (fun _ => rfl)
  rw [List.cons.injEq] at hfn
  exact ⟨fn', hfn.1 ▸ hrun, hsat⟩

theorem c0Lite_eq_legacy_check (t : LegalTarget) :
    (unified c0LiteFrontend t refBackend).run =
      fun p => bindE (c0LiteFrontend.lower.run p) fun q =>
        bindE (legacyMid t q) refBackend.lower :=
  unified_eq_legacy c0LiteFrontend t refBackend

theorem c0Lite_fine_sound (src : CStmt) (ds : List Fn)
    (h : ((c0LiteFrontend.lower ≫ midEndFine LegalTarget.scalar64) ≫ refBackend.stage).run src =
      .ok ds) :
    ∃ fn, ds = [fn] ∧
      ssa.Sat fn (((c0LiteFrontend.lower ≫ midEndFine LegalTarget.scalar64) ≫
        refBackend.stage).tr src (fun v _ => v = src.eval)) :=
  ((c0LiteFrontend.lower ≫ midEndFine LegalTarget.scalar64) ≫ refBackend.stage).sound
    src ds (fun v _ => v = src.eval) trivial h (fun _ => rfl)

theorem factoring_sample_check :
    let F : Factoring Nat Nat Nat := {
      direct := fun n => .ok [n + 1, n + 2]
      vll := fun n => .ok [n]
      asm := fun k => [k + 1, k + 2]
      factor := fun _ => rfl
    }
    ∀ n is, F.vll n = .ok is → F.direct n = .ok (is.flatMap F.asm) :=
  fun n is h => Factoring.same_bytes _ n is h

/-! ## 2. `Pass.gate_off` and `Stage.mapM_sound` checks -/

theorem gate_off_opt (fn : Fn) :
    (Pass.gate (fun _ => false) optP).run fn = fn :=
  Pass.gate_off _ _ _ rfl

theorem mapM_c0Lite_sound (t : LegalTarget) (ps : List CStmt) (qs : List Fn)
    (h : (c0LiteFrontend.lower ≫ midEnd t).mapM ps = .ok qs) :
    ∀ q ∈ qs, ∃ p ∈ ps, (c0LiteFrontend.lower ≫ midEnd t).run p = .ok q ∧
      ssa.Ok q ∧
      ssa.Sat q ((c0LiteFrontend.lower ≫ midEnd t).tr p (fun (v : BitVec 64) _ => v = p.eval)) :=
  Stage.mapM_sound (c0LiteFrontend.lower ≫ midEnd t)
    (fun (p : CStmt) (v : BitVec 64) _ => v = p.eval) ps qs
    (fun _ _ => trivial) (fun _ _ _ => rfl) h

/-! ## 3. Generic XCAP Core: L0 (`WordSt`) and L1 (`MachSt`) + `wp_of_ranked` + `ModOk.link` -/

structure WordSt : Type where
  sp : BitVec 64
  rp : BitVec 64
  rv : BitVec 64
  r1 : BitVec 64
  r2 : BitVec 64
  r3 : BitVec 64
  mem : Mem 64

structure MachSt (Reg : Type) : Type where
  gpr : Reg → BitVec 64
  flags : BitVec 8
  mem : Mem 64

inductive TBlk (Reg : Type) : Type
  | movJmp (r : Reg) (v : BitVec 64) (tgt : BitVec 64)
  | ijmp (r : Reg)
  | decLoop (r : Reg) (bodyTgt exitTgt : BitVec 64)
  | halt (r : Reg)

def l1Mach (Reg : Type) [DecidableEq Reg] : Xcap.Mach (MachSt Reg) (TBlk Reg) where
  exec
    | .movJmp r v t, s, o =>
      o = .jump t { s with gpr := fun q => if q = r then v else s.gpr q }
    | .ijmp r, s, o => o = .jump (s.gpr r) s
    | .decLoop r bt et, s, o =>
      if s.gpr r = 0#64 then o = .jump et s
      else o = .jump bt { s with gpr := fun q => if q = r then s.gpr r - 1#64 else s.gpr q }
    | .halt r, s, o => o = .halt (s.gpr r) s

inductive WReg : Type | rp | rv
  deriving DecidableEq

def wget (s : WordSt) : WReg → BitVec 64 | .rp => s.rp | .rv => s.rv

def l0Mach : Xcap.Mach WordSt (TBlk WReg) where
  exec
    | .movJmp .rp v t, s, o => o = .jump t { s with rp := v }
    | .movJmp .rv v t, s, o => o = .jump t { s with rv := v }
    | .ijmp r, s, o => o = .jump (wget s r) s
    | .decLoop r bt et, s, o =>
      if wget s r = 0#64 then o = .jump et s
      else
        let v' := wget s r - 1#64
        let s' := match r with
          | .rp => { s with rp := v' }
          | .rv => { s with rv := v' }
        o = .jump bt s'
    | .halt r, s, o => o = .halt (wget s r) s

def demoCode (Reg : Type) (ra rv : Reg) : Xcap.Code (TBlk Reg) := fun pc =>
  if pc = 0#64 then some (.movJmp ra 16#64 8#64)
  else if pc = 8#64 then some (.ijmp ra)
  else if pc = 16#64 then some (.halt rv)
  else none

theorem demo_l1 (s : MachSt (Fin 16)) :
    Xcap.wp (l1Mach (Fin 16)) (demoCode (Fin 16) 1 0) (fun c _ => c = s.gpr 0) 0#64 s := by
  apply Xcap.wp_block (M := l1Mach (Fin 16)) (b := TBlk.movJmp 1 16#64 8#64) rfl ⟨_, rfl⟩
    _ (fun _ _ h => nomatch h)
  rintro _ _ ⟨⟩
  apply Xcap.wp_block (M := l1Mach (Fin 16)) (b := TBlk.ijmp 1) rfl ⟨_, rfl⟩
    _ (fun _ _ h => nomatch h)
  rintro _ _ ⟨⟩
  apply Xcap.wp_block (M := l1Mach (Fin 16)) (b := TBlk.halt 0) rfl ⟨_, rfl⟩
    (fun _ _ h => nomatch h)
  rintro _ _ ⟨⟩
  rfl

theorem demo_l0 (s : WordSt) :
    Xcap.wp l0Mach (demoCode WReg .rp .rv) (fun c _ => c = s.rv) 0#64 s := by
  apply Xcap.wp_block (M := l0Mach) (b := TBlk.movJmp .rp 16#64 8#64) rfl ⟨_, rfl⟩
    _ (fun _ _ h => nomatch h)
  rintro _ _ ⟨⟩
  apply Xcap.wp_block (M := l0Mach) (b := TBlk.ijmp .rp) rfl ⟨_, rfl⟩
    _ (fun _ _ h => nomatch h)
  rintro _ _ ⟨⟩
  apply Xcap.wp_block (M := l0Mach) (b := TBlk.halt .rv) rfl ⟨_, rfl⟩
    (fun _ _ h => nomatch h)
  rintro _ _ ⟨⟩
  rfl

theorem demo_adequate (s₀ : WordSt) (s₁ : MachSt (Fin 16)) :
    (∃ c s', Xcap.Halts l0Mach (demoCode WReg .rp .rv) 0#64 s₀ c s' ∧ c = s₀.rv) ∧
    (∃ c s', Xcap.Halts (l1Mach (Fin 16)) (demoCode (Fin 16) 1 0) 0#64 s₁ c s' ∧
      c = s₁.gpr 0) :=
  ⟨Xcap.adequacy (demo_l0 s₀), Xcap.adequacy (demo_l1 s₁)⟩

/-! ### `Xcap.wp_of_ranked` countdown loop + `Xcap.ModOk.link` / `close` -/

def loopCode : Xcap.Code (TBlk (Fin 16)) := fun pc =>
  if pc = 0#64 then some (.decLoop 0 0#64 8#64)
  else if pc = 8#64 then some (.halt 0)
  else none

theorem loop_ranked (s : MachSt (Fin 16)) :
    Xcap.wp (l1Mach (Fin 16)) loopCode (fun c _ => c = 0#64) 0#64 s := by
  let I : Nat → Xcap.CodeSpec (MachSt (Fin 16)) := fun n pc st =>
    (pc = 0#64 ∧ n = (st.gpr 0).toNat + 1) ∨ (pc = 8#64 ∧ st.gpr 0 = 0#64 ∧ n = 0)
  refine Xcap.wp_of_ranked I ?_ ((s.gpr 0).toNat + 1) 0#64 s (Or.inl ⟨rfl, rfl⟩)
  rintro n pc st (⟨rfl, rfl⟩ | ⟨rfl, h0, rfl⟩)
  · have hex : ∃ o, (l1Mach (Fin 16)).exec (TBlk.decLoop 0 0#64 8#64) st o := by
      by_cases hz : st.gpr 0 = 0#64
      · exact ⟨.jump 8#64 st, by simp [l1Mach, hz]⟩
      · exact ⟨.jump 0#64 { st with
          gpr := fun q => if q = 0 then st.gpr 0 - 1#64 else st.gpr q }, by simp [l1Mach, hz]⟩
    refine ⟨.decLoop 0 0#64 8#64, rfl, hex, ?_, fun _ _ h => by
      dsimp [l1Mach] at h; split at h <;> cases h⟩
    intro pc' st' hx
    dsimp [l1Mach] at hx
    split at hx
    · rename_i hzero
      cases hx
      exact ⟨0, Nat.succ_pos _, Or.inr ⟨rfl, hzero, rfl⟩⟩
    · rename_i hnz
      cases hx
      have hpos : 0 < (st.gpr 0).toNat := by
        cases h0 : (st.gpr 0).toNat with
        | zero =>
          exfalso; apply hnz
          exact BitVec.eq_of_toNat_eq h0
        | succ k => exact Nat.succ_pos k
      have hle : (1#64 : BitVec 64) ≤ st.gpr 0 :=
        BitVec.le_def.mpr (by simpa using Nat.succ_le_of_lt hpos)
      have hdec : (st.gpr 0 - 1#64).toNat = (st.gpr 0).toNat - 1 := by
        rw [BitVec.toNat_sub_of_le hle]
        rfl
      refine ⟨(st.gpr 0).toNat, Nat.lt_succ_self _, Or.inl ⟨rfl, ?_⟩⟩
      dsimp only
      split
      · rw [hdec]; omega
      · contradiction
  · refine ⟨.halt 0, rfl, ⟨_, rfl⟩, ?_, ?_⟩
    · intro _ _ hx; cases hx
    · intro c st' hx; cases hx; exact h0

def modRet : Xcap.Code (TBlk WReg) := fun pc =>
  if pc = 16#64 then some (.halt .rv) else none

def modCallee : Xcap.Code (TBlk WReg) := fun pc =>
  if pc = 8#64 then some (.ijmp .rp) else none

def modCaller : Xcap.Code (TBlk WReg) := fun pc =>
  if pc = 0#64 then some (.movJmp .rp 16#64 8#64) else none

def retPre (v : BitVec 64) : Xcap.CodeSpec WordSt → WordSt → Prop :=
  fun _ s => s.rv = v

def calleePre (v : BitVec 64) : Xcap.CodeSpec WordSt → WordSt → Prop :=
  Xcap.callPre WordSt.rp (fun s => s.rv = v) (fun s => s.rv = v)

theorem modRet_ok (v : BitVec 64) :
    Xcap.ModOk l0Mach modRet (fun c _ => c = v) [] [(16#64, retPre v)] := by
  intro big Ψ hs hcl _ e he
  simp only [List.mem_singleton] at he
  subst he
  intro s hs_rv
  apply hcl 16#64 (.halt .rv) (hs 16#64 (.halt .rv) rfl) s
  refine ⟨⟨_, rfl⟩, ?_, ?_⟩
  · intro _ _ h; cases h
  · rintro c s' ⟨⟩; exact hs_rv

theorem modCallee_ok (v : BitVec 64) :
    Xcap.ModOk l0Mach modCallee (fun c _ => c = v) [] [(8#64, calleePre v)] := by
  intro big Ψ hs hcl _ e he
  simp only [List.mem_singleton] at he
  subst he
  intro s ⟨hs_rv, hrp⟩
  apply hcl 8#64 (.ijmp .rp) (hs 8#64 (.ijmp .rp) rfl) s
  refine ⟨⟨_, rfl⟩, ?_, fun _ _ h => nomatch h⟩
  rintro pc' s' ⟨⟩
  exact hrp s hs_rv

theorem modCaller_ok (v : BitVec 64) :
    Xcap.ModOk l0Mach modCaller (fun c _ => c = v)
      [(16#64, retPre v), (8#64, calleePre v)] [(0#64, retPre v)] := by
  intro big Ψ hs hcl himp e he
  simp only [List.mem_singleton] at he
  subst he
  intro s hs_rv
  have h16 := himp (16#64, retPre v) List.mem_cons_self
  have h8 := himp (8#64, calleePre v) (List.mem_cons_of_mem _ List.mem_cons_self)
  apply hcl 0#64 (.movJmp .rp 16#64 8#64) (hs 0#64 _ rfl) s
  refine ⟨⟨_, rfl⟩, ?_, fun _ _ h => nomatch h⟩
  rintro pc' s' ⟨⟩
  exact h8 { s with rp := 16#64 } ⟨hs_rv, fun s'' hs'' => h16 s'' hs''⟩

theorem linked_demo_wp (v : BitVec 64) (s : WordSt) (hrv : s.rv = v) :
    Xcap.wp l0Mach (Xcap.union (Xcap.union modRet modCallee) modCaller)
      (fun c _ => c = v) 0#64 s := by
  have h12 :
      Xcap.ModOk l0Mach (Xcap.union modRet modCallee) (fun c _ => c = v)
        [] [(16#64, retPre v), (8#64, calleePre v)] :=
    Xcap.ModOk.link (modRet_ok v) (modCallee_ok v)
      (fun pc => by by_cases h : pc = 16#64 <;> simp [modRet, modCallee, h])
      (fun _ h => nomatch h)
  have h123 :
      Xcap.ModOk l0Mach (Xcap.union (Xcap.union modRet modCallee) modCaller) (fun c _ => c = v)
        [] ([(16#64, retPre v), (8#64, calleePre v)] ++ [(0#64, retPre v)]) :=
    Xcap.ModOk.link h12 (modCaller_ok v)
      (fun pc => by
        by_cases h1 : pc = 16#64 <;> by_cases h2 : pc = 8#64 <;>
          simp [Xcap.union, modRet, modCallee, modCaller, h1, h2])
      (fun e he => Or.inl he)
  exact Xcap.ModOk.close h123 (e := (0#64, retPre v)) (by simp) (fun _ => hrv)

theorem linked_demo_adequate (v : BitVec 64) (s : WordSt) (hrv : s.rv = v) :
    ∃ c s', Xcap.Halts l0Mach (Xcap.union (Xcap.union modRet modCallee) modCaller)
      0#64 s c s' ∧ c = v :=
  Xcap.adequacy (linked_demo_wp v s hrv)

end LeanQbeTest.T.UnifiedPipelineTest

#print axioms LeanQbe.T.Unified.Stage.mapM_sound
#print axioms LeanQbe.T.Unified.Pass.gate_off
#print axioms LeanQbe.T.Unified.midEnd
#print axioms LeanQbe.T.Unified.midEndFine
#print axioms LeanQbe.T.Unified.Factoring.transport
#print axioms LeanQbe.T.Unified.Factoring.same_bytes
#print axioms LeanQbe.T.Unified.unified_sound
#print axioms LeanQbe.T.Unified.unified_eq_legacy
#print axioms LeanQbe.T.Unified.unified_direct
#print axioms LeanQbe.T.Unified.unified_refBackend_sound
#print axioms LeanQbe.T.Xcap.Lfp.lfp_fix
#print axioms LeanQbe.T.Xcap.Lfp.lfp_of_ranked
#print axioms LeanQbe.T.Xcap.adequacy
#print axioms LeanQbe.T.Xcap.wp_of_ranked
#print axioms LeanQbe.T.Xcap.ModOk.link
#print axioms LeanQbe.T.Xcap.ModOk.close
#print axioms LeanQbeTest.T.UnifiedPipelineTest.c0Lite_end_to_end
#print axioms LeanQbeTest.T.UnifiedPipelineTest.c0Lite_sample_ok
#print axioms LeanQbeTest.T.UnifiedPipelineTest.demo_adequate
#print axioms LeanQbeTest.T.UnifiedPipelineTest.loop_ranked
#print axioms LeanQbeTest.T.UnifiedPipelineTest.linked_demo_adequate
