module

public import LeanQbe.T.RegaLemmas3a

/-!
# Soundness and Label-Cleanliness for `tryMoviZero` (`T.RegaLemmasZero`)

Verifies `tryMoviZero_ok` (proving `T.mach.Run` regardless of whether `Hints.deadFlags` matches
actual flag liveness, because `clob` returned by `T.gpr.moviDeadFlags?` frames every flag fact
via `T.mach.Frame` + `killFlags`/`killRegs`) and `tryMoviZero_clean`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace Rega

section Lemmas
variable {T : Target} {host : T.mach.Host} {post : T.mach.State → Prop} {hints : T.toIsa.Hints}

theorem tryMoviZero_ok {G : VCtx} {k ip : Nat} {st : SymState T.toIsa}
    {s : T.mach.MData} {sig ts : List Ty}
    {code : OpCode sig ts} {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    {dsts : Tup (PDst T.Reg T.VReg T.Cond) ts} {P : Tup Val ts → Prop}
    {c : List T.Directive} {clob : FlagMask} {z32 : Bool}
    (hargs : TRel (ArgRel G) args₁ args)
    (hwp : code.wp (vals args₁) P) (hinf : c.IsInfixAt (T.mach.prog host) k)
    (h : tryMoviZero T.toIsa hints ip st code args dsts = some (c, clob, z32))
    (fin : z32 = false → ∀ s',
      (∃ rvs, P rvs ∧ TRel (T.mach.PDstHolds s') dsts rvs) → T.mach.mem s' = T.mach.mem s →
      T.mach.Frame T.gpr.condReads s s' (tupDstGprs dsts ++ T.frame.scratch) [] clob →
      T.mach.Run host (k + c.length) s' post)
    (fin32 : z32 = true → ∀ {rd} (ht : ts = [.bits 32]),
      dsts = (ht ▸ (PDst.gpr rd, ())) → ∀ s' (rv : BitVec 32), P (ht ▸ (rv, ())) →
      T.mach.getGpr s' rd = rv.setWidth 64 → T.mach.mem s' = T.mach.mem s →
      T.mach.Frame T.gpr.condReads s s' (rd :: T.frame.scratch) [] clob →
      T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  dsimp only [tryMoviZero] at h
  cases hfl : !flagsDeadAt T.toIsa hints (some ip) st with
  | true => simp [hfl] at h
  | false =>
    simp only [hfl, Bool.false_eq_true, ↓reduceIte] at h
    cases hmd : T.gpr.moviDeadFlags? with
    | none => rw [hmd] at h; cases h
    | some fn =>
      rw [hmd] at h; dsimp only at h
      have zeroOut : ∀ (n : Nat) (rd : T.Reg) (hn : n ≤ 64) (ht : ts = [.bits n])
          (hd : dsts = (ht ▸ (PDst.gpr rd, ()))),
          c = (fn rd 0#64).1 → clob = (fn rd 0#64).2 →
          z32 = (Nat.beq n 32 && T.frame.bitWidths.contains 32) →
          P (ht ▸ (0#n, ())) → T.mach.Run host k s post := by
        intro n rd hn ht hd hc hcl hz hP
        subst ht; dsimp only at hd; subst hd; subst hc; subst hcl
        refine T.gprSpec.moviDeadFlags?_spec (rd := rd) (c := 0#64) hmd hinf
          fun s' ⟨hrd, hm⟩ hfr => ?_
        by_cases hn32 : n = 32
        · subst hn32
          cases hbw : T.frame.bitWidths.contains 32 with
          | true =>
            have hzt : z32 = true := by
              have hbeq : Nat.beq 32 32 = true := rfl
              rw [hbeq, hbw] at hz; exact hz
            exact fin32 hzt rfl rfl s' 0#32 hP (by simpa using hrd) hm hfr
          | false =>
            have hzf : z32 = false := by
              have hbeq : Nat.beq 32 32 = true := rfl
              rw [hbeq, hbw] at hz; exact hz
            exact fin hzf s' ⟨(0#32, ()), hP, .cons ⟨by decide, by rw [hrd]; rfl⟩ .nil⟩ hm hfr
        · have hzf : z32 = false := by
            have hbeq : Nat.beq n 32 = false := by
              cases hb : Nat.beq n 32
              · rfl
              · exact absurd (Nat.beq_eq.mp hb) hn32
            simpa [hbeq] using hz
          refine fin hzf s' ⟨(0#n, ()), hP, .cons ⟨hn, ?_⟩ .nil⟩ hm hfr
          rw [hrd, BitVec.setWidth_zero]
      cases code with
      | copy t =>
        cases t with
        | bits n =>
          rcases args with ⟨a, ⟨⟩⟩; rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
          cases a with
          | var _ => dsimp only at h; cases h
          | imm cb =>
            cases d0 with
            | gpr rd =>
              dsimp only at h; split at h
              · rename_i hcb
                simp only [Bool.and_eq_true, Nat.ble_eq, beq_iff_eq] at hcb
                cases hargs; rename_i ha _; cases ha
                simp only [OpCode.wp, vals, Arg.val, hcb.2] at hwp
                cases h
                exact zeroOut n rd hcb.1.1 rfl rfl rfl rfl rfl hwp
              · cases h
            | vec _ => dsimp only at h; cases h
        | bool =>
          rcases args with ⟨a, ⟨⟩⟩; rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
          cases a with
          | var _ => dsimp only at h; cases h
          | imm b =>
            cases b with
            | true => dsimp only at h; cases h
            | false =>
              cases d0 with
              | gpr rd =>
                dsimp only at h
                cases hargs; rename_i ha _; cases ha
                simp only [OpCode.wp, vals, Arg.val] at hwp
                cases h
                refine T.gprSpec.moviDeadFlags?_spec (rd := rd) (c := 0#64) hmd hinf
                  fun s' ⟨hrd, hm⟩ hfr => ?_
                refine fin rfl s' ⟨(false, ()), hwp, .cons ?_ .nil⟩ hm hfr
                show GprHolds (T.mach.getGpr s' rd) .bool false
                rw [hrd]; rfl
              | vec _ | flag _ => dsimp only at h; cases h
        | float _ | pair _ _ => dsimp only at h; cases h
      | ofBool n =>
        rcases args with ⟨a, ⟨⟩⟩; rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
        cases a with
        | var _ => dsimp only at h; cases h
        | imm b =>
          cases b with
          | true => dsimp only at h; cases h
          | false =>
            cases d0 with
            | gpr rd =>
              dsimp only at h; split at h
              · rename_i hnb
                simp only [Bool.and_eq_true, Nat.ble_eq] at hnb
                cases hargs; rename_i ha _; cases ha
                simp only [OpCode.wp, vals, Arg.val, Bool.toNat_false] at hwp
                cases h
                exact zeroOut n rd hnb.1 rfl rfl rfl rfl rfl hwp
              · cases h
            | vec _ => dsimp only at h; cases h
      | bitcast t u hsz =>
        cases t with
        | bits m =>
          cases u with
          | bits n =>
            have hmn : m = n := hsz
            subst hmn
            rcases args with ⟨a, ⟨⟩⟩; rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
            cases a with
            | var _ => dsimp only at h; cases h
            | imm cb =>
              cases d0 with
              | gpr rd =>
                dsimp only at h; split at h
                · rename_i hcb
                  simp only [Bool.and_eq_true, Nat.ble_eq, beq_iff_eq] at hcb
                  cases hargs; rename_i ha _; cases ha
                  simp only [OpCode.wp, vals, Arg.val, hcb.2, toBits, ofBits] at hwp
                  cases h
                  exact zeroOut m rd hcb.1.1.1.1 rfl rfl rfl rfl rfl hwp
                · cases h
              | vec _ => dsimp only at h; cases h
          | _ => dsimp only at h; cases h
        | _ => dsimp only at h; cases h
      | _ => dsimp only at h; cases h

theorem tryMoviZero_clean {I : Isa} (hcl : LabelClean I) {h : I.Hints} {ip : Nat}
    {st : SymState I} {sig ts : List Ty} {code : OpCode sig ts} {args : Tup (Arg VNat) sig}
    {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts} {c : List I.Directive} {cl : FlagMask}
    {z32 : Bool} (ht : tryMoviZero I h ip st code args dsts = some (c, cl, z32)) :
    NoLab I c := by
  dsimp only [tryMoviZero] at ht
  cases hfl : !flagsDeadAt I h (some ip) st with
  | true => simp [hfl] at ht
  | false =>
    simp only [hfl, Bool.false_eq_true, ↓reduceIte] at ht
    cases hmd : I.gpr.moviDeadFlags? with
    | none => rw [hmd] at ht; cases ht
    | some fn =>
      rw [hmd] at ht; dsimp only at ht
      cases code with
      | copy t =>
        cases t with
        | bits n =>
          rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
          cases a <;> cases d0 <;> (dsimp only at ht; try split at ht) <;>
            cases ht <;> exact hcl.moviDeadFlags _ _ _ hmd
        | bool =>
          rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
          cases a with
          | var _ => dsimp only at ht; cases ht
          | imm b =>
            cases b <;> cases d0 <;>
              (dsimp only at ht; cases ht <;> exact hcl.moviDeadFlags _ _ _ hmd)
        | float _ | pair _ _ => dsimp only at ht; cases ht
      | ofBool _ =>
        rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
        cases a with
        | var _ => dsimp only at ht; cases ht
        | imm b =>
          cases b <;> cases d0 <;> (dsimp only at ht; try split at ht) <;>
            cases ht <;> exact hcl.moviDeadFlags _ _ _ hmd
      | bitcast t u _ =>
        cases t <;> cases u <;> first
          | (dsimp only at ht; cases ht)
          | (rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
             cases a <;> cases d0 <;> (dsimp only at ht; try split at ht) <;>
               cases ht <;> exact hcl.moviDeadFlags _ _ _ hmd)
      | _ => dsimp only at ht; cases ht

end Lemmas
end Rega
end LeanQbe.T
