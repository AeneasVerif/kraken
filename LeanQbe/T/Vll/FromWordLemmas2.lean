module

public import LeanQbe.T.Vll.FromWord
import LeanQbe.T.Vll.FromWordLemmas0
import LeanQbe.T.Vll.FromWordLemmas1
import LeanQbe.T.Unified.CfgContifyLemmas
import LeanQbe.T.BedrockWord.Ops
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.TargetLemmas

/-!
# Block & Cascade Simulation Lemmas (`Vll.FromWordLemmas2`)

Arch-free intermediate simulation layer behind the private proof firewall for
`LeanQbe.T.Vll.FromWord`:
* §1. `IsNoRaInstr` (`raReg` preservation across straight-line lowered instructions), Stage-0/1
      code-map slice extractors, and generic `VllCodeMap.Closed` dispatch helpers.
* §2. Open L0 → VLL block body simulation (`lowerPlainBody_bwp`).

Zero `@[expose]`, zero `Arm64`/`Amd64`/`Kraken.X64`/`Kraken.AArch64` imports, zero `*Lemmas*`
public imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.BedrockWord
open LeanQbe.T.Unified

/-! ## §1. Straight-Line `raReg` Preservation & `VllCodeMap` Dispatch Helpers -/

/-- Instruction whose execution preserves every register outside `b.allRegs` (and leaves `sp`
and `mem` untouched except `.store`/`.slotSt`, never touching `A.abi.raRegs`). -/
def IsNoRaInstr {A : Arch} (b : WordRegBind A) : Instr A → Prop
  | .mov _ rd _ | .movi rd _ | .alu _ _ rd _ _ _ | .setcc rd _ | .load _ _ rd _
  | .slotLd rd _ | .symAddr _ rd => rd ∈ b.allRegs
  | .cmp _ _ _ | .test _ _ _ | .clearFlags | .store _ _ _ | .slotSt _ _
  | .pad _ | .label _ => True
  | _ => False

private theorem isNoRaInstr_fall_raReg {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {i : Instr A} {s s' : MachSt A} {ra : BitVec 64}
    (hno : IsNoRaInstr b i) (hra : (vllFramePreds A).raReg s ra)
    (hr : instrRel A symAddr 0#64 i s (.fall s')) :
    (vllFramePreds A).raReg s' ra := by
  cases hkind : A.abi.raKind with
  | stack => simp [vllFramePreds, hkind]
  | linkReg lr =>
    have hra' : s.gpr lr = ra := by simpa only [vllFramePreds, hkind] using hra
    have hlreq : ∀ {r : A.Reg}, r ∈ b.allRegs → lr ≠ r := fun {r} hm he =>
      hwf.no_ra r hm (by rw [← he]; simp [Abi.raRegs, hkind, RaKind.raRegs])
    have hs' : s'.gpr lr = ra := by
      cases i with
      | mov _ rd _ | movi rd _ | alu _ _ rd _ _ _ | setcc rd _ =>
        dsimp only [IsNoRaInstr] at hno
        dsimp only [instrRel] at hr; cases hr
        simpa [MachSt.gpr_setFlags, MachSt.gpr_setGprW_ne _ _ _ (hlreq hno),
          MachSt.gpr_setGpr_ne _ _ (hlreq hno)] using hra'
      | load _ _ rd _ | slotLd rd _ =>
        dsimp only [IsNoRaInstr] at hno
        dsimp only [instrRel] at hr
        rcases hr with ⟨_, _, hr'⟩; cases hr'
        simpa [MachSt.gpr_setGpr_ne _ _ (hlreq hno)] using hra'
      | symAddr _ rd =>
        dsimp only [IsNoRaInstr] at hno
        dsimp only [instrRel] at hr; cases hr
        simpa [MachSt.gpr_setGpr_ne _ _ (hlreq hno)] using hra'
      | cmp _ _ _ | test _ _ _ | clearFlags =>
        dsimp only [instrRel] at hr; cases hr; exact hra'
      | store _ _ _ | slotSt _ _ =>
        dsimp only [instrRel] at hr; rcases hr with ⟨_, hr'⟩; cases hr'; exact hra'
      | pad _ | label _ =>
        dsimp only [instrRel] at hr; cases hr; exact hra'
      | prologue _ | epilogue _ | canonAbi _ _ | jmp _ | jcc _ _ | jnzGpr _ _
      | call _ | icall _ | ret | exitJmp _ | tailJmpR _ | ijmp _ | native _ =>
        cases hno
    simpa only [vllFramePreds, hkind] using hs'

theorem bodyWp_preserve_raReg {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {ra : BitVec 64} {K : MachSt A → Prop}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} :
    ∀ {is : List (Instr A)} {s : MachSt A},
      (∀ i ∈ is, IsNoRaInstr b i) →
      (vllFramePreds A).raReg s ra →
      bodyWp A symAddr is K Ψ H s →
      bodyWp A symAddr is (fun s' => K s' ∧ (vllFramePreds A).raReg s' ra) Ψ H s
  | [], _, _, hra, hwp => ⟨hwp, hra⟩
  | i :: is, _, hno, hra, ⟨hex, hf, hj, hh⟩ => by
    have hnoi : IsNoRaInstr b i := hno i List.mem_cons_self
    have hnois : ∀ x ∈ is, IsNoRaInstr b x := fun x hx => hno x (List.mem_cons_of_mem _ hx)
    exact ⟨hex, fun s' hr => bodyWp_preserve_raReg hwf hnois
      (isNoRaInstr_fall_raReg hwf hnoi hra hr) (hf s' hr), hj, hh⟩

theorem isNoRa_mem_append {A : Arch} {b : WordRegBind A} {xs ys : List (Instr A)}
    (hx : ∀ i ∈ xs, IsNoRaInstr b i) (hy : ∀ i ∈ ys, IsNoRaInstr b i) :
    ∀ i ∈ xs ++ ys, IsNoRaInstr b i := fun i hi => by
  rcases List.mem_append.mp hi with h1 | h2
  · exact hx i h1
  · exact hy i h2

theorem work_mem_allRegs {A : Arch} (b : WordRegBind A) :
    b.altRet ∈ b.allRegs ∧ b.w0 ∈ b.allRegs ∧ b.w1 ∈ b.allRegs ∧ b.w2 ∈ b.allRegs := by
  have hm : ∀ r ∈ b.workRegs, r ∈ b.allRegs := fun r hr =>
    List.mem_append_left _ (List.mem_append_right _ hr)
  exact ⟨hm _ (by simp [WordRegBind.workRegs]), hm _ (by simp [WordRegBind.workRegs]),
    hm _ (by simp [WordRegBind.workRegs]), hm _ (by simp [WordRegBind.workRegs])⟩

theorem wordRegs_mem_allRegs {A : Arch} (b : WordRegBind A) :
    ∀ r ∈ b.wordRegs, r ∈ b.allRegs := fun _ hr =>
  List.mem_append_left _ (List.mem_append_left _ hr)

theorem isNoRa_emitToLoc {A : Arch} (b : WordRegBind A) (dst : WordLoc A)
    {build : A.Reg → List (Instr A)}
    (hb : ∀ rd, (rd = b.w0 ∨ dst = .gpr rd) → ∀ i ∈ build rd, IsNoRaInstr b i) :
    ∀ i ∈ emitToLoc b.w0 dst build, IsNoRaInstr b i := by
  dsimp only [emitToLoc]
  cases dst with
  | gpr rd => exact hb rd (Or.inr rfl)
  | slot k =>
    refine isNoRa_mem_append (hb b.w0 (Or.inl rfl)) (fun i hi => ?_)
    simp only [List.mem_singleton] at hi; subst hi; trivial

theorem isNoRa_loadArgToGpr {A : Arch} (b : WordRegBind A) {sb d : Nat} {tmp : A.Reg}
    {t : Ty} {a : Arg K t} {is : List (Instr A)} {rg : A.Reg}
    (ht : tmp ∈ b.allRegs) (h : loadArgToGpr b sb d tmp a = .ok (is, rg)) :
    ∀ i ∈ is, IsNoRaInstr b i := by
  intro i hi
  cases a with
  | imm c =>
    dsimp only [loadArgToGpr] at h
    cases him : immToBitVec64 t c <;> simp [him] at h
    rcases h with ⟨rfl, _⟩
    simp only [List.mem_singleton] at hi; subst hi; exact ht
  | var idx =>
    dsimp only [loadArgToGpr] at h; split at h
    · cases hl : locOf b sb (d - 1 - idx) <;> simp [hl] at h
      · rcases h with ⟨rfl, _⟩; cases hi
      · rcases h with ⟨rfl, _⟩; simp only [List.mem_singleton] at hi; subst hi; exact ht
    · cases h

theorem isNoRa_loadArgInto {A : Arch} (b : WordRegBind A) {sb d : Nat} {dst : A.Reg}
    {t : Ty} {a : Arg K t} {is : List (Instr A)}
    (hd : dst ∈ b.allRegs) (h : loadArgInto b sb d dst a = .ok is) :
    ∀ i ∈ is, IsNoRaInstr b i := by
  intro i hi
  cases a with
  | imm c =>
    dsimp only [loadArgInto] at h
    cases him : immToBitVec64 t c <;> simp [him] at h
    subst h; simp only [List.mem_singleton] at hi; subst hi; exact hd
  | var idx =>
    dsimp only [loadArgInto] at h; split at h
    · cases hl : locOf b sb (d - 1 - idx) with
      | gpr r =>
        simp only [hl] at h; split at h
        · cases h; cases hi
        · cases h; simp only [List.mem_singleton] at hi; subst hi; exact hd
      | slot k =>
        simp only [hl, Except.ok.injEq] at h; subst h
        simp only [List.mem_singleton] at hi; subst hi; exact hd
    · cases h

theorem isNoRa_loadLevelInto {A : Arch} (b : WordRegBind A) (sb : Nat) {dst : A.Reg}
    (lvl : Nat) (hd : dst ∈ b.allRegs) :
    ∀ i ∈ loadLevelInto b sb dst lvl, IsNoRaInstr b i := by
  intro i hi
  dsimp only [loadLevelInto] at hi
  cases hl : locOf b sb lvl <;> simp only [hl] at hi
  · split at hi
    · cases hi
    · simp only [List.mem_singleton] at hi; subst hi; exact hd
  · simp only [List.mem_singleton] at hi; subst hi; exact hd

private theorem isNoRa_argToSrc {A : Arch} (b : WordRegBind A) {sb d : Nat} {tmp : A.Reg}
    {t : Ty} {a : Arg K t} {is : List (Instr A)} {sr : Src A}
    (ht : tmp ∈ b.allRegs) (h : argToSrc b sb d tmp a = .ok (is, sr)) :
    ∀ i ∈ is, IsNoRaInstr b i := by
  intro i hi
  cases a with
  | imm c =>
    dsimp only [argToSrc] at h
    cases him : immToBitVec64 t c <;> simp [him] at h
    rcases h with ⟨rfl, _⟩; cases hi
  | var idx =>
    dsimp only [argToSrc] at h; split at h
    · cases hl : locOf b sb (d - 1 - idx) <;> simp [hl] at h
      · rcases h with ⟨rfl, _⟩; cases hi
      · rcases h with ⟨rfl, _⟩; simp only [List.mem_singleton] at hi; subst hi; exact ht
    · cases h

private theorem isNoRa_emitParOne {A : Arch} (b : WordRegBind A) {d : A.Reg} {sv : ParSrc A}
    (hd : d ∈ b.allRegs) : ∀ i ∈ emitParOne d sv, IsNoRaInstr b i := by
  intro i hi
  cases sv <;> dsimp only [emitParOne] at hi
  · split at hi
    · cases hi
    · simp only [List.mem_singleton] at hi; subst hi; exact hd
  · simp only [List.mem_singleton] at hi; subst hi; exact hd
  · simp only [List.mem_singleton] at hi; subst hi; exact hd

private theorem isNoRa_parMoveAux {A : Arch} (b : WordRegBind A) {dests : List A.Reg}
    {tmp : A.Reg} (ht : tmp ∈ b.allRegs) (hd : ∀ r ∈ dests, r ∈ b.allRegs) :
    ∀ (fuel : Nat) (ms : List (A.Reg × ParSrc A)),
      (∀ p ∈ ms, p.1 ∈ dests) → ∀ i ∈ parMoveAux tmp fuel ms, IsNoRaInstr b i
  | 0, [], _, _, hi => by cases hi
  | _ + 1, [], _, _, hi => by cases hi
  | 0, _ :: _, _, _, hi => by cases hi
  | fuel + 1, m :: ms, hsub, i, hi => by
    dsimp only [parMoveAux] at hi
    cases hf : (m :: ms).find? (fun p => !isReadIn p.1 (m :: ms)) with
    | some p =>
      rw [hf] at hi
      have hp := hsub p (List.mem_of_find?_eq_some hf)
      rcases List.mem_append.mp hi with h1 | h2
      · exact isNoRa_emitParOne b (hd p.1 hp) i h1
      · refine isNoRa_parMoveAux b ht hd fuel _ (fun q hq => ?_) i h2
        exact hsub q (List.mem_filter.mp (List.mem_filter.mp hq).1).1
    | none =>
      rw [hf] at hi
      rcases m with ⟨d, sv⟩
      have hdm := hsub (d, sv) List.mem_cons_self
      cases sv with
      | reg r =>
        dsimp only at hi
        split at hi
        · exact isNoRa_parMoveAux b ht hd fuel ms
            (fun q hq => hsub q (List.mem_cons_of_mem _ hq)) i hi
        · rcases List.mem_append.mp hi with h1 | h2
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
            rcases h1 with rfl | rfl
            · exact ht
            · exact hd d hdm
          · refine isNoRa_parMoveAux b ht hd fuel _ (fun q hq => ?_) i h2
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hq).1
            exact hsub p (List.mem_cons_of_mem _ hp)
      | slot _ | imm _ =>
        rcases List.mem_append.mp hi with h1 | h2
        · exact isNoRa_emitParOne b (hd d hdm) i h1
        · exact isNoRa_parMoveAux b ht hd fuel ms
            (fun q hq => hsub q (List.mem_cons_of_mem _ hq)) i h2

theorem isNoRa_emitNextRegs {A : Arch} (b : WordRegBind A) {sb d : Nat}
    {nxt : RegsExpr K} {is : List (Instr A)} (h : emitNextRegs b sb d nxt = .ok is) :
    ∀ i ∈ is, IsNoRaInstr b i := by
  dsimp only [emitNextRegs, Except.bind] at h
  cases h0 : argToParSrc b sb d nxt.sp <;> rw [h0] at h; · cases h
  cases h1 : argToParSrc b sb d nxt.rp <;> rw [h1] at h; · cases h
  cases h2 : argToParSrc b sb d nxt.rv <;> rw [h2] at h; · cases h
  cases h3 : argToParSrc b sb d nxt.r1 <;> rw [h3] at h; · cases h
  cases h4 : argToParSrc b sb d nxt.r2 <;> rw [h4] at h; · cases h
  cases h5 : argToParSrc b sb d nxt.r3 <;> rw [h5] at h; · cases h
  cases h
  have hwk := work_mem_allRegs b
  refine isNoRa_parMoveAux b hwk.2.2.1 (wordRegs_mem_allRegs b) _ _ (fun p hp => ?_)
  have hm := (List.mem_filter.mp hp).1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [WordRegBind.wordRegs]

private theorem isNoRa_lowerBinBits {A : Arch} (b : WordRegBind A) {sb d : Nat}
    {op : CoreAlu} {w : Width} {t : Ty} {lhs rhs : Arg K t} {is : List (Instr A)}
    (h : lowerBinBits b sb d (locOf b sb d) op w lhs rhs = .ok is) :
    ∀ i ∈ is, IsNoRaInstr b i := by
  dsimp only [lowerBinBits, Except.bind] at h
  cases h1 : loadArgToGpr b sb d b.w1 lhs <;> rw [h1] at h; · cases h
  cases h2 : argToSrc b sb d b.w2 rhs <;> rw [h2] at h; · cases h
  cases h
  have hwk := work_mem_allRegs b
  refine isNoRa_mem_append (isNoRa_mem_append (isNoRa_loadArgToGpr b hwk.2.2.1 h1)
    (isNoRa_argToSrc b hwk.2.2.2 h2)) (isNoRa_emitToLoc b _ fun rd hrd i hi => ?_)
  simp only [List.mem_singleton] at hi; subst hi
  rcases hrd with rfl | hl
  · exact hwk.2.1
  · exact locOf_gpr_mem_allRegs b sb d hl

private theorem isNoRa_lowerCmpBits {A : Arch} (b : WordRegBind A) {sb d : Nat}
    {o : CmpOp} {w : Width} {t : Ty} {lhs rhs : Arg K t} {is : List (Instr A)}
    (h : lowerCmpBits b sb d (locOf b sb d) o w lhs rhs = .ok is) :
    ∀ i ∈ is, IsNoRaInstr b i := by
  dsimp only [lowerCmpBits, Except.bind] at h
  cases hcc : b.condOfCmp? o <;> rw [hcc] at h; · cases h
  cases h1 : loadArgToGpr b sb d b.w1 lhs <;> rw [h1] at h; · cases h
  cases h2 : argToSrc b sb d b.w2 rhs <;> rw [h2] at h; · cases h
  cases h
  have hwk := work_mem_allRegs b
  refine isNoRa_mem_append (isNoRa_mem_append (isNoRa_mem_append
    (isNoRa_loadArgToGpr b hwk.2.2.1 h1) (isNoRa_argToSrc b hwk.2.2.2 h2))
    (fun i hi => by simp only [List.mem_singleton] at hi; subst hi; trivial))
    (isNoRa_emitToLoc b _ fun rd hrd i hi => ?_)
  simp only [List.mem_singleton] at hi; subst hi
  rcases hrd with rfl | hl
  · exact hwk.2.1
  · exact locOf_gpr_mem_allRegs b sb d hl

private theorem isNoRa_lowerSelect {A : Arch} (b : WordRegBind A) {sb d : Nat}
    {t : Ty} {c : Arg K .bool} {tVal fVal : Arg K t} {is : List (Instr A)}
    (h : lowerSelect b sb d (locOf b sb d) c tVal fVal = .ok is) :
    ∀ i ∈ is, IsNoRaInstr b i := by
  dsimp only [lowerSelect, Except.bind] at h
  cases h1 : loadArgToGpr b sb d b.w0 c <;> rw [h1] at h; · cases h
  cases h2 : loadArgInto b sb d b.w1 tVal <;> rw [h2] at h; · cases h
  cases h3 : loadArgInto b sb d b.w2 fVal <;> rw [h3] at h; · cases h
  cases h
  have hwk := work_mem_allRegs b
  refine isNoRa_mem_append (isNoRa_mem_append (isNoRa_mem_append (isNoRa_mem_append
    (isNoRa_loadArgToGpr b hwk.2.1 h1) (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact hwk.2.1
      · exact hwk.2.2.1
      · exact hwk.2.1))
    (isNoRa_loadArgInto b hwk.2.2.1 h2)) (isNoRa_loadArgInto b hwk.2.2.2 h3))
    (isNoRa_emitToLoc b _ fun rd hrd i hi => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact hwk.2.2.1
  · exact hwk.2.1
  · exact hwk.2.2.2
  · rcases hrd with rfl | hl
    · exact hwk.2.1
    · exact locOf_gpr_mem_allRegs b sb d hl

theorem isNoRa_lowerOp {A : Arch} (b : WordRegBind A) {sb d d' : Nat}
    {ts : List Ty} {op : Op K ts} {is : List (Instr A)}
    (h : lowerOp b sb d op = .ok (is, d')) :
    ∀ i ∈ is, IsNoRaInstr b i := by
  rcases op with ⟨code, args⟩
  have hwk := work_mem_allRegs b
  dsimp only [lowerOp] at h
  cases code with
  | copy t =>
    rcases args with ⟨x, ⟨⟩⟩; cases t with
    | bool =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases h1 : loadArgToGpr b sb d b.w1 x <;> rw [h1] at h; · cases h
      cases h
      exact isNoRa_mem_append (isNoRa_loadArgToGpr b hwk.2.2.1 h1)
        (isNoRa_emitToLoc b _ fun rd hrd i hi => by
          simp only [List.mem_singleton] at hi; subst hi
          rcases hrd with rfl | hl
          · exact hwk.2.1
          · exact locOf_gpr_mem_allRegs b sb d hl)
    | bits n =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases hw : Width.ofBits? n with
      | none => rw [hw] at h; cases h
      | some w =>
        rw [hw] at h; dsimp only at h
        cases h1 : loadArgToGpr b sb d b.w1 x <;> rw [h1] at h; · cases h
        cases h
        exact isNoRa_mem_append (isNoRa_loadArgToGpr b hwk.2.2.1 h1)
          (isNoRa_emitToLoc b _ fun rd hrd i hi => by
            simp only [List.mem_singleton] at hi; subst hi
            rcases hrd with rfl | hl
            · exact hwk.2.1
            · exact locOf_gpr_mem_allRegs b sb d hl)
    | float _ | pair _ _ => cases h
  | neg t =>
    rcases args with ⟨x, ⟨⟩⟩; cases t with
    | bool =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases h1 : loadArgToGpr b sb d b.w1 x <;> rw [h1] at h; · cases h
      cases h
      exact isNoRa_mem_append (isNoRa_loadArgToGpr b hwk.2.2.1 h1)
        (isNoRa_emitToLoc b _ fun rd hrd i hi => by
          simp only [List.mem_singleton] at hi; subst hi
          rcases hrd with rfl | hl
          · exact hwk.2.1
          · exact locOf_gpr_mem_allRegs b sb d hl)
    | bits n =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases hw : Width.ofBits? n with
      | none => rw [hw] at h; cases h
      | some w =>
        rw [hw] at h; dsimp only at h
        cases h1 : loadArgToGpr b sb d b.w2 x <;> rw [h1] at h; · cases h
        cases h
        refine isNoRa_mem_append (isNoRa_mem_append
          (fun i hi => by simp only [List.mem_singleton] at hi; subst hi; exact hwk.2.2.1)
          (isNoRa_loadArgToGpr b hwk.2.2.2 h1))
          (isNoRa_emitToLoc b _ fun rd hrd i hi => by
            simp only [List.mem_singleton] at hi; subst hi
            rcases hrd with rfl | hl
            · exact hwk.2.1
            · exact locOf_gpr_mem_allRegs b sb d hl)
    | float _ | pair _ _ => cases h
  | not t =>
    rcases args with ⟨x, ⟨⟩⟩; cases t with
    | bool =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases h1 : loadArgToGpr b sb d b.w1 x <;> rw [h1] at h; · cases h
      cases h
      exact isNoRa_mem_append (isNoRa_loadArgToGpr b hwk.2.2.1 h1)
        (isNoRa_emitToLoc b _ fun rd hrd i hi => by
          simp only [List.mem_singleton] at hi; subst hi
          rcases hrd with rfl | hl
          · exact hwk.2.1
          · exact locOf_gpr_mem_allRegs b sb d hl)
    | bits n =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases hw : Width.ofBits? n with
      | none => rw [hw] at h; cases h
      | some w =>
        rw [hw] at h; dsimp only at h
        cases h1 : loadArgToGpr b sb d b.w1 x <;> rw [h1] at h; · cases h
        cases h
        exact isNoRa_mem_append (isNoRa_loadArgToGpr b hwk.2.2.1 h1)
          (isNoRa_emitToLoc b _ fun rd hrd i hi => by
            simp only [List.mem_singleton] at hi; subst hi
            rcases hrd with rfl | hl
            · exact hwk.2.1
            · exact locOf_gpr_mem_allRegs b sb d hl)
    | float _ | pair _ _ => cases h
  | add t | sub t | mul t | and t | or t | xor t =>
    rcases args with ⟨x, y, ⟨⟩⟩; cases t with
    | bool =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases hb : lowerBinBits b sb d (locOf b sb d) _ .w8 x y <;> rw [hb] at h; · cases h
      cases h; exact isNoRa_lowerBinBits b hb
    | bits n =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases hw : Width.ofBits? n with
      | none => rw [hw] at h; cases h
      | some w =>
        rw [hw] at h; dsimp only at h
        cases hb : lowerBinBits b sb d (locOf b sb d) _ w x y <;> rw [hb] at h; · cases h
        cases h; exact isNoRa_lowerBinBits b hb
    | float _ | pair _ _ => cases h
  | shl t | lshr t | ashr t =>
    rcases args with ⟨x, y, ⟨⟩⟩; cases t with
    | bits n =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases hw : Width.ofBits? n with
      | none => rw [hw] at h; cases h
      | some w =>
        rw [hw] at h; dsimp only at h
        cases hb : lowerBinBits b sb d (locOf b sb d) _ w x y <;> rw [hb] at h; · cases h
        cases h; exact isNoRa_lowerBinBits b hb
    | bool | float _ | pair _ _ => cases h
  | cmp _ t _ hm =>
    subst hm; rcases args with ⟨x, y, ⟨⟩⟩; cases t with
    | bool =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases hc : lowerCmpBits b sb d (locOf b sb d) _ .w8 x y <;> rw [hc] at h; · cases h
      cases h; exact isNoRa_lowerCmpBits b hc
    | bits n =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases hw : Width.ofBits? n with
      | none => rw [hw] at h; cases h
      | some w =>
        rw [hw] at h; dsimp only at h
        cases hc : lowerCmpBits b sb d (locOf b sb d) _ w x y <;> rw [hc] at h; · cases h
        cases h; exact isNoRa_lowerCmpBits b hc
    | float _ | pair _ _ => cases h
  | select t =>
    rcases args with ⟨c, x, y, ⟨⟩⟩
    dsimp only [lowerOpCode, Except.bind] at h; split at h
    · cases hs : lowerSelect b sb d (locOf b sb d) c x y <;> rw [hs] at h; · cases h
      cases h; exact isNoRa_lowerSelect b hs
    · cases h
  | zext m n =>
    rcases args with ⟨x, ⟨⟩⟩; dsimp only [lowerOpCode, Except.bind] at h; split at h
    · cases h1 : loadArgToGpr b sb d b.w1 x <;> rw [h1] at h; · cases h
      cases h
      exact isNoRa_mem_append (isNoRa_loadArgToGpr b hwk.2.2.1 h1)
        (isNoRa_emitToLoc b _ fun rd hrd i hi => by
          simp only [List.mem_singleton] at hi; subst hi
          rcases hrd with rfl | hl
          · exact hwk.2.1
          · exact locOf_gpr_mem_allRegs b sb d hl)
    · cases h
  | sext m n =>
    rcases args with ⟨x, ⟨⟩⟩; dsimp only [lowerOpCode, Except.bind] at h; split at h
    · cases h1 : loadArgInto b sb d b.w1 x <;> rw [h1] at h; · cases h
      cases h
      refine isNoRa_mem_append (isNoRa_mem_append (isNoRa_loadArgInto b hwk.2.2.1 h1)
        (fun i hi => by
          split at hi
          · cases hi
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl <;> exact hwk.2.2.1))
        (fun i hi => by
          cases hl : locOf b sb d <;> simp only [hl] at hi
          · simp only [List.mem_singleton] at hi; subst hi
            exact locOf_gpr_mem_allRegs b sb d hl
          · simp only [List.mem_singleton] at hi; subst hi; trivial)
    · cases h
  | trunc m n =>
    rcases args with ⟨x, ⟨⟩⟩; dsimp only [lowerOpCode, Except.bind] at h
    cases hwn : Width.ofBits? n with
    | none => rw [hwn] at h; cases h
    | some w =>
      rw [hwn] at h; dsimp only at h
      split at h
      · cases h1 : loadArgToGpr b sb d b.w1 x <;> rw [h1] at h; · cases h
        cases h
        exact isNoRa_mem_append (isNoRa_loadArgToGpr b hwk.2.2.1 h1)
          (isNoRa_emitToLoc b _ fun rd hrd i hi => by
            simp only [List.mem_singleton] at hi; subst hi
            rcases hrd with rfl | hl
            · exact hwk.2.1
            · exact locOf_gpr_mem_allRegs b sb d hl)
      · cases h
  | ofBool n =>
    rcases args with ⟨x, ⟨⟩⟩; dsimp only [lowerOpCode, Except.bind] at h; split at h
    · cases h1 : loadArgToGpr b sb d b.w1 x <;> rw [h1] at h; · cases h
      cases h
      exact isNoRa_mem_append (isNoRa_loadArgToGpr b hwk.2.2.1 h1)
        (isNoRa_emitToLoc b _ fun rd hrd i hi => by
          simp only [List.mem_singleton] at hi; subst hi
          rcases hrd with rfl | hl
          · exact hwk.2.1
          · exact locOf_gpr_mem_allRegs b sb d hl)
    · cases h
  | ternlog _ _ | rotl _ | rotr _ | fshl _ | fshr _ | bswap _ | clz _ | cls _ | rbit _
  | ctz _ | popcnt _ | blend _ _ _ | addc _ | subb _ | umulw _ | smulw _ | udiv _ | sdiv _
  | urem _ | srem _ | udiv0 _ | sdiv0 _ | mkpair _ _ | unpair _ _ | bitcast _ _ _ | shufd _ _
  | shufb _ | alignr _ _ | blendw _ _ | sha256rnds2 | sha256msg1 | sha256msg2 | fadd _ | fsub _
  | fmul _ | fdiv _ | ffma _ | fsqrt _ | fneg _ | fabs _ | fcmp _ _ _ _ | fptoui _ _ | fptosi _ _
  | uitofp _ _ | sitofp _ _ | fcvt _ _ =>
    dsimp only [lowerOpCode] at h; cases h

theorem isNoRa_lowerMemLoad {A : Arch} (b : WordRegBind A) {sb d : Nat} {t : Ty}
    {a : Arg K i64} {is : List (Instr A)} (h : lowerMemLoad b sb d t a = .ok is) :
    ∀ i ∈ is, IsNoRaInstr b i := by
  dsimp only [lowerMemLoad, Except.bind] at h
  cases hw : tyToWidth? t with
  | none => rw [hw] at h; cases h
  | some w =>
    rw [hw] at h; dsimp only at h
    cases h1 : loadArgToGpr b sb d b.w1 a <;> rw [h1] at h; · cases h
    cases h
    have hwk := work_mem_allRegs b
    refine isNoRa_mem_append (isNoRa_loadArgToGpr b hwk.2.2.1 h1)
      (isNoRa_emitToLoc b _ fun rd hrd i hi => ?_)
    simp only [List.mem_singleton] at hi; subst hi
    rcases hrd with rfl | hl
    · exact hwk.2.1
    · exact locOf_gpr_mem_allRegs b sb d hl

theorem isNoRa_lowerMemStore {A : Arch} (b : WordRegBind A) {sb d : Nat} {t : Ty}
    {v : Arg K t} {a : Arg K i64} {is : List (Instr A)} (h : lowerMemStore b sb d v a = .ok is) :
    ∀ i ∈ is, IsNoRaInstr b i := by
  dsimp only [lowerMemStore, Except.bind] at h
  cases hw : tyToWidth? t with
  | none => rw [hw] at h; cases h
  | some w =>
    rw [hw] at h; dsimp only at h
    cases h1 : loadArgToGpr b sb d b.w1 v <;> rw [h1] at h; · cases h
    cases h2 : loadArgToGpr b sb d b.w2 a <;> rw [h2] at h; · cases h
    cases h
    have hwk := work_mem_allRegs b
    exact isNoRa_mem_append (isNoRa_mem_append (isNoRa_loadArgToGpr b hwk.2.2.1 h1)
      (isNoRa_loadArgToGpr b hwk.2.2.2 h2))
      (fun i hi => by simp only [List.mem_singleton] at hi; subst hi; trivial)

theorem isNoRa_slotLd {A : Arch} (b : WordRegBind A) {rd : A.Reg} (k : Nat)
    (hrd : rd ∈ b.allRegs) : IsNoRaInstr b (.slotLd rd k) := hrd

theorem isNoRa_slotSt {A : Arch} (b : WordRegBind A) (k : Nat) (rs : A.Reg) :
    IsNoRaInstr b (.slotSt k rs) := trivial

private theorem isNoRa_emitPrivFrameInitAux {A : Arch} (b : WordRegBind A) (nPriv k : Nat) :
    ∀ i ∈ emitPrivFrameInitAux b nPriv k, IsNoRaInstr b i := by
  have hwk := work_mem_allRegs b
  unfold emitPrivFrameInitAux
  split
  · intro i hi
    rcases List.mem_append.mp hi with h1 | h2
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      rcases h1 with rfl | rfl | rfl
      · exact hwk.2.1
      · exact hwk.2.1
      · trivial
    · exact isNoRa_emitPrivFrameInitAux b nPriv (k + 1) i h2
  · intro _ hi; cases hi
termination_by nPriv - k

theorem isNoRa_emitPrivFrameInit {A : Arch} (b : WordRegBind A) (nPriv : Nat) :
    ∀ i ∈ emitPrivFrameInit b nPriv, IsNoRaInstr b i := by
  intro i hi
  dsimp only [emitPrivFrameInit] at hi
  split at hi
  · cases hi
  · rcases List.mem_cons.mp hi with rfl | hrest
    · trivial
    · exact isNoRa_emitPrivFrameInitAux b nPriv 0 i hrest

private theorem isNoRa_emitPrivFlushAux {A : Arch} (b : WordRegBind A) (nPriv k : Nat) :
    ∀ i ∈ emitPrivFlushAux b nPriv k, IsNoRaInstr b i := by
  have hwk := work_mem_allRegs b
  unfold emitPrivFlushAux
  split
  · intro i hi
    rcases List.mem_append.mp hi with h1 | h2
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      rcases h1 with rfl | rfl | rfl
      · exact hwk.2.2.2
      · exact hwk.2.2.1
      · trivial
    · exact isNoRa_emitPrivFlushAux b nPriv (k + 1) i h2
  · intro _ hi; cases hi
termination_by nPriv - k

theorem isNoRa_emitPrivFlush {A : Arch} (b : WordRegBind A) (nPriv : Nat) :
    ∀ i ∈ emitPrivFlush b nPriv, IsNoRaInstr b i := by
  have hwk := work_mem_allRegs b
  intro i hi
  dsimp only [emitPrivFlush] at hi
  split at hi
  · cases hi
  · rcases List.mem_cons.mp hi with rfl | hrest
    · exact hwk.2.2.1
    · exact isNoRa_emitPrivFlushAux b nPriv 0 i hrest

theorem isNoRa_emitDynAliasGuard {A : Arch} (b : WordRegBind A)
    {sb d nPriv bytes : Nat} {a : Arg K i64} {cg : List (Instr A)}
    (h : emitDynAliasGuard b sb d nPriv bytes a = .ok cg) :
    ∀ i ∈ cg, IsNoRaInstr b i := by
  dsimp only [emitDynAliasGuard] at h
  cases hge : b.condOfCmp? .uge <;> rw [hge] at h; · cases h
  cases hle : b.condOfCmp? .ule <;> rw [hle] at h; · cases h
  dsimp only [Except.bind] at h
  cases hca : loadArgInto b sb d b.w0 a <;> rw [hca] at h; · cases h
  cases h
  have hwk := work_mem_allRegs b
  refine isNoRa_mem_append (isNoRa_loadArgInto b hwk.2.1 hca) (fun i hi => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hwk.2.2.1
  · exact hwk.2.2.1
  · exact hwk.2.1
  · trivial
  · exact hwk.2.2.1
  · trivial
  · exact hwk.2.2.2
  · exact hwk.2.1

theorem lowerOp_ts_length {A : Arch} {b : WordRegBind A} {sb d d' : Nat}
    {ts : List Ty} {op : Op K ts} {is : List (Instr A)}
    (h : lowerOp b sb d op = .ok (is, d')) : ts.length = 1 := by
  rcases op with ⟨code, args⟩
  dsimp only [lowerOp] at h
  cases code with
  | copy t => rcases args with ⟨_, ⟨⟩⟩; rfl
  | neg t | not t => rcases args with ⟨_, ⟨⟩⟩; rfl
  | add t | sub t | mul t | and t | or t | xor t | shl t | lshr t | ashr t =>
    rcases args with ⟨_, _, ⟨⟩⟩; rfl
  | cmp _ t _ hm => subst hm; rcases args with ⟨_, _, ⟨⟩⟩; rfl
  | select t => rcases args with ⟨_, _, _, ⟨⟩⟩; rfl
  | zext _ _ | sext _ _ | trunc _ _ | ofBool _ => rcases args with ⟨_, ⟨⟩⟩; rfl
  | ternlog _ _ | rotl _ | rotr _ | fshl _ | fshr _ | bswap _ | clz _ | cls _ | rbit _
  | ctz _ | popcnt _ | blend _ _ _ | addc _ | subb _ | umulw _ | smulw _ | udiv _ | sdiv _
  | urem _ | srem _ | udiv0 _ | sdiv0 _ | mkpair _ _ | unpair _ _ | bitcast _ _ _ | shufd _ _
  | shufb _ | alignr _ _ | blendw _ _ | sha256rnds2 | sha256msg1 | sha256msg2 | fadd _ | fsub _
  | fmul _ | fdiv _ | ffma _ | fsqrt _ | fneg _ | fabs _ | fcmp _ _ _ _ | fptoui _ _ | fptosi _ _
  | uitofp _ _ | sitofp _ _ | fcvt _ _ =>
    dsimp only [lowerOpCode] at h; cases h

theorem lowerM_bind_ok' {α β : Type} {m : LowerM α} {f : α → LowerM β} {s0 s1 : Nat} {r : β}
    (h : (m >>= f).run s0 = .ok (r, s1)) :
    ∃ a sMid, m.run s0 = .ok (a, sMid) ∧ (f a).run sMid = .ok (r, s1) := by
  change Except.bind (m.run s0) (fun p => (f p.1).run p.2) = .ok (r, s1) at h
  cases hm : m.run s0 with
  | error e => rw [hm] at h; cases h
  | ok p => rw [hm] at h; exact ⟨p.1, p.2, rfl, h⟩

theorem closed_bwp {A : Arch} {vcm : VllCodeMap A} (hwf : vcm.Wf)
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    (hcl : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ H)
    {blk : Block A} {s : MachSt A} (hb : blk ∈ vcm.blocks)
    (hbwp : bodyWp A vcm.symAddr blk.body (termWp A vcm.symAddr blk.term Ψ H) Ψ H s) :
    Ψ (vcm.symAddr blk.label) s :=
  hcl (vcm.symAddr blk.label) blk (VllCodeMap.lookupPc_of_wf hwf hb) s (bwp_of_bodyWp hbwp)

theorem bodyWp_imp_raReg {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {P : Prop} {ra : BitVec 64}
    {K : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {is : List (Instr A)} {s : MachSt A}
    (hno : ∀ i ∈ is, IsNoRaInstr b i) (hra : P → (vllFramePreds A).raReg s ra)
    (hwp : bodyWp A symAddr is K Ψ H s) :
    bodyWp A symAddr is (fun s' => K s' ∧ (P → (vllFramePreds A).raReg s' ra)) Ψ H s := by
  by_cases hp : P
  · exact bodyWp_mono (fun s' ⟨hk, hr⟩ => ⟨hk, fun _ => hr⟩)
      (bodyWp_preserve_raReg hwf hno (hra hp) hwp)
  · exact bodyWp_mono (fun s' hk => ⟨hk, fun h => absurd h hp⟩) hwp

theorem raReg_setFlags (A : Arch) (s : MachSt A) (f : A.Flags) (ra : BitVec 64) :
    (vllFramePreds A).raReg (s.setFlags f) ra ↔ (vllFramePreds A).raReg s ra := by
  cases h : A.abi.raKind <;> simp [vllFramePreds, h]

private theorem lowerM_mapM_mem' {α β : Type} (f : α → LowerM (List β)) :
    ∀ (xs : List α) (s0 s1 : Nat) (xss : List (List β)),
      (xs.mapM f).run s0 = .ok (xss, s1) →
      ∀ x ∈ xs, ∃ sA sB ys, (f x).run sA = .ok (ys, sB) ∧ ∀ y ∈ ys, y ∈ xss.flatten
  | [], _, _, _, _, _, hx => by cases hx
  | x :: xs, s0, s1, xss, h, z, hz => by
    rw [List.mapM_cons] at h
    obtain ⟨y0, sMid, hx, h1⟩ := lowerM_bind_ok' h
    obtain ⟨xss', sEnd, hxs, h2⟩ := lowerM_bind_ok' h1
    change Except.ok (y0 :: xss', sEnd) = Except.ok _ at h2
    cases h2
    rcases List.mem_cons.mp hz with rfl | hzTail
    · exact ⟨s0, sMid, y0, hx, fun y hy => List.mem_flatten.mpr ⟨y0, List.mem_cons_self, hy⟩⟩
    · obtain ⟨sA, sB, ys, hfy, hmem⟩ := lowerM_mapM_mem' f xs sMid s1 xss' hxs z hzTail
      exact ⟨sA, sB, ys, hfy, fun y hy => by
        rw [List.flatten_cons]; exact List.mem_append_right _ (hmem y hy)⟩

theorem fromWord_entry_blocks_sub {A : Arch} {b : WordRegBind A} {cm : CodeMap}
    {vcm : VllCodeMap A} (h : fromWord b cm = .ok vcm) {e : CodeEntry} (he : e ∈ cm) :
    ∃ sA sB bs, (lowerPlainEntry b cm e).run sA = .ok (bs, sB) ∧
      ∀ x ∈ bs, x ∈ vcm.blocks := by
  dsimp only [fromWord] at h
  cases hck : cm.checkWf with
  | false => rw [hck] at h; cases h
  | true =>
    rw [hck] at h; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases hrun : (cm.mapM (lowerPlainEntry b cm)).run 0 with
    | error _ =>
      change Except.bind ((cm.mapM (lowerPlainEntry b cm)).run 0) _ = .ok vcm at h
      rw [hrun] at h; cases h
    | ok p =>
      rcases p with ⟨blocksList, sEnd⟩
      change Except.bind ((cm.mapM (lowerPlainEntry b cm)).run 0) _ = .ok vcm at h
      rw [hrun] at h; dsimp only [Except.bind] at h
      obtain ⟨rfl, _, _⟩ := finalizeVllCodeMap_wf h
      exact lowerM_mapM_mem' (lowerPlainEntry b cm) cm 0 sEnd blocksList hrun e he

theorem fromWordContify_contBlock_sub {A : Arch} {b : WordRegBind A} {cm : CodeMap}
    {wit : ContifyWitness} {vcm : VllCodeMap A} (h : fromWordContify b cm wit = .ok vcm)
    {cr : ContifyRegion} (hcr : cr ∈ wit.regions) {pc : BitVec 64} (hpc : pc ∈ cr.allPcs) :
    ∃ ceBlock sA sB bs, cm.lookupAddr pc = some ceBlock ∧
      (lowerContBlock b cm cr pc (regionSpillBase cr) (regionFrameSlots b cm cr)
        (regionNeedFrame b cm cr) (innerLabel cr pc) [] 6 []
        ContSymState.init ceBlock).run sA = .ok (bs, sB) ∧
      ∀ x ∈ bs, x ∈ vcm.blocks := by
  dsimp only [fromWordContify] at h
  cases hck : cm.checkWf with
  | false => rw [hck] at h; cases h
  | true =>
    rw [hck] at h; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hwck : wit.check cm = true
    · rw [hwck] at h; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hr1 : (wit.regions.mapM (lowerContRegion b cm)).run 0 with
      | error _ =>
        change Except.bind ((wit.regions.mapM (lowerContRegion b cm)).run 0) _ = .ok vcm at h
        rw [hr1] at h; cases h
      | ok p1 =>
        rcases p1 with ⟨regBlocksList, st1⟩
        change Except.bind ((wit.regions.mapM (lowerContRegion b cm)).run 0) _ = .ok vcm at h
        rw [hr1] at h; dsimp only [Except.bind] at h
        let wRes := residualContifyCodeMap cm wit
        cases hr2 : (wRes.mapM (lowerPlainEntry b cm)).run st1 with
        | error _ =>
          change Except.bind ((wRes.mapM (lowerPlainEntry b cm)).run st1) _ = .ok vcm at h
          rw [hr2] at h; cases h
        | ok p2 =>
          rcases p2 with ⟨resBlocksList, st2⟩
          change Except.bind ((wRes.mapM (lowerPlainEntry b cm)).run st1) _ = .ok vcm at h
          rw [hr2] at h; dsimp only [Except.bind] at h
          obtain ⟨rfl, _, _⟩ := finalizeVllCodeMap_wf h
          obtain ⟨sA, sB, rbs, hregRun, hsub⟩ :=
            lowerM_mapM_mem' (lowerContRegion b cm) wit.regions 0 st1 regBlocksList hr1 cr hcr
          dsimp only [lowerContRegion] at hregRun
          obtain ⟨innerLists, sMid, hInners, hrest⟩ := lowerM_bind_ok' hregRun
          change StateT.pure _ sMid = Except.ok _ at hrest; cases hrest
          obtain ⟨sA', sB', bs, hpcRun, hpcSub⟩ :=
            lowerM_mapM_mem' (fun pc => do
              let some ceBlock := cm.lookupAddr pc
                | liftEx (.error s!"FromWord: missing pc {pc}")
              lowerContBlock b cm cr pc (regionSpillBase cr) (regionFrameSlots b cm cr)
                (regionNeedFrame b cm cr) (innerLabel cr pc) [] 6 []
                ContSymState.init ceBlock) cr.allPcs sA sB innerLists hInners pc hpc
          cases hlu : cm.lookupAddr pc with
          | none => rw [hlu] at hpcRun; dsimp only [liftEx, StateT.lift] at hpcRun; cases hpcRun
          | some ceBlock =>
            rw [hlu] at hpcRun
            exact ⟨ceBlock, sA', sB', bs, rfl, hpcRun, fun x hx =>
              List.mem_append_left _ (hsub x (List.mem_cons_of_mem _ (hpcSub x hx)))⟩
    · have hwfF : wit.check cm = false := Bool.eq_false_iff.mpr hwck
      rw [hwfF] at h; dsimp only [Bool.not_false, ↓reduceIte, Bind.bind, Except.bind] at h
      cases h

theorem fromWordContify_plainEntry_sub {A : Arch} {b : WordRegBind A} {cm : CodeMap}
    {wit : ContifyWitness} {vcm : VllCodeMap A} (h : fromWordContify b cm wit = .ok vcm)
    {e : CodeEntry} (he : e ∈ residualContifyCodeMap cm wit) :
    ∃ sA sB bs, (lowerPlainEntry b cm e).run sA = .ok (bs, sB) ∧
      ∀ x ∈ bs, x ∈ vcm.blocks := by
  dsimp only [fromWordContify] at h
  cases hck : cm.checkWf with
  | false => rw [hck] at h; cases h
  | true =>
    rw [hck] at h; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hwck : wit.check cm = true
    · rw [hwck] at h; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hr1 : (wit.regions.mapM (lowerContRegion b cm)).run 0 with
      | error _ =>
        change Except.bind ((wit.regions.mapM (lowerContRegion b cm)).run 0) _ = .ok vcm at h
        rw [hr1] at h; cases h
      | ok p1 =>
        rcases p1 with ⟨regBlocksList, st1⟩
        change Except.bind ((wit.regions.mapM (lowerContRegion b cm)).run 0) _ = .ok vcm at h
        rw [hr1] at h; dsimp only [Except.bind] at h
        let wRes := residualContifyCodeMap cm wit
        cases hr2 : (wRes.mapM (lowerPlainEntry b cm)).run st1 with
        | error _ =>
          change Except.bind ((wRes.mapM (lowerPlainEntry b cm)).run st1) _ = .ok vcm at h
          rw [hr2] at h; cases h
        | ok p2 =>
          rcases p2 with ⟨resBlocksList, st2⟩
          change Except.bind ((wRes.mapM (lowerPlainEntry b cm)).run st1) _ = .ok vcm at h
          rw [hr2] at h; dsimp only [Except.bind] at h
          obtain ⟨rfl, _, _⟩ := finalizeVllCodeMap_wf h
          obtain ⟨sA, sB, bs, hbe, hsub⟩ :=
            lowerM_mapM_mem' (lowerPlainEntry b cm) wRes st1 st2 resBlocksList hr2 e he
          exact ⟨sA, sB, bs, hbe, fun x hx => List.mem_append_right _ (hsub x hx)⟩
    · have hwfF : wit.check cm = false := Bool.eq_false_iff.mpr hwck
      rw [hwfF] at h; dsimp only [Bool.not_false, ↓reduceIte, Bind.bind, Except.bind] at h
      cases h

theorem pushLabelPcs_mem {ps acc : List (BitVec 64)} {x : BitVec 64} :
    x ∈ pushLabelPcs ps acc ↔ x ∈ ps ∨ x ∈ acc := by
  induction ps generalizing acc with
  | nil => simp [pushLabelPcs]
  | cons p ps ih =>
    dsimp only [pushLabelPcs]; rw [ih, List.mem_cons, List.mem_cons]
    constructor
    · rintro (h | rfl | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr h
    · rintro ((rfl | h) | h)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

theorem mem_of_findLabelIdx {pcs : List (BitVec 64)} {t : BitVec 64} {idx : Nat}
    (h : findLabelIdx pcs t = some idx) : t ∈ pcs := by
  induction pcs generalizing idx with
  | nil => cases h
  | cons p ps ih =>
    dsimp only [findLabelIdx] at h
    by_cases he : p = t
    · subst he; exact List.mem_cons_self
    · rw [ite_eq_right (by simp [he])] at h
      cases h' : findLabelIdx ps t with
      | none => rw [h'] at h; cases h
      | some _ => exact List.mem_cons_of_mem _ (ih h')

theorem checkStrideTargets_spec {pcs : List (BitVec 64)} {base : BitVec 64} :
    ∀ {idx : Nat} {targets : List (BitVec 64)},
      checkStrideTargets pcs base idx targets = true →
      ∀ k < targets.length, ∃ tPc, targets[k]? = some tPc ∧
        tPc = base + BitVec.ofNat 64 (8 * (idx + k)) ∧ (findLabelIdx pcs tPc).isSome = true
  | _, [], _, k, hk => absurd hk (Nat.not_lt_zero _)
  | idx, t :: ts, hchk, k, hk => by
    dsimp only [checkStrideTargets] at hchk
    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
    cases k with
    | zero => exact ⟨t, rfl, by simpa using hchk.1.1, hchk.1.2⟩
    | succ k' =>
      obtain ⟨tPc, ht, heq, his⟩ :=
        checkStrideTargets_spec (idx := idx + 1) hchk.2 k' (Nat.lt_of_succ_lt_succ hk)
      exact ⟨tPc, ht, by rw [show idx + (k' + 1) = idx + 1 + k' by omega]; exact heq, his⟩

mutual
private def gtSize : GroupTree → Nat
  | .leaf _ => 1
  | .loop _ nodes => 1 + gtListSize nodes

private def gtListSize : List GroupTree → Nat
  | [] => 0
  | g :: gs => gtSize g + gtListSize gs
end

theorem checkContGroupNodes_leaf_prop {cm : CodeMap} {cr : ContifyRegion}
    {callees : List ContCalleeMeta} :
    ∀ {gs : List GroupTree} {pcsOuter : List (BitVec 64)},
      checkContGroupNodes cm cr callees pcsOuter gs = true →
      (∀ p ∈ pcsOuter, p ∈ cr.allPcs) →
      (∀ g ∈ gs, ∀ p ∈ g.allPcs, p ∈ cr.allPcs) →
      ∀ {pc : BitVec 64}, pc ∈ gs.flatMap GroupTree.allPcs →
        ∃ pcsInner, (∀ p ∈ pcsInner, p ∈ cr.allPcs) ∧
          checkContBlockLeaves cm cr callees pcsInner pc = true
  | [], _, _, _, _, _, hpc => by cases hpc
  | .leaf pc0 :: gs, pcsOuter, hchk, hpOut, hgSub, pc, hpc => by
    dsimp only [checkContGroupNodes] at hchk
    rcases Bool.and_eq_true_iff.mp hchk with ⟨hgChk, hgsChk⟩
    rw [List.flatMap_cons, List.mem_append] at hpc
    rcases hpc with hpG | hpGs
    · simp only [GroupTree.allPcs, List.mem_singleton] at hpG; subst hpG
      exact ⟨pcsOuter, hpOut, hgChk⟩
    · exact checkContGroupNodes_leaf_prop hgsChk hpOut
        (fun x hx => hgSub x (List.mem_cons_of_mem _ hx)) hpGs
  | .loop header nodes :: gs, pcsOuter, hchk, hpOut, hgSub, pc, hpc => by
    dsimp only [checkContGroupNodes] at hchk
    rcases Bool.and_eq_true_iff.mp hchk with ⟨hgChk, hgsChk⟩
    rw [List.flatMap_cons, List.mem_append] at hpc
    rcases hpc with hpG | hpGs
    · dsimp only [checkContGroupNode] at hgChk
      simp only [Bool.and_eq_true] at hgChk
      let pcsInner := pushLabelPcs (nodes.map GroupTree.entryPc) pcsOuter
      have hpIn : ∀ p ∈ pcsInner, p ∈ cr.allPcs := by
        intro p hp
        rcases pushLabelPcs_mem.mp hp with hpEnt | hpO
        · obtain ⟨c, hcMem, rfl⟩ := List.mem_map.mp hpEnt
          have hcChk := checkContGroupNodes_forall cm cr callees _ nodes hgChk.2 c hcMem
          have hcEnt := checkContGroupNode_entryPc_mem cm cr callees _ c hcChk
          exact hgSub (.loop header nodes) List.mem_cons_self _
            (by simpa [GroupTree.allPcs] using List.mem_flatMap.mpr ⟨c, hcMem, hcEnt⟩)
        · exact hpOut p hpO
      have hnodeSub : ∀ c ∈ nodes, ∀ p ∈ c.allPcs, p ∈ cr.allPcs := fun c hc p hp =>
        hgSub (.loop header nodes) List.mem_cons_self p
          (by simpa [GroupTree.allPcs] using List.mem_flatMap.mpr ⟨c, hc, hp⟩)
      exact checkContGroupNodes_leaf_prop hgChk.2 hpIn hnodeSub
        (by simpa [GroupTree.allPcs] using hpG)
    · exact checkContGroupNodes_leaf_prop hgsChk hpOut
        (fun x hx => hgSub x (List.mem_cons_of_mem _ hx)) hpGs
termination_by gs => gtListSize gs
decreasing_by
  · simp only [gtListSize, gtSize]; omega
  · simp only [gtListSize, gtSize]; omega
  · simp only [gtListSize, gtSize]; omega

theorem checkContRegion_allPcs_leaf {cm : CodeMap} {cr : ContifyRegion}
    {callees : List ContCalleeMeta} (hchk : cr.check cm callees = true)
    {pc : BitVec 64} (hpc : pc ∈ cr.allPcs) :
    ∃ pcsInner, (∀ p ∈ pcsInner, p ∈ cr.allPcs) ∧
      checkContBlockLeaves cm cr callees pcsInner pc = true := by
  simp only [ContifyRegion.check, Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hGrpChk⟩, _⟩, _⟩
  have hpOut : ∀ p ∈ pushLabelPcs (cr.tree.map GroupTree.entryPc) [], p ∈ cr.allPcs := by
    intro p hp
    rcases pushLabelPcs_mem.mp hp with hpE | hpNil
    · obtain ⟨g, hgMem, rfl⟩ := List.mem_map.mp hpE
      have hgChk := checkContGroupNodes_forall cm cr callees _ cr.tree hGrpChk g hgMem
      exact List.mem_flatMap.mpr
        ⟨g, hgMem, checkContGroupNode_entryPc_mem cm cr callees _ g hgChk⟩
    · cases hpNil
  exact checkContGroupNodes_leaf_prop hGrpChk hpOut
    (fun g hg p hp => List.mem_flatMap.mpr ⟨g, hg, hp⟩) hpc

def foldCallees (cm : CodeMap) (acc : List ContCalleeMeta) :
    List ContifyRegion → List ContCalleeMeta
  | [] => acc
  | cr :: crs =>
    let acc' := match cr.toCalleeMeta? cm acc with
      | some c => c :: acc
      | none => acc
    foldCallees cm acc' crs

theorem foldl_toCalleeMeta_eq (cm : CodeMap) :
    ∀ (pre : List ContifyRegion) (acc : List ContCalleeMeta),
      pre.foldl (fun a r => match r.toCalleeMeta? cm a with | some c => c :: a | none => a) acc =
        foldCallees cm acc pre
  | [], _ => rfl
  | r :: rest, acc => by
    dsimp only [List.foldl, foldCallees]
    cases r.toCalleeMeta? cm acc <;> exact foldl_toCalleeMeta_eq cm rest _

private theorem checkAux_append (cm : CodeMap) :
    ∀ (pre post : List ContifyRegion) (acc : List ContCalleeMeta),
      ContifyWitness.checkAux cm acc (pre ++ post) = true →
      ContifyWitness.checkAux cm (foldCallees cm acc pre) post = true
  | [], _, _, h => h
  | cr :: pre, post, acc, h => by
    dsimp only [List.cons_append, ContifyWitness.checkAux] at h
    rcases Bool.and_eq_true_iff.mp h with ⟨_, hrest⟩
    exact checkAux_append cm pre post _ hrest

theorem mem_foldCallees (cm : CodeMap) :
    ∀ (pre : List ContifyRegion) (c : ContCalleeMeta) (aBase : List ContCalleeMeta),
      c ∈ foldCallees cm aBase pre →
      c ∈ aBase ∨
        ∃ p1 p2 cr_c, pre = p1 ++ cr_c :: p2 ∧
          cr_c.toCalleeMeta? cm (foldCallees cm aBase p1) = some c
  | [], c, aBase, h => Or.inl h
  | cr :: pre, c, aBase, h => by
    dsimp only [foldCallees] at h
    cases ht : cr.toCalleeMeta? cm aBase with
    | none =>
      rw [ht] at h
      rcases mem_foldCallees cm pre c aBase h with ha | ⟨p1, p2, cr_c, rfl, hto⟩
      · exact Or.inl ha
      · exact Or.inr ⟨cr :: p1, p2, cr_c, rfl, by simpa [foldCallees, ht] using hto⟩
    | some c0 =>
      rw [ht] at h
      rcases mem_foldCallees cm pre c (c0 :: aBase) h with hc | ⟨p1, p2, cr_c, rfl, hto⟩
      · rcases List.mem_cons.mp hc with rfl | ha
        · exact Or.inr ⟨[], pre, cr, rfl, ht⟩
        · exact Or.inl ha
      · exact Or.inr ⟨cr :: p1, p2, cr_c, rfl, by simpa [foldCallees, ht] using hto⟩

theorem witness_checkAux_split {cm : CodeMap} {wit : ContifyWitness} (hw : wit.check cm = true)
    {pre : List ContifyRegion} {cr : ContifyRegion} {post : List ContifyRegion}
    (hs : wit.regions = pre ++ cr :: post) :
    cr.check cm (foldCallees cm [] pre) = true := by
  dsimp only [ContifyWitness.check] at hw
  simp only [Bool.and_eq_true] at hw
  have h1 := checkAux_append cm pre (cr :: post) [] (hs ▸ hw.2)
  exact (Bool.and_eq_true_iff.mp h1).1

theorem lowerOp_d_eq {A : Arch} {b : WordRegBind A} {sb d d' : Nat}
    {ts : List Ty} {op : Op K ts} {is : List (Instr A)}
    (h : lowerOp b sb d op = .ok (is, d')) : d' = d + ts.length := by
  rcases op with ⟨code, args⟩
  dsimp only [lowerOp] at h
  cases code with
  | copy t =>
    rcases args with ⟨_, ⟨⟩⟩; cases t with
    | bool =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases h1 : loadArgToGpr b sb d b.w1 _ <;> rw [h1] at h; · cases h
      cases h; rfl
    | bits n =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases hw : Width.ofBits? n <;> simp [hw] at h
      cases h1 : loadArgToGpr b sb d b.w1 _ <;> rw [h1] at h; · cases h
      cases h; rfl
    | float _ | pair _ _ => cases h
  | neg t =>
    rcases args with ⟨_, ⟨⟩⟩; cases t with
    | bool =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases h1 : loadArgToGpr b sb d b.w1 _ <;> rw [h1] at h; · cases h
      cases h; rfl
    | bits n =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases hw : Width.ofBits? n <;> simp [hw] at h
      cases h1 : loadArgToGpr b sb d b.w2 _ <;> rw [h1] at h; · cases h
      cases h; rfl
    | float _ | pair _ _ => cases h
  | not t =>
    rcases args with ⟨_, ⟨⟩⟩; cases t with
    | bool =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases h1 : loadArgToGpr b sb d b.w1 _ <;> rw [h1] at h; · cases h
      cases h; rfl
    | bits n =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases hw : Width.ofBits? n <;> simp [hw] at h
      cases h1 : loadArgToGpr b sb d b.w1 _ <;> rw [h1] at h; · cases h
      cases h; rfl
    | float _ | pair _ _ => cases h
  | add t | sub t | mul t | and t | or t | xor t =>
    rcases args with ⟨_, _, ⟨⟩⟩; cases t with
    | bool =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases hb : lowerBinBits b sb d (locOf b sb d) _ .w8 _ _ <;> rw [hb] at h; · cases h
      cases h; rfl
    | bits n =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases hw : Width.ofBits? n <;> simp [hw] at h
      cases hb : lowerBinBits b sb d (locOf b sb d) _ _ _ _ <;> rw [hb] at h; · cases h
      cases h; rfl
    | float _ | pair _ _ => cases h
  | shl t | lshr t | ashr t =>
    rcases args with ⟨_, _, ⟨⟩⟩; cases t with
    | bits n =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases hw : Width.ofBits? n <;> simp [hw] at h
      cases hb : lowerBinBits b sb d (locOf b sb d) _ _ _ _ <;> rw [hb] at h; · cases h
      cases h; rfl
    | bool | float _ | pair _ _ => cases h
  | cmp _ t _ hm =>
    subst hm; rcases args with ⟨_, _, ⟨⟩⟩; cases t with
    | bool =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases hc : lowerCmpBits b sb d (locOf b sb d) _ .w8 _ _ <;> rw [hc] at h; · cases h
      cases h; rfl
    | bits n =>
      dsimp only [lowerOpCode, Except.bind] at h
      cases hw : Width.ofBits? n <;> simp [hw] at h
      cases hc : lowerCmpBits b sb d (locOf b sb d) _ _ _ _ <;> rw [hc] at h; · cases h
      cases h; rfl
    | float _ | pair _ _ => cases h
  | select _ =>
    rcases args with ⟨_, _, _, ⟨⟩⟩; dsimp only [lowerOpCode, Except.bind] at h; split at h
    · cases hs : lowerSelect b sb d (locOf b sb d) _ _ _ <;> rw [hs] at h; · cases h
      cases h; rfl
    · cases h
  | zext _ _ =>
    rcases args with ⟨_, ⟨⟩⟩; dsimp only [lowerOpCode, Except.bind] at h; split at h
    · cases h1 : loadArgToGpr b sb d b.w1 _ <;> rw [h1] at h; · cases h
      cases h; rfl
    · cases h
  | sext _ _ =>
    rcases args with ⟨_, ⟨⟩⟩; dsimp only [lowerOpCode, Except.bind] at h; split at h
    · cases h1 : loadArgInto b sb d b.w1 _ <;> rw [h1] at h; · cases h
      cases h; rfl
    · cases h
  | trunc _ n =>
    rcases args with ⟨_, ⟨⟩⟩; dsimp only [lowerOpCode, Except.bind] at h
    cases hwn : Width.ofBits? n <;> simp [hwn] at h
    split at h
    · cases h1 : loadArgToGpr b sb d b.w1 _ <;> rw [h1] at h; · cases h
      cases h; rfl
    · cases h
  | ofBool _ =>
    rcases args with ⟨_, ⟨⟩⟩; dsimp only [lowerOpCode, Except.bind] at h; split at h
    · cases h1 : loadArgToGpr b sb d b.w1 _ <;> rw [h1] at h; · cases h
      cases h; rfl
    · cases h
  | ternlog _ _ | rotl _ | rotr _ | fshl _ | fshr _ | bswap _ | clz _ | cls _ | rbit _
  | ctz _ | popcnt _ | blend _ _ _ | addc _ | subb _ | umulw _ | smulw _ | udiv _ | sdiv _
  | urem _ | srem _ | udiv0 _ | sdiv0 _ | mkpair _ _ | unpair _ _ | bitcast _ _ _ | shufd _ _
  | shufb _ | alignr _ _ | blendw _ _ | sha256rnds2 | sha256msg1 | sha256msg2 | fadd _ | fsub _
  | fmul _ | fdiv _ | ffma _ | fsqrt _ | fneg _ | fabs _ | fcmp _ _ _ _ | fptoui _ _ | fptosi _ _
  | uitofp _ _ | sitofp _ _ | fcvt _ _ =>
    dsimp only [lowerOpCode] at h; cases h

theorem lowerCodeAddr_bodyWp {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {vcm : VllCodeMap A} {sb d dMax : Nat} {sym : Sym} {a : BitVec 64}
    {bvs : List ((t : Ty) × Val t)} {rw : Regs} {slots : List (BitVec 64)}
    {G : Mem 64 → Prop} {s : MachSt A} {P : Prop} {ra₀ : BitVec 64}
    {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    {Kpost : MachSt A → Prop}
    (hd : d < dMax) (h6 : 6 ≤ d) (hbound : sb + tempSpillCount b dMax ≤ slots.length)
    (ha : vcm.symAddr sym = a)
    (he : EnvRel b sb d bvs s) (hr : WordRegsRel b rw s)
    (hra : P → (vllFramePreds A).raReg s ra₀)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ G) s.mem)
    (hk : ∀ s' (slots' : List (BitVec 64)),
      slots'.length = slots.length → (∀ j < sb, slots'[j]? = slots[j]?) →
      EnvRel b sb (d + 1) (⟨i64, a⟩ :: bvs) s' → WordRegsRel b rw s' →
      (P → (vllFramePreds A).raReg s' ra₀) → s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (array64 (s'.gpr A.abi.sp) slots' ⋆ G) s'.mem → Kpost s') :
    bodyWp A vcm.symAddr
      (emitToLoc b.w0 (locOf b sb d) fun rd => [.symAddr sym rd]) Kpost Ψ_L1 H_L1 s := by
  have hwk := w_mem_workRegs b; have hwsp := work_not_sp hwf
  have hno : ∀ i ∈ emitToLoc b.w0 (locOf b sb d) fun rd => [.symAddr sym rd], IsNoRaInstr b i := by
    refine isNoRa_emitToLoc b _ fun rd hrd i hi => ?_
    simp only [List.mem_singleton] at hi; subst hi
    rcases hrd with rfl | hl
    · exact (work_mem_allRegs b).2.1
    · exact locOf_gpr_mem_allRegs b sb d hl
  have hva : ∀ g, g = a → ValHolds64 i64 a g := fun g hg =>
    ⟨by decide, by simp [hg]⟩
  have hcore : bodyWp A vcm.symAddr
      (emitToLoc b.w0 (locOf b sb d) fun rd => [.symAddr sym rd])
      (fun s' => ∃ slots' : List (BitVec 64),
        slots'.length = slots.length ∧ (∀ j < sb, slots'[j]? = slots[j]?) ∧
        EnvRel b sb (d + 1) (⟨i64, a⟩ :: bvs) s' ∧ WordRegsRel b rw s' ∧
        s'.gpr A.abi.sp = s.gpr A.abi.sp ∧ (array64 (s'.gpr A.abi.sp) slots' ⋆ G) s'.mem)
      Ψ_L1 H_L1 s := by
    refine emitToLoc_bodyWp hwf hd hbound (fun rd hloc => ?_) (fun _ _ => ?_)
      (fun s' slots' hlen hsb he' hr' hsp' hm' => ⟨slots', hlen, hsb, he', hr', hsp', hm'⟩)
    · refine instrWp_symAddr ?_
      have hsp' : (s.setGpr rd (vcm.symAddr sym)).gpr A.abi.sp = s.gpr A.abi.sp :=
        MachSt.gpr_setGpr_ne _ _ (locOf_gpr_ne_sp hwf sb d hloc).symm
      exact ⟨hva _ (by rw [MachSt.gpr_setGpr_same, ha]), hsp',
        envRel_setGpr_new hwf hloc _ he,
        wordRegsRel_upd_ge6' hwf hr h6 hloc (fun q hq => MachSt.gpr_setGpr_ne _ _ hq),
        slots, rfl, fun _ _ => rfl, by simpa [hsp'] using hm⟩
    · refine instrWp_symAddr ?_
      have hsp' : (s.setGpr b.w0 (vcm.symAddr sym)).gpr A.abi.sp = s.gpr A.abi.sp :=
        MachSt.gpr_setGpr_ne _ _ hwsp.2.1.symm
      exact ⟨hva _ (by rw [MachSt.gpr_setGpr_same, ha]), hsp',
        (envRel_setGpr_work hwf sb d bvs s hwk.1 _).mpr he,
        wordRegsRel_updWork hwf hr b.w0 hwk.1 (fun q hq => MachSt.gpr_setGpr_ne _ _ hq),
        slots, rfl, fun _ _ => rfl, by simpa [hsp'] using hm⟩
  exact bodyWp_mono (fun s' ⟨⟨slots', hlen, hsb, he', hr', hsp', hm'⟩, hra'⟩ =>
      hk s' slots' hlen hsb he' hr' hra' hsp' hm')
    (bodyWp_imp_raReg hwf hno hra hcore)

/-! ## §2. Open `lowerPlainBody` Simulation (`lowerPlainBody_bwp`) -/

private theorem bodyWp_imp_raReg_cont {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {P : Prop} {ra₀ : BitVec 64} {is : List (Instr A)}
    {Kpost : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {s : MachSt A} (hno : ∀ i ∈ is, IsNoRaInstr b i) (hra : P → (vllFramePreds A).raReg s ra₀)
    (hwp : bodyWp A symAddr is (fun s' => (P → (vllFramePreds A).raReg s' ra₀) → Kpost s') Ψ H s) :
    bodyWp A symAddr is Kpost Ψ H s :=
  bodyWp_mono (fun _ ⟨hk, hra'⟩ => hk hra') (bodyWp_imp_raReg hwf hno hra hwp)

private theorem bodyWp_imp_raReg_mono {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {P : Prop} {ra₀ : BitVec 64} {is : List (Instr A)}
    {K₁ K₂ : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {s : MachSt A} (hno : ∀ i ∈ is, IsNoRaInstr b i) (hra : P → (vllFramePreds A).raReg s ra₀)
    (hwp : bodyWp A symAddr is K₁ Ψ H s)
    (hmono : ∀ s', K₁ s' → (P → (vllFramePreds A).raReg s' ra₀) → K₂ s') :
    bodyWp A symAddr is K₂ Ψ H s :=
  bodyWp_mono (fun s' ⟨hk, hra'⟩ => hmono s' hk hra') (bodyWp_imp_raReg hwf hno hra hwp)

private theorem lowerPlainBody_head_shape {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (auxPfx : Sym) (frameSlots? : Option Nat) :
    ∀ (blk : BlockFlat) (curLbl : Sym) (pad? : Option PadKind) (acc : List (Instr A)) (d : Nat)
      {s0 s1 : Nat} {bs : List (Block A)},
      (lowerPlainBody b cm auxPfx frameSlots? curLbl pad? acc d blk).run s0 = .ok (bs, s1) →
      ∃ blk0 rest bodyTail, bs = blk0 :: rest ∧ blk0.label = curLbl ∧ blk0.pad? = pad? ∧
        blk0.body = acc ++ bodyTail
  | .let_ _ k, l, p, acc, d, _, _, _, h => by
    dsimp only [lowerPlainBody] at h
    obtain ⟨p', sMid, _, hk⟩ := lowerM_bind_ok' h
    obtain ⟨blk0, rest, tail, rfl, hlbl, hpad, hbody⟩ :=
      lowerPlainBody_head_shape b cm auxPfx frameSlots? k l p _ _ hk
    exact ⟨blk0, rest, p'.1 ++ tail, rfl, hlbl, hpad, by simpa [List.append_assoc] using hbody⟩
  | .load _ _ k, l, p, acc, d, _, _, _, h => by
    dsimp only [lowerPlainBody] at h
    obtain ⟨is, sMid, _, hk⟩ := lowerM_bind_ok' h
    obtain ⟨blk0, rest, tail, rfl, hlbl, hpad, hbody⟩ :=
      lowerPlainBody_head_shape b cm auxPfx frameSlots? k l p _ _ hk
    exact ⟨blk0, rest, is ++ tail, rfl, hlbl, hpad, by simpa [List.append_assoc] using hbody⟩
  | .store _ _ k, l, p, acc, d, _, _, _, h => by
    dsimp only [lowerPlainBody] at h
    obtain ⟨is, sMid, _, hk⟩ := lowerM_bind_ok' h
    obtain ⟨blk0, rest, tail, rfl, hlbl, hpad, hbody⟩ :=
      lowerPlainBody_head_shape b cm auxPfx frameSlots? k l p _ _ hk
    exact ⟨blk0, rest, is ++ tail, rfl, hlbl, hpad, by simpa [List.append_assoc] using hbody⟩
  | .codeAddr sym k, l, p, acc, d, _, _, _, h => by
    dsimp only [lowerPlainBody] at h; split at h
    · dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at h; cases h
    · let is := emitToLoc b.w0 (locOf b 0 d) fun rd => [.symAddr sym rd]
      obtain ⟨blk0, rest, tail, rfl, hlbl, hpad, hbody⟩ :=
        lowerPlainBody_head_shape b cm auxPfx frameSlots? k l p (acc ++ is) (d + 1) h
      exact ⟨blk0, rest, is ++ tail, rfl, hlbl, hpad, by simpa [List.append_assoc] using hbody⟩
  | .jnz _ _ _, l, p, acc, d, _, _, _, h => by
    dsimp only [lowerPlainBody] at h
    obtain ⟨p1, _, _, h2⟩ := lowerM_bind_ok' h
    obtain ⟨_, _, _, h3⟩ := lowerM_bind_ok' h2
    obtain ⟨_, _, _, h4⟩ := lowerM_bind_ok' h3
    obtain ⟨_, _, _, h5⟩ := lowerM_bind_ok' h4
    obtain ⟨_, _, _, h6⟩ := lowerM_bind_ok' h5
    dsimp only [Pure.pure, StateT.pure] at h6; cases h6
    exact ⟨_, _, p1.1, rfl, rfl, rfl, rfl⟩
  | .ijmp _ _, l, p, acc, d, _, _, _, h => by
    dsimp only [lowerPlainBody] at h
    obtain ⟨ctgt, _, _, h2⟩ := lowerM_bind_ok' h
    obtain ⟨cnxt, _, _, h3⟩ := lowerM_bind_ok' h2
    cases hfs : frameSlots? with
    | none =>
      rw [hfs] at h3; dsimp only [Pure.pure, StateT.pure] at h3; cases h3
      exact ⟨_, _, ctgt ++ cnxt, rfl, rfl, rfl, by simp [List.append_assoc]⟩
    | some ns =>
      rw [hfs] at h3; dsimp only [Pure.pure, StateT.pure] at h3; cases h3
      exact ⟨_, _, ctgt ++ cnxt ++ [.epilogue ns], rfl, rfl, rfl, by simp [List.append_assoc]⟩
  | .halt _, l, p, acc, d, _, _, _, h => by
    dsimp only [lowerPlainBody] at h
    obtain ⟨ccode, _, _, h2⟩ := lowerM_bind_ok' h
    cases hfs : frameSlots? with
    | none =>
      rw [hfs] at h2; dsimp only [Pure.pure, StateT.pure] at h2; cases h2
      exact ⟨_, _, ccode, rfl, rfl, rfl, by simp⟩
    | some ns =>
      rw [hfs] at h2; dsimp only [Pure.pure, StateT.pure] at h2; cases h2
      exact ⟨_, _, ccode ++ [.epilogue ns], rfl, rfl, rfl, by simp [List.append_assoc]⟩
  | .hlt, _, _, _, _, _, _, _, h => by
    dsimp only [lowerPlainBody, liftEx, StateT.lift, StateT.run, Except.map] at h; cases h

private theorem lowerPlainBody_body_bwp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {vcm : VllCodeMap A} (hvwf : vcm.Wf)
    {auxPfx : Sym} {frameSlots? : Option Nat} {dMax : Nat} {hwSp ra₀ : BitVec 64}
    {G : Mem 64 → Prop} {Ψ_L0 : BedrockWord.CodeSpec} {H_L0 : HaltPost}
    {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hcl : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (hcmAddr : ∀ sym a, cm.addrOf? sym = some a → vcm.symAddr sym = a)
    (hspills : tempSpillCount b dMax ≤ frameSlots?.getD 0)
    (hEndIjmp : ∀ s_fin (tgtVal : BitVec 64) (nxt' : RegsExpr Val) (m' : Mem 64)
      (slots' : List (BitVec 64)),
      slots'.length = frameSlots?.getD 0 →
      s_fin.gpr b.w0 = tgtVal →
      WordRegsRel b nxt'.eval s_fin →
      (frameSlots? = none → (vllFramePreds A).raReg s_fin ra₀) →
      s_fin.gpr A.abi.sp = hwSp →
      (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
      Ψ_L0 tgtVal ⟨nxt'.eval, m'⟩ →
      bodyWp A vcm.symAddr (match frameSlots? with | some ns => [.epilogue ns] | none => [])
        (fun s' => Ψ_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin)
    (hEndHalt : ∀ s_fin (cVal : BitVec 64) (m' : Mem 64) (slots' : List (BitVec 64)),
      slots'.length = frameSlots?.getD 0 →
      s_fin.gpr b.w0 = cVal →
      s_fin.gpr A.abi.sp = hwSp →
      (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
      H_L0 cVal m' →
      bodyWp A vcm.symAddr (match frameSlots? with | some ns => [.epilogue ns] | none => [])
        (fun s' => H_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin) :
    ∀ (blk : BlockFlat) (curLbl : Sym) (pad? : Option PadKind) (acc bodyTail : List (Instr A))
      (d : Nat) (bvs : List ((t : Ty) × Val t)) (rw : Regs) (mL0 : Mem 64)
      {s0 s1 : Nat} {blk0 : Block A} {rest : List (Block A)},
      6 ≤ d → maxBlockDepth blk d ≤ dMax →
      (lowerPlainBody b cm auxPfx frameSlots? curLbl pad? acc d blk).run s0 =
        .ok (blk0 :: rest, s1) →
      blk0.body = acc ++ bodyTail →
      (∀ x ∈ blk0 :: rest, x ∈ vcm.blocks) →
      blk.wp cm.symEnv Ψ_L0 H_L0 bvs mL0 →
      ∀ (s : MachSt A) (slots : List (BitVec 64)),
        slots.length = frameSlots?.getD 0 →
        EnvRel b 0 d bvs s → WordRegsRel b rw s →
        (frameSlots? = none → (vllFramePreds A).raReg s ra₀) →
        s.gpr A.abi.sp = hwSp →
        (array64 hwSp slots ⋆ (Eq mL0 ⋆ G)) s.mem →
        bodyWp A vcm.symAddr bodyTail (termWp A vcm.symAddr blk0.term Ψ_L1 H_L1) Ψ_L1 H_L1 s
  | .let_ (ts := ts) op k, l, p, acc, bodyTail, d, bvs, rw, mL0, s0, s1, blk0, rest,
      h6, hdMax, hlo, hbody, hsub, hbp, s, slots, hlen, he, hr, hra, hsp, hm => by
    dsimp only [lowerPlainBody] at hlo
    obtain ⟨pOp, sMid, hOp, hRest⟩ := lowerM_bind_ok' hlo
    cases hOp' : lowerOp b 0 d op with
    | error _ =>
      rw [hOp'] at hOp; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hOp; cases hOp
    | ok pair =>
      rcases pair with ⟨is, d'⟩
      rw [hOp'] at hOp; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hOp; cases hOp
      have hdEq := lowerOp_d_eq hOp'; subst hdEq
      obtain ⟨_, _, tail', hEqC, _, _, hbody'⟩ := lowerPlainBody_head_shape b cm auxPfx frameSlots?
        k l p (acc ++ is) (d + ts.length) hRest
      cases hEqC
      have hTailEq : bodyTail = is ++ tail' :=
        List.append_cancel_left (hbody.symm.trans (by simpa [List.append_assoc] using hbody'))
      subst hTailEq
      dsimp only [BlockFlat.wp] at hbp
      cases hden : denoteArgs bvs op.args with
      | none => rw [hden] at hbp; exact False.elim hbp
      | some args' =>
        rw [hden] at hbp
        have hdMax' : maxBlockDepth k (d + ts.length) ≤ dMax := by simpa [maxBlockDepth] using hdMax
        have hdLt : d < dMax := by
          have hle := maxBlockDepth_le k (d + ts.length)
          have hts := lowerOp_ts_length hOp'; omega
        have hNo : ∀ i ∈ is, IsNoRaInstr b i := isNoRa_lowerOp b hOp'
        refine bodyWp_append is tail' s (bodyWp_imp_raReg_cont hwf hNo hra ?_)
        have hm' : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mL0 ⋆ G)) s.mem := by simpa [hsp] using hm
        exact lowerOp_bodyWp hawf hwf hdLt h6 (by omega) he hr hm' hden hbp hOp'
          (fun rvs s' slots' hkRes _ hlen' _ he' hr' hsp' hm'' => fun hra' =>
            lowerPlainBody_body_bwp hawf hwf hvwf hcl hcmAddr hspills hEndIjmp hEndHalt k l p
              (acc ++ is) tail' (d + ts.length) (pushTup rvs bvs) rw mL0 (by omega) hdMax' hRest
              hbody' hsub hkRes s' slots' (hlen'.trans hlen) he' hr' hra' (hsp'.trans hsp)
              (by simpa [hsp'.trans hsp] using hm''))
  | .load t a k, l, p, acc, bodyTail, d, bvs, rw, mL0, s0, s1, blk0, rest,
      h6, hdMax, hlo, hbody, hsub, hbp, s, slots, hlen, he, hr, hra, hsp, hm => by
    dsimp only [lowerPlainBody] at hlo
    obtain ⟨is, sMid, hLd, hRest⟩ := lowerM_bind_ok' hlo
    cases hLd' : lowerMemLoad b 0 d t a with
    | error _ =>
      rw [hLd'] at hLd; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hLd; cases hLd
    | ok is_ =>
      rw [hLd'] at hLd; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hLd; cases hLd
      obtain ⟨_, _, tail', hEqC, _, _, hbody'⟩ :=
        lowerPlainBody_head_shape b cm auxPfx frameSlots? k l p (acc ++ is) (d + 1) hRest
      cases hEqC
      have hTailEq : bodyTail = is ++ tail' :=
        List.append_cancel_left (hbody.symm.trans (by simpa [List.append_assoc] using hbody'))
      subst hTailEq
      dsimp only [BlockFlat.wp] at hbp
      cases hda : denoteArg bvs a with
      | none => rw [hda] at hbp; exact False.elim hbp
      | some aa =>
        rw [hda] at hbp; rcases hbp with ⟨v, hv, hk⟩
        have hdMax' : maxBlockDepth k (d + 1) ≤ dMax := by simpa [maxBlockDepth] using hdMax
        have hdLt : d < dMax := Nat.lt_of_lt_of_le (Nat.lt_succ_self d)
          (Nat.le_trans (maxBlockDepth_le k (d + 1)) hdMax')
        have hNo : ∀ i ∈ is, IsNoRaInstr b i := isNoRa_lowerMemLoad b hLd'
        refine bodyWp_append is tail' s (bodyWp_imp_raReg_cont hwf hNo hra ?_)
        have hm' : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mL0 ⋆ G)) s.mem := by simpa [hsp] using hm
        exact lowerMemLoad_bodyWp hwf hdLt h6 (by omega) he hr hm' hda hv hLd'
          (fun s' slots' hlen' _ he' hr' hsp' hm'' => fun hra' =>
            lowerPlainBody_body_bwp hawf hwf hvwf hcl hcmAddr hspills hEndIjmp hEndHalt k l p
              (acc ++ is) tail' (d + 1) (⟨t, v⟩ :: bvs) rw mL0 (by omega) hdMax' hRest hbody'
              hsub hk s' slots' (hlen'.trans hlen) he' hr' hra' (hsp'.trans hsp)
              (by simpa [hsp'.trans hsp] using hm''))
  | .store v a k, l, p, acc, bodyTail, d, bvs, rw, mL0, s0, s1, blk0, rest,
      h6, hdMax, hlo, hbody, hsub, hbp, s, slots, hlen, he, hr, hra, hsp, hm => by
    dsimp only [lowerPlainBody] at hlo
    obtain ⟨is, sMid, hSt, hRest⟩ := lowerM_bind_ok' hlo
    cases hSt' : lowerMemStore b 0 d v a with
    | error _ =>
      rw [hSt'] at hSt; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hSt; cases hSt
    | ok is_ =>
      rw [hSt'] at hSt; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hSt; cases hSt
      obtain ⟨_, _, tail', hEqC, _, _, hbody'⟩ :=
        lowerPlainBody_head_shape b cm auxPfx frameSlots? k l p (acc ++ is) d hRest
      cases hEqC
      have hTailEq : bodyTail = is ++ tail' :=
        List.append_cancel_left (hbody.symm.trans (by simpa [List.append_assoc] using hbody'))
      subst hTailEq
      dsimp only [BlockFlat.wp] at hbp
      cases hdv : denoteArg bvs v <;> rw [hdv] at hbp; · exact False.elim hbp
      cases hda : denoteArg bvs a <;> rw [hda] at hbp; · exact False.elim hbp
      rcases hbp with ⟨hst, hk⟩
      have hdMax' : maxBlockDepth k d ≤ dMax := by simpa [maxBlockDepth] using hdMax
      have hdLe : d ≤ dMax := Nat.le_trans (maxBlockDepth_le k d) hdMax'
      have hNo : ∀ i ∈ is, IsNoRaInstr b i := isNoRa_lowerMemStore b hSt'
      refine bodyWp_append is tail' s (bodyWp_imp_raReg_cont hwf hNo hra ?_)
      have hm' : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mL0 ⋆ G)) s.mem := by simpa [hsp] using hm
      exact lowerMemStore_bodyWp hwf hdLe (by omega) he hr hm' hdv hda hst hSt'
        (fun s' he' hr' hsp' hm'' => fun hra' =>
          lowerPlainBody_body_bwp hawf hwf hvwf hcl hcmAddr hspills hEndIjmp hEndHalt k l p
            (acc ++ is) tail' d bvs rw _ h6 hdMax' hRest hbody' hsub hk s' slots hlen he' hr'
            hra' (hsp'.trans hsp) (by simpa [hsp'.trans hsp] using hm''))
  | .codeAddr sym k, l, p, acc, bodyTail, d, bvs, rw, mL0, s0, s1, blk0, rest,
      h6, hdMax, hlo, hbody, hsub, hbp, s, slots, hlen, he, hr, hra, hsp, hm => by
    dsimp only [lowerPlainBody] at hlo
    dsimp only [BlockFlat.wp] at hbp; rcases hbp with ⟨a, ha, hk⟩
    have ha' : cm.addrOf? sym = some a := ha
    have hnone : (cm.addrOf? sym).isNone = false := by simp [ha']
    simp only [hnone, Bool.false_eq_true, ↓reduceIte] at hlo
    let is := emitToLoc b.w0 (locOf b 0 d) fun rd => [.symAddr sym rd]
    obtain ⟨_, _, tail', hEqC, _, _, hbody'⟩ :=
      lowerPlainBody_head_shape b cm auxPfx frameSlots? k l p (acc ++ is) (d + 1) hlo
    cases hEqC
    have hTailEq : bodyTail = is ++ tail' :=
      List.append_cancel_left (hbody.symm.trans (by simpa [List.append_assoc] using hbody'))
    rw [hTailEq]
    have hdMax' : maxBlockDepth k (d + 1) ≤ dMax := by simpa [maxBlockDepth] using hdMax
    have hdLt : d < dMax := Nat.lt_of_lt_of_le (Nat.lt_succ_self d)
      (Nat.le_trans (maxBlockDepth_le k (d + 1)) hdMax')
    refine bodyWp_append is tail' s ?_
    have hm' : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mL0 ⋆ G)) s.mem := by simpa [hsp] using hm
    exact lowerCodeAddr_bodyWp hwf hdLt h6 (by omega) (hcmAddr sym a ha') he hr hra hm'
      fun s' slots' hlen' _ he' hr' hra' hsp' hm'' =>
        lowerPlainBody_body_bwp hawf hwf hvwf hcl hcmAddr hspills hEndIjmp hEndHalt k l p
          (acc ++ is) tail' (d + 1) (⟨i64, a⟩ :: bvs) rw mL0 (by omega) hdMax' hlo hbody' hsub hk
          s' slots' (hlen'.trans hlen) he' hr' hra' (hsp'.trans hsp)
          (by simpa [hsp'.trans hsp] using hm'')
  | .jnz c t e, l, p, acc, bodyTail, d, bvs, rw, mL0, s0, s1, blk0, rest,
      h6, hdMax, hlo, hbody, hsub, hbp, s, slots, hlen, he, hr, hra, hsp, hm => by
    dsimp only [lowerPlainBody] at hlo
    obtain ⟨pC, _, hC, h2⟩ := lowerM_bind_ok' hlo
    cases hC' : loadArgToGpr b 0 d b.w0 c with
    | error _ =>
      rw [hC'] at hC; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hC; cases hC
    | ok pair =>
      rcases pair with ⟨cc, rc⟩
      rw [hC'] at hC; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hC; cases hC
      obtain ⟨lT, _, _, h3⟩ := lowerM_bind_ok' h2
      obtain ⟨lF, _, _, h4⟩ := lowerM_bind_ok' h3
      obtain ⟨bsT, _, hbsT, h5⟩ := lowerM_bind_ok' h4
      obtain ⟨bsF, _, hbsF, h6'⟩ := lowerM_bind_ok' h5
      dsimp only [Pure.pure, StateT.pure] at h6'; cases h6'
      dsimp only at hbody
      have hTailEq : bodyTail = cc := List.append_cancel_left hbody.symm
      rw [hTailEq]
      dsimp only [BlockFlat.wp] at hbp
      cases hdc : denoteArg bvs c <;> rw [hdc] at hbp; · exact False.elim hbp
      rename_i c'; rcases hbp with ⟨hbt, hbf⟩
      have hNo : ∀ i ∈ cc, IsNoRaInstr b i := isNoRa_loadArgToGpr b (work_mem_allRegs b).2.1 hC'
      have hdMaxT : maxBlockDepth t d ≤ dMax :=
        Nat.le_trans (Nat.le_max_left _ _) (by simpa [maxBlockDepth] using hdMax)
      have hdMaxF : maxBlockDepth e d ≤ dMax :=
        Nat.le_trans (Nat.le_max_right _ _) (by simpa [maxBlockDepth] using hdMax)
      have hsubT : ∀ x ∈ bsT, x ∈ vcm.blocks := fun x hx =>
        hsub x (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      have hsubF : ∀ x ∈ bsF, x ∈ vcm.blocks := fun x hx =>
        hsub x (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
      refine bodyWp_imp_raReg_mono hwf hNo hra (loadArgToGpr_bodyWp hwf (w_mem_workRegs b).1 he hdc
        (by simpa [hsp] using hm) hC' fun s1 hs1_ne hv1 hm1 he1 =>
          And.intro hs1_ne (And.intro hv1 (And.intro hm1 he1)))
        fun s1 ⟨hs1_ne, hv1, hm1, he1⟩ hra1 => ?_
      have hsp1 : s1.gpr A.abi.sp = hwSp := (hs1_ne A.abi.sp (work_not_sp hwf).2.1.symm).trans hsp
      have hr1 := wordRegsRel_updWork hwf hr b.w0 (w_mem_workRegs b).1 hs1_ne
      have hnz : ((s1.gpr rc).setWidth 8 != 0#8) = c'.val := valHolds64_bool_nonzero hv1
      refine termWp_jnzGpr (fun htr => ?_) (fun hfl => ?_)
      · obtain ⟨blkT, restT, tailT, rfl, hlblT, _, hbodyT⟩ :=
          lowerPlainBody_head_shape b cm auxPfx frameSlots? t lT none [] d hbsT
        have hbwT := lowerPlainBody_body_bwp hawf hwf hvwf hcl hcmAddr hspills hEndIjmp hEndHalt t
          lT none [] tailT d bvs rw mL0 h6 hdMaxT hbsT hbodyT hsubT (hbt (hnz ▸ htr))
          (s1.setFlags (A.jnzGprFlags (s1.gpr rc) s1.flags)) slots hlen
          ((envRel_setFlags _ _ _ _ _ _).mpr he1) ((wordRegsRel_setFlags _ _ _ _).mpr hr1)
          (fun h => (raReg_setFlags A _ _ _).mpr (hra1 h)) hsp1 (by simpa [hsp1, hm1] using hm)
        exact hlblT ▸ closed_bwp hvwf hcl (hsubT blkT List.mem_cons_self)
          ((List.nil_append tailT ▸ hbodyT) ▸ hbwT)
      · obtain ⟨blkF, restF, tailF, rfl, hlblF, _, hbodyF⟩ :=
          lowerPlainBody_head_shape b cm auxPfx frameSlots? e lF none [] d hbsF
        have hbwF := lowerPlainBody_body_bwp hawf hwf hvwf hcl hcmAddr hspills hEndIjmp hEndHalt e
          lF none [] tailF d bvs rw mL0 h6 hdMaxF hbsF hbodyF hsubF (hbf (hnz ▸ hfl))
          (s1.setFlags (A.jnzGprFlags (s1.gpr rc) s1.flags)) slots hlen
          ((envRel_setFlags _ _ _ _ _ _).mpr he1) ((wordRegsRel_setFlags _ _ _ _).mpr hr1)
          (fun h => (raReg_setFlags A _ _ _).mpr (hra1 h)) hsp1 (by simpa [hsp1, hm1] using hm)
        exact hlblF ▸ closed_bwp hvwf hcl (hsubF blkF List.mem_cons_self)
          ((List.nil_append tailF ▸ hbodyF) ▸ hbwF)
  | .ijmp tgt nxt, l, p, acc, bodyTail, d, bvs, rw, mL0, s0, s1, blk0, rest,
      _, hdMax, hlo, hbody, _, hbp, s, slots, hlen, he, _, hra, hsp, hm => by
    dsimp only [lowerPlainBody] at hlo
    obtain ⟨ctgt, _, hT, h2⟩ := lowerM_bind_ok' hlo
    cases hT' : loadArgInto b 0 d b.w0 tgt with
    | error _ =>
      rw [hT'] at hT; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hT; cases hT
    | ok ctgt_ =>
      rw [hT'] at hT; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hT; cases hT
      obtain ⟨cnxt, _, hN, h3⟩ := lowerM_bind_ok' h2
      cases hN' : emitNextRegs b 0 d nxt with
      | error _ =>
        rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
      | ok cnxt_ =>
        rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
        dsimp only [Pure.pure, StateT.pure] at h3; cases h3
        let ep : List (Instr A) := frameSlots?.elim [] fun ns => [.epilogue ns]
        have hTailEq : bodyTail = ctgt ++ (cnxt ++ ep) := by
          cases frameSlots? <;> (
            have h := hbody.symm; dsimp only at h; simp only [List.append_assoc] at h
            exact List.append_cancel_left h)
        rw [hTailEq]
        dsimp only [BlockFlat.wp] at hbp
        cases hdt : denoteArg bvs tgt <;> rw [hdt] at hbp; · exact False.elim hbp
        cases hdn : denoteRegsExpr bvs nxt <;> rw [hdn] at hbp; · exact False.elim hbp
        rename_i tgt' nxt'
        have hwk := w_mem_workRegs b; have hwne := wordRegBind_work_ne hwf
        have hNoT : ∀ i ∈ ctgt, IsNoRaInstr b i := isNoRa_loadArgInto b (work_mem_allRegs b).2.1 hT'
        have hNoN : ∀ i ∈ cnxt, IsNoRaInstr b i := isNoRa_emitNextRegs b hN'
        refine bodyWp_append ctgt (cnxt ++ ep) s (bodyWp_imp_raReg_mono hwf hNoT hra
          (loadArgInto_bodyWp hawf hwf hwk.1 he hdt (by simpa [hsp] using hm) hT'
            fun s1 hs1_ne hv1 hm1 he1 => And.intro hs1_ne (And.intro hv1 (And.intro hm1 he1)))
          fun s1 ⟨hs1_ne, hv1, hm1, he1⟩ hra1 => ?_)
        have hsp1 : s1.gpr A.abi.sp = hwSp := (hs1_ne A.abi.sp (work_not_sp hwf).2.1.symm).trans hsp
        have hslots1 : ∀ lvl < d, ∀ j, locOf b 0 lvl = .slot j → j < slots.length :=
          envRel_slots_bound b (by simpa [maxBlockDepth] using hdMax) (by omega)
        refine bodyWp_append cnxt ep s1 (bodyWp_imp_raReg_mono hwf hNoN hra1
          (emitNextRegs_bodyWp hawf hwf he1 hdn (by simpa [hsp1, hm1] using hm) hslots1 hN'
            fun s2 hr2 hs2_ne hm2 => And.intro hr2 (And.intro hs2_ne hm2))
          fun s2 ⟨hr2, hs2_ne, hm2⟩ hra2 => ?_)
        have hsp2 : s2.gpr A.abi.sp = hwSp :=
          (hs2_ne A.abi.sp (fun hm' => (wordRegs_not_sp_ra hwf).1 _ hm' |>.1 rfl)
            (work_not_sp hwf).2.2.1.symm).trans hsp1
        have hw0_eq : s2.gpr b.w0 = tgt'.val := by
          have hw0_1 := hs2_ne b.w0 (fun hm' => (wordRegs_not_sp_ra hwf).2 _ hm' |>.2.1 rfl)
            hwne.2.2.2.1
          dsimp only [ValHolds64] at hv1
          exact hw0_1.trans (by simpa [BitVec.setWidth_eq] using hv1.2)
        refine bodyWp_mono (fun s' h => termWp_ijmp h) ?_
        cases frameSlots? <;>
          exact hEndIjmp s2 tgt'.val nxt' mL0 slots hlen hw0_eq hr2 hra2 hsp2
            (by simpa [hm2, hm1] using hm) hbp
  | .halt code, l, p, acc, bodyTail, d, bvs, rw, mL0, s0, s1, blk0, rest,
      _, _, hlo, hbody, _, hbp, s, slots, hlen, he, _, hra, hsp, hm => by
    dsimp only [lowerPlainBody] at hlo
    obtain ⟨ccode, _, hC, h2⟩ := lowerM_bind_ok' hlo
    cases hC' : loadArgInto b 0 d b.w0 code with
    | error _ =>
      rw [hC'] at hC; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hC; cases hC
    | ok ccode_ =>
      rw [hC'] at hC; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hC; cases hC
      dsimp only [Pure.pure, StateT.pure] at h2; cases h2
      let ep : List (Instr A) := frameSlots?.elim [] fun ns => [.epilogue ns]
      have hTailEq : bodyTail = ccode ++ ep := by
        cases frameSlots? <;> (
          have h := hbody.symm; dsimp only at h; simp only [List.append_assoc] at h
          exact List.append_cancel_left h)
      rw [hTailEq]
      dsimp only [BlockFlat.wp] at hbp
      cases hdc : denoteArg bvs code <;> rw [hdc] at hbp; · exact False.elim hbp
      rename_i c'
      have hNo : ∀ i ∈ ccode, IsNoRaInstr b i := isNoRa_loadArgInto b (work_mem_allRegs b).2.1 hC'
      refine bodyWp_append ccode ep s (bodyWp_imp_raReg_mono hwf hNo hra
        (loadArgInto_bodyWp hawf hwf (w_mem_workRegs b).1 he hdc (by simpa [hsp] using hm) hC'
          fun s1 hs1_ne hv1 hm1 he1 => And.intro hs1_ne (And.intro hv1 (And.intro hm1 he1)))
        fun s1 ⟨hs1_ne, hv1, hm1, _⟩ _ => ?_)
      have hsp1 : s1.gpr A.abi.sp = hwSp := (hs1_ne A.abi.sp (work_not_sp hwf).2.1.symm).trans hsp
      have hw0_eq : s1.gpr b.w0 = c'.val := by
        dsimp only [ValHolds64] at hv1; simpa [BitVec.setWidth_eq] using hv1.2
      refine bodyWp_mono (fun s' h => termWp_halt h) ?_
      cases frameSlots? <;>
        exact hEndHalt s1 c'.val mL0 slots hlen hw0_eq hsp1 (by simpa [hm1] using hm) hbp
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlo, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [lowerPlainBody, liftEx, StateT.lift, StateT.run, Except.map] at hlo; cases hlo

theorem lowerPlainBody_bwp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {vcm : VllCodeMap A} (hvwf : vcm.Wf)
    {auxPfx : Sym} {frameSlots? : Option Nat} {dMax : Nat} {hwSp ra₀ : BitVec 64}
    {G : Mem 64 → Prop} {Ψ_L0 : BedrockWord.CodeSpec} {H_L0 : HaltPost}
    {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hcl : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (hcmAddr : ∀ sym a, cm.addrOf? sym = some a → vcm.symAddr sym = a)
    (hspills : tempSpillCount b dMax ≤ frameSlots?.getD 0)
    (hEndIjmp : ∀ s_fin (tgtVal : BitVec 64) (nxt' : RegsExpr Val) (m' : Mem 64)
      (slots' : List (BitVec 64)),
      slots'.length = frameSlots?.getD 0 →
      s_fin.gpr b.w0 = tgtVal →
      WordRegsRel b nxt'.eval s_fin →
      (frameSlots? = none → (vllFramePreds A).raReg s_fin ra₀) →
      s_fin.gpr A.abi.sp = hwSp →
      (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
      Ψ_L0 tgtVal ⟨nxt'.eval, m'⟩ →
      bodyWp A vcm.symAddr (match frameSlots? with | some ns => [.epilogue ns] | none => [])
        (fun s' => Ψ_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin)
    (hEndHalt : ∀ s_fin (cVal : BitVec 64) (m' : Mem 64) (slots' : List (BitVec 64)),
      slots'.length = frameSlots?.getD 0 →
      s_fin.gpr b.w0 = cVal →
      s_fin.gpr A.abi.sp = hwSp →
      (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
      H_L0 cVal m' →
      bodyWp A vcm.symAddr (match frameSlots? with | some ns => [.epilogue ns] | none => [])
        (fun s' => H_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin)
    (blk : BlockFlat) (curLbl : Sym) (pad? : Option PadKind) (acc : List (Instr A))
    (d : Nat) (bvs : List ((t : Ty) × Val t)) (rw : Regs) (mL0 : Mem 64)
    {s0 s1 : Nat} {bs : List (Block A)} (s_entry : MachSt A)
    (h6 : 6 ≤ d) (hdMax : maxBlockDepth blk d ≤ dMax)
    (hlo : (lowerPlainBody b cm auxPfx frameSlots? curLbl pad? acc d blk).run s0 = .ok (bs, s1))
    (hsub : ∀ x ∈ bs, x ∈ vcm.blocks)
    (hbp : blk.wp cm.symEnv Ψ_L0 H_L0 bvs mL0)
    (hacc : bodyWp A vcm.symAddr acc (fun s => ∃ slots : List (BitVec 64),
      slots.length = frameSlots?.getD 0 ∧
      EnvRel b 0 d bvs s ∧ WordRegsRel b rw s ∧
      (frameSlots? = none → (vllFramePreds A).raReg s ra₀) ∧
      s.gpr A.abi.sp = hwSp ∧
      (array64 hwSp slots ⋆ (Eq mL0 ⋆ G)) s.mem) Ψ_L1 H_L1 s_entry) :
    Ψ_L1 (vcm.symAddr curLbl) s_entry := by
  obtain ⟨blk0, rest, bodyTail, rfl, hlbl, _, hbody⟩ :=
    lowerPlainBody_head_shape b cm auxPfx frameSlots? blk curLbl pad? acc d hlo
  refine hlbl ▸ closed_bwp hvwf hcl (hsub blk0 List.mem_cons_self) ?_
  rw [hbody]
  refine bodyWp_append acc bodyTail s_entry (bodyWp_mono (fun s hs => ?_) hacc)
  rcases hs with ⟨slots, hlen, he, hr, hra, hsp, hm⟩
  exact lowerPlainBody_body_bwp hawf hwf hvwf hcl hcmAddr hspills hEndIjmp hEndHalt blk curLbl
    pad? acc bodyTail d bvs rw mL0 h6 hdMax hlo hbody hsub hbp s slots hlen he hr hra hsp hm

/-! ## §3. Stage-1 Unpromoted Tail (`lowerContUnpromoted_bwp`) -/

private theorem lowerContUnpromoted_head_shape {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (cr : ContifyRegion) (spillBase ns : Nat) (needFrame : Bool) :
    ∀ (blk : BlockFlat) (curLbl : Sym) (acc : List (Instr A)) (d : Nat)
      {s0 s1 : Nat} {bs : List (Block A)},
      (lowerContUnpromoted b cm cr spillBase ns needFrame curLbl acc d blk).run s0 = .ok (bs, s1) →
      ∃ blk0 rest bodyTail, bs = blk0 :: rest ∧ blk0.label = curLbl ∧ blk0.pad? = none ∧
        blk0.body = acc ++ bodyTail
  | .let_ _ k, l, acc, d, _, _, _, h => by
    dsimp only [lowerContUnpromoted] at h
    obtain ⟨p', _, _, hk⟩ := lowerM_bind_ok' h
    obtain ⟨blk0, rest, tail, rfl, hlbl, hpad, hbody⟩ :=
      lowerContUnpromoted_head_shape b cm cr spillBase ns needFrame k l _ _ hk
    exact ⟨blk0, rest, p'.1 ++ tail, rfl, hlbl, hpad, by simpa [List.append_assoc] using hbody⟩
  | .load _ _ k, l, acc, d, _, _, _, h => by
    dsimp only [lowerContUnpromoted] at h
    obtain ⟨is, _, _, hk⟩ := lowerM_bind_ok' h
    obtain ⟨blk0, rest, tail, rfl, hlbl, hpad, hbody⟩ :=
      lowerContUnpromoted_head_shape b cm cr spillBase ns needFrame k l _ _ hk
    exact ⟨blk0, rest, is ++ tail, rfl, hlbl, hpad, by simpa [List.append_assoc] using hbody⟩
  | .store _ _ k, l, acc, d, _, _, _, h => by
    dsimp only [lowerContUnpromoted] at h
    obtain ⟨is, _, _, hk⟩ := lowerM_bind_ok' h
    obtain ⟨blk0, rest, tail, rfl, hlbl, hpad, hbody⟩ :=
      lowerContUnpromoted_head_shape b cm cr spillBase ns needFrame k l _ _ hk
    exact ⟨blk0, rest, is ++ tail, rfl, hlbl, hpad, by simpa [List.append_assoc] using hbody⟩
  | .codeAddr sym k, l, acc, d, _, _, _, h => by
    dsimp only [lowerContUnpromoted] at h; split at h
    · dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at h; cases h
    · let is := emitToLoc b.w0 (locOf b spillBase d) fun rd => [.symAddr sym rd]
      obtain ⟨blk0, rest, tail, rfl, hlbl, hpad, hbody⟩ :=
        lowerContUnpromoted_head_shape b cm cr spillBase ns needFrame k l (acc ++ is) (d + 1) h
      exact ⟨blk0, rest, is ++ tail, rfl, hlbl, hpad, by simpa [List.append_assoc] using hbody⟩
  | .jnz _ _ _, l, acc, d, _, _, _, h => by
    dsimp only [lowerContUnpromoted] at h
    obtain ⟨p1, _, _, h2⟩ := lowerM_bind_ok' h
    obtain ⟨_, _, _, h3⟩ := lowerM_bind_ok' h2
    obtain ⟨_, _, _, h4⟩ := lowerM_bind_ok' h3
    obtain ⟨_, _, _, h5⟩ := lowerM_bind_ok' h4
    obtain ⟨_, _, _, h6⟩ := lowerM_bind_ok' h5
    dsimp only [Pure.pure, StateT.pure] at h6; cases h6
    exact ⟨_, _, p1.1, rfl, rfl, rfl, rfl⟩
  | .ijmp _ _, l, acc, d, _, _, _, h => by
    dsimp only [lowerContUnpromoted] at h
    obtain ⟨ctgt, _, _, h2⟩ := lowerM_bind_ok' h
    obtain ⟨cnxt, _, _, h3⟩ := lowerM_bind_ok' h2
    cases hnf : needFrame with
    | false =>
      rw [hnf] at h3; dsimp only [Pure.pure, StateT.pure] at h3; cases h3
      exact ⟨_, _, ctgt ++ cnxt, rfl, rfl, rfl, by simp [List.append_assoc]⟩
    | true =>
      rw [hnf] at h3; dsimp only [Pure.pure, StateT.pure] at h3; cases h3
      exact ⟨_, _, ctgt ++ cnxt ++ [.epilogue ns], rfl, rfl, rfl, by simp [List.append_assoc]⟩
  | .halt _, l, acc, d, _, _, _, h => by
    dsimp only [lowerContUnpromoted] at h
    obtain ⟨ccode, _, _, h2⟩ := lowerM_bind_ok' h
    cases hnf : needFrame with
    | false =>
      rw [hnf] at h2; dsimp only [Pure.pure, StateT.pure] at h2; cases h2
      exact ⟨_, _, ccode, rfl, rfl, rfl, by simp⟩
    | true =>
      rw [hnf] at h2; dsimp only [Pure.pure, StateT.pure] at h2; cases h2
      exact ⟨_, _, ccode ++ [.epilogue ns], rfl, rfl, rfl, by simp [List.append_assoc]⟩
  | .hlt, _, _, _, _, _, _, h => by
    dsimp only [lowerContUnpromoted, liftEx, StateT.lift, StateT.run, Except.map] at h; cases h

private theorem lowerContUnpromoted_body_bwp {A : Arch} (hawf : A.Wf) {b : WordRegBind A}
    (hwf : b.Wf) {cm : CodeMap} {vcm : VllCodeMap A} (hvwf : vcm.Wf)
    {cr : ContifyRegion} {spillBase ns ns_ dMax : Nat} {needFrame : Bool}
    {hwSp ra₀ : BitVec 64} {G : Mem 64 → Prop} {Ψ_L0 : BedrockWord.CodeSpec} {H_L0 : HaltPost}
    {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hcl : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (hcmAddr : ∀ sym a, cm.addrOf? sym = some a → vcm.symAddr sym = a)
    (hspills : spillBase + tempSpillCount b dMax ≤ ns_)
    (hEndIjmp : ∀ s_fin (tgtVal : BitVec 64) (nxt' : Regs) (m' : Mem 64)
      (slots' : List (BitVec 64)),
      slots'.length = ns_ →
      s_fin.gpr b.w0 = tgtVal →
      WordRegsRel b nxt' s_fin →
      (needFrame = false → (vllFramePreds A).raReg s_fin ra₀) →
      s_fin.gpr A.abi.sp = hwSp →
      (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
      Ψ_L0 tgtVal ⟨nxt', m'⟩ →
      bodyWp A vcm.symAddr (if needFrame then [.epilogue ns] else [])
        (fun s' => Ψ_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin)
    (hEndHalt : ∀ s_fin (cVal : BitVec 64) (m' : Mem 64) (slots' : List (BitVec 64)),
      slots'.length = ns_ →
      s_fin.gpr b.w0 = cVal →
      s_fin.gpr A.abi.sp = hwSp →
      (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
      H_L0 cVal m' →
      bodyWp A vcm.symAddr (if needFrame then [.epilogue ns] else [])
        (fun s' => H_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin) :
    ∀ (blk : BlockFlat) (curLbl : Sym) (acc bodyTail : List (Instr A)) (d : Nat)
      (bvs : List ((t : Ty) × Val t)) (rw : Regs) (mL0 : Mem 64)
      {s0 s1 : Nat} {blk0 : Block A} {rest : List (Block A)},
      6 ≤ d → maxBlockDepth blk d ≤ dMax →
      (lowerContUnpromoted b cm cr spillBase ns needFrame curLbl acc d blk).run s0 =
        .ok (blk0 :: rest, s1) →
      blk0.body = acc ++ bodyTail →
      (∀ x ∈ blk0 :: rest, x ∈ vcm.blocks) →
      blk.wp cm.symEnv Ψ_L0 H_L0 bvs mL0 →
      ∀ (s : MachSt A) (slots : List (BitVec 64)),
        slots.length = ns_ →
        EnvRel b spillBase d bvs s → WordRegsRel b rw s →
        (needFrame = false → (vllFramePreds A).raReg s ra₀) →
        s.gpr A.abi.sp = hwSp →
        (array64 hwSp slots ⋆ (Eq mL0 ⋆ G)) s.mem →
        bodyWp A vcm.symAddr bodyTail (termWp A vcm.symAddr blk0.term Ψ_L1 H_L1) Ψ_L1 H_L1 s
  | .let_ (ts := ts) op k, l, acc, bodyTail, d, bvs, rw, mL0, s0, s1, blk0, rest,
      h6, hdMax, hlo, hbody, hsub, hbp, s, slots, hlen, he, hr, hra, hsp, hm => by
    dsimp only [lowerContUnpromoted] at hlo
    obtain ⟨pOp, sMid, hOp, hRest⟩ := lowerM_bind_ok' hlo
    cases hOp' : lowerOp b spillBase d op with
    | error _ =>
      rw [hOp'] at hOp; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hOp; cases hOp
    | ok pair =>
      rcases pair with ⟨is, d'⟩
      rw [hOp'] at hOp; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hOp; cases hOp
      have hdEq := lowerOp_d_eq hOp'; subst hdEq
      obtain ⟨_, _, tail', hEqC, _, _, hbody'⟩ := lowerContUnpromoted_head_shape b cm cr
        spillBase ns needFrame k l (acc ++ is) (d + ts.length) hRest
      cases hEqC
      have hTailEq : bodyTail = is ++ tail' :=
        List.append_cancel_left (hbody.symm.trans (by simpa [List.append_assoc] using hbody'))
      subst hTailEq
      dsimp only [BlockFlat.wp] at hbp
      cases hden : denoteArgs bvs op.args with
      | none => rw [hden] at hbp; exact False.elim hbp
      | some args' =>
        rw [hden] at hbp
        have hdMax' : maxBlockDepth k (d + ts.length) ≤ dMax := by simpa [maxBlockDepth] using hdMax
        have hdLt : d < dMax := by
          have hle := maxBlockDepth_le k (d + ts.length)
          have hts := lowerOp_ts_length hOp'; omega
        have hNo : ∀ i ∈ is, IsNoRaInstr b i := isNoRa_lowerOp b hOp'
        refine bodyWp_append is tail' s (bodyWp_imp_raReg_cont hwf hNo hra ?_)
        have hm' : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mL0 ⋆ G)) s.mem := by simpa [hsp] using hm
        exact lowerOp_bodyWp hawf hwf hdLt h6 (by omega) he hr hm' hden hbp hOp'
          (fun rvs s' slots' hkRes _ hlen' _ he' hr' hsp' hm'' => fun hra' =>
            lowerContUnpromoted_body_bwp hawf hwf hvwf hcl hcmAddr hspills hEndIjmp hEndHalt
              k l (acc ++ is) tail' (d + ts.length) (pushTup rvs bvs) rw mL0 (by omega) hdMax'
              hRest hbody' hsub hkRes s' slots' (hlen'.trans hlen) he' hr' hra' (hsp'.trans hsp)
              (by simpa [hsp'.trans hsp] using hm''))
  | .load t a k, l, acc, bodyTail, d, bvs, rw, mL0, s0, s1, blk0, rest,
      h6, hdMax, hlo, hbody, hsub, hbp, s, slots, hlen, he, hr, hra, hsp, hm => by
    dsimp only [lowerContUnpromoted] at hlo
    obtain ⟨is, sMid, hLd, hRest⟩ := lowerM_bind_ok' hlo
    cases hLd' : lowerMemLoad b spillBase d t a with
    | error _ =>
      rw [hLd'] at hLd; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hLd; cases hLd
    | ok is_ =>
      rw [hLd'] at hLd; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hLd; cases hLd
      obtain ⟨_, _, tail', hEqC, _, _, hbody'⟩ :=
        lowerContUnpromoted_head_shape b cm cr spillBase ns needFrame k l (acc ++ is) (d + 1)
          hRest
      cases hEqC
      have hTailEq : bodyTail = is ++ tail' :=
        List.append_cancel_left (hbody.symm.trans (by simpa [List.append_assoc] using hbody'))
      subst hTailEq
      dsimp only [BlockFlat.wp] at hbp
      cases hda : denoteArg bvs a with
      | none => rw [hda] at hbp; exact False.elim hbp
      | some aa =>
        rw [hda] at hbp; rcases hbp with ⟨v, hv, hk⟩
        have hdMax' : maxBlockDepth k (d + 1) ≤ dMax := by simpa [maxBlockDepth] using hdMax
        have hdLt : d < dMax := Nat.lt_of_lt_of_le (Nat.lt_succ_self d)
          (Nat.le_trans (maxBlockDepth_le k (d + 1)) hdMax')
        have hNo : ∀ i ∈ is, IsNoRaInstr b i := isNoRa_lowerMemLoad b hLd'
        refine bodyWp_append is tail' s (bodyWp_imp_raReg_cont hwf hNo hra ?_)
        have hm' : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mL0 ⋆ G)) s.mem := by simpa [hsp] using hm
        exact lowerMemLoad_bodyWp hwf hdLt h6 (by omega) he hr hm' hda hv hLd'
          (fun s' slots' hlen' _ he' hr' hsp' hm'' => fun hra' =>
            lowerContUnpromoted_body_bwp hawf hwf hvwf hcl hcmAddr hspills hEndIjmp hEndHalt
              k l (acc ++ is) tail' (d + 1) (⟨t, v⟩ :: bvs) rw mL0 (by omega) hdMax' hRest
              hbody' hsub hk s' slots' (hlen'.trans hlen) he' hr' hra' (hsp'.trans hsp)
              (by simpa [hsp'.trans hsp] using hm''))
  | .store v a k, l, acc, bodyTail, d, bvs, rw, mL0, s0, s1, blk0, rest,
      h6, hdMax, hlo, hbody, hsub, hbp, s, slots, hlen, he, hr, hra, hsp, hm => by
    dsimp only [lowerContUnpromoted] at hlo
    obtain ⟨is, sMid, hSt, hRest⟩ := lowerM_bind_ok' hlo
    cases hSt' : lowerMemStore b spillBase d v a with
    | error _ =>
      rw [hSt'] at hSt; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hSt; cases hSt
    | ok is_ =>
      rw [hSt'] at hSt; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hSt; cases hSt
      obtain ⟨_, _, tail', hEqC, _, _, hbody'⟩ :=
        lowerContUnpromoted_head_shape b cm cr spillBase ns needFrame k l (acc ++ is) d hRest
      cases hEqC
      have hTailEq : bodyTail = is ++ tail' :=
        List.append_cancel_left (hbody.symm.trans (by simpa [List.append_assoc] using hbody'))
      subst hTailEq
      dsimp only [BlockFlat.wp] at hbp
      cases hdv : denoteArg bvs v <;> rw [hdv] at hbp; · exact False.elim hbp
      cases hda : denoteArg bvs a <;> rw [hda] at hbp; · exact False.elim hbp
      rcases hbp with ⟨hst, hk⟩
      have hdMax' : maxBlockDepth k d ≤ dMax := by simpa [maxBlockDepth] using hdMax
      have hdLe : d ≤ dMax := Nat.le_trans (maxBlockDepth_le k d) hdMax'
      have hNo : ∀ i ∈ is, IsNoRaInstr b i := isNoRa_lowerMemStore b hSt'
      refine bodyWp_append is tail' s (bodyWp_imp_raReg_cont hwf hNo hra ?_)
      have hm' : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mL0 ⋆ G)) s.mem := by simpa [hsp] using hm
      exact lowerMemStore_bodyWp hwf hdLe (by omega) he hr hm' hdv hda hst hSt'
        (fun s' he' hr' hsp' hm'' => fun hra' =>
          lowerContUnpromoted_body_bwp hawf hwf hvwf hcl hcmAddr hspills hEndIjmp hEndHalt
            k l (acc ++ is) tail' d bvs rw _ h6 hdMax' hRest hbody' hsub hk s' slots hlen he'
            hr' hra' (hsp'.trans hsp) (by simpa [hsp'.trans hsp] using hm''))
  | .codeAddr sym k, l, acc, bodyTail, d, bvs, rw, mL0, s0, s1, blk0, rest,
      h6, hdMax, hlo, hbody, hsub, hbp, s, slots, hlen, he, hr, hra, hsp, hm => by
    dsimp only [lowerContUnpromoted] at hlo
    dsimp only [BlockFlat.wp] at hbp; rcases hbp with ⟨a, ha, hk⟩
    have ha' : cm.addrOf? sym = some a := ha
    have hnone : (cm.addrOf? sym).isNone = false := by simp [ha']
    simp only [hnone, Bool.false_eq_true, ↓reduceIte] at hlo
    let is := emitToLoc b.w0 (locOf b spillBase d) fun rd => [.symAddr sym rd]
    obtain ⟨_, _, tail', hEqC, _, _, hbody'⟩ :=
      lowerContUnpromoted_head_shape b cm cr spillBase ns needFrame k l (acc ++ is) (d + 1) hlo
    cases hEqC
    have hTailEq : bodyTail = is ++ tail' :=
      List.append_cancel_left (hbody.symm.trans (by simpa [List.append_assoc] using hbody'))
    rw [hTailEq]
    have hdMax' : maxBlockDepth k (d + 1) ≤ dMax := by simpa [maxBlockDepth] using hdMax
    have hdLt : d < dMax := Nat.lt_of_lt_of_le (Nat.lt_succ_self d)
      (Nat.le_trans (maxBlockDepth_le k (d + 1)) hdMax')
    refine bodyWp_append is tail' s ?_
    have hm' : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mL0 ⋆ G)) s.mem := by simpa [hsp] using hm
    exact lowerCodeAddr_bodyWp hwf hdLt h6 (by omega) (hcmAddr sym a ha') he hr hra hm'
      fun s' slots' hlen' _ he' hr' hra' hsp' hm'' =>
        lowerContUnpromoted_body_bwp hawf hwf hvwf hcl hcmAddr hspills hEndIjmp hEndHalt k l
          (acc ++ is) tail' (d + 1) (⟨i64, a⟩ :: bvs) rw mL0 (by omega) hdMax' hlo hbody' hsub hk
          s' slots' (hlen'.trans hlen) he' hr' hra' (hsp'.trans hsp)
          (by simpa [hsp'.trans hsp] using hm'')
  | .jnz c t e, l, acc, bodyTail, d, bvs, rw, mL0, s0, s1, blk0, rest,
      h6, hdMax, hlo, hbody, hsub, hbp, s, slots, hlen, he, hr, hra, hsp, hm => by
    dsimp only [lowerContUnpromoted] at hlo
    obtain ⟨pC, _, hC, h2⟩ := lowerM_bind_ok' hlo
    cases hC' : loadArgToGpr b spillBase d b.w0 c with
    | error _ =>
      rw [hC'] at hC; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hC; cases hC
    | ok pair =>
      rcases pair with ⟨cc, rc⟩
      rw [hC'] at hC; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hC; cases hC
      obtain ⟨lT, _, _, h3⟩ := lowerM_bind_ok' h2
      obtain ⟨lF, _, _, h4⟩ := lowerM_bind_ok' h3
      obtain ⟨bsT, _, hbsT, h5⟩ := lowerM_bind_ok' h4
      obtain ⟨bsF, _, hbsF, h6'⟩ := lowerM_bind_ok' h5
      dsimp only [Pure.pure, StateT.pure] at h6'; cases h6'
      dsimp only at hbody
      have hTailEq : bodyTail = cc := List.append_cancel_left hbody.symm
      rw [hTailEq]
      dsimp only [BlockFlat.wp] at hbp
      cases hdc : denoteArg bvs c <;> rw [hdc] at hbp; · exact False.elim hbp
      rename_i c'; rcases hbp with ⟨hbt, hbf⟩
      have hNo : ∀ i ∈ cc, IsNoRaInstr b i := isNoRa_loadArgToGpr b (work_mem_allRegs b).2.1 hC'
      have hdMaxT : maxBlockDepth t d ≤ dMax :=
        Nat.le_trans (Nat.le_max_left _ _) (by simpa [maxBlockDepth] using hdMax)
      have hdMaxF : maxBlockDepth e d ≤ dMax :=
        Nat.le_trans (Nat.le_max_right _ _) (by simpa [maxBlockDepth] using hdMax)
      have hsubT : ∀ x ∈ bsT, x ∈ vcm.blocks := fun x hx =>
        hsub x (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      have hsubF : ∀ x ∈ bsF, x ∈ vcm.blocks := fun x hx =>
        hsub x (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
      refine bodyWp_imp_raReg_mono hwf hNo hra (loadArgToGpr_bodyWp hwf (w_mem_workRegs b).1 he hdc
        (by simpa [hsp] using hm) hC' fun s1 hs1_ne hv1 hm1 he1 =>
          And.intro hs1_ne (And.intro hv1 (And.intro hm1 he1)))
        fun s1 ⟨hs1_ne, hv1, hm1, he1⟩ hra1 => ?_
      have hsp1 : s1.gpr A.abi.sp = hwSp := (hs1_ne A.abi.sp (work_not_sp hwf).2.1.symm).trans hsp
      have hr1 := wordRegsRel_updWork hwf hr b.w0 (w_mem_workRegs b).1 hs1_ne
      have hnz : ((s1.gpr rc).setWidth 8 != 0#8) = c'.val := valHolds64_bool_nonzero hv1
      refine termWp_jnzGpr (fun htr => ?_) (fun hfl => ?_)
      · obtain ⟨blkT, restT, tailT, rfl, hlblT, _, hbodyT⟩ :=
          lowerContUnpromoted_head_shape b cm cr spillBase ns needFrame t lT [] d hbsT
        have hbwT := lowerContUnpromoted_body_bwp hawf hwf hvwf hcl hcmAddr hspills hEndIjmp
          hEndHalt t lT [] tailT d bvs rw mL0 h6 hdMaxT hbsT hbodyT hsubT (hbt (hnz ▸ htr))
          (s1.setFlags (A.jnzGprFlags (s1.gpr rc) s1.flags)) slots hlen
          ((envRel_setFlags _ _ _ _ _ _).mpr he1) ((wordRegsRel_setFlags _ _ _ _).mpr hr1)
          (fun h => (raReg_setFlags A _ _ _).mpr (hra1 h)) hsp1 (by simpa [hsp1, hm1] using hm)
        exact hlblT ▸ closed_bwp hvwf hcl (hsubT blkT List.mem_cons_self)
          ((List.nil_append tailT ▸ hbodyT) ▸ hbwT)
      · obtain ⟨blkF, restF, tailF, rfl, hlblF, _, hbodyF⟩ :=
          lowerContUnpromoted_head_shape b cm cr spillBase ns needFrame e lF [] d hbsF
        have hbwF := lowerContUnpromoted_body_bwp hawf hwf hvwf hcl hcmAddr hspills hEndIjmp
          hEndHalt e lF [] tailF d bvs rw mL0 h6 hdMaxF hbsF hbodyF hsubF (hbf (hnz ▸ hfl))
          (s1.setFlags (A.jnzGprFlags (s1.gpr rc) s1.flags)) slots hlen
          ((envRel_setFlags _ _ _ _ _ _).mpr he1) ((wordRegsRel_setFlags _ _ _ _).mpr hr1)
          (fun h => (raReg_setFlags A _ _ _).mpr (hra1 h)) hsp1 (by simpa [hsp1, hm1] using hm)
        exact hlblF ▸ closed_bwp hvwf hcl (hsubF blkF List.mem_cons_self)
          ((List.nil_append tailF ▸ hbodyF) ▸ hbwF)
  | .ijmp tgt nxt, l, acc, bodyTail, d, bvs, rw, mL0, s0, s1, blk0, rest,
      _, hdMax, hlo, hbody, _, hbp, s, slots, hlen, he, _, hra, hsp, hm => by
    dsimp only [lowerContUnpromoted] at hlo
    obtain ⟨ctgt, _, hT, h2⟩ := lowerM_bind_ok' hlo
    cases hT' : loadArgInto b spillBase d b.w0 tgt with
    | error _ =>
      rw [hT'] at hT; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hT; cases hT
    | ok ctgt_ =>
      rw [hT'] at hT; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hT; cases hT
      obtain ⟨cnxt, _, hN, h3⟩ := lowerM_bind_ok' h2
      cases hN' : emitNextRegs b spillBase d nxt with
      | error _ =>
        rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
      | ok cnxt_ =>
        rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
        dsimp only [Pure.pure, StateT.pure] at h3; cases h3
        let ep : List (Instr A) := if needFrame then [.epilogue ns] else []
        have hTailEq : bodyTail = ctgt ++ cnxt ++ ep := by
          have h := hbody.symm; dsimp only at h
          simp only [List.append_assoc, ep] at h ⊢; exact List.append_cancel_left h
        rw [hTailEq, List.append_assoc]
        dsimp only [BlockFlat.wp] at hbp
        cases hdt : denoteArg bvs tgt <;> rw [hdt] at hbp; · exact False.elim hbp
        cases hdn : denoteRegsExpr bvs nxt <;> rw [hdn] at hbp; · exact False.elim hbp
        rename_i tgt' nxt'
        have hwk := w_mem_workRegs b; have hwne := wordRegBind_work_ne hwf
        have hNoT : ∀ i ∈ ctgt, IsNoRaInstr b i := isNoRa_loadArgInto b (work_mem_allRegs b).2.1 hT'
        have hNoN : ∀ i ∈ cnxt, IsNoRaInstr b i := isNoRa_emitNextRegs b hN'
        refine bodyWp_append ctgt (cnxt ++ ep) s (bodyWp_imp_raReg_mono hwf hNoT hra
          (loadArgInto_bodyWp hawf hwf hwk.1 he hdt (by simpa [hsp] using hm) hT'
            fun s1 hs1_ne hv1 hm1 he1 => And.intro hs1_ne (And.intro hv1 (And.intro hm1 he1)))
          fun s1 ⟨hs1_ne, hv1, hm1, he1⟩ hra1 => ?_)
        have hsp1 : s1.gpr A.abi.sp = hwSp := (hs1_ne A.abi.sp (work_not_sp hwf).2.1.symm).trans hsp
        have hslots1 : ∀ lvl < d, ∀ j, locOf b spillBase lvl = .slot j → j < slots.length :=
          envRel_slots_bound b (by simpa [maxBlockDepth] using hdMax) (by omega)
        refine bodyWp_append cnxt ep s1 (bodyWp_imp_raReg_mono hwf hNoN hra1
          (emitNextRegs_bodyWp hawf hwf he1 hdn (by simpa [hsp1, hm1] using hm) hslots1 hN'
            fun s2 hr2 hs2_ne hm2 => And.intro hr2 (And.intro hs2_ne hm2))
          fun s2 ⟨hr2, hs2_ne, hm2⟩ hra2 => ?_)
        have hsp2 : s2.gpr A.abi.sp = hwSp :=
          (hs2_ne A.abi.sp (fun hm' => (wordRegs_not_sp_ra hwf).1 _ hm' |>.1 rfl)
            (work_not_sp hwf).2.2.1.symm).trans hsp1
        have hw0_eq : s2.gpr b.w0 = tgt'.val := by
          have hw0_1 := hs2_ne b.w0 (fun hm' => (wordRegs_not_sp_ra hwf).2 _ hm' |>.2.1 rfl)
            hwne.2.2.2.1
          dsimp only [ValHolds64] at hv1
          exact hw0_1.trans (by simpa [BitVec.setWidth_eq] using hv1.2)
        refine bodyWp_mono (fun s' h => termWp_ijmp h) ?_
        exact hEndIjmp s2 tgt'.val nxt'.eval mL0 slots hlen hw0_eq hr2 hra2 hsp2
          (by simpa [hm2, hm1] using hm) hbp
  | .halt code, l, acc, bodyTail, d, bvs, rw, mL0, s0, s1, blk0, rest,
      _, _, hlo, hbody, _, hbp, s, slots, hlen, he, _, hra, hsp, hm => by
    dsimp only [lowerContUnpromoted] at hlo
    obtain ⟨ccode, _, hC, h2⟩ := lowerM_bind_ok' hlo
    cases hC' : loadArgInto b spillBase d b.w0 code with
    | error _ =>
      rw [hC'] at hC; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hC; cases hC
    | ok ccode_ =>
      rw [hC'] at hC; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hC; cases hC
      dsimp only [Pure.pure, StateT.pure] at h2; cases h2
      let ep : List (Instr A) := if needFrame then [.epilogue ns] else []
      have hTailEq : bodyTail = ccode ++ ep := by
        have h := hbody.symm; dsimp only at h
        simp only [List.append_assoc, ep] at h ⊢; exact List.append_cancel_left h
      rw [hTailEq, List.append_assoc]
      dsimp only [BlockFlat.wp] at hbp
      cases hdc : denoteArg bvs code <;> rw [hdc] at hbp; · exact False.elim hbp
      rename_i c'
      have hNo : ∀ i ∈ ccode, IsNoRaInstr b i := isNoRa_loadArgInto b (work_mem_allRegs b).2.1 hC'
      refine bodyWp_append ccode ep s (bodyWp_imp_raReg_mono hwf hNo hra
        (loadArgInto_bodyWp hawf hwf (w_mem_workRegs b).1 he hdc (by simpa [hsp] using hm) hC'
          fun s1 hs1_ne hv1 hm1 he1 => And.intro hs1_ne (And.intro hv1 (And.intro hm1 he1)))
        fun s1 ⟨hs1_ne, hv1, hm1, _⟩ _ => ?_)
      have hsp1 : s1.gpr A.abi.sp = hwSp := (hs1_ne A.abi.sp (work_not_sp hwf).2.1.symm).trans hsp
      have hw0_eq : s1.gpr b.w0 = c'.val := by
        dsimp only [ValHolds64] at hv1; simpa [BitVec.setWidth_eq] using hv1.2
      refine bodyWp_mono (fun s' h => termWp_halt h) ?_
      exact hEndHalt s1 c'.val mL0 slots hlen hw0_eq hsp1 (by simpa [hm1] using hm) hbp
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _, hlo, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [lowerContUnpromoted, liftEx, StateT.lift, StateT.run, Except.map] at hlo
    cases hlo

theorem lowerContUnpromoted_bwp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {vcm : VllCodeMap A} (hvwf : vcm.Wf)
    {cr : ContifyRegion} {spillBase ns ns_ dMax : Nat} {needFrame : Bool}
    {hwSp ra₀ : BitVec 64} {G : Mem 64 → Prop} {Ψ_L0 : BedrockWord.CodeSpec} {H_L0 : HaltPost}
    {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hcl : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (hcmAddr : ∀ sym a, cm.addrOf? sym = some a → vcm.symAddr sym = a)
    (hspills : spillBase + tempSpillCount b dMax ≤ ns_)
    (hEndIjmp : ∀ s_fin (tgtVal : BitVec 64) (nxt' : Regs) (m' : Mem 64)
      (slots' : List (BitVec 64)),
      slots'.length = ns_ →
      s_fin.gpr b.w0 = tgtVal →
      WordRegsRel b nxt' s_fin →
      (needFrame = false → (vllFramePreds A).raReg s_fin ra₀) →
      s_fin.gpr A.abi.sp = hwSp →
      (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
      Ψ_L0 tgtVal ⟨nxt', m'⟩ →
      bodyWp A vcm.symAddr (if needFrame then [.epilogue ns] else [])
        (fun s' => Ψ_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin)
    (hEndHalt : ∀ s_fin (cVal : BitVec 64) (m' : Mem 64) (slots' : List (BitVec 64)),
      slots'.length = ns_ →
      s_fin.gpr b.w0 = cVal →
      s_fin.gpr A.abi.sp = hwSp →
      (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
      H_L0 cVal m' →
      bodyWp A vcm.symAddr (if needFrame then [.epilogue ns] else [])
        (fun s' => H_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin)
    (blk : BlockFlat) (curLbl : Sym) (acc : List (Instr A)) (d : Nat)
    (bvs : List ((t : Ty) × Val t)) (rw : Regs) (mL0 : Mem 64)
    {s0 s1 : Nat} {bs : List (Block A)} (s_entry : MachSt A)
    (h6 : 6 ≤ d) (hdMax : maxBlockDepth blk d ≤ dMax)
    (hlo : (lowerContUnpromoted b cm cr spillBase ns needFrame curLbl acc d blk).run s0 =
      .ok (bs, s1))
    (hsub : ∀ x ∈ bs, x ∈ vcm.blocks)
    (hbp : blk.wp cm.symEnv Ψ_L0 H_L0 bvs mL0)
    (hacc : bodyWp A vcm.symAddr acc (fun s => ∃ slots : List (BitVec 64),
      slots.length = ns_ ∧
      EnvRel b spillBase d bvs s ∧ WordRegsRel b rw s ∧
      (needFrame = false → (vllFramePreds A).raReg s ra₀) ∧
      s.gpr A.abi.sp = hwSp ∧
      (array64 hwSp slots ⋆ (Eq mL0 ⋆ G)) s.mem) Ψ_L1 H_L1 s_entry) :
    Ψ_L1 (vcm.symAddr curLbl) s_entry := by
  obtain ⟨blk0, rest, bodyTail, rfl, hlbl, _, hbody⟩ :=
    lowerContUnpromoted_head_shape b cm cr spillBase ns needFrame blk curLbl acc d hlo
  refine hlbl ▸ closed_bwp hvwf hcl (hsub blk0 List.mem_cons_self) ?_
  rw [hbody]
  refine bodyWp_append acc bodyTail s_entry (bodyWp_mono (fun s hs => ?_) hacc)
  rcases hs with ⟨slots, hlen, he, hr, hra, hsp, hm⟩
  exact lowerContUnpromoted_body_bwp hawf hwf hvwf hcl hcmAddr hspills hEndIjmp hEndHalt blk curLbl
    acc bodyTail d bvs rw mL0 h6 hdMax hlo hbody hsub hbp s slots hlen he hr hra hsp hm

end LeanQbe.T.Vll
