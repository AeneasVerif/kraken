module

public import LeanQbe.T.MainLemmas
public import LeanQbe.T.MainSplice
public import LeanQbe.T.FlatLemmas
import LeanQbe.T.RegaLemmas3
public import LeanQbeTest.T.RegaLitmusTarget
public meta import Lean
public meta import LeanQbe.T.MainSplice
public meta import LeanQbeTest.T.RegaLitmusTarget

/-!
# End-to-End Driver, `Compiled` Certificate Harness, & `TargetInit` Test

Verifies `LeanQbe.T.Main` and `LeanQbe.T.MainLemmas` above `RegaLitmus.litmusTarget` (with no
legacy untyped-IR or target-specific architecture imports):
1. `litmusLabelClean : Rega.LabelClean litmusTarget.toIsa` (`Rega.NoLab` on every ISA snippet).
2. `litmusLayout : TargetLayout litmusTarget` (structural `ofClean` + explicit `labelsNodupBy` check).
3. `litmusInit : TargetInit litmusTarget` (general `setAbiRegs` over all legal `as : List Ty` +
   `stackZeros` / `raBytes` / `bsMem` at `0x1000#64` with `sp0 = 0x0ff8#64`).
4. 2-function caller+callee module `litmusMod` (`inc` + `caller`), `checkAcyclic = true` by `rfl`,
   external `splice_module_hints`, single `checkCompile ... = true` by `t_kernel_rfl`,
   `Compiled.fnSpec_host_src`, concrete `TargetInit.run_ret1` / `run_ret1_i64` / `run_ret1_sep_i64`
   execution witnesses, and `#print axioms` audit (`[propext, Classical.choice, Quot.sound]` only).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.MainTest

open LeanQbe.T LeanQbe.T.RegaLitmus Std Std.ExtHashMap Kraken.Bedrock2.Test

/-! ## 1. `Rega.LabelClean litmusTarget.toIsa` -/

private def isNoLabel (c : List Instr) : Bool :=
  c.all fun | .label _ => false | _ => true

private theorem noLab_of_bool {c : List Instr} (h : isNoLabel c = true) :
    Rega.NoLab litmusTarget.toIsa c := fun l hl => by
  have hmem := List.all_eq_true.mp h (Instr.label l) hl
  simp at hmem

private theorem noLab_binArm {k n d} {a b : PArg Nat Nat Cond (.bits n)} {c cl}
    (h : binArm k n d a b = some (c, cl)) : Rega.NoLab litmusTarget.toIsa c := by
  simp only [binArm] at h
  split at h
  · cases ha : srcOf a <;> cases hb : srcOf b <;> simp [ha, hb] at h
    rcases h with ⟨rfl, _⟩; exact noLab_of_bool rfl
  · cases h

private theorem noLab_boolArm {k d} {a b : PArg Nat Nat Cond .bool} {c cl}
    (h : boolArm k d a b = some (c, cl)) : Rega.NoLab litmusTarget.toIsa c := by
  simp only [boolArm] at h
  cases ha : srcOfBool a <;> cases hb : srcOfBool b <;> simp [ha, hb] at h
  rcases h with ⟨rfl, _⟩; exact noLab_of_bool rfl

private theorem noLab_addArm {n d} {a b : PArg Nat Nat Cond (.bits n)} {vh c cl}
    (h : addArm n d a b vh = some (c, cl)) : Rega.NoLab litmusTarget.toIsa c := by
  unfold addArm at h
  split at h
  · split at h
    · injection h with h'; have h'' := congrArg Prod.fst h'; subst h''
      exact noLab_of_bool rfl
    · cases h
  · exact noLab_binArm h

private theorem noLab_subArm {n d} {a b : PArg Nat Nat Cond (.bits n)} {vh c cl}
    (h : subArm n d a b vh = some (c, cl)) : Rega.NoLab litmusTarget.toIsa c := by
  unfold subArm at h
  split at h
  · split at h
    · cases ha : srcOf a <;> simp [ha] at h
      rcases h with ⟨rfl, _⟩; exact noLab_of_bool rfl
    · cases h
  · exact noLab_binArm h

private theorem noLab_cmpArm {o n} {a b : PArg Nat Nat Cond (.bits n)} {dst vh c cl}
    (h : cmpArm o n a b dst vh = some (c, cl)) : Rega.NoLab litmusTarget.toIsa c := by
  unfold cmpArm at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases ha : srcOf a <;> simp [ha] at h
        rcases h with ⟨rfl, _⟩; exact noLab_of_bool rfl
      · cases h
    · cases hco : cmpCond o <;> cases ha : srcOf a <;> cases hb : srcOf b <;>
        simp [hco, ha, hb] at h
      cases dst <;> simp at h
      · rcases h with ⟨rfl, _⟩; exact noLab_of_bool rfl
      · rcases h with ⟨_, rfl, _⟩; exact noLab_of_bool rfl

private theorem noLab_addcArm {n d} {a b : PArg Nat Nat Cond (.bits n)} {cin cout vh c cl}
    (h : addcArm n d a b cin cout vh = some (c, cl)) : Rega.NoLab litmusTarget.toIsa c := by
  unfold addcArm at h
  split at h
  · cases h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨sa, _, sb, _, h⟩ := h
    split at h
    · rcases h with ⟨rfl, _⟩; exact noLab_of_bool rfl
    · rcases h with ⟨rfl, _⟩; exact noLab_of_bool rfl
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨m, hm, p, hp, heq⟩ := h
      injection heq with hc _; subst hc
      refine Rega.NoLab.append ?_ ?_
      · split at hm <;> simp at hm <;> (cases hm; exact noLab_of_bool rfl)
      · split at hp <;> simp at hp
        · cases hp; exact noLab_of_bool rfl
        · rcases hp with ⟨_, rfl⟩; exact noLab_of_bool rfl
    · cases h

private theorem noLab_gop {sig rs} (code : OpCode sig rs) pas dsts vh c cl
    (h : gop code pas dsts vh = some (c, cl)) : Rega.NoLab litmusTarget.toIsa c := by
  unfold gop at h
  split at h <;> first
    | exact noLab_addArm h | exact noLab_subArm h | exact noLab_binArm h
    | exact noLab_boolArm h | exact noLab_cmpArm h | exact noLab_addcArm h | cases h

private theorem noLab_vop {sig rs} (code : OpCode sig rs) pas dsts vh c cl
    (h : vop code pas dsts vh = some (c, cl)) : Rega.NoLab litmusTarget.toIsa c := by
  unfold vop at h
  split at h
  case h_6 => cases h
  all_goals
    simp only [vbinArm] at h; split at h <;> simp at h; exact noLab_of_bool (h.1 ▸ rfl)

/-- Every emitted directive of `litmusTarget.toIsa` is label-free and `.label` is injective. -/
theorem litmusLabelClean : Rega.LabelClean litmusTarget.toIsa where
  label_inj _ _ h := Instr.label.inj h
  mov _ _ := noLab_of_bool rfl
  movi _ _ := noLab_of_bool rfl
  setcc _ _ := noLab_of_bool rfl
  jmp _ := noLab_of_bool rfl
  jcc _ _ := noLab_of_bool rfl
  jnzGpr _ _ := noLab_of_bool rfl
  op := noLab_gop
  load t r a c cl h := by
    simp only [litmusTarget, gprIsa, gprLoad] at h
    split at h <;> simp at h; rcases h with ⟨rfl, _⟩; exact noLab_of_bool rfl
  store t pa a c cl h := by
    simp only [litmusTarget, gprIsa, gprStore] at h
    split at h <;> cases pa <;> simp at h <;> rcases h with ⟨rfl, _⟩ <;> exact noLab_of_bool rfl
  clearFlags := noLab_of_bool rfl
  vmov _ _ _ := noLab_of_bool rfl
  vmovi _ _ _ _ h := by
    simp only [litmusTarget, vecIsa] at h; cases h; exact noLab_of_bool rfl
  vslotSt _ _ _ := noLab_of_bool rfl
  vslotLd _ _ _ := noLab_of_bool rfl
  vop := noLab_vop
  vload _ _ _ _ _ h := by simp [litmusTarget, vecIsa] at h
  vstore _ _ _ _ _ h := by simp [litmusTarget, vecIsa] at h
  prologue _ := noLab_of_bool rfl
  epilogue _ := noLab_of_bool rfl
  slotSt _ _ := noLab_of_bool rfl
  slotLd _ _ := noLab_of_bool rfl
  canonAbi t r := by
    cases t <;> dsimp [litmusTarget, frameIsa, canonAbi] <;>
      first | exact noLab_of_bool rfl | (split <;> exact noLab_of_bool rfl)
  call _ := noLab_of_bool rfl
  exitJmp _ := noLab_of_bool rfl
  ret := noLab_of_bool rfl

/-! ## 2. `TargetLayout litmusTarget` -/

/-- Structural `TargetLayout` relying on `litmusLabelClean` (`checkCompile` / `compileChecked`). -/
def litmusLayout : TargetLayout litmusTarget :=
  TargetLayout.ofClean
    (fun prog => Nat.ble (prog.length + 1) (2 ^ 64))
    (fun prog h => ⟨prog, Nat.lt_of_succ_le (Nat.le_of_ble_eq_true h)⟩)
    (fun _ _ => rfl)

def progLabelsOk (prog : List Instr) : Bool :=
  (List.range prog.length).all fun i =>
    match prog[i]? with
    | some (.label l) => (prog.findIdx? (· == Instr.label l)) == some i
    | _ => true

theorem progLabelsOk_unique {prog : List Instr} (hok : progLabelsOk prog = true) :
    ∀ (i j : Nat) (l : Sym), prog[i]? = some (Instr.label l) →
      prog[j]? = some (Instr.label l) → i = j := by
  have first : ∀ {k : Nat} {l : Sym}, prog[k]? = some (Instr.label l) →
      prog.findIdx? (· == Instr.label l) = some k := fun {k l} hk => by
    have hlt : k < prog.length := by
      rcases Nat.lt_or_ge k prog.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hk; cases hk
    have ha := List.all_eq_true.mp hok k (List.mem_range.mpr hlt)
    rw [hk] at ha; exact beq_iff_eq.mp ha
  intro i j l hi hj
  exact Option.some.inj ((first hi).symm.trans (first hj))

/-- Secondary `TargetLayout` also providing `labelsNodup` (`checkCompileWithLabels`). -/
def litmusLayoutWithLabels : TargetLayout litmusTarget where
  progSmall prog := Nat.ble (prog.length + 1) (2 ^ 64)
  layoutOf prog h := ⟨prog, Nat.lt_of_succ_le (Nat.le_of_ble_eq_true h)⟩
  prog_layoutOf _ _ := rfl
  labelsNodup := progLabelsOk
  labelsUnique_layoutOf _ hnod i j l hi hj := progLabelsOk_unique hnod i j l hi hj

/-! ## 3. `TargetInit litmusTarget` -/

def setAbiRegs (sp0 : BitVec 64) :
    {ts : List Ty} → Tup (AbiReg Nat Nat) ts → Tup Val ts →
    (Nat → BitVec 64) × (Nat → BitVec 512)
  | [], _, _ => (fun r => if r = 4 then sp0 else 0, fun _ => 0)
  | t :: _, (loc, locs), (v, vs) =>
    let p := setAbiRegs sp0 locs vs
    match loc with
    | .gpr r => (fun x => if x = r then valToGpr t v else p.1 x, p.2)
    | .vec vr => (p.1, fun x => if x = vr then (toBits t v).setWidth 512 else p.2 x)

private theorem pair_size_le_512 {a b : Ty} (h : vecIsa.isAbiVec (.pair a b) = true) :
    (Ty.pair a b).size ≤ 512 := Nat.le_of_not_lt fun hlt => by
  simp [vecIsa, vecSlotWidth, show ¬ (Ty.pair a b).size ≤ 64 by omega,
    show ¬ (Ty.pair a b).size ≤ 128 by omega, show ¬ (Ty.pair a b).size ≤ 256 by omega,
    show ¬ (Ty.pair a b).size ≤ 512 by omega] at h

private theorem setWidth_512_cancel {n : Nat} (hn : n ≤ 512) (x : BitVec n) :
    (x.setWidth 512).setWidth n = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [show (i : Nat) < 512 by omega, hi]

private theorem assignSig_cons {t : Ty} {ts : List Ty} {loc : AbiReg Nat Nat t}
    {locs : Tup (AbiReg Nat Nat) ts} {gs vs : List Nat}
    (h : isa.assignSig (t :: ts) gs vs = some (loc, locs)) :
    match loc with
    | .gpr r => ∃ gs', gs = r :: gs' ∧ isa.assignSig ts gs' vs = some locs ∧
        (t = .bool ∨ ∃ n, t = .bits n ∧ n ≤ 64)
    | .vec vr => ∃ vs' a b, t = .pair a b ∧ vs = vr :: vs' ∧
        isa.assignSig ts gs vs' = some locs ∧ (Ty.pair a b).size ≤ 512 := by
  cases t with
  | bool =>
    cases gs with
    | nil => simp [Isa.assignSig] at h
    | cons r0 gs' =>
      simp only [Isa.assignSig, Option.map_eq_some_iff] at h
      obtain ⟨locs', h', hloc⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hloc
      exact ⟨gs', rfl, h', Or.inl rfl⟩
  | bits n =>
    cases gs with
    | nil => simp [Isa.assignSig] at h
    | cons r0 gs' =>
      simp only [Isa.assignSig, isa, frameIsa] at h
      cases hbw : [8, 16, 32, 64].contains n
      · simp only [hbw, Bool.false_eq_true, ↓reduceIte] at h; cases h
      · simp only [hbw, ↓reduceIte, Option.map_eq_some_iff] at h
        obtain ⟨locs', h', hloc⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hloc
        have hle : n ≤ 64 := by
          simp only [List.contains_eq_mem, List.mem_cons,
            List.not_mem_nil, or_false, decide_eq_true_eq] at hbw
          rcases hbw with rfl | rfl | rfl | rfl <;> decide
        exact ⟨gs', rfl, h', Or.inr ⟨n, rfl, hle⟩⟩
  | float _ => simp [Isa.assignSig] at h
  | pair a b =>
    cases vs with
    | nil => simp [Isa.assignSig] at h
    | cons vr0 vs' =>
      simp only [Isa.assignSig, isa] at h
      cases hvec : vecIsa.isAbiVec (.pair a b)
      · simp only [hvec, Bool.false_eq_true, ↓reduceIte] at h; cases h
      · simp only [hvec, ↓reduceIte, Option.map_eq_some_iff] at h
        obtain ⟨locs', h', hloc⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hloc
        exact ⟨vs', a, b, rfl, rfl, h', pair_size_le_512 hvec⟩

private theorem setAbiRegs_get_sp {sp0 : BitVec 64} :
    ∀ {ts : List Ty} {locs : Tup (AbiReg Nat Nat) ts} {args : Tup Val ts} {gs vs : List Nat},
      4 ∉ gs → isa.assignSig ts gs vs = some locs → (setAbiRegs sp0 locs args).1 4 = sp0
  | [], (), (), _, _, _, _ => rfl
  | t :: ts, (loc, locs), (_, vs), gs, vs', hsp, h => by
    have hc := assignSig_cons h
    cases loc with
    | gpr r =>
      obtain ⟨gs', rfl, h', _⟩ := hc
      have hne : (4 : Nat) ≠ r := fun e => hsp (e ▸ List.mem_cons_self)
      simp [setAbiRegs, hne, setAbiRegs_get_sp (fun hm => hsp (List.mem_cons_of_mem _ hm)) h']
    | vec vr =>
      obtain ⟨vs'', _, _, rfl, rfl, h', _⟩ := hc
      simp [setAbiRegs, setAbiRegs_get_sp hsp h']

private theorem abi_frame {g g' : Nat → BitVec 64} {vf vf' : Nat → BitVec 512} :
    ∀ {ts : List Ty} {locs : Tup (AbiReg Nat Nat) ts} {args : Tup Val ts} {gs vs : List Nat},
      (∀ r ∈ gs, g' r = g r) → (∀ vr ∈ vs, vf' vr = vf vr) → isa.assignSig ts gs vs = some locs →
      TRel (fun t loc val => match loc with
        | .gpr r => AbiGprHolds (g r) t val
        | .vec vr => VecHolds (vf vr) t val) locs args →
      TRel (fun t loc val => match loc with
        | .gpr r => AbiGprHolds (g' r) t val
        | .vec vr => VecHolds (vf' vr) t val) locs args
  | [], (), (), _, _, _, _, _, _ => .nil
  | _ :: _, (loc, _), (_, _), _, _, hg, hv, h, hrel => by
    cases hrel with
    | cons h1 h2 =>
      have hc := assignSig_cons h
      cases loc with
      | gpr r =>
        obtain ⟨_, rfl, h', _⟩ := hc
        exact .cons (by simpa [hg r List.mem_cons_self] using h1)
          (abi_frame (fun x hm => hg x (List.mem_cons_of_mem _ hm)) hv h' h2)
      | vec vr =>
        obtain ⟨_, _, _, rfl, rfl, h', _⟩ := hc
        exact .cons (by simpa [hv vr List.mem_cons_self] using h1)
          (abi_frame hg (fun x hm => hv x (List.mem_cons_of_mem _ hm)) h' h2)

private theorem setAbiRegs_holds (sp0 : BitVec 64) :
    ∀ {ts : List Ty} {locs : Tup (AbiReg Nat Nat) ts} {args : Tup Val ts} {gs vs : List Nat},
      gs.Nodup → vs.Nodup → isa.assignSig ts gs vs = some locs →
      TRel (fun t loc val => match loc with
        | .gpr r => AbiGprHolds ((setAbiRegs sp0 locs args).1 r) t val
        | .vec vr => VecHolds ((setAbiRegs sp0 locs args).2 vr) t val) locs args
  | [], (), (), _, _, _, _, _ => .nil
  | t :: ts, (loc, locs), (v, vs), gs, vs', hgs, hvs, h => by
    have hc := assignSig_cons h
    cases loc with
    | gpr r =>
      obtain ⟨gs', rfl, h', hty⟩ := hc
      obtain ⟨hnmem, hgs'⟩ := List.nodup_cons.mp hgs
      have hhead :
          AbiGprHolds ((setAbiRegs (ts := t :: ts) sp0 (AbiReg.gpr r, locs) (v, vs)).1 r) t v := by
        rcases hty with rfl | ⟨n, rfl, hn⟩
        · simp [setAbiRegs, valToGpr, AbiGprHolds]
        · simp [setAbiRegs, valToGpr, AbiGprHolds, hn]
      exact .cons hhead (abi_frame
        (fun x hx => by simp only [setAbiRegs, show ¬ x = r from fun e => hnmem (e ▸ hx), ite_false])
        (fun _ _ => rfl) h' (setAbiRegs_holds sp0 hgs' hvs h'))
    | vec vr =>
      obtain ⟨vs'', a, b, rfl, rfl, h', hsz⟩ := hc
      obtain ⟨hnmem, hvs'⟩ := List.nodup_cons.mp hvs
      have hhead :
          VecHolds
            ((setAbiRegs (ts := .pair a b :: ts) sp0 (AbiReg.vec vr, locs) (v, vs)).2 vr)
            (.pair a b) v := by
        simp only [setAbiRegs, ↓reduceIte, VecHolds, hsz, true_and]
        exact setWidth_512_cancel hsz (toBits (.pair a b) v)
      exact .cons hhead (abi_frame (fun _ _ => rfl)
        (fun x hx => by simp only [setAbiRegs, show ¬ x = vr from fun e => hnmem (e ▸ hx), ite_false])
        h' (setAbiRegs_holds sp0 hgs hvs' h'))

def litmusInitMem (n : Nat) (bs : List UInt8) : Mem 64 :=
  ((stackZeros n ++ Int.toBytes 8 (BitVec.ofNat 64 0x1234).toInt) ++ bs).At
    (0x0ff8#64 - BitVec.ofNat 64 n)

def litmusInitState (n : Nat) (bs : List UInt8) {as : List Ty} (args : Tup Val as) :
    MData :=
  let rv :=
    match litmusTarget.toIsa.assignArgs as with
    | some locs => setAbiRegs 0x0ff8#64 locs args
    | none => (fun r => if r = 4 then 0x0ff8#64 else 0, fun _ => 0)
  ⟨rv.1, rv.2, false, false, false, litmusInitMem n bs⟩

private theorem trel_imp {P Q : ∀ t, AbiReg Nat Nat t → Val t → Prop}
    (h : ∀ t a v, P t a v → Q t a v) :
    ∀ {ts : List Ty} {xs : Tup (AbiReg Nat Nat) ts} {ys : Tup Val ts},
      TRel P xs ys → TRel Q xs ys
  | [], _, _, .nil => .nil
  | _ :: _, _, _, .cons hx hxs => .cons (h _ _ _ hx) (trel_imp h hxs)

/-- Closed initial-state provider for `RegaLitmus.litmusTarget` (`sp0 = 0x0ff8#64`, `ra0 = 0x1234`,
mapping user data `bs` right after the return address at `0x1000#64`). -/
def litmusInit : TargetInit litmusTarget where
  sp0 := 0x0ff8#64
  ra0 := (0x1234 : Nat)
  ret0 := 0
  arg0 := 7
  initState := litmusInitState
  get_sp := fun n bs {as} args => by
    simp only [litmusTarget, mach, frameIsa, litmusInitState]
    cases h : isa.assignArgs as with
    | none => rfl
    | some locs => exact setAbiRegs_get_sp (by decide) h
  argsIn := fun n bs {as} args his => by
    obtain ⟨locs, hlocs⟩ := Option.isSome_iff_exists.mp his
    refine ⟨locs, hlocs, ?_⟩
    simp only [litmusTarget, litmusInitState, hlocs]
    exact trel_imp (fun t loc v h => by cases loc <;> exact h)
      (setAbiRegs_holds 0x0ff8#64 (args := args) (by decide) (by decide) hlocs)
  raReg := fun _ _ {_} _ => trivial
  spEntry := trivial
  mem_entry := fun n bs {_} _ hn hbs => by
    let ra : List UInt8 := Int.toBytes 8 (BitVec.ofNat 64 0x1234).toInt
    have hra : ra.length = 8 := Int.toBytes_length 8 _
    have hzs : (stackZeros n).length = n := stackZeros_length n
    have hsp : (0x0ff8#64 - BitVec.ofNat 64 n) + BitVec.ofNat 64 n = 0x0ff8#64 :=
      BitVec.sub_add_cancel _ _
    have h1000 : (0x0ff8#64 : BitVec 64) + BitVec.ofNat 64 8 = 0x1000#64 := by decide
    have hlen1 : (stackZeros n).length + (ra ++ bs).length ≤ 2 ^ 64 := by
      rw [hzs, List.length_append, hra]
      exact Nat.le_trans (Nat.add_le_add hn (Nat.add_le_add_left hbs 8)) (by decide)
    have hlen2 : ra.length + bs.length ≤ 2 ^ 64 := by
      rw [hra]
      exact Nat.le_trans (Nat.add_le_add_left hbs 8) (by decide)
    have h1 : Eq ((stackZeros n ++ (ra ++ bs)).At (0x0ff8#64 - BitVec.ofNat 64 n)) =
        (Eq ((stackZeros n).At (0x0ff8#64 - BitVec.ofNat 64 n)) ⋆
          Eq ((ra ++ bs).At 0x0ff8#64)) := by
      have e := eq_append_At (0x0ff8#64 - BitVec.ofNat 64 n) (stackZeros n) (ra ++ bs) hlen1
      rwa [hzs, hsp] at e
    have h2 : Eq ((ra ++ bs).At 0x0ff8#64) =
        (Eq (ra.At 0x0ff8#64) ⋆ Eq (bs.At 0x1000#64)) := by
      have e := eq_append_At 0x0ff8#64 ra bs hlen2
      rwa [hra, h1000] at e
    have hmem : (Eq (bs.At 0x1000#64) ⋆
        (Eq ((stackZeros n).At (0x0ff8#64 - BitVec.ofNat 64 n)) ⋆ Eq (ra.At 0x0ff8#64)) ⋆
        emp) (litmusInitMem n bs) := by
      refine sep_cast (show Eq (litmusInitMem n bs) (litmusInitMem n bs) from rfl) ?_
      change Eq ((stackZeros n ++ ra ++ bs).At (0x0ff8#64 - BitVec.ofNat 64 n)) = _
      rw [List.append_assoc, h1, h2]
      ac_rfl
    have hsub : ∀ m, (Eq ((stackZeros n).At (0x0ff8#64 - BitVec.ofNat 64 n)) ⋆ Eq (ra.At 0x0ff8#64)) m →
        litmusTarget.Entry 0x0ff8#64 (0x1234 : Nat) n m :=
      sep_mono2 (fun _ hf1 => ⟨stackZeros n, hzs, hf1.symm⟩) (fun _ hf2 => ⟨by decide, hf2⟩)
    change (Eq (bs.At 0x1000#64) ⋆ litmusTarget.Entry 0x0ff8#64 (0x1234 : Nat) n ⋆ emp)
      (litmusInitMem n bs)
    exact sep_mono_mid hsub hmem
  retsIn_singleton v s h := by
    obtain ⟨locs, hlocs, hrel⟩ := h
    change some (AbiReg.gpr 0, ()) = some locs at hlocs
    injection hlocs with hlocs; subst hlocs
    cases hrel with
    | cons h1 _ => exact h1.2.trans (by simp)
  argsIn_singleton v s h := by
    obtain ⟨locs, hlocs, hrel⟩ := h
    change some (AbiReg.gpr 7, ()) = some locs at hlocs
    injection hlocs with hlocs; subst hlocs
    cases hrel with
    | cons h1 _ => exact h1.2.trans (by simp)

/-! ## 4. Two-Function Caller+Callee `Module`, `checkAcyclic`, & `splice_module_hints` -/

/-- Callee `inc(y) = y + 1`. -/
def fnModInc : Fn := ⟨"inc", [i64], [i64], fun _ _ (y, ()) =>
  .let_ (op2 (.add i64) (.var y) (.imm 1)) fun (r, ()) => .ret (.var r, ())⟩

/-- Caller `caller(x) = inc(x) + 2`. -/
def fnModCaller : Fn := ⟨"caller", [i64], [i64], fun _ _ (x, ()) =>
  .call "inc" (as := [i64]) (bs := [i64]) (.var x, ()) fun (y, ()) =>
  .let_ (op2 (.add i64) (.var y) (.imm 2)) fun (r, ()) => .ret (.var r, ())⟩

/-- Callee-first 2-function module. -/
def litmusMod : Module where
  fns := [fnModInc, fnModCaller]
  externs := []
  exits := []

theorem litmusMod_checkAcyclic : litmusMod.checkAcyclic = true := by rfl

theorem litmusMod_wf : ∀ f ∈ litmusMod.fns, f.Wf := by
  intro f hf
  simp only [litmusMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · unfold Fn.Wf; t_wf_reify
  · unfold Fn.Wf; t_wf_reify

theorem litmusMod_supportsSource :
    ∀ f ∈ litmusMod.fns, (f.earlyOpt).body.supportsSource LegalTarget.aarch64 = true := by
  intro f hf
  simp only [litmusMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> t_kernel_rfl

/-- Source contract environment for `litmusMod`. -/
def litmusΓ : Env
  | "inc", [.bits 64], [.bits 64], (y, ()), m, Q, _ => Q (y + 1#64, ()) m
  | "caller", [.bits 64], [.bits 64], (x, ()), m, Q, _ => Q (x + 3#64, ()) m
  | _, _, _, _, _, _, _ => False

theorem litmusMod_wp : ∀ f ∈ litmusMod.fns, ∀ xs m Q X,
    litmusΓ f.name f.as f.rs xs m Q X → Func.wp litmusΓ f.body xs m Q X := by
  intro f hf xs m Q X hΓ
  simp only [litmusMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · rcases xs with ⟨y, ⟨⟩⟩
    exact hΓ
  · rcases xs with ⟨x, ⟨⟩⟩
    refine ⟨fun r m' => r = (x + 1#64, ()) ∧ m' = m, fun _ _ _ _ => False, ⟨rfl, rfl⟩, ?_,
      fun _ _ _ _ h => nomatch h⟩
    rintro ⟨y, ⟨⟩⟩ _ ⟨hy, rfl⟩
    have hy' : y = x + 1#64 := (Prod.ext_iff.mp hy).1
    subst hy'
    show Q ((x + 1#64) + 2#64, _) _
    rwa [BitVec.add_assoc]

splice_module_hints litmusHints litmusTarget.toIsa LegalTarget.aarch64 litmusMod.fns

/-! ## 5. Single Kernel `t_kernel_rfl`, `Compiled.fnSpec_host_src`, & `TargetInit` Witnesses -/

theorem litmus_check :
    checkCompile litmusTarget litmusLayout LegalTarget.aarch64 [] [] 0 litmusMod.fns
      litmusHints 2048 = true := by
  t_kernel_rfl

theorem litmus_check_withLabels :
    checkCompileWithLabels litmusTarget litmusLayoutWithLabels LegalTarget.aarch64 [] [] 0
      litmusMod.fns litmusHints 2048 = true := by
  t_kernel_rfl

/-- Certified compiled bundle constructed structurally via `litmusLabelClean`. -/
def litmusCompiled :
    Compiled litmusTarget LegalTarget.aarch64 [] [] 0 litmusMod.fns litmusHints 2048 :=
  compileChecked litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
    [] [] 0 litmusMod.fns litmusHints 2048 litmus_check

/-- Secondary bundle exercising the explicit `labelsNodup` path. -/
def litmusCompiledWithLabels :
    Compiled litmusTarget LegalTarget.aarch64 [] [] 0 litmusMod.fns litmusHints 2048 :=
  compileCheckedWithLabels litmusTarget litmusLayoutWithLabels LegalTarget.aarch64
    [] [] 0 litmusMod.fns litmusHints 2048 litmus_check_withLabels

theorem litmusInc_fnSpec :
    litmusTarget.Defined litmusCompiled.host "inc" ∧
      litmusTarget.FnSpec litmusCompiled.host "inc" (litmusΓ "inc" [i64] [i64])
        (litmusCompiled.bound "inc") 0 :=
  litmusCompiled.fnSpec_host_src litmusMod rfl litmusΓ litmusMod_checkAcyclic
    litmusMod_wf litmusMod_supportsSource litmusMod_wp List.mem_cons_self
    rfl rfl (fun _ _ _ _ _ h => h)

theorem litmusCaller_fnSpec :
    litmusTarget.Defined litmusCompiled.host "caller" ∧
      litmusTarget.FnSpec litmusCompiled.host "caller" (litmusΓ "caller" [i64] [i64])
        (litmusCompiled.bound "caller") 0 :=
  litmusCompiled.fnSpec_host_src litmusMod rfl litmusΓ litmusMod_checkAcyclic
    litmusMod_wf litmusMod_supportsSource litmusMod_wp
    (List.mem_cons_of_mem _ List.mem_cons_self) rfl rfl (fun _ _ _ _ _ h => h)

theorem litmusCaller_fnSpec_withLabels :
    litmusTarget.Defined litmusCompiledWithLabels.host "caller" ∧
      litmusTarget.FnSpec litmusCompiledWithLabels.host "caller"
        (litmusΓ "caller" [i64] [i64]) (litmusCompiledWithLabels.bound "caller") 0 :=
  litmusCompiledWithLabels.fnSpec_host_src litmusMod rfl litmusΓ litmusMod_checkAcyclic
    litmusMod_wf litmusMod_supportsSource litmusMod_wp
    (List.mem_cons_of_mem _ List.mem_cons_self) rfl rfl (fun _ _ _ _ _ h => h)

/-- Concrete `TargetInit.run_ret1` execution witness (`caller 41 = 44`). -/
theorem litmusCaller_run_ret1 :
    Eventually (litmusTarget.mach.step litmusCompiled.host)
      (fun st => litmusTarget.mach.pc st = litmusInit.ra0 ∧
        litmusTarget.RetsIn (bs := [i64]) ((44#64, ()) : Tup Val [i64])
          (litmusTarget.mach.data st))
      (litmusTarget.mach.mkState
        (litmusInit.initState (as := [i64]) (litmusCompiled.bound "caller") []
          ((41#64, ()) : Tup Val [i64]))
        (litmusTarget.mach.labelAddr litmusCompiled.host "caller")) :=
  litmusInit.run_ret1 (as := [i64]) litmusCompiled litmusCaller_fnSpec.2 []
    ((41#64, ()) : Tup Val [i64]) 44#64 (by decide) rfl
    (Q := fun rets _ => rets = (44#64, ())) (by rfl) (fun _ _ h => h)

/-- Concrete `TargetInit.run_ret1_i64` GPR return witness (`rax = 44`). -/
theorem litmusCaller_run_i64 :
    Eventually (litmusTarget.mach.step litmusCompiled.host)
      (fun st => litmusTarget.mach.pc st = litmusInit.ra0 ∧
        litmusTarget.mach.getGpr (litmusTarget.mach.data st) litmusInit.ret0 = 44#64)
      (litmusTarget.mach.mkState
        (litmusInit.initState (as := [i64]) (litmusCompiled.bound "caller") []
          ((41#64, ()) : Tup Val [i64]))
        (litmusTarget.mach.labelAddr litmusCompiled.host "caller")) :=
  litmusInit.run_ret1_i64 (as := [i64]) litmusCompiled litmusCaller_fnSpec.2 []
    ((41#64, ()) : Tup Val [i64]) 44#64 (by decide) rfl
    (Q := fun rets _ => rets = (44#64, ())) (by rfl) (fun _ _ h => h)

/-- Concrete `TargetInit.run_ret1_sep_i64` witness framing a concrete memory byte at `0x1000#64`. -/
theorem litmusCaller_run_sep :
    Eventually (litmusTarget.mach.step litmusCompiled.host)
      (fun st => litmusTarget.mach.pc st = litmusInit.ra0 ∧
        litmusTarget.mach.getGpr (litmusTarget.mach.data st) litmusInit.ret0 = 44#64 ∧
        (litmusTarget.mach.mem (litmusTarget.mach.data st) =⋆
          Eq ([0x2a].At 0x1000#64) ⋆ litmusTarget.Exit litmusInit.sp0 (litmusCompiled.bound "caller") ⋆
          Std.ExtHashMap.emp))
      (litmusTarget.mach.mkState
        (litmusInit.initState (as := [i64]) (litmusCompiled.bound "caller") [0x2a]
          ((41#64, ()) : Tup Val [i64]))
        (litmusTarget.mach.labelAddr litmusCompiled.host "caller")) :=
  litmusInit.run_ret1_sep_i64 (as := [i64]) litmusCompiled litmusCaller_fnSpec.2 [0x2a]
    ((41#64, ()) : Tup Val [i64]) 44#64 (Eq ([0x2a].At 0x1000#64)) (by decide) rfl
    (Q := fun rets m' => rets = (44#64, ()) ∧ m' = [0x2a].At 0x1000#64) ⟨rfl, rfl⟩
    (fun _ _ h => ⟨h.1, h.2.symm⟩)

/-! ## 6. Abnormal `exit`, Non-Empty `extCallees`, and Callee Signature Rejection -/

/-- `guard(x)`: abnormally exits to `"abort"(x)` when `x == 0`, otherwise returns `x + 1`. -/
def fnExitGuard : Fn := ⟨"guard", [i64], [i64], fun _ _ (x, ()) =>
  .let_ (op2 (@OpCode.cmp .eq i64 .bool rfl) (.var x) (.imm 0)) fun (isZero, ()) =>
  .jnz (.var isZero)
    (.exit "abort" (as := [i64]) (.var x, ()))
    (.let_ (op2 (.add i64) (.var x) (.imm 1)) fun (r, ()) => .ret (.var r, ()))⟩

def guardMod : Module where
  fns := [fnExitGuard]
  externs := []
  exits := ["abort"]

theorem guardMod_checkAcyclic : guardMod.checkAcyclic = true := by rfl

theorem guardMod_wf : ∀ f ∈ guardMod.fns, f.Wf := by
  intro f hf
  simp only [guardMod, List.mem_singleton] at hf
  subst hf; unfold Fn.Wf; t_wf_reify

theorem guardMod_supportsSource :
    ∀ f ∈ guardMod.fns, (f.earlyOpt).body.supportsSource LegalTarget.aarch64 = true := by
  intro f hf
  simp only [guardMod, List.mem_singleton] at hf
  subst hf; t_kernel_rfl

def guardΓ : Env
  | "guard", [.bits 64], [.bits 64], (x, ()), m, Q, X =>
      if x == 0#64 then X "abort" [i64] (0#64, ()) m else Q (x + 1#64, ()) m
  | _, _, _, _, _, _, _ => False

theorem guardMod_wp : ∀ f ∈ guardMod.fns, ∀ xs m Q X,
    guardΓ f.name f.as f.rs xs m Q X → Func.wp guardΓ f.body xs m Q X := by
  intro f hf xs m Q X hΓ
  simp only [guardMod, List.mem_singleton] at hf
  subst hf
  rcases xs with ⟨x, ⟨⟩⟩
  change (if x == 0#64 then X "abort" [i64] (0#64, ()) m else Q (x + 1#64, ()) m) at hΓ
  dsimp only [Func.wp, fnExitGuard, wp, Op.wp, op2, OpCode.wp,
    liftCmp, CmpOp.evalBits, lift2, Ty.hasFloat, Arg.val, vals]
  by_cases hx : x = 0#64
  · subst hx
    split at hΓ
    · exact ⟨fun _ => hΓ, fun h => absurd h (by decide)⟩
    · rename_i hcond; exact absurd (by decide) hcond
  · split at hΓ
    · exact absurd (by simp_all) hx
    · exact ⟨fun h => absurd (by simpa using h) hx, fun _ => hΓ⟩

splice_module_hints guardHints litmusTarget.toIsa LegalTarget.aarch64 guardMod.fns

theorem guard_check :
    checkCompile litmusTarget litmusLayout LegalTarget.aarch64 [] ["abort"] 16 guardMod.fns
      guardHints 2048 = true := by
  t_kernel_rfl

def guardCompiled :
    Compiled litmusTarget LegalTarget.aarch64 [] ["abort"] 16 guardMod.fns guardHints 2048 :=
  compileChecked litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
    [] ["abort"] 16 guardMod.fns guardHints 2048 guard_check

theorem guard_fnSpec :
    litmusTarget.Defined guardCompiled.host "guard" ∧
      litmusTarget.FnSpec guardCompiled.host "guard"
        (legalEnv LegalTarget.aarch64 (Env.ofModule guardMod guardΓ) "guard" [i64] [i64])
        (guardCompiled.bound "guard") 16 :=
  guardCompiled.fnSpec_host guardMod rfl guardΓ guardMod_checkAcyclic
    guardMod_wf guardMod_supportsSource guardMod_wp List.mem_cons_self

private theorem guard_fnSpec_src :
    litmusTarget.FnSpec guardCompiled.host "guard"
      (fun args m Q X => guardΓ "guard" [i64] [i64] args m Q
        (fun g cs xs m' => X g (LegalTarget.aarch64.legalSig cs)
          (encodeTup LegalTarget.aarch64 cs xs) m'))
      (guardCompiled.bound "guard") 16 :=
  fnSpec_of_legalEnv_legalSig_eq (lt := LegalTarget.aarch64) (M := guardMod)
    (as := [i64]) (bs := [i64]) (by rfl) (by rfl)
    (by simp [guardMod, Module.sigs, fnExitGuard, Fn.sig]) guard_fnSpec.2

/-- Concrete execution witness for the normal return branch of `guard` (`guard 41 = 42`). -/
theorem guard_run_normal :
    Eventually (litmusTarget.mach.step guardCompiled.host)
      (fun st => litmusTarget.mach.pc st = litmusInit.ra0 ∧
        litmusTarget.mach.getGpr (litmusTarget.mach.data st) litmusInit.ret0 = 42#64)
      (litmusTarget.mach.mkState
        (litmusInit.initState (as := [i64]) (guardCompiled.bound "guard") []
          ((41#64, ()) : Tup Val [i64]))
        (litmusTarget.mach.labelAddr guardCompiled.host "guard")) := by
  refine litmusInit.run_fnSpec (as := [i64]) guardCompiled guard_fnSpec_src []
    ((41#64, ()) : Tup Val [i64]) (by decide) rfl
    (Q := fun rets _ => rets = (42#64, ())) (X := fun _ _ _ _ => False) (by rfl) ?_
  rintro st (⟨hpc, rets, m', hq, hrets, _⟩ | ⟨_, _, _, _, hx, _⟩)
  · subst hq; exact ⟨hpc, litmusInit.retsIn_singleton 42#64 _ hrets⟩
  · exact hx.elim

/-- Concrete execution witness for the abnormal `exit` branch of `guard` (`guard 0 → abort(0)`). -/
theorem guard_run_exit :
    Eventually (litmusTarget.mach.step guardCompiled.host)
      (fun st => litmusTarget.mach.pc st = litmusTarget.mach.labelAddr guardCompiled.host "abort" ∧
        litmusTarget.ArgsIn (as := [i64]) (0#64, ()) (litmusTarget.mach.data st))
      (litmusTarget.mach.mkState
        (litmusInit.initState (as := [i64]) (guardCompiled.bound "guard") []
          ((0#64, ()) : Tup Val [i64]))
        (litmusTarget.mach.labelAddr guardCompiled.host "guard")) := by
  refine litmusInit.run_fnSpec (as := [i64]) guardCompiled guard_fnSpec_src []
    ((0#64, ()) : Tup Val [i64]) (by decide) rfl
    (Q := fun _ _ => False)
    (X := fun sym cs xs _ => sym = "abort" ∧ cs = [i64] ∧ HEq xs ((0#64, ()) : Tup Val [i64]))
    ⟨rfl, rfl, HEq.rfl⟩ ?_
  rintro st (⟨_, _, _, hq, _⟩ | ⟨sym', cs', xs', _, ⟨rfl, rfl, hxs⟩, hpc, has⟩)
  · exact hq.elim
  · obtain rfl := eq_of_heq hxs; exact ⟨hpc, has⟩

/-- Compiling `fnExitGuard` without declaring `"abort"` in `exits` is rejected. -/
theorem guard_missing_exit_rejected :
    checkCompile litmusTarget litmusLayout LegalTarget.aarch64 [] [] 16 guardMod.fns
      guardHints 2048 = false := by
  t_kernel_rfl

/-- Separate compilation with non-empty `extCallees`: compile `fnModInc` alone, then compile
`fnModCaller` against `extCallees := [(("inc", [i64], [i64]), bInc)]` and link on `codeInc ++ codeCaller`. -/
def incOnlyMod : Module where
  fns := [fnModInc]
  externs := []
  exits := []

def callerOnlyMod : Module where
  fns := [fnModCaller]
  externs := [⟨"inc", [i64], [i64]⟩]
  exits := []

theorem incOnlyMod_checkAcyclic : incOnlyMod.checkAcyclic = true := by rfl
theorem callerOnlyMod_checkAcyclic : callerOnlyMod.checkAcyclic = true := by rfl

splice_module_hints incOnlyHints litmusTarget.toIsa LegalTarget.aarch64 incOnlyMod.fns
splice_module_hints callerOnlyHints litmusTarget.toIsa LegalTarget.aarch64 callerOnlyMod.fns

theorem incOnly_check :
    checkCompile litmusTarget litmusLayout LegalTarget.aarch64 [] [] 0 incOnlyMod.fns
      incOnlyHints 2048 = true := by
  t_kernel_rfl

def incOnlyCompiled :
    Compiled litmusTarget LegalTarget.aarch64 [] [] 0 incOnlyMod.fns incOnlyHints 2048 :=
  compileChecked litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
    [] [] 0 incOnlyMod.fns incOnlyHints 2048 incOnly_check

theorem callerExt_check :
    checkCompile litmusTarget litmusLayout LegalTarget.aarch64
      [(("inc", [i64], [i64]), incOnlyCompiled.bound "inc")] [] 0
      callerOnlyMod.fns callerOnlyHints 2048 = true := by
  t_kernel_rfl

def callerExtCompiled :
    Compiled litmusTarget LegalTarget.aarch64
      [(("inc", [i64], [i64]), incOnlyCompiled.bound "inc")] [] 0
      callerOnlyMod.fns callerOnlyHints 2048 :=
  compileChecked litmusTarget litmusLayout LegalTarget.aarch64 litmusLabelClean
    [(("inc", [i64], [i64]), incOnlyCompiled.bound "inc")] [] 0
    callerOnlyMod.fns callerOnlyHints 2048 callerExt_check

/-- Combined host containing both separately-compiled `inc` and `caller` code. -/
theorem combinedExt_progSmall :
    litmusLayout.progSmall (incOnlyCompiled.code ++ callerExtCompiled.code) = true := by
  t_kernel_rfl

def combinedExtHost : LHost :=
  litmusLayout.layoutOf (incOnlyCompiled.code ++ callerExtCompiled.code) combinedExt_progSmall

theorem combinedExt_labelsUnique : litmusTarget.LabelsUnique combinedExtHost :=
  compileModule_append_labelsUnique litmusLabelClean combinedExtHost
    (litmusLayout.prog_layoutOf _ _)
    incOnlyCompiled.compileModule_eq callerExtCompiled.compileModule_eq
    (by decide) (by decide)

theorem callerExt_linked_fnSpec :
    litmusTarget.Defined combinedExtHost "caller" ∧
      litmusTarget.FnSpec combinedExtHost "caller"
        (legalEnv LegalTarget.aarch64 (Env.ofModule callerOnlyMod litmusΓ) "caller" [i64] [i64])
        (callerExtCompiled.bound "caller") 0 := by
  have hprog : litmusTarget.mach.prog combinedExtHost =
      incOnlyCompiled.code ++ callerExtCompiled.code := litmusLayout.prog_layoutOf _ _
  have hIncInfix : incOnlyCompiled.code.IsInfixAt (litmusTarget.mach.prog combinedExtHost) 0 := by
    rw [hprog]; exact ⟨callerExtCompiled.code, rfl⟩
  have hCallerInfix : callerExtCompiled.code.IsInfixAt (litmusTarget.mach.prog combinedExtHost)
      incOnlyCompiled.code.length := by
    rw [hprog]; exact ⟨[], by simp⟩
  have hIncSpec := incOnlyCompiled.fnSpec incOnlyMod rfl combinedExtHost litmusΓ 0
    hIncInfix combinedExt_labelsUnique incOnlyMod_checkAcyclic
    (fun f hf => by
      simp only [incOnlyMod, List.mem_singleton] at hf; subst hf
      exact litmusMod_wf fnModInc List.mem_cons_self)
    (fun f hf => by
      simp only [incOnlyMod, List.mem_singleton] at hf; subst hf
      exact litmusMod_supportsSource fnModInc List.mem_cons_self)
    (fun f hf xs m Q X hΓ => by
      simp only [incOnlyMod, List.mem_singleton] at hf; subst hf
      exact litmusMod_wp fnModInc List.mem_cons_self xs m Q X hΓ)
    (fun _ h => nomatch h) ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    (fun _ h => nomatch h) List.mem_cons_self
  have hExt : ∀ p ∈ [(("inc", [i64], [i64]), incOnlyCompiled.bound "inc")],
      litmusTarget.FnSpec combinedExtHost p.1.1
        (legalEnv LegalTarget.aarch64 (Env.ofModule callerOnlyMod litmusΓ) p.1.1 p.1.2.1 p.1.2.2)
        p.2 0 := by
    intro p hp
    simp only [List.mem_singleton] at hp; subst hp
    intro args m Q X ⟨as', bs', has', hbs', args', Q', X', h1, h2, h3, hmem, hΓ⟩
    refine hIncSpec.2 args m Q X ⟨as', bs', has', hbs', args', Q', X', h1, h2, h3, ?_, hΓ⟩
    simp only [callerOnlyMod, incOnlyMod, Module.sigs, fnModCaller, fnModInc, Fn.sig, Extern.sig,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] at hmem ⊢
    rcases hmem with ⟨hbad, _⟩ | hok
    · exact absurd hbad (by decide)
    · exact hok
  exact callerExtCompiled.fnSpec callerOnlyMod rfl combinedExtHost litmusΓ
    incOnlyCompiled.code.length hCallerInfix combinedExt_labelsUnique callerOnlyMod_checkAcyclic
    (fun f hf => by
      simp only [callerOnlyMod, List.mem_singleton] at hf; subst hf
      exact litmusMod_wf fnModCaller (List.mem_cons_of_mem _ List.mem_cons_self))
    (fun f hf => by
      simp only [callerOnlyMod, List.mem_singleton] at hf; subst hf
      exact litmusMod_supportsSource fnModCaller (List.mem_cons_of_mem _ List.mem_cons_self))
    (fun f hf xs m Q X hΓ => by
      simp only [callerOnlyMod, List.mem_singleton] at hf; subst hf
      exact litmusMod_wp fnModCaller (List.mem_cons_of_mem _ List.mem_cons_self) xs m Q X hΓ)
    hExt ⟨fun _ hp _ hq _ => by simp at hp hq; subst hp hq; rfl,
      fun _ hp => by simp at hp; subst hp; decide⟩
    (fun _ h => nomatch h) List.mem_cons_self

/-- Callee signature change rejection: changing arg type, return type, or arity in `extCallees`
causes `compileModule` and `checkCompile` to reject `fnModCaller`. -/
theorem extCallee_argSig_mismatch_rejected :
    checkCompile litmusTarget litmusLayout LegalTarget.aarch64
      [(("inc", [i32], [i64]), 0)] [] 0 callerOnlyMod.fns callerOnlyHints 2048 = false := by
  t_kernel_rfl

theorem extCallee_retSig_mismatch_rejected :
    checkCompile litmusTarget litmusLayout LegalTarget.aarch64
      [(("inc", [i64], [i32]), 0)] [] 0 callerOnlyMod.fns callerOnlyHints 2048 = false := by
  t_kernel_rfl

theorem extCallee_arity_mismatch_rejected :
    checkCompile litmusTarget litmusLayout LegalTarget.aarch64
      [(("inc", [i64, i64], [i64]), 0)] [] 0 callerOnlyMod.fns callerOnlyHints 2048 = false := by
  t_kernel_rfl

/-! ## 7. Axiom Audit -/

#print axioms litmusLabelClean
#print axioms litmus_check
#print axioms litmusInc_fnSpec
#print axioms litmusCaller_fnSpec
#print axioms litmusCaller_fnSpec_withLabels
#print axioms litmusCaller_run_ret1
#print axioms litmusCaller_run_i64
#print axioms litmusCaller_run_sep
#print axioms guard_fnSpec
#print axioms guard_run_normal
#print axioms guard_run_exit
#print axioms callerExt_linked_fnSpec
#print axioms LeanQbe.T.compileFn_correct
#print axioms LeanQbe.T.compile_sound

end LeanQbeTest.T.MainTest
