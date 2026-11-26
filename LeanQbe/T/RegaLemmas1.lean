module

public import LeanQbe.T.Rega
public import LeanQbe.T.RegaLemmas0
public import LeanQbe.T.TargetLemmas
public import LeanQbe.T.WfLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.Logic.MemLemmas
import all Kraken.Separation
import all Kraken.Mem

/-!
# `RegaLemmas` Part 1: Semantic Invariants, Frame `Inv`, Checked Moves, and `shuffle`

Interface shared by `RegaLemmas2` (operands/ABI/frame code) and `RegaLemmas3` (`Wf.induct`):
* `GprSym`/`VecSym`/`FlagSym`: what a `SymArg` entry asserts about a 64-bit GPR word, a
  512-bit vector (truncated to a slot width), or a flag, quantified over *all* context entries
  `⟨t, v, x⟩ ∈ G` (so out-of-scope ids are vacuous).
* `Agree G nv st s σ`: every register/slot/def/width fact of `st` holds in `(s, σ)`.
* `Inv hints s₀ ra n Rf m s σ`: the frame invariant (typed `array64` slots).
* `execMoves_ok`, `stepPre_ok`, `holdsLoc_ok`, `shuffle_ok`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

theorem array64_splice_eq (a : BitVec 64) (pre ws post : List (BitVec 64)) :
    array64 a (pre ++ ws ++ post) = (array64 (a + BitVec.ofNat 64 (8 * pre.length)) ws ⋆
      (array64 a pre ⋆ array64 (a + BitVec.ofNat 64 (8 * (pre.length + ws.length))) post)) := by
  rw [List.append_assoc, array64_append, array64_append, Std.ExtHashMap.sep_comm_l]; congr 3
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega

theorem array64_single (a v : BitVec 64) : array64 a [v] = cell64 a v := by
  simp [Std.ExtHashMap.sep_emp]

theorem cell64_region {a v : BitVec 64} {f : Mem 64} (h : cell64 a v f) : region a 8 f :=
  ⟨_, Int.toBytes_length 8 v.toInt, h.symm⟩

theorem array64_toRegion : ∀ (a : BitVec 64) (xs : List (BitVec 64)) (f : Mem 64),
    8 * xs.length ≤ 2 ^ 64 → array64 a xs f → region a (8 * xs.length) f
  | a, [], f, _, h => ⟨[], rfl, by
      simp only [array64_nil, Std.ExtHashMap.emp] at h; subst h; simp [List.At]⟩
  | a, x :: xs, f, hl, h => by
    obtain ⟨f1, f2, hu, hd, h1, h2⟩ := h
    obtain ⟨bs, hbs, rfl⟩ := array64_toRegion (a + 8) xs f2 (by simp at hl; omega) h2
    have e := Mem.At_append_sep (Int.toBytes 8 x.toInt) bs a
      (by simp [Int.toBytes_length, hbs]; simp at hl; omega)
    refine ⟨Int.toBytes 8 x.toInt ++ bs, by simp [Int.toBytes_length, hbs]; omega, ?_⟩
    refine ((congrFun e f).mpr ⟨f1, _, hu, hd, h1, ?_⟩).symm
    rw [Int.toBytes_length]; rfl

abbrev VCtx : Type := Ctx Val VNat

/-! ## 1. Semantic content of symbolic arguments -/

/-- `w` holds the canonical zero-extended (ABI) form of every context value of `sa`. -/
def SymZ (G : VCtx) (w : BitVec 64) : SymArg → Prop
  | .var x => ∀ t v, ⟨t, v, x⟩ ∈ G → AbiGprHolds w t v
  | _ => True

def FlagHolds (b : Bool) : (t : Ty) → Val t → Prop
  | .bool, v => v = b
  | _, _ => False

def GprSym (G : VCtx) (w : BitVec 64) : SymArg → Prop
  | .var x => ∀ t v, ⟨t, v, x⟩ ∈ G → GprHolds w t v
  | .immBool b => GprHolds w .bool b
  | .immBits n c => n ≤ 64 ∧ w.setWidth n = c.setWidth n
  | .immVec _ _ => False

def VecSym (G : VCtx) (sw : SlotWidth) (bv : BitVec 512) : SymArg → Prop
  | .var x => ∀ t v, ⟨t, v, x⟩ ∈ G → t.size ≤ sw.bits ∧ VecHolds bv t v
  | .immVec w c => w.bits ≤ sw.bits ∧ bv.setWidth w.bits = c.setWidth w.bits
  | _ => False

def FlagSym (G : VCtx) (b : Bool) : SymArg → Prop
  | .var x => ∀ t v, ⟨t, v, x⟩ ∈ G → FlagHolds b t v
  | .immBool b' => b = b'
  | _ => False

/-- A variable's context entries are all vector (pair) typed. -/
def VecTy (G : VCtx) : SymArg → Prop
  | .var x => ∀ t v, ⟨t, v, x⟩ ∈ G → ∃ a b, t = .pair a b
  | _ => True

def SymBits (G : VCtx) (w : Nat) (bv : BitVec w) : SymArg → Prop
  | .var x => ∀ v : BitVec w, ⟨.bits w, v, x⟩ ∈ G → v = bv
  | .immBits w' c => w' = w ∧ c.setWidth w = bv
  | _ => False

def FlagFactOk (T : Target) (G : VCtx) (s : T.mach.MData) : Option FlagFact → Prop
  | none => True
  | some (.cmp w lhs rhs eqNe) =>
    w ≤ 64 ∧ ∃ va vb : BitVec w,
      SymValAt G w va lhs ∧ SymBits G w va lhs ∧
      SymValAt G w vb rhs ∧ SymBits G w vb rhs ∧
      FlagCmpOk T.mach T.gpr s va vb eqNe

def FlagFactScope (nv : Nat) : Option FlagFact → Prop
  | none => True
  | some (.cmp _ lhs rhs _) => symArgScopeOk nv lhs = true ∧ symArgScopeOk nv rhs = true

@[simp] theorem FlagFactOk_none (T : Target) (G : VCtx) (s : T.mach.MData) :
    FlagFactOk T G s none = True := rfl

@[simp] theorem FlagFactScope_none (nv : Nat) : FlagFactScope nv none = True := rfl

def SlotEntry.sas : SlotEntry → List SymArg
  | .gpr sas => sas | .gprZ sas => sas.map (·.1) | .vec _ sas => sas

def SlotOk (G : VCtx) (σ : List (BitVec 64)) (i : Nat) : SlotEntry → Prop
  | .gpr sas => ∃ w, σ[i]? = some w ∧ ∀ sa ∈ sas, GprSym G w sa
  | .gprZ sas => ∃ w, σ[i]? = some w ∧
    ∀ p ∈ sas, GprSym G w p.1 ∧ (p.2 = true → SymZ G w p.1)
  | .vec sw sas => ∃ bv, slice σ i sw.slots = unpackSlotWords sw bv ∧ ∀ sa ∈ sas, VecSym G sw bv sa

section Mach
variable {R V C D : Type} (M : Machine R V C D)

def RegLocOk (G : VCtx) (s : M.MData) (sa : SymArg) : RegLoc R V C → Prop
  | .gpr r => GprSym G (M.getGpr s r) sa
  | .gprZ r => GprSym G (M.getGpr s r) sa ∧ SymZ G (M.getGpr s r) sa
  | .vec v => VecSym G .w512 (M.getVec s v) sa
  | .flag c => FlagSym G (M.evalCond s c) sa

/-- Meaning of a target/entry pair `(sa, loc)` (used by jumps, block entries, ABI shuffles). -/
def LocOk (G : VCtx) (s : M.MData) (σ : List (BitVec 64)) (sa : SymArg) : Loc R V C → Prop
  | .gpr r => GprSym G (M.getGpr s r) sa
  | .vec v => VecSym G .w512 (M.getVec s v) sa
  | .flag c => FlagSym G (M.evalCond s c) sa
  | .slot i w => (SlotOk G σ i (.vec w [sa]) ∧ VecTy G sa) ∨ (w = .w64 ∧ SlotOk G σ i (.gpr [sa]))

/-- Meaning of a block parameter value `v : Val t` placed at `loc`. -/
def LocVal (s : M.MData) (σ : List (BitVec 64)) (t : Ty) (v : Val t) : Loc R V C → Prop
  | .gpr r => GprHolds (M.getGpr s r) t v
  | .vec vr => VecHolds (M.getVec s vr) t v
  | .flag c => FlagHolds (M.evalCond s c) t v
  | .slot i w =>
    ((∃ bv, slice σ i w.slots = unpackSlotWords w bv ∧ t.size ≤ w.bits ∧ VecHolds bv t v) ∧
      ∃ a b, t = .pair a b) ∨
    (w = .w64 ∧ ∃ x, σ[i]? = some x ∧ GprHolds x t v)

def ParamsOk (s : M.MData) (σ : List (BitVec 64)) : (ts : List Ty) → Tup Val ts → List (Loc R V C) → Prop
  | [], (), [] => True
  | t :: ts, (v, vs), loc :: locs => LocVal M s σ t v loc ∧ ParamsOk s σ ts vs locs
  | _, _, _ => False

end Mach

def RmwOp.eval {w : Nat} : RmwOp → BitVec w → BitVec w → BitVec w
  | .add => (· + ·)
  | .sub => (· - ·)
  | .and => (· &&& ·)
  | .or  => (· ||| ·)
  | .xor => (· ^^^ ·)

theorem RmwOp.eval_comm {w : Nat} {op : RmwOp} (h : op.isComm = true) (a b : BitVec w) :
    op.eval a b = op.eval b a := by
  cases op with
  | add => exact BitVec.add_comm a b
  | sub => simp [RmwOp.isComm] at h
  | and => exact BitVec.and_comm a b
  | or  => exact BitVec.or_comm a b
  | xor => exact BitVec.xor_comm a b

theorem RmwOp.wp_eval {w : Nat} (op : RmwOp) (a b : BitVec w) (P : Tup Val [.bits w] → Prop) :
    (op.toOpCode w).wp (a, b, ()) P ↔ P (op.eval a b, ()) := by
  cases op <;> simp [RmwOp.toOpCode, RmwOp.eval, OpCode.wp, lift2, Ty.hasFloat]

def DefOk (G : VCtx) (x : Nat) : DefFact → Prop
  | .addImm64 b d => ∀ v, ⟨i64, v, x⟩ ∈ G → ∃ vb : BitVec 64, ⟨i64, vb, b⟩ ∈ G ∧ v = vb + d
  | .scaleOff i sh d =>
    ∀ v, ⟨i64, v, x⟩ ∈ G → ∃ vi : BitVec 64, ⟨i64, vi, i⟩ ∈ G ∧ v = (vi <<< sh) + d
  | .addrSum b i sh d =>
    ∀ v, ⟨i64, v, x⟩ ∈ G → ∃ vb vi : BitVec 64, ⟨i64, vb, b⟩ ∈ G ∧ ⟨i64, vi, i⟩ ∈ G ∧
      v = vb + (vi <<< sh) + d
  | .imm64 c => ∀ v, ⟨i64, v, x⟩ ∈ G → v = c
  | .andVarVar w a b => w ≤ 64 ∧ ∀ v : BitVec w, ⟨.bits w, v, x⟩ ∈ G →
    ∃ va vb : BitVec w, ⟨.bits w, va, a⟩ ∈ G ∧ ⟨.bits w, vb, b⟩ ∈ G ∧ v = va &&& vb
  | .andVarImm w a c => w ≤ 64 ∧ ∀ v : BitVec w, ⟨.bits w, v, x⟩ ∈ G →
    ∃ va : BitVec w, ⟨.bits w, va, a⟩ ∈ G ∧ v = va &&& c.setWidth w
  | .binVarVar w op a b => w ≤ 64 ∧ ∀ v : BitVec w, ⟨.bits w, v, x⟩ ∈ G →
    ∃ va vb : BitVec w, ⟨.bits w, va, a⟩ ∈ G ∧ ⟨.bits w, vb, b⟩ ∈ G ∧ v = op.eval va vb
  | .binVarImm w op a c => w ≤ 64 ∧ ∀ v : BitVec w, ⟨.bits w, v, x⟩ ∈ G →
    ∃ va : BitVec w, ⟨.bits w, va, a⟩ ∈ G ∧ v = op.eval va (c.setWidth w)
  | .shlVarImm w a sh => w ≤ 64 ∧ sh < w ∧ ∀ v : BitVec w, ⟨.bits w, v, x⟩ ∈ G →
    ∃ va : BitVec w, ⟨.bits w, va, a⟩ ∈ G ∧ v = va <<< sh
  | .sextVar m n a => 0 < m ∧ m < n ∧ n ≤ 64 ∧ ∀ v : BitVec n, ⟨.bits n, v, x⟩ ∈ G →
    ∃ va : BitVec m, ⟨.bits m, va, a⟩ ∈ G ∧ v = va.signExtend n
  | .zextVar m n a => 0 < m ∧ m < n ∧ n ≤ 64 ∧ ∀ v : BitVec n, ⟨.bits n, v, x⟩ ∈ G →
    ∃ va : BitVec m, ⟨.bits m, va, a⟩ ∈ G ∧ v = va.zeroExtend n
  | .cmpZeroVar co w a => w ≤ 64 ∧ ∀ cv : Bool, ⟨.bool, cv, x⟩ ∈ G →
    ∃ va : BitVec w, ⟨.bits w, va, a⟩ ∈ G ∧ cv = co.evalBits va 0#w
  | .testBitVar neg w a c => w ≤ 64 ∧ ∀ cv : Bool, ⟨.bool, cv, x⟩ ∈ G →
    ∃ va : BitVec w, ⟨.bits w, va, a⟩ ∈ G ∧
      cv = (if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& c.setWidth w) 0#w

/-- Validity of straight-line elided-load memory definitions against abstract heap `m`. -/
def MemDefsOk (G : VCtx) (m : Mem 64) (nv : Nat) (md : Trie (Ty × Arg VNat i64)) : Prop :=
  ∀ x t a, md.find? x = some (t, a) →
    x < nv ∧ ∀ (v : Val t), ⟨t, v, x⟩ ∈ G →
      ∃ (a₁ : Arg Val i64), ArgRel G i64 a₁ a ∧ loadVal m t a₁.val = some v

theorem MemDefsOk.empty (G : VCtx) (m : Mem 64) (nv : Nat) : MemDefsOk G m nv .empty := by
  intro _ _ _ h; simp [Trie.find?] at h

theorem argRel_mono {G G' : VCtx} (hsub : ∀ p ∈ G, p ∈ G') {t : Ty} {a₁ : Arg Val t}
    {a₂ : Arg VNat t} (h : ArgRel G t a₁ a₂) : ArgRel G' t a₁ a₂ := by
  cases h with
  | var hm => exact .var (hsub _ hm)
  | imm c => exact .imm c

theorem MemDefsOk.grow {G G' : VCtx} {m : Mem 64} {nv nv' : Nat}
    {md : Trie (Ty × Arg VNat i64)} (hle : nv ≤ nv')
    (hG : ∀ p ∈ G', p ∈ G ∨ nv ≤ p.2.2) (hsub : ∀ p ∈ G, p ∈ G')
    (hM : MemDefsOk G m nv md) : MemDefsOk G' m nv' md := by
  intro x t a hx
  obtain ⟨hlt, hv⟩ := hM x t a hx
  refine ⟨Nat.lt_of_lt_of_le hlt hle, fun v hm => ?_⟩
  have hm0 : ⟨t, v, x⟩ ∈ G := (hG _ hm).resolve_right (Nat.not_le.mpr hlt)
  obtain ⟨a₁, hr, hl⟩ := hv v hm0
  exact ⟨a₁, argRel_mono hsub hr, hl⟩

theorem MemDefsOk.insert {G : VCtx} {m : Mem 64} {nv : Nat} {md : Trie (Ty × Arg VNat i64)}
    {t : Ty} {v : Val t} {a₁ : Arg Val i64} {a : Arg VNat i64}
    (hltG : ∀ p ∈ G, p.2.2 < nv) (hrel : ArgRel G i64 a₁ a) (hlv : loadVal m t a₁.val = some v)
    (hM : MemDefsOk G m nv md) :
    MemDefsOk (⟨t, v, nv⟩ :: G) m (nv + 1) (md.insert nv (t, a)) := by
  intro x t' a' hx
  rw [Trie.find?_insert] at hx; split at hx
  · rename_i hxn; simp only [Option.some.injEq, Prod.mk.injEq] at hx
    rcases hx with ⟨rfl, rfl⟩; subst hxn
    refine ⟨Nat.lt_succ_self _, fun v' hm => ?_⟩
    rcases List.mem_cons.mp hm with heq | hm0
    · cases heq; exact ⟨a₁, argRel_mono (fun _ h => List.mem_cons_of_mem _ h) hrel, hlv⟩
    · exact absurd (hltG _ hm0) (Nat.lt_irrefl _)
  · exact (hM.grow (Nat.le_succ _)
      (fun p hp => (List.mem_cons.mp hp).elim (fun h => Or.inr (h ▸ Nat.le_refl _)) Or.inl)
      (fun _ h => List.mem_cons_of_mem _ h)) x t' a' hx

/-! ## 2. `Agree` -/

structure Agree (T : Target) (G : VCtx) (nv : Nat) (st : SymState T.toIsa) (s : T.mach.MData)
    (σ : List (BitVec 64)) : Prop where
  ctx_lt : ∀ p ∈ G, p.2.2 < nv
  ctx_uniq : ∀ {t : Ty} {x : Nat} {v₁ v₂ : Val t}, ⟨t, v₁, x⟩ ∈ G → ⟨t, v₂, x⟩ ∈ G → v₁ = v₂
  regs : ∀ p ∈ st.regs, RegLocOk T.mach G s p.1 p.2
  slots : ∀ i se, st.slots.find? i = some se → SlotOk G σ i se
  defs : ∀ x d, st.defs.find? x = some d → DefOk G x d
  vw : ∀ x w, st.vecWidths.find? x = some w → ∀ t v, ⟨t, v, x⟩ ∈ G →
    t.size ≤ w.bits ∧ ∃ a b, t = .pair a b
  regs_lt : ∀ p ∈ st.regs, symArgScopeOk nv p.1 = true
  slots_lt : ∀ i se, st.slots.find? i = some se → ∀ sa ∈ se.sas, symArgScopeOk nv sa = true
  defs_lt : ∀ x d, st.defs.find? x = some d → x < nv
  vw_lt : ∀ x w, st.vecWidths.find? x = some w → x < nv
  /-- Converse of `vw`: a variable without a vector width is not pair typed. -/
  vt : ∀ x t v, ⟨t, v, x⟩ ∈ G → st.vecWidths.find? x = none → ∀ a b, t ≠ .pair a b
  zeroExt32_ok : ∀ r ∈ st.zeroExt32,
    T.mach.getGpr s r = ((T.mach.getGpr s r).setWidth 32).setWidth 64
  flags_ok : FlagFactOk T G s st.flags
  flags_lt : FlagFactScope nv st.flags

theorem setWidth_setWidth_64_32 (w : BitVec 64) :
    ((w.setWidth 32).setWidth 64).setWidth 32 = w.setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [show (i : Nat) < 32 from hi]

theorem setWidth_32_64_idem (w : BitVec 64) :
    ((((w.setWidth 32).setWidth 64).setWidth 32).setWidth 64) = ((w.setWidth 32).setWidth 64) := by
  rw [setWidth_setWidth_64_32]

theorem setWidth_32_64_val (v : BitVec 32) :
    ((v.setWidth 64).setWidth 32).setWidth 64 = v.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [show (i : Nat) < 64 from hi]

theorem tyEq_iff {a b : Ty} : tyEq a b = true ↔ a = b := by
  induction a generalizing b with
  | pair a1 b1 ih1 ih2 => cases b <;> simp [tyEq, ih1, ih2]
  | _ => cases b <;> simp [tyEq]

/-! ## 3. The frame invariant -/

section Frame
variable (T : Target) (hints : T.toIsa.Hints) (s₀ : T.mach.MData) (ra : T.mach.Addr) (n : Nat)
  (Rf : Mem 64 → Prop)

abbrev frameZ (zl : Bool) : Nat := if zl then 0 else T.frame.frameSize hints.totalSlots

theorem effFrame_le (I : Isa) (h : I.Hints) (E : Ext) :
    effFrame I h E ≤ I.frame.frameSize h.totalSlots := by
  unfold effFrame; split
  · exact Nat.zero_le _
  · exact Nat.le_refl _
abbrev base : BitVec 64 := T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 (frame T hints)

abbrev baseZ (zl : Bool) : BitVec 64 :=
  T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 (frameZ T hints zl)

def csSlots : Mem 64 → Prop :=
  array64 (base T hints s₀ + BitVec.ofNat 64 (8 * hints.nslots)) (hints.saved.map (T.mach.getGpr s₀))

def csSlotsZ (zl : Bool) : Mem 64 → Prop :=
  array64 (baseZ T hints s₀ zl + BitVec.ofNat 64 (8 * hints.nslots))
    (hints.saved.map (T.mach.getGpr s₀))

def Fr : Mem 64 → Prop :=
  csSlots T hints s₀ ⋆ (T.frameSpec.Saved (T.mach.getGpr s₀ T.frame.sp) ra hints.totalSlots ⋆
    (region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n) (n - frame T hints) ⋆ Rf))

def FrZ (zl : Bool) : Mem 64 → Prop :=
  csSlotsZ T hints s₀ zl ⋆
    ((if zl then T.frameSpec.RetAddr (T.mach.getGpr s₀ T.frame.sp) ra
      else T.frameSpec.Saved (T.mach.getGpr s₀ T.frame.sp) ra hints.totalSlots) ⋆
    (region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n) (n - frameZ T hints zl) ⋆ Rf))

def Inv (m : Mem 64) (s : T.mach.MData) (σ : List (BitVec 64)) (zl : Bool := false) : Prop :=
  σ.length = hints.nslots ∧ T.mach.getGpr s T.frame.sp = baseZ T hints s₀ zl ∧
  (∀ r ∈ T.frame.calleeSaved, r ∉ hints.saved → T.mach.getGpr s r = T.mach.getGpr s₀ r) ∧
  (T.mach.mem s =⋆ Eq m ⋆ (array64 (baseZ T hints s₀ zl) σ ⋆ FrZ T hints s₀ ra n Rf zl)) ∧
  (∀ r ∈ hints.saved, r ∈ T.frame.calleeSaved) ∧ hints.saved.Nodup ∧
  (zl = true → hints.totalSlots = 0 ∧ T.frameSpec.raReg s ra)

end Frame

/-! ## `clearSlotRange` -/

theorem eraseIfOverlaps_find {i d j : Nat} {sl : Trie SlotEntry} {se : SlotEntry}
    (h : (eraseIfOverlaps i d sl).find? j = some se) :
    sl.find? j = some se ∧ ¬(d ≤ i ∧ j = i - d ∧ d + 1 ≤ se.slots) := by
  unfold eraseIfOverlaps at h; split at h
  · rename_i hdi; split at h
    · rename_i se' hf; split at h
      · rename_i hs; by_cases hj : j = i - d
        · subst hj; simp [Trie.find?_erase_self] at h
        · rw [Trie.find?_erase_ne _ hj] at h; exact ⟨h, fun hh => hj hh.2.1⟩
      · rename_i hs
        refine ⟨h, fun ⟨_, hj, hd⟩ => hs ?_⟩
        subst hj; rw [hf] at h; cases h; simpa using hd
    · rename_i hf
      refine ⟨h, fun ⟨_, hj, _⟩ => ?_⟩
      subst hj; rw [hf] at h; cases h
  · rename_i hdi; exact ⟨h, fun hh => hdi (by simpa using hh.1)⟩

theorem eraseSeq_find : ∀ (k i j : Nat) (sl : Trie SlotEntry) (se : SlotEntry),
    (eraseSeq i k sl).find? j = some se → sl.find? j = some se ∧ ¬(i ≤ j ∧ j < i + k)
  | 0, _, _, _, _, h => ⟨h, by omega⟩
  | k + 1, i, j, sl, se, h => by
    obtain ⟨h1, h2⟩ := eraseSeq_find k (i + 1) j _ se h
    by_cases hj : j = i
    · subst hj; simp [Trie.find?_erase_self] at h1
    · rw [Trie.find?_erase_ne _ hj] at h1; exact ⟨h1, by omega⟩

theorem SlotEntry.slots_le (se : SlotEntry) : se.slots ≤ 8 := by
  cases se <;> simp [SlotEntry.slots, SlotWidth.slots_le_eight]

theorem clearSlotRange_find {i k j : Nat} {sl : Trie SlotEntry} {se : SlotEntry}
    (h : (clearSlotRange i k sl).find? j = some se) :
    sl.find? j = some se ∧ (j + se.slots ≤ i ∨ i + k ≤ j) := by
  unfold clearSlotRange at h
  obtain ⟨h, h0⟩ := eraseSeq_find _ _ _ _ _ h
  obtain ⟨h, h1⟩ := eraseIfOverlaps_find h; obtain ⟨h, h2⟩ := eraseIfOverlaps_find h
  obtain ⟨h, h3⟩ := eraseIfOverlaps_find h; obtain ⟨h, h4⟩ := eraseIfOverlaps_find h
  obtain ⟨h, h5⟩ := eraseIfOverlaps_find h; obtain ⟨h, h6⟩ := eraseIfOverlaps_find h
  obtain ⟨h, h7⟩ := eraseIfOverlaps_find h
  refine ⟨h, ?_⟩
  have h8 := se.slots_le
  have key : ∀ d, 1 ≤ d → d ≤ 7 → ¬(d ≤ i ∧ j = i - d ∧ d + 1 ≤ se.slots) := fun d h1 h7 => by
    rcases (show d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  by_cases hji : i ≤ j
  · exact Or.inr (Decidable.byContradiction fun hc => h0 ⟨hji, by omega⟩)
  · exact Or.inl (Decidable.byContradiction fun hc =>
      key (i - j) (by omega) (by omega) ⟨by omega, by omega, by omega⟩)

theorem clearSlotRange_sub {i k j : Nat} {sl : Trie SlotEntry} {se : SlotEntry}
    (h : (clearSlotRange i k sl).find? j = some se) : sl.find? j = some se :=
  (clearSlotRange_find h).1

theorem SlotOk.splice {G : VCtx} {σ ws : List (BitVec 64)} {i k j : Nat} {se : SlotEntry}
    (h : i + k ≤ σ.length) (hw : ws.length = k) (hd : j + se.slots ≤ i ∨ i + k ≤ j)
    (hs : SlotOk G σ j se) : SlotOk G (splice σ i k ws) j se := by
  cases se with
  | gpr sas =>
    obtain ⟨x, h1, h2⟩ := hs
    exact ⟨x, by rw [getElem?_splice_disj h hw (by simp [SlotEntry.slots] at hd; omega)]; exact h1, h2⟩
  | gprZ sas =>
    obtain ⟨x, h1, h2⟩ := hs
    exact ⟨x, by
      rw [getElem?_splice_disj h hw (by simp [SlotEntry.slots] at hd; omega)]; exact h1, h2⟩
  | vec sw sas => obtain ⟨bv, h1, h2⟩ := hs; exact ⟨bv, by rw [slice_splice_disj (kj := sw.slots) h hw hd]; exact h1, h2⟩

/-! ## 4. Interface lemmas (`execMoves_ok`, `stepPre_ok`, `holdsLoc_ok`, `shuffle_ok`) -/

section Lemmas
variable {T : Target} {host : T.mach.Host} {post : T.mach.State → Prop} {hints : T.toIsa.Hints}
  {s₀ : T.mach.MData} {ra : T.mach.Addr} {n : Nat} {Rf : Mem 64 → Prop}
variable {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s s' : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}

theorem scope_lt {nv x : Nat} (h : symArgScopeOk nv (.var x) = true) : x < nv := by
  simp only [symArgScopeOk, Nat.ble_eq] at h; omega
private theorem mem_grow {G G' : VCtx} (hG : ∀ p ∈ G', p ∈ G ∨ nv ≤ p.2.2) {sa : SymArg} (hs : symArgScopeOk nv sa = true)
    : ∀ x, sa = .var x → ∀ t (v : Val t), ⟨t, v, x⟩ ∈ G' → ⟨t, v, x⟩ ∈ G := by
  rintro x rfl t v hm; exact (hG _ hm).resolve_right (Nat.not_le.mpr (scope_lt hs))

section Tr
variable {G G' : VCtx} {sa : SymArg}
  (hT : ∀ x, sa = .var x → ∀ t (v : Val t), ⟨t, v, x⟩ ∈ G → ⟨t, v, x⟩ ∈ G')
include hT

theorem GprSym.tr {w : BitVec 64} (h : GprSym G' w sa) : GprSym G w sa := by
  cases sa <;> first | exact h | exact fun t v hm => h t v (hT _ rfl t v hm)
theorem SymZ.tr {w : BitVec 64} (h : SymZ G' w sa) : SymZ G w sa := by
  cases sa with
  | var x => exact fun t v hm => h t v (hT x rfl t v hm)
  | _ => trivial
theorem VecSym.tr {sw : SlotWidth} {bv : BitVec 512} (h : VecSym G' sw bv sa) : VecSym G sw bv sa := by
  cases sa <;> first | exact h | exact fun t v hm => h t v (hT _ rfl t v hm)
theorem FlagSym.tr {b : Bool} (h : FlagSym G' b sa) : FlagSym G b sa := by
  cases sa <;> first | exact h | exact fun t v hm => h t v (hT _ rfl t v hm)
theorem VecTy.tr (h : VecTy G' sa) : VecTy G sa := by
  cases sa <;> first | exact h | exact fun t v hm => h t v (hT _ rfl t v hm)
theorem SymBits.tr {w : Nat} {bv : BitVec w} (h : SymBits G' w bv sa) : SymBits G w bv sa := by
  cases sa with
  | var x => exact fun v hm => h v (hT x rfl (.bits w) v hm)
  | _ => exact h
theorem RegLocOk.tr {R V C D : Type} {M : Machine R V C D} {s : M.MData} {rl : RegLoc R V C}
    (h : RegLocOk M G' s sa rl) : RegLocOk M G s sa rl := by
  cases rl with
  | gpr _ => exact GprSym.tr hT h
  | gprZ _ => exact ⟨GprSym.tr hT h.1, SymZ.tr hT h.2⟩
  | vec _ => exact VecSym.tr hT h
  | flag _ => exact FlagSym.tr hT h
end Tr

theorem SlotOk.tr {G G' : VCtx} {i : Nat} {se : SlotEntry}
    (hT : ∀ sa ∈ se.sas, ∀ x, sa = .var x → ∀ t (v : Val t), ⟨t, v, x⟩ ∈ G → ⟨t, v, x⟩ ∈ G') (h : SlotOk G' σ i se)
    : SlotOk G σ i se := by
  cases se with
  | gpr sas => obtain ⟨w, h1, h2⟩ := h; exact ⟨w, h1, fun sa hsa => GprSym.tr (hT sa hsa) (h2 sa hsa)⟩
  | gprZ sas =>
    obtain ⟨w, h1, h2⟩ := h
    refine ⟨w, h1, fun p hp => ?_⟩
    have hmem : p.1 ∈ SlotEntry.sas (.gprZ sas) := List.mem_map.mpr ⟨p, hp, rfl⟩
    exact ⟨GprSym.tr (hT p.1 hmem) (h2 p hp).1, fun hz => SymZ.tr (hT p.1 hmem) ((h2 p hp).2 hz)⟩
  | vec sw sas => obtain ⟨w, h1, h2⟩ := h; exact ⟨w, h1, fun sa hsa => VecSym.tr (hT sa hsa) (h2 sa hsa)⟩

theorem DefOk.grow {G G' : VCtx} {nv x : Nat} {d : DefFact} (hG : ∀ p ∈ G', p ∈ G ∨ nv ≤ p.2.2)
    (hsub : ∀ p ∈ G, p ∈ G') (hx : x < nv) (h : DefOk G x d) : DefOk G' x d := by
  have hm := mem_grow hG (sa := .var x) (by simp [symArgScopeOk, Nat.ble_eq]; omega) x rfl
  cases d with
  | addImm64 b c => intro v hv; obtain ⟨vb, h1, h2⟩ := h v (hm _ _ hv); exact ⟨vb, hsub _ h1, h2⟩
  | scaleOff i sh d =>
    intro v hv; obtain ⟨vi, h1, h2⟩ := h v (hm _ _ hv); exact ⟨vi, hsub _ h1, h2⟩
  | addrSum b i sh d =>
    intro v hv; obtain ⟨vb, vi, h1, h2, h3⟩ := h v (hm _ _ hv)
    exact ⟨vb, vi, hsub _ h1, hsub _ h2, h3⟩
  | imm64 c => intro v hv; exact h v (hm _ _ hv)
  | andVarVar w a b =>
    refine ⟨h.1, fun v hv => ?_⟩
    obtain ⟨va, vb, h1, h2, h3⟩ := h.2 v (hm _ _ hv)
    exact ⟨va, vb, hsub _ h1, hsub _ h2, h3⟩
  | andVarImm w a c =>
    refine ⟨h.1, fun v hv => ?_⟩
    obtain ⟨va, h1, h2⟩ := h.2 v (hm _ _ hv)
    exact ⟨va, hsub _ h1, h2⟩
  | binVarVar w op a b =>
    refine ⟨h.1, fun v hv => ?_⟩
    obtain ⟨va, vb, h1, h2, h3⟩ := h.2 v (hm _ _ hv)
    exact ⟨va, vb, hsub _ h1, hsub _ h2, h3⟩
  | binVarImm w op a c =>
    refine ⟨h.1, fun v hv => ?_⟩
    obtain ⟨va, h1, h2⟩ := h.2 v (hm _ _ hv)
    exact ⟨va, hsub _ h1, h2⟩
  | shlVarImm w a sh =>
    refine ⟨h.1, h.2.1, fun v hv => ?_⟩
    obtain ⟨va, h1, h2⟩ := h.2.2 v (hm _ _ hv)
    exact ⟨va, hsub _ h1, h2⟩
  | sextVar m n a =>
    refine ⟨h.1, h.2.1, h.2.2.1, fun v hv => ?_⟩
    obtain ⟨va, h1, h2⟩ := h.2.2.2 v (hm _ _ hv)
    exact ⟨va, hsub _ h1, h2⟩
  | zextVar m n a =>
    refine ⟨h.1, h.2.1, h.2.2.1, fun v hv => ?_⟩
    obtain ⟨va, h1, h2⟩ := h.2.2.2 v (hm _ _ hv)
    exact ⟨va, hsub _ h1, h2⟩
  | cmpZeroVar co w a =>
    refine ⟨h.1, fun cv hcv => ?_⟩
    obtain ⟨va, h1, h2⟩ := h.2 cv (hm _ _ hcv)
    exact ⟨va, hsub _ h1, h2⟩
  | testBitVar neg w a c =>
    refine ⟨h.1, fun cv hcv => ?_⟩
    obtain ⟨va, h1, h2⟩ := h.2 cv (hm _ _ hcv)
    exact ⟨va, hsub _ h1, h2⟩

theorem execMove_memDefs {I : Isa} {nslots : Nat} {saved : List I.Reg} {mv : I.Move}
    {st st' : SymState I} {deadHint : Bool} {c : List I.Directive}
    (h : execMove I nslots saved mv st deadHint = some (c, st')) : st'.memDefs = st.memDefs := by
  cases mv <;> simp only [execMove] at h <;> (repeat' split at h) <;>
    first | (simp at h; done) |
      (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl)

theorem execMoves_memDefs {I : Isa} {nslots : Nat} {saved : List I.Reg} {deadHint : Bool} :
    ∀ {mvs : List I.Move} {st st' : SymState I} {c : List I.Directive},
    execMoves I nslots saved mvs st deadHint = some (c, st') → st'.memDefs = st.memDefs
  | [], _, _, _, h => by
    simp only [execMoves, Option.some.injEq, Prod.mk.injEq] at h
    exact congrArg SymState.memDefs h.2.symm
  | _ :: _, _, _, _, h => by
    simp only [execMoves, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨_, _⟩, h1, ⟨_, _⟩, h2, he⟩ := h
    simp only [Prod.mk.injEq] at he; rw [← he.2]
    exact (execMoves_memDefs h2).trans (execMove_memDefs h1)

theorem stepPre_memDefs {I : Isa} {h : I.Hints} {ip : Nat} {st st' : SymState I}
    {c : List I.Directive} (hs : stepPre I h ip st = some (c, st')) :
    st'.memDefs = st.memDefs := by
  unfold stepPre at hs; split at hs
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs; exact congrArg SymState.memDefs hs.2.symm
  · obtain ⟨⟨_, _⟩, h1, he⟩ := Option.map_eq_some_iff.mp hs
    simp only [execClearFlags] at he
    split at he <;> simp only [Prod.mk.injEq] at he <;> rw [← he.2] <;>
      simpa using execMoves_memDefs h1

theorem shuffle_memDefs {I : Isa} {nslots : Nat} {saved : List I.Reg} {st st' : SymState I}
    {tgts : List (SymArg × I.Loc)} {c : List I.Directive}
    (hs : shuffle I nslots saved st tgts = some (c, st')) : st'.memDefs = st.memDefs := by
  unfold shuffle at hs; split at hs
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs; exact congrArg SymState.memDefs hs.2.symm
  · dsimp only at hs
    cases hem : execMoves I nslots saved
        (pmoveAux I nslots saved (2 * tgts.length + 4) st tgts []) st with
    | none => simp [hem] at hs
    | some p =>
      rcases p with ⟨code, st1⟩
      simp only [hem] at hs
      split at hs
      · simp only [Option.some.injEq, Prod.mk.injEq] at hs; rw [← hs.2]
        exact execMoves_memDefs hem
      · simp at hs

theorem buildEntryBase_memDefs {I : Isa} {nslots : Nat} {vw : Trie SlotWidth} :
    ∀ {xs : List (SymArg × I.Loc)} {st0 st' : SymState I},
    buildEntryBase I nslots vw xs st0 = some st' → st'.memDefs = st0.memDefs
  | [], _, _, h => by simp only [buildEntryBase, Option.some.injEq] at h; rw [h]
  | (_, loc) :: _, _, _, h => by
    cases loc <;> simp only [buildEntryBase] at h
    · split at h; · simpa using buildEntryBase_memDefs h
      · simp at h
    · split at h; · simpa using buildEntryBase_memDefs h
      · simp at h
    · simpa using buildEntryBase_memDefs h
    · split at h; · simp at h
      · obtain ⟨_, -, h'⟩ := Option.bind_eq_some_iff.mp h; simpa using buildEntryBase_memDefs h'

theorem bindBlockParams_memDefs {I : Isa} {nslots : Nat} :
    ∀ {ts : List Ty} {locs : List I.Loc} {nv0 : Nat} {st0 st' : SymState I},
    bindBlockParams I nslots ts locs nv0 st0 = some st' → st'.memDefs = st0.memDefs
  | [], [], _, _, _, h => by simp only [bindBlockParams, Option.some.injEq] at h; rw [h]
  | t :: _, loc :: _, _, _, _, h => by
    cases loc <;> simp only [bindBlockParams] at h
    · split at h; · simpa using bindBlockParams_memDefs h
      · simp at h
    · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
      split at h; · simpa using bindBlockParams_memDefs h
      · simp at h
    · cases t <;> simp at h; simpa using bindBlockParams_memDefs h
    · split at h; · simp at h
      · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; simpa using bindBlockParams_memDefs h
  | [], _ :: _, _, _, _, h | _ :: _, [], _, _, _, h => by simp [bindBlockParams] at h

theorem bindAbiParams_memDefs {I : Isa} :
    ∀ {ts : List Ty} {locs : Tup (AbiReg I.Reg I.VReg) ts} {nv0 : Nat} {st0 st' : SymState I},
    bindAbiParams I locs nv0 st0 = some st' → st'.memDefs = st0.memDefs
  | [], (), _, _, _, h => by simp only [bindAbiParams, Option.some.injEq] at h; rw [h]
  | _ :: _, (.gpr _, _), _, _, _, h => by
    simp only [bindAbiParams] at h; split at h
    · simpa using bindAbiParams_memDefs h
    · simp at h
  | _ :: _, (.vec _, _), _, _, _, h => by
    simp only [bindAbiParams] at h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; simpa using bindAbiParams_memDefs h

theorem keepRegLoc_frame {gClob : List T.Reg} {vClob : List T.VReg} {fClob : FlagMask}
    (hfr : T.mach.Frame T.gpr.condReads s s' gClob vClob fClob) {sa : SymArg} {rl : RegLoc T.Reg T.VReg T.Cond}
    (hk : keepRegLoc T.toIsa gClob vClob fClob rl = true) (h : RegLocOk T.mach G s sa rl) : RegLocOk T.mach G s' sa rl := by
  cases rl with
  | gpr r => simp only [RegLocOk] at h ⊢; rwa [hfr.1 r (by simpa [keepRegLoc] using hk)]
  | gprZ r => simp only [RegLocOk] at h ⊢; rwa [hfr.1 r (by simpa [keepRegLoc] using hk)]
  | vec v => simp only [RegLocOk] at h ⊢; rwa [hfr.2.1 v (by simpa [keepRegLoc] using hk)]
  | flag c => simp only [RegLocOk] at h ⊢; rwa [hfr.2.2 c hk]

theorem zeroExt32_frame {gClob : List T.Reg} {vClob : List T.VReg} {fClob : FlagMask}
    (hA : Agree T G nv st s σ)
    (hfr : T.mach.Frame T.gpr.condReads s s' gClob vClob fClob) :
    ∀ r ∈ killZeroExt gClob st.zeroExt32,
      T.mach.getGpr s' r = ((T.mach.getGpr s' r).setWidth 32).setWidth 64 := by
  intro r hr
  simp only [killZeroExt, List.mem_filter] at hr
  have hr_not : r ∉ gClob := by
    have h2 := hr.2
    intro hmem
    have hc : gClob.contains r = true := by simpa [List.contains_iff_mem] using hmem
    rw [hc] at h2; cases h2
  rw [hfr.1 r hr_not]
  exact hA.zeroExt32_ok r hr.1

theorem keepFlagCmp_none (I : Isa) (eqNe : Bool) : keepFlagCmp I FlagMask.none eqNe = true := by
  unfold keepFlagCmp; rw [List.all_eq_true]; intro co _
  cases h : I.gpr.condOfCmp? co <;> simp [FlagMask.disjoint, FlagMask.none]

theorem killFlags_none (I : Isa) (fl : Option FlagFact) : killFlags I FlagMask.none fl = fl := by
  cases fl with
  | none => rfl
  | some f => cases f; simp [killFlags, keepFlagCmp_none]

theorem FlagFactOk.frame {gClob : List T.Reg} {vClob : List T.VReg} {fClob : FlagMask}
    (hfr : T.mach.Frame T.gpr.condReads s s' gClob vClob fClob)
    (hf : fClob = FlagMask.none) {fl : Option FlagFact} (h : FlagFactOk T G s fl) :
    FlagFactOk T G s' fl := by
  cases fl with
  | none => trivial
  | some f =>
    cases f with
    | cmp w lhs rhs eqNe =>
      obtain ⟨hw, va, vb, hva, ha, hvb, hb, hcmp⟩ := h
      refine ⟨hw, va, vb, hva, ha, hvb, hb, fun co cc hco hcc => ?_⟩
      subst hf
      rw [hfr.2.2 cc (by simp [FlagMask.disjoint, FlagMask.none])]
      exact hcmp co cc hco hcc

theorem FlagFactOk.kill {gClob : List T.Reg} {vClob : List T.VReg} {fClob : FlagMask}
    (hfr : T.mach.Frame T.gpr.condReads s s' gClob vClob fClob)
    {fl : Option FlagFact} (h : FlagFactOk T G s fl) :
    FlagFactOk T G s' (killFlags T.toIsa fClob fl) := by
  cases fl with
  | none => simp [killFlags]
  | some f =>
    cases f with
    | cmp w lhs rhs eqNe =>
      simp only [killFlags]
      split
      · rename_i hk
        obtain ⟨hw, va, vb, hva, ha, hvb, hb, hcmp⟩ := h
        refine ⟨hw, va, vb, hva, ha, hvb, hb, fun co cc hco hcc => ?_⟩
        unfold keepFlagCmp at hk
        have hmem : co ∈ (if eqNe then [.eq, .ne]
            else [.eq, .ne, .ult, .ule, .ugt, .uge, .slt, .sle, .sgt, .sge]) := by
          cases eqNe <;> cases co <;> simp at hco ⊢
        have hd := List.all_eq_true.mp hk co hmem
        rw [hcc] at hd
        rw [hfr.2.2 cc hd]
        exact hcmp co cc hco hcc
      · trivial

theorem symArgScopeOk_mono {nv nv' : Nat} (hle : nv ≤ nv') {sa : SymArg}
    (h : symArgScopeOk nv sa = true) : symArgScopeOk nv' sa = true := by
  cases sa <;> simp only [symArgScopeOk, Nat.ble_eq] at h ⊢ <;> omega

theorem FlagFactScope.mono {nv nv' : Nat} (hle : nv ≤ nv') {fl : Option FlagFact}
    (h : FlagFactScope nv fl) : FlagFactScope nv' fl := by
  cases fl with
  | none => trivial
  | some f => cases f; exact ⟨symArgScopeOk_mono hle h.1, symArgScopeOk_mono hle h.2⟩

theorem FlagFactOk.tr {G G' : VCtx} {nv : Nat} {s : T.mach.MData} {fl : Option FlagFact}
    (hsub : ∀ p ∈ G, p ∈ G') (hG : ∀ p ∈ G', p ∈ G ∨ nv ≤ p.2.2) (hsc : FlagFactScope nv fl)
    (h : FlagFactOk T G s fl) : FlagFactOk T G' s fl := by
  cases fl with
  | none => trivial
  | some f =>
    cases f with
    | cmp w lhs rhs eqNe =>
      obtain ⟨hw, va, vb, hva, ha, hvb, hb, hcmp⟩ := h
      exact ⟨hw, va, vb, hva.mono hsub, SymBits.tr (mem_grow hG hsc.1) ha,
        hvb.mono hsub, SymBits.tr (mem_grow hG hsc.2) hb, hcmp⟩

theorem FlagFactScope.kill {I : Isa} {nv : Nat} {fClob : FlagMask} {fl : Option FlagFact}
    (h : FlagFactScope nv fl) : FlagFactScope nv (killFlags I fClob fl) := by
  cases fl with
  | none => trivial
  | some f => cases f; simp only [killFlags]; split; exact h; trivial

theorem Agree.setRegs (hA : Agree T G nv st s σ) (R : List (SymArg × RegLoc T.Reg T.VReg T.Cond))
    (hR : ∀ p ∈ R, RegLocOk T.mach G s' p.1 p.2 ∧ symArgScopeOk nv p.1 = true)
    {zExt : List T.Reg}
    (hz : ∀ r ∈ zExt, T.mach.getGpr s' r = ((T.mach.getGpr s' r).setWidth 32).setWidth 64)
    (hfl : FlagFactOk T G s' st.flags) :
    Agree T G nv { st with
      regs := R
      zeroExt32 := zExt } s' σ :=
  { hA with
    regs := fun p hp => (hR p hp).1, regs_lt := fun p hp => (hR p hp).2, zeroExt32_ok := hz,
    flags_ok := hfl }

theorem kill_ok (hA : Agree T G nv st s σ) {gClob : List T.Reg} {vClob : List T.VReg} {fClob : FlagMask}
    (hfr : T.mach.Frame T.gpr.condReads s s' gClob vClob fClob) {p : SymArg × RegLoc T.Reg T.VReg T.Cond}
    (hp : p ∈ killRegs T.toIsa gClob vClob fClob st.regs) : RegLocOk T.mach G s' p.1 p.2 ∧ symArgScopeOk nv p.1 = true :=
  have h : p ∈ st.regs ∧ keepRegLoc T.toIsa gClob vClob fClob p.2 = true := by simpa [killRegs] using hp
  ⟨keepRegLoc_frame hfr h.2 (hA.regs p h.1), hA.regs_lt p h.1⟩

theorem isMoveGpr_false {saved : List T.Reg} {r : T.Reg} (h1 : r ∉ T.frame.allocatable)
    (h2 : r ∉ saved) (h3 : r ∉ T.frame.argRegs) (h4 : r ∉ T.frame.retRegs)
    (h5 : r ∉ T.frame.scratch) : isMoveGpr T.toIsa saved r = false := by
  simp [isMoveGpr, isAllocGpr, h1, h2, h3, h4, h5]
theorem vecWidth?_spec {I : Isa} {t : Ty} {w : SlotWidth} (h : vecWidth? I t = some w) :
    t.size ≤ w.bits ∧ ∃ a b, t = .pair a b := by
  unfold vecWidth? at h; split at h <;> try split at h <;> try split at h
  all_goals simp_all

theorem immVec_vecHolds {t : Ty} {c : Val t} {w : SlotWidth} {bv : BitVec 512} (hle : t.size ≤ w.bits)
    (h : bv.setWidth w.bits = ((toBits t c).setWidth 512).setWidth w.bits) : VecHolds bv t c := by
  have h512 : t.size ≤ 512 := Nat.le_trans hle (SlotWidth.bits_le_512 w); refine ⟨h512, ?_⟩
  rw [← BitVec.setWidth_setWidth_of_le bv hle, h, BitVec.setWidth_setWidth_of_le _ hle,
    BitVec.setWidth_setWidth_of_le _ h512, BitVec.setWidth_eq]

theorem slotWidthEq_iff {a b : SlotWidth} : slotWidthEq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [slotWidthEq]
theorem symArgEq_iff {a b : SymArg} : symArgEq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [symArgEq, slotWidthEq_iff, Nat.beq_eq]
  rename_i a b; cases a <;> cases b <;> decide
theorem gprHolds_boolImm (b : Bool) : GprHolds (if b then 1#64 else 0#64) .bool b := by
  cases b <;> rfl

theorem GprSym.ofMatch {w : BitVec 64} {sa' sa : SymArg} (hm : symArgMatchesGpr sa' sa = true) (h : GprSym G w sa')
    : GprSym G w sa := by
  unfold symArgMatchesGpr at hm; split at hm
  · rename_i he; rw [symArgEq_iff.mp he] at h; exact h
  · split at hm <;> simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, beq_iff_eq, Bool.false_eq_true] at hm <;>
      obtain ⟨_, he⟩ := h
    · obtain ⟨⟨rfl, hk⟩, rfl⟩ := hm; rw [BitVec.setWidth_eq, BitVec.setWidth_eq] at he; subst he; exact ⟨hk, rfl⟩
    · obtain ⟨rfl, rfl⟩ := hm; rw [BitVec.setWidth_eq, BitVec.setWidth_eq] at he; subst he; exact gprHolds_boolImm _

theorem vecTy_of_width (hA : Agree T G nv st s σ) {sa : SymArg} {wsa : SlotWidth}
    (hw : symArgWidth st.vecWidths sa = some wsa) : VecTy G sa := by
  cases sa <;> first | trivial | exact fun t v hm => (hA.vw _ _ hw t v hm).2
theorem isMoveGpr_scratch {saved : List T.Reg} {r : T.Reg} (h : r ∈ T.frame.scratch) :
    isMoveGpr T.toIsa saved r = true := by simp [isMoveGpr, h]
theorem isMoveGpr_of_alloc {saved : List T.Reg} {r : T.Reg} (h : isAllocGpr T.toIsa saved r = true) :
    isMoveGpr T.toIsa saved r = true := by simp [isMoveGpr, h]
theorem Agree.frame (hA : Agree T G nv st s σ) {gClob : List T.Reg} {vClob : List T.VReg} {fClob : FlagMask}
    (hfr : T.mach.Frame T.gpr.condReads s s' gClob vClob fClob)
    (hk : ∀ p ∈ st.regs, keepRegLoc T.toIsa gClob vClob fClob p.2 = true)
    (hz : ∀ r ∈ st.zeroExt32, T.mach.getGpr s' r = ((T.mach.getGpr s' r).setWidth 32).setWidth 64)
    (hf : fClob = FlagMask.none := by rfl) :
    Agree T G nv st s' σ := by
  have hR : ∀ p ∈ st.regs, RegLocOk T.mach G s' p.1 p.2 ∧ symArgScopeOk nv p.1 = true :=
    fun p hp => ⟨keepRegLoc_frame hfr (hk p hp) (hA.regs p hp), hA.regs_lt p hp⟩
  exact { hA with
    regs := fun p hp => (hR p hp).1, regs_lt := fun p hp => (hR p hp).2, zeroExt32_ok := hz,
    flags_ok := hA.flags_ok.frame hfr hf }

theorem mem_gprTaggedEntries {I : Isa} {r : I.Reg} {R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)}
    {sa : SymArg} {z : Bool} (h : (sa, z) ∈ gprTaggedEntries r R) :
    (sa, if z then RegLoc.gprZ r else .gpr r) ∈ R := by
  simp only [gprTaggedEntries, List.mem_filterMap] at h
  obtain ⟨⟨sa', rl⟩, hm, he⟩ := h
  cases rl <;> simp at he
  · obtain ⟨rfl, rfl, rfl⟩ := he; exact hm
  · obtain ⟨rfl, rfl, rfl⟩ := he; exact hm

theorem mem_flagEntries {I : Isa} {c : I.Cond} {R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)}
    {sa : SymArg} (h : sa ∈ flagEntries c R) : (sa, RegLoc.flag c) ∈ R := by
  simp only [flagEntries, List.mem_filterMap] at h
  obtain ⟨⟨sa', rl⟩, hm, he⟩ := h
  cases rl <;> simp at he
  obtain ⟨rfl, rfl⟩ := he; exact hm

theorem mem_vecEntries {I : Isa} {vw : Trie SlotWidth} {w : SlotWidth} {v : I.VReg}
    {R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)} {sa : SymArg} (h : sa ∈ vecEntries vw w v R) :
    (sa, RegLoc.vec v) ∈ R ∧ ∃ wsa, symArgWidth vw sa = some wsa ∧ wsa.bits ≤ w.bits := by
  simp only [vecEntries, List.mem_filterMap] at h
  obtain ⟨⟨sa', rl⟩, hm, he⟩ := h
  cases rl <;> simp only [reduceCtorEq] at he
  split at he <;> try split at he <;> try split at he
  all_goals simp_all

theorem VecSym.setW {sw : SlotWidth} {bv bv' : BitVec 512} {sa : SymArg} (he : bv'.setWidth sw.bits = bv.setWidth sw.bits)
    (h : VecSym G sw bv sa) : VecSym G sw bv' sa := by
  cases sa with
  | var x => exact fun t v hm => ⟨(h t v hm).1, VecHolds.of_setWidth_eq (h t v hm).1 he (h t v hm).2⟩
  | immVec w c =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, by rw [← BitVec.setWidth_setWidth_of_le bv' h1, he, BitVec.setWidth_setWidth_of_le bv h1, h2]⟩
  | _ => exact h

theorem VecSym.widen {sw sw' : SlotWidth} {bv : BitVec 512} {sa : SymArg} (hle : sw.bits ≤ sw'.bits) (h : VecSym G sw bv sa)
    : VecSym G sw' bv sa := by
  cases sa with
  | var x => exact fun t v hm => ⟨Nat.le_trans (h t v hm).1 hle, (h t v hm).2⟩
  | immVec w c => exact ⟨Nat.le_trans h.1 hle, h.2⟩
  | _ => exact h

theorem VecSym.narrow (hA : Agree T G nv st s σ) {sw w wsa : SlotWidth} {bv : BitVec 512} {sa : SymArg}
    (hw : symArgWidth st.vecWidths sa = some wsa) (hle : wsa.bits ≤ w.bits) (h : VecSym G sw bv sa) : VecSym G w bv sa := by
  cases sa with
  | var x => exact fun t v hm => ⟨Nat.le_trans (hA.vw x wsa hw t v hm).1 hle, (h t v hm).2⟩
  | immVec w' c => simp only [symArgWidth, Option.some.injEq] at hw; subst hw; exact ⟨hle, h.2⟩
  | _ => simp [symArgWidth] at hw

theorem FlagSym.toGpr {b : Bool} {w : BitVec 64} {sa : SymArg} (hb : GprHolds w .bool b) (h : FlagSym G b sa) : GprSym
    G w sa := by
  cases sa with
  | var x =>
    intro t v hm
    have h1 := h t v hm
    cases t with
    | bool => simp only [FlagHolds] at h1; subst h1; exact hb
    | _ => exact h1.elim
  | immBool b' => simp only [FlagSym] at h; subst h; exact hb
  | _ => exact h.elim

/-- The frame memory outside slots `[i, i + k)`. -/
abbrev Rest (T : Target) (hints : T.toIsa.Hints) (s₀ : T.mach.MData) (ra : T.mach.Addr) (n : Nat)
    (Rf : Mem 64 → Prop) (m : Mem 64) (σ : List (BitVec 64)) (i k : Nat)
    (zl : Bool := false) : Mem 64 → Prop :=
  Eq m ⋆ ((array64 (baseZ T hints s₀ zl) (σ.take i) ⋆
    array64 (baseZ T hints s₀ zl + BitVec.ofNat 64 (8 * (i + k))) (σ.drop (i + k))) ⋆
      FrZ T hints s₀ ra n Rf zl)

theorem Inv.window {zl : Bool} (hI : Inv T hints s₀ ra n Rf m s σ zl) {i k : Nat}
    (h : i + k ≤ σ.length) : T.mach.mem s =⋆ array64
    (T.mach.getGpr s T.frame.sp + BitVec.ofNat 64 (8 * i)) (slice σ i k) ⋆
      Rest T hints s₀ ra n Rf m σ i k zl := by
  obtain ⟨-, hsp, -, hmem, -, -, -⟩ := hI
  have e := array64_splice_eq (baseZ T hints s₀ zl) (σ.take i) (slice σ i k) (σ.drop (i + k))
  rw [List.length_take_of_le (by omega), slice_length h] at e
  rw [← splice_slice (σ := σ) (i := i) (k := k)] at hmem
  rw [show splice σ i k (slice σ i k) = σ.take i ++ slice σ i k ++ σ.drop (i + k) from rfl, e] at hmem
  rw [hsp]; dsimp only [Rest]; exact sep_cast hmem (by ac_rfl)

theorem Inv.unwindow {zl : Bool} {σ ws : List (BitVec 64)}
    (hI : Inv T hints s₀ ra n Rf m s σ zl) {i k : Nat} (h : i + k ≤ σ.length)
    (hw : ws.length = k)
    (hmem : T.mach.mem s' =⋆ array64 (T.mach.getGpr s T.frame.sp + BitVec.ofNat 64 (8 * i)) ws ⋆
      Rest T hints s₀ ra n Rf m σ i k zl)
    (hg : ∀ r, r ∉ T.frame.scratch → T.mach.getGpr s' r = T.mach.getGpr s r) :
    Inv T hints s₀ ra n Rf m s' (splice σ i k ws) zl := by
  obtain ⟨hl, hsp, hcs, -, hsv, hnd, hzl⟩ := hI
  refine ⟨by rw [length_splice h hw, hl], ?_, fun r hr hns => ?_, ?_, hsv, hnd, fun h => ?_⟩
  · rw [hg _ T.frameSpec.sp_disj.1]; exact hsp
  · rw [hg r fun hs => (T.frameSpec.scratch_disj r hs).2.1 hr]; exact hcs r hr hns
  · have e := array64_splice_eq (baseZ T hints s₀ zl) (σ.take i) ws (σ.drop (i + k))
    rw [List.length_take_of_le (by omega), hw] at e
    show (Eq m ⋆ (array64 (baseZ T hints s₀ zl) (σ.take i ++ ws ++ σ.drop (i + k)) ⋆
      FrZ T hints s₀ ra n Rf zl)) (T.mach.mem s')
    rw [e]; rw [hsp] at hmem; dsimp only [Rest] at hmem; exact sep_cast hmem (by ac_rfl)
  · obtain ⟨htot, hra⟩ := hzl h
    exact ⟨htot, T.frameSpec.raReg_of_raRegs s s' ra
      (fun r hr => hg r (T.frameSpec.ra_disj r hr).2.1) hra⟩

theorem Agree.writeSlot (hA : Agree T G nv st s σ) {i k : Nat} (h : i + k ≤ σ.length) {ws : List (BitVec 64)}
    (hw : ws.length = k) {E : SlotEntry} (hE : SlotOk G (splice σ i k ws) i E)
    (hEs : ∀ sa ∈ E.sas, symArgScopeOk nv sa = true) : Agree T G nv
    { st with slots := (clearSlotRange i k st.slots).insert i E } s (splice σ i k ws) := by
  refine { hA with slots := fun j se hj => ?_, slots_lt := fun j se hj => ?_ } <;>
    (by_cases hji : j = i
     · subst hji; rw [Trie.find?_insert_self] at hj; cases hj; assumption)
  · rw [Trie.find?_insert_ne _ _ hji] at hj
    obtain ⟨h1, h2⟩ := clearSlotRange_find hj
    exact (hA.slots j se h1).splice h hw h2
  · rw [Trie.find?_insert_ne _ _ hji] at hj; exact hA.slots_lt j se (clearSlotRange_sub hj)

/-- Machine-level framing of `Agree`: dropping clobbered facts. -/
theorem Agree.kill {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s s' : T.mach.MData}
    {σ : List (BitVec 64)} {gClob : List T.Reg} {vClob : List T.VReg} {fClob : FlagMask}
    (hA : Agree T G nv st s σ) (hfr : T.mach.Frame T.gpr.condReads s s' gClob vClob fClob) :
    Agree T G nv { st with
      regs := killRegs T.toIsa gClob vClob fClob st.regs
      zeroExt32 := killZeroExt gClob st.zeroExt32
      flags := killFlags T.toIsa fClob st.flags } s' σ :=
  { hA with
    regs := fun _ hp => (kill_ok hA hfr hp).1
    regs_lt := fun _ hp => (kill_ok hA hfr hp).2
    zeroExt32_ok := zeroExt32_frame hA hfr
    flags_ok := hA.flags_ok.kill hfr
    flags_lt := hA.flags_lt.kill }

/-- `Agree` is stable when the value context grows by binders at or above `nv`; the vector-width
trie may simultaneously gain entries for those new binders. -/
theorem Agree.extend {G G' : VCtx} {nv nv' : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) (hle : nv ≤ nv')
    (hG : ∀ p ∈ G', p ∈ G ∨ nv ≤ p.2.2) (hG' : ∀ p ∈ G', p.2.2 < nv') (hsub : ∀ p ∈ G, p ∈ G')
    (huniq : ∀ {t : Ty} {x : Nat} {v₁ v₂ : Val t}, ⟨t, v₁, x⟩ ∈ G' → ⟨t, v₂, x⟩ ∈ G' → v₁ = v₂)
    {vw' : Trie SlotWidth} (hvw0 : ∀ x < nv, vw'.find? x = st.vecWidths.find? x)
    (hvw : ∀ x w, vw'.find? x = some w → nv ≤ x →
      x < nv' ∧ ∀ t v, ⟨t, v, x⟩ ∈ G' → t.size ≤ w.bits ∧ ∃ a b, t = .pair a b)
    (hty : ∀ p ∈ G', nv ≤ p.2.2 → vw'.find? p.2.2 = none → ∀ a b, p.1 ≠ .pair a b) :
    Agree T G' nv' { st with vecWidths := vw' } s σ where
  ctx_lt := hG'
  ctx_uniq := huniq
  regs p hp := RegLocOk.tr (mem_grow hG (hA.regs_lt p hp)) (hA.regs p hp)
  slots i se h := SlotOk.tr (fun sa hsa => mem_grow hG (hA.slots_lt i se h sa hsa)) (hA.slots i se h)
  defs x d h := DefOk.grow hG hsub (hA.defs_lt x d h) (hA.defs x d h)
  vw x w h t v hm := by
    by_cases hx : x < nv
    · rw [hvw0 x hx] at h
      exact hA.vw x w h t v (mem_grow hG (sa := .var x)
        (by simp only [symArgScopeOk, Nat.ble_eq]; omega) x rfl t v hm)
    · exact (hvw x w h (by omega)).2 t v hm
  regs_lt p hp := symArgScopeOk_mono hle (hA.regs_lt p hp)
  slots_lt i se h sa hsa := symArgScopeOk_mono hle (hA.slots_lt i se h sa hsa)
  defs_lt x d h := Nat.lt_of_lt_of_le (hA.defs_lt x d h) hle
  vw_lt x w h := by
    by_cases hx : x < nv
    · omega
    · exact (hvw x w h (by omega)).1
  vt x t v hm hn := by
    rcases hG _ hm with h | h
    · have hx : x < nv := hA.ctx_lt _ h; rw [hvw0 x hx] at hn; exact hA.vt x t v h hn
    · exact hty _ hm h hn
  zeroExt32_ok := hA.zeroExt32_ok
  flags_ok := hA.flags_ok.tr hsub hG hA.flags_lt
  flags_lt := hA.flags_lt.mono hle

/-- `Inv` survives register writes outside `allocatable ∪ saved ∪ arg ∪ ret ∪ scratch`. -/
theorem Inv.keep {zl : Bool} {m : Mem 64} {s s' : T.mach.MData} {σ : List (BitVec 64)}
    (hI : Inv T hints s₀ ra n Rf m s σ zl) (hm : T.mach.mem s' = T.mach.mem s)
    (hs : ∀ r, isMoveGpr T.toIsa hints.saved r = false → T.mach.getGpr s' r = T.mach.getGpr s r) :
    Inv T hints s₀ ra n Rf m s' σ zl := by
  obtain ⟨hl, hsp, hcs, hmem, hsv, hnd, hzl⟩ := hI
  have sd := T.frameSpec.sp_disj
  refine ⟨hl, ?_, fun r hr hns => ?_, by rw [hm]; exact hmem, hsv, hnd, fun h => ?_⟩
  · rw [hs _ (isMoveGpr_false sd.2.1 (fun h => sd.2.2.1 (hsv _ h)) sd.2.2.2.1 sd.2.2.2.2.1 sd.1)]
    exact hsp
  · have cd := T.frameSpec.cs_disj r hr
    rw [hs r (isMoveGpr_false cd.1 hns cd.2.1 cd.2.2 fun h => (T.frameSpec.scratch_disj r h).2.1 hr)]
    exact hcs r hr hns
  · obtain ⟨htot, hra⟩ := hzl h
    refine ⟨htot, T.frameSpec.raReg_of_raRegs s s' ra (fun r hr => ?_) hra⟩
    have rd := T.frameSpec.ra_disj r hr
    exact hs r (isMoveGpr_false rd.1 (fun h => rd.2.2.1 (hsv r h))
      rd.2.2.2.1 rd.2.2.2.2 rd.2.1)

theorem not_scratch_of_isAllocGpr (hsv : ∀ r ∈ hints.saved, r ∈ T.frame.calleeSaved) {r : T.Reg}
    (h : isAllocGpr T.toIsa hints.saved r = true) : r ∉ T.frame.scratch := by
  intro hr
  have sd := T.frameSpec.scratch_disj r hr
  simp only [isAllocGpr, Bool.or_eq_true, List.contains_iff_mem] at h; rcases h with ((h | h) | h) | h
  · exact sd.1 h
  · exact sd.2.1 (hsv r h)
  · exact sd.2.2.1 h
  · exact sd.2.2.2 h

theorem not_vecScratch_of_isAllocVec {v : T.VReg} (h : isAllocVec T.toIsa v = true) :
    v ∉ T.vec.vecScratch := by
  intro hv
  have sd := T.vecSpec.vecScratch_disj v hv
  simp only [isAllocVec, Bool.or_eq_true, List.contains_iff_mem] at h; rcases h with (h | h) | h
  · exact sd.1 h
  · exact sd.2.1 h
  · exact sd.2.2 h

theorem inv_of_frame {zl : Bool} (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hm : T.mach.mem s' = T.mach.mem s) {gC : List T.Reg}
    (hk : T.mach.KeepsGpr s s' gC) (hgc : ∀ r ∈ gC, isMoveGpr T.toIsa hints.saved r = true) :
    Inv T hints s₀ ra n Rf m s' σ zl :=
  Inv.keep hI hm fun r hr => hk r fun h => by rw [hgc r h] at hr; cases hr

theorem spOk_of_inv (hspE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp)) {m : Mem 64}
    {s : T.mach.MData} {σ : List (BitVec 64)} {zl : Bool}
    (hI : Inv T hints s₀ ra n Rf m s σ zl) (hns : 0 < hints.nslots) :
    T.frameSpec.spOk (T.mach.getGpr s T.frame.sp) := by
  cases zl with
  | false => rw [hI.2.1]; exact T.frameSpec.spOk_frame _ _ hspE
  | true =>
    have h0 := (hI.2.2.2.2.2.2 rfl).1
    simp only [Hints.totalSlots] at h0; omega

theorem Agree.addKillZ (hA : Agree T G nv st s σ)
    {gC : List T.Reg} {vC : List T.VReg} {fC : FlagMask}
    (hfr : T.mach.Frame T.gpr.condReads s s' gC vC fC)
    (L : List (SymArg × RegLoc T.Reg T.VReg T.Cond))
    (hL : ∀ p ∈ L, RegLocOk T.mach G s' p.1 p.2 ∧ symArgScopeOk nv p.1 = true)
    (zExt : List T.Reg)
    (hz : ∀ r ∈ zExt, T.mach.getGpr s' r = ((T.mach.getGpr s' r).setWidth 32).setWidth 64)
    (hf : fC = FlagMask.none := by rfl) :
    Agree T G nv { st with
      regs := L ++ killRegs T.toIsa gC vC fC st.regs
      zeroExt32 := zExt } s' σ :=
  hA.setRegs _ (fun p hp => (List.mem_append.mp hp).elim (hL p) (kill_ok hA hfr)) hz
    (hA.flags_ok.frame hfr hf)

theorem Agree.addKill (hA : Agree T G nv st s σ) {gC : List T.Reg} {vC : List T.VReg} {fC : FlagMask}
    (hfr : T.mach.Frame T.gpr.condReads s s' gC vC fC)
    (L : List (SymArg × RegLoc T.Reg T.VReg T.Cond))
    (hL : ∀ p ∈ L, RegLocOk T.mach G s' p.1 p.2 ∧ symArgScopeOk nv p.1 = true)
    (hf : fC = FlagMask.none := by rfl) :
    Agree T G nv { st with
      regs := L ++ killRegs T.toIsa gC vC fC st.regs
      zeroExt32 := killZeroExt gC st.zeroExt32 } s' σ :=
  hA.addKillZ hfr L hL _ (zeroExt32_frame hA hfr) hf

theorem moveCons {saved : List T.Reg} {d : T.Reg} (hd : isMoveGpr T.toIsa saved d = true) :
    ∀ r ∈ d :: T.frame.scratch, isMoveGpr T.toIsa saved r = true := fun _ hr =>
  (List.mem_cons.mp hr).elim (fun h => h ▸ hd) isMoveGpr_scratch

/-- Peel the guard of an `execMove` equation. -/
local macro "peel " he:ident : tactic =>
  `(tactic| (simp only [execMove] at $he:ident; split at $he:ident; · simp at $he:ident))
/-- Peel the guard of an `execMove` equation, naming the simplified guard `hg : t`. -/
local macro "peel " he:ident hg:ident " : " t:term : tactic =>
  `(tactic| (peel $he; rename_i $hg:ident; replace $hg:ident : $t := by simpa using $hg:ident))
/-- Substitute `some (c, st') = some (_, _)`. -/
local macro "fin " he:ident : tactic =>
  `(tactic| (simp only [Option.some.injEq, Prod.mk.injEq] at $he:ident; obtain ⟨h₁, h₂⟩ := $he:ident; subst h₁ h₂))

theorem execMove_ok {zl : Bool} (hspE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp))
    {mv : T.toIsa.Move} {st st' : SymState T.toIsa} {deadHint : Bool}
    {c : List T.Directive} {k : Nat}
    (he : execMove T.toIsa hints.nslots hints.saved mv st deadHint = some (c, st'))
    (hc : c.IsInfixAt (T.mach.prog host) k) (hA : Agree T G nv st s σ)
    (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (kont : ∀ s' σ', Agree T G nv st' s' σ' → Inv T hints s₀ ra n Rf m s' σ' zl →
      T.mach.Run host (k + c.length) s' post)
    : T.mach.Run host k s post := by
  have hsv := hI.2.2.2.2.1
  have hscr : ∀ r ∈ T.frame.scratch, isMoveGpr T.toIsa hints.saved r = true := fun _ h => isMoveGpr_scratch h
  have rsc : ∀ {sa rl}, (sa, rl) ∈ st.regs → symArgScopeOk nv sa = true := fun h => hA.regs_lt _ h
  cases mv with
  | mov d r =>
    peel he hg : isMoveGpr T.toIsa hints.saved d = true; split at he
    · rename_i hdr; fin he; have hdr : d = r := by simpa using hdr
      subst hdr
      refine T.gprSpec.mov_spec hc fun s1 ⟨hd1, hm1⟩ hfr => kont s1 σ ?_ (inv_of_frame hI hm1 hfr.1 (by simpa using hg))
      refine hA.frame (gClob := []) ⟨fun q _ => ?_, hfr.2.1, hfr.2.2⟩
        (fun ⟨_, rl⟩ _ => by cases rl <;> simp [keepRegLoc]) (fun q hq => ?_)
      · exact if hq : q = d then hq ▸ hd1 else hfr.1 q (by simpa using hq)
      · have heq : T.mach.getGpr s1 q = T.mach.getGpr s q :=
          if hq_eq : q = d then hq_eq ▸ hd1 else hfr.1 q (by simpa using hq_eq)
        rw [heq]; exact hA.zeroExt32_ok q hq
    · fin he
      refine T.gprSpec.mov_spec hc fun s1 ⟨hd1, hm1⟩ hfr => ?_
      have hzExt : ∀ q ∈ (if st.zeroExt32.contains r = true then
            d :: killZeroExt [d] st.zeroExt32
          else killZeroExt [d] st.zeroExt32),
          T.mach.getGpr s1 q = ((T.mach.getGpr s1 q).setWidth 32).setWidth 64 := by
        intro q hq
        split at hq
        · rename_i hcr
          rcases List.mem_cons.mp hq with rfl | hq'
          · rw [hd1]; exact hA.zeroExt32_ok r (List.contains_iff_mem.mp hcr)
          · exact zeroExt32_frame hA hfr q hq'
        · exact zeroExt32_frame hA hfr q hq
      refine kont s1 σ (hA.addKillZ hfr _ (fun p hp => ?_) _ hzExt)
        (inv_of_frame hI hm1 hfr.1 (by simpa using hg))
      obtain ⟨⟨sa, z⟩, hsa, rfl⟩ := List.mem_map.mp hp
      have hm := hA.regs _ (mem_gprTaggedEntries hsa)
      have hsc := rsc (mem_gprTaggedEntries hsa)
      cases z
      · exact ⟨by show GprSym G (T.mach.getGpr s1 d) sa; rw [hd1]; exact hm, hsc⟩
      · exact ⟨by show GprSym G (T.mach.getGpr s1 d) sa ∧ SymZ G (T.mach.getGpr s1 d) sa
                  rw [hd1]; exact hm, hsc⟩
  | movi d c =>
    peel he hg : isMoveGpr T.toIsa hints.saved d = true; fin he
    refine execMovi_spec hc fun s1 ⟨hd1, hm1⟩ hfr => ?_
    have hzExt : ∀ q ∈ (if (BitVec.setWidth 64 (BitVec.setWidth 32 c) == c) = true then
        d :: killZeroExt (d :: T.frame.scratch) st.zeroExt32
      else killZeroExt (d :: T.frame.scratch) st.zeroExt32),
        T.mach.getGpr s1 q = ((T.mach.getGpr s1 q).setWidth 32).setWidth 64 := by
      intro q hq
      split at hq
      · rename_i hc_z
        rcases List.mem_cons.mp hq with rfl | hq'
        · rw [hd1]
          have hc_eq : (c.setWidth 32).setWidth 64 = c := beq_iff_eq.mp hc_z
          exact hc_eq.symm
        · exact zeroExt32_frame hA hfr q hq'
      · exact zeroExt32_frame hA hfr q hq
    have hK := hA.kill (gClob := d :: T.frame.scratch) (vClob := [])
      (fClob := (execMovi T.toIsa st deadHint d c).2) hfr
    have hfl_eq : (if (execMovi T.toIsa st deadHint d c).2 == FlagMask.none then st.flags
        else killFlags T.toIsa (execMovi T.toIsa st deadHint d c).2 st.flags) =
        killFlags T.toIsa (execMovi T.toIsa st deadHint d c).2 st.flags := by
      by_cases hf : (execMovi T.toIsa st deadHint d c).2 = FlagMask.none
      · rw [hf]; simp [killFlags_none]
      · simp [hf]
    refine kont s1 σ (by
      rw [hfl_eq]
      exact hK.setRegs _ (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨⟨Nat.le_refl _, by show (T.mach.getGpr s1 d).setWidth 64 = _; rw [hd1]⟩, rfl⟩
        · exact kill_ok hA hfr hp') hzExt hK.flags_ok)
      (inv_of_frame hI hm1 hfr.1 (moveCons hg))
  | ld d i =>
    peel he hg : isAllocGpr T.toIsa hints.saved d = true ∧ i + 1 ≤ hints.nslots; fin he
    have hsp := spOk_of_inv hspE hI (by omega)
    have hi : i < σ.length := by rw [hI.1]; omega
    have hw := hI.window (i := i) (k := 1) (by omega)
    rw [slice_one hi, array64_single] at hw
    refine T.frameSpec.slotLd_spec (not_scratch_of_isAllocGpr hsv hg.1) hsp hw hc fun s1 ⟨hd1, hm1⟩ hfr =>
      kont s1 σ (hA.addKill hfr _ fun p hp => ?_) (inv_of_frame hI hm1 hfr.1 (moveCons (isMoveGpr_of_alloc hg.1)))
    split at hp
    · rename_i sas hf
      obtain ⟨sa, hsa, rfl⟩ := List.mem_map.mp hp
      obtain ⟨x, hx, hall⟩ := hA.slots i _ hf
      rw [List.getElem?_eq_getElem hi] at hx; cases hx
      exact ⟨by show GprSym G (T.mach.getGpr s1 d) sa; rw [hd1]; exact hall sa hsa, hA.slots_lt i _ hf sa hsa⟩
    · rename_i sas hf
      obtain ⟨⟨sa, z⟩, hsa, rfl⟩ := List.mem_map.mp hp
      obtain ⟨x, hx, hall⟩ := hA.slots i _ hf
      rw [List.getElem?_eq_getElem hi] at hx; cases hx
      have hsc : symArgScopeOk nv sa = true :=
        hA.slots_lt i _ hf sa (List.mem_map.mpr ⟨(sa, z), hsa, rfl⟩)
      cases z
      · exact ⟨by show GprSym G (T.mach.getGpr s1 d) sa; rw [hd1]; exact (hall _ hsa).1, hsc⟩
      · exact ⟨by show GprSym G (T.mach.getGpr s1 d) sa ∧ SymZ G (T.mach.getGpr s1 d) sa
                  rw [hd1]; exact ⟨(hall _ hsa).1, (hall _ hsa).2 rfl⟩, hsc⟩
    · simp at hp
  | st i r =>
    peel he hg : r ∉ T.frame.scratch ∧ i + 1 ≤ hints.nslots; fin he
    have hsp := spOk_of_inv hspE hI (by omega)
    have hi : i < σ.length := by rw [hI.1]; omega
    have h1 : i + 1 ≤ σ.length := by omega
    have hw := hI.window h1
    rw [slice_one hi, array64_single] at hw
    refine T.frameSpec.slotSt_spec hg.1 hsp (sep_mono (fun _ => cell64_region) hw) hc
      fun s1 hm1 hfr => kont s1 (splice σ i 1 [T.mach.getGpr s r]) ?_
        (Inv.unwindow hI h1 rfl (by rw [array64_single]; exact hm1) hfr.1)
    have hK : Agree T G nv
        { st with
          regs := killRegs T.toIsa T.frame.scratch [] FlagMask.none st.regs
          zeroExt32 := killZeroExt T.frame.scratch st.zeroExt32 } s1 σ := by
      simpa [killFlags_none] using hA.kill hfr
    refine hK.writeSlot h1 rfl (E := .gprZ (gprTaggedEntries r st.regs))
      ⟨T.mach.getGpr s r, ?_, fun q hq => ?_⟩
      fun sa hsa => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hsa
        exact rsc (mem_gprTaggedEntries hq)
    · rw [getElem?_splice h1 rfl]; simp
    · have hm := hA.regs _ (mem_gprTaggedEntries hq)
      cases hq2 : q.2
      · rw [hq2] at hm; exact ⟨hm, fun h => by cases h⟩
      · rw [hq2] at hm; exact ⟨hm.1, fun _ => hm.2⟩
  | setcc d c =>
    peel he hg : isAllocGpr T.toIsa hints.saved d = true; fin he
    refine T.gprSpec.setcc_spec (not_scratch_of_isAllocGpr hsv hg) hc fun s1 ⟨hd1, hm1⟩ hfr =>
      kont s1 σ (hA.addKill hfr _ fun p hp => ?_) (inv_of_frame hI hm1 hfr.1 (moveCons (isMoveGpr_of_alloc hg)))
    obtain ⟨sa, hsa, rfl⟩ := List.mem_map.mp hp
    exact ⟨FlagSym.toGpr hd1 (hA.regs _ (mem_flagEntries hsa)), rsc (mem_flagEntries hsa)⟩
  | vmov w d r =>
    peel he; fin he
    refine T.vecSpec.vmov_spec hc fun s1 ⟨hd1, hm1⟩ hfr =>
      kont s1 σ (hA.addKillZ hfr _ (fun p hp => ?_) st.zeroExt32
        (fun q hq => by rw [hfr.1 q (by simp)]; exact hA.zeroExt32_ok q hq))
        (inv_of_frame hI hm1 hfr.1 (by simp))
    obtain ⟨sa, hsa, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hm, wsa, hw, hle⟩ := mem_vecEntries hsa
    exact ⟨((VecSym.narrow hA hw hle (hA.regs _ hm)).setW hd1).widen (SlotWidth.bits_le_512 w), rsc hm⟩
  | vmovi w d c =>
    peel he hg : isAllocVec T.toIsa d = true; split at he
    · simp at he
    rename_i code hcode; fin he
    refine T.vecSpec.vmovi_spec hcode (not_vecScratch_of_isAllocVec hg) hc fun s1 ⟨hd1, hm1⟩ hfr =>
      kont s1 σ (hA.addKill hfr [_] fun p hp => ?_) (inv_of_frame hI hm1 hfr.1 hscr)
    rw [List.mem_singleton.mp hp]; exact ⟨⟨SlotWidth.bits_le_512 w, hd1⟩, rfl⟩
  | vld w d i =>
    peel he hg : isAllocVec T.toIsa d = true ∧ i + w.slots ≤ hints.nslots; fin he
    have hwpos : 0 < w.slots := by cases w <;> decide
    have hsp := spOk_of_inv hspE hI (by omega)
    have hk : i + w.slots ≤ σ.length := by rw [hI.1]; exact hg.2
    obtain ⟨bv0, hb0⟩ : ∃ bv, unpackSlotWords w bv = slice σ i w.slots := ⟨_, unpack_packW (slice_length hk)⟩
    have hw := hI.window hk
    rw [← hb0] at hw; refine T.vecSpec.vslotLd_spec (not_vecScratch_of_isAllocVec hg.1) hsp hw hc
      fun s1 ⟨hd1, hm1⟩ hfr => kont s1 σ (hA.addKill hfr _ fun p hq => ?_) (inv_of_frame hI hm1 hfr.1 hscr)
    rcases hf : st.slots.find? i with _ | ⟨sas⟩ | ⟨sas⟩ | ⟨w', sas⟩ <;> try (simp [hf] at hq; done)
    simp only [hf] at hq; split at hq
    · rename_i hww; rw [slotWidthEq_iff] at hww; subst hww
      obtain ⟨sa, hsa, rfl⟩ := List.mem_map.mp hq
      obtain ⟨bv1, h1, h2⟩ := hA.slots i _ hf
      exact ⟨(((h2 sa hsa).setW (unpack_inj (h1.symm.trans hb0.symm)).symm).setW hd1).widen
        (SlotWidth.bits_le_512 _), hA.slots_lt i _ hf sa hsa⟩
    · simp at hq
  | vst w i r =>
    peel he hg : r ∉ T.vec.vecScratch ∧ i + w.slots ≤ hints.nslots; fin he
    have hwpos : 0 < w.slots := by cases w <;> decide
    have hsp := spOk_of_inv hspE hI (by omega)
    have hk : i + w.slots ≤ σ.length := by rw [hI.1]; exact hg.2
    have hreg := sep_mono (fun f hf => array64_toRegion _ _ f
      (by rw [slice_length hk]; have := SlotWidth.slots_le_eight w; omega) hf) (hI.window hk)
    rw [slice_length hk] at hreg
    have hlen := unpackSlotWords_length w (T.mach.getVec s r)
    refine T.vecSpec.vslotSt_spec hg.1 hsp hreg hc fun s1 hm1 hfr =>
      kont s1 (splice σ i w.slots (unpackSlotWords w (T.mach.getVec s r))) ?_ (Inv.unwindow hI hk hlen hm1 hfr.1)
    have hK : Agree T G nv
        { st with
          regs := killRegs T.toIsa T.frame.scratch T.vec.vecScratch FlagMask.none st.regs
          zeroExt32 := killZeroExt T.frame.scratch st.zeroExt32 } s1 σ := by
      simpa [killFlags_none] using hA.kill hfr
    refine hK.writeSlot hk hlen (E := .vec w (vecEntries st.vecWidths w r st.regs))
      ⟨T.mach.getVec s r, slice_splice_self hk hlen, fun sa hsa => ?_⟩
      fun sa hsa => rsc (mem_vecEntries hsa).1
    obtain ⟨hm, wsa, hw, hle⟩ := mem_vecEntries hsa
    exact VecSym.narrow hA hw hle (hA.regs _ hm)

theorem execMoves_ok {zl : Bool} (hspE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp))
    {G : VCtx} {nv : Nat} {m : Mem 64} {deadHint : Bool} :
    ∀ (mvs : List T.toIsa.Move) (st st' : SymState T.toIsa) (c : List T.Directive) (k : Nat)
      (s : T.mach.MData) (σ : List (BitVec 64)),
    execMoves T.toIsa hints.nslots hints.saved mvs st deadHint = some (c, st') →
    c.IsInfixAt (T.mach.prog host) k →
    Agree T G nv st s σ → Inv T hints s₀ ra n Rf m s σ zl →
    (∀ s' σ', Agree T G nv st' s' σ' → Inv T hints s₀ ra n Rf m s' σ' zl →
      T.mach.Run host (k + c.length) s' post) →
    T.mach.Run host k s post := by
  intro mvs; induction mvs with
  | nil =>
    intro st st' c k s σ he _ hA hI kont
    simp only [execMoves, Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    simpa using kont s σ hA hI
  | cons mv mvs ih =>
    intro st st' c k s σ he hc hA hI kont
    simp only [execMoves, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
    obtain ⟨⟨c1, st1⟩, h1, ⟨c2, st2⟩, h2, he⟩ := he
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    have hc' := hc.append
    exact execMove_ok hspE h1 hc'.1 hA hI fun s1 σ1 hA1 hI1 =>
      ih st1 st2 c2 _ s1 σ1 h2 hc'.2 hA1 hI1 fun s2 σ2 hA2 hI2 => by
        simpa [List.length_append, Nat.add_assoc] using kont s2 σ2 hA2 hI2

theorem stepPre_ok {zl : Bool} (hspE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp)) {G : VCtx}
    {nv : Nat} {m : Mem 64} {ip : Nat} {st st' : SymState T.toIsa} {c : List T.Directive}
    {k : Nat} {s : T.mach.MData} {σ : List (BitVec 64)}
    (he : stepPre T.toIsa hints ip st = some (c, st')) (hc : c.IsInfixAt (T.mach.prog host) k)
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (kont : ∀ s' σ', Agree T G nv st' s' σ' → Inv T hints s₀ ra n Rf m s' σ' zl →
      T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  unfold stepPre at he; split at he
  · fin he; simpa using kont s σ hA hI
  · simp only [Option.map_eq_some_iff] at he
    obtain ⟨⟨mc, st1⟩, h1, he⟩ := he
    split at he
    · simp only [execClearFlags, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      have hc' := hc.append
      refine execMoves_ok hspE _ _ _ _ _ _ _ h1 hc'.1 hA hI fun s1 σ1 hA1 hI1 =>
        T.gprSpec.clearFlags_spec hc'.2 fun s2 ⟨hz, hm2⟩ hfr => ?_
      have hA2 : Agree T G nv
          { st1 with
            regs := T.gpr.zeroFlags.map (SymArg.immBool false, RegLoc.flag ·) ++
                    killRegs T.toIsa T.frame.scratch [] FlagMask.all st1.regs
            zeroExt32 := killZeroExt T.frame.scratch st1.zeroExt32
            flags := none } s2 σ1 :=
        { hA1 with
          regs := fun p hp => (List.mem_append.mp hp).elim
            (fun hp' => by
              obtain ⟨c, hcz, rfl⟩ := List.mem_map.mp hp'
              exact hz c hcz)
            (fun hp' => (kill_ok hA1 hfr hp').1)
          regs_lt := fun p hp => (List.mem_append.mp hp).elim
            (fun hp' => by
              obtain ⟨c, _, rfl⟩ := List.mem_map.mp hp'
              rfl)
            (fun hp' => (kill_ok hA1 hfr hp').2)
          zeroExt32_ok := zeroExt32_frame hA1 hfr
          flags_ok := trivial
          flags_lt := trivial }
      simpa [Nat.add_assoc] using
        kont s2 σ1 hA2 (inv_of_frame hI1 hm2 hfr.1 fun _ h => isMoveGpr_scratch h)
    · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact execMoves_ok hspE _ _ _ _ _ _ _ h1 hc hA hI kont

theorem holdsLoc_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} {sa : SymArg} {loc : T.toIsa.Loc}
    (hA : Agree T G nv st s σ) (hh : holdsLoc T.toIsa st sa loc = true) :
    LocOk T.mach G s σ sa loc := by
  cases loc with
  | slot i w => ?_
  | _ =>
    simp only [holdsLoc, List.any_eq_true] at hh
    obtain ⟨⟨sa', rl⟩, hm, he⟩ := hh
    cases rl <;> simp only [Bool.and_eq_true, beq_iff_eq, symArgEq_iff, reduceCtorEq] at he <;>
      obtain ⟨rfl, he⟩ := he <;>
      first
      | exact GprSym.ofMatch he (hA.regs _ hm)
      | exact GprSym.ofMatch he (hA.regs _ hm).1
      | (subst he; exact hA.regs _ hm)
  all_goals
    simp only [holdsLoc] at hh; split at hh
    · rename_i wsa hw; simp only [Bool.and_eq_true] at hh
      obtain ⟨-, hh⟩ := hh
      split at hh
      · rename_i w' sas hf
        simp only [Bool.and_eq_true, slotWidthEq_iff, List.any_eq_true, symArgEq_iff] at hh
        obtain ⟨rfl, sa'', hmem, rfl⟩ := hh
        obtain ⟨bv, h1, h2⟩ := hA.slots i _ hf
        refine Or.inl ⟨⟨bv, h1, fun x hx => ?_⟩, vecTy_of_width hA hw⟩
        rw [List.mem_singleton] at hx; subst hx; exact h2 _ hmem
      · simp at hh
    · simp only [Bool.and_eq_true, slotWidthEq_iff] at hh
      obtain ⟨rfl, hh⟩ := hh
      split at hh
      · rename_i sas hf; simp only [List.any_eq_true] at hh
        obtain ⟨sa', hmem, he⟩ := hh
        obtain ⟨x, h1, h2⟩ := hA.slots i _ hf
        refine Or.inr ⟨rfl, x, h1, fun y hy => ?_⟩
        rw [List.mem_singleton] at hy; subst hy; exact GprSym.ofMatch he (h2 _ hmem)
      · rename_i sas hf; simp only [List.any_eq_true] at hh
        obtain ⟨⟨sa', z⟩, hmem, he⟩ := hh
        obtain ⟨x, h1, h2⟩ := hA.slots i _ hf
        refine Or.inr ⟨rfl, x, h1, fun y hy => ?_⟩
        rw [List.mem_singleton] at hy; subst hy; exact GprSym.ofMatch he (h2 _ hmem).1
      · simp at hh

theorem shuffle_ok {zl : Bool} (hspE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp)) {G : VCtx}
    {nv : Nat} {m : Mem 64} {st st' : SymState T.toIsa} {tgts : List (SymArg × T.toIsa.Loc)}
    {c : List T.Directive} {k : Nat} {s : T.mach.MData} {σ : List (BitVec 64)}
    (hs : shuffle T.toIsa hints.nslots hints.saved st tgts = some (c, st'))
    (hc : c.IsInfixAt (T.mach.prog host) k)
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (kont : ∀ s' σ', (∀ p ∈ tgts, LocOk T.mach G s' σ' p.1 p.2) → Agree T G nv st' s' σ' →
      Inv T hints s₀ ra n Rf m s' σ' zl → T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  unfold shuffle at hs; split at hs
  · rename_i hall
    simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
    simpa using kont s σ (fun ⟨_, _⟩ hp => holdsLoc_ok hA (List.all_eq_true.mp hall _ hp)) hA hI
  · dsimp only at hs; split at hs
    · simp at hs
    · rename_i code st'' he; split at hs
      · rename_i hall
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        exact execMoves_ok hspE _ st _ code k s σ he hc hA hI fun s' σ' hA' hI' =>
          kont s' σ' (fun ⟨_, _⟩ hp => holdsLoc_ok hA' (List.all_eq_true.mp hall _ hp)) hA' hI'
      · simp at hs

/-- Jump/ABI argument transfer: a target established for `toSymArg` of a related argument. -/
theorem locVal_of_locOk {G : VCtx} {s : T.mach.MData} {σ : List (BitVec 64)} {t : Ty}
    {a₁ : Arg Val t} {a₂ : Arg VNat t} {sa : SymArg} {loc : T.toIsa.Loc}
    (hrel : ArgRel G t a₁ a₂) (hsa : toSymArg T.toIsa t a₂ = some sa)
    (hok : LocOk T.mach G s σ sa loc) : LocVal T.mach s σ t a₁.val loc := by
  have hm1 : ∀ {β : Type} (x : β), x ∈ [x] := fun x => List.mem_singleton_self x
  cases hrel with
  | var hm =>
    simp only [toSymArg, Option.some.injEq] at hsa; subst hsa
    cases loc with
    | vec r => exact (hok _ _ hm).2
    | slot i w =>
      exact hok.elim (fun ⟨⟨bv, h1, h2⟩, hty⟩ => Or.inl ⟨⟨bv, h1, h2 _ (hm1 _) _ _ hm⟩, hty _ _ hm⟩)
        fun ⟨hw, x', h1, h2⟩ => Or.inr ⟨hw, x', h1, h2 _ (hm1 _) _ _ hm⟩
    | _ => exact hok _ _ hm
  | imm c =>
    cases t with
    | bool =>
      simp only [toSymArg, Option.some.injEq] at hsa; subst hsa
      cases loc with
      | flag c' => exact hok.symm
      | slot i w =>
        exact hok.elim (fun ⟨⟨_, _, h2⟩, _⟩ => (h2 _ (hm1 _)).elim) fun ⟨hw, x', h1, h2⟩ => Or.inr ⟨hw, x', h1, h2 _ (hm1 _)⟩
      | _ => first | exact hok | exact hok.elim
    | bits k =>
      simp only [toSymArg] at hsa; split at hsa
      · rename_i hk; simp only [Option.some.injEq] at hsa; subst hsa; have hk : k ≤ 64 := by simpa using hk
        have e : ∀ x : BitVec 64, x.setWidth k = (c.setWidth 64).setWidth k → GprHolds x (.bits k) c :=
          fun x h => ⟨hk, by rw [h, BitVec.setWidth_setWidth_of_le _ hk, BitVec.setWidth_eq]⟩
        cases loc with
        | gpr r => exact e _ hok.2
        | slot i w =>
          exact hok.elim (fun ⟨⟨_, _, h2⟩, _⟩ => (h2 _ (hm1 _)).elim) fun ⟨hw, x', h1, h2⟩ =>
            Or.inr ⟨hw, x', h1, e _ (h2 _ (hm1 _)).2⟩
        | _ => exact hok.elim
      · simp at hsa
    | pair a b =>
      simp only [toSymArg, Option.map_eq_some_iff] at hsa
      obtain ⟨w', hw', rfl⟩ := hsa
      have hle := (vecWidth?_spec hw').1
      cases loc with
      | vec r => exact immVec_vecHolds hle hok.2
      | slot i w =>
        refine hok.elim (fun ⟨⟨bv, h1, h2⟩, _⟩ => ?_) fun ⟨_, _, _, h2⟩ => (h2 _ (hm1 _)).elim
        obtain ⟨hww, he⟩ := h2 _ (hm1 _)
        exact Or.inl ⟨⟨bv, h1, Nat.le_trans hle hww, immVec_vecHolds hle he⟩, a, b, rfl⟩
      | _ => exact hok.elim
    | float f => simp [toSymArg] at hsa

/-- `LocOk` is antitone in the context (jumps from inner scopes to outer join points). -/
theorem LocOk.mono {G G' : VCtx} (hsub : ∀ p ∈ G, p ∈ G') {s : T.mach.MData}
    {σ : List (BitVec 64)} {sa : SymArg} {loc : T.toIsa.Loc}
    (h : LocOk T.mach G' s σ sa loc) : LocOk T.mach G s σ sa loc := by
  have hT : ∀ x, sa = .var x → ∀ t (v : Val t), ⟨t, v, x⟩ ∈ G → ⟨t, v, x⟩ ∈ G' := fun _ _ _ _ hm => hsub _ hm
  have hT' : ∀ sa' ∈ [sa], ∀ x, sa' = .var x → ∀ t (v : Val t), ⟨t, v, x⟩ ∈ G → ⟨t, v, x⟩ ∈ G' :=
    fun _ _ _ _ _ _ hm => hsub _ hm
  cases loc with
  | gpr r => exact GprSym.tr hT h
  | vec r => exact VecSym.tr hT h
  | flag c => exact FlagSym.tr hT h
  | slot i w => exact h.imp (fun h => ⟨SlotOk.tr hT' h.1, VecTy.tr hT h.2⟩) fun h => ⟨h.1, SlotOk.tr hT' h.2⟩

theorem paramsOk_of_jumpTargets {G : VCtx} {s : T.mach.MData} {σ : List (BitVec 64)} :
    ∀ {ts : List Ty} {args₁ : Tup (Arg Val) ts} {args : Tup (Arg VNat) ts}
      {ploc : List T.toIsa.Loc} {tgts : List (SymArg × T.toIsa.Loc)},
    TRel (ArgRel G) args₁ args → jumpTargets T.toIsa args ploc = some tgts →
    (∀ p ∈ tgts, LocOk T.mach G s σ p.1 p.2) → ParamsOk T.mach s σ ts (vals args₁) ploc := by
  intro ts args₁ args ploc tgts hrel; induction hrel generalizing ploc tgts with
  | nil => intro hj _; cases ploc <;> simp_all [jumpTargets, ParamsOk]
  | cons hr _ ih =>
    intro hj hok
    cases ploc with
    | nil => simp [jumpTargets] at hj
    | cons loc locs =>
      simp only [jumpTargets] at hj; split at hj
      · rename_i sa rest hsa hrest; simp only [Option.some.injEq] at hj; subst hj
        exact ⟨locVal_of_locOk hr hsa (hok _ (List.mem_cons_self ..)), ih hrest fun p hp => hok p (List.mem_cons_of_mem _ hp)⟩
      · simp at hj

/-! ### Block entry and parameter binding -/

section Entry

/-- Slot facts plus scope bounds. -/
abbrev SlotsOk (G : VCtx) (nv : Nat) (σ : List (BitVec 64)) (sl : Trie SlotEntry) : Prop :=
  ∀ j se, sl.find? j = some se → SlotOk G σ j se ∧ ∀ sa ∈ se.sas, symArgScopeOk nv sa = true

theorem SlotsOk.insert {sl : Trie SlotEntry} (h : SlotsOk G nv σ sl) {i : Nat} {E : SlotEntry}
    (hE : SlotOk G σ i E ∧ ∀ sa ∈ E.sas, symArgScopeOk nv sa = true) : SlotsOk G nv σ (sl.insert i E) := by
  intro j se hj; by_cases hji : j = i
  · subst hji; rw [Trie.find?_insert_self] at hj; cases hj; exact hE
  · rw [Trie.find?_insert_ne _ _ hji] at hj; exact h j se hj

theorem SlotsOk.clear {sl : Trie SlotEntry} (h : SlotsOk G nv σ sl) (i k : Nat) :
    SlotsOk G nv σ (clearSlotRange i k sl) := fun j se hj => h j se (clearSlotRange_sub hj)

theorem addSlotEntry_ok {vw : Trie SlotWidth} {sa : SymArg} {i : Nat} {w : SlotWidth}
    {sl sl' : Trie SlotEntry} (ha : addSlotEntry vw sa i w sl = some sl') (hsl : SlotsOk G nv σ sl)
    (hloc : (SlotOk G σ i (.vec w [sa]) ∧ VecTy G sa) ∨ (w = .w64 ∧ SlotOk G σ i (.gpr [sa])))
    (hsc : symArgScopeOk nv sa = true)
    (hvw : ∀ x wx, vw.find? x = some wx → ∀ t (v : Val t), ⟨t, v, x⟩ ∈ G → ∃ a b, t = .pair a b)
    (hvt : ∀ x, vw.find? x = none → ∀ t (v : Val t), ⟨t, v, x⟩ ∈ G → ∀ a b, t ≠ .pair a b)
    (hi : i + w.slots ≤ σ.length) : SlotsOk G nv σ sl' := by
  have hm1 : sa ∈ [sa] := List.mem_singleton_self _
  have hsc' : ∀ sas : List SymArg, (∀ sa ∈ sas, symArgScopeOk nv sa = true) →
      ∀ sa' ∈ sa :: sas, symArgScopeOk nv sa' = true := fun sas h sa' hm => (List.mem_cons.mp hm).elim (· ▸ hsc) (h sa')
  unfold addSlotEntry at ha
  split at ha
  · rename_i wsa hw
    -- vector form: every packing of the slice satisfies `sa`
    have hall : ∀ bv, slice σ i w.slots = unpackSlotWords w bv → VecSym G w bv sa := by
      intro bv hbv; rcases hloc with ⟨⟨bv0, h1, h2⟩, _⟩ | ⟨rfl, x, _, h2⟩
      · exact (h2 sa hm1).setW (unpack_inj (hbv.symm.trans h1))
      · have h3 := h2 sa hm1
        cases sa with
        | var x' => exact fun t v hm => by obtain ⟨a, b, rfl⟩ := hvw x' wsa hw t v hm; exact (h3 _ v hm).elim
        | immVec _ _ => exact h3.elim
        | _ => simp [symArgWidth] at hw
    have hfresh : SlotOk G σ i (.vec w [sa]) ∧ ∀ sa' ∈ (SlotEntry.vec w [sa]).sas, symArgScopeOk nv sa' = true :=
      ⟨⟨packW (slice σ i w.slots), (unpack_packW (slice_length hi)).symm,
        by simpa using hall _ (unpack_packW (slice_length hi)).symm⟩, by simpa [SlotEntry.sas] using hsc⟩
    split at ha
    · simp at ha
    · split at ha
      · rename_i w' sas hf; split at ha
        · rename_i hww; rw [slotWidthEq_iff] at hww; subst hww; simp only [Option.some.injEq] at ha; subst ha
          obtain ⟨⟨bv, h1, h2⟩, h3⟩ := hsl i _ hf
          exact hsl.insert ⟨⟨bv, h1, fun sa' hm => (List.mem_cons.mp hm).elim (· ▸ hall bv h1) (h2 sa')⟩, hsc' sas h3⟩
        · simp only [Option.some.injEq] at ha; subst ha; exact (hsl.clear _ _).insert hfresh
      · simp only [Option.some.injEq] at ha; subst ha; exact (hsl.clear _ _).insert hfresh
  · rename_i hw; split at ha
    · simp at ha
    rename_i hw64; have hw64 : w = .w64 := by simpa [slotWidthEq_iff] using hw64
    subst hw64; have hi' : i < σ.length := by simp [SlotWidth.slots] at hi; omega
    have hall : ∀ x, σ[i]? = some x → GprSym G x sa := by
      intro x hx; rcases hloc with ⟨⟨bv0, _, h2⟩, hty⟩ | ⟨_, x0, h1, h2⟩
      · have h3 := h2 sa hm1
        cases sa with
        | var x' => exact fun t v hm => by obtain ⟨a, b, rfl⟩ := hty t v hm; exact (hvt x' hw _ v hm a b rfl).elim
        | immVec _ _ => simp [symArgWidth] at hw
        | _ => exact h3.elim
      · rw [hx] at h1; cases h1; exact h2 sa hm1
    have hfresh : SlotOk G σ i (.gpr [sa]) ∧ ∀ sa' ∈ (SlotEntry.gpr [sa]).sas, symArgScopeOk nv sa' = true :=
      ⟨⟨σ[i], List.getElem?_eq_getElem hi', by simpa using hall _ (List.getElem?_eq_getElem hi')⟩,
        by simpa [SlotEntry.sas] using hsc⟩
    split at ha
    · rename_i sas hf; simp only [Option.some.injEq] at ha; subst ha
      obtain ⟨⟨x, h1, h2⟩, h3⟩ := hsl i _ hf
      exact hsl.insert ⟨⟨x, h1, fun sa' hm => (List.mem_cons.mp hm).elim (· ▸ hall x h1) (h2 sa')⟩, hsc' sas h3⟩
    · simp only [Option.some.injEq] at ha; subst ha; exact (hsl.clear _ _).insert hfresh

theorem Agree.setSlots (hA : Agree T G nv st s σ) {sl : Trie SlotEntry} (h : SlotsOk G nv σ sl) : Agree T G nv
    { st with slots := sl } s σ :=
  { hA with slots := fun j se hj => (h j se hj).1, slots_lt := fun j se hj => (h j se hj).2 }
theorem Agree.pushRegZ (hA : Agree T G nv st s σ) {sa : SymArg} {rl : RegLoc T.Reg T.VReg T.Cond}
    (h : RegLocOk T.mach G s sa rl) (hsc : symArgScopeOk nv sa = true)
    (zExt : List T.Reg)
    (hz : ∀ r ∈ zExt, T.mach.getGpr s r = ((T.mach.getGpr s r).setWidth 32).setWidth 64) :
    Agree T G nv
    { st with
      regs := (sa, rl) :: st.regs
      zeroExt32 := zExt } s σ :=
  hA.setRegs _ (fun p hp => (List.mem_cons.mp hp).elim (fun e => e ▸ ⟨h, hsc⟩)
    fun hp => ⟨hA.regs p hp, hA.regs_lt p hp⟩) hz hA.flags_ok

theorem Agree.pushReg (hA : Agree T G nv st s σ) {sa : SymArg} {rl : RegLoc T.Reg T.VReg T.Cond}
    (h : RegLocOk T.mach G s sa rl) (hsc : symArgScopeOk nv sa = true) : Agree T G nv
    { st with regs := (sa, rl) :: st.regs } s σ :=
  hA.pushRegZ h hsc st.zeroExt32 hA.zeroExt32_ok

theorem buildEntryBase_aux {vw : Trie SlotWidth} {s : T.mach.MData} (hσ : σ.length = hints.nslots) :
    ∀ (live : List (SymArg × T.toIsa.Loc)) (st st' : SymState T.toIsa), st.vecWidths = vw →
    buildEntryBase T.toIsa hints.nslots vw live st = some st' →
    (∀ p ∈ live, LocOk T.mach G s σ p.1 p.2) → (∀ p ∈ live, symArgScopeOk nv p.1 = true) →
    Agree T G nv st s σ → Agree T G nv st' s σ
  | [], st, st', _, hb, _, _, hA => by simp only [buildEntryBase, Option.some.injEq] at hb; subst hb; exact hA
  | (sa, loc) :: rest, st, st', hvw, hb, hl, hs, hA => by
    have hl0 := hl _ (List.mem_cons_self ..)
    have hs0 : symArgScopeOk nv sa = true := hs _ (List.mem_cons_self ..)
    have IH := fun st1 (h1 : st1.vecWidths = vw) hb1 => buildEntryBase_aux hσ rest st1 st' h1 hb1
      (fun p hp => hl p (List.mem_cons_of_mem _ hp)) fun p hp => hs p (List.mem_cons_of_mem _ hp)
    cases loc with
    | gpr r =>
      simp only [buildEntryBase] at hb; split at hb
      · exact IH _ (by exact hvw) hb (hA.pushReg (rl := .gpr r) hl0 hs0)
      · simp at hb
    | vec v =>
      simp only [buildEntryBase] at hb; split at hb
      · exact IH _ (by exact hvw) hb (hA.pushReg (rl := .vec v) hl0 hs0)
      · simp at hb
    | flag c => simp only [buildEntryBase] at hb; exact IH _ (by exact hvw) hb (hA.pushReg (rl := .flag c) hl0 hs0)
    | slot i w =>
      simp only [buildEntryBase] at hb; split at hb
      · simp at hb
      rename_i hi
      simp only [Option.bind_eq_some_iff] at hb
      obtain ⟨sl', ha, hb⟩ := hb
      exact IH _ (by exact hvw) hb (hA.setSlots (addSlotEntry_ok ha (fun j se hj => ⟨hA.slots j se hj, hA.slots_lt j se hj⟩) hl0 hs0
        (fun x wx hx t v hm => (hA.vw x wx (hvw ▸ hx) t v hm).2) (fun x hx t v hm => hA.vt x t v hm (hvw ▸ hx))
        (by rw [hσ]; simpa using hi)))

theorem mem_head_cases (hlt : ∀ p ∈ G, p.2.2 < nv) {t t' : Ty} {x : Val t} {v' : Val t'}
    (hm : (⟨t', v', nv⟩ : (t : Ty) × Val t × VNat t) ∈ (⟨t, x, nv⟩ :: G : VCtx))
    (P : (t : Ty) → Val t → Prop) (hP : P t x) : P t' v' := by
  rcases List.mem_cons.mp hm with he | hm
  · cases he; exact hP
  · exact absurd (hlt _ hm) (Nat.lt_irrefl _)

theorem not_pair_of_isGprTy {I : Isa} {t : Ty} (h : isGprTy I t = true) : ∀ a b, t ≠ .pair a b := by
  cases t <;> simp_all [isGprTy]

theorem Agree.bindVar (hA : Agree T G nv st s σ) {t : Ty} (x : Val t) {vw' : Trie SlotWidth}
    (hvw0 : ∀ y < nv, vw'.find? y = st.vecWidths.find? y)
    (hvwn : ∀ w, vw'.find? nv = some w → t.size ≤ w.bits ∧ ∃ a b, t = .pair a b) (hvwy : ∀ y, nv < y → vw'.find? y = none)
    (hvtn : vw'.find? nv = none → ∀ a b, t ≠ .pair a b) : Agree T (⟨t, x, nv⟩ :: G) (nv + 1) { st with vecWidths := vw' } s σ
    := by
  have hlt := hA.ctx_lt
  refine hA.extend (Nat.le_succ nv) (fun p hp => ?_) (fun p hp => ?_)
    (fun p hp => List.mem_cons_of_mem _ hp) (ctx_uniq_cons hlt hA.ctx_uniq)
    hvw0 (fun y w hy hle => ?_) (fun p hp hle hn => ?_)
  · exact (List.mem_cons.mp hp).imp (fun e => e ▸ Nat.le_refl _) id |>.symm
  · exact (List.mem_cons.mp hp).elim (fun e => e ▸ Nat.lt_succ_self _) fun hp => Nat.lt_succ_of_lt (hlt p hp)
  · obtain rfl : y = nv := Decidable.byContradiction fun hy' => by rw [hvwy y (by omega)] at hy; cases hy
    exact ⟨Nat.lt_succ_self _, fun t' v' hm =>
      mem_head_cases hlt hm (fun t' _ => t'.size ≤ w.bits ∧ ∃ a b, t' = .pair a b) (hvwn w hy)⟩
  · exact (List.mem_cons.mp hp).elim (fun e => by subst e; exact hvtn hn)
      fun hp => absurd (hlt p hp) (Nat.not_lt.mpr hle)

theorem Agree.congrG {G' : VCtx} {nv' : Nat} (hA : Agree T G nv st s σ) (hG : ∀ p, p ∈ G ↔ p ∈ G') (hn : nv = nv') :
    Agree T G' nv' st s σ := by
  subst hn
  exact hA.extend (Nat.le_refl _) (fun p hp => Or.inl ((hG p).mpr hp)) (fun p hp => hA.ctx_lt p ((hG p).mpr hp))
    (fun p hp => (hG p).mp hp) (fun h1 h2 => hA.ctx_uniq ((hG _).mpr h1) ((hG _).mpr h2))
    (fun _ _ => rfl) (fun y w hy hle => absurd (hA.vw_lt y w hy) (by omega))
    (fun p hp hle _ => absurd (hA.ctx_lt p ((hG p).mpr hp)) (Nat.not_lt.mpr hle))

theorem vw_none_of_ge (hA : Agree T G nv st s σ) {y : Nat} (hy : nv ≤ y) : st.vecWidths.find? y = none := by
  cases h : st.vecWidths.find? y with
  | none => rfl
  | some w => exact absurd (hA.vw_lt y w h) (by omega)

/-- Binding a non-vector variable (no new width). -/
theorem Agree.bindSame (hA : Agree T G nv st s σ) {t : Ty} (x : Val t) (hty : ∀ a b, t ≠ .pair a b) : Agree T
    (⟨t, x, nv⟩ :: G) (nv + 1) { st with vecWidths := st.vecWidths } s σ :=
  hA.bindVar x (fun _ _ => rfl) (fun w h => by rw [vw_none_of_ge hA (Nat.le_refl _)] at h; cases h)
    (fun y hy => vw_none_of_ge hA (by omega)) fun _ => hty

/-- Binding a vector variable with width `w`. -/
theorem Agree.bindIns (hA : Agree T G nv st s σ) {t : Ty} (x : Val t) {w : SlotWidth} (hw : vecWidth? T.toIsa t = some w)
    : Agree T (⟨t, x, nv⟩ :: G) (nv + 1) { st with vecWidths := st.vecWidths.insert nv w } s σ :=
  hA.bindVar x (fun y hy => Trie.find?_insert_ne _ _ (by omega))
    (fun w' h => by rw [Trie.find?_insert_self] at h; cases h; exact vecWidth?_spec hw)
    (fun y hy => by rw [Trie.find?_insert_ne _ _ (by omega)]; exact vw_none_of_ge hA (by omega))
    fun hn => by rw [Trie.find?_insert_self] at hn; cases hn

end Entry

theorem scope_nv (nv : Nat) : symArgScopeOk (nv + 1) (.var nv) = true := by simp [symArgScopeOk]

theorem bindBlockParams_aux {s : T.mach.MData} {σ : List (BitVec 64)} (hσ : σ.length = hints.nslots) :
    ∀ (ts : List Ty) (xs : Tup Val ts) (ploc : List T.toIsa.Loc) (G : VCtx) (nv : Nat) (st st' : SymState T.toIsa),
    bindBlockParams T.toIsa hints.nslots ts ploc nv st = some st' → ParamsOk T.mach s σ ts xs ploc →
    Agree T G nv st s σ → Agree T (Tup.zip xs (Tup.levels ts nv) ++ G) (nv + ts.length) st' s σ
  | [], _, [], G, nv, st, st', hb, _, hA => by simp only [bindBlockParams, Option.some.injEq] at hb; subst hb; exact hA
  | [], _, _ :: _, _, _, _, _, hb, _, _ | _ :: _, _, [], _, _, _, _, hb, _, _ => by simp [bindBlockParams] at hb
  | t :: ts, (x, xs), loc :: locs, G, nv, st, st', hb, ⟨hp0, hp'⟩, hA => by
    have fin := fun st1 hb1 hA1 => (bindBlockParams_aux hσ ts xs locs (⟨t, x, nv⟩ :: G) _ st1 st' hb1 hp' hA1).congrG
      (G' := Tup.zip (x, xs) (Tup.levels (t :: ts) nv) ++ G) (fun p => List.perm_middle.mem_iff) (show nv + 1 + ts.length = nv + (ts.length + 1) by omega)
    have hlt := hA.ctx_lt
    cases loc with
    | gpr r =>
      simp only [bindBlockParams] at hb; split at hb
      · rename_i hg
        have hg : r ∉ T.frame.scratch ∧ isGprTy T.toIsa t = true := by simpa using hg
        exact fin _ hb ((hA.bindSame x (not_pair_of_isGprTy hg.2)).pushReg (rl := .gpr r)
          (fun t' v' hm => mem_head_cases hlt hm (fun t v => GprHolds (T.mach.getGpr s r) t v) hp0) (scope_nv nv))
      · simp at hb
    | vec v =>
      simp only [bindBlockParams, Option.bind_eq_some_iff] at hb
      obtain ⟨w, hw, hb⟩ := hb
      split at hb
      · exact fin _ hb ((hA.bindIns x hw).pushReg (rl := .vec v) (fun t' v' hm => mem_head_cases hlt hm
          (fun t0 v0 => t0.size ≤ SlotWidth.w512.bits ∧ VecHolds (T.mach.getVec s v) t0 v0) ⟨hp0.1, hp0⟩) (scope_nv nv))
      · simp at hb
    | flag c =>
      simp only [bindBlockParams] at hb
      split at hb
      · exact fin _ hb ((hA.bindSame x (by simp)).pushReg (rl := .flag c) (fun t' v' hm =>
          mem_head_cases hlt hm (fun t v => FlagHolds (T.mach.evalCond s c) t v) hp0) (scope_nv nv))
      · simp at hb
    | slot i w =>
      simp only [bindBlockParams] at hb
      split at hb
      · simp at hb
      rename_i hg
      have hg : i + w.slots ≤ hints.nslots ∧ (isGprTy T.toIsa t = false → ¬vecWidth? T.toIsa t = none) := by
        simpa using hg
      simp only [Option.bind_eq_some_iff] at hb
      obtain ⟨sl', ha, hb⟩ := hb
      have hA1 : Agree T (⟨t, x, nv⟩ :: G) (nv + 1) { st with vecWidths := match vecWidth? T.toIsa t with
          | some wt => st.vecWidths.insert nv wt | none => st.vecWidths } s σ := by
        split
        · rename_i wt hwt; exact hA.bindIns x hwt
        · rename_i hwt; refine hA.bindSame x ?_
          cases hgt : isGprTy T.toIsa t
          · exact (hg.2 hgt hwt).elim
          · exact not_pair_of_isGprTy hgt
      refine fin _ hb (hA1.setSlots (addSlotEntry_ok ha (fun j se hj => ⟨hA1.slots j se hj, hA1.slots_lt j se hj⟩) ?_
        (scope_nv nv) (fun y wy hy t' v' hm => (hA1.vw y wy hy t' v' hm).2) (fun y hy t' v' hm => hA1.vt y t' v' hm hy)
        (by rw [hσ]; exact hg.1)))
      rcases hp0 with ⟨⟨bv, h1, h2, h3⟩, hpair⟩ | ⟨rfl, y, h1, h2⟩
      · refine Or.inl ⟨⟨bv, h1, fun sa hm => ?_⟩, fun t' v' hm => mem_head_cases hlt hm (fun t _ => ∃ a b, t = .pair a b) hpair⟩
        rw [List.mem_singleton] at hm; subst hm
        exact fun t' v' hm => mem_head_cases hlt hm (fun t v => t.size ≤ w.bits ∧ VecHolds bv t v) ⟨h2, h3⟩
      · refine Or.inr ⟨rfl, y, h1, fun sa hm => ?_⟩
        rw [List.mem_singleton] at hm; subst hm
        exact fun t' v' hm => mem_head_cases hlt hm (fun t v => GprHolds y t v) h2

theorem bindAbiParams_aux {s : T.mach.MData} {σ : List (BitVec 64)} :
    ∀ (ts : List Ty) (xs : Tup Val ts) (locs : Tup (AbiReg T.Reg T.VReg) ts) (G : VCtx) (nv : Nat)
      (st st' : SymState T.toIsa), bindAbiParams T.toIsa locs nv st = some st' → TRel (T.mach.AbiHolds s) locs xs →
    Agree T G nv st s σ → Agree T (Tup.zip xs (Tup.levels ts nv) ++ G) (nv + ts.length) st' s σ
  | [], _, _, G, nv, st, st', hb, _, hA => by simp only [bindAbiParams, Option.some.injEq] at hb; subst hb; exact hA
  | t :: ts, (x, xs), (loc, locs), G, nv, st, st', hb, .cons hr0 hr', hA => by
    have fin := fun st1 hb1 (hA1 : Agree T _ _ st1 s σ) => (bindAbiParams_aux ts xs locs (⟨t, x, nv⟩ :: G) _ st1 st' hb1 hr' hA1).congrG
      (G' := Tup.zip (x, xs) (Tup.levels (t :: ts) nv) ++ G) (fun p => List.perm_middle.mem_iff) (show nv + 1 + ts.length = nv + (ts.length + 1) by omega)
    cases loc with
    | gpr r =>
      simp only [bindAbiParams] at hb; split at hb
      · rename_i hg
        let zExt := if tyEq t (.bits 32) then r :: killZeroExt [r] st.zeroExt32 else st.zeroExt32
        have hzExt : ∀ q ∈ zExt,
            T.mach.getGpr s q = ((T.mach.getGpr s q).setWidth 32).setWidth 64 := by
          intro q hq
          dsimp only [zExt] at hq
          split at hq
          · rename_i ht32
            have ht32' : t = .bits 32 := tyEq_iff.mp ht32
            rcases List.mem_cons.mp hq with rfl | hq'
            · subst ht32'
              have ⟨_, hw⟩ := hr0
              rw [hw, setWidth_32_64_val]
            · have hq_mem : q ∈ st.zeroExt32 := by
                simp only [killZeroExt, List.mem_filter] at hq'
                exact hq'.1
              exact hA.zeroExt32_ok q hq_mem
          · exact hA.zeroExt32_ok q hq
        have hreg : RegLocOk T.mach (⟨t, x, nv⟩ :: G) s (.var nv) (.gprZ r) :=
          ⟨fun t' v' hm => mem_head_cases hA.ctx_lt hm
              (fun t v => GprHolds (T.mach.getGpr s r) t v) (AbiGprHolds.toGprHolds hr0),
            fun t' v' hm => mem_head_cases hA.ctx_lt hm
              (fun t v => AbiGprHolds (T.mach.getGpr s r) t v) hr0⟩
        exact fin _ hb ((hA.bindSame x (not_pair_of_isGprTy hg)).pushRegZ (rl := .gprZ r)
          hreg (scope_nv nv) zExt hzExt)
      · simp at hb
    | vec v =>
      simp only [bindAbiParams, Option.bind_eq_some_iff] at hb
      obtain ⟨w, hw, hb⟩ := hb
      exact fin _ hb ((hA.bindIns x hw).pushReg (rl := .vec v) (fun t' v' hm => mem_head_cases hA.ctx_lt hm
        (fun t0 v0 => t0.size ≤ SlotWidth.w512.bits ∧ VecHolds (T.mach.getVec s v) t0 v0) ⟨hr0.1, hr0⟩) (scope_nv nv))

/-- Block entry: the live set of `Entry` (lexical `defs`/`vw` of the enclosing group). -/
theorem buildEntryBase_ok {G : VCtx} {nv : Nat} {vw : Trie SlotWidth} {defs : Trie DefFact}
    {live : List (SymArg × T.toIsa.Loc)} {st' : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)}
    (hb : buildEntryBase T.toIsa hints.nslots vw live
      { regs := [], slots := .empty, defs := defs, vecWidths := vw } = some st')
    (hlive : ∀ p ∈ live, LocOk T.mach G s σ p.1 p.2)
    (hlt : ∀ p ∈ live, symArgScopeOk nv p.1 = true) (hσ : σ.length = hints.nslots)
    (hA : Agree T G nv { regs := [], slots := .empty, defs := defs, vecWidths := vw } s σ) :
    Agree T G nv st' s σ :=
  buildEntryBase_aux hσ live _ _ rfl hb hlive hlt hA

theorem bindBlockParams_ok {G : VCtx} {nv : Nat} :
    ∀ {ts : List Ty} {xs : Tup Val ts} {ploc : List T.toIsa.Loc} {st st' : SymState T.toIsa}
      {s : T.mach.MData} {σ : List (BitVec 64)},
    bindBlockParams T.toIsa hints.nslots ts ploc nv st = some st' →
    ParamsOk T.mach s σ ts xs ploc → σ.length = hints.nslots → Agree T G nv st s σ →
    Agree T (Tup.zip xs (Tup.levels ts nv) ++ G) (nv + ts.length) st' s σ :=
  fun hb hp hσ hA => bindBlockParams_aux hσ _ _ _ _ _ _ _ hb hp hA

theorem bindAbiParams_ok {G : VCtx} {nv : Nat} :
    ∀ {ts : List Ty} {xs : Tup Val ts} {locs : Tup (AbiReg T.Reg T.VReg) ts}
      {st st' : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)},
    bindAbiParams T.toIsa locs nv st = some st' → TRel (T.mach.AbiHolds s) locs xs →
    Agree T G nv st s σ → Agree T (Tup.zip xs (Tup.levels ts nv) ++ G) (nv + ts.length) st' s σ :=
  fun hb hr hA => bindAbiParams_aux _ _ _ _ _ _ _ hb hr hA

theorem isStdBitWidth_spec {n : Nat} (h : isStdBitWidth n = true) :
    n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 := by
  simp only [isStdBitWidth, Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with ((h | h) | h) | h <;> simp [h]

private theorem findSlotGprGo_spec {G : VCtx} {σ : List (BitVec 64)} {slots : Trie SlotEntry}
    (hS : ∀ j se, slots.find? j = some se → SlotOk G σ j se) {x : Nat} :
    ∀ (i fuel idx : Nat), findSlotGprGo slots x i fuel = some idx →
      idx < i + fuel ∧ ∃ w, σ[idx]? = some w ∧ ∀ t v, ⟨t, v, x⟩ ∈ G → GprHolds w t v
  | _, 0, _, h => by cases h
  | i, fuel + 1, idx, h => by
    simp only [findSlotGprGo] at h
    cases hf : slots.find? i with
    | none =>
      rw [hf] at h
      obtain ⟨hlt, hw⟩ := findSlotGprGo_spec hS (i + 1) fuel idx h
      exact ⟨by omega, hw⟩
    | some se =>
      rw [hf] at h
      cases se with
      | vec _ _ =>
        obtain ⟨hlt, hw⟩ := findSlotGprGo_spec hS (i + 1) fuel idx h
        exact ⟨by omega, hw⟩
      | gpr sas =>
        dsimp only at h
        split at h
        · rename_i hany
          simp only [Option.some.injEq] at h; subst h
          obtain ⟨sa, hsa, heq⟩ := List.any_eq_true.mp hany
          rw [symArgEq_iff] at heq; subst heq
          obtain ⟨w, hw, hall⟩ := hS i _ hf
          exact ⟨by omega, w, hw, hall (.var x) hsa⟩
        · obtain ⟨hlt, hw⟩ := findSlotGprGo_spec hS (i + 1) fuel idx h
          exact ⟨by omega, hw⟩
      | gprZ sas =>
        dsimp only at h
        split at h
        · rename_i hany
          simp only [Option.some.injEq] at h; subst h
          obtain ⟨⟨sa, z⟩, hsa, heq⟩ := List.any_eq_true.mp hany
          rw [symArgEq_iff] at heq; subst heq
          obtain ⟨w, hw, hall⟩ := hS i _ hf
          exact ⟨by omega, w, hw, (hall (.var x, z) hsa).1⟩
        · obtain ⟨hlt, hw⟩ := findSlotGprGo_spec hS (i + 1) fuel idx h
          exact ⟨by omega, hw⟩

theorem findSlotGpr_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {x idx : Nat}
    (hf : findSlotGpr hints.nslots st.slots x = some idx) :
    idx < hints.nslots ∧ ∃ w, σ[idx]? = some w ∧ ∀ t v, ⟨t, v, x⟩ ∈ G → GprHolds w t v := by
  simpa using findSlotGprGo_spec hA.slots 0 hints.nslots idx hf

private theorem spAddr_cell64 {zl : Bool} {idx : Nat} {w64 : BitVec 64}
    (hlt : idx < hints.nslots) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hσ : σ[idx]? = some w64) :
    ∃ R : Mem 64 → Prop, (cell64 ((spAddr T.toIsa idx).eval (T.mach.getGpr s)) w64 ⋆ R)
      (T.mach.mem s) := by
  have hi : idx < σ.length := by rw [hI.1]; omega
  have hwin := hI.window (i := idx) (k := 1) (by omega)
  rw [slice_one hi, array64_single] at hwin
  rw [List.getElem?_eq_getElem hi] at hσ
  cases hσ
  have hev : (spAddr T.toIsa idx).eval (T.mach.getGpr s) =
      T.mach.getGpr s T.frame.sp + BitVec.ofNat 64 (8 * idx) := rfl
  rw [hev]
  exact ⟨_, hwin⟩

theorem spAddr_load_bits {zl : Bool} {idx w : Nat} {w64 : BitVec 64} {vx : BitVec w}
    (hlt : idx < hints.nslots) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hw : isStdBitWidth w = true) (hσ : σ[idx]? = some w64)
    (hgpr : GprHolds w64 (.bits w) vx) :
    loadVal (T.mach.mem s) (.bits w) ((spAddr T.toIsa idx).eval (T.mach.getGpr s)) = some vx := by
  obtain ⟨R, hcell⟩ := spAddr_cell64 hlt hI hσ
  rw [loadVal_bits_of_cell64 (isStdBitWidth_spec hw) hcell, hgpr.2]

theorem spAddr_load_bool {zl : Bool} {idx : Nat} {w64 : BitVec 64} {b : Bool}
    (hlt : idx < hints.nslots) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hσ : σ[idx]? = some w64) (hgpr : GprHolds w64 .bool b) :
    ∃ v8 : BitVec 8,
      loadVal (T.mach.mem s) (.bits 8) ((spAddr T.toIsa idx).eval (T.mach.getGpr s)) = some v8 ∧
      v8 = BitVec.ofNat 8 b.toNat := by
  obtain ⟨R, hcell⟩ := spAddr_cell64 hlt hI hσ
  exact ⟨w64.setWidth 8, loadVal_bits_of_cell64 (.inl rfl) hcell, hgpr⟩

end Lemmas

theorem orElse_eq_some {α : Type} {a b : Option α} {r : α} (h : (a <|> b) = some r) :
    a = some r ∨ b = some r := by
  cases a <;> simp_all [HOrElse.hOrElse, OrElse.orElse, Option.orElse]

theorem slotWidthEq_eq {a b : SlotWidth} (h : slotWidthEq a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [slotWidthEq]

theorem symArgEq_eq {a b : SymArg} (h : symArgEq a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [symArgEq]
  · rename_i x y; revert h; cases x <;> cases y <;> decide
  · exact slotWidthEq_eq h.1

theorem regLocEq_eq {I : Isa} {a b : RegLoc I.Reg I.VReg I.Cond} (h : regLocEq a b = true) :
    a = b := by
  cases a <;> cases b <;> simp_all [regLocEq]

theorem gprSym_match {G : VCtx} {w : BitVec 64} {sa' sa : SymArg} (h : GprSym G w sa')
    (hm : symArgMatchesGpr sa' sa = true) : GprSym G w sa := by
  unfold symArgMatchesGpr at hm
  split at hm
  · next he => rwa [← symArgEq_eq he]
  · split at hm
    · simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, beq_iff_eq] at hm
      obtain ⟨⟨rfl, hle⟩, rfl⟩ := hm
      simp only [GprSym, BitVec.setWidth_eq] at h ⊢
      exact ⟨hle, by rw [h.2]⟩
    · simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      simp only [GprSym, BitVec.setWidth_eq] at h ⊢
      rw [h.2]; cases ‹Bool› <;> rfl
    · simp at hm

theorem mem_cons_top {G : VCtx} {nv : Nat} (hlt : ∀ p ∈ G, p.2.2 < nv) {t t' : Ty} {v : Val t}
    {v' : Val t'} (h : (⟨t', v', nv⟩ : (a : Ty) × Val a × VNat a) ∈ ⟨t, v, nv⟩ :: G) :
    (⟨t', v'⟩ : Sigma Val) = ⟨t, v⟩ := by
  rcases List.mem_cons.mp h with h | h
  · cases h; rfl
  · exact absurd (hlt _ h) (Nat.lt_irrefl _)

private theorem bv_shiftLeft_shiftLeft {w : Nat} (a : BitVec w) (k1 k2 : Nat) :
    (a <<< k1) <<< k2 = a <<< (k1 + k2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mod_mul_mod, Nat.pow_add, Nat.mul_assoc]

private theorem defOk_addVarImm {G : VCtx} {nv x : Nat} {vx c : BitVec 64}
    {defs : Trie DefFact} (hdefs : ∀ y d, defs.find? y = some d → DefOk G y d)
    (hlt : ∀ p ∈ G, p.2.2 < nv) (hm : ⟨i64, vx, x⟩ ∈ G) :
    DefOk (⟨i64, vx + c, nv⟩ :: G) nv (recordAddVarImm defs x c) := by
  unfold recordAddVarImm
  cases hd : defs.find? x with
  | none =>
    intro v hv; cases mem_cons_top hlt hv
    exact ⟨vx, List.mem_cons_of_mem _ hm, rfl⟩
  | some d =>
    have hdx := hdefs x d hd
    cases d with
    | imm64 c0 =>
      intro v hv; cases mem_cons_top hlt hv
      have hx := hdx vx hm; rw [hx]
    | addImm64 b disp =>
      intro v hv; cases mem_cons_top hlt hv
      obtain ⟨vb, hb, hvx⟩ := hdx vx hm
      exact ⟨vb, List.mem_cons_of_mem _ hb, by simp [hvx, BitVec.add_assoc]⟩
    | scaleOff idx sh disp =>
      intro v hv; cases mem_cons_top hlt hv
      obtain ⟨vi, hi, hvx⟩ := hdx vx hm
      exact ⟨vi, List.mem_cons_of_mem _ hi, by simp [hvx, BitVec.add_assoc]⟩
    | addrSum b idx sh disp =>
      dsimp only
      split
      · intro v hv; cases mem_cons_top hlt hv
        exact ⟨vx, List.mem_cons_of_mem _ hm, rfl⟩
      · intro v hv; cases mem_cons_top hlt hv
        obtain ⟨vb, vi, hb, hi, hvx⟩ := hdx vx hm
        exact ⟨vb, vi, List.mem_cons_of_mem _ hb, List.mem_cons_of_mem _ hi,
          by simp [hvx, BitVec.add_assoc]⟩
    | andVarVar _ _ _ | andVarImm _ _ _ | binVarVar _ _ _ _ | binVarImm _ _ _ _
    | shlVarImm _ _ _ | sextVar _ _ _ | zextVar _ _ _ | cmpZeroVar _ _ _
    | testBitVar _ _ _ _ =>
      intro v hv; cases mem_cons_top hlt hv
      exact ⟨vx, List.mem_cons_of_mem _ hm, rfl⟩

private theorem defOk_addScale {G : VCtx} {nv x y : Nat} {vx vy : BitVec 64}
    {dfx : DefFact} {dfy? : Option DefFact} {df : DefFact}
    (hx : DefOk G x dfx) (hy : ∀ d, dfy? = some d → DefOk G y d)
    (hlt : ∀ p ∈ G, p.2.2 < nv) (hmx : ⟨i64, vx, x⟩ ∈ G) (hmy : ⟨i64, vy, y⟩ ∈ G)
    (h : recordAddScale dfx dfy? y = some df) :
    DefOk (⟨i64, vx + vy, nv⟩ :: G) nv df := by
  unfold recordAddScale at h
  cases dfx with
  | scaleOff idx sh d1 =>
    dsimp only at h
    split at h
    · cases dfy? with
      | some dy =>
        cases dy with
        | addImm64 b d2 =>
          cases h; intro v hv; cases mem_cons_top hlt hv
          obtain ⟨vi, hi, hvx⟩ := hx vx hmx
          obtain ⟨vb, hb, hvy⟩ := hy (.addImm64 b d2) rfl vy hmy
          refine ⟨vb, vi, List.mem_cons_of_mem _ hb, List.mem_cons_of_mem _ hi, ?_⟩
          rw [hvx, hvy]; ac_rfl
        | _ =>
          cases h; intro v hv; cases mem_cons_top hlt hv
          obtain ⟨vi, hi, hvx⟩ := hx vx hmx
          refine ⟨vy, vi, List.mem_cons_of_mem _ hmy, List.mem_cons_of_mem _ hi, ?_⟩
          rw [hvx]; ac_rfl
      | none =>
        cases h; intro v hv; cases mem_cons_top hlt hv
        obtain ⟨vi, hi, hvx⟩ := hx vx hmx
        refine ⟨vy, vi, List.mem_cons_of_mem _ hmy, List.mem_cons_of_mem _ hi, ?_⟩
        rw [hvx]; ac_rfl
    · simp at h
  | _ => simp at h

private theorem defOk_addBase {G : VCtx} {nv x y : Nat} {vx vy : BitVec 64}
    {dfx : DefFact} {dfy? : Option DefFact} {df : DefFact}
    (hx : DefOk G x dfx) (hy : ∀ d, dfy? = some d → DefOk G y d)
    (hlt : ∀ p ∈ G, p.2.2 < nv) (hmx : ⟨i64, vx, x⟩ ∈ G) (hmy : ⟨i64, vy, y⟩ ∈ G)
    (h : recordAddBase dfx y dfy? = some df) :
    DefOk (⟨i64, vx + vy, nv⟩ :: G) nv df := by
  unfold recordAddBase at h
  cases dfx with
  | addImm64 b d1 =>
    cases dfy? with
    | some dy =>
      cases dy with
      | addImm64 b2 d2 =>
        cases h; intro v hv; cases mem_cons_top hlt hv
        obtain ⟨vb, hb, hvx⟩ := hx vx hmx
        obtain ⟨vb2, hb2, hvy⟩ := hy (.addImm64 b2 d2) rfl vy hmy
        refine ⟨vb, vb2, List.mem_cons_of_mem _ hb, List.mem_cons_of_mem _ hb2, ?_⟩
        rw [hvx, hvy]; simp only [BitVec.shiftLeft_zero]; ac_rfl
      | _ =>
        cases h; intro v hv; cases mem_cons_top hlt hv
        obtain ⟨vb, hb, hvx⟩ := hx vx hmx
        refine ⟨vb, vy, List.mem_cons_of_mem _ hb, List.mem_cons_of_mem _ hmy, ?_⟩
        rw [hvx]; simp only [BitVec.shiftLeft_zero]; ac_rfl
    | none =>
      cases h; intro v hv; cases mem_cons_top hlt hv
      obtain ⟨vb, hb, hvx⟩ := hx vx hmx
      refine ⟨vb, vy, List.mem_cons_of_mem _ hb, List.mem_cons_of_mem _ hmy, ?_⟩
      rw [hvx]; simp only [BitVec.shiftLeft_zero]; ac_rfl
  | _ => simp at h

private theorem defOk_addVarVar {G : VCtx} {nv x y : Nat} {vx vy : BitVec 64}
    {defs : Trie DefFact} (hdefs : ∀ z d, defs.find? z = some d → DefOk G z d)
    (hlt : ∀ p ∈ G, p.2.2 < nv) (hmx : ⟨i64, vx, x⟩ ∈ G) (hmy : ⟨i64, vy, y⟩ ∈ G) :
    DefOk (⟨i64, vx + vy, nv⟩ :: G) nv (recordAddVarVar defs x y) := by
  let s1 := (defs.find? x).bind (recordAddScale · (defs.find? y) y)
  let s2 := (defs.find? y).bind (recordAddScale · (defs.find? x) x)
  let b1 := (defs.find? x).bind (recordAddBase · y (defs.find? y))
  let b2 := (defs.find? y).bind (recordAddBase · x (defs.find? x))
  have fall : DefOk (⟨i64, vx + vy, nv⟩ :: G) nv (.addrSum x y 0 0) := by
    intro v hv; cases mem_cons_top hlt hv
    exact ⟨vx, vy, List.mem_cons_of_mem _ hmx, List.mem_cons_of_mem _ hmy, by simp⟩
  have hs1 : ∀ df, s1 = some df → DefOk (⟨i64, vx + vy, nv⟩ :: G) nv df := by
    intro df hs; obtain ⟨dx, hdx, hk⟩ := Option.bind_eq_some_iff.mp hs
    exact defOk_addScale (hdefs x dx hdx) (fun d hd => hdefs y d hd) hlt hmx hmy hk
  have hs2 : ∀ df, s2 = some df → DefOk (⟨i64, vx + vy, nv⟩ :: G) nv df := by
    intro df hs; obtain ⟨dy, hdy, hk⟩ := Option.bind_eq_some_iff.mp hs
    simpa [BitVec.add_comm] using
      defOk_addScale (hdefs y dy hdy) (fun d hd => hdefs x d hd) hlt hmy hmx hk
  have hb1 : ∀ df, b1 = some df → DefOk (⟨i64, vx + vy, nv⟩ :: G) nv df := by
    intro df hb; obtain ⟨dx, hdx, hk⟩ := Option.bind_eq_some_iff.mp hb
    exact defOk_addBase (hdefs x dx hdx) (fun d hd => hdefs y d hd) hlt hmx hmy hk
  have hb2 : ∀ df, b2 = some df → DefOk (⟨i64, vx + vy, nv⟩ :: G) nv df := by
    intro df hb; obtain ⟨dy, hdy, hk⟩ := Option.bind_eq_some_iff.mp hb
    simpa [BitVec.add_comm] using
      defOk_addBase (hdefs y dy hdy) (fun d hd => hdefs x d hd) hlt hmy hmx hk
  have hmid : DefOk (⟨i64, vx + vy, nv⟩ :: G) nv
      ((s1 <|> s2 <|> b1 <|> b2).getD (.addrSum x y 0 0)) := by
    cases ho : (s1 <|> s2 <|> b1 <|> b2) with
    | none => exact fall
    | some df =>
      rcases orElse_eq_some ho with h | h
      · exact hs1 df h
      rcases orElse_eq_some h with h | h
      · exact hs2 df h
      rcases orElse_eq_some h with h | h
      · exact hb1 df h
      · exact hb2 df h
  unfold recordAddVarVar; dsimp only
  cases hx : defs.find? x with
  | none =>
    cases hy : defs.find? y with
    | none => simpa [s1, s2, b1, b2, hx, hy] using hmid
    | some dy =>
      cases dy with
      | imm64 c =>
        have hc : vy = c := hdefs y (.imm64 c) hy vy hmy
        subst hc; simpa using defOk_addVarImm hdefs hlt hmx (c := vy)
      | _ => simpa [s1, s2, b1, b2, hx, hy] using hmid
  | some dx =>
    cases dx with
    | imm64 c =>
      have hc : vx = c := hdefs x (.imm64 c) hx vx hmx
      subst hc; simpa [BitVec.add_comm] using defOk_addVarImm hdefs hlt hmy (c := vx)
    | _ =>
      cases hy : defs.find? y with
      | none => simpa [s1, s2, b1, b2, hx, hy] using hmid
      | some dy =>
        cases dy with
        | imm64 c =>
          have hc : vy = c := hdefs y (.imm64 c) hy vy hmy
          subst hc; simpa using defOk_addVarImm hdefs hlt hmx (c := vy)
        | _ => simpa [s1, s2, b1, b2, hx, hy] using hmid

private theorem defOk_rmwBin {G : VCtx} {nv w : Nat} {op : RmwOp}
    {a₁ b₁ : Arg Val (.bits w)} {a b : Arg VNat (.bits w)} {df : DefFact}
    (ha : ArgRel G (.bits w) a₁ a) (hb : ArgRel G (.bits w) b₁ b)
    (hlt : ∀ p ∈ G, p.2.2 < nv) (h : recordRmwBin w op a b = some df) :
    DefOk (Tup.zip (op.eval a₁.val b₁.val, ()) (Tup.levels [.bits w] nv) ++ G) nv df := by
  cases a with
  | var x =>
    cases b with
    | var y =>
      unfold recordRmwBin at h; split at h; · simp at h
      rename_i hw; replace hw : w ≤ 64 := by simpa [Nat.ble_eq] using hw
      simp only [Option.some.injEq] at h; subst h
      cases ha with | var hmx => cases hb with | var hmy =>
      refine ⟨hw, fun v hv => ?_⟩
      simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
      exact ⟨_, _, List.mem_cons_of_mem _ hmx, List.mem_cons_of_mem _ hmy, rfl⟩
    | imm c =>
      unfold recordRmwBin at h; split at h; · simp at h
      rename_i hw; replace hw : w ≤ 64 := by simpa [Nat.ble_eq] using hw
      simp only [Option.some.injEq] at h; subst h
      cases ha with | var hmx => cases hb with | imm =>
      refine ⟨hw, fun v hv => ?_⟩
      simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
      exact ⟨_, List.mem_cons_of_mem _ hmx, by
        rw [BitVec.setWidth_setWidth_of_le c hw, BitVec.setWidth_eq]; rfl⟩
  | imm c =>
    cases b with
    | var y =>
      unfold recordRmwBin at h; split at h; · simp at h
      rename_i hw; replace hw : w ≤ 64 := by simpa [Nat.ble_eq] using hw
      dsimp only at h; split at h
      · rename_i hcomm; simp only [Option.some.injEq] at h; subst h
        cases ha with | imm => cases hb with | var hmy =>
        refine ⟨hw, fun v hv => ?_⟩
        simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
        exact ⟨_, List.mem_cons_of_mem _ hmy, by
          simp only [Arg.val]
          rw [BitVec.setWidth_setWidth_of_le c hw, BitVec.setWidth_eq, RmwOp.eval_comm hcomm]⟩
      · simp at h
    | imm _ => simp [recordRmwBin] at h

private theorem recordDef_rs {defs : Trie DefFact} {sig rs : List Ty} {code : OpCode sig rs}
    {args : Tup (Arg VNat) sig} {df : DefFact} (hd : recordDef defs code args = some df) :
    ∃ w, rs = [.bits w] := by
  cases code with
  | add t | sub t | shl t | copy t | and t | or t | xor t =>
    cases t with
    | bits n => exact ⟨n, rfl⟩
    | _ => simp [recordDef] at hd
  | sext _ n | zext _ n => exact ⟨n, rfl⟩
  | _ => simp [recordDef] at hd

theorem wp_recordDef {G : VCtx} {nv : Nat} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d)
    {sig rs : List Ty} {code : OpCode sig rs}
    {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    (hrel : TRel (ArgRel G) args₁ args) (hlt : ∀ p ∈ G, p.2.2 < nv) {P : Tup Val rs → Prop}
    (hwp : code.wp (vals args₁) P) {df : DefFact} (hd : recordDef defs code args = some df) :
    code.wp (vals args₁) (fun rvs => P rvs ∧
      0 < rs.length ∧ DefOk (Tup.zip rvs (Tup.levels rs nv) ++ G) nv df) := by
  cases code with
  | add t =>
    cases t with
    | bits n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
      by_cases hn64 : n = 64
      · subst hn64
        cases a with
        | var x =>
          cases b with
          | var y =>
            simp only [recordDef] at hd
            cases hd; cases h1 with | var hmx => cases h2 with | var hmy =>
            simp only [OpCode.wp_add, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
              ite_false, Tup.zip, Tup.levels] at hwp ⊢
            exact ⟨hwp, by simp, defOk_addVarVar hdefs hlt hmx hmy⟩
          | imm c =>
            simp only [recordDef] at hd
            cases hd; cases h1 with | var hm => cases h2 with | imm =>
            simp only [OpCode.wp_add, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
              ite_false, BitVec.setWidth_eq, Tup.zip, Tup.levels] at hwp ⊢
            exact ⟨hwp, by simp, defOk_addVarImm hdefs hlt hm⟩
        | imm c =>
          cases b with
          | var y =>
            simp only [recordDef] at hd
            cases hd; cases h1 with | imm => cases h2 with | var hm =>
            simp only [OpCode.wp_add, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
              ite_false, BitVec.setWidth_eq, Tup.zip, Tup.levels] at hwp ⊢
            refine ⟨hwp, by simp, ?_⟩
            rw [BitVec.add_comm]; exact defOk_addVarImm hdefs hlt hm
          | imm _ => simp [recordDef] at hd
      · have hnf : Nat.beq n 64 = false :=
          Bool.eq_false_iff.mpr (by simpa [Nat.beq_eq] using hn64)
        simp only [recordDef, hnf, Bool.not_false, ↓reduceIte] at hd
        simp only [OpCode.wp_add, vals, lift2, Ty.hasFloat, Bool.false_eq_true, ite_false]
          at hwp ⊢
        exact ⟨hwp, by simp, defOk_rmwBin h1 h2 hlt hd⟩
    | _ => simp [recordDef] at hd
  | sub t =>
    cases t with
    | bits n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
      cases a with
      | var x =>
        cases b with
        | imm c =>
          by_cases hn64 : n = 64
          · subst hn64
            simp only [recordDef, Nat.beq_eq, ↓reduceIte] at hd
            cases hd; cases h1 with | var hm => cases h2 with | imm =>
            simp only [OpCode.wp_sub, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
              ite_false, BitVec.setWidth_eq, Tup.zip, Tup.levels] at hwp ⊢
            refine ⟨hwp, by simp, ?_⟩
            rw [BitVec.sub_eq_add_neg]; exact defOk_addVarImm hdefs hlt hm
          · have hnf : Nat.beq n 64 = false :=
              Bool.eq_false_iff.mpr (by simpa [Nat.beq_eq] using hn64)
            simp only [recordDef, hnf, Bool.false_eq_true, ↓reduceIte] at hd
            simp only [OpCode.wp_sub, vals, lift2, Ty.hasFloat, Bool.false_eq_true, ite_false]
              at hwp ⊢
            exact ⟨hwp, by simp, defOk_rmwBin h1 h2 hlt hd⟩
        | var y =>
          simp only [recordDef] at hd
          simp only [OpCode.wp_sub, vals, lift2, Ty.hasFloat, Bool.false_eq_true, ite_false]
            at hwp ⊢
          exact ⟨hwp, by simp, defOk_rmwBin h1 h2 hlt hd⟩
      | imm _ =>
        simp only [recordDef] at hd
        cases b <;> simp [recordRmwBin, RmwOp.isComm] at hd
    | _ => simp [recordDef] at hd
  | or t =>
    cases t with
    | bits n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
      simp only [recordDef] at hd
      simp only [OpCode.wp_or, vals, lift2] at hwp ⊢
      exact ⟨hwp, by simp, defOk_rmwBin h1 h2 hlt hd⟩
    | _ => simp [recordDef] at hd
  | xor t =>
    cases t with
    | bits n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
      simp only [recordDef] at hd
      simp only [OpCode.wp_xor, vals, lift2] at hwp ⊢
      exact ⟨hwp, by simp, defOk_rmwBin h1 h2 hlt hd⟩
    | _ => simp [recordDef] at hd
  | shl t =>
    cases t with
    | bits n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      cases a with
      | imm _ => simp [recordDef] at hd
      | var x =>
        cases b with
        | var _ => simp [recordDef] at hd
        | imm k =>
          by_cases hn : n = 64
          · subst hn
            have hb64 : Nat.beq 64 64 = true := rfl
            have hk : k.toNat < 64 := Decidable.byContradiction fun hke => by
              simp [recordDef, Nat.blt_eq, hke] at hd
            simp only [recordDef, hb64, ↓reduceIte] at hd
            split at hd
            · cases hd
            rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
            cases h1 with | var hm => cases h2 with | imm =>
            dsimp only [vals, Arg.val] at hwp ⊢
            simp only [OpCode.wp_shl, lift2, Ty.hasFloat, Bool.false_eq_true, ite_false] at hwp ⊢
            rw [Nat.mod_eq_of_lt hk] at hwp ⊢
            refine ⟨hwp, by simp, ?_⟩
            cases hdx : defs.find? x with
            | none =>
              rw [hdx] at hd; cases hd
              intro v hv; simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
              exact ⟨_, List.mem_cons_of_mem _ hm, by simp⟩
            | some d =>
              rw [hdx] at hd
              have hxok := hdefs x d hdx
              cases d with
              | imm64 c0 =>
                cases hd; intro v hv; simp only [Tup.zip, Tup.levels] at hv
                cases mem_cons_top hlt hv; simp only [DefOk] at hxok; rw [hxok _ hm]
              | addImm64 b d =>
                cases hd; intro v hv; simp only [Tup.zip, Tup.levels] at hv
                cases mem_cons_top hlt hv
                obtain ⟨vb, hb, hvx⟩ := hxok _ hm
                exact ⟨vb, List.mem_cons_of_mem _ hb, by simp [hvx]⟩
              | scaleOff idx sh d =>
                dsimp only at hd; split at hd
                · cases hd; intro v hv; simp only [Tup.zip, Tup.levels] at hv
                  cases mem_cons_top hlt hv
                  obtain ⟨vi, hi, hvx⟩ := hxok _ hm
                  exact ⟨vi, List.mem_cons_of_mem _ hi, by simp [hvx, bv_shiftLeft_shiftLeft]⟩
                · cases hd
              | addrSum _ _ _ _ | andVarVar _ _ _ | andVarImm _ _ _ | binVarVar _ _ _ _
              | binVarImm _ _ _ _ | shlVarImm _ _ _ | sextVar _ _ _ | zextVar _ _ _
              | cmpZeroVar _ _ _ | testBitVar _ _ _ _ =>
                cases hd; intro v hv; simp only [Tup.zip, Tup.levels] at hv
                cases mem_cons_top hlt hv
                exact ⟨_, List.mem_cons_of_mem _ hm, by simp⟩
          · have hnf : Nat.beq n 64 = false :=
              Bool.eq_false_iff.mpr (by simpa [Nat.beq_eq] using hn)
            simp only [recordDef, hnf, Bool.false_eq_true, ↓reduceIte] at hd
            split at hd
            · rename_i hc
              simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
              obtain ⟨⟨hnle, _⟩, hklt⟩ := hc
              cases hd
              rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
              cases h1 with | var hm => cases h2 with | imm =>
              dsimp only [vals, Arg.val] at hwp ⊢
              simp only [OpCode.wp_shl, lift2, Ty.hasFloat, Bool.false_eq_true, ite_false]
                at hwp ⊢
              rw [Nat.mod_eq_of_lt hklt] at hwp ⊢
              refine ⟨hwp, by simp, hnle, hklt, fun v hv => ?_⟩
              simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
              exact ⟨_, List.mem_cons_of_mem _ hm, rfl⟩
            · cases hd
    | _ => simp [recordDef] at hd
  | copy t =>
    cases t with
    | bits n =>
      rcases args with ⟨a, ⟨⟩⟩
      have hn : n = 64 := Decidable.byContradiction fun hne => by
        cases a <;> simp [recordDef, hne] at hd
      subst hn
      rcases hrel with _ | ⟨h1, -⟩
      cases a with
      | imm c =>
        simp only [recordDef, Nat.beq_eq, ↓reduceIte] at hd
        cases hd; cases h1 with | imm =>
        simp only [OpCode.wp_copy, vals, Arg.val, BitVec.setWidth_eq] at hwp ⊢
        refine ⟨hwp, by simp, fun v' hm' => ?_⟩
        simp only [Tup.zip, Tup.levels] at hm'; cases mem_cons_top hlt hm'; simp
      | var x =>
        simp only [recordDef, Nat.beq_eq, ↓reduceIte] at hd
        cases h1 with | var hm =>
        dsimp only [vals, Arg.val] at hwp ⊢
        simp only [OpCode.wp_copy] at hwp ⊢
        refine ⟨hwp, by simp, ?_⟩
        cases hdx : defs.find? x with
        | none =>
          rw [hdx] at hd; cases hd
          intro v hv; simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
          exact ⟨_, List.mem_cons_of_mem _ hm, by simp⟩
        | some d =>
          rw [hdx] at hd
          have h' := hdefs x d hdx
          cases d with
          | imm64 c0 =>
            simp only [DefFact.isAddr, ↓reduceIte, Option.some.injEq] at hd; subst hd
            intro v hv; simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
            simpa using h' _ hm
          | addImm64 b disp =>
            simp only [DefFact.isAddr, ↓reduceIte, Option.some.injEq] at hd; subst hd
            intro v hv; simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
            obtain ⟨vb, hb, hvx⟩ := h' _ hm
            exact ⟨vb, List.mem_cons_of_mem _ hb, hvx⟩
          | scaleOff idx sh disp =>
            simp only [DefFact.isAddr, ↓reduceIte, Option.some.injEq] at hd; subst hd
            intro v hv; simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
            obtain ⟨vi, hi, hvx⟩ := h' _ hm
            exact ⟨vi, List.mem_cons_of_mem _ hi, hvx⟩
          | addrSum b idx sh disp =>
            simp only [DefFact.isAddr, ↓reduceIte, Option.some.injEq] at hd; subst hd
            intro v hv; simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
            obtain ⟨vb, vi, hb, hi, hvx⟩ := h' _ hm
            exact ⟨vb, vi, List.mem_cons_of_mem _ hb, List.mem_cons_of_mem _ hi, hvx⟩
          | andVarVar _ _ _ | andVarImm _ _ _ | binVarVar _ _ _ _ | binVarImm _ _ _ _
          | shlVarImm _ _ _ | sextVar _ _ _ | zextVar _ _ _ | cmpZeroVar _ _ _
          | testBitVar _ _ _ _ =>
            simp only [DefFact.isAddr, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hd
            subst hd
            intro v hv; simp only [Tup.zip, Tup.levels] at hv; cases mem_cons_top hlt hv
            exact ⟨_, List.mem_cons_of_mem _ hm, by simp⟩
    | _ => simp [recordDef] at hd
  | and t =>
    cases t with
    | bits n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      have hn : n ≤ 64 := Decidable.byContradiction fun hne => by
        have hbf : Nat.ble n 64 = false := Bool.eq_false_iff.mpr (by simpa [Nat.ble_eq] using hne)
        cases a <;> cases b <;> simp [recordDef, hbf] at hd
      have hbt : Nat.ble n 64 = true := Nat.ble_eq.mpr hn
      rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
      cases a with
      | var x =>
        cases b with
        | var y =>
          simp only [recordDef, hbt, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Option.some.injEq] at hd
          subst hd; cases h1 with | var hmx => cases h2 with | var hmy =>
          simp only [OpCode.wp_and, vals, Arg.val, lift2, Tup.zip, Tup.levels] at hwp ⊢
          refine ⟨hwp, by simp, hn, fun v hv => ?_⟩
          cases mem_cons_top hlt hv
          exact ⟨_, _, List.mem_cons_of_mem _ hmx, List.mem_cons_of_mem _ hmy, rfl⟩
        | imm c =>
          simp only [recordDef, hbt, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Option.some.injEq] at hd
          subst hd; cases h1 with | var hmx => cases h2 with | imm =>
          simp only [OpCode.wp_and, vals, Arg.val, lift2, Tup.zip, Tup.levels] at hwp ⊢
          refine ⟨hwp, by simp, hn, fun v hv => ?_⟩
          cases mem_cons_top hlt hv
          exact ⟨_, List.mem_cons_of_mem _ hmx, by
            rw [BitVec.setWidth_setWidth_of_le c hn, BitVec.setWidth_eq]⟩
      | imm c =>
        cases b with
        | var y =>
          simp only [recordDef, hbt, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Option.some.injEq] at hd
          subst hd; cases h1 with | imm => cases h2 with | var hmy =>
          simp only [OpCode.wp_and, vals, Arg.val, lift2, Tup.zip, Tup.levels] at hwp ⊢
          refine ⟨hwp, by simp, hn, fun v hv => ?_⟩
          cases mem_cons_top hlt hv
          exact ⟨_, List.mem_cons_of_mem _ hmy, by
            rw [BitVec.setWidth_setWidth_of_le c hn, BitVec.setWidth_eq, BitVec.and_comm]⟩
        | imm _ => simp [recordDef, hbt] at hd
    | _ => simp [recordDef] at hd
  | sext m n =>
    rcases args with ⟨a, ⟨⟩⟩
    cases a with
    | imm _ => simp [recordDef] at hd
    | var x =>
      simp only [recordDef] at hd
      split at hd
      · rename_i hc
        simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
        cases hd
        rcases hrel with _ | ⟨h1, -⟩
        cases h1 with | var hmx =>
        simp only [OpCode.wp_sext, vals, Arg.val, Tup.zip, Tup.levels] at hwp ⊢
        refine ⟨hwp.1, hwp.2, by simp, hc.1.1, hc.1.2, hc.2, fun v hv => ?_⟩
        cases mem_cons_top hlt hv
        exact ⟨_, List.mem_cons_of_mem _ hmx, rfl⟩
      · cases hd
  | zext m n =>
    rcases args with ⟨a, ⟨⟩⟩
    cases a with
    | imm _ => simp [recordDef] at hd
    | var x =>
      simp only [recordDef] at hd
      split at hd
      · rename_i hc
        simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
        cases hd
        rcases hrel with _ | ⟨h1, -⟩
        cases h1 with | var hmx =>
        simp only [OpCode.wp_zext, vals, Arg.val, Tup.zip, Tup.levels] at hwp ⊢
        refine ⟨hwp.1, hwp.2, by simp, hc.1.1, hc.1.2, hc.2, fun v hv => ?_⟩
        cases mem_cons_top hlt hv
        exact ⟨_, List.mem_cons_of_mem _ hmx, rfl⟩
      · cases hd
  | _ => simp [recordDef] at hd

theorem recordDef_elide_ok {G : VCtx} {nv : Nat} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d)
    {sig rs : List Ty} {code : OpCode sig rs}
    {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    (hrel : TRel (ArgRel G) args₁ args) (hlt : ∀ p ∈ G, p.2.2 < nv) {P : Tup Val rs → Prop}
    (hwp : code.wp (vals args₁) P) {df : DefFact} (hd : recordDef defs code args = some df) :
    ∃ (w : Nat) (_h : rs = [.bits w]) (rvs : Tup Val rs), P rvs ∧
      DefOk (Tup.zip rvs (Tup.levels rs nv) ++ G) nv df := by
  obtain ⟨w, hrs⟩ := recordDef_rs hd
  subst hrs
  have hwp' := wp_recordDef hdefs hrel hlt hwp hd
  cases code with
  | add _ =>
    simp only [OpCode.wp_add, Ty.hasFloat, Bool.false_eq_true, ite_false] at hwp'
    exact ⟨w, rfl, _, hwp'.1, hwp'.2.2⟩
  | sub _ =>
    simp only [OpCode.wp_sub, Ty.hasFloat, Bool.false_eq_true, ite_false] at hwp'
    exact ⟨w, rfl, _, hwp'.1, hwp'.2.2⟩
  | or _ =>
    simp only [OpCode.wp_or] at hwp'
    exact ⟨w, rfl, _, hwp'.1, hwp'.2.2⟩
  | xor _ =>
    simp only [OpCode.wp_xor] at hwp'
    exact ⟨w, rfl, _, hwp'.1, hwp'.2.2⟩
  | shl _ =>
    simp only [OpCode.wp_shl, Ty.hasFloat, Bool.false_eq_true, ite_false] at hwp'
    exact ⟨w, rfl, _, hwp'.1, hwp'.2.2⟩
  | copy _ =>
    simp only [OpCode.wp_copy] at hwp'
    exact ⟨w, rfl, _, hwp'.1, hwp'.2.2⟩
  | and _ =>
    simp only [OpCode.wp_and] at hwp'
    exact ⟨w, rfl, _, hwp'.1, hwp'.2.2⟩
  | sext _ _ =>
    simp only [OpCode.wp_sext] at hwp'
    exact ⟨w, rfl, _, hwp'.2.1, hwp'.2.2.2⟩
  | zext _ _ =>
    simp only [OpCode.wp_zext] at hwp'
    exact ⟨w, rfl, _, hwp'.2.1, hwp'.2.2.2⟩
  | _ => simp [recordDef] at hd

end Rega
end LeanQbe.T
