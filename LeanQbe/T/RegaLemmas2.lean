module

public import LeanQbe.T.RegaLemmas1
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.Logic.Bytes

/-!
# `RegaLemmas` Part 2: ABI Frame Code (`call`/`ret`/`exit`/entry), `FnPost`, and `Hyps`

* `FnPost`, `Hyps`: the function-level postcondition (exactly `Target.FnSpec`'s) and hypotheses.
* `ret_ok`, `exit_ok`, `call_ok`, `fn_entry_ok` (callee-save/restore, `canonAbi`, epilogue, and
  call soundness, typed via `AbiHolds`/`ArgsIn`/`RetsIn`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

open Std Std.ExtHashMap

section Ctx
variable (T : Target) (host : T.mach.Host) (hints : T.toIsa.Hints) (E : Ext) (Γ : Env)
  (s₀ : T.mach.MData) (ra : T.mach.Addr) (n nX : Nat) (Rf : Mem 64 → Prop) (bound : Sym → Nat)

/-- `Target.FnSpec`'s postcondition for the function entered with `s₀`, `ra`, bound `n`, frame `Rf`. -/
def FnPost {rs : List Ty} (Q : Post rs) (X : XPost) : T.mach.State → Prop := fun st =>
  (T.mach.pc st = ra ∧ ∃ (rets : Tup Val rs) (m' : Mem 64),
    Q rets m' ∧ T.RetsIn rets (T.mach.data st) ∧ T.Restored s₀ (T.mach.data st) ∧
    (T.mach.mem (T.mach.data st) =⋆ Eq m' ⋆ T.Exit (T.mach.getGpr s₀ T.frame.sp) n ⋆ Rf)) ∨
  (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64),
    X sym' cs xs m' ∧ T.Defined host sym' ∧ T.mach.pc st = T.mach.labelAddr host sym' ∧
    T.ArgsIn xs (T.mach.data st) ∧ T.frameSpec.spEntry (T.mach.getGpr (T.mach.data st) T.frame.sp) ∧
    ∃ (ra' : T.mach.Addr) (n' : Nat) (F : Mem 64 → Prop),
      nX ≤ n' ∧ n' + T.frame.raBytes ≤ 2 ^ 64 ∧ T.frameSpec.raReg (T.mach.data st) ra' ∧
      (T.mach.mem (T.mach.data st) =⋆
        Eq m' ⋆ T.Entry (T.mach.getGpr (T.mach.data st) T.frame.sp) ra' n' ⋆ F ⋆ Rf))

/-- What the function-level proof provides to the body. -/
structure Hyps : Prop where
  unique : T.LabelsUnique host
  spE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp)
  frame_le : effFrame T.toIsa hints E ≤ n
  frame_bound : effFrame T.toIsa hints E + T.frame.raBytes ≤ 2 ^ 64
  stack_bound : n + T.frame.raBytes ≤ 2 ^ 64
  saved_cs : ∀ r ∈ hints.saved, r ∈ T.frame.calleeSaved
  saved_nodup : hints.saved.Nodup
  callees : ∀ g as bs, (g, as, bs) ∈ E.callees →
    T.FnSpec host g (Γ g as bs) (bound g) nX ∧
      effFrame T.toIsa hints E + T.frame.raBytes + bound g ≤ n
  exits : ∀ g, g ∈ E.exits → T.Defined host g ∧ nX ≤ n

end Ctx

/-! ## Helpers: memory -/

section MemH

private theorem toBytes_ofInt_ofBytes {bs : List UInt8} (hl : bs.length = 8) :
    Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes bs)).toInt = bs := by
  rw [← Int.toBytes_emod]
  have h1 : ((BitVec.ofInt 64 (Int.ofBytes bs)).toInt).take (8 * 8) =
      (Int.ofBytes bs).take (8 * 8) := by
    grind
  rw [h1, Int.toBytes_emod, ← hl]
  exact Int.toBytes_ofBytes_all bs

private theorem eight_eq : (8 : BitVec 64) = BitVec.ofNat 64 8 := rfl

private theorem add_ofNat_8 (x : BitVec 64) (i : Nat) :
    x + BitVec.ofNat 64 (8 * i) + 8 = x + BitVec.ofNat 64 (8 * (i + 1)) := by
  rw [BitVec.add_assoc, eight_eq, ← BitVec.ofNat_add, Nat.mul_succ]

private theorem array64_region : ∀ {a : BitVec 64} {xs : List (BitVec 64)} {f : Mem 64},
    8 * xs.length ≤ 2 ^ 64 → array64 a xs f → region a (8 * xs.length) f
  | _, [], _, _, h => by rw [List.length_nil, Nat.mul_zero, region_zero]; exact h
  | a, x :: xs, f, hl, h => by
    simp only [List.length_cons] at hl ⊢
    rw [Nat.mul_succ, Nat.add_comm, region_split (by omega)]
    rw [array64_cons, eight_eq] at h
    exact sep_mono (fun _ hc => ⟨_, Int.toBytes_length 8 _, hc.symm⟩)
      (sep_mono_r (fun _ => array64_region (by omega)) h)

private theorem region_cell64 {a : BitVec 64} {f : Mem 64} (h : region a 8 f) :
    ∃ v, cell64 a v f := by
  obtain ⟨bs, hl, rfl⟩ := h
  exact ⟨BitVec.ofInt 64 (Int.ofBytes bs), by
    show (Int.toBytes 8 _).At a = _
    rw [toBytes_ofInt_ofBytes hl]⟩

private theorem region_array64 : ∀ (k : Nat) {a : BitVec 64} {f : Mem 64},
    8 * k ≤ 2 ^ 64 → region a (8 * k) f → ∃ xs : List (BitVec 64), xs.length = k ∧ array64 a xs f
  | 0, _, _, _, h => ⟨[], rfl, by rw [Nat.mul_zero, region_zero] at h; exact h⟩
  | k + 1, a, f, hk, h => by
    rw [Nat.mul_succ, Nat.add_comm, region_split (by omega)] at h
    have h' := sep_mono_r (Q' := fun g => ∃ xs : List (BitVec 64), xs.length = k ∧
        array64 (a + BitVec.ofNat 64 8) xs g)
      (fun g hg => region_array64 k (by omega) hg)
      (sep_mono (P' := fun g => ∃ v, cell64 a v g) (fun _ hg => region_cell64 hg) h)
    obtain ⟨v, h'⟩ := sep_ex_l.mp h'
    obtain ⟨xs, h'⟩ := sep_ex_r.mp h'
    obtain ⟨hl, h'⟩ := sep_pure_r.mp h'
    refine ⟨v :: xs, by simp [hl], ?_⟩
    rw [array64_cons, eight_eq]
    exact h'

private theorem region_array64_sep {k : Nat} {a : BitVec 64} {G : Mem 64 → Prop} {M : Mem 64}
    (hk : 8 * k ≤ 2 ^ 64) (h : (region a (8 * k) ⋆ G) M) :
    ∃ xs : List (BitVec 64), xs.length = k ∧ (array64 a xs ⋆ G) M := by
  have h' := sep_ex_l.mp (sep_mono (fun _ hg => region_array64 k hk hg) h)
  obtain ⟨xs, h'⟩ := h'
  rw [sep_pure_l] at h'
  exact ⟨xs, h'⟩

variable {T : Target} {hints : T.toIsa.Hints} {s₀ : T.mach.MData}

private theorem sub_add_sub {x : BitVec 64} {n f : Nat} (h : f ≤ n) :
    x - BitVec.ofNat 64 n + BitVec.ofNat 64 (n - f) = x - BitVec.ofNat 64 f := by
  bv_omega

private theorem slots_split (hb : 8 * hints.totalSlots ≤ 2 ^ 64) :
    region (base T hints s₀) (8 * hints.totalSlots) =
      (region (base T hints s₀) (8 * hints.nslots) ⋆
        region (base T hints s₀ + BitVec.ofNat 64 (8 * hints.nslots))
          (8 * hints.saved.length)) := by
  have e : 8 * hints.totalSlots = 8 * hints.nslots + 8 * hints.saved.length := by
    simp [Hints.totalSlots, Nat.mul_add]
  rw [e, region_split (by omega)]

private theorem pad_split (h8 : 8 * hints.totalSlots ≤ frame T hints)
    (hF : frame T hints ≤ 2 ^ 64) :
    region (base T hints s₀) (frame T hints) =
      (region (base T hints s₀) (8 * hints.totalSlots) ⋆
        region (base T hints s₀ + BitVec.ofNat 64 (8 * hints.totalSlots))
          (frame T hints - 8 * hints.totalSlots)) := by
  have := region_split (a := base T hints s₀) (n1 := 8 * hints.totalSlots)
    (n2 := frame T hints - 8 * hints.totalSlots) (by omega)
  rwa [Nat.add_sub_cancel' h8] at this

private theorem below_split {n : Nat} (hFn : frame T hints ≤ n) (hn : n ≤ 2 ^ 64) :
    region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n) n =
      (region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n) (n - frame T hints) ⋆
        region (base T hints s₀) (frame T hints)) := by
  have := region_split (a := T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n)
    (n1 := n - frame T hints) (n2 := frame T hints) (by omega)
  rwa [Nat.sub_add_cancel hFn, sub_add_sub hFn] at this

private theorem callee_split' {n b : Nat} (hb : frame T hints + T.frame.raBytes + b ≤ n)
    (hn : n ≤ 2 ^ 64) :
    region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n) (n - frame T hints) =
      (region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n)
          (n - frame T hints - (b + T.frame.raBytes)) ⋆
        region (base T hints s₀ - BitVec.ofNat 64 T.frame.raBytes - BitVec.ofNat 64 b)
          (b + T.frame.raBytes)) := by
  have h1 := region_split (a := T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n)
    (n1 := n - frame T hints - (b + T.frame.raBytes)) (n2 := b + T.frame.raBytes) (by omega)
  have e : T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n +
      BitVec.ofNat 64 (n - frame T hints - (b + T.frame.raBytes)) =
      base T hints s₀ - BitVec.ofNat 64 T.frame.raBytes - BitVec.ofNat 64 b := by
    rw [Nat.sub_sub, sub_add_sub (by omega), BitVec.ofNat_add, BitVec.ofNat_add]
    simp only [base]; grind
  rwa [Nat.sub_add_cancel (by omega), e] at h1

private theorem callee_split {n b : Nat} (hb : frame T hints + T.frame.raBytes + b ≤ n)
    (hn : n ≤ 2 ^ 64) :
    region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n) (n - frame T hints) =
      (region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n)
          (n - frame T hints - (b + T.frame.raBytes)) ⋆
        (region (base T hints s₀ - BitVec.ofNat 64 T.frame.raBytes - BitVec.ofNat 64 b) b ⋆
          region (base T hints s₀ - BitVec.ofNat 64 T.frame.raBytes) T.frame.raBytes)) := by
  have h2 := region_split (a := base T hints s₀ - BitVec.ofNat 64 T.frame.raBytes -
    BitVec.ofNat 64 b) (n1 := b) (n2 := T.frame.raBytes) (by omega)
  rw [BitVec.sub_add_cancel] at h2
  rw [callee_split' hb hn, h2]

private theorem entry_exit {sp : BitVec 64} {ra : T.mach.Addr} {n : Nat}
    (hn : n + T.frame.raBytes ≤ 2 ^ 64) {f : Mem 64} (h : T.Entry sp ra n f) : T.Exit sp n f := by
  unfold Target.Entry at h
  unfold Target.Exit
  rw [region_split hn, BitVec.sub_add_cancel]
  exact sep_mono_r (fun _ h => T.frameSpec.retAddr_region _ _ _ h) h

private theorem slots_region {σ : List (BitVec 64)} (hσ : σ.length = hints.nslots)
    (hb : 8 * hints.totalSlots ≤ 2 ^ 64) {f : Mem 64}
    (h : (array64 (base T hints s₀) σ ⋆ csSlots T hints s₀) f) :
    region (base T hints s₀) (8 * hints.totalSlots) f := by
  have hl : hints.totalSlots = hints.nslots + hints.saved.length := rfl
  rw [slots_split hb]
  refine sep_mono (fun _ h => ?_) (sep_mono_r (fun _ h => ?_) h)
  · rw [← hσ]; exact array64_region (by omega) h
  · have := array64_region (by simp; omega) h
    simpa using this

end MemH

/-! ## Helpers: register-class disjointness -/

section RegH
variable {T : Target}

private abbrev IsAbi (T : Target) (r : T.Reg) : Prop := r ∈ T.frame.argRegs ∨ r ∈ T.frame.retRegs

private theorem IsAbi.not_scratch {r : T.Reg} (h : IsAbi T r) : r ∉ T.frame.scratch := fun hs => by
  have := T.frameSpec.scratch_disj r hs; rcases h with h | h <;> simp_all

private theorem IsAbi.not_cs {r : T.Reg} (h : IsAbi T r) : r ∉ T.frame.calleeSaved := fun hs => by
  have := T.frameSpec.cs_disj r hs; rcases h with h | h <;> simp_all

private theorem IsAbi.not_ra {r : T.Reg} (h : IsAbi T r) : r ∉ T.frame.raRegs := fun hs => by
  have := T.frameSpec.ra_disj r hs; rcases h with h | h <;> simp_all

private theorem IsAbi.ne_sp {r : T.Reg} (h : IsAbi T r) : r ≠ T.frame.sp := fun e => by
  have := T.frameSpec.sp_disj; subst e; rcases h with h | h <;> simp_all

private theorem cs_not_scratch {r : T.Reg} (h : r ∈ T.frame.calleeSaved) :
    r ∉ T.frame.scratch := fun hs => (T.frameSpec.scratch_disj r hs).2.1 h

private theorem cs_not_ra {r : T.Reg} (h : r ∈ T.frame.calleeSaved) :
    r ∉ T.frame.raRegs := fun hs => (T.frameSpec.ra_disj r hs).2.2.1 h

private theorem cs_ne_sp {r : T.Reg} (h : r ∈ T.frame.calleeSaved) : r ≠ T.frame.sp := fun e =>
  T.frameSpec.sp_disj.2.2.1 (e ▸ h)

private theorem isMoveGpr_abi {saved : List T.Reg} {r : T.Reg}
    (h : isMoveGpr T.toIsa saved r = false) : ¬IsAbi T r ∧ r ∉ T.frame.scratch := by
  simp only [isMoveGpr, isAllocGpr, Bool.or_eq_false_iff, List.contains_eq_mem,
    decide_eq_false_iff_not] at h
  exact ⟨fun h' => by rcases h' with h' | h' <;> simp_all, h.2⟩

private theorem cs_of_isMoveGpr {saved : List T.Reg} {r : T.Reg}
    (h : isMoveGpr T.toIsa saved r = false) : r ∉ saved := by
  simp only [isMoveGpr, isAllocGpr, Bool.or_eq_false_iff, List.contains_eq_mem,
    decide_eq_false_iff_not] at h
  exact h.1.1.1.2

end RegH

/-! ## Helpers: ABI register tuples and `canonAbiCode` -/

section AbiH

/-- An ABI value before canonicalization (a `GprHolds`/`VecHolds` fact). -/
def PreHolds {R V C D : Type} (M : Machine R V C D) (s : M.MData) :
    (t : Ty) → AbiReg R V t → Val t → Prop
  | t, .gpr r, v => GprHolds (M.getGpr s r) t v
  | t, .vec vr, v => VecHolds (M.getVec s vr) t v

/-- The GPRs of an ABI register tuple. -/
def abiGprs {R V : Type} : {ts : List Ty} → Tup (AbiReg R V) ts → List R
  | [], () => []
  | _ :: _, (.gpr r, ls) => r :: abiGprs ls
  | _ :: _, (.vec _, ls) => abiGprs ls

private theorem trel_keep {R V C D : Type} {M : Machine R V C D}
    {P : M.MData → (t : Ty) → AbiReg R V t → Val t → Prop}
    (hP : ∀ s s' t (l : AbiReg R V t) v, (∀ r, l = .gpr r → M.getGpr s' r = M.getGpr s r) →
      (∀ vr, M.getVec s' vr = M.getVec s vr) → P s t l v → P s' t l v)
    {s s' : M.MData} {ts : List Ty} {ls : Tup (AbiReg R V) ts} {xs : Tup Val ts}
    (hg : ∀ r ∈ abiGprs ls, M.getGpr s' r = M.getGpr s r)
    (hv : ∀ vr, M.getVec s' vr = M.getVec s vr) (h : TRel (P s) ls xs) : TRel (P s') ls xs := by
  induction h with
  | nil => exact .nil
  | @cons t ts l x ls xs h1 _ ih =>
    have hsub : ∀ r ∈ abiGprs ls, r ∈ abiGprs (ts := t :: ts) (l, ls) := by
      intro r hr; cases l <;> simp [abiGprs, hr]
    exact .cons (hP _ _ _ _ _ (fun r e => hg r (by subst e; simp [abiGprs])) hv h1)
      (ih fun r hr => hg r (hsub r hr))

private theorem preHolds_keep {R V C D : Type} {M : Machine R V C D} (s s' : M.MData) (t : Ty)
    (l : AbiReg R V t) (v : Val t) (hg : ∀ r, l = .gpr r → M.getGpr s' r = M.getGpr s r)
    (hv : ∀ vr, M.getVec s' vr = M.getVec s vr) (h : PreHolds M s t l v) : PreHolds M s' t l v := by
  cases l with
  | gpr r => simp only [PreHolds] at h ⊢; rwa [hg r rfl]
  | vec vr => simp only [PreHolds] at h ⊢; rwa [hv vr]

private theorem abiHolds_keep {R V C D : Type} {M : Machine R V C D} (s s' : M.MData) (t : Ty)
    (l : AbiReg R V t) (v : Val t) (hg : ∀ r, l = .gpr r → M.getGpr s' r = M.getGpr s r)
    (hv : ∀ vr, M.getVec s' vr = M.getVec s vr) (h : M.AbiHolds s t l v) : M.AbiHolds s' t l v := by
  cases l with
  | gpr r => simp only [Machine.AbiHolds] at h ⊢; rwa [hg r rfl]
  | vec vr => simp only [Machine.AbiHolds] at h ⊢; rwa [hv vr]

private theorem assignSig_gpr {I : Isa} {t : Ty} {ts : List Ty} {gs : List I.Reg}
    {vs : List I.VReg} {r : I.Reg} {ls : Tup (AbiReg I.Reg I.VReg) ts}
    (h : I.assignSig (t :: ts) gs vs = some (.gpr r, ls)) :
    ∃ gs', gs = r :: gs' ∧ I.assignSig ts gs' vs = some ls ∧
      (t = .bool ∨ ∃ n ∈ I.frame.bitWidths, t = .bits n) := by
  cases t <;> cases gs <;> cases vs <;> simp [Isa.assignSig] at h ⊢ <;> grind

private theorem assignSig_vec {I : Isa} {t : Ty} {ts : List Ty} {gs : List I.Reg}
    {vs : List I.VReg} {v : I.VReg} {ls : Tup (AbiReg I.Reg I.VReg) ts}
    (h : I.assignSig (t :: ts) gs vs = some (.vec v, ls)) :
    ∃ vs', vs = v :: vs' ∧ I.assignSig ts gs vs' = some ls := by
  cases t <;> cases gs <;> cases vs <;> simp [Isa.assignSig] at h ⊢ <;> grind

private theorem abiGprs_sub {I : Isa} : ∀ {ts : List Ty} {gs : List I.Reg} {vs : List I.VReg}
    {ls : Tup (AbiReg I.Reg I.VReg) ts}, I.assignSig ts gs vs = some ls → ∀ r ∈ abiGprs ls, r ∈ gs
  | [], _, _, (), _, r, hr => by simp [abiGprs] at hr
  | _ :: _, _, _, (.gpr q, ls), h, r, hr => by
    obtain ⟨gs', rfl, h', _⟩ := assignSig_gpr h
    simp only [abiGprs, List.mem_cons] at hr ⊢
    exact hr.imp_right (abiGprs_sub h' r)
  | _ :: _, _, _, (.vec _, ls), h, r, hr => by
    obtain ⟨vs', rfl, h'⟩ := assignSig_vec h
    exact abiGprs_sub h' r hr

variable {T : Target} {host : T.mach.Host}

private theorem pre_of_targets {G : VCtx} {s : T.mach.MData} {σ : List (BitVec 64)} :
    ∀ {ts : List Ty} {args₁ : Tup (Arg Val) ts} {args : Tup (Arg VNat) ts}
      {locs : Tup (AbiReg T.Reg T.VReg) ts} {tgts : List (SymArg × T.toIsa.Loc)},
    TRel (ArgRel G) args₁ args → abiTargets T.toIsa args locs = some tgts →
    (∀ p ∈ tgts, LocOk T.mach G s σ p.1 p.2) → TRel (PreHolds T.mach s) locs (vals args₁)
  | [], (), (), (), _, _, _, _ => .nil
  | t :: ts, (a₁, as₁), (a, as), (l, ls), tgts, hrel, htg, hok => by
    cases hrel with
    | cons h1 h2 =>
      cases hsa : toSymArg T.toIsa t a with
      | none => simp [abiTargets, hsa] at htg
      | some sa =>
        cases hr : abiTargets T.toIsa as ls with
        | none => simp [abiTargets, hsa, hr] at htg
        | some rest =>
          simp only [abiTargets, hsa, hr, Option.some.injEq] at htg
          subst htg
          refine .cons ?_ (pre_of_targets h2 hr fun p hp => hok p (List.mem_cons_of_mem _ hp))
          have hv := locVal_of_locOk h1 hsa (hok _ List.mem_cons_self)
          cases l <;> exact hv

/-- Skipped canonicalization: GPR positions flagged in `sk` already satisfy `AbiHolds`. -/
def SkipOk {R V C D : Type} (M : Machine R V C D) (s : M.MData) :
    {ts : List Ty} → Tup (AbiReg R V) ts → Tup Val ts → List Bool → Prop
  | [], (), (), _ => True
  | t :: _, (l, ls), (x, xs), sk =>
    (sk.headD false = true → M.AbiHolds s t l x) ∧ SkipOk M s ls xs sk.tail

private theorem skipOk_keep {R V C D : Type} {M : Machine R V C D} {s s' : M.MData} :
    ∀ {ts : List Ty} {ls : Tup (AbiReg R V) ts} {xs : Tup Val ts} {sk : List Bool},
    (∀ r ∈ abiGprs ls, M.getGpr s' r = M.getGpr s r) → (∀ vr, M.getVec s' vr = M.getVec s vr) →
    SkipOk M s ls xs sk → SkipOk M s' ls xs sk
  | [], (), (), _, _, _, _ => trivial
  | t :: ts, (l, ls), (_, _), _, hg, hv, ⟨h1, h2⟩ => by
    have hsub : ∀ r ∈ abiGprs ls, r ∈ abiGprs (ts := t :: ts) (l, ls) := by
      intro r hr; cases l <;> simp [abiGprs, hr]
    exact ⟨fun hs => abiHolds_keep _ _ _ _ _ (fun r e => hg r (by subst e; simp [abiGprs])) hv
      (h1 hs), skipOk_keep (fun r hr => hg r (hsub r hr)) hv h2⟩

private theorem canon_ok {post : T.mach.State → Prop} :
    ∀ {ts : List Ty} {gs : List T.Reg} {vs : List T.VReg}
      {locs : Tup (AbiReg T.Reg T.VReg) ts} {xs : Tup Val ts} {sk : List Bool} {k : Nat}
      {s : T.mach.MData},
    T.toIsa.assignSig ts gs vs = some locs → gs.Nodup → (∀ r ∈ gs, r ∉ T.frame.scratch) →
    TRel (PreHolds T.mach s) locs xs → SkipOk T.mach s locs xs sk →
    (canonAbiCode T.toIsa locs sk).IsInfixAt (T.mach.prog host) k →
    (∀ s', TRel (T.mach.AbiHolds s') locs xs → T.mach.KeepsGpr s s' (gs ++ T.frame.scratch) →
      (∀ v, T.mach.getVec s' v = T.mach.getVec s v) → T.mach.mem s' = T.mach.mem s →
      T.mach.Run host (k + (canonAbiCode T.toIsa locs sk).length) s' post) →
    T.mach.Run host k s post
  | [], _, _, (), (), _, k, s, _, _, _, _, _, _, kont => by
    simpa [canonAbiCode] using kont s .nil (fun _ _ => rfl) (fun _ => rfl) rfl
  | t :: ts, gs, vs, (l, ls), (x, xs), sk, k, s, ha, hnd, hns, hpre, hsk, hc, kont => by
    obtain ⟨hs1, hs2⟩ := hsk
    cases hpre with
    | cons h1 h2 =>
    cases l with
    | gpr r =>
      obtain ⟨gs', rfl, ha', hty⟩ := assignSig_gpr ha
      obtain ⟨hrn, hnd'⟩ := List.nodup_cons.mp hnd
      have hns' : ∀ q ∈ gs', q ∉ T.frame.scratch := fun q hq => hns q (List.mem_cons_of_mem _ hq)
      have hr2 : ∀ s1 s2 : T.mach.MData, T.mach.KeepsGpr s1 s2 (gs' ++ T.frame.scratch) →
          T.mach.getGpr s2 r = T.mach.getGpr s1 r := fun _ _ hk2 =>
        hk2 r (by simp only [List.mem_append, not_or]; exact ⟨hrn, hns r List.mem_cons_self⟩)
      by_cases hsk0 : sk.headD false = true
      · have hc' : (canonAbiCode T.toIsa ls sk.tail).IsInfixAt (T.mach.prog host) k := by
          simpa only [canonAbiCode, hsk0, ↓reduceIte, List.nil_append] using hc
        refine canon_ok ha' hnd' hns' h2 hs2 hc' fun s2 htr hk2 hv2 hm2 => ?_
        have := kont s2 (.cons (show AbiGprHolds _ _ _ from (hr2 s s2 hk2) ▸ hs1 hsk0) htr)
          (fun q hq => by
            simp only [List.mem_append, List.mem_cons, not_or] at hq
            exact hk2 q (by simp only [List.mem_append, not_or]; exact ⟨hq.1.2, hq.2⟩))
          hv2 hm2
        simpa only [canonAbiCode, hsk0, ↓reduceIte, List.nil_append] using this
      · have hc' : ((T.frame.canonAbi t r).1 ++ canonAbiCode T.toIsa ls sk.tail).IsInfixAt
            (T.mach.prog host) k := by
          simpa only [canonAbiCode, hsk0, Bool.false_eq_true, ↓reduceIte] using hc
        refine T.frameSpec.canonAbi_spec hty (hns r List.mem_cons_self) h1 hc'.append.1
          fun s1 hq1 hfr1 => ?_
        have hk1 := hfr1.1
        have hv1 := hfr1.2.1
        have hkeep : ∀ q ∈ abiGprs ls, T.mach.getGpr s1 q = T.mach.getGpr s q := fun q hq => by
          have hq' := abiGprs_sub ha' q hq
          exact hk1 q (by simp only [List.mem_cons, not_or]; exact ⟨fun e => hrn (e ▸ hq'),
            hns' q hq'⟩)
        refine canon_ok ha' hnd' hns' (trel_keep preHolds_keep hkeep
          (fun v => hv1 v List.not_mem_nil) h2) (skipOk_keep hkeep (fun v => hv1 v List.not_mem_nil)
          hs2) hc'.append.2 fun s2 htr hk2 hv2 hm2 => ?_
        have := kont s2 (.cons (show AbiGprHolds _ _ _ from (hr2 s1 s2 hk2) ▸ hq1.1) htr)
          (fun q hq => by
            simp only [List.mem_append, List.mem_cons, not_or] at hq
            rw [hk2 q (by simp only [List.mem_append, not_or]; exact ⟨hq.1.2, hq.2⟩),
              hk1 q (by simp only [List.mem_cons, not_or]; exact ⟨hq.1.1, hq.2⟩)])
          (fun v => (hv2 v).trans (hv1 v List.not_mem_nil)) (hm2.trans hq1.2)
        simpa only [canonAbiCode, hsk0, Bool.false_eq_true, ↓reduceIte, List.length_append,
          Nat.add_assoc] using this
    | vec v =>
      obtain ⟨vs', rfl, ha'⟩ := assignSig_vec ha
      exact canon_ok ha' hnd hns h2 hs2 hc fun s2 htr hk2 hv2 hm2 =>
        kont s2 (.cons (show VecHolds _ _ _ by rw [hv2 v]; exact h1) htr) hk2 hv2 hm2

/-- `abiHeld` soundness: the register already holds the canonical ABI value. -/
theorem abiHeld_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {t : Ty} {a₁ : Arg Val t}
    {a : Arg VNat t} (hrel : ArgRel G t a₁ a) {sa : SymArg} (hsa : toSymArg T.toIsa t a = some sa)
    {r : T.Reg} (hh : abiHeld T.toIsa st.regs st.zeroExt32 t r sa = true) :
    AbiGprHolds (T.mach.getGpr s r) t a₁.val := by
  have gsym : ∀ {sa' : SymArg} {rl : RegLoc T.Reg T.VReg T.Cond}, (sa', rl) ∈ st.regs →
      regLocMatchesGpr rl r = true → GprSym G (T.mach.getGpr s r) sa' := by
    intro sa' rl hm h
    have h0 := hA.regs _ hm
    cases rl with
    | gpr r' => simp only [regLocMatchesGpr, beq_iff_eq] at h; subst h; exact h0
    | gprZ r' => simp only [regLocMatchesGpr, beq_iff_eq] at h; subst h; exact h0.1
    | _ => simp [regLocMatchesGpr] at h
  cases hrel with
  | var hm =>
    simp only [toSymArg, Option.some.injEq] at hsa; subst hsa
    simp only [abiHeld, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · simp only [Bool.and_eq_true] at hh
      obtain ⟨⟨ht32, hzer⟩, hhas⟩ := hh
      have ht32' : t = .bits 32 := tyEq_iff.mp ht32
      subst ht32'
      simp only [hasVarGpr, List.any_eq_true, Bool.and_eq_true] at hhas
      obtain ⟨⟨sa', rl⟩, hmem, he1, he2⟩ := hhas
      obtain rfl := symArgEq_iff.mp he1
      have hgs : GprHolds (T.mach.getGpr s r) (.bits 32) _ := gsym hmem he2 _ _ hm
      have hzk := hA.zeroExt32_ok r (List.contains_iff_mem.mp hzer)
      exact ⟨by decide, by rw [hzk, hgs.2]; rfl⟩
    · simp only [List.any_eq_true, Bool.and_eq_true] at hh
      obtain ⟨⟨sa', rl⟩, hmem, he1, he2⟩ := hh
      obtain rfl := symArgEq_iff.mp he1
      cases rl with
      | gprZ r' =>
        simp only [regLocEq, beq_iff_eq] at he2; subst he2
        exact (hA.regs _ hmem).2 _ _ hm
      | _ => simp [regLocEq] at he2
  | imm c =>
    cases t with
    | bool =>
      simp only [toSymArg, Option.some.injEq] at hsa; subst hsa
      simp only [abiHeld, List.any_eq_true, Bool.and_eq_true] at hh
      obtain ⟨⟨sa', rl⟩, hmem, he1, he2⟩ := hh
      obtain rfl := symArgEq_iff.mp he1
      obtain ⟨-, hw⟩ := gsym hmem he2
      rw [BitVec.setWidth_eq, BitVec.setWidth_eq] at hw
      show T.mach.getGpr s r = BitVec.ofNat 64 c.toNat
      rw [hw]; cases c <;> rfl
    | bits n =>
      simp only [toSymArg] at hsa; split at hsa
      · rename_i hn
        simp only [Option.some.injEq] at hsa; subst hsa
        simp only [abiHeld, List.any_eq_true, Bool.and_eq_true] at hh
        obtain ⟨⟨sa', rl⟩, hmem, he1, he2⟩ := hh
        obtain rfl := symArgEq_iff.mp he1
        obtain ⟨-, hw⟩ := gsym hmem he2
        rw [BitVec.setWidth_eq, BitVec.setWidth_eq] at hw
        exact ⟨by simpa using hn, hw⟩
      · simp at hsa
    | pair _ _ =>
      simp only [toSymArg, Option.map_eq_some_iff] at hsa
      obtain ⟨_, _, rfl⟩ := hsa
      simp [abiHeld] at hh
    | float _ => simp [toSymArg] at hsa

theorem skipOk_of_abiSkips {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) :
    ∀ {ts : List Ty} {args₁ : Tup (Arg Val) ts} {args : Tup (Arg VNat) ts}
      {locs : Tup (AbiReg T.Reg T.VReg) ts}, TRel (ArgRel G) args₁ args →
    SkipOk T.mach s locs (vals args₁) (abiSkips T.toIsa st.regs st.zeroExt32 args locs)
  | [], (), (), (), _ => trivial
  | t :: _, (_, _), (a, _), (l, _), .cons h1 h2 => by
    refine ⟨fun hsk => ?_, skipOk_of_abiSkips hA h2⟩
    simp only [abiSkips, List.headD_cons] at hsk
    split at hsk
    · rename_i r sa hsa
      exact abiHeld_ok hA h1 hsa hsk
    · simp at hsk

/-! ## Helpers: `saveCs`/`restoreCs` -/

private theorem saveCsList_ok {post : T.mach.State → Prop} :
    ∀ (i : Nat) (rs : List T.Reg) (k : Nat) (s : T.mach.MData) (G : Mem 64 → Prop),
    (saveCsList T.toIsa i rs).IsInfixAt (T.mach.prog host) k →
    T.frameSpec.spOk (T.mach.getGpr s T.frame.sp) → 8 * i + 8 * rs.length ≤ 2 ^ 64 →
    (∀ r ∈ rs, r ∉ T.frame.scratch) →
    (T.mach.mem s =⋆
      region (T.mach.getGpr s T.frame.sp + BitVec.ofNat 64 (8 * i)) (8 * rs.length) ⋆ G) →
    (∀ s', T.mach.KeepsGpr s s' T.frame.scratch → (∀ v, T.mach.getVec s' v = T.mach.getVec s v) →
      (T.mach.mem s' =⋆ array64 (T.mach.getGpr s T.frame.sp + BitVec.ofNat 64 (8 * i))
        (rs.map (T.mach.getGpr s)) ⋆ G) →
      T.mach.Run host (k + (saveCsList T.toIsa i rs).length) s' post) →
    T.mach.Run host k s post
  | _, [], k, s, G, _, _, _, _, hmem, kont => by
    simp only [List.length_nil, Nat.mul_zero, region_zero, emp_sep] at hmem
    simpa [saveCsList] using
      kont s (fun _ _ => rfl) (fun _ => rfl) (by simpa [emp_sep] using hmem)
  | i, r :: rs, k, s, G, hc, hsp, hlen, hns, hmem, kont => by
    have hc' : (T.frame.slotSt i r ++ saveCsList T.toIsa (i + 1) rs).IsInfixAt
        (T.mach.prog host) k := hc
    have hmem1 : T.mach.mem s =⋆
        region (T.mach.getGpr s T.frame.sp + BitVec.ofNat 64 (8 * i)) 8 ⋆
        (region (T.mach.getGpr s T.frame.sp + BitVec.ofNat 64 (8 * (i + 1))) (8 * rs.length) ⋆
          G) := by
      have e : 8 * (r :: rs).length = 8 + 8 * rs.length := by simp; omega
      rw [e, region_split (by simp at hlen; omega), ← eight_eq, add_ofNat_8] at hmem
      exact sep_cast hmem (by ac_rfl)
    refine T.frameSpec.slotSt_spec (hns r List.mem_cons_self) hsp hmem1 hc'.append.1
      fun s1 hm1 hfr1 => ?_
    have hsp1 : T.mach.getGpr s1 T.frame.sp = T.mach.getGpr s T.frame.sp :=
      hfr1.1 _ T.frameSpec.sp_disj.1
    refine saveCsList_ok (i + 1) rs _ s1
      (cell64 (T.mach.getGpr s T.frame.sp + BitVec.ofNat 64 (8 * i)) (T.mach.getGpr s r) ⋆ G)
      hc'.append.2 (hsp1 ▸ hsp)
      (by simp at hlen; omega) (fun q hq => hns q (List.mem_cons_of_mem _ hq))
      (by rw [hsp1]; exact sep_cast hm1 (by ac_rfl)) fun s' hk' hv' hm' => ?_
    have hmap : rs.map (T.mach.getGpr s1) = rs.map (T.mach.getGpr s) :=
      List.map_congr_left fun q hq => hfr1.1 q (hns q (List.mem_cons_of_mem _ hq))
    have := kont s' (fun q hq => (hk' q hq).trans (hfr1.1 q hq))
      (fun v => (hv' v).trans (hfr1.2.1 v List.not_mem_nil)) (by
        rw [hsp1, hmap] at hm'
        simp only [List.map_cons, array64_cons]
        rw [add_ofNat_8]
        exact sep_cast hm' (by ac_rfl))
    simpa [saveCsList, Nat.add_assoc] using this

private theorem saveCs_ok {post : T.mach.State → Prop}
    (i : Nat) (rs : List T.Reg) (k : Nat) (s : T.mach.MData) (G : Mem 64 → Prop)
    (hc : (saveCs T.toIsa i rs).IsInfixAt (T.mach.prog host) k)
    (hsp : T.frameSpec.spOk (T.mach.getGpr s T.frame.sp)) (hlen : 8 * i + 8 * rs.length ≤ 2 ^ 64)
    (hns : ∀ r ∈ rs, r ∉ T.frame.scratch)
    (hmem : T.mach.mem s =⋆
      region (T.mach.getGpr s T.frame.sp + BitVec.ofNat 64 (8 * i)) (8 * rs.length) ⋆ G)
    (kont : ∀ s', T.mach.KeepsGpr s s' T.frame.scratch →
      (∀ v, T.mach.getVec s' v = T.mach.getVec s v) →
      (T.mach.mem s' =⋆ array64 (T.mach.getGpr s T.frame.sp + BitVec.ofNat 64 (8 * i))
        (rs.map (T.mach.getGpr s)) ⋆ G) →
      T.mach.Run host (k + (saveCs T.toIsa i rs).length) s' post) :
    T.mach.Run host k s post := by
  cases rs with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, region_zero, emp_sep] at hmem
    simpa [saveCs] using kont s (fun _ _ => rfl) (fun _ => rfl) (by simpa [emp_sep] using hmem)
  | cons r rs' =>
    cases hfn : T.frame.saveRegs? with
    | none =>
      have hc' : (saveCsList T.toIsa i (r :: rs')).IsInfixAt (T.mach.prog host) k := by
        simpa [saveCs, hfn] using hc
      simpa [saveCs, hfn] using
        saveCsList_ok i (r :: rs') k s G hc' hsp hlen hns hmem (by simpa [saveCs, hfn] using kont)
    | some fn =>
      have hc' : (fn i (r :: rs')).IsInfixAt (T.mach.prog host) k := by
        simpa [saveCs, hfn] using hc
      refine T.frameSpec.saveRegs_spec hfn hlen hns hsp hmem hc' fun s' hm' hfr => ?_
      have := kont s' hfr.1 (fun v => hfr.2.1 v List.not_mem_nil) hm'
      simpa [saveCs, hfn] using this

private theorem restoreCsList_ok {post : T.mach.State → Prop} {s₀ : T.mach.MData} :
    ∀ (i : Nat) (rs : List T.Reg) (k : Nat) (s : T.mach.MData) (G : Mem 64 → Prop),
    (restoreCsList T.toIsa i rs).IsInfixAt (T.mach.prog host) k →
    T.frameSpec.spOk (T.mach.getGpr s T.frame.sp) → rs.Nodup →
    (∀ r ∈ rs, r ∈ T.frame.calleeSaved) →
    (T.mach.mem s =⋆ array64 (T.mach.getGpr s T.frame.sp + BitVec.ofNat 64 (8 * i))
      (rs.map (T.mach.getGpr s₀)) ⋆ G) →
    (∀ s', (∀ r ∈ rs, T.mach.getGpr s' r = T.mach.getGpr s₀ r) →
      T.mach.KeepsGpr s s' (rs ++ T.frame.scratch) →
      (∀ v, T.mach.getVec s' v = T.mach.getVec s v) → T.mach.mem s' = T.mach.mem s →
      T.mach.Run host (k + (restoreCsList T.toIsa i rs).length) s' post) →
    T.mach.Run host k s post
  | _, [], k, s, _, _, _, _, _, _, kont => by
    simpa [restoreCsList] using kont s (fun _ h => nomatch h) (fun _ _ => rfl) (fun _ => rfl) rfl
  | i, r :: rs, k, s, G, hc, hsp, hnd, hsub, hmem, kont => by
    have hc' : (T.frame.slotLd r i ++ restoreCsList T.toIsa (i + 1) rs).IsInfixAt
      (T.mach.prog host) k := hc
    obtain ⟨hrn, hnd'⟩ := List.nodup_cons.mp hnd
    have hrc := hsub r List.mem_cons_self
    have hmem1 : T.mach.mem s =⋆
        cell64 (T.mach.getGpr s T.frame.sp + BitVec.ofNat 64 (8 * i)) (T.mach.getGpr s₀ r) ⋆
        (array64 (T.mach.getGpr s T.frame.sp + BitVec.ofNat 64 (8 * (i + 1)))
          (rs.map (T.mach.getGpr s₀)) ⋆ G) := by
      simp only [List.map_cons, array64_cons, add_ofNat_8] at hmem
      exact sep_cast hmem (by ac_rfl)
    refine T.frameSpec.slotLd_spec (cs_not_scratch hrc) hsp hmem1 hc'.append.1
      fun s1 hq1 hfr1 => ?_
    have hsp1 : T.mach.getGpr s1 T.frame.sp = T.mach.getGpr s T.frame.sp :=
      hfr1.1 _ (by simp only [List.mem_cons, not_or]
                   exact ⟨fun e => cs_ne_sp hrc e.symm, T.frameSpec.sp_disj.1⟩)
    refine restoreCsList_ok (i + 1) rs _ s1
      (cell64 (T.mach.getGpr s T.frame.sp + BitVec.ofNat 64 (8 * i)) (T.mach.getGpr s₀ r) ⋆ G)
      hc'.append.2 (hsp1 ▸ hsp) hnd'
      (fun q hq => hsub q (List.mem_cons_of_mem _ hq))
      (by rw [hsp1, hq1.2]; exact sep_cast hmem1 (by ac_rfl)) fun s' hr' hk' hv' hm' => ?_
    have := kont s' (fun q hq => by
        rcases List.mem_cons.mp hq with rfl | hq
        · rw [hk' q (by simp only [List.mem_append, not_or]; exact ⟨hrn, cs_not_scratch hrc⟩)]
          exact hq1.1
        · exact hr' q hq)
      (fun q hq => by
        simp only [List.mem_append, List.mem_cons, not_or] at hq
        rw [hk' q (by simp only [List.mem_append, not_or]; exact ⟨hq.1.2, hq.2⟩),
          hfr1.1 q (by simp only [List.mem_cons, not_or]; exact ⟨hq.1.1, hq.2⟩)])
      (fun v => (hv' v).trans (hfr1.2.1 v List.not_mem_nil)) (hm'.trans hq1.2)
    simpa [restoreCsList, Nat.add_assoc] using this

private theorem restoreCs_ok {post : T.mach.State → Prop} {s₀ : T.mach.MData}
    (i : Nat) (rs : List T.Reg) (k : Nat) (s : T.mach.MData) (G : Mem 64 → Prop)
    (hc : (restoreCs T.toIsa i rs).IsInfixAt (T.mach.prog host) k)
    (hsp : T.frameSpec.spOk (T.mach.getGpr s T.frame.sp)) (hnd : rs.Nodup)
    (hsub : ∀ r ∈ rs, r ∈ T.frame.calleeSaved)
    (hmem : T.mach.mem s =⋆ array64 (T.mach.getGpr s T.frame.sp + BitVec.ofNat 64 (8 * i))
      (rs.map (T.mach.getGpr s₀)) ⋆ G)
    (kont : ∀ s', (∀ r ∈ rs, T.mach.getGpr s' r = T.mach.getGpr s₀ r) →
      T.mach.KeepsGpr s s' (rs ++ T.frame.scratch) →
      (∀ v, T.mach.getVec s' v = T.mach.getVec s v) → T.mach.mem s' = T.mach.mem s →
      T.mach.Run host (k + (restoreCs T.toIsa i rs).length) s' post) :
    T.mach.Run host k s post := by
  cases rs with
  | nil =>
    simpa [restoreCs] using kont s (fun _ h => nomatch h) (fun _ _ => rfl) (fun _ => rfl) rfl
  | cons r rs' =>
    cases hfn : T.frame.restoreRegs? with
    | none =>
      have hc' : (restoreCsList T.toIsa i (r :: rs')).IsInfixAt (T.mach.prog host) k := by
        simpa [restoreCs, hfn] using hc
      simpa [restoreCs, hfn] using
        restoreCsList_ok i (r :: rs') k s G hc' hsp hnd hsub hmem
          (by simpa [restoreCs, hfn] using kont)
    | some fn =>
      have hc' : (fn i (r :: rs')).IsInfixAt (T.mach.prog host) k := by
        simpa [restoreCs, hfn] using hc
      refine T.frameSpec.restoreRegs_spec hfn hnd hsub hsp hmem hc' fun s' hq hfr => ?_
      have := kont s' hq.1 hfr.1 (fun v => hfr.2.1 v List.not_mem_nil) hq.2
      simpa [restoreCs, hfn] using this

end AbiH

section Lemmas
variable {T : Target} {host : T.mach.Host} {post : T.mach.State → Prop} {hints : T.toIsa.Hints}
  {E : Ext} {Γ : Env} {s₀ : T.mach.MData} {ra : T.mach.Addr} {n nX : Nat} {Rf : Mem 64 → Prop}
  {bound : Sym → Nat}

private theorem base_add_frame :
    base T hints s₀ + BitVec.ofNat 64 (frame T hints) = T.mach.getGpr s₀ T.frame.sp :=
  BitVec.sub_add_cancel _ _

private theorem abi_not_leave {r : T.Reg} (h : IsAbi T r) :
    r ∉ T.frame.calleeSaved ++ (T.frame.sp :: T.frame.raRegs ++ T.frame.scratch) := by
  simp only [List.mem_append, List.mem_cons, not_or]
  exact ⟨h.not_cs, ⟨h.ne_sp, h.not_ra⟩, h.not_scratch⟩

private theorem frame_close (hy : Hyps T host hints E Γ s₀ n nX bound)
    (hzl : isZeroLeaf T.toIsa hints E = false) {m : Mem 64}
    {σ : List (BitVec 64)} (hσ : σ.length = hints.nslots) {M : Mem 64}
    (hM : M =⋆ T.frameSpec.RetAddr (T.mach.getGpr s₀ T.frame.sp) ra ⋆
      region (base T hints s₀ + BitVec.ofNat 64 (8 * hints.totalSlots))
        (frame T hints - 8 * hints.totalSlots) ⋆
      (Eq m ⋆ array64 (base T hints s₀) σ ⋆ csSlots T hints s₀ ⋆
        region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n) (n - frame T hints) ⋆ Rf)) :
    M =⋆ Eq m ⋆ (T.Entry (T.mach.getGpr s₀ T.frame.sp) ra n ⋆ Rf) := by
  have h8 : 8 * hints.totalSlots ≤ frame T hints := T.frameSpec.slots_le_frameSize _
  have hF : frame T hints + T.frame.raBytes ≤ 2 ^ 64 := by
    have := hy.frame_bound
    simp only [effFrame, hzl, Bool.false_eq_true, ↓reduceIte] at this; exact this
  have hFn : frame T hints ≤ n := by
    have := hy.frame_le
    simp only [effFrame, hzl, Bool.false_eq_true, ↓reduceIte] at this; exact this
  have hn := hy.stack_bound
  have h1 : M =⋆ (array64 (base T hints s₀) σ ⋆ csSlots T hints s₀) ⋆
      region (base T hints s₀ + BitVec.ofNat 64 (8 * hints.totalSlots))
        (frame T hints - 8 * hints.totalSlots) ⋆
      (T.frameSpec.RetAddr (T.mach.getGpr s₀ T.frame.sp) ra ⋆ Eq m ⋆
        region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n) (n - frame T hints) ⋆ Rf) :=
    sep_cast hM (by ac_rfl)
  have h2 := sep_mono (fun _ h => sep_mono (P' := region (base T hints s₀) (8 * hints.totalSlots))
    (fun _ h => slots_region hσ (by omega) h) h) h1
  have h2' : M =⋆ region (base T hints s₀) (frame T hints) ⋆
      (T.frameSpec.RetAddr (T.mach.getGpr s₀ T.frame.sp) ra ⋆ Eq m ⋆
        region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n) (n - frame T hints) ⋆ Rf) := by
    rw [pad_split h8 (by omega)]; exact h2
  have h3 : M =⋆ region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n) n ⋆
      (Eq m ⋆ T.frameSpec.RetAddr (T.mach.getGpr s₀ T.frame.sp) ra ⋆ Rf) := by
    rw [below_split hFn (by omega)]; exact sep_cast h2' (by ac_rfl)
  unfold Target.Entry
  exact sep_cast h3 (by ac_rfl)

/-- `restoreCs; epilogue`: from the frame invariant to the caller's `Entry` footprint. -/
private theorem leave_ok (hy : Hyps T host hints E Γ s₀ n nX bound) {k : Nat}
    {s : T.mach.MData} {m : Mem 64} {σ : List (BitVec 64)}
    (hr : (restoreCs T.toIsa hints.nslots hints.saved).IsInfixAt (T.mach.prog host) k)
    (he : (fnEpilogue T.toIsa hints E).IsInfixAt (T.mach.prog host)
      (k + (restoreCs T.toIsa hints.nslots hints.saved).length))
    (hI : Inv T hints s₀ ra n Rf m s σ (isZeroLeaf T.toIsa hints E))
    (kont : ∀ s2, (∀ r ∈ T.frame.calleeSaved, T.mach.getGpr s2 r = T.mach.getGpr s₀ r) →
      T.mach.getGpr s2 T.frame.sp = T.mach.getGpr s₀ T.frame.sp → T.frameSpec.raReg s2 ra →
      T.mach.KeepsGpr s s2
        (T.frame.calleeSaved ++ (T.frame.sp :: T.frame.raRegs ++ T.frame.scratch)) →
      (∀ v, T.mach.getVec s2 v = T.mach.getVec s v) →
      (T.mach.mem s2 =⋆ Eq m ⋆ (T.Entry (T.mach.getGpr s₀ T.frame.sp) ra n ⋆ Rf)) →
      T.mach.Run host (k + (restoreCs T.toIsa hints.nslots hints.saved).length +
        (fnEpilogue T.toIsa hints E).length) s2 post) :
    T.mach.Run host k s post := by
  cases hzl : isZeroLeaf T.toIsa hints E with
  | true =>
    rw [hzl] at hI
    obtain ⟨hσ, hsp, hcs, hmem, -, -, hzlI⟩ := hI
    obtain ⟨htot0, hra⟩ := hzlI rfl
    have htot0' : hints.nslots + hints.saved.length = 0 := htot0
    have hns0 : hints.nslots = 0 := by omega
    have hsaved : hints.saved = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hσnil : σ = [] := List.eq_nil_of_length_eq_zero (hσ.trans hns0)
    have hsp' : T.mach.getGpr s T.frame.sp = T.mach.getGpr s₀ T.frame.sp := by
      simpa [baseZ, frameZ] using hsp
    have hm : T.mach.mem s =⋆ Eq m ⋆ (T.Entry (T.mach.getGpr s₀ T.frame.sp) ra n ⋆ Rf) := by
      subst hσnil
      simp only [FrZ, csSlotsZ, hsaved, List.map_nil, array64_nil, frameZ, ↓reduceIte,
        Nat.sub_zero, emp_sep] at hmem
      unfold Target.Entry
      exact sep_cast hmem (by ac_rfl)
    have hlen : k + (restoreCs T.toIsa hints.nslots hints.saved).length +
        (fnEpilogue T.toIsa hints E).length = k := by
      simp [restoreCs, fnEpilogue, hzl, hsaved]
    rw [← hlen]
    exact kont s (fun r hr => hcs r hr (by simp [hsaved])) hsp' hra
      (fun _ _ => rfl) (fun _ => rfl) hm
  | false =>
    rw [hzl] at hI
    simp only [fnEpilogue, hzl, Bool.false_eq_true, ↓reduceIte] at he kont ⊢
    obtain ⟨hσ, hsp, hcs, hmem, hsub, hnd, -⟩ := hI
    have hF : frame T hints + T.frame.raBytes ≤ 2 ^ 64 := by
      have := hy.frame_bound
      simp only [effFrame, hzl, Bool.false_eq_true, ↓reduceIte] at this; exact this
    have hspOk : T.frameSpec.spOk (base T hints s₀) := T.frameSpec.spOk_frame _ _ hy.spE
    have hsp' : T.mach.getGpr s T.frame.sp = base T hints s₀ := hsp
    have hmem' :
        T.mach.mem s =⋆ Eq m ⋆ (array64 (base T hints s₀) σ ⋆ Fr T hints s₀ ra n Rf) := hmem
    unfold Fr at hmem'
    refine restoreCs_ok (s₀ := s₀) hints.nslots hints.saved k s
      (Eq m ⋆ array64 (base T hints s₀) σ ⋆
        T.frameSpec.Saved (T.mach.getGpr s₀ T.frame.sp) ra hints.totalSlots ⋆
        region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n) (n - frame T hints) ⋆ Rf)
      hr (by rw [hsp']; exact hspOk) hnd hsub
      (by
        rw [hsp']
        exact (sep_cast hmem' (by ac_rfl) :
          (csSlots T hints s₀ ⋆ (Eq m ⋆ array64 (base T hints s₀) σ ⋆
          T.frameSpec.Saved (T.mach.getGpr s₀ T.frame.sp) ra hints.totalSlots ⋆
          region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n) (n - frame T hints) ⋆ Rf)) _))
      fun s1 hrest1 hk1 hv1 hm1 => ?_
    have hsp1 : T.mach.getGpr s1 T.frame.sp = base T hints s₀ := by
      rw [hk1 _ (by
        simp only [List.mem_append, not_or]
        exact ⟨fun h => cs_ne_sp (hsub _ h) rfl, T.frameSpec.sp_disj.1⟩), hsp']
    refine T.frameSpec.epilogue_spec (by rw [hsp1]; exact hspOk) hF
      (G := Eq m ⋆ array64 (base T hints s₀) σ ⋆ csSlots T hints s₀ ⋆
        region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n) (n - frame T hints) ⋆ Rf)
      (by rw [hsp1, base_add_frame, hm1]; exact sep_cast hmem' (by ac_rfl)) he
      fun s2 hq2 hfr2 => ?_
    obtain ⟨hsp2, hra2, hm2⟩ := hq2
    rw [hsp1, base_add_frame] at hm2
    have hk2 := hfr2.1
    refine kont s2 (fun r hr => ?_) (by rw [hsp2, hsp1, base_add_frame]) hra2
      ((hk1.trans hk2).mono fun r hr => ?_) (fun v => (hfr2.2.1 v List.not_mem_nil).trans (hv1 v))
      (frame_close hy hzl hσ hm2)
    · have h2 : T.mach.getGpr s2 r = T.mach.getGpr s1 r := hk2 r (by
        simp only [List.mem_cons, List.mem_append, not_or]
        exact ⟨⟨cs_ne_sp hr, cs_not_ra hr⟩, cs_not_scratch hr⟩)
      rw [h2]
      by_cases hs : r ∈ hints.saved
      · exact hrest1 r hs
      · rw [hk1 r (by simp only [List.mem_append, not_or]; exact ⟨hs, cs_not_scratch hr⟩)]
        exact hcs r hr hs
    · simp only [List.mem_append, List.mem_cons] at hr ⊢
      rcases hr with (h | h) | h
      · exact .inl (hsub r h)
      · exact .inr (.inr h)
      · exact .inr h

/-- Canonicalization of the ABI targets, keeping the frame invariant. -/
private theorem canon_inv {zl : Bool} {gs : List T.Reg} {vs : List T.VReg}
    (hy : Hyps T host hints E Γ s₀ n nX bound)
    (hgs : ∀ r ∈ gs, IsAbi T r) (hnd : gs.Nodup) {G : VCtx} {ts : List Ty}
    {args₁ : Tup (Arg Val) ts} {args : Tup (Arg VNat) ts} (hrel : TRel (ArgRel G) args₁ args)
    {locs : Tup (AbiReg T.Reg T.VReg) ts} (hloc : T.toIsa.assignSig ts gs vs = some locs)
    {tgts : List (SymArg × T.toIsa.Loc)} (htg : abiTargets T.toIsa args locs = some tgts)
    {k nv : Nat} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64} {st : SymState T.toIsa}
    (hc : (canonAbiCode T.toIsa locs (abiSkips T.toIsa st.regs st.zeroExt32 args locs)).IsInfixAt
      (T.mach.prog host) k)
    (hok : ∀ p ∈ tgts, LocOk T.mach G s σ p.1 p.2) (hA : Agree T G nv st s σ)
    (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (kont : ∀ s1, TRel (T.mach.AbiHolds s1) locs (vals args₁) →
      (∀ r ∈ T.frame.calleeSaved, T.mach.getGpr s1 r = T.mach.getGpr s r) →
      Inv T hints s₀ ra n Rf m s1 σ zl →
      T.mach.Run host (k + (canonAbiCode T.toIsa locs
        (abiSkips T.toIsa st.regs st.zeroExt32 args locs)).length) s1 post) :
    T.mach.Run host k s post := by
  have _ := hy
  refine canon_ok hloc hnd (fun r hr => (hgs r hr).not_scratch) (pre_of_targets hrel htg hok)
    (skipOk_of_abiSkips hA hrel) hc
    fun s1 hab hk1 hv1 hm1 =>
      kont s1 hab (fun r hr => hk1 r ?_) (Inv.keep hI hm1 fun r hr => hk1 r ?_)
  · simp only [List.mem_append, not_or]
    exact ⟨fun h => (hgs r h).not_cs hr, cs_not_scratch hr⟩
  · obtain ⟨h1, h2⟩ := isMoveGpr_abi hr
    simp only [List.mem_append, not_or]
    exact ⟨fun h => h1 (hgs r h), h2⟩

theorem listTyEq_iff {a b : List Ty} : listTyEq a b = true ↔ a = b := by
  have hty : ∀ {x y : Ty}, tyEq x y = true ↔ x = y := by
    intro x
    induction x with
    | pair a1 b1 ih1 ih2 => intro y; cases y <;> simp [tyEq, ih1, ih2]
    | _ => intro y; cases y <;> simp [tyEq]
  induction a generalizing b with
  | nil => cases b <;> simp [listTyEq]
  | cons x xs ih => cases b <;> simp [listTyEq, hty, ih]

/-- `ret`: after the shuffle established the ABI return targets. -/
theorem ret_ok (hy : Hyps T host hints E Γ s₀ n nX bound) {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : VCtx} {vs₁ : Tup (Arg Val) rs} {vs : Tup (Arg VNat) rs} (hrel : TRel (ArgRel G) vs₁ vs)
    {retLocs : Tup (AbiReg T.Reg T.VReg) rs} (hloc : T.toIsa.assignRets rs = some retLocs)
    {tgts : List (SymArg × T.toIsa.Loc)} (htg : abiTargets T.toIsa vs retLocs = some tgts)
    {k nv : Nat} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64} {st : SymState T.toIsa}
    (hc : (canonAbiCode T.toIsa retLocs (abiSkips T.toIsa st.regs st.zeroExt32 vs retLocs) ++
      restoreCs T.toIsa hints.nslots hints.saved ++
      fnEpilogue T.toIsa hints E ++ T.frame.ret).IsInfixAt (T.mach.prog host) k)
    (hok : ∀ p ∈ tgts, LocOk T.mach G s σ p.1 p.2) (hA : Agree T G nv st s σ)
    (hI : Inv T hints s₀ ra n Rf m s σ (isZeroLeaf T.toIsa hints E))
    (hQ : Q (vals vs₁) m) :
    T.mach.Run host k s (FnPost T host s₀ ra n nX Rf Q X) := by
  obtain ⟨hc3, hc4⟩ := hc.append
  obtain ⟨hc2, hc3⟩ := hc3.append
  obtain ⟨hc1, hc2⟩ := hc2.append
  simp only [List.length_append, ← Nat.add_assoc] at hc3 hc4
  refine canon_inv hy (fun r hr => .inr hr) T.frameSpec.retRegs_nodup hrel hloc htg hc1 hok hA hI
    fun s1 hab _ hI1 => leave_ok hy hc2 hc3 hI1 fun s2 hcs2 hsp2 hra2 hk2 hv2 hm2 => ?_
  have hm2' : T.mach.mem s2 =⋆ T.frameSpec.RetAddr (T.mach.getGpr s2 T.frame.sp) ra ⋆
      (Eq m ⋆ region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n) n ⋆ Rf) := by
    rw [hsp2]; unfold Target.Entry at hm2; exact sep_cast hm2 (by ac_rfl)
  refine T.frameSpec.ret_spec hc4 hra2 hm2' fun s3 hk3 hv3 hsp3 hm3 => ?_
  refine .done _ (Or.inl ⟨T.mach.pc_mk _ _, vals vs₁, m, hQ, ?_, ⟨?_, ?_⟩, ?_⟩) <;>
    rw [T.mach.data_mk]
  · refine ⟨retLocs, hloc, trel_keep abiHolds_keep (fun r hr => ?_)
      (fun v => (hv3 v List.not_mem_nil).trans (hv2 v)) hab⟩
    have ha : IsAbi T r := .inr (abiGprs_sub hloc r hr)
    rw [hk3 r (by simp only [List.mem_cons, not_or]; exact ⟨ha.ne_sp, ha.not_scratch⟩),
      hk2 r (abi_not_leave ha)]
  · intro r hr
    rw [hk3 r (by simp only [List.mem_cons, not_or]; exact ⟨cs_ne_sp hr, cs_not_scratch hr⟩)]
    exact hcs2 r hr
  · rw [hsp3, hsp2]
  · rw [hm3]
    exact sep_mono_mid (fun _ h => entry_exit hy.stack_bound h) (sep_cast hm2 (by ac_rfl))

/-- `exit`: tail jump to an allowed exit symbol. -/
theorem exit_ok (hy : Hyps T host hints E Γ s₀ n nX bound) {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : VCtx} {f : Sym} {as : List Ty} {args₁ : Tup (Arg Val) as} {args : Tup (Arg VNat) as}
    (hrel : TRel (ArgRel G) args₁ args) (hex : E.exits.contains f = true)
    {argLocs : Tup (AbiReg T.Reg T.VReg) as} (hloc : T.toIsa.assignArgs as = some argLocs)
    {tgts : List (SymArg × T.toIsa.Loc)} (htg : abiTargets T.toIsa args argLocs = some tgts)
    {k nv : Nat} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64} {st : SymState T.toIsa}
    (hc : (canonAbiCode T.toIsa argLocs (abiSkips T.toIsa st.regs st.zeroExt32 args argLocs) ++
      restoreCs T.toIsa hints.nslots hints.saved ++
      fnEpilogue T.toIsa hints E ++ T.frame.exitJmp f).IsInfixAt (T.mach.prog host) k)
    (hok : ∀ p ∈ tgts, LocOk T.mach G s σ p.1 p.2) (hA : Agree T G nv st s σ)
    (hI : Inv T hints s₀ ra n Rf m s σ (isZeroLeaf T.toIsa hints E))
    (hX : X f as (vals args₁) m) :
    T.mach.Run host k s (FnPost T host s₀ ra n nX Rf Q X) := by
  obtain ⟨hdef, hnX⟩ := hy.exits f (by simpa using hex)
  obtain ⟨hc3, hc4⟩ := hc.append
  obtain ⟨hc2, hc3⟩ := hc3.append
  obtain ⟨hc1, hc2⟩ := hc2.append
  simp only [List.length_append, ← Nat.add_assoc] at hc3 hc4
  refine canon_inv hy (fun r hr => .inl hr) T.frameSpec.argRegs_nodup hrel hloc htg hc1 hok hA hI
    fun s1 hab _ hI1 => leave_ok hy hc2 hc3 hI1 fun s2 hcs2 hsp2 hra2 hk2 hv2 hm2 => ?_
  refine T.frameSpec.exitJmp_spec hc4 fun s3 hfr3 hm3 => ?_
  have hsp3 : T.mach.getGpr s3 T.frame.sp = T.mach.getGpr s₀ T.frame.sp := by
    rw [hfr3.1 _ T.frameSpec.sp_disj.1, hsp2]
  refine .done _ (Or.inr ⟨f, as, vals args₁, m, hX, hdef, T.mach.pc_mk _ _, ?_, ?_, ra, n, emp,
    hnX, hy.stack_bound, ?_, ?_⟩) <;> rw [T.mach.data_mk]
  · refine ⟨argLocs, hloc, trel_keep abiHolds_keep (fun r hr => ?_)
      (fun v => (hfr3.2.1 v List.not_mem_nil).trans (hv2 v)) hab⟩
    have ha : IsAbi T r := .inl (abiGprs_sub hloc r hr)
    rw [hfr3.1 r ha.not_scratch, hk2 r (abi_not_leave ha)]
  · rw [hsp3]; exact hy.spE
  · exact T.frameSpec.raReg_of_raRegs _ _ _
      (fun r hr => hfr3.1 r (T.frameSpec.ra_disj r hr).2.1) hra2
  · rw [hm3, hsp3, sep_emp]
    exact sep_cast hm2 (by ac_rfl)

/-- `call`: ABI argument targets established; returns to `k + code.length` with results bound. -/
theorem call_ok (hy : Hyps T host hints E Γ s₀ n nX bound) {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : VCtx} {nv : Nat} {f : Sym} {as bs : List Ty} {args₁ : Tup (Arg Val) as}
    {args : Tup (Arg VNat) as} (hrel : TRel (ArgRel G) args₁ args)
    (hcal : calleeAllowed E f as bs = true)
    {argLocs : Tup (AbiReg T.Reg T.VReg) as} (hal : T.toIsa.assignArgs as = some argLocs)
    {retLocs : Tup (AbiReg T.Reg T.VReg) bs} (hrl : T.toIsa.assignRets bs = some retLocs)
    {tgts : List (SymArg × T.toIsa.Loc)} (htg : abiTargets T.toIsa args argLocs = some tgts)
    {st st' : SymState T.toIsa}
    (hb : bindAbiParams T.toIsa retLocs nv (afterCallState T.toIsa hints.saved st) = some st')
    {k : Nat} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    (hc : (canonAbiCode T.toIsa argLocs (abiSkips T.toIsa st.regs st.zeroExt32 args argLocs) ++
      T.frame.call f).IsInfixAt (T.mach.prog host) k)
    (hok : ∀ p ∈ tgts, LocOk T.mach G s σ p.1 p.2) (hA : Agree T G nv st s σ)
    (hI : Inv T hints s₀ ra n Rf m s σ (isZeroLeaf T.toIsa hints E))
    {P : Post bs} {X' : XPost} (hspec : Γ f as bs (vals args₁) m P X')
    (hX : ∀ g cs xs m', X' g cs xs m' → X g cs xs m')
    (kont : ∀ (rets : Tup Val bs) (m' : Mem 64) s' σ', P rets m' →
      Agree T (Tup.zip rets (Tup.levels bs nv) ++ G) (nv + bs.length) st' s' σ' →
      Inv T hints s₀ ra n Rf m' s' σ' (isZeroLeaf T.toIsa hints E) →
      T.mach.Run host (k +
        (canonAbiCode T.toIsa argLocs (abiSkips T.toIsa st.regs st.zeroExt32 args argLocs) ++
        T.frame.call f).length) s' (FnPost T host s₀ ra n nX Rf Q X)) :
    T.mach.Run host k s (FnPost T host s₀ ra n nX Rf Q X) := by
  have hmemE : (f, as, bs) ∈ E.callees := by
    simp only [calleeAllowed, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      listTyEq_iff] at hcal
    obtain ⟨⟨g, gas, gbs⟩, hmem, ⟨rfl, rfl⟩, rfl⟩ := hcal
    exact hmem
  have hzl : isZeroLeaf T.toIsa hints E = false := by
    cases hcE : E.callees with
    | nil => simp [hcE] at hmemE
    | cons _ _ => simp [isZeroLeaf, hcE]
  rw [hzl] at hI
  obtain ⟨hf, hbd⟩ := hy.callees f as bs hmemE
  simp only [effFrame, hzl, Bool.false_eq_true, ↓reduceIte] at hbd
  have hn := hy.stack_bound
  obtain ⟨hc1, hc2⟩ := hc.append
  refine canon_inv hy (fun r hr => .inl hr) T.frameSpec.argRegs_nodup hrel hal htg hc1 hok hA hI
    fun s1 hab hcs1 hI1 => ?_
  obtain ⟨hσ, hsp1, hcsI, hmem1, hsub, hnd, -⟩ := hI1
  have hsp1' : T.mach.getGpr s1 T.frame.sp = base T hints s₀ := hsp1
  have hmem1' :
      T.mach.mem s1 =⋆ Eq m ⋆ (array64 (base T hints s₀) σ ⋆ Fr T hints s₀ ra n Rf) := hmem1
  unfold Fr at hmem1'
  rw [callee_split hbd (by omega)] at hmem1'
  have hm1 : T.mach.mem s1 =⋆
      region (T.mach.getGpr s1 T.frame.sp - BitVec.ofNat 64 T.frame.raBytes) T.frame.raBytes ⋆
      (Eq m ⋆ region (base T hints s₀ - BitVec.ofNat 64 T.frame.raBytes -
          BitVec.ofNat 64 (bound f)) (bound f) ⋆
        ((array64 (base T hints s₀) σ ⋆ csSlots T hints s₀ ⋆
          T.frameSpec.Saved (T.mach.getGpr s₀ T.frame.sp) ra hints.totalSlots ⋆
          region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n)
            (n - frame T hints - (bound f + T.frame.raBytes))) ⋆ Rf)) := by
    rw [hsp1']; exact sep_cast hmem1' (by ac_rfl)
  refine T.frameSpec.call_spec hc2 hm1 fun s2 hsp2 hfr2 hra2 hm2 => ?_
  rw [hsp1'] at hsp2
  have hk2 := hfr2.1
  have hab2 : TRel (T.mach.AbiHolds s2) argLocs (vals args₁) :=
    trel_keep abiHolds_keep (fun r hr => by
      have ha : IsAbi T r := .inl (abiGprs_sub hal r hr)
      exact hk2 r (by
        simp only [List.mem_cons, List.mem_append, not_or]
        exact ⟨⟨ha.ne_sp, ha.not_ra⟩, ha.not_scratch⟩))
      (fun v => hfr2.2.1 v List.not_mem_nil) hab
  have hentry : T.mach.mem s2 =⋆ Eq m ⋆
      T.Entry (T.mach.getGpr s2 T.frame.sp)
        (T.mach.addrOf host (k + (canonAbiCode T.toIsa argLocs
          (abiSkips T.toIsa st.regs st.zeroExt32 args argLocs)).length + (T.frame.call f).length))
        (bound f) ⋆
      ((array64 (base T hints s₀) σ ⋆ csSlots T hints s₀ ⋆
          T.frameSpec.Saved (T.mach.getGpr s₀ T.frame.sp) ra hints.totalSlots ⋆
          region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n)
            (n - frame T hints - (bound f + T.frame.raBytes))) ⋆ Rf) := by
    unfold Target.Entry; rw [hsp2]; rw [hsp2] at hm2; exact sep_cast hm2 (by ac_rfl)
  have hspE : T.frameSpec.spEntry (T.mach.getGpr s2 T.frame.sp) := by
    rw [hsp2]; exact T.frameSpec.spEntry_call _ _ hy.spE
  refine eventually_trans _ _ _ _
    (hf (vals args₁) m P X' hspec s2 _ _ ⟨argLocs, hal, hab2⟩ hra2 hspE hentry) ?_
  rintro st0 (⟨hpc, rets, m', hP, ⟨locs', hl', hrets⟩, ⟨hres, hspr⟩, hmx⟩ |
    ⟨sym', cs, xs, m', hX', hdef, hpc, has, hspE', ra', n', F, hnX, hb', hra', hmx⟩)
  · rw [hrl, Option.some.injEq] at hl'
    subst hl'
    have hkeep : ∀ r ∈ T.frame.calleeSaved,
        T.mach.getGpr (T.mach.data st0) r = T.mach.getGpr s1 r := fun r hr => by
      rw [hres r hr, hk2 r (by
        simp only [List.mem_cons, List.mem_append, not_or]
        exact ⟨⟨cs_ne_sp hr, cs_not_ra hr⟩, cs_not_scratch hr⟩)]
    have hA' : Agree T G nv (afterCallState T.toIsa hints.saved st) (T.mach.data st0) σ :=
      { hA with
        regs := fun p hp => by
          obtain ⟨hp, hs⟩ := List.mem_filter.mp hp
          have h := hA.regs p hp
          obtain ⟨sa, rl⟩ := p
          cases rl with
          | gpr r =>
            have hs' : r ∈ hints.saved := by simpa using hs
            show GprSym G _ sa
            rw [hkeep r (hsub r hs'), hcs1 r (hsub r hs')]
            exact h
          | gprZ r =>
            have hs' : r ∈ hints.saved := by simpa using hs
            refine ⟨?_, ?_⟩
            · show GprSym G _ sa
              rw [hkeep r (hsub r hs'), hcs1 r (hsub r hs')]
              exact h.1
            · show SymZ G _ sa
              rw [hkeep r (hsub r hs'), hcs1 r (hsub r hs')]
              exact h.2
          | vec _ => simp at hs
          | flag _ => simp at hs
        regs_lt := fun p hp => hA.regs_lt p (List.mem_filter.mp hp).1
        zeroExt32_ok := fun r hr => by
          simp only [afterCallState, List.mem_filter] at hr
          have hs' : r ∈ hints.saved := by simpa [List.contains_iff_mem] using hr.2
          have hcs : r ∈ T.frame.calleeSaved := hsub r hs'
          rw [hkeep r hcs, hcs1 r hcs]
          exact hA.zeroExt32_ok r hr.1
        flags_ok := trivial
        flags_lt := trivial
        scrConsts_ok := scrOk_nil _ _ _ }
    have hI' : Inv T hints s₀ ra n Rf m' (T.mach.data st0) σ false := by
      refine ⟨hσ, by show T.mach.getGpr (T.mach.data st0) T.frame.sp = base T hints s₀
                     rw [hspr, hsp2, BitVec.sub_add_cancel],
        fun r hr hns => (hkeep r hr).trans (hcsI r hr hns), ?_, hsub, hnd, fun h => by cases h⟩
      change T.mach.mem (T.mach.data st0) =⋆
        Eq m' ⋆ (array64 (base T hints s₀) σ ⋆ Fr T hints s₀ ra n Rf)
      unfold Fr
      rw [callee_split' hbd (by omega)]
      unfold Target.Exit at hmx
      rw [hsp2] at hmx
      exact sep_cast hmx (by ac_rfl)
    have := kont rets m' _ σ hP (bindAbiParams_ok hb hrets hA') (by rw [hzl]; exact hI')
    rw [← T.mach.mk_eta st0, hpc]
    unfold Machine.Run at this
    rwa [List.length_append, ← Nat.add_assoc] at this
  · exact .done _ (Or.inr ⟨sym', cs, xs, m', hX _ _ _ _ hX', hdef, hpc, has, hspE', ra', n',
      F ⋆ (array64 (base T hints s₀) σ ⋆ csSlots T hints s₀ ⋆
          T.frameSpec.Saved (T.mach.getGpr s₀ T.frame.sp) ra hints.totalSlots ⋆
          region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n)
            (n - frame T hints - (bound f + T.frame.raBytes))),
      hnX, hb', hra', sep_cast hmx (by ac_rfl)⟩)

/-- Function entry: prologue + `saveCs` + ABI parameter binding. -/
theorem fn_entry_ok (hy : Hyps T host hints E Γ s₀ n nX bound) {as : List Ty} {args : Tup Val as}
    {m : Mem 64} (hargs : T.ArgsIn args s₀) (hra : T.frameSpec.raReg s₀ ra)
    (hmem : T.mach.mem s₀ =⋆ Eq m ⋆ T.Entry (T.mach.getGpr s₀ T.frame.sp) ra n ⋆ Rf)
    {argLocs : Tup (AbiReg T.Reg T.VReg) as} (hal : T.toIsa.assignArgs as = some argLocs)
    {st0 : SymState T.toIsa}
    (hb : bindAbiParams T.toIsa argLocs 0
      { regs := [], slots := .empty, defs := .empty, vecWidths := .empty } = some st0) {k : Nat}
    (hc : (fnPrologue T.toIsa hints E ++ saveCs T.toIsa hints.nslots hints.saved).IsInfixAt
      (T.mach.prog host) k)
    (kont : ∀ s' σ, Agree T (Tup.zip args (Tup.levels as 0)) as.length st0 s' σ →
      Inv T hints s₀ ra n Rf m s' σ (isZeroLeaf T.toIsa hints E) →
      T.mach.Run host (k + (fnPrologue T.toIsa hints E ++
        saveCs T.toIsa hints.nslots hints.saved).length) s' post) :
    T.mach.Run host k s₀ post := by
  obtain ⟨locs, hl, htr⟩ := hargs
  rw [hal, Option.some.injEq] at hl
  subst hl
  cases hzl : isZeroLeaf T.toIsa hints E with
  | true =>
    have hzl' := hzl
    simp only [isZeroLeaf, Bool.and_eq_true, Nat.beq_eq] at hzl'
    obtain ⟨⟨-, htot0⟩, -⟩ := hzl'
    have htot0' : hints.nslots + hints.saved.length = 0 := htot0
    have hns0 : hints.nslots = 0 := by omega
    have hsaved : hints.saved = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hI0 : Inv T hints s₀ ra n Rf m s₀ [] true := by
      refine ⟨hns0.symm, by simp [baseZ, frameZ], fun _ _ _ => rfl, ?_, hy.saved_cs,
        hy.saved_nodup, fun _ => ⟨htot0, hra⟩⟩
      simp only [FrZ, csSlotsZ, hsaved, List.map_nil, array64_nil, frameZ, ↓reduceIte,
        Nat.sub_zero, emp_sep]
      unfold Target.Entry at hmem
      exact sep_cast hmem (by ac_rfl)
    have hA0 : Agree T [] 0
        { regs := [], slots := .empty, defs := .empty, vecWidths := .empty } s₀ [] := by
      constructor <;> intros <;> first | exact scrOk_nil _ _ _ | simp_all [Trie.find?]
    have hA := bindAbiParams_ok hb htr hA0
    rw [List.append_nil, Nat.zero_add] at hA
    have hlen : k + (fnPrologue T.toIsa hints E ++
        saveCs T.toIsa hints.nslots hints.saved).length = k := by
      simp [fnPrologue, saveCs, hzl, hsaved]
    rw [← hlen]
    exact kont s₀ [] hA (by rw [hzl]; exact hI0)
  | false =>
    simp only [fnPrologue, hzl, Bool.false_eq_true, ↓reduceIte] at hc kont ⊢
    have h8 : 8 * hints.totalSlots ≤ frame T hints := T.frameSpec.slots_le_frameSize _
    have hF : frame T hints + T.frame.raBytes ≤ 2 ^ 64 := by
      have := hy.frame_bound
      simp only [effFrame, hzl, Bool.false_eq_true, ↓reduceIte] at this; exact this
    have hFn : frame T hints ≤ n := by
      have := hy.frame_le
      simp only [effFrame, hzl, Bool.false_eq_true, ↓reduceIte] at this; exact this
    have hn := hy.stack_bound
    have htot : hints.totalSlots = hints.nslots + hints.saved.length := rfl
    obtain ⟨hc1, hc2⟩ := hc.append
    have hm0 : T.mach.mem s₀ =⋆ T.frameSpec.RetAddr (T.mach.getGpr s₀ T.frame.sp) ra ⋆
        region (base T hints s₀) (frame T hints) ⋆
        (Eq m ⋆
          region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n) (n - frame T hints) ⋆ Rf) := by
      unfold Target.Entry at hmem
      rw [below_split hFn (by omega)] at hmem
      exact sep_cast hmem (by ac_rfl)
    refine T.frameSpec.prologue_spec hra hy.spE hF hm0 hc1 fun s1 hq1 hfr1 => ?_
    obtain ⟨hsp1, hm1⟩ := hq1
    have hsp1' : T.mach.getGpr s1 T.frame.sp = base T hints s₀ := hsp1
    have hm1' : T.mach.mem s1 =⋆ region (base T hints s₀) (8 * hints.totalSlots) ⋆
        (T.frameSpec.Saved (T.mach.getGpr s₀ T.frame.sp) ra hints.totalSlots ⋆
          (Eq m ⋆ region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n) (n - frame T hints) ⋆
            Rf)) := by
      have hm1a :
        T.mach.mem s1 =⋆ T.frameSpec.Saved (T.mach.getGpr s₀ T.frame.sp) ra hints.totalSlots ⋆
        region (base T hints s₀) (8 * hints.totalSlots) ⋆
        (Eq m ⋆ region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n) (n - frame T hints) ⋆
          Rf) := hm1
      exact sep_cast hm1a (by ac_rfl)
    rw [slots_split (by omega), sep_assoc] at hm1'
    obtain ⟨σ, hσ, hm1''⟩ := region_array64_sep (by omega) hm1'
    have hk1 := hfr1.1
    have hcs1 : ∀ r ∈ T.frame.calleeSaved, T.mach.getGpr s1 r = T.mach.getGpr s₀ r :=
      fun r hr => hk1 r (by
        simp only [List.mem_cons, List.mem_append, not_or]
        exact ⟨⟨cs_ne_sp hr, cs_not_ra hr⟩, cs_not_scratch hr⟩)
    refine saveCs_ok hints.nslots hints.saved _ s1
      (array64 (base T hints s₀) σ ⋆
        (T.frameSpec.Saved (T.mach.getGpr s₀ T.frame.sp) ra hints.totalSlots ⋆
          (Eq m ⋆ region (T.mach.getGpr s₀ T.frame.sp - BitVec.ofNat 64 n) (n - frame T hints) ⋆
            Rf)))
      hc2 (by rw [hsp1']; exact T.frameSpec.spOk_frame _ _ hy.spE) (by omega)
      (fun r hr => cs_not_scratch (hy.saved_cs r hr))
      (by rw [hsp1']; exact sep_cast hm1'' (by ac_rfl)) fun s2 hk2 hv2 hm2 => ?_
    have hmap : hints.saved.map (T.mach.getGpr s1) = hints.saved.map (T.mach.getGpr s₀) :=
      List.map_congr_left fun r hr => hcs1 r (hy.saved_cs r hr)
    rw [hsp1', hmap] at hm2
    have hI2 : Inv T hints s₀ ra n Rf m s2 σ false := by
      refine ⟨hσ, by
          show T.mach.getGpr s2 T.frame.sp = base T hints s₀
          rw [hk2 _ T.frameSpec.sp_disj.1, hsp1'],
        fun r hr _ => (hk2 r (cs_not_scratch hr)).trans (hcs1 r hr), ?_, hy.saved_cs,
        hy.saved_nodup, fun h => by cases h⟩
      change T.mach.mem s2 =⋆ Eq m ⋆ (array64 (base T hints s₀) σ ⋆ Fr T hints s₀ ra n Rf)
      unfold Fr csSlots
      exact sep_cast hm2 (by ac_rfl)
    have htr2 : TRel (T.mach.AbiHolds s2) argLocs args :=
      trel_keep abiHolds_keep (fun r hr => by
        have ha : IsAbi T r := .inl (abiGprs_sub hal r hr)
        rw [hk2 r ha.not_scratch, hk1 r (by
          simp only [List.mem_cons, List.mem_append, not_or]
          exact ⟨⟨ha.ne_sp, ha.not_ra⟩, ha.not_scratch⟩)])
        (fun v => (hv2 v).trans (hfr1.2.1 v List.not_mem_nil)) htr
    have hA0 : Agree T [] 0
        { regs := [], slots := .empty, defs := .empty, vecWidths := .empty } s2 σ := by
      constructor <;> intros <;> first | exact scrOk_nil _ _ _ | simp_all [Trie.find?]
    have hA := bindAbiParams_ok hb htr2 hA0
    rw [List.append_nil, Nat.zero_add] at hA
    have := kont s2 σ hA hI2
    rwa [List.length_append, ← Nat.add_assoc] at this

end Lemmas

private theorem addrScale_ofShift_eq {sh : Nat} {sc : AddrScale}
    (h : AddrScale.ofShift? sh = some sc) : sc.shift = sh := by
  rcases sh with _ | _ | _ | _ | _ <;> simp [AddrScale.ofShift?] at h <;> subst h <;> rfl

private theorem signExtend_64_setWidth_32 (d : BitVec 32) :
    (Int64.ofBitVec (d.signExtend 64)).toBitVec.setWidth 32 = d := by
  rw [Int64.toBitVec_ofBitVec]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi64 : i < 64 := by omega
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  simp [hi, hi64]

private theorem setWidth_32_signExtend_64 (d : BitVec 32) :
    (d.signExtend 64).setWidth 32 = d := by
  simpa [Int64.toBitVec_ofBitVec] using signExtend_64_setWidth_32 d

private theorem bv_shiftLeft_shiftLeft {w : Nat} (a : BitVec w) (k1 k2 : Nat) :
    (a <<< k1) <<< k2 = a <<< (k1 + k2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mod_mul_mod, Nat.pow_add, Nat.mul_assoc]

private theorem extractLea64_addImm {G : VCtx} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d) {x : Nat} {vx c rv : BitVec 64}
    (hmx : ⟨i64, vx, x⟩ ∈ G) (hrv : rv = vx + c)
    {base? : Option Nat} {idx : Nat} {sc : AddrScale} {disp : Int64}
    (h : (match defs.find? x with
      | some (.addrSum b idx 0 d) => some (some b, idx, .s1, Int64.ofBitVec (d + c))
      | _ =>
        match recordAddVarImm defs x c with
        | .scaleOff idx sh disp =>
          if Nat.beq sh 0 then none
          else (AddrScale.ofShift? sh).map fun sc => (none, idx, sc, Int64.ofBitVec disp)
        | .addrSum b idx sh disp =>
          if Nat.beq sh 0 && disp == 0#64 then none
          else (AddrScale.ofShift? sh).map fun sc => (some b, idx, sc, Int64.ofBitVec disp)
        | _ => none) = some (base?, idx, sc, disp)) :
    ∃ vi : BitVec 64, ⟨i64, vi, idx⟩ ∈ G ∧ ∃ vb : BitVec 64,
      (∀ b, base? = some b → ⟨i64, vb, b⟩ ∈ G) ∧
      rv = (if base?.isSome then vb else 0#64) + (vi <<< sc.shift) + disp.toBitVec := by
  cases hdx : defs.find? x with
  | none => simp [hdx, recordAddVarImm] at h
  | some d =>
    have hxok := hdefs x d hdx
    rw [hdx] at h
    cases d with
    | imm64 _ | addImm64 _ _ | andVarVar _ _ _ | andVarImm _ _ _ | binVarVar _ _ _ _
    | binVarImm _ _ _ _ | shlVarImm _ _ _ | sextVar _ _ _ | zextVar _ _ _
    | cmpZeroVar _ _ _ | testBitVar _ _ _ _ | shiftVarImm _ _ _ _ | negVar _ _ =>
      simp [recordAddVarImm, hdx] at h
    | scaleOff idx0 sh0 d0 =>
      simp only [recordAddVarImm, hdx] at h
      split at h
      · cases h
      · obtain ⟨sc0, hsc, he⟩ := Option.map_eq_some_iff.mp h
        cases he
        obtain ⟨vi, hi, hvx⟩ := hxok vx hmx
        exact ⟨vi, hi, 0#64, by simp, by
          simp [hrv, hvx, addrScale_ofShift_eq hsc, BitVec.add_assoc]⟩
    | addrSum b0 idx0 sh0 d0 =>
      cases sh0 with
      | zero =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl, rfl⟩
        obtain ⟨vb, vi, hb, hi, hvx⟩ := hxok vx hmx
        exact ⟨vi, hi, vb, fun _ hb' => by cases hb'; exact hb, by
          simp [hrv, hvx, AddrScale.shift, Int64.toBitVec_ofBitVec, BitVec.add_assoc]⟩
      | succ sh' =>
        simp only [recordAddVarImm, hdx, Nat.beq_eq, Nat.add_one_ne_zero, ↓reduceIte] at h
        obtain ⟨sc0, hsc, he⟩ := Option.map_eq_some_iff.mp h
        cases he
        obtain ⟨vb, vi, hb, hi, hvx⟩ := hxok vx hmx
        exact ⟨vi, hi, vb, fun _ hb' => by cases hb'; exact hb, by
          simp [hrv, hvx, addrScale_ofShift_eq hsc, BitVec.add_assoc]⟩

private theorem extractLea64_varVar_aux {G : VCtx} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d) {x y : Nat} {vx vy : BitVec 64}
    (hmx : ⟨i64, vx, x⟩ ∈ G) (hmy : ⟨i64, vy, y⟩ ∈ G)
    {base? : Option Nat} {idx : Nat} {sc : AddrScale} {disp : Int64}
    (hs12 : ∀ df, (defs.find? x).bind (recordAddScale defs · (defs.find? y) y) = some df →
      ∃ b i sh d, df = .addrSum b i sh d ∧ ∃ vb vi : BitVec 64,
        ⟨i64, vb, b⟩ ∈ G ∧ ⟨i64, vi, i⟩ ∈ G ∧ vx + vy = vb + (vi <<< sh) + d)
    (hb12 : ∀ df, (defs.find? x).bind (recordAddBase · y (defs.find? y)) = some df →
      ∃ b i sh d, df = .addrSum b i sh d ∧ ∃ vb vi : BitVec 64,
        ⟨i64, vb, b⟩ ∈ G ∧ ⟨i64, vi, i⟩ ∈ G ∧ vx + vy = vb + (vi <<< sh) + d) :
    ∀ {df},
      ((defs.find? x).bind (recordAddScale defs · (defs.find? y) y) <|>
       (defs.find? y).bind (recordAddScale defs · (defs.find? x) x) <|>
       (defs.find? x).bind (recordAddBase · y (defs.find? y)) <|>
       (defs.find? y).bind (recordAddBase · x (defs.find? x))).getD
         (.addrSum x y 0 0) = df →
      (match some df with
      | some (.scaleOff idx sh disp) =>
        if Nat.beq sh 0 then none
        else (AddrScale.ofShift? sh).map fun sc => (none, idx, sc, Int64.ofBitVec disp)
      | some (.addrSum b idx sh disp) =>
        if Nat.beq sh 0 && disp == 0#64 then none
        else (AddrScale.ofShift? sh).map fun sc => (some b, idx, sc, Int64.ofBitVec disp)
      | _ => none) = some (base?, idx, sc, disp) →
      ∃ vi : BitVec 64, ⟨i64, vi, idx⟩ ∈ G ∧ ∃ vb : BitVec 64,
        (∀ b, base? = some b → ⟨i64, vb, b⟩ ∈ G) ∧
        vx + vy = (if base?.isSome then vb else 0#64) + (vi <<< sc.shift) + disp.toBitVec := by
  intro df hdf h
  have hsum : ∃ b i sh d, df = .addrSum b i sh d ∧ ∃ vb vi : BitVec 64,
      ⟨i64, vb, b⟩ ∈ G ∧ ⟨i64, vi, i⟩ ∈ G ∧ vx + vy = vb + (vi <<< sh) + d := by
    cases hu : ((defs.find? x).bind (recordAddScale defs · (defs.find? y) y) <|>
        (defs.find? y).bind (recordAddScale defs · (defs.find? x) x) <|>
        (defs.find? x).bind (recordAddBase · y (defs.find? y)) <|>
        (defs.find? y).bind (recordAddBase · x (defs.find? x))) with
    | none =>
      rw [hu] at hdf; subst hdf
      exact ⟨x, y, 0, 0#64, rfl, vx, vy, hmx, hmy, by simp⟩
    | some df' =>
      rw [hu] at hdf; simp only [Option.getD_some] at hdf; subst hdf
      rcases orElse_eq_some hu with h1 | h1
      · exact hs12 _ h1
      rcases orElse_eq_some h1 with h2 | h2
      · obtain ⟨dy, hdy, hk⟩ := Option.bind_eq_some_iff.mp h2
        unfold recordAddScale at hk
        cases dy with
        | scaleOff idx0 sh0 d1 =>
          dsimp only at hk; split at hk; · cases hdx : defs.find? x with
            | some dx => cases dx with
              | addImm64 b d2 =>
                rw [hdx] at hk; dsimp only at hk
                by_cases hc : isScaledAddrSum defs b = true
                · simp only [hc, ↓reduceIte, Option.some.injEq] at hk; subst hk
                  obtain ⟨vi, hi, hvy⟩ := hdefs y _ hdy vy hmy
                  exact ⟨x, idx0, sh0, d1, rfl, vx, vi, hmx, hi, by rw [hvy]; ac_rfl⟩
                · simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hk
                  subst hk
                  obtain ⟨vi, hi, hvy⟩ := hdefs y _ hdy vy hmy
                  obtain ⟨vb, hb, hvx⟩ := (hdefs x _ hdx).2 vx hmx
                  exact ⟨b, idx0, sh0, d1 + d2, rfl, vb, vi, hb, hi, by rw [hvy, hvx]; ac_rfl⟩
              | _ =>
                rw [hdx] at hk; simp only [Option.some.injEq] at hk; subst hk
                obtain ⟨vi, hi, hvy⟩ := hdefs y _ hdy vy hmy
                exact ⟨x, idx0, sh0, d1, rfl, vx, vi, hmx, hi, by rw [hvy]; ac_rfl⟩
            | none =>
              rw [hdx] at hk; simp only [Option.some.injEq] at hk; subst hk
              obtain ⟨vi, hi, hvy⟩ := hdefs y _ hdy vy hmy
              exact ⟨x, idx0, sh0, d1, rfl, vx, vi, hmx, hi, by rw [hvy]; ac_rfl⟩
          · simp at hk
        | _ => simp at hk
      rcases orElse_eq_some h2 with h3 | h3
      · exact hb12 _ h3
      · obtain ⟨dy, hdy, hk⟩ := Option.bind_eq_some_iff.mp h3
        unfold recordAddBase at hk
        cases dy with
        | addImm64 b d1 =>
          cases hdx : defs.find? x with
          | some dx => cases dx with
            | addImm64 b2 d2 =>
              simp only [hdx, Option.some.injEq] at hk; subst hk
              obtain ⟨vb, hb, hvy⟩ := (hdefs y _ hdy).2 vy hmy
              obtain ⟨vb2, hb2, hvx⟩ := (hdefs x _ hdx).2 vx hmx
              exact ⟨b, b2, 0, d1 + d2, rfl, vb, vb2, hb, hb2, by
                simp only [BitVec.shiftLeft_zero]; rw [hvy, hvx]; ac_rfl⟩
            | _ =>
              simp only [hdx, Option.some.injEq] at hk; subst hk
              obtain ⟨vb, hb, hvy⟩ := (hdefs y _ hdy).2 vy hmy
              exact ⟨b, x, 0, d1, rfl, vb, vx, hb, hmx, by
                simp only [BitVec.shiftLeft_zero]; rw [hvy]; ac_rfl⟩
          | none =>
            simp only [hdx, Option.some.injEq] at hk; subst hk
            obtain ⟨vb, hb, hvy⟩ := (hdefs y _ hdy).2 vy hmy
            exact ⟨b, x, 0, d1, rfl, vb, vx, hb, hmx, by
              simp only [BitVec.shiftLeft_zero]; rw [hvy]; ac_rfl⟩
        | _ => simp at hk
  obtain ⟨b, i, sh, d, rfl, vb, vi, hb, hi, he⟩ := hsum
  dsimp only at h; split at h; · cases h
  obtain ⟨sc0, hsc, he0⟩ := Option.map_eq_some_iff.mp h; cases he0
  exact ⟨vi, hi, vb, fun _ hb' => by cases hb'; exact hb, by
    simp [he, addrScale_ofShift_eq hsc, Int64.toBitVec_ofBitVec]⟩

private theorem extractLea64_some_addImm {G : VCtx} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d) {x : Nat} {vx c rv : BitVec 64}
    (hmx : ⟨i64, vx, x⟩ ∈ G) (hrv : rv = vx + c)
    {base? : Option Nat} {idx : Nat} {sc : AddrScale} {disp : Int64}
    (h : (match defs.find? x with
      | some (.addrSum b idx 0 d) => some (some b, idx, .s1, Int64.ofBitVec (d + c))
      | _ =>
        match some (recordAddVarImm defs x c) with
        | some (.scaleOff idx sh disp) =>
          if Nat.beq sh 0 then none
          else (AddrScale.ofShift? sh).map fun sc => (none, idx, sc, Int64.ofBitVec disp)
        | some (.addrSum b idx sh disp) =>
          if Nat.beq sh 0 && disp == 0#64 then none
          else (AddrScale.ofShift? sh).map fun sc => (some b, idx, sc, Int64.ofBitVec disp)
        | _ => none) = some (base?, idx, sc, disp)) :
    ∃ vi : BitVec 64, ⟨i64, vi, idx⟩ ∈ G ∧ ∃ vb : BitVec 64,
      (∀ b, base? = some b → ⟨i64, vb, b⟩ ∈ G) ∧
      rv = (if base?.isSome then vb else 0#64) + (vi <<< sc.shift) + disp.toBitVec := by
  have h' : (match defs.find? x with
      | some (.addrSum b idx 0 d) => some (some b, idx, .s1, Int64.ofBitVec (d + c))
      | _ =>
        match recordAddVarImm defs x c with
        | .scaleOff idx sh disp =>
          if Nat.beq sh 0 then none
          else (AddrScale.ofShift? sh).map fun sc => (none, idx, sc, Int64.ofBitVec disp)
        | .addrSum b idx sh disp =>
          if Nat.beq sh 0 && disp == 0#64 then none
          else (AddrScale.ofShift? sh).map fun sc => (some b, idx, sc, Int64.ofBitVec disp)
        | _ => none) = some (base?, idx, sc, disp) := by
    cases hdx : defs.find? x with
    | none =>
      rw [hdx] at h
      cases hrec : recordAddVarImm defs x c <;> simp only [hrec] at h <;> exact h
    | some d =>
      rw [hdx] at h
      cases d with
      | addrSum b0 i0 sh0 d0 =>
        cases sh0 with
        | zero => exact h
        | succ _ =>
          cases hrec : recordAddVarImm defs x c <;> simp only [hrec] at h <;> exact h
      | _ =>
        cases hrec : recordAddVarImm defs x c <;> simp only [hrec] at h <;> exact h
  exact extractLea64_addImm hdefs hmx hrv h'

private theorem recordAddVarVar_imm_left {defs : Trie DefFact} {x y : Nat} {cx : BitVec 64}
    (hx : defs.find? x = some (.imm64 cx)) :
    recordAddVarVar defs x y = recordAddVarImm defs y cx := by
  unfold recordAddVarVar; rw [hx]

private theorem recordAddVarVar_imm_right {defs : Trie DefFact} {x y : Nat} {cy : BitVec 64}
    (hx : ∀ c, defs.find? x ≠ some (.imm64 c)) (hy : defs.find? y = some (.imm64 cy)) :
    recordAddVarVar defs x y = recordAddVarImm defs x cy := by
  unfold recordAddVarVar; rw [hy]
  cases h1 : defs.find? x with
  | none => rfl
  | some d1 => cases d1 <;> (try exact absurd h1 (hx _)) <;> rfl

private theorem recordAddVarVar_eq_comb {defs : Trie DefFact} {x y : Nat}
    (hx : ∀ c, defs.find? x ≠ some (.imm64 c))
    (hy : ∀ c, defs.find? y ≠ some (.imm64 c)) :
    recordAddVarVar defs x y =
      ((defs.find? x).bind (recordAddScale defs · (defs.find? y) y) <|>
       (defs.find? y).bind (recordAddScale defs · (defs.find? x) x) <|>
       (defs.find? x).bind (recordAddBase · y (defs.find? y)) <|>
       (defs.find? y).bind (recordAddBase · x (defs.find? x))).getD (.addrSum x y 0 0) := by
  unfold recordAddVarVar
  cases h1 : defs.find? x with
  | none =>
    cases h2 : defs.find? y with
    | none => rfl
    | some d2 => cases d2 <;> (try exact absurd h2 (hy _)) <;> rfl
  | some d1 =>
    cases d1 <;> (try exact absurd h1 (hx _)) <;> cases h2 : defs.find? y with
    | none => rfl
    | some d2 => cases d2 <;> (try exact absurd h2 (hy _)) <;> rfl

private theorem extractLea64_recAddVarImm {G : VCtx} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d) {x : Nat} {vx c rv : BitVec 64}
    (hmx : ⟨i64, vx, x⟩ ∈ G) (hrv : rv = vx + c)
    {base? : Option Nat} {idx : Nat} {sc : AddrScale} {disp : Int64}
    (h : (match some (recordAddVarImm defs x c) with
      | some (.scaleOff idx sh disp) =>
        if Nat.beq sh 0 then none
        else (AddrScale.ofShift? sh).map fun sc => (none, idx, sc, Int64.ofBitVec disp)
      | some (.addrSum b idx sh disp) =>
        if Nat.beq sh 0 && disp == 0#64 then none
        else (AddrScale.ofShift? sh).map fun sc => (some b, idx, sc, Int64.ofBitVec disp)
      | _ => none) = some (base?, idx, sc, disp)) :
    ∃ vi : BitVec 64, ⟨i64, vi, idx⟩ ∈ G ∧ ∃ vb : BitVec 64,
      (∀ b, base? = some b → ⟨i64, vb, b⟩ ∈ G) ∧
      rv = (if base?.isSome then vb else 0#64) + (vi <<< sc.shift) + disp.toBitVec := by
  cases hdx : defs.find? x with
  | none => simp [recordAddVarImm, hdx] at h
  | some d =>
    have hxok := hdefs x d hdx
    cases d with
    | imm64 _ | addImm64 _ _ | andVarVar _ _ _ | andVarImm _ _ _ | binVarVar _ _ _ _
    | binVarImm _ _ _ _ | shlVarImm _ _ _ | sextVar _ _ _ | zextVar _ _ _
    | cmpZeroVar _ _ _ | testBitVar _ _ _ _ | shiftVarImm _ _ _ _ | negVar _ _ =>
      simp [recordAddVarImm, hdx] at h
    | scaleOff idx0 sh0 d0 =>
      simp only [recordAddVarImm, hdx] at h
      split at h; · cases h
      obtain ⟨sc0, hsc, he⟩ := Option.map_eq_some_iff.mp h; cases he
      obtain ⟨vi, hi, hvx⟩ := hxok vx hmx
      exact ⟨vi, hi, 0#64, by simp, by
        simp [hrv, hvx, addrScale_ofShift_eq hsc, BitVec.add_assoc]⟩
    | addrSum b0 idx0 sh0 d0 =>
      cases sh0 with
      | zero => simp [recordAddVarImm, hdx] at h
      | succ _ =>
        simp only [recordAddVarImm, hdx, Nat.beq_eq, Nat.add_one_ne_zero, ↓reduceIte] at h
        obtain ⟨sc0, hsc, he⟩ := Option.map_eq_some_iff.mp h; cases he
        obtain ⟨vb, vi, hb, hi, hvx⟩ := hxok vx hmx
        exact ⟨vi, hi, vb, fun _ hb' => by cases hb'; exact hb, by
          simp [hrv, hvx, addrScale_ofShift_eq hsc, BitVec.add_assoc]⟩

theorem extractLea64_ok {G : VCtx} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d)
    {sig : List Ty} {code : OpCode sig [.bits 64]}
    {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    (hrel : TRel (ArgRel G) args₁ args) {P : Tup Val [.bits 64] → Prop}
    (hwp : code.wp (vals args₁) P) {base? : Option Nat} {idx : Nat} {sc : AddrScale} {disp : Int64}
    (hext : extractLea64 defs code args = some (base?, idx, sc, disp)) :
    ∃ rv vi : BitVec 64, P (rv, ()) ∧ ⟨i64, vi, idx⟩ ∈ G ∧
      ∃ vb : BitVec 64, (∀ b, base? = some b → ⟨i64, vb, b⟩ ∈ G) ∧
        rv = (if base?.isSome then vb else 0#64) + (vi <<< sc.shift) + disp.toBitVec := by
  have hb64 : Nat.beq 64 64 = true := rfl
  cases code with
  | add =>
    rcases args with ⟨a, b, ⟨⟩⟩
    cases a with
    | var x =>
      cases b with
      | imm c =>
        rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
        cases h1 with | var hmx => cases h2 with | imm =>
        simp only [OpCode.wp_add, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
          ite_false] at hwp
        simp only [extractLea64, recordDef, hb64, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, BitVec.setWidth_eq] at hext
        obtain ⟨vi, hi, vb, hvb, hr⟩ := extractLea64_some_addImm hdefs hmx rfl hext
        exact ⟨_, vi, hwp, hi, vb, hvb, hr⟩
      | var y =>
        rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
        cases h1 with | var hmx => cases h2 with | var hmy =>
        simp only [OpCode.wp_add, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
          ite_false] at hwp
        simp only [extractLea64, recordDef, hb64, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte] at hext
        have haux := fun df hdf h => extractLea64_varVar_aux (df := df) hdefs hmx hmy
          (base? := base?) (idx := idx) (sc := sc) (disp := disp)
          (fun df h => by
            obtain ⟨dx, hdx, hk⟩ := Option.bind_eq_some_iff.mp h
            unfold recordAddScale at hk
            cases dx with
            | scaleOff idx0 sh0 d1 =>
              dsimp only at hk; split at hk; · cases hdy : defs.find? y with
                | some dy => cases dy with
                  | addImm64 b d2 =>
                    simp only [hdy] at hk
                    by_cases hc : isScaledAddrSum defs b = true
                    · simp only [hc, ↓reduceIte, Option.some.injEq] at hk; subst hk
                      obtain ⟨vi, hi, hvx⟩ := hdefs x _ hdx _ hmx
                      exact ⟨y, idx0, sh0, d1, rfl, _, vi, hmy, hi, by rw [hvx]; ac_rfl⟩
                    · simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hk
                      subst hk
                      obtain ⟨vi, hi, hvx⟩ := hdefs x _ hdx _ hmx
                      obtain ⟨vb, hb, hvy⟩ := (hdefs y _ hdy).2 _ hmy
                      exact ⟨b, idx0, sh0, d1 + d2, rfl, vb, vi, hb, hi, by
                        rw [hvx, hvy]; ac_rfl⟩
                  | _ =>
                    simp only [hdy, Option.some.injEq] at hk; subst hk
                    obtain ⟨vi, hi, hvx⟩ := hdefs x _ hdx _ hmx
                    exact ⟨y, idx0, sh0, d1, rfl, _, vi, hmy, hi, by rw [hvx]; ac_rfl⟩
                | none =>
                  simp only [hdy, Option.some.injEq] at hk; subst hk
                  obtain ⟨vi, hi, hvx⟩ := hdefs x _ hdx _ hmx
                  exact ⟨y, idx0, sh0, d1, rfl, _, vi, hmy, hi, by rw [hvx]; ac_rfl⟩
              · simp at hk
            | _ => simp at hk)
          (fun df h => by
            obtain ⟨dx, hdx, hk⟩ := Option.bind_eq_some_iff.mp h
            unfold recordAddBase at hk
            cases dx with
            | addImm64 b d1 =>
              cases hdy : defs.find? y with
              | some dy => cases dy with
                | addImm64 b2 d2 =>
                  simp only [hdy, Option.some.injEq] at hk; subst hk
                  obtain ⟨vb, hb, hvx⟩ := (hdefs x _ hdx).2 _ hmx
                  obtain ⟨vb2, hb2, hvy⟩ := (hdefs y _ hdy).2 _ hmy
                  exact ⟨b, b2, 0, d1 + d2, rfl, vb, vb2, hb, hb2, by
                    simp only [BitVec.shiftLeft_zero]; rw [hvx, hvy]; ac_rfl⟩
                | _ =>
                  simp only [hdy, Option.some.injEq] at hk; subst hk
                  obtain ⟨vb, hb, hvx⟩ := (hdefs x _ hdx).2 _ hmx
                  exact ⟨b, y, 0, d1, rfl, vb, _, hb, hmy, by
                    simp only [BitVec.shiftLeft_zero]; rw [hvx]; ac_rfl⟩
              | none =>
                simp only [hdy, Option.some.injEq] at hk; subst hk
                obtain ⟨vb, hb, hvx⟩ := (hdefs x _ hdx).2 _ hmx
                exact ⟨b, y, 0, d1, rfl, vb, _, hb, hmy, by
                  simp only [BitVec.shiftLeft_zero]; rw [hvx]; ac_rfl⟩
            | _ => simp at hk) hdf h
        rename_i vx vy
        by_cases hx : ∃ cx, defs.find? x = some (.imm64 cx)
        · obtain ⟨cx, hdx⟩ := hx
          have hcx : vx = cx := hdefs x _ hdx vx hmx
          rw [recordAddVarVar_imm_left hdx] at hext
          obtain ⟨vi, hi, vb, hvb, hr⟩ :=
            extractLea64_recAddVarImm (rv := vx + vy) hdefs hmy (by rw [hcx, BitVec.add_comm]) hext
          exact ⟨_, vi, hwp, hi, vb, hvb, hr⟩
        · have hx' : ∀ c, defs.find? x ≠ some (.imm64 c) := fun c h => hx ⟨c, h⟩
          by_cases hy : ∃ cy, defs.find? y = some (.imm64 cy)
          · obtain ⟨cy, hdy⟩ := hy
            have hcy : vy = cy := hdefs y _ hdy vy hmy
            rw [recordAddVarVar_imm_right hx' hdy] at hext
            obtain ⟨vi, hi, vb, hvb, hr⟩ :=
              extractLea64_recAddVarImm (rv := vx + vy) hdefs hmx (by rw [hcy]) hext
            exact ⟨_, vi, hwp, hi, vb, hvb, hr⟩
          · have hy' : ∀ c, defs.find? y ≠ some (.imm64 c) := fun c h => hy ⟨c, h⟩
            rw [recordAddVarVar_eq_comb hx' hy'] at hext
            obtain ⟨vi, hi, vb, hvb, hr⟩ := haux _ rfl hext
            exact ⟨_, vi, hwp, hi, vb, hvb, hr⟩
    | imm c =>
      cases b with
      | imm _ => simp [extractLea64] at hext
      | var x =>
        rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
        cases h1 with | imm => cases h2 with | var hmx =>
        simp only [OpCode.wp_add, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
          ite_false] at hwp
        simp only [extractLea64, recordDef, hb64, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, BitVec.setWidth_eq] at hext
        obtain ⟨vi, hi, vb, hvb, hr⟩ :=
          extractLea64_some_addImm hdefs hmx (BitVec.add_comm _ _) hext
        exact ⟨_, vi, hwp, hi, vb, hvb, hr⟩
  | sub =>
    rcases args with ⟨a, b, ⟨⟩⟩
    cases a with
    | imm _ => simp [extractLea64] at hext
    | var x =>
      cases b with
      | var _ => simp [extractLea64] at hext
      | imm c =>
        rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
        cases h1 with | var hmx => cases h2 with | imm =>
        simp only [OpCode.wp_sub, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
          ite_false] at hwp
        simp only [extractLea64, recordDef, hb64, ↓reduceIte, BitVec.setWidth_eq] at hext
        simp only [BitVec.sub_eq_add_neg] at hext
        obtain ⟨vi, hi, vb, hvb, hr⟩ :=
          extractLea64_some_addImm hdefs hmx (BitVec.sub_eq_add_neg _ _) hext
        exact ⟨_, vi, hwp, hi, vb, hvb, hr⟩
  | shl =>
    rcases args with ⟨a, b, ⟨⟩⟩
    cases a with
    | imm _ => simp [extractLea64] at hext
    | var x =>
      cases b with
      | var _ => simp [extractLea64] at hext
      | imm k =>
        rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
        cases h1 with | var hmx => cases h2 with | imm =>
        rename_i vx
        simp only [OpCode.wp_shl, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
          ite_false] at hwp
        simp only [extractLea64] at hext
        cases hdx : defs.find? x with
        | none => simp [hdx] at hext
        | some d =>
          rw [hdx] at hext
          have hxok := hdefs x d hdx
          cases d with
          | addImm64 b0 d0 =>
            by_cases hk : k.toNat < 64
            · have hbk : Nat.blt k.toNat 64 = true := by simpa [Nat.blt_eq] using hk
              simp only [recordDef, hb64, ↓reduceIte, hdx, hbk,
                Bool.not_true, Bool.false_eq_true] at hext
              split at hext; · cases hext
              obtain ⟨sc0, hsc, he⟩ := Option.map_eq_some_iff.mp hext; cases he
              obtain ⟨vb, hb, hvx⟩ := hxok.2 vx hmx
              rw [Nat.mod_eq_of_lt hk] at hwp
              exact ⟨_, vb, hwp, hb, 0#64, by simp, by
                simp [hvx, addrScale_ofShift_eq hsc, Int64.toBitVec_ofBitVec]⟩
            · have hbk : Nat.blt k.toNat 64 = false :=
                Bool.eq_false_iff.mpr (by simpa [Nat.blt_eq] using hk)
              simp [recordDef, hbk] at hext
          | scaleOff idx0 sh0 d0 =>
            by_cases hk : k.toNat < 64
            · have hbk : Nat.blt k.toNat 64 = true := by simpa [Nat.blt_eq] using hk
              by_cases hsk : sh0 + k.toNat < 64
              · have hbsk : Nat.blt (sh0 + k.toNat) 64 = true := by simpa [Nat.blt_eq] using hsk
                simp only [recordDef, hb64, ↓reduceIte, hdx, hbk, hbsk,
                  Bool.not_true, Bool.false_eq_true] at hext
                split at hext; · cases hext
                obtain ⟨sc0, hsc, he⟩ := Option.map_eq_some_iff.mp hext; cases he
                obtain ⟨vi, hi, hvx⟩ := hxok vx hmx
                rw [Nat.mod_eq_of_lt hk] at hwp
                exact ⟨_, vi, hwp, hi, 0#64, by simp, by
                  simp [hvx, bv_shiftLeft_shiftLeft, addrScale_ofShift_eq hsc,
                    Int64.toBitVec_ofBitVec]⟩
              · have hbsk : Nat.blt (sh0 + k.toNat) 64 = false :=
                  Bool.eq_false_iff.mpr (by simpa [Nat.blt_eq] using hsk)
                simp [recordDef, hdx, hbk, hbsk] at hext
            · have hbk : Nat.blt k.toNat 64 = false :=
                Bool.eq_false_iff.mpr (by simpa [Nat.blt_eq] using hk)
              simp [recordDef, hbk] at hext
          | _ => simp at hext
  | _ => simp [extractLea64] at hext

private theorem asScale32_ok {G : VCtx} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d) {v idx : Nat}
    {sc : AddrScale} {d : BitVec 32} (h : asScale32 defs v = some (idx, sc, d)) :
    ∀ vv : BitVec 32, ⟨.bits 32, vv, v⟩ ∈ G →
      ∃ vi : BitVec 32, ⟨.bits 32, vi, idx⟩ ∈ G ∧ vv = (vi <<< sc.shift) + d := by
  intro vv hmv
  unfold asScale32 at h
  cases hdv : defs.find? v with
  | none => simp [hdv] at h
  | some df =>
    rw [hdv] at h
    have hvok := hdefs v df hdv
    cases df with
    | shlVarImm w0 idx0 sh0 =>
      by_cases hw : w0 = 32
      · subst hw; simp only at h
        by_cases hsh : sh0 = 0
        · simp [hsh] at h
        · have hb : Nat.beq sh0 0 = false :=
            Bool.eq_false_iff.mpr (by simpa [Nat.beq_eq] using hsh)
          simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨sc0, hsc, he⟩ := Option.map_eq_some_iff.mp h; cases he
          obtain ⟨_, _, hok⟩ := hvok
          obtain ⟨vi, hi, hvv⟩ := hok vv hmv
          exact ⟨vi, hi, by simp [hvv, addrScale_ofShift_eq hsc]⟩
      · simp [hw] at h
    | binVarImm w0 op x c =>
      cases op with
      | add | sub =>
        by_cases hw : w0 = 32
        · subst hw; simp only at h
          cases hdx : defs.find? x with
          | none => simp [hdx] at h
          | some dx =>
            rw [hdx] at h
            cases dx with
            | shlVarImm w1 idx0 sh0 =>
              by_cases hw1 : w1 = 32
              · subst hw1; simp only at h
                by_cases hsh : sh0 = 0
                · simp [hsh] at h
                · have hb : Nat.beq sh0 0 = false :=
                    Bool.eq_false_iff.mpr (by simpa [Nat.beq_eq] using hsh)
                  simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
                  obtain ⟨sc0, hsc, he⟩ := Option.map_eq_some_iff.mp h; cases he
                  obtain ⟨_, hokv⟩ := hvok
                  obtain ⟨vx, hx, hvv⟩ := hokv vv hmv
                  obtain ⟨_, _, hokx⟩ := hdefs x _ hdx
                  obtain ⟨vi, hi, hvx⟩ := hokx vx hx
                  exact ⟨vi, hi, by
                    simp [hvv, hvx, RmwOp.eval, addrScale_ofShift_eq hsc, BitVec.sub_eq_add_neg]⟩
              · simp [hw1] at h
            | _ => simp at h
        · simp [hw] at h
      | _ => simp at h
    | _ => simp at h

private theorem asBaseImm32_ok {G : VCtx} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d) {v rb : Nat} {d : BitVec 32}
    (h : asBaseImm32 defs v = (rb, d)) :
    ∀ vv : BitVec 32, ⟨.bits 32, vv, v⟩ ∈ G →
      ∃ vb : BitVec 32, ⟨.bits 32, vb, rb⟩ ∈ G ∧ vv = vb + d := by
  intro vv hmv
  unfold asBaseImm32 at h
  cases hdv : defs.find? v with
  | none => rw [hdv] at h; cases h; exact ⟨vv, hmv, by simp⟩
  | some df =>
    rw [hdv] at h
    have hvok := hdefs v df hdv
    cases df with
    | binVarImm w0 op x c =>
      cases op with
      | add | sub =>
        by_cases hw : w0 = 32
        · subst hw; simp only at h; cases h
          obtain ⟨_, hok⟩ := hvok
          obtain ⟨vb, hb, hvv⟩ := hok vv hmv
          exact ⟨vb, hb, by simp [hvv, RmwOp.eval, BitVec.sub_eq_add_neg]⟩
        · split at h
          · exfalso; apply hw; injections
          · exfalso; apply hw; injections
          · cases h; exact ⟨vv, hmv, by simp⟩
      | _ =>
      split at h <;> first | (exfalso; injections; done) | (cases h; exact ⟨vv, hmv, by simp⟩)
    | _ =>
      split at h <;> first | (exfalso; injections; done) | (cases h; exact ⟨vv, hmv, by simp⟩)

theorem extractLea32_ok {G : VCtx} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d)
    {sig : List Ty} {code : OpCode sig [.bits 32]}
    {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    (hrel : TRel (ArgRel G) args₁ args) {P : Tup Val [.bits 32] → Prop}
    (hwp : code.wp (vals args₁) P) {base? : Option Nat} {idx : Nat} {sc : AddrScale} {disp : Int64}
    (hext : extractLea32 defs code args = some (base?, idx, sc, disp)) :
    ∃ rv vi : BitVec 32, P (rv, ()) ∧ ⟨.bits 32, vi, idx⟩ ∈ G ∧
      ∃ vb : BitVec 32, (∀ b, base? = some b → ⟨.bits 32, vb, b⟩ ∈ G) ∧
        rv = (if base?.isSome then vb else 0#32) +
          (vi <<< sc.shift) + disp.toBitVec.setWidth 32 := by
  have addImmAux : ∀ (x : Nat) (vx c : BitVec 32) (isSub : Bool),
      ⟨.bits 32, vx, x⟩ ∈ G →
      (if isSub then extractLea32 defs (.sub (.bits 32)) (.var x, .imm c, ())
       else extractLea32 defs (.add (.bits 32)) (.var x, .imm c, ())) =
        some (base?, idx, sc, disp) →
      ∃ vi : BitVec 32, ⟨.bits 32, vi, idx⟩ ∈ G ∧ ∃ vb : BitVec 32,
        (∀ b, base? = some b → ⟨.bits 32, vb, b⟩ ∈ G) ∧
        (if isSub then vx - c else vx + c) =
          (if base?.isSome then vb else 0#32) + (vi <<< sc.shift) + disp.toBitVec.setWidth 32 := by
    intro x vx c isSub hmx h
    cases isSub <;> (
      simp only [Bool.false_eq_true, ↓reduceIte, extractLea32] at h
      cases hs : asScale32 defs x with
      | some p =>
        rw [hs] at h; rcases p with ⟨idx0, sc0, d0⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl, rfl, rfl⟩
        obtain ⟨vi, hi, hvx⟩ := asScale32_ok hdefs hs vx hmx
        refine ⟨vi, hi, 0#32, by simp, ?_⟩
        simp [hvx, Int64.toBitVec_ofBitVec, setWidth_32_signExtend_64,
          BitVec.sub_eq_add_neg, BitVec.add_assoc]
      | none =>
        rw [hs] at h
        cases hdx : defs.find? x with
        | none => simp [hdx] at h
        | some dx =>
          rw [hdx] at h
          cases dx with
          | binVarVar w0 op a b =>
            cases op with
            | add =>
              by_cases hw : w0 = 32
              · subst hw; simp only at h
                obtain ⟨_, hok⟩ := hdefs x _ hdx
                obtain ⟨va, vb', ha, hb, hvx⟩ := hok vx hmx
                simp only [RmwOp.eval] at hvx
                cases hsa : asScale32 defs a with
                | some p =>
                  rw [hsa] at h; rcases p with ⟨idx0, sc0, d0⟩
                  rcases hbr : asBaseImm32 defs b with ⟨rb, d2⟩
                  rw [hbr] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  rcases h with ⟨rfl, rfl, rfl, rfl⟩
                  obtain ⟨vi, hi, hva⟩ := asScale32_ok hdefs hsa va ha
                  obtain ⟨vb, hmb, hvb⟩ := asBaseImm32_ok hdefs hbr vb' hb
                  refine ⟨vi, hi, vb, fun _ hb' => by cases hb'; exact hmb, ?_⟩
                  simp [hvx, hva, hvb, Int64.toBitVec_ofBitVec, setWidth_32_signExtend_64,
                    BitVec.sub_eq_add_neg]; ac_rfl
                | none =>
                  rw [hsa] at h
                  cases hsb : asScale32 defs b with
                  | some p =>
                    rw [hsb] at h; rcases p with ⟨idx0, sc0, d0⟩
                    rcases har : asBaseImm32 defs a with ⟨rb, d2⟩
                    rw [har] at h
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    rcases h with ⟨rfl, rfl, rfl, rfl⟩
                    obtain ⟨vi, hi, hvb⟩ := asScale32_ok hdefs hsb vb' hb
                    obtain ⟨vb, hma, hva⟩ := asBaseImm32_ok hdefs har va ha
                    refine ⟨vi, hi, vb, fun _ hb' => by cases hb'; exact hma, ?_⟩
                    simp [hvx, hva, hvb, Int64.toBitVec_ofBitVec, setWidth_32_signExtend_64,
                      BitVec.sub_eq_add_neg]; ac_rfl
                  | none =>
                    rw [hsb] at h
                    rcases har : asBaseImm32 defs a with ⟨ra, da⟩
                    rcases hbr : asBaseImm32 defs b with ⟨rb, db⟩
                    rw [har, hbr] at h
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    rcases h with ⟨rfl, rfl, rfl, rfl⟩
                    obtain ⟨va', hma, hva⟩ := asBaseImm32_ok hdefs har va ha
                    obtain ⟨vb', hmb, hvb⟩ := asBaseImm32_ok hdefs hbr vb' hb
                    refine ⟨vb', hmb, va', fun _ hb' => by cases hb'; exact hma, ?_⟩
                    simp [hvx, hva, hvb, AddrScale.shift, Int64.toBitVec_ofBitVec,
                      setWidth_32_signExtend_64, BitVec.sub_eq_add_neg]; ac_rfl
              · simp [hw] at h
            | _ => simp at h
          | _ => simp at h)
  cases code with
  | add =>
    rcases args with ⟨a, b, ⟨⟩⟩
    cases a with
    | var x =>
      cases b with
      | imm c =>
        rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
        cases h1 with | var hmx => cases h2 with | imm =>
        simp only [OpCode.wp_add, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
          ite_false] at hwp
        obtain ⟨vi, hi, vb, hvb, hr⟩ := addImmAux x _ c false hmx (by
          simpa only [Bool.false_eq_true, ↓reduceIte] using hext)
        exact ⟨_, vi, hwp, hi, vb, hvb, hr⟩
      | var y =>
        rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
        cases h1 with | var hmx => cases h2 with | var hmy =>
        rename_i vx vy
        simp only [OpCode.wp_add, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
          ite_false] at hwp
        simp only [extractLea32] at hext
        cases hsx : asScale32 defs x with
        | some p =>
          rw [hsx] at hext; rcases p with ⟨idx0, sc0, d1⟩
          rcases hby : asBaseImm32 defs y with ⟨rb, d2⟩
          rw [hby] at hext
          simp only [Option.some.injEq, Prod.mk.injEq] at hext
          rcases hext with ⟨rfl, rfl, rfl, rfl⟩
          obtain ⟨vi, hi, hvx⟩ := asScale32_ok hdefs hsx vx hmx
          obtain ⟨vb, hmb, hvy⟩ := asBaseImm32_ok hdefs hby vy hmy
          exact ⟨_, vi, hwp, hi, vb, fun _ hb' => by cases hb'; exact hmb, by
            simp [hvx, hvy, Int64.toBitVec_ofBitVec, setWidth_32_signExtend_64]; ac_rfl⟩
        | none =>
          rw [hsx] at hext
          cases hsy : asScale32 defs y with
          | some p =>
            rw [hsy] at hext; rcases p with ⟨idx0, sc0, d1⟩
            rcases hbx : asBaseImm32 defs x with ⟨rb, d2⟩
            rw [hbx] at hext
            simp only [Option.some.injEq, Prod.mk.injEq] at hext
            rcases hext with ⟨rfl, rfl, rfl, rfl⟩
            obtain ⟨vi, hi, hvy⟩ := asScale32_ok hdefs hsy vy hmy
            obtain ⟨vb, hma, hvx⟩ := asBaseImm32_ok hdefs hbx vx hmx
            exact ⟨_, vi, hwp, hi, vb, fun _ hb' => by cases hb'; exact hma, by
              simp [hvx, hvy, Int64.toBitVec_ofBitVec, setWidth_32_signExtend_64]; ac_rfl⟩
          | none =>
            rw [hsy] at hext
            rcases hbx : asBaseImm32 defs x with ⟨rx, dx⟩
            rcases hby : asBaseImm32 defs y with ⟨ry, dy⟩
            rw [hbx, hby] at hext; dsimp only at hext
            split at hext; · simp at hext
            simp only [Option.some.injEq, Prod.mk.injEq] at hext
            rcases hext with ⟨rfl, rfl, rfl, rfl⟩
            obtain ⟨vx', hma, hvx⟩ := asBaseImm32_ok hdefs hbx vx hmx
            obtain ⟨vy', hmb, hvy⟩ := asBaseImm32_ok hdefs hby vy hmy
            exact ⟨_, vy', hwp, hmb, vx', fun _ hb' => by cases hb'; exact hma, by
              simp [hvx, hvy, AddrScale.shift, Int64.toBitVec_ofBitVec,
                setWidth_32_signExtend_64]; ac_rfl⟩
    | imm c =>
      cases b with
      | imm _ => simp [extractLea32] at hext
      | var x =>
        rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
        cases h1 with | imm => cases h2 with | var hmx =>
        simp only [OpCode.wp_add, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
          ite_false] at hwp
        obtain ⟨vi, hi, vb, hvb, hr⟩ := addImmAux x _ c false hmx (by
          simp only [Bool.false_eq_true, ↓reduceIte, extractLea32]
          simpa only [extractLea32] using hext)
        exact ⟨_, vi, hwp, hi, vb, hvb, by rw [BitVec.add_comm]; exact hr⟩
  | sub =>
    rcases args with ⟨a, b, ⟨⟩⟩
    cases a with
    | imm _ => simp [extractLea32] at hext
    | var x =>
      cases b with
      | var _ => simp [extractLea32] at hext
      | imm c =>
        rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
        cases h1 with | var hmx => cases h2 with | imm =>
        simp only [OpCode.wp_sub, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
          ite_false] at hwp
        obtain ⟨vi, hi, vb, hvb, hr⟩ := addImmAux x _ c true hmx (by
          simpa only [↓reduceIte] using hext)
        exact ⟨_, vi, hwp, hi, vb, hvb, hr⟩
  | shl =>
    rcases args with ⟨a, b, ⟨⟩⟩
    cases a with
    | imm _ => simp [extractLea32] at hext
    | var x =>
      cases b with
      | var _ => simp [extractLea32] at hext
      | imm k =>
        rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
        cases h1 with | var hmx => cases h2 with | imm =>
        rename_i vx
        simp only [OpCode.wp_shl, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
          ite_false] at hwp
        simp only [extractLea32] at hext
        split at hext; · simp at hext
        rename_i hnk; have hk : k.toNat < 32 := by simpa [Nat.blt_eq] using hnk
        rw [Nat.mod_eq_of_lt hk] at hwp
        cases hdx : defs.find? x with
        | none => simp [hdx] at hext
        | some df =>
          rw [hdx] at hext
          have hxok := hdefs x df hdx
          cases df with
          | binVarImm w0 op b0 d0 =>
            cases op with
            | add =>
              by_cases hw : w0 = 32
              · subst hw; simp only at hext
                split at hext; · cases hext
                obtain ⟨sc0, hsc, he⟩ := Option.map_eq_some_iff.mp hext; cases he
                obtain ⟨_, hok⟩ := hxok
                obtain ⟨vb, hb, hvx⟩ := hok vx hmx
                exact ⟨_, vb, hwp, hb, 0#32, by simp, by
                  simp [hvx, RmwOp.eval, addrScale_ofShift_eq hsc,
                    Int64.toBitVec_ofBitVec, setWidth_32_signExtend_64]⟩
              · simp [hw] at hext
            | sub =>
              by_cases hw : w0 = 32
              · subst hw; simp only at hext
                split at hext; · cases hext
                obtain ⟨sc0, hsc, he⟩ := Option.map_eq_some_iff.mp hext; cases he
                obtain ⟨_, hok⟩ := hxok
                obtain ⟨vb, hb, hvx⟩ := hok vx hmx
                exact ⟨_, vb, hwp, hb, 0#32, by simp, by
                  simp [hvx, RmwOp.eval, BitVec.sub_eq_add_neg,
                    addrScale_ofShift_eq hsc, Int64.toBitVec_ofBitVec, setWidth_32_signExtend_64]⟩
              · simp [hw] at hext
            | _ => simp at hext
          | shlVarImm w0 idx0 sh0 =>
            by_cases hw : w0 = 32
            · subst hw; simp only at hext
              split at hext; · cases hext
              obtain ⟨sc0, hsc, he⟩ := Option.map_eq_some_iff.mp hext; cases he
              obtain ⟨_, _, hok⟩ := hxok
              obtain ⟨vi, hi, hvx⟩ := hok vx hmx
              exact ⟨_, vi, hwp, hi, 0#32, by simp, by
                simp [hvx, bv_shiftLeft_shiftLeft, addrScale_ofShift_eq hsc]⟩
            · simp [hw] at hext
          | _ => simp at hext
  | _ => simp [extractLea32] at hext

private theorem asZext32_ok {G : VCtx} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d) {v idx : Nat}
    (h : asZext32? defs v = some idx) :
    ∀ vv : BitVec 64, ⟨i64, vv, v⟩ ∈ G →
      ∃ vi : BitVec 32, ⟨.bits 32, vi, idx⟩ ∈ G ∧ vv = vi.setWidth 64 := by
  intro vv hmv
  unfold asZext32? at h
  cases hdv : defs.find? v with
  | none => simp [hdv] at h
  | some df =>
    rw [hdv] at h
    cases df with
    | zextVar m n idx0 =>
      dsimp only at h; split at h
      · rename_i hc; simp only [Bool.and_eq_true, Nat.beq_eq] at hc
        rcases hc with ⟨rfl, rfl⟩
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨_, _, _, hok⟩ := hdefs v _ hdv
        obtain ⟨vi32, hmi, hvv⟩ := hok vv hmv
        exact ⟨vi32, hmi, by simp [hvv, BitVec.zeroExtend]⟩
      · simp at h
    | _ => simp at h

theorem zextAddrSumVar_ok {G : VCtx} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d) {b i sh rb ridx zv : Nat}
    {d : BitVec 64} {vb0 vi0 : BitVec 64} (hb0 : ⟨i64, vb0, b⟩ ∈ G) (hi0 : ⟨i64, vi0, i⟩ ∈ G)
    (h : zextAddrSumVar? defs b i sh = some (rb, ridx, zv)) :
    ∃ (vb : BitVec 64) (vi : BitVec 32),
      ⟨i64, vb, rb⟩ ∈ G ∧ ⟨.bits 32, vi, ridx⟩ ∈ G ∧
      vb0 + (vi0 <<< sh) + d = vb + (vi.setWidth 64 <<< sh) + d := by
  unfold zextAddrSumVar? at h
  cases hi : asZext32? defs i with
  | some idx =>
    rw [hi] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    obtain ⟨vi, hmi, hvi⟩ := asZext32_ok hdefs hi vi0 hi0
    exact ⟨vb0, vi, hb0, hmi, by simp [hvi]⟩
  | none =>
    rw [hi] at h; dsimp only at h
    split at h
    · rename_i hsh0; obtain rfl : sh = 0 := Nat.beq_eq.mp hsh0
      obtain ⟨idx, hbz, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he; rcases he with ⟨rfl, rfl, rfl⟩
      obtain ⟨vb, hmb, hvb⟩ := asZext32_ok hdefs hbz vb0 hb0
      exact ⟨vi0, vb, hi0, hmb, by simp [hvb, BitVec.add_comm]⟩
    · simp at h

private theorem zextScalePart_ok {G : VCtx} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d) {v idx sh : Nat} {d : BitVec 64}
    (h : zextScalePart? defs v = some (idx, sh, d)) :
    ∀ vv : BitVec 64, ⟨i64, vv, v⟩ ∈ G →
      ∃ vi : BitVec 32, ⟨.bits 32, vi, idx⟩ ∈ G ∧ vv = (vi.setWidth 64 <<< sh) + d := by
  intro vv hmv
  unfold zextScalePart? at h
  cases hdv : defs.find? v with
  | none => simp [hdv] at h
  | some df =>
    rw [hdv] at h
    have hvok := hdefs v df hdv
    cases df with
    | zextVar m n idx0 =>
      dsimp only at h; split at h
      · rename_i hc; simp only [Bool.and_eq_true, Nat.beq_eq] at hc
        rcases hc with ⟨rfl, rfl⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        obtain ⟨_, _, _, hok⟩ := hvok
        obtain ⟨vi32, hi, hvv⟩ := hok vv hmv
        exact ⟨vi32, hi, by simp [hvv, BitVec.zeroExtend]⟩
      · simp at h
    | addImm64 z d0 =>
      obtain ⟨idx0, hdz, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he; rcases he with ⟨rfl, rfl, rfl⟩
      obtain ⟨vz, hz, hvv⟩ := hvok.2 vv hmv
      obtain ⟨vi32, hi, hvz⟩ := asZext32_ok hdefs hdz vz hz
      exact ⟨vi32, hi, by simp [hvv, hvz]⟩
    | scaleOff z sh0 d0 =>
      obtain ⟨idx0, hdz, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he; rcases he with ⟨rfl, rfl, rfl⟩
      obtain ⟨vz, hz, hvv⟩ := hvok vv hmv
      obtain ⟨vi32, hi, hvz⟩ := asZext32_ok hdefs hdz vz hz
      exact ⟨vi32, hi, by simp [hvv, hvz]⟩
    | _ => simp at h

private theorem baseDispPart_ok {G : VCtx} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d) {v rb : Nat} {d : BitVec 64}
    (h : baseDispPart defs v = (rb, d)) :
    ∀ vv : BitVec 64, ⟨i64, vv, v⟩ ∈ G →
      ∃ vb : BitVec 64, ⟨i64, vb, rb⟩ ∈ G ∧ vv = vb + d := by
  intro vv hmv
  unfold baseDispPart at h
  cases hdv : defs.find? v with
  | none => rw [hdv] at h; rcases h with ⟨rfl, rfl⟩; exact ⟨vv, hmv, by simp⟩
  | some df =>
    have hvok := hdefs v df hdv
    rw [hdv] at h
    cases df with
    | addImm64 b0 d0 => rcases h with ⟨rfl, rfl⟩; exact hvok.2 vv hmv
    | _ => simp at h; rcases h with ⟨rfl, rfl⟩; exact ⟨vv, hmv, by simp⟩

private theorem extractLeaZextImm_ok {G : VCtx} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d) {x : Nat} {vx cc : BitVec 64}
    (hmx : ⟨i64, vx, x⟩ ∈ G) {base? : Option Nat} {idx shift : Nat} {disp : Int64}
    (h : extractLeaZextImm defs x cc = some (base?, idx, shift, disp)) :
    ∃ vi : BitVec 32, ⟨.bits 32, vi, idx⟩ ∈ G ∧ ∃ vb : BitVec 64,
      (∀ b, base? = some b → ⟨i64, vb, b⟩ ∈ G) ∧
      vx + cc = (if base?.isSome then vb else 0#64) +
        (vi.setWidth 64 <<< shift) + disp.toBitVec := by
  unfold extractLeaZextImm at h
  have fallback : (match zextScalePart? defs x with
      | some (idx0, sh0, d0) =>
        if Nat.blt 0 sh0 then some (none, idx0, sh0, Int64.ofBitVec (d0 + cc)) else none
      | none => none) = some (base?, idx, shift, disp) →
      ∃ vi : BitVec 32, ⟨.bits 32, vi, idx⟩ ∈ G ∧ ∃ vb : BitVec 64,
        (∀ b, base? = some b → ⟨i64, vb, b⟩ ∈ G) ∧
        vx + cc = (if base?.isSome then vb else 0#64) +
          (vi.setWidth 64 <<< shift) + disp.toBitVec := by
    intro hs
    cases hsp : zextScalePart? defs x with
    | none => simp [hsp] at hs
    | some p =>
      rw [hsp] at hs; rcases p with ⟨idx0, sh0, d0⟩
      dsimp only at hs; split at hs
      · simp only [Option.some.injEq, Prod.mk.injEq] at hs
        rcases hs with ⟨rfl, rfl, rfl, rfl⟩
        obtain ⟨vi, hmi, hvx⟩ := zextScalePart_ok hdefs hsp vx hmx
        exact ⟨vi, hmi, 0#64, by simp, by
          simp [hvx, Int64.toBitVec_ofBitVec, BitVec.add_assoc]⟩
      · simp at hs
  cases hdx : defs.find? x with
  | none => rw [hdx] at h; exact fallback h
  | some df =>
    rw [hdx] at h
    cases df with
    | addrSum b i sh d =>
      obtain ⟨⟨rb, ridx, zv⟩, hz, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he; rcases he with ⟨rfl, rfl, rfl, rfl⟩
      obtain ⟨vb0, vi0, hb0, hi0, hvx⟩ := hdefs x _ hdx vx hmx
      obtain ⟨vb, vi, hmb, hmi, hsum⟩ := zextAddrSumVar_ok hdefs hb0 hi0 hz
      refine ⟨vi, hmi, vb, fun _ hb' => by cases hb'; exact hmb, ?_⟩
      simp [hvx, Int64.toBitVec_ofBitVec]
      rw [← BitVec.add_assoc, hsum]
    | _ => exact fallback h

theorem extractLeaZext64_ok {G : VCtx} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d)
    {sig : List Ty} {code : OpCode sig [.bits 64]}
    {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    (hrel : TRel (ArgRel G) args₁ args) {P : Tup Val [.bits 64] → Prop}
    (hwp : code.wp (vals args₁) P) {base? : Option Nat} {idx shift : Nat} {disp : Int64}
    (hext : extractLeaZext64 defs code args = some (base?, idx, shift, disp)) :
    ∃ (rv : BitVec 64) (vi : BitVec 32), P (rv, ()) ∧ ⟨.bits 32, vi, idx⟩ ∈ G ∧
      ∃ vb : BitVec 64, (∀ b, base? = some b → ⟨i64, vb, b⟩ ∈ G) ∧
        rv = (if base?.isSome then vb else 0#64) +
          (vi.setWidth 64 <<< shift) + disp.toBitVec := by
  cases code with
  | shl =>
    rcases args with ⟨a, b, ⟨⟩⟩
    cases a with
    | imm _ => simp [extractLeaZext64] at hext
    | var x =>
      cases b with
      | var _ => simp [extractLeaZext64] at hext
      | imm k =>
        rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
        cases h1 with | var hmx => cases h2 with | imm =>
        rename_i vx
        simp only [OpCode.wp_shl, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
          ite_false] at hwp
        simp only [extractLeaZext64] at hext
        split at hext; · simp at hext
        rename_i hnk; have hk : k.toNat < 64 := by simpa [Nat.blt_eq] using hnk
        rw [Nat.mod_eq_of_lt hk] at hwp
        cases hsp : zextScalePart? defs x with
        | none => simp [hsp] at hext
        | some p =>
          rw [hsp] at hext; rcases p with ⟨idx0, sh0, d0⟩
          dsimp only at hext; split at hext
          · simp only [Option.some.injEq, Prod.mk.injEq] at hext
            rcases hext with ⟨rfl, rfl, rfl, rfl⟩
            obtain ⟨vi, hmi, hvx⟩ := zextScalePart_ok hdefs hsp vx hmx
            exact ⟨_, vi, hwp, hmi, 0#64, by simp, by
              simp [hvx, bv_shiftLeft_shiftLeft, Int64.toBitVec_ofBitVec]⟩
          · simp at hext
  | add =>
    rcases args with ⟨a, b, ⟨⟩⟩
    cases a with
    | var x =>
      cases b with
      | var y =>
        rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
        cases h1 with | var hmx => cases h2 with | var hmy =>
        rename_i vx vy
        simp only [OpCode.wp_add, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
          ite_false] at hwp
        simp only [extractLeaZext64] at hext
        rcases orElse_eq_some hext with he1 | he2
        · cases hsx : zextScalePart? defs x with
          | none => simp [hsx] at he1
          | some p =>
            rw [hsx] at he1; rcases p with ⟨idx0, sh0, d1⟩
            rcases hby : baseDispPart defs y with ⟨rb, d2⟩
            rw [hby] at he1; simp only [Option.some.injEq, Prod.mk.injEq] at he1
            rcases he1 with ⟨rfl, rfl, rfl, rfl⟩
            obtain ⟨vi, hmi, hvx⟩ := zextScalePart_ok hdefs hsx vx hmx
            obtain ⟨vb, hmb, hvy⟩ := baseDispPart_ok hdefs hby vy hmy
            exact ⟨_, vi, hwp, hmi, vb, fun _ hb' => by cases hb'; exact hmb, by
              simp [hvx, hvy, Int64.toBitVec_ofBitVec]; ac_rfl⟩
        · cases hsy : zextScalePart? defs y with
          | none => simp [hsy] at he2
          | some p =>
            rw [hsy] at he2; rcases p with ⟨idx0, sh0, d1⟩
            rcases hbx : baseDispPart defs x with ⟨rb, d2⟩
            rw [hbx] at he2; simp only [Option.some.injEq, Prod.mk.injEq] at he2
            rcases he2 with ⟨rfl, rfl, rfl, rfl⟩
            obtain ⟨vi, hmi, hvy⟩ := zextScalePart_ok hdefs hsy vy hmy
            obtain ⟨vb, hmb, hvx⟩ := baseDispPart_ok hdefs hbx vx hmx
            exact ⟨_, vi, hwp, hmi, vb, fun _ hb' => by cases hb'; exact hmb, by
              simp [hvx, hvy, Int64.toBitVec_ofBitVec]; ac_rfl⟩
      | imm c =>
        rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
        cases h1 with | var hmx => cases h2 with | imm =>
        simp only [OpCode.wp_add, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
          ite_false] at hwp
        simp only [extractLeaZext64, BitVec.setWidth_eq] at hext
        obtain ⟨vi, hmi, vb, hvb, hr⟩ := extractLeaZextImm_ok hdefs hmx hext
        exact ⟨_, vi, hwp, hmi, vb, hvb, hr⟩
    | imm c =>
      cases b with
      | imm _ => simp [extractLeaZext64] at hext
      | var x =>
        rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
        cases h1 with | imm => cases h2 with | var hmx =>
        simp only [OpCode.wp_add, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
          ite_false] at hwp
        simp only [extractLeaZext64, BitVec.setWidth_eq] at hext
        obtain ⟨vi, hmi, vb, hvb, hr⟩ := extractLeaZextImm_ok hdefs hmx hext
        exact ⟨_, vi, hwp, hmi, vb, hvb, by rw [BitVec.add_comm]; exact hr⟩
  | sub =>
    rcases args with ⟨a, b, ⟨⟩⟩
    cases a with
    | imm _ => simp [extractLeaZext64] at hext
    | var x =>
      cases b with
      | var _ => simp [extractLeaZext64] at hext
      | imm c =>
        rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
        cases h1 with | var hmx => cases h2 with | imm =>
        simp only [OpCode.wp_sub, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
          ite_false] at hwp
        simp only [extractLeaZext64, BitVec.setWidth_eq] at hext
        obtain ⟨vi, hmi, vb, hvb, hr⟩ := extractLeaZextImm_ok hdefs hmx hext
        exact ⟨_, vi, hwp, hmi, vb, hvb, by simpa [BitVec.sub_eq_add_neg] using hr⟩
  | _ => simp [extractLeaZext64] at hext

end Rega
end LeanQbe.T
