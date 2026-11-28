module

public import LeanQbe.T.Examples.Kissat.PlainIngestLemmas1
import LeanQbe.T.Logic.C0Step
meta import Lean.Elab.Tactic
meta import LeanQbe.T.Logic.C0Step
import Kraken.Separation

/-!
# Soundness Proofs for Kissat `D-Plain` Tables & Initialization (`Stage 3`, Part 2)

Proves layout splitting (`avail_to_initArrs`) and parametric `Func.wp` specifications for:
1. `plain_zero_tables` (`plainZeroTablesSpec`, `plain_zero_tables_wp`)
2. `plain_init_state` (`plainInitStateSpec`, `plain_init_state_wp`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap LeanQbe.T.C0Step
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. `hdrTail92`, scoped tactics, and `PlainCfg` arena splitting -/

def hdrTail92 (hdr : BitVec 64) (ws : List (BitVec 64)) : Mem 64 → Prop :=
  fun m => ws.length = 92 ∧ array64 (hdr + 32) ws m

namespace PlainIngestTactics

private theorem pi_ptr_add_ofNat (p : BitVec 64) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

@[scoped bv_c0] theorem cfg_minDepth_mod (c : PlainCfg) : c.minDepth % 2 ^ 64 = c.minDepth := by
  have := plainMinDepthOf_le c.mv; unfold PlainCfg.minDepth; exact Nat.mod_eq_of_lt (by omega)

@[scoped c0_store] theorem c0_store_wstk0 {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.wstk.length) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pWstk + 0#64) ∧
      (PlainMem c { s with wstk := s.wstk.set 0 v } ⋆ R)
        (storeMem m i32 (c.pWstk + 0#64) v) := by
  have hz : c.pWstk = c.pWstk + BitVec.ofNat 64 (4 * 0) := (BitVec.add_zero _).symm
  rw [BitVec.add_zero, hz]; exact store_arena_wstk v hi hm

@[scoped c0_store] theorem c0_store_hdr92 (off v hdr : BitVec 64) (ws : List (BitVec 64))
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (hdrTail92 hdr ws ⋆ F) m)
    (h123 : 32 ≤ off.toNat ∧ (off.toNat - 32) % 8 = 0 ∧ (off.toNat - 32) / 8 < 92) :
    storeOk m i64 (hdr + off) ∧
      (hdrTail92 hdr (ws.set ((off.toNat - 32) / 8) v) ⋆ F) (storeMem m i64 (hdr + off) v) := by
  unfold hdrTail92 at hm ⊢
  obtain ⟨hwl, hm'⟩ := sep_pure_l.mp hm
  have h : hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * ((off.toNat - 32) / 8)) = hdr + off := by
    rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, pi_ptr_add_ofNat,
      show 32 + 8 * ((off.toNat - 32) / 8) = off.toNat by omega, bv_ofNat_toNat_eq]
  obtain ⟨hok, hst⟩ :=
    store_array64 (i := (off.toNat - 32) / 8) v (by rw [hwl]; exact h123.2.2) hm'
  rw [h] at hok hst
  exact ⟨hok, sep_pure_l.mpr ⟨by simp [hwl], hst⟩⟩

@[scoped c0_load] theorem c0_load_dimacs_mv {d mv nc cur val : BitVec 64}
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (dimacsState d mv nc cur val ⋆ F) m) :
    loadVal m i64 d = some mv := Kissat.load_dimacs_mv hm

@[scoped c0_load] theorem c0_load_dimacs_nc {d mv nc cur val : BitVec 64}
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (dimacsState d mv nc cur val ⋆ F) m) :
    loadVal m i64 (d + 8) = some nc := Kissat.load_dimacs_nc hm

private meta def piShallowRun (stopOnMem : Bool) : Lean.Elab.Tactic.TacticM Unit := do
  let isStopHead (ty : Lean.Expr) : Bool :=
    let ty := ty.consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
      let e := (ty.getArg! 4).consumeMData.headBeta
      e.isAppOf ``LeanQbe.T.Expr.jnz || e.isAppOf ``LeanQbe.T.Expr.group ||
        (stopOnMem && (e.isAppOf ``LeanQbe.T.Expr.store || e.isAppOf ``LeanQbe.T.Expr.load))
    else false
  let unwrapMData (g : Lean.MVarId) : Lean.MetaM Lean.MVarId := do
    let ty0 ← Lean.instantiateMVars (← g.getType)
    let g ← if ty0.isMData then g.replaceTargetDefEq ty0.consumeMData else pure g
    let ty := (← Lean.instantiateMVars (← g.getType)).headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
      let e := (ty.getArg! 4).consumeMData.headBeta
      return ← g.replaceTargetDefEq (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e))
    return g
  for _ in [:450] do
    let gs ← Lean.Elab.Tactic.getUnsolvedGoals
    let some g := gs.head? | break
    let (nextGs, cont) ← g.withContext do
      let g ← unwrapMData g
      let ty ← Lean.instantiateMVars (← g.getType)
      if isStopHead ty then
        return (g :: gs.tail!, false)
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
        let e := ty.getArg! 4
        if e.isAppOf ``LeanQbe.T.Blocks.get then
          let e' ← Lean.Meta.whnf e
          if e' != e then
            let g' ← g.replaceTargetDefEq
              (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
            return (g' :: gs.tail!, true)
        let kOpt? : Option (Lean.Expr × (Lean.Expr → Lean.Expr)) :=
          if e.isAppOf ``LeanQbe.T.Expr.let_ && e.getAppNumArgs == 6 then
            some (e.getArg! 5, fun k' => Lean.mkAppN e.getAppFn (e.getAppArgs.set! 5 k'))
          else if !stopOnMem && e.isAppOf ``LeanQbe.T.Expr.load && e.getAppNumArgs == 6 then
            some (e.getArg! 5, fun k' => Lean.mkAppN e.getAppFn (e.getAppArgs.set! 5 k'))
          else if !stopOnMem && e.isAppOf ``LeanQbe.T.Expr.store && e.getAppNumArgs == 7 then
            some (e.getArg! 6, fun k' => Lean.mkAppN e.getAppFn (e.getAppArgs.set! 6 k'))
          else none
        if let some (k, mkE) := kOpt? then
          let s ← Lean.Elab.Tactic.saveState
          let kTy ← Lean.Meta.inferType k
          let mTy ← Lean.Meta.withLocalDeclD `kTmp kTy fun kVar => do
            let eqTy ← Lean.Meta.mkEq kVar k
            Lean.Meta.withLocalDeclD `hkTmp eqTy fun hkVar => do
              let body := Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 (mkE kVar))
              Lean.Meta.mkForallFVars #[kVar, hkVar] body
          let gMasked ← Lean.Meta.mkFreshExprMVar mTy
          g.assign (Lean.mkApp2 gMasked k (← Lean.Meta.mkEqRefl k))
          let (kFvar, g1) ← gMasked.mvarId!.intro1P
          let (hkFvar, g2) ← g1.intro1P
          Lean.Elab.Tactic.setGoals [g2]
          let ok ← try stepOnce catch _ => s.restore; pure false
          if !ok then
            s.restore
            return (g :: gs.tail!, false)
          let mut restGoals : List Lean.MVarId := []
          for rg in (← Lean.Elab.Tactic.getUnsolvedGoals) do
            let rg' ← rg.withContext do
              let rg' ← try
                let res ← rg.rewrite (← Lean.instantiateMVars (← rg.getType))
                  (Lean.mkFVar hkFvar)
                rg.replaceTargetEq res.eNew res.eqProof
              catch _ => pure rg
              let rg' ← rg'.tryClear hkFvar
              let rg' ← rg'.tryClear kFvar
              unwrapMData rg'
            restGoals := restGoals ++ [rg']
          return (restGoals ++ gs.tail!, true)
      let s ← Lean.Elab.Tactic.saveState
      Lean.Elab.Tactic.setGoals [g]
      let ok ← try stepOnce catch _ => s.restore; pure false
      if !ok then return (g :: gs.tail!, false)
      return ((← Lean.Elab.Tactic.getUnsolvedGoals) ++ gs.tail!, true)
    Lean.Elab.Tactic.setGoals nextGs
    if !cont then break

end PlainIngestTactics

open scoped PlainIngestTactics open PlainIngestTactics

local elab "pi_head_steps" : tactic => do
  let isBranchHead (ty : Lean.Expr) : Bool :=
    let ty := ty.consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
      let e := (ty.getArg! 4).consumeMData.headBeta
      e.isAppOf ``LeanQbe.T.Expr.jnz || e.isAppOf ``LeanQbe.T.Expr.group
    else false
  let unwrapMData (g : Lean.MVarId) : Lean.MetaM Lean.MVarId := do
    let ty0 ← Lean.instantiateMVars (← g.getType)
    let g ← if ty0.isMData then g.replaceTargetDefEq ty0.consumeMData else pure g
    let ty := (← Lean.instantiateMVars (← g.getType)).headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
      let e := ty.getArg! 4
      if e.isMData then
        return ← g.replaceTargetDefEq
          (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e.consumeMData))
    return g
  for _ in [:450] do
    let gs ← Lean.Elab.Tactic.getUnsolvedGoals
    let some g := gs.head? | break
    let g ← unwrapMData g
    if isBranchHead (← Lean.instantiateMVars (← g.getType)) then
      Lean.Elab.Tactic.setGoals (g :: gs.tail!); break
    Lean.Elab.Tactic.setGoals [g]
    let s ← Lean.Elab.Tactic.saveState
    let ok ← try stepOnce catch _ => s.restore; pure false
    Lean.Elab.Tactic.setGoals ((← Lean.Elab.Tactic.getUnsolvedGoals) ++ gs.tail!)
    if !ok then break

local elab "pi_shallow_steps" : tactic => piShallowRun false
local elab "pi_shallow_lets" : tactic => piShallowRun true

private theorem bv64_align8 {n : Nat} (hn : n + 7 < 2 ^ 64) :
    (BitVec.ofNat 64 n + (7 : BitVec 64)) &&& (~~~(7 : BitVec 64)) =
      BitVec.ofNat 64 (((n + 7) / 8) * 8) := by
  apply BitVec.eq_of_toNat_eq; rw [show (7 : BitVec 64) = BitVec.ofNat 64 7 from rfl, bv_add_ofNat]
  simp only [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show ((n + 7) / 8) * 8 < 2 ^ 64 by omega),
    show (2 ^ 64 - 1 - 7 % 2 ^ 64) = 2 ^ 64 - 8 from by decide]
  have hd := Nat.and_div_two_pow (a := n + 7) (b := 2 ^ 64 - 8) (n := 3)
  have hr := Nat.and_mod_two_pow (a := n + 7) (b := 2 ^ 64 - 8) (n := 3)
  rw [show (2 ^ 64 - 8) / 2 ^ 3 = 2 ^ 61 - 1 from by decide] at hd
  rw [show (2 ^ 64 - 8) % 2 ^ 3 = 0 from by decide, Nat.and_zero] at hr
  have hq := Nat.and_two_pow_sub_one_eq_mod ((n + 7) / 8) 61; rw [Nat.mod_eq_of_lt (by omega)] at hq
  rw [show (2 ^ 3 : Nat) = 8 from by decide] at hd hr; rw [hq] at hd; omega

private theorem bv64_shl2_nat {n : Nat} :
    BitVec.ofNat 64 n <<< (2 : Nat) = BitVec.ofNat 64 (4 * n) := by bv_omega
private theorem bv64_shl3_nat {n : Nat} :
    BitVec.ofNat 64 n <<< (3 : Nat) = BitVec.ofNat 64 (8 * n) := by bv_omega
private theorem bv64_shr3_nat {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> (3 : Nat) = BitVec.ofNat 64 (n / 8) := by
  simpa [Nat.shiftRight_eq_div_pow] using bv_shr_ofNat hn (k := 3) (by decide)
private theorem bv_udiv_ofNat {a b : Nat} (ha : a < 2 ^ 64) (_hb : 0 < b) (hb64 : b < 2 ^ 64) :
    BitVec.ofNat 64 a / BitVec.ofNat 64 b = BitVec.ofNat 64 (a / b) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_udiv, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb64,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha)]
private theorem bv64_mul12 (n : Nat) :
    BitVec.ofNat 64 n * (12 : BitVec 64) = BitVec.ofNat 64 (12 * n) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_comm, Nat.mul_mod]
private theorem bv64_mul40 (n : Nat) :
    BitVec.ofNat 64 n * (40 : BitVec 64) = BitVec.ofNat 64 (n * 40) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_mod]
private theorem bv64_mul3 (n : Nat) :
    BitVec.ofNat 64 n * (3 : BitVec 64) = BitVec.ofNat 64 (3 * n) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_comm, Nat.mul_mod]
private theorem bv64_add1_nat {n : Nat} : BitVec.ofNat 64 n + 1 = BitVec.ofNat 64 (n + 1) := by
  bv_omega

/-- Pure `del_cap`, `total_pairs`, `arena_pairs`, `red_pairs`, and `w_pairs` computed by init. -/
def plainInitDelCap (rem : Nat) : Nat := if 524288 ≤ rem then 4096 else 8
def plainInitTotalPairs (rem : Nat) : Nat := (rem - plainInitDelCap rem * 12) / 8
def plainInitArenaPairs (rem : Nat) : Nat :=
  min ((plainInitTotalPairs rem * 3) / 5) 134217727
def plainInitRedPairs (rem : Nat) : Nat := (plainInitArenaPairs rem + 5) / 6
def plainInitWPairs (rem : Nat) : Nat :=
  min (plainInitTotalPairs rem - plainInitArenaPairs rem - plainInitRedPairs rem) 134217727

theorem plainInitDelCap_lt (rem : Nat) : plainInitDelCap rem < dimacsBound := by
  unfold plainInitDelCap dimacsBound; split <;> omega
theorem plainInitArenaCap_lt (rem : Nat) : 2 * plainInitArenaPairs rem < 2 * dimacsBound := by
  unfold plainInitArenaPairs dimacsBound; omega
theorem plainInitRedCap_lt (rem : Nat) : 2 * plainInitRedPairs rem < dimacsBound := by
  unfold plainInitRedPairs plainInitArenaPairs dimacsBound; omega
theorem plainInitWCap_lt (rem : Nat) : 2 * plainInitWPairs rem < 2 * dimacsBound := by
  unfold plainInitWPairs dimacsBound; omega

theorem plainInit_total_ge5 {nc rem : Nat} (h : nc * 40 + 136 ≤ rem) :
    plainInitDelCap rem * 12 ≤ rem ∧ 5 ≤ plainInitTotalPairs rem ∧
    plainInitArenaPairs rem + plainInitRedPairs rem ≤ plainInitTotalPairs rem := by
  by_cases hbig : 524288 ≤ rem <;>
    simp only [plainInitRedPairs, plainInitArenaPairs, plainInitTotalPairs, plainInitDelCap,
      hbig, ↓reduceIte] <;> omega

theorem plain_init_arena_fits {mv nc avail : Nat}
    (h : plainFixedBytes mv + nc * 40 + 136 ≤ avail) :
    let rem := avail - plainFixedBytes mv
    plainFixedBytes mv + 4 * (2 * plainInitArenaPairs rem) +
      4 * (2 * plainInitWPairs rem) + 12 * plainInitDelCap rem +
      4 * (2 * plainInitRedPairs rem) ≤ avail := by
  intro rem; have ⟨h1, _, h3⟩ := plainInit_total_ge5 (nc := nc) (rem := rem) (by omega)
  have h4 : plainInitWPairs rem ≤
      plainInitTotalPairs rem - plainInitArenaPairs rem - plainInitRedPairs rem := by
    unfold plainInitWPairs; omega
  have h5 : 8 * plainInitTotalPairs rem ≤ rem - plainInitDelCap rem * 12 := by
    unfold plainInitTotalPairs; omega
  omega

private theorem reg_peel {a b : BitVec 64} {n1 n2 n : Nat} {m : Mem 64} (hm : region a n m)
    (hb : a + BitVec.ofNat 64 n1 = b := by rfl) (hn : n = n1 + n2 := by omega)
    (hle : n1 + n2 ≤ 2 ^ 64 := by omega) : (region a n1 ⋆ region b n2) m := by
  subst hb hn; rwa [← region_merge_eq (a := a) (n1 := n1) (n2 := n2) (n := n1 + n2) rfl hle] at hm

private theorem sep_ex_pure_l {α : Type} {P Q : Mem 64 → Prop} {φ : α → Prop}
    {P' : α → Mem 64 → Prop} {m : Mem 64}
    (hm : (P ⋆ Q) m) (h : ∀ m1, P m1 → ∃ x, φ x ∧ P' x m1) :
    ∃ x, φ x ∧ (P' x ⋆ Q) m := by
  obtain ⟨x, hx⟩ := sep_ex_l.mp (sep_mono h hm)
  obtain ⟨hφ, hp⟩ := sep_pure_l.mp hx
  exact ⟨x, hφ, hp⟩

private theorem sep_ex_step {α : Type} {P Q R : Mem 64 → Prop} {φ : α → Prop}
    {P' : α → Mem 64 → Prop} {m : Mem 64}
    (hm : (R ⋆ (P ⋆ Q)) m) (h : ∀ m1, P m1 → ∃ x, φ x ∧ P' x m1) :
    ∃ x, φ x ∧ ((R ⋆ P' x) ⋆ Q) m := by
  obtain ⟨x, hφ, hx⟩ := sep_ex_pure_l (show (P ⋆ (R ⋆ Q)) m from sep_ac hm) h
  exact ⟨x, hφ, sep_ac hx⟩

private theorem sep_ex_pure_r {α : Type} {R P : Mem 64 → Prop} {φ : α → Prop}
    {P' : α → Mem 64 → Prop} {m : Mem 64}
    (hm : (R ⋆ P) m) (h : ∀ m1, P m1 → ∃ x, φ x ∧ P' x m1) :
    ∃ x, φ x ∧ (R ⋆ P' x) m := by
  obtain ⟨x, hφ, hx⟩ := sep_ex_pure_l (show (P ⋆ R) m from sep_ac hm) h
  exact ⟨x, hφ, sep_ac hx⟩

private theorem sep_mono_mid {R P P' Q : Mem 64 → Prop} {m : Mem 64}
    (hm : (R ⋆ (P ⋆ Q)) m) (h : ∀ m1, P m1 → P' m1) : (P' ⋆ (R ⋆ Q)) m :=
  sep_mono h (sep_ac hm)

private theorem sep_mono_rr {A B Q Q' : Mem 64 → Prop} {m : Mem 64}
    (hm : (A ⋆ (B ⋆ Q)) m) (h : ∀ m1, Q m1 → Q' m1) : ((A ⋆ B) ⋆ Q') m :=
  sep_mono_r h (sep_ac hm)

private theorem sep_rr_mono {A B Q Q' : Mem 64 → Prop} {m : Mem 64}
    (hm : (A ⋆ (B ⋆ Q)) m) (h : ∀ m1, Q m1 → Q' m1) : (Q' ⋆ (A ⋆ B)) m :=
  sep_mono h (sep_ac hm)

private theorem reg_split_i8_pad {a : BitVec 64} {act tot : Nat} {m : Mem 64}
    (hle : act ≤ tot) (hfit : tot ≤ 2 ^ 64) (hm : region a tot m) :
    ∃ xs : List (BitVec 8), xs.length = act ∧
      (array (t := i8) a xs ⋆ region (a + BitVec.ofNat 64 act) (tot - act)) m :=
  sep_ex_pure_l (reg_peel (n1 := act) (n2 := tot - act) hm)
    (fun _ hr => region_to_array_i8 act (by omega) hr)

private theorem reg_split_i32_pad {a : BitVec 64} {cnt tot : Nat} {m : Mem 64}
    (hle : 4 * cnt ≤ tot) (hfit : tot ≤ 2 ^ 64) (hm : region a tot m) :
    ∃ xs : List (BitVec 32), xs.length = cnt ∧
      (array (t := i32) a xs ⋆ region (a + BitVec.ofNat 64 (4 * cnt)) (tot - 4 * cnt)) m :=
  sep_ex_pure_l (reg_peel (n1 := 4 * cnt) (n2 := tot - 4 * cnt) hm)
    (fun _ hr => region_to_array_i32 cnt (by omega) hr)

private theorem sep_split_i8_l {a : BitVec 64} {act tot : Nat} {Q : Mem 64 → Prop} {m : Mem 64}
    (hm : (region a tot ⋆ Q) m) (hle : act ≤ tot) (hfit : tot ≤ 2 ^ 64) :
    ∃ xs : List (BitVec 8), xs.length = act ∧
      ((array (t := i8) a xs ⋆ region (a + BitVec.ofNat 64 act) (tot - act)) ⋆ Q) m :=
  sep_ex_pure_l hm (fun _ hr => reg_split_i8_pad hle hfit hr)

private theorem sep_split_i8_step {a : BitVec 64} {act tot : Nat} {R Q : Mem 64 → Prop}
    {m : Mem 64} (hm : (R ⋆ (region a tot ⋆ Q)) m) (hle : act ≤ tot) (hfit : tot ≤ 2 ^ 64) :
    ∃ xs : List (BitVec 8), xs.length = act ∧
      ((R ⋆ (array (t := i8) a xs ⋆ region (a + BitVec.ofNat 64 act) (tot - act))) ⋆ Q) m :=
  sep_ex_step hm (fun _ hr => reg_split_i8_pad hle hfit hr)

private theorem sep_split_i8_r {a : BitVec 64} {act tot : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (R ⋆ region a tot) m) (hle : act ≤ tot) (hfit : tot ≤ 2 ^ 64) :
    ∃ xs : List (BitVec 8), xs.length = act ∧
      (R ⋆ (array (t := i8) a xs ⋆ region (a + BitVec.ofNat 64 act) (tot - act))) m :=
  sep_ex_pure_r hm (fun _ hr => reg_split_i8_pad hle hfit hr)

private theorem sep_split_i32_l {a : BitVec 64} {cnt tot : Nat} {Q : Mem 64 → Prop}
    {m : Mem 64} (hm : (region a tot ⋆ Q) m) (hle : 4 * cnt ≤ tot) (hfit : tot ≤ 2 ^ 64) :
    ∃ xs : List (BitVec 32), xs.length = cnt ∧
      ((array (t := i32) a xs ⋆
        region (a + BitVec.ofNat 64 (4 * cnt)) (tot - 4 * cnt)) ⋆ Q) m :=
  sep_ex_pure_l hm (fun _ hr => reg_split_i32_pad hle hfit hr)

private theorem sep_split_i32_step {a : BitVec 64} {cnt tot : Nat} {R Q : Mem 64 → Prop}
    {m : Mem 64} (hm : (R ⋆ (region a tot ⋆ Q)) m) (hle : 4 * cnt ≤ tot) (hfit : tot ≤ 2 ^ 64) :
    ∃ xs : List (BitVec 32), xs.length = cnt ∧
      ((R ⋆ (array (t := i32) a xs ⋆
        region (a + BitVec.ofNat 64 (4 * cnt)) (tot - 4 * cnt))) ⋆ Q) m :=
  sep_ex_step hm (fun _ hr => reg_split_i32_pad hle hfit hr)

private theorem sep_split_i32_r {a : BitVec 64} {cnt tot : Nat} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (R ⋆ region a tot) m) (hle : 4 * cnt ≤ tot) (hfit : tot ≤ 2 ^ 64) :
    ∃ xs : List (BitVec 32), xs.length = cnt ∧
      (R ⋆ (array (t := i32) a xs ⋆
        region (a + BitVec.ofNat 64 (4 * cnt)) (tot - 4 * cnt))) m :=
  sep_ex_pure_r hm (fun _ hr => reg_split_i32_pad hle hfit hr)

private theorem sep_unzip5 {A B C D E A' B' C' D' E' : Mem 64 → Prop} {m : Mem 64}
    (h : ((((A ⋆ A') ⋆ (B ⋆ B')) ⋆ (C ⋆ C')) ⋆ (D ⋆ D') ⋆ (E ⋆ E')) m) :
    ((A ⋆ B ⋆ C ⋆ D ⋆ E) ⋆ (A' ⋆ B' ⋆ C' ⋆ D' ⋆ E')) m := sep_ac h

private theorem sep_arr_i32_l (cnt : Nat) {a : BitVec 64} {n : Nat} {Q : Mem 64 → Prop}
    {m : Mem 64} (hm : (region a n ⋆ Q) m) (hn : 4 * cnt = n) (hfit : n ≤ 2 ^ 64) :
    ∃ xs : List (BitVec 32), xs.length = cnt ∧ (array (t := i32) a xs ⋆ Q) m := by
  subst hn; exact sep_ex_pure_l hm (fun _ hr => region_to_array_i32 cnt hfit hr)

private theorem sep_arr_i32_step (cnt : Nat) {a : BitVec 64} {n : Nat} {R Q : Mem 64 → Prop}
    {m : Mem 64} (hm : (R ⋆ (region a n ⋆ Q)) m) (hn : 4 * cnt = n) (hfit : n ≤ 2 ^ 64) :
    ∃ xs : List (BitVec 32), xs.length = cnt ∧ ((R ⋆ array (t := i32) a xs) ⋆ Q) m := by
  subst hn; exact sep_ex_step hm (fun _ hr => region_to_array_i32 cnt hfit hr)

private theorem sep_arr_i64_l (cnt : Nat) {a : BitVec 64} {n : Nat} {Q : Mem 64 → Prop}
    {m : Mem 64} (hm : (region a n ⋆ Q) m) (hn : 8 * cnt = n) (hfit : n ≤ 2 ^ 64) :
    ∃ xs : List (BitVec 64), xs.length = cnt ∧ (array64 a xs ⋆ Q) m := by
  subst hn; exact sep_ex_pure_l hm (fun _ hr => region_to_array64 cnt hfit hr)

private theorem sep_arr_i64_step (cnt : Nat) {a : BitVec 64} {n : Nat} {R Q : Mem 64 → Prop}
    {m : Mem 64} (hm : (R ⋆ (region a n ⋆ Q)) m) (hn : 8 * cnt = n) (hfit : n ≤ 2 ^ 64) :
    ∃ xs : List (BitVec 64), xs.length = cnt ∧ ((R ⋆ array64 a xs) ⋆ Q) m := by
  subst hn; exact sep_ex_step hm (fun _ hr => region_to_array64 cnt hfit hr)

private theorem split_marks_regs (c : PlainCfg) {m : Mem 64}
    (hm : region c.pVals (valsBytes c.mv + 4 * markBytes c.mv) m) :
    ∃ (vals mrk ph ptgt pbst : List (BitVec 8)),
      vals.length = 2 * c.mv ∧ mrk.length = c.mv ∧ ph.length = c.mv ∧
      ptgt.length = c.mv ∧ pbst.length = c.mv ∧
      ((array (t := i8) c.pVals vals ⋆ array (t := i8) c.pMark mrk ⋆
        array (t := i8) c.pPhases ph ⋆ array (t := i8) c.pPhasesTarget ptgt ⋆
        array (t := i8) c.pPhasesBest pbst) ⋆ c.padMarks) m := by
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hv := valsBytes_ge c.mv; have hmk := markBytes_ge c.mv
  have hvlt : valsBytes c.mv ≤ 2 * c.mv + 7 := by unfold valsBytes; omega
  have hmlt : markBytes c.mv ≤ c.mv + 7 := by unfold markBytes; omega
  have h1 := reg_peel (b := c.pMark) (n1 := valsBytes c.mv) (n2 := 4 * markBytes c.mv) hm
    rfl rfl (by omega)
  have h2 := sep_mono_r (fun _ h => reg_peel (b := c.pPhases) (n1 := markBytes c.mv)
    (n2 := 3 * markBytes c.mv) h rfl (by omega) (by omega)) h1
  have h3 := sep_mono_r (fun _ => sep_mono_r (fun _ h => reg_peel (b := c.pPhasesTarget)
    (n1 := markBytes c.mv) (n2 := 2 * markBytes c.mv) h rfl (by omega) (by omega))) h2
  have h4 := sep_mono_r (fun _ => sep_mono_r (fun _ => sep_mono_r (fun _ h =>
    reg_peel (b := c.pPhasesBest) (n1 := markBytes c.mv) (n2 := markBytes c.mv) h
      rfl (by omega) (by omega)))) h3
  obtain ⟨vals, hvl, h5⟩ := sep_split_i8_l h4 hv (by omega)
  obtain ⟨mrk, hmkl, h6⟩ := sep_split_i8_step h5 hmk (by omega)
  obtain ⟨ph, hphl, h7⟩ := sep_split_i8_step h6 hmk (by omega)
  obtain ⟨ptgt, hptl, h8⟩ := sep_split_i8_step h7 hmk (by omega)
  obtain ⟨pbst, hpbl, h9⟩ := sep_split_i8_r h8 hmk (by omega)
  refine ⟨vals, mrk, ph, ptgt, pbst, hvl, hmkl, hphl, hptl, hpbl, ?_⟩
  unfold PlainCfg.padMarks
  exact sep_unzip5 h9

private theorem split_u32_six {a1 a2 a3 a4 a5 a6 : BitVec 64} {mv : Nat} (hmv : mv < dimacsBound)
    (h12 : a2 = a1 + BitVec.ofNat 64 (u32VarBytes mv))
    (h23 : a3 = a2 + BitVec.ofNat 64 (u32VarBytes mv))
    (h34 : a4 = a3 + BitVec.ofNat 64 (u32VarBytes mv))
    (h45 : a5 = a4 + BitVec.ofNat 64 (u32VarBytes mv))
    (h56 : a6 = a5 + BitVec.ofNat 64 (u32VarBytes mv))
    {m : Mem 64} (hm : region a1 (6 * u32VarBytes mv) m) :
    ∃ x1 x2 x3 x4 x5 x6 : List (BitVec 32), x1.length = mv ∧ x2.length = mv ∧ x3.length = mv ∧
      x4.length = mv ∧ x5.length = mv ∧ x6.length = mv ∧
      ((array (t := i32) a1 x1 ⋆ array (t := i32) a2 x2 ⋆ array (t := i32) a3 x3 ⋆
        array (t := i32) a4 x4 ⋆ array (t := i32) a5 x5 ⋆ array (t := i32) a6 x6) ⋆
        (region (a1 + BitVec.ofNat 64 (4 * mv)) (u32VarBytes mv - 4 * mv) ⋆
         region (a2 + BitVec.ofNat 64 (4 * mv)) (u32VarBytes mv - 4 * mv) ⋆
         region (a3 + BitVec.ofNat 64 (4 * mv)) (u32VarBytes mv - 4 * mv) ⋆
         region (a4 + BitVec.ofNat 64 (4 * mv)) (u32VarBytes mv - 4 * mv) ⋆
         region (a5 + BitVec.ofNat 64 (4 * mv)) (u32VarBytes mv - 4 * mv) ⋆
         region (a6 + BitVec.ofNat 64 (4 * mv)) (u32VarBytes mv - 4 * mv))) m := by
  unfold dimacsBound at hmv; have hu := u32VarBytes_ge mv
  have hult : u32VarBytes mv ≤ 4 * mv + 7 := by unfold u32VarBytes; omega
  have h1 := reg_peel (b := a2) (n1 := u32VarBytes mv) (n2 := 5 * u32VarBytes mv) hm
    h12.symm (by omega) (by omega)
  have h2 := sep_mono_r (fun _ h => reg_peel (b := a3) (n1 := u32VarBytes mv)
    (n2 := 4 * u32VarBytes mv) h h23.symm (by omega) (by omega)) h1
  have h3 := sep_mono_r (fun _ => sep_mono_r (fun _ h => reg_peel (b := a4) (n1 := u32VarBytes mv)
    (n2 := 3 * u32VarBytes mv) h h34.symm (by omega) (by omega))) h2
  have h4 := sep_mono_r (fun _ => sep_mono_r (fun _ => sep_mono_r (fun _ h =>
    reg_peel (b := a5) (n1 := u32VarBytes mv) (n2 := 2 * u32VarBytes mv) h
      h45.symm (by omega) (by omega)))) h3
  have h5 := sep_mono_r (fun _ => sep_mono_r (fun _ => sep_mono_r (fun _ => sep_mono_r (fun _ h =>
    reg_peel (b := a6) (n1 := u32VarBytes mv) (n2 := u32VarBytes mv) h
      h56.symm (by omega) (by omega))))) h4
  obtain ⟨x1, hx1, s1⟩ := sep_split_i32_l h5 hu (by omega)
  obtain ⟨x2, hx2, s2⟩ := sep_split_i32_step s1 hu (by omega)
  obtain ⟨x3, hx3, s3⟩ := sep_split_i32_step s2 hu (by omega)
  obtain ⟨x4, hx4, s4⟩ := sep_split_i32_step s3 hu (by omega)
  obtain ⟨x5, hx5, s5⟩ := sep_split_i32_step s4 hu (by omega)
  obtain ⟨x6, hx6, s6⟩ := sep_split_i32_r s5 hu (by omega)
  exact ⟨x1, x2, x3, x4, x5, x6, hx1, hx2, hx3, hx4, hx5, hx6, sep_ac s6⟩

private theorem split_tail_regs (c : PlainCfg) {m : Mem 64}
    (hm : region c.pWvec (c.avail - (768 + valsBytes c.mv + 4 * markBytes c.mv +
      12 * u32VarBytes c.mv)) m) :
    ∃ (wvec wsort mstk gu arena wstk del rr : List (BitVec 32)) (score : List (BitVec 64)),
      wvec.length = 4 * c.mv ∧ wsort.length = 2 * c.mv ∧ score.length = c.mv ∧
      mstk.length = 2 * c.minDepth ∧ gu.length = 64 ∧ arena.length = c.arena_cap ∧
      wstk.length = c.wcap ∧ del.length = 3 * c.delayed_cap ∧ rr.length = c.red_cap ∧
      ((array (t := i32) c.pWvec wvec ⋆ array (t := i32) c.pWsort wsort ⋆
        array64 c.pScore score ⋆ array (t := i32) c.pMinStk mstk ⋆
        array (t := i32) c.pGlueUsed gu ⋆ array (t := i32) c.pArena arena ⋆
        array (t := i32) c.pWstk wstk ⋆ array (t := i32) c.pDelayed del ⋆
        array (t := i32) c.pRedRefs rr) ⋆ region c.pSlack c.slack) m := by
  have hmv := c.hmv; have har := c.harena; have hw := c.hwcap; have hdl := c.hdel
  have hrd := c.hred; have hfit := c.havail_fit; have hsz := c.hsize
  have hv := valsBytes_ge c.mv; have hmk := markBytes_ge c.mv; have hu := u32VarBytes_ge c.mv
  have hmd_eq : c.minDepth = plainMinDepthOf c.mv := rfl
  have hmd : c.minDepth ≤ 1000 := hmd_eq ▸ plainMinDepthOf_le c.mv
  unfold dimacsBound at hmv har hw hdl hrd
  unfold plainFixedBytes at hsz
  rw [← hmd_eq] at hsz
  let n_tl := c.avail - (768 + valsBytes c.mv + 4 * markBytes c.mv + 12 * u32VarBytes c.mv)
  let slk := c.avail - (1024 + valsBytes c.mv + 4 * markBytes c.mv + 12 * u32VarBytes c.mv +
    32 * c.mv + 8 * c.minDepth + 4 * c.arena_cap + 4 * c.wcap +
    12 * c.delayed_cap + 4 * c.red_cap)
  have hm1 := reg_peel (b := c.pWsort) (n1 := 16 * c.mv) (n2 := n_tl - 16 * c.mv) hm
    rfl (by omega) (by omega)
  obtain ⟨wvec, hwl, hm1⟩ := sep_arr_i32_l (4 * c.mv) hm1 (by omega) (by omega)
  have hm2 := sep_mono_r (fun _ h => reg_peel (b := c.pScore) (n1 := 8 * c.mv)
    (n2 := n_tl - 24 * c.mv) h rfl (by omega) (by omega)) hm1
  obtain ⟨wsort, hwsl, hm2⟩ := sep_arr_i32_step (2 * c.mv) hm2 (by omega) (by omega)
  have hm3 := sep_mono_r (fun _ h => reg_peel (b := c.pMinStk) (n1 := 8 * c.mv)
    (n2 := n_tl - 32 * c.mv) h rfl (by omega) (by omega)) hm2
  obtain ⟨score, hscl, hm3⟩ := sep_arr_i64_step c.mv hm3 rfl (by omega)
  have hm4 := sep_mono_r (fun _ h => reg_peel (b := c.pGlueUsed) (n1 := 8 * c.minDepth)
    (n2 := n_tl - 32 * c.mv - 8 * c.minDepth) h rfl (by omega) (by omega)) hm3
  obtain ⟨mstk, hmstl, hm4⟩ := sep_arr_i32_step (2 * c.minDepth) hm4 (by omega) (by omega)
  have hm5 := sep_mono_r (fun _ h => reg_peel (b := c.pArena) (n1 := 256)
    (n2 := n_tl - 32 * c.mv - 8 * c.minDepth - 256) h rfl (by omega) (by omega)) hm4
  obtain ⟨gu, hgul, hm5⟩ := sep_arr_i32_step 64 hm5 (by decide) (by decide)
  have hm6 := sep_mono_r (fun _ h => reg_peel (b := c.pWstk) (n1 := 4 * c.arena_cap)
    (n2 := 4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap + slk) h
    rfl (by omega) (by omega)) hm5
  obtain ⟨arena, harl, hm6⟩ := sep_arr_i32_step c.arena_cap hm6 rfl (by omega)
  have hm7 := sep_mono_r (fun _ h => reg_peel (b := c.pDelayed) (n1 := 4 * c.wcap)
    (n2 := 12 * c.delayed_cap + 4 * c.red_cap + slk) h rfl (by omega) (by omega)) hm6
  obtain ⟨wstk, hwksl, hm7⟩ := sep_arr_i32_step c.wcap hm7 rfl (by omega)
  have hm8 := sep_mono_r (fun _ h => reg_peel (b := c.pRedRefs) (n1 := 12 * c.delayed_cap)
    (n2 := 4 * c.red_cap + slk) h rfl (by omega) (by omega)) hm7
  obtain ⟨del, hdll, hm8⟩ := sep_arr_i32_step (3 * c.delayed_cap) hm8 (by omega) (by omega)
  have hm9 := sep_mono_r (fun _ h => reg_peel (b := c.pSlack) (n1 := 4 * c.red_cap) (n2 := slk) h
    rfl (by omega) (by omega)) hm8
  obtain ⟨rr, hrrl, hm9⟩ := sep_arr_i32_step c.red_cap hm9 rfl (by omega)
  have hslk : slk = c.slack := by
    unfold PlainCfg.slack plainFixedBytes; rw [← hmd_eq]
  rw [hslk] at hm9
  exact ⟨wvec, wsort, mstk, gu, arena, wstk, del, rr, score,
    hwl, hwsl, hscl, hmstl, hgul, harl, hwksl, hdll, hrrl, hm9⟩

private structure InitArrs (c : PlainCfg) where
  (vals mrk ph ptgt pbst : List (BitVec 8))
  (lvl rsns trl tpos tmp heap pos mclr sstk qp qn qs : List (BitVec 32))
  (wvec wsort mstk gu arena wstk del rr : List (BitVec 32))
  (score : List (BitVec 64))
  ok : vals.length = 2 * c.mv ∧ mrk.length = c.mv ∧ ph.length = c.mv ∧
    ptgt.length = c.mv ∧ pbst.length = c.mv ∧ lvl.length = c.mv ∧
    rsns.length = c.mv ∧ trl.length = c.mv ∧ tpos.length = c.mv ∧
    tmp.length = c.mv ∧ heap.length = c.mv ∧ pos.length = c.mv ∧
    mclr.length = c.mv ∧ sstk.length = c.mv ∧ qp.length = c.mv ∧
    qn.length = c.mv ∧ qs.length = c.mv ∧ wvec.length = 4 * c.mv ∧
    wsort.length = 2 * c.mv ∧ score.length = c.mv ∧ mstk.length = 2 * c.minDepth ∧
    gu.length = 64 ∧ arena.length = c.arena_cap ∧ wstk.length = c.wcap ∧
    del.length = 3 * c.delayed_cap ∧ rr.length = c.red_cap

private def initPreState (c : PlainCfg) (d_cur d_val fuel : BitVec 64) (a : InitArrs c) :
    PlainState :=
  let qF : BitVec 64 := if c.mv = 0 then 0xFFFFFFFF#64 else 0#64
  let qL : BitVec 64 := if c.mv = 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (c.mv - 1)
  { d_cur := d_cur, d_val := d_val, arena_len := 0, wlen := 1, wusable := 0#64,
    arena_garbage := 0#64, first_reducible := 0xFFFFFFFF#64, num_irred := 0#64,
    num_redundant := 0#64, num_binary := 0#64, unflushed := 0#64, probing := 0#64,
    trail_end := 0, propagated := 0, cur_level := 0, fuel := fuel,
    confl_ref := 0xFFFFFFFF#64, confl_type := 0#64, confl_lit0 := 0#64, confl_lit1 := 0#64,
    tmp_cnt := 0, tmp_len := 0, min_clr_len := 0, min_clr_full := 0#64, oom := 0#64,
    vals := a.vals, mrk := a.mrk, lvl := a.lvl, rsns := a.rsns, trl := a.trl,
    trail_pos := a.tpos, tmp := a.tmp, wvec := a.wvec, arena := a.arena, wstk := a.wstk,
    min_stk := a.mstk, min_clr := a.mclr,
    heur := {
      heap_len := c.mv, scinc := 268435456#64, rel_period := 1024#64,
      rel_limit := 1048576#64, rel_wait := 1024#64, rel_u := 1#64, rel_v := 1#64,
      rel_trigger := 0#64, conflicts := 0#64, learned_lits := 0#64, min_removed := 0#64,
      delayed_len := 0, stable := 0#64, switched := 0#64, mode_count := 0#64,
      mode_confl_lim := 1000#64, mode_tick_lim := 0#64, mode_saved_ticks := 0#64,
      search_ticks := 0#64, q_first := qF, q_last := qL, q_search_idx := qL,
      q_search_stamp := BitVec.ofNat 64 c.mv, q_cur_stamp := BitVec.ofNat 64 c.mv,
      target_assigned := 0#64, best_assigned := 0#64, rephase_limit := 1000#64, rephased := 0#64,
      reduce_limit := 1000#64, reductions := 0#64, tier1 := 2#64, tier2 := 6#64,
      restarts := 0#64, restart_limit := 1#64, ema_fast_biased := 0#64,
      ema_fast_exp := 16777216#64, ema_slow_biased := 0#64, ema_slow_exp := 16777216#64,
      heap := a.heap, pos := a.pos, score := a.score, phases := a.ph, phases_target := a.ptgt,
      phases_best := a.pbst, wsort := a.wsort, shrink_stk := a.sstk, red_refs := a.rr,
      glue_used := a.gu, q_prev := a.qp, q_next := a.qn, q_stamp := a.qs, delayed := a.del } }

private theorem avail_to_initArrs (c : PlainCfg) {m : Mem 64}
    (hm : region (c.hdr + BitVec.ofNat 64 768) (c.avail - 768) m) :
    ∃ a : InitArrs c, (PlainCoreArrays c (initPreState c 0#64 0#64 0#64 a) ⋆
      PlainHeurArrays c (initPreState c 0#64 0#64 0#64 a).heur ⋆ c.pad) m := by
  have hmv := c.hmv; have har := c.harena; have hw := c.hwcap; have hdl := c.hdel
  have hrd := c.hred; have hfit := c.havail_fit; have hsz := c.hsize
  have hv := valsBytes_ge c.mv; have hmk := markBytes_ge c.mv
  have hu := u32VarBytes_ge c.mv; have hmd := plainMinDepthOf_le c.mv
  unfold PlainCfg.minDepth plainFixedBytes dimacsBound at *
  let n_tail := c.avail - (768 + valsBytes c.mv + 4 * markBytes c.mv + 12 * u32VarBytes c.mv)
  have hpL : c.pLevel = c.pVals + BitVec.ofNat 64 (valsBytes c.mv + 4 * markBytes c.mv) := by
    unfold PlainCfg.pLevel PlainCfg.pPhasesBest PlainCfg.pPhasesTarget PlainCfg.pPhases
      PlainCfg.pMark
    simp only [ptr_add_ofNat]; exact congrArg (fun n => c.pVals + BitVec.ofNat 64 n) (by omega)
  have hpP : c.pPos = c.pLevel + BitVec.ofNat 64 (6 * u32VarBytes c.mv) := by
    unfold PlainCfg.pPos PlainCfg.pHeap PlainCfg.pTmp PlainCfg.pTrailPos PlainCfg.pTrail
      PlainCfg.pReason
    simp only [ptr_add_ofNat]; exact congrArg (fun n => c.pLevel + BitVec.ofNat 64 n) (by omega)
  have hpW : c.pWvec = c.pPos + BitVec.ofNat 64 (6 * u32VarBytes c.mv) := by
    unfold PlainCfg.pWvec PlainCfg.pQStamp PlainCfg.pQNext PlainCfg.pQPrev
      PlainCfg.pShrinkStk PlainCfg.pMinClr
    simp only [ptr_add_ofNat]; exact congrArg (fun n => c.pPos + BitVec.ofNat 64 n) (by omega)
  have hr1 := reg_peel (b := c.pLevel) (n1 := valsBytes c.mv + 4 * markBytes c.mv)
    (n2 := 12 * u32VarBytes c.mv + n_tail) hm hpL.symm (by omega) (by omega)
  obtain ⟨vals, hr1⟩ := sep_ex_l.mp (sep_mono (fun _ h => split_marks_regs c h) hr1)
  obtain ⟨mrk, hr1⟩ := sep_ex_l.mp hr1
  obtain ⟨ph, hr1⟩ := sep_ex_l.mp hr1
  obtain ⟨ptgt, hr1⟩ := sep_ex_l.mp hr1
  obtain ⟨pbst, hr1⟩ := sep_ex_l.mp hr1
  obtain ⟨hvl, hr1⟩ := sep_pure_l.mp hr1
  obtain ⟨hmkl, hr1⟩ := sep_pure_l.mp hr1
  obtain ⟨hphl, hr1⟩ := sep_pure_l.mp hr1
  obtain ⟨hptl, hr1⟩ := sep_pure_l.mp hr1
  obtain ⟨hpbl, hr1⟩ := sep_pure_l.mp hr1
  have hr2 := sep_mono_r (fun _ h => reg_peel (b := c.pPos) (n1 := 6 * u32VarBytes c.mv)
    (n2 := 6 * u32VarBytes c.mv + n_tail) h hpP.symm (by omega) (by omega)) hr1
  obtain ⟨lvl, hr2⟩ := sep_ex_l.mp (sep_mono_mid hr2 (fun _ h =>
    split_u32_six c.hmv rfl rfl rfl rfl rfl h))
  obtain ⟨rsns, hr2⟩ := sep_ex_l.mp hr2
  obtain ⟨trl, hr2⟩ := sep_ex_l.mp hr2
  obtain ⟨tpos, hr2⟩ := sep_ex_l.mp hr2
  obtain ⟨tmp, hr2⟩ := sep_ex_l.mp hr2
  obtain ⟨heap, hr2⟩ := sep_ex_l.mp hr2
  obtain ⟨hll, hr2⟩ := sep_pure_l.mp hr2
  obtain ⟨hrsl, hr2⟩ := sep_pure_l.mp hr2
  obtain ⟨htrl, hr2⟩ := sep_pure_l.mp hr2
  obtain ⟨htpl, hr2⟩ := sep_pure_l.mp hr2
  obtain ⟨htmpl, hr2⟩ := sep_pure_l.mp hr2
  obtain ⟨hhpl, hr2⟩ := sep_pure_l.mp hr2
  have hr3 := sep_mono_rr hr2 (fun _ h => reg_peel (b := c.pWvec) (n1 := 6 * u32VarBytes c.mv)
    (n2 := n_tail) h hpW.symm (by omega) (by omega))
  obtain ⟨pos, hr3⟩ := sep_ex_l.mp (sep_mono_mid hr3 (fun _ h =>
    split_u32_six c.hmv rfl rfl rfl rfl rfl h))
  obtain ⟨mclr, hr3⟩ := sep_ex_l.mp hr3
  obtain ⟨sstk, hr3⟩ := sep_ex_l.mp hr3
  obtain ⟨qp, hr3⟩ := sep_ex_l.mp hr3
  obtain ⟨qn, hr3⟩ := sep_ex_l.mp hr3
  obtain ⟨qs, hr3⟩ := sep_ex_l.mp hr3
  obtain ⟨hpsl, hr3⟩ := sep_pure_l.mp hr3
  obtain ⟨hmcl, hr3⟩ := sep_pure_l.mp hr3
  obtain ⟨hssl, hr3⟩ := sep_pure_l.mp hr3
  obtain ⟨hqpl, hr3⟩ := sep_pure_l.mp hr3
  obtain ⟨hqnl, hr3⟩ := sep_pure_l.mp hr3
  obtain ⟨hqsl, hr3⟩ := sep_pure_l.mp hr3
  obtain ⟨wvec, hr4⟩ := sep_ex_l.mp (sep_rr_mono hr3 (fun _ h => split_tail_regs c h))
  obtain ⟨wsort, hr4⟩ := sep_ex_l.mp hr4
  obtain ⟨mstk, hr4⟩ := sep_ex_l.mp hr4
  obtain ⟨gu, hr4⟩ := sep_ex_l.mp hr4
  obtain ⟨arena, hr4⟩ := sep_ex_l.mp hr4
  obtain ⟨wstk, hr4⟩ := sep_ex_l.mp hr4
  obtain ⟨del, hr4⟩ := sep_ex_l.mp hr4
  obtain ⟨rr, hr4⟩ := sep_ex_l.mp hr4
  obtain ⟨score, hr4⟩ := sep_ex_l.mp hr4
  obtain ⟨hwl, hr4⟩ := sep_pure_l.mp hr4
  obtain ⟨hwsl, hr4⟩ := sep_pure_l.mp hr4
  obtain ⟨hscl, hr4⟩ := sep_pure_l.mp hr4
  obtain ⟨hmstl, hr4⟩ := sep_pure_l.mp hr4
  obtain ⟨hgul, hr4⟩ := sep_pure_l.mp hr4
  obtain ⟨harl, hr4⟩ := sep_pure_l.mp hr4
  obtain ⟨hwksl, hr4⟩ := sep_pure_l.mp hr4
  obtain ⟨hdll, hr4⟩ := sep_pure_l.mp hr4
  obtain ⟨hrrl, hr4⟩ := sep_pure_l.mp hr4
  refine ⟨⟨vals, mrk, ph, ptgt, pbst, lvl, rsns, trl, tpos, tmp, heap, pos, mclr, sstk,
    qp, qn, qs, wvec, wsort, mstk, gu, arena, wstk, del, rr, score,
    hvl, hmkl, hphl, hptl, hpbl, hll, hrsl, htrl, htpl, htmpl, hhpl, hpsl, hmcl, hssl,
    hqpl, hqnl, hqsl, hwl, hwsl, hscl, hmstl, hgul, harl, hwksl, hdll, hrrl⟩, ?_⟩
  let C1 := array (t := i8) c.pVals vals ⋆ array (t := i8) c.pMark mrk
  let H1 := array (t := i8) c.pPhases ph ⋆ array (t := i8) c.pPhasesTarget ptgt ⋆
    array (t := i8) c.pPhasesBest pbst
  let C2 := array (t := i32) c.pLevel lvl ⋆ array (t := i32) c.pReason rsns ⋆
    array (t := i32) c.pTrail trl ⋆ array (t := i32) c.pTrailPos tpos ⋆
    array (t := i32) c.pTmp tmp
  let H2 := array (t := i32) c.pHeap heap
  let C3 := array (t := i32) c.pMinClr mclr
  let H3 := array (t := i32) c.pPos pos ⋆ array (t := i32) c.pShrinkStk sstk ⋆
    array (t := i32) c.pQPrev qp ⋆ array (t := i32) c.pQNext qn ⋆
    array (t := i32) c.pQStamp qs
  let C4 := array (t := i32) c.pWvec wvec ⋆ array (t := i32) c.pArena arena ⋆
    array (t := i32) c.pWstk wstk ⋆ array (t := i32) c.pMinStk mstk
  let H4 := array64 c.pScore score ⋆ array (t := i32) c.pWsort wsort ⋆
    array (t := i32) c.pRedRefs rr ⋆ array (t := i32) c.pGlueUsed gu ⋆
    array (t := i32) c.pDelayed del
  have hr4' : (((array (t := i32) c.pWvec wvec ⋆ array (t := i32) c.pWsort wsort ⋆
      array64 c.pScore score ⋆ array (t := i32) c.pMinStk mstk ⋆
      array (t := i32) c.pGlueUsed gu ⋆ array (t := i32) c.pArena arena ⋆
      array (t := i32) c.pWstk wstk ⋆ array (t := i32) c.pDelayed del ⋆
      array (t := i32) c.pRedRefs rr) ⋆ region c.pSlack c.slack) ⋆
    (((array (t := i32) c.pPos pos ⋆ array (t := i32) c.pMinClr mclr ⋆
      array (t := i32) c.pShrinkStk sstk ⋆ array (t := i32) c.pQPrev qp ⋆
      array (t := i32) c.pQNext qn ⋆ array (t := i32) c.pQStamp qs) ⋆ c.padU32B) ⋆
    (((array (t := i32) c.pLevel lvl ⋆ array (t := i32) c.pReason rsns ⋆
      array (t := i32) c.pTrail trl ⋆ array (t := i32) c.pTrailPos tpos ⋆
      array (t := i32) c.pTmp tmp ⋆ array (t := i32) c.pHeap heap) ⋆ c.padU32A) ⋆
    ((array (t := i8) c.pVals vals ⋆ array (t := i8) c.pMark mrk ⋆
      array (t := i8) c.pPhases ph ⋆ array (t := i8) c.pPhasesTarget ptgt ⋆
      array (t := i8) c.pPhasesBest pbst) ⋆ c.padMarks)))) m := hr4
  have hg : ((C4 ⋆ H4 ⋆ region c.pSlack c.slack) ⋆
      ((C3 ⋆ H3 ⋆ c.padU32B) ⋆ ((C2 ⋆ H2 ⋆ c.padU32A) ⋆ (C1 ⋆ H1 ⋆ c.padMarks)))) m :=
    sep_mono2 (fun _ h => by dsimp only [C4, H4]; exact sep_ac h)
      (sep_mono2 (fun _ h => by dsimp only [C3, H3]; exact sep_ac h)
        (sep_mono2 (fun _ h => by dsimp only [C2, H2]; exact sep_ac h)
          (fun _ h => by dsimp only [C1, H1]; exact sep_ac h))) m hr4'
  have hc : (((C1 ⋆ C2 ⋆ C4 ⋆ C3) ⋆ (H1 ⋆ H2 ⋆ H3 ⋆ H4)) ⋆
      (c.padMarks ⋆ c.padU32A ⋆ c.padU32B ⋆ region c.pSlack c.slack)) m := sep_ac hg
  refine sep_mono2 (sep_mono2 (fun _ h => ?_) (fun _ h => ?_)) (fun _ h => h) m hc
  · unfold PlainCoreArrays initPreState; dsimp only [C1, C2, C3, C4] at h; exact sep_ac h
  · unfold PlainHeurArrays initPreState; dsimp only [H1, H2, H3, H4] at h; exact sep_ac h

/-! ## 2. `plain_zero_tables` -/

private theorem replicate_of_getElem? {α : Type _} {xs : List α} {n : Nat} {v : α}
    (hlen : xs.length = n) (hall : ∀ k < n, xs[k]? = some v) : xs = List.replicate n v := by
  refine List.ext_getElem (by simp [hlen]) fun k hk _ => ?_
  have h := hall k (hlen ▸ hk); rw [List.getElem?_eq_getElem hk] at h
  simpa [List.getElem_replicate] using Option.some.inj h

private theorem forall_lt_set {α : Type _} {xs : List α} {i : Nat} {v : α}
    (hi : i < xs.length) (hall : ∀ k < i, xs[k]? = some v) :
    ∀ k < i + 1, (xs.set i v)[k]? = some v := fun k hk => by
  by_cases hki : k = i
  · subst hki; exact List.getElem?_set_self hi
  · rw [List.getElem?_set_ne (Ne.symm hki)]; exact hall k (by omega)

private theorem forall_lt_set2 {α : Type _} {xs : List α} {i : Nat} {v : α}
    (hi : 2 * i + 1 < xs.length) (hall : ∀ k < 2 * i, xs[k]? = some v) :
    ∀ k < 2 * (i + 1), ((xs.set (2 * i) v).set (2 * i + 1) v)[k]? = some v := fun k hk => by
  by_cases hk1 : k = 2 * i + 1
  · subst hk1; exact List.getElem?_set_self (by simp; exact hi)
  · rw [List.getElem?_set_ne (Ne.symm hk1)]; exact forall_lt_set (by omega) hall k (by omega)

private theorem zero_tables_loop2_step {c : PlainCfg} {s1 st : PlainState} {v : Nat}
    (v32 qv nv qs32 : BitVec 32) (hv : v < c.mv) (hlok : st.LengthsOk c)
    (hag : st = { s1 with
      mrk := st.mrk, lvl := st.lvl, rsns := st.rsns,
      trail_pos := st.trail_pos, tmp := st.tmp, min_clr := st.min_clr, heur := st.heur })
    (hall : ∀ k < v, st.mrk[k]? = some 0#8 ∧ st.lvl[k]? = some 0#32 ∧
      st.rsns[k]? = some 0xFFFFFFFF#32 ∧ st.trail_pos[k]? = some 0#32 ∧
      st.tmp[k]? = some 0#32 ∧ st.min_clr[k]? = some 0#32) :
    let h0 := st.heur
    let hr' : PlainHeur := { h0 with
      phases := h0.phases.set v 1#8, phases_target := h0.phases_target.set v 0#8,
      phases_best := h0.phases_best.set v 0#8, heap := h0.heap.set v v32,
      pos := h0.pos.set v v32, shrink_stk := h0.shrink_stk.set v 0#32,
      q_prev := h0.q_prev.set v qv, q_next := h0.q_next.set v nv,
      q_stamp := h0.q_stamp.set v qs32,
      score := h0.score.set v 0#64 }
    let st' : PlainState := { st with
      mrk := st.mrk.set v 0#8, lvl := st.lvl.set v 0#32, rsns := st.rsns.set v 0xFFFFFFFF#32,
      trail_pos := st.trail_pos.set v 0#32, tmp := st.tmp.set v 0#32,
      min_clr := st.min_clr.set v 0#32, heur := hr' }
    v + 1 ≤ c.mv ∧ st' = { s1 with
      mrk := st'.mrk, lvl := st'.lvl, rsns := st'.rsns, trail_pos := st'.trail_pos,
      tmp := st'.tmp, min_clr := st'.min_clr, heur := hr' } ∧
    st'.LengthsOk c ∧ hr'.rel_trigger = h0.rel_trigger ∧
    ∀ k < v + 1, st'.mrk[k]? = some 0#8 ∧ st'.lvl[k]? = some 0#32 ∧
      st'.rsns[k]? = some 0xFFFFFFFF#32 ∧ st'.trail_pos[k]? = some 0#32 ∧
      st'.tmp[k]? = some 0#32 ∧ st'.min_clr[k]? = some 0#32 := by
  intro h0 hr' st'; have hh := hlok.heur_ok
  have hhr' : hr'.LengthsOk c :=
    { hh with
      heap_len_arr := by simp [hr', h0, hh.heap_len_arr],
      pos_len := by simp [hr', h0, hh.pos_len], score_len := by simp [hr', h0, hh.score_len],
      phases_len := by simp [hr', h0, hh.phases_len],
      phases_target_len := by simp [hr', h0, hh.phases_target_len],
      phases_best_len := by simp [hr', h0, hh.phases_best_len],
      shrink_stk_len := by simp [hr', h0, hh.shrink_stk_len],
      q_prev_len := by simp [hr', h0, hh.q_prev_len],
      q_next_len := by simp [hr', h0, hh.q_next_len],
      q_stamp_len := by simp [hr', h0, hh.q_stamp_len] }
  refine ⟨by omega, congrArg (fun x => { x with
      mrk := st'.mrk, lvl := st'.lvl, rsns := st'.rsns, trail_pos := st'.trail_pos,
      tmp := st'.tmp, min_clr := st'.min_clr, heur := hr' }) hag,
    { hlok with
      mrk_len := by simp [st', hlok.mrk_len], lvl_len := by simp [st', hlok.lvl_len],
      rsns_len := by simp [st', hlok.rsns_len],
      trail_pos_len := by simp [st', hlok.trail_pos_len],
      tmp_len_arr := by simp [st', hlok.tmp_len_arr],
      min_clr_len_arr := by simp [st', hlok.min_clr_len_arr], heur_ok := hhr' }, rfl,
    fun k hk => ?_⟩
  by_cases hke : k = v
  · subst hke
    exact ⟨List.getElem?_set_self (by rw [hlok.mrk_len]; exact hv),
      List.getElem?_set_self (by rw [hlok.lvl_len]; exact hv),
      List.getElem?_set_self (by rw [hlok.rsns_len]; exact hv),
      List.getElem?_set_self (by rw [hlok.trail_pos_len]; exact hv),
      List.getElem?_set_self (by rw [hlok.tmp_len_arr]; exact hv),
      List.getElem?_set_self (by rw [hlok.min_clr_len_arr]; exact hv)⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hall k (by omega)
    simp only [st', List.getElem?_set_ne (Ne.symm hke)]; exact ⟨h1, h2, h3, h4, h5, h6⟩

private abbrev zSt (st : PlainState) (v32 : BitVec 32) (v : Nat) (qv? nv? : Option (BitVec 32)) :
    PlainState :=
  let h0 := st.heur
  let h1 := { h0 with
    phases := h0.phases.set v 1#8, phases_target := h0.phases_target.set v 0#8,
    phases_best := h0.phases_best.set v 0#8,
    heap := h0.heap.set v v32, pos := h0.pos.set v v32,
    shrink_stk := h0.shrink_stk.set v 0#32 }
  let h2 := match qv?, nv? with
    | some qv, some nv => { h1 with q_prev := h1.q_prev.set v qv, q_next := h1.q_next.set v nv }
    | some qv, none => { h1 with q_prev := h1.q_prev.set v qv }
    | _, _ => h1
  { st with
    mrk := st.mrk.set v 0#8, lvl := st.lvl.set v 0#32, rsns := st.rsns.set v 0xFFFFFFFF#32,
    trail_pos := st.trail_pos.set v 0#32, tmp := st.tmp.set v 0#32,
    min_clr := st.min_clr.set v 0#32, heur := h2 }

private def ZeroTablesPost (c : PlainCfg) (s : PlainState) (R : Mem 64 → Prop)
    (Q : Tup Val [] → Mem 64 → Prop) : Prop :=
  ∀ (wstk' mstk' : List (BitVec 32)) (hr' : PlainHeur) (m' : Mem 64),
    wstk'.length = c.wcap → mstk'.length = 2 * c.minDepth → hr'.LengthsOk c →
    hr'.rel_trigger = s.heur.rel_trigger →
    (PlainMem c { s with
      vals := List.replicate (2 * c.mv) 0#8, mrk := List.replicate c.mv 0#8,
      lvl := List.replicate c.mv 0#32, rsns := List.replicate c.mv 0xFFFFFFFF#32,
      trail_pos := List.replicate c.mv 0#32, tmp := List.replicate c.mv 0#32,
      wvec := List.replicate (4 * c.mv) 0#32, wstk := wstk', min_stk := mstk',
      min_clr := List.replicate c.mv 0#32, heur := hr' } ⋆ R) m' → Q () m'

local macro "pi_zload" hm:ident lem:ident : tactic => `(tactic|
  (pi_shallow_lets; refine wp_load_of ($lem $hm:ident) ?_))

local macro "pi_zstore" lem:ident hf:ident : tactic => do
  let hmId := Lean.mkIdent `hm
  `(tactic| (
    pi_shallow_lets
    apply wp_store_sep
    · refine $lem _ ?_ (by assumption)
      try dsimp only
      rw [$hf:ident]
      assumption
    intro _ $hmId:ident))

theorem plain_zero_tables_wp (Γ : Env) :
    ∀ a m Q X, plainZeroTablesSpec a m Q X → Func.wp Γ plain_zero_tables_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen0, hm0, hQ⟩
  have hPost : ZeroTablesPost c s R Q := hQ
  clear hQ
  have hmv := c.hmv; have hwcap := c.hwcap
  have hcm_eq : c.minDepth = plainMinDepthOf c.mv := rfl
  have hmd : c.minDepth ≤ 1000 := hcm_eq ▸ plainMinDepthOf_le c.mv
  unfold dimacsBound at hmv hwcap
  pi_shallow_steps
  refine wp_loop_inv (fun (iv : Tup Val [i64]) m1 => ∃ st1 : PlainState,
      iv.1.toNat ≤ 2 * c.mv ∧ st1 = { s with vals := st1.vals, wvec := st1.wvec } ∧
      st1.vals.length = 2 * c.mv ∧ st1.wvec.length = 4 * c.mv ∧
      (∀ k < iv.1.toNat, st1.vals[k]? = some 0#8) ∧
      (∀ k < 2 * iv.1.toNat, st1.wvec[k]? = some 0#32) ∧ (PlainMem c st1 ⋆ R) m1)
    (fun iv _ => 2 * c.mv - iv.1.toNat) ?_ ?_
  · intro L1 hL1; pi_shallow_steps; exact hL1 (0#64, ()) m ⟨s, Nat.zero_le _, rfl,
      hlen0.vals_len, hlen0.wvec_len, (fun _ h => by cases h), (fun _ h => by cases h), hm0⟩
  · intro L1 ⟨iv, ⟨⟩⟩ m1 ⟨st1, hi, hag1, hvl, hwl, hvk, hwk, hm1⟩ hL1
    dsimp only at hi hvk hwk
    p_lets; refine wp_head_jnz_iff (b := decide (iv.toNat < 2 * c.mv)) (by
      simp only [Arg.val_var]; rw [bv64_shl1_nat_eq, ← bv_ofNat_toNat_eq iv,
        bv_ult_eq (by omega) (by omega), bv64_ofNat_toNat iv.isLt]) ?_
    rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun hilt => ?_, fun hige => ?_⟩
    · pi_shallow_steps
      have hi1 : (iv + 1#64).toNat = iv.toNat + 1 := by clear hm hPost; simp only [bv_c0]; omega
      rw [show (iv <<< 1).toNat = 2 * iv.toNat by clear hm hPost; bv_omega,
        show (iv <<< (1 : Nat) + 1).toNat = 2 * iv.toNat + 1 by
          clear hm hPost; bv_omega] at hm
      exact hL1 (iv + 1#64, ()) _ (by dsimp only; rw [hi1]; omega)
        ⟨_, by dsimp only; rw [hi1]; omega, congrArg (fun x => { x with
            vals := st1.vals.set iv.toNat 0#8,
            wvec := (st1.wvec.set (2 * iv.toNat) 0#32).set (2 * iv.toNat + 1) 0#32 }) hag1,
          by simp [hvl], by simp [hwl],
          (by dsimp only; rw [hi1]; exact forall_lt_set (by rw [hvl]; exact hilt) hvk),
          (by dsimp only; rw [hi1]; exact forall_lt_set2 (by rw [hwl]; omega) hwk), hm⟩
    · have hieq : iv.toNat = 2 * c.mv := by omega
      rw [hieq] at hvk hwk
      let s2 : PlainState := { s with
        vals := List.replicate (2 * c.mv) 0#8, wvec := List.replicate (4 * c.mv) 0#32 }
      have hs2_eq : st1 = s2 := by
        rw [hag1, replicate_of_getElem? hvl hvk,
          replicate_of_getElem? hwl fun k hk => hwk k (by omega)]
      rw [hs2_eq] at hm1
      have hwlen0 : s2.wstk.length = c.wcap := hlen0.wstk_len_arr
      p_lets; refine wp_load_of (load_arena_watch_stk hm1) ?_; p_lets
      refine wp_join_group (ts := []) (fun () m2 => ∃ wstk2, wstk2.length = c.wcap ∧
          (PlainMem c { s2 with wstk := wstk2 } ⋆ R) m2) ?_ ?_
      · rintro _ ⟨⟩ m2 ⟨wstk2, hwk2, hm2⟩
        let s3 : PlainState := { s2 with wstk := wstk2 }
        have hlen3 : s3.LengthsOk c :=
          { hlen0 with
            vals_len := by simp [s3, s2], wvec_len := by simp [s3, s2], wstk_len_arr := hwk2 }
        pi_zload hm2 load_arena_mark; pi_zload hm2 load_arena_phases_ptr
        pi_zload hm2 load_arena_phases_target_ptr; pi_zload hm2 load_arena_phases_best_ptr
        pi_zload hm2 load_arena_level; pi_zload hm2 load_arena_reason
        pi_zload hm2 load_arena_tmp_lits; pi_zload hm2 load_arena_heap_ptr
        pi_zload hm2 load_arena_pos_ptr; pi_zload hm2 load_arena_min_clr_ptr
        pi_zload hm2 load_arena_shrink_stk_ptr; pi_zload hm2 load_arena_trail_pos
        pi_zload hm2 load_arena_q_prev; pi_zload hm2 load_arena_q_next
        pi_zload hm2 load_arena_q_stamp; pi_zload hm2 load_arena_score_ptr
        pi_shallow_steps
        refine wp_loop_inv (fun (vv : Tup Val [i64]) ml => ∃ st2 : PlainState,
            vv.1.toNat ≤ c.mv ∧ st2 = { s3 with
              mrk := st2.mrk, lvl := st2.lvl, rsns := st2.rsns, trail_pos := st2.trail_pos,
              tmp := st2.tmp, min_clr := st2.min_clr, heur := st2.heur } ∧
            st2.LengthsOk c ∧ st2.heur.rel_trigger = s.heur.rel_trigger ∧
            (∀ k < vv.1.toNat, st2.mrk[k]? = some 0#8 ∧ st2.lvl[k]? = some 0#32 ∧
              st2.rsns[k]? = some 0xFFFFFFFF#32 ∧ st2.trail_pos[k]? = some 0#32 ∧
              st2.tmp[k]? = some 0#32 ∧ st2.min_clr[k]? = some 0#32) ∧
            (PlainMem c st2 ⋆ R) ml) (fun vv _ => c.mv - vv.1.toNat) ?_ ?_
        · intro L2 hL2; pi_shallow_steps; exact hL2 (0#64, ()) _
            ⟨s3, Nat.zero_le _, rfl, hlen3, rfl, (fun _ h => by cases h), hm2⟩
        · intro L2 ⟨vv, ⟨⟩⟩ ml ⟨st2, hvle, hag2, hln, hrel, hall2, hml⟩ hL2
          dsimp only at hvle hall2
          have hhk : st2.heur.LengthsOk c := hln.heur_ok
          p_lets; refine wp_head_jnz_iff (b := decide (vv.toNat < c.mv))
            (by simp only [Arg.val_var]; rw [← bv_ofNat_toNat_eq vv, bv_ult_eq (by omega)
              (by omega), bv64_ofNat_toNat vv.isLt]) ?_
          rw [decide_eq_true_eq, decide_eq_false_iff_not]; refine ⟨fun hvlt => ?_, fun hvge => ?_⟩
          · have hv1 : (vv + 1#64).toNat = vv.toNat + 1 := by
              clear hml hPost; simp only [bv_c0]; omega
            have hl1 := hln.mrk_len; have hl2 := hln.lvl_len; have hl3 := hln.rsns_len
            have hl4 := hln.trail_pos_len; have hl5 := hln.tmp_len_arr
            have hl6 := hln.min_clr_len_arr
            have hh1 := hhk.phases_len; have hh2 := hhk.phases_target_len
            have hh3 := hhk.phases_best_len; have hh4 := hhk.heap_len_arr
            have hh5 := hhk.pos_len; have hh6 := hhk.shrink_stk_len
            have hh7 := hhk.q_prev_len; have hh8 := hhk.q_next_len
            have hh9 := hhk.q_stamp_len; have hh10 := hhk.score_len
            pi_zstore c0_store_arena_mrk hl1
            pi_zstore c0_store_arena_phases hh1
            pi_zstore c0_store_arena_phases_target hh2
            pi_zstore c0_store_arena_phases_best hh3
            pi_zstore c0_store_arena_lvl hl2
            pi_zstore c0_store_arena_rsns hl3
            pi_zstore c0_store_arena_tmp hl5
            pi_zstore c0_store_arena_heap hh4
            pi_zstore c0_store_arena_pos hh5
            pi_zstore c0_store_arena_min_clr hl6
            pi_zstore c0_store_arena_shrink_stk hh6
            pi_zstore c0_store_arena_tpos hl4
            pi_shallow_lets
            refine wp_join_group (ts := [i32]) (fun (_, ()) mq =>
                (PlainMem c (zSt st2 (vv.setWidth 32) vv.toNat none none) ⋆ R) mq) ?_ ?_
            · rintro _ ⟨qv, ⟨⟩⟩ mq hmq
              clear hm; pi_zstore c0_store_arena_q_prev_arr hh7; pi_shallow_lets
              refine wp_join_group (ts := [i32]) (fun (_, ()) mn =>
                  (PlainMem c (zSt st2 (vv.setWidth 32) vv.toNat (some qv) none) ⋆ R) mn) ?_ ?_
              · rintro _ ⟨nv, ⟨⟩⟩ mn hmn
                clear hm
                pi_zstore c0_store_arena_q_next_arr hh8
                pi_zstore c0_store_arena_q_stamp_arr hh9
                pi_zstore c0_store_arena_score hh10
                pi_shallow_lets
                obtain ⟨hv1_le, hag2', hln', hrt', hall2'⟩ := zero_tables_loop2_step
                  (vv.setWidth 32) qv nv ((vv + 1#64).setWidth 32) hvlt hln hag2 hall2
                have hdec : c.mv - (vv + 1#64, ()).1.toNat < c.mv - vv.toNat := by
                  dsimp only; rw [hv1]; exact Nat.sub_lt_sub_left hvlt (Nat.lt_succ_self _)
                refine hL2 (vv + 1#64, ()) _ hdec
                  ⟨_, by dsimp only; rw [hv1]; exact hv1_le, hag2', hln', hrt'.trans hrel,
                    (by dsimp only; rw [hv1]; exact hall2'), ?_⟩
                exact hm
              · intro Jn hJn; pi_shallow_steps
                refine wp_jnz_of (fun _ => ?_) (fun _ => ?_) <;>
                  (pi_shallow_steps; exact hJn _ _ hm)
            · intro Jq hJq; pi_shallow_steps
              refine wp_jnz_of (fun _ => ?_) (fun _ => ?_) <;>
                (pi_shallow_steps; exact hJq _ _ hm)
          · have hveq : vv.toNat = c.mv := by omega
            rw [hveq] at hall2
            let hr2 := st2.heur
            let s_z2 : PlainState :=
              { s with
                vals := List.replicate (2 * c.mv) 0#8, wvec := List.replicate (4 * c.mv) 0#32,
                wstk := wstk2, mrk := List.replicate c.mv 0#8, lvl := List.replicate c.mv 0#32,
                rsns := List.replicate c.mv 0xFFFFFFFF#32, trail_pos := List.replicate c.mv 0#32,
                tmp := List.replicate c.mv 0#32, min_clr := List.replicate c.mv 0#32,
                heur := hr2 }
            have hs4_eq : st2 = s_z2 := by
              have hmrk := replicate_of_getElem? hln.mrk_len fun k hk => (hall2 k hk).1
              have hlvl := replicate_of_getElem? hln.lvl_len fun k hk => (hall2 k hk).2.1
              have hrsn := replicate_of_getElem? hln.rsns_len fun k hk => (hall2 k hk).2.2.1
              have htp := replicate_of_getElem? hln.trail_pos_len fun k hk => (hall2 k hk).2.2.2.1
              have htm := replicate_of_getElem? hln.tmp_len_arr fun k hk => (hall2 k hk).2.2.2.2.1
              have hmc :=
                replicate_of_getElem? hln.min_clr_len_arr fun k hk => (hall2 k hk).2.2.2.2.2
              change st2 = s_z2; rw [hag2]; dsimp only [s_z2, s3, s2]
              rw [hmrk, hlvl, hrsn, htp, htm, hmc]
            rw [hs4_eq] at hml; pi_shallow_steps
            refine wp_loop_inv (fun (kv : Tup Val [i64]) m3 => ∃ mstk3,
                kv.1.toNat ≤ 2 * c.minDepth ∧ mstk3.length = 2 * c.minDepth ∧
                (PlainMem c { s_z2 with min_stk := mstk3 } ⋆ R) m3)
              (fun kv _ => 2 * c.minDepth - kv.1.toNat) ?_ ?_
            · intro L3 hL3; pi_shallow_steps
              exact hL3 (0#64, ()) ml ⟨s.min_stk, Nat.zero_le _, hlen0.min_stk_len, hml⟩
            · intro L3 ⟨kv, ⟨⟩⟩ m3 ⟨mstk3, hk3, hmsl3, hm3⟩ hL3
              dsimp only at hk3
              p_lets
              have hmcnt_eq : (BitVec.ofNat 64 c.minDepth <<< (1 : Nat)) =
                  BitVec.ofNat 64 (2 * c.minDepth) := bv64_shl1_nat_eq
              refine wp_head_jnz_iff (b := decide (kv.toNat < 2 * c.minDepth)) (by
                simp only [Arg.val_var]; rw [hmcnt_eq, ← bv_ofNat_toNat_eq kv,
                  bv_ult_eq (by omega) (by omega), bv64_ofNat_toNat kv.isLt]) ?_
              rw [decide_eq_true_eq, decide_eq_false_iff_not]
              refine ⟨fun hklt => ?_, fun hkge => ?_⟩
              · pi_shallow_steps
                have hk1 : (kv + 1#64).toNat = kv.toNat + 1 := by
                  clear hPost; simp only [bv_c0]; omega
                exact hL3 (kv + 1#64, ()) _ (by dsimp only; rw [hk1]; omega)
                  ⟨mstk3.set kv.toNat 0#32, by dsimp only; rw [hk1]; omega, by simp [hmsl3], hm⟩
              · pi_shallow_steps
                refine wp_loop_inv (fun (kv4 : Tup Val [i64]) m4 => ∃ gu4, kv4.1.toNat ≤ 64 ∧
                      gu4.length = 64 ∧ (PlainMem c { s_z2 with
                        heur := { st2.heur with glue_used := gu4 }, min_stk := mstk3 } ⋆ R) m4)
                    (fun kv4 _ => 64 - kv4.1.toNat) ?_ ?_
                · intro L4 hL4; pi_shallow_steps
                  exact hL4 (0#64, ()) _ ⟨st2.heur.glue_used, Nat.zero_le _, hhk.glue_used_len, hm3⟩
                · intro L4 ⟨kv4, ⟨⟩⟩ m4 ⟨gu4, hk4, hgul4, hm4⟩ hL4
                  dsimp only at hk4; p_lets
                  refine wp_head_jnz_iff (b := decide (kv4.toNat < 64)) (by
                    simp only [Arg.val_var, show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl]
                    rw [← bv_ofNat_toNat_eq kv4, bv_ult_eq (by omega) (by decide),
                      bv64_ofNat_toNat kv4.isLt]) ?_
                  rw [decide_eq_true_eq, decide_eq_false_iff_not]
                  refine ⟨fun hk4lt => ?_, fun hk4ge => ?_⟩
                  · pi_shallow_steps
                    have hk41 : (kv4 + 1#64).toNat = kv4.toNat + 1 := by
                      clear hPost; simp only [bv_c0]; omega
                    exact hL4 (kv4 + 1#64, ()) _ (by dsimp only; rw [hk41]; omega)
                      ⟨gu4.set kv4.toNat 0#32, by dsimp only; rw [hk41]; omega,
                        by simp [hgul4], hm⟩
                  · pi_shallow_steps
                    exact hPost wstk2 mstk3 { st2.heur with glue_used := gu4 } m4 hwk2 hmsl3
                      { hhk with glue_used_len := hgul4 } hrel hm4
      · intro Jw hJw; pi_shallow_steps
        refine wp_jnz_of (fun hgt => ?_) (fun _ => ?_)
        · have hwpos : 0 < c.wcap := by
            clear hm1 hPost; simp only [Arg.val_var, bv_c0] at hgt; omega
          pi_shallow_steps; exact hJw () _ ⟨s2.wstk.set 0 0#32, by simp [hwlen0], hm⟩
        · pi_shallow_steps; exact hJw () _ ⟨s2.wstk, hwlen0, hm1⟩

/-! ## 3. `plain_init_state` -/

private theorem len_cons10 {α} (xs : List α) (n : Nat) (h : xs.length = n + 10) :
    ∃ a b c d e f g h1 i j ys, ys.length = n ∧
      xs = a :: b :: c :: d :: e :: f :: g :: h1 :: i :: j :: ys := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h1, _ | ⟨i, _ |
    ⟨j, ys⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨a, b, c, d, e, f, g, h1, i, j, ys, h, rfl⟩

private theorem init_state_split_arena (c : PlainCfg) (fuel : BitVec 64) {cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {j : Nat} {R : Mem 64 → Prop} {m0 : Mem 64} (hav768 : 768 ≤ c.avail)
    (hm0 : (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr (BitVec.ofNat 64 c.mv)
        (BitVec.ofNat 64 c.nc) (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) ⋆
        (region (c.hdr + 32#64) (c.avail - 32) ⋆ R)) m0) :
    ∃ (ws : List (BitVec 64)) (a : InitArrs c), ws.length = 92 ∧ (hdrTail92 c.hdr ws ⋆
        (PlainCoreArrays c (initPreState c (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc)
          fuel a) ⋆ PlainHeurArrays c (initPreState c (cnf_ptr + BitVec.ofNat 64 j)
            (BitVec.ofNat 64 c.nc) fuel a).heur ⋆ c.pad ⋆ bytes cnf_ptr cnfBytes ⋆
          dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
            (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) ⋆ R)) m0 := by
  have hav_le := c.havail_fit
  have h1 : (region (c.hdr + 32#64) (c.avail - 32) ⋆
      (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) ⋆ R)) m0 := sep_ac hm0
  rw [← region_merge_eq (a := c.hdr + 32#64) (n1 := 736) (n2 := c.avail - 768) (n := c.avail - 32)
      (by omega) (by omega), ptr_add_ofNat, show (32 + 736 : Nat) = 768 from rfl] at h1
  have h1' : (region (c.hdr + 32#64) 736 ⋆
      (region (c.hdr + BitVec.ofNat 64 768) (c.avail - 768) ⋆
        (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
          (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) ⋆ R))) m0 := sep_ac h1
  obtain ⟨ws, hwl, h2⟩ := sep_arr_i64_l 92 h1' (by decide) (by decide)
  obtain ⟨a, h3⟩ := sep_ex_l.mp (sep_mono_mid h2 (fun _ h => avail_to_initArrs c h))
  have h3' : ((PlainCoreArrays c (initPreState c 0#64 0#64 0#64 a) ⋆
      PlainHeurArrays c (initPreState c 0#64 0#64 0#64 a).heur ⋆ c.pad) ⋆
      (array64 (c.hdr + 32) ws ⋆ (bytes cnf_ptr cnfBytes ⋆
        dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
          (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) ⋆ R))) m0 := h3
  have hca : PlainCoreArrays c (initPreState c 0#64 0#64 0#64 a) = PlainCoreArrays c
      (initPreState c (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) fuel a) := rfl
  have hha : PlainHeurArrays c (initPreState c 0#64 0#64 0#64 a).heur = PlainHeurArrays c
      (initPreState c (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) fuel a).heur := rfl
  rw [hca, hha] at h3'
  have h4 : (hdrTail92 c.hdr ws ⋆
      (PlainCoreArrays c (initPreState c (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc)
        fuel a) ⋆ PlainHeurArrays c (initPreState c (cnf_ptr + BitVec.ofNat 64 j)
          (BitVec.ofNat 64 c.nc) fuel a).heur ⋆ c.pad ⋆ bytes cnf_ptr cnfBytes ⋆
        dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
          (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) ⋆ R)) m0 := by
    unfold hdrTail92
    exact sep_pure_l.mpr ⟨hwl, sep_ac h3'⟩
  exact ⟨ws, a, hwl, h4⟩

private theorem init_hdrtail_norm (c : PlainCfg) (d_cur d_val fuel : BitVec 64)
    (a : InitArrs c) (ws : List (BitVec 64)) (hwl : ws.length = 92) (rem : Nat)
    (hap : c.arena_cap = 2 * plainInitArenaPairs rem)
    (hwp : c.wcap = 2 * plainInitWPairs rem) (hdel : plainInitDelCap rem = c.delayed_cap)
    (hrp : c.red_cap = 2 * plainInitRedPairs rem) :
    let vb := (BitVec.ofNat 64 c.mv <<< (1 : Nat) + 7) &&& ~~~7
    let mb := (BitVec.ofNat 64 c.mv + 7) &&& ~~~7
    let ub := (BitVec.ofNat 64 c.mv <<< (2 : Nat) + 7) &&& ~~~7
    let sb := BitVec.ofNat 64 c.mv <<< (3 : Nat)
    let wb := (BitVec.ofNat 64 c.mv <<< (1 : Nat)) <<< (3 : Nat)
    let db := BitVec.ofNat 64 (plainMinDepthOf c.mv) <<< (3 : Nat)
    let acBV := BitVec.ofNat 64 (plainInitArenaPairs rem) <<< (1 : Nat)
    let wcBV := BitVec.ofNat 64 (plainInitWPairs rem) <<< (1 : Nat)
    let rcBV := BitVec.ofNat 64 (plainInitRedPairs rem) <<< (1 : Nat)
    let dlB := BitVec.ofNat 64 (plainInitDelCap rem) * (12 : BitVec 64)
    let p0 := c.hdr + 768; let p1 := p0 + vb; let p2 := p1 + mb; let p3 := p2 + mb
    let p4 := p3 + mb; let p5 := p4 + mb; let p6 := p5 + ub; let p7 := p6 + ub
    let p8 := p7 + ub; let p9 := p8 + ub; let p10 := p9 + ub; let p11 := p10 + ub
    let p12 := p11 + ub; let p13 := p12 + ub; let p14 := p13 + ub; let p15 := p14 + ub
    let p16 := p15 + ub; let p17 := p16 + ub; let p18 := p17 + wb; let p19 := p18 + sb
    let p20 := p19 + sb; let p21 := p20 + db; let p22 := p21 + 256
    let p23 := p22 + (acBV <<< (2 : Nat)); let p24 := p23 + (wcBV <<< (2 : Nat))
    let p25 := p24 + dlB
    let qF := if c.mv = 0 then 0xFFFFFFFF#64 else 0#64
    let qL := if c.mv = 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (c.mv - 1)
    ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((
      (ws.set 4 p0).set 5 p1).set 24 p2).set 45 p3).set 46 p4).set 6 p5).set 7 p6).set
      8 p7).set 41 p8).set 13 p9).set 21 p10).set 22 p11).set 26 p12).set 48 p13).set
      42 p14).set 43 p15).set 44 p16).set 9 p17).set 47 p18).set 23 p19).set 25 p20).set
      50 p21).set 10 p22).set 11 p23).set 12 p24).set 49 p25).set 0 acBV).set 1 wcBV).set
      51 rcBV).set 52 (BitVec.ofNat 64 (plainInitDelCap rem))).set 53 0).set 2 0).set 3 1).set
      54 0).set 55 0).set 56 4294967295).set 57 0).set 58 0).set 59 0).set 60 0).set 61 0).set
      14 0).set 15 0).set 16 0).set 17 fuel).set 18 4294967295).set 62 0).set 63 0).set 64 0).set
      19 0).set 20 0).set 27 (BitVec.ofNat 64 c.mv)).set 28 268435456#64).set
      29 (BitVec.ofNat 64 (plainMinDepthOf c.mv))).set 30 0).set 31 0).set 32 1024).set
      33 1048576).set 34 1024).set 35 1).set 36 1).set 37 0).set 38 0).set 39 0).set 40 0).set
      65 0).set 66 0).set 67 0).set 68 1000).set 69 0).set 70 0).set 71 0).set 72 qF).set
      73 qL).set 74 qL).set 75 (BitVec.ofNat 64 c.mv)).set 76 (BitVec.ofNat 64 c.mv)).set
      77 0).set 78 0).set 79 1000).set 80 0).set 81 1000).set 82 0).set 83 2).set 84 6).set
      85 0).set 86 1).set 87 0).set 88 16777216#64).set 89 0).set 90 16777216#64).set 91 0 =
    hdrTailWords c (initPreState c d_cur d_val fuel a) := by
  have hmv := c.hmv; unfold dimacsBound at hmv; have hmd := plainMinDepthOf_le c.mv; dsimp only
  have hvb : (BitVec.ofNat 64 c.mv <<< (1 : Nat) + 7) &&& ~~~7 =
      BitVec.ofNat 64 (valsBytes c.mv) := by
    rw [bv64_shl1_nat_eq, bv64_align8 (n := 2 * c.mv) (by omega)]; rfl
  have hmb : (BitVec.ofNat 64 c.mv + 7) &&& ~~~7 = BitVec.ofNat 64 (markBytes c.mv) := by
    simpa [markBytes] using bv64_align8 (n := c.mv) (by omega)
  have hub : (BitVec.ofNat 64 c.mv <<< (2 : Nat) + 7) &&& ~~~7 =
      BitVec.ofNat 64 (u32VarBytes c.mv) := by
    rw [bv64_shl2_nat, bv64_align8 (n := 4 * c.mv) (by omega)]; rfl
  have hac : BitVec.ofNat 64 (plainInitArenaPairs rem) <<< (1 : Nat) =
      BitVec.ofNat 64 c.arena_cap := by rw [bv64_shl1_nat_eq, hap]
  have hwc : BitVec.ofNat 64 (plainInitWPairs rem) <<< (1 : Nat) =
      BitVec.ofNat 64 c.wcap := by rw [bv64_shl1_nat_eq, hwp]
  have hrc : BitVec.ofNat 64 (plainInitRedPairs rem) <<< (1 : Nat) =
      BitVec.ofNat 64 c.red_cap := by rw [bv64_shl1_nat_eq, hrp]
  rw [hvb, hmb, hub, hac, hwc, hrc, hdel]
  simp only [bv64_shl1_nat_eq, bv64_shl3_nat, bv64_shl2_nat, bv64_mul12]
  rw [show c.hdr + (768 : BitVec 64) = c.pVals from rfl,
    show c.pVals + BitVec.ofNat 64 (valsBytes c.mv) = c.pMark from rfl,
    show c.pMark + BitVec.ofNat 64 (markBytes c.mv) = c.pPhases from rfl,
    show c.pPhases + BitVec.ofNat 64 (markBytes c.mv) = c.pPhasesTarget from rfl,
    show c.pPhasesTarget + BitVec.ofNat 64 (markBytes c.mv) = c.pPhasesBest from rfl,
    show c.pPhasesBest + BitVec.ofNat 64 (markBytes c.mv) = c.pLevel from rfl,
    show c.pLevel + BitVec.ofNat 64 (u32VarBytes c.mv) = c.pReason from rfl,
    show c.pReason + BitVec.ofNat 64 (u32VarBytes c.mv) = c.pTrail from rfl,
    show c.pTrail + BitVec.ofNat 64 (u32VarBytes c.mv) = c.pTrailPos from rfl,
    show c.pTrailPos + BitVec.ofNat 64 (u32VarBytes c.mv) = c.pTmp from rfl,
    show c.pTmp + BitVec.ofNat 64 (u32VarBytes c.mv) = c.pHeap from rfl,
    show c.pHeap + BitVec.ofNat 64 (u32VarBytes c.mv) = c.pPos from rfl,
    show c.pPos + BitVec.ofNat 64 (u32VarBytes c.mv) = c.pMinClr from rfl,
    show c.pMinClr + BitVec.ofNat 64 (u32VarBytes c.mv) = c.pShrinkStk from rfl,
    show c.pShrinkStk + BitVec.ofNat 64 (u32VarBytes c.mv) = c.pQPrev from rfl,
    show c.pQPrev + BitVec.ofNat 64 (u32VarBytes c.mv) = c.pQNext from rfl,
    show c.pQNext + BitVec.ofNat 64 (u32VarBytes c.mv) = c.pQStamp from rfl,
    show c.pQStamp + BitVec.ofNat 64 (u32VarBytes c.mv) = c.pWvec from rfl,
    show c.pWvec + BitVec.ofNat 64 (8 * (2 * c.mv)) = c.pWsort from by
      rw [show 8 * (2 * c.mv) = 16 * c.mv by omega]; rfl,
    show c.pWsort + BitVec.ofNat 64 (8 * c.mv) = c.pScore from rfl,
    show c.pScore + BitVec.ofNat 64 (8 * c.mv) = c.pMinStk from rfl,
    show c.pMinStk + BitVec.ofNat 64 (8 * plainMinDepthOf c.mv) = c.pGlueUsed from rfl,
    show c.pGlueUsed + (256 : BitVec 64) = c.pArena from rfl,
    show c.pArena + BitVec.ofNat 64 (4 * c.arena_cap) = c.pWstk from rfl,
    show c.pWstk + BitVec.ofNat 64 (4 * c.wcap) = c.pDelayed from rfl,
    show c.pDelayed + BitVec.ofNat 64 (12 * c.delayed_cap) = c.pRedRefs from rfl]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ws1, h1, rfl⟩ := len_cons10 ws 82 hwl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ws2, h2, rfl⟩ := len_cons10 ws1 72 h1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ws3, h3, rfl⟩ := len_cons10 ws2 62 h2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ws4, h4, rfl⟩ := len_cons10 ws3 52 h3
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ws5, h5, rfl⟩ := len_cons10 ws4 42 h4
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ws6, h6, rfl⟩ := len_cons10 ws5 32 h5
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ws7, h7, rfl⟩ := len_cons10 ws6 22 h6
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ws8, h8, rfl⟩ := len_cons10 ws7 12 h7
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ws9, h9, rfl⟩ := len_cons10 ws8 2 h8
  rcases ws9 with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> simp at h9
  simp only [List.set_cons_zero, List.set_cons_succ, hdrTailWords, initPreState]; rfl

private theorem init_state_finish_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hZero : ∀ a m Q X, plainZeroTablesSpec a m Q X → Γ "plain_zero_tables" [i64] [] a m Q X)
    {c : PlainCfg} {ws : List (BitVec 64)} {cnf_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {j : Nat} {rest : List UInt8} (a : InitArrs c) (hwp1 : 1 ≤ c.wcap) {R : Mem 64 → Prop}
    {m : Mem 64} (hhdr : parseHeader cnfBytes = some (c.mv, c.nc, rest))
    (hj : j ≤ cnfBytes.length) (hdrop : cnfBytes.drop j = rest)
    (hws : ws = hdrTailWords c
      (initPreState c (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) fuel a))
    (hm : (hdrTail92 c.hdr ws ⋆ (PlainCoreArrays c
      (initPreState c (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) fuel a) ⋆
      PlainHeurArrays c (initPreState c (cnf_ptr + BitVec.ofNat 64 j)
        (BitVec.ofNat 64 c.nc) fuel a).heur ⋆ c.pad ⋆ bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) ⋆ R)) m)
    (hQtrue : ∀ (c' : PlainCfg) (s : PlainState) (j' : Nat) (rest' : List UInt8) (m' : Mem 64),
      c'.hdr = c.hdr → c'.avail = c.avail →
      parseHeader cnfBytes = some (c'.mv, c'.nc, rest') → j' ≤ cnfBytes.length →
      cnfBytes.drop j' = rest' → PlainInv c' (shiftDownCnf CNF.empty) s →
      s.d_cur = cnf_ptr + BitVec.ofNat 64 j' → s.arena_len = 0 → s.wlen = 1 →
      s.trail_end = 0 → s.propagated = 0 → s.cur_level = 0 → s.fuel = fuel →
      s.unflushed = 0#64 → s.probing = 0#64 → s.min_clr_len = 0 → s.min_clr_full = 0#64 →
      s.oom = 0#64 → s.vals = List.replicate (2 * c'.mv) 0#8 →
      s.wvec = List.replicate (4 * c'.mv) 0#32 → s.mrk = List.replicate c'.mv 0#8 →
      s.heur.rel_trigger = 0#64 → (bytes cnf_ptr cnfBytes ⋆ PlainMem c' s ⋆ R) m' →
      Q (true, ()) m') :
    wp Γ Q X (.call "plain_zero_tables" (as := [i64]) (bs := [])
        (Arg.var (t := i64) c.hdr, ()) fun _ => .ret (Arg.imm (t := .bool) true, ())) m := by
  let s1 := initPreState c (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 c.nc) fuel a
  have ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26⟩ := a.ok
  have hmem1 : (PlainMem c s1 ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := by
    unfold hdrTail92 at hm
    obtain ⟨_, hm'⟩ := sep_pure_l.mp hm
    rw [hws] at hm'; unfold PlainMem; exact sep_ac hm'
  have hlen1 : s1.LengthsOk c := by
    dsimp only [s1, initPreState]
    exact ⟨h1, h2, h6, h7, h8, h9, h10, h18, h23, h24, h21, h13, Nat.zero_le _, hwp1,
      Nat.zero_le _, Nat.le_refl _, Nat.zero_le _, Nat.zero_le _,
      ⟨h11, h12, h20, h3, h4, h5, h19, h14, h26, h22, h15, h16, h17, h25⟩⟩
  apply wp_call_of_spec; apply hZero
  refine ⟨c, s1, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen1, hmem1, ?_⟩
  intro wstk' mstk' heur' m' hwk' hmstk' hhok' hrt' s0 hm'; pi_head_steps
  have hlen0 : s0.LengthsOk c := { hlen1 with
    vals_len := by simp [s0], wvec_len := by simp [s0], wstk_len_arr := hwk',
    mrk_len := by simp [s0], lvl_len := by simp [s0], rsns_len := by simp [s0],
    trail_pos_len := by simp [s0], tmp_len_arr := by simp [s0], min_stk_len := hmstk',
    min_clr_len_arr := by simp [s0], heur_ok := hhok' }
  dsimp only [s1, initPreState] at hrt'
  exact hQtrue c s0 j rest m' rfl rfl hhdr hj hdrop (plainInv_init hlen0 rfl rfl rfl rfl rfl rfl)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hrt' (sep_ac hm')

private theorem init_hdr_remerge {cnf_ptr hdr_addr : BitVec 64} {avail : Nat}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} (h32 : 32 ≤ avail) (hle : avail ≤ 2 ^ 64)
    {mv' nc' cur' val' : BitVec 64} {m' : Mem 64}
    (hm' : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr mv' nc' cur' val' ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail - 32) ⋆ R) m') :
    (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail ⋆ R) m' := by
  have h2 := sep_mono2 (sep_mono2 (fun _ => Kissat.dimacsState_to_region) (fun _ h => h))
    (fun _ h => h) m' (show ((dimacsState hdr_addr mv' nc' cur' val' ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail - 32)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m' from sep_ac hm')
  rw [region_merge_eq (a := hdr_addr) (n1 := 32) (n2 := avail - 32) (n := avail)
    (by omega) hle] at h2
  exact sep_ac h2

private theorem init_hdr_fail {cnf_ptr hdr_addr : BitVec 64} {avail : Nat}
    {cnfBytes rest : List UInt8} {mv nc : Nat} {cur' val' : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {m' : Mem 64} (h32 : 32 ≤ avail) (hle : avail ≤ 2 ^ 64)
    (hhdr : parseHeader cnfBytes = some (mv, nc, rest))
    (hfail : avail < plainFixedBytes mv + nc * 40 + 136)
    (hm' : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr (BitVec.ofNat 64 mv)
      (BitVec.ofNat 64 nc) cur' val' ⋆ region (hdr_addr + 32#64) (avail - 32) ⋆ R) m')
    (hQfalse : ∀ m'', (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail ⋆ R) m'' →
      (∀ mv' nc' rest', parseHeader cnfBytes = some (mv', nc', rest') →
        avail < plainFixedBytes mv' + nc' * 40 + 136) → Q (false, ()) m'') : Q (false, ()) m' :=
  hQfalse m' (init_hdr_remerge h32 hle hm') fun _ _ _ h => by
    rw [hhdr] at h; rcases Option.some.inj h with ⟨rfl, rfl, rfl⟩; exact hfail

local macro "pi_jnz_t" h:ident : tactic => `(tactic|
  (dsimp only [Arg.val_var] at $h:ident; rw [decide_eq_true_eq] at $h:ident; pi_shallow_steps))
local macro "pi_jnz_f" h:ident : tactic => `(tactic|
  (dsimp only [Arg.val_var] at $h:ident; rw [decide_eq_false_iff_not] at $h:ident
   pi_shallow_steps))

private theorem plain_fixed_bv_eq {mv : Nat} (hmv : mv < dimacsBound) :
    1024#64 + ((BitVec.ofNat 64 mv <<< (1 : Nat) + 7) &&& ~~~7) +
      (((BitVec.ofNat 64 mv + 7) &&& ~~~7) <<< (2 : Nat)) +
      (((BitVec.ofNat 64 mv <<< (2 : Nat) + 7) &&& ~~~7) * (12 : BitVec 64)) +
      BitVec.ofNat 64 (8 * (BitVec.ofNat 64 mv <<< (1 : Nat)).toNat) +
      BitVec.ofNat 64 (8 * (BitVec.ofNat 64 mv).toNat) +
      BitVec.ofNat 64 (8 * (BitVec.ofNat 64 mv).toNat) +
      BitVec.ofNat 64 (8 * (BitVec.ofNat 64 (plainMinDepthOf mv)).toNat) =
      BitVec.ofNat 64 (plainFixedBytes mv) := by
  have hmv' := hmv; unfold dimacsBound at hmv'; have hmd := plainMinDepthOf_le mv
  have hvb : (BitVec.ofNat 64 mv <<< (1 : Nat) + 7) &&& ~~~7 = BitVec.ofNat 64 (valsBytes mv) := by
    rw [bv64_shl1_nat_eq, bv64_align8 (n := 2 * mv) (by omega)]; rfl
  have hmb : (BitVec.ofNat 64 mv + 7) &&& ~~~7 = BitVec.ofNat 64 (markBytes mv) := by
    simpa [markBytes] using bv64_align8 (n := mv) (by omega)
  have hub : (BitVec.ofNat 64 mv <<< (2 : Nat) + 7) &&& ~~~7 =
      BitVec.ofNat 64 (u32VarBytes mv) := by
    rw [bv64_shl2_nat, bv64_align8 (n := 4 * mv) (by omega)]; rfl
  rw [hvb, hmb, hub, show (1024#64 : BitVec 64) = BitVec.ofNat 64 1024 from rfl]
  simp only [bv64_shl1_nat_eq, bv64_shl2_nat, bv64_mul12, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 * mv < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show mv < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show plainMinDepthOf mv < 2 ^ 64 by omega)]
  repeat rw [bv_add_ofNat]
  unfold plainFixedBytes; congr 1; omega

private theorem init_qidx_jnz {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {e1 e2 : Expr Val Cont rs} {mv : Nat} (hmv : mv < 2 ^ 64)
    (h1 : mv = 0 → wp Γ Q X e1 m)
    (h2 : mv ≠ 0 → BitVec.ofNat 64 mv - (1 : BitVec 64) = BitVec.ofNat 64 (mv - 1) →
      wp Γ Q X e2 m) :
    wp Γ Q X (.jnz (Arg.var (BitVec.ofNat 64 mv == 0#64)) e1 e2) m := by
  have hbv : (BitVec.ofNat 64 mv == 0#64) = decide (mv = 0) := by
    by_cases h0 : mv = 0
    · subst h0; decide
    · have hne : BitVec.ofNat 64 mv ≠ 0#64 := fun h => h0 ((bv_eq_zero_iff hmv).mp h)
      simp [h0, hne]
  refine wp_jnz_of (fun ht => ?_) (fun hf => ?_)
  · dsimp only [Arg.val_var] at ht; rw [hbv, decide_eq_true_eq] at ht; exact h1 ht
  · dsimp only [Arg.val_var] at hf; rw [hbv, decide_eq_false_iff_not] at hf
    exact h2 hf (by rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl]
                    exact bv_sub_ofNat (by omega) hmv)

private def InitFalsePost (cnf_ptr hdr_addr avail : BitVec 64) (cnfBytes : List UInt8)
    (R : Mem 64 → Prop) (Q : Post [.bool]) : Prop :=
  ∀ (m' : Mem 64), (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail.toNat ⋆ R) m' →
    (∀ mv nc rest, parseHeader cnfBytes = some (mv, nc, rest) →
      avail.toNat < plainFixedBytes mv + nc * 40 + 136) → Q (false, ()) m'

private def InitTruePost (cnf_ptr hdr_addr avail fuel : BitVec 64) (cnfBytes : List UInt8)
    (R : Mem 64 → Prop) (Q : Post [.bool]) : Prop :=
  ∀ (c : PlainCfg) (s : PlainState) (j : Nat) (rest : List UInt8) (m' : Mem 64),
    c.hdr = hdr_addr → c.avail = avail.toNat → parseHeader cnfBytes = some (c.mv, c.nc, rest) →
    j ≤ cnfBytes.length → cnfBytes.drop j = rest → PlainInv c (shiftDownCnf CNF.empty) s →
    s.d_cur = cnf_ptr + BitVec.ofNat 64 j → s.arena_len = 0 → s.wlen = 1 → s.trail_end = 0 →
    s.propagated = 0 → s.cur_level = 0 → s.fuel = fuel → s.unflushed = 0#64 →
    s.probing = 0#64 → s.min_clr_len = 0 → s.min_clr_full = 0#64 → s.oom = 0#64 →
    s.vals = List.replicate (2 * c.mv) 0#8 → s.wvec = List.replicate (4 * c.mv) 0#32 →
    s.mrk = List.replicate c.mv 0#8 → s.heur.rel_trigger = 0#64 →
    (bytes cnf_ptr cnfBytes ⋆ PlainMem c s ⋆ R) m' → Q (true, ()) m'

private theorem hdr92_opaque {hdr : BitVec 64} {ws : List (BitVec 64)} {F : Mem 64 → Prop}
    {m : Mem 64} (hm : (hdrTail92 hdr ws ⋆ F) m) :
    ∃ ws', ws = ws' ∧ (hdrTail92 hdr ws' ⋆ F) m := ⟨ws, rfl, hm⟩

local macro "pi_hdr_store" : tactic => do
  let mId := Lean.mkIdent `m
  let hmId := Lean.mkIdent `hm
  `(tactic| (
    pi_shallow_lets
    apply wp_store_sep
    · dsimp only [Arg.val_var, Arg.val_imm]
      refine c0_store_hdr92 _ _ _ _ (by assumption) (by decide)
    intro $mId:ident $hmId:ident))

theorem plain_init_state_wp (Γ : Env)
    (hHdr : ∀ a m Q X, kissatParseHeaderSpec a m Q X →
      Γ "kissat_parse_header" [i64, i64, i64] [.bool] a m Q X)
    (hZero : ∀ a m Q X, plainZeroTablesSpec a m Q X → Γ "plain_zero_tables" [i64] [] a m Q X) :
    ∀ a m Q X, plainInitStateSpec a m Q X → Func.wp Γ plain_init_state_body a m Q X := by
  rintro ⟨cnf_ptr, cend, hdr_addr, avail, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, R, rfl, hfit, havel_fit, hav768, hm_in, hQfalse, hQtrue⟩
  have hFt : InitFalsePost cnf_ptr hdr_addr avail cnfBytes R Q := hQfalse
  have hTt : InitTruePost cnf_ptr hdr_addr avail fuel cnfBytes R Q := hQtrue
  clear hQfalse hQtrue
  have hav_le : avail.toNat ≤ 2 ^ 64 := by omega
  have hm0 : (bytes cnf_ptr cnfBytes ⋆ (region hdr_addr 32 ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32)) ⋆ R) m := by
    rw [region_merge_eq (a := hdr_addr) (n1 := 32) (n2 := avail.toNat - 32) (n := avail.toNat)
      (by omega) hav_le]; exact hm_in
  have hm0' : (region hdr_addr 32 ⋆ (bytes cnf_ptr cnfBytes ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R)) m := sep_ac hm0
  obtain ⟨mv0, hm_pre⟩ := sep_ex_l.mp (sep_mono (fun _ h => Kissat.region32_to_dimacsState h) hm0')
  obtain ⟨nc0, hm_pre⟩ := sep_ex_l.mp hm_pre
  obtain ⟨cur0, hm_pre⟩ := sep_ex_l.mp hm_pre
  obtain ⟨val0, hm_pre⟩ := sep_ex_l.mp hm_pre
  unfold Func.wp plain_init_state_body; apply wp_call_of_spec; apply hHdr
  change kissatParseHeaderSpec (cnf_ptr, cnf_ptr + BitVec.ofNat 64 cnfBytes.length, hdr_addr, ())
    m _ _
  refine ⟨mv0, nc0, cur0, val0, cnfBytes,
    region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R, rfl, hfit, sep_ac hm_pre, ?_⟩
  cases hhdr : parseHeader cnfBytes with
  | none =>
    intro _ _ _ _ m' hm'; refine wp_jnz_of (fun hc => by cases hc) (fun _ => ?_)
    rw [wp_ret]; exact hFt m' (init_hdr_remerge (by omega) hav_le (sep_ac hm'))
      (fun _ _ _ h => by rw [hhdr] at h; cases h)
  | some p =>
    rcases p with ⟨mv, nc, rest⟩; intro j m0 hmv_bd hnc_bd hj hdrop hm0
    have hmv := hmv_bd; have hnc := hnc_bd; unfold dimacsBound at hmv hnc
    refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc); pi_shallow_steps
    refine wp_join_group
      (fun (md_v, ()) m_md => md_v = BitVec.ofNat 64 (plainMinDepthOf mv) ∧ m_md = m0) ?_ ?_
    · rintro _ ⟨md_v, ⟨⟩⟩ m_md ⟨rfl, hm_md⟩; subst m_md; pi_shallow_steps
      have hfx_eq := plain_fixed_bv_eq hmv_bd; have hfx_lt := plainFixedBytes_lt hmv_bd
      have hult_fx : avail.ult (BitVec.ofNat 64 (plainFixedBytes mv)) =
          decide (avail.toNat < plainFixedBytes mv) := by
        simpa [bv_ofNat_toNat_eq avail] using bv_ult_eq avail.isLt (by omega)
      refine wp_jnz_of (fun hlt => ?_) (fun hge => ?_)
      · rw [hfx_eq, hult_fx] at hlt; pi_jnz_t hlt
        exact init_hdr_fail (by omega) hav_le hhdr (by omega) (sep_ac hm0) hFt
      · rw [hfx_eq, hult_fx] at hge; pi_jnz_f hge
        have hrem_eq : avail - BitVec.ofNat 64 (plainFixedBytes mv) =
            BitVec.ofNat 64 (avail.toNat - plainFixedBytes mv) := by
          simpa [bv_ofNat_toNat_eq avail] using bv_sub_ofNat (by omega) avail.isLt
        let rem := avail.toNat - plainFixedBytes mv; have hrem64 : rem < 2 ^ 64 := by omega
        rw [hfx_eq, hrem_eq, bv64_mul40, show (136 : BitVec 64) = BitVec.ofNat 64 136 from rfl,
          bv_add_ofNat, bv_ult_eq hrem64 (by omega)]
        refine wp_jnz_of (fun hlt2 => ?_) (fun hge2 => ?_)
        · pi_jnz_t hlt2; exact init_hdr_fail (by omega) hav_le hhdr (by omega) (sep_ac hm0) hFt
        · pi_jnz_f hge2
          refine wp_join_group
            (fun (dc_v, ()) m2 => dc_v = BitVec.ofNat 64 (plainInitDelCap rem) ∧ m2 = m0) ?_ ?_
          · rintro _ ⟨dc_v, ⟨⟩⟩ m2 ⟨rfl, hm2⟩; subst m2; pi_shallow_steps
            have ⟨hdel_le, ht_ge5, har_sum⟩ :=
              plainInit_total_ge5 (nc := nc) (rem := rem) (by omega)
            have ht_lt : plainInitTotalPairs rem < 2 ^ 63 := by unfold plainInitTotalPairs; omega
            have htot_eq : (rem - 12 * plainInitDelCap rem) / 8 = plainInitTotalPairs rem := by
              unfold plainInitTotalPairs; rw [Nat.mul_comm]
            have hap_raw_eq : ((BitVec.ofNat 64 (avail.toNat - plainFixedBytes mv) -
                BitVec.ofNat 64 (plainInitDelCap rem) * 12) >>> 3 * 3) / 5 =
                BitVec.ofNat 64 ((plainInitTotalPairs rem * 3) / 5) := by
              rw [bv64_mul12, bv_sub_ofNat (by omega) hrem64, bv64_shr3_nat (by omega),
                htot_eq, bv64_mul3, Nat.mul_comm 3 _, show (5 : BitVec 64) = BitVec.ofNat 64 5
                  from rfl]
              exact bv_udiv_ofNat (by omega) (by decide) (by decide)
            refine wp_join_group (fun (ap_v, ()) m3 =>
                ap_v = BitVec.ofNat 64 (plainInitArenaPairs rem) ∧ m3 = m0) ?_ ?_
            · rintro _ ⟨ap_v, ⟨⟩⟩ m3 ⟨rfl, hm3⟩; subst m3; pi_shallow_steps
              have hap_lt := plainInitArenaCap_lt rem
              have hrp_eq : (BitVec.ofNat 64 (plainInitArenaPairs rem) + 5) / 6 =
                  BitVec.ofNat 64 (plainInitRedPairs rem) := by
                rw [show (5 : BitVec 64) = BitVec.ofNat 64 5 from rfl, bv_add_ofNat,
                  show (6 : BitVec 64) = BitVec.ofNat 64 6 from rfl]; unfold plainInitRedPairs
                exact bv_udiv_ofNat (by omega) (by decide) (by decide)
              refine wp_join_group (fun (wp_v, ()) m4 =>
                  wp_v = BitVec.ofNat 64 (plainInitWPairs rem) ∧ m4 = m0) ?_ ?_
              · rintro _ ⟨wp_v, ⟨⟩⟩ m4 ⟨rfl, hm4⟩; subst m4
                let ap := plainInitArenaPairs rem; let rp := plainInitRedPairs rem
                let wpr := plainInitWPairs rem
                let c : PlainCfg :=
                  ⟨hdr_addr, avail.toNat, mv, nc, 2 * ap, 2 * wpr, plainInitDelCap rem, 2 * rp,
                    hmv_bd, hnc_bd, plainInitArenaCap_lt rem, plainInitWCap_lt rem,
                    plainInitDelCap_lt rem,
                    (by have := plainInitRedCap_lt rem; unfold dimacsBound at *; omega),
                    havel_fit, plain_init_arena_fits (nc := nc) (by omega)⟩
                have hwpr_ge1 : 1 ≤ wpr := by
                  dsimp [wpr]; unfold plainInitWPairs plainInitRedPairs plainInitArenaPairs; omega
                have hwc1 : 1 ≤ c.wcap := by dsimp [c]; omega
                have hmv_lt : mv < 2 ^ 64 := by unfold dimacsBound at hmv_bd; omega
                obtain ⟨ws, arrs, hwl, hm_st⟩ := init_state_split_arena c fuel hav768 hm0
                clear hm_in hm_pre hm0
                iterate 25 pi_hdr_store
                obtain ⟨ws1, hws1, hm⟩ := hdr92_opaque hm
                iterate 25 pi_hdr_store
                obtain ⟨ws2, hws2, hm⟩ := hdr92_opaque hm
                repeat pi_hdr_store
                obtain ⟨ws3, hws3, hm⟩ := hdr92_opaque hm
                pi_shallow_lets
                let qF : BitVec 64 := if mv = 0 then 0xFFFFFFFF#64 else 0#64
                let qL : BitVec 64 := if mv = 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (mv - 1)
                refine wp_join_group (fun (qf_v, ()) mg => qf_v = qF ∧ mg = m) ?_ ?_
                · rintro _ ⟨qf_v, ⟨⟩⟩ mg ⟨rfl, rfl⟩; pi_hdr_store; pi_shallow_lets
                  refine wp_join_group (fun (ql_v, ()) mg2 => ql_v = qL ∧ mg2 = m) ?_ ?_
                  · rintro _ ⟨ql_v, ⟨⟩⟩ mg2 ⟨rfl, rfl⟩; pi_hdr_store; pi_shallow_lets
                    refine wp_join_group (fun (qs_v, ()) mg3 => qs_v = qL ∧ mg3 = m) ?_ ?_
                    · rintro _ ⟨qs_v, ⟨⟩⟩ mg3 ⟨rfl, rfl⟩; repeat pi_hdr_store
                      pi_shallow_lets
                      rw [← hws3, ← hws2, ← hws1, hrp_eq] at hm
                      dsimp only [qF, qL] at hm
                      simp only [BitVec.reduceToNat, Nat.reduceSub, Nat.reduceDiv,
                        show (1 : BitVec 64) <<< (28 : Nat) = 268435456#64 from by decide,
                        show (1 : BitVec 64) <<< (24 : Nat) = 16777216#64 from by decide] at hm
                      have hws' := init_hdrtail_norm c (cnf_ptr + BitVec.ofNat 64 j)
                        (BitVec.ofNat 64 c.nc) fuel arrs ws hwl rem rfl rfl rfl rfl
                      dsimp only at hws'; simp only [shl_three] at hws'
                      have hc_mv : c.mv = mv := rfl; have hc_hdr : c.hdr = hdr_addr := rfl
                      conv at hws' => lhs; rw [hc_mv, hc_hdr]
                      rw [hws', ← hc_hdr] at hm
                      exact init_state_finish_wp hZero arrs hwc1 hhdr hj hdrop rfl hm hTt
                    · intro Jqs hJqs; pi_shallow_steps
                      refine init_qidx_jnz hmv_lt ?_ ?_
                      · intro h0; pi_shallow_steps
                        exact hJqs _ _ ⟨by simp only [qL, h0, ite_true]; try rfl, rfl⟩
                      · intro hne hs; pi_shallow_steps; rw [hs]
                        exact hJqs _ _ ⟨by simp only [qL, hne, ite_false]; try rfl, rfl⟩
                  · intro Jql hJql; pi_shallow_steps
                    refine init_qidx_jnz hmv_lt ?_ ?_
                    · intro h0; pi_shallow_steps
                      exact hJql _ _ ⟨by simp only [qL, h0, ite_true]; try rfl, rfl⟩
                    · intro hne hs; pi_shallow_steps; rw [hs]
                      exact hJql _ _ ⟨by simp only [qL, hne, ite_false]; try rfl, rfl⟩
                · intro Jqf hJqf; pi_shallow_steps
                  refine init_qidx_jnz hmv_lt ?_ ?_
                  · intro h0; pi_shallow_steps
                    exact hJqf _ _ ⟨by simp only [qF, h0, ite_true]; try rfl, rfl⟩
                  · intro hne _; pi_shallow_steps
                    exact hJqf _ _ ⟨by simp only [qF, hne, ite_false]; try rfl, rfl⟩
              · intro Jwp hJwp; pi_shallow_steps
                have hwp_rem : plainInitTotalPairs rem - plainInitArenaPairs rem -
                    plainInitRedPairs rem < 2 ^ 64 := by unfold plainInitTotalPairs; omega
                rw [bv64_mul12, bv_sub_ofNat (by omega) hrem64, bv64_shr3_nat (by omega),
                  htot_eq, hrp_eq,
                  show (134217727 : BitVec 64) = BitVec.ofNat 64 134217727 from rfl,
                  bv_sub_ofNat (by omega) (by omega), bv_sub_ofNat (by omega) (by omega),
                  bv_ult_eq (by decide) hwp_rem]
                refine wp_jnz_of (fun hgt => by
                    pi_jnz_t hgt; exact hJwp _ _ ⟨congrArg (BitVec.ofNat 64)
                      (by unfold plainInitWPairs; omega), rfl⟩)
                  (fun hle => by
                    pi_jnz_f hle; exact hJwp _ _ ⟨congrArg (BitVec.ofNat 64)
                      (by unfold plainInitWPairs; omega), rfl⟩)
            · intro Jap hJap; pi_shallow_steps
              have hap_raw : (plainInitTotalPairs rem * 3) / 5 < 2 ^ 64 := by
                unfold plainInitTotalPairs; omega
              rw [hap_raw_eq, show (134217727 : BitVec 64) = BitVec.ofNat 64 134217727 from rfl,
                bv_ult_eq (by decide) hap_raw]
              refine wp_jnz_of (fun hgt => by
                  pi_jnz_t hgt; exact hJap _ _ ⟨congrArg (BitVec.ofNat 64)
                    (by unfold plainInitArenaPairs; omega), rfl⟩)
                (fun hle => by
                  pi_jnz_f hle; exact hJap _ _ ⟨congrArg (BitVec.ofNat 64)
                    (by unfold plainInitArenaPairs; omega), rfl⟩)
          · intro Jdc hJdc; pi_shallow_steps
            rw [show (524288 : BitVec 64) = BitVec.ofNat 64 524288 from rfl,
              bv_ule_eq (by decide) hrem64]
            refine wp_jnz_of
              (fun hge => by pi_jnz_t hge; exact hJdc _ _ ⟨by simp [plainInitDelCap, hge], rfl⟩)
              (fun hlt => by pi_jnz_f hlt; exact hJdc _ _ ⟨by simp [plainInitDelCap, hlt], rfl⟩)
    · intro J hJ; pi_shallow_steps
      have hadd1 : BitVec.ofNat 64 mv + (1 : BitVec 64) = BitVec.ofNat 64 (mv + 1) := bv64_add1_nat
      rw [hadd1, show (1000 : BitVec 64) = BitVec.ofNat 64 1000 from rfl,
        bv_ult_eq (by omega) (by decide)]
      refine wp_jnz_of
        (fun hlt => by pi_jnz_t hlt; exact hJ _ _ ⟨by rw [hadd1]; simp [plainMinDepthOf, hlt], rfl⟩)
        (fun hge => by pi_jnz_f hge; exact hJ _ _ ⟨by simp [plainMinDepthOf, hge], rfl⟩)

end LeanQbe.T.Examples.Kissat.Plain
