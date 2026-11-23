module

public import LeanQbe.T.Examples.Kissat.FullM6Tiers
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat M6 Tiers `Func.wp` Proofs — Part 0 (`FullM6TiersProof0`)

Proves UNSAT-only `SafetySlice` / `Mem 64` `Func.wp` contracts (`0` SAT/model proofs) for the
`23` foundational functions of `FullM6Tiers`:
1. Struct layout size helpers (`full_m6_hdr_sizeof`, `full_m6_ext_sizeof`) & 64-bit `delayed`
   word accessors (`full_m6_get64`, `full_m6_set64`).
2. Extended header initialization (`full_m6_ext_ready`) with `del[0..15]` non-interference
   (`∀ k < 16, sc'.delayed[k]? = sc.delayed[k]?`).
3. Mode-split tiers (`full_m6_sync_legacy_tiers`, `full_m6_recompute_tiers_mode`,
   `full_recompute_tiers_m6`, `full_m6_update_tier_limits`, `full_m6_record_used`,
   `full_m6_get_tier1`, `full_m6_get_tier2`).
4. `delay[4]` backoff (`full_m6_delaying`, `full_m6_bump_delay`, `full_m6_reduce_delay`,
   `full_m6_reset_delay`).
5. Watermarks & tick routing (`full_m6_get_watermark`, `full_m6_set_watermark`,
   `full_m6_add_ticks`, `full_log10_q16_m6`, `full_scale_delta_m6`, `full_probe_dticks_m6`,
   `full_elim_dticks_m6`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6Tiers

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open Kraken.Bedrock2.Test

/-! ## 1. Pure Helpers, `M6` Non-Interference & Specs -/

/-- Decodes two consecutive `u32` words in `del` as a little-endian `u64`. -/
def m6Get64Val (del : List (BitVec 32)) (idx : Nat) : BitVec 64 :=
  (del[idx]?.getD 0#32).setWidth 64 ||| ((del[idx + 1]?.getD 0#32).setWidth 64 <<< 32)

/-- Encodes a `u64` into two consecutive `u32` words in `del` (`lo`, then `hi`). -/
def m6Set64List (del : List (BitVec 32)) (idx : Nat) (val : BitVec 64) : List (BitVec 32) :=
  (del.set idx (val.setWidth 32)).set (idx + 1) ((val >>> 32).setWidth 32)

theorem m6Set64List_length (del : List (BitVec 32)) (idx : Nat) (val : BitVec 64) :
    (m6Set64List del idx val).length = del.length := by
  simp [m6Set64List]

theorem m6Set64List_get_lt (del : List (BitVec 32)) (idx : Nat) (val : BitVec 64)
    {k : Nat} (hk : k < idx) : (m6Set64List del idx val)[k]? = del[k]? := by
  unfold m6Set64List
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

theorem m6Get64Val_set64_self {del : List (BitVec 32)} {idx : Nat} (val : BitVec 64)
    (hi : idx + 1 < del.length) : m6Get64Val (m6Set64List del idx val) idx = val := by
  unfold m6Get64Val m6Set64List
  have hlen : (del.set idx (val.setWidth 32)).length = del.length := List.length_set
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
    List.getElem?_set_self (by rw [hlen]; exact hi)]
  simp only [Option.getD_some]
  apply BitVec.eq_of_getElem_eq; intro k hk
  simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth]
  by_cases h32 : k < 32
  · simp [h32]; rfl
  · have hlo : k - 32 < 32 := by omega
    have hk' : 32 + (k - 32) = k := by omega
    simp [h32, hlo, hk']; rfl

/-- `FullM6MinShrink` (`decision_rate`) non-interference: `del[0..15]` (`64` bytes) untouched. -/
def FullM6DelayedW2bPres (s s' : FullState) : Prop :=
  ∀ k < 16, s'.scratch.delayed[k]? = s.scratch.delayed[k]?

/-- Combined probe-scratch and `del[0..15]`-prefix preservation for `M6` helpers. -/
def FullM6ScratchPres (s s' : FullState) : Prop :=
  FullProbeScratchPres s s' ∧ FullM6DelayedW2bPres s s'

theorem FullM6DelayedW2bPres.refl (s : FullState) : FullM6DelayedW2bPres s s := fun _ _ => rfl

theorem FullM6DelayedW2bPres.trans {s₁ s₂ s₃ : FullState}
    (h12 : FullM6DelayedW2bPres s₁ s₂) (h23 : FullM6DelayedW2bPres s₂ s₃) :
    FullM6DelayedW2bPres s₁ s₃ := fun k hk => (h23 k hk).trans (h12 k hk)

theorem probePres_refl_m6 (s : FullState) : FullProbeScratchPres s s :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem probePres_trans_m6 {s₁ s₂ s₃ : FullState}
    (h12 : FullProbeScratchPres s₁ s₂) (h23 : FullProbeScratchPres s₂ s₃) :
    FullProbeScratchPres s₁ s₃ :=
  ⟨⟨h23.1.1.trans h12.1.1, h23.1.2.trans h12.1.2⟩, h23.2.1.trans h12.2.1,
   h23.2.2.1.trans h12.2.2.1, h23.2.2.2.1.trans h12.2.2.2.1,
   h23.2.2.2.2.1.trans h12.2.2.2.2.1, h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2⟩

theorem FullM6ScratchPres.refl (s : FullState) : FullM6ScratchPres s s :=
  ⟨probePres_refl_m6 s, FullM6DelayedW2bPres.refl s⟩

theorem FullM6ScratchPres.trans {s₁ s₂ s₃ : FullState}
    (h12 : FullM6ScratchPres s₁ s₂) (h23 : FullM6ScratchPres s₂ s₃) :
    FullM6ScratchPres s₁ s₃ :=
  ⟨probePres_trans_m6 h12.1 h23.1, h12.2.trans h23.2⟩

def m6HdrSizeofSpec : Spec [] [i64] := fun () m Q _ =>
  Q (BitVec.ofNat 64 fullM6HdrTotalBytes, ()) m

def m6ExtSizeofSpec : Spec [] [i64] := fun () m Q _ =>
  Q (BitVec.ofNat 64 fullM6ExtBytes, ()) m

def m6Get64Spec : Spec [i64, i64] [i64] := fun (del_ptr, idx, ()) m Q _ =>
  ∃ (del : List (BitVec 32)) (R : Mem 64 → Prop),
    idx.toNat + 1 < del.length ∧ del.length < 2 ^ 62 ∧
    (array (t := i32) del_ptr del ⋆ R) m ∧ Q (m6Get64Val del idx.toNat, ()) m

def m6Set64Spec : Spec [i64, i64, i64] [] := fun (del_ptr, idx, val, ()) m Q _ =>
  ∃ (del : List (BitVec 32)) (R : Mem 64 → Prop),
    idx.toNat + 1 < del.length ∧ del.length < 2 ^ 62 ∧
    (array (t := i32) del_ptr del ⋆ R) m ∧
    ∀ m', (array (t := i32) del_ptr (m6Set64List del idx.toNat val) ⋆ R) m' → Q () m'

def m6ExtReadySpec : Spec [i64] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun c _ (r, ()) s s' =>
      FullM6ScratchPres s s' ∧
      (r = true ↔ fullM6DelMinCap ≤ c.delayed_cap) ∧
      (r = true → m6Get64Val s'.scratch.delayed m6DelMagicIdx = fullM6Magic) ∧
      (r = false → s' = s))

def m6SafetyVoidSpec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullM6ScratchPres s s')

def m6RecomputeExtSpec : Spec [i64, i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, mode, ()) _ =>
      h = c.hdr ∧ fullM6DelMinCap ≤ c.delayed_cap ∧ (mode = 0#64 ∨ mode = 1#64))
    (fun _ _ _ s s' => FullM6ScratchPres s s')

def m6SafetyArgVoidSpec (α : Ty) : Spec [i64, α] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullM6ScratchPres s s')

def m6SafetyBoolU64Spec : Spec [i64, .bool] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullM6ScratchPres s s')

def m6DelayingSpec : Spec [i64, i64] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullM6ScratchPres s s')

def m6GetWmSpec : Spec [i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullM6ScratchPres s s')

def m6SetWmSpec : Spec [i64, i64, i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _, _, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullM6ScratchPres s s')

def m6Log10Q16Spec : Spec [i64] [i64] := fun (x, ()) m Q _ =>
  ∀ r : BitVec 64, r.toNat < 20 * 65536 → (10 ≤ x.toNat → 65536 ≤ r.toNat) → Q (r, ()) m

def m6ScaleDeltaSpec : Spec [i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => s' = s)

def m6DticksSpec : Spec [i64, .bool] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullM6ScratchPres s s')

theorem m6SafetyVoidSpec_to_full {a : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : fullSafetyVoidSpec a m Q X) : m6SafetyVoidSpec a m Q X := by
  rcases h with ⟨c, s, R, hc, hl, hm, hQ⟩
  exact ⟨c, s, R, hc, hl, hm, fun r s' m' hco hln hpr hm' => hQ r s' m' hco hln hpr.1 hm'⟩

/-! ## 2. Local Tactics & `FullMem`-Delayed Framing Adapters -/

section M6Proof0Tactics

open Lean Elab Tactic in
local elab "m6_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let rawTy ← Lean.instantiateMVars (← g.getType)
      let ty := rawTy.consumeMData
      if rawTy.isMData then
        let g' ← g.change ty (checkDefEq := false)
        setGoals [g']
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out ++ (← getUnsolvedGoals)
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out ++ (← getUnsolvedGoals)
    setGoals out.toList
  go 500

open Lean Elab Tactic in
local elab "m6_to_jnz" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      let rawTy ← Lean.instantiateMVars (← g.getType)
      let ty := rawTy.consumeMData
      if rawTy.isMData then
        let g' ← g.change ty (checkDefEq := false)
        setGoals [g']
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
        out := out ++ (← getUnsolvedGoals)
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out ++ (← getUnsolvedGoals)
    setGoals out.toList
  go 500

private theorem wp_let_add64_m6 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i64} {k : Tup Val [i64] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i64, i64], code := .add i64, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val + b.val, ())) m := by
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, lift2] using
    @wp_let_add_eq Γ rs Q X m i64 (a, b, ()) k

private theorem wp_let_mul64_m6 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i64} {k : Tup Val [i64] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i64, i64], code := .mul i64, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val * b.val, ())) m := by
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, lift2] using
    @wp_let_mul_eq Γ rs Q X m i64 (a, b, ()) k

private theorem wp_let_ult64_m6 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {hm : Ty.bool = Ty.mask i64} {a b : Arg Val i64}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i64 .bool hm) (a, b, ())) k) m =
      wp Γ Q X (k (BitVec.ult a.val b.val, ())) m := by
  have hc := @wp_let_cmp_eq Γ rs Q X m .ult i64 .bool hm (a, b, ()) k
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, liftCmp,
    evalBits_ult_eq, cast_eq] using hc

private theorem pow10_lt_64_m6 {d : Nat} (hd : d ≤ 19) : 10 ^ d < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hd) (by decide)

private theorem m6_del_len_lt62 (c : FullCfg) {s : FullState} (hlen : s.LengthsOk c) :
    s.scratch.delayed.length < 2 ^ 62 := by
  have hdl := hlen.scratch_ok.delayed_len_arr
  have hcd := c.hdel; unfold dimacsBound at hcd; omega

private def m6ScrDynRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
  array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
  array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
   FullScrMetaArrs c s.scratch ⋆ fullScrOuter c s)

private theorem fullMem_focus_delayed {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pDelayed s.scratch.delayed ⋆ (m6ScrDynRest c s ⋆ R)) m := by
  rw [fullMem_eq_scrDyn] at hm; unfold FullScrDynArrs at hm
  unfold m6ScrDynRest; exact sep_ac hm

private theorem fullScrByte_del_irrel (c : FullCfg) (sc : FullScratch) (d : List (BitVec 32)) :
    FullScrByteArrs c { sc with delayed := d } = FullScrByteArrs c sc := by
  unfold FullScrByteArrs; rfl

private theorem fullScrU32A_del_irrel (c : FullCfg) (sc : FullScratch) (d : List (BitVec 32)) :
    FullScrU32A c { sc with delayed := d } = FullScrU32A c sc := by
  unfold FullScrU32A; rfl

private theorem fullScrWks_del_irrel (c : FullCfg) (sc : FullScratch) (d : List (BitVec 32)) :
    FullScrWksArrs c { sc with delayed := d } = FullScrWksArrs c sc := by
  unfold FullScrWksArrs; rfl

private theorem fullScrMeta_del_irrel (c : FullCfg) (sc : FullScratch) (d : List (BitVec 32)) :
    FullScrMetaArrs c { sc with delayed := d } = FullScrMetaArrs c sc := by
  unfold FullScrMetaArrs; rfl

private theorem fullScrOuter_del_irrel (c : FullCfg) (s : FullState) (d : List (BitVec 32)) :
    fullScrOuter c { s with scratch := { s.scratch with delayed := d } } = fullScrOuter c s := by
  unfold fullScrOuter Full.hdrTailWords Full.hdrTailWords0 Full.hdrTailWords1
    Full.hdrTailWords2 Full.hdrTailWords3
  rfl

private theorem m6_used_idx_lt {cap : Nat} {gi base : BitVec 64} (hcap : 200 ≤ cap)
    (hgi : gi.toNat < 128) (hb : base = 54#64 ∨ base = 310#64) :
    (base + (gi <<< (1 : BitVec 64))).toNat + 1 < 3 * cap := by
  have hsh : (gi <<< (1 : BitVec 64)).toNat = 2 * gi.toNat := by
    rw [show (gi <<< (1 : BitVec 64)) = gi <<< (1 : Nat) from rfl,
      BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
  rcases hb with rfl | rfl <;> (rw [BitVec.toNat_add, hsh]; bv_omega)

private theorem m6_used_tu_lt {cap : Nat} {tu_idx : BitVec 64} (hcap : 200 ≤ cap)
    (htu : tu_idx = 26#64 ∨ tu_idx = 28#64) : tu_idx.toNat + 1 < 3 * cap := by
  rcases htu with rfl | rfl <;> bv_omega

private theorem m6_used_ge16 {gi base : BitVec 64} (hgi : gi.toNat < 128)
    (hb : base = 54#64 ∨ base = 310#64) :
    16 ≤ (base + (gi <<< (1 : BitVec 64))).toNat := by
  have hsh : (gi <<< (1 : BitVec 64)).toNat = 2 * gi.toNat := by
    rw [show (gi <<< (1 : BitVec 64)) = gi <<< (1 : Nat) from rfl,
      BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
  rcases hb with rfl | rfl <;> (rw [BitVec.toNat_add, hsh]; bv_omega)

private theorem m6_tier_mode_lt {cap : Nat} {base mode : BitVec 64} (hcap : 200 ≤ cap)
    (hm : mode = 0#64 ∨ mode = 1#64) (hb : base = (18 : BitVec 64) ∨ base = (20 : BitVec 64)) :
    (base + mode).toNat < 3 * cap := by
  rcases hm with rfl | rfl <;> rcases hb with rfl | rfl <;> bv_omega

private theorem m6_tier_mode_ge16 {mode : BitVec 64} (hm : mode = 0#64 ∨ mode = 1#64)
    {k : Nat} (hk : k < 16) (l : List (BitVec 32)) (a b : BitVec 32) :
    ((l.set ((18 : BitVec 64) + mode).toNat a).set ((20 : BitVec 64) + mode).toNat b)[k]? =
      l[k]? := by
  rcases hm with rfl | rfl <;>
    rw [List.getElem?_set_ne (by bv_omega), List.getElem?_set_ne (by bv_omega)]

private theorem m6_delay_lt {cap : Nat} {id base : BitVec 64} (hcap : 200 ≤ cap)
    (hid : id.toNat < 4) (hb : base = (30 : BitVec 64) ∨ base = (34 : BitVec 64)) :
    (base + id).toNat < 3 * cap := by
  rcases hb with rfl | rfl <;> bv_omega

private theorem m6_delay_ge16 {id base : BitVec 64} (hid : id.toNat < 4)
    (hb : base = (30 : BitVec 64) ∨ base = (34 : BitVec 64)) {k : Nat} (hk : k < 16) :
    (base + id).toNat ≠ k := by
  rcases hb with rfl | rfl <;> bv_omega

private theorem m6_wm_lt {cap : Nat} {kind : BitVec 64} (hcap : 200 ≤ cap)
    (hkind : kind.toNat < 8) :
    (38#64 + (kind <<< (1 : BitVec 64))).toNat + 1 < 3 * cap := by
  have hsh : (kind <<< (1 : BitVec 64)).toNat = 2 * kind.toNat := by
    rw [show (kind <<< (1 : BitVec 64)) = kind <<< (1 : Nat) from rfl,
      BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
  rw [BitVec.toNat_add, hsh]; bv_omega

private theorem m6_wm_ge16 {kind : BitVec 64} (hkind : kind.toNat < 8) {k : Nat} (hk : k < 16) :
    k < (38#64 + (kind <<< (1 : BitVec 64))).toNat := by
  have hsh : (kind <<< (1 : BitVec 64)).toNat = 2 * kind.toNat := by
    rw [show (kind <<< (1 : BitVec 64)) = kind <<< (1 : Nat) from rfl,
      BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
  rw [BitVec.toNat_add, hsh]; bv_omega

private theorem fullMem_unfocus_delayed {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {del' : List (BitVec 32)} {m' : Mem 64}
    (hm : (array (t := i32) c.pDelayed del' ⋆ (m6ScrDynRest c s ⋆ R)) m') :
    (FullMem c { s with scratch := { s.scratch with delayed := del' } } ⋆ R) m' := by
  rw [fullMem_eq_scrDyn]; unfold FullScrDynArrs
  rw [fullScrByte_del_irrel, fullScrU32A_del_irrel, fullScrWks_del_irrel,
    fullScrMeta_del_irrel, fullScrOuter_del_irrel]
  unfold m6ScrDynRest at hm; exact sep_ac hm

private theorem m6_get64_full_spec {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {idx : BitVec 64} {Q : Post [i64]} {X : XPost}
    (hlen : s.LengthsOk c) (hi : idx.toNat + 1 < s.scratch.delayed.length)
    (hm : (FullMem c s ⋆ R) m) (hQ : Q (m6Get64Val s.scratch.delayed idx.toNat, ()) m) :
    m6Get64Spec (c.pDelayed, idx, ()) m Q X :=
  ⟨s.scratch.delayed, m6ScrDynRest c s ⋆ R, hi, m6_del_len_lt62 c hlen,
    fullMem_focus_delayed hm, hQ⟩

private theorem m6_set64_full_spec {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {idx val : BitVec 64} {Q : Post []} {X : XPost}
    (hlen : s.LengthsOk c) (hi : idx.toNat + 1 < s.scratch.delayed.length)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ m', (FullMem c { s with scratch :=
      { s.scratch with delayed := m6Set64List s.scratch.delayed idx.toNat val } } ⋆ R) m' →
      Q () m') :
    m6Set64Spec (c.pDelayed, idx, val, ()) m Q X :=
  ⟨s.scratch.delayed, m6ScrDynRest c s ⋆ R, hi, m6_del_len_lt62 c hlen,
    fullMem_focus_delayed hm, fun m' hm' => hQ m' (fullMem_unfocus_delayed hm')⟩

/-! ## 3. Layout Sizeof & 64-bit `delayed` Helpers (`4` fns) -/

theorem full_m6_hdr_sizeof_wp (Γ : Env) :
    ∀ a m Q X, m6HdrSizeofSpec a m Q X → Func.wp Γ full_m6_hdr_sizeof_body a m Q X := by
  rintro ⟨⟩ m Q X hQ; c0_steps; exact hQ

theorem full_m6_ext_sizeof_wp (Γ : Env) :
    ∀ a m Q X, m6ExtSizeofSpec a m Q X → Func.wp Γ full_m6_ext_sizeof_body a m Q X := by
  rintro ⟨⟩ m Q X hQ; c0_steps; exact hQ

private theorem arr32_load_m6 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (hi : i.toNat < xs.length) (hm : (array (t := i32) a xs ⋆ F) m) :
    loadVal m i32 (a + i * 4) = some xs[i.toNat] := by
  rw [show a + i * 4 = a + BitVec.ofNat 64 (4 * i.toNat) from by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]]
  exact loadVal_array (t := i32) (by decide) hi hm

private theorem arr32_store_m6 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (v : BitVec 32) (hi : i.toNat < xs.length)
    (hm : (array (t := i32) a xs ⋆ F) m) :
    storeOk m i32 (a + i * 4) ∧
    (array (t := i32) a (xs.set i.toNat v) ⋆ F) (storeMem m i32 (a + i * 4) v) := by
  rw [show a + i * 4 = a + BitVec.ofNat 64 (4 * i.toNat) from by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]]
  exact store_array (t := i32) v (by decide) hi hm

theorem full_m6_get64_wp (Γ : Env) :
    ∀ a m Q X, m6Get64Spec a m Q X → Func.wp Γ full_m6_get64_body a m Q X := by
  rintro ⟨del_ptr, idx, ⟨⟩⟩ m Q X ⟨del, R, hi1, hlen, hm, hQ⟩
  have hi0 : idx.toNat < del.length := by omega
  have hip1 : (idx + (1 : BitVec 64)).toNat = idx.toNat + 1 := by bv_omega
  have hi1' : (idx + (1 : BitVec 64)).toNat < del.length := by omega
  unfold Func.wp full_m6_get64_body
  c0_hsteps_nogrp
  have heq : m6Get64Val del idx.toNat =
      del[idx.toNat].setWidth 64 |||
        (del[(idx + (1 : BitVec 64)).toNat].setWidth 64 <<< (32 : BitVec 64)) := by
    unfold m6Get64Val
    rw [List.getElem?_eq_getElem hi0, List.getElem?_eq_getElem hi1,
      Option.getD_some, Option.getD_some]
    simp only [hip1]
    rfl
  rw [heq] at hQ
  exact hQ

theorem full_m6_set64_wp (Γ : Env) :
    ∀ a m Q X, m6Set64Spec a m Q X → Func.wp Γ full_m6_set64_body a m Q X := by
  rintro ⟨del_ptr, idx, val, ⟨⟩⟩ m Q X ⟨del, R, hi1, hlen, hm, hQ⟩
  have hi0 : idx.toNat < del.length := by omega
  have hip1 : (idx + 1#64).toNat = idx.toNat + 1 := by bv_omega
  have hlen0 : (del.set idx.toNat (val.setWidth 32)).length = del.length := List.length_set
  have hi1' : (idx + 1#64).toNat <
      (del.set idx.toNat (val.setWidth 32)).length := by omega
  unfold Func.wp full_m6_set64_body
  c0_hsteps_nogrp
  have heq :
      (del.set idx.toNat (val.setWidth 32)).set (idx + 1#64).toNat
        ((val >>> (32 : BitVec 64)).setWidth 32) = m6Set64List del idx.toNat val := by
    unfold m6Set64List; rw [hip1]; rfl
  exact hQ m (Eq.mp (congrArg (fun xs => (array del_ptr xs ⋆ R) m) heq) hm)

/-! ## 4. `full_m6_ext_ready` & `full_m6_sync_legacy_tiers` (`2` fns) -/

theorem full_m6_ext_ready_wp (Γ : Env)
    (hGet64 : ∀ a m Q X, m6Get64Spec a m Q X → Γ "full_m6_get64" [i64, i64] [i64] a m Q X)
    (hSet64 : ∀ a m Q X, m6Set64Spec a m Q X → Γ "full_m6_set64" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, m6ExtReadySpec a m Q X → Func.wp Γ full_m6_ext_ready_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  have hdel_len := hlen.scratch_ok.delayed_len_arr
  c0_hsteps_nogrp
  · have hlt : c.delayed_cap < fullM6DelMinCap := by
      have hc0 : c.delayed_cap < 200 := by
        have := c.hdel; unfold dimacsBound at this; c0_bound
      exact hc0
    exact hQ (false, ()) s m rfl hlen
      ⟨FullM6ScratchPres.refl s,
       ⟨(fun hf => by cases hf), fun hle => by omega⟩,
       (fun hf => by cases hf), fun _ => rfl⟩ hm
  · have hge_cap : fullM6DelMinCap ≤ c.delayed_cap := by
      have := c.hdel; unfold dimacsBound at this; unfold fullM6DelMinCap; c0_bound
    have hge_len : fullM6DelTotalU32s ≤ s.scratch.delayed.length := by
      unfold fullM6DelTotalU32s fullM6DelMinCap at *; omega
    c0_call hGet64
    refine m6_get64_full_spec hlen (by unfold fullM6DelMinCap at hge_cap; bv_omega) hm ?_
    c0_hsteps_nogrp
    · exact hQ (true, ()) s m rfl hlen
        ⟨FullM6ScratchPres.refl s, ⟨fun _ => hge_cap, fun _ => rfl⟩,
         fun _ => hc, (fun ht => by cases ht)⟩ hm
    · refine wp_loop_safety_slice_pure (ts := [i64]) (fullSafetySlice c) s R
        (fun st (i, ()) => 18 ≤ i.toNat ∧ i.toNat ≤ fullM6DelTotalU32s ∧
          FullM6ScratchPres s st)
        (fun (i, ()) => fullM6DelTotalU32s - i.toNat)
        (fun Jl hJl => by
          c0_steps
          exact hJl s (18#64, ()) m hm rfl hlen ⟨by decide, by decide, FullM6ScratchPres.refl s⟩)
        (fun Jl st (i, ()) ml hcore_l hlen_l ⟨hi18, hi_le, hpres_l⟩ hml hJl => ?_)
      dsimp only [fullSafetySlice] at hlen_l hml
      clear hm
      have hdl := hlen_l.scratch_ok.delayed_len_arr
      have hlen_ge : fullM6DelTotalU32s ≤ st.scratch.delayed.length := by
        unfold fullM6DelTotalU32s fullM6DelMinCap at *; omega
      c0_hsteps_nogrp
      · have hilt : i.toNat < fullM6DelTotalU32s := by
          unfold fullM6DelTotalU32s; c0_bound
        have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
        let st1 : FullState :=
          { st with scratch := { st.scratch with delayed := st.scratch.delayed.set i.toNat 0#32 } }
        dsimp only [fullSafetySlice] at hJl
        exact hJl st1 (i + 1#64, ()) m hm (by dsimp only; rw [hi1]; omega) rfl
          (hlen_l.with_scratch { hlen_l.scratch_ok with delayed_len_arr := by simp [hdl] })
          ⟨by dsimp only; rw [hi1]; omega, by dsimp only; rw [hi1]; omega,
           ⟨hpres_l.1, fun k hk => by
             dsimp only [st1]
             rw [List.getElem?_set_ne (by omega)]
             exact hpres_l.2 k hk⟩⟩
      · have hcap_ge : 200 ≤ c.delayed_cap := by unfold fullM6DelMinCap at hge_cap; exact hge_cap
        let del4 := (((st.scratch.delayed.set 18 2#32).set 19 2#32).set 20 6#32).set 21 6#32
        let s4 : FullState := { st with scratch := { st.scratch with delayed := del4 } }
        have hm4 : (FullMem c s4 ⋆ R) m := hm
        have h4len : s4.scratch.delayed.length = 3 * c.delayed_cap := by simp [s4, del4, hdl]
        have hlen4 : s4.LengthsOk c :=
          hlen_l.with_scratch { hlen_l.scratch_ok with delayed_len_arr := h4len }
        have h4w2b : FullM6DelayedW2bPres st s4 := fun k hk => by
          dsimp only [s4, del4]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        have h24 : (24 : BitVec 64).toNat = 24 := rfl
        have h38 : (38#64).toNat = 38 := rfl
        have h40 : (40#64).toNat = 40 := rfl
        have h16 : (16 : BitVec 64).toNat = 16 := rfl
        c0_call hSet64
        refine m6_set64_full_spec hlen4 (by rw [h4len]; omega) hm4 fun m5 hm5 => ?_
        let del5 := m6Set64List del4 24 2#64
        let s5 : FullState := { s4 with scratch := { s4.scratch with delayed := del5 } }
        have h5len : s5.scratch.delayed.length = 3 * c.delayed_cap := by
          simp [s5, del5, del4, m6Set64List_length, hdl]
        have hlen5 : s5.LengthsOk c :=
          hlen4.with_scratch { hlen4.scratch_ok with delayed_len_arr := h5len }
        have h5w2b : FullM6DelayedW2bPres s4 s5 := fun k hk => m6Set64List_get_lt _ 24 _ (by omega)
        c0_hsteps_nogrp
        c0_call hSet64
        refine m6_set64_full_spec hlen5 (by rw [h5len]; omega) hm5 fun m6 hm6 => ?_
        let del6 := m6Set64List del5 38 s4.scratch.fwd_sub_cnt
        let s6 : FullState := { s5 with scratch := { s5.scratch with delayed := del6 } }
        have h6len : s6.scratch.delayed.length = 3 * c.delayed_cap := by
          simp [s6, del6, del5, del4, m6Set64List_length, hdl]
        have hlen6 : s6.LengthsOk c :=
          hlen5.with_scratch { hlen5.scratch_ok with delayed_len_arr := h6len }
        have h6w2b : FullM6DelayedW2bPres s5 s6 := fun k hk => m6Set64List_get_lt _ 38 _ (by omega)
        c0_hsteps_nogrp
        c0_call hSet64
        refine m6_set64_full_spec hlen6 (by rw [h6len]; omega) hm6 fun m7 hm7 => ?_
        let del7 := m6Set64List del6 40 s5.scratch.fwd_str_cnt
        let s7 : FullState := { s6 with scratch := { s6.scratch with delayed := del7 } }
        have h7len : s7.scratch.delayed.length = 3 * c.delayed_cap := by
          simp [s7, del7, del6, del5, del4, m6Set64List_length, hdl]
        have hlen7 : s7.LengthsOk c :=
          hlen6.with_scratch { hlen6.scratch_ok with delayed_len_arr := h7len }
        have h7w2b : FullM6DelayedW2bPres s6 s7 := fun k hk => m6Set64List_get_lt _ 40 _ (by omega)
        c0_hsteps_nogrp
        c0_call hSet64
        refine m6_set64_full_spec hlen7 (by rw [h7len]; omega) hm7 fun m8 hm8 => ?_
        let del8 := m6Set64List del7 16 fullM6Magic
        let s8 : FullState := { s7 with scratch := { s7.scratch with delayed := del8 } }
        have h8len : s8.scratch.delayed.length = 3 * c.delayed_cap := by
          simp [s8, del8, del7, del6, del5, del4, m6Set64List_length, hdl]
        have hlen8 : s8.LengthsOk c :=
          hlen7.with_scratch { hlen7.scratch_ok with delayed_len_arr := h8len }
        have h8w2b : FullM6DelayedW2bPres s7 s8 := fun k hk => m6Set64List_get_lt _ 16 _ (by omega)
        have hpres8 : FullM6ScratchPres s s8 :=
          ⟨hpres_l.1,
           hpres_l.2.trans (h4w2b.trans (h5w2b.trans (h6w2b.trans (h7w2b.trans h8w2b))))⟩
        have hmag8 : m6Get64Val s8.scratch.delayed m6DelMagicIdx = fullM6Magic := by
          unfold m6DelMagicIdx; rw [h8len] at *
          exact m6Get64Val_set64_self fullM6Magic (by rw [h7len]; omega)
        c0_steps
        exact hQ (true, ()) s8 m8 hcore_l hlen8
          ⟨hpres8, ⟨fun _ => hge_cap, fun _ => rfl⟩, fun _ => hmag8,
           fun h => Bool.noConfusion h⟩ hm8

theorem full_m6_sync_legacy_tiers_wp (Γ : Env)
    (hReady : ∀ a m Q X, m6ExtReadySpec a m Q X →
      Γ "full_m6_ext_ready" [i64] [.bool] a m Q X) :
    ∀ a m Q X, m6SafetyVoidSpec a m Q X →
      Func.wp Γ full_m6_sync_legacy_tiers_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  c0_hsteps_nogrp
  c0_call hReady
  refine ⟨c, s, R, rfl, hlen, hm,
    fun ⟨ok, ⟨⟩⟩ s1 m1 hcore1 hlen1 ⟨hpres1, hok_iff, _, _⟩ hm1 => ?_⟩
  dsimp only [fullSafetySlice] at hlen1 hm1
  clear hm hlen
  c0_hsteps_nogrp
  · have hcap1 := hok_iff.mp hc
    have hdl1 := hlen1.scratch_ok.delayed_len_arr
    have h18 : 18 < s1.scratch.delayed.length := by unfold fullM6DelMinCap at hcap1; omega
    have h21 : 21 < s1.scratch.delayed.length := by unfold fullM6DelMinCap at hcap1; omega
    c0_hsteps <;>
      (refine hQ () _ m ?_ ?_ ?_ hm
       · exact hcore1
       · exact hlen1.with_scratch
           { hlen1.scratch_ok with walk_vals_len := hlen1.scratch_ok.walk_vals_len }
       · exact ⟨hpres1.1, hpres1.2⟩)
  · exact hQ () s1 m1 hcore1 hlen1 hpres1 hm1

/-! ## 5. Mode-Split Tier Recomputation, Glue Histogram & Getters (`7` fns) -/

theorem full_m6_recompute_tiers_legacy_wp (Γ : Env) :
    ∀ a m Q X, m6SafetyVoidSpec a m Q X →
      Func.wp Γ full_m6_recompute_tiers_legacy_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  have hgu_len := hlen.scratch_ok.glue_used_len
  m6_to_group
  refine wp_loop_inv (ts := [i64, i64])
    (fun (_tot, g, ()) mL => g.toNat ≤ 64 ∧ mL = m)
    (fun (_, g, ()) _ => 64 - g.toNat)
    (fun Jl hJl => by c0_steps; exact hJl (_, _, ()) m ⟨Nat.zero_le _, rfl⟩)
    (fun Jl (tot, g, ()) mL ⟨hg64, hmL⟩ hJl => ?_)
  · subst mL
    c0_hsteps_nogrp
    · have hg_lt : g.toNat < s.scratch.glue_used.length := by rw [hgu_len]; c0_bound
      have hg1 : (g + 1#64).toNat = g.toNat + 1 := by bv_omega
      c0_hsteps <;> exact hJl (_, g + 1#64, ()) m (by dsimp only; omega) ⟨by omega, rfl⟩
    · refine wp_join_group (ts := [i64, i64, i64]) (fun _ m2 => m2 = m)
        (fun _ (_g', t1, t2, ()) m2 hm2 => ?_) ?_
      · subst m2
        refine wp_join_group (ts := [i64]) (fun _ m2 => m2 = m)
          (fun _ (t2c, ()) m2 hm2 => ?_) ?_
        · subst m2
          c0_steps
          let s1 : FullState := { s with scratch := { s.scratch with tier1 := t1, tier2 := t2c } }
          refine hQ () s1 _ rfl
            (hlen.with_scratch { hlen.scratch_ok with
              walk_vals_len := hlen.scratch_ok.walk_vals_len })
            (FullM6ScratchPres.refl s) (by assumption)
        · intro _ hJt2c; c0_steps <;> exact hJt2c (_, ()) m rfl
      · intro _ hJt; c0_hsteps_nogrp
        · refine wp_join_group (ts := [i64]) (fun _ m2 => m2 = m)
            (fun _ (_lim1, ()) m2 hm2 => ?_) ?_
          · subst m2
            refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m)
              (fun _ (_lim2, ()) m3 hm3 => ?_) ?_
            · subst m3
              refine wp_join_group (ts := [i64, i64, i64, i64, .bool, .bool])
                (fun _ m4 => m4 = m)
                (fun _ (_g', _t1, _t2, _acc, _g1, _g2, ()) m4 hm4 => by
                  subst m4; c0_hsteps <;> exact hJt (_, _, _, ()) m rfl)
                ?_
              · intro _ hJb
                c0_hsteps_nogrp
                refine wp_loop_inv (ts := [i64, i64, i64, .bool])
                  (fun (g, _t1, _acc, _g1, ()) mL => g.toNat ≤ 64 ∧ mL = m)
                  (fun (g, _, _, _, ()) _ => 64 - g.toNat)
                  (fun Ja hJa => by c0_steps; exact hJa (0#64, _, _, _, ()) m ⟨by decide, rfl⟩)
                  (fun Ja (g, t1, acc, g1, ()) mL ⟨hg64', hmL⟩ hJa => ?_)
                · subst mL
                  c0_hsteps_nogrp
                  · have hg_lt : g.toNat < s.scratch.glue_used.length := by rw [hgu_len]; c0_bound
                    have hg1 : (g + 1#64).toNat = g.toNat + 1 := by bv_omega
                    c0_hsteps
                    all_goals
                      try
                        exact hJa (g + 1#64, _, _, _, ()) m
                          (by dsimp only; omega) ⟨by omega, rfl⟩
                    all_goals (c0_hsteps; exact hJb (_, _, _, _, _, _, ()) m rfl)
                  · c0_hsteps <;> exact hJb (_, _, _, _, _, _, ()) m rfl
            · intro _ hJ2; c0_steps <;> exact hJ2 (_, ()) m rfl
          · intro _ hJ1; c0_hsteps <;> exact hJ1 (_, ()) m rfl
        · exact hJt (_, _, _, ()) m rfl

theorem full_m6_recompute_tiers_ext_wp (Γ : Env)
    (hGet64 : ∀ a m Q X, m6Get64Spec a m Q X → Γ "full_m6_get64" [i64, i64] [i64] a m Q X)
    (hSet64 : ∀ a m Q X, m6Set64Spec a m Q X → Γ "full_m6_set64" [i64, i64, i64] [] a m Q X)
    (hSync : ∀ a m Q X, m6SafetyVoidSpec a m Q X →
      Γ "full_m6_sync_legacy_tiers" [i64] [] a m Q X) :
    ∀ a m Q X, m6RecomputeExtSpec a m Q X →
      Func.wp Γ full_m6_recompute_tiers_ext_body a m Q X := by
  rintro ⟨h, mode, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hcap1, hmode⟩, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  have hdel_len := hlen.scratch_ok.delayed_len_arr
  have hcap200 : 200 ≤ c.delayed_cap := by unfold fullM6DelMinCap at hcap1; exact hcap1
  m6_to_group
  refine wp_join_group (ts := [i64]) (fun (base, ()) m2 =>
      m2 = m ∧ (mode = 0#64 ∧ base = 54#64 ∨ mode = 1#64 ∧ base = 310#64))
    (fun _ (base, ()) m2 ⟨hm2, hbm⟩ => ?_) ?_
  · subst m2
    have hbase_or : base = 54#64 ∨ base = 310#64 := by
      rcases hbm with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> (first | exact Or.inl rfl | exact Or.inr rfl)
    have hbase_lt : ∀ g : BitVec 64, g.toNat < 128 →
        (base + (g <<< (1 : BitVec 64))).toNat + 1 < s.scratch.delayed.length := by
      intro g hg; rw [hdel_len]; exact m6_used_idx_lt hcap200 hg hbase_or
    refine wp_loop_inv (ts := [i64, i64])
      (fun (_tot, g, ()) mL => g.toNat ≤ 128 ∧ mL = m)
      (fun (_, g, ()) _ => 128 - g.toNat)
      (fun Jl hJl => by c0_steps; exact hJl (_, _, ()) m ⟨Nat.zero_le _, rfl⟩)
      (fun Jl (tot, g, ()) mL ⟨hg128, hmL⟩ hJl => ?_)
    · subst mL
      c0_hsteps_nogrp
      · have hg_lt : g.toNat < 128 := by c0_bound
        have hg1 : (g + 1#64).toNat = g.toNat + 1 := by bv_omega
        c0_call hGet64
        refine m6_get64_full_spec hlen (hbase_lt g hg_lt) hm ?_
        c0_hsteps <;> exact hJl (_, g + 1#64, ()) m (by dsimp only; omega) ⟨by omega, rfl⟩
      · refine wp_join_group (ts := [i64]) (fun (tu_idx, ()) m2 =>
            m2 = m ∧ (mode = 0#64 ∧ tu_idx = 26#64 ∨ mode = 1#64 ∧ tu_idx = 28#64))
          (fun _ (tu_idx, ()) m2 ⟨hm2, htu⟩ => ?_) ?_
        · subst m2
          have htu_or : tu_idx = 26#64 ∨ tu_idx = 28#64 := by
            rcases htu with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> (first | exact Or.inl rfl | exact Or.inr rfl)
          have htu_lt : tu_idx.toNat + 1 < s.scratch.delayed.length := by
            rw [hdel_len]; exact m6_used_tu_lt hcap200 htu_or
          c0_call hSet64
          refine m6_set64_full_spec hlen htu_lt hm fun m2 hm2 => ?_
          let del2 := m6Set64List s.scratch.delayed tu_idx.toNat tot
          let s2 : FullState := { s with scratch := { s.scratch with delayed := del2 } }
          have hlen2 : s2.LengthsOk c :=
            hlen.with_scratch { hlen.scratch_ok with
              delayed_len_arr := by dsimp only [s2, del2]; rw [m6Set64List_length, hdel_len] }
          have h2w2b : FullM6DelayedW2bPres s s2 := fun k hk => by
            dsimp only [s2, del2]
            rcases htu_or with rfl | rfl
            · exact m6Set64List_get_lt _ _ _ (by rw [show (26#64).toNat = 26 from rfl]; omega)
            · exact m6Set64List_get_lt _ _ _ (by rw [show (28#64).toNat = 28 from rfl]; omega)
          have hpres2 : FullM6ScratchPres s s2 := ⟨probePres_refl_m6 s, h2w2b⟩
          have hbase_lt2 : ∀ g : BitVec 64, g.toNat < 128 →
              (base + (g <<< (1 : BitVec 64))).toNat + 1 < s2.scratch.delayed.length := by
            intro g hg; dsimp only [s2, del2]; rw [m6Set64List_length]; exact hbase_lt g hg
          clear hbase_lt hm
          refine wp_join_group (ts := [i64, i64, i64]) (fun _ m3 => m3 = m2)
            (fun _ (_g', t1, t2, ()) m3 hm3 => ?_) ?_
          · subst m3
            refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m2)
              (fun _ (t2c, ()) m3 hm3 => ?_) ?_
            · subst m3
              have h2len : s2.scratch.delayed.length = 3 * c.delayed_cap :=
                hlen2.scratch_ok.delayed_len_arr
              have ht1_idx : ((18 : BitVec 64) + mode).toNat < s2.scratch.delayed.length := by
                rw [h2len]; exact m6_tier_mode_lt hcap200 hmode (Or.inl rfl)
              have ht2_idx : ((20 : BitVec 64) + mode).toNat < s2.scratch.delayed.length := by
                rw [h2len]; exact m6_tier_mode_lt hcap200 hmode (Or.inr rfl)
              c0_hsteps_nogrp
              let del2' := (s2.scratch.delayed.set ((18 : BitVec 64) + mode).toNat
                (t1.setWidth 32)).set ((20 : BitVec 64) + mode).toNat (t2c.setWidth 32)
              let s2' : FullState := { s2 with scratch := { s2.scratch with delayed := del2' } }
              have h2'len : s2'.scratch.delayed.length = 3 * c.delayed_cap := by
                dsimp only [s2', del2']; rw [List.length_set, List.length_set, h2len]
              c0_call hSync
              refine ⟨c, s2', R, rfl,
                hlen2.with_scratch { hlen2.scratch_ok with delayed_len_arr := h2'len },
                by assumption, fun () s5 m5 hcore5 hlen5 hpres5 hm5 => ?_⟩
              have h4w2b : FullM6DelayedW2bPres s2 s2' := fun k hk => by
                dsimp only [s2', del2']; exact m6_tier_mode_ge16 hmode hk _ _ _
              exact hQ () s5 m5 hcore5 hlen5 (hpres2.trans ⟨hpres5.1, h4w2b.trans hpres5.2⟩) hm5
            · intro _ hJt2c; c0_steps <;> exact hJt2c (_, ()) m2 rfl
          · intro _ hJt; c0_hsteps_nogrp
            · refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m2)
                (fun _ (_lim1, ()) m3 hm3 => ?_) ?_
              · subst m3
                refine wp_join_group (ts := [i64]) (fun _ m4 => m4 = m2)
                  (fun _ (_lim2, ()) m4 hm4 => ?_) ?_
                · subst m4
                  refine wp_join_group (ts := [i64, i64, i64, i64, .bool, .bool])
                    (fun _ m5 => m5 = m2)
                    (fun _ (_g', _t1, _t2, _acc, _g1, _g2, ()) m5 hm5 => by
                      subst m5; c0_hsteps <;> exact hJt (_, _, _, ()) m2 rfl)
                    ?_
                  · intro _ hJb
                    c0_hsteps_nogrp
                    refine wp_loop_inv (ts := [i64, i64, i64, .bool])
                      (fun (g, _t1, _acc, _g1, ()) mL => g.toNat ≤ 128 ∧ mL = m2)
                      (fun (g, _, _, _, ()) _ => 128 - g.toNat)
                      (fun Ja hJa => by
                        c0_steps
                        exact hJa (0#64, _, _, _, ()) m2 ⟨by decide, rfl⟩)
                      (fun Ja (g, t1, acc, g1, ()) mL ⟨hg128', hmL⟩ hJa => ?_)
                    · subst mL
                      c0_hsteps_nogrp
                      · have hg_lt : g.toNat < 128 := by c0_bound
                        have hg1 : (g + 1#64).toNat = g.toNat + 1 := by bv_omega
                        c0_call hGet64
                        refine m6_get64_full_spec hlen2 (hbase_lt2 g hg_lt) hm2 ?_
                        c0_hsteps
                        all_goals
                          try
                            exact hJa (g + 1#64, _, _, _, ()) m2
                              (by dsimp only; omega) ⟨by omega, rfl⟩
                        all_goals (c0_hsteps; exact hJb (_, _, _, _, _, _, ()) m2 rfl)
                      · c0_hsteps <;> exact hJb (_, _, _, _, _, _, ()) m2 rfl
                · intro _ hJ2; c0_steps <;> exact hJ2 (_, ()) m2 rfl
              · intro _ hJ1; c0_hsteps <;> exact hJ1 (_, ()) m2 rfl
            · exact hJt (_, _, _, ()) m2 rfl
        · intro _ hJtu; c0_steps
          · exact hJtu (_, ()) m ⟨rfl, Or.inl ⟨‹_›, rfl⟩⟩
          · exact hJtu (_, ()) m
              ⟨rfl, Or.inr ⟨hmode.resolve_left (fun h0 => hc (by rw [h0]; rfl)), rfl⟩⟩
  · intro _ hJb; c0_steps
    · exact hJb (_, ()) m ⟨rfl, Or.inl ⟨‹_›, rfl⟩⟩
    · exact hJb (_, ()) m ⟨rfl, Or.inr ⟨hmode.resolve_left (fun h0 => hc (by rw [h0]; rfl)), rfl⟩⟩

theorem full_m6_recompute_tiers_mode_wp (Γ : Env)
    (hReady : ∀ a m Q X, m6ExtReadySpec a m Q X →
      Γ "full_m6_ext_ready" [i64] [.bool] a m Q X)
    (hLeg : ∀ a m Q X, m6SafetyVoidSpec a m Q X →
      Γ "full_m6_recompute_tiers_legacy" [i64] [] a m Q X)
    (hExt : ∀ a m Q X, m6RecomputeExtSpec a m Q X →
      Γ "full_m6_recompute_tiers_ext" [i64, i64] [] a m Q X) :
    ∀ a m Q X, m6SafetyArgVoidSpec i64 a m Q X →
      Func.wp Γ full_m6_recompute_tiers_mode_body a m Q X := by
  rintro ⟨h, st, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  m6_to_group
  refine wp_join_group (ts := [i64]) (fun (mode, ()) m1 => m1 = m ∧ (mode = 0#64 ∨ mode = 1#64))
    (fun _ (mode, ()) m1 ⟨hm1, hmode⟩ => ?_) ?_
  · subst m1
    c0_hsteps_nogrp
    c0_call hReady
    refine ⟨c, s, R, rfl, hlen, hm,
      fun ⟨ok, ⟨⟩⟩ s1 m1 hcore1 hlen1 ⟨hpres1, hok_iff, _, _⟩ hm1 => ?_⟩
    dsimp only [fullSafetySlice] at hlen1 hm1
    clear hm hlen
    c0_hsteps_nogrp
    · c0_call hExt
      refine ⟨c, s1, R, ⟨rfl, hok_iff.mp hc, hmode⟩, hlen1, hm1,
        fun () s2 m2 hcore2 hlen2 hpres2 hm2 => ?_⟩
      c0_steps
      exact hQ () s2 m2 (hcore1.trans hcore2) hlen2 (hpres1.trans hpres2) hm2
    · c0_call hLeg
      refine ⟨c, s1, R, rfl, hlen1, hm1, fun () s2 m2 hcore2 hlen2 hpres2 hm2 => ?_⟩
      c0_steps
      exact hQ () s2 m2 (hcore1.trans hcore2) hlen2 (hpres1.trans hpres2) hm2
  · intro _ hJm; c0_hsteps
    · exact hJm (_, ()) m ⟨rfl, Or.inr rfl⟩
    · exact hJm (_, ()) m ⟨rfl, Or.inl rfl⟩

theorem full_recompute_tiers_m6_wp (Γ : Env)
    (hMode : ∀ a m Q X, m6SafetyArgVoidSpec i64 a m Q X →
      Γ "full_m6_recompute_tiers_mode" [i64, i64] [] a m Q X) :
    ∀ a m Q X, m6SafetyVoidSpec a m Q X →
      Func.wp Γ full_recompute_tiers_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  m6_to_group
  refine wp_join_group (ts := [i64]) (fun _ m1 => m1 = m)
    (fun _ (st, ()) m1 hm1 => by subst m1; c0_call hMode; exact ⟨c, s, R, rfl, hlen, hm, hQ⟩)
    (fun _ hJs => by c0_hsteps <;> exact hJs (_, ()) m rfl)

theorem full_m6_update_tier_limits_wp (Γ : Env)
    (hReady : ∀ a m Q X, m6ExtReadySpec a m Q X →
      Γ "full_m6_ext_ready" [i64] [.bool] a m Q X)
    (hGet64 : ∀ a m Q X, m6Get64Spec a m Q X → Γ "full_m6_get64" [i64, i64] [i64] a m Q X)
    (hSet64 : ∀ a m Q X, m6Set64Spec a m Q X → Γ "full_m6_set64" [i64, i64, i64] [] a m Q X)
    (hRecomp : ∀ a m Q X, m6SafetyVoidSpec a m Q X →
      Γ "full_recompute_tiers_m6" [i64] [] a m Q X) :
    ∀ a m Q X, m6SafetyVoidSpec a m Q X →
      Func.wp Γ full_m6_update_tier_limits_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  c0_hsteps_nogrp
  c0_call hReady
  refine ⟨c, s, R, rfl, hlen, hm,
    fun ⟨ok, ⟨⟩⟩ s1 m1 hcore1 hlen1 ⟨hpres1, hok_iff, _, _⟩ hm1 => ?_⟩
  dsimp only [fullSafetySlice] at hlen1 hm1
  clear hm hlen
  c0_hsteps_nogrp
  · have hcap1 := hok_iff.mp hc
    have hdl1 := hlen1.scratch_ok.delayed_len_arr
    c0_call hGet64
    refine m6_get64_full_spec hlen1
      (by unfold fullM6DelMinCap at hcap1; rw [show (22 : BitVec 64).toNat = 22 from rfl]; omega)
      hm1 ?_
    m6_to_group
    refine wp_join_group (ts := [])
      (fun () mJ => ∃ sJ : FullState, PreservesCoreSlice (fullSafetySlice c).coreProj s1 sJ ∧
        sJ.LengthsOk c ∧ FullM6ScratchPres s sJ ∧ (FullMem c sJ ⋆ R) mJ)
      (fun _ () mJ ⟨sJ, hcoreJ, hlenJ, hpresJ, hmJ⟩ => by
        c0_steps; exact hQ () sJ mJ (hcore1.trans hcoreJ) hlenJ hpresJ hmJ)
      (fun _ hJ => by
        c0_hsteps_nogrp
        · c0_call hRecomp
          refine ⟨c, s1, R, rfl, hlen1, hm1, fun () s2 m2 hcore2 hlen2 hpres2 hm2 => ?_⟩
          dsimp only [fullSafetySlice] at hlen2 hm2
          have hdl2 := hlen2.scratch_ok.delayed_len_arr
          c0_hsteps_nogrp
          c0_call hGet64
          refine m6_get64_full_spec hlen2
            (by unfold fullM6DelMinCap at hcap1
                rw [show (24 : BitVec 64).toNat = 24 from rfl]; omega)
            hm2 ?_
          refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m2)
            (fun _ (iv, ()) m3 hm3 => ?_) ?_
          · subst m3
            c0_hsteps_nogrp
            c0_call hSet64
            refine m6_set64_full_spec hlen2
              (by unfold fullM6DelMinCap at hcap1
                  rw [show (24 : BitVec 64).toNat = 24 from rfl]; omega)
              hm2 fun m3 hm3 => ?_
            let del3 := m6Set64List s2.scratch.delayed 24 iv
            let s3 : FullState := { s2 with scratch := { s2.scratch with delayed := del3 } }
            have hlen3 : s3.LengthsOk c :=
              hlen2.with_scratch { hlen2.scratch_ok with
                delayed_len_arr := by dsimp only [s3, del3]; rw [m6Set64List_length, hdl2] }
            have h3w2b : FullM6DelayedW2bPres s2 s3 :=
              fun k hk => m6Set64List_get_lt _ 24 _ (by omega)
            c0_hsteps_nogrp
            c0_call hSet64
            refine m6_set64_full_spec hlen3
              (by rw [hlen3.scratch_ok.delayed_len_arr]
                  have h22 : (22 : BitVec 64).toNat = 22 := rfl
                  unfold fullM6DelMinCap at hcap1; omega)
              hm3 fun m4 hm4 => ?_
            let del4 := m6Set64List del3 22 (s2.scratch.conflicts + iv)
            let s4 : FullState := { s3 with scratch := { s3.scratch with delayed := del4 } }
            have hlen4 : s4.LengthsOk c :=
              hlen3.with_scratch { hlen3.scratch_ok with
                delayed_len_arr := by
                  dsimp only [s4, del4, del3]; rw [m6Set64List_length, m6Set64List_length, hdl2] }
            have h4w2b : FullM6DelayedW2bPres s3 s4 :=
              fun k hk => m6Set64List_get_lt _ 22 _ (by omega)
            c0_steps
            exact hJ () m4 ⟨s4, hcore2, hlen4,
              hpres1.trans (hpres2.trans ⟨probePres_refl_m6 s2, h3w2b.trans h4w2b⟩), hm4⟩
          · intro _ hJiv; c0_steps <;> exact hJiv (_, ()) m2 rfl
        · c0_steps; exact hJ () m1 ⟨s1, rfl, hlen1, hpres1, hm1⟩)
  · m6_to_group
    refine wp_join_group (ts := [])
      (fun () mJ => ∃ sJ : FullState, PreservesCoreSlice (fullSafetySlice c).coreProj s1 sJ ∧
        sJ.LengthsOk c ∧ FullM6ScratchPres s sJ ∧ (FullMem c sJ ⋆ R) mJ)
      (fun _ () mJ ⟨sJ, hcoreJ, hlenJ, hpresJ, hmJ⟩ => by
        c0_steps; exact hQ () sJ mJ (hcore1.trans hcoreJ) hlenJ hpresJ hmJ)
      (fun _ hJ => by
        c0_hsteps_nogrp
        · c0_call hRecomp
          refine ⟨c, s1, R, rfl, hlen1, hm1, fun () s2 m2 hcore2 hlen2 hpres2 hm2 => ?_⟩
          c0_steps
          exact hJ () m2 ⟨s2, hcore2, hlen2, hpres1.trans hpres2, hm2⟩
        · c0_steps; exact hJ () m1 ⟨s1, rfl, hlen1, hpres1, hm1⟩
        · c0_steps; exact hJ () m1 ⟨s1, rfl, hlen1, hpres1, hm1⟩)

theorem full_m6_record_used_wp (Γ : Env)
    (hReady : ∀ a m Q X, m6ExtReadySpec a m Q X →
      Γ "full_m6_ext_ready" [i64] [.bool] a m Q X)
    (hGet64 : ∀ a m Q X, m6Get64Spec a m Q X → Γ "full_m6_get64" [i64, i64] [i64] a m Q X)
    (hSet64 : ∀ a m Q X, m6Set64Spec a m Q X → Γ "full_m6_set64" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, m6SafetyArgVoidSpec i64 a m Q X →
      Func.wp Γ full_m6_record_used_body a m Q X := by
  rintro ⟨h, glue, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  c0_hsteps_nogrp
  c0_call hReady
  refine ⟨c, s, R, rfl, hlen, hm,
    fun ⟨ok, ⟨⟩⟩ s1 m1 hcore1 hlen1 ⟨hpres1, hok_iff, _, _⟩ hm1 => ?_⟩
  dsimp only [fullSafetySlice] at hlen1 hm1
  clear hm hlen
  have hgu1 := hlen1.scratch_ok.glue_used_len
  have hdl1 := hlen1.scratch_ok.delayed_len_arr
  c0_hsteps_nogrp
  · have hcap1 := hok_iff.mp hc
    have hcap200 : 200 ≤ c.delayed_cap := by unfold fullM6DelMinCap at hcap1; exact hcap1
    refine wp_join_group (ts := [i64]) (fun (st, ()) m2 => m2 = m1 ∧ (st = 0#64 ∨ st = 1#64))
      (fun _ (st, ()) m2 ⟨hm2, hst⟩ => ?_) ?_
    · subst m2
      refine wp_join_group (ts := [i64]) (fun (gi, ()) m3 => m3 = m1 ∧ gi.toNat < 128)
        (fun _ (gi, ()) m3 ⟨hm3, hgi⟩ => ?_) ?_
      · subst m3
        refine wp_join_group (ts := [i64]) (fun (base, ()) m4 =>
            m4 = m1 ∧ (st = 0#64 ∧ base = 54#64 ∨ st = 1#64 ∧ base = 310#64))
          (fun _ (base, ()) m4 ⟨hm4, hsb⟩ => ?_) ?_
        · subst m4
          have hbase_or : base = 54#64 ∨ base = 310#64 := by
            rcases hsb with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> (first | exact Or.inl rfl | exact Or.inr rfl)
          have hb_lt : (base + (gi <<< (1 : BitVec 64))).toNat + 1 < s1.scratch.delayed.length := by
            rw [hdl1]; exact m6_used_idx_lt hcap200 hgi hbase_or
          c0_hsteps_nogrp
          c0_call hGet64
          refine m6_get64_full_spec hlen1 hb_lt hm1 ?_
          refine wp_join_group (ts := [])
            (fun () m2 => ∃ del2 : List (BitVec 32), del2.length = 3 * c.delayed_cap ∧
              (∀ k < 16, del2[k]? = s1.scratch.delayed[k]?) ∧
              (FullMem c { s1 with scratch := { s1.scratch with delayed := del2 } } ⋆ R) m2)
            (fun _ () m2 ⟨del2, hdl2, h2w2b, hm2⟩ => ?_) ?_
          · let s2 : FullState := { s1 with scratch := { s1.scratch with delayed := del2 } }
            have hlen2 : s2.LengthsOk c :=
              hlen1.with_scratch { hlen1.scratch_ok with delayed_len_arr := hdl2 }
            refine wp_join_group (ts := [i64]) (fun (tu_idx, ()) m3 =>
                m3 = m2 ∧ (st = 0#64 ∧ tu_idx = 26#64 ∨ st = 1#64 ∧ tu_idx = 28#64))
              (fun _ (tu_idx, ()) m3 ⟨hm3, htu⟩ => ?_) ?_
            · subst m3
              have htu_or : tu_idx = 26#64 ∨ tu_idx = 28#64 := by
                rcases htu with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
                  (first | exact Or.inl rfl | exact Or.inr rfl)
              have htu_lt : tu_idx.toNat + 1 < s2.scratch.delayed.length := by
                dsimp only [s2]; rw [hdl2]; exact m6_used_tu_lt hcap200 htu_or
              c0_hsteps_nogrp
              c0_call hGet64
              refine m6_get64_full_spec hlen2 htu_lt hm2 ?_
              refine wp_join_group (ts := [])
                (fun () m3 => ∃ del3 : List (BitVec 32), del3.length = 3 * c.delayed_cap ∧
                  (∀ k < 16, del3[k]? = s2.scratch.delayed[k]?) ∧
                  (FullMem c { s2 with scratch := { s2.scratch with delayed := del3 } } ⋆ R) m3)
                (fun _ () m3 ⟨del3, hdl3, h3w2b, hm3⟩ => by
                  c0_steps
                  let s3 : FullState := { s2 with scratch := { s2.scratch with delayed := del3 } }
                  have hlen3 : s3.LengthsOk c :=
                    hlen2.with_scratch { hlen2.scratch_ok with delayed_len_arr := hdl3 }
                  exact hQ () s3 m3 hcore1 hlen3
                    ⟨hpres1.1, fun k hk => (h3w2b k hk).trans ((h2w2b k hk).trans (hpres1.2 k hk))⟩
                    hm3)
                (fun _ hJr => by
                  c0_hsteps_nogrp
                  · c0_call hSet64
                    refine m6_set64_full_spec hlen2 htu_lt hm2 fun m3 hm3 => ?_
                    c0_steps
                    exact hJr () m3 ⟨m6Set64List s2.scratch.delayed tu_idx.toNat _,
                      by rw [m6Set64List_length, hdl2],
                      fun k hk => by
                        rcases htu_or with rfl | rfl
                        · exact m6Set64List_get_lt _ _ _
                            (by rw [show (26#64).toNat = 26 from rfl]; omega)
                        · exact m6Set64List_get_lt _ _ _
                            (by rw [show (28#64).toNat = 28 from rfl]; omega),
                      hm3⟩
                  · c0_steps; exact hJr () m2 ⟨s2.scratch.delayed, hdl2, fun _ _ => rfl, hm2⟩)
            · intro _ hJtu; c0_steps
              · exact hJtu (_, ()) m2 ⟨rfl, Or.inl ⟨‹_›, rfl⟩⟩
              · exact hJtu (_, ()) m2
                  ⟨rfl, Or.inr ⟨hst.resolve_left (fun h0 => hc (by rw [h0]; rfl)), rfl⟩⟩
          · intro _ hJtu_pre; c0_hsteps_nogrp
            · c0_call hSet64
              refine m6_set64_full_spec hlen1 hb_lt hm1 fun m2 hm2 => ?_
              exact hJtu_pre () m2 ⟨m6Set64List s1.scratch.delayed _ _,
                by rw [m6Set64List_length, hdl1],
                fun k hk => m6Set64List_get_lt _ _ _
                  (Nat.lt_of_lt_of_le hk (m6_used_ge16 hgi hbase_or)),
                hm2⟩
            · exact hJtu_pre () m1 ⟨s1.scratch.delayed, hdl1, fun _ _ => rfl, hm1⟩
        · intro _ hJb; c0_steps
          · exact hJb (_, ()) m1 ⟨rfl, Or.inl ⟨‹_›, rfl⟩⟩
          · exact hJb (_, ()) m1
              ⟨rfl, Or.inr ⟨hst.resolve_left (fun h0 => hc (by rw [h0]; rfl)), rfl⟩⟩
      · intro _ hJg; c0_steps
        · exact hJg (_, ()) m1 ⟨rfl, by decide⟩
        · exact hJg (glue, ()) m1 ⟨rfl, by c0_bound⟩
    · intro _ hJs; c0_steps
      · exact hJs (_, ()) m1 ⟨rfl, Or.inr rfl⟩
      · exact hJs (_, ()) m1 ⟨rfl, Or.inl rfl⟩
  · refine wp_join_group (ts := [i64]) (fun (gi, ()) m2 => m2 = m1 ∧ gi.toNat < 64)
      (fun _ (gi, ()) m2 ⟨hm2, hgi⟩ => ?_) ?_
    · subst m2
      have hgi' : gi.toNat < s1.scratch.glue_used.length := by rw [hgu1]; exact hgi
      c0_hsteps
      · refine hQ () _ m ?_ ?_ ?_ hm
        · exact hcore1
        · exact hlen1.with_scratch { hlen1.scratch_ok with glue_used_len := by simp [hgu1] }
        · exact ⟨hpres1.1, hpres1.2⟩
      · exact hQ () s1 m1 hcore1 hlen1 hpres1 hm1
    · intro _ hJgi; c0_steps
      · exact hJgi (_, ()) m1 ⟨rfl, by decide⟩
      · exact hJgi (glue, ()) m1 ⟨rfl, by c0_bound⟩

theorem full_m6_get_tier1_wp (Γ : Env)
    (hReady : ∀ a m Q X, m6ExtReadySpec a m Q X →
      Γ "full_m6_ext_ready" [i64] [.bool] a m Q X) :
    ∀ a m Q X, m6SafetyBoolU64Spec a m Q X →
      Func.wp Γ full_m6_get_tier1_body a m Q X := by
  rintro ⟨h, viv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  c0_hsteps_nogrp
  c0_call hReady
  refine ⟨c, s, R, rfl, hlen, hm,
    fun ⟨ok, ⟨⟩⟩ s1 m1 hcore1 hlen1 ⟨hpres1, hok_iff, _, _⟩ hm1 => ?_⟩
  dsimp only [fullSafetySlice] at hlen1 hm1
  clear hm hlen
  c0_hsteps_nogrp
  · have hcap1 := hok_iff.mp hc
    have hcap200 : 200 ≤ c.delayed_cap := by unfold fullM6DelMinCap at hcap1; exact hcap1
    have hdl1 := hlen1.scratch_ok.delayed_len_arr
    refine wp_join_group (ts := [i64]) (fun (st, ()) m2 => m2 = m1 ∧ (st = 0#64 ∨ st = 1#64))
      (fun _ (st, ()) m2 ⟨hm2, hst⟩ => ?_) ?_
    · subst m2
      have hidx : ((18 : BitVec 64) + st).toNat < s1.scratch.delayed.length := by
        rw [hdl1]; exact m6_tier_mode_lt hcap200 hst (Or.inl rfl)
      c0_hsteps
      exact hQ _ s1 m1 hcore1 hlen1 hpres1 hm1
    · intro _ hJs; c0_steps
      · exact hJs (_, ()) m1 ⟨rfl, Or.inl rfl⟩
      · exact hJs (_, ()) m1 ⟨rfl, Or.inr rfl⟩
      · exact hJs (_, ()) m1 ⟨rfl, Or.inl rfl⟩
  · c0_steps; exact hQ _ s1 m1 hcore1 hlen1 hpres1 hm1

theorem full_m6_get_tier2_wp (Γ : Env)
    (hReady : ∀ a m Q X, m6ExtReadySpec a m Q X →
      Γ "full_m6_ext_ready" [i64] [.bool] a m Q X) :
    ∀ a m Q X, m6SafetyBoolU64Spec a m Q X →
      Func.wp Γ full_m6_get_tier2_body a m Q X := by
  rintro ⟨h, viv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  c0_hsteps_nogrp
  c0_call hReady
  refine ⟨c, s, R, rfl, hlen, hm,
    fun ⟨ok, ⟨⟩⟩ s1 m1 hcore1 hlen1 ⟨hpres1, hok_iff, _, _⟩ hm1 => ?_⟩
  dsimp only [fullSafetySlice] at hlen1 hm1
  clear hm hlen
  c0_hsteps_nogrp
  · have hcap1 := hok_iff.mp hc
    have hcap200 : 200 ≤ c.delayed_cap := by unfold fullM6DelMinCap at hcap1; exact hcap1
    have hdl1 := hlen1.scratch_ok.delayed_len_arr
    have h18 : 18 < s1.scratch.delayed.length := by omega
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun (st, ()) m2 => m2 = m1 ∧ (st = 0#64 ∨ st = 1#64))
      (fun _ (st, ()) m2 ⟨hm2, hst⟩ => ?_) ?_
    · subst m2
      have hidx : ((20 : BitVec 64) + st).toNat < s1.scratch.delayed.length := by
        rw [hdl1]; exact m6_tier_mode_lt hcap200 hst (Or.inr rfl)
      c0_hsteps <;> exact hQ _ s1 m1 hcore1 hlen1 hpres1 hm1
    · intro _ hJs; c0_steps
      · exact hJs (_, ()) m1 ⟨rfl, Or.inl rfl⟩
      · exact hJs (_, ()) m1 ⟨rfl, Or.inr rfl⟩
  · c0_steps; exact hQ _ s1 m1 hcore1 hlen1 hpres1 hm1

/-! ## 6. `delay[4]` Backoff (`4` fns) -/

theorem full_m6_delaying_wp (Γ : Env)
    (hReady : ∀ a m Q X, m6ExtReadySpec a m Q X →
      Γ "full_m6_ext_ready" [i64] [.bool] a m Q X) :
    ∀ a m Q X, m6DelayingSpec a m Q X → Func.wp Γ full_m6_delaying_body a m Q X := by
  rintro ⟨h, id, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  c0_hsteps_nogrp
  · exact hQ (false, ()) s m rfl hlen (FullM6ScratchPres.refl s) hm
  · c0_call hReady
    refine ⟨c, s, R, rfl, hlen, hm,
      fun ⟨ok, ⟨⟩⟩ s1 m1 hcore1 hlen1 ⟨hpres1, hok_iff, _, _⟩ hm1 => ?_⟩
    dsimp only [fullSafetySlice] at hlen1 hm1
    clear hm hlen
    c0_hsteps_nogrp
    · have hid4 : id.toNat < 4 := by c0_bound
      have hcap1 := hok_iff.mp hc
      have hcap200 : 200 ≤ c.delayed_cap := by unfold fullM6DelMinCap at hcap1; exact hcap1
      have hdl1 := hlen1.scratch_ok.delayed_len_arr
      have hidx : ((30 : BitVec 64) + id).toNat < s1.scratch.delayed.length := by
        rw [hdl1]; exact m6_delay_lt hcap200 hid4 (Or.inl rfl)
      c0_hsteps
      · refine hQ (true, ()) _ m ?_ ?_ ?_ hm
        · exact hcore1
        · exact hlen1.with_scratch { hlen1.scratch_ok with delayed_len_arr := by simp [hdl1] }
        · exact ⟨hpres1.1, fun k hk => by
            dsimp only
            rw [List.getElem?_set_ne (m6_delay_ge16 hid4 (Or.inl rfl) hk)]
            exact hpres1.2 k hk⟩
      · exact hQ (false, ()) s1 m1 hcore1 hlen1 hpres1 hm1
    · exact hQ (false, ()) s1 m1 hcore1 hlen1 hpres1 hm1

theorem full_m6_bump_delay_wp (Γ : Env)
    (hReady : ∀ a m Q X, m6ExtReadySpec a m Q X →
      Γ "full_m6_ext_ready" [i64] [.bool] a m Q X) :
    ∀ a m Q X, m6SafetyArgVoidSpec i64 a m Q X →
      Func.wp Γ full_m6_bump_delay_body a m Q X := by
  rintro ⟨h, id, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  c0_hsteps_nogrp
  · exact hQ () s m rfl hlen (FullM6ScratchPres.refl s) hm
  · c0_call hReady
    refine ⟨c, s, R, rfl, hlen, hm,
      fun ⟨ok, ⟨⟩⟩ s1 m1 hcore1 hlen1 ⟨hpres1, hok_iff, _, _⟩ hm1 => ?_⟩
    dsimp only [fullSafetySlice] at hlen1 hm1
    clear hm hlen
    c0_hsteps_nogrp
    · have hid4 : id.toNat < 4 := by c0_bound
      have hcap1 := hok_iff.mp hc
      have hcap200 : 200 ≤ c.delayed_cap := by unfold fullM6DelMinCap at hcap1; exact hcap1
      have hdl1 := hlen1.scratch_ok.delayed_len_arr
      have hicur : ((34 : BitVec 64) + id).toNat < s1.scratch.delayed.length := by
        rw [hdl1]; exact m6_delay_lt hcap200 hid4 (Or.inr rfl)
      have hicnt : ((30 : BitVec 64) + id).toNat < s1.scratch.delayed.length := by
        rw [hdl1]; exact m6_delay_lt hcap200 hid4 (Or.inl rfl)
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i32]) (fun _ m2 => m2 = m1) (fun _ (cur, ()) _ hm2 => ?_) ?_
      · subst hm2
        c0_hsteps_nogrp
        refine hQ () _ m ?_ ?_ ?_ hm
        · exact hcore1
        · exact hlen1.with_scratch { hlen1.scratch_ok with delayed_len_arr := by simp [hdl1] }
        · exact ⟨hpres1.1, fun k hk => by
            dsimp only
            rw [List.getElem?_set_ne (m6_delay_ge16 hid4 (Or.inl rfl) hk),
              List.getElem?_set_ne (m6_delay_ge16 hid4 (Or.inr rfl) hk)]
            exact hpres1.2 k hk⟩
      · intro _ hJc; c0_steps <;> exact hJc (_, ()) m1 rfl
    · exact hQ () s1 m1 hcore1 hlen1 hpres1 hm1

theorem full_m6_reduce_delay_wp (Γ : Env)
    (hReady : ∀ a m Q X, m6ExtReadySpec a m Q X →
      Γ "full_m6_ext_ready" [i64] [.bool] a m Q X) :
    ∀ a m Q X, m6SafetyArgVoidSpec i64 a m Q X →
      Func.wp Γ full_m6_reduce_delay_body a m Q X := by
  rintro ⟨h, id, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  c0_hsteps_nogrp
  · exact hQ () s m rfl hlen (FullM6ScratchPres.refl s) hm
  · c0_call hReady
    refine ⟨c, s, R, rfl, hlen, hm,
      fun ⟨ok, ⟨⟩⟩ s1 m1 hcore1 hlen1 ⟨hpres1, hok_iff, _, _⟩ hm1 => ?_⟩
    dsimp only [fullSafetySlice] at hlen1 hm1
    clear hm hlen
    c0_hsteps_nogrp
    · have hid4 : id.toNat < 4 := by c0_bound
      have hcap1 := hok_iff.mp hc
      have hcap200 : 200 ≤ c.delayed_cap := by unfold fullM6DelMinCap at hcap1; exact hcap1
      have hdl1 := hlen1.scratch_ok.delayed_len_arr
      have hicur : ((34 : BitVec 64) + id).toNat < s1.scratch.delayed.length := by
        rw [hdl1]; exact m6_delay_lt hcap200 hid4 (Or.inr rfl)
      have hicnt : ((30 : BitVec 64) + id).toNat < s1.scratch.delayed.length := by
        rw [hdl1]; exact m6_delay_lt hcap200 hid4 (Or.inl rfl)
      c0_hsteps_nogrp
      refine hQ () _ m ?_ ?_ ?_ hm
      · exact hcore1
      · exact hlen1.with_scratch { hlen1.scratch_ok with delayed_len_arr := by simp [hdl1] }
      · exact ⟨hpres1.1, fun k hk => by
          dsimp only
          rw [List.getElem?_set_ne (m6_delay_ge16 hid4 (Or.inl rfl) hk),
            List.getElem?_set_ne (m6_delay_ge16 hid4 (Or.inr rfl) hk)]
          exact hpres1.2 k hk⟩
    · exact hQ () s1 m1 hcore1 hlen1 hpres1 hm1

theorem full_m6_reset_delay_wp (Γ : Env)
    (hReady : ∀ a m Q X, m6ExtReadySpec a m Q X →
      Γ "full_m6_ext_ready" [i64] [.bool] a m Q X) :
    ∀ a m Q X, m6SafetyArgVoidSpec i64 a m Q X →
      Func.wp Γ full_m6_reset_delay_body a m Q X := by
  rintro ⟨h, id, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  c0_hsteps_nogrp
  · exact hQ () s m rfl hlen (FullM6ScratchPres.refl s) hm
  · c0_call hReady
    refine ⟨c, s, R, rfl, hlen, hm,
      fun ⟨ok, ⟨⟩⟩ s1 m1 hcore1 hlen1 ⟨hpres1, hok_iff, _, _⟩ hm1 => ?_⟩
    dsimp only [fullSafetySlice] at hlen1 hm1
    clear hm hlen
    c0_hsteps_nogrp
    · have hid4 : id.toNat < 4 := by c0_bound
      have hcap1 := hok_iff.mp hc
      have hcap200 : 200 ≤ c.delayed_cap := by unfold fullM6DelMinCap at hcap1; exact hcap1
      have hdl1 := hlen1.scratch_ok.delayed_len_arr
      have hicur : ((34 : BitVec 64) + id).toNat < s1.scratch.delayed.length := by
        rw [hdl1]; exact m6_delay_lt hcap200 hid4 (Or.inr rfl)
      have hicnt : ((30 : BitVec 64) + id).toNat < s1.scratch.delayed.length := by
        rw [hdl1]; exact m6_delay_lt hcap200 hid4 (Or.inl rfl)
      c0_hsteps_nogrp
      refine hQ () _ m ?_ ?_ ?_ hm
      · exact hcore1
      · exact hlen1.with_scratch { hlen1.scratch_ok with delayed_len_arr := by simp [hdl1] }
      · exact ⟨hpres1.1, fun k hk => by
          dsimp only
          rw [List.getElem?_set_ne (m6_delay_ge16 hid4 (Or.inl rfl) hk),
            List.getElem?_set_ne (m6_delay_ge16 hid4 (Or.inr rfl) hk)]
          exact hpres1.2 k hk⟩
    · exact hQ () s1 m1 hcore1 hlen1 hpres1 hm1

/-! ## 7. Watermarks, Tick Routing, `log10_q16_m6`, `scale_delta_m6` & `dticks` (`7` fns) -/

theorem full_m6_get_watermark_wp (Γ : Env)
    (hReady : ∀ a m Q X, m6ExtReadySpec a m Q X →
      Γ "full_m6_ext_ready" [i64] [.bool] a m Q X)
    (hGet64 : ∀ a m Q X, m6Get64Spec a m Q X → Γ "full_m6_get64" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6GetWmSpec a m Q X → Func.wp Γ full_m6_get_watermark_body a m Q X := by
  rintro ⟨h, kind, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  c0_hsteps_nogrp
  · exact hQ (0#64, ()) s m rfl hlen (FullM6ScratchPres.refl s) hm
  · c0_call hReady
    refine ⟨c, s, R, rfl, hlen, hm,
      fun ⟨ok, ⟨⟩⟩ s1 m1 hcore1 hlen1 ⟨hpres1, hok_iff, _, _⟩ hm1 => ?_⟩
    dsimp only [fullSafetySlice] at hlen1 hm1
    clear hm hlen
    c0_hsteps_nogrp
    · have hkind8 : kind.toNat < 8 := by c0_bound
      have hcap1 := hok_iff.mp hc
      have hcap200 : 200 ≤ c.delayed_cap := by unfold fullM6DelMinCap at hcap1; exact hcap1
      have hdl1 := hlen1.scratch_ok.delayed_len_arr
      have hidx : (38#64 + (kind <<< (1 : BitVec 64))).toNat + 1 < s1.scratch.delayed.length := by
        rw [hdl1]; exact m6_wm_lt hcap200 hkind8
      c0_call hGet64
      refine m6_get64_full_spec hlen1 hidx hm1 ?_
      exact hQ _ s1 m1 hcore1 hlen1 hpres1 hm1
    · exact hQ _ s1 m1 hcore1 hlen1 hpres1 hm1
    · exact hQ _ s1 m1 hcore1 hlen1 hpres1 hm1
    · exact hQ _ s1 m1 hcore1 hlen1 hpres1 hm1

theorem full_m6_set_watermark_wp (Γ : Env)
    (hReady : ∀ a m Q X, m6ExtReadySpec a m Q X →
      Γ "full_m6_ext_ready" [i64] [.bool] a m Q X)
    (hSet64 : ∀ a m Q X, m6Set64Spec a m Q X → Γ "full_m6_set64" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, m6SetWmSpec a m Q X → Func.wp Γ full_m6_set_watermark_body a m Q X := by
  rintro ⟨h, kind, val, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  c0_hsteps_nogrp
  · exact hQ () s m rfl hlen (FullM6ScratchPres.refl s) hm
  · c0_call hReady
    refine ⟨c, s, R, rfl, hlen, hm,
      fun ⟨ok, ⟨⟩⟩ s1 m1 hcore1 hlen1 ⟨hpres1, hok_iff, _, _⟩ hm1 => ?_⟩
    dsimp only [fullSafetySlice] at hlen1 hm1
    clear hm hlen
    c0_hsteps_nogrp
    · have hkind8 : kind.toNat < 8 := by c0_bound
      have hcap1 := hok_iff.mp hc
      have hcap200 : 200 ≤ c.delayed_cap := by unfold fullM6DelMinCap at hcap1; exact hcap1
      have hdl1 := hlen1.scratch_ok.delayed_len_arr
      have hidx : (38#64 + (kind <<< (1 : BitVec 64))).toNat + 1 < s1.scratch.delayed.length := by
        rw [hdl1]; exact m6_wm_lt hcap200 hkind8
      c0_call hSet64
      refine m6_set64_full_spec hlen1 hidx hm1 fun m2 hm2 => ?_
      let del2 := m6Set64List s1.scratch.delayed (38#64 + (kind <<< (1 : BitVec 64))).toNat val
      let s2 : FullState := { s1 with scratch := { s1.scratch with delayed := del2 } }
      have hlen2 : s2.LengthsOk c :=
        hlen1.with_scratch { hlen1.scratch_ok with
          delayed_len_arr := by simp [del2, m6Set64List_length, hdl1] }
      have h2w2b : FullM6DelayedW2bPres s1 s2 := fun k hk =>
        m6Set64List_get_lt _ _ _ (m6_wm_ge16 hkind8 hk)
      exact hQ () s2 m2 hcore1 hlen2 ⟨hpres1.1, hpres1.2.trans h2w2b⟩ hm2
    · c0_hsteps
      · refine hQ () _ m ?_ ?_ ?_ hm
        · exact hcore1
        · exact hlen1.with_scratch
            { hlen1.scratch_ok with walk_vals_len := hlen1.scratch_ok.walk_vals_len }
        · exact ⟨hpres1.1, hpres1.2⟩
      · refine hQ () _ m ?_ ?_ ?_ hm
        · exact hcore1
        · exact hlen1.with_scratch
            { hlen1.scratch_ok with walk_vals_len := hlen1.scratch_ok.walk_vals_len }
        · exact ⟨hpres1.1, hpres1.2⟩
      · exact hQ () s1 m1 hcore1 hlen1 hpres1 hm1

theorem full_m6_add_ticks_wp (Γ : Env)
    (hReady : ∀ a m Q X, m6ExtReadySpec a m Q X →
      Γ "full_m6_ext_ready" [i64] [.bool] a m Q X)
    (hGetWm : ∀ a m Q X, m6GetWmSpec a m Q X →
      Γ "full_m6_get_watermark" [i64, i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6SetWmSpec a m Q X →
      Γ "full_m6_set_watermark" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, m6SafetyArgVoidSpec i64 a m Q X →
      Func.wp Γ full_m6_add_ticks_body a m Q X := by
  rintro ⟨h, ticks, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  c0_hsteps_nogrp
  · refine wp_join_group (ts := []) (fun () m2 =>
        ∃ s2, PreservesCoreSlice FullState.core s s2 ∧ s2.LengthsOk c ∧
          FullM6ScratchPres s s2 ∧ (FullMem c s2 ⋆ R) m2)
      (fun _ () m2 ⟨s2, hc2, hl2, hp2, hm2⟩ => by c0_steps; exact hQ () s2 m2 hc2 hl2 hp2 hm2) ?_
    intro _ hJr
    c0_call hReady
    refine ⟨c, s, R, rfl, hlen, hm, fun ⟨ok, ⟨⟩⟩ s1 m1 hcore1 hlen1 ⟨hpres1, _⟩ hm1 => ?_⟩
    dsimp only [fullSafetySlice] at hlen1 hm1
    c0_hsteps_nogrp
    · c0_call hGetWm
      refine ⟨c, s1, R, rfl, hlen1, hm1, fun ⟨pt, ⟨⟩⟩ s2 m2 hcore2 hlen2 hpres2 hm2 => ?_⟩
      dsimp only [fullSafetySlice] at hlen2 hm2
      c0_call hSetWm
      refine ⟨c, s2, R, rfl, hlen2, hm2, fun () s3 m3 hcore3 hlen3 hpres3 hm3 => ?_⟩
      dsimp only [fullSafetySlice] at hlen3 hm3
      exact hJr () m3 ⟨s3, hcore1.trans (hcore2.trans hcore3), hlen3,
        hpres1.trans (hpres2.trans hpres3), hm3⟩
    · exact hJr () m1 ⟨s1, hcore1, hlen1, hpres1, hm1⟩
  · let s1 : FullState :=
      { s with scratch := { s.scratch with search_ticks := s.scratch.search_ticks + ticks } }
    have hlen1 : s1.LengthsOk c :=
      hlen.with_scratch { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }
    refine wp_join_group (ts := []) (fun () m3 =>
        ∃ s3, PreservesCoreSlice FullState.core s s3 ∧ s3.LengthsOk c ∧
          FullM6ScratchPres s s3 ∧ (FullMem c s3 ⋆ R) m3)
      (fun _ () m3 ⟨s3, hc3, hl3, hp3, hm3⟩ => by c0_steps; exact hQ () s3 m3 hc3 hl3 hp3 hm3) ?_
    intro _ hJr
    c0_call hReady
    refine ⟨c, s1, R, rfl, hlen1, hm, fun ⟨ok, ⟨⟩⟩ s2 m2 hcore2 hlen2 ⟨hpres2, _⟩ hm2 => ?_⟩
    dsimp only [fullSafetySlice] at hlen2 hm2
    c0_hsteps_nogrp
    · refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m2)
        (fun _ (_wk, ()) m3 hm3 => ?_) ?_
      · subst m3
        c0_call hGetWm
        refine ⟨c, s2, R, rfl, hlen2, hm2, fun ⟨cur, ⟨⟩⟩ s3 m3 hcore3 hlen3 hpres3 hm3 => ?_⟩
        dsimp only [fullSafetySlice] at hlen3 hm3
        c0_call hSetWm
        refine ⟨c, s3, R, rfl, hlen3, hm3, fun () s4 m4 hcore4 hlen4 hpres4 hm4 => ?_⟩
        dsimp only [fullSafetySlice] at hlen4 hm4
        exact hJr () m4 ⟨s4, hcore2.trans (hcore3.trans hcore4), hlen4,
          (FullM6ScratchPres.refl s).trans (hpres2.trans (hpres3.trans hpres4)), hm4⟩
      · intro _ hJmk; c0_steps
        · exact hJmk (7#64, ()) m2 rfl
        · exact hJmk (6#64, ()) m2 rfl
    · exact hJr () m2 ⟨s2, hcore2, hlen2, (FullM6ScratchPres.refl s).trans hpres2, hm2⟩

local macro "solve_log10_tail_m6" x:ident d:ident p:ident hp:ident hd10:ident m:ident hQ:ident :
    tactic => `(tactic| (
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64, i64])
    (fun (_, pm', ()) m2 => $m = m2 ∧ 1 ≤ pm'.toNat) ?_ ?_
  · rintro _ ⟨xm', pm', ⟨⟩⟩ m2 ⟨hm2, hpm⟩
    subst m2
    have hpm_ne : pm' ≠ 0#64 := by intro h0; subst h0; simp at hpm
    c0_hsteps_nogrp
    all_goals try exact hpm_ne
    refine wp_loop_inv (ts := [i64, i64, i64])
      (fun (_mv, frac, i, ()) m3 =>
        $m = m3 ∧ i.toNat ≤ 16 ∧ frac.toNat < 2 ^ i.toNat)
      (fun (_, _, i, ()) _ => 16 - i.toNat) ?_ ?_
    · intro J2 hJ2
      c0_hsteps; exact hJ2 (_, 0#64, 0#64, ()) $m ⟨Eq.refl _, by decide, by decide⟩
    · rintro J2 ⟨mv, frac, i, ⟨⟩⟩ m3 ⟨hm3, hi16, hfl⟩ hJ2
      subst m3
      c0_hsteps
      · have hi_lt : i.toNat < 16 := by c0_bound
        have hf_lt : frac.toNat < 2 ^ 15 :=
          Nat.lt_of_lt_of_le hfl (Nat.pow_le_pow_right (by omega) (by omega))
        have hf_sh : (frac <<< (1 : Nat)).toNat = 2 * frac.toNat := by
          rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
        have hf2_lt : 2 * frac.toNat < 2 ^ (i.toNat + 1) := by rw [Nat.pow_succ]; omega
        have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
        have h16pow : 2 ^ (i.toNat + 1) ≤ 2 ^ 16 :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hf2p1 : (frac <<< (1 : Nat) + 1#64).toNat = 2 * frac.toNat + 1 := by bv_omega
        have hf2p1_lt : 2 * frac.toNat + 1 < 2 ^ (i.toNat + 1) := by rw [Nat.pow_succ]; omega
        exact hJ2 (_, (frac <<< (1 : Nat)) + 1#64, i + 1#64, ()) $m
          (by dsimp only; omega) ⟨Eq.refl _, by omega, by rw [hi1, hf2p1]; exact hf2p1_lt⟩
      · have hi_lt : i.toNat < 16 := by c0_bound
        have hf_lt : frac.toNat < 2 ^ 15 :=
          Nat.lt_of_lt_of_le hfl (Nat.pow_le_pow_right (by omega) (by omega))
        have hf_sh : (frac <<< (1 : Nat)).toNat = 2 * frac.toNat := by
          rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
        have hf2_lt : 2 * frac.toNat < 2 ^ (i.toNat + 1) := by rw [Nat.pow_succ]; omega
        have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
        exact hJ2 (_, frac <<< (1 : Nat), i + 1#64, ()) $m
          (by dsimp only; omega) ⟨Eq.refl _, by omega, by rw [hi1, hf_sh]; exact hf2_lt⟩
      · have hflt : frac.toNat < 65536 :=
          Nat.lt_of_lt_of_le hfl (Nat.pow_le_pow_right (by omega) hi16)
        have hd_sh : (($d) <<< (16 : Nat)).toNat = ($d).toNat * 65536 := by
          rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
        have hres_lt : ((($d) <<< (16 : Nat)) + frac).toNat < 20 * 65536 := by
          have hsum : ($d).toNat * 65536 + frac.toNat < 20 * 65536 := by omega
          have h64 : ($d).toNat * 65536 + frac.toNat < 2 ^ 64 := by omega
          rw [BitVec.toNat_add, hd_sh, Nat.mod_eq_of_lt h64]; exact hsum
        have hres_ge : 10 ≤ ($x).toNat →
            65536 ≤ ((($d) <<< (16 : Nat)) + frac).toNat := by
          intro hx10; have hd1 := $hd10 hx10
          have hsum : 65536 ≤ ($d).toNat * 65536 + frac.toNat := by omega
          have h64 : ($d).toNat * 65536 + frac.toNat < 2 ^ 64 := by omega
          rw [BitVec.toNat_add, hd_sh, Nat.mod_eq_of_lt h64]; exact hsum
        exact $hQ ((($d) <<< (16 : Nat)) + frac) hres_lt hres_ge
  · intro _ hJm
    c0_hsteps_nogrp
    · have hpm_gt : 100000000 < ($p).toNat := by c0_bound
      intro h0; have ht := congrArg BitVec.toNat h0
      change ($p).toNat / 100000000 = 0 at ht
      have hpos : 0 < ($p).toNat / 100000000 :=
        Nat.div_pos (Nat.le_of_lt hpm_gt) (by decide)
      omega
    · exact hJm ($x / ($p / 100000000#64), 100000000#64, ()) $m ⟨Eq.refl _, by decide⟩
    · exact hJm ($x, $p, ()) $m ⟨Eq.refl _, $hp⟩))

theorem full_log10_q16_m6_wp (Γ : Env) :
    ∀ a m Q X, m6Log10Q16Spec a m Q X → Func.wp Γ full_log10_q16_m6_body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  c0_hsteps_nogrp
  · have hx1 : x.toNat ≤ 1 := by c0_bound
    exact hQ 0#64 (by decide) (fun hx10 => by omega)
  · refine wp_loop_inv (ts := [i64, i64])
      (fun (d, pow10, ()) m1 =>
        m = m1 ∧ d.toNat ≤ 19 ∧ 1 ≤ pow10.toNat ∧ pow10.toNat ≤ 10 ^ d.toNat ∧
        (d.toNat = 0 → pow10.toNat = 1))
      (fun (d, _, ()) _ => 19 - d.toNat) ?_ ?_
    · intro J hJ
      c0_hsteps; exact hJ (0#64, 1#64, ()) m ⟨rfl, by decide, by decide, by decide, fun _ => rfl⟩
    · rintro J ⟨d, pow10, ⟨⟩⟩ _ ⟨rfl, hd19, hp1, hple, hd0p⟩ hJ
      refine wp_join_group (ts := []) (fun _ m1 => m = m1 ∧ (10 ≤ x.toNat → 1 ≤ d.toNat))
        ?_ ?_
      · rintro _ ⟨⟩ _ ⟨rfl, hd10⟩
        solve_log10_tail_m6 x d pow10 hp1 hd10 m hQ
      · intro _ hJexit
        c0_hsteps_nogrp
        · have hd_lt : d.toNat < 19 := by c0_bound
          have hpow_10 : pow10.toNat * 10 ≤ 10 ^ (d.toNat + 1) := by
            rw [Nat.pow_succ]; exact Nat.mul_le_mul_right 10 hple
          have hpow_lt64 : pow10.toNat * 10 < 2 ^ 64 :=
            Nat.lt_of_le_of_lt hpow_10 (pow10_lt_64_m6 (by omega))
          have hd1 : (d + 1#64).toNat = d.toNat + 1 := by bv_omega
          have hp10' : (pow10 * 10#64).toNat = pow10.toNat * 10 := by
            rw [BitVec.toNat_mul, show (10#64).toNat = 10 from rfl,
              Nat.mod_eq_of_lt hpow_lt64]
          exact hJ (d + 1#64, pow10 * 10#64, ()) m (by dsimp only; omega)
            ⟨rfl, by omega, by omega, by rw [hd1, hp10']; exact hpow_10,
             fun h0 => by rw [hd1] at h0; omega⟩
        · have hge : 19 ≤ d.toNat := by c0_bound
          exact hJexit () m ⟨rfl, fun _ => by omega⟩
        · have hlt : x.toNat / 10 < pow10.toNat := by
            have hdiv : (x / 10#64).toNat < pow10.toNat := by c0_bound
            have hmod : (x / 10#64).toNat = x.toNat / 10 := by bv_omega
            omega
          refine hJexit () m ⟨rfl, fun hx10 => ?_⟩
          rcases Nat.eq_zero_or_pos d.toNat with hd0 | hdpos
          · have hp1' := hd0p hd0; omega
          · exact hdpos

theorem full_scale_delta_m6_wp (Γ : Env)
    (hLog : ∀ a m Q X, m6Log10Q16Spec a m Q X → Γ "full_log10_q16_m6" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6ScaleDeltaSpec a m Q X → Func.wp Γ full_scale_delta_m6_body a m Q X := by
  rintro ⟨h, delta, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  c0_hsteps_nogrp
  c0_call hLog; intro q _ _
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun _ m2 => m2 = m) (fun _ (l, ()) m2 hm2 => ?_) ?_
  · subst m2
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m) (fun _ (dl, ()) m3 hm3 => ?_) ?_
    · subst m3; c0_steps; exact hQ _ s m rfl hlen rfl hm
    · intro _ hJdl; c0_steps <;> exact hJdl (_, ()) m rfl
  · intro _ hJl; c0_steps <;> exact hJl (_, ()) m rfl

theorem full_probe_dticks_m6_wp (Γ : Env)
    (hGetWm : ∀ a m Q X, m6GetWmSpec a m Q X →
      Γ "full_m6_get_watermark" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6DticksSpec a m Q X → Func.wp Γ full_probe_dticks_m6_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  c0_hsteps_nogrp
  c0_call hGetWm
  refine ⟨c, s, R, rfl, hlen, hm, fun ⟨last_p, ⟨⟩⟩ s1 m1 hcore1 hlen1 hpres1 hm1 => ?_⟩
  dsimp only [fullSafetySlice] at hlen1 hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun _ m2 => m2 = m1)
    (fun _ (raw, ()) m2 hm2 => ?_) ?_
  · subst m2
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m1)
      (fun _ (dt, ()) m3 hm3 => ?_) ?_
    · subst m3
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun _ m4 => m4 = m1)
        (fun _ (res, ()) m4 hm4 => by
          subst m4; exact hQ (res, ()) s1 m1 hcore1 hlen1 hpres1 hm1)
        (fun _ hJr => by c0_steps <;> exact hJr (_, ()) m1 rfl)
    · intro _ hJd; c0_hsteps <;> exact hJd (_, ()) m1 rfl
  · intro _ hJr; c0_hsteps <;> exact hJr (_, ()) m1 rfl

theorem full_elim_dticks_m6_wp (Γ : Env)
    (hGetWm : ∀ a m Q X, m6GetWmSpec a m Q X →
      Γ "full_m6_get_watermark" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6DticksSpec a m Q X → Func.wp Γ full_elim_dticks_m6_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen hQ
  c0_hsteps_nogrp
  · c0_steps; exact hQ _ s m rfl hlen (FullM6ScratchPres.refl s) hm
  · c0_call hGetWm
    refine ⟨c, s, R, rfl, hlen, hm, fun ⟨last_e, ⟨⟩⟩ s1 m1 hcore1 hlen1 hpres1 hm1 => ?_⟩
    dsimp only [fullSafetySlice] at hlen1 hm1
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m2 => m2 = m1)
      (fun _ (dt, ()) m2 hm2 => by
        subst m2; c0_steps; exact hQ (dt, ()) s1 m1 hcore1 hlen1 hpres1 hm1)
      (fun _ hJd => by c0_hsteps <;> exact hJd (_, ()) m1 rfl)

end M6Proof0Tactics

end LeanQbe.T.Examples.Kissat.FullM6Tiers
