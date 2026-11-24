/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8WaveACore
public import LeanQbe.T.Examples.Kissat.PatchModule
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof1
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3b
public import LeanQbe.T.Examples.Kissat.FullM7SearchProof0
public import LeanQbe.T.Examples.Kissat.FullM3BackboneLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M8 `FullM8WaveACore` Proofs (`FullM8WaveACoreProof`)

M1-clean UNSAT-only proofs (`public section`, `0` `@[expose]`, `0` `import all`, `0` SAT proofs):
1. Pure Q16 `log2` spec (`m8Log2Q16Spec`) and `FullM6HdrMem`-lifted inprocessing contracts
   (`m8VivifyTierSpec` recording `e[118]` and `m8EliminateSpec` tracking `e[119]` / `e[128]`).
2. Parametric `(Γ : Env)` `Func.wp` proofs for all `11` functions of `waveACoreFns`.
3. Closed `33`-row `waveACoreSpecTable`, `waveACoreEnv`, `waveACoreEnv_noExit`,
   `waveACore_tableImpl`, `waveACore_moduleOk`, and `PatchModule` splicing bridges
   (`waveACorePatchRows`, `waveACorePatchBeforeRows`, `waveACorePatch_tableImpl`,
   `waveACorePatch_tableImpl_of`).
4. Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT proofs) covering AE-bump
   Q16 Padé `tanh` + `>= 2^56` rescale paths, `64`-bin glue histogram, M8 delay slots
   (`id = 4, 6`), `full_vivify_m6_hdr`, `full_eliminate_m6`, and `full_probe_tail_m6`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8WaveACore

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM3Backbone
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.PatchModule
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics

local macro "wac_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Wave A Core Specifications (`m8Log2Q16Spec`, `m8VivifyTierSpec`, `m8EliminateSpec`) -/

section Specs

/-- Pure Q16 `log2` specification for `m8_log2_q16`: returns `0` for `x ≤ 1` and
`(b <<< 16) + frac ∈ [b * 65536, (b + 1) * 65536)` for `2 ≤ x` with `2^b ≤ x < 2^(b+1)`. -/
def m8Log2Q16Spec : Spec [i64] [i64] := fun (x, ()) m Q _ =>
  ∀ r : BitVec 64,
    (x.toNat ≤ 1 → r = 0#64) →
    (2 ≤ x.toNat →
      ∃ b : Nat, 1 ≤ b ∧ b < 64 ∧ 2 ^ b ≤ x.toNat ∧ x.toNat < 2 ^ (b + 1) ∧
      b * 65536 ≤ r.toNat ∧ r.toNat < (b + 1) * 65536 ∧ r.toNat < 2 ^ 22) →
    Q (r, ()) m

theorem m8Log2Q16Spec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : m8Log2Q16Spec xs m Q X) : m8Log2Q16Spec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

/-- `FullM6HdrMem`-lifted `full_vivify_tier_m6_hdr` specification tracking `e[M8W_VIV_LAST_TRIED]`
at word `118` inside `M6HdrExt` while preserving `M6HdrExtOk` and `M6ExtW2bPres`. -/
def m8VivifyTierSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (h, _tier_mode, budget, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInv c F0 s ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        M6HdrExtOk ext' →
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        FullSparseInv c F0 s' →
        (s.core.cur_level = 0 → s'.core.cur_level = 0) →
        (s.core.probing = 0#64 → s'.core.probing = 0#64) →
        (budget ≠ 0#64 → s'.core.cur_level = 0 ∧ s'.core.probing = 0#64) →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem m8VivifyTierSpec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {tm bud tl : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hsp : FullSparseInv c F0 s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' s' m',
      M6HdrExtOk ext' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullSparseInv c F0 s' →
      (s.core.cur_level = 0 → s'.core.cur_level = 0) →
      (s.core.probing = 0#64 → s'.core.probing = 0#64) →
      (bud ≠ 0#64 → s'.core.cur_level = 0 ∧ s'.core.probing = 0#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    m8VivifyTierSpec (c.hdr, tm, bud, tl, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hcfg, hext, hsp, hm, hQ⟩

theorem m8VivifyTierSpec_elim {h tm bud tl : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : m8VivifyTierSpec (h, tm, bud, tl, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInv c F0 s ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        M6HdrExtOk ext' →
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        FullSparseInv c F0 s' →
        (s.core.cur_level = 0 → s'.core.cur_level = 0) →
        (s.core.probing = 0#64 → s'.core.probing = 0#64) →
        (bud ≠ 0#64 → s'.core.cur_level = 0 ∧ s'.core.probing = 0#64) →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' := hs

theorem m8VivifyTierSpec_monoX {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : m8VivifyTierSpec xs m Q X) :
    m8VivifyTierSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, ⟨⟩⟩; exact h

/-- `FullM6HdrMem`-lifted `full_eliminate_m6` specification tracking `M8W_BVE_STALL` (`128`) and
`M8W_BVE_THROTTLED` (`119`) inside `M6HdrExt` on `!initial && res != 20ULL`. -/
def m8EliminateSpec : Spec [i64, .bool] [i64] :=
  fun (h, _initial, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInv c F0 s ∧
      s.core.cur_level = 0 ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        M6HdrExtOk ext' →
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        FullSparseInv c F0 s' → s'.core.cur_level = 0 →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem m8EliminateSpec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {initial : Bool} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hsp : FullSparseInv c F0 s)
    (hcl0 : s.core.cur_level = 0) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' s' m',
      M6HdrExtOk ext' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    m8EliminateSpec (c.hdr, initial, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hcfg, hext, hsp, hcl0, hm, hQ⟩

theorem m8EliminateSpec_elim {h : BitVec 64} {initial : Bool} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : m8EliminateSpec (h, initial, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInv c F0 s ∧
      s.core.cur_level = 0 ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        M6HdrExtOk ext' →
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        FullSparseInv c F0 s' → s'.core.cur_level = 0 →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' := hs

theorem m8EliminateSpec_monoX {xs : Tup Val [i64, .bool]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : m8EliminateSpec xs m Q X) :
    m8EliminateSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

end Specs

/-! ## 2. Private Arithmetic, `BitVec`, & Invariant Helpers -/

section Helpers

private theorem bv64_add_small {k x : BitVec 64} {n : Nat} (hk : k.toNat = n)
    (hsum : n + x.toNat < 2 ^ 64) : (k + x).toNat = n + x.toNat := by
  rw [BitVec.toNat_add, hk, Nat.mod_eq_of_lt hsum]

private theorem bv64_add_toNat_small {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

private theorem bv64_add1_toNat {g : BitVec 64} (h : g.toNat + 1 < 2 ^ 64) :
    (g + 1).toNat = g.toNat + 1 := by
  rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem w2a_pres_of_init {ext ext1 ext' : List (BitVec 64)}
    (h1 : M6HdrExtInitOk ext → ext1 = ext) (h2 : M6HdrExtInitOk ext')
    (h3 : M6ExtW2bPres ext1 ext') :
    M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext' :=
  fun hi => ⟨h2, (h1 hi) ▸ h3⟩

private theorem ext_pres_compose {ext ext1 ext2 : List (BitVec 64)}
    (h1 : M6HdrExtInitOk ext → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext ext1)
    (h2 : M6HdrExtInitOk ext1 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext1 ext2) :
    M6HdrExtInitOk ext → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext ext2 := fun hi =>
  ⟨(h2 (h1 hi).1).1, (h1 hi).2.trans (h2 (h1 hi).1).2⟩

private theorem ext_pres_set_ge8 {ext ext1 : List (BitVec 64)} {idx : Nat} (v : BitVec 64)
    (h8 : 8 ≤ idx)
    (h1 : M6HdrExtInitOk ext → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext ext1) :
    M6HdrExtInitOk ext → M6HdrExtInitOk (ext1.set idx v) ∧ M6ExtW2bPres ext (ext1.set idx v) :=
  fun hi => ⟨(h1 hi).1.set_pos v (by omega), (h1 hi).2.trans (M6ExtW2bPres.set_ge8 v h8)⟩

private theorem fullSparseInv_of_core_eq_wac {c : FullCfg} {F0 : CNF Nat}
    {s s' : FullState} (h : FullSparseInv c F0 s)
    (hlen' : s'.LengthsOk c) (hcore : s'.core = s.core)
    (hpres : M6HdrScratchPres s s') : FullSparseInv c F0 s' := by
  obtain ⟨hcore_inv, hmc, hvn, hsc, hdm⟩ := h
  refine ⟨⟨hlen', ?_⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨F_cur, hw⟩ := hcore_inv.2
    exact ⟨F_cur, by rw [hcore]; exact hw⟩
  · unfold FullLitMarksClear FullMrkZero; rw [hcore]; exact hmc
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [hcore]; exact hvn
  · exact FullExtScratchOk.of_pres hsc hpres.extPres fun r hr => by
      unfold fullArenaClauseRefs; rwa [hcore]
  · rw [hcore]; exact hdm

private theorem fullSparseInv_with_ticks_wac {c : FullCfg} {F0 : CNF Nat}
    {s : FullState} (h : FullSparseInv c F0 s) (st : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with search_ticks := st } } :=
  fullSparseInv_of_core_eq_wac h (h.1.lengths.with_scratch { h.1.lengths.scratch_ok with }) rfl
    (M6HdrScratchPres.of_ticks st)

private theorem fullState_with_scinc_len {c : FullCfg} {s : FullState}
    (h : s.LengthsOk c) (v : BitVec 64) :
    ({ s with scratch := { s.scratch with scinc := v } } : FullState).LengthsOk c :=
  h.with_scratch { h.scratch_ok with }

private theorem fullState_with_scinc_pres {s : FullState} (v : BitVec 64) :
    FullProbeScratchPres s { s with scratch := { s.scratch with scinc := v } } :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem log2_step_true {x v bit : BitVec 64} {W max_b : Nat}
    (hW : W < 64) (hmw : max_b + W < 64) (hb : bit.toNat ≤ max_b)
    (hv : v = x >>> bit.toNat) (hhi : x.toNat < 2 ^ (bit.toNat + 2 * W))
    (hle : 1 <<< W % 2 ^ 64 ≤ v.toNat) :
    (bit + BitVec.ofNat 64 W).toNat ≤ max_b + W ∧
    v >>> W = x >>> (bit + BitVec.ofNat 64 W).toNat ∧
    2 ^ (bit + BitVec.ofNat 64 W).toNat ≤ x.toNat ∧
    x.toNat < 2 ^ ((bit + BitVec.ofNat 64 W).toNat + W) := by
  have h2W : 1 <<< W % 2 ^ 64 = 2 ^ W := by
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hW)]
  have hpow : 0 < 2 ^ bit.toNat := Nat.pow_pos (by decide)
  have hvnat : v.toNat = x.toNat / 2 ^ bit.toNat := by
    rw [hv, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hvge : 2 ^ W ≤ x.toNat / 2 ^ bit.toNat := by rw [← hvnat, ← h2W]; exact hle
  have hbit' : (bit + BitVec.ofNat 64 W).toNat = bit.toNat + W := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_trans hW (by decide)), Nat.mod_eq_of_lt (by omega)]
  refine ⟨by rw [hbit']; omega, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hvnat,
      Nat.div_div_eq_div_mul, ← Nat.pow_add, ← hbit', BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
  · rw [hbit', Nat.pow_add, Nat.mul_comm]
    exact (Nat.le_div_iff_mul_le hpow).mp hvge
  · rw [hbit', show bit.toNat + W + W = bit.toNat + 2 * W by omega]; exact hhi

private theorem log2_step_false {x v bit : BitVec 64} {W max_b : Nat}
    (hW : W < 64) (hb : bit.toNat ≤ max_b) (hv : v = x >>> bit.toNat)
    (hlo : 2 ^ bit.toNat ≤ x.toNat) (hlt : v.toNat < 2 ^ W) :
    bit.toNat ≤ max_b + W ∧ v = x >>> bit.toNat ∧ 2 ^ bit.toNat ≤ x.toNat ∧
    x.toNat < 2 ^ (bit.toNat + W) := by
  have hpow : 0 < 2 ^ bit.toNat := Nat.pow_pos (by decide)
  have hvnat : v.toNat = x.toNat / 2 ^ bit.toNat := by
    rw [hv, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hvlt : x.toNat / 2 ^ bit.toNat < 2 ^ W := by rw [← hvnat]; exact hlt
  refine ⟨by omega, hv, hlo, ?_⟩
  rw [Nat.pow_add, Nat.mul_comm]
  exact (Nat.div_lt_iff_lt_mul hpow).mp hvlt

private theorem ae_decay_lt_bounds {rq : BitVec 64} (h : rq.toNat < 32768) :
    60000 ≤ (62259#64 - ((1966#64 * (32768#64 - rq)) >>> 16)).toNat ∧
    (62259#64 - ((1966#64 * (32768#64 - rq)) >>> 16)).toNat ≤ 70000 := by
  have hd : (32768#64 - rq).toNat = 32768 - rq.toNat := by bv_omega
  have hm_le : 1966 * (32768 - rq.toNat) ≤ 1966 * 32768 := Nat.mul_le_mul_left _ (by omega)
  have hm : (1966#64 * (32768#64 - rq)).toNat = 1966 * (32768 - rq.toNat) := by
    rw [BitVec.toNat_mul, hd, show (1966#64 : BitVec 64).toNat = 1966 from rfl,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hm_le (by decide))]
  have hs : ((1966#64 * (32768#64 - rq)) >>> 16).toNat ≤ 983 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hm]
    omega
  have hle : ((1966#64 * (32768#64 - rq)) >>> 16) ≤ 62259#64 :=
    BitVec.le_def.mpr (by rw [show (62259#64 : BitVec 64).toNat = 62259 from rfl]; omega)
  rw [BitVec.toNat_sub_of_le hle, show (62259#64 : BitVec 64).toNat = 62259 from rfl]
  omega

private theorem ae_decay_ge_denom {rq : BitVec 64}
    (hlo : 32768 ≤ rq.toNat) (hhi : rq.toNat ≤ 65536) :
    let u := (rq - 32768#64) <<< 1
    let u2 := (u * u) >>> 16
    let denom := 27#64 * 65536#64 + 9#64 * u2
    u.toNat ≤ 65536 ∧ u2.toNat ≤ 65536 ∧
    1769472 ≤ denom.toNat ∧ denom.toNat ≤ 2359296 := by
  have hu : ((rq - 32768#64) <<< 1).toNat ≤ 65536 := by bv_omega
  have huu_le : ((rq - 32768#64) <<< 1).toNat * ((rq - 32768#64) <<< 1).toNat ≤
      65536 * 65536 := Nat.mul_le_mul hu hu
  have huu : (((rq - 32768#64) <<< 1) * ((rq - 32768#64) <<< 1)).toNat =
      ((rq - 32768#64) <<< 1).toNat * ((rq - 32768#64) <<< 1).toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt huu_le (by decide))]
  have hu2 : ((((rq - 32768#64) <<< 1) * ((rq - 32768#64) <<< 1)) >>> 16).toNat ≤ 65536 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, huu]
    exact Nat.div_le_of_le_mul (Nat.le_trans huu_le (by decide))
  have h9_le : 9 * ((((rq - 32768#64) <<< 1) * ((rq - 32768#64) <<< 1)) >>> 16).toNat ≤
      9 * 65536 := Nat.mul_le_mul_left _ hu2
  have h9 : (9#64 *
      ((((rq - 32768#64) <<< 1) * ((rq - 32768#64) <<< 1)) >>> 16)).toNat =
      9 * ((((rq - 32768#64) <<< 1) * ((rq - 32768#64) <<< 1)) >>> 16).toNat := by
    rw [BitVec.toNat_mul, show (9#64 : BitVec 64).toNat = 9 from rfl,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h9_le (by decide))]
  have hden : (27#64 * 65536#64 +
      9#64 * ((((rq - 32768#64) <<< 1) * ((rq - 32768#64) <<< 1)) >>> 16)).toNat =
      1769472 + 9 * ((((rq - 32768#64) <<< 1) * ((rq - 32768#64) <<< 1)) >>> 16).toNat := by
    rw [BitVec.toNat_add, show (27#64 * 65536#64 : BitVec 64).toNat = 1769472 from rfl, h9,
      Nat.mod_eq_of_lt (by omega)]
  exact ⟨hu, hu2, by omega, by omega⟩

private theorem ae_decay_ge_bounds {rq : BitVec 64}
    (hlo : 32768 ≤ rq.toNat) (hhi : rq.toNat ≤ 65536) :
    let u := (rq - 32768#64) <<< 1
    let u2 := (u * u) >>> 16
    let denom := 27#64 * 65536#64 + 9#64 * u2
    let th := (u * (27#64 * 65536#64 + u2)) / denom
    60000 ≤ (62259#64 + ((2621#64 * th) >>> 16)).toNat ∧
    (62259#64 + ((2621#64 * th) >>> 16)).toNat ≤ 70000 := by
  intro u u2 denom th
  obtain ⟨hu, hu2, hden_lo, hden_hi⟩ := ae_decay_ge_denom hlo hhi
  have hu2' : u2.toNat ≤ 65536 := hu2
  have hden_lo' : 1769472 ≤ denom.toNat := hden_lo
  have hden_hi' : denom.toNat ≤ 2359296 := hden_hi
  have h1 : (27#64 * 65536#64 + u2).toNat = 1769472 + u2.toNat := by
    rw [BitVec.toNat_add, show (27#64 * 65536#64 : BitVec 64).toNat = 1769472 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have h9_le : 9 * u2.toNat ≤ 9 * 65536 := Nat.mul_le_mul_left _ hu2'
  have h9 : (9#64 * u2).toNat = 9 * u2.toNat := by
    rw [BitVec.toNat_mul, show (9#64 : BitVec 64).toNat = 9 from rfl,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h9_le (by decide))]
  have hden_eq : denom.toNat = 1769472 + 9 * u2.toNat := by
    rw [BitVec.toNat_add, show (27#64 * 65536#64 : BitVec 64).toNat = 1769472 from rfl,
      h9, Nat.mod_eq_of_lt (by omega)]
  have hle_den : 1769472 + u2.toNat ≤ denom.toNat := by omega
  have hnum_le_mul : u.toNat * (1769472 + u2.toNat) ≤ 65536 * denom.toNat :=
    Nat.mul_le_mul hu hle_den
  have hnum_lt : u.toNat * (1769472 + u2.toNat) < 2 ^ 64 := by
    have hmul_hi : 65536 * denom.toNat ≤ 65536 * 2359296 := Nat.mul_le_mul_left _ hden_hi'
    exact Nat.lt_of_le_of_lt (Nat.le_trans hnum_le_mul hmul_hi) (by decide)
  have hnum_eq : (u * (27#64 * 65536#64 + u2)).toNat = u.toNat * (1769472 + u2.toNat) := by
    rw [BitVec.toNat_mul, h1, Nat.mod_eq_of_lt hnum_lt]
  have hth : th.toNat ≤ 65536 := by
    dsimp only [th]
    rw [BitVec.toNat_udiv, hnum_eq]
    exact Nat.div_le_of_le_mul (Nat.le_trans hnum_le_mul (Nat.le_of_eq (Nat.mul_comm _ _)))
  have hm2621_le : 2621 * th.toNat ≤ 2621 * 65536 := Nat.mul_le_mul_left _ hth
  have hm2621 : (2621#64 * th).toNat = 2621 * th.toNat := by
    rw [BitVec.toNat_mul, show (2621#64 : BitVec 64).toNat = 2621 from rfl,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hm2621_le (by decide))]
  have hsh : ((2621#64 * th) >>> 16).toNat ≤ 2621 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hm2621]
    exact Nat.div_le_of_le_mul (Nat.le_trans hm2621_le (by decide))
  rw [BitVec.toNat_add, show (62259#64 : BitVec 64).toNat = 62259 from rfl,
    Nat.mod_eq_of_lt (by omega)]
  omega

end Helpers

/-! ## 3. AE-Kissat-Bump Proofs (`m8_log2_q16`, `full_bump_decay`) -/

section AeBumpProofs

/-- Parametric pure arithmetic `Func.wp` proof for `m8_log2_q16_body`. -/
theorem m8_log2_q16_wp (Γ : Env) :
    ∀ a m Q X, m8Log2Q16Spec a m Q X → Func.wp Γ m8_log2_q16_body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  unfold Func.wp m8_log2_q16_body
  c0_hsteps_nogrp
  · exact hQ 0#64 (fun _ => rfl) (fun h => absurd (by c0_bound : x.toNat ≤ 1) (by omega))
  · have hx2 : 2 ≤ x.toNat := by c0_bound
    let StepInv (max_b width : Nat) : Tup Val [i64, i64] → Mem 64 → Prop :=
      fun (bit, v, ()) m1 => m1 = m ∧ bit.toNat ≤ max_b ∧ v = x >>> bit.toNat ∧
        2 ^ bit.toNat ≤ x.toNat ∧ x.toNat < 2 ^ (bit.toNat + width)
    refine wp_join_group (ts := [i64, i64]) (StepInv 32 32) ?_ ?_
    · rintro _ ⟨bit1, v1, ⟨⟩⟩ m1 ⟨hm1, hb1, hv1, hlo1, hhi1⟩
      subst m1
      refine wp_join_group (ts := [i64, i64]) (StepInv 48 16) ?_ ?_
      · rintro _ ⟨bit2, v2, ⟨⟩⟩ m2 ⟨hm2, hb2, hv2, hlo2, hhi2⟩
        subst m2
        refine wp_join_group (ts := [i64, i64]) (StepInv 56 8) ?_ ?_
        · rintro _ ⟨bit3, v3, ⟨⟩⟩ m3 ⟨hm3, hb3, hv3, hlo3, hhi3⟩
          subst m3
          refine wp_join_group (ts := [i64, i64]) (StepInv 60 4) ?_ ?_
          · rintro _ ⟨bit4, v4, ⟨⟩⟩ m4 ⟨hm4, hb4, hv4, hlo4, hhi4⟩
            subst m4
            refine wp_join_group (ts := [i64, i64]) (StepInv 62 2) ?_ ?_
            · rintro _ ⟨bit5, v5, ⟨⟩⟩ m5 ⟨hm5, hb5, hv5, hlo5, hhi5⟩
              subst m5
              refine wp_join_group (ts := [i64])
                (fun (bit6, ()) m6 => m6 = m ∧ 1 ≤ bit6.toNat ∧ bit6.toNat < 64 ∧
                  2 ^ bit6.toNat ≤ x.toNat ∧ x.toNat < 2 ^ (bit6.toNat + 1)) ?_ ?_
              · rintro _ ⟨bit6, ⟨⟩⟩ m6 ⟨hm6, hlo6, hhi6_b, hlo6x, hhi6x⟩
                subst m6
                refine wp_join_group (ts := [i64])
                  (fun (frac, ()) mf => mf = m ∧ frac.toNat < 65536) ?_ ?_
                · rintro _ ⟨frac, ⟨⟩⟩ mf ⟨hmf, hfrac⟩
                  subst mf
                  c0_hsteps
                  have hres_nat : ((bit6 <<< (16 : Nat)) + frac).toNat =
                      bit6.toNat * 65536 + frac.toNat := by
                    have hsh : (bit6 <<< (16 : Nat)).toNat = bit6.toNat * 65536 := by
                      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
                        Nat.mod_eq_of_lt (by omega)]
                    rw [BitVec.toNat_add, hsh, Nat.mod_eq_of_lt (by omega)]
                  refine hQ _ (fun h => absurd h (by omega))
                    (fun _ => ⟨bit6.toNat, hlo6, hhi6_b, hlo6x, hhi6x,
                      by simp [hres_nat],
                      by simpa [hres_nat] using (by omega : bit6.toNat * 65536 + frac.toNat <
                        (bit6.toNat + 1) * 65536),
                      by simpa [hres_nat] using (by omega : bit6.toNat * 65536 + frac.toNat <
                        2 ^ 22)⟩)
                · intro Jf hJf
                  have h_and : ∀ w : BitVec 64, (w &&& 65535#64).toNat < 65536 := fun w => by
                    rw [BitVec.toNat_and, show (65535#64 : BitVec 64).toNat = 65535 from rfl]
                    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                  c0_hsteps
                  · exact hJf (_, ()) m ⟨rfl, h_and _⟩
                  · exact hJf (_, ()) m ⟨rfl, h_and _⟩
              · intro J6 hJ6; c0_hsteps
                · obtain ⟨hb6, _, hlo6x, hhi6x⟩ := log2_step_true (W := 1) (max_b := 62)
                    (by decide) (by decide) hb5 hv5 hhi5 hc
                  exact hJ6 (bit5 + 1#64, ()) m ⟨rfl, by bv_omega, by omega, hlo6x, hhi6x⟩
                · obtain ⟨hb6, _, hlo6x, hhi6x⟩ := log2_step_false (W := 1) (max_b := 62)
                    (by decide) hb5 hv5 hlo5 (Nat.lt_of_lt_of_le (Nat.lt_of_not_le hc) (by decide))
                  have hbit5_nz : bit5.toNat ≠ 0 := fun hz => by rw [hz] at hhi6x; omega
                  exact hJ6 (bit5, ()) m ⟨rfl, by omega, by omega, hlo6x, hhi6x⟩
            · intro J5 hJ5; c0_hsteps
              · obtain ⟨hb5, hv5, hlo5, hhi5⟩ := log2_step_true (W := 2) (max_b := 60)
                  (by decide) (by decide) hb4 hv4 hhi4 hc
                exact hJ5 (bit4 + 2#64, v4 >>> 2, ()) m ⟨rfl, hb5, hv5, hlo5, hhi5⟩
              · obtain ⟨hb5, hv5, hlo5, hhi5⟩ := log2_step_false (W := 2) (max_b := 60)
                  (by decide) hb4 hv4 hlo4 (Nat.lt_of_lt_of_le (Nat.lt_of_not_le hc) (by decide))
                exact hJ5 (bit4, v4, ()) m ⟨rfl, hb5, hv5, hlo5, hhi5⟩
          · intro J4 hJ4; c0_hsteps
            · obtain ⟨hb4, hv4, hlo4, hhi4⟩ := log2_step_true (W := 4) (max_b := 56)
                (by decide) (by decide) hb3 hv3 hhi3 hc
              exact hJ4 (bit3 + 4#64, v3 >>> 4, ()) m ⟨rfl, hb4, hv4, hlo4, hhi4⟩
            · obtain ⟨hb4, hv4, hlo4, hhi4⟩ := log2_step_false (W := 4) (max_b := 56)
                (by decide) hb3 hv3 hlo3 (Nat.lt_of_lt_of_le (Nat.lt_of_not_le hc) (by decide))
              exact hJ4 (bit3, v3, ()) m ⟨rfl, hb4, hv4, hlo4, hhi4⟩
        · intro J3 hJ3; c0_hsteps
          · obtain ⟨hb3, hv3, hlo3, hhi3⟩ := log2_step_true (W := 8) (max_b := 48)
              (by decide) (by decide) hb2 hv2 hhi2 hc
            exact hJ3 (bit2 + 8#64, v2 >>> 8, ()) m ⟨rfl, hb3, hv3, hlo3, hhi3⟩
          · obtain ⟨hb3, hv3, hlo3, hhi3⟩ := log2_step_false (W := 8) (max_b := 48)
              (by decide) hb2 hv2 hlo2 (Nat.lt_of_lt_of_le (Nat.lt_of_not_le hc) (by decide))
            exact hJ3 (bit2, v2, ()) m ⟨rfl, hb3, hv3, hlo3, hhi3⟩
      · intro J2 hJ2; c0_hsteps
        · obtain ⟨hb2, hv2, hlo2, hhi2⟩ := log2_step_true (W := 16) (max_b := 32)
            (by decide) (by decide) hb1 hv1 hhi1 hc
          exact hJ2 (bit1 + 16#64, v1 >>> 16, ()) m ⟨rfl, hb2, hv2, hlo2, hhi2⟩
        · obtain ⟨hb2, hv2, hlo2, hhi2⟩ := log2_step_false (W := 16) (max_b := 32)
            (by decide) hb1 hv1 hlo1 (Nat.lt_of_lt_of_le (Nat.lt_of_not_le hc) (by decide))
          exact hJ2 (bit1, v1, ()) m ⟨rfl, hb2, hv2, hlo2, hhi2⟩
    · intro J1 hJ1; c0_hsteps
      · obtain ⟨hb1, hv1, hlo1, hhi1⟩ := log2_step_true (bit := 0#64) (W := 32) (max_b := 0)
          (by decide) (by decide) (by decide) (by simp) x.isLt hc
        exact hJ1 (0#64 + 32#64, x >>> 32, ()) m ⟨rfl, hb1, hv1, hlo1, hhi1⟩
      · obtain ⟨hb1, hv1, hlo1, hhi1⟩ := log2_step_false (x := x) (v := x) (bit := 0#64) (W := 32)
          (max_b := 0) (by decide) (by decide) (by simp) (by simp; omega)
          (by exact Nat.lt_of_lt_of_le (Nat.lt_of_not_le hc) (by decide))
        exact hJ1 (0#64, x, ()) m ⟨rfl, hb1, hv1, hlo1, hhi1⟩

/-- Parametric `Func.wp` proof for `m8_ae_bump_decay_body` against canonical
`Full.fullBumpDecaySpec` (`FullProbeScratchPres` preserved across AE-bump Q16 decay & rescale). -/
theorem m8_ae_bump_decay_wp (Γ : Env)
    (hLog2 : ∀ a m Q X, m8Log2Q16Spec a m Q X → Γ "m8_log2_q16" [i64] [i64] a m Q X)
    (hRes : ∀ a m Q X, Full.fullRescaleSpec a m Q X → Γ "full_rescale" [i64] [] a m Q X) :
    ∀ a m Q X, Full.fullBumpDecaySpec a m Q X → Func.wp Γ m8_ae_bump_decay_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  unfold Func.wp m8_ae_bump_decay_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun _ m1 => m1 = m) ?_
    (fun _ hJ => by c0_hsteps <;> exact hJ (_, ()) m rfl)
  rintro _ ⟨inc1, ⟨⟩⟩ m1 hm1; subst m1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (_inc2, ()) m2 => ∃ s2 : FullState,
      PreservesCoreSlice FullState.core s s2 ∧ s2.LengthsOk c ∧
      FullProbeScratchPres s s2 ∧ (FullMem c s2 ⋆ R) m2) ?_ ?_
  · rintro _ ⟨inc2, ⟨⟩⟩ m2 ⟨s2, hcore2, hlen2, hpr2, hm2⟩
    clear hm
    c0_hsteps_nogrp
    wac_call hLog2
    intro lg _ _
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ md => md = m2) ?_
      (fun _ hJr => by c0_hsteps <;> exact hJr (_, ()) m2 rfl)
    rintro _ ⟨rel, ⟨⟩⟩ md hmd; subst md
    have h36 : (36#64 : BitVec 64) ≠ 0#64 := by decide
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (rq, ()) mr => mr = m2 ∧ rq.toNat ≤ 65536) ?_
      (fun _ hJq => by
        c0_hsteps
        · exact hJq (65536#64, ()) m2 ⟨rfl, by decide⟩
        · exact hJq _ m2 ⟨rfl, by c0_bound⟩)
    rintro _ ⟨rq, ⟨⟩⟩ mr ⟨hmr, hrq⟩; subst mr
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (d_dyn, ()) md => md = m2 ∧ 60000 ≤ d_dyn.toNat ∧ d_dyn.toNat ≤ 70000) ?_ ?_
    · rintro _ ⟨d_dyn, ⟨⟩⟩ md ⟨hmd, hd_lo, hd_hi⟩; subst md
      have hd_nz : d_dyn ≠ 0#64 := fun hz => by rw [hz] at hd_lo; exact absurd hd_lo (by decide)
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun _ mn => mn = m2) ?_
        (fun _ hJn => by c0_hsteps <;> exact hJn (_, ()) m2 rfl)
      rintro _ ⟨ninc, ⟨⟩⟩ mn hmn; subst mn
      c0_hsteps
      · refine wp_safety_slice_call hRes (fun _ => True) trivial rfl
          (fullState_with_scinc_len hlen2 ninc) (by assumption)
          fun _ s3 m3 hcore3 hlen3 _ hpr3 hm3 => ?_
        dsimp only [fullSafetySlice] at hm3 hlen3
        c0_hsteps
        exact hQ () s3 m3 (hcore2.trans hcore3) hlen3
          (fullProbeScratchPres_trans (fullProbeScratchPres_trans hpr2
            (fullState_with_scinc_pres ninc)) hpr3) hm3
      · exact hQ () { s2 with scratch := { s2.scratch with scinc := ninc } } _ hcore2
          (fullState_with_scinc_len hlen2 ninc)
          (fullProbeScratchPres_trans hpr2 (fullState_with_scinc_pres ninc)) (by assumption)
    · intro Jd hJd; c0_hsplit
      · have hlt : rq.toNat < 32768 := by
          have h32k : (32768#64 : BitVec 64).toNat = 32768 := rfl; bv_omega
        c0_hfast
        obtain ⟨hlo, hhi⟩ := ae_decay_lt_bounds hlt
        exact hJd _ m2 ⟨rfl, hlo, hhi⟩
      · have hge : 32768 ≤ rq.toNat := by
          have h32k : (32768#64 : BitVec 64).toNat = 32768 := rfl; bv_omega
        obtain ⟨_, _, hden_lo, _⟩ := ae_decay_ge_denom hge hrq
        have hden_nz : (27#64 * 65536#64 +
            9#64 * ((((rq - 32768#64) <<< 1) * ((rq - 32768#64) <<< 1)) >>> 16)) ≠ 0#64 :=
          fun hz => by rw [hz] at hden_lo; exact absurd hden_lo (by decide)
        c0_hfast
        obtain ⟨hlo, hhi⟩ := ae_decay_ge_bounds hge hrq
        exact hJd _ m2 ⟨rfl, hlo, hhi⟩
  · intro J2 hJ2; c0_hsteps
    · refine wp_safety_slice_call hRes (fun _ => True) trivial rfl hlen hm
        fun _ s2 m2 hcore2 hlen2 _ hpr2 hm2 => ?_
      dsimp only [fullSafetySlice] at hm2 hlen2
      c0_hsteps
      exact hJ2 (_, ()) m2 ⟨s2, hcore2, hlen2, hpr2, hm2⟩
    · exact hJ2 (_, ()) m ⟨s, rfl, hlen, fullProbeScratchPres_refl s, hm⟩

end AeBumpProofs

/-! ## 4. `64`-Bin Glue Histogram & `delay[8]` Slot Proofs (`5` Functions) -/

section M6HdrWaveAProofs

/-- `m8_hdr_recompute_tiers_mode` (`M6_GLUE_BINS = 64`) satisfies exact `m6HdrW2aSpec [i64] []`. -/
theorem m8_hdr_recompute_tiers_mode_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X)
    (hSync : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_sync_legacy_tiers" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ m8_hdr_recompute_tiers_mode_body a m Q X := by
  rintro ⟨h, st, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp m8_hdr_recompute_tiers_mode_body
  c0_hsteps_nogrp
  wac_call hEnsure
  refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (mode, ()) m2 => m2 = m1 ∧ (mode = 0#64 ∨ mode = 1#64))
    (fun _ (mode, ()) m2 ⟨hm2, hmode⟩ => ?_)
    (fun _ hJm => by
      c0_hsteps
      · exact hJm (1#64, ()) m1 ⟨rfl, Or.inr rfl⟩
      · exact hJm (0#64, ()) m1 ⟨rfl, Or.inl rfl⟩)
  subst m2
  have hmode_le : mode.toNat ≤ 1 := by rcases hmode with rfl | rfl <;> decide
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (base, ()) m2 => m2 = m1 ∧ (base = 32#64 ∨ base = 160#64))
    (fun _ (base, ()) m2 ⟨hm2, hbase⟩ => ?_)
    (fun _ hJb => by
      c0_hsteps
      · exact hJb (32#64, ()) m1 ⟨rfl, Or.inl rfl⟩
      · exact hJb (160#64, ()) m1 ⟨rfl, Or.inr rfl⟩)
  subst m2
  have hbase_le : base.toNat ≤ 160 := by rcases hbase with rfl | rfl <;> decide
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64, i64])
    (fun (_tot, g, ()) mL => g.toNat ≤ 64 ∧ mL = m1)
    (fun (_, g, ()) _ => 64 - g.toNat)
    (fun Jl hJl => by c0_hsteps; exact hJl (0#64, 0#64, ()) m1 ⟨by decide, rfl⟩)
    (fun Jl (tot, g, ()) mL ⟨hg64, hmL⟩ ih => ?_)
  subst mL
  c0_hsteps_nogrp
  · have hg_lt : g.toNat < 64 := by
      have h64 : (64 : BitVec 64).toNat = 64 := rfl; omega
    have hidx : (base + g).toNat < ext1.length := by
      rw [hl1, bv64_add_toNat_small (by omega)]; omega
    have hg1 : (g + 1).toNat = g.toNat + 1 := bv64_add1_toNat (by omega)
    c0_hsteps
    all_goals exact ih (_, g + 1, ()) m1 (by dsimp only; omega) ⟨by omega, rfl⟩
  · have htu_idx : ((14 : BitVec 64) + mode).toNat = 14 + mode.toNat :=
      bv64_add_small (n := 14) rfl (by omega)
    have htu_lt : ((14 : BitVec 64) + mode).toNat < ext1.length := by rw [hl1, htu_idx]; omega
    c0_hsteps_nogrp
    let ext2 := ext1.set ((14 : BitVec 64) + mode).toNat tot
    have hl2 : ext2.length = 288 := by simp [ext2, hl1]
    have hinit2 : M6HdrExtInitOk ext2 := hinit1.set_pos tot (by rw [htu_idx]; omega)
    have hw2 : M6ExtW2bPres ext1 ext2 := M6ExtW2bPres.set_ge8 tot (by rw [htu_idx]; omega)
    let m2 := m
    have hm2 : (FullMem c s ⋆ (array64 (c.hdr - 2304) ext2 ⋆ R)) m2 := hm
    refine wp_join_group (ts := [i64, i64, i64]) (fun _ m3 => m3 = m2)
      (fun _ (_g', t1, t2, ()) m3 hm3 => ?_) ?_
    · subst m3
      refine wp_join_group (ts := [i64]) (fun _ m3 => m3 = m2)
        (fun _ (t2c, ()) m3 hm3 => ?_) ?_
      · subst m3
        have ht1_idx : ((8 : BitVec 64) + mode).toNat = 8 + mode.toNat :=
          bv64_add_small (n := 8) rfl (by omega)
        have ht2_idx : ((10 : BitVec 64) + mode).toNat = 10 + mode.toNat :=
          bv64_add_small (n := 10) rfl (by omega)
        have ht1_lt : ((8 : BitVec 64) + mode).toNat < ext2.length := by rw [hl2, ht1_idx]; omega
        have ht2_lt : ((10 : BitVec 64) + mode).toNat <
            (ext2.set ((8 : BitVec 64) + mode).toNat t1).length := by
          rw [List.length_set, hl2, ht2_idx]; omega
        c0_hsteps_nogrp
        let ext3 := (ext2.set ((8 : BitVec 64) + mode).toNat t1).set
          ((10 : BitVec 64) + mode).toNat t2c
        have hinit3 : M6HdrExtInitOk ext3 :=
          (hinit2.set_pos t1 (by rw [ht1_idx]; omega)).set_pos t2c (by rw [ht2_idx]; omega)
        have hw3 : M6ExtW2bPres ext1 ext3 :=
          hw2.trans ((M6ExtW2bPres.set_ge8 t1 (by rw [ht1_idx]; omega)).trans
            (M6ExtW2bPres.set_ge8 t2c (by rw [ht2_idx]; omega)))
        wac_call hSync
        refine m6HdrW2aSpec_of rfl hcfg hinit3.toOk hlen
          ((fullM6HdrMem_iff ..).mpr (by assumption))
          fun () ext4 s4 m4 hcore4 hlen4 hpres4 hok4 hw4 hm4 => ?_
        have ⟨hinit4, hw34⟩ := hw4 hinit3
        exact hQ () ext4 s4 m4 hcore4 hlen4 hpres4 hok4
          (w2a_pres_of_init hpres1 hinit4 (hw3.trans hw34)) hm4
      · intro _ hJt2c; c0_hsteps <;> exact hJt2c (_, ()) m2 rfl
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
                (fun (g, _t1, _acc, _g1, ()) mL => g.toNat ≤ 64 ∧ mL = m2)
                (fun (g, _, _, _, ()) _ => 64 - g.toNat)
                (fun Ja hJa => by c0_hsteps; exact hJa (0#64, _, _, _, ()) m2 ⟨by decide, rfl⟩)
                (fun Ja (g, t1, acc, g1, ()) mL ⟨hg64', hmL⟩ ih2 => ?_)
              subst mL
              c0_hsteps_nogrp
              · have hg_lt : g.toNat < 64 := by
                  have h64 : (64 : BitVec 64).toNat = 64 := rfl; omega
                have hidx2 : (base + g).toNat < ext2.length := by
                  rw [hl2, bv64_add_toNat_small (by omega)]; omega
                have hg1 : (g + 1).toNat = g.toNat + 1 := bv64_add1_toNat (by omega)
                c0_hsteps
                all_goals
                  try exact ih2 (g + 1, _, _, _, ()) m2 (by dsimp only; omega) ⟨by omega, rfl⟩
                all_goals (c0_hsteps; exact hJb (_, _, _, _, _, _, ()) m2 rfl)
              · c0_hsteps <;> exact hJb (_, _, _, _, _, _, ()) m2 rfl
          · intro _ hJ2; c0_hsteps <;> exact hJ2 (_, ()) m2 rfl
        · intro _ hJ1; c0_hsteps <;> exact hJ1 (_, ()) m2 rfl
      · exact hJt (_, _, _, ()) m2 rfl

/-- `m8_hdr_record_used` (`M6_GLUE_BINS = 64`) satisfies exact `m6HdrW2aSpec [i64] []`. -/
theorem m8_hdr_record_used_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ m8_hdr_record_used_body a m Q X := by
  rintro ⟨h, glue, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp m8_hdr_record_used_body
  c0_hsteps_nogrp
  wac_call hEnsure
  refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [fullM6HdrMem_iff] at hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (st, ()) m2 => m2 = m1 ∧ (st = 0#64 ∨ st = 1#64))
    (fun _ (st, ()) m2 ⟨hm2, hst⟩ => ?_)
    (fun _ hJs => by
      c0_hsteps
      · exact hJs (1#64, ()) m1 ⟨rfl, Or.inr rfl⟩
      · exact hJs (0#64, ()) m1 ⟨rfl, Or.inl rfl⟩)
  subst m2
  have hst_le : st.toNat ≤ 1 := by rcases hst with rfl | rfl <;> decide
  refine wp_join_group (ts := [i64]) (fun (gi, ()) m2 => m2 = m1 ∧ gi.toNat < 64)
    (fun _ (gi, ()) m2 ⟨hm2, hgi⟩ => ?_)
    (fun _ hJg => by
      c0_hsteps
      · exact hJg (_, ()) m1 ⟨rfl, by decide⟩
      · exact hJg (glue, ()) m1 ⟨rfl, by
          have h64 : (64 : BitVec 64).toNat = 64 := rfl; omega⟩)
  subst m2
  refine wp_join_group (ts := [i64])
    (fun (base, ()) m2 => m2 = m1 ∧ (base = 32#64 ∨ base = 160#64))
    (fun _ (base, ()) m2 ⟨hm2, hbase⟩ => ?_)
    (fun _ hJb => by
      c0_hsteps
      · exact hJb (32#64, ()) m1 ⟨rfl, Or.inl rfl⟩
      · exact hJb (160#64, ()) m1 ⟨rfl, Or.inr rfl⟩)
  subst m2
  have hbase_ge : 32 ≤ base.toNat := by rcases hbase with rfl | rfl <;> decide
  have hbase_le : base.toNat ≤ 160 := by rcases hbase with rfl | rfl <;> decide
  have hbg_eq : (base + gi).toNat = base.toNat + gi.toNat := bv64_add_toNat_small (by omega)
  have hbg_lt : (base + gi).toNat < ext1.length := by rw [hl1, hbg_eq]; omega
  c0_hsteps_nogrp
  refine wp_join_group (ts := [])
    (fun () m2 => ∃ ext2, M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext1 ext2 ∧
      (FullMem c s ⋆ (array64 (c.hdr - 2304) ext2 ⋆ R)) m2)
    (fun _ () m2 ⟨ext2, hinit2, hw2, hm2⟩ => ?_)
    (fun _ hJu => by
      c0_hsteps
      · refine hJu () _ ⟨ext1.set (base + gi).toNat _,
          hinit1.set_pos _ (by rw [hbg_eq]; omega),
          M6ExtW2bPres.set_ge8 _ (by rw [hbg_eq]; omega), by assumption⟩
      · exact hJu () m1 ⟨ext1, hinit1, M6ExtW2bPres.refl ext1, hm1⟩)
  have hl2 : ext2.length = 288 := hinit2.toOk.len
  have htu_eq : ((14 : BitVec 64) + st).toNat = 14 + st.toNat :=
    bv64_add_small (n := 14) rfl (by omega)
  have htu_lt : ((14 : BitVec 64) + st).toNat < ext2.length := by rw [hl2, htu_eq]; omega
  c0_hsteps
  · refine hQ () _ s _ rfl hlen (M6HdrScratchPres.refl s) ?_ ?_
      ((fullM6HdrMem_iff ..).mpr (by assumption))
    · exact (hinit2.set_pos _ (by rw [htu_eq]; omega)).toOk
    · exact w2a_pres_of_init hpres1 (hinit2.set_pos _ (by rw [htu_eq]; omega))
        (hw2.trans (M6ExtW2bPres.set_ge8 _ (by rw [htu_eq]; omega)))
  · exact hQ () ext2 s m2 rfl hlen (M6HdrScratchPres.refl s) hinit2.toOk
      (w2a_pres_of_init hpres1 hinit2 hw2) ((fullM6HdrMem_iff ..).mpr hm2)

/-- `m6_hdr_delaying` extended to `id < 8` (slots `4..7` at `M8W_DEL_CNT_BASE = 120..123`)
satisfies exact `m6HdrW2aSpec [i64] [.bool]`. -/
theorem m6_hdr_delaying_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Func.wp Γ m6_hdr_delaying_body a m Q X := by
  rintro ⟨h, id, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp m6_hdr_delaying_body
  c0_hsteps_nogrp
  · exact hQ (false, ()) ext s m rfl hlen (M6HdrScratchPres.refl s) hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) hm
  · have hid8 : id.toNat < 8 := by
      have h8 : (8 : BitVec 64).toNat = 8 := rfl; omega
    wac_call hEnsure
    refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
    have hl1 : ext1.length = 288 := hinit1.toOk.len
    rw [fullM6HdrMem_iff] at hm1
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (idx, ()) m2 => m2 = m1 ∧ 8 ≤ idx.toNat ∧ idx.toNat < ext1.length)
      (fun _ (idx, ()) m2 ⟨hm2, hidx8, hidx_lt⟩ => by
        subst m2
        c0_hsteps
        · refine hQ (true, ()) _ s _ rfl hlen (M6HdrScratchPres.refl s) ?_ ?_
            ((fullM6HdrMem_iff ..).mpr (by assumption))
          · exact (hinit1.set_pos _ (by omega)).toOk
          · exact w2a_pres_of_init hpres1 (hinit1.set_pos _ (by omega))
              (M6ExtW2bPres.set_ge8 _ hidx8)
        · exact hQ (false, ()) ext1 s m1 rfl hlen (M6HdrScratchPres.refl s) hinit1.toOk
            (w2a_pres_of_init hpres1 hinit1 (M6ExtW2bPres.refl ext1))
            ((fullM6HdrMem_iff ..).mpr hm1))
      (fun _ hJi => by
        c0_hsteps
        · exact hJi (_, ()) m1 ⟨rfl, by bv_omega, by rw [hl1]; bv_omega⟩
        · exact hJi (_, ()) m1 ⟨rfl, by bv_omega, by rw [hl1]; bv_omega⟩)

/-- `m6_hdr_bump_delay` extended to `id < 8` (slots `4..7` at `120..127`) satisfies exact
`m6HdrW2aSpec [i64] []`. -/
theorem m6_hdr_bump_delay_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ m6_hdr_bump_delay_body a m Q X := by
  rintro ⟨h, id, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp m6_hdr_bump_delay_body
  c0_hsteps_nogrp
  · exact hQ () ext s m rfl hlen (M6HdrScratchPres.refl s) hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) hm
  · have hid8 : id.toNat < 8 := by
      have h8 : (8 : BitVec 64).toNat = 8 := rfl; omega
    wac_call hEnsure
    refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
    have hl1 : ext1.length = 288 := hinit1.toOk.len
    rw [fullM6HdrMem_iff] at hm1
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (cidx, ()) m2 => m2 = m1 ∧ 8 ≤ cidx.toNat ∧ cidx.toNat < ext1.length) ?_ ?_
    · rintro _ ⟨cidx, ⟨⟩⟩ m2 ⟨hm2, hc8, hc_lt⟩; subst m2
      refine wp_join_group (ts := [i64])
        (fun (nidx, ()) m3 => m3 = m1 ∧ 8 ≤ nidx.toNat ∧ nidx.toNat < ext1.length) ?_ ?_
      · rintro _ ⟨nidx, ⟨⟩⟩ m3 ⟨hm3, hn8, hn_lt⟩; subst m3
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64]) (fun _ m4 => m4 = m1) ?_
          (fun _ hJcap => by c0_hsteps <;> exact hJcap (_, ()) m1 rfl)
        rintro _ ⟨cap, ⟨⟩⟩ m4 hm4; subst m4
        refine wp_join_group (ts := [i64]) (fun _ m5 => m5 = m1) ?_
          (fun _ hJc => by c0_hsteps <;> exact hJc (_, ()) m1 rfl)
        rintro _ ⟨cur, ⟨⟩⟩ m5 hm5; subst m5
        have hn_lt2 : nidx.toNat < (ext1.set cidx.toNat cur).length := by
          rw [List.length_set]; exact hn_lt
        c0_hsteps
        let ext2 := (ext1.set cidx.toNat cur).set nidx.toNat cur
        have hinit2 : M6HdrExtInitOk ext2 :=
          (hinit1.set_pos cur (by omega)).set_pos cur (by omega)
        have hw2 : M6ExtW2bPres ext1 ext2 :=
          (M6ExtW2bPres.set_ge8 cur hc8).trans (M6ExtW2bPres.set_ge8 cur hn8)
        exact hQ () ext2 s _ rfl hlen (M6HdrScratchPres.refl s) hinit2.toOk
          (w2a_pres_of_init hpres1 hinit2 hw2) ((fullM6HdrMem_iff ..).mpr (by assumption))
      · intro _ hJn; c0_hsteps
        · exact hJn (_, ()) m1 ⟨rfl, by bv_omega, by rw [hl1]; bv_omega⟩
        · exact hJn (_, ()) m1 ⟨rfl, by bv_omega, by rw [hl1]; bv_omega⟩
    · intro _ hJc; c0_hsteps
      · exact hJc (_, ()) m1 ⟨rfl, by bv_omega, by rw [hl1]; bv_omega⟩
      · exact hJc (_, ()) m1 ⟨rfl, by bv_omega, by rw [hl1]; bv_omega⟩

/-- `m6_hdr_reduce_delay` extended to `id < 8` (slots `4..7` at `120..127`) satisfies exact
`m6HdrW2aSpec [i64] []`. -/
theorem m6_hdr_reduce_delay_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Func.wp Γ m6_hdr_reduce_delay_body a m Q X := by
  rintro ⟨h, id, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hs
  unfold Func.wp m6_hdr_reduce_delay_body
  c0_hsteps_nogrp
  · exact hQ () ext s m rfl hlen (M6HdrScratchPres.refl s) hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) hm
  · have hid8 : id.toNat < 8 := by
      have h8 : (8 : BitVec 64).toNat = 8 := rfl; omega
    wac_call hEnsure
    refine m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
    have hl1 : ext1.length = 288 := hinit1.toOk.len
    rw [fullM6HdrMem_iff] at hm1
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (cidx, ()) m2 => m2 = m1 ∧ 8 ≤ cidx.toNat ∧ cidx.toNat < ext1.length) ?_ ?_
    · rintro _ ⟨cidx, ⟨⟩⟩ m2 ⟨hm2, hc8, hc_lt⟩; subst m2
      refine wp_join_group (ts := [i64])
        (fun (nidx, ()) m3 => m3 = m1 ∧ 8 ≤ nidx.toNat ∧ nidx.toNat < ext1.length) ?_ ?_
      · rintro _ ⟨nidx, ⟨⟩⟩ m3 ⟨hm3, hn8, hn_lt⟩; subst m3
        have hn_lt2 : nidx.toNat < (ext1.set cidx.toNat (ext1[cidx.toNat] >>> 1)).length := by
          rw [List.length_set]; exact hn_lt
        c0_hsteps
        refine hQ () _ s _ rfl hlen (M6HdrScratchPres.refl s) ?_ ?_
          ((fullM6HdrMem_iff ..).mpr (by assumption))
        · exact ((hinit1.set_pos _ (by omega)).set_pos _ (by omega)).toOk
        · exact w2a_pres_of_init hpres1
            ((hinit1.set_pos _ (by omega)).set_pos _ (by omega))
            ((M6ExtW2bPres.set_ge8 _ hc8).trans (M6ExtW2bPres.set_ge8 _ hn8))
      · intro _ hJn; c0_hsteps
        · exact hJn (_, ()) m1 ⟨rfl, by bv_omega, by rw [hl1]; bv_omega⟩
        · exact hJn (_, ()) m1 ⟨rfl, by bv_omega, by rw [hl1]; bv_omega⟩
    · intro _ hJc; c0_hsteps
      · exact hJc (_, ()) m1 ⟨rfl, by bv_omega, by rw [hl1]; bv_omega⟩
      · exact hJc (_, ()) m1 ⟨rfl, by bv_omega, by rw [hl1]; bv_omega⟩

end M6HdrWaveAProofs

/-! ## 5. Adaptive Vivification, BVE Throttling, & Backbone Tail Proofs (`4` Functions) -/

section InprocProofs

private theorem sparse_with_tr_wac {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {tr' : List (BitVec 32)} (htr : tr'.length = 2 * c.max_vars) :
    FullSparseInv c F0 { s with scratch := { s.scratch with tarjan_reach := tr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with tarjan_reach_len := htr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem sparse_with_rr_wac {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {rr' : List (BitVec 32)} (hrr : rr'.length = c.red_cap) :
    FullSparseInv c F0 { s with scratch := { s.scratch with red_refs := rr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with red_refs_len := hrr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem sparseInvW_of_prop_wac {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64}
    {wsort' : List (BitVec 32)} {phases' : List (BitVec 8)} {delayed' : List (BitVec 32)}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases',
                                  delayed := delayed' } } :
      FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
                    wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                    confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                    confl_lit1 := c1', oom := oom' })
    (hperm : FullArenaPermEq s.core
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
                    wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                    confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                    confl_lit1 := c1', oom := oom' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              propagated := prop', unassigned := unass', unflushed := unfl',
                              wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                              wusable := wu', fuel := fuel', confl_type := ctype',
                              confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                              oom := oom' }
        scratch := { s.scratch with
          search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases',
                                  delayed := delayed' } }
  have hnd' : FullArenaVarsNodup s' := fun ref href hng => by
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 ref href0 (hgb.symm.trans hng))
  have hrefs : ∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s' := fun ref hr => by
    change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact hr
  exact FullVivTop.fullSparseInvW_of_prop_state hsp hlen' hw' hnd'
    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hrefs

private theorem tr_lim_ne_zero (dticks : BitVec 64) :
    dticks / 50#64 + 100000#64 ≠ 0#64 := by
  have hdiv : (dticks / 50#64).toNat < 2 ^ 64 / 50 + 1 := by
    rw [BitVec.toNat_udiv, show (50#64 : BitVec 64).toNat = 50 from rfl]
    have := dticks.isLt; omega
  intro hz
  have hto := congrArg BitVec.toNat hz
  rw [BitVec.toNat_add, show (100000#64 : BitVec 64).toNat = 100000 from rfl,
    BitVec.toNat_zero, Nat.mod_eq_of_lt (by omega)] at hto
  omega

/-- Parametric `Func.wp` proof for `full_vivify_tier_m6_hdr_body` against `m8VivifyTierSpec`
(recording `e[M8W_VIV_LAST_TRIED]` at word `118`, skipping redundant histogram sorting for
`tier_mode == 0 && num_irred / 10 <= num_redundant`). -/
theorem full_vivify_tier_m6_hdr_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCollect : ∀ a m Q X, fullVivCollectM6Spec a m Q X →
      Γ "full_viv_collect_m6" [i64, i64] [i64] a m Q X)
    (hCount : ∀ a m Q X, fullVivCountM6Spec a m Q X →
      Γ "full_viv_count_m6" [i64, i64] [] a m Q X)
    (hKeys : ∀ a m Q X, fullVivKeysM6Spec a m Q X →
      Γ "full_viv_keys_m6" [i64, i64] [] a m Q X)
    (hSortSched : ∀ a m Q X, fullVivSortSchedM6Spec a m Q X →
      Γ "full_viv_sort_sched_m6" [i64, i64] [] a m Q X)
    (hVivClause : ∀ a m Q X, fullVivClauseM6Spec a m Q X →
      Γ "full_viv_clause_m6" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullBcpS15Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hClearTier : ∀ a m Q X, fullVivClearTierM6Spec a m Q X →
      Γ "full_viv_clear_tier_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, m8VivifyTierSpec a m Q X → Func.wp Γ full_vivify_tier_m6_hdr_body a m Q X := by
  rintro ⟨h, tier_mode, budget0, tick_lim, ⟨⟩⟩ m0 Q X hs
  obtain ⟨c, F0, ext, s, R, rfl, hcfg, hext, hsp0, hm0, hQ⟩ := m8VivifyTierSpec_elim hs
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold LratBytes.dimacsBound at har_cap hmx hrc
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := hmx
  have h3 : (3#64 : BitVec 64) ≠ 0#64 := by decide
  have h10 : (10#64 : BitVec 64) ≠ 0#64 := by decide
  have h118_mod : (944#64 : BitVec 64).toNat % 8 = 0 := by decide
  have h118_lt : (944#64 : BitVec 64).toNat / 8 < ext.length := by rw [hext.len]; decide
  unfold Func.wp full_vivify_tier_m6_hdr_body; c0_hsteps_nogrp
  · exact hQ 1#64 ext s m0 hext (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) hsp0 (fun h => h)
      (fun h => h) (fun hb => absurd (by c0_bound) hb) (Nat.le_refl _) (Or.inl rfl)
      (fun h => by cases h) hm0
  rw [fullM6HdrMem_iff] at hm0
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (FullMem c s1 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m1) ?_ ?_
  · rintro _ ⟨⟩ m ⟨s1, hsp1, hcl1, hfl1, hm⟩
    c0_hsteps_nogrp
    let s2 : FullState := { s1 with core := { s1.core with probing := 1#64 } }
    have hsp2 : FullSparseInv c F0 s2 := FullVivTop.FullSparseInv.with_probing hsp1 1#64
    have hm2 : (FullMem c s2 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m := hm
    have hfl2 : s2.core.fuel.toNat ≤ s.core.fuel.toNat := hfl1
    clear_value s2; clear hsp1 hcl1 hfl1
    wac_call hCollect
    refine ⟨c, F0, s2, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp2, hm2,
      fun bn rr3 m3 h3bn hrr3 hok3 hm3 => ?_⟩
    let s3 : FullState := { s2 with scratch := { s2.scratch with red_refs := rr3 } }
    have hsp3 : FullSparseInv c F0 s3 := sparse_with_rr_wac hsp2 hrr3
    c0_hsteps_nogrp
    refine wp_join_group (ts := [])
      (fun () m5 => ∃ s5 : FullState, FullSparseInv c F0 s5 ∧
        s5.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        fullArenaClauseRefs s5 = fullArenaClauseRefs s2 ∧
        s5.scratch.red_refs.length = c.red_cap ∧
        (∀ k < bn.toNat, (s5.scratch.red_refs[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s2) ∧
        (FullMem c s5 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m5) ?_ ?_
    · rintro _ ⟨⟩ m5 ⟨s5, hsp5, hfl5, hrefs5, hrr5_len, hok5', hm5'⟩
      let rr5 := s5.scratch.red_refs
      have hrr5 : s5.scratch.red_refs = rr5 := rfl
      clear hrr3 hok3 hm3 s3 hsp3 hsp2 hm2 hfl2 hCollect hCount hKeys hSortSched
      c0_hsteps_nogrp
      refine wp_loop_break_group (brkTs := [i64, i64, i64]) (lpTs := [i64, i64])
        (fun (_budget_b, res_b, bi_b, ()) mb => ∃ sb : FullState,
          FullSparseInv c F0 sb ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (res_b = 1#64 ∨ res_b = 20#64) ∧ (res_b = 20#64 → F0.Unsat) ∧
          (FullMem c sb ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) mb)
        (fun rem (budget, bi, ()) mvi => ∃ svi : FullState,
          bi.toNat ≤ bn.toNat ∧ rem = bn.toNat - bi.toNat ∧
          FullSparseInv c F0 svi ∧ svi.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          fullArenaClauseRefs svi = fullArenaClauseRefs s2 ∧
          svi.scratch.red_refs = rr5 ∧
          (FullMem c svi ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) mvi)
        ?_ ?_ ?_
      · rintro _ ⟨_, res_b, bi_b, ⟨⟩⟩ mb ⟨sb, hspb, hflb, hresb, h20b, hmb⟩
        refine wp_join_group (ts := [])
          (fun () m_bt => ∃ sbt : FullState, FullSparseInv c F0 sbt ∧ sbt.core.cur_level = 0 ∧
            sbt.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (FullMem c sbt ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m_bt) ?_ ?_
        · rintro _ ⟨⟩ m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
          refine wp_join_group (ts := [])
            (fun () m_w => ∃ sw : FullState, FullSparseInv c F0 sw ∧ sw.core.cur_level = 0 ∧
              sw.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullMem c sw ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m_w) ?_ ?_
          · rintro _ ⟨⟩ m_w ⟨sw, hspw, hclw, hflw, hm_w⟩
            c0_hsteps
            let ext' := ext.set ((944#64 : BitVec 64).toNat / 8) bi_b
            have hext' : M6HdrExtOk ext' := M6HdrExtOk.of_len (by rw [List.length_set, hext.len])
            have hpres' : M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext' :=
              fun hi => ⟨hi.set_pos _ (by decide), M6ExtW2bPres.set_ge8 _ (by decide)⟩
            let sf : FullState := { sw with core := { sw.core with probing := 0#64 } }
            have hspf : FullSparseInv c F0 sf := FullVivTop.FullSparseInv.with_probing hspw 0#64
            exact hQ res_b ext' sf _ hext' hpres' hspf (fun _ => hclw) (fun _ => rfl)
              (fun _ => ⟨hclw, rfl⟩) hflw hresb h20b ((fullM6HdrMem_iff ..).mpr (by assumption))
          · intro Jw hJw; c0_hsteps
            · wac_call hClearTier
              refine ⟨c, F0, sbt, array64 (c.hdr - 2304) ext ⋆ R, rfl, hspbt, hclbt, hm_bt,
                fun sw m_w hspw hclw hflw hm_w =>
                  hJw () m_w ⟨sw, hspw, hclw, by rw [hflw]; exact hflbt, hm_w⟩⟩
            · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
            · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
            · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
        · intro Jbt hJbt
          obtain ⟨F_curb, hswb⟩ := hspb.exists_witness
          have hclb_lt : sb.core.cur_level < 2 ^ 64 := by
            have := hswb.2.1.cur_level_le; have := hspb.1.lengths.core_ok.trail_end_le
            have := hspb.1.lengths.core_ok.cur_vars_le; omega
          c0_hsteps
          · wac_call hBacktrack
            refine ⟨c, sb, array64 (c.hdr - 2304) ext ⋆ R, rfl, hspb.1.lengths, hclb_lt,
              (by intro _; have := hswb.2.1.cur_level_le
                  have := hspb.1.lengths.core_ok.trail_end_le
                  have := hspb.1.lengths.core_ok.cur_vars_le; omega),
              hswb.2.1.trail_lits_lt, hmb,
              fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
                hlen_bt _ _ hcl_bt hpres_bt _ _ _ hw_bt _ hm_bt => ?_⟩
            have hsp_bt : FullSparseInv c F0 _ :=
              FullVivTop.FullSparseInv.of_backtrack hspb (Nat.zero_le _) hlen_bt hpres_bt
                (by simpa using hw_bt F0)
            exact hJbt () m_bt ⟨_, hsp_bt, by rw [hcl_bt]; simp, hflb, hm_bt⟩
          · have hclb0 : sb.core.cur_level = 0 := by
              have h0 : (BitVec.ofNat 64 sb.core.cur_level).toNat = 0 := by rw [hc]; rfl
              rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclb_lt] at h0
            exact hJbt () mb ⟨sb, hspb, hclb0, hflb, hmb⟩
      · intro B L rem ⟨budget, bi, ⟨⟩⟩ mvi hB hL
          ⟨svi, hbi_le, hrem, hspv, hflv, hrefsv, hrrv, hmvi⟩
        subst hrem
        c0_hsteps
        · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
          have hbi3_nat : (bi * 3).toNat = 3 * bi.toNat := by
            rw [BitVec.toNat_mul, show (3 : BitVec 64).toNat = 3 from rfl,
              Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
          have hrr5_len' : rr5.length = c.red_cap := hrr5_len
          have hbi3_lt : (bi * 3).toNat < svi.scratch.red_refs.length := by
            rw [hrrv, hrr5_len', hbi3_nat]; omega
          let cr := svi.scratch.red_refs[(bi * 3).toNat]'hbi3_lt
          have hcr_ref : cr.toNat ∈ fullArenaClauseRefs svi := by
            rw [hrefsv]
            have h := hok5' bi.toNat hbi_lt
            dsimp only [rr5] at hrr5_len' h ⊢
            rw [List.getElem?_eq_getElem (by rw [hrr5_len']; omega), Option.getD_some] at h
            have heq : cr = s5.scratch.red_refs[3 * bi.toNat]'(by rw [hrr5_len']; omega) :=
              Option.some.inj (by
                rw [← List.getElem?_eq_getElem hbi3_lt, hrrv, hbi3_nat,
                  List.getElem?_eq_getElem (by rw [hrr5_len']; omega)])
            rwa [heq]
          obtain ⟨F_curv, hswv⟩ := hspv.exists_witness
          have hbi1 : (bi + 1#64).toNat = bi.toNat + 1 := by bv_omega
          c0_hsteps
          wac_call hVivClause
          refine ⟨c, F0, F_curv, svi, array64 (c.hdr - 2304) ext ⋆ R, rfl, hswv, hcr_ref, hmvi,
            fun vc s_vc m_vc hsw_vc hfl_vc _ hrefs_vc hrr_vc hvc h20_vc hm_vc => ?_⟩
          have hrefs_vc2 : fullArenaClauseRefs s_vc = fullArenaClauseRefs s2 :=
            hrefs_vc.trans hrefsv
          have hrr_vc5 : s_vc.scratch.red_refs = rr5 := hrr_vc.trans hrrv
          have hfl_vc' : s_vc.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_vc hflv
          c0_hsteps
          · exact hB (budget - 1#64, 20#64, bi, ()) m_vc
              ⟨s_vc, hsw_vc.toSparse, hfl_vc', Or.inr rfl, fun _ => h20_vc (by c0_bound), hm_vc⟩
          · exact hB (budget - 1#64, 1#64, bi, ()) m_vc
              ⟨s_vc, hsw_vc.toSparse, hfl_vc', Or.inl rfl, (fun h => by cases h), hm_vc⟩
          · have hcl_vc_lt : s_vc.core.cur_level < 2 ^ 64 := by
              have := hsw_vc.2.1.cur_level_le; have := hsw_vc.1.core_ok.trail_end_le
              have := hsw_vc.1.core_ok.cur_vars_le; omega
            have hcl_vc0 : s_vc.core.cur_level = 0 := by
              have h0 : (BitVec.ofNat 64 s_vc.core.cur_level).toNat = 0 := by
                have hc0 : BitVec.ofNat 64 s_vc.core.cur_level = 0#64 := by c0_bound
                rw [hc0]; rfl
              rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_vc_lt] at h0
            wac_call hProp
            refine ⟨c, F0, F_curv, s_vc, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsw_vc.1,
              hsw_vc.2.1, hsw_vc.2.2.2.2.2, hm_vc,
              fun pr vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
                wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p
                ticks_p wsort_p phases_p delayed_p m_p hlen_p hw_p _ hperm_p _ hfl_p _ _ hpr1 _ _
                hm_p => ?_⟩
            let s_p : FullState :=
              { s_vc with
                core := { s_vc.core with
                  vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
                  trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
                  unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
                  arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
                  fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
                  confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
                scratch := { s_vc.scratch with
                  search_ticks := ticks_p, wsort := wsort_p, phases := phases_p,
                  delayed := delayed_p } }
            have hsw_p : FullSparseInvW c F0 F_curv s_p :=
              sparseInvW_of_prop_wac hsw_vc hlen_p hw_p hperm_p
            have hrefs_p : fullArenaClauseRefs s_p = fullArenaClauseRefs s_vc := hperm_p.2.1
            have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_p hfl_vc'
            c0_hsteps
            · have hpr_eq1 : pr = 1#64 := by c0_bound
              have hunsat : F0.Unsat :=
                FullVivTopSpecs.level0_unsat_of_conflict_okW hw_p hcl_vc0 (hpr1 hpr_eq1).2.2
              exact hB (budget - 1#64, 20#64, bi, ()) m_p
                ⟨s_p, hsw_p.toSparse, hfl_p', Or.inr rfl, fun _ => hunsat, hm_p⟩
            · exact hL (bn.toNat - (bi + 1#64).toNat) (budget - 1#64, bi + 1#64, ()) m_p
                (by rw [hbi1]; omega)
                ⟨s_p, by rw [hbi1]; omega, rfl, hsw_p.toSparse, hfl_p',
                  hrefs_p.trans hrefs_vc2, hrr_vc5, hm_p⟩
          · exact hL (bn.toNat - (bi + 1#64).toNat) (budget - 1#64, bi + 1#64, ()) m_vc
              (by rw [hbi1]; omega)
              ⟨s_vc, by rw [hbi1]; omega, rfl, hsw_vc.toSparse, hfl_vc', hrefs_vc2, hrr_vc5, hm_vc⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · intro B L _ hL; c0_hsteps
        exact hL bn.toNat (budget0, 0#64, ()) m5
          ⟨s5, Nat.zero_le _, by simp, hsp5, hfl5, hrefs5, hrr5, hm5'⟩
    · intro J5 hJ5; c0_hsteps
      · exact hJ5 () m3 ⟨s3, hsp3, hfl2, rfl, hrr3, hok3, hm3⟩
      all_goals
        wac_call hCount
        refine ⟨c, F0, s3, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp3, h3bn, hok3, hm3,
          fun tr3 m3c htr3 hm3c => ?_⟩
        let s3c : FullState := { s3 with scratch := { s3.scratch with tarjan_reach := tr3 } }
        have hsp3c : FullSparseInv c F0 s3c := sparse_with_tr_wac hsp3 htr3
        wac_call hKeys
        refine ⟨c, F0, s3c, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp3c, h3bn, hok3, hm3c,
          fun rr4 m4 hrr4 hok4 hm4 => ?_⟩
        let s4 : FullState := { s3c with scratch := { s3c.scratch with red_refs := rr4 } }
        have hsp4 : FullSparseInv c F0 s4 := sparse_with_rr_wac hsp3c hrr4
        wac_call hSortSched
        refine ⟨c, F0, s4, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp4, h3bn, hok4, hm4,
          fun rr5 m5 hrr5_len hok5 hm5 => ?_⟩
        let s5 : FullState := { s4 with scratch := { s4.scratch with red_refs := rr5 } }
        exact hJ5 () m5 ⟨s5, sparse_with_rr_wac hsp4 hrr5_len, hfl2, rfl, hrr5_len, hok5, hm5⟩
  · intro Jc hJc
    obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
    have hcl0_lt : s.core.cur_level < 2 ^ 64 := by
      have := hsw0.2.1.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
      have := hsp0.1.lengths.core_ok.cur_vars_le; omega
    c0_hsteps
    · wac_call hBacktrack
      refine ⟨c, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp0.1.lengths, hcl0_lt,
        (by intro _; have := hsw0.2.1.cur_level_le
            have := hsp0.1.lengths.core_ok.trail_end_le
            have := hsp0.1.lengths.core_ok.cur_vars_le; omega),
        hsw0.2.1.trail_lits_lt, hm0,
        fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1
          hlen1 _ _ hcl1 hpres1 _ _ _ hw_bt _ hm1 => ?_⟩
      have hsp1 : FullSparseInv c F0 _ :=
        FullVivTop.FullSparseInv.of_backtrack hsp0 (Nat.zero_le _) hlen1 hpres1
          (by simpa using hw_bt F0)
      exact hJc () m1 ⟨_, hsp1, by rw [hcl1]; simp, Nat.le_refl _, hm1⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have h0 : (BitVec.ofNat 64 s.core.cur_level).toNat = 0 := by rw [hc]; rfl
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl0_lt] at h0
      exact hJc () m0 ⟨s, hsp0, hcl0, Nat.le_refl _, hm0⟩

/-- Parametric `Func.wp` proof for `full_vivify_m6_hdr_body` against canonical
`m6aVivifySpec` (including M8 adaptive `M8_DELAY_VIVIFY_IRR` throttling around tier 0). -/
theorem full_vivify_m6_hdr_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hSync : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_sync_legacy_tiers" [i64] [] a m Q X)
    (hGetWm : ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hDelaying : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hBumpDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hReduceDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hVivTier : ∀ a m Q X, m8VivifyTierSpec a m Q X →
      Γ "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6aVivifySpec a m Q X → Func.wp Γ full_vivify_m6_hdr_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, ext, s, R, rfl, hcfg, hext, hsp, hm, hQ⟩ := m6aVivifySpec_elim hs
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold LratBytes.dimacsBound at har_cap hmx hrc
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := hmx
  obtain ⟨F_cur, hw0⟩ := hsp.1.witness
  have hco0 := hsp.1.lengths.core_ok
  have hclv_lt : s.core.cur_level < 2 ^ 64 := by
    have := hw0.cur_level_le; have := hco0.trail_end_le; have := hco0.cur_vars_le; omega
  have hmax_vars_pos : 0 < s.core.cur_level → 0 < c.max_vars := by
    intro _; have := hw0.cur_level_le; have := hco0.trail_end_le; have := hco0.cur_vars_le; omega
  have h10 : (10#64 : BitVec 64) ≠ 0#64 := by decide
  have hbud : (0xFFFFFFFF#64 : BitVec 64) ≠ 0#64 := by decide
  unfold Func.wp full_vivify_m6_hdr_body; c0_hsteps_nogrp
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext s1 ⋆ R) m1)
    (fun _ () m1 ⟨s1, hsp1, hcl01, hfu1, hm1⟩ => ?_) (fun _ hJ => ?_)
  · clear hm
    wac_call hSync
    refine m6HdrW2aSpec_of rfl hcfg hext hsp1.1.lengths hm1
      fun () ext2 s2 m2 hcore2 hlen2 hsc2 hext2 hw2 hm2 => ?_
    have hsp2 : FullSparseInv c F0 s2 := fullSparseInv_of_core_eq_wac hsp1 hlen2 hcore2 hsc2
    have hcl02 : s2.core.cur_level = 0 := by rw [hcore2]; exact hcl01
    rw [fullM6HdrMem_iff] at hm2
    c0_hsteps_nogrp
    wac_call hGetWm
    refine m6HdrW2aSpec_of rfl hcfg hext2 hsp2.1.lengths ((fullM6HdrMem_iff ..).mpr hm2)
      fun ⟨last_p, ⟨⟩⟩ ext3 s3 m3 hcore3 hlen3 hsc3 hext3 hw3 hm3 => ?_
    have hsp3 : FullSparseInv c F0 s3 := fullSparseInv_of_core_eq_wac hsp2 hlen3 hcore3 hsc3
    have hcl03 : s3.core.cur_level = 0 := by rw [hcore3]; exact hcl02
    have hpres3 : M6HdrExtInitOk ext → M6HdrExtInitOk ext3 ∧ M6ExtW2bPres ext ext3 :=
      ext_pres_compose hw2 hw3
    have hfl3_le : s3.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcore3, hcore2]; exact hfu1
    rw [fullM6HdrMem_iff] at hm3
    let start := s2.scratch.search_ticks
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ md => md = m3) ?_
      (fun _ hJd => by c0_hsteps <;> exact hJd _ m3 rfl)
    rintro _ ⟨delta, ⟨⟩⟩ md hmd; rw [hmd]; c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ me => me = m3) ?_
      (fun _ hJe => by c0_hsteps <;> exact hJe _ m3 rfl)
    rintro _ ⟨eff_ref, ⟨⟩⟩ me hme; rw [hme]; c0_hsteps_nogrp
    · refine wp_join_group (ts := [i64]) (fun _ ml0 => ml0 = m3) ?_
        (fun _ hJl0 => by c0_hsteps <;> exact hJl0 _ m3 rfl)
      rintro _ ⟨lim0, ⟨⟩⟩ ml0 hml0; rw [hml0]
      wac_call hVivTier
      refine m8VivifyTierSpec_of hcfg hext3 hsp3 ((fullM6HdrMem_iff ..).mpr hm3)
        fun r2 ext4 s4 m4 hext4 hw34 hsp4 _ _ hnz2 hfl4 hr2 hu2 hm4 => ?_
      obtain ⟨hcl4, hpr4⟩ := hnz2 hbud
      rw [fullM6HdrMem_iff] at hm4
      c0_hsteps
      let s4' : FullState := { s4 with scratch := { s4.scratch with search_ticks := start } }
      have hsp4' : FullSparseInv c F0 s4' := fullSparseInv_with_ticks_wac hsp4 start
      exact hQ r2 ext4 s4' _ ⟨hext4, ext_pres_compose hpres3 hw34⟩ hsp4' ⟨hcl4, hpr4⟩
        (Nat.le_trans hfl4 hfl3_le) hr2 hu2 ((fullM6HdrMem_iff ..).mpr (by assumption))
    · refine wp_join_group (ts := [i64, i64]) (fun _ mw => mw = m3) ?_
        (fun _ hJw => by c0_hsteps <;> exact hJw _ m3 rfl)
      rintro _ ⟨w1, w2, ⟨⟩⟩ mw hmw; rw [hmw]; c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun _ ml1 => ml1 = m3) ?_
        (fun _ hJl1 => by c0_hsteps <;> exact hJl1 _ m3 rfl)
      rintro _ ⟨lim1, ⟨⟩⟩ ml1 hml1; rw [hml1]
      wac_call hVivTier
      refine m8VivifyTierSpec_of hcfg hext3 hsp3 ((fullM6HdrMem_iff ..).mpr hm3)
        fun res1 ext4 s4 m4 hext4 hw34 hsp4 _ _ hnz4 hfl4 hr1 hu1 hm4 => ?_
      obtain ⟨hcl4, hpr4⟩ := hnz4 hbud
      let TierInv : Tup Val [i64, i64] → Mem 64 → Prop := fun (r, _lim, ()) mk =>
        ∃ extk sk, M6HdrExtOk extk ∧
          (M6HdrExtInitOk ext → M6HdrExtInitOk extk ∧ M6ExtW2bPres ext extk) ∧
          FullSparseInv c F0 sk ∧ sk.core.cur_level = 0 ∧ sk.core.probing = 0#64 ∧
          sk.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat) ∧ (FullM6HdrMem c extk sk ⋆ R) mk
      have hpres4 : M6HdrExtInitOk ext → M6HdrExtInitOk ext4 ∧ M6ExtW2bPres ext ext4 :=
        ext_pres_compose hpres3 hw34
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64, i64]) TierInv ?_ ?_
      · rintro _ ⟨res2, lim2, ⟨⟩⟩ m_t2
          ⟨ext_t2, s_t2, hext_t2, hpres_t2, hsp_t2, hcl_t2, hpr_t2, hfl_t2, hr_t2, hu_t2, hm_t2⟩
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64, i64]) TierInv ?_ ?_
        · rintro _ ⟨res3, lim3, ⟨⟩⟩ m_t3
            ⟨ext_t3, s_t3, hext_t3, hpres_t3, hsp_t3, hcl_t3, hpr_t3, hfl_t3, hr_t3, hu_t3, hm_t3⟩
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64, i64]) TierInv ?_ ?_
          · rintro _ ⟨res0, _lim0, ⟨⟩⟩ m_t0
              ⟨ext_t0, s_t0, hext_t0, hpres_t0, hsp_t0, hcl_t0, hpr_t0, hfl_t0,
                hr_t0, hu_t0, hm_t0⟩
            rw [fullM6HdrMem_iff] at hm_t0
            c0_hsteps
            let s_fin : FullState :=
              { s_t0 with scratch := { s_t0.scratch with search_ticks := start } }
            have hsp_fin : FullSparseInv c F0 s_fin := fullSparseInv_with_ticks_wac hsp_t0 start
            exact hQ res0 ext_t0 s_fin _ ⟨hext_t0, hpres_t0⟩ hsp_fin ⟨hcl_t0, hpr_t0⟩
              hfl_t0 hr_t0 hu_t0 ((fullM6HdrMem_iff ..).mpr (by assumption))
          · intro J0 hJ0; c0_hsteps_nogrp
            · c0_hsteps
              wac_call hDelaying
              refine m6HdrW2aSpec_of rfl hcfg hext_t3 hsp_t3.1.lengths hm_t3
                fun ⟨del, ⟨⟩⟩ ext_d s_d m_d hcore_d hlen_d hsc_d hext_d hw_d hm_d => ?_
              have hsp_d : FullSparseInv c F0 s_d :=
                fullSparseInv_of_core_eq_wac hsp_t3 hlen_d hcore_d hsc_d
              have hcl_d : s_d.core.cur_level = 0 := by rw [hcore_d]; exact hcl_t3
              have hpr_d : s_d.core.probing = 0#64 := by rw [hcore_d]; exact hpr_t3
              have hfl_d : s_d.core.fuel.toNat ≤ s.core.fuel.toNat := by
                rw [hcore_d]; exact hfl_t3
              have hpres_d : M6HdrExtInitOk ext → M6HdrExtInitOk ext_d ∧ M6ExtW2bPres ext ext_d :=
                ext_pres_compose hpres_t3 hw_d
              c0_hsteps_nogrp
              · have h133_mod : (1064#64 : BitVec 64).toNat % 8 = 0 := by decide
                have h133_lt : (1064#64 : BitVec 64).toNat / 8 < ext_d.length := by
                  rw [hext_d.len]; decide
                rw [fullM6HdrMem_iff] at hm_d
                c0_hsteps
                let ext_d' := ext_d.set ((1064#64 : BitVec 64).toNat / 8)
                  (ext_d[(1064#64 : BitVec 64).toNat / 8] + 1#64)
                have hext_d' : M6HdrExtOk ext_d' :=
                  M6HdrExtOk.of_len (by rw [List.length_set, hext_d.len])
                have hpres_d' := ext_pres_set_ge8 (idx := (1064#64 : BitVec 64).toNat / 8)
                  (ext_d[(1064#64 : BitVec 64).toNat / 8] + 1#64) (by decide) hpres_d
                exact hJ0 (res3, lim3, ()) _ ⟨ext_d', s_d, hext_d', hpres_d', hsp_d, hcl_d, hpr_d,
                  hfl_d, hr_t3, hu_t3, (fullM6HdrMem_iff ..).mpr (by assumption)⟩
              · refine wp_join_group (ts := [i64]) (fun _ ml0 => ml0 = m_d) ?_
                  (fun _ hJl0 => by c0_hsteps <;> exact hJl0 _ m_d rfl)
                rintro _ ⟨lim0', ⟨⟩⟩ ml0 hml0; rw [hml0]
                rw [fullM6HdrMem_iff] at hm_d; c0_hsteps_nogrp
                wac_call hVivTier
                refine m8VivifyTierSpec_of hcfg hext_d hsp_d ((fullM6HdrMem_iff ..).mpr hm_d)
                  fun res0 ext0 s_t0 m_t0 hext0 hw0_e hsp_t0 _ _ hnz0 hfl0 hr0 hu0 hm_t0 => ?_
                obtain ⟨hcl0, hpr0⟩ := hnz0 hbud
                have hpres0 : M6HdrExtInitOk ext → M6HdrExtInitOk ext0 ∧ M6ExtW2bPres ext ext0 :=
                  ext_pres_compose hpres_d hw0_e
                have hfl0' : s_t0.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl0 hfl_d
                have h118_mod : (944#64 : BitVec 64).toNat % 8 = 0 := by decide
                have h118_lt : (944#64 : BitVec 64).toNat / 8 < ext0.length := by
                  rw [hext0.len]; decide
                rw [fullM6HdrMem_iff] at hm_t0
                c0_hsteps_nogrp
                refine wp_join_group (ts := [])
                  (fun _ m_f => ∃ ext_f s_f, M6HdrExtOk ext_f ∧
                    (M6HdrExtInitOk ext → M6HdrExtInitOk ext_f ∧ M6ExtW2bPres ext ext_f) ∧
                    FullSparseInv c F0 s_f ∧ s_f.core.cur_level = 0 ∧
                    s_f.core.probing = 0#64 ∧ s_f.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    (FullM6HdrMem c ext_f s_f ⋆ R) m_f) ?_ ?_
                · rintro _ ⟨⟩ m_f
                    ⟨ext_f, s_f, hext_f, hpres_f, hsp_f, hcl_f, hpr_f, hfl_f, hm_f⟩
                  c0_hsteps
                  exact hJ0 (res0, lim0', ()) m_f
                    ⟨ext_f, s_f, hext_f, hpres_f, hsp_f, hcl_f, hpr_f, hfl_f, hr0, hu0, hm_f⟩
                · intro Jv hJv
                  c0_hsteps_nogrp
                  · refine wp_join_group (ts := [i64]) (fun _ my => my = m_t0) ?_
                      (fun _ hJy => by c0_hsteps <;> exact hJy _ m_t0 rfl)
                    rintro _ ⟨y, ⟨⟩⟩ my hmy; subst hmy
                    c0_hsteps
                    · wac_call hBumpDelay
                      refine m6HdrW2aSpec_of rfl hcfg hext0 hsp_t0.1.lengths
                        ((fullM6HdrMem_iff ..).mpr hm_t0)
                        fun () ext_b s_b m_b hcb hlb hscb hext_b hwb hm_b => ?_
                      have hsp_b := fullSparseInv_of_core_eq_wac hsp_t0 hlb hcb hscb
                      c0_hsteps
                      exact hJv () m_b ⟨ext_b, s_b, hext_b, ext_pres_compose hpres0 hwb, hsp_b,
                        by rw [hcb]; exact hcl0, by rw [hcb]; exact hpr0,
                        by change s_b.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hcb]; exact hfl0',
                        hm_b⟩
                    · wac_call hReduceDelay
                      refine m6HdrW2aSpec_of rfl hcfg hext0 hsp_t0.1.lengths
                        ((fullM6HdrMem_iff ..).mpr hm_t0)
                        fun () ext_r s_r m_r hcr hlr hscr hext_r hwr hm_r => ?_
                      have hsp_r := fullSparseInv_of_core_eq_wac hsp_t0 hlr hcr hscr
                      c0_hsteps
                      exact hJv () m_r ⟨ext_r, s_r, hext_r, ext_pres_compose hpres0 hwr, hsp_r,
                        by rw [hcr]; exact hcl0, by rw [hcr]; exact hpr0,
                        by change s_r.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hcr]; exact hfl0',
                        hm_r⟩
                  all_goals
                    exact hJv () m_t0 ⟨ext0, s_t0, hext0, hpres0, hsp_t0, hcl0, hpr0, hfl0',
                      (fullM6HdrMem_iff ..).mpr hm_t0⟩
            · exact hJ0 (res3, lim3, ()) m_t3 ⟨ext_t3, s_t3, hext_t3, hpres_t3, hsp_t3,
                hcl_t3, hpr_t3, hfl_t3, hr_t3, hu_t3, hm_t3⟩
        · intro J3 hJ3; c0_hsteps_nogrp
          · refine wp_join_group (ts := [i64]) (fun _ ml3 => ml3 = m_t2) ?_
              (fun _ hJl3 => by c0_hsteps <;> exact hJl3 _ m_t2 rfl)
            rintro _ ⟨lim3', ⟨⟩⟩ ml3 hml3; rw [hml3]
            wac_call hVivTier
            refine m8VivifyTierSpec_of hcfg hext_t2 hsp_t2 hm_t2
              fun res3 ext_t3 s_t3 m_t3 hext_t3 hw_t3 hsp_t3 _ _ hnz3 hfl3 hr3 hu3 hm_t3 => ?_
            obtain ⟨hcl3, hpr3⟩ := hnz3 hbud
            exact hJ3 (res3, lim3', ()) m_t3
              ⟨ext_t3, s_t3, hext_t3, ext_pres_compose hpres_t2 hw_t3,
                hsp_t3, hcl3, hpr3, Nat.le_trans hfl3 hfl_t2, hr3, hu3, hm_t3⟩
          · exact hJ3 (res2, lim2, ()) m_t2 ⟨ext_t2, s_t2, hext_t2, hpres_t2, hsp_t2,
              hcl_t2, hpr_t2, hfl_t2, hr_t2, hu_t2, hm_t2⟩
      · intro J2 hJ2; c0_hsteps_nogrp
        · refine wp_join_group (ts := [i64]) (fun _ ml2 => ml2 = m4) ?_
            (fun _ hJl2 => by c0_hsteps <;> exact hJl2 _ m4 rfl)
          rintro _ ⟨lim2', ⟨⟩⟩ ml2 hml2; rw [hml2]
          wac_call hVivTier
          refine m8VivifyTierSpec_of hcfg hext4 hsp4 hm4
            fun res2 ext_t2 s_t2 m_t2 hext_t2 hw_t2 hsp_t2 _ _ hnz2 hfl2 hr2 hu2 hm_t2 => ?_
          obtain ⟨hcl2, hpr2⟩ := hnz2 hbud
          exact hJ2 (res2, lim2', ()) m_t2 ⟨ext_t2, s_t2, hext_t2, ext_pres_compose hpres4 hw_t2,
            hsp_t2, hcl2, hpr2, Nat.le_trans hfl2 (Nat.le_trans hfl4 hfl3_le), hr2, hu2, hm_t2⟩
        all_goals
          exact hJ2 (res1, lim1, ()) m4 ⟨ext4, s4, hext4, hpres4, hsp4, hcl4, hpr4,
            Nat.le_trans hfl4 hfl3_le, hr1, hu1, hm4⟩
  · rw [fullM6HdrMem_iff] at hm
    c0_hsteps
    · wac_call hBacktrack
      refine ⟨c, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1.lengths, hclv_lt, hmax_vars_pos,
        hw0.trail_lits_lt, hm,
        fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1
          hlen1 _ _ hcl1 hpres1 _ _ _ hw_bt _ hm1 => ?_⟩
      have hsp1 : FullSparseInv c F0 _ :=
        FullVivTop.FullSparseInv.of_backtrack hsp (Nat.zero_le _) hlen1 hpres1
          (by simpa using hw_bt F0)
      exact hJ () m1 ⟨_, hsp1, by rw [hcl1]; simp, Nat.le_refl _, (fullM6HdrMem_iff ..).mpr hm1⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have h0 : (BitVec.ofNat 64 s.core.cur_level).toNat = 0 := by rw [hc]; rfl
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at h0
      exact hJ () m ⟨s, hsp, hcl0, Nat.le_refl _, (fullM6HdrMem_iff ..).mpr hm⟩

/-- Parametric `Func.wp` proof for `m8_eliminate_m6_body` against `m8EliminateSpec`
(tracking `M8W_BVE_STALL` at word `128` and `M8W_BVE_THROTTLED` at word `119` in `M6HdrExt`). -/
theorem m8_eliminate_m6_wp (Γ : Env)
    (hDticks : ∀ a m Q X, schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hLog10 : ∀ a m Q X, m7Log10Q16Spec a m Q X → Γ "full_log10_q16_m7" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFwd : ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, m3ElimBveSpec a m Q X → Γ "full_elim_bve_m7" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, m8EliminateSpec a m Q X → Func.wp Γ m8_eliminate_m6_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m0 Q X ⟨c, F0, ext, s0, R, rfl, hcfg, hext, hinv0, hcl0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  rw [fullM6HdrMem_iff] at hm0
  unfold Func.wp m8_eliminate_m6_body
  c0_hsteps_nogrp
  wac_call hDticks
  refine ⟨c, s0, array64 (c.hdr - 2304) ext ⋆ R, rfl, hinv0.lengths, hm0, ?_⟩
  intro dticks
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      (FullMem c s1 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m1)
    (fun _ s1 m1 ⟨hinv1, _, hfu1, hm1⟩ => by
      c0_hsteps_nogrp
      wac_call hEnter
      refine ⟨c, F0, s1, array64 (c.hdr - 2304) ext ⋆ R, rfl, hinv1, hm1, ?_⟩
      intro ok s2 m2 hcl2 hfu2 hok_d hfail_s hm2
      c0_hsplit
      · have hden2 : FullDenseInv c F0 s2 := hok_d hc
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
          (fun b => (b, ())) (fun _ => True)
          (fun _ _ _ => by
            c0_hsteps_nogrp
            wac_call hMin; intro fbud _
            c0_hsteps_nogrp
            wac_call hFwd
            refine ⟨c, F0, s2, array64 (c.hdr - 2304) ext ⋆ R, rfl, hden2, hm2, ?_⟩
            intro fs s3 m3 hden3 hcv3 hfu3 _ huf3 hm3
            have hcv2_le := hden2.lengths.core_ok.cur_vars_le
            let s3r : FullState :=
              { s3 with scratch := { s3.scratch with fwd_sub_cnt := s2.scratch.fwd_sub_cnt } }
            have hden3r : FullDenseInv c F0 s3r :=
              fullDenseInv_with_scratch_keep hden3
                { hden3.lengths.scratch_ok with
                  walk_vals_len := hden3.lengths.scratch_ok.walk_vals_len } rfl rfl
            have hfu3r : s3r.core.fuel.toNat ≤ s0.core.fuel.toNat := by
              change s3.core.fuel.toNat ≤ s0.core.fuel.toNat; rw [hfu3]; omega
            c0_hsplit
            · c0_hsteps_nogrp
              wac_call hReb
              refine ⟨c, F0, s3r, array64 (c.hdr - 2304) ext ⋆ R, rfl, hden3r, hm, ?_⟩
              intro _ s4 m4 hsp4 hcl4 hfu4 _ _ hm4
              c0_hsteps!
              exact hQ 20#64 ext s4 _ hext (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) hsp4 hcl4
                (by omega) (Or.inr rfl) (fun _ => huf3 hc) ((fullM6HdrMem_iff ..).mpr hm4)
            · let cv3 := s3r.core.cur_vars
              have hcv3_le : cv3 ≤ c.max_vars := hden3r.lengths.core_ok.cur_vars_le
              have htl3 := hden3r.lengths.scratch_ok.tarjan_mark_len
              c0_hsteps_nogrp
              refine wp_loop_group (ts := [i64])
                (fun rem_t (ti, ()) mt => ∃ tmki : List (BitVec 32),
                  tmki.length = 2 * c.max_vars ∧ ti.toNat ≤ cv3 ∧ rem_t = cv3 - ti.toNat ∧
                  (∀ k < ti.toNat, tmki[k]?.getD 0#32 = 0#32) ∧
                  (FullMem c { s3r with scratch := { s3r.scratch with tarjan_mark := tmki } } ⋆
                    (array64 (c.hdr - 2304) ext ⋆ R)) mt)
                ?_ ?_
              · rintro Lt rem_t ⟨ti, ⟨⟩⟩ mt hLt ⟨tmki, htli, hti_le, rfl, hinit, hmt⟩
                c0_hsplit
                · have hti_lt : ti.toNat < cv3 := by
                    rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                  have hti_b : ti.toNat < tmki.length := by omega
                  have hti1 : (ti + 1#64).toNat = ti.toNat + 1 := by c0_bound
                  c0_hsteps!
                  exact hLt (cv3 - (ti + 1#64).toNat) (ti + 1#64, ()) _ (by omega)
                    ⟨tmki.set ti.toNat 0#32, by simp [htli], by omega, rfl, fun k hk => by
                       rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hti1 ▸ hk)) with h | h
                       · rw [List.getElem?_set_ne (by omega)]; exact hinit k h
                       · subst h; rw [List.getElem?_set_self hti_b, Option.getD_some], hm⟩
                · have hti_eq : ti.toNat = cv3 := by
                    rw [Nat.mod_eq_of_lt (by omega)] at hc
                    change ¬ti.toNat < cv3 at hc; omega
                  rw [hti_eq] at hinit
                  let s3t : FullState :=
                    { s3r with scratch := { s3r.scratch with tarjan_mark := tmki } }
                  have hden3t : FullDenseInv c F0 s3t :=
                    fullDenseInv_with_scratch_keep hden3r
                      { hden3r.lengths.scratch_ok with tarjan_mark_len := htli } rfl rfl
                  have htmk3t : TmkZero s3t := fun v hv => hinit v hv
                  c0_hsteps_nogrp
                  refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                    (fun b => (b, ())) (fun _ => True)
                    (fun _ bve_lim _ => by
                      c0_hsteps_nogrp
                      wac_call hBve
                      refine ⟨c, F0, s3t, array64 (c.hdr - 2304) ext ⋆ R, rfl,
                        hden3t, htmk3t, hmt, ?_⟩
                      intro res s4 m4 hden4 _ hfu4 _ hres_u hm4
                      have hfu4' : s4.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                        dsimp only [s3t, s3r] at hfu4
                        have hfu3' : s3.core.fuel.toNat ≤ s0.core.fuel.toNat := hfu3r
                        omega
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [])
                        (fun () m4t => ∃ ext' elim_lim',
                          M6HdrExtOk ext' ∧
                          (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') ∧
                          (FullMem c { s4 with scratch :=
                            { s4.scratch with elim_limit := elim_lim' } } ⋆
                            (array64 (c.hdr - 2304) ext' ⋆ R)) m4t) ?_ ?_
                      · rintro _ ⟨⟩ m4t ⟨ext', elim_lim', hext', hpres', hm4t⟩
                        let s4t : FullState :=
                          { s4 with scratch := { s4.scratch with elim_limit := elim_lim' } }
                        have hden4t : FullDenseInv c F0 s4t :=
                          fullDenseInv_with_scratch_keep hden4
                            { hden4.lengths.scratch_ok with
                              walk_vals_len := hden4.lengths.scratch_ok.walk_vals_len } rfl rfl
                        wac_call hReb
                        refine ⟨c, F0, s4t, array64 (c.hdr - 2304) ext' ⋆ R, rfl,
                          hden4t, hm4t, ?_⟩
                        intro rr se me hspe hcle hfue _ hue hme
                        let se' : FullState :=
                          { se with scratch :=
                            { se.scratch with fwd_str_cnt := se.scratch.search_ticks } }
                        have hspe' : FullSparseInv c F0 se' :=
                          fullSparseInv_with_scratch_keep hspe
                            { hspe.lengths.scratch_ok with
                              walk_vals_len := hspe.lengths.scratch_ok.walk_vals_len } rfl rfl
                        have hfue' : se'.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                          change se.core.fuel.toNat ≤ s4.core.fuel.toNat at hfue
                          exact Nat.le_trans hfue hfu4'
                        c0_hsteps!
                        · exact hQ 20#64 ext' se' _ hext' hpres' hspe' hcle hfue' (Or.inr rfl)
                            (fun _ => hres_u hc) ((fullM6HdrMem_iff ..).mpr hm)
                        · exact hQ 20#64 ext' se' _ hext' hpres' hspe' hcle hfue' (Or.inr rfl)
                            (fun _ => hue hc) ((fullM6HdrMem_iff ..).mpr hm)
                        · exact hQ 20#64 ext' se' _ hext' hpres' hspe' hcle hfue' (Or.inr rfl)
                            (fun _ => hspe'.inconsistent_unsat hc) ((fullM6HdrMem_iff ..).mpr hm)
                        · exact hQ 1#64 ext' se' _ hext' hpres' hspe' hcle hfue' (Or.inl rfl)
                            (fun h => by cases h) ((fullM6HdrMem_iff ..).mpr hm)
                      · intro Jt hJt
                        have h128_mod : (1024#64 : BitVec 64).toNat % 8 = 0 := by decide
                        have h128_lt : (1024#64 : BitVec 64).toNat / 8 < ext.length := by
                          rw [hext.len]; decide
                        c0_hsteps_nogrp
                        · exact hJt () m4 ⟨ext, s4.scratch.elim_limit, hext,
                            (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩), hm4⟩
                        · refine wp_join_group (ts := [i64]) (fun _ my => my = m4) ?_
                            (fun _ hJy => by c0_hsteps <;> exact hJy _ m4 rfl)
                          rintro _ ⟨y, ⟨⟩⟩ my hmy; rw [hmy]
                          c0_hsteps_nogrp
                          refine wp_join_group (ts := [])
                            (fun _ m_o => ∃ ext' elim_lim', M6HdrExtOk ext' ∧
                              (M6HdrExtInitOk ext →
                                M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') ∧
                              (FullMem c
                                { s4 with scratch := { s4.scratch with elim_limit := elim_lim' } }
                                ⋆ (array64 (c.hdr - 2304) ext' ⋆ R)) m_o) ?_ ?_
                          · rintro _ ⟨⟩ m_o ⟨ext', el', hext', hpres', hm_o⟩
                            exact hJt () m_o ⟨ext', el', hext', hpres', hm_o⟩
                          · intro J_o hJo
                            refine wp_join_group (ts := []) (fun _ m_r => m_r = m4) ?_ ?_
                            · rintro _ ⟨⟩ m_r hm_r; subst hm_r; c0_hsteps
                              · let ext1 := ext.set ((1024#64 : BitVec 64).toNat / 8) 0#64
                                have hext1 : M6HdrExtOk ext1 :=
                                  M6HdrExtOk.of_len (by rw [List.length_set, hext.len])
                                have hpres1 := ext_pres_set_ge8
                                  (idx := (1024#64 : BitVec 64).toNat / 8) 0#64 (by decide)
                                  fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩
                                exact hJo () _ ⟨ext1, s4.scratch.elim_limit, hext1, hpres1,
                                  (by assumption)⟩
                              · exact hJo () m_r ⟨ext, s4.scratch.elim_limit, hext,
                                  (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩), hm4⟩
                            · intro J_r hJr
                              c0_hsteps_nogrp
                              · refine wp_join_group (ts := [i64])
                                  (fun (st, ()) m_st => m_st = m4 ∧ st.toNat ≤ 3) ?_ ?_
                                · rintro _ ⟨st, ⟨⟩⟩ m_st ⟨hst_m, hst_le⟩; rw [hst_m]
                                  have hst_lt64 : st.toNat < 64 := by omega
                                  let ext1 := ext.set ((1024#64 : BitVec 64).toNat / 8) st
                                  have h119_mod : (952#64 : BitVec 64).toNat % 8 = 0 := by decide
                                  have h119_lt : (952#64 : BitVec 64).toNat / 8 < ext1.length := by
                                    rw [List.length_set, hext.len]; decide
                                  c0_hsteps_nogrp
                                  refine wp_join_group (ts := [i64])
                                    (fun _ m_bd =>
                                      (FullMem c s4 ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) m_bd) ?_
                                    (fun _ hJbd => by c0_hsteps <;> exact hJbd _ _ (by assumption))
                                  rintro _ ⟨base_d, ⟨⟩⟩ m_bd hm_bd
                                  c0_hsteps
                                  let ext2 := ext1.set ((952#64 : BitVec 64).toNat / 8)
                                    (ext1[(952#64 : BitVec 64).toNat / 8] + 1#64)
                                  have hext2 : M6HdrExtOk ext2 :=
                                    M6HdrExtOk.of_len (by
                                      rw [List.length_set, List.length_set, hext.len])
                                  have hpres2 := ext_pres_set_ge8
                                    (idx := (952#64 : BitVec 64).toNat / 8)
                                    (ext1[(952#64 : BitVec 64).toNat / 8] + 1#64) (by decide)
                                    (ext_pres_set_ge8 (idx := (1024#64 : BitVec 64).toNat / 8) st
                                      (by decide) fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩)
                                  exact hJo () _ ⟨ext2, _, hext2, hpres2, (by assumption)⟩
                                · intro Jst hJst; c0_hsteps
                                  · exact hJst (3#64, ()) m4 ⟨rfl, by decide⟩
                                  · exact hJst (_, ()) m4 ⟨rfl, by bv_omega⟩
                              all_goals exact hJr () m4 rfl
                        · exact hJt () m4 ⟨ext, s4.scratch.elim_limit, hext,
                            (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩), hm4⟩)
                    (fun Jb hJb => by
                      c0_hsplit
                      · c0_hsteps!; exact hJb _ trivial
                      · c0_hsteps_nogrp; wac_call hMin; intro b _
                        c0_hsteps!; exact hJb b trivial)
              · intro Lt hLt; c0_hsteps!
                exact hLt cv3 (0#64, ()) _
                  ⟨s3r.scratch.tarjan_mark, htl3, Nat.zero_le _, by simp,
                   fun _ h => by simp at h, hm⟩)
          (fun Jfb hJfb => by c0_hsplit <;> (c0_hsteps!; exact hJfb _ trivial))
      · have hsp2 : FullSparseInv c F0 s2 := hfail_s hc
        let s2' : FullState :=
          { s2 with scratch := { s2.scratch with fwd_str_cnt := s2.scratch.search_ticks } }
        have hsp2' : FullSparseInv c F0 s2' :=
          fullSparseInv_with_scratch_keep hsp2
            { hsp2.lengths.scratch_ok with
              walk_vals_len := hsp2.lengths.scratch_ok.walk_vals_len } rfl rfl
        have hfu2' : s2'.core.fuel.toNat ≤ s0.core.fuel.toNat := by
          change s2.core.fuel.toNat ≤ s0.core.fuel.toNat; omega
        c0_hsteps!
        · exact hQ 20#64 ext s2' _ hext (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) hsp2' hcl2 hfu2'
            (Or.inr rfl) (fun _ => hsp2'.inconsistent_unsat hc) ((fullM6HdrMem_iff ..).mpr hm)
        · exact hQ 1#64 ext s2' _ hext (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) hsp2' hcl2 hfu2'
            (Or.inl rfl) (fun h => by cases h) ((fullM6HdrMem_iff ..).mpr hm))
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps!; exact hJ1 s0 m0 ⟨hinv0, hcl0, Nat.le_refl _, hm0⟩
      · c0_hsteps_nogrp
        let s0a : FullState :=
          { s0 with scratch := { s0.scratch with eliminations := s0.scratch.eliminations + 1#64 } }
        have hlen0a : s0a.LengthsOk c :=
          ⟨hinv0.lengths.core_ok,
           { hinv0.lengths.scratch_ok with
             walk_vals_len := hinv0.lengths.scratch_ok.walk_vals_len }⟩
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
          (fun b => (b, ())) (fun _ => True)
          (fun _ arg _ => by
            c0_hsteps_nogrp
            wac_call hLog10
            refine m7Log10Q16Spec_of fun qlog _ _ => ?_
            c0_hsteps_nogrp
            refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
              (fun b => (b, ())) (fun _ => True)
              (fun _ ec _ => by
                c0_hsteps_nogrp
                wac_call hScale
                refine ⟨c, s0a, array64 (c.hdr - 2304) ext ⋆ R, rfl, hlen0a, hm, ?_⟩
                intro delta
                c0_hsteps!
                let s0b : FullState :=
                  { s0a with
                    scratch := { s0a.scratch with elim_limit := s0a.scratch.conflicts + delta } }
                have hinv0b : FullSparseInv c F0 s0b :=
                  fullSparseInv_with_scratch_keep hinv0
                    { hinv0.lengths.scratch_ok with
                      walk_vals_len := hinv0.lengths.scratch_ok.walk_vals_len } rfl rfl
                exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)
              (fun Jec hJec => by c0_hsplit <;> (c0_hsteps!; exact hJec _ trivial)))
          (fun Jarg hJarg => by c0_hsplit <;> (c0_hsteps!; exact hJarg _ trivial)))

/-- Parametric `Func.wp` proof for `full_probe_tail_m6_body` against canonical `m6ProbeTailSpec`
(adaptive `M8_DELAY_BACKBONE` throttling + `M8W_BACKBONE_SKIPS` tracking at word `134`). -/
theorem full_probe_tail_m6_wp (Γ : Env)
    (hDelaying : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hBackbone : ∀ a m Q X, fullBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hBumpDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hReduceDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hTrans : ∀ a m Q X, fullTransitiveFastSpec a m Q X →
      Γ "full_transitive_m6" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m6ProbeTailSpec a m Q X → Func.wp Γ full_probe_tail_m6_body a m Q X := by
  rintro ⟨h, dticks, ⟨⟩⟩ m Q X hs
  rcases m6ProbeTailSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  have h50 : (50#64 : BitVec 64) ≠ 0#64 := by decide
  unfold Func.wp full_probe_tail_m6_body
  refine wp_join_group (ts := [])
    (fun _ m1 => ∃ ext1 s1, FullM6HdrInv c F0 ext1 s1 ∧
      s1.core.cur_level = 0 ∧ s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (FullM6HdrMem c ext1 s1 ⋆ R) m1) ?_ ?_
  · rintro _ _ m1 ⟨ext1, s1, hinv1, hcl1, hfu1, hm1⟩
    refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
    c0_hsteps_nogrp
    · have hnbin : s1.core.num_binary ≠ 0#64 := by c0_bound
      wac_call hTrans
      refine ⟨c, F0, s1, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hinv1.sparse, hm1f,
        fun r2 s2 m2 hsp2 _ _ hnb2 hfu2 hdom2 hu2 hm2 => ?_⟩
      obtain ⟨hcl2, _⟩ := hnb2 hnbin (tr_lim_ne_zero dticks)
      have hinv2 := FullM6HdrInv.mk_inv hinv1.cfgOk hinv1.extOk hsp2
      have hm2' := fullM6HdrMem_unfocus_full hm2
      c0_hsteps_nogrp
      · exact hQ 20#64 ext1 s2 m2 hsp2.lengths hinv2.extOk (Nat.le_trans hfu2 hfu1)
          (Or.inr rfl) (fun _ => hu2 ‹_›) (fun h => by cases h) hm2'
      · exact hQ 1#64 ext1 s2 m2 hsp2.lengths hinv2.extOk (Nat.le_trans hfu2 hfu1)
          (Or.inl rfl) (fun h => by cases h) (fun _ => ⟨hinv2, hcl2⟩) hm2'
    · exact hQ 1#64 ext1 s1 m1 hinv1.sparse.lengths hinv1.extOk hfu1
        (Or.inl rfl) (fun h => by cases h) (fun _ => ⟨hinv1, hcl1⟩) (fullM6HdrMem_unfocus_full hm1f)
  · intro J1 hJ1
    rw [fullM6HdrMem_iff] at hm
    c0_hsteps_nogrp
    · c0_hsteps
      wac_call hDelaying
      refine m6HdrW2aSpec_of rfl hinv.cfgOk hinv.extOk hinv.sparse.lengths
        ((fullM6HdrMem_iff ..).mpr hm)
        fun ⟨del, ⟨⟩⟩ ext_d s_d m_d hcore_d hlen_d hsc_d hext_d _ hm_d => ?_
      have hsp_d := fullSparseInv_of_core_eq_wac hinv.sparse hlen_d hcore_d hsc_d
      have hcl_d : s_d.core.cur_level = 0 := by rw [hcore_d]; exact hcl0
      have hfu_d : s_d.core.fuel.toNat ≤ s.core.fuel.toNat := by
        rw [hcore_d]; exact Nat.le_refl _
      rw [fullM6HdrMem_iff] at hm_d
      c0_hsteps_nogrp
      · have h134_mod : (1072#64 : BitVec 64).toNat % 8 = 0 := by decide
        have h134_lt : (1072#64 : BitVec 64).toNat / 8 < ext_d.length := by rw [hext_d.len]; decide
        c0_hsteps
        let ext_d' := ext_d.set ((1072#64 : BitVec 64).toNat / 8)
          (ext_d[(1072#64 : BitVec 64).toNat / 8] + 1#64)
        have hext_d' : M6HdrExtOk ext_d' :=
          M6HdrExtOk.of_len (by rw [List.length_set, hext_d.len])
        exact hJ1 () _ ⟨ext_d', s_d, FullM6HdrInv.mk_inv hinv.cfgOk hext_d' hsp_d,
          hcl_d, hfu_d, (fullM6HdrMem_iff ..).mpr (by assumption)⟩
      · c0_hsteps_nogrp
        wac_call hBackbone
        refine ⟨c, F0, s_d, array64 (c.hdr - 2304) ext_d ⋆ R, rfl, hsp_d, hm_d,
          fun r1 s1 m1 hsp1 hcl1 _ hfu1 hr1 hu1 hm1 => ?_⟩
        have hfu1' : s1.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfu1 hfu_d
        c0_hsteps_nogrp
        · exact hQ 20#64 ext_d s1 m1 hsp1.lengths hext_d hfu1'
            (Or.inr rfl) (fun _ => hu1 ‹_›) (fun h => by cases h) ((fullM6HdrMem_iff ..).mpr hm1)
        · c0_hsteps
          · wac_call hBumpDelay
            refine m6HdrW2aSpec_of rfl hinv.cfgOk hext_d hsp1.lengths
              ((fullM6HdrMem_iff ..).mpr hm1)
              fun () ext_b s_b m_b hcb hlb hscb hext_b _ hm_b => ?_
            have hsp_b := fullSparseInv_of_core_eq_wac hsp1 hlb hcb hscb
            c0_hsteps
            exact hJ1 () m_b ⟨ext_b, s_b, FullM6HdrInv.mk_inv hinv.cfgOk hext_b hsp_b,
              by rw [hcb]; exact hcl1,
              by change s_b.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hcb]; exact hfu1', hm_b⟩
          all_goals
            wac_call hReduceDelay
            refine m6HdrW2aSpec_of rfl hinv.cfgOk hext_d hsp1.lengths
              ((fullM6HdrMem_iff ..).mpr hm1)
              fun () ext_r s_r m_r hcr hlr hscr hext_r _ hm_r => ?_
            have hsp_r := fullSparseInv_of_core_eq_wac hsp1 hlr hcr hscr
            c0_hsteps
            exact hJ1 () m_r ⟨ext_r, s_r, FullM6HdrInv.mk_inv hinv.cfgOk hext_r hsp_r,
              by rw [hcr]; exact hcl1,
              by change s_r.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hcr]; exact hfu1', hm_r⟩
    · exact hJ1 () m ⟨ext, s, hinv, hcl0, Nat.le_refl _, (fullM6HdrMem_iff ..).mpr hm⟩

end InprocProofs

/-! ## 6. Closed `33`-Row `waveACoreSpecTable`, `ModuleOk`, & `PatchModule` Bridges -/

section ModuleOkSection

/-- Before-host insertion specification row (`m8_log2_q16`, `noExit = true`). -/
def waveACoreBeforeRows : List SpecEntry :=
  [ ⟨"m8_log2_q16", [i64], [i64], m8Log2Q16Spec, true⟩ ]

/-- Replacement specification rows (`10` fns) matching `waveACoreRepls` in exact order. -/
def waveACorePatchRows : List SpecEntry :=
  [ ⟨"full_bump_decay", [i64], [], Full.fullBumpDecaySpec, true⟩
  , ⟨"m6_hdr_recompute_tiers_mode", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_record_used", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_delaying", [i64, i64], [.bool], m6HdrW2aSpec [i64] [.bool], true⟩
  , ⟨"m6_hdr_bump_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"m6_hdr_reduce_delay", [i64, i64], [], m6HdrW2aSpec [i64] [], true⟩
  , ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m8VivifyTierSpec, true⟩
  , ⟨"full_vivify_m6_hdr", [i64], [i64], m6aVivifySpec, true⟩
  , ⟨"full_eliminate_m6", [i64, .bool], [i64], m8EliminateSpec, true⟩
  , ⟨"full_probe_tail_m6", [i64, i64], [i64], m6ProbeTailSpec, true⟩ ]

/-- `PatchModule.patchRows` insertion plan aligned with `waveACoreBefores`. -/
def waveACorePatchBeforeRows : List (Sym × List SpecEntry) :=
  [("full_bump_decay", waveACoreBeforeRows)]

/-- External callee specification rows (`22` externs) matching `waveACoreExterns`. -/
def waveACoreExtRows : List SpecEntry :=
  [ ⟨"full_rescale", [i64], [], Full.fullRescaleSpec, true⟩
  , ⟨"m6_ext_ensure_init", [i64], [], m6ExtEnsureInitSpec, true⟩
  , ⟨"m6_hdr_sync_legacy_tiers", [i64], [], m6HdrW2aSpec [] [], true⟩
  , ⟨"m6_hdr_get_watermark", [i64, i64], [i64], m6HdrW2aSpec [i64] [i64], true⟩
  , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  , ⟨"full_viv_collect_m6", [i64, i64], [i64], fullVivCollectM6Spec, true⟩
  , ⟨"full_viv_count_m6", [i64, i64], [], fullVivCountM6Spec, true⟩
  , ⟨"full_viv_keys_m6", [i64, i64], [], fullVivKeysM6Spec, true⟩
  , ⟨"full_viv_sort_sched_m6", [i64, i64], [], fullVivSortSchedM6Spec, true⟩
  , ⟨"full_viv_clause_m6", [i64, i32], [i64], fullVivClauseM6Spec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullBcpS15Spec, true⟩
  , ⟨"full_viv_clear_tier_m6", [i64, i64], [], fullVivClearTierM6Spec, true⟩
  , ⟨"full_elim_dticks", [i64, .bool], [i64], schedElimDticksSpec, true⟩
  , ⟨"full_log10_q16_m7", [i64], [i64], m7Log10Q16Spec, true⟩
  , ⟨"full_scale_delta", [i64, i64], [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], schedEnterDenseSpec, true⟩
  , ⟨"full_min_u64", [i64, i64], [i64], schedMinU64Spec, true⟩
  , ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩
  , ⟨"full_elim_bve_m7", [i64, i64], [i64], m3ElimBveSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  , ⟨"full_backbone_m6", [i64, i64], [i64], fullBackboneSpec, true⟩
  , ⟨"full_transitive_m6", [i64, i64], [i64], fullTransitiveFastSpec, true⟩ ]

/-- Closed `33`-row specification table for standalone `waveACoreModule` (`11` defined + `22`
externs, all `noExit = true`). -/
def waveACoreSpecTable : List SpecEntry :=
  waveACoreBeforeRows ++ waveACorePatchRows ++ waveACoreExtRows

theorem waveACoreSpecTable_length : waveACoreSpecTable.length = 33 := by rfl

theorem waveACoreSpecTable_sigs :
    waveACoreSpecTable.map (fun e => (e.name, e.as, e.rs)) =
      waveACoreModule.fns.map Fn.sig ++ waveACoreModule.externs.map Extern.sig := by rfl

theorem waveACoreSpecTable_nodup : (waveACoreSpecTable.map SpecEntry.name).Nodup := by
  have heq : waveACoreSpecTable.map SpecEntry.name =
      waveACoreModule.fns.map Fn.name ++ waveACoreModule.externs.map Extern.name := by rfl
  rw [heq]; decide

theorem waveACoreSpecTable_noExit : ∀ e ∈ waveACoreSpecTable, e.noExit = true :=
  fun e he => List.all_eq_true.mp (by rfl : waveACoreSpecTable.all (·.noExit) = true) e he

/-- Closed specification environment for `waveACoreModule`. -/
def waveACoreEnv : Env := Env.ofTable waveACoreSpecTable

theorem waveACoreEnv_noExit : ∀ f as bs xs m Q X X',
    waveACoreEnv f as bs xs m Q X → waveACoreEnv f as bs xs m Q X' :=
  fun _ _ _ _ _ _ _ h => env_ofTable_noExit_all (by rfl) _ _ _ _ _ _ _ h

private theorem waveACoreEnv_row (idx : Nat) (e : SpecEntry)
    (hidx : waveACoreSpecTable[idx]? = some e) (xs : Tup Val e.as) (m : Mem 64) (Q : Post e.rs)
    (X : XPost) (hs : e.eff xs m Q X) : waveACoreEnv e.name e.as e.rs xs m Q X :=
  env_ofTable_row_at hidx waveACoreSpecTable_nodup hs

/-- Generic `TableImpl` bridge over any downstream environment `Γ` for `waveACoreRepls` (`10` fns).
-/
theorem waveACorePatch_tableImpl_of (Γ : Env)
    (hLog2 : ∀ a m Q X, m8Log2Q16Spec a m Q X → Γ "m8_log2_q16" [i64] [i64] a m Q X)
    (hRes : ∀ a m Q X, Full.fullRescaleSpec a m Q X → Γ "full_rescale" [i64] [] a m Q X)
    (hEnsure : ∀ a m Q X, m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X)
    (hSync : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_sync_legacy_tiers" [i64] [] a m Q X)
    (hGetWm : ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hDelaying : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hBumpDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hReduceDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hVivTier : ∀ a m Q X, m8VivifyTierSpec a m Q X →
      Γ "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCollect : ∀ a m Q X, fullVivCollectM6Spec a m Q X →
      Γ "full_viv_collect_m6" [i64, i64] [i64] a m Q X)
    (hCount : ∀ a m Q X, fullVivCountM6Spec a m Q X →
      Γ "full_viv_count_m6" [i64, i64] [] a m Q X)
    (hKeys : ∀ a m Q X, fullVivKeysM6Spec a m Q X →
      Γ "full_viv_keys_m6" [i64, i64] [] a m Q X)
    (hSortSched : ∀ a m Q X, fullVivSortSchedM6Spec a m Q X →
      Γ "full_viv_sort_sched_m6" [i64, i64] [] a m Q X)
    (hVivClause : ∀ a m Q X, fullVivClauseM6Spec a m Q X →
      Γ "full_viv_clause_m6" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullBcpS15Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hClearTier : ∀ a m Q X, fullVivClearTierM6Spec a m Q X →
      Γ "full_viv_clear_tier_m6" [i64, i64] [] a m Q X)
    (hDticks : ∀ a m Q X, schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hLog10 : ∀ a m Q X, m7Log10Q16Spec a m Q X → Γ "full_log10_q16_m7" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFwd : ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, m3ElimBveSpec a m Q X → Γ "full_elim_bve_m7" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hBackbone : ∀ a m Q X, fullBackboneSpec a m Q X →
      Γ "full_backbone_m6" [i64, i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, fullTransitiveFastSpec a m Q X →
      Γ "full_transitive_m6" [i64, i64] [i64] a m Q X) :
    TableImpl Γ waveACoreRepls waveACorePatchRows := by
  unfold waveACoreRepls waveACorePatchRows
  exact
    ⟨ SpecEntry.Impl.of (m8_ae_bump_decay_wp Γ hLog2 hRes)
    , SpecEntry.Impl.of (m8_hdr_recompute_tiers_mode_wp Γ hEnsure hSync)
    , SpecEntry.Impl.of (m8_hdr_record_used_wp Γ hEnsure)
    , SpecEntry.Impl.of (m6_hdr_delaying_wp Γ hEnsure)
    , SpecEntry.Impl.of (m6_hdr_bump_delay_wp Γ hEnsure)
    , SpecEntry.Impl.of (m6_hdr_reduce_delay_wp Γ hEnsure)
    , SpecEntry.Impl.of (full_vivify_tier_m6_hdr_wp Γ hBacktrack hCollect hCount hKeys
        hSortSched hVivClause hProp hClearTier)
    , SpecEntry.Impl.of (full_vivify_m6_hdr_wp Γ hBacktrack hSync hGetWm hDelaying
        hBumpDelay hReduceDelay hVivTier)
    , SpecEntry.Impl.of (m8_eliminate_m6_wp Γ hDticks hLog10 hScale hEnter hMin hFwd hBve hReb)
    , SpecEntry.Impl.of (full_probe_tail_m6_wp Γ hDelaying hBackbone hBumpDelay hReduceDelay hTrans)
    , trivial ⟩

/-- Helper `TableImpl` bridge for `[m8Log2Q16Fn]` (`waveACoreBeforeRows`) over any `Γ`. -/
theorem waveACoreBefore_tableImpl_of (Γ : Env) :
    TableImpl Γ [m8Log2Q16Fn] waveACoreBeforeRows :=
  ⟨SpecEntry.Impl.of (m8_log2_q16_wp Γ), trivial⟩

theorem waveACorePatch_tableImpl :
    TableImpl waveACoreEnv waveACoreRepls waveACorePatchRows := by
  let er := fun i n as rs sp (h : waveACoreSpecTable[i]? = some ⟨n, as, rs, sp, true⟩) =>
    fun a m Q X hs => waveACoreEnv_row i ⟨n, as, rs, sp, true⟩ h a m Q X hs
  let erM := fun i n as rs sp (h : waveACoreSpecTable[i]? = some ⟨n, as, rs, sp, true⟩)
      (hm : ∀ a m Q X, sp a m Q X → sp a m Q (fun _ _ _ _ => False)) =>
    fun a m Q X hs => waveACoreEnv_noExit _ _ _ _ _ _ _ X
      (waveACoreEnv_row i ⟨n, as, rs, sp, true⟩ h a m Q (fun _ _ _ _ => False) (hm a m Q X hs))
  let erW := fun i n ea rs
      (h : waveACoreSpecTable[i]? = some ⟨n, i64 :: ea, rs, m6HdrW2aSpec ea rs, true⟩) =>
    erM i n (i64 :: ea) rs (m6HdrW2aSpec ea rs) h fun _ _ _ _ hs => m6HdrW2aSpec_monoX hs
  exact waveACorePatch_tableImpl_of waveACoreEnv
    (erM 0 _ _ _ _ rfl fun _ _ _ _ hs => m8Log2Q16Spec_monoX hs)
    (er 11 _ _ _ _ rfl)
    (erM 12 _ _ _ _ rfl fun _ _ _ _ hs => m6ExtEnsureInitSpec_monoX hs)
    (erW 13 _ _ _ rfl) (erW 14 _ _ _ rfl) (erW 4 _ _ _ rfl) (erW 5 _ _ _ rfl)
    (erW 6 _ _ _ rfl)
    (erM 7 _ _ _ _ rfl fun _ _ _ _ hs => m8VivifyTierSpec_monoX hs)
    (er 15 _ _ _ _ rfl) (er 16 _ _ _ _ rfl) (er 17 _ _ _ _ rfl) (er 18 _ _ _ _ rfl)
    (er 19 _ _ _ _ rfl) (er 20 _ _ _ _ rfl) (er 21 _ _ _ _ rfl) (er 22 _ _ _ _ rfl)
    (er 23 _ _ _ _ rfl)
    (erM 24 _ _ _ _ rfl fun _ _ _ _ hs => m7Log10Q16Spec_monoX hs)
    (er 25 _ _ _ _ rfl) (er 26 _ _ _ _ rfl) (er 27 _ _ _ _ rfl) (er 28 _ _ _ _ rfl)
    (er 29 _ _ _ _ rfl) (er 30 _ _ _ _ rfl) (er 31 _ _ _ _ rfl) (er 32 _ _ _ _ rfl)

theorem waveACore_tableImpl :
    TableImpl waveACoreEnv waveACoreFns waveACoreSpecTable := by
  change TableImpl waveACoreEnv ([m8Log2Q16Fn] ++ waveACoreRepls)
    (waveACoreBeforeRows ++ (waveACorePatchRows ++ waveACoreExtRows))
  exact tableImpl_append rfl (waveACoreBefore_tableImpl_of waveACoreEnv)
    (tableImpl_append rfl waveACorePatch_tableImpl
      (tableImpl_nil waveACoreEnv waveACoreExtRows))

/-- Closed `ModuleOk` for standalone `waveACoreModule` (`11` functions, `22` externs, `0` exits).
-/
theorem waveACore_moduleOk : ModuleOk waveACoreEnv waveACoreModule :=
  Env.ofTable_moduleOk waveACore_acyclic (allFns_of_mem waveACoreFns_wf) waveACore_tableImpl

theorem waveACorePatchRows_sigs :
    waveACorePatchRows.map (fun e => (e.name, e.as, e.rs)) = waveACoreRepls.map Fn.sig := by rfl

theorem waveACoreBeforeRows_sigs :
    waveACoreBeforeRows.map (fun e => (e.name, e.as, e.rs)) =
      [m8Log2Q16Fn].map Fn.sig := by rfl

theorem waveACorePatchRows_noExit : waveACorePatchRows.all SpecEntry.noExit = true := by rfl

theorem waveACoreBeforeRows_noExit : waveACoreBeforeRows.all SpecEntry.noExit = true := by rfl

end ModuleOkSection

/-! ## 7. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

section ConcreteNonVacuity

private theorem nvWac_unsat : nvOneLitF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have h0 : (cnfClause [0]).Sat α := (CNF.sat_iff_all_mem_sat.mp hα) _
    (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α := (CNF.sat_iff_all_mem_sat.mp hα) _
    (CNF.Internal.mem_iff.mpr (by dsimp only [nvOneLitF0]; simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1; simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

private theorem nvWac_witness_of_bin (nb : BitVec 64) :
    FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]]
      { nvOneLitState.core with num_binary := nb } := by
  let k : FullCoreState := { nvOneLitState.core with num_binary := nb }
  change FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] k
  have hcv : k.cur_vars = 1 := rfl
  have hte : k.trail_end = 1 := rfl
  have hcl : k.cur_level = 0 := rfl
  have hdm : k.dense_mode = 0#64 := rfl
  have hr0 : ∀ r, r ∈ fullArenaClauseRefsCore k → False := fun _ hr => by
    rw [show fullArenaClauseRefsCore k = [] from rfl] at hr; cases hr
  have hi0 : ∀ i, i < k.trail_end → i = 0 := fun _ hi => by rw [hte] at hi; omega
  have hL0 : ∀ L, L ≤ k.cur_level → L = 0 := fun _ hL => by rw [hcl] at hL; omega
  have hwat : ModeWatchesInv [[0], [1]] k := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> exact .empty)
    · rw [hcv] at hl
      change fullWatchOffCore nvOneLitState.core l +
          fullWatchSizeCore nvOneLitState.core l ≤ nvOneLitState.core.wlen
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, k, nvOneLitState] at hp
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        simp [fullWatchSizeCore, k, nvOneLitState] at hp
  have hent0 : (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) :=
    CNF.entails_clause_def.mpr fun _ hα =>
      (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => (hr0 r hr).elim, fun r hr => (hr0 r hr).elim,
        fun r hr => (hr0 r hr).elim, fun r hr => (hr0 r hr).elim⟩
      watches := hwat, cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by
        rw [hi0 i hi]
        change (nvOneLitState.core.trl[0]?.getD 0#32).toNat <
          2 * nvOneLitState.core.cur_vars
        decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hi0 i hi, hi0 j hj]
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [k, nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by rw [hi0 i hi] at h; cases h)⟩
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by rw [hi0 i hi] at h; cases h)⟩
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by
        rw [hi0 i hi]
        change (nvOneLitState.core.lvl[(nvOneLitState.core.trl[0]?.getD 0#32).toNat / 2]?.getD
          0#32).toNat ≤ nvOneLitState.core.cur_level
        decide
      dec_earliest := fun _ j _ hj _ hp => by
        rw [hi0 j hj] at hp
        have hp1 : 0 < (nvOneLitState.core.lvl[(nvOneLitState.core.trl[0]?.getD 0#32).toNat /
          2]?.getD 0#32).toNat := hp.1
        exact absurd hp1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by rw [hi0 i hi]; exact hent0
      trail_pos_inv := fun i hi => by
        rw [hi0 i hi]
        change (nvOneLitState.core.trail_pos[(nvOneLitState.core.trl[0]?.getD 0#32).toNat /
          2]?.getD 0#32).toNat = 0
        decide
      level0_rsn_none := fun i hi _ => by
        rw [hi0 i hi]
        change nvOneLitState.core.rsns[(nvOneLitState.core.trl[0]?.getD 0#32).toNat /
          2]?.getD 4294967295#32 = 4294967295#32
        decide
      frame_trail_lt := fun L hL => by
        rw [hL0 L hL]
        change (nvOneLitState.core.frame_trail[0]?.getD 0#32).toNat ≤
          nvOneLitState.core.trail_end
        decide
      frame_trail_mono := fun L1 L2 h12 hL2 => by
        rw [hL0 L1 (by omega), hL0 L2 hL2]; exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hi0 i hi] at hne
        change nvOneLitState.core.rsns[(nvOneLitState.core.trl[0]?.getD 0#32).toNat /
          2]?.getD 4294967295#32 ≠ 4294967295#32 at hne
        exact absurd (by decide) hne
      reason_lit_mem := fun i hi hne => by
        rw [hi0 i hi] at hne
        change nvOneLitState.core.rsns[(nvOneLitState.core.trl[0]?.getD 0#32).toNat /
          2]?.getD 4294967295#32 ≠ 4294967295#32 at hne
        exact absurd (by decide) hne }

private theorem nvWac_sparse_of_bin (nb : BitVec 64) :
    FullSparseInv nvOneLitCfg nvOneLitF0
      { nvOneLitState with core := { nvOneLitState.core with num_binary := nb } } := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  have hr0 : ∀ r, r ∈ fullArenaClauseRefsCore nvOneLitState.core → False := fun _ hr => by
    rw [show fullArenaClauseRefsCore nvOneLitState.core = [] from rfl] at hr; cases hr
  have hlen : ({ nvOneLitState with core := { nvOneLitState.core with num_binary := nb } } :
      FullState).LengthsOk nvOneLitCfg :=
    ⟨{ nvOneLit_lengths.core_ok with vals_len := nvOneLit_lengths.core_ok.vals_len },
     nvOneLit_lengths.scratch_ok⟩
  refine ⟨⟨hlen, [[0], [1]], nvWac_witness_of_bin nb⟩, ⟨fun v hv => ?_, fun l hl => ?_⟩,
    fun r hr => (hr0 r hr).elim, ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvOneLitState, nvOneLitScratch, List.getElem?_replicate, show i < 16 by omega,
        ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩, rfl⟩
  · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

private theorem nvWac_sparse : FullSparseInv nvOneLitCfg nvOneLitF0 nvOneLitState :=
  nvWac_sparse_of_bin 0#64

private theorem nvWac_hdrMem_emp :
    (FullM6HdrMem nvOneLitCfg nvM6ExtWords nvOneLitState ⋆ emp) nvM6HdrMem := by
  rw [sep_emp]; exact nvM6HdrMem_ok

private theorem nvWac_wp {f : Sym} {as rs : List Ty} {sp : Spec as rs} (idx : Nat)
    (hidx : waveACoreSpecTable[idx]? = some ⟨f, as, rs, sp, true⟩)
    (pre post : List Fn) (fn : Fn)
    (hsplit : waveACoreFns = pre ++ fn :: post) (hname : fn.name = f) (has : fn.as = as)
    (hrs : fn.rs = rs) (body : Func as rs) (hbody : has ▸ hrs ▸ fn.body = body) :
    ∀ (a : Tup Val as) m Q, sp a m Q (fun _ _ _ _ => False) →
      Func.wp waveACoreEnv body a m Q (fun _ _ _ _ => False) := by
  subst has hrs hname hbody
  let ⟨_, _, hwp⟩ := waveACore_moduleOk.fnsOk pre fn post hsplit
  exact fun a m Q hs => hwp a m Q _
    (waveACoreEnv_row idx ⟨fn.name, fn.as, fn.rs, sp, true⟩ hidx a m Q
      (fun _ _ _ _ => False) hs)

/-- Concrete `Mem 64` NV (`XPost := False`) for `m8_log2_q16` on `x = 1#64 <<< 44`. -/
theorem nv_m8_log2_q16_pow44 :
    Func.wp waveACoreEnv m8_log2_q16_body (1#64 <<< 44, ()) nvOneLitMem
      (fun (r, ()) m' => 44 * 65536 ≤ r.toNat ∧ r.toNat < 45 * 65536 ∧ m' = nvOneLitMem)
      (fun _ _ _ _ => False) :=
  nvWac_wp 0 rfl [] (waveACoreFns.drop 1) waveACoreFns[0] rfl rfl rfl rfl
    m8_log2_q16_body rfl _ _ _ fun r _ hr2 => by
      obtain ⟨b, _, _, hlo, hhi, h1, h2, _⟩ := hr2 (by decide)
      have hb44 : b = 44 := by
        have h44 : (1#64 <<< 44).toNat = 2 ^ 44 := by decide
        rw [h44] at hlo hhi
        rcases Nat.lt_trichotomy b 44 with hlt | rfl | hgt
        · have : 2 ^ (b + 1) ≤ 2 ^ 44 := Nat.pow_le_pow_right (by decide) hlt
          omega
        · rfl
        · have : 2 ^ 45 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) hgt
          omega
      subst hb44; exact ⟨h1, h2, rfl⟩

/-- Concrete `Mem 64` heap exercising the AE-bump Q16 Padé `tanh` path (`scinc = 1#64 <<< 44`). -/
def nvAeTanhState : FullState :=
  { nvOneLitState with scratch := { nvOneLitState.scratch with scinc := 1#64 <<< 44 } }

def nvAeTanhMem : Mem 64 :=
  storeMem nvOneLitMem i64 (nvOneLitCfg.hdr + 256) (1#64 <<< 44)

theorem nvAeTanhMem_ok : FullMem nvOneLitCfg nvAeTanhState nvAeTanhMem := by
  have hm0 : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  have hst := (FullArenaTactics.store_full_scinc (1#64 <<< 44) hm0).2
  rw [sep_emp] at hst; exact hst

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) exercising AE-bump Q16 `tanh` (`r_q16 >= 32768`).
-/
theorem nv_m8_bump_decay_tanh :
    Func.wp waveACoreEnv m8_ae_bump_decay_body (nvOneLitCfg.hdr, ()) nvAeTanhMem
      (fun () m' => ∃ s', PreservesCoreSlice FullState.core nvAeTanhState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ FullProbeScratchPres nvAeTanhState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 1 rfl (waveACoreFns.take 1) (waveACoreFns.drop 2) waveACoreFns[1] rfl rfl rfl rfl
    m8_ae_bump_decay_body rfl _ nvAeTanhMem _
    ⟨nvOneLitCfg, nvAeTanhState, emp, rfl,
      nvOneLit_lengths.with_scratch { nvOneLit_lengths.scratch_ok with },
      by rw [sep_emp]; exact nvAeTanhMem_ok,
      fun () s' m' hcore hlen hpr hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hcore, hlen, hpr, nvWac_unsat, hm'⟩⟩

/-- Concrete `Mem 64` heap exercising the AE-bump `inc >= (1ULL << 56)` -> `full_rescale` path. -/
def nvAeRescaleState : FullState :=
  { nvOneLitState with scratch := { nvOneLitState.scratch with scinc := 1#64 <<< 56 } }

def nvAeRescaleMem : Mem 64 :=
  storeMem nvOneLitMem i64 (nvOneLitCfg.hdr + 256) (1#64 <<< 56)

theorem nvAeRescaleMem_ok : FullMem nvOneLitCfg nvAeRescaleState nvAeRescaleMem := by
  have hm0 : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  have hst := (FullArenaTactics.store_full_scinc (1#64 <<< 56) hm0).2
  rw [sep_emp] at hst; exact hst

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) exercising AE-bump `full_rescale(h)`. -/
theorem nv_m8_bump_decay_rescale :
    Func.wp waveACoreEnv m8_ae_bump_decay_body (nvOneLitCfg.hdr, ()) nvAeRescaleMem
      (fun () m' => ∃ s', PreservesCoreSlice FullState.core nvAeRescaleState s' ∧
        s'.LengthsOk nvOneLitCfg ∧ FullProbeScratchPres nvAeRescaleState s' ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 1 rfl (waveACoreFns.take 1) (waveACoreFns.drop 2) waveACoreFns[1] rfl rfl rfl rfl
    m8_ae_bump_decay_body rfl _ nvAeRescaleMem _
    ⟨nvOneLitCfg, nvAeRescaleState, emp, rfl,
      nvOneLit_lengths.with_scratch { nvOneLit_lengths.scratch_ok with },
      by rw [sep_emp]; exact nvAeRescaleMem_ok,
      fun () s' m' hcore hlen hpr hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hcore, hlen, hpr, nvWac_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `64`-bin `m8_hdr_recompute_tiers_mode`. -/
theorem nv_m8_recompute_tiers_mode :
    Func.wp waveACoreEnv m8_hdr_recompute_tiers_mode_body (nvOneLitCfg.hdr, 0#64, ()) nvM6HdrMem
      (fun () m' => ∃ ext' s', s'.LengthsOk nvOneLitCfg ∧ M6HdrExtOk ext' ∧
        nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 2 rfl (waveACoreFns.take 2) (waveACoreFns.drop 3) waveACoreFns[2] rfl rfl rfl rfl
    m8_hdr_recompute_tiers_mode_body rfl _ nvM6HdrMem _
    (m6HdrW2aSpec_of rfl nvM6HdrCfg_ok nvM6ExtWords_ok nvOneLit_lengths nvWac_hdrMem_emp
      fun () ext' s' m' _ hlen' _ hext' _ hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hlen', hext', nvWac_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `m8_hdr_record_used` (64-bin clamp `80#64`).
-/
theorem nv_m8_record_used_clamp64 :
    Func.wp waveACoreEnv m8_hdr_record_used_body (nvOneLitCfg.hdr, 80#64, ()) nvM6HdrMem
      (fun () m' => ∃ ext' s', s'.LengthsOk nvOneLitCfg ∧ M6HdrExtOk ext' ∧
        nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 3 rfl (waveACoreFns.take 3) (waveACoreFns.drop 4) waveACoreFns[3] rfl rfl rfl rfl
    m8_hdr_record_used_body rfl _ nvM6HdrMem _
    (m6HdrW2aSpec_of rfl nvM6HdrCfg_ok nvM6ExtWords_ok nvOneLit_lengths nvWac_hdrMem_emp
      fun () ext' s' m' _ hlen' _ hext' _ hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hlen', hext', nvWac_unsat, hm'⟩)

/-- Initialized M8 `delay[6].cnt = 2` concrete extension words (`M8W_DEL_CNT_BASE + 2 = 122`). -/
def nvM8DelayExt : List (BitVec 64) :=
  (nvM6ExtWords.set 0 fullM6HdrMagic).set 122 2#64

/-- Concrete `Mem 64` image with `M8W_MAGIC` at `e[0]` and `e[122] = 2#64` (`delay[6].cnt = 2`). -/
def nvM8DelayMem : Mem 64 :=
  storeMem (storeMem nvM6HdrMem i64 (nvOneLitCfg.hdr - 2304) fullM6HdrMagic)
    i64 ((nvOneLitCfg.hdr - 2304) + 976#64) 2#64

private theorem nvM8DelayExt_len : nvM8DelayExt.length = 288 := by
  simp [nvM8DelayExt, nvM6ExtWords_len]

theorem nvM8DelayExt_ok : M6HdrExtOk nvM8DelayExt :=
  M6HdrExtOk.of_len nvM8DelayExt_len

theorem nvM8DelayMem_ok : FullM6HdrMem nvOneLitCfg nvM8DelayExt nvOneLitState nvM8DelayMem := by
  have hm0 := (fullM6HdrMem_iff nvOneLitCfg nvM6ExtWords nvOneLitState emp nvM6HdrMem).mp
    nvWac_hdrMem_emp
  have h1 := (M6HdrTactics.store_m6Ext_zero fullM6HdrMagic hm0
    (by rw [nvM6ExtWords_len]; decide)).2
  have h2 := (M6HdrTactics.store_m6Ext_const (k := 976#64) 2#64 h1 (by decide)
    (by rw [List.length_set, nvM6ExtWords_len]; decide)).2
  have hm' := (fullM6HdrMem_iff nvOneLitCfg nvM8DelayExt nvOneLitState emp nvM8DelayMem).mpr h2
  rw [sep_emp] at hm'; exact hm'

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) exercising M8 delay slot `id = 6`. -/
theorem nv_m8_delay_slot6_delaying :
    Func.wp waveACoreEnv m6_hdr_delaying_body (nvOneLitCfg.hdr, 6#64, ()) nvM8DelayMem
      (fun (b, ()) m' => ∃ ext' s', (b = true ∨ b = false) ∧ s'.LengthsOk nvOneLitCfg ∧
        M6HdrExtOk ext' ∧ nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 4 rfl (waveACoreFns.take 4) (waveACoreFns.drop 5) waveACoreFns[4] rfl rfl rfl rfl
    m6_hdr_delaying_body rfl _ nvM8DelayMem _
    (m6HdrW2aSpec_of rfl nvM6HdrCfg_ok nvM8DelayExt_ok nvOneLit_lengths
      (by rw [sep_emp]; exact nvM8DelayMem_ok)
      fun ⟨b, ⟨⟩⟩ ext' s' m' _ hlen _ hext' _ hm' => by
        rw [sep_emp] at hm'
        exact ⟨ext', s', by cases b <;> simp, hlen, hext', nvWac_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) exercising M8 `m6_hdr_bump_delay` (`id = 4`). -/
theorem nv_m8_delay_slot4_bump :
    Func.wp waveACoreEnv m6_hdr_bump_delay_body (nvOneLitCfg.hdr, 4#64, ()) nvM8DelayMem
      (fun () m' => ∃ ext' s', s'.LengthsOk nvOneLitCfg ∧ M6HdrExtOk ext' ∧
        nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 5 rfl (waveACoreFns.take 5) (waveACoreFns.drop 6) waveACoreFns[5] rfl rfl rfl rfl
    m6_hdr_bump_delay_body rfl _ nvM8DelayMem _
    (m6HdrW2aSpec_of rfl nvM6HdrCfg_ok nvM8DelayExt_ok nvOneLit_lengths
      (by rw [sep_emp]; exact nvM8DelayMem_ok)
      fun () ext' s' m' _ hlen' _ hext' _ hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hlen', hext', nvWac_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) exercising M8 `m6_hdr_reduce_delay` (`id = 6`). -/
theorem nv_m8_delay_slot6_reduce :
    Func.wp waveACoreEnv m6_hdr_reduce_delay_body (nvOneLitCfg.hdr, 6#64, ()) nvM8DelayMem
      (fun () m' => ∃ ext' s', s'.LengthsOk nvOneLitCfg ∧ M6HdrExtOk ext' ∧
        nvOneLitF0.Unsat ∧ FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 6 rfl (waveACoreFns.take 6) (waveACoreFns.drop 7) waveACoreFns[6] rfl rfl rfl rfl
    m6_hdr_reduce_delay_body rfl _ nvM8DelayMem _
    (m6HdrW2aSpec_of rfl nvM6HdrCfg_ok nvM8DelayExt_ok nvOneLit_lengths
      (by rw [sep_emp]; exact nvM8DelayMem_ok)
      fun () ext' s' m' _ hlen' _ hext' _ hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hlen', hext', nvWac_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_vivify_tier_m6_hdr`. -/
theorem nv_m8_vivify_tier :
    Func.wp waveACoreEnv full_vivify_tier_m6_hdr_body
      (nvOneLitCfg.hdr, 0#64, 1#64, 100#64, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', M6HdrExtOk ext' ∧ FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 7 rfl (waveACoreFns.take 7) (waveACoreFns.drop 8) waveACoreFns[7] rfl rfl rfl rfl
    full_vivify_tier_m6_hdr_body rfl _ nvM6HdrMem _
    (m8VivifyTierSpec_of nvM6HdrCfg_ok nvM6ExtWords_ok nvWac_sparse nvWac_hdrMem_emp
      fun r ext' s' m' hext' _ hsp' _ _ hnz _ hr hu hm' => by
        rw [sep_emp] at hm'; obtain ⟨hcl, hpr⟩ := hnz (by decide)
        exact ⟨ext', s', hext', hsp', hcl, hpr, hr, hu, hm'⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_vivify_m6_hdr`. -/
theorem nv_m8_vivify :
    Func.wp waveACoreEnv full_vivify_m6_hdr_body (nvOneLitCfg.hdr, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', M6HdrExtOk ext' ∧ FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 8 rfl (waveACoreFns.take 8) (waveACoreFns.drop 9) waveACoreFns[8] rfl rfl rfl rfl
    full_vivify_m6_hdr_body rfl _ nvM6HdrMem _
    (m6aVivifySpec_of nvM6HdrCfg_ok nvM6ExtWords_ok nvWac_sparse nvWac_hdrMem_emp
      fun r ext' s' m' ⟨hext', _⟩ hsp' ⟨hcl', hpr'⟩ _ hr hu hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hext', hsp', hcl', hpr', hr, hu, hm'⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `m8_eliminate_m6` (`initial := true`). -/
theorem nv_m8_eliminate_init :
    Func.wp waveACoreEnv m8_eliminate_m6_body (nvOneLitCfg.hdr, true, ()) nvM6HdrMem
      (fun (r, ()) m' => ∃ ext' s', M6HdrExtOk ext' ∧ FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 9 rfl (waveACoreFns.take 9) (waveACoreFns.drop 10) waveACoreFns[9] rfl rfl rfl rfl
    m8_eliminate_m6_body rfl _ nvM6HdrMem _
    (m8EliminateSpec_of nvM6HdrCfg_ok nvM6ExtWords_ok nvWac_sparse rfl nvWac_hdrMem_emp
      fun r ext' s' m' hext' _ hsp' hcl' _ hr' _ hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hext', hsp', hcl', hr', nvWac_unsat, hm'⟩)

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `m8_eliminate_m6` (`initial := false`,
exercising the M8 `M8W_BVE_STALL`/`M8W_BVE_THROTTLED` inprocessing throttling branch). -/
theorem nv_m8_eliminate_post :
    Func.wp waveACoreEnv m8_eliminate_m6_body (nvOneLitCfg.hdr, false, ()) nvM8DelayMem
      (fun (r, ()) m' => ∃ ext' s', M6HdrExtOk ext' ∧ FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_level = 0 ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 9 rfl (waveACoreFns.take 9) (waveACoreFns.drop 10) waveACoreFns[9] rfl rfl rfl rfl
    m8_eliminate_m6_body rfl _ nvM8DelayMem _
    (m8EliminateSpec_of nvM6HdrCfg_ok nvM8DelayExt_ok nvWac_sparse rfl
      (by rw [sep_emp]; exact nvM8DelayMem_ok)
      fun r ext' s' m' hext' _ hsp' hcl' _ hr' _ hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hext', hsp', hcl', hr', nvWac_unsat, hm'⟩)

/-- Mutated concrete `FullM6HdrMem` state with `num_binary = 1#64` and `delay[6].cnt = 2#64` so
`full_probe_tail_m6` exercises `M8_DELAY_BACKBONE` and `M8W_BACKBONE_SKIPS` (`e[134]`). -/
def nvM8ProbeTailState : FullState :=
  { nvOneLitState with core := { nvOneLitState.core with num_binary := 1#64 } }

def nvM8ProbeTailMem : Mem 64 :=
  storeMem nvM8DelayMem i64 (nvOneLitCfg.hdr + 504) 1#64

theorem nvM8ProbeTailMem_ok :
    FullM6HdrMem nvOneLitCfg nvM8DelayExt nvM8ProbeTailState nvM8ProbeTailMem := by
  have hm_del : (FullM6HdrMem nvOneLitCfg nvM8DelayExt nvOneLitState ⋆ emp) nvM8DelayMem := by
    rw [sep_emp]; exact nvM8DelayMem_ok
  have hm0 := (fullM6HdrMem_iff nvOneLitCfg nvM8DelayExt nvOneLitState emp nvM8DelayMem).mp hm_del
  have h1 := (FullArenaTactics.store_full_num_binary 1#64 hm0).2
  have hm' :=
    (fullM6HdrMem_iff nvOneLitCfg nvM8DelayExt nvM8ProbeTailState emp nvM8ProbeTailMem).mpr h1
  rw [sep_emp] at hm'; exact hm'

/-- Concrete `Mem 64` UNSAT NV (`XPost := False`) for `full_probe_tail_m6` exercising `delay[6]`
and `M8W_BACKBONE_SKIPS` (`e[134]`). -/
theorem nv_m8_probe_tail_delay6 :
    Func.wp waveACoreEnv full_probe_tail_m6_body (nvOneLitCfg.hdr, 100#64, ()) nvM8ProbeTailMem
      (fun (r, ()) m' => ∃ ext' s', (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        (r = 1#64 → FullM6HdrInv nvOneLitCfg nvOneLitF0 ext' s' ∧ s'.core.cur_level = 0) ∧
        FullM6HdrMem nvOneLitCfg ext' s' m')
      (fun _ _ _ _ => False) :=
  nvWac_wp 10 rfl (waveACoreFns.take 10) [] waveACoreFns[10] rfl rfl rfl rfl
    full_probe_tail_m6_body rfl _ nvM8ProbeTailMem _
    (m6ProbeTailSpec_of (FullM6HdrInv.mk_inv nvM6HdrCfg_ok nvM8DelayExt_ok
      (nvWac_sparse_of_bin 1#64)) rfl (by rw [sep_emp]; exact nvM8ProbeTailMem_ok)
      fun r ext' s' m' _ _ _ hr' hu' h1' hm' => by
        rw [sep_emp] at hm'; exact ⟨ext', s', hr', hu', h1', hm'⟩)

end ConcreteNonVacuity

end LeanQbe.T.Examples.Kissat.FullM8WaveACore

end
