module

public import LeanQbe.T.Examples.Kissat.FullM7MemShrinkProof0
public import LeanQbe.T.Examples.Kissat.FullM7MemShrinkProof1
public import LeanQbe.T.Examples.Kissat.FullM7
public import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullArena1
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.Cells
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullM7MemShrink

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullParseInitHelpers
open LeanQbe.T.Examples.Kissat.Full.FullParseInitSpecs
open scoped FullArenaTactics FullParseInitTactics
open Kraken.Bedrock2.Test

public section

/-! ## Prototype A (`151 -> 90 B/var`) Footprint, Zeroing, Init-State & Module Proofs -/

theorem m7FixedBytes_le_full (max_v : Nat) :
    m7FixedBytes max_v ≤ Full.fullFixedBytes max_v := by
  rw [m7FixedBytes_eq]; unfold Full.fullFixedBytes; omega

theorem m7FixedBytes_saving (max_v : Nat) :
    Full.fullFixedBytes max_v - m7FixedBytes max_v =
      2 * valsBytes max_v + markBytes max_v + 56 * max_v := by
  rw [m7FixedBytes_eq]; unfold Full.fullFixedBytes; omega

theorem m7FixedBytes_footprint_eval :
    m7FixedBytes 10000 = 909592 ∧
      Full.fullFixedBytes 10000 = 1519592 ∧
      Full.fullFixedBytes 10000 - m7FixedBytes 10000 = 610000 := by
  simp only [m7FixedBytes_eq]
  decide

theorem full_avail_to_m7 (max_v dyn avail : Nat)
    (h : Full.fullFixedBytes max_v + dyn ≤ avail) :
    m7FixedBytes max_v + m7TransBytes max_v + dyn ≤ avail := by
  have := m7Fixed_plus_trans_le max_v
  omega

private theorem valsBytes_div8 (mv : Nat) : 8 * (valsBytes mv / 8) = valsBytes mv := by
  unfold valsBytes; omega

private theorem markBytes_div8 (mv : Nat) : 8 * (markBytes mv / 8) = markBytes mv := by
  unfold markBytes; omega

private theorem u32FullBytes_div8 (mv : Nat) :
    8 * (Full.u32FullBytes mv / 8) = Full.u32FullBytes mv := by
  unfold Full.u32FullBytes; omega

private theorem bv64_add_ofNat_lt (a : BitVec 64) (n : Nat) (h : a.toNat + n < 2 ^ 64) :
    (a + BitVec.ofNat 64 n).toNat = a.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), Nat.mod_eq_of_lt h]

private theorem hdr_off_eq (hdr off : BitVec 64) (idx : Nat)
    (h : off = 32#64 + BitVec.ofNat 64 (8 * idx)) :
    hdr + off = (hdr + 32) + BitVec.ofNat 64 (8 * idx) := by
  rw [h, BitVec.add_assoc]; rfl

private theorem wp_load_m7Hdr {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {R : Mem 64 → Prop} (c : MemShrinkCfg) (s : FullState)
    (idx : Nat) (hidx : idx < 140) (off : BitVec 64) (v : BitVec 64)
    (hv : (m7HdrTailWords c s)[idx]? = some v)
    (hoff : c.hdr + off = (c.hdr + 32) + BitVec.ofNat 64 (8 * idx))
    (hm : (array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆ R) m)
    {k : Val i64 → Expr Val Cont rs}
    (hk : wp Γ Q X (k v) m) :
    wp Γ Q X (Expr.load i64 (Arg.var (c.hdr + off)) k) m := by
  have hi : idx < (m7HdrTailWords c s).length := by rw [m7HdrTailWords_length]; exact hidx
  have heq : (m7HdrTailWords c s)[idx]'hi = v := by
    simpa [List.getElem?_eq_getElem hi] using hv
  rw [wp_load]
  exact load_array64_step (c.hdr + 32) idx hi hm hoff (by simpa [heq] using hk)

private theorem zt_fill_i8_pad {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec)
    {a : BitVec 64} {xs : List (BitVec 8)} {w used : Nat} {val64 : BitVec 64}
    {v8 : BitVec 8} {R F : Mem 64 → Prop} {m : Mem 64} {k : Tup Val [] → Expr Val Cont rs}
    (hmem : R = ((array (t := i8) a xs ⋆
      region (a + BitVec.ofNat 64 used) (8 * w - used)) ⋆ F))
    (hxs : xs.length = used) (hle : used ≤ 8 * w) (hw : 8 * w ≤ 2 ^ 64)
    (hfit : a.toNat + 8 * w ≤ 2 ^ 64)
    (hbytes : bytes64 [val64] = bytesOf (t := i8) (List.replicate 8 v8))
    (hm : R m)
    (hk : ∀ m', ((array (t := i8) a (List.replicate used v8) ⋆
        region (a + BitVec.ofNat 64 used) (8 * w - used)) ⋆ F) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call "full_fill_u64_m7" (as := [i64, i64, i64]) (bs := [])
      (Arg.var a, Arg.var (BitVec.ofNat 64 w), Arg.imm val64, ()) k) m := by
  rw [hmem] at hm
  obtain ⟨ys, hys, hm64⟩ := array_i8_pad_to_u64 hxs hle hw hm
  refine ⟨fun _ m' => ((array (t := i8) a (List.replicate used v8) ⋆
      region (a + BitVec.ofNat 64 used) (8 * w - used)) ⋆ F) m', X, ?_,
    (fun _ m' hm' => hk m' hm'), fun _ _ _ _ h => h⟩
  rw [envSpec_eq] at hFill
  apply hFill
  rw [m7FillU64Spec_eq]; dsimp only [vals, Arg.val]
  have hw_lt : w < 2 ^ 64 := by omega
  refine ⟨ys, F, by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt, hys],
    by rw [hys]; exact hfit, hm64, fun m1 hm1 => ?_⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt] at hm1
  exact array64_rep_to_i8_pad hle hw hbytes hm1

private theorem zt_fill_i32_pad {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec)
    {a : BitVec 64} {xs : List (BitVec 32)} {w used : Nat} {val64 : BitVec 64}
    {v32 : BitVec 32} {R F : Mem 64 → Prop} {m : Mem 64} {k : Tup Val [] → Expr Val Cont rs}
    (hmem : R = ((array (t := i32) a xs ⋆
      region (a + BitVec.ofNat 64 (4 * used)) (8 * w - 4 * used)) ⋆ F))
    (hxs : xs.length = used) (hle : 4 * used ≤ 8 * w) (hw : 8 * w ≤ 2 ^ 64)
    (hfit : a.toNat + 8 * w ≤ 2 ^ 64)
    (hbytes : bytes64 [val64] = bytesOf (t := i32) (List.replicate 2 v32))
    (hm : R m)
    (hk : ∀ m', ((array (t := i32) a (List.replicate used v32) ⋆
        region (a + BitVec.ofNat 64 (4 * used)) (8 * w - 4 * used)) ⋆ F) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call "full_fill_u64_m7" (as := [i64, i64, i64]) (bs := [])
      (Arg.var a, Arg.var (BitVec.ofNat 64 w), Arg.imm val64, ()) k) m := by
  rw [hmem] at hm
  obtain ⟨ys, hys, hm64⟩ := array_i32_pad_to_u64 hxs hle hw hm
  refine ⟨fun _ m' => ((array (t := i32) a (List.replicate used v32) ⋆
      region (a + BitVec.ofNat 64 (4 * used)) (8 * w - 4 * used)) ⋆ F) m', X, ?_,
    (fun _ m' hm' => hk m' hm'), fun _ _ _ _ h => h⟩
  rw [envSpec_eq] at hFill
  apply hFill
  rw [m7FillU64Spec_eq]; dsimp only [vals, Arg.val]
  have hw_lt : w < 2 ^ 64 := by omega
  refine ⟨ys, F, by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt, hys],
    by rw [hys]; exact hfit, hm64, fun m1 hm1 => ?_⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt] at hm1
  exact array64_rep_to_i32_pad (used := used) (by omega) hw hbytes hm1

private theorem zt_fill_i32_core {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec)
    {a : BitVec 64} {xs : List (BitVec 32)} {w : Nat} {val64 : BitVec 64}
    {wArg valArg : Arg Val i64}
    {v32 : BitVec 32} {R F : Mem 64 → Prop} {m : Mem 64} {k : Tup Val [] → Expr Val Cont rs}
    (hmem : R = (array (t := i32) a xs ⋆ F))
    (hxs : xs.length = 2 * w) (hw : 8 * w ≤ 2 ^ 64) (hfit : a.toNat + 8 * w ≤ 2 ^ 64)
    (hbytes : bytes64 [val64] = bytesOf (t := i32) (List.replicate 2 v32))
    (hwArg : wArg.val = BitVec.ofNat 64 w)
    (hvalArg : valArg.val = val64)
    (hm : R m)
    (hk : ∀ m', (array (t := i32) a (List.replicate (2 * w) v32) ⋆ F) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call "full_fill_u64_m7" (as := [i64, i64, i64]) (bs := [])
      (Arg.var a, wArg, valArg, ()) k) m := by
  rw [hmem] at hm
  obtain ⟨ys, hys, hm64⟩ := array_i32_to_u64_exact hxs hw hm
  refine ⟨fun _ m' => (array (t := i32) a (List.replicate (2 * w) v32) ⋆ F) m', X, ?_,
    (fun _ m' hm' => hk m' hm'), fun _ _ _ _ h => h⟩
  rw [envSpec_eq] at hFill
  apply hFill
  rw [m7FillU64Spec_eq]; dsimp only [vals]; rw [hwArg, hvalArg]
  have hw_lt : w < 2 ^ 64 := by omega
  refine ⟨ys, F, by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt, hys],
    by rw [hys]; exact hfit, hm64, fun m1 hm1 => ?_⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt] at hm1
  exact array64_rep_to_i32_exact hw hbytes hm1

private theorem zt_fill_i32_exact {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec)
    {a : BitVec 64} {xs : List (BitVec 32)} {w : Nat} {val64 : BitVec 64}
    {v32 : BitVec 32} {R F : Mem 64 → Prop} {m : Mem 64} {k : Tup Val [] → Expr Val Cont rs}
    (hmem : R = (array (t := i32) a xs ⋆ F))
    (hxs : xs.length = 2 * w) (hw : 8 * w ≤ 2 ^ 64) (hfit : a.toNat + 8 * w ≤ 2 ^ 64)
    (hbytes : bytes64 [val64] = bytesOf (t := i32) (List.replicate 2 v32))
    (hm : R m)
    (hk : ∀ m', (array (t := i32) a (List.replicate (2 * w) v32) ⋆ F) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call "full_fill_u64_m7" (as := [i64, i64, i64]) (bs := [])
      (Arg.var a, Arg.var (BitVec.ofNat 64 w), Arg.imm val64, ()) k) m :=
  zt_fill_i32_core hFill hmem hxs hw hfit hbytes rfl rfl hm hk

private theorem zt_fill_i32_exact_imm {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec)
    {a : BitVec 64} {xs : List (BitVec 32)} {w : Nat} {val64 : BitVec 64}
    {v32 : BitVec 32} {R F : Mem 64 → Prop} {m : Mem 64} {k : Tup Val [] → Expr Val Cont rs}
    (hmem : R = (array (t := i32) a xs ⋆ F))
    (hxs : xs.length = 2 * w) (hw : 8 * w ≤ 2 ^ 64) (hfit : a.toNat + 8 * w ≤ 2 ^ 64)
    (hbytes : bytes64 [val64] = bytesOf (t := i32) (List.replicate 2 v32))
    (hm : R m)
    (hk : ∀ m', (array (t := i32) a (List.replicate (2 * w) v32) ⋆ F) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call "full_fill_u64_m7" (as := [i64, i64, i64]) (bs := [])
      (Arg.var a, Arg.imm (BitVec.ofNat 64 w), Arg.imm val64, ()) k) m :=
  zt_fill_i32_core hFill hmem hxs hw hfit hbytes rfl rfl hm hk

private theorem zt_fill_u64_exact {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec)
    {a : BitVec 64} {xs : List (BitVec 64)} {w : Nat} {val64 : BitVec 64}
    {R F : Mem 64 → Prop} {m : Mem 64} {k : Tup Val [] → Expr Val Cont rs}
    (hmem : R = (array64 a xs ⋆ F))
    (hxs : xs.length = w) (hw : 8 * w ≤ 2 ^ 64) (hfit : a.toNat + 8 * w ≤ 2 ^ 64)
    (hm : R m)
    (hk : ∀ m', (array64 a (List.replicate w val64) ⋆ F) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (Expr.call "full_fill_u64_m7" (as := [i64, i64, i64]) (bs := [])
      (Arg.var a, Arg.var (BitVec.ofNat 64 w), Arg.imm val64, ()) k) m := by
  rw [hmem] at hm
  refine ⟨fun _ m' => (array64 a (List.replicate w val64) ⋆ F) m', X, ?_,
    (fun _ m' hm' => hk m' hm'), fun _ _ _ _ h => h⟩
  rw [envSpec_eq] at hFill
  apply hFill
  rw [m7FillU64Spec_eq]; dsimp only [vals, Arg.val]
  have hw_lt : w < 2 ^ 64 := by omega
  refine ⟨xs, F, by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt, hxs],
    by rw [hxs]; exact hfit, hm, fun m1 hm1 => ?_⟩
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_lt] using hm1

private theorem m7Cfg_sizes_bound (c : MemShrinkCfg) :
    8 * c.max_vars < 2 ^ 64 ∧ valsBytes c.max_vars < 2 ^ 64 ∧
      markBytes c.max_vars < 2 ^ 64 ∧ Full.u32FullBytes c.max_vars < 2 ^ 64 ∧
      16 * c.max_vars < 2 ^ 64 ∧ 8 * c.minDepth < 2 ^ 64 ∧
      4 * c.arena_cap < 2 ^ 64 ∧ 4 * c.wcap < 2 ^ 64 ∧ 12 * c.delayed_cap < 2 ^ 64 ∧
      4 * c.red_cap < 2 ^ 64 ∧ 4 * c.extend_cap < 2 ^ 64 ∧ 4 * c.scratch_cap < 2 ^ 64 ∧
      m7FixedBytes c.max_vars < 2 ^ 64 ∧ m7TransBytes c.max_vars < 2 ^ 64 := by
  have hm := c.hmaxv; have ha := c.harena; have hw := c.hwcap; have hd := c.hdel
  have hr := c.hred; have he := c.hext; have hs := c.hscr
  rw [m7FixedBytes_eq, m7TransBytes_eq, MemShrinkCfg.minDepth_eq] at *
  unfold Examples.LratBytes.dimacsBound valsBytes markBytes Full.u32FullBytes
    Full.fullMinDepthOf at *
  split <;> omega

private theorem m7Cfg_sum_lt (c : MemShrinkCfg) :
    c.hdr.toNat + 1152 + valsBytes c.max_vars + 4 * markBytes c.max_vars +
      15 * Full.u32FullBytes c.max_vars + 24 * c.max_vars + 8 * c.minDepth + 320 +
      4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap +
      4 * c.extend_cap + 4 * c.scratch_cap + 56 * c.max_vars +
      valsBytes c.max_vars < 2 ^ 64 := by
  have hs := c.hsize; have hf := c.havail_fit
  rw [m7FixedBytes_eq, m7TransBytes_eq, ← MemShrinkCfg.minDepth_eq] at hs
  omega

private theorem bv64_mul_step {x : BitVec 64} {base d k n bound : Nat}
    (hx : x.toNat = base + k * d) (hk : k < n) (hb : base + n * d < bound)
    (ht : bound ≤ 2 ^ 64) :
    (x + BitVec.ofNat 64 d).toNat = base + (k + 1) * d := by
  have hmul : (k + 1) * d ≤ n * d := Nat.mul_le_mul_right d hk
  have hkd : k * d + d = (k + 1) * d := by rw [Nat.add_mul, Nat.one_mul]
  have hlt : x.toNat + d < 2 ^ 64 := by omega
  rw [bv64_add_ofNat_lt x d hlt, hx, Nat.add_assoc, hkd]

private theorem step_r {x : BitVec 64} {prev d tail : Nat}
    (hx : x.toNat = prev) (h : prev + (d + tail) < 2 ^ 64) :
    (x + BitVec.ofNat 64 d).toNat = prev + d ∧ (prev + d) + tail < 2 ^ 64 := by
  have hlt : x.toNat + d < 2 ^ 64 := by omega
  exact ⟨by rw [bv64_add_ofNat_lt x d hlt, hx], by omega⟩

private theorem m7Cfg_end_le (c : MemShrinkCfg) :
    c.hdr.toNat + m7FixedBytes c.max_vars + 4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap +
      4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + m7TransBytes c.max_vars +
      c.slack < 2 ^ 64 := by
  have hs := c.hsize; have hf := c.havail_fit; rw [MemShrinkCfg.slack_eq]; omega

private theorem m7Cfg_pVals_nat (c : MemShrinkCfg) :
    c.pVals.toNat = c.hdr.toNat + 1152 := by
  have h := m7Cfg_sum_lt c; rw [MemShrinkCfg.pVals_eq]
  exact bv64_add_ofNat_lt c.hdr 1152 (by omega)

private theorem m7Cfg_pMark_nat (c : MemShrinkCfg) :
    c.pMark.toNat = c.pVals.toNat + valsBytes c.max_vars := by
  have h := m7Cfg_sum_lt c; have pv := m7Cfg_pVals_nat c
  rw [MemShrinkCfg.pMark_eq]; exact bv64_add_ofNat_lt c.pVals _ (by omega)

private theorem m7Cfg_pPhases_nat (c : MemShrinkCfg) :
    c.pPhases.toNat = c.pMark.toNat + markBytes c.max_vars := by
  have h := m7Cfg_sum_lt c; have pv := m7Cfg_pVals_nat c; have pm := m7Cfg_pMark_nat c
  rw [MemShrinkCfg.pPhases_eq]; exact bv64_add_ofNat_lt c.pMark _ (by omega)

private theorem m7Cfg_pPhasesTarget_nat (c : MemShrinkCfg) :
    c.pPhasesTarget.toNat = c.pPhases.toNat + markBytes c.max_vars := by
  have h := m7Cfg_sum_lt c; have pv := m7Cfg_pVals_nat c; have pm := m7Cfg_pMark_nat c
  have pph := m7Cfg_pPhases_nat c; rw [MemShrinkCfg.pPhasesTarget_eq]
  exact bv64_add_ofNat_lt c.pPhases _ (by omega)

private theorem m7Cfg_pPhasesBest_nat (c : MemShrinkCfg) :
    c.pPhasesBest.toNat = c.pPhasesTarget.toNat + markBytes c.max_vars := by
  have h := m7Cfg_sum_lt c; have pv := m7Cfg_pVals_nat c; have pm := m7Cfg_pMark_nat c
  have pph := m7Cfg_pPhases_nat c; have ppt := m7Cfg_pPhasesTarget_nat c
  rw [MemShrinkCfg.pPhasesBest_eq]; exact bv64_add_ofNat_lt c.pPhasesTarget _ (by omega)

private theorem m7Cfg_pFlags_nat (c : MemShrinkCfg) :
    c.pFlags.toNat = c.pPhasesBest.toNat + markBytes c.max_vars := by
  have h := m7Cfg_sum_lt c; have pv := m7Cfg_pVals_nat c; have pm := m7Cfg_pMark_nat c
  have pph := m7Cfg_pPhases_nat c; have ppt := m7Cfg_pPhasesTarget_nat c
  have ppb := m7Cfg_pPhasesBest_nat c; rw [MemShrinkCfg.pFlags_eq]
  exact bv64_add_ofNat_lt c.pPhasesBest _ (by omega)

private theorem m7Cfg_pFlags_eq_hdr (c : MemShrinkCfg) :
    c.pFlags.toNat = c.hdr.toNat + 1152 + valsBytes c.max_vars + 4 * markBytes c.max_vars := by
  have pv := m7Cfg_pVals_nat c; have pm := m7Cfg_pMark_nat c; have pph := m7Cfg_pPhases_nat c
  have ppt := m7Cfg_pPhasesTarget_nat c; have ppb := m7Cfg_pPhasesBest_nat c
  have pfl := m7Cfg_pFlags_nat c; omega

private theorem m7Cfg_u32_chain_nat (c : MemShrinkCfg) :
    c.pLevel.toNat = c.pFlags.toNat + Full.u32FullBytes c.max_vars ∧
      c.pReason.toNat = c.pLevel.toNat + Full.u32FullBytes c.max_vars ∧
      c.pTrail.toNat = c.pReason.toNat + Full.u32FullBytes c.max_vars ∧
      c.pTrailPos.toNat = c.pTrail.toNat + Full.u32FullBytes c.max_vars ∧
      c.pTmp.toNat = c.pTrailPos.toNat + Full.u32FullBytes c.max_vars ∧
      c.pHeap.toNat = c.pTmp.toNat + Full.u32FullBytes c.max_vars ∧
      c.pPos.toNat = c.pHeap.toNat + Full.u32FullBytes c.max_vars ∧
      c.pMinClr.toNat = c.pPos.toNat + Full.u32FullBytes c.max_vars ∧
      c.pShrinkStk.toNat = c.pMinClr.toNat + Full.u32FullBytes c.max_vars ∧
      c.pQPrev.toNat = c.pShrinkStk.toNat + Full.u32FullBytes c.max_vars ∧
      c.pQNext.toNat = c.pQPrev.toNat + Full.u32FullBytes c.max_vars ∧
      c.pQStamp.toNat = c.pQNext.toNat + Full.u32FullBytes c.max_vars ∧
      c.pFrameTrail.toNat = c.pQStamp.toNat + Full.u32FullBytes c.max_vars ∧
      c.pFrameDec.toNat = c.pFrameTrail.toNat + Full.u32FullBytes c.max_vars ∧
      c.pWvec.toNat = c.pFrameDec.toNat + Full.u32FullBytes c.max_vars := by
  have hub : c.pFlags.toNat + 15 * Full.u32FullBytes c.max_vars < 2 ^ 64 := by
    have hfl := m7Cfg_pFlags_eq_hdr c; have hs := m7Cfg_sum_lt c; omega
  have a0 : c.pFlags.toNat = c.pFlags.toNat + 0 * Full.u32FullBytes c.max_vars := by simp
  have a1 : c.pLevel.toNat = c.pFlags.toNat + 1 * Full.u32FullBytes c.max_vars := by
    rw [MemShrinkCfg.pLevel_eq]; exact bv64_mul_step a0 (by decide : 0 < 15) hub (le_refl _)
  have a2 : c.pReason.toNat = c.pFlags.toNat + 2 * Full.u32FullBytes c.max_vars := by
    rw [MemShrinkCfg.pReason_eq]; exact bv64_mul_step a1 (by decide : 1 < 15) hub (le_refl _)
  have a3 : c.pTrail.toNat = c.pFlags.toNat + 3 * Full.u32FullBytes c.max_vars := by
    rw [MemShrinkCfg.pTrail_eq]; exact bv64_mul_step a2 (by decide : 2 < 15) hub (le_refl _)
  have a4 : c.pTrailPos.toNat = c.pFlags.toNat + 4 * Full.u32FullBytes c.max_vars := by
    rw [MemShrinkCfg.pTrailPos_eq]; exact bv64_mul_step a3 (by decide : 3 < 15) hub (le_refl _)
  have a5 : c.pTmp.toNat = c.pFlags.toNat + 5 * Full.u32FullBytes c.max_vars := by
    rw [MemShrinkCfg.pTmp_eq]; exact bv64_mul_step a4 (by decide : 4 < 15) hub (le_refl _)
  have a6 : c.pHeap.toNat = c.pFlags.toNat + 6 * Full.u32FullBytes c.max_vars := by
    rw [MemShrinkCfg.pHeap_eq]; exact bv64_mul_step a5 (by decide : 5 < 15) hub (le_refl _)
  have a7 : c.pPos.toNat = c.pFlags.toNat + 7 * Full.u32FullBytes c.max_vars := by
    rw [MemShrinkCfg.pPos_eq]; exact bv64_mul_step a6 (by decide : 6 < 15) hub (le_refl _)
  have a8 : c.pMinClr.toNat = c.pFlags.toNat + 8 * Full.u32FullBytes c.max_vars := by
    rw [MemShrinkCfg.pMinClr_eq]; exact bv64_mul_step a7 (by decide : 7 < 15) hub (le_refl _)
  have a9 : c.pShrinkStk.toNat = c.pFlags.toNat + 9 * Full.u32FullBytes c.max_vars := by
    rw [MemShrinkCfg.pShrinkStk_eq]; exact bv64_mul_step a8 (by decide : 8 < 15) hub (le_refl _)
  have a10 : c.pQPrev.toNat = c.pFlags.toNat + 10 * Full.u32FullBytes c.max_vars := by
    rw [MemShrinkCfg.pQPrev_eq]; exact bv64_mul_step a9 (by decide : 9 < 15) hub (le_refl _)
  have a11 : c.pQNext.toNat = c.pFlags.toNat + 11 * Full.u32FullBytes c.max_vars := by
    rw [MemShrinkCfg.pQNext_eq]; exact bv64_mul_step a10 (by decide : 10 < 15) hub (le_refl _)
  have a12 : c.pQStamp.toNat = c.pFlags.toNat + 12 * Full.u32FullBytes c.max_vars := by
    rw [MemShrinkCfg.pQStamp_eq]; exact bv64_mul_step a11 (by decide : 11 < 15) hub (le_refl _)
  have a13 : c.pFrameTrail.toNat = c.pFlags.toNat + 13 * Full.u32FullBytes c.max_vars := by
    rw [MemShrinkCfg.pFrameTrail_eq]; exact bv64_mul_step a12 (by decide : 12 < 15) hub (le_refl _)
  have a14 : c.pFrameDec.toNat = c.pFlags.toNat + 14 * Full.u32FullBytes c.max_vars := by
    rw [MemShrinkCfg.pFrameDec_eq]; exact bv64_mul_step a13 (by decide : 13 < 15) hub (le_refl _)
  have a15 : c.pWvec.toNat = c.pFlags.toNat + 15 * Full.u32FullBytes c.max_vars := by
    rw [MemShrinkCfg.pWvec_eq]; exact bv64_mul_step a14 (by decide : 14 < 15) hub (le_refl _)
  refine ⟨by rw [a1, Nat.one_mul], by rw [a2, a1]; omega, by rw [a3, a2]; omega,
    by rw [a4, a3]; omega, by rw [a5, a4]; omega, by rw [a6, a5]; omega,
    by rw [a7, a6]; omega, by rw [a8, a7]; omega, by rw [a9, a8]; omega,
    by rw [a10, a9]; omega, by rw [a11, a10]; omega, by rw [a12, a11]; omega,
    by rw [a13, a12]; omega, by rw [a14, a13]; omega, by rw [a15, a14]; omega⟩

private theorem m7Cfg_pWvec_eq_hdr (c : MemShrinkCfg) :
    c.pWvec.toNat = c.hdr.toNat + 1152 + valsBytes c.max_vars + 4 * markBytes c.max_vars +
      15 * Full.u32FullBytes c.max_vars := by
  have hfl := m7Cfg_pFlags_eq_hdr c
  rcases m7Cfg_u32_chain_nat c with
    ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15⟩
  rw [u15, u14, u13, u12, u11, u10, u9, u8, u7, u6, u5, u4, u3, u2, u1, hfl]
  clear hfl u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15
  omega

private theorem m7Cfg_tail_chain_nat (c : MemShrinkCfg) :
    c.pScore.toNat = c.pWvec.toNat + 16 * c.max_vars ∧
      c.pMinStk.toNat = c.pScore.toNat + 8 * c.max_vars ∧
      c.pGlueUsed.toNat = c.pMinStk.toNat + 8 * c.minDepth ∧
      c.pLastLearned.toNat = c.pGlueUsed.toNat + 256 ∧
      c.pArena.toNat = c.pLastLearned.toNat + 64 ∧
      c.pWstk.toNat = c.pArena.toNat + 4 * c.arena_cap ∧
      c.pDelayed.toNat = c.pWstk.toNat + 4 * c.wcap ∧
      c.pRedRefs.toNat = c.pDelayed.toNat + 12 * c.delayed_cap ∧
      c.pExtendStk.toNat = c.pRedRefs.toNat + 4 * c.red_cap ∧
      c.pScratchBuf.toNat = c.pExtendStk.toNat + 4 * c.extend_cap ∧
      c.pTrans.toNat = c.pScratchBuf.toNat + 4 * c.scratch_cap ∧
      c.pLitMark.toNat = c.pTrans.toNat + 56 * c.max_vars ∧
      c.pLitMark.toNat + valsBytes c.max_vars ≤ c.hdr.toNat + c.avail := by
  have hwv := m7Cfg_pWvec_eq_hdr c
  have h0 : c.pWvec.toNat + (16 * c.max_vars + (8 * c.max_vars + (8 * c.minDepth + (256 +
      (64 + (4 * c.arena_cap + (4 * c.wcap + (12 * c.delayed_cap + (4 * c.red_cap +
      (4 * c.extend_cap + (4 * c.scratch_cap + (56 * c.max_vars + valsBytes c.max_vars)))))))))))) <
      2 ^ 64 := by
    have hs := m7Cfg_sum_lt c; omega
  obtain ⟨q1, h1⟩ := step_r (rfl : c.pWvec.toNat = c.pWvec.toNat) h0
  rw [← MemShrinkCfg.pScore_eq] at q1
  obtain ⟨q2, h2⟩ := step_r q1 h1; rw [← MemShrinkCfg.pMinStk_eq] at q2
  obtain ⟨q3, h3⟩ := step_r q2 h2; rw [← MemShrinkCfg.pGlueUsed_eq] at q3
  obtain ⟨q4, h4⟩ := step_r q3 h3; rw [← MemShrinkCfg.pLastLearned_eq] at q4
  obtain ⟨q5, h5⟩ := step_r q4 h4; rw [← MemShrinkCfg.pArena_eq] at q5
  obtain ⟨q6, h6⟩ := step_r q5 h5; rw [← MemShrinkCfg.pWstk_eq] at q6
  obtain ⟨q7, h7⟩ := step_r q6 h6; rw [← MemShrinkCfg.pDelayed_eq] at q7
  obtain ⟨q8, h8⟩ := step_r q7 h7; rw [← MemShrinkCfg.pRedRefs_eq] at q8
  obtain ⟨q9, h9⟩ := step_r q8 h8; rw [← MemShrinkCfg.pExtendStk_eq] at q9
  obtain ⟨q10, h10⟩ := step_r q9 h9; rw [← MemShrinkCfg.pScratchBuf_eq] at q10
  obtain ⟨q11, h11⟩ := step_r q10 h10; rw [← MemShrinkCfg.pTrans_eq] at q11
  have htr_hub : c.pTrans.toNat + (56 * c.max_vars + valsBytes c.max_vars) < 2 ^ 64 := by
    rw [q11]; exact h11
  have htr7 : c.pTrans.toNat + 7 * (8 * c.max_vars) < 2 ^ 64 := by
    have h78 : 7 * (8 * c.max_vars) = 56 * c.max_vars := (Nat.mul_assoc 7 8 c.max_vars).symm
    rw [h78]; exact Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_right _ _) _) htr_hub
  have m0 : c.pTrans.toNat = c.pTrans.toNat + 0 * (8 * c.max_vars) := by simp
  have m1 : c.pWorkStk1.toNat = c.pTrans.toNat + 1 * (8 * c.max_vars) := by
    rw [MemShrinkCfg.pWorkStk1_eq]; exact bv64_mul_step m0 (by decide : 0 < 7) htr7 (le_refl _)
  have m2 : c.pWorkStk2.toNat = c.pTrans.toNat + 2 * (8 * c.max_vars) := by
    rw [MemShrinkCfg.pWorkStk2_eq]; exact bv64_mul_step m1 (by decide : 1 < 7) htr7 (le_refl _)
  have m3 : c.pTarjanMark.toNat = c.pTrans.toNat + 3 * (8 * c.max_vars) := by
    rw [MemShrinkCfg.pTarjanMark_eq]; exact bv64_mul_step m2 (by decide : 2 < 7) htr7 (le_refl _)
  have m4 : c.pTarjanReach.toNat = c.pTrans.toNat + 4 * (8 * c.max_vars) := by
    rw [MemShrinkCfg.pTarjanReach_eq]; exact bv64_mul_step m3 (by decide : 3 < 7) htr7 (le_refl _)
  have m5 : c.pRepr.toNat = c.pTrans.toNat + 5 * (8 * c.max_vars) := by
    rw [MemShrinkCfg.pRepr_eq]; exact bv64_mul_step m4 (by decide : 4 < 7) htr7 (le_refl _)
  have m6 : c.pSimSig.toNat = c.pTrans.toNat + 6 * (8 * c.max_vars) := by
    rw [MemShrinkCfg.pSimSig_eq]; exact bv64_mul_step m5 (by decide : 5 < 7) htr7 (le_refl _)
  have m7 : c.pLitMark.toNat = c.pTrans.toNat + 7 * (8 * c.max_vars) := by
    rw [MemShrinkCfg.pLitMark_eq]; exact bv64_mul_step m6 (by decide : 6 < 7) htr7 (le_refl _)
  have rlm : c.pLitMark.toNat = c.pTrans.toNat + 56 * c.max_vars := by
    rw [m7, ← Nat.mul_assoc]
  have h_av := c.hsize
  rw [m7FixedBytes_eq, m7TransBytes_eq, ← MemShrinkCfg.minDepth_eq] at h_av
  have hlit_le : c.pLitMark.toNat + valsBytes c.max_vars ≤ c.hdr.toNat + c.avail := by
    rw [rlm, q11, hwv]
    clear m0 m1 m2 m3 m4 m5 m6 m7 h0 q1 h1 q2 h2 q3 h3 q4 h4 q5 h5 q6 h6
    clear q7 h7 q8 h8 q9 h9 q10 h10 q11 h11 htr_hub htr7 rlm hwv
    omega
  refine ⟨q1, q1 ▸ q2, q2 ▸ q3, q3 ▸ q4, q4 ▸ q5, q5 ▸ q6, q6 ▸ q7, q7 ▸ q8,
    q8 ▸ q9, q9 ▸ q10, q10 ▸ q11, rlm, hlit_le⟩

private theorem m7Cfg_ptrs_fit (c : MemShrinkCfg) :
    c.pVals.toNat + valsBytes c.max_vars < 2 ^ 64 ∧
      c.pMark.toNat + markBytes c.max_vars < 2 ^ 64 ∧
      c.pPhases.toNat + markBytes c.max_vars < 2 ^ 64 ∧
      c.pPhasesTarget.toNat + markBytes c.max_vars < 2 ^ 64 ∧
      c.pPhasesBest.toNat + markBytes c.max_vars < 2 ^ 64 ∧
      c.pFlags.toNat + Full.u32FullBytes c.max_vars < 2 ^ 64 ∧
      c.pLevel.toNat + Full.u32FullBytes c.max_vars < 2 ^ 64 ∧
      c.pReason.toNat + Full.u32FullBytes c.max_vars < 2 ^ 64 ∧
      c.pHeap.toNat + Full.u32FullBytes c.max_vars < 2 ^ 64 ∧
      c.pPos.toNat + Full.u32FullBytes c.max_vars < 2 ^ 64 ∧
      c.pQPrev.toNat + Full.u32FullBytes c.max_vars < 2 ^ 64 ∧
      c.pQNext.toNat + Full.u32FullBytes c.max_vars < 2 ^ 64 ∧
      c.pQStamp.toNat + Full.u32FullBytes c.max_vars < 2 ^ 64 ∧
      c.pFrameTrail.toNat + Full.u32FullBytes c.max_vars < 2 ^ 64 ∧
      c.pFrameDec.toNat + Full.u32FullBytes c.max_vars < 2 ^ 64 ∧
      c.pWvec.toNat + 16 * c.max_vars < 2 ^ 64 ∧
      c.pScore.toNat + 8 * c.max_vars < 2 ^ 64 ∧
      c.pMinStk.toNat + 8 * c.minDepth < 2 ^ 64 ∧
      c.pGlueUsed.toNat + 256 < 2 ^ 64 ∧
      c.pLastLearned.toNat + 64 < 2 ^ 64 ∧
      c.pLitMark.toNat + valsBytes c.max_vars < 2 ^ 64 := by
  have hf := c.havail_fit
  have pm := m7Cfg_pMark_nat c; have pph := m7Cfg_pPhases_nat c
  have ppt := m7Cfg_pPhasesTarget_nat c; have ppb := m7Cfg_pPhasesBest_nat c
  have pfl := m7Cfg_pFlags_nat c
  rcases m7Cfg_u32_chain_nat c with
    ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15⟩
  rcases m7Cfg_tail_chain_nat c with
    ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, hlm, hfit⟩
  exact ⟨pm ▸ c.pMark.isLt, pph ▸ c.pPhases.isLt, ppt ▸ c.pPhasesTarget.isLt,
    ppb ▸ c.pPhasesBest.isLt, pfl ▸ c.pFlags.isLt, u1 ▸ c.pLevel.isLt,
    u2 ▸ c.pReason.isLt, u3 ▸ c.pTrail.isLt, u7 ▸ c.pPos.isLt,
    u8 ▸ c.pMinClr.isLt, u11 ▸ c.pQNext.isLt, u12 ▸ c.pQStamp.isLt,
    u13 ▸ c.pFrameTrail.isLt, u14 ▸ c.pFrameDec.isLt, u15 ▸ c.pWvec.isLt,
    t1 ▸ c.pScore.isLt, t2 ▸ c.pMinStk.isLt, t3 ▸ c.pGlueUsed.isLt,
    t4 ▸ c.pLastLearned.isLt, t5 ▸ c.pArena.isLt, Nat.lt_of_le_of_lt hfit hf⟩

private def m7RestFrame (c : MemShrinkCfg) (s : FullState) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
    array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆ MemShrinkTransRegions c ⋆
    region c.pSlack c.slack ⋆ R

private theorem memShrink_frame_hdr (c : MemShrinkCfg) (s : FullState) (R : Mem 64 → Prop) :
    (MemShrinkMem c s ⋆ R) =
      (array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆
        (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
          s.core.d_cur s.core.d_val ⋆ MemShrinkResArrays c s ⋆ MemShrinkLitMark c s ⋆
          MemShrinkTransRegions c ⋆ region c.pSlack c.slack ⋆ R)) := by
  rw [MemShrinkMem_eq]; ac_rfl

private theorem memShrink_frame_resBytes (c : MemShrinkCfg) (s : FullState) (R : Mem 64 → Prop) :
    (MemShrinkMem c s ⋆ R) =
      (MemShrinkResBytes c s ⋆
        (MemShrinkResU32A c s ⋆ MemShrinkResU32B c s ⋆ MemShrinkResTail c s ⋆
          MemShrinkLitMark c s ⋆ m7RestFrame c s R)) := by
  rw [MemShrinkMem_eq, MemShrinkResArrays_eq]; unfold m7RestFrame; ac_rfl

private theorem memShrink_frame_resTail (c : MemShrinkCfg) (s : FullState) (R : Mem 64 → Prop) :
    (MemShrinkMem c s ⋆ R) =
      (MemShrinkResTail c s ⋆
        (MemShrinkResBytes c s ⋆ MemShrinkResU32A c s ⋆ MemShrinkResU32B c s ⋆
          MemShrinkLitMark c s ⋆ m7RestFrame c s R)) := by
  rw [MemShrinkMem_eq, MemShrinkResArrays_eq]; unfold m7RestFrame; ac_rfl

private theorem memShrink_frame_litMark (c : MemShrinkCfg) (s : FullState) (R : Mem 64 → Prop) :
    (MemShrinkMem c s ⋆ R) =
      (MemShrinkLitMark c s ⋆ (MemShrinkResArrays c s ⋆ m7RestFrame c s R)) := by
  rw [MemShrinkMem_eq]; unfold m7RestFrame; ac_rfl

private theorem zt1_post_wp (Γ : Env)
    (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec)
    (c : MemShrinkCfg) (s : FullState) {Q : Post []} {X : XPost} (R : Mem 64 → Prop)
    (hlen : MemShrinkLengthsOk c s)
    (hpost : ∀ s' m', FullHdrScalarsEq s' s →
      s'.core.vals = List.replicate (2 * c.max_vars) 0#8 →
      s'.core.lit_mark = List.replicate (2 * c.max_vars) 0#8 →
      s'.core.wvec = List.replicate (4 * c.max_vars) 0#32 →
      s'.core.min_stk = List.replicate (2 * c.minDepth) 0#32 →
      s'.scratch.glue_used = List.replicate 64 0#32 →
      s'.scratch.last_learned = List.replicate 16 4294967295#32 →
      MemShrinkLengthsOk c s' → (MemShrinkMem c s' ⋆ R) m' → Q () m')
    (wstk1 : List (BitVec 32)) (hwstk1 : wstk1.length = c.wcap)
    (m1 : Mem 64) :
    let s1 : FullState := FullState.mk {
      s.core with
      vals := List.replicate (2 * c.max_vars) 0#8
      lit_mark := List.replicate (2 * c.max_vars) 0#8
      wvec := List.replicate (4 * c.max_vars) 0#32
      wstk := wstk1 } s.scratch
    (MemShrinkMem c s1 ⋆ R) m1 →
      wp Γ Q X
        (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 232, ())) fun p_16 =>
          Expr.load i64 (Arg.var p_16.fst) fun ld_ms =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 264, ())) fun p_17 =>
          Expr.load i64 (Arg.var p_17.fst) fun ld_md =>
          Expr.call "full_fill_u64_m7" (as := [i64, i64, i64]) (bs := [])
            (Arg.var ld_ms, Arg.var ld_md, Arg.imm 0, ()) fun (_ : Tup Val []) =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 432, ())) fun p_19 =>
          Expr.load i64 (Arg.var p_19.fst) fun ld_gu =>
          Expr.call "full_fill_u64_m7" (as := [i64, i64, i64]) (bs := [])
            (Arg.var ld_gu, Arg.imm 32, Arg.imm 0, ()) fun (_ : Tup Val []) =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 936, ())) fun p_21 =>
          Expr.load i64 (Arg.var p_21.fst) fun ld_ll =>
          Expr.call "full_fill_u64_m7" (as := [i64, i64, i64]) (bs := [])
            (Arg.var ld_ll, Arg.imm 8, Arg.imm (-1), ()) fun (_ : Tup Val []) =>
          Expr.ret ()) m1 := by
  intro s1 hm1
  rcases m7Cfg_sizes_bound c with ⟨_, _, _, _, _, hmd8, _, _, _, _, _, _, _, _⟩
  have hfit := m7Cfg_ptrs_fit c
  have hm_h1 : (array64 (c.hdr + 32) (m7HdrTailWords c s1) ⋆ _) m1 :=
    (memShrink_frame_hdr c s1 R) ▸ hm1
  c0_hsteps
  have hw25 : (m7HdrTailWords c s1)[25]? = some c.pMinStk := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq]; rfl
  refine wp_load_m7Hdr c s1 25 (by omega) 232#64 c.pMinStk hw25
    (hdr_off_eq _ _ 25 (by decide)) hm_h1 ?_
  c0_hsteps
  have hm_h1' : (array64 (c.hdr + 32) (m7HdrTailWords c s1) ⋆ _) m1 := hm_h1
  have hw29 : (m7HdrTailWords c s1)[29]? = some (BitVec.ofNat 64 c.minDepth) := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq]; rfl
  refine wp_load_m7Hdr c s1 29 (by omega) 264#64 (BitVec.ofNat 64 c.minDepth) hw29
    (hdr_off_eq _ _ 29 (by decide)) hm_h1' ?_
  c0_hsteps
  let s2 : FullState :=
    FullState.mk { s1.core with min_stk := List.replicate (2 * c.minDepth) 0#32 } s1.scratch
  refine zt_fill_i32_exact hFill (a := c.pMinStk) (xs := s1.core.min_stk) (w := c.minDepth)
    (val64 := 0#64) (v32 := 0#32)
    (F := array (t := i32) c.pWvec s1.core.wvec ⋆ array64 c.pScore s1.scratch.score ⋆
      array (t := i32) c.pGlueUsed s1.scratch.glue_used ⋆
      array (t := i32) c.pLastLearned s1.scratch.last_learned ⋆
      array (t := i32) c.pArena s1.core.arena ⋆ array (t := i32) c.pWstk s1.core.wstk ⋆
      array (t := i32) c.pDelayed s1.scratch.delayed ⋆
      array (t := i32) c.pRedRefs s1.scratch.red_refs ⋆
      array (t := i32) c.pExtendStk s1.scratch.extend_stk ⋆
      array (t := i32) c.pScratchBuf s1.scratch.scratch_buf ⋆
      (MemShrinkResBytes c s1 ⋆ MemShrinkResU32A c s1 ⋆ MemShrinkResU32B c s1 ⋆
        MemShrinkLitMark c s1 ⋆ m7RestFrame c s1 R))
    (by rw [memShrink_frame_resTail, MemShrinkResTail_eq]; ac_rfl)
    hlen.min_stk_len (by omega) (by omega) bytes64_zero_i32 hm1 ?_
  intro m2 hm2
  have hm2' : (MemShrinkMem c s2 ⋆ R) m2 := by
    rw [memShrink_frame_resTail, MemShrinkResTail_eq]
    have hst : m7RestFrame c s1 R = m7RestFrame c s2 R := by
      simp only [m7RestFrame, m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
        m7HdrTailWords2_eq, m7HdrTailWords3_eq]; rfl
    rw [← hst, show MemShrinkResBytes c s2 = MemShrinkResBytes c s1 from by
        simp only [MemShrinkResBytes_eq]; rfl,
      show MemShrinkResU32A c s2 = MemShrinkResU32A c s1 from by
        simp only [MemShrinkResU32A_eq]; rfl,
      show MemShrinkResU32B c s2 = MemShrinkResU32B c s1 from by
        simp only [MemShrinkResU32B_eq]; rfl,
      show MemShrinkLitMark c s2 = MemShrinkLitMark c s1 from by
        simp only [MemShrinkLitMark_eq]; rfl]
    dsimp only [s2]
    exact Eq.mp (congrFun (by ac_rfl) m2) hm2
  have hm_h2 : (array64 (c.hdr + 32) (m7HdrTailWords c s2) ⋆ _) m2 :=
    (memShrink_frame_hdr c s2 R) ▸ hm2'
  c0_hsteps
  have hw50 : (m7HdrTailWords c s2)[50]? = some c.pGlueUsed := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq]; rfl
  refine wp_load_m7Hdr c s2 50 (by omega) 432#64 c.pGlueUsed hw50
    (hdr_off_eq _ _ 50 (by decide)) hm_h2 ?_
  c0_hsteps
  let s3 : FullState :=
    FullState.mk s2.core { s2.scratch with glue_used := List.replicate 64 0#32 }
  refine zt_fill_i32_exact_imm hFill (a := c.pGlueUsed) (xs := s2.scratch.glue_used)
    (w := 32) (val64 := 0#64) (v32 := 0#32)
    (F := array (t := i32) c.pWvec s2.core.wvec ⋆ array64 c.pScore s2.scratch.score ⋆
      array (t := i32) c.pMinStk s2.core.min_stk ⋆
      array (t := i32) c.pLastLearned s2.scratch.last_learned ⋆
      array (t := i32) c.pArena s2.core.arena ⋆ array (t := i32) c.pWstk s2.core.wstk ⋆
      array (t := i32) c.pDelayed s2.scratch.delayed ⋆
      array (t := i32) c.pRedRefs s2.scratch.red_refs ⋆
      array (t := i32) c.pExtendStk s2.scratch.extend_stk ⋆
      array (t := i32) c.pScratchBuf s2.scratch.scratch_buf ⋆
      (MemShrinkResBytes c s2 ⋆ MemShrinkResU32A c s2 ⋆ MemShrinkResU32B c s2 ⋆
        MemShrinkLitMark c s2 ⋆ m7RestFrame c s2 R))
    (by rw [memShrink_frame_resTail, MemShrinkResTail_eq]; ac_rfl)
    hlen.glue_used_len (by decide) (by omega) bytes64_zero_i32 hm2' ?_
  intro m3 hm3
  have hm3' : (MemShrinkMem c s3 ⋆ R) m3 := by
    rw [memShrink_frame_resTail, MemShrinkResTail_eq]
    have hst : m7RestFrame c s2 R = m7RestFrame c s3 R := by
      simp only [m7RestFrame, m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
        m7HdrTailWords2_eq, m7HdrTailWords3_eq]; rfl
    rw [← hst, show MemShrinkResBytes c s3 = MemShrinkResBytes c s2 from by
        simp only [MemShrinkResBytes_eq]; rfl,
      show MemShrinkResU32A c s3 = MemShrinkResU32A c s2 from by
        simp only [MemShrinkResU32A_eq]; rfl,
      show MemShrinkResU32B c s3 = MemShrinkResU32B c s2 from by
        simp only [MemShrinkResU32B_eq]; rfl,
      show MemShrinkLitMark c s3 = MemShrinkLitMark c s2 from by
        simp only [MemShrinkLitMark_eq]; rfl]
    dsimp only [s3]
    exact Eq.mp (congrFun (by ac_rfl) m3) hm3
  have hm_h3 : (array64 (c.hdr + 32) (m7HdrTailWords c s3) ⋆ _) m3 :=
    (memShrink_frame_hdr c s3 R) ▸ hm3'
  c0_hsteps
  have hw113 : (m7HdrTailWords c s3)[113]? = some c.pLastLearned := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq, m7HdrTailWords2_eq,
      m7HdrTailWords3_eq]; rfl
  refine wp_load_m7Hdr c s3 113 (by omega) 936#64 c.pLastLearned hw113
    (hdr_off_eq _ _ 113 (by decide)) hm_h3 ?_
  c0_hsteps
  let s4 : FullState := FullState.mk s3.core
    { s3.scratch with last_learned := List.replicate 16 4294967295#32 }
  refine zt_fill_i32_exact_imm hFill (a := c.pLastLearned) (xs := s3.scratch.last_learned)
    (w := 8) (val64 := 18446744073709551615#64) (v32 := 4294967295#32)
    (F := array (t := i32) c.pWvec s3.core.wvec ⋆ array64 c.pScore s3.scratch.score ⋆
      array (t := i32) c.pMinStk s3.core.min_stk ⋆
      array (t := i32) c.pGlueUsed s3.scratch.glue_used ⋆
      array (t := i32) c.pArena s3.core.arena ⋆ array (t := i32) c.pWstk s3.core.wstk ⋆
      array (t := i32) c.pDelayed s3.scratch.delayed ⋆
      array (t := i32) c.pRedRefs s3.scratch.red_refs ⋆
      array (t := i32) c.pExtendStk s3.scratch.extend_stk ⋆
      array (t := i32) c.pScratchBuf s3.scratch.scratch_buf ⋆
      (MemShrinkResBytes c s3 ⋆ MemShrinkResU32A c s3 ⋆ MemShrinkResU32B c s3 ⋆
        MemShrinkLitMark c s3 ⋆ m7RestFrame c s3 R))
    (by rw [memShrink_frame_resTail, MemShrinkResTail_eq]; ac_rfl)
    hlen.last_learned_len (by decide) (by omega) bytes64_ff_i32 hm3' ?_
  intro m4 hm4
  have hm4' : (MemShrinkMem c s4 ⋆ R) m4 := by
    rw [memShrink_frame_resTail, MemShrinkResTail_eq]
    have hst : m7RestFrame c s3 R = m7RestFrame c s4 R := by
      simp only [m7RestFrame, m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
        m7HdrTailWords2_eq, m7HdrTailWords3_eq]; rfl
    rw [← hst, show MemShrinkResBytes c s4 = MemShrinkResBytes c s3 from by
        simp only [MemShrinkResBytes_eq]; rfl,
      show MemShrinkResU32A c s4 = MemShrinkResU32A c s3 from by
        simp only [MemShrinkResU32A_eq]; rfl,
      show MemShrinkResU32B c s4 = MemShrinkResU32B c s3 from by
        simp only [MemShrinkResU32B_eq]; rfl,
      show MemShrinkLitMark c s4 = MemShrinkLitMark c s3 from by
        simp only [MemShrinkLitMark_eq]; rfl]
    dsimp only [s4]
    exact Eq.mp (congrFun (by ac_rfl) m4) hm4
  c0_hsteps
  have hsc : FullHdrScalarsEq s4 s := by
    rw [fullHdrScalarsEq_eq]; dsimp only [s4, s3, s2, s1]; simp only [and_self]
  exact hpost s4 m4 hsc
    (by simp [s4, s3, s2, s1]) (by simp [s4, s3, s2, s1])
    (by simp [s4, s3, s2, s1]) (by simp [s4, s3, s2]) (by simp [s4, s3]) (by simp [s4])
    { hlen with
      vals_len := by simp [s4, s3, s2, s1]
      lit_mark_len := by simp [s4, s3, s2, s1]
      wvec_len := by simp [s4, s3, s2, s1]
      min_stk_len := by simp [s4, s3, s2]
      wstk_len_arr := by simp [s4, s3, s2, s1, hwstk1]
      glue_used_len := by simp [s4, s3]
      last_learned_len := by simp [s4] } hm4'

theorem full_zero_tables1_m7_wp (Γ : Env)
    (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec) :
    ∀ a m Q X, m7ZeroTables1Spec a m Q X → Func.wp Γ full_zero_tables1_m7_body a m Q X := by
  rintro ⟨h, _⟩ m Q X hsp
  rw [m7ZeroTables1Spec_eq] at hsp
  rcases hsp with ⟨c, s, R, rfl, hlen, hm, hpost⟩
  unfold full_zero_tables1_m7_body; dsimp only [Func.wp]
  rcases m7Cfg_sizes_bound c with ⟨hmv8, hvb64, _, _, hmv16, _, _, _, _, _, _, _, _, _⟩
  have hfit := m7Cfg_ptrs_fit c
  have hmx : c.max_vars < 2 * Examples.LratBytes.dimacsBound := c.hmaxv
  have h2mv_lt : 2 * c.max_vars < 2 ^ 64 := by
    have := c.hmaxv; unfold Examples.LratBytes.dimacsBound at *; omega
  have hw92 : (m7HdrTailWords c s)[92]? = some (BitVec.ofNat 64 c.max_vars) := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
      m7HdrTailWords2_eq]; rfl
  have hm_h0 : (array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆ _) m :=
    (memShrink_frame_hdr c s R) ▸ hm
  c0_hsteps
  refine wp_load_m7Hdr c s 92 (by omega) 768#64 (BitVec.ofNat 64 c.max_vars) hw92
    (hdr_off_eq _ _ 92 (by decide)) hm_h0 ?_
  c0_hsteps
  have hshl1 : BitVec.ofNat 64 c.max_vars <<< (1 : Nat) =
      BitVec.ofNat 64 (2 * c.max_vars) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [Nat.shiftLeft_eq, Nat.mul_comm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2mv_lt,
      Nat.mod_eq_of_lt (by omega : c.max_vars < 2 ^ 64)]
  have hvb_eq : ((BitVec.ofNat 64 c.max_vars <<< (1 : Nat) + (7 : BitVec 64)) &&&
      ~~~(7 : BitVec 64)) >>> (3 : Nat) =
      BitVec.ofNat 64 (valsBytes c.max_vars / 8) := by
    rw [show (1 : Nat) = (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64 from by decide,
      show (3 : Nat) = (BitVec.signExtend 64 (3 : BitVec 32)).toNat % 64 from by decide,
      fp_vb_eq hmx, fp_shr_sext3 hvb64]
  rw [hvb_eq, hshl1]; dsimp only
  have hw4 : (m7HdrTailWords c s)[4]? = some c.pVals := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq]; rfl
  refine wp_load_m7Hdr c s 4 (by omega) 64#64 c.pVals hw4
    (hdr_off_eq _ _ 4 (by decide)) hm_h0 ?_
  let wV := valsBytes c.max_vars / 8
  have hwV : 8 * wV = valsBytes c.max_vars := valsBytes_div8 c.max_vars
  let sA : FullState :=
    FullState.mk { s.core with vals := List.replicate (2 * c.max_vars) 0#8 } s.scratch
  refine zt_fill_i8_pad hFill (a := c.pVals) (w := wV) (used := 2 * c.max_vars) (val64 := 0#64)
    (v8 := 0#8)
    (F := (array (t := i8) c.pMark s.core.mrk ⋆
        region (c.pMark + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
      (array (t := i8) c.pPhases s.scratch.phases ⋆
        region (c.pPhases + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
      (array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
        region (c.pPhasesTarget + BitVec.ofNat 64 c.max_vars)
          (markBytes c.max_vars - c.max_vars)) ⋆
      (array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
        region (c.pPhasesBest + BitVec.ofNat 64 c.max_vars)
          (markBytes c.max_vars - c.max_vars)) ⋆
      (MemShrinkResU32A c s ⋆ MemShrinkResU32B c s ⋆ MemShrinkResTail c s ⋆
        MemShrinkLitMark c s ⋆ m7RestFrame c s R))
    (by rw [hwV, memShrink_frame_resBytes, MemShrinkResBytes_eq]; ac_rfl)
    hlen.vals_len (by unfold valsBytes at hwV; omega) (by omega) (by omega) bytes64_zero_i8 hm ?_
  intro mA hmA
  have hmA' : (MemShrinkMem c sA ⋆ R) mA := by
    rw [hwV] at hmA
    rw [memShrink_frame_resBytes, MemShrinkResBytes_eq]
    have hst : m7RestFrame c s R = m7RestFrame c sA R := by
      simp only [m7RestFrame, m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
        m7HdrTailWords2_eq, m7HdrTailWords3_eq]; rfl
    rw [← hst, show MemShrinkResU32A c sA = MemShrinkResU32A c s from by
        simp only [MemShrinkResU32A_eq]; rfl,
      show MemShrinkResU32B c sA = MemShrinkResU32B c s from by
        simp only [MemShrinkResU32B_eq]; rfl,
      show MemShrinkResTail c sA = MemShrinkResTail c s from by
        simp only [MemShrinkResTail_eq]; rfl,
      show MemShrinkLitMark c sA = MemShrinkLitMark c s from by
        simp only [MemShrinkLitMark_eq]; rfl]
    try rw [hwV] at hmA
    dsimp only [sA]
    exact Eq.mp (congrFun (by ac_rfl) mA) hmA
  have hm_hA : (array64 (c.hdr + 32) (m7HdrTailWords c sA) ⋆ _) mA :=
    (memShrink_frame_hdr c sA R) ▸ hmA'
  c0_hsteps
  have hw97 : (m7HdrTailWords c sA)[97]? = some c.pLitMark := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
      m7HdrTailWords2_eq]; rfl
  refine wp_load_m7Hdr c sA 97 (by omega) 808#64 c.pLitMark hw97
    (hdr_off_eq _ _ 97 (by decide)) hm_hA ?_
  let sB : FullState :=
    FullState.mk { sA.core with lit_mark := List.replicate (2 * c.max_vars) 0#8 } sA.scratch
  refine zt_fill_i8_pad hFill (a := c.pLitMark) (w := wV) (used := 2 * c.max_vars)
    (val64 := 0#64) (v8 := 0#8)
    (F := MemShrinkResArrays c sA ⋆ m7RestFrame c sA R)
    (by rw [hwV, memShrink_frame_litMark, MemShrinkLitMark_eq])
    hlen.lit_mark_len (by unfold valsBytes at hwV; omega) (by omega) (by omega)
    bytes64_zero_i8 hmA' ?_
  intro mB hmB
  have hmB' : (MemShrinkMem c sB ⋆ R) mB := by
    rw [hwV] at hmB
    rw [memShrink_frame_litMark, MemShrinkLitMark_eq]
    have hst : m7RestFrame c sA R = m7RestFrame c sB R := by
      simp only [m7RestFrame, m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
        m7HdrTailWords2_eq, m7HdrTailWords3_eq]; rfl
    rw [← hst, show MemShrinkResArrays c sB = MemShrinkResArrays c sA from by
        simp only [MemShrinkResArrays_eq, MemShrinkResBytes_eq, MemShrinkResU32A_eq,
          MemShrinkResU32B_eq, MemShrinkResTail_eq]; rfl]
    dsimp only [sB]
    exact Eq.mp (congrFun (by ac_rfl) mB) hmB
  have hm_hB : (array64 (c.hdr + 32) (m7HdrTailWords c sB) ⋆ _) mB :=
    (memShrink_frame_hdr c sB R) ▸ hmB'
  c0_hsteps
  have hw9 : (m7HdrTailWords c sB)[9]? = some c.pWvec := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq]; rfl
  refine wp_load_m7Hdr c sB 9 (by omega) 104#64 c.pWvec hw9
    (hdr_off_eq _ _ 9 (by decide)) hm_hB ?_
  let sC : FullState :=
    FullState.mk { sB.core with wvec := List.replicate (4 * c.max_vars) 0#32 } sB.scratch
  refine zt_fill_i32_exact hFill (a := c.pWvec) (w := 2 * c.max_vars) (val64 := 0#64) (v32 := 0#32)
    (F := array64 c.pScore sB.scratch.score ⋆ array (t := i32) c.pMinStk sB.core.min_stk ⋆
      array (t := i32) c.pGlueUsed sB.scratch.glue_used ⋆
      array (t := i32) c.pLastLearned sB.scratch.last_learned ⋆
      array (t := i32) c.pArena sB.core.arena ⋆ array (t := i32) c.pWstk sB.core.wstk ⋆
      array (t := i32) c.pDelayed sB.scratch.delayed ⋆
      array (t := i32) c.pRedRefs sB.scratch.red_refs ⋆
      array (t := i32) c.pExtendStk sB.scratch.extend_stk ⋆
      array (t := i32) c.pScratchBuf sB.scratch.scratch_buf ⋆
      (MemShrinkResBytes c sB ⋆ MemShrinkResU32A c sB ⋆ MemShrinkResU32B c sB ⋆
        MemShrinkLitMark c sB ⋆ m7RestFrame c sB R))
    (by rw [memShrink_frame_resTail, MemShrinkResTail_eq]; ac_rfl)
    (by have hwv := hlen.wvec_len; dsimp only [sB, sA]; omega)
    (by omega) (by omega) bytes64_zero_i32 hmB' ?_
  intro mC hmC
  have hmC' : (MemShrinkMem c sC ⋆ R) mC := by
    rw [show 2 * (2 * c.max_vars) = 4 * c.max_vars by omega] at hmC
    rw [memShrink_frame_resTail, MemShrinkResTail_eq]
    have hst : m7RestFrame c sB R = m7RestFrame c sC R := by
      simp only [m7RestFrame, m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
        m7HdrTailWords2_eq, m7HdrTailWords3_eq]; rfl
    rw [← hst, show MemShrinkResBytes c sC = MemShrinkResBytes c sB from by
        simp only [MemShrinkResBytes_eq]; rfl,
      show MemShrinkResU32A c sC = MemShrinkResU32A c sB from by
        simp only [MemShrinkResU32A_eq]; rfl,
      show MemShrinkResU32B c sC = MemShrinkResU32B c sB from by
        simp only [MemShrinkResU32B_eq]; rfl,
      show MemShrinkLitMark c sC = MemShrinkLitMark c sB from by
        simp only [MemShrinkLitMark_eq]; rfl]
    dsimp only [sC]
    exact Eq.mp (congrFun (by ac_rfl) mC) hmC
  refine wp_join_state0 (α := List (BitVec 32))
    (Inv := fun wstk1 m1 => wstk1.length = c.wcap ∧
      (MemShrinkMem c (FullState.mk { sC.core with wstk := wstk1 } sC.scratch) ⋆ R) m1) ?_ ?_
  · rintro _ wstk1 m1 ⟨hwstk1, hm1⟩
    exact zt1_post_wp Γ hFill c s R hlen hpost wstk1 hwstk1 m1 hm1
  · intro J hJ
    have hm_hC : (array64 (c.hdr + 32) (m7HdrTailWords c sC) ⋆ _) mC :=
      (memShrink_frame_hdr c sC R) ▸ hmC'
    c0_hsteps_nogrp
    have hw1 : (m7HdrTailWords c sC)[1]? = some (BitVec.ofNat 64 c.wcap) := by
      simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq]; rfl
    refine wp_load_m7Hdr c sC 1 (by omega) 40#64 (BitVec.ofNat 64 c.wcap) hw1
      (hdr_off_eq _ _ 1 (by decide)) hm_hC ?_
    c0_hsplit
    · rw [Nat.mod_eq_of_lt (by have := c.hwcap; unfold Examples.LratBytes.dimacsBound at *; omega)]
        at hc
      have hwpos : 0 < c.wcap := hc
      c0_hsteps
      have hw11 : (m7HdrTailWords c sC)[11]? = some c.pWstk := by
        simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq]; rfl
      refine wp_load_m7Hdr c sC 11 (by omega) 120#64 c.pWstk hw11
        (hdr_off_eq _ _ 11 (by decide)) hm_hC ?_
      c0_hsteps
      have hm_ws : (array (t := i32) c.pWstk sC.core.wstk ⋆
          (array (t := i32) c.pWvec sC.core.wvec ⋆ array64 c.pScore sC.scratch.score ⋆
            array (t := i32) c.pMinStk sC.core.min_stk ⋆
            array (t := i32) c.pGlueUsed sC.scratch.glue_used ⋆
            array (t := i32) c.pLastLearned sC.scratch.last_learned ⋆
            array (t := i32) c.pArena sC.core.arena ⋆
            array (t := i32) c.pDelayed sC.scratch.delayed ⋆
            array (t := i32) c.pRedRefs sC.scratch.red_refs ⋆
            array (t := i32) c.pExtendStk sC.scratch.extend_stk ⋆
            array (t := i32) c.pScratchBuf sC.scratch.scratch_buf ⋆
            (MemShrinkResBytes c sC ⋆ MemShrinkResU32A c sC ⋆ MemShrinkResU32B c sC ⋆
              MemShrinkLitMark c sC ⋆ m7RestFrame c sC R))) mC := by
        rw [memShrink_frame_resTail, MemShrinkResTail_eq] at hmC'
        exact Eq.mp (congrFun (by ac_rfl) mC) hmC'
      refine wp_store_array (i := 0) (by decide) ?_
        (by rw [show sC.core.wstk = s.core.wstk from rfl, hlen.wstk_len_arr]; exact hwpos)
        hm_ws ?_
      · simp
      · intro mD hmD
        let sD : FullState :=
          FullState.mk { sC.core with wstk := sC.core.wstk.set 0 0#32 } sC.scratch
        have hmD' : (MemShrinkMem c sD ⋆ R) mD := by
          rw [memShrink_frame_resTail, MemShrinkResTail_eq]
          have hst : m7RestFrame c sC R = m7RestFrame c sD R := by
            simp only [m7RestFrame, m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
              m7HdrTailWords2_eq, m7HdrTailWords3_eq]; rfl
          rw [← hst, show MemShrinkResBytes c sD = MemShrinkResBytes c sC from by
              simp only [MemShrinkResBytes_eq]; rfl,
            show MemShrinkResU32A c sD = MemShrinkResU32A c sC from by
              simp only [MemShrinkResU32A_eq]; rfl,
            show MemShrinkResU32B c sD = MemShrinkResU32B c sC from by
              simp only [MemShrinkResU32B_eq]; rfl,
            show MemShrinkLitMark c sD = MemShrinkLitMark c sC from by
              simp only [MemShrinkLitMark_eq]; rfl]
          dsimp only [sD]
          exact Eq.mp (congrFun (by ac_rfl) mD) hmD
        c0_hsteps
        exact hJ (sC.core.wstk.set 0 0#32) mD ⟨by simp [sC, sB, sA, hlen.wstk_len_arr], hmD'⟩
    · c0_hsteps
      exact hJ sC.core.wstk mC ⟨by simpa [sC, sB, sA] using hlen.wstk_len_arr, hmC'⟩

private theorem wp_load_m7Mv_frame {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {A : Mem 64 → Prop} (c : MemShrinkCfg) (s : FullState) (R : Mem 64 → Prop)
    (hm : (A ⋆ m7RestFrame c s R) m)
    {k : Val i64 → Expr Val Cont rs} (hk : wp Γ Q X (k (BitVec.ofNat 64 c.mv)) m) :
    wp Γ Q X (Expr.load i64 (Arg.var c.hdr) k) m := by
  have hm' : (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
      s.core.d_val ⋆
      (A ⋆ array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆ MemShrinkTransRegions c ⋆
        region c.pSlack c.slack ⋆ R)) m := by
    unfold m7RestFrame at hm; exact Eq.mp (congrFun (by ac_rfl) m) hm
  rw [wp_load]; unfold dimacsState at hm'
  exact load_array64_step c.hdr 0 (by simp) hm' (by simp) hk

private theorem wp_load_m7Hdr_frame {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {A : Mem 64 → Prop} (c : MemShrinkCfg) (s : FullState) (R : Mem 64 → Prop)
    (idx : Nat) (hidx : idx < 140) (off : BitVec 64) (v : BitVec 64)
    (hv : (m7HdrTailWords c s)[idx]? = some v)
    (hoff : c.hdr + off = (c.hdr + 32) + BitVec.ofNat 64 (8 * idx))
    (hm : (A ⋆ m7RestFrame c s R) m)
    {k : Val i64 → Expr Val Cont rs} (hk : wp Γ Q X (k v) m) :
    wp Γ Q X (Expr.load i64 (Arg.var (c.hdr + off)) k) m := by
  have hm' : (array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆
      (A ⋆ dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
        s.core.d_val ⋆ MemShrinkTransRegions c ⋆ region c.pSlack c.slack ⋆ R)) m := by
    unfold m7RestFrame at hm; exact Eq.mp (congrFun (by ac_rfl) m) hm
  exact wp_load_m7Hdr c s idx hidx off v hv hoff hm' hk

private def m7U32ARestLvlRsns (c : MemShrinkCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pFlags s.core.flags ⋆
    region (c.pFlags + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pTrail s.core.trl ⋆
    region (c.pTrail + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pTrailPos s.core.trail_pos ⋆
    region (c.pTrailPos + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pTmp s.core.tmp ⋆
    region (c.pTmp + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pHeap s.scratch.heap ⋆
    region (c.pHeap + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pPos s.scratch.pos ⋆
    region (c.pPos + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars))

private theorem u32a_focus_lvl_rsns (c : MemShrinkCfg) (s : FullState) :
    MemShrinkResU32A c s =
      ((array (t := i32) c.pLevel s.core.lvl ⋆
        region (c.pLevel + BitVec.ofNat 64 (4 * c.max_vars))
          (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pReason s.core.rsns ⋆
        region (c.pReason + BitVec.ofNat 64 (4 * c.max_vars))
          (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      m7U32ARestLvlRsns c s) := by
  rw [MemShrinkResU32A_eq]; unfold m7U32ARestLvlRsns; ac_rfl

private def m7U32BRestFrame (c : MemShrinkCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pMinClr s.core.min_clr ⋆
    region (c.pMinClr + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pShrinkStk s.scratch.shrink_stk ⋆
    region (c.pShrinkStk + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pQPrev s.scratch.q_prev ⋆
    region (c.pQPrev + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pQNext s.scratch.q_next ⋆
    region (c.pQNext + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
    region (c.pQStamp + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars))

private theorem u32b_focus_frame (c : MemShrinkCfg) (s : FullState) :
    MemShrinkResU32B c s =
      ((array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
        region (c.pFrameTrail + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
          (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
      (array (t := i32) c.pFrameDec s.core.frame_dec ⋆
        region (c.pFrameDec + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
          (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
      m7U32BRestFrame c s) := by
  rw [MemShrinkResU32B_eq]; unfold m7U32BRestFrame; ac_rfl

private def m7TailRestScore (c : MemShrinkCfg) (s : FullState) : Mem 64 → Prop :=
  array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pMinStk s.core.min_stk ⋆
  array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
  array (t := i32) c.pLastLearned s.scratch.last_learned ⋆
  array (t := i32) c.pArena s.core.arena ⋆ array (t := i32) c.pWstk s.core.wstk ⋆
  array (t := i32) c.pDelayed s.scratch.delayed ⋆ array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
  array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
  array (t := i32) c.pScratchBuf s.scratch.scratch_buf

private theorem resTail_focus_score (c : MemShrinkCfg) (s : FullState) :
    MemShrinkResTail c s = (array64 c.pScore s.scratch.score ⋆ m7TailRestScore c s) := by
  rw [MemShrinkResTail_eq]; unfold m7TailRestScore; ac_rfl

private def m7U32ALoopsRest (c : MemShrinkCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pLevel s.core.lvl ⋆
    region (c.pLevel + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pReason s.core.rsns ⋆
    region (c.pReason + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pTrail s.core.trl ⋆
    region (c.pTrail + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pTrailPos s.core.trail_pos ⋆
    region (c.pTrailPos + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pTmp s.core.tmp ⋆
    region (c.pTmp + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars))

private theorem u32a_focus_loops (c : MemShrinkCfg) (s : FullState) :
    MemShrinkResU32A c s =
      (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pHeap s.scratch.heap ⋆
        array (t := i32) c.pPos s.scratch.pos ⋆
        (region (c.pFlags + BitVec.ofNat 64 (4 * c.max_vars))
          (Full.u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
        region (c.pHeap + BitVec.ofNat 64 (4 * c.max_vars))
          (Full.u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
        region (c.pPos + BitVec.ofNat 64 (4 * c.max_vars))
          (Full.u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
        m7U32ALoopsRest c s)) := by
  rw [MemShrinkResU32A_eq]; unfold m7U32ALoopsRest; ac_rfl

private def m7U32BLoopsRest (c : MemShrinkCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pMinClr s.core.min_clr ⋆
    region (c.pMinClr + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pShrinkStk s.scratch.shrink_stk ⋆
    region (c.pShrinkStk + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
    region (c.pFrameTrail + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
      (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
  (array (t := i32) c.pFrameDec s.core.frame_dec ⋆
    region (c.pFrameDec + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
      (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1)))

private theorem u32b_focus_loops (c : MemShrinkCfg) (s : FullState) :
    MemShrinkResU32B c s =
      (array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        (region (c.pQPrev + BitVec.ofNat 64 (4 * c.max_vars))
          (Full.u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
        region (c.pQNext + BitVec.ofNat 64 (4 * c.max_vars))
          (Full.u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
        region (c.pQStamp + BitVec.ofNat 64 (4 * c.max_vars))
          (Full.u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
        m7U32BLoopsRest c s)) := by
  rw [MemShrinkResU32B_eq]; unfold m7U32BLoopsRest; ac_rfl

private def m7LoopsRest (c : MemShrinkCfg) (s : FullState) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  MemShrinkResBytes c s ⋆ m7U32ALoopsRest c s ⋆ m7U32BLoopsRest c s ⋆ MemShrinkResTail c s ⋆
    MemShrinkLitMark c s ⋆
    (region (c.pFlags + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
    region (c.pHeap + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
    region (c.pPos + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
    region (c.pQPrev + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
    region (c.pQNext + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
    region (c.pQStamp + BitVec.ofNat 64 (4 * c.max_vars))
      (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
    m7RestFrame c s R

private def m7LoopsMem (c : MemShrinkCfg) (s : FullState)
    (fl hp ps qp qn qs : List (BitVec 32)) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  array (t := i32) c.pFlags fl ⋆ array (t := i32) c.pHeap hp ⋆ array (t := i32) c.pPos ps ⋆
    array (t := i32) c.pQPrev qp ⋆ array (t := i32) c.pQNext qn ⋆
    array (t := i32) c.pQStamp qs ⋆ m7LoopsRest c s R

private theorem memShrink_eq_loopsMem (c : MemShrinkCfg) (s : FullState) (R : Mem 64 → Prop) :
    (MemShrinkMem c s ⋆ R) =
      m7LoopsMem c s s.core.flags s.scratch.heap s.scratch.pos s.scratch.q_prev s.scratch.q_next
        s.scratch.q_stamp R := by
  rw [MemShrinkMem_eq, MemShrinkResArrays_eq, u32a_focus_loops, u32b_focus_loops]
  unfold m7LoopsMem m7LoopsRest m7RestFrame; ac_rfl

private theorem loopsMem_eq_memShrink (c : MemShrinkCfg) (s : FullState)
    (fl hp ps qp qn qs : List (BitVec 32)) (R : Mem 64 → Prop) :
    let s' : FullState := FullState.mk { s.core with flags := fl }
      { s.scratch with heap := hp, pos := ps, q_prev := qp, q_next := qn, q_stamp := qs }
    m7LoopsMem c s fl hp ps qp qn qs R = (MemShrinkMem c s' ⋆ R) := by
  intro s'
  have h1 : m7LoopsRest c s R = m7LoopsRest c s' R := by
    simp only [m7LoopsRest, m7U32ALoopsRest, m7U32BLoopsRest, m7RestFrame, MemShrinkResBytes_eq,
      MemShrinkResTail_eq, MemShrinkLitMark_eq, m7HdrTailWords_eq, m7HdrTailWords0_eq,
      m7HdrTailWords1_eq, m7HdrTailWords2_eq, m7HdrTailWords3_eq]; rfl
  rw [memShrink_eq_loopsMem c s' R]
  unfold m7LoopsMem
  rw [h1]

private def zt2BytesState (s : FullState) (mx : Nat) : FullState :=
  FullState.mk { s.core with mrk := List.replicate mx 0#8 }
    { s.scratch with
      phases := List.replicate mx 1#8
      phases_target := List.replicate mx 0#8
      phases_best := List.replicate mx 0#8 }

private def zt2FillState (s : FullState) (mx : Nat) : FullState :=
  FullState.mk
    { s.core with
      lvl := List.replicate mx 0#32
      rsns := List.replicate mx 4294967295#32
      frame_trail := List.replicate (mx + 1) 0#32
      frame_dec := List.replicate (mx + 1) 4294967295#32 }
    { s.scratch with score := List.replicate mx 0#64 }

private theorem zt2_bytes4_wp (Γ : Env)
    (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec)
    (c : MemShrinkCfg) (s : FullState) {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (A R : Mem 64 → Prop) (hlen : MemShrinkLengthsOk c s)
    (hfit : c.pMark.toNat + markBytes c.max_vars < 2 ^ 64 ∧
      c.pPhases.toNat + markBytes c.max_vars < 2 ^ 64 ∧
      c.pPhasesTarget.toNat + markBytes c.max_vars < 2 ^ 64 ∧
      c.pPhasesBest.toNat + markBytes c.max_vars < 2 ^ 64)
    (hmb64 : markBytes c.max_vars < 2 ^ 64)
    (hm : (MemShrinkResBytes c s ⋆ A ⋆ m7RestFrame c s R) m)
    {k : Expr Val Cont rs}
    (hk : ∀ m',
      (MemShrinkResBytes c (zt2BytesState s c.max_vars) ⋆ A ⋆
        m7RestFrame c (zt2BytesState s c.max_vars) R) m' → wp Γ Q X k m') :
    wp Γ Q X
      (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 72, ())) fun p0 =>
        Expr.load i64 (Arg.var p0.fst) fun ld0 =>
          Expr.call "full_fill_u64_m7" (as := [i64, i64, i64]) (bs := [])
            (Arg.var ld0, Arg.var (BitVec.ofNat 64 (markBytes c.max_vars / 8)), Arg.imm 0#64, ())
            fun _ =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 392, ())) fun p1 =>
            Expr.load i64 (Arg.var p1.fst) fun ld1 =>
              Expr.call "full_fill_u64_m7" (as := [i64, i64, i64]) (bs := [])
                (Arg.var ld1, Arg.var (BitVec.ofNat 64 (markBytes c.max_vars / 8)),
                  Arg.imm 0#64, ()) fun _ =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 400, ())) fun p2 =>
                Expr.load i64 (Arg.var p2.fst) fun ld2 =>
                  Expr.call "full_fill_u64_m7" (as := [i64, i64, i64]) (bs := [])
                    (Arg.var ld2, Arg.var (BitVec.ofNat 64 (markBytes c.max_vars / 8)),
                      Arg.imm 0#64, ()) fun _ =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 224, ())) fun p3 =>
                    Expr.load i64 (Arg.var p3.fst) fun ld3 =>
                      Expr.call "full_fill_u64_m7" (as := [i64, i64, i64]) (bs := [])
                        (Arg.var ld3, Arg.var (BitVec.ofNat 64 (markBytes c.max_vars / 8)),
                          Arg.imm 72340172838076673#64, ()) fun _ => k) m := by
  have hm_unp :
      ((array (t := i8) c.pMark s.core.mrk ⋆
          region (c.pMark + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pPhases s.scratch.phases ⋆
          region (c.pPhases + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
          region (c.pPhasesTarget + BitVec.ofNat 64 c.max_vars)
            (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
          region (c.pPhasesBest + BitVec.ofNat 64 c.max_vars)
            (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pVals s.core.vals ⋆
          region (c.pVals + BitVec.ofNat 64 (2 * c.max_vars))
            (valsBytes c.max_vars - 2 * c.max_vars)) ⋆ A ⋆ m7RestFrame c s R) m := by
    rw [MemShrinkResBytes_eq] at hm; exact Eq.mp (congrFun (by ac_rfl) m) hm
  have hm_f0 :
      (((array (t := i8) c.pPhases s.scratch.phases ⋆
          region (c.pPhases + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
          region (c.pPhasesTarget + BitVec.ofNat 64 c.max_vars)
            (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
          region (c.pPhasesBest + BitVec.ofNat 64 c.max_vars)
            (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pMark s.core.mrk ⋆
          region (c.pMark + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pVals s.core.vals ⋆
          region (c.pVals + BitVec.ofNat 64 (2 * c.max_vars))
            (valsBytes c.max_vars - 2 * c.max_vars)) ⋆ A) ⋆ m7RestFrame c s R) m :=
    Eq.mp (congrFun (by ac_rfl) m) hm_unp
  have hw5 : (m7HdrTailWords c s)[5]? = some c.pMark := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq]; rfl
  c0_hsteps
  refine wp_load_m7Hdr_frame c s R 5 (by omega) 72#64 c.pMark hw5
    (hdr_off_eq _ _ 5 (by decide)) hm_f0 ?_
  have hmb8 : 8 * (markBytes c.max_vars / 8) = markBytes c.max_vars := markBytes_div8 c.max_vars
  have hmb_le : c.max_vars ≤ markBytes c.max_vars := by unfold markBytes; omega
  refine zt_fill_i8_pad hFill (a := c.pMark) (w := markBytes c.max_vars / 8) (used := c.max_vars)
    (val64 := 0#64) (v8 := 0#8)
    (F := (array (t := i8) c.pPhases s.scratch.phases ⋆
        region (c.pPhases + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
      (array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
        region (c.pPhasesTarget + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
      (array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
        region (c.pPhasesBest + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
      (array (t := i8) c.pVals s.core.vals ⋆
        region (c.pVals + BitVec.ofNat 64 (2 * c.max_vars))
          (valsBytes c.max_vars - 2 * c.max_vars)) ⋆ A ⋆ m7RestFrame c s R)
    (by rw [hmb8]; ac_rfl) hlen.mrk_len (by omega) (by omega) (by omega) bytes64_zero_i8 hm_f0 ?_
  intro m1 hm1
  have hm1_f :
      (((array (t := i8) c.pMark (List.replicate c.max_vars 0#8) ⋆
          region (c.pMark + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pPhases s.scratch.phases ⋆
          region (c.pPhases + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
          region (c.pPhasesTarget + BitVec.ofNat 64 c.max_vars)
            (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
          region (c.pPhasesBest + BitVec.ofNat 64 c.max_vars)
            (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pVals s.core.vals ⋆
          region (c.pVals + BitVec.ofNat 64 (2 * c.max_vars))
            (valsBytes c.max_vars - 2 * c.max_vars)) ⋆ A) ⋆ m7RestFrame c s R) m1 := by
    rw [hmb8] at hm1; exact Eq.mp (congrFun (by ac_rfl) m1) hm1
  have hw45 : (m7HdrTailWords c s)[45]? = some c.pPhasesTarget := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq]; rfl
  c0_hsteps
  refine wp_load_m7Hdr_frame c s R 45 (by omega) 392#64 c.pPhasesTarget hw45
    (hdr_off_eq _ _ 45 (by decide)) hm1_f ?_
  refine zt_fill_i8_pad hFill (a := c.pPhasesTarget) (w := markBytes c.max_vars / 8)
    (used := c.max_vars) (val64 := 0#64) (v8 := 0#8)
    (F := (array (t := i8) c.pMark (List.replicate c.max_vars 0#8) ⋆
        region (c.pMark + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
      (array (t := i8) c.pPhases s.scratch.phases ⋆
        region (c.pPhases + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
      (array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
        region (c.pPhasesBest + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
      (array (t := i8) c.pVals s.core.vals ⋆
        region (c.pVals + BitVec.ofNat 64 (2 * c.max_vars))
          (valsBytes c.max_vars - 2 * c.max_vars)) ⋆ A ⋆ m7RestFrame c s R)
    (by rw [hmb8]; ac_rfl) hlen.phases_target_len (by omega) (by omega) (by omega) bytes64_zero_i8
    hm1_f ?_
  intro m2 hm2
  have hm2_f :
      (((array (t := i8) c.pMark (List.replicate c.max_vars 0#8) ⋆
          region (c.pMark + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pPhases s.scratch.phases ⋆
          region (c.pPhases + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pPhasesTarget (List.replicate c.max_vars 0#8) ⋆
          region (c.pPhasesTarget + BitVec.ofNat 64 c.max_vars)
            (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
          region (c.pPhasesBest + BitVec.ofNat 64 c.max_vars)
            (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pVals s.core.vals ⋆
          region (c.pVals + BitVec.ofNat 64 (2 * c.max_vars))
            (valsBytes c.max_vars - 2 * c.max_vars)) ⋆ A) ⋆ m7RestFrame c s R) m2 := by
    rw [hmb8] at hm2; exact Eq.mp (congrFun (by ac_rfl) m2) hm2
  have hw46 : (m7HdrTailWords c s)[46]? = some c.pPhasesBest := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq]; rfl
  c0_hsteps
  refine wp_load_m7Hdr_frame c s R 46 (by omega) 400#64 c.pPhasesBest hw46
    (hdr_off_eq _ _ 46 (by decide)) hm2_f ?_
  refine zt_fill_i8_pad hFill (a := c.pPhasesBest) (w := markBytes c.max_vars / 8)
    (used := c.max_vars) (val64 := 0#64) (v8 := 0#8)
    (F := (array (t := i8) c.pMark (List.replicate c.max_vars 0#8) ⋆
        region (c.pMark + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
      (array (t := i8) c.pPhases s.scratch.phases ⋆
        region (c.pPhases + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
      (array (t := i8) c.pPhasesTarget (List.replicate c.max_vars 0#8) ⋆
        region (c.pPhasesTarget + BitVec.ofNat 64 c.max_vars)
          (markBytes c.max_vars - c.max_vars)) ⋆
      (array (t := i8) c.pVals s.core.vals ⋆
        region (c.pVals + BitVec.ofNat 64 (2 * c.max_vars))
          (valsBytes c.max_vars - 2 * c.max_vars)) ⋆ A ⋆ m7RestFrame c s R)
    (by rw [hmb8]; ac_rfl) hlen.phases_best_len (by omega) (by omega) (by omega) bytes64_zero_i8
    hm2_f ?_
  intro m3 hm3
  have hm3_f :
      (((array (t := i8) c.pMark (List.replicate c.max_vars 0#8) ⋆
          region (c.pMark + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pPhases s.scratch.phases ⋆
          region (c.pPhases + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pPhasesTarget (List.replicate c.max_vars 0#8) ⋆
          region (c.pPhasesTarget + BitVec.ofNat 64 c.max_vars)
            (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pPhasesBest (List.replicate c.max_vars 0#8) ⋆
          region (c.pPhasesBest + BitVec.ofNat 64 c.max_vars)
            (markBytes c.max_vars - c.max_vars)) ⋆
        (array (t := i8) c.pVals s.core.vals ⋆
          region (c.pVals + BitVec.ofNat 64 (2 * c.max_vars))
            (valsBytes c.max_vars - 2 * c.max_vars)) ⋆ A) ⋆ m7RestFrame c s R) m3 := by
    rw [hmb8] at hm3; exact Eq.mp (congrFun (by ac_rfl) m3) hm3
  have hw24 : (m7HdrTailWords c s)[24]? = some c.pPhases := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq]; rfl
  c0_hsteps
  refine wp_load_m7Hdr_frame c s R 24 (by omega) 224#64 c.pPhases hw24
    (hdr_off_eq _ _ 24 (by decide)) hm3_f ?_
  refine zt_fill_i8_pad hFill (a := c.pPhases) (w := markBytes c.max_vars / 8)
    (used := c.max_vars) (val64 := 72340172838076673#64) (v8 := 1#8)
    (F := (array (t := i8) c.pMark (List.replicate c.max_vars 0#8) ⋆
        region (c.pMark + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
      (array (t := i8) c.pPhasesTarget (List.replicate c.max_vars 0#8) ⋆
        region (c.pPhasesTarget + BitVec.ofNat 64 c.max_vars)
          (markBytes c.max_vars - c.max_vars)) ⋆
      (array (t := i8) c.pPhasesBest (List.replicate c.max_vars 0#8) ⋆
        region (c.pPhasesBest + BitVec.ofNat 64 c.max_vars)
          (markBytes c.max_vars - c.max_vars)) ⋆
      (array (t := i8) c.pVals s.core.vals ⋆
        region (c.pVals + BitVec.ofNat 64 (2 * c.max_vars))
          (valsBytes c.max_vars - 2 * c.max_vars)) ⋆ A ⋆ m7RestFrame c s R)
    (by rw [hmb8]; ac_rfl) hlen.phases_len (by omega) (by omega) (by omega) bytes64_one_i8 hm3_f ?_
  intro m4 hm4
  let s1 : FullState := FullState.mk { s.core with mrk := List.replicate c.max_vars 0#8 }
    { s.scratch with
      phases := List.replicate c.max_vars 1#8
      phases_target := List.replicate c.max_vars 0#8
      phases_best := List.replicate c.max_vars 0#8 }
  have hm4' : (MemShrinkResBytes c s1 ⋆ A ⋆ m7RestFrame c s1 R) m4 := by
    rw [hmb8] at hm4
    have hst : m7RestFrame c s R = m7RestFrame c s1 R := by
      simp only [m7RestFrame, m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
        m7HdrTailWords2_eq, m7HdrTailWords3_eq]; rfl
    rw [← hst, MemShrinkResBytes_eq]; dsimp only [s1]
    exact Eq.mp (congrFun (by ac_rfl) m4) hm4
  exact hk m4 hm4'

private theorem zt2_u32_score5_wp (Γ : Env)
    (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec)
    (c : MemShrinkCfg) (s : FullState) {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (B R : Mem 64 → Prop) (hlen : MemShrinkLengthsOk c s)
    (hfit : c.pLevel.toNat + Full.u32FullBytes c.max_vars < 2 ^ 64 ∧
      c.pReason.toNat + Full.u32FullBytes c.max_vars < 2 ^ 64 ∧
      c.pFrameTrail.toNat + Full.u32FullBytes c.max_vars < 2 ^ 64 ∧
      c.pFrameDec.toNat + Full.u32FullBytes c.max_vars < 2 ^ 64 ∧
      c.pScore.toNat + 8 * c.max_vars < 2 ^ 64)
    (hub64 : Full.u32FullBytes c.max_vars < 2 ^ 64) (hmv8 : 8 * c.max_vars < 2 ^ 64)
    (hm : (MemShrinkResU32A c s ⋆ MemShrinkResU32B c s ⋆ MemShrinkResTail c s ⋆ B ⋆
      m7RestFrame c s R) m)
    {k : Expr Val Cont rs}
    (hk : ∀ m',
      (MemShrinkResU32A c (zt2FillState s c.max_vars) ⋆
        MemShrinkResU32B c (zt2FillState s c.max_vars) ⋆
        MemShrinkResTail c (zt2FillState s c.max_vars) ⋆ B ⋆
        m7RestFrame c (zt2FillState s c.max_vars) R) m' → wp Γ Q X k m') :
    wp Γ Q X
      (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 80, ())) fun p0 =>
        Expr.load i64 (Arg.var p0.fst) fun ld0 =>
          Expr.call "full_fill_u64_m7" (as := [i64, i64, i64]) (bs := [])
            (Arg.var ld0, Arg.var (BitVec.ofNat 64 (Full.u32FullBytes c.max_vars / 8)),
              Arg.imm 0#64, ()) fun _ =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 832, ())) fun p1 =>
            Expr.load i64 (Arg.var p1.fst) fun ld1 =>
              Expr.call "full_fill_u64_m7" (as := [i64, i64, i64]) (bs := [])
                (Arg.var ld1, Arg.var (BitVec.ofNat 64 (Full.u32FullBytes c.max_vars / 8)),
                  Arg.imm 0#64, ()) fun _ =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 88, ())) fun p2 =>
                Expr.load i64 (Arg.var p2.fst) fun ld2 =>
                  Expr.call "full_fill_u64_m7" (as := [i64, i64, i64]) (bs := [])
                    (Arg.var ld2, Arg.var (BitVec.ofNat 64 (Full.u32FullBytes c.max_vars / 8)),
                      Arg.imm 18446744073709551615#64, ()) fun _ =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 840, ())) fun p3 =>
                    Expr.load i64 (Arg.var p3.fst) fun ld3 =>
                      Expr.call "full_fill_u64_m7" (as := [i64, i64, i64]) (bs := [])
                        (Arg.var ld3,
                          Arg.var (BitVec.ofNat 64 (Full.u32FullBytes c.max_vars / 8)),
                          Arg.imm 18446744073709551615#64, ()) fun _ =>
                      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 216, ())) fun p4 =>
                        Expr.load i64 (Arg.var p4.fst) fun ld4 =>
                          Expr.call "full_fill_u64_m7" (as := [i64, i64, i64]) (bs := [])
                            (Arg.var ld4, Arg.var (BitVec.ofNat 64 c.max_vars),
                              Arg.imm 0#64, ()) fun _ => k) m := by
  have hub8 : 8 * (Full.u32FullBytes c.max_vars / 8) = Full.u32FullBytes c.max_vars :=
    u32FullBytes_div8 c.max_vars
  have hub_le0 : 4 * c.max_vars ≤ Full.u32FullBytes c.max_vars := by
    unfold Full.u32FullBytes; omega
  have hub_le1 : 4 * (c.max_vars + 1) ≤ Full.u32FullBytes c.max_vars := by
    unfold Full.u32FullBytes; omega
  have hm_f0 :
      (((array (t := i32) c.pLevel s.core.lvl ⋆
          region (c.pLevel + BitVec.ofNat 64 (4 * c.max_vars))
            (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
        (array (t := i32) c.pReason s.core.rsns ⋆
          region (c.pReason + BitVec.ofNat 64 (4 * c.max_vars))
            (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
          region (c.pFrameTrail + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
            (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
        (array (t := i32) c.pFrameDec s.core.frame_dec ⋆
          region (c.pFrameDec + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
            (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
        array64 c.pScore s.scratch.score ⋆
        m7U32ARestLvlRsns c s ⋆ m7U32BRestFrame c s ⋆ m7TailRestScore c s ⋆ B) ⋆
        m7RestFrame c s R) m := by
    rw [u32a_focus_lvl_rsns, u32b_focus_frame, resTail_focus_score] at hm
    exact Eq.mp (congrFun (by ac_rfl) m) hm
  have hw6 : (m7HdrTailWords c s)[6]? = some c.pLevel := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq]; rfl
  c0_hsteps
  refine wp_load_m7Hdr_frame c s R 6 (by omega) 80#64 c.pLevel hw6
    (hdr_off_eq _ _ 6 (by decide)) hm_f0 ?_
  refine zt_fill_i32_pad hFill (a := c.pLevel) (w := Full.u32FullBytes c.max_vars / 8)
    (used := c.max_vars) (val64 := 0#64) (v32 := 0#32)
    (F := (array (t := i32) c.pReason s.core.rsns ⋆
        region (c.pReason + BitVec.ofNat 64 (4 * c.max_vars))
          (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
        region (c.pFrameTrail + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
          (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
      (array (t := i32) c.pFrameDec s.core.frame_dec ⋆
        region (c.pFrameDec + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
          (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
      array64 c.pScore s.scratch.score ⋆
      m7U32ARestLvlRsns c s ⋆ m7U32BRestFrame c s ⋆ m7TailRestScore c s ⋆ B ⋆ m7RestFrame c s R)
    (by rw [hub8]; ac_rfl) hlen.lvl_len (by omega) (by omega) (by omega) bytes64_zero_i32 hm_f0 ?_
  intro m1 hm1
  have hm1_f :
      (((array (t := i32) c.pLevel (List.replicate c.max_vars 0#32) ⋆
          region (c.pLevel + BitVec.ofNat 64 (4 * c.max_vars))
            (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
        (array (t := i32) c.pReason s.core.rsns ⋆
          region (c.pReason + BitVec.ofNat 64 (4 * c.max_vars))
            (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
          region (c.pFrameTrail + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
            (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
        (array (t := i32) c.pFrameDec s.core.frame_dec ⋆
          region (c.pFrameDec + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
            (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
        array64 c.pScore s.scratch.score ⋆
        m7U32ARestLvlRsns c s ⋆ m7U32BRestFrame c s ⋆ m7TailRestScore c s ⋆ B) ⋆
        m7RestFrame c s R) m1 := by
    rw [hub8] at hm1; exact Eq.mp (congrFun (by ac_rfl) m1) hm1
  have hw100 : (m7HdrTailWords c s)[100]? = some c.pFrameTrail := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
      m7HdrTailWords2_eq]; rfl
  c0_hsteps
  refine wp_load_m7Hdr_frame c s R 100 (by omega) 832#64 c.pFrameTrail hw100
    (hdr_off_eq _ _ 100 (by decide)) hm1_f ?_
  refine zt_fill_i32_pad hFill (a := c.pFrameTrail) (w := Full.u32FullBytes c.max_vars / 8)
    (used := c.max_vars + 1) (val64 := 0#64) (v32 := 0#32)
    (F := (array (t := i32) c.pLevel (List.replicate c.max_vars 0#32) ⋆
        region (c.pLevel + BitVec.ofNat 64 (4 * c.max_vars))
          (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pReason s.core.rsns ⋆
        region (c.pReason + BitVec.ofNat 64 (4 * c.max_vars))
          (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pFrameDec s.core.frame_dec ⋆
        region (c.pFrameDec + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
          (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
      array64 c.pScore s.scratch.score ⋆
      m7U32ARestLvlRsns c s ⋆ m7U32BRestFrame c s ⋆ m7TailRestScore c s ⋆ B ⋆ m7RestFrame c s R)
    (by rw [hub8]; ac_rfl) hlen.frame_trail_len (by omega) (by omega) (by omega)
    bytes64_zero_i32 hm1_f ?_
  intro m2 hm2
  have hm2_f :
      (((array (t := i32) c.pLevel (List.replicate c.max_vars 0#32) ⋆
          region (c.pLevel + BitVec.ofNat 64 (4 * c.max_vars))
            (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
        (array (t := i32) c.pReason s.core.rsns ⋆
          region (c.pReason + BitVec.ofNat 64 (4 * c.max_vars))
            (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
        (array (t := i32) c.pFrameTrail (List.replicate (c.max_vars + 1) 0#32) ⋆
          region (c.pFrameTrail + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
            (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
        (array (t := i32) c.pFrameDec s.core.frame_dec ⋆
          region (c.pFrameDec + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
            (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
        array64 c.pScore s.scratch.score ⋆
        m7U32ARestLvlRsns c s ⋆ m7U32BRestFrame c s ⋆ m7TailRestScore c s ⋆ B) ⋆
        m7RestFrame c s R) m2 := by
    rw [hub8] at hm2; exact Eq.mp (congrFun (by ac_rfl) m2) hm2
  have hw7 : (m7HdrTailWords c s)[7]? = some c.pReason := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq]; rfl
  c0_hsteps
  refine wp_load_m7Hdr_frame c s R 7 (by omega) 88#64 c.pReason hw7
    (hdr_off_eq _ _ 7 (by decide)) hm2_f ?_
  refine zt_fill_i32_pad hFill (a := c.pReason) (w := Full.u32FullBytes c.max_vars / 8)
    (used := c.max_vars) (val64 := 18446744073709551615#64) (v32 := 4294967295#32)
    (F := (array (t := i32) c.pLevel (List.replicate c.max_vars 0#32) ⋆
        region (c.pLevel + BitVec.ofNat 64 (4 * c.max_vars))
          (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pFrameTrail (List.replicate (c.max_vars + 1) 0#32) ⋆
        region (c.pFrameTrail + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
          (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
      (array (t := i32) c.pFrameDec s.core.frame_dec ⋆
        region (c.pFrameDec + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
          (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
      array64 c.pScore s.scratch.score ⋆
      m7U32ARestLvlRsns c s ⋆ m7U32BRestFrame c s ⋆ m7TailRestScore c s ⋆ B ⋆ m7RestFrame c s R)
    (by rw [hub8]; ac_rfl) hlen.rsns_len (by omega) (by omega) (by omega) bytes64_ff_i32 hm2_f ?_
  intro m3 hm3
  have hm3_f :
      (((array (t := i32) c.pLevel (List.replicate c.max_vars 0#32) ⋆
          region (c.pLevel + BitVec.ofNat 64 (4 * c.max_vars))
            (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
        (array (t := i32) c.pReason (List.replicate c.max_vars 4294967295#32) ⋆
          region (c.pReason + BitVec.ofNat 64 (4 * c.max_vars))
            (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
        (array (t := i32) c.pFrameTrail (List.replicate (c.max_vars + 1) 0#32) ⋆
          region (c.pFrameTrail + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
            (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
        (array (t := i32) c.pFrameDec s.core.frame_dec ⋆
          region (c.pFrameDec + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
            (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
        array64 c.pScore s.scratch.score ⋆
        m7U32ARestLvlRsns c s ⋆ m7U32BRestFrame c s ⋆ m7TailRestScore c s ⋆ B) ⋆
        m7RestFrame c s R) m3 := by
    rw [hub8] at hm3; exact Eq.mp (congrFun (by ac_rfl) m3) hm3
  have hw101 : (m7HdrTailWords c s)[101]? = some c.pFrameDec := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
      m7HdrTailWords2_eq]; rfl
  c0_hsteps
  refine wp_load_m7Hdr_frame c s R 101 (by omega) 840#64 c.pFrameDec hw101
    (hdr_off_eq _ _ 101 (by decide)) hm3_f ?_
  refine zt_fill_i32_pad hFill (a := c.pFrameDec) (w := Full.u32FullBytes c.max_vars / 8)
    (used := c.max_vars + 1) (val64 := 18446744073709551615#64) (v32 := 4294967295#32)
    (F := (array (t := i32) c.pLevel (List.replicate c.max_vars 0#32) ⋆
        region (c.pLevel + BitVec.ofNat 64 (4 * c.max_vars))
          (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pReason (List.replicate c.max_vars 4294967295#32) ⋆
        region (c.pReason + BitVec.ofNat 64 (4 * c.max_vars))
          (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pFrameTrail (List.replicate (c.max_vars + 1) 0#32) ⋆
        region (c.pFrameTrail + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
          (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
      array64 c.pScore s.scratch.score ⋆
      m7U32ARestLvlRsns c s ⋆ m7U32BRestFrame c s ⋆ m7TailRestScore c s ⋆ B ⋆ m7RestFrame c s R)
    (by rw [hub8]; ac_rfl) hlen.frame_dec_len (by omega) (by omega) (by omega) bytes64_ff_i32
    hm3_f ?_
  intro m4 hm4
  have hm4_f :
      (((array (t := i32) c.pLevel (List.replicate c.max_vars 0#32) ⋆
          region (c.pLevel + BitVec.ofNat 64 (4 * c.max_vars))
            (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
        (array (t := i32) c.pReason (List.replicate c.max_vars 4294967295#32) ⋆
          region (c.pReason + BitVec.ofNat 64 (4 * c.max_vars))
            (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
        (array (t := i32) c.pFrameTrail (List.replicate (c.max_vars + 1) 0#32) ⋆
          region (c.pFrameTrail + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
            (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
        (array (t := i32) c.pFrameDec (List.replicate (c.max_vars + 1) 4294967295#32) ⋆
          region (c.pFrameDec + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
            (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
        array64 c.pScore s.scratch.score ⋆
        m7U32ARestLvlRsns c s ⋆ m7U32BRestFrame c s ⋆ m7TailRestScore c s ⋆ B) ⋆
        m7RestFrame c s R) m4 := by
    rw [hub8] at hm4; exact Eq.mp (congrFun (by ac_rfl) m4) hm4
  have hw23 : (m7HdrTailWords c s)[23]? = some c.pScore := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq]; rfl
  c0_hsteps
  refine wp_load_m7Hdr_frame c s R 23 (by omega) 216#64 c.pScore hw23
    (hdr_off_eq _ _ 23 (by decide)) hm4_f ?_
  refine zt_fill_u64_exact hFill (a := c.pScore) (w := c.max_vars) (val64 := 0#64)
    (F := (array (t := i32) c.pLevel (List.replicate c.max_vars 0#32) ⋆
        region (c.pLevel + BitVec.ofNat 64 (4 * c.max_vars))
          (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pReason (List.replicate c.max_vars 4294967295#32) ⋆
        region (c.pReason + BitVec.ofNat 64 (4 * c.max_vars))
          (Full.u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pFrameTrail (List.replicate (c.max_vars + 1) 0#32) ⋆
        region (c.pFrameTrail + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
          (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
      (array (t := i32) c.pFrameDec (List.replicate (c.max_vars + 1) 4294967295#32) ⋆
        region (c.pFrameDec + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
          (Full.u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
      m7U32ARestLvlRsns c s ⋆ m7U32BRestFrame c s ⋆ m7TailRestScore c s ⋆ B ⋆ m7RestFrame c s R)
    (by ac_rfl) hlen.score_len (by omega) (by omega) hm4_f ?_
  intro m5 hm5
  let s1 : FullState := FullState.mk
    { s.core with
      lvl := List.replicate c.max_vars 0#32
      rsns := List.replicate c.max_vars 4294967295#32
      frame_trail := List.replicate (c.max_vars + 1) 0#32
      frame_dec := List.replicate (c.max_vars + 1) 4294967295#32 }
    { s.scratch with score := List.replicate c.max_vars 0#64 }
  have hm5' :
      (MemShrinkResU32A c s1 ⋆ MemShrinkResU32B c s1 ⋆ MemShrinkResTail c s1 ⋆ B ⋆
        m7RestFrame c s1 R) m5 := by
    have hst : m7RestFrame c s R = m7RestFrame c s1 R := by
      simp only [m7RestFrame, m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
        m7HdrTailWords2_eq, m7HdrTailWords3_eq]; rfl
    have hra : m7U32ARestLvlRsns c s = m7U32ARestLvlRsns c s1 := by
      simp only [m7U32ARestLvlRsns]; rfl
    have hrb : m7U32BRestFrame c s = m7U32BRestFrame c s1 := by
      simp only [m7U32BRestFrame]; rfl
    have hrt : m7TailRestScore c s = m7TailRestScore c s1 := by
      simp only [m7TailRestScore]; rfl
    rw [u32a_focus_lvl_rsns, u32b_focus_frame, resTail_focus_score, ← hst, ← hra, ← hrb, ← hrt]
    dsimp only [s1]
    exact Eq.mp (congrFun (by ac_rfl) m5) hm5
  exact hk m5 hm5'

private theorem bv64_mul4_eq (base : BitVec 64) (i : Nat) (h4 : 4 * i < 2 ^ 64)
    (hi : i < 2 ^ 64) :
    base + BitVec.ofNat 64 i * 4#64 = base + BitVec.ofNat 64 (4 * i) := by
  congr 1; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, show (4#64 : BitVec 64).toNat = 4 by decide, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h4,
    Nat.mul_comm, Nat.mod_eq_of_lt h4]

private theorem zt2_loop1_step_core (Γ : Env) (c : MemShrinkCfg) (sF : FullState)
    (R : Mem 64 → Prop) (Q : Post []) (X : XPost) {m : Mem 64}
    (i : Nat) (hi_mv : i < c.mv)
    (fl hp ps qp qn qs : List (BitVec 32))
    (hfl : fl.length = c.max_vars) (hhp : hp.length = c.max_vars) (hps : ps.length = c.max_vars)
    (hqp : qp.length = c.max_vars) (hqn : qn.length = c.max_vars) (hqs : qs.length = c.max_vars)
    (hm : m7LoopsMem c sF fl hp ps qp qn qs R m)
    (vflag : Val i32) (J : Cont [i64])
    (hnext : ∀ (fl' hp' ps' qp' qn' qs' : List (BitVec 32)) (m' : Mem 64),
      fl'.length = c.max_vars → hp'.length = c.max_vars → ps'.length = c.max_vars →
      qp'.length = c.max_vars → qn'.length = c.max_vars → qs'.length = c.max_vars →
      m7LoopsMem c sF fl' hp' ps' qp' qn' qs' R m' →
      J (BitVec.ofNat 64 (i + 1), ()) m') :
    wp Γ Q X
      (Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var (BitVec.ofNat 64 i), Arg.imm 4, ())) fun p0 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pFlags, Arg.var p0.fst, ())) fun p1 =>
          Expr.store (Arg.var vflag) (Arg.var p1.fst) (
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var (BitVec.ofNat 64 i), Arg.imm 4, ()))
              fun p2 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pHeap, Arg.var p2.fst, ())) fun p3 =>
                Expr.let_ (Op.mk (OpCode.trunc 64 32) (Arg.var (BitVec.ofNat 64 i), ())) fun p4 =>
                  Expr.store (Arg.var p4.fst) (Arg.var p3.fst) (
                    Expr.let_ (Op.mk (OpCode.mul i64)
                        (Arg.var (BitVec.ofNat 64 i), Arg.imm 4, ())) fun p5 =>
                      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pPos, Arg.var p5.fst, ()))
                        fun p6 =>
                        Expr.let_ (Op.mk (OpCode.trunc 64 32) (Arg.var (BitVec.ofNat 64 i), ()))
                          fun p7 =>
                          Expr.store (Arg.var p7.fst) (Arg.var p6.fst) (
                            Expr.let_ (Op.mk (OpCode.mul i64)
                                (Arg.var (BitVec.ofNat 64 i), Arg.imm 4, ())) fun p8 =>
                              Expr.let_ (Op.mk (OpCode.add i64)
                                  (Arg.var c.pQStamp, Arg.var p8.fst, ())) fun p9 =>
                                Expr.let_ (Op.mk (OpCode.add i64)
                                    (Arg.var (BitVec.ofNat 64 i), Arg.imm 1, ())) fun p10 =>
                                  Expr.let_ (Op.mk (OpCode.trunc 64 32) (Arg.var p10.fst, ()))
                                    fun p11 =>
                                    Expr.store (Arg.var p11.fst) (Arg.var p9.fst) (
                                      Expr.let_ (Op.mk (OpCode.mul i64)
                                          (Arg.var (BitVec.ofNat 64 i), Arg.imm 4, ())) fun p12 =>
                                        Expr.let_ (Op.mk (OpCode.add i64)
                                            (Arg.var c.pQPrev, Arg.var p12.fst, ())) fun p13 =>
                                          Expr.group (sig := [[i32]]) (fun _Js1 =>
                                            Blocks.cons (fun (bqp : Tup Val [i32]) =>
                                            Expr.store (Arg.var bqp.fst) (Arg.var p13.fst) (
                                              Expr.let_ (Op.mk (OpCode.mul i64)
                                                  (Arg.var (BitVec.ofNat 64 i), Arg.imm 4, ()))
                                                  fun p14 =>
                                                Expr.let_ (Op.mk (OpCode.add i64)
                                                    (Arg.var c.pQNext, Arg.var p14.fst, ()))
                                                    fun p15 =>
                                                  Expr.group (sig := [[i32]]) (fun _Js2 =>
                                                    Blocks.cons (fun (bqn : Tup Val [i32]) =>
                                                    Expr.store (Arg.var bqn.fst) (Arg.var p15.fst) (
                                                      Expr.let_ (Op.mk (OpCode.add i64)
                                                          (Arg.var (BitVec.ofNat 64 i),
                                                            Arg.imm 1, ())) fun p16 =>
                                                        Expr.jump J (Arg.var p16.fst, ())))
                                                    Blocks.nil)
                                                    fun Js2 =>
                                                      Expr.let_ (Op.mk (OpCode.add i64)
                                                          (Arg.var (BitVec.ofNat 64 i),
                                                            Arg.imm 1, ())) fun p17 =>
                                                        Expr.let_ (Op.mk
                                                            (OpCode.cmp CmpOp.uge i64 Ty.bool)
                                                            (Arg.var p17.fst,
                                                              Arg.var (BitVec.ofNat 64 c.mv), ()))
                                                            fun p18 =>
                                                          Expr.jnz (Arg.var p18.fst)
                                                            (Expr.jump Js2.fst
                                                              (Arg.imm 4294967295#32, ()))
                                                            (Expr.let_ (Op.mk (OpCode.add i64)
                                                                (Arg.var (BitVec.ofNat 64 i),
                                                                  Arg.imm 1, ())) fun p19 =>
                                                              Expr.let_ (Op.mk (OpCode.trunc 64 32)
                                                                  (Arg.var p19.fst, ())) fun p20 =>
                                                                Expr.jump Js2.fst
                                                                  (Arg.var p20.fst, ()))))
                                            Blocks.nil)
                                            fun Js1 =>
                                              Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i64 Ty.bool)
                                                  (Arg.var (BitVec.ofNat 64 i), Arg.imm 0, ()))
                                                  fun p21 =>
                                                Expr.jnz (Arg.var p21.fst)
                                                  (Expr.jump Js1.fst (Arg.imm 4294967295#32, ()))
                                                  (Expr.let_ (Op.mk (OpCode.sub i64)
                                                      (Arg.var (BitVec.ofNat 64 i),
                                                        Arg.imm 1, ())) fun p22 =>
                                                    Expr.let_ (Op.mk (OpCode.trunc 64 32)
                                                        (Arg.var p22.fst, ())) fun p23 =>
                                                      Expr.jump Js1.fst
                                                        (Arg.var p23.fst, ()))))))) m := by
  have hi_mx : i < c.max_vars := by
    have := c.hbva; omega
  have h4i : 4 * i < 2 ^ 64 := by
    have := c.hmaxv; unfold Examples.LratBytes.dimacsBound at *; omega
  have hi64 : i < 2 ^ 64 := by omega
  c0_hsteps
  have hm0 : (array (t := i32) c.pFlags fl ⋆ (array (t := i32) c.pHeap hp ⋆
      array (t := i32) c.pPos ps ⋆ array (t := i32) c.pQPrev qp ⋆
      array (t := i32) c.pQNext qn ⋆ array (t := i32) c.pQStamp qs ⋆ m7LoopsRest c sF R)) m := by
    unfold m7LoopsMem at hm; exact Eq.mp (congrFun (by ac_rfl) m) hm
  refine wp_store_array (i := i) (by decide) (bv64_mul4_eq c.pFlags i h4i hi64)
    (by omega) hm0 ?_
  intro m1 hm1; let fl' := fl.set i vflag
  c0_hstep; c0_hstep; c0_hstep
  have hm1s : (array (t := i32) c.pHeap hp ⋆ (array (t := i32) c.pFlags fl' ⋆
      array (t := i32) c.pPos ps ⋆ array (t := i32) c.pQPrev qp ⋆
      array (t := i32) c.pQNext qn ⋆ array (t := i32) c.pQStamp qs ⋆
      m7LoopsRest c sF R)) m1 := Eq.mp (congrFun (by ac_rfl) m1) hm1
  refine wp_store_array (i := i) (by decide) (bv64_mul4_eq c.pHeap i h4i hi64)
    (by omega) hm1s ?_
  intro m2 hm2; let hp' := hp.set i (BitVec.setWidth 32 (BitVec.ofNat 64 i))
  dsimp only [Arg.val] at hm2
  c0_hstep; c0_hstep; c0_hstep
  have hm2' : (array (t := i32) c.pHeap hp' ⋆ (array (t := i32) c.pFlags fl' ⋆
      array (t := i32) c.pPos ps ⋆ array (t := i32) c.pQPrev qp ⋆
      array (t := i32) c.pQNext qn ⋆ array (t := i32) c.pQStamp qs ⋆
      m7LoopsRest c sF R)) m2 := hm2
  have hm2s : (array (t := i32) c.pPos ps ⋆ (array (t := i32) c.pFlags fl' ⋆
      array (t := i32) c.pHeap hp' ⋆ array (t := i32) c.pQPrev qp ⋆
      array (t := i32) c.pQNext qn ⋆ array (t := i32) c.pQStamp qs ⋆
      m7LoopsRest c sF R)) m2 := Eq.mp (congrFun (by ac_rfl) m2) hm2'
  refine wp_store_array (i := i) (by decide) (bv64_mul4_eq c.pPos i h4i hi64)
    (by omega) hm2s ?_
  intro m3 hm3; let ps' := ps.set i (BitVec.setWidth 32 (BitVec.ofNat 64 i))
  dsimp only [Arg.val] at hm3
  c0_hstep; c0_hstep; c0_hstep; c0_hstep
  have hm3' : (array (t := i32) c.pPos ps' ⋆ (array (t := i32) c.pFlags fl' ⋆
      array (t := i32) c.pHeap hp' ⋆ array (t := i32) c.pQPrev qp ⋆
      array (t := i32) c.pQNext qn ⋆ array (t := i32) c.pQStamp qs ⋆
      m7LoopsRest c sF R)) m3 := hm3
  have hm3s : (array (t := i32) c.pQStamp qs ⋆ (array (t := i32) c.pFlags fl' ⋆
      array (t := i32) c.pHeap hp' ⋆ array (t := i32) c.pPos ps' ⋆
      array (t := i32) c.pQPrev qp ⋆ array (t := i32) c.pQNext qn ⋆
      m7LoopsRest c sF R)) m3 := Eq.mp (congrFun (by ac_rfl) m3) hm3'
  refine wp_store_array (i := i) (by decide) (bv64_mul4_eq c.pQStamp i h4i hi64)
    (by omega) hm3s ?_
  intro m4 hm4
  let qs' := qs.set i (BitVec.truncate 32 (BitVec.ofNat 64 i + 1))
  c0_hstep; c0_hstep
  refine wp_join_state1 (α := BitVec 32) id (fun _ m' => m4 = m') ?_ ?_
  · rintro Js1 bqp m4' rfl
    rw [Blocks.get_here]
    have hm4s : (array (t := i32) c.pQPrev qp ⋆ (array (t := i32) c.pFlags fl' ⋆
        array (t := i32) c.pHeap hp' ⋆ array (t := i32) c.pPos ps' ⋆
        array (t := i32) c.pQNext qn ⋆ array (t := i32) c.pQStamp qs' ⋆
        m7LoopsRest c sF R)) m4 := Eq.mp (congrFun (by ac_rfl) m4) hm4
    refine wp_store_array (i := i) (by decide) (bv64_mul4_eq c.pQPrev i h4i hi64)
      (by omega) hm4s ?_
    intro m5 hm5; let qp' := qp.set i bqp
    c0_hstep; c0_hstep
    refine wp_join_state1 (α := BitVec 32) id (fun _ m' => m5 = m') ?_ ?_
    · rintro Js2 bqn m5' rfl
      rw [Blocks.get_here]
      have hm5s : (array (t := i32) c.pQNext qn ⋆ (array (t := i32) c.pFlags fl' ⋆
          array (t := i32) c.pHeap hp' ⋆ array (t := i32) c.pPos ps' ⋆
          array (t := i32) c.pQPrev qp' ⋆ array (t := i32) c.pQStamp qs' ⋆
          m7LoopsRest c sF R)) m5 := Eq.mp (congrFun (by ac_rfl) m5) hm5
      refine wp_store_array (i := i) (by decide) (bv64_mul4_eq c.pQNext i h4i hi64)
        (by omega) hm5s ?_
      intro m6 hm6; let qn' := qn.set i bqn
      c0_hstep; c0_hstep
      have hinc : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        simp [Nat.mod_eq_of_lt (by omega : i + 1 < 2 ^ 64),
          Nat.mod_eq_of_lt hi64]
      rw [hinc]
      have hm6' : m7LoopsMem c sF fl' hp' ps' qp' qn' qs' R m6 := by
        unfold m7LoopsMem; exact Eq.mp (congrFun (by ac_rfl) m6) hm6
      exact hnext fl' hp' ps' qp' qn' qs' m6 (by simp [fl', hfl]) (by simp [hp', hhp])
        (by simp [ps', hps]) (by simp [qp', hqp]) (by simp [qn', hqn]) (by simp [qs', hqs]) hm6'
    · intro Js2 hJs2; c0_hsplit <;> (c0_hsteps; exact hJs2 _ m5 rfl)
  · intro Js1 hJs1; c0_hsplit <;> (c0_hsteps; exact hJs1 _ m4 rfl)

private abbrev zt2Loop2StepExpr (c : MemShrinkCfg) (J : Cont [i64]) (v : BitVec 64) :
    Expr Val Cont [] :=
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var v, Arg.imm 4, ())) fun p0 =>
    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pFlags, Arg.var p0.fst, ())) fun p1 =>
      Expr.store (t := i32) (Arg.imm (t := i32) 0#32) (Arg.var p1.fst) (
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var v, Arg.imm 4, ())) fun p2 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pHeap, Arg.var p2.fst, ())) fun p3 =>
            Expr.store (t := i32) (Arg.imm (t := i32) 0#32) (Arg.var p3.fst) (
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var v, Arg.imm 4, ())) fun p4 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pPos, Arg.var p4.fst, ())) fun p5 =>
                  Expr.store (t := i32) (Arg.imm (t := i32) 4294967295#32) (Arg.var p5.fst) (
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var v, Arg.imm 4, ())) fun p6 =>
                      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pQPrev, Arg.var p6.fst, ()))
                        fun p7 =>
                        Expr.store (t := i32) (Arg.imm (t := i32) 4294967295#32) (Arg.var p7.fst) (
                          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var v, Arg.imm 4, ())) fun p8 =>
                            Expr.let_ (Op.mk (OpCode.add i64)
                                (Arg.var c.pQNext, Arg.var p8.fst, ())) fun p9 =>
                              Expr.store (t := i32) (Arg.imm (t := i32) 4294967295#32)
                                (Arg.var p9.fst) (
                                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var v, Arg.imm 4, ()))
                                  fun p10 =>
                                  Expr.let_ (Op.mk (OpCode.add i64)
                                      (Arg.var c.pQStamp, Arg.var p10.fst, ())) fun p11 =>
                                    Expr.store (t := i32) (Arg.imm (t := i32) 0#32)
                                      (Arg.var p11.fst) (
                                      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var v, Arg.imm 1, ()))
                                        fun p12 => Expr.jump J (Arg.var p12.fst, ())))))))

private theorem zt2_loop2_step_core (Γ : Env) (c : MemShrinkCfg) (sF : FullState)
    (R : Mem 64 → Prop) (Q : Post []) (X : XPost) {m : Mem 64}
    (i : Nat) (hi_mx : i < c.max_vars)
    (fl hp ps qp qn qs : List (BitVec 32))
    (hfl : fl.length = c.max_vars) (hhp : hp.length = c.max_vars) (hps : ps.length = c.max_vars)
    (hqp : qp.length = c.max_vars) (hqn : qn.length = c.max_vars) (hqs : qs.length = c.max_vars)
    (hm : m7LoopsMem c sF fl hp ps qp qn qs R m) (J : Cont [i64])
    (hnext : ∀ (fl' hp' ps' qp' qn' qs' : List (BitVec 32)) (m' : Mem 64),
      fl'.length = c.max_vars → hp'.length = c.max_vars → ps'.length = c.max_vars →
      qp'.length = c.max_vars → qn'.length = c.max_vars → qs'.length = c.max_vars →
      m7LoopsMem c sF fl' hp' ps' qp' qn' qs' R m' →
      J (BitVec.ofNat 64 (i + 1), ()) m') :
    wp Γ Q X
      (Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var (BitVec.ofNat 64 i), Arg.imm 4, ())) fun p0 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pFlags, Arg.var p0.fst, ())) fun p1 =>
          Expr.store (t := i32) (Arg.imm (t := i32) 0#32) (Arg.var p1.fst) (
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var (BitVec.ofNat 64 i), Arg.imm 4, ()))
              fun p2 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pHeap, Arg.var p2.fst, ())) fun p3 =>
                Expr.store (t := i32) (Arg.imm (t := i32) 0#32) (Arg.var p3.fst) (
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var (BitVec.ofNat 64 i), Arg.imm 4, ()))
                    fun p4 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pPos, Arg.var p4.fst, ()))
                      fun p5 =>
                      Expr.store (t := i32) (Arg.imm (t := i32) 4294967295#32) (Arg.var p5.fst) (
                        Expr.let_ (Op.mk (OpCode.mul i64)
                            (Arg.var (BitVec.ofNat 64 i), Arg.imm 4, ())) fun p6 =>
                          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pQPrev, Arg.var p6.fst, ()))
                            fun p7 =>
                            Expr.store (t := i32) (Arg.imm (t := i32) 4294967295#32)
                              (Arg.var p7.fst) (
                              Expr.let_ (Op.mk (OpCode.mul i64)
                                  (Arg.var (BitVec.ofNat 64 i), Arg.imm 4, ())) fun p8 =>
                                Expr.let_ (Op.mk (OpCode.add i64)
                                    (Arg.var c.pQNext, Arg.var p8.fst, ())) fun p9 =>
                                  Expr.store (t := i32) (Arg.imm (t := i32) 4294967295#32)
                                    (Arg.var p9.fst) (
                                    Expr.let_ (Op.mk (OpCode.mul i64)
                                        (Arg.var (BitVec.ofNat 64 i), Arg.imm 4, ())) fun p10 =>
                                      Expr.let_ (Op.mk (OpCode.add i64)
                                          (Arg.var c.pQStamp, Arg.var p10.fst, ())) fun p11 =>
                                        Expr.store (t := i32) (Arg.imm (t := i32) 0#32)
                                          (Arg.var p11.fst) (
                                          Expr.let_ (Op.mk (OpCode.add i64)
                                              (Arg.var (BitVec.ofNat 64 i), Arg.imm 1, ()))
                                              fun p12 =>
                                            Expr.jump J (Arg.var p12.fst, ())))))))) m := by
  have h4i : 4 * i < 2 ^ 64 := by
    have := c.hmaxv; unfold Examples.LratBytes.dimacsBound at *; omega
  have hi64 : i < 2 ^ 64 := by omega
  c0_hsteps
  have hm0 : (array (t := i32) c.pFlags fl ⋆ (array (t := i32) c.pHeap hp ⋆
      array (t := i32) c.pPos ps ⋆ array (t := i32) c.pQPrev qp ⋆
      array (t := i32) c.pQNext qn ⋆ array (t := i32) c.pQStamp qs ⋆ m7LoopsRest c sF R)) m := by
    unfold m7LoopsMem at hm; exact Eq.mp (congrFun (by ac_rfl) m) hm
  refine wp_store_array (i := i) (by decide) (bv64_mul4_eq c.pFlags i h4i hi64)
    (by omega) hm0 ?_
  intro m1 hm1; let fl' := fl.set i 0#32
  c0_hstep; c0_hstep
  have hm1s : (array (t := i32) c.pHeap hp ⋆ (array (t := i32) c.pFlags fl' ⋆
      array (t := i32) c.pPos ps ⋆ array (t := i32) c.pQPrev qp ⋆
      array (t := i32) c.pQNext qn ⋆ array (t := i32) c.pQStamp qs ⋆
      m7LoopsRest c sF R)) m1 := Eq.mp (congrFun (by ac_rfl) m1) hm1
  refine wp_store_array (i := i) (by decide) (bv64_mul4_eq c.pHeap i h4i hi64)
    (by omega) hm1s ?_
  intro m2 hm2; let hp' := hp.set i 0#32
  c0_hstep; c0_hstep
  have hm2' : (array (t := i32) c.pHeap hp' ⋆ (array (t := i32) c.pFlags fl' ⋆
      array (t := i32) c.pPos ps ⋆ array (t := i32) c.pQPrev qp ⋆
      array (t := i32) c.pQNext qn ⋆ array (t := i32) c.pQStamp qs ⋆
      m7LoopsRest c sF R)) m2 := hm2
  have hm2s : (array (t := i32) c.pPos ps ⋆ (array (t := i32) c.pFlags fl' ⋆
      array (t := i32) c.pHeap hp' ⋆ array (t := i32) c.pQPrev qp ⋆
      array (t := i32) c.pQNext qn ⋆ array (t := i32) c.pQStamp qs ⋆
      m7LoopsRest c sF R)) m2 := Eq.mp (congrFun (by ac_rfl) m2) hm2'
  refine wp_store_array (i := i) (by decide) (bv64_mul4_eq c.pPos i h4i hi64)
    (by omega) hm2s ?_
  intro m3 hm3; let ps' := ps.set i 4294967295#32
  c0_hstep; c0_hstep
  have hm3s : (array (t := i32) c.pQPrev qp ⋆ (array (t := i32) c.pFlags fl' ⋆
      array (t := i32) c.pHeap hp' ⋆ array (t := i32) c.pPos ps' ⋆
      array (t := i32) c.pQNext qn ⋆ array (t := i32) c.pQStamp qs ⋆
      m7LoopsRest c sF R)) m3 := by
    dsimp only [ps']; exact Eq.mp (congrFun (by ac_rfl) m3) hm3
  refine wp_store_array (i := i) (by decide) (bv64_mul4_eq c.pQPrev i h4i hi64)
    (by omega) hm3s ?_
  intro m4 hm4; let qp' := qp.set i 4294967295#32
  c0_hstep; c0_hstep
  have hm4s : (array (t := i32) c.pQNext qn ⋆ (array (t := i32) c.pFlags fl' ⋆
      array (t := i32) c.pHeap hp' ⋆ array (t := i32) c.pPos ps' ⋆
      array (t := i32) c.pQPrev qp' ⋆ array (t := i32) c.pQStamp qs ⋆
      m7LoopsRest c sF R)) m4 := Eq.mp (congrFun (by ac_rfl) m4) hm4
  refine wp_store_array (i := i) (by decide) (bv64_mul4_eq c.pQNext i h4i hi64)
    (by omega) hm4s ?_
  intro m5 hm5; let qn' := qn.set i 4294967295#32
  c0_hstep; c0_hstep
  have hm5s : (array (t := i32) c.pQStamp qs ⋆ (array (t := i32) c.pFlags fl' ⋆
      array (t := i32) c.pHeap hp' ⋆ array (t := i32) c.pPos ps' ⋆
      array (t := i32) c.pQPrev qp' ⋆ array (t := i32) c.pQNext qn' ⋆
      m7LoopsRest c sF R)) m5 := Eq.mp (congrFun (by ac_rfl) m5) hm5
  refine wp_store_array (i := i) (by decide) (bv64_mul4_eq c.pQStamp i h4i hi64)
    (by omega) hm5s ?_
  intro m6 hm6; let qs' := qs.set i 0#32
  c0_hsteps
  have hinc : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp [Nat.mod_eq_of_lt (by omega : i + 1 < 2 ^ 64), Nat.mod_eq_of_lt hi64]
  rw [hinc]
  have hm6' : m7LoopsMem c sF fl' hp' ps' qp' qn' qs' R m6 := by
    unfold m7LoopsMem; exact Eq.mp (congrFun (by ac_rfl) m6) hm6
  exact hnext fl' hp' ps' qp' qn' qs' m6 (by simp [fl', hfl]) (by simp [hp', hhp])
    (by simp [ps', hps]) (by simp [qp', hqp]) (by simp [qn', hqn]) (by simp [qs', hqs]) hm6'

private theorem zt2_loop2_wp (Γ : Env) (c : MemShrinkCfg) (sF : FullState)
    (R : Mem 64 → Prop) (Q : Post []) (X : XPost) {mL : Mem 64}
    (fl hp ps qp qn qs : List (BitVec 32))
    (hfl : fl.length = c.max_vars) (hhp : hp.length = c.max_vars) (hps : ps.length = c.max_vars)
    (hqp : qp.length = c.max_vars) (hqn : qn.length = c.max_vars) (hqs : qs.length = c.max_vars)
    (hmL : m7LoopsMem c sF fl hp ps qp qn qs R mL)
    (hdone : ∀ (fl2 hp2 ps2 qp2 qn2 qs2 : List (BitVec 32)) (mR : Mem 64),
      fl2.length = c.max_vars → hp2.length = c.max_vars → ps2.length = c.max_vars →
      qp2.length = c.max_vars → qn2.length = c.max_vars → qs2.length = c.max_vars →
      m7LoopsMem c sF fl2 hp2 ps2 qp2 qn2 qs2 R mR → Q () mR) :
    wp Γ Q X
      (Expr.group (sig := [[i64]])
        (fun Js2 => Blocks.cons (fun x2 =>
          Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool)
              (Arg.var x2.fst, Arg.var (BitVec.ofNat 64 c.max_vars), ())) fun p1 =>
            Expr.jnz (Arg.var p1.fst) (zt2Loop2StepExpr c Js2.fst x2.fst) (Expr.ret ()))
          Blocks.nil)
        (fun Js2 => Expr.jump Js2.fst (Arg.var (BitVec.ofNat 64 c.mv), ()))) mL := by
  refine wp_loop_group (ts := [i64]) (fun (n2 : Nat) (x2 : Tup Val [i64]) (mR : Mem 64) =>
    ∃ (j : Nat) (fl2 hp2 ps2 qp2 qn2 qs2 : List (BitVec 32)),
      j ≤ c.max_vars ∧ j + n2 = c.max_vars ∧ x2 = (BitVec.ofNat 64 j, ()) ∧
      fl2.length = c.max_vars ∧ hp2.length = c.max_vars ∧ ps2.length = c.max_vars ∧
      qp2.length = c.max_vars ∧ qn2.length = c.max_vars ∧ qs2.length = c.max_vars ∧
      m7LoopsMem c sF fl2 hp2 ps2 qp2 qn2 qs2 R mR) ?_ ?_
  · rintro J2 n2 x2 mR hIH2 ⟨j, fl2, hp2, ps2, qp2, qn2, qs2, hj_le, hjn, rfl,
      hfl2, hhp2, hps2, hqp2, hqn2, hqs2, hmR⟩
    c0_hsplit
    · have hj_lt : j < c.max_vars := by
        have hmx64 : c.max_vars < 2 ^ 64 := by
          have := c.hmaxv; unfold Examples.LratBytes.dimacsBound at *; omega
        have hj64 : j < 2 ^ 64 := Nat.lt_of_le_of_lt hj_le hmx64
        rw [Nat.mod_eq_of_lt hj64, Nat.mod_eq_of_lt hmx64] at hc; exact hc
      cases hn2 : n2 with
      | zero => omega
      | succ n2' =>
        unfold zt2Loop2StepExpr
        exact zt2_loop2_step_core Γ c sF R Q X j hj_lt fl2 hp2 ps2 qp2 qn2 qs2
          hfl2 hhp2 hps2 hqp2 hqn2 hqs2 hmR J2 (fun fl' hp' ps' qp' qn' qs' m'
            hfl' hhp' hps' hqp' hqn' hqs' hm' =>
            hIH2 n2' (BitVec.ofNat 64 (j + 1), ()) m' (by omega)
              ⟨j + 1, fl', hp', ps', qp', qn', qs', by omega, by omega, rfl,
                hfl', hhp', hps', hqp', hqn', hqs', hm'⟩)
    · c0_hsteps
      exact hdone fl2 hp2 ps2 qp2 qn2 qs2 mR hfl2 hhp2 hps2 hqp2 hqn2 hqs2 hmR
  · intro J2 hJ2; c0_hsteps
    exact hJ2 (c.max_vars - c.mv) (BitVec.ofNat 64 c.mv, ()) mL
      ⟨c.mv, fl, hp, ps, qp, qn, qs, by have := c.hbva; omega,
        by have := c.hbva; omega, rfl, hfl, hhp, hps, hqp, hqn, hqs, hmL⟩

theorem full_zero_tables2_m7_wp (Γ : Env)
    (hFill : EnvSpec Γ "full_fill_u64_m7" m7FillU64Spec) :
    ∀ a m Q X, m7ZeroTables2Spec a m Q X → Func.wp Γ full_zero_tables2_m7_body a m Q X := by
  rintro ⟨h, _⟩ m Q X hsp
  rw [m7ZeroTables2Spec_eq] at hsp
  rcases hsp with ⟨c, s, R, rfl, hlen, hm, hpost⟩
  unfold full_zero_tables2_m7_body; dsimp only [Func.wp]
  rcases m7Cfg_sizes_bound c with ⟨hmv8, _, hmb64, hub64, _, _, _, _, _, _, _, _, _, _⟩
  have hfit := m7Cfg_ptrs_fit c
  have hmx : c.max_vars < 2 * Examples.LratBytes.dimacsBound := c.hmaxv
  have hm_top : (MemShrinkResBytes c s ⋆
      (MemShrinkResU32A c s ⋆ MemShrinkResU32B c s ⋆ MemShrinkResTail c s ⋆ MemShrinkLitMark c s) ⋆
      m7RestFrame c s R) m := by
    rw [MemShrinkMem_eq, MemShrinkResArrays_eq] at hm
    unfold m7RestFrame; exact Eq.mp (congrFun (by ac_rfl) m) hm
  refine wp_load_m7Mv_frame c s R hm_top ?_
  c0_hsteps
  have hw92 : (m7HdrTailWords c s)[92]? = some (BitVec.ofNat 64 c.max_vars) := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
      m7HdrTailWords2_eq]; rfl
  refine wp_load_m7Hdr_frame c s R 92 (by omega) 768#64 (BitVec.ofNat 64 c.max_vars) hw92
    (hdr_off_eq _ _ 92 (by decide)) hm_top ?_
  c0_hsteps
  have hmb_eq : ((BitVec.ofNat 64 c.max_vars + (7 : BitVec 64)) &&& ~~~(7 : BitVec 64)) >>>
      (3 : Nat) = BitVec.ofNat 64 (markBytes c.max_vars / 8) := by
    rw [show (3 : Nat) = (BitVec.signExtend 64 (3 : BitVec 32)).toNat % 64 from by decide,
      fp_mb_eq hmx, fp_shr_sext3 hmb64]
  have hub_eq : ((((BitVec.ofNat 64 c.max_vars + (1 : BitVec 64)) <<< (2 : Nat)) +
      (7 : BitVec 64)) &&& ~~~(7 : BitVec 64)) >>> (3 : Nat) =
      BitVec.ofNat 64 (Full.u32FullBytes c.max_vars / 8) := by
    rw [show (2 : Nat) = (BitVec.signExtend 64 (2 : BitVec 32)).toNat % 64 from by decide,
      show (3 : Nat) = (BitVec.signExtend 64 (3 : BitVec 32)).toNat % 64 from by decide,
      fp_ub_eq hmx, fp_shr_sext3 hub64]
  rw [hmb_eq, hub_eq]; dsimp only
  refine zt2_bytes4_wp Γ hFill c s
    (MemShrinkResU32A c s ⋆ MemShrinkResU32B c s ⋆ MemShrinkResTail c s ⋆ MemShrinkLitMark c s)
    R hlen ⟨hfit.2.1, hfit.2.2.1, hfit.2.2.2.1, hfit.2.2.2.2.1⟩ hmb64 hm_top ?_
  intro m1 hm1
  let s1 := zt2BytesState s c.max_vars
  have hlen1 : MemShrinkLengthsOk c s1 :=
    { hlen with
      mrk_len := by simp [s1, zt2BytesState]
      phases_len := by simp [s1, zt2BytesState]
      phases_target_len := by simp [s1, zt2BytesState]
      phases_best_len := by simp [s1, zt2BytesState] }
  have hm1_u : (MemShrinkResU32A c s1 ⋆ MemShrinkResU32B c s1 ⋆ MemShrinkResTail c s1 ⋆
      (MemShrinkResBytes c s1 ⋆ MemShrinkLitMark c s1) ⋆ m7RestFrame c s1 R) m1 := by
    rw [show MemShrinkResU32A c s1 = MemShrinkResU32A c s from by
        simp only [MemShrinkResU32A_eq]; rfl,
      show MemShrinkResU32B c s1 = MemShrinkResU32B c s from by
        simp only [MemShrinkResU32B_eq]; rfl,
      show MemShrinkResTail c s1 = MemShrinkResTail c s from by
        simp only [MemShrinkResTail_eq]; rfl,
      show MemShrinkLitMark c s1 = MemShrinkLitMark c s from by
        simp only [MemShrinkLitMark_eq]; rfl]
    exact Eq.mp (congrFun (by ac_rfl) m1) hm1
  refine zt2_u32_score5_wp Γ hFill c s1
    (MemShrinkResBytes c s1 ⋆ MemShrinkLitMark c s1) R hlen1
    ⟨hfit.2.2.2.2.2.2.1, hfit.2.2.2.2.2.2.2.1,
      hfit.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hfit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ hub64 hmv8 hm1_u ?_
  intro m2 hm2
  let sF : FullState := zt2FillState s1 c.max_vars
  have hlenF : MemShrinkLengthsOk c sF :=
    { hlen1 with
      lvl_len := by simp [sF, zt2FillState]
      rsns_len := by simp [sF, zt2FillState]
      frame_trail_len := by simp [sF, zt2FillState]
      frame_dec_len := by simp [sF, zt2FillState]
      score_len := by simp [sF, zt2FillState] }
  have hm2_full : (MemShrinkMem c sF ⋆ R) m2 := by
    have hrb : MemShrinkResBytes c s1 = MemShrinkResBytes c sF := by
      simp only [MemShrinkResBytes_eq]; rfl
    have hlm : MemShrinkLitMark c s1 = MemShrinkLitMark c sF := by
      simp only [MemShrinkLitMark_eq]; rfl
    have hm2_rf : (MemShrinkResU32A c sF ⋆ MemShrinkResU32B c sF ⋆
        MemShrinkResTail c sF ⋆ (MemShrinkResBytes c s1 ⋆ MemShrinkLitMark c s1) ⋆
        m7RestFrame c sF R) m2 := by
      dsimp only [sF]; exact hm2
    unfold m7RestFrame at hm2_rf
    rw [MemShrinkMem_eq, MemShrinkResArrays_eq, ← hrb, ← hlm]
    exact Eq.mp (congrFun (by ac_rfl) m2) hm2_rf
  have hm_l0 : ((MemShrinkResArrays c sF ⋆ MemShrinkLitMark c sF) ⋆ m7RestFrame c sF R) m2 := by
    rw [MemShrinkMem_eq] at hm2_full; unfold m7RestFrame
    exact Eq.mp (congrFun (by ac_rfl) m2) hm2_full
  have hw96 : (m7HdrTailWords c sF)[96]? = some c.pFlags := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq,
      m7HdrTailWords2_eq]; rfl
  have hw21 : (m7HdrTailWords c sF)[21]? = some c.pHeap := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq]; rfl
  have hw22 : (m7HdrTailWords c sF)[22]? = some c.pPos := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq]; rfl
  have hw44 : (m7HdrTailWords c sF)[44]? = some c.pQStamp := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq]; rfl
  have hw42 : (m7HdrTailWords c sF)[42]? = some c.pQPrev := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq]; rfl
  have hw43 : (m7HdrTailWords c sF)[43]? = some c.pQNext := by
    simp only [m7HdrTailWords_eq, m7HdrTailWords0_eq, m7HdrTailWords1_eq]; rfl
  c0_hsteps
  refine wp_load_m7Hdr_frame c sF R 96 (by omega) 800#64 c.pFlags hw96
    (hdr_off_eq _ _ 96 (by decide)) hm_l0 ?_
  c0_hsteps
  refine wp_load_m7Hdr_frame c sF R 21 (by omega) 200#64 c.pHeap hw21
    (hdr_off_eq _ _ 21 (by decide)) hm_l0 ?_
  c0_hsteps
  refine wp_load_m7Hdr_frame c sF R 22 (by omega) 208#64 c.pPos hw22
    (hdr_off_eq _ _ 22 (by decide)) hm_l0 ?_
  c0_hsteps
  refine wp_load_m7Hdr_frame c sF R 44 (by omega) 384#64 c.pQStamp hw44
    (hdr_off_eq _ _ 44 (by decide)) hm_l0 ?_
  c0_hsteps
  refine wp_load_m7Hdr_frame c sF R 42 (by omega) 368#64 c.pQPrev hw42
    (hdr_off_eq _ _ 42 (by decide)) hm_l0 ?_
  c0_hsteps
  refine wp_load_m7Hdr_frame c sF R 43 (by omega) 376#64 c.pQNext hw43
    (hdr_off_eq _ _ 43 (by decide)) hm_l0 ?_
  c0_hsteps_nogrp
  have hm_loops0 : m7LoopsMem c sF sF.core.flags sF.scratch.heap sF.scratch.pos
      sF.scratch.q_prev sF.scratch.q_next sF.scratch.q_stamp R m2 := by
    rw [← memShrink_eq_loopsMem]; exact hm2_full
  refine wp_loop_group (ts := [i64]) (fun (n : Nat) (x : Tup Val [i64]) (m' : Mem 64) =>
    ∃ (i : Nat) (fl hp ps qp qn qs : List (BitVec 32)),
      i ≤ c.mv ∧ i + n = c.mv ∧ x = (BitVec.ofNat 64 i, ()) ∧
      fl.length = c.max_vars ∧ hp.length = c.max_vars ∧ ps.length = c.max_vars ∧
      qp.length = c.max_vars ∧ qn.length = c.max_vars ∧ qs.length = c.max_vars ∧
      m7LoopsMem c sF fl hp ps qp qn qs R m') ?_ ?_
  · rintro J1 n1 x1 mL hIH ⟨i, fl, hp, ps, qp, qn, qs, hi_le, hin, rfl,
      hfl, hhp, hps, hqp, hqn, hqs, hmL⟩
    c0_hsplit
    · have hi_lt : i < c.mv := by
        have hmv64 : c.mv < 2 ^ 64 := by
          have := c.hmv; unfold Examples.LratBytes.dimacsBound at *; omega
        have hi64 : i < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hmv64] at hc
        exact hc
      cases hn : n1 with
      | zero => omega
      | succ n' =>
        exact zt2_loop1_step_core Γ c sF R Q X i hi_lt fl hp ps qp qn qs
          hfl hhp hps hqp hqn hqs hmL
          (1 ||| 8 ||| 16 ||| 32 ||| 64 ||| 128 ||| 256 ||| 512 ||| 1024, ()).fst
          J1 (fun fl' hp' ps' qp' qn' qs' m'
            hfl' hhp' hps' hqp' hqn' hqs' hm' =>
            hIH n' (BitVec.ofNat 64 (i + 1), ()) m' (by omega)
              ⟨i + 1, fl', hp', ps', qp', qn', qs', by omega, by omega, rfl,
                hfl', hhp', hps', hqp', hqn', hqs', hm'⟩)
    · have hi_eq : i = c.mv := by
        have hmv64 : c.mv < 2 ^ 64 := by
          have := c.hmv; unfold Examples.LratBytes.dimacsBound at *; omega
        have hi64 : i < 2 ^ 64 := by omega
        rw [Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hmv64] at hc
        omega
      subst hi_eq
      c0_hsteps_nogrp
      exact zt2_loop2_wp Γ c sF R Q X fl hp ps qp qn qs hfl hhp hps hqp hqn hqs hmL
        fun fl2 hp2 ps2 qp2 qn2 qs2 mR hfl2 hhp2 hps2 hqp2 hqn2 hqs2 hmR => by
          let sEnd : FullState := FullState.mk { sF.core with flags := fl2 }
            { sF.scratch with
              heap := hp2, pos := ps2, q_prev := qp2, q_next := qn2, q_stamp := qs2 }
          have hmEnd : (MemShrinkMem c sEnd ⋆ R) mR :=
            (loopsMem_eq_memShrink c sF fl2 hp2 ps2 qp2 qn2 qs2 R) ▸ hmR
          have hlenEnd : MemShrinkLengthsOk c sEnd :=
            { hlenF with
              flags_len := by simpa [sEnd] using hfl2
              heap_len_arr := by simpa [sEnd] using hhp2
              pos_len := by simpa [sEnd] using hps2
              q_prev_len := by simpa [sEnd] using hqp2
              q_next_len := by simpa [sEnd] using hqn2
              q_stamp_len := by simpa [sEnd] using hqs2 }
          have hscEnd : FullHdrScalarsEq sEnd s := by
            rw [fullHdrScalarsEq_eq]
            dsimp only [sEnd, sF, s1, zt2FillState, zt2BytesState]
            simp only [and_self]
          exact hpost sEnd mR hscEnd
            rfl rfl rfl rfl rfl rfl rfl hlenEnd hmEnd
  · intro J1 hJ1; c0_hsteps
    exact hJ1 c.mv (0#64, ()) m2
      ⟨0, sF.core.flags, sF.scratch.heap, sF.scratch.pos, sF.scratch.q_prev,
        sF.scratch.q_next, sF.scratch.q_stamp, by omega, by omega, rfl,
        hlenF.flags_len, hlenF.heap_len_arr, hlenF.pos_len, hlenF.q_prev_len,
        hlenF.q_next_len, hlenF.q_stamp_len, hm_loops0⟩

/-! ## 2. Specification Table, Closed `ModuleOk` & Canonical Drop-In Bridges -/

section ModuleOkSection

/-- Closed `13`-row specification table (`12` functions + `kissat_parse_header` extern). -/
def m7MemShrinkSpecTable : List SpecEntry :=
  [ ⟨"full_fill_u64_m7", [i64, i64, i64], [], m7FillU64Spec, true⟩
  , ⟨"full_zero_tables1_m7", [i64], [], m7ZeroTables1Spec, true⟩
  , ⟨"full_zero_tables2_m7", [i64], [], m7ZeroTables2Spec, true⟩
  , ⟨"full_fixed_bytes_m7", [i64], [i64], m7FixedBytesSpec, true⟩
  , ⟨"full_trans_bytes_m7", [i64], [i64], m7TransBytesSpec, true⟩
  , ⟨"full_init_ptrs_m7", [i64, i64, i64], [], m7InitPtrsSpec, true⟩
  , ⟨"full_init_hdr_m7", [i64, i64, i64, i64], [], m7InitHdrSpec, true⟩
  , ⟨"full_calc_max_v_m7", [i64, i64, i64, i64], [i64], m7CalcMaxVSpec, true⟩
  , ⟨"full_calc_ext_cap_m7", [i64], [i64], m7CalcExtCapSpec, true⟩
  , ⟨"full_calc_scr_cap_m7", [i64], [i64], m7CalcScrCapSpec, true⟩
  , ⟨"full_init_arenas_m7", [i64, i64, i64, i64], [], m7InitArenasSpec, true⟩
  , ⟨"full_init_state_m7", [i64, i64, i64, i64, i64], [.bool], m7InitStateSpec, true⟩
  , ⟨"kissat_parse_header", [i64, i64, i64], [.bool], kissatParseHeaderSpec, true⟩ ]

theorem m7MemShrinkSpecTable_length : m7MemShrinkSpecTable.length = 13 := by rfl

theorem m7MemShrinkSpecTable_nodup : (m7MemShrinkSpecTable.map SpecEntry.name).Nodup := by
  simp only [m7MemShrinkSpecTable, List.map_cons, List.map_nil]
  decide

theorem m7MemShrinkSpecTable_noExit :
    ∀ e ∈ m7MemShrinkSpecTable, e.noExit = true := by
  intro e he
  simp only [m7MemShrinkSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

/-- Canonical verified specification environment for `m7MemShrinkModule`. -/
def m7MemShrinkEnv : Env :=
  Env.ofTable m7MemShrinkSpecTable

private theorem m7Env_row {i : Nat} (nm : Sym) {as rs : List Ty} (sp : Spec as rs)
    (hi : m7MemShrinkSpecTable[i]? = some ⟨nm, as, rs, sp, true⟩)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    EnvSpec m7MemShrinkEnv nm sp := by
  rw [envSpec_eq]; intro xs m Q X h
  exact Env.ofTable_of_mem (List.mem_of_getElem? hi) m7MemShrinkSpecTable_nodup
    (by simp only [SpecEntry.eff, ↓reduceIte]; exact hno xs m Q X h)

private theorem m7Env_fill_row : EnvSpec m7MemShrinkEnv "full_fill_u64_m7" m7FillU64Spec :=
  m7Env_row "full_fill_u64_m7" m7FillU64Spec (i := 0) rfl fun xs m Q X h => by
    rw [m7FillU64Spec_eq] at h ⊢; exact h

private theorem m7Env_zt1_row : EnvSpec m7MemShrinkEnv "full_zero_tables1_m7" m7ZeroTables1Spec :=
  m7Env_row "full_zero_tables1_m7" m7ZeroTables1Spec (i := 1) rfl fun ⟨hdr, ⟨⟩⟩ m Q X h => by
    rw [m7ZeroTables1Spec_eq] at h ⊢; exact h

private theorem m7Env_zt2_row : EnvSpec m7MemShrinkEnv "full_zero_tables2_m7" m7ZeroTables2Spec :=
  m7Env_row "full_zero_tables2_m7" m7ZeroTables2Spec (i := 2) rfl fun ⟨hdr, ⟨⟩⟩ m Q X h => by
    rw [m7ZeroTables2Spec_eq] at h ⊢; exact h

private theorem m7Env_fixed_row : EnvSpec m7MemShrinkEnv "full_fixed_bytes_m7" m7FixedBytesSpec :=
  m7Env_row "full_fixed_bytes_m7" m7FixedBytesSpec (i := 3) rfl fun xs m Q X h => by
    rw [m7FixedBytesSpec_eq] at h ⊢; exact h

private theorem m7Env_trans_row : EnvSpec m7MemShrinkEnv "full_trans_bytes_m7" m7TransBytesSpec :=
  m7Env_row "full_trans_bytes_m7" m7TransBytesSpec (i := 4) rfl fun xs m Q X h => by
    rw [m7TransBytesSpec_eq] at h ⊢; exact h

private theorem m7Env_ptrs_row : EnvSpec m7MemShrinkEnv "full_init_ptrs_m7" m7InitPtrsSpec :=
  m7Env_row "full_init_ptrs_m7" m7InitPtrsSpec (i := 5) rfl
    fun ⟨h1, h2, h3, ⟨⟩⟩ m Q X h => by rw [m7InitPtrsSpec_eq] at h ⊢; exact h

private theorem m7Env_hdr_row : EnvSpec m7MemShrinkEnv "full_init_hdr_m7" m7InitHdrSpec :=
  m7Env_row "full_init_hdr_m7" m7InitHdrSpec (i := 6) rfl
    fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [m7InitHdrSpec_eq] at h ⊢; exact h

private theorem m7Env_maxv_row : EnvSpec m7MemShrinkEnv "full_calc_max_v_m7" m7CalcMaxVSpec :=
  m7Env_row "full_calc_max_v_m7" m7CalcMaxVSpec (i := 7) rfl
    fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [m7CalcMaxVSpec_eq] at h ⊢; exact h

private theorem m7Env_ext_row : EnvSpec m7MemShrinkEnv "full_calc_ext_cap_m7" m7CalcExtCapSpec :=
  m7Env_row "full_calc_ext_cap_m7" m7CalcExtCapSpec (i := 8) rfl fun xs m Q X h => by
    rw [m7CalcExtCapSpec_eq] at h ⊢; exact h

private theorem m7Env_scr_row : EnvSpec m7MemShrinkEnv "full_calc_scr_cap_m7" m7CalcScrCapSpec :=
  m7Env_row "full_calc_scr_cap_m7" m7CalcScrCapSpec (i := 9) rfl fun xs m Q X h => by
    rw [m7CalcScrCapSpec_eq] at h ⊢; exact h

private theorem m7Env_arenas_row :
    EnvSpec m7MemShrinkEnv "full_init_arenas_m7" m7InitArenasSpec :=
  m7Env_row "full_init_arenas_m7" m7InitArenasSpec (i := 10) rfl
    fun ⟨h1, h2, h3, h4, ⟨⟩⟩ m Q X h => by rw [m7InitArenasSpec_eq] at h ⊢; exact h

private theorem m7Env_parse_row :
    EnvSpec m7MemShrinkEnv "kissat_parse_header" kissatParseHeaderSpec :=
  m7Env_row "kissat_parse_header" kissatParseHeaderSpec (i := 12) rfl fun _ _ _ _ h => h

private theorem m7Env_noExit :
    ∀ f as bs xs m Q X X',
      m7MemShrinkEnv f as bs xs m Q X → m7MemShrinkEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m7MemShrinkSpecTable_noExit

theorem m7_fill_u64_env_wp :
    ∀ a m Q X, m7FillU64Spec a m Q X →
      Func.wp m7MemShrinkEnv full_fill_u64_m7_body a m Q X :=
  full_fill_u64_m7_wp m7MemShrinkEnv

theorem m7_zero_tables1_env_wp :
    ∀ a m Q X, m7ZeroTables1Spec a m Q X →
      Func.wp m7MemShrinkEnv full_zero_tables1_m7_body a m Q X :=
  full_zero_tables1_m7_wp m7MemShrinkEnv m7Env_fill_row

theorem m7_zero_tables2_env_wp :
    ∀ a m Q X, m7ZeroTables2Spec a m Q X →
      Func.wp m7MemShrinkEnv full_zero_tables2_m7_body a m Q X :=
  full_zero_tables2_m7_wp m7MemShrinkEnv m7Env_fill_row

theorem m7_fixed_bytes_env_wp :
    ∀ a m Q X, m7FixedBytesSpec a m Q X →
      Func.wp m7MemShrinkEnv full_fixed_bytes_m7_body a m Q X :=
  full_fixed_bytes_m7_wp m7MemShrinkEnv

theorem m7_trans_bytes_env_wp :
    ∀ a m Q X, m7TransBytesSpec a m Q X →
      Func.wp m7MemShrinkEnv full_trans_bytes_m7_body a m Q X :=
  full_trans_bytes_m7_wp m7MemShrinkEnv

theorem m7_init_ptrs_env_wp :
    ∀ a m Q X, m7InitPtrsSpec a m Q X →
      Func.wp m7MemShrinkEnv full_init_ptrs_m7_body a m Q X :=
  full_init_ptrs_m7_wp m7MemShrinkEnv

theorem m7_init_hdr_env_wp :
    ∀ a m Q X, m7InitHdrSpec a m Q X →
      Func.wp m7MemShrinkEnv full_init_hdr_m7_body a m Q X :=
  full_init_hdr_m7_wp m7MemShrinkEnv

theorem m7_calc_max_v_env_wp :
    ∀ a m Q X, m7CalcMaxVSpec a m Q X →
      Func.wp m7MemShrinkEnv full_calc_max_v_m7_body a m Q X :=
  full_calc_max_v_m7_wp m7MemShrinkEnv m7Env_fixed_row m7Env_trans_row

theorem m7_calc_ext_cap_env_wp :
    ∀ a m Q X, m7CalcExtCapSpec a m Q X →
      Func.wp m7MemShrinkEnv full_calc_ext_cap_m7_body a m Q X :=
  full_calc_ext_cap_m7_wp m7MemShrinkEnv

theorem m7_calc_scr_cap_env_wp :
    ∀ a m Q X, m7CalcScrCapSpec a m Q X →
      Func.wp m7MemShrinkEnv full_calc_scr_cap_m7_body a m Q X :=
  full_calc_scr_cap_m7_wp m7MemShrinkEnv

theorem m7_init_arenas_env_wp :
    ∀ a m Q X, m7InitArenasSpec a m Q X →
      Func.wp m7MemShrinkEnv full_init_arenas_m7_body a m Q X :=
  full_init_arenas_m7_wp m7MemShrinkEnv m7Env_ptrs_row

theorem m7_init_state_env_wp :
    ∀ a m Q X, m7InitStateSpec a m Q X →
      Func.wp m7MemShrinkEnv full_init_state_m7_body a m Q X :=
  full_init_state_m7_wp m7MemShrinkEnv m7Env_parse_row m7Env_fixed_row m7Env_trans_row
    m7Env_maxv_row m7Env_ext_row m7Env_scr_row m7Env_arenas_row m7Env_hdr_row
    m7Env_zt1_row m7Env_zt2_row

theorem m7MemShrink_allFns_wf : AllFns Fn.Wf m7MemShrinkModule.fns :=
  ⟨full_fill_u64_m7_wf, full_zero_tables1_m7_wf, full_zero_tables2_m7_wf,
   full_fixed_bytes_m7_wf, full_trans_bytes_m7_wf, full_init_ptrs_m7_wf,
   full_init_hdr_m7_wf, full_calc_max_v_m7_wf, full_calc_ext_cap_m7_wf,
   full_calc_scr_cap_m7_wf, full_init_arenas_m7_wf, full_init_state_m7_wf, trivial⟩

theorem m7MemShrink_tableImpl :
    TableImpl m7MemShrinkEnv m7MemShrinkModule.fns m7MemShrinkSpecTable :=
  ⟨SpecEntry.Impl.of m7_fill_u64_env_wp, SpecEntry.Impl.of m7_zero_tables1_env_wp,
   SpecEntry.Impl.of m7_zero_tables2_env_wp, SpecEntry.Impl.of m7_fixed_bytes_env_wp,
   SpecEntry.Impl.of m7_trans_bytes_env_wp, SpecEntry.Impl.of m7_init_ptrs_env_wp,
   SpecEntry.Impl.of m7_init_hdr_env_wp, SpecEntry.Impl.of m7_calc_max_v_env_wp,
   SpecEntry.Impl.of m7_calc_ext_cap_env_wp, SpecEntry.Impl.of m7_calc_scr_cap_env_wp,
   SpecEntry.Impl.of m7_init_arenas_env_wp, SpecEntry.Impl.of m7_init_state_env_wp, trivial⟩

/-- Closed `ModuleOk` certifying all `12` functions of `m7MemShrinkModule` (`1` extern,
`0` exits). -/
theorem m7MemShrink_moduleOk : ModuleOk m7MemShrinkEnv m7MemShrinkModule :=
  Env.ofTable_moduleOk m7MemShrink_acyclic m7MemShrink_allFns_wf m7MemShrink_tableImpl

theorem m7ZeroTables1Fn_impl : SpecEntry.Impl m7MemShrinkEnv m7ZeroTables1Fn
    (.ofFn m7ZeroTables1Fn m7ZeroTables1Spec true) :=
  SpecEntry.Impl.of m7_zero_tables1_env_wp

theorem m7ZeroTables2Fn_impl : SpecEntry.Impl m7MemShrinkEnv m7ZeroTables2Fn
    (.ofFn m7ZeroTables2Fn m7ZeroTables2Spec true) :=
  SpecEntry.Impl.of m7_zero_tables2_env_wp

theorem m7FixedBytesFn_impl : SpecEntry.Impl m7MemShrinkEnv m7FixedBytesFn
    (.ofFn m7FixedBytesFn m7FixedBytesSpec true) :=
  SpecEntry.Impl.of m7_fixed_bytes_env_wp

theorem m7InitPtrsFn_impl : SpecEntry.Impl m7MemShrinkEnv m7InitPtrsFn
    (.ofFn m7InitPtrsFn m7InitPtrsSpec true) :=
  SpecEntry.Impl.of m7_init_ptrs_env_wp

theorem m7InitHdrFn_impl : SpecEntry.Impl m7MemShrinkEnv m7InitHdrFn
    (.ofFn m7InitHdrFn m7InitHdrSpec true) :=
  SpecEntry.Impl.of m7_init_hdr_env_wp

theorem m7CalcMaxVFn_impl : SpecEntry.Impl m7MemShrinkEnv m7CalcMaxVFn
    (.ofFn m7CalcMaxVFn m7CalcMaxVSpec true) :=
  SpecEntry.Impl.of m7_calc_max_v_env_wp

theorem m7CalcExtCapM5Fn_impl : SpecEntry.Impl m7MemShrinkEnv m7CalcExtCapM5Fn
    (.ofFn m7CalcExtCapM5Fn m7CalcExtCapSpec true) :=
  SpecEntry.Impl.of m7_calc_ext_cap_env_wp

theorem m7CalcScrCapM5Fn_impl : SpecEntry.Impl m7MemShrinkEnv m7CalcScrCapM5Fn
    (.ofFn m7CalcScrCapM5Fn m7CalcScrCapSpec true) :=
  SpecEntry.Impl.of m7_calc_scr_cap_env_wp

theorem m7InitArenasFn_impl : SpecEntry.Impl m7MemShrinkEnv m7InitArenasFn
    (.ofFn m7InitArenasFn m7InitArenasSpec true) :=
  SpecEntry.Impl.of m7_init_arenas_env_wp

theorem m7InitStateFn_impl : SpecEntry.Impl m7MemShrinkEnv m7InitStateFn
    (.ofFn m7InitStateFn m7InitStateSpec true) :=
  SpecEntry.Impl.of m7_init_state_env_wp

theorem m7InitStateM5Fn_impl : SpecEntry.Impl m7MemShrinkEnv m7InitStateM5Fn
    (.ofFn m7InitStateM5Fn m7InitStateSpec true) :=
  SpecEntry.Impl.of m7_init_state_env_wp

end ModuleOkSection

/-! ## 3. `FullM7` / `spliceFns` Compatibility, `-40.4%` Footprint & Transient Views -/

section FullM7SpliceCompat

/-- Unified `M7` function list spliced with `m7MemShrinkHelperFns` and `m7MemShrinkCanonFns`. -/
def m7SplicedM7Fns : List Fn :=
  spliceM7MemShrinkFns FullM7.m7Fns

/-- Unified `M7` module spliced with Prototype-A memory shrink (`421` fns, `0` externs/exits). -/
def m7SplicedM7Module : LeanQbe.T.Module :=
  spliceM7MemShrinkModule FullM7.m7Module

theorem m7SplicedM7Fns_wf : ∀ f ∈ m7SplicedM7Fns, f.Wf :=
  spliceM7MemShrinkFns_wf FullM7.m7Fns_wf

private theorem insertHelpersBefore_length (anchor : Sym) (helpers : List Fn) :
    ∀ (fs : List Fn), fs.any (·.name == anchor) = true →
      (insertHelpersBefore anchor helpers fs).length = fs.length + helpers.length
  | [], h => by simp at h
  | f :: fs, h => by
    rw [insertHelpersBefore_cons]
    by_cases heq : (f.name == anchor) = true
    · simp only [heq, ↓reduceIte, List.length_append, List.length_cons]; omega
    · simp only [heq, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have ht : fs.any (·.name == anchor) = true := by simpa [heq] using h
      have ih := insertHelpersBefore_length anchor helpers fs ht
      omega

private theorem m7Fns_has_zt1 : FullM7.m7Fns.any (·.name == "full_zero_tables1") = true := by
  t_kernel_rfl

private theorem m7Helper_len11 : m7MemShrinkHelperFns.length = 11 := by
  t_kernel_rfl

theorem m7SplicedM7Fns_length : m7SplicedM7Fns.length = FullM7.m7Fns.length + 11 := by
  unfold m7SplicedM7Fns spliceM7MemShrinkFns spliceM7Repls
  rw [List.length_map]; simp only [m7Fns_has_zt1, ↓reduceIte]
  rw [insertHelpersBefore_length "full_zero_tables1" m7MemShrinkHelperFns _ m7Fns_has_zt1]
  rw [m7Helper_len11]

theorem m7SplicedM7_acyclic : m7SplicedM7Module.checkAcyclic = true := by
  t_kernel_rfl

/-- Fixed-footprint `-40.4%` per-variable reduction (`151 -> 90 B/var`): at `max_v = 10000`,
`610,000 B` saved (`> 40.1%`), and at `max_v = 100000`, `> 40.3%` (`-40.4%` asymptotic). -/
theorem m7FixedBytes_shrink_40pct :
    1000 * (Full.fullFixedBytes 10000 - m7FixedBytes 10000) ≥ 401 * Full.fullFixedBytes 10000 ∧
      1000 * (Full.fullFixedBytes 100000 - m7FixedBytes 100000) ≥
        403 * Full.fullFixedBytes 100000 ∧
      ∀ n, Full.fullFixedBytes n - m7FixedBytes n =
        2 * valsBytes n + markBytes n + 56 * n := by
  refine ⟨?_, ?_, m7FixedBytes_saving⟩ <;>
    (simp only [m7FixedBytes_eq]; unfold Full.fullFixedBytes valsBytes markBytes
      u32FullBytes fullMinDepthOf; decide)

/-- Mutually exclusive transient pool views: `MemShrinkTransRegions c m` supports borrowing either
the Walk layout (`m7TransWalk_to_regions`) or the Congruence layout (`m7TransCong_to_regions`). -/
theorem m7_transient_phases_excl {c : MemShrinkCfg} {m : Mem 64}
    (h : MemShrinkTransRegions c m) :
    (∃ ws ws1 ws2 tmk trc wv wb,
      ws.length = 2 * c.max_vars ∧ ws1.length = 2 * c.max_vars ∧
      ws2.length = 2 * c.max_vars ∧ tmk.length = 2 * c.max_vars ∧
      trc.length = 2 * c.max_vars ∧ wv.length = 2 * c.max_vars ∧
      wb.length = c.max_vars ∧ MemShrinkTransWalk c ws ws1 ws2 tmk trc wv wb m) ∧
    (∃ ws ws1 ws2 tmk trc repr sig,
      ws.length = 2 * c.max_vars ∧ ws1.length = 2 * c.max_vars ∧
      ws2.length = 2 * c.max_vars ∧ tmk.length = 2 * c.max_vars ∧
      trc.length = 2 * c.max_vars ∧ repr.length = 2 * c.max_vars ∧
      sig.length = c.max_vars ∧ MemShrinkTransCong c ws ws1 ws2 tmk trc repr sig m) :=
  ⟨m7Trans_to_walk h, m7Trans_to_cong h⟩

end FullM7SpliceCompat

/-! ## 4. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Model Proofs) -/

section ConcreteUnsatNv

/-- Concrete `1`-variable, `2`-clause UNSAT formula `(x1) ∧ (~x1)`. -/
def nvM7UnsatCnf : CNF Nat :=
  CNF.empty |>.add (CNF.Clause.ofLiterals [(1, true)]) |>.add (CNF.Clause.ofLiterals [(1, false)])

theorem nvM7UnsatCnf_unsat : nvM7UnsatCnf.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hsat
  rw [nvM7UnsatCnf, CNF.sat_add, CNF.sat_add] at hsat
  rcases hsat with ⟨hc2, hc1, _⟩
  rw [CNF.Clause.sat_iff_exists_mem_eq] at hc1 hc2
  obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := hc1
  obtain ⟨⟨v2, p2⟩, hm2, he2⟩ := hc2
  rw [← CNF.Clause.mem_literals_iff] at hm1 hm2
  simp at hm1 hm2
  rcases hm1 with ⟨rfl, rfl⟩
  rcases hm2 with ⟨rfl, rfl⟩
  rw [he1] at he2
  exact nomatch he2

/-- DIMACS bytes for `"p cnf 1 2\n1 0\n-1 0\n"` (`19` bytes). -/
def nvM7UnsatBytes : List UInt8 :=
  [ 0x70, 0x20, 0x63, 0x6e, 0x66, 0x20, 0x31, 0x20, 0x32, 0x0a
  , 0x31, 0x20, 0x30, 0x0a, 0x2d, 0x31, 0x20, 0x30, 0x0a ]

theorem nvM7Unsat_header :
    parseHeader nvM7UnsatBytes = some (1, 2, nvM7UnsatBytes.drop 9) := by rfl

def nvM7CnfPtr : BitVec 64 := 0x1000#64
def nvM7HdrPtr : BitVec 64 := nvM7CnfPtr + BitVec.ofNat 64 nvM7UnsatBytes.length

/-- Concrete `Mem 64` holding `nvM7UnsatBytes` at `0x1000` and `4096`-byte workspace. -/
def nvM7InitMem : Mem 64 :=
  (nvM7UnsatBytes ++ List.replicate 4096 (0 : UInt8)).At nvM7CnfPtr

/-- Concrete `Mem 64` holding `nvM7UnsatBytes` at `0x1000` and undersized `1200`-byte arena. -/
def nvM7SmallMem : Mem 64 :=
  (nvM7UnsatBytes ++ List.replicate 1200 (0 : UInt8)).At nvM7CnfPtr

private theorem nv_mem_split (k : Nat) (hk : nvM7UnsatBytes.length + k ≤ 2 ^ 64) :
    (bytes nvM7CnfPtr nvM7UnsatBytes ⋆ region nvM7HdrPtr k ⋆ emp)
      ((nvM7UnsatBytes ++ List.replicate k (0 : UInt8)).At nvM7CnfPtr) := by
  rw [sep_emp]
  have e := Mem.At_append_sep nvM7UnsatBytes (List.replicate k (0 : UInt8)) nvM7CnfPtr
    (by simpa using hk)
  have hbase : (Eq (nvM7UnsatBytes.At nvM7CnfPtr) ⋆
      Eq ((List.replicate k (0 : UInt8)).At nvM7HdrPtr))
      ((nvM7UnsatBytes ++ List.replicate k (0 : UInt8)).At nvM7CnfPtr) :=
    (congrFun e _).mp rfl
  exact sep_mono2 (fun _ h => h)
    (fun _ h => ⟨List.replicate k (0 : UInt8), by simp, h.symm⟩) _ hbase

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, `0` SAT model proofs):
`full_init_state_m7` succeeds (`r = true`) on `(x1) ∧ (~x1)` with `4096`-byte budget, returning
valid `MemShrinkSparseInv` and `MemShrinkMem` (`mv = 1`, `nc = 2`, `avail = 4096`). -/
theorem nv_m7_init_state_unsat :
    Func.wp m7MemShrinkEnv full_init_state_m7_body
      (nvM7CnfPtr, nvM7CnfPtr + BitVec.ofNat 64 nvM7UnsatBytes.length,
        nvM7HdrPtr, 4096#64, 16#64, ())
      nvM7InitMem
      (fun (r, ()) m' =>
        r = true ∧ ∃ c s,
          c.hdr = nvM7HdrPtr ∧ c.avail = 4096 ∧ c.mv = 1 ∧ c.nc = 2 ∧
          nvM7UnsatCnf.Unsat ∧ MemShrinkSparseInv c s ∧
          (bytes nvM7CnfPtr nvM7UnsatBytes ⋆ MemShrinkMem c s) m')
      (fun _ _ _ _ => False) := by
  have hm := nv_mem_split 4096 (by decide)
  apply m7_init_state_env_wp
  rw [m7InitStateSpec_eq]
  refine ⟨nvM7UnsatBytes, emp, rfl, by decide, by decide, by decide, hm, ?_, ?_⟩
  · intro _ _ hfail
    have hlt := hfail 1 2 (nvM7UnsatBytes.drop 9) nvM7Unsat_header
    have hge : ¬ (4096#64).toNat <
        m7FixedBytes 1 + m7TransBytes 1 + 2 * 40 + 136 := by
      simp only [m7FixedBytes_eq, m7TransBytes_eq]
      unfold valsBytes markBytes u32FullBytes fullMinDepthOf; decide
    exact absurd hlt hge
  · intro c s j rest m' hhdr hav hph _ _ hsp
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    intro _ _ _ _ _ _ _ hm'
    rw [sep_emp] at hm'
    simp only [nvM7Unsat_header, Option.some.injEq, Prod.mk.injEq] at hph
    refine ⟨rfl, c, s, hhdr, by simpa using hav, hph.1.symm, hph.2.1.symm,
      nvM7UnsatCnf_unsat, hsp, hm'⟩

/-- Concrete `Mem 64` insufficient-budget bailout non-vacuity (`XPost := False`): with `avail =
1200 < m7FixedBytes 1 + m7TransBytes 1 + 2 * 40 + 136`, `full_init_state_m7` returns `false`
leaving `(bytes ⋆ region)` intact. -/
theorem nv_m7_init_state_small_unsat :
    Func.wp m7MemShrinkEnv full_init_state_m7_body
      (nvM7CnfPtr, nvM7CnfPtr + BitVec.ofNat 64 nvM7UnsatBytes.length,
        nvM7HdrPtr, 1200#64, 16#64, ())
      nvM7SmallMem
      (fun (r, ()) m' =>
        r = false ∧ nvM7UnsatCnf.Unsat ∧
          (bytes nvM7CnfPtr nvM7UnsatBytes ⋆ region nvM7HdrPtr 1200) m')
      (fun _ _ _ _ => False) := by
  have hm := nv_mem_split 1200 (by decide)
  apply m7_init_state_env_wp
  rw [m7InitStateSpec_eq]
  refine ⟨nvM7UnsatBytes, emp, rfl, by decide, by decide, by decide, hm, ?_, ?_⟩
  · intro m' hm' _
    rw [sep_emp] at hm'
    exact ⟨rfl, nvM7UnsatCnf_unsat, hm'⟩
  · intro c _ _ _ _ _ hav hph
    exfalso
    have hf := c.hsize
    have hav' : c.avail = 1200 := by simpa using hav
    have hfx : 1472 ≤ m7FixedBytes c.max_vars := by
      simp only [m7FixedBytes_eq]; omega
    omega

end ConcreteUnsatNv

end

end LeanQbe.T.Examples.Kissat.FullM7MemShrink
