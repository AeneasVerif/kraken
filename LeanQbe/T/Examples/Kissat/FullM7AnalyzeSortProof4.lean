module

public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSortProof3
import LeanQbe.T.Examples.Kissat.FullMinLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.Rules
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M7 Analyze/Sort Proof Shard 4: Modular Phase WP Proofs for `full_sort_tmp_m7`

Splits the large C0 AST of `full_sort_tmp_m7_body` into `7` same-file `private abbrev`
sub-expressions (unifying via `rfl` / `change` with `0 @[expose]`), proves each phase WP
independently inside its own `200k`-heartbeat theorem over opaque `FullState` FVars, and
assembles `full_sort_tmp_m7_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullMinTactics
open Kraken.Bedrock2.Test

local syntax "m7_lets_core" : tactic
local macro_rules
  | `(tactic| m7_lets_core) => `(tactic| repeat (first
      | rw [FullMinTactics.ml_copy_bool] | rw [FullMinTactics.ml_copy8]
      | rw [FullMinTactics.ml_copy32] | rw [FullMinTactics.ml_copy64]
      | rw [FullMinTactics.ml_add32] | rw [FullMinTactics.ml_add64]
      | rw [FullMinTactics.ml_sub64] | rw [FullMinTactics.ml_mul64]
      | rw [FullMinTactics.ml_shl64] | rw [FullMinTactics.ml_lshr64]
      | rw [FullMinTactics.ml_zext32_64] | rw [FullMinTactics.ml_sext32_64]
      | rw [FullMinTactics.ml_trunc64_32]
      | rw [FullMinTactics.ml_ult32] | rw [FullMinTactics.ml_ule32]
      | rw [FullMinTactics.ml_ugt32] | rw [FullMinTactics.ml_eq32]
      | rw [FullMinTactics.ml_ne32]
      | rw [FullMinTactics.ml_ult64] | rw [FullMinTactics.ml_ule64]
      | rw [FullMinTactics.ml_ugt64] | rw [FullMinTactics.ml_uge64]
      | rw [FullMinTactics.ml_eq64] | rw [FullMinTactics.ml_ne64]
      | rw [Arg.val_var] | rw [Arg.val_imm]))

local macro "m7_dsimp" : tactic =>
  `(tactic| dsimp (zeta := false) only [LeanQbe.T.vals, Arg.val, Prod.fst, Prod.snd])

local macro "m7_lets" : tactic =>
  `(tactic| (m7_lets_core; (try rw [LeanQbe.T.wp_jump]); try m7_dsimp))

local syntax "m7_jnz" : tactic
local macro_rules
  | `(tactic| m7_jnz) => `(tactic| (m7_lets; rw [LeanQbe.T.wp_jnz]; dsimp only [Arg.val]))

local syntax "m7_ld " term : tactic
local macro_rules
  | `(tactic| m7_ld $lem:term) => `(tactic| (m7_lets; rw [LeanQbe.T.wp]; refine ⟨_, $lem, ?_⟩))

local macro "m7_st " m:ident ", " h:ident " := " lem:term : tactic =>
  `(tactic| (m7_lets; refine LeanQbe.T.wp_store_sep $lem fun $m:ident $h:ident => ?_))

/-! ## 1. BitVec, Opaque Nat-Indexed Load/Store & Finishing Helpers -/

private theorem m7_ult64_true {a b : BitVec 64} (h : BitVec.ult a b = true) :
    a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem m7_ult64_false {a b : BitVec 64} (h : BitVec.ult a b = false) :
    b.toNat ≤ a.toNat := by
  have h1 : ¬ (a.toNat < b.toNat) := by simpa [BitVec.ult] using h
  omega

private theorem m7_ule64_true {a b : BitVec 64} (h : BitVec.ule a b = true) :
    a.toNat ≤ b.toNat := by
  simpa [BitVec.ule] using h

private theorem m7_ule64_false {a b : BitVec 64} (h : BitVec.ule a b = false) :
    b.toNat < a.toNat := by
  have h1 : ¬ (a.toNat ≤ b.toNat) := by simpa [BitVec.ule] using h
  omega

private theorem m7_ult32_true {a b : BitVec 32} (h : BitVec.ult a b = true) :
    a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem m7_ult32_false {a b : BitVec 32} (h : BitVec.ult a b = false) :
    b.toNat ≤ a.toNat := by
  have h1 : ¬ (a.toNat < b.toNat) := by simpa [BitVec.ult] using h
  omega

private theorem m7_ule32_true {a b : BitVec 32} (h : BitVec.ule a b = true) :
    a.toNat ≤ b.toNat := by
  simpa [BitVec.ule] using h

private theorem m7_ule32_false {a b : BitVec 32} (h : BitVec.ule a b = false) :
    b.toNat < a.toNat := by
  have h1 : ¬ (a.toNat ≤ b.toNat) := by simpa [BitVec.ule] using h
  omega

private theorem m7_var_idx64 (v : BitVec 32) :
    BitVec.setWidth 64 v >>> ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) =
      BitVec.ofNat 64 (v.toNat / 2) := by
  apply BitVec.eq_of_toNat_eq
  have hv64 : v.toNat / 2 < 2 ^ 64 := by have := v.isLt; omega
  rw [m7_ushr1_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv64]

private theorem m7_sub_bv64_ofNat {a b : Nat} (hba : b ≤ a) (ha : a < 2 ^ 64)
    (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [m7_bv64_sub (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]; exact hba),
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega)]

private theorem m7_add_bv64_ofNat {a b : Nat} (hab : a + b < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  rw [m7_bv64_add (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact hab),
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hab]

private theorem m7_add1_bv64 {a : Nat} (ha : a + 1 < 2 ^ 64) :
    BitVec.ofNat 64 a + (1 : BitVec 64) = BitVec.ofNat 64 (a + 1) := by
  simpa using m7_add_bv64_ofNat ha

private theorem m7_sub1_bv64 {a : Nat} (h1 : 1 ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - (1 : BitVec 64) = BitVec.ofNat 64 (a - 1) := by
  simpa using m7_sub_bv64_ofNat h1 ha (by decide)

private theorem m7_sub_zext64_of_le {v minL : BitVec 32} (hle : minL.toNat ≤ v.toNat) :
    BitVec.setWidth 64 v - BitVec.setWidth 64 minL =
      BitVec.ofNat 64 (v.toNat - minL.toNat) := by
  have hv64 : v.toNat < 2 ^ 64 := Nat.lt_trans v.isLt (by decide)
  have hm64 : minL.toNat < 2 ^ 64 := Nat.lt_trans minL.isLt (by decide)
  have h1 : BitVec.setWidth 64 v = BitVec.ofNat 64 v.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv64]
  have h2 : BitVec.setWidth 64 minL = BitVec.ofNat 64 minL.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64]
  rw [h1, h2]
  exact m7_sub_bv64_ofNat hle hv64 hm64

private theorem m7_trunc_add1_32 {v : BitVec 32} (hv : v.toNat + 1 < 2 ^ 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 v + (1 : BitVec 64)) =
      BitVec.ofNat 32 (v.toNat + 1) := by
  apply BitVec.eq_of_toNat_eq
  have hv64 : (BitVec.setWidth 64 v + (1 : BitVec 64)).toNat = v.toNat + 1 := by
    have hvlt : (BitVec.setWidth 64 v).toNat + (1 : BitVec 64).toNat < 2 ^ 64 := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide))]
      change v.toNat + 1 < 2 ^ 64; omega
    rw [m7_bv64_add hvlt, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide))]
    rfl
  rw [m7_bv32_trunc64 (by rw [hv64]; exact hv), hv64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

private theorem m7_trunc_zext64 {r : BitVec 64} (hr : r.toNat < 2 ^ 32) :
    BitVec.setWidth 32 r = BitVec.ofNat 32 r.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [m7_bv32_trunc64 hr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]

private theorem m7_add_bv32_ofNat {v : BitVec 32} (hv : v.toNat + 1 < 2 ^ 32) :
    v + (1 : BitVec 32) = BitVec.ofNat 32 (v.toNat + 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : v + (1 : BitVec 32) = v + 1#32 := rfl
  rw [h1, m7_bv32_add1_lt hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

private theorem m7_load_tmp_nat {c : FullCfg} {st s : FullState} {tmp_cur : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hc : st.core = { s.core with tmp := tmp_cur })
    (hi : i < tmp_cur.length) (hi64 : i < 2 ^ 64) (hm : (FullMem c st ⋆ R) m) :
    loadVal m i32 (c.pTmp + BitVec.ofNat 64 i * 4) = some (tmp_cur[i]'hi) := by
  have hi' : (BitVec.ofNat 64 i).toNat < tmp_cur.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]; exact hi
  have hld := m7_load_tmp_of hc hi' hm
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] using hld

private theorem m7_load_lvl_nat {c : FullCfg} {st s : FullState} {tmp_cur : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hc : st.core = { s.core with tmp := tmp_cur })
    (hi : i < s.core.lvl.length) (hi64 : i < 2 ^ 64) (hm : (FullMem c st ⋆ R) m) :
    loadVal m i32 (c.pLevel + BitVec.ofNat 64 i * 4) = some (s.core.lvl[i]'hi) := by
  have hi' : (BitVec.ofNat 64 i).toNat < s.core.lvl.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]; exact hi
  have hld := m7_load_lvl_of hc hi' hm
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] using hld

private theorem m7_load_tpos_nat {c : FullCfg} {st s : FullState} {tmp_cur : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hc : st.core = { s.core with tmp := tmp_cur })
    (hi : i < s.core.trail_pos.length) (hi64 : i < 2 ^ 64) (hm : (FullMem c st ⋆ R) m) :
    loadVal m i32 (c.pTrailPos + BitVec.ofNat 64 i * 4) = some (s.core.trail_pos[i]'hi) := by
  have hi' : (BitVec.ofNat 64 i).toNat < s.core.trail_pos.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]; exact hi
  have hld := m7_load_tpos_of hc hi' hm
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] using hld

private theorem m7_load_wsort_nat {c : FullCfg} {st s : FullState}
    {ws_cur : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hs : st.scratch = { s.scratch with wsort := ws_cur })
    (hi : i < ws_cur.length) (hi64 : i < 2 ^ 64) (hm : (FullMem c st ⋆ R) m) :
    loadVal m i32 (c.pWsort + BitVec.ofNat 64 i * 4) = some (ws_cur[i]'hi) := by
  have hi' : (BitVec.ofNat 64 i).toNat < ws_cur.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]; exact hi
  have hld := m7_load_wsort_of hs hi' hm
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] using hld

private theorem m7_store_tmp_nat {c : FullCfg} {st s : FullState} {tmp_cur : List (BitVec 32)}
    {sc0 : FullScratch} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 32)
    (hc : st.core = { s.core with tmp := tmp_cur }) (hs : st.scratch = sc0)
    (hi : i < tmp_cur.length) (hi64 : i < 2 ^ 64) (hm : (FullMem c st ⋆ R) m) :
    ∃ st' : FullState,
      st'.core = { s.core with tmp := tmp_cur.set i v } ∧
      st'.scratch = sc0 ∧
      storeOk m i32 (c.pTmp + BitVec.ofNat 64 i * 4) ∧
      (FullMem c st' ⋆ R) (storeMem m i32 (c.pTmp + BitVec.ofNat 64 i * 4) v) := by
  have hi' : (BitVec.ofNat 64 i).toNat < tmp_cur.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]; exact hi
  obtain ⟨st', hc', hs', hok, hm'⟩ := m7_store_tmp_upd v hc hs hi' hm
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] at hc'
  exact ⟨st', hc', hs', hok, hm'⟩

private theorem m7_store_wsort_nat {c : FullCfg} {st s : FullState}
    {tmp_cur ws_cur : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : Nat} (v : BitVec 32)
    (hc : st.core = { s.core with tmp := tmp_cur })
    (hs : st.scratch = { s.scratch with wsort := ws_cur })
    (hi : i < ws_cur.length) (hi64 : i < 2 ^ 64) (hm : (FullMem c st ⋆ R) m) :
    ∃ st' : FullState,
      st'.core = { s.core with tmp := tmp_cur } ∧
      st'.scratch = { s.scratch with wsort := ws_cur.set i v } ∧
      storeOk m i32 (c.pWsort + BitVec.ofNat 64 i * 4) ∧
      (FullMem c st' ⋆ R) (storeMem m i32 (c.pWsort + BitVec.ofNat 64 i * 4) v) := by
  have hi' : (BitVec.ofNat 64 i).toNat < ws_cur.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]; exact hi
  obtain ⟨st', hc', hs', hok, hm'⟩ := m7_store_wsort_upd v hc hs hi' hm
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] at hs'
  exact ⟨st', hc', hs', hok, hm'⟩

private theorem m7_state_eq {s1 s2 : FullState}
    (hc : s1.core = s2.core) (hs : s1.scratch = s2.scratch) : s1 = s2 := by
  cases s1; cases s2; simp at hc hs; subst hc; subst hs; rfl

private theorem m7Slice_congr_lt {α : Type _} {xs ys : List α} {lo hi : Nat}
    (hlo : lo ≤ hi) (hx : hi ≤ xs.length) (hy : hi ≤ ys.length)
    (heq : ∀ q < hi, xs[q]? = ys[q]?) :
    m7Slice xs lo hi = m7Slice ys lo hi := by
  apply List.ext_getElem
  · simp [m7Slice_length]; omega
  · intro k hk1 hk2
    rw [m7Slice_getElem, m7Slice_getElem]
    rw [m7Slice_length] at hk1
    have hlt : lo + k < hi := by omega
    have hq := heq (lo + k) hlt
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hq
    exact Option.some.inj hq

private theorem m7_drop_set_offset {α : Type _} (ws : List α) {mv b : Nat} (v : α)
    (hlen : ws.length = 2 * mv) (hb : b < mv) :
    (ws.set (mv + b) v).drop mv = (ws.drop mv).set b v := by
  apply List.ext_getElem
  · simp [hlen]
  · intro k hk1 hk2
    simp only [List.getElem_drop]
    by_cases hkb : k = b
    · subst hkb; simp
    · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (by omega)]
      simp only [List.getElem_drop]

private theorem m7_finish_spec {c : FullCfg} {s st' : FullState}
    {tmp' ws' : List (BitVec 32)} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post []}
    (hlenOk : FullState.LengthsOk c s) (htl : s.core.tmp_len ≤ c.max_vars)
    (hc' : st'.core = { s.core with tmp := tmp' })
    (hs' : st'.scratch = { s.scratch with wsort := ws' })
    (hlen_t : tmp'.length = c.max_vars)
    (hlen_w : ws'.length = 2 * c.max_vars)
    (hle16_w : s.core.tmp_len ≤ 16 → ws' = s.scratch.wsort)
    (hperm : (m7Slice tmp' 1 s.core.tmp_len).Perm (m7Slice s.core.tmp 1 s.core.tmp_len))
    (h0 : 0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?)
    (hsort : ∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
      Full.fullTmpLe s.core.lvl s.core.trail_pos (tmp'[i]?.getD 0#32) (tmp'[j]?.getD 0#32))
    (hm' : (FullMem c st' ⋆ R) m')
    (hQ : ∀ tmp' wsort' m',
      let s' : FullState := FullState.mk { s.core with tmp := tmp' }
        { s.scratch with wsort := wsort' };
      FullState.LengthsOk c s' → tmp'.length = c.max_vars →
      (s.core.tmp_len ≤ 16 → wsort' = s.scratch.wsort) →
      (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len) →
      (0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?) →
      (∀ j, 1 ≤ j → j < s.core.tmp_len →
        ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp'[j]? = s.core.tmp[i]?) →
      (∀ i, 1 ≤ i → i < s.core.tmp_len →
        ∃ j, 1 ≤ j ∧ j < s.core.tmp_len ∧ s.core.tmp[i]? = tmp'[j]?) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        Full.fullTmpLe s.core.lvl s.core.trail_pos
          (tmp'[i]?.getD 0#32) (tmp'[j]?.getD 0#32)) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      FullExtScratchPres s s' → (FullMem c s' ⋆ R) m' → Q () m') :
    Q () m' := by
  have hst_ok := m7SortTmp_stateOk c s tmp' ws' hlenOk hlen_t hlen_w
  have htake : (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len) := by
    by_cases hn0 : 0 < s.core.tmp_len
    · exact m7Slice_perm_to_take (h0 hn0) hperm hn0 (by rw [hlen_t]; exact htl)
        (by rw [hlenOk.core_ok.tmp_len_arr]; exact htl)
    · have : s.core.tmp_len = 0 := by omega
      simp [this]
  have hbij := m7Slice_perm_bij hperm (by rw [hlen_t]; exact htl)
    (by rw [hlenOk.core_ok.tmp_len_arr]; exact htl)
  have hlvl_le := m7_ins_exit_lvl hsort
  have hst_eq : st' = FullState.mk { s.core with tmp := tmp' }
      { s.scratch with wsort := ws' } :=
    m7_state_eq hc' hs'
  exact hQ tmp' ws' m' hst_ok.1 hlen_t hle16_w htake h0 hbij.1 hbij.2 hsort hlvl_le
    hst_ok.2 (hst_eq ▸ hm')

/-! ## 2. Phase Sub-AST Definitions (`rfl`-identical to `full_sort_tmp_m7_body`) -/

private abbrev m7SortInsExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (n64 pTmp pLvl pTpos : Val i64) : Expr Val Cont [] :=
  .group (sig := [[i64]]) (fun J1 =>
    .cons (fun x3 =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var x3.1, Arg.var n64, ())) fun x4 =>
      .jnz (Arg.var x4.1)
        (.let_ (Op.mk (.mul i64) (Arg.var x3.1, Arg.imm 4, ())) fun x5 =>
        .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var x5.1, ())) fun x6 =>
        .load i32 (Arg.var x6.1) fun v7 =>
        .let_ (Op.mk (.zext 32 64) (Arg.var v7, ())) fun x8 =>
        .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun x9 =>
        .let_ (Op.mk (.lshr i64) (Arg.var x8.1, Arg.var x9.1, ())) fun x10 =>
        .let_ (Op.mk (.mul i64) (Arg.var x10.1, Arg.imm 4, ())) fun x11 =>
        .let_ (Op.mk (.add i64) (Arg.var pLvl, Arg.var x11.1, ())) fun x12 =>
        .load i32 (Arg.var x12.1) fun v13 =>
        .let_ (Op.mk (.mul i64) (Arg.var x10.1, Arg.imm 4, ())) fun x14 =>
        .let_ (Op.mk (.add i64) (Arg.var pTpos, Arg.var x14.1, ())) fun x15 =>
        .load i32 (Arg.var x15.1) fun v16 =>
        .group (sig := [[i64, .bool]]) (fun J17 =>
          .cons (fun x19 =>
            .jnz (Arg.var x19.2.1)
              (.group (sig := [[i64, .bool]]) (fun _ =>
                .cons (fun x21 =>
                  .jump J17.1 (Arg.var x21.1, Arg.var x21.2.1, ()))
                .nil)
                (fun J20 => .let_ (Op.mk (.cmp .ule i64 .bool rfl)
                    (Arg.var x19.1, Arg.imm 1, ())) fun x22 =>
                .jnz (Arg.var x22.1)
                  (.jump J20.1 (Arg.var x19.1, Arg.imm false, ()))
                  (.let_ (Op.mk (.sub i64) (Arg.var x19.1, Arg.imm 1, ())) fun x23 =>
                  .let_ (Op.mk (.mul i64) (Arg.var x23.1, Arg.imm 4, ())) fun x24 =>
                  .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var x24.1, ())) fun x25 =>
                  .load i32 (Arg.var x25.1) fun v26 =>
                  .let_ (Op.mk (.zext 32 64) (Arg.var v26, ())) fun x27 =>
                  .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun x28 =>
                  .let_ (Op.mk (.lshr i64) (Arg.var x27.1, Arg.var x28.1, ())) fun x29 =>
                  .let_ (Op.mk (.mul i64) (Arg.var x29.1, Arg.imm 4, ())) fun x30 =>
                  .let_ (Op.mk (.add i64) (Arg.var pLvl, Arg.var x30.1, ())) fun x31 =>
                  .load i32 (Arg.var x31.1) fun v32 =>
                  .group (sig := [[i64, .bool]]) (fun _ =>
                    .cons (fun x34 =>
                      .jump J20.1 (Arg.var x34.1, Arg.var x34.2.1, ()))
                    .nil)
                    (fun J33 => .let_ (Op.mk (.cmp .ult i32 .bool rfl)
                        (Arg.var v32, Arg.var v13, ())) fun x35 =>
                    .jnz (Arg.var x35.1)
                      (.jump J33.1 (Arg.var x19.1, Arg.imm false, ()))
                      (.group (sig := [[]]) (fun _ =>
                        .cons (fun _ =>
                          .let_ (Op.mk (.mul i64) (Arg.var x19.1, Arg.imm 4, ())) fun x37 =>
                          .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var x37.1, ())) fun x38 =>
                          .store (t := i32) (Arg.var v26) (Arg.var x38.1) (
                            .let_ (Op.mk (.sub i64) (Arg.var x19.1, Arg.imm 1, ())) fun x39 =>
                            .jump J33.1 (Arg.var x39.1, Arg.var x19.2.1, ())))
                        .nil)
                        (fun J36 => .let_ (Op.mk (.cmp .eq i32 .bool rfl)
                            (Arg.var v32, Arg.var v13, ())) fun x40 =>
                        .jnz (Arg.var x40.1)
                          (.let_ (Op.mk (.mul i64) (Arg.var x29.1, Arg.imm 4, ())) fun x41 =>
                          .let_ (Op.mk (.add i64)
                              (Arg.var pTpos, Arg.var x41.1, ())) fun x42 =>
                          .load i32 (Arg.var x42.1) fun v43 =>
                          .let_ (Op.mk (.cmp .ule i32 .bool rfl)
                              (Arg.var v43, Arg.var v16, ())) fun x44 =>
                          .jnz (Arg.var x44.1)
                            (.jump J33.1 (Arg.var x19.1, Arg.imm false, ()))
                            (.jump J36.1 ()))
                          (.jump J36.1 ())))))))
              (.let_ (Op.mk (.mul i64) (Arg.var x19.1, Arg.imm 4, ())) fun x45 =>
              .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var x45.1, ())) fun x46 =>
              .store (t := i32) (Arg.var v7) (Arg.var x46.1) (
                .let_ (Op.mk (.add i64) (Arg.var x3.1, Arg.imm 1, ())) fun x47 =>
                .jump J1.1 (Arg.var x47.1, ()))))
          .nil)
          (fun J18 => .jump J18.1 (Arg.var x3.1, Arg.imm true, ())))
        (.ret ()))
    .nil)
    (fun J2 => .jump J2.1 (Arg.imm 2, ()))

private abbrev m7SortZeroExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (mv64 span pWsort : Val i64) (kNext : Expr Val Cont []) : Expr Val Cont [] :=
  .group (sig := [[i64]]) (fun J48 =>
    .cons (fun x50 =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var x50.1, Arg.var span, ())) fun x51 =>
      .jnz (Arg.var x51.1)
        (.let_ (Op.mk (.add i64) (Arg.var mv64, Arg.var x50.1, ())) fun xidx =>
        .let_ (Op.mk (.mul i64) (Arg.var xidx.1, Arg.imm 4, ())) fun x52 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var x52.1, ())) fun x53 =>
        .store (t := i32) (Arg.imm 0) (Arg.var x53.1) (
          .let_ (Op.mk (.add i64) (Arg.var x50.1, Arg.imm 1, ())) fun x54 =>
          .jump J48.1 (Arg.var x54.1, ())))
        (kNext))
    .nil)
    (fun J49 => .jump J49.1 (Arg.imm 0, ()))

private abbrev m7SortHistExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (mv64 n64 pLvl pWsort : Val i64) (minL : Val i32)
    (kNext : Expr Val Cont []) : Expr Val Cont [] :=
  .group (sig := [[i64]]) (fun J55 =>
    .cons (fun x57 =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var x57.1, Arg.var n64, ())) fun x58 =>
      .jnz (Arg.var x58.1)
        (.let_ (Op.mk (.mul i64) (Arg.var x57.1, Arg.imm 4, ())) fun x59 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var x59.1, ())) fun x60 =>
        .load i32 (Arg.var x60.1) fun v61 =>
        .let_ (Op.mk (.zext 32 64) (Arg.var v61, ())) fun x62 =>
        .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun x63 =>
        .let_ (Op.mk (.lshr i64) (Arg.var x62.1, Arg.var x63.1, ())) fun x64 =>
        .let_ (Op.mk (.mul i64) (Arg.var x64.1, Arg.imm 4, ())) fun x65 =>
        .let_ (Op.mk (.add i64) (Arg.var pLvl, Arg.var x65.1, ())) fun x66 =>
        .load i32 (Arg.var x66.1) fun v67 =>
        .let_ (Op.mk (.zext 32 64) (Arg.var v67, ())) fun x68 =>
        .let_ (Op.mk (.zext 32 64) (Arg.var minL, ())) fun x69 =>
        .let_ (Op.mk (.sub i64) (Arg.var x68.1, Arg.var x69.1, ())) fun x70 =>
        .let_ (Op.mk (.add i64) (Arg.var mv64, Arg.var x70.1, ())) fun xidx1 =>
        .let_ (Op.mk (.mul i64) (Arg.var xidx1.1, Arg.imm 4, ())) fun x71 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var x71.1, ())) fun x72 =>
        .let_ (Op.mk (.add i64) (Arg.var mv64, Arg.var x70.1, ())) fun xidx2 =>
        .let_ (Op.mk (.mul i64) (Arg.var xidx2.1, Arg.imm 4, ())) fun x73 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var x73.1, ())) fun x74 =>
        .load i32 (Arg.var x74.1) fun v75 =>
        .let_ (Op.mk (.add i32) (Arg.var v75, Arg.imm 1, ())) fun x76 =>
        .store (t := i32) (Arg.var x76.1) (Arg.var x72.1) (
          .let_ (Op.mk (.add i64) (Arg.var x57.1, Arg.imm 1, ())) fun x77 =>
          .jump J55.1 (Arg.var x77.1, ())))
        (kNext))
    .nil)
    (fun J56 => .jump J56.1 (Arg.imm 1, ()))

private abbrev m7SortPrefExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (mv64 span pWsort : Val i64) (kNext : Expr Val Cont []) : Expr Val Cont [] :=
  .group (sig := [[i64, i64]]) (fun J78 =>
    .cons (fun x80 =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var x80.1, Arg.var span, ())) fun x81 =>
      .jnz (Arg.var x81.1)
        (.let_ (Op.mk (.add i64) (Arg.var mv64, Arg.var x80.1, ())) fun xidx1 =>
        .let_ (Op.mk (.mul i64) (Arg.var xidx1.1, Arg.imm 4, ())) fun x82 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var x82.1, ())) fun x83 =>
        .load i32 (Arg.var x83.1) fun v84 =>
        .let_ (Op.mk (.add i64) (Arg.var mv64, Arg.var x80.1, ())) fun xidx2 =>
        .let_ (Op.mk (.mul i64) (Arg.var xidx2.1, Arg.imm 4, ())) fun x85 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var x85.1, ())) fun x86 =>
        .let_ (Op.mk (.trunc 64 32) (Arg.var x80.2.1, ())) fun x87 =>
        .store (t := i32) (Arg.var x87.1) (Arg.var x86.1) (
          .let_ (Op.mk (.zext 32 64) (Arg.var v84, ())) fun x88 =>
          .let_ (Op.mk (.add i64) (Arg.var x80.2.1, Arg.var x88.1, ())) fun x89 =>
          .let_ (Op.mk (.add i64) (Arg.var x80.1, Arg.imm 1, ())) fun x90 =>
          .jump J78.1 (Arg.var x90.1, Arg.var x89.1, ())))
        (kNext))
    .nil)
    (fun J79 => .jump J79.1 (Arg.imm 0, Arg.imm 1, ()))

private abbrev m7SortScatExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (mv64 n64 pTmp pLvl pWsort : Val i64) (minL : Val i32)
    (kNext : Expr Val Cont []) : Expr Val Cont [] :=
  .group (sig := [[i64]]) (fun J91 =>
    .cons (fun x93 =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var x93.1, Arg.var n64, ())) fun x94 =>
      .jnz (Arg.var x94.1)
        (.let_ (Op.mk (.mul i64) (Arg.var x93.1, Arg.imm 4, ())) fun x95 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var x95.1, ())) fun x96 =>
        .load i32 (Arg.var x96.1) fun v97 =>
        .let_ (Op.mk (.zext 32 64) (Arg.var v97, ())) fun x98 =>
        .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun x99 =>
        .let_ (Op.mk (.lshr i64) (Arg.var x98.1, Arg.var x99.1, ())) fun x100 =>
        .let_ (Op.mk (.mul i64) (Arg.var x100.1, Arg.imm 4, ())) fun x101 =>
        .let_ (Op.mk (.add i64) (Arg.var pLvl, Arg.var x101.1, ())) fun x102 =>
        .load i32 (Arg.var x102.1) fun v103 =>
        .let_ (Op.mk (.zext 32 64) (Arg.var v103, ())) fun x104 =>
        .let_ (Op.mk (.zext 32 64) (Arg.var minL, ())) fun x105 =>
        .let_ (Op.mk (.sub i64) (Arg.var x104.1, Arg.var x105.1, ())) fun x106 =>
        .let_ (Op.mk (.add i64) (Arg.var mv64, Arg.var x106.1, ())) fun xidx1 =>
        .let_ (Op.mk (.mul i64) (Arg.var xidx1.1, Arg.imm 4, ())) fun x107 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var x107.1, ())) fun x108 =>
        .load i32 (Arg.var x108.1) fun v109 =>
        .let_ (Op.mk (.zext 32 64) (Arg.var v109, ())) fun x110 =>
        .let_ (Op.mk (.add i64) (Arg.var mv64, Arg.var x106.1, ())) fun xidx2 =>
        .let_ (Op.mk (.mul i64) (Arg.var xidx2.1, Arg.imm 4, ())) fun x111 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var x111.1, ())) fun x112 =>
        .let_ (Op.mk (.add i64) (Arg.var x110.1, Arg.imm 1, ())) fun x113 =>
        .let_ (Op.mk (.trunc 64 32) (Arg.var x113.1, ())) fun x114 =>
        .store (t := i32) (Arg.var x114.1) (Arg.var x112.1) (
          .let_ (Op.mk (.mul i64) (Arg.var x110.1, Arg.imm 4, ())) fun x115 =>
          .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var x115.1, ())) fun x116 =>
          .store (t := i32) (Arg.var v97) (Arg.var x116.1) (
            .let_ (Op.mk (.add i64) (Arg.var x93.1, Arg.imm 1, ())) fun x117 =>
            .jump J91.1 (Arg.var x117.1, ()))))
        (kNext))
    .nil)
    (fun J92 => .jump J92.1 (Arg.imm 1, ()))

private abbrev m7SortRInsExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (pTmp pTpos rb re rb1 : Val i64) (kNext : Expr Val Cont []) :
    Expr Val Cont [] :=
  .group (sig := [[i64]]) (fun J118 =>
    .cons (fun x120 =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var x120.1, Arg.var re, ())) fun x121 =>
      .jnz (Arg.var x121.1)
        (.let_ (Op.mk (.mul i64) (Arg.var x120.1, Arg.imm 4, ())) fun x122 =>
        .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var x122.1, ())) fun x123 =>
        .load i32 (Arg.var x123.1) fun v124 =>
        .let_ (Op.mk (.zext 32 64) (Arg.var v124, ())) fun x125 =>
        .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun x126 =>
        .let_ (Op.mk (.lshr i64) (Arg.var x125.1, Arg.var x126.1, ())) fun x127 =>
        .let_ (Op.mk (.mul i64) (Arg.var x127.1, Arg.imm 4, ())) fun x128 =>
        .let_ (Op.mk (.add i64) (Arg.var pTpos, Arg.var x128.1, ())) fun x129 =>
        .load i32 (Arg.var x129.1) fun v130 =>
        .group (sig := [[i64, .bool]]) (fun J131 =>
          .cons (fun x133 =>
            .jnz (Arg.var x133.2.1)
              (.group (sig := [[i64, .bool]]) (fun _ =>
                .cons (fun x135 =>
                  .jump J131.1 (Arg.var x135.1, Arg.var x135.2.1, ()))
                .nil)
                (fun J134 => .let_ (Op.mk (.cmp .ule i64 .bool rfl)
                    (Arg.var x133.1, Arg.var rb, ())) fun x136 =>
                .jnz (Arg.var x136.1)
                  (.jump J134.1 (Arg.var x133.1, Arg.imm false, ()))
                  (.let_ (Op.mk (.sub i64) (Arg.var x133.1, Arg.imm 1, ())) fun x137 =>
                  .let_ (Op.mk (.mul i64) (Arg.var x137.1, Arg.imm 4, ())) fun x138 =>
                  .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var x138.1, ())) fun x139 =>
                  .load i32 (Arg.var x139.1) fun v140 =>
                  .group (sig := [[i64, .bool]]) (fun _ =>
                    .cons (fun x142 =>
                      .jump J134.1 (Arg.var x142.1, Arg.var x142.2.1, ()))
                    .nil)
                    (fun J141 => .let_ (Op.mk (.zext 32 64) (Arg.var v140, ())) fun x143 =>
                    .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun x144 =>
                    .let_ (Op.mk (.lshr i64) (Arg.var x143.1, Arg.var x144.1, ())) fun x145 =>
                    .let_ (Op.mk (.mul i64) (Arg.var x145.1, Arg.imm 4, ())) fun x146 =>
                    .let_ (Op.mk (.add i64) (Arg.var pTpos, Arg.var x146.1, ())) fun x147 =>
                    .load i32 (Arg.var x147.1) fun v148 =>
                    .let_ (Op.mk (.cmp .ule i32 .bool rfl)
                        (Arg.var v148, Arg.var v130, ())) fun x149 =>
                    .jnz (Arg.var x149.1)
                      (.jump J141.1 (Arg.var x133.1, Arg.imm false, ()))
                      (.let_ (Op.mk (.mul i64) (Arg.var x133.1, Arg.imm 4, ())) fun x150 =>
                      .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var x150.1, ())) fun x151 =>
                      .store (t := i32) (Arg.var v140) (Arg.var x151.1) (
                        .let_ (Op.mk (.sub i64) (Arg.var x133.1, Arg.imm 1, ())) fun x152 =>
                        .jump J141.1 (Arg.var x152.1, Arg.var x133.2.1, ())))))))
              (.let_ (Op.mk (.mul i64) (Arg.var x133.1, Arg.imm 4, ())) fun x153 =>
              .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var x153.1, ())) fun x154 =>
              .store (t := i32) (Arg.var v124) (Arg.var x154.1) (
                .let_ (Op.mk (.add i64) (Arg.var x120.1, Arg.imm 1, ())) fun x155 =>
                .jump J118.1 (Arg.var x155.1, ()))))
          .nil)
          (fun J132 => .jump J132.1 (Arg.var x120.1, Arg.imm true, ())))
        (kNext))
    .nil)
    (fun J119 => .jump J119.1 (Arg.var rb1, ()))

private abbrev m7SortRunsExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (n64 pTmp pLvl pTpos : Val i64) : Expr Val Cont [] :=
  .group (sig := [[i64]]) (fun J156 =>
    .cons (fun x158 =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var x158.1, Arg.var n64, ())) fun x159 =>
      .jnz (Arg.var x159.1)
        (.let_ (Op.mk (.mul i64) (Arg.var x158.1, Arg.imm 4, ())) fun x160 =>
        .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var x160.1, ())) fun x161 =>
        .load i32 (Arg.var x161.1) fun v162 =>
        .let_ (Op.mk (.zext 32 64) (Arg.var v162, ())) fun x163 =>
        .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun x164 =>
        .let_ (Op.mk (.lshr i64) (Arg.var x163.1, Arg.var x164.1, ())) fun x165 =>
        .let_ (Op.mk (.mul i64) (Arg.var x165.1, Arg.imm 4, ())) fun x166 =>
        .let_ (Op.mk (.add i64) (Arg.var pLvl, Arg.var x166.1, ())) fun x167 =>
        .load i32 (Arg.var x167.1) fun v168 =>
        .let_ (Op.mk (.add i64) (Arg.var x158.1, Arg.imm 1, ())) fun x169 =>
        .group (sig := [[i64, .bool]]) (fun J170 =>
          .cons (fun x172 =>
            .jnz (Arg.var x172.2.1)
              (.group (sig := [[i64, .bool]]) (fun _ =>
                .cons (fun x174 =>
                  .jump J170.1 (Arg.var x174.1, Arg.var x174.2.1, ()))
                .nil)
                (fun J173 => .let_ (Op.mk (.cmp .uge i64 .bool rfl)
                    (Arg.var x172.1, Arg.var n64, ())) fun x175 =>
                .jnz (Arg.var x175.1)
                  (.jump J173.1 (Arg.var x172.1, Arg.imm false, ()))
                  (.group (sig := [[i64, .bool]]) (fun _ =>
                    .cons (fun x177 =>
                      .jump J173.1 (Arg.var x177.1, Arg.var x177.2.1, ()))
                    .nil)
                    (fun J176 =>
                    .let_ (Op.mk (.mul i64) (Arg.var x172.1, Arg.imm 4, ())) fun x178 =>
                    .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var x178.1, ())) fun x179 =>
                    .load i32 (Arg.var x179.1) fun v180 =>
                    .let_ (Op.mk (.zext 32 64) (Arg.var v180, ())) fun x181 =>
                    .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun x182 =>
                    .let_ (Op.mk (.lshr i64) (Arg.var x181.1, Arg.var x182.1, ())) fun x183 =>
                    .let_ (Op.mk (.mul i64) (Arg.var x183.1, Arg.imm 4, ())) fun x184 =>
                    .let_ (Op.mk (.add i64) (Arg.var pLvl, Arg.var x184.1, ())) fun x185 =>
                    .load i32 (Arg.var x185.1) fun v186 =>
                    .let_ (Op.mk (.cmp .ne i32 .bool rfl)
                        (Arg.var v186, Arg.var v168, ())) fun x187 =>
                    .jnz (Arg.var x187.1)
                      (.jump J176.1 (Arg.var x172.1, Arg.imm false, ()))
                      (.let_ (Op.mk (.add i64) (Arg.var x172.1, Arg.imm 1, ())) fun x188 =>
                      .jump J176.1 (Arg.var x188.1, Arg.var x172.2.1, ()))))))
              (.let_ (Op.mk (.sub i64) (Arg.var x172.1, Arg.var x158.1, ())) fun x189 =>
              .group (sig := [[]]) (fun _ =>
                .cons (fun _ =>
                  .jump J156.1 (Arg.var x172.1, ()))
                .nil)
                (fun J190 => .let_ (Op.mk (.cmp .eq i64 .bool rfl)
                    (Arg.var x189.1, Arg.imm 2, ())) fun x191 =>
                .jnz (Arg.var x191.1)
                  (.let_ (Op.mk (.mul i64) (Arg.var x158.1, Arg.imm 4, ())) fun x192 =>
                  .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var x192.1, ())) fun x193 =>
                  .load i32 (Arg.var x193.1) fun v194 =>
                  .let_ (Op.mk (.add i64) (Arg.var x158.1, Arg.imm 1, ())) fun x195 =>
                  .let_ (Op.mk (.mul i64) (Arg.var x195.1, Arg.imm 4, ())) fun x196 =>
                  .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var x196.1, ())) fun x197 =>
                  .load i32 (Arg.var x197.1) fun v198 =>
                  .group (sig := [[]]) (fun _ =>
                    .cons (fun _ =>
                      .jump J190.1 ())
                    .nil)
                    (fun J199 => .let_ (Op.mk (.zext 32 64) (Arg.var v194, ())) fun x200 =>
                    .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun x201 =>
                    .let_ (Op.mk (.lshr i64) (Arg.var x200.1, Arg.var x201.1, ())) fun x202 =>
                    .let_ (Op.mk (.mul i64) (Arg.var x202.1, Arg.imm 4, ())) fun x203 =>
                    .let_ (Op.mk (.add i64) (Arg.var pTpos, Arg.var x203.1, ())) fun x204 =>
                    .load i32 (Arg.var x204.1) fun v205 =>
                    .let_ (Op.mk (.zext 32 64) (Arg.var v198, ())) fun x206 =>
                    .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun x207 =>
                    .let_ (Op.mk (.lshr i64) (Arg.var x206.1, Arg.var x207.1, ())) fun x208 =>
                    .let_ (Op.mk (.mul i64) (Arg.var x208.1, Arg.imm 4, ())) fun x209 =>
                    .let_ (Op.mk (.add i64) (Arg.var pTpos, Arg.var x209.1, ())) fun x210 =>
                    .load i32 (Arg.var x210.1) fun v211 =>
                    .let_ (Op.mk (.cmp .ugt i32 .bool rfl)
                        (Arg.var v205, Arg.var v211, ())) fun x212 =>
                    .jnz (Arg.var x212.1)
                      (.let_ (Op.mk (.mul i64) (Arg.var x158.1, Arg.imm 4, ())) fun x213 =>
                      .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var x213.1, ())) fun x214 =>
                      .store (t := i32) (Arg.var v198) (Arg.var x214.1) (
                        .let_ (Op.mk (.add i64) (Arg.var x158.1, Arg.imm 1, ())) fun x215 =>
                        .let_ (Op.mk (.mul i64) (Arg.var x215.1, Arg.imm 4, ())) fun x216 =>
                        .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var x216.1, ())) fun x217 =>
                        .store (t := i32) (Arg.var v194) (Arg.var x217.1) (
                          .jump J199.1 ())))
                      (.jump J199.1 ())))
                  (.group (sig := [[]]) (fun _ =>
                    .cons (fun _ =>
                      .jump J190.1 ())
                    .nil)
                    (fun J218 => .let_ (Op.mk (.cmp .ugt i64 .bool rfl)
                        (Arg.var x189.1, Arg.imm 2, ())) fun x219 =>
                    .jnz (Arg.var x219.1)
                      (.group (sig := [[]]) (fun _ =>
                        .cons (fun _ =>
                          .jump J218.1 ())
                        .nil)
                        (fun J220 => .let_ (Op.mk (.cmp .ule i64 .bool rfl)
                            (Arg.var x189.1, Arg.imm 16, ())) fun x221 =>
                        .jnz (Arg.var x221.1)
                          (.let_ (Op.mk (.add i64) (Arg.var x158.1, Arg.imm 1, ())) fun x222 =>
                          m7SortRInsExpr pTmp pTpos x158.1 x172.1 x222.1 (.jump J220.1 ()))
                          (.let_ (Op.mk (.sub i64) (Arg.var x158.1, Arg.imm 1, ())) fun x223 =>
                          .let_ (Op.mk (.sext 32 64) (Arg.imm 2, ())) fun x224 =>
                          .let_ (Op.mk (.shl i64)
                              (Arg.var x223.1, Arg.var x224.1, ())) fun x225 =>
                          .let_ (Op.mk (.add i64)
                              (Arg.var pTmp, Arg.var x225.1, ())) fun x226 =>
                          .let_ (Op.mk (.add i64) (Arg.var x189.1, Arg.imm 1, ())) fun x227 =>
                          .call (as := [i64, i64, i64, i64]) (bs := [])
                            "full_sort_tmp_heap_m7"
                            (Arg.var x226.1, Arg.var pLvl, Arg.var pTpos, Arg.var x227.1, ())
                            fun _ => .jump J220.1 ())))
                      (.jump J218.1 ()))))))
          .nil)
          (fun J171 => .jump J171.1 (Arg.var x169.1, Arg.imm true, ())))
        (.ret ()))
    .nil)
    (fun J157 => .jump J157.1 (Arg.imm 1, ()))

/-! ## 3. Modular Phase WP Proofs -/

private theorem m7_sort_ins_wp {Γ : Env} {c : FullCfg} {s st0 : FullState}
    {sc0 : FullScratch} {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post []} {X : XPost}
    (htmp_len : s.core.tmp.length = c.max_vars)
    (hlvl_len : s.core.lvl.length = c.max_vars)
    (htpos_len : s.core.trail_pos.length = c.max_vars)
    (htl : s.core.tmp_len ≤ c.max_vars)
    (h2lt : 2 ≤ s.core.tmp_len)
    (hbd0 : ∀ p, 1 ≤ p → p < s.core.tmp_len →
      (s.core.tmp[p]?.getD 0#32).toNat < 2 * c.max_vars)
    (hc0 : st0.core = { s.core with tmp := s.core.tmp })
    (hs0 : st0.scratch = sc0)
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hPost : ∀ st' tmp' m',
      st'.core = { s.core with tmp := tmp' } → st'.scratch = sc0 →
      tmp'.length = c.max_vars →
      (m7Slice tmp' 1 s.core.tmp_len).Perm (m7Slice s.core.tmp 1 s.core.tmp_len) →
      tmp'[0]? = s.core.tmp[0]? →
      (∀ q, s.core.tmp_len ≤ q → tmp'[q]? = s.core.tmp[q]?) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        Full.fullTmpLe s.core.lvl s.core.trail_pos
          (tmp'[i]?.getD 0#32) (tmp'[j]?.getD 0#32)) →
      (FullMem c st' ⋆ R) m' → Q () m') :
    wp Γ Q X
      (m7SortInsExpr (BitVec.ofNat 64 s.core.tmp_len) c.pTmp c.pLevel c.pTrailPos) m0 := by
  let N := s.core.tmp_len
  have hN64 : N < 2 ^ 64 := by have := c.hmaxv; unfold dimacsBound at this; omega
  let InvOut : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ i st tmp_i, xs.1 = BitVec.ofNat 64 i ∧ 2 ≤ i ∧ i ≤ N ∧ meas = N - i ∧
      st.core = { s.core with tmp := tmp_i } ∧ st.scratch = sc0 ∧
      tmp_i.length = c.max_vars ∧ (m7Slice tmp_i 1 N).Perm (m7Slice s.core.tmp 1 N) ∧
      tmp_i[0]? = s.core.tmp[0]? ∧ (∀ q, N ≤ q → tmp_i[q]? = s.core.tmp[q]?) ∧
      (∀ a b, 1 ≤ a → a ≤ b → b < i →
        Full.fullTmpLe s.core.lvl s.core.trail_pos
          (tmp_i[a]?.getD 0#32) (tmp_i[b]?.getD 0#32)) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group InvOut ?_ ?_
  · intro J1 meas xs m hm_ex ⟨i, st, tmp_i, hxs, hi2, hiN, hmeas, hst_c, hst_s, hlen_i,
      hperm_i, h0_i, hout_i, hsort_i, hm⟩
    rw [Blocks.get_here]
    m7_lets
    m7_jnz
    refine ⟨fun hlt_b => ?_, fun hge_b => ?_⟩
    · have hi_lt : i < N := by
        have h := m7_ult64_true hlt_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
      have hi_tmp : i < tmp_i.length := by rw [hlen_i]; omega
      have hbd_i := m7Slice_perm_bd hperm_i (by rw [hlen_i]; exact htl)
        (by rw [htmp_len]; exact htl) hbd0 i (by omega) hi_lt
      rw [List.getElem?_eq_getElem (l := tmp_i) (i := i) hi_tmp, Option.getD_some] at hbd_i
      m7_lets
      rw [hxs]
      have hld_v7 := m7_load_tmp_nat hst_c hi_tmp (by omega) hm
      m7_ld hld_v7
      m7_lets
      let v7 := tmp_i[i]'hi_tmp
      have hv7_bd : v7.toNat < 2 * c.max_vars := hbd_i
      rw [m7_var_idx64 v7]
      have hv7_lvl : v7.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
      have hv7_tp : v7.toNat / 2 < s.core.trail_pos.length := by rw [htpos_len]; omega
      have hld_lvl := m7_load_lvl_nat hst_c hv7_lvl (by omega) hm
      m7_ld hld_lvl
      m7_lets
      have hld_tp := m7_load_tpos_nat hst_c hv7_tp (by omega) hm
      m7_ld hld_tp
      let v13 := s.core.lvl[v7.toNat / 2]'hv7_lvl
      let v16 := s.core.trail_pos[v7.toNat / 2]'hv7_tp
      let InvIn : Nat → Tup Val [i64, .bool] → Mem 64 → Prop := fun m_in ys m_cur =>
        ∃ j cont st_j tmp_j,
          ys.1 = BitVec.ofNat 64 j ∧ ys.2.1 = cont ∧ 1 ≤ j ∧ j ≤ i ∧
          m_in = j + (if cont then 1 else 0) ∧
          st_j.core = { s.core with tmp := tmp_j } ∧ st_j.scratch = sc0 ∧
          tmp_j.length = c.max_vars ∧
          (m7Slice (tmp_j.set j v7) 1 N).Perm (m7Slice s.core.tmp 1 N) ∧
          tmp_j[0]? = s.core.tmp[0]? ∧
          (∀ q, N ≤ q → tmp_j[q]? = s.core.tmp[q]?) ∧
          (∀ a b, 1 ≤ a → a ≤ b → b ≤ i → a ≠ j → b ≠ j →
            Full.fullTmpLe s.core.lvl s.core.trail_pos
              (tmp_j[a]?.getD 0#32) (tmp_j[b]?.getD 0#32)) ∧
          (∀ k, j < k → k ≤ i →
            Full.fullTmpLe s.core.lvl s.core.trail_pos v7 (tmp_j[k]?.getD 0#32)) ∧
          (cont = false → 1 < j →
            Full.fullTmpLe s.core.lvl s.core.trail_pos (tmp_j[j - 1]?.getD 0#32) v7) ∧
          (FullMem c st_j ⋆ R) m_cur
      refine wp_loop_group InvIn ?_ ?_
      · intro J17 m_in ys m_cur hIH_in ⟨j, cont, st_j, tmp_j, hys1, hys2, hj1, hji, hmin,
          hstj_c, hstj_s, hlen_j, hperm_j, h0_j, hout_j, hinv_j, hgt_j, hstop_j, hm_j⟩
        rw [Blocks.get_here]
        m7_lets
        m7_jnz
        refine ⟨fun hcont_t => ?_, fun hcont_f => ?_⟩
        · have hcont : cont = true := by simpa [hys2] using hcont_t
          subst hcont
          simp only [↓reduceIte] at hmin
          let Pj20 : Tup Val [i64, .bool] → Mem 64 → Prop := fun ys2 m2 =>
            ∃ n', n' < m_in ∧ InvIn n' ys2 m2
          refine wp_join_group Pj20 ?_ ?_
          · intro J20 ys2 m2 ⟨n', hn', hInv'⟩
            rw [Blocks.get_here]
            exact hIH_in n' ys2 m2 hn' hInv'
          · intro J20 hExit20
            m7_lets
            m7_jnz
            refine ⟨fun hule_b => ?_, fun hule_f => ?_⟩
            ·
              have hj_eq : j = 1 := by
                have h := m7_ule64_true hule_b
                rw [hys1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
                change j ≤ 1 at h; omega
              apply hExit20
              refine ⟨j, by rw [hmin]; omega, j, false, st_j, tmp_j, hys1, rfl, hj1, hji,
                by simp, hstj_c, hstj_s, hlen_j, hperm_j, h0_j, hout_j, hinv_j, hgt_j,
                fun _ hbad => by omega, hm_j⟩
            ·
              have hj_gt1 : 1 < j := by
                have h := m7_ule64_false hule_f
                rw [hys1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
                exact h
              have hj_sub_eq : ys.1 - (1 : BitVec 64) = BitVec.ofNat 64 (j - 1) := by
                rw [hys1]; exact m7_sub1_bv64 (by omega) (by omega)
              m7_lets
              rw [hj_sub_eq]
              have hj1_lt : j - 1 < tmp_j.length := by rw [hlen_j]; omega
              have hld_v26 := m7_load_tmp_nat hstj_c hj1_lt (by omega) hm_j
              m7_ld hld_v26
              m7_lets
              let v26 := tmp_j[j - 1]'hj1_lt
              have hv26_bd : v26.toNat < 2 * c.max_vars := by
                have hslice_bd := m7Slice_perm_bd hperm_j
                  (by simp [hlen_j]; exact htl) (by rw [htmp_len]; exact htl)
                  hbd0 (j - 1) (by omega) (by omega)
                rw [List.getElem?_set_ne (by omega),
                  List.getElem?_eq_getElem (l := tmp_j) (i := j - 1) hj1_lt,
                  Option.getD_some] at hslice_bd
                exact hslice_bd
              rw [m7_var_idx64 v26]
              have hv26_lvl : v26.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
              have hld_v32 := m7_load_lvl_nat hstj_c hv26_lvl (by omega) hm_j
              m7_ld hld_v32
              let v32 := s.core.lvl[v26.toNat / 2]'hv26_lvl
              refine wp_join_group Pj20 ?_ ?_
              · intro J33 ys34 m34 hP34
                rw [Blocks.get_here]
                exact hExit20 ys34 m34 hP34
              · intro J33 hExit33
                m7_lets
                m7_jnz
                refine ⟨fun hlt_32 => ?_, fun hge_32 => ?_⟩
                ·
                  have hlt_lv : v32.toNat < v13.toNat := m7_ult32_true hlt_32
                  have hle_f : Full.fullTmpLe s.core.lvl s.core.trail_pos
                      (tmp_j[j - 1]?.getD 0#32) v7 := by
                    rw [List.getElem?_eq_getElem (l := tmp_j) (i := j - 1) hj1_lt,
                      Option.getD_some]
                    exact m7_fullTmpLe_of_lt hv26_lvl hv7_lvl hlt_lv
                  apply hExit33
                  refine ⟨j, by rw [hmin]; omega, j, false, st_j, tmp_j, hys1, rfl, hj1, hji,
                    by simp, hstj_c, hstj_s, hlen_j, hperm_j, h0_j, hout_j, hinv_j, hgt_j,
                    fun _ _ => hle_f, hm_j⟩
                ·
                  have hge_lv : v13.toNat ≤ v32.toNat := m7_ult32_false hge_32
                  let Pj36 : Tup Val [] → Mem 64 → Prop := fun _ m36 =>
                    m36 = m_cur ∧ Full.fullTmpLe s.core.lvl s.core.trail_pos v7 v26
                  refine wp_join_group Pj36 ?_ ?_
                  · intro J36 _ m36 ⟨hm_eq36, hv7_le⟩
                    subst hm_eq36
                    rw [Blocks.get_here]
                    m7_lets
                    have hj_lt : j < tmp_j.length := by rw [hlen_j]; omega
                    rw [hys1]
                    obtain ⟨st_s, hst_sc, hst_ss, hok_s, hm_s0⟩ :=
                      m7_store_tmp_nat (i := j) v26 hstj_c
                      hstj_s hj_lt (by omega) hm_j
                    m7_st m_s, hm_s := And.intro hok_s hm_s0
                    m7_lets
                    let tmp_j' := tmp_j.set j v26
                    have hj1_bv : BitVec.ofNat 64 j - (1 : BitVec 64) = BitVec.ofNat 64 (j - 1) :=
                      m7_sub1_bv64 (by omega) (by omega)
                    rw [hj1_bv]
                    have hv26_get : tmp_j[j - 1]?.getD 0#32 = v26 := by
                      rw [List.getElem?_eq_getElem (l := tmp_j) (i := j - 1) hj1_lt,
                        Option.getD_some]
                    have htmpj'_set : tmp_j' = tmp_j.set j (tmp_j[j - 1]?.getD 0#32) := by
                      simp [tmp_j', hv26_get]
                    have hi_j : i < tmp_j.length := by rw [hlen_j]; omega
                    have hshift := m7_ins_shift_inv
                      (ltp := Full.fullTmpLe s.core.lvl s.core.trail_pos)
                      (xs := tmp_j) (lo := 1) (i := i) (j := j) (x := v7)
                      hj_gt1 hji hi_j hinv_j hgt_j (hv26_get ▸ hv7_le)
                    have hperm_j' :
                        (m7Slice (tmp_j'.set (j - 1) v7) 1 N).Perm (m7Slice s.core.tmp 1 N) :=
                      (m7_shift_slice_perm (xs := tmp_j) (lo := 1) (hi := N)
                        (j := j) (j' := j - 1) v7 (by omega) (by omega) (by omega)
                        (by rw [hlen_j]; exact htl)).trans hperm_j
                    apply hExit33
                    refine ⟨(j - 1) + 1, by rw [hmin]; omega, j - 1, true, st_s, tmp_j',
                      rfl, by simpa using hys2,
                      by omega, by omega, rfl, hst_sc, hst_ss,
                      by simp [tmp_j', hlen_j], hperm_j',
                      by dsimp [tmp_j']; rw [← h0_j]; exact List.getElem?_set_ne (by omega),
                      fun q hq => by dsimp [tmp_j']; rw [← hout_j q hq]
                                     exact List.getElem?_set_ne (by omega),
                      by simpa [htmpj'_set] using hshift.1,
                      by simpa [htmpj'_set] using hshift.2,
                      fun hbad => absurd hbad (by decide), hm_s⟩
                  · intro J36 hExit36
                    m7_lets
                    m7_jnz
                    refine ⟨fun heq_32 => ?_, fun hne_32 => ?_⟩
                    ·
                      have heq_lv : v32.toNat = v13.toNat :=
                        congrArg BitVec.toNat (beq_iff_eq.mp heq_32)
                      have hv26_tp : v26.toNat / 2 < s.core.trail_pos.length := by
                        rw [htpos_len]; omega
                      have hld_v43 := m7_load_tpos_nat hstj_c hv26_tp (by omega) hm_j
                      m7_ld hld_v43
                      let v43 := s.core.trail_pos[v26.toNat / 2]'hv26_tp
                      m7_lets
                      m7_jnz
                      refine ⟨fun hule_tp => ?_, fun hgt_tp => ?_⟩
                      ·
                        have htp_le : v43.toNat ≤ v16.toNat := m7_ule32_true hule_tp
                        have hle_f : Full.fullTmpLe s.core.lvl s.core.trail_pos
                            (tmp_j[j - 1]?.getD 0#32) v7 := by
                          rw [List.getElem?_eq_getElem (l := tmp_j) (i := j - 1) hj1_lt,
                            Option.getD_some]
                          exact m7_fullTmpLe_of_eq_lvl_tpos hv26_lvl hv7_lvl hv26_tp hv7_tp
                            heq_lv htp_le
                        apply hExit33
                        refine ⟨j, by rw [hmin]; omega, j, false, st_j, tmp_j, hys1, rfl,
                          hj1, hji, by simp, hstj_c, hstj_s, hlen_j, hperm_j, h0_j, hout_j,
                          hinv_j, hgt_j, fun _ _ => hle_f, hm_j⟩
                      ·
                        have htp_lt : v16.toNat < v43.toNat := m7_ule32_false hgt_tp
                        apply hExit36
                        exact ⟨rfl, m7_fullTmpLe_of_eq_lvl_tpos hv7_lvl hv26_lvl hv7_tp hv26_tp
                          heq_lv.symm (Nat.le_of_lt htp_lt)⟩
                    ·
                      have hne_lv : v32 ≠ v13 := by simpa [bne_iff_ne] using hne_32
                      have hlt_lv : v13.toNat < v32.toNat := by
                        have hne_nat : v32.toNat ≠ v13.toNat := fun h =>
                          hne_lv (BitVec.eq_of_toNat_eq h)
                        omega
                      apply hExit36
                      exact ⟨rfl, m7_fullTmpLe_of_lt hv7_lvl hv26_lvl hlt_lv⟩
        · have hcont : cont = false := by simpa [hys2] using hcont_f
          m7_lets
          have hj_lt : j < tmp_j.length := by rw [hlen_j]; omega
          rw [hys1]
          obtain ⟨st_e, hst_ec, hst_es, hok_e, hm_e0⟩ := m7_store_tmp_nat (i := j) v7 hstj_c hstj_s
            hj_lt (by omega) hm_j
          m7_st m_e, hm_e := And.intro hok_e hm_e0
          m7_lets
          let tmp_e := tmp_j.set j v7
          have hi_j : i < tmp_j.length := by rw [hlen_j]; omega
          have hsort_e := m7_ins_place_sorted
            (ltp := Full.fullTmpLe s.core.lvl s.core.trail_pos)
            (fun a => m7_fullTmpLe_refl _ _ a)
            (fun a b c h1 h2 => m7_fullTmpLe_trans h1 h2)
            (xs := tmp_j) (lo := 1) (i := i) (j := j) (x := v7)
            hj1 hji hi_j hinv_j (hstop_j hcont) hgt_j
          have hi1_bv : BitVec.ofNat 64 i + (1 : BitVec 64) = BitVec.ofNat 64 (i + 1) :=
            m7_add1_bv64 (by omega)
          rw [hi1_bv]
          exact hm_ex (N - (i + 1)) (BitVec.ofNat 64 (i + 1), ()) _ (by omega)
            ⟨i + 1, st_e, tmp_e, rfl, by omega, by omega, rfl, hst_ec, hst_es,
              by simp [tmp_e, hlen_j], hperm_j,
              by dsimp [tmp_e]; rw [← h0_j]; exact List.getElem?_set_ne (by omega),
              fun q hq => by dsimp [tmp_e]; rw [← hout_j q hq]
                             exact List.getElem?_set_ne (by omega),
              fun a b ha hab hb => hsort_e a b ha hab (by omega), hm_e⟩
      · intro J18 hExit18
        apply hExit18 (i + 1) (BitVec.ofNat 64 i, true, ()) m
        refine ⟨i, true, st, tmp_i, rfl, rfl, by omega, le_refl i, rfl, hst_c, hst_s,
          hlen_i, ?_, h0_i, hout_i, ?_, fun k hk1 hk2 => by omega,
          fun hbad => absurd hbad (by decide), hm⟩
        · have hset : tmp_i.set i v7 = tmp_i := by
            apply List.ext_getElem
            · simp
            · intro p hp1 hp2
              by_cases hpi : p = i
              · subst hpi; simp [v7]
              · simp [List.getElem_set_ne (Ne.symm hpi)]
          simpa [hset] using hperm_i
        · intro a b ha hab hbi _ _
          exact hsort_i a b ha hab (by omega)
    · have hi_ge : N ≤ i := by
        have h := m7_ult64_false hge_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
      have hi_eq : i = N := by omega
      subst hi_eq
      exact hPost st tmp_i m hst_c hst_s hlen_i hperm_i h0_i hout_i hsort_i hm
  · intro J2 hExit2
    apply hExit2 (N - 2) (BitVec.ofNat 64 2, ()) m0
    refine ⟨2, st0, s.core.tmp, rfl, le_refl 2, h2lt, rfl, hc0, hs0, htmp_len, List.Perm.refl _,
      rfl, fun _ _ => rfl, ?_, hm0⟩
    intro a b ha hab hb
    have ha1 : a = 1 := by omega
    have hb1 : b = 1 := by omega
    subst ha1; subst hb1
    exact m7_fullTmpLe_refl _ _ _

private theorem m7_sort_zero_wp {Γ : Env} {c : FullCfg} {s st0 : FullState}
    {tmp0 ws0 : List (BitVec 32)} {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post []}
    {X : XPost} {span : Nat} {kNext : Expr Val Cont []}
    (hspan_le : span ≤ c.max_vars)
    (hc0 : st0.core = { s.core with tmp := tmp0 })
    (hs0 : st0.scratch = { s.scratch with wsort := ws0 })
    (hws_len : ws0.length = 2 * c.max_vars)
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hNext : ∀ st' ws' m',
      st'.core = { s.core with tmp := tmp0 } →
      st'.scratch = { s.scratch with wsort := ws' } →
      ws'.length = 2 * c.max_vars →
      (∀ q < c.max_vars, ws'[q]? = ws0[q]?) →
      (∀ b < span, (ws'[c.max_vars + b]?.getD 0#32).toNat = 0) →
      (FullMem c st' ⋆ R) m' → wp Γ Q X kNext m') :
    wp Γ Q X (m7SortZeroExpr (BitVec.ofNat 64 c.max_vars) (BitVec.ofNat 64 span) c.pWsort kNext)
      m0 := by
  have hmv60 : c.max_vars < 2 ^ 60 := by have := c.hmaxv; unfold dimacsBound at this; omega
  have hsp64 : span < 2 ^ 64 := by omega
  let Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ k st ws_k, xs.1 = BitVec.ofNat 64 k ∧ k ≤ span ∧ meas = span - k ∧
      st.core = { s.core with tmp := tmp0 } ∧
      st.scratch = { s.scratch with wsort := ws_k } ∧
      ws_k.length = 2 * c.max_vars ∧
      (∀ q < c.max_vars, ws_k[q]? = ws0[q]?) ∧
      (∀ b < k, (ws_k[c.max_vars + b]?.getD 0#32).toNat = 0) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group Inv ?_ ?_
  · intro J48 meas xs m hIH ⟨k, st, ws_k, hxs, hk_le, hmeas, hst_c, hst_s, hlen_ws, hpre, hz, hm⟩
    rw [Blocks.get_here]
    m7_lets
    m7_jnz
    refine ⟨fun hlt_b => ?_, fun hge_b => ?_⟩
    · have hk_lt : k < span := by
        have h := m7_ult64_true hlt_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hsp64, Nat.mod_eq_of_lt (by omega)] at h
      m7_lets
      rw [hxs, m7_add_bv64_ofNat (by omega)]
      obtain ⟨st', hst_c', hst_s', hok, hm_raw⟩ := m7_store_wsort_nat (i := c.max_vars + k)
        0#32 hst_c hst_s (by rw [hlen_ws]; omega) (by omega) hm
      m7_st m_n, hm' := And.intro hok hm_raw
      m7_lets
      let ws' := ws_k.set (c.max_vars + k) 0#32
      have hk1_bv : BitVec.ofNat 64 k + (1 : BitVec 64) = BitVec.ofNat 64 (k + 1) :=
        m7_add1_bv64 (by omega)
      rw [hk1_bv]
      refine hIH (span - (k + 1)) (BitVec.ofNat 64 (k + 1), ()) _ (by omega)
        ⟨k + 1, st', ws', rfl, by omega, rfl, hst_c', hst_s',
          by simp [ws', hlen_ws], fun q hq => by
            dsimp [ws']; rw [List.getElem?_set_ne (by omega)]; exact hpre q hq,
          fun b hb => ?_, hm'⟩
      by_cases hbk : b = k
      · subst hbk; dsimp [ws']
        rw [List.getElem?_eq_getElem (by simp [hlen_ws]; omega),
          List.getElem_set_self, Option.getD_some]; rfl
      · dsimp [ws']; rw [List.getElem?_set_ne (by omega)]; exact hz b (by omega)
    · have hk_ge : span ≤ k := by
        have h := m7_ult64_false hge_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hsp64, Nat.mod_eq_of_lt (by omega)] at h
      have hk_eq : k = span := by omega
      subst hk_eq
      exact hNext st ws_k m hst_c hst_s hlen_ws hpre hz hm
  · intro J49 hExit49
    exact hExit49 span (BitVec.ofNat 64 0, ()) m0
      ⟨0, st0, ws0, rfl, Nat.zero_le span, rfl, hc0, hs0, hws_len,
        fun _ _ => rfl, fun _ hb => by omega, hm0⟩

private theorem m7_sort_hist_wp {Γ : Env} {c : FullCfg} {s st0 : FullState}
    {ws0 : List (BitVec 32)} {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post []} {X : XPost}
    {minL_bv : BitVec 32} {span : Nat} {kNext : Expr Val Cont []}
    (hlvl_len : s.core.lvl.length = c.max_vars)
    (hle_mv : s.core.tmp_len ≤ c.max_vars) (h1N : 1 ≤ s.core.tmp_len)
    (hlen_ws0 : ws0.length = 2 * c.max_vars)
    (hspan_le : span ≤ c.max_vars)
    (hminmax : ∀ p, 1 ≤ p → p < s.core.tmp_len →
      minL_bv.toNat ≤ (s.core.lvl[(ws0[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[(ws0[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < minL_bv.toNat + span)
    (hbd_ws : ∀ p, 1 ≤ p → p < s.core.tmp_len → (ws0[p]?.getD 0#32).toNat < 2 * c.max_vars)
    (hzero : ∀ b < span, (ws0[c.max_vars + b]?.getD 0#32).toNat = 0)
    (hc0 : st0.core = { s.core with tmp := s.core.tmp })
    (hs0 : st0.scratch = { s.scratch with wsort := ws0 })
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hNext : ∀ st' ws' m',
      st'.core = { s.core with tmp := s.core.tmp } →
      st'.scratch = { s.scratch with wsort := ws' } →
      ws'.length = 2 * c.max_vars →
      (∀ q < c.max_vars, ws'[q]? = ws0[q]?) →
      (∀ b < span, (ws'[c.max_vars + b]?.getD 0#32).toNat =
        m7BktCnt s.core.lvl minL_bv.toNat (m7Slice ws0 1 s.core.tmp_len) b) →
      (FullMem c st' ⋆ R) m' → wp Γ Q X kNext m') :
    wp Γ Q X (m7SortHistExpr (BitVec.ofNat 64 c.max_vars) (BitVec.ofNat 64 s.core.tmp_len)
      c.pLevel c.pWsort minL_bv kNext) m0 := by
  let N := s.core.tmp_len
  let minL := minL_bv.toNat
  have hmv60 : c.max_vars < 2 ^ 60 := by have := c.hmaxv; unfold dimacsBound at this; omega
  have hN64 : N < 2 ^ 64 := by omega
  let Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ k st ws_k, xs.1 = BitVec.ofNat 64 k ∧ 1 ≤ k ∧ k ≤ N ∧ meas = N - k ∧
      st.core = { s.core with tmp := s.core.tmp } ∧
      st.scratch = { s.scratch with wsort := ws_k } ∧
      ws_k.length = 2 * c.max_vars ∧
      (∀ q < c.max_vars, ws_k[q]? = ws0[q]?) ∧
      (∀ b < span, (ws_k[c.max_vars + b]?.getD 0#32).toNat =
        m7BktCnt s.core.lvl minL (m7Slice ws0 1 k) b) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group Inv ?_ ?_
  · intro J55 meas xs m hIH ⟨k, st, ws_k, hxs, hk1, hk_le, hmeas, hst_c, hst_s,
      hlen_wk, hpre, hcnt, hm⟩
    rw [Blocks.get_here]
    m7_lets
    m7_jnz
    refine ⟨fun hlt_b => ?_, fun hge_b => ?_⟩
    · have hk_lt : k < N := by
        have h := m7_ult64_true hlt_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
      have hk_ws : k < ws_k.length := by rw [hlen_wk]; omega
      have hk_ws0 : k < ws0.length := by rw [hlen_ws0]; omega
      have hpre_k : ws_k[k] = ws0[k] := by
        have hq := hpre k (by omega)
        rw [List.getElem?_eq_getElem hk_ws, List.getElem?_eq_getElem hk_ws0] at hq
        exact Option.some.inj hq
      have hbd_k := hbd_ws k hk1 hk_lt
      rw [List.getElem?_eq_getElem (l := ws0) (i := k) hk_ws0, Option.getD_some,
        ← hpre_k] at hbd_k
      m7_lets
      rw [hxs]
      have hld_v61 := m7_load_wsort_nat hst_s hk_ws (by omega) hm
      m7_ld hld_v61
      m7_lets
      let v61 := ws_k[k]'hk_ws
      have hv61_bd : v61.toNat < 2 * c.max_vars := hbd_k
      rw [m7_var_idx64 v61]
      have hv61_lvl : v61.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
      have hld_v67 := m7_load_lvl_nat hst_c hv61_lvl (by omega) hm
      m7_ld hld_v67
      m7_lets
      let v67 := s.core.lvl[v61.toNat / 2]'hv61_lvl
      let wst_k := ws_k.drop c.max_vars
      have hwst_len : wst_k.length = c.max_vars := by simp [wst_k, hlen_wk]; omega
      have hsl_eq : m7Slice ws_k 1 N = m7Slice ws0 1 N :=
        m7Slice_congr_lt (by omega) (by rw [hlen_wk]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      have hsl_k : m7Slice ws_k 1 k = m7Slice ws0 1 k :=
        m7Slice_congr_lt hk1 (by rw [hlen_wk]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      have hminmax_k : ∀ p, 1 ≤ p → p < s.core.tmp_len →
          minL ≤ (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
          (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < minL + span := by
        intro p hp1 hp2
        rw [show ws_k[p]? = ws0[p]? from hpre p (by omega)]
        exact hminmax p hp1 hp2
      have hcnt_wst : ∀ b < span, (wst_k[b]?.getD 0#32).toNat =
          m7BktCnt s.core.lvl minL (m7Slice ws_k 1 k) b := by
        intro b hb; dsimp [wst_k]; rw [List.getElem?_drop, hsl_k]; exact hcnt b hb
      have hstep := m7_hist_step_cnt hlvl_len hlen_wk hwst_len hk1 hk_lt hle_mv
        hminmax_k hcnt_wst hspan_le
      have hx_min : minL ≤ v67.toNat := by
        have h := (hminmax_k k hk1 hk_lt).1
        rw [List.getElem?_eq_getElem (l := ws_k) (i := k) hk_ws, Option.getD_some,
          List.getElem?_eq_getElem (l := s.core.lvl) (i := v61.toNat / 2) hv61_lvl,
          Option.getD_some] at h
        exact h
      have hbi_eq : v67.toNat - minL = m7Bkt s.core.lvl minL v61 := by
        rw [m7Bkt_eq, List.getElem?_eq_getElem (l := s.core.lvl) (i := v61.toNat / 2) hv61_lvl,
          Option.getD_some]
      have hx70_eq : BitVec.setWidth 64 v67 - BitVec.setWidth 64 minL_bv =
          BitVec.ofNat 64 (m7Bkt s.core.lvl minL v61) := by
        rw [m7_sub_zext64_of_le hx_min, hbi_eq]
      rw [hx70_eq]
      let bi := m7Bkt s.core.lvl minL v61
      have hbi_lt : bi < span := hstep.1
      have hidx64 : BitVec.ofNat 64 c.max_vars + BitVec.ofNat 64 bi =
          BitVec.ofNat 64 (c.max_vars + bi) :=
        m7_add_bv64_ofNat (by omega)
      rw [hidx64]
      have hbi_w : c.max_vars + bi < ws_k.length := by rw [hlen_wk]; omega
      have hld_v75 := m7_load_wsort_nat hst_s hbi_w (by omega) hm
      m7_ld hld_v75
      m7_lets
      let old := ws_k[c.max_vars + bi]'hbi_w
      have hold_eq : old = wst_k[bi]'(by rw [hwst_len]; omega) := by
        dsimp [old, wst_k]; simp [List.getElem_drop]
      have hold_le : old.toNat + 1 ≤ k := hold_eq ▸ hstep.2.1
      have hold32 : old.toNat + 1 < 2 ^ 32 := by have := c.hmaxv; unfold dimacsBound at this; omega
      rw [m7_add_bv32_ofNat hold32]
      obtain ⟨st', hst_c', hst_s', hok, hm_raw⟩ := m7_store_wsort_nat (i := c.max_vars + bi)
        (BitVec.ofNat 32 (old.toNat + 1)) hst_c hst_s hbi_w (by omega) hm
      m7_st m_n, hm' := And.intro hok hm_raw
      m7_lets
      have hk1_bv : BitVec.ofNat 64 k + (1 : BitVec 64) = BitVec.ofNat 64 (k + 1) :=
        m7_add1_bv64 (by omega)
      rw [hk1_bv]
      let ws_k1 := ws_k.set (c.max_vars + bi) (BitVec.ofNat 32 (old.toNat + 1))
      have hpre1 : ∀ q < c.max_vars, ws_k1[q]? = ws0[q]? := fun q hq => by
        dsimp [ws_k1]; rw [List.getElem?_set_ne (by omega)]; exact hpre q hq
      have hsl_k1 : m7Slice ws_k 1 (k + 1) = m7Slice ws0 1 (k + 1) :=
        m7Slice_congr_lt (by omega) (by rw [hlen_wk]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      refine hIH (N - (k + 1)) (BitVec.ofNat 64 (k + 1), ()) _ (by omega)
        ⟨k + 1, st', ws_k1, rfl, by omega, by omega, rfl, hst_c', hst_s',
          by simp [ws_k1, hlen_wk], hpre1, fun b hb => ?_, hm'⟩
      have hd_drop : ws_k1.drop c.max_vars = wst_k.set bi (BitVec.ofNat 32 (old.toNat + 1)) :=
        m7_drop_set_offset ws_k _ hlen_wk (by omega)
      have hst_b := hstep.2.2.2 b hb
      rw [← hold_eq, ← hd_drop, List.getElem?_drop] at hst_b
      rwa [← hsl_k1]
    · have hk_ge : N ≤ k := by
        have h := m7_ult64_false hge_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
      have hk_eq : k = N := by omega
      subst hk_eq
      exact hNext st ws_k m hst_c hst_s hlen_wk hpre hcnt hm
  · intro J56 hExit56
    apply hExit56 (N - 1) (BitVec.ofNat 64 1, ()) m0
    refine ⟨1, st0, ws0, rfl, le_refl 1, h1N, rfl, hc0, hs0, hlen_ws0,
      fun _ _ => rfl, fun b hb => ?_, hm0⟩
    rw [m7Slice_nil _ (le_refl 1), m7BktCnt_nil]
    exact hzero b hb

private theorem m7_sort_pref_wp {Γ : Env} {c : FullCfg} {s st0 : FullState}
    {ws0 : List (BitVec 32)} {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post []} {X : XPost}
    {tot : Nat → Nat} {span : Nat} {kNext : Expr Val Cont []}
    (hlen_ws0 : ws0.length = 2 * c.max_vars)
    (hspan_le : span ≤ c.max_vars)
    (hspos_N : m7PrefixStart tot span ≤ c.max_vars)
    (hsuf0 : ∀ b < span, (ws0[c.max_vars + b]?.getD 0#32).toNat = tot b)
    (hc0 : st0.core = { s.core with tmp := s.core.tmp })
    (hs0 : st0.scratch = { s.scratch with wsort := ws0 })
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hNext : ∀ st' ws' m',
      st'.core = { s.core with tmp := s.core.tmp } →
      st'.scratch = { s.scratch with wsort := ws' } →
      ws'.length = 2 * c.max_vars →
      (∀ q < c.max_vars, ws'[q]? = ws0[q]?) →
      (∀ b < span, (ws'[c.max_vars + b]?.getD 0#32).toNat = m7PrefixStart tot b) →
      (FullMem c st' ⋆ R) m' → wp Γ Q X kNext m') :
    wp Γ Q X (m7SortPrefExpr (BitVec.ofNat 64 c.max_vars) (BitVec.ofNat 64 span) c.pWsort kNext)
      m0 := by
  have hmv60 : c.max_vars < 2 ^ 60 := by have := c.hmaxv; unfold dimacsBound at this; omega
  have hsp64 : span < 2 ^ 64 := by omega
  have hmv32 : c.max_vars < 2 ^ 32 := by have := c.hmaxv; unfold dimacsBound at this; omega
  let Inv : Nat → Tup Val [i64, i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ j st ws_j, xs.1 = BitVec.ofNat 64 j ∧ j ≤ span ∧ meas = span - j ∧
      xs.2.1.toNat = m7PrefixStart tot j ∧
      st.core = { s.core with tmp := s.core.tmp } ∧
      st.scratch = { s.scratch with wsort := ws_j } ∧
      ws_j.length = 2 * c.max_vars ∧
      (∀ q < c.max_vars, ws_j[q]? = ws0[q]?) ∧
      (∀ b, j ≤ b → b < span → (ws_j[c.max_vars + b]?.getD 0#32).toNat = tot b) ∧
      (∀ b < j, (ws_j[c.max_vars + b]?.getD 0#32).toNat = m7PrefixStart tot b) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group Inv ?_ ?_
  · intro J78 meas xs m hIH ⟨j, st, ws_j, hxs1, hj_le, hmeas, hsum, hst_c, hst_s,
      hlen_ws, hpre_arr, hsuf, hpre, hm⟩
    rw [Blocks.get_here]
    m7_lets
    m7_jnz
    refine ⟨fun hlt_b => ?_, fun hge_b => ?_⟩
    · have hj_lt : j < span := by
        have h := m7_ult64_true hlt_b
        rw [hxs1, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hsp64, Nat.mod_eq_of_lt (by omega)] at h
      have hs_bd : m7PrefixStart tot (j + 1) < 2 ^ 32 := by
        have hmono : m7PrefixStart tot (j + 1) ≤ m7PrefixStart tot span :=
          m7PrefixStart_mono (by omega)
        omega
      let wst_j := ws_j.drop c.max_vars
      have hwst_len : wst_j.length = c.max_vars := by simp [wst_j, hlen_ws]; omega
      have hj_ws : c.max_vars + j < ws_j.length := by rw [hlen_ws]; omega
      m7_lets
      have hj_off64 : BitVec.ofNat 64 c.max_vars + BitVec.ofNat 64 j =
          BitVec.ofNat 64 (c.max_vars + j) :=
        m7_add_bv64_ofNat (by omega)
      rw [hxs1, hj_off64]
      have hld_v84 := m7_load_wsort_nat hst_s hj_ws (by omega) hm
      m7_ld hld_v84
      m7_lets
      rw [hj_off64]
      let wj := ws_j[c.max_vars + j]'hj_ws
      have hwj_drop : wj = wst_j[j]'(by rw [hwst_len]; omega) := by
        dsimp [wj, wst_j]; simp [List.getElem_drop]
      have hrs32 : xs.2.1.toNat < 2 ^ 32 := by
        have hmono : m7PrefixStart tot j ≤ m7PrefixStart tot (j + 1) := by
          rw [m7PrefixStart_succ]; exact Nat.le_add_right _ _
        omega
      rw [m7_trunc_zext64 hrs32]
      obtain ⟨st', hst_c', hst_s', hok, hm_raw⟩ := m7_store_wsort_nat (i := c.max_vars + j)
        (BitVec.ofNat 32 xs.2.1.toNat) hst_c hst_s hj_ws (by omega) hm
      m7_st m_n, hm' := And.intro hok hm_raw
      m7_lets
      have hsuf_w : ∀ b, j ≤ b → b < span → (wst_j[b]?.getD 0#32).toNat = tot b := by
        intro b hb1 hb2; dsimp [wst_j]; rw [List.getElem?_drop]; exact hsuf b hb1 hb2
      have hpre_w : ∀ b < j, (wst_j[b]?.getD 0#32).toNat = m7PrefixStart tot b := by
        intro b hb; dsimp [wst_j]; rw [List.getElem?_drop]; exact hpre b hb
      have hstep := m7_pref_step_inv hwst_len hj_lt hspan_le hsum hsuf_w hpre_w hs_bd
      have hj1_bv : BitVec.ofNat 64 j + (1 : BitVec 64) = BitVec.ofNat 64 (j + 1) :=
        m7_add1_bv64 (by omega)
      rw [hj1_bv]
      let ws_j1 := ws_j.set (c.max_vars + j) (BitVec.ofNat 32 xs.2.1.toNat)
      have hd_drop : ws_j1.drop c.max_vars = wst_j.set j (BitVec.ofNat 32 xs.2.1.toNat) :=
        m7_drop_set_offset ws_j _ hlen_ws (by omega)
      refine hIH (span - (j + 1)) (BitVec.ofNat 64 (j + 1), xs.2.1 + wj.setWidth 64, ()) _
        (by omega) ⟨j + 1, st', ws_j1, rfl, by omega, rfl, hwj_drop ▸ hstep.1, hst_c', hst_s',
          by simp [ws_j1, hlen_ws],
          fun q hq => by dsimp [ws_j1]; rw [List.getElem?_set_ne (by omega)]; exact hpre_arr q hq,
          fun b hb1 hb2 => by
            have h := hstep.2.1 b hb1 hb2
            rwa [← hd_drop, List.getElem?_drop] at h,
          fun b hb => by
            have h := hstep.2.2 b hb
            rwa [← hd_drop, List.getElem?_drop] at h,
          hm'⟩
    · have hj_ge : span ≤ j := by
        have h := m7_ult64_false hge_b
        rw [hxs1, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hsp64, Nat.mod_eq_of_lt (by omega)] at h
      have hj_eq : j = span := by omega
      subst hj_eq
      exact hNext st ws_j m hst_c hst_s hlen_ws hpre_arr hpre hm
  · intro J79 hExit79
    apply hExit79 span (BitVec.ofNat 64 0, BitVec.ofNat 64 1, ()) m0
    refine ⟨0, st0, ws0, rfl, Nat.zero_le span, rfl, ?_, hc0, hs0, hlen_ws0,
      fun _ _ => rfl, fun b _ hb => hsuf0 b hb, fun _ hb => by omega, hm0⟩
    rw [m7PrefixStart_zero]; rfl

private theorem m7_sort_scat_wp {Γ : Env} {c : FullCfg} {s st0 : FullState}
    {ws0 : List (BitVec 32)} {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post []} {X : XPost}
    {minL_bv : BitVec 32} {span : Nat} {kNext : Expr Val Cont []}
    (htmp_len : s.core.tmp.length = c.max_vars)
    (hlvl_len : s.core.lvl.length = c.max_vars)
    (htl : s.core.tmp_len ≤ c.max_vars) (h1N : 1 ≤ s.core.tmp_len)
    (hlen_ws0 : ws0.length = 2 * c.max_vars)
    (hspan_le : span ≤ c.max_vars)
    (hsl_ws : m7Slice ws0 1 s.core.tmp_len = m7Slice s.core.tmp 1 s.core.tmp_len)
    (hminmax : ∀ p, 1 ≤ p → p < s.core.tmp_len →
      minL_bv.toNat ≤ (s.core.lvl[(ws0[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[(ws0[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < minL_bv.toNat + span)
    (hbd_ws : ∀ p, 1 ≤ p → p < s.core.tmp_len → (ws0[p]?.getD 0#32).toNat < 2 * c.max_vars)
    (hspos_N : m7PrefixStart (m7BktCnt s.core.lvl minL_bv.toNat (m7Slice ws0 1 s.core.tmp_len))
      span = s.core.tmp_len)
    (hspos_le : ∀ b ≤ span, m7PrefixStart
      (m7BktCnt s.core.lvl minL_bv.toNat (m7Slice ws0 1 s.core.tmp_len)) b ≤ s.core.tmp_len)
    (hspos0 : ∀ b < span, (ws0[c.max_vars + b]?.getD 0#32).toNat = m7PrefixStart
      (m7BktCnt s.core.lvl minL_bv.toNat (m7Slice ws0 1 s.core.tmp_len)) b)
    (hc0 : st0.core = { s.core with tmp := s.core.tmp })
    (hs0 : st0.scratch = { s.scratch with wsort := ws0 })
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hNext : ∀ st' tmp' ws' m',
      st'.core = { s.core with tmp := tmp' } →
      st'.scratch = { s.scratch with wsort := ws' } →
      tmp'.length = c.max_vars → ws'.length = 2 * c.max_vars →
      (m7Slice tmp' 1 s.core.tmp_len).Perm (m7Slice s.core.tmp 1 s.core.tmp_len) →
      tmp'[0]? = s.core.tmp[0]? →
      (∀ q, s.core.tmp_len ≤ q → tmp'[q]? = s.core.tmp[q]?) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (FullMem c st' ⋆ R) m' → wp Γ Q X kNext m') :
    wp Γ Q X (m7SortScatExpr (BitVec.ofNat 64 c.max_vars) (BitVec.ofNat 64 s.core.tmp_len)
      c.pTmp c.pLevel c.pWsort minL_bv kNext) m0 := by
  let N := s.core.tmp_len
  let minL := minL_bv.toNat
  let tot := m7BktCnt s.core.lvl minL (m7Slice ws0 1 N)
  let spos := m7PrefixStart tot
  have hmv60 : c.max_vars < 2 ^ 60 := by have := c.hmaxv; unfold dimacsBound at this; omega
  have hN64 : N < 2 ^ 64 := by omega
  let Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ k_s st tmp_s ws_s, xs.1 = BitVec.ofNat 64 k_s ∧ 1 ≤ k_s ∧ k_s ≤ N ∧ meas = N - k_s ∧
      st.core = { s.core with tmp := tmp_s } ∧
      st.scratch = { s.scratch with wsort := ws_s } ∧
      tmp_s.length = c.max_vars ∧ ws_s.length = 2 * c.max_vars ∧
      (∀ q < c.max_vars, ws_s[q]? = ws0[q]?) ∧
      tmp_s[0]? = s.core.tmp[0]? ∧ (∀ q, N ≤ q → tmp_s[q]? = s.core.tmp[q]?) ∧
      (∀ b < span, (ws_s[c.max_vars + b]?.getD 0#32).toNat =
        spos b + m7BktCnt s.core.lvl minL (m7Slice ws0 1 k_s) b) ∧
      (∀ b < span, ∀ p, spos b ≤ p → p < (ws_s[c.max_vars + b]?.getD 0#32).toNat →
        m7Bkt s.core.lvl minL (tmp_s[p]?.getD 0#32) = b ∧
        minL ≤ (s.core.lvl[(tmp_s[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
      (m7FlatBkts tmp_s spos (fun b => (ws_s[c.max_vars + b]?.getD 0#32).toNat) span).Perm
        (m7Slice ws0 1 k_s) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group Inv ?_ ?_
  · intro J91 meas xs m hIH ⟨k_s, st, tmp_s, ws_s, hxs, hk1, hk_le, hmeas, hst_c, hst_s,
      hlen_ts, hlen_ws, hpre, h0_s, hout_s, hepos_s, hbkt_s, hperm_s, hm⟩
    rw [Blocks.get_here]
    m7_lets
    m7_jnz
    refine ⟨fun hlt_b => ?_, fun hge_b => ?_⟩
    · have hk_lt : k_s < N := by
        have h := m7_ult64_true hlt_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
      have hks_ws : k_s < ws_s.length := by rw [hlen_ws]; omega
      have hks_ws0 : k_s < ws0.length := by rw [hlen_ws0]; omega
      have hpre_k : ws_s[k_s] = ws0[k_s] := by
        have hq := hpre k_s (by omega)
        rw [List.getElem?_eq_getElem hks_ws, List.getElem?_eq_getElem hks_ws0] at hq
        exact Option.some.inj hq
      have hbd_k := hbd_ws k_s hk1 hk_lt
      rw [List.getElem?_eq_getElem (l := ws0) (i := k_s) hks_ws0, Option.getD_some,
        ← hpre_k] at hbd_k
      m7_lets
      rw [hxs]
      have hld_v97 := m7_load_wsort_nat hst_s hks_ws (by omega) hm
      m7_ld hld_v97
      m7_lets
      let v97 := ws_s[k_s]'hks_ws
      have hv97_bd : v97.toNat < 2 * c.max_vars := hbd_k
      rw [m7_var_idx64 v97]
      have hv97_lvl : v97.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
      have hld_v103 := m7_load_lvl_nat hst_c hv97_lvl (by omega) hm
      m7_ld hld_v103
      m7_lets
      let v103 := s.core.lvl[v97.toNat / 2]'hv97_lvl
      let wst_s := ws_s.drop c.max_vars
      have hwst_len : wst_s.length = c.max_vars := by simp [wst_s, hlen_ws]; omega
      have hsl_eq : m7Slice ws_s 1 N = m7Slice ws0 1 N :=
        m7Slice_congr_lt (by omega) (by rw [hlen_ws]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      have hsl_ks : m7Slice ws_s 1 k_s = m7Slice ws0 1 k_s :=
        m7Slice_congr_lt hk1 (by rw [hlen_ws]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      have hminmax_s : ∀ p, 1 ≤ p → p < N →
          minL ≤ (s.core.lvl[(ws_s[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
          (s.core.lvl[(ws_s[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < minL + span := by
        intro p hp1 hp2
        rw [show ws_s[p]? = ws0[p]? from hpre p (by omega)]
        exact hminmax p hp1 hp2
      have hstep := m7_scat_step_inv hlen_ws hlen_ts hwst_len htl hk1 hk_lt hspan_le
        hminmax_s (by rw [hsl_eq]; exact hspos_N) (by intro b hb; rw [hsl_eq]; exact hspos_le b hb)
        h0_s hout_s
        (fun b hb => by dsimp [wst_s]; rw [List.getElem?_drop, hsl_eq, hsl_ks]; exact hepos_s b hb)
        (fun b hb p hp1 hp2 => by
          dsimp [wst_s] at hp2; rw [List.getElem?_drop] at hp2
          rw [hsl_eq] at hp1; exact hbkt_s b hb p hp1 hp2)
        (by
          have hcon : m7FlatBkts tmp_s
              (m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_s 1 N)))
              (fun b => (wst_s[b]?.getD 0#32).toNat) span =
              m7FlatBkts tmp_s spos (fun b => (ws_s[c.max_vars + b]?.getD 0#32).toNat) span := by
            have h1 : m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_s 1 N)) = spos := by
              rw [hsl_eq]
            rw [h1]
            simp only [wst_s, List.getElem?_drop]
          rw [hcon, hsl_ks]; exact hperm_s)
      have hx_min : minL ≤ v103.toNat := by
        have h := (hminmax_s k_s hk1 hk_lt).1
        rw [List.getElem?_eq_getElem (l := ws_s) (i := k_s) hks_ws, Option.getD_some,
          List.getElem?_eq_getElem (l := s.core.lvl) (i := v97.toNat / 2) hv97_lvl,
          Option.getD_some] at h
        exact h
      have hbi_eq : v103.toNat - minL = m7Bkt s.core.lvl minL v97 := by
        rw [m7Bkt_eq, List.getElem?_eq_getElem (l := s.core.lvl) (i := v97.toNat / 2) hv97_lvl,
          Option.getD_some]
      have hx106_eq : BitVec.setWidth 64 v103 - BitVec.setWidth 64 minL_bv =
          BitVec.ofNat 64 (m7Bkt s.core.lvl minL v97) := by
        rw [m7_sub_zext64_of_le hx_min, hbi_eq]
      rw [hx106_eq]
      let bi := m7Bkt s.core.lvl minL v97
      have hbi_lt : bi < span := hstep.1
      have hidx64 : BitVec.ofNat 64 c.max_vars + BitVec.ofNat 64 bi =
          BitVec.ofNat 64 (c.max_vars + bi) :=
        m7_add_bv64_ofNat (by omega)
      rw [hidx64]
      have hbi_w : c.max_vars + bi < ws_s.length := by rw [hlen_ws]; omega
      have hld_v109 := m7_load_wsort_nat hst_s hbi_w (by omega) hm
      m7_ld hld_v109
      m7_lets
      let dst_bv := ws_s[c.max_vars + bi]'hbi_w
      let dst := dst_bv.toNat
      have hdst_eq : dst_bv = wst_s[bi]'(by rw [hwst_len]; omega) := by
        dsimp [dst_bv, wst_s]; simp [List.getElem_drop]
      have hdst_ge1 : 1 ≤ dst := by dsimp [dst]; rw [hdst_eq]; exact hstep.2.1
      have hdst1_32 : dst + 1 < 2 ^ 32 := by dsimp [dst]; rw [hdst_eq]; exact hstep.2.2.2.1
      rw [hidx64, m7_trunc_add1_32 hdst1_32]
      obtain ⟨st1, hst1_c, hst1_s, hok1, hm1_raw⟩ := m7_store_wsort_nat (i := c.max_vars + bi)
        (BitVec.ofNat 32 (dst + 1)) hst_c hst_s hbi_w (by omega) hm
      m7_st m1, hm1 := And.intro hok1 hm1_raw
      m7_lets
      have hv109_eq : BitVec.setWidth 64 dst_bv = BitVec.ofNat 64 dst := by
        apply BitVec.eq_of_toNat_eq
        have hdst64 : dst < 2 ^ 64 := Nat.lt_trans dst_bv.isLt (by decide : 2 ^ 32 < 2 ^ 64)
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdst64]
      rw [hv109_eq]
      have hdst_lt : dst < N := by dsimp [dst]; rw [hdst_eq]; exact hstep.2.2.1
      have hdst_ts : dst < tmp_s.length := by rw [hlen_ts]; omega
      obtain ⟨st2, hst2_c, hst2_s, hok2, hm2_raw⟩ := m7_store_tmp_nat (i := dst) v97 hst1_c
        hst1_s hdst_ts (by omega) hm1
      m7_st m2, hm2 := And.intro hok2 hm2_raw
      m7_lets
      have hk1_bv : BitVec.ofNat 64 k_s + (1 : BitVec 64) = BitVec.ofNat 64 (k_s + 1) :=
        m7_add1_bv64 (by omega)
      rw [hk1_bv]
      let ws_s1 := ws_s.set (c.max_vars + bi) (BitVec.ofNat 32 (dst + 1))
      have hpre1 : ∀ q < c.max_vars, ws_s1[q]? = ws0[q]? := fun q hq => by
        dsimp [ws_s1]; rw [List.getElem?_set_ne (by omega)]; exact hpre q hq
      have hd_drop : ws_s1.drop c.max_vars = wst_s.set bi (BitVec.ofNat 32 (dst + 1)) :=
        m7_drop_set_offset ws_s _ hlen_ws (by omega)
      have hdst_raw : dst_bv =
          wst_s[m7Bkt s.core.lvl minL ws_s[k_s]]'(by rw [hwst_len]; have := hstep.1; omega) := by
        simpa only [bi, v97] using hdst_eq
      have hd_drop_raw : ws_s1.drop c.max_vars =
          wst_s.set (m7Bkt s.core.lvl minL ws_s[k_s])
            (BitVec.ofNat 32 (wst_s[m7Bkt s.core.lvl minL ws_s[k_s]].toNat + 1)) := by
        simpa only [bi, v97, dst, hdst_raw] using hd_drop
      have hsl_k1 : m7Slice ws_s 1 (k_s + 1) = m7Slice ws0 1 (k_s + 1) :=
        m7Slice_congr_lt (by omega) (by rw [hlen_ws]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      refine hIH (N - (k_s + 1)) (BitVec.ofNat 64 (k_s + 1), ()) _ (by omega)
        ⟨k_s + 1, st2, tmp_s.set dst v97, ws_s1,
          rfl, by omega, by omega, rfl, hst2_c, hst2_s,
          by simp [hlen_ts],
          by simp [ws_s1, hlen_ws], hpre1,
          by rw [List.getElem?_set_ne (by omega)]; exact h0_s,
          fun q hq => by rw [List.getElem?_set_ne (by omega)]; exact hout_s q hq,
          fun b hb => by
            have h := hstep.2.2.2.2.2.2.2.2.1 b hb
            simpa only [spos, minL, N, ← hd_drop_raw, List.getElem?_drop, hsl_eq, hsl_k1] using h,
          fun b hb p hp1 hp2 => by
            have h := hstep.2.2.2.2.2.2.2.2.2.1 b hb p
              (by simpa only [spos, tot, minL, N, hsl_eq] using hp1)
              (by simpa only [← hd_drop_raw, List.getElem?_drop] using hp2)
            simpa only [dst, v97, ← hdst_raw] using h,
          by
            have h := hstep.2.2.2.2.2.2.2.2.2.2
            rw [← hd_drop_raw, ← hdst_raw] at h
            have hcon : m7FlatBkts (tmp_s.set dst v97) spos
                (fun b => (ws_s1[c.max_vars + b]?.getD 0#32).toNat) span =
                m7FlatBkts (tmp_s.set dst v97)
                  (m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_s 1 N)))
                  (fun b => ((ws_s1.drop c.max_vars)[b]?.getD 0#32).toNat) span := by
              have h1 : m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_s 1 N)) = spos := by
                rw [hsl_eq]
              rw [h1]; simp [List.getElem?_drop]
            rw [hcon]
            simpa only [dst, v97, N, hsl_k1] using h,
          hm2⟩
    · have hk_ge : N ≤ k_s := by
        have h := m7_ult64_false hge_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
      have hk_eq : k_s = N := by omega
      subst hk_eq
      have hsl_eq : m7Slice ws_s 1 N = m7Slice ws0 1 N :=
        m7Slice_congr_lt (by omega) (by rw [hlen_ws]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      have hfin := m7_scat_finish_inv hlen_ts htl (hsl_eq.trans hsl_ws)
        (by rw [hsl_eq]; exact hspos_N)
        (fun b hb => by
          rw [List.getElem?_drop, hsl_eq]; exact hepos_s b hb)
        (fun b hb p hp1 hp2 => by
          rw [List.getElem?_drop] at hp2
          rw [hsl_eq] at hp1; exact hbkt_s b hb p hp1 hp2)
        (by
          have hcon : m7FlatBkts tmp_s
              (m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_s 1 N)))
              (fun b => ((ws_s.drop c.max_vars)[b]?.getD 0#32).toNat) span =
              m7FlatBkts tmp_s spos (fun b => (ws_s[c.max_vars + b]?.getD 0#32).toNat) span := by
            have h1 : m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_s 1 N)) = spos := by
              rw [hsl_eq]
            rw [h1]; simp [List.getElem?_drop]
          rw [hcon, hsl_eq]; exact hperm_s)
      exact hNext st tmp_s ws_s m hst_c hst_s hlen_ts hlen_ws hfin.1 h0_s hout_s hfin.2 hm
  · intro J92 hExit92
    apply hExit92 (N - 1) (BitVec.ofNat 64 1, ()) m0
    refine ⟨1, st0, s.core.tmp, ws0, rfl, le_refl 1, h1N, rfl, hc0, hs0, htmp_len, hlen_ws0,
      fun _ _ => rfl, rfl, fun _ _ => rfl, ?_, ?_, ?_, hm0⟩
    · intro b hb; rw [m7Slice_nil _ (le_refl 1), m7BktCnt_nil, Nat.add_zero]; exact hspos0 b hb
    · intro b hb p hp1 hp2
      change spos b ≤ p at hp1; rw [hspos0 b hb] at hp2
      dsimp only [spos, tot, minL, N] at hp1; omega
    · rw [m7FlatBkts_nil _ _ _ _ (fun b hb => by
          rw [hspos0 b hb]; dsimp only [spos, tot, minL]; exact Nat.le_refl _),
        m7Slice_nil _ (le_refl 1)]

private theorem m7_sort_rins_wp {Γ : Env} {c : FullCfg} {s st0 : FullState}
    {tmp_r : List (BitVec 32)} {sc0 : FullScratch} {R : Mem 64 → Prop} {m0 : Mem 64}
    {Q : Post []} {X : XPost} {N rb re : Nat} {kNext : Expr Val Cont []}
    (htmp_len : s.core.tmp.length = c.max_vars)
    (htpos_len : s.core.trail_pos.length = c.max_vars)
    (htl : N ≤ c.max_vars) (hrb1 : 1 ≤ rb) (hrbe : rb + 2 ≤ re) (hre_N : re ≤ N)
    (hperm_r : (m7Slice tmp_r 1 N).Perm (m7Slice s.core.tmp 1 N))
    (hbd0 : ∀ p, 1 ≤ p → p < N → (s.core.tmp[p]?.getD 0#32).toNat < 2 * c.max_vars)
    (hc0 : st0.core = { s.core with tmp := tmp_r }) (hs0 : st0.scratch = sc0)
    (hlen_r : tmp_r.length = c.max_vars) (hm0 : (FullMem c st0 ⋆ R) m0)
    (hNext : ∀ st' tmp_ri m',
      st'.core = { s.core with tmp := tmp_ri } → st'.scratch = sc0 →
      tmp_ri.length = c.max_vars →
      (m7Slice tmp_ri rb re).Perm (m7Slice tmp_r rb re) →
      (∀ q, (q < rb ∨ re ≤ q) → tmp_ri[q]? = tmp_r[q]?) →
      (∀ i j, rb ≤ i → i ≤ j → j < re →
        (s.core.trail_pos[(tmp_ri[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.trail_pos[(tmp_ri[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (FullMem c st' ⋆ R) m' → wp Γ Q X kNext m') :
    wp Γ Q X (m7SortRInsExpr c.pTmp c.pTrailPos (BitVec.ofNat 64 rb) (BitVec.ofNat 64 re)
      (BitVec.ofNat 64 (rb + 1)) kNext) m0 := by
  have hre64 : re < 2 ^ 64 := by have := c.hmaxv; unfold dimacsBound at this; omega
  let ltTP : BitVec 32 → BitVec 32 → Prop := fun a b =>
    (s.core.trail_pos[a.toNat / 2]?.getD 0#32).toNat ≤
    (s.core.trail_pos[b.toNat / 2]?.getD 0#32).toNat
  let InvOut : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ i st tmp_i, xs.1 = BitVec.ofNat 64 i ∧ rb + 1 ≤ i ∧ i ≤ re ∧ meas = re - i ∧
      st.core = { s.core with tmp := tmp_i } ∧ st.scratch = sc0 ∧
      tmp_i.length = c.max_vars ∧ (m7Slice tmp_i rb re).Perm (m7Slice tmp_r rb re) ∧
      (∀ q, (q < rb ∨ re ≤ q) → tmp_i[q]? = tmp_r[q]?) ∧
      (∀ a b, rb ≤ a → a ≤ b → b < i →
        ltTP (tmp_i[a]?.getD 0#32) (tmp_i[b]?.getD 0#32)) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group InvOut ?_ ?_
  · intro J118 meas xs m hm_ex ⟨i, st, tmp_i, hxs, hi_lo, hi_re, hmeas, hst_c, hst_s,
      hlen_i, hperm_i, hout_i, hsort_i, hm⟩
    rw [Blocks.get_here]
    m7_lets
    m7_jnz
    refine ⟨fun hlt_b => ?_, fun hge_b => ?_⟩
    · have hi_lt : i < re := by
        have h := m7_ult64_true hlt_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hre64, Nat.mod_eq_of_lt (by omega)] at h
      have hi_tmp : i < tmp_i.length := by rw [hlen_i]; omega
      have hperm_i_N : (m7Slice tmp_i 1 N).Perm (m7Slice s.core.tmp 1 N) :=
        (m7_slice_perm_sub (xs := tmp_i) (ys := tmp_r) hrb1 (by omega) hre_N
          (by rw [hlen_i]; exact htl) (by rw [hlen_r]; exact htl) hperm_i hout_i).trans hperm_r
      have hbd_i := m7Slice_perm_bd hperm_i_N (by rw [hlen_i]; exact htl)
        (by rw [htmp_len]; exact htl) hbd0 i (by omega) (by omega)
      rw [List.getElem?_eq_getElem (l := tmp_i) (i := i) hi_tmp, Option.getD_some] at hbd_i
      m7_lets
      rw [hxs]
      have hld_v124 := m7_load_tmp_nat hst_c hi_tmp (by omega) hm
      m7_ld hld_v124
      m7_lets
      let v124 := tmp_i[i]'hi_tmp
      have hv124_bd : v124.toNat < 2 * c.max_vars := hbd_i
      rw [m7_var_idx64 v124]
      have hv124_tp : v124.toNat / 2 < s.core.trail_pos.length := by rw [htpos_len]; omega
      have hld_v130 := m7_load_tpos_nat hst_c hv124_tp (by omega) hm
      m7_ld hld_v130
      let v130 := s.core.trail_pos[v124.toNat / 2]'hv124_tp
      let InvIn : Nat → Tup Val [i64, .bool] → Mem 64 → Prop := fun m_in ys m_cur =>
        ∃ j cont st_j tmp_j,
          ys.1 = BitVec.ofNat 64 j ∧ ys.2.1 = cont ∧ rb ≤ j ∧ j ≤ i ∧
          m_in = j + (if cont then 1 else 0) ∧
          st_j.core = { s.core with tmp := tmp_j } ∧ st_j.scratch = sc0 ∧
          tmp_j.length = c.max_vars ∧
          (m7Slice (tmp_j.set j v124) rb re).Perm (m7Slice tmp_r rb re) ∧
          (∀ q, (q < rb ∨ re ≤ q) → tmp_j[q]? = tmp_r[q]?) ∧
          (∀ a b, rb ≤ a → a ≤ b → b ≤ i → a ≠ j → b ≠ j →
            ltTP (tmp_j[a]?.getD 0#32) (tmp_j[b]?.getD 0#32)) ∧
          (∀ k, j < k → k ≤ i → ltTP v124 (tmp_j[k]?.getD 0#32)) ∧
          (cont = false → rb < j → ltTP (tmp_j[j - 1]?.getD 0#32) v124) ∧
          (FullMem c st_j ⋆ R) m_cur
      refine wp_loop_group InvIn ?_ ?_
      · intro J131 m_in ys m_cur hIH_in ⟨j, cont, st_j, tmp_j, hys1, hys2, hj_lo, hji, hmin,
          hstj_c, hstj_s, hlen_j, hperm_j, hout_j, hinv_j, hgt_j, hstop_j, hm_j⟩
        rw [Blocks.get_here]
        m7_lets
        m7_jnz
        refine ⟨fun hcont_t => ?_, fun hcont_f => ?_⟩
        · have hcont : cont = true := by simpa [hys2] using hcont_t
          subst hcont
          simp only [↓reduceIte] at hmin
          let Pj134 : Tup Val [i64, .bool] → Mem 64 → Prop := fun ys2 m2 =>
            ∃ n', n' < m_in ∧ InvIn n' ys2 m2
          refine wp_join_group Pj134 ?_ ?_
          · intro J134 ys2 m2 ⟨n', hn', hInv'⟩
            rw [Blocks.get_here]
            exact hIH_in n' ys2 m2 hn' hInv'
          · intro J134 hExit134
            m7_lets
            m7_jnz
            refine ⟨fun hule_b => ?_, fun hule_f => ?_⟩
            ·
              have hj_eq : j = rb := by
                have h := m7_ule64_true hule_b
                rw [hys1, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
                omega
              apply hExit134
              refine ⟨j, by rw [hmin]; omega, j, false, st_j, tmp_j, hys1, rfl, hj_lo, hji,
                by simp, hstj_c, hstj_s, hlen_j, hperm_j, hout_j, hinv_j, hgt_j,
                fun _ hbad => by omega, hm_j⟩
            ·
              have hj_gtrb : rb < j := by
                have h := m7_ule64_false hule_f
                rw [hys1, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
                exact h
              have hj_sub_eq : ys.1 - (1 : BitVec 64) = BitVec.ofNat 64 (j - 1) := by
                rw [hys1]; exact m7_sub1_bv64 (by omega) (by omega)
              m7_lets
              rw [hj_sub_eq]
              have hj1_lt : j - 1 < tmp_j.length := by rw [hlen_j]; omega
              have hld_v140 := m7_load_tmp_nat hstj_c hj1_lt (by omega) hm_j
              m7_ld hld_v140
              m7_lets
              let v140 := tmp_j[j - 1]'hj1_lt
              have hv140_bd : v140.toNat < 2 * c.max_vars := by
                have hout_s : ∀ q, (q < rb ∨ re ≤ q) → (tmp_j.set j v124)[q]? = tmp_r[q]? :=
                  fun q hq => by
                    rw [List.getElem?_set_ne (by omega)]; exact hout_j q hq
                have hperm_j_N : (m7Slice (tmp_j.set j v124) 1 N).Perm (m7Slice s.core.tmp 1 N) :=
                  (m7_slice_perm_sub (xs := tmp_j.set j v124) (ys := tmp_r) hrb1 (by omega) hre_N
                    (by simp [hlen_j]; exact htl) (by rw [hlen_r]; exact htl)
                    hperm_j hout_s).trans hperm_r
                have hs_bd := m7Slice_perm_bd hperm_j_N (by simp [hlen_j]; exact htl)
                  (by rw [htmp_len]; exact htl) hbd0 (j - 1) (by omega) (by omega)
                rw [List.getElem?_set_ne (by omega),
                  List.getElem?_eq_getElem (l := tmp_j) (i := j - 1) hj1_lt,
                  Option.getD_some] at hs_bd
                exact hs_bd
              refine wp_join_group Pj134 ?_ ?_
              · intro J141 ys142 m142 hP142
                rw [Blocks.get_here]
                exact hExit134 ys142 m142 hP142
              · intro J141 hExit141
                m7_lets
                rw [m7_var_idx64 v140]
                have hv140_tp : v140.toNat / 2 < s.core.trail_pos.length := by
                  rw [htpos_len]; omega
                have hld_v148 := m7_load_tpos_nat hstj_c hv140_tp (by omega) hm_j
                m7_ld hld_v148
                let v148 := s.core.trail_pos[v140.toNat / 2]'hv140_tp
                m7_lets
                m7_jnz
                refine ⟨fun hle_tp => ?_, fun hgt_tp => ?_⟩
                ·
                  have htp_le : v148.toNat ≤ v130.toNat := m7_ule32_true hle_tp
                  have hle_f : ltTP (tmp_j[j - 1]?.getD 0#32) v124 := by
                    dsimp only [ltTP]
                    rw [List.getElem?_eq_getElem (l := tmp_j) (i := j - 1) hj1_lt,
                      Option.getD_some,
                      List.getElem?_eq_getElem (l := s.core.trail_pos) (i := v140.toNat / 2)
                        hv140_tp,
                      List.getElem?_eq_getElem (l := s.core.trail_pos) (i := v124.toNat / 2)
                        hv124_tp,
                      Option.getD_some, Option.getD_some]
                    exact htp_le
                  apply hExit141
                  refine ⟨j, by rw [hmin]; omega, j, false, st_j, tmp_j, hys1, rfl, hj_lo, hji,
                    by simp, hstj_c, hstj_s, hlen_j, hperm_j, hout_j, hinv_j, hgt_j,
                    fun _ _ => hle_f, hm_j⟩
                ·
                  have htp_lt : v130.toNat < v148.toNat := m7_ule32_false hgt_tp
                  m7_lets
                  have hj_lt : j < tmp_j.length := by rw [hlen_j]; omega
                  rw [hys1]
                  obtain ⟨st_s, hst_sc, hst_ss, hok_s, hm_s0⟩ :=
                    m7_store_tmp_nat (i := j) v140 hstj_c
                    hstj_s hj_lt (by omega) hm_j
                  m7_st m_s, hm_s := And.intro hok_s hm_s0
                  m7_lets
                  let tmp_j' := tmp_j.set j v140
                  have hj1_bv : BitVec.ofNat 64 j - (1 : BitVec 64) = BitVec.ofNat 64 (j - 1) :=
                    m7_sub1_bv64 (by omega) (by omega)
                  rw [hj1_bv]
                  have hv140_get : tmp_j[j - 1]?.getD 0#32 = v140 := by
                    rw [List.getElem?_eq_getElem (l := tmp_j) (i := j - 1) hj1_lt,
                      Option.getD_some]
                  have hlt_f : ltTP v124 (tmp_j[j - 1]?.getD 0#32) := by
                    dsimp only [ltTP]
                    rw [hv140_get,
                      List.getElem?_eq_getElem (l := s.core.trail_pos) (i := v124.toNat / 2)
                        hv124_tp,
                      List.getElem?_eq_getElem (l := s.core.trail_pos) (i := v140.toNat / 2)
                        hv140_tp,
                      Option.getD_some, Option.getD_some]
                    exact Nat.le_of_lt htp_lt
                  have htmpj'_set : tmp_j' = tmp_j.set j (tmp_j[j - 1]?.getD 0#32) := by
                    simp [tmp_j', hv140_get]
                  have hi_j : i < tmp_j.length := by rw [hlen_j]; omega
                  have hshift := m7_ins_shift_inv (ltp := ltTP) (xs := tmp_j) (lo := rb)
                    (i := i) (j := j) (x := v124) hj_gtrb hji hi_j hinv_j hgt_j hlt_f
                  have hperm_j' :
                      (m7Slice (tmp_j'.set (j - 1) v124) rb re).Perm (m7Slice tmp_r rb re) :=
                    (m7_shift_slice_perm (xs := tmp_j) (lo := rb) (hi := re) (j := j) (j' := j - 1)
                      v124 (by omega) (by omega) (by omega)
                      (by rw [hlen_j]; exact Nat.le_trans hre_N htl)).trans hperm_j
                  apply hExit141
                  refine ⟨(j - 1) + 1, by rw [hmin]; omega, j - 1, true, st_s, tmp_j',
                    rfl, by simpa using hys2,
                    by omega, by omega, rfl, hst_sc, hst_ss, by simp [tmp_j', hlen_j], hperm_j',
                    fun q hq => by dsimp [tmp_j']; rw [List.getElem?_set_ne (by omega)]
                                   exact hout_j q hq,
                    by simpa [htmpj'_set] using hshift.1,
                    by simpa [htmpj'_set] using hshift.2,
                    fun hbad => absurd hbad (by decide), hm_s⟩
        · have hcont : cont = false := by simpa [hys2] using hcont_f
          m7_lets
          have hj_lt : j < tmp_j.length := by rw [hlen_j]; omega
          rw [hys1]
          obtain ⟨st_e, hst_ec, hst_es, hok_e, hm_e0⟩ :=
            m7_store_tmp_nat (i := j) v124 hstj_c hstj_s
            hj_lt (by omega) hm_j
          m7_st m_e, hm_e := And.intro hok_e hm_e0
          m7_lets
          let tmp_e := tmp_j.set j v124
          have hi_j : i < tmp_j.length := by rw [hlen_j]; omega
          have hsort_e := m7_ins_place_sorted (ltp := ltTP)
            (fun a => le_refl _) (fun a b c h1 h2 => Nat.le_trans h1 h2)
            (xs := tmp_j) (lo := rb) (i := i) (j := j) (x := v124)
            hj_lo hji hi_j hinv_j (hstop_j hcont) hgt_j
          have hi1_bv : BitVec.ofNat 64 i + (1 : BitVec 64) = BitVec.ofNat 64 (i + 1) :=
            m7_add1_bv64 (by omega)
          rw [hi1_bv]
          exact hm_ex (re - (i + 1)) (BitVec.ofNat 64 (i + 1), ()) _ (by omega)
            ⟨i + 1, st_e, tmp_e, rfl, by omega, by omega, rfl, hst_ec, hst_es,
              by simp [tmp_e, hlen_j], hperm_j,
              fun q hq => by dsimp [tmp_e]; rw [List.getElem?_set_ne (by omega)]
                             exact hout_j q hq,
              fun a b ha hab hb => hsort_e a b ha hab (by omega), hm_e⟩
      · intro J132 hExit132
        apply hExit132 (i + 1) (BitVec.ofNat 64 i, true, ()) m
        refine ⟨i, true, st, tmp_i, rfl, rfl, by omega, le_refl i, rfl, hst_c, hst_s,
          hlen_i, ?_, hout_i, ?_, fun k hk1 hk2 => by omega,
          fun hbad => absurd hbad (by decide), hm⟩
        · have hset : tmp_i.set i v124 = tmp_i := by
            apply List.ext_getElem
            · simp
            · intro p hp1 hp2
              by_cases hpi : p = i
              · subst hpi; simp [v124]
              · simp [List.getElem_set_ne (Ne.symm hpi)]
          simpa [hset] using hperm_i
        · intro a b ha hab hbi _ _
          exact hsort_i a b ha hab (by omega)
    · have hi_ge : re ≤ i := by
        have h := m7_ult64_false hge_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hre64, Nat.mod_eq_of_lt (by omega)] at h
      have hi_eq : i = re := by omega
      subst hi_eq
      exact hNext st tmp_i m hst_c hst_s hlen_i hperm_i hout_i hsort_i hm
  · intro J119 hExit119
    apply hExit119 (re - (rb + 1)) (BitVec.ofNat 64 (rb + 1), ()) m0
    refine ⟨rb + 1, st0, tmp_r, rfl, le_refl _, by omega, rfl, hc0, hs0, hlen_r, List.Perm.refl _,
      fun _ _ => rfl, ?_, hm0⟩
    intro a b ha hab hb
    have ha_rb : a = rb := by omega
    have hb_rb : b = rb := by omega
    subst ha_rb; subst hb_rb
    exact le_refl _

private theorem m7_sort_runs_wp {Γ : Env} {c : FullCfg} {s st0 : FullState}
    {tmp0 : List (BitVec 32)} {sc0 : FullScratch} {R : Mem 64 → Prop} {m0 : Mem 64}
    {Q : Post []} {X : XPost}
    (hHeap : ∀ (args : Tup Val [i64, i64, i64, i64]) (m : Mem 64)
      (Q : Post []) (X : XPost), m7SortTmpHeapSpec args m Q X →
      Γ "full_sort_tmp_heap_m7" [i64, i64, i64, i64] [] args m Q X)
    (htmp_len : s.core.tmp.length = c.max_vars)
    (hlvl_len : s.core.lvl.length = c.max_vars)
    (htpos_len : s.core.trail_pos.length = c.max_vars)
    (htl : s.core.tmp_len ≤ c.max_vars) (h1lt : 1 ≤ s.core.tmp_len)
    (hbd0 : ∀ p, 1 ≤ p → p < s.core.tmp_len →
      (s.core.tmp[p]?.getD 0#32).toNat < 2 * c.max_vars)
    (hc0 : st0.core = { s.core with tmp := tmp0 }) (hs0 : st0.scratch = sc0)
    (hlen0 : tmp0.length = c.max_vars)
    (hperm0 : (m7Slice tmp0 1 s.core.tmp_len).Perm (m7Slice s.core.tmp 1 s.core.tmp_len))
    (h0_0 : tmp0[0]? = s.core.tmp[0]?)
    (hout0 : ∀ q, s.core.tmp_len ≤ q → tmp0[q]? = s.core.tmp[q]?)
    (hlvl0 : ∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
      (s.core.lvl[(tmp0[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(tmp0[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hPost : ∀ st' tmp' m',
      st'.core = { s.core with tmp := tmp' } → st'.scratch = sc0 →
      tmp'.length = c.max_vars →
      (m7Slice tmp' 1 s.core.tmp_len).Perm (m7Slice s.core.tmp 1 s.core.tmp_len) →
      tmp'[0]? = s.core.tmp[0]? →
      (∀ q, s.core.tmp_len ≤ q → tmp'[q]? = s.core.tmp[q]?) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        Full.fullTmpLe s.core.lvl s.core.trail_pos
          (tmp'[i]?.getD 0#32) (tmp'[j]?.getD 0#32)) →
      (FullMem c st' ⋆ R) m' → Q () m') :
    wp Γ Q X
      (m7SortRunsExpr (BitVec.ofNat 64 s.core.tmp_len) c.pTmp c.pLevel c.pTrailPos) m0 := by
  let N := s.core.tmp_len
  have hN64 : N < 2 ^ 64 := by have := c.hmaxv; unfold dimacsBound at this; omega
  let InvOut : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ rb st tmp_r, xs.1 = BitVec.ofNat 64 rb ∧ 1 ≤ rb ∧ rb ≤ N ∧ meas = N - rb ∧
      st.core = { s.core with tmp := tmp_r } ∧ st.scratch = sc0 ∧
      tmp_r.length = c.max_vars ∧ (m7Slice tmp_r 1 N).Perm (m7Slice s.core.tmp 1 N) ∧
      tmp_r[0]? = s.core.tmp[0]? ∧ (∀ q, N ≤ q → tmp_r[q]? = s.core.tmp[q]?) ∧
      (∀ i j, 1 ≤ i → i ≤ j → j < N →
        (s.core.lvl[(tmp_r[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp_r[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
      (1 < rb → rb < N →
        (s.core.lvl[(tmp_r[rb - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
        (s.core.lvl[(tmp_r[rb]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
      (∀ i j, 1 ≤ i → i ≤ j → j < rb →
        Full.fullTmpLe s.core.lvl s.core.trail_pos
          (tmp_r[i]?.getD 0#32) (tmp_r[j]?.getD 0#32)) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group InvOut ?_ ?_
  · intro J156 meas xs m hIH ⟨rb, st, tmp_r, hxs, hrb1, hrb_N, hmeas, hst_c, hst_s,
      hlen_r, hperm_r, h0_r, hout_r, hlvl_r, hbdry_r, hsort_r, hm⟩
    rw [Blocks.get_here]
    m7_lets
    m7_jnz
    refine ⟨fun hlt_b => ?_, fun hge_b => ?_⟩
    · have hrb_lt : rb < N := by
        have h := m7_ult64_true hlt_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
      have hrb_tmp : rb < tmp_r.length := by rw [hlen_r]; omega
      have hbd_rb := m7Slice_perm_bd hperm_r (by rw [hlen_r]; exact htl)
        (by rw [htmp_len]; exact htl) hbd0 rb hrb1 hrb_lt
      rw [List.getElem?_eq_getElem (l := tmp_r) (i := rb) hrb_tmp, Option.getD_some] at hbd_rb
      m7_lets
      rw [hxs]
      have hld_v162 := m7_load_tmp_nat hst_c hrb_tmp (by omega) hm
      m7_ld hld_v162
      m7_lets
      let v162 := tmp_r[rb]'hrb_tmp
      have hv162_bd : v162.toNat < 2 * c.max_vars := hbd_rb
      rw [m7_var_idx64 v162]
      have hv162_lvl : v162.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
      have hld_v168 := m7_load_lvl_nat hst_c hv162_lvl (by omega) hm
      m7_ld hld_v168
      m7_lets
      let rl_bv := s.core.lvl[v162.toNat / 2]'hv162_lvl
      let rl := rl_bv.toNat
      have hrb1_bv : BitVec.ofNat 64 rb + (1 : BitVec 64) = BitVec.ofNat 64 (rb + 1) :=
        m7_add1_bv64 (by omega)
      rw [hrb1_bv]
      let InvScan : Nat → Tup Val [i64, .bool] → Mem 64 → Prop := fun m_sc ys m_cur =>
        ∃ re cont, ys.1 = BitVec.ofNat 64 re ∧ ys.2.1 = cont ∧
          rb + 1 ≤ re ∧ re ≤ N ∧ m_sc = (N - re) + (if cont then 1 else 0) ∧
          m_cur = m ∧
          (∀ p, rb ≤ p → p < re →
            (s.core.lvl[(tmp_r[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = rl) ∧
          (cont = false → re = N ∨
            rl < (s.core.lvl[(tmp_r[re]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
      refine wp_loop_group InvScan ?_ ?_
      · intro J170 m_sc ys m_cur hIH_sc ⟨re, cont, hys1, hys2, hre_lo, hre_hi, hmsc, hm_eq,
          hre_eq, hre_exit⟩
        subst m_cur
        rw [Blocks.get_here]
        m7_lets
        m7_jnz
        refine ⟨fun hcont_t => ?_, fun hcont_f => ?_⟩
        · have hcont : cont = true := by simpa [hys2] using hcont_t
          subst hcont
          simp only [↓reduceIte] at hmsc
          let Pj173 : Tup Val [i64, .bool] → Mem 64 → Prop := fun ys2 m2 =>
            ∃ n', n' < m_sc ∧ InvScan n' ys2 m2
          refine wp_join_group Pj173 ?_ ?_
          · intro J173 ys2 m2 ⟨n', hn', hInv'⟩
            rw [Blocks.get_here]
            exact hIH_sc n' ys2 m2 hn' hInv'
          · intro J173 hExit173
            m7_lets
            m7_jnz
            refine ⟨fun huge_b => ?_, fun huge_f => ?_⟩
            ·
              have hre_ge : N ≤ re := by
                have h := m7_ule64_true huge_b
                rwa [hys1, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
              have hre_eqN : re = N := by omega
              apply hExit173
              refine ⟨N - re, by rw [hmsc]; omega, re, false, hys1, rfl, hre_lo, hre_hi,
                by simp, rfl, hre_eq, fun _ => Or.inl hre_eqN⟩
            ·
              have hre_lt : re < N := by
                have h := m7_ule64_false huge_f
                rwa [hys1, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
              refine wp_join_group Pj173 ?_ ?_
              · intro J176 ys177 m177 hP177
                rw [Blocks.get_here]
                exact hExit173 ys177 m177 hP177
              · intro J176 hExit176
                m7_lets
                have hre_tmp : re < tmp_r.length := by rw [hlen_r]; omega
                have hbd_re := m7Slice_perm_bd hperm_r (by rw [hlen_r]; exact htl)
                  (by rw [htmp_len]; exact htl) hbd0 re (by omega) hre_lt
                rw [List.getElem?_eq_getElem (l := tmp_r) (i := re) hre_tmp,
                  Option.getD_some] at hbd_re
                rw [hys1]
                have hld_v180 := m7_load_tmp_nat hst_c hre_tmp (by omega) hm
                m7_ld hld_v180
                m7_lets
                let v180 := tmp_r[re]'hre_tmp
                have hv180_bd : v180.toNat < 2 * c.max_vars := hbd_re
                rw [m7_var_idx64 v180]
                have hv180_lvl : v180.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
                have hld_v186 := m7_load_lvl_nat hst_c hv180_lvl (by omega) hm
                m7_ld hld_v186
                let v186 := s.core.lvl[v180.toNat / 2]'hv180_lvl
                m7_lets
                m7_jnz
                refine ⟨fun hne_b => ?_, fun heq_b => ?_⟩
                ·
                  have hne_lv : v186 ≠ rl_bv := by simpa [bne_iff_ne] using hne_b
                  have hlt_rl :
                      rl < (s.core.lvl[(tmp_r[re]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
                    have hle := hlvl_r rb re hrb1 (by omega) hre_lt
                    rw [hre_eq rb (le_refl _) (by omega)] at hle
                    rw [List.getElem?_eq_getElem (l := tmp_r) (i := re) hre_tmp,
                      Option.getD_some,
                      List.getElem?_eq_getElem (l := s.core.lvl) (i := v180.toNat / 2) hv180_lvl,
                      Option.getD_some] at hle ⊢
                    have hne_nat : v186.toNat ≠ rl_bv.toNat := fun h =>
                      hne_lv (BitVec.eq_of_toNat_eq h)
                    change rl_bv.toNat ≤ v186.toNat at hle
                    exact Nat.lt_of_le_of_ne hle hne_nat.symm
                  m7_lets
                  apply hExit176
                  refine ⟨N - re, by rw [hmsc]; omega, re, false, rfl, rfl, hre_lo, hre_hi,
                    by simp, rfl, hre_eq, fun _ => Or.inr hlt_rl⟩
                ·
                  have heq_lv : v186 = rl_bv := by simpa [bne_iff_ne] using heq_b
                  m7_lets
                  have hre1_bv : BitVec.ofNat 64 re + (1 : BitVec 64) = BitVec.ofNat 64 (re + 1) :=
                    m7_add1_bv64 (by omega)
                  rw [hre1_bv]
                  apply hExit176
                  refine ⟨(N - (re + 1)) + 1, by rw [hmsc]; omega, re + 1, true, rfl,
                    by simpa using hys2,
                    by omega, by omega, rfl, rfl, fun p hp1 hp2 => ?_,
                    fun hbad => absurd hbad (by decide)⟩
                  by_cases hpre_eq : p = re
                  · subst p
                    rw [List.getElem?_eq_getElem (l := tmp_r) (i := re) hre_tmp, Option.getD_some,
                      List.getElem?_eq_getElem (l := s.core.lvl) (i := v180.toNat / 2) hv180_lvl,
                      Option.getD_some]
                    exact congrArg BitVec.toNat heq_lv
                  · exact hre_eq p hp1 (by omega)
        · have hcont : cont = false := by simpa [hys2] using hcont_f
          have hre_done := hre_exit hcont
          m7_lets
          rw [hys1]
          have hx189_eq : BitVec.ofNat 64 re - BitVec.ofNat 64 rb =
              BitVec.ofNat 64 (re - rb) :=
            m7_sub_bv64_ofNat (by omega) (by omega) (by omega)
          rw [hx189_eq]
          let Pj190 : Tup Val [] → Mem 64 → Prop := fun _ m190 =>
            ∃ n', n' < N - rb ∧ InvOut n' (BitVec.ofNat 64 re, ()) m190
          refine wp_join_group Pj190 ?_ ?_
          · intro J190 _ m190 ⟨n', hn', hInv'⟩
            rw [Blocks.get_here]
            exact hIH n' (BitVec.ofNat 64 re, ()) m190 (by rw [hmeas]; exact hn') hInv'
          · intro J190 hExit190
            m7_lets
            m7_jnz
            refine ⟨fun heq2_b => ?_, fun hne2_b => ?_⟩
            ·
              have hlen2 : re - rb = 2 := by
                have h := beq_iff_eq.mp heq2_b
                have hn := congrArg BitVec.toNat h
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : re - rb < 2 ^ 64),
                  show (2 : BitVec 64).toNat = 2 from rfl] at hn
                exact hn
              have hrb1_lt : rb + 1 < tmp_r.length := by rw [hlen_r]; omega
              have hbd_rb1 := m7Slice_perm_bd hperm_r (by rw [hlen_r]; exact htl)
                (by rw [htmp_len]; exact htl) hbd0 (rb + 1) (by omega) (by omega)
              rw [List.getElem?_eq_getElem (l := tmp_r) (i := rb + 1) hrb1_lt,
                Option.getD_some] at hbd_rb1
              m7_lets
              have hld_a := m7_load_tmp_nat hst_c hrb_tmp (by omega) hm
              m7_ld hld_a
              m7_lets
              rw [hrb1_bv]
              have hld_c := m7_load_tmp_nat hst_c hrb1_lt (by omega) hm
              m7_ld hld_c
              let a := tmp_r[rb]'hrb_tmp
              let c_lit := tmp_r[rb + 1]'hrb1_lt
              have ha_bd : a.toNat < 2 * c.max_vars := hbd_rb
              have hc_bd : c_lit.toNat < 2 * c.max_vars := hbd_rb1
              refine wp_join_group Pj190 ?_ ?_
              · intro J199 _ m199 hP199
                rw [Blocks.get_here]
                exact hExit190 () m199 hP199
              · intro J199 hExit199
                m7_lets
                rw [m7_var_idx64 a]
                have ha_tp : a.toNat / 2 < s.core.trail_pos.length := by rw [htpos_len]; omega
                have hc_tp : c_lit.toNat / 2 < s.core.trail_pos.length := by rw [htpos_len]; omega
                have hld_tpa := m7_load_tpos_nat hst_c ha_tp (by omega) hm
                m7_ld hld_tpa
                m7_lets
                rw [m7_var_idx64 c_lit]
                have hld_tpc := m7_load_tpos_nat hst_c hc_tp (by omega) hm
                m7_ld hld_tpc
                m7_lets
                m7_jnz
                refine ⟨fun hgt_tp => ?_, fun hle_tp => ?_⟩
                ·
                  have hlt_tp :
                      (s.core.trail_pos[c_lit.toNat / 2]'hc_tp).toNat <
                      (s.core.trail_pos[a.toNat / 2]'ha_tp).toNat :=
                    m7_ult32_true hgt_tp
                  have hsw := m7_run_swap2_inv htmp_len hlen_r hlvl_len htpos_len htl hrb1
                    (by omega) hperm_r hbd0 (fun p hp1 hp2 => hre_eq p hp1 (by omega)) hlt_tp
                  m7_lets
                  obtain ⟨st1, hst1_c, hst1_s, hok1, hm1_raw⟩ :=
                    m7_store_tmp_nat (i := rb) c_lit hst_c
                    hst_s hrb_tmp (by omega) hm
                  m7_st m1, hm1 := And.intro hok1 hm1_raw
                  m7_lets
                  rw [hrb1_bv]
                  have hrb1_lt' : rb + 1 < (tmp_r.set rb c_lit).length := by simp [hrb1_lt]
                  obtain ⟨st2, hst2_c, hst2_s, hok2, hm2_raw⟩ :=
                    m7_store_tmp_nat (i := rb + 1) a hst1_c
                    hst1_s hrb1_lt' (by omega) hm1
                  m7_st m2, hm2 := And.intro hok2 hm2_raw
                  let tmp_n := (tmp_r.set rb c_lit).set (rb + 1) a
                  have hnext := m7_run_next_inv htmp_len hlen_r hsw.1 hlvl_len htl hrb1 hrb_lt
                    hre_lo hre_hi hperm_r hlvl_r hbdry_r hsort_r hre_eq hre_done
                    (by have hr : re = rb + 2 := by omega
                        rw [congrArg (m7Slice tmp_n rb) hr, congrArg (m7Slice tmp_r rb) hr]
                        exact hsw.2.1)
                    (fun q hq => hsw.2.2.2.1 q (by rcases hq with h | h <;> omega))
                    (fun i j hi hij hj => hsw.2.2.2.2 i j hi hij (by omega)) hbd0
                  exact hExit199 () m2 ⟨N - re, by omega, re, st2, tmp_n, rfl, by omega, hre_hi,
                    rfl, hst2_c, hst2_s, hsw.1, hnext.1,
                    by rw [hsw.2.2.1]; exact h0_r,
                    fun q hq => by rw [hsw.2.2.2.1 q (Or.inr (by omega))]; exact hout_r q hq,
                    hnext.2.1, hnext.2.2.1, hnext.2.2.2, hm2⟩
                ·
                  have hle_tp' :
                      (s.core.trail_pos[a.toNat / 2]'ha_tp).toNat ≤
                      (s.core.trail_pos[c_lit.toNat / 2]'hc_tp).toNat :=
                    m7_ult32_false hle_tp
                  have hsort2 := m7_run_noswap2_inv htmp_len hlen_r hlvl_len htpos_len htl hrb1
                    (by omega) hperm_r hbd0 (fun p hp1 hp2 => hre_eq p hp1 (by omega)) hle_tp'
                  have hnext := m7_run_next_inv htmp_len hlen_r hlen_r hlvl_len htl hrb1 hrb_lt
                    hre_lo hre_hi hperm_r hlvl_r hbdry_r hsort_r hre_eq hre_done (List.Perm.refl _)
                    (fun _ _ => rfl) (fun i j hi hij hj => hsort2 i j hi hij (by omega)) hbd0
                  exact hExit199 () m ⟨N - re, by omega, re, st, tmp_r, rfl, by omega, hre_hi,
                    rfl, hst_c, hst_s, hlen_r, hnext.1, h0_r, hout_r, hnext.2.1,
                    hnext.2.2.1, hnext.2.2.2, hm⟩
            ·
              have hne2 : re - rb ≠ 2 := fun h => by simp [h] at hne2_b
              refine wp_join_group Pj190 ?_ ?_
              · intro J218 _ m218 hP218
                rw [Blocks.get_here]
                exact hExit190 () m218 hP218
              · intro J218 hExit218
                m7_lets
                m7_jnz
                refine ⟨fun hgt2_b => ?_, fun hle2_b => ?_⟩
                ·
                  have hgt2 : 2 < re - rb := by
                    have h := m7_ult64_true hgt2_b
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : re - rb < 2 ^ 64),
                      show (2 : BitVec 64).toNat = 2 from rfl] at h
                    exact h
                  refine wp_join_group Pj190 ?_ ?_
                  · intro J220 _ m220 hP220
                    rw [Blocks.get_here]
                    exact hExit218 () m220 hP220
                  · intro J220 hExit220
                    m7_lets
                    m7_jnz
                    refine ⟨fun hle16_b => ?_, fun hgt16_b => ?_⟩
                    ·
                      have hle16 : re - rb ≤ 16 := by
                        have h := m7_ule64_true hle16_b
                        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : re - rb < 2 ^ 64),
                          show (16 : BitVec 64).toNat = 16 from rfl] at h
                        exact h
                      m7_lets
                      rw [hrb1_bv]
                      exact m7_sort_rins_wp htmp_len htpos_len htl hrb1 (by omega) hre_hi
                        hperm_r hbd0 hst_c hst_s hlen_r hm fun st' tmp_ri m' hst_c' hst_s'
                          hlen_ri hperm_ri hout_ri hsort_ri hm' => by
                        have hsort_ri_f := m7_rins_finish_fullTmpLe htmp_len hlen_r hlen_ri
                          hlvl_len htpos_len htl hrb1 hre_hi (by omega) hperm_r hperm_ri
                          hout_ri hbd0 hre_eq hsort_ri
                        have hnext := m7_run_next_inv htmp_len hlen_r hlen_ri hlvl_len htl hrb1
                          hrb_lt hre_lo hre_hi hperm_r hlvl_r hbdry_r hsort_r hre_eq hre_done
                          hperm_ri hout_ri hsort_ri_f hbd0
                        exact hExit220 () m' ⟨N - re, by omega, re, st', tmp_ri, rfl, by omega,
                          hre_hi, rfl, hst_c', hst_s', hlen_ri, hnext.1,
                          by rw [hout_ri 0 (Or.inl (by omega))]; exact h0_r,
                          fun q hq => by rw [hout_ri q (Or.inr (by omega))]; exact hout_r q hq,
                          hnext.2.1, hnext.2.2.1, hnext.2.2.2, hm'⟩
                    ·
                      m7_lets
                      have hoff_lt : rb - 1 ≤ tmp_r.length := by rw [hlen_r]; omega
                      have hm_cp := hm
                      rw [m7_sub_ptr c.pTmp (BitVec.ofNat 64 rb)
                        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hrb1)
                        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                            have := c.hmaxv; unfold dimacsBound at this; omega)]
                      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                      have hsub_len : BitVec.ofNat 64 (re - rb) + (1 : BitVec 64) =
                          BitVec.ofNat 64 (re - rb + 1) := m7_add1_bv64 (by omega)
                      rw [hsub_len]
                      obtain ⟨F, hF, hrec⟩ := m7FullMem_focus_sub_heap (off := rb - 1)
                        (by rw [m7_core_tmp_eq hst_c]; exact hoff_lt) hm
                      rw [m7_core_tmp_eq hst_c, m7_core_lvl_eq hst_c, m7_core_tpos_eq hst_c]
                        at hF hrec
                      refine wp_call_of_spec _ _ ?_
                      dsimp only [LeanQbe.T.vals, Arg.val]
                      refine hHeap _ m _ _ (m7SortTmpHeapSpec_of ?_ ?_ ?_ hF ?_)
                      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                          List.length_drop, hlen_r]; omega
                      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                        have := c.hmaxv; unfold dimacsBound at this; omega
                      · intro k hk1 hk_lt
                        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hk_lt
                        rw [List.getElem?_drop]
                        have hbk := m7Slice_perm_bd hperm_r (by rw [hlen_r]; exact htl)
                          (by rw [htmp_len]; exact htl) hbd0 (rb - 1 + k) (by omega) (by omega)
                        rw [hlvl_len, htpos_len]; omega
                      · intro sub' m' hlen_s hperm_s h0_s hout_s _ hsort_s hm'
                        have hm_full := hrec sub' m' hm'
                        obtain ⟨st', hst_c', hst_s', hm_st'⟩ :=
                          m7_wrap_upd_tmp hst_c hst_s hm_full
                        have hsub_toNat : (BitVec.ofNat 64 (re - rb + 1)).toNat =
                            re - rb + 1 := by
                          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                        rw [hsub_toNat] at hperm_s h0_s hout_s hsort_s
                        have hfin := m7_run_heap_finish hlen_r htl hrb1 (by omega) hre_hi
                          hlen_s hperm_s h0_s hout_s hsort_s
                        let tmp_n := tmp_r.take (rb - 1) ++ sub'
                        have hnext := m7_run_next_inv htmp_len hlen_r hfin.1 hlvl_len htl hrb1
                          hrb_lt hre_lo hre_hi hperm_r hlvl_r hbdry_r hsort_r hre_eq hre_done
                          hfin.2.1 hfin.2.2.2.1 hfin.2.2.2.2 hbd0
                        exact hExit220 () m' ⟨N - re, by omega, re, st', tmp_n, rfl, by omega,
                          hre_hi, rfl, hst_c', hst_s', hfin.1, hnext.1,
                          by rw [hfin.2.2.1]; exact h0_r,
                          fun q hq => by rw [hfin.2.2.2.1 q (Or.inr (by omega))]; exact hout_r q hq,
                          hnext.2.1, hnext.2.2.1, hnext.2.2.2, hm_st'⟩
                ·
                  have hle2 : re - rb ≤ 2 := by
                    have h := m7_ult64_false hle2_b
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : re - rb < 2 ^ 64),
                      show (2 : BitVec 64).toNat = 2 from rfl] at h
                    exact h
                  have hre_rb1 : re = rb + 1 := by omega
                  have hnext := m7_run_next_inv htmp_len hlen_r hlen_r hlvl_len htl hrb1 hrb_lt
                    hre_lo hre_hi hperm_r hlvl_r hbdry_r hsort_r hre_eq hre_done (List.Perm.refl _)
                    (fun _ _ => rfl) (fun i j hi hij hj => by
                      have hi_rb : i = rb := by omega
                      have hj_rb : j = rb := by omega
                      subst hi_rb; subst hj_rb; exact m7_fullTmpLe_refl _ _ _) hbd0
                  exact hExit218 () m ⟨N - re, by omega, re, st, tmp_r, rfl, by omega, hre_hi,
                    rfl, hst_c, hst_s, hlen_r, hnext.1, h0_r, hout_r, hnext.2.1,
                    hnext.2.2.1, hnext.2.2.2, hm⟩
      · intro J171 hExit171
        m7_lets
        apply hExit171 (N - (rb + 1) + 1) (BitVec.ofNat 64 (rb + 1), true, ()) m
        refine ⟨rb + 1, true, rfl, rfl, le_refl _, hrb_lt, by simp, rfl, fun p hp1 hp2 => ?_,
          fun hbad => absurd hbad (by decide)⟩
        have hprb : p = rb := by omega
        subst p
        rw [List.getElem?_eq_getElem (l := tmp_r) (i := rb) hrb_tmp, Option.getD_some,
          List.getElem?_eq_getElem (l := s.core.lvl) (i := v162.toNat / 2) hv162_lvl,
          Option.getD_some]
    · have hrb_ge : N ≤ rb := by
        have h := m7_ult64_false hge_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
      have hrb_eq : rb = N := by omega
      subst hrb_eq
      exact hPost st tmp_r m hst_c hst_s hlen_r hperm_r h0_r hout_r hsort_r hm
  · intro J157 hExit157
    apply hExit157 (N - 1) (BitVec.ofNat 64 1, ()) m0
    refine ⟨1, st0, tmp0, rfl, le_refl 1, h1lt, rfl, hc0, hs0, hlen0, hperm0, h0_0, hout0,
      hlvl0, fun hbad => by omega, fun i j hi hij hj => by omega, hm0⟩

/-! ## 4. Main Exported WP Theorem -/

theorem full_sort_tmp_m7_wp (Γ : Env)
    (hHeap : ∀ (args : Tup Val [i64, i64, i64, i64]) (m : Mem 64)
      (Q : Post []) (X : XPost), m7SortTmpHeapSpec args m Q X →
      Γ "full_sort_tmp_heap_m7" [i64, i64, i64, i64] [] args m Q X) :
    ∀ (args : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost),
      m7SortTmpSpec args m Q X → Func.wp Γ full_sort_tmp_m7_body args m Q X := by
  intro args m Q X hspec
  rcases args with ⟨p_hd, ⟨⟩⟩
  obtain ⟨c, s, R, heq, hlenOk, htl, hbd, hm, hQ⟩ := m7SortTmpSpec_elim hspec
  dsimp only at heq; subst heq
  dsimp only [Func.wp, full_sort_tmp_m7_body]
  have htmp_len : s.core.tmp.length = c.max_vars := hlenOk.core_ok.tmp_len_arr
  have hlvl_len : s.core.lvl.length = c.max_vars := hlenOk.core_ok.lvl_len
  have htpos_len : s.core.trail_pos.length = c.max_vars := hlenOk.core_ok.trail_pos_len
  have hws_len : s.scratch.wsort.length = 2 * c.max_vars := hlenOk.scratch_ok.wsort_len
  have hmv64 : c.max_vars < 2 ^ 64 := by have := c.hmaxv; unfold dimacsBound at this; omega
  have hN64 : s.core.tmp_len < 2 ^ 64 := by omega
  m7_lets
  m7_ld (load_full_tmp_len hm)
  m7_lets
  m7_ld (load_full_max_vars hm)
  m7_lets
  m7_jnz
  refine ⟨fun hule2 => ?_, fun hgt2 => ?_⟩
  · have hNle2 : s.core.tmp_len ≤ 2 := by
      have h := m7_ule64_true hule2
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN64] using h
    obtain ⟨st0, hc0, hs0, hm0⟩ := m7_wrap_state hm
    exact m7_finish_spec hlenOk htl hc0 hs0 htmp_len hws_len (fun _ => rfl) (List.Perm.refl _)
      (fun _ => rfl) (fun i j hi hij hj => by
        have : i = 1 := by omega
        have : j = 1 := by omega
        subst_vars; exact m7_fullTmpLe_refl _ _ _) hm0 hQ
  · have hNgt2 : 2 < s.core.tmp_len := by
      have h := m7_ule64_false hgt2
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN64] using h
    m7_lets
    m7_jnz
    refine ⟨fun hbad_gt => ?_, fun _ => ?_⟩
    · have h := m7_ult64_true hbad_gt
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hmv64, Nat.mod_eq_of_lt hN64] at h
      omega
    · m7_lets
      m7_ld (load_full_tmp_lits_ptr hm)
      m7_lets
      m7_ld (load_full_level_ptr hm)
      m7_lets
      m7_ld (load_full_trail_pos_ptr hm)
      m7_lets
      m7_jnz
      refine ⟨fun heq3_b => ?_, fun hne3_b => ?_⟩
      · have hN3 : s.core.tmp_len = 3 := by
          have h := beq_iff_eq.mp heq3_b
          have hn := congrArg BitVec.toNat h
          simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN64] using hn
        obtain ⟨st0, hc0, hs0, hm0⟩ := m7_wrap_state hm
        m7_lets
        have hs1 : BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 := by decide
        have hs2 : BitVec.signExtend 64 (2 : BitVec 32) = BitVec.ofNat 64 2 := by decide
        rw [hs1]
        have h1t : 1 < s.core.tmp.length := by rw [htmp_len]; omega
        have h2t : 2 < s.core.tmp.length := by rw [htmp_len]; omega
        have hbd1 := hbd 1 (le_refl 1) (by omega)
        have hbd2 := hbd 2 (by omega) (by omega)
        rw [List.getElem?_eq_getElem (l := s.core.tmp) (i := 1) h1t, Option.getD_some] at hbd1
        rw [List.getElem?_eq_getElem (l := s.core.tmp) (i := 2) h2t, Option.getD_some] at hbd2
        have hld1 := m7_load_tmp_nat hc0 h1t (by decide) hm0
        m7_ld hld1
        m7_lets
        rw [hs2]
        have hld2 := m7_load_tmp_nat hc0 h2t (by decide) hm0
        m7_ld hld2
        let v1 := s.core.tmp[1]'h1t
        let v2 := s.core.tmp[2]'h2t
        have hv1_bd : v1.toNat < 2 * c.max_vars := hbd1
        have hv2_bd : v2.toNat < 2 * c.max_vars := hbd2
        m7_lets
        rw [m7_var_idx64 v1, m7_var_idx64 v2]
        have hl1 : v1.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
        have hl2 : v2.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
        have hld_l1 := m7_load_lvl_nat hc0 hl1 (by omega) hm0
        m7_ld hld_l1
        m7_lets
        have hld_l2 := m7_load_lvl_nat hc0 hl2 (by omega) hm0
        m7_ld hld_l2
        let lv1 := s.core.lvl[v1.toNat / 2]'hl1
        let lv2 := s.core.lvl[v2.toNat / 2]'hl2
        let sc0 : FullScratch := { s.scratch with wsort := s.scratch.wsort }
        let Pj261 : Tup Val [] → Mem 64 → Prop := fun _ m' =>
          ∃ st' tmp', st'.core = { s.core with tmp := tmp' } ∧ st'.scratch = sc0 ∧
            tmp'.length = c.max_vars ∧
            (m7Slice tmp' 1 s.core.tmp_len).Perm (m7Slice s.core.tmp 1 s.core.tmp_len) ∧
            tmp'[0]? = s.core.tmp[0]? ∧
            (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
              Full.fullTmpLe s.core.lvl s.core.trail_pos
                (tmp'[i]?.getD 0#32) (tmp'[j]?.getD 0#32)) ∧
            (FullMem c st' ⋆ R) m'
        refine wp_join_group Pj261 ?_ ?_
        · intro J261 _ m' ⟨st', tmp', hc', hs', hlen', hperm', h0', hsort', hm'⟩
          rw [Blocks.get_here]
          m7_lets
          exact m7_finish_spec hlenOk htl hc' hs' hlen' hws_len (fun _ => rfl) hperm'
            (fun _ => h0') hsort' hm' hQ
        · intro J261 hExit261
          let Pj262 : Tup Val [] → Mem 64 → Prop := fun _ m' =>
            m' = m ∧ Full.fullTmpLe s.core.lvl s.core.trail_pos v2 v1
          refine wp_join_group Pj262 ?_ ?_
          · intro J262 _ m' ⟨hm_eq, hle21⟩
            subst hm_eq
            rw [Blocks.get_here]
            m7_lets
            rw [hs1]
            obtain ⟨st1, hc1, hs1', hok1, hm1_raw⟩ := m7_store_tmp_nat (i := 1) v2 hc0 hs0 h1t
              (by decide) hm0
            m7_st m1, hm1 := And.intro hok1 hm1_raw
            m7_lets
            rw [hs2]
            have h2t' : 2 < (s.core.tmp.set 1 v2).length := by simp [h2t]
            obtain ⟨st2, hc2, hs2', hok2, hm2_raw⟩ := m7_store_tmp_nat (i := 2) v1 hc1 hs1' h2t'
              (by decide) hm1
            m7_st m2, hm2 := And.intro hok2 hm2_raw
            let tmp' := (s.core.tmp.set 1 v2).set 2 v1
            have hsw := m7_swap12_perm h1t h2t (by rw [htmp_len]; omega)
            have h12_get : tmp'[1]?.getD 0#32 = v2 := by
              dsimp [tmp']; simp [h1t]
            have h21_get : tmp'[2]?.getD 0#32 = v1 := by
              dsimp [tmp']; simp [h2t]
            exact hExit261 () m2 ⟨st2, tmp', hc2, hs2', by simp [tmp', htmp_len],
              by simpa [hN3, tmp', v1, v2] using hsw,
              by dsimp [tmp']; simp,
              fun i j hi hij hj => m7_three_sorted_step (by rw [h12_get, h21_get]; exact hle21)
                i j hi hij (hN3 ▸ hj), hm2⟩
          · intro J262 hExit262
            m7_lets
            m7_jnz
            refine ⟨fun hgt_lv => ?_, fun hle_lv => ?_⟩
            ·
              have hlt : lv2.toNat < lv1.toNat := m7_ult32_true hgt_lv
              exact hExit262 () m ⟨rfl, m7_fullTmpLe_of_lt hl2 hl1 hlt⟩
            ·
              have hle : lv1.toNat ≤ lv2.toNat := m7_ult32_false hle_lv
              m7_lets
              m7_jnz
              refine ⟨fun heq_lv => ?_, fun hne_lv => ?_⟩
              ·
                have heq' : lv1.toNat = lv2.toNat :=
                  congrArg BitVec.toNat (beq_iff_eq.mp heq_lv)
                have ht1 : v1.toNat / 2 < s.core.trail_pos.length := by rw [htpos_len]; omega
                have ht2 : v2.toNat / 2 < s.core.trail_pos.length := by rw [htpos_len]; omega
                have hld_t1 := m7_load_tpos_nat hc0 ht1 (by omega) hm0
                m7_ld hld_t1
                m7_lets
                have hld_t2 := m7_load_tpos_nat hc0 ht2 (by omega) hm0
                m7_ld hld_t2
                let tp1 := s.core.trail_pos[v1.toNat / 2]'ht1
                let tp2 := s.core.trail_pos[v2.toNat / 2]'ht2
                m7_lets
                m7_jnz
                refine ⟨fun hgt_tp => ?_, fun hle_tp => ?_⟩
                ·
                  have hlt_tp : tp2.toNat < tp1.toNat := m7_ult32_true hgt_tp
                  exact hExit262 () m ⟨rfl,
                    m7_fullTmpLe_of_eq_lvl_tpos hl2 hl1 ht2 ht1 heq'.symm (Nat.le_of_lt hlt_tp)⟩
                ·
                  have hle_tp' : tp1.toNat ≤ tp2.toNat := m7_ult32_false hle_tp
                  have h12 : Full.fullTmpLe s.core.lvl s.core.trail_pos
                      (s.core.tmp[1]?.getD 0#32) (s.core.tmp[2]?.getD 0#32) := by
                    rw [List.getElem?_eq_getElem (l := s.core.tmp) (i := 1) h1t,
                      List.getElem?_eq_getElem (l := s.core.tmp) (i := 2) h2t,
                      Option.getD_some, Option.getD_some]
                    exact m7_fullTmpLe_of_eq_lvl_tpos hl1 hl2 ht1 ht2 heq' hle_tp'
                  exact hExit261 () m ⟨st0, s.core.tmp, hc0, hs0, htmp_len, List.Perm.refl _, rfl,
                    fun i j hi hij hj => m7_three_sorted_step h12 i j hi hij (hN3 ▸ hj), hm0⟩
              ·
                have hne : lv1 ≠ lv2 := by simpa [bne_iff_ne] using hne_lv
                have hlt : lv1.toNat < lv2.toNat := by
                  have hne_nat : lv1.toNat ≠ lv2.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
                  omega
                have h12 : Full.fullTmpLe s.core.lvl s.core.trail_pos
                    (s.core.tmp[1]?.getD 0#32) (s.core.tmp[2]?.getD 0#32) := by
                  rw [List.getElem?_eq_getElem (l := s.core.tmp) (i := 1) h1t,
                    List.getElem?_eq_getElem (l := s.core.tmp) (i := 2) h2t,
                    Option.getD_some, Option.getD_some]
                  exact m7_fullTmpLe_of_lt hl1 hl2 hlt
                exact hExit261 () m ⟨st0, s.core.tmp, hc0, hs0, htmp_len, List.Perm.refl _, rfl,
                  fun i j hi hij hj => m7_three_sorted_step h12 i j hi hij (hN3 ▸ hj), hm0⟩
      · m7_lets
        m7_jnz
        refine ⟨fun _ => ?_, fun hgt16_b => ?_⟩
        · obtain ⟨st0, hc0, hs0, hm0⟩ := m7_wrap_state hm
          change wp Γ Q X
            (m7SortInsExpr (BitVec.ofNat 64 s.core.tmp_len) c.pTmp c.pLevel c.pTrailPos) m
          exact m7_sort_ins_wp htmp_len hlvl_len htpos_len htl (by omega) hbd hc0 hs0 hm0
            fun st' tmp' m' hc' hs' hlen' hperm' h0' _ hsort' hm' =>
              m7_finish_spec hlenOk htl hc' hs' hlen' hws_len (fun _ => rfl) hperm'
                (fun _ => h0') hsort' hm' hQ
        · have hNgt16 : 16 < s.core.tmp_len := by
            have h := m7_ule64_false hgt16_b
            simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN64] using h
          m7_lets
          m7_ld (load_full_wsort_ptr hm)
          m7_lets
          have hs1 : BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 := by decide
          rw [hs1]
          have h1t : 1 < s.core.tmp.length := by rw [htmp_len]; omega
          have h1w : 1 < s.scratch.wsort.length := by rw [hws_len]; omega
          have hbd1 := hbd 1 (le_refl 1) (by omega)
          rw [List.getElem?_eq_getElem (l := s.core.tmp) (i := 1) h1t, Option.getD_some] at hbd1
          obtain ⟨st0, hc0, hs0, hm0⟩ := m7_wrap_state hm
          have hld_v284 := m7_load_tmp_nat hc0 h1t (by decide) hm0
          m7_ld hld_v284
          m7_lets
          obtain ⟨st1, hc1, hs1', hok1, hm1_raw⟩ := m7_store_wsort_nat (i := 1)
            (s.core.tmp[1]'h1t) hc0 hs0 h1w (by decide) hm0
          m7_st m1, hm1 := And.intro hok1 hm1_raw
          m7_lets
          let v284 := s.core.tmp[1]'h1t
          have hv284_bd : v284.toNat < 2 * c.max_vars := hbd1
          rw [m7_var_idx64 v284]
          have hv284_lvl : v284.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
          have hld_v293 := m7_load_lvl_nat hc1 hv284_lvl (by omega) hm1
          m7_ld hld_v293
          let v293 := s.core.lvl[v284.toNat / 2]'hv284_lvl
          let InvCopy : Nat → Tup Val [i32, i32, i64] → Mem 64 → Prop := fun meas xs m_c =>
            ∃ k st ws_k, xs.1.toNat ≤ xs.2.1.toNat ∧
              xs.2.2.1 = BitVec.ofNat 64 k ∧ 2 ≤ k ∧ k ≤ s.core.tmp_len ∧
              meas = s.core.tmp_len - k ∧
              st.core = { s.core with tmp := s.core.tmp } ∧
              st.scratch = { s.scratch with wsort := ws_k } ∧
              ws_k.length = 2 * c.max_vars ∧
              m7Slice ws_k 1 k = m7Slice s.core.tmp 1 k ∧
              (∀ p, 1 ≤ p → p < k →
                xs.1.toNat ≤ (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
                (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ xs.2.1.toNat) ∧
              (FullMem c st ⋆ R) m_c
          refine wp_loop_group InvCopy ?_ ?_
          · intro J294 meas xs m_c hIH ⟨k, st_c, ws_k, hmn_mx, hxs3, hk2, hkN, hmeas, hst_c,
              hst_s, hlen_wk, hsl_wk, hminmax_k, hm_c⟩
            rw [Blocks.get_here]
            m7_lets
            m7_jnz
            refine ⟨fun hlt_b => ?_, fun hge_b => ?_⟩
            · have hk_lt : k < s.core.tmp_len := by
                have h := m7_ult64_true hlt_b
                rw [hxs3, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
                rwa [Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
              have hkt : k < s.core.tmp.length := by rw [htmp_len]; omega
              have hbdk := hbd k (by omega) hk_lt
              rw [List.getElem?_eq_getElem (l := s.core.tmp) (i := k) hkt, Option.getD_some]
                at hbdk
              m7_lets
              rw [hxs3]
              have hld_v300 := m7_load_tmp_nat hst_c hkt (by omega) hm_c
              m7_ld hld_v300
              m7_lets
              have hkw : k < ws_k.length := by rw [hlen_wk]; omega
              obtain ⟨st_c', hst_c', hst_s', hok_c, hm_c0⟩ := m7_store_wsort_nat (i := k)
                (s.core.tmp[k]'hkt) hst_c hst_s hkw (by omega) hm_c
              m7_st m_c1, hm_c' := And.intro hok_c hm_c0
              m7_lets
              let v300 := s.core.tmp[k]'hkt
              have hv300_bd : v300.toNat < 2 * c.max_vars := hbdk
              rw [m7_var_idx64 v300]
              have hv300_lvl : v300.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
              have hld_v308 := m7_load_lvl_nat hst_c' hv300_lvl (by omega) hm_c'
              m7_ld hld_v308
              let v308 := s.core.lvl[v300.toNat / 2]'hv300_lvl
              let Pj309 : Tup Val [i32] → Mem 64 → Prop := fun mn m309 =>
                m309 = m_c1 ∧
                mn.1.toNat ≤ v308.toNat ∧
                (∀ p, 1 ≤ p → p < k →
                  mn.1.toNat ≤ (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
                mn.1.toNat ≤ xs.2.1.toNat
              refine wp_join_group Pj309 ?_ ?_
              · intro J309 mn m309 ⟨hm_eq, hmn_lx, hmn_pre, hmn_mx'⟩
                subst hm_eq
                rw [Blocks.get_here]
                let Pj311 : Tup Val [i32] → Mem 64 → Prop := fun mx m311 =>
                  m311 = m309 ∧
                  v308.toNat ≤ mx.1.toNat ∧
                  (∀ p, 1 ≤ p → p < k →
                    (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ mx.1.toNat) ∧
                  mn.1.toNat ≤ mx.1.toNat
                refine wp_join_group Pj311 ?_ ?_
                · intro J311 mx m311 ⟨hm_eq2, hlx_mx, hmx_pre, hmn_mx''⟩
                  subst hm_eq2
                  rw [Blocks.get_here]
                  m7_lets
                  have hstep := m7_copy_step_inv htmp_len hlvl_len hlen_wk hk2 hk_lt htl
                    hsl_wk (by rw [List.getElem?_eq_getElem (l := s.core.tmp) (i := k) hkt,
                      Option.getD_some]; exact hbdk) rfl hmn_lx hlx_mx hmn_pre hmx_pre
                  have hk1_bv : BitVec.ofNat 64 k + (1 : BitVec 64) = BitVec.ofNat 64 (k + 1) :=
                    m7_add1_bv64 (by omega)
                  rw [hk1_bv]
                  refine hIH (s.core.tmp_len - (k + 1)) (mn.1, mx.1, BitVec.ofNat 64 (k + 1), ())
                    _ (by omega) ⟨k + 1, st_c', ws_k.set k v300, hmn_mx'', rfl, by omega,
                      by omega, rfl, hst_c', hst_s', hstep.1, hstep.2.1, hstep.2.2, hm_c'⟩
                · intro J311 hExit311
                  m7_lets
                  m7_jnz
                  refine ⟨fun hgt_mx => ?_, fun hle_mx => ?_⟩
                  ·
                    have hlt_mx : xs.2.1.toNat < v308.toNat := m7_ult32_true hgt_mx
                    exact hExit311 (v308, ()) _ ⟨rfl, le_refl _, fun p hp1 hp2 =>
                      Nat.le_trans (hminmax_k p hp1 hp2).2 (Nat.le_of_lt hlt_mx),
                      Nat.le_trans hmn_mx' (Nat.le_of_lt hlt_mx)⟩
                  ·
                    have hle_mx' : v308.toNat ≤ xs.2.1.toNat := m7_ult32_false hle_mx
                    exact hExit311 (xs.2.1, ()) _ ⟨rfl, hle_mx', fun p hp1 hp2 =>
                      (hminmax_k p hp1 hp2).2, hmn_mx'⟩
              · intro J309 hExit309
                m7_lets
                m7_jnz
                refine ⟨fun hlt_mn => ?_, fun hge_mn => ?_⟩
                ·
                  have hlt_mn' : v308.toNat < xs.1.toNat := m7_ult32_true hlt_mn
                  exact hExit309 (v308, ()) _ ⟨rfl, le_refl _, fun p hp1 hp2 =>
                    Nat.le_trans (Nat.le_of_lt hlt_mn') (hminmax_k p hp1 hp2).1,
                    Nat.le_trans (Nat.le_of_lt hlt_mn') hmn_mx⟩
                ·
                  have hge_mn' : xs.1.toNat ≤ v308.toNat := m7_ult32_false hge_mn
                  exact hExit309 (xs.1, ()) _ ⟨rfl, hge_mn', fun p hp1 hp2 =>
                    (hminmax_k p hp1 hp2).1, hmn_mx⟩
            · have hk_ge : s.core.tmp_len ≤ k := by
                have h := m7_ult64_false hge_b
                rw [hxs3, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
                rwa [Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
              have hk_eq : k = s.core.tmp_len := by omega
              subst hk_eq
              m7_lets
              have hmv60 : c.max_vars < 2 ^ 60 := by
                have := c.hmaxv; unfold dimacsBound at this; omega
              have hspan_bv :
                  (BitVec.setWidth 64 xs.2.1 - BitVec.setWidth 64 xs.1) + (1 : BitVec 64) =
                  BitVec.ofNat 64 (xs.2.1.toNat - xs.1.toNat + 1) := by
                rw [m7_sub_zext64_of_le hmn_mx]
                exact m7_add1_bv64 (by
                  have h32 := xs.2.1.isLt
                  change xs.2.1.toNat - xs.1.toNat + 1 < 2 ^ 64; omega)
              rw [hspan_bv]
              let span := xs.2.1.toNat - xs.1.toNat + 1
              have hN1_bv : BitVec.ofNat 64 s.core.tmp_len - (1 : BitVec 64) =
                  BitVec.ofNat 64 (s.core.tmp_len - 1) :=
                m7_sub1_bv64 (by omega) hN64
              rw [hN1_bv]
              have hs1_se : (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64 = 1 := by decide
              have h2mv_toNat : (BitVec.ofNat 64 c.max_vars <<<
                  ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat = 2 * c.max_vars := by
                rw [hs1_se, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmv64,
                  Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]; omega
              have hs2_se : (BitVec.signExtend 64 (2 : BitVec 32)).toNat % 64 = 2 := by decide
              have h4N1_toNat : (BitVec.ofNat 64 (s.core.tmp_len - 1) <<<
                  ((BitVec.signExtend 64 (2 : BitVec 32)).toNat % 64)).toNat =
                    4 * (s.core.tmp_len - 1) := by
                rw [hs2_se, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
                  Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
              let Pj323 : Tup Val [] → Mem 64 → Prop := fun _ m323 => m323 = m_c
              refine wp_join_group Pj323 ?_ ?_
              · intro J323 _ m323 hm_eq323
                rw [hm_eq323, Blocks.get_here]
                m7_lets
                obtain ⟨F, hF, hrec⟩ := m7FullMem_focus_heap hm_c
                rw [m7_core_tmp_eq hst_c] at hF
                rw [m7_core_lvl_eq hst_c, m7_core_tpos_eq hst_c] at hF hrec
                refine wp_call_of_spec _ _ ?_
                dsimp only [LeanQbe.T.vals, Arg.val]
                refine hHeap _ m_c _ _ (m7SortTmpHeapSpec_of ?_ ?_ ?_ hF ?_)
                · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN64, htmp_len]; exact htl
                · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN64]; omega
                · intro p hp1 hp_lt
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN64] at hp_lt
                  have hbp := hbd p hp1 hp_lt
                  rw [hlvl_len, htpos_len]; omega
                · intro tmp' m' hlen' htake' h0' _ _ hsort' hm'
                  have hsub := hrec tmp' m' hm'
                  obtain ⟨st', hc', hs', hm_st'⟩ := m7_wrap_upd_tmp hst_c hst_s hsub
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN64] at htake' h0' hsort'
                  have hperm' : (m7Slice tmp' 1 s.core.tmp_len).Perm
                      (m7Slice s.core.tmp 1 s.core.tmp_len) :=
                    m7Slice_perm_of_take (h0' (by omega)) htake'
                      (by omega) (by rw [hlen', htmp_len]; exact htl)
                      (by rw [htmp_len]; exact htl)
                  exact m7_finish_spec hlenOk htl hc' hs' (by rw [hlen', htmp_len])
                    hlen_wk (fun h => by omega) hperm' h0' hsort' hm_st' hQ
              · intro J323 hExit323
                m7_lets
                m7_jnz
                refine ⟨fun _ => ?_, fun hne1_b => ?_⟩
                · exact hExit323 () m_c rfl
                · m7_lets
                  m7_jnz
                  refine ⟨fun _ => ?_, fun hle_mv_b => ?_⟩
                  · exact hExit323 () m_c rfl
                  · have hspan_le_mv : span ≤ c.max_vars := by
                      have h := m7_ult64_false hle_mv_b
                      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmv64] at h
                      rw [Nat.mod_eq_of_lt (by have := xs.2.1.isLt; omega)] at h
                      exact (by dsimp [span]; omega)
                    m7_lets
                    m7_jnz
                    refine ⟨fun _ => ?_, fun hle_4N_b => ?_⟩
                    · exact hExit323 () m_c rfl
                    · m7_lets
                      change wp Γ Q X (m7SortZeroExpr (BitVec.ofNat 64 c.max_vars)
                        (BitVec.ofNat 64 span) c.pWsort
                        (m7SortHistExpr (BitVec.ofNat 64 c.max_vars)
                          (BitVec.ofNat 64 s.core.tmp_len) c.pLevel c.pWsort xs.1
                          (m7SortPrefExpr (BitVec.ofNat 64 c.max_vars) (BitVec.ofNat 64 span)
                            c.pWsort
                            (m7SortScatExpr (BitVec.ofNat 64 c.max_vars)
                              (BitVec.ofNat 64 s.core.tmp_len) c.pTmp c.pLevel c.pWsort xs.1
                              (m7SortRunsExpr (BitVec.ofNat 64 s.core.tmp_len) c.pTmp c.pLevel
                                c.pTrailPos))))) m_c
                      have hminmax_ws : ∀ p, 1 ≤ p → p < s.core.tmp_len →
                          xs.1.toNat ≤
                            (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
                          (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
                            xs.1.toNat + span := by
                        intro p hp1 hp2
                        have h := hminmax_k p hp1 hp2
                        exact ⟨h.1, by dsimp [span]; omega⟩
                      have hbd_ws : ∀ p, 1 ≤ p → p < s.core.tmp_len →
                          (ws_k[p]?.getD 0#32).toNat < 2 * c.max_vars := by
                        intro p hp1 hp2
                        have h1 : ws_k[p]? = s.core.tmp[p]? := by
                          have hw : p < ws_k.length := by rw [hlen_wk]; omega
                          have ht : p < s.core.tmp.length := by rw [htmp_len]; omega
                          rw [List.getElem?_eq_getElem (l := ws_k) (i := p) hw,
                            List.getElem?_eq_getElem (l := s.core.tmp) (i := p) ht]
                          congr 1
                          have hs := congrArg (fun l => l[p - 1]?) hsl_wk
                          rw [List.getElem?_eq_getElem (by rw [m7Slice_length, hlen_wk]; omega),
                            List.getElem?_eq_getElem (by rw [m7Slice_length, htmp_len]; omega),
                            m7Slice_getElem, m7Slice_getElem] at hs
                          simp only [Option.some.injEq] at hs
                          simpa [show 1 + (p - 1) = p by omega] using hs
                        rw [h1]; exact hbd p hp1 hp2
                      let tot := m7BktCnt s.core.lvl xs.1.toNat (m7Slice ws_k 1 s.core.tmp_len)
                      have hspos_N : m7PrefixStart tot span = s.core.tmp_len := by
                        rw [m7PrefixStart_eq_sum]
                        have hsum := m7BktCnt_sum_range s.core.lvl xs.1.toNat
                          (m7Slice ws_k 1 s.core.tmp_len) span (fun y hy => by
                            rw [List.mem_iff_getElem] at hy
                            obtain ⟨idx, hidx, rfl⟩ := hy
                            rw [m7Slice_length, hlen_wk] at hidx
                            rw [m7Slice_getElem, m7Bkt_eq]
                            have hmm := hminmax_ws (1 + idx) (by omega) (by omega)
                            rw [List.getElem?_eq_getElem (l := ws_k) (i := 1 + idx)
                              (by rw [hlen_wk]; omega), Option.getD_some] at hmm
                            omega)
                        rw [m7Slice_length, hlen_wk] at hsum
                        dsimp only [tot]; rw [hsum]; omega
                      have hspos_le : ∀ b ≤ span, m7PrefixStart tot b ≤ s.core.tmp_len :=
                        fun b hb => hspos_N ▸ m7PrefixStart_mono hb
                      refine m7_sort_zero_wp hspan_le_mv hst_c hst_s hlen_wk hm_c ?_
                      intro st1 ws1 m1 hst1_c hst1_s hlen_ws1 hpre1 hz1 hm1
                      have hsl1 :
                          m7Slice ws1 1 s.core.tmp_len = m7Slice s.core.tmp 1 s.core.tmp_len :=
                        (m7Slice_congr_lt (by omega) (by rw [hlen_ws1]; omega)
                          (by rw [hlen_wk]; omega) (fun q hq => hpre1 q (by omega))).trans hsl_wk
                      have hminmax1 : ∀ p, 1 ≤ p → p < s.core.tmp_len →
                          xs.1.toNat ≤
                            (s.core.lvl[(ws1[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
                          (s.core.lvl[(ws1[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
                            xs.1.toNat + span := fun p hp1 hp2 => by
                        rw [show ws1[p]? = ws_k[p]? from hpre1 p (by omega)]
                        exact hminmax_ws p hp1 hp2
                      have hbd1' : ∀ p, 1 ≤ p → p < s.core.tmp_len →
                          (ws1[p]?.getD 0#32).toNat < 2 * c.max_vars := fun p hp1 hp2 => by
                        rw [show ws1[p]? = ws_k[p]? from hpre1 p (by omega)]
                        exact hbd_ws p hp1 hp2
                      refine m7_sort_hist_wp hlvl_len htl (by omega) hlen_ws1 hspan_le_mv
                        hminmax1 hbd1' hz1 hst1_c hst1_s hm1 ?_
                      intro st2 ws2 m2 hst2_c hst2_s hlen_ws2 hpre2 hcnt2 hm2
                      have hpre20 : ∀ q < c.max_vars, ws2[q]? = ws_k[q]? :=
                        fun q hq => (hpre2 q hq).trans (hpre1 q hq)
                      have hsl1_k : m7Slice ws1 1 s.core.tmp_len = m7Slice ws_k 1 s.core.tmp_len :=
                        m7Slice_congr_lt (by omega) (by rw [hlen_ws1]; omega)
                          (by rw [hlen_wk]; omega) (fun q hq => hpre1 q (by omega))
                      refine m7_sort_pref_wp hlen_ws2 hspan_le_mv (by rw [hspos_N]; exact htl)
                        (fun b hb => by rw [hcnt2 b hb, hsl1_k])
                        hst2_c hst2_s hm2 ?_
                      intro st3 ws3 m3 hst3_c hst3_s hlen_ws3 hpre3 hpref3 hm3
                      have hpre3k : ∀ q < c.max_vars, ws3[q]? = ws_k[q]? :=
                        fun q hq => (hpre3 q hq).trans (hpre20 q hq)
                      have hsl3 : m7Slice ws3 1 s.core.tmp_len = m7Slice ws_k 1 s.core.tmp_len :=
                        m7Slice_congr_lt (by omega) (by rw [hlen_ws3]; omega)
                          (by rw [hlen_wk]; omega) (fun q hq => hpre3k q (by omega))
                      have hminmax3 : ∀ p, 1 ≤ p → p < s.core.tmp_len →
                          xs.1.toNat ≤
                            (s.core.lvl[(ws3[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
                          (s.core.lvl[(ws3[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
                            xs.1.toNat + span := fun p hp1 hp2 => by
                        rw [show ws3[p]? = ws_k[p]? from hpre3k p (by omega)]
                        exact hminmax_ws p hp1 hp2
                      have hbd3 : ∀ p, 1 ≤ p → p < s.core.tmp_len →
                          (ws3[p]?.getD 0#32).toNat < 2 * c.max_vars := fun p hp1 hp2 => by
                        rw [show ws3[p]? = ws_k[p]? from hpre3k p (by omega)]
                        exact hbd_ws p hp1 hp2
                      refine m7_sort_scat_wp htmp_len hlvl_len htl (by omega) hlen_ws3 hspan_le_mv
                        (hsl3.trans hsl_wk) hminmax3 hbd3 (by rw [hsl3]; exact hspos_N)
                        (fun b hb => by rw [hsl3]; exact hspos_le b hb)
                        (fun b hb => by rw [hsl3]; exact hpref3 b hb) hst3_c hst3_s hm3 ?_
                      intro st4 tmp4 ws4 m4 hst4_c hst4_s hlen_t4 hlen_ws4 hperm4 h0_4 hout_4
                        hlvl4 hm4
                      refine m7_sort_runs_wp hHeap htmp_len hlvl_len htpos_len htl (by omega) hbd
                        hst4_c hst4_s hlen_t4 hperm4 h0_4 hout_4 hlvl4 hm4 ?_
                      intro st5 tmp5 m5 hst5_c hst5_s hlen_t5 hperm5 h0_5 _ hsort5 hm5
                      exact m7_finish_spec hlenOk htl hst5_c hst5_s hlen_t5 hlen_ws4
                        (fun h => by omega) hperm5 (fun _ => h0_5) hsort5 hm5 hQ
          · intro J295 hExit295
            have hinv0 := m7_copy_init_inv htmp_len hlvl_len hws_len (by omega) htl
              (hbd 1 (le_refl 1) (by omega))
            apply hExit295 (s.core.tmp_len - 2) (v293, v293, BitVec.ofNat 64 2, ()) m1
            refine ⟨2, st1, s.scratch.wsort.set 1 v284, le_refl _, rfl, le_refl 2,
              by omega, rfl, hc1, hs1', hinv0.1, hinv0.2.1, hinv0.2.2, hm1⟩

end LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
