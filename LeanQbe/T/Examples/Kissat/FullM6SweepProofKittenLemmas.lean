module

public import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec

/-!
# Kissat `D-Full` M6 — Scaled `K6` Core Preservation Lemmas & Leaf `Func.wp` Proofs (`5/39`)

1. Scoped pointer-base normalization tactics (`K6PtrTactics`), pure bitvector/list helpers,
   semantic entailment (`SemEntails`), and trail refutation lemmas (`k6_conflict_unsat_lvl0`,
   `k6_conflict_unsat_assumps`, `k6_falsified_assump_unsat`).
2. `K6WatchesOk` (including exact inline binary `K6_BIN_FLAG` invariant), `k6AssignStep`,
   `k6SetIncons`, `K6BtLoopInv`, `k6Init_finish_inv`, and `k6AddClause_ge2_preserves`.
3. Parametric `(Γ : Env)` `Func.wp` proofs for `5/39` owned functions:
   - `full_m6_max_v_wp`, `full_k6_add_ticks_wp`, `full_k6_watch_wp`, `full_k6_assign_wp`,
     `full_k6_mtf_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open Kraken.Bedrock2.Test

open K6MemATactics
open scoped K6MemATactics

/-! ## 1. Pointer Normalization Tactics & Pure Helpers -/

namespace K6PtrTactics

@[scoped bv_c0] theorem k6_bv32_zero : (0 : BitVec 32) = 0#32 := rfl
@[scoped bv_c0] theorem k6_bv32_one : (1 : BitVec 32) = 1#32 := rfl
@[scoped bv_c0] theorem k6_bv32_two : (2 : BitVec 32) = 2#32 := rfl

@[scoped bv_c0] theorem k6_shl1_toNat (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem k6_mv32_toNat (L : K6Layout) : L.mv32.toNat = L.maxV := by
  have hm := L.hmaxV; unfold K6Layout.mv32
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

@[scoped bv_c0] theorem k6_ptr_base (L : K6Layout) (pScr : BitVec 64) :
    pScr + ((1280 : BitVec 32) + (L.mv32 <<< (1 : Nat))).setWidth 64 * 4 = L.kPtr pScr :=
  k6_ptr_base_k6Base L pScr

@[scoped bv_c0] theorem k6_ptr_base_bv (L : K6Layout) (pScr : BitVec 64) :
    pScr + ((1280 : BitVec 32) + (L.mv32 <<< 1#32)).setWidth 64 * 4 = L.kPtr pScr := by
  rw [show L.mv32 <<< 1#32 = L.mv32 <<< (1 : Nat) from rfl]
  exact k6_ptr_base_k6Base L pScr

@[scoped bv_c0] theorem k6_ptr_lvl_sw (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + (32 : BitVec 32).setWidth 64 * 4 = kPtr + BitVec.ofNat 64 (4 * L.oLvl) :=
  k6_ptr_lvl L kPtr

@[scoped bv_c0] theorem k6_ptr_lvl_64 (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + 32#64 * 4 = kPtr + BitVec.ofNat 64 (4 * L.oLvl) :=
  k6_ptr_lvl L kPtr

@[scoped bv_c0] theorem k6_ptr_rsn (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + L.mv32).setWidth 64 * 4 = kPtr + BitVec.ofNat 64 (4 * L.oRsn) :=
  k6_ptr_add_1 L kPtr

@[scoped bv_c0] theorem k6_ptr_qprev (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (2 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oQPrev) :=
  k6_ptr_add_mul L kPtr 2 (by decide)

@[scoped bv_c0] theorem k6_ptr_qnext (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (3 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oQNext) :=
  k6_ptr_add_mul L kPtr 3 (by decide)

@[scoped bv_c0] theorem k6_ptr_qstampArr (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (4 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oQStamp) :=
  k6_ptr_add_mul L kPtr 4 (by decide)

@[scoped bv_c0] theorem k6_ptr_trl (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (5 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oTrl) :=
  k6_ptr_add_mul L kPtr 5 (by decide)

@[scoped bv_c0] theorem k6_ptr_flags (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (6 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oFlags) :=
  k6_ptr_add_mul L kPtr 6 (by decide)

@[scoped bv_c0] theorem k6_ptr_ana (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (7 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oAna) :=
  k6_ptr_add_mul L kPtr 7 (by decide)

@[scoped bv_c0] theorem k6_ptr_kl (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (8 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oKl) :=
  k6_ptr_add_mul L kPtr 8 (by decide)

@[scoped bv_c0] theorem k6_ptr_assump (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (9 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oAssump) :=
  k6_ptr_add_mul L kPtr 9 (by decide)

@[scoped bv_c0] theorem k6_ptr_vals (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (10 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oVals) :=
  k6_ptr_add_mul L kPtr 10 (by decide)

@[scoped bv_c0] theorem k6_ptr_whead (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (12 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oWHead) :=
  k6_ptr_add_mul L kPtr 12 (by decide)

@[scoped bv_c0] theorem k6_ptr_wnext (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (14 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oWNext) :=
  k6_ptr_add_mul L kPtr 14 (by decide)

@[scoped bv_c0] theorem k6_ptr_wblit (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (22 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oWBlit) :=
  k6_ptr_add_mul L kPtr 22 (by decide)

@[scoped bv_c0] theorem k6_ptr_clOff (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (30 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oClOff) :=
  k6_ptr_add_mul L kPtr 30 (by decide)

@[scoped bv_c0] theorem k6_ptr_clSz (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (34 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oClSz) :=
  k6_ptr_add_mul L kPtr 34 (by decide)

@[scoped bv_c0] theorem k6_ptr_arena (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (38 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oArena) :=
  k6_ptr_add_mul L kPtr 38 (by decide)

section DynArrMem
variable {L : K6Layout} {kPtr : BitVec 64} {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64}

@[scoped c0_load] theorem load_k6_lvlArr_dyn {i : BitVec 32} (hi : i.toNat < szV L)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 ((kPtr + 32#64 * 4) + i.setWidth 64 * 4) =
      some (ks.lvlArr[i.toNat]?.getD 0#32) := by
  rw [k6_ptr_lvl_64 L kPtr]; exact load_k6_lvlArr hi hm

@[scoped c0_store] theorem store_k6_lvlArr_dyn (v : BitVec 32) {i : BitVec 32}
    (hi : i.toNat < szV L) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + 32#64 * 4) + i.setWidth 64 * 4) ∧
      (K6MemA L kPtr (ks.putArr .lvlArr i.toNat v) ⋆ R)
        (storeMem m i32 ((kPtr + 32#64 * 4) + i.setWidth 64 * 4) v) := by
  rw [k6_ptr_lvl_64 L kPtr]; exact store_k6_lvlArr v hi hm

@[scoped c0_load] theorem load_k6_lvlArr_sw {i : BitVec 32} (hi : i.toNat < szV L)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 ((kPtr + (32 : BitVec 32).setWidth 64 * 4) + i.setWidth 64 * 4) =
      some (ks.lvlArr[i.toNat]?.getD 0#32) := by
  rw [k6_ptr_lvl_sw L kPtr]; exact load_k6_lvlArr hi hm

@[scoped c0_store] theorem store_k6_lvlArr_sw (v : BitVec 32) {i : BitVec 32}
    (hi : i.toNat < szV L) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + (32 : BitVec 32).setWidth 64 * 4) + i.setWidth 64 * 4) ∧
      (K6MemA L kPtr (ks.putArr .lvlArr i.toNat v) ⋆ R)
        (storeMem m i32 ((kPtr + (32 : BitVec 32).setWidth 64 * 4) + i.setWidth 64 * 4) v) := by
  rw [k6_ptr_lvl_sw L kPtr]; exact store_k6_lvlArr v hi hm

@[scoped c0_load] theorem load_k6_rsn_dyn {i : BitVec 32} (hi : i.toNat < szV L)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 ((kPtr + ((32 : BitVec 32) + L.mv32).setWidth 64 * 4) + i.setWidth 64 * 4) =
      some (ks.rsn[i.toNat]?.getD 0#32) := by
  rw [k6_ptr_rsn L kPtr]; exact load_k6_rsn hi hm

@[scoped c0_store] theorem store_k6_rsn_dyn (v : BitVec 32) {i : BitVec 32}
    (hi : i.toNat < szV L) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + ((32 : BitVec 32) + L.mv32).setWidth 64 * 4) + i.setWidth 64 * 4) ∧
      (K6MemA L kPtr (ks.putArr .rsn i.toNat v) ⋆ R)
        (storeMem m i32
          ((kPtr + ((32 : BitVec 32) + L.mv32).setWidth 64 * 4) + i.setWidth 64 * 4) v) := by
  rw [k6_ptr_rsn L kPtr]; exact store_k6_rsn v hi hm

end DynArrMem

local syntax "def_k6_dyn_arr " ident num ident ident : command
local macro_rules
  | `(def_k6_dyn_arr $fld $c $szfn $plem) => do
    let dlnm := Lean.mkIdent (Lean.Name.mkSimple s!"load_k6_{fld.getId}_dyn")
    let dsnm := Lean.mkIdent (Lean.Name.mkSimple s!"store_k6_{fld.getId}_dyn")
    let lbase := Lean.mkIdent (Lean.Name.mkSimple s!"load_k6_{fld.getId}")
    let sbase := Lean.mkIdent (Lean.Name.mkSimple s!"store_k6_{fld.getId}")
    let tag := Lean.mkIdent (`K6ArrField ++ fld.getId)
    let ii := Lean.mkIdent (Lean.Name.mkSimple "i")
    `(
      @[scoped c0_load] theorem $dlnm {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
          {R : Mem 64 → Prop} {m : Mem 64} {$ii : BitVec 32} (hi : ($ii).toNat < ($szfn L))
          (hm : (K6MemA L kPtr ks ⋆ R) m) :
          loadVal m i32
            ((kPtr + ((32 : BitVec 32) + ($c : BitVec 32) * L.mv32).setWidth 64 * 4) +
              ($ii).setWidth 64 * 4) =
            some ((ks.$fld)[($ii).toNat]?.getD 0#32) := by
        rw [$plem L kPtr]; exact $lbase hi hm
      @[scoped c0_store] theorem $dsnm {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
          {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {$ii : BitVec 32}
          (hi : ($ii).toNat < ($szfn L)) (hm : (K6MemA L kPtr ks ⋆ R) m) :
          storeOk m i32
            ((kPtr + ((32 : BitVec 32) + ($c : BitVec 32) * L.mv32).setWidth 64 * 4) +
              ($ii).setWidth 64 * 4) ∧
            (K6MemA L kPtr (ks.putArr $tag ($ii).toNat v) ⋆ R)
              (storeMem m i32
                ((kPtr + ((32 : BitVec 32) + ($c : BitVec 32) * L.mv32).setWidth 64 * 4) +
                  ($ii).setWidth 64 * 4) v) := by
        rw [$plem L kPtr]; exact $sbase v hi hm
    )

def_k6_dyn_arr qprev 2 szV k6_ptr_qprev
def_k6_dyn_arr qnext 3 szV k6_ptr_qnext
def_k6_dyn_arr qstampArr 4 szV k6_ptr_qstampArr
def_k6_dyn_arr trl 5 szV k6_ptr_trl
def_k6_dyn_arr flags 6 szV k6_ptr_flags
def_k6_dyn_arr ana 7 szV k6_ptr_ana
def_k6_dyn_arr kl 8 szV k6_ptr_kl
def_k6_dyn_arr assump 9 szV k6_ptr_assump
def_k6_dyn_arr vals 10 sz2V k6_ptr_vals
def_k6_dyn_arr whead 12 sz2V k6_ptr_whead
def_k6_dyn_arr wnext 14 sz2Cl k6_ptr_wnext
def_k6_dyn_arr wblit 22 sz2Cl k6_ptr_wblit
def_k6_dyn_arr clOff 30 szCl k6_ptr_clOff
def_k6_dyn_arr clSz 34 szCl k6_ptr_clSz
def_k6_dyn_arr arena 38 szAr k6_ptr_arena

end K6PtrTactics

open scoped K6PtrTactics

theorem k6_nat_xor1_cases (l : Nat) :
    (l = 2 * (l / 2) ∧ (l ^^^ 1) = 2 * (l / 2) + 1) ∨
    (l = 2 * (l / 2) + 1 ∧ (l ^^^ 1) = 2 * (l / 2)) := by
  have h := litNeg_eq l
  unfold litNeg at h
  rcases Nat.mod_two_eq_zero_or_one l with hm | hm
  · left; simp [hm] at h; omega
  · right; simp [hm] at h; omega

theorem k6_nat_xor1_xor1 (l : Nat) : (l ^^^ 1) ^^^ 1 = l := by
  rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases k6_nat_xor1_cases (l ^^^ 1) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

theorem k6_slab_drop_exact {α : Type _} (p s : List α) {k : Nat} (hk : p.length = k) :
    (p ++ s).drop k = s := by
  rw [List.drop_append_of_le_length (by omega), ← hk, List.drop_length, List.nil_append]

theorem k6_fullState_lengthsOk_scratch {c : FullCfg} {s : FullState} {scr' : List (BitVec 32)}
    (hlen : s.LengthsOk c) (hscr : scr'.length = c.scratch_cap) :
    ({ s with scratch := { s.scratch with scratch_buf := scr' } } : FullState).LengthsOk c :=
  ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscr }⟩

theorem k6_bv32_lt31_and_mask {x : BitVec 32} (hx : x.toNat < 2 ^ 31) :
    x &&& 0x7FFFFFFF#32 = x ∧ x &&& 0x80000000#32 = 0#32 := by
  constructor <;> apply BitVec.eq_of_getElem_eq <;> intro i hi
  · simp only [BitVec.getElem_and]
    by_cases h31 : i = 31
    · subst h31
      have hf : x[31] = false := by
        rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq,
          Nat.div_eq_of_lt hx]
        rfl
      simp [hf]
    · have ht : (0x7FFFFFFF#32 : BitVec 32)[i] = true := by revert i hi h31; decide
      simp [ht]
  · simp only [BitVec.getElem_and, BitVec.getElem_zero]
    by_cases h31 : i = 31
    · subst h31
      have hf : x[31] = false := by
        rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq,
          Nat.div_eq_of_lt hx]
        rfl
      simp [hf]
    · have hf : (0x80000000#32 : BitVec 32)[i] = false := by revert i hi h31; decide
      simp [hf]

theorem k6_bv32_or_bin_mask {x : BitVec 32} (hx : x.toNat < 2 ^ 31) :
    (x ||| 0x80000000#32) &&& 0x7FFFFFFF#32 = x ∧
      (x ||| 0x80000000#32) &&& 0x80000000#32 = 0x80000000#32 := by
  have hlt := k6_bv32_lt31_and_mask hx
  have h1 : (x ||| 0x80000000#32) &&& 0x7FFFFFFF#32 =
      (x &&& 0x7FFFFFFF#32) ||| (0x80000000#32 &&& 0x7FFFFFFF#32) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, Bool.and_or_distrib_right]
  have h2 : (x ||| 0x80000000#32) &&& 0x80000000#32 =
      (x &&& 0x80000000#32) ||| (0x80000000#32 &&& 0x80000000#32) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, Bool.and_or_distrib_right]
  rw [h1, hlt.1, show (0x80000000#32 &&& 0x7FFFFFFF#32 : BitVec 32) = 0#32 from by decide,
    BitVec.or_zero]
  rw [h2, hlt.2, BitVec.zero_or, BitVec.and_self]
  exact ⟨rfl, rfl⟩

theorem k6_list_nodup_getElem_inj {α : Type} {xs : List α} (hnd : xs.Nodup)
    {i j : Nat} (hi : i < xs.length) (hj : j < xs.length) (hij : xs[i] = xs[j]) : i = j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons x tl ih =>
    rcases List.nodup_cons.mp hnd with ⟨hnot, hnd_tl⟩
    cases i <;> cases j
    · rfl
    · exfalso; simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hij
      exact hnot (hij ▸ List.getElem_mem (by simp at hj; omega))
    · exfalso; simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hij
      exact hnot (hij ▸ List.getElem_mem (by simp at hi; omega))
    · simp only [List.getElem_cons_succ] at hij
      exact congrArg Nat.succ (ih hnd_tl (by simp at hi; omega) (by simp at hj; omega) hij)

theorem k6_nodup_subset_length {n : Nat} :
    ∀ {xs : List Nat}, xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n := by
  induction n with
  | zero =>
    intro xs _ hlt; cases xs with
    | nil => simp
    | cons x _ => exact absurd (hlt x List.mem_cons_self) (by omega)
  | succ k ih =>
    intro xs hnd hlt
    by_cases hmem : k ∈ xs
    · have hnd' := hnd.erase k
      have hlt' : ∀ x ∈ xs.erase k, x < k := fun x hx => by
        have hne : x ≠ k := fun h => by subst h; exact List.Nodup.not_mem_erase hnd hx
        have := hlt x (List.mem_of_mem_erase hx); omega
      have hle := ih hnd' hlt'
      have hlen := List.length_erase_of_mem hmem
      omega
    · have hle := ih hnd (fun x hx => by
        have := hlt x hx; have : x ≠ k := fun h => hmem (h ▸ hx); omega)
      omega

theorem k6_nodup_mem_of_length_ge {n : Nat} {xs : List Nat} (hnd : xs.Nodup)
    (hlt : ∀ x ∈ xs, x < n) (hlen : n ≤ xs.length) {v : Nat} (hv : v < n) : v ∈ xs := by
  by_cases hmem : v ∈ xs
  · exact hmem
  · exfalso
    have hle := k6_nodup_subset_length (List.nodup_cons.mpr ⟨hmem, hnd⟩) fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hv
      · exact hlt x hx'
    simp at hle; omega

private theorem k6_count_set_eq {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {i : Nat}
    (hi : i < xs.length) (v a : α) :
    (xs.set i v).count a + (if xs[i] == a then 1 else 0) =
      xs.count a + (if v == a then 1 else 0) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x tl ih =>
    cases i with
    | zero => simp [List.count_cons]; omega
    | succ i' =>
      simp only [List.set_cons_succ, List.count_cons, List.getElem_cons_succ]
      have := ih (i := i') (by simp at hi; omega); omega

theorem k6_list_swap_perm {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    ((xs.set i xs[j]).set j xs[i]).Perm xs := by
  rw [List.perm_iff_count]; intro a
  have h1 := k6_count_set_eq xs hi xs[j] a
  have h2 := k6_count_set_eq (xs.set i xs[j]) (i := j) (by simp [hj]) xs[i] a
  by_cases hij : i = j
  · subst hij; simp only [List.getElem_set_self] at h2; omega
  · simp only [List.getElem_set_ne hij] at h2; omega

theorem k6_drop_take_set_swap {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {off sz p q : Nat}
    (hp : p < sz) (hq : q < sz) (hbd : off + sz ≤ xs.length) :
    (((xs.set (off + p) (xs[off + q]'(by omega))).set (off + q)
        (xs[off + p]'(by omega))).drop off |>.take sz).Perm ((xs.drop off).take sz) := by
  have hlen : ((xs.drop off).take sz).length = sz := by simp; omega
  have h1 : (((xs.set (off + p) (xs[off + q]'(by omega))).set (off + q)
      (xs[off + p]'(by omega))).drop off).take sz =
      (((xs.drop off).take sz).set p (((xs.drop off).take sz)[q]'(by omega))).set q
        (((xs.drop off).take sz)[p]'(by omega)) := by
    apply List.ext_getElem?; intro k
    by_cases hk : k < sz
    · have hk1 : k < (((xs.set (off + p) xs[off + q]).set (off + q) xs[off + p]).drop off
          |>.take sz).length := by simp; omega
      have hk2 : k < ((((xs.drop off).take sz).set p ((xs.drop off).take sz)[q]).set q
          ((xs.drop off).take sz)[p]).length := by simp [hlen]; exact hk
      rw [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem hk2]
      simp only [List.getElem_take, List.getElem_drop, Option.some.injEq]
      by_cases hkq : k = q
      · subst hkq
        rw [List.getElem_set_self (by simp; omega), List.getElem_set_self (by simp [hlen, hq])]
      · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (Ne.symm hkq)]
        by_cases hkp : k = p
        · subst hkp
          rw [List.getElem_set_self (by simp; omega), List.getElem_set_self (by simp [hlen, hp])]
        · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (Ne.symm hkp)]
          simp [List.getElem_take, List.getElem_drop]
    · have hk1 : (((xs.set (off + p) xs[off + q]).set (off + q) xs[off + p]).drop off
          |>.take sz).length ≤ k := by simp; omega
      have hk2 : ((((xs.drop off).take sz).set p ((xs.drop off).take sz)[q]).set q
          ((xs.drop off).take sz)[p]).length ≤ k := by simp [hlen]; omega
      rw [List.getElem?_eq_none hk1, List.getElem?_eq_none hk2]
  rw [h1]; exact k6_list_swap_perm ((xs.drop off).take sz) (by omega) (by omega)

theorem k6_drop_take_set_out {α : Type} (xs : List α) {off sz idx : Nat} (v : α)
    (hout : idx < off ∨ off + sz ≤ idx) :
    ((xs.set idx v).drop off).take sz = (xs.drop off).take sz := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop, List.length_set]
  · intro k hk1 _
    have : k < sz ∧ off + k < xs.length := by simp at hk1; omega
    simp only [List.getElem_take, List.getElem_drop]
    rw [List.getElem_set_ne (by omega)]

theorem k6_list_flatten_set_perm {α : Type} (xs : List (List α)) {i : Nat} (hi : i < xs.length)
    (a : α) : (xs.set i (a :: xs[i])).flatten.Perm (a :: xs.flatten) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x tl ih =>
    cases i with
    | zero => simp
    | succ i' =>
      simp only [List.set_cons_succ, List.flatten_cons, List.getElem_cons_succ]
      exact (List.Perm.append_left x (ih (by simp at hi; omega))).trans List.perm_middle

theorem K6Inv.mono_P {L : K6Layout} {P P' : (Nat → Bool) → Prop} {ks : K6State}
    (himp : ∀ β, P' β → P β) (h : K6Inv L P ks) : K6Inv L P' ks :=
  { shapes := h.shapes
    clauses := { h.clauses with
      cl_wf := fun cid hc => let w := h.clauses.cl_wf cid hc
        ⟨w.1, w.2.1, w.2.2.1, fun β hβ => w.2.2.2 β (himp β hβ)⟩
      incons_ok := fun hi β hβ => h.clauses.incons_ok hi β (himp β hβ) }
    watches := h.watches
    assign := { h.assign with
      lvl0_ok := fun i hi hl0 => let w := h.assign.lvl0_ok i hi hl0
        ⟨w.1, w.2.1, fun β hβ => w.2.2 β (himp β hβ)⟩ }
    reasons := h.reasons }

theorem K6ScratchInv.mono_P {P P' : (Nat → Bool) → Prop} {scr : List (BitVec 32)}
    (himp : ∀ β, P' β → P β) (h : K6ScratchInv P scr) : K6ScratchInv P' scr :=
  ⟨h.1, h.2.1, h.2.2.mono_P himp⟩

/-! ## 2. Trail, Clause-Literal, & Refutation Helpers -/

theorem k6_mem_clauseLits_iff {ks : K6State} {cid : Nat}
    (hbd : k6ClauseOff ks cid + k6ClauseSize ks cid ≤ ks.arena.length) {l : Nat} :
    l ∈ k6ClauseLits ks cid ↔
      ∃ n < k6ClauseSize ks cid, (ks.arena[k6ClauseOff ks cid + n]?.getD 0#32).toNat = l := by
  unfold k6ClauseLits; rw [List.mem_map]; constructor
  · rintro ⟨b, hb, rfl⟩; rw [List.mem_iff_getElem] at hb; obtain ⟨n, hn, rfl⟩ := hb
    have hns : n < k6ClauseSize ks cid := by simp [List.length_take] at hn; omega
    have hlt : k6ClauseOff ks cid + n < ks.arena.length := by omega
    exact ⟨n, hns, by simp [List.getElem_take, List.getElem_drop, List.getElem?_eq_getElem hlt]⟩
  · rintro ⟨n, hn, rfl⟩
    have hlt : k6ClauseOff ks cid + n < ks.arena.length := by omega
    refine ⟨ks.arena[k6ClauseOff ks cid + n]'hlt, ?_, by simp [List.getElem?_eq_getElem hlt]⟩
    rw [List.mem_iff_getElem]
    exact ⟨n, by simp [List.length_take, List.length_drop]; omega,
      by simp [List.getElem_take, List.getElem_drop]⟩

theorem k6_mem_trailLits_of_lt {ks : K6State} {i : Nat}
    (hi : i < ks.trl_end.toNat) (hle : ks.trl_end.toNat ≤ ks.trl.length) :
    (ks.trl[i]?.getD 0#32).toNat ∈ k6TrailLits ks := by
  unfold k6TrailLits; rw [List.mem_map]
  refine ⟨ks.trl[i]'(by omega), ?_,
    by simp [List.getElem?_eq_getElem (by omega : i < ks.trl.length)]⟩
  rw [List.mem_iff_getElem]; exact ⟨i, by simp [List.length_take]; omega, by simp⟩

theorem k6_mem_trailDecisions_iff {ks : K6State} {d : Nat}
    (hle : ks.trl_end.toNat ≤ ks.trl.length) :
    d ∈ k6TrailDecisions ks ↔
      ∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat = d ∧
        0 < (ks.lvlArr[d / 2]?.getD 0#32).toNat ∧ ks.rsn[d / 2]?.getD 0#32 = 0xFFFFFFFF#32 := by
  unfold k6TrailDecisions; rw [List.mem_filterMap]; constructor
  · rintro ⟨l, hl, hif⟩; obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    have hlt : i < ks.trl_end.toNat := by simp at hi; omega
    simp only [List.getElem_take] at hif
    have h1 : i < ks.trl.length := by omega
    split at hif
    · rename_i hc; simp only [Option.some.injEq] at hif
      refine ⟨i, hlt, ?_, hif ▸ hc.1, hif ▸ hc.2⟩
      rw [List.getElem?_eq_getElem h1, Option.getD_some]; exact hif
    · simp at hif
  · rintro ⟨i, hi, hteq, hpos, hrs⟩
    have h1 : i < ks.trl.length := by omega
    refine ⟨ks.trl[i], ?_, ?_⟩
    · rw [List.mem_iff_getElem]; exact ⟨i, by simp [List.length_take]; omega, by simp⟩
    · rw [List.getElem?_eq_getElem h1, Option.getD_some] at hteq
      rw [hteq]; simp [hpos, hrs]

theorem k6_trl_nodup_var_ne {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hsh : ks.ShapesOk L) (hnv : ks.nv.toNat ≤ L.maxV) (hba : K6BaseAssignOk P ks)
    {i j : Nat} (hi : i < ks.trl_end.toNat) (hj : j < ks.trl_end.toNat) (hne : i ≠ j) :
    (ks.trl[i]?.getD 0#32).toNat / 2 ≠ (ks.trl[j]?.getD 0#32).toNat / 2 := by
  have hte := hba.trl_end_le
  have hlen : ks.trl_end.toNat ≤ ks.trl.length := by rw [hsh.trl_len]; omega
  have hnd := hba.trl_nodup; unfold k6TrailLits at hnd; rw [List.map_map] at hnd
  have hm_len : (List.map ((fun x => x / 2) ∘ BitVec.toNat)
      (ks.trl.take ks.trl_end.toNat)).length = ks.trl_end.toNat := by simp [List.length_take]; omega
  intro heq
  exact hne (k6_list_nodup_getElem_inj hnd (by omega) (by omega) (by
    simp only [List.getElem_map, List.getElem_take, Function.comp_def]
    rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length),
      List.getElem?_eq_getElem (by omega : j < ks.trl.length), Option.getD_some,
      Option.getD_some] at heq
    exact heq))

theorem k6_trl_end_lt_of_unassigned {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hsh : ks.ShapesOk L) (hnv : ks.nv.toNat ≤ L.maxV) (hba : K6BaseAssignOk P ks)
    {l : Nat} (hl : l < 2 * ks.nv.toNat) (h0 : ks.vals[l]?.getD 0#32 = 0#32) :
    ks.trl_end.toNat < ks.nv.toNat := by
  have hle := hba.trl_end_le
  by_cases hlt : ks.trl_end.toNat < ks.nv.toNat
  · exact hlt
  · exfalso
    have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by rw [hsh.trl_len]; omega
    have hv_mem := k6_nodup_mem_of_length_ge (n := ks.nv.toNat) hba.trl_nodup (fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨t, ht, rfl⟩ := hx; have := hba.trl_lt t ht; omega)
      (by simp [k6TrailLits, List.length_take]; omega) (v := l / 2) (by omega)
    rw [List.mem_map] at hv_mem; obtain ⟨t, ht, htv⟩ := hv_mem
    unfold k6TrailLits at ht; rw [List.mem_map] at ht; obtain ⟨bv, hbv, rfl⟩ := ht
    obtain ⟨i, hi, heq_bv⟩ := List.getElem_of_mem hbv
    have hi_te : i < ks.trl_end.toNat := by simp [List.length_take] at hi; omega
    simp only [List.getElem_take] at heq_bv
    have hnz := (hba.vals_nz_iff_trl l hl).mpr ⟨i, hi_te, by
      rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length), Option.getD_some, heq_bv]
      exact htv⟩
    exact hnz h0

theorem k6_vals_xor1_zero {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) {l : Nat} (hl : l < 2 * ks.nv.toNat)
    (hz : ks.vals[l]?.getD 0#32 = 0#32) : ks.vals[l ^^^ 1]?.getD 0#32 = 0#32 := by
  have hnl : l ^^^ 1 < 2 * ks.nv.toNat := by
    rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  rcases hinv.assign.vals_dom (l ^^^ 1) hnl with h0 | h1 | h2
  · exact h0
  · exfalso; have hneg := (hinv.assign.vals_neg_iff (l ^^^ 1) hnl).mp h1
    rw [k6_nat_xor1_xor1, hz] at hneg; cases hneg
  · exfalso; have hneg := (hinv.assign.vals_neg_iff l hl).mpr h2; rw [hz] at hneg; cases hneg

theorem k6_falsified_to_trail {P : (Nat → Bool) → Prop} {ks : K6State}
    (hba : K6BaseAssignOk P ks) (hsync : K6TrailSynced ks) {l : Nat} (hl : l < 2 * ks.nv.toNat)
    (hfals : ks.vals[l]? = some 2#32) :
    ∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat = l ^^^ 1 := by
  obtain ⟨i, hi, hveq⟩ := (hba.vals_nz_iff_trl l hl).mp (by simp [hfals])
  have hs := hsync i hi
  let tl := (ks.trl[i]?.getD 0#32).toNat
  change ks.vals[tl]? = some 1#32 ∧ ks.vals[tl ^^^ 1]? = some 2#32 at hs
  rcases (litVar_eq_iff tl l).mp (by simpa [litVar] using hveq) with heq | heq
  · rw [heq, hfals] at hs; cases hs.1
  · exact ⟨i, hi, heq⟩

theorem k6_falsified_lvl0_entails {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hlvl0 : ks.lvl = 0#32) {l : Nat} (hl : l < 2 * ks.nv.toNat)
    (hfals : ks.vals[l]? = some 2#32) :
    (∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat = l ^^^ 1) ∧
    SemEntails P [l ^^^ 1] := by
  obtain ⟨i, hi, hveq⟩ := (hinv.assign.vals_nz_iff_trl l hl).mp (by simp [hfals])
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.clauses.nv_le; omega
  let tl := (ks.trl[i]?.getD 0#32).toNat
  have htl_lt : tl < 2 * ks.nv.toNat := hinv.assign.trl_lt tl (k6_mem_trailLits_of_lt hi htrl_len)
  have hl0 : ks.lvlArr[tl / 2]?.getD 0#32 = 0#32 := by
    have hle := hinv.assign.trl_lvl_le (tl / 2) (by omega)
    rw [hlvl0] at hle; exact BitVec.eq_of_toNat_eq (Nat.eq_zero_of_le_zero hle)
  have hok := hinv.assign.lvl0_ok i hi hl0
  change ks.vals[tl]? = some 1#32 ∧ ks.vals[tl ^^^ 1]? = some 2#32 ∧ SemEntails P [tl] at hok
  rcases (litVar_eq_iff tl l).mp (by simpa [litVar] using hveq) with heq | heq
  · rw [heq, hfals] at hok; cases hok.1
  · rw [show litNeg l = l ^^^ 1 from rfl] at heq
    exact ⟨⟨i, hi, heq⟩, heq ▸ hok.2.2⟩

theorem k6_conflict_unsat_lvl0 {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hlvl0 : ks.lvl = 0#32) {cid : Nat} (hcid : cid < ks.nc.toNat)
    (hfals : ∀ l ∈ k6ClauseLits ks cid, ks.vals[l]? = some 2#32) : ∀ β, ¬ P β :=
  fun β hβ => by
    obtain ⟨l, hl, hs⟩ := (clause_sat_cnfClause_iff β _).mp
      ((hinv.clauses.cl_wf cid hcid).2.2.2 β hβ)
    have hneg := (k6_falsified_lvl0_entails hinv hlvl0
      ((hinv.clauses.cl_wf cid hcid).2.2.1 l hl) (hfals l hl)).2 β hβ
    exact absurd ((sat_cnfClause_singleton β l).mpr hs)
      ((sat_cnfClause_litNeg_iff β l).mp hneg)

theorem k6_trail_entails_assumps {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hdec : ∀ d ∈ k6TrailDecisions ks, d ∈ k6AssumpLits ks)
    {β : Nat → Bool} (hP : P β) (hA : (unitsCnf (k6AssumpLits ks)).Sat β) :
    ∀ i < ks.trl_end.toNat, (cnfClause [(ks.trl[i]?.getD 0#32).toNat]).Sat β := by
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.clauses.nv_le; omega
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi
    let l := (ks.trl[i]?.getD 0#32).toNat
    rcases hinv.reasons i hi with hrsn | ⟨hr_lt, hl_mem, hoth⟩
    · by_cases hl0 : ks.lvlArr[l / 2]?.getD 0#32 = 0#32
      · exact (hinv.assign.lvl0_ok i hi hl0).2.2 β hP
      · have hpos : 0 < (ks.lvlArr[l / 2]?.getD 0#32).toNat :=
          Nat.pos_of_ne_zero fun hz => hl0 (BitVec.eq_of_toNat_eq hz)
        have hl_lt := hinv.assign.trl_lt l (k6_mem_trailLits_of_lt hi htrl_len)
        have hrl : l / 2 < ks.rsn.length := by
          rw [hinv.shapes.rsn_len]; have := hinv.clauses.nv_le; omega
        have hrsn' : ks.rsn[l / 2]?.getD 0#32 = 0xFFFFFFFF#32 := by
          rw [List.getElem?_eq_getElem hrl, Option.getD_some] at hrsn ⊢; exact hrsn
        have hd_mem : l ∈ k6TrailDecisions ks :=
          (k6_mem_trailDecisions_iff htrl_len).mpr ⟨i, hi, rfl, hpos, hrsn'⟩
        exact (sat_unitsCnf_iff β (k6AssumpLits ks)).mp hA l (hdec l hd_mem)
    · have hce := (hinv.clauses.cl_wf _ hr_lt).2.2.2 β hP
      obtain ⟨x, hx_mem, hxs⟩ := (clause_sat_cnfClause_iff β _).mp hce
      by_cases hxl : x = l
      · rw [hxl] at hxs; exact (sat_cnfClause_singleton β l).mpr hxs
      · obtain ⟨j, hj_lt, hj_eq⟩ := hoth x hx_mem hxl
        have hjs := ih j hj_lt (Nat.lt_trans hj_lt hi)
        rw [hj_eq] at hjs
        exact absurd ((sat_cnfClause_singleton β x).mpr hxs) ((sat_cnfClause_litNeg_iff β x).mp hjs)

theorem k6_conflict_unsat_assumps {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    (hdec : ∀ d ∈ k6TrailDecisions ks, d ∈ k6AssumpLits ks)
    {cid : Nat} (hcid : cid < ks.nc.toNat)
    (hfals : ∀ l ∈ k6ClauseLits ks cid, ks.vals[l]? = some 2#32) :
    ∀ β, P β → ¬ (unitsCnf (k6AssumpLits ks)).Sat β := fun β hP hA => by
  obtain ⟨l, hl_mem, hls⟩ := (clause_sat_cnfClause_iff β _).mp
    ((hinv.clauses.cl_wf cid hcid).2.2.2 β hP)
  have hl_lt := (hinv.clauses.cl_wf cid hcid).2.2.1 l hl_mem
  obtain ⟨i, hi, hieq⟩ := k6_falsified_to_trail hinv.assign hsync hl_lt (hfals l hl_mem)
  have hts := k6_trail_entails_assumps hinv hdec hP hA i hi
  rw [hieq] at hts
  exact (sat_cnfClause_litNeg_iff β l).mp hts ((sat_cnfClause_singleton β l).mpr hls)

theorem k6_falsified_assump_unsat {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    (hdec : ∀ d ∈ k6TrailDecisions ks, d ∈ k6AssumpLits ks)
    {i : Nat} (hi : i < ks.nassump.toNat)
    (hfals : ks.vals[(ks.assump[i]?.getD 0#32).toNat]? = some 2#32) :
    ∀ β, P β → ¬ (unitsCnf (k6AssumpLits ks)).Sat β := fun β hP hA => by
  let a := (ks.assump[i]?.getD 0#32).toNat
  have ha_lt := hinv.clauses.assump_ok i hi
  have ha_mem : a ∈ k6AssumpLits ks := by
    unfold k6AssumpLits; rw [List.mem_map]
    have hlen : ks.nassump.toNat ≤ ks.assump.length := by
      rw [hinv.shapes.assump_len]; exact hinv.clauses.nassump_le
    refine ⟨ks.assump[i]?.getD 0#32, ?_, rfl⟩
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [List.length_take]; omega,
      by simp [List.getElem?_eq_getElem (by omega : i < ks.assump.length)]⟩
  have hsa := (sat_unitsCnf_iff β (k6AssumpLits ks)).mp hA a ha_mem
  obtain ⟨j, hj, hjeq⟩ := k6_falsified_to_trail hinv.assign hsync ha_lt hfals
  have hts := k6_trail_entails_assumps hinv hdec hP hA j hj
  rw [hjeq] at hts
  exact (sat_cnfClause_litNeg_iff β a).mp hts hsa

/-! ## 3. Watch-Chain (`K6_BIN_FLAG`) & Structural Preservation Lemmas -/

theorem k6_wchain_congr {wn1 wn2 : List (BitVec 32)} {hd : BitVec 32} {ws : List Nat}
    (hc : K5WChain wn1 hd ws) (hcongr : ∀ w ∈ ws, wn1[w]? = wn2[w]?) : K5WChain wn2 hd ws := by
  induction hc with
  | nil => exact K5WChain.nil
  | @cons w ws hw _ ih =>
    have hw2 : w < wn2.length := by
      have heq := hcongr w List.mem_cons_self
      rw [List.getElem?_eq_getElem hw] at heq
      exact (List.getElem?_eq_some_iff.mp heq.symm).1
    have hnxt : wn1[w]'hw = wn2[w]'hw2 := by
      have heq := hcongr w List.mem_cons_self
      rw [List.getElem?_eq_getElem hw, List.getElem?_eq_getElem hw2] at heq
      exact Option.some.inj heq
    have ih' := ih fun x hx => hcongr x (List.mem_cons_of_mem _ hx)
    rw [hnxt] at ih'; exact K5WChain.cons hw2 ih'

theorem k6_wchain_lt_length {wn : List (BitVec 32)} {hd : BitVec 32} {ws : List Nat}
    (hc : K5WChain wn hd ws) : ∀ w ∈ ws, w < wn.length := by
  induction hc with
  | nil => intro _ hm; nomatch hm
  | @cons w ws hw _ ih =>
    intro x hx; rcases List.mem_cons.mp hx with rfl | hmem
    · exact hw
    · exact ih x hmem

theorem k6_wchain_cases {wn : List (BitVec 32)} {hd : BitVec 32} {ws : List Nat}
    (hc : K5WChain wn hd ws) :
    (hd = 0xFFFFFFFF#32 ∧ ws = []) ∨
    (∃ w ws', ∃ (hw : w < wn.length),
      hd = BitVec.ofNat 32 w ∧ ws = w :: ws' ∧ K5WChain wn (wn[w]'hw) ws') := by
  cases hc with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | @cons w ws' hw ht => exact Or.inr ⟨w, ws', hw, rfl, rfl, ht⟩

theorem k6_wchain_unique {wn : List (BitVec 32)} {hd : BitVec 32} {ws1 ws2 : List Nat}
    (hwn : wn.length < 2 ^ 32) (h1 : K5WChain wn hd ws1) (h2 : K5WChain wn hd ws2) :
    ws1 = ws2 := by
  induction h1 generalizing ws2 with
  | nil =>
    rcases k6_wchain_cases h2 with ⟨_, rfl⟩ | ⟨w, _, hw, h2eq, _, _⟩
    · rfl
    · exfalso; have h2 := congrArg BitVec.toNat h2eq
      simp [Nat.mod_eq_of_lt (Nat.lt_trans hw hwn)] at h2; omega
  | @cons w1 ws1' hw1 _ ih =>
    rcases k6_wchain_cases h2 with ⟨h2eq, _⟩ | ⟨w2, ws2', hw2, h2eq, rfl, ht2⟩
    · exfalso; have h2 := congrArg BitVec.toNat h2eq
      simp [Nat.mod_eq_of_lt (Nat.lt_trans hw1 hwn)] at h2; omega
    · have h12 : w1 = w2 := by
        have ht := congrArg BitVec.toNat h2eq
        rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (Nat.lt_trans hw1 hwn), Nat.mod_eq_of_lt (Nat.lt_trans hw2 hwn)] at ht
      subst h12; exact congrArg (w1 :: ·) (ih ht2)

theorem k6_wchain_getElem_of_eq {wn : List (BitVec 32)} {hd : BitVec 32} {ws : List Nat}
    (hc : K5WChain wn hd ws) (hne : hd ≠ 0xFFFFFFFF#32) :
    ∃ w ws', ∃ (hw : w < wn.length), ws = w :: ws' ∧ hd = BitVec.ofNat 32 w ∧
      K5WChain wn (wn[w]'hw) ws' := by
  rcases k6_wchain_cases hc with ⟨heq, _⟩ | ⟨w, ws', hw, rfl, rfl, htail⟩
  · exact absurd heq hne
  · exact ⟨w, ws', hw, rfl, rfl, htail⟩

theorem k6_wchain_nil_iff {wn : List (BitVec 32)} {hd : BitVec 32} {ws : List Nat}
    (hwn : wn.length < 2 ^ 32) (hc : K5WChain wn hd ws) : hd = 0xFFFFFFFF#32 → ws = [] := by
  intro heq
  rcases k6_wchain_cases hc with ⟨_, rfl⟩ | ⟨w, _, hw, h2eq, _, _⟩
  · rfl
  · exfalso
    have h2 : (BitVec.ofNat 32 w).toNat = (0xFFFFFFFF#32 : BitVec 32).toNat :=
      congrArg BitVec.toNat (h2eq.symm.trans heq)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hw hwn),
      show (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 by decide] at h2; omega

theorem k6WatchStep0_preserves_shapes {L : K6Layout} {ks : K6State} (h : ks.ShapesOk L)
    (w l vo : BitVec 32) : (k6WatchStep0 ks w l vo).ShapesOk L :=
  { h with whead_len := by simp [k6WatchStep0, h.whead_len]
           wnext_len := by simp [k6WatchStep0, h.wnext_len]
           wblit_len := by simp [k6WatchStep0, h.wblit_len] }

theorem k6WatchStep_preserves_shapes {L : K6Layout} {ks : K6State} (h : ks.ShapesOk L)
    (cid l0 l1 : BitVec 32) : (k6WatchStep ks cid l0 l1).ShapesOk L :=
  k6WatchStep0_preserves_shapes (k6WatchStep0_preserves_shapes h _ _ _) _ _ _

theorem k6WatchStep0_preserves_watches_with {L : K6Layout} {ks : K6State} (hsh : ks.ShapesOk L)
    {chains : List (List Nat)} (hlen : chains.length = 2 * ks.nv.toNat) (hnd : chains.flatten.Nodup)
    (hwc : ∀ x < 2 * ks.nv.toNat,
      K5WChain ks.wnext (ks.whead[x]?.getD 0xFFFFFFFF#32) (chains[x]?.getD []))
    (hbnd : ∀ x < 2 * ks.nv.toNat, ∀ u ∈ chains[x]?.getD [],
      u < 2 * ks.nc.toNat ∧ 2 ≤ k6ClauseSize ks (u / 2) ∧
      (ks.arena[k6ClauseOff ks (u / 2) + (u % 2)]?.getD 0#32).toNat = x ∧
      let wb := ks.wblit[u]?.getD 0#32
      let bv := (wb &&& 0x7FFFFFFF#32).toNat
      bv < 2 * ks.nv.toNat ∧ bv ∈ k6ClauseLits ks (u / 2) ∧
      ((wb &&& 0x80000000#32) ≠ 0#32 ↔ k6ClauseSize ks (u / 2) = 2) ∧
      (k6ClauseSize ks (u / 2) = 2 →
        bv = (ks.arena[k6ClauseOff ks (u / 2) + (u % 2 ^^^ 1)]?.getD 0#32).toNat))
    {w l ot : BitVec 32} (hw_nc : w.toNat < 2 * ks.nc.toNat) (hw_max : ks.nc.toNat ≤ L.maxCl)
    (hnv : ks.nv.toNat ≤ L.maxV) (hl : l.toNat < 2 * ks.nv.toNat) (hot : ot.toNat < 2 * ks.nv.toNat)
    (hot_mem : ot.toNat ∈ k6ClauseLits ks (w.toNat / 2))
    (hot_bin : k6ClauseSize ks (w.toNat / 2) = 2 →
      ot.toNat = (ks.arena[k6ClauseOff ks (w.toNat / 2) + (w.toNat % 2 ^^^ 1)]?.getD 0#32).toNat)
    (hsz : 2 ≤ k6ClauseSize ks (w.toNat / 2))
    (hlit : (ks.arena[k6ClauseOff ks (w.toNat / 2) + (w.toNat % 2)]?.getD 0#32).toNat = l.toNat)
    (hfresh : w.toNat ∉ chains.flatten) :
    let bf := if k6ClauseSize ks (w.toNat / 2) = 2 then 0x80000000#32 else 0#32
    let ks' := k6WatchStep0 ks w l (ot ||| bf)
    let chains' := chains.set l.toNat (w.toNat :: chains[l.toNat]'(by omega))
    chains'.length = 2 * ks'.nv.toNat ∧ chains'.flatten.Nodup ∧
    (∀ x < 2 * ks'.nv.toNat,
      K5WChain ks'.wnext (ks'.whead[x]?.getD 0xFFFFFFFF#32) (chains'[x]?.getD [])) ∧
    (∀ x < 2 * ks'.nv.toNat, ∀ u ∈ chains'[x]?.getD [],
      u < 2 * ks'.nc.toNat ∧ 2 ≤ k6ClauseSize ks' (u / 2) ∧
      (ks'.arena[k6ClauseOff ks' (u / 2) + (u % 2)]?.getD 0#32).toNat = x ∧
      let wb := ks'.wblit[u]?.getD 0#32
      let bv := (wb &&& 0x7FFFFFFF#32).toNat
      bv < 2 * ks'.nv.toNat ∧ bv ∈ k6ClauseLits ks' (u / 2) ∧
      ((wb &&& 0x80000000#32) ≠ 0#32 ↔ k6ClauseSize ks' (u / 2) = 2) ∧
      (k6ClauseSize ks' (u / 2) = 2 →
        bv = (ks'.arena[k6ClauseOff ks' (u / 2) + (u % 2 ^^^ 1)]?.getD 0#32).toNat)) ∧
    (∀ u, u ∈ chains'.flatten ↔ u = w.toNat ∨ u ∈ chains.flatten) := by
  intro bf ks' chains'
  have hm := L.hmaxV
  have hl_ch : l.toNat < chains.length := by omega
  have hwi_len : w.toNat < ks.wnext.length := by rw [hsh.wnext_len]; omega
  have hwbi_len : w.toNat < ks.wblit.length := by rw [hsh.wblit_len]; omega
  have hwh_len : l.toNat < ks.whead.length := by rw [hsh.whead_len]; omega
  have hnd' : chains'.flatten.Nodup :=
    (k6_list_flatten_set_perm chains hl_ch w.toNat).nodup_iff.mpr
      (List.nodup_cons.mpr ⟨hfresh, hnd⟩)
  have hperm : ∀ u, u ∈ chains'.flatten ↔ u = w.toNat ∨ u ∈ chains.flatten := fun u => by
    rw [(k6_list_flatten_set_perm chains hl_ch w.toNat).mem_iff, List.mem_cons]
  have hot31 : ot.toNat < 2 ^ 31 := by omega
  have hm1 := k6_bv32_lt31_and_mask hot31
  have hm2 := k6_bv32_or_bin_mask hot31
  refine ⟨by simp [chains', ks', k6WatchStep0, hlen], hnd', ?_, ?_, hperm⟩
  · intro x hx
    change x < 2 * ks.nv.toNat at hx
    have hx_ch : x < chains.length := by omega
    have hch_old := hwc x hx; rw [List.getElem?_eq_getElem hx_ch, Option.getD_some] at hch_old
    have hcl_x : x < chains'.length := by simp [chains', hx_ch]
    by_cases hxl : x = l.toNat
    · subst hxl; rw [List.getElem?_eq_getElem hcl_x, Option.getD_some]
      simp only [chains', List.getElem_set_self]
      have hwh' : ks'.whead[l.toNat]?.getD 0xFFFFFFFF#32 = w := by
        simp [ks', k6WatchStep0, List.getElem?_set_self hwh_len]
      rw [hwh']
      have hw_lt' : w.toNat < ks'.wnext.length := by simp [ks', k6WatchStep0, hwi_len]
      have hget : ks'.wnext[w.toNat]'hw_lt' = ks.whead[l.toNat]?.getD 0xFFFFFFFF#32 := by
        simp [ks', k6WatchStep0, List.getElem?_eq_getElem hwh_len]
      have htail : K5WChain ks'.wnext (ks'.wnext[w.toNat]'hw_lt') chains[l.toNat] := by
        rw [hget]; refine k6_wchain_congr hch_old fun u hu => ?_
        have hune : u ≠ w.toNat := fun heq => hfresh (by
          rw [← heq]; exact List.mem_flatten.mpr ⟨chains[l.toNat], List.getElem_mem hx_ch, hu⟩)
        exact (List.getElem?_set_ne hune.symm).symm
      simpa [BitVec.ofNat_toNat] using K5WChain.cons hw_lt' htail
    · rw [List.getElem?_eq_getElem hcl_x, Option.getD_some]
      simp only [chains', List.getElem_set_ne (Ne.symm hxl)]
      have hwh' : ks'.whead[x]?.getD 0xFFFFFFFF#32 = ks.whead[x]?.getD 0xFFFFFFFF#32 := by
        simp [ks', k6WatchStep0, List.getElem?_set_ne (Ne.symm hxl)]
      rw [hwh']; refine k6_wchain_congr hch_old fun u hu => ?_
      have hune : u ≠ w.toNat := fun heq => hfresh (by
        rw [← heq]; exact List.mem_flatten.mpr ⟨chains[x], List.getElem_mem hx_ch, hu⟩)
      exact (List.getElem?_set_ne hune.symm).symm
  · intro x hx u hu
    change x < 2 * ks.nv.toNat at hx
    have hx_ch : x < chains.length := by omega
    have hcl_x : x < chains'.length := by simp [chains', hx_ch]
    rw [List.getElem?_eq_getElem hcl_x, Option.getD_some] at hu
    by_cases hxl : x = l.toNat
    · subst hxl; simp only [chains', List.getElem_set_self] at hu
      rcases List.mem_cons.mp hu with rfl | hu_old
      · refine ⟨hw_nc, hsz, hlit, ?_⟩
        dsimp only; rw [show ks'.wblit[w.toNat]?.getD 0#32 = ot ||| bf by
          simp [ks', k6WatchStep0, List.getElem?_set_self hwbi_len]]
        by_cases hb2 : k6ClauseSize ks (w.toNat / 2) = 2
        · have hbf : bf = 0x80000000#32 := by simp only [bf, hb2, ite_true]
          rw [hbf, hm2.1, hm2.2]
          refine ⟨hot, hot_mem, ⟨fun _ => hb2, fun _ => by decide⟩, fun _ => hot_bin hb2⟩
        · have hbf : bf = 0#32 := by simp only [bf, hb2, ite_false]
          rw [hbf, BitVec.or_zero, hm1.1, hm1.2]
          exact ⟨hot, hot_mem, ⟨fun h => absurd rfl h, fun h => absurd h hb2⟩,
            fun h => absurd h hb2⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hbnd l.toNat hx u
          (by simpa [List.getElem?_eq_getElem hx_ch] using hu_old)
        have hune : u ≠ w.toNat := fun heq => hfresh (by
          rw [← heq]; exact List.mem_flatten.mpr ⟨chains[l.toNat], List.getElem_mem hx_ch, hu_old⟩)
        refine ⟨h1, h2, h3, ?_⟩
        rwa [show ks'.wblit[u]? = ks.wblit[u]? from List.getElem?_set_ne hune.symm]
    · simp only [chains', List.getElem_set_ne (Ne.symm hxl)] at hu
      obtain ⟨h1, h2, h3, h4⟩ := hbnd x hx u (by simpa [List.getElem?_eq_getElem hx_ch] using hu)
      have hune : u ≠ w.toNat := fun heq => hfresh (by
        rw [← heq]; exact List.mem_flatten.mpr ⟨chains[x], List.getElem_mem hx_ch, hu⟩)
      refine ⟨h1, h2, h3, ?_⟩
      rwa [show ks'.wblit[u]? = ks.wblit[u]? from List.getElem?_set_ne hune.symm]

theorem k6WatchStep_preserves_watches {L : K6Layout} {ks : K6State} (hsh : ks.ShapesOk L)
    (hw : K6WatchesOk ks) {cid l0 l1 : BitVec 32} (hc_lt : cid.toNat < ks.nc.toNat)
    (hc_max : ks.nc.toNat ≤ L.maxCl) (hnv : ks.nv.toNat ≤ L.maxV)
    (hl0 : l0.toNat < 2 * ks.nv.toNat) (hl1 : l1.toNat < 2 * ks.nv.toNat)
    (hsz : 2 ≤ k6ClauseSize ks cid.toNat)
    (hl0_mem : l0.toNat ∈ k6ClauseLits ks cid.toNat)
    (hl1_mem : l1.toNat ∈ k6ClauseLits ks cid.toNat)
    (hlit0 : (ks.arena[k6ClauseOff ks cid.toNat]?.getD 0#32).toNat = l0.toNat)
    (hlit1 : (ks.arena[k6ClauseOff ks cid.toNat + 1]?.getD 0#32).toNat = l1.toNat)
    (hfwd : ∀ chains : List (List Nat), chains.length = 2 * ks.nv.toNat → chains.flatten.Nodup →
      (∀ x < 2 * ks.nv.toNat,
        K5WChain ks.wnext (ks.whead[x]?.getD 0xFFFFFFFF#32) (chains[x]?.getD [])) →
      2 * cid.toNat ∉ chains.flatten ∧ 2 * cid.toNat + 1 ∉ chains.flatten) :
    K6WatchesOk (k6WatchStep ks cid l0 l1) := by
  have hm := L.hmaxV
  obtain ⟨chains, hlen, hnd, hwc, hbnd⟩ := hw
  obtain ⟨hf0, hf1⟩ := hfwd chains hlen hnd hwc
  have hw0 := k6_bv32_cid_w0 hc_lt (by unfold K6Layout.maxCl at hc_max; omega)
  have hw1 := k6_bv32_cid_w1 hc_lt (by unfold K6Layout.maxCl at hc_max; omega)
  let w0 := cid <<< 1; let w1 := w0 ||| 1#32
  have hw0_tn : w0.toNat = 2 * cid.toNat := hw0.1
  have hw1_tn : w1.toNat = 2 * cid.toNat + 1 := hw1.1
  have hstep0 := k6WatchStep0_preserves_watches_with hsh hlen hnd hwc hbnd
    (w := w0) (l := l0) (ot := l1) (by omega) hc_max hnv hl0 hl1
    (by rw [hw0_tn, show 2 * cid.toNat / 2 = cid.toNat by omega]; exact hl1_mem)
    (fun _ => by
      rw [hw0_tn, show 2 * cid.toNat / 2 = cid.toNat by omega,
        show 2 * cid.toNat % 2 = 0 by omega]; exact hlit1.symm)
    (by rw [hw0_tn, show 2 * cid.toNat / 2 = cid.toNat by omega]; exact hsz)
    (by rw [hw0_tn, show 2 * cid.toNat / 2 = cid.toNat by omega,
      show 2 * cid.toNat % 2 = 0 by omega]; exact hlit0)
    (by rw [hw0_tn]; exact hf0)
  have hsh0 := k6WatchStep0_preserves_shapes hsh w0 l0
    (l1 ||| (if k6ClauseSize ks (w0.toNat / 2) = 2 then 0x80000000#32 else 0#32))
  have h1 := k6WatchStep0_preserves_watches_with hsh0 hstep0.1 hstep0.2.1 hstep0.2.2.1
    hstep0.2.2.2.1 (w := w1) (l := l1) (ot := l0)
    (by change w1.toNat < 2 * ks.nc.toNat; omega) hc_max hnv hl1 hl0
    (by dsimp only [k6WatchStep0, k6ClauseLits, k6ClauseOff, k6ClauseSize]
        rw [hw1_tn, show (2 * cid.toNat + 1) / 2 = cid.toNat by omega]; exact hl0_mem)
    (fun _ => by
      dsimp only [k6WatchStep0, k6ClauseOff]
      rw [hw1_tn, show (2 * cid.toNat + 1) / 2 = cid.toNat by omega,
        show (2 * cid.toNat + 1) % 2 = 1 by omega]; exact hlit0.symm)
    (by dsimp only [k6WatchStep0, k6ClauseSize]
        rw [hw1_tn, show (2 * cid.toNat + 1) / 2 = cid.toNat by omega]; exact hsz)
    (by dsimp only [k6WatchStep0, k6ClauseOff]
        rw [hw1_tn, show (2 * cid.toNat + 1) / 2 = cid.toNat by omega,
          show (2 * cid.toNat + 1) % 2 = 1 by omega]; exact hlit1)
    (fun hm => by rcases (hstep0.2.2.2.2 w1.toNat).mp hm with heq | hmem
                  · omega
                  · exact hf1 (by rwa [← hw1_tn]))
  have hbf : (if k6ClauseSize ks (w0.toNat / 2) = 2 then 0x80000000#32 else 0#32) =
      if (ks.clSz[cid.toNat]?.getD 0#32).toNat = 2 then 0x80000000#32 else 0#32 := by
    rw [hw0_tn, show 2 * cid.toNat / 2 = cid.toNat by omega]; rfl
  have hcl1 :
      k6ClauseSize (k6WatchStep0 ks w0 l0
        (l1 ||| if k6ClauseSize ks (w0.toNat / 2) = 2 then 0x80000000#32 else 0#32))
        (w1.toNat / 2) = k6ClauseSize ks (w0.toNat / 2) := by
    dsimp only [k6ClauseSize, k6WatchStep0]
    rw [hw0_tn, hw1_tn, show 2 * cid.toNat / 2 = cid.toNat by omega,
      show (2 * cid.toNat + 1) / 2 = cid.toNat by omega]
  rw [hcl1] at h1
  let chains1 := chains.set l0.toNat (w0.toNat :: chains[l0.toNat]'(by omega))
  refine ⟨chains1.set l1.toNat (w1.toNat :: chains1[l1.toNat]'(by simp [chains1]; omega)), ?_⟩
  simpa only [k6WatchStep, ← hbf] using ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1⟩

theorem k6AssignStep_preserves_shapes {L : K6Layout} {ks : K6State} (h : ks.ShapesOk L)
    (lit rsn : BitVec 32) : (k6AssignStep ks lit rsn).ShapesOk L :=
  { h with lvlArr_len := by simp [k6AssignStep, h.lvlArr_len]
           rsn_len := by simp [k6AssignStep, h.rsn_len]
           trl_len := by simp [k6AssignStep, h.trl_len]
           flags_len := by simp [k6AssignStep, h.flags_len]
           vals_len := by simp [k6AssignStep, h.vals_len] }

private theorem k6_flags_bit1_preserved (fl : BitVec 32) (b : Bool) :
    ((if b then fl ||| 1#32 else fl &&& ~~~1#32) &&& 2#32) = (fl &&& 2#32) := by
  cases b <;> ext i hi
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.getElem_and, BitVec.getElem_not]
    have h1 : (1#32 : BitVec 32)[i] = false ∨ (2#32 : BitVec 32)[i] = false := by
      revert i hi; decide
    rcases h1 with h | h <;> simp [h]
  · simp only [↓reduceIte, BitVec.getElem_and, BitVec.getElem_or]
    have h1 : (1#32 : BitVec 32)[i] = false ∨ (2#32 : BitVec 32)[i] = false := by
      revert i hi; decide
    rcases h1 with h | h <;> simp [h]

theorem k6AssignStep_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    {lit rsn : BitVec 32} (hlit : lit.toNat < 2 * ks.nv.toNat)
    (hun : ks.vals[lit.toNat]? = some 0#32)
    (hlvl0 : ks.lvl = 0#32 → SemEntails P [lit.toNat])
    (hdec : 0 < ks.lvl.toNat → rsn = 0xFFFFFFFF#32 →
      ∀ i < ks.trl_end.toNat, ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ ks.lvl)
    (hrsn_ok : rsn = 0xFFFFFFFF#32 ∨
      (rsn.toNat < ks.nc.toNat ∧ lit.toNat ∈ k6ClauseLits ks rsn.toNat ∧
       ∀ x ∈ k6ClauseLits ks rsn.toNat, x ≠ lit.toNat →
         ∃ j < ks.trl_end.toNat, (ks.trl[j]?.getD 0#32).toNat = x ^^^ 1)) :
    K6Inv L P (k6AssignStep ks lit rsn) ∧ K6TrailSynced (k6AssignStep ks lit rsn) := by
  have hm := L.hmaxV
  let ks' := k6AssignStep ks lit rsn
  have hsh' := k6AssignStep_preserves_shapes hinv.shapes lit rsn
  have hnv := hinv.clauses.nv_le
  have hte_lt := k6_trl_end_lt_of_unassigned hinv.shapes hnv hinv.assign hlit (by simp [hun])
  have hun_pos : 0 < ks.unass.toNat := by have := hinv.assign.unass_eq; omega
  have e_te : ks'.trl_end.toNat = ks.trl_end.toNat + 1 := by
    dsimp only [ks', k6AssignStep]; bv_omega
  have e_un : ks'.unass.toNat = ks.unass.toNat - 1 := by
    dsimp only [ks', k6AssignStep]; simp only [hun_pos, ite_true]; bv_omega
  have hnl_eq : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := by simp
  have hv_eq : (lit >>> 1).toNat = lit.toNat / 2 := (k6_bv32_div2_lt hlit).1
  have hlit_len : lit.toNat < 2 * L.maxV := by omega
  have hnl_len : lit.toNat ^^^ 1 < 2 * L.maxV := by
    rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  have hv_len : lit.toNat / 2 < L.maxV := by omega
  have hte_len : ks.trl_end.toNat < L.maxV := by omega
  have hne_nl : lit.toNat ≠ lit.toNat ^^^ 1 := by
    rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  have hnot_trl : ∀ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := by
    intro i hi heq; have hnz := (hinv.assign.vals_nz_iff_trl lit.toNat hlit).mpr ⟨i, hi, heq⟩
    simp [hun] at hnz
  have hvals_lit : ks'.vals[lit.toNat]? = some 1#32 := by
    dsimp only [ks', k6AssignStep]
    rw [hnl_eq, List.getElem?_set_ne hne_nl.symm,
      List.getElem?_set_self (by rw [hinv.shapes.vals_len]; omega)]
  have hvals_nl : ks'.vals[lit.toNat ^^^ 1]? = some 2#32 := by
    dsimp only [ks', k6AssignStep]
    rw [hnl_eq, List.getElem?_set_self (by simp [hinv.shapes.vals_len]; omega)]
  have hvals_other : ∀ x, x / 2 ≠ lit.toNat / 2 → ks'.vals[x]? = ks.vals[x]? := fun x hne => by
    have hx1 : lit.toNat ≠ x := by
      rcases k6_nat_xor1_cases x with ⟨_, _⟩ | ⟨_, _⟩ <;>
        rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    have hx2 : lit.toNat ^^^ 1 ≠ x := by
      rcases k6_nat_xor1_cases x with ⟨_, _⟩ | ⟨_, _⟩ <;>
        rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    dsimp only [ks', k6AssignStep]; rw [hnl_eq, List.getElem?_set_ne hx2, List.getElem?_set_ne hx1]
  have htrl_lt_idx : ∀ i < ks.trl_end.toNat, ks'.trl[i]? = ks.trl[i]? := fun i hi => by
    dsimp only [ks', k6AssignStep]; exact List.getElem?_set_ne (by omega)
  have htrl_end_idx : ks'.trl[ks.trl_end.toNat]? = some lit := by
    dsimp only [ks', k6AssignStep]
    exact List.getElem?_set_self (by rw [hinv.shapes.trl_len]; omega)
  have hlvl_other : ∀ v, v ≠ lit.toNat / 2 → ks'.lvlArr[v]? = ks.lvlArr[v]? := fun v hne => by
    dsimp only [ks', k6AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne hne.symm
  have hlvl_v : ks'.lvlArr[lit.toNat / 2]? = some ks.lvl := by
    dsimp only [ks', k6AssignStep]; rw [hv_eq]
    exact List.getElem?_set_self (by rw [hinv.shapes.lvlArr_len]; omega)
  have hrsn_other : ∀ v, v ≠ lit.toNat / 2 → ks'.rsn[v]? = ks.rsn[v]? := fun v hne => by
    dsimp only [ks', k6AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne hne.symm
  have hrsn_v : ks'.rsn[lit.toNat / 2]? = some rsn := by
    dsimp only [ks', k6AssignStep]; rw [hv_eq]
    exact List.getElem?_set_self (by rw [hinv.shapes.rsn_len]; omega)
  have hcl' : K6ClausesOk L P ks' :=
    { hinv.clauses with
      flags_clean := fun v hv => by
        by_cases hvv : v = lit.toNat / 2
        · subst hvv
          have hfl : ks'.flags[lit.toNat / 2]?.getD 0#32 =
              if (lit &&& 1#32) ≠ 0#32 then ks.flags[lit.toNat / 2]?.getD 0#32 ||| 1#32
              else ks.flags[lit.toNat / 2]?.getD 0#32 &&& ~~~1#32 := by
            dsimp only [ks', k6AssignStep]
            rw [hv_eq, List.getElem?_set_self (by rw [hinv.shapes.flags_len]; omega),
              Option.getD_some]
          rw [hfl]
          by_cases hc : (lit &&& 1#32) ≠ 0#32
          · simpa [hc] using (k6_flags_bit1_preserved
              (ks.flags[lit.toNat / 2]?.getD 0#32) true).trans
              (hinv.clauses.flags_clean (lit.toNat / 2) hv)
          · simpa [hc] using (k6_flags_bit1_preserved
              (ks.flags[lit.toNat / 2]?.getD 0#32) false).trans
              (hinv.clauses.flags_clean (lit.toNat / 2) hv)
        · have hf : ks'.flags[v]? = ks.flags[v]? := by
            dsimp only [ks', k6AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne (Ne.symm hvv)
          rw [hf]; exact hinv.clauses.flags_clean v hv }
  have hsync' : K6TrailSynced ks' := fun i hi => by
    rw [e_te] at hi
    by_cases hie : i = ks.trl_end.toNat
    · subst hie
      change ks'.vals[(ks'.trl[ks.trl_end.toNat]?.getD 0#32).toNat]? = some 1#32 ∧
        ks'.vals[(ks'.trl[ks.trl_end.toNat]?.getD 0#32).toNat ^^^ 1]? = some 2#32
      rw [htrl_end_idx, Option.getD_some]; exact ⟨hvals_lit, hvals_nl⟩
    · have hi' : i < ks.trl_end.toNat := by omega
      let l := (ks.trl[i]?.getD 0#32).toNat
      have hne_v := hnot_trl i hi'
      have hne_vx : (l ^^^ 1) / 2 ≠ lit.toNat / 2 := by
        rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
      change ks'.vals[(ks'.trl[i]?.getD 0#32).toNat]? = some 1#32 ∧
        ks'.vals[(ks'.trl[i]?.getD 0#32).toNat ^^^ 1]? = some 2#32
      rw [htrl_lt_idx i hi']; change ks'.vals[l]? = some 1#32 ∧ ks'.vals[l ^^^ 1]? = some 2#32
      rw [hvals_other l hne_v, hvals_other (l ^^^ 1) hne_vx]; exact hsync i hi'
  have htrl_take : ks'.trl.take ks'.trl_end.toNat = ks.trl.take ks.trl_end.toNat ++ [lit] := by
    apply List.ext_getElem
    · have hlen1 : ks'.trl.length = L.maxV := hsh'.trl_len
      rw [List.length_take, List.length_append, List.length_cons, List.length_nil,
        e_te, hlen1, List.length_take, hinv.shapes.trl_len,
        Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    · intro i hi1 _
      have h1 : i < ks.trl_end.toNat + 1 := by simp [List.length_take, e_te] at hi1; omega
      simp only [List.getElem_take]
      by_cases hie : i = ks.trl_end.toNat
      · subst hie
        have hgl : ks'.trl[ks.trl_end.toNat]'(by rw [hsh'.trl_len]; omega) = lit := by
          have := htrl_end_idx; rw [List.getElem?_eq_getElem (by rw [hsh'.trl_len]; omega)] at this
          exact Option.some.inj this
        rw [hgl, List.getElem_append_right (by simp [List.length_take, hinv.shapes.trl_len]; omega)]
        simp [List.length_take, hinv.shapes.trl_len,
          show min ks.trl_end.toNat L.maxV = ks.trl_end.toNat by omega]
      · have hi' : i < ks.trl_end.toNat := by omega
        have hgl : ks'.trl[i]'(by rw [hsh'.trl_len]; omega) =
            ks.trl[i]'(by rw [hinv.shapes.trl_len]; omega) := by
          have := htrl_lt_idx i hi'
          rw [List.getElem?_eq_getElem (by rw [hsh'.trl_len]; omega),
            List.getElem?_eq_getElem (by rw [hinv.shapes.trl_len]; omega)] at this
          exact Option.some.inj this
        rw [hgl, List.getElem_append_left (by simp [List.length_take, hinv.shapes.trl_len]; omega),
          List.getElem_take]
  have hba' : K6BaseAssignOk P ks' := by
    refine ⟨by rw [e_te]; change ks.trl_end.toNat + 1 ≤ ks.nv.toNat; omega,
      by rw [e_te]; change ks.prop.toNat ≤ ks.trl_end.toNat + 1; have := hinv.assign.prop_le; omega,
      by rw [e_un, e_te]; change (ks.unass.toNat - 1) + (ks.trl_end.toNat + 1) = ks.nv.toNat
         have := hinv.assign.unass_eq; omega,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l hl; by_cases hv : l / 2 = lit.toNat / 2
      · rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
          rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩
        · rw [show l = lit.toNat by omega, hvals_lit]; exact Or.inr (Or.inl rfl)
        · rw [show l = lit.toNat ^^^ 1 by omega, hvals_nl]; exact Or.inr (Or.inr rfl)
        · rw [show l = lit.toNat ^^^ 1 by omega, hvals_nl]; exact Or.inr (Or.inr rfl)
        · rw [show l = lit.toNat by omega, hvals_lit]; exact Or.inr (Or.inl rfl)
      · rw [hvals_other l hv]; exact hinv.assign.vals_dom l hl
    · intro l hl; by_cases hv : l / 2 = lit.toNat / 2
      · rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
          rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩
        · rw [show l = lit.toNat by omega, hvals_lit, hvals_nl]; simp
        · rw [show l = lit.toNat ^^^ 1 by omega, k6_nat_xor1_xor1, hvals_nl, hvals_lit]; simp
        · rw [show l = lit.toNat ^^^ 1 by omega, k6_nat_xor1_xor1, hvals_nl, hvals_lit]; simp
        · rw [show l = lit.toNat by omega, hvals_lit, hvals_nl]; simp
      · have hvx : (l ^^^ 1) / 2 ≠ lit.toNat / 2 := by
          rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [hvals_other l hv, hvals_other (l ^^^ 1) hvx]; exact hinv.assign.vals_neg_iff l hl
    · intro l hl; constructor
      · intro hnz; by_cases hv : l / 2 = lit.toNat / 2
        · exact ⟨ks.trl_end.toNat, by rw [e_te]; omega,
            by rw [htrl_end_idx, Option.getD_some]; exact hv.symm⟩
        · rw [hvals_other l hv] at hnz
          obtain ⟨i, hi, hiv⟩ := (hinv.assign.vals_nz_iff_trl l hl).mp hnz
          exact ⟨i, by rw [e_te]; omega, by rw [htrl_lt_idx i hi]; exact hiv⟩
      · rintro ⟨i, hi, hiv⟩; rw [e_te] at hi
        by_cases hie : i = ks.trl_end.toNat
        · subst hie; rw [htrl_end_idx, Option.getD_some] at hiv
          rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
            rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩
          · rw [show l = lit.toNat by omega, hvals_lit]; decide
          · rw [show l = lit.toNat ^^^ 1 by omega, hvals_nl]; decide
          · rw [show l = lit.toNat ^^^ 1 by omega, hvals_nl]; decide
          · rw [show l = lit.toNat by omega, hvals_lit]; decide
        · have hi' : i < ks.trl_end.toNat := by omega
          rw [htrl_lt_idx i hi'] at hiv
          have hv : l / 2 ≠ lit.toNat / 2 := by rw [← hiv]; exact hnot_trl i hi'
          rw [hvals_other l hv]; exact (hinv.assign.vals_nz_iff_trl l hl).mpr ⟨i, hi', hiv⟩
    · unfold k6TrailLits; rw [htrl_take, List.map_append, List.map_append, List.nodup_append]
      refine ⟨hinv.assign.trl_nodup, by simp, fun x hx y hy heq => ?_⟩
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy; subst hy; subst heq
      rw [List.mem_map] at hx; obtain ⟨l0, hl0, hlv⟩ := hx
      rw [List.mem_map] at hl0; obtain ⟨b, hb, rfl⟩ := hl0
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      have hi' : i < ks.trl_end.toNat := by simp [List.length_take] at hi; omega
      simp only [List.getElem_take] at hlv
      exact hnot_trl i hi'
        (by rw [List.getElem?_eq_getElem (by rw [hinv.shapes.trl_len]; omega), Option.getD_some]
            exact hlv)
    · intro l hl; unfold k6TrailLits at hl; rw [htrl_take, List.map_append, List.mem_append] at hl
      rcases hl with hl | hl
      · exact hinv.assign.trl_lt l hl
      · simp at hl; subst hl; exact hlit
    · intro v hv; by_cases hvv : v = lit.toNat / 2
      · subst hvv; rw [hlvl_v, Option.getD_some]; exact Nat.le_refl _
      · rw [hlvl_other v hvv]; exact hinv.assign.trl_lvl_le v hv
    · intro v hv hz
      have hne : v ≠ lit.toNat / 2 := fun h => by
        subst h; rcases k6_nat_xor1_cases lit.toNat with ⟨he, _⟩ | ⟨_, hx⟩
        · rw [← he, hvals_lit] at hz; cases hz
        · rw [← hx, hvals_nl] at hz; cases hz
      rw [hvals_other (2 * v) (by omega)] at hz
      rw [hlvl_other v hne, hrsn_other v hne]; exact hinv.assign.unass_lvl_zero v hv hz
    · intro i j hij hj; rw [e_te] at hj
      by_cases hje : j = ks.trl_end.toNat
      · subst hje; rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some]
        by_cases hie : i = ks.trl_end.toNat
        · subst hie; rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some]
          exact Nat.le_refl _
        · have hi' : i < ks.trl_end.toNat := by omega
          rw [htrl_lt_idx i hi', hlvl_other _ (hnot_trl i hi')]
          have hli := hinv.assign.trl_lt _
            (k6_mem_trailLits_of_lt hi' (by rw [hinv.shapes.trl_len]; omega))
          exact hinv.assign.trl_lvl_le _ (by omega)
      · have hj' : j < ks.trl_end.toNat := by omega
        have hi' : i < ks.trl_end.toNat := by omega
        rw [htrl_lt_idx i hi', htrl_lt_idx j hj', hlvl_other _ (hnot_trl i hi'),
          hlvl_other _ (hnot_trl j hj')]
        exact hinv.assign.trl_lvl_mono i j hij hj'
    · intro i j hji hi hpos hlvl_eq; rw [e_te] at hi
      by_cases hie : i = ks.trl_end.toNat
      · subst hie
        have hj' : j < ks.trl_end.toNat := by omega
        rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some] at hpos hlvl_eq
        rw [htrl_lt_idx j hj', hlvl_other _ (hnot_trl j hj')] at hlvl_eq
        rw [htrl_end_idx, Option.getD_some, hrsn_v, Option.getD_some]
        intro hrs_eq; exact hdec hpos hrs_eq j hj' hlvl_eq
      · have hi' : i < ks.trl_end.toNat := by omega
        have hj' : j < ks.trl_end.toNat := by omega
        rw [htrl_lt_idx i hi', hlvl_other _ (hnot_trl i hi')] at hpos hlvl_eq
        rw [htrl_lt_idx j hj', hlvl_other _ (hnot_trl j hj')] at hlvl_eq
        rw [htrl_lt_idx i hi', hrsn_other _ (hnot_trl i hi')]
        exact hinv.assign.dec_earliest i j hji hi' hpos hlvl_eq
    · intro i hi; dsimp only; intro hl0; rw [e_te] at hi
      by_cases hie : i = ks.trl_end.toNat
      · subst hie
        rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some] at hl0
        rw [htrl_end_idx, Option.getD_some]; exact ⟨hvals_lit, hvals_nl, hlvl0 hl0⟩
      · have hi' : i < ks.trl_end.toNat := by omega
        let l := (ks.trl[i]?.getD 0#32).toNat
        have hne_v := hnot_trl i hi'
        have hne_vx : (l ^^^ 1) / 2 ≠ lit.toNat / 2 := by
          rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [htrl_lt_idx i hi'] at hl0 ⊢
        change ks'.lvlArr[l / 2]?.getD 0#32 = 0#32 at hl0
        rw [hlvl_other (l / 2) hne_v] at hl0
        change ks'.vals[l]? = some 1#32 ∧ ks'.vals[l ^^^ 1]? = some 2#32 ∧ SemEntails P [l]
        rw [hvals_other l hne_v, hvals_other (l ^^^ 1) hne_vx]; exact hinv.assign.lvl0_ok i hi' hl0
  have hre' : K6ReasonOk ks' := fun i hi => by
    rw [e_te] at hi
    by_cases hie : i = ks.trl_end.toNat
    · subst hie
      change let l := (ks'.trl[ks.trl_end.toNat]?.getD 0#32).toNat
             let r := ks'.rsn[l / 2]?.getD 0#32; _
      rw [htrl_end_idx, Option.getD_some, hrsn_v, Option.getD_some]
      rcases hrsn_ok with rfl | ⟨hr_lt, hmem, hoth⟩
      · exact Or.inl rfl
      · right; refine ⟨hr_lt, hmem, fun x hx hne => ?_⟩
        obtain ⟨j, hj, hje⟩ := hoth x hx hne
        exact ⟨j, hj, by rw [htrl_lt_idx j hj]; exact hje⟩
    · have hi' : i < ks.trl_end.toNat := by omega
      change let l := (ks'.trl[i]?.getD 0#32).toNat; let r := ks'.rsn[l / 2]?.getD 0#32; _
      rw [htrl_lt_idx i hi', hrsn_other _ (hnot_trl i hi')]
      rcases hinv.reasons i hi' with hnone | ⟨hr_lt, hmem, hoth⟩
      · exact Or.inl hnone
      · right; refine ⟨hr_lt, hmem, fun x hx hne => ?_⟩
        obtain ⟨j, hj, hje⟩ := hoth x hx hne
        exact ⟨j, by omega, by rw [htrl_lt_idx j (by omega)]; exact hje⟩
  exact ⟨⟨hsh', hcl', hinv.watches, hba', hre'⟩, hsync'⟩

theorem k6SetIncons_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hunsat : ∀ β, ¬ P β) :
    K6Inv L P (ks.putHdr .incons 1#32) := by
  dsimp only [K6State.putHdr]
  exact
    { shapes := hinv.shapes.putHdr .incons 1#32
      clauses := { hinv.clauses with incons_ok := fun _ => hunsat }
      watches := hinv.watches
      assign := ⟨hinv.assign.trl_end_le, hinv.assign.prop_le, hinv.assign.unass_eq,
        hinv.assign.vals_dom, hinv.assign.vals_neg_iff, hinv.assign.vals_nz_iff_trl,
        hinv.assign.trl_nodup, hinv.assign.trl_lt, hinv.assign.trl_lvl_le,
        hinv.assign.unass_lvl_zero, hinv.assign.trl_lvl_mono, hinv.assign.dec_earliest,
        hinv.assign.lvl0_ok⟩
      reasons := hinv.reasons }

theorem k6LitsBounded_mono {M1 M2 : Nat} {ks : K6State} (hle : M1 ≤ M2) (h : K6LitsBounded M1 ks) :
    K6LitsBounded M2 ks :=
  ⟨fun cid hc l hl => Nat.lt_of_lt_of_le (h.1 cid hc l hl) (by omega),
   fun w hw => Nat.lt_of_lt_of_le (h.2 w hw) (by omega)⟩

structure K6BtLoopInv (L : K6Layout) (ks : K6State) (target_lvl te : BitVec 32)
    (st : K6State) : Prop where
  sh : st.ShapesOk L
  te_le : te.toNat ≤ ks.trl_end.toNat
  unass_eq : st.unass.toNat + te.toNat = ks.nv.toNat
  nv_eq : st.nv = ks.nv
  nc_eq : st.nc = ks.nc
  lvl_eq : st.lvl = ks.lvl
  prop_eq : st.prop = ks.prop
  te_hdr : st.trl_end = ks.trl_end
  inc_eq : st.incons = ks.incons
  alen_eq : st.alen = ks.alen
  acap_eq : st.acap = ks.acap
  na_eq : st.nassump = ks.nassump
  nk_eq : st.nkl = ks.nkl
  nan_eq : st.nana = ks.nana
  st_eq : st.status = ks.status
  ph_eq : st.phase = ks.phase
  op_eq : st.openCnt = ks.openCnt
  mv_eq : st.max_v = ks.max_v
  mo_eq : st.max_orig = ks.max_orig
  mc_eq : st.max_cl = ks.max_cl
  nq_eq : st.neq = ks.neq
  ht_eq : st.hdrTail = ks.hdrTail
  qs_eq : st.qstampArr = ks.qstampArr
  trl_eq : st.trl = ks.trl
  fl_eq : st.flags = ks.flags
  ass_eq : st.assump = ks.assump
  ana_eq : st.ana = ks.ana
  kl_eq : st.kl = ks.kl
  wh_eq : st.whead = ks.whead
  wn_eq : st.wnext = ks.wnext
  wb_eq : st.wblit = ks.wblit
  co_eq : st.clOff = ks.clOff
  cs_eq : st.clSz = ks.clSz
  ar_eq : st.arena = ks.arena
  kept_var : ∀ w < ks.nv.toNat,
    (∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = w) →
    st.lvlArr[w]? = ks.lvlArr[w]? ∧ st.rsn[w]? = ks.rsn[w]? ∧
    st.vals[2 * w]? = ks.vals[2 * w]? ∧ st.vals[2 * w + 1]? = ks.vals[2 * w + 1]?
  cleared_var : ∀ w < ks.nv.toNat,
    (¬ ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = w) →
    st.lvlArr[w]? = some 0#32 ∧ st.rsn[w]? = some 0xFFFFFFFF#32 ∧
    st.vals[2 * w]? = some 0#32 ∧ st.vals[2 * w + 1]? = some 0#32
  popped_gt : ∀ i, te.toNat ≤ i → i < ks.trl_end.toNat →
    target_lvl.toNat < (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat

theorem k6BtLoopInv_init {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {target_lvl : BitVec 32} (hinv : K6Inv L P ks) :
    K6BtLoopInv L ks target_lvl ks.trl_end ks :=
  ⟨hinv.shapes, Nat.le_refl _, hinv.assign.unass_eq, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl,
   fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩,
   fun w hw hno => by
     have hz : ks.vals[2 * w]?.getD 0#32 = 0#32 := by
       by_cases hcz : ks.vals[2 * w]?.getD 0#32 = 0#32
       · exact hcz
       · obtain ⟨i, hi, hie⟩ := (hinv.assign.vals_nz_iff_trl (2 * w) (by omega)).mp hcz
         exact absurd ⟨i, hi, by simpa using hie⟩ hno
     have hzo := hinv.assign.unass_lvl_zero w hw hz
     have hz1 := k6_vals_xor1_zero hinv (by omega : 2 * w < 2 * ks.nv.toNat) hz
     rw [show (2 * w) ^^^ 1 = 2 * w + 1 by
       rcases k6_nat_xor1_cases (2 * w) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega] at hz1
     have hv0_len : 2 * w < ks.vals.length := by
       rw [hinv.shapes.vals_len]; have := hinv.clauses.nv_le; omega
     have hv1_len : 2 * w + 1 < ks.vals.length := by
       rw [hinv.shapes.vals_len]; have := hinv.clauses.nv_le; omega
     have hl_len : w < ks.lvlArr.length := by
       rw [hinv.shapes.lvlArr_len]; have := hinv.clauses.nv_le; omega
     have hr_len : w < ks.rsn.length := by
       rw [hinv.shapes.rsn_len]; have := hinv.clauses.nv_le; omega
     rw [List.getElem?_eq_getElem hl_len, Option.getD_some] at hzo
     rw [List.getElem?_eq_getElem hr_len, Option.getD_some] at hzo
     rw [List.getElem?_eq_getElem hv0_len, Option.getD_some] at hz
     rw [List.getElem?_eq_getElem hv1_len, Option.getD_some] at hz1
     exact ⟨by rw [List.getElem?_eq_getElem hl_len, hzo.1],
       by rw [List.getElem?_eq_getElem hr_len, hzo.2],
       by rw [List.getElem?_eq_getElem hv0_len, hz],
       by rw [List.getElem?_eq_getElem hv1_len, hz1]⟩,
   fun _ h1 h2 => absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.lt_irrefl _)⟩

theorem k6BtLoopInv_step {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {target_lvl te : BitVec 32} {st : K6State} (hinv : K6Inv L P ks)
    (hbt : K6BtLoopInv L ks target_lvl te st) (hpos : 0 < te.toNat)
    (hpop : target_lvl.toNat <
      (st.lvlArr[(ks.trl[te.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) :
    let lit := ks.trl[te.toNat - 1]?.getD 0#32
    let v := (lit >>> 1).toNat
    let st' := ((((st.putArr .vals lit.toNat 0#32).putArr .vals (lit ^^^ 1#32).toNat 0#32).putArr
      .lvlArr v 0#32).putArr .rsn v 0xFFFFFFFF#32).putHdr .unass (st.unass + 1#32)
    K6BtLoopInv L ks target_lvl (te - 1#32) st' ∧
    ∀ qs, K6BtLoopInv L ks target_lvl (te - 1#32) (st'.putHdr .qsearch qs) := by
  intro lit v st'
  have hm := L.hmaxV
  have hnv := hinv.clauses.nv_le
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; omega
  have hte1_lt : te.toNat - 1 < ks.trl_end.toNat := by have := hbt.te_le; omega
  have hv_lt : v < ks.nv.toNat := by
    have hm1 := k6_mem_trailLits_of_lt hte1_lt htrl_len
    have hlt := hinv.assign.trl_lt lit.toNat hm1
    have hdv := (k6_bv32_div2_lt hlt).1; omega
  have hnl_eq : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := by simp
  have hsh' : st'.ShapesOk L :=
    ((((hbt.sh.putArr .vals _ _).putArr .vals _ _).putArr .lvlArr _ _).putArr
      .rsn _ _).putHdr .unass _
  have hun_lt : st.unass.toNat + 1 < 2 ^ 32 := by have := hbt.unass_eq; omega
  have hmk : ∀ qOpt : Option (BitVec 32),
      K6BtLoopInv L ks target_lvl (te - 1#32)
        (match qOpt with | none => st' | some qs => st'.putHdr .qsearch qs) := by
    intro qOpt
    let finSt := match qOpt with | none => st' | some qs => st'.putHdr .qsearch qs
    have hshF : finSt.ShapesOk L := by
      cases qOpt with | none => exact hsh' | some qs => exact hsh'.putHdr .qsearch qs
    have hte_sub : (te - 1#32).toNat = te.toNat - 1 := by bv_omega
    have hunF : finSt.unass.toNat + (te - 1#32).toNat = ks.nv.toNat := by
      have hun_st : finSt.unass = st.unass + 1#32 := by
        cases qOpt <;> dsimp only [finSt, st'] <;> k6_field
      rw [hun_st, hte_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have := hbt.unass_eq; omega
    have hlvl_st : finSt.lvlArr = st.lvlArr.set v 0#32 := by
      cases qOpt <;> dsimp only [finSt, st'] <;> k6_field
    have hrsn_st : finSt.rsn = st.rsn.set v 0xFFFFFFFF#32 := by
      cases qOpt <;> dsimp only [finSt, st'] <;> k6_field
    have hvals_st : finSt.vals = (st.vals.set lit.toNat 0#32).set (lit.toNat ^^^ 1) 0#32 := by
      cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> rw [hnl_eq]
    have hv_eq : v = lit.toNat / 2 := (k6_bv32_div2_lt
      (hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hte1_lt htrl_len))).1
    have hl_xor := k6_nat_xor1_cases lit.toNat
    refine ⟨hshF, by rw [hte_sub]; omega, hunF,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.nv_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.nc_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.lvl_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.prop_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.te_hdr,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.inc_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.alen_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.acap_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.na_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.nk_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.nan_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.st_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.ph_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.op_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.mv_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.mo_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.mc_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.nq_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.ht_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.qs_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.trl_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.fl_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.ass_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.ana_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.kl_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.wh_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.wn_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.wb_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.co_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.cs_eq,
      by cases qOpt <;> dsimp only [finSt, st'] <;> k6_field <;> exact hbt.ar_eq,
      ?_, ?_, ?_⟩
    · intro w hw ⟨i, hi, hiw⟩
      have hi' : i < te.toNat - 1 := by rw [hte_sub] at hi; exact hi
      have hne_v : w ≠ v := by
        rw [← hiw, hv_eq]
        exact k6_trl_nodup_var_ne hinv.shapes hnv hinv.assign (Nat.lt_trans hi' (by omega)) hte1_lt
          (by omega)
      have hold := hbt.kept_var w hw ⟨i, by omega, hiw⟩
      rw [hlvl_st, hrsn_st, hvals_st, List.getElem?_set_ne (Ne.symm hne_v),
        List.getElem?_set_ne (Ne.symm hne_v)]
      rcases hl_xor with ⟨_, _⟩ | ⟨_, _⟩ <;>
        exact ⟨hold.1, hold.2.1,
          by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
             exact hold.2.2.1,
          by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
             exact hold.2.2.2⟩
    · intro w hw hnone
      by_cases hwv : w = v
      · subst hwv
        have hlv_len : v < st.lvlArr.length := by rw [hbt.sh.lvlArr_len]; omega
        have hrs_len : v < st.rsn.length := by rw [hbt.sh.rsn_len]; omega
        have hv0_len : 2 * v < st.vals.length := by rw [hbt.sh.vals_len]; omega
        have hv1_len : 2 * v + 1 < st.vals.length := by rw [hbt.sh.vals_len]; omega
        rw [hlvl_st, hrsn_st, hvals_st, List.getElem?_set_self hlv_len,
          List.getElem?_set_self hrs_len]
        refine ⟨rfl, rfl, ?_, ?_⟩
        · rcases hl_xor with ⟨h0a, h1a⟩ | ⟨h0a, h1a⟩
          · rw [h1a, h0a, ← hv_eq, List.getElem?_set_ne (by omega),
              List.getElem?_set_self hv0_len]
          · rw [h1a, ← hv_eq,
              List.getElem?_set_self (by simp only [List.length_set]; exact hv0_len)]
        · rcases hl_xor with ⟨h0a, h1a⟩ | ⟨h0a, h1a⟩
          · rw [h1a, ← hv_eq,
              List.getElem?_set_self (by simp only [List.length_set]; exact hv1_len)]
          · rw [h1a, h0a, ← hv_eq, List.getElem?_set_ne (by omega),
              List.getElem?_set_self hv1_len]
      · have hnone_old : ¬ ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = w := by
          rintro ⟨i, hi, hiw⟩
          by_cases hie : i = te.toNat - 1
          · subst hie; exact hwv (by rw [hv_eq]; exact hiw.symm)
          · exact hnone ⟨i, by rw [hte_sub]; omega, hiw⟩
        have hold := hbt.cleared_var w hw hnone_old
        rw [hlvl_st, hrsn_st, hvals_st, List.getElem?_set_ne (Ne.symm hwv),
          List.getElem?_set_ne (Ne.symm hwv)]
        rcases hl_xor with ⟨_, _⟩ | ⟨_, _⟩ <;>
          exact ⟨hold.1, hold.2.1,
            by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
               exact hold.2.2.1,
            by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
               exact hold.2.2.2⟩
    · intro i hlo hhi; rw [hte_sub] at hlo
      by_cases hie : i = te.toNat - 1
      · subst hie
        have hkept := hbt.kept_var (lit.toNat / 2) (by omega) ⟨te.toNat - 1, by omega, rfl⟩
        rw [hkept.1] at hpop; exact hpop
      · exact hbt.popped_gt i (by omega) hhi
  exact ⟨hmk none, fun qs => hmk (some qs)⟩

theorem k6BtLoopInv_finish {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {target_lvl te : BitVec 32} {st : K6State} (hinv : K6Inv L P ks)
    (hbt : K6BtLoopInv L ks target_lvl te st)
    (hsync_below : target_lvl = 0#32 ∨ K6TrailSynced ks)
    (hexit : te = 0#32 ∨
      ∃ i < te.toNat, i = te.toNat - 1 ∧
        (st.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat) :
    let st' := ((st.putHdr .trl_end te).putHdr .prop
      (if te.toNat < st.prop.toNat then te else st.prop)).putHdr .lvl target_lvl
    K6Inv L P st' ∧ K6TrailSynced st' ∧ st'.lvl = target_lvl ∧
    st'.trl_end.toNat ≤ ks.trl_end.toNat ∧ K6BtPreserved ks st' ∧
    (∀ i < st'.trl_end.toNat,
      st'.trl[i]? = ks.trl[i]? ∧ st'.rsn[(st'.trl[i]?.getD 0#32).toNat / 2]? =
        ks.rsn[(st'.trl[i]?.getD 0#32).toNat / 2]? ∧
      (st'.lvlArr[(st'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat) := by
  intro st'
  have hm := L.hmaxV; have hnv := hinv.clauses.nv_le
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; omega
  have hkept_lvl : ∀ i < te.toNat,
      (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat := by
    intro i hi
    rcases hexit with rfl | ⟨j, hj, _, hle⟩
    · simp at hi
    · have hj_lt : j < ks.trl_end.toNat := Nat.lt_of_lt_of_le hj hbt.te_le
      have hlj := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hj_lt htrl_len)
      have hkj := (hbt.kept_var _ (by omega) ⟨j, hj, rfl⟩).1
      rw [hkj] at hle
      exact Nat.le_trans (hinv.assign.trl_lvl_mono i j (by omega) hj_lt) hle
  have hsh' : st'.ShapesOk L := ((hbt.sh.putHdr .trl_end _).putHdr .prop _).putHdr .lvl _
  have e_nv : st'.nv = ks.nv := by dsimp only [st']; k6_field; exact hbt.nv_eq
  have e_nc : st'.nc = ks.nc := by dsimp only [st']; k6_field; exact hbt.nc_eq
  have e_lvl : st'.lvl = target_lvl := by dsimp only [st']; k6_field
  have e_te : st'.trl_end = te := by dsimp only [st']; k6_field
  have e_un : st'.unass = st.unass := by dsimp only [st']; k6_field
  have e_pr : st'.prop = if te.toNat < st.prop.toNat then te else st.prop := by
    dsimp only [st']; k6_field
  have e_trl : st'.trl = ks.trl := by dsimp only [st']; k6_field; exact hbt.trl_eq
  have e_la : st'.lvlArr = st.lvlArr := by dsimp only [st']; k6_field
  have e_rs : st'.rsn = st.rsn := by dsimp only [st']; k6_field
  have e_va : st'.vals = st.vals := by dsimp only [st']; k6_field
  have hpres : K6BtPreserved ks st' :=
    { nv := e_nv, nc := e_nc, incons := by dsimp only [st']; k6_field; exact hbt.inc_eq
      alen := by dsimp only [st']; k6_field; exact hbt.alen_eq
      acap := by dsimp only [st']; k6_field; exact hbt.acap_eq
      nassump := by dsimp only [st']; k6_field; exact hbt.na_eq
      nkl := by dsimp only [st']; k6_field; exact hbt.nk_eq
      nana := by dsimp only [st']; k6_field; exact hbt.nan_eq
      status := by dsimp only [st']; k6_field; exact hbt.st_eq
      phase := by dsimp only [st']; k6_field; exact hbt.ph_eq
      openCnt := by dsimp only [st']; k6_field; exact hbt.op_eq
      max_v := by dsimp only [st']; k6_field; exact hbt.mv_eq
      max_orig := by dsimp only [st']; k6_field; exact hbt.mo_eq
      max_cl := by dsimp only [st']; k6_field; exact hbt.mc_eq
      neq := by dsimp only [st']; k6_field; exact hbt.nq_eq
      hdrTail := by dsimp only [st']; k6_field; exact hbt.ht_eq
      assump := by dsimp only [st']; k6_field; exact hbt.ass_eq
      ana := by dsimp only [st']; k6_field; exact hbt.ana_eq
      kl := by dsimp only [st']; k6_field; exact hbt.kl_eq
      whead := by dsimp only [st']; k6_field; exact hbt.wh_eq
      wnext := by dsimp only [st']; k6_field; exact hbt.wn_eq
      wblit := by dsimp only [st']; k6_field; exact hbt.wb_eq
      clOff := by dsimp only [st']; k6_field; exact hbt.co_eq
      clSz := by dsimp only [st']; k6_field; exact hbt.cs_eq
      arena := by dsimp only [st']; k6_field; exact hbt.ar_eq
      flags2_eq := fun v _ => by
        have hfl : st'.flags = ks.flags := by dsimp only [st']; k6_field; exact hbt.fl_eq
        rw [hfl]
      lvlArr_kept := fun i hi => by
        rw [e_te] at hi; rw [e_trl, e_la]
        have hli :=
          hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt (Nat.lt_of_lt_of_le hi hbt.te_le) htrl_len)
        exact (hbt.kept_var _ (by omega) ⟨i, hi, rfl⟩).1 }
  have hcl' : K6ClausesOk L P st' :=
    { acap_eq := hpres.acap.trans hinv.clauses.acap_eq
      max_v_eq := hpres.max_v.trans hinv.clauses.max_v_eq
      max_orig_eq := hpres.max_orig.trans hinv.clauses.max_orig_eq
      max_cl_eq := hpres.max_cl.trans hinv.clauses.max_cl_eq
      nv_le := e_nv ▸ hinv.clauses.nv_le, nc_le := e_nc ▸ hinv.clauses.nc_le
      alen_le := hpres.alen ▸ hinv.clauses.alen_le
      nassump_le := hpres.nassump ▸ hinv.clauses.nassump_le
      nkl_le := hpres.nkl ▸ hinv.clauses.nkl_le, nana_le := hpres.nana ▸ hinv.clauses.nana_le
      cl_wf := by
        unfold k6ClauseLits k6ClauseOff k6ClauseSize
        rw [e_nc, e_nv, hpres.alen, hpres.clOff, hpres.clSz, hpres.arena]; exact hinv.clauses.cl_wf
      cl_mono := by
        unfold k6ClauseOff k6ClauseSize; rw [e_nc, hpres.clOff, hpres.clSz]
        exact hinv.clauses.cl_mono
      incons_ok := hpres.incons ▸ hinv.clauses.incons_ok
      assump_ok := by rw [e_nv, hpres.nassump, hpres.assump]; exact hinv.clauses.assump_ok
      flags_clean := fun v hv => by
        rw [e_nv] at hv; rw [hpres.flags2_eq v hv]; exact hinv.clauses.flags_clean v hv }
  have hw' : K6WatchesOk st' := by
    obtain ⟨ch, hch_len, hch_nd, hch_wc, hch_bnd⟩ := hinv.watches
    refine ⟨ch, by rw [e_nv]; exact hch_len, hch_nd, fun l hl => ?_, fun l hl w hw => ?_⟩
    · rw [e_nv] at hl; rw [hpres.wnext, hpres.whead]; exact hch_wc l hl
    · rw [e_nv] at hl
      have hcl_sz : ∀ c, k6ClauseSize st' c = k6ClauseSize ks c := fun c => by
        unfold k6ClauseSize; rw [hpres.clSz]
      have hcl_off : ∀ c, k6ClauseOff st' c = k6ClauseOff ks c := fun c => by
        unfold k6ClauseOff; rw [hpres.clOff]
      have hcl_lits : ∀ c, k6ClauseLits st' c = k6ClauseLits ks c := fun c => by
        unfold k6ClauseLits; rw [hcl_off, hcl_sz, hpres.arena]
      rw [e_nv, e_nc, hcl_sz, hcl_off, hcl_lits, hpres.arena, hpres.wblit]
      exact hch_bnd l hl w hw
  have hsync' : K6TrailSynced st' := fun i hi => by
    rw [e_te] at hi
    have hi_ks : i < ks.trl_end.toNat := Nat.lt_of_lt_of_le hi hbt.te_le
    let l := (ks.trl[i]?.getD 0#32).toNat
    have hl_lt : l < 2 * ks.nv.toNat := hinv.assign.trl_lt l (k6_mem_trailLits_of_lt hi_ks htrl_len)
    have hkv := hbt.kept_var (l / 2) (by omega) ⟨i, hi, rfl⟩
    have hvals_old : ks.vals[l]? = some 1#32 ∧ ks.vals[l ^^^ 1]? = some 2#32 := by
      rcases hsync_below with rfl | hsy
      · have hl0 : ks.lvlArr[l / 2]?.getD 0#32 = 0#32 :=
          BitVec.eq_of_toNat_eq (Nat.eq_zero_of_le_zero (hkept_lvl i hi))
        have h0 := hinv.assign.lvl0_ok i hi_ks hl0; exact ⟨h0.1, h0.2.1⟩
      · exact hsy i hi_ks
    change st'.vals[(st'.trl[i]?.getD 0#32).toNat]? = some 1#32 ∧
      st'.vals[(st'.trl[i]?.getD 0#32).toNat ^^^ 1]? = some 2#32
    rw [e_trl, e_va]; change st.vals[l]? = some 1#32 ∧ st.vals[l ^^^ 1]? = some 2#32
    have hpair : st.vals[l]? = ks.vals[l]? ∧ st.vals[l ^^^ 1]? = ks.vals[l ^^^ 1]? := by
      rcases k6_nat_xor1_cases l with ⟨he, hx⟩ | ⟨he, hx⟩
      · exact ⟨by rw [he]; exact hkv.2.2.1, by rw [hx]; exact hkv.2.2.2⟩
      · exact ⟨by rw [he]; exact hkv.2.2.2, by rw [hx]; exact hkv.2.2.1⟩
    rw [hpair.1, hpair.2]; exact hvals_old
  have hba' : K6BaseAssignOk P st' := by
    refine ⟨by rw [e_te, e_nv]; exact Nat.le_trans hbt.te_le hinv.assign.trl_end_le,
      by rw [e_pr, e_te]; split <;> omega,
      by rw [e_un, e_te, e_nv]; exact hbt.unass_eq,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l hl; rw [e_nv] at hl; rw [e_va]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
      · have hkv := hbt.kept_var (l / 2) (by omega) hex
        rcases k6_nat_xor1_cases l with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he, hkv.2.2.1, ← he]; exact hinv.assign.vals_dom l hl
        · rw [he, hkv.2.2.2, ← he]; exact hinv.assign.vals_dom l hl
      · have hcv := hbt.cleared_var (l / 2) (by omega) hex
        rcases k6_nat_xor1_cases l with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he, hcv.2.2.1]; left; rfl
        · rw [he, hcv.2.2.2]; left; rfl
    · intro l hl; rw [e_nv] at hl; rw [e_va]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
      · have hkv := hbt.kept_var (l / 2) (by omega) hex
        have hpair : st.vals[l]? = ks.vals[l]? ∧ st.vals[l ^^^ 1]? = ks.vals[l ^^^ 1]? := by
          rcases k6_nat_xor1_cases l with ⟨he, hx⟩ | ⟨he, hx⟩
          · exact ⟨by rw [he]; exact hkv.2.2.1, by rw [hx]; exact hkv.2.2.2⟩
          · exact ⟨by rw [he]; exact hkv.2.2.2, by rw [hx]; exact hkv.2.2.1⟩
        rw [hpair.1, hpair.2]; exact hinv.assign.vals_neg_iff l hl
      · have hcv := hbt.cleared_var (l / 2) (by omega) hex
        have hpair : st.vals[l]? = some 0#32 ∧ st.vals[l ^^^ 1]? = some 0#32 := by
          rcases k6_nat_xor1_cases l with ⟨he, hx⟩ | ⟨he, hx⟩
          · exact ⟨by rw [he]; exact hcv.2.2.1, by rw [hx]; exact hcv.2.2.2⟩
          · exact ⟨by rw [he]; exact hcv.2.2.2, by rw [hx]; exact hcv.2.2.1⟩
        rw [hpair.1, hpair.2]; simp
    · intro l hl; rw [e_nv] at hl; rw [e_va, e_te, e_trl]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
      · refine ⟨fun _ => hex, fun _ => ?_⟩
        obtain ⟨i, hi, hiv⟩ := hex
        have hkv := hbt.kept_var (l / 2) (by omega) ⟨i, hi, hiv⟩
        have hnz := (hinv.assign.vals_nz_iff_trl l hl).mpr ⟨i, Nat.lt_of_lt_of_le hi hbt.te_le, hiv⟩
        rcases k6_nat_xor1_cases l with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he, hkv.2.2.1, ← he]; exact hnz
        · rw [he, hkv.2.2.2, ← he]; exact hnz
      · have hcv := hbt.cleared_var (l / 2) (by omega) hex
        refine ⟨fun hnz => absurd ?_ hnz, fun h => absurd h hex⟩
        rcases k6_nat_xor1_cases l with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he, hcv.2.2.1]; rfl
        · rw [he, hcv.2.2.2]; rfl
    · have hpf : k6TrailLits st' <+: k6TrailLits ks := by
        unfold k6TrailLits; rw [e_te, e_trl]
        exact List.IsPrefix.map BitVec.toNat (List.take_prefix_take_left hbt.te_le)
      exact hinv.assign.trl_nodup.sublist (hpf.map (· / 2)).sublist
    · intro l hl; rw [e_nv]
      have hpf : k6TrailLits st' <+: k6TrailLits ks := by
        unfold k6TrailLits; rw [e_te, e_trl]
        exact List.IsPrefix.map BitVec.toNat (List.take_prefix_take_left hbt.te_le)
      exact hinv.assign.trl_lt l (hpf.subset hl)
    · intro v hv; rw [e_nv] at hv; rw [e_la, e_lvl]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = v
      · obtain ⟨i, hi, rfl⟩ := hex
        rw [(hbt.kept_var _ hv ⟨i, hi, rfl⟩).1]; exact hkept_lvl i hi
      · rw [(hbt.cleared_var v hv hex).1]; simp
    · intro v hv hz; rw [e_nv] at hv; rw [e_va] at hz; rw [e_la, e_rs]
      by_cases hex : ∃ i < te.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = v
      · exfalso; obtain ⟨i, hi, hiv⟩ := hex
        have hkv := hbt.kept_var v hv ⟨i, hi, hiv⟩
        rw [hkv.2.2.1] at hz
        exact (hinv.assign.vals_nz_iff_trl (2 * v) (by omega)).mpr
          ⟨i, Nat.lt_of_lt_of_le hi hbt.te_le, by omega⟩ hz
      · have hcv := hbt.cleared_var v hv hex; rw [hcv.1, hcv.2.1]; exact ⟨rfl, rfl⟩
    · intro i j hij hj; rw [e_te] at hj; rw [e_la, e_trl]
      have hi_ks := Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hij hj) hbt.te_le
      have hj_ks := Nat.lt_of_lt_of_le hj hbt.te_le
      have hli := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hi_ks htrl_len)
      have hlj := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hj_ks htrl_len)
      rw [(hbt.kept_var _ (by omega) ⟨i, by omega, rfl⟩).1,
        (hbt.kept_var _ (by omega) ⟨j, hj, rfl⟩).1]
      exact hinv.assign.trl_lvl_mono i j hij hj_ks
    · intro i j hji hi hpos heq; rw [e_te] at hi
      rw [e_la, e_trl] at hpos heq; rw [e_trl, e_rs]
      have hi_ks := Nat.lt_of_lt_of_le hi hbt.te_le
      have hj_ks := Nat.lt_of_lt_of_le (Nat.lt_trans hji hi) hbt.te_le
      have hli := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hi_ks htrl_len)
      have hlj := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hj_ks htrl_len)
      have hki := hbt.kept_var _ (by omega) ⟨i, hi, rfl⟩
      have hkj := hbt.kept_var _ (by omega) ⟨j, Nat.lt_trans hji hi, rfl⟩
      rw [hki.1] at hpos heq; rw [hkj.1] at heq; rw [hki.2.1]
      exact hinv.assign.dec_earliest i j hji hi_ks hpos heq
    · intro i hi; dsimp only; intro hl0; rw [e_te] at hi
      have hi_ks := Nat.lt_of_lt_of_le hi hbt.te_le
      let l := (ks.trl[i]?.getD 0#32).toNat
      have hl_lt := hinv.assign.trl_lt l (k6_mem_trailLits_of_lt hi_ks htrl_len)
      have hkv := hbt.kept_var (l / 2) (by omega) ⟨i, hi, rfl⟩
      rw [e_la, e_trl] at hl0; change st.lvlArr[l / 2]?.getD 0#32 = 0#32 at hl0
      rw [hkv.1] at hl0
      have h0 := hinv.assign.lvl0_ok i hi_ks hl0
      have hsy := hsync' i (by rw [e_te]; exact hi)
      exact ⟨hsy.1, hsy.2, by rw [e_trl]; exact h0.2.2⟩
  have hre' : K6ReasonOk st' := fun i hi => by
    rw [e_te] at hi
    have hi_ks := Nat.lt_of_lt_of_le hi hbt.te_le
    let l := (ks.trl[i]?.getD 0#32).toNat
    have hl_lt := hinv.assign.trl_lt l (k6_mem_trailLits_of_lt hi_ks htrl_len)
    have hkv := hbt.kept_var (l / 2) (by omega) ⟨i, hi, rfl⟩
    change let l := (st'.trl[i]?.getD 0#32).toNat; let r := st'.rsn[l / 2]?.getD 0#32; _
    rw [e_trl, e_rs, hkv.2.1, e_nc]
    have hcl_eq : ∀ c, k6ClauseLits st' c = k6ClauseLits ks c := fun c => by
      unfold k6ClauseLits k6ClauseOff k6ClauseSize; rw [hpres.clOff, hpres.clSz, hpres.arena]
    rcases hinv.reasons i hi_ks with hnone | ⟨hr_lt, hmem, hoth⟩
    · exact Or.inl hnone
    · right; rw [hcl_eq]; exact ⟨hr_lt, hmem, hoth⟩
  refine ⟨⟨hsh', hcl', hw', hba', hre'⟩, hsync', e_lvl, by rw [e_te]; exact hbt.te_le, hpres, ?_⟩
  intro i hi; rw [e_te] at hi
  have hi_ks := Nat.lt_of_lt_of_le hi hbt.te_le
  have hl_lt := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hi_ks htrl_len)
  have hkv := hbt.kept_var _ (by omega) ⟨i, hi, rfl⟩
  rw [e_trl, e_rs, e_la, hkv.2.1, hkv.1]; exact ⟨rfl, rfl, hkept_lvl i hi⟩

theorem k6Init_finish_inv {L : K6Layout} {nv : BitVec 32} {st : K6State}
    (hsh : st.ShapesOk L) (hnv_le : nv.toNat ≤ L.maxV)
    (e_nv : st.nv = nv) (e_nc : st.nc = 0#32) (e_lvl : st.lvl = 0#32)
    (e_prop : st.prop = 0#32) (e_te : st.trl_end = 0#32) (e_un : st.unass = nv)
    (e_ac : st.acap = BitVec.ofNat 32 L.acap) (e_mv : st.max_v = BitVec.ofNat 32 L.maxV)
    (e_mo : st.max_orig = BitVec.ofNat 32 L.maxOrig) (e_mc : st.max_cl = BitVec.ofNat 32 L.maxCl)
    (e_al : st.alen = 0#32) (e_in : st.incons = 0#32) (e_na : st.nassump = 0#32)
    (e_nk : st.nkl = 0#32) (e_nn : st.nana = 0#32)
    (hvars : ∀ v < nv.toNat, st.lvlArr[v]? = some 0#32 ∧ st.rsn[v]? = some 0xFFFFFFFF#32 ∧
      st.flags[v]? = some 0#32)
    (hlits : ∀ l < 2 * nv.toNat, st.vals[l]? = some 0#32 ∧ st.whead[l]? = some 0xFFFFFFFF#32) :
    (∀ P, K6Inv L P st) ∧ K6TrailSynced st := by
  have hsync : K6TrailSynced st := fun i hi => by rw [e_te] at hi; simp at hi
  refine ⟨fun P => ⟨hsh, ?_, ?_, ?_, fun i hi => by rw [e_te] at hi; simp at hi⟩, hsync⟩
  · refine ⟨e_ac, e_mv, e_mo, e_mc, by rw [e_nv]; exact hnv_le, by rw [e_nc]; simp,
      by simp [e_al], by rw [e_na]; simp, by rw [e_nk]; simp, by rw [e_nn]; simp,
      fun cid hc => by rw [e_nc] at hc; simp at hc,
      fun _ _ _ hc => by rw [e_nc] at hc; simp at hc,
      fun hi => absurd e_in hi,
      fun i hi => by rw [e_na] at hi; simp at hi,
      fun v hv => by rw [e_nv] at hv; rw [(hvars v hv).2.2, Option.getD_some]; decide⟩
  · refine ⟨List.replicate (2 * nv.toNat) [], by rw [e_nv]; simp,
      by rw [List.flatten_replicate_nil]; exact List.nodup_nil, ?_, ?_⟩
    · intro l hl; rw [e_nv] at hl
      rw [(hlits l hl).2, Option.getD_some]
      simp only [List.getElem?_replicate, hl, ↓reduceIte, Option.getD_some]
      exact K5WChain.nil
    · intro l hl w hw; rw [e_nv] at hl
      simp only [List.getElem?_replicate, hl, ↓reduceIte, Option.getD_some] at hw
      cases hw
  · refine ⟨by simp [e_te], by simp [e_prop, e_te], by rw [e_un, e_te, e_nv]; simp,
      fun l hl => by rw [e_nv] at hl; rw [(hlits l hl).1]; left; rfl,
      fun l hl => by
        rw [e_nv] at hl
        have hnl : l ^^^ 1 < 2 * nv.toNat := by
          rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [(hlits l hl).1, (hlits (l ^^^ 1) hnl).1]; simp,
      fun l hl => by rw [e_nv] at hl; rw [(hlits l hl).1]; simp [e_te],
      by unfold k6TrailLits; rw [e_te]; simp,
      fun l hl => by unfold k6TrailLits at hl; rw [e_te] at hl; simp at hl,
      fun v hv => by rw [e_nv] at hv; rw [(hvars v hv).1, e_lvl]; simp,
      fun v hv _ => by rw [e_nv] at hv; rw [(hvars v hv).1, (hvars v hv).2.1]; exact ⟨rfl, rfl⟩,
      fun _ _ _ hj => by rw [e_te] at hj; simp at hj,
      fun _ _ _ hi => by rw [e_te] at hi; simp at hi,
      fun _ hi => by rw [e_te] at hi; simp at hi⟩

theorem k6AddClause_ge2_preserves {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {ar : List (BitVec 32)} {xs : List (BitVec 32)} {sz : BitVec 32}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    (hnc_lt : ks.nc.toNat < L.maxCl) (hsz2 : 2 ≤ sz.toNat) (hsz_max : sz.toNat < 2 ^ 28)
    (hsz_xs : sz.toNat ≤ xs.length) (hfit : ks.alen.toNat + sz.toNat ≤ L.acap)
    (har_len : ar.length = L.acap) (har_old : ∀ j < ks.alen.toNat, ar[j]? = ks.arena[j]?)
    (har_new : ∀ j < sz.toNat, ar[ks.alen.toNat + j]? = xs[j]?)
    (hxlits : ∀ j < sz.toNat, (xs[j]?.getD 0#32).toNat < 2 * ks.nv.toNat)
    (hent : SemEntails P ((xs.take sz.toNat).map BitVec.toNat)) :
    let stM := (((({ ks with arena := ar } : K6State).putHdr .alen (ks.alen + sz)).putArr
      .clOff ks.nc.toNat ks.alen).putArr .clSz ks.nc.toNat sz).putHdr .nc (ks.nc + 1#32)
    let ks' := k6WatchStep stM ks.nc (xs[0]'(by omega)) (xs[1]'(by omega))
    K6Inv L P ks' ∧ K6TrailSynced ks' ∧ ks'.lvl = ks.lvl ∧ ks'.nv = ks.nv ∧
    ks'.nassump = ks.nassump ∧ ks'.assump = ks.assump ∧ ks'.trl_end = ks.trl_end ∧
    ks'.unass = ks.unass ∧ ks'.incons = ks.incons ∧
    (∀ M, (∀ j < sz.toNat, (xs[j]?.getD 0#32).toNat < 2 * M) →
      K6LitsBounded M ks → K6LitsBounded M ks') := by
  intro stM ks'
  have hm := L.hmaxV; have hac := L.hacap
  have hnc_mc : ks.nc.toNat < L.maxCl := hnc_lt
  have hnc1 : (ks.nc + 1#32).toNat = ks.nc.toNat + 1 := by
    unfold K6Layout.maxCl at hnc_lt; bv_omega
  have hal1 : (ks.alen + sz).toNat = ks.alen.toNat + sz.toNat := by
    unfold dimacsBound at *; bv_omega
  have hsh_ar : ({ ks with arena := ar } : K6State).ShapesOk L :=
    { hinv.shapes with arena_len := har_len }
  have hshM : stM.ShapesOk L :=
    (((hsh_ar.putHdr .alen _).putArr .clOff _ _).putArr .clSz _ _).putHdr .nc _
  have hcl_old : ∀ c < ks.nc.toNat,
      k6ClauseOff stM c = k6ClauseOff ks c ∧ k6ClauseSize stM c = k6ClauseSize ks c ∧
      k6ClauseLits stM c = k6ClauseLits ks c := fun c hc => by
    have hoff : k6ClauseOff stM c = k6ClauseOff ks c := by
      unfold k6ClauseOff; dsimp only [stM]; k6_field; rw [List.getElem?_set_ne (by omega)]
    have hszc : k6ClauseSize stM c = k6ClauseSize ks c := by
      unfold k6ClauseSize; dsimp only [stM]; k6_field; rw [List.getElem?_set_ne (by omega)]
    have hwf := hinv.clauses.cl_wf c hc
    have hlits : k6ClauseLits stM c = k6ClauseLits ks c := by
      unfold k6ClauseLits; rw [hoff, hszc]
      have har_eq : stM.arena = ar := by dsimp only [stM]; k6_field
      rw [har_eq]; congr 1
      apply List.ext_getElem
      · simp [List.length_take, List.length_drop, har_len, hinv.shapes.arena_len]
      · intro k hk1 _
        have hk_sz : k < k6ClauseSize ks c := by simp [List.length_take] at hk1; omega
        have hal_le := hinv.clauses.alen_le
        have har0 := hinv.shapes.arena_len
        have hbd_al : k6ClauseOff ks c + k6ClauseSize ks c ≤ ks.alen.toNat := hwf.2.1
        simp only [List.getElem_take, List.getElem_drop]
        have hg := har_old (k6ClauseOff ks c + k) (by omega)
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hg
        exact Option.some.inj hg
    exact ⟨hoff, hszc, hlits⟩
  have hnew_off : k6ClauseOff stM ks.nc.toNat = ks.alen.toNat := by
    unfold k6ClauseOff; dsimp only [stM]; k6_field
    rw [List.getElem?_set_self (by rw [hinv.shapes.clOff_len]; exact hnc_mc), Option.getD_some]
  have hnew_sz : k6ClauseSize stM ks.nc.toNat = sz.toNat := by
    unfold k6ClauseSize; dsimp only [stM]; k6_field
    rw [List.getElem?_set_self (by rw [hinv.shapes.clSz_len]; exact hnc_mc), Option.getD_some]
  have hnew_lits : k6ClauseLits stM ks.nc.toNat = (xs.take sz.toNat).map BitVec.toNat := by
    unfold k6ClauseLits; rw [hnew_off, hnew_sz]
    have har_eq : stM.arena = ar := by dsimp only [stM]; k6_field
    rw [har_eq]; congr 1
    apply List.ext_getElem
    · simp [List.length_take, List.length_drop, har_len]; omega
    · intro k hk1 _
      have hk_sz : k < sz.toNat := by simp [List.length_take] at hk1; omega
      simp only [List.getElem_take, List.getElem_drop]
      have hg := har_new k hk_sz
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hg
      exact Option.some.inj hg
  have hks'_ar : ks'.arena = ar := by
    dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
  have hks'_nc : ks'.nc = ks.nc + 1#32 := by
    dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
  have hks'_nv : ks'.nv = ks.nv := by
    dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
  have hks'_al : ks'.alen = ks.alen + sz := by
    dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
  have hcl' : K6ClausesOk L P ks' := by
    refine ⟨by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]
               k6_field; exact hinv.clauses.acap_eq,
      by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv.clauses.max_v_eq,
      by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv.clauses.max_orig_eq,
      by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv.clauses.max_cl_eq,
      by rw [hks'_nv]; exact hinv.clauses.nv_le, by rw [hks'_nc, hnc1]; omega,
      by rw [hks'_al, hal1]; exact hfit,
      by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv.clauses.nassump_le,
      by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv.clauses.nkl_le,
      by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv.clauses.nana_le,
      ?_, ?_,
      by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv.clauses.incons_ok,
      by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv.clauses.assump_ok,
      by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field; exact hinv.clauses.flags_clean⟩
    · intro cid hc; rw [hks'_nc, hnc1] at hc
      have heq_cl : k6ClauseOff ks' cid = k6ClauseOff stM cid ∧
          k6ClauseSize ks' cid = k6ClauseSize stM cid ∧
          k6ClauseLits ks' cid = k6ClauseLits stM cid := ⟨rfl, rfl, rfl⟩
      rw [heq_cl.1, heq_cl.2.1, heq_cl.2.2, hks'_al, hal1, hks'_nv]
      by_cases hcid : cid = ks.nc.toNat
      · subst hcid; rw [hnew_off, hnew_sz, hnew_lits]
        refine ⟨hsz2, Nat.le_refl _, fun l hl => ?_, hent⟩
        rw [List.mem_map] at hl; obtain ⟨b, hb, rfl⟩ := hl
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
        have hj_sz : j < sz.toNat := by simp [List.length_take] at hj; omega
        simp only [List.getElem_take]
        have hxj := hxlits j hj_sz
        rwa [List.getElem?_eq_getElem (by omega : j < xs.length), Option.getD_some] at hxj
      · have hlt : cid < ks.nc.toNat := by omega
        obtain ⟨ho, hs, hl⟩ := hcl_old cid hlt
        rw [ho, hs, hl]; have hw := hinv.clauses.cl_wf cid hlt
        exact ⟨hw.1, by omega, hw.2.2.1, hw.2.2.2⟩
    · intro c1 c2 h12 h2; rw [hks'_nc, hnc1] at h2
      change k6ClauseOff stM c1 + k6ClauseSize stM c1 ≤ k6ClauseOff stM c2
      have ho1 := hcl_old c1 (by omega)
      rw [ho1.1, ho1.2.1]
      by_cases h2e : c2 = ks.nc.toNat
      · subst h2e; rw [hnew_off]; exact (hinv.clauses.cl_wf c1 (by omega)).2.1
      · have ho2 := hcl_old c2 (by omega); rw [ho2.1]
        exact hinv.clauses.cl_mono c1 c2 h12 (by omega)
  have hwM : K6WatchesOk stM := by
    obtain ⟨chains, hlen, hnd, hwc, hbnd⟩ := hinv.watches
    refine ⟨chains, by dsimp only [stM]; k6_field; exact hlen, hnd,
      by dsimp only [stM]; k6_field; exact hwc, fun l hl w hw => ?_⟩
    have hl' : l < 2 * ks.nv.toNat := by revert hl; dsimp only [stM]; k6_field; exact id
    obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ := hbnd l hl' w hw
    have ho := hcl_old (w / 2) (by omega)
    have har_get : stM.arena[k6ClauseOff ks (w / 2) + w % 2]? =
        ks.arena[k6ClauseOff ks (w / 2) + w % 2]? := by
      have har_eq : stM.arena = ar := by dsimp only [stM]; k6_field
      rw [har_eq]; have hwf := hinv.clauses.cl_wf (w / 2) (by omega)
      exact har_old _ (by omega)
    have har_get1 : stM.arena[k6ClauseOff ks (w / 2) + (w % 2 ^^^ 1)]? =
        ks.arena[k6ClauseOff ks (w / 2) + (w % 2 ^^^ 1)]? := by
      have har_eq : stM.arena = ar := by dsimp only [stM]; k6_field
      rw [har_eq]; have hwf := hinv.clauses.cl_wf (w / 2) (by omega)
      rcases Nat.mod_two_eq_zero_or_one w with hm0 | hm1
      · rw [hm0, show (0 ^^^ 1 : Nat) = 1 from by decide]; exact har_old _ (by omega)
      · rw [hm1, show (1 ^^^ 1 : Nat) = 0 from by decide]; exact har_old _ (by omega)
    refine ⟨by dsimp only [stM]; k6_field; rw [hnc1]; omega,
      by rw [ho.2.1]; exact hw2, by rw [ho.1, har_get]; exact hw3,
      by dsimp only [stM]; k6_field; exact hw4,
      by rw [ho.2.2]; dsimp only [stM]; k6_field; exact hw5,
      by rw [ho.2.1]; dsimp only [stM]; k6_field; exact hw6,
      fun h2 => by
        rw [ho.2.1] at h2; rw [ho.1, har_get1]
        dsimp only [stM]; k6_field; exact hw7 h2⟩
  have hl0_lt : (xs[0]'(by omega)).toNat < 2 * stM.nv.toNat := by
    have h0 := hxlits 0 (by omega); rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
    dsimp only [stM]; k6_field; exact h0
  have hl1_lt : (xs[1]'(by omega)).toNat < 2 * stM.nv.toNat := by
    have h1 := hxlits 1 (by omega); rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
    dsimp only [stM]; k6_field; exact h1
  have hl0_mem : (xs[0]'(by omega)).toNat ∈ k6ClauseLits stM ks.nc.toNat := by
    rw [hnew_lits, List.mem_map]; refine ⟨xs[0]'(by omega), ?_, rfl⟩
    rw [List.mem_take_iff_getElem]; exact ⟨0, by omega, by simp⟩
  have hl1_mem : (xs[1]'(by omega)).toNat ∈ k6ClauseLits stM ks.nc.toNat := by
    rw [hnew_lits, List.mem_map]; refine ⟨xs[1]'(by omega), ?_, rfl⟩
    rw [List.mem_take_iff_getElem]; exact ⟨1, by omega, by simp⟩
  have hw' : K6WatchesOk ks' :=
    k6WatchStep_preserves_watches hshM hwM
      (by dsimp only [stM]; k6_field; rw [hnc1]; omega)
      (by dsimp only [stM]; k6_field; rw [hnc1]; omega)
      (by dsimp only [stM]; k6_field; exact hinv.clauses.nv_le)
      hl0_lt hl1_lt (by rw [hnew_sz]; exact hsz2) hl0_mem hl1_mem
      (by rw [hnew_off]; have har_eq : stM.arena = ar := by dsimp only [stM]; k6_field
          have h0 := har_new 0 (by omega); rw [Nat.add_zero] at h0
          rw [har_eq, h0, List.getElem?_eq_getElem (by omega), Option.getD_some])
      (by rw [hnew_off]; have har_eq : stM.arena = ar := by dsimp only [stM]; k6_field
          rw [har_eq, har_new 1 (by omega), List.getElem?_eq_getElem (by omega), Option.getD_some])
      (fun chains hclen _ hwc => by
        obtain ⟨ch0, h0len, _, h0wc, h0bnd⟩ := hinv.watches
        have hwn_eq : stM.wnext = ks.wnext := by dsimp only [stM]; k6_field
        have hwh_eq : stM.whead = ks.whead := by dsimp only [stM]; k6_field
        have hnv_eq : stM.nv = ks.nv := by dsimp only [stM]; k6_field
        have hcheq : chains = ch0 := by
          apply List.ext_getElem (by rw [hclen, hnv_eq, h0len])
          intro x hx1 hx2
          have hx_nv : x < 2 * ks.nv.toNat := by omega
          have hc1 := hwc x (by rw [hnv_eq]; exact hx_nv)
          have hc2 := h0wc x hx_nv
          rw [hwn_eq, hwh_eq, List.getElem?_eq_getElem hx1, Option.getD_some] at hc1
          rw [List.getElem?_eq_getElem hx2, Option.getD_some] at hc2
          refine k6_wchain_unique (by rw [hinv.shapes.wnext_len]
                                      unfold K6Layout.maxCl; omega) hc1 hc2
        rw [hcheq]; constructor <;> intro hmem <;>
          (obtain ⟨ch, hch_m, hw_m⟩ := List.mem_flatten.mp hmem
           obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem hch_m
           have hb := h0bnd x (by omega) _ (by simpa [List.getElem?_eq_getElem hx] using hw_m)
           omega))
  have hba' : K6BaseAssignOk P ks' := by
    have h1 : ks'.trl_end = ks.trl_end := by
      dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h2 : ks'.prop = ks.prop := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h3 : ks'.unass = ks.unass := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h4 : ks'.vals = ks.vals := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h5 : ks'.trl = ks.trl := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h6 : ks'.lvl = ks.lvl := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h7 : ks'.lvlArr = ks.lvlArr := by
      dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h8 : ks'.rsn = ks.rsn := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    exact ⟨by rw [h1, hks'_nv]; exact hinv.assign.trl_end_le,
      by rw [h2, h1]; exact hinv.assign.prop_le,
      by rw [h3, h1, hks'_nv]; exact hinv.assign.unass_eq,
      by rw [hks'_nv, h4]; exact hinv.assign.vals_dom,
      by rw [hks'_nv, h4]; exact hinv.assign.vals_neg_iff,
      by rw [hks'_nv, h4, h1, h5]; exact hinv.assign.vals_nz_iff_trl,
      by unfold k6TrailLits; rw [h1, h5]; exact hinv.assign.trl_nodup,
      by unfold k6TrailLits; rw [hks'_nv, h1, h5]; exact hinv.assign.trl_lt,
      by rw [hks'_nv, h7, h6]; exact hinv.assign.trl_lvl_le,
      by rw [hks'_nv, h4, h7, h8]; exact hinv.assign.unass_lvl_zero,
      by rw [h1, h7, h5]; exact hinv.assign.trl_lvl_mono,
      by rw [h1, h7, h5, h8]; exact hinv.assign.dec_earliest,
      by rw [h1, h5, h7, h4]; exact hinv.assign.lvl0_ok⟩
  have hre' : K6ReasonOk ks' := fun i hi => by
    have h1 : ks'.trl_end = ks.trl_end := by
      dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h5 : ks'.trl = ks.trl := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h8 : ks'.rsn = ks.rsn := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    rw [h1] at hi
    change let l := (ks'.trl[i]?.getD 0#32).toNat; let r := ks'.rsn[l / 2]?.getD 0xFFFFFFFF#32; _
    rw [h5, h8, hks'_nc]
    rcases hinv.reasons i hi with hnone | ⟨hr_lt, hmem, hoth⟩
    · exact Or.inl hnone
    · right; have ho := hcl_old _ hr_lt
      have hl_eq :
          k6ClauseLits ks' (ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat =
          k6ClauseLits ks (ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat :=
        ho.2.2
      rw [hnc1, hl_eq]; exact ⟨by omega, hmem, hoth⟩
  have hsync' : K6TrailSynced ks' := by
    have h1 : ks'.trl_end = ks.trl_end := by
      dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h4 : ks'.vals = ks.vals := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    have h5 : ks'.trl = ks.trl := by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field
    intro i hi; rw [h1] at hi; unfold K6TrailSynced at hsync
    change ks'.vals[(ks'.trl[i]?.getD 0#32).toNat]? = some 1#32 ∧
      ks'.vals[(ks'.trl[i]?.getD 0#32).toNat ^^^ 1]? = some 2#32
    rw [h4, h5]; exact hsync i hi
  have hlb' : ∀ M, (∀ j < sz.toNat, (xs[j]?.getD 0#32).toNat < 2 * M) →
      K6LitsBounded M ks → K6LitsBounded M ks' := fun M hxsM hM => by
    have hnc4 : ks.nc.toNat < 4 * L.maxV := hnc_lt
    have hxs1 : 1 < xs.length := by omega
    constructor
    · intro cid hcid l hl
      rw [hks'_nc, hnc1] at hcid
      have heq_cl : k6ClauseLits ks' cid = k6ClauseLits stM cid := rfl
      rw [heq_cl] at hl
      by_cases hc : cid = ks.nc.toNat
      · subst hc; rw [hnew_lits] at hl
        rw [List.mem_map] at hl; obtain ⟨b, hb, rfl⟩ := hl
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
        have hj_sz : j < sz.toNat := by simp [List.length_take] at hj; omega
        simp only [List.getElem_take]
        have hx := hxsM j hj_sz
        rwa [List.getElem?_eq_getElem (by omega : j < xs.length), Option.getD_some] at hx
      · rw [(hcl_old cid (by omega)).2.2] at hl; exact hM.1 cid (by omega) l hl
    · intro w hw; rw [hks'_nc, hnc1] at hw
      have hw0 := k6_bv32_cid_w0 hnc_lt (by unfold K6Layout.maxCl; omega)
      have hw1 := k6_bv32_cid_w1 hnc_lt (by unfold K6Layout.maxCl; omega)
      let bf : BitVec 32 := if (stM.clSz[ks.nc.toNat]?.getD 0#32).toNat = 2 then 0x80000000#32
        else 0#32
      have hwb_eq : ks'.wblit =
          (ks.wblit.set (2 * ks.nc.toNat) ((xs[1]'(by omega)) ||| bf)).set
            (2 * ks.nc.toNat + 1) ((xs[0]'(by omega)) ||| bf) := by
        dsimp only [ks', k6WatchStep, k6WatchStep0, bf]
        rw [hw0.1, hw1.1]; dsimp only [stM]; k6_field
      have h0_lt31 : (xs[0]'(by omega)).toNat < 2 ^ 31 := by
        have hx0 := hxlits 0 (by omega); have hnv_le := hinv.clauses.nv_le
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hx0; omega
      have h1_lt31 : (xs[1]'(by omega)).toNat < 2 ^ 31 := by
        have hx1 := hxlits 1 (by omega); have hnv_le := hinv.clauses.nv_le
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hx1; omega
      have hbf_m0 : ((xs[0]'(by omega)) ||| bf) &&& 0x7FFFFFFF#32 = xs[0]'(by omega) := by
        dsimp only [bf]; split
        · exact (k6_bv32_or_bin_mask h0_lt31).1
        · rw [BitVec.or_zero]; exact (k6_bv32_lt31_and_mask h0_lt31).1
      have hbf_m1 : ((xs[1]'(by omega)) ||| bf) &&& 0x7FFFFFFF#32 = xs[1]'(by omega) := by
        dsimp only [bf]; split
        · exact (k6_bv32_or_bin_mask h1_lt31).1
        · rw [BitVec.or_zero]; exact (k6_bv32_lt31_and_mask h1_lt31).1
      rw [hwb_eq]
      by_cases h1 : w = 2 * ks.nc.toNat + 1
      · subst h1
        rw [List.getElem?_set_self (by
          simp only [List.length_set, hinv.shapes.wblit_len]; unfold K6Layout.maxCl; omega),
          Option.getD_some, hbf_m0]
        have hx := hxsM 0 (by omega)
        rwa [List.getElem?_eq_getElem (by omega : 0 < xs.length), Option.getD_some] at hx
      · rw [List.getElem?_set_ne (Ne.symm h1)]
        by_cases h0 : w = 2 * ks.nc.toNat
        · subst h0
          rw [List.getElem?_set_self (by rw [hinv.shapes.wblit_len]; unfold K6Layout.maxCl; omega),
            Option.getD_some, hbf_m1]
          have hx := hxsM 1 (by omega)
          rwa [List.getElem?_eq_getElem (by omega : 1 < xs.length), Option.getD_some] at hx
        · rw [List.getElem?_set_ne (Ne.symm h0)]; exact hM.2 w (by omega)
  exact ⟨⟨k6WatchStep_preserves_shapes hshM ks.nc (xs[0]'(by omega)) (xs[1]'(by omega)),
    hcl', hw', hba', hre'⟩, hsync',
    by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field, hks'_nv,
    by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field,
    by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field,
    by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field,
    by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field,
    by dsimp only [ks', k6WatchStep, k6WatchStep0, stM]; k6_field, hlb'⟩

/-! ## 4. Parametric `(Γ : Env)` `Func.wp` Proofs (`5/39`) -/

/-- `1/39`: Parametric `Func.wp` proof for `full_m6_max_v`. -/
theorem full_m6_max_v_wp (Γ : Env) :
    ∀ args m Q X, m6MaxVSpec args m Q X → Func.wp Γ full_m6_max_v_body args m Q X := by
  rintro ⟨cap, ⟨⟩⟩ m Q X hQ
  have hbv := k6MaxV_bv64_eq cap.isLt
  have hcap : BitVec.ofNat 64 cap.toNat = cap := BitVec.eq_of_toNat_eq (by simp)
  dsimp only at hbv; rw [hcap] at hbv
  rw [show (0#64 : BitVec 64) = 0 from rfl, show (512#64 : BitVec 64) = 512 from rfl,
    show (1312#64 : BitVec 64) = 1312 from rfl, show (45#64 : BitVec 64) = 45 from rfl,
    show (8192#64 : BitVec 64) = 8192 from rfl, show (24576#64 : BitVec 64) = 24576 from rfl,
    show (524288#64 : BitVec 64) = 524288 from rfl,
    show (0xFFFFFFFFFFFFFFC0#64 : BitVec 64) = 18446744073709551552 from rfl] at hbv
  dsimp only [m6MaxVSpec] at hQ; rw [← hbv] at hQ
  c0_hsteps! <;>
    exact Eq.mp (congrArg (fun v => Q (v, ()) m) (by
      repeat (first | rfl | bv_omega | split))) hQ

/-- `2/39`: Parametric `Func.wp` proof for `full_k6_add_ticks`. -/
theorem full_k6_add_ticks_wp (Γ : Env) :
    ∀ args m Q X, k6AddTicksSpec args m Q X → Func.wp Γ full_k6_add_ticks_body args m Q X := by
  rintro ⟨kPtr, delta, ⟨⟩⟩ m Q X ⟨L, ks, R, hsh, hm, hQ⟩
  have hmA := k6Mem_to_amem hsh hm; clear hm
  c0_hsteps! <;> (obtain ⟨_, hm'⟩ := k6MemA_to_mem hm; exact hQ _ _ hm')

/-- `3/39`: Parametric `Func.wp` proof for `full_k6_watch`. -/
theorem full_k6_watch_wp (Γ : Env) :
    ∀ args m Q X, k6WatchSpec args m Q X → Func.wp Γ full_k6_watch_body args m Q X := by
  rintro ⟨kPtr, cid, l0, l1, ⟨⟩⟩ m Q X ⟨L, ks, R, hsh, hmv, hcid, hl0, hl1, hm, hQ⟩
  have hmc : L.maxCl ≤ 32768 := by have := L.hmaxV; unfold K6Layout.maxCl; omega
  have h0 := k6_bv32_cid_w0 hcid hmc
  have h1 := k6_bv32_cid_w1 hcid hmc
  have hw0_len : (cid <<< (1 : Nat)).toNat < sz2Cl L := by
    unfold sz2Cl K6Layout.maxCl at *; omega
  have hw1_len : ((cid <<< (1 : Nat)) ||| 1#32).toNat < sz2Cl L := by
    unfold sz2Cl K6Layout.maxCl at *; omega
  have hcid_len : cid.toNat < szCl L := by unfold szCl; exact hcid
  have hl0_len : l0.toNat < sz2V L := by unfold sz2V; exact hl0
  have hl1_len : l1.toNat < sz2V L := by unfold sz2V; exact hl1
  have hmA := k6Mem_to_amem hsh hm; clear hm
  c0_hsteps_nogrp
  rw [hmv]
  c0_hsteps!
  · obtain ⟨_, hm'⟩ := k6MemA_to_mem hm
    refine hQ _ (Eq.mp (congrArg (fun x => (K6Mem L kPtr x ⋆ R) _) ?_) hm')
    have hsz2 : (ks.clSz[cid.toNat]?.getD 0#32).toNat = 2 := by bv_omega
    dsimp only [k6WatchStep, k6WatchStep0]; simp only [hsz2, ite_true]; k6_ext
  · obtain ⟨_, hm'⟩ := k6MemA_to_mem hm
    refine hQ _ (Eq.mp (congrArg (fun x => (K6Mem L kPtr x ⋆ R) _) ?_) hm')
    dsimp only [k6WatchStep, k6WatchStep0]
    have hne : (ks.clSz[cid.toNat]?.getD 0#32).toNat ≠ 2 := by bv_omega
    simp only [hne, ite_false]; k6_ext

/-- `4/39`: Parametric `Func.wp` proof for `full_k6_assign`. -/
theorem full_k6_assign_wp (Γ : Env) :
    ∀ args m Q X, k6AssignSpec args m Q X → Func.wp Γ full_k6_assign_body args m Q X := by
  rintro ⟨kPtr, lit, rsn, ⟨⟩⟩ m Q X ⟨L, ks, R, hsh, hmv, hlit, hte, hm, hQ⟩
  obtain ⟨hv_eq, hv_lt⟩ := k6_bv32_div2_lt hlit
  obtain ⟨hn_eq, hn_lt⟩ := k6_bv32_xor1_lt hlit
  have hl_len : lit.toNat < sz2V L := by unfold sz2V; exact hlit
  have hnl_len : (lit ^^^ 1#32).toNat < sz2V L := by unfold sz2V; exact hn_lt
  have hv_len : (lit >>> (1 : Nat)).toNat < szV L := by unfold szV; exact hv_lt
  have hte_len : ks.trl_end.toNat < szV L := by unfold szV; exact hte
  have hmA := k6Mem_to_amem hsh hm; clear hm
  c0_hsteps_nogrp
  rw [hmv]
  c0_hsteps_nogrp
  let ksPre := ((((((ks.putArr .vals lit.toNat 1#32).putArr .vals (lit ^^^ 1#32).toNat 2#32).putArr
    .lvlArr (lit >>> (1 : Nat)).toNat ks.lvl).putArr .rsn (lit >>> (1 : Nat)).toNat rsn).putArr
    .trl ks.trl_end.toNat lit).putHdr .trl_end (ks.trl_end + 1#32))
  let ksU := if (0 : BitVec 32).ult ks.unass then ksPre.putHdr .unass (ks.unass - 1#32) else ksPre
  have hult_iff : (0 : BitVec 32).ult ks.unass = true ↔ 0 < ks.unass.toNat := decide_eq_true_iff
  refine wp_join0 (fun m' => (K6MemA L kPtr ksU ⋆ R) m') ?_ ?_
  · intro J m' hm'
    c0_hsteps!
    · obtain ⟨_, hm''⟩ := k6MemA_to_mem hm
      refine hQ _ (Eq.mp (congrArg (fun x => (K6Mem L kPtr x ⋆ R) _) ?_) hm'')
      have hcond : (lit &&& 1#32) ≠ 0#32 := by
        simpa [K6PtrTactics.k6_bv32_one] using ‹_›
      by_cases hu : (0 : BitVec 32).ult ks.unass = true
      · have hu_nat := hult_iff.mp hu
        dsimp only [ksU, ksPre, k6AssignStep]
        simp only [hu, ite_true, hu_nat, hcond, ne_eq, not_false_eq_true]
        k6_ext <;> simp [hv_eq]
      · have hu_nat : ¬ 0 < ks.unass.toNat := fun hp => hu (hult_iff.mpr hp)
        dsimp only [ksU, ksPre, k6AssignStep]
        simp only [hu, ite_false, hu_nat, hcond, ne_eq, not_false_eq_true, ite_true]
        k6_ext <;> simp [hv_eq]
    · obtain ⟨_, hm''⟩ := k6MemA_to_mem hm
      refine hQ _ (Eq.mp (congrArg (fun x => (K6Mem L kPtr x ⋆ R) _) ?_) hm'')
      have hcond : (lit &&& 1#32) = 0#32 := by
        simpa [K6PtrTactics.k6_bv32_one] using ‹_›
      by_cases hu : (0 : BitVec 32).ult ks.unass = true
      · have hu_nat := hult_iff.mp hu
        dsimp only [ksU, ksPre, k6AssignStep]
        simp only [hu, ite_true, hu_nat, hcond, ne_eq, not_true_eq_false, ite_false]
        k6_ext <;> simp [hv_eq]
      · have hu_nat : ¬ 0 < ks.unass.toNat := fun hp => hu (hult_iff.mpr hp)
        dsimp only [ksU, ksPre, k6AssignStep]
        simp only [hu, ite_false, hu_nat, hcond, ne_eq, not_true_eq_false]
        k6_ext <;> simp [hv_eq]
  · intro J hJ
    c0_hsteps!
    · have hu : (0 : BitVec 32).ult ks.unass = true := by
        apply hult_iff.mpr; revert hc; k6_field; intro hc; bv_omega
      refine hJ _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm)
      dsimp only [ksU, ksPre]; simp only [hu, ite_true]
      k6_ext <;> (first | rfl | (simp only [hv_eq, K6PtrTactics.k6_bv32_one]; rfl))
    · have hu : (0 : BitVec 32).ult ks.unass = false :=
        Bool.eq_false_iff.mpr fun h => by
          have := hult_iff.mp h; revert hc; k6_field; intro hc; bv_omega
      refine hJ _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm)
      dsimp only [ksU, ksPre]; simp only [hu, Bool.false_eq_true, ite_false]
      k6_ext <;> (first | rfl | (simp only [hv_eq, K6PtrTactics.k6_bv32_one]; rfl))

private def K6MtfSt (L : K6Layout) (ks ks' : K6State) : Prop :=
  ks'.ShapesOk L ∧ ∃ qf ql qs qst qp qn qsa,
    ks' = { ks with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                    qprev := qp, qnext := qn, qstampArr := qsa }

private theorem K6MtfSt.base {L : K6Layout} {ks : K6State} (hsh : ks.ShapesOk L) :
    K6MtfSt L ks ks :=
  ⟨hsh, ks.qfirst, ks.qlast, ks.qsearch, ks.qstamp, ks.qprev, ks.qnext, ks.qstampArr,
    by cases ks; rfl⟩
private theorem K6MtfSt.nv_eq {L : K6Layout} {ks ks' : K6State} (r : K6MtfSt L ks ks') :
    ks'.nv = ks.nv := by rcases r.2 with ⟨_, _, _, _, _, _, _, rfl⟩; rfl
private theorem K6MtfSt.mv_eq {L : K6Layout} {ks ks' : K6State} (r : K6MtfSt L ks ks') :
    ks'.max_v = ks.max_v := by rcases r.2 with ⟨_, _, _, _, _, _, _, rfl⟩; rfl
private theorem K6MtfSt.putQf {L : K6Layout} {ks ks' : K6State} (r : K6MtfSt L ks ks')
    (v : BitVec 32) : K6MtfSt L ks (ks'.putHdr .qfirst v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putHdr .qfirst v, v, ql, qs, qst, qp, qn, qsa, rfl⟩
private theorem K6MtfSt.putQl {L : K6Layout} {ks ks' : K6State} (r : K6MtfSt L ks ks')
    (v : BitVec 32) : K6MtfSt L ks (ks'.putHdr .qlast v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putHdr .qlast v, qf, v, qs, qst, qp, qn, qsa, rfl⟩
private theorem K6MtfSt.putQs {L : K6Layout} {ks ks' : K6State} (r : K6MtfSt L ks ks')
    (v : BitVec 32) : K6MtfSt L ks (ks'.putHdr .qsearch v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putHdr .qsearch v, qf, ql, v, qst, qp, qn, qsa, rfl⟩
private theorem K6MtfSt.putQst {L : K6Layout} {ks ks' : K6State} (r : K6MtfSt L ks ks')
    (v : BitVec 32) : K6MtfSt L ks (ks'.putHdr .qstamp v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putHdr .qstamp v, qf, ql, qs, v, qp, qn, qsa, rfl⟩
private theorem K6MtfSt.putQp {L : K6Layout} {ks ks' : K6State} (r : K6MtfSt L ks ks')
    (i : Nat) (v : BitVec 32) : K6MtfSt L ks (ks'.putArr .qprev i v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putArr .qprev i v, qf, ql, qs, qst, qp.set i v, qn, qsa, rfl⟩
private theorem K6MtfSt.putQn {L : K6Layout} {ks ks' : K6State} (r : K6MtfSt L ks ks')
    (i : Nat) (v : BitVec 32) : K6MtfSt L ks (ks'.putArr .qnext i v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putArr .qnext i v, qf, ql, qs, qst, qp, qn.set i v, qsa, rfl⟩
private theorem K6MtfSt.putQsa {L : K6Layout} {ks ks' : K6State} (r : K6MtfSt L ks ks')
    (i : Nat) (v : BitVec 32) : K6MtfSt L ks (ks'.putArr .qstampArr i v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putArr .qstampArr i v, qf, ql, qs, qst, qp, qn, qsa.set i v, rfl⟩
private theorem K6MtfSt.finishA {L : K6Layout} {ks ks' : K6State} {kPtr : BitVec 64}
    {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post []}
    (hQ : ∀ qf' ql' qs' qst' qp' qn' qsa' m',
      let ks' : K6State := { ks with qfirst := qf', qlast := ql', qsearch := qs', qstamp := qst',
                                     qprev := qp', qnext := qn', qstampArr := qsa' }
      ks'.ShapesOk L → (K6Mem L kPtr ks' ⋆ R) m' → Q () m')
    (r : K6MtfSt L ks ks') (hm' : (K6MemA L kPtr ks' ⋆ R) m') : Q () m' := by
  obtain ⟨hsh, hm''⟩ := k6MemA_to_mem hm'
  rcases r with ⟨_, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact hQ qf ql qs qst qp qn qsa m' hsh hm''

/-- `5/39`: Parametric `Func.wp` proof for `full_k6_mtf`. -/
theorem full_k6_mtf_wp (Γ : Env) :
    ∀ args m Q X, k6MtfSpec args m Q X → Func.wp Γ full_k6_mtf_body args m Q X := by
  rintro ⟨kPtr, v, ⟨⟩⟩ m Q X ⟨L, ks, R, hsh, hmv, hnv, hm, hQ⟩
  have hmA := k6Mem_to_amem hsh hm; clear hm
  c0_hsteps_nogrp
  · exact hQ _ _ _ _ _ _ _ m hsh (k6MemA_to_mem hmA).2
  · exact hQ _ _ _ _ _ _ _ m hsh (k6MemA_to_mem hmA).2
  · have hv_lt : v.toNat < ks.nv.toNat := by bv_omega
    have hv_len : v.toNat < szV L := by unfold szV; omega
    have hv2_len : (v <<< (1 : Nat)).toNat < sz2V L := by
      have := K6PtrTactics.k6_shl1_toNat v; unfold sz2V; omega
    rw [hmv]
    c0_hsteps_nogrp
    let pv := ks.qprev[v.toNat]?.getD 0#32
    let nxt := ks.qnext[v.toNat]?.getD 0#32
    refine wp_join_state0 (α := K6State)
      (fun st m' => K6MtfSt L ks st ∧ (K6MemA L kPtr st ⋆ R) m') ?_ ?_
    · intro J1 ks1 m1 ⟨hr1, hm1⟩
      have hnv1 := hr1.nv_eq; have hmv1 := hr1.mv_eq
      c0_hsteps_nogrp
      refine wp_join_state0 (α := K6State)
        (fun st m' => K6MtfSt L ks st ∧ (K6MemA L kPtr st ⋆ R) m') ?_ ?_
      · intro J2 ks2 m2 ⟨hr2, hm2⟩
        have hnv2 := hr2.nv_eq; have hmv2 := hr2.mv_eq
        c0_hsteps_nogrp
        refine wp_join_state0 (α := K6State)
          (fun st m' => K6MtfSt L ks st ∧ (K6MemA L kPtr st ⋆ R) m') ?_ ?_
        · intro J3 ks3 m3 ⟨hr3, hm3⟩
          have hnv3 := hr3.nv_eq; have hmv3 := hr3.mv_eq
          c0_hsteps_nogrp
          let ol := ks3.qlast
          refine wp_join_state0 (α := K6State)
            (fun st m' => K6MtfSt L ks st ∧ (K6MemA L kPtr st ⋆ R) m') ?_ ?_
          · intro J4 ks4 m4 ⟨hr4, hm4⟩
            c0_hsteps_nogrp
            refine wp_join_state0 (α := K6State)
              (fun st m' => K6MtfSt L ks st ∧ (K6MemA L kPtr st ⋆ R) m') ?_ ?_
            · intro J5 ks5 m5 ⟨hr5, hm5⟩
              c0_hsteps!
              · exact (hr5.putQs v).finishA hQ hm
              · exact hr5.finishA hQ hm5
            · intro J5 hJ5
              c0_hsteps!
              · exact hJ5 _ _ ⟨(hr4.putQst _).putQsa _ _, hm⟩
              · exact hJ5 _ _ ⟨hr4, hm4⟩
          · intro J4 hJ4
            c0_hsteps_nogrp
            · c0_hsteps!
              exact hJ4 _ _ ⟨(((hr3.putQp v.toNat ol).putQn v.toNat 0xFFFFFFFF#32).putQl v).putQf
                v, hm⟩
            · have hol_len : ol.toNat < szV L := by
                have : ol.toNat < ks.nv.toNat := by dsimp only [ol]; rw [← hnv3]; bv_omega
                unfold szV; omega
              c0_hsteps!
              exact hJ4 _ _ ⟨(((hr3.putQp v.toNat ol).putQn v.toNat 0xFFFFFFFF#32).putQl v).putQn
                ol.toNat v, hm⟩
        · intro J3 hJ3
          c0_hsteps_nogrp
          · c0_hsteps!; exact hJ3 _ _ ⟨hr2.putQl pv, hm⟩
          · have hn_len : nxt.toNat < szV L := by
              have : nxt.toNat < ks.nv.toNat := by dsimp only [nxt]; rw [← hnv2]; bv_omega
              unfold szV; omega
            c0_hsteps!
            exact hJ3 _ _ ⟨hr2.putQp nxt.toNat pv, hm⟩
      · intro J2 hJ2
        c0_hsteps_nogrp
        · c0_hsteps!; exact hJ2 _ _ ⟨hr1.putQf nxt, hm⟩
        · have hp_len : pv.toNat < szV L := by
            have : pv.toNat < ks.nv.toNat := by dsimp only [pv]; rw [← hnv1]; bv_omega
            unfold szV; omega
          c0_hsteps!
          exact hJ2 _ _ ⟨hr1.putQn pv.toNat nxt, hm⟩
    · intro J1 hJ1
      c0_hsteps!
      · exact hJ1 _ _ ⟨(K6MtfSt.base hsh).putQs pv, hm⟩
      · exact hJ1 _ _ ⟨(K6MtfSt.base hsh).putQs nxt, hm⟩
      · exact hJ1 _ _ ⟨K6MtfSt.base hsh, hmA⟩
      · exact hJ1 _ _ ⟨K6MtfSt.base hsh, hmA⟩
      · exact hJ1 _ _ ⟨K6MtfSt.base hsh, hmA⟩

end LeanQbe.T.Examples.Kissat.FullM6Sweep
