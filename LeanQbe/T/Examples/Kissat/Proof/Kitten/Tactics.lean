/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec

/-!
# Scoped Pointer Tactics & Pure Array/BitVector Helpers (`Kissat.Proof.Kitten.Tactics`)

Provides `K6PtrTactics` (`bv_c0` pointer-base normalization, `c0_load`/`c0_store` dynamic-array
rules for all `17` `K6State` arrays, `k6_call`, `k6_maxV_call_step`, `k6Focus_hdr`,
`k6Unfocus_hdr`) and pure bitvector/list/nodup/swap helpers shared across Kitten proofs.

Zero legacy `Full*` imports; zero `@[expose]` on theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Kitten

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec

open K6MemATactics
open scoped K6MemATactics

/-! ## 1. Scoped Pointer Normalization & C0 Call Tactics (`K6PtrTactics`) -/

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

private theorem k6_ptr_sw_mul (L : K6Layout) (kPtr : BitVec 64) (c off : Nat)
    (hc : c ≤ 38) (hoff : off = 32 + c * L.maxV) :
    kPtr + ((32 : BitVec 32) + BitVec.ofNat 32 c * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * off) := by
  subst hoff
  have hm := L.hmaxV
  have hmul : c * L.maxV ≤ 38 * 8192 := Nat.mul_le_mul hc hm.2
  have hc32 : c % 2 ^ 32 = c := Nat.mod_eq_of_lt (by omega)
  have hv32 : L.maxV % 2 ^ 32 = L.maxV := Nat.mod_eq_of_lt (by omega)
  have hcm : (BitVec.ofNat 32 c * L.mv32).toNat = c * L.maxV := by
    unfold K6Layout.mv32
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hc32, hv32,
      Nat.mod_eq_of_lt (by omega)]
  have hadd : ((32 : BitVec 32) + BitVec.ofNat 32 c * L.mv32).toNat = 32 + c * L.maxV := by
    rw [BitVec.toNat_add, hcm, show (32 : BitVec 32).toNat = 32 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  congr 1; bv_omega

@[scoped bv_c0] theorem k6_ptr_base (L : K6Layout) (pScr : BitVec 64) :
    pScr + ((1280 : BitVec 32) + (L.mv32 <<< (1 : Nat))).setWidth 64 * 4 = L.kPtr pScr := by
  have hm := L.hmaxV
  unfold K6Layout.kPtr K6Layout.k6Base K6Layout.mv32
  congr 1; bv_omega

@[scoped bv_c0] theorem k6_ptr_base_bv (L : K6Layout) (pScr : BitVec 64) :
    pScr + ((1280 : BitVec 32) + (L.mv32 <<< 1#32)).setWidth 64 * 4 = L.kPtr pScr := by
  rw [show L.mv32 <<< 1#32 = L.mv32 <<< (1 : Nat) from rfl]
  exact k6_ptr_base L pScr

@[scoped bv_c0] theorem k6_ptr_lvl_sw (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + (32 : BitVec 32).setWidth 64 * 4 = kPtr + BitVec.ofNat 64 (4 * L.oLvl) :=
  k6_ptr_lvl L kPtr

@[scoped bv_c0] theorem k6_ptr_lvl_64 (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + 32#64 * 4 = kPtr + BitVec.ofNat 64 (4 * L.oLvl) :=
  k6_ptr_lvl L kPtr

@[scoped bv_c0] theorem k6_ptr_rsn (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + L.mv32).setWidth 64 * 4 = kPtr + BitVec.ofNat 64 (4 * L.oRsn) := by
  have hm := L.hmaxV
  unfold K6Layout.oRsn K6Layout.mv32
  congr 1; bv_omega

@[scoped bv_c0] theorem k6_ptr_qprev (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (2 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oQPrev) :=
  k6_ptr_sw_mul L kPtr 2 L.oQPrev (by decide) (by unfold K6Layout.oQPrev; omega)

@[scoped bv_c0] theorem k6_ptr_qnext (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (3 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oQNext) :=
  k6_ptr_sw_mul L kPtr 3 L.oQNext (by decide) (by unfold K6Layout.oQNext; omega)

@[scoped bv_c0] theorem k6_ptr_qstampArr (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (4 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oQStamp) :=
  k6_ptr_sw_mul L kPtr 4 L.oQStamp (by decide) (by unfold K6Layout.oQStamp; omega)

@[scoped bv_c0] theorem k6_ptr_trl (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (5 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oTrl) :=
  k6_ptr_sw_mul L kPtr 5 L.oTrl (by decide) (by unfold K6Layout.oTrl; omega)

@[scoped bv_c0] theorem k6_ptr_flags (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (6 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oFlags) :=
  k6_ptr_sw_mul L kPtr 6 L.oFlags (by decide) (by unfold K6Layout.oFlags; omega)

@[scoped bv_c0] theorem k6_ptr_ana (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (7 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oAna) :=
  k6_ptr_sw_mul L kPtr 7 L.oAna (by decide) (by unfold K6Layout.oAna; omega)

@[scoped bv_c0] theorem k6_ptr_kl (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (8 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oKl) :=
  k6_ptr_sw_mul L kPtr 8 L.oKl (by decide) (by unfold K6Layout.oKl; omega)

@[scoped bv_c0] theorem k6_ptr_assump (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (9 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oAssump) :=
  k6_ptr_sw_mul L kPtr 9 L.oAssump (by decide) (by unfold K6Layout.oAssump; omega)

@[scoped bv_c0] theorem k6_ptr_vals (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (10 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oVals) :=
  k6_ptr_sw_mul L kPtr 10 L.oVals (by decide) (by unfold K6Layout.oVals; omega)

@[scoped bv_c0] theorem k6_ptr_whead (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (12 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oWHead) :=
  k6_ptr_sw_mul L kPtr 12 L.oWHead (by decide) (by unfold K6Layout.oWHead; omega)

@[scoped bv_c0] theorem k6_ptr_wnext (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (14 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oWNext) :=
  k6_ptr_sw_mul L kPtr 14 L.oWNext (by decide) (by unfold K6Layout.oWNext; omega)

@[scoped bv_c0] theorem k6_ptr_wblit (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (22 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oWBlit) :=
  k6_ptr_sw_mul L kPtr 22 L.oWBlit (by decide) (by unfold K6Layout.oWBlit; rfl)

@[scoped bv_c0] theorem k6_ptr_clOff (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (30 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oClOff) :=
  k6_ptr_sw_mul L kPtr 30 L.oClOff (by decide) (by unfold K6Layout.oClOff; rfl)

@[scoped bv_c0] theorem k6_ptr_clSz (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (34 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oClSz) :=
  k6_ptr_sw_mul L kPtr 34 L.oClSz (by decide) (by unfold K6Layout.oClSz; rfl)

@[scoped bv_c0] theorem k6_ptr_arena (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + ((32 : BitVec 32) + (38 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oArena) :=
  k6_ptr_sw_mul L kPtr 38 L.oArena (by decide) (by unfold K6Layout.oArena; rfl)

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

theorem k6_vals_cons {t : Ty} {ts : List Ty} (a : Arg Val t) (as : Tup (Arg Val) ts) :
    @vals (t :: ts) (a, as) = (a.val, vals as) := rfl
theorem k6_vals_nil : vals (ts := []) () = () := rfl
theorem k6_val_var {t : Ty} (v : Val t) : (@Arg.var Val t v).val = v := rfl
theorem k6_val_imm {t : Ty} (v : Val t) : (@Arg.imm Val t v).val = v := rfl
theorem k6_fst {α β : Sort _} (a : α) (b : β) : (a, b).1 = a := rfl
theorem k6_snd {α β : Sort _} (a : α) (b : β) : (a, b).2 = b := rfl

scoped macro "k6_call " h:ident : tactic =>
  `(tactic| (refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_); dsimp only [vals, Arg.val]))

theorem k6_maxV_call_step {Γ : Env} {rs : List Ty}
    (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec)
    {n : Nat} (hn : n < 2 ^ 64) {Q : Post rs} {X : XPost}
    {k : Tup Val [i64] → Expr Val Cont rs} {m : Mem 64}
    (hk : wp Γ Q X (k (BitVec.ofNat 64 (k6MaxV n), ())) m) :
    wp Γ Q X (@Expr.call Val Cont rs "full_m6_max_v" [i64] [i64]
      (@Arg.var Val i64 (BitVec.ofNat 64 n), ()) k) m := by
  refine LeanQbe.T.wp_call_of_spec _ _ (hMaxV _ _ _ _ ?_)
  have h1 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  change wp Γ Q X (k (BitVec.ofNat 64 (k6MaxV (BitVec.ofNat 64 n).toNat), ())) m
  rw [h1]; exact hk

theorem k6Focus_hdr {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (K6Mem L kPtr ks ⋆ R) m) :
    (array (t := i32) kPtr (k6HdrWords ks) ⋆ ((K6Tree L kPtr ks).rest (k6Path 0) ⋆ R)) m :=
  SepTree.focus (t := K6Tree L kPtr ks) (k6Path 0) hm

theorem k6Unfocus_hdr {L : K6Layout} {kPtr : BitVec 64} {ks ks' : K6State}
    {hdr' : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (heq : ((K6Tree L kPtr ks).set (k6Path 0) (array (t := i32) kPtr hdr')).eval =
      K6Mem L kPtr ks')
    (hm : (array (t := i32) kPtr hdr' ⋆ ((K6Tree L kPtr ks).rest (k6Path 0) ⋆ R)) m) :
    (K6Mem L kPtr ks' ⋆ R) m :=
  SepTree.unfocus_eq (t := K6Tree L kPtr ks) (k6Path 0) heq hm

/-! ## 2. Pure BitVector, List, Nodup, & Slab Helpers -/

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
    apply BitVec.eq_of_getLsbD_eq; intro i _hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, Bool.and_or_distrib_right]
  have h2 : (x ||| 0x80000000#32) &&& 0x80000000#32 =
      (x &&& 0x80000000#32) ||| (0x80000000#32 &&& 0x80000000#32) := by
    apply BitVec.eq_of_getLsbD_eq; intro i _hi
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

theorem k6_arena_take2 {ar : List (BitVec 32)} {off acap : Nat} {a b : BitVec 32}
    (hlen : ar.length = acap) (h1 : off + 1 < acap) :
    ((((ar.set off a).set (off + 1) b).drop off).take 2).map BitVec.toNat =
      [a.toNat, b.toNat] := by
  have hlen0 : (ar.set off a).length = acap := by rw [List.length_set, hlen]
  have hlen1 : ((ar.set off a).set (off + 1) b).length = acap := by rw [List.length_set, hlen0]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_drop, hlen1,
      List.length_cons, List.length_nil]
    omega
  · intro k hk1 _
    have hk2 : k < 2 := by simp at hk1; omega
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · simp only [Nat.add_zero, List.getElem_cons_zero]
      rw [List.getElem_set_ne (by omega : off + 1 ≠ off), List.getElem_set_self]
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero]
      rw [List.getElem_set_self]

end LeanQbe.T.Examples.Kissat.Proof.Kitten

end
