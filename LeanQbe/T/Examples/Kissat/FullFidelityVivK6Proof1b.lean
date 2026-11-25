/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Cached-Pointer `full_k6_core_m8_fid_wp` (`FullFidelityVivK6Proof1b`)

Proves `full_k6_core_m8_fid_wp` (`G1-P2.1c`: all 8 Kitten sub-array pointers cached outside the
loops, plus inner `cl`/`rcl`/`ants` slice pointers) against exact
`FullM8CoreParity.m8K6CoreSpec` (`XPost := False`, `std3`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityVivK6

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

section K6CoreFid

private def FidCoreInv (scr0 : List (BitVec 32)) (nc : BitVec 32)
    (scr : List (BitVec 32)) : Prop :=
  M8K6BufOk scr ∧ scr.length = scr0.length ∧
  (∀ idx < scr0.length, (idx < 5760 ∨ (6016 ≤ idx ∧ idx < 12672) ∨ 13696 ≤ idx) →
    scr[idx]? = scr0[idx]?) ∧
  (∀ cid < nc.toNat,
    let m0 := scr0[12672 + cid]?.getD 0#32
    let m1 := scr[12672 + cid]?.getD 0#32
    (m1 &&& 0xFFFF#32) = (m0 &&& 0xFFFF#32) ∧
    (m1 &&& 0x40000000#32) = (m0 &&& 0x40000000#32))

private theorem fidCoreInv_set_meta {scr0 : List (BitVec 32)} {nc : BitVec 32}
    (hnc_le : nc.toNat ≤ 1024) {scr : List (BitVec 32)} (hik : FidCoreInv scr0 nc scr)
    {cid : Nat} (hcid : cid < nc.toNat) {v : BitVec 32}
    (hsz : (v &&& 0xFFFF#32) = ((scr[12672 + cid]?.getD 0#32) &&& 0xFFFF#32))
    (hlrn : (v &&& 0x40000000#32) = ((scr[12672 + cid]?.getD 0#32) &&& 0x40000000#32)) :
    FidCoreInv scr0 nc (scr.set (12672 + cid) v) := by
  refine ⟨m8K6BufOk_set_core_meta hik.1 (by omega) hsz hlrn, by simp [hik.2.1],
    fun idx hi hor => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.1 idx hi hor
  · by_cases heq : j = cid
    · subst heq
      have hk_l : 12672 + j < scr.length := by have := hik.1.base_ge; omega
      dsimp only
      rw [List.getElem?_set_self hk_l, Option.getD_some, hsz, hlrn]
      exact hik.2.2.2 j hj
    · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.2 j hj

private theorem fidCoreInv_set_flags {scr0 : List (BitVec 32)} {nc : BitVec 32}
    {scr : List (BitVec 32)} (hik : FidCoreInv scr0 nc scr)
    {v : Nat} (hv : v < 256) (val : BitVec 32) :
    FidCoreInv scr0 nc (scr.set (5760 + v) val) := by
  refine ⟨m8K6BufOk_set_flags hik.1 hv val, by simp [hik.2.1],
    fun idx hi hor => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.1 idx hi hor
  · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.2 j hj

private def fidFullMemNoScr (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
  FullScrMetaArrs c s.scratch ⋆
  array (t := i32) c.pDelayed s.scratch.delayed ⋆
  array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
  array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆ c.pad

private theorem fid_fullMem_eq_scr (c : FullCfg) (s : FullState) (scr : List (BitVec 32)) :
    FullMem c { s with scratch := { s.scratch with scratch_buf := scr } } =
      (array (t := i32) c.pScratchBuf scr ⋆ fidFullMemNoScr c s) := by
  unfold FullMem FullScratchArrays FullScrDynArrs fidFullMemNoScr
  ac_rfl

private theorem scr_addr_off (pScr : BitVec 64) (K : Nat) (i : BitVec 32) :
    (pScr + BitVec.ofNat 64 (4 * K)) + i.setWidth 64 * 4 =
      pScr + BitVec.ofNat 64 (4 * (K + i.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  have h4 : (4 : BitVec 64).toNat = 4 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth, h4, Nat.mod_eq_of_lt (Nat.lt_trans i.isLt (by decide : 2 ^ 32 < 2 ^ 64))]
  rw [Nat.mul_add, Nat.add_mod_mod, Nat.mod_add_mod]
  omega

private theorem scr_addr_off2 (pScr : BitVec 64) (K : Nat) (off j : BitVec 32) :
    ((pScr + BitVec.ofNat 64 (4 * K)) + off.setWidth 64 * 4) + j.setWidth 64 * 4 =
      pScr + BitVec.ofNat 64 (4 * (K + off.toNat + j.toNat)) := by
  rw [scr_addr_off]
  apply BitVec.eq_of_toNat_eq
  have h4 : (4 : BitVec 64).toNat = 4 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth, h4, Nat.mod_eq_of_lt (Nat.lt_trans j.isLt (by decide : 2 ^ 32 < 2 ^ 64))]
  rw [Nat.mul_add, Nat.mul_add, Nat.add_mod_mod, Nat.mod_add_mod]
  omega

private theorem scr_addr_off_mul (pScr : BitVec 64) (K : Nat) (hK : K < 2 ^ 32) (i : BitVec 32) :
    (pScr + BitVec.ofNat 64 K * 4) + i.setWidth 64 * 4 =
      pScr + BitVec.ofNat 64 (4 * (K + i.toNat)) := by
  have h1 : BitVec.ofNat 64 K * 4 = BitVec.ofNat 64 (4 * K) := by
    apply BitVec.eq_of_toNat_eq
    have h4 : (4 : BitVec 64).toNat = 4 := rfl
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, h4]
    rw [Nat.mod_eq_of_lt (by omega : K < 2 ^ 64), Nat.mul_comm]
  rw [h1]; exact scr_addr_off pScr K i

private theorem scr_addr_off2_mul (pScr : BitVec 64) (K : Nat) (hK : K < 2 ^ 32)
    (off j : BitVec 32) :
    ((pScr + BitVec.ofNat 64 K * 4) + off.setWidth 64 * 4) + j.setWidth 64 * 4 =
      pScr + BitVec.ofNat 64 (4 * (K + off.toNat + j.toNat)) := by
  have h1 : BitVec.ofNat 64 K * 4 = BitVec.ofNat 64 (4 * K) := by
    apply BitVec.eq_of_toNat_eq
    have h4 : (4 : BitVec 64).toNat = 4 := rfl
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, h4]
    rw [Nat.mod_eq_of_lt (by omega : K < 2 ^ 64), Nat.mul_comm]
  rw [h1]; exact scr_addr_off2 pScr K off j

namespace K6CoreCachedTactics

@[scoped c0_load] theorem ld_scr_off {pScr : BitVec 64} {xs : List (BitVec 32)} {R : Mem 64 → Prop}
    {m : Mem 64} {K : Nat} {i : BitVec 32} (hK : K < 2 ^ 32) (hi : K + i.toNat < xs.length)
    (hm : (array (t := i32) pScr xs ⋆ R) m) :
    loadVal m i32 ((pScr + BitVec.ofNat 64 K * 4) + i.setWidth 64 * 4) =
      some (xs[K + i.toNat]'hi) := by
  rw [scr_addr_off_mul pScr K hK i]
  exact loadVal_array (t := i32) (by decide) hi hm

@[scoped c0_store] theorem st_scr_off {pScr : BitVec 64} {xs : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {K : Nat} {i : BitVec 32} (v : BitVec 32) (hK : K < 2 ^ 32)
    (hi : K + i.toNat < xs.length) (hm : (array (t := i32) pScr xs ⋆ R) m) :
    storeOk m i32 ((pScr + BitVec.ofNat 64 K * 4) + i.setWidth 64 * 4) ∧
      (array (t := i32) pScr (xs.set (K + i.toNat) v) ⋆ R)
        (storeMem m i32 ((pScr + BitVec.ofNat 64 K * 4) + i.setWidth 64 * 4) v) := by
  rw [scr_addr_off_mul pScr K hK i]
  exact store_array (t := i32) v (by decide) hi hm

@[scoped c0_load] theorem ld_arena2 {pScr : BitVec 64} {xs : List (BitVec 32)} {R : Mem 64 → Prop}
    {m : Mem 64} {K : Nat} {off j : BitVec 32} (hK : K < 2 ^ 32)
    (hi : K + off.toNat + j.toNat < xs.length) (hm : (array (t := i32) pScr xs ⋆ R) m) :
    loadVal m i32 (((pScr + BitVec.ofNat 64 K * 4) + off.setWidth 64 * 4) + j.setWidth 64 * 4) =
      some (xs[K + off.toNat + j.toNat]'hi) := by
  rw [scr_addr_off2_mul pScr K hK off j]
  exact loadVal_array (t := i32) (by decide) hi hm

end K6CoreCachedTactics

open scoped K6CoreCachedTactics

private theorem fid_bv32_lshr1_toNat (x : BitVec 32) :
    (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem fid_bv32_lshr1_bv_toNat (x : BitVec 32) :
    (x >>> (1 : BitVec 32)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem zext32_64_toNat (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat :=
  zext_toNat x (by decide)

/-- `full_k6_core_m8_fid` (`G1-P2.1c`: cached Kitten sub-array pointers) satisfies exact
`FullM8CoreParity.m8K6CoreSpec` parametrically in `Γ`. -/
theorem full_k6_core_m8_fid_wp (Γ : Env) :
    ∀ a m Q X, m8K6CoreSpec a m Q X →
      Func.wp Γ full_k6_core_m8_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hsc16, hok0, hm0, hQ⟩ := m8K6CoreSpec_elim hSpec
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hsc := c.hscr; unfold dimacsBound at hsc
  let scr := s.scratch.scratch_buf
  have hscr_l : scr.length = c.scratch_cap := hscr_len
  have hlen_ge := hok0.base_ge
  let nc := scr[4193]'(by rw [hscr_l]; omega)
  let nv := scr[4192]'(by rw [hscr_l]; omega)
  let acap := scr[4207]'(by rw [hscr_l]; omega)
  have h4192 : (4192#64).toNat < scr.length := by
    rw [hscr_l, show (4192#64).toNat = 4192 from rfl]; omega
  have h4193 : (4193#64).toNat < scr.length := by
    rw [hscr_l, show (4193#64).toNat = 4193 from rfl]; omega
  have h4207 : (4207#64).toNat < scr.length := by
    rw [hscr_l, show (4207#64).toNat = 4207 from rfl]; omega
  unfold Func.wp full_k6_core_m8_fid_body
  c0_hsplit
  · c0_hsteps!; exact hQ scr m0 hscr_len (fun _ _ _ => rfl) hok0 hm0
  · have hnc_le : nc.toNat ≤ 1024 :=
      Nat.le_of_not_lt (show ¬ 1024 < nc.toNat from by simpa [nc, scr] using hc)
    clear hc
    c0_hsplit
    · c0_hsteps!; exact hQ scr m0 hscr_len (fun _ _ _ => rfl) hok0 hm0
    · have hnv_le : nv.toNat ≤ 256 :=
        Nat.le_of_not_lt (show ¬ 256 < nv.toNat from by simpa [nv, scr] using hc)
      clear hc
      let invCore := FidCoreInv scr nc
      have invCore_set_meta := @fidCoreInv_set_meta scr nc hnc_le
      have invCore_set_flags := @fidCoreInv_set_flags scr nc
      let R' : Mem 64 → Prop := fidFullMemNoScr c s ⋆ R
      have hm0' : (array (t := i32) c.pScratchBuf scr ⋆ R') m0 := by
        have h := hm0
        change (FullMem c { s with scratch := { s.scratch with scratch_buf := scr } } ⋆ R) m0 at h
        rw [fid_fullMem_eq_scr, sep_assoc] at h; exact h
      have hInv_hdr : ∀ {scx : List (BitVec 32)} (hkx : invCore scx),
          scx[4193]'(by have := hkx.2.1; omega) = nc ∧
          scx[4207]'(by have := hkx.2.1; omega) = acap := by
        intro scx hkx
        have hlx := hkx.2.1
        have h1 := hkx.2.2.1 4193 (by omega) (Or.inl (by omega))
        have h15 := hkx.2.2.1 4207 (by omega) (Or.inl (by omega))
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1 h15
        exact ⟨Option.some.inj h1, Option.some.inj h15⟩
      have hInv_clause : ∀ {scx : List (BitVec 32)} (hkx : invCore scx),
          ∀ {cid : Nat} (hcid : cid < nc.toNat),
            let off := scx[11648 + cid]'(by have := hkx.2.1; omega)
            let mval := scx[12672 + cid]'(by have := hkx.2.1; omega)
            let aux := scx[13696 + cid]'(by have := hkx.2.1; omega)
            off.toNat + (mval &&& 0xFFFF#32).toNat ≤ acap.toNat ∧
            ((mval &&& 0x40000000#32) ≠ 0#32 →
              off.toNat + (mval &&& 0xFFFF#32).toNat + aux.toNat ≤ acap.toNat) ∧
            15744 + acap.toNat ≤ scx.length := by
        intro scx hkx cid hcid
        have hlx := hkx.2.1
        obtain ⟨hnc_x, hac_x⟩ := hInv_hdr hkx
        have hkcl := hkx.1.clause_ok (cid := cid) (by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hnc_x]; exact hcid)
        have hge := hkx.1.length_ge
        rw [List.getElem?_eq_getElem (by omega : 4207 < scx.length), Option.getD_some, hac_x] at hge
        rw [List.getElem?_eq_getElem (by omega : 11648 + cid < scx.length),
          List.getElem?_eq_getElem (by omega : 12672 + cid < scx.length),
          List.getElem?_eq_getElem (by omega : 13696 + cid < scx.length),
          List.getElem?_eq_getElem (by omega : 4207 < scx.length),
          Option.getD_some, Option.getD_some, Option.getD_some, Option.getD_some, hac_x] at hkcl
        exact ⟨hkcl.1, hkcl.2, hge⟩
      -- Loop 1: clear `KM_CORE` on `cl_meta[0 ..< nc)`
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i32])
        (fun rem (i, ()) mi => ∃ scri, invCore scri ∧ i.toNat ≤ nc.toNat ∧
          rem = nc.toNat - i.toNat ∧ (array (t := i32) c.pScratchBuf scri ⋆ R') mi)
        ?_ ?_
      · rintro L1 rem1 ⟨i1, ⟨⟩⟩ m1 hL1 ⟨sc1, hk1, hi1_le, rfl, hm1⟩
        have hk1_l := hk1.2.1
        c0_hsplit
        · have hi1_lt : i1.toNat < nc.toNat := hc; clear hc
          have hi1_s : (i1 + 1#32).toNat = i1.toNat + 1 := by c0_bound
          have hbd1 : 12672 + i1.toNat < sc1.length := by omega
          have hpres := m8_km_core_clear_pres (sc1[12672 + i1.toNat]'hbd1)
          c0_hsteps!
          exact hL1 (nc.toNat - (i1 + 1#32).toNat) (i1 + 1#32, ()) _ (by omega)
            ⟨_, invCore_set_meta hk1 hi1_lt
              (by rw [List.getElem?_eq_getElem hbd1, Option.getD_some]; exact hpres.1)
              (by rw [List.getElem?_eq_getElem hbd1, Option.getD_some]; exact hpres.2),
             by omega, rfl, hm⟩
        · clear hc
          have h4199_1 : (4199#64).toNat < sc1.length := by
            rw [hk1_l, show (4199#64).toNat = 4199 from rfl]; omega
          c0_hsteps_nogrp
          -- Join after `if (inc < nc)` block
          refine wp_join_group (ts := [i32])
            (fun (_, ()) mj => ∃ scj, invCore scj ∧ (array (t := i32) c.pScratchBuf scj ⋆ R') mj)
            ?_ ?_
          · -- Fixpoint loop: `while (changed && pass < nc)`
            rintro _ ⟨_, ⟨⟩⟩ mj ⟨scj, hkj, hmj⟩
            c0_hsteps_nogrp
            refine wp_loop_group (ts := [i32, .bool])
              (fun rem (pass, _ch, ()) mp => ∃ scp, invCore scp ∧ pass.toNat ≤ nc.toNat ∧
                rem = nc.toNat - pass.toNat ∧ (array (t := i32) c.pScratchBuf scp ⋆ R') mp)
              ?_ ?_
            · rintro Lp remp ⟨pass, ch, ⟨⟩⟩ mp hLp ⟨scp, hkp, hpass_le, rfl, hmp⟩
              c0_hsplit
              · clear hc
                c0_hsplit
                · have hpass_lt : pass.toNat < nc.toNat := hc; clear hc
                  have hpass1 : (pass + 1#32).toNat = pass.toNat + 1 := by c0_bound
                  c0_hsteps_nogrp
                  refine wp_loop_group (ts := [.bool, i32])
                    (fun rem (_chc, cid_c, ()) mc => ∃ scc, invCore scc ∧
                      cid_c.toNat ≤ nc.toNat ∧ rem = cid_c.toNat ∧
                      (array (t := i32) c.pScratchBuf scc ⋆ R') mc)
                    ?_ ?_
                  · rintro Lc remc ⟨ch_c, cid_c, ⟨⟩⟩ mc hLc ⟨scc, hkc, hc_le, rfl, hmc⟩
                    have hkc_l := hkc.2.1
                    c0_hsplit
                    · have hcid_pos : 0 < cid_c.toNat := hc; clear hc
                      let c_i := cid_c - 1#32
                      have hc_i_nat : c_i.toNat = cid_c.toNat - 1 := by
                        dsimp only [c_i]; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
                        omega
                      have hc_i_lt : c_i.toNat < nc.toNat := by omega
                      have hbd_c : 12672 + c_i.toNat < scc.length := by omega
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [.bool])
                        (fun (_, ()) mc' => ∃ scc', invCore scc' ∧
                          (array (t := i32) c.pScratchBuf scc' ⋆ R') mc')
                        (fun _ ⟨ch', ⟨⟩⟩ mc' ⟨scc', hkc', hmc'⟩ => by
                          c0_hsteps!
                          exact hLc c_i.toNat (ch', c_i, ()) mc' (by omega)
                            ⟨scc', hkc', by omega, rfl, hmc'⟩)
                        (fun Jcid hJcid => by
                          c0_hsplit
                          · clear hc
                            obtain ⟨hoff_sz, hoff_na, hge_c⟩ := hInv_clause hkc hc_i_lt
                            have hlt_c := hkc.1.length_lt
                            have hbd_off : 11648 + c_i.toNat < scc.length := by omega
                            let off_c := scc[11648 + c_i.toNat]'hbd_off
                            let meta_c := scc[12672 + c_i.toNat]'hbd_c
                            let sz_c := meta_c &&& 0xFFFF#32
                            have hno_ov1 : off_c.toNat + sz_c.toNat < 2 ^ 32 := by
                              have : off_c.toNat + sz_c.toNat ≤ acap.toNat := hoff_sz
                              omega
                            c0_hsteps_nogrp
                            refine wp_join_group (ts := [.bool])
                              (fun (_, ()) mc' => ∃ scc', invCore scc' ∧
                                (array (t := i32) c.pScratchBuf scc' ⋆ R') mc')
                              (fun _ ⟨ch', ⟨⟩⟩ mc' ⟨scc', hkc', hmc'⟩ => by
                                c0_hsteps!; exact hJcid (ch', ()) mc' ⟨scc', hkc', hmc'⟩)
                              (fun Jbr hJbr => by
                                c0_hsplit
                                · have hlrn_c : (meta_c &&& 0x40000000#32) ≠ 0#32 := hc
                                  clear hc
                                  have hbd_aux : 13696 + c_i.toNat < scc.length := by omega
                                  let na_c := scc[13696 + c_i.toNat]'hbd_aux
                                  have hna_le : off_c.toNat + sz_c.toNat + na_c.toNat ≤ acap.toNat :=
                                    hoff_na hlrn_c
                                  have hsum_bv : (off_c + sz_c).toNat = off_c.toNat + sz_c.toNat := by
                                    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hno_ov1]
                                  c0_hsteps_nogrp
                                  refine wp_join_group (ts := [.bool])
                                    (fun (_, ()) mc' => ∃ scc', invCore scc' ∧
                                      (array (t := i32) c.pScratchBuf scc' ⋆ R') mc')
                                    (fun _ ⟨ch', ⟨⟩⟩ mc' ⟨scc', hkc', hmc'⟩ => by
                                      c0_hsteps!; exact hJbr (ch', ()) mc' ⟨scc', hkc', hmc'⟩)
                                    (fun Ja hJa => by
                                      c0_hsplit
                                      · clear hc; c0_hsteps_nogrp
                                        refine wp_loop_group (ts := [.bool, i32])
                                          (fun rem (_, j, ()) mj' => ∃ scj2, invCore scj2 ∧
                                            j.toNat ≤ na_c.toNat ∧ rem = na_c.toNat - j.toNat ∧
                                            (array (t := i32) c.pScratchBuf scj2 ⋆ R') mj')
                                          ?_ ?_
                                        · rintro Lj remj ⟨chj, jj, ⟨⟩⟩ mj2 hLj
                                            ⟨scj2, hkj2, hj_le, rfl, hmj2⟩
                                          have hkj2_l := hkj2.2.1
                                          c0_hsplit
                                          · have hj_lt : jj.toNat < na_c.toNat := hc; clear hc
                                            have hj1 : (jj + 1#32).toNat = jj.toNat + 1 := by
                                              have : na_c.toNat < 2 ^ 30 := by omega
                                              c0_bound
                                            have har_bd :
                                                15744 + (off_c + sz_c).toNat + jj.toNat <
                                                  scj2.length := by
                                              rw [hsum_bv]; omega
                                            c0_hsteps_nogrp
                                            refine wp_join_group (ts := [.bool])
                                              (fun (_, ()) mj3 => ∃ scj3, invCore scj3 ∧
                                                (array (t := i32) c.pScratchBuf scj3 ⋆ R') mj3)
                                              (fun _ ⟨ch3, ⟨⟩⟩ mj3 ⟨scj3, hkj3, hmj3⟩ => by
                                                c0_hsteps!
                                                exact hLj (na_c.toNat - (jj + 1#32).toNat)
                                                  (ch3, jj + 1#32, ()) mj3 (by omega)
                                                  ⟨scj3, hkj3, by omega, rfl, hmj3⟩)
                                              (fun Jant hJant => by
                                                c0_hsplit
                                                · have hant_lt :
                                                      (scj2[15744 + (off_c + sz_c).toNat +
                                                        jj.toNat]'har_bd).toNat < nc.toNat := hc
                                                  clear hc
                                                  let ant := scj2[15744 + (off_c + sz_c).toNat +
                                                    jj.toNat]'har_bd
                                                  have hbd_a : 12672 + ant.toNat < scj2.length := by
                                                    have : ant.toNat < nc.toNat := hant_lt; omega
                                                  have hpa := m8_km_core_or_pres
                                                    (scj2[12672 + ant.toNat]'hbd_a)
                                                  c0_hsplit
                                                  · clear hc; c0_hsteps!
                                                    exact hJant (true, ()) _
                                                      ⟨_, invCore_set_meta hkj2 hant_lt
                                                        (by rw [List.getElem?_eq_getElem hbd_a,
                                                          Option.getD_some]; exact hpa.1)
                                                        (by rw [List.getElem?_eq_getElem hbd_a,
                                                          Option.getD_some]; exact hpa.2), hm⟩
                                                  · c0_hsteps!; exact hJant (chj, ()) mj2
                                                      ⟨scj2, hkj2, hmj2⟩
                                                · c0_hsteps!; exact hJant (chj, ()) mj2
                                                    ⟨scj2, hkj2, hmj2⟩)
                                          · c0_hsteps!; exact hJa (chj, ()) mj2 ⟨scj2, hkj2, hmj2⟩
                                        · intro Lj hLj; c0_hsteps!
                                          exact hLj na_c.toNat (ch_c, 0#32, ()) mc
                                            ⟨scc, hkc, Nat.zero_le _, by simp, hmc⟩
                                      · c0_hsteps!; exact hJa (ch_c, ()) mc ⟨scc, hkc, hmc⟩)
                                · clear hc; c0_hsteps_nogrp
                                  refine wp_join_group (ts := [.bool])
                                    (fun (_, ()) mc' => ∃ scc', invCore scc' ∧
                                      (array (t := i32) c.pScratchBuf scc' ⋆ R') mc')
                                    (fun _ ⟨ch', ⟨⟩⟩ mc' ⟨scc', hkc', hmc'⟩ => by
                                      c0_hsteps!; exact hJbr (ch', ()) mc' ⟨scc', hkc', hmc'⟩)
                                    (fun Jelse hJelse => by
                                      c0_hsplit
                                      · clear hc; c0_hsteps_nogrp
                                        refine wp_loop_group (ts := [.bool, i32])
                                          (fun rem (_, j, ()) mj' => ∃ scj2, invCore scj2 ∧
                                            j.toNat ≤ sz_c.toNat ∧ rem = sz_c.toNat - j.toNat ∧
                                            (array (t := i32) c.pScratchBuf scj2 ⋆ R') mj')
                                          ?_ ?_
                                        · rintro Lj remj ⟨chj, jj, ⟨⟩⟩ mj2 hLj
                                            ⟨scj2, hkj2, hj_le, rfl, hmj2⟩
                                          have hkj2_l := hkj2.2.1
                                          c0_hsplit
                                          · have hj_lt : jj.toNat < sz_c.toNat := hc; clear hc
                                            have hsz_lt : sz_c.toNat < 65536 := by
                                              dsimp only [sz_c]; rw [BitVec.toNat_and]
                                              exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                                            have hj1 : (jj + 1#32).toNat = jj.toNat + 1 := by
                                              c0_bound
                                            have har_bd :
                                                15744 + off_c.toNat + jj.toNat < scj2.length := by
                                              have : off_c.toNat + sz_c.toNat ≤ acap.toNat := hoff_sz
                                              omega
                                            c0_hsteps_nogrp
                                            refine wp_join_group (ts := [.bool])
                                              (fun (_, ()) mj3 => ∃ scj3, invCore scj3 ∧
                                                (array (t := i32) c.pScratchBuf scj3 ⋆ R') mj3)
                                              (fun _ ⟨ch3, ⟨⟩⟩ mj3 ⟨scj3, hkj3, hmj3⟩ => by
                                                c0_hsteps!
                                                exact hLj (sz_c.toNat - (jj + 1#32).toNat)
                                                  (ch3, jj + 1#32, ()) mj3 (by omega)
                                                  ⟨scj3, hkj3, by omega, rfl, hmj3⟩)
                                              (fun Jlv hJlv => by
                                                c0_hsplit
                                                · have hlv_lt :
                                                      ((scj2[15744 + off_c.toNat +
                                                        jj.toNat]'har_bd) >>> (1 : Nat)).toNat <
                                                        nv.toNat := by
                                                    rw [fid_bv32_lshr1_toNat]; exact hc
                                                  clear hc
                                                  let lv := (scj2[15744 + off_c.toNat +
                                                    jj.toNat]'har_bd) >>> (1 : Nat)
                                                  have hlv_lt' : lv.toNat < nv.toNat := hlv_lt
                                                  have hlv_4224 : 4224 + lv.toNat < scj2.length := by
                                                    omega
                                                  have hlv_4480 : 4480 + lv.toNat < scj2.length := by
                                                    omega
                                                  c0_hsplit
                                                  · clear hc; c0_hsteps_nogrp
                                                    refine wp_join_group (ts := [.bool])
                                                      (fun (_, ()) mj3 => ∃ scj3, invCore scj3 ∧
                                                        (array (t := i32) c.pScratchBuf scj3 ⋆ R')
                                                          mj3)
                                                      (fun _ ⟨ch3, ⟨⟩⟩ mj3 ⟨scj3, hkj3, hmj3⟩ => by
                                                        c0_hsteps!; exact hJlv (ch3, ()) mj3
                                                          ⟨scj3, hkj3, hmj3⟩)
                                                      (fun Jr0 hJr0 => by
                                                        c0_hsplit
                                                        · have hr0_lt :
                                                              (scj2[4480 + lv.toNat]'hlv_4480).toNat
                                                                < nc.toNat := hc
                                                          clear hc
                                                          let r0 := scj2[4480 + lv.toNat]'hlv_4480
                                                          have hbd_r0 :
                                                              12672 + r0.toNat < scj2.length := by
                                                            have : r0.toNat < nc.toNat := hr0_lt; omega
                                                          have hpr0 := m8_km_core_or_pres
                                                            (scj2[12672 + r0.toNat]'hbd_r0)
                                                          c0_hsplit
                                                          · clear hc; c0_hsteps!
                                                            exact hJr0 (true, ()) _
                                                              ⟨_, invCore_set_meta hkj2 hr0_lt
                                                                (by rw [List.getElem?_eq_getElem
                                                                  hbd_r0, Option.getD_some]
                                                                    exact hpr0.1)
                                                                (by rw [List.getElem?_eq_getElem
                                                                  hbd_r0, Option.getD_some]
                                                                    exact hpr0.2), hm⟩
                                                          · c0_hsteps!; exact hJr0 (chj, ()) mj2
                                                              ⟨scj2, hkj2, hmj2⟩
                                                        · c0_hsteps!; exact hJr0 (chj, ()) mj2
                                                            ⟨scj2, hkj2, hmj2⟩)
                                                  · c0_hsteps!; exact hJlv (chj, ()) mj2
                                                      ⟨scj2, hkj2, hmj2⟩
                                                · c0_hsteps!; exact hJlv (chj, ()) mj2
                                                    ⟨scj2, hkj2, hmj2⟩)
                                          · c0_hsteps!; exact hJelse (chj, ()) mj2 ⟨scj2, hkj2, hmj2⟩
                                        · intro Lj hLj; c0_hsteps!
                                          exact hLj sz_c.toNat (ch_c, 0#32, ()) mc
                                            ⟨scc, hkc, Nat.zero_le _, by simp, hmc⟩
                                      · c0_hsteps!; exact hJelse (ch_c, ()) mc ⟨scc, hkc, hmc⟩))
                          · c0_hsteps!; exact hJcid (ch_c, ()) mc ⟨scc, hkc, hmc⟩)
                    · c0_hsteps!
                      exact hLp (nc.toNat - (pass + 1#32).toNat) (pass + 1#32, ch_c, ()) mc
                        (by omega) ⟨scc, hkc, by omega, rfl, hmc⟩
                  · intro Lc hLc; c0_hsteps!
                    exact hLc nc.toNat (false, nc, ()) mp ⟨scp, hkp, Nat.le_refl _, rfl, hmp⟩
                · c0_hsteps!
                  exact hQ scp mp (by rw [hkp.2.1, hscr_l])
                    (fun idx hi hor => hkp.2.2.1 idx (hscr_l.symm ▸ hi) hor) hkp.1
                    (by rw [fid_fullMem_eq_scr, sep_assoc]; exact hmp)
              · c0_hsteps!
                exact hQ scp mp (by rw [hkp.2.1, hscr_l])
                  (fun idx hi hor => hkp.2.2.1 idx (hscr_l.symm ▸ hi) hor) hkp.1
                  (by rw [fid_fullMem_eq_scr, sep_assoc]; exact hmp)
            · intro Lp hLp; c0_hsteps!
              exact hLp nc.toNat (0#32, true, ()) mj ⟨scj, hkj, Nat.zero_le _, by simp, hmj⟩
          · -- `if (inc < nc)` block
            intro Jinc hJinc
            let inc := sc1[4199]'(by omega)
            c0_hsplit
            · have hinc : inc.toNat < nc.toNat := hc; clear hc
              -- Loop 2a: clear flag bit 2 on `kflags[0 ..< nv)`
              refine wp_loop_group (ts := [i32])
                (fun rem (i, ()) mf => ∃ scf, invCore scf ∧ i.toNat ≤ nv.toNat ∧
                  rem = nv.toNat - i.toNat ∧ (array (t := i32) c.pScratchBuf scf ⋆ R') mf)
                ?_ ?_
              · rintro Lf remf ⟨if1, ⟨⟩⟩ mf1 hLf ⟨scf1, hkf1, hif1, rfl, hmf1⟩
                have hkf1_l := hkf1.2.1
                c0_hsplit
                · have hi_lt : if1.toNat < nv.toNat := hc; clear hc
                  have hif1_s : (if1 + 1#32).toNat = if1.toNat + 1 := by c0_bound
                  have hbd_f : 5760 + if1.toNat < scf1.length := by omega
                  c0_hsteps!
                  exact hLf (nv.toNat - (if1 + 1#32).toNat) (if1 + 1#32, ()) _ (by omega)
                    ⟨_, invCore_set_flags hkf1 (by rw [zext_toNat _ (by decide)]; omega) _,
                      by omega, rfl, hm⟩
                · clear hc
                  obtain ⟨hoff_i, _, hge_i⟩ := hInv_clause hkf1 hinc
                  have hbd_mi : 12672 + inc.toNat < scf1.length := by omega
                  have hbd_oi : 11648 + inc.toNat < scf1.length := by omega
                  have hpmi := m8_km_core_or_pres (scf1[12672 + inc.toNat]'hbd_mi)
                  let scf2 := scf1.set (12672 + inc.toNat)
                    ((scf1[12672 + inc.toNat]'hbd_mi) ||| 0x80000000#32)
                  have hkf2 : invCore scf2 := invCore_set_meta hkf1 hinc
                    (by rw [List.getElem?_eq_getElem hbd_mi, Option.getD_some]; exact hpmi.1)
                    (by rw [List.getElem?_eq_getElem hbd_mi, Option.getD_some]; exact hpmi.2)
                  c0_hsteps_nogrp
                  -- Join after `if (off + sz <= acap)`
                  refine wp_join_group (ts := [])
                    (fun () mj => ∃ scj, invCore scj ∧
                      (array (t := i32) c.pScratchBuf scj ⋆ R') mj) ?_ ?_
                  · rintro _ ⟨⟩ mj ⟨scj, hkj, hmj⟩
                    have hkj_l := hkj.2.1
                    have h4197 : (4197#64).toNat < scj.length := by
                      rw [hkj_l, show (4197#64).toNat = 4197 from rfl]; omega
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [i32])
                      (fun (ti, ()) mti => mj = mti ∧ ti.toNat ≤ 256) ?_ ?_
                    · rintro _ ⟨ti, ⟨⟩⟩ _ ⟨rfl, hti⟩
                      c0_hsteps_nogrp
                      -- Loop 2b: trail walk `while (ti > 0)`
                      refine wp_loop_group (ts := [i32])
                        (fun rem (tic, ()) mt => ∃ sct, invCore sct ∧ tic.toNat ≤ 256 ∧
                          rem = tic.toNat ∧ (array (t := i32) c.pScratchBuf sct ⋆ R') mt)
                        ?_ ?_
                      · rintro Lt remt ⟨tic, ⟨⟩⟩ mt hLt ⟨sct, hkt, htic, rfl, hmt⟩
                        have hkt_l := hkt.2.1
                        c0_hsplit
                        · have ht_pos : 0 < tic.toNat := hc; clear hc
                          let t1 := tic - 1#32
                          have ht1_nat : t1.toNat = tic.toNat - 1 := by
                            dsimp only [t1]; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
                            omega
                          have ht1_bd : 5504 + t1.toNat < sct.length := by omega
                          c0_hsplit
                          · c0_hsteps!; exact hLt t1.toNat (t1, ()) mt (by omega)
                              ⟨sct, hkt, by omega, rfl, hmt⟩
                          · let vt := (sct[5504 + t1.toNat]'ht1_bd) >>> (1 : Nat)
                            have hvt_lt : vt.toNat < nv.toNat := by
                              refine Nat.lt_of_not_le ?_
                              dsimp only [vt]; rw [fid_bv32_lshr1_toNat]; exact hc
                            clear hc
                            have hvt_f : 5760 + vt.toNat < sct.length := by omega
                            have hvt_r : 4480 + vt.toNat < sct.length := by omega
                            have hvt_r_c0 :
                                4480 + (sct[(BitVec.ofNat (OfNat.ofNat 64)
                                    (OfNat.ofNat 5504)).toNat +
                                  (BitVec.setWidth 64 (tic - 1)).toNat]'(by
                                    rw [zext_toNat _ (by decide)]
                                    change 5504 + t1.toNat < sct.length; exact ht1_bd) >>>
                                  (OfNat.ofNat 1)).toNat < sct.length := by
                              have h5504 : (BitVec.ofNat (OfNat.ofNat 64)
                                  (OfNat.ofNat 5504)).toNat = 5504 := rfl
                              have ht1w : (BitVec.setWidth 64 (tic - 1)).toNat = t1.toNat :=
                                zext_toNat (tic - 1) (by decide)
                              simpa only [vt, h5504, ht1w] using hvt_r
                            c0_hsplit
                            · c0_hsteps!; exact hLt t1.toNat (t1, ()) mt (by omega)
                                ⟨sct, hkt, by omega, rfl, hmt⟩
                            · clear hc
                              let sct1 := sct.set (5760 + vt.toNat)
                                ((sct[5760 + vt.toNat]'hvt_f) &&& ~~~2#32)
                              have hkt1 : invCore sct1 :=
                                invCore_set_flags hkt (by omega) _
                              c0_hsplit
                              · c0_hsteps!; exact hLt t1.toNat (t1, ()) _ (by omega)
                                  ⟨sct1, hkt1, by omega, rfl, hm⟩
                              · have hrsn_lt :
                                    (sct1[4480 + vt.toNat]'(by simp [sct1]; omega)).toNat <
                                      nc.toNat := by
                                  refine Nat.lt_of_not_le ?_; exact hc
                                clear hc
                                let rsn := sct1[4480 + vt.toNat]'(by simp [sct1]; omega)
                                have hrsn_lt' : rsn.toNat < nc.toNat := hrsn_lt
                                obtain ⟨hroff_sz, _, hge_r⟩ := hInv_clause hkt1 hrsn_lt'
                                have hbd_mr : 12672 + rsn.toNat < sct1.length := by
                                  have := hkt1.2.1; omega
                                have hbd_or : 11648 + rsn.toNat < sct1.length := by
                                  have := hkt1.2.1; omega
                                have hpr := m8_km_core_or_pres (sct1[12672 + rsn.toNat]'hbd_mr)
                                let sct2 := sct1.set (12672 + rsn.toNat)
                                  ((sct1[12672 + rsn.toNat]'hbd_mr) ||| 0x80000000#32)
                                have hkt2 : invCore sct2 := invCore_set_meta hkt1 hrsn_lt'
                                  (by rw [List.getElem?_eq_getElem hbd_mr, Option.getD_some]
                                      exact hpr.1)
                                  (by rw [List.getElem?_eq_getElem hbd_mr, Option.getD_some]
                                      exact hpr.2)
                                c0_hsteps_nogrp
                                have hm_sct2 : (array (t := i32) c.pScratchBuf sct2 ⋆ R') m := by
                                  dsimp only [sct2, sct1, rsn, vt, t1]
                                  simpa only [BitVec.toNat_ofNat, zext32_64_toNat,
                                    Nat.mod_eq_of_lt (by decide : 5760 < 2 ^ 64),
                                    Nat.mod_eq_of_lt (by decide : 5504 < 2 ^ 64),
                                    Nat.mod_eq_of_lt (by decide : 4480 < 2 ^ 64),
                                    Nat.mod_eq_of_lt (by decide : 12672 < 2 ^ 64),
                                    show (OfNat.ofNat 1 : Nat) = 1 from rfl,
                                    show (1 : BitVec 32) = 1#32 from rfl,
                                    show (2147483648 : BitVec 32) = 0x80000000#32 from rfl,
                                    show (2 : BitVec 32) = 2#32 from rfl] using hm
                                clear hm
                                let roff := sct2[11648 + rsn.toNat]'(by rw [hkt2.2.1]; omega)
                                let rmeta := sct2[12672 + rsn.toNat]'(by rw [hkt2.2.1]; omega)
                                let rsz := rmeta &&& 0xFFFF#32
                                have hroff_eq : roff = sct1[11648 + rsn.toNat]'hbd_or := by
                                  dsimp only [roff, sct2]; rw [List.getElem_set_ne (by omega)]
                                have hrsz_eq : rsz =
                                    ((sct1[12672 + rsn.toNat]'hbd_mr) &&& 0xFFFF#32) := by
                                  dsimp only [rsz, rmeta, sct2]; rw [List.getElem_set_self]
                                  exact hpr.1
                                have hrr_le : roff.toNat + rsz.toNat ≤ acap.toNat := by
                                  rw [hroff_eq, hrsz_eq]; exact hroff_sz
                                have hld_roff := K6CoreCachedTactics.ld_scr_off
                                  (pScr := c.pScratchBuf) (xs := sct2) (K := 11648) (i := rsn)
                                  (by decide) (by rw [hkt2.2.1]; omega) hm_sct2
                                have hld_rmeta := K6CoreCachedTactics.ld_scr_off
                                  (pScr := c.pScratchBuf) (xs := sct2) (K := 12672) (i := rsn)
                                  (by decide) (by rw [hkt2.2.1]; omega) hm_sct2
                                refine wp_load_of (by
                                  dsimp only [Arg.val, rsn, sct2, sct1, vt, t1]
                                  simpa only [BitVec.toNat_ofNat, zext32_64_toNat,
                                    Nat.mod_eq_of_lt (by decide : 5760 < 2 ^ 64),
                                    Nat.mod_eq_of_lt (by decide : 5504 < 2 ^ 64),
                                    Nat.mod_eq_of_lt (by decide : 4480 < 2 ^ 64),
                                    Nat.mod_eq_of_lt (by decide : 12672 < 2 ^ 64),
                                    show BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 11648) =
                                      11648#64 from rfl,
                                    show (OfNat.ofNat 1 : Nat) = 1 from rfl,
                                    show (1 : BitVec 32) = 1#32 from rfl,
                                    show (2147483648 : BitVec 32) = 0x80000000#32 from rfl,
                                    show (2 : BitVec 32) = 2#32 from rfl] using hld_roff) ?_
                                c0_hsteps_nogrp
                                refine wp_load_of (by
                                  dsimp only [Arg.val, rsn, sct2, sct1, vt, t1]
                                  simpa only [BitVec.toNat_ofNat, zext32_64_toNat,
                                    Nat.mod_eq_of_lt (by decide : 5760 < 2 ^ 64),
                                    Nat.mod_eq_of_lt (by decide : 5504 < 2 ^ 64),
                                    Nat.mod_eq_of_lt (by decide : 4480 < 2 ^ 64),
                                    Nat.mod_eq_of_lt (by decide : 12672 < 2 ^ 64),
                                    show BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 12672) =
                                      12672#64 from rfl,
                                    show (OfNat.ofNat 1 : Nat) = 1 from rfl,
                                    show (1 : BitVec 32) = 1#32 from rfl,
                                    show (2147483648 : BitVec 32) = 0x80000000#32 from rfl,
                                    show (2 : BitVec 32) = 2#32 from rfl] using hld_rmeta) ?_
                                refine wp_join_group (ts := [])
                                  (fun () mj => ∃ scj, invCore scj ∧
                                    (array (t := i32) c.pScratchBuf scj ⋆ R') mj)
                                  (fun _ () mj ⟨scj, hkj, hmj⟩ => by
                                    c0_hsteps!
                                    exact hLt t1.toNat (t1, ()) mj (by omega)
                                      ⟨scj, hkj, by omega, rfl, hmj⟩)
                                  fun Jg hJg => ?_
                                c0_hsplit
                                · clear hc; c0_hsteps_nogrp
                                  refine wp_loop_group (ts := [i32])
                                    (fun rem (j, ()) mrj => ∃ scrj, invCore scrj ∧
                                      j.toNat ≤ rsz.toNat ∧ rem = rsz.toNat - j.toNat ∧
                                      (array (t := i32) c.pScratchBuf scrj ⋆ R') mrj)
                                    ?_ ?_
                                  · rintro Lr remr ⟨jr, ⟨⟩⟩ mrj hLr
                                      ⟨scrj, hkrj, hjr_le, rfl, hmrj⟩
                                    have hkrj_l := hkrj.2.1
                                    c0_hsplit
                                    · have hjr_lt : jr.toNat < rsz.toNat := hc; clear hc
                                      have hrsz_lt : rsz.toNat < 65536 := by
                                        dsimp only [rsz]; rw [BitVec.toNat_and]
                                        exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                                      have hjr1 : (jr + 1#32).toNat = jr.toNat + 1 := by c0_bound
                                      have har_r :
                                          15744 + roff.toNat + jr.toNat < scrj.length := by omega
                                      c0_hsteps_nogrp
                                      refine wp_join_group (ts := [])
                                        (fun () mr2 => ∃ scr2, invCore scr2 ∧
                                          (array (t := i32) c.pScratchBuf scr2 ⋆ R') mr2)
                                        (fun _ () mr2 ⟨scr2, hkr2, hmr2⟩ => by
                                          c0_hsteps!
                                          exact hLr (rsz.toNat - (jr + 1#32).toNat)
                                            (jr + 1#32, ()) mr2 (by omega)
                                            ⟨scr2, hkr2, by omega, rfl, hmr2⟩)
                                        (fun Jrlv hJrlv => by
                                          c0_hsplit
                                          · have hrv_c0 := hc
                                            have hlv_r :
                                                ((scrj[15744 + roff.toNat +
                                                  jr.toNat]'har_r) >>> (1 : Nat)).toNat <
                                                  nv.toNat := by
                                              rw [fid_bv32_lshr1_toNat]; exact hc
                                            clear hc
                                            c0_hsplit
                                            · clear hc
                                              have hlv_r256 :
                                                  ((scrj[15744 + roff.toNat +
                                                    jr.toNat]'har_r) >>> (1 : Nat)).toNat <
                                                    256 := by omega
                                              have hbd_fr :
                                                  (BitVec.ofNat (OfNat.ofNat 64)
                                                    (OfNat.ofNat 5760)).toNat +
                                                    (BitVec.setWidth 64
                                                      (scrj[OfNat.ofNat 15744 +
                                                        (sct2[11648 + rsn.toNat]'(by
                                                          rw [hkt2.2.1]; omega)).toNat +
                                                        jr.toNat]'(by
                                                          change 15744 + roff.toNat + jr.toNat <
                                                            scrj.length
                                                          exact har_r) >>>
                                                      OfNat.ofNat 1)).toNat < scrj.length := by
                                                rw [zext_toNat _ (by decide)]
                                                change 5760 + ((scrj[15744 + roff.toNat +
                                                  jr.toNat]'har_r) >>> (1 : Nat)).toNat <
                                                  scrj.length
                                                omega
                                              c0_hsteps!
                                              exact hJrlv () _
                                                ⟨_, invCore_set_flags hkrj
                                                  (by
                                                    rw [zext_toNat _ (by decide)]
                                                    dsimp only [roff] at hlv_r256
                                                    simpa only [
                                                      show (OfNat.ofNat 15744 : Nat) = 15744
                                                        from rfl,
                                                      show (OfNat.ofNat 1 : Nat) = 1 from rfl]
                                                      using hlv_r256)
                                                  _, hm⟩
                                            · c0_hsteps!; exact hJrlv () mrj ⟨scrj, hkrj, hmrj⟩
                                          · c0_hsteps!; exact hJrlv () mrj ⟨scrj, hkrj, hmrj⟩)
                                    · c0_hsteps!
                                      exact hJg () mrj ⟨scrj, hkrj, hmrj⟩
                                  · intro Lr hLr; c0_hsteps!
                                    exact hLr rsz.toNat (0#32, ()) _
                                      ⟨sct2, hkt2, Nat.zero_le _, by simp, hm_sct2⟩
                                · c0_hsteps!
                                  exact hJg () _ ⟨sct2, hkt2, hm_sct2⟩
                        · clear hc
                          -- Loop 2c: clear flag bit 2 on `kflags[0 ..< nv)`
                          c0_hsteps_nogrp
                          refine wp_loop_group (ts := [i32])
                            (fun rem (i, ()) mf => ∃ scf, invCore scf ∧ i.toNat ≤ nv.toNat ∧
                              rem = nv.toNat - i.toNat ∧
                              (array (t := i32) c.pScratchBuf scf ⋆ R') mf)
                            ?_ ?_
                          · rintro Lc2 remc2 ⟨ic2, ⟨⟩⟩ mc2 hLc2 ⟨scc2, hkc2, hic2, rfl, hmc2⟩
                            have hkc2_l := hkc2.2.1
                            c0_hsplit
                            · have hi_lt : ic2.toNat < nv.toNat := hc; clear hc
                              have hi_s : (ic2 + 1#32).toNat = ic2.toNat + 1 := by c0_bound
                              have hbd_f : 5760 + ic2.toNat < scc2.length := by omega
                              c0_hsteps!
                              exact hLc2 (nv.toNat - (ic2 + 1#32).toNat) (ic2 + 1#32, ()) _
                                (by omega)
                                ⟨_, invCore_set_flags hkc2
                                  (by rw [zext_toNat _ (by decide)]; omega) _, by omega, rfl, hm⟩
                            · c0_hsteps!; exact hJinc (ic2, ()) mc2 ⟨scc2, hkc2, hmc2⟩
                          · intro Lc2 hLc2; c0_hsteps!
                            exact hLc2 nv.toNat (0#32, ()) mt ⟨sct, hkt, Nat.zero_le _, by simp, hmt⟩
                      · intro Lt hLt; c0_hsteps!
                        exact hLt ti.toNat (ti, ()) mj ⟨scj, hkj, hti, rfl, hmj⟩
                    · intro Jti hJti; c0_hsplit
                      · c0_hsteps!; exact hJti (256#32, ()) mj ⟨rfl, by decide⟩
                      · have hle : (scj[4197]'(by omega)).toNat ≤ 256 := Nat.le_of_not_lt hc
                        c0_hsteps!; exact hJti (scj[4197]'(by omega), ()) mj ⟨rfl, hle⟩
                  · intro Ji hJi
                    c0_hsplit
                    · clear hc; c0_hsteps_nogrp
                      let off_i := scf2[11648 + inc.toNat]'(by rw [hkf2.2.1]; omega)
                      let sz_i := (scf2[12672 + inc.toNat]'(by rw [hkf2.2.1]; omega)) &&& 0xFFFF#32
                      have hoff_eq : off_i = scf1[11648 + inc.toNat]'hbd_oi := by
                        dsimp only [off_i, scf2]; rw [List.getElem_set_ne (by omega)]
                      have hsz_eq : sz_i = ((scf1[12672 + inc.toNat]'hbd_mi) &&& 0xFFFF#32) := by
                        dsimp only [sz_i, scf2]; rw [List.getElem_set_self]; exact hpmi.1
                      have hii_le : off_i.toNat + sz_i.toNat ≤ acap.toNat := by
                        rw [hoff_eq, hsz_eq]; exact hoff_i
                      refine wp_loop_group (ts := [i32])
                        (fun rem (j, ()) mj1 => ∃ scj1, invCore scj1 ∧
                          j.toNat ≤ sz_i.toNat ∧ rem = sz_i.toNat - j.toNat ∧
                          (array (t := i32) c.pScratchBuf scj1 ⋆ R') mj1)
                        ?_ ?_
                      · rintro Li remi ⟨ji, ⟨⟩⟩ mji hLi ⟨sci, hki, hji_le, rfl, hmji⟩
                        have hki_l := hki.2.1
                        c0_hsplit
                        · have hji_lt : ji.toNat < sz_i.toNat := hc; clear hc
                          have hsz_lt : sz_i.toNat < 65536 := by
                            dsimp only [sz_i]; rw [BitVec.toNat_and]
                            exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                          have hji1 : (ji + 1#32).toNat = ji.toNat + 1 := by c0_bound
                          have har_i : 15744 + off_i.toNat + ji.toNat < sci.length := by omega
                          c0_hsteps_nogrp
                          refine wp_join_group (ts := [])
                            (fun () mji2 => ∃ sci2, invCore sci2 ∧
                              (array (t := i32) c.pScratchBuf sci2 ⋆ R') mji2)
                            (fun _ () mji2 ⟨sci2, hki2, hmji2⟩ => by
                              c0_hsteps!
                              exact hLi (sz_i.toNat - (ji + 1#32).toNat) (ji + 1#32, ()) mji2
                                (by omega) ⟨sci2, hki2, by omega, rfl, hmji2⟩)
                            (fun Jilv hJilv => by
                              c0_hsplit
                              · have hlv_i :
                                    ((sci[15744 + off_i.toNat + ji.toNat]'har_i) >>>
                                      (1 : Nat)).toNat < nv.toNat := by
                                  rw [fid_bv32_lshr1_toNat]; exact hc
                                clear hc
                                have hbd_fi :
                                    5760 + ((sci[15744 + off_i.toNat + ji.toNat]'har_i) >>>
                                      (1 : Nat)).toNat < sci.length := by
                                  have := hlv_i; omega
                                c0_hsteps!
                                exact hJilv () _ ⟨_, invCore_set_flags hki (by
                                  rw [zext32_64_toNat]
                                  have hlt' : (sci[15744 + off_i.toNat + ji.toNat]'har_i >>>
                                      (1 : Nat)).toNat < 256 := Nat.lt_of_lt_of_le hlv_i hnv_le
                                  simpa only [off_i, scf2, inc, BitVec.toNat_ofNat,
                                    zext32_64_toNat,
                                    show (2147483648 : BitVec 32) = 2147483648#32 from rfl,
                                    Nat.mod_eq_of_lt (by decide : 12672 < 2 ^ 64),
                                    Nat.mod_eq_of_lt (by decide : 11648 < 2 ^ 64),
                                    Nat.mod_eq_of_lt (by decide : 4199 < 2 ^ 64)] using hlt') _,
                                  hm⟩
                              · c0_hsteps!; exact hJilv () mji ⟨sci, hki, hmji⟩)
                        · c0_hsteps!; exact hJi () mji ⟨sci, hki, hmji⟩
                      · intro Li hLi; c0_hsteps!
                        exact hLi sz_i.toNat (0#32, ()) _ ⟨scf2, hkf2, Nat.zero_le _, by simp, hm⟩
                    · c0_hsteps!; exact hJi () _ ⟨scf2, hkf2, hm⟩
              · intro Lf hLf; c0_hsteps!
                exact hLf nv.toNat (0#32, ()) m1 ⟨sc1, hk1, Nat.zero_le _, by simp, hm1⟩
            · c0_hsteps!; exact hJinc (i1, ()) m1 ⟨sc1, hk1, hm1⟩
      · intro L1 hL1; c0_hsteps!
        exact hL1 nc.toNat (0#32, ()) m0
          ⟨scr, ⟨hok0, rfl, fun _ _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩, Nat.zero_le _, by simp, hm0'⟩

end K6CoreFid

end LeanQbe.T.Examples.Kissat.FullFidelityVivK6
