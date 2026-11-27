/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1Core
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProof0
import LeanQbe.T.Examples.Kissat.FullFidelityBveTactics
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S1-C Proofs — Part 1a (`full_k6_core_fid` Helpers & Fixpoint)

Certifies `s13_fid_fixpoint_wp` for Step-13 `full_k6_core_fid` (`F-P0-1` non-exclusive level-0
trace in the fixpoint loop), decomposed into `<= 420`-line theorems (`public section`, `0`
`@[expose]` on theorems/lemmas, `0` `import all`, `<= 100` cols, `< 1,400` LOC).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityBve
open Kraken.Bedrock2.Test

open scoped M8K6bTactics FidK6Tactics

attribute [local bv_c0] List.length_set

local macro_rules
  | `(tactic| c0_bound) => `(tactic| first | assumption | rfl | decide | omega | fid_omega)

@[expose] public def FidCoreInv (scr0 : List (BitVec 32)) (mv nc : BitVec 32)
    (scr : List (BitVec 32)) : Prop :=
  FidK6BufOk scr ∧ scr.length = scr0.length ∧
  (∀ idx < scr0.length,
    (idx < 4224 + 6 * mv.toNat ∨ (4224 + 7 * mv.toNat ≤ idx ∧ idx < 4224 + 33 * mv.toNat) ∨
      4224 + 37 * mv.toNat ≤ idx) →
    scr[idx]? = scr0[idx]?) ∧
  (∀ cid < nc.toNat,
    let m0 := scr0[4224 + 33 * mv.toNat + cid]?.getD 0#32
    let m1 := scr[4224 + 33 * mv.toNat + cid]?.getD 0#32
    (m1 &&& 0xFFFF#32) = (m0 &&& 0xFFFF#32) ∧
    (m1 &&& 0x40000000#32) = (m0 &&& 0x40000000#32))

@[expose] public def fidDflt : (t : Ty) → Val t
  | .bool => false | .bits _ => 0 | .float _ => 0 | .pair a b => (fidDflt a, fidDflt b)
@[expose] public def fidDfltT : (ts : List Ty) → Tup Val ts
  | [] => () | t :: r => (fidDflt t, fidDfltT r)
@[expose] public def fSLet {L rs} : Expr Val L rs → Expr Val L rs
  | .let_ (ts := ts) _ k => k (fidDfltT ts) | _ => .hlt
@[expose] public def fSLet32 {L rs} (v : Val i32) : Expr Val L rs → Expr Val L rs
  | .let_ (ts := [.bits 32]) _ k => k (v, ()) | _ => .hlt
@[expose] public def fSLd {L rs} (v : Val i32) : Expr Val L rs → Expr Val L rs
  | .load (.bits 32) _ k => k v | _ => .hlt
@[expose] public def fSLd64 {L rs} (v : Val i64) : Expr Val L rs → Expr Val L rs
  | .load (.bits 64) _ k => k v | _ => .hlt
@[expose] public def fSJF {L rs} : Expr Val L rs → Expr Val L rs
  | .jnz _ _ e => e | _ => .hlt
@[expose] public def fSJT {L rs} : Expr Val L rs → Expr Val L rs
  | .jnz _ e _ => e | _ => .hlt
@[expose] public def fSGrp1 {rs} (x : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) bs _ =>
      match bs ((fun _ _ => True), ()) with | .cons b _ => b (x, ())
  | _ => .hlt

@[expose] public def s13FidPhase2E (h scrPtr : BitVec 64) (mv nc nv acap inc : BitVec 32) :
    Expr Val Cont [] :=
  let e := fSLd mv (fSLet (fSLet (fSLet (fSLd64 scrPtr
    (fSLet (full_k6_core_fid_body Val Cont (h, ())))))))
  let e := fSLd acap (fSLet (fSLet (fSLet (fSLd nv (fSLet (fSLet (fSLet
    (fSLd nc (fSLet (fSLet (fSLet e)))))))))))
  let e := fSJF (fSLet (fSJF (fSLet (fSLet (fSJF (fSLet (fSJF (fSLet e))))))))
  let e := fSLet32 (4224#32 + 45#32 * mv) (fSLet32 (45#32 * mv)
    (fSLet32 (4224#32 + 37#32 * mv) (fSLet32 (37#32 * mv)
    (fSLet32 (4224#32 + 33#32 * mv) (fSLet32 (33#32 * mv)
    (fSLet32 (4224#32 + 29#32 * mv) (fSLet32 (29#32 * mv)
    (fSLet32 (4224#32 + 6#32 * mv) (fSLet32 (6#32 * mv)
    (fSLet32 (4224#32 + 5#32 * mv) (fSLet32 (5#32 * mv)
    (fSLet32 (4224#32 + mv) e))))))))))))
  let e := fSGrp1 0#32 e
  fSLd inc (fSLet (fSLet (fSLet (fSJF (fSLet e)))))

@[expose] public def s13FidFixE (h scrPtr : BitVec 64) (mv nc nv acap x_i : BitVec 32)
    (J2 : Cont [.bits 32]) : Expr Val Cont [] :=
  match s13FidPhase2E h scrPtr mv nc nv acap 0#32 with
  | .group (sig := [[.bits 32]]) bs _ =>
      match bs (J2, ()) with | .cons b _ => b (x_i, ())
  | _ => .hlt

@[expose] public def s13FidLvl0E (h scrPtr : BitVec 64)
    (mv nc nv acap off_c sz_c : BitVec 32)
    (ch' : Bool) (J2 : Cont [.bits 32]) (Jcid : Cont [.bool]) : Expr Val Cont [] :=
  let e := s13FidFixE h scrPtr mv nc nv acap 0#32 J2
  let e := match e with
    | .group (sig := [[.bits 32, .bool]]) bs _ =>
        match bs ((fun _ _ => True), ()) with | .cons b _ => b (0#32, true, ())
    | _ => .hlt
  let e := fSLet (fSJT (fSLet (fSJT e)))
  let e := match e with
    | .group (sig := [[.bool, .bits 32]]) bs _ =>
        match bs ((fun _ _ => True), ()) with | .cons b _ => b (false, nc, ())
    | _ => .hlt
  let e := fSLd 0#32 (fSLet (fSLet (fSLet (fSLet (fSLet (fSJT (fSLet e)))))))
  let e := match e with
    | .group (sig := [[.bool]]) _ body => body (Jcid, ())
    | _ => .hlt
  let e := fSLet32 sz_c (fSLd off_c (fSLet (fSLet (fSLet (fSLet (fSJT (fSLet (fSLet e))))))))
  match e with
  | .group (sig := [[.bool]]) bs _ =>
      match bs (Jcid, ()) with | .cons b _ => b ((ch' : Val .bool), ())
  | _ => .hlt

@[expose] public def s13FidIncE (h scrPtr : BitVec 64) (mv nc nv acap inc : BitVec 32)
    (J2 : Cont [.bits 32]) : Expr Val Cont [] :=
  match s13FidPhase2E h scrPtr mv nc nv acap inc with
  | .group (sig := [[.bits 32]]) _ body => fSJT (fSLet (body (J2, ())))
  | _ => .hlt

public section

theorem s13f_and_ffff (x : BitVec 32) : (x &&& 0xFFFF#32).toNat = x.toNat % 65536 := by
  rw [BitVec.toNat_and, show (0xFFFF#32 : BitVec 32).toNat = 2 ^ 16 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem s13f_sub1_mod32 (a x : Nat) (hx : 0 < x) (hlt : a + (x - 1) < 4294967296) :
    (a + (4294967296 - 1 + x)) % 4294967296 = a + (x - 1) := by
  rw [show a + (4294967296 - 1 + x) = (a + (x - 1)) + 4294967296 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

theorem fidCoreInv_mv {scr0 scr : List (BitVec 32)} {mv nc : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (h : FidCoreInv scr0 mv nc scr) : scr[4214]?.getD 0#32 = mv := by
  rw [h.2.2.1 4214 h4214 (Or.inl (by omega)), hmv_eq]

theorem fidCoreInv_set_meta {scr0 : List (BitVec 32)} {mv nc : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (hnc_le : nc.toNat ≤ 4 * mv.toNat) {scr : List (BitVec 32)} (hik : FidCoreInv scr0 mv nc scr)
    {cid : Nat} (hcid : cid < nc.toNat) {v : BitVec 32}
    (hsz : (v &&& 0xFFFF#32) = ((scr[4224 + 33 * mv.toNat + cid]?.getD 0#32) &&& 0xFFFF#32))
    (hlrn : (v &&& 0x40000000#32) =
      ((scr[4224 + 33 * mv.toNat + cid]?.getD 0#32) &&& 0x40000000#32)) :
    FidCoreInv scr0 mv nc (scr.set (4224 + 33 * mv.toNat + cid) v) := by
  have hmv' := fidCoreInv_mv h4214 hmv_eq hik
  have hb := hik.1.base_ge; rw [hmv'] at hb
  have hok' : FidK6BufOk (scr.set (4224 + 33 * mv.toNat + cid) v) := by
    have h1 := fidK6BufOk_set_core_meta hik.1 (cid := cid) (v := v)
      (by rw [hmv']; omega) (by rw [hmv']; exact hsz) (by rw [hmv']; exact hlrn)
    rwa [hmv'] at h1
  refine ⟨hok', by simp [hik.2.1], fun idx hi hor => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by fid_ne)]; exact hik.2.2.1 idx hi hor
  · by_cases heq : j = cid
    · subst heq; dsimp only; rw [List.getElem?_set_self (by omega), Option.getD_some, hsz, hlrn]
      exact hik.2.2.2 j hj
    · rw [List.getElem?_set_ne (by fid_ne)]; exact hik.2.2.2 j hj

theorem fidCoreInv_set_flags {scr0 : List (BitVec 32)} {mv nc : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    {scr : List (BitVec 32)} (hik : FidCoreInv scr0 mv nc scr) {v : Nat} (hv : v < mv.toNat)
    (val : BitVec 32) : FidCoreInv scr0 mv nc (scr.set (4224 + 6 * mv.toNat + v) val) := by
  have hmv' := fidCoreInv_mv h4214 hmv_eq hik
  have hok' : FidK6BufOk (scr.set (4224 + 6 * mv.toNat + v) val) := by
    have h1 := fidK6BufOk_set_flags hik.1 (i := v) (by rw [hmv']; exact hv) val
    rwa [hmv'] at h1
  refine ⟨hok', by simp [hik.2.1], fun idx hi hor => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by fid_ne)]; exact hik.2.2.1 idx hi hor
  · rw [List.getElem?_set_ne (by fid_ne)]; exact hik.2.2.2 j hj

theorem fidCoreInv_set_meta_pres {scr0 scr : List (BitVec 32)} {mv nc : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (hnc_le : nc.toNat ≤ 4 * mv.toNat) (hik : FidCoreInv scr0 mv nc scr)
    {cid : BitVec 32} (hcid : cid.toNat < nc.toNat) {v : BitVec 32}
    (he : ((4224 + 33 * mv + cid).setWidth 64).toNat = 4224 + 33 * mv.toNat + cid.toNat)
    (hlt : ((4224 + 33 * mv + cid).setWidth 64).toNat < scr.length)
    (hpres : (v &&& 0xFFFF#32) =
        ((scr[((4224 + 33 * mv + cid).setWidth 64).toNat]'hlt) &&& 0xFFFF#32) ∧
      (v &&& 0x40000000#32) =
        ((scr[((4224 + 33 * mv + cid).setWidth 64).toNat]'hlt) &&& 0x40000000#32)) :
    FidCoreInv scr0 mv nc (scr.set ((4224 + 33 * mv + cid).setWidth 64).toNat v) := by
  have hll := hik.2.1
  have h1 := fidCoreInv_set_meta h4214 hmv_eq hnc_le hik hcid (v := v)
    (by rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
        m8_k6_get_congr he.symm (by omega) hlt]; exact hpres.1)
    (by rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
        m8_k6_get_congr he.symm (by omega) hlt]; exact hpres.2)
  simpa only [he] using h1

theorem fidCoreInv_set_flags_e {scr0 scr : List (BitVec 32)} {mv nc : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (hik : FidCoreInv scr0 mv nc scr) {v : BitVec 32} (hv : v.toNat < mv.toNat)
    (he : ((4224 + 6 * mv + v).setWidth 64).toNat = 4224 + 6 * mv.toNat + v.toNat)
    (val : BitVec 32) :
    FidCoreInv scr0 mv nc (scr.set ((4224 + 6 * mv + v).setWidth 64).toNat val) := by
  simpa only [he] using fidCoreInv_set_flags h4214 hmv_eq hik hv val

theorem fidCore_k_lt (k : Nat) {x : Nat} {mv : BitVec 32} {len : Nat}
    (hx : x ≤ 4 * mv.toNat) (hmv : 256 ≤ mv.toNat)
    (hbge : 4224 + 45 * mv.toNat ≤ len) (hk : k ≤ 40 := by decide) :
    4224 + k * mv.toNat + x < len := by
  have hk_le : k * mv.toNat ≤ 40 * mv.toNat := Nat.mul_le_mul_right mv.toNat hk; omega

theorem fidCore_mv_lt (k : Nat) {x : Nat} {mv : BitVec 32} {len : Nat}
    (hx : x ≤ mv.toNat) (hmv : 256 ≤ mv.toNat)
    (hbge : 4224 + 45 * mv.toNat ≤ len) (hk : k ≤ 40 := by decide) :
    4224 + k * mv.toNat + x < len :=
  fidCore_k_lt k (Nat.le_trans hx (by omega)) hmv hbge hk

theorem fidCore_1_lt {x : Nat} {mv : BitVec 32} {len : Nat}
    (hx : x ≤ mv.toNat) (hmv : 256 ≤ mv.toNat) (hbge : 4224 + 45 * mv.toNat ≤ len) :
    4224 + mv.toNat + x < len := by have h := fidCore_mv_lt 1 hx hmv hbge; omega

theorem fidCore_clause_ok_bnds {scr0 scrt : List (BitVec 32)} {mv nc acap cid : BitVec 32}
    (h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (h4193 : 4193 < scr0.length) (hnc_eq : scr0[4193]?.getD 0#32 = nc)
    (h4207 : 4207 < scr0.length) (hac_eq : scr0[4207]?.getD 0#32 = acap)
    (hmv_hi : mv.toNat ≤ 8192) (_hnc_le : nc.toNat ≤ 4 * mv.toNat)
    (hik : FidCoreInv scr0 mv nc scrt) (hcid : cid.toNat < nc.toNat)
    (hor_e : ((4224 + 29 * mv + cid).setWidth 64).toNat = 4224 + 29 * mv.toNat + cid.toNat)
    (hmr_e : ((4224 + 33 * mv + cid).setWidth 64).toNat = 4224 + 33 * mv.toNat + cid.toNat)
    (hor_b : ((4224 + 29 * mv + cid).setWidth 64).toNat < scrt.length)
    (hmr_b : ((4224 + 33 * mv + cid).setWidth 64).toNat < scrt.length) :
    let roff := scrt[((4224 + 29 * mv + cid).setWidth 64).toNat]'hor_b
    let rmeta := scrt[((4224 + 33 * mv + cid).setWidth 64).toNat]'hmr_b
    roff.toNat + (rmeta &&& 0xFFFF#32).toNat ≤ acap.toNat ∧
    (scrt[4224 + 33 * mv.toNat + cid.toNat]?.getD 0#32).toNat % 65536 =
      (rmeta &&& 0xFFFF#32).toNat ∧
    roff.toNat + (rmeta &&& 0xFFFF#32).toNat ≤ 65535 + acap.toNat ∧
    4224 + 45 * mv.toNat + acap.toNat ≤ scrt.length := by
  have hlt := hik.2.1; have hmin := hik.1.base_ge; have hmv_t := fidCoreInv_mv h4214 hmv_eq hik
  have hnc_t : scrt[4193]?.getD 0#32 = nc := by
    rw [hik.2.2.1 4193 h4193 (Or.inl (by omega)), hnc_eq]
  have hac_t : scrt[4207]?.getD 0#32 = acap := by
    rw [hik.2.2.1 4207 h4207 (Or.inl (by omega)), hac_eq]
  have hcl := hik.1.clause_ok (cid := cid.toNat) (by rw [hnc_t]; exact hcid)
  dsimp only at hcl; rw [hmv_t, hac_t] at hcl
  have hroff_eq : (scrt[4224 + 29 * mv.toNat + cid.toNat]?.getD 0#32) =
      scrt[((4224 + 29 * mv + cid).setWidth 64).toNat]'hor_b := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact m8_k6_get_congr hor_e.symm _ _
  have hrm_eq : (scrt[4224 + 33 * mv.toNat + cid.toNat]?.getD 0#32) =
      scrt[((4224 + 33 * mv + cid).setWidth 64).toNat]'hmr_b := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact m8_k6_get_congr hmr_e.symm _ _
  rw [hroff_eq, hrm_eq] at hcl
  have hlen_ge := hik.1.length_ge; rw [hmv_t, hac_t] at hlen_ge
  refine ⟨hcl.1, ?_, ?_, hlen_ge⟩
  · rw [hrm_eq, s13f_and_ffff]
  · have := m8_and_ffff_le (scrt[((4224 + 33 * mv + cid).setWidth 64).toNat]'hmr_b); omega

private theorem s13_fid_lvl0_lits_wp {Γ : Env} {c : FullCfg} {s : FullState}
    {scr0 : List (BitVec 32)} {mv nc nv acap off_c sz_c : BitVec 32} {R : Mem 64 → Prop}
    {Q : Post []} {X : XPost} {J2 : Cont [.bits 32]} {Jcid : Cont [.bool]}
    (hscr_len : scr0.length = c.scratch_cap)
    (h4214 : 4214 < scr0.length) (_hmv_d : scr0[4214]'h4214 = mv)
    (hmv_eq : scr0[4214]?.getD 0#32 = mv) (hmv_lo : 256 ≤ mv.toNat) (hmv_hi : mv.toNat ≤ 8192)
    (h4192 : 4192 < scr0.length) (_hnv_d : scr0[4192]'h4192 = nv)
    (h4193 : 4193 < scr0.length) (_hnc_d : scr0[4193]'h4193 = nc) (hnc_le : nc.toNat ≤ 4 * mv.toNat)
    (h4207 : 4207 < scr0.length) (_hac_d : scr0[4207]'h4207 = acap)
    (hac_eq : scr0[4207]?.getD 0#32 = acap)
    (hnv_le : nv.toNat ≤ mv.toNat) (hbge : 4224 + 45 * mv.toNat ≤ scr0.length)
    (hlen_scr : 4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length) (hcap_lt : scr0.length < 2 ^ 30)
    {scrc : List (BitVec 32)} {mc : Mem 64} {ch_c : Bool}
    (hikc : FidCoreInv scr0 mv nc scrc) (hoff_sz : off_c.toNat + sz_c.toNat ≤ acap.toNat)
    (hsz_le : sz_c.toNat ≤ 65535) (hmc : (FullMem c (m8ScrSt s scrc) ⋆ R) mc)
    (hJcid : ∀ xs mc', (match xs with
      | (_ch', ()) => ∃ scrc', FidCoreInv scr0 mv nc scrc' ∧
          (FullMem c (m8ScrSt s scrc') ⋆ R) mc') → Jcid xs mc') :
    wp Γ Q X (s13FidLvl0E c.hdr c.pScratchBuf mv nc nv acap off_c sz_c ch_c J2 Jcid) mc := by
  have hlc : scrc.length = scr0.length := hikc.2.1
  have hac_c : scrc[4207]?.getD 0#32 = acap := by
    rw [hikc.2.2.1 4207 h4207 (Or.inl (by omega)), hac_eq]
  have hmv_c := fidCoreInv_mv h4214 hmv_eq hikc
  have hac_g : scrc[4207]'(by omega) = acap := by
    rw [← Option.some_inj, ← List.getElem?_eq_getElem, ← hac_c, List.getElem?_eq_getElem (by omega),
      Option.getD_some]
  dsimp only [s13FidLvl0E, s13FidFixE, s13FidPhase2E, full_k6_core_fid_body, fSLet, fSLet32,
    fSLd, fSLd64, fSJF, fSJT, fSGrp1, fidDfltT, fidDflt]
  c0_hsteps_nogrp
  refine wp_join_state (ts := [.bool]) (α := Bool × List (BitVec 32)) (fun x => (x.1, ()))
    (fun x mk => FidCoreInv scr0 mv nc x.2 ∧ (FullMem c (m8ScrSt s x.2) ⋆ R) mk)
    (fun _ ⟨ch'', scr'⟩ mk ⟨hik', hmk'⟩ => by
      c0_hsteps!; exact hJcid (ch'', ()) mk ⟨scr', hik', hmk'⟩)
    (fun Jl0 hJl0 => by
      c0_hsplit
      · clear hc; c0_hsteps_nogrp
        refine wp_loop_group (ts := [.bool, i32])
          (fun remj (chj, j, ()) mj => ∃ scrj : List (BitVec 32),
            FidCoreInv scr0 mv nc scrj ∧ j.toNat ≤ sz_c.toNat ∧ remj = sz_c.toNat - j.toNat ∧
            (FullMem c (m8ScrSt s scrj) ⋆ R) mj) ?_ ?_
        · rintro Lj remj ⟨chj, j, ⟨⟩⟩ mj hLj ⟨scrj, hikj, hj_le, rfl, hmj⟩
          have hlj : scrj.length = scr0.length := hikj.2.1
          c0_hsplit
          · have hj_lt : j.toNat < sz_c.toNat := by c0_bound
            have hj1 : (j + 1#32).toNat = j.toNat + 1 := m8_bv32_add1_toNat hj_lt (by omega)
            have har_e := fid_k6_off_add2 (mv := mv) (k := 45) (x := off_c) (y := j)
              hmv_hi (by decide) (by omega)
            have har_lt : ((4224 + 45 * mv + off_c + j).setWidth 64).toNat < scrj.length := by
              rw [hlj, har_e]; omega
            let lv := (scrj[((4224 + 45 * mv + off_c + j).setWidth 64).toNat]'har_lt) >>> (1 : Nat)
            c0_hsteps_nogrp
            refine wp_join_state (ts := [.bool]) (α := Bool × List (BitVec 32))
              (fun x => (x.1, ()))
              (fun x mk => FidCoreInv scr0 mv nc x.2 ∧ (FullMem c (m8ScrSt s x.2) ⋆ R) mk)
              (fun _ ⟨chj', scrj'⟩ mj' ⟨hikj', hmj'⟩ => by
                c0_hsteps!; exact hLj (sz_c.toNat - (j + 1#32).toNat) (chj', j + 1#32, ()) mj'
                  (by omega) ⟨scrj', hikj', by omega, rfl, hmj'⟩)
              (fun Jk hJk => by
                c0_hsplit
                · have hlv_lt : lv.toNat < nv.toNat := by
                    have hc' := hc; fid_norm_ofnat
                    simp (disch := fid_omega) only [bv_c0, Nat.reducePow, Nat.reduceMod] at hc'
                    have har_lt' : 4224 + 45 * mv.toNat + off_c.toNat + j.toNat < 4294967296 := by
                      omega
                    have har_i : (4224 + 45 * mv.toNat + off_c.toNat + j.toNat) %
                        4294967296 = ((4224 + 45 * mv + off_c + j).setWidth 64).toNat := by
                      rw [har_e, Nat.mod_eq_of_lt har_lt']
                    rw [m8_k6_get_congr har_i _ har_lt, ← m8_bv32_lshr1_toNat] at hc'
                    exact hc'
                  clear hc
                  have hlv_e := fid_k6_off_add0 (x := lv) (by omega)
                  have hlv_b : (((4224 : BitVec 32) + lv).setWidth 64).toNat < scrj.length := by
                    rw [hlj, hlv_e]; omega
                  c0_hsplit
                  · have hrs_e := fid_k6_off_add1 (mv := mv) (x := lv) hmv_hi (by omega)
                    have hrs_b : ((4224 + mv + lv).setWidth 64).toNat < scrj.length := by
                      rw [hlj, hrs_e]; exact fidCore_1_lt (by omega) hmv_lo hbge
                    c0_hsteps_nogrp
                    refine wp_join_state (ts := [.bool]) (α := Bool × List (BitVec 32))
                      (fun x => (x.1, ()))
                      (fun x mk => FidCoreInv scr0 mv nc x.2 ∧ (FullMem c (m8ScrSt s x.2) ⋆ R) mk)
                      (fun _ ⟨ch9, scr9⟩ m9 ⟨hik9, hm9⟩ => by
                        c0_hsteps!; exact hJk (ch9, scr9) m9 ⟨hik9, hm9⟩)
                      (fun J9 hJ9 => by
                        let r0 := scrj[((4224 + mv + lv).setWidth 64).toNat]'hrs_b
                        c0_hsplit
                        · have hr0_lt : r0.toNat < nc.toNat := by
                            have hc' := hc; fid_norm_ofnat
                            simp (disch := fid_omega) only
                              [bv_c0, Nat.reducePow, Nat.reduceMod] at hc'
                            have har_lt' :
                                4224 + 45 * mv.toNat + off_c.toNat + j.toNat < 4294967296 := by
                              omega
                            have har_i : (4224 + 45 * mv.toNat + off_c.toNat + j.toNat) %
                                4294967296 = ((4224 + 45 * mv + off_c + j).setWidth 64).toNat := by
                              rw [har_e, Nat.mod_eq_of_lt har_lt']
                            have hsum_lt : 4224 + mv.toNat + lv.toNat < 4294967296 := by omega
                            have hrs_i : (4224 + mv.toNat +
                                (scrj[(4224 + 45 * mv.toNat + off_c.toNat + j.toNat) %
                                  4294967296]'(by rw [har_i]; exact har_lt)).toNat / 2) %
                                4294967296 = ((4224 + mv + lv).setWidth 64).toNat := by
                              rw [m8_k6_get_congr har_i _ har_lt, ← m8_bv32_lshr1_toNat, hrs_e,
                                Nat.mod_eq_of_lt hsum_lt]
                            rw [m8_k6_get_congr hrs_i _ hrs_b] at hc'; exact hc'
                          clear hc
                          have hmr_e := fid_k6_off_add (mv := mv) (k := 33) (x := r0)
                            hmv_hi (by decide) (by omega)
                          have hmr_b : ((4224 + 33 * mv + r0).setWidth 64).toNat < scrj.length := by
                            rw [hlj, hmr_e]; exact fidCore_k_lt 33 (by omega) hmv_lo hbge
                          c0_hsplit
                          · c0_hsteps!; refine hJ9 (true, _) _
                              ⟨fidCoreInv_set_meta_pres h4214 hmv_eq hnc_le hikj hr0_lt hmr_e hmr_b
                                (m8_km_core_or_pres _), hm⟩
                          · c0_hsteps!; exact hJ9 (chj, scrj) mj ⟨hikj, hmj⟩
                        · c0_hsteps!; exact hJ9 (chj, scrj) mj ⟨hikj, hmj⟩)
                  · c0_hsteps!; exact hJk (chj, scrj) mj ⟨hikj, hmj⟩
                · c0_hsteps!; exact hJk (chj, scrj) mj ⟨hikj, hmj⟩)
          · c0_hsteps!; exact hJl0 (chj, scrj) mj ⟨hikj, hmj⟩
        · intro Lj hLj; c0_hsteps!; exact hLj sz_c.toNat (ch_c, 0#32, ()) mc
            ⟨scrc, hikc, Nat.zero_le _, by simp, hmc⟩
      · c0_hsteps!; exact hJl0 (ch_c, scrc) mc ⟨hikc, hmc⟩)

theorem s13_fid_fixpoint_wp {Γ : Env} {c : FullCfg} {s : FullState}
    {scr0 : List (BitVec 32)} {mv nc nv acap x_i : BitVec 32} {R : Mem 64 → Prop}
    {Q : Post []} {X : XPost} {J2 : Cont [.bits 32]}
    (hscr_len : scr0.length = c.scratch_cap)
    (h4214 : 4214 < scr0.length) (hmv_d : scr0[4214]'h4214 = mv)
    (hmv_eq : scr0[4214]?.getD 0#32 = mv) (hmv_lo : 256 ≤ mv.toNat) (hmv_hi : mv.toNat ≤ 8192)
    (h4192 : 4192 < scr0.length) (hnv_d : scr0[4192]'h4192 = nv)
    (h4193 : 4193 < scr0.length) (hnc_d : scr0[4193]'h4193 = nc)
    (hnc_eq : scr0[4193]?.getD 0#32 = nc) (hnc_le : nc.toNat ≤ 4 * mv.toNat)
    (h4207 : 4207 < scr0.length) (hac_d : scr0[4207]'h4207 = acap)
    (hac_eq : scr0[4207]?.getD 0#32 = acap)
    (hnv_le : nv.toNat ≤ mv.toNat) (hbge : 4224 + 45 * mv.toNat ≤ scr0.length)
    (hlen_scr : 4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length) (hcap_lt : scr0.length < 2 ^ 30)
    (hRet : ∀ scrp mp, FidCoreInv scr0 mv nc scrp → scrp.length = c.scratch_cap →
      (FullMem c (m8ScrSt s scrp) ⋆ R) mp → Q () mp)
    {scr2 : List (BitVec 32)} {m2 : Mem 64}
    (hik2 : FidCoreInv scr0 mv nc scr2) (hm2 : (FullMem c (m8ScrSt s scr2) ⋆ R) m2) :
    wp Γ Q X (s13FidFixE c.hdr c.pScratchBuf mv nc nv acap x_i J2) m2 := by
  let invB : Bool × List (BitVec 32) → Mem 64 → Prop := fun x mk =>
    FidCoreInv scr0 mv nc x.2 ∧ (FullMem c (m8ScrSt s x.2) ⋆ R) mk
  dsimp only [s13FidFixE, s13FidPhase2E, full_k6_core_fid_body, fSLet, fSLd, fSLd64, fSJF,
    fSGrp1, fidDfltT, fidDflt]
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32, .bool])
    (fun rem (pass, chg, ()) mp => ∃ scrp : List (BitVec 32), FidCoreInv scr0 mv nc scrp ∧
      pass.toNat ≤ nc.toNat ∧ rem = (if chg then nc.toNat - pass.toNat else 0) ∧
      (FullMem c (m8ScrSt s scrp) ⋆ R) mp)
    ?_ (fun Lp hLp => by
      c0_hsteps!; exact hLp nc.toNat (0#32, true, ()) m2 ⟨scr2, hik2, Nat.zero_le _, by simp, hm2⟩)
  rintro Lp rem ⟨pass, chg, ⟨⟩⟩ mp hLp ⟨scrp, hikp, hpass_le, rfl, hmp⟩
  have hfin_p : Q () mp := hRet scrp mp hikp (hikp.2.1.trans hscr_len) hmp
  c0_hsplit
  · have hchg_t : chg = true := hc
    c0_hsplit
    · have hpass_lt : pass.toNat < nc.toNat := hc
      have hp1 : (pass + 1#32).toNat = pass.toNat + 1 := m8_bv32_add1_toNat hpass_lt (by omega)
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [.bool, i32])
        (fun rem_c (chg_c, cid, ()) mc => ∃ scrc : List (BitVec 32),
          FidCoreInv scr0 mv nc scrc ∧ cid.toNat ≤ nc.toNat ∧ rem_c = cid.toNat ∧
          (FullMem c (m8ScrSt s scrc) ⋆ R) mc)
        ?_ (fun Lc hLc => by
          c0_hsteps!; exact hLc nc.toNat (false, nc, ()) mp ⟨scrp, hikp, Nat.le_refl _, rfl, hmp⟩)
      rintro Lc rem_c ⟨chg_c, cid, ⟨⟩⟩ mc hLc ⟨scrc, hikc, hcid_le, rfl, hmc⟩
      have hlc : scrc.length = scr0.length := hikc.2.1
      c0_hsplit
      · have hcid_pos : 0 < cid.toNat := hc; clear hc
        have hcid1 : (cid - 1#32).toNat = cid.toNat - 1 := m8_bv32_sub1_toNat hcid_pos
        let cid' := cid - 1#32
        have hcid'_lt : cid'.toNat < nc.toNat := by dsimp only [cid']; rw [hcid1]; omega
        have hcm_e := fid_k6_off_add (mv := mv) (k := 33) (x := cid') hmv_hi (by decide) (by omega)
        have hcm_lt : ((4224 + 33 * mv + cid').setWidth 64).toNat < scrc.length := by
          rw [hlc, hcm_e]; omega
        let cmeta := scrc[((4224 + 33 * mv + cid').setWidth 64).toNat]'hcm_lt
        c0_hsteps_nogrp
        refine wp_join_state (ts := [.bool]) (α := Bool × List (BitVec 32))
          (fun x => (x.1, ())) invB
          (fun _ ⟨chgj, scrj⟩ mj ⟨hikj, hmj⟩ => by
            c0_hsteps!; exact hLc cid'.toNat (chgj, cid', ()) mj
              (by dsimp only [cid']; rw [hcid1]; omega) ⟨scrj, hikj, by omega, rfl, hmj⟩)
          (fun Jc hJc => by
            c0_hsplit
            · have hco_e := fid_k6_off_add (mv := mv) (k := 29) (x := cid')
                hmv_hi (by decide) (by omega)
              have hco_lt : ((4224 + 29 * mv + cid').setWidth 64).toNat < scrc.length := by
                rw [hlc, hco_e]; omega
              let off := scrc[((4224 + 29 * mv + cid').setWidth 64).toNat]'hco_lt
              let sz := cmeta &&& 0xFFFF#32
              have hcm_bnd : 4224 + 33 * mv.toNat + (cid.toNat - 1) < 4294967296 := by
                dsimp only [cid'] at hcm_e; rw [hcid1] at hcm_e; omega
              have hco_bnd : 4224 + 29 * mv.toNat + (cid.toNat - 1) < 4294967296 := by
                dsimp only [cid'] at hco_e; rw [hcid1] at hco_e; omega
              have hcm_idx : (4224 + 33 * mv.toNat + (4294967296 - 1 + cid.toNat)) %
                  4294967296 = ((4224 + 33 * mv + cid').setWidth 64).toNat := by
                rw [hcm_e]; dsimp only [cid']; rw [hcid1]
                exact s13f_sub1_mod32 _ _ hcid_pos hcm_bnd
              have hco_idx : (4224 + 29 * mv.toNat + (4294967296 - 1 + cid.toNat)) %
                  4294967296 = ((4224 + 29 * mv + cid').setWidth 64).toNat := by
                rw [hco_e]; dsimp only [cid']; rw [hcid1]
                exact s13f_sub1_mod32 _ _ hcid_pos hco_bnd
              have hcm_get : scrc[(4224 + 33 * mv.toNat + (4294967296 - 1 + cid.toNat)) %
                  4294967296]'(by rw [hcm_idx]; exact hcm_lt) = cmeta :=
                m8_k6_get_congr hcm_idx _ _
              have hsz_le : sz.toNat ≤ 65535 := m8_and_ffff_le cmeta
              have hcl_c := fidCore_clause_ok_bnds h4214 hmv_eq h4193 hnc_eq h4207 hac_eq
                hmv_hi hnc_le hikc hcid'_lt hco_e hcm_e hco_lt hcm_lt
              have hoff_g : scrc[(4224 + 29 * mv.toNat + (4294967296 - 1 + cid.toNat)) %
                  4294967296]'(by rw [hco_idx]; exact hco_lt) = off :=
                m8_k6_get_congr hco_idx _ _
              c0_hsteps_nogrp
              refine wp_join_state (ts := [.bool]) (α := Bool × List (BitVec 32))
                (fun x => (x.1, ())) invB
                (fun _ ⟨ch_c', scrc'⟩ mc' ⟨hikc', hmc'⟩ => by
                  dsimp only [Blocks.get]
                  change wp Γ Q X
                    (s13FidLvl0E c.hdr c.pScratchBuf mv nc nv acap off sz ch_c' J2
                      (fun xs mc'' => Jc xs mc'')) mc'
                  exact s13_fid_lvl0_lits_wp hscr_len h4214 hmv_d hmv_eq hmv_lo hmv_hi h4192 hnv_d
                    h4193 hnc_d hnc_le h4207 hac_d hac_eq hnv_le hbge hlen_scr hcap_lt hikc'
                    hcl_c.1 hsz_le hmc'
                    (fun ⟨ch'', ⟨⟩⟩ mk ⟨scrc'', hik'', hmk''⟩ =>
                      hJc (ch'', scrc'') mk ⟨hik'', hmk''⟩))
                (fun Jm hJm => by
                  c0_hsplit
                  · have hlrn : (cmeta &&& 0x40000000#32) ≠ 0#32 := by
                      intro heq; apply hc; rw [← hcm_get] at heq; exact heq
                    have hca_e := fid_k6_off_add (mv := mv) (k := 37) (x := cid') hmv_hi (by decide)
                      (by omega)
                    have hca_lt : ((4224 + 37 * mv + cid').setWidth 64).toNat < scrc.length := by
                      rw [hlc, hca_e]; omega
                    let na := scrc[((4224 + 37 * mv + cid').setWidth 64).toNat]'hca_lt
                    have hna_eq : (scrc[4224 + 37 * mv.toNat + cid'.toNat]?.getD 0#32) = na := by
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                      exact m8_k6_get_congr hca_e.symm _ _
                    have hosn_le : off.toNat + sz.toNat + na.toNat ≤ acap.toNat := by
                      have := hikc.1.clause_ok (cid := cid'.toNat) (by
                        rw [hikc.2.2.1 4193 h4193 (Or.inl (by omega)), hnc_eq]; exact hcid'_lt)
                      dsimp only at this
                      rw [fidCoreInv_mv h4214 hmv_eq hikc,
                        hikc.2.2.1 4207 h4207 (Or.inl (by omega)), hac_eq,
                        List.getElem?_eq_getElem (by omega), Option.getD_some,
                        List.getElem?_eq_getElem (by omega), Option.getD_some,
                        m8_k6_get_congr hco_e.symm _ _, m8_k6_get_congr hcm_e.symm _ _,
                        hna_eq] at this
                      exact this.2 hlrn
                    c0_hsteps_nogrp
                    refine wp_join_state (ts := [.bool]) (α := Bool × List (BitVec 32))
                      (fun x => (x.1, ())) invB
                      (fun _ x mj h => by c0_hsteps_nogrp; exact hJm x mj h)
                      (fun Jw hJw => by
                        c0_hsplit
                        · c0_hsteps_nogrp
                          refine wp_loop_group (ts := [.bool, i32])
                            (fun rj (chgj, j, ()) mj => ∃ scrj : List (BitVec 32),
                              FidCoreInv scr0 mv nc scrj ∧ j.toNat ≤ na.toNat ∧
                              rj = na.toNat - j.toNat ∧ (FullMem c (m8ScrSt s scrj) ⋆ R) mj) ?_ ?_
                          · rintro Lj rem_j ⟨chgj, j, ⟨⟩⟩ mj hLj ⟨scrj, hikj, hj_le, rfl, hmj⟩
                            have hlj : scrj.length = scr0.length := hikj.2.1
                            c0_hsplit
                            · have hj_lt : j.toNat < na.toNat := by
                                have hc' := hc; clear hc
                                have hca_idx : (4224 + 37 % 2 ^ 32 * mv.toNat +
                                    (2 ^ 32 - (1#32).toNat + cid.toNat)) % 2 ^ 32 =
                                    ((4224 + 37 * mv + cid').setWidth 64).toNat := by
                                  rw [hca_e]; dsimp only [cid']
                                  rw [hcid1, show (1#32 : BitVec 32).toNat = 1 from rfl,
                                    show 37 % 2 ^ 32 = 37 from rfl,
                                    show (2 ^ 32 : Nat) = 4294967296 from rfl]
                                  exact s13f_sub1_mod32 _ _ hcid_pos (by omega)
                                exact (congrArg BitVec.toNat
                                  (m8_k6_get_congr hca_idx _ hca_lt)) ▸ hc'
                              have hj1 : (j + 1#32).toNat = j.toNat + 1 :=
                                m8_bv32_add1_toNat hj_lt (by omega)
                              have har_e := fid_k6_off_add3 (mv := mv) (k := 45)
                                (x := off) (y := sz) (z := j) hmv_hi (by decide) (by omega)
                              have har_lt :
                                  ((4224 + 45 * mv + off + sz + j).setWidth 64).toNat <
                                    scrj.length := by rw [hlj, har_e]; omega
                              let ant :=
                                scrj[((4224 + 45 * mv + off + sz + j).setWidth 64).toNat]'har_lt
                              c0_hsteps_nogrp
                              refine wp_join_state (ts := [.bool]) (α := Bool × List (BitVec 32))
                                (fun x => (x.1, ())) invB
                                (fun _ ⟨chgk, scrk⟩ mk ⟨hikk, hmk⟩ => by
                                  c0_hsteps_nogrp
                                  exact hLj (na.toNat - (j + 1#32).toNat) (chgk, j + 1#32, ())
                                    mk (by omega) ⟨scrk, hikk, by omega, rfl, hmk⟩)
                                (fun Jk hJk => by
                                  c0_hsplit
                                  · have hant_lt : ant.toNat < nc.toNat := by
                                      have hc' := hc; clear hc
                                      have hco_raw : (4224 + 29 % 2 ^ 32 * mv.toNat +
                                          (2 ^ 32 - (1#32).toNat + cid.toNat)) % 2 ^ 32 =
                                          ((4224 + 29 * mv + cid').setWidth 64).toNat := by
                                        rw [hco_e]; dsimp only [cid']
                                        rw [hcid1, show (1#32 : BitVec 32).toNat = 1 from rfl,
                                          show 29 % 2 ^ 32 = 29 from rfl,
                                          show (2 ^ 32 : Nat) = 4294967296 from rfl]
                                        exact s13f_sub1_mod32 _ _ hcid_pos (by omega)
                                      have hcm_raw : (4224 + 33 % 2 ^ 32 * mv.toNat +
                                          (2 ^ 32 - (1#32).toNat + cid.toNat)) % 2 ^ 32 =
                                          ((4224 + 33 * mv + cid').setWidth 64).toNat := by
                                        rw [hcm_e]; dsimp only [cid']
                                        rw [hcid1, show (1#32 : BitVec 32).toNat = 1 from rfl,
                                          show 33 % 2 ^ 32 = 33 from rfl,
                                          show (2 ^ 32 : Nat) = 4294967296 from rfl]
                                        exact s13f_sub1_mod32 _ _ hcid_pos (by omega)
                                      have hco_gt : scrc[(4224 + 29 % 2 ^ 32 * mv.toNat +
                                          (2 ^ 32 - (1#32).toNat + cid.toNat)) % 2 ^ 32]'(by
                                            rw [hco_raw]; exact hco_lt) = off :=
                                        m8_k6_get_congr hco_raw _ hco_lt
                                      have hcm_gt : scrc[(4224 + 33 % 2 ^ 32 * mv.toNat +
                                          (2 ^ 32 - (1#32).toNat + cid.toNat)) % 2 ^ 32]'(by
                                            rw [hcm_raw]; exact hcm_lt) = cmeta :=
                                        m8_k6_get_congr hcm_raw _ hcm_lt
                                      have har_raw : (4224 + 45 % 2 ^ 32 * mv.toNat +
                                          (scrc[(4224 + 29 % 2 ^ 32 * mv.toNat +
                                            (2 ^ 32 - (1#32).toNat + cid.toNat)) % 2 ^ 32]'(by
                                              rw [hco_raw]; exact hco_lt)).toNat +
                                          (scrc[(4224 + 33 % 2 ^ 32 * mv.toNat +
                                            (2 ^ 32 - (1#32).toNat + cid.toNat)) % 2 ^ 32]'(by
                                              rw [hcm_raw]; exact hcm_lt)).toNat % 65536 +
                                          j.toNat) % 2 ^ 32 =
                                          ((4224 + 45 * mv + off + sz + j).setWidth 64).toNat := by
                                        rw [hco_gt, hcm_gt, har_e]
                                        rw [← s13f_and_ffff cmeta]
                                        change (4224 + 45 % 2 ^ 32 * mv.toNat + off.toNat +
                                          sz.toNat + j.toNat) % 2 ^ 32 =
                                          4224 + 45 * mv.toNat + off.toNat + sz.toNat + j.toNat
                                        rw [show 45 % 2 ^ 32 = 45 from rfl,
                                          Nat.mod_eq_of_lt (by omega)]
                                      exact (congrArg BitVec.toNat
                                        (m8_k6_get_congr har_raw _ har_lt)) ▸ hc'
                                    clear hc
                                    have hma_e := fid_k6_off_add (mv := mv) (k := 33) (x := ant)
                                      hmv_hi (by decide) (by omega)
                                    have hma_lt :
                                        ((4224 + 33 * mv + ant).setWidth 64).toNat <
                                          scrj.length := by
                                      rw [hlj, hma_e]; exact fidCore_k_lt 33 (by omega) hmv_lo hbge
                                    c0_hsplit
                                    · c0_hsteps_nogrp; refine hJk (true, _) _
                                        ⟨fidCoreInv_set_meta_pres h4214 hmv_eq hnc_le hikj hant_lt
                                          hma_e hma_lt (m8_km_core_or_pres _), by assumption⟩
                                    · c0_hsteps_nogrp; exact hJk (chgj, scrj) mj ⟨hikj, hmj⟩
                                  · c0_hsteps_nogrp; exact hJk (chgj, scrj) mj ⟨hikj, hmj⟩)
                            · c0_hsteps_nogrp; exact hJw (chgj, scrj) mj ⟨hikj, hmj⟩
                          · intro Lj hLj; c0_hsteps_nogrp; exact hLj na.toNat (chg_c, 0#32, ()) mc
                              ⟨scrc, hikc, Nat.zero_le _, rfl, hmc⟩
                        · c0_hsteps_nogrp; exact hJw (chg_c, scrc) mc ⟨hikc, hmc⟩)
                  · c0_hsteps_nogrp; exact hJm (chg_c, scrc) mc ⟨hikc, hmc⟩)
            · c0_hsteps_nogrp; exact hJc (chg_c, scrc) mc ⟨hikc, hmc⟩)
      · c0_hsteps_nogrp; exact hLp (if chg_c then nc.toNat - (pass + 1#32).toNat else 0)
          (pass + 1#32, chg_c, ()) mc (by subst hchg_t; cases chg_c <;> simp [hp1] <;> omega)
          ⟨scrc, hikc, by omega, rfl, hmc⟩
    · c0_hsteps_nogrp; exact hfin_p
  · c0_hsteps_nogrp; exact hfin_p

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1
