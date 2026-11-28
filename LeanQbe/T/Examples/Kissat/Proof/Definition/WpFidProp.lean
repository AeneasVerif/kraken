/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidBasic

/-!
# Kissat Fidelity BVE WP Proofs — `full_k6_prop_fid_wp`

`CanonicalEnv`-clean `Func.wp` proof for `full_k6_prop_fid` (`0` legacy `Full*` imports;
zero `@[expose]` on theorems; every decl `<= 450` LOC; `<= 100` cols).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Definition
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open Kraken.Bedrock2.Test

open scoped FidK6Tactics M8K6bTactics FidK6DefTactics

public section

local macro_rules
  | `(tactic| c0_bound) => `(tactic| first | assumption | rfl | decide | omega | fid_omega)

/-! ## 1. `FidPropKeep` Preservation & Call Helpers -/

private def FidPropKeep (scr0 : List (BitVec 32)) (mv : Nat) (scr : List (BitVec 32)) : Prop :=
  scr.length = scr0.length ∧
  (∀ i, i < 4195 → scr[i]? = scr0[i]?) ∧
  (∀ i, 4199 ≤ i → i < 4204 → scr[i]? = scr0[i]?) ∧
  (∀ i, 4205 ≤ i → i < 4224 → scr[i]? = scr0[i]?) ∧
  (∀ i, 4224 + 2 * mv ≤ i → i < 4224 + 5 * mv → scr[i]? = scr0[i]?) ∧
  (∀ i, 4224 + 7 * mv ≤ i → i < 4224 + 9 * mv → scr[i]? = scr0[i]?) ∧
  (∀ i, 4224 + 29 * mv ≤ i → i < 4224 + 45 * mv → scr[i]? = scr0[i]?)

private theorem fidPropKeep_refl (scr0 : List (BitVec 32)) (mv : Nat) :
    FidPropKeep scr0 mv scr0 :=
  ⟨rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

private theorem fidPropKeep_set {scr0 scra : List (BitVec 32)} {mv idx : Nat}
    (hk : FidPropKeep scr0 mv scra) (v : BitVec 32)
    (hidx : (4195 ≤ idx ∧ idx < 4199) ∨ idx = 4204 ∨
      (4224 ≤ idx ∧ idx < 4224 + 2 * mv) ∨ (4224 + 5 * mv ≤ idx ∧ idx < 4224 + 7 * mv) ∨
      (4224 + 9 * mv ≤ idx ∧ idx < 4224 + 29 * mv) ∨ 4224 + 45 * mv ≤ idx) :
    FidPropKeep scr0 mv (scra.set idx v) := by
  refine ⟨by simp [hk.1], fun i hi => ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_,
    fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.1 i hi
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.1 i h1 h2
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.2.1 i h1 h2
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.2.2.1 i h1 h2
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.2.2.2.1 i h1 h2
  · rw [List.getElem?_set_ne (by omega)]; exact hk.2.2.2.2.2.2 i h1 h2

private theorem fidPropKeep_of_assign {c : FullCfg} {scr0 scra scrb : List (BitVec 32)}
    {mv : Nat} (hk : FidPropKeep scr0 mv scra) (h4214 : 4214 < scr0.length)
    (hmv_eq : scr0[4214]?.getD 0#32 = BitVec.ofNat 32 mv)
    (hmv_hi : mv ≤ 8192) (hlen : scr0.length = c.scratch_cap)
    (hbge : 4224 + 45 * mv ≤ scr0.length) (hlb : scrb.length = c.scratch_cap)
    (ha : ∀ idx < c.scratch_cap, idx ≠ 4197 → idx ≠ 4198 →
      (idx < 4224 ∨ 4224 + 2 * (scra[4214]?.getD 0#32).toNat ≤ idx) →
      (idx < 4224 + 5 * (scra[4214]?.getD 0#32).toNat ∨
        4224 + 7 * (scra[4214]?.getD 0#32).toNat ≤ idx) →
      (idx < 4224 + 9 * (scra[4214]?.getD 0#32).toNat ∨
        4224 + 11 * (scra[4214]?.getD 0#32).toNat ≤ idx) →
      scrb[idx]? = scra[idx]?) :
    FidPropKeep scr0 mv scrb := by
  have hmva : (scra[4214]?.getD 0#32).toNat = mv := by
    rw [hk.2.2.2.1 4214 (by omega) (by omega), hmv_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  rw [hmva] at ha
  have hs := hlen; have _ := h4214
  refine ⟨by rw [hlb, ← hlen], fun i hi => ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_,
    fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_⟩
  · rw [ha i (by omega) (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega))]; exact hk.2.1 i hi
  · rw [ha i (by omega) (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega))]; exact hk.2.2.1 i h1 h2
  · rw [ha i (by omega) (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega))]; exact hk.2.2.2.1 i h1 h2
  · rw [ha i (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega))
      (Or.inl (by omega))]; exact hk.2.2.2.2.1 i h1 h2
  · rw [ha i (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inl (by omega))]; exact hk.2.2.2.2.2.1 i h1 h2
  · rw [ha i (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega))]; exact hk.2.2.2.2.2.2 i h1 h2

private theorem fidPropKeep_bufOk {scr0 scra : List (BitVec 32)} {mv : BitVec 32}
    (hok : FidK6BufOk scr0) (_h4214 : 4214 < scr0.length) (hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (hk : FidPropKeep scr0 mv.toNat scra) :
    FidK6BufOk scra := by
  have hb := hok.base_ge; have hnc := hok.nc_le
  rw [hmv_eq] at hb hnc
  have hk_mv : scra[4214]? = scr0[4214]? := hk.2.2.2.1 4214 (by omega) (by omega)
  have hk_nc : scra[4193]? = scr0[4193]? := hk.2.1 4193 (by omega)
  have hk_al : scra[4206]? = scr0[4206]? := hk.2.2.2.1 4206 (by omega) (by omega)
  have hk_ac : scra[4207]? = scr0[4207]? := hk.2.2.2.1 4207 (by omega) (by omega)
  refine ⟨by rw [hk_mv]; exact hok.mv_lo, by rw [hk_mv]; exact hok.mv_hi,
    by rw [hk_mv, hk_ac, hk.1]; exact hok.length_ge, by rw [hk.1]; exact hok.length_lt,
    by rw [hk_nc, hk_mv]; exact hok.nc_le, by rw [hk_al, hk_ac]; exact hok.alen_le,
    fun cid hcid => ?_⟩
  rw [hk_nc] at hcid
  have hcl := hok.clause_ok (cid := cid) hcid
  rw [hmv_eq] at hcl
  have hcid_4 : cid < 4 * mv.toNat := Nat.lt_of_lt_of_le hcid hnc
  have hk_off : scra[4224 + 29 * mv.toNat + cid]? = scr0[4224 + 29 * mv.toNat + cid]? :=
    hk.2.2.2.2.2.2 _ (by omega) (by omega)
  have hk_meta : scra[4224 + 33 * mv.toNat + cid]? = scr0[4224 + 33 * mv.toNat + cid]? :=
    hk.2.2.2.2.2.2 _ (by omega) (by omega)
  have hk_aux : scra[4224 + 37 * mv.toNat + cid]? = scr0[4224 + 37 * mv.toNat + cid]? :=
    hk.2.2.2.2.2.2 _ (by omega) (by omega)
  dsimp only at hcl ⊢
  rw [hk_mv, hmv_eq, hk_ac, hk_off, hk_meta, hk_aux]
  exact hcl

private theorem fidPropKeep_get {scr0 scra : List (BitVec 32)} {mv i : Nat}
    (hk : FidPropKeep scr0 mv scra) (hi : i < scr0.length)
    (hr : i < 4195 ∨ (4199 ≤ i ∧ i < 4204) ∨ (4205 ≤ i ∧ i < 4224) ∨
      (4224 + 2 * mv ≤ i ∧ i < 4224 + 5 * mv) ∨ (4224 + 7 * mv ≤ i ∧ i < 4224 + 9 * mv) ∨
      (4224 + 29 * mv ≤ i ∧ i < 4224 + 45 * mv)) :
    scra[i]'(by rw [hk.1]; exact hi) = scr0[i]'hi := by
  rw [← Option.some_inj, ← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem]
  rcases hr with h | h | h | h | h | h
  · exact hk.2.1 i h
  · exact hk.2.2.1 i h.1 h.2
  · exact hk.2.2.2.1 i h.1 h.2
  · exact hk.2.2.2.2.1 i h.1 h.2
  · exact hk.2.2.2.2.2.1 i h.1 h.2
  · exact hk.2.2.2.2.2.2 i h.1 h.2

private theorem fidProp_k_lt (k : Nat) {x : Nat} {mv : BitVec 32} {len : Nat}
    (hx : x < 8 * mv.toNat) (_hmv : 256 ≤ mv.toNat)
    (hbge : 4224 + 45 * mv.toNat ≤ len) (hk : k ≤ 21 := by decide) :
    4224 + k * mv.toNat + x < len := by
  have hk_le : k * mv.toNat ≤ 21 * mv.toNat := Nat.mul_le_mul_right mv.toNat hk
  omega

private theorem fidProp_call_add_ticks {Γ : Env} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post [i32]} {X : XPost} {scr0 scra : List (BitVec 32)}
    {mv rv : BitVec 32} {delta : BitVec 64} {ma : Mem 64}
    (hTicks : Γ.Has "full_fid_k6_add_ticks" fidK6AddTicksSpec)
    (hlen : FullState.LengthsOk c s) (hscr_len : scr0.length = c.scratch_cap)
    (_h4214 : 4214 < scr0.length) (_hmv_eq : scr0[4214]?.getD 0#32 = mv)
    (hmin : 15744 ≤ scr0.length) (hk : FidPropKeep scr0 mv.toNat scra)
    (hma : (FullMem c (m8ScrSt s scra) ⋆ R) ma)
    (hcont : ∀ (scrb : List (BitVec 32)) (mb : Mem 64),
      FidPropKeep scr0 mv.toNat scrb → scrb[4196]? = scra[4196]? →
      (FullMem c (m8ScrSt s scrb) ⋆ R) mb → Q (rv, ()) mb) :
    wp Γ Q X
      (Expr.call (as := [i64, i64]) (bs := []) "full_fid_k6_add_ticks"
        (Arg.var c.hdr, Arg.var delta, PUnit.unit) fun _ =>
        Expr.ret (Arg.var rv, ())) ma := by
  fid_call hTicks
  refine fidK6AddTicksSpec_intro rfl (m8ScrSt_lengthsOk hlen (hk.1.trans hscr_len))
    (by omega) hma (fun tk' m' hm' => ?_)
  c0_hsteps!
  have hkeep := fidPropKeep_set hk tk' (Or.inr (Or.inl rfl))
  have h4196 : (scra.set 4204 tk')[4196]? = scra[4196]? := List.getElem?_set_ne (by decide)
  exact hcont _ m' hkeep h4196 hm'

private theorem fidProp_call_assign {Γ : Env} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {Q : Post [i32]} {X : XPost} {scr0 scra : List (BitVec 32)}
    {mv lit rsn_cid : BitVec 32} {ma : Mem 64} {J : Cont []}
    (hAssign : Γ.Has "full_k6_assign_fid" fidK6AssignSpec)
    (hlen : FullState.LengthsOk c s) (hok : FidK6BufOk scr0)
    (hscr_len : scr0.length = c.scratch_cap) (h4214 : 4214 < scr0.length)
    (hmv_eq : scr0[4214]?.getD 0#32 = mv) (hmv_hi : mv.toNat ≤ 8192)
    (hbge : 4224 + 45 * mv.toNat ≤ scr0.length)
    (hk : FidPropKeep scr0 mv.toNat scra) (hma : (FullMem c (m8ScrSt s scra) ⋆ R) ma)
    (hcont : ∀ (scrb : List (BitVec 32)) (mb : Mem 64),
      FidPropKeep scr0 mv.toNat scrb → scrb[4196]? = scra[4196]? →
      (FullMem c (m8ScrSt s scrb) ⋆ R) mb → wp Γ Q X (Expr.jump J ()) mb) :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i32]) (bs := []) "full_k6_assign_fid"
        (Arg.var c.hdr, Arg.var lit, Arg.var rsn_cid, PUnit.unit) fun _ =>
        Expr.jump J ()) ma := by
  have hmva_b : scra[4214]?.getD 0#32 = mv := by
    rw [hk.2.2.2.1 4214 (by omega) (by omega), hmv_eq]
  have hmva : (scra[4214]?.getD 0#32).toNat = mv.toNat := congrArg BitVec.toNat hmva_b
  fid_call hAssign
  refine fidK6AssignSpec_intro rfl (m8ScrSt_lengthsOk hlen (hk.1.trans hscr_len))
    (fidPropKeep_bufOk hok h4214 hmv_eq hk) hma (fun scr' m' hlen' hpres hm' => ?_)
  have hkeep := fidPropKeep_of_assign hk h4214
    (by rw [hmv_eq]; exact (BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])).symm)
    hmv_hi hscr_len hbge hlen' hpres
  have h4196 : scr'[4196]? = scra[4196]? := by
    have h4196' := hpres 4196 (by omega) (by decide) (by decide) (Or.inl (by decide))
    dsimp only [m8ScrSt] at h4196'; rw [hmva] at h4196'
    exact h4196' (Or.inl (by omega)) (Or.inl (by omega))
  exact hcont scr' m' hkeep h4196 hm'

/-! ## 2. Long-Clause Replacement Block (`fidPropReplExpr` & `fidProp_repl_wp`) -/

private def fidPropReplExpr (pScr cHdr : BitVec 64)
    (mv nv nc flit cid prev next wsteps' other slot off sz c_id : BitVec 32)
    (ticks1 props' : BitVec 64)
    (J_loop : Cont [i64, i64, i32, i32, i32]) : Expr Val Cont [i32] :=
  let o_vals : BitVec 32 := 4224 + 9 * mv
  let o_whead : BitVec 32 := 4224 + 11 * mv
  let o_wnext : BitVec 32 := 4224 + 13 * mv
  let o_wblk : BitVec 32 := 4224 + 21 * mv
  let o_arena : BitVec 32 := 4224 + 45 * mv
  Expr.group (sig := [[i32, i32, i32]]) (fun _ =>
    Blocks.cons (fun p_122 =>
      Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool (by decide),
                  args := (Arg.var p_122.snd.fst, Arg.imm 4294967295, ()) } fun p_123 =>
      Expr.jnz (Arg.var p_123.fst)
        (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                     args := (Arg.var o_arena, Arg.var off, ()) } fun p =>
         Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                     args := (Arg.var p.fst, Arg.var slot, ()) } fun p =>
         Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                     args := (Arg.var p.fst, ()) } fun p =>
         Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                     args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
         Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                     args := (Arg.var pScr, Arg.var p.fst, ()) } fun p =>
         Expr.store (Arg.var (t := i32) p_122.snd.snd.fst) (Arg.var p.fst)
           (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                        args := (Arg.var o_arena, Arg.var off, ()) } fun p =>
            Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                        args := (Arg.var p.fst, Arg.var p_122.snd.fst, ()) } fun p =>
            Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                        args := (Arg.var p.fst, ()) } fun p =>
            Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                        args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
            Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var pScr, Arg.var p.fst, ()) } fun p =>
            Expr.store (Arg.var (t := i32) flit) (Arg.var p.fst)
              (Expr.group (sig := [[]]) (fun _ =>
                 Blocks.cons (fun _ =>
                   Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                args := (Arg.var o_wblk, Arg.var cid, ()) } fun p =>
                   Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                               args := (Arg.var p.fst, ()) } fun p =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                               args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                               args := (Arg.var pScr, Arg.var p.fst, ()) } fun p =>
                   Expr.store (Arg.var (t := i32) other) (Arg.var p.fst)
                     (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                  args := (Arg.var o_wnext, Arg.var cid, ()) } fun p =>
                      Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                  args := (Arg.var p.fst, ()) } fun p =>
                      Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                  args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                  args := (Arg.var pScr, Arg.var p.fst, ()) } fun p =>
                      Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                  args := (Arg.var o_whead, Arg.var p_122.snd.snd.fst, ()) }
                        fun p_124 =>
                      Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                  args := (Arg.var p_124.fst, ()) } fun p_125 =>
                      Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                  args := (Arg.var p_125.fst, Arg.imm 4, ()) } fun p_126 =>
                      Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                  args := (Arg.var pScr, Arg.var p_126.fst, ()) } fun p_127 =>
                      Expr.load i32 (Arg.var p_127.fst) fun ld_19 =>
                      Expr.store (Arg.var ld_19) (Arg.var p.fst)
                        (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                     args := (Arg.var o_whead, Arg.var p_122.snd.snd.fst, ()) }
                           fun p =>
                         Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                     args := (Arg.var p.fst, ()) } fun p =>
                         Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                     args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                         Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                     args := (Arg.var pScr, Arg.var p.fst, ()) } fun p =>
                         Expr.store (Arg.var (t := i32) cid) (Arg.var p.fst)
                           (Expr.jump J_loop (Arg.var ticks1, Arg.var props',
                             Arg.var prev, Arg.var next, Arg.var wsteps', ()))))) Blocks.nil)
                   fun Js =>
                 Expr.let_ { sig := [i32, i32], code := OpCode.shl i32,
                             args := (Arg.var nc, Arg.imm 1, ()) } fun p =>
                 Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.uge i32 Ty.bool
                               (by decide),
                             args := (Arg.var prev, Arg.var p.fst, ()) } fun p =>
                 Expr.jnz (Arg.var p.fst)
                   (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                args := (Arg.var o_whead, Arg.var flit, ()) } fun p =>
                    Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                args := (Arg.var p.fst, ()) } fun p =>
                    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                    Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                args := (Arg.var pScr, Arg.var p.fst, ()) } fun p =>
                    Expr.store (Arg.var (t := i32) next) (Arg.var p.fst) (Expr.jump Js.fst ()))
                   (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                args := (Arg.var o_wnext, Arg.var prev, ()) } fun p =>
                    Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                args := (Arg.var p.fst, ()) } fun p =>
                    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                    Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                args := (Arg.var pScr, Arg.var p.fst, ()) } fun p =>
                    Expr.store (Arg.var (t := i32) next) (Arg.var p.fst) (Expr.jump Js.fst ())))))
        (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                     args := (Arg.var o_wblk, Arg.var cid, ()) } fun p_124 =>
         Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                     args := (Arg.var p_124.fst, ()) } fun p_125 =>
         Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                     args := (Arg.var p_125.fst, Arg.imm 4, ()) } fun p_126 =>
         Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                     args := (Arg.var pScr, Arg.var p_126.fst, ()) } fun p_127 =>
         Expr.store (Arg.var (t := i32) other) (Arg.var p_127.fst)
           (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                        args := (Arg.var o_vals, Arg.var other, ()) } fun p_128 =>
            Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                        args := (Arg.var p_128.fst, ()) } fun p_129 =>
            Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                        args := (Arg.var p_129.fst, Arg.imm 4, ()) } fun p_130 =>
            Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var pScr, Arg.var p_130.fst, ()) } fun p_131 =>
            Expr.load i32 (Arg.var p_131.fst) fun ld =>
            Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
                        args := (Arg.var ld, Arg.imm 2, ()) } fun p_132 =>
            Expr.jnz (Arg.var p_132.fst)
              (Expr.let_ { sig := [i32], code := OpCode.sext 32 64,
                           args := (Arg.imm 4, ()) } fun p_133 =>
               Expr.let_ { sig := [i64, i64], code := OpCode.lshr i64,
                           args := (Arg.var props', Arg.var p_133.fst, ()) } fun p_134 =>
               Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                           args := (Arg.var ticks1, Arg.var p_134.fst, ()) } fun p_135 =>
               Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                           args := (Arg.var p_135.fst, Arg.imm 1, ()) } fun p_136 =>
               Expr.call (as := [i64, i64]) (bs := []) "full_fid_k6_add_ticks"
                 (Arg.var cHdr, Arg.var p_136.fst, PUnit.unit) fun _ =>
                 Expr.ret (Arg.var c_id, ()))
              (Expr.group (sig := [[]]) (fun _ =>
                 Blocks.cons (fun _ =>
                   Expr.jump J_loop (Arg.var ticks1, Arg.var props',
                     Arg.var cid, Arg.var next, Arg.var wsteps', ())) Blocks.nil) fun Js =>
               Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool
                             (by decide),
                           args := (Arg.var ld, Arg.imm 0, ()) } fun p_133 =>
               Expr.jnz (Arg.var p_133.fst)
                 (Expr.call (as := [i64, i32, i32]) (bs := []) "full_k6_assign_fid"
                    (Arg.var cHdr, Arg.var other, Arg.var c_id, PUnit.unit) fun _ =>
                    Expr.jump Js.fst ())
                 (Expr.jump Js.fst ()))))) Blocks.nil) fun Js =>
  Expr.group (sig := [[i32]]) (fun Js_3 =>
    Blocks.cons (fun p =>
      Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                  args := (Arg.var p.fst, Arg.var sz, ()) } fun p_122 =>
      Expr.jnz (Arg.var p_122.fst)
        (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                     args := (Arg.var o_arena, Arg.var off, ()) } fun p_123 =>
         Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                     args := (Arg.var p_123.fst, Arg.var p.fst, ()) } fun p_124 =>
         Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                     args := (Arg.var p_124.fst, ()) } fun p_125 =>
         Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                     args := (Arg.var p_125.fst, Arg.imm 4, ()) } fun p_126 =>
         Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                     args := (Arg.var pScr, Arg.var p_126.fst, ()) } fun p_127 =>
         Expr.load i32 (Arg.var p_127.fst) fun ld_19 =>
         Expr.group (sig := [[]]) (fun _ =>
           Blocks.cons (fun _ =>
             Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                         args := (Arg.var p.fst, Arg.imm 1, ()) } fun p =>
             Expr.jump Js_3.fst (Arg.var p.fst, ())) Blocks.nil) fun Js_4 =>
         Expr.let_ { sig := [i32, i32], code := OpCode.shl i32,
                     args := (Arg.var nv, Arg.imm 1, ()) } fun p_128 =>
         Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                     args := (Arg.var ld_19, Arg.var p_128.fst, ()) } fun p_129 =>
         Expr.jnz (Arg.var p_129.fst)
           (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                        args := (Arg.var o_vals, Arg.var ld_19, ()) } fun p_130 =>
            Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                        args := (Arg.var p_130.fst, ()) } fun p_131 =>
            Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                        args := (Arg.var p_131.fst, Arg.imm 4, ()) } fun p_132 =>
            Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var pScr, Arg.var p_132.fst, ()) } fun p_133 =>
            Expr.load i32 (Arg.var p_133.fst) fun ld =>
            Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool (by decide),
                        args := (Arg.var ld, Arg.imm 2, ()) } fun p_134 =>
            Expr.jnz (Arg.var p_134.fst)
              (Expr.jump Js.fst (Arg.var p.fst, Arg.var p.fst, Arg.var ld_19, ()))
              (Expr.jump Js_4.fst ()))
           (Expr.jump Js_4.fst ()))
        (Expr.jump Js.fst (Arg.var p.fst, Arg.imm 4294967295, Arg.imm 0, ()))) Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 2, ())

private theorem fidProp_repl_wp (Γ : Env) (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (Q : Post [i32]) (X : XPost) (scr0 scra : List (BitVec 32))
    (flit cid prev next wsteps' other slot off sz c_id : BitVec 32)
    (ticks1 props' : BitVec 64) (J_loop : Cont [i64, i64, i32, i32, i32]) (ma : Mem 64)
    (hTicks : Γ.Has "full_fid_k6_add_ticks" fidK6AddTicksSpec)
    (hAssign : Γ.Has "full_k6_assign_fid" fidK6AssignSpec)
    (hlen : FullState.LengthsOk c s) (hok : FidK6BufOk scr0)
    (hscr_len : scr0.length = c.scratch_cap)
    (h4214 : 4214 < scr0.length) :
    let mv := scr0[4214]'h4214
    let nv := scr0[4192]'(by have := hok.base_ge; omega)
    let nc := scr0[4193]'(by have := hok.base_ge; omega)
    let acap := scr0[4207]'(by have := hok.base_ge; omega)
    256 ≤ mv.toNat → mv.toNat ≤ 8192 → nv.toNat ≤ mv.toNat → nc.toNat ≤ 4 * mv.toNat →
    4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length →
    4224 + 45 * mv.toNat ≤ scr0.length → scr0.length < 2 ^ 30 →
    flit.toNat < 2 * nv.toNat → cid.toNat < 2 * nc.toNat →
    other.toNat < 2 * nv.toNat → slot.toNat < 2 →
    2 ≤ sz.toNat → sz.toNat ≤ 65535 → off.toNat + sz.toNat ≤ acap.toNat →
    FidPropKeep scr0 mv.toNat scra → (FullMem c (m8ScrSt s scra) ⋆ R) ma →
    (∀ (scrb : List (BitVec 32)) (prev' : BitVec 32) (mb : Mem 64),
      FidPropKeep scr0 mv.toNat scrb → scrb[4196]? = scra[4196]? →
      (FullMem c (m8ScrSt s scrb) ⋆ R) mb →
      wp Γ Q X (Expr.jump J_loop (Arg.var ticks1, Arg.var props', Arg.var prev',
        Arg.var next, Arg.var wsteps', ())) mb) →
    (∀ (scrb : List (BitVec 32)) (mb : Mem 64),
      FidPropKeep scr0 mv.toNat scrb → (FullMem c (m8ScrSt s scrb) ⋆ R) mb →
      Q (c_id, ()) mb) →
    wp Γ Q X (fidPropReplExpr c.pScratchBuf c.hdr mv nv nc flit cid prev next wsteps' other
      slot off sz c_id ticks1 props' J_loop) ma := by
  intro mv nv nc acap hmv_lo hmv_hi hnv_le hnc_le hlen_scr hbge hcap_lt
    hflit hcid hother hslot hsz_ge hsz_le hos_le hka hma hJloop hQret
  have hmv_eq : scr0[4214]?.getD 0#32 = mv := m8_k6_get_eq h4214
  have hla : scra.length = scr0.length := hka.1
  have hmin : 15744 ≤ scr0.length := by omega
  dsimp only [fidPropReplExpr]
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [i32, i32, i32])
    (α := BitVec 32 × BitVec 32 × BitVec 32) (fun x => (x.1, x.2.1, x.2.2, ()))
    (fun x => x.2.1 = 4294967295#32 ∨
      (x.2.1.toNat < sz.toNat ∧ x.2.2.toNat < 2 * nv.toNat)) ?_ ?_
  · rintro _ ⟨_, r_j, cand⟩ hcand
    have hcand' : r_j = 4294967295#32 ∨ (r_j.toNat < sz.toNat ∧ cand.toNat < 2 * nv.toNat) :=
      hcand
    rcases hcand' with hrj_nil | ⟨hrj_lt, hcand_lt⟩
    · subst hrj_nil
      have hwb_e := fid_k6_off_add (mv := mv) (k := 21) (x := cid) hmv_hi (by decide)
        (by clear hka hma hJloop hQret; omega)
      have hwb_lt : ((4224 + 21 * mv + cid).setWidth 64).toNat < scra.length := by
        rw [hla, hwb_e]; exact fidProp_k_lt 21 (by omega) hmv_lo hbge
      have hva_e := fid_k6_off_add (mv := mv) (k := 9) (x := other) hmv_hi (by decide)
        (by clear hka hma hJloop hQret; omega)
      have hva_lt : ((4224 + 9 * mv + other).setWidth 64).toNat <
          (scra.set ((4224 + 21 * mv + cid).setWidth 64).toNat other).length := by
        rw [List.length_set, hla, hva_e]; exact fidProp_k_lt 9 (by omega) hmv_lo hbge
      c0_hsteps_nogrp
      · c0_hsteps_nogrp
        exact fidProp_call_add_ticks hTicks hlen hscr_len h4214 hmv_eq hmin
          (fidPropKeep_set (idx := ((4224 + 21 * mv + cid).setWidth 64).toNat) hka other
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
              rw [hwb_e]; exact ⟨by omega, by omega⟩)))))))
          hm (fun scrb mb hkb _ hmb => hQret scrb mb hkb hmb)
      · c0_hsteps_nogrp
        refine wp_join0 (fun m' => ∃ scrb : List (BitVec 32), FidPropKeep scr0 mv.toNat scrb ∧
            scrb[4196]? = scra[4196]? ∧ (FullMem c (m8ScrSt s scrb) ⋆ R) m') ?_ ?_
        · rintro _ mb ⟨scrb, hkb, h4196, hmb⟩
          c0_hsteps!
          exact hJloop scrb cid mb hkb h4196 hmb
        · intro Jc hJc
          c0_hstraight
          have hk1 := fidPropKeep_set (idx := ((4224 + 21 * mv + cid).setWidth 64).toNat) hka
            other (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
              rw [hwb_e]; exact ⟨by omega, by omega⟩))))))
          have h4196_1 : (scra.set ((4224 + 21 * mv + cid).setWidth 64).toNat other)[4196]? =
              scra[4196]? := List.getElem?_set_ne (by rw [hwb_e]; omega)
          c0_hsplit
          · exact fidProp_call_assign hAssign hlen hok hscr_len h4214 hmv_eq hmv_hi hbge hk1 hm
              (fun scrb mb hkb h4196_2 hmb => by
                c0_hsteps!; exact hJc mb ⟨scrb, hkb, h4196_2.trans h4196_1, hmb⟩)
          · c0_hsteps!
            exact hJc m ⟨_, hk1, h4196_1, hm⟩
    · have har1_e := fid_k6_off_add2 (mv := mv) (k := 45) (x := off) (y := slot) hmv_hi
        (by decide) (by clear hka hma hJloop hQret; omega)
      have har1_lt : ((4224 + 45 * mv + off + slot).setWidth 64).toNat < scra.length := by
        rw [hla, har1_e]; omega
      have har2_e := fid_k6_off_add2 (mv := mv) (k := 45) (x := off) (y := r_j) hmv_hi
        (by decide) (by clear hka hma hJloop hQret; omega)
      have har2_lt : ((4224 + 45 * mv + off + r_j).setWidth 64).toNat <
          (scra.set ((4224 + 45 * mv + off + slot).setWidth 64).toNat cand).length := by
        rw [List.length_set, hla, har2_e]; omega
      let scrb1 := (scra.set ((4224 + 45 * mv + off + slot).setWidth 64).toNat cand).set
        ((4224 + 45 * mv + off + r_j).setWidth 64).toNat flit
      have hkb1 : FidPropKeep scr0 mv.toNat scrb1 := by
        refine fidPropKeep_set (fidPropKeep_set hka cand (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (by rw [har1_e]; omega))))))) flit (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (by rw [har2_e]; omega))))))
      have h4196_1 : scrb1[4196]? = scra[4196]? := by
        dsimp only [scrb1]
        rw [List.getElem?_set_ne (by rw [har2_e]; omega),
          List.getElem?_set_ne (by rw [har1_e]; omega)]
      have hlb1 : scrb1.length = scr0.length := hkb1.1
      c0_hsteps_nogrp
      refine wp_join0 (fun m' => ∃ scrb : List (BitVec 32), FidPropKeep scr0 mv.toNat scrb ∧
          scrb[4196]? = scra[4196]? ∧ (FullMem c (m8ScrSt s scrb) ⋆ R) m') ?_ ?_
      · rintro _ mb ⟨scrb, hkb, h4196, hmb⟩
        have hlb : scrb.length = scr0.length := hkb.1
        have hwb_e := fid_k6_off_add (mv := mv) (k := 21) (x := cid) hmv_hi (by decide)
          (by clear hka hJloop hQret hkb hmb; omega)
        have hwn_e := fid_k6_off_add (mv := mv) (k := 13) (x := cid) hmv_hi (by decide)
          (by clear hka hJloop hQret hkb hmb; omega)
        have hwh_e := fid_k6_off_add (mv := mv) (k := 11) (x := cand) hmv_hi (by decide)
          (by clear hka hJloop hQret hkb hmb; omega)
        have hwb_lt : ((4224 + 21 * mv + cid).setWidth 64).toNat < scrb.length := by
          rw [hlb, hwb_e]; exact fidProp_k_lt 21 (by omega) hmv_lo hbge
        have hwn_lt : ((4224 + 13 * mv + cid).setWidth 64).toNat <
            (scrb.set ((4224 + 21 * mv + cid).setWidth 64).toNat other).length := by
          rw [List.length_set, hlb, hwn_e]; exact fidProp_k_lt 13 (by omega) hmv_lo hbge
        have hwh_lt : ((4224 + 11 * mv + cand).setWidth 64).toNat <
            (scrb.set ((4224 + 21 * mv + cid).setWidth 64).toNat other).length := by
          rw [List.length_set, hlb, hwh_e]; exact fidProp_k_lt 11 (by omega) hmv_lo hbge
        let old_wh := (scrb.set ((4224 + 21 * mv + cid).setWidth 64).toNat other)[((4224 +
          11 * mv + cand).setWidth 64).toNat]'hwh_lt
        have hwh_lt2 : ((4224 + 11 * mv + cand).setWidth 64).toNat <
            ((scrb.set ((4224 + 21 * mv + cid).setWidth 64).toNat other).set
              ((4224 + 13 * mv + cid).setWidth 64).toNat old_wh).length := by
          simp only [List.length_set, hlb, hwh_e]; exact fidProp_k_lt 11 (by omega) hmv_lo hbge
        have hk_fin : FidPropKeep scr0 mv.toNat
            (((scrb.set ((4224 + 21 * mv + cid).setWidth 64).toNat other).set
              ((4224 + 13 * mv + cid).setWidth 64).toNat old_wh).set
              ((4224 + 11 * mv + cand).setWidth 64).toNat cid) := by
          refine fidPropKeep_set (idx := ((4224 + 11 * mv + cand).setWidth 64).toNat)
            (fidPropKeep_set (idx := ((4224 + 13 * mv + cid).setWidth 64).toNat)
              (fidPropKeep_set (idx := ((4224 + 21 * mv + cid).setWidth 64).toNat) hkb other
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
                  rw [hwb_e]; exact ⟨by omega, by omega⟩)))))))
              old_wh (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
                rw [hwn_e]; exact ⟨by omega, by omega⟩)))))))
            cid (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
              rw [hwh_e]; exact ⟨by omega, by omega⟩))))))
        have h4196_fin : (((scrb.set ((4224 + 21 * mv + cid).setWidth 64).toNat other).set
            ((4224 + 13 * mv + cid).setWidth 64).toNat old_wh).set
            ((4224 + 11 * mv + cand).setWidth 64).toNat cid)[4196]? = scra[4196]? := by
          rw [List.getElem?_set_ne (by rw [hwh_e]; omega),
            List.getElem?_set_ne (by rw [hwn_e]; omega),
            List.getElem?_set_ne (by rw [hwb_e]; omega)]
          exact h4196
        c0_hsteps!
        exact hJloop _ prev m hk_fin h4196_fin hm
      · intro Js hJs
        c0_hsplit
        · have hwhf_e := fid_k6_off_add (mv := mv) (k := 11) (x := flit) hmv_hi (by decide)
            (by clear hka hJloop hQret hkb1; omega)
          have hwhf_lt : ((4224 + 11 * mv + flit).setWidth 64).toNat < scrb1.length := by
            rw [hlb1, hwhf_e]; exact fidProp_k_lt 11 (by omega) hmv_lo hbge
          c0_hsteps!
          exact hJs _ ⟨_, fidPropKeep_set (idx := ((4224 + 11 * mv + flit).setWidth 64).toNat)
            hkb1 next (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
              rw [hwhf_e]; exact ⟨by omega, by omega⟩)))))),
            by rw [List.getElem?_set_ne (by rw [hwhf_e]; omega)]; exact h4196_1, hm⟩
        · have hprev_lt : prev.toNat < 2 * nc.toNat := by
            have hc' := hc; clear hc; fid_norm_ofnat
            simp (disch := fid_omega) only [bv_c0, Nat.reducePow] at hc'
            rw [Nat.mod_eq_of_lt (by omega : nc.toNat * 2 < 2 ^ 32)] at hc'
            have := Nat.lt_of_not_le hc'; omega
          have hwnp_e := fid_k6_off_add (mv := mv) (k := 13) (x := prev) hmv_hi (by decide)
            (by clear hka hJloop hQret hkb1; omega)
          have hwnp_lt : ((4224 + 13 * mv + prev).setWidth 64).toNat < scrb1.length := by
            rw [hlb1, hwnp_e]; exact fidProp_k_lt 13 (by omega) hmv_lo hbge
          c0_hsteps!
          exact hJs _ ⟨_, fidPropKeep_set (idx := ((4224 + 13 * mv + prev).setWidth 64).toNat)
            hkb1 next (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
              rw [hwnp_e]; exact ⟨by omega, by omega⟩)))))),
            by rw [List.getElem?_set_ne (by rw [hwnp_e]; omega)]; exact h4196_1, hm⟩
  · intro Js hJs
    c0_hsteps_nogrp
    refine wp_loop_group (ts := [i32])
      (fun rem (r_i, ()) mi => mi = ma ∧ r_i.toNat ≤ sz.toNat ∧ rem = sz.toNat - r_i.toNat)
      ?_ ?_
    · rintro L3 rem ⟨r_i, ⟨⟩⟩ mi hL3 ⟨rfl, hri_le, rfl⟩
      c0_hsplit
      · have hri_lt : r_i.toNat < sz.toNat := hc
        have hri1 : (r_i + 1#32).toNat = r_i.toNat + 1 :=
          m8_bv32_add1_toNat hri_lt (by clear hka hma hJloop hQret hL3; omega)
        have hari_e := fid_k6_off_add2 (mv := mv) (k := 45) (x := off) (y := r_i) hmv_hi
          (by decide) (by clear hka hma hJloop hQret hL3; omega)
        have hari_lt : ((4224 + 45 * mv + off + r_i).setWidth 64).toNat < scra.length := by
          rw [hla, hari_e]; omega
        let rl := scra[((4224 + 45 * mv + off + r_i).setWidth 64).toNat]'hari_lt
        c0_hstraight
        refine wp_join0 (fun mi' => mi' = mi)
          (fun _ mi' hmi' => by
            rw [hmi']; c0_hsteps!
            exact hL3 (sz.toNat - (r_i + 1#32).toNat) (r_i + 1#32, ()) mi (by rw [hri1]; omega)
              ⟨rfl, by rw [hri1]; omega, rfl⟩)
          (fun J4 hJ4 => by
            c0_hsplit
            · have hrl_lt : rl.toNat < 2 * nv.toNat := by
                have hc' := hc; clear hc; fid_norm_ofnat
                simp (disch := fid_omega) only [bv_c0, Nat.reducePow, BitVec.reduceToNat] at hc'
                have hmod : (4224 + 45 * mv.toNat + off.toNat + r_i.toNat) % 4294967296 =
                    ((4224 + 45 * mv + off + r_i).setWidth 64).toNat := by
                  rw [hari_e, Nat.mod_eq_of_lt (by omega)]
                have hrl_eq := congrArg BitVec.toNat
                  (m8_k6_get_congr hmod (by rw [hmod]; exact hari_lt) hari_lt)
                dsimp only [rl] at hrl_eq ⊢
                rw [hrl_eq] at hc'; omega
              have hval_e := fid_k6_off_add (mv := mv) (k := 9) (x := rl) hmv_hi (by decide)
                (by clear hka hma hJloop hQret hL3 hJ4; omega)
              have hval_lt : ((4224 + 9 * mv + rl).setWidth 64).toNat < scra.length := by
                rw [hla, hval_e]; exact fidProp_k_lt 9 (by omega) hmv_lo hbge
              c0_hsplit
              · c0_hsteps!; exact hJs (r_i, r_i, rl) (Or.inr ⟨hri_lt, hrl_lt⟩)
              · c0_hsteps!; exact hJ4 mi rfl
            · c0_hsteps!; exact hJ4 mi rfl)
      · c0_hsteps!; exact hJs (r_i, 4294967295#32, 0#32) (Or.inl rfl)
    · intro L3 hL3; c0_hsteps!; exact hL3 (sz.toNat - 2) (2#32, ()) ma ⟨rfl, hsz_ge, rfl⟩

/-! ## 3. Watch-List Loop (`fidPropWatchLoopExpr` & `fidProp_watch_loop_wp`) -/

private def fidPropWatchLoopExpr (pScr cHdr : BitVec 64)
    (mv mv4 nv nc acap flit whead_flit : BitVec 32) (ticks0 : BitVec 64)
    (J_out : Cont [i64]) : Expr Val Cont [i32] :=
  let o_vals : BitVec 32 := 4224 + 9 * mv
  let o_wnext : BitVec 32 := 4224 + 13 * mv
  let o_wblk : BitVec 32 := 4224 + 21 * mv
  let o_cl_off : BitVec 32 := 4224 + 29 * mv
  let o_cl_meta : BitVec 32 := 4224 + 33 * mv
  let o_arena : BitVec 32 := 4224 + 45 * mv
  Expr.group (sig := [[i64, i64, i32, i32, i32]]) (fun Js_2 =>
    Blocks.cons (fun p_69 =>
      Expr.group (sig := [[]]) (fun _ =>
        Blocks.cons (fun _ =>
          Expr.let_ { sig := [i32], code := OpCode.sext 32 64,
                      args := (Arg.imm 4, ()) } fun p =>
          Expr.let_ { sig := [i64, i64], code := OpCode.lshr i64,
                      args := (Arg.var p_69.snd.fst, Arg.var p.fst, ()) } fun p =>
          Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var p_69.fst, Arg.var p.fst, ()) } fun p =>
          Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var p.fst, Arg.imm 1, ()) } fun p =>
          Expr.jump J_out (Arg.var p.fst, ())) Blocks.nil) fun Js_exit =>
      Expr.let_ { sig := [i32, i32], code := OpCode.shl i32,
                  args := (Arg.var nc, Arg.imm 1, ()) } fun p_70 =>
      Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                  args := (Arg.var p_69.snd.snd.snd.fst, Arg.var p_70.fst, ()) } fun p_71 =>
      Expr.jnz (Arg.var p_71.fst)
        (Expr.let_ { sig := [i32, i32], code := OpCode.shl i32,
                     args := (Arg.var mv4, Arg.imm 1, ()) } fun p_72 =>
         Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                     args := (Arg.var p_69.snd.snd.snd.snd.fst, Arg.var p_72.fst, ()) }
           fun p_73 =>
         Expr.jnz (Arg.var p_73.fst)
           (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                        args := (Arg.var p_69.snd.snd.snd.snd.fst, Arg.imm 1, ()) } fun p_74 =>
            Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                        args := (Arg.var o_wnext, Arg.var p_69.snd.snd.snd.fst, ()) } fun p_75 =>
            Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                        args := (Arg.var p_75.fst, ()) } fun p_76 =>
            Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                        args := (Arg.var p_76.fst, Arg.imm 4, ()) } fun p_77 =>
            Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var pScr, Arg.var p_77.fst, ()) } fun p_78 =>
            Expr.load i32 (Arg.var p_78.fst) fun ld_12 =>
            Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var p_69.snd.fst, Arg.imm 1, ()) } fun p_79 =>
            Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                        args := (Arg.var o_wblk, Arg.var p_69.snd.snd.snd.fst, ()) } fun p_80 =>
            Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                        args := (Arg.var p_80.fst, ()) } fun p_81 =>
            Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                        args := (Arg.var p_81.fst, Arg.imm 4, ()) } fun p_82 =>
            Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var pScr, Arg.var p_82.fst, ()) } fun p_83 =>
            Expr.load i32 (Arg.var p_83.fst) fun ld_13 =>
            Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                        args := (Arg.var ld_13, Arg.imm 2147483647, ()) } fun p_84 =>
            Expr.let_ { sig := [i32, i32], code := OpCode.shl i32,
                        args := (Arg.var nv, Arg.imm 1, ()) } fun p_85 =>
            Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.uge i32 Ty.bool (by decide),
                        args := (Arg.var p_84.fst, Arg.var p_85.fst, ()) } fun p_86 =>
            Expr.jnz (Arg.var p_86.fst)
              (Expr.jump Js_2.fst (Arg.var p_69.fst, Arg.var p_79.fst,
                Arg.var p_69.snd.snd.snd.fst, Arg.var ld_12, Arg.var p_74.fst, ()))
              (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                           args := (Arg.var o_vals, Arg.var p_84.fst, ()) } fun p_87 =>
               Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                           args := (Arg.var p_87.fst, ()) } fun p_88 =>
               Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                           args := (Arg.var p_88.fst, Arg.imm 4, ()) } fun p_89 =>
               Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                           args := (Arg.var pScr, Arg.var p_89.fst, ()) } fun p_90 =>
               Expr.load i32 (Arg.var p_90.fst) fun ld_14 =>
               Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool
                             (by decide),
                           args := (Arg.var ld_14, Arg.imm 1, ()) } fun p_91 =>
               Expr.jnz (Arg.var p_91.fst)
                 (Expr.jump Js_2.fst (Arg.var p_69.fst, Arg.var p_79.fst,
                    Arg.var p_69.snd.snd.snd.fst, Arg.var ld_12, Arg.var p_74.fst, ()))
                 (Expr.let_ { sig := [i32, i32], code := OpCode.lshr i32,
                              args := (Arg.var p_69.snd.snd.snd.fst, Arg.imm 1, ()) } fun p_92 =>
                  Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                              args := (Arg.var ld_13, Arg.imm 2147483648, ()) } fun p_93 =>
                  Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool
                                (by decide),
                              args := (Arg.var p_93.fst, Arg.imm 0, ()) } fun p_94 =>
                  Expr.jnz (Arg.var p_94.fst)
                    (Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool
                                   (by decide),
                                 args := (Arg.var ld_14, Arg.imm 2, ()) } fun p_95 =>
                     Expr.jnz (Arg.var p_95.fst)
                       (Expr.let_ { sig := [i32], code := OpCode.sext 32 64,
                                    args := (Arg.imm 4, ()) } fun p_96 =>
                        Expr.let_ { sig := [i64, i64], code := OpCode.lshr i64,
                                    args := (Arg.var p_79.fst, Arg.var p_96.fst, ()) } fun p_97 =>
                        Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                    args := (Arg.var p_69.fst, Arg.var p_97.fst, ()) } fun p_98 =>
                        Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                    args := (Arg.var p_98.fst, Arg.imm 1, ()) } fun p_99 =>
                        Expr.call (as := [i64, i64]) (bs := []) "full_fid_k6_add_ticks"
                          (Arg.var cHdr, Arg.var p_99.fst, PUnit.unit) fun _ =>
                          Expr.ret (Arg.var p_92.fst, ()))
                       (Expr.group (sig := [[]]) (fun _ =>
                          Blocks.cons (fun _ =>
                            Expr.jump Js_2.fst (Arg.var p_69.fst, Arg.var p_79.fst,
                              Arg.var p_69.snd.snd.snd.fst, Arg.var ld_12, Arg.var p_74.fst, ()))
                            Blocks.nil) fun Js =>
                        Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool
                                      (by decide),
                                    args := (Arg.var ld_14, Arg.imm 0, ()) } fun p_96 =>
                        Expr.jnz (Arg.var p_96.fst)
                          (Expr.call (as := [i64, i32, i32]) (bs := []) "full_k6_assign_fid"
                             (Arg.var cHdr, Arg.var p_84.fst, Arg.var p_92.fst, PUnit.unit) fun _ =>
                             Expr.jump Js.fst ())
                          (Expr.jump Js.fst ())))
                    (Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                                 args := (Arg.var p_69.snd.snd.snd.fst, Arg.imm 1, ()) } fun p_95 =>
                     Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                 args := (Arg.var o_cl_off, Arg.var p_92.fst, ()) } fun p_96 =>
                     Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                 args := (Arg.var p_96.fst, ()) } fun p_97 =>
                     Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                 args := (Arg.var p_97.fst, Arg.imm 4, ()) } fun p_98 =>
                     Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                 args := (Arg.var pScr, Arg.var p_98.fst, ()) } fun p_99 =>
                     Expr.load i32 (Arg.var p_99.fst) fun ld_15 =>
                     Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                 args := (Arg.var o_cl_meta, Arg.var p_92.fst, ()) } fun p_100 =>
                     Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                 args := (Arg.var p_100.fst, ()) } fun p_101 =>
                     Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                 args := (Arg.var p_101.fst, Arg.imm 4, ()) } fun p_102 =>
                     Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                 args := (Arg.var pScr, Arg.var p_102.fst, ()) } fun p_103 =>
                     Expr.load i32 (Arg.var p_103.fst) fun ld_16 =>
                     Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                                 args := (Arg.var ld_16, Arg.imm 65535, ()) } fun p_104 =>
                     Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool
                                   (by decide),
                                 args := (Arg.var p_104.fst, Arg.imm 2, ()) } fun p_105 =>
                     Expr.jnz (Arg.var p_105.fst)
                       (Expr.jump Js_2.fst (Arg.var p_69.fst, Arg.var p_79.fst,
                          Arg.var p_69.snd.snd.snd.fst, Arg.var ld_12, Arg.var p_74.fst, ()))
                       (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                    args := (Arg.var ld_15, Arg.var p_104.fst, ()) } fun p_106 =>
                        Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ugt i32 Ty.bool
                                      (by decide),
                                    args := (Arg.var p_106.fst, Arg.var acap, ()) } fun p_107 =>
                        Expr.jnz (Arg.var p_107.fst)
                          (Expr.jump Js_2.fst (Arg.var p_69.fst, Arg.var p_79.fst,
                             Arg.var p_69.snd.snd.snd.fst, Arg.var ld_12, Arg.var p_74.fst, ()))
                          (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                       args := (Arg.var o_arena, Arg.var ld_15, ()) }
                             fun p_108 =>
                           Expr.let_ { sig := [i32, i32], code := OpCode.xor i32,
                                       args := (Arg.var p_95.fst, Arg.imm 1, ()) } fun p_109 =>
                           Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                       args := (Arg.var p_108.fst, Arg.var p_109.fst, ()) }
                             fun p_110 =>
                           Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                       args := (Arg.var p_110.fst, ()) } fun p_111 =>
                           Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                       args := (Arg.var p_111.fst, Arg.imm 4, ()) } fun p_112 =>
                           Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                       args := (Arg.var pScr, Arg.var p_112.fst, ()) } fun p_113 =>
                           Expr.load i32 (Arg.var p_113.fst) fun ld_17 =>
                           Expr.let_ { sig := [i32, i32], code := OpCode.shl i32,
                                       args := (Arg.var nv, Arg.imm 1, ()) } fun p_114 =>
                           Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.uge i32 Ty.bool
                                         (by decide),
                                       args := (Arg.var ld_17, Arg.var p_114.fst, ()) } fun p_115 =>
                           Expr.jnz (Arg.var p_115.fst)
                             (Expr.jump Js_2.fst (Arg.var p_69.fst, Arg.var p_79.fst,
                                Arg.var p_69.snd.snd.snd.fst, Arg.var ld_12, Arg.var p_74.fst, ()))
                             (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                          args := (Arg.var p_69.fst, Arg.imm 1, ()) } fun p_116 =>
                              Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                          args := (Arg.var o_vals, Arg.var ld_17, ()) } fun p_117 =>
                              Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                          args := (Arg.var p_117.fst, ()) } fun p_118 =>
                              Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                          args := (Arg.var p_118.fst, Arg.imm 4, ()) } fun p_119 =>
                              Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                          args := (Arg.var pScr, Arg.var p_119.fst, ()) }
                                fun p_120 =>
                              Expr.load i32 (Arg.var p_120.fst) fun ld_18 =>
                              Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32
                                            Ty.bool (by decide),
                                          args := (Arg.var ld_18, Arg.imm 1, ()) } fun p_121 =>
                              Expr.jnz (Arg.var p_121.fst)
                                (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                             args := (Arg.var o_wblk,
                                               Arg.var p_69.snd.snd.snd.fst, ()) } fun p =>
                                 Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                             args := (Arg.var p.fst, ()) } fun p =>
                                 Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                             args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                                 Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                             args := (Arg.var pScr, Arg.var p.fst, ()) } fun p =>
                                 Expr.store (Arg.var ld_17) (Arg.var p.fst)
                                   (Expr.jump Js_2.fst (Arg.var p_116.fst, Arg.var p_79.fst,
                                      Arg.var p_69.snd.snd.snd.fst, Arg.var ld_12,
                                      Arg.var p_74.fst, ())))
                                (fidPropReplExpr pScr cHdr mv nv nc flit
                                   p_69.snd.snd.snd.fst p_69.snd.snd.fst ld_12 p_74.fst ld_17
                                   p_95.fst ld_15 p_104.fst p_92.fst p_116.fst p_79.fst
                                   Js_2.fst))))))))
           (Expr.jump Js_exit.fst ()))
        (Expr.jump Js_exit.fst ())) Blocks.nil) fun Js =>
  Expr.jump Js.fst (Arg.var ticks0, Arg.imm 0, Arg.imm 4294967295, Arg.var whead_flit,
    Arg.imm 0, ())

private theorem fidProp_watch_loop_wp (Γ : Env) (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (Q : Post [i32]) (X : XPost) (scr0 scr_in : List (BitVec 32))
    (mv4 flit whead_flit : BitVec 32) (ticks0 : BitVec 64)
    (J_out : Cont [i64]) (m_in : Mem 64)
    (hTicks : Γ.Has "full_fid_k6_add_ticks" fidK6AddTicksSpec)
    (hAssign : Γ.Has "full_k6_assign_fid" fidK6AssignSpec)
    (hlen : FullState.LengthsOk c s) (hok : FidK6BufOk scr0)
    (hscr_len : scr0.length = c.scratch_cap)
    (h4214 : 4214 < scr0.length) :
    let mv := scr0[4214]'h4214
    let nv := scr0[4192]'(by have := hok.base_ge; omega)
    let nc := scr0[4193]'(by have := hok.base_ge; omega)
    let acap := scr0[4207]'(by have := hok.base_ge; omega)
    256 ≤ mv.toNat → mv.toNat ≤ 8192 → nv.toNat ≤ mv.toNat → nc.toNat ≤ 4 * mv.toNat →
    4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length →
    4224 + 45 * mv.toNat ≤ scr0.length → scr0.length < 2 ^ 30 →
    mv4.toNat = 4 * mv.toNat → flit.toNat < 2 * nv.toNat →
    FidPropKeep scr0 mv.toNat scr_in → (FullMem c (m8ScrSt s scr_in) ⋆ R) m_in →
    (∀ (scrb : List (BitVec 32)) (ticks' : BitVec 64) (mb : Mem 64),
      FidPropKeep scr0 mv.toNat scrb → scrb[4196]? = scr_in[4196]? →
      (FullMem c (m8ScrSt s scrb) ⋆ R) mb →
      wp Γ Q X (Expr.jump J_out (Arg.var ticks', ())) mb) →
    (∀ (r : BitVec 32) (scrb : List (BitVec 32)) (mb : Mem 64),
      FidPropKeep scr0 mv.toNat scrb → (FullMem c (m8ScrSt s scrb) ⋆ R) mb →
      Q (r, ()) mb) →
    wp Γ Q X (fidPropWatchLoopExpr c.pScratchBuf c.hdr mv mv4 nv nc acap flit whead_flit
      ticks0 J_out) m_in := by
  intro mv nv nc acap hmv_lo hmv_hi hnv_le hnc_le hlen_scr hbge hcap_lt
    hmv4 hflit hkin hm_in hJout hQret
  have hmv_eq : scr0[4214]?.getD 0#32 = mv := m8_k6_get_eq h4214
  have hmin : 15744 ≤ scr0.length := by omega
  have h4192 : 4192 < scr0.length := by omega
  have h4193 : 4193 < scr0.length := by omega
  have h4207 : 4207 < scr0.length := by omega
  dsimp only [fidPropWatchLoopExpr]
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i64, i64, i32, i32, i32])
    (fun rem (ticks, props, prev, cid, wsteps, ()) m =>
      ∃ scra : List (BitVec 32), FidPropKeep scr0 mv.toNat scra ∧
        scra[4196]? = scr_in[4196]? ∧ wsteps.toNat ≤ 8 * mv.toNat ∧
        rem = 8 * mv.toNat - wsteps.toNat ∧ (FullMem c (m8ScrSt s scra) ⋆ R) m) ?_ ?_
  · rintro L2 rem ⟨ticks, props, prev, cid, wsteps, ⟨⟩⟩ m hL2 ⟨scra, hka, h4196a, hw_le, rfl, hma⟩
    have hla : scra.length = scr0.length := hka.1
    c0_hsteps_nogrp
    refine wp_join0 (fun m' => ∃ scrb : List (BitVec 32), FidPropKeep scr0 mv.toNat scrb ∧
        scrb[4196]? = scr_in[4196]? ∧ (FullMem c (m8ScrSt s scrb) ⋆ R) m')
      (fun _ mb ⟨scrb, hkb, h4196b, hmb⟩ => by
        c0_hsteps!; exact hJout scrb _ mb hkb h4196b hmb)
      (fun Jexit hJexit => by
        c0_hsplit
        · have hcid : cid.toNat < 2 * nc.toNat := by
            have hc' := hc; clear hc; fid_norm_ofnat
            simp (disch := fid_omega) only [bv_c0, Nat.reducePow] at hc'
            rw [Nat.mod_eq_of_lt (by omega : nc.toNat * 2 < 2 ^ 32)] at hc'
            omega
          c0_hsplit
          · have hw_lt : wsteps.toNat < 8 * mv.toNat := by
              have hc' := hc; clear hc; fid_norm_ofnat
              simp (disch := fid_omega) only [bv_c0, Nat.reducePow] at hc'
              omega
            have hw1 : (wsteps + 1#32).toNat = wsteps.toNat + 1 :=
              m8_bv32_add1_toNat hw_lt (by clear hka hma hL2 hJout hQret hJexit; omega)
            have hwn_e := fid_k6_off_add (mv := mv) (k := 13) (x := cid) hmv_hi (by decide)
              (by clear hka hma hL2 hJout hQret hJexit; omega)
            have hwn_lt : ((4224 + 13 * mv + cid).setWidth 64).toNat < scra.length := by
              rw [hla, hwn_e]; exact fidProp_k_lt 13 (by omega) hmv_lo hbge
            have hwb_e := fid_k6_off_add (mv := mv) (k := 21) (x := cid) hmv_hi (by decide)
              (by clear hka hma hL2 hJout hQret hJexit; omega)
            have hwb_lt : ((4224 + 21 * mv + cid).setWidth 64).toNat < scra.length := by
              rw [hla, hwb_e]; exact fidProp_k_lt 21 (by omega) hmv_lo hbge
            let next := scra[((4224 + 13 * mv + cid).setWidth 64).toNat]'hwn_lt
            let blk := scra[((4224 + 21 * mv + cid).setWidth 64).toNat]'hwb_lt
            let blk_lit := blk &&& 2147483647#32
            c0_hstraight
            c0_hsplit
            · c0_hsteps!
              exact hL2 (8 * mv.toNat - (wsteps + 1#32).toNat)
                (ticks, props + 1#64, cid, next, wsteps + 1#32, ()) m (by omega)
                ⟨scra, hka, h4196a, by omega, rfl, hma⟩
            · have hblit_lt : blk_lit.toNat < 2 * nv.toNat := by
                have hc' := hc; clear hc; fid_norm_ofnat
                simp (disch := fid_omega) only [bv_c0, Nat.reducePow, BitVec.reduceToNat] at hc'
                have hwb_mod : (4224 + 21 * mv.toNat + cid.toNat) % 4294967296 =
                    ((4224 + 21 * mv + cid).setWidth 64).toNat := by
                  rw [hwb_e, Nat.mod_eq_of_lt (by omega)]
                have hblk_eq := congrArg (fun v : BitVec 32 => v.toNat % 2147483648)
                  (m8_k6_get_congr hwb_mod (by rw [hwb_mod]; exact hwb_lt) hwb_lt)
                have hbl_nat : blk_lit.toNat = blk.toNat % 2147483648 := by
                  dsimp only [blk_lit]; rw [BitVec.toNat_and, show (2147483647#32 : BitVec
                    32).toNat = 2 ^ 31 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
                rw [hblk_eq, ← hbl_nat] at hc'; exact Nat.lt_of_not_le (by omega)
              have hva_e := fid_k6_off_add (mv := mv) (k := 9) (x := blk_lit) hmv_hi (by decide)
                (by clear hka hma hL2 hJout hQret hJexit; omega)
              have hva_lt : ((4224 + 9 * mv + blk_lit).setWidth 64).toNat < scra.length := by
                rw [hla, hva_e]; exact fidProp_k_lt 9 (by omega) hmv_lo hbge
              c0_hsplit
              · c0_hsteps!
                exact hL2 (8 * mv.toNat - (wsteps + 1#32).toNat)
                  (ticks, props + 1#64, cid, next, wsteps + 1#32, ()) m (by omega)
                  ⟨scra, hka, h4196a, by omega, rfl, hma⟩
              · have hc_id : (cid >>> (1 : Nat)).toNat < nc.toNat := by
                  rw [m8_bv32_lshr1_toNat]; omega
                c0_hsplit
                · c0_hsplit
                  · c0_hsteps_nogrp
                    exact fidProp_call_add_ticks hTicks hlen hscr_len h4214 hmv_eq hmin hka hma
                      (fun scrb mb hkb _ hmb => hQret _ scrb mb hkb hmb)
                  · c0_hsteps_nogrp
                    refine wp_join0 (fun m' => ∃ scrb : List (BitVec 32),
                        FidPropKeep scr0 mv.toNat scrb ∧ scrb[4196]? = scr_in[4196]? ∧
                        (FullMem c (m8ScrSt s scrb) ⋆ R) m')
                      (fun _ mb ⟨scrb, hkb, h4196b, hmb⟩ => by
                        c0_hsteps!
                        exact hL2 (8 * mv.toNat - (wsteps + 1#32).toNat)
                          (ticks, props + 1#64, cid, next, wsteps + 1#32, ()) mb (by omega)
                          ⟨scrb, hkb, h4196b, by omega, rfl, hmb⟩)
                      (fun Js hJs => by
                        c0_hsplit
                        · exact fidProp_call_assign hAssign hlen hok hscr_len h4214 hmv_eq hmv_hi
                            hbge hka hma (fun scrb mb hkb h4196_b hmb => by
                              c0_hsteps!
                              exact hJs mb ⟨scrb, hkb, h4196_b.trans h4196a, hmb⟩)
                        · c0_hsteps!; exact hJs m ⟨scra, hka, h4196a, hma⟩)
                · have hco_e := fid_k6_off_add (mv := mv) (k := 29) (x := cid >>> (1 : Nat))
                    hmv_hi (by decide) (by clear hka hma hL2 hJout hQret hJexit; omega)
                  have hcm_e := fid_k6_off_add (mv := mv) (k := 33) (x := cid >>> (1 : Nat))
                    hmv_hi (by decide) (by clear hka hma hL2 hJout hQret hJexit; omega)
                  have hco_lt : ((4224 + 29 * mv + (cid >>> (1 : Nat))).setWidth 64).toNat <
                      scra.length := by
                    rw [hla, hco_e]; omega
                  have hcm_lt : ((4224 + 33 * mv + (cid >>> (1 : Nat))).setWidth 64).toNat <
                      scra.length := by
                    rw [hla, hcm_e]; omega
                  let off := scra[((4224 + 29 * mv + (cid >>> (1 : Nat))).setWidth 64).toNat]'hco_lt
                  let cm := scra[((4224 + 33 * mv + (cid >>> (1 : Nat))).setWidth 64).toNat]'hcm_lt
                  let sz := cm &&& 65535#32
                  have hco_mod : (4224 + 29 * mv.toNat + cid.toNat / 2) % 4294967296 =
                      ((4224 + 29 * mv + (cid >>> (1 : Nat))).setWidth 64).toNat := by
                    rw [hco_e, m8_bv32_lshr1_toNat, Nat.mod_eq_of_lt (by omega)]
                  have hcm_mod : (4224 + 33 * mv.toNat + cid.toNat / 2) % 4294967296 =
                      ((4224 + 33 * mv + (cid >>> (1 : Nat))).setWidth 64).toNat := by
                    rw [hcm_e, m8_bv32_lshr1_toNat, Nat.mod_eq_of_lt (by omega)]
                  have hoff_eq := m8_k6_get_congr hco_mod (by rw [hco_mod]; exact hco_lt) hco_lt
                  have hcm_eq := m8_k6_get_congr hcm_mod (by rw [hcm_mod]; exact hcm_lt) hcm_lt
                  have hsz_mod : sz.toNat = cm.toNat % 65536 := by
                    dsimp only [sz]; rw [BitVec.toNat_and, show (65535#32 : BitVec 32).toNat =
                      2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
                  have hsz_le : sz.toNat ≤ 65535 := m8_and_ffff_le cm
                  c0_hstraight
                  c0_hsplit
                  · c0_hsteps!
                    exact hL2 (8 * mv.toNat - (wsteps + 1#32).toNat)
                      (ticks, props + 1#64, cid, next, wsteps + 1#32, ()) m (by omega)
                      ⟨scra, hka, h4196a, by omega, rfl, hma⟩
                  · have hsz_ge : 2 ≤ sz.toNat := by
                      have hc' := hc; clear hc; fid_norm_ofnat
                      simp (disch := fid_omega) only [bv_c0, Nat.reducePow, BitVec.reduceToNat]
                        at hc'
                      have h1 := congrArg (fun v : BitVec 32 => v.toNat % 65536) hcm_eq
                      rw [h1, ← hsz_mod] at hc'; exact Nat.le_of_not_lt hc'
                    c0_hsplit
                    · c0_hsteps!
                      exact hL2 (8 * mv.toNat - (wsteps + 1#32).toNat)
                        (ticks, props + 1#64, cid, next, wsteps + 1#32, ()) m (by omega)
                        ⟨scra, hka, h4196a, by omega, rfl, hma⟩
                    · have hos_le : off.toNat + sz.toNat ≤ acap.toNat := by
                        have hc' := hc; clear hc; fid_norm_ofnat
                        simp (disch := fid_omega) only [bv_c0, Nat.reducePow, BitVec.reduceToNat]
                          at hc'
                        have hc'' := Nat.le_of_not_lt hc'
                        have h1 := congrArg BitVec.toNat hoff_eq
                        have h2 := congrArg (fun v : BitVec 32 => v.toNat % 65536) hcm_eq
                        rw [h1, h2, ← hsz_mod] at hc''
                        have hsum : (off.toNat + sz.toNat) % 4294967296 ≤ acap.toNat := hc''
                        have hlt32 : off.toNat + sz.toNat < 4294967296 := by
                          have hb := (fidPropKeep_bufOk hok h4214 hmv_eq hka).clause_ok
                            (cid := (cid >>> (1 : Nat)).toNat)
                          have hk_mv : scra[4214]? = scr0[4214]? :=
                            hka.2.2.2.1 4214 (by omega) (by omega)
                          have hk_nc : scra[4193]? = scr0[4193]? := hka.2.1 4193 (by omega)
                          have hk_ac : scra[4207]? = scr0[4207]? :=
                            hka.2.2.2.1 4207 (by omega) (by omega)
                          have hcl := hb (by rw [hk_nc, List.getElem?_eq_getElem h4193,
                            Option.getD_some]; exact hc_id)
                          rw [hk_mv, hk_ac, List.getElem?_eq_getElem h4214,
                            List.getElem?_eq_getElem h4207, Option.getD_some,
                            Option.getD_some] at hcl
                          dsimp only at hcl
                          have h1 : (scra[4224 + 29 * (scr0[4214]'h4214).toNat +
                              (cid >>> (1 : Nat)).toNat]?.getD 0#32) = off := by
                            rw [List.getElem?_eq_getElem (by
                              rw [hla, show (scr0[4214]'h4214) = mv from rfl]; omega),
                              Option.getD_some]
                            exact m8_k6_get_congr hco_e.symm _ _
                          have h2 : (scra[4224 + 33 * (scr0[4214]'h4214).toNat +
                              (cid >>> (1 : Nat)).toNat]?.getD 0#32) = cm := by
                            rw [List.getElem?_eq_getElem (by
                              rw [hla, show (scr0[4214]'h4214) = mv from rfl]; omega),
                              Option.getD_some]
                            exact m8_k6_get_congr hcm_e.symm _ _
                          rw [h1, h2] at hcl; exact Nat.lt_of_le_of_lt hcl.1 (by omega)
                        rwa [Nat.mod_eq_of_lt hlt32] at hsum
                      have hslot_lt : (cid &&& 1#32).toNat < 2 := by
                        rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl]
                        have := Nat.and_le_right (n := cid.toNat) (m := 1); omega
                      have hslotx_lt : ((cid &&& 1#32) ^^^ 1#32).toNat < 2 := m8k6_slot_xor1_lt
                      have hoi_e := fid_k6_off_add2 (mv := mv) (k := 45) (x := off)
                        (y := (cid &&& 1#32) ^^^ 1#32) hmv_hi (by decide)
                        (by clear hka hma hL2 hJout hQret hJexit; omega)
                      have hoi_lt : ((4224 + 45 * mv + off + ((cid &&& 1#32) ^^^ 1#32)).setWidth
                          64).toNat < scra.length := by
                        rw [hla, hoi_e]; omega
                      let other := scra[((4224 + 45 * mv + off + ((cid &&& 1#32) ^^^ 1#32)).setWidth
                        64).toNat]'hoi_lt
                      c0_hstraight
                      c0_hsplit
                      · c0_hsteps!
                        exact hL2 (8 * mv.toNat - (wsteps + 1#32).toNat)
                          (ticks, props + 1#64, cid, next, wsteps + 1#32, ()) m (by omega)
                          ⟨scra, hka, h4196a, by omega, rfl, hma⟩
                      · have hother_lt : other.toNat < 2 * nv.toNat := by
                          have hc' := hc; clear hc; fid_norm_ofnat
                          simp (disch := fid_omega) only [bv_c0, Nat.reducePow, BitVec.reduceToNat]
                            at hc'
                          have h1 := congrArg BitVec.toNat hoff_eq
                          have hxor : cid.toNat % 2 + 1 - 2 * (cid.toNat % 2 % 2) =
                              ((cid &&& 1#32) ^^^ 1#32).toNat := by
                            rw [BitVec.toNat_xor, BitVec.toNat_and,
                              show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
                            rcases Nat.mod_two_eq_zero_or_one cid.toNat with h | h <;> simp [h]
                          have hoi_mod : (4224 + 45 * mv.toNat + scra[(4224 + 29 * mv.toNat +
                              cid.toNat / 2) % 4294967296].toNat + (cid.toNat % 2 + 1 -
                              2 * (cid.toNat % 2 % 2))) % 4294967296 =
                              ((4224 + 45 * mv + off + ((cid &&& 1#32) ^^^ 1#32)).setWidth
                                64).toNat := by
                            rw [h1, hxor, hoi_e]
                            exact Nat.mod_eq_of_lt
                              (by rw [← hoi_e]; exact lt_trans hoi_lt (by omega))
                          have ho_eq := congrArg BitVec.toNat
                            (m8_k6_get_congr hoi_mod (by rw [hoi_mod]; exact hoi_lt) hoi_lt)
                          rw [ho_eq, Nat.mod_eq_of_lt (by omega : nv.toNat * 2 < 2 ^ 32)] at hc'
                          dsimp only [other]
                          have := Nat.lt_of_not_le hc'; omega
                        have hvo_e := fid_k6_off_add (mv := mv) (k := 9) (x := other) hmv_hi
                          (by decide) (by clear hka hma hL2 hJout hQret hJexit; omega)
                        have hvo_lt : ((4224 + 9 * mv + other).setWidth 64).toNat <
                            scra.length := by
                          rw [hla, hvo_e]; exact fidProp_k_lt 9 (by omega) hmv_lo hbge
                        c0_hsplit
                        · c0_hsteps!
                          have hk1 := fidPropKeep_set
                            (idx := ((4224 + 21 * mv + cid).setWidth 64).toNat) hka other
                            (Or.inr (Or.inr (Or.inr (Or.inr
                              (Or.inl (by rw [hwb_e]; exact ⟨by omega, by omega⟩))))))
                          have h4196_1 : (scra.set ((4224 + 21 * mv + cid).setWidth 64).toNat
                              other)[4196]? = scr_in[4196]? := by
                            rw [List.getElem?_set_ne (by rw [hwb_e]; omega)]; exact h4196a
                          exact hL2 (8 * mv.toNat - (wsteps + 1#32).toNat)
                            (ticks + 1#64, props + 1#64, cid, next, wsteps + 1#32, ()) _ (by omega)
                            ⟨_, hk1, h4196_1, by omega, rfl, hm⟩
                        · exact fidProp_repl_wp Γ c s R Q X scr0 scra flit cid prev next
                            (wsteps + 1#32) other (cid &&& 1#32) off sz (cid >>> (1 : Nat))
                            (ticks + 1#64) (props + 1#64) L2 m hTicks hAssign hlen hok hscr_len
                            h4214 hmv_lo hmv_hi hnv_le hnc_le hlen_scr hbge hcap_lt hflit hcid
                            hother_lt hslot_lt hsz_ge hsz_le hos_le hka hma
                            (fun scrb prev' mb hkb h4196b hmb =>
                              hL2 (8 * mv.toNat - (wsteps + 1#32).toNat)
                                (ticks + 1#64, props + 1#64, prev', next, wsteps + 1#32, ()) mb
                                (by omega) ⟨scrb, hkb, h4196b.trans h4196a, by omega, rfl, hmb⟩)
                            (hQret (cid >>> (1 : Nat)))
          · c0_hsteps!; exact hJexit m ⟨scra, hka, h4196a, hma⟩
        · c0_hsteps!; exact hJexit m ⟨scra, hka, h4196a, hma⟩)
  · intro L2 hL2; c0_hsteps!
    exact hL2 (8 * mv.toNat) (ticks0, 0#64, 4294967295#32, whead_flit, 0#32, ()) m_in
      ⟨scr_in, hkin, rfl, by simp, rfl, hm_in⟩

/-! ## 4. `full_k6_prop_fid_wp` -/

/-- Parametric `Func.wp` proof for `full_k6_prop_fid`, certifying `fidK6PropSpec`. -/
theorem full_k6_prop_fid_wp (Γ : Env)
    (hTicks : Γ.Has "full_fid_k6_add_ticks" fidK6AddTicksSpec)
    (hAssign : Γ.Has "full_k6_assign_fid" fidK6AssignSpec) :
    ∀ a m Q X, fidK6PropSpec a m Q X → Func.wp Γ full_k6_prop_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hok, hm0, hQ⟩ := fidK6PropSpec_elim hSpec
  let scr0 := s.scratch.scratch_buf
  have hscr_len : scr0.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hmin : 15744 ≤ scr0.length := hok.min_len
  have hmv_lo : 256 ≤ (scr0[4214]?.getD 0#32).toNat := hok.mv_lo
  have hmv_hi : (scr0[4214]?.getD 0#32).toNat ≤ 8192 := hok.mv_hi
  have hbge : 4224 + 45 * (scr0[4214]?.getD 0#32).toNat ≤ scr0.length := hok.base_ge
  have hlen_ge := hok.length_ge; have hlen_lt := hok.length_lt
  have h4214 : 4214 < scr0.length := by omega
  have h4192 : 4192 < scr0.length := by omega
  have h4193 : 4193 < scr0.length := by omega
  have h4207 : 4207 < scr0.length := by omega
  have h4196 : 4196 < scr0.length := by omega
  let mv := scr0[4214]'h4214
  let nv := scr0[4192]'h4192
  let nc := scr0[4193]'h4193
  let acap := scr0[4207]'h4207
  have hmv_eq : scr0[4214]?.getD 0#32 = mv := m8_k6_get_eq h4214
  have hac_eq : scr0[4207]?.getD 0#32 = acap := m8_k6_get_eq h4207
  rw [hmv_eq] at hmv_lo hmv_hi hbge hlen_ge; rw [hac_eq] at hlen_ge
  have hlen_scr : 4224 + 45 * mv.toNat + acap.toNat ≤ scr0.length := hlen_ge
  have hcap_lt : scr0.length < 2 ^ 30 := hlen_lt
  have hm0' : (FullMem c (m8ScrSt s scr0) ⋆ R) m0 := by rwa [m8ScrSt_self]
  have hret_noop : Q (4294967295#32, ()) m0 :=
    hQ 4294967295#32 scr0 m0 hok hscr_len (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) hm0
  have hq_ret : ∀ r (scrb : List (BitVec 32)) mb, FidPropKeep scr0 mv.toNat scrb →
      (FullMem c (m8ScrSt s scrb) ⋆ R) mb → Q (r, ()) mb := by
    intro r scrb mb hkb hmb
    refine hQ r scrb mb (fidPropKeep_bufOk hok h4214 hmv_eq hkb) (hkb.1.trans hscr_len)
      hkb.2.1 hkb.2.2.1 hkb.2.2.2.1 ?_ ?_ ?_ (m8ScrSt_eq s scrb ▸ hmb)
    · intro i h1 h2; rw [hmv_eq] at h1 h2; exact hkb.2.2.2.2.1 i h1 h2
    · intro i h1 h2; rw [hmv_eq] at h1 h2; exact hkb.2.2.2.2.2.1 i h1 h2
    · intro i h1 h2; rw [hmv_eq] at h1 h2; exact hkb.2.2.2.2.2.2 i h1 h2
  unfold Func.wp full_k6_prop_fid_body
  c0_hsplit
  · c0_hsteps!; exact hret_noop
  · c0_hsplit
    · c0_hsteps!; exact hret_noop
    · c0_hsplit
      · c0_hsteps!; exact hret_noop
      · have hnv_le : nv.toNat ≤ mv.toNat := Nat.le_of_not_lt hc
        c0_hsplit
        · c0_hsteps!; exact hret_noop
        · have hnc_le : nc.toNat ≤ 4 * mv.toNat := by dsimp only [nc, mv] at *; fid_omega
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i64])
            (fun rem (ticks, ()) m => ∃ scrl : List (BitVec 32), ∃ qp : BitVec 32,
              scrl[4196]? = some qp ∧ FidPropKeep scr0 mv.toNat scrl ∧
              rem = mv.toNat - qp.toNat ∧ (FullMem c (m8ScrSt s scrl) ⋆ R) m) ?_ ?_
          · rintro L1 rem ⟨ticks, ⟨⟩⟩ m hL1 ⟨scrl, qp, h4196_eq, hkl, rfl, hml⟩
            have hll : scrl.length = scr0.length := hkl.1
            have h4196_l : 4196 < scrl.length := by omega
            have h4197_l : 4197 < scrl.length := by omega
            have hqp_eq : scrl[4196]'h4196_l = qp := by
              rw [← Option.some_inj, ← List.getElem?_eq_getElem]; exact h4196_eq
            c0_hsteps_nogrp
            refine wp_join0 (fun m1 => ∃ scrb : List (BitVec 32), FidPropKeep scr0 mv.toNat scrb ∧
                (FullMem c (m8ScrSt s scrb) ⋆ R) m1)
              (fun _ mb ⟨scrb, hkb, hmb⟩ => by
                c0_hsteps_nogrp
                exact fidProp_call_add_ticks hTicks hlen hscr_len h4214 hmv_eq hmin hkb hmb
                  (fun scrc mc hkc _ hmc => hq_ret 4294967295#32 scrc mc hkc hmc))
              (fun J1 hJ1 => by
                c0_hsplit
                · c0_hsplit
                  · have hqp_lt : qp.toNat < mv.toNat := by
                      have hc' := hc; clear hc; fid_norm_ofnat
                      try simp (disch := fid_omega) only [bv_c0, Nat.reducePow, BitVec.reduceToNat]
                        at hc'
                      try rw [hqp_eq] at hc'
                      exact hc'
                    have hqp1 : (qp + 1#32).toNat = qp.toNat + 1 :=
                      m8_bv32_add1_toNat hqp_lt (by omega)
                    have htr_e := fid_k6_off_add (mv := mv) (k := 5) (x := qp) hmv_hi (by decide)
                      (by omega)
                    have htr_lt : ((4224 + 5 * mv + qp).setWidth 64).toNat < scrl.length := by
                      rw [hll, htr_e]; exact fidProp_k_lt 5 (by omega) hmv_lo hbge
                    have htr_lt' : (((4224 : BitVec 32) + (5 : BitVec 32) * scr0[4214]'h4214 +
                        scrl[4196]'h4196_l).setWidth 64).toNat < scrl.length := by
                      rw [hqp_eq]; exact htr_lt
                    let plit := scrl[((4224 + 5 * mv + qp).setWidth 64).toNat]'htr_lt
                    let scrl1 := scrl.set 4196 (qp + 1#32)
                    have hk_l1 : FidPropKeep scr0 mv.toNat scrl1 :=
                      fidPropKeep_set hkl (qp + 1#32) (Or.inl ⟨by decide, by decide⟩)
                    have h4196_1 : scrl1[4196]? = some (qp + 1#32) := by
                      dsimp only [scrl1]; rw [List.getElem?_set_self h4196_l]
                    have hll1 : scrl1.length = scr0.length := hk_l1.1
                    c0_hstraight
                    have hscrl1_eq : scrl.set (@OfNat.ofNat Nat 4196 _)
                        (scrl[@OfNat.ofNat Nat 4196 _]'h4196_l + 1#32) = scrl1 := by
                      fid_norm_ofnat; dsimp only [scrl1]; rw [hqp_eq]
                    have hm1 : (FullMem c (m8ScrSt s scrl1) ⋆ R) m := hscrl1_eq ▸ hm
                    clear hm
                    c0_hsplit
                    · c0_hsteps!
                      exact hL1 (mv.toNat - (qp + 1#32).toNat) (ticks, ()) _ (by omega)
                        ⟨scrl1, qp + 1#32, h4196_1, hk_l1, rfl, hm1⟩
                    · have hplit_lt : plit.toNat < 2 * nv.toNat := by
                        have hc' := hc; clear hc; fid_norm_ofnat
                        simp (disch := fid_omega) only [bv_c0, Nat.reducePow, BitVec.reduceToNat]
                          at hc'
                        have h1 := Nat.lt_of_not_le hc'
                        have hnv_bnd : scr0[4192].toNat ≤ 8192 := by
                          dsimp only [nv, mv] at hnv_le hmv_hi; omega
                        rw [Nat.mod_eq_of_lt (by omega : scr0[4192].toNat * 2 < 2 ^ 32)] at h1
                        have htr_mod : (4224 + 5 * mv.toNat + scrl[4196].toNat) % 4294967296 =
                            ((4224 + 5 * mv + qp).setWidth 64).toNat := by
                          rw [hqp_eq, htr_e, Nat.mod_eq_of_lt (by omega)]
                        have h2 := congrArg BitVec.toNat
                          (m8_k6_get_congr htr_mod (by rw [htr_mod]; exact htr_lt) htr_lt)
                        dsimp only [mv, nv] at h1 h2 ⊢; rw [← h2]; omega
                      let flit := plit ^^^ 1#32
                      have hflit_lt : flit.toNat < 2 * nv.toNat :=
                        (m8_bv32_xor1_lt plit hplit_lt).2
                      have hwh_e := fid_k6_off_add (mv := mv) (k := 11) (x := flit) hmv_hi
                        (by decide) (by omega)
                      have hwh_lt : ((4224 + 11 * mv + flit).setWidth 64).toNat <
                          scrl1.length := by
                        rw [hll1, hwh_e]; exact fidProp_k_lt 11 (by omega) hmv_lo hbge
                      have hplit_eq : scrl[(((4224 : BitVec 32) +
                          (5 : BitVec 32) * scr0[4214]'h4214 +
                          scrl[4196]'h4196_l).setWidth 64).toNat]'htr_lt' = plit := by
                        refine m8_k6_get_congr ?_ htr_lt' htr_lt
                        rw [hqp_eq]
                      have hwh_lt' : (((4224 : BitVec 32) + (11 : BitVec 32) * scr0[4214]'h4214 +
                          (scrl[(((4224 : BitVec 32) + (5 : BitVec 32) * scr0[4214]'h4214 +
                          scrl[4196]'h4196_l).setWidth 64).toNat]'htr_lt' ^^^
                          (1 : BitVec 32))).setWidth 64).toNat < scrl1.length := by
                        rw [hplit_eq]; exact hwh_lt
                      let wh := scrl1[((4224 + 11 * mv + flit).setWidth 64).toNat]'hwh_lt
                      have hmv4 : (mv <<< (2 : BitVec 32)).toNat = 4 * mv.toNat := by
                        change (mv <<< 2).toNat = 4 * mv.toNat
                        rw [BitVec.toNat_shiftLeft]; simp only [Nat.shiftLeft_eq]; omega
                      c0_hstraight
                      simp only [hplit_eq]
                      exact fidProp_watch_loop_wp Γ c s R Q X scr0 scrl1 (mv <<< (2 : BitVec 32))
                        flit wh ticks L1 m hTicks hAssign hlen hok hscr_len h4214 hmv_lo hmv_hi
                        hnv_le hnc_le hlen_scr hbge hcap_lt hmv4 hflit_lt hk_l1 hm1
                        (fun scrb ticks' mb hkb h4196b hmb => by
                          c0_hsteps!
                          exact hL1 (mv.toNat - (qp + 1#32).toNat) (ticks', ()) mb (by omega)
                            ⟨scrb, qp + 1#32, h4196b.trans h4196_1, hkb, rfl, hmb⟩)
                        hq_ret
                  · c0_hsteps!; exact hJ1 m ⟨scrl, hkl, hml⟩
                · c0_hsteps!; exact hJ1 m ⟨scrl, hkl, hml⟩)
          · intro L1 hL1; c0_hsteps!
            exact hL1 (mv.toNat - (scr0[4196]'h4196).toNat) (0#64, ()) m0
              ⟨scr0, scr0[4196]'h4196, List.getElem?_eq_getElem h4196,
                fidPropKeep_refl scr0 mv.toNat, rfl, hm0'⟩


end

end LeanQbe.T.Examples.Kissat.Proof.Definition
