/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpOtfsLarge1
public import LeanQbe.T.Examples.Kissat.Src.Deduce
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpCommon
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import Kraken.Mem
import Kraken.Separation

/-!
# Large OTFS Header, Swap, Watch Update & Full WP (`Proof.Deduce.WpOtfsLarge2`)

Weakest-precondition proofs for clause header/glue/sentinel updates, slot-1/`best_pos` swap,
reverse watch-stack blocking-literal update, and `full_otfs_large_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Deduce

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics DeduceTactics

/-! ## 1. Pure Watch-Stack Update & BitVec Helpers -/

theorem otfs_bv64_zext_shl1 (l : BitVec 32) :
    (BitVec.setWidth 64 l <<< (1 : Nat)).toNat = 2 * l.toNat := by
  have hs : (BitVec.signExtend 64 1#32 : BitVec 64) = 1#64 := rfl
  have h1 : (BitVec.setWidth 64 l <<< (1 : Nat)) =
      (BitVec.setWidth 64 l <<< BitVec.signExtend 64 1#32) := by
    rw [hs]; rfl
  rw [h1, otfs_bv64_shl_sext1 (l.setWidth 64)
      (by rw [zext_toNat l (by decide)]; have := l.isLt; omega),
    zext_toNat l (by decide)]

theorem otfs_bv64_zext_shl1_add1 (l : BitVec 32) :
    (BitVec.setWidth 64 l <<< (1 : Nat) + (1 : BitVec 64)).toNat = 2 * l.toNat + 1 := by
  have hlt : l.toNat < 2 ^ 32 := l.isLt
  rw [BitVec.toNat_add, otfs_bv64_zext_shl1 l,
    show ((1 : BitVec 64)).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]

theorem otfs_bv_idx4_64 (cref : BitVec 32) (h : cref.toNat + 4 < 2 ^ 32) :
    (BitVec.setWidth 64 cref + 3#64 + 1#64).toNat = cref.toNat + 4 :=
  otfs_bv_idx3_64 cref 1 (by omega) (by decide)

theorem s13_otfs_loop4_hit_watches {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} {l0 w0' cref : BitVec 32} {p_nat : Nat}
    (hlen : k.LengthsOk c) (hdm : k.dense_mode = 0#64) (hmw : ModeWatchesInv F_cur k)
    (hl0 : l0.toNat < 2 * k.cur_vars)
    (hp_lo : fullWatchOffCore k l0.toNat + 2 ≤ p_nat)
    (hp_hi : p_nat ≤ fullWatchOffCore k l0.toNat + fullWatchSizeCore k l0.toNat)
    (hpre : WatchSliceOk F_cur k l0.toNat (fullWatchOffCore k l0.toNat)
      (p_nat - 2 - fullWatchOffCore k l0.toNat))
    (hsuf : WatchSliceOk F_cur k l0.toNat p_nat
      (fullWatchOffCore k l0.toNat + fullWatchSizeCore k l0.toNat - p_nat))
    (hcr : k.wstk[p_nat - 1]? = some cref)
    (hw0' : (w0' &&& 0x80000000#32) = 0#32)
    (hcr_lt : cref.toNat < 0x80000000)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore k) :
    let k' := { k with wstk := k.wstk.set (p_nat - 2) w0' }
    k'.LengthsOk c ∧ ModeWatchesInv F_cur k' := by
  intro k'
  have hwat : WatchesInv F_cur k := by simpa only [ModeWatchesInv, hdm, ↓reduceIte] using hmw
  have hlay := hwat.layout
  have hbd0 := hlay.bounds l0.toNat hl0
  have hwl_le := hlen.wlen_le
  have hws_len := hlen.wstk_len_arr
  have hp2_lt : p_nat - 2 < k.wstk.length := by omega
  have hw0'_ne : w0' ≠ 0xFFFFFFFF#32 := by
    intro h; rw [h] at hw0'; exact absurd hw0' (by decide)
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  have hdisj : ∀ l < 2 * k.cur_vars, l ≠ l0.toNat → ∀ idx < fullWatchSizeCore k l,
      fullWatchOffCore k l + idx ≠ p_nat - 2 := by
    intro l hl hne idx hidx
    have h0l : 0 < fullWatchSizeCore k l := by omega
    have h0l0 : 0 < fullWatchSizeCore k l0.toNat := by omega
    rcases hlay.disjoint l l0.toNat hl hl0 hne h0l h0l0 with h1 | h2 <;> omega
  have hlay' : WatchStackLayout k' := by
    refine ⟨hlay.bounds, hlay.pos_off, hlay.disjoint, fun l hl idx hidx => ?_⟩
    by_cases hll0 : l = l0.toNat
    · subst l
      by_cases heq : fullWatchOffCore k l0.toNat + idx = p_nat - 2
      · change (k.wstk.set (p_nat - 2) w0')[fullWatchOffCore k l0.toNat + idx]? ≠ some 0xFFFFFFFF#32
        rw [heq, List.getElem?_set_self hp2_lt]; exact fun h => absurd (Option.some.inj h) hw0'_ne
      · change (k.wstk.set (p_nat - 2) w0')[fullWatchOffCore k l0.toNat + idx]? ≠ some 0xFFFFFFFF#32
        rw [List.getElem?_set_ne (Ne.symm heq)]; exact hlay.no_sentinel _ hl0 idx hidx
    · change (k.wstk.set (p_nat - 2) w0')[fullWatchOffCore k l + idx]? ≠ some 0xFFFFFFFF#32
      rw [List.getElem?_set_ne (Ne.symm (hdisj l hl hll0 idx hidx))]
      exact hlay.no_sentinel l hl idx hidx
  have hslices' : ∀ l < 2 * k'.cur_vars,
      WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l) := by
    intro l hl
    by_cases hll0 : l = l0.toNat
    · subst l
      have hpre' : WatchSliceOk F_cur k' l0.toNat (fullWatchOffCore k l0.toNat)
          (p_nat - 2 - fullWatchOffCore k l0.toNat) :=
        fullWatchSlice_relocate (k := k) (k' := k') (p := fullWatchOffCore k l0.toNat)
          (p' := fullWatchOffCore k l0.toNat) hrefl (Nat.le_refl _) (fun _ h => h)
          (fun idx hidx => by
            dsimp only [k']; rw [List.getElem?_set_ne (by omega)]) hpre
      have happ := fullWatchSlice_append_large (Nat.le_refl _) (fun _ h => h)
        (fun _ _ => rfl) hpre'
        (by dsimp only [k']
            rw [show fullWatchOffCore k l0.toNat + (p_nat - 2 - fullWatchOffCore k l0.toNat) =
                p_nat - 2 by omega, List.getElem?_set_self hp2_lt])
        (by dsimp only [k']
            rw [show fullWatchOffCore k l0.toNat + (p_nat - 2 - fullWatchOffCore k l0.toNat) + 1 =
                p_nat - 1 by omega, List.getElem?_set_ne (by omega), hcr])
        hw0' hcr_lt hcr_ref
      have hsuf' : WatchSliceOk F_cur k' l0.toNat p_nat
          (fullWatchOffCore k l0.toNat + fullWatchSizeCore k l0.toNat - p_nat) :=
        fullWatchSlice_relocate (k := k) (k' := k') (p := p_nat) (p' := p_nat) hrefl
          (Nat.le_refl _) (fun _ h => h)
          (fun idx hidx => by
            dsimp only [k']; rw [List.getElem?_set_ne (by omega)]) hsuf
      have hfin := otfs_watchSlice_append happ
        (by rwa [show fullWatchOffCore k l0.toNat +
            (p_nat - 2 - fullWatchOffCore k l0.toNat + 2) = p_nat by omega])
      rwa [show p_nat - 2 - fullWatchOffCore k l0.toNat + 2 +
          (fullWatchOffCore k l0.toNat + fullWatchSizeCore k l0.toNat - p_nat) =
          fullWatchSizeCore k l0.toNat by omega] at hfin
    · exact fullWatchSlice_relocate (k := k) (k' := k') (p := fullWatchOffCore k l)
        (p' := fullWatchOffCore k l) hrefl (Nat.le_refl _) (fun _ h => h)
        (fun idx hidx => by
          dsimp only [k']; rw [List.getElem?_set_ne (Ne.symm (hdisj l hl hll0 idx hidx))])
        (hwat.slices l hl)
  refine ⟨{ hlen with wstk_len_arr := by simp [k', hws_len] }, ?_⟩
  have hwat' : WatchesInv F_cur k' := ⟨hlay', hslices'⟩
  dsimp only [k'] at hwat'
  dsimp only [ModeWatchesInv]
  simp only [show k'.dense_mode = 0#64 from by simpa [k'] using hdm, ite_true]
  exact hwat'

theorem otfs_bv64_sub1_toNat {p : BitVec 64} (hp : 1 ≤ p.toNat) :
    (p - (1 : BitVec 64)).toNat = p.toNat - 1 :=
  BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (1 : BitVec 64).toNat = 1 from rfl]; omega)

theorem otfs_bv64_sub2_toNat {p : BitVec 64} (hp : 2 ≤ p.toNat) :
    (p - (2 : BitVec 64)).toNat = p.toNat - 2 :=
  BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (2 : BitVec 64).toNat = 2 from rfl]; omega)

/-! ## 2. Header, Glue Tightening, Flags & Shrink Sentinel WP -/

@[expose] def otfs_hdr_shrink_expr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (hdr pArena cr3 : V i64) (cref old_sz nsz uip : V i32)
    (cont : Expr V L rs) : Expr V L rs :=
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var cref, ())) fun p_30 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_30.fst, Arg.imm 4, ())) fun p_31 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pArena, Arg.var p_31.fst, ())) fun p_32 =>
  Expr.load i32 (Arg.var p_32.fst) fun ld_5 =>
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var cref, ())) fun p_33 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_33.fst, Arg.imm 2, ())) fun p_34 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_34.fst, Arg.imm 4, ())) fun p_35 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pArena, Arg.var p_35.fst, ())) fun p_36 =>
  Expr.store (Arg.var nsz) (Arg.var p_36.fst)
    (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var cref, ())) fun p_37 =>
     Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_37.fst, Arg.imm 1, ())) fun p_38 =>
     Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_38.fst, Arg.imm 4, ())) fun p_39 =>
     Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pArena, Arg.var p_39.fst, ())) fun p_40 =>
     Expr.store (t := i32) (Arg.imm 2) (Arg.var p_40.fst)
       (Expr.group (sig := [[i32]]) (fun Js =>
         Blocks.cons (fun p_41 =>
           Expr.group (sig := [[]]) (fun Js_s =>
             Blocks.cons (fun _ => cont) Blocks.nil)
           fun Js_s =>
             Expr.let_ (Op.mk (OpCode.and i32) (Arg.var p_41.fst, Arg.imm 8388608, ())) fun p_42 =>
             Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i32) (Arg.var p_42.fst, Arg.imm 0, ()))
               fun p_43 =>
             Expr.jnz (Arg.var p_43.fst)
               (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var cref, ())) fun pa0 =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pa0.fst, Arg.imm 4, ())) fun pa1 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pArena, Arg.var pa1.fst, ())) fun pa2 =>
                Expr.let_ (Op.mk (OpCode.or i32)
                    (Arg.var p_41.fst, Arg.imm 8388608, ())) fun p_44 =>
                Expr.store (Arg.var p_44.fst) (Arg.var pa2.fst)
                  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var old_sz, ())) fun pb0 =>
                   Expr.let_ (Op.mk (OpCode.add i64) (Arg.var cr3, Arg.var pb0.fst, ())) fun pb1 =>
                   Expr.let_ (Op.mk (OpCode.sub i64) (Arg.var pb1.fst, Arg.imm 1, ())) fun pb2 =>
                   Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pb2.fst, Arg.imm 4, ())) fun pb3 =>
                   Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pArena, Arg.var pb3.fst, ()))
                     fun pb4 =>
                   Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var pb4.fst)
                     (Expr.jump Js_s.fst ())))
               (Expr.jump Js_s.fst ())) Blocks.nil)
        fun Js =>
          Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld_5, Arg.imm 4194304, ())) fun p_41 =>
          Expr.let_ (Op.mk (OpCode.cmp CmpOp.ne i32) (Arg.var p_41.fst, Arg.imm 0, ())) fun p_42 =>
          Expr.jnz (Arg.var p_42.fst)
            (Expr.group (sig := [[i32]]) (fun Js_1 =>
               Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil)
             fun Js_g =>
               Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld_5, Arg.imm 524287, ())) fun p_43 =>
               Expr.let_ (Op.mk (OpCode.cmp CmpOp.uge i32) (Arg.var p_43.fst, Arg.var nsz, ()))
                 fun p_44 =>
               Expr.jnz (Arg.var p_44.fst)
                 (Expr.let_ (Op.mk (OpCode.not i32) (Arg.imm 524287, ())) fun p_45 =>
                  Expr.let_ (Op.mk (OpCode.and i32)
                      (Arg.var ld_5, Arg.var p_45.fst, ())) fun p_46 =>
                  Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var nsz, Arg.imm 1, ())) fun p_47 =>
                  Expr.let_ (Op.mk (OpCode.or i32) (Arg.var p_46.fst, Arg.var p_47.fst, ()))
                    fun p_48 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var cref, ())) fun pc0 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pc0.fst, Arg.imm 4, ())) fun pc1 =>
                  Expr.let_ (Op.mk (OpCode.add i64)
                      (Arg.var pArena, Arg.var pc1.fst, ())) fun pc2 =>
                  Expr.store (Arg.var p_48.fst) (Arg.var pc2.fst)
                    (Expr.jump Js_g.fst (Arg.var p_48.fst, ())))
                 (Expr.jump Js_g.fst (Arg.var ld_5, ())))
            (otfs_flags_expr hdr pArena cr3 uip nsz ld_5 Js.fst)))

theorem s13_otfs_hdr_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {s s2 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {cref _l0 uip : BitVec 32} {ar1 ar_cur : List (BitVec 32)} {old_sz nsz : Nat}
    {origMap : List Nat}
    (hlen2 : s2.LengthsOk c)
    (hm : (FullMem c { s2 with core := { s2.core with arena := ar_cur } } ⋆ R) m)
    (har_len : s.core.arena.length = c.arena_cap)
    (har_c : ar_cur.length = c.arena_cap)
    (hcap : c.arena_cap < 2 ^ 31 - 1)
    (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap) (h4_old : 4 ≤ old_sz)
    (h3_nsz : 3 ≤ nsz) (hnsz_lt : nsz < old_sz) (huip_bd : uip.toNat < 2 * s2.core.cur_vars)
    (hlits : ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ 4294967295#32)
    (hcv_eq : s2.core.cur_vars = s.core.cur_vars)
    (hmapeq : ∀ k < nsz,
      ar_cur[cref.toNat + 3 + k]? = s.core.arena[cref.toNat + 3 + origMap[k]?.getD 0]?)
    (hmapeq_bd : ∀ k < nsz, origMap[k]?.getD 0 < old_sz)
    (hout_cur : ∀ q, q < cref.toNat + 4 ∨ cref.toNat + 3 + nsz ≤ q → ar_cur[q]? = ar1[q]?)
    (har1_2 : ∀ q, 2 ≤ q → ar1[cref.toNat + 3 + q]? = s.core.arena[cref.toNat + 3 + q]?)
    (har1_s2 : ∀ i, i < cref.toNat + 3 ∨ cref.toNat + 5 ≤ i → ar1[i]? = s2.core.arena[i]?)
    (hhdr_eq : ar_cur[cref.toNat]? = some (fullArenaHdrCore s2.core cref.toNat))
    (cont : Expr Val Cont [.bool])
    (hcont : ∀ ml3, S13OtfsHdrPost c s s2 R cref old_sz nsz origMap ml3 →
      wp Γ Q X cont ml3) :
    wp Γ Q X (otfs_hdr_shrink_expr c.hdr c.pArena (cref.setWidth 64 + 3#64) cref
      (BitVec.ofNat 32 old_sz) (BitVec.ofNat 32 nsz) uip cont) m := by
  have hfl_len := hlen2.core_ok.flags_len
  have hcr0_z : (cref.setWidth 64).toNat = cref.toNat := zext_toNat cref (by decide)
  have hcr1_z : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1 := by
    rw [BitVec.toNat_add, hcr0_z, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hcr2_z : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by
    rw [BitVec.toNat_add, hcr0_z, show (2#64 : BitVec 64).toNat = 2 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hcr3_z : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by
    rw [BitVec.toNat_add, hcr0_z, show (3#64 : BitVec 64).toNat = 3 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hcr0_bd : (cref.setWidth 64).toNat < ar_cur.length := by rw [har_c, hcr0_z]; omega
  let hdr0 := fullArenaHdrCore s2.core cref.toNat
  have hbd0 : cref.toNat < ar_cur.length := by rw [har_c]; omega
  have hhdr_cref : ar_cur[cref.toNat]'hbd0 = hdr0 := by
    rw [← Option.some_inj, ← List.getElem?_eq_getElem hbd0, hhdr_eq]
  have hhdr_idx : ar_cur[(cref.setWidth 64).toNat]'hcr0_bd = hdr0 :=
    (getElem_eq_of_idx (hj := hbd0) hcr0_z).trans hhdr_cref
  have hcr2_bd : (cref.setWidth 64 + 2#64).toNat < ar_cur.length := by rw [har_c, hcr2_z]; omega
  have hcr1_bd : (cref.setWidth 64 + 1#64).toNat <
      (ar_cur.set (cref.setWidth 64 + 2#64).toNat (BitVec.ofNat 32 nsz)).length := by
    rw [List.length_set, har_c, hcr1_z]; omega
  let ar_a := (ar_cur.set (cref.toNat + 2) (BitVec.ofNat 32 nsz)).set (cref.toNat + 1) 2#32
  have har_a_eq : ((ar_cur.set (cref.setWidth 64 + 2#64).toNat (BitVec.ofNat 32 nsz)).set
      (cref.setWidth 64 + 1#64).toNat 2#32) = ar_a := by
    dsimp only [ar_a]; rw [hcr2_z, hcr1_z]
  have har_a_len : ar_a.length = c.arena_cap := by simp [ar_a, har_c]
  have hcr0_bda : (cref.setWidth 64).toNat < ar_a.length := by rw [har_a_len, hcr0_z]; omega
  have h_end_bd : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 old_sz).setWidth 64 - 1#64).toNat =
      cref.toNat + 3 + old_sz - 1 := by
    have hz_o : ((BitVec.ofNat 32 old_sz).setWidth 64).toNat = old_sz := by
      rw [zext_toNat _ (by decide), bv32_ofNat_toNat (by omega)]
    have hsum : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 old_sz).setWidth 64).toNat =
        cref.toNat + 3 + old_sz := by
      rw [BitVec.toNat_add, hcr3_z, hz_o, Nat.mod_eq_of_lt (by omega)]
    have hle1 : (1#64 : BitVec 64) ≤
        cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 old_sz).setWidth 64 := by
      rw [BitVec.le_def, hsum, show (1#64 : BitVec 64).toNat = 1 from rfl]; omega
    rw [BitVec.toNat_sub_of_le hle1, hsum, show (1#64 : BitVec 64).toNat = 1 from rfl]
  let hdr_gl :=
    if hdr0 &&& 4194304#32 ≠ 0#32 ∧ nsz ≤ (hdr0 &&& 524287#32).toNat then
      hdr0 &&& ~~~524287#32 ||| BitVec.ofNat 32 nsz - 1#32
    else hdr0
  let ar_b :=
    if hdr0 &&& 4194304#32 ≠ 0#32 ∧ nsz ≤ (hdr0 &&& 524287#32).toNat then
      ar_a.set cref.toNat hdr_gl
    else ar_a
  have har_b_len : ar_b.length = c.arena_cap := by dsimp only [ar_b]; split <;> simp [har_a_len]
  unfold otfs_hdr_shrink_expr
  c0_hstraight
  dsimp only at *
  refine wp_join_group (ts := [i32])
    (fun (hgl_v, ()) ml1 => ∃ fl3 : List (BitVec 32),
      hgl_v = hdr_gl ∧ fl3.length = c.max_vars ∧
      (FullMem c { s2 with core := { s2.core with arena := ar_b, flags := fl3 } } ⋆ R) ml1)
    ?_ ?_
  · rintro Js ⟨hgl_v, ⟨⟩⟩ ml1 ⟨fl3, rfl, hfl3_len, hml1⟩
    refine wp_join_group (ts := [])
      (fun _ ml3 => S13OtfsHdrPost c s s2 R cref old_sz nsz origMap ml3)
      ?_ ?_
    · intro Js_s _ ml3 hpost; c0_hstraight; exact hcont ml3 hpost
    · intro Js_s hJs_s
      have hcr0_bdb : (cref.setWidth 64).toNat < ar_b.length := by rw [har_b_len, hcr0_z]; omega
      have h_end_bdb : (cref.setWidth 64 + 3#64 +
          (BitVec.ofNat 32 old_sz).setWidth 64 - 1#64).toNat <
          (ar_b.set (cref.setWidth 64).toNat (hdr_gl ||| 8388608#32)).length := by
        rw [List.length_set, har_b_len, h_end_bd]; omega
      c0_hstraight
      c0_hstep_np
      · have hsh_zero : hdr_gl &&& 8388608#32 = 0#32 := by
          have hc' : (hdr_gl &&& 8388608#32).toNat = (0#32 : BitVec 32).toNat := by c0_bound
          exact BitVec.eq_of_toNat_eq hc'
        c0_hstraight
        dsimp only at *
        have har3_eq : ((ar_b.set (cref.setWidth 64).toNat (hdr_gl ||| 8388608#32)).set
            (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 old_sz).setWidth 64 - 1#64).toNat
              4294967295#32) =
            (ar_b.set cref.toNat (hdr_gl ||| 8388608#32)).set
              (cref.toNat + 3 + old_sz - 1) 4294967295#32 := by
          rw [hcr0_z, h_end_bd]
        apply hJs_s ()
        exact s13_otfs_hdr_ok true har_len har_c h3o h4_old h3_nsz hnsz_lt hlits hmapeq
          hout_cur har1_2 har1_s2 hhdr_eq hfl3_len (Or.inl ⟨rfl, hsh_zero⟩) (by assumption) har3_eq
      · have hsh_nz : hdr_gl &&& 8388608#32 ≠ 0#32 := by
          intro h
          have hc' : (hdr_gl &&& 8388608#32).toNat ≠ (0#32 : BitVec 32).toNat := by c0_bound
          exact hc' (congrArg BitVec.toNat h)
        c0_hstraight
        dsimp only at *
        apply hJs_s ()
        exact s13_otfs_hdr_ok false har_len har_c h3o h4_old h3_nsz hnsz_lt hlits hmapeq
          hout_cur har1_2 har1_s2 hhdr_eq hfl3_len (Or.inr ⟨rfl, hsh_nz⟩) hml1 rfl
  · intro Js hJs
    c0_hstraight
    dsimp only at *
    c0_hstep_np
    · have hred_nz : hdr0 &&& 4194304#32 ≠ 0#32 := by
        rw [← hhdr_cref]; exact hc
      clear hc
      refine wp_join_group (ts := [i32])
        (fun (hgl_v, ()) ml1 => hgl_v = hdr_gl ∧
          (FullMem c { s2 with core := { s2.core with arena := ar_b } } ⋆ R) ml1) ?_ ?_
      · rintro Js_g ⟨hgl_v, ⟨⟩⟩ ml1 ⟨rfl, hml1⟩
        c0_hstraight; exact hJs (hdr_gl, ()) ml1 ⟨s2.core.flags, rfl, hfl_len, hml1⟩
      · intro Js_g hJs_g
        c0_hstraight
        dsimp only at *
        c0_hstep_np
        · have hge_nsz : nsz ≤ (hdr0 &&& 524287#32).toNat := by
            rw [Nat.mod_eq_of_lt (by omega), hhdr_cref] at hc; exact hc
          have hcond : hdr0 &&& 4194304#32 ≠ 0#32 ∧ nsz ≤ (hdr0 &&& 524287#32).toNat :=
            ⟨hred_nz, hge_nsz⟩
          have hhgl_eq : hdr_gl = hdr0 &&& ~~~524287#32 ||| BitVec.ofNat 32 nsz - 1#32 := by
            simp only [hdr_gl, ite_eq_left_iff]; intro h; exact absurd hcond h
          have har_b_eq : ar_b = ar_a.set cref.toNat hdr_gl := by
            simp only [ar_b, ite_eq_left_iff]; intro h; exact absurd hcond h
          c0_hstraight
          dsimp only at *
          have hgl_v_eq : (ar_cur[(cref.setWidth 64).toNat]'hcr0_bd &&& ~~~(524287 : BitVec 32) |||
              (BitVec.ofNat 32 nsz - (1 : BitVec 32))) = hdr_gl := by
            rw [hhdr_idx, hhgl_eq]; rfl
          refine hJs_g (_, ()) _ ⟨hgl_v_eq, ?_⟩
          rw [har_b_eq, ← hgl_v_eq, ← har_a_eq, ← hcr0_z]; assumption
        · have hlt_nsz : ¬ nsz ≤ (hdr0 &&& 524287#32).toNat := by
            rw [Nat.mod_eq_of_lt (by omega), hhdr_cref] at hc; exact hc
          have hcond : ¬ (hdr0 &&& 4194304#32 ≠ 0#32 ∧ nsz ≤ (hdr0 &&& 524287#32).toNat) :=
            fun h => hlt_nsz h.2
          have hhgl_eq : hdr_gl = hdr0 := by
            simp only [hdr_gl, ite_eq_right_iff]; intro h; exact absurd h hcond
          have har_b_eq : ar_b = ar_a := by
            simp only [ar_b, ite_eq_right_iff]; intro h; exact absurd h hcond
          c0_hstraight
          refine hJs_g (_, ()) _ ⟨by rw [hhdr_idx, hhgl_eq], ?_⟩
          rw [har_b_eq, ← har_a_eq]; assumption
    · have hred_z : ¬ (hdr0 &&& 4194304#32 ≠ 0#32) := by
        rw [← hhdr_cref]; exact fun h => h hc
      have hcond : ¬ (hdr0 &&& 4194304#32 ≠ 0#32 ∧ nsz ≤ (hdr0 &&& 524287#32).toNat) :=
        fun h => hred_z h.1
      have hhgl_eq : hdr_gl = hdr0 := by
        simp only [hdr_gl, ite_eq_right_iff]; intro h; exact absurd h hcond
      have har_b_eq : ar_b = ar_a := by
        simp only [ar_b, ite_eq_right_iff]; intro h; exact absurd h hcond
      have hlits_a : ∀ k < nsz,
          (ar_a[cref.toNat + 3 + k]?.getD 0#32).toNat < 2 * s2.core.cur_vars := by
        intro k hk
        dsimp only [ar_a]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hmapeq k hk, hcv_eq]
        exact (hlits (origMap[k]?.getD 0) (hmapeq_bd k hk)).1
      rw [hhdr_idx]
      refine s13_otfs_flags_wp (R := R) hlen2 ?_ har_a_len hcap h3o hnsz_lt huip_bd hlits_a ?_
      · rw [← har_a_eq]; assumption
      · intro fl3 m' hfl3_len hm'
        refine hJs (hdr0, ()) m' ⟨fl3, hhgl_eq.symm, hfl3_len, ?_⟩
        simpa only [har_b_eq] using hm'

/-! ## 3. Best-Pos Swap (`full_otfs_large`) -/

@[expose] def otfs_swap_bp_expr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (pArena cr3 : V i64) (best_pos : V i32) (cont : Expr V L rs) : Expr V L rs :=
  Expr.group (sig := [[]]) (fun Js =>
    Blocks.cons (fun _ => cont) Blocks.nil)
  fun Js =>
    Expr.let_ (Op.mk (OpCode.cmp CmpOp.ne i32) (Arg.var best_pos, Arg.imm 1, ())) fun p =>
    Expr.jnz (Arg.var p.fst)
      (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var cr3, Arg.imm 1, ())) fun p0 =>
       Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p0.fst, Arg.imm 4, ())) fun p1 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pArena, Arg.var p1.fst, ())) fun p2 =>
       Expr.load i32 (Arg.var p2.fst) fun ld_6 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var cr3, Arg.imm 1, ())) fun q0 =>
       Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var q0.fst, Arg.imm 4, ())) fun q1 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pArena, Arg.var q1.fst, ())) fun q2 =>
       Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var best_pos, ())) fun p_43 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var cr3, Arg.var p_43.fst, ())) fun p_44 =>
       Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_44.fst, Arg.imm 4, ())) fun p_45 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pArena, Arg.var p_45.fst, ())) fun p_46 =>
       Expr.load i32 (Arg.var p_46.fst) fun ld_7 =>
       Expr.store (Arg.var ld_7) (Arg.var q2.fst)
         (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var best_pos, ())) fun r0 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var cr3, Arg.var r0.fst, ())) fun r1 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var r1.fst, Arg.imm 4, ())) fun r2 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pArena, Arg.var r2.fst, ())) fun r3 =>
          Expr.store (Arg.var ld_6) (Arg.var r3.fst) (Expr.jump Js.fst ())))
      (Expr.jump Js.fst ())

theorem s13_otfs_swap_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {s3 : FullState} {R : Mem 64 → Prop} {m : Mem 64} {cref : BitVec 32} {bp : Nat}
    (hlen3 : s3.LengthsOk c) (hw3 : FullWitnessCutInv c F0 F_cur cut s3.core)
    (hnd3 : FullArenaVarsNodup s3) (hm : (FullMem c s3 ⋆ R) m)
    (hcap : c.arena_cap < 2 ^ 31 - 1)
    (hcref3 : cref.toNat ∈ fullArenaClauseRefs s3)
    (hng3 : fullArenaClauseGarb s3 cref.toNat = false)
    (hbp_ge1 : 1 ≤ bp) (hbp_lt : bp < fullArenaClauseSize s3 cref.toNat)
    (cont : Expr Val Cont [.bool])
    (hcont : ∀ (s4 : FullState) (m' : Mem 64),
      (∃ ar4, s4 = { s3 with core := { s3.core with arena := ar4 } }) →
      s4.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s4.core →
      FullArenaVarsNodup s4 → fullArenaClauseRefs s4 = fullArenaClauseRefs s3 →
      fullArenaClauseGarb s4 cref.toNat = false →
      (fullArenaClauseLits s4 cref.toNat).Perm (fullArenaClauseLits s3 cref.toNat) →
      (FullMem c s4 ⋆ R) m' → wp Γ Q X cont m') :
    wp Γ Q X (otfs_swap_bp_expr c.pArena (cref.setWidth 64 + 3#64)
      (BitVec.ofNat 32 bp) cont) m := by
  have hwf := hw3.arena.refs_wf cref.toNat hcref3
  have hal := hlen3.core_ok.arena_len_le
  have har_len := hlen3.core_ok.arena_len_arr
  have h3_lt_cap : cref.toNat + 3 + fullArenaClauseSize s3 cref.toNat ≤ c.arena_cap := by
    have h1 := hwf.1; have h2 := hwf.2.2.1; have h3 := hwf.2.2.2.1
    exact Nat.le_trans h2 (Nat.le_trans h3 hal)
  have hbp_32 : (BitVec.ofNat 32 bp).toNat = bp := bv32_ofNat_toNat (by omega)
  unfold otfs_swap_bp_expr
  refine wp_join_group (ts := []) (fun _ m' =>
    ∃ s4 : FullState,
      (∃ ar4, s4 = { s3 with core := { s3.core with arena := ar4 } }) ∧
      s4.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur cut s4.core ∧
      FullArenaVarsNodup s4 ∧ fullArenaClauseRefs s4 = fullArenaClauseRefs s3 ∧
      fullArenaClauseGarb s4 cref.toNat = false ∧
      (fullArenaClauseLits s4 cref.toNat).Perm (fullArenaClauseLits s3 cref.toNat) ∧
      (FullMem c s4 ⋆ R) m') ?_ ?_
  · intro Js _ m' ⟨s4, hs4, hl4, hw4, hnd4, hr4, hg4, hp4, hm'⟩
    c0_hstraight
    exact hcont s4 m' hs4 hl4 hw4 hnd4 hr4 hg4 hp4 hm'
  · intro Js hJs
    c0_hstraight
    c0_hstep_np
    · have hbp_ne1 : bp ≠ 1 := by
        intro h
        have hc' : (BitVec.ofNat 32 bp).toNat ≠ (1#32 : BitVec 32).toNat := by c0_bound
        rw [hbp_32, h, show (1#32 : BitVec 32).toNat = 1 from rfl] at hc'; exact hc' rfl
      have hbp_gt : 1 < bp := by omega
      have hcr4_z : (cref.setWidth 64 + 3#64 + 1#64).toNat = cref.toNat + 4 :=
        otfs_bv_idx3_64 cref 1 (by omega) (by decide)
      have hcr4_bd : (cref.setWidth 64 + 3#64 + 1#64).toNat < s3.core.arena.length := by
        rw [hcr4_z, har_len]; omega
      obtain ⟨hz_bp, hbp_bd⟩ := s13_otfs_ar_idx3_lt_len hcap har_len h3_lt_cap hbp_lt
      have hbp_bd_set : (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 bp).setWidth 64).toNat <
          (s3.core.arena.set (cref.setWidth 64 + 3#64 + 1#64).toNat
            (s3.core.arena[(cref.setWidth 64 + 3#64 +
              (BitVec.ofNat 32 bp).setWidth 64).toNat]'hbp_bd)).length := by
        rw [List.length_set]; exact hbp_bd
      obtain ⟨hw4, hnd4, hr4, _, hg4, hp4, _⟩ :=
        s13_otfs_cut_swap1 hlen3 hw3 hnd3 hcref3 hng3 hbp_gt hbp_lt
      c0_hstraight
      let l1 := s3.core.arena[cref.toNat + 4]?.getD 0#32
      let lbp := s3.core.arena[cref.toNat + 3 + bp]?.getD 0#32
      let ar' := (s3.core.arena.set (cref.toNat + 4) lbp).set (cref.toNat + 3 + bp) l1
      have har'_eq : ((s3.core.arena.set (cref.setWidth 64 + 3#64 + 1#64).toNat
            (s3.core.arena[(cref.setWidth 64 + 3#64 +
              (BitVec.ofNat 32 bp).setWidth 64).toNat]'hbp_bd)).set
          (cref.setWidth 64 + 3#64 + (BitVec.ofNat 32 bp).setWidth 64).toNat
          (s3.core.arena[(cref.setWidth 64 + 3#64 + 1#64).toNat]'hcr4_bd)) = ar' := by
        dsimp only [ar', l1, lbp]
        rw [getElem_eq_of_idx hz_bp, getElem_eq_of_idx hcr4_z, hcr4_z, hz_bp,
          List.getElem?_eq_getElem (by rw [har_len]; omega), Option.getD_some,
          List.getElem?_eq_getElem (by rw [har_len]; omega), Option.getD_some]
      refine hJs () _ ⟨{ s3 with core := { s3.core with arena := ar' } }, ⟨ar', rfl⟩,
        ⟨{ hlen3.core_ok with arena_len_arr := by simp [ar', har_len] }, hlen3.scratch_ok⟩,
        hw4, hnd4, hr4, hg4, hp4, ?_⟩
      rw [← har'_eq]; assumption
    · c0_hstraight
      exact hJs () m ⟨s3, ⟨s3.core.arena, rfl⟩, hlen3, hw3, hnd3, rfl, hng3, List.Perm.refl _, hm⟩

/-! ## 4. Watch-Stack Loop 4 & `otfs_cnt++` (`full_otfs_large`) -/

@[expose] def otfs_loop4_expr {V : Ty → Type} {L : List Ty → Type}
    (hdr pArena cr3 : V i64) (l0 cref : V i32) : Expr V L [.bool] :=
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var cr3, Arg.imm 1, ())) fun p_44 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_44.fst, Arg.imm 4, ())) fun p_45 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pArena, Arg.var p_45.fst, ())) fun p_46 =>
  Expr.load i32 (Arg.var p_46.fst) fun ld_l1 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var hdr, Arg.imm 104, ())) fun p_47 =>
  Expr.load i64 (Arg.var p_47.fst) fun ld_6 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var hdr, Arg.imm 120, ())) fun p_48 =>
  Expr.load i64 (Arg.var p_48.fst) fun ld_7 =>
  Expr.group (sig := [[]]) (fun Js_cnt =>
    Blocks.cons (fun _ =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var hdr, Arg.imm 960, ())) fun p_50 =>
      Expr.load i64 (Arg.var p_50.fst) fun ld_cnt =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var ld_cnt, Arg.imm 1, ())) fun p_51 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var hdr, Arg.imm 960, ())) fun p_c =>
      Expr.store (Arg.var p_51.fst) (Arg.var p_c.fst) (Expr.ret (Arg.imm true, ()))) Blocks.nil)
  fun Js_cnt =>
    Expr.let_ (Op.mk (OpCode.and i32) (Arg.var cref, Arg.imm 2147483648, ())) fun p_49 =>
    Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i32) (Arg.var p_49.fst, Arg.imm 0, ())) fun p_50 =>
    Expr.jnz (Arg.var p_50.fst)
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var l0, ())) fun p_51 =>
       Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 1, ())) fun p_52 =>
       Expr.let_ (Op.mk (OpCode.shl i64) (Arg.var p_51.fst, Arg.var p_52.fst, ())) fun p_53 =>
       Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_53.fst, Arg.imm 4, ())) fun p_54 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var ld_6, Arg.var p_54.fst, ())) fun p_55 =>
       Expr.load i32 (Arg.var p_55.fst) fun ld_8 =>
       Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld_8, ())) fun p_56 =>
       Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var l0, ())) fun p_57 =>
       Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 1, ())) fun p_58 =>
       Expr.let_ (Op.mk (OpCode.shl i64) (Arg.var p_57.fst, Arg.var p_58.fst, ())) fun p_59 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_59.fst, Arg.imm 1, ())) fun p_60 =>
       Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_60.fst, Arg.imm 4, ())) fun p_61 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var ld_6, Arg.var p_61.fst, ())) fun p_62 =>
       Expr.load i32 (Arg.var p_62.fst) fun ld_9 =>
       Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld_9, ())) fun p_63 =>
       Expr.group (sig := [[]]) (fun Js_out =>
         Blocks.cons (fun _ => Expr.jump Js_cnt.fst ()) Blocks.nil)
       fun Js_out =>
         Expr.let_ (Op.mk (OpCode.cmp CmpOp.uge i64) (Arg.var p_63.fst, Arg.imm 2, ())) fun p_64 =>
         Expr.jnz (Arg.var p_64.fst)
           (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_56.fst, Arg.var p_63.fst, ())) fun p_65 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_56.fst, Arg.imm 2, ())) fun p_66 =>
            Expr.group (sig := [[i64]]) (fun Js_done =>
              Blocks.cons (fun _ => Expr.jump Js_out.fst ()) Blocks.nil)
            fun Js_done =>
              Expr.group (sig := [[i64]]) (fun Js_1 =>
                Blocks.cons (fun p_67 =>
                  Expr.let_ (Op.mk (OpCode.cmp CmpOp.uge i64)
                      (Arg.var p_67.fst, Arg.var p_66.fst, ())) fun p_68 =>
                  Expr.jnz (Arg.var p_68.fst)
                    (Expr.let_ (Op.mk (OpCode.sub i64)
                         (Arg.var p_67.fst, Arg.imm 1, ())) fun p_69 =>
                     Expr.let_ (Op.mk (OpCode.mul i64)
                         (Arg.var p_69.fst, Arg.imm 4, ())) fun p_70 =>
                     Expr.let_ (Op.mk (OpCode.add i64)
                         (Arg.var ld_7, Arg.var p_70.fst, ())) fun p_71 =>
                     Expr.load i32 (Arg.var p_71.fst) fun ld_10 =>
                     Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i32) (Arg.var ld_10, Arg.var cref, ()))
                       fun p_eq =>
                     Expr.jnz (Arg.var p_eq.fst)
                       (Expr.let_ (Op.mk (OpCode.sub i64)
                            (Arg.var p_67.fst, Arg.imm 2, ())) fun px =>
                        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var px.fst, Arg.imm 4, ())) fun py =>
                        Expr.let_ (Op.mk (OpCode.add i64)
                            (Arg.var ld_7, Arg.var py.fst, ())) fun pz =>
                        Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld_l1, Arg.imm 2147483647, ()))
                          fun p_72 =>
                        Expr.store (Arg.var p_72.fst) (Arg.var pz.fst)
                          (Expr.jump Js_done.fst (Arg.var p_67.fst, ())))
                       (Expr.let_ (Op.mk (OpCode.sub i64)
                            (Arg.var p_67.fst, Arg.imm 2, ())) fun pn =>
                        Expr.let_ (Op.mk (OpCode.lshr i32)
                            (Arg.var ld_10, Arg.imm 31, ())) fun p_72 =>
                        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_72.fst, ())) fun p_73 =>
                        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pn.fst, Arg.var p_73.fst, ()))
                          fun p_nxt =>
                        Expr.jump Js_1.fst (Arg.var p_nxt.fst, ())))
                    (Expr.jump Js_done.fst (Arg.var p_67.fst, ()))) Blocks.nil)
              fun Js_1 => Expr.jump Js_1.fst (Arg.var p_65.fst, ()))
           (Expr.jump Js_out.fst ()))
      (Expr.jump Js_cnt.fst ())

theorem s13_otfs_loop4_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {s4 : FullState} {R : Mem 64 → Prop} {m : Mem 64} {cref l0 : BitVec 32}
    (hlen4 : s4.LengthsOk c) (hw4 : FullWitnessCutInv c F0 F_cur cut s4.core)
    (hnd4 : FullArenaVarsNodup s4) (hdm4 : s4.core.dense_mode = 0#64)
    (hm : (FullMem c s4 ⋆ R) m) (hcap : c.arena_cap < 2 ^ 31 - 1)
    (hcref4 : cref.toNat ∈ fullArenaClauseRefs s4)
    (hng4 : fullArenaClauseGarb s4 cref.toNat = false)
    (hl0 : l0.toNat < 2 * s4.core.cur_vars)
    (hPost : ∀ wstk' otfs' m',
      let s4' : FullState :=
        { s4 with
          core := { s4.core with wstk := wstk' }
          scratch := { s4.scratch with otfs_cnt := otfs' } }
      s4'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s4'.core →
      FullArenaVarsNodup s4' → fullArenaClauseRefs s4' = fullArenaClauseRefs s4 →
      fullArenaClauseGarb s4' cref.toNat = false →
      fullArenaClauseLits s4' cref.toNat = fullArenaClauseLits s4 cref.toNat →
      (FullMem c s4' ⋆ R) m' → Q (true, ()) m') :
    wp Γ Q X (otfs_loop4_expr c.hdr c.pArena (cref.setWidth 64 + 3#64) l0 cref) m := by
  have har_len := hlen4.core_ok.arena_len_arr
  have hwv_len := hlen4.core_ok.wvec_len
  have hws_len := hlen4.core_ok.wstk_len_arr
  have hwl_le := hlen4.core_ok.wlen_le
  have hcv_le := hlen4.core_ok.cur_vars_le
  have hwf := hw4.arena.refs_wf cref.toNat hcref4
  have hwf1 := hwf.1; have hwf2 := hwf.2.1; have hwf3 := hwf.2.2.1; have hwf4 := hwf.2.2.2.1
  have hal := hlen4.core_ok.arena_len_le
  have hcr4_z : (cref.setWidth 64 + 3#64 + 1#64).toNat = cref.toNat + 4 :=
    otfs_bv_idx4_64 cref (by omega)
  have hcr4_bd : (cref.setWidth 64 + 3#64 + 1#64).toNat < s4.core.arena.length := by
    rw [hcr4_z, har_len]; omega
  have hwat : WatchesInv F_cur s4.core := by
    have := hw4.watches; simpa only [ModeWatchesInv, hdm4, ↓reduceIte] using this
  have hlay := hwat.layout
  unfold otfs_loop4_expr
  c0_hstraight
  refine wp_join_group (ts := [])
    (fun _ ml => ∃ wstk' : List (BitVec 32),
      wstk'.length = c.wcap ∧ ModeWatchesInv F_cur { s4.core with wstk := wstk' } ∧
      (FullMem c { s4 with core := { s4.core with wstk := wstk' } } ⋆ R) ml) ?_ ?_
  · intro Js_cnt _ ml ⟨wstk', hwl', hmw', hml⟩
    c0_hstraight
    dsimp only at *
    let s4' : FullState :=
      { s4 with core := { s4.core with wstk := wstk' }
                scratch := { s4.scratch with otfs_cnt := s4.scratch.otfs_cnt + (1 : BitVec 64) } }
    have hl4' : s4'.LengthsOk c :=
      ⟨{ hlen4.core_ok with wstk_len_arr := hwl' },
        { hlen4.scratch_ok with walk_vals_len := hlen4.scratch_ok.walk_vals_len }⟩
    have hw4' : FullWitnessCutInv c F0 F_cur cut s4'.core :=
      ⟨{ hw4.toFullOtfsWitnessInv with
          arena := { hw4.arena with len_ok := hw4.arena.len_ok }
          watches := hmw' },
        hw4.cut_le, hw4.reason_inv_cut, hw4.reason_lit_mem_cut⟩
    exact hPost wstk' (s4.scratch.otfs_cnt + (1 : BitVec 64)) _ hl4' hw4' hnd4 rfl hng4 rfl
      (by assumption)
  · intro Js_cnt hJs_cnt
    c0_hstraight
    c0_hstep_np
    · have hcr_msb : (cref &&& 0x80000000#32) = 0#32 :=
        (otfs_bv32_lt_highbit_iff cref).mp (by have := hwf.1; omega)
      have h2l_lt : (BitVec.setWidth 64 l0 <<< (1 : Nat)).toNat < s4.core.wvec.length := by
        rw [otfs_bv64_zext_shl1 l0, hwv_len]; omega
      have h2l1_lt : (BitVec.setWidth 64 l0 <<< (1 : Nat) + (1 : BitVec 64)).toNat <
          s4.core.wvec.length := by
        rw [otfs_bv64_zext_shl1_add1 l0, hwv_len]; omega
      let off0 := fullWatchOffCore s4.core l0.toNat
      let sz0 := fullWatchSizeCore s4.core l0.toNat
      have h2l_bd : 2 * l0.toNat < s4.core.wvec.length := by rw [hwv_len]; omega
      have h2l1_bd : 2 * l0.toNat + 1 < s4.core.wvec.length := by rw [hwv_len]; omega
      have hoff_eq : (s4.core.wvec[(BitVec.setWidth 64 l0 <<<
          (1 : Nat)).toNat]'h2l_lt).toNat = off0 := by
        unfold off0 fullWatchOffCore
        rw [List.getElem?_eq_getElem h2l_bd, Option.getD_some]
        exact congrArg BitVec.toNat (getElem_eq_of_idx (hj := h2l_bd) (otfs_bv64_zext_shl1 l0))
      have hsz_eq : (s4.core.wvec[(BitVec.setWidth 64 l0 <<<
          (1 : Nat) + (1 : BitVec 64)).toNat]'h2l1_lt).toNat = sz0 := by
        unfold sz0 fullWatchSizeCore
        rw [List.getElem?_eq_getElem h2l1_bd, Option.getD_some]
        exact congrArg BitVec.toNat
          (getElem_eq_of_idx (hj := h2l1_bd) (otfs_bv64_zext_shl1_add1 l0))
      have hbd_end : off0 + sz0 ≤ s4.core.wlen := hlay.bounds l0.toNat hl0
      have hwcap_lt := c.hwcap
      c0_hstraight
      refine wp_join_group (ts := [])
        (fun _ ml => ∃ wstk' : List (BitVec 32),
          wstk'.length = c.wcap ∧ ModeWatchesInv F_cur { s4.core with wstk := wstk' } ∧
          (FullMem c { s4 with core := { s4.core with wstk := wstk' } } ⋆ R) ml) ?_ ?_
      · intro Js_out _ ml h; c0_hstraight; exact hJs_cnt () ml h
      · intro Js_out hJs_out
        c0_hstraight
        c0_hstep_np
        · have hbd_mod :
              (2 * l0.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = 2 * l0.toNat + 1 := by
            rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
          have hsz2 : 2 ≤ sz0 := by
            unfold sz0 fullWatchSizeCore
            rw [List.getElem?_eq_getElem h2l1_bd, Option.getD_some,
              ← congrArg BitVec.toNat (getElem_eq_of_idx (hj := h2l1_bd) hbd_mod)]
            exact hc
          have hoff64 : (BitVec.setWidth 64 (s4.core.wvec[(BitVec.setWidth 64 l0 <<<
              (1 : Nat)).toNat]'h2l_lt)).toNat = off0 := by
            rw [zext_toNat _ (by decide), hoff_eq]
          have hsz64 : (BitVec.setWidth 64 (s4.core.wvec[(BitVec.setWidth 64 l0 <<<
              (1 : Nat) + (1 : BitVec 64)).toNat]'h2l1_lt)).toNat = sz0 := by
            rw [zext_toNat _ (by decide), hsz_eq]
          have hend64 : (BitVec.setWidth 64 (s4.core.wvec[(BitVec.setWidth 64 l0 <<<
              (1 : Nat)).toNat]'h2l_lt) + BitVec.setWidth 64
              (s4.core.wvec[(BitVec.setWidth 64 l0 <<<
                (1 : Nat) + (1 : BitVec 64)).toNat]'h2l1_lt)).toNat = off0 + sz0 := by
            rw [BitVec.toNat_add, hoff64, hsz64, Nat.mod_eq_of_lt (by omega)]
          have hoff2_64 : (BitVec.setWidth 64 (s4.core.wvec[(BitVec.setWidth 64 l0 <<<
              (1 : Nat)).toNat]'h2l_lt) + (2 : BitVec 64)).toNat = off0 + 2 := by
            rw [BitVec.toNat_add, hoff64, show (2 : BitVec 64).toNat = 2 from rfl,
              Nat.mod_eq_of_lt (by omega)]
          c0_hstraight
          refine wp_join_group (ts := [i64])
            (fun _ ml => ∃ wstk' : List (BitVec 32),
              wstk'.length = c.wcap ∧ ModeWatchesInv F_cur { s4.core with wstk := wstk' } ∧
              (FullMem c { s4 with core := { s4.core with wstk := wstk' } } ⋆ R) ml) ?_ ?_
          · rintro Js_done ⟨_, ⟨⟩⟩ ml h; c0_hstraight; exact hJs_out () ml h
          · intro Js_done hJs_done
            refine wp_loop_inv (ts := [i64])
              (fun (p_v, ()) ml => ml = m ∧ off0 ≤ p_v.toNat ∧ p_v.toNat ≤ off0 + sz0 ∧
                WatchSliceOk F_cur s4.core l0.toNat off0 (p_v.toNat - off0) ∧
                WatchSliceOk F_cur s4.core l0.toNat p_v.toNat (off0 + sz0 - p_v.toNat))
              (fun (p_v, ()) _ => p_v.toNat - off0) ?_ ?_
            · intro Js_1 hL1
              c0_hstraight
              refine hL1 _ m ⟨rfl, by rw [hend64]; omega,
                by rw [hend64]; exact Nat.le_refl _, ?_, ?_⟩
              · rw [hend64, show off0 + sz0 - off0 = sz0 by omega]
                exact hwat.slices l0.toNat hl0
              · rw [hend64, Nat.sub_self]; exact .empty
            · rintro Js_1 ⟨p_v, ⟨⟩⟩ ml ⟨hm1, hp_lo, hp_hi, hpre, hsuf⟩ hL1; subst ml
              c0_hstraight
              c0_hstep_np
              · have hp_ge2 : off0 + 2 ≤ p_v.toNat := by
                  have hc' : (BitVec.setWidth 64 (s4.core.wvec[(BitVec.setWidth 64 l0 <<<
                      (1 : Nat)).toNat]'h2l_lt) + (2 : BitVec 64)).toNat ≤ p_v.toNat := by
                    c0_bound
                  rwa [hoff2_64] at hc'
                have hp1_z := otfs_bv64_sub1_toNat (p := p_v) (by omega)
                have hp1_lt : (p_v - (1 : BitVec 64)).toNat < s4.core.wstk.length := by
                  rw [hp1_z]; omega
                clear hc
                c0_hstraight
                c0_hstep_np
                · have hw_eq : s4.core.wstk[(p_v - (1 : BitVec 64)).toNat]'hp1_lt = cref := hc
                  have hp2_z := otfs_bv64_sub2_toNat (p := p_v) (by omega)
                  have hp2_lt : (p_v - (2 : BitVec 64)).toNat < s4.core.wstk.length := by
                    rw [hp2_z]; omega
                  have hp1_bd : p_v.toNat - 1 < s4.core.wstk.length := by omega
                  have hcr_some : s4.core.wstk[p_v.toNat - 1]? = some cref := by
                    rw [List.getElem?_eq_getElem hp1_bd, ← hw_eq]
                    exact congrArg some (getElem_eq_of_idx (hj := hp1_bd) hp1_z).symm
                  rcases otfs_watchSlice_split_last hpre (by omega) with
                    ⟨w0, hw0, hfl0, _, _, _, _⟩ | ⟨_, w0, cr, hw0, hw1, hfl0, hcr_lt, hcr_r, hpre2⟩
                  · have hp_off : off0 + (p_v.toNat - off0) - 1 = p_v.toNat - 1 := by omega
                    rw [hp_off, hcr_some] at hw0
                    cases hw0; exact absurd hcr_msb hfl0
                  · have hp2_eq : (p_v - (2 : BitVec 64)).toNat = p_v.toNat - 2 := hp2_z
                    have hl1_and :
                        (s4.core.arena[(cref.setWidth 64 + 3#64 + 1#64).toNat]'hcr4_bd &&&
                          0x7FFFFFFF#32) &&& 0x80000000#32 = 0#32 := by
                      rw [BitVec.and_assoc,
                        show (0x7FFFFFFF#32 &&& 0x80000000#32 : BitVec 32) = 0#32 from rfl,
                        BitVec.and_zero]
                    have hcr_lt31 : cref.toNat < 0x80000000 := by have := hwf.1; omega
                    have hpre2' : WatchSliceOk F_cur s4.core l0.toNat
                        (fullWatchOffCore s4.core l0.toNat)
                        (p_v.toNat - 2 - fullWatchOffCore s4.core l0.toNat) := by
                      rwa [show p_v.toNat - off0 - 2 = p_v.toNat - 2 - off0 by omega] at hpre2
                    obtain ⟨hlen', hmw'⟩ := s13_otfs_loop4_hit_watches hlen4.core_ok hdm4
                      hw4.watches hl0 hp_ge2 hp_hi hpre2' hsuf hcr_some hl1_and hcr_lt31 hcref4
                    c0_hstraight
                    let wstk' := s4.core.wstk.set (p_v - (2 : BitVec 64)).toNat
                      (s4.core.arena[(cref.setWidth 64 + 3#64 + 1#64).toNat]'hcr4_bd &&&
                        0x7FFFFFFF#32)
                    refine hJs_done (p_v, ()) _ ⟨wstk',
                      (by rw [← hp2_eq] at hlen'; exact hlen'.wstk_len_arr), ?_, ?_⟩
                    · simpa only [wstk', hp2_eq] using hmw'
                    · dsimp only [wstk'] at *
                      assumption
                · have hw_ne : s4.core.wstk[(p_v - (1 : BitVec 64)).toNat]'hp1_lt ≠ cref := hc
                  let w := s4.core.wstk[(p_v - (1 : BitVec 64)).toNat]'hp1_lt
                  have hp1_bd : p_v.toNat - 1 < s4.core.wstk.length := by omega
                  have hw_some : s4.core.wstk[p_v.toNat - 1]? = some w := by
                    rw [List.getElem?_eq_getElem hp1_bd]
                    exact congrArg some (getElem_eq_of_idx (hj := hp1_bd) hp1_z).symm
                  have hp2_z := otfs_bv64_sub2_toNat (p := p_v) (by omega)
                  rcases otfs_watchSlice_split_last hpre (by omega) with
                    ⟨w0, hw0, hfl0, hne, hlt, hent, hpre1⟩ |
                    ⟨_, w0, cr, hw0, hw1, hfl0, hcr_lt, hcr_r, hpre2⟩
                  · rw [show off0 + (p_v.toNat - off0) - 1 = p_v.toNat - 1 by omega, hw_some] at hw0
                    cases hw0
                    have hlshr : (w >>> (31 : Nat)).toNat = 1 := by
                      change (w >>> (31#32 : BitVec 32)).toNat = 1
                      exact (otfs_bv32_lshr31_nat_cases w).2.1 hfl0
                    let p_nxt : BitVec 64 :=
                      (p_v - (2 : BitVec 64)) + BitVec.setWidth 64 (w >>> (31 : Nat))
                    have hn_z : p_nxt.toNat = p_v.toNat - 1 := by
                      dsimp only [p_nxt]
                      rw [BitVec.toNat_add, hp2_z, zext_toNat _ (by decide), hlshr,
                        Nat.mod_eq_of_lt (by omega)]; omega
                    c0_hstraight
                    change Js_1 (p_nxt, ()) m
                    refine hL1 (p_nxt, ()) m (by dsimp only; rw [hn_z]; omega)
                      ⟨rfl, by rw [hn_z]; omega, by rw [hn_z]; omega, ?_, ?_⟩
                    · rw [hn_z]
                      rwa [show p_v.toNat - off0 - 1 = p_v.toNat - 1 - off0 by omega] at hpre1
                    · rw [hn_z,
                        show off0 + sz0 - (p_v.toNat - 1) = off0 + sz0 - p_v.toNat + 1 by omega]
                      exact .bin hw_some hfl0 hne hlt hent (by
                        simpa only [show p_v.toNat - 1 + 1 = p_v.toNat by omega] using hsuf)
                  · rw [show off0 + (p_v.toNat - off0) - 1 = p_v.toNat - 1 by omega, hw_some] at hw1
                    cases hw1
                    have hlshr : (w >>> (31 : Nat)).toNat = 0 := by
                      change (w >>> (31#32 : BitVec 32)).toNat = 0
                      exact (otfs_bv32_lshr31_nat_cases w).1
                        ((otfs_bv32_lt_highbit_iff w).mp hcr_lt)
                    let p_nxt : BitVec 64 :=
                      (p_v - (2 : BitVec 64)) + BitVec.setWidth 64 (w >>> (31 : Nat))
                    have hn_z : p_nxt.toNat = p_v.toNat - 2 := by
                      dsimp only [p_nxt]
                      rw [BitVec.toNat_add, hp2_z, zext_toNat _ (by decide), hlshr,
                        Nat.mod_eq_of_lt (by omega)]; omega
                    c0_hstraight
                    change Js_1 (p_nxt, ()) m
                    refine hL1 (p_nxt, ()) m (by dsimp only; rw [hn_z]; omega)
                      ⟨rfl, by rw [hn_z]; omega, by rw [hn_z]; omega, ?_, ?_⟩
                    · rw [hn_z]
                      rwa [show p_v.toNat - off0 - 2 = p_v.toNat - 2 - off0 by omega] at hpre2
                    · rw [hn_z,
                        show off0 + sz0 - (p_v.toNat - 2) = off0 + sz0 - p_v.toNat + 2 by omega]
                      exact .large (by
                          rwa [show off0 + (p_v.toNat - off0) - 2 = p_v.toNat - 2 by omega] at hw0)
                        (by rwa [show p_v.toNat - 2 + 1 = p_v.toNat - 1 by omega])
                        hfl0 hcr_lt hcr_r (by
                          simpa only [show p_v.toNat - 2 + 2 = p_v.toNat by omega] using hsuf)
              · c0_hstraight; exact hJs_done (p_v, ()) m ⟨s4.core.wstk, hws_len, hw4.watches, hm⟩
        · c0_hstraight; exact hJs_out () m ⟨s4.core.wstk, hws_len, hw4.watches, hm⟩
    · c0_hstraight; exact hJs_cnt () m ⟨s4.core.wstk, hws_len, hw4.watches, hm⟩

theorem s13_otfs_cut_nd_of_watch_eq {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {s s1 : FullState}
    {wv ws : List (BitVec 32)} {wl : Nat} {wu oom' : BitVec 64}
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hnd : FullArenaVarsNodup s)
    (hs1_c : s1.core =
      { s.core with wvec := wv, wstk := ws, wlen := wl, wusable := wu, oom := oom' })
    (hmw1 : ModeWatchesInv F_cur s1.core) :
    FullWitnessCutInv c F0 F_cur cut s1.core ∧ FullArenaVarsNodup s1 := by
  have hmw_exp : ModeWatchesInv F_cur
      { s.core with wvec := wv, wstk := ws, wlen := wl, wusable := wu, oom := oom' } := by
    rw [← hs1_c]; exact hmw1
  have hcut := s13_otfs_cut_with_watch_oom hw (wv := wv) (ws := ws) (wl := wl) (wu := wu)
    (oom := oom') hmw_exp
  have hw1 : FullWitnessCutInv c F0 F_cur cut s1.core := by rw [hs1_c]; exact hcut
  have hnd1 : FullArenaVarsNodup s1 := fun r hr hngr => by
    change r ∈ fullArenaClauseRefsCore s1.core at hr
    have hr' : r ∈ fullArenaClauseRefsCore s.core := by
      unfold fullArenaClauseRefsCore at hr ⊢; rw [hs1_c] at hr; exact hr
    change ((fullArenaClauseLitsCore s1.core r).map (· / 2)).Nodup
    have hngr' : fullArenaClauseGarb s r = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hngr ⊢
      rw [hs1_c] at hngr; exact hngr
    have hl := hnd r hr' hngr'
    unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [hs1_c]; exact hl
  exact ⟨hw1, hnd1⟩

private theorem s13_otfs_oom_ret_false {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s s1o : FullState}
    {wv1 ws1 : List (BitVec 32)} {wl1 : Nat} {wu1 : BitVec 64}
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hnd : FullArenaVarsNodup s)
    (hiu_cut : idx_u < cut) (hs1o_len : s1o.LengthsOk c)
    (hs1o_c : s1o.core =
      { s.core with wvec := wv1, wstk := ws1, wlen := wl1, wusable := wu1, oom := 1#64 })
    (hmw1o : ModeWatchesInv F_cur s1o.core) :
    s1o.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur idx_u s1o.core ∧ FullArenaVarsNodup s1o := by
  obtain ⟨hw1, hnd1o⟩ := s13_otfs_cut_nd_of_watch_eq hw hnd hs1o_c hmw1o
  exact ⟨hs1o_len, s13_otfs_cut_shrink hw1 (Nat.le_of_lt hiu_cut), hnd1o⟩

theorem s13_otfs_loop2_tail_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut idx_u : Nat}
    {s s2 : FullState} {R : Mem 64 → Prop} {m2 : Mem 64}
    {cref l0 uip : BitVec 32} {old_sz : Nat}
    {wv2 ws2 : List (BitVec 32)} {wl1 : Nat} {wu2 : BitVec 64} {wso1 : List (BitVec 32)}
    (hlen : s.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (hnd : FullArenaVarsNodup s)
    (hs2_len : s2.LengthsOk c) (hw2 : FullWitnessCutInv c F0 F_cur cut s2.core)
    (hnd2 : FullArenaVarsNodup s2) (hm2 : (FullMem c s2 ⋆ R) m2)
    (hs2_c : s2.core =
      { s.core with
        wvec := wv2, wstk := ws2, wlen := wl1, wusable := wu2,
        arena := (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip })
    (hs2_sc : s2.scratch = { s.scratch with wsort := wso1 })
    (hcap : c.arena_cap < 2 ^ 31 - 1)
    (h3o : cref.toNat + 3 + old_sz ≤ c.arena_cap) (h4_old : 4 ≤ old_sz)
    (hact_ge : 3 ≤ 1 + otfsActCnt s.core cref.toNat old_sz)
    (hcref : cref.toNat ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref.toNat = false) (hdm : s.core.dense_mode = 0#64)
    (huip_lt : uip.toNat < 2 * s.core.cur_vars)
    (hiu_cut : idx_u < cut) (hiu_te : idx_u < s.core.trail_end)
    (ht_u : (s.core.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hr_u : s.core.rsns[uip.toNat / 2]?.getD 4294967295#32 = cref)
    (hlu_eq : (s.core.lvl[uip.toNat / 2]?.getD 0#32).toNat = s.core.cur_level)
    (hent_orig : (cnfOfClauses F_cur).EntailsClause (cnfClause (List.filter
      (fun l => decide (l ≠ uip.toNat ∧ (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∨
        l = (s.core.arena[cref.toNat + 3]?.getD 0#32).toNat ∨
        l = (s.core.arena[cref.toNat + 4]?.getD 0#32).toNat)))
      (fullArenaClauseLits s cref.toNat))))
    (hs01 : (l0 = s.core.arena[cref.toNat + 3]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 4]?.getD 0#32 = uip) ∨
      (l0 = s.core.arena[cref.toNat + 4]?.getD 0#32 ∧
        s.core.arena[cref.toNat + 3]?.getD 0#32 = uip))
    (hl0_bd : l0.toNat < 2 * s.core.cur_vars)
    (hlits_all : ∀ j < old_sz,
      (s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
      s.core.arena[cref.toNat + 3 + j]?.getD 0#32 ≠ 4294967295#32)
    (hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s)
    (hng2 : fullArenaClauseGarb s2 cref.toNat = false)
    (hsz2 : fullArenaClauseSize s2 cref.toNat = old_sz)
    (hTailPost : ∀ (fl3 ar4 wstk' : List (BitVec 32)) (otfs' : BitVec 64) (m5 : Mem 64),
      let s5 : FullState :=
        { core :=
            { s.core with
              flags := fl3, arena := ar4, wvec := wv2, wstk := wstk',
              wlen := wl1, wusable := wu2, oom := s.core.oom }
          scratch := { s.scratch with wsort := wso1, otfs_cnt := otfs' } }
      s5.LengthsOk c → FullWitnessCutInv c F0 F_cur idx_u s5.core →
      FullArenaVarsNodup s5 → fullArenaClauseRefs s5 = fullArenaClauseRefs s →
      cref.toNat ∈ fullArenaClauseRefs s5 →
      fullArenaClauseGarb s5 cref.toNat = false →
      (∀ l ∈ fullArenaClauseLits s5 cref.toNat,
        l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat ∧
        s5.core.vals[l]?.getD 0#8 = 255#8 ∧
        ((s5.core.lvl[l / 2]?.getD 0#32).toNat = s5.core.cur_level →
          ∃ mk, mk < idx_u ∧ (s5.core.trl[mk]?.getD 0#32).toNat = l ^^^ 1)) →
      (FullMem c s5 ⋆ R) m5 → Q (true, ()) m5) :
    wp Γ Q X (otfs_loop2_expr c.pArena c.pLevel (cref.setWidth 64 + 3#64)
      (BitVec.ofNat 32 old_sz) (fun nsz bp =>
        otfs_hdr_shrink_expr c.hdr c.pArena (cref.setWidth 64 + 3#64) cref
          (BitVec.ofNat 32 old_sz) nsz uip
          (otfs_swap_bp_expr c.pArena (cref.setWidth 64 + 3#64) bp
            (otfs_loop4_expr c.hdr c.pArena (cref.setWidth 64 + 3#64) l0 cref)))) m2 := by
  have har_len := hlen.core_ok.arena_len_arr
  let ar1 := (s.core.arena.set (cref.toNat + 3) l0).set (cref.toNat + 4) uip
  have har2_eq : s2.core.arena = ar1 := by rw [hs2_c]
  have hlvl2_eq : s2.core.lvl = s.core.lvl := by rw [hs2_c]
  have hcv2_eq : s2.core.cur_vars = s.core.cur_vars := by rw [hs2_c]
  let cont_l2 : Val i32 → Val i32 → Expr Val Cont [.bool] := fun nsz bp =>
    otfs_hdr_shrink_expr c.hdr c.pArena (cref.setWidth 64 + 3#64) cref
      (BitVec.ofNat 32 old_sz) nsz uip
      (otfs_swap_bp_expr c.pArena (cref.setWidth 64 + 3#64) bp
        (otfs_loop4_expr c.hdr c.pArena (cref.setWidth 64 + 3#64) l0 cref))
  refine s13_otfs_loop2_wp hlen hs2_len hm2 hlvl2_eq hcv2_eq hcap h3o h4_old hs01 har2_eq
    (fun j hj => (hlits_all j hj).1) cont_l2 ?_
  intro nsz bp ar_cur origMap m3 hinv hnsz_lt hbp1 hbp2 hm3
  obtain ⟨har_c, _, _, _, _, hnsz_act, hlm, hpw, hlt_m, h01, hcov, hmapeq, hout_cur⟩ := hinv
  have h3_nsz : 3 ≤ nsz := by omega
  obtain ⟨hbp_ge1, hbp_lt⟩ := hbp2 (by omega)
  have hhdr_cur : ar_cur[cref.toNat]? = some (fullArenaHdrCore s2.core cref.toNat) := by
    rw [hout_cur _ (Or.inl (by omega))]
    unfold fullArenaHdrCore; rw [har2_eq]
    dsimp only [ar1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    rw [List.getElem?_eq_getElem (by rw [har_len]; omega), Option.getD_some]
  have har1_2' : ∀ q, 2 ≤ q →
      ar1[cref.toNat + 3 + q]? = s.core.arena[cref.toNat + 3 + q]? := fun q hq => by
    dsimp only [ar1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have har1_s2' : ∀ i, i < cref.toNat + 3 ∨ cref.toNat + 5 ≤ i → ar1[i]? = s2.core.arena[i]? :=
    fun i _ => by rw [har2_eq]
  refine s13_otfs_hdr_wp (_l0 := l0) hs2_len hm3 har_len har_c hcap h3o h4_old h3_nsz hnsz_lt
    (by rw [hcv2_eq]; exact huip_lt) hlits_all hcv2_eq hmapeq
    (fun k hk => by
      rw [List.getElem?_eq_getElem (by rw [hlm]; exact hk), Option.getD_some]
      exact hlt_m _ (List.getElem_mem _))
    hout_cur har1_2' har1_s2' hhdr_cur _ ?_
  intro ml3 hpost_hdr
  have hsz_old : fullArenaClauseSize s cref.toNat = old_sz := by
    rw [← hsz2]; change fullArenaClauseSizeCore s.core cref.toNat =
      fullArenaClauseSizeCore s2.core cref.toNat
    unfold fullArenaClauseSizeCore; rw [hs2_c]; dsimp only
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  obtain ⟨s3, _, _, ⟨ar3, fl3, hs3_eq⟩, hm3', hlen3, hw3, hnd3, hrefs3, _, hsz3, hng3, _,
    hsub3⟩ :=
    s13_otfs_shrink_ok_of_hdrPost hlen hw hnd hs2_len hw2 hnd2 hcv2_eq
      (by rw [hs2_c]) (by rw [hs2_c]) hlvl2_eq (by rw [hs2_c]) (by rw [hs2_c])
      hcref hng (hrefs2 ▸ hcref) hng2 rfl (hsz2.trans hsz_old.symm) hiu_cut hiu_te ht_u hr_u
      hlu_eq hent_orig (hsz_old ▸ h3o) h3_nsz (hsz_old ▸ hnsz_lt) hlm hpw
      (fun p hp => hsz_old ▸ hlt_m p hp) h01 (hsz_old ▸ hcov) (hsz_old ▸ hpost_hdr)
  have hcref3 : cref.toNat ∈ fullArenaClauseRefs s3 := by
    change cref.toNat ∈ fullArenaClauseRefsCore s3.core; rw [hrefs3]
    change cref.toNat ∈ fullArenaClauseRefs s2; rw [hrefs2]; exact hcref
  refine s13_otfs_swap_wp hlen3 hw3 hnd3 hm3' hcap hcref3 hng3 hbp_ge1
    (by change bp < fullArenaClauseSizeCore s3.core cref.toNat; rw [hsz3]; exact hbp_lt) _ ?_
  intro s4 m4 ⟨ar4, hs4_eq⟩ hlen4 hw4 hnd4 hrefs4 hng4 hperm4 hm4
  have hl0_4 : l0.toNat < 2 * s4.core.cur_vars := by rw [hs4_eq, hs3_eq, hs2_c]; exact hl0_bd
  have hdm4 : s4.core.dense_mode = 0#64 := by rw [hs4_eq, hs3_eq, hs2_c]; exact hdm
  have hcref4 : cref.toNat ∈ fullArenaClauseRefs s4 := by rw [hrefs4]; exact hcref3
  refine s13_otfs_loop4_wp hlen4 hw4 hnd4 hdm4 hm4 hcap hcref4 hng4 hl0_4 ?_
  intro wstk' otfs' m5 s5 hlen5 hw5 hnd5 hrefs5 hng5 hlits5 hm5
  have hs5_c : s5.core = { s.core with
      flags := fl3, arena := ar4, wvec := wv2, wstk := wstk',
      wlen := wl1, wusable := wu2, oom := s.core.oom } := by
    dsimp only [s5]; rw [hs4_eq, hs3_eq, hs2_c]
  have hs5_sc : s5.scratch = { s.scratch with wsort := wso1, otfs_cnt := otfs' } := by
    dsimp only [s5]; rw [hs4_eq, hs3_eq, hs2_sc]
  have hs5_eq : s5 =
      { core := { s.core with
          flags := fl3, arena := ar4, wvec := wv2, wstk := wstk',
          wlen := wl1, wusable := wu2, oom := s.core.oom },
        scratch := { s.scratch with wsort := wso1, otfs_cnt := otfs' } } :=
    congr (congrArg FullState.mk hs5_c) hs5_sc
  have hrefs5_s : fullArenaClauseRefs s5 = fullArenaClauseRefs s := by
    rw [hrefs5, hrefs4]; exact hrefs3.trans hrefs2
  have hsub5 : ∀ l ∈ fullArenaClauseLits s5 cref.toNat,
      l ≠ uip.toNat ∧ l ∈ fullArenaClauseLits s cref.toNat := fun l hl => by
    rw [hlits5] at hl; exact hsub3 l (hperm4.subset hl)
  have hfin := s13_otfs_large_fin hlen hw hcref hng hiu_cut hiu_te ht_u hr_u
    (by rw [hs5_c]) (by rw [hs5_c]) (by rw [hs5_c]) (by rw [hs5_c]) hsub5
  exact hTailPost fl3 ar4 wstk' otfs' m5
    (hs5_eq ▸ hlen5) (hs5_c ▸ hw5) (hs5_eq ▸ hnd5) (hs5_eq ▸ hrefs5_s)
    (hs5_eq ▸ (hrefs5_s ▸ hcref)) (hs5_eq ▸ hng5) (hs5_eq ▸ hfin) (hs5_eq ▸ hm5)

theorem s13_otfs_oom_core {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut idx_u : Nat} {s s_i : FullState} {R : Mem 64 → Prop} {ml_o : Mem 64}
    {wv_i ws_i : List (BitVec 32)} {wl_i : Nat} {wu_i : BitVec 64}
    (hw : FullWitnessCutInv c F0 F_cur cut s.core) (hnd : FullArenaVarsNodup s)
    (hiu_cut : idx_u < cut) (hsi_len : s_i.LengthsOk c)
    (hsi_c : s_i.core =
      { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i, wusable := wu_i })
    (hmw_i : ModeWatchesInv F_cur s_i.core)
    (hm_o : (FullMem c { s_i with core := { s_i.core with oom := 1#64 } } ⋆ R) ml_o) :
    let s_f : FullState :=
      { core :=
          { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i, wusable := wu_i, oom := 1#64 },
        scratch := s_i.scratch }
    s_f.LengthsOk c ∧ FullWitnessCutInv c F0 F_cur idx_u s_f.core ∧
    FullArenaVarsNodup s_f ∧ (FullMem c s_f ⋆ R) ml_o := by
  let s_o : FullState := { s_i with core := { s_i.core with oom := 1#64 } }
  have hso_c : s_o.core =
      { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i, wusable := wu_i, oom := 1#64 } := by
    dsimp only [s_o]; rw [hsi_c]
  have hso_eq : s_o =
      { core :=
          { s.core with wvec := wv_i, wstk := ws_i, wlen := wl_i, wusable := wu_i, oom := 1#64 },
        scratch := s_i.scratch } :=
    congrArg (fun k => ({ core := k, scratch := s_i.scratch } : FullState)) hso_c
  have hso_len : s_o.LengthsOk c := ⟨{ hsi_len.core_ok with }, hsi_len.scratch_ok⟩
  obtain ⟨h1, h2, h3⟩ := s13_otfs_oom_ret_false hw hnd hiu_cut hso_len hso_c
    (hmw_i.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr))
  exact ⟨hso_eq ▸ h1, hso_eq ▸ h2, hso_eq ▸ h3, hso_eq ▸ hm_o⟩

end LeanQbe.T.Examples.Kissat.Proof.Deduce
