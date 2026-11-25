/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofKitten2a

/-!
# Kissat Fidelity Cached-Pointer `full_k6_propagate_fid` Proof (`FullFidelityVivK6Proof1a`)

UNSAT-only `Func.wp` proof (`public section`, `0 @[expose]`, `0 import all`, `std3`) for
`G1-P2.1c`: `full_k6_propagate_fid` (caching all 11 Kitten sub-array pointers plus `prop`/`te`/
`klvl`/`unass`, with inlined `assign` and saturating `ticks` flush) against exact
`FullM6Sweep.k6PropagateSpec`.
-/

set_option autoImplicit false

local elab "fid_steps_np" : tactic => LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "fid_nogrp_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityVivK6

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Sweep LeanQbe.T.Examples.Kissat.FullM6Sweep
open K6MemATactics K6PtrTactics
open scoped K6MemATactics K6PtrTactics

section K6PropagateFid

/-! ## 1. Cached Sub-Array Pointer Normalization & 2-Step Arena Access -/

private theorem k6_ptr_step_sh (L : K6Layout) (kp : BitVec 64) (a b sh : Nat)
    (hsh : 2 ^ sh = b) (hab : a + b ≤ 38) :
    (kp + BitVec.ofNat 64 (4 * (32 + a * L.maxV))) +
        (L.mv32 <<< sh).setWidth 64 * 4 =
      kp + BitVec.ofNat 64 (4 * (32 + (a + b) * L.maxV)) := by
  have hm := L.hmaxV
  have h1 : b * L.maxV ≤ 38 * 8192 := Nat.mul_le_mul (by omega) hm.2
  have h2 : (a + b) * L.maxV ≤ 38 * 8192 := Nat.mul_le_mul hab hm.2
  have ha : a * L.maxV ≤ 38 * 8192 := Nat.mul_le_mul (by omega) hm.2
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  have h4 : (4 : BitVec 64).toNat = 4 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, K6Layout.mv32, Nat.shiftLeft_eq, hsh, h4]
  rw [Nat.mod_eq_of_lt (by omega : L.maxV < 2 ^ 32),
    Nat.mul_comm L.maxV b,
    Nat.mod_eq_of_lt (by omega : b * L.maxV < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : b * L.maxV < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : b * L.maxV * 4 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4 * (32 + a * L.maxV) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4 * (32 + a * L.maxV) + b * L.maxV * 4 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4 * (32 + (a + b) * L.maxV) < 2 ^ 64)]
  rw [Nat.add_mul]; omega

private theorem k6_ptr_step1 (L : K6Layout) (kp : BitVec 64) (a : Nat) (ha : a + 1 ≤ 38) :
    (kp + BitVec.ofNat 64 (4 * (32 + a * L.maxV))) + L.mv32.setWidth 64 * 4 =
      kp + BitVec.ofNat 64 (4 * (32 + (a + 1) * L.maxV)) := by
  simpa using k6_ptr_step_sh L kp a 1 0 rfl ha

private theorem k6_ptr_step_bv (L : K6Layout) (kp : BitVec 64) (a b : Nat) (sh : BitVec 32)
    (hsh : 2 ^ sh.toNat = b) (hab : a + b ≤ 38) :
    (kp + BitVec.ofNat 64 (4 * (32 + a * L.maxV))) +
        (L.mv32 <<< sh).setWidth 64 * 4 =
      kp + BitVec.ofNat 64 (4 * (32 + (a + b) * L.maxV)) := by
  simpa [BitVec.shiftLeft_eq'] using k6_ptr_step_sh L kp a b sh.toNat hsh hab

private theorem k6_arena_off2_addr (L : K6Layout) (kp : BitVec 64) (off j : BitVec 32)
    (hwrap : off.toNat + j.toNat < 2 ^ 32) :
    ((kp + BitVec.ofNat 64 (4 * L.oArena)) + off.setWidth 64 * 4) + j.setWidth 64 * 4 =
      (kp + BitVec.ofNat 64 (4 * L.oArena)) + (off + j).setWidth 64 * 4 := by
  have hadd : (off + j).setWidth 64 = off.setWidth 64 + j.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    have hoj : (off + j).toNat = off.toNat + j.toNat := by bv_omega
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, hoj]
    rw [Nat.mod_eq_of_lt (by omega : off.toNat + j.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (Nat.lt_trans off.isLt (by decide : 2 ^ 32 < 2 ^ 64)),
      Nat.mod_eq_of_lt (Nat.lt_trans j.isLt (by decide : 2 ^ 32 < 2 ^ 64)),
      Nat.mod_eq_of_lt (by omega : off.toNat + j.toNat < 2 ^ 64)]
  rw [hadd, BitVec.add_mul, BitVec.add_assoc, BitVec.add_assoc]

namespace K6CachedArTactics

@[scoped c0_load] theorem load_k6_arena_off2 {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
    {R : Mem 64 → Prop} {m : Mem 64} {off j : BitVec 32}
    (h : off.toNat + j.toNat < szAr L) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 (((kPtr + BitVec.ofNat 64 (4 * L.oArena)) + off.setWidth 64 * 4) +
        j.setWidth 64 * 4) =
      some (ks.arena[off.toNat + j.toNat]?.getD 0#32) := by
  have hac := L.hacap; unfold szAr at h; unfold dimacsBound at hac
  have hwrap : off.toNat + j.toNat < 2 ^ 32 := by omega
  rw [k6_arena_off2_addr L kPtr off j hwrap]
  exact load_k6_arena_off hwrap h hm

@[scoped c0_store] theorem store_k6_arena_off2 {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {off j : BitVec 32}
    (h : off.toNat + j.toNat < szAr L) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 (((kPtr + BitVec.ofNat 64 (4 * L.oArena)) + off.setWidth 64 * 4) +
        j.setWidth 64 * 4) ∧
      (K6MemA L kPtr (ks.putArr .arena (off.toNat + j.toNat) v) ⋆ R)
        (storeMem m i32 (((kPtr + BitVec.ofNat 64 (4 * L.oArena)) + off.setWidth 64 * 4) +
          j.setWidth 64 * 4) v) := by
  have hac := L.hacap; unfold szAr at h; unfold dimacsBound at hac
  have hwrap : off.toNat + j.toNat < 2 ^ 32 := by omega
  rw [k6_arena_off2_addr L kPtr off j hwrap]
  exact store_k6_arena_off v hwrap h hm

end K6CachedArTactics

open scoped K6CachedArTactics

/-! ## 2. Shadow-Header State & `K6PropFrame` Helpers -/

/-- Memory state while `prop`, `trl_end`, and `unass` are held in local registers. -/
private def k6ShadowHdr (ks0 st : K6State) : K6State :=
  { st with prop := ks0.prop, trl_end := ks0.trl_end, unass := ks0.unass }

private theorem k6ShadowHdr_self (ks : K6State) : k6ShadowHdr ks ks = ks := by
  dsimp only [k6ShadowHdr]

private theorem k6ShadowHdr_putArr (ks0 st : K6State) (f : K6ArrField) (i : Nat) (v : BitVec 32) :
    (k6ShadowHdr ks0 st).putArr f i v = k6ShadowHdr ks0 (st.putArr f i v) := by
  dsimp only [k6ShadowHdr]; cases f <;> k6_ext

private theorem k6ShadowHdr_bumpProp (ks0 st : K6State) (p : BitVec 32) :
    k6ShadowHdr ks0 (st.putHdr .prop p) = k6ShadowHdr ks0 st := by
  dsimp only [k6ShadowHdr]; k6_ext

private theorem k6ShadowHdr_prep (ks0 st : K6State) :
    (((k6ShadowHdr ks0 st).putHdr .prop st.prop).putHdr .trl_end st.trl_end).putHdr
      .unass st.unass = st := by
  dsimp only [k6ShadowHdr]; k6_ext

private theorem k6ShadowHdr_flush (ks0 st : K6State) (tk' : BitVec 32) :
    ((((k6ShadowHdr ks0 st).putHdr .prop st.prop).putHdr .trl_end st.trl_end).putHdr
      .unass st.unass).putHdr .ticks tk' = st.putHdr .ticks tk' := by
  dsimp only [k6ShadowHdr]; k6_ext

private theorem fid_k6ShadowHdr_assign (ks0 st : K6State) (lit rsn fl' : BitVec 32)
    (hlvl : ks0.lvl = st.lvl)
    (hfl : fl' = if (lit &&& 1#32) ≠ 0#32 then (st.flags[(lit >>> 1).toNat]?.getD 0#32) ||| 1#32
      else (st.flags[(lit >>> 1).toNat]?.getD 0#32) &&& ~~~1#32) :
    (((((((k6ShadowHdr ks0 st).putArr .vals lit.toNat 1#32).putArr .vals (lit ^^^ 1#32).toNat
        2#32).putArr .lvlArr (lit >>> 1).toNat ks0.lvl).putArr .rsn (lit >>> 1).toNat rsn).putArr
      .trl st.trl_end.toNat lit).putArr .flags (lit >>> 1).toNat fl') =
      k6ShadowHdr ks0 (k6AssignStep st lit rsn) := by
  dsimp only [k6ShadowHdr]
  k6_ext <;> (try simp only [k6AssignStep, hlvl, hfl])

private theorem fid_k6Assign_unass_pos {st : K6State} {lit rsn : BitVec 32} {u0 : BitVec 32}
    (hu : u0 = st.unass) (h : 0#32 < u0) :
    u0 - 1#32 = (k6AssignStep st lit rsn).unass := by
  subst hu; dsimp only [k6AssignStep]; split <;> bv_omega

private theorem fid_k6Assign_unass_zero {st : K6State} {lit rsn : BitVec 32} {u0 : BitVec 32}
    (hu : u0 = st.unass) (h : ¬ 0#32 < u0) :
    u0 = (k6AssignStep st lit rsn).unass := by
  subst hu; dsimp only [k6AssignStep]; split <;> bv_omega

private theorem fid_k6Assign_mem_pos {L : K6Layout} {kp : BitVec 64} {P : Mem 64 → Prop}
    {ks st st_fl : K6State} {lit rsn : BitVec 32} {trlEnd : Nat} {m : Mem 64}
    (hm : (K6MemA L kp (((((((k6ShadowHdr ks st).putArr .vals lit.toNat 1#32).putArr
      .vals (lit ^^^ 1#32).toNat 2#32).putArr .lvlArr (lit >>> 1).toNat ks.lvl).putArr
      .rsn (lit >>> 1).toNat rsn).putArr .trl trlEnd lit).putArr
      .flags (lit >>> 1).toNat (st_fl.flags[(lit >>> 1).toNat]?.getD 0#32 ||| 1#32)) ⋆ P) m)
    (hlvl : ks.lvl = st.lvl) (htrl : trlEnd = st.trl_end.toNat)
    (hfl_arr : st_fl.flags = st.flags) (hbit : (lit &&& 1#32) ≠ 0#32) :
    (K6MemA L kp (k6ShadowHdr ks (k6AssignStep st lit rsn)) ⋆ P) m := by
  subst htrl
  refine Eq.mp (congrArg (fun x => (K6MemA L kp x ⋆ P) m) ?_) hm
  exact fid_k6ShadowHdr_assign ks st lit rsn _ hlvl
    (by simp only [hfl_arr, hbit, ne_eq, not_false_eq_true, ↓reduceIte])

private theorem fid_bv32_shr1 (x : BitVec 32) :
    (x >>> (1#32 : BitVec 32)) = x >>> (1 : Nat) := rfl

private theorem fid_r_add1 {sz off alen acap : Nat} {rb : BitVec 32}
    (hr : rb.toNat < sz) (h1 : off + sz ≤ alen) (h2 : alen ≤ acap) (h3 : acap < dimacsBound) :
    (rb + 1#32).toNat = rb.toNat + 1 := by
  unfold dimacsBound at h3
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]

private theorem fid_k6Assign_mem_eq0 {L : K6Layout} {kp : BitVec 64} {P : Mem 64 → Prop}
    {ks st st_fl : K6State} {lit rsn : BitVec 32} {trlEnd : Nat} {m : Mem 64}
    (hm : (K6MemA L kp (((((((k6ShadowHdr ks st).putArr .vals lit.toNat 1#32).putArr
      .vals (lit ^^^ 1#32).toNat 2#32).putArr .lvlArr (lit >>> 1).toNat ks.lvl).putArr
      .rsn (lit >>> 1).toNat rsn).putArr .trl trlEnd lit).putArr
      .flags (lit >>> 1).toNat (st_fl.flags[(lit >>> 1).toNat]?.getD 0#32 &&& ~~~1#32)) ⋆ P) m)
    (hlvl : ks.lvl = st.lvl) (htrl : trlEnd = st.trl_end.toNat)
    (hfl_arr : st_fl.flags = st.flags) (hbit : (lit &&& 1#32) = 0#32) :
    (K6MemA L kp (k6ShadowHdr ks (k6AssignStep st lit rsn)) ⋆ P) m := by
  subst htrl
  refine Eq.mp (congrArg (fun x => (K6MemA L kp x ⋆ P) m) ?_) hm
  exact fid_k6ShadowHdr_assign ks st lit rsn _ hlvl
    (by rw [hfl_arr]; simp only [hbit, ne_eq, not_true_eq_false, ↓reduceIte])

private theorem fid_bv32_add1 {x : BitVec 32} (hx : x.toNat < 2 ^ 30) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]

private structure K6PropFrame (L : K6Layout) (c : (Nat → Bool) → Prop) (ks0 ks : K6State) : Prop where
  hinv : K6Inv L c ks
  hsync : K6TrailSynced ks
  hpres : K6PropPreserved ks0 ks
  htrl_ge : ks0.trl_end.toNat ≤ ks.trl_end.toNat
  hold : ∀ i < ks0.trl_end.toNat,
    ks.trl[i]? = ks0.trl[i]? ∧
    ks.lvlArr[(ks0.trl[i]?.getD 0#32).toNat / 2]? =
      ks0.lvlArr[(ks0.trl[i]?.getD 0#32).toNat / 2]? ∧
    ks.rsn[(ks0.trl[i]?.getD 0#32).toNat / 2]? = ks0.rsn[(ks0.trl[i]?.getD 0#32).toNat / 2]?
  hnew : ∀ i, ks0.trl_end.toNat ≤ i → i < ks.trl_end.toNat →
    ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks0.lvl ∧
    ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ 0xFFFFFFFF#32

private theorem fid_k6PropFrame_refl {L : K6Layout} {c : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L c ks) (hsync : K6TrailSynced ks) : K6PropFrame L c ks ks :=
  ⟨hinv, hsync,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    Nat.le_refl _, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ h1 h2 => absurd h1 (Nat.not_le_of_gt h2)⟩

private theorem fid_k6WatchesOk_putHdr {ks : K6State} (hw : K6WatchesOk ks) (f : K6HdrField)
    (hf : f = .prop ∨ f = .ticks) (v : BitVec 32) : K6WatchesOk (ks.putHdr f v) := by
  rcases hf with rfl | rfl <;> exact hw

private theorem fid_k6ReasonOk_putHdr {ks : K6State} (hr : K6ReasonOk ks) (f : K6HdrField)
    (hf : f = .prop ∨ f = .ticks) (v : BitVec 32) : K6ReasonOk (ks.putHdr f v) := by
  rcases hf with rfl | rfl <;> exact hr

private theorem fid_k6TrailSynced_putHdr {ks : K6State} (hs : K6TrailSynced ks) (f : K6HdrField)
    (hf : f = .prop ∨ f = .ticks) (v : BitVec 32) : K6TrailSynced (ks.putHdr f v) := by
  rcases hf with rfl | rfl <;> simpa [K6TrailSynced, K6State.putHdr] using hs

private theorem fid_k6PropFrame_ticks {L : K6Layout} {c : (Nat → Bool) → Prop} {ks0 ks : K6State}
    (hf : K6PropFrame L c ks0 ks) (tk : BitVec 32) :
    K6PropFrame L c ks0 (ks.putHdr .ticks tk) :=
  ⟨k6AddTicks_preserves_inv hf.hinv tk, fid_k6TrailSynced_putHdr hf.hsync .ticks (Or.inr rfl) _,
   { hf.hpres with }, hf.htrl_ge, hf.hold, hf.hnew⟩

private theorem fid_k6BumpProp_frame {L : K6Layout} {c : (Nat → Bool) → Prop} {ks0 ks : K6State}
    (hf : K6PropFrame L c ks0 ks) (hlt : ks.prop.toNat < ks.trl_end.toNat) :
    K6PropFrame L c ks0 (ks.putHdr .prop (ks.prop + 1#32)) := by
  have hmV := L.hmaxV
  have hnv_le := hf.hinv.clauses.nv_le
  have hte_le := hf.hinv.assign.trl_end_le
  have hpr1 : (ks.prop + 1#32).toNat = ks.prop.toNat + 1 := by bv_omega
  have hcl' : K6ClausesOk L c (ks.putHdr .prop (ks.prop + 1#32)) :=
    { hf.hinv.clauses with }
  have hass' : K6BaseAssignOk c (ks.putHdr .prop (ks.prop + 1#32)) :=
    { hf.hinv.assign with prop_le := by change (ks.prop + 1#32).toNat ≤ ks.trl_end.toNat; omega }
  have hinv' : K6Inv L c (ks.putHdr .prop (ks.prop + 1#32)) :=
    ⟨hf.hinv.shapes.putHdr .prop _, hcl', fid_k6WatchesOk_putHdr hf.hinv.watches .prop (Or.inl rfl) _,
      hass', fid_k6ReasonOk_putHdr hf.hinv.reasons .prop (Or.inl rfl) _⟩
  exact ⟨hinv', fid_k6TrailSynced_putHdr hf.hsync .prop (Or.inl rfl) _,
    { hf.hpres with }, hf.htrl_ge, hf.hold, hf.hnew⟩

private theorem fid_k6WChainCursor_assignStep {ks : K6State} {l : Nat} {chains : List (List Nat)}
    {done todo : List Nat} {prev w : BitVec 32} (hcur : K6WChainCursor ks l chains done todo prev w)
    (lit rsn : BitVec 32) :
    K6WChainCursor (k6AssignStep ks lit rsn) l chains done todo prev w :=
  { len_eq := hcur.len_eq
    nodup := hcur.nodup
    chain_l := hcur.chain_l
    chains_wc := hcur.chains_wc
    chains_bnd := hcur.chains_bnd
    tail_wc := hcur.tail_wc
    prev_rel := hcur.prev_rel }

private theorem fid_k6AssignStep_propFrame {L : K6Layout} {c : (Nat → Bool) → Prop}
    {ks0 ks : K6State} (hf : K6PropFrame L c ks0 ks) {lit : BitVec 32} {cid : Nat}
    (hlit : lit.toNat < 2 * ks.nv.toNat) (hzero : ks.vals[lit.toNat]? = some 0#32)
    (hcid_lt : cid < ks.nc.toNat) (hmem : lit.toNat ∈ k6ClauseLits ks cid)
    (hoth : ∀ x ∈ k6ClauseLits ks cid, x ≠ lit.toNat → ks.vals[x]? = some 2#32) :
    let cid32 := BitVec.ofNat 32 cid
    K6PropFrame L c ks0 (k6AssignStep ks lit cid32) := by
  intro cid32
  have hmV := L.hmaxV
  have hnv_le := hf.hinv.clauses.nv_le
  have hnc_le := hf.hinv.clauses.nc_le
  have hcid32_ne : cid32 ≠ 0xFFFFFFFF#32 := by
    intro h; have h1 := congrArg BitVec.toNat h
    unfold K6Layout.maxCl at hnc_le; have hac := L.hacap; unfold dimacsBound at hac
    simp only [cid32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cid < 2 ^ 32)] at h1
    change cid = 4294967295 at h1; omega
  have hcid32_toNat : cid32.toNat = cid := by
    unfold K6Layout.maxCl at hnc_le; have hac := L.hacap; unfold dimacsBound at hac
    simp [cid32, Nat.mod_eq_of_lt (by omega : cid < 2 ^ 32)]
  have hoth_trl : ∀ x ∈ k6ClauseLits ks cid32.toNat, x ≠ lit.toNat →
      ∃ j < ks.trl_end.toNat, (ks.trl[j]?.getD 0#32).toNat = x ^^^ 1 := by
    rw [hcid32_toNat]; intro x hx hne
    have hwf := hf.hinv.clauses.cl_wf cid hcid_lt
    exact k6_falsified_to_trail hf.hinv.assign hf.hsync (hwf.2.2.1 x hx) (hoth x hx hne)
  have hent0 : ks.lvl = 0#32 → FullM4Sweep.SemEntails c [lit.toNat] := by
    intro hlvl0 β hP
    have hwf := hf.hinv.clauses.cl_wf cid hcid_lt
    obtain ⟨x, hx, hxt⟩ := (clause_sat_cnfClause_iff β (k6ClauseLits ks cid)).mp (hwf.2.2.2 β hP)
    by_cases hxl : x = lit.toNat
    · subst hxl; exact (sat_cnfClause_singleton β lit.toNat).mpr hxt
    · obtain ⟨_, hentx⟩ := k6_falsified_lvl0_entails hf.hinv hlvl0 (hwf.2.2.1 x hx) (hoth x hx hxl)
      have hneg : (cnfClause [litNeg x]).Sat β := hentx β hP
      rw [sat_cnfClause_litNeg_iff] at hneg
      exact absurd ((sat_cnfClause_singleton β x).mpr hxt) hneg
  have ⟨hinv', hsync'⟩ := k6AssignStep_preserves_inv hf.hinv hf.hsync hlit hzero hent0
    (fun _ hne => absurd hne hcid32_ne)
    (Or.inr ⟨by rw [hcid32_toNat]; exact hcid_lt, by rw [hcid32_toNat]; exact hmem, hoth_trl⟩)
  have hte_lt : ks.trl_end.toNat < ks.nv.toNat :=
    k6_trl_end_lt_of_unassigned hf.hinv.shapes hnv_le hf.hinv.assign hlit (by rw [hzero]; rfl)
  have hte1 : (ks.trl_end + 1#32).toNat = ks.trl_end.toNat + 1 := by bv_omega
  have hnot_on_trl :
      ∀ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 ≠ (lit >>> (1 : Nat)).toNat := by
    intro i hi heq
    have hshr : (lit >>> (1 : Nat)).toNat = lit.toNat / 2 := by
      simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [hshr] at heq
    have hnz := (hf.hinv.assign.vals_nz_iff_trl lit.toNat hlit).mpr ⟨i, hi, heq⟩
    apply hnz; rw [hzero]; rfl
  have hlvl_lt : (lit >>> (1 : Nat)).toNat < ks.lvlArr.length := by
    rw [hf.hinv.shapes.lvlArr_len]
    have hshr : (lit >>> (1 : Nat)).toNat = lit.toNat / 2 := by
      simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  have hrsn_lt : (lit >>> (1 : Nat)).toNat < ks.rsn.length := by
    rw [hf.hinv.shapes.rsn_len]
    have hshr : (lit >>> (1 : Nat)).toNat = lit.toNat / 2 := by
      simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  have htrl_lt : ks.trl_end.toNat < ks.trl.length := by
    rw [hf.hinv.shapes.trl_len]; omega
  refine ⟨hinv', hsync', ?_,
    by rw [show (k6AssignStep ks lit cid32).trl_end.toNat = (ks.trl_end + 1#32).toNat from rfl, hte1]
       have := hf.htrl_ge; omega,
    ?_, ?_⟩
  · exact ⟨hf.hpres.nv, hf.hpres.nc, hf.hpres.lvl, hf.hpres.incons, hf.hpres.alen, hf.hpres.acap,
      hf.hpres.nassump, hf.hpres.status, hf.hpres.openCnt, hf.hpres.max_v, hf.hpres.max_orig,
      hf.hpres.max_cl, hf.hpres.neq, hf.hpres.assump⟩
  · intro i hi
    have hi_ks : i < ks.trl_end.toNat := Nat.lt_of_lt_of_le hi hf.htrl_ge
    obtain ⟨h1, h2, h3⟩ := hf.hold i hi
    have hne_i : ks.trl_end.toNat ≠ i := Nat.ne_of_gt hi_ks
    have htr_i : (ks.trl[i]?.getD 0#32).toNat / 2 = (ks0.trl[i]?.getD 0#32).toNat / 2 := by
      have hx : ks.trl[i]? = ks0.trl[i]? := h1; simp only [hx]
    have hne_v : (ks0.trl[i]?.getD 0#32).toNat / 2 ≠ (lit >>> (1 : Nat)).toNat := by
      rw [← htr_i]; exact hnot_on_trl i hi_ks
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [k6AssignStep]; rw [List.getElem?_set_ne hne_i]; exact h1
    · dsimp only [k6AssignStep]; rw [List.getElem?_set_ne hne_v.symm]; exact h2
    · dsimp only [k6AssignStep]; rw [List.getElem?_set_ne hne_v.symm]; exact h3
  · intro i hi1 hi2
    change i < (ks.trl_end + 1#32).toNat at hi2; rw [hte1] at hi2
    by_cases hilt : i < ks.trl_end.toNat
    · obtain ⟨h1, h2⟩ := hf.hnew i hi1 hilt
      have hne_i : ks.trl_end.toNat ≠ i := Nat.ne_of_gt hilt
      have hne_v : (ks.trl[i]?.getD 0#32).toNat / 2 ≠ (lit >>> (1 : Nat)).toNat :=
        hnot_on_trl i hilt
      dsimp only [k6AssignStep]
      rw [List.getElem?_set_ne hne_i, List.getElem?_set_ne hne_v.symm,
        List.getElem?_set_ne hne_v.symm]
      exact ⟨h1, h2⟩
    · have hieq : i = ks.trl_end.toNat := by omega
      subst hieq
      dsimp only [k6AssignStep]
      rw [List.getElem?_set_self htrl_lt, Option.getD_some]
      have hdiv : lit.toNat / 2 = (lit >>> (1 : Nat)).toNat := by
        simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      rw [hdiv, List.getElem?_set_self hlvl_lt, List.getElem?_set_self hrsn_lt]
      simp only [Option.getD_some]
      exact ⟨hf.hpres.lvl, hcid32_ne⟩

private theorem fid_k6PropFrame_watchStep {L : K6Layout} {c : (Nat → Bool) → Prop}
    {ks0 ks ks' : K6State} (hf : K6PropFrame L c ks0 ks) (hinv' : K6Inv L c ks')
    (hnv : ks'.nv = ks.nv) (hnc : ks'.nc = ks.nc) (hlvl : ks'.lvl = ks.lvl)
    (hincons : ks'.incons = ks.incons) (halen : ks'.alen = ks.alen) (hacap : ks'.acap = ks.acap)
    (hnass : ks'.nassump = ks.nassump) (hst : ks'.status = ks.status)
    (hoc : ks'.openCnt = ks.openCnt) (hmv : ks'.max_v = ks.max_v)
    (hmo : ks'.max_orig = ks.max_orig) (hmc : ks'.max_cl = ks.max_cl)
    (hneq : ks'.neq = ks.neq) (hass : ks'.assump = ks.assump)
    (hte : ks'.trl_end = ks.trl_end) (htrl : ks'.trl = ks.trl)
    (hla : ks'.lvlArr = ks.lvlArr) (hrsn : ks'.rsn = ks.rsn) (hvals : ks'.vals = ks.vals) :
    K6PropFrame L c ks0 ks' := by
  refine ⟨hinv', ?_, ?_, hte ▸ hf.htrl_ge, ?_, ?_⟩
  · simpa [K6TrailSynced, hte, htrl, hvals] using hf.hsync
  · exact ⟨hnv.trans hf.hpres.nv, hnc.trans hf.hpres.nc, hlvl.trans hf.hpres.lvl,
      hincons.trans hf.hpres.incons, halen.trans hf.hpres.alen, hacap.trans hf.hpres.acap,
      hnass.trans hf.hpres.nassump, hst.trans hf.hpres.status, hoc.trans hf.hpres.openCnt,
      hmv.trans hf.hpres.max_v, hmo.trans hf.hpres.max_orig, hmc.trans hf.hpres.max_cl,
      hneq.trans hf.hpres.neq, hass.trans hf.hpres.assump⟩
  · intro i hi; simp only [htrl, hla, hrsn]; exact hf.hold i hi
  · intro i hi1 hi2; simp only [hte, htrl, hla, hrsn] at hi2 ⊢; exact hf.hnew i hi1 hi2

/-! ## 3. Main Proof: `full_k6_propagate_fid_wp` (`k6PropagateSpec`) -/

/-- `full_k6_propagate_fid` (`G1-P2.1c`: cached Kitten sub-array pointers, leaf function with
inlined assign & saturating ticks) satisfies exact `FullM6Sweep.k6PropagateSpec`. -/
theorem full_k6_propagate_fid_wp (Γ : Env) :
    ∀ args m Q X, k6PropagateSpec args m Q X →
      Func.wp Γ full_k6_propagate_fid_body args m Q X := by
  rintro ⟨kp, ⟨⟩⟩ m Q X ⟨L, c, ks, P, hinv, hsync, hm, hQ⟩
  unfold Func.wp full_k6_propagate_fid_body
  have hmA := k6Mem_to_amem hinv.shapes hm
  have hmv_eq : ks.max_v = L.mv32 := hinv.clauses.max_v_eq
  -- Normalize all 11 cached sub-array pointers at entry before entering the outer loop.
  have hp_lvl : kp + 32#64 * 4 = kp + BitVec.ofNat 64 (4 * L.oLvl) := by rfl
  have hp_rsn : (kp + BitVec.ofNat 64 (4 * L.oLvl)) + L.mv32.setWidth 64 * 4 =
      kp + BitVec.ofNat 64 (4 * L.oRsn) := by
    simpa [K6Layout.oLvl, K6Layout.oRsn] using k6_ptr_step1 L kp 0 (by decide)
  have hp_trl : (kp + BitVec.ofNat 64 (4 * L.oRsn)) + (L.mv32 <<< (2 : Nat)).setWidth 64 * 4 =
      kp + BitVec.ofNat 64 (4 * L.oTrl) := by
    simpa [K6Layout.oRsn, K6Layout.oTrl] using k6_ptr_step_sh L kp 1 4 2 rfl (by decide)
  have hp_flg : (kp + BitVec.ofNat 64 (4 * L.oTrl)) + L.mv32.setWidth 64 * 4 =
      kp + BitVec.ofNat 64 (4 * L.oFlags) := by
    simpa [K6Layout.oTrl, K6Layout.oFlags] using k6_ptr_step1 L kp 5 (by decide)
  have hp_val : (kp + BitVec.ofNat 64 (4 * L.oFlags)) +
        (L.mv32 <<< (2 : Nat)).setWidth 64 * 4 =
      kp + BitVec.ofNat 64 (4 * L.oVals) := by
    simpa [K6Layout.oFlags, K6Layout.oVals] using k6_ptr_step_sh L kp 6 4 2 rfl (by decide)
  have hp_whd : (kp + BitVec.ofNat 64 (4 * L.oVals)) +
        (L.mv32 <<< (1 : Nat)).setWidth 64 * 4 =
      kp + BitVec.ofNat 64 (4 * L.oWHead) := by
    simpa [K6Layout.oVals, K6Layout.oWHead] using k6_ptr_step_sh L kp 10 2 1 rfl (by decide)
  have hp_wnx : (kp + BitVec.ofNat 64 (4 * L.oWHead)) +
        (L.mv32 <<< (1 : Nat)).setWidth 64 * 4 =
      kp + BitVec.ofNat 64 (4 * L.oWNext) := by
    simpa [K6Layout.oWHead, K6Layout.oWNext] using k6_ptr_step_sh L kp 12 2 1 rfl (by decide)
  have hp_wbl : (kp + BitVec.ofNat 64 (4 * L.oWNext)) +
        (L.mv32 <<< (3 : Nat)).setWidth 64 * 4 =
      kp + BitVec.ofNat 64 (4 * L.oWBlit) := by
    simpa [K6Layout.oWNext, K6Layout.oWBlit] using k6_ptr_step_sh L kp 14 8 3 rfl (by decide)
  have hp_clo : (kp + BitVec.ofNat 64 (4 * L.oWBlit)) +
        (L.mv32 <<< (3 : Nat)).setWidth 64 * 4 =
      kp + BitVec.ofNat 64 (4 * L.oClOff) := by
    simpa [K6Layout.oWBlit, K6Layout.oClOff] using k6_ptr_step_sh L kp 22 8 3 rfl (by decide)
  have hp_cls : (kp + BitVec.ofNat 64 (4 * L.oClOff)) +
        (L.mv32 <<< (2 : Nat)).setWidth 64 * 4 =
      kp + BitVec.ofNat 64 (4 * L.oClSz) := by
    simpa [K6Layout.oClOff, K6Layout.oClSz] using k6_ptr_step_sh L kp 30 4 2 rfl (by decide)
  have hp_arn : (kp + BitVec.ofNat 64 (4 * L.oClSz)) +
        (L.mv32 <<< (2 : Nat)).setWidth 64 * 4 =
      kp + BitVec.ofNat 64 (4 * L.oArena) := by
    simpa [K6Layout.oClSz, K6Layout.oArena] using k6_ptr_step_sh L kp 34 4 2 rfl (by decide)
  fid_nogrp_np
  simp only [hmv_eq, hp_lvl, hp_rsn, hp_trl, hp_flg, hp_val,
    hp_whd, hp_wnx, hp_wbl, hp_clo, hp_cls, hp_arn]
  refine wp_while_state (ts := [i32, i32, i32, i64])
    (proj := fun st : K6State × BitVec 64 => (st.1.prop, st.1.trl_end, st.1.unass, st.2, ()))
    (fun st => ks.nv.toNat - st.1.prop.toNat)
    (fun (st, _) m' => K6PropFrame L c ks st ∧ (K6MemA L kp (k6ShadowHdr ks st) ⋆ P) m') ?_ ?_
  · intro J hJ; fid_steps_np
    exact hJ (ks, 0#64) m ⟨fid_k6PropFrame_refl hinv hsync, by rw [k6ShadowHdr_self]; exact hmA⟩
  · intro J ⟨st, ticks⟩ m' ⟨hf_st, hm'⟩ hJ
    have hsh0 := hf_st.hinv.shapes
    have hcl0 := hf_st.hinv.clauses
    c0_hsplit
    · have hlt : st.prop.toNat < st.trl_end.toNat := by
        try rw [show (k6ShadowHdr ks st).prop = st.prop from rfl] at hc
        try rw [show (k6ShadowHdr ks st).trl_end = st.trl_end from rfl] at hc
        exact hc
      have hpr_lt_nv : st.prop.toNat < st.nv.toNat :=
        Nat.lt_of_lt_of_le hlt hf_st.hinv.assign.trl_end_le
      have hpr_szV : st.prop.toNat < szV L := by unfold szV; have := hcl0.nv_le; omega
      have htr_mem : (st.trl[st.prop.toNat]?.getD 0#32).toNat ∈ k6TrailLits st := by
        unfold k6TrailLits; rw [List.mem_map]
        refine ⟨st.trl[st.prop.toNat]?.getD 0#32, ?_, rfl⟩
        have htl := hsh0.trl_len; have hnl := hcl0.nv_le
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact List.mem_iff_getElem.mpr
          ⟨st.prop.toNat, by simp only [List.length_take]; omega, by simp⟩
      have hlit_nv : (st.trl[st.prop.toNat]?.getD 0#32).toNat < 2 * st.nv.toNat :=
        hf_st.hinv.assign.trl_lt _ htr_mem
      let lit0 := st.trl[st.prop.toNat]?.getD 0#32
      have hnl_pair := k6_bv32_xor1_lt (l := lit0) hlit_nv
      have hnl_sz : (lit0 ^^^ 1#32).toNat < sz2V L := by
        unfold sz2V; have := hcl0.nv_le; exact Nat.lt_of_lt_of_le hnl_pair.2 (by omega)
      have hnl_fal0 : st.vals[(lit0 ^^^ 1#32).toNat]? = some 2#32 := by
        have hs := hf_st.hsync st.prop.toNat hlt
        simpa [lit0, hnl_pair.1, litNeg] using hs.2
      have hpr1_wrap : (st.prop + 1#32).toNat = st.prop.toNat + 1 := by
        have := hcl0.nv_le; have := L.hmaxV; bv_omega
      have hf_bump := fid_k6BumpProp_frame hf_st hlt
      fid_nogrp_np
      refine wp_while_state (ts := [i32, i32, i64, i64, i32, i32])
        (proj := fun stw : K6State × BitVec 32 × BitVec 64 × BitVec 64 × BitVec 32 × BitVec 32 ×
            List (List Nat) × List Nat × List Nat =>
          (stw.1.trl_end, stw.1.unass, stw.2.2.1, stw.2.2.2.1, stw.2.2.2.2.1,
            stw.2.2.2.2.2.1, ()))
        (fun stw => stw.2.2.2.2.2.2.2.2.length)
        (fun (stw, nl, _, _, prev, w, chains, done, todo) mw =>
          K6PropFrame L c ks stw ∧ nl = lit0 ^^^ 1#32 ∧ stw.prop = st.prop + 1#32 ∧
            nl.toNat < 2 * stw.nv.toNat ∧ stw.vals[nl.toNat]? = some 2#32 ∧
            K6WChainCursor stw nl.toNat chains done todo prev w ∧
            (K6MemA L kp (k6ShadowHdr ks stw) ⋆ P) mw) ?_ ?_
      · intro Jw hJw
        obtain ⟨chains0, hcur0⟩ :=
          K6WChainCursor.init hf_bump.hinv.shapes hf_bump.hinv.clauses.nv_le hf_bump.hinv.watches
            (l := (lit0 ^^^ 1#32).toNat) hnl_pair.2
        fid_steps_np
        exact hJw (st.putHdr .prop (st.prop + 1#32), lit0 ^^^ 1#32, ticks, 0#64, 0xFFFFFFFF#32,
            (st.putHdr .prop (st.prop + 1#32)).whead[(lit0 ^^^ 1#32).toNat]?.getD 0#32,
            chains0, [], chains0[(lit0 ^^^ 1#32).toNat]?.getD []) _
          ⟨hf_bump, rfl, rfl, hnl_pair.2, hnl_fal0, hcur0,
            by rw [k6ShadowHdr_bumpProp]; exact hm'⟩
      · intro Jw ⟨stw, nl, ticks', visits, prev, w, chains, done, todo⟩ mw
            ⟨hfw, hnl_lit, hpr_w, hnlW, hnl_fal, hcurW, hmw⟩ hJw
        have hshW := hfw.hinv.shapes
        have hclW := hfw.hinv.clauses
        have hac_b := L.hacap
        c0_hsplit
        · have hw_ne : w ≠ 0xFFFFFFFF#32 := ‹_›
          obtain ⟨w0, todo', hw0_wn, htodo_eq, hw_eq, hw0_nc, hw0_mc, hwnat, hcid_eq, hslot_eq,
            hsz2, har_l, hbv_nv, hbv_mem, hbin_iff, hbin_other, htail_wc⟩ :=
            hcurW.step_unfold hclW.nc_le hnlW hw_ne
          have hw_sz : w.toNat < sz2Cl L := by unfold sz2Cl; omega
          have hcid_cl : w0 / 2 < szCl L := by unfold szCl K6Layout.maxCl at *; omega
          have hbv_sz : ((stw.wblit[w.toNat]?.getD 0#32) &&& 0x7FFFFFFF#32).toNat < sz2V L := by
            unfold sz2V; have := hclW.nv_le; rw [hwnat]; omega
          have har_nl : (stw.arena[k6ClauseOff stw (w0 / 2) + w0 % 2]?.getD 0#32).toNat =
              nl.toNat := har_l
          have hcid_nc : w0 / 2 < stw.nc.toNat := by omega
          have hw_div_ne : (w >>> (1 : Nat)) ≠ 0xFFFFFFFF#32 := by
            intro h; have h1 := congrArg BitVec.toNat h
            rw [hcid_eq] at h1; unfold K6Layout.maxCl dimacsBound at hac_b; have := hclW.nc_le
            change w0 / 2 = 4294967295 at h1; omega
          c0_hsplit
          · -- `vals[bv] == 1u`
            fid_nogrp_np
            have hcur' := k6WatchSkip_cursor hshW (hw_eq ▸ htodo_eq ▸ hcurW) hw0_wn
            exact hJw (stw, nl, ticks', visits + 1#64, w, stw.wnext[w.toNat]?.getD 0#32,
                chains, done ++ [w0], todo') _
              (by dsimp only; rw [htodo_eq]; simp)
              ⟨hfw, hnl_lit, hpr_w, hnlW, hnl_fal, by rw [hwnat, hw_eq]; exact hcur', hmw⟩
          c0_hsplit
          {
          c0_hsplit
          · -- Binary watch conflict (`vals[bv] == 2u`): flush header + ticks & return `cid`
            have hbin_nz : (stw.wblit[w.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := ‹_›
            have hsz2_eq : k6ClauseSize stw (w0 / 2) = 2 := hbin_iff.mp (hwnat ▸ hbin_nz)
            have hbv_eq_ar := hbin_other hsz2_eq
            have hbv_fal :
                stw.vals[(stw.wblit[w0]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat]? = some 2#32 := by
              have hlt_bv :
                  (stw.wblit[w0]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat < stw.vals.length := by
                rw [hshW.vals_len]; have := hclW.nv_le; omega
              have h2 : stw.vals[(stw.wblit[w.toNat]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat]?.getD
                  0#32 = 2#32 := ‹_›
              rw [hwnat, List.getElem?_eq_getElem hlt_bv, Option.getD_some] at h2
              rw [List.getElem?_eq_getElem hlt_bv, h2]
            have hall_fal : ∀ l ∈ k6ClauseLits stw (w0 / 2), stw.vals[l]? = some 2#32 := by
              intro l hl
              rw [k6_mem_clauseLits_iff
                  (by rw [hshW.arena_len]; exact Nat.le_trans (hclW.cl_wf _ hcid_nc).2.1 hclW.alen_le),
                hsz2_eq] at hl
              obtain ⟨idx, hidx, rfl⟩ := hl
              have hx2 : idx = w0 % 2 ∨ idx = w0 % 2 ^^^ 1 := by
                rcases Nat.mod_two_eq_zero_or_one w0 with hm | hm <;> simp [hm] <;> omega
              rcases hx2 with rfl | rfl
              · rw [har_nl]; exact hnl_fal
              · rw [← hbv_eq_ar]; exact hbv_fal
            have hret_bin : ∀ (tk : BitVec 32) (m_out : Mem 64),
                (K6MemA L kp (stw.putHdr .ticks tk) ⋆ P) m_out →
                Q (w >>> (1 : Nat), ()) m_out := by
              intro tk m_out hmt
              let hfT := fid_k6PropFrame_ticks hfw tk
              exact hQ (w >>> (1 : Nat)) _ m_out hfT.hinv hfT.hsync hfT.hpres
                hfT.htrl_ge hfT.hold hfT.hnew (fun h => absurd h hw_div_ne)
                (fun _ => ⟨by k6_field; rw [hcid_eq]; exact hcid_nc,
                  by k6_field; rw [hcid_eq]; exact hall_fal⟩)
                (k6MemA_to_mem hmt).2
            fid_nogrp_np
            try dsimp only at hm
            try rw [show (1 : BitVec 32) = 1#32 from rfl, ← hpr_w] at hm
            try rw [k6ShadowHdr_prep] at hm
            c0_hfast
            all_goals
              try dsimp only at hm
              try rw [show (1 : BitVec 32) = 1#32 from rfl, ← hpr_w] at hm
              try rw [k6ShadowHdr_flush] at hm
              exact hret_bin _ m hm
          · -- Binary watch unit (`vals[bv] == 0u`): inlined `k6AssignStep`!
            have hbin_nz : (stw.wblit[w.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := ‹_›
            have hsz2_eq : k6ClauseSize stw (w0 / 2) = 2 := hbin_iff.mp (hwnat ▸ hbin_nz)
            have hbv_eq_ar := hbin_other hsz2_eq
            have hbv0 :
                stw.vals[(stw.wblit[w0]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat]? = some 0#32 := by
              have h1 : stw.vals[(stw.wblit[w.toNat]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat]?.getD
                  0#32 ≠ 1#32 := ‹_›
              have h2 : stw.vals[(stw.wblit[w.toNat]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat]?.getD
                  0#32 ≠ 2#32 := ‹_›
              have hlt_bv :
                  (stw.wblit[w0]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat < stw.vals.length := by
                rw [hshW.vals_len]; have := hclW.nv_le; omega
              rw [hwnat] at h1 h2
              rcases hfw.hinv.assign.vals_dom _ hbv_nv with hz | ho | ht
              · rw [List.getElem?_eq_getElem hlt_bv]
                rw [List.getElem?_eq_getElem hlt_bv, Option.getD_some] at hz; rw [hz]
              · rw [ho] at h1; exact absurd rfl h1
              · rw [ht] at h2; exact absurd rfl h2
            let bv := stw.wblit[w.toNat]?.getD 0#32 &&& 0x7FFFFFFF#32
            have hbv_toNat : bv.toNat < 2 * stw.nv.toNat := by
              dsimp only [bv]; rw [hwnat]; exact hbv_nv
            have hbv_z' : stw.vals[bv.toNat]? = some 0#32 := by
              dsimp only [bv]; rw [hwnat]; exact hbv0
            have hbv_neg := k6_bv32_xor1_lt hbv_toNat
            have hbv_neg_sz : (bv ^^^ 1#32).toNat < sz2V L := by
              unfold sz2V; have := hclW.nv_le; omega
            have hbv_v_sz : (bv >>> (1 : Nat)).toNat < szV L := by
              unfold szV; have := hclW.nv_le; have := (k6_bv32_div2_lt hbv_toNat).2; omega
            have hte_lt := k6_trl_end_lt_of_unassigned hshW hclW.nv_le hfw.hinv.assign hbv_toNat
              (by rw [hbv_z']; rfl)
            have hte_sz : stw.trl_end.toNat < szV L := by
              unfold szV; have := hclW.nv_le; omega
            have hmem_bv : bv.toNat ∈ k6ClauseLits stw (w0 / 2) := by
              dsimp only [bv]; rw [hwnat]; exact hbv_mem
            have hoth_bv : ∀ x ∈ k6ClauseLits stw (w0 / 2), x ≠ bv.toNat →
                stw.vals[x]? = some 2#32 := by
              intro x hx hne
              rw [k6_mem_clauseLits_iff
                  (by rw [hshW.arena_len]; exact Nat.le_trans (hclW.cl_wf _ hcid_nc).2.1 hclW.alen_le),
                hsz2_eq] at hx
              obtain ⟨idx, hidx, rfl⟩ := hx
              have hx2 : idx = w0 % 2 ∨ idx = w0 % 2 ^^^ 1 := by
                rcases Nat.mod_two_eq_zero_or_one w0 with hm | hm <;> simp [hm] <;> omega
              rcases hx2 with rfl | rfl
              · rw [har_nl]; exact hnl_fal
              · exfalso; apply hne; dsimp only [bv]; rw [hwnat]; exact hbv_eq_ar.symm
            have hfw' := fid_k6AssignStep_propFrame hfw hbv_toNat hbv_z' hcid_nc hmem_bv hoth_bv
            have hcid_bv : BitVec.ofNat 32 (w0 / 2) = w >>> (1 : Nat) := by
              apply BitVec.eq_of_toNat_eq; rw [hcid_eq, BitVec.toNat_ofNat]
              exact Nat.mod_eq_of_lt (by have := stw.nc.isLt; omega)
            rw [hcid_bv] at hfw'
            have hnl_ne1 : nl.toNat ≠ bv.toNat := fun h => by
              rw [h, hbv_z'] at hnl_fal; cases hnl_fal
            have hnl_ne2 : nl.toNat ≠ (bv ^^^ 1#32).toNat := fun h => by
              have hne2 : stw.vals[(bv ^^^ 1#32).toNat]?.getD 0#32 ≠ 2#32 := by
                intro h2'
                have h1 : stw.vals[bv.toNat]?.getD 0#32 = 1#32 :=
                  (hfw.hinv.assign.vals_neg_iff bv.toNat hbv_toNat).mpr (by
                    change stw.vals[litNeg bv.toNat]?.getD 0#32 = 2#32
                    rw [← hbv_neg.1]; exact h2')
                rw [hbv_z'] at h1; simp at h1
              exact hne2 (by rw [← h, hnl_fal]; rfl)
            have hnl_fal' : (k6AssignStep stw bv (w >>> (1 : Nat))).vals[nl.toNat]? = some 2#32 := by
              dsimp only [k6AssignStep]
              rw [List.getElem?_set_ne hnl_ne2.symm, List.getElem?_set_ne hnl_ne1.symm]
              exact hnl_fal
            have hcur'' := fid_k6WChainCursor_assignStep (hw_eq ▸ htodo_eq ▸ hcurW) bv (w >>> (1 : Nat))
            have hcur''' := k6WatchSkip_cursor hfw'.hinv.shapes hcur'' hw0_wn
            refine LeanQbe.T.wp_unroll_group fun Jdone hJdone => ?_
            c0_hsplit
            · -- `bvv == 0u` branch: `if (unass > 0)` and ternary `flags[v]`
              have hJw_bin : ∀ (unass' : BitVec 32) (m_out : Mem 64),
                  unass' = (k6AssignStep stw bv (w >>> (1 : Nat))).unass →
                  (K6MemA L kp (k6ShadowHdr ks (k6AssignStep stw bv (w >>> (1 : Nat)))) ⋆ P)
                    m_out →
                  Jw (stw.trl_end + 1#32, unass', ticks', visits + 1#64, w,
                      stw.wnext[w.toNat]?.getD 0#32, ()) m_out := by
                rintro _ m_out rfl hmem_eq
                exact hJw (k6AssignStep stw bv (w >>> (1 : Nat)), nl, ticks', visits + 1#64, w,
                    (k6AssignStep stw bv (w >>> (1 : Nat))).wnext[w.toNat]?.getD 0#32,
                    chains, done ++ [w0], todo') m_out
                  (by dsimp only; rw [htodo_eq]; simp)
                  ⟨hfw', hnl_lit, hpr_w, hnlW, hnl_fal',
                    (by
                      rw [hwnat]
                      exact (congrArg (fun p => K6WChainCursor
                        (k6AssignStep stw bv (w >>> (1 : Nat))) nl.toNat chains (done ++ [w0])
                        todo' p ((k6AssignStep stw bv (w >>> (1 : Nat))).wnext[w0]?.getD 0#32))
                        hw_eq).mpr hcur'''),
                    hmem_eq⟩
              have hbv_c0 :
                  ((k6ShadowHdr ks stw).wblit[w.toNat]?.getD 0#32 &&& (2147483647 : BitVec 32)) =
                    bv := rfl
              have hbv_c0' :
                  ((k6ShadowHdr ks stw).wblit[w.toNat]?.getD 0#32 &&& 0x7FFFFFFF#32) = bv := rfl
              rw [show (k6ShadowHdr ks stw).wblit = stw.wblit from rfl]
              try rw [hbv_c0]
              try rw [hbv_c0']
              try rw [fid_bv32_shr1 w]
              try rw [fid_bv32_shr1 bv]
              c0_hfast
              all_goals
                dsimp only
                (try rw [show (k6ShadowHdr ks stw).wnext = stw.wnext from rfl])
                (try rw [show (1 : BitVec 32) = 1#32 from rfl])
                (try rw [show (1 : BitVec 64) = 1#64 from rfl])
                refine hJw_bin _ m ?_ ?_
                · first
                  | (refine fid_k6Assign_unass_pos rfl ?_; assumption)
                  | (refine fid_k6Assign_unass_zero rfl ?_; assumption)
                · first
                  | (refine fid_k6Assign_mem_pos hm hfw.hpres.lvl.symm rfl rfl ?_
                     (try rw [hbv_c0] at hc)
                     (try rw [hbv_c0'] at hc)
                     (try rw [show (1 : BitVec 32) = 1#32 from rfl] at hc)
                     (try rw [show (0 : BitVec 32) = 0#32 from rfl] at hc)
                     exact hc)
                  | (refine fid_k6Assign_mem_eq0 hm hfw.hpres.lvl.symm rfl rfl ?_
                     (try rw [hbv_c0] at hc)
                     (try rw [hbv_c0'] at hc)
                     (try rw [show (1 : BitVec 32) = 1#32 from rfl] at hc)
                     (try rw [show (0 : BitVec 32) = 0#32 from rfl] at hc)
                     exact hc)
            · have hfalse :
                  stw.vals[(stw.wblit[w.toNat]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat]? =
                    some 0#32 := by rw [hwnat]; exact hbv0
              have hc' : stw.vals[(stw.wblit[w.toNat]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat]?.getD
                  0#32 ≠ 0#32 := ‹_›
              rw [hfalse] at hc'; exact absurd rfl hc'
          }
          · -- Non-binary watch (`wb &&& 0x80000000 = 0`)
            have hbin_z : (stw.wblit[w.toNat]?.getD 0#32 &&& 0x80000000#32) = 0#32 := ‹_›
            have hsz_ne2 : k6ClauseSize stw (w0 / 2) ≠ 2 := fun h2 =>
              absurd (hbin_iff.mpr h2) (by rw [← hwnat, hbin_z]; simp)
            have hwf_c := hclW.cl_wf (w0 / 2) hcid_nc
            have har_ok : ∀ idx < k6ClauseSize stw (w0 / 2),
                k6ClauseOff stw (w0 / 2) + idx < L.acap ∧
                (stw.arena[k6ClauseOff stw (w0 / 2) + idx]?.getD 0#32).toNat < 2 * stw.nv.toNat := by
              intro idx hidx
              exact ⟨by have := hclW.alen_le; omega,
                hwf_c.2.2.1 _ (by
                  rw [k6_mem_clauseLits_iff
                    (by rw [hshW.arena_len]; exact Nat.le_trans hwf_c.2.1 hclW.alen_le)]
                  exact ⟨idx, hidx, rfl⟩)⟩
            have hother_slot_lt : w0 % 2 ^^^ 1 < 2 := by
              rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [h]
            let other := stw.arena[k6ClauseOff stw (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32
            have hother_nv : other.toNat < 2 * stw.nv.toNat := (har_ok _ (by omega)).2
            have hot_mem : other.toNat ∈ k6ClauseLits stw (w0 / 2) := by
              rw [k6_mem_clauseLits_iff
                (by rw [hshW.arena_len]; exact Nat.le_trans hwf_c.2.1 hclW.alen_le)]
              exact ⟨w0 % 2 ^^^ 1, by omega, rfl⟩
            have hw_sh1 : (w >>> (1 : Nat)).toNat = w0 / 2 := hcid_eq
            have hw_m2_lt : w0 % 2 < 2 ^ 32 := Nat.lt_trans (Nat.mod_lt w0 (by decide)) (by decide)
            have hm2_xor_lt : w0 % 2 ^^^ 1 < 2 ^ 32 := by
              rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [h]
            have hslot_bv : (w &&& (1 : BitVec 32)) = BitVec.ofNat 32 (w0 % 2) := by
              apply BitVec.eq_of_toNat_eq
              change (w &&& 1#32).toNat = (BitVec.ofNat 32 (w0 % 2)).toNat
              rw [hslot_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_m2_lt]
            have hslot_other_bv :
                (w &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)) = BitVec.ofNat 32 (w0 % 2 ^^^ 1) := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_xor, show (w &&& (1 : BitVec 32)).toNat = (w &&& 1#32).toNat from rfl,
                hslot_eq, show (1 : BitVec 32).toNat = 1 from rfl, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt hm2_xor_lt]
            have hcl_off_add :
                (stw.clOff[w0 / 2]?.getD 0#32).toNat +
                  (w &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat =
                k6ClauseOff stw (w0 / 2) + (w0 % 2 ^^^ 1) := by
              rw [hslot_other_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm2_xor_lt]; rfl
            have hcl_off_ar :
                (stw.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                  (w &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat < szAr L := by
              unfold szAr; rw [hw_sh1, hcl_off_add]; exact (har_ok (w0 % 2 ^^^ 1) (by omega)).1
            have hother_mv2 : other.toNat < sz2V L := by unfold sz2V; have := hclW.nv_le; omega
            have hother_mv2' :
                (stw.arena[(stw.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                  (w &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat]?.getD 0#32).toNat < sz2V L := by
              rw [hw_sh1, hcl_off_add]; exact hother_mv2
            have hw_div_ar : (w >>> (1 : Nat)).toNat < szCl L := by rw [hw_sh1]; exact hcid_cl
            have hwc : K6WChainCursor stw nl.toNat chains done (w0 :: todo') prev
                (BitVec.ofNat 32 w0) := hw_eq ▸ htodo_eq ▸ hcurW
            c0_hsplit
            · -- `vals[other] == 1u`
              obtain ⟨hkp_inv, hkp_wc⟩ :=
                k6WatchKeep_preserves hfw.hinv hnlW hwc hother_nv hot_mem hsz_ne2
              have hfw' := fid_k6PropFrame_watchStep hfw hkp_inv
                rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
              c0_hfast
              refine hJw (stw.putArr .wblit w0 other, nl, ticks' + 1#64, visits + 1#64, w,
                  stw.wnext[w.toNat]?.getD 0#32, chains, done ++ [w0], todo') _
                (by dsimp only; rw [htodo_eq]; simp)
                ⟨hfw', hnl_lit, hpr_w, hnlW, hnl_fal, by rw [hwnat, hw_eq]; exact hkp_wc, ?_⟩
              refine Eq.mp (congrArg (fun x => (K6MemA L kp x ⋆ _) _) ?_) ‹_›
              rw [k6ShadowHdr_putArr]
              dsimp only [k6ShadowHdr, K6State.putArr, other, k6ClauseOff]
              simp only [hwnat, hw_sh1, hcl_off_add]
              rfl
            · -- `vals[other] ≠ 1u`: search `[2..sz)` for non-falsified replacement
              have hidx_eq :
                  (stw.clOff[w.toNat / 2]?.getD 0#32).toNat + (w.toNat % 2 ^^^ 1) =
                  k6ClauseOff stw (w0 / 2) + (w0 % 2 ^^^ 1) := by rw [hwnat]; rfl
              have hother_ne1 : stw.vals[other.toNat]?.getD 0#32 ≠ 1#32 := by
                rw [show (k6ShadowHdr ks stw).vals = stw.vals from rfl,
                  show (k6ShadowHdr ks stw).arena = stw.arena from rfl,
                  show (k6ShadowHdr ks stw).clOff = stw.clOff from rfl, hwnat] at hc
                rw [show (w &&& 1#32 ^^^ 1#32) = (w &&& (1 : BitVec 32) ^^^ (1 : BitVec 32))
                  from rfl, hcl_off_add] at hc
                exact hc
              let sz := stw.clSz[w0 / 2]?.getD 0#32
              let off := stw.clOff[w0 / 2]?.getD 0#32
              refine wp_while_break_state
                (projBrk := fun b : BitVec 32 × BitVec 32 × BitVec 32 => (b.1, b.2.1, b.2.2, ()))
                (fun b mb => mb = mw ∧
                  (b.2.1 = 0xFFFFFFFF#32 ∧
                      (∀ j, 2 ≤ j → j < sz.toNat →
                        stw.vals[(stw.arena[off.toNat + j]?.getD 0#32).toNat]? = some 2#32) ∨
                    (2 ≤ b.2.1.toNat ∧ b.2.1.toNat < sz.toNat ∧
                      b.2.2 = stw.arena[off.toNat + b.2.1.toNat]?.getD 0#32 ∧
                      stw.vals[b.2.2.toNat]? ≠ some 2#32)))
                (projLp := fun r : BitVec 32 => (r, ())) (fun r => sz.toNat - r.toNat)
                (fun r m'' => m'' = mw ∧ r.toNat ≤ sz.toNat ∧ 2 ≤ r.toNat ∧
                  ∀ j, 2 ≤ j → j < r.toNat →
                    stw.vals[(stw.arena[off.toNat + j]?.getD 0#32).toNat]? = some 2#32) ?_ ?_ ?_
              · rintro Br ⟨_, ri, repl⟩ mb ⟨rfl, hbrk⟩
                dsimp only at hbrk ⊢
                c0_hsplit
                · -- Relocate watch (`ri != 0xFFFFFFFFu`)
                  have hri_ne : ri ≠ 0xFFFFFFFF#32 := by exact hc
                  rcases hbrk with ⟨habs, _⟩ | ⟨hri_ge, hri_lt, hrepl_eq, hrepl_nf⟩
                  · exact absurd habs hri_ne
                  have hrepl_ne' : repl.toNat ≠ nl.toNat := fun h => by
                    rw [h, hnl_fal] at hrepl_nf; exact hrepl_nf rfl
                  obtain ⟨hrl_inv, ⟨chW', hwc'⟩⟩ :=
                    k6WatchReloc_preserves hfw.hinv hnlW hwc hri_ge hri_lt hrepl_ne' rfl hrepl_eq
                  have hfw' := fid_k6PropFrame_watchStep hfw hrl_inv
                    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                  obtain ⟨hri_cap, _⟩ := har_ok ri.toNat hri_lt
                  obtain ⟨hslot_cap, _⟩ :=
                    har_ok (w0 % 2) (by have := Nat.mod_lt w0 (by decide : 0 < 2); omega)
                  have hslot_off_eq :
                      (stw.clOff[w0 / 2]?.getD 0#32).toNat + (w &&& (1 : BitVec 32)).toNat =
                      (stw.clOff[w0 / 2]?.getD 0#32).toNat + w0 % 2 := by
                    rw [hslot_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw_m2_lt]
                  have hslot_ar :
                      (stw.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                        (w &&& (1 : BitVec 32)).toNat < szAr L := by
                    unfold szAr; rw [hw_sh1, hslot_off_eq]; exact hslot_cap
                  have hri_ar :
                      (stw.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32).toNat + ri.toNat < szAr L := by
                    unfold szAr; rw [hw_sh1]; exact hri_cap
                  have hrepl_mv2 : repl.toNat < sz2V L := by
                    change repl = stw.arena[k6ClauseOff stw (w0 / 2) + ri.toNat]?.getD 0#32 at hrepl_eq
                    rw [hrepl_eq]; unfold sz2V; have := hclW.nv_le; omega
                  have hnl_bn : BitVec.ofNat 32 nl.toNat = nl := by simp
                  have hprv_lt : prev ≠ 0xFFFFFFFF#32 → prev.toNat < sz2Cl L := fun hp => by
                    rcases hwc.prev_rel with ⟨_, hpf, _⟩ | ⟨_, u, _, hp_eq, hu_len, _⟩
                    · exact absurd hpf hp
                    · rw [hshW.wnext_len] at hu_len
                      have hu32 : u < 2 ^ 32 := by
                        have hmx := L.hmaxV
                        try unfold sz2Cl at hu_len
                        try unfold K6Layout.maxCl at hu_len
                        omega
                      rw [hp_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu32]
                      unfold sz2Cl; exact hu_len
                  let hw_rel := k6WatchStep0
                    { stw with
                      whead := if prev = 0xFFFFFFFF#32 then
                        stw.whead.set nl.toNat (stw.wnext[w0]?.getD 0#32) else stw.whead
                      wnext := if prev = 0xFFFFFFFF#32 then
                        stw.wnext else stw.wnext.set prev.toNat (stw.wnext[w0]?.getD 0#32)
                      arena := (stw.arena.set (k6ClauseOff stw (w0 / 2) + w0 % 2) repl).set
                        (k6ClauseOff stw (w0 / 2) + ri.toNat) (BitVec.ofNat 32 nl.toNat) }
                    (BitVec.ofNat 32 w0) repl
                    (stw.arena[k6ClauseOff stw (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32)
                  fid_nogrp_np
                  try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                  c0_hsplit
                  · have hpeq : prev = 0xFFFFFFFF#32 := by exact hc
                    fid_steps_np
                    refine hJw (hw_rel, nl, ticks' + 1#64, visits + 1#64, prev,
                        stw.wnext[w.toNat]?.getD 0#32, chW', done, todo') _
                      (by dsimp only; rw [htodo_eq]; simp)
                      ⟨hfw', hnl_lit, by dsimp only [hw_rel, k6WatchStep0]; exact hpr_w, hnlW,
                        by dsimp only [hw_rel, k6WatchStep0]; exact hnl_fal,
                        by rw [hwnat]; exact hwc', ?_⟩
                    refine Eq.mp (congrArg (fun x => (K6MemA L kp x ⋆ _) _) ?_) ‹_›
                    dsimp only [hw_rel, k6ShadowHdr, k6WatchStep0, k6ClauseOff]
                    simp only [hpeq, ↓reduceIte]
                    have hnl_lit' : st.trl[st.prop.toNat]?.getD 0#32 ^^^ 1 = nl := hnl_lit.symm
                    have hw_cid1 : (w >>> OfNat.ofNat 1).toNat = w0 / 2 := hcid_eq
                    have hbv_w0 : (BitVec.ofNat 32 w0).toNat = w0 := hw_eq ▸ hwnat
                    k6_ext <;> (first | rfl | {
                      (try simp only [hw_cid1, hwnat, hcl_off_add, hslot_off_eq, hnl_lit', hnl_bn])
                      (try rw [hbv_w0])
                      (try rw [hw_eq])
                      (try dsimp only [k6ClauseOff])
                      (try rfl) })
                  · have hpne : prev ≠ 0xFFFFFFFF#32 := by exact hc
                    have hprv_bd := hprv_lt hpne
                    fid_steps_np
                    refine hJw (hw_rel, nl, ticks' + 1#64, visits + 1#64, prev,
                        stw.wnext[w.toNat]?.getD 0#32, chW', done, todo') _
                      (by dsimp only; rw [htodo_eq]; simp)
                      ⟨hfw', hnl_lit, by dsimp only [hw_rel, k6WatchStep0]; exact hpr_w, hnlW,
                        by dsimp only [hw_rel, k6WatchStep0]; exact hnl_fal,
                        by rw [hwnat]; exact hwc', ?_⟩
                    refine Eq.mp (congrArg (fun x => (K6MemA L kp x ⋆ _) _) ?_) ‹_›
                    dsimp only [hw_rel, k6ShadowHdr, k6WatchStep0, k6ClauseOff]
                    simp only [hpne, ↓reduceIte]
                    have hnl_lit' : st.trl[st.prop.toNat]?.getD 0#32 ^^^ 1 = nl := hnl_lit.symm
                    have hw_cid1 : (w >>> OfNat.ofNat 1).toNat = w0 / 2 := hcid_eq
                    have hbv_w0 : (BitVec.ofNat 32 w0).toNat = w0 := hw_eq ▸ hwnat
                    k6_ext <;> (first | rfl | {
                      (try simp only [hw_cid1, hwnat, hcl_off_add, hslot_off_eq, hnl_lit', hnl_bn])
                      (try rw [hbv_w0])
                      (try rw [hw_eq])
                      (try dsimp only [k6ClauseOff])
                      (try rfl) })
                · -- No replacement (`ri = 0xFFFFFFFFu`): keep watch with `other` & conflict/unit check
                  have hrieq : ri = 0xFFFFFFFF#32 := by exact hc
                  rcases hbrk with ⟨_, hall_r2⟩ | ⟨hri_ge, hri_lt, _⟩
                  · obtain ⟨hkp_inv, hkp_wc⟩ :=
                      k6WatchKeep_preserves hfw.hinv hnlW hwc hother_nv hot_mem hsz_ne2
                    have hfw' := fid_k6PropFrame_watchStep hfw hkp_inv
                      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                    have hmem_other : other.toNat < stw.vals.length := by
                      rw [hshW.vals_len]; exact hother_mv2
                    have hoth_sz : other.toNat < sz2V L := hother_mv2
                    let hw' := stw.putArr .wblit w0 other
                    have hall_other_fal : ∀ l ∈ k6ClauseLits hw' (w0 / 2),
                        l ≠ other.toNat → hw'.vals[l]? = some 2#32 := by
                      intro l hl hne
                      change l ∈ k6ClauseLits stw (w0 / 2) at hl
                      rw [k6_mem_clauseLits_iff
                        (by rw [hshW.arena_len]; exact Nat.le_trans hwf_c.2.1 hclW.alen_le)] at hl
                      obtain ⟨idx, hidx, rfl⟩ := hl
                      change stw.vals[(stw.arena[off.toNat + idx]?.getD 0#32).toNat]? = some 2#32
                      by_cases h01 : idx < 2
                      · have hx2 : idx = w0 % 2 ∨ idx = w0 % 2 ^^^ 1 := by
                          rcases Nat.mod_two_eq_zero_or_one w0 with hm | hm <;> simp [hm] <;> omega
                        rcases hx2 with rfl | rfl
                        · change stw.vals[(stw.arena[k6ClauseOff stw (w0 / 2) +
                            w0 % 2]?.getD 0#32).toNat]? = some 2#32
                          rw [har_nl]; exact hnl_fal
                        · exfalso; exact hne rfl
                      · exact hall_r2 idx (by omega) hidx
                    c0_hsplit
                    · -- `ov == 2u`: conflict -> flush header + ticks & return `cid`
                      have hov2 : hw'.vals[other.toNat]? = some 2#32 := by
                        have h2 : stw.vals[(stw.arena[k6ClauseOff stw (w0 / 2) +
                            (w0 % 2 ^^^ 1)]?.getD 0#32).toNat]?.getD 0#32 = 2#32 := by
                          simpa [K6State.putArr, k6ShadowHdr, hidx_eq] using hc
                        dsimp only [hw', K6State.putArr, other]
                        rw [List.getElem?_eq_getElem hmem_other, Option.getD_some] at h2
                        rw [List.getElem?_eq_getElem hmem_other, h2]
                      have hall_fal' : ∀ l ∈ k6ClauseLits hw' (w0 / 2), hw'.vals[l]? = some 2#32 := by
                        intro l hl
                        by_cases he : l = other.toNat
                        · subst he; exact hov2
                        · exact hall_other_fal l hl he
                      have hw_cid1 : (w >>> OfNat.ofNat 1).toNat = w0 / 2 := hcid_eq
                      have hmw_kp : (K6MemA L kp (k6ShadowHdr ks hw') ⋆ P) m := by
                        refine Eq.mp (congrArg (fun x => (K6MemA L kp x ⋆ P) m) ?_) hm
                        rw [k6ShadowHdr_putArr]
                        dsimp only [hw', k6ShadowHdr, K6State.putArr, other, k6ClauseOff]
                        simp only [hwnat, hw_cid1, hcl_off_add]
                        rfl
                      clear hm
                      have hret_ov2 : ∀ (tk : BitVec 32) (m_out : Mem 64),
                          (K6MemA L kp (hw'.putHdr .ticks tk) ⋆ P) m_out →
                          Q (w >>> (1 : Nat), ()) m_out := by
                        intro tk m_out hmt
                        let hfT := fid_k6PropFrame_ticks hfw' tk
                        exact hQ (w >>> (1 : Nat)) _ m_out hfT.hinv hfT.hsync hfT.hpres
                          hfT.htrl_ge hfT.hold hfT.hnew (fun h => absurd h hw_div_ne)
                          (fun _ => ⟨by rw [hcid_eq]; exact hcid_nc,
                            by rw [hcid_eq]; intro l hl; exact hall_fal' l hl⟩)
                          (k6MemA_to_mem hmt).2
                      fid_nogrp_np
                      try dsimp only at hm
                      try rw [show (1 : BitVec 32) = 1#32 from rfl, ← hpr_w] at hm
                      try rw [k6ShadowHdr_prep] at hm
                      c0_hfast
                      all_goals
                        try dsimp only at hm
                        try rw [show (1 : BitVec 32) = 1#32 from rfl, ← hpr_w] at hm
                        try rw [k6ShadowHdr_flush] at hm
                        exact hret_ov2 _ m hm
                    · -- `ov == 0u`: unit -> inlined `k6AssignStep`!
                      have hoth0 : hw'.vals[other.toNat]? = some 0#32 := by
                        have hdom := hfw.hinv.assign.vals_dom other.toNat hother_nv
                        have hne1 : stw.vals[other.toNat]?.getD 0#32 ≠ 1#32 := hother_ne1
                        have hne2 : stw.vals[other.toNat]?.getD 0#32 ≠ 2#32 := by
                          simpa [K6State.putArr, k6ShadowHdr, hidx_eq, other] using hc
                        rw [List.getElem?_eq_getElem hmem_other, Option.getD_some] at hne1 hne2
                        dsimp only [hw', K6State.putArr]
                        rw [List.getElem?_eq_getElem hmem_other]
                        rcases hdom with hz | ho | ht
                        · rw [List.getElem?_eq_getElem hmem_other, Option.getD_some] at hz; rw [hz]
                        · rw [List.getElem?_eq_getElem hmem_other, Option.getD_some] at ho
                          exact absurd ho hne1
                        · rw [List.getElem?_eq_getElem hmem_other, Option.getD_some] at ht
                          exact absurd ht hne2
                      have hte_lt := k6_trl_end_lt_of_unassigned hfw'.hinv.shapes
                        hfw'.hinv.clauses.nv_le hfw'.hinv.assign hother_nv (by rw [hoth0]; rfl)
                      have hw_cid1 : (w >>> OfNat.ofNat 1).toNat = w0 / 2 := hcid_eq
                      have hmw_kp : (K6MemA L kp (k6ShadowHdr ks hw') ⋆ P) m := by
                        refine Eq.mp (congrArg (fun x => (K6MemA L kp x ⋆ P) m) ?_) hm
                        rw [k6ShadowHdr_putArr]
                        dsimp only [hw', k6ShadowHdr, K6State.putArr, other, k6ClauseOff]
                        simp only [hwnat, hw_cid1, hcl_off_add]
                        rfl
                      clear hm
                      have hother_c0 :
                          stw.arena[(stw.clOff[(w >>> OfNat.ofNat 1).toNat]?.getD 0#32).toNat +
                            (w &&& 1 ^^^ 1).toNat]?.getD 0#32 = other := by
                        rw [hw_cid1, hcl_off_add]
                      have hw_sh1_bv : (w >>> OfNat.ofNat 1) = w >>> (1 : Nat) := by
                        apply BitVec.eq_of_toNat_eq; exact hw_cid1.trans hw_sh1.symm
                      have hoth_neg := k6_bv32_xor1_lt hother_nv
                      have hoth_neg_sz : (other ^^^ 1#32).toNat < sz2V L := by
                        unfold sz2V; have := hclW.nv_le; omega
                      have hoth_v_sz : (other >>> (1 : Nat)).toNat < szV L := by
                        unfold szV; have := hclW.nv_le; have := (k6_bv32_div2_lt hother_nv).2; omega
                      have hte_sz : hw'.trl_end.toNat < szV L := by
                        unfold szV; have := hclW.nv_le; exact Nat.lt_of_lt_of_le hte_lt this
                      have hfw'' := fid_k6AssignStep_propFrame hfw' hother_nv hoth0 hcid_nc hot_mem
                        hall_other_fal
                      have hcid_bv : BitVec.ofNat 32 (w0 / 2) = w >>> (1 : Nat) := by
                        apply BitVec.eq_of_toNat_eq; rw [hcid_eq, BitVec.toNat_ofNat]
                        exact Nat.mod_eq_of_lt (by have := stw.nc.isLt; omega)
                      rw [hcid_bv] at hfw''
                      have hnl_ne1 : nl.toNat ≠ other.toNat := fun h => by
                        have hoth0' : stw.vals[other.toNat]? = some 0#32 := hoth0
                        rw [h, hoth0'] at hnl_fal; cases hnl_fal
                      have hnl_ne2 : nl.toNat ≠ (other ^^^ 1#32).toNat := fun h => by
                        have h1 : stw.vals[other.toNat]?.getD 0#32 = 1#32 :=
                          (hfw.hinv.assign.vals_neg_iff other.toNat hother_nv).mpr (by
                            change stw.vals[litNeg other.toNat]?.getD 0#32 = 2#32
                            rw [← hoth_neg.1, ← h]; rw [hnl_fal]; rfl)
                        rw [show stw.vals[other.toNat]?.getD 0#32 = 0#32 by
                          simpa [hw', K6State.putArr] using congrArg (Option.getD · 0#32) hoth0]
                          at h1
                        simp at h1
                      have hnl_fal'' :
                          (k6AssignStep hw' other (w >>> (1 : Nat))).vals[nl.toNat]? = some 2#32 := by
                        dsimp only [k6AssignStep]
                        rw [List.getElem?_set_ne hnl_ne2.symm, List.getElem?_set_ne hnl_ne1.symm]
                        exact hnl_fal
                      have hcur''' := fid_k6WChainCursor_assignStep hkp_wc other (w >>> (1 : Nat))
                      obtain ⟨hw'', hw''_eq⟩ : ∃ x, x = hw' := ⟨hw', rfl⟩
                      have hm : (K6MemA L kp (k6ShadowHdr ks hw'') ⋆ P) m := by
                        rw [hw''_eq]; exact hmw_kp
                      clear hmw_kp
                      have hfw''_op :
                          K6PropFrame L c ks (k6AssignStep hw'' other (w >>> (1 : Nat))) := by
                        rw [hw''_eq]; exact hfw''
                      have hnl_fal''_op :
                          (k6AssignStep hw'' other (w >>> (1 : Nat))).vals[nl.toNat]? = some 2#32 := by
                        rw [hw''_eq]; exact hnl_fal''
                      have hcur'''_op :
                          K6WChainCursor (k6AssignStep hw'' other (w >>> (1 : Nat))) nl.toNat chains
                            (done ++ [w0]) todo' (BitVec.ofNat 32 w0)
                            (stw.wnext[w0]?.getD 0#32) := by
                        rw [hw''_eq]; exact hcur'''
                      have htrl_hw'' : stw.trl_end = hw''.trl_end := by rw [hw''_eq]; rfl
                      have hunass_hw'' : stw.unass = hw''.unass := by rw [hw''_eq]; rfl
                      have hlvl_hw'' : ks.lvl = hw''.lvl := by
                        rw [hw''_eq]; exact hfw'.hpres.lvl.symm
                      have hprop_hw'' : hw''.prop = stw.prop := by rw [hw''_eq]; rfl
                      have hnv_hw'' : hw''.nv = stw.nv := by rw [hw''_eq]; rfl
                      have hwnext_hw'' : hw''.wnext = stw.wnext := by rw [hw''_eq]; rfl
                      refine LeanQbe.T.wp_unroll_group fun Jdone hJdone => ?_
                      c0_hsplit
                      · -- `ov == 0u` branch
                        have hJw_ov0 : ∀ (unass' : BitVec 32) (m_out : Mem 64),
                            unass' = (k6AssignStep hw'' other (w >>> (1 : Nat))).unass →
                            (K6MemA L kp (k6ShadowHdr ks
                              (k6AssignStep hw'' other (w >>> (1 : Nat)))) ⋆ P) m_out →
                            Jw (stw.trl_end + 1#32, unass', ticks' + 1#64, visits + 1#64, w,
                                stw.wnext[w.toNat]?.getD 0#32, ()) m_out := by
                          rintro _ m_out rfl hmem_eq
                          rw [htrl_hw'', ← hwnext_hw'']
                          exact hJw (k6AssignStep hw'' other (w >>> (1 : Nat)), nl, ticks' + 1#64,
                              visits + 1#64, w, hw''.wnext[w.toNat]?.getD 0#32, chains,
                              done ++ [w0], todo') m_out
                            (by dsimp only; rw [htodo_eq]; simp)
                            ⟨hfw''_op, hnl_lit, hprop_hw''.trans hpr_w,
                              (by change nl.toNat < 2 * hw''.nv.toNat; rw [hnv_hw'']
                                  exact hnlW),
                              hnl_fal''_op,
                              (by rw [hwnat, hw_eq]; have hc' := hcur'''_op
                                  rw [hw_eq, ← hwnext_hw''] at hc'; exact hc'),
                              hmem_eq⟩
                        rw [show (k6ShadowHdr ks stw).arena = stw.arena from rfl,
                          show (k6ShadowHdr ks stw).clOff = stw.clOff from rfl,
                          hother_c0, hw_sh1_bv]
                        try rw [fid_bv32_shr1 other]
                        c0_hfast
                        all_goals
                          (try dsimp only)
                          (try rw [show (k6ShadowHdr ks stw).wnext = stw.wnext from rfl])
                          (try rw [show (1 : BitVec 32) = 1#32 from rfl])
                          (try rw [show (1 : BitVec 64) = 1#64 from rfl])
                          refine hJw_ov0 _ m ?_ ?_
                          · first
                            | (refine fid_k6Assign_unass_pos hunass_hw'' ?_; assumption)
                            | (refine fid_k6Assign_unass_zero hunass_hw'' ?_; assumption)
                          · first
                            | (refine fid_k6Assign_mem_pos hm hlvl_hw''
                                 (congrArg BitVec.toNat htrl_hw'') rfl ?_
                               (try rw [show (1 : BitVec 32) = 1#32 from rfl] at hc)
                               (try rw [show (0 : BitVec 32) = 0#32 from rfl] at hc)
                               exact hc)
                            | (refine fid_k6Assign_mem_eq0 hm hlvl_hw''
                                 (congrArg BitVec.toNat htrl_hw'') rfl ?_
                               (try rw [show (1 : BitVec 32) = 1#32 from rfl] at hc)
                               (try rw [show (0 : BitVec 32) = 0#32 from rfl] at hc)
                               exact hc)
                      · have hc' : hw'.vals[other.toNat]?.getD 0#32 ≠ 0#32 := by
                          simpa [hw', K6State.putArr, k6ShadowHdr, hidx_eq, other] using hc
                        rw [hoth0] at hc'; exact absurd rfl hc'
                  · exfalso
                    have h429 : (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 := rfl
                    rw [hrieq, h429] at hri_lt
                    have hwf_bd : k6ClauseSize stw (w0 / 2) ≤ stw.alen.toNat := by
                      have := hwf_c.2.1; omega
                    have hal := hclW.alen_le
                    have hsz_nat : sz.toNat = k6ClauseSize stw (w0 / 2) := rfl
                    rw [hsz_nat] at hri_lt
                    unfold K6Layout.acap at hac_b hal
                    unfold dimacsBound at hac_b
                    omega
              · intro B2 L2 r m1 hB2 ih1 ⟨rfl, hr_le, hr2, hall_j⟩
                dsimp only at hr_le hr2 hall_j ⊢
                c0_hsplit
                · have hr_lt : r.toNat < sz.toNat := by
                    rw [show (k6ShadowHdr ks stw).clSz = stw.clSz from rfl, hwnat] at hc
                    exact hc
                  obtain ⟨hr_cap, hr_lit⟩ := har_ok r.toNat hr_lt
                  have hr_ar :
                      (stw.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32).toNat + r.toNat < szAr L := by
                    rw [hw_sh1]; exact hr_cap
                  have hcand_mv2 :
                      (stw.arena[(stw.clOff[(w >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                        r.toNat]?.getD 0#32).toNat < sz2V L := by
                    rw [hw_sh1]; unfold sz2V
                    exact Nat.lt_of_lt_of_le hr_lit (Nat.mul_le_mul_left 2 hclW.nv_le)
                  have hr1_wrap : (r + 1#32).toNat = r.toNat + 1 :=
                    fid_r_add1 (hr_lt : r.toNat < k6ClauseSize stw (w0 / 2))
                      hwf_c.2.1 hclW.alen_le hac_b.2
                  c0_hsplit
                  · have hc_nf : stw.vals[(stw.arena[off.toNat + r.toNat]?.getD 0#32).toNat]? ≠
                        some 2#32 := by
                      have hc0 : stw.vals[(stw.arena[(stw.clOff[(w >>> (1 : Nat)).toNat]?.getD
                          0#32).toNat + r.toNat]?.getD 0#32).toNat]?.getD 0#32 ≠ 2#32 := ‹_›
                      rw [hw_sh1] at hc0
                      intro h2; apply hc0; rw [h2]; rfl
                    rw [hw_sh1]
                    exact hB2 (r, r, stw.arena[off.toNat + r.toNat]?.getD 0#32) _
                      ⟨rfl, Or.inr ⟨hr2, hr_lt, rfl, hc_nf⟩⟩
                  · have hc_f : stw.vals[(stw.arena[off.toNat + r.toNat]?.getD 0#32).toNat]? =
                        some 2#32 := by
                      have hc0 : stw.vals[(stw.arena[(stw.clOff[(w >>> (1 : Nat)).toNat]?.getD
                          0#32).toNat + r.toNat]?.getD 0#32).toNat]?.getD 0#32 = 2#32 := ‹_›
                      have hvl : (stw.arena[off.toNat + r.toNat]?.getD 0#32).toNat <
                          stw.vals.length := by
                        change (stw.arena[k6ClauseOff stw (w0 / 2) + r.toNat]?.getD 0#32).toNat <
                          stw.vals.length
                        rw [hshW.vals_len]
                        exact Nat.lt_of_lt_of_le hr_lit (Nat.mul_le_mul_left 2 hclW.nv_le)
                      rw [hw_sh1, List.getElem?_eq_getElem hvl, Option.getD_some] at hc0
                      rw [List.getElem?_eq_getElem hvl, hc0]
                    refine ih1 (r + 1#32) _
                      (by rw [hr1_wrap]; exact Nat.sub_lt_sub_left hr_lt (Nat.lt_succ_self _))
                      ⟨rfl, by rw [hr1_wrap]; exact hr_lt,
                       by rw [hr1_wrap]; exact Nat.le_trans hr2 (Nat.le_succ _), fun j hj1 hj2 => ?_⟩
                    rw [hr1_wrap] at hj2
                    by_cases hjr : j = r.toNat
                    · subst hjr; exact hc_f
                    · exact hall_j j hj1 (by omega)
                · have hr_ge : sz.toNat ≤ r.toNat := by
                    rw [show (k6ShadowHdr ks stw).clSz = stw.clSz from rfl, hwnat] at hc
                    exact Nat.le_of_not_lt hc
                  fid_steps_np
                  exact hB2 (r, 0xFFFFFFFF#32, 0#32) _
                    ⟨rfl, Or.inl ⟨rfl, fun j hj1 hj2 => hall_j j hj1 (by omega)⟩⟩
              · intro B2 L2 _ hL2; fid_steps_np
                exact hL2 2#32 mw ⟨rfl, hsz2, le_refl _, fun j hj1 hj2 => by
                  have h2n : (2#32 : BitVec 32).toNat = 2 := rfl; omega⟩
        · -- `w = 0xFFFFFFFF#32`: inner loop exit -> outer loop continue
          fid_steps_np
          dsimp only
          rw [show (1 : BitVec 32) = 1#32 from rfl, show (1 : BitVec 64) = 1#64 from rfl,
            show (OfNat.ofNat 4 : Nat) = 4 from rfl, ← hpr_w]
          exact hJ (stw, ticks' + (visits >>> (4 : Nat)) + 1#64) mw
            (by
              dsimp only; rw [hpr_w, hpr1_wrap, ← hf_st.hpres.nv]
              exact Nat.sub_lt_sub_left
                (Nat.lt_of_lt_of_le hlt hf_st.hinv.assign.trl_end_le) (Nat.lt_succ_self _))
            ⟨hfw, hmw⟩
    · -- `st.prop ≥ st.trl_end`: outer loop exit -> flush header + ticks & return `0xFFFFFFFFu`
      have hpeq : st.prop = st.trl_end :=
        BitVec.eq_of_toNat_eq (Nat.le_antisymm hf_st.hinv.assign.prop_le
          (Nat.le_of_not_lt hc))
      have hret_exit : ∀ (tk : BitVec 32) (m_out : Mem 64),
          (K6MemA L kp (st.putHdr .ticks tk) ⋆ P) m_out →
          Q (0xFFFFFFFF#32, ()) m_out := by
        intro tk m_out hmt
        let hfT := fid_k6PropFrame_ticks hf_st tk
        exact hQ 0xFFFFFFFF#32 _ m_out hfT.hinv hfT.hsync hfT.hpres hfT.htrl_ge
          hfT.hold hfT.hnew (fun _ => hpeq)
          (fun h => absurd rfl h) (k6MemA_to_mem hmt).2
      fid_nogrp_np
      try dsimp only at hm'
      try rw [k6ShadowHdr_prep] at hm'
      c0_hfast
      all_goals
        try dsimp only at hm
        try rw [k6ShadowHdr_flush] at hm
        exact hret_exit _ m hm

end K6PropagateFid

end LeanQbe.T.Examples.Kissat.FullFidelityVivK6
