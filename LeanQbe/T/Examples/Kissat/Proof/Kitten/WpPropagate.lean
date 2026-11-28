/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.WpBtFlip

/-!
# Step-13 `Func.wp` Proof for `full_k6_propagate` (`9/14`, `Kissat.Proof.Kitten.WpPropagate`)

Certifies `full_k6_propagate_wp` (`step13K6PropagateSpec`) against
`Src.Kitten.full_k6_propagate_body` with `K6TailEq` preservation. Zero legacy `Full*` imports;
zero `@[expose]` on theorems/lemmas; `<= 100` cols; every decl `<= 450` LOC.
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
open LeanQbe.T.Examples.Kissat.Src.Kitten

open K6MemATactics K6PtrTactics
open scoped K6MemATactics K6PtrTactics

/-! ## 1. Propagation Frame & Pure Helpers -/

private structure K6PropFrame (L : K6Layout) (ks0 ks : K6State) : Prop where
  pres : K6PropPreserved ks0 ks
  tail : K6TailEq L ks0 ks
  te_ge : ks0.trl_end.toNat ≤ ks.trl_end.toNat
  old_trl : ∀ i < ks0.trl_end.toNat,
    ks.trl[i]? = ks0.trl[i]? ∧
    ks.lvlArr[(ks0.trl[i]?.getD 0#32).toNat / 2]? =
      ks0.lvlArr[(ks0.trl[i]?.getD 0#32).toNat / 2]? ∧
    ks.rsn[(ks0.trl[i]?.getD 0#32).toNat / 2]? =
      ks0.rsn[(ks0.trl[i]?.getD 0#32).toNat / 2]?
  new_trl : ∀ i, ks0.trl_end.toNat ≤ i → i < ks.trl_end.toNat →
    ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks0.lvl ∧
    ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ 0xFFFFFFFF#32

private theorem K6PropFrame.refl (L : K6Layout) (ks : K6State) : K6PropFrame L ks ks :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   k6TailEq_refl L ks, le_refl _, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ h1 h2 => by omega⟩

private theorem K6PropFrame.cast {L : K6Layout} {ks0 ks ks' : K6State}
    (h : K6PropFrame L ks0 ks) (htl : K6TailEq L ks ks')
    (h1 : ks'.nv = ks.nv := by rfl) (h2 : ks'.nc = ks.nc := by rfl)
    (h3 : ks'.lvl = ks.lvl := by rfl) (h4 : ks'.incons = ks.incons := by rfl)
    (h5 : ks'.alen = ks.alen := by rfl) (h6 : ks'.acap = ks.acap := by rfl)
    (h7 : ks'.nassump = ks.nassump := by rfl) (h8 : ks'.status = ks.status := by rfl)
    (h9 : ks'.openCnt = ks.openCnt := by rfl) (h10 : ks'.max_v = ks.max_v := by rfl)
    (h11 : ks'.max_orig = ks.max_orig := by rfl) (h12 : ks'.max_cl = ks.max_cl := by rfl)
    (h13 : ks'.neq = ks.neq := by rfl) (h14 : ks'.assump = ks.assump := by rfl)
    (h15 : ks'.trl_end = ks.trl_end := by rfl) (h16 : ks'.trl = ks.trl := by rfl)
    (h17 : ks'.lvlArr = ks.lvlArr := by rfl) (h18 : ks'.rsn = ks.rsn := by rfl) :
    K6PropFrame L ks0 ks' :=
  ⟨⟨h1.trans h.pres.nv, h2.trans h.pres.nc, h3.trans h.pres.lvl, h4.trans h.pres.incons,
    h5.trans h.pres.alen, h6.trans h.pres.acap, h7.trans h.pres.nassump, h8.trans h.pres.status,
    h9.trans h.pres.openCnt, h10.trans h.pres.max_v, h11.trans h.pres.max_orig,
    h12.trans h.pres.max_cl, h13.trans h.pres.neq, h14.trans h.pres.assump⟩,
   k6TailEq_trans h.tail htl, h15 ▸ h.te_ge,
   fun i hi => by rw [h16, h17, h18]; exact h.old_trl i hi,
   fun i hlo hhi => by rw [h15] at hhi; rw [h16, h17, h18]; exact h.new_trl i hlo hhi⟩

private theorem K6PropFrame.trans {L : K6Layout} {ks0 ks1 ks2 : K6State}
    (h12 : K6PropFrame L ks0 ks1) (h23 : K6PropFrame L ks1 ks2) : K6PropFrame L ks0 ks2 :=
  ⟨⟨h23.pres.nv.trans h12.pres.nv, h23.pres.nc.trans h12.pres.nc, h23.pres.lvl.trans h12.pres.lvl,
    h23.pres.incons.trans h12.pres.incons, h23.pres.alen.trans h12.pres.alen,
    h23.pres.acap.trans h12.pres.acap, h23.pres.nassump.trans h12.pres.nassump,
    h23.pres.status.trans h12.pres.status, h23.pres.openCnt.trans h12.pres.openCnt,
    h23.pres.max_v.trans h12.pres.max_v, h23.pres.max_orig.trans h12.pres.max_orig,
    h23.pres.max_cl.trans h12.pres.max_cl, h23.pres.neq.trans h12.pres.neq,
    h23.pres.assump.trans h12.pres.assump⟩,
   k6TailEq_trans h12.tail h23.tail, Nat.le_trans h12.te_ge h23.te_ge,
   fun i hi => by
     have h1 := h12.old_trl i hi; have h2 := h23.old_trl i (Nat.lt_of_lt_of_le hi h12.te_ge)
     rw [h1.1] at h2; exact ⟨h2.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩,
   fun i hlo hhi => by
     by_cases h1 : i < ks1.trl_end.toNat
     · have hn := h12.new_trl i hlo h1; have ho := h23.old_trl i h1
       rw [ho.1, ho.2.1, ho.2.2]; exact hn
     · have hn := h23.new_trl i (by omega) hhi; rw [h12.pres.lvl] at hn; exact hn⟩

private theorem k6PropAssign_frame {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) {lit rsn : BitVec 32} (hlit : lit.toNat < 2 * ks.nv.toNat)
    (hun : ks.vals[lit.toNat]? = some 0#32) (hrsn_ne : rsn ≠ 0xFFFFFFFF#32) :
    K6PropFrame L ks (k6AssignStep ks lit rsn) := by
  have hm := L.hmaxV; have hnv := hinv.clauses.nv_le
  have hte_lt := k6_trl_end_lt_of_unassigned hinv.shapes hnv hinv.assign hlit (by simp [hun])
  have hv_eq := (k6_bv32_div2_lt hlit).1
  have hte1 : (ks.trl_end + 1#32).toNat = ks.trl_end.toNat + 1 := by bv_omega
  have hnot_trl : ∀ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := by
    intro i hi heq; have hnz := (hinv.assign.vals_nz_iff_trl lit.toNat hlit).mpr ⟨i, hi, heq⟩
    simp [hun] at hnz
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    k6TailEq_of_k6AssignStep lit rsn hlit,
    by change ks.trl_end.toNat ≤ (ks.trl_end + 1#32).toNat; omega,
    fun i hi => by
      have hne := hnot_trl i hi
      exact ⟨List.getElem?_set_ne (by omega),
        by dsimp only [k6AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne (Ne.symm hne),
        by dsimp only [k6AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne (Ne.symm hne)⟩,
    fun i hlo hhi => by
      change i < (ks.trl_end + 1#32).toNat at hhi; rw [hte1] at hhi
      have hie : i = ks.trl_end.toNat := by omega
      subst hie; dsimp only [k6AssignStep]
      rw [List.getElem?_set_self (by rw [hinv.shapes.trl_len]; omega), Option.getD_some, hv_eq,
        List.getElem?_set_self (by rw [hinv.shapes.lvlArr_len]; omega),
        List.getElem?_set_self (by rw [hinv.shapes.rsn_len]; omega),
        Option.getD_some, Option.getD_some]
      exact ⟨rfl, hrsn_ne⟩⟩

private theorem k6_unlinked_clause_falsified {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks : K6State} (hinv : K6Inv L P ks) {cid slot : Nat} (hcid : cid < ks.nc.toNat)
    (hslot : slot < 2) {nl other : BitVec 32} (hnl_f : ks.vals[nl.toNat]? = some 2#32)
    (hslot_eq : (ks.arena[k6ClauseOff ks cid + slot]?.getD 0#32).toNat = nl.toNat)
    (hoth_eq : other.toNat = (ks.arena[k6ClauseOff ks cid + (slot ^^^ 1)]?.getD 0#32).toNat)
    (hrest : ∀ q, 2 ≤ q → q < k6ClauseSize ks cid →
      ks.vals[(ks.arena[k6ClauseOff ks cid + q]?.getD 0#32).toNat]? = some 2#32) :
    ∀ x ∈ k6ClauseLits ks cid, x ≠ other.toNat → ks.vals[x]? = some 2#32 := by
  intro x hx hne
  have hbd : k6ClauseOff ks cid + k6ClauseSize ks cid ≤ ks.arena.length := by
    rw [hinv.shapes.arena_len]; have := (hinv.clauses.cl_wf cid hcid).2.1
    have := hinv.clauses.alen_le; omega
  obtain ⟨q, hq, rfl⟩ := (k6_mem_clauseLits_iff hbd).mp hx
  by_cases hq2 : q < 2
  · by_cases hqs : q = slot
    · subst hqs; rw [hslot_eq]; exact hnl_f
    · have hqo : q = slot ^^^ 1 := by
        rcases (show slot = 0 ∨ slot = 1 by omega) with rfl | rfl <;> (simp; omega)
      subst hqo; exact absurd hoth_eq.symm hne
  · exact hrest q (by omega) hq

private theorem k6_prop_vals_dom_zero {L : K6Layout} {P : (Nat → Bool) → Prop} {ksW : K6State}
    (hinvW : K6Inv L P ksW) {l : Nat} (hl_nv : l < 2 * ksW.nv.toNat) (hl_mv : l < sz2V L)
    (hne1 : ksW.vals[l]? ≠ some 1#32) (hne2 : ksW.vals[l]? ≠ some 2#32) :
    ksW.vals[l]? = some 0#32 := by
  rcases hinvW.assign.vals_dom l hl_nv with h0 | h1 | h2
  · exact k6_vals_some hinvW.shapes hl_mv h0
  · exact absurd (k6_vals_some hinvW.shapes hl_mv h1) hne1
  · exact absurd (k6_vals_some hinvW.shapes hl_mv h2) hne2

private theorem k6_prop_confl_post {ks : K6State}
    {w0 : Nat} {tgt : BitVec 32} (hdiv : (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat = w0 / 2)
    (hcid_lt : w0 / 2 < ks.nc.toNat) (htgt2 : ks.vals[tgt.toNat]? = some 2#32)
    (hfals : ∀ x ∈ k6ClauseLits ks (w0 / 2), x ≠ tgt.toNat → ks.vals[x]? = some 2#32) :
    BitVec.ofNat 32 w0 >>> (1 : Nat) ≠ 0xFFFFFFFF#32 →
    (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat < ks.nc.toNat ∧
      ∀ x ∈ k6ClauseLits ks (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat, ks.vals[x]? = some 2#32 :=
  fun _ => by
    rw [hdiv]; refine ⟨hcid_lt, fun x hx => ?_⟩
    by_cases hxt : x = tgt.toNat
    · rw [hxt]; exact htgt2
    · exact hfals x hx hxt

private theorem k6_prop_assign_step_pres {L : K6Layout} {P : (Nat → Bool) → Prop} {ks0 ks : K6State}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks) (hfr : K6PropFrame L ks0 ks)
    {cid_bv tgt : BitVec 32} {cid : Nat} (hcid_eq : cid_bv.toNat = cid)
    (hcid_lt : cid < ks.nc.toNat) (hcid_ne_ff : cid_bv ≠ 0xFFFFFFFF#32)
    (htgt_nv : tgt.toNat < 2 * ks.nv.toNat) (htgt_mem : tgt.toNat ∈ k6ClauseLits ks cid)
    (htgt0 : ks.vals[tgt.toNat]? = some 0#32)
    (hfals : ∀ x ∈ k6ClauseLits ks cid, x ≠ tgt.toNat → ks.vals[x]? = some 2#32) :
    ks.trl_end.toNat < ks.nv.toNat ∧ K6Inv L P (k6AssignStep ks tgt cid_bv) ∧
    K6TrailSynced (k6AssignStep ks tgt cid_bv) ∧ K6PropFrame L ks0 (k6AssignStep ks tgt cid_bv) :=
      by
  have hsh := hinv.shapes; have hnv := hinv.clauses.nv_le
  have hwf := hinv.clauses.cl_wf cid hcid_lt
  have hte_lt := k6_trl_end_lt_of_unassigned hsh hnv hinv.assign htgt_nv (by rw [htgt0]; rfl)
  obtain ⟨hinvB, hsyncB⟩ := k6AssignStep_preserves_inv hinv hsync htgt_nv htgt0
    (fun hl0 => SemEntails.unit_of_falsified hwf.2.2.2 fun x hx hne =>
      (k6_falsified_lvl0_entails hinv hl0 (hwf.2.2.1 x hx) (hfals x hx hne)).2)
    (fun _ hrs => absurd hrs hcid_ne_ff)
    (Or.inr ⟨by rw [hcid_eq]; exact hcid_lt, by rw [hcid_eq]; exact htgt_mem,
      fun x hx hne => by
        rw [hcid_eq] at hx
        exact k6_falsified_to_trail hinv.assign hsync (hwf.2.2.1 x hx) (hfals x hx hne)⟩)
  exact ⟨hte_lt, hinvB, hsyncB, hfr.trans (k6PropAssign_frame hinv htgt_nv htgt0 hcid_ne_ff)⟩

private theorem k6_prop_prv_lt {L : K6Layout} {ksW : K6State} {l : Nat}
    {chains : List (List Nat)} {done todo : List Nat} {prev w : BitVec 32}
    (hwc : K6WChainCursor ksW l chains done todo prev w) (hwn_len : ksW.wnext.length = 2 * L.maxCl)
    (hp : prev ≠ 0xFFFFFFFF#32) : prev.toNat < sz2Cl L := by
  rcases hwc.prev_rel with ⟨_, hpf, _⟩ | ⟨_, u, _, hp_eq, hu_len, _⟩
  · exact absurd hpf hp
  · rw [hwn_len] at hu_len; have hm_b := L.hmaxV
    have hu32 : u < 2 ^ 32 := by unfold K6Layout.maxCl at hu_len; omega
    rw [hp_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu32]; unfold sz2Cl; exact hu_len

private theorem k6_prop_sh_bv {w0 : Nat} (hw : w0 < 2 ^ 32) :
    (BitVec.ofNat 32 w0 >>> 1#32).toNat = w0 / 2 := by
  change ((BitVec.ofNat 32 w0).toNat >>> (1#32 : BitVec 32).toNat) = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]; simp [Nat.shiftRight_eq_div_pow]

private theorem k6_prop_ticks_done {L : K6Layout} {P : (Nat → Bool) → Prop} {ks0 ksO : K6State}
    {tk' : BitVec 32} (hinvO : K6Inv L P ksO) (hfrO : K6PropFrame L ks0 ksO) :
    K6Inv L P (ksO.putHdr .ticks tk') ∧ K6PropFrame L ks0 (ksO.putHdr .ticks tk') :=
  ⟨k6AddTicks_preserves_inv hinvO tk',
   hfrO.cast (k6TailEq_of_putHdr_ne_nv (f := .ticks) (by decide) tk')⟩

/-! ## 2. Standalone Memory-State & Inline-Assign / Flush Helpers -/

private def k6PropMemState (ks0 ks : K6State) : K6State :=
  { ks with prop := ks0.prop, trl_end := ks0.trl_end, unass := ks0.unass }

private theorem k6_prop_reloc_mem {L : K6Layout}
    {ks0 ksW : K6State} {lit repl nxt prev : BitVec 32} {w0 : Nat} {ri : BitVec 32}
    (hw_tn : (BitVec.ofNat 32 w0).toNat = w0)
    (hw_sh_bv : (BitVec.ofNat 32 w0 >>> 1#32).toNat = w0 / 2)
    (hslot_cap : k6ClauseOff ksW (w0 / 2) + w0 % 2 < L.acap)
    (hri_cap : k6ClauseOff ksW (w0 / 2) + ri.toNat < L.acap)
    (hsb : (BitVec.ofNat 32 w0 &&& (1 : BitVec 32)) = BitVec.ofNat 32 (w0 % 2))
    (hnxt : ksW.wnext[w0]?.getD 0#32 = nxt) :
    let ar1 := (ksW.arena.set (k6ClauseOff ksW (w0 / 2) + w0 % 2) repl).set
      (k6ClauseOff ksW (w0 / 2) + ri.toNat) (BitVec.ofNat 32 (lit ^^^ 1#32).toNat)
    let wh1 := if prev = 0xFFFFFFFF#32 then ksW.whead.set (lit ^^^ 1#32).toNat nxt else ksW.whead
    let wn1 := if prev = 0xFFFFFFFF#32 then ksW.wnext else ksW.wnext.set prev.toNat nxt
    let tgt := k6PropMemState ks0 { ksW with arena := ar1, whead := wh1, wnext := wn1 }
    (prev = 0xFFFFFFFF#32 →
      (((k6PropMemState ks0 ksW).putArr .arena
        (ksW.clOff[(BitVec.ofNat 32 w0 >>> 1#32).toNat]?.getD 0#32 +
          (BitVec.ofNat 32 w0 &&& 1#32)).toNat repl).putArr .arena
          (ksW.clOff[(BitVec.ofNat 32 w0 >>> 1#32).toNat]?.getD 0#32 + ri).toNat
          (lit ^^^ 1#32)).putArr .whead (lit ^^^ 1#32).toNat
          (ksW.wnext[(BitVec.ofNat 32 w0).toNat]?.getD 0#32) = tgt) ∧
    (prev ≠ 0xFFFFFFFF#32 →
      (((k6PropMemState ks0 ksW).putArr .arena
        (ksW.clOff[(BitVec.ofNat 32 w0 >>> 1#32).toNat]?.getD 0#32 +
          (BitVec.ofNat 32 w0 &&& 1#32)).toNat repl).putArr .arena
          (ksW.clOff[(BitVec.ofNat 32 w0 >>> 1#32).toNat]?.getD 0#32 + ri).toNat
          (lit ^^^ 1#32)).putArr .wnext prev.toNat
          (ksW.wnext[(BitVec.ofNat 32 w0).toNat]?.getD 0#32) = tgt) := by
  intro ar1 wh1 wn1 tgt
  refine ⟨fun hp => ?_, fun hp => ?_⟩ <;>
    (dsimp only [tgt, wh1, wn1, k6PropMemState]; simp only [hp, ↓reduceIte]
     rw [hw_tn, hnxt]; k6_ext <;> first | rfl |
       exact k6_reloc_arena_slot hw_sh_bv hw_sh_bv (by simp) hsb hslot_cap hri_cap)

private theorem k6_prop_cast_flush {L : K6Layout} {kPtr : BitVec 64} {R : Mem 64 → Prop}
    {m : Mem 64} {ks0 ks ks' : K6State} {pr : BitVec 32}
    (hm : (K6MemA L kPtr ks' ⋆ R) m) (hpr : pr = ks.prop)
    (heq : ks' = (((k6PropMemState ks0 ks).putHdr .prop pr).putHdr
      .trl_end ks.trl_end).putHdr .unass ks.unass) :
    (K6MemA L kPtr ks ⋆ R) m :=
  Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) m)
    (heq.trans (by subst hpr; dsimp only [k6PropMemState, K6State.putHdr]))) hm

private theorem k6_prop_c0_other {ks0 ksW : K6State} {w0 : Nat} {rhs : BitVec 32}
    (hr : ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32 +
      (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32))).toNat]?.getD 0#32 = rhs) :
    (k6PropMemState ks0 ksW).arena[((k6PropMemState ks0 ksW).clOff[
      (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32 +
      (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32))).toNat]?.getD 0#32 = rhs := hr

private theorem k6_prop_c0_other_bv {ks0 ksW : K6State} {w0 : Nat} {rhs : BitVec 32}
    (hr : ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32 +
      (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32))).toNat]?.getD 0#32 = rhs) :
    (k6PropMemState ks0 ksW).arena[((k6PropMemState ks0 ksW).clOff[
      (BitVec.ofNat 32 w0 >>> 1#32).toNat]?.getD 0#32 +
      (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32)).toNat]?.getD 0#32 = rhs := hr

private theorem k6PropMemState_assign {ks0 ksW : K6State} {tgt cid fl' : BitVec 32}
    {v l1 l2 : Nat} (hv : v = (tgt >>> 1).toNat) (hl1 : l1 = tgt.toNat)
    (hl2 : l2 = (tgt ^^^ 1#32).toNat) (hlvl : ksW.lvl = ks0.lvl)
    (hfl : fl' = if tgt &&& 1#32 ≠ 0#32 then
      ksW.flags[(tgt >>> 1).toNat]?.getD 0#32 ||| 1#32 else
      ksW.flags[(tgt >>> 1).toNat]?.getD 0#32 &&& ~~~1#32) :
    ((((((k6PropMemState ks0 ksW).putArr .vals l1 1#32).putArr .vals l2 2#32).putArr
      .lvlArr v ks0.lvl).putArr .rsn v cid).putArr .trl ksW.trl_end.toNat tgt).putArr
      .flags v fl' =
    k6PropMemState ks0 (k6AssignStep ksW tgt cid) := by
  subst hv hl1 hl2 hfl; rw [← hlvl]; dsimp only [k6PropMemState, K6State.putArr, k6AssignStep]

private theorem k6_prop_flush_finish {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks0 ksF : K6State} {kPtr : BitVec 64} {R : Mem 64 → Prop} {m' : Mem 64}
    {Q : Post [i32]} {confl ret : BitVec 32} (tk' : BitVec 32)
    (hret : ∀ (confl : BitVec 32) (ks : K6State) (m : Mem 64),
      K6Inv L P ks → K6TrailSynced ks → K6PropFrame L ks0 ks →
      (confl = 0xFFFFFFFF#32 → ks.prop = ks.trl_end) →
      (confl ≠ 0xFFFFFFFF#32 → confl.toNat < ks.nc.toNat ∧
        ∀ l ∈ k6ClauseLits ks confl.toNat, ks.vals[l]? = some 2#32) →
      (K6Mem L kPtr ks ⋆ R) m → Q (confl, ()) m)
    (hinvF : K6Inv L P ksF) (hsyncF : K6TrailSynced ksF) (hfrF : K6PropFrame L ks0 ksF)
    (h1 : ret = 0xFFFFFFFF#32 → ksF.prop = ksF.trl_end)
    (h2 : ret ≠ 0xFFFFFFFF#32 → ret.toNat < ksF.nc.toNat ∧
      ∀ l ∈ k6ClauseLits ksF ret.toNat, ksF.vals[l]? = some 2#32)
    (hconfl : confl = ret) (hmA : (K6MemA L kPtr (ksF.putHdr .ticks tk') ⋆ R) m') :
    Q (confl, ()) m' := by
  subst hconfl
  obtain ⟨hinvT, hfrT⟩ := k6_prop_ticks_done (tk' := tk') hinvF hfrF
  exact hret _ (ksF.putHdr .ticks tk') m' hinvT
    (by dsimp only [K6State.putHdr]; exact hsyncF) hfrT
    (fun h => by dsimp only [K6State.putHdr]; exact h1 h)
    (fun h => by dsimp only [K6State.putHdr]; exact h2 h)
    (k6MemA_to_mem hmA).2

open Lean Elab Tactic in
local elab "k6_prop_do_flush" hret:ident ksF:term:max
    hinvF:term:max hsyncF:term:max hfrF:term:max h1:term:max h2:term:max
    hpr:term:max : tactic => do
  let hm := mkIdent `hm
  let lId := mkIdent `L; let kPtr := mkIdent `kPtr; let rId := mkIdent `R
  evalTactic (← `(tactic| (
    c0_hsteps_nogrp
    have $hm:ident := k6_prop_cast_flush $hm ($hpr) (Eq.refl _)
    refine wp_join_state (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
      (fun _ m' => (K6MemA $lId $kPtr $ksF ⋆ $rId) m') ?_ ?_
    · rintro _ tk m_f hm_f; c0_hsteps!
      exact k6_prop_flush_finish tk $hret $hinvF $hsyncF $hfrF $h1 $h2 rfl $hm
    · intro Jt hJt; c0_hsteps! <;> exact hJt _ _ $hm)))

open Lean Elab Tactic in
local elab "k6_prop_do_assign" ksM:term:max tgt:term:max cid:term:max htgt_nv:term:max
    _htgt_mv2:term:max hte_lt:term:max hlvl:term:max hfl_false:term:max hJb_step:term:max :
    tactic => do
  let hm := mkIdent `hm; let ks0 := mkIdent `ks0
  let mB := mkIdent `mB; let hmB := mkIdent `hmB
  let lId := mkIdent `L; let kPtr := mkIdent `kPtr; let rId := mkIdent `R
  evalTactic (← `(tactic| (
    have hnvM := ($hfl_false).1
    have hv_lt_sz : ($tgt >>> (1 : Nat)).toNat < szV $lId := by
      unfold szV; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
      exact Nat.div_lt_of_lt_mul
        (Nat.lt_of_lt_of_le $htgt_nv (Nat.mul_le_mul_left 2 ($hfl_false).1))
    have hnxor_lt : ($tgt ^^^ 1#32).toNat < sz2V $lId :=
      Nat.lt_of_lt_of_le (k6_bv32_xor1_lt $htgt_nv).2
        (by unfold sz2V; have := ($hfl_false).1; omega)
    have hte_sz : ($ksM).trl_end.toNat < szV $lId := by
      unfold szV; refine Nat.lt_of_lt_of_le (by exact $hte_lt) ?_
      try dsimp +zetaDelta only [K6State.putArr]
      exact ($hfl_false).1
    refine wp_join_state (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
      (fun p => (p.1, p.2, ()))
      (fun p mB' => p.1 = (k6AssignStep $ksM $tgt $cid).trl_end ∧
        p.2 = (k6AssignStep $ksM $tgt $cid).unass ∧
        (K6MemA $lId $kPtr (k6PropMemState $ks0 (k6AssignStep $ksM $tgt $cid)) ⋆ $rId) mB')
      ?_ ?_
    focus
      rintro _ ⟨_, _⟩ $mB:ident ⟨hpr_te, hpr_un, $hmB:ident⟩; rw [hpr_te, hpr_un]; exact $hJb_step
    intro Jb hJb; c0_hsplit
    focus
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i32]) (α := BitVec 32) (fun u => (u, ()))
        (fun u' mU => u' = (k6AssignStep $ksM $tgt $cid).unass ∧
          (K6MemA $lId $kPtr ((((((k6PropMemState $ks0 $ksM).putArr .vals
            ($tgt).toNat 1#32).putArr .vals ($tgt ^^^ 1#32).toNat 2#32).putArr .lvlArr
              ($tgt >>> 1#32).toNat ($ks0).lvl).putArr .rsn
              ($tgt >>> 1#32).toNat $cid).putArr .trl ($ksM).trl_end.toNat $tgt) ⋆ $rId) mU)
        ?_ ?_
      · rintro _ un' mU ⟨hun', hmU⟩; subst hun'; c0_hsteps_nogrp
        refine wp_join_state (ts := [i32]) (α := BitVec 32) (fun f => (f, ()))
          (fun fl' mFl => fl' = (if $tgt &&& 1#32 ≠ 0#32 then
              ($ksM).flags[($tgt >>> 1).toNat]?.getD 0#32 ||| 1#32
            else ($ksM).flags[($tgt >>> 1).toNat]?.getD 0#32 &&& ~~~1#32) ∧ mFl = mU) ?_ ?_
        · rintro _ fl' mFl ⟨hfl, hmfl⟩; subst hfl hmfl; c0_hsteps!
          have hmB_out := Eq.mp (congrArg (fun x => (K6MemA $lId $kPtr x ⋆ $rId) _)
            (k6PropMemState_assign (ks0 := $ks0) (ksW := $ksM) (tgt := $tgt) (cid := $cid)
              (Eq.refl _) (Eq.refl _) (Eq.refl _) $hlvl (Eq.refl _))) $hm
          exact hJb ((k6AssignStep $ksM $tgt $cid).trl_end,
            (k6AssignStep $ksM $tgt $cid).unass) _ ⟨Eq.refl _, Eq.refl _, hmB_out⟩
        · intro Jf hJf; c0_hsteps!
          · have hne : ($tgt &&& 1#32) ≠ 0#32 := ‹_›
            exact hJf _ _ ⟨(by
              dsimp only [K6State.putArr, k6PropMemState]; simp [hne]
              try (rw [BitVec.toNat_and]; exact Eq.refl _)), rfl⟩
          · have heq : ($tgt &&& 1#32) = 0#32 := ‹_›
            exact hJf _ _ ⟨(by
              dsimp only [K6State.putArr, k6PropMemState]; simp [heq]
              try (rw [BitVec.toNat_and]; exact Eq.refl _)), rfl⟩
      · intro Ju hJu; c0_hsteps!
        · have hup : 0 < ($ksM).unass.toNat := by
            try dsimp +zetaDelta only [K6State.putArr]
            simp only [Nat.zero_mod] at *; bv_omega
          exact hJu _ _ ⟨by dsimp only [k6AssignStep]; simp [hup]; all_goals exact Eq.refl _, $hm⟩
        · have hu0 : ¬ 0 < ($ksM).unass.toNat := by
            try dsimp +zetaDelta only [K6State.putArr]
            simp only [Nat.zero_mod] at *; bv_omega
          exact hJu _ _ ⟨by dsimp only [k6AssignStep]; simp [hu0]; all_goals exact Eq.refl _,
            $hm⟩)))

private theorem k6_prop_other_bounds {L : K6Layout} {ksW : K6State} {w0 : Nat}
    (hac_b : L.acap < dimacsBound) (hw_sh1 : (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat = w0 / 2)
    (hw_mod2 : (BitVec.ofNat 32 w0 &&& 1#32).toNat = w0 % 2)
    (har_ok : ∀ idx, idx < k6ClauseSize ksW (w0 / 2) → k6ClauseOff ksW (w0 / 2) + idx < L.acap ∧
      (ksW.arena[k6ClauseOff ksW (w0 / 2) + idx]?.getD 0#32).toNat < 2 * ksW.nv.toNat)
    (hsz_ge : 2 ≤ k6ClauseSize ksW (w0 / 2)) :
    (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
        (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat < L.acap ∧
      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
        (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat < 2 ^ 32 := by
  have hcap : (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
      (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat < L.acap := by
    rw [hw_sh1, BitVec.toNat_xor, hw_mod2, show (1#32 : BitVec 32).toNat = 1 from rfl]
    rcases Nat.mod_two_eq_zero_or_one w0 with h0 | h1
    · rw [h0, show (0 ^^^ 1) = 1 from rfl]; exact (har_ok _ (by omega)).1
    · rw [h1, show (1 ^^^ 1) = 0 from rfl]; exact (har_ok _ (by omega)).1
  exact ⟨hcap, by unfold dimacsBound at hac_b; omega⟩

private theorem k6_prop_off_add_lt {L : K6Layout} {ksW : K6State} {w0 : Nat} {j : BitVec 32}
    (hac_b : L.acap < dimacsBound) (hw_sh1 : (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat = w0 / 2)
    (hcap : k6ClauseOff ksW (w0 / 2) + j.toNat < L.acap) :
    (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat + j.toNat < 2 ^ 32 ∧
      (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat + j.toNat < L.acap :=
        by
  rw [hw_sh1]; unfold dimacsBound at hac_b; unfold k6ClauseOff at hcap; exact ⟨by omega, hcap⟩

private theorem k6_ptr_c_shl (L : K6Layout) (kPtr : BitVec 64) {a b sh : Nat}
    (hsh : sh ≤ 3) (ha : a ≤ 38 * L.maxV + 32) (hab : b = a + 2 ^ sh * L.maxV) :
    kPtr + BitVec.ofNat 64 (4 * a) + BitVec.setWidth 64 (L.mv32 <<< sh) * 4 =
      kPtr + BitVec.ofNat 64 (4 * b) := by
  subst hab; have hmax := L.hmaxV.2
  rw [BitVec.add_assoc]; congr 1
  rcases (by omega : sh = 0 ∨ sh = 1 ∨ sh = 2 ∨ sh = 3) with rfl | rfl | rfl | rfl <;>
    (unfold K6Layout.mv32; apply BitVec.eq_of_toNat_eq; bv_omega)

private theorem k6_ptr_p0 (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + BitVec.ofNat 64 32 * 4 = kPtr + BitVec.ofNat 64 (4 * L.oLvl) := by simp [K6Layout.oLvl]
private theorem k6_ptr_p1 (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + BitVec.ofNat 64 (4 * L.oLvl) + BitVec.setWidth 64 L.mv32 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oRsn) := by
  simpa using k6_ptr_c_shl L kPtr (Nat.zero_le 3) (by simp [K6Layout.oLvl])
    (by simp [K6Layout.oLvl, K6Layout.oRsn])
private theorem k6_ptr_p2 (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + BitVec.ofNat 64 (4 * L.oRsn) + BitVec.setWidth 64 (L.mv32 <<< 2) * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oTrl) :=
  k6_ptr_c_shl L kPtr (by decide) (by simp [K6Layout.oRsn]; omega)
    (by simp [K6Layout.oRsn, K6Layout.oTrl]; omega)
private theorem k6_ptr_p3 (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + BitVec.ofNat 64 (4 * L.oTrl) + BitVec.setWidth 64 L.mv32 * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oFlags) := by
  simpa using k6_ptr_c_shl L kPtr (Nat.zero_le 3) (by simp [K6Layout.oTrl]; omega)
    (by simp [K6Layout.oTrl, K6Layout.oFlags]; omega)
private theorem k6_ptr_p4 (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + BitVec.ofNat 64 (4 * L.oFlags) + BitVec.setWidth 64 (L.mv32 <<< 2) * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oVals) :=
  k6_ptr_c_shl L kPtr (by decide) (by simp [K6Layout.oFlags]; omega)
    (by simp [K6Layout.oFlags, K6Layout.oVals]; omega)
private theorem k6_ptr_p5 (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + BitVec.ofNat 64 (4 * L.oVals) + BitVec.setWidth 64 (L.mv32 <<< 1) * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oWHead) :=
  k6_ptr_c_shl L kPtr (by decide) (by simp [K6Layout.oVals]; omega)
    (by simp [K6Layout.oVals, K6Layout.oWHead]; omega)
private theorem k6_ptr_p6 (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + BitVec.ofNat 64 (4 * L.oWHead) + BitVec.setWidth 64 (L.mv32 <<< 1) * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oWNext) :=
  k6_ptr_c_shl L kPtr (by decide) (by simp [K6Layout.oWHead]; omega)
    (by simp [K6Layout.oWHead, K6Layout.oWNext]; omega)
private theorem k6_ptr_p7 (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + BitVec.ofNat 64 (4 * L.oWNext) + BitVec.setWidth 64 (L.mv32 <<< 3) * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oWBlit) :=
  k6_ptr_c_shl L kPtr (by decide) (by simp [K6Layout.oWNext]; omega)
    (by simp [K6Layout.oWNext, K6Layout.oWBlit]; omega)
private theorem k6_ptr_p8 (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + BitVec.ofNat 64 (4 * L.oWBlit) + BitVec.setWidth 64 (L.mv32 <<< 3) * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oClOff) :=
  k6_ptr_c_shl L kPtr (by decide) (by simp [K6Layout.oWBlit]; omega)
    (by simp [K6Layout.oWBlit, K6Layout.oClOff]; omega)
private theorem k6_ptr_p9 (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + BitVec.ofNat 64 (4 * L.oClOff) + BitVec.setWidth 64 (L.mv32 <<< 2) * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oClSz) :=
  k6_ptr_c_shl L kPtr (by decide) (by simp [K6Layout.oClOff]; omega)
    (by simp [K6Layout.oClOff, K6Layout.oClSz]; omega)
private theorem k6_ptr_p10 (L : K6Layout) (kPtr : BitVec 64) :
    kPtr + BitVec.ofNat 64 (4 * L.oClSz) + BitVec.setWidth 64 (L.mv32 <<< 2) * 4 =
      kPtr + BitVec.ofNat 64 (4 * L.oArena) :=
  k6_ptr_c_shl L kPtr (by decide) (by simp [K6Layout.oClSz]; omega)
    (by simp [K6Layout.oClSz, K6Layout.oArena]; omega)

/-! ## 3. `full_k6_propagate_wp` (`9/14`) -/

/-- `9/14`: Parametric `Func.wp` proof for `full_k6_propagate`. -/
theorem full_k6_propagate_wp (Γ : Env) :
    ∀ args m Q X, step13K6PropagateSpec args m Q X →
      Func.wp Γ full_k6_propagate_body args m Q X := by
  rintro ⟨kPtr, ⟨⟩⟩ m Q X ⟨L, P, ks0, R, hinv0, hsync0, hm0, hQ⟩
  have hm_b := L.hmaxV; have hac_b := L.hacap
  have hmv0 : ks0.max_v = L.mv32 := hinv0.clauses.max_v_eq
  have hmA0 := k6Mem_to_amem hinv0.shapes hm0; clear hm0
  have hret : ∀ (confl : BitVec 32) (ksF : K6State) (mF : Mem 64),
      K6Inv L P ksF → K6TrailSynced ksF → K6PropFrame L ks0 ksF →
      (confl = 0xFFFFFFFF#32 → ksF.prop = ksF.trl_end) →
      (confl ≠ 0xFFFFFFFF#32 → confl.toNat < ksF.nc.toNat ∧
        ∀ l ∈ k6ClauseLits ksF confl.toNat, ksF.vals[l]? = some 2#32) →
      (K6Mem L kPtr ksF ⋆ R) mF → Q (confl, ()) mF := fun confl ksF mF hi hs hf h1 h2 hmF =>
    hQ confl ksF mF hi hs hf.pres hf.tail hf.te_ge hf.old_trl hf.new_trl h1 h2 hmF
  c0_hsteps_nogrp
  rw [hmv0, k6_ptr_p0, k6_ptr_p1, k6_ptr_p2, k6_ptr_p3, k6_ptr_p4, k6_ptr_p5,
    k6_ptr_p6, k6_ptr_p7, k6_ptr_p8, k6_ptr_p9, k6_ptr_p10]
  refine wp_while_state (ts := [i32, i32, i32, i64]) (α := BitVec 64 × K6State)
    (fun st => (st.2.prop, st.2.trl_end, st.2.unass, st.1, ()))
    (fun st => ks0.nv.toNat - st.2.prop.toNat)
    (fun st mO => K6Inv L P st.2 ∧ K6TrailSynced st.2 ∧ K6PropFrame L ks0 st.2 ∧
      (K6MemA L kPtr (k6PropMemState ks0 st.2) ⋆ R) mO) ?_ ?_
  · intro J hJ
    exact wp_jump_state (proj := fun st : BitVec 64 × K6State =>
      (st.2.prop, st.2.trl_end, st.2.unass, st.1, ())) (0#64, ks0) rfl
      (hJ (0#64, ks0) m ⟨hinv0, hsync0, K6PropFrame.refl L ks0, hmA0⟩)
  · rintro J ⟨ticksO, ksO⟩ mO ⟨hinvO, hsyncO, hfrO, hmO⟩ ihO
    dsimp only at hinvO hsyncO hfrO hmO ⊢
    have hnvO := hinvO.clauses.nv_le
    c0_hsplit
    · have hp_lt : ksO.prop.toNat < ksO.trl_end.toNat := by bv_omega
      have hp_mv : ksO.prop.toNat < szV L := by
        have := hinvO.assign.trl_end_le; unfold szV; omega
      let pO := ksO.prop; let lit := ksO.trl[pO.toNat]?.getD 0#32
      have hnl_bn : BitVec.ofNat 32 (lit ^^^ 1#32).toNat = lit ^^^ 1#32 := by simp
      have hlit_lt : lit.toNat < 2 * ksO.nv.toNat :=
        hinvO.assign.trl_lt lit.toNat (k6_mem_trailLits_of_lt hp_lt
          (by rw [hinvO.shapes.trl_len]; have := hinvO.assign.trl_end_le; omega))
      obtain ⟨hnl_eq, hnl_lt⟩ := k6_bv32_xor1_lt hlit_lt
      have hnl_mv2 : (lit ^^^ 1#32).toNat < sz2V L := by unfold sz2V; omega
      have hp1_eq : (pO + 1#32).toNat = pO.toNat + 1 := by dsimp only [pO]; bv_omega
      let ks1 := ksO.putHdr .prop (pO + 1#32)
      have hinv1 : K6Inv L P ks1 := ⟨hinvO.shapes.putHdr .prop _, k6ClausesOk_cast hinvO.clauses,
        by dsimp only [ks1, K6State.putHdr]; exact hinvO.watches,
        { hinvO.assign with
          prop_le := by dsimp only [ks1, K6State.putHdr]; rw [hp1_eq]; exact hp_lt },
        by dsimp only [ks1, K6State.putHdr]; exact hinvO.reasons⟩
      have hsync1 : K6TrailSynced ks1 := k6TrailSynced_cast hsyncO
      have hfr1 := hfrO.cast (k6TailEq_of_putHdr_ne_nv (f := .prop) (by decide) (pO + 1#32))
      obtain ⟨ch1, hwc1⟩ :=
        K6WChainCursor.init hinv1.shapes hinv1.clauses.nv_le hinv1.watches hnl_lt
      c0_hsteps_nogrp
      refine wp_while_state (ts := [i32, i32, i64, i64, i32, i32])
        (α := BitVec 64 × BitVec 64 × BitVec 32 × BitVec 32 × List Nat × List Nat ×
          K6State × List (List Nat))
        (fun st => (st.2.2.2.2.2.2.1.trl_end, st.2.2.2.2.2.2.1.unass,
          st.1, st.2.1, st.2.2.1, st.2.2.2.1, ()))
        (fun st => st.2.2.2.2.2.1.length)
        (fun st mW =>
          K6WChainCursor st.2.2.2.2.2.2.1 (lit ^^^ 1#32).toNat st.2.2.2.2.2.2.2
            st.2.2.2.2.1 st.2.2.2.2.2.1 st.2.2.1 st.2.2.2.1 ∧
          K6Inv L P st.2.2.2.2.2.2.1 ∧ K6TrailSynced st.2.2.2.2.2.2.1 ∧
          K6PropFrame L ks0 st.2.2.2.2.2.2.1 ∧ st.2.2.2.2.2.2.1.prop.toNat = pO.toNat + 1 ∧
          pO.toNat < st.2.2.2.2.2.2.1.trl_end.toNat ∧
          st.2.2.2.2.2.2.1.trl[pO.toNat]? = some lit ∧ st.2.2.2.2.2.2.1.max_v = L.mv32 ∧
          (K6MemA L kPtr (k6PropMemState ks0 st.2.2.2.2.2.2.1) ⋆ R) mW) ?_ ?_
      · intro Jw hJw
        have htr_lit : ks1.trl[pO.toNat]? = some lit := by
          change ksO.trl[pO.toNat]? = some (ksO.trl[pO.toNat]?.getD 0#32)
          rw [List.getElem?_eq_getElem
            (by rw [hinvO.shapes.trl_len]; unfold szV at hp_mv; exact hp_mv), Option.getD_some]
        exact wp_jump_state
          (proj := fun st : BitVec 64 × BitVec 64 × BitVec 32 × BitVec 32 × List Nat × List Nat ×
            K6State × List (List Nat) =>
            (st.2.2.2.2.2.2.1.trl_end, st.2.2.2.2.2.2.1.unass,
              st.1, st.2.1, st.2.2.1, st.2.2.2.1, ()))
          (ticksO, 0#64, 0xFFFFFFFF#32, ks1.whead[(lit ^^^ 1#32).toNat]?.getD 0#32, [],
            ch1[(lit ^^^ 1#32).toNat]?.getD [], ks1, ch1)
          rfl (hJw _ _ ⟨hwc1, hinv1, hsync1, hfr1, by change (pO + 1#32).toNat = _; exact hp1_eq,
            hp_lt, htr_lit, hinv1.clauses.max_v_eq, hmO⟩)
      · rintro Jw ⟨ticks, visits, prev, w, done, todo, ksW, chW⟩ mW
          ⟨hwc, hinvW, hsyncW, hfrW, hw_pr, hw_te, hw_lit, hw_mv, hmW⟩ ihW
        dsimp only at hwc hinvW hsyncW hfrW hw_pr hw_te hw_lit hw_mv hmW ⊢
        have hshW := hinvW.shapes; have hclW := hinvW.clauses
        have hnvW := hclW.nv_le; have hncW := hclW.nc_le
        have hw_nl_lt : (lit ^^^ 1#32).toNat < 2 * ksW.nv.toNat := by
          rw [hfrW.pres.nv, ← hfrO.pres.nv]; exact hnl_lt
        have hnl_val2W : ksW.vals[(lit ^^^ 1#32).toNat]? = some 2#32 := by
          have hs := hsyncW pO.toNat hw_te; rw [hw_lit, Option.getD_some] at hs
          rw [hnl_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl]; exact hs.2
        c0_hsplit
        · have hw_ne : w ≠ 0xFFFFFFFF#32 := by bv_omega
          obtain ⟨w0, todo', hw0_len, rfl, rfl, hw0_nc, hw0_mc2, hw_tn, hw_div2, hw_mod2,
              hsz_ge, har_slot_l, hbv_nv, hbv_mem, hbin_iff, hbin_eq, _⟩ :=
            hwc.step_unfold hncW hw_nl_lt hw_ne
          have hw_mod32 : w0 % 2 ^ 32 = w0 := by unfold K6Layout.maxCl at hw0_mc2; omega
          have hw0_bv2 : (BitVec.ofNat 32 w0).toNat < sz2Cl L := by
            rw [hw_tn]; unfold sz2Cl; exact hw0_mc2
          have hcid_lt : w0 / 2 < ksW.nc.toNat := by omega
          have hcid_cl : w0 / 2 < szCl L := by unfold szCl K6Layout.maxCl at *; omega
          have hcid_ne_ff : BitVec.ofNat 32 w0 >>> (1 : Nat) ≠ 0xFFFFFFFF#32 := fun h => by
            have := congrArg BitVec.toNat h; rw [hw_div2] at this
            change w0 / 2 = 4294967295 at this; unfold K6Layout.maxCl at *; omega
          let bv_bv := ksW.wblit[w0]?.getD 0#32 &&& 0x7FFFFFFF#32
          have hbv_mv2 : bv_bv.toNat < sz2V L := by dsimp only [bv_bv]; unfold sz2V; omega
          have hbv_mv2' : (ksW.wblit[(BitVec.ofNat 32 w0).toNat]?.getD 0#32 &&&
              0x7FFFFFFF#32).toNat < sz2V L := by rw [hw_tn]; exact hbv_mv2
          c0_hsplit
          · have hwc_next := k6WatchSkip_cursor hshW hwc hw0_len; c0_hsteps!; rw [hw_tn]
            exact ihW (ticks, visits + 1#64, BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32,
                done ++ [w0], todo', ksW, chW) mW (by simp)
              ⟨hwc_next, hinvW, hsyncW, hfrW, hw_pr, hw_te, hw_lit, hw_mv, hmW⟩
          · have hbv_ne1 : ksW.vals[bv_bv.toNat]? ≠ some 1#32 := fun h1 => by
              have hhc : ¬ksW.vals[(ksW.wblit[w0 % 2 ^ 32]?.getD 0#32 &&&
                  2147483647).toNat]?.getD 0#32 = 1#32 := ‹_›
              rw [hw_mod32] at hhc
              exact hhc (by change ksW.vals[bv_bv.toNat]?.getD 0#32 = 1#32; rw [h1]; rfl)
            c0_hsplit
            · have hbin_nz : (ksW.wblit[w0]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
                rw [← hw_tn]; exact ‹_›
              have hsz2 : k6ClauseSize ksW (w0 / 2) = 2 := hbin_iff.mp hbin_nz
              have hbin_fals := k6_unlinked_clause_falsified hinvW hcid_lt
                (Nat.mod_lt w0 (by decide)) hnl_val2W har_slot_l (hbin_eq hsz2)
                (fun q hq2 hqlt => by rw [hsz2] at hqlt; omega)
              c0_hsplit
              · have hbv2 : ksW.vals[bv_bv.toNat]? = some 2#32 := by
                  have h0 : ksW.vals[bv_bv.toNat]?.getD 0#32 = 2#32 := by
                    dsimp only [bv_bv]; rw [← hw_tn]; exact ‹_›
                  exact k6_vals_some hshW hbv_mv2 h0
                k6_prop_do_flush hret ksW hinvW hsyncW hfrW (fun h => absurd h hcid_ne_ff)
                  (k6_prop_confl_post hw_div2 hcid_lt hbv2 hbin_fals)
                  (BitVec.eq_of_toNat_eq (by rw [hw_pr]; exact hp1_eq))
              · have hbv_ne2 : ksW.vals[bv_bv.toNat]? ≠ some 2#32 := fun h2 => by
                  have hhc : ¬ksW.vals[(ksW.wblit[w0 % 2 ^ 32]?.getD 0#32 &&&
                      2147483647).toNat]?.getD 0#32 = 2#32 := ‹_›
                  rw [hw_mod32] at hhc
                  exact hhc (by change ksW.vals[bv_bv.toNat]?.getD 0#32 = 2#32; rw [h2]; rfl)
                have hbv0 := k6_prop_vals_dom_zero hinvW hbv_nv hbv_mv2 hbv_ne1 hbv_ne2
                obtain ⟨hte_ltW, hinvB, hsyncB, hfrB⟩ := k6_prop_assign_step_pres hinvW hsyncW
                  hfrW hw_div2 hcid_lt hcid_ne_ff hbv_nv hbv_mem hbv0 hbin_fals
                let ksB := k6AssignStep ksW bv_bv (BitVec.ofNat 32 w0 >>> (1 : Nat))
                rw [hw_tn]
                k6_prop_do_assign ksW bv_bv (BitVec.ofNat 32 w0 >>> (1 : Nat)) hbv_nv hbv_mv2
                  hte_ltW hfrW.pres.lvl (And.intro hnvW hinvB.clauses.nv_le) (by
                    have hwcB : K6WChainCursor ksB (lit ^^^ 1#32).toNat chW done
                        (w0 :: todo') prev (BitVec.ofNat 32 w0) :=
                      ⟨hwc.len_eq, hwc.nodup, hwc.chain_l, hwc.chains_wc, hwc.chains_bnd,
                       hwc.tail_wc, hwc.prev_rel⟩
                    have hskipB := k6WatchSkip_cursor hinvB.shapes hwcB hw0_len
                    c0_hsteps!; try rw [hw_tn]
                    exact ihW (ticks, visits + 1#64, BitVec.ofNat 32 w0, ksB.wnext[w0]?.getD 0#32,
                        done ++ [w0], todo', ksB, chW) mB (by simp)
                      ⟨hskipB, hinvB, hsyncB, hfrB, hw_pr,
                       Nat.lt_of_lt_of_le hw_te (k6PropAssign_frame hinvW hbv_nv hbv0
                         hcid_ne_ff).te_ge,
                       ((k6PropAssign_frame hinvW hbv_nv hbv0 hcid_ne_ff).old_trl pO.toNat
                         hw_te).1.trans hw_lit, hw_mv, hmB⟩)
                · exfalso; have hhc : ¬ksW.vals[(ksW.wblit[w0]?.getD 0#32 &&&
                      2147483647).toNat]?.getD 0#32 = 0#32 := ‹_›
                  exact hhc (by change ksW.vals[bv_bv.toNat]?.getD 0#32 = 0#32; rw [hbv0]; rfl)
            · have hnonbin : (ksW.wblit[w0]?.getD 0#32 &&& 0x80000000#32) = 0#32 := by
                rw [← hw_tn]; exact ‹_›
              have hsz_ne2 : k6ClauseSize ksW (w0 / 2) ≠ 2 := fun h2 =>
                absurd (hbin_iff.mpr h2) (by rw [hnonbin]; simp)
              obtain ⟨har_ok, hother_nv, hot_mem, hslot_bv, hslot_other_bv, hcl_off_add,
                hcl_off_ar, hother_mv2, hother_hc_eq⟩ :=
                k6_nonbin_setup hinvW hcid_lt hw_div2 hw_mod2
              let other := ksW.arena[k6ClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32
              have hw_sh1 : (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat = w0 / 2 := hw_div2
              have hoth_arr_lt : (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>>
                  (1 : Nat)).toNat]?.getD 0#32 + (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^
                  (1 : BitVec 32))).toNat]?.getD 0#32).toNat < sz2V L := by
                rw [hw_sh1, hcl_off_add]; exact hother_mv2
              obtain ⟨hoth_cap, hoth_sum⟩ :=
                k6_prop_other_bounds hac_b.2 hw_sh1 hw_mod2 har_ok hsz_ge
              c0_hsplit
              · obtain ⟨hkp_inv, hkp_wc⟩ :=
                  k6WatchKeep_preserves hinvW hw_nl_lt hwc hother_nv hot_mem hsz_ne2
                c0_hsteps!; rw [hw_tn]
                refine ihW (ticks + 1#64, visits + 1#64, BitVec.ofNat 32 w0,
                    ksW.wnext[w0]?.getD 0#32, done ++ [w0], todo',
                    ksW.putArr .wblit w0 other, chW) _ (by simp)
                  ⟨hkp_wc, hkp_inv, hsyncW,
                    hfrW.cast (k6TailEq_putArr_nonTail (f := .wblit) (by decide) w0 other),
                    hw_pr, hw_te, hw_lit, hw_mv, ?_⟩
                refine Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm
                dsimp only [k6PropMemState]; k6_ext <;> (first | rfl | {
                  dsimp only [other]; try rw [hw_tn]; try rw [hw_sh1]; try rw [hcl_off_add]
                  try dsimp only [k6ClauseOff]; try rfl })
              · have hoth_ne1 : ksW.vals[other.toNat]? ≠ some 1#32 := fun h1 => by
                  have hhc : ¬ksW.vals[(ksW.arena[((ksW.clOff[w0 % 2 ^ 32 / 2]?.getD 0#32).toNat +
                      (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat) % 2 ^ 32]?.getD
                        0#32).toNat]?.getD 0#32 = 1#32 := ‹_›
                  rw [hother_hc_eq] at hhc; exact hhc (by rw [h1]; rfl)
                c0_hsteps_nogrp
                let sz := ksW.clSz[w0 / 2]?.getD 0#32; let off := ksW.clOff[w0 / 2]?.getD 0#32
                refine wp_while_break_state
                  (projBrk := fun b : BitVec 32 × BitVec 32 × BitVec 32 => (b.1, b.2.1, b.2.2, ()))
                  (fun b mb => mW = mb ∧
                    ((b.2.1 = 0xFFFFFFFF#32 ∧ ∀ q, 2 ≤ q → q < sz.toNat →
                      ksW.vals[(ksW.arena[off.toNat + q]?.getD 0#32).toNat]? = some 2#32) ∨
                     (2 ≤ b.2.1.toNat ∧ b.2.1.toNat < sz.toNat ∧
                      b.2.2 = ksW.arena[off.toNat + b.2.1.toNat]?.getD 0#32 ∧
                      ksW.vals[b.2.2.toNat]? ≠ some 2#32)))
                  (projLp := fun st : BitVec 32 => (st, ())) (fun st => sz.toNat - st.toNat)
                  (fun r m'' => mW = m'' ∧ r.toNat ≤ sz.toNat ∧ 2 ≤ r.toNat ∧
                    ∀ q, 2 ≤ q → q < r.toNat →
                      ksW.vals[(ksW.arena[off.toNat + q]?.getD 0#32).toNat]? = some 2#32)
                  ?_ ?_ ?_
                · rintro B ⟨_, ri, repl⟩ mb ⟨hmb, hbrk⟩; subst mb; dsimp only at hbrk ⊢
                  c0_hsplit
                  · have hri_ne : ri ≠ 0xFFFFFFFF#32 := by bv_omega
                    obtain ⟨hri_ge, hri_lt, hrepl_eq, hrepl_ne2⟩ :=
                      hbrk.resolve_left (fun h => hri_ne h.1)
                    have hrepl_ne : repl.toNat ≠ (lit ^^^ 1#32).toNat := fun h =>
                      hrepl_ne2 (by rw [h]; exact hnl_val2W)
                    obtain ⟨hrl_inv, ⟨chR, hwcR⟩⟩ :=
                      k6WatchReloc_preserves hinvW hw_nl_lt hwc hri_ge hri_lt hrepl_ne rfl hrepl_eq
                    obtain ⟨hri_cap, hri_lit⟩ := har_ok ri.toNat hri_lt
                    obtain ⟨hslot_cap, _⟩ :=
                      har_ok (w0 % 2) (by have := Nat.mod_lt w0 (by decide : 0 < 2); omega)
                    obtain ⟨hslot_off_eq, _, _, _⟩ :=
                      k6_reloc_addrs hw_div2 hslot_bv hslot_cap hri_cap
                    have hrepl_mv2 : repl.toNat < sz2V L := by
                      change repl = ksW.arena[k6ClauseOff ksW (w0 / 2) +
                        ri.toNat]?.getD 0#32 at hrepl_eq
                      rw [hrepl_eq]; unfold sz2V; omega
                    have hprv_lt := k6_prop_prv_lt hwc hshW.wnext_len
                    let nxt := ksW.wnext[w0]?.getD 0#32
                    let ar1 := (ksW.arena.set (k6ClauseOff ksW (w0 / 2) + w0 % 2) repl).set
                      (k6ClauseOff ksW (w0 / 2) + ri.toNat) (BitVec.ofNat 32 (lit ^^^ 1#32).toNat)
                    let wh1 := if prev = 0xFFFFFFFF#32 then ksW.whead.set (lit ^^^ 1#32).toNat nxt
                      else ksW.whead
                    let wn1 := if prev = 0xFFFFFFFF#32 then ksW.wnext
                      else ksW.wnext.set prev.toNat nxt
                    let ks1r : K6State := { ksW with arena := ar1, whead := wh1, wnext := wn1 }
                    have htl_rel := k6_reloc_tailEq (L := L) (ks0 := ksW)
                      (w := BitVec.ofNat 32 w0) (repl := repl) (other := other)
                      (nxt := nxt) (prev := prev) (arOff := k6ClauseOff ksW (w0 / 2))
                      (slot := w0 % 2) (ri := ri.toNat) (k6TailEq_refl L ksW) hw_nl_lt
                      (by rw [hrepl_eq]; exact hri_lit)
                    have hw_sh_bv := k6_prop_sh_bv (w0 := w0)
                      (by unfold K6Layout.maxCl at hw0_mc2; omega)
                    have hreq := k6_prop_reloc_mem (L := L) (ks0 := ks0) (ksW := ksW)
                      (lit := lit) (repl := repl) (nxt := nxt) (prev := prev) hw_tn
                      hw_sh_bv hslot_cap hri_cap hslot_bv rfl
                    obtain ⟨hslot_sum, hslot_cap'⟩ :=
                      k6_prop_off_add_lt hac_b.2 hw_sh1 (by rw [hw_mod2]; exact hslot_cap)
                    obtain ⟨hri_sum, hri_cap'⟩ := k6_prop_off_add_lt hac_b.2 hw_sh1 hri_cap
                    c0_hsteps_nogrp
                    refine wp_join0 (fun mr => (K6MemA L kPtr (k6PropMemState ks0 ks1r) ⋆ R) mr)
                      ?_ ?_
                    · intro Jr mr hmr; c0_hsteps!; rw [hw_tn]
                      refine ihW (ticks + 1#64, visits + 1#64, prev, nxt, done, todo',
                          k6WatchStep0 ks1r (BitVec.ofNat 32 w0) repl other, chR) _ (by simp)
                        ⟨hwcR, hrl_inv, hsyncW, hfrW.cast htl_rel, hw_pr, hw_te, hw_lit, hw_mv, ?_⟩
                      refine Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm
                      dsimp only [k6PropMemState, k6WatchStep0, ks1r, wh1, wn1, ar1, nxt, Val,
                        other]
                      k6_ext <;> (first | rfl | {
                        try rw [hw_tn]; try rw [hw_sh1]; try rw [hw_sh_bv]
                        try rw [hcl_off_add]
                        try simp only [show (1 : BitVec 32) = 1#32 from rfl]
                        try dsimp only [k6ClauseOff]; try rfl })
                    · intro Jr hJr; c0_hsplit
                      · have hpeq : prev = 0xFFFFFFFF#32 := by bv_omega
                        c0_hsteps!
                        exact hJr _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _)
                          (hreq.1 hpeq)) hm)
                      · have hpne : prev ≠ 0xFFFFFFFF#32 := by bv_omega
                        have hprv_bd := hprv_lt hpne; c0_hsteps!
                        exact hJr _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _)
                          (hreq.2 hpne)) hm)
                  · have hri_eq : ri = 0xFFFFFFFF#32 := by bv_omega
                    have h_all2 : ∀ q, 2 ≤ q → q < sz.toNat →
                        ksW.vals[(ksW.arena[off.toNat + q]?.getD 0#32).toNat]? = some 2#32 :=
                      (hbrk.resolve_right fun h => by
                        have hlt := h.2.1; have := hclW.alen_le; unfold dimacsBound at hac_b
                        have hcl_sz_lt := (har_ok (k6ClauseSize ksW (w0 / 2) - 1) (by omega)).1
                        have hsz_bd : sz.toNat < 2 ^ 28 := by
                          change k6ClauseSize ksW (w0 / 2) < 2 ^ 28; omega
                        rw [hri_eq, show (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 from rfl]
                          at hlt; omega).2
                    obtain ⟨hinvK, hwcK⟩ :=
                      k6WatchKeep_preserves hinvW hw_nl_lt hwc hother_nv hot_mem hsz_ne2
                    let ksK := ksW.putArr .wblit w0 other
                    have hfrK := hfrW.cast (k6TailEq_putArr_nonTail (f :=
                      .wblit) (by decide) w0 other)
                    have hcl_fals := k6_unlinked_clause_falsified hinvK hcid_lt
                      (Nat.mod_lt w0 (by decide)) hnl_val2W har_slot_l rfl h_all2
                    have hother_bv_eq : ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>>
                        (1 : Nat)).toNat]?.getD 0#32 + (BitVec.ofNat 32 w0 &&&
                        (1 : BitVec 32) ^^^ (1 : BitVec 32))).toNat]?.getD 0#32 = other := by
                      rw [hw_sh1, hcl_off_add]
                    have hk_put : ∀ {idx : Nat} {val : BitVec 32}, idx = w0 → val = other →
                        (k6PropMemState ks0 ksW).putArr .wblit idx val =
                          k6PropMemState ks0 ksK := fun hi hv => by subst hi; subst hv; rfl
                    c0_hsplit
                    · have hm := (fun {s1 s2 m} (h : (K6MemA L kPtr s1 ⋆ R) m) (e : s1 = s2) =>
                          e ▸ h) hm (hk_put hw_tn hother_bv_eq)
                      have hov2 : ksK.vals[other.toNat]? = some 2#32 := by
                        have hc0 : ksW.vals[other.toNat]?.getD 0#32 = 2#32 := by
                          dsimp only [other]; rw [← hother_hc_eq]; assumption
                        exact k6_vals_some hinvK.shapes hother_mv2 hc0
                      k6_prop_do_flush hret ksK hinvK hsyncW hfrK (fun h => absurd h hcid_ne_ff)
                        (k6_prop_confl_post hw_div2 hcid_lt hov2 hcl_fals)
                        (BitVec.eq_of_toNat_eq (by
                          rw [show ksK.prop = ksW.prop from rfl, hw_pr]; exact hp1_eq))
                    · have hm := (fun {s1 s2 m} (h : (K6MemA L kPtr s1 ⋆ R) m) (e : s1 = s2) =>
                          e ▸ h) hm (hk_put hw_tn hother_bv_eq)
                      have hov_ne2 : ksW.vals[other.toNat]? ≠ some 2#32 := fun h2 => by
                        have hhc : ¬ksW.vals[(ksW.arena[((ksW.clOff[w0 % 2 ^ 32 / 2]?.getD
                            0#32).toNat + (BitVec.ofNat 32 w0 &&& 1#32 ^^^ 1#32).toNat) %
                            2 ^ 32]?.getD 0#32).toNat]?.getD 0#32 = 2#32 := ‹_›
                        rw [hother_hc_eq] at hhc; exact hhc (by rw [h2]; rfl)
                      have hov0 := k6_prop_vals_dom_zero hinvW hother_nv hother_mv2 hoth_ne1 hov_ne2
                      obtain ⟨hte_ltK, hinvF, hsyncF, hfrF⟩ := k6_prop_assign_step_pres hinvK hsyncW
                        hfrK hw_div2 hcid_lt hcid_ne_ff hother_nv hot_mem hov0 hcl_fals
                      let ksF := k6AssignStep ksK other (BitVec.ofNat 32 w0 >>> (1 : Nat))
                      try simp only [k6_prop_c0_other (ks0 := ks0) hother_bv_eq]
                      try simp only [k6_prop_c0_other_bv (ks0 := ks0) hother_bv_eq]
                      k6_prop_do_assign ksK other (BitVec.ofNat 32 w0 >>> (1 : Nat)) hother_nv
                        hother_mv2 hte_ltK hfrK.pres.lvl (And.intro hnvW hinvF.clauses.nv_le) (by
                          have hskipF : K6WChainCursor ksF (lit ^^^ 1#32).toNat chW (done ++ [w0])
                              todo' (BitVec.ofNat 32 w0) (ksW.wnext[w0]?.getD 0#32) :=
                            ⟨hwcK.len_eq, hwcK.nodup, hwcK.chain_l, hwcK.chains_wc, hwcK.chains_bnd,
                             hwcK.tail_wc, hwcK.prev_rel⟩
                          c0_hsteps!; try rw [hw_tn]
                          exact ihW (ticks + 1#64, visits + 1#64, BitVec.ofNat 32 w0,
                              ksF.wnext[w0]?.getD 0#32, done ++ [w0], todo', ksF, chW) mB (by simp)
                            ⟨hskipF, hinvF, hsyncF, hfrF, hw_pr,
                             Nat.lt_of_lt_of_le hw_te (k6PropAssign_frame hinvK hother_nv hov0
                               hcid_ne_ff).te_ge,
                             ((k6PropAssign_frame hinvK hother_nv hov0 hcid_ne_ff).old_trl pO.toNat
                               hw_te).1.trans hw_lit, hw_mv, hmB⟩)
                      · exfalso
                        have hhc : ¬ksK.vals[other.toNat]?.getD 0#32 = 0#32 := by assumption
                        exact hhc (by change ksW.vals[other.toNat]?.getD 0#32 = 0#32
                                      rw [hov0]; rfl)
                · intro B L2 r m2 hB ih2 ⟨hm2, hr_le, hr2, hr_fals⟩
                  subst m2; dsimp only at hr_le hr2 hr_fals ⊢
                  c0_hsplit
                  · have hr_lt : r.toNat < sz.toNat := by
                      have hc0 : r.toNat < (ksW.clSz[w0 % 2 ^ 32 / 2]?.getD 0#32).toNat := ‹_›
                      rwa [hw_mod32] at hc0
                    obtain ⟨hr_cap, hr_lit⟩ := har_ok r.toNat hr_lt
                    have hr_off_eq : (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD
                        0#32 + r).toNat = off.toNat + r.toNat := by
                      rw [hw_sh1]; unfold off; unfold dimacsBound at hac_b
                      change k6ClauseOff ksW (w0 / 2) + r.toNat < L.acap at hr_cap
                      unfold k6ClauseOff at hr_cap; bv_omega
                    have hr_ar : (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32 +
                        r).toNat < szAr L := by unfold szAr; rw [hr_off_eq]; exact hr_cap
                    have hcand_mv2 : (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>>
                        (1 : Nat)).toNat]?.getD 0#32 + r).toNat]?.getD 0#32).toNat < sz2V L := by
                      rw [hr_off_eq]; unfold off sz2V; exact Nat.lt_of_lt_of_le hr_lit (by omega)
                    have hr1_wrap : (r + 1#32).toNat = r.toNat + 1 := by
                      have := hclW.alen_le; unfold dimacsBound at hac_b
                      have hcl_sz_lt := (har_ok (k6ClauseSize ksW (w0 / 2) - 1) (by omega)).1
                      have hsz_bd : sz.toNat < 2 ^ 28 := by
                        change k6ClauseSize ksW (w0 / 2) < 2 ^ 28; omega
                      bv_omega
                    obtain ⟨hr_sum, hr_cap'⟩ := k6_prop_off_add_lt hac_b.2 hw_sh1 hr_cap
                    c0_hsteps_nogrp; c0_hsplit
                    · have hc_ne2 : ksW.vals[(ksW.arena[off.toNat + r.toNat]?.getD
                          0#32).toNat]? ≠ some 2#32 := fun heq => by
                        have hc0 : ksW.vals[(ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>>
                            (1 : Nat)).toNat]?.getD 0#32 + r).toNat]?.getD 0#32).toNat]?.getD
                            0#32 ≠ 2#32 := ‹_›
                        rw [hr_off_eq, heq, Option.getD_some] at hc0; exact hc0 rfl
                      c0_hsteps!; dsimp only [k6PropMemState]; rw [hr_off_eq]
                      exact hB (r, r, ksW.arena[off.toNat + r.toNat]?.getD 0#32) mW
                        ⟨rfl, Or.inr ⟨hr2, hr_lt, rfl, hc_ne2⟩⟩
                    · have hc_eq2 : ksW.vals[(ksW.arena[off.toNat + r.toNat]?.getD
                          0#32).toNat]? = some 2#32 := by
                        have hc0 : ksW.vals[(ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>>
                            (1 : Nat)).toNat]?.getD 0#32 + r).toNat]?.getD 0#32).toNat]?.getD
                            0#32 = 2#32 := ‹_›
                        rw [hr_off_eq] at hc0
                        exact k6_vals_some hshW (by rw [← hr_off_eq]; exact hcand_mv2) hc0
                      c0_hsteps!; refine ih2 (r + 1#32) mW (by rw [hr1_wrap]; omega)
                        ⟨rfl, by rw [hr1_wrap]; omega, by rw [hr1_wrap]; omega, fun q hq2 hqr => by
                          rw [hr1_wrap] at hqr; by_cases hqe : q = r.toNat
                          · subst hqe; exact hc_eq2
                          · exact hr_fals q hq2 (by omega)⟩
                  · have hr_eq : r.toNat = sz.toNat := by
                      have hge : ¬ r.toNat < (ksW.clSz[(BitVec.ofNat 32 w0 >>>
                          (1 : Nat)).toNat]?.getD 0#32).toNat := ‹_›
                      rw [hw_sh1] at hge; dsimp only [sz] at hr_le ⊢; omega
                    c0_hsteps!; exact hB (r, 0xFFFFFFFF#32, 0#32) mW
                      ⟨rfl, Or.inl ⟨rfl, fun q hq2 hqsz => hr_fals q hq2 (by omega)⟩⟩
                · intro B L2 _ hL2; c0_hsteps!
                  exact hL2 2#32 mW ⟨rfl, hsz_ge, le_refl _, fun _ _ hq => by
                    rw [show (2#32 : BitVec 32).toNat = 2 from rfl] at hq; omega⟩
        · c0_hsteps!
          have hw_pr' : ksW.prop = pO + 1#32 :=
            BitVec.eq_of_toNat_eq (by rw [hw_pr]; exact hp1_eq.symm)
          change J (pO + 1#32, ksW.trl_end, ksW.unass, ticks + (visits >>> 4#64) + 1#64, ()) mW
          rw [← hw_pr']
          refine ihO (ticks + (visits >>> 4#64) + 1#64, ksW) mW (by
            have := hinvO.assign.trl_end_le
            have := congrArg BitVec.toNat hfrO.pres.nv
            dsimp only [pO] at hw_pr; dsimp only; omega) ⟨hinvW, hsyncW, hfrW, hmW⟩
    · have hpr_eq : ksO.prop = ksO.trl_end :=
        BitVec.eq_of_toNat_eq (by have := hinvO.assign.prop_le; bv_omega)
      k6_prop_do_flush hret ksO hinvO hsyncO hfrO (fun _ => hpr_eq) (fun h => absurd rfl h) rfl

end LeanQbe.T.Examples.Kissat.Proof.Kitten
end
