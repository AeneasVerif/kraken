/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.LemmasTrail

/-!
# Watch-Chain (`K6_BIN_FLAG`), `K6WChainCursor`, & Literal-Flip Lemmas
  (`Kissat.Proof.Kitten.LemmasWatch`)

Covers `K5WChain` traversal/bypass lemmas, `k6WatchStep0` / `k6WatchStep` 2WL preservation,
`K6WChainCursor`, `k6WatchSkip_cursor`, `k6WatchKeep_preserves`, `k6WatchReloc_preserves`, and
`k6FlipFinish_preserves`.

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

open K6MemATactics K6PtrTactics
open scoped K6MemATactics K6PtrTactics

/-! ## 1. Watch-Chain Lemmas & `k6WatchStep` Preservation -/

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
          Nat.mod_eq_of_lt (Nat.lt_trans hw1 hwn),
          Nat.mod_eq_of_lt (Nat.lt_trans hw2 hwn)] at ht
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
  have := L.hmaxV
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
      · obtain ⟨h1, h2, h3, _⟩ := hbnd l.toNat hx u
          (by simpa [List.getElem?_eq_getElem hx_ch] using hu_old)
        have hune : u ≠ w.toNat := fun heq => hfresh (by
          rw [← heq]; exact List.mem_flatten.mpr ⟨chains[l.toNat], List.getElem_mem hx_ch, hu_old⟩)
        refine ⟨h1, h2, h3, ?_⟩
        rwa [show ks'.wblit[u]? = ks.wblit[u]? from List.getElem?_set_ne hune.symm]
    · simp only [chains', List.getElem_set_ne (Ne.symm hxl)] at hu
      obtain ⟨h1, h2, h3, _⟩ := hbnd x hx u (by simpa [List.getElem?_eq_getElem hx_ch] using hu)
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
  have := L.hmaxV
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

/-! ## 2. `K6WChainCursor`, Relocation, & Literal-Flip Preservation -/

private theorem k6_list_flatten_set_sub_perm {α : Type} (xs : List (List α)) {l : Nat}
    (hi : l < xs.length) (done todo' : List α) (w0 : α)
    (heq : xs[l]'hi = done ++ w0 :: todo') :
    xs.flatten.Perm (w0 :: (xs.set l (done ++ todo')).flatten) := by
  induction xs generalizing l with
  | nil => simp at hi
  | cons x tl ih =>
    cases l with
    | zero =>
      simp only [List.getElem_cons_zero] at heq
      simp only [List.set_cons_zero, List.flatten_cons, heq, List.append_assoc]
      exact List.perm_middle
    | succ l' =>
      simp only [List.getElem_cons_succ] at heq
      simp only [List.set_cons_succ, List.flatten_cons]
      exact ((ih (by simp at hi; omega) heq).append_left x).trans List.perm_middle

private theorem k6_list_flatten_nodup_getElem {α : Type} :
    ∀ {xs : List (List α)}, xs.flatten.Nodup → ∀ {i : Nat} (hi : i < xs.length),
      (xs[i]'hi).Nodup ∧ ∀ j, j ≠ i → (hj : j < xs.length) → ∀ a ∈ xs[i]'hi, a ∉ xs[j]'hj
  | [], _, _, hi => absurd hi (by simp)
  | x :: tl, hnd, 0, _hi => by
    simp only [List.flatten_cons] at hnd
    have ha := List.nodup_append.mp hnd
    refine ⟨ha.1, fun j hne hj a hai haj => ?_⟩
    cases j with
    | zero => exact hne rfl
    | succ j' =>
      have hj' : j' < tl.length := by simp at hj; exact hj
      simp only [List.getElem_cons_zero] at hai; simp only [List.getElem_cons_succ] at haj
      exact ha.2.2 a hai a (List.mem_flatten.mpr ⟨tl[j'], List.getElem_mem hj', haj⟩) rfl
  | x :: tl, hnd, i + 1, hi => by
    simp only [List.flatten_cons] at hnd
    have ha := List.nodup_append.mp hnd
    have hi' : i < tl.length := by simp at hi; exact hi
    have ihr := k6_list_flatten_nodup_getElem ha.2.1 hi'
    refine ⟨ihr.1, fun j hne hj a hai haj => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem_cons_succ] at hai; simp only [List.getElem_cons_zero] at haj
      exact ha.2.2 a haj a (List.mem_flatten.mpr ⟨tl[i], List.getElem_mem hi', hai⟩) rfl
    | succ j' =>
      exact ihr.2 j' (fun h => hne (congrArg Nat.succ h)) (by simp at hj; exact hj) a hai haj

theorem k6_wchain_bypass {wn : List (BitVec 32)} {hd nxt : BitVec 32}
    {pfx : List Nat} {u w0 : Nat} {todo' : List Nat}
    (hc : K5WChain wn hd (pfx ++ u :: w0 :: todo'))
    (hnd : (pfx ++ u :: w0 :: todo').Nodup)
    (hu : u < wn.length) (hw0 : w0 < wn.length) (hnxt : wn[w0]'hw0 = nxt) :
    K5WChain (wn.set u nxt) hd (pfx ++ [u] ++ todo') := by
  induction pfx generalizing hd with
  | nil =>
    simp only [List.nil_append, List.singleton_append] at hc hnd ⊢
    rcases k6_wchain_cases hc with ⟨_, hc_nil⟩ | ⟨u', ws1, hu', hhd, hcons, htail⟩
    · cases hc_nil
    · obtain ⟨hu_eq, hws1⟩ := List.cons.inj hcons; subst hhd hu_eq hws1
      rcases k6_wchain_cases htail with ⟨_, hnil⟩ | ⟨w', ws2, hw', _hw_eq, hcons2, htail2⟩
      · cases hnil
      · obtain ⟨hw0_eq, hws2⟩ := List.cons.inj hcons2; subst hw0_eq hws2
        have hnd_u : u ∉ w0 :: todo' := (List.nodup_cons.mp hnd).1
        have hu_nt : u ∉ todo' := fun h => hnd_u (List.mem_cons_of_mem _ h)
        have htail_c : K5WChain (wn.set u nxt) nxt todo' := by
          rw [← hnxt]
          exact k6_wchain_congr htail2 fun y hy =>
            (List.getElem?_set_ne (fun h : u = y => hu_nt (h ▸ hy))).symm
        have hus : u < (wn.set u nxt).length := by simp [hu]
        exact K5WChain.cons hus (by rw [List.getElem_set_self]; exact htail_c)
  | cons x xs ih =>
    simp only [List.cons_append] at hc hnd ⊢
    rcases k6_wchain_cases hc with ⟨_, hc_nil⟩ | ⟨x', ws1, hx', hhd, hcons, htail⟩
    · cases hc_nil
    · obtain ⟨hx_eq, hws1⟩ := List.cons.inj hcons; subst hhd hx_eq hws1
      have hnd_x := List.nodup_cons.mp hnd
      have hxu : x ≠ u := fun h => hnd_x.1 (h ▸ List.mem_append_right xs List.mem_cons_self)
      have hxs_s : x < (wn.set u nxt).length := by simp [hx']
      have hset_x : (wn.set u nxt)[x]'hxs_s = wn[x]'hx' := List.getElem_set_ne hxu.symm hxs_s
      have ih' := ih htail hnd_x.2
      rw [← hset_x] at ih'; exact K5WChain.cons hxs_s ih'

structure K6WChainCursor (ks : K6State) (l : Nat) (chains : List (List Nat))
    (done todo : List Nat) (prev w : BitVec 32) : Prop where
  len_eq : chains.length = 2 * ks.nv.toNat
  nodup : chains.flatten.Nodup
  chain_l : chains[l]?.getD [] = done ++ todo
  chains_wc : ∀ x < 2 * ks.nv.toNat,
    K5WChain ks.wnext (ks.whead[x]?.getD 0xFFFFFFFF#32) (chains[x]?.getD [])
  chains_bnd : ∀ x < 2 * ks.nv.toNat, ∀ u ∈ chains[x]?.getD [],
    u < 2 * ks.nc.toNat ∧ 2 ≤ k6ClauseSize ks (u / 2) ∧
    (ks.arena[k6ClauseOff ks (u / 2) + (u % 2)]?.getD 0#32).toNat = x ∧
    let wb := ks.wblit[u]?.getD 0#32
    let bv := (wb &&& 0x7FFFFFFF#32).toNat
    bv < 2 * ks.nv.toNat ∧ bv ∈ k6ClauseLits ks (u / 2) ∧
    ((wb &&& 0x80000000#32) ≠ 0#32 ↔ k6ClauseSize ks (u / 2) = 2) ∧
    (k6ClauseSize ks (u / 2) = 2 →
      bv = (ks.arena[k6ClauseOff ks (u / 2) + (u % 2 ^^^ 1)]?.getD 0#32).toNat)
  tail_wc : K5WChain ks.wnext w todo
  prev_rel : (done = [] ∧ prev = 0xFFFFFFFF#32 ∧ ks.whead[l]?.getD 0xFFFFFFFF#32 = w) ∨
    (∃ pfx u, done = pfx ++ [u] ∧ prev = BitVec.ofNat 32 u ∧
      u < ks.wnext.length ∧ ks.wnext[u]?.getD 0xFFFFFFFF#32 = w)

theorem K6WChainCursor.watchesOk {ks : K6State} {l : Nat} {chains : List (List Nat)}
    {done todo : List Nat} {prev w : BitVec 32}
    (wc : K6WChainCursor ks l chains done todo prev w) : K6WatchesOk ks :=
  ⟨chains, wc.len_eq, wc.nodup, wc.chains_wc, wc.chains_bnd⟩

theorem K6WChainCursor.init {L : K6Layout} {ks : K6State} (hsh : ks.ShapesOk L)
    (hnv : ks.nv.toNat ≤ L.maxV) (hw : K6WatchesOk ks) {l : Nat} (hl : l < 2 * ks.nv.toNat) :
    ∃ chains, K6WChainCursor ks l chains [] (chains[l]?.getD []) 0xFFFFFFFF#32
      (ks.whead[l]?.getD 0#32) := by
  have := L.hmaxV
  obtain ⟨chains, hlen, hnd, hwc, hbnd⟩ := hw
  have hwh_len : l < ks.whead.length := by rw [hsh.whead_len]; omega
  have hwh_eq : ks.whead[l]?.getD 0#32 = ks.whead[l]?.getD 0xFFFFFFFF#32 := by
    rw [List.getElem?_eq_getElem hwh_len]; rfl
  rw [hwh_eq]
  exact ⟨chains, hlen, hnd, rfl, hwc, hbnd, hwc l hl, Or.inl ⟨rfl, rfl, rfl⟩⟩

theorem K6WChainCursor.step_unfold {L : K6Layout} {ks : K6State} (hnc : ks.nc.toNat ≤ L.maxCl)
    {l : Nat} (hl : l < 2 * ks.nv.toNat) {chains : List (List Nat)}
    {done todo : List Nat} {prev w : BitVec 32}
    (wc : K6WChainCursor ks l chains done todo prev w) (hne : w ≠ 0xFFFFFFFF#32) :
    ∃ w0 todo', w0 < ks.wnext.length ∧
      todo = w0 :: todo' ∧ w = BitVec.ofNat 32 w0 ∧ w0 < 2 * ks.nc.toNat ∧ w0 < 2 * L.maxCl ∧
      w.toNat = w0 ∧ (w >>> (1 : Nat)).toNat = w0 / 2 ∧ (w &&& 1#32).toNat = w0 % 2 ∧
      2 ≤ k6ClauseSize ks (w0 / 2) ∧
      (ks.arena[k6ClauseOff ks (w0 / 2) + (w0 % 2)]?.getD 0#32).toNat = l ∧
      let wb := ks.wblit[w0]?.getD 0#32
      let bv := (wb &&& 0x7FFFFFFF#32).toNat
      bv < 2 * ks.nv.toNat ∧ bv ∈ k6ClauseLits ks (w0 / 2) ∧
      ((wb &&& 0x80000000#32) ≠ 0#32 ↔ k6ClauseSize ks (w0 / 2) = 2) ∧
      (k6ClauseSize ks (w0 / 2) = 2 →
        bv = (ks.arena[k6ClauseOff ks (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32).toNat) ∧
      K5WChain ks.wnext (ks.wnext[w0]?.getD 0#32) todo' := by
  have := L.hmaxV
  obtain ⟨w0, todo', hw0, htd, hw_eq, htail⟩ := k6_wchain_getElem_of_eq wc.tail_wc hne
  have hm_l : w0 ∈ chains[l]?.getD [] := by
    rw [wc.chain_l, htd]; exact List.mem_append_right _ List.mem_cons_self
  have hb := wc.chains_bnd l hl w0 hm_l
  have hlt_mc : w0 < 2 * L.maxCl := by omega
  have hlt32 : w0 < 2 ^ 32 := by unfold K6Layout.maxCl at hlt_mc; omega
  have hw_tn : w.toNat = w0 := by rw [hw_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32]
  have hw_div2 : (w >>> (1 : Nat)).toNat = w0 / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one, hw_tn]
  have hw_mod2 : (w &&& 1#32).toNat = w0 % 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod w.toNat 1, hw_tn]
  have hnxt_eq : ks.wnext[w0]?.getD 0#32 = ks.wnext[w0]'hw0 := by
    rw [List.getElem?_eq_getElem hw0, Option.getD_some]
  refine ⟨w0, todo', hw0, htd, hw_eq, hb.1, hlt_mc, hw_tn, hw_div2, hw_mod2,
    hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2.1, hb.2.2.2.2.2.2, ?_⟩
  rw [hnxt_eq]; exact htail

theorem k6WatchSkip_cursor {L : K6Layout} {ks : K6State} (hsh : ks.ShapesOk L)
    {l : Nat} {chains : List (List Nat)} {done todo' : List Nat} {prev : BitVec 32} {w0 : Nat}
    (wc : K6WChainCursor ks l chains done (w0 :: todo') prev (BitVec.ofNat 32 w0))
    (hw0_len : w0 < ks.wnext.length) :
    K6WChainCursor ks l chains (done ++ [w0]) todo' (BitVec.ofNat 32 w0)
      (ks.wnext[w0]?.getD 0#32) := by
  have := L.hmaxV
  have hnxt_eq : ks.wnext[w0]?.getD 0#32 = ks.wnext[w0]?.getD 0xFFFFFFFF#32 := by
    rw [List.getElem?_eq_getElem hw0_len]; rfl
  rcases k6_wchain_cases wc.tail_wc with ⟨_, hnil⟩ | ⟨w0', _, hw0', hw_eq, hcons, htail'⟩
  · cases hnil
  · obtain ⟨_, htd_eq⟩ := List.cons.inj hcons; subst htd_eq
    have hw0_eq : w0 = w0' := by
      have ht := congrArg BitVec.toNat hw_eq
      have h1 : w0 < 2 ^ 32 := by
        rw [hsh.wnext_len] at hw0_len; unfold K6Layout.maxCl at hw0_len; omega
      have h2 : w0' < 2 ^ 32 := by
        rw [hsh.wnext_len] at hw0'; unfold K6Layout.maxCl at hw0'; omega
      simpa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] using ht
    subst hw0_eq
    refine ⟨wc.len_eq, wc.nodup, by rw [wc.chain_l]; simp, wc.chains_wc, wc.chains_bnd, ?_,
      Or.inr ⟨done, w0, rfl, rfl, hw0_len, hnxt_eq.symm⟩⟩
    rwa [List.getElem?_eq_getElem hw0', Option.getD_some]

theorem k6WatchKeep_preserves {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) {l : Nat} (hl : l < 2 * ks.nv.toNat) {chains : List (List Nat)}
    {done todo' : List Nat} {prev : BitVec 32} {w0 : Nat}
    (wc : K6WChainCursor ks l chains done (w0 :: todo') prev (BitVec.ofNat 32 w0))
    {other : BitVec 32} (hoth : other.toNat < 2 * ks.nv.toNat)
    (hot_mem : other.toNat ∈ k6ClauseLits ks (w0 / 2))
    (hsz3 : k6ClauseSize ks (w0 / 2) ≠ 2) :
    let ks' := ks.putArr .wblit w0 other
    K6Inv L P ks' ∧
    K6WChainCursor ks' l chains (done ++ [w0]) todo' (BitVec.ofNat 32 w0)
      (ks.wnext[w0]?.getD 0#32) := by
  intro ks'
  have := L.hmaxV
  have hsh := hinv.shapes; have hnv := hinv.clauses.nv_le; have hnc := hinv.clauses.nc_le
  have hoth31 : other.toNat < 2 ^ 31 := by omega
  have hmk := k6_bv32_lt31_and_mask hoth31
  have hm_l : w0 ∈ chains[l]?.getD [] := by
    rw [wc.chain_l]; exact List.mem_append_right _ List.mem_cons_self
  have hb0 := wc.chains_bnd l hl w0 hm_l
  have hwb_len : w0 < ks.wblit.length := by rw [hsh.wblit_len]; have := hb0.1; omega
  have hwn_len : w0 < ks.wnext.length := by rw [hsh.wnext_len]; have := hb0.1; omega
  have hnxt_eq : ks.wnext[w0]?.getD 0#32 = ks.wnext[w0]?.getD 0xFFFFFFFF#32 := by
    rw [List.getElem?_eq_getElem hwn_len]; rfl
  rcases k6_wchain_cases wc.tail_wc with ⟨_, hnil⟩ | ⟨w0', _, hw0', hw_eq, hcons, htail'⟩
  · cases hnil
  · obtain ⟨_, htd_eq⟩ := List.cons.inj hcons; subst htd_eq
    have hw0_eq : w0 = w0' := by
      have ht := congrArg BitVec.toNat hw_eq
      have h1 : w0 < 2 ^ 32 := by unfold K6Layout.maxCl at hnc; omega
      have h2 : w0' < 2 ^ 32 := by
        rw [hsh.wnext_len] at hw0'; unfold K6Layout.maxCl at hw0'; omega
      simpa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] using ht
    subst hw0_eq
    have wc' : K6WChainCursor ks' l chains (done ++ [w0]) todo' (BitVec.ofNat 32 w0)
        (ks.wnext[w0]?.getD 0#32) := by
      refine ⟨wc.len_eq, wc.nodup, by rw [wc.chain_l]; simp, wc.chains_wc, ?_, ?_,
        Or.inr ⟨done, w0, rfl, rfl, hwn_len, hnxt_eq.symm⟩⟩
      · intro x hx u hu; have hbu := wc.chains_bnd x hx u hu
        by_cases hu0 : u = w0
        · rw [hu0] at hbu ⊢
          refine ⟨hbu.1, hbu.2.1, hbu.2.2.1, ?_⟩
          change let wb := (ks.wblit.set w0 other)[w0]?.getD 0#32
                 let bv := (wb &&& 0x7FFFFFFF#32).toNat
                 bv < 2 * ks.nv.toNat ∧ bv ∈ k6ClauseLits ks (w0 / 2) ∧
                 ((wb &&& 0x80000000#32) ≠ 0#32 ↔ k6ClauseSize ks (w0 / 2) = 2) ∧
                 (k6ClauseSize ks (w0 / 2) = 2 →
                   bv = (ks.arena[k6ClauseOff ks (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32).toNat)
          dsimp only
          rw [List.getElem?_set_self hwb_len, Option.getD_some, hmk.1, hmk.2]
          exact ⟨hoth, hot_mem, ⟨fun h => absurd rfl h, fun h => absurd h hsz3⟩,
            fun h => absurd h hsz3⟩
        · refine ⟨hbu.1, hbu.2.1, hbu.2.2.1, ?_⟩
          have hwb : (ks.wblit.set w0 other)[u]? = ks.wblit[u]? :=
            List.getElem?_set_ne (Ne.symm hu0)
          dsimp only [ks', K6State.putArr]; rw [hwb]
          exact ⟨hbu.2.2.2.1, hbu.2.2.2.2.1, hbu.2.2.2.2.2.1, hbu.2.2.2.2.2.2⟩
      · change K5WChain ks.wnext (ks.wnext[w0]?.getD 0#32) todo'
        rwa [List.getElem?_eq_getElem hw0', Option.getD_some]
    exact ⟨⟨hsh.putArr .wblit w0 other,
      k6ClausesOk_cast hinv.clauses rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
      wc'.watchesOk,
      k6BaseAssignOk_cast hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl,
      by dsimp only [ks', K6State.putArr]; exact hinv.reasons⟩, wc'⟩

theorem k6WatchReloc_preserves {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) {l : Nat} (hl : l < 2 * ks.nv.toNat) {chains : List (List Nat)}
    {done todo' : List Nat} {prev : BitVec 32} {w0 : Nat}
    (wc : K6WChainCursor ks l chains done (w0 :: todo') prev (BitVec.ofNat 32 w0))
    {ri : Nat} (hri_ge : 2 ≤ ri) (hri_lt : ri < k6ClauseSize ks (w0 / 2))
    {repl other : BitVec 32} (hrepl_ne : repl.toNat ≠ l)
    (hother_eq : other = ks.arena[k6ClauseOff ks (w0 / 2) + ((w0 % 2) ^^^ 1)]?.getD 0#32)
    (hrepl_eq : repl = ks.arena[k6ClauseOff ks (w0 / 2) + ri]?.getD 0#32) :
    let w := BitVec.ofNat 32 w0
    let nxt := ks.wnext[w0]?.getD 0#32
    let cid := w0 / 2
    let slot := w0 % 2
    let off := k6ClauseOff ks cid
    let ar' := (ks.arena.set (off + slot) repl).set (off + ri) (BitVec.ofNat 32 l)
    let wh1 := if prev = 0xFFFFFFFF#32 then ks.whead.set l nxt else ks.whead
    let wn1 := if prev = 0xFFFFFFFF#32 then ks.wnext else ks.wnext.set prev.toNat nxt
    let ks1 : K6State := { ks with arena := ar', whead := wh1, wnext := wn1 }
    let ks' := k6WatchStep0 ks1 w repl other
    K6Inv L P ks' ∧ (∃ chains', K6WChainCursor ks' l chains' done todo' prev nxt) := by
  intro w nxt cid slot off ar' wh1 wn1 ks1 ks'
  have := L.hmaxV
  have hsh := hinv.shapes; have hnv := hinv.clauses.nv_le; have hnc := hinv.clauses.nc_le
  have hch_l : l < chains.length := by rw [wc.len_eq]; exact hl
  have hm_l : w0 ∈ chains[l]?.getD [] := by
    rw [wc.chain_l]; exact List.mem_append_right _ List.mem_cons_self
  have hb0 := wc.chains_bnd l hl w0 hm_l
  have hcid_lt : cid < ks.nc.toNat := by dsimp only [cid]; omega
  have hwf_c := hinv.clauses.cl_wf cid hcid_lt
  have hsz_ge : 2 ≤ k6ClauseSize ks cid := hb0.2.1
  have hsz_ne2 : k6ClauseSize ks cid ≠ 2 := by dsimp only [cid]; omega
  have hslot_lt : slot < 2 := Nat.mod_lt w0 (by decide)
  have hother_slot_lt : slot ^^^ 1 < 2 := by
    rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [slot, h]
  have hoff_le : off + k6ClauseSize ks cid ≤ ks.alen.toNat := hwf_c.2.1
  have har_len : ks.arena.length = L.acap := hsh.arena_len
  have hal_le : ks.alen.toNat ≤ L.acap := hinv.clauses.alen_le
  have hwn_len : w0 < ks.wnext.length := by rw [hsh.wnext_len]; have := hb0.1; omega
  have hwh_len : l < ks.whead.length := by rw [hsh.whead_len]; omega
  have hnxt_eq : nxt = ks.wnext[w0]'hwn_len := by
    dsimp only [nxt]; rw [List.getElem?_eq_getElem hwn_len, Option.getD_some]
  have hoff_le' : k6ClauseOff ks (w0 / 2) + k6ClauseSize ks (w0 / 2) ≤ ks.alen.toNat := hoff_le
  have har_slot :
      ks.arena[off + slot]'(by dsimp only [off, cid, slot]; omega) = BitVec.ofNat 32 l := by
    have ha := hb0.2.2.1
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at ha
    exact BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_ofNat]
      exact ha.trans (Nat.mod_eq_of_lt (by omega)).symm)
  have hrepl_lt_ar : off + ri < ks.arena.length := by dsimp only [off, cid]; omega
  have hrepl_mem : repl.toNat ∈ k6ClauseLits ks cid := by
    rw [hrepl_eq, k6_mem_clauseLits_iff (by omega)]; exact ⟨ri, hri_lt, rfl⟩
  have hrepl_nv : repl.toNat < 2 * ks.nv.toNat := hwf_c.2.2.1 _ hrepl_mem
  have hother_mem : other.toNat ∈ k6ClauseLits ks cid := by
    rw [hother_eq, k6_mem_clauseLits_iff (by omega)]; exact ⟨slot ^^^ 1, by omega, rfl⟩
  have hother_nv : other.toNat < 2 * ks.nv.toNat := hwf_c.2.2.1 _ hother_mem
  have har'_eq : ar' = (ks.arena.set (off + slot) (ks.arena[off + ri]'hrepl_lt_ar)).set
      (off + ri) (ks.arena[off + slot]'(by dsimp only [off]; omega)) := by
    dsimp only [ar']; rw [har_slot, hrepl_eq]
    change (ks.arena.set (off + slot) (ks.arena[off + ri]?.getD 0#32)).set (off + ri) _ = _
    rw [List.getElem?_eq_getElem hrepl_lt_ar, Option.getD_some]
  have hsh1 : ks1.ShapesOk L :=
    { hsh with
      whead_len := by dsimp only [ks1, wh1]; split <;> simp [hsh.whead_len]
      wnext_len := by dsimp only [ks1, wn1]; split <;> simp [hsh.wnext_len]
      arena_len := by simp [ks1, ar', hsh.arena_len] }
  have hsh' := k6WatchStep0_preserves_shapes hsh1 w repl other
  have hlits_perm_all : ∀ c < ks.nc.toNat, (k6ClauseLits ks' c).Perm (k6ClauseLits ks c) := by
    intro c hc
    by_cases hcc : c = cid
    · subst hcc; change (((ar'.drop off).take (k6ClauseSize ks cid)).map BitVec.toNat).Perm
        (((ks.arena.drop off).take (k6ClauseSize ks cid)).map BitVec.toNat)
      rw [har'_eq]
      exact (k6_drop_take_set_swap ks.arena (off := off) (sz := k6ClauseSize ks cid)
        (p := slot) (q := ri) (by omega) hri_lt (by dsimp only [off]; omega)).map _
    · have hout : ∀ idx, idx = off + slot ∨ idx = off + ri →
          idx < k6ClauseOff ks c ∨ k6ClauseOff ks c + k6ClauseSize ks c ≤ idx := by
        intro idx hidx; by_cases hlt : c < cid
        · right; have hm := hinv.clauses.cl_mono c cid hlt hcid_lt
          change k6ClauseOff ks c + k6ClauseSize ks c ≤ off at hm
          rcases hidx with rfl | rfl <;> omega
        · left; have hm := hinv.clauses.cl_mono cid c (by omega) hc
          change off + k6ClauseSize ks cid ≤ k6ClauseOff ks c at hm
          dsimp only [cid] at hm; rcases hidx with rfl | rfl <;> omega
      change (((ar'.drop (k6ClauseOff ks c)).take (k6ClauseSize ks c)).map BitVec.toNat).Perm _
      dsimp only [ar']
      rw [k6_drop_take_set_out _ _ (hout _ (Or.inr rfl)),
        k6_drop_take_set_out _ _ (hout _ (Or.inl rfl))]
      exact List.Perm.refl _
  have hcl' : K6ClausesOk L P ks' :=
    { hinv.clauses with
      cl_wf := fun c hc => by
        have hw := hinv.clauses.cl_wf c hc; have hp := hlits_perm_all c hc
        exact ⟨hw.1, hw.2.1, fun x hx => hw.2.2.1 x (hp.mem_iff.mp hx),
          SemEntails.perm hp.symm hw.2.2.2⟩ }
  have hrsn' : K6ReasonOk ks' := fun i hi => by
    rcases hinv.reasons i hi with hdec | ⟨hr_lt, hmem, hall⟩
    · exact Or.inl hdec
    · right; have hp := hlits_perm_all _ hr_lt
      exact ⟨hr_lt, hp.mem_iff.mpr hmem, fun x hx => hall x (hp.mem_iff.mp hx)⟩
  let chains1 := chains.set l (done ++ todo')
  have hch1_len : chains1.length = 2 * ks1.nv.toNat := by rw [List.length_set]; exact wc.len_eq
  have hch_l_eq : chains[l]'hch_l = done ++ w0 :: todo' := by
    have := wc.chain_l; rwa [List.getElem?_eq_getElem hch_l, Option.getD_some] at this
  have hperm1 := k6_list_flatten_set_sub_perm chains hch_l done todo' w0 hch_l_eq
  have hnd_cons := hperm1.nodup_iff.mp wc.nodup
  have hw0_not_in : w0 ∉ chains1.flatten := (List.nodup_cons.mp hnd_cons).1
  have hch1_nd : chains1.flatten.Nodup := (List.nodup_cons.mp hnd_cons).2
  have hch1_sub : ∀ x < 2 * ks.nv.toNat, ∀ u ∈ chains1[x]?.getD [], u ∈ chains[x]?.getD [] := by
    intro x hx u hu
    have hx1 : x < chains1.length := by rw [hch1_len]; exact hx
    have hx0 : x < chains.length := by rw [wc.len_eq]; exact hx
    rw [List.getElem?_eq_getElem hx1, Option.getD_some] at hu
    rw [List.getElem?_eq_getElem hx0, Option.getD_some]
    by_cases hxl : x = l
    · subst hxl; simp only [chains1, List.getElem_set_self] at hu; rw [hch_l_eq]
      exact (List.mem_append.mp hu).elim (List.mem_append_left _)
        (fun ht => List.mem_append_right _ (List.mem_cons_of_mem _ ht))
    · simpa only [chains1, List.getElem_set_ne (Ne.symm hxl)] using hu
  have hdone_elim : prev = 0xFFFFFFFF#32 → done = [] := fun hprev => by
    rcases wc.prev_rel with ⟨hd, _, _⟩ | ⟨_, u, _, hp_eq, hu_len, _⟩
    · exact hd
    · exfalso
      have h2 : u < 2 * L.maxCl := by rw [hsh.wnext_len] at hu_len; exact hu_len
      have h3 := congrArg BitVec.toNat (hp_eq.symm.trans hprev)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold K6Layout.maxCl at h2; omega),
        show (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 by decide] at h3
      unfold K6Layout.maxCl at h2; omega
  have htail_ks : K5WChain ks.wnext nxt todo' := by
    rcases k6_wchain_cases wc.tail_wc with ⟨_, hn⟩ | ⟨w0', _, hw0', hw_eq', hcons, htail'⟩
    · cases hn
    · obtain ⟨_, htd_eq⟩ := List.cons.inj hcons; subst htd_eq
      have hw0_eq : w0 = w0' := by
        have ht := congrArg BitVec.toNat hw_eq'
        have h1 : w0 < 2 ^ 32 := by unfold K6Layout.maxCl at hnc; omega
        have h2 : w0' < 2 ^ 32 := by
          rw [hsh.wnext_len] at hw0'; unfold K6Layout.maxCl at hw0'; omega
        simpa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] using ht
      subst hw0_eq
      have hg : nxt = ks.wnext[w0]'hw0' := by
        dsimp only [nxt]; rw [List.getElem?_eq_getElem hw0', Option.getD_some]
      rwa [hg]
  have hwc1 : ∀ x < 2 * ks1.nv.toNat,
      K5WChain ks1.wnext (ks1.whead[x]?.getD 0xFFFFFFFF#32) (chains1[x]?.getD []) := by
    intro x hx
    have hx1 : x < chains1.length := by rw [hch1_len]; exact hx
    have hx0 : x < chains.length := by rw [wc.len_eq]; exact hx
    by_cases hprev : prev = 0xFFFFFFFF#32
    · have hdone_nil := hdone_elim hprev
      have hwh1 : wh1 = ks.whead.set l nxt := by simp [wh1, hprev]
      have hwn1 : wn1 = ks.wnext := by simp [wn1, hprev]
      by_cases hxl : l = x
      · subst hxl; rw [List.getElem?_eq_getElem hx1, Option.getD_some]
        simp only [chains1, List.getElem_set_self, hdone_nil, List.nil_append, ks1, hwh1, hwn1]
        rw [List.getElem?_set_self hwh_len, Option.getD_some]; exact htail_ks
      · have hwc0 := wc.chains_wc x hx
        rw [List.getElem?_eq_getElem hx1, Option.getD_some]
        rw [List.getElem?_eq_getElem hx0, Option.getD_some] at hwc0
        simp only [chains1, List.getElem_set_ne hxl, ks1, hwh1, hwn1] at hwc0 ⊢
        rwa [List.getElem?_set_ne hxl]
    · rcases wc.prev_rel with ⟨_, hp_fff, _⟩ | ⟨pfx, u, hdone_eq, hp_eq, hu_len, _⟩
      · exact absurd hp_fff hprev
      · have hu_2c : u < 2 * L.maxCl := by rw [hsh.wnext_len] at hu_len; exact hu_len
        have hu_tn : prev.toNat = u := by
          rw [hp_eq, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by unfold K6Layout.maxCl at hu_2c; omega)]
        have hwh1 : wh1 = ks.whead := by simp [wh1, hprev]
        have hwn1 : wn1 = ks.wnext.set u nxt := by simp [wn1, hprev, hu_tn]
        have hnd_get := k6_list_flatten_nodup_getElem wc.nodup hch_l
        by_cases hxl : l = x
        · subst hxl; rw [List.getElem?_eq_getElem hx1, Option.getD_some]
          simp only [chains1, List.getElem_set_self, hdone_eq, List.append_assoc, ks1, hwh1, hwn1]
          have hwc0 := wc.chains_wc l hx
          rw [List.getElem?_eq_getElem hch_l, Option.getD_some, hch_l_eq, hdone_eq,
            List.append_assoc] at hwc0
          have hnd_l := hnd_get.1; rw [hch_l_eq, hdone_eq, List.append_assoc] at hnd_l
          simpa [List.append_assoc] using k6_wchain_bypass hwc0 hnd_l hu_len hwn_len hnxt_eq.symm
        · have hu_not_x : u ∉ chains[x]'hx0 :=
            hnd_get.2 x (Ne.symm hxl) hx0 u (by rw [hch_l_eq, hdone_eq]; simp)
          have hwc0 := wc.chains_wc x hx
          rw [List.getElem?_eq_getElem hx1, Option.getD_some]
          rw [List.getElem?_eq_getElem hx0, Option.getD_some] at hwc0
          simp only [chains1, List.getElem_set_ne hxl, ks1, hwh1, hwn1]
          exact k6_wchain_congr hwc0 fun y hy =>
            (List.getElem?_set_ne (fun h : u = y => hu_not_x (h ▸ hy))).symm
  have hbnd1 : ∀ x < 2 * ks1.nv.toNat, ∀ u ∈ chains1[x]?.getD [],
      u < 2 * ks1.nc.toNat ∧ 2 ≤ k6ClauseSize ks1 (u / 2) ∧
      (ks1.arena[k6ClauseOff ks1 (u / 2) + (u % 2)]?.getD 0#32).toNat = x ∧
      let wb := ks1.wblit[u]?.getD 0#32
      let bv := (wb &&& 0x7FFFFFFF#32).toNat
      bv < 2 * ks1.nv.toNat ∧ bv ∈ k6ClauseLits ks1 (u / 2) ∧
      ((wb &&& 0x80000000#32) ≠ 0#32 ↔ k6ClauseSize ks1 (u / 2) = 2) ∧
      (k6ClauseSize ks1 (u / 2) = 2 →
        bv = (ks1.arena[k6ClauseOff ks1 (u / 2) + (u % 2 ^^^ 1)]?.getD 0#32).toNat) := by
    intro x hx u hu
    have hbu := wc.chains_bnd x hx u (hch1_sub x hx u hu)
    have hu_ne : u ≠ w0 := fun h => hw0_not_in (by
      rw [← h, List.mem_flatten]; have hx1 : x < chains1.length := by rw [hch1_len]; exact hx
      exact ⟨chains1[x], List.getElem_mem hx1, by simpa [List.getElem?_eq_getElem hx1] using hu⟩)
    have hdisj : ∀ (huc : u / 2 ≠ cid) (koff : Nat), koff < 2 →
        ks1.arena[k6ClauseOff ks (u / 2) + koff]? = ks.arena[k6ClauseOff ks (u / 2) + koff]? :=
      fun huc koff hkoff => by
        dsimp only [ks1, ar']
        have hu_lt : u / 2 < ks.nc.toNat := Nat.div_lt_of_lt_mul hbu.1
        have hne_i : ∀ idx, idx = off + slot ∨ idx = off + ri →
            idx ≠ k6ClauseOff ks (u / 2) + koff := fun idx hidx => by
          by_cases hlu : u / 2 < cid
          · have hmn := hinv.clauses.cl_mono (u / 2) cid hlu hcid_lt
            have := hbu.2.1; change k6ClauseOff ks (u / 2) + k6ClauseSize ks (u / 2) ≤ off at hmn
            rcases hidx with rfl | rfl <;> omega
          · have hmn := hinv.clauses.cl_mono cid (u / 2) (by omega) hu_lt
            change off + k6ClauseSize ks cid ≤ k6ClauseOff ks (u / 2) at hmn
            dsimp only [cid] at hmn; rcases hidx with rfl | rfl <;> omega
        rw [List.getElem?_set_ne (hne_i _ (Or.inr rfl)),
          List.getElem?_set_ne (hne_i _ (Or.inl rfl))]
    have har_u : ks1.arena[k6ClauseOff ks (u / 2) + u % 2]? =
        ks.arena[k6ClauseOff ks (u / 2) + u % 2]? := by
      by_cases huc : u / 2 = cid
      · dsimp only [ks1, ar']
        have hm1 : u % 2 ≠ slot := fun hm => hu_ne (by omega)
        have hm2 : u % 2 ≠ ri := by have := Nat.mod_lt u (by decide : 0 < 2); omega
        rw [huc, List.getElem?_set_ne (by dsimp only [off]; omega),
          List.getElem?_set_ne (by dsimp only [off]; omega)]
      · exact hdisj huc (u % 2) (Nat.mod_lt u (by decide))
    have hp_u : (k6ClauseLits ks1 (u / 2)).Perm (k6ClauseLits ks (u / 2)) :=
      hlits_perm_all (u / 2) (Nat.div_lt_of_lt_mul hbu.1)
    refine ⟨hbu.1, hbu.2.1, ?_, hbu.2.2.2.1, hp_u.mem_iff.mpr hbu.2.2.2.2.1,
      hbu.2.2.2.2.2.1, fun h2 => ?_⟩
    · change (ks1.arena[k6ClauseOff ks (u / 2) + u % 2]?.getD 0#32).toNat = x
      rw [har_u]; exact hbu.2.2.1
    · have huc_ne : u / 2 ≠ cid := fun heq => by rw [heq] at h2; exact hsz_ne2 h2
      have hk1 := hdisj huc_ne (u % 2 ^^^ 1) (by
        rcases Nat.mod_two_eq_zero_or_one u with h | h <;> simp [h])
      change ((ks1.wblit[u]?.getD 0#32) &&& 0x7FFFFFFF#32).toNat =
        (ks1.arena[k6ClauseOff ks (u / 2) + (u % 2 ^^^ 1)]?.getD 0#32).toNat
      rw [hk1]; exact hbu.2.2.2.2.2.2 h2
  have hw_tn : w.toNat = w0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold K6Layout.maxCl at hnc; omega)]
  have har_slot_repl :
      (ar'[k6ClauseOff ks (w.toNat / 2) + w.toNat % 2]?.getD 0#32).toNat = repl.toNat := by
    rw [hw_tn]; change (ar'[off + slot]?.getD 0#32).toNat = repl.toNat
    simp [ar', List.getElem?_set_ne (by omega : off + ri ≠ off + slot),
      List.getElem?_set_self (by dsimp only [off]; omega : off + slot < ks.arena.length)]
  have hot_mem1 : other.toNat ∈ k6ClauseLits ks1 (w.toNat / 2) := by
    have hp := hlits_perm_all cid hcid_lt
    rw [hw_tn]; exact hp.mem_iff.mpr hother_mem
  have hw_step0 := k6WatchStep0_preserves_watches_with hsh1 hch1_len hch1_nd hwc1 hbnd1
    (w := w) (l := repl) (ot := other)
    (by change w.toNat < 2 * ks.nc.toNat; rw [hw_tn]; exact hb0.1)
    hnc hnv hrepl_nv hother_nv hot_mem1
    (fun h2 => absurd h2 (by change k6ClauseSize ks (w.toNat / 2) ≠ 2; rw [hw_tn]; exact hsz_ne2))
    (by change 2 ≤ k6ClauseSize ks (w.toNat / 2); rw [hw_tn]; exact hsz_ge)
    har_slot_repl (by rw [hw_tn]; exact hw0_not_in)
  have hbf0 : (if k6ClauseSize ks1 (w.toNat / 2) = 2 then 0x80000000#32 else 0#32) = 0#32 := by
    have hne : k6ClauseSize ks1 (w.toNat / 2) ≠ 2 := by
      change k6ClauseSize ks (w.toNat / 2) ≠ 2; rw [hw_tn]; exact hsz_ne2
    simp only [hne, ite_false]
  dsimp only at hw_step0; rw [hbf0, BitVec.or_zero] at hw_step0
  have hrepl_ch1 : repl.toNat < chains1.length := by rw [hch1_len]; exact hrepl_nv
  let chains' := chains1.set repl.toNat (w.toNat :: chains1[repl.toNat]'hrepl_ch1)
  have hwc_cur' : K6WChainCursor ks' l chains' done todo' prev nxt := by
    have hch'_l : l < chains'.length := by
      simp only [chains', List.length_set]; rw [hch1_len]; exact hl
    have hcl'_eq : chains'[l]?.getD [] = done ++ todo' := by
      rw [List.getElem?_eq_getElem hch'_l, Option.getD_some]
      simp only [chains', List.getElem_set_ne hrepl_ne, chains1, List.getElem_set_self]
    have hnd_l := (k6_list_flatten_nodup_getElem wc.nodup hch_l).1
    have hw0_nt : w0 ∉ todo' := by
      rw [hch_l_eq] at hnd_l; exact (List.nodup_cons.mp (List.nodup_append.mp hnd_l).2.1).1
    have htail1 : K5WChain ks1.wnext nxt todo' := by
      by_cases hprev : prev = 0xFFFFFFFF#32
      · simp [ks1, wn1, hprev, htail_ks]
      · rcases wc.prev_rel with ⟨_, hp, _⟩ | ⟨pfx, u, hde, hp_eq, hu_len, _⟩
        · exact absurd hp hprev
        · have hu_2c : u < 2 * L.maxCl := by rw [hsh.wnext_len] at hu_len; exact hu_len
          have hu_tn : prev.toNat = u := by
            rw [hp_eq, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by unfold K6Layout.maxCl at hu_2c; omega)]
          have hu_nt : u ∉ todo' := by
            rw [hch_l_eq, hde] at hnd_l
            have hd := (List.nodup_append.mp hnd_l).2.2 u (by simp)
            exact fun h => hd u (List.mem_cons_of_mem _ h) rfl
          simp only [ks1, wn1, hprev, ↓reduceIte, hu_tn]
          exact k6_wchain_congr htail_ks fun y hy =>
            (List.getElem?_set_ne (fun h : u = y => hu_nt (h ▸ hy))).symm
    have htail' : K5WChain ks'.wnext nxt todo' := by
      change K5WChain (ks1.wnext.set w.toNat _) nxt todo'; rw [hw_tn]
      exact k6_wchain_congr htail1 fun y hy =>
        (List.getElem?_set_ne (fun h : w0 = y => hw0_nt (h ▸ hy))).symm
    have hprev' : (done = [] ∧ prev = 0xFFFFFFFF#32 ∧ ks'.whead[l]?.getD 0xFFFFFFFF#32 = nxt) ∨
        (∃ pfx u, done = pfx ++ [u] ∧ prev = BitVec.ofNat 32 u ∧
          u < ks'.wnext.length ∧ ks'.wnext[u]?.getD 0xFFFFFFFF#32 = nxt) := by
      by_cases hprev : prev = 0xFFFFFFFF#32
      · left; refine ⟨hdone_elim hprev, hprev, ?_⟩
        change (ks1.whead.set repl.toNat w)[l]?.getD 0xFFFFFFFF#32 = nxt
        rw [List.getElem?_set_ne hrepl_ne]; change wh1[l]?.getD 0xFFFFFFFF#32 = nxt
        simp only [wh1, hprev, ↓reduceIte, List.getElem?_set_self hwh_len, Option.getD_some]
      · right
        rcases wc.prev_rel with ⟨_, hp, _⟩ | ⟨pfx, u, hde, hp_eq, hu_len, _⟩
        · exact absurd hp hprev
        · have hu_2c : u < 2 * L.maxCl := by rw [hsh.wnext_len] at hu_len; exact hu_len
          have hu_tn : prev.toNat = u := by
            rw [hp_eq, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by unfold K6Layout.maxCl at hu_2c; omega)]
          have hune : w0 ≠ u := fun heq => by
            rw [hch_l_eq, hde] at hnd_l
            exact (List.nodup_append.mp hnd_l).2.2 u (by simp) w0 List.mem_cons_self heq.symm
          refine ⟨pfx, u, hde, hp_eq, by simpa [ks', k6WatchStep0, ks1, wn1, hprev] using hu_len,
            ?_⟩
          change (ks1.wnext.set w.toNat _)[u]?.getD 0xFFFFFFFF#32 = nxt
          rw [hw_tn, List.getElem?_set_ne hune]; change wn1[u]?.getD 0xFFFFFFFF#32 = nxt
          simp only [wn1, hprev, ↓reduceIte, hu_tn, List.getElem?_set_self hu_len, Option.getD_some]
    exact ⟨hw_step0.1, hw_step0.2.1, hcl'_eq, hw_step0.2.2.1, hw_step0.2.2.2.1, htail', hprev'⟩
  exact ⟨⟨hsh', hcl', hwc_cur'.watchesOk,
    k6BaseAssignOk_cast hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl, hrsn'⟩, chains', hwc_cur'⟩

theorem k6FlipFinish_preserves {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) {lit : BitVec 32} (hlit : lit.toNat < 2 * ks.nv.toNat)
    (hval1 : ks.vals[lit.toNat]? = some 1#32)
    (hlvl_nz : ks.lvlArr[(lit >>> (1 : Nat)).toNat]?.getD 0#32 ≠ 0#32) :
    K6Inv L P ((ks.putArr .vals lit.toNat 2#32).putArr .vals (lit ^^^ 1#32).toNat 1#32) := by
  let ks' := (ks.putArr .vals lit.toNat 2#32).putArr .vals (lit ^^^ 1#32).toNat 1#32
  have := L.hmaxV; have hsh := hinv.shapes; have hnv := hinv.clauses.nv_le
  obtain ⟨hv_eq, _⟩ := k6_bv32_div2_lt hlit
  obtain ⟨hn_eq, _⟩ := k6_bv32_xor1_lt hlit
  have hl_ne : lit.toNat ≠ (lit ^^^ 1#32).toNat := by
    rw [hn_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl]
    rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  have hlen_v : lit.toNat < ks.vals.length := by rw [hsh.vals_len]; omega
  have hlen_nl : (lit ^^^ 1#32).toNat < ks.vals.length := by
    rw [hsh.vals_len, hn_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl]
    rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  have hval_lit : ks'.vals[lit.toNat]? = some 2#32 := by
    change ((ks.vals.set lit.toNat 2#32).set (lit ^^^ 1#32).toNat 1#32)[lit.toNat]? = some 2#32
    rw [List.getElem?_set_ne hl_ne.symm, List.getElem?_set_self hlen_v]
  have hval_nl : ks'.vals[(lit ^^^ 1#32).toNat]? = some 1#32 := by
    change ((ks.vals.set lit.toNat 2#32).set (lit ^^^ 1#32).toNat 1#32)[(lit ^^^ 1#32).toNat]? =
      some 1#32
    rw [List.getElem?_set_self (by simp; exact hlen_nl)]
  have hval_other : ∀ x, x / 2 ≠ lit.toNat / 2 → ks'.vals[x]? = ks.vals[x]? := fun x hx => by
    have h1 : x ≠ lit.toNat := fun h => hx (h ▸ rfl)
    have h2 : x ≠ (lit ^^^ 1#32).toNat := fun h => by
      have : x / 2 = (lit.toNat ^^^ 1) / 2 := by
        rw [h, hn_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl]
      rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    change ((ks.vals.set lit.toNat 2#32).set (lit ^^^ 1#32).toNat 1#32)[x]? = ks.vals[x]?
    rw [List.getElem?_set_ne h2.symm, List.getElem?_set_ne h1.symm]
  have hba' : K6BaseAssignOk P ks' := by
    have h0 := hinv.assign
    refine ⟨h0.trl_end_le, h0.prop_le, h0.unass_eq, ?_, ?_, ?_, h0.trl_nodup, h0.trl_lt,
      h0.trl_lvl_le, ?_, h0.trl_lvl_mono, h0.dec_earliest, ?_⟩
    · intro l hl; by_cases hv : l / 2 = lit.toNat / 2
      · have he : l = lit.toNat ∨ l = (lit ^^^ 1#32).toNat := by
          rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;>
            rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
              (rw [hn_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl]; omega)
        rcases he with rfl | rfl
        · rw [hval_lit]; exact Or.inr (Or.inr rfl)
        · rw [hval_nl]; exact Or.inr (Or.inl rfl)
      · rw [hval_other l hv]; exact h0.vals_dom l hl
    · intro l hl; by_cases hv : l / 2 = lit.toNat / 2
      · have he : l = lit.toNat ∨ l = (lit ^^^ 1#32).toNat := by
          rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;>
            rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
              (rw [hn_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl]; omega)
        rcases he with rfl | rfl
        · rw [hval_lit,
            show lit.toNat ^^^ 1 = (lit ^^^ 1#32).toNat by
              rw [hn_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl],
            hval_nl]; simp
        · rw [hval_nl,
            show (lit ^^^ 1#32).toNat ^^^ 1 = lit.toNat by
              rw [hn_eq]; exact litNeg_litNeg _,
            hval_lit]; simp
      · have hnv' : (l ^^^ 1) / 2 ≠ lit.toNat / 2 := by
          rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [hval_other l hv, hval_other (l ^^^ 1) hnv']; exact h0.vals_neg_iff l hl
    · intro l hl; by_cases hv : l / 2 = lit.toNat / 2
      · have hex := (h0.vals_nz_iff_trl lit.toNat hlit).mp (by simp [hval1])
        have hnz_new : ks'.vals[l]?.getD 0#32 ≠ 0#32 := by
          have he : l = lit.toNat ∨ l = (lit ^^^ 1#32).toNat := by
            rcases k6_nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;>
              rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
                (rw [hn_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl]; omega)
          rcases he with rfl | rfl
          · rw [hval_lit]; decide
          · rw [hval_nl]; decide
        exact ⟨fun _ => by
          dsimp only [ks', K6State.putArr]; simpa [hv] using hex, fun _ => hnz_new⟩
      · rw [hval_other l hv]; exact h0.vals_nz_iff_trl l hl
    · intro v hv hv0; by_cases hvq : v = lit.toNat / 2
      · exfalso; subst hvq; rcases k6_nat_xor1_cases lit.toNat with ⟨ha, _⟩ | ⟨_, hb⟩
        · rw [← ha, hval_lit] at hv0; cases hv0
        · rw [show 2 * (lit.toNat / 2) = (lit ^^^ 1#32).toNat by
            rw [hn_eq, show litNeg lit.toNat = lit.toNat ^^^ 1 from rfl]; omega, hval_nl] at hv0
          cases hv0
      · rw [hval_other (2 * v) (by omega)] at hv0; exact h0.unass_lvl_zero v hv hv0
    · intro i hi; dsimp only [ks', K6State.putArr]; intro hlv
      have hne_v : (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := fun heq => by
        rw [heq, ← hv_eq] at hlv; exact hlvl_nz hlv
      have hne_x : ((ks.trl[i]?.getD 0#32).toNat ^^^ 1) / 2 ≠ lit.toNat / 2 := by
        rcases k6_nat_xor1_cases (ks.trl[i]?.getD 0#32).toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
      have h0l := h0.lvl0_ok i hi hlv
      change ks'.vals[(ks.trl[i]?.getD 0#32).toNat]? = some 1#32 ∧
        ks'.vals[(ks.trl[i]?.getD 0#32).toNat ^^^ 1]? = some 2#32 ∧ _
      rw [hval_other _ hne_v, hval_other _ hne_x]; exact h0l
  exact ⟨(hsh.putArr .vals _ _).putArr .vals _ _,
    k6ClausesOk_cast hinv.clauses rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
    by dsimp only [K6State.putArr]; exact hinv.watches,
    hba', by dsimp only [K6State.putArr]; exact hinv.reasons⟩

end LeanQbe.T.Examples.Kissat.Proof.Kitten

end
