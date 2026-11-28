/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.Layout

/-!
# Balanced `SepTree` Memory Ownership & Access Tactics for `K6State` (`Kissat.Proof.Kitten.Mem`)

Zero legacy `Full*` imports; zero `@[expose]` on theorems/lemmas (`@[expose]` on defs only).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Kitten

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. Balanced 18-Leaf `SepTree` (`K6Tree`, `K6Mem`) & Scratch Bridges -/

@[expose] def k6Path : Nat → List Bool
  | 0  => [false, false, false, false]
  | 1  => [false, false, false, true]
  | 2  => [false, false, true, false]
  | 3  => [false, false, true, true]
  | 4  => [false, true, false, false]
  | 5  => [false, true, false, true]
  | 6  => [false, true, true, false]
  | 7  => [false, true, true, true, false]
  | 8  => [false, true, true, true, true]
  | 9  => [true, false, false, false]
  | 10 => [true, false, false, true]
  | 11 => [true, false, true, false]
  | 12 => [true, false, true, true]
  | 13 => [true, true, false, false]
  | 14 => [true, true, false, true]
  | 15 => [true, true, true, false]
  | 16 => [true, true, true, true, false]
  | _  => [true, true, true, true, true]

@[expose] def K6Tree (L : K6Layout) (kPtr : BitVec 64) (ks : K6State) : SepTree :=
  let a (off : Nat) (xs : List (BitVec 32)) : SepTree :=
    .leaf (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * off)) xs)
  let tL :=
    .node
      (.node (.node (.leaf (array (t := i32) kPtr (k6HdrWords ks))) (a L.oLvl ks.lvlArr))
             (.node (a L.oRsn ks.rsn) (a L.oQPrev ks.qprev)))
      (.node (.node (a L.oQNext ks.qnext) (a L.oQStamp ks.qstampArr))
             (.node (a L.oTrl ks.trl) (.node (a L.oFlags ks.flags) (a L.oAna ks.ana))))
  let tR :=
    .node
      (.node (.node (a L.oKl ks.kl) (a L.oAssump ks.assump))
             (.node (a L.oVals ks.vals) (a L.oWHead ks.whead)))
      (.node (.node (a L.oWNext ks.wnext) (a L.oWBlit ks.wblit))
             (.node (a L.oClOff ks.clOff) (.node (a L.oClSz ks.clSz) (a L.oArena ks.arena))))
  .node tL tR

@[expose] def K6Mem (L : K6Layout) (kPtr : BitVec 64) (ks : K6State) : Mem 64 → Prop :=
  (K6Tree L kPtr ks).eval

private theorem k6_arr32_append (a : BitVec 64) (xs ys : List (BitVec 32)) (k0 : Nat)
    (hk0 : k0 = xs.length) :
    array (t := i32) a (xs ++ ys) =
      (array (t := i32) a xs ⋆ array (t := i32) (a + BitVec.ofNat 64 (4 * k0)) ys) := by
  rw [array_append, show (i32 : Ty).bytes = 4 from rfl, hk0]

private theorem array_toSlab_eq_k6Mem {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
    (hsh : ks.ShapesOk L) :
    array (t := i32) kPtr ks.toSlab = K6Mem L kPtr ks := by
  have hkh := k6HdrWords_length hsh
  rcases hsh with ⟨_, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, _⟩
  unfold K6State.toSlab K6Mem K6Tree
  dsimp only [SepTree.eval]
  rw [k6_arr32_append _ _ _ L.oLvl hkh.symm]
  rw [k6_arr32_append _ _ _ L.maxV h1.symm, k6_ptr_add_off,
    show L.oLvl + L.maxV = L.oRsn from rfl]
  rw [k6_arr32_append _ _ _ L.maxV h2.symm, k6_ptr_add_off,
    show L.oRsn + L.maxV = L.oQPrev by unfold K6Layout.oRsn K6Layout.oQPrev; omega]
  rw [k6_arr32_append _ _ _ L.maxV h3.symm, k6_ptr_add_off,
    show L.oQPrev + L.maxV = L.oQNext by unfold K6Layout.oQPrev K6Layout.oQNext; omega]
  rw [k6_arr32_append _ _ _ L.maxV h4.symm, k6_ptr_add_off,
    show L.oQNext + L.maxV = L.oQStamp by unfold K6Layout.oQNext K6Layout.oQStamp; omega]
  rw [k6_arr32_append _ _ _ L.maxV h5.symm, k6_ptr_add_off,
    show L.oQStamp + L.maxV = L.oTrl by unfold K6Layout.oQStamp K6Layout.oTrl; omega]
  rw [k6_arr32_append _ _ _ L.maxV h6.symm, k6_ptr_add_off,
    show L.oTrl + L.maxV = L.oFlags by unfold K6Layout.oTrl K6Layout.oFlags; omega]
  rw [k6_arr32_append _ _ _ L.maxV h7.symm, k6_ptr_add_off,
    show L.oFlags + L.maxV = L.oAna by unfold K6Layout.oFlags K6Layout.oAna; omega]
  rw [k6_arr32_append _ _ _ L.maxV h8.symm, k6_ptr_add_off,
    show L.oAna + L.maxV = L.oKl by unfold K6Layout.oAna K6Layout.oKl; omega]
  rw [k6_arr32_append _ _ _ L.maxV h9.symm, k6_ptr_add_off,
    show L.oKl + L.maxV = L.oAssump by unfold K6Layout.oKl K6Layout.oAssump; omega]
  rw [k6_arr32_append _ _ _ L.maxV h10.symm, k6_ptr_add_off,
    show L.oAssump + L.maxV = L.oVals by unfold K6Layout.oAssump K6Layout.oVals; omega]
  rw [k6_arr32_append _ _ _ (2 * L.maxV) h11.symm, k6_ptr_add_off,
    show L.oVals + 2 * L.maxV = L.oWHead by unfold K6Layout.oVals K6Layout.oWHead; omega]
  rw [k6_arr32_append _ _ _ (2 * L.maxV) h12.symm, k6_ptr_add_off,
    show L.oWHead + 2 * L.maxV = L.oWNext by unfold K6Layout.oWHead K6Layout.oWNext; omega]
  rw [k6_arr32_append _ _ _ (2 * L.maxCl) h13.symm, k6_ptr_add_off,
    show L.oWNext + 2 * L.maxCl = L.oWBlit by
      unfold K6Layout.oWNext K6Layout.oWBlit K6Layout.maxCl; omega]
  rw [k6_arr32_append _ _ _ (2 * L.maxCl) h14.symm, k6_ptr_add_off,
    show L.oWBlit + 2 * L.maxCl = L.oClOff by
      unfold K6Layout.oWBlit K6Layout.oClOff K6Layout.maxCl; omega]
  rw [k6_arr32_append _ _ _ L.maxCl h15.symm, k6_ptr_add_off,
    show L.oClOff + L.maxCl = L.oClSz by
      unfold K6Layout.oClOff K6Layout.oClSz K6Layout.maxCl; omega]
  rw [k6_arr32_append _ _ _ L.maxCl h16.symm, k6_ptr_add_off,
    show L.oClSz + L.maxCl = L.oArena by
      unfold K6Layout.oClSz K6Layout.oArena K6Layout.maxCl; omega]
  ac_rfl

theorem array_scratch_eq_k6 {L : K6Layout} {p : BitVec 64} {scr : List (BitVec 32)}
    (hlen : scr.length = L.scrLen) :
    array (t := i32) p scr =
      (array (t := i32) p (scr.take L.k6Base) ⋆
        K6Mem L (L.kPtr p) (K6State.ofSlab L (scr.drop L.k6Base))) := by
  have hkb : L.k6Base ≤ scr.length := by rw [hlen]; unfold K6Layout.scrLen; omega
  have hdrop : (scr.drop L.k6Base).length = L.k6Fixed + L.acap := by
    rw [List.length_drop, hlen]; unfold K6Layout.scrLen; omega
  have hsh : (K6State.ofSlab L (scr.drop L.k6Base)).ShapesOk L := K6State.shapesOk_ofSlab_eq hdrop
  have htk_len : (scr.take L.k6Base).length = L.k6Base := List.length_take_of_le hkb
  conv => lhs; rw [← List.take_append_drop L.k6Base scr]
  rw [k6_arr32_append p (scr.take L.k6Base) (scr.drop L.k6Base) L.k6Base htk_len.symm,
    k6_ptr_base_k6Base,
    ← K6State.toSlab_ofSlab (L := L) (xs := scr.drop L.k6Base)
      (by rw [hdrop]; unfold K6Layout.k6Fixed; omega),
    array_toSlab_eq_k6Mem hsh, K6State.ofSlab_toSlab hsh]

theorem k6_append_eq_array_scratch {L : K6Layout} {p : BitVec 64} {scrHead : List (BitVec 32)}
    {ks : K6State} (htk : scrHead.length = L.k6Base) (hsh : ks.ShapesOk L) :
    (array (t := i32) p scrHead ⋆ K6Mem L (L.kPtr p) ks) =
      array (t := i32) p (scrHead ++ ks.toSlab) := by
  rw [k6_arr32_append p scrHead ks.toSlab L.k6Base htk.symm, k6_ptr_base_k6Base,
    array_toSlab_eq_k6Mem hsh]

/-! ## 2. `FullK6Frame`, `FullMem` Join, & Frame Header Accessors -/

@[expose] def FullK6Frame (c : FullCfg) (L : K6Layout) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
  FullScrMetaArrs c s.scratch ⋆ array (t := i32) c.pDelayed s.scratch.delayed ⋆
  array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
  array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
  array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take L.k6Base) ⋆ c.pad

theorem fullMem_eq_k6Frame {c : FullCfg} {L : K6Layout} {s : FullState}
    (hlen : s.scratch.scratch_buf.length = L.scrLen) :
    FullMem c s =
      (FullK6Frame c L s ⋆
        K6Mem L (L.kPtr c.pScratchBuf)
          (K6State.ofSlab L (s.scratch.scratch_buf.drop L.k6Base))) := by
  unfold FullMem FullScratchArrays FullScrDynArrs FullK6Frame
  rw [array_scratch_eq_k6 hlen]; ac_rfl

theorem fullMem_join_k6 {c : FullCfg} {L : K6Layout} {s : FullState} {ks' : K6State}
    {R : Mem 64 → Prop} {m' : Mem 64}
    (hkbase : L.k6Base ≤ s.scratch.scratch_buf.length) (hsh : ks'.ShapesOk L)
    (hm : (FullK6Frame c L s ⋆ K6Mem L (L.kPtr c.pScratchBuf) ks' ⋆ R) m') :
    (FullMem c
      { s with scratch :=
        { s.scratch with scratch_buf := s.scratch.scratch_buf.take L.k6Base ++ ks'.toSlab } } ⋆
      R) m' := by
  have htk : (s.scratch.scratch_buf.take L.k6Base).length = L.k6Base :=
    List.length_take_of_le hkbase
  have hm1 : (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
        s.core.d_val ⋆
      array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
      FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
      FullScrMetaArrs c s.scratch ⋆ array (t := i32) c.pDelayed s.scratch.delayed ⋆
      array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
      array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
      (array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take L.k6Base) ⋆
        K6Mem L (L.kPtr c.pScratchBuf) ks') ⋆
      c.pad ⋆ R) m' := by
    unfold FullK6Frame at hm; exact sep_ac hm
  rw [k6_append_eq_array_scratch htk hsh] at hm1
  unfold FullMem FullScratchArrays FullScrDynArrs
  exact sep_ac hm1

theorem fullK6Frame_hdrGet {c : FullCfg} {L : K6Layout} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (i : Nat) (hi : i < 140) (hm : (FullK6Frame c L s ⋆ R) m) :
    loadVal m i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * i)) =
      some ((hdrTailWords c s)[i]'(by simpa using hi)) := by
  have h1 : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
        s.core.d_val ⋆
       FullCoreArrays c s.core ⋆ FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
       FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
       array (t := i32) c.pDelayed s.scratch.delayed ⋆
       array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
       array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
       array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take L.k6Base) ⋆ c.pad ⋆ R)) m := by
    unfold FullK6Frame at hm; exact sep_ac hm
  have hl := loadVal_array64 (i := i) (by rw [hdrTailWords_length]; exact hi) h1
  rwa [show c.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * i) =
    c.hdr + BitVec.ofNat 64 (32 + 8 * i) from ptr_add_ofNat c.hdr 32 (8 * i)] at hl

theorem fullK6Frame_fuel_store {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hm : (FullK6Frame c L s ⋆ R) m) :
    storeOk m i64 (c.hdr + 168) ∧
      (FullK6Frame c L { s with core := { s.core with fuel := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 168) v) := by
  have h1 : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
        s.core.d_val ⋆
       FullCoreArrays c s.core ⋆ FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
       FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
       array (t := i32) c.pDelayed s.scratch.delayed ⋆
       array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
       array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
       array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take L.k6Base) ⋆ c.pad ⋆ R)) m := by
    unfold FullK6Frame at hm; exact sep_ac hm
  obtain ⟨hok, hst⟩ := store_array64 (i := 17) v (by rw [hdrTailWords_length]; decide) h1
  rw [show c.hdr + 32 + BitVec.ofNat 64 (8 * 17) = c.hdr + 168 from
    ptr_add_ofNat c.hdr 32 136] at hok hst
  have hset : (hdrTailWords c s).set 17 v =
      hdrTailWords c { s with core := { s.core with fuel := v } } := by
    have hs := (HdrWordField.hdrTailWords_set .fuel rfl c s v).symm
    simpa [HdrWordField.wordIdx, HdrWordField.set] using hs
  rw [hset] at hst; unfold FullK6Frame; exact ⟨hok, sep_ac hst⟩

/-! ## 3. Non-Expanding `putHdr`/`putArr`, `K6MemA`, & Scoped Tactics -/

inductive K6HdrField where
  | nv | nc | lvl | prop | trl_end | unass | incons | qfirst | qlast | qsearch | qstamp
  | ticks | tick_lim | alen | acap | nassump | nkl | nana | status | phase
  | openCnt | max_v | max_orig | max_cl | neq
  deriving DecidableEq

inductive K6ArrField where
  | lvlArr | rsn | qprev | qnext | qstampArr | trl | flags | ana | kl | assump
  | vals | whead | wnext | wblit | clOff | clSz | arena
  deriving DecidableEq

@[expose] def K6State.putHdr (ks : K6State) (f : K6HdrField) (v : BitVec 32) : K6State :=
  K6HdrField.casesOn (motive := fun _ => K6State) f
    { ks with nv := v } { ks with nc := v } { ks with lvl := v }
    { ks with prop := v } { ks with trl_end := v } { ks with unass := v }
    { ks with incons := v } { ks with qfirst := v } { ks with qlast := v }
    { ks with qsearch := v } { ks with qstamp := v } { ks with ticks := v }
    { ks with tick_lim := v } { ks with alen := v } { ks with acap := v }
    { ks with nassump := v } { ks with nkl := v } { ks with nana := v }
    { ks with status := v } { ks with phase := v } { ks with openCnt := v }
    { ks with max_v := v } { ks with max_orig := v } { ks with max_cl := v }
    { ks with neq := v }

@[expose] def K6State.putArr (ks : K6State) (f : K6ArrField) (i : Nat) (v : BitVec 32) :
    K6State :=
  K6ArrField.casesOn (motive := fun _ => K6State) f
    { ks with lvlArr := ks.lvlArr.set i v }
    { ks with rsn := ks.rsn.set i v }
    { ks with qprev := ks.qprev.set i v }
    { ks with qnext := ks.qnext.set i v }
    { ks with qstampArr := ks.qstampArr.set i v }
    { ks with trl := ks.trl.set i v }
    { ks with flags := ks.flags.set i v }
    { ks with ana := ks.ana.set i v }
    { ks with kl := ks.kl.set i v }
    { ks with assump := ks.assump.set i v }
    { ks with vals := ks.vals.set i v }
    { ks with whead := ks.whead.set i v }
    { ks with wnext := ks.wnext.set i v }
    { ks with wblit := ks.wblit.set i v }
    { ks with clOff := ks.clOff.set i v }
    { ks with clSz := ks.clSz.set i v }
    { ks with arena := ks.arena.set i v }

theorem K6State.ShapesOk.putHdr {L : K6Layout} {ks : K6State}
    (h : ks.ShapesOk L) (f : K6HdrField) (v : BitVec 32) :
    (ks.putHdr f v).ShapesOk L := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
  cases f <;> exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem K6State.ShapesOk.putArr {L : K6Layout} {ks : K6State}
    (h : ks.ShapesOk L) (f : K6ArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).ShapesOk L := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
  cases f <;> refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simpa [K6State.putArr]

theorem k6State_ext {a b : K6State}
    (h1 : a.nv = b.nv) (h2 : a.nc = b.nc) (h3 : a.lvl = b.lvl) (h4 : a.prop = b.prop)
    (h5 : a.trl_end = b.trl_end) (h6 : a.unass = b.unass) (h7 : a.incons = b.incons)
    (h8 : a.qfirst = b.qfirst) (h9 : a.qlast = b.qlast) (h10 : a.qsearch = b.qsearch)
    (h11 : a.qstamp = b.qstamp) (h12 : a.ticks = b.ticks) (h13 : a.tick_lim = b.tick_lim)
    (h14 : a.alen = b.alen) (h15 : a.acap = b.acap) (h16 : a.nassump = b.nassump)
    (h17 : a.nkl = b.nkl) (h18 : a.nana = b.nana) (h19 : a.status = b.status)
    (h20 : a.phase = b.phase) (h21 : a.openCnt = b.openCnt) (h22 : a.max_v = b.max_v)
    (h23 : a.max_orig = b.max_orig) (h24 : a.max_cl = b.max_cl) (h25 : a.neq = b.neq)
    (h26 : a.hdrTail = b.hdrTail) (h27 : a.lvlArr = b.lvlArr) (h28 : a.rsn = b.rsn)
    (h29 : a.qprev = b.qprev) (h30 : a.qnext = b.qnext) (h31 : a.qstampArr = b.qstampArr)
    (h32 : a.trl = b.trl) (h33 : a.flags = b.flags) (h34 : a.ana = b.ana) (h35 : a.kl = b.kl)
    (h36 : a.assump = b.assump) (h37 : a.vals = b.vals) (h38 : a.whead = b.whead)
    (h39 : a.wnext = b.wnext) (h40 : a.wblit = b.wblit) (h41 : a.clOff = b.clOff)
    (h42 : a.clSz = b.clSz) (h43 : a.arena = b.arena) : a = b := by
  cases a; cases b; simp only [K6State.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38,
    h39, h40, h41, h42, h43⟩

@[expose] def K6MemA (L : K6Layout) (kPtr : BitVec 64) (ks : K6State) : Mem 64 → Prop :=
  fun m => K6Mem L kPtr ks m ∧ ks.ShapesOk L

theorem k6Mem_to_amem {L : K6Layout} {kPtr : BitVec 64} {ks : K6State} {R : Mem 64 → Prop}
    {m : Mem 64} (hsh : ks.ShapesOk L) (hm : (K6Mem L kPtr ks ⋆ R) m) :
    (K6MemA L kPtr ks ⋆ R) m :=
  sep_mono (fun _ h => ⟨h, hsh⟩) hm

theorem k6MemA_to_mem {L : K6Layout} {kPtr : BitVec 64} {ks : K6State} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (K6MemA L kPtr ks ⋆ R) m) :
    ks.ShapesOk L ∧ (K6Mem L kPtr ks ⋆ R) m :=
  sep_pure_l.mp (sep_mono (fun _ ⟨h1, h2⟩ => ⟨h2, h1⟩) hm)

private theorem k6HdrGet {L : K6Layout} {kPtr : BitVec 64} {ks : K6State} {R : Mem 64 → Prop}
    {m : Mem 64} (idx : Nat) (hlt : idx < 32) (v : BitVec 32)
    (heq : ∀ hsh : ks.ShapesOk L,
      (k6HdrWords ks)[idx]'(by rw [k6HdrWords_length hsh]; exact hlt) = v)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 idx * 4) = some v := by
  obtain ⟨hsh, hm'⟩ := k6MemA_to_mem hm
  have hi : idx < (k6HdrWords ks).length := by rw [k6HdrWords_length hsh]; exact hlt
  rw [k6_ptr_nat_mul4 kPtr idx (by omega), ← heq hsh]
  exact sepTree_arr_get (t := K6Tree L kPtr ks) (p := k6Path 0) rfl (by decide) hi hm'

private theorem k6HdrPut {L : K6Layout} {kPtr : BitVec 64} {ks : K6State} {R : Mem 64 → Prop}
    {m : Mem 64} (f : K6HdrField) (idx : Nat) (v : BitVec 32) (hlt : idx < 32)
    (hset : (k6HdrWords ks).set idx v = k6HdrWords (ks.putHdr f v))
    (heq : ((K6Tree L kPtr ks).set (k6Path 0)
      (array (t := i32) kPtr (k6HdrWords (ks.putHdr f v)))).eval = K6Mem L kPtr (ks.putHdr f v))
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 idx * 4) ∧
      (K6MemA L kPtr (ks.putHdr f v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 idx * 4) v) := by
  obtain ⟨hsh, hm'⟩ := k6MemA_to_mem hm
  have hi : idx < (k6HdrWords ks).length := by rw [k6HdrWords_length hsh]; exact hlt
  rw [k6_ptr_nat_mul4 kPtr idx (by omega)]
  obtain ⟨hok, hst⟩ := sepTree_arr_put (t := K6Tree L kPtr ks) (p := k6Path 0) rfl (by decide) v hi
    (hset ▸ heq) hm'
  exact ⟨hok, k6Mem_to_amem (hsh.putHdr f v) hst⟩

private theorem k6ArrGetBase {L : K6Layout} {kPtr : BitVec 64} {ks : K6State} (p : List Bool)
    (kOff n : Nat) (xs : List (BitVec 32)) {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : ks.ShapesOk L → xs.length = n)
    (hget : (K6Tree L kPtr ks).get p = array (t := i32) (kPtr + BitVec.ofNat 64 (4 * kOff)) xs)
    {i : BitVec 32} (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < n)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 ((kPtr + BitVec.ofNat 64 (4 * kOff)) + i.setWidth 64 * 4) =
      some (xs[i.toNat]?.getD 0#32) := by
  obtain ⟨hsh, hm'⟩ := k6MemA_to_mem hm
  have hi' : i.toNat < xs.length := by rw [hlen hsh]; exact hi
  rw [List.getElem?_eq_getElem hi', Option.getD_some,
    show i.setWidth 64 = BitVec.ofNat 64 i.toNat from by apply BitVec.eq_of_toNat_eq; simp,
    k6_ptr_nat_mul4 _ i.toNat hlt]
  exact sepTree_arr_get (t := K6Tree L kPtr ks) (p := p) hget (by decide) hi' hm'

private theorem k6ArrPutBase {L : K6Layout} {kPtr : BitVec 64} {ks : K6State} (p : List Bool)
    (f : K6ArrField) (kOff n : Nat) (xs : List (BitVec 32)) {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : ks.ShapesOk L → xs.length = n)
    (hget : (K6Tree L kPtr ks).get p = array (t := i32) (kPtr + BitVec.ofNat 64 (4 * kOff)) xs)
    (v : BitVec 32) {i : BitVec 32} (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < n)
    (heq : ((K6Tree L kPtr ks).set p
      (array (t := i32) (kPtr + BitVec.ofNat 64 (4 * kOff)) (xs.set i.toNat v))).eval =
      K6Mem L kPtr (ks.putArr f i.toNat v))
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * kOff)) + i.setWidth 64 * 4) ∧
      (K6MemA L kPtr (ks.putArr f i.toNat v) ⋆ R)
        (storeMem m i32 ((kPtr + BitVec.ofNat 64 (4 * kOff)) + i.setWidth 64 * 4) v) := by
  obtain ⟨hsh, hm'⟩ := k6MemA_to_mem hm
  have hi' : i.toNat < xs.length := by rw [hlen hsh]; exact hi
  rw [show i.setWidth 64 = BitVec.ofNat 64 i.toNat from by apply BitVec.eq_of_toNat_eq; simp,
    k6_ptr_nat_mul4 _ i.toNat hlt]
  obtain ⟨hok, hst⟩ := sepTree_arr_put (t := K6Tree L kPtr ks) (p := p) hget (by decide) v hi'
    heq hm'
  exact ⟨hok, k6Mem_to_amem (hsh.putArr f i.toNat v) hst⟩

theorem fullAddClause6_mem_to_ka {c : FullCfg} {L : K6Layout} {s : FullState}
    {scr xs : List (BitVec 32)} {litsPtr : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {ks : K6State} (hlen : scr.length = L.scrLen) (hsh : ks.ShapesOk L)
    (hof : K6State.ofSlab L (scr.drop L.k6Base) = ks)
    (hm : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      array (t := i32) c.pScratchBuf scr ⋆ array (t := i32) litsPtr xs ⋆ R) m) :
    (K6MemA L (L.kPtr c.pScratchBuf) ks ⋆
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        (array (t := i32) litsPtr xs ⋆
          (array (t := i32) c.pScratchBuf (scr.take L.k6Base) ⋆ R)))) m := by
  rw [array_scratch_eq_k6 hlen, hof] at hm
  exact k6Mem_to_amem hsh (sep_ac hm)

theorem fullAddClause6_ka_to_mem {c : FullCfg} {L : K6Layout} {s : FullState}
    {scr xs : List (BitVec 32)} {litsPtr : BitVec 64} {R : Mem 64 → Prop} {m' : Mem 64}
    {ks' : K6State} (hkbase : L.k6Base ≤ scr.length) (hsh' : ks'.ShapesOk L)
    (hm' : (K6MemA L (L.kPtr c.pScratchBuf) ks' ⋆
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
        (array (t := i32) litsPtr xs ⋆
          (array (t := i32) c.pScratchBuf (scr.take L.k6Base) ⋆ R)))) m') :
    let scr' := scr.take L.k6Base ++ ks'.toSlab
    let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
    (array64 (c.hdr + 32) (hdrTailWords c s') ⋆
      array (t := i32) c.pScratchBuf scr' ⋆ array (t := i32) litsPtr xs ⋆ R) m' := by
  intro scr' s'
  obtain ⟨_, hm0⟩ := k6MemA_to_mem hm'
  have htk : (scr.take L.k6Base).length = L.k6Base := List.length_take_of_le hkbase
  have hm1 : (array64 (c.hdr + 32) (hdrTailWords c s') ⋆
      ((array (t := i32) c.pScratchBuf (scr.take L.k6Base) ⋆
        K6Mem L (L.kPtr c.pScratchBuf) ks') ⋆
      (array (t := i32) litsPtr xs ⋆ R))) m' := by
    have hhdr : hdrTailWords c s' = hdrTailWords c s := rfl
    rw [hhdr]; exact sep_ac hm0
  rw [k6_append_eq_array_scratch htk hsh'] at hm1; exact sep_ac hm1

namespace K6MemATactics

attribute [scoped bv_c0] bv32_lshr_1 bv32_and_1 bv32_xor_1 List.length_set Bool.false_eq_true

section FrameAccess
variable {c : FullCfg} {L : K6Layout} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}

@[scoped c0_load] theorem load_k6f_scratch_cap (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 928) = some (BitVec.ofNat 64 c.scratch_cap) :=
  FullArenaTactics.load_full_scratch_cap hm

@[scoped c0_load] theorem load_k6fr_scratch_cap (hm : (FullK6Frame c L s ⋆ R) m) :
    loadVal m i64 (c.hdr + 928) = some (BitVec.ofNat 64 c.scratch_cap) := by
  have h := fullK6Frame_hdrGet 112 (by decide) hm
  have hg : (hdrTailWords c s)[112] = BitVec.ofNat 64 c.scratch_cap :=
    HdrWordField.hdrTailWords_get .scratch_cap (by decide) c s
  rwa [show 32 + 8 * 112 = 928 from rfl, hg] at h

@[scoped c0_load] theorem load_k6f_scratch_buf (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf :=
  FullArenaTactics.load_full_scratch_buf_ptr hm

@[scoped c0_load] theorem load_k6fr_scratch_buf (hm : (FullK6Frame c L s ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf := by
  have h := fullK6Frame_hdrGet 111 (by decide) hm
  have hg : (hdrTailWords c s)[111] = c.pScratchBuf :=
    HdrWordField.hdrTailWords_get .scratch_buf_ptr (by decide) c s
  rwa [show 32 + 8 * 111 = 920 from rfl, hg] at h

@[scoped c0_load] theorem load_k6fr_fuel (hm : (FullK6Frame c L s ⋆ R) m) :
    loadVal m i64 (c.hdr + 168) = some s.core.fuel := by
  have h := fullK6Frame_hdrGet 17 (by decide) hm
  have hg : (hdrTailWords c s)[17] = s.core.fuel :=
    HdrWordField.hdrTailWords_get .fuel (by decide) c s
  rwa [show 32 + 8 * 17 = 168 from rfl, hg] at h

@[scoped c0_store] theorem store_k6fr_fuel (v : BitVec 64) (hm : (FullK6Frame c L s ⋆ R) m) :
    storeOk m i64 (c.hdr + 168) ∧
      (FullK6Frame c L { s with core := { s.core with fuel := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 168) v) := fullK6Frame_fuel_store v hm

@[scoped c0_load] theorem load_k6hdrTail_scratch_cap
    (hm : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ R) m) :
    loadVal m i64 (c.hdr + 928) = some (BitVec.ofNat 64 c.scratch_cap) := by
  have h := loadVal_array64 (i := 112) (by rw [hdrTailWords_length]; decide) hm
  have hg : (hdrTailWords c s)[112] = BitVec.ofNat 64 c.scratch_cap :=
    HdrWordField.hdrTailWords_get .scratch_cap (by decide) c s
  rwa [show c.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * 112) = c.hdr + 928 from
    ptr_add_ofNat c.hdr 32 896, hg] at h

@[scoped c0_load] theorem load_k6hdrTail_scratch_buf
    (hm : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf := by
  have h := loadVal_array64 (i := 111) (by rw [hdrTailWords_length]; decide) hm
  have hg : (hdrTailWords c s)[111] = c.pScratchBuf :=
    HdrWordField.hdrTailWords_get .scratch_buf_ptr (by decide) c s
  rwa [show c.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * 111) = c.hdr + 920 from
    ptr_add_ofNat c.hdr 32 888, hg] at h

@[scoped c0_load] theorem load_k6hdrTail_glue_used
    (hm : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ R) m) :
    loadVal m i64 (c.hdr + 432) = some c.pGlueUsed := by
  have h := loadVal_array64 (i := 50) (by rw [hdrTailWords_length]; decide) hm
  have hg : (hdrTailWords c s)[50] = c.pGlueUsed :=
    HdrWordField.hdrTailWords_get .glue_used_ptr (by decide) c s
  rwa [show c.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * 50) = c.hdr + 432 from
    ptr_add_ofNat c.hdr 32 400, hg] at h

@[scoped c0_load] theorem load_k6fr_glue_used (hm : (FullK6Frame c L s ⋆ R) m) :
    loadVal m i64 (c.hdr + 432) = some c.pGlueUsed := by
  have h := fullK6Frame_hdrGet 50 (by decide) hm
  have hg : (hdrTailWords c s)[50] = c.pGlueUsed :=
    HdrWordField.hdrTailWords_get .glue_used_ptr (by decide) c s
  rwa [show 32 + 8 * 50 = 432 from rfl, hg] at h

@[scoped c0_load] theorem load_k6arr32_z0 {a : BitVec 64} {xs : List (BitVec 32)}
    (hi : 0 < xs.length) (hm : (array (t := i32) a xs ⋆ R) m) :
    loadVal m i32 a = some xs[0] := by
  have h := loadVal_array (t := i32) (a := a) (xs := xs) (i := 0) (by decide) hi hm
  simpa [show (i32 : Ty).bytes * 0 = 0 from rfl] using h

@[scoped c0_load] theorem load_k6arr32_z1 {a : BitVec 64} {xs : List (BitVec 32)}
    (hi : 1 < xs.length) (hm : (array (t := i32) a xs ⋆ R) m) :
    loadVal m i32 (a + BitVec.ofNat 64 1 * 4) = some xs[1] := by
  have h := loadVal_array (t := i32) (a := a) (xs := xs) (i := 1) (by decide) hi hm
  rw [show BitVec.ofNat 64 ((i32 : Ty).bytes * 1) = BitVec.ofNat 64 1 * 4 from rfl] at h
  exact h

@[scoped c0_load] theorem load_k6arr32_u32 {a : BitVec 64} {i : BitVec 32} {xs : List (BitVec 32)}
    (hi : i.toNat < xs.length) (hm : (array (t := i32) a xs ⋆ R) m) :
    loadVal m i32 (a + i.setWidth 64 * 4) = some xs[i.toNat] := by
  have h := loadVal_array (t := i32) (a := a) (xs := xs) (i := i.toNat) (by decide) hi hm
  have hptr : a + i.setWidth 64 * 4 = a + BitVec.ofNat 64 (4 * i.toNat) := by
    congr 1; apply BitVec.eq_of_toNat_eq; bv_omega
  rw [hptr]; simpa [show (i32 : Ty).bytes = 4 from rfl] using h

@[scoped c0_load] theorem load_k6arr32_u64 {a i : BitVec 64} {xs : List (BitVec 32)}
    (hi : i.toNat < xs.length) (_hlt : i.toNat < 2 ^ 60)
    (hm : (array (t := i32) a xs ⋆ R) m) :
    loadVal m i32 (a + i * 4) = some xs[i.toNat] := by
  have h := loadVal_array (t := i32) (a := a) (xs := xs) (i := i.toNat) (by decide) hi hm
  have hptr : a + i * 4 = a + BitVec.ofNat 64 (4 * i.toNat) := by
    congr 1; apply BitVec.eq_of_toNat_eq; bv_omega
  rw [hptr]; simpa [show (i32 : Ty).bytes = 4 from rfl] using h

@[scoped c0_store] theorem store_k6arr32_u64 {a i : BitVec 64} {xs : List (BitVec 32)}
    (v : BitVec 32) (hi : i.toNat < xs.length) (_hlt : i.toNat < 2 ^ 60)
    (hm : (array (t := i32) a xs ⋆ R) m) :
    storeOk m i32 (a + i * 4) ∧
      (array (t := i32) a (xs.set i.toNat v) ⋆ R) (storeMem m i32 (a + i * 4) v) := by
  have h := store_array (t := i32) (a := a) (xs := xs) (i := i.toNat) v (by decide) hi hm
  have hptr : a + i * 4 = a + BitVec.ofNat 64 (4 * i.toNat) := by
    congr 1; apply BitVec.eq_of_toNat_eq; bv_omega
  rw [hptr]; simpa [show (i32 : Ty).bytes = 4 from rfl] using h

end FrameAccess

@[expose] def szV (L : K6Layout) : Nat := L.maxV
@[expose] def sz2V (L : K6Layout) : Nat := 2 * L.maxV
@[expose] def szCl (L : K6Layout) : Nat := L.maxCl
@[expose] def sz2Cl (L : K6Layout) : Nat := 2 * L.maxCl
@[expose] def szAr (L : K6Layout) : Nat := L.acap

private meta def elabK6Cmd (tag src : String) : Lean.Elab.Command.CommandElabM Unit := do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command src tag with
  | .ok stx => Lean.Elab.Command.elabCommand stx
  | .error err => throwError "{tag}: generated code failed to parse: {err}\n{src}"

local elab "gen_k6_mem_access!" : command => do
  let hdrFields : List (String × Nat) :=
    [ ("nv", 0), ("nc", 1), ("lvl", 2), ("prop", 3), ("trl_end", 4), ("unass", 5), ("incons", 6)
    , ("qfirst", 7), ("qlast", 8), ("qsearch", 9), ("qstamp", 10), ("ticks", 11)
    , ("tick_lim", 12), ("alen", 13), ("acap", 14), ("nassump", 15), ("nkl", 16), ("nana", 17)
    , ("status", 18), ("phase", 19), ("openCnt", 20), ("max_v", 21), ("max_orig", 22)
    , ("max_cl", 23), ("neq", 24) ]
  for (fld, idx) in hdrFields do
    let lsrc :=
      s!"@[scoped c0_load] theorem load_k6_{fld} " ++
      "{L : K6Layout} {kPtr : BitVec 64} {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} " ++
      s!"(hm : (K6MemA L kPtr ks ⋆ R) m) :\n" ++
      s!"    loadVal m i32 (kPtr + BitVec.ofNat 64 {idx} * 4) = some ks.{fld} :=\n" ++
      s!"  k6HdrGet {idx} (by decide) ks.{fld} (fun _ => rfl) hm"
    let ssrc :=
      s!"@[scoped c0_store] theorem store_k6_{fld} (v : BitVec 32) " ++
      "{L : K6Layout} {kPtr : BitVec 64} {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} " ++
      s!"(hm : (K6MemA L kPtr ks ⋆ R) m) :\n" ++
      s!"    storeOk m i32 (kPtr + BitVec.ofNat 64 {idx} * 4) ∧\n" ++
      s!"      (K6MemA L kPtr (ks.putHdr .{fld} v) ⋆ R)\n" ++
      s!"        (storeMem m i32 (kPtr + BitVec.ofNat 64 {idx} * 4) v) :=\n" ++
      s!"  k6HdrPut .{fld} {idx} v (by decide) rfl rfl hm"
    elabK6Cmd s!"load_k6_{fld}" lsrc
    elabK6Cmd s!"store_k6_{fld}" ssrc
  let arrFields : List (String × Nat × String × String × String) :=
    [ ("lvlArr",    1,  "K6Layout.oLvl",      "szV",   "lvlArr_len")
    , ("rsn",       2,  "K6Layout.oRsn",      "szV",   "rsn_len")
    , ("qprev",     3,  "K6Layout.oQPrev",    "szV",   "qprev_len")
    , ("qnext",     4,  "K6Layout.oQNext",    "szV",   "qnext_len")
    , ("qstampArr", 5,  "K6Layout.oQStamp",   "szV",   "qstampArr_len")
    , ("trl",       6,  "K6Layout.oTrl",      "szV",   "trl_len")
    , ("flags",     7,  "K6Layout.oFlags",    "szV",   "flags_len")
    , ("ana",       8,  "K6Layout.oAna",      "szV",   "ana_len")
    , ("kl",        9,  "K6Layout.oKl",       "szV",   "kl_len")
    , ("assump",    10, "K6Layout.oAssump",   "szV",   "assump_len")
    , ("vals",      11, "K6Layout.oVals",     "sz2V",  "vals_len")
    , ("whead",     12, "K6Layout.oWHead",    "sz2V",  "whead_len")
    , ("wnext",     13, "K6Layout.oWNext",    "sz2Cl", "wnext_len")
    , ("wblit",     14, "K6Layout.oWBlit",    "sz2Cl", "wblit_len")
    , ("clOff",     15, "K6Layout.oClOff",    "szCl",  "clOff_len")
    , ("clSz",      16, "K6Layout.oClSz",     "szCl",  "clSz_len")
    , ("arena",     17, "K6Layout.oArena",    "szAr",  "arena_len") ]
  for (fld, leaf, oFn, szFn, lenFn) in arrFields do
    let bdPf :=
      if szFn == "szAr" then "have := L.hacap; unfold szAr dimacsBound at *; omega"
      else if szFn == "szCl" || szFn == "sz2Cl" then
        s!"have := L.hmaxV; unfold {szFn} K6Layout.maxCl at *; omega"
      else s!"have := L.hmaxV; unfold {szFn} at *; omega"
    let lsrc :=
      s!"@[scoped c0_load] theorem load_k6_{fld} " ++
      "{L : K6Layout} {kPtr : BitVec 64} {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} " ++
      "{i : BitVec 32} " ++
      s!"(hi : i.toNat < {szFn} L) (hm : (K6MemA L kPtr ks ⋆ R) m) :\n" ++
      s!"    loadVal m i32 ((kPtr + BitVec.ofNat 64 (4 * {oFn} L)) + i.setWidth 64 * 4) =\n" ++
      s!"      some (ks.{fld}[i.toNat]?.getD 0#32) :=\n" ++
      s!"  k6ArrGetBase (k6Path {leaf}) ({oFn} L) ({szFn} L) ks.{fld} (fun h => h.{lenFn}) rfl " ++
      s!"(by {bdPf}) hi hm"
    let ssrc :=
      s!"@[scoped c0_store] theorem store_k6_{fld} " ++
      "{L : K6Layout} {kPtr : BitVec 64} {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} " ++
      "(v : BitVec 32) {i : BitVec 32} " ++
      s!"(hi : i.toNat < {szFn} L) (hm : (K6MemA L kPtr ks ⋆ R) m) :\n" ++
      s!"    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * {oFn} L)) + i.setWidth 64 * 4) ∧\n" ++
      s!"      (K6MemA L kPtr (ks.putArr .{fld} i.toNat v) ⋆ R)\n" ++
      s!"        (storeMem m i32 ((kPtr + BitVec.ofNat 64 (4 * {oFn} L)) + i.setWidth 64 * 4) " ++
      s!"v) :=\n" ++
      s!"  k6ArrPutBase (k6Path {leaf}) .{fld} ({oFn} L) ({szFn} L) ks.{fld} " ++
      s!"(fun h => h.{lenFn}) rfl v (by {bdPf}) hi rfl hm"
    elabK6Cmd s!"load_k6_{fld}" lsrc
    elabK6Cmd s!"store_k6_{fld}" ssrc

gen_k6_mem_access!

@[scoped c0_load] theorem load_k6_nv_base
    {L : K6Layout} {kPtr : BitVec 64} {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (K6MemA L kPtr ks ⋆ R) m) : loadVal m i32 kPtr = some ks.nv := by
  simpa using load_k6_nv hm

@[scoped c0_store] theorem store_k6_nv_base (v : BitVec 32)
    {L : K6Layout} {kPtr : BitVec 64} {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 kPtr ∧ (K6MemA L kPtr (ks.putHdr .nv v) ⋆ R) (storeMem m i32 kPtr v) := by
  simpa using store_k6_nv v hm

section ExtraK6Access
variable {L : K6Layout} {kPtr : BitVec 64} {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64}

@[scoped c0_load] theorem load_k6_kl0 (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oKl)) + (0#32).setWidth 64 * 4) =
      some (ks.kl[0]?.getD 0#32) :=
  load_k6_kl (i := 0#32) (by unfold szV; have := L.hmaxV; bv_omega) hm

@[scoped c0_store] theorem store_k6_kl0 (v : BitVec 32) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oKl)) + (0#32).setWidth 64 * 4) ∧
      (K6MemA L kPtr (ks.putArr .kl 0 v) ⋆ R)
        (storeMem m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oKl)) + (0#32).setWidth 64 * 4) v) :=
  store_k6_kl v (i := 0#32) (by unfold szV; have := L.hmaxV; bv_omega) hm

@[scoped c0_load] theorem load_k6_kl1 (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oKl)) + (1#32).setWidth 64 * 4) =
      some (ks.kl[1]?.getD 0#32) :=
  load_k6_kl (i := 1#32) (by unfold szV; have := L.hmaxV; bv_omega) hm

@[scoped c0_store] theorem store_k6_kl1 (v : BitVec 32) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oKl)) + (1#32).setWidth 64 * 4) ∧
      (K6MemA L kPtr (ks.putArr .kl 1 v) ⋆ R)
        (storeMem m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oKl)) + (1#32).setWidth 64 * 4) v) :=
  store_k6_kl v (i := 1#32) (by unfold szV; have := L.hmaxV; bv_omega) hm

@[scoped c0_load] theorem load_k6_assump0 (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + (0#32).setWidth 64 * 4) =
      some (ks.assump[0]?.getD 0#32) :=
  load_k6_assump (i := 0#32) (by unfold szV; have := L.hmaxV; bv_omega) hm

@[scoped c0_store] theorem store_k6_assump0 (v : BitVec 32) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + (0#32).setWidth 64 * 4) ∧
      (K6MemA L kPtr (ks.putArr .assump 0 v) ⋆ R)
        (storeMem m i32
          ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + (0#32).setWidth 64 * 4) v) :=
  store_k6_assump v (i := 0#32) (by unfold szV; have := L.hmaxV; bv_omega) hm

@[scoped c0_load] theorem load_k6_trl_sub1 {te : BitVec 32} (hpos : 0 < te.toNat)
    (hi : te.toNat - 1 < L.maxV) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oTrl)) + (te - 1#32).setWidth 64 * 4) =
      some (ks.trl[te.toNat - 1]?.getD 0#32) := by
  have hsub : (te - 1#32).toNat = te.toNat - 1 := by bv_omega
  simpa [hsub] using load_k6_trl (i := te - 1#32) (by unfold szV; rw [hsub]; exact hi) hm

@[scoped c0_store] theorem store_k6_qnext_sub1 (v : BitVec 32) {nv : BitVec 32}
    (hpos : 0 < nv.toNat) (hi : nv.toNat - 1 < L.maxV) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oQNext)) + (nv - 1#32).setWidth 64 * 4) ∧
      (K6MemA L kPtr (ks.putArr .qnext (nv.toNat - 1) v) ⋆ R)
        (storeMem m i32
          ((kPtr + BitVec.ofNat 64 (4 * L.oQNext)) + (nv - 1#32).setWidth 64 * 4) v) := by
  have hsub : (nv - 1#32).toNat = nv.toNat - 1 := by bv_omega
  simpa [hsub] using store_k6_qnext v (i := nv - 1#32) (by unfold szV; rw [hsub]; exact hi) hm

@[scoped c0_load] theorem load_k6_arena_off {off j : BitVec 32}
    (hwrap : off.toNat + j.toNat < 2 ^ 32) (hi : off.toNat + j.toNat < L.acap)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oArena)) + (off + j).setWidth 64 * 4) =
      some (ks.arena[off.toNat + j.toNat]?.getD 0#32) := by
  have hoj : (off + j).toNat = off.toNat + j.toNat := by bv_omega
  simpa [hoj] using load_k6_arena (i := off + j) (by unfold szAr; rw [hoj]; exact hi) hm

@[scoped c0_store] theorem store_k6_arena_off (v : BitVec 32) {off j : BitVec 32}
    (hwrap : off.toNat + j.toNat < 2 ^ 32) (hi : off.toNat + j.toNat < L.acap)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oArena)) + (off + j).setWidth 64 * 4) ∧
      (K6MemA L kPtr (ks.putArr .arena (off.toNat + j.toNat) v) ⋆ R)
        (storeMem m i32
          ((kPtr + BitVec.ofNat 64 (4 * L.oArena)) + (off + j).setWidth 64 * 4) v) := by
  have hoj : (off + j).toNat = off.toNat + j.toNat := by bv_omega
  simpa [hoj] using store_k6_arena v (i := off + j) (by unfold szAr; rw [hoj]; exact hi) hm

end ExtraK6Access

@[scoped bv_c0] theorem putHdr_nv (ks : K6State) (v : BitVec 32) : (ks.putHdr .nv v).nv = v := rfl
@[scoped bv_c0] theorem putHdr_nc (ks : K6State) (v : BitVec 32) : (ks.putHdr .nc v).nc = v := rfl
@[scoped bv_c0] theorem putHdr_lvl (ks : K6State) (v : BitVec 32) :
    (ks.putHdr .lvl v).lvl = v := rfl
@[scoped bv_c0] theorem putHdr_prop (ks : K6State) (v : BitVec 32) :
    (ks.putHdr .prop v).prop = v := rfl
@[scoped bv_c0] theorem putHdr_trl_end (ks : K6State) (v : BitVec 32) :
    (ks.putHdr .trl_end v).trl_end = v := rfl
@[scoped bv_c0] theorem putHdr_unass (ks : K6State) (v : BitVec 32) :
    (ks.putHdr .unass v).unass = v := rfl
@[scoped bv_c0] theorem putHdr_incons (ks : K6State) (v : BitVec 32) :
    (ks.putHdr .incons v).incons = v := rfl
@[scoped bv_c0] theorem putHdr_ticks (ks : K6State) (v : BitVec 32) :
    (ks.putHdr .ticks v).ticks = v := rfl
@[scoped bv_c0] theorem putHdr_tick_lim (ks : K6State) (v : BitVec 32) :
    (ks.putHdr .tick_lim v).tick_lim = v := rfl
@[scoped bv_c0] theorem putHdr_openCnt (ks : K6State) (v : BitVec 32) :
    (ks.putHdr .openCnt v).openCnt = v := rfl
@[scoped bv_c0] theorem putHdr_nkl (ks : K6State) (v : BitVec 32) :
    (ks.putHdr .nkl v).nkl = v := rfl
@[scoped bv_c0] theorem putHdr_nana (ks : K6State) (v : BitVec 32) :
    (ks.putHdr .nana v).nana = v := rfl

scoped macro "k6_field" : tactic => `(tactic|
  simp only [K6State.putHdr, K6State.putArr, reduceCtorEq, ite_true, ite_false])

scoped macro "k6_ext" : tactic => `(tactic|
  (apply k6State_ext <;> (k6_field; try rfl)))

end K6MemATactics

end LeanQbe.T.Examples.Kissat.Proof.Kitten

end
