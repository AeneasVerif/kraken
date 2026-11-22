module

public import LeanQbe.T.Examples.Kissat.FullM4Sweep
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
public import LeanQbe.T.Logic.SepTree

/-!
# Kissat `D-Full` M4b — 512-Var `kitten` + Partition-Class Sweeping Specs & Memory Layout

Defines:
1. `K512State`, `K512Tree` (balanced 18-leaf `SepTree`), `K512Mem`, `K512MemA`, `FullK512Frame`,
   and strictly scoped `K512MemTactics` / `K512MemATactics` / `K512ProjTactics`.
2. Semantic model-set invariant `K512Inv acap P ks` (parametric in `P : (Nat → Bool) → Prop`),
   `K512TrailSynced`, `K512AnaInv`, `K512ScratchInv`, `ConeModelSet`, and `PhtOk`.
3. All `24` UNSAT-only `Spec` contracts (`12` `k512` + `12` `m4_sweep`), `31`-row
   `fullM4SweepSpecTable` (`24` owned + `7` canonical `Full` externs), and `fullM4SweepEnv`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Layout Constants & Small Bitvector Helpers -/

def phtHead : Nat := 256
def phtSz : Nat := 1024
def phtNext : Nat := 1280
def phtMerged : Nat := 1792

def k5Base : Nat := 2304
def k5MaxV : Nat := 512
def k5MaxL : Nat := 1024
def k5MaxOrig : Nat := 1536
def k5MaxCl : Nat := 2048
def k5SlabFixed : Nat := 19488
def k5MinScr : Nat := 24576

theorem k5_bv32_div2_lt {nv : Nat} {l : BitVec 32} (hl : l.toNat < 2 * nv) :
    (l >>> (1 : Nat)).toNat = l.toNat / 2 ∧ (l >>> (1 : Nat)).toNat < nv := by
  have h1 : (l >>> (1 : Nat)).toNat = l.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact ⟨h1, by omega⟩

theorem k5_bv32_xor1_lt {nv : Nat} {l : BitVec 32} (hl : l.toNat < 2 * nv) :
    (l ^^^ 1#32).toNat = litNeg l.toNat ∧ (l ^^^ 1#32).toNat < 2 * nv := by
  have h1 : (l ^^^ 1#32).toNat = l.toNat ^^^ 1 := by simp
  have h2 : l.toNat ^^^ 1 = litNeg l.toNat := rfl
  refine ⟨h1.trans h2, ?_⟩
  rw [h1, h2, litNeg_eq]; split <;> omega

theorem k5_bv32_cid_w0 {nc : Nat} {cid : BitVec 32} (hc : cid.toNat < nc) (hnc : nc ≤ 2048) :
    (cid <<< (1 : Nat)).toNat = 2 * cid.toNat ∧ (cid <<< (1 : Nat)).toNat < 2 * nc := by
  have hshl : (cid <<< (1 : Nat)).toNat = 2 * cid.toNat := by bv_omega
  exact ⟨hshl, by omega⟩

theorem k5_bv32_cid_w1 {nc : Nat} {cid : BitVec 32} (hc : cid.toNat < nc) (hnc : nc ≤ 2048) :
    ((cid <<< (1 : Nat)) ||| 1#32).toNat = 2 * cid.toNat + 1 ∧
      ((cid <<< (1 : Nat)) ||| 1#32).toNat < 2 * nc := by
  have hsh : cid <<< (1 : Nat) = BitVec.ofNat 32 (2 * cid.toNat) := by bv_omega
  have h1 : BitVec.ofNat 32 (2 * cid.toNat) ||| 1#32 = BitVec.ofNat 32 (2 * cid.toNat + 1) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
      show (1#32).getLsbD i = decide (i = 0) by cases i <;> simp]
    cases i with
    | zero => simp [Nat.testBit_zero]
    | succ k => simp [Nat.testBit_succ, show (2 * cid.toNat + 1) / 2 = cid.toNat by omega]
  have hor : ((cid <<< (1 : Nat)) ||| 1#32).toNat = 2 * cid.toNat + 1 := by
    rw [hsh, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact ⟨hor, by omega⟩

theorem k5_ptr_nat_mul4 (p : BitVec 64) (idx : Nat) (h : idx < 2 ^ 28) :
    p + BitVec.ofNat 64 idx * 4 = p + BitVec.ofNat 64 (4 * idx) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
  congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), show 4 % 2 ^ 64 = 4 from by decide,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mul_comm]

theorem k5_ptr_off_bv32_mul4 (kPtr : BitVec 64) (kOff : Nat) (off32 : BitVec 32)
    (hk : kOff ≤ 19488) (hoff : off32 = BitVec.ofNat 32 kOff)
    {i : BitVec 32} (hi : i.toNat < 2 ^ 28) :
    kPtr + (off32 + i).setWidth 64 * 4 =
      kPtr + BitVec.ofNat 64 (4 * kOff) + BitVec.ofNat 64 (4 * i.toNat) := by
  rw [hoff, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
  have heq : (BitVec.ofNat 32 kOff + i).setWidth 64 * BitVec.ofNat 64 4 =
      BitVec.ofNat 64 (4 * kOff) + BitVec.ofNat 64 (4 * i.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : kOff < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : kOff + i.toNat < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : kOff + i.toNat < 2 ^ 64),
      show 4 % 2 ^ 64 = 4 from by decide,
      Nat.mod_eq_of_lt (by omega : (kOff + i.toNat) * 4 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 4 * kOff < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 4 * i.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 4 * kOff + 4 * i.toNat < 2 ^ 64)]
    omega
  rw [heq, BitVec.add_assoc]

theorem k5Ptr_base_eq (p : BitVec 64) : p + BitVec.ofNat 64 2304 * 4 = p + 9216#64 := rfl

/-! ## 2. `K512State`, `ShapesOk`, Slab Serialization, & Balanced `K512Tree` -/

/-- Typed representation of `k512`'s `u32` slab starting at `scratch_buf + K512_BASE` (`2304`). -/
structure K512State where
  nv : BitVec 32
  nc : BitVec 32
  lvl : BitVec 32
  prop : BitVec 32
  trl_end : BitVec 32
  unass : BitVec 32
  incons : BitVec 32
  qfirst : BitVec 32
  qlast : BitVec 32
  qsearch : BitVec 32
  qstamp : BitVec 32
  ticks : BitVec 32
  tick_lim : BitVec 32
  alen : BitVec 32
  acap : BitVec 32
  nassump : BitVec 32
  nkl : BitVec 32
  nana : BitVec 32
  status : BitVec 32
  phase : BitVec 32
  hdrTail : List (BitVec 32)
  lvlArr : List (BitVec 32)
  rsn : List (BitVec 32)
  qprev : List (BitVec 32)
  qnext : List (BitVec 32)
  qstampArr : List (BitVec 32)
  trl : List (BitVec 32)
  flags : List (BitVec 32)
  ana : List (BitVec 32)
  kl : List (BitVec 32)
  assump : List (BitVec 32)
  vals : List (BitVec 32)
  whead : List (BitVec 32)
  wnext : List (BitVec 32)
  wblit : List (BitVec 32)
  clOff : List (BitVec 32)
  clSz : List (BitVec 32)
  arena : List (BitVec 32)

def k5HdrWords (ks : K512State) : List (BitVec 32) :=
  [ ks.nv, ks.nc, ks.lvl, ks.prop, ks.trl_end, ks.unass, ks.incons, ks.qfirst, ks.qlast,
    ks.qsearch, ks.qstamp, ks.ticks, ks.tick_lim, ks.alen, ks.acap, ks.nassump, ks.nkl,
    ks.nana, ks.status, ks.phase ] ++ ks.hdrTail

structure K512State.ShapesOk (acap : Nat) (ks : K512State) : Prop where
  hdrTail_len : ks.hdrTail.length = 12
  lvlArr_len : ks.lvlArr.length = 512
  rsn_len : ks.rsn.length = 512
  qprev_len : ks.qprev.length = 512
  qnext_len : ks.qnext.length = 512
  qstampArr_len : ks.qstampArr.length = 512
  trl_len : ks.trl.length = 512
  flags_len : ks.flags.length = 512
  ana_len : ks.ana.length = 512
  kl_len : ks.kl.length = 512
  assump_len : ks.assump.length = 512
  vals_len : ks.vals.length = 1024
  whead_len : ks.whead.length = 1024
  wnext_len : ks.wnext.length = 4096
  wblit_len : ks.wblit.length = 4096
  clOff_len : ks.clOff.length = 2048
  clSz_len : ks.clSz.length = 2048
  arena_len : ks.arena.length = acap

theorem k5HdrWords_length {acap : Nat} {ks : K512State} (h : ks.ShapesOk acap) :
    (k5HdrWords ks).length = 32 := by
  simp [k5HdrWords, h.hdrTail_len]

def K512State.toSlab (ks : K512State) : List (BitVec 32) :=
  k5HdrWords ks ++ (ks.lvlArr ++ (ks.rsn ++ (ks.qprev ++ (ks.qnext ++ (ks.qstampArr ++
  (ks.trl ++ (ks.flags ++ (ks.ana ++ (ks.kl ++ (ks.assump ++ (ks.vals ++ (ks.whead ++
  (ks.wnext ++ (ks.wblit ++ (ks.clOff ++ (ks.clSz ++ ks.arena))))))))))))))))

theorem K512State.toSlab_length {acap : Nat} {ks : K512State} (h : ks.ShapesOk acap) :
    ks.toSlab.length = 19488 + acap := by
  have hh := k5HdrWords_length h
  rcases h with ⟨_, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
  dsimp only [K512State.toSlab]
  simp only [List.length_append]
  rw [hh, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
  simp only [← Nat.add_assoc]

def K512State.ofSlab (xs : List (BitVec 32)) : K512State where
  nv := xs[0]?.getD 0#32; nc := xs[1]?.getD 0#32; lvl := xs[2]?.getD 0#32
  prop := xs[3]?.getD 0#32; trl_end := xs[4]?.getD 0#32; unass := xs[5]?.getD 0#32
  incons := xs[6]?.getD 0#32; qfirst := xs[7]?.getD 0#32; qlast := xs[8]?.getD 0#32
  qsearch := xs[9]?.getD 0#32; qstamp := xs[10]?.getD 0#32; ticks := xs[11]?.getD 0#32
  tick_lim := xs[12]?.getD 0#32; alen := xs[13]?.getD 0#32; acap := xs[14]?.getD 0#32
  nassump := xs[15]?.getD 0#32; nkl := xs[16]?.getD 0#32; nana := xs[17]?.getD 0#32
  status := xs[18]?.getD 0#32; phase := xs[19]?.getD 0#32
  hdrTail := (xs.drop 20).take 12
  lvlArr := (xs.drop 32).take 512
  rsn := (xs.drop 544).take 512
  qprev := (xs.drop 1056).take 512
  qnext := (xs.drop 1568).take 512
  qstampArr := (xs.drop 2080).take 512
  trl := (xs.drop 2592).take 512
  flags := (xs.drop 3104).take 512
  ana := (xs.drop 3616).take 512
  kl := (xs.drop 4128).take 512
  assump := (xs.drop 4640).take 512
  vals := (xs.drop 5152).take 1024
  whead := (xs.drop 6176).take 1024
  wnext := (xs.drop 7200).take 4096
  wblit := (xs.drop 11296).take 4096
  clOff := (xs.drop 15392).take 2048
  clSz := (xs.drop 17440).take 2048
  arena := xs.drop 19488

theorem K512State.shapesOk_ofSlab {xs : List (BitVec 32)} (h : 19488 ≤ xs.length) :
    (K512State.ofSlab xs).ShapesOk (xs.length - 19488) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [K512State.ofSlab, List.length_take, List.length_drop]; try omega

private theorem k5_slice_append {α : Type _} (xs : List α) (a b : Nat) :
    (xs.drop a).take b ++ xs.drop (a + b) = xs.drop a := by
  rw [← @List.drop_drop _ b a xs, List.take_append_drop]

private theorem k5_drop_exact {α : Type _} (p s : List α) {k : Nat} (hk : p.length = k) :
    (p ++ s).drop k = s := by
  rw [List.drop_append_of_le_length (by omega), ← hk, List.drop_length, List.nil_append]

private theorem k5_drop_step {α : Type _} {xs p rest : List α} {k0 k1 n : Nat}
    (hd : xs.drop k0 = p ++ rest) (hp : p.length = n) (hsum : k1 = k0 + n) :
    xs.drop k1 = rest := by
  rw [hsum, ← List.drop_drop, hd]; exact k5_drop_exact p rest hp

private theorem k5_take_prefix {α : Type _} {xs p rest : List α} {k n : Nat}
    (hd : xs.drop k = p ++ rest) (hp : p.length = n) :
    (xs.drop k).take n = p := by
  rw [hd, List.take_append_of_le_length (by omega), ← hp, List.take_length]

theorem K512State.toSlab_ofSlab {xs : List (BitVec 32)} (h : 19488 ≤ xs.length) :
    (K512State.ofSlab xs).toSlab = xs := by
  have h0 : k5HdrWords (K512State.ofSlab xs) = xs.take 32 := by
    apply List.ext_getElem
    · rw [k5HdrWords_length (shapesOk_ofSlab h), List.length_take_of_le (by omega)]
    · intro i hi1 hi2
      rw [k5HdrWords_length (shapesOk_ofSlab h)] at hi1
      have hge : i < xs.length := by omega
      simp only [List.getElem_take]
      by_cases h20 : i < 20
      · have hfn : ∀ k : Fin 20,
            (k5HdrWords (K512State.ofSlab xs))[k.1]'(by
              rw [k5HdrWords_length (shapesOk_ofSlab h)]; omega) = xs[k.1]'(by omega) := by
          intro ⟨k, hk⟩
          have hget (j : Nat) (hj : j < 20) : xs[j]?.getD 0#32 = xs[j]'(by omega) := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          match k, hk with
          | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _
          | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ =>
            exact hget _ (by omega)
          | _ + 20, hk => omega
        exact hfn ⟨i, h20⟩
      · have hlo : 20 ≤ i := by omega
        have hi_lt : i - 20 < 12 := by omega
        simp only [k5HdrWords, K512State.ofSlab]
        rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_cons, List.length_nil, List.getElem_take, List.getElem_drop]
        congr 1; omega
  simp only [K512State.toSlab, K512State.ofSlab] at h0 ⊢
  rw [h0, k5_slice_append xs 17440 2048, k5_slice_append xs 15392 2048,
    k5_slice_append xs 11296 4096, k5_slice_append xs 7200 4096, k5_slice_append xs 6176 1024,
    k5_slice_append xs 5152 1024, k5_slice_append xs 4640 512, k5_slice_append xs 4128 512,
    k5_slice_append xs 3616 512, k5_slice_append xs 3104 512, k5_slice_append xs 2592 512,
    k5_slice_append xs 2080 512, k5_slice_append xs 1568 512, k5_slice_append xs 1056 512,
    k5_slice_append xs 544 512, k5_slice_append xs 32 512, List.take_append_drop]

theorem K512State.ofSlab_toSlab {acap : Nat} {ks : K512State} (h : ks.ShapesOk acap) :
    K512State.ofSlab ks.toSlab = ks := by
  rcases ks with ⟨nv, nc, lvl, prop, trl_end, unass, incons, qfirst, qlast, qsearch, qstamp,
    ticks, tick_lim, alen, acapF, nassump, nkl, nana, status, phase, hdrTail, lvlArr, rsn, qprev,
    qnext, qstampArr, trl, flags, ana, kl, assump, vals, whead, wnext, wblit, clOff, clSz, arena⟩
  rcases h with ⟨htl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, _⟩
  let L0 := [nv, nc, lvl, prop, trl_end, unass, incons, qfirst, qlast, qsearch, qstamp, ticks,
    tick_lim, alen, acapF, nassump, nkl, nana, status, phase]
  let ts : List (BitVec 32) :=
    (L0 ++ hdrTail) ++ (lvlArr ++ (rsn ++ (qprev ++ (qnext ++ (qstampArr ++ (trl ++ (flags ++
    (ana ++ (kl ++ (assump ++ (vals ++ (whead ++ (wnext ++ (wblit ++ (clOff ++ (clSz ++
    arena))))))))))))))))
  have hd0 : ts.drop 32 = lvlArr ++ (rsn ++ (qprev ++ (qnext ++ (qstampArr ++ (trl ++ (flags ++
      (ana ++ (kl ++ (assump ++ (vals ++ (whead ++ (wnext ++ (wblit ++ (clOff ++ (clSz ++
      arena))))))))))))))) :=
    k5_drop_exact (L0 ++ hdrTail) _ (by simpa [L0, List.length_append] using htl)
  have hd1 := k5_drop_step hd0 h1 (by decide : 544 = 32 + 512)
  have hd2 := k5_drop_step hd1 h2 (by decide : 1056 = 544 + 512)
  have hd3 := k5_drop_step hd2 h3 (by decide : 1568 = 1056 + 512)
  have hd4 := k5_drop_step hd3 h4 (by decide : 2080 = 1568 + 512)
  have hd5 := k5_drop_step hd4 h5 (by decide : 2592 = 2080 + 512)
  have hd6 := k5_drop_step hd5 h6 (by decide : 3104 = 2592 + 512)
  have hd7 := k5_drop_step hd6 h7 (by decide : 3616 = 3104 + 512)
  have hd8 := k5_drop_step hd7 h8 (by decide : 4128 = 3616 + 512)
  have hd9 := k5_drop_step hd8 h9 (by decide : 4640 = 4128 + 512)
  have hd10 := k5_drop_step hd9 h10 (by decide : 5152 = 4640 + 512)
  have hd11 := k5_drop_step hd10 h11 (by decide : 6176 = 5152 + 1024)
  have hd12 := k5_drop_step hd11 h12 (by decide : 7200 = 6176 + 1024)
  have hd13 := k5_drop_step hd12 h13 (by decide : 11296 = 7200 + 4096)
  have hd14 := k5_drop_step hd13 h14 (by decide : 15392 = 11296 + 4096)
  have hd15 := k5_drop_step hd14 h15 (by decide : 17440 = 15392 + 2048)
  have hd16 := k5_drop_step hd15 h16 (by decide : 19488 = 17440 + 2048)
  have hht : (ts.drop 20).take 12 = hdrTail := by
    simp only [ts, List.append_assoc]
    rw [List.drop_append_of_le_length (by simp [L0])]
    have hnil : L0.drop 20 = [] := by simp [L0]
    rw [hnil, List.nil_append, List.take_append_of_le_length (by rw [htl]; decide),
      ← htl, List.take_length]
  change K512State.ofSlab ts = _
  simp only [K512State.ofSlab]
  rw [hht, k5_take_prefix hd0 h1, k5_take_prefix hd1 h2, k5_take_prefix hd2 h3,
    k5_take_prefix hd3 h4, k5_take_prefix hd4 h5, k5_take_prefix hd5 h6, k5_take_prefix hd6 h7,
    k5_take_prefix hd7 h8, k5_take_prefix hd8 h9, k5_take_prefix hd9 h10, k5_take_prefix hd10 h11,
    k5_take_prefix hd11 h12, k5_take_prefix hd12 h13, k5_take_prefix hd13 h14,
    k5_take_prefix hd14 h15, k5_take_prefix hd15 h16, hd16]
  rfl

def k5Path : Nat → List Bool
  | 0 => [false, false, false, false]
  | 1 => [false, false, false, true]
  | 2 => [false, false, true, false]
  | 3 => [false, false, true, true]
  | 4 => [false, true, false, false]
  | 5 => [false, true, false, true]
  | 6 => [false, true, true, false]
  | 7 => [false, true, true, true, false]
  | 8 => [false, true, true, true, true]
  | 9 => [true, false, false, false]
  | 10 => [true, false, false, true]
  | 11 => [true, false, true, false]
  | 12 => [true, false, true, true]
  | 13 => [true, true, false, false]
  | 14 => [true, true, false, true]
  | 15 => [true, true, true, false]
  | 16 => [true, true, true, true, false]
  | _ => [true, true, true, true, true]

/-- Balanced `18`-leaf `SepTree` over `k512`'s `u32` slab at `kPtr`. -/
def K512Tree (kPtr : BitVec 64) (ks : K512State) : SepTree :=
  let t01 := SepTree.node (.leaf (array (t := i32) kPtr (k5HdrWords ks)))
    (.leaf (array (t := i32) (kPtr + 128#64) ks.lvlArr))
  let t23 := SepTree.node (.leaf (array (t := i32) (kPtr + 2176#64) ks.rsn))
    (.leaf (array (t := i32) (kPtr + 4224#64) ks.qprev))
  let t45 := SepTree.node (.leaf (array (t := i32) (kPtr + 6272#64) ks.qnext))
    (.leaf (array (t := i32) (kPtr + 8320#64) ks.qstampArr))
  let t78 := SepTree.node (.leaf (array (t := i32) (kPtr + 12416#64) ks.flags))
    (.leaf (array (t := i32) (kPtr + 14464#64) ks.ana))
  let t68 := SepTree.node (.leaf (array (t := i32) (kPtr + 10368#64) ks.trl)) t78
  let t910 := SepTree.node (.leaf (array (t := i32) (kPtr + 16512#64) ks.kl))
    (.leaf (array (t := i32) (kPtr + 18560#64) ks.assump))
  let t1112 := SepTree.node (.leaf (array (t := i32) (kPtr + 20608#64) ks.vals))
    (.leaf (array (t := i32) (kPtr + 24704#64) ks.whead))
  let t1314 := SepTree.node (.leaf (array (t := i32) (kPtr + 28800#64) ks.wnext))
    (.leaf (array (t := i32) (kPtr + 45184#64) ks.wblit))
  let t1617 := SepTree.node (.leaf (array (t := i32) (kPtr + 69760#64) ks.clSz))
    (.leaf (array (t := i32) (kPtr + 77952#64) ks.arena))
  let t1517 := SepTree.node (.leaf (array (t := i32) (kPtr + 61568#64) ks.clOff)) t1617
  .node (.node (.node t01 t23) (.node t45 t68)) (.node (.node t910 t1112) (.node t1314 t1517))

def K512Mem (kPtr : BitVec 64) (ks : K512State) : Mem 64 → Prop := (K512Tree kPtr ks).eval

private theorem k5_arr32_append (a off : BitVec 64) (xs ys : List (BitVec 32))
    (hs : a + BitVec.ofNat 64 (4 * xs.length) = off) :
    array (t := i32) a (xs ++ ys) = (array (t := i32) a xs ⋆ array (t := i32) off ys) := by
  rw [array_append, show (i32 : Ty).bytes = 4 from rfl, hs]

theorem k5Mem_eq_array {acap : Nat} (kPtr : BitVec 64) {ks : K512State} (h : ks.ShapesOk acap) :
    K512Mem kPtr ks = array (t := i32) kPtr ks.toSlab := by
  have hh := k5HdrWords_length h
  rcases h with ⟨_, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, _⟩
  dsimp only [K512Mem, K512Tree, SepTree.eval, K512State.toSlab]
  rw [k5_arr32_append kPtr (kPtr + 128#64) (k5HdrWords ks) _ (by rw [hh])]
  rw [k5_arr32_append (kPtr + 128#64) (kPtr + 2176#64) ks.lvlArr _ (by rw [h1, ptr_add_ofNat])]
  rw [k5_arr32_append (kPtr + 2176#64) (kPtr + 4224#64) ks.rsn _ (by rw [h2, ptr_add_ofNat])]
  rw [k5_arr32_append (kPtr + 4224#64) (kPtr + 6272#64) ks.qprev _ (by rw [h3, ptr_add_ofNat])]
  rw [k5_arr32_append (kPtr + 6272#64) (kPtr + 8320#64) ks.qnext _ (by rw [h4, ptr_add_ofNat])]
  rw [k5_arr32_append (kPtr + 8320#64) (kPtr + 10368#64) ks.qstampArr _ (by rw [h5, ptr_add_ofNat])]
  rw [k5_arr32_append (kPtr + 10368#64) (kPtr + 12416#64) ks.trl _ (by rw [h6, ptr_add_ofNat])]
  rw [k5_arr32_append (kPtr + 12416#64) (kPtr + 14464#64) ks.flags _ (by rw [h7, ptr_add_ofNat])]
  rw [k5_arr32_append (kPtr + 14464#64) (kPtr + 16512#64) ks.ana _ (by rw [h8, ptr_add_ofNat])]
  rw [k5_arr32_append (kPtr + 16512#64) (kPtr + 18560#64) ks.kl _ (by rw [h9, ptr_add_ofNat])]
  rw [k5_arr32_append (kPtr + 18560#64) (kPtr + 20608#64) ks.assump _ (by rw [h10, ptr_add_ofNat])]
  rw [k5_arr32_append (kPtr + 20608#64) (kPtr + 24704#64) ks.vals _ (by rw [h11, ptr_add_ofNat])]
  rw [k5_arr32_append (kPtr + 24704#64) (kPtr + 28800#64) ks.whead _ (by rw [h12, ptr_add_ofNat])]
  rw [k5_arr32_append (kPtr + 28800#64) (kPtr + 45184#64) ks.wnext _ (by rw [h13, ptr_add_ofNat])]
  rw [k5_arr32_append (kPtr + 45184#64) (kPtr + 61568#64) ks.wblit _ (by rw [h14, ptr_add_ofNat])]
  rw [k5_arr32_append (kPtr + 61568#64) (kPtr + 69760#64) ks.clOff _ (by rw [h15, ptr_add_ofNat])]
  rw [k5_arr32_append (kPtr + 69760#64) (kPtr + 77952#64) ks.clSz _ (by rw [h16, ptr_add_ofNat])]
  ac_rfl

theorem array_scratch_eq_k5 {p : BitVec 64} {scr : List (BitVec 32)} (hlen : 21792 ≤ scr.length) :
    array (t := i32) p scr =
      (array (t := i32) p (scr.take 2304) ⋆
        K512Mem (p + 9216#64) (K512State.ofSlab (scr.drop 2304))) := by
  have hsh := K512State.shapesOk_ofSlab (xs := scr.drop 2304) (by simp; omega)
  rw [k5Mem_eq_array (p + 9216#64) hsh, K512State.toSlab_ofSlab (by simp; omega)]
  have htk : (scr.take 2304).length = 2304 := List.length_take_of_le (by omega)
  have happ := k5_arr32_append p (p + 9216#64) (scr.take 2304) (scr.drop 2304) (by rw [htk])
  rwa [List.take_append_drop] at happ

theorem k5_append_eq_array_scratch {p : BitVec 64} {scrHead : List (BitVec 32)}
    {acap : Nat} {ks : K512State} (hh : scrHead.length = 2304) (hsh : ks.ShapesOk acap) :
    (array (t := i32) p scrHead ⋆ K512Mem (p + 9216#64) ks) =
      array (t := i32) p (scrHead ++ ks.toSlab) := by
  rw [k5Mem_eq_array (p + 9216#64) hsh]
  exact (k5_arr32_append p (p + 9216#64) scrHead ks.toSlab (by rw [hh])).symm

def FullK512Frame (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
  FullScrMetaArrs c s.scratch ⋆ array (t := i32) c.pDelayed s.scratch.delayed ⋆
  array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
  array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
  array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take 2304) ⋆ c.pad

theorem fullMem_eq_k5Frame {c : FullCfg} {s : FullState}
    (hlen : 21792 ≤ s.scratch.scratch_buf.length) :
    FullMem c s = (FullK512Frame c s ⋆
      K512Mem (c.pScratchBuf + 9216#64) (K512State.ofSlab (s.scratch.scratch_buf.drop 2304))) := by
  unfold FullMem FullScratchArrays FullScrDynArrs FullK512Frame
  rw [array_scratch_eq_k5 hlen]; ac_rfl

theorem fullMem_join_k5 {c : FullCfg} {s : FullState} {acap : Nat} {ks' : K512State}
    {R : Mem 64 → Prop} {m : Mem 64}
    (h2304 : 2304 ≤ s.scratch.scratch_buf.length) (hsh : ks'.ShapesOk acap)
    (hm : (FullK512Frame c s ⋆ K512Mem (c.pScratchBuf + 9216#64) ks' ⋆ R) m) :
    let scr' := s.scratch.scratch_buf.take 2304 ++ ks'.toSlab
    let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
    (FullMem c s' ⋆ R) m := by
  intro scr' s'
  have htk : (s.scratch.scratch_buf.take 2304).length = 2304 := List.length_take_of_le h2304
  have h1 : (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (Full.hdrTailWords c s') ⋆ FullCoreArrays c s.core ⋆
      FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
      FullScrMetaArrs c s.scratch ⋆ array (t := i32) c.pDelayed s.scratch.delayed ⋆
      array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
      array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
      (array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take 2304) ⋆
        K512Mem (c.pScratchBuf + 9216#64) ks') ⋆ c.pad ⋆ R) m := by
    have hhdr : Full.hdrTailWords c s' = Full.hdrTailWords c s := rfl
    rw [hhdr]; unfold FullK512Frame at hm; exact sep_ac hm
  rw [k5_append_eq_array_scratch htk hsh] at h1
  unfold FullMem FullScratchArrays FullScrDynArrs; exact sep_ac h1

private theorem fullK5Frame_hdrGet {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (i : Nat) (hi : i < 140) (hm : (FullK512Frame c s ⋆ R) m) :
    loadVal m i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * i)) =
      some ((Full.hdrTailWords c s)[i]'(by rw [Full.hdrTailWords_length]; exact hi)) := by
  have h1 : (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
       FullCoreArrays c s.core ⋆ FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
       FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
       array (t := i32) c.pDelayed s.scratch.delayed ⋆
       array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
       array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
       array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take 2304) ⋆ c.pad ⋆ R)) m := by
    unfold FullK512Frame at hm; exact sep_ac hm
  have hl := loadVal_array64 (i := i) (by rw [Full.hdrTailWords_length]; exact hi) h1
  rwa [show c.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * i) =
    c.hdr + BitVec.ofNat 64 (32 + 8 * i) from ptr_add_ofNat c.hdr 32 (8 * i)] at hl

theorem fullK5Frame_fuel_store {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 64) (hm : (FullK512Frame c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 168) ∧
      (FullK512Frame c { s with core := { s.core with fuel := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 168) v) := by
  have h1 : (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
       FullCoreArrays c s.core ⋆ FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
       FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
       array (t := i32) c.pDelayed s.scratch.delayed ⋆
       array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
       array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
       array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take 2304) ⋆ c.pad ⋆ R)) m := by
    unfold FullK512Frame at hm; exact sep_ac hm
  obtain ⟨hok, hst⟩ := store_array64 (i := 17) v (by rw [Full.hdrTailWords_length]; decide) h1
  rw [show c.hdr + 32 + BitVec.ofNat 64 (8 * 17) = c.hdr + 168 from
    ptr_add_ofNat c.hdr 32 136] at hok hst
  have hset : (Full.hdrTailWords c s).set 17 v =
      Full.hdrTailWords c { s with core := { s.core with fuel := v } } := by
    simp [Full.hdrTailWords, hdrTailWords0, hdrTailWords1, hdrTailWords2, hdrTailWords3, List.set]
  rw [hset] at hst; unfold FullK512Frame; exact ⟨hok, sep_ac hst⟩

/-! ## 3. Non-Expanding `putHdr`/`putArr`, `K512MemA`, & Scoped Tactics -/

inductive K5HdrField where
  | nv | nc | lvl | prop | trl_end | unass | incons | qfirst | qlast | qsearch | qstamp
  | ticks | tick_lim | alen | acap | nassump | nkl | nana | status | phase
  deriving DecidableEq

inductive K5ArrField where
  | lvlArr | rsn | qprev | qnext | qstampArr | trl | flags | ana | kl | assump
  | vals | whead | wnext | wblit | clOff | clSz | arena
  deriving DecidableEq

def K512State.putHdr (ks : K512State) (f : K5HdrField) (v : BitVec 32) : K512State :=
  match f with
  | .nv => { ks with nv := v } | .nc => { ks with nc := v } | .lvl => { ks with lvl := v }
  | .prop => { ks with prop := v } | .trl_end => { ks with trl_end := v }
  | .unass => { ks with unass := v } | .incons => { ks with incons := v }
  | .qfirst => { ks with qfirst := v } | .qlast => { ks with qlast := v }
  | .qsearch => { ks with qsearch := v } | .qstamp => { ks with qstamp := v }
  | .ticks => { ks with ticks := v } | .tick_lim => { ks with tick_lim := v }
  | .alen => { ks with alen := v } | .acap => { ks with acap := v }
  | .nassump => { ks with nassump := v } | .nkl => { ks with nkl := v }
  | .nana => { ks with nana := v } | .status => { ks with status := v }
  | .phase => { ks with phase := v }

def K512State.putArr (ks : K512State) (f : K5ArrField) (i : Nat) (v : BitVec 32) : K512State :=
  match f with
  | .lvlArr => { ks with lvlArr := ks.lvlArr.set i v }
  | .rsn => { ks with rsn := ks.rsn.set i v }
  | .qprev => { ks with qprev := ks.qprev.set i v }
  | .qnext => { ks with qnext := ks.qnext.set i v }
  | .qstampArr => { ks with qstampArr := ks.qstampArr.set i v }
  | .trl => { ks with trl := ks.trl.set i v }
  | .flags => { ks with flags := ks.flags.set i v }
  | .ana => { ks with ana := ks.ana.set i v }
  | .kl => { ks with kl := ks.kl.set i v }
  | .assump => { ks with assump := ks.assump.set i v }
  | .vals => { ks with vals := ks.vals.set i v }
  | .whead => { ks with whead := ks.whead.set i v }
  | .wnext => { ks with wnext := ks.wnext.set i v }
  | .wblit => { ks with wblit := ks.wblit.set i v }
  | .clOff => { ks with clOff := ks.clOff.set i v }
  | .clSz => { ks with clSz := ks.clSz.set i v }
  | .arena => { ks with arena := ks.arena.set i v }

theorem K512State.ShapesOk.putHdr {acap : Nat} {ks : K512State}
    (h : ks.ShapesOk acap) (f : K5HdrField) (v : BitVec 32) :
    (ks.putHdr f v).ShapesOk acap := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
  cases f <;> exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem K512State.ShapesOk.putArr {acap : Nat} {ks : K512State}
    (h : ks.ShapesOk acap) (f : K5ArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).ShapesOk acap := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
  cases f <;> refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simpa [K512State.putArr]

theorem k5State_ext {a b : K512State}
    (h1 : a.nv = b.nv) (h2 : a.nc = b.nc) (h3 : a.lvl = b.lvl) (h4 : a.prop = b.prop)
    (h5 : a.trl_end = b.trl_end) (h6 : a.unass = b.unass) (h7 : a.incons = b.incons)
    (h8 : a.qfirst = b.qfirst) (h9 : a.qlast = b.qlast) (h10 : a.qsearch = b.qsearch)
    (h11 : a.qstamp = b.qstamp) (h12 : a.ticks = b.ticks) (h13 : a.tick_lim = b.tick_lim)
    (h14 : a.alen = b.alen) (h15 : a.acap = b.acap) (h16 : a.nassump = b.nassump)
    (h17 : a.nkl = b.nkl) (h18 : a.nana = b.nana) (h19 : a.status = b.status)
    (h20 : a.phase = b.phase) (h21 : a.hdrTail = b.hdrTail) (h22 : a.lvlArr = b.lvlArr)
    (h23 : a.rsn = b.rsn) (h24 : a.qprev = b.qprev) (h25 : a.qnext = b.qnext)
    (h26 : a.qstampArr = b.qstampArr) (h27 : a.trl = b.trl) (h28 : a.flags = b.flags)
    (h29 : a.ana = b.ana) (h30 : a.kl = b.kl) (h31 : a.assump = b.assump) (h32 : a.vals = b.vals)
    (h33 : a.whead = b.whead) (h34 : a.wnext = b.wnext) (h35 : a.wblit = b.wblit)
    (h36 : a.clOff = b.clOff) (h37 : a.clSz = b.clSz) (h38 : a.arena = b.arena) : a = b := by
  cases a; cases b; simp only [K512State.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38⟩

def K512MemA (kPtr : BitVec 64) (acap : Nat) (ks : K512State) : Mem 64 → Prop :=
  fun m => K512Mem kPtr ks m ∧ ks.ShapesOk acap

theorem k5Mem_to_amem {kPtr : BitVec 64} {acap : Nat} {ks : K512State} {R : Mem 64 → Prop}
    {m : Mem 64} (hsh : ks.ShapesOk acap) (hm : (K512Mem kPtr ks ⋆ R) m) :
    (K512MemA kPtr acap ks ⋆ R) m :=
  sep_mono (fun _ h => ⟨h, hsh⟩) hm

theorem k5MemA_to_mem {kPtr : BitVec 64} {acap : Nat} {ks : K512State} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    ks.ShapesOk acap ∧ (K512Mem kPtr ks ⋆ R) m :=
  sep_pure_l.mp (sep_mono (fun _ ⟨h1, h2⟩ => ⟨h2, h1⟩) hm)

theorem k5Focus_hdr {kPtr : BitVec 64} {ks : K512State} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (K512Mem kPtr ks ⋆ R) m) :
    (array (t := i32) kPtr (k5HdrWords ks) ⋆ ((K512Tree kPtr ks).rest (k5Path 0) ⋆ R)) m :=
  SepTree.focus (t := K512Tree kPtr ks) (k5Path 0) hm

theorem k5Unfocus_hdr {kPtr : BitVec 64} {ks ks' : K512State} {hdr' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (heq : ((K512Tree kPtr ks).set (k5Path 0) (array (t := i32) kPtr hdr')).eval =
      K512Mem kPtr ks')
    (hm : (array (t := i32) kPtr hdr' ⋆ ((K512Tree kPtr ks).rest (k5Path 0) ⋆ R)) m) :
    (K512Mem kPtr ks' ⋆ R) m :=
  SepTree.unfocus_eq (t := K512Tree kPtr ks) (k5Path 0) heq hm

private theorem k5HdrGet {kPtr : BitVec 64} {acap : Nat} {ks : K512State} {R : Mem 64 → Prop}
    {m : Mem 64} (idx : Nat) (hlt : idx < 32) (v : BitVec 32)
    (heq : ∀ hsh : ks.ShapesOk acap,
      (k5HdrWords ks)[idx]'(by rw [k5HdrWords_length hsh]; exact hlt) = v)
    (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 idx * 4) = some v := by
  obtain ⟨hsh, hm'⟩ := k5MemA_to_mem hm
  have hi : idx < (k5HdrWords ks).length := by rw [k5HdrWords_length hsh]; exact hlt
  rw [k5_ptr_nat_mul4 kPtr idx (by omega), ← heq hsh]
  exact sepTree_arr_get (t := K512Tree kPtr ks) (p := k5Path 0) rfl (by decide) hi hm'

private theorem k5HdrPut {kPtr : BitVec 64} {acap : Nat} {ks : K512State} {R : Mem 64 → Prop}
    {m : Mem 64} (f : K5HdrField) (idx : Nat) (v : BitVec 32) (hlt : idx < 32)
    (hset : (k5HdrWords ks).set idx v = k5HdrWords (ks.putHdr f v))
    (heq : ((K512Tree kPtr ks).set (k5Path 0)
      (array (t := i32) kPtr (k5HdrWords (ks.putHdr f v)))).eval = K512Mem kPtr (ks.putHdr f v))
    (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 idx * 4) ∧
      (K512MemA kPtr acap (ks.putHdr f v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 idx * 4) v) := by
  obtain ⟨hsh, hm'⟩ := k5MemA_to_mem hm
  have hi : idx < (k5HdrWords ks).length := by rw [k5HdrWords_length hsh]; exact hlt
  rw [k5_ptr_nat_mul4 kPtr idx (by omega)]
  obtain ⟨hok, hst⟩ := sepTree_arr_put (t := K512Tree kPtr ks) (p := k5Path 0) rfl (by decide) v hi
    (hset ▸ heq) hm'
  exact ⟨hok, k5Mem_to_amem (hsh.putHdr f v) hst⟩

private theorem k5ArrGet {kPtr : BitVec 64} {acap : Nat} {ks : K512State} (p : List Bool)
    (kOff n : Nat) (off32 : BitVec 32) (off64 : BitVec 64) (xs : List (BitVec 32))
    {R : Mem 64 → Prop} {m : Mem 64} (hk : kOff ≤ 19488) (h32 : off32 = BitVec.ofNat 32 kOff)
    (hoff : off64 = BitVec.ofNat 64 (4 * kOff)) (hlen : ks.ShapesOk acap → xs.length = n)
    (hget : (K512Tree kPtr ks).get p = array (t := i32) (kPtr + off64) xs)
    {i : BitVec 32} (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < n)
    (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (off32 + i).setWidth 64 * 4) = some (xs[i.toNat]?.getD 0#32) := by
  obtain ⟨hsh, hm'⟩ := k5MemA_to_mem hm
  have hi' : i.toNat < xs.length := by rw [hlen hsh]; exact hi
  rw [List.getElem?_eq_getElem hi', Option.getD_some,
    k5_ptr_off_bv32_mul4 kPtr kOff off32 hk h32 hlt, ← hoff]
  exact sepTree_arr_get (t := K512Tree kPtr ks) (p := p) hget (by decide) hi' hm'

private theorem k5ArrPut {kPtr : BitVec 64} {acap : Nat} {ks : K512State} (p : List Bool)
    (f : K5ArrField) (kOff n : Nat) (off32 : BitVec 32) (off64 : BitVec 64) (xs : List (BitVec 32))
    {R : Mem 64 → Prop} {m : Mem 64} (hk : kOff ≤ 19488) (h32 : off32 = BitVec.ofNat 32 kOff)
    (hoff : off64 = BitVec.ofNat 64 (4 * kOff)) (hlen : ks.ShapesOk acap → xs.length = n)
    (hget : (K512Tree kPtr ks).get p = array (t := i32) (kPtr + off64) xs) (v : BitVec 32)
    {i : BitVec 32} (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < n)
    (heq : ((K512Tree kPtr ks).set p (array (t := i32) (kPtr + off64) (xs.set i.toNat v))).eval =
      K512Mem kPtr (ks.putArr f i.toNat v))
    (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (off32 + i).setWidth 64 * 4) ∧
      (K512MemA kPtr acap (ks.putArr f i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (off32 + i).setWidth 64 * 4) v) := by
  obtain ⟨hsh, hm'⟩ := k5MemA_to_mem hm
  have hi' : i.toNat < xs.length := by rw [hlen hsh]; exact hi
  rw [k5_ptr_off_bv32_mul4 kPtr kOff off32 hk h32 hlt, ← hoff]
  obtain ⟨hok, hst⟩ := sepTree_arr_put (t := K512Tree kPtr ks) (p := p) hget (by decide) v hi'
    heq hm'
  exact ⟨hok, k5Mem_to_amem (hsh.putArr f i.toNat v) hst⟩

theorem fullAddClause5_mem_to_ka {c : FullCfg} {s : FullState} {scr xs : List (BitVec 32)}
    {litsPtr : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} {acap : Nat} {ks : K512State}
    (h21792 : 21792 ≤ scr.length) (hsh : ks.ShapesOk acap)
    (hof : K512State.ofSlab (scr.drop 2304) = ks)
    (hm : (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      array (t := i32) c.pScratchBuf scr ⋆ array (t := i32) litsPtr xs ⋆ R) m) :
    (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap ks ⋆
      (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
        (array (t := i32) litsPtr xs ⋆
          (array (t := i32) c.pScratchBuf (scr.take 2304) ⋆ R)))) m := by
  rw [array_scratch_eq_k5 h21792, hof] at hm
  exact k5Mem_to_amem hsh (by rw [k5Ptr_base_eq]; exact sep_ac hm)

theorem fullAddClause5_ka_to_mem {c : FullCfg} {s : FullState} {scr xs : List (BitVec 32)}
    {litsPtr : BitVec 64} {R : Mem 64 → Prop} {m' : Mem 64} {acap : Nat} {ks' : K512State}
    (h2304 : 2304 ≤ scr.length) (hsh' : ks'.ShapesOk acap)
    (hm' : (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap ks' ⋆
      (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
        (array (t := i32) litsPtr xs ⋆
          (array (t := i32) c.pScratchBuf (scr.take 2304) ⋆ R)))) m') :
    let scr' := scr.take 2304 ++ ks'.toSlab
    let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
    (array64 (c.hdr + 32) (Full.hdrTailWords c s') ⋆
      array (t := i32) c.pScratchBuf scr' ⋆ array (t := i32) litsPtr xs ⋆ R) m' := by
  intro scr' s'
  obtain ⟨_, hm0⟩ := k5MemA_to_mem hm'
  have htk : (scr.take 2304).length = 2304 := List.length_take_of_le h2304
  have hm1 : (array64 (c.hdr + 32) (Full.hdrTailWords c s') ⋆
      ((array (t := i32) c.pScratchBuf (scr.take 2304) ⋆ K512Mem (c.pScratchBuf + 9216#64) ks') ⋆
      (array (t := i32) litsPtr xs ⋆ R))) m' := by
    have hhdr : Full.hdrTailWords c s' = Full.hdrTailWords c s := rfl
    rw [hhdr]; rw [k5Ptr_base_eq] at hm0; exact sep_ac hm0
  rw [k5_append_eq_array_scratch htk hsh'] at hm1; exact sep_ac hm1

namespace K512MemATactics

attribute [scoped bv_c0] bv32_lshr_1 bv32_and_1 bv32_xor_1 List.length_set Bool.false_eq_true

section FrameAccess
variable {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}

@[scoped c0_load] theorem load_k5f_scratch_cap (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 928) = some (BitVec.ofNat 64 c.scratch_cap) :=
  FullArenaTactics.load_full_scratch_cap hm
@[scoped c0_load] theorem load_k5fr_scratch_cap (hm : (FullK512Frame c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 928) = some (BitVec.ofNat 64 c.scratch_cap) := by
  simpa [Full.hdrTailWords, hdrTailWords0, hdrTailWords1, hdrTailWords2, hdrTailWords3] using
    fullK5Frame_hdrGet 112 (by decide) hm
@[scoped c0_load] theorem load_k5f_scratch_buf (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf :=
  FullArenaTactics.load_full_scratch_buf_ptr hm
@[scoped c0_load] theorem load_k5fr_scratch_buf (hm : (FullK512Frame c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf := by
  simpa [Full.hdrTailWords, hdrTailWords0, hdrTailWords1, hdrTailWords2, hdrTailWords3] using
    fullK5Frame_hdrGet 111 (by decide) hm
@[scoped c0_load] theorem load_k5fr_fuel (hm : (FullK512Frame c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 168) = some s.core.fuel := by
  simpa [Full.hdrTailWords, hdrTailWords0, hdrTailWords1, hdrTailWords2, hdrTailWords3] using
    fullK5Frame_hdrGet 17 (by decide) hm
@[scoped c0_store] theorem store_k5fr_fuel (v : BitVec 64) (hm : (FullK512Frame c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 168) ∧
      (FullK512Frame c { s with core := { s.core with fuel := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 168) v) := fullK5Frame_fuel_store v hm
@[scoped c0_load] theorem load_k5hdrTail_scratch_buf
    (hm : (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf := by
  have hl := loadVal_array64 (i := 111) (by rw [Full.hdrTailWords_length]; decide) hm
  rw [show c.hdr + 32 + BitVec.ofNat 64 (8 * 111) = c.hdr + 920 from
    ptr_add_ofNat c.hdr 32 888] at hl
  simpa [Full.hdrTailWords, hdrTailWords0, hdrTailWords1, hdrTailWords2, hdrTailWords3] using hl
@[scoped c0_load] theorem load_k5arr32_z0 {a : BitVec 64} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m) (hi : 0 < xs.length) :
    loadVal m i32 (a + BitVec.ofNat 64 0 * 4) = some (xs[0]'hi) := by
  rw [k5_ptr_nat_mul4 a 0 (by decide)]; exact loadVal_array (t := i32) (by decide) hi h
@[scoped c0_load] theorem load_k5arr32_z1 {a : BitVec 64} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m) (hi : 1 < xs.length) :
    loadVal m i32 (a + BitVec.ofNat 64 1 * 4) = some (xs[1]'hi) := by
  rw [k5_ptr_nat_mul4 a 1 (by decide)]; exact loadVal_array (t := i32) (by decide) hi h
@[scoped c0_load] theorem load_k5arr32_u32 {a : BitVec 64} {i : BitVec 32} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i32 (a + i.setWidth 64 * 4) = some (xs[i.toNat]'hi) := by
  rw [show (4 : BitVec 64) = 4#64 from rfl]; exact c0_load_array32_u32 h hi
@[scoped c0_store] theorem store_k5arr32_u32 {a : BitVec 64} {i : BitVec 32} {xs : List (BitVec 32)}
    (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    storeOk m i32 (a + i.setWidth 64 * 4) ∧
      (array (t := i32) a (xs.set i.toNat v) ⋆ R) (storeMem m i32 (a + i.setWidth 64 * 4) v) := by
  rw [show (4 : BitVec 64) = 4#64 from rfl]; exact c0_store_array32_u32 v h hi
end FrameAccess

local syntax "def_k5_hdr " ident num : command
local macro_rules
  | `(def_k5_hdr $fld $idx) => do
    let lnm := Lean.mkIdent (Lean.Name.mkSimple s!"load_k5_{fld.getId}")
    let snm := Lean.mkIdent (Lean.Name.mkSimple s!"store_k5_{fld.getId}")
    let pnm := Lean.mkIdent (Lean.Name.mkSimple s!"putArr_{fld.getId}")
    let hnm := Lean.mkIdent (Lean.Name.mkSimple s!"putHdr_{fld.getId}")
    let tag := Lean.mkIdent (`K5HdrField ++ fld.getId)
    `(
      @[scoped bv_c0] theorem $pnm (ks : K512State) (f : K5ArrField) (i : Nat) (v : BitVec 32) :
          (ks.putArr f i v).$fld = ks.$fld := by cases f <;> rfl
      theorem $hnm (ks : K512State) (f : K5HdrField) (v : BitVec 32) :
          (ks.putHdr f v).$fld = if f = $tag then v else ks.$fld := by cases f <;> rfl
      @[scoped c0_load] theorem $lnm {kPtr : BitVec 64} {acap : Nat} {ks : K512State}
          {R : Mem 64 → Prop} {m : Mem 64} (hm : (K512MemA kPtr acap ks ⋆ R) m) :
          loadVal m i32 (kPtr + BitVec.ofNat 64 ($idx) * 4) = some ks.$fld :=
        k5HdrGet ($idx) (by decide) ks.$fld (fun _ => rfl) hm
      @[scoped c0_store] theorem $snm {kPtr : BitVec 64} {acap : Nat} {ks : K512State}
          {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (K512MemA kPtr acap ks ⋆ R) m) :
          storeOk m i32 (kPtr + BitVec.ofNat 64 ($idx) * 4) ∧
            (K512MemA kPtr acap (ks.putHdr $tag v) ⋆ R)
              (storeMem m i32 (kPtr + BitVec.ofNat 64 ($idx) * 4) v) :=
        k5HdrPut $tag ($idx) v (by decide) rfl
          (by simp only [K512Mem, K512Tree, k5Path, SepTree.set, SepTree.eval, k5HdrWords,
            K512State.putHdr]) hm
    )

def_k5_hdr nv 0
def_k5_hdr nc 1
def_k5_hdr lvl 2
def_k5_hdr prop 3
def_k5_hdr trl_end 4
def_k5_hdr unass 5
def_k5_hdr incons 6
def_k5_hdr qfirst 7
def_k5_hdr qlast 8
def_k5_hdr qsearch 9
def_k5_hdr qstamp 10
def_k5_hdr ticks 11
def_k5_hdr tick_lim 12
def_k5_hdr alen 13
def_k5_hdr acap 14
def_k5_hdr nassump 15
def_k5_hdr nkl 16
def_k5_hdr nana 17
def_k5_hdr status 18
def_k5_hdr phase 19

theorem putHdr_hdrTail (ks : K512State) (f : K5HdrField) (v : BitVec 32) :
    (ks.putHdr f v).hdrTail = ks.hdrTail := by cases f <;> rfl
theorem putArr_hdrTail (ks : K512State) (f : K5ArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).hdrTail = ks.hdrTail := by cases f <;> rfl

local syntax "def_k5_arr " ident num num num num ident : command
local macro_rules
  | `(def_k5_arr $fld $pidx $koff $boff $sz $lenfld) => do
    let lnm := Lean.mkIdent (Lean.Name.mkSimple s!"load_k5_{fld.getId}")
    let snm := Lean.mkIdent (Lean.Name.mkSimple s!"store_k5_{fld.getId}")
    let hnm := Lean.mkIdent (Lean.Name.mkSimple s!"putHdr_{fld.getId}")
    let pnm := Lean.mkIdent (Lean.Name.mkSimple s!"putArr_{fld.getId}")
    let tag := Lean.mkIdent (`K5ArrField ++ fld.getId)
    `(
      @[scoped bv_c0] theorem $hnm (ks : K512State) (f : K5HdrField) (v : BitVec 32) :
          (ks.putHdr f v).$fld = ks.$fld := by cases f <;> rfl
      theorem $pnm (ks : K512State) (f : K5ArrField) (i : Nat) (v : BitVec 32) :
          (ks.putArr f i v).$fld = if f = $tag then (ks.$fld).set i v else ks.$fld := by
        cases f <;> rfl
      @[scoped c0_load] theorem $lnm {kPtr : BitVec 64} {acap : Nat} {ks : K512State}
          {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 32} (hi : i.toNat < $sz)
          (hm : (K512MemA kPtr acap ks ⋆ R) m) :
          loadVal m i32 (kPtr + ($koff + i).setWidth 64 * 4) =
            some ((ks.$fld)[i.toNat]?.getD 0#32) :=
        k5ArrGet (k5Path $pidx) $koff $sz $koff (BitVec.ofNat 64 $boff) ks.$fld (by decide) rfl rfl
          (fun h => h.$lenfld) (by simp only [K512Tree, k5Path, SepTree.get]) (by omega) hi hm
      @[scoped c0_store] theorem $snm {kPtr : BitVec 64} {acap : Nat} {ks : K512State}
          {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {i : BitVec 32} (hi : i.toNat < $sz)
          (hm : (K512MemA kPtr acap ks ⋆ R) m) :
          storeOk m i32 (kPtr + ($koff + i).setWidth 64 * 4) ∧
            (K512MemA kPtr acap (ks.putArr $tag i.toNat v) ⋆ R)
              (storeMem m i32 (kPtr + ($koff + i).setWidth 64 * 4) v) :=
        k5ArrPut (k5Path $pidx) $tag $koff $sz $koff (BitVec.ofNat 64 $boff) ks.$fld (by decide)
          rfl rfl (fun h => h.$lenfld) (by simp only [K512Tree, k5Path, SepTree.get]) v (by omega)
          hi (by simp only [K512Mem, K512Tree, k5Path, SepTree.set, SepTree.eval, k5HdrWords,
            K512State.putArr]) hm
    )

def_k5_arr lvlArr 1 32 128 512 lvlArr_len
def_k5_arr rsn 2 544 2176 512 rsn_len
def_k5_arr qprev 3 1056 4224 512 qprev_len
def_k5_arr qnext 4 1568 6272 512 qnext_len
def_k5_arr qstampArr 5 2080 8320 512 qstampArr_len
def_k5_arr trl 6 2592 10368 512 trl_len
def_k5_arr flags 7 3104 12416 512 flags_len
def_k5_arr ana 8 3616 14464 512 ana_len
def_k5_arr kl 9 4128 16512 512 kl_len
def_k5_arr assump 10 4640 18560 512 assump_len
def_k5_arr vals 11 5152 20608 1024 vals_len
def_k5_arr whead 12 6176 24704 1024 whead_len
def_k5_arr wnext 13 7200 28800 4096 wnext_len
def_k5_arr wblit 14 11296 45184 4096 wblit_len
def_k5_arr clOff 15 15392 61568 2048 clOff_len
def_k5_arr clSz 16 17440 69760 2048 clSz_len

@[scoped bv_c0] theorem putHdr_arena (ks : K512State) (f : K5HdrField) (v : BitVec 32) :
    (ks.putHdr f v).arena = ks.arena := by cases f <;> rfl
theorem putArr_arena (ks : K512State) (f : K5ArrField) (i : Nat) (v : BitVec 32) :
    (ks.putArr f i v).arena = if f = .arena then ks.arena.set i v else ks.arena := by
  cases f <;> rfl

section ExtraK5Access
variable {kPtr : BitVec 64} {acap : Nat} {ks : K512State} {R : Mem 64 → Prop} {m : Mem 64}

@[scoped c0_load] theorem load_k5_arena {i : BitVec 32} (hlt : i.toNat < 2 ^ 28)
    (hi : i.toNat < acap) (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (19488 + i).setWidth 64 * 4) = some (ks.arena[i.toNat]?.getD 0#32) :=
  k5ArrGet (k5Path 17) 19488 acap 19488 77952#64 ks.arena (by decide) rfl rfl
    (fun h => h.arena_len) (by simp only [K512Tree, k5Path, SepTree.get]) hlt hi hm

@[scoped c0_store] theorem store_k5_arena (v : BitVec 32) {i : BitVec 32}
    (hlt : i.toNat < 2 ^ 28) (hi : i.toNat < acap) (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (19488 + i).setWidth 64 * 4) ∧
      (K512MemA kPtr acap (ks.putArr .arena i.toNat v) ⋆ R)
        (storeMem m i32 (kPtr + (19488 + i).setWidth 64 * 4) v) :=
  k5ArrPut (k5Path 17) .arena 19488 acap 19488 77952#64 ks.arena (by decide) rfl rfl
    (fun h => h.arena_len) (by simp only [K512Tree, k5Path, SepTree.get]) v hlt hi
    (by simp only [K512Mem, K512Tree, k5Path, SepTree.set, SepTree.eval, k5HdrWords,
      K512State.putArr]) hm

@[scoped c0_load] theorem load_k5_arena_off {off j : BitVec 32}
    (hwrap : off.toNat + j.toNat < 2 ^ 28) (hi : off.toNat + j.toNat < acap)
    (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + ((19488 + off) + j).setWidth 64 * 4) =
      some (ks.arena[off.toNat + j.toNat]?.getD 0#32) := by
  have heq : ((19488 : BitVec 32) + off) + j = 19488 + (off + j) := BitVec.add_assoc _ _ _
  have hoj : (off + j).toNat = off.toNat + j.toNat := by bv_omega
  rw [heq]; simpa [hoj] using load_k5_arena (i := off + j) (by rw [hoj]; exact hwrap)
    (by rw [hoj]; exact hi) hm

@[scoped c0_store] theorem store_k5_arena_off (v : BitVec 32) {off j : BitVec 32}
    (hwrap : off.toNat + j.toNat < 2 ^ 28) (hi : off.toNat + j.toNat < acap)
    (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + ((19488 + off) + j).setWidth 64 * 4) ∧
      (K512MemA kPtr acap (ks.putArr .arena (off.toNat + j.toNat) v) ⋆ R)
        (storeMem m i32 (kPtr + ((19488 + off) + j).setWidth 64 * 4) v) := by
  have heq : ((19488 : BitVec 32) + off) + j = 19488 + (off + j) := BitVec.add_assoc _ _ _
  have hoj : (off + j).toNat = off.toNat + j.toNat := by bv_omega
  rw [heq]; simpa [hoj] using store_k5_arena v (i := off + j) (by rw [hoj]; exact hwrap)
    (by rw [hoj]; exact hi) hm

@[scoped c0_load] theorem load_k5_kl0 (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 4128 * 4) = some (ks.kl[0]?.getD 0#32) := by
  simpa using load_k5_kl (by decide : (0#32).toNat < 512) hm

@[scoped c0_store] theorem store_k5_kl0 (v : BitVec 32) (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 4128 * 4) ∧
      (K512MemA kPtr acap (ks.putArr .kl 0 v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 4128 * 4) v) := by
  simpa using store_k5_kl v (by decide : (0#32).toNat < 512) hm

@[scoped c0_load] theorem load_k5_kl1 (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 4129 * 4) = some (ks.kl[1]?.getD 0#32) := by
  simpa using load_k5_kl (by decide : (1#32).toNat < 512) hm

@[scoped c0_store] theorem store_k5_kl1 (v : BitVec 32) (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 4129 * 4) ∧
      (K512MemA kPtr acap (ks.putArr .kl 1 v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 4129 * 4) v) := by
  simpa using store_k5_kl v (by decide : (1#32).toNat < 512) hm

@[scoped c0_load] theorem load_k5_assump0 (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 4640 * 4) = some (ks.assump[0]?.getD 0#32) := by
  simpa using load_k5_assump (by decide : (0#32).toNat < 512) hm

@[scoped c0_store] theorem store_k5_assump0 (v : BitVec 32) (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 4640 * 4) ∧
      (K512MemA kPtr acap (ks.putArr .assump 0 v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 4640 * 4) v) := by
  simpa using store_k5_assump v (by decide : (0#32).toNat < 512) hm

@[scoped c0_load] theorem load_k5_assump1 (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + BitVec.ofNat 64 4641 * 4) = some (ks.assump[1]?.getD 0#32) := by
  simpa using load_k5_assump (by decide : (1#32).toNat < 512) hm

@[scoped c0_store] theorem store_k5_assump1 (v : BitVec 32) (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + BitVec.ofNat 64 4641 * 4) ∧
      (K512MemA kPtr acap (ks.putArr .assump 1 v) ⋆ R)
        (storeMem m i32 (kPtr + BitVec.ofNat 64 4641 * 4) v) := by
  simpa using store_k5_assump v (by decide : (1#32).toNat < 512) hm

@[scoped c0_load] theorem load_k5_trl_sub1 {te : BitVec 32} (hpos : 0 < te.toNat)
    (hi : te.toNat - 1 < 512) (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    loadVal m i32 (kPtr + (2592 + te - 1).setWidth 64 * 4) =
      some (ks.trl[te.toNat - 1]?.getD 0#32) := by
  have heq : (2592 : BitVec 32) + te - 1 = 2592 + (te - 1#32) := by bv_omega
  have hsub : (te - 1#32).toNat = te.toNat - 1 := by bv_omega
  rw [heq]; simpa [hsub] using load_k5_trl (by rw [hsub]; exact hi : (te - 1#32).toNat < 512) hm

@[scoped c0_store] theorem store_k5_qnext_sub1 (v : BitVec 32) {nv : BitVec 32}
    (hpos : 0 < nv.toNat) (hi : nv.toNat - 1 < 512) (hm : (K512MemA kPtr acap ks ⋆ R) m) :
    storeOk m i32 (kPtr + (1568 + nv - 1).setWidth 64 * 4) ∧
      (K512MemA kPtr acap (ks.putArr .qnext (nv.toNat - 1) v) ⋆ R)
        (storeMem m i32 (kPtr + (1568 + nv - 1).setWidth 64 * 4) v) := by
  have heq : (1568 : BitVec 32) + nv - 1 = 1568 + (nv - 1#32) := by bv_omega
  have hsub : (nv - 1#32).toNat = nv.toNat - 1 := by bv_omega
  rw [heq]
  simpa [hsub] using store_k5_qnext v (by rw [hsub]; exact hi : (nv - 1#32).toNat < 512) hm
end ExtraK5Access

scoped macro "c0_call " h:ident : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

scoped macro "k5_field" : tactic => `(tactic|
  simp only [
    putHdr_nv, putHdr_nc, putHdr_lvl, putHdr_prop, putHdr_trl_end, putHdr_unass, putHdr_incons,
    putHdr_qfirst, putHdr_qlast, putHdr_qsearch, putHdr_qstamp, putHdr_ticks, putHdr_tick_lim,
    putHdr_alen, putHdr_acap, putHdr_nassump, putHdr_nkl, putHdr_nana, putHdr_status, putHdr_phase,
    putHdr_hdrTail, putArr_hdrTail, putArr_nv, putArr_nc, putArr_lvl, putArr_prop, putArr_trl_end,
    putArr_unass, putArr_incons, putArr_qfirst, putArr_qlast, putArr_qsearch, putArr_qstamp,
    putArr_ticks, putArr_tick_lim, putArr_alen, putArr_acap, putArr_nassump, putArr_nkl,
    putArr_nana, putArr_status, putArr_phase,
    putHdr_lvlArr, putHdr_rsn, putHdr_qprev, putHdr_qnext, putHdr_qstampArr, putHdr_trl,
    putHdr_flags, putHdr_ana, putHdr_kl, putHdr_assump, putHdr_vals, putHdr_whead, putHdr_wnext,
    putHdr_wblit, putHdr_clOff, putHdr_clSz, putHdr_arena,
    putArr_lvlArr, putArr_rsn, putArr_qprev, putArr_qnext, putArr_qstampArr, putArr_trl,
    putArr_flags, putArr_ana, putArr_kl, putArr_assump, putArr_vals, putArr_whead, putArr_wnext,
    putArr_wblit, putArr_clOff, putArr_clSz, putArr_arena,
    reduceCtorEq, ite_true, ite_false])

scoped macro "k5_ext" : tactic => `(tactic|
  (apply k5State_ext <;> (k5_field; try rfl)))

end K512MemATactics

/-! ## 4. Semantic Model-Set Invariants (`K512Inv`, `ConeModelSet`, `PhtOk`) -/

/-- Model-set semantic entailment: every local assignment `β` in `P` satisfies clause `cl`. -/
def SemEntails (P : (Nat → Bool) → Prop) (cl : List Nat) : Prop :=
  ∀ β, P β → (cnfClause cl).Sat β

/-- Cone projection of global models of `F_cur` onto local variables `0 ..< nv` via `work_stk1`. -/
def ConeModelSet (F_cur : List (List Nat)) (cone_v : List (BitVec 32)) (nv : Nat)
    (β : Nat → Bool) : Prop :=
  ∃ α, (cnfOfClauses F_cur).Sat α ∧ ∀ i < nv, β i = α (cone_v[i]?.getD 0#32).toNat

def k5WatchStep0 (ks : K512State) (w l valOther : BitVec 32) : K512State :=
  let wi := w.toNat; let li := l.toNat
  { ks with
    wblit := ks.wblit.set wi valOther
    wnext := ks.wnext.set wi (ks.whead[li]?.getD 0#32)
    whead := ks.whead.set li w }

def k5WatchStep (ks : K512State) (cid l0 l1 : BitVec 32) : K512State :=
  let w0 := cid <<< 1; let w1 := w0 ||| 1#32
  k5WatchStep0 (k5WatchStep0 ks w0 l0 l1) w1 l1 l0

def k5AssignStep (ks : K512State) (lit rsn : BitVec 32) : K512State :=
  let v := (lit >>> 1).toNat; let li := lit.toNat; let nli := (lit ^^^ 1#32).toNat
  let te := ks.trl_end.toNat
  let unass' := if ks.unass.toNat > 0 then ks.unass - 1#32 else ks.unass
  let fl := ks.flags[v]?.getD 0#32
  let fl' := if (lit &&& 1#32) ≠ 0#32 then fl ||| 1#32 else fl &&& ~~~1#32
  { ks with
    vals := (ks.vals.set li 1#32).set nli 2#32
    lvlArr := ks.lvlArr.set v ks.lvl
    rsn := ks.rsn.set v rsn
    trl := ks.trl.set te lit
    trl_end := ks.trl_end + 1#32
    unass := unass'
    flags := ks.flags.set v fl' }

inductive K5WChain (wnext : List (BitVec 32)) : BitVec 32 → List Nat → Prop where
  | nil : K5WChain wnext 0xFFFFFFFF#32 []
  | cons {w : Nat} {ws : List Nat} (hw : w < wnext.length) :
      K5WChain wnext (wnext[w]'hw) ws → K5WChain wnext (BitVec.ofNat 32 w) (w :: ws)

def k5ClauseOff (ks : K512State) (cid : Nat) : Nat := (ks.clOff[cid]?.getD 0#32).toNat
def k5ClauseSize (ks : K512State) (cid : Nat) : Nat := (ks.clSz[cid]?.getD 0#32).toNat
def k5ClauseLits (ks : K512State) (cid : Nat) : List Nat :=
  ((ks.arena.drop (k5ClauseOff ks cid)).take (k5ClauseSize ks cid)).map BitVec.toNat
def k5AssumpLits (ks : K512State) : List Nat :=
  (ks.assump.take ks.nassump.toNat).map BitVec.toNat
def k5TrailLits (ks : K512State) : List Nat :=
  (ks.trl.take ks.trl_end.toNat).map BitVec.toNat

/-- Positive-level decisions on the trail (`lvl > 0 ∧ rsn = 0xFFFFFFFF`). -/
def k5TrailDecisions (ks : K512State) : List Nat :=
  (ks.trl.take ks.trl_end.toNat).filterMap fun l =>
    if 0 < (ks.lvlArr[l.toNat / 2]?.getD 0#32).toNat ∧
       ks.rsn[l.toNat / 2]?.getD 0#32 = 0xFFFFFFFF#32
    then some l.toNat else none

def K512WatchesOk (ks : K512State) : Prop :=
  ∃ chains : List (List Nat),
    chains.length = 2 * ks.nv.toNat ∧ chains.flatten.Nodup ∧
    (∀ l < 2 * ks.nv.toNat,
      K5WChain ks.wnext (ks.whead[l]?.getD 0xFFFFFFFF#32) (chains[l]?.getD [])) ∧
    (∀ l < 2 * ks.nv.toNat, ∀ w ∈ chains[l]?.getD [],
      w < 2 * ks.nc.toNat ∧ 2 ≤ k5ClauseSize ks (w / 2) ∧
      (ks.arena[k5ClauseOff ks (w / 2) + (w % 2)]?.getD 0#32).toNat = l ∧
      (ks.wblit[w]?.getD 0#32).toNat < 2 * ks.nv.toNat)

structure K512ClausesOk (acap : Nat) (P : (Nat → Bool) → Prop) (ks : K512State) : Prop where
  acap_ge : k5MinScr - k5Base - k5SlabFixed ≤ acap
  acap_lt : acap < dimacsBound
  acap_eq : ks.acap = BitVec.ofNat 32 acap
  nv_le : ks.nv.toNat ≤ k5MaxV
  nc_le : ks.nc.toNat ≤ k5MaxCl
  alen_le : ks.alen.toNat ≤ acap
  nassump_le : ks.nassump.toNat ≤ k5MaxV
  nkl_le : ks.nkl.toNat ≤ k5MaxV
  nana_le : ks.nana.toNat ≤ k5MaxV
  cl_wf : ∀ cid < ks.nc.toNat,
    2 ≤ k5ClauseSize ks cid ∧
    k5ClauseOff ks cid + k5ClauseSize ks cid ≤ ks.alen.toNat ∧
    (∀ l ∈ k5ClauseLits ks cid, l < 2 * ks.nv.toNat) ∧
    SemEntails P (k5ClauseLits ks cid)
  cl_mono : ∀ c1 c2, c1 < c2 → c2 < ks.nc.toNat →
    k5ClauseOff ks c1 + k5ClauseSize ks c1 ≤ k5ClauseOff ks c2
  incons_ok : ks.incons ≠ 0#32 → ∀ β, ¬ P β
  assump_ok : ∀ i < ks.nassump.toNat, (ks.assump[i]?.getD 0#32).toNat < 2 * ks.nv.toNat
  flags_clean : ∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) = 0#32

structure K512BaseAssignOk (P : (Nat → Bool) → Prop) (ks : K512State) : Prop where
  trl_end_le : ks.trl_end.toNat ≤ ks.nv.toNat
  prop_le : ks.prop.toNat ≤ ks.trl_end.toNat
  unass_eq : ks.unass.toNat + ks.trl_end.toNat = ks.nv.toNat
  vals_dom : ∀ l < 2 * ks.nv.toNat,
    let v := ks.vals[l]?.getD 0#32; v = 0#32 ∨ v = 1#32 ∨ v = 2#32
  vals_neg_iff : ∀ l < 2 * ks.nv.toNat,
    ks.vals[l]?.getD 0#32 = 1#32 ↔ ks.vals[l ^^^ 1]?.getD 0#32 = 2#32
  vals_nz_iff_trl : ∀ l < 2 * ks.nv.toNat,
    ks.vals[l]?.getD 0#32 ≠ 0#32 ↔
      ∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2
  trl_nodup : (k5TrailLits ks |>.map (· / 2)).Nodup
  trl_lt : ∀ l ∈ k5TrailLits ks, l < 2 * ks.nv.toNat
  trl_lvl_le : ∀ v < ks.nv.toNat, (ks.lvlArr[v]?.getD 0#32).toNat ≤ ks.lvl.toNat
  unass_lvl_zero : ∀ v < ks.nv.toNat, ks.vals[2 * v]?.getD 0#32 = 0#32 →
    ks.lvlArr[v]?.getD 0#32 = 0#32 ∧ ks.rsn[v]?.getD 0#32 = 0xFFFFFFFF#32
  trl_lvl_mono : ∀ i j, i ≤ j → j < ks.trl_end.toNat →
    (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
    (ks.lvlArr[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  dec_earliest : ∀ i j, j < i → i < ks.trl_end.toNat →
    0 < (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
    ks.lvlArr[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 =
      ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 →
    ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ 0xFFFFFFFF#32
  lvl0_ok : ∀ i < ks.trl_end.toNat,
    let l := (ks.trl[i]?.getD 0#32).toNat
    ks.lvlArr[l / 2]?.getD 0#32 = 0#32 →
    ks.vals[l]? = some 1#32 ∧ ks.vals[l ^^^ 1]? = some 2#32 ∧ SemEntails P [l]

def K512TrailSynced (ks : K512State) : Prop :=
  ∀ i < ks.trl_end.toNat,
    let l := (ks.trl[i]?.getD 0#32).toNat
    ks.vals[l]? = some 1#32 ∧ ks.vals[l ^^^ 1]? = some 2#32

def K512ReasonOk (ks : K512State) : Prop :=
  ∀ i < ks.trl_end.toNat,
    let l := (ks.trl[i]?.getD 0#32).toNat
    let r := ks.rsn[l / 2]?.getD 0#32
    r = 0xFFFFFFFF#32 ∨
    (r.toNat < ks.nc.toNat ∧ l ∈ k5ClauseLits ks r.toNat ∧
     ∀ x ∈ k5ClauseLits ks r.toNat, x ≠ l → ∃ j < i, (ks.trl[j]?.getD 0#32).toNat = x ^^^ 1)

structure K512Inv (acap : Nat) (P : (Nat → Bool) → Prop) (ks : K512State) : Prop where
  shapes : ks.ShapesOk acap
  clauses : K512ClausesOk acap P ks
  watches : K512WatchesOk ks
  assign : K512BaseAssignOk P ks
  reasons : K512ReasonOk ks

def k5StateOfScratch (scr : List (BitVec 32)) : K512State := K512State.ofSlab (scr.drop k5Base)
def k5AssumpLitsS (scr : List (BitVec 32)) : List Nat := k5AssumpLits (k5StateOfScratch scr)

def K512ScratchInv (P : (Nat → Bool) → Prop) (scr : List (BitVec 32)) : Prop :=
  k5MinScr ≤ scr.length ∧ scr.length < dimacsBound ∧
  K512Inv (scr.length - (k5Base + k5SlabFixed)) P (k5StateOfScratch scr)

/-- Every clause literal and watch blocking literal lies below `2 * M`. -/
def K512LitsBounded (M : Nat) (ks : K512State) : Prop :=
  (∀ cid < ks.nc.toNat, ∀ l ∈ k5ClauseLits ks cid, l < 2 * M) ∧
  (∀ w < 2 * ks.nc.toNat, (ks.wblit[w]?.getD 0#32).toNat < 2 * M)

def k5ResolventLits (ks : K512State) (idx : Nat) : List Nat :=
  let seenTop := ((List.range idx).filterMap fun j =>
    let l := (ks.trl[j]?.getD 0#32).toNat
    if ks.lvlArr[l / 2]?.getD 0#32 = ks.lvl ∧ (ks.flags[l / 2]?.getD 0#32 &&& 2#32) ≠ 0#32
    then some (l ^^^ 1) else none)
  let klLits := ((ks.kl.take ks.nkl.toNat).drop 1).map BitVec.toNat
  seenTop ++ klLits

structure K512AnaInv (acap : Nat) (P : (Nat → Bool) → Prop) (ks : K512State) (idx : Nat) :
    Prop where
  shapes : ks.ShapesOk acap
  acap_ge : k5MinScr - k5Base - k5SlabFixed ≤ acap
  acap_lt : acap < dimacsBound
  acap_eq : ks.acap = BitVec.ofNat 32 acap
  nv_le : ks.nv.toNat ≤ k5MaxV
  nc_le : ks.nc.toNat ≤ k5MaxCl
  alen_le : ks.alen.toNat ≤ acap
  nassump_le : ks.nassump.toNat ≤ k5MaxV
  lvl_pos : 0 < ks.lvl.toNat
  idx_le : idx ≤ ks.trl_end.toNat
  cl_wf : ∀ cid < ks.nc.toNat,
    2 ≤ k5ClauseSize ks cid ∧ k5ClauseOff ks cid + k5ClauseSize ks cid ≤ ks.alen.toNat ∧
    (∀ l ∈ k5ClauseLits ks cid, l < 2 * ks.nv.toNat) ∧ SemEntails P (k5ClauseLits ks cid)
  cl_mono : ∀ c1 c2, c1 < c2 → c2 < ks.nc.toNat →
    k5ClauseOff ks c1 + k5ClauseSize ks c1 ≤ k5ClauseOff ks c2
  incons_ok : ks.incons ≠ 0#32 → ∀ β, ¬ P β
  assump_ok : ∀ i < ks.nassump.toNat, (ks.assump[i]?.getD 0#32).toNat < 2 * ks.nv.toNat
  watches : K512WatchesOk ks
  assign : K512BaseAssignOk P ks
  synced : K512TrailSynced ks
  reasons : K512ReasonOk ks
  nkl_pos : 1 ≤ ks.nkl.toNat
  nkl_le : ks.nkl.toNat ≤ ks.nv.toNat
  nana_le : ks.nana.toNat ≤ ks.nv.toNat
  ana_nodup : ((ks.ana.take ks.nana.toNat).map BitVec.toNat).Nodup
  ana_lt : ∀ i < ks.nana.toNat, (ks.ana[i]?.getD 0#32).toNat < ks.nv.toNat
  flags_seen : ∀ v < ks.nv.toNat,
    ((ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32) ↔
      ∃ i < ks.nana.toNat, (ks.ana[i]?.getD 0#32).toNat = v
  kl_nonTop : ∀ i, 1 ≤ i → i < ks.nkl.toNat →
    let l := (ks.kl[i]?.getD 0#32).toNat
    l < 2 * ks.nv.toNat ∧ (ks.flags[l / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 ∧
    0 < (ks.lvlArr[l / 2]?.getD 0#32).toNat ∧ (ks.lvlArr[l / 2]?.getD 0#32).toNat < ks.lvl.toNat ∧
    ks.vals[l]? = some 2#32
  kl_injective : ∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
    (ks.lvlArr[v]?.getD 0#32).toNat < ks.lvl.toNat →
    ∃ i, 1 ≤ i ∧ i < ks.nkl.toNat ∧ (ks.kl[i]?.getD 0#32).toNat / 2 = v
  nkl_count : ∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
    0 < (ks.lvlArr[v]?.getD 0#32).toNat
  kl_nodup : (((ks.kl.take ks.nkl.toNat).drop 1).map (fun l => l.toNat / 2)).Nodup
  status_eq : ks.status.toNat =
    ((List.range idx).filter fun j =>
      let v := (ks.trl[j]?.getD 0#32).toNat / 2
      decide (ks.lvlArr[v]?.getD 0#32 = ks.lvl ∧ (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)).length
  seen_in_trl : ∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
    ks.lvlArr[v]?.getD 0#32 = ks.lvl →
    ∃ j < ks.trl_end.toNat, (ks.trl[j]?.getD 0#32).toNat / 2 = v

/-- Strictly decreasing acyclic partition-class hash chains in `scratch_buf[256..1792)`. -/
def PhtOk (nv : Nat) (scr : List (BitVec 32)) : Prop :=
  (∀ b < phtSz,
    let h := scr[phtHead + b]?.getD 0xFFFFFFFF#32
    h = 0xFFFFFFFF#32 ∨ h.toNat < nv) ∧
  (∀ i < nv,
    let nx := scr[phtNext + i]?.getD 0xFFFFFFFF#32
    nx = 0xFFFFFFFF#32 ∨ nx.toNat < i)

/-- Zero-initialized `tarjan_mark[0 ..< cur_vars)` for M4 sweeping. -/
def M4TmkZero (s : FullState) : Prop :=
  ∀ v < s.core.cur_vars, s.scratch.tarjan_mark[v]?.getD 0#32 = 0#32

/-- Valid 512-var cone invariant for `full_m4_sweep_*`. -/
def M4SweepConeOk (F_cur : List (List Nat)) (s : FullState) (nv : Nat) : Prop :=
  1 ≤ nv ∧ nv ≤ k5MaxV ∧ nv ≤ s.core.cur_vars ∧
  (∀ i < nv, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
  K512ScratchInv (ConeModelSet F_cur s.scratch.work_stk1 nv) s.scratch.scratch_buf ∧
  (k5StateOfScratch s.scratch.scratch_buf).nv = BitVec.ofNat 32 nv

/-- Unchanged `K512State` fields across `full_k512_backtrack`. -/
structure K5BtPreserved (ks ks' : K512State) : Prop where
  nv : ks'.nv = ks.nv
  nc : ks'.nc = ks.nc
  incons : ks'.incons = ks.incons
  alen : ks'.alen = ks.alen
  acap : ks'.acap = ks.acap
  nassump : ks'.nassump = ks.nassump
  nkl : ks'.nkl = ks.nkl
  nana : ks'.nana = ks.nana
  status : ks'.status = ks.status
  phase : ks'.phase = ks.phase
  hdrTail : ks'.hdrTail = ks.hdrTail
  assump : ks'.assump = ks.assump
  ana : ks'.ana = ks.ana
  kl : ks'.kl = ks.kl
  whead : ks'.whead = ks.whead
  wnext : ks'.wnext = ks.wnext
  wblit : ks'.wblit = ks.wblit
  clOff : ks'.clOff = ks.clOff
  clSz : ks'.clSz = ks.clSz
  arena : ks'.arena = ks.arena
  flags2_eq : ∀ v < ks.nv.toNat,
    (ks'.flags[v]?.getD 0#32 &&& 2#32) = (ks.flags[v]?.getD 0#32 &&& 2#32)
  lvlArr_kept : ∀ i < ks'.trl_end.toNat,
    ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]? =
      ks.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?

/-- Unchanged `K512State` fields across `full_k512_ana_clause`. -/
structure K5AnaPreserved (ks ks' : K512State) : Prop where
  nv : ks'.nv = ks.nv
  nc : ks'.nc = ks.nc
  lvl : ks'.lvl = ks.lvl
  prop : ks'.prop = ks.prop
  trl_end : ks'.trl_end = ks.trl_end
  unass : ks'.unass = ks.unass
  incons : ks'.incons = ks.incons
  alen : ks'.alen = ks.alen
  acap : ks'.acap = ks.acap
  nassump : ks'.nassump = ks.nassump
  lvlArr : ks'.lvlArr = ks.lvlArr
  rsn : ks'.rsn = ks.rsn
  trl : ks'.trl = ks.trl
  vals : ks'.vals = ks.vals
  assump : ks'.assump = ks.assump
  whead : ks'.whead = ks.whead
  wnext : ks'.wnext = ks.wnext
  wblit : ks'.wblit = ks.wblit
  clOff : ks'.clOff = ks.clOff
  clSz : ks'.clSz = ks.clSz
  arena : ks'.arena = ks.arena

/-- Unchanged `K512State` fields across `full_k512_propagate`. -/
structure K5PropPreserved (ks ks' : K512State) : Prop where
  nv : ks'.nv = ks.nv
  nc : ks'.nc = ks.nc
  lvl : ks'.lvl = ks.lvl
  incons : ks'.incons = ks.incons
  alen : ks'.alen = ks.alen
  acap : ks'.acap = ks.acap
  nassump : ks'.nassump = ks.nassump
  assump : ks'.assump = ks.assump

/-! ## 5. All `24` UNSAT-Only `Spec` Contracts (`12` `k512` + `12` `m4_sweep`) -/

def k5InitSpec : Spec [i64, i32] [] := fun (h, nv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    if c.scratch_cap < k5MinScr ∨ k5MaxV < nv.toNat then Q () m
    else ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
      let ks' := k5StateOfScratch scr'
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      s'.LengthsOk c → (∀ i < k5Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      (∀ P, K512ScratchInv P scr') → K512TrailSynced ks' →
      ks'.nv = nv → ks'.nc = 0#32 → ks'.lvl = 0#32 → ks'.prop = 0#32 →
      ks'.trl_end = 0#32 → ks'.unass = nv → ks'.incons = 0#32 → ks'.nassump = 0#32 →
      (FullMem c s' ⋆ R) m' → Q () m'

def k5WatchSpec : Spec [i64, i32, i32, i32] [] := fun (kPtr, cid, l0, l1, ()) m Q _ =>
  ∃ (acap : Nat) (ks : K512State) (R : Mem 64 → Prop),
    ks.ShapesOk acap ∧ acap < dimacsBound ∧ ks.nv.toNat ≤ k5MaxV ∧ cid.toNat < k5MaxCl ∧
    l0.toNat < 2 * ks.nv.toNat ∧ l1.toNat < 2 * ks.nv.toNat ∧ (K512Mem kPtr ks ⋆ R) m ∧
    ∀ m', (K512Mem kPtr (k5WatchStep ks cid l0 l1) ⋆ R) m' → Q () m'

def k5AssignSpec : Spec [i64, i32, i32] [] := fun (kPtr, lit, rsn, ()) m Q _ =>
  ∃ (acap : Nat) (ks : K512State) (R : Mem 64 → Prop),
    ks.ShapesOk acap ∧ acap < dimacsBound ∧ ks.nv.toNat ≤ k5MaxV ∧
    lit.toNat < 2 * ks.nv.toNat ∧ ks.trl_end.toNat < ks.nv.toNat ∧ (K512Mem kPtr ks ⋆ R) m ∧
    ∀ m', (K512Mem kPtr (k5AssignStep ks lit rsn) ⋆ R) m' → Q () m'

def k5AddClauseSpec : Spec [i64, i64, i32] [.bool] := fun (h, lits_ptr, sz, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (scr xs : List (BitVec 32))
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.scratch.scratch_buf = scr ∧
    K512ScratchInv P scr ∧ K512TrailSynced (k5StateOfScratch scr) ∧
    (k5StateOfScratch scr).lvl = 0#32 ∧ sz.toNat ≤ xs.length ∧ sz.toNat < 2 ^ 16 ∧
    (∀ i < sz.toNat, (xs[i]?.getD 0#32).toNat < 2 * (k5StateOfScratch scr).nv.toNat) ∧
    SemEntails P ((xs.take sz.toNat).map BitVec.toNat) ∧
    (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      array (t := i32) c.pScratchBuf scr ⋆ array (t := i32) lits_ptr xs ⋆ R) m ∧
    ∀ (ok : Bool) (scr' : List (BitVec 32)) (m' : Mem 64),
      let ks := k5StateOfScratch scr; let ks' := k5StateOfScratch scr'
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap → (∀ i < k5Base, scr'[i]? = scr[i]?) →
      K512ScratchInv P scr' → K512TrailSynced ks' → ks'.lvl = 0#32 → ks'.nv = ks.nv →
      ks'.nassump = ks.nassump → k5AssumpLitsS scr' = k5AssumpLitsS scr →
      (2 ≤ sz.toNat → ks'.trl_end = ks.trl_end ∧ ks'.unass = ks.unass ∧ ks'.incons = ks.incons) →
      (∀ M, (∀ i < sz.toNat, (xs[i]?.getD 0#32).toNat < 2 * M) →
        K512LitsBounded M ks → K512LitsBounded M ks') →
      (array64 (c.hdr + 32) (Full.hdrTailWords c s') ⋆
        array (t := i32) c.pScratchBuf scr' ⋆ array (t := i32) lits_ptr xs ⋆ R) m' → Q (ok, ()) m'

def k5MtfSpec : Spec [i64, i32] [] := fun (kPtr, _v, ()) m Q _ =>
  ∃ (acap : Nat) (ks : K512State) (R : Mem 64 → Prop),
    ks.ShapesOk acap ∧ acap < dimacsBound ∧ ks.nv.toNat ≤ k5MaxV ∧ (K512Mem kPtr ks ⋆ R) m ∧
    ∀ qf' ql' qs' qst' qp' qn' qsa' m',
      let ks' : K512State := { ks with qfirst := qf', qlast := ql', qsearch := qs', qstamp := qst',
                                       qprev := qp', qnext := qn', qstampArr := qsa' }
      ks'.ShapesOk acap → (K512Mem kPtr ks' ⋆ R) m' → Q () m'

def k5BacktrackSpec : Spec [i64, i32] [] := fun (kPtr, target_lvl, ()) m Q _ =>
  ∃ (acap : Nat) (P : (Nat → Bool) → Prop) (ks : K512State) (R : Mem 64 → Prop),
    K512Inv acap P ks ∧ (target_lvl = 0#32 ∨ K512TrailSynced ks) ∧ (K512Mem kPtr ks ⋆ R) m ∧
    ∀ (ks' : K512State) (m' : Mem 64),
      K512Inv acap P ks' → K512TrailSynced ks' → ks'.lvl = target_lvl →
      ks'.trl_end.toNat ≤ ks.trl_end.toNat → K5BtPreserved ks ks' →
      (∀ i < ks'.trl_end.toNat,
        ks'.trl[i]? = ks.trl[i]? ∧ ks'.rsn[(ks'.trl[i]?.getD 0#32).toNat / 2]? =
          ks.rsn[(ks'.trl[i]?.getD 0#32).toNat / 2]? ∧
        (ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat) →
      (∀ i < ks.trl_end.toNat,
        (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat →
        i < ks'.trl_end.toNat) →
      (K512Mem kPtr ks' ⋆ R) m' → Q () m'

def k5PropagateSpec : Spec [i64] [i32] := fun (kPtr, ()) m Q _ =>
  ∃ (acap : Nat) (P : (Nat → Bool) → Prop) (ks : K512State) (R : Mem 64 → Prop),
    K512Inv acap P ks ∧ K512TrailSynced ks ∧ (K512Mem kPtr ks ⋆ R) m ∧
    ∀ (confl : BitVec 32) (ks' : K512State) (m' : Mem 64),
      K512Inv acap P ks' → K512TrailSynced ks' → K5PropPreserved ks ks' →
      ks.trl_end.toNat ≤ ks'.trl_end.toNat →
      (∀ i < ks.trl_end.toNat, ks'.trl[i]? = ks.trl[i]? ∧
        ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
          ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? ∧
        ks'.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]? =
          ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?) →
      (∀ i, ks.trl_end.toNat ≤ i → i < ks'.trl_end.toNat →
        ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks.lvl ∧
        ks'.rsn[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ 0xFFFFFFFF#32) →
      (confl = 0xFFFFFFFF#32 → ks'.prop = ks'.trl_end) →
      (confl ≠ 0xFFFFFFFF#32 →
        confl.toNat < ks'.nc.toNat ∧ ∀ l ∈ k5ClauseLits ks' confl.toNat, ks'.vals[l]? = some 2#32) →
      (K512Mem kPtr ks' ⋆ R) m' → Q (confl, ()) m'

def k5AnaClauseSpec : Spec [i64, i32, i32] [] := fun (kPtr, cid, skip_v, ()) m Q _ =>
  ∃ (acap : Nat) (P : (Nat → Bool) → Prop) (ks : K512State) (idx : Nat) (R : Mem 64 → Prop),
    K512AnaInv acap P ks idx ∧ cid.toNat < ks.nc.toNat ∧
    (∃ v_dec < ks.nv.toNat, ks.lvlArr[v_dec]?.getD 0#32 = ks.lvl) ∧
    (∀ l ∈ k5ClauseLits ks cid.toNat, l / 2 ≠ skip_v.toNat →
      ks.vals[l]? = some 2#32 ∧
      (ks.lvlArr[l / 2]?.getD 0#32 = ks.lvl →
        ∃ j < idx, (ks.trl[j]?.getD 0#32).toNat = l ^^^ 1)) ∧
    (skip_v ≠ 0xFFFFFFFF#32 →
      ∃ l ∈ k5ClauseLits ks cid.toNat, l / 2 = skip_v.toNat ∧
        (∀ l' ∈ k5ClauseLits ks cid.toNat, l' / 2 = skip_v.toNat → l' = l) ∧
        (ks.flags[skip_v.toNat]?.getD 0#32 &&& 2#32) ≠ 0#32 ∧
        ks.lvlArr[skip_v.toNat]?.getD 0#32 = ks.lvl ∧
        SemEntails P ((l ^^^ 1) :: k5ResolventLits ks idx)) ∧
    (K512Mem kPtr ks ⋆ R) m ∧
    ∀ (ks' : K512State) (m' : Mem 64),
      K512AnaInv acap P ks' idx → K5AnaPreserved ks ks' →
      SemEntails P (k5ResolventLits ks' idx) →
      (∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
        (ks'.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32) →
      (K512Mem kPtr ks' ⋆ R) m' → Q () m'

def k5AnalyzeSpec : Spec [i64, i32] [.bool] := fun (kPtr, confl_cid, ()) m Q _ =>
  ∃ (acap : Nat) (P : (Nat → Bool) → Prop) (ks : K512State) (R : Mem 64 → Prop),
    K512Inv acap P ks ∧ K512TrailSynced ks ∧ 0 < ks.lvl.toNat ∧
    (∃ i < ks.trl_end.toNat,
      ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks.lvl) ∧
    confl_cid.toNat < ks.nc.toNat ∧
    (∀ l ∈ k5ClauseLits ks confl_cid.toNat, ks.vals[l]? = some 2#32) ∧
    (K512Mem kPtr ks ⋆ R) m ∧
    ∀ (ok : Bool) (ks' : K512State) (m' : Mem 64),
      K512Inv acap P ks' → ks'.nv = ks.nv → ks'.nassump = ks.nassump →
      ks'.assump = ks.assump → ks'.incons = ks.incons →
      (ok = true →
        K512TrailSynced ks' ∧ ks'.lvl.toNat < ks.lvl.toNat ∧
        (0 < ks'.lvl.toNat → ∃ i < ks'.trl_end.toNat,
          ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks'.lvl) ∧
        (∀ d ∈ k5TrailDecisions ks', ∃ i < ks.trl_end.toNat,
          (ks.trl[i]?.getD 0#32).toNat = d ∧ d ∈ k5TrailDecisions ks ∧
          (ks.lvlArr[d / 2]?.getD 0#32).toNat ≤ ks'.lvl.toNat) ∧
        (∀ i < ks.trl_end.toNat,
          (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ ks'.lvl.toNat →
          i < ks'.trl_end.toNat ∧ ks'.trl[i]? = ks.trl[i]? ∧
          ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
            ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?)) →
      (K512Mem kPtr ks' ⋆ R) m' → Q (ok, ()) m'

def k5SolveSpec : Spec [i64, i64] [i64] := fun (h, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ K512ScratchInv P s.scratch.scratch_buf ∧ (FullMem c s ⋆ R) m ∧
    ∀ (r fuel' : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with core := { s.core with fuel := fuel' }
                                     scratch := { s.scratch with scratch_buf := scr' } }
      let ks := k5StateOfScratch s.scratch.scratch_buf; let ks' := k5StateOfScratch scr'
      s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ i < k5Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K512ScratchInv P scr' → ks'.nv = ks.nv → ks'.nassump = ks.nassump →
      k5AssumpLitsS scr' = k5AssumpLitsS s.scratch.scratch_buf →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → ∀ β, P β → ¬ (unitsCnf (k5AssumpLitsS scr')).Sat β) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def k5FlipSpec : Spec [i64, i32] [.bool] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ K512ScratchInv P s.scratch.scratch_buf ∧
    lit.toNat < 2 * (k5StateOfScratch s.scratch.scratch_buf).nv.toNat ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      let ks := k5StateOfScratch s.scratch.scratch_buf; let ks' := k5StateOfScratch scr'
      s'.LengthsOk c → (∀ i < k5Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K512ScratchInv P scr' → ks'.nv = ks.nv → ks'.nassump = ks.nassump →
      k5AssumpLitsS scr' = k5AssumpLitsS s.scratch.scratch_buf →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def k5AddLiveSpec : Spec [i64, i32, i32] [] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (R : Mem 64 → Prop),
    let ks0 := k5StateOfScratch s.scratch.scratch_buf
    h = c.hdr ∧ s.LengthsOk c ∧ K512ScratchInv P s.scratch.scratch_buf ∧
    a.toNat < 2 * ks0.nv.toNat ∧
    (b = 0xFFFFFFFF#32 → SemEntails P [a.toNat]) ∧
    (b ≠ 0xFFFFFFFF#32 → b.toNat < 2 * ks0.nv.toNat ∧ SemEntails P [a.toNat, b.toNat]) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      let ks' := k5StateOfScratch scr'
      s'.LengthsOk c → (∀ i < k5Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K512ScratchInv P scr' → K512TrailSynced ks' → ks'.nv = ks0.nv →
      ks'.nassump = ks0.nassump → k5AssumpLitsS scr' = k5AssumpLitsS s.scratch.scratch_buf →
      (FullMem c s' ⋆ R) m' → Q () m'

/-! ### Part B: `full_m4_sweep_*` (`12` fns) -/

def m4SweepConeSpec : Spec [i64, i32] [i64] := fun (h, root_v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ k5MinScr ≤ c.scratch_cap ∧
    root_v.toNat < s.core.cur_vars ∧ M4TmkZero s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r tmp' ws1' tmk' scr' m',
      let s' : FullState := { s with core := { s.core with tmp := tmp' }
                                     scratch := { s.scratch with work_stk1 := ws1',
                                                                 tarjan_mark := tmk',
                                                                 scratch_buf := scr' } }
      let nv := (r &&& 0xFFFF#64).toNat
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.vals = s.core.vals →
      s'.core.inconsistent = s.core.inconsistent → M4SweepConeOk F_cur s' nv →
      (∀ v < s.core.cur_vars, tmk'[v]?.getD 0#32 ≠ 0#32 →
        ∃ i < nv, (ws1'[i]?.getD 0#32).toNat = v) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def m4SweepRefineSigSpec : Spec [i64, i32, i32] [] := fun (h, nv, _bit_idx, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ k5MinScr ≤ c.scratch_cap ∧
    nv.toNat ≤ k5MaxV ∧ nv.toNat ≤ 2 * c.max_vars ∧
    (∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ sig' m', sig'.length = c.max_vars →
      (FullMem c { s with scratch := { s.scratch with sim_sig := sig' } } ⋆ R) m' → Q () m'

def m4SweepRandPhasesSpec : Spec [i64, i32] [] := fun (h, nv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ K512ScratchInv P s.scratch.scratch_buf ∧
    (k5StateOfScratch s.scratch.scratch_buf).nv = nv ∧ (FullMem c s ⋆ R) m ∧
    ∀ rng' scr' m',
      let s' : FullState := { s with scratch := { s.scratch with rng_state := rng',
                                                                 scratch_buf := scr' } }
      s'.LengthsOk c → (∀ i < k5Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K512ScratchInv P scr' → (k5StateOfScratch scr').nv = nv →
      (FullMem c s' ⋆ R) m' → Q () m'

def m4SweepFlipRoundSpec : Spec [i64, i32] [i32] := fun (h, nv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (P : (Nat → Bool) → Prop) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ K512ScratchInv P s.scratch.scratch_buf ∧
    (k5StateOfScratch s.scratch.scratch_buf).nv = nv ∧ (FullMem c s ⋆ R) m ∧
    ∀ ret rng' scr' m',
      let s' : FullState := { s with scratch := { s.scratch with rng_state := rng',
                                                                 scratch_buf := scr' } }
      s'.LengthsOk c → (∀ i < k5Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K512ScratchInv P scr' → (k5StateOfScratch scr').nv = nv →
      (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

def m4SweepSimSpec : Spec [i64, i32, i64] [i32] := fun (h, nv, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ M4SweepConeOk F_cur s nv.toNat ∧ (FullMem c s ⋆ R) m ∧
    ∀ r fuel' rng' sig' scr' m',
      let s' : FullState := { s with core := { s.core with fuel := fuel' }
                                     scratch := { s.scratch with rng_state := rng',
                                                                 sim_sig := sig',
                                                                 scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → fuel'.toNat ≤ s.core.fuel.toNat →
      M4SweepConeOk F_cur s' nv.toNat →
      (r = 0xFFFFFFFF#32 → (cnfOfClauses F_cur).Unsat) →
      (r ≠ 0xFFFFFFFF#32 → r.toNat ≤ 64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def m4SweepRearmSpec : Spec [i64, i32] [] := fun (h, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ flags' m',
      let s' : FullState := { s with core := { s.core with flags := flags' } }
      flags'.length = c.max_vars → FullDenseInvW c F0 F_cur s' →
      (FullMem c s' ⋆ R) m' → Q () m'

def m4SweepBuildPhtSpec : Spec [i64, i32, i64] [] := fun (h, nv, _smask, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ k5MinScr ≤ c.scratch_cap ∧
    nv.toNat ≤ k5MaxV ∧ nv.toNat ≤ 2 * c.max_vars ∧
    (∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, i < phtHead ∨ phtMerged ≤ i → scr'[i]? = s.scratch.scratch_buf[i]?) →
      PhtOk nv.toNat scr' → (FullMem c s' ⋆ R) m' → Q () m'

def m4SweepUnitsSpec : Spec [i64, i32, i32, i64] [i64] := fun (h, nv, rbit_in, _tlim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ M4SweepConeOk F_cur s nv.toNat ∧
    rbit_in.toNat ≤ 64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      M4SweepConeOk F_cur s' nv.toNat →
      (r = 0xFFFFFFFFFFFFFFFF#64 → F0.Unsat) →
      (r ≠ 0xFFFFFFFFFFFFFFFF#64 → r.toNat ≤ 64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def m4SweepClassesSpec : Spec [i64, i32, i32, i64] [i64] := fun (h, nv, rbit_in, _tlim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ M4SweepConeOk F_cur s nv.toNat ∧
    rbit_in.toNat ≤ 64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def m4SweepVarSpec : Spec [i64, i32, i64] [i64] := fun (h, root_v, _tlim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ k5MinScr ≤ c.scratch_cap ∧
    root_v.toNat < s.core.cur_vars ∧ M4TmkZero s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → M4TmkZero s' →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def m4SweepDenseSpec : Spec [i64, i64, i64] [i64] := fun (h, _budget, _tlim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Top-level sparse-mode (`FullSparseInv` → `FullSparseInv`) UNSAT-sound sweeping contract. -/
def m4SweepSatSpec : Spec [i64, i64, i64] [i64] := fun (h, _budget, _tlim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ### `31`-Row Specification Table & Environment (`24` owned + `7` canonical `Full` externs) -/

def fullM4SweepSpecTable : List SpecEntry :=
  [ ⟨"full_k512_init", [i64, i32], [], k5InitSpec, true⟩
  , ⟨"full_k512_watch", [i64, i32, i32, i32], [], k5WatchSpec, true⟩
  , ⟨"full_k512_assign", [i64, i32, i32], [], k5AssignSpec, true⟩
  , ⟨"full_k512_add_clause", [i64, i64, i32], [.bool], k5AddClauseSpec, true⟩
  , ⟨"full_k512_mtf", [i64, i32], [], k5MtfSpec, true⟩
  , ⟨"full_k512_backtrack", [i64, i32], [], k5BacktrackSpec, true⟩
  , ⟨"full_k512_propagate", [i64], [i32], k5PropagateSpec, true⟩
  , ⟨"full_k512_ana_clause", [i64, i32, i32], [], k5AnaClauseSpec, true⟩
  , ⟨"full_k512_analyze", [i64, i32], [.bool], k5AnalyzeSpec, true⟩
  , ⟨"full_k512_solve", [i64, i64], [i64], k5SolveSpec, true⟩
  , ⟨"full_k512_flip", [i64, i32], [.bool], k5FlipSpec, true⟩
  , ⟨"full_k512_add_live", [i64, i32, i32], [], k5AddLiveSpec, true⟩
  , ⟨"full_m4_sweep_cone", [i64, i32], [i64], m4SweepConeSpec, true⟩
  , ⟨"full_m4_sweep_refine_sig", [i64, i32, i32], [], m4SweepRefineSigSpec, true⟩
  , ⟨"full_m4_sweep_rand_phases", [i64, i32], [], m4SweepRandPhasesSpec, true⟩
  , ⟨"full_m4_sweep_flip_round", [i64, i32], [i32], m4SweepFlipRoundSpec, true⟩
  , ⟨"full_m4_sweep_sim", [i64, i32, i64], [i32], m4SweepSimSpec, true⟩
  , ⟨"full_m4_sweep_rearm", [i64, i32], [], m4SweepRearmSpec, true⟩
  , ⟨"full_m4_sweep_build_pht", [i64, i32, i64], [], m4SweepBuildPhtSpec, true⟩
  , ⟨"full_m4_sweep_units", [i64, i32, i32, i64], [i64], m4SweepUnitsSpec, true⟩
  , ⟨"full_m4_sweep_classes", [i64, i32, i32, i64], [i64], m4SweepClassesSpec, true⟩
  , ⟨"full_m4_sweep_var", [i64, i32, i64], [i64], m4SweepVarSpec, true⟩
  , ⟨"full_m4_sweep_dense", [i64, i64, i64], [i64], m4SweepDenseSpec, true⟩
  , ⟨"full_m4_sweep_sat", [i64, i64, i64], [i64], m4SweepSatSpec, true⟩
  , ⟨"full_rng_next", [i64], [i64], Full.fullRngNextSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩
  , ⟨"full_add_unit", [i64, i32], [.bool], Full.fullAddUnitSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], Full.fullAddBinSpec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], Full.fullEnterDenseSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], Full.fullRebuildWatchesSpec, true⟩ ]

def fullM4SweepEnv : Env := Env.ofTable fullM4SweepSpecTable

theorem fullM4SweepSpecTable_nodup : (fullM4SweepSpecTable.map SpecEntry.name).Nodup := by decide

theorem fullM4SweepSpecTable_noExit : ∀ e ∈ fullM4SweepSpecTable, e.noExit = true := by
  intro e he
  have hall : fullM4SweepSpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem fullM4SweepSpecTable_sigs :
    (fullM4SweepSpecTable.take 24).map (fun e => (e.name, e.as, e.rs)) =
      fullM4Sweep_fns.map (fun f => (f.name, f.as, f.rs)) := by t_kernel_rfl

theorem fullM4SweepSpecTable_ext_sigs :
    (fullM4SweepSpecTable.drop 24).map (fun e => ⟨e.name, e.as, e.rs⟩) = fullM4SweepExterns := by
  t_kernel_rfl

theorem fullM4SweepEnv_noExit :
    ∀ f as bs xs m Q X X',
      fullM4SweepEnv f as bs xs m Q X → fullM4SweepEnv f as bs xs m Q X' :=
  Env.ofTable_noExit fullM4SweepSpecTable_noExit

end LeanQbe.T.Examples.Kissat.FullM4Sweep
